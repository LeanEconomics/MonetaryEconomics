/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DiscretionCommitment.Commitment
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Optimal policy with a distorted steady state

Galí (2015), Section 5.3, pp. 139–144.

When the zero-inflation steady state is inefficient (distortion `Φ > 0`), the policy-relevant
welfare loss acquires a linear term `−Λ x̂_t`, `Λ = Φ λ / ε` (eq. (17)), and the Phillips curve
is written in the gap `x̂_t` from its steady-state value (eq. (18)).

## Main results

* `loss_rescale`, `nkpc_in_xhat`: the loss (17) and the Phillips curve (18) from the
  Appendix 5.1 welfare expression and the Phillips curve in the output gap.
* `discretion_period_optimal_iff`: (19) is necessary and sufficient for the per-period
  problem under discretion.
* `discretion_exists`, `discretion_unique`: (20) and the `x̂` formula give the unique bounded
  equilibrium under discretion; `inflationBias_pos`, `strictMono_inflationBias`,
  `strictMono_inflationBias_Phi`: the inflation bias is positive and increasing in `Λ` and `Φ`.
* `γ`, `δ` and their lemmas (`del_pos`, `del_lt_one_iff`, `kappa_sq_del`:
  `κ² δ / ϑ = (1 − δ)(1 − β δ)`) are imported from `Commitment`; `gam_lt_one` is added here.
* `commitment_eq21`, `commitment_eq22`, `commitment_exists`, `commitment_unique`,
  `commitment_eq23`, `commitment_eq24`: commitment with distortion, (21)–(24).
* `commitment_eq25`, `commitment_eq26_corrected`, `commitment_eq27_corrected`: the output gap.
  The book's (26)–(27) deterministic term `(1 − δ) Λ / ϑ` is wrong (`printed_eq26_false`); the
  correct term is `δ^{t+1} Λ / ϑ`.
* `tendsto_priceLevel_zeroShock`, `tendsto_gap_zeroShock`, `tendsto_infl_zeroShock`: no
  long-run inflation bias under commitment.
* `lagrangian_identity`, `lagrangian_sufficiency`, `det_optimal_iff`, `det_commitment_optimal`:
  in the deterministic problem, the Lagrangian conditions are necessary and sufficient for
  optimality among bounded paths, and the optimum exists and is unique for every bounded
  cost-push sequence; `det_zeroShock_optimal`: the explicit plan without shocks;
  `zero_path_not_optimal`: with `Λ ≠ 0` the optimum is not the zero path.
-/

namespace Gali.DiscretionCommitment.DistortedSS

open Filter Topology
open Gali.DiscretionCommitment.Commitment (gam del gam_pos gam_mul_lt_iff del_pos
  del_lt_one_iff kappa_sq_del lag lag_zero lag_succ lag_adapted)

/-! ### The loss function and the Phillips curve, (17)–(18) -/

/-- Galí (2015), (17), p. 139: the period loss `½ (π² + ϑ x̂²) − Λ x̂`. -/
noncomputable def periodLoss (ϑ Λ infl x : ℝ) : ℝ := (infl ^ 2 + ϑ * x ^ 2) / 2 - Λ * x

/-- Galí (2015), (17), p. 139: the weight of the linear term, `Λ ≡ Φ λ / ε`. -/
noncomputable def distLambda (Φ lam ε : ℝ) : ℝ := Φ * lam / ε

/-- Galí (2015), p. 139: with a steady-state gross markup `M > 1` and no subsidy, the
distortion is `Φ = 1 − 1/M > 0`. -/
theorem markup_distortion_pos {M : ℝ} (hM : 1 < M) : 0 < 1 - 1 / M := by
  have : 1 / M < 1 := by rw [div_lt_one (by linarith)]; exact hM
  linarith

/-- Galí (2015), p. 139: `Λ = Φ λ / ε > 0` when `Φ, λ, ε > 0`. -/
theorem distLambda_pos {Φ lam ε : ℝ} (hΦ : 0 < Φ) (hlam : 0 < lam) (hε : 0 < ε) :
    0 < distLambda Φ lam ε := by
  unfold distLambda; positivity

/-- Galí (2015), (17), p. 139, and Appendix 5.1, p. 156: multiplying the period welfare loss
`−[Φ x̂ − ½ ((ε/λ) π² + c x̂²)]` of Appendix 5.1 (`c = σ + (φ+α)/(1−α)`) by `λ/ε` gives the
period loss of (17), with `κ = λ c`, `ϑ = κ/ε` and `Λ = Φ λ/ε`. -/
theorem loss_rescale {lam ε c Φ κ ϑ Λ : ℝ} (hlam : lam ≠ 0) (hε : ε ≠ 0) (hκ : κ = lam * c)
    (hϑ : ϑ = κ / ε) (hΛ : Λ = distLambda Φ lam ε) (infl x : ℝ) :
    lam / ε * -(Φ * x - ((ε / lam) * infl ^ 2 + c * x ^ 2) / 2) = periodLoss ϑ Λ infl x := by
  subst hκ hϑ hΛ
  unfold periodLoss distLambda
  field_simp
  ring

/-- Galí (2015), (17), p. 139: completing the square, the period loss is
`½ π² + (ϑ/2)(x̂ − Λ/ϑ)² − Λ²/(2ϑ)`, so the loss is minimised at `x̂ = Λ/ϑ` when `π = 0`
is free. -/
theorem periodLoss_complete_square {ϑ : ℝ} (hϑ : ϑ ≠ 0) (Λ infl x : ℝ) :
    periodLoss ϑ Λ infl x = infl ^ 2 / 2 + ϑ / 2 * (x - Λ / ϑ) ^ 2 - Λ ^ 2 / (2 * ϑ) := by
  unfold periodLoss
  field_simp
  ring

/-- Galí (2015), (18), p. 139: the Phillips curve `π_t = β E_t π_{t+1} + κ (y_t − y^n_t)`
rewritten in `x̂_t ≡ x_t − x̄`, where `x_t = y_t − y^e_t` and `x̄ = y^n − y^e` is its
steady-state value, reads `π_t = β E_t π_{t+1} + κ x̂_t + u_t` with
`u_t ≡ κ (ŷ^e_t − ŷ^n_t)` (hats: deviations from the steady states `y^e`, `y^n`). -/
theorem nkpc_in_xhat {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ yne yee : ℝ}
    {infl y yn ye : ℕ → Ω → ℝ}
    (h : ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • (y t - yn t)) (t : ℕ) :
    infl t = β • 𝔼.E t (infl (t + 1)) + κ • ((y t - ye t) - fun _ => yne - yee) +
      κ • ((ye t - fun _ => yee) - (yn t - fun _ => yne)) := by
  rw [h t]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-! ### Optimal discretionary policy, (19)–(20) -/

/-- Galí (2015), (19), p. 140: the per-period problem under discretion: minimise
`½(π² + ϑ x̂²) − Λ x̂` subject to `π = κ x̂ + υ`, `υ` taken as given. The first-order
condition `x̂ = Λ/ϑ − (κ/ϑ) π` is necessary and sufficient for a minimum. -/
theorem discretion_period_optimal_iff {κ ϑ Λ υ x : ℝ} (hϑ : 0 < ϑ) :
    (∀ x', periodLoss ϑ Λ (κ * x + υ) x ≤ periodLoss ϑ Λ (κ * x' + υ) x') ↔
      x = Λ / ϑ - κ / ϑ * (κ * x + υ) := by
  set F := κ * (κ * x + υ) + ϑ * x - Λ with hF
  have hdiff : ∀ y, periodLoss ϑ Λ (κ * y + υ) y - periodLoss ϑ Λ (κ * x + υ) x =
      (y - x) * F + (κ ^ 2 + ϑ) / 2 * (y - x) ^ 2 := by
    intro y; unfold periodLoss; rw [hF]; ring
  have hpos : 0 < κ ^ 2 + ϑ := by positivity
  have hiff : x = Λ / ϑ - κ / ϑ * (κ * x + υ) ↔ F = 0 := by
    rw [hF]
    constructor
    · intro h; field_simp at h; linarith
    · intro h; field_simp; linarith
  rw [hiff]
  constructor
  · intro hmin
    have h1 := hmin (x - F / (κ ^ 2 + ϑ))
    have h2 := hdiff (x - F / (κ ^ 2 + ϑ))
    have h3 : (x - F / (κ ^ 2 + ϑ) - x) * F + (κ ^ 2 + ϑ) / 2 * (x - F / (κ ^ 2 + ϑ) - x) ^ 2
        = -(F ^ 2 / (2 * (κ ^ 2 + ϑ))) := by
      field_simp; ring
    have h4 : F ^ 2 / (2 * (κ ^ 2 + ϑ)) ≤ 0 := by linarith
    have h5 : F ^ 2 ≤ 0 := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (κ ^ 2 + ϑ))).mp h4
      linarith
    nlinarith [sq_nonneg F]
  · intro h0 y
    have := hdiff y
    rw [h0, mul_zero, zero_add] at this
    nlinarith [sq_nonneg (y - x)]

/-- Galí (2015), (19), p. 140: under the first-order condition, the per-period optimum is
strict: any other `x̂'` gives a strictly larger loss. -/
theorem discretion_period_strict {κ ϑ Λ υ x x' : ℝ} (hϑ : 0 < ϑ)
    (hfoc : x = Λ / ϑ - κ / ϑ * (κ * x + υ)) (hne : x' ≠ x) :
    periodLoss ϑ Λ (κ * x + υ) x < periodLoss ϑ Λ (κ * x' + υ) x' := by
  have hF : κ * (κ * x + υ) + ϑ * x - Λ = 0 := by
    field_simp at hfoc; linarith
  have hd : periodLoss ϑ Λ (κ * x' + υ) x' - periodLoss ϑ Λ (κ * x + υ) x =
      (x' - x) * (κ * (κ * x + υ) + ϑ * x - Λ) + (κ ^ 2 + ϑ) / 2 * (x' - x) ^ 2 := by
    unfold periodLoss; ring
  rw [hF, mul_zero, zero_add] at hd
  have : 0 < (x' - x) ^ 2 := by
    have : x' - x ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have : 0 < (κ ^ 2 + ϑ) / 2 * (x' - x) ^ 2 := by positivity
  linarith

/-- Galí (2015), (18)–(19), p. 140: an equilibrium under discretion with a distorted steady
state: the Phillips curve (18) and the targeting rule (19), at every date. -/
def DiscretionEqm {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κ ϑ Λ : ℝ)
    (u infl x : ℕ → Ω → ℝ) : Prop :=
  (∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + u t) ∧
    ∀ t, x t = (fun _ => Λ / ϑ) - (κ / ϑ) • infl t

/-- Galí (2015), p. 141: the average inflation (inflation bias) under discretion,
`π̄ = κ Λ / (κ² + ϑ (1 − β))`. -/
noncomputable def inflationBias (β κ ϑ Λ : ℝ) : ℝ := κ * Λ / (κ ^ 2 + ϑ * (1 - β))

/-- Galí (2015), p. 141: the average output gap under discretion,
`x̄ = (1 − β) Λ / (κ² + ϑ (1 − β))`. -/
noncomputable def gapBias (β κ ϑ Λ : ℝ) : ℝ := (1 - β) * Λ / (κ ^ 2 + ϑ * (1 - β))

/-- Galí (2015), (20), p. 140: the discretionary inflation path
`π_t = π̄ + ϑ/(κ² + ϑ(1 − βρ_u)) u_t`. -/
noncomputable def discInfl {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => inflationBias β κ ϑ Λ) + (ϑ / (κ ^ 2 + ϑ * (1 - β * ρ))) • u t

/-- Galí (2015), p. 141: the discretionary output-gap path
`x̂_t = x̄ − κ/(κ² + ϑ(1 − βρ_u)) u_t`. -/
noncomputable def discGap {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => gapBias β κ ϑ Λ) - (κ / (κ ^ 2 + ϑ * (1 - β * ρ))) • u t

/-- Galí (2015), p. 130: `1 − βρ > 0` for `0 < β < 1` and `|ρ| < 1`. -/
theorem one_sub_mul_pos {β ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : |ρ| < 1) :
    0 < 1 - β * ρ := by
  have : |β * ρ| < 1 := by
    rw [abs_mul, abs_of_pos hβ0]
    nlinarith [abs_nonneg ρ]
  linarith [le_abs_self (β * ρ)]

/-- Galí (2015), (20), p. 140, and p. 141: the discretionary paths (20) and
`x̂_t = x̄ − κ/(κ² + ϑ(1 − βρ_u)) u_t` form an equilibrium under discretion (existence of the
MSV solution) for an AR(1) cost-push process. -/
theorem discretion_exists {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ ρ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ u) :
    DiscretionEqm 𝔼 β κ ϑ Λ u (discInfl β κ ϑ Λ ρ u) (discGap β κ ϑ Λ ρ u) := by
  have h1 : 0 < 1 - β * ρ := one_sub_mul_pos hβ0 hβ1 hρ
  have hD : 0 < κ ^ 2 + ϑ * (1 - β * ρ) := by positivity
  have hD1 : 0 < κ ^ 2 + ϑ * (1 - β) := by
    have : 0 < 1 - β := by linarith
    positivity
  have hD' := hD.ne'
  have hD1' := hD1.ne'
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have hE : 𝔼.E t (discInfl β κ ϑ Λ ρ u (t + 1)) = (fun _ => inflationBias β κ ϑ Λ) +
        (ϑ / (κ ^ 2 + ϑ * (1 - β * ρ)) * ρ) • u t := by
      unfold discInfl; rw [map_add, 𝔼.const, 𝔼.E_smul, hu.2 t, smul_smul]
    rw [hE]; funext ω
    unfold discInfl discGap inflationBias gapBias
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · have hc : gapBias β κ ϑ Λ = Λ / ϑ - κ / ϑ * inflationBias β κ ϑ Λ := by
      unfold gapBias inflationBias
      rw [eq_sub_iff_add_eq, div_mul_div_comm, div_add_div _ _ hD1' (by positivity),
        div_eq_div_iff (by positivity) hϑ.ne']
      ring
    have hk : κ / (κ ^ 2 + ϑ * (1 - β * ρ)) = κ / ϑ * (ϑ / (κ ^ 2 + ϑ * (1 - β * ρ))) := by
      rw [div_mul_div_comm, mul_comm κ ϑ, mul_div_mul_left _ _ hϑ.ne']
    funext ω
    unfold discInfl discGap
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [hc, hk]
    ring

/-- Galí (2015), p. 140: under discretion, combining (18) and (19), inflation solves the
scalar forward equation `π_t = (ϑβ/(ϑ + κ²)) E_t π_{t+1} + (κΛ + ϑ u_t)/(ϑ + κ²)`. -/
theorem discretion_forward {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ : ℝ}
    (hϑ : 0 < ϑ) {u infl x : ℕ → Ω → ℝ} (hE : DiscretionEqm 𝔼 β κ ϑ Λ u infl x) (t : ℕ) :
    infl t = (ϑ * β / (ϑ + κ ^ 2)) • 𝔼.E t (infl (t + 1)) +
      ((fun _ => κ * Λ / (ϑ + κ ^ 2)) + (ϑ / (ϑ + κ ^ 2)) • u t) := by
  have h1 := hE.1 t
  rw [hE.2 t] at h1
  have hD : 0 < ϑ + κ ^ 2 := by positivity
  funext ω
  have h2 := congrFun h1 ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h2 ⊢
  field_simp at h2 ⊢
  linear_combination h2

/-- Galí (2015), (20), p. 140, and p. 141: uniqueness. Any equilibrium under discretion with
bounded inflation coincides with (20) and the `x̂` formula of p. 141 (for a bounded AR(1)
cost-push process, `0 < β < 1`, `ϑ > 0`, `|ρ_u| < 1`). -/
theorem discretion_unique {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ ρ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1) {u infl x : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) (hE : DiscretionEqm 𝔼 β κ ϑ Λ u infl x)
    (hb : BoundedProc infl) :
    infl = discInfl β κ ϑ Λ ρ u ∧ x = discGap β κ ϑ Λ ρ u := by
  have hD : 0 < ϑ + κ ^ 2 := by positivity
  have ha0 : 0 ≤ ϑ * β / (ϑ + κ ^ 2) := by positivity
  have ha1 : ϑ * β / (ϑ + κ ^ 2) < 1 := by
    rw [div_lt_one hD]; nlinarith [sq_nonneg κ]
  have ha : |ϑ * β / (ϑ + κ ^ 2)| < 1 := by rwa [abs_of_nonneg ha0]
  have hc := discretion_exists 𝔼 hβ0 hβ1 hϑ hρ (Λ := Λ) (κ := κ) hu
  have hcb : BoundedProc (discInfl β κ ϑ Λ ρ u) := by
    obtain ⟨M, hM⟩ := hub
    refine ⟨|inflationBias β κ ϑ Λ| + |ϑ / (κ ^ 2 + ϑ * (1 - β * ρ))| * M, fun t ω => ?_⟩
    unfold discInfl
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    gcongr
    exact hM t ω
  have hπ : infl = discInfl β κ ϑ Λ ρ u :=
    𝔼.forward_unique ha (discretion_forward 𝔼 hϑ hE) (discretion_forward 𝔼 hϑ hc) hb hcb
  refine ⟨hπ, ?_⟩
  funext t
  rw [hE.2 t, hc.2 t, hπ]

/-- Galí (2015), p. 141: the inflation bias `π̄ = κΛ/(κ² + ϑ(1 − β))` is positive when the
steady state is inefficient (`Λ > 0`). -/
theorem inflationBias_pos {β κ ϑ Λ : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hΛ : 0 < Λ) :
    0 < inflationBias β κ ϑ Λ := by
  have : 0 < 1 - β := by linarith
  unfold inflationBias; positivity

/-- Galí (2015), p. 141: the average output gap under discretion,
`x̄ = (1 − β)Λ/(κ² + ϑ(1 − β))`, is positive when `Λ > 0`. -/
theorem gapBias_pos {β κ ϑ Λ : ℝ} (hβ1 : β < 1) (hϑ : 0 < ϑ) (hΛ : 0 < Λ) :
    0 < gapBias β κ ϑ Λ := by
  have : 0 < 1 - β := by linarith
  unfold gapBias; positivity

/-- Galí (2015), p. 141: the inflation bias is strictly increasing in `Λ`. -/
theorem strictMono_inflationBias {β κ ϑ : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) :
    StrictMono (fun Λ => inflationBias β κ ϑ Λ) := by
  intro Λ₁ Λ₂ h
  have : 0 < 1 - β := by linarith
  have hD : 0 < κ ^ 2 + ϑ * (1 - β) := by positivity
  simp only [inflationBias]
  gcongr

/-- Galí (2015), p. 141: the inflation bias is strictly increasing in the steady-state
distortion `Φ` (through `Λ = Φλ/ε`, `λ, ε > 0`). -/
theorem strictMono_inflationBias_Phi {β κ ϑ lam ε : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hlam : 0 < lam) (hε : 0 < ε) :
    StrictMono (fun Φ => inflationBias β κ ϑ (distLambda Φ lam ε)) := by
  intro Φ₁ Φ₂ h
  refine strictMono_inflationBias hβ1 hκ hϑ ?_
  simp only [distLambda]
  gcongr

/-- Galí (2015), p. 141: without cost-push shocks, inflation under discretion is constant at
the bias `π̄` at every date: the inflation bias is permanent. -/
theorem discretion_zeroShock {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (t : ℕ) :
    discInfl β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t = fun _ => inflationBias β κ ϑ Λ := by
  unfold discInfl; simp

/-- Galí (2015), p. 141: the distortion does not affect the response to cost-push shocks under
discretion: the discretionary paths with `Λ` differ from those with `Λ = 0` by the constants
`π̄`, `x̄` only. -/
theorem discretion_shock_response_indep {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    discInfl β κ ϑ Λ ρ u t - discInfl β κ ϑ 0 ρ u t = (fun _ => inflationBias β κ ϑ Λ) ∧
      discGap β κ ϑ Λ ρ u t - discGap β κ ϑ 0 ρ u t = (fun _ => gapBias β κ ϑ Λ) := by
  unfold discInfl discGap inflationBias gapBias
  constructor <;> funext ω <;> simp

/-! ### The coefficients `γ` and `δ` -/

/-- Galí (2015), (22), p. 142: `γ ∈ (0, 1)` when `κ > 0` (derived from the `γ` lemmas of
`Commitment`, where `γ` and `δ` are defined). -/
theorem gam_lt_one {β κ ϑ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hϑ : 0 < ϑ) : gam β κ ϑ < 1 := by
  have h := (gam_mul_lt_iff hβ0 hϑ).mpr hκ.ne'
  have := gam_pos (κ := κ) hβ0 hϑ
  nlinarith

/-- Galí (2015), p. 142: `1 − δβρ > 0` for `|ρ| ≤ 1`. -/
theorem one_sub_del_mul_pos {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) : 0 < 1 - del β κ ϑ * β * ρ := by
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have : |del β κ ϑ * β * ρ| < 1 := by
    rw [abs_mul, abs_mul, abs_of_pos h0, abs_of_pos hβ0]
    have : del β κ ϑ * β < 1 := by nlinarith
    nlinarith [abs_nonneg ρ, mul_pos h0 hβ0]
  linarith [le_abs_self (del β κ ϑ * β * ρ)]

/-! ### Optimal policy under commitment: structure, (21)–(22) -/

/-- Galí (2015), (21), p. 142: the (log) price level relative to its initial value,
`p̂_t ≡ p_t − p_{−1} = ∑_{s ≤ t} π_s`. -/
def priceLevel {α : Type*} [AddCommMonoid α] (infl : ℕ → α) (t : ℕ) : α :=
  ∑ s ∈ Finset.range (t + 1), infl s

/-- Galí (2015), p. 142: `π_t = p̂_t − p̂_{t−1}` (with `p̂_{−1} = 0`). -/
theorem infl_eq_priceLevel_sub {α : Type*} [AddCommGroup α] (infl : ℕ → α) (t : ℕ) :
    infl t = priceLevel infl t - lag (priceLevel infl) t := by
  cases t with
  | zero => simp [priceLevel]
  | succ t =>
    rw [lag_succ, priceLevel, Finset.sum_range_succ _ (t + 1)]
    simp [priceLevel]

/-- Galí (2015), p. 142: the commitment problem's optimality conditions with a distorted
steady state: the Phillips curve (18), `ϑ x̂_t − κ ξ_t − Λ = 0` and `π_t + ξ_t − ξ_{t−1} = 0`
with `ξ_{−1} = 0`, at every date. -/
def CommitmentFOC {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κ ϑ Λ : ℝ)
    (u infl x ξ : ℕ → Ω → ℝ) : Prop :=
  (∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + u t) ∧
    (∀ t, ϑ • x t - κ • ξ t - (fun _ => Λ) = 0) ∧ ∀ t, infl t + ξ t - lag ξ t = 0

/-- Galí (2015), p. 142: eliminating the multiplier, `ξ_t = −p̂_t`. -/
theorem mult_eq_neg_priceLevel {α : Type*} [AddCommGroup α] {infl ξ : ℕ → α}
    (h : ∀ t, infl t + ξ t - lag ξ t = 0) (t : ℕ) : ξ t = -priceLevel infl t := by
  induction t with
  | zero =>
    have h0 := h 0
    rw [lag_zero, sub_zero] at h0
    simp only [priceLevel, zero_add, Finset.sum_range_one]
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h0
  | succ t ih =>
    have h1 := h (t + 1)
    rw [lag_succ, ih] at h1
    rw [priceLevel, Finset.sum_range_succ _ (t + 1), ← sub_eq_zero, ← h1]
    simp only [priceLevel]
    abel

/-- Galí (2015), p. 142: the price level of an adapted inflation process is adapted. -/
theorem priceLevel_adapted {Ω : Type*} (𝔼 : ExpectationSystem Ω) {infl : ℕ → Ω → ℝ}
    (h : 𝔼.Adapted infl) : 𝔼.Adapted (priceLevel infl) := by
  intro t
  unfold priceLevel
  rw [map_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hst : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  rw [← h s]
  exact 𝔼.known hst _

/-- Galí (2015), (21), p. 142: `ϑ x̂_t = −κ p̂_t + Λ`. -/
theorem commitment_eq21 {Ω : Type*} {𝔼 : ExpectationSystem Ω} {β κ ϑ Λ : ℝ}
    {u infl x ξ : ℕ → Ω → ℝ} (hE : CommitmentFOC 𝔼 β κ ϑ Λ u infl x ξ) (t : ℕ) :
    ϑ • x t = -(κ • priceLevel infl t) + fun _ => Λ := by
  have h1 := hE.2.1 t
  rw [mult_eq_neg_priceLevel hE.2.2 t] at h1
  funext ω
  have h2 := congrFun h1 ω
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply] at h2
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  linarith

/-- Galí (2015), (18) and (21), p. 142: pointwise form of the Phillips curve in the price
level, `p̂_t − p̂_{t−1} = β (E_t p̂_{t+1} − p̂_t) + κ x̂_t + u_t`. -/
theorem commitment_core {Ω : Type*} {𝔼 : ExpectationSystem Ω} {β κ ϑ Λ : ℝ}
    {u infl x ξ : ℕ → Ω → ℝ} (hE : CommitmentFOC 𝔼 β κ ϑ Λ u infl x ξ)
    (ha : 𝔼.Adapted infl) (t : ℕ) (ω : Ω) :
    priceLevel infl t ω - lag (priceLevel infl) t ω =
      β * (𝔼.E t (priceLevel infl (t + 1)) ω - priceLevel infl t ω) + κ * x t ω + u t ω := by
  have h1 := hE.1 t
  have hi := infl_eq_priceLevel_sub infl
  rw [hi t, hi (t + 1), lag_succ, map_sub, priceLevel_adapted 𝔼 ha t] at h1
  have h2 := congrFun h1 ω
  simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h2

/-- Galí (2015), (22), p. 142: the price level satisfies
`p̂_t = γ p̂_{t−1} + γβ E_t p̂_{t+1} + γκΛ/ϑ + γ u_t`. -/
theorem commitment_eq22 {Ω : Type*} {𝔼 : ExpectationSystem Ω} {β κ ϑ Λ : ℝ}
    (hβ0 : 0 < β) (hϑ : 0 < ϑ) {u infl x ξ : ℕ → Ω → ℝ}
    (hE : CommitmentFOC 𝔼 β κ ϑ Λ u infl x ξ) (ha : 𝔼.Adapted infl) (t : ℕ) :
    priceLevel infl t = gam β κ ϑ • lag (priceLevel infl) t +
      (gam β κ ϑ * β) • 𝔼.E t (priceLevel infl (t + 1)) +
      (fun _ => gam β κ ϑ * (κ * Λ / ϑ)) + gam β κ ϑ • u t := by
  funext ω
  have hc := commitment_core hE ha t ω
  have hx := congrFun (commitment_eq21 hE t) ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at hx ⊢
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  unfold gam
  field_simp
  linear_combination ϑ * hc + κ * hx

/-! ### The commitment solution, (23)–(24) -/

/-- Galí (2015), (23), p. 142: the coefficient on `u_t`, `b = δ / (1 − δβρ_u)`. -/
noncomputable def commB (β κ ϑ ρ : ℝ) : ℝ := del β κ ϑ / (1 - del β κ ϑ * β * ρ)

/-- Galí (2015), (23), p. 142: the constant `c = (δ / (1 − δβ)) (κΛ/ϑ)`. -/
noncomputable def commConst (β κ ϑ Λ : ℝ) : ℝ := del β κ ϑ / (1 - del β κ ϑ * β) * (κ * Λ / ϑ)

/-- Galí (2015), (24), p. 142: backward recursion `y_0 = w_0`, `y_{t+1} = d y_t + w_{t+1}`. -/
def backRec {α : Type*} [Add α] [SMul ℝ α] (d : ℝ) (w : ℕ → α) : ℕ → α
  | 0 => w 0
  | t + 1 => d • backRec d w t + w (t + 1)

/-- Galí (2015), (24), p. 142: the backward sum `y_t = ∑_{k ≤ t} dᵏ w_{t−k}`. -/
theorem backRec_eq_sum {α : Type*} [AddCommGroup α] [Module ℝ α] (d : ℝ) (w : ℕ → α)
    (t : ℕ) : backRec d w t = ∑ k ∈ Finset.range (t + 1), d ^ k • w (t - k) := by
  induction t with
  | zero => simp [backRec]
  | succ t ih =>
    rw [backRec, ih, Finset.sum_range_succ' _ (t + 1), Finset.smul_sum]
    simp only [pow_zero, one_smul, Nat.sub_zero, smul_smul, ← pow_succ']
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k < t + 1 := Finset.mem_range.mp hk
    congr 2
    omega

/-- Galí (2015), (23), p. 142: the commitment price level, the solution of
`p̂_t = δ p̂_{t−1} + b u_t + c` with `p̂_{−1} = 0`. -/
noncomputable def commPrice {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  backRec (del β κ ϑ) (fun t => commB β κ ϑ ρ • u t + fun _ => commConst β κ ϑ Λ)

/-- Galí (2015), (21), p. 142: the commitment output gap `x̂_t = Λ/ϑ − (κ/ϑ) p̂_t`. -/
noncomputable def commGap {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => Λ / ϑ) - (κ / ϑ) • commPrice β κ ϑ Λ ρ u t

/-- Galí (2015), p. 142: commitment inflation `π_t = p̂_t − p̂_{t−1}`. -/
noncomputable def commInfl {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  commPrice β κ ϑ Λ ρ u t - lag (commPrice β κ ϑ Λ ρ u) t

/-- Galí (2015), p. 142: the commitment multiplier `ξ_t = −p̂_t`. -/
noncomputable def commMult {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  -commPrice β κ ϑ Λ ρ u t

/-- Galí (2015), (23), p. 142: the candidate satisfies
`p̂_t = δ p̂_{t−1} + b u_t + c` at every date, with `p̂_{−1} = 0`. -/
theorem commPrice_eq23 {Ω : Type*} (β κ ϑ Λ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    commPrice β κ ϑ Λ ρ u t = del β κ ϑ • lag (commPrice β κ ϑ Λ ρ u) t +
      commB β κ ϑ ρ • u t + fun _ => commConst β κ ϑ Λ := by
  cases t with
  | zero => simp [commPrice, backRec]
  | succ t => rw [lag_succ, commPrice, backRec, add_assoc]

/-- Galí (2015), p. 142: `b (1 − δβρ_u) = δ`. -/
theorem commB_rel {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hρ : |ρ| ≤ 1) : commB β κ ϑ ρ * (1 - del β κ ϑ * β * ρ) = del β κ ϑ := by
  unfold commB
  exact div_mul_cancel₀ _ (one_sub_del_mul_pos hβ0 hβ1 hκ hϑ hρ).ne'

/-- Galí (2015), p. 142: `c (1 − δβ) = δ κΛ/ϑ`. -/
theorem commConst_rel {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) :
    commConst β κ ϑ Λ * (1 - del β κ ϑ * β) = del β κ ϑ * (κ * Λ / ϑ) := by
  have h := one_sub_del_mul_pos (ρ := 1) hβ0 hβ1 hκ hϑ (by simp)
  rw [mul_one] at h
  unfold commConst
  field_simp

/-- Galí (2015), p. 143: `κ c = (1 − δ) Λ`, i.e. `κ²δΛ / ((1 − δβ)ϑ) = (1 − δ)Λ`, from the
key identity `κ²δ/ϑ = (1 − δ)(1 − βδ)`. -/
theorem kappa_commConst {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) :
    κ * commConst β κ ϑ Λ = (1 - del β κ ϑ) * Λ := by
  have h := one_sub_del_mul_pos (ρ := 1) hβ0 hβ1 hκ hϑ (by simp)
  rw [mul_one] at h
  have hk : κ ^ 2 * del β κ ϑ = ϑ * ((1 - del β κ ϑ) * (1 - β * del β κ ϑ)) := by
    rw [← kappa_sq_del hβ0 hβ1 hϑ]; field_simp
  unfold commConst
  field_simp
  linear_combination Λ * hk

/-- Galí (2015), p. 142: `b (ϑ(1 + β − βδ − βρ_u) + κ²) = ϑ` (the `u_t` coefficient identity
behind (23)). -/
theorem commB_X {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hρ : |ρ| ≤ 1) :
    commB β κ ϑ ρ * (ϑ * (1 + β - β * del β κ ϑ - β * ρ) + κ ^ 2) = ϑ := by
  have h := one_sub_del_mul_pos hβ0 hβ1 hκ hϑ hρ
  have hk : κ ^ 2 * del β κ ϑ = ϑ * ((1 - del β κ ϑ) * (1 - β * del β κ ϑ)) := by
    rw [← kappa_sq_del hβ0 hβ1 hϑ]; field_simp
  unfold commB
  field_simp
  linear_combination hk

/-- Galí (2015), p. 142: `c (ϑ(1 − βδ) + κ²) = κΛ` (the constant identity behind (23)). -/
theorem commConst_X {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) :
    commConst β κ ϑ Λ * (ϑ * (1 - β * del β κ ϑ) + κ ^ 2) = κ * Λ := by
  have h1 := kappa_commConst (Λ := Λ) hβ0 hβ1 hκ hϑ
  have h2 := commConst_rel (Λ := Λ) hβ0 hβ1 hκ hϑ
  have h3 : ϑ * (del β κ ϑ * (κ * Λ / ϑ)) = del β κ ϑ * (κ * Λ) := by
    field_simp
  linear_combination ϑ * h2 + κ * h1 + h3

/-- Galí (2015), (23), p. 142: the commitment price level is adapted. -/
theorem commPrice_adapted {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κ ϑ Λ ρ : ℝ)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) : 𝔼.Adapted (commPrice β κ ϑ Λ ρ u) := by
  intro t
  induction t with
  | zero =>
    change 𝔼.E 0 (commB β κ ϑ ρ • u 0 + fun _ => commConst β κ ϑ Λ) = _
    rw [map_add, 𝔼.E_smul, hu 0, 𝔼.const]
    rfl
  | succ t ih =>
    change 𝔼.E (t + 1) (del β κ ϑ • commPrice β κ ϑ Λ ρ u t +
      (commB β κ ϑ ρ • u (t + 1) + fun _ => commConst β κ ϑ Λ)) = _
    rw [map_add, map_add, 𝔼.E_smul, 𝔼.E_smul, hu (t + 1), 𝔼.const, ← ih,
      𝔼.known (Nat.le_succ t), ih]
    rfl

/-- Galí (2015), (23), p. 142: `E_t p̂_{t+1} = δ p̂_t + bρ_u u_t + c` along the commitment
solution. -/
theorem commPrice_E_succ {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κ ϑ Λ ρ : ℝ)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (t : ℕ) :
    𝔼.E t (commPrice β κ ϑ Λ ρ u (t + 1)) = del β κ ϑ • commPrice β κ ϑ Λ ρ u t +
      (commB β κ ϑ ρ * ρ) • u t + fun _ => commConst β κ ϑ Λ := by
  change 𝔼.E t (del β κ ϑ • commPrice β κ ϑ Λ ρ u t +
      (commB β κ ϑ ρ • u (t + 1) + fun _ => commConst β κ ϑ Λ)) = _
  rw [map_add, map_add, 𝔼.E_smul, 𝔼.E_smul, hu.2 t, 𝔼.const,
    commPrice_adapted 𝔼 β κ ϑ Λ ρ hu.1 t, smul_smul, add_assoc]

/-- Galí (2015), (21), p. 142: `ϑ x̂_t = Λ − κ p̂_t` along the commitment solution. -/
theorem commGap_mul {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hϑ : 0 < ϑ) (u : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : ϑ * commGap β κ ϑ Λ ρ u t ω = Λ - κ * commPrice β κ ϑ Λ ρ u t ω := by
  unfold commGap
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Galí (2015), (23)–(24), p. 142: the commitment price level is bounded for a bounded
cost-push process. -/
theorem commPrice_bounded {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) {u : ℕ → Ω → ℝ} (hub : BoundedProc u) :
    BoundedProc (commPrice β κ ϑ Λ ρ u) := by
  obtain ⟨M, hM⟩ := hub
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  set d := del β κ ϑ
  set N := |commB β κ ϑ ρ| * |M| + |commConst β κ ϑ Λ|
  have hN : 0 ≤ N := by positivity
  have hw : ∀ t ω, |(commB β κ ϑ ρ • u t + fun _ => commConst β κ ϑ Λ : Ω → ℝ) ω| ≤ N := by
    intro t ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := (hM t ω).trans (le_abs_self M)
    have := mul_le_mul_of_nonneg_left this (abs_nonneg (commB β κ ϑ ρ))
    simp only [N]
    linarith
  refine ⟨N / (1 - d), fun t ω => ?_⟩
  have hK : N ≤ N / (1 - d) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  induction t with
  | zero => exact (hw 0 ω).trans hK
  | succ t ih =>
    change |(d • commPrice β κ ϑ Λ ρ u t +
      (commB β κ ϑ ρ • u (t + 1) + fun _ => commConst β κ ϑ Λ) : Ω → ℝ) ω| ≤ _
    rw [Pi.add_apply]
    refine (abs_add_le _ _).trans ?_
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos h0]
    have := hw (t + 1) ω
    have hd1 : 1 - d ≠ 0 := (by linarith : (0 : ℝ) < 1 - d).ne'
    have hdK : d * (N / (1 - d)) + N = N / (1 - d) := by
      field_simp; ring
    nlinarith

/-- Galí (2015), (21)–(23), p. 142: **existence**. The commitment paths built from (23)
satisfy the Phillips curve and both optimality conditions, are adapted, and are bounded
(bounded AR(1) cost-push process, `0 < β < 1`, `κ, ϑ > 0`, `|ρ_u| ≤ 1`). -/
theorem commitment_exists {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ ρ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) :
    CommitmentFOC 𝔼 β κ ϑ Λ u (commInfl β κ ϑ Λ ρ u) (commGap β κ ϑ Λ ρ u)
        (commMult β κ ϑ Λ ρ u) ∧
      𝔼.Adapted (commInfl β κ ϑ Λ ρ u) ∧ BoundedProc (commPrice β κ ϑ Λ ρ u) ∧
      BoundedProc (commGap β κ ϑ Λ ρ u) ∧ BoundedProc (commInfl β κ ϑ Λ ρ u) := by
  have hPa := commPrice_adapted 𝔼 β κ ϑ Λ ρ hu.1
  obtain ⟨K, hK⟩ := commPrice_bounded (Λ := Λ) (ρ := ρ) hβ0 hβ1 hκ hϑ hub
  have hlagK : ∀ t ω, |lag (commPrice β κ ϑ Λ ρ u) t ω| ≤ |K| := by
    intro t ω
    cases t with
    | zero => simp
    | succ t => exact (hK t ω).trans (le_abs_self K)
  refine ⟨⟨fun t => ?_, fun t => ?_, fun t => ?_⟩, fun t => ?_, ⟨K, hK⟩, ?_, ?_⟩
  · funext ω
    have hE : 𝔼.E t (commInfl β κ ϑ Λ ρ u (t + 1)) ω =
        del β κ ϑ * commPrice β κ ϑ Λ ρ u t ω + commB β κ ϑ ρ * ρ * u t ω +
          commConst β κ ϑ Λ - commPrice β κ ϑ Λ ρ u t ω := by
      unfold commInfl
      rw [lag_succ, map_sub, commPrice_E_succ 𝔼 β κ ϑ Λ ρ hu t, hPa t]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hP := congrFun (commPrice_eq23 β κ ϑ Λ ρ u t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hP
    have hx := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u t ω
    have hk : κ ^ 2 * del β κ ϑ = ϑ * ((1 - del β κ ϑ) * (1 - β * del β κ ϑ)) := by
      rw [← kappa_sq_del hβ0 hβ1 hϑ]; field_simp
    have hB := commB_X hβ0 hβ1 hκ hϑ hρ
    have hC := commConst_X (Λ := Λ) hβ0 hβ1 hκ hϑ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hE]
    unfold commInfl
    simp only [Pi.sub_apply]
    apply mul_left_cancel₀ hϑ.ne'
    linear_combination (ϑ * (1 - β * del β κ ϑ + β) + κ ^ 2) * hP - κ * hx +
      lag (commPrice β κ ϑ Λ ρ u) t ω * hk + u t ω * hB + hC
  · funext ω
    have hx := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u t ω
    unfold commMult
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination hx
  · funext ω
    cases t with
    | zero => simp [commInfl, commMult]
    | succ t =>
      simp only [commInfl, commMult, lag_succ, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
        Pi.zero_apply]
      ring
  · unfold commInfl
    rw [map_sub, hPa t, lag_adapted 𝔼 hPa t]
  · refine ⟨|Λ / ϑ| + |κ / ϑ| * K, fun t ω => ?_⟩
    unfold commGap
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    gcongr
    exact hK t ω
  · refine ⟨K + |K|, fun t ω => ?_⟩
    unfold commInfl
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hK t ω) (hlagK t ω))

/-- Galí (2015), (21)–(23), p. 142: **uniqueness**. Any adapted solution of the commitment
optimality conditions with a bounded output gap coincides with the commitment paths of (23):
price level, inflation, output gap and multiplier. -/
theorem commitment_unique {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ ρ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1)
    {u infl x ξ : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    (hE : CommitmentFOC 𝔼 β κ ϑ Λ u infl x ξ) (ha : 𝔼.Adapted infl) (hb : BoundedProc x) :
    priceLevel infl = commPrice β κ ϑ Λ ρ u ∧ infl = commInfl β κ ϑ Λ ρ u ∧
      x = commGap β κ ϑ Λ ρ u ∧ ξ = commMult β κ ϑ Λ ρ u := by
  set P := priceLevel infl with hPdef
  set d := del β κ ϑ with hd
  set b := commB β κ ϑ ρ
  set c := commConst β κ ϑ Λ
  have h0 : 0 < d := del_pos hβ0 hϑ
  have h1 : d < 1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hPa : 𝔼.Adapted P := priceLevel_adapted 𝔼 ha
  have hx : ∀ t ω, ϑ * x t ω = Λ - κ * P t ω := by
    intro t ω
    have := congrFun (commitment_eq21 hE t) ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at this
    linarith
  obtain ⟨M, hM⟩ := hb
  have hPb : ∀ t ω, |P t ω| ≤ (|Λ| + ϑ * M) / κ := by
    intro t ω
    rw [le_div_iff₀ hκ]
    have h2 : κ * P t ω = Λ - ϑ * x t ω := by linarith [hx t ω]
    have h3 : |κ * P t ω| ≤ |Λ| + ϑ * M := by
      rw [h2]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_pos hϑ]
      gcongr
      exact hM t ω
    rw [abs_mul, abs_of_pos hκ] at h3
    linarith
  set K := (|Λ| + ϑ * M) / κ
  have hlagb : ∀ t ω, |lag P t ω| ≤ |K| := by
    intro t ω
    cases t with
    | zero => simp
    | succ t => exact (hPb t ω).trans (le_abs_self K)
  -- the quasi-difference z_t = p̂_t − δ p̂_{t−1} solves a stable forward equation
  set z : ℕ → Ω → ℝ := fun t => P t - d • lag P t with hz
  set w : ℕ → Ω → ℝ := fun t => (fun _ => d * (κ * Λ / ϑ)) + d • u t with hw
  set zc : ℕ → Ω → ℝ := fun t => b • u t + fun _ => c with hzc
  have hkl : ϑ * (κ * Λ / ϑ) = κ * Λ := by field_simp
  have hk : κ ^ 2 * del β κ ϑ = ϑ * ((1 - del β κ ϑ) * (1 - β * del β κ ϑ)) := by
    rw [← kappa_sq_del hβ0 hβ1 hϑ]; field_simp
  have hzeq : ∀ t, z t = (d * β) • 𝔼.E t (z (t + 1)) + w t := by
    intro t
    funext ω
    have hc := commitment_core hE ha t ω
    have hEz : 𝔼.E t (z (t + 1)) ω = 𝔼.E t (P (t + 1)) ω - d * P t ω := by
      simp only [hz, lag_succ, map_sub, 𝔼.E_smul, hPa t, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hEz]
    simp only [hz, hw, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    apply mul_left_cancel₀ hϑ.ne'
    linear_combination (d * ϑ) * hc - P t ω * hk + (d * κ) * hx t ω - d * hkl
  have hzceq : ∀ t, zc t = (d * β) • 𝔼.E t (zc (t + 1)) + w t := by
    intro t
    have hB := commB_rel hβ0 hβ1 hκ hϑ hρ
    have hC := commConst_rel (Λ := Λ) hβ0 hβ1 hκ hϑ
    have hEz : 𝔼.E t (zc (t + 1)) = (b * ρ) • u t + fun _ => c := by
      simp only [hzc, map_add, 𝔼.E_smul, hu.2 t, 𝔼.const, smul_smul]
    rw [hEz]
    funext ω
    simp only [hzc, hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * hB + hC
  have hdb : |d * β| < 1 := by
    rw [abs_of_pos (mul_pos h0 hβ0)]; nlinarith
  have hzb : BoundedProc z := by
    refine ⟨K + d * |K|, fun t ω => ?_⟩
    simp only [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hPb t ω) ?_)
    rw [abs_mul, abs_of_pos h0]
    exact mul_le_mul_of_nonneg_left (hlagb t ω) h0.le
  have hzcb : BoundedProc zc := by
    obtain ⟨Mu, hMu⟩ := hub
    refine ⟨|b| * Mu + |c|, fun t ω => ?_⟩
    simp only [hzc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_left (hMu t ω) (abs_nonneg b)
    linarith
  have hzz : z = zc := 𝔼.forward_unique hdb hzeq hzceq hzb hzcb
  have hPeq : P = commPrice β κ ϑ Λ ρ u := by
    funext t
    induction t with
    | zero =>
      have := congrFun hzz 0
      simp only [hz, hzc, lag_zero, smul_zero, sub_zero] at this
      rw [this]
      rfl
    | succ t ih =>
      have := congrFun hzz (t + 1)
      simp only [hz, hzc, lag_succ] at this
      rw [sub_eq_iff_eq_add] at this
      rw [this, ih, add_comm]
      rfl
  refine ⟨hPeq, ?_, ?_, ?_⟩
  · funext t
    rw [infl_eq_priceLevel_sub infl t, ← hPdef, hPeq]
    rfl
  · funext t ω
    have h2 := hx t ω
    have h3 := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u t ω
    rw [hPeq] at h2
    apply mul_left_cancel₀ hϑ.ne'
    rw [h2, h3]
  · funext t
    rw [mult_eq_neg_priceLevel hE.2.2 t, ← hPdef, hPeq]
    rfl

/-- Galí (2015), (23), p. 142: along the (unique bounded) commitment equilibrium,
`p̂_t = δ p̂_{t−1} + δ/(1 − δβρ_u) u_t + (δ/(1 − δβ)) κΛ/ϑ`. -/
theorem commitment_eq23 {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ ρ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1)
    {u infl x ξ : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    (hE : CommitmentFOC 𝔼 β κ ϑ Λ u infl x ξ) (ha : 𝔼.Adapted infl) (hb : BoundedProc x)
    (t : ℕ) :
    priceLevel infl t = del β κ ϑ • lag (priceLevel infl) t +
      (del β κ ϑ / (1 - del β κ ϑ * β * ρ)) • u t +
      fun _ => del β κ ϑ / (1 - del β κ ϑ * β) * (κ * Λ / ϑ) := by
  rw [(commitment_unique 𝔼 hβ0 hβ1 hκ hϑ hρ hu hub hE ha hb).1]
  exact commPrice_eq23 β κ ϑ Λ ρ u t

/-- Galí (2015), (24), p. 142: solving (23) backward,
`p̂_t = ((1 − δ^{t+1})/(1 − δ)) (δ/(1 − δβ)) (κΛ/ϑ) + (δ/(1 − δβρ_u)) ∑_{k ≤ t} δᵏ u_{t−k}`. -/
theorem commitment_eq24 {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    commPrice β κ ϑ Λ ρ u t =
      (fun _ => (1 - del β κ ϑ ^ (t + 1)) / (1 - del β κ ϑ) *
        (del β κ ϑ / (1 - del β κ ϑ * β) * (κ * Λ / ϑ))) +
      (del β κ ϑ / (1 - del β κ ϑ * β * ρ)) •
        ∑ k ∈ Finset.range (t + 1), del β κ ϑ ^ k • u (t - k) := by
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hne : del β κ ϑ - 1 ≠ 0 := (by linarith : del β κ ϑ - 1 < 0).ne
  have hne' : 1 - del β κ ϑ ≠ 0 := (by linarith : (0 : ℝ) < 1 - del β κ ϑ).ne'
  unfold commPrice
  rw [backRec_eq_sum]
  funext ω
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  rw [← Finset.sum_mul, geom_sum_eq (by linarith) (t + 1), Finset.mul_sum, add_comm]
  congr 1
  · unfold commConst
    field_simp
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    unfold commB
    ring

/-! ### The output gap under commitment, (25)–(27), corrected -/

/-- Galí (2015), (25), p. 143: `x̂_{t+1} = δ x̂_t − (κδ/(ϑ(1 − δβρ_u))) u_{t+1}` along the
commitment solution. -/
theorem commGap_eq25 {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (u : ℕ → Ω → ℝ) (t : ℕ) :
    commGap β κ ϑ Λ ρ u (t + 1) = del β κ ϑ • commGap β κ ϑ Λ ρ u t -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) • u (t + 1) := by
  funext ω
  have hx1 := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u (t + 1) ω
  have hx0 := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u t ω
  have hP := congrFun (commPrice_eq23 β κ ϑ Λ ρ u (t + 1)) ω
  simp only [lag_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hP
  have hkc := kappa_commConst (Λ := Λ) hβ0 hβ1 hκ hϑ
  have hpos := one_sub_del_mul_pos hβ0 hβ1 hκ hϑ hρ
  have hcoef : ϑ * (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) = κ * commB β κ ϑ ρ := by
    unfold commB; field_simp
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hϑ.ne'
  linear_combination hx1 - del β κ ϑ * hx0 + u (t + 1) ω * hcoef - κ * hP - hkc

/-- Galí (2015), (26) **corrected**, p. 143: along the commitment solution
`x̂_0 = δΛ/ϑ − (κδ/(ϑ(1 − δβρ_u))) u_0` (the book prints `(1 − δ)Λ/ϑ` as the constant). -/
theorem commGap_eq26_corrected {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (u : ℕ → Ω → ℝ) :
    commGap β κ ϑ Λ ρ u 0 = (fun _ => del β κ ϑ * Λ / ϑ) -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) • u 0 := by
  funext ω
  have hx0 := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u 0 ω
  have hP := congrFun (commPrice_eq23 β κ ϑ Λ ρ u 0) ω
  simp only [lag_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hP
  have hkc := kappa_commConst (Λ := Λ) hβ0 hβ1 hκ hϑ
  have hpos := one_sub_del_mul_pos hβ0 hβ1 hκ hϑ hρ
  have hcoef : ϑ * (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) = κ * commB β κ ϑ ρ := by
    unfold commB; field_simp
  have hdl : ϑ * (del β κ ϑ * Λ / ϑ) = del β κ ϑ * Λ := by field_simp
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hϑ.ne'
  linear_combination hx0 - hdl + u 0 ω * hcoef - κ * hP - hkc

/-- Galí (2015), (27) **corrected**, p. 143: along the commitment solution
`x̂_t = δ^{t+1}Λ/ϑ − (κδ/(ϑ(1 − δβρ_u))) ∑_{k ≤ t} δᵏ u_{t−k}`. -/
theorem commGap_eq27_corrected {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (u : ℕ → Ω → ℝ) (t : ℕ) :
    commGap β κ ϑ Λ ρ u t = (fun _ => del β κ ϑ ^ (t + 1) * Λ / ϑ) -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) •
        ∑ k ∈ Finset.range (t + 1), del β κ ϑ ^ k • u (t - k) := by
  funext ω
  have hx := commGap_mul (Λ := Λ) (ρ := ρ) (β := β) (κ := κ) hϑ u t ω
  have hP := congrFun (commitment_eq24 (Λ := Λ) (ρ := ρ) hβ0 hβ1 hκ hϑ u t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hP
  have hkc := kappa_commConst (Λ := Λ) hβ0 hβ1 hκ hϑ
  have hpos := one_sub_del_mul_pos hβ0 hβ1 hκ hϑ hρ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hne' : 1 - del β κ ϑ ≠ 0 := (by linarith : (0 : ℝ) < 1 - del β κ ϑ).ne'
  have hS : κ * ((1 - del β κ ϑ ^ (t + 1)) / (1 - del β κ ϑ) *
      (del β κ ϑ / (1 - del β κ ϑ * β) * (κ * Λ / ϑ))) = (1 - del β κ ϑ ^ (t + 1)) * Λ := by
    have : κ * (del β κ ϑ / (1 - del β κ ϑ * β) * (κ * Λ / ϑ)) = (1 - del β κ ϑ) * Λ := by
      rw [← hkc]; rfl
    calc _ = (1 - del β κ ϑ ^ (t + 1)) / (1 - del β κ ϑ) *
          (κ * (del β κ ϑ / (1 - del β κ ϑ * β) * (κ * Λ / ϑ))) := by ring
      _ = _ := by rw [this]; field_simp
  have hcoef : ϑ * (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) =
      κ * (del β κ ϑ / (1 - del β κ ϑ * β * ρ)) := by
    field_simp
  have hdl : ϑ * (del β κ ϑ ^ (t + 1) * Λ / ϑ) = del β κ ϑ ^ (t + 1) * Λ := by field_simp
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hϑ.ne'
  linear_combination hx - hdl + (∑ k ∈ Finset.range (t + 1), del β κ ϑ ^ k • u (t - k)) ω * hcoef -
    κ * hP - hS

/-- Galí (2015), (25)–(27), p. 143, for the commitment equilibrium itself: any adapted
solution of the commitment conditions with bounded output gap satisfies (25), the corrected
(26) and the corrected (27). -/
theorem commitment_eq25_eq27 {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ϑ Λ ρ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1)
    {u infl x ξ : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    (hE : CommitmentFOC 𝔼 β κ ϑ Λ u infl x ξ) (ha : 𝔼.Adapted infl) (hb : BoundedProc x) :
    (∀ t, x (t + 1) = del β κ ϑ • x t -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) • u (t + 1)) ∧
    x 0 = (fun _ => del β κ ϑ * Λ / ϑ) -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) • u 0 ∧
    ∀ t, x t = (fun _ => del β κ ϑ ^ (t + 1) * Λ / ϑ) -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) •
        ∑ k ∈ Finset.range (t + 1), del β κ ϑ ^ k • u (t - k) := by
  rw [(commitment_unique 𝔼 hβ0 hβ1 hκ hϑ hρ hu hub hE ha hb).2.2.1]
  exact ⟨commGap_eq25 hβ0 hβ1 hκ hϑ hρ u, commGap_eq26_corrected hβ0 hβ1 hκ hϑ hρ u,
    commGap_eq27_corrected hβ0 hβ1 hκ hϑ hρ u⟩

/-! ### The printed (26)–(27) are false -/

/-- Galí (2015), (26), p. 143, as printed, is false: without cost-push shocks (`u ≡ 0`) and
with `Λ ≠ 0`, the commitment output gap at `t = 0` equals the printed `(1 − δ)Λ/ϑ` if and
only if `δ = 1/2`. (The correct value is `δΛ/ϑ`.) -/
theorem printed_eq26_iff {Ω : Type*} [Nonempty Ω] {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (hΛ : Λ ≠ 0) :
    commGap β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) 0 = (fun _ => (1 - del β κ ϑ) * Λ / ϑ) ↔
      del β κ ϑ = 1 / 2 := by
  rw [commGap_eq26_corrected hβ0 hβ1 hκ hϑ hρ]
  simp only [Pi.zero_apply, smul_zero, sub_zero]
  constructor
  · intro h
    have h2 := congrFun h (Classical.arbitrary Ω)
    field_simp at h2
    linarith
  · intro h
    funext ω
    rw [h]
    ring

/-- Galí (2015), (27), p. 143, as printed (deterministic term `(1 − δ)δᵗΛ/ϑ`), is false: with
`u ≡ 0` and `Λ ≠ 0`, the commitment output gap at date `t` equals the printed value if and only
if `δ = 1/2`. (The correct deterministic term is `δ^{t+1}Λ/ϑ`.) -/
theorem printed_eq27_iff {Ω : Type*} [Nonempty Ω] {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (hΛ : Λ ≠ 0) (t : ℕ) :
    commGap β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t =
        (fun _ => (1 - del β κ ϑ) * del β κ ϑ ^ t * Λ / ϑ) ↔ del β κ ϑ = 1 / 2 := by
  rw [commGap_eq27_corrected hβ0 hβ1 hκ hϑ hρ]
  have h0 := del_pos (κ := κ) hβ0 hϑ
  simp only [Pi.zero_apply, smul_zero, Finset.sum_const_zero, sub_zero]
  constructor
  · intro h
    have h2 := congrFun h (Classical.arbitrary Ω)
    field_simp at h2
    have hp : 0 < del β κ ϑ ^ t := pow_pos h0 t
    have : (2 * del β κ ϑ - 1) * del β κ ϑ ^ t = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h3 | h3
    · linarith
    · linarith
  · intro h
    funext ω
    rw [h, pow_succ]
    ring

/-- Galí (2015), (27), p. 143, read with the sum over `k` also applied to the deterministic
term: `∑_{k ≤ t} (1 − δ)δᵏΛ/ϑ = (1 − δ^{t+1})Λ/ϑ`, which tends to `Λ/ϑ`, not to `0`; so this
reading contradicts the book's own `lim x̂_T = 0` (and its `t = 0` term is the false (26)). -/
theorem printed_eq27_sum_tendsto {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) :
    Tendsto (fun t : ℕ => ∑ k ∈ Finset.range (t + 1), (1 - del β κ ϑ) * del β κ ϑ ^ k * Λ / ϑ)
      atTop (𝓝 (Λ / ϑ)) := by
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hne : del β κ ϑ - 1 ≠ 0 := (by linarith : del β κ ϑ - 1 < 0).ne
  have heq : ∀ t : ℕ, ∑ k ∈ Finset.range (t + 1), (1 - del β κ ϑ) * del β κ ϑ ^ k * Λ / ϑ =
      (1 - del β κ ϑ ^ (t + 1)) * (Λ / ϑ) := by
    intro t
    simp only [mul_div_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [geom_sum_eq (by linarith) (t + 1)]
    field_simp
    ring
  simp only [heq]
  have hp : Tendsto (fun t : ℕ => del β κ ϑ ^ (t + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).comp (tendsto_add_atTop_nat 1)
  simpa using (hp.const_sub 1).mul_const (Λ / ϑ)

/-- Galí (2015), p. 142: a parameter point at which `δ = 1/4`: `β = 1/2`, `κ = 1`,
`ϑ = 8/21` (then `γ = 8/33` and `√(1 − 4βγ²) = 31/33`). -/
theorem del_example : del (1 / 2) 1 (8 / 21) = 1 / 4 := by
  unfold del gam
  have h : (1 : ℝ) - 4 * (1 / 2) * (8 / 21 / (8 / 21 * (1 + 1 / 2) + 1 ^ 2)) ^ 2 =
      (31 / 33) ^ 2 := by norm_num
  rw [h, Real.sqrt_sq (by norm_num)]
  norm_num

/-- Galí (2015), (26)–(27), p. 143: **counterexample** to the printed formulas. With
`β = 1/2`, `κ = 1`, `ϑ = 8/21`, `Λ = 1` and no cost-push shocks, the commitment equilibrium has
`x̂_0 = δΛ/ϑ = 21/32`, whereas the printed (26) gives `(1 − δ)Λ/ϑ = 63/32`. -/
theorem printed_eq26_false :
    commGap (1 / 2) 1 (8 / 21) 1 0 (0 : ℕ → Unit → ℝ) 0 () = 21 / 32 ∧
      (1 - del (1 / 2) 1 (8 / 21)) * 1 / (8 / 21) = 63 / 32 ∧
      commGap (1 / 2) 1 (8 / 21) 1 0 (0 : ℕ → Unit → ℝ) 0 () ≠
        (1 - del (1 / 2) 1 (8 / 21)) * 1 / (8 / 21) := by
  have h := congrFun (commGap_eq26_corrected (Λ := 1) (ρ := 0) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 8 / 21) (by norm_num)
    (0 : ℕ → Unit → ℝ)) ()
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply] at h
  rw [h, del_example]
  norm_num

/-! ### No long-run inflation bias under commitment -/

/-- Galí (2015), (24), p. 142, with `u ≡ 0`:
`p̂_t = ((1 − δ^{t+1})/(1 − δ)) (δ/(1 − δβ)) κΛ/ϑ`. -/
theorem commPrice_zeroShock {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (t : ℕ) :
    commPrice β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t =
      fun _ => (1 - del β κ ϑ ^ (t + 1)) / (1 - del β κ ϑ) * commConst β κ ϑ Λ := by
  rw [commitment_eq24 hβ0 hβ1 hκ hϑ]
  funext ω
  simp only [Pi.zero_apply, smul_zero, Finset.sum_const_zero, add_zero, commConst]

/-- Galí (2015), (27) corrected, p. 143, with `u ≡ 0`: `x̂_t = δ^{t+1}Λ/ϑ`. -/
theorem commGap_zeroShock {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (t : ℕ) :
    commGap β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t = fun _ => del β κ ϑ ^ (t + 1) * Λ / ϑ := by
  rw [commGap_eq27_corrected hβ0 hβ1 hκ hϑ hρ]
  funext ω
  simp

/-- Galí (2015), p. 143, with `u ≡ 0`: commitment inflation is `π_t = δᵗ c`,
`c = (δ/(1 − δβ)) κΛ/ϑ`. -/
theorem commInfl_zeroShock {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (t : ℕ) :
    commInfl β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t = fun _ => del β κ ϑ ^ t * commConst β κ ϑ Λ := by
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hne' : 1 - del β κ ϑ ≠ 0 := (by linarith : (0 : ℝ) < 1 - del β κ ϑ).ne'
  unfold commInfl
  funext ω
  cases t with
  | zero =>
    simp only [lag_zero, Pi.sub_apply, Pi.zero_apply, sub_zero, pow_zero, one_mul]
    rw [commPrice_zeroShock hβ0 hβ1 hκ hϑ]
    field_simp
    ring
  | succ t =>
    simp only [lag_succ, Pi.sub_apply]
    rw [commPrice_zeroShock hβ0 hβ1 hκ hϑ, commPrice_zeroShock hβ0 hβ1 hκ hϑ]
    field_simp
    ring

/-- Galí (2015), p. 143: with `u ≡ 0` the price level converges,
`lim p̂_T = δκΛ / ((1 − δβ)(1 − δ)ϑ)`. -/
theorem tendsto_priceLevel_zeroShock {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hϑ : 0 < ϑ) (ω : Ω) :
    Tendsto (fun t => commPrice β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω) atTop
      (𝓝 (del β κ ϑ * κ * Λ / ((1 - del β κ ϑ * β) * (1 - del β κ ϑ) * ϑ))) := by
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hne' : 1 - del β κ ϑ ≠ 0 := (by linarith : (0 : ℝ) < 1 - del β κ ϑ).ne'
  have hb := one_sub_del_mul_pos (ρ := 1) hβ0 hβ1 hκ hϑ (by simp)
  simp only [commPrice_zeroShock hβ0 hβ1 hκ hϑ]
  have hp : Tendsto (fun t : ℕ => del β κ ϑ ^ (t + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).comp (tendsto_add_atTop_nat 1)
  have := ((hp.const_sub 1).div_const (1 - del β κ ϑ)).mul_const (commConst β κ ϑ Λ)
  convert this using 2
  unfold commConst
  rw [mul_one] at hb
  field_simp
  ring

/-- Galí (2015), p. 143: in the long run the marginal benefit of output equals the cost of
cumulative inflation, `κ lim p̂_T = Λ`. -/
theorem kappa_limit_priceLevel {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) :
    κ * (del β κ ϑ * κ * Λ / ((1 - del β κ ϑ * β) * (1 - del β κ ϑ) * ϑ)) = Λ := by
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hne' : 1 - del β κ ϑ ≠ 0 := (by linarith : (0 : ℝ) < 1 - del β κ ϑ).ne'
  have hb := one_sub_del_mul_pos (ρ := 1) hβ0 hβ1 hκ hϑ (by simp)
  rw [mul_one] at hb
  have hk : κ ^ 2 * del β κ ϑ = ϑ * ((1 - del β κ ϑ) * (1 - β * del β κ ϑ)) := by
    rw [← kappa_sq_del hβ0 hβ1 hϑ]; field_simp
  field_simp
  linear_combination Λ * hk

/-- Galí (2015), p. 143: with `u ≡ 0`, `lim x̂_T = 0`: output returns to its natural level
under commitment (no long-run output bias). -/
theorem tendsto_gap_zeroShock {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (ω : Ω) :
    Tendsto (fun t => commGap β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω) atTop (𝓝 0) := by
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  simp only [commGap_zeroShock hβ0 hβ1 hκ hϑ hρ]
  have hp : Tendsto (fun t : ℕ => del β κ ϑ ^ (t + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).comp (tendsto_add_atTop_nat 1)
  simpa using (hp.mul_const Λ).div_const ϑ

/-- Galí (2015), p. 143: with `u ≡ 0`, commitment inflation converges to zero: no long-run
inflation bias. -/
theorem tendsto_infl_zeroShock {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (ω : Ω) :
    Tendsto (fun t => commInfl β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω) atTop (𝓝 0) := by
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have h1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  simp only [commInfl_zeroShock hβ0 hβ1 hκ hϑ]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).mul_const (commConst β κ ϑ Λ)

/-- Galí (2015), p. 143: with `u ≡ 0` and `Λ > 0`, output and inflation stay above their
steady-state values at every date (`x̂_t > 0`, `π_t > 0`): persistent deterministic
transitional dynamics. -/
theorem commitment_zeroShock_pos {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hϑ : 0 < ϑ) (hρ : |ρ| ≤ 1) (hΛ : 0 < Λ) (t : ℕ) (ω : Ω) :
    0 < commGap β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω ∧ 0 < commInfl β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω := by
  have h0 := del_pos (κ := κ) hβ0 hϑ
  have hb := one_sub_del_mul_pos (ρ := 1) hβ0 hβ1 hκ hϑ (by simp)
  rw [mul_one] at hb
  rw [commGap_zeroShock hβ0 hβ1 hκ hϑ hρ, commInfl_zeroShock hβ0 hβ1 hκ hϑ]
  unfold commConst
  constructor <;> positivity

/-- Galí (2015), pp. 143–144: commitment versus discretion without cost-push shocks. Under
discretion inflation equals the bias `π̄ > 0` at every date; under commitment it converges to
zero, so it eventually falls (and stays) below `π̄`. -/
theorem commitment_vs_discretion_longrun {Ω : Type*} {β κ ϑ Λ ρ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hΛ : 0 < Λ) (ω : Ω) :
    (∀ t, discInfl β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω = inflationBias β κ ϑ Λ) ∧
      0 < inflationBias β κ ϑ Λ ∧
      ∀ᶠ t in atTop, commInfl β κ ϑ Λ ρ (0 : ℕ → Ω → ℝ) t ω < inflationBias β κ ϑ Λ := by
  have hpos := inflationBias_pos hβ1 hκ hϑ hΛ
  refine ⟨fun t => by rw [discretion_zeroShock], hpos, ?_⟩
  exact (tendsto_infl_zeroShock hβ0 hβ1 hκ hϑ ω).eventually (gt_mem_nhds hpos)

/-! ### Optimality of the commitment plan in the deterministic problem -/

/-- Galí (2015), p. 141: a bounded real sequence (the admissible paths of the deterministic
problem). -/
def BddSeq (s : ℕ → ℝ) : Prop := ∃ M, ∀ t, |s t| ≤ M

/-- Galí (2015), (18), p. 139, under perfect foresight: a path `(π, x̂)` is feasible when
`π_t = β π_{t+1} + κ x̂_t + u_t` at every date. -/
def DetFeasible (β κ : ℝ) (u infl x : ℕ → ℝ) : Prop :=
  ∀ t, infl t = β * infl (t + 1) + κ * x t + u t

/-- Galí (2015), p. 142: the Lagrangian first-order conditions `ϑ x̂_t − κ ξ_t − Λ = 0`,
`π_t + ξ_t − ξ_{t−1} = 0`, `ξ_{−1} = 0`. -/
def DetFOC (κ ϑ Λ : ℝ) (infl x ξ : ℕ → ℝ) : Prop :=
  (∀ t, ϑ * x t - κ * ξ t - Λ = 0) ∧ ∀ t, infl t + ξ t - lag ξ t = 0

/-- Galí (2015), (17), p. 139, under perfect foresight: the discounted loss
`∑ βᵗ (½(π_t² + ϑ x̂_t²) − Λ x̂_t)`. -/
noncomputable def detLoss (β ϑ Λ : ℝ) (infl x : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * periodLoss ϑ Λ (infl t) (x t)

/-- Galí (2015), (17), p. 139: the period loss is bounded on bounded arguments. -/
theorem abs_periodLoss_le {ϑ Λ a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |periodLoss ϑ Λ a b| ≤ (A ^ 2 + |ϑ| * B ^ 2) / 2 + |Λ| * B := by
  have hA : a ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hB : b ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg b) hb 2
  unfold periodLoss
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_two]
    gcongr
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg a), abs_of_nonneg (sq_nonneg b)]
    gcongr
  · rw [abs_mul]; gcongr

/-- Galí (2015), (17), p. 139: discounted bounded sequences are summable, so the loss of a
bounded path is a genuine (convergent) infinite sum. -/
theorem summable_disc {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {g : ℕ → ℝ} {K : ℝ}
    (hg : ∀ t, |g t| ≤ K) : Summable (fun t => β ^ t * g t) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right K)
    (fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (hg t) (pow_nonneg hβ0 t)

/-- Galí (2015), (17), p. 139: the discounted loss of a bounded path is summable. -/
theorem detLoss_summable {β ϑ Λ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {infl x : ℕ → ℝ}
    (hb : BddSeq infl) (hbx : BddSeq x) :
    Summable (fun t => β ^ t * periodLoss ϑ Λ (infl t) (x t)) := by
  obtain ⟨A, hA⟩ := hb
  obtain ⟨B, hB⟩ := hbx
  exact summable_disc hβ0 hβ1 (fun t => abs_periodLoss_le (hA t) (hB t))

/-- Galí (2015), pp. 141–142: **Lagrangian identity**. If a bounded feasible path
`(π⁰, x̂⁰)` satisfies the first-order conditions with a bounded multiplier, then for every
bounded feasible path `(π, x̂)`
`L(π, x̂) = L(π⁰, x̂⁰) + ∑ βᵗ ½((π_t − π⁰_t)² + ϑ(x̂_t − x̂⁰_t)²)`.
The linear terms telescope to zero, using `ξ_{−1} = 0` and `βᵗ ξ_{t−1} → 0`. -/
theorem lagrangian_identity {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u infl₀ x₀ ξ infl x : ℕ → ℝ} (hF₀ : DetFeasible β κ u infl₀ x₀)
    (hFOC : DetFOC κ ϑ Λ infl₀ x₀ ξ) (hb₀ : BddSeq infl₀) (hbx₀ : BddSeq x₀)
    (hbξ : BddSeq ξ) (hF : DetFeasible β κ u infl x) (hb : BddSeq infl) (hbx : BddSeq x) :
    detLoss β ϑ Λ infl x = detLoss β ϑ Λ infl₀ x₀ +
      ∑' t, β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t) := by
  obtain ⟨A₀, hA₀⟩ := hb₀
  obtain ⟨B₀, hB₀⟩ := hbx₀
  obtain ⟨A, hA⟩ := hb
  obtain ⟨B, hB⟩ := hbx
  obtain ⟨Ξ, hΞ⟩ := hbξ
  have hdA : ∀ t, |infl t - infl₀ t| ≤ A + A₀ := fun t =>
    (abs_sub _ _).trans (add_le_add (hA t) (hA₀ t))
  have hdB : ∀ t, |x t - x₀ t| ≤ B + B₀ := fun t =>
    (abs_sub _ _).trans (add_le_add (hB t) (hB₀ t))
  have hS : Summable (fun t => β ^ t * periodLoss ϑ Λ (infl t) (x t)) :=
    detLoss_summable hβ0.le hβ1 ⟨A, hA⟩ ⟨B, hB⟩
  have hS₀ : Summable (fun t => β ^ t * periodLoss ϑ Λ (infl₀ t) (x₀ t)) :=
    detLoss_summable hβ0.le hβ1 ⟨A₀, hA₀⟩ ⟨B₀, hB₀⟩
  have hSq : Summable (fun t => β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t)) :=
    summable_disc hβ0.le hβ1 (fun t => abs_periodLoss_le (hdA t) (hdB t))
  -- the linear part `βᵗ ℓ_t` telescopes: `βᵗ ℓ_t = a_t − a_{t+1}`
  set a : ℕ → ℝ := fun t => β ^ t * (lag ξ t * (infl t - infl₀ t)) with ha
  set ℓ : ℕ → ℝ := fun t => β ^ t * periodLoss ϑ Λ (infl t) (x t) -
    β ^ t * periodLoss ϑ Λ (infl₀ t) (x₀ t) -
    β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t) with hℓ
  have hℓa : ∀ t, ℓ t = a t - a (t + 1) := by
    intro t
    have h1 := hFOC.1 t
    have h2 := hFOC.2 t
    have h3 := hF t
    have h4 := hF₀ t
    simp only [hℓ, ha, lag_succ, periodLoss, pow_succ]
    linear_combination (β ^ t * (x t - x₀ t)) * h1 + (β ^ t * (infl t - infl₀ t)) * h2 -
      (β ^ t * ξ t) * h3 + (β ^ t * ξ t) * h4
  have hℓS : Summable ℓ := (hS.sub hS₀).sub hSq
  have hℓ0 : ∑' t, ℓ t = 0 := by
    have hpart : ∀ N, ∑ t ∈ Finset.range N, ℓ t = -a N := by
      intro N
      rw [Finset.sum_congr rfl (fun t _ => hℓa t), Finset.sum_range_sub']
      simp [ha]
    have haN : Tendsto a atTop (𝓝 0) := by
      have hb' : ∀ N, ‖a N‖ ≤ β ^ N * (|Ξ| * (A + A₀)) := by
        intro N
        have hL : |lag ξ N| ≤ |Ξ| := by
          cases N with
          | zero => simp
          | succ N => exact (hΞ N).trans (le_abs_self Ξ)
        have hval : ‖a N‖ = β ^ N * (|lag ξ N| * |infl N - infl₀ N|) := by
          simp only [ha, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
        rw [hval]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hL (hdA N) (abs_nonneg _) (abs_nonneg _)) (pow_nonneg hβ0.le N)
      refine squeeze_zero_norm hb' ?_
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (|Ξ| * (A + A₀))
    have h1 := hℓS.hasSum.tendsto_sum_nat
    simp only [hpart] at h1
    have h2 : Tendsto (fun N => -a N) atTop (𝓝 0) := by simpa using haN.neg
    exact tendsto_nhds_unique h1 h2
  have hsplit : ∀ t, β ^ t * periodLoss ϑ Λ (infl t) (x t) =
      (β ^ t * periodLoss ϑ Λ (infl₀ t) (x₀ t) +
        β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t)) + ℓ t := by
    intro t; simp only [hℓ]; ring
  unfold detLoss
  rw [tsum_congr hsplit, (hS₀.add hSq).tsum_add hℓS, hℓ0, add_zero, hS₀.tsum_add hSq]

/-- Galí (2015), pp. 141–142: **Lagrangian sufficiency**. A bounded feasible path satisfying
the first-order conditions with a bounded multiplier minimises the loss among all bounded
feasible paths, strictly: any other bounded feasible path has a strictly larger loss. -/
theorem lagrangian_sufficiency {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    {u infl₀ x₀ ξ infl x : ℕ → ℝ} (hF₀ : DetFeasible β κ u infl₀ x₀)
    (hFOC : DetFOC κ ϑ Λ infl₀ x₀ ξ) (hb₀ : BddSeq infl₀) (hbx₀ : BddSeq x₀)
    (hbξ : BddSeq ξ) (hF : DetFeasible β κ u infl x) (hb : BddSeq infl) (hbx : BddSeq x) :
    detLoss β ϑ Λ infl₀ x₀ ≤ detLoss β ϑ Λ infl x ∧
      (detLoss β ϑ Λ infl x = detLoss β ϑ Λ infl₀ x₀ → infl = infl₀ ∧ x = x₀) := by
  have hid := lagrangian_identity hβ0 hβ1 hF₀ hFOC hb₀ hbx₀ hbξ hF hb hbx
  have hnn : ∀ t, 0 ≤ β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t) := by
    intro t
    simp only [periodLoss, zero_mul, sub_zero]
    have := pow_pos hβ0 t
    positivity
  refine ⟨?_, fun heq => ?_⟩
  · have h : 0 ≤ ∑' t, β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t) :=
      tsum_nonneg hnn
    rw [hid]
    linarith
  · obtain ⟨A₀, hA₀⟩ := hb₀
    obtain ⟨B₀, hB₀⟩ := hbx₀
    obtain ⟨A, hA⟩ := hb
    obtain ⟨B, hB⟩ := hbx
    have hSq : Summable (fun t => β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t)) :=
      summable_disc hβ0.le hβ1 (fun t => abs_periodLoss_le
        ((abs_sub _ _).trans (add_le_add (hA t) (hA₀ t)))
        ((abs_sub _ _).trans (add_le_add (hB t) (hB₀ t))))
    have h0 : ∑' t, β ^ t * periodLoss ϑ 0 (infl t - infl₀ t) (x t - x₀ t) = 0 := by
      linarith
    have hz := (hasSum_zero_iff_of_nonneg hnn).mp (h0 ▸ hSq.hasSum)
    have hpt : ∀ t, infl t - infl₀ t = 0 ∧ x t - x₀ t = 0 := by
      intro t
      have h1 := congrFun hz t
      have hp := pow_pos hβ0 t
      simp only [Pi.zero_apply, mul_eq_zero, hp.ne', false_or, periodLoss] at h1
      have h2 : (infl t - infl₀ t) ^ 2 + ϑ * (x t - x₀ t) ^ 2 = 0 := by linarith
      have h3 : 0 ≤ ϑ * (x t - x₀ t) ^ 2 := by positivity
      have h4 : (infl t - infl₀ t) ^ 2 = 0 := by nlinarith [sq_nonneg (infl t - infl₀ t)]
      have h5 : (x t - x₀ t) ^ 2 = 0 := by
        have : ϑ * (x t - x₀ t) ^ 2 = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hϑ.ne'
        · exact h
      exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4,
        pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5⟩
    exact ⟨funext fun t => sub_eq_zero.mp (hpt t).1, funext fun t => sub_eq_zero.mp (hpt t).2⟩

/-- Galí (2015), p. 142, fn. 8, under perfect foresight with an arbitrary bounded cost-push
sequence `u`: **existence** of a bounded feasible path satisfying the first-order conditions
with a bounded multiplier. The price level solves `p̂_t = δ p̂_{t−1} + δ z_t`, where
`z_t = ∑_{k ≥ 0} (δβ)ᵏ (κΛ/ϑ + u_{t+k})` is the forward solution of
`z_t = δβ z_{t+1} + κΛ/ϑ + u_t` (for AR(1) shocks this is (23)). -/
theorem det_commitment_exists {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) {u : ℕ → ℝ} (hu : BddSeq u) :
    ∃ infl₀ x₀ ξ : ℕ → ℝ, DetFeasible β κ u infl₀ x₀ ∧ DetFOC κ ϑ Λ infl₀ x₀ ξ ∧
      BddSeq infl₀ ∧ BddSeq x₀ ∧ BddSeq ξ := by
  obtain ⟨M, hM⟩ := hu
  set d := del β κ ϑ with hd
  have h0 : 0 < d := del_pos hβ0 hϑ
  have h1 : d < 1 := (del_lt_one_iff hβ0 hβ1 hϑ).mpr hκ.ne'
  have hdb0 : 0 ≤ d * β := by positivity
  have hdb1 : d * β < 1 := by nlinarith
  set W : ℕ → Unit → ℝ := fun t _ => κ * Λ / ϑ + u t with hW
  have hWb : ∀ t ω, |W t ω| ≤ |κ * Λ / ϑ| + M := fun t _ =>
    (abs_add_le _ _).trans (add_le_add le_rfl (hM t))
  have hWa : perfectForesight.Adapted W := fun _ => rfl
  set z : ℕ → ℝ := fun t => perfectForesight.forwardSeries (d * β) W t () with hz
  have hzeq : ∀ t, z t = d * β * z (t + 1) + (κ * Λ / ϑ + u t) := by
    intro t
    have := congrFun (perfectForesight.forwardSeries_solves hdb0 hdb1 hWb hWa t) ()
    exact this
  obtain ⟨Kz, hKz⟩ := perfectForesight.forwardSeries_bounded hdb0 hdb1 hWb
  set P : ℕ → ℝ := backRec d (fun t => d * z t) with hP
  have hPrec : ∀ t, P t = d * lag P t + d * z t := by
    intro t
    cases t with
    | zero => simp [hP, backRec]
    | succ t => rfl
  set K := d * |Kz| / (1 - d)
  have hne : 1 - d ≠ 0 := (by linarith : (0 : ℝ) < 1 - d).ne'
  have hK0 : 0 ≤ K := by
    have : 0 < 1 - d := by linarith
    positivity
  have hPb : ∀ t, |P t| ≤ K := by
    intro t
    induction t with
    | zero =>
      rw [hPrec 0, lag_zero, mul_zero, zero_add, abs_mul, abs_of_pos h0]
      have : |z 0| ≤ |Kz| := (hKz 0 ()).trans (le_abs_self Kz)
      have hKK : d * |Kz| ≤ K := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith [mul_nonneg (mul_nonneg h0.le (abs_nonneg Kz)) h0.le]
      nlinarith
    | succ t ih =>
      rw [hPrec (t + 1), lag_succ]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos h0]
      have : |z (t + 1)| ≤ |Kz| := (hKz (t + 1) ()).trans (le_abs_self Kz)
      have hKK : d * K + d * |Kz| = K := by
        simp only [K]; field_simp; ring
      nlinarith
  have hlagb : ∀ t, |lag P t| ≤ K := by
    intro t
    cases t with
    | zero => simpa using hK0
    | succ t => exact hPb t
  have hk : κ ^ 2 * del β κ ϑ = ϑ * ((1 - del β κ ϑ) * (1 - β * del β κ ϑ)) := by
    rw [← kappa_sq_del hβ0 hβ1 hϑ]; field_simp
  have hkl : ϑ * (κ * Λ / ϑ) = κ * Λ := by field_simp
  refine ⟨fun t => P t - lag P t, fun t => Λ / ϑ - κ / ϑ * P t, fun t => -P t, ?_, ⟨?_, ?_⟩,
    ⟨K + K, fun t => (abs_sub _ _).trans (add_le_add (hPb t) (hlagb t))⟩,
    ⟨|Λ / ϑ| + |κ / ϑ| * K, fun t => ?_⟩, ⟨K, fun t => by rw [abs_neg]; exact hPb t⟩⟩
  · intro t
    have hp := hPrec t
    have hp' := hPrec (t + 1)
    rw [lag_succ] at hp'
    have hzt := hzeq t
    have hx : ϑ * (Λ / ϑ - κ / ϑ * P t) = Λ - κ * P t := by field_simp
    simp only [lag_succ]
    apply mul_left_cancel₀ hϑ.ne'
    linear_combination (ϑ - ϑ * β * d + ϑ * β + κ ^ 2) * hp - ϑ * β * hp' - κ * hx +
      ϑ * hzt + hkl + (lag P t + z t) * hk
  · intro t
    field_simp
    ring
  · intro t
    cases t with
    | zero => simp
    | succ t => simp only [lag_succ]; ring
  · refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    gcongr
    exact hPb t

/-- Galí (2015), pp. 141–142, deterministic problem: **the Lagrangian conditions are
necessary and sufficient**. For a bounded cost-push sequence, a bounded feasible path
minimises the loss (17) among all bounded feasible paths if and only if it satisfies the
first-order conditions with some bounded multiplier `ξ` (`ξ_{−1} = 0`). -/
theorem det_optimal_iff {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    {u infl x : ℕ → ℝ} (hu : BddSeq u) (hF : DetFeasible β κ u infl x) (hb : BddSeq infl)
    (hbx : BddSeq x) :
    (∀ infl' x', DetFeasible β κ u infl' x' → BddSeq infl' → BddSeq x' →
      detLoss β ϑ Λ infl x ≤ detLoss β ϑ Λ infl' x') ↔
      ∃ ξ, BddSeq ξ ∧ DetFOC κ ϑ Λ infl x ξ := by
  constructor
  · intro hopt
    obtain ⟨infl₀, x₀, ξ, hF₀, hFOC, hb₀, hbx₀, hbξ⟩ :=
      det_commitment_exists (Λ := Λ) hβ0 hβ1 hκ hϑ hu
    have hs := lagrangian_sufficiency hβ0 hβ1 hϑ hF₀ hFOC hb₀ hbx₀ hbξ hF hb hbx
    have heq : detLoss β ϑ Λ infl x = detLoss β ϑ Λ infl₀ x₀ :=
      le_antisymm (hopt infl₀ x₀ hF₀ hb₀ hbx₀) hs.1
    obtain ⟨h1, h2⟩ := hs.2 heq
    subst h1 h2
    exact ⟨ξ, hbξ, hFOC⟩
  · rintro ⟨ξ, hbξ, hFOC⟩ infl' x' hF' hb' hbx'
    exact (lagrangian_sufficiency hβ0 hβ1 hϑ hF hFOC hb hbx hbξ hF' hb' hbx').1

/-- Galí (2015), pp. 141–143, deterministic problem: **existence and uniqueness of the
optimal commitment plan**. For every bounded cost-push sequence there is a bounded feasible
path whose loss is no larger than that of any bounded feasible path, and it is the only
bounded feasible path attaining that loss. -/
theorem det_commitment_optimal {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) {u : ℕ → ℝ} (hu : BddSeq u) :
    ∃ infl₀ x₀ : ℕ → ℝ, DetFeasible β κ u infl₀ x₀ ∧ BddSeq infl₀ ∧ BddSeq x₀ ∧
      ∀ infl x, DetFeasible β κ u infl x → BddSeq infl → BddSeq x →
        detLoss β ϑ Λ infl₀ x₀ ≤ detLoss β ϑ Λ infl x ∧
          (detLoss β ϑ Λ infl x = detLoss β ϑ Λ infl₀ x₀ → infl = infl₀ ∧ x = x₀) := by
  obtain ⟨infl₀, x₀, ξ, hF₀, hFOC, hb₀, hbx₀, hbξ⟩ :=
    det_commitment_exists (Λ := Λ) hβ0 hβ1 hκ hϑ hu
  exact ⟨infl₀, x₀, hF₀, hb₀, hbx₀, fun infl x hF hb hbx =>
    lagrangian_sufficiency hβ0 hβ1 hϑ hF₀ hFOC hb₀ hbx₀ hbξ hF hb hbx⟩

/-- Galí (2015), p. 143: **the linear term makes the optimum non-zero**. Without cost-push
shocks the zero path is feasible, but when `Λ ≠ 0` some bounded feasible path has strictly
smaller loss (with `Λ = 0` the zero path would be optimal: it gives zero loss). -/
theorem zero_path_not_optimal {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hΛ : Λ ≠ 0) :
    DetFeasible β κ 0 0 0 ∧ ∃ infl x, DetFeasible β κ 0 infl x ∧ BddSeq infl ∧ BddSeq x ∧
      detLoss β ϑ Λ infl x < detLoss β ϑ Λ 0 0 := by
  have hF0 : DetFeasible β κ 0 0 0 := fun t => by simp
  have hb0 : BddSeq (0 : ℕ → ℝ) := ⟨0, fun t => by simp⟩
  refine ⟨hF0, ?_⟩
  obtain ⟨infl₀, x₀, ξ, hF₀, hFOC, hb₀, hbx₀, hbξ⟩ :=
    det_commitment_exists (Λ := Λ) hβ0 hβ1 hκ hϑ hb0
  refine ⟨infl₀, x₀, hF₀, hb₀, hbx₀, ?_⟩
  have hs := lagrangian_sufficiency hβ0 hβ1 hϑ hF₀ hFOC hb₀ hbx₀ hbξ hF0 hb0 hb0
  refine lt_of_le_of_ne hs.1 fun heq => ?_
  obtain ⟨h1, h2⟩ := hs.2 heq.symm
  have hx := hFOC.1 0
  have hi := hFOC.2 0
  rw [← h1] at hi
  rw [← h2] at hx
  simp only [Pi.zero_apply, lag_zero, zero_add, sub_zero, mul_zero, zero_sub] at hx hi
  rw [hi, mul_zero, neg_zero, zero_sub, neg_eq_zero] at hx
  exact hΛ hx

/-- Galí (2015), p. 143, deterministic problem without cost-push shocks: the commitment path
`π_t = δᵗ (δ/(1 − δβ)) κΛ/ϑ`, `x̂_t = δ^{t+1} Λ/ϑ` is feasible and minimises the loss (17)
among all bounded feasible paths. -/
theorem det_zeroShock_optimal {β κ ϑ Λ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) :
    DetFeasible β κ 0 (fun t => del β κ ϑ ^ t * commConst β κ ϑ Λ)
        (fun t => del β κ ϑ ^ (t + 1) * Λ / ϑ) ∧
      ∀ infl x, DetFeasible β κ 0 infl x → BddSeq infl → BddSeq x →
        detLoss β ϑ Λ (fun t => del β κ ϑ ^ t * commConst β κ ϑ Λ)
          (fun t => del β κ ϑ ^ (t + 1) * Λ / ϑ) ≤ detLoss β ϑ Λ infl x := by
  have hu : perfectForesight.IsAR1 0 (0 : ℕ → Unit → ℝ) :=
    ⟨fun _ => rfl, fun _ => by simp⟩
  have hub : BoundedProc (0 : ℕ → Unit → ℝ) := ⟨0, fun _ _ => by simp⟩
  obtain ⟨hE, -, ⟨Kp, hKp⟩, ⟨Kx, hKx⟩, ⟨Ki, hKi⟩⟩ :=
    commitment_exists perfectForesight (Λ := Λ) hβ0 hβ1 hκ hϑ (by simp) hu hub
  have hI : ∀ t, commInfl β κ ϑ Λ 0 (0 : ℕ → Unit → ℝ) t () = del β κ ϑ ^ t * commConst β κ ϑ Λ :=
    fun t => congrFun (commInfl_zeroShock hβ0 hβ1 hκ hϑ t) ()
  have hG : ∀ t, commGap β κ ϑ Λ 0 (0 : ℕ → Unit → ℝ) t () = del β κ ϑ ^ (t + 1) * Λ / ϑ :=
    fun t => congrFun (commGap_zeroShock hβ0 hβ1 hκ hϑ (by simp) t) ()
  have hF₀ : DetFeasible β κ 0 (fun t => del β κ ϑ ^ t * commConst β κ ϑ Λ)
      (fun t => del β κ ϑ ^ (t + 1) * Λ / ϑ) := by
    intro t
    have := congrFun (hE.1 t) ()
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    beta_reduce
    rw [← hI t, ← hI (t + 1), ← hG t]
    exact this
  have hFOC : DetFOC κ ϑ Λ (fun t => del β κ ϑ ^ t * commConst β κ ϑ Λ)
      (fun t => del β κ ϑ ^ (t + 1) * Λ / ϑ)
      (fun t => commMult β κ ϑ Λ 0 (0 : ℕ → Unit → ℝ) t ()) := by
    refine ⟨fun t => ?_, fun t => ?_⟩
    · have := congrFun (hE.2.1 t) ()
      beta_reduce
      rw [← hG t]
      exact this
    · have := congrFun (hE.2.2 t) ()
      beta_reduce
      rw [← hI t]
      cases t with
      | zero => exact this
      | succ t => exact this
  have hbξ : BddSeq (fun t => commMult β κ ϑ Λ 0 (0 : ℕ → Unit → ℝ) t ()) :=
    ⟨Kp, fun t => by simp only [commMult, Pi.neg_apply, abs_neg]; exact hKp t ()⟩
  have hb₀ : BddSeq (fun t => del β κ ϑ ^ t * commConst β κ ϑ Λ) :=
    ⟨Ki, fun t => by beta_reduce; rw [← hI t]; exact hKi t ()⟩
  have hbx₀ : BddSeq (fun t => del β κ ϑ ^ (t + 1) * Λ / ϑ) :=
    ⟨Kx, fun t => by beta_reduce; rw [← hG t]; exact hKx t ()⟩
  exact ⟨hF₀, fun infl x hF hb hbx =>
    (lagrangian_sufficiency hβ0 hβ1 hϑ hF₀ hFOC hb₀ hbx₀ hbξ hF hb hbx).1⟩

end Gali.DiscretionCommitment.DistortedSS
