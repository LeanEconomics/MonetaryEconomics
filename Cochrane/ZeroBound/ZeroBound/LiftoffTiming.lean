/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.LinksGaliWoodford
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Lift-off timing: at the commitment optimum the zero bound binds throughout the shock

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.4 "Forward guidance"
(pp. 478–480), compared with Galí (2015), §5.4.2 (pp. 148–152), in the model of
`LinksGaliWoodford` (loss `∑ βᵗ(π_t² + ϑ x_t²)`, `π_t = βπ_{t+1} + κx_t`,
`x_t = x_{t+1} − σ⁻¹(i_t − π_{t+1} − rⁿ_t)`, `i_t ≥ 0`, `rⁿ_t = −η` on `[0, t_Z]`, `ρ` after).

Galí's algorithm guesses a lift-off date `t_C ≥ t_Z`; `LinksGaliWoodford` carried `t_Z ≤ t_C`
(and the zero rate on the whole shock, (48)) as hypotheses. Here both are **proved** for the
commitment optimum, for all `β ∈ (0,1)`, `κ, σ, ϑ > 0`, `η > 0`, `ρ ≥ 0`.

## Necessity of the KKT conditions (`kkt_necessary`)
* `mult`, `mxi1`, `mxi2`: the multipliers solving (35)–(36) forward (`foc35_mult`,
  `foc36_mult`, unique: `mult_unique`).
* `foc_dir`: an optimum has a nonnegative derivative in every feasible direction.
* `hdir s`: raise the rate at `s` alone (finite support); `cross_hdir`: its derivative is
  `β^s ξ₂,s / σ` (Lagrangian identity), so `ξ₂ ≥ 0` with complementary slackness.
* `wdir`: the bounded peg mode (zero rate gaps), with zero derivative (`cross_wdir`);
  `ddir = hdir − c₁λ₁ˢ wdir` is localised (`backState_closed`, `ddir_le`, `ddir_gt`,
  `ddir_bound`); by Tannery's theorem `β^t ξ₂,t → 0` (`tendsto_mxi2`, transversality).

## The sign argument (`trap_mult_pos`)
Write `gap_t = i_t − rⁿ_t` and `lam_t = π_{t+1} + (ϑ/κ)(x_{t+1} − x_t)`; then
`gap = r·lam − (r−1)π_{+1}` with `r = σκ/ϑ` (`gap_lam`) and `κ·lam_t = cξ₂,t − ξ₂,t+1 −
ξ₂,t−1/β` (`lam_mult`). Under the Phillips curve both are second-difference operators of `π`
(`gap_comb`, `lam_comb`), which gives discrete maximum principles.
* `pi_le_bound`/`optimal_pi_le`: commitment inflation never exceeds `η`.
* `σκ ≤ ϑ` (`slack_contra_le`): a slack shock date `s` would give
  `gap_s ≤ (1 − r)π_{s+1} ≤ (1 − r)η < η`, i.e. `i_s < 0`.
* `ϑ < σκ` (`slack_contra_gt`): a slack date forces `π_{s+1} ≤ −η/(r−1)`; a minimum principle on
  the shock carries this to its end with inflation falling there; inflation then stays negative
  (`post_nonpos`), the multipliers vanish from `s` on (`mult_zero_left`, `mult_zero_right`),
  and the remaining peg dynamics explode (`comb_blowup`), contradicting the finite loss.

## Results
* `optimal_trap_binds`, `optimal_h48`: at the optimum `i_t = 0` and `ξ₂,t > 0` on `[0, t_Z]`.
* `liftoff_ge`, `liftoff_ge_mult`, `liftoff_after_shock`: the lift-off date satisfies
  `t_C ≥ t_Z`.
* Hypothesis-free versions (no `t_Z ≤ t_C`, no (48)): `comm_gt_disc_opt`, `comm_loss_lt_opt`,
  `comm_promise_opt`, `comm_gt_disc_of_state_opt`, and the verification theorem for an arbitrary
  guess `algorithm_verification_gen` (it proves `t_Z ≤ t_C`), `comm_loss_lt_alg_gen`.
-/

namespace Cochrane.ZeroBound.LiftoffTiming

open Filter Topology
open Cochrane.ZeroBound Cochrane.ZeroBound.LinksGaliWoodford

/-! ## Second differences and geometric blow-up -/

/-- Cochrane (2023), §20.2.4, p. 479 (Galí (2015), (29)–(30), p. 145, with `x` eliminated by
the Phillips curve): `u_{t+1} + a((u_{t+1} − u_t) + β(u_{t+1} − u_{t+2}))`. With `a = σ/κ` it is
the rate gap `i_t − rⁿ_t` (`gap_comb`), with `a = ϑ/κ²` the multiplier combination
`lam` (`lam_comb`). -/
noncomputable def comb (β a : ℝ) (u : ℕ → ℝ) (t : ℕ) : ℝ :=
  u (t + 1) + a * ((u (t + 1) - u t) + β * (u (t + 1) - u (t + 2)))

/-- Cochrane (2023), p. 479: at a weak local minimum `comb` is at most the value there. -/
theorem comb_le_of_min {β a : ℝ} (hβ : 0 ≤ β) (ha : 0 ≤ a) {u : ℕ → ℝ} {t : ℕ}
    (h1 : u (t + 1) ≤ u t) (h2 : u (t + 1) ≤ u (t + 2)) : comb β a u t ≤ u (t + 1) := by
  unfold comb
  have h3 : β * (u (t + 1) - u (t + 2)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ (by linarith)
  have h4 : a * ((u (t + 1) - u t) + β * (u (t + 1) - u (t + 2))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha (by linarith)
  linarith

/-- Cochrane (2023), p. 479: if `comb ≤ B < u_{t+1}` and `u_t ≤ u_{t+1}`, the sequence keeps
rising: `u_{t+1} < u_{t+2}`. -/
theorem comb_up {β a B : ℝ} (hβ : 0 < β) (ha : 0 < a) {u : ℕ → ℝ} {t : ℕ}
    (h : comb β a u t ≤ B) (hB : B < u (t + 1)) (hu : u t ≤ u (t + 1)) :
    u (t + 1) < u (t + 2) := by
  unfold comb at h
  have h1 : a * ((u (t + 1) - u t) + β * (u (t + 1) - u (t + 2))) < 0 := by linarith
  have h2 : (u (t + 1) - u t) + β * (u (t + 1) - u (t + 2)) < 0 := by
    by_contra hc
    push Not at hc
    linarith [mul_nonneg ha.le hc]
  have h4 : u (t + 1) - u (t + 2) < 0 := by
    by_contra hc
    push Not at hc
    linarith [mul_nonneg hβ.le hc]
  linarith

/-- Cochrane (2023), p. 479: if `comb ≤ B ≤ u_{t+1}`, the increment grows by at least the
factor `β⁻¹`: `(u_{t+1} − u_t)/β ≤ u_{t+2} − u_{t+1}`. -/
theorem comb_step {β a B : ℝ} (hβ : 0 < β) (ha : 0 < a) {u : ℕ → ℝ} {t : ℕ}
    (h : comb β a u t ≤ B) (hB : B ≤ u (t + 1)) :
    (u (t + 1) - u t) / β ≤ u (t + 2) - u (t + 1) := by
  unfold comb at h
  have h1 : a * ((u (t + 1) - u t) + β * (u (t + 1) - u (t + 2))) ≤ 0 := by linarith
  have h2 : (u (t + 1) - u t) + β * (u (t + 1) - u (t + 2)) ≤ 0 := by
    by_contra hc
    push Not at hc
    linarith [mul_pos ha hc]
  rw [div_le_iff₀ hβ]
  linarith

/-- Cochrane (2023), p. 479: `comb` is odd in the sequence. -/
theorem comb_neg (β a : ℝ) (u : ℕ → ℝ) (t : ℕ) :
    comb β a (fun n => -u n) t = -comb β a u t := by
  unfold comb; ring

/-- Cochrane (2023), §20.2.4, p. 479 (the explosive direction of the zero-rate dynamics,
`ForwardGuidance`): if, from `n₀` on, every rise above `B` makes the next increment at least
`β⁻¹` times the previous one, then a rise at `n₀` grows geometrically:
`u_{n₀+1} − u_{n₀} ≤ β^k (u_{n₀+k+1} − u_{n₀+k})` and `B < u_{n₀+k+1}`. -/
theorem grow {β : ℝ} (hβ0 : 0 < β) {u : ℕ → ℝ} {n0 : ℕ} {B : ℝ}
    (hstep : ∀ n, n0 ≤ n → B < u (n + 1) → u n < u (n + 1) →
      (u (n + 1) - u n) / β ≤ u (n + 2) - u (n + 1))
    (h0 : B < u (n0 + 1)) (h1 : u n0 < u (n0 + 1)) (k : ℕ) :
    u (n0 + 1) - u n0 ≤ β ^ k * (u (n0 + k + 1) - u (n0 + k)) ∧ B < u (n0 + k + 1) := by
  induction k with
  | zero => simp only [pow_zero, one_mul, add_zero, le_refl, h0, and_self]
  | succ k ih =>
    obtain ⟨ha, hb⟩ := ih
    have hpk : 0 < β ^ k := pow_pos hβ0 k
    have hd : 0 < u (n0 + k + 1) - u (n0 + k) := by
      by_contra hc
      push Not at hc
      have : β ^ k * (u (n0 + k + 1) - u (n0 + k)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpk.le hc
      linarith
    have hs := hstep (n0 + k) (by omega) hb (by linarith)
    rw [show n0 + k + 2 = n0 + (k + 1) + 1 by omega,
      show n0 + k + 1 = n0 + (k + 1) by omega] at hs
    rw [show n0 + (k + 1) = n0 + k + 1 by omega] at hs ⊢
    rw [div_le_iff₀ hβ0] at hs
    have hdpos : 0 < (u (n0 + k + 1) - u (n0 + k)) / β := div_pos hd hβ0
    constructor
    · have e : β ^ (k + 1) * (u (n0 + k + 1 + 1) - u (n0 + k + 1)) =
          β ^ k * ((u (n0 + k + 1 + 1) - u (n0 + k + 1)) * β) := by ring
      rw [e]
      have : β ^ k * (u (n0 + k + 1) - u (n0 + k)) ≤
          β ^ k * ((u (n0 + k + 1 + 1) - u (n0 + k + 1)) * β) :=
        mul_le_mul_of_nonneg_left hs hpk.le
      linarith
    · have : u (n0 + k + 1) - u (n0 + k) ≤ (u (n0 + k + 1 + 1) - u (n0 + k + 1)) * β := hs
      have hβd : 0 < (u (n0 + k + 1 + 1) - u (n0 + k + 1)) * β := by linarith
      have : 0 < u (n0 + k + 1 + 1) - u (n0 + k + 1) :=
        (pos_iff_pos_of_mul_pos hβd).mpr hβ0
      linarith

/-- Cochrane (2023), p. 479: such geometric growth is incompatible with a finite discounted loss,
`β^t u_t² ↛ 0` (with `0 ≤ B`, `0 < β ≤ 1`). -/
theorem not_tendsto_sq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) {u : ℕ → ℝ} {n0 : ℕ} {B : ℝ}
    (hB : 0 ≤ B)
    (hstep : ∀ n, n0 ≤ n → B < u (n + 1) → u n < u (n + 1) →
      (u (n + 1) - u n) / β ≤ u (n + 2) - u (n + 1))
    (h0 : B < u (n0 + 1)) (h1 : u n0 < u (n0 + 1)) :
    ¬ Tendsto (fun t => β ^ t * u t ^ 2) atTop (𝓝 0) := by
  intro hT
  set d := u (n0 + 1) - u n0 with hd
  have hdpos : 0 < d := by linarith
  have hc : 0 < β ^ (n0 + 1) * d ^ 2 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 hT).2 _ hc)
  have key : β ^ (n0 + 1) * d ^ 2 ≤ β ^ (n0 + (N + 1) + 1) * u (n0 + (N + 1) + 1) ^ 2 := by
    obtain ⟨g1, g2⟩ := grow hβ0 hstep h0 h1 (N + 1)
    obtain ⟨-, g3⟩ := grow hβ0 hstep h0 h1 N
    rw [show n0 + (N + 1) = n0 + N + 1 by omega] at g1 g2 ⊢
    set v := u (n0 + N + 1 + 1)
    have hv0 : 0 ≤ u (n0 + N + 1) := by linarith
    have hpk : 0 < β ^ (N + 1) := pow_pos hβ0 _
    have hvd : d ≤ β ^ (N + 1) * v := by
      have : β ^ (N + 1) * (v - u (n0 + N + 1)) ≤ β ^ (N + 1) * v :=
        mul_le_mul_of_nonneg_left (by linarith) hpk.le
      linarith
    have hsq : d ^ 2 ≤ (β ^ (N + 1) * v) ^ 2 := pow_le_pow_left₀ hdpos.le hvd 2
    have hle : β ^ (N + 1) ≤ 1 := pow_le_one₀ hβ0.le hβ1
    have e : β ^ (n0 + N + 1 + 1) = β ^ (n0 + 1) * β ^ (N + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    have hp1 : 0 ≤ β ^ (n0 + 1) := pow_nonneg hβ0.le _
    have : (β ^ (N + 1) * v) ^ 2 ≤ β ^ (N + 1) * v ^ 2 := by
      rw [mul_pow, sq (β ^ (N + 1))]
      have := mul_le_mul_of_nonneg_right hle (mul_nonneg hpk.le (sq_nonneg v))
      nlinarith
    calc β ^ (n0 + 1) * d ^ 2 ≤ β ^ (n0 + 1) * (β ^ (N + 1) * v ^ 2) :=
          mul_le_mul_of_nonneg_left (hsq.trans this) hp1
      _ = β ^ (n0 + 1) * β ^ (N + 1) * v ^ 2 := by ring
  have := hN (n0 + (N + 1) + 1) (by omega)
  linarith

/-- Cochrane (2023), p. 479: the same growth with `u ≥ 0` is incompatible with `β^t u_t → 0`
(used for the multipliers). -/
theorem not_tendsto_lin {β : ℝ} (hβ0 : 0 < β) {u : ℕ → ℝ} {n0 : ℕ} (hnn : ∀ n, 0 ≤ u n)
    (hstep : ∀ n, n0 ≤ n → 0 < u (n + 1) → u n < u (n + 1) →
      (u (n + 1) - u n) / β ≤ u (n + 2) - u (n + 1))
    (h0 : 0 < u (n0 + 1)) (h1 : u n0 < u (n0 + 1)) :
    ¬ Tendsto (fun t => β ^ t * u t) atTop (𝓝 0) := by
  intro hT
  set d := u (n0 + 1) - u n0 with hd
  have hdpos : 0 < d := by linarith
  have hc : 0 < β ^ (n0 + 1) * d := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 hT).2 _ hc)
  have key : β ^ (n0 + 1) * d ≤ β ^ (n0 + N + 1) * u (n0 + N + 1) := by
    obtain ⟨g1, -⟩ := grow hβ0 hstep h0 h1 N
    have e : β ^ (n0 + N + 1) = β ^ (n0 + 1) * β ^ N := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    have hpN : 0 ≤ β ^ N := pow_nonneg hβ0.le _
    have : β ^ N * (u (n0 + N + 1) - u (n0 + N)) ≤ β ^ N * u (n0 + N + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hnn (n0 + N)]) hpN
    have hp1 : 0 ≤ β ^ (n0 + 1) := pow_nonneg hβ0.le _
    calc β ^ (n0 + 1) * d ≤ β ^ (n0 + 1) * (β ^ N * u (n0 + N + 1)) :=
          mul_le_mul_of_nonneg_left (g1.trans this) hp1
      _ = β ^ (n0 + 1) * β ^ N * u (n0 + N + 1) := by ring
  have := hN (n0 + N + 1) (by omega)
  linarith

/-- Cochrane (2023), §20.2.4, p. 479: if from `N₀` on one of two `comb` combinations (positive
weights) is at most `B ≥ 0`, a rise above `B` at some `m₀ ≥ N₀` makes `β^t u_t² ↛ 0`. -/
theorem comb_blowup {β a1 a2 B : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hB : 0 ≤ B) {u : ℕ → ℝ} {N0 m0 : ℕ}
    (hd : ∀ n, N0 ≤ n → comb β a1 u n ≤ B ∨ comb β a2 u n ≤ B) (hm : N0 ≤ m0)
    (h0 : B < u (m0 + 1)) (h1 : u m0 < u (m0 + 1)) :
    ¬ Tendsto (fun t => β ^ t * u t ^ 2) atTop (𝓝 0) := by
  refine not_tendsto_sq hβ0 hβ1 hB (fun n hn hb _ => ?_) h0 h1
  rcases hd n (by omega) with h | h
  · exact comb_step hβ0 ha1 h hb.le
  · exact comb_step hβ0 ha2 h hb.le

/-! ## The rate gap and the multiplier combination -/

/-- Cochrane (2023), §20.1, p. 465, and Galí (2015), eq. (30), p. 145: the rate gap
`i_t − rⁿ_t = π_{t+1} + σ(x_{t+1} − x_t)` (`impliedRate_eq_gap`). -/
noncomputable def gap (σ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : ℝ := π (t + 1) + σ * (x (t + 1) - x t)

/-- Galí (2015), eqs. (35)–(36), p. 149; Cochrane (2023), §20.2.4, p. 479: the combination
`π_{t+1} + (ϑ/κ)(x_{t+1} − x_t)`, which the first-order conditions express through the zero-bound
multipliers alone (`lam_mult`). -/
noncomputable def lam (κ ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  π (t + 1) + ϑ / κ * (x (t + 1) - x t)

/-- Galí (2015), eqs. (35)–(36) at `t = 0`, p. 149; Cochrane (2023), p. 479: `π₀ + (ϑ/κ) x₀`
(`= −ξ₂,₀/κ`, `lamI_mult`). -/
noncomputable def lamI (κ ϑ : ℝ) (x π : ℕ → ℝ) : ℝ := π 0 + ϑ / κ * x 0

/-- Galí (2015), eq. (30), p. 145; Cochrane (2023), p. 465: the implied rate is the natural rate
plus the rate gap. -/
theorem impliedRate_eq_gap (σ : ℝ) (rn x π : ℕ → ℝ) (t : ℕ) :
    impliedRate σ rn x π t = rn t + gap σ x π t := by
  unfold impliedRate gap; ring

/-- Galí (2015), eq. (29), p. 145; Cochrane (2023), eq. (5.2), p. 118: the Phillips curve solved
for the output gap, `x_t = (π_t − βπ_{t+1})/κ`. -/
theorem x_of_nkpc {β κ : ℝ} (hκ : κ ≠ 0) {x π : ℕ → ℝ} {t : ℕ} (h : NKPC β κ x π t) :
    x t = (π t - β * π (t + 1)) / κ := by
  unfold NKPC at h; field_simp; linarith

/-- Galí (2015), eqs. (29)–(30), p. 145; Cochrane (2023), p. 479: under the Phillips curve the
rate gap is `comb β (σ/κ) π t`. -/
theorem gap_comb {β κ σ : ℝ} (hκ : κ ≠ 0) {x π : ℕ → ℝ} {t : ℕ} (h0 : NKPC β κ x π t)
    (h1 : NKPC β κ x π (t + 1)) : gap σ x π t = comb β (σ / κ) π t := by
  have e0 := x_of_nkpc hκ h0
  have e1 := x_of_nkpc hκ h1
  rw [show t + 1 + 1 = t + 2 by omega] at e1
  unfold gap comb
  rw [e0, e1]
  field_simp
  ring

/-- Galí (2015), eqs. (29), (35)–(36), p. 149; Cochrane (2023), p. 479: under the Phillips curve
`lam` is `comb β (ϑ/κ²) π t`. -/
theorem lam_comb {β κ ϑ : ℝ} (hκ : κ ≠ 0) {x π : ℕ → ℝ} {t : ℕ} (h0 : NKPC β κ x π t)
    (h1 : NKPC β κ x π (t + 1)) : lam κ ϑ x π t = comb β (ϑ / κ ^ 2) π t := by
  have e0 := x_of_nkpc hκ h0
  have e1 := x_of_nkpc hκ h1
  rw [show t + 1 + 1 = t + 2 by omega] at e1
  unfold lam comb
  rw [e0, e1]
  field_simp
  ring

/-- Galí (2015), eq. (29), p. 145; Cochrane (2023), p. 479: `lamI = π₀ + (ϑ/κ²)(π₀ − βπ₁)`. -/
theorem lamI_eq {β κ ϑ : ℝ} (hκ : κ ≠ 0) {x π : ℕ → ℝ} (h0 : NKPC β κ x π 0) :
    lamI κ ϑ x π = π 0 + ϑ / κ ^ 2 * (π 0 - β * π 1) := by
  unfold lamI
  rw [x_of_nkpc hκ h0]
  field_simp

/-- Cochrane (2023), §20.2.4, p. 479: with `r = σκ/ϑ`, the rate gap is
`r · lam − (r − 1) π_{t+1}`. -/
theorem gap_lam {κ σ ϑ : ℝ} (hκ : κ ≠ 0) (hϑ : ϑ ≠ 0) (x π : ℕ → ℝ) (t : ℕ) :
    gap σ x π t = σ * κ / ϑ * lam κ ϑ x π t - (σ * κ / ϑ - 1) * π (t + 1) := by
  unfold gap lam
  field_simp
  ring

/-- Galí (2015), eqs. (35)–(36), p. 149; Cochrane (2023), §20.2.4, p. 479: the first-order
conditions give `κ · lam_t = c ξ₂,t − ξ₂,t+1 − ξ₂,t−1/β` with `c = 1 + 1/β + κ/(βσ)`: the
multiplier combination is a three-term (`Z`-matrix) operator of the multipliers. -/
theorem lam_mult {β κ σ ϑ : ℝ} (hκ : κ ≠ 0) {x π ξ1 ξ2 : ℕ → ℝ} {t : ℕ}
    (h35 : FOC35 β σ π ξ1 ξ2 (t + 1)) (h36a : FOC36 β κ ϑ x ξ1 ξ2 t)
    (h36b : FOC36 β κ ϑ x ξ1 ξ2 (t + 1)) :
    κ * lam κ ϑ x π t = (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β := by
  have e : κ * lam κ ϑ x π t = κ * π (t + 1) + ϑ * (x (t + 1) - x t) := by
    unfold lam; field_simp
  rw [e]
  unfold FOC35 at h35
  unfold FOC36 at h36a h36b
  simp only [lag_succ] at h35 h36b
  linear_combination κ * h35 + h36b - h36a

/-- Galí (2015), eqs. (35)–(36) at `t = 0`, p. 149; Cochrane (2023), p. 479:
`κ (π₀ + (ϑ/κ) x₀) = −ξ₂,₀`. -/
theorem lamI_mult {β κ σ ϑ : ℝ} (hκ : κ ≠ 0) {x π ξ1 ξ2 : ℕ → ℝ}
    (h35 : FOC35 β σ π ξ1 ξ2 0) (h36 : FOC36 β κ ϑ x ξ1 ξ2 0) :
    κ * lamI κ ϑ x π = -ξ2 0 := by
  have e : κ * lamI κ ϑ x π = κ * π 0 + ϑ * x 0 := by
    unfold lamI; field_simp
  rw [e]
  unfold FOC35 at h35
  unfold FOC36 at h36
  simp only [lag_zero, zero_div, sub_zero] at h35 h36
  linear_combination κ * h35 + h36

/-- Galí (2015), p. 149; Cochrane (2023), §20.1, p. 465: on a feasible path the implied rate is
nonnegative at every date. -/
theorem rate_nonneg {β κ σ : ℝ} (hσ : 0 < σ) {rn x π : ℕ → ℝ} (hF : Feasible β κ σ rn x π)
    (t : ℕ) : 0 ≤ impliedRate σ rn x π t := by
  rw [impliedRate_eq hσ.ne']
  exact mul_nonneg hσ.le (by linarith [(hF t).2])

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: a finite loss forces `β^t π_t² → 0`. -/
theorem tendsto_pi_sq {β ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {x π : ℕ → ℝ}
    (hs : Summable (lossTerm β ϑ x π)) : Tendsto (fun t => β ^ t * π t ^ 2) atTop (𝓝 0) := by
  refine (Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_) hs).tendsto_atTop_zero
  unfold lossTerm
  have : 0 ≤ β ^ t * (ϑ * x t ^ 2) := by positivity
  nlinarith

/-! ## Maximum principles for the Karush–Kuhn–Tucker system -/

/-- Cochrane (2023), §20.2.4, p. 479 (Galí (2015), (35)–(36)): a nonnegative multiplier sequence
vanishing at `s` whose three-term operator is `≤ 0` on `[0, s)` (with `ξ₂,₋₁ = 0`) vanishes on
`[0, s]` (finite maximum principle). -/
theorem mult_zero_left {β cc : ℝ} (hβ : 0 < β) (hcc : 1 + 1 / β < cc) {ξ2 : ℕ → ℝ}
    (hpos : ∀ t, 0 ≤ ξ2 t) {s : ℕ} (hs : ξ2 s = 0)
    (h : ∀ t, t < s → cc * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β ≤ 0) :
    ∀ t, t ≤ s → ξ2 t = 0 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · intro t ht
    obtain rfl : t = 0 := by omega
    exact hs
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range s) ξ2 ⟨0, by simp; omega⟩
  rw [Finset.mem_range] at hm
  have hM0 : 0 ≤ ξ2 m := hpos m
  have hnext : ξ2 (m + 1) ≤ ξ2 m := by
    rcases Nat.lt_or_ge (m + 1) s with h' | h'
    · exact hmax _ (Finset.mem_range.mpr h')
    · obtain rfl : s = m + 1 := by omega
      rw [hs]; exact hM0
  have hprev : lag ξ2 m ≤ ξ2 m := by
    rcases m with _ | j
    · simpa using hM0
    · simpa using hmax j (Finset.mem_range.mpr (by omega))
  have hM : ξ2 m ≤ 0 := by
    have h1 := h m hm
    have h2 : lag ξ2 m / β ≤ ξ2 m / β := div_le_div_of_nonneg_right hprev hβ.le
    have h3 : (cc - 1 - 1 / β) * ξ2 m ≤ 0 := by
      have : ξ2 m / β = 1 / β * ξ2 m := by ring
      nlinarith
    by_contra hc
    push Not at hc
    have : 0 < (cc - 1 - 1 / β) * ξ2 m := mul_pos (by linarith) hc
    linarith
  intro t ht
  rcases ht.eq_or_lt with rfl | ht'
  · exact hs
  · exact le_antisymm ((hmax t (Finset.mem_range.mpr ht')).trans hM) (hpos t)

/-- Cochrane (2023), §20.2.4, p. 479 (transversality, Galí (2015), p. 149): a nonnegative
multiplier sequence vanishing at `s`, with three-term operator `≤ 0` after `s` and
`β^t ξ₂,t → 0`, vanishes on `[s, ∞)` (otherwise it grows at least like `β⁻ᵗ`). -/
theorem mult_zero_right {β cc : ℝ} (hβ : 0 < β) (hcc : 1 + 1 / β < cc) {ξ2 : ℕ → ℝ}
    (hpos : ∀ t, 0 ≤ ξ2 t) {s : ℕ} (hs : ξ2 s = 0)
    (h : ∀ t, s < t → cc * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β ≤ 0)
    (hlim : Tendsto (fun t => β ^ t * ξ2 t) atTop (𝓝 0)) :
    ∀ t, s ≤ t → ξ2 t = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hex : ∃ t, s ≤ t ∧ ξ2 t ≠ 0 := hcon
  set t1 := Nat.find hex with ht1
  obtain ⟨ht1s, ht1z⟩ := Nat.find_spec hex
  have ht1ne : t1 ≠ s := by
    intro h'
    rw [← ht1, h'] at ht1z
    exact ht1z hs
  obtain ⟨n0, hn0⟩ : ∃ n0, t1 = n0 + 1 := ⟨t1 - 1, by omega⟩
  have hn0s : s ≤ n0 := by omega
  have hz0 : ξ2 n0 = 0 := by
    by_contra hz
    have := Nat.find_min hex (show n0 < Nat.find hex by omega)
    exact this ⟨hn0s, hz⟩
  have hpos1 : 0 < ξ2 (n0 + 1) := by
    rw [← hn0]
    exact lt_of_le_of_ne (hpos _) (Ne.symm ht1z)
  refine not_tendsto_lin hβ hpos (n0 := n0) (fun n hn _ _ => ?_) hpos1 (by linarith) hlim
  have h1 := h (n + 1) (by omega)
  simp only [lag_succ] at h1
  have h2 : 0 ≤ (cc - 1 - 1 / β) * ξ2 (n + 1) := mul_nonneg (by linarith) (hpos _)
  rw [show n + 1 + 1 = n + 2 by omega] at h1
  have e : (ξ2 (n + 1) - ξ2 n) / β = 1 / β * ξ2 (n + 1) - ξ2 n / β := by ring
  rw [e]
  nlinarith

/-- Cochrane (2023), §20.2.4, p. 479: **inflation never exceeds `B ≥ 0`** on a path where at
every date either the rate gap is at most `B` or the multiplier combination is `≤ 0`, with
`lamI ≤ 0` and `β^t π_t² → 0` (a discrete maximum principle; with `B = η` this is "commitment
inflation never exceeds the depth of the shock"). -/
theorem pi_le_bound {β κ σ ϑ B : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hB : 0 ≤ B) {x π : ℕ → ℝ} (hN : ∀ t, NKPC β κ x π t)
    (hd : ∀ t, gap σ x π t ≤ B ∨ lam κ ϑ x π t ≤ 0) (hI : lamI κ ϑ x π ≤ 0)
    (hS : Tendsto (fun t => β ^ t * π t ^ 2) atTop (𝓝 0)) (n : ℕ) : π n ≤ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1)) π ⟨n, by simp⟩
  rw [Finset.mem_range] at hm0
  have hpm : B < π m0 := lt_of_lt_of_le hcon (hmax n (by simp))
  have hθ : 0 < ϑ / κ ^ 2 := by positivity
  have hsk : 0 < σ / κ := by positivity
  have hdc : ∀ t, comb β (σ / κ) π t ≤ B ∨ comb β (ϑ / κ ^ 2) π t ≤ B := by
    intro t
    rcases hd t with h | h
    · left; rwa [← gap_comb hκ.ne' (hN t) (hN (t + 1))]
    · right; rw [← lam_comb hκ.ne' (hN t) (hN (t + 1))]; linarith
  have hup : π m0 < π (m0 + 1) := by
    rcases m0 with _ | j
    · rw [lamI_eq hκ.ne' (hN 0)] at hI
      by_contra hc
      push Not at hc
      have h0 : 0 < π 0 := by linarith
      have : (1 - β) * π 0 ≤ π 0 - β * π 1 := by nlinarith
      have : 0 ≤ ϑ / κ ^ 2 * (π 0 - β * π 1) :=
        mul_nonneg hθ.le (by nlinarith [mul_pos (show 0 < 1 - β by linarith) h0])
      linarith
    · have hj : π j ≤ π (j + 1) := hmax j (Finset.mem_range.mpr (by omega))
      rcases hdc j with h | h
      · exact comb_up hβ hsk h hpm hj
      · exact comb_up hβ hθ h hpm hj
  exact comb_blowup hβ hβ1.le hsk hθ hB (fun t _ => hdc t) (Nat.zero_le m0) (hpm.trans hup)
    hup hS

/-- Cochrane (2023), §20.2.4, p. 479: after date `K`, if at every date either the rate gap is
`≤ 0` or the multiplier combination is `≤ 0`, then negative inflation at `K + 1` stays
nonpositive forever (`β^t π_t² → 0`). -/
theorem post_nonpos {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) {x π : ℕ → ℝ} (hN : ∀ t, NKPC β κ x π t) {K : ℕ}
    (hd : ∀ t, K ≤ t → gap σ x π t ≤ 0 ∨ lam κ ϑ x π t ≤ 0) (hK : π (K + 1) < 0)
    (hS : Tendsto (fun t => β ^ t * π t ^ 2) atTop (𝓝 0)) (n : ℕ) (hn : K + 1 ≤ n) :
    π n ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image (Finset.Icc (K + 1) n) π
    ⟨n, Finset.mem_Icc.mpr ⟨hn, le_rfl⟩⟩
  rw [Finset.mem_Icc] at hm0
  have hpm : 0 < π m0 := lt_of_lt_of_le hcon (hmax n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩))
  have hθ : 0 < ϑ / κ ^ 2 := by positivity
  have hsk : 0 < σ / κ := by positivity
  have hdc : ∀ t, K ≤ t → comb β (σ / κ) π t ≤ 0 ∨ comb β (ϑ / κ ^ 2) π t ≤ 0 := by
    intro t ht
    rcases hd t ht with h | h
    · left; rwa [← gap_comb hκ.ne' (hN t) (hN (t + 1))]
    · right; rwa [← lam_comb hκ.ne' (hN t) (hN (t + 1))]
  have hne : m0 ≠ K + 1 := by rintro rfl; linarith
  obtain ⟨j, rfl⟩ : ∃ j, m0 = j + 1 := ⟨m0 - 1, by omega⟩
  have hj : π j ≤ π (j + 1) := hmax j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hup : π (j + 1) < π (j + 2) := by
    rcases hdc j (by omega) with h | h
    · exact comb_up hβ hsk h hpm hj
    · exact comb_up hβ hθ h hpm hj
  exact comb_blowup hβ hβ1.le hsk hθ le_rfl hdc (show K ≤ j + 1 by omega) (hpm.trans hup)
    hup hS

/-! ## A slack date inside the shock is impossible -/

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), §5.4.2: **case `σκ ≤ ϑ`.** On a path
satisfying the first-order conditions (`hmult`, `hmI`) with nonnegative multipliers, binding
dates as stated and `β^t π_t² → 0`, the multiplier `ξ₂,s` of a date `s ≤ t_Z` of the shock cannot
vanish: otherwise the rate gap at `s` is at most `(1 − σκ/ϑ) π_{s+1} ≤ (1 − σκ/ϑ) η < η`
(`pi_le_bound`), so `i_s < 0`. -/
theorem slack_contra_le {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hη : 0 < η) (hr : σ * κ ≤ ϑ) {tZ s : ℕ} (hsZ : s ≤ tZ) {x π ξ2 : ℕ → ℝ}
    (hN : ∀ t, NKPC β κ x π t) (hS : Tendsto (fun t => β ^ t * π t ^ 2) atTop (𝓝 0))
    (hpos : ∀ t, 0 ≤ ξ2 t)
    (hmult : ∀ t, κ * lam κ ϑ x π t =
      (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β)
    (hmI : κ * lamI κ ϑ x π = -ξ2 0)
    (htrap : ∀ t, t ≤ tZ → η ≤ gap σ x π t)
    (hbind : ∀ t, t ≤ tZ → 0 < ξ2 t → gap σ x π t = η)
    (hpost : ∀ t, tZ < t → 0 < ξ2 t → gap σ x π t ≤ 0) (hs0 : ξ2 s = 0) : False := by
  have hslack : ∀ t, ξ2 t = 0 → lam κ ϑ x π t ≤ 0 := by
    intro t ht
    have h := hmult t
    rw [ht] at h
    have hl : 0 ≤ lag ξ2 t := by
      cases t with
      | zero => simp
      | succ n => simpa using hpos n
    have hk : κ * lam κ ϑ x π t ≤ 0 := by
      rw [h]
      have := div_nonneg hl hβ.le
      have := hpos (t + 1)
      linarith
    by_contra hc
    push Not at hc
    linarith [mul_pos hκ hc]
  have hd : ∀ t, gap σ x π t ≤ η ∨ lam κ ϑ x π t ≤ 0 := by
    intro t
    rcases (hpos t).eq_or_lt with h | h
    · exact Or.inr (hslack t h.symm)
    · rcases le_or_gt t tZ with ht | ht
      · exact Or.inl (hbind t ht h).le
      · exact Or.inl ((hpost t ht h).trans hη.le)
  have hI : lamI κ ϑ x π ≤ 0 := by
    by_contra hc
    push Not at hc
    linarith [mul_pos hκ hc, hpos 0]
  have hpi := pi_le_bound hβ hβ1 hκ hσ hϑ hη.le hN hd hI hS (s + 1)
  have hg := htrap s hsZ
  rw [gap_lam hκ.ne' hϑ.ne'] at hg
  have hl := hslack s hs0
  set r := σ * κ / ϑ with hrdef
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hϑ]; exact hr
  have h1 : r * lam κ ϑ x π s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0.le hl
  have h2 : (1 - r) * π (s + 1) ≤ (1 - r) * η := mul_le_mul_of_nonneg_left hpi (by linarith)
  have h3 : 0 < r * η := mul_pos hr0 hη
  linarith

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), §5.4.2: **case `ϑ < σκ`.** Under the
hypotheses of `slack_contra_le` and `β^t ξ₂,t → 0`, a vanishing multiplier `ξ₂,s = 0` at a date
`s ≤ t_Z` is impossible. A slack date forces `π_{s+1} ≤ c = −η/(σκ/ϑ − 1)`; a discrete minimum
principle on the shock (the rate gap is `≥ η` there) propagates `π ≤ c` to the end of the shock
and makes inflation fall at its end; then inflation stays negative after the shock
(`post_nonpos`), the multipliers vanish from `s` on (`mult_zero_left`, `mult_zero_right`), and
the resulting peg dynamics explode, contradicting the finite loss. -/
theorem slack_contra_gt {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hη : 0 < η) (hr : ϑ < σ * κ) {tZ s : ℕ} (hsZ : s ≤ tZ) {x π ξ2 : ℕ → ℝ}
    (hN : ∀ t, NKPC β κ x π t) (hS : Tendsto (fun t => β ^ t * π t ^ 2) atTop (𝓝 0))
    (hpos : ∀ t, 0 ≤ ξ2 t) (hlim : Tendsto (fun t => β ^ t * ξ2 t) atTop (𝓝 0))
    (hmult : ∀ t, κ * lam κ ϑ x π t =
      (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β)
    (hmI : κ * lamI κ ϑ x π = -ξ2 0)
    (htrap : ∀ t, t ≤ tZ → η ≤ gap σ x π t)
    (hbind : ∀ t, t ≤ tZ → 0 < ξ2 t → gap σ x π t = η)
    (hpost : ∀ t, tZ < t → 0 < ξ2 t → gap σ x π t ≤ 0) (hs0 : ξ2 s = 0) : False := by
  set r := σ * κ / ϑ with hrdef
  have hr1 : 1 < r := by rw [hrdef, lt_div_iff₀ hϑ]; linarith
  have hr0 : 0 < r := by linarith
  set c := -η / (r - 1) with hcdef
  have hc : c < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hrc : (r - 1) * c = -η := by
    have hne : r - 1 ≠ 0 := by linarith
    rw [hcdef]; field_simp
  set θ := ϑ / κ ^ 2 with hθdef
  have hθ0 : 0 < θ := by positivity
  set cc := 1 + 1 / β + κ / (β * σ) with hccdef
  have hcc : 1 + 1 / β < cc := by
    have : 0 < κ / (β * σ) := by positivity
    linarith
  have hgl : ∀ t, gap σ x π t = r * lam κ ϑ x π t - (r - 1) * π (t + 1) :=
    fun t => gap_lam hκ.ne' hϑ.ne' x π t
  have hlamc : ∀ t, lam κ ϑ x π t = comb β θ π t := fun t => lam_comb hκ.ne' (hN t) (hN (t + 1))
  have hgapc : ∀ t, gap σ x π t = comb β (σ / κ) π t :=
    fun t => gap_comb hκ.ne' (hN t) (hN (t + 1))
  have hslack : ∀ t, ξ2 t = 0 → lam κ ϑ x π t ≤ 0 := by
    intro t ht
    have h := hmult t
    rw [ht] at h
    have hl : 0 ≤ lag ξ2 t := by
      cases t with
      | zero => simp
      | succ n => simpa using hpos n
    have hk : κ * lam κ ϑ x π t ≤ 0 := by
      rw [h]
      have := div_nonneg hl hβ.le
      have := hpos (t + 1)
      linarith
    by_contra hc'
    push Not at hc'
    linarith [mul_pos hκ hc']
  have hBLt : ∀ t, t ≤ tZ → π (t + 1) ≤ c → lam κ ϑ x π t ≤ 0 := by
    intro t ht hp
    rcases (hpos t).eq_or_lt with h | h
    · exact hslack t h.symm
    · have hg := hbind t ht h
      rw [hgl t] at hg
      have : (r - 1) * π (t + 1) ≤ (r - 1) * c := mul_le_mul_of_nonneg_left hp (by linarith)
      have hrl : r * lam κ ϑ x π t ≤ 0 := by linarith
      by_contra hc'
      push Not at hc'
      linarith [mul_pos hr0 hc']
  have hBLp : ∀ t, tZ < t → π (t + 1) ≤ 0 → lam κ ϑ x π t ≤ 0 := by
    intro t ht hp
    rcases (hpos t).eq_or_lt with h | h
    · exact hslack t h.symm
    · have hg := hpost t ht h
      rw [hgl t] at hg
      have : (r - 1) * π (t + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hp
      have hrl : r * lam κ ϑ x π t ≤ 0 := by linarith
      by_contra hc'
      push Not at hc'
      linarith [mul_pos hr0 hc']
  have hn0 : π (s + 1) ≤ c := by
    have hg := htrap s hsZ
    have hl := hslack s hs0
    rw [hgl s] at hg
    have : r * lam κ ϑ x π s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0.le hl
    have h1 : (r - 1) * π (s + 1) ≤ (r - 1) * c := by linarith
    exact le_of_mul_le_mul_left h1 (by linarith)
  have hTMP : ∀ j, j ≤ tZ → π (j + 1) ≤ π j → π (j + 1) ≤ π (j + 2) → η ≤ π (j + 1) := by
    intro j hj h1 h2
    have := htrap j hj
    rw [hgapc j] at this
    exact this.trans (comb_le_of_min hβ.le (by positivity) h1 h2)
  have hP0 : (∀ a, 1 ≤ a → a ≤ s + 1 → π a ≤ c) → π 1 < π 0 := by
    intro hL
    have hz := mult_zero_left hβ hcc hpos hs0 (fun t ht => by
      have hl := hBLt t (by omega) (hL (t + 1) (by omega) (by omega))
      rw [← hmult t]
      exact mul_nonpos_of_nonneg_of_nonpos hκ.le hl) 0 (Nat.zero_le _)
    rw [hz, neg_zero] at hmI
    have hI0 : lamI κ ϑ x π = 0 := (mul_eq_zero.mp hmI).resolve_left hκ.ne'
    rw [lamI_eq hκ.ne' (hN 0)] at hI0
    have hp1 : π 1 < 0 := lt_of_le_of_lt (hL 1 le_rfl (by omega)) hc
    by_contra hcon
    push Not at hcon
    have h1 : θ * (π 0 - β * π 1) ≤ θ * (π 1 - β * π 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hθ0.le
    have h2 : π 1 + θ * (π 1 - β * π 1) < 0 := by
      have : π 1 + θ * (π 1 - β * π 1) = π 1 * (1 + θ * (1 - β)) := by ring
      rw [this]
      exact mul_neg_of_neg_of_pos hp1 (by nlinarith)
    linarith
  have hR : ∀ n, s + 1 ≤ n → n ≤ tZ + 1 → π n ≤ c := by
    intro n hn1 hn2
    by_contra hb
    push Not at hb
    have hns : s + 1 < n := by
      rcases hn1.eq_or_lt with h | h
      · subst h; linarith
      · exact h
    by_cases hL : ∀ a, 1 ≤ a → a ≤ s + 1 → π a ≤ c
    · have h01 := hP0 hL
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc 0 n) π
        ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩
      rw [Finset.mem_Icc] at hm
      have hms : π m ≤ π (s + 1) := hmin _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hm0 : m ≠ 0 := by
        rintro rfl
        have := hmin 1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        linarith
      have hmn : m ≠ n := by
        rintro rfl
        linarith
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have := hTMP j (by omega) (hmin j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        (hmin (j + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
      linarith
    · push Not at hL
      obtain ⟨a, ha1, ha2, hac⟩ := hL
      have has : a < s + 1 := by
        rcases ha2.eq_or_lt with h | h
        · subst h; linarith
        · exact h
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc a n) π
        ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
      rw [Finset.mem_Icc] at hm
      have hms : π m ≤ π (s + 1) := hmin _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hma : m ≠ a := by
        rintro rfl
        linarith
      have hmn : m ≠ n := by
        rintro rfl
        linarith
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have := hTMP j (by omega) (hmin j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        (hmin (j + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
      linarith
  have hE : π (tZ + 2) ≤ π (tZ + 1) := by
    by_cases hL : ∀ a, 1 ≤ a → a ≤ s + 1 → π a ≤ c
    · have h01 := hP0 hL
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc 0 (tZ + 2)) π
        ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩
      rw [Finset.mem_Icc] at hm
      have hms : π m ≤ π (s + 1) := hmin _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hm0 : m ≠ 0 := by
        rintro rfl
        have := hmin 1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        linarith
      by_cases hmt : m = tZ + 2
      · subst hmt
        exact hmin _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have := hTMP j (by omega) (hmin j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
          (hmin (j + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        linarith
    · push Not at hL
      obtain ⟨a, ha1, ha2, hac⟩ := hL
      have has : a < s + 1 := by
        rcases ha2.eq_or_lt with h | h
        · subst h; linarith
        · exact h
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc a (tZ + 2)) π
        ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
      rw [Finset.mem_Icc] at hm
      have hms : π m ≤ π (s + 1) := hmin _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hma : m ≠ a := by
        rintro rfl
        linarith
      by_cases hmt : m = tZ + 2
      · subst hmt
        exact hmin _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have := hTMP j (by omega) (hmin j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
          (hmin (j + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        linarith
  have hK1 : π (tZ + 2) < 0 := lt_of_le_of_lt hE (lt_of_le_of_lt (hR (tZ + 1) (by omega) le_rfl) hc)
  have hB1 : ∀ n, tZ + 2 ≤ n → π n ≤ 0 := by
    intro n hn
    refine post_nonpos hβ hβ1 hκ hσ hϑ hN (K := tZ + 1) (fun t ht => ?_) hK1 hS n hn
    rcases (hpos t).eq_or_lt with h | h
    · exact Or.inr (hslack t h.symm)
    · exact Or.inl (hpost t (by omega) h)
  have hlam : ∀ t, s ≤ t → lam κ ϑ x π t ≤ 0 := by
    intro t ht
    rcases le_or_gt t tZ with h | h
    · exact hBLt t h (hR (t + 1) (by omega) (by omega))
    · exact hBLp t h (hB1 (t + 1) (by omega))
  have hz := mult_zero_right hβ hcc hpos hs0 (fun t ht => by
    rw [← hmult t]
    exact mul_nonpos_of_nonneg_of_nonpos hκ.le (hlam t ht.le)) hlim
  have hharm : ∀ t, s + 1 ≤ t → lam κ ϑ x π t = 0 := by
    intro t ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have h := hmult (t' + 1)
    rw [lag_succ, hz t' (by omega), hz (t' + 1) (by omega), hz (t' + 1 + 1) (by omega)] at h
    have h' : κ * lam κ ϑ x π (t' + 1) = 0 := by rw [h]; ring
    exact (mul_eq_zero.mp h').resolve_left hκ.ne'
  have hθa : ∀ n, s + 1 ≤ n → comb β θ (fun k => -π k) n ≤ 0 ∨ comb β θ (fun k => -π k) n ≤ 0 :=
    fun n hn => Or.inl (by rw [comb_neg, ← hlamc n, hharm n hn, neg_zero])
  have h3 : π (tZ + 3) < π (tZ + 2) := by
    have h := hharm (tZ + 1) (by omega)
    rw [hlamc] at h
    unfold comb at h
    rw [show tZ + 1 + 1 = tZ + 2 by omega, show tZ + 1 + 2 = tZ + 3 by omega] at h
    by_contra hcon
    push Not at hcon
    have e1 : θ * (π (tZ + 2) - π (tZ + 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ0.le (by linarith)
    have e2 : θ * (β * (π (tZ + 2) - π (tZ + 3))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ0.le
        (mul_nonpos_of_nonneg_of_nonpos hβ.le (by linarith))
    have e3 : θ * ((π (tZ + 2) - π (tZ + 1)) + β * (π (tZ + 2) - π (tZ + 3))) =
        θ * (π (tZ + 2) - π (tZ + 1)) + θ * (β * (π (tZ + 2) - π (tZ + 3))) := by ring
    linarith
  have hbl := comb_blowup hβ hβ1.le hθ0 hθ0 le_rfl (u := fun k => -π k) (N0 := s + 1)
    (m0 := tZ + 2) hθa (by omega) (by change 0 < -π (tZ + 3); linarith)
    (by change -π (tZ + 2) < -π (tZ + 3); linarith)
  apply hbl
  simpa only [neg_sq] using hS

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), §5.4.2: **on a KKT path whose multipliers
satisfy `β^t ξ₂,t → 0`, every zero-bound multiplier of the shock interval is strictly positive**,
`0 < ξ₂,s` for all `s ≤ t_Z` (any `β ∈ (0,1)`, `κ, σ, ϑ > 0`, `η > 0`, `ρ ≥ 0`). -/
theorem trap_mult_pos {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hF : Feasible β κ σ (natRate ρ η tZ) x π) (hs : Summable (lossTerm β ϑ x π))
    (h35 : ∀ t, FOC35 β σ π ξ1 ξ2 t) (h36 : ∀ t, FOC36 β κ ϑ x ξ1 ξ2 t)
    (hpos : ∀ t, 0 ≤ ξ2 t) (hcs : ∀ t, ξ2 t * impliedRate σ (natRate ρ η tZ) x π t = 0)
    (hlim : Tendsto (fun t => β ^ t * ξ2 t) atTop (𝓝 0)) (s : ℕ) (hsZ : s ≤ tZ) :
    0 < ξ2 s := by
  have hN : ∀ t, NKPC β κ x π t := fun t => (hF t).1
  have hS := tendsto_pi_sq hβ hϑ hs
  have hmult : ∀ t, κ * lam κ ϑ x π t =
      (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β :=
    fun t => lam_mult hκ.ne' (h35 (t + 1)) (h36 t) (h36 (t + 1))
  have hmI := lamI_mult hκ.ne' (h35 0) (h36 0)
  have hrate : ∀ t, 0 < ξ2 t → impliedRate σ (natRate ρ η tZ) x π t = 0 :=
    fun t ht => (mul_eq_zero.mp (hcs t)).resolve_left ht.ne'
  have htrap : ∀ t, t ≤ tZ → η ≤ gap σ x π t := by
    intro t ht
    have := rate_nonneg hσ hF t
    rw [impliedRate_eq_gap, natRate_of_le ht] at this
    linarith
  have hbind : ∀ t, t ≤ tZ → 0 < ξ2 t → gap σ x π t = η := by
    intro t ht h
    have := hrate t h
    rw [impliedRate_eq_gap, natRate_of_le ht] at this
    linarith
  have hpost : ∀ t, tZ < t → 0 < ξ2 t → gap σ x π t ≤ 0 := by
    intro t ht h
    have := hrate t h
    rw [impliedRate_eq_gap, natRate_of_lt ht] at this
    linarith
  rcases (hpos s).eq_or_lt with h0 | h0
  · exfalso
    rcases le_or_gt (σ * κ) ϑ with hr | hr
    · exact slack_contra_le hβ hβ1 hκ hσ hϑ hη hr hsZ hN hS hpos hmult hmI htrap hbind hpost
        h0.symm
    · exact slack_contra_gt hβ hβ1 hκ hσ hϑ hη hr hsZ hN hS hpos hlim hmult hmI htrap hbind
        hpost h0.symm
  · exact h0

/-! ## Necessity of the Karush–Kuhn–Tucker conditions -/

/-- Galí (2015), eqs. (35)–(36), p. 149; Cochrane (2023), §20.2.4, p. 479: the multipliers
`(ξ₁, ξ₂)` attached to a path by solving (35)–(36) forward from `ξ₁,₋₁ = ξ₂,₋₁ = 0`. -/
noncomputable def mult (β κ σ ϑ : ℝ) (x π : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (-π 0, -(κ * π 0) - ϑ * x 0)
  | t + 1 =>
    ((mult β κ σ ϑ x π t).1 + (mult β κ σ ϑ x π t).2 / (β * σ) - π (t + 1),
      (mult β κ σ ϑ x π t).2 / β +
        κ * ((mult β κ σ ϑ x π t).1 + (mult β κ σ ϑ x π t).2 / (β * σ) - π (t + 1)) -
          ϑ * x (t + 1))

/-- Galí (2015), eq. (35), p. 149; Cochrane (2023), p. 479: the Phillips-curve multiplier
`ξ₁` of `mult`. -/
noncomputable def mxi1 (β κ σ ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : ℝ := (mult β κ σ ϑ x π t).1

/-- Galí (2015), eq. (36), p. 149; Cochrane (2023), p. 479: the zero-bound multiplier `ξ₂` of
`mult`. -/
noncomputable def mxi2 (β κ σ ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : ℝ := (mult β κ σ ϑ x π t).2

/-- Galí (2015), eq. (35), p. 149; Cochrane (2023), p. 479: `mult` satisfies (35) at every date. -/
theorem foc35_mult (β κ σ ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) :
    FOC35 β σ π (mxi1 β κ σ ϑ x π) (mxi2 β κ σ ϑ x π) t := by
  unfold FOC35
  cases t with
  | zero => simp [mxi1, mult]
  | succ t => simp only [lag_succ, mxi1, mxi2, mult]; ring

/-- Galí (2015), eq. (36), p. 149; Cochrane (2023), p. 479: `mult` satisfies (36) at every date. -/
theorem foc36_mult (β κ σ ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) :
    FOC36 β κ ϑ x (mxi1 β κ σ ϑ x π) (mxi2 β κ σ ϑ x π) t := by
  unfold FOC36
  cases t with
  | zero => simp only [lag_zero, mxi1, mxi2, mult]; ring
  | succ t => simp only [lag_succ, mxi1, mxi2, mult]; ring

/-- Galí (2015), eqs. (35)–(36), p. 149; Cochrane (2023), p. 479: the multipliers solving
(35)–(36) on `[0, N]` are unique (they are `mult`). -/
theorem mult_unique {β κ σ ϑ : ℝ} {x π ξ1 ξ2 : ℕ → ℝ} {N : ℕ}
    (h : ∀ t, t ≤ N → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t) :
    ∀ t, t ≤ N → ξ1 t = mxi1 β κ σ ϑ x π t ∧ ξ2 t = mxi2 β κ σ ϑ x π t := by
  intro t
  induction t with
  | zero =>
    intro _
    obtain ⟨a, b⟩ := h 0 (Nat.zero_le _)
    unfold FOC35 at a
    unfold FOC36 at b
    simp only [lag_zero, zero_div, sub_zero] at a b
    simp only [mxi1, mxi2, mult]
    exact ⟨by linear_combination a, by linear_combination b + κ * a⟩
  | succ t ih =>
    intro ht
    obtain ⟨i1, i2⟩ := ih (by omega)
    obtain ⟨a, b⟩ := h (t + 1) ht
    unfold FOC35 at a
    unfold FOC36 at b
    simp only [lag_succ] at a b
    have e1 : ξ1 (t + 1) = mxi1 β κ σ ϑ x π (t + 1) := by
      simp only [mxi1, mult]
      rw [← mxi1, ← mxi2, ← i1, ← i2]
      linarith
    refine ⟨e1, ?_⟩
    simp only [mxi2, mult]
    rw [← mxi1, ← mxi2, ← i1, ← i2]
    have : ξ1 (t + 1) = ξ1 t + ξ2 t / (β * σ) - π (t + 1) := by linarith
    rw [← this]
    linarith

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: the cross term `β^t (π_t dπ_t + ϑ x_t dx_t)`
of the loss in a direction `(dx, dπ)`. -/
noncomputable def cross (β ϑ : ℝ) (x π dx dπ : ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t * (π t * dπ t + ϑ * x t * dx t)

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: the loss term along `(x, π) + ε (dx, dπ)`. -/
theorem lossTerm_pert (β ϑ ε : ℝ) (x π dx dπ : ℕ → ℝ) (t : ℕ) :
    lossTerm β ϑ (fun s => x s + ε * dx s) (fun s => π s + ε * dπ s) t =
      lossTerm β ϑ x π t + 2 * ε * cross β ϑ x π dx dπ t + ε ^ 2 * lossTerm β ϑ dx dπ t := by
  unfold lossTerm cross; ring

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: with finite losses the cross term is summable. -/
theorem summable_cross {β ϑ : ℝ} (hβ : 0 ≤ β) (hϑ : 0 < ϑ) {x π dx dπ : ℕ → ℝ}
    (h1 : Summable (lossTerm β ϑ x π)) (h2 : Summable (lossTerm β ϑ dx dπ)) :
    Summable (cross β ϑ x π dx dπ) := by
  refine Summable.of_norm_bounded ((h1.add h2).div_const 2) (fun t => ?_)
  unfold cross lossTerm
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ t)]
  have hp : 0 ≤ β ^ t := pow_nonneg hβ t
  have ha : |π t * dπ t + ϑ * x t * dx t| ≤
      ((π t ^ 2 + ϑ * x t ^ 2) + (dπ t ^ 2 + ϑ * dx t ^ 2)) / 2 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (π t + dπ t), sq_nonneg (x t + dx t), mul_nonneg hϑ.le
        (sq_nonneg (x t + dx t))]
    · nlinarith [sq_nonneg (π t - dπ t), sq_nonneg (x t - dx t), mul_nonneg hϑ.le
        (sq_nonneg (x t - dx t))]
  calc β ^ t * |π t * dπ t + ϑ * x t * dx t|
      ≤ β ^ t * (((π t ^ 2 + ϑ * x t ^ 2) + (dπ t ^ 2 + ϑ * dx t ^ 2)) / 2) :=
        mul_le_mul_of_nonneg_left ha hp
    _ = (β ^ t * (π t ^ 2 + ϑ * x t ^ 2) + β ^ t * (dπ t ^ 2 + ϑ * dx t ^ 2)) / 2 := by ring

/-- Galí (2015), p. 149; Cochrane (2023), §20.2.4, p. 479: **first-order necessary condition**.
If `(x, π)` is optimal and `(x, π) + ε (dx, dπ)` is feasible for all small `ε > 0` (`dx, dπ` with
finite loss), the derivative of the loss in that direction is nonnegative:
`0 ≤ ∑ β^t (π_t dπ_t + ϑ x_t dx_t)`. -/
theorem foc_dir {β κ σ ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {rn x π dx dπ : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ rn x π) (hd : Summable (lossTerm β ϑ dx dπ)) {ε0 : ℝ}
    (hε0 : 0 < ε0)
    (hfe : ∀ ε, 0 < ε → ε ≤ ε0 →
      Feasible β κ σ rn (fun t => x t + ε * dx t) (fun t => π t + ε * dπ t)) :
    0 ≤ ∑' t, cross β ϑ x π dx dπ t := by
  obtain ⟨-, hs, hmin⟩ := hopt
  have hc := summable_cross hβ.le hϑ hs hd
  set B := ∑' t, cross β ϑ x π dx dπ t with hB
  set L := ∑' t, lossTerm β ϑ dx dπ t with hL
  have hL0 : 0 ≤ L := tsum_nonneg fun t => by unfold lossTerm; positivity
  have key : ∀ ε, 0 < ε → ε ≤ ε0 → 0 ≤ 2 * B + ε * L := by
    intro ε hε he0
    have hsum : Summable (lossTerm β ϑ (fun s => x s + ε * dx s) (fun s => π s + ε * dπ s)) := by
      have := (hs.add (hc.mul_left (2 * ε))).add (hd.mul_left (ε ^ 2))
      exact this.congr fun t => (lossTerm_pert β ϑ ε x π dx dπ t).symm
    have hle := hmin _ _ (hfe ε hε he0) hsum
    have he : loss β ϑ (fun s => x s + ε * dx s) (fun s => π s + ε * dπ s) =
        loss β ϑ x π + 2 * ε * B + ε ^ 2 * L := by
      unfold loss
      rw [show (fun t => lossTerm β ϑ (fun s => x s + ε * dx s) (fun s => π s + ε * dπ s) t) =
        fun t => (lossTerm β ϑ x π t + 2 * ε * cross β ϑ x π dx dπ t) +
          ε ^ 2 * lossTerm β ϑ dx dπ t from funext fun t => lossTerm_pert β ϑ ε x π dx dπ t]
      rw [(hs.add (hc.mul_left (2 * ε))).tsum_add (hd.mul_left (ε ^ 2)),
        hs.tsum_add (hc.mul_left (2 * ε)), tsum_mul_left, tsum_mul_left]
    rw [he] at hle
    have h2 : 0 ≤ ε * (2 * B + ε * L) := by nlinarith
    by_contra hc
    push Not at hc
    nlinarith [mul_neg_of_pos_of_neg hε hc]
  by_contra hneg
  push Not at hneg
  set ε := min ε0 (-B / (L + 1)) with hε
  have hεpos : 0 < ε := lt_min hε0 (div_pos (by linarith) (by linarith))
  have k := key ε hεpos (min_le_left _ _)
  have h1 : ε * L ≤ -B / (L + 1) * L := mul_le_mul_of_nonneg_right (min_le_right _ _) hL0
  have h2 : -B / (L + 1) * L < -B := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- Galí (2015), p. 149 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 479:
`(x, π) + ε (dx, dπ)` is feasible when `(dx, dπ)` satisfies the linear Phillips curve and the
change of `x_t − υ₁,t` keeps the bound: `(x_t − υ₁,t) + ε (dx_t − dx_{t+1} − dπ_{t+1}/σ) ≤ 0`. -/
theorem feasible_pert {β κ σ ε : ℝ} {rn x π dx dπ : ℕ → ℝ} (hF : Feasible β κ σ rn x π)
    (hd : ∀ t, dπ t = β * dπ (t + 1) + κ * dx t)
    (hb : ∀ t, x t - ups1 σ rn x π t + ε * (dx t - dx (t + 1) - dπ (t + 1) / σ) ≤ 0) :
    Feasible β κ σ rn (fun t => x t + ε * dx t) (fun t => π t + ε * dπ t) := by
  intro t
  obtain ⟨hN, -⟩ := hF t
  refine ⟨?_, ?_⟩
  · unfold NKPC at hN ⊢
    simp only
    rw [hN, hd t]
    ring
  · have := hb t
    unfold ups1 at this ⊢
    simp only
    have e : x (t + 1) + ε * dx (t + 1) + (π (t + 1) + ε * dπ (t + 1) + rn t) / σ =
        x (t + 1) + (π (t + 1) + rn t) / σ + ε * (dx (t + 1) + dπ (t + 1) / σ) := by ring
    rw [e]
    linarith

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: the cross term is odd in the direction. -/
theorem cross_neg (β ϑ : ℝ) (x π dx dπ : ℕ → ℝ) (t : ℕ) :
    cross β ϑ x π (fun s => -dx s) (fun s => -dπ s) t = -cross β ϑ x π dx dπ t := by
  unfold cross; ring

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), p. 475: a direction obeying one backward step
at forcing `e` satisfies the linear Phillips curve and changes `x_t − υ₁,t` by `−e/σ` (raises
the rate gap by `e`). -/
theorem dir_of_step {β κ σ e : ℝ} (hσ : σ ≠ 0) {d : ℕ → ℝ × ℝ} {t : ℕ}
    (h : d t = backStep β κ σ e (d (t + 1))) :
    (d t).2 = β * (d (t + 1)).2 + κ * (d t).1 ∧
      (d t).1 - (d (t + 1)).1 - (d (t + 1)).2 / σ = -(e / σ) := by
  rw [h]
  simp only [backStep]
  constructor
  · field_simp; ring
  · ring

/-- Cochrane (2023), §20.2.4, p. 479 (Galí (2015), (34)): the direction **"raise the rate at date
`s` by one, holding all other rates and the path after `s` fixed"**: zero after `s`,
`(−1/σ, −κ/σ)` at `s`, and the zero-gap backward recursion before `s` (finite support). -/
noncomputable def hdir (β κ σ : ℝ) (s t : ℕ) : ℝ × ℝ :=
  if t ≤ s then backState β κ σ 0 (-(1 / σ), -(κ / σ)) (s - t) else (0, 0)

/-- Cochrane (2023), p. 479: `hdir` is zero after `s`. -/
theorem hdir_gt {β κ σ : ℝ} {s t : ℕ} (h : s < t) : hdir β κ σ s t = (0, 0) := by
  simp [hdir, Nat.not_le.mpr h]

/-- Cochrane (2023), p. 479 (Galí (2015), (34)): `hdir` obeys one backward step at forcing `1`
at `s` and `0` elsewhere. -/
theorem hdir_step (β κ σ : ℝ) (s t : ℕ) :
    hdir β κ σ s t = backStep β κ σ (if t = s then 1 else 0) (hdir β κ σ s (t + 1)) := by
  rcases lt_trichotomy t s with h | rfl | h
  · unfold hdir
    simp only [show t ≤ s from h.le, show t + 1 ≤ s from h, ↓reduceIte, h.ne]
    rw [show s - t = (s - (t + 1)) + 1 by omega]
    rfl
  · rw [hdir_gt (show t < t + 1 by omega)]
    simp only [hdir, le_refl, ↓reduceIte, Nat.sub_self, backState, backStep]
    ext <;> simp
  · rw [hdir_gt h, hdir_gt (show s < t + 1 by omega)]
    simp only [h.ne', ↓reduceIte, backStep]
    ext <;> simp

/-- Cochrane (2023), p. 479: `hdir` satisfies the linear Phillips curve and raises the rate gap
by one exactly at `s`. -/
theorem hdir_dir {β κ σ : ℝ} (hσ : σ ≠ 0) (s t : ℕ) :
    (hdir β κ σ s t).2 = β * (hdir β κ σ s (t + 1)).2 + κ * (hdir β κ σ s t).1 ∧
      (hdir β κ σ s t).1 - (hdir β κ σ s (t + 1)).1 - (hdir β κ σ s (t + 1)).2 / σ =
        -((if t = s then 1 else 0) / σ) :=
  dir_of_step hσ (d := hdir β κ σ s) (hdir_step β κ σ s t)

/-- Galí (2015), p. 148: `hdir` has finite loss (finite support). -/
theorem hdir_summable (β ϑ κ σ : ℝ) (s : ℕ) :
    Summable (lossTerm β ϑ (fun t => (hdir β κ σ s t).1) (fun t => (hdir β κ σ s t).2)) := by
  refine summable_of_ne_finset_zero (s := Finset.range (s + 1)) fun t ht => ?_
  rw [Finset.mem_range, not_lt] at ht
  simp [lossTerm, hdir_gt (show s < t by omega)]

/-- Galí (2015), p. 149 (the Lagrangian identity `lagrangian_identity`); Cochrane (2023), p. 479:
the derivative of the loss in the direction `hdir s` is `β^s ξ₂,s / σ`, for any multipliers
solving (35)–(36). -/
theorem cross_hdir {β κ σ ϑ : ℝ} (hβ : β ≠ 0) (hσ : σ ≠ 0) {x π ξ1 ξ2 : ℕ → ℝ}
    (h35 : ∀ t, FOC35 β σ π ξ1 ξ2 t) (h36 : ∀ t, FOC36 β κ ϑ x ξ1 ξ2 t) (s : ℕ) :
    ∑' t, cross β ϑ x π (fun t => (hdir β κ σ s t).1) (fun t => (hdir β κ σ s t).2) t =
      β ^ s * ξ2 s / σ := by
  have hd : ∀ t, (hdir β κ σ s t).2 = β * (hdir β κ σ s (t + 1)).2 + κ * (hdir β κ σ s t).1 :=
    fun t => (hdir_dir hσ s t).1
  rw [tsum_eq_sum (s := Finset.range (s + 1 + 1)) fun t ht => by
    rw [Finset.mem_range, not_lt] at ht
    simp [cross, hdir_gt (show s < t by omega)]]
  unfold cross
  rw [lagrangian_identity hβ hσ h35 h36 hd (s + 1)]
  rw [hdir_gt (show s < s + 1 by omega), hdir_gt (show s < s + 1 + 1 by omega)]
  simp only [mul_zero, sub_zero]
  rw [Finset.sum_eq_single s]
  · have := (hdir_dir (β := β) (κ := κ) hσ s s).2
    simp only [↓reduceIte] at this
    have e : (hdir β κ σ s (s + 1)).1 + (hdir β κ σ s (s + 1)).2 / σ - (hdir β κ σ s s).1 =
        1 / σ := by linarith
    rw [e]
    ring
  · intro u _ hu
    have := (hdir_dir (β := β) (κ := κ) hσ s u).2
    simp only [hu, ↓reduceIte, zero_div, neg_zero] at this
    have e : (hdir β κ σ s (u + 1)).1 + (hdir β κ σ s (u + 1)).2 / σ - (hdir β κ σ s u).1 = 0 :=
      by linarith
    rw [e]
    ring
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- Cochrane (2023), §20.1, p. 467 (`ZLBPeg`), §20.2.2, p. 475: the bounded peg mode
`w_t = λ₁⁻ᵗ (v_x, 1)`, a direction with zero rate gap at every date. -/
noncomputable def wdir (β κ σ : ℝ) (t : ℕ) : ℝ × ℝ :=
  ((l1 β σ κ)⁻¹ ^ t * vx β σ κ, (l1 β σ κ)⁻¹ ^ t)

/-- Cochrane (2023), p. 475 (`backStep_eigen`): `w` obeys the zero-gap backward recursion. -/
theorem wdir_step {β κ σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (t : ℕ) :
    wdir β κ σ t = backStep β κ σ 0 (wdir β κ σ (t + 1)) := by
  have hl : l1 β σ κ ≠ 0 := by linarith [one_lt_l1 hβ hσ hκ]
  unfold wdir
  rw [backStep_eigen hβ hσ hκ]
  have e : l1 β σ κ * (l1 β σ κ)⁻¹ ^ (t + 1) = (l1 β σ κ)⁻¹ ^ t := by
    rw [pow_succ]; field_simp
  ext
  · simp only; rw [← mul_assoc, e]
  · simp only; rw [e]

/-- Cochrane (2023), p. 475: `w` satisfies the linear Phillips curve and leaves every rate gap
unchanged. -/
theorem wdir_dir {β κ σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (t : ℕ) :
    (wdir β κ σ t).2 = β * (wdir β κ σ (t + 1)).2 + κ * (wdir β κ σ t).1 ∧
      (wdir β κ σ t).1 - (wdir β κ σ (t + 1)).1 - (wdir β κ σ (t + 1)).2 / σ = 0 := by
  have := dir_of_step hσ.ne' (d := wdir β κ σ) (wdir_step hβ hσ hκ t)
  simpa using this

/-- Galí (2015), p. 148: the peg mode has finite loss (`β λ₁⁻² < 1`). -/
theorem wdir_summable {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) :
    Summable (lossTerm β ϑ (fun t => (wdir β κ σ t).1) (fun t => (wdir β κ σ t).2)) := by
  have hl := one_lt_l1 hβ hσ hκ
  set q := (l1 β σ κ)⁻¹ with hq
  have hq0 : 0 < q := inv_pos.mpr (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hl
  have hg : β * q ^ 2 < 1 := by
    have : q ^ 2 < 1 := by nlinarith
    nlinarith
  have e : (lossTerm β ϑ (fun t => (wdir β κ σ t).1) (fun t => (wdir β κ σ t).2)) =
      fun t => (1 + ϑ * vx β σ κ ^ 2) * (β * q ^ 2) ^ t := by
    funext t
    simp only [lossTerm, wdir]
    rw [← hq]
    ring
  rw [e]
  exact (summable_geometric_of_lt_one (by positivity) hg).mul_left _

/-- Galí (2015), p. 149; Cochrane (2023), §20.2.4, p. 479 (the choice among the peg family is
free): at an optimum the derivative of the loss in the peg direction vanishes. -/
theorem cross_wdir {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) {rn x π : ℕ → ℝ} (hopt : Optimal β κ σ ϑ rn x π) :
    ∑' t, cross β ϑ x π (fun t => (wdir β κ σ t).1) (fun t => (wdir β κ σ t).2) t = 0 := by
  have hw := wdir_summable (ϑ := ϑ) hβ hβ1 hσ hκ
  have hd := fun t => (wdir_dir hβ hσ hκ t)
  have h1 := foc_dir hβ hϑ hopt hw one_pos fun ε _ _ =>
    feasible_pert hopt.1 (fun t => (hd t).1) fun t => by
      rw [(hd t).2, mul_zero, add_zero]; linarith [(hopt.1 t).2]
  have hwn : Summable (lossTerm β ϑ (fun t => -(wdir β κ σ t).1) fun t => -(wdir β κ σ t).2) :=
    hw.congr fun t => by simp [lossTerm]
  have h2 := foc_dir hβ hϑ hopt hwn one_pos fun ε _ _ =>
    feasible_pert hopt.1 (fun t => by rw [(hd t).1]; ring) fun t => by
      have := (hd t).2
      have e : -(wdir β κ σ t).1 - -(wdir β κ σ (t + 1)).1 - -(wdir β κ σ (t + 1)).2 / σ = 0 := by
        rw [neg_div]; linarith
      rw [e, mul_zero, add_zero]; linarith [(hopt.1 t).2]
  simp only [cross_neg, tsum_neg] at h2
  linarith

/-! ### The two modes of the zero-gap dynamics and transversality of the multipliers -/

/-- Cochrane (2023), eq. (5.6), p. 119: the output-gap coordinate `(1 − λ₁)/κ` of the stable
backward mode `λ₂` of the zero-gap dynamics. -/
noncomputable def vx2 (β σ κ : ℝ) : ℝ := (1 - l1 β σ κ) / κ

/-- Cochrane (2023), p. 479: the coefficient of the `λ₁`-mode in `(−1/σ, −κ/σ)`. -/
noncomputable def cf1 (β σ κ : ℝ) : ℝ := -(κ / σ) * l1 β σ κ / (l1 β σ κ - l2 β σ κ)

/-- Cochrane (2023), p. 479: the coefficient of the `λ₂`-mode in `(−1/σ, −κ/σ)`. -/
noncomputable def cf2 (β σ κ : ℝ) : ℝ := κ / σ * l2 β σ κ / (l1 β σ κ - l2 β σ κ)

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₁ + λ₂ = 1 + β + κ/σ`. -/
theorem l_add (β σ κ : ℝ) : l1 β σ κ + l2 β σ κ = 1 + β + κ / σ := by
  have := ZLBPeg.lam_add β σ⁻¹ κ
  unfold l1 l2
  rw [this]
  ring

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₁ λ₂ = β`. -/
theorem l_mul {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    l1 β σ κ * l2 β σ κ = β :=
  ZLBPeg.lam_mul hβ (by positivity)

/-- Cochrane (2023), eq. (5.6), p. 119: `0 < λ₂ < 1 < λ₁`. -/
theorem l2_bounds {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    0 < l2 β σ κ ∧ l2 β σ κ < 1 :=
  ⟨ZLBPeg.lam2_pos hβ (by positivity), ZLBPeg.lam2_lt_one hβ (by positivity)⟩

/-- Cochrane (2023), p. 475: `λ₂ v₂ = v₂ + σ⁻¹` (the `λ₂` eigenvector of the backward map). -/
theorem l2_vx2 {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    l2 β σ κ * vx2 β σ κ = vx2 β σ κ + σ⁻¹ := by
  have ha := l_add β σ κ
  have hm := l_mul hβ hσ hκ
  have key : (l2 β σ κ - 1) * (1 - l1 β σ κ) = κ / σ := by linear_combination ha - hm
  unfold vx2
  rw [show l2 β σ κ * ((1 - l1 β σ κ) / κ) =
    (1 - l1 β σ κ) / κ + (l2 β σ κ - 1) * (1 - l1 β σ κ) / κ by ring, key]
  field_simp

/-- Cochrane (2023), p. 475: `κ v₂ + β + κ/σ = λ₂`. -/
theorem kappa_vx2 {β σ κ : ℝ} (hκ : 0 < κ) : κ * vx2 β σ κ + (β + κ / σ) = l2 β σ κ := by
  have ha := l_add β σ κ
  have : κ * vx2 β σ κ = 1 - l1 β σ κ := by unfold vx2; field_simp
  rw [this]
  linarith

/-- Cochrane (2023), p. 479: `(−1/σ, −κ/σ) = c₁ (v_x, 1) + c₂ (v₂, 1)`, first coordinate. -/
theorem cf_vx {β σ κ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hl : l1 β σ κ - l2 β σ κ ≠ 0) :
    cf1 β σ κ * vx β σ κ + cf2 β σ κ * vx2 β σ κ = -(1 / σ) := by
  unfold cf1 cf2 vx vx2
  field_simp
  ring

/-- Cochrane (2023), p. 479: `(−1/σ, −κ/σ) = c₁ (v_x, 1) + c₂ (v₂, 1)`, second coordinate. -/
theorem cf_sum {β σ κ : ℝ} (hl : l1 β σ κ - l2 β σ κ ≠ 0) :
    cf1 β σ κ + cf2 β σ κ = -(κ / σ) := by
  unfold cf1 cf2
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 475 (Galí (2015), (34)): `k` zero-gap backward steps from
`(−1/σ, −κ/σ)` are `c₁ λ₁ᵏ (v_x, 1) + c₂ λ₂ᵏ (v₂, 1)`. -/
theorem backState_closed {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (k : ℕ) :
    backState β κ σ 0 (-(1 / σ), -(κ / σ)) k =
      (cf1 β σ κ * l1 β σ κ ^ k * vx β σ κ + cf2 β σ κ * l2 β σ κ ^ k * vx2 β σ κ,
        cf1 β σ κ * l1 β σ κ ^ k + cf2 β σ κ * l2 β σ κ ^ k) := by
  have hl : l1 β σ κ - l2 β σ κ ≠ 0 := by
    have := one_lt_l1 hβ hσ hκ
    have := (l2_bounds hβ hσ hκ).2
    linarith
  have h1 := l1_vx hβ hσ hκ
  have h2 := l2_vx2 hβ hσ hκ
  have g1 := kappa_vx (β := β) (σ := σ) hκ
  have g2 := kappa_vx2 (β := β) (σ := σ) hκ
  induction k with
  | zero =>
    simp only [backState, pow_zero, mul_one]
    rw [cf_vx hκ hσ hl, cf_sum hl]
  | succ k ih =>
    simp only [backState]
    rw [ih]
    simp only [backStep]
    ext
    · simp only
      linear_combination (-(cf1 β σ κ * l1 β σ κ ^ k)) * h1 - cf2 β σ κ * l2 β σ κ ^ k * h2
    · simp only
      linear_combination (cf1 β σ κ * l1 β σ κ ^ k) * g1 + (cf2 β σ κ * l2 β σ κ ^ k) * g2

/-- Cochrane (2023), p. 479: the direction `hdir s` minus `c₁ λ₁ˢ` times the peg mode: only the
stable backward mode `λ₂^{s−t}` survives before `s`, and the forward-decaying `λ₁^{-(t−s)}`
after. -/
noncomputable def ddir (β κ σ : ℝ) (s t : ℕ) : ℝ × ℝ :=
  ((hdir β κ σ s t).1 - cf1 β σ κ * l1 β σ κ ^ s * (wdir β κ σ t).1,
    (hdir β κ σ s t).2 - cf1 β σ κ * l1 β σ κ ^ s * (wdir β κ σ t).2)

/-- Cochrane (2023), p. 479: `ddir` before `s`. -/
theorem ddir_le {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {s t : ℕ} (h : t ≤ s) :
    ddir β κ σ s t = (cf2 β σ κ * l2 β σ κ ^ (s - t) * vx2 β σ κ,
      cf2 β σ κ * l2 β σ κ ^ (s - t)) := by
  have hl0 : l1 β σ κ ≠ 0 := by linarith [one_lt_l1 hβ hσ hκ]
  have e : l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t = l1 β σ κ ^ (s - t) := by
    rw [show s = (s - t) + t by omega, pow_add, Nat.add_sub_cancel, mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hl0, one_pow, mul_one]
  unfold ddir wdir
  rw [show hdir β κ σ s t = backState β κ σ 0 (-(1 / σ), -(κ / σ)) (s - t) by
    simp [hdir, h], backState_closed hβ hσ hκ]
  ext
  · simp only
    rw [show cf1 β σ κ * l1 β σ κ ^ s * ((l1 β σ κ)⁻¹ ^ t * vx β σ κ) =
      cf1 β σ κ * (l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t) * vx β σ κ by ring, e]
    ring
  · simp only
    rw [show cf1 β σ κ * l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t =
      cf1 β σ κ * (l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t) by ring, e]
    ring

/-- Cochrane (2023), p. 479: `ddir` after `s`. -/
theorem ddir_gt {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {s t : ℕ} (h : s < t) :
    ddir β κ σ s t = (-(cf1 β σ κ * (l1 β σ κ)⁻¹ ^ (t - s) * vx β σ κ),
      -(cf1 β σ κ * (l1 β σ κ)⁻¹ ^ (t - s))) := by
  have hl0 : l1 β σ κ ≠ 0 := by linarith [one_lt_l1 hβ hσ hκ]
  have e : l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t = (l1 β σ κ)⁻¹ ^ (t - s) := by
    rw [show t = (t - s) + s by omega, pow_add, Nat.add_sub_cancel, mul_comm, mul_assoc,
      ← mul_pow, inv_mul_cancel₀ hl0, one_pow, mul_one]
  unfold ddir wdir
  rw [hdir_gt h]
  ext
  · simp only
    rw [show cf1 β σ κ * l1 β σ κ ^ s * ((l1 β σ κ)⁻¹ ^ t * vx β σ κ) =
      cf1 β σ κ * (l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t) * vx β σ κ by ring, e]
    ring
  · simp only
    rw [show cf1 β σ κ * l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t =
      cf1 β σ κ * (l1 β σ κ ^ s * (l1 β σ κ)⁻¹ ^ t) by ring, e]
    ring

/-- Cochrane (2023), p. 479: `ddir` is bounded uniformly in `s` and `t`. -/
theorem ddir_bound {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (s t : ℕ) :
    |(ddir β κ σ s t).1| ≤ |cf1 β σ κ| * (|vx β σ κ| + 1) + |cf2 β σ κ| * (|vx2 β σ κ| + 1) ∧
      |(ddir β κ σ s t).2| ≤
        |cf1 β σ κ| * (|vx β σ κ| + 1) + |cf2 β σ κ| * (|vx2 β σ κ| + 1) := by
  obtain ⟨h20, h21⟩ := l2_bounds hβ hσ hκ
  have hl := one_lt_l1 hβ hσ hκ
  have hq0 : 0 < (l1 β σ κ)⁻¹ := inv_pos.mpr (by linarith)
  have hq1 : (l1 β σ κ)⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hl).le
  have a1 := abs_nonneg (cf1 β σ κ)
  have a2 := abs_nonneg (cf2 β σ κ)
  have b1 := abs_nonneg (vx β σ κ)
  have b2 := abs_nonneg (vx2 β σ κ)
  rcases le_or_gt t s with h | h
  · rw [ddir_le hβ hσ hκ h]
    have p0 : 0 ≤ l2 β σ κ ^ (s - t) := pow_nonneg h20.le _
    have p1 : l2 β σ κ ^ (s - t) ≤ 1 := pow_le_one₀ h20.le h21.le
    simp only [abs_mul, abs_of_nonneg p0]
    constructor
    · have : |cf2 β σ κ| * l2 β σ κ ^ (s - t) * |vx2 β σ κ| ≤ |cf2 β σ κ| * |vx2 β σ κ| := by
        have := mul_le_mul_of_nonneg_left p1 a2
        nlinarith
      nlinarith
    · have : |cf2 β σ κ| * l2 β σ κ ^ (s - t) ≤ |cf2 β σ κ| :=
        mul_le_of_le_one_right a2 p1
      nlinarith
  · rw [ddir_gt hβ hσ hκ h]
    have p0 : 0 ≤ (l1 β σ κ)⁻¹ ^ (t - s) := pow_nonneg hq0.le _
    have p1 : (l1 β σ κ)⁻¹ ^ (t - s) ≤ 1 := pow_le_one₀ hq0.le hq1
    simp only [abs_neg, abs_mul, abs_of_nonneg p0]
    constructor
    · have : |cf1 β σ κ| * (l1 β σ κ)⁻¹ ^ (t - s) * |vx β σ κ| ≤ |cf1 β σ κ| * |vx β σ κ| := by
        have := mul_le_mul_of_nonneg_left p1 a1
        nlinarith
      nlinarith
    · have : |cf1 β σ κ| * (l1 β σ κ)⁻¹ ^ (t - s) ≤ |cf1 β σ κ| :=
        mul_le_of_le_one_right a1 p1
      nlinarith

/-- Galí (2015), p. 148: with a finite loss, `β^t |π_t|` and `β^t |x_t|` are summable. -/
theorem summable_abs {β ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {x π : ℕ → ℝ}
    (hs : Summable (lossTerm β ϑ x π)) :
    Summable (fun t => β ^ t * |π t|) ∧ Summable (fun t => β ^ t * |x t|) := by
  have hg : Summable (fun t : ℕ => β ^ t) := summable_geometric_of_lt_one hβ.le hβ1
  have hp : Summable (fun t => β ^ t * π t ^ 2) := by
    refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_) hs
    unfold lossTerm
    have : 0 ≤ β ^ t * (ϑ * x t ^ 2) := by positivity
    nlinarith
  have hx : Summable (fun t => β ^ t * x t ^ 2) := by
    refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_) (hs.div_const ϑ)
    unfold lossTerm
    rw [le_div_iff₀ hϑ]
    have : 0 ≤ β ^ t * π t ^ 2 * ϑ := by positivity
    nlinarith
  constructor
  · refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
      ((hg.add hp).div_const 2)
    have hpt : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have : |π t| ≤ (1 + π t ^ 2) / 2 := by nlinarith [sq_nonneg (|π t| - 1), sq_abs (π t)]
    nlinarith
  · refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
      ((hg.add hx).div_const 2)
    have hpt : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have : |x t| ≤ (1 + x t ^ 2) / 2 := by nlinarith [sq_nonneg (|x t| - 1), sq_abs (x t)]
    nlinarith

/-- Galí (2015), p. 149; Cochrane (2023), §20.2.4, p. 479: **transversality of the multipliers**.
At an optimum the zero-bound multipliers of `mult` satisfy `β^t ξ₂,t → 0`: the derivative in the
direction `hdir t` equals that in the localised direction `ddir t` (the peg-mode derivative is
zero, `cross_wdir`), which tends to zero by dominated convergence (Tannery). -/
theorem tendsto_mxi2 {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) {rn x π : ℕ → ℝ} (hopt : Optimal β κ σ ϑ rn x π) :
    Tendsto (fun t => β ^ t * mxi2 β κ σ ϑ x π t) atTop (𝓝 0) := by
  have hs := hopt.2.1
  have hw := wdir_summable (ϑ := ϑ) hβ hβ1 hσ hκ
  have hcw := summable_cross hβ.le hϑ hs hw
  have hw0 := cross_wdir hβ hβ1 hκ hσ hϑ hopt
  have hsplit : ∀ s, β ^ s * mxi2 β κ σ ϑ x π s / σ =
      ∑' t, cross β ϑ x π (fun t => (ddir β κ σ s t).1) (fun t => (ddir β κ σ s t).2) t := by
    intro s
    rw [← cross_hdir hβ.ne' hσ.ne' (foc35_mult β κ σ ϑ x π) (foc36_mult β κ σ ϑ x π) s]
    have hch := summable_cross hβ.le hϑ hs (hdir_summable β ϑ κ σ s)
    set c := cf1 β σ κ * l1 β σ κ ^ s
    have e : (fun t => cross β ϑ x π (fun t => (hdir β κ σ s t).1)
        (fun t => (hdir β κ σ s t).2) t) = fun t =>
        cross β ϑ x π (fun t => (ddir β κ σ s t).1) (fun t => (ddir β κ σ s t).2) t +
          c * cross β ϑ x π (fun t => (wdir β κ σ t).1) (fun t => (wdir β κ σ t).2) t := by
      funext t
      simp only [cross, ddir, c]
      ring
    have hcd : Summable (fun t => cross β ϑ x π (fun t => (ddir β κ σ s t).1)
        (fun t => (ddir β κ σ s t).2) t) := by
      have := hch.sub (hcw.mul_left c)
      refine this.congr fun t => ?_
      have := congrFun e t
      linarith
    rw [e, hcd.tsum_add (hcw.mul_left c), tsum_mul_left, hw0, mul_zero, add_zero]
  obtain ⟨hsp, hsx⟩ := summable_abs hβ hβ1 hϑ hs
  set C := |cf1 β σ κ| * (|vx β σ κ| + 1) + |cf2 β σ κ| * (|vx2 β σ κ| + 1)
  have hC : 0 ≤ C := by positivity
  have hT : Tendsto (fun s => ∑' t, cross β ϑ x π (fun t => (ddir β κ σ s t).1)
      (fun t => (ddir β κ σ s t).2) t) atTop (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun t =>
      C * (β ^ t * |π t|) + ϑ * C * (β ^ t * |x t|))
      ((hsp.mul_left C).add (hsx.mul_left (ϑ * C))) (fun t => ?_) ?_
    · obtain ⟨h20, h21⟩ := l2_bounds hβ hσ hκ
      have hp : Tendsto (fun s : ℕ => l2 β σ κ ^ (s - t)) atTop (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one h20.le h21).comp (tendsto_sub_atTop_nat t)
      have hm := hp.const_mul (β ^ t * cf2 β σ κ * (π t + ϑ * x t * vx2 β σ κ))
      rw [mul_zero] at hm
      refine hm.congr' ?_
      filter_upwards [eventually_ge_atTop t] with s hst
      simp only [cross, ddir_le hβ hσ hκ hst]
      ring
    · refine Eventually.of_forall fun s t => ?_
      obtain ⟨b1, b2⟩ := ddir_bound hβ hσ hκ s t
      unfold cross
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ.le t)]
      have hpt : 0 ≤ β ^ t := pow_nonneg hβ.le t
      have h1 : |π t * (ddir β κ σ s t).2 + ϑ * x t * (ddir β κ σ s t).1| ≤
          |π t| * C + ϑ * |x t| * C := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hϑ]
        have := mul_le_mul_of_nonneg_left b2 (abs_nonneg (π t))
        have := mul_le_mul_of_nonneg_left b1 (mul_nonneg hϑ.le (abs_nonneg (x t)))
        nlinarith
      calc β ^ t * |π t * (ddir β κ σ s t).2 + ϑ * x t * (ddir β κ σ s t).1|
          ≤ β ^ t * (|π t| * C + ϑ * |x t| * C) := mul_le_mul_of_nonneg_left h1 hpt
        _ = C * (β ^ t * |π t|) + ϑ * C * (β ^ t * |x t|) := by ring
  rw [tsum_zero] at hT
  have := hT.const_mul σ
  rw [mul_zero] at this
  refine this.congr fun s => ?_
  rw [← hsplit s]
  field_simp

/-- Galí (2015), p. 149; Cochrane (2023), §20.2.4, p. 479: **necessity of the KKT conditions**.
If `(x, π)` solves the commitment problem (for any natural-rate path), the multipliers `mult`
solve (35)–(36), are nonnegative, satisfy complementary slackness, and `β^t ξ₂,t → 0`. -/
theorem kkt_necessary {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) {rn x π : ℕ → ℝ} (hopt : Optimal β κ σ ϑ rn x π) :
    KKT β κ σ ϑ rn x π (mxi1 β κ σ ϑ x π) (mxi2 β κ σ ϑ x π) ∧
      Tendsto (fun t => β ^ t * mxi2 β κ σ ϑ x π t) atTop (𝓝 0) := by
  have hF := hopt.1
  have hcr := fun s => cross_hdir hβ.ne' hσ.ne' (foc35_mult β κ σ ϑ x π)
    (foc36_mult β κ σ ϑ x π) (ϑ := ϑ) (κ := κ) s
  have hdd := fun s t => hdir_dir (β := β) (κ := κ) hσ.ne' s t
  have hnn : ∀ s, 0 ≤ mxi2 β κ σ ϑ x π s := by
    intro s
    have h := foc_dir hβ hϑ hopt (hdir_summable β ϑ κ σ s) one_pos fun ε hε _ =>
      feasible_pert hF (fun t => (hdd s t).1) fun t => by
        rw [(hdd s t).2]
        have h1 : 0 ≤ (if t = s then (1 : ℝ) else 0) / σ := by
          split_ifs <;> positivity
        have := (hF t).2
        nlinarith
    rw [hcr s] at h
    have hp : 0 < β ^ s := pow_pos hβ s
    by_contra hc
    push Not at hc
    have : β ^ s * mxi2 β κ σ ϑ x π s / σ < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp hc) hσ
    linarith
  refine ⟨⟨hF, fun t => ⟨foc35_mult β κ σ ϑ x π t, foc36_mult β κ σ ϑ x π t, hnn t, ?_⟩⟩,
    tendsto_mxi2 hβ hβ1 hκ hσ hϑ hopt⟩
  rcases (rate_nonneg hσ hF t).eq_or_lt with h | h
  · rw [← h, mul_zero]
  · have hneg : Summable (lossTerm β ϑ (fun u => -(hdir β κ σ t u).1)
        fun u => -(hdir β κ σ t u).2) :=
      (hdir_summable β ϑ κ σ t).congr fun u => by simp [lossTerm]
    have hb := foc_dir hβ hϑ hopt hneg h fun ε hε hεi =>
      feasible_pert hF (fun u => by rw [(hdd t u).1]; ring) fun u => by
        have e := (hdd t u).2
        have e2 : -(hdir β κ σ t u).1 - -(hdir β κ σ t (u + 1)).1 -
            -(hdir β κ σ t (u + 1)).2 / σ = (if u = t then (1 : ℝ) else 0) / σ := by
          rw [neg_div]; linarith
        rw [e2]
        have hr := impliedRate_eq hσ.ne' rn x π u
        split_ifs with hu
        · subst hu
          have : ε / σ ≤ ups1 σ rn x π u - x u := by
            rw [div_le_iff₀ hσ]; nlinarith
          have e3 : ε * (1 / σ) = ε / σ := by ring
          rw [e3]; linarith
        · rw [zero_div, mul_zero, add_zero]; linarith [(hF u).2]
    simp only [cross_neg, tsum_neg] at hb
    rw [hcr t] at hb
    have hp : 0 < β ^ t := pow_pos hβ t
    have hle : mxi2 β κ σ ϑ x π t ≤ 0 := by
      by_contra hc
      push Not at hc
      have : 0 < β ^ t * mxi2 β κ σ ϑ x π t / σ := by positivity
      linarith
    rw [le_antisymm hle (hnn t), zero_mul]

/-! ## At the commitment optimum the zero bound binds throughout the shock -/

/-- Cochrane (2023), §20.2.4, pp. 478–479, and Galí (2015), §5.4.2, pp. 148–152: **at the
commitment optimum the interest rate is zero at every date of the shock**, `i_t = 0` for all
`t ≤ t_Z`, and the zero-bound multiplier is strictly positive there (any `β ∈ (0,1)`,
`κ, σ, ϑ > 0`, `η > 0`, `ρ ≥ 0`). This is the step Galí's algorithm assumes (`t_C ≥ t_Z`). -/
theorem optimal_trap_binds {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) (t : ℕ) (ht : t ≤ tZ) :
    impliedRate σ (natRate ρ η tZ) x π t = 0 ∧ 0 < mxi2 β κ σ ϑ x π t := by
  obtain ⟨⟨hF, hK⟩, hlim⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  have hpos := trap_mult_pos hβ hβ1 hκ hσ hϑ hρ hη hF hopt.2.1 (fun t => (hK t).1)
    (fun t => (hK t).2.1) (fun t => (hK t).2.2.1) (fun t => (hK t).2.2.2) hlim t ht
  exact ⟨(mul_eq_zero.mp (hK t).2.2.2).resolve_left hpos.ne', hpos⟩

/-- Galí (2015), eq. (48), p. 151; Cochrane (2023), p. 479: hence the optimum obeys the zero-rate
recursion (48) on the whole shock interval (the hypothesis `h48` of Galí's algorithm). -/
theorem optimal_h48 {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) (t : ℕ) (ht : t ≤ tZ) :
    (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)) := by
  refine backStep_of_rate hσ.ne' (rn := natRate ρ η tZ) (hopt.1 t).1 ?_
  rw [(optimal_trap_binds hβ hβ1 hκ hσ hϑ hρ hη hopt t ht).1, natRate_of_le ht]
  ring

/-- Cochrane (2023), p. 479, Galí (2015), p. 152: **the lift-off date is at least the end of the
shock**: if the optimal rate is positive at `t_C + 1`, then `t_Z ≤ t_C`. -/
theorem liftoff_ge {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ tC : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (hlift : 0 < impliedRate σ (natRate ρ η tZ) x π (tC + 1)) : tZ ≤ tC := by
  by_contra h
  push Not at h
  have := (optimal_trap_binds hβ hβ1 hκ hσ hϑ hρ hη hopt (tC + 1) (by omega)).1
  linarith

/-- Galí (2015), pp. 149–152; Cochrane (2023), p. 479: the same in terms of multipliers: if
`ξ₁, ξ₂` solve (35)–(36) on `[0, t_C + 1]` along the optimum and `ξ₂,t_C+1 = 0` (Galí's lift-off
condition), then `t_Z ≤ t_C`. -/
theorem liftoff_ge_mult {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (hξ2 : ξ2 (tC + 1) = 0) : tZ ≤ tC := by
  by_contra h
  push Not at h
  have e := (mult_unique h50 (tC + 1) le_rfl).2
  have := (optimal_trap_binds hβ hβ1 hκ hσ hϑ hρ hη hopt (tC + 1) (by omega)).2
  rw [← e, hξ2] at this
  exact lt_irrefl _ this

/-- Cochrane (2023), p. 479, Galí (2015), p. 152: equivalently, **every date with a positive
optimal interest rate lies after the shock**: `0 < i_t ⇒ t_Z < t`. -/
theorem liftoff_after_shock {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) (t : ℕ)
    (ht : 0 < impliedRate σ (natRate ρ η tZ) x π t) : tZ < t := by
  by_contra h
  push Not at h
  have := (optimal_trap_binds hβ hβ1 hκ hσ hϑ hρ hη hopt t h).1
  linarith

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), §5.4.2: **commitment inflation never exceeds
the depth of the shock**: at the optimum `π_t ≤ η` at every date (admissible parameters), a discrete
maximum principle for the KKT system (`pi_le_bound`). -/
theorem optimal_pi_le {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) (n : ℕ) : π n ≤ η := by
  obtain ⟨⟨hF, hK⟩, -⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  set ξ2 := mxi2 β κ σ ϑ x π
  have hmult : ∀ t, κ * lam κ ϑ x π t =
      (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β :=
    fun t => lam_mult hκ.ne' (hK (t + 1)).1 (hK t).2.1 (hK (t + 1)).2.1
  have hd : ∀ t, gap σ x π t ≤ η ∨ lam κ ϑ x π t ≤ 0 := by
    intro t
    rcases (hK t).2.2.1.eq_or_lt with h | h
    · right
      have hl : 0 ≤ lag ξ2 t := by
        cases t with
        | zero => simp
        | succ n => simpa using (hK n).2.2.1
      have hk : κ * lam κ ϑ x π t ≤ 0 := by
        rw [hmult t, ← h]
        have := div_nonneg hl hβ.le
        have := (hK (t + 1)).2.2.1
        linarith
      by_contra hc
      push Not at hc
      linarith [mul_pos hκ hc]
    · left
      have hr := (mul_eq_zero.mp (hK t).2.2.2).resolve_left h.ne'
      rw [impliedRate_eq_gap] at hr
      unfold natRate at hr
      split_ifs at hr <;> linarith
  have hI : lamI κ ϑ x π ≤ 0 := by
    have := lamI_mult hκ.ne' (hK 0).1 (hK 0).2.1
    by_contra hc
    push Not at hc
    linarith [mul_pos hκ hc, (hK 0).2.2.1]
  exact pi_le_bound hβ hβ1 hκ hσ hϑ hη (fun t => (hF t).1) hd hI
    (tendsto_pi_sq hβ hϑ hopt.2.1) n

/-! ## Hypothesis-free versions of the commitment theorems -/

/-- Cochrane (2023), §20.2.4, pp. 478–479, and Galí (2015), §5.4.2: `comm_gt_disc` without the
assumptions `t_Z ≤ t_C` and (48): for the commitment optimum, with (35)–(36) on `[0, t_C + 1]`,
(49), (46), `ξ₂,t_C+1 = 0`, the closed form after lift-off, `ξ₂,t_C ≥ 0` and `ξ₁,t_C+1 > 0`,
output and inflation exceed discretion at every date. -/
theorem comm_gt_disc_opt {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k)
    (hsign : 0 ≤ ξ2 tC) (hξ : 0 < ξ1 (tC + 1)) (t : ℕ) :
    discX β κ σ η tZ t < x t ∧ discPi β κ σ η tZ t < π t :=
  comm_gt_disc hβ hβ1 hκ hσ hϑ hρ
    (liftoff_ge_mult hβ hβ1 hκ hσ hϑ hρ.le hη hopt h50 hξ2)
    (optimal_h48 hβ hβ1 hκ hσ hϑ hρ.le hη hopt) h49 (h50 (tC + 1) le_rfl).2 h46 hξ2 hpost
    hsign hξ t

/-- Cochrane (2023), §20.2.4, p. 479, and Galí (2015), p. 152: `comm_loss_lt` without the
assumptions `t_Z ≤ t_C` and (48): discretion has strictly larger loss than the optimum. -/
theorem comm_loss_lt_opt {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k)
    (hsign : 0 ≤ ξ2 tC) (hξ : 0 < ξ1 (tC + 1)) :
    loss β ϑ x π < loss β ϑ (discX β κ σ η tZ) (discPi β κ σ η tZ) :=
  comm_loss_lt hβ hβ1 hκ hσ hϑ hρ
    (liftoff_ge_mult hβ hβ1 hκ hσ hϑ hρ.le hη hopt h50 hξ2)
    (optimal_h48 hβ hβ1 hκ hσ hϑ hρ.le hη hopt) h49 (h50 (tC + 1) le_rfl).2 h46 hξ2 hpost
    hsign hξ hopt

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.glide_path`): `comm_promise` without the
assumptions `t_Z ≤ t_C` and (48): the optimum's date-0 inflation equals that of exactly one
Werning-family member, whose promise `c` is strictly positive. -/
theorem comm_promise_opt {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k)
    (hsign : 0 ≤ ξ2 tC) (hξ : 0 < ξ1 (tC + 1)) :
    (∃! c, (wState β κ σ η tZ c 0).2 = π 0) ∧
      ∀ c, (wState β κ σ η tZ c 0).2 = π 0 → 0 < c :=
  comm_promise hβ hβ1 hκ hσ hϑ hρ
    (liftoff_ge_mult hβ hβ1 hκ hσ hϑ hρ.le hη hopt h50 hξ2)
    (optimal_h48 hβ hβ1 hκ hσ hϑ hρ.le hη hopt) h49 (h50 (tC + 1) le_rfl).2 h46 hξ2 hpost
    hsign hξ

/-- Cochrane (2023), §20.2.4, p. 479: `comm_gt_disc_of_state` without the assumptions
`t_Z ≤ t_C` and (48): for the optimum with lift-off at `t_C + 1` (positive rate there), (49), and
a weakly positive nonzero lift-off state, output and inflation exceed discretion on `[0, t_C]`. -/
theorem comm_gt_disc_of_state_opt {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ tC : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (hlift : 0 < impliedRate σ (natRate ρ η tZ) x π (tC + 1))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (hx : 0 ≤ x (tC + 1)) (hp : 0 ≤ π (tC + 1)) (hs : 0 < x (tC + 1) ∨ 0 < π (tC + 1))
    (t : ℕ) (ht : t ≤ tC) : discX β κ σ η tZ t < x t ∧ discPi β κ σ η tZ t < π t :=
  comm_gt_disc_of_state hβ hκ hσ hρ (liftoff_ge hβ hβ1 hκ hσ hϑ hρ.le hη hopt hlift)
    (optimal_h48 hβ hβ1 hκ hσ hϑ hρ.le hη hopt) h49 hx hp hs t ht

/-- Galí (2015), p. 152, **verification theorem for an arbitrary guess `t_C`** (no `t_Z ≤ t_C`):
if the candidate keeps the rate at zero on `[0, t_C]` (whatever the natural rate there),
satisfies (35)–(36) on `[0, t_C + 1]`, (46), `ξ₂,t_C+1 = 0`, the closed form (42)–(43) after
lift-off, `ξ₂ ≥ 0` on `[0, t_C]` and `i ≥ 0` at every date after `t_C`, then it is the unique
optimum, satisfies the KKT system, and necessarily `t_Z ≤ t_C`: the guess in Galí's algorithm
is without loss of generality. -/
theorem algorithm_verification_gen {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hzero : ∀ t, t ≤ tC →
      (x t, π t) = backStep β κ σ (-natRate ρ η tZ t) (x (t + 1), π (t + 1)))
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k ∧
      ξ1 (tC + k + 2) = postXi β κ ϑ (ξ1 (tC + 1)) (k + 1) ∧ ξ2 (tC + k + 2) = 0)
    (hsign : ∀ t, t ≤ tC → 0 ≤ ξ2 t)
    (hrate : ∀ k, 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 1 + k)) :
    tZ ≤ tC ∧ KKT β κ σ ϑ (natRate ρ η tZ) x π ξ1 ξ2 ∧
      Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      (∀ y q, Feasible β κ σ (natRate ρ η tZ) y q → Summable (lossTerm β ϑ y q) →
        loss β ϑ y q ≤ loss β ϑ x π → y = x ∧ q = π) := by
  have hδ0 := del_pos (κ := κ) hβ hϑ
  have hδ1 := (del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  set ξ := ξ1 (tC + 1) with hξ
  set rn := natRate ρ η tZ with hrn
  have hξ1post : ∀ k, ξ1 (tC + 1 + k) = postXi β κ ϑ ξ k := by
    intro k
    rcases k with _ | k
    · simp [postXi, hξ]
    · rw [show tC + 1 + (k + 1) = tC + k + 2 by omega]; exact (hpost k).2.2.1
  have hξ2post : ∀ k, ξ2 (tC + 1 + k) = 0 := by
    intro k
    rcases k with _ | k
    · simpa using hξ2
    · rw [show tC + 1 + (k + 1) = tC + k + 2 by omega]; exact (hpost k).2.2.2
  have hbind : ∀ t, t ≤ tC → NKPC β κ x π t ∧ impliedRate σ rn x π t = 0 :=
    fun t ht => backStep_nkpc_rate hσ.ne' (hzero t ht) (by rw [hrn, neg_neg])
  have hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k := fun k => (hpost k).1
  have hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k := fun k => (hpost k).2.1
  have hrt : ∀ t, 0 ≤ impliedRate σ rn x π t := by
    intro t
    rcases le_or_gt t tC with ht | ht
    · rw [(hbind t ht).2]
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + 1 + k := ⟨t - tC - 1, by omega⟩
      exact hrate k
  have hnkpc : ∀ t, NKPC β κ x π t := by
    intro t
    rcases le_or_gt t tC with ht | ht
    · exact (hbind t ht).1
    · rcases Nat.eq_or_lt_of_le ht with h | h
      · rw [← h]; exact h46
      · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
        unfold NKPC
        rw [show tC + k + 2 + 1 = tC + (k + 1) + 2 by omega, hx, hπ, hπ]
        exact post_eq39 hβ hβ1 hϑ ξ k
  have hK : KKT β κ σ ϑ rn x π ξ1 ξ2 := by
    refine ⟨feasible_of_rate hσ fun t => ⟨hnkpc t, hrt t⟩, fun t => ?_⟩
    rcases le_or_gt t (tC + 1) with ht | ht
    · refine ⟨(h50 t ht).1, (h50 t ht).2, ?_, ?_⟩
      · rcases le_or_gt t tC with h | h
        · exact hsign t h
        · rw [show t = tC + 1 by omega, hξ2]
      · rcases le_or_gt t tC with h | h
        · rw [(hbind t h).2, mul_zero]
        · rw [show t = tC + 1 by omega, hξ2, zero_mul]
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
      have e : tC + k + 2 = (tC + 1 + k) + 1 := by omega
      have l1' : lag ξ1 (tC + k + 2) = postXi β κ ϑ ξ k := by rw [e, lag_succ, hξ1post]
      have l2' : lag ξ2 (tC + k + 2) = 0 := by rw [e, lag_succ, hξ2post]
      have x1 : ξ1 (tC + k + 2) = postXi β κ ϑ ξ (k + 1) := (hpost k).2.2.1
      have x2 : ξ2 (tC + k + 2) = 0 := (hpost k).2.2.2
      refine ⟨?_, ?_, by rw [x2], by rw [x2, zero_mul]⟩
      · unfold FOC35
        rw [l1', l2', x1, hπ, zero_div, sub_zero]
        exact post_eq37 β κ ϑ ξ k
      · unfold FOC36
        rw [l2', x1, x2, hx, zero_div, sub_zero, add_zero]
        exact post_eq38 hϑ.ne' ξ k
  have hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C := by
    refine ⟨∑ s ∈ Finset.range (tC + 1), (|ξ1 s| + |ξ2 s|) + |ξ|, fun t => ?_⟩
    have hS : 0 ≤ ∑ s ∈ Finset.range (tC + 1), (|ξ1 s| + |ξ2 s|) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hξ0 := abs_nonneg ξ
    rcases le_or_gt t tC with ht | ht
    · have hle := Finset.single_le_sum (f := fun s => |ξ1 s| + |ξ2 s|)
        (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
      have a1 := abs_nonneg (ξ1 t)
      have a2 := abs_nonneg (ξ2 t)
      constructor <;> linarith
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + 1 + k := ⟨t - tC - 1, by omega⟩
      rw [hξ1post, hξ2post, abs_zero]
      refine ⟨?_, by linarith⟩
      unfold postXi
      rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0.le k)]
      have : del β κ ϑ ^ k * |ξ| ≤ |ξ| :=
        mul_le_of_le_one_left hξ0 (pow_le_one₀ hδ0.le hδ1.le)
      linarith
  have hs : Summable (lossTerm β ϑ x π) := by
    refine (summable_nat_add_iff (tC + 2)).mp ?_
    have e : (fun n => lossTerm β ϑ x π (n + (tC + 2))) = fun n =>
        β ^ (tC + 2) * (((1 - del β κ ϑ) * ξ) ^ 2 +
          ϑ * (κ * del β κ ϑ * ξ / ϑ) ^ 2) *
          (β * del β κ ϑ ^ 2) ^ n := by
      funext n
      rw [lossTerm, show n + (tC + 2) = tC + n + 2 by omega, hx, hπ]
      unfold postX postPi
      ring
    rw [e]
    exact (summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
  have hopt := kkt_optimal hβ hβ1 hσ hϑ hK hb hs
  exact ⟨liftoff_ge_mult hβ hβ1 hκ hσ hϑ hρ hη hopt h50 hξ2, hK, hopt,
    fun y q hy hsy hle => kkt_unique hβ hβ1 hσ hϑ hK hb hs hy hsy hle⟩

/-- Cochrane (2023), §20.2.4, p. 479, and Galí (2015), p. 152: `comm_loss_lt_alg` for an
arbitrary guess `t_C` (no `t_Z ≤ t_C`): under the hypotheses of `algorithm_verification_gen` and
`ξ₁,t_C+1 > 0`, the candidate is the optimum, `t_Z ≤ t_C`, and discretion is strictly worse. -/
theorem comm_loss_lt_alg_gen {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (hzero : ∀ t, t ≤ tC →
      (x t, π t) = backStep β κ σ (-natRate ρ η tZ t) (x (t + 1), π (t + 1)))
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k ∧
      ξ1 (tC + k + 2) = postXi β κ ϑ (ξ1 (tC + 1)) (k + 1) ∧ ξ2 (tC + k + 2) = 0)
    (hsign : ∀ t, t ≤ tC → 0 ≤ ξ2 t)
    (hrate : ∀ k, 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 1 + k))
    (hξ : 0 < ξ1 (tC + 1)) :
    tZ ≤ tC ∧ Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      loss β ϑ x π < loss β ϑ (discX β κ σ η tZ) (discPi β κ σ η tZ) := by
  obtain ⟨htC, -, hopt, -⟩ := algorithm_verification_gen hβ hβ1 hκ hσ hϑ hρ.le hη hzero h50 h46
    hξ2 hpost hsign hrate
  refine ⟨htC, hopt, comm_loss_lt_opt hβ hβ1 hκ hσ hϑ hρ hη hopt h50 (fun t h1 h2 => ?_) h46
    hξ2 (fun k => ⟨(hpost k).1, (hpost k).2.1⟩) (hsign tC le_rfl) hξ⟩
  rw [hzero t h2, natRate_of_lt h1]

end Cochrane.ZeroBound.LiftoffTiming
