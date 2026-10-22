/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.LiftoffStructure

/-!
# A zero post-shock natural rate: exactly when does the rate lift off?

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.4 (pp. 478–480),
compared with Galí (2015), §5.4.2 (pp. 148–152), in the model of `LinksGaliWoodford`
(loss `∑ βᵗ(π_t² + ϑ x_t²)`, `π_t = βπ_{t+1} + κx_t`, `i_t = rⁿ_t + π_{t+1} + σ(x_{t+1} − x_t)
≥ 0`, `rⁿ_t = −η` on `[0, t_Z]` and `ρ` after). Continues `LiftoffStructure`, whose
`rho_zero_structure` shows that with `ρ = 0` the optimum either (a) keeps the rate at zero
forever or (b) lifts off at a finite `t_C ≥ t_Z` with `i > 0` afterwards.

**Classification** (`rho_zero_zero_iff`, `rho_zero_liftoff_iff`, `rho_zero_classification`):
for every `β ∈ (0,1)`, `κ, σ, ϑ, η > 0` and `t_Z`, branch (a) holds iff `ϑ ≤ σκ` and branch (b)
iff `σκ < ϑ`. The depth `η`, the discount factor `β` and the length `t_Z` of the shock play no
role.

* `σκ < ϑ` (`rho_zero_lt_not_zero`): on a zero-rate path the post-shock inflation decays at the
  stable peg root `μ` (`peg_geometric`) from `π_{t_Z+1} > 0` (`zero_rate_pi_pos`), so the
  multiplier recursion is forced by `κ(1 − σκ/ϑ)/(σκ/ϑ) · π_{t+1} > 0`; as `μ` is itself a root
  of the multiplier recursion (resonance) the multipliers either explode or turn negative
  (`forced_mult_contra`).
* `ϑ < σκ` (`rho_zero_gt_no_slack`): after a lift-off, feasibility forces `A > 0`, hence
  `ξ₁,t_B+1 < 0` and deflation with a recession after lift-off; nonnegative rate gaps carry
  `π_t < π_{t+1} < 0` back to date 0 (`back_rise`), so the whole path is nonpositive, which the
  optimal choice along the bounded peg mode forbids (`nonpos_contra`, from `cross_wdir`).
* `σκ = ϑ`: `rho_zero_unit_ratio`.

Further: on branch (a) the optimum is the zero-rate (Werning) path with `π_{t_Z+1} > 0`
decaying at `μ` (`rho_zero_branch_a`); on branch (b) Galí's sign condition `ξ₁,t_B+1 > 0` holds
automatically (`rho_zero_branch_b`). A verification theorem for `ρ = 0` (`verification_zero`)
certifies exact rational optima on both sides: `cert_liftoff_now` (`t_C = t_Z = 0`),
`cert_liftoff_late` (`t_C = 1 > t_Z = 0`) and `cert_zero_forever` (rate zero forever, explicit
multipliers `ξ₂,t = (29 + 5t)/(192·2ᵗ)`).
-/

namespace Cochrane.ZeroBound.LiftoffRhoZero

open Filter Topology
open Cochrane.ZeroBound Cochrane.ZeroBound.LinksGaliWoodford Cochrane.ZeroBound.LiftoffTiming
  Cochrane.ZeroBound.LiftoffStructure

/-! ## Tools -/

/-- Cochrane (2023), §20.2.4, p. 479: with `ρ = 0` every rate gap of a feasible path is
nonnegative, `i_t − rⁿ_t ≥ 0` (since `i_t ≥ 0 ≥ rⁿ_t`). -/
theorem gap_nonneg_zero {β κ σ η : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hF : Feasible β κ σ (natRate 0 η tZ) x π) (t : ℕ) : 0 ≤ gap σ x π t := by
  have h := rate_nonneg hσ hF t
  rw [impliedRate_eq_gap] at h
  have : natRate 0 η tZ t ≤ 0 := by
    unfold natRate
    split_ifs <;> linarith
  linarith

/-- Cochrane (2023), §20.2.4, p. 479: **backward propagation of a rise in negative inflation.**
If the rate gaps are nonnegative before `M`, `π_M < π_{M+1}` and `π_{M+1} ≤ 0`, then
`π_t < π_{t+1} ≤ 0` for every `t ≤ M` (from `gap = comb β (σ/κ) π`). -/
theorem back_rise {β κ σ : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) {x π : ℕ → ℝ}
    (hN : ∀ t, NKPC β κ x π t) {M : ℕ} (hg : ∀ t, t < M → 0 ≤ gap σ x π t)
    (h1 : π M < π (M + 1)) (h2 : π (M + 1) ≤ 0) :
    ∀ t, t ≤ M → π t < π (t + 1) ∧ π (t + 1) ≤ 0 := by
  refine down_ind (P := fun t => π t < π (t + 1) ∧ π (t + 1) ≤ 0) ⟨h1, h2⟩ ?_
  intro t ht hP
  obtain ⟨ha, hb⟩ := hP
  have hc := hg t ht
  rw [gap_comb hκ.ne' (hN t) (hN (t + 1))] at hc
  unfold comb at hc
  rw [show t + 1 + 1 = t + 2 by omega] at ha hb
  have hsk : 0 < σ / κ := by positivity
  refine ⟨?_, by linarith⟩
  by_contra hcon
  push Not at hcon
  have e1 : σ / κ * (π (t + 1) - π t) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hsk.le (by linarith)
  have e2 : σ / κ * (β * (π (t + 1) - π (t + 2))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hsk.le (mul_nonpos_of_nonneg_of_nonpos hβ (by linarith))
  nlinarith

/-- Galí (2015), eq. (29), p. 145; Cochrane (2023), p. 479: if `π_t < π_{t+1} ≤ 0` then the
output gap is negative, `x_t = (π_t − βπ_{t+1})/κ < 0`. -/
theorem x_neg_of_rise {β κ : ℝ} (hβ1 : β ≤ 1) (hκ : 0 < κ) {x π : ℕ → ℝ} {t : ℕ}
    (hN : NKPC β κ x π t) (h1 : π t < π (t + 1)) (h2 : π (t + 1) ≤ 0) : x t < 0 := by
  unfold NKPC at hN
  have : (1 - β) * π (t + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h2
  by_contra hc
  push Not at hc
  nlinarith

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), p. 149: **an optimum is never nonpositive
throughout.** At any commitment optimum (any natural-rate path) the loss derivative along the
bounded peg mode `wdir`, which leaves every rate unchanged, vanishes (`cross_wdir`); its weights
`β^t λ₁⁻ᵗ (1, ϑ v_x)` are positive, so `π, x ≤ 0` at every date with `π₀ < 0` is impossible. -/
theorem nonpos_contra {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) {rn x π : ℕ → ℝ} (hopt : Optimal β κ σ ϑ rn x π)
    (hπ : ∀ t, π t ≤ 0) (hx : ∀ t, x t ≤ 0) (h0 : π 0 < 0) : False := by
  have hc := cross_wdir hβ hβ1 hκ hσ hϑ hopt
  have hs := summable_cross hβ.le hϑ hopt.2.1 (wdir_summable (ϑ := ϑ) hβ hβ1 hσ hκ)
  have hl := one_lt_l1 hβ hσ hκ
  have hv : 0 < vx β σ κ := by
    have := (l2_bounds hβ hσ hκ).2
    unfold vx
    exact div_pos (by linarith) hκ
  have hterm : ∀ t, 0 ≤ -cross β ϑ x π (fun t => (wdir β κ σ t).1)
      (fun t => (wdir β κ σ t).2) t := by
    intro t
    simp only [cross, wdir]
    have hq : 0 < (l1 β σ κ)⁻¹ ^ t := pow_pos (inv_pos.mpr (by linarith)) t
    have hp : 0 < β ^ t := pow_pos hβ t
    have a1 : 0 ≤ -π t * (l1 β σ κ)⁻¹ ^ t := mul_nonneg (by linarith [hπ t]) hq.le
    have a2 : 0 ≤ ϑ * (-x t) * ((l1 β σ κ)⁻¹ ^ t * vx β σ κ) :=
      mul_nonneg (mul_nonneg hϑ.le (by linarith [hx t])) (mul_nonneg hq.le hv.le)
    have : 0 ≤ β ^ t * (-π t * (l1 β σ κ)⁻¹ ^ t + ϑ * (-x t) * ((l1 β σ κ)⁻¹ ^ t *
        vx β σ κ)) := mul_nonneg hp.le (by linarith)
    linarith
  have h0' : 0 < -cross β ϑ x π (fun t => (wdir β κ σ t).1) (fun t => (wdir β κ σ t).2) 0 := by
    simp only [cross, wdir, pow_zero, one_mul]
    have : ϑ * x 0 * vx β σ κ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hϑ.le (hx 0)) hv.le
    linarith
  have := hs.neg.tsum_pos hterm 0 h0'
  rw [tsum_neg, hc] at this
  simp at this

/-- Cochrane (2023), §20.2.4, p. 479 (transversality of the zero-bound multipliers): **a
resonantly forced multiplier recursion has no admissible solution.** If `μ ∈ (0, 1]` is a root
of `z² − cc z + 1/β` (`cc = μ + 1/(βμ)`), `F > 0`, and from `n₀` on
`ξ_{n+2} − cc ξ_{n+1} + ξ_n/β = F μⁿ`, then `ξ ≥ 0` and `βⁿ ξ_n → 0` are incompatible: with
`u_n = ξ_{n+1} − μξ_n`, `u_{n+1} = u_n/(βμ) + Fμⁿ`; a positive `u` grows like `(βμ)⁻ⁿ`
(violating `βⁿξ_n → 0`), and `u ≤ 0` forces `ξ_n/μⁿ` to fall linearly below zero. -/
theorem forced_mult_contra {β μ cc F : ℝ} (hβ : 0 < β) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hcc : cc = μ + 1 / (β * μ)) (hF : 0 < F) {ξ : ℕ → ℝ} (hpos : ∀ n, 0 ≤ ξ n) {n0 : ℕ}
    (hrec : ∀ n, n0 ≤ n → ξ (n + 2) - cc * ξ (n + 1) + ξ n / β = F * μ ^ n)
    (hlim : Tendsto (fun n => β ^ n * ξ n) atTop (𝓝 0)) : False := by
  have hz0 : 0 < 1 / (β * μ) := by positivity
  have hzμ : 1 / (β * μ) * μ = 1 / β := by field_simp
  have hstep : ∀ n, n0 ≤ n → ξ (n + 2) - μ * ξ (n + 1) =
      1 / (β * μ) * (ξ (n + 1) - μ * ξ n) + F * μ ^ n := by
    intro n hn
    have h := hrec n hn
    rw [hcc] at h
    linear_combination h + ξ n * hzμ
  by_cases hA : ∃ m, n0 ≤ m ∧ 0 < ξ (m + 1) - μ * ξ m
  · obtain ⟨m, hm, hum⟩ := hA
    set u0 := ξ (m + 1) - μ * ξ m with hu0
    have hgrow : ∀ j, (1 / (β * μ)) ^ j * u0 ≤ ξ (m + j + 1) - μ * ξ (m + j) := by
      intro j
      induction j with
      | zero => simp [hu0]
      | succ j ih =>
        have h := hstep (m + j) (by omega)
        rw [show m + (j + 1) + 1 = m + j + 2 by omega, show m + (j + 1) = m + j + 1 by omega, h,
          pow_succ]
        have hF' : 0 ≤ F * μ ^ (m + j) := mul_nonneg hF.le (pow_nonneg hμ0.le _)
        have := mul_le_mul_of_nonneg_left ih hz0.le
        nlinarith
    have hc0 : 0 < β ^ (m + 1) * u0 := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 hlim).2 _ hc0)
    have hlt := hN (m + N + 1) (by omega)
    have hg := hgrow N
    have hxi : ξ (m + N + 1) - μ * ξ (m + N) ≤ ξ (m + N + 1) := by
      have := mul_nonneg hμ0.le (hpos (m + N))
      linarith
    have hpow1 : 1 ≤ (1 / μ) ^ N := one_le_pow₀ (by rw [le_div_iff₀ hμ0]; linarith)
    have e : β ^ (m + N + 1) * ((1 / (β * μ)) ^ N * u0) = β ^ (m + 1) * u0 * (1 / μ) ^ N := by
      rw [show m + N + 1 = (m + 1) + N by omega, pow_add, div_pow, div_pow, mul_pow, one_pow]
      field_simp
    have hp : 0 ≤ β ^ (m + N + 1) := pow_nonneg hβ.le _
    have k1 : β ^ (m + N + 1) * ((1 / (β * μ)) ^ N * u0) ≤ β ^ (m + N + 1) * ξ (m + N + 1) :=
      mul_le_mul_of_nonneg_left (hg.trans hxi) hp
    have k2 : β ^ (m + 1) * u0 ≤ β ^ (m + 1) * u0 * (1 / μ) ^ N := by
      have := mul_le_mul_of_nonneg_left hpow1 hc0.le
      linarith
    linarith
  · push Not at hA
    have hdec : ∀ m, n0 ≤ m → ξ (m + 1) ≤ μ * ξ m - F * β * μ ^ (m + 1) := by
      intro m hm
      have h1 := hA (m + 1) (by omega)
      rw [show m + 1 + 1 = m + 2 by omega, hstep m hm] at h1
      have hbm : 0 < β * μ := by positivity
      have e : β * μ * (1 / (β * μ)) = 1 := by field_simp
      have h2 := mul_le_mul_of_nonneg_left (show 1 / (β * μ) * (ξ (m + 1) - μ * ξ m) ≤
        -(F * μ ^ m) by linarith) hbm.le
      rw [← mul_assoc, e, one_mul] at h2
      rw [pow_succ]
      nlinarith
    have hind : ∀ j : ℕ, ξ (n0 + j) ≤ μ ^ j * (ξ n0 - j * (F * β * μ ^ n0)) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have h := hdec (n0 + j) (by omega)
        rw [show n0 + (j + 1) = n0 + j + 1 by omega]
        have := mul_le_mul_of_nonneg_left ih hμ0.le
        have e : F * β * μ ^ (n0 + j + 1) = μ ^ (j + 1) * (F * β * μ ^ n0) := by ring
        have e2 : μ * (μ ^ j * (ξ n0 - j * (F * β * μ ^ n0))) - μ ^ (j + 1) * (F * β * μ ^ n0) =
            μ ^ (j + 1) * (ξ n0 - ((j : ℝ) + 1) * (F * β * μ ^ n0)) := by ring
        push_cast
        linarith
    have hd : 0 < F * β * μ ^ n0 := by positivity
    obtain ⟨j, hj⟩ := exists_nat_gt (ξ n0 / (F * β * μ ^ n0))
    have h1 := hind j
    have h2 : ξ n0 - j * (F * β * μ ^ n0) < 0 := by
      rw [div_lt_iff₀ hd] at hj
      linarith
    have : μ ^ j * (ξ n0 - j * (F * β * μ ^ n0)) < 0 :=
      mul_neg_of_pos_of_neg (pow_pos hμ0 j) h2
    linarith [hpos (n0 + j)]

/-! ## Zero-rate paths -/

/-- Cochrane (2023), §20.1, p. 467 and §20.2.2, p. 475 (`ρ = 0`): **after the shock a zero rate
path decays at the stable peg root** `μ = δ(β, κ, κσ)` (the root in `(0,1)` of
`βμ² − (1 + β + κ/σ)μ + 1 = 0`): if the optimum has `i_t = 0` for all `t > t_Z`, then
`π_{n+1} = μ π_n` for `n ≥ t_Z + 1` (finite loss excludes the other root, `two_root`). -/
theorem peg_geometric {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) {tZ : ℕ} {x π : ℕ → ℝ} (hopt : Optimal β κ σ ϑ (natRate 0 η tZ) x π)
    (h0 : ∀ t, tZ < t → impliedRate σ (natRate 0 η tZ) x π t = 0) :
    ∀ n, tZ + 1 ≤ n → π (n + 1) = del β κ (κ * σ) * π n := by
  have hN : ∀ t, NKPC β κ x π t := fun t => (hopt.1 t).1
  have hS := tendsto_pi_sq hβ hϑ hopt.2.1
  have hab : σ / κ * (κ / σ) = 1 := by field_simp
  have hrec : ∀ n, tZ + 1 ≤ n → β * π (n + 2) - (1 + β + κ / σ) * π (n + 1) + π n = 0 := by
    intro n hn
    have h := h0 n (by omega)
    rw [impliedRate_eq_gap, natRate_of_lt (by omega), zero_add,
      gap_comb hκ.ne' (hN n) (hN (n + 1))] at h
    unfold comb at h
    linear_combination (-(κ / σ)) * h +
      ((π (n + 1) - π n) + β * (π (n + 1) - π (n + 2))) * hab
  have hks : 0 < κ * σ := by positivity
  have hq : β * del β κ (κ * σ) ^ 2 - (1 + β + κ / σ) * del β κ (κ * σ) + 1 = 0 := by
    have := del_root (κ := κ) hβ hβ1 hks
    rw [show κ ^ 2 / (κ * σ) = κ / σ by field_simp] at this
    exact this
  exact two_root hβ hβ1 (del_pos hβ hks) ((del_lt_one_iff hβ hβ1 hks).mpr hκ.ne') hq hrec hS

/-- Cochrane (2023), §20.2.2, p. 475, §20.2.4, p. 479 (`ρ = 0`, any `σκ/ϑ`): **if the optimal
rate is zero at every date, the promised post-shock inflation is positive**, `π_{t_Z+1} > 0`.
Otherwise inflation would be `≤ 0` after the shock, rise strictly through the shock
(`back_rise`), and the whole path would be nonpositive (`nonpos_contra`). -/
theorem zero_rate_pi_pos {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate 0 η tZ) x π)
    (h0 : ∀ t, impliedRate σ (natRate 0 η tZ) x π t = 0) : 0 < π (tZ + 1) := by
  by_contra hc
  push Not at hc
  have hN : ∀ t, NKPC β κ x π t := fun t => (hopt.1 t).1
  have hgeo := peg_geometric hβ hβ1 hκ hσ hϑ hopt fun t _ => h0 t
  have hks : 0 < κ * σ := by positivity
  set μ := del β κ (κ * σ) with hμ
  have hμ0 : 0 < μ := del_pos hβ hks
  have hμ1 : μ < 1 := (del_lt_one_iff hβ hβ1 hks).mpr hκ.ne'
  have hpow : ∀ j, π (tZ + 1 + j) = μ ^ j * π (tZ + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show tZ + 1 + (j + 1) = (tZ + 1 + j) + 1 by omega, hgeo _ (by omega), ih, pow_succ]
      ring
  have hpost : ∀ t, tZ + 1 ≤ t → π t ≤ 0 ∧ x t ≤ 0 := by
    intro t ht
    obtain ⟨j, rfl⟩ : ∃ j, t = tZ + 1 + j := ⟨t - (tZ + 1), by omega⟩
    have hp : π (tZ + 1 + j) ≤ 0 := by
      rw [hpow]
      exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hμ0.le _) hc
    refine ⟨hp, ?_⟩
    rw [x_of_nkpc hκ.ne' (hN _), hgeo _ (by omega)]
    have hb : 0 < 1 - β * μ := by nlinarith
    have : π (tZ + 1 + j) - β * (μ * π (tZ + 1 + j)) = (1 - β * μ) * π (tZ + 1 + j) := by ring
    rw [this]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hb.le hp) hκ.le
  have hstart : π tZ < π (tZ + 1) := by
    have h := h0 tZ
    rw [impliedRate_eq_gap, natRate_of_le le_rfl, gap_comb hκ.ne' (hN tZ) (hN (tZ + 1))] at h
    unfold comb at h
    have e2 : π (tZ + 2) = μ * π (tZ + 1) := hgeo (tZ + 1) le_rfl
    rw [e2] at h
    have hsk : 0 < σ / κ := by positivity
    have k1 : σ / κ * (β * ((1 - μ) * π (tZ + 1))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hsk.le (mul_nonpos_of_nonneg_of_nonpos hβ.le
        (mul_nonpos_of_nonneg_of_nonpos (by linarith) hc))
    by_contra hcon
    push Not at hcon
    have k2 : σ / κ * (π (tZ + 1) - π tZ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hsk.le (by linarith)
    nlinarith
  have hrise := back_rise hβ.le hκ hσ hN (M := tZ)
    (fun t _ => gap_nonneg_zero hσ hη.le hopt.1 t) hstart hc
  refine nonpos_contra hβ hβ1 hκ hσ hϑ hopt (fun t => ?_) (fun t => ?_) ?_
  · rcases le_or_gt t tZ with h | h
    · linarith [(hrise t h).1, (hrise t h).2]
    · exact (hpost t h).1
  · rcases le_or_gt t tZ with h | h
    · exact (x_neg_of_rise hβ1.le hκ (hN t) (hrise t h).1 (hrise t h).2).le
    · exact (hpost t h).2
  · linarith [(hrise 0 (Nat.zero_le _)).1, (hrise 0 (Nat.zero_le _)).2]

/-! ## The two directions -/

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), §5.4.2 (`ρ = 0`): **if `σκ < ϑ` the optimal
rate is not zero at every date.** On a zero-rate optimum `π_{t_Z+1+j} = μʲ π_{t_Z+1}` with
`π_{t_Z+1} > 0`, and (35)–(36) give, for the multipliers `ξ_n = ξ₂,t_Z+n`,
`ξ_{n+2} − cc ξ_{n+1} + ξ_n/β = −κ·lam = κ(1 − r)/r · μ^{n+1} π_{t_Z+1}` (`r = σκ/ϑ < 1`), a
resonant positive forcing (`μ` is a root of the multiplier recursion), so
`forced_mult_contra` contradicts `ξ₂ ≥ 0` and `β^t ξ₂,t → 0` (`kkt_necessary`). -/
theorem rho_zero_lt_not_zero {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hη : 0 < η) (hr : σ * κ < ϑ) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate 0 η tZ) x π) :
    ¬ ∀ t, impliedRate σ (natRate 0 η tZ) x π t = 0 := by
  intro h0
  obtain ⟨⟨hF, hK⟩, hlim⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  have hc := zero_rate_pi_pos hβ hβ1 hκ hσ hϑ hη hopt h0
  have hgeo := peg_geometric hβ hβ1 hκ hσ hϑ hopt fun t _ => h0 t
  have hks : 0 < κ * σ := by positivity
  set μ := del β κ (κ * σ) with hμ
  have hμ0 : 0 < μ := del_pos hβ hks
  have hμ1 : μ < 1 := (del_lt_one_iff hβ hβ1 hks).mpr hκ.ne'
  have hq : β * μ ^ 2 - (1 + β + κ / σ) * μ + 1 = 0 := by
    have := del_root (κ := κ) hβ hβ1 hks
    rw [show κ ^ 2 / (κ * σ) = κ / σ by field_simp] at this
    exact this
  have hpow : ∀ j, π (tZ + 1 + j) = μ ^ j * π (tZ + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show tZ + 1 + (j + 1) = (tZ + 1 + j) + 1 by omega, hgeo _ (by omega), ih, pow_succ]
      ring
  set ξ2 := mxi2 β κ σ ϑ x π with hξ2
  set r := σ * κ / ϑ with hrdef
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hrdef, div_lt_one hϑ]; exact hr
  set cc := 1 + 1 / β + κ / (β * σ) with hccdef
  have hcc : cc = μ + 1 / (β * μ) := by
    have e : μ + 1 / (β * μ) - cc = (β * μ ^ 2 - (1 + β + κ / σ) * μ + 1) / (β * μ) := by
      rw [hccdef]
      field_simp
      ring
    rw [hq, zero_div] at e
    linarith
  clear_value r cc
  set F := κ * (1 - r) / r * μ * π (tZ + 1) with hFdef
  have hF : 0 < F := by
    have : 0 < 1 - r := by linarith
    positivity
  have hmult : ∀ t, κ * lam κ ϑ x π t = cc * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β :=
    fun t => by rw [hccdef]; exact lam_mult hκ.ne' (hK (t + 1)).1 (hK t).2.1 (hK (t + 1)).2.1
  have hrec : ∀ n, 0 ≤ n → ξ2 (tZ + n + 2) - cc * ξ2 (tZ + n + 1) + ξ2 (tZ + n) / β =
      F * μ ^ n := by
    intro n _
    have hm := hmult (tZ + n + 1)
    simp only [lag_succ] at hm
    have hg : gap σ x π (tZ + n + 1) = 0 := by
      have h := h0 (tZ + n + 1)
      rw [impliedRate_eq_gap, natRate_of_lt (by omega), zero_add] at h
      exact h
    have hgl := gap_lam (σ := σ) hκ.ne' hϑ.ne' x π (tZ + n + 1)
    rw [hg, ← hrdef] at hgl
    have hp : π (tZ + n + 1 + 1) = μ ^ (n + 1) * π (tZ + 1) := by
      rw [show tZ + n + 1 + 1 = tZ + 1 + (n + 1) by omega, hpow]
    rw [hp] at hgl
    have hlam : lam κ ϑ x π (tZ + n + 1) = (r - 1) / r * (μ ^ (n + 1) * π (tZ + 1)) := by
      field_simp
      linarith
    rw [hlam, show tZ + n + 1 + 1 = tZ + n + 2 by omega] at hm
    rw [hFdef]
    linear_combination hm
  have hlim' : Tendsto (fun n => β ^ n * ξ2 (tZ + n)) atTop (𝓝 0) := by
    have h1 := (hlim.comp (tendsto_add_atTop_nat tZ)).const_mul (1 / β ^ tZ)
    rw [mul_zero] at h1
    refine h1.congr fun n => ?_
    simp only [Function.comp, pow_add]
    rw [show n + tZ = tZ + n by omega]
    field_simp
  exact forced_mult_contra hβ hμ0 hμ1.le hcc hF (fun n => (hK (tZ + n)).2.2.1) hrec hlim'

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), p. 152 (`ρ = 0`): **if `ϑ < σκ` no date after
the shock has a zero multiplier**, so the rate never lifts off. After a lift-off at `t_B + 1`,
`i_{t_B+1} ≥ 0` forces `A = (1 − δ)(1 − σκ/ϑ)ξ₁,t_B+1 > 0` (`liftoff_rates`), i.e.
`ξ₁,t_B+1 < 0`: deflation and a recession after lift-off (`post_form`). The nonnegative rate gap
at `t_B + 1` gives `π_{t_B+1} < π_{t_B+2} < 0`, `back_rise` carries the rise back to date 0,
and the resulting nonpositive path contradicts `nonpos_contra`. -/
theorem rho_zero_gt_no_slack {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hη : 0 < η) (hr : ϑ < σ * κ) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate 0 η tZ) x π) :
    ¬ ∃ s, tZ < s ∧ mxi2 β κ σ ϑ x π s = 0 := by
  intro hex
  have hF := hopt.1
  have hN : ∀ t, NKPC β κ x π t := fun t => (hF t).1
  obtain ⟨tB, -, -, hz, -, h1, -⟩ := liftoff_rates hβ hβ1 hκ hσ hϑ le_rfl hη hopt hex
  have hpost := post_form hβ hβ1 hκ hϑ hopt (tB := tB) fun t ht => hz t (by omega)
  set ξ := mxi1 β κ σ ϑ x π (tB + 1) with hξ
  set δ := del β κ ϑ with hδ
  have hδ0 : 0 < δ := del_pos hβ hϑ
  have hδ1 : δ < 1 := (del_lt_one_iff hβ hβ1 hϑ).mpr hκ.ne'
  have hA : 0 < (1 - δ) * (1 - σ * κ / ϑ) * ξ := by
    have := rate_nonneg hσ hF (tB + 1)
    linarith
  have hr1 : 1 - σ * κ / ϑ < 0 := by
    have : 1 < σ * κ / ϑ := by rw [one_lt_div hϑ]; exact hr
    linarith
  have hξn : ξ < 0 := by
    by_contra hc
    push Not at hc
    have : (1 - δ) * (1 - σ * κ / ϑ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hr1.le
    nlinarith
  have hπp : ∀ k, π (tB + k + 2) < 0 := by
    intro k
    rw [(hpost k).2.1]
    unfold postPi
    have : 0 < (1 - δ) * δ ^ k := mul_pos (by linarith) (pow_pos hδ0 k)
    exact mul_neg_of_pos_of_neg this hξn
  have hxp : ∀ k, x (tB + k + 2) < 0 := by
    intro k
    rw [(hpost k).1]
    unfold postX
    have : κ * δ ^ (k + 1) * ξ < 0 := mul_neg_of_pos_of_neg (by positivity) hξn
    exact div_neg_of_neg_of_pos this hϑ
  have e1 : π (tB + 1 + 1) = (1 - δ) * ξ := by
    rw [show tB + 1 + 1 = tB + 0 + 2 by omega, (hpost 0).2.1]
    unfold postPi
    ring
  have e2 : π (tB + 1 + 2) = (1 - δ) * δ * ξ := by
    rw [(hpost 1).2.1]
    unfold postPi
    ring
  have hk3 : (1 - δ) * ξ < 0 := mul_neg_of_pos_of_neg (by linarith) hξn
  have hstart : π (tB + 1) < π (tB + 1 + 1) := by
    have hg := gap_nonneg_zero hσ hη.le hF (tB + 1)
    rw [gap_comb hκ.ne' (hN (tB + 1)) (hN (tB + 1 + 1))] at hg
    unfold comb at hg
    rw [e1, e2] at hg
    rw [e1]
    have hsk : 0 < σ / κ := by positivity
    have k2 : σ / κ * (β * ((1 - δ) * ξ - (1 - δ) * δ * ξ)) ≤ 0 := by
      have : (1 - δ) * ξ - (1 - δ) * δ * ξ = (1 - δ) * ((1 - δ) * ξ) := by ring
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos hsk.le (mul_nonpos_of_nonneg_of_nonpos hβ.le
        (mul_nonpos_of_nonneg_of_nonpos (by linarith) hk3.le))
    by_contra hc
    push Not at hc
    have k1 : σ / κ * ((1 - δ) * ξ - π (tB + 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hsk.le (by linarith)
    linarith
  have hrise := back_rise hβ.le hκ hσ hN (M := tB + 1)
    (fun t _ => gap_nonneg_zero hσ hη.le hF t) hstart (by rw [e1]; exact hk3.le)
  refine nonpos_contra hβ hβ1 hκ hσ hϑ hopt (fun t => ?_) (fun t => ?_) ?_
  · rcases le_or_gt t (tB + 1) with h | h
    · linarith [(hrise t h).1, (hrise t h).2]
    · obtain ⟨k, rfl⟩ : ∃ k, t = tB + k + 2 := ⟨t - tB - 2, by omega⟩
      exact (hπp k).le
  · rcases le_or_gt t (tB + 1) with h | h
    · exact (x_neg_of_rise hβ1.le hκ (hN t) (hrise t h).1 (hrise t h).2).le
    · obtain ⟨k, rfl⟩ : ∃ k, t = tB + k + 2 := ⟨t - tB - 2, by omega⟩
      exact (hxp k).le
  · linarith [(hrise 0 (Nat.zero_le _)).1, (hrise 0 (Nat.zero_le _)).2]

/-! ## The classification -/

/-- Cochrane (2023), §20.2.4, pp. 478–480, Galí (2015), §5.4.2 (`ρ = 0`; any `β ∈ (0,1)`,
`κ, σ, ϑ, η > 0`, `t_Z`): **the optimal rate is zero at every date iff `ϑ ≤ σκ`.** -/
theorem rho_zero_zero_iff {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate 0 η tZ) x π) :
    (∀ t, impliedRate σ (natRate 0 η tZ) x π t = 0) ↔ ϑ ≤ σ * κ := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact rho_zero_lt_not_zero hβ hβ1 hκ hσ hϑ hη hc hopt h
  · intro hle
    obtain ⟨⟨-, hK⟩, -⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
    rcases rho_zero_structure hβ hβ1 hκ hσ hϑ hη hopt with h | ⟨hne, tC, htC, -, hpos⟩
    · exact h
    · exfalso
      refine rho_zero_gt_no_slack hβ hβ1 hκ hσ hϑ hη (lt_of_le_of_ne hle (Ne.symm hne)) hopt
        ⟨tC + 1, by omega, ?_⟩
      exact (mul_eq_zero.mp (hK (tC + 1)).2.2.2).resolve_right (hpos (tC + 1) (by omega)).ne'

/-- Cochrane (2023), §20.2.4, pp. 478–480, Galí (2015), §5.4.2, p. 152 (`ρ = 0`; any
`β ∈ (0,1)`, `κ, σ, ϑ, η > 0`, `t_Z`): **the optimal rate lifts off — there is `t_C ≥ t_Z` with
`i = 0` exactly on `[0, t_C]` and `i > 0` at every later date — iff `σκ < ϑ`.** -/
theorem rho_zero_liftoff_iff {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate 0 η tZ) x π) :
    (∃ tC, tZ ≤ tC ∧ (∀ t, t ≤ tC → impliedRate σ (natRate 0 η tZ) x π t = 0) ∧
      ∀ t, tC < t → 0 < impliedRate σ (natRate 0 η tZ) x π t) ↔ σ * κ < ϑ := by
  constructor
  · rintro ⟨tC, -, -, hpos⟩
    by_contra hc
    push Not at hc
    have h0 := (rho_zero_zero_iff hβ hβ1 hκ hσ hϑ hη hopt).mpr hc (tC + 1)
    linarith [hpos (tC + 1) (by omega)]
  · intro hr
    rcases rho_zero_structure hβ hβ1 hκ hσ hϑ hη hopt with h | ⟨-, h⟩
    · exact absurd h (rho_zero_lt_not_zero hβ hβ1 hκ hσ hϑ hη hr hopt)
    · exact h

/-- Cochrane (2023), §20.2.4, pp. 478–480, and Galí (2015), §5.4.2: **the commitment optimum with
a zero post-shock natural rate, fully classified** (`β ∈ (0,1)`, `κ, σ, ϑ, η > 0`, any `t_Z`):
it exists and is unique; if `ϑ ≤ σκ` its rate is zero at every date (no lift-off ever), and if
`σκ < ϑ` it lifts off at some `t_C ≥ t_Z`, with `i = 0` exactly on `[0, t_C]` and `i > 0` after.
Neither `η`, `β` nor `t_Z` affects which case occurs. -/
theorem rho_zero_classification {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hη : 0 < η) (tZ : ℕ) :
    ∃ x π, Optimal β κ σ ϑ (natRate 0 η tZ) x π ∧
      (∀ y q, Optimal β κ σ ϑ (natRate 0 η tZ) y q → y = x ∧ q = π) ∧
      (ϑ ≤ σ * κ → (∀ t, impliedRate σ (natRate 0 η tZ) x π t = 0) ∧
        ¬ ∃ tC, ∀ t, tC < t → 0 < impliedRate σ (natRate 0 η tZ) x π t) ∧
      (σ * κ < ϑ → ∃ tC, tZ ≤ tC ∧ (∀ t, t ≤ tC → impliedRate σ (natRate 0 η tZ) x π t = 0) ∧
        ∀ t, tC < t → 0 < impliedRate σ (natRate 0 η tZ) x π t) := by
  obtain ⟨x, π, hopt, hu⟩ := optimal_exists_unique (κ := κ) (η := η) hβ hσ hϑ le_rfl tZ
  refine ⟨x, π, hopt, hu, fun hle => ?_, fun hr => ?_⟩
  · have h0 := (rho_zero_zero_iff hβ hβ1 hκ hσ hϑ hη hopt).mpr hle
    refine ⟨h0, fun ⟨tC, h⟩ => ?_⟩
    have := h (tC + 1) (by omega)
    rw [h0] at this
    exact lt_irrefl _ this
  · exact (rho_zero_liftoff_iff hβ hβ1 hκ hσ hϑ hη hopt).mpr hr

/-- Cochrane (2023), §20.2.2, p. 475 and §20.2.4, p. 479 (`ρ = 0`, `ϑ ≤ σκ`): **the
no-lift-off optimum is a zero-rate (Werning) path with a positive promise**: `i ≡ 0`,
`π_{t_Z+1} > 0`, and after the shock inflation decays at the stable peg root
`μ = δ(β, κ, κσ)`. -/
theorem rho_zero_branch_a {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hη : 0 < η) (hr : ϑ ≤ σ * κ) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate 0 η tZ) x π) :
    (∀ t, impliedRate σ (natRate 0 η tZ) x π t = 0) ∧ 0 < π (tZ + 1) ∧
      ∀ n, tZ + 1 ≤ n → π (n + 1) = del β κ (κ * σ) * π n := by
  have h0 := (rho_zero_zero_iff hβ hβ1 hκ hσ hϑ hη hopt).mpr hr
  exact ⟨h0, zero_rate_pi_pos hβ hβ1 hκ hσ hϑ hη hopt h0,
    peg_geometric hβ hβ1 hκ hσ hϑ hopt fun t _ => h0 t⟩

/-- Galí (2015), pp. 149–152; Cochrane (2023), §20.2.4, p. 479 (`ρ = 0`, `σκ < ϑ`): **on the
lift-off branch Galí's sign condition holds automatically.** With `t_B` the last binding date,
`ξ₂ > 0` exactly on `[0, t_B]`, `i = 0` there, `ξ₁,t_B+1 > 0`, and after lift-off
`i_{t_B+2+k} = A δ^{k+1} > 0` with `A = (1 − δ)(1 − σκ/ϑ)ξ₁,t_B+1 > 0`. -/
theorem rho_zero_branch_b {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hη : 0 < η) (hr : σ * κ < ϑ) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate 0 η tZ) x π) :
    ∃ tB, tZ ≤ tB ∧ (∀ t, t ≤ tB → 0 < mxi2 β κ σ ϑ x π t) ∧
      (∀ t, tB < t → mxi2 β κ σ ϑ x π t = 0) ∧
      (∀ t, t ≤ tB → impliedRate σ (natRate 0 η tZ) x π t = 0) ∧
      0 < mxi1 β κ σ ϑ x π (tB + 1) ∧
      0 < (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * mxi1 β κ σ ϑ x π (tB + 1) ∧
      ∀ k, impliedRate σ (natRate 0 η tZ) x π (tB + k + 2) =
        (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * mxi1 β κ σ ϑ x π (tB + 1) * del β κ ϑ ^ (k + 1) := by
  obtain ⟨⟨hF, hK⟩, -⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  have hex : ∃ s, tZ < s ∧ mxi2 β κ σ ϑ x π s = 0 := by
    by_contra hcon
    push Not at hcon
    refine rho_zero_lt_not_zero hβ hβ1 hκ hσ hϑ hη hr hopt fun t => ?_
    rcases le_or_gt t tZ with h | h
    · exact (optimal_trap_binds hβ hβ1 hκ hσ hϑ le_rfl hη hopt t h).1
    · exact (mul_eq_zero.mp (hK t).2.2.2).resolve_left
        (lt_of_le_of_ne (hK t).2.2.1 (Ne.symm (hcon t h))).ne'
  obtain ⟨tB, htB, hpos, hz, h0, h1, hk⟩ := liftoff_rates hβ hβ1 hκ hσ hϑ le_rfl hη hopt hex
  have hA : 0 < (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * mxi1 β κ σ ϑ x π (tB + 1) := by
    have := rate_nonneg hσ hF (tB + 1)
    linarith
  have hδ1 : del β κ ϑ < 1 := (del_lt_one_iff hβ hβ1 hϑ).mpr hκ.ne'
  have hr1 : 0 < 1 - σ * κ / ϑ := by
    have : σ * κ / ϑ < 1 := by rw [div_lt_one hϑ]; exact hr
    linarith
  have hc : 0 < (1 - del β κ ϑ) * (1 - σ * κ / ϑ) := mul_pos (by linarith) hr1
  refine ⟨tB, htB, hpos, hz, h0, pos_of_mul_pos_right hA hc.le, hA, fun k => ?_⟩
  rw [hk k, zero_add]

/-! ## Exact certificates -/

/-- Galí (2015), p. 152, the verification theorem for the algorithm, **with `ρ = 0`**
(adapted from `algorithm_verification`, which needs `ρ > 0`); Cochrane (2023), §20.2.4, p. 479.
Guess `t_C ≥ t_Z`; if the candidate satisfies (48) on `[0, t_Z]`, the zero-rate recursion on
`(t_Z, t_C]`, (35)–(36) for `t ≤ t_C + 1`, the Phillips curve at `t_C + 1`, `ξ₂,t_C+1 = 0`, the
closed form (42)–(43) after `t_C + 1`, `ξ₂ ≥ 0` on `[0, t_C]`, `i_{t_C+1} ≥ 0` and
`A = (1 − δ)(1 − σκ/ϑ)ξ₁,t_C+1 ≥ 0` (so that every later rate `Aδ^{k+1}` is `≥ 0`), then it
satisfies the KKT system, is optimal and is the unique optimum. -/
theorem verification_zero {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) {tZ tC : ℕ} (htC : tZ ≤ tC)
    {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ 0 (x (t + 1), π (t + 1)))
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k ∧
      ξ1 (tC + k + 2) = postXi β κ ϑ (ξ1 (tC + 1)) (k + 1) ∧ ξ2 (tC + k + 2) = 0)
    (hsign : ∀ t, t ≤ tC → 0 ≤ ξ2 t)
    (hi1 : 0 ≤ impliedRate σ (natRate 0 η tZ) x π (tC + 1))
    (hA : 0 ≤ (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * ξ1 (tC + 1)) :
    KKT β κ σ ϑ (natRate 0 η tZ) x π ξ1 ξ2 ∧ Optimal β κ σ ϑ (natRate 0 η tZ) x π ∧
      (∀ t, t ≤ tC → impliedRate σ (natRate 0 η tZ) x π t = 0) ∧
      (∀ t, 0 ≤ impliedRate σ (natRate 0 η tZ) x π t) ∧
      (∀ y q, Feasible β κ σ (natRate 0 η tZ) y q → Summable (lossTerm β ϑ y q) →
        loss β ϑ y q ≤ loss β ϑ x π → y = x ∧ q = π) := by
  have hδ0 := del_pos (κ := κ) hβ hϑ
  have hδ1 := (del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  set ξ := ξ1 (tC + 1) with hξ
  set rn := natRate 0 η tZ with hrn
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
  have hbind : ∀ t, t ≤ tC → NKPC β κ x π t ∧ impliedRate σ rn x π t = 0 := by
    intro t ht
    rcases le_or_gt t tZ with h | h
    · exact backStep_nkpc_rate hσ.ne' (h48 t h) (by rw [hrn, natRate_of_le h])
    · exact backStep_nkpc_rate hσ.ne' (h49 t h ht) (by rw [hrn, natRate_of_lt h, neg_zero])
  have hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k := fun k => (hpost k).1
  have hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k := fun k => (hpost k).2.1
  have hrate : ∀ t, 0 ≤ impliedRate σ rn x π t := by
    intro t
    rcases le_or_gt t tC with ht | ht
    · rw [(hbind t ht).2]
    · rcases Nat.eq_or_lt_of_le ht with h | h
      · rw [← h]; exact hi1
      · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
        rw [post_rate hϑ.ne' htC hx hπ k]
        have e : (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * del β κ ϑ ^ (k + 1) * ξ =
            (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * ξ * del β κ ϑ ^ (k + 1) := by ring
        rw [e, zero_add]
        exact mul_nonneg hA (pow_nonneg hδ0.le _)
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
    refine ⟨feasible_of_rate hσ fun t => ⟨hnkpc t, hrate t⟩, fun t => ?_⟩
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
      have l1 : lag ξ1 (tC + k + 2) = postXi β κ ϑ ξ k := by rw [e, lag_succ, hξ1post]
      have l2 : lag ξ2 (tC + k + 2) = 0 := by rw [e, lag_succ, hξ2post]
      have x1 : ξ1 (tC + k + 2) = postXi β κ ϑ ξ (k + 1) := (hpost k).2.2.1
      have x2 : ξ2 (tC + k + 2) = 0 := (hpost k).2.2.2
      refine ⟨?_, ?_, by rw [x2], by rw [x2, zero_mul]⟩
      · unfold FOC35
        rw [l1, l2, x1, hπ, zero_div, sub_zero]
        exact post_eq37 β κ ϑ ξ k
      · unfold FOC36
        rw [l2, x1, x2, hx, zero_div, sub_zero, add_zero]
        exact post_eq38 hϑ.ne' ξ k
  -- bounded multipliers
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
  -- finite loss
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
  refine ⟨hK, kkt_optimal hβ hβ1 hσ hϑ hK hb hs, fun t ht => (hbind t ht).2, hrate,
    fun y q hy hsy hle => kkt_unique hβ hβ1 hσ hϑ hK hb hs hy hsy hle⟩

/-- Galí (2015), (15), p. 136; Cochrane (2023), p. 479: with `β = 1/2` and `κ² = (3/4)ϑ` the
commitment root is `δ = 1/2` (`γ = 4/9`, `√(1 − 4βγ²) = 7/9`). -/
theorem del_half {κ ϑ : ℝ} (hϑ : 0 < ϑ) (h : κ ^ 2 = 3 / 4 * ϑ) : del (1 / 2) κ ϑ = 1 / 2 := by
  have hg : gam (1 / 2) κ ϑ = 4 / 9 := by
    unfold gam
    rw [h, div_eq_iff (by positivity)]
    ring
  unfold del
  rw [hg, show (1 : ℝ) - 4 * (1 / 2) * (4 / 9) ^ 2 = (7 / 9) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- Cochrane (2023), §20.2.4, p. 479 (certificate, `β = 1/2`, `κ = 3`, `σ = 1`, `ϑ = 12`,
`η = 1`, `ρ = 0`, `t_Z = 0`): the output gap of the optimum, lift-off at `t_C = 0`. -/
noncomputable def nowX (t : ℕ) : ℝ :=
  if t = 0 then -50 / 621 else if t = 1 then 127 / 621 else postX (1 / 2) 3 12 (28 / 69) (t - 2)

/-- Cochrane (2023), §20.2.4, p. 479 (certificate): inflation of the optimum, `t_C = 0`. -/
noncomputable def nowP (t : ℕ) : ℝ :=
  if t = 0 then 8 / 69 else if t = 1 then 148 / 207 else postPi (1 / 2) 3 12 (28 / 69) (t - 2)

/-- Galí (2015), (35)–(36), p. 149 (certificate): the Phillips-curve multipliers, `t_C = 0`. -/
noncomputable def nowXi1 (t : ℕ) : ℝ :=
  if t = 0 then -8 / 69 else postXi (1 / 2) 3 12 (28 / 69) (t - 1)

/-- Galí (2015), (35)–(36), p. 149 (certificate): the zero-bound multipliers, `t_C = 0`. -/
noncomputable def nowXi2 (t : ℕ) : ℝ := if t = 0 then 128 / 207 else 0

/-- Cochrane (2023), §20.2.4, pp. 478–479, Galí (2015), p. 152: **exact certificate of an
immediate lift-off with `ρ = 0`** (`β = 1/2`, `κ = 3`, `σ = 1`, `ϑ = 12`, so `σκ/ϑ = 1/4 < 1`;
`η = 1`, `t_Z = 0`). The unique optimum has `x₀ = −50/621`, `π₀ = 8/69`, `x₁ = 127/621`,
`π₁ = 148/207`, `i₀ = 0`, `i₁ = 61/1242 > 0` and `i_{k+2} = (7/46)(1/2)^{k+1} > 0`. -/
theorem cert_liftoff_now :
    ∃ x π, Optimal (1 / 2) 3 1 12 (natRate 0 1 0) x π ∧
      (∀ y q, Optimal (1 / 2) 3 1 12 (natRate 0 1 0) y q → y = x ∧ q = π) ∧
      x 0 = -50 / 621 ∧ π 0 = 8 / 69 ∧ x 1 = 127 / 621 ∧ π 1 = 148 / 207 ∧
      impliedRate 1 (natRate 0 1 0) x π 0 = 0 ∧ impliedRate 1 (natRate 0 1 0) x π 1 = 61 / 1242 ∧
      ∀ k, impliedRate 1 (natRate 0 1 0) x π (k + 2) = 7 / 46 * (1 / 2) ^ (k + 1) := by
  have hd : del (1 / 2) 3 12 = 1 / 2 := del_half (by norm_num) (by norm_num)
  have h1 : nowXi1 (0 + 1) = 28 / 69 := by simp [nowXi1, postXi]
  have hx2 : nowX 2 = 7 / 138 := by simp only [nowX, postX]; norm_num; rw [hd]; norm_num
  have hp2 : nowP 2 = 14 / 69 := by simp only [nowP, postPi]; norm_num; rw [hd]; norm_num
  have hpost : ∀ k, nowX (0 + k + 2) = postX (1 / 2) 3 12 (nowXi1 (0 + 1)) k ∧
      nowP (0 + k + 2) = postPi (1 / 2) 3 12 (nowXi1 (0 + 1)) k ∧
      nowXi1 (0 + k + 2) = postXi (1 / 2) 3 12 (nowXi1 (0 + 1)) (k + 1) ∧
      nowXi2 (0 + k + 2) = 0 := by
    intro k
    rw [h1]
    simp [nowX, nowP, nowXi1, nowXi2]
  have hv := verification_zero (β := 1 / 2) (κ := 3) (σ := 1) (ϑ := 12) (η := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (tZ := 0) (tC := 0)
    le_rfl (x := nowX) (π := nowP) (ξ1 := nowXi1) (ξ2 := nowXi2)
    (fun t ht => by
      obtain rfl : t = 0 := by omega
      simp [nowX, nowP, backStep]
      norm_num)
    (fun t h1 h2 => by omega)
    (fun t ht => by
      interval_cases t <;> simp [FOC35, FOC36, nowX, nowP, nowXi1, nowXi2, postXi] <;> norm_num)
    (by unfold NKPC; rw [hp2]; simp [nowX, nowP]; norm_num) (by simp [nowXi2]) hpost
    (fun t ht => by obtain rfl : t = 0 := (by omega); simp [nowXi2]; norm_num)
    (by unfold impliedRate; rw [hp2, hx2, natRate_of_lt (by norm_num)]; simp [nowX]; norm_num)
    (by rw [h1, hd]; norm_num)
  obtain ⟨-, hopt, h0, -, huniq⟩ := hv
  refine ⟨nowX, nowP, hopt, fun y q hy => huniq y q hy.1 hy.2.1 (hy.2.2 _ _ hopt.1 hopt.2.1),
    by simp [nowX], by simp [nowP], by simp [nowX], by simp [nowP], h0 0 le_rfl, ?_, fun k => ?_⟩
  · unfold impliedRate
    rw [hp2, hx2, natRate_of_lt (by norm_num)]
    simp [nowX]
    norm_num
  · have hx := fun k => (hpost k).1
    have hp := fun k => (hpost k).2.1
    rw [show k + 2 = 0 + k + 2 by omega, post_rate (by norm_num) le_rfl hx hp k, h1, hd]
    ring

/-- Cochrane (2023), §20.2.4, p. 479 (certificate, `β = 1/2`, `κ = 1`, `σ = 1/2`, `ϑ = 4/3`,
`η = 1`, `ρ = 0`, `t_Z = 0`): the output gap of the optimum, lift-off at `t_C = 1`. -/
noncomputable def lateX (t : ℕ) : ℝ :=
  if t = 0 then -11446 / 48863 else if t = 1 then 25696 / 48863 else if t = 2 then 7312 / 48863
  else postX (1 / 2) 1 (4 / 3) (7520 / 48863) (t - 3)

/-- Cochrane (2023), §20.2.4, p. 479 (certificate): inflation of the optimum, `t_C = 1`. -/
noncomputable def lateP (t : ℕ) : ℝ :=
  if t = 0 then 3700 / 48863 else if t = 1 then 30292 / 48863 else if t = 2 then 9192 / 48863
  else postPi (1 / 2) 1 (4 / 3) (7520 / 48863) (t - 3)

/-- Galí (2015), (35)–(36), p. 149 (certificate): the Phillips-curve multipliers, `t_C = 1`. -/
noncomputable def lateXi1 (t : ℕ) : ℝ :=
  if t = 0 then -3700 / 48863 else if t = 1 then 36760 / 146589
  else postXi (1 / 2) 1 (4 / 3) (7520 / 48863) (t - 2)

/-- Galí (2015), (35)–(36), p. 149 (certificate): the zero-bound multipliers, `t_C = 1`. -/
noncomputable def lateXi2 (t : ℕ) : ℝ :=
  if t = 0 then 34684 / 146589 else if t = 1 then 3344 / 146589 else 0

/-- Cochrane (2023), §20.2.4, pp. 478–479, Galí (2015), p. 152: **exact certificate of a
delayed lift-off with `ρ = 0`** (`β = 1/2`, `κ = 1`, `σ = 1/2`, `ϑ = 4/3`, so
`σκ/ϑ = 3/8 < 1`; `η = 1`, `t_Z = 0`): the unique optimum keeps the rate at zero one period
beyond the shock (`i₀ = i₁ = 0`, `t_C = 1 > t_Z`), then `i₂ = 1514/48863 > 0` and
`i_{k+3} = (2350/48863)(1/2)^{k+1} > 0`. -/
theorem cert_liftoff_late :
    ∃ x π, Optimal (1 / 2) 1 (1 / 2) (4 / 3) (natRate 0 1 0) x π ∧
      (∀ y q, Optimal (1 / 2) 1 (1 / 2) (4 / 3) (natRate 0 1 0) y q → y = x ∧ q = π) ∧
      x 0 = -11446 / 48863 ∧ π 0 = 3700 / 48863 ∧ x 1 = 25696 / 48863 ∧ π 1 = 30292 / 48863 ∧
      x 2 = 7312 / 48863 ∧ π 2 = 9192 / 48863 ∧
      impliedRate (1 / 2) (natRate 0 1 0) x π 0 = 0 ∧
      impliedRate (1 / 2) (natRate 0 1 0) x π 1 = 0 ∧
      impliedRate (1 / 2) (natRate 0 1 0) x π 2 = 1514 / 48863 ∧
      ∀ k, impliedRate (1 / 2) (natRate 0 1 0) x π (k + 3) = 2350 / 48863 * (1 / 2) ^ (k + 1) := by
  have hd : del (1 / 2) 1 (4 / 3) = 1 / 2 := del_half (by norm_num) (by norm_num)
  have h1 : lateXi1 (1 + 1) = 7520 / 48863 := by simp [lateXi1, postXi]
  have hx3 : lateX 3 = 2820 / 48863 := by
    simp only [lateX, postX]; norm_num; rw [hd]; norm_num
  have hp3 : lateP 3 = 3760 / 48863 := by
    simp only [lateP, postPi]; norm_num; rw [hd]; norm_num
  have hpost : ∀ k, lateX (1 + k + 2) = postX (1 / 2) 1 (4 / 3) (lateXi1 (1 + 1)) k ∧
      lateP (1 + k + 2) = postPi (1 / 2) 1 (4 / 3) (lateXi1 (1 + 1)) k ∧
      lateXi1 (1 + k + 2) = postXi (1 / 2) 1 (4 / 3) (lateXi1 (1 + 1)) (k + 1) ∧
      lateXi2 (1 + k + 2) = 0 := by
    intro k
    rw [h1]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [lateX, lateP, lateXi1, lateXi2, show 1 + k + 2 = k + 3 by omega,
        show k + 3 - 3 = k by omega, show k + 3 - 2 = k + 1 by omega] <;> simp
  have hv := verification_zero (β := 1 / 2) (κ := 1) (σ := 1 / 2) (ϑ := 4 / 3) (η := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (tZ := 0) (tC := 1)
    (by norm_num) (x := lateX) (π := lateP) (ξ1 := lateXi1) (ξ2 := lateXi2)
    (fun t ht => by
      obtain rfl : t = 0 := by omega
      simp [lateX, lateP, backStep]
      norm_num)
    (fun t h1 h2 => by
      obtain rfl : t = 1 := by omega
      simp [lateX, lateP, backStep]
      norm_num)
    (fun t ht => by
      interval_cases t <;> simp [FOC35, FOC36, lateX, lateP, lateXi1, lateXi2, postXi] <;>
        norm_num)
    (by unfold NKPC; rw [show 1 + 1 + 1 = 3 by norm_num, hp3]; simp [lateX, lateP]; norm_num)
    (by simp [lateXi2]) hpost
    (fun t ht => by interval_cases t <;> simp [lateXi2] <;> norm_num)
    (by
      unfold impliedRate
      rw [show 1 + 1 + 1 = 3 by norm_num, hp3, hx3, natRate_of_lt (by norm_num)]
      simp [lateX]
      norm_num)
    (by rw [h1, hd]; norm_num)
  obtain ⟨-, hopt, h0, -, huniq⟩ := hv
  refine ⟨lateX, lateP, hopt, fun y q hy => huniq y q hy.1 hy.2.1 (hy.2.2 _ _ hopt.1 hopt.2.1),
    by simp [lateX], by simp [lateP], by simp [lateX], by simp [lateP], by simp [lateX],
    by simp [lateP], h0 0 (by norm_num), h0 1 le_rfl, ?_, fun k => ?_⟩
  · unfold impliedRate
    rw [show 2 + 1 = 3 by norm_num, hp3, hx3, natRate_of_lt (by norm_num)]
    simp [lateX]
    norm_num
  · have hx := fun k => (hpost k).1
    have hp := fun k => (hpost k).2.1
    rw [show k + 3 = 1 + k + 2 by omega, post_rate (by norm_num) (by norm_num) hx hp k, h1, hd]
    ring

/-- Cochrane (2023), §20.2.2, p. 475 (certificate, `β = 1/2`, `κ = 3/4`, `σ = 1`, `ϑ = 1/2`,
`η = 1`, `ρ = 0`, `t_Z = 0`, stable peg root `μ = 1/2`): the output gap of the zero-rate
optimum, `x₀ = −13/48`, `x_t = (35/48)(1/2)ᵗ` after the shock. -/
noncomputable def zfX (t : ℕ) : ℝ := if t = 0 then -13 / 48 else 35 / 48 * (1 / 2) ^ t

/-- Cochrane (2023), §20.2.2, p. 475 (certificate): inflation of the zero-rate optimum,
`π₀ = −1/48`, `π_t = (35/48)(1/2)ᵗ` after the shock. -/
noncomputable def zfP (t : ℕ) : ℝ := if t = 0 then -1 / 48 else 35 / 48 * (1 / 2) ^ t

/-- Galí (2015), (35)–(36), p. 149 (certificate): `ξ₁,t = (1 − 5t)/48 · (1/2)ᵗ`. -/
noncomputable def zfXi1 (t : ℕ) : ℝ := (1 - 5 * (t : ℝ)) / 48 * (1 / 2) ^ t

/-- Galí (2015), (35)–(36), p. 149 (certificate): `ξ₂,t = (29 + 5t)/192 · (1/2)ᵗ > 0` (the
resonant `t μᵗ` term of `forced_mult_contra`, here with the admissible sign). -/
noncomputable def zfXi2 (t : ℕ) : ℝ := (29 + 5 * (t : ℝ)) / 192 * (1 / 2) ^ t

/-- Cochrane (2023), §20.2.4, p. 479: `t · (1/2)ᵗ ≤ 1`. -/
theorem nat_mul_half_pow_le (t : ℕ) : (t : ℝ) * (1 / 2) ^ t ≤ 1 := by
  have h : (t : ℝ) < 2 ^ t := by exact_mod_cast Nat.lt_two_pow_self
  rw [one_div_pow, mul_one_div, div_le_one (by positivity)]
  exact h.le

/-- Cochrane (2023), §20.2.2, p. 475 and §20.2.4, pp. 478–479, Galí (2015), §5.4.2: **exact
certificate of a zero rate forever with `ρ = 0`** (`β = 1/2`, `κ = 3/4`, `σ = 1`, `ϑ = 1/2`, so
`σκ/ϑ = 3/2 > 1`; `η = 1`, `t_Z = 0`). The unique optimum is the zero-rate path
`x₀ = −13/48`, `π₀ = −1/48`, `x_t = π_t = (35/48)(1/2)ᵗ` for `t ≥ 1` (promise
`π₁ = 35/96 > 0`, decay at the peg root `1/2`), with `i_t = 0` at every date and zero-bound
multipliers `ξ₂,t = (29 + 5t)/192 · (1/2)ᵗ > 0` at every date. -/
theorem cert_zero_forever :
    ∃ x π, Optimal (1 / 2) (3 / 4) 1 (1 / 2) (natRate 0 1 0) x π ∧
      (∀ y q, Optimal (1 / 2) (3 / 4) 1 (1 / 2) (natRate 0 1 0) y q → y = x ∧ q = π) ∧
      x 0 = -13 / 48 ∧ π 0 = -1 / 48 ∧
      (∀ t, 0 < t → x t = 35 / 48 * (1 / 2) ^ t ∧ π t = 35 / 48 * (1 / 2) ^ t) ∧
      (∀ t, impliedRate 1 (natRate 0 1 0) x π t = 0) ∧
      ∀ t, mxi2 (1 / 2) (3 / 4) 1 (1 / 2) x π t = (29 + 5 * (t : ℝ)) / 192 * (1 / 2) ^ t ∧
        0 < mxi2 (1 / 2) (3 / 4) 1 (1 / 2) x π t := by
  have hN : ∀ t, NKPC (1 / 2) (3 / 4) zfX zfP t := by
    intro t
    rcases t with _ | n
    · simp [NKPC, zfX, zfP]
      norm_num
    · simp only [NKPC, zfX, zfP, Nat.succ_ne_zero, ↓reduceIte, pow_succ]
      ring
  have hR : ∀ t, impliedRate 1 (natRate 0 1 0) zfX zfP t = 0 := by
    intro t
    rcases t with _ | n
    · simp [impliedRate, natRate, zfX, zfP]
      norm_num
    · simp only [impliedRate, natRate_of_lt (Nat.succ_pos n), zfX, zfP, Nat.succ_ne_zero,
        ↓reduceIte, pow_succ]
      ring
  have hF : Feasible (1 / 2) (3 / 4) 1 (natRate 0 1 0) zfX zfP :=
    feasible_of_rate one_pos fun t => ⟨hN t, (hR t).symm.le⟩
  have h35 : ∀ t, FOC35 (1 / 2) 1 zfP zfXi1 zfXi2 t := by
    intro t
    rcases t with _ | n
    · simp [FOC35, zfP, zfXi1]
      norm_num
    · simp only [FOC35, zfP, zfXi1, zfXi2, lag_succ, Nat.succ_ne_zero, ↓reduceIte, pow_succ]
      push_cast
      ring
  have h36 : ∀ t, FOC36 (1 / 2) (3 / 4) (1 / 2) zfX zfXi1 zfXi2 t := by
    intro t
    rcases t with _ | n
    · simp [FOC36, zfX, zfXi1, zfXi2]
      norm_num
    · simp only [FOC36, zfX, zfXi1, zfXi2, lag_succ, Nat.succ_ne_zero, ↓reduceIte, pow_succ]
      push_cast
      ring
  have hpos : ∀ t, 0 < zfXi2 t := fun t => by unfold zfXi2; positivity
  have hK : KKT (1 / 2) (3 / 4) 1 (1 / 2) (natRate 0 1 0) zfX zfP zfXi1 zfXi2 :=
    ⟨hF, fun t => ⟨h35 t, h36 t, (hpos t).le, by rw [hR t, mul_zero]⟩⟩
  have hb : ∃ C, ∀ t, |zfXi1 t| ≤ C ∧ |zfXi2 t| ≤ C := by
    refine ⟨1, fun t => ?_⟩
    have h1 := nat_mul_half_pow_le t
    have h2 : (1 / 2 : ℝ) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h3 : (0 : ℝ) ≤ (1 / 2) ^ t := by positivity
    have h4 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    unfold zfXi1 zfXi2
    constructor
    · rw [abs_le]
      constructor <;> nlinarith
    · rw [abs_of_nonneg (by positivity)]
      nlinarith
  have hs : Summable (lossTerm (1 / 2) (1 / 2) zfX zfP) := by
    refine (summable_nat_add_iff 1).mp ?_
    have e : (fun n => lossTerm (1 / 2) (1 / 2) zfX zfP (n + 1)) = fun n =>
        (35 / 48) ^ 2 * (3 / 2) * (1 / 8) * (1 / 8 : ℝ) ^ n := by
      funext n
      simp only [lossTerm, zfX, zfP, Nat.succ_ne_zero, ↓reduceIte]
      rw [show (1 / 8 : ℝ) = (1 / 2) ^ 3 by norm_num, ← pow_mul]
      ring
    rw [e]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hopt := kkt_optimal (by norm_num) (by norm_num) one_pos (by norm_num) hK hb hs
  refine ⟨zfX, zfP, hopt, fun y q hy => kkt_unique (by norm_num) (by norm_num) one_pos
    (by norm_num) hK hb hs hy.1 hy.2.1 (hy.2.2 _ _ hopt.1 hopt.2.1), by simp [zfX],
    by simp [zfP], fun t ht => ?_, hR, fun t => ?_⟩
  · simp [zfX, zfP, Nat.pos_iff_ne_zero.mp ht]
  · have := (mult_unique (N := t) (κ := 3 / 4) (ϑ := 1 / 2) (x := zfX)
      (fun s _ => ⟨h35 s, h36 s⟩) t le_rfl).2
    rw [← this]
    exact ⟨rfl, hpos t⟩

end Cochrane.ZeroBound.LiftoffRhoZero
