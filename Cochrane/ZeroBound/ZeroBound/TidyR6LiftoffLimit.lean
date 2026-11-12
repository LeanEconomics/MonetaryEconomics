/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.ZLBRule
import ZeroBound.ForwardGuidance
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The early lift-off of Figure 20.3 in the continuous-time limit

Cochrane (2023), Chapter 20, §20.2.1, pp. 471–474 and Figure 20.3 (the rule
`i = max[π* + φ(π − π*), 0]` with a natural-rate shock; survey error E3: the rate lifts off before
`T`), compared with the delayed lift-off of §20.2.4, p. 479 (`ForwardGuidance.delayPi`).

The models of Figure 20.3 (static IS curve, discrete time, period 1) and of §20.2.4 (Werning's
continuous-time model, dynamic IS curve, an exogenous rate path) do not match. We build the
family of discrete models with period `h`: the model of `ZLBRule` with Phillips-curve slope `κh`
(rates per unit of time), whose map is an exact semi-implicit Euler step of the continuous-time
model `dπ/dt = σκ(i(π) − π − u)` (`fmap_scheme`); at `h = 1` it is Figure 20.3
(`fig203_member`). Throughout, `σκ > 0`, `φ > 1`, `π* > 0` and the shock is deep enough that
there is no steady state during the trap, `π*(φ − 1)/φ < −u` (the case of Figure 20.3, survey
E2, `ZLBRule.steady_exists_iff`).

## Main results

* Discrete, every period `h > 0` and trap length `N` periods (`sel_path`, `rate_pos_iff`,
  `AA_gt_kink_iff`): along the path selected by `π_N = π*`, the rate is positive at date
  `N − k` iff `k·log c_h < Λ`, where `c_h = (1 + φσκh)/(1 + σκh)` and
  `Λ = −log(1 − π*(φ − 1)/(−φu))`. The explicit selected path is `selPath`.
* The continuous-time limit model (`CTEq`, `piC`): `piC_solves` (existence), `ct_unique` (with
  local boundedness after `T`, the solution is unique), `ct_liftoff` (the rate is zero exactly up
  to `t_L = T − Λ/(σκ(φ − 1))` and positive after).
* **Convergence** for `h = T/N → 0`: `liftoff_eps` (for every `ε > 0` and all large `N` the rate
  is zero at every grid date `≤ t_L − ε` and positive at every grid date `≥ t_L + ε`),
  `liftoff_time_tendsto` (the discrete lift-off time tends to `max(t_L, 0)`) and `path_tendsto`
  (the inflation path converges pointwise on `[0, T]` to the continuous-time path).
* **The two lift-offs genuinely differ** (`early_vs_delayed`): the limit of Figure 20.3 lifts
  off strictly before the end of the trap, `t_L < T`, for every calibration, so survey error E3
  is not a discretisation artefact; delayed lift-off (`ForwardGuidance.delayI`) keeps the rate at
  zero until `L ≥ T`. On the nonempty interval `(max(t_L, 0), T)` the rule's rate is positive and
  the delayed rate is zero. At the Figure 20.3 calibration `t_L = 10 − 2 log 2 ≈ 8.61`, while the
  period-1 model lifts off at date 8 (`fig203_member`).
-/

namespace Cochrane.ZeroBound.TidyR6LiftoffLimit

open Filter Topology
open Cochrane.ZeroBound Cochrane.ZeroBound.ZLBRule

/-! ## Constants -/

/-- Cochrane (2023), eq. (20.4), p. 472: the shifted steady state `ū = u/(φ − 1)` of the active
branch (`π* + ū` is the upper steady state when it exists). -/
noncomputable def ubar (φ u : ℝ) : ℝ := u / (φ - 1)

/-- Cochrane (2023), p. 472: `q = 1 − π*(φ − 1)/(φ(−u))`, in `(0, 1)` when there is no steady
state. -/
noncomputable def qq (φ πs u : ℝ) : ℝ := 1 - πs * (φ - 1) / (φ * -u)

/-- Cochrane (2023), p. 472: `Λ = −log q`, the log growth of the distance to `ū` from `π*` down
to the kink. -/
noncomputable def Lam (φ πs u : ℝ) : ℝ := -Real.log (qq φ πs u)

/-- Cochrane (2023), eq. (20.4), p. 472: the continuous-time slope `σκ(φ − 1)` of the active
branch. -/
noncomputable def a0 (σ κ φ : ℝ) : ℝ := σ * κ * (φ - 1)

/-- Cochrane (2023), p. 472: the length `s* = Λ/(σκ(φ − 1))` of the positive-rate spell before
`T` in the continuous-time limit. -/
noncomputable def sStar (σ κ φ πs u : ℝ) : ℝ := Lam φ πs u / a0 σ κ φ

/-- Cochrane (2023), p. 472: the continuous-time lift-off date `t_L = T − s*`. -/
noncomputable def tL (σ κ φ πs u T : ℝ) : ℝ := T - sStar σ κ φ πs u

/-- Cochrane (2023), p. 472: `−ū(1 − q) = π*/φ`, the distance from `π*` to the kink. -/
theorem ubar_one_sub_qq {φ πs u : ℝ} (hφ : 1 < φ) (hu : u < 0) :
    -ubar φ u * (1 - qq φ πs u) = πs / φ := by
  have h1 : φ - 1 ≠ 0 := by linarith
  have h2 : φ ≠ 0 := by linarith
  have h3 : u ≠ 0 := hu.ne
  unfold ubar qq
  field_simp
  ring

/-- Cochrane (2023), p. 472: under the standing hypotheses `u < 0`, `ū < 0`, `0 < q < 1`,
`Λ > 0`, `σκ(φ − 1) > 0` and `s* > 0`. -/
theorem consts_pos {σ κ φ πs u : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) :
    u < 0 ∧ ubar φ u < 0 ∧ 0 < qq φ πs u ∧ qq φ πs u < 1 ∧ 0 < Lam φ πs u ∧ 0 < a0 σ κ φ ∧
      0 < sStar σ κ φ πs u := by
  have hk0 := (kink_mem hφ hπs).1
  have hu : u < 0 := by linarith
  have hub : ubar φ u < 0 := div_neg_of_neg_of_pos hu (by linarith)
  have hθ : πs * (φ - 1) / (φ * -u) = kink φ πs / -u := by
    unfold kink
    have : φ ≠ 0 := by linarith
    field_simp
  have hθ0 : 0 < kink φ πs / -u := div_pos hk0 (by linarith)
  have hθ1 : kink φ πs / -u < 1 := (div_lt_one (by linarith)).mpr hk
  have hq0 : 0 < qq φ πs u := by unfold qq; rw [hθ]; linarith
  have hq1 : qq φ πs u < 1 := by unfold qq; rw [hθ]; linarith
  have hL : 0 < Lam φ πs u := by
    unfold Lam
    have := Real.log_neg hq0 hq1
    linarith
  have ha : 0 < a0 σ κ φ := by unfold a0; nlinarith
  exact ⟨hu, hub, hq0, hq1, hL, ha, div_pos hL ha⟩

/-- Cochrane (2023), p. 472: `e^{−σκ(φ−1)s*} = q`. -/
theorem exp_sStar {σ κ φ πs u : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) : Real.exp (-(a0 σ κ φ * sStar σ κ φ πs u)) = qq φ πs u := by
  obtain ⟨-, -, hq0, -, -, ha, -⟩ := consts_pos hσκ hφ hπs hk
  unfold sStar Lam
  rw [mul_div_cancel₀ _ ha.ne', neg_neg, Real.exp_log hq0]

/-! ## The discrete model with period `h` -/

/-- Cochrane (2023), eq. (20.4), p. 472, with period `h`: the active-branch slope
`c_h = (1 + φσκh)/(1 + σκh)`. -/
noncomputable def cc (σ κ φ h : ℝ) : ℝ := slopeR σ (h * κ) φ

/-- Cochrane (2023), p. 472, with period `h`: the candidate active-branch path `k` periods
before `T`, `A_k = π* + ū(1 − c_h^{−k})`. -/
noncomputable def AA (σ κ φ πs u h : ℝ) (k : ℕ) : ℝ := πs + ubar φ u * (1 - (cc σ κ φ h)⁻¹ ^ k)

/-- Cochrane (2023), eq. (20.2), p. 472, with period `h`: the coefficient `σκh` is positive. -/
theorem ah_pos {σ κ h : ℝ} (hσκ : 0 < σ * κ) (hh : 0 < h) : 0 < σ * (h * κ) := by
  have : σ * (h * κ) = h * (σ * κ) := by ring
  rw [this]
  exact mul_pos hh hσκ

/-- Cochrane (2023), eq. (20.2), p. 472: the period-`h` map is an exact semi-implicit Euler step
of the continuous-time model `dπ/dt = σκ(i(π) − π − u)`:
`(f_h(π) − π)/h = σκ(i(π) − f_h(π) − u)`. -/
theorem fmap_scheme {σ κ φ πs u h : ℝ} (hh : 0 < h) (hσκ : 0 < σ * κ) (π : ℝ) :
    (fmap σ (h * κ) φ πs u π - π) / h =
      σ * κ * (rule φ πs π - fmap σ (h * κ) φ πs u π - u) := by
  have ha : 0 < σ * (h * κ) := ah_pos hσκ hh
  have hne : 1 + σ * h * κ ≠ 0 := by
    have : σ * h * κ = σ * (h * κ) := by ring
    rw [this]; linarith
  unfold fmap
  field_simp
  ring

/-- Cochrane (2023), eq. (20.4), p. 472: `c_h > 1`. -/
theorem cc_gt_one {σ κ φ h : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hh : 0 < h) :
    1 < cc σ κ φ h :=
  (slope_right_gt_one_iff (ah_pos hσκ hh)).mpr hφ

/-- Cochrane (2023), eq. (20.4), p. 472: the active-branch line
`ℓ(π) = π* + c_h(π − π*) − σκh u/(1 + σκh)` lies below the map everywhere. -/
theorem line_le {σ κ φ πs u h : ℝ} (hσκ : 0 < σ * κ) (hh : 0 < h) (π : ℝ) :
    πs + cc σ κ φ h * (π - πs) - σ * (h * κ) / (1 + σ * (h * κ)) * u ≤
      fmap σ (h * κ) φ πs u π := by
  have ha := ah_pos hσκ hh
  have hr : πs + φ * (π - πs) ≤ rule φ πs π := le_max_left _ _
  have e : fmap σ (h * κ) φ πs u π -
      (πs + cc σ κ φ h * (π - πs) - σ * (h * κ) / (1 + σ * (h * κ)) * u) =
      σ * (h * κ) * (rule φ πs π - (πs + φ * (π - πs))) / (1 + σ * (h * κ)) := by
    have hne : 1 + σ * h * κ ≠ 0 := by
      have : σ * h * κ = σ * (h * κ) := by ring
      rw [this]; linarith
    unfold fmap cc slopeR
    field_simp
    ring
  have : 0 ≤ σ * (h * κ) * (rule φ πs π - (πs + φ * (π - πs))) / (1 + σ * (h * κ)) :=
    div_nonneg (mul_nonneg ha.le (by linarith)) (by linarith)
  linarith

/-- Cochrane (2023), eq. (20.4), p. 472: on the active branch the map is the line. -/
theorem line_eq {σ κ φ πs u h π : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hh : 0 < h)
    (hπ : kink φ πs ≤ π) :
    fmap σ (h * κ) φ πs u π =
      πs + cc σ κ φ h * (π - πs) - σ * (h * κ) / (1 + σ * (h * κ)) * u := by
  have := eq20_4 (u := u) (ah_pos hσκ hh) (active_of_kink_le (by linarith) hπ)
  unfold cc
  linarith

/-- Cochrane (2023), eq. (20.3), p. 472: on the zero-bound branch the map is
`π/(1 + σκh) − σκh u/(1 + σκh)`. -/
theorem zlb_eq {σ κ φ πs u h π : ℝ} (hφ : 1 < φ) (hπ : π ≤ kink φ πs) :
    fmap σ (h * κ) φ πs u π =
      1 / (1 + σ * (h * κ)) * π - σ * (h * κ) / (1 + σ * (h * κ)) * u :=
  eq20_3 ((kink_iff (by linarith)).mpr hπ)

/-- Cochrane (2023), p. 472 (survey E2): with no steady state, the map lies strictly above the
diagonal, `π < f_h(π)`. -/
theorem lt_fmap {σ κ φ πs u h : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hh : 0 < h)
    (hk : kink φ πs < -u) (π : ℝ) : π < fmap σ (h * κ) φ πs u π := by
  have ha := ah_pos hσκ hh
  have hpos : 0 < rule φ πs π - π - u := by
    have h0 : 0 ≤ rule φ πs π := le_max_right _ _
    have h1 : πs + φ * (π - πs) ≤ rule φ πs π := le_max_left _ _
    rcases le_total π (kink φ πs) with hπ | hπ
    · linarith
    · have : (φ - 1) * (kink φ πs - πs) = -kink φ πs := by
        unfold kink; field_simp; ring
      have h2 : (φ - 1) * (kink φ πs - πs) ≤ (φ - 1) * (π - πs) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
  have e : fmap σ (h * κ) φ πs u π - π =
      σ * (h * κ) * (rule φ πs π - π - u) / (1 + σ * (h * κ)) := by
    have hne : 1 + σ * h * κ ≠ 0 := by
      have : σ * h * κ = σ * (h * κ) := by ring
      rw [this]; linarith
    unfold fmap
    field_simp
    ring
  have : 0 < σ * (h * κ) * (rule φ πs π - π - u) / (1 + σ * (h * κ)) :=
    div_pos (mul_pos ha hpos) (by linarith)
  linarith

/-- Cochrane (2023), p. 472: the line maps `A_{k+1}` to `A_k`. -/
theorem line_AA {σ κ φ πs u h : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hh : 0 < h) (k : ℕ) :
    πs + cc σ κ φ h * (AA σ κ φ πs u h (k + 1) - πs) - σ * (h * κ) / (1 + σ * (h * κ)) * u =
      AA σ κ φ πs u h k := by
  have ha := ah_pos hσκ hh
  have hc := cc_gt_one hσκ hφ hh
  have hc0 : cc σ κ φ h ≠ 0 := by linarith
  have hcm : cc σ κ φ h - 1 = (φ - 1) * (σ * (h * κ)) / (1 + σ * (h * κ)) := by
    have hne : 1 + σ * h * κ ≠ 0 := by
      have : σ * h * κ = σ * (h * κ) := by ring
      rw [this]; linarith
    unfold cc slopeR
    field_simp
    ring
  have hφ1 : φ - 1 ≠ 0 := by linarith
  unfold AA ubar
  rw [pow_succ]
  set X := (cc σ κ φ h)⁻¹ ^ k
  have hinv : cc σ κ φ h * (cc σ κ φ h)⁻¹ = 1 := mul_inv_cancel₀ hc0
  have e : cc σ κ φ h * (u / (φ - 1)) - σ * (h * κ) / (1 + σ * (h * κ)) * u = u / (φ - 1) := by
    have : cc σ κ φ h = 1 + (φ - 1) * (σ * (h * κ)) / (1 + σ * (h * κ)) := by linarith
    rw [this]
    field_simp
    ring
  linear_combination e - u / (φ - 1) * X * hinv

/-- Cochrane (2023), p. 472: `A_0 = π*`. -/
theorem AA_zero (σ κ φ πs u h : ℝ) : AA σ κ φ πs u h 0 = πs := by
  simp [AA]

/-- Cochrane (2023), p. 472: `A_k` is antitone in `k` (inflation falls going back in time). -/
theorem AA_antitone {σ κ φ πs u h : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hh : 0 < h) (hu : u < 0) :
    Antitone (AA σ κ φ πs u h) := by
  have hc := cc_gt_one hσκ hφ hh
  have hub : ubar φ u < 0 := div_neg_of_neg_of_pos hu (by linarith)
  refine antitone_nat_of_succ_le fun k => ?_
  have h0 : 0 < (cc σ κ φ h)⁻¹ := inv_pos.mpr (by linarith)
  have h1 : (cc σ κ φ h)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
  have : (cc σ κ φ h)⁻¹ ^ (k + 1) ≤ (cc σ κ φ h)⁻¹ ^ k :=
    pow_le_pow_of_le_one h0.le h1.le (Nat.le_succ k)
  unfold AA
  nlinarith

/-- Cochrane (2023), p. 472, Figure 20.3 with period `h`: **the selected path before `T`.** If
`p_N = π*` and `p_{n+1} = f_h(p_n)` before `N`, then `k ≤ N` periods before `N` the path is
`A_k` when `A_k` lies above the kink, and lies at or below the kink otherwise. -/
theorem sel_path {σ κ φ πs u h : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) (hh : 0 < h) {N : ℕ} {p : ℕ → ℝ} (hN : p N = πs)
    (hrec : ∀ n, n < N → p (n + 1) = fmap σ (h * κ) φ πs u (p n)) :
    ∀ k, k ≤ N → (kink φ πs < AA σ κ φ πs u h k → p (N - k) = AA σ κ φ πs u h k) ∧
      (AA σ κ φ πs u h k ≤ kink φ πs → p (N - k) ≤ kink φ πs) := by
  have ha := ah_pos hσκ hh
  have hc := cc_gt_one hσκ hφ hh
  have hu := (consts_pos hσκ hφ hπs hk).1
  have hkp := (kink_mem hφ hπs).2
  have hinj := (fmap_strictMono (σ := σ) (κ := h * κ) (φ := φ) (πs := πs) (u := u)
    (by linarith) ha).injective
  intro k
  induction k with
  | zero =>
    intro _
    rw [AA_zero, Nat.sub_zero, hN]
    exact ⟨fun _ => rfl, fun h => absurd h (not_le.mpr hkp)⟩
  | succ k ih =>
    intro hk1
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hstep : p (N - k) = fmap σ (h * κ) φ πs u (p (N - (k + 1))) := by
      have := hrec (N - (k + 1)) (by omega)
      rwa [show N - (k + 1) + 1 = N - k by omega] at this
    have hmono : AA σ κ φ πs u h (k + 1) ≤ AA σ κ φ πs u h k :=
      AA_antitone hσκ hφ hh hu (Nat.le_succ k)
    constructor
    · intro hA
      have e1 := ih1 (lt_of_lt_of_le hA hmono)
      have e2 : fmap σ (h * κ) φ πs u (AA σ κ φ πs u h (k + 1)) = AA σ κ φ πs u h k := by
        rw [line_eq hσκ hφ hh hA.le, line_AA hσκ hφ hh]
      exact hinj (by rw [← hstep, e1, e2])
    · intro hA
      by_cases hAk : kink φ πs < AA σ κ φ πs u h k
      · have e1 := ih1 hAk
        have hle := line_le (u := u) (φ := φ) (πs := πs) hσκ hh (p (N - (k + 1)))
        rw [← hstep, e1, ← line_AA hσκ hφ hh k] at hle
        have : p (N - (k + 1)) ≤ AA σ κ φ πs u h (k + 1) := by
          by_contra hcon
          push Not at hcon
          have := mul_lt_mul_of_pos_left (sub_lt_sub_right hcon πs) (by linarith : 0 < cc σ κ φ h)
          linarith
        linarith
      · push Not at hAk
        have := ih2 hAk
        have hg := lt_fmap (u := u) hσκ hφ hh hk (p (N - (k + 1)))
        rw [← hstep] at hg
        linarith

/-- Cochrane (2023), eq. (20.1), p. 472: for `φ > 0` the rate is positive iff inflation is above
the kink. -/
theorem rule_pos_iff {φ πs x : ℝ} (hφ : 0 < φ) : 0 < rule φ πs x ↔ kink φ πs < x := by
  unfold rule
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [max_eq_right ((kink_iff hφ).mpr hc)] at h
    exact lt_irrefl 0 h
  · intro h
    have : 0 < πs + φ * (x - πs) := by
      by_contra hc
      push Not at hc
      exact absurd ((kink_iff hφ).mp hc) (not_le.mpr h)
    exact lt_of_lt_of_le this (le_max_left _ _)

/-- Cochrane (2023), p. 472, Figure 20.3 with period `h` (survey E3): on the selected path the
rate at date `n ≤ N` is positive iff `A_{N−n}` lies above the kink. -/
theorem rate_pos_iff {σ κ φ πs u h : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) (hh : 0 < h) {N : ℕ} {p : ℕ → ℝ} (hN : p N = πs)
    (hrec : ∀ n, n < N → p (n + 1) = fmap σ (h * κ) φ πs u (p n)) {n : ℕ} (hn : n ≤ N) :
    0 < rule φ πs (p n) ↔ kink φ πs < AA σ κ φ πs u h (N - n) := by
  have hsp := sel_path hσκ hφ hπs hk hh hN hrec (N - n) (by omega)
  rw [show N - (N - n) = n by omega] at hsp
  rw [rule_pos_iff (by linarith)]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    linarith [hsp.2 hc]
  · intro h
    rw [hsp.1 h]
    exact h

/-- Cochrane (2023), p. 472: `A_k` lies above the kink iff `k·log c_h < Λ`. -/
theorem AA_gt_kink_iff {σ κ φ πs u h : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) (hh : 0 < h) (k : ℕ) :
    kink φ πs < AA σ κ φ πs u h k ↔ (k : ℝ) * Real.log (cc σ κ φ h) < Lam φ πs u := by
  obtain ⟨hu, hub, hq0, -, -, -, -⟩ := consts_pos hσκ hφ hπs hk
  have hc := cc_gt_one hσκ hφ hh
  have hX : 0 < (cc σ κ φ h)⁻¹ ^ k := pow_pos (inv_pos.mpr (by linarith)) k
  have hid : AA σ κ φ πs u h k - kink φ πs =
      -ubar φ u * ((cc σ κ φ h)⁻¹ ^ k - qq φ πs u) := by
    have h1 := ubar_one_sub_qq (πs := πs) hφ hu
    have h2 : πs - kink φ πs = πs / φ := by
      unfold kink; field_simp; ring
    unfold AA
    linear_combination h2 - h1
  have hlog : Real.log ((cc σ κ φ h)⁻¹ ^ k) = -((k : ℝ) * Real.log (cc σ κ φ h)) := by
    rw [Real.log_pow, Real.log_inv]
    ring
  constructor
  · intro hA
    have : qq φ πs u < (cc σ κ φ h)⁻¹ ^ k := by
      by_contra hcon
      push Not at hcon
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ -ubar φ u) (by linarith :
        (cc σ κ φ h)⁻¹ ^ k - qq φ πs u ≤ 0)
      linarith
    have := Real.log_lt_log hq0 this
    unfold Lam
    linarith
  · intro hA
    have : Real.log (qq φ πs u) < Real.log ((cc σ κ φ h)⁻¹ ^ k) := by
      unfold Lam at hA
      linarith
    have hlt := (Real.log_lt_log_iff hq0 hX).mp this
    have := mul_pos (by linarith : 0 < -ubar φ u) (by linarith :
      0 < (cc σ κ φ h)⁻¹ ^ k - qq φ πs u)
    linarith

/-! ## Limits as the period shrinks -/

/-- Cochrane (2023), eq. (20.4), p. 472: per unit of time, the log growth of the active branch
tends to the continuous-time rate, `log(c_h)/h → σκ(φ − 1)` as `h → 0⁺`. -/
theorem tendsto_logcc {σ κ φ : ℝ} :
    Tendsto (fun h => Real.log (cc σ κ φ h) / h) (𝓝[>] 0) (𝓝 (a0 σ κ φ)) := by
  have hnum : HasDerivAt (fun h : ℝ => 1 + φ * (σ * (h * κ))) (φ * (σ * κ)) 0 := by
    have := ((((hasDerivAt_id' (0 : ℝ)).mul_const κ).const_mul σ).const_mul φ).const_add 1
    convert this using 1
    ring
  have hden : HasDerivAt (fun h : ℝ => 1 + σ * (h * κ)) (σ * κ) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).mul_const κ).const_mul σ).const_add 1
    convert this using 1
    ring
  have hq := hnum.div hden (by simp)
  have hl := hq.log (by simp)
  have hs := hl.tendsto_slope_zero_right
  have h2 := hs.congr' (f₂ := fun h => Real.log (cc σ κ φ h) / h) (by
    filter_upwards [self_mem_nhdsWithin] with t _
    simp [cc, slopeR, smul_eq_mul, div_eq_inv_mul])
  convert h2 using 2
  simp only [Pi.div_apply, mul_zero, zero_mul, add_zero, one_pow, div_one, mul_one, one_mul]
  unfold a0
  ring

/-- Cochrane (2023), p. 472: the period `h = T/N` tends to `0⁺` as the number of periods in the
trap grows. -/
theorem tendsto_T_div {T : ℝ} (hT : 0 < T) : Tendsto (fun N : ℕ => T / N) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_div_atTop_nhds_zero_nat T,
    (eventually_gt_atTop 0).mono fun N hN => Set.mem_Ioi.mpr (div_pos hT (by exact_mod_cast hN))⟩

/-- Cochrane (2023), p. 472, Figure 20.3 in the continuous-time limit: **convergence of the
lift-off date.** For every `ε > 0`, for all large `N` (period `h = T/N`), along the path selected
by `π_N = π*` the rate is zero at every grid date `nh ≤ t_L − ε` and positive at every grid date
`nh ≥ t_L + ε` (`n ≤ N`). -/
theorem liftoff_eps {σ κ φ πs u T ε : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) (hT : 0 < T) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ → ℝ, p N = πs →
      (∀ n, n < N → p (n + 1) = fmap σ (T / N * κ) φ πs u (p n)) →
      ∀ n, n ≤ N → ((n : ℝ) * (T / N) ≤ tL σ κ φ πs u T - ε → rule φ πs (p n) = 0) ∧
        (tL σ κ φ πs u T + ε ≤ (n : ℝ) * (T / N) → 0 < rule φ πs (p n)) := by
  obtain ⟨-, -, -, -, hL, ha, hs⟩ := consts_pos hσκ hφ hπs hk
  set S := sStar σ κ φ πs u with hS
  have hLs : Lam φ πs u = a0 σ κ φ * S := by
    rw [hS, sStar]
    field_simp
  set r1 := Lam φ πs u / (S + ε) with hr1d
  set r2 := a0 σ κ φ + a0 σ κ φ * ε / S with hr2d
  have hr1 : r1 < a0 σ κ φ := by
    rw [hr1d, div_lt_iff₀ (by linarith), hLs]
    nlinarith
  have hr2 : a0 σ κ φ < r2 := by
    have : 0 < a0 σ κ φ * ε / S := by positivity
    linarith
  have hev := (tendsto_logcc.comp (tendsto_T_div hT)).eventually (Ioo_mem_nhds hr1 hr2)
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0 p hpN hrec n hn
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hh : 0 < T / N := div_pos hT hNr
  obtain ⟨hra, hrb⟩ := hN
  simp only [Function.comp] at hra hrb
  set r := Real.log (cc σ κ φ (T / N)) / (T / N) with hrd
  have hlogc : Real.log (cc σ κ φ (T / N)) = T / N * r := by
    rw [hrd]; field_simp
  have hkh : ((N - n : ℕ) : ℝ) * (T / N) = T - n * (T / N) := by
    rw [Nat.cast_sub hn]
    field_simp
  have key : 0 < rule φ πs (p n) ↔ (T - n * (T / N)) * r < Lam φ πs u := by
    rw [rate_pos_iff hσκ hφ hπs hk hh hpN hrec hn, AA_gt_kink_iff hσκ hφ hπs hk hh, hlogc,
      ← mul_assoc, hkh]
  have hr0 : 0 < r := lt_trans (div_pos hL (by linarith)) hra
  have hnT : (n : ℝ) * (T / N) ≤ T := by
    have : (n : ℝ) ≤ N := by exact_mod_cast hn
    calc (n : ℝ) * (T / N) ≤ N * (T / N) := by gcongr
      _ = T := by field_simp
  constructor
  · intro hle
    have hnot : ¬ 0 < rule φ πs (p n) := by
      rw [key, not_lt]
      have h1 : S + ε ≤ T - n * (T / N) := by
        have : tL σ κ φ πs u T = T - S := rfl
        linarith
      calc Lam φ πs u = (S + ε) * r1 := by rw [hr1d]; field_simp
        _ ≤ (S + ε) * r := by gcongr
        _ ≤ (T - n * (T / N)) * r := by gcongr
    exact le_antisymm (not_lt.mp hnot) (le_max_right _ _)
  · intro hge
    rw [key]
    have h1 : T - n * (T / N) ≤ S - ε := by
      have : tL σ κ φ πs u T = T - S := rfl
      linarith
    by_cases hse : S - ε ≤ 0
    · have : T - n * (T / N) = 0 := by linarith
      rw [this, zero_mul]
      exact hL
    · push Not at hse
      calc (T - n * (T / N)) * r ≤ (S - ε) * r := by gcongr
        _ < (S - ε) * r2 := by gcongr
        _ = a0 σ κ φ * (S ^ 2 - ε ^ 2) / S := by rw [hr2d]; field_simp; ring
        _ < Lam φ πs u := by
          rw [div_lt_iff₀ hs, hLs]
          nlinarith [mul_pos ha (mul_pos hε hε)]

/-! ## The explicit selected path and its lift-off date -/

/-- Cochrane (2023), eq. (20.2), p. 472, with period `h`: the explicit inverse of the
(strictly increasing, onto) map: the active-branch inverse above `f_h(kink)`, the zero-bound
inverse below. -/
noncomputable def finv (σ κ φ πs u h y : ℝ) : ℝ :=
  if fmap σ (h * κ) φ πs u (kink φ πs) ≤ y then
    πs + (y - πs + σ * (h * κ) / (1 + σ * (h * κ)) * u) / cc σ κ φ h
  else (1 + σ * (h * κ)) * y + σ * (h * κ) * u

/-- Cochrane (2023), eq. (20.2), p. 472: `f_h(finv(y)) = y`. -/
theorem fmap_finv {σ κ φ πs u h : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hh : 0 < h) (y : ℝ) :
    fmap σ (h * κ) φ πs u (finv σ κ φ πs u h y) = y := by
  have ha := ah_pos hσκ hh
  have hc := cc_gt_one hσκ hφ hh
  have hkink := line_eq (u := u) hσκ hφ hh (le_refl (kink φ πs))
  have hkz := zlb_eq (σ := σ) (κ := κ) (u := u) (h := h) hφ (le_refl (kink φ πs))
  have hne : 1 + σ * h * κ ≠ 0 := by
    have : σ * h * κ = σ * (h * κ) := by ring
    rw [this]; linarith
  unfold finv
  split_ifs with hy
  · set x := πs + (y - πs + σ * (h * κ) / (1 + σ * (h * κ)) * u) / cc σ κ φ h
    have hlx : πs + cc σ κ φ h * (x - πs) - σ * (h * κ) / (1 + σ * (h * κ)) * u = y := by
      simp only [x]
      field_simp
      ring
    have hxk : kink φ πs ≤ x := by
      by_contra hcon
      push Not at hcon
      have := mul_lt_mul_of_pos_left (sub_lt_sub_right hcon πs) (by linarith : 0 < cc σ κ φ h)
      linarith
    rw [line_eq hσκ hφ hh hxk, hlx]
  · push Not at hy
    set x := (1 + σ * (h * κ)) * y + σ * (h * κ) * u
    have hzx : 1 / (1 + σ * (h * κ)) * x - σ * (h * κ) / (1 + σ * (h * κ)) * u = y := by
      simp only [x]
      field_simp
      ring
    have hxk : x ≤ kink φ πs := by
      by_contra hcon
      push Not at hcon
      have h1 : 1 / (1 + σ * (h * κ)) * kink φ πs < 1 / (1 + σ * (h * κ)) * x :=
        mul_lt_mul_of_pos_left hcon (by positivity)
      linarith
    rw [zlb_eq hφ hxk, hzx]

/-- Cochrane (2023), Figure 20.3 with period `h`: the selected path, `π*` from `N` on and the
inverse map iterated backward before `N`. -/
noncomputable def selPath (σ κ φ πs u h : ℝ) (N n : ℕ) : ℝ :=
  if N ≤ n then πs else (finv σ κ φ πs u h)^[N - n] πs

/-- Cochrane (2023), Figure 20.3: `π_N = π*` on the selected path. -/
theorem selPath_N (σ κ φ πs u h : ℝ) (N : ℕ) : selPath σ κ φ πs u h N N = πs := by
  simp [selPath]

/-- Cochrane (2023), eq. (20.2), p. 472: the selected path solves the model before `N`. -/
theorem selPath_rec {σ κ φ πs u h : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hh : 0 < h) (N : ℕ) :
    ∀ n, n < N → selPath σ κ φ πs u h N (n + 1) =
      fmap σ (h * κ) φ πs u (selPath σ κ φ πs u h N n) := by
  intro n hn
  have h1 : selPath σ κ φ πs u h N (n + 1) = (finv σ κ φ πs u h)^[N - (n + 1)] πs := by
    unfold selPath
    by_cases hN : N ≤ n + 1
    · simp only [hN, ↓reduceIte, show N - (n + 1) = 0 by omega, Function.iterate_zero, id]
    · simp only [hN, ↓reduceIte]
  have h2 : selPath σ κ φ πs u h N n =
      finv σ κ φ πs u h ((finv σ κ φ πs u h)^[N - (n + 1)] πs) := by
    unfold selPath
    simp only [show ¬ N ≤ n by omega, ↓reduceIte]
    rw [show N - n = N - (n + 1) + 1 by omega, Function.iterate_succ_apply']
  rw [h1, h2, fmap_finv hσκ hφ hh]

/-- Cochrane (2023), Figure 20.3 with period `h`: the lift-off date, the first date with a
positive rate on the selected path. -/
noncomputable def liftIdx (σ κ φ πs u h : ℝ) (N : ℕ) : ℕ :=
  sInf {n | 0 < rule φ πs (selPath σ κ φ πs u h N n)}

/-- Cochrane (2023), Figure 20.3: the rate is positive at `N` (it is `π* > 0`). -/
theorem rate_N_pos {σ κ φ πs u h : ℝ} (hφ : 1 < φ) (hπs : 0 < πs) (N : ℕ) :
    0 < rule φ πs (selPath σ κ φ πs u h N N) := by
  rw [selPath_N, rule_pos_iff (by linarith)]
  exact (kink_mem hφ hπs).2

/-- Cochrane (2023), Figure 20.3: lift-off happens by `N`, and the rate is positive there. -/
theorem liftIdx_spec {σ κ φ πs u h : ℝ} (hφ : 1 < φ) (hπs : 0 < πs) (N : ℕ) :
    liftIdx σ κ φ πs u h N ≤ N ∧
      0 < rule φ πs (selPath σ κ φ πs u h N (liftIdx σ κ φ πs u h N)) ∧
      ∀ n, n < liftIdx σ κ φ πs u h N → rule φ πs (selPath σ κ φ πs u h N n) = 0 := by
  have hmem : N ∈ {n | 0 < rule φ πs (selPath σ κ φ πs u h N n)} := rate_N_pos hφ hπs N
  refine ⟨Nat.sInf_le hmem, Nat.sInf_mem ⟨N, hmem⟩, fun n hn => ?_⟩
  have := Nat.notMem_of_lt_sInf hn
  simp only [Set.mem_ofPred_eq, not_lt] at this
  exact le_antisymm this (le_max_right _ _)

/-- Cochrane (2023), Figure 20.3 in the continuous-time limit: **the discrete lift-off time
converges**, `h·liftIdx → max(t_L, 0)` as `h = T/N → 0`. -/
theorem liftoff_time_tendsto {σ κ φ πs u T : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) (hT : 0 < T) :
    Tendsto (fun N : ℕ => (liftIdx σ κ φ πs u (T / N) N : ℝ) * (T / N)) atTop
      (𝓝 (max (tL σ κ φ πs u T) 0)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hε : 0 < δ / 2 := by linarith
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (liftoff_eps (u := u) hσκ hφ hπs hk hT hε)
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp
    ((tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat T)).2 (δ / 2) hε)
  refine ⟨max (max N1 N2) 1, fun N hN => ?_⟩
  have hN0 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hh : 0 < T / N := div_pos hT hNr
  have hhd : T / N < δ / 2 := hN2 N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hE := hN1 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
    (selPath σ κ φ πs u (T / N) N) (selPath_N _ _ _ _ _ _ N) (selPath_rec hσκ hφ hh N)
  obtain ⟨hLN, hLpos, -⟩ := liftIdx_spec (σ := σ) (κ := κ) (u := u) (h := T / N) hφ hπs N
  set L := liftIdx σ κ φ πs u (T / N) N
  set t0 := tL σ κ φ πs u T
  have hx0 : 0 ≤ (L : ℝ) * (T / N) := by positivity
  -- lower bound
  have hlow : t0 - δ / 2 < (L : ℝ) * (T / N) := by
    by_contra hcon
    push Not at hcon
    have := (hE L hLN).1 hcon
    linarith
  -- upper bound
  have hup : (L : ℝ) * (T / N) < max t0 0 + δ / 2 + T / N := by
    set x := (t0 + δ / 2) / (T / N)
    set m := ⌈x⌉₊
    by_cases hm : m ≤ N
    · have hmx : t0 + δ / 2 ≤ (m : ℝ) * (T / N) := by
        have := Nat.le_ceil x
        rw [div_le_iff₀ hh] at this
        exact this
      have hpos := (hE m hm).2 hmx
      have hLm : L ≤ m := Nat.sInf_le hpos
      have hmlt : (m : ℝ) < max x 0 + 1 := by
        rcases le_or_gt x 0 with hx | hx
        · have : m = 0 := Nat.ceil_eq_zero.mpr hx
          rw [this, Nat.cast_zero]
          linarith [le_max_right x 0]
        · have := Nat.ceil_lt_add_one hx.le
          linarith [le_max_left x 0]
      have hxm : max x 0 * (T / N) = max (t0 + δ / 2) 0 := by
        rw [max_mul_of_nonneg _ _ hh.le, zero_mul]
        simp only [x, div_mul_cancel₀ _ hh.ne']
      calc (L : ℝ) * (T / N) ≤ m * (T / N) := by gcongr
        _ < (max x 0 + 1) * (T / N) := by gcongr
        _ = max (t0 + δ / 2) 0 + T / N := by rw [add_mul, one_mul, hxm]
        _ ≤ max t0 0 + δ / 2 + T / N := by
          have : max (t0 + δ / 2) 0 ≤ max t0 0 + δ / 2 :=
            max_le (by linarith [le_max_left t0 0]) (by linarith [le_max_right t0 0])
          linarith
    · push Not at hm
      have hxN : (N : ℝ) < x := Nat.lt_ceil.mp hm
      have hT' : T < t0 + δ / 2 := by
        rw [lt_div_iff₀ hh] at hxN
        have : (N : ℝ) * (T / N) = T := by field_simp
        linarith
      have : (L : ℝ) * (T / N) ≤ T := by
        calc (L : ℝ) * (T / N) ≤ N * (T / N) := by gcongr
          _ = T := by field_simp
      linarith [le_max_left t0 0]
  rw [Real.dist_eq, abs_lt]
  constructor
  · rcases le_total t0 0 with h0 | h0
    · rw [max_eq_right h0]; linarith
    · rw [max_eq_left h0]; linarith
  · linarith

/-! ## The continuous-time limit model -/

/-- Cochrane (2023), §20.2.1, p. 471, in continuous time (the limit of `fmap_scheme`): the
right-hand side `σκ(i(π) − π − u)` of `dπ/dt`, with `i(π) = max[π* + φ(π − π*), 0]`. -/
noncomputable def vfield (σ κ φ πs u x : ℝ) : ℝ := σ * κ * (rule φ πs x - x - u)

/-- Cochrane (2023), §20.2.1 and Figure 20.3, in continuous time: `π` is continuous on
`[0, ∞)`, solves `dπ/dt = σκ(i(π) − π − u)` on `(0, T]` (left derivative at `T`, the natural
rate `u` during the trap) and `dπ/dt = σκ(i(π) − π)` after `T`. -/
def CTEq (σ κ φ πs u T : ℝ) (π : ℝ → ℝ) : Prop :=
  ContinuousOn π (Set.Ici 0) ∧
    (∀ t ∈ Set.Ioc 0 T, HasDerivWithinAt π (vfield σ κ φ πs u (π t)) (Set.Iic t) t) ∧
    ∀ t, T < t → HasDerivAt π (vfield σ κ φ πs 0 (π t)) t

/-- Cochrane (2023), p. 472, continuous time: the active-branch path ending at `π_T = π*`,
`π* + ū(1 − e^{−σκ(φ−1)(T−t)})`. -/
noncomputable def piAct (σ κ φ πs u T t : ℝ) : ℝ :=
  πs + ubar φ u * (1 - Real.exp (-(a0 σ κ φ * (T - t))))

/-- Cochrane (2023), p. 472, continuous time: the zero-bound path reaching the kink at `t_L`,
`−u + (π*(φ − 1)/φ + u)e^{σκ(t_L − t)}`. -/
noncomputable def piZlb (σ κ φ πs u T t : ℝ) : ℝ :=
  -u + (kink φ πs + u) * Real.exp (σ * κ * (tL σ κ φ πs u T - t))

/-- Cochrane (2023), p. 472, continuous time: the trap path, zero-bound before `t_L`, active
after. -/
noncomputable def piG (σ κ φ πs u T t : ℝ) : ℝ :=
  if tL σ κ φ πs u T ≤ t then piAct σ κ φ πs u T t else piZlb σ κ φ πs u T t

/-- Cochrane (2023), Figure 20.3 in continuous time: the selected path, `piG` up to `T` and
`π*` afterwards. -/
noncomputable def piC (σ κ φ πs u T t : ℝ) : ℝ :=
  if t ≤ T then piG σ κ φ πs u T t else πs

/-- Cochrane (2023), eq. (20.1): `π* − π*(φ − 1)/φ = π*/φ`. -/
theorem sub_kink {φ πs : ℝ} (hφ : 1 < φ) : πs - kink φ πs = πs / φ := by
  unfold kink
  have : φ ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), p. 472: `piAct − kink = ū(q − e^{−σκ(φ−1)(T−t)})`. -/
theorem piAct_sub_kink {σ κ φ πs u T : ℝ} (hφ : 1 < φ) (hu : u < 0) (t : ℝ) :
    piAct σ κ φ πs u T t - kink φ πs =
      ubar φ u * (qq φ πs u - Real.exp (-(a0 σ κ φ * (T - t)))) := by
  have h1 := ubar_one_sub_qq (πs := πs) hφ hu
  have h2 := sub_kink (πs := πs) hφ
  unfold piAct
  linear_combination h2 - h1

/-- Cochrane (2023), p. 472: at or after `t_L` the active path is at or above the kink, strictly
after `t_L`. -/
theorem piAct_ge {σ κ φ πs u T t : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) (ht : tL σ κ φ πs u T ≤ t) :
    kink φ πs ≤ piAct σ κ φ πs u T t ∧
      (tL σ κ φ πs u T < t → kink φ πs < piAct σ κ φ πs u T t) := by
  obtain ⟨hu, hub, -, -, -, ha, -⟩ := consts_pos hσκ hφ hπs hk
  have he := exp_sStar hσκ hφ hπs hk
  have hd := piAct_sub_kink (σ := σ) (κ := κ) (πs := πs) (T := T) hφ hu t
  have htl : tL σ κ φ πs u T = T - sStar σ κ φ πs u := rfl
  have hmono : ∀ {x y : ℝ}, x ≤ y → Real.exp (-(a0 σ κ φ * y)) ≤ Real.exp (-(a0 σ κ φ * x)) :=
    fun hxy => Real.exp_le_exp.mpr (by nlinarith)
  constructor
  · have : qq φ πs u ≤ Real.exp (-(a0 σ κ φ * (T - t))) := by
      rw [← he]; exact hmono (by linarith)
    nlinarith
  · intro hlt
    have : qq φ πs u < Real.exp (-(a0 σ κ φ * (T - t))) := by
      rw [← he]; exact Real.exp_lt_exp.mpr (by nlinarith)
    nlinarith

/-- Cochrane (2023), p. 472: up to `t_L` the zero-bound path is at or below the kink, strictly
before `t_L`. -/
theorem piZlb_le {σ κ φ πs u T t : ℝ} (hσκ : 0 < σ * κ) (hk : kink φ πs < -u)
    (ht : t ≤ tL σ κ φ πs u T) :
    piZlb σ κ φ πs u T t ≤ kink φ πs ∧
      (t < tL σ κ φ πs u T → piZlb σ κ φ πs u T t < kink φ πs) := by
  have hku : kink φ πs + u < 0 := by linarith
  have e : piZlb σ κ φ πs u T t - kink φ πs =
      (kink φ πs + u) * (Real.exp (σ * κ * (tL σ κ φ πs u T - t)) - 1) := by
    unfold piZlb; ring
  constructor
  · have : 1 ≤ Real.exp (σ * κ * (tL σ κ φ πs u T - t)) :=
      Real.one_le_exp (mul_nonneg hσκ.le (by linarith))
    nlinarith
  · intro hlt
    have : 1 < Real.exp (σ * κ * (tL σ κ φ πs u T - t)) :=
      Real.one_lt_exp_iff.mpr (mul_pos hσκ (by linarith))
    nlinarith

/-- Cochrane (2023), eq. (20.4) in continuous time: on the active branch
`σκ(i(x) − x − u) = σκ((φ − 1)(x − π*) − u)`. -/
theorem vfield_active {σ κ φ πs u x : ℝ} (hφ : 1 < φ) (hx : kink φ πs ≤ x) :
    vfield σ κ φ πs u x = σ * κ * ((φ - 1) * (x - πs) - u) := by
  unfold vfield rule
  rw [max_eq_left (active_of_kink_le (by linarith) hx)]
  ring

/-- Cochrane (2023), eq. (20.3) in continuous time: on the zero-bound branch
`σκ(i(x) − x − u) = σκ(−x − u)`. -/
theorem vfield_zlb {σ κ φ πs u x : ℝ} (hφ : 1 < φ) (hx : x ≤ kink φ πs) :
    vfield σ κ φ πs u x = σ * κ * (-x - u) := by
  unfold vfield rule
  rw [max_eq_right ((kink_iff (by linarith)).mpr hx)]
  ring

/-- Cochrane (2023), p. 472: the active path solves the active-branch ODE. -/
theorem hasDerivAt_piAct {σ κ φ πs u T : ℝ} (hφ : 1 < φ) (t : ℝ) :
    HasDerivAt (piAct σ κ φ πs u T)
      (σ * κ * ((φ - 1) * (piAct σ κ φ πs u T t - πs) - u)) t := by
  have hg : HasDerivAt (fun s => -(a0 σ κ φ * (T - s))) (a0 σ κ φ) t := by
    have := ((hasDerivAt_id' t).const_sub T).const_mul (a0 σ κ φ) |>.neg
    convert this using 1; ring
  have h := ((hg.exp).const_sub 1).const_mul (ubar φ u) |>.const_add πs
  unfold piAct
  refine h.congr_deriv ?_
  have hφ1 : φ - 1 ≠ 0 := by linarith
  unfold ubar a0
  field_simp
  ring

/-- Cochrane (2023), p. 472: the zero-bound path solves the zero-bound ODE. -/
theorem hasDerivAt_piZlb {σ κ φ πs u T : ℝ} (t : ℝ) :
    HasDerivAt (piZlb σ κ φ πs u T) (σ * κ * (-piZlb σ κ φ πs u T t - u)) t := by
  have hg : HasDerivAt (fun s => σ * κ * (tL σ κ φ πs u T - s)) (-(σ * κ)) t := by
    have := ((hasDerivAt_id' t).const_sub (tL σ κ φ πs u T)).const_mul (σ * κ)
    convert this using 1; ring
  have h := ((hg.exp).const_mul (kink φ πs + u)).const_add (-u)
  unfold piZlb
  refine h.congr_deriv ?_
  ring

/-- Cochrane (2023), p. 472: `piAct(t_L) = π*(φ − 1)/φ`. -/
theorem piAct_tL {σ κ φ πs u T : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) : piAct σ κ φ πs u T (tL σ κ φ πs u T) = kink φ πs := by
  have hu := (consts_pos hσκ hφ hπs hk).1
  have hd := piAct_sub_kink (σ := σ) (κ := κ) (πs := πs) (T := T) hφ hu (tL σ κ φ πs u T)
  rw [show T - tL σ κ φ πs u T = sStar σ κ φ πs u by unfold tL; ring,
    exp_sStar hσκ hφ hπs hk, sub_self, mul_zero] at hd
  linarith

/-- Cochrane (2023), p. 472: the trap path is continuous. -/
theorem piG_continuous {σ κ φ πs u T : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) : Continuous (piG σ κ φ πs u T) := by
  unfold piG
  refine Continuous.if_le ?_ ?_ continuous_const continuous_id ?_
  · unfold piAct; fun_prop
  · unfold piZlb; fun_prop
  · intro x hx
    rw [← hx, piAct_tL hσκ hφ hπs hk]
    unfold piZlb
    simp

/-- Cochrane (2023), eq. (20.1): the right-hand side is continuous. -/
theorem vfield_continuous (σ κ φ πs u : ℝ) : Continuous (vfield σ κ φ πs u) := by
  unfold vfield rule
  fun_prop

/-- Cochrane (2023), p. 472: the trap path solves `dπ/dt = σκ(i(π) − π − u)` at every date
(including `t_L`, where the two branches meet with the same slope). -/
theorem hasDerivAt_piG {σ κ φ πs u T : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) (t : ℝ) :
    HasDerivAt (piG σ κ φ πs u T) (vfield σ κ φ πs u (piG σ κ φ πs u T t)) t := by
  refine hasDerivAt_of_hasDerivAt_of_ne' (x := tL σ κ φ πs u T) (fun y hy => ?_)
    (piG_continuous hσκ hφ hπs hk).continuousAt
    ((vfield_continuous σ κ φ πs u).comp (piG_continuous hσκ hφ hπs hk)).continuousAt t
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · have hev : piG σ κ φ πs u T =ᶠ[𝓝 y] piZlb σ κ φ πs u T := by
      filter_upwards [Iio_mem_nhds hlt] with z hz
      simp [piG, not_le.mpr (Set.mem_Iio.mp hz)]
    have hy' : piG σ κ φ πs u T y = piZlb σ κ φ πs u T y := hev.eq_of_nhds
    change HasDerivAt _ (vfield σ κ φ πs u (piG σ κ φ πs u T y)) y
    rw [hy', vfield_zlb hφ (piZlb_le hσκ hk hlt.le).1]
    exact (hasDerivAt_piZlb y).congr_of_eventuallyEq hev
  · have hev : piG σ κ φ πs u T =ᶠ[𝓝 y] piAct σ κ φ πs u T := by
      filter_upwards [Ioi_mem_nhds hgt] with z hz
      simp [piG, (Set.mem_Ioi.mp hz).le]
    have hy' : piG σ κ φ πs u T y = piAct σ κ φ πs u T y := hev.eq_of_nhds
    change HasDerivAt _ (vfield σ κ φ πs u (piG σ κ φ πs u T y)) y
    rw [hy', vfield_active hφ (piAct_ge hσκ hφ hπs hk hgt.le).1]
    exact (hasDerivAt_piAct hφ y).congr_of_eventuallyEq hev

/-- Cochrane (2023), p. 472: `t_L < T`. -/
theorem tL_lt {σ κ φ πs u T : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) : tL σ κ φ πs u T < T := by
  have := (consts_pos hσκ hφ hπs hk).2.2.2.2.2.2
  unfold tL; linarith

/-- Cochrane (2023), p. 472: `piG(T) = π*`. -/
theorem piG_T {σ κ φ πs u T : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) : piG σ κ φ πs u T T = πs := by
  simp [piG, (tL_lt (T := T) hσκ hφ hπs hk).le, piAct]

/-- Cochrane (2023), Figure 20.3 in continuous time: the selected path is continuous. -/
theorem piC_continuous {σ κ φ πs u T : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) : Continuous (piC σ κ φ πs u T) := by
  unfold piC
  refine Continuous.if_le (piG_continuous hσκ hφ hπs hk) continuous_const continuous_id
    continuous_const ?_
  intro x hx
  rw [hx, piG_T hσκ hφ hπs hk]

/-- Cochrane (2023), Figure 20.3 in continuous time: **existence** — the selected path solves the
continuous-time model. -/
theorem piC_solves {σ κ φ πs u T : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) : CTEq σ κ φ πs u T (piC σ κ φ πs u T) := by
  refine ⟨(piC_continuous hσκ hφ hπs hk).continuousOn, fun t ht => ?_, fun t ht => ?_⟩
  · have heq : Set.EqOn (piC σ κ φ πs u T) (piG σ κ φ πs u T) (Set.Iic t) := fun s hs => by
      simp [piC, le_trans (Set.mem_Iic.mp hs) ht.2]
    rw [heq (Set.mem_Iic.mpr le_rfl)]
    exact (hasDerivAt_piG hσκ hφ hπs hk t).hasDerivWithinAt.congr heq
      (heq (Set.mem_Iic.mpr le_rfl))
  · have hev : piC σ κ φ πs u T =ᶠ[𝓝 t] fun _ => πs := by
      filter_upwards [Ioi_mem_nhds ht] with z hz
      simp [piC, not_le.mpr (Set.mem_Ioi.mp hz)]
    have hv : vfield σ κ φ πs 0 πs = 0 := by
      unfold vfield rule; simp [max_eq_left hπs.le]
    rw [hev.eq_of_nhds, hv]
    exact (hasDerivAt_const t πs).congr_of_eventuallyEq hev

/-- Cochrane (2023), eq. (20.1): the right-hand side is Lipschitz with constant `σκ(φ + 1)`. -/
theorem vfield_lipschitz {σ κ φ πs u : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) :
    LipschitzWith (Real.toNNReal (σ * κ * (φ + 1))) (vfield σ κ φ πs u) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by nlinarith)]
  have h1 := abs_max_sub_max_le_abs (πs + φ * (x - πs)) (πs + φ * (y - πs)) 0
  have h2 : |πs + φ * (x - πs) - (πs + φ * (y - πs))| = φ * |x - y| := by
    rw [show πs + φ * (x - πs) - (πs + φ * (y - πs)) = φ * (x - y) by ring, abs_mul,
      abs_of_pos (by linarith)]
  have h3 : vfield σ κ φ πs u x - vfield σ κ φ πs u y =
      σ * κ * ((rule φ πs x - rule φ πs y) - (x - y)) := by
    unfold vfield; ring
  rw [h3, abs_mul, abs_of_pos hσκ]
  have h4 : |rule φ πs x - rule φ πs y - (x - y)| ≤ |rule φ πs x - rule φ πs y| + |x - y| :=
    abs_sub _ _
  unfold rule at h4
  have h5 : |rule φ πs x - rule φ πs y - (x - y)| ≤ (φ + 1) * |x - y| := by
    unfold rule; nlinarith
  calc σ * κ * |rule φ πs x - rule φ πs y - (x - y)| ≤ σ * κ * ((φ + 1) * |x - y|) :=
        mul_le_mul_of_nonneg_left h5 hσκ.le
    _ = σ * κ * (φ + 1) * |x - y| := by ring

/-- Cochrane (2023), Figure 20.3 in continuous time: **uniqueness** (the continuous-time
counterpart of `ZLBRule.fig203_selection`). If `π` solves the model and stays within
`ε < π* − π*(φ − 1)/φ` of `π*` from `T` on (local boundedness under the active rule), then
`π = π*` from `T` on and `π` is the path `piC` on `[0, ∞)`. -/
theorem ct_unique {σ κ φ πs u T ε : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) (hT : 0 < T) {π : ℝ → ℝ} (h : CTEq σ κ φ πs u T π)
    (hε : ε < πs - kink φ πs) (hb : ∀ t, T ≤ t → |π t - πs| ≤ ε) :
    ∀ t, 0 ≤ t → π t = piC σ κ φ πs u T t := by
  obtain ⟨hc, hd, hd'⟩ := h
  have ha := (consts_pos hσκ hφ hπs hk).2.2.2.2.2.1
  -- after `T`
  have hafter : ∀ t, T ≤ t → π t - πs = 0 := by
    refine ContinuousTimeNK.unstable_bdd_zero (f := fun t => π t - πs) (a := a0 σ κ φ) (S := ∅) ha
      Set.countable_empty ((hc.mono (Set.Ici_subset_Ici.mpr hT.le)).sub continuousOn_const)
      (fun t ht _ => ?_) hb
    have hπt : kink φ πs ≤ π t := by
      have := hb t ht.le
      rw [abs_le] at this
      linarith
    have := (hd' t ht).sub_const πs
    rw [vfield_active hφ hπt] at this
    refine this.congr_deriv ?_
    unfold a0; ring
  have hπT : π T = piC σ κ φ πs u T T := by
    have := hafter T le_rfl
    simp only [piC, le_rfl, ↓reduceIte, piG_T hσκ hφ hπs hk]
    linarith
  -- on `[0, T]`
  have hon : Set.EqOn π (piC σ κ φ πs u T) (Set.Icc 0 T) := by
    have hsol := piC_solves (u := u) (T := T) hσκ hφ hπs hk
    refine ODE_solution_unique_of_mem_Icc_left (v := fun _ x => vfield σ κ φ πs u x)
      (s := fun _ => Set.univ) (K := Real.toNNReal (σ * κ * (φ + 1)))
      (fun _ _ => (vfield_lipschitz hσκ hφ).lipschitzOnWith)
      (hc.mono Set.Icc_subset_Ici_self) hd (fun _ _ => Set.mem_univ _)
      (hsol.1.mono Set.Icc_subset_Ici_self) hsol.2.1 (fun _ _ => Set.mem_univ _) hπT
  intro t ht
  by_cases htT : t ≤ T
  · exact hon ⟨ht, htT⟩
  · push Not at htT
    have := hafter t htT.le
    simp only [piC, not_le.mpr htT, ↓reduceIte]
    linarith

/-- Cochrane (2023), Figure 20.3 in continuous time, survey error E3: on `[0, T]` the rate is
positive exactly after `t_L`: `i(π_t) > 0 ↔ t_L < t`. -/
theorem ct_liftoff {σ κ φ πs u T t : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) (htT : t ≤ T) :
    0 < rule φ πs (piC σ κ φ πs u T t) ↔ tL σ κ φ πs u T < t := by
  rw [rule_pos_iff (by linarith)]
  simp only [piC, htT, ↓reduceIte, piG]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    rcases hcon.lt_or_eq with hlt | heq
    · simp only [not_le.mpr hlt, ↓reduceIte] at h
      linarith [(piZlb_le hσκ hk hlt.le).1]
    · simp only [heq, le_rfl, ↓reduceIte, piAct_tL hσκ hφ hπs hk] at h
      exact lt_irrefl _ h
  · intro h
    simp only [h.le, ↓reduceIte]
    exact (piAct_ge hσκ hφ hπs hk h.le).2 h

/-! ## Convergence of the discrete paths -/

/-- Cochrane (2023), eq. (20.3), p. 472: per unit of time, the log growth of the zero-bound
branch tends to `σκ`, `log(1 + σκh)/h → σκ` as `h → 0⁺`. -/
theorem tendsto_log1p {σ κ : ℝ} :
    Tendsto (fun h => Real.log (1 + σ * (h * κ)) / h) (𝓝[>] 0) (𝓝 (σ * κ)) := by
  have hden : HasDerivAt (fun h : ℝ => 1 + σ * (h * κ)) (σ * κ) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).mul_const κ).const_mul σ).const_add 1
    convert this using 1
    ring
  have hl := hden.log (by simp)
  have hs := hl.tendsto_slope_zero_right
  have h2 := hs.congr' (f₂ := fun h => Real.log (1 + σ * (h * κ)) / h) (by
    filter_upwards [self_mem_nhdsWithin] with t _
    simp [smul_eq_mul, div_eq_inv_mul])
  convert h2 using 2
  simp

/-- Cochrane (2023), p. 472: `(c⁻¹)ᵏ = e^{−(kh)(log c/h)}`. -/
theorem inv_pow_eq_exp {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (k : ℕ) :
    c⁻¹ ^ k = Real.exp (-((k : ℝ) * h * (Real.log c / h))) := by
  rw [show -((k : ℝ) * h * (Real.log c / h)) = k * Real.log c⁻¹ by
    rw [Real.log_inv]; field_simp, Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hc)]

/-- Cochrane (2023), p. 472: `(1 + b)ᵐ = e^{(mh)(log(1 + b)/h)}`. -/
theorem pow_eq_exp {b h : ℝ} (hb : 0 < 1 + b) (hh : 0 < h) (m : ℕ) :
    (1 + b) ^ m = Real.exp ((m : ℝ) * h * (Real.log (1 + b) / h)) := by
  rw [show (m : ℝ) * h * (Real.log (1 + b) / h) = m * Real.log (1 + b) by field_simp,
    Real.exp_nat_mul, Real.exp_log hb]

/-- Cochrane (2023), p. 472: `(L − n)h = max(Lh − nh, 0)` for truncated subtraction. -/
theorem natSub_mul {h : ℝ} (hh : 0 ≤ h) (L n : ℕ) :
    ((L - n : ℕ) : ℝ) * h = max ((L : ℝ) * h - n * h) 0 := by
  rcases le_total n L with hnL | hnL
  · rw [Nat.cast_sub hnL, sub_mul, max_eq_left]
    have : (n : ℝ) ≤ L := by exact_mod_cast hnL
    nlinarith
  · rw [Nat.sub_eq_zero_of_le hnL, Nat.cast_zero, zero_mul, max_eq_right]
    have : (L : ℝ) ≤ n := by exact_mod_cast hnL
    nlinarith

/-- Cochrane (2023), eq. (20.3), p. 472: on the zero-bound spell before lift-off the selected
path is `p_{L−j} = −u + (1 + σκh)ʲ(p_L + u)`. -/
theorem zlb_back {σ κ φ πs u h : ℝ} (hφ : 1 < φ) {N : ℕ} {p : ℕ → ℝ}
    (hrec : ∀ n, n < N → p (n + 1) = fmap σ (h * κ) φ πs u (p n)) {L : ℕ} (hLN : L ≤ N)
    (hzero : ∀ n, n < L → rule φ πs (p n) = 0) (hσh : 0 < 1 + σ * (h * κ)) :
    ∀ j, j ≤ L → p (L - j) = -u + (1 + σ * (h * κ)) ^ j * (p L + u) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hn : L - (j + 1) < L := by omega
    have hle : p (L - (j + 1)) ≤ kink φ πs := by
      have := hzero _ hn
      by_contra hcon
      push Not at hcon
      have := (rule_pos_iff (πs := πs) (by linarith)).mpr hcon
      linarith
    have hstep := hrec (L - (j + 1)) (by omega)
    rw [show L - (j + 1) + 1 = L - j by omega, ih (by omega), zlb_eq hφ hle] at hstep
    have hne' : 1 + σ * h * κ ≠ 0 := by
      have : σ * h * κ = σ * (h * κ) := by ring
      rw [this]; exact hσh.ne'
    have hy : p (L - (j + 1)) = (1 + σ * (h * κ)) * (-u + (1 + σ * (h * κ)) ^ j * (p L + u)) +
        σ * (h * κ) * u := by
      rw [hstep]; field_simp; ring
    rw [hy, pow_succ]
    ring

/-- Cochrane (2023), p. 472: on the selected path, once the rate is positive it stays positive
up to `N`. -/
theorem pos_of_ge {σ κ φ πs u h : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) (hh : 0 < h) {N : ℕ} {p : ℕ → ℝ} (hN : p N = πs)
    (hrec : ∀ n, n < N → p (n + 1) = fmap σ (h * κ) φ πs u (p n)) {L n : ℕ} (hLn : L ≤ n)
    (hnN : n ≤ N) (hL : 0 < rule φ πs (p L)) : 0 < rule φ πs (p n) := by
  have hu := (consts_pos hσκ hφ hπs hk).1
  rw [rate_pos_iff hσκ hφ hπs hk hh hN hrec (le_trans hLn hnN)] at hL
  rw [rate_pos_iff hσκ hφ hπs hk hh hN hrec hnN]
  exact lt_of_lt_of_le hL (AA_antitone hσκ hφ hh hu (by omega))

/-- Cochrane (2023), p. 472: a sequence that at each date equals one of two sequences with the
same limit has that limit. -/
theorem tendsto_of_or {f x y : ℕ → ℝ} {l : ℝ} (h : ∀ᶠ N in atTop, f N = x N ∨ f N = y N)
    (hx : Tendsto x atTop (𝓝 l)) (hy : Tendsto y atTop (𝓝 l)) : Tendsto f atTop (𝓝 l) := by
  rw [Metric.tendsto_nhds] at hx hy ⊢
  intro ε hε
  filter_upwards [h, hx ε hε, hy ε hε] with N hN h1 h2
  rcases hN with e | e <;> rw [e] <;> assumption

/-- Cochrane (2023), p. 472: the limit of the zero-bound part, at `0 ≤ t ≤ t_L`. -/
theorem ylim_eq {σ κ φ πs u T t : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) (ht0 : 0 ≤ t) (ht : t ≤ tL σ κ φ πs u T) :
    -u + Real.exp (max (max (tL σ κ φ πs u T) 0 - t) 0 * (σ * κ)) *
      (πs + ubar φ u * (1 - Real.exp (-((T - max (tL σ κ φ πs u T) 0) * a0 σ κ φ))) + u) =
      piZlb σ κ φ πs u T t := by
  have hu := (consts_pos hσκ hφ hπs hk).1
  have h0 : max (tL σ κ φ πs u T) 0 = tL σ κ φ πs u T := max_eq_left (by linarith)
  have h1 : max (tL σ κ φ πs u T - t) 0 = tL σ κ φ πs u T - t := max_eq_left (by linarith)
  have h2 : -((T - tL σ κ φ πs u T) * a0 σ κ φ) = -(a0 σ κ φ * sStar σ κ φ πs u) := by
    unfold tL; ring
  have h3 : πs + ubar φ u * (1 - qq φ πs u) = kink φ πs := by
    have a := ubar_one_sub_qq (πs := πs) hφ hu
    have b := sub_kink (πs := πs) hφ
    linarith
  rw [h0, h1, h2, exp_sStar hσκ hφ hπs hk, h3]
  unfold piZlb
  ring_nf

/-- Cochrane (2023), Figure 20.3 in the continuous-time limit: **convergence of the inflation
path.** For `0 ≤ t ≤ T`, the selected discrete path with period `h = T/N`, read at the grid date
`⌊t/h⌋`, converges to the continuous-time path `piC` as `N → ∞`. -/
theorem path_tendsto {σ κ φ πs u T t : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) (hT : 0 < T) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Tendsto (fun N : ℕ => selPath σ κ φ πs u (T / N) N ⌊t / (T / N)⌋₊) atTop
      (𝓝 (piC σ κ φ πs u T t)) := by
  obtain ⟨hu, -, -, -, -, -, -⟩ := consts_pos hσκ hφ hπs hk
  have hev1 : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < N :=
    (eventually_gt_atTop 0).mono fun N hN => by exact_mod_cast hN
  have hnN : ∀ N : ℕ, (0 : ℝ) < N → ⌊t / (T / N)⌋₊ ≤ N := fun N hN => by
    refine Nat.floor_le_of_le ?_
    rw [div_le_iff₀ (div_pos hT hN)]
    calc t ≤ T := htT
      _ = N * (T / N) := by field_simp
  have hnh : Tendsto (fun N : ℕ => (⌊t / (T / N)⌋₊ : ℝ) * (T / N)) atTop (𝓝 t) := by
    have hh0 := tendsto_const_div_atTop_nhds_zero_nat T
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun N : ℕ => t - T / N)
      (h := fun _ => t) ?_ tendsto_const_nhds ?_ ?_
    · simpa using hh0.const_sub t
    · filter_upwards [hev1] with N hN
      have hhp : 0 < T / N := div_pos hT hN
      have := Nat.lt_floor_add_one (t / (T / N))
      rw [div_lt_iff₀ hhp, add_mul, one_mul] at this
      linarith
    · filter_upwards [hev1] with N hN
      have hhp : 0 < T / N := div_pos hT hN
      have := Nat.floor_le (div_nonneg ht0 hhp.le)
      rwa [le_div_iff₀ hhp] at this
  have hr := tendsto_logcc (σ := σ) (κ := κ) (φ := φ) |>.comp (tendsto_T_div hT)
  have hρ := tendsto_log1p (σ := σ) (κ := κ) |>.comp (tendsto_T_div hT)
  have hLh := liftoff_time_tendsto (u := u) hσκ hφ hπs hk hT
  have hexp : Continuous Real.exp := Real.continuous_exp
  -- the active part
  have hX : Tendsto (fun N : ℕ => AA σ κ φ πs u (T / N) (N - ⌊t / (T / N)⌋₊)) atTop
      (𝓝 (piAct σ κ φ πs u T t)) := by
    have hk' : Tendsto (fun N : ℕ => ((N - ⌊t / (T / N)⌋₊ : ℕ) : ℝ) * (T / N)) atTop
        (𝓝 (T - t)) := by
      refine (tendsto_const_nhds.sub hnh).congr' ?_
      filter_upwards [hev1] with N hN
      rw [Nat.cast_sub (hnN N hN), sub_mul]
      field_simp
    have he := (hexp.tendsto _).comp ((hk'.mul hr).neg)
    have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).sub he).const_mul (ubar φ u) |>.const_add πs
    have hval : piAct σ κ φ πs u T t =
        πs + ubar φ u * (1 - Real.exp (-((T - t) * a0 σ κ φ))) := by
      unfold piAct; ring_nf
    rw [hval]
    refine hlim.congr' ?_
    filter_upwards [hev1] with N hN
    have hhp : 0 < T / N := div_pos hT hN
    simp only [Function.comp, AA]
    rw [inv_pow_eq_exp (by linarith [cc_gt_one hσκ hφ hhp]) hhp]
  -- the zero-bound part
  set Lf := fun N : ℕ => liftIdx σ κ φ πs u (T / N) N
  have hY : Tendsto (fun N : ℕ => -u + (1 + σ * (T / N * κ)) ^ (Lf N - ⌊t / (T / N)⌋₊) *
      (AA σ κ φ πs u (T / N) (N - Lf N) + u)) atTop
      (𝓝 (-u + Real.exp (max (max (tL σ κ φ πs u T) 0 - t) 0 * (σ * κ)) *
        (πs + ubar φ u * (1 - Real.exp (-((T - max (tL σ κ φ πs u T) 0) * a0 σ κ φ))) +
          u))) := by
    have hm : Tendsto (fun N : ℕ => ((Lf N - ⌊t / (T / N)⌋₊ : ℕ) : ℝ) * (T / N)) atTop
        (𝓝 (max (max (tL σ κ φ πs u T) 0 - t) 0)) := by
      refine ((hLh.sub hnh).max tendsto_const_nhds).congr' ?_
      filter_upwards [hev1] with N hN
      rw [natSub_mul (div_pos hT hN).le]
    have hNL : Tendsto (fun N : ℕ => ((N - Lf N : ℕ) : ℝ) * (T / N)) atTop
        (𝓝 (T - max (tL σ κ φ πs u T) 0)) := by
      refine (tendsto_const_nhds.sub hLh).congr' ?_
      filter_upwards [hev1] with N hN
      have hLN := (liftIdx_spec (σ := σ) (κ := κ) (u := u) (h := T / N) hφ hπs N).1
      rw [Nat.cast_sub hLN, sub_mul]
      field_simp
    have hA := ((tendsto_const_nhds (x := (1 : ℝ))).sub ((hexp.tendsto _).comp
      ((hNL.mul hr).neg))).const_mul (ubar φ u) |>.const_add πs
    have hP := (hexp.tendsto _).comp (hm.mul hρ)
    have hlim := ((hP.mul (hA.add_const u)).const_add (-u))
    refine hlim.congr' ?_
    filter_upwards [hev1] with N hN
    have hhp : 0 < T / N := div_pos hT hN
    simp only [Function.comp, AA]
    rw [inv_pow_eq_exp (by linarith [cc_gt_one hσκ hφ hhp]) hhp,
      pow_eq_exp (by linarith [ah_pos hσκ hhp]) hhp]
  -- the structure of the selected path
  have hstruct : ∀ N : ℕ, (0 : ℝ) < N →
      (Lf N ≤ ⌊t / (T / N)⌋₊ → selPath σ κ φ πs u (T / N) N ⌊t / (T / N)⌋₊ =
        AA σ κ φ πs u (T / N) (N - ⌊t / (T / N)⌋₊)) ∧
      (⌊t / (T / N)⌋₊ ≤ Lf N → selPath σ κ φ πs u (T / N) N ⌊t / (T / N)⌋₊ =
        -u + (1 + σ * (T / N * κ)) ^ (Lf N - ⌊t / (T / N)⌋₊) *
          (AA σ κ φ πs u (T / N) (N - Lf N) + u)) := by
    intro N hN
    have hhp : 0 < T / N := div_pos hT hN
    have hrec := selPath_rec (u := u) (πs := πs) hσκ hφ hhp N
    have hNN := selPath_N σ κ φ πs u (T / N) N
    obtain ⟨hLN, hLpos, hzero⟩ := liftIdx_spec (σ := σ) (κ := κ) (u := u) (h := T / N) hφ hπs N
    replace hLN : Lf N ≤ N := hLN
    replace hLpos : 0 < rule φ πs (selPath σ κ φ πs u (T / N) N (Lf N)) := hLpos
    replace hzero : ∀ n, n < Lf N → rule φ πs (selPath σ κ φ πs u (T / N) N n) = 0 := hzero
    have hsel := sel_path hσκ hφ hπs hk hhp hNN hrec
    have hpL : selPath σ κ φ πs u (T / N) N (Lf N) = AA σ κ φ πs u (T / N) (N - Lf N) := by
      have h1 := (rate_pos_iff hσκ hφ hπs hk hhp hNN hrec hLN).mp hLpos
      have := (hsel (N - Lf N) (by omega)).1 h1
      rwa [show N - (N - Lf N) = Lf N by omega] at this
    constructor
    · intro hle
      have hpos := pos_of_ge hσκ hφ hπs hk hhp hNN hrec hle (hnN N hN) hLpos
      have h1 := (rate_pos_iff hσκ hφ hπs hk hhp hNN hrec (hnN N hN)).mp hpos
      have := (hsel (N - ⌊t / (T / N)⌋₊) (by omega)).1 h1
      rwa [show N - (N - ⌊t / (T / N)⌋₊) = ⌊t / (T / N)⌋₊ by have := hnN N hN; omega] at this
    · intro hle
      have := zlb_back hφ hrec hLN hzero (by linarith [ah_pos hσκ hhp])
        (Lf N - ⌊t / (T / N)⌋₊) (by omega)
      rw [show Lf N - (Lf N - ⌊t / (T / N)⌋₊) = ⌊t / (T / N)⌋₊ by omega, hpL] at this
      exact this
  rcases lt_trichotomy t (tL σ κ φ πs u T) with hlt | heq | hgt
  · -- before lift-off
    have hval : piC σ κ φ πs u T t = piZlb σ κ φ πs u T t := by
      simp [piC, htT, piG, not_le.mpr hlt]
    rw [hval, ← ylim_eq hσκ hφ hπs hk ht0 hlt.le]
    refine hY.congr' ?_
    have hε : 0 < (tL σ κ φ πs u T - t) / 2 := by linarith
    filter_upwards [liftoff_eps (u := u) hσκ hφ hπs hk hT hε, hev1] with N hE hN
    have hhp : 0 < T / N := div_pos hT hN
    have hzero := (hE _ (selPath_N σ κ φ πs u (T / N) N)
      (selPath_rec hσκ hφ hhp N) _ (hnN N hN)).1 (by
        have := Nat.floor_le (div_nonneg ht0 hhp.le)
        rw [le_div_iff₀ hhp] at this
        linarith)
    have hlt' : ⌊t / (T / N)⌋₊ ≤ Lf N := by
      by_contra hcon
      push Not at hcon
      have := pos_of_ge hσκ hφ hπs hk hhp (selPath_N σ κ φ πs u (T / N) N)
        (selPath_rec hσκ hφ hhp N) hcon.le (hnN N hN)
        (liftIdx_spec (σ := σ) (κ := κ) (u := u) (h := T / N) hφ hπs N).2.1
      linarith
    exact ((hstruct N hN).2 hlt').symm
  · -- at lift-off
    have hval : piC σ κ φ πs u T t = piZlb σ κ φ πs u T t := by
      have htT' : tL σ κ φ πs u T ≤ T := heq ▸ htT
      simp only [piC, heq, htT', ↓reduceIte, piG, le_rfl]
      rw [piAct_tL hσκ hφ hπs hk]
      unfold piZlb
      simp
    have hX' : Tendsto (fun N : ℕ => AA σ κ φ πs u (T / N) (N - ⌊t / (T / N)⌋₊)) atTop
        (𝓝 (piZlb σ κ φ πs u T t)) := by
      have : piZlb σ κ φ πs u T t = piAct σ κ φ πs u T t := by
        rw [heq, piAct_tL hσκ hφ hπs hk]
        unfold piZlb
        simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
        ring
      rw [this]
      exact hX
    have hY' := hY
    rw [ylim_eq hσκ hφ hπs hk ht0 heq.le] at hY'
    rw [hval]
    refine tendsto_of_or ?_ hX' hY'
    filter_upwards [hev1] with N hN
    rcases le_total (Lf N) ⌊t / (T / N)⌋₊ with hle | hle
    · exact Or.inl ((hstruct N hN).1 hle)
    · exact Or.inr ((hstruct N hN).2 hle)
  · -- after lift-off
    have hval : piC σ κ φ πs u T t = piAct σ κ φ πs u T t := by
      simp [piC, htT, piG, hgt.le]
    rw [hval]
    refine hX.congr' ?_
    have hε : 0 < (t - tL σ κ φ πs u T) / 2 := by linarith
    filter_upwards [liftoff_eps (u := u) hσκ hφ hπs hk hT hε, hev1,
      hnh.eventually (lt_mem_nhds (show tL σ κ φ πs u T + (t - tL σ κ φ πs u T) / 2 < t by
        linarith))] with N hE hN hgtN
    have hhp : 0 < T / N := div_pos hT hN
    have hpos := (hE _ (selPath_N σ κ φ πs u (T / N) N)
      (selPath_rec hσκ hφ hhp N) _ (hnN N hN)).2 hgtN.le
    have h1 := (rate_pos_iff hσκ hφ hπs hk hhp (selPath_N σ κ φ πs u (T / N) N)
      (selPath_rec hσκ hφ hhp N) (hnN N hN)).mp hpos
    have := (sel_path hσκ hφ hπs hk hhp (selPath_N σ κ φ πs u (T / N) N)
      (selPath_rec hσκ hφ hhp N) (N - ⌊t / (T / N)⌋₊) (by omega)).1 h1
    rw [show N - (N - ⌊t / (T / N)⌋₊) = ⌊t / (T / N)⌋₊ by have := hnN N hN; omega] at this
    exact this.symm

/-! ## Early versus delayed lift-off, and Figure 20.3 -/

/-- Cochrane (2023), §20.2.1 (Figure 20.3, survey E3) against §20.2.4, p. 479 (delayed
lift-off): **the two lift-offs genuinely differ.** In the continuous-time limit of Figure 20.3
the rate lifts off strictly before the end of the trap, `t_L < T`, for every calibration; under
delayed lift-off (`ForwardGuidance.delayI`, lift-off at any `L ≥ T`) the rate is zero until
`L`. On the nonempty interval `(max(t_L, 0), T)` the rule's rate is positive and the delayed
rate is zero. -/
theorem early_vs_delayed {σ κ φ πs u T : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    (hk : kink φ πs < -u) (hT : 0 < T) (u2 L : ℝ) (hL : T ≤ L) :
    tL σ κ φ πs u T < T ∧ (Set.Ioo (max (tL σ κ φ πs u T) 0) T).Nonempty ∧
      ∀ t ∈ Set.Ioo (max (tL σ κ φ πs u T) 0) T,
        0 < rule φ πs (piC σ κ φ πs u T t) ∧ ForwardGuidance.delayI u2 L t = 0 := by
  have htl := tL_lt (T := T) hσκ hφ hπs hk
  refine ⟨htl, Set.nonempty_Ioo.mpr (max_lt htl hT), fun t ht => ⟨?_, ?_⟩⟩
  · exact (ct_liftoff hσκ hφ hπs hk ht.2.le).mpr (lt_of_le_of_lt (le_max_left _ _) ht.1)
  · simp [ForwardGuidance.delayI, lt_of_lt_of_le ht.2 hL]

/-- Cochrane (2023), Figure 20.3, p. 473 (`σ = 1`, `κ = 1/2`, `φ = 2`, `π* = 2`, `u = −2`,
`T = 10`): the period-1 member of the family is the model of `ZLBRule`, with `c₁ = 4/3`,
`Λ = log 2`, `σκ(φ − 1) = 1/2`; it lifts off at date `8` (survey E3), while the continuous-time
limit lifts off at `t_L = 10 − 2 log 2 ∈ (8.6, 8.62)`. -/
theorem fig203_member :
    fmap 1 (1 * (1 / 2)) 2 2 (-2) = fmap 1 (1 / 2) 2 2 (-2) ∧ cc 1 (1 / 2) 2 1 = 4 / 3 ∧
      Lam 2 2 (-2) = Real.log 2 ∧ a0 1 (1 / 2) 2 = 1 / 2 ∧
      tL 1 (1 / 2) 2 2 (-2) 10 = 10 - 2 * Real.log 2 ∧
      (86 / 10 : ℝ) < 10 - 2 * Real.log 2 ∧ 10 - 2 * Real.log 2 < (862 / 100 : ℝ) ∧
      liftIdx 1 (1 / 2) 2 2 (-2) 1 10 = 8 := by
  have hσκ : (0 : ℝ) < 1 * (1 / 2) := by norm_num
  have hφ : (1 : ℝ) < 2 := by norm_num
  have hπs : (0 : ℝ) < 2 := by norm_num
  have hk : kink 2 2 < -(-2 : ℝ) := by rw [kink_fig203.1]; norm_num
  have hc : cc 1 (1 / 2) 2 1 = 4 / 3 := by unfold cc slopeR; norm_num
  have hL : Lam 2 2 (-2) = Real.log 2 := by
    unfold Lam qq
    rw [show (1 : ℝ) - 2 * (2 - 1) / (2 * -(-2)) = 2⁻¹ by norm_num, Real.log_inv, neg_neg]
  have ha : a0 1 (1 / 2) 2 = 1 / 2 := by unfold a0; norm_num
  have htl : tL 1 (1 / 2) 2 2 (-2) 10 = 10 - 2 * Real.log 2 := by
    unfold tL sStar; rw [hL, ha]; ring
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  -- the rate is positive at `n ≤ 10` iff `(10 − n) log(4/3) < log 2`
  have hrate : ∀ n, n ≤ 10 → (0 < rule 2 2 (selPath 1 (1 / 2) 2 2 (-2) 1 10 n) ↔
      ((10 - n : ℕ) : ℝ) * Real.log (4 / 3) < Real.log 2) := by
    intro n hn
    rw [rate_pos_iff hσκ hφ hπs hk one_pos (selPath_N _ _ _ _ _ _ 10)
      (selPath_rec hσκ hφ one_pos 10) hn, AA_gt_kink_iff hσκ hφ hπs hk one_pos, hc, hL]
  have hl43 : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have h8 : 0 < rule 2 2 (selPath 1 (1 / 2) 2 2 (-2) 1 10 8) := by
    rw [hrate 8 (by norm_num)]
    norm_num
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_lt_log (by positivity) (by norm_num)
  have hlt : ∀ n, n < 8 → ¬ 0 < rule 2 2 (selPath 1 (1 / 2) 2 2 (-2) 1 10 n) := by
    intro n hn
    rw [hrate n (by omega), not_lt]
    have h3 : (3 : ℝ) ≤ ((10 - n : ℕ) : ℝ) := by
      have : 3 ≤ 10 - n := by omega
      exact_mod_cast this
    have h64 : Real.log 2 < 3 * Real.log (4 / 3) := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_lt_log (by norm_num) (by norm_num)
    nlinarith
  refine ⟨by norm_num, hc, hL, ha, htl, by linarith, by linarith, ?_⟩
  apply le_antisymm (Nat.sInf_le h8)
  refine le_csInf ⟨8, h8⟩ fun n hn => ?_
  by_contra hcon
  push Not at hcon
  exact hlt n hcon hn

end Cochrane.ZeroBound.TidyR6LiftoffLimit
