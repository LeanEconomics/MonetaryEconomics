/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.IRuleBasic

/-!
# The forward-integrated form of the optimal interest-rate rule

Woodford (2003), *Interest and Prices*, Chapter 8, §3.1, pp. 588–591, and Appendix G.5,
pp. 723–724 (proof of Proposition 8.6).

## Main results

* **(3.10)–(3.11).** `rule_iff_g14`: the rule (3.7) is `(1 − λ₁L)(1 − λ₂L)(i_t − i*) = q_t` with
  `q_t = φ_ππ_t + (φ_x/4)Δx_t` and `0 < λ₁ < 1 < λ₂` the roots of fn. 35 (`IRuleBasic.lam1`,
  `IRuleBasic.lam2`). In deviations from long-run values (`î = i − ī`, `q̂ = q − φ_ππ̄`) the
  same holds exactly when `λ_i(ī − i*) = −βπ̄` (`steady_state_rule`, `g14_hat_iff`).
* **Proposition 8.6** (`prop_8_6`): for bounded adapted processes (with pre-sample values), (3.10)
  holds at all dates iff (3.12)
  `(1 − λ₁L)î_{t−1} = −λ₂⁻¹ ∑_{j ≥ 0} λ₂^{−j} E_t q̂_{t+j}` does — under `λ₂ > 1` alone (the book
  also assumes `0 < λ₁ < 1`, which is not needed). The forward iteration of the book is made
  explicit in `prop_8_6_remainder`: the remainder `λ₂^{−n} E_t[(1 − λ₁L)î_{t+n−1}] → 0`.
  `g15_hat_iff`: the constant term of (3.12) vanishes when `λ_i(ī − i*) = −βπ̄`.
* **(3.13), the target criterion** (`rule_iff_crit313`): for bounded adapted `π, x, i`, the rule
  holds at all dates iff
  `F_t(π) + (φ_x/4)F_t(x) = (θ_x/4)x_{t−1} − θ_i(i_{t−1} − i*) − θ_Δ Δi_{t−1}` holds at all dates,
  with `F_t(z) = ∑ α_j E_t z_{t+j}`, `α_j = (1 − λ₂⁻¹)λ₂^{−j}` (weights
  summing to one, `alphaW_sum`; mean horizon `(λ₂ − 1)⁻¹`, `alphaW_mean`),
  `φ_x = θ_x = 4(1 − λ₂⁻¹)λ_x/κ`, `θ_i = λ₂(1−λ₁)(1−λ₂⁻¹)λ_i/(κσ) = λ_i/β`,
  `θ_Δ = λ₁λ₂(1−λ₂⁻¹)λ_i/(κσ)` (`thetaI_eq`, `coef313_pos`). There is no constant term.
* **Numbers, pp. 590–591** (`p590_numbers`): `λ₂⁻¹ ∈ (.676, .677)`, mean horizon
  `∈ (2.08, 2.10)`, `θ_i ∈ (.238, .239)`, `θ_Δ ∈ (.514, .515)` all agree with the book; but
  `φ_x = θ_x ∈ (.164, .165)`, not the printed `.15` (survey S2, confirmed: `p591_phiX_not_015`),
  and no single `λ_x` reproduces both printed values `φ_x = .33` (p. 586) and `.15` (p. 591)
  (`printed_phiX_inconsistent`).
* **The limit `λ_i → 0`, p. 591.** `θ_i, θ_Δ → 0` (`tendsto_thetaI`, `tendsto_thetaD`) while
  `φ_x, θ_x, α_j` do not depend on `λ_i`; the limiting criterion is equivalent, for bounded
  adapted processes, to the Chapter 7 criterion (Ch. 8 (2.5), p. 561)
  `π_t + (λ_x/κ)(x_t − x_{t−1}) = 0` (`crit_limit_iff_25`), via the lemma behind
  (1.30) ⇔ (1.31) proved here (`forwardSeries_eq_zero_iff`); a fixed bounded plan satisfying (3.13)
  along a sequence `λ_i → 0` satisfies (2.5) (`limit_plan_satisfies_25`).
-/

namespace Woodford.OptimalPolicyRules.IRuleForwardIntegrated

open Filter Topology
open Woodford.OptimalPolicyRules.IRuleBasic

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Proposition 8.6 -/

/-- Woodford (2003), (3.10) and (G.14), pp. 588 and 723: `(1 − λ₁L)(1 − λ₂L)î_t = q̂_t`, i.e.
`(1 − λ₁L)î_t − λ₂(1 − λ₁L)î_{t−1} = q̂_t`, with pre-sample values `î_{−1} = h₁`, `î_{−2} = h₂`. -/
def G14 (l1 l2 : ℝ) (ih q : ℕ → Ω → ℝ) (h1 h2 : ℝ) (t : ℕ) : Prop :=
  ih t - l1 • lag h1 ih t - l2 • (lag h1 ih t - l1 • lag h2 (lag h1 ih) t) = q t

/-- Woodford (2003), (3.12), p. 588: the lagged quasi-difference `(1 − λ₁L)î_{t−1}`. -/
def wLag (l1 : ℝ) (ih : ℕ → Ω → ℝ) (h1 h2 : ℝ) : ℕ → Ω → ℝ :=
  fun t => lag h1 ih t - l1 • lag h2 (lag h1 ih) t

/-- Woodford (2003), (3.12) and (G.15), pp. 588 and 723:
`(1 − λ₁L)î_{t−1} = −λ₂⁻¹ E_t[(1 − λ₂⁻¹L⁻¹)⁻¹ q̂_t] = −λ₂⁻¹ ∑_{j ≥ 0} λ₂^{−j} E_t q̂_{t+j}`. -/
def G15 (l1 l2 : ℝ) (ih q : ℕ → Ω → ℝ) (h1 h2 : ℝ) (t : ℕ) : Prop :=
  wLag l1 ih h1 h2 t = (-l2⁻¹) • 𝔼.forwardSeries l2⁻¹ q t

/-- Woodford (2003), App. G.5, p. 723 (tool): the forward series is linear in the forcing. -/
theorem forwardSeries_smul (a k : ℝ) (q : ℕ → Ω → ℝ) (t : ℕ) :
    𝔼.forwardSeries a (fun s => k • q s) t = k • 𝔼.forwardSeries a q t := by
  funext ω
  simp only [ExpectationSystem.forwardSeries, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- Woodford (2003), App. G.5, p. 723 (tool): `(1 − λ₁L)î_t` at date `t` is the lagged
quasi-difference at `t + 1`. -/
theorem wLag_succ (l1 : ℝ) (ih : ℕ → Ω → ℝ) (h1 h2 : ℝ) (t : ℕ) :
    wLag l1 ih h1 h2 (t + 1) = ih t - l1 • lag h1 ih t := rfl

/-- Woodford (2003), App. G.5, p. 723 (tool): `(1 − λ₁L)î_t` is known at date `t`. -/
theorem wLag_known {l1 : ℝ} {ih : ℕ → Ω → ℝ} {h1 h2 : ℝ} (hih : 𝔼.Adapted ih) (t : ℕ) :
    𝔼.E t (wLag l1 ih h1 h2 (t + 1)) = wLag l1 ih h1 h2 (t + 1) := by
  rw [wLag_succ, map_sub, map_smul, hih t, lag_known 𝔼 h1 hih t]

/-- Woodford (2003), App. G.5, p. 723 (tool): the lagged quasi-difference of a bounded process is
bounded. -/
theorem wLag_bounded (l1 : ℝ) {ih : ℕ → Ω → ℝ} (h1 h2 : ℝ) (hb : BoundedProc ih) :
    BoundedProc (wLag l1 ih h1 h2) := by
  obtain ⟨M, hM⟩ := hb
  have hl : ∀ t ω, |lag h1 ih t ω| ≤ max M |h1| := by
    intro t ω
    cases t with
    | zero => exact le_max_right _ _
    | succ t => exact (hM t ω).trans (le_max_left _ _)
  have hl2 : ∀ t ω, |lag h2 (lag h1 ih) t ω| ≤ max (max M |h1|) |h2| := by
    intro t ω
    cases t with
    | zero => exact le_max_right _ _
    | succ t => exact (hl t ω).trans (le_max_left _ _)
  refine ⟨max M |h1| + |l1| * max (max M |h1|) |h2|, fun t ω => ?_⟩
  simp only [wLag, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_sub _ _).trans (add_le_add (hl t ω) ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hl2 t ω) (abs_nonneg _)

/-- Woodford (2003), App. G.5, p. 723: (G.14) at date `t` says that the lagged quasi-difference
`v_t = (1 − λ₁L)î_{t−1}` solves `v_t = λ₂⁻¹ E_t v_{t+1} − λ₂⁻¹ q̂_t` (for adapted `î`). -/
theorem g14_iff_solves {l1 l2 : ℝ} (hl2 : l2 ≠ 0) {ih q : ℕ → Ω → ℝ} {h1 h2 : ℝ}
    (hih : 𝔼.Adapted ih) (t : ℕ) :
    G14 l1 l2 ih q h1 h2 t ↔ wLag l1 ih h1 h2 t =
      l2⁻¹ • 𝔼.E t (wLag l1 ih h1 h2 (t + 1)) + (-l2⁻¹) • q t := by
  rw [wLag_known 𝔼 hih t, wLag_succ]
  unfold G14 wLag
  constructor
  · intro h
    rw [← h]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · intro h
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    field_simp at this
    linarith

/-- **Woodford (2003), Proposition 8.6, p. 588, and App. G.5, pp. 723–724.** Let `λ₂ > 1`. Two
bounded adapted processes `î, q̂` (with pre-sample values `î_{−1}, î_{−2}`) satisfy (3.10)
`(1 − λ₁L)(1 − λ₂L)î_t = q̂_t` for all `t ≥ 0` if and only if they satisfy (3.12)
`(1 − λ₁L)î_{t−1} = −λ₂⁻¹ ∑_j λ₂^{−j} E_t q̂_{t+j}` for all `t ≥ 0`. (Only `λ₂ > 1` is used; the
book's `0 < λ₁ < 1` is not needed.) -/
theorem prop_8_6 {l1 l2 : ℝ} (hl2 : 1 < l2) {ih q : ℕ → Ω → ℝ} {h1 h2 : ℝ}
    (hih : 𝔼.Adapted ih) (hqa : 𝔼.Adapted q) (hihb : BoundedProc ih) (hqb : BoundedProc q) :
    (∀ t, G14 l1 l2 ih q h1 h2 t) ↔ (∀ t, G15 𝔼 l1 l2 ih q h1 h2 t) := by
  have hl0 : l2 ≠ 0 := by linarith
  have ha : |l2⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < l2)]
    exact inv_lt_one_of_one_lt₀ hl2
  obtain ⟨Mq, hMq⟩ := hqb
  set u : ℕ → Ω → ℝ := fun s => (-l2⁻¹) • q s with hu
  have hub : ∀ t ω, |u t ω| ≤ |l2⁻¹| * Mq := by
    intro t ω
    simp only [hu, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hMq t ω) (abs_nonneg _)
  have hua : 𝔼.Adapted u := by
    intro t
    simp only [hu, map_smul, hqa t]
  have hfs : ∀ t, 𝔼.forwardSeries l2⁻¹ u t = (-l2⁻¹) • 𝔼.forwardSeries l2⁻¹ q t :=
    fun t => forwardSeries_smul 𝔼 l2⁻¹ (-l2⁻¹) q t
  constructor
  · intro h t
    have hs : ForwardSolution.Solves 𝔼 l2⁻¹ u (wLag l1 ih h1 h2) :=
      fun s => (g14_iff_solves 𝔼 hl0 hih s).mp (h s)
    have e := ForwardSolution.eq_forwardSeries_abs 𝔼 ha hub hua hs
      (wLag_bounded l1 h1 h2 hihb)
    unfold G15
    rw [e, hfs]
  · intro h t
    have e : wLag l1 ih h1 h2 = 𝔼.forwardSeries l2⁻¹ u := by
      funext s
      rw [hfs]
      exact h s
    have hs := ForwardSolution.forwardSeries_solves_abs 𝔼 ha hub hua
    rw [← e] at hs
    exact (g14_iff_solves 𝔼 hl0 hih t).mpr (hs t)

/-- **Woodford (2003), App. G.5, p. 723 — the forward iteration with its remainder.** If (3.10)
holds at all dates, then for every horizon `n`,
`(1 − λ₁L)î_{t−1} = −λ₂⁻¹ ∑_{j<n} λ₂^{−j} E_t q̂_{t+j} + λ₂^{−n} E_t[(1 − λ₁L)î_{t+n−1}]`,
and the remainder tends to zero because `î` is bounded and `λ₂ > 1`. -/
theorem prop_8_6_remainder {l1 l2 : ℝ} (hl2 : 1 < l2) {ih q : ℕ → Ω → ℝ} {h1 h2 : ℝ}
    (hih : 𝔼.Adapted ih) (hqa : 𝔼.Adapted q) (hihb : BoundedProc ih)
    (h : ∀ t, G14 l1 l2 ih q h1 h2 t) (t : ℕ) (ω : Ω) :
    (∀ n, wLag l1 ih h1 h2 t ω = -l2⁻¹ * ∑ j ∈ Finset.range n, l2⁻¹ ^ j * 𝔼.E t (q (t + j)) ω
      + l2⁻¹ ^ n * 𝔼.E t (wLag l1 ih h1 h2 (t + n)) ω) ∧
      Tendsto (fun n => l2⁻¹ ^ n * 𝔼.E t (wLag l1 ih h1 h2 (t + n)) ω) atTop (𝓝 0) := by
  have hl0 : l2 ≠ 0 := by linarith
  have hpos : 0 < l2⁻¹ := inv_pos.mpr (by linarith)
  have ha1 : l2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl2
  set u : ℕ → Ω → ℝ := fun s => (-l2⁻¹) • q s with hu
  have hua : 𝔼.Adapted u := by
    intro t
    simp only [hu, map_smul, hqa t]
  have hs : ForwardSolution.Solves 𝔼 l2⁻¹ u (wLag l1 ih h1 h2) :=
    fun s => (g14_iff_solves 𝔼 hl0 hih s).mp (h s)
  refine ⟨fun n => ?_, ?_⟩
  · have e := congrFun (ForwardSolution.iterate_A15 𝔼 hua hs t n) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, hu, map_smul] at e
    rw [e, Finset.mul_sum]
    have : ∀ j ∈ Finset.range n, l2⁻¹ ^ j * (-l2⁻¹ * 𝔼.E t (q (t + j)) ω) =
        -l2⁻¹ * (l2⁻¹ ^ j * 𝔼.E t (q (t + j)) ω) := fun j _ => by ring
    rw [Finset.sum_congr rfl this]
    ring
  · obtain ⟨M, hM⟩ := wLag_bounded l1 h1 h2 hihb
    refine squeeze_zero_norm (a := fun n => l2⁻¹ ^ n * M) (fun n => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM (t + n)) t ω) (pow_nonneg hpos.le n)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le ha1).mul_const M

/-! ### (3.10)–(3.11): the rule as `(1 − λ₁L)(1 − λ₂L)î_t = q̂_t` -/

/-- Woodford (2003), (3.11), p. 588: `q_t = φ_ππ_t + (φ_x/4)Δx_t`. -/
noncomputable def qProc (c : Calib) (xm1 : ℝ) (π x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => phiPi c.σ c.κ c.li • π t + (phiX c.σ c.lx c.li / 4) • (x t - lag xm1 x t)

/-- Woodford (2003), (3.10), p. 588: the interest rate in deviation from a constant. -/
def idev (k : ℝ) (i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => i t - fun _ => k

/-- Woodford (2003), (3.10), p. 588: the root `λ₁` of the optimal rule. -/
noncomputable def L1c (c : Calib) : ℝ := lam1 (rho1 c.β c.σ c.κ) (rho2 c.β)

/-- Woodford (2003), (3.10), p. 588: the root `λ₂` of the optimal rule. -/
noncomputable def L2c (c : Calib) : ℝ := lam2 (rho1 c.β c.σ c.κ) (rho2 c.β)

/-- Woodford (2003), (3.10), p. 588: `0 < λ₁ < 1 < λ₂`, `λ₁ + λ₂ = ρ₁ + ρ₂`, `λ₁λ₂ = ρ₂`. -/
theorem L_props (c : Calib) (hc : c.Adm) :
    0 < L1c c ∧ L1c c < 1 ∧ 1 < L2c c ∧ L1c c + L2c c = rho1 c.β c.σ c.κ + rho2 c.β ∧
      L1c c * L2c c = rho2 c.β := by
  obtain ⟨hβ0, hβ1, hσ, hκ, hlx, hli⟩ := hc
  obtain ⟨h1, h2, -, -⟩ := coef_signs hβ0 hβ1 hσ hκ hlx hli
  obtain ⟨r0, r1, r2⟩ := fn35_roots h1 (by linarith : (0 : ℝ) < rho2 c.β)
  obtain ⟨hs, hp, -⟩ := lam_factor (r2 := rho2 c.β) h1
  exact ⟨r0, r1, r2, hs, hp⟩

/-- Woodford (2003), (3.10), p. 588 (tool): lags of the deviation. -/
theorem lag_idev (k h : ℝ) (i : ℕ → Ω → ℝ) (t : ℕ) :
    lag (h - k) (idev k i) t = lag h i t - fun _ => k := by
  cases t with
  | zero => rfl
  | succ t => rfl

/-- Woodford (2003), (3.10), p. 588 (tool): second lags of the deviation. -/
theorem lag_lag_idev (k h1 h2 : ℝ) (i : ℕ → Ω → ℝ) (t : ℕ) :
    lag (h2 - k) (lag (h1 - k) (idev k i)) t = lag h2 (lag h1 i) t - fun _ => k := by
  cases t with
  | zero => rfl
  | succ t => exact lag_idev k h1 i t

/-- **Woodford (2003), (3.10)–(3.11), p. 588.** The rule (3.7) holds at date `t` iff
`(1 − λ₁L)(1 − λ₂L)(i_t − i*) = q_t` (with the history `i_{−1}, i_{−2}`), where
`(1 − λ₁L)(1 − λ₂L) = 1 − (ρ₁ + ρ₂)L + ρ₂L²`. -/
theorem rule_iff_g14 (c : Calib) (hc : c.Adm) (xm1 im1 im2 : ℝ) (π x i : ℕ → Ω → ℝ) (t : ℕ) :
    Rule c xm1 im1 im2 π x i t ↔ G14 (L1c c) (L2c c) (idev c.istar i) (qProc c xm1 π x)
      (im1 - c.istar) (im2 - c.istar) t := by
  obtain ⟨-, -, -, hs, hp⟩ := L_props c hc
  unfold Rule G14
  rw [lag_idev, lag_lag_idev, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [idev, qProc, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    linear_combination h - (lag im1 i t ω - c.istar) * hs
      + (lag im2 (lag im1 i) t ω - c.istar) * hp
  · intro h
    linear_combination h + (lag im1 i t ω - c.istar) * hs
      - (lag im2 (lag im1 i) t ω - c.istar) * hp

/-- **Woodford (2003), (3.10), p. 588 (the long-run values).** A constant plan `(π̄, x̄, ī)`
satisfies the rule iff `λ_i(ī − i*) = −βπ̄` (equivalently `(1 − ρ₁)(ī − i*) = φ_ππ̄`). -/
theorem steady_state_rule (c : Calib) (hc : c.Adm) (pbar xbar ibar : ℝ) :
    ibar = (1 - rho1 c.β c.σ c.κ) * c.istar + rho1 c.β c.σ c.κ * ibar
        + rho2 c.β * (ibar - ibar) + phiPi c.σ c.κ c.li * pbar
        + phiX c.σ c.lx c.li / 4 * (xbar - xbar) ↔ c.li * (ibar - c.istar) = -(c.β * pbar) := by
  obtain ⟨hβ0, -, hσ, hκ, -, hli⟩ := hc
  unfold rho1 phiPi
  have hk : c.κ * c.σ ≠ 0 := mul_ne_zero hκ.ne' hσ.ne'
  constructor
  · intro h
    field_simp at h
    have : c.κ * c.σ * (c.li * (ibar - c.istar) + c.β * pbar) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hk
    · linarith
  · intro h
    have e : ibar = c.istar - c.β * pbar / c.li := by
      field_simp
      linarith
    rw [e]
    field_simp
    ring

/-- **Woodford (2003), (3.10), p. 588: deviations from long-run values.** If
`λ_i(ī − i*) = −βπ̄`, then `(1 − λ₁L)(1 − λ₂L)(i_t − ī) = q_t − φ_ππ̄` iff
`(1 − λ₁L)(1 − λ₂L)(i_t − i*) = q_t`: the constant terms cancel. -/
theorem g14_hat_iff (c : Calib) (hc : c.Adm) {pbar ibar : ℝ}
    (hss : c.li * (ibar - c.istar) = -(c.β * pbar)) (xm1 im1 im2 : ℝ) (π x i : ℕ → Ω → ℝ)
    (t : ℕ) :
    G14 (L1c c) (L2c c) (idev ibar i) (fun s => qProc c xm1 π x s - fun _ =>
        phiPi c.σ c.κ c.li * pbar) (im1 - ibar) (im2 - ibar) t ↔
      G14 (L1c c) (L2c c) (idev c.istar i) (qProc c xm1 π x) (im1 - c.istar)
        (im2 - c.istar) t := by
  obtain ⟨-, -, -, hs, hp⟩ := L_props c hc
  obtain ⟨hβ0, -, hσ, hκ, -, hli⟩ := hc
  have key : (1 - L1c c) * (1 - L2c c) * (ibar - c.istar) = phiPi c.σ c.κ c.li * pbar := by
    have e : (1 - L1c c) * (1 - L2c c) = 1 - rho1 c.β c.σ c.κ := by
      linear_combination (-1 : ℝ) * hs + hp
    rw [e]
    unfold rho1 phiPi
    field_simp
    linear_combination (-(c.κ * c.σ)) * hss
  unfold G14
  rw [lag_idev, lag_lag_idev, lag_idev, lag_lag_idev, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [idev, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    linear_combination h + key
  · intro h
    linear_combination h - key

/-! ### (3.12)–(3.13): the target criterion -/

/-- Woodford (2003), App. G.5 (tool): the forward series of a process minus a constant,
`∑ aʲ E_t(q_{t+j} − k) = ∑ aʲ E_t q_{t+j} − k/(1 − a)`. -/
theorem forwardSeries_sub_const {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {q : ℕ → Ω → ℝ} {M : ℝ}
    (hq : ∀ t ω, |q t ω| ≤ M) (k : ℝ) (t : ℕ) (ω : Ω) :
    𝔼.forwardSeries a (fun s => q s - fun _ => k) t ω =
      𝔼.forwardSeries a q t ω - k / (1 - a) := by
  have ha : |a| < 1 := by rwa [abs_of_nonneg ha0]
  simp only [ExpectationSystem.forwardSeries, map_sub, 𝔼.const, Pi.sub_apply, mul_sub]
  rw [Summable.tsum_sub (ForwardSolution.summable_A16 𝔼 ha hq t ω)
    ((summable_geometric_of_lt_one ha0 ha1).mul_right k), tsum_mul_right,
    tsum_geometric_of_lt_one ha0 ha1, div_eq_inv_mul]

/-- **Woodford (2003), (3.12), p. 588 (the constant term vanishes).** If `λ_i(ī − i*) = −βπ̄`,
then (3.12) in deviations from long-run values,
`(1 − λ₁L)(i_{t−1} − ī) = −λ₂⁻¹ ∑ λ₂^{−j} E_t(q_{t+j} − φ_ππ̄)`, holds iff
`(1 − λ₁L)(i_{t−1} − i*) = −λ₂⁻¹ ∑ λ₂^{−j} E_t q_{t+j}` does. -/
theorem g15_hat_iff (c : Calib) (hc : c.Adm) {pbar ibar : ℝ}
    (hss : c.li * (ibar - c.istar) = -(c.β * pbar)) {q : ℕ → Ω → ℝ} {M : ℝ}
    (hq : ∀ t ω, |q t ω| ≤ M) (im1 im2 : ℝ) (i : ℕ → Ω → ℝ) (t : ℕ) :
    G15 𝔼 (L1c c) (L2c c) (idev ibar i) (fun s => q s - fun _ => phiPi c.σ c.κ c.li * pbar)
        (im1 - ibar) (im2 - ibar) t ↔
      G15 𝔼 (L1c c) (L2c c) (idev c.istar i) q (im1 - c.istar) (im2 - c.istar) t := by
  obtain ⟨-, -, hL2, hs, hp⟩ := L_props c hc
  obtain ⟨hβ0, -, hσ, hκ, -, hli⟩ := hc
  have hL0 : L2c c ≠ 0 := by linarith
  have ha0 : 0 ≤ (L2c c)⁻¹ := inv_nonneg.mpr (by linarith)
  have ha1 : (L2c c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL2
  have h1a : 1 - (L2c c)⁻¹ ≠ 0 := by linarith
  have hL1 : L2c c - 1 ≠ 0 := by linarith
  have key : (1 - L1c c) * (1 - L2c c) * (ibar - c.istar) = phiPi c.σ c.κ c.li * pbar := by
    have e : (1 - L1c c) * (1 - L2c c) = 1 - rho1 c.β c.σ c.κ := by
      linear_combination (-1 : ℝ) * hs + hp
    rw [e]
    unfold rho1 phiPi
    field_simp
    linear_combination (-(c.κ * c.σ)) * hss
  unfold G15 wLag
  rw [lag_idev, lag_lag_idev, lag_idev, lag_lag_idev, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [forwardSeries_sub_const 𝔼 ha0 ha1 hq]
  have key2 : (1 - L1c c) * (ibar - c.istar) =
      -((L2c c)⁻¹ * (phiPi c.σ c.κ c.li * pbar / (1 - (L2c c)⁻¹))) := by
    rw [← key]
    field_simp
    ring
  constructor
  · intro h
    linear_combination h + key2
  · intro h
    linear_combination h - key2

/-- Woodford (2003), p. 590: the weights `α_j = (1 − λ₂⁻¹)λ₂^{−j}` of the conditional forecasts. -/
noncomputable def alphaW (l2 : ℝ) (j : ℕ) : ℝ := (1 - l2⁻¹) * l2⁻¹ ^ j

/-- Woodford (2003), p. 589: the conditional forecast `F_t(z) = ∑_{j ≥ 0} α_j E_t z_{t+j}`. -/
noncomputable def Fz (l2 : ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, alphaW l2 j * 𝔼.E t (z (t + j)) ω

/-- Woodford (2003), p. 590: `θ_x = 4(1 − λ₂⁻¹)λ_x/κ`. -/
noncomputable def thetaX (c : Calib) : ℝ := 4 * (1 - (L2c c)⁻¹) * c.lx / c.κ

/-- Woodford (2003), p. 590: the weight `φ_x` on the output-gap forecast in (3.13); the book's
formula is `φ_x = θ_x`. -/
noncomputable def phiX313 (c : Calib) : ℝ := 4 * (1 - (L2c c)⁻¹) * c.lx / c.κ

/-- Woodford (2003), p. 590: `θ_i = λ₂(1 − λ₁)(1 − λ₂⁻¹)λ_i/(κσ)`. -/
noncomputable def thetaI (c : Calib) : ℝ :=
  L2c c * (1 - L1c c) * (1 - (L2c c)⁻¹) * c.li / (c.κ * c.σ)

/-- Woodford (2003), p. 590: `θ_Δ = λ₁λ₂(1 − λ₂⁻¹)λ_i/(κσ)`. -/
noncomputable def thetaD (c : Calib) : ℝ :=
  L1c c * L2c c * (1 - (L2c c)⁻¹) * c.li / (c.κ * c.σ)

/-- Woodford (2003), (3.13), p. 589: the target criterion
`F_t(π) + (φ_x/4)F_t(x) = (θ_x/4)x_{t−1} − θ_i(i_{t−1} − i*) − θ_Δ(i_{t−1} − i_{t−2})`. -/
def Crit313 (c : Calib) (xm1 im1 im2 : ℝ) (π x i : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  Fz 𝔼 (L2c c) π t + (phiX313 c / 4) • Fz 𝔼 (L2c c) x t =
    (thetaX c / 4) • lag xm1 x t - thetaI c • (lag im1 i t - fun _ => c.istar)
      - thetaD c • (lag im1 i t - lag im2 (lag im1 i) t)

/-- Woodford (2003), p. 590: `φ_x = θ_x` in (3.13). -/
theorem phiX313_eq_thetaX (c : Calib) : phiX313 c = thetaX c := rfl

/-- Woodford (2003), p. 589: `F_t(z) = (1 − λ₂⁻¹) ∑ λ₂^{−j} E_t z_{t+j}`. -/
theorem Fz_eq (l2 : ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Fz 𝔼 l2 z t ω = (1 - l2⁻¹) * 𝔼.forwardSeries l2⁻¹ z t ω := by
  simp only [Fz, alphaW, ExpectationSystem.forwardSeries]
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- **Woodford (2003), p. 589: the weights sum to one.** -/
theorem alphaW_sum {l2 : ℝ} (hl2 : 1 < l2) : ∑' j, alphaW l2 j = 1 := by
  have h0 : 0 ≤ l2⁻¹ := inv_nonneg.mpr (by linarith)
  have h1 : l2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl2
  simp only [alphaW]
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  have : 1 - l2⁻¹ ≠ 0 := by linarith
  exact mul_inv_cancel₀ this

/-- **Woodford (2003), p. 590: the weights are positive and decline exponentially.** -/
theorem alphaW_pos {l2 : ℝ} (hl2 : 1 < l2) (j : ℕ) :
    0 < alphaW l2 j ∧ alphaW l2 (j + 1) = l2⁻¹ * alphaW l2 j := by
  have h0 : 0 < l2⁻¹ := inv_pos.mpr (by linarith)
  have h1 : l2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl2
  refine ⟨mul_pos (by linarith) (pow_pos h0 j), ?_⟩
  simp only [alphaW, pow_succ]
  ring

/-- **Woodford (2003), p. 590: the mean forecast horizon** `∑ α_j j = (λ₂ − 1)⁻¹`. -/
theorem alphaW_mean {l2 : ℝ} (hl2 : 1 < l2) : ∑' j : ℕ, alphaW l2 j * j = (l2 - 1)⁻¹ := by
  have h0 : 0 ≤ l2⁻¹ := inv_nonneg.mpr (by linarith)
  have h1 : l2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl2
  have hn : ‖l2⁻¹‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have e : ∀ j : ℕ, alphaW l2 j * j = (1 - l2⁻¹) * ((j : ℝ) * l2⁻¹ ^ j) := fun j => by
    simp only [alphaW]; ring
  rw [tsum_congr e, tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hn]
  have hl0 : l2 ≠ 0 := by linarith
  have hl1 : l2 - 1 ≠ 0 := by linarith
  have : 1 - l2⁻¹ ≠ 0 := by linarith
  field_simp

/-- **Woodford (2003), p. 590: the coefficients of (3.13) are positive**, and
`θ_i = λ_i/β` (since `λ₂(1 − λ₂⁻¹)(1 − λ₁) = −(1 − λ₁)(1 − λ₂) = κσ/β`). -/
theorem coef313_pos (c : Calib) (hc : c.Adm) :
    0 < phiX313 c ∧ 0 < thetaX c ∧ 0 < thetaI c ∧ 0 < thetaD c := by
  obtain ⟨h1, h2, h3, -, -⟩ := L_props c hc
  obtain ⟨-, -, hσ, hκ, hlx, hli⟩ := hc
  have ha : 0 < 1 - (L2c c)⁻¹ := by linarith [inv_lt_one_of_one_lt₀ h3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold phiX313; positivity
  · unfold thetaX; positivity
  · unfold thetaI
    have : 0 < 1 - L1c c := by linarith
    have : 0 < L2c c := by linarith
    positivity
  · unfold thetaD
    have : 0 < L2c c := by linarith
    positivity

/-- **Woodford (2003), p. 590: `θ_i = λ_i/β`** (a closed form the book does not state). -/
theorem thetaI_eq (c : Calib) (hc : c.Adm) : thetaI c = c.li / c.β := by
  have hL2 : L2c c ≠ 0 := by
    have := (L_props c hc).2.2.1
    linarith
  obtain ⟨hβ0, -, hσ, hκ, -, -⟩ := hc
  have hm := (lam_model hβ0 hσ hκ).2.2
  have e : L2c c * (1 - L1c c) * (1 - (L2c c)⁻¹) = c.κ * c.σ / c.β := by
    have : L2c c * (1 - L1c c) * (1 - (L2c c)⁻¹) = -((1 - L1c c) * (1 - L2c c)) := by
      field_simp
      ring
    rw [this]
    unfold L1c L2c
    rw [hm]
    ring
  unfold thetaI
  rw [e]
  field_simp

/-- Woodford (2003), App. G.5 (tool): the forward series is additive for bounded processes. -/
theorem forwardSeries_lin {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f g : ℕ → Ω → ℝ} {Mf Mg : ℝ}
    (hf : ∀ t ω, |f t ω| ≤ Mf) (hg : ∀ t ω, |g t ω| ≤ Mg) (p r : ℝ) (t : ℕ) (ω : Ω) :
    𝔼.forwardSeries a (fun s => p • f s + r • g s) t ω =
      p * 𝔼.forwardSeries a f t ω + r * 𝔼.forwardSeries a g t ω := by
  have ha : |a| < 1 := by rwa [abs_of_nonneg ha0]
  simp only [ExpectationSystem.forwardSeries, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add
    ((ForwardSolution.summable_A16 𝔼 ha hf t ω).mul_left p)
    ((ForwardSolution.summable_A16 𝔼 ha hg t ω).mul_left r)]
  exact tsum_congr fun j => by ring

/-- Woodford (2003), p. 590 (the computation behind (3.13)): for bounded `x` with `x_{t−1}` known,
`∑ aʲ E_t Δx_{t+j} = (1 − a) ∑ aʲ E_t x_{t+j} − x_{t−1}`. -/
theorem forwardSeries_diff {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (hxa : 𝔼.Adapted x) (xm1 : ℝ) (t : ℕ) (ω : Ω) :
    𝔼.forwardSeries a (fun s => x s - lag xm1 x s) t ω =
      (1 - a) * 𝔼.forwardSeries a x t ω - lag xm1 x t ω := by
  have ha : |a| < 1 := by rwa [abs_of_nonneg ha0]
  have hlb : ∀ t ω, |lag xm1 x t ω| ≤ max M |xm1| := by
    intro t ω
    cases t with
    | zero => exact le_max_right _ _
    | succ t => exact (hx t ω).trans (le_max_left _ _)
  have hsx := ForwardSolution.summable_A16 𝔼 ha hx t ω
  have hsl := ForwardSolution.summable_A16 𝔼 ha hlb t ω
  have hlag : 𝔼.forwardSeries a (lag xm1 x) t ω =
      lag xm1 x t ω + a * 𝔼.forwardSeries a x t ω := by
    simp only [ExpectationSystem.forwardSeries]
    rw [hsl.tsum_eq_zero_add, pow_zero, one_mul, add_zero, lag_known 𝔼 xm1 hxa t,
      ← tsum_mul_left]
    congr 1
    refine tsum_congr fun j => ?_
    rw [show t + (j + 1) = (t + j) + 1 from by omega]
    change a ^ (j + 1) * 𝔼.E t (x (t + j)) ω = _
    ring
  have e : 𝔼.forwardSeries a (fun s => x s - lag xm1 x s) t ω =
      𝔼.forwardSeries a x t ω - 𝔼.forwardSeries a (lag xm1 x) t ω := by
    simp only [ExpectationSystem.forwardSeries, map_sub, Pi.sub_apply, mul_sub]
    exact Summable.tsum_sub hsx hsl
  rw [e, hlag]
  ring

/-- Woodford (2003), (3.11) (tool): `q` is bounded and adapted when `π, x` are. -/
theorem qProc_bounded_adapted (c : Calib) (xm1 : ℝ) {π x : ℕ → Ω → ℝ} (hπa : 𝔼.Adapted π)
    (hxa : 𝔼.Adapted x) (hπb : BoundedProc π) (hxb : BoundedProc x) :
    𝔼.Adapted (qProc c xm1 π x) ∧ BoundedProc (qProc c xm1 π x) := by
  refine ⟨fun t => ?_, ?_⟩
  · simp only [qProc, map_add, map_smul, map_sub, hπa t, hxa t, lag_known 𝔼 xm1 hxa t]
  · obtain ⟨Mπ, hMπ⟩ := hπb
    obtain ⟨Mx, hMx⟩ := hxb
    have hlb : ∀ t ω, |lag xm1 x t ω| ≤ max Mx |xm1| := by
      intro t ω
      cases t with
      | zero => exact le_max_right _ _
      | succ t => exact (hMx t ω).trans (le_max_left _ _)
    refine ⟨|phiPi c.σ c.κ c.li| * Mπ + |phiX c.σ c.lx c.li / 4| * (Mx + max Mx |xm1|),
      fun t ω => ?_⟩
    simp only [qProc, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul_of_nonneg_left (hMπ t ω) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMx t ω) (hlb t ω)))
        (abs_nonneg _)

/-- Woodford (2003), (3.12)–(3.13), pp. 588–590 (date by date): for bounded `π, x` with `x`
adapted, (3.12) at date `t` is equivalent to the target criterion (3.13) at date `t`. -/
theorem g15_iff_crit313 (c : Calib) (hc : c.Adm) {π x i : ℕ → Ω → ℝ} {xm1 im1 im2 : ℝ}
    (hxa : 𝔼.Adapted x) (hπb : BoundedProc π) (hxb : BoundedProc x) (t : ℕ) :
    G15 𝔼 (L1c c) (L2c c) (idev c.istar i) (qProc c xm1 π x) (im1 - c.istar)
        (im2 - c.istar) t ↔ Crit313 𝔼 c xm1 im1 im2 π x i t := by
  obtain ⟨-, -, hL2, -, -⟩ := L_props c hc
  obtain ⟨-, -, hσ, hκ, -, hli⟩ := hc
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  have hL0 : L2c c ≠ 0 := by linarith
  have ha0 : 0 ≤ (L2c c)⁻¹ := inv_nonneg.mpr (by linarith)
  have ha1 : (L2c c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL2
  have h1a : 1 - (L2c c)⁻¹ ≠ 0 := by linarith
  have hlb : ∀ t ω, |lag xm1 x t ω| ≤ max Mx |xm1| := by
    intro t ω
    cases t with
    | zero => exact le_max_right _ _
    | succ t => exact (hMx t ω).trans (le_max_left _ _)
  have hdx : ∀ t ω, |x t ω - lag xm1 x t ω| ≤ Mx + max Mx |xm1| := fun t ω =>
    (abs_sub _ _).trans (add_le_add (hMx t ω) (hlb t ω))
  unfold G15 wLag Crit313
  rw [lag_idev, lag_lag_idev, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  have hq : 𝔼.forwardSeries (L2c c)⁻¹ (qProc c xm1 π x) t ω =
      phiPi c.σ c.κ c.li * 𝔼.forwardSeries (L2c c)⁻¹ π t ω
        + phiX c.σ c.lx c.li / 4 * ((1 - (L2c c)⁻¹) * 𝔼.forwardSeries (L2c c)⁻¹ x t ω
          - lag xm1 x t ω) := by
    have e1 : 𝔼.forwardSeries (L2c c)⁻¹ (qProc c xm1 π x) t ω =
        phiPi c.σ c.κ c.li * 𝔼.forwardSeries (L2c c)⁻¹ π t ω + phiX c.σ c.lx c.li / 4 *
          𝔼.forwardSeries (L2c c)⁻¹ (fun s => x s - lag xm1 x s) t ω :=
      forwardSeries_lin 𝔼 (g := fun s => x s - lag xm1 x s) ha0 ha1 hMπ hdx _ _ t ω
    rw [e1, forwardSeries_diff 𝔼 ha0 ha1 hMx hxa]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fz_eq, hq]
  set P := 𝔼.forwardSeries (L2c c)⁻¹ π t ω
  set X := 𝔼.forwardSeries (L2c c)⁻¹ x t ω
  set W := lag im1 i t ω - c.istar - L1c c * (lag im2 (lag im1 i) t ω - c.istar)
  have hk : L2c c * (1 - (L2c c)⁻¹) * c.li / (c.κ * c.σ) ≠ 0 := by
    have : 0 < 1 - (L2c c)⁻¹ := by linarith
    have : 0 < L2c c := by linarith
    have : 0 < c.κ * c.σ := mul_pos hκ hσ
    positivity
  have key : (1 - (L2c c)⁻¹) * P + phiX313 c / 4 * ((1 - (L2c c)⁻¹) * X)
      - (thetaX c / 4 * lag xm1 x t ω - thetaI c * (lag im1 i t ω - c.istar)
        - thetaD c * (lag im1 i t ω - lag im2 (lag im1 i) t ω)) =
      L2c c * (1 - (L2c c)⁻¹) * c.li / (c.κ * c.σ) *
        (W - -(L2c c)⁻¹ * (phiPi c.σ c.κ c.li * P + phiX c.σ c.lx c.li / 4 *
          ((1 - (L2c c)⁻¹) * X - lag xm1 x t ω))) := by
    simp only [W, phiX313, thetaX, thetaI, thetaD, phiPi, phiX]
    field_simp
    ring
  constructor
  · intro h
    rw [← sub_eq_zero, key, h, sub_self, mul_zero]
  · intro h
    rw [← sub_eq_zero] at h
    rw [key] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hk
    · linarith

/-- **Woodford (2003), (3.12)–(3.13) and Proposition 8.6, pp. 588–591: the rule as a pure
targeting rule.** For bounded adapted `π, x, i` (and any history), commitment to the instrument
rule (3.7) at all dates is equivalent to commitment to the target criterion (3.13) at all
dates. -/
theorem rule_iff_crit313 (c : Calib) (hc : c.Adm) {π x i : ℕ → Ω → ℝ} (xm1 im1 im2 : ℝ)
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) (hia : 𝔼.Adapted i) (hπb : BoundedProc π)
    (hxb : BoundedProc x) (hib : BoundedProc i) :
    (∀ t, Rule c xm1 im1 im2 π x i t) ↔ (∀ t, Crit313 𝔼 c xm1 im1 im2 π x i t) := by
  obtain ⟨-, -, hL2, -, -⟩ := L_props c hc
  obtain ⟨hqa, hqb⟩ := qProc_bounded_adapted 𝔼 c xm1 hπa hxa hπb hxb
  have hida : 𝔼.Adapted (idev c.istar i) := by
    intro t
    simp only [idev, map_sub, hia t, 𝔼.const]
  have hidb : BoundedProc (idev c.istar i) := by
    obtain ⟨M, hM⟩ := hib
    exact ⟨M + |c.istar|, fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) le_rfl)⟩
  rw [forall_congr' (rule_iff_g14 c hc xm1 im1 im2 π x i), prop_8_6 𝔼 hL2 hida hqa hidb hqb]
  exact forall_congr' (g15_iff_crit313 𝔼 c hc hxa hπb hxb)

/-! ### The numbers of pp. 590–591 -/

/-- Woodford (2003), Table 6.1 and pp. 586–591: the calibration `β = .99`, `σ = 1/.16`,
`κ = .024`, `λ_x = κ/θ = .024/7.88`, `λ_i = .236` (survey E10; the targets play no role). -/
noncomputable def cal : Calib := ⟨0.99, 1 / 0.16, 0.024, 0.024 / 7.88, 0.236, 0, 0⟩

/-- Woodford (2003), Table 6.1: the calibration is admissible. -/
theorem cal_adm : cal.Adm := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [cal] <;> norm_num

/-- Woodford (2003), p. 590: at the calibration, `1.4783 < λ₂ < 1.4785`. -/
theorem L2_cal : (1.4783 : ℝ) < L2c cal ∧ L2c cal < 1.4785 := by
  have hd : (0 : ℝ) ≤ (rho1 0.99 (1 / 0.16) 0.024 + rho2 0.99) ^ 2 - 4 * rho2 0.99 := by
    unfold rho1 rho2; norm_num
  have h1 : (0.795 : ℝ) < Real.sqrt ((rho1 0.99 (1 / 0.16) 0.024 + rho2 0.99) ^ 2
      - 4 * rho2 0.99) := by
    rw [Real.lt_sqrt (by norm_num)]
    unfold rho1 rho2; norm_num
  have h2 : Real.sqrt ((rho1 0.99 (1 / 0.16) 0.024 + rho2 0.99) ^ 2 - 4 * rho2 0.99) <
      0.7952 := by
    rw [Real.sqrt_lt' (by norm_num)]
    unfold rho1 rho2; norm_num
  have hs : rho1 0.99 (1 / 0.16) 0.024 + rho2 0.99 = 2.14 / 0.99 := by
    unfold rho1 rho2; norm_num
  have e : L2c cal = ((rho1 0.99 (1 / 0.16) 0.024 + rho2 0.99) + Real.sqrt
      ((rho1 0.99 (1 / 0.16) 0.024 + rho2 0.99) ^ 2 - 4 * rho2 0.99)) / 2 := rfl
  rw [e, hs]
  rw [hs] at h1 h2
  constructor <;> norm_num <;> linarith

/-- **Woodford (2003), pp. 590–591: the numbers.** At the calibration: the decay rate
`λ₂⁻¹ ∈ (.676, .677)` (printed `.68`), the mean horizon `(λ₂ − 1)⁻¹ ∈ (2.08, 2.10)` (printed
`2.1`), `θ_i ∈ (.238, .239)` (printed `.24`), `θ_Δ ∈ (.514, .515)` (printed `.51`), and
`φ_x = θ_x ∈ (.164, .165)` (printed `.15`: see `p591_phiX_not_015`). -/
theorem p590_numbers :
    (0.676 : ℝ) < (L2c cal)⁻¹ ∧ (L2c cal)⁻¹ < 0.677 ∧
      (2.08 : ℝ) < (L2c cal - 1)⁻¹ ∧ (L2c cal - 1)⁻¹ < 2.10 ∧
      (0.238 : ℝ) < thetaI cal ∧ thetaI cal < 0.239 ∧
      (0.514 : ℝ) < thetaD cal ∧ thetaD cal < 0.515 ∧
      (0.164 : ℝ) < phiX313 cal ∧ phiX313 cal < 0.165 ∧ thetaX cal = phiX313 cal := by
  obtain ⟨l1, l2⟩ := L2_cal
  have hpos : 0 < L2c cal := by linarith
  have u1 : (0.6763 : ℝ) < (L2c cal)⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hpos]
    have : (1.4785 : ℝ) < (0.6763 : ℝ)⁻¹ := by norm_num
    linarith
  have u2 : (L2c cal)⁻¹ < 0.6765 := by
    rw [inv_lt_comm₀ hpos (by norm_num)]
    have : (0.6765 : ℝ)⁻¹ < 1.4783 := by norm_num
    linarith
  have hprod : L1c cal * L2c cal = 1 / 0.99 := by
    have := (L_props cal cal_adm).2.2.2.2
    rw [this]
    simp only [cal, rho2]
    norm_num
  have v1 : (2.08 : ℝ) < (L2c cal - 1)⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) (by linarith)]
    have : (0.4785 : ℝ) < (2.08 : ℝ)⁻¹ := by norm_num
    linarith
  have v2 : (L2c cal - 1)⁻¹ < 2.10 := by
    rw [inv_lt_comm₀ (by linarith) (by norm_num)]
    have : (2.10 : ℝ)⁻¹ < 0.4783 := by norm_num
    linarith
  have hI : thetaI cal = 0.236 / 0.99 := by
    rw [thetaI_eq cal cal_adm]
    simp only [cal]
  have hD : thetaD cal = 1 / 0.99 * (1 - (L2c cal)⁻¹) * 0.236 / (0.024 * (1 / 0.16)) := by
    unfold thetaD
    rw [hprod]
    simp only [cal]
  have hX : phiX313 cal = 4 * (1 - (L2c cal)⁻¹) * (0.024 / 7.88) / 0.024 := by
    unfold phiX313
    simp only [cal]
  refine ⟨by linarith, by linarith, v1, v2, by rw [hI]; norm_num, by rw [hI]; norm_num,
    ?_, ?_, ?_, ?_, rfl⟩
  · rw [hD]; norm_num; linarith
  · rw [hD]; norm_num; linarith
  · rw [hX]; norm_num; linarith
  · rw [hX]; norm_num; linarith

/-- **Woodford (2003), p. 591 (survey S2, confirmed): the printed `φ_x = θ_x = .15` is wrong.**
The formula `4(1 − λ₂⁻¹)λ_x/κ` gives `.164…` with `λ_x = κ/θ`, more than `.005` above `.15`; the
other p. 590–591 numbers are reproduced (`p590_numbers`). -/
theorem p591_phiX_not_015 : (0.15 : ℝ) + 0.005 < phiX313 cal := by
  have := (p590_numbers).2.2.2.2.2.2.2.2.1
  linarith

/-- **Woodford (2003), pp. 586 and 591: the two printed values of `φ_x` are inconsistent.** No
weight `λ_x > 0` makes the instrument-rule coefficient `4σλ_x/λ_i` round to `.33` and the
target-criterion coefficient `4(1 − λ₂⁻¹)λ_x/κ` round to `.15` at the same time. -/
theorem printed_phiX_inconsistent (lx : ℝ) (hlx : 0 < lx) :
    ¬ (|phiX (1 / 0.16) lx 0.236 - 0.33| ≤ 0.005 ∧
      |phiX313 { cal with lx := lx } - 0.15| ≤ 0.005) := by
  rintro ⟨h1, h2⟩
  obtain ⟨u1, -⟩ := (abs_le.mp h1)
  obtain ⟨-, u2⟩ := (abs_le.mp h2)
  have hL : (0.6765 : ℝ) > (L2c cal)⁻¹ := by
    obtain ⟨l1, -⟩ := L2_cal
    rw [gt_iff_lt, inv_lt_comm₀ (by linarith) (by norm_num)]
    have : (0.6765 : ℝ)⁻¹ < 1.4783 := by norm_num
    linarith
  have e : phiX313 { cal with lx := lx } = 4 * (1 - (L2c cal)⁻¹) * lx / 0.024 := rfl
  rw [e] at u2
  unfold phiX at u1
  have hlx' : 0.003068 ≤ lx := by
    have : (0.325 : ℝ) ≤ 4 * (1 / 0.16) * lx / 0.236 := by linarith
    rw [le_div_iff₀ (by norm_num)] at this
    linarith
  have hprod : (0.3235 : ℝ) * 0.003068 ≤ (1 - (L2c cal)⁻¹) * lx := by
    have : (0.3235 : ℝ) ≤ 1 - (L2c cal)⁻¹ := by linarith
    nlinarith
  have e2 : 4 * (1 - (L2c cal)⁻¹) * lx / 0.024 = ((1 - (L2c cal)⁻¹) * lx) * (4 / 0.024) := by
    ring
  rw [e2] at u2
  norm_num at u2 hprod
  linarith

/-! ### The limit `λ_i → 0` (p. 591) -/

/-- **Woodford (2003), p. 591: `θ_i → 0` as `λ_i → 0`.** -/
theorem tendsto_thetaI (c : Calib) :
    Tendsto (fun l => thetaI { c with li := l }) (𝓝 0) (𝓝 0) := by
  have e : (fun l => thetaI { c with li := l }) =
      fun l => L2c c * (1 - L1c c) * (1 - (L2c c)⁻¹) / (c.κ * c.σ) * l := by
    funext l
    simp only [thetaI, L1c, L2c]
    ring
  rw [e]
  simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul
    (L2c c * (1 - L1c c) * (1 - (L2c c)⁻¹) / (c.κ * c.σ))

/-- **Woodford (2003), p. 591: `θ_Δ → 0` as `λ_i → 0`.** -/
theorem tendsto_thetaD (c : Calib) :
    Tendsto (fun l => thetaD { c with li := l }) (𝓝 0) (𝓝 0) := by
  have e : (fun l => thetaD { c with li := l }) =
      fun l => L1c c * L2c c * (1 - (L2c c)⁻¹) / (c.κ * c.σ) * l := by
    funext l
    simp only [thetaD, L1c, L2c]
    ring
  rw [e]
  simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul
    (L1c c * L2c c * (1 - (L2c c)⁻¹) / (c.κ * c.σ))

/-- **Woodford (2003), p. 591: `φ_x`, `θ_x` and the weights `α_j` do not depend on `λ_i`** (nor
do `λ₁, λ₂`). -/
theorem coef313_indep_li (c : Calib) (l : ℝ) :
    phiX313 { c with li := l } = phiX313 c ∧ thetaX { c with li := l } = thetaX c ∧
      L1c { c with li := l } = L1c c ∧ L2c { c with li := l } = L2c c :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Woodford (2003), (1.30) ⇔ (1.31), pp. 557–558 (the lemma, proved locally):** for `0 ≤ a < 1`
and bounded adapted `y`, `∑ aʲ E_t y_{t+j} = 0` at every date iff `y_t = 0` at every date. -/
theorem forwardSeries_eq_zero_iff {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {y : ℕ → Ω → ℝ}
    {M : ℝ} (hy : ∀ t ω, |y t ω| ≤ M) (hya : 𝔼.Adapted y) :
    (∀ t, 𝔼.forwardSeries a y t = 0) ↔ ∀ t, y t = 0 := by
  constructor
  · intro h t
    have hs := 𝔼.forwardSeries_solves ha0 ha1 hy hya t
    rw [h t, h (t + 1), map_zero, smul_zero, zero_add] at hs
    exact hs.symm
  · intro h t
    funext ω
    simp [ExpectationSystem.forwardSeries, h]

/-- **Woodford (2003), p. 591: the limiting criterion is the Chapter 7 rule (2.5).** For bounded
adapted `π, x`, the `λ_i = 0` form of (3.13), `F_t(π) + (φ_x/4)F_t(x) = (θ_x/4)x_{t−1}`, holds at
every date iff `π_t + (λ_x/κ)(x_t − x_{t−1}) = 0` (Ch. 8 (2.5), p. 561, `φ = λ_x/κ`) holds at
every date. -/
theorem crit_limit_iff_25 (c : Calib) (hc : c.Adm) {π x : ℕ → Ω → ℝ} (xm1 : ℝ)
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) (hπb : BoundedProc π) (hxb : BoundedProc x) :
    (∀ t, Fz 𝔼 (L2c c) π t + (phiX313 c / 4) • Fz 𝔼 (L2c c) x t =
        (thetaX c / 4) • lag xm1 x t) ↔
      ∀ t, π t + (c.lx / c.κ) • (x t - lag xm1 x t) = 0 := by
  obtain ⟨-, -, hL2, -, -⟩ := L_props c hc
  obtain ⟨-, -, -, hκ, -, -⟩ := hc
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  have ha0 : 0 ≤ (L2c c)⁻¹ := inv_nonneg.mpr (by linarith)
  have ha1 : (L2c c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL2
  have h1a : 1 - (L2c c)⁻¹ ≠ 0 := by linarith
  have hlb : ∀ t ω, |lag xm1 x t ω| ≤ max Mx |xm1| := by
    intro t ω
    cases t with
    | zero => exact le_max_right _ _
    | succ t => exact (hMx t ω).trans (le_max_left _ _)
  have hdx : ∀ t ω, |x t ω - lag xm1 x t ω| ≤ Mx + max Mx |xm1| := fun t ω =>
    (abs_sub _ _).trans (add_le_add (hMx t ω) (hlb t ω))
  set y : ℕ → Ω → ℝ := fun s => (1 : ℝ) • π s + (c.lx / c.κ) • (fun s => x s - lag xm1 x s) s
    with hy
  have hyb : ∀ t ω, |y t ω| ≤ Mπ + |c.lx / c.κ| * (Mx + max Mx |xm1|) := by
    intro t ω
    simp only [hy, one_smul, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add (hMπ t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hdx t ω) (abs_nonneg _)
  have hya : 𝔼.Adapted y := by
    intro t
    simp only [hy, one_smul, map_add, map_smul, map_sub, hπa t, hxa t, lag_known 𝔼 xm1 hxa t]
  have key : ∀ t, (Fz 𝔼 (L2c c) π t + (phiX313 c / 4) • Fz 𝔼 (L2c c) x t =
      (thetaX c / 4) • lag xm1 x t) ↔ 𝔼.forwardSeries (L2c c)⁻¹ y t = 0 := by
    intro t
    rw [funext_iff, funext_iff]
    refine forall_congr' fun ω => ?_
    have e1 : 𝔼.forwardSeries (L2c c)⁻¹ y t ω = 1 * 𝔼.forwardSeries (L2c c)⁻¹ π t ω
        + c.lx / c.κ * 𝔼.forwardSeries (L2c c)⁻¹ (fun s => x s - lag xm1 x s) t ω :=
      forwardSeries_lin 𝔼 (g := fun s => x s - lag xm1 x s) ha0 ha1 hMπ hdx _ _ t ω
    rw [forwardSeries_diff 𝔼 ha0 ha1 hMx hxa] at e1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fz_eq, Pi.zero_apply, e1]
    have e2 : phiX313 c / 4 = (1 - (L2c c)⁻¹) * (c.lx / c.κ) := by
      unfold phiX313; field_simp
    have e3 : thetaX c / 4 = (1 - (L2c c)⁻¹) * (c.lx / c.κ) := by
      unfold thetaX; field_simp
    rw [e2, e3]
    constructor
    · intro h
      have : (1 - (L2c c)⁻¹) * (1 * 𝔼.forwardSeries (L2c c)⁻¹ π t ω + c.lx / c.κ *
          ((1 - (L2c c)⁻¹) * 𝔼.forwardSeries (L2c c)⁻¹ x t ω - lag xm1 x t ω)) = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp this).resolve_left h1a
    · intro h
      linear_combination (1 - (L2c c)⁻¹) * h
  rw [forall_congr' key, forwardSeries_eq_zero_iff 𝔼 ha0 ha1 hyb hya]
  refine forall_congr' fun t => ?_
  simp only [hy, one_smul]

/-- **Woodford (2003), p. 591 ("in the limit as λ_i approaches zero, the optimal target criterion
(2.5) derived in Chapter 7 is recovered"), as a genuine limit.** If a fixed bounded adapted plan
satisfies the criterion (3.13) for a sequence of weights `λ_i = l_n > 0` with `l_n → 0`, it
satisfies (2.5) `π_t + (λ_x/κ)(x_t − x_{t−1}) = 0` at every date. -/
theorem limit_plan_satisfies_25 (c : Calib) (hc : c.Adm) {l : ℕ → ℝ}
    (hl : Tendsto l atTop (𝓝 0)) {π x i : ℕ → Ω → ℝ} {xm1 im1 im2 : ℝ}
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) (hπb : BoundedProc π) (hxb : BoundedProc x)
    (h : ∀ n t, Crit313 𝔼 { c with li := l n } xm1 im1 im2 π x i t) :
    ∀ t, π t + (c.lx / c.κ) • (x t - lag xm1 x t) = 0 := by
  refine (crit_limit_iff_25 𝔼 c hc xm1 hπa hxa hπb hxb).mp fun t => ?_
  funext ω
  have hI := (tendsto_thetaI c).comp hl
  have hD := (tendsto_thetaD c).comp hl
  have hlim : Tendsto (fun n => thetaX c / 4 * lag xm1 x t ω
      - thetaI { c with li := l n } * (lag im1 i t ω - c.istar)
      - thetaD { c with li := l n } * (lag im1 i t ω - lag im2 (lag im1 i) t ω)) atTop
      (𝓝 (thetaX c / 4 * lag xm1 x t ω)) := by
    have := ((tendsto_const_nhds (x := thetaX c / 4 * lag xm1 x t ω)).sub
      (hI.mul_const (lag im1 i t ω - c.istar))).sub
      (hD.mul_const (lag im1 i t ω - lag im2 (lag im1 i) t ω))
    simpa using this
  have hconst : ∀ n, Fz 𝔼 (L2c c) π t ω + phiX313 c / 4 * Fz 𝔼 (L2c c) x t ω =
      thetaX c / 4 * lag xm1 x t ω - thetaI { c with li := l n } * (lag im1 i t ω - c.istar)
        - thetaD { c with li := l n } * (lag im1 i t ω - lag im2 (lag im1 i) t ω) := by
    intro n
    have := congrFun (h n t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hc' : Tendsto (fun _ : ℕ => Fz 𝔼 (L2c c) π t ω + phiX313 c / 4 * Fz 𝔼 (L2c c) x t ω)
      atTop (𝓝 (thetaX c / 4 * lag xm1 x t ω)) := by
    exact hlim.congr fun n => (hconst n).symm
  have := tendsto_nhds_unique tendsto_const_nhds hc'
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this

end Woodford.OptimalPolicyRules.IRuleForwardIntegrated
