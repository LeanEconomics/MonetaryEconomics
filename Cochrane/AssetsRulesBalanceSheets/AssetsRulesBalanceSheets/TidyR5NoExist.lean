/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.TidyR5FiscalLink

/-!
# Theorem FR (d), existence: `d₀ ≥ 0` is not sufficient

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.2,
eqs. (9.8)–(9.12), pp. 266–267 (Theorem FR; a stochastic target `P*`, initial debt
`b₀ = b̄ + θ d₀ ≠ b̄`).

`FiscalRulesTargetFinal.exists_iff_pathwise` characterises existence of an equilibrium with prices
bounded above implicitly; for a predetermined target value and for one-shot news the condition is
explicit and holds for every `d₀ ≥ 0`. This module shows that with news at infinitely many dates
`d₀ ≥ 0` is **not** sufficient, and that no threshold condition can describe existence.

## The settle-or-continue target

`gSys p` is the genuine probability space `Ω = ℕ` (state `k` = "the target settles at date
`k + 1`") with `P(k) = p (1 − p)ᵏ` and the tree's information
(`FiscalRulesMeasure.SunspotMeasure.sunFiltration`): at each date the target either settles, with
probability `p`, at the level `σ` forever, or continues at the level `1` (`tgtS`). News arrives at
every date (`not_resolved`).

## Main results

* `orbit_nonpos`, `orbit_nonneg` (the key inequalities): along the continuation path, with
  `b_t = (1 − β) D_t/σ`, `c_t = P_t − 1`, Jensen's inequality gives
  `c_t ≤ Q_S b_{t+1} + Q_C c_{t+1}` (`Q_S + Q_C = 1` the risk-adjusted settle and continue
  probabilities) while the flow is `b_t = β b_{t+1} + ((1 − β)/σ) c_t`; comparing suprema,
  `sup b ≤ (β + (1 − β)/σ) sup b`, so `sup b ≤ 0` when `σ > 1`. Symmetrically, with prices bounded
  away from zero, `D_0 ≥ 0`.
* `no_eqm_pos` (**counterexample to sufficiency of `d₀ ≥ 0`**): for `σ > 1`, every `0 < β < 1`,
  `0 < p < 1`, `θ ≠ 0`, `b̄` and every `d₀ > 0` there is no equilibrium of the rule with prices
  bounded above and `b₀ = b̄ + θ d₀`; `exists_zero`: at `d₀ = 0` the target is one.
* `existsBoth_iff`: equilibria with prices bounded above and away from zero exist iff `d₀ = 0`.
* `existsAbove_not_upward_closed`, `existsBoth_not_open`, `existsAbove_not_downward_closed`
  (**no threshold or strict-inequality condition**): the existence set in `d₀` need not be
  upward-closed, is never downward-closed, and need not be open, so no condition of the form
  `d₀ > c`, `d₀ ≥ c`, `d₀ < c` (with `c` any function of the primitives), and no condition given by
  strict inequalities continuous in `d₀` (such as the explicit conditions for predetermined target
  values and one-shot news), characterises existence on every system.
-/

namespace Cochrane.AssetsRulesBalanceSheets.TidyR5NoExist

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure FiscalRulesMeasure FiscalRulesTargetMeasure FiscalRulesTargetOpen
open FiscalRulesTargetClose FiscalRulesTargetFinal

/-! ### The key inequalities along the continuation path -/

/-- Cochrane (2023), eq. (9.12), p. 267 (Jensen's inequality for the harmonic mean): for weights
`q₁, q₂ ≥ 0` with `q₁ + q₂ = 1` and `P, Q > 0`, if `x (q₁/P + q₂/Q) = 1` then
`x ≤ q₁ P + q₂ Q`. -/
theorem harmonic_le {q1 q2 P Q x : ℝ} (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hq : q1 + q2 = 1)
    (hP : 0 < P) (hQ : 0 < Q) (hx : x * (q1 / P + q2 / Q) = 1) : x ≤ q1 * P + q2 * Q := by
  have hx0 : 0 ≤ x := by
    by_contra h
    push Not at h
    have : x * (q1 / P + q2 / Q) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h.le (by positivity)
    linarith
  have key : 1 ≤ (q1 * P + q2 * Q) * (q1 / P + q2 / Q) := by
    have e : (q1 * P + q2 * Q) * (q1 / P + q2 / Q) - 1 = q1 * q2 * (P - Q) ^ 2 / (P * Q) := by
      have hq2' : q2 = 1 - q1 := by linarith
      subst hq2'
      field_simp
      ring
    have : 0 ≤ q1 * q2 * (P - Q) ^ 2 / (P * Q) := by positivity
    linarith
  calc x = x * 1 := (mul_one x).symm
    _ ≤ x * ((q1 * P + q2 * Q) * (q1 / P + q2 / Q)) := mul_le_mul_of_nonneg_left key hx0
    _ = (q1 * P + q2 * Q) * (x * (q1 / P + q2 / Q)) := by ring
    _ = q1 * P + q2 * Q := by rw [hx, mul_one]

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the continuation path cannot carry positive debt**):
let `0 < β < 1`, `σ > 1`, `0 < p < 1`, and let sequences `a` (the scaled debt deviation on the
continuation path), `x` (the continuation price level) satisfy the flow `a_t = x_t − 1 + β a_{t+1}`,
the interest-rate target `x_t (p/(σ + (1 − β) a_{t+1}) + (1 − p)/x_{t+1}) = p/σ + 1 − p` (the
settled price is `σ + (1 − β) a_{t+1}`), positivity, and the bounds `x ≤ M`, `a ≤ K`. Then
`a_0 ≤ 0`. -/
theorem orbit_nonpos {β σ p M K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ) (hp0 : 0 < p)
    (hp1 : p < 1) {a x : ℕ → ℝ} (hx : ∀ t, 0 < x t) (hy : ∀ t, 0 < σ + (1 - β) * a (t + 1))
    (hflow : ∀ t, a t = x t - 1 + β * a (t + 1))
    (hrate : ∀ t, x t * (p / (σ + (1 - β) * a (t + 1)) + (1 - p) / x (t + 1)) = p / σ + (1 - p))
    (hxM : ∀ t, x t ≤ M) (haK : ∀ t, a t ≤ K) : a 0 ≤ 0 := by
  have hσ0 : 0 < σ := by linarith
  have h1β : 0 < 1 - β := by linarith
  set γ : ℝ := p / σ + (1 - p) with hγ
  have hγ0 : 0 < γ := by positivity
  set qS : ℝ := p / (γ * σ) with hqS
  set qC : ℝ := (1 - p) / γ with hqC
  have hqS0 : 0 < qS := by positivity
  have hqC0 : 0 ≤ qC := div_nonneg (by linarith) hγ0.le
  have hq1 : qS + qC = 1 := by
    have e : qS + qC = (p / σ + (1 - p)) / γ := by
      rw [hqS, hqC]
      field_simp
    rw [e, ← hγ, div_self hγ0.ne']
  set b : ℕ → ℝ := fun t => (1 - β) * a t / σ with hb
  set c : ℕ → ℝ := fun t => x t - 1 with hc
  have key1 : ∀ t, c t ≤ qS * b (t + 1) + qC * c (t + 1) := by
    intro t
    have hP : 0 < 1 + b (t + 1) := by
      simp only [hb]
      have := hy t
      rw [show 1 + (1 - β) * a (t + 1) / σ = (σ + (1 - β) * a (t + 1)) / σ by field_simp]
      positivity
    have hQ : 0 < 1 + c (t + 1) := by simp only [hc]; linarith [hx (t + 1)]
    have hxe : x t * (qS / (1 + b (t + 1)) + qC / (1 + c (t + 1))) = 1 := by
      have h := hrate t
      have e1 : σ + (1 - β) * a (t + 1) = σ * (1 + b (t + 1)) := by
        simp only [hb]; field_simp
      have e2 : x (t + 1) = 1 + c (t + 1) := by simp only [hc]; ring
      rw [e1, e2] at h
      simp only [hqS, hqC]
      field_simp
      field_simp at h
      linear_combination h
    have := harmonic_le hqS0.le hqC0 hq1 hP hQ hxe
    have e : qS * (1 + b (t + 1)) + qC * (1 + c (t + 1)) =
        (qS + qC) + (qS * b (t + 1) + qC * c (t + 1)) := by ring
    rw [e, hq1] at this
    have e2 : c t = x t - 1 := rfl
    rw [e2]
    linarith
  have key2 : ∀ t, b t = β * b (t + 1) + ((1 - β) / σ) * c t := fun t => by
    simp only [hb, hc]
    rw [hflow t]
    field_simp
    ring
  have hbB : BddAbove (Set.range b) := ⟨(1 - β) * K / σ, by
    rintro _ ⟨t, rfl⟩
    simp only [hb]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (haK t) h1β.le) hσ0.le⟩
  have hcB : BddAbove (Set.range c) := ⟨M - 1, by
    rintro _ ⟨t, rfl⟩
    simp only [hc]
    linarith [hxM t]⟩
  set Sb := ⨆ t, b t with hSb
  set Sc := ⨆ t, c t with hSc
  have hScb : Sc ≤ Sb := by
    have h : Sc ≤ qS * Sb + qC * Sc := ciSup_le fun t => (key1 t).trans
      (add_le_add (mul_le_mul_of_nonneg_left (le_ciSup hbB (t + 1)) hqS0.le)
        (mul_le_mul_of_nonneg_left (le_ciSup hcB (t + 1)) hqC0))
    have e : qS * Sc + qC * Sc = Sc := by rw [← add_mul, hq1, one_mul]
    have h2 : qS * Sc ≤ qS * Sb := by linarith
    exact le_of_mul_le_mul_left h2 hqS0
  have hk : 0 < (1 - β) / σ := div_pos h1β hσ0
  have hSb : Sb ≤ β * Sb + ((1 - β) / σ) * Sb := ciSup_le fun t => by
    rw [key2 t]
    exact add_le_add (mul_le_mul_of_nonneg_left (le_ciSup hbB (t + 1)) hβ0.le)
      (mul_le_mul_of_nonneg_left ((le_ciSup hcB t).trans hScb) hk.le)
  have hκ : 0 < 1 - β - (1 - β) / σ := by
    have : (1 - β) / σ < 1 - β := by
      rw [div_lt_iff₀ hσ0]
      nlinarith
    linarith
  have hSb0 : Sb ≤ 0 := by nlinarith
  have hb0 : b 0 ≤ 0 := (le_ciSup hbB 0).trans hSb0
  simp only [hb] at hb0
  have : (1 - β) * a 0 ≤ 0 := by
    rwa [div_le_iff₀ hσ0, zero_mul] at hb0
  nlinarith

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**with prices bounded away from zero the continuation
path cannot carry negative debt**): under the hypotheses of `orbit_nonpos` without the upper
bounds, but with the continuation and settled prices bounded below by `m_P > 0`, `a_0 ≥ 0`.
Proof: `v_t = 1/(1 + b_t)`, `u_t = 1/x_t` obey `u_t = Q_S v_{t+1} + Q_C u_{t+1}` exactly and, by
convexity of `z ↦ 1/(1 + z)`, `v_t ≤ β v_{t+1} + ((1 − β)/σ) u_t + (1 − β)(1 − 1/σ)`; comparing
suprema gives `sup v ≤ 1`. -/
theorem orbit_nonneg {β σ p mP : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ) (hp0 : 0 < p)
    (hp1 : p < 1) (hmP : 0 < mP) {a x : ℕ → ℝ} (hx : ∀ t, mP ≤ x t)
    (hy : ∀ t, mP ≤ σ + (1 - β) * a (t + 1))
    (hflow : ∀ t, a t = x t - 1 + β * a (t + 1))
    (hrate : ∀ t, x t * (p / (σ + (1 - β) * a (t + 1)) + (1 - p) / x (t + 1)) = p / σ + (1 - p)) :
    0 ≤ a 0 := by
  have hσ0 : 0 < σ := by linarith
  have h1β : 0 < 1 - β := by linarith
  have hx0 : ∀ t, 0 < x t := fun t => hmP.trans_le (hx t)
  set γ : ℝ := p / σ + (1 - p) with hγ
  have hγ0 : 0 < γ := by positivity
  set qS : ℝ := p / (γ * σ) with hqS
  set qC : ℝ := (1 - p) / γ with hqC
  have hqS0 : 0 < qS := by positivity
  have hqC0 : 0 ≤ qC := div_nonneg (by linarith) hγ0.le
  have hq1 : qS + qC = 1 := by
    have e : qS + qC = (p / σ + (1 - p)) / γ := by
      rw [hqS, hqC]
      field_simp
    rw [e, ← hγ, div_self hγ0.ne']
  set b : ℕ → ℝ := fun t => (1 - β) * a t / σ with hb
  have hyb : ∀ t, σ + (1 - β) * a t = σ * (1 + b t) := fun t => by
    simp only [hb]; field_simp
  have hb1 : ∀ t, mP / σ ≤ 1 + b (t + 1) := fun t => by
    rw [div_le_iff₀ hσ0, mul_comm, ← hyb]
    exact hy t
  have hb1p : ∀ t, 0 < 1 + b (t + 1) := fun t => (div_pos hmP hσ0).trans_le (hb1 t)
  have key2 : ∀ t, b t = β * b (t + 1) + ((1 - β) / σ) * (x t - 1) := fun t => by
    simp only [hb]
    rw [hflow t]
    field_simp
    ring
  have hbp : ∀ t, 0 < 1 + b t := fun t => by
    rw [key2 t]
    have h1 := hb1p t
    have h2 := hx0 t
    have e : 1 + (β * b (t + 1) + (1 - β) / σ * (x t - 1)) =
        β * (1 + b (t + 1)) + (1 - β) / σ * x t + (1 - β) * (1 - 1 / σ) := by ring
    rw [e]
    have : 0 ≤ (1 - β) * (1 - 1 / σ) := mul_nonneg h1β.le (by
      rw [sub_nonneg, div_le_one hσ0]; linarith)
    positivity
  set v : ℕ → ℝ := fun t => 1 / (1 + b t) with hv
  set u : ℕ → ℝ := fun t => 1 / x t with hu
  have keyU : ∀ t, u t = qS * v (t + 1) + qC * u (t + 1) := fun t => by
    have h := hrate t
    rw [hyb] at h
    have hx1 := (hx0 t).ne'
    have hx2 := (hx0 (t + 1)).ne'
    have hb2 := (hb1p t).ne'
    have h' : p / (σ * (1 + b (t + 1))) + (1 - p) / x (t + 1) = γ / x t := by
      rw [eq_div_iff hx1, mul_comm]
      exact h
    have e : qS * v (t + 1) + qC * u (t + 1) =
        (p / (σ * (1 + b (t + 1))) + (1 - p) / x (t + 1)) / γ := by
      simp only [hqS, hqC, hv, hu]
      field_simp
    rw [e, h']
    simp only [hu]
    field_simp
  -- convexity: the tangent line of `z ↦ 1/(1 + z)` at `b_t`
  have tang : ∀ t (z : ℝ), 0 < 1 + z →
      1 / (1 + b t) - (z - b t) / (1 + b t) ^ 2 ≤ 1 / (1 + z) := fun t z hz => by
    have h := FiscalRules.inv_ge_tangent hz (hbp t)
    have e : 2 / (1 + b t) - (1 + z) / (1 + b t) ^ 2 =
        1 / (1 + b t) - (z - b t) / (1 + b t) ^ 2 := by
      field_simp
      ring
    linarith
  have keyV : ∀ t, v t ≤ β * v (t + 1) + ((1 - β) / σ) * u t + (1 - β) * (1 - 1 / σ) := by
    intro t
    have w3 : 0 ≤ (1 - β) * (1 - 1 / σ) := mul_nonneg h1β.le (by
      rw [sub_nonneg, div_le_one hσ0]; linarith)
    have t1 := tang t (b (t + 1)) (hb1p t)
    have t2 := tang t (x t - 1) (by linarith [hx0 t])
    have t3 := tang t 0 (by norm_num)
    have e2 : 1 / (1 + (x t - 1)) = u t := by simp only [hu]; ring_nf
    rw [e2] at t2
    have e3 : (1 : ℝ) / (1 + 0) = 1 := by norm_num
    rw [e3] at t3
    have hsum : β * (b (t + 1) - b t) + (1 - β) / σ * (x t - 1 - b t) +
        (1 - β) * (1 - 1 / σ) * (0 - b t) = 0 := by
      rw [key2 t]
      field_simp
      ring
    have hq0 : 0 < (1 + b t) ^ 2 := by have := hbp t; positivity
    have comb : β * (1 / (1 + b t) - (b (t + 1) - b t) / (1 + b t) ^ 2) +
        (1 - β) / σ * (1 / (1 + b t) - (x t - 1 - b t) / (1 + b t) ^ 2) +
        (1 - β) * (1 - 1 / σ) * (1 / (1 + b t) - (0 - b t) / (1 + b t) ^ 2) = v t := by
      simp only [hv]
      have e : β + (1 - β) / σ + (1 - β) * (1 - 1 / σ) = 1 := by field_simp; ring
      have : β * (1 / (1 + b t) - (b (t + 1) - b t) / (1 + b t) ^ 2) +
          (1 - β) / σ * (1 / (1 + b t) - (x t - 1 - b t) / (1 + b t) ^ 2) +
          (1 - β) * (1 - 1 / σ) * (1 / (1 + b t) - (0 - b t) / (1 + b t) ^ 2) =
          (β + (1 - β) / σ + (1 - β) * (1 - 1 / σ)) * (1 / (1 + b t)) -
          (β * (b (t + 1) - b t) + (1 - β) / σ * (x t - 1 - b t) +
            (1 - β) * (1 - 1 / σ) * (0 - b t)) / (1 + b t) ^ 2 := by ring
      rw [this, e, hsum]
      ring
    have hk : 0 ≤ (1 - β) / σ := (div_pos h1β hσ0).le
    have := add_le_add (add_le_add (mul_le_mul_of_nonneg_left t1 hβ0.le)
      (mul_le_mul_of_nonneg_left t2 hk)) (mul_le_mul_of_nonneg_left t3 w3)
    rw [comb] at this
    simp only [hv] at this ⊢
    linarith
  -- bounds
  have hvB : BddAbove (Set.range v) := ⟨v 0 + σ / mP, by
    rintro _ ⟨t, rfl⟩
    have hv0 : 0 ≤ v 0 := (one_div_pos.2 (hbp 0)).le
    rcases t with _ | t
    · linarith [div_pos hσ0 hmP]
    · have : v (t + 1) ≤ σ / mP := by
        simp only [hv]
        rw [div_le_div_iff₀ (hb1p t) hmP, one_mul]
        have := hb1 t
        rw [div_le_iff₀ hσ0] at this
        linarith
      linarith⟩
  have huB : BddAbove (Set.range u) := ⟨1 / mP, by
    rintro _ ⟨t, rfl⟩
    exact one_div_le_one_div_of_le hmP (hx t)⟩
  set Sv := ⨆ t, v t with hSv
  set Su := ⨆ t, u t with hSu
  have hSuv : Su ≤ Sv := by
    have h : Su ≤ qS * Sv + qC * Su := ciSup_le fun t => by
      rw [keyU t]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_ciSup hvB (t + 1)) hqS0.le)
        (mul_le_mul_of_nonneg_left (le_ciSup huB (t + 1)) hqC0)
    have e : qS * Su + qC * Su = Su := by rw [← add_mul, hq1, one_mul]
    have h2 : qS * Su ≤ qS * Sv := by linarith
    exact le_of_mul_le_mul_left h2 hqS0
  have hk : 0 < (1 - β) / σ := div_pos h1β hσ0
  have hSv : Sv ≤ β * Sv + ((1 - β) / σ) * Sv + (1 - β) * (1 - 1 / σ) := ciSup_le fun t =>
    (keyV t).trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (le_ciSup hvB (t + 1))
      hβ0.le) (mul_le_mul_of_nonneg_left ((le_ciSup huB t).trans hSuv) hk.le)) le_rfl)
  have hκ : 0 < 1 - β - (1 - β) / σ := by
    have : (1 - β) / σ < 1 - β := by
      rw [div_lt_iff₀ hσ0]
      nlinarith
    linarith
  have hSv1 : Sv ≤ 1 := by
    have e : (1 - β) * (1 - 1 / σ) = 1 - β - (1 - β) / σ := by field_simp
    rw [e] at hSv
    nlinarith
  have hv0 : v 0 ≤ 1 := (le_ciSup hvB 0).trans hSv1
  simp only [hv] at hv0
  rw [div_le_one (hbp 0)] at hv0
  simp only [hb] at hv0
  have : 0 ≤ (1 - β) * a 0 / σ := by linarith
  rw [le_div_iff₀ hσ0, zero_mul] at this
  nlinarith

/-! ### The settle-or-continue probability space -/

/-- Cochrane (2023), §9.3.2, p. 267: the probability that the target settles at date `k + 1`,
`p (1 − p)ᵏ`. -/
noncomputable def gw (p : ℝ) (k : ℕ) : ℝ := p * (1 - p) ^ k

/-- Cochrane (2023), §9.3.2, p. 267: every settlement date has positive probability. -/
theorem gw_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (k : ℕ) : 0 < gw p k := by
  unfold gw
  have : 0 < 1 - p := by linarith
  positivity

/-- Cochrane (2023), §9.3.2, p. 267: `∑_{k<n} p (1 − p)ᵏ = 1 − (1 − p)ⁿ`. -/
theorem sum_gw (p : ℝ) (n : ℕ) : ∑ k ∈ Finset.range n, gw p k = 1 - (1 - p) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, gw, pow_succ]
    ring

/-- Cochrane (2023), §9.3.2, p. 267: the settlement probabilities sum to one. -/
theorem hasSum_gw {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : HasSum (gw p) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => (gw_pos hp0 hp1 k).le)]
  simp_rw [sum_gw]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0 : ℝ) ≤ 1 - p)
    (by linarith : 1 - p < 1)).const_sub (1 : ℝ)

/-- Cochrane (2023), §9.3.2, p. 267: the law of the settlement date, `∑_k p (1 − p)ᵏ δ_k`. -/
noncomputable def gMeasure (p : ℝ) : Measure ℕ :=
  Measure.sum fun k => ENNReal.ofReal (gw p k) • Measure.dirac k

/-- Cochrane (2023), §9.3.2, p. 267: the measure of a set of settlement dates. -/
theorem gMeasure_apply (p : ℝ) (s : Set ℕ) :
    gMeasure p s = ∑' k, s.indicator (fun k => ENNReal.ofReal (gw p k)) k := by
  rw [gMeasure, Measure.sum_apply _ (MeasurableSet.of_discrete)]
  refine tsum_congr fun k => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases h : k ∈ s <;> simp [h]

/-- Cochrane (2023), §9.3.2, p. 267: `P(settle at k + 1) = p (1 − p)ᵏ`. -/
theorem gMeasure_singleton (p : ℝ) (j : ℕ) : gMeasure p {j} = ENNReal.ofReal (gw p j) := by
  rw [gMeasure_apply, tsum_eq_single j (fun k hk => by simp [hk])]
  simp

/-- Cochrane (2023), §9.3.2, p. 267: the settlement-date law is a probability measure. -/
theorem gMeasure_univ {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : gMeasure p Set.univ = 1 := by
  rw [gMeasure_apply]
  simp only [Set.indicator_univ]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (gw_pos hp0 hp1 k).le)
    (hasSum_gw hp0 hp1).summable, (hasSum_gw hp0 hp1).tsum_eq, ENNReal.ofReal_one]

/-- Cochrane (2023), §9.3.2, p. 267: the settle-or-continue target system — `Ω = ℕ` with the
geometric settlement law and the tree's information, Mathlib's conditional expectation. -/
noncomputable def gSys {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : MeasExpectationSystem ℕ :=
  ⟨⟨gMeasure p, ⟨gMeasure_univ hp0 hp1⟩⟩, SunspotMeasure.sunFiltration⟩

/-- Cochrane (2023), §9.3.2, p. 267: the measure of `gSys`. -/
theorem gSys_μ {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : (gSys hp0 hp1).μ = gMeasure p := rfl

/-- Cochrane (2023), §9.3.2, p. 267: every state has positive probability. -/
theorem gSys_full {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ω : ℕ) : (gSys hp0 hp1).μ {ω} ≠ 0 := by
  rw [gSys_μ, gMeasure_singleton, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact gw_pos hp0 hp1 ω

/-- Cochrane (2023), §9.3.2, p. 267: on `gSys` an a.e. statement holds at every state. -/
theorem ae_at {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {q : ℕ → Prop}
    (h : ∀ᵐ ω ∂(gSys hp0 hp1).μ, q ω) (ω : ℕ) : q ω := by
  by_contra hq
  exact gSys_full hp0 hp1 ω (measure_mono_null (fun x hx => by
    rw [Set.mem_singleton_iff.1 hx]; exact hq) (ae_iff.1 h))

/-- Cochrane (2023), §9.3.2, p. 267: `P(settle at k + 1) = p (1 − p)ᵏ` (real form). -/
theorem gReal_singleton {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (k : ℕ) :
    (gMeasure p).real {k} = gw p k := by
  rw [measureReal_def, gMeasure_singleton, ENNReal.toReal_ofReal (gw_pos hp0 hp1 k).le]

/-- Cochrane (2023), §9.3.2, p. 267: the probability of not having settled by date `n`,
`(1 − p)ⁿ`. -/
theorem gReal_Ici {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    (gMeasure p).real (Set.Ici n) = (1 - p) ^ n := by
  have : IsProbabilityMeasure (gMeasure p) := ⟨gMeasure_univ hp0 hp1⟩
  have h1 : Set.Ici n = (↑(Finset.range n) : Set ℕ)ᶜ := by
    ext k
    simp
  rw [h1, probReal_compl_eq_one_sub MeasurableSet.of_discrete, ← sum_measureReal_singleton]
  simp_rw [gReal_singleton hp0 hp1]
  rw [sum_gw]
  ring

/-- Cochrane (2023), §9.3.2, p. 267: Mathlib's conditional expectation on `gSys` — the value on a
settled state, the average over the unsettled cell `{ω ≥ t}` otherwise. -/
theorem g_E {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (t : ℕ) {X : ℕ → ℝ}
    (hX : Integrable X (gMeasure p)) :
    (gSys hp0 hp1).E t X = fun ω => if t ≤ ω then
      (∫ ω in Set.Ici t, X ω ∂gMeasure p) / (1 - p) ^ t else X ω := by
  set S := gSys hp0 hp1
  have hX' : Integrable X S.μ := hX
  set a := (∫ ω in Set.Ici t, X ω ∂gMeasure p) / (1 - p) ^ t with ha
  set g : ℕ → ℝ := fun ω => if t ≤ ω then a else X ω with hg
  set G : Option ℕ → ℝ := fun x => x.elim a fun m => X (m - 1) with hG
  have hgG : g = G ∘ SunspotMeasure.node t := by
    funext ω
    rcases Nat.lt_or_ge ω t with h | h
    · simp [hg, hG, SunspotMeasure.node_of_lt h, Nat.not_le.mpr h]
    · simp [hg, hG, SunspotMeasure.node_of_le h, h]
  have hgm : StronglyMeasurable[S.𝓕 t] g := by
    have : Measurable[S.𝓕 t] g := by
      rw [hgG]
      exact fun U _ => MeasurableSpace.measurableSet_comap.2
        ⟨G ⁻¹' U, MeasurableSpace.measurableSet_top, rfl⟩
    exact this.stronglyMeasurable
  have hgi : Integrable g S.μ := by
    refine Integrable.mono' (hX'.abs.add (integrable_const |a|))
      Measurable.of_discrete.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    simp only [hg, Pi.add_apply]
    split_ifs
    · linarith [abs_nonneg (X ω)]
    · linarith [abs_nonneg a]
  have hct : 0 < (1 - p) ^ t := pow_pos (by linarith) t
  refine (S.eq_of_ae_eq (gSys_full hp0 hp1)
    (ae_eq_condExp_of_forall_setIntegral_eq (S.𝓕.le t) hX' (fun _ _ _ => hgi.integrableOn)
      (fun A hA _ => ?_) hgm.aestronglyMeasurable)).symm
  obtain ⟨B, -, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  rw [← integral_inter_add_sdiff (measurableSet_Ici (a := t)) hgi.integrableOn,
    ← integral_inter_add_sdiff (measurableSet_Ici (a := t)) hX'.integrableOn]
  congr 1
  · by_cases hB : none ∈ B
    · have hset : SunspotMeasure.node t ⁻¹' B ∩ Set.Ici t = Set.Ici t := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici, and_iff_right_iff_imp]
        intro h
        rw [SunspotMeasure.node_of_le h]
        exact hB
      rw [hset, setIntegral_congr_fun measurableSet_Ici (g := fun _ => a)
        (fun ω hω => by simp [hg, Set.mem_Ici.1 hω]), setIntegral_const, smul_eq_mul]
      rw [gSys_μ, gReal_Ici hp0 hp1, ha]
      field_simp
    · have hset : SunspotMeasure.node t ⁻¹' B ∩ Set.Ici t = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro hω h
        rw [SunspotMeasure.node_of_le h] at hω
        exact hB hω
      rw [hset]
      simp
  · refine setIntegral_congr_fun (MeasurableSet.of_discrete) fun ω hω => ?_
    have : ¬ t ≤ ω := fun h => hω.2 (Set.mem_Ici.2 h)
    simp [hg, this]

/-- Cochrane (2023), §9.3.2, p. 267: at the continue node of date `t`, the conditional expectation
of a variable that is constant on the states not settled by `t + 1` is
`p X(settle at t + 1) + (1 − p) X(continue)`. -/
theorem g_E_cont {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {t ω : ℕ} (hω : t ≤ ω) {X : ℕ → ℝ}
    (hX : Integrable X (gMeasure p)) (hc : ∀ k, t + 1 ≤ k → X k = X (t + 1)) :
    (gSys hp0 hp1).E t X ω = p * X t + (1 - p) * X (t + 1) := by
  rw [g_E hp0 hp1 t hX]
  simp only [hω, ↓reduceIte]
  have hset : Set.Ici t = {t} ∪ Set.Ici (t + 1) := by
    ext k
    simp only [Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff]
    omega
  have hdisj : Disjoint ({t} : Set ℕ) (Set.Ici (t + 1)) := by
    rw [Set.disjoint_singleton_left, Set.mem_Ici]
    omega
  rw [hset, setIntegral_union hdisj measurableSet_Ici hX.integrableOn hX.integrableOn,
    integral_singleton, gReal_singleton hp0 hp1, smul_eq_mul,
    setIntegral_congr_fun measurableSet_Ici (g := fun _ => X (t + 1))
      (fun k hk => hc k (Set.mem_Ici.1 hk)), setIntegral_const, smul_eq_mul,
    gReal_Ici hp0 hp1, gw]
  have : (0 : ℝ) < (1 - p) ^ t := pow_pos (by linarith) t
  field_simp
  ring

/-- Cochrane (2023), §9.3.2, p. 267: on a state settled by `t` the conditional expectation is the
realised value. -/
theorem g_E_settled {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {t ω : ℕ} (hω : ω < t) {X : ℕ → ℝ}
    (hX : Integrable X (gMeasure p)) : (gSys hp0 hp1).E t X ω = X ω := by
  rw [g_E hp0 hp1 t hX]
  simp [Nat.not_le.mpr hω]

/-- Cochrane (2023), §9.3.2, p. 267: a variable known at `t` takes one value on the unsettled cell
`{ω ≥ t}`. -/
theorem meas_cell {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {t : ℕ} {f : ℕ → ℝ}
    (hf : StronglyMeasurable[(gSys hp0 hp1).𝓕 t] f) {ω ω' : ℕ} (hω : t ≤ ω) (hω' : t ≤ ω') :
    f ω = f ω' := by
  have hs : MeasurableSet[(gSys hp0 hp1).𝓕 t] (f ⁻¹' {f ω}) :=
    hf.measurable (measurableSet_singleton _)
  obtain ⟨B, -, hB⟩ := MeasurableSpace.measurableSet_comap.1 hs
  have h1 : ω ∈ SunspotMeasure.node t ⁻¹' B := by rw [hB]; rfl
  have h2 : ω' ∈ SunspotMeasure.node t ⁻¹' B := by
    simp only [Set.mem_preimage] at h1 ⊢
    rwa [SunspotMeasure.node_of_le hω', ← SunspotMeasure.node_of_le hω]
  rw [hB] at h2
  exact h2.symm

/-- Cochrane (2023), §9.3.2, p. 267 (**news at infinitely many dates**): `gSys` is never resolved:
whether the target settles at `T + 1` is news at `T + 1`. -/
theorem not_resolved {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (T : ℕ) :
    ¬ EventuallyResolved (gSys hp0 hp1) T := by
  intro hres
  have hs : MeasurableSet[(gSys hp0 hp1).𝓕 (T + 1)] {T} := by
    refine MeasurableSpace.measurableSet_comap.2 ⟨{some (T + 1)},
      MeasurableSpace.measurableSet_top, ?_⟩
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rcases Nat.lt_or_ge ω (T + 1) with h | h
    · rw [SunspotMeasure.node_of_lt h, Option.some.injEq]
      constructor
      · intro e; omega
      · intro e; omega
    · rw [SunspotMeasure.node_of_le h]
      constructor
      · intro e; exact absurd e (by simp)
      · intro e; omega
  have hs' := hres (T + 1) (by omega) _ hs
  obtain ⟨B, -, hB⟩ := MeasurableSpace.measurableSet_comap.1 hs'
  have h1 : T ∈ SunspotMeasure.node T ⁻¹' B := by rw [hB]; rfl
  have h2 : T + 1 ∈ SunspotMeasure.node T ⁻¹' B := by
    simp only [Set.mem_preimage] at h1 ⊢
    rwa [SunspotMeasure.node_of_le (by omega : T ≤ T + 1), ← SunspotMeasure.node_of_le le_rfl]
  rw [hB] at h2
  simp at h2

/-- Cochrane (2023), §9.3.2, p. 267: the settle-or-continue target, `P*_t = 1` before settlement
and `P*_t = σ` once settled. -/
noncomputable def tgtS (σ : ℝ) (t ω : ℕ) : ℝ := if t ≤ ω then 1 else σ

/-- Cochrane (2023), §9.3.2, p. 267: the target is adapted. -/
theorem tgtS_adapted {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (σ : ℝ) :
    StronglyAdapted (gSys hp0 hp1).𝓕 (tgtS σ) := fun t => by
  set G : Option ℕ → ℝ := fun x => x.elim 1 fun _ => σ with hG
  have e : tgtS σ t = fun ω => G (SunspotMeasure.node t ω) := by
    funext ω
    rcases Nat.lt_or_ge ω t with h | h
    · simp [tgtS, hG, SunspotMeasure.node_of_lt h, Nat.not_le.mpr h]
    · simp [tgtS, hG, SunspotMeasure.node_of_le h, h]
  rw [e]
  have : Measurable[(gSys hp0 hp1).𝓕 t] (fun ω => G (SunspotMeasure.node t ω)) :=
    fun U _ => MeasurableSpace.measurableSet_comap.2
      ⟨G ⁻¹' U, MeasurableSpace.measurableSet_top, rfl⟩
  exact this.stronglyMeasurable

/-- Cochrane (2023), §9.3.2, p. 267: for `σ ≥ 1` the target satisfies `1 ≤ P* ≤ σ`. -/
theorem tgtS_bounds {σ : ℝ} (hσ : 1 ≤ σ) (t ω : ℕ) : 1 ≤ tgtS σ t ω ∧ tgtS σ t ω ≤ σ := by
  unfold tgtS
  split_ifs <;> constructor <;> linarith

/-! ### Equilibria on the settle-or-continue system -/

/-- Cochrane (2023), eq. (9.9), p. 266 (supporting lemma): a bounded sequence with
`z_k = c + β z_{k+1}`, `0 < β < 1`, is the constant `c/(1 − β)`; in particular `z_0 = c/(1 − β)`. -/
theorem geom_fix {β c K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {z : ℕ → ℝ}
    (hz : ∀ k, z k = c + β * z (k + 1)) (hK : ∀ k, |z k| ≤ K) : z 0 = c / (1 - β) := by
  have h1β : 1 - β ≠ 0 := by linarith
  set w : ℕ → ℝ := fun k => z k - c / (1 - β) with hw
  have hrec : ∀ k, w k = β * w (k + 1) := fun k => by
    simp only [hw]
    rw [hz k]
    field_simp
    ring
  have hiter : ∀ n, w 0 = β ^ n * w n := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [ih, hrec n, pow_succ]; ring
  have hwK : ∀ n, |w n| ≤ K + |c / (1 - β)| := fun n =>
    (abs_sub _ _).trans (add_le_add (hK n) le_rfl)
  have hlim : Tendsto (fun n => β ^ n * (K + |c / (1 - β)|)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
      (K + |c / (1 - β)|)
  have h0 : |w 0| ≤ 0 := ge_of_tendsto' hlim fun n => by
    rw [hiter n, abs_mul, abs_of_pos (pow_pos hβ0 n)]
    exact mul_le_mul_of_nonneg_left (hwK n) (pow_pos hβ0 n).le
  have : w 0 = 0 := abs_nonpos_iff.1 h0
  simp only [hw] at this
  linarith

/-- Cochrane (2023), §9.3.2, p. 267: the scaled debt deviation `θ⁻¹ (b_t − b̄)` on the
continuation path (at the continue node of date `t`). -/
noncomputable def aC (θ bbar : ℝ) (b : ℕ → ℕ → ℝ) (t : ℕ) : ℝ := θ⁻¹ * (b t t - bbar)

/-- Cochrane (2023), eq. (9.12), p. 267: on `gSys`, if (9.12) holds at date `s`, the price ratio
`P_s/P_{s+1}` is integrable (otherwise its conditional expectation would be `0`, while the
target's is positive). -/
theorem ratio_integrable {p σ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hσ : 1 ≤ σ) {P : ℕ → ℕ → ℝ}
    (s : ℕ) (hrate : (gSys hp0 hp1).E s (P s / P (s + 1)) =ᵐ[(gSys hp0 hp1).μ]
      (gSys hp0 hp1).E s (tgtS σ s / tgtS σ (s + 1))) :
    Integrable (P s / P (s + 1)) (gMeasure p) ∧
      Integrable (tgtS σ s / tgtS σ (s + 1)) (gMeasure p) := by
  have hTi : Integrable (tgtS σ s / tgtS σ (s + 1)) (gMeasure p) := by
    have : IsProbabilityMeasure (gMeasure p) := ⟨gMeasure_univ hp0 hp1⟩
    refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable σ
      (Eventually.of_forall fun ω => ?_)
    have h1 := tgtS_bounds hσ s ω
    have h2 := tgtS_bounds hσ (s + 1) ω
    rw [Real.norm_eq_abs, Pi.div_apply, abs_of_pos (div_pos (by linarith) (by linarith)),
      div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨?_, hTi⟩
  by_contra hint
  have h0 := ae_at hp0 hp1 hrate 0
  have hz : (gSys hp0 hp1).E s (P s / P (s + 1)) = 0 := condExp_of_not_integrable hint
  rw [hz] at h0
  rcases Nat.lt_or_ge 0 s with h | h
  · rw [g_E_settled hp0 hp1 h hTi] at h0
    have h1 := tgtS_bounds hσ s 0
    have h2 := tgtS_bounds hσ (s + 1) 0
    simp only [Pi.zero_apply, Pi.div_apply] at h0
    have := div_pos (by linarith : (0 : ℝ) < tgtS σ s 0) (by linarith : (0 : ℝ) < tgtS σ (s + 1) 0)
    linarith
  · rw [g_E hp0 hp1 s hTi] at h0
    simp only [h, ↓reduceIte, Pi.zero_apply] at h0
    have hpos : 0 < ∫ ω in Set.Ici s, (tgtS σ s / tgtS σ (s + 1)) ω ∂gMeasure p := by
      have hs0 : s = 0 := by omega
      subst hs0
      rw [setIntegral_pos_iff_support_of_nonneg_ae]
      · refine (lt_of_lt_of_le ?_ (measure_mono (s := {0}) ?_))
        · rw [gMeasure_singleton]
          exact ENNReal.ofReal_pos.2 (gw_pos hp0 hp1 0)
        · intro k hk
          rw [Set.mem_singleton_iff.1 hk]
          refine ⟨?_, Set.mem_Ici.2 le_rfl⟩
          simp only [Function.mem_support, Pi.div_apply, ne_eq, div_eq_zero_iff, not_or]
          have h1 := tgtS_bounds hσ 0 0
          have h2 := tgtS_bounds hσ 1 0
          constructor <;> linarith
      · refine Eventually.of_forall fun ω => ?_
        have h1 := tgtS_bounds hσ 0 ω
        have h2 := tgtS_bounds hσ 1 ω
        simp only [Pi.zero_apply, Pi.div_apply]
        exact (div_pos (by linarith) (by linarith)).le
      · exact hTi.integrableOn
    have : 0 < (1 - p) ^ s := pow_pos (by linarith) s
    have := div_pos hpos this
    linarith

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the equilibrium on the continuation path**): every
equilibrium of the rule on `gSys` with target `tgtS σ` (`σ ≥ 1`) and prices bounded above
satisfies, with `a_t = aC θ b̄ b t` and `x_t = P_t` at the continue node:
the flow `a_t = x_t − 1 + β a_{t+1}`; the settled price `P_{t+1} = σ + (1 − β) a_{t+1}` on the
state that settles at `t + 1`; the interest-rate target
`x_t (p/(σ + (1 − β) a_{t+1}) + (1 − p)/x_{t+1}) = p/σ + 1 − p`; and `a` is bounded. -/
theorem continuation_relations {p β θ bbar σ M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 ≤ σ) {P b : ℕ → ℕ → ℝ}
    (hE : RuleEqm (gSys hp0 hp1) β θ bbar (tgtS σ) P b) (hPM : ∀ t ω, P t ω ≤ M) :
    (∀ t, aC θ bbar b t = P t t - 1 + β * aC θ bbar b (t + 1)) ∧
    (∀ t, P (t + 1) t = σ + (1 - β) * aC θ bbar b (t + 1)) ∧
    (∀ t, P t t * (p / (σ + (1 - β) * aC θ bbar b (t + 1)) + (1 - p) / P (t + 1) (t + 1)) =
      p / σ + (1 - p)) ∧
    ∃ K, ∀ t, aC θ bbar b t ≤ K := by
  have hEc := hE
  obtain ⟨hP, hPa, -, -, hrate, hflow, hpre, -, -⟩ := hE
  set D : ℕ → ℕ → ℝ := fun t ω => θ⁻¹ * (b t ω - bbar) with hD
  have hDflow : ∀ t ω, D t ω = P t ω - tgtS σ t ω + β * D (t + 1) ω := fun t ω => by
    simp only [hD]
    rw [hflow t ω]
    field_simp
    ring
  have hDcell : ∀ t ω ω', t ≤ ω → t ≤ ω' → D (t + 1) ω = D (t + 1) ω' := fun t ω ω' h h' => by
    simp only [hD]
    rw [meas_cell hp0 hp1 (hpre t) h h']
  have hPcell : ∀ t ω ω', t ≤ ω → t ≤ ω' → P t ω = P t ω' := fun t ω ω' h h' =>
    meas_cell hp0 hp1 (hPa t) h h'
  -- bounded debt
  have hbK := fun t => ae_at hp0 hp1 (TidyR5FiscalLink.debt_bdd_rule (gSys hp0 hp1) hβ0 hβ1
    (tgtS_adapted hp0 hp1 σ) one_pos (fun t ω => tgtS_bounds hσ t ω) hEc hPM t)
  set Kb := (|(1 - β) * bbar| + |θ| * (M + σ)) / (1 - β) with hKb
  have hDK : ∀ t ω, |D t ω| ≤ |θ⁻¹| * (Kb + |bbar|) := fun t ω => by
    simp only [hD]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hbK t ω) le_rfl))
      (abs_nonneg _)
  -- after settlement the price is constant
  have hsettled : ∀ s ω, ω < s → P (s + 1) ω = P s ω := fun s ω hω => by
    obtain ⟨hXi, hTi⟩ := ratio_integrable hp0 hp1 hσ s (hrate s)
    have h := ae_at hp0 hp1 (hrate s) ω
    rw [g_E_settled hp0 hp1 hω hXi, g_E_settled hp0 hp1 hω hTi] at h
    simp only [Pi.div_apply, tgtS, Nat.not_le.mpr hω,
      Nat.not_le.mpr (Nat.lt_succ_of_lt hω), ↓reduceIte] at h
    have hσ0 : σ ≠ 0 := by linarith
    rw [div_self hσ0, div_eq_one_iff_eq (hP (s + 1) ω).ne'] at h
    exact h.symm
  have hsett2 : ∀ t k, P (t + 1 + k) t = P (t + 1) t := fun t k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [← add_assoc, hsettled (t + 1 + k) t (by omega), ih]
  have hsetD : ∀ t, P (t + 1) t = σ + (1 - β) * aC θ bbar b (t + 1) := fun t => by
    have hz := geom_fix hβ0 hβ1 (z := fun k => D (t + 1 + k) t) (c := P (t + 1) t - σ)
      (K := |θ⁻¹| * (Kb + |bbar|)) (fun k => by
        rw [hDflow (t + 1 + k) t, hsett2 t k]
        simp only [tgtS, Nat.not_le.mpr (show t < t + 1 + k by omega), ↓reduceIte]
        rw [show t + 1 + k + 1 = t + 1 + (k + 1) by ring]) (fun k => hDK _ _)
    simp only [add_zero] at hz
    have e : D (t + 1) t = aC θ bbar b (t + 1) := by
      simp only [aC]
      exact hDcell t t (t + 1) le_rfl (by omega)
    rw [e] at hz
    have h1β : 1 - β ≠ 0 := by linarith
    rw [hz]
    field_simp
    ring
  refine ⟨fun t => ?_, hsetD, fun t => ?_, ⟨|θ⁻¹| * (Kb + |bbar|), fun t =>
    (le_abs_self _).trans (hDK t t)⟩⟩
  · have h := hDflow t t
    simp only [tgtS, le_refl, ↓reduceIte] at h
    have e : D (t + 1) t = aC θ bbar b (t + 1) := by
      simp only [aC]
      exact hDcell t t (t + 1) le_rfl (by omega)
    simp only [aC] at e ⊢
    rw [← e]
    exact h
  · obtain ⟨hXi, hTi⟩ := ratio_integrable hp0 hp1 hσ t (hrate t)
    have h := ae_at hp0 hp1 (hrate t) t
    have hcX : ∀ k, t + 1 ≤ k → (P t / P (t + 1)) k = (P t / P (t + 1)) (t + 1) := fun k hk => by
      simp only [Pi.div_apply]
      rw [hPcell t k (t + 1) (by omega) (by omega), hPcell (t + 1) k (t + 1) hk le_rfl]
    have hcT : ∀ k, t + 1 ≤ k → (tgtS σ t / tgtS σ (t + 1)) k =
        (tgtS σ t / tgtS σ (t + 1)) (t + 1) := fun k hk => by
      simp only [Pi.div_apply, tgtS, show t ≤ k by omega, hk, ↓reduceIte, le_refl,
        show t ≤ t + 1 by omega]
    rw [g_E_cont hp0 hp1 le_rfl hXi hcX, g_E_cont hp0 hp1 le_rfl hTi hcT] at h
    simp only [Pi.div_apply, tgtS, le_refl, ↓reduceIte, show t ≤ t + 1 by omega,
      show ¬ t + 1 ≤ t by omega, div_one] at h
    rw [hPcell t (t + 1) t (by omega) le_rfl, hsetD t] at h
    have e : P t t * (p / (σ + (1 - β) * aC θ bbar b (t + 1)) + (1 - p) / P (t + 1) (t + 1)) =
        p * (P t t / (σ + (1 - β) * aC θ bbar b (t + 1))) +
          (1 - p) * (P t t / P (t + 1) (t + 1)) := by ring
    rw [e, h]
    ring

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**`d₀ ≥ 0` is not sufficient for existence**): on the
settle-or-continue system with `σ > 1`, for every `0 < β < 1`, `0 < p < 1`, `θ ≠ 0` and `b̄`, an
equilibrium of the rule with prices bounded above and initial debt `b₀ = b̄ + θ d₀` forces
`d₀ ≤ 0`: there is none for any `d₀ > 0`. -/
theorem no_eqm_pos {p β θ bbar σ M d0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) {P b : ℕ → ℕ → ℝ}
    (hE : RuleEqm (gSys hp0 hp1) β θ bbar (tgtS σ) P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hb0 : ∀ ω, b 0 ω = bbar + θ * d0) : d0 ≤ 0 := by
  obtain ⟨h1, h2, h3, K, hK⟩ := continuation_relations hp0 hp1 hβ0 hβ1 hθ hσ.le hE hPM
  have hP := hE.1
  have ha0 : aC θ bbar b 0 = d0 := by
    simp only [aC, hb0 0]
    field_simp
    ring
  rw [← ha0]
  exact orbit_nonpos hβ0 hβ1 hσ hp0 hp1 (x := fun t => P t t) (fun t => hP t t)
    (fun t => by rw [← h2 t]; exact hP _ _) h1 h3 (fun t => hPM t t) hK

/-- Cochrane (2023), §9.3.2, pp. 266–267: on the settle-or-continue system with `σ > 1`, an
equilibrium with prices bounded above and bounded away from zero and `b₀ = b̄ + θ d₀` forces
`d₀ ≥ 0` (and hence, by `no_eqm_pos`, `d₀ = 0`). -/
theorem no_eqm_neg {p β θ bbar σ M mP d0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) {P b : ℕ → ℕ → ℝ}
    (hE : RuleEqm (gSys hp0 hp1) β θ bbar (tgtS σ) P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hmP : 0 < mP) (hPm : ∀ t ω, mP ≤ P t ω) (hb0 : ∀ ω, b 0 ω = bbar + θ * d0) : 0 ≤ d0 := by
  obtain ⟨h1, h2, h3, -⟩ := continuation_relations hp0 hp1 hβ0 hβ1 hθ hσ.le hE hPM
  have ha0 : aC θ bbar b 0 = d0 := by
    simp only [aC, hb0 0]
    field_simp
    ring
  rw [← ha0]
  exact orbit_nonneg hβ0 hβ1 hσ hp0 hp1 hmP (x := fun t => P t t) (fun t => hPm t t)
    (fun t => by rw [← h2 t]; exact hPm _ _) h1 h3

/-- Cochrane (2023), §9.3.2, p. 267: existence of an equilibrium of the rule with prices bounded
above (and integrable `1/P`) and initial debt `b₀ = b̄ + θ d₀` — the notion of
`FiscalRulesTargetFinal.exists_iff_pathwise`. -/
def ExistsAbove {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω) (β θ bbar : ℝ)
    (Pstar : ℕ → Ω → ℝ) (d0 : ℝ) : Prop :=
  ∃ (P b : ℕ → Ω → ℝ) (M : ℝ), RuleEqm S β θ bbar Pstar P b ∧ (∀ t ω, P t ω ≤ M) ∧
    (∀ t, Integrable (fun ω => 1 / P t ω) S.μ) ∧ ∀ ω, b 0 ω = bbar + θ * d0

/-- Cochrane (2023), §9.3.2, p. 267: existence of an equilibrium with prices bounded above and
bounded away from zero and initial debt `b₀ = b̄ + θ d₀`. -/
def ExistsBoth {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω) (β θ bbar : ℝ)
    (Pstar : ℕ → Ω → ℝ) (d0 : ℝ) : Prop :=
  ∃ (P b : ℕ → Ω → ℝ) (M mP : ℝ), RuleEqm S β θ bbar Pstar P b ∧ (∀ t ω, P t ω ≤ M) ∧
    0 < mP ∧ (∀ t ω, mP ≤ P t ω) ∧ ∀ ω, b 0 ω = bbar + θ * d0

/-- Cochrane (2023), §9.3.2, pp. 266–267: on every system, for every adapted target
`0 < m ≤ P* ≤ M*`, the target itself is an equilibrium with `b₀ = b̄` (`d₀ = 0`), with prices
bounded above and away from zero. -/
theorem exists_zero {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)
    {β θ bbar m Ms : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Pstar : ℕ → Ω → ℝ}
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) :
    ExistsAbove S β θ bbar Pstar 0 ∧ ExistsBoth S β θ bbar Pstar 0 := by
  have hzero : ∀ t ω, fwdDebt β 0 Pstar Pstar t ω = 0 := by
    intro t
    induction t with
    | zero => intro ω; rfl
    | succ t ih => intro ω; simp [fwdDebt, ih ω]
  have hE := eqm_of_bdd S hβ0 hβ1 (θ := θ) (bbar := bbar) (K := 0) hPsa hm hPs
    (fun t ω => hm.trans_le (hPs t ω).1) hPsa (fun t ω => (hPs t ω).2)
    (fun _ => EventuallyEq.rfl) (fun t => Eventually.of_forall fun ω => by rw [hzero]; simp)
  have hq : ∀ t, Integrable (fun ω => 1 / Pstar t ω) S.μ := fun t =>
    Integrable.of_bound ((((hPsa t).measurable.const_div 1).stronglyMeasurable.mono
      (S.𝓕.le t))).aestronglyMeasurable (1 / m) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hm.trans_le (hPs t ω).1))]
        exact one_div_le_one_div_of_le hm (hPs t ω).1)
  exact ⟨⟨_, _, Ms, hE, fun t ω => (hPs t ω).2, hq, fun ω => by simp [hzero]⟩,
    ⟨_, _, Ms, m, hE, fun t ω => (hPs t ω).2, hm, fun t ω => (hPs t ω).1,
      fun ω => by simp [hzero]⟩⟩

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**exact existence on the settle-or-continue system**):
with `σ > 1`, an equilibrium with prices bounded above and away from zero and `b₀ = b̄ + θ d₀`
exists **iff** `d₀ = 0`. -/
theorem existsBoth_iff {p β θ bbar σ d0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) :
    ExistsBoth (gSys hp0 hp1) β θ bbar (tgtS σ) d0 ↔ d0 = 0 := by
  constructor
  · rintro ⟨P, b, M, mP, hE, hPM, hmP, hPm, hb0⟩
    exact le_antisymm (no_eqm_pos hp0 hp1 hβ0 hβ1 hθ hσ hE hPM hb0)
      (no_eqm_neg hp0 hp1 hβ0 hβ1 hθ hσ hE hPM hmP hPm hb0)
  · rintro rfl
    exact (exists_zero _ hβ0 hβ1 (tgtS_adapted hp0 hp1 σ) one_pos
      (fun t ω => tgtS_bounds hσ.le t ω)).2

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the existence set is not upward-closed**): on the
settle-or-continue system with `σ > 1`, an equilibrium with prices bounded above exists for
`d₀ = 0` and for no `d₀ > 0`; so no condition of the form `d₀ > c` or `d₀ ≥ c` (`c` any function
of the primitives) — in particular not `d₀ ≥ 0` — characterises existence on every system. -/
theorem existsAbove_not_upward_closed {p β θ bbar σ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) :
    ExistsAbove (gSys hp0 hp1) β θ bbar (tgtS σ) 0 ∧
      (∀ d0, 0 < d0 → ¬ ExistsAbove (gSys hp0 hp1) β θ bbar (tgtS σ) d0) ∧
      ¬ ∀ d d', ExistsAbove (gSys hp0 hp1) β θ bbar (tgtS σ) d → d ≤ d' →
        ExistsAbove (gSys hp0 hp1) β θ bbar (tgtS σ) d' := by
  have h0 := (exists_zero (gSys hp0 hp1) hβ0 hβ1 (θ := θ) (bbar := bbar)
    (tgtS_adapted hp0 hp1 σ) one_pos (fun t ω => tgtS_bounds hσ.le t ω)).1
  have hno : ∀ d0, 0 < d0 → ¬ ExistsAbove (gSys hp0 hp1) β θ bbar (tgtS σ) d0 := by
    rintro d0 hd ⟨P, b, M, hE, hPM, -, hb0⟩
    have := no_eqm_pos hp0 hp1 hβ0 hβ1 hθ hσ hE hPM hb0
    linarith
  exact ⟨h0, hno, fun h => hno 1 one_pos (h 0 1 h0 zero_le_one)⟩

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the existence set need not be open**): on the
settle-or-continue system with `σ > 1` the set of `d₀` admitting an equilibrium with prices bounded
above and away from zero is `{0}`, which is not open; so no condition given by strict inequalities
continuous in `d₀` (as the explicit conditions for one-shot news and predetermined target values
are) characterises existence. -/
theorem existsBoth_not_open {p β θ bbar σ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) :
    {d0 | ExistsBoth (gSys hp0 hp1) β θ bbar (tgtS σ) d0} = {0} ∧
      ¬ IsOpen {d0 | ExistsBoth (gSys hp0 hp1) β θ bbar (tgtS σ) d0} := by
  have e : {d0 | ExistsBoth (gSys hp0 hp1) β θ bbar (tgtS σ) d0} = {0} := by
    ext d0
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact existsBoth_iff hp0 hp1 hβ0 hβ1 hθ hσ
  refine ⟨e, ?_⟩
  rw [e]
  exact not_isOpen_singleton 0

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the existence set is never downward-closed**): on every
system, for every adapted target `0 < m ≤ P* ≤ M*`, an equilibrium with prices bounded above exists
at `d₀ = 0` but not at `d₀ = −M*/(1 − β) − 1` (`FiscalRulesTargetFinal.exists_imp_pos`); so no
condition of the form `d₀ < c` or `d₀ ≤ c` characterises existence either. -/
theorem existsAbove_not_downward_closed {Ω : Type*} [MeasurableSpace Ω]
    (S : MeasExpectationSystem Ω) {β θ bbar m Ms : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {Pstar : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) :
    ExistsAbove S β θ bbar Pstar 0 ∧ ¬ ExistsAbove S β θ bbar Pstar (-(Ms / (1 - β)) - 1) ∧
      ¬ ∀ d d', ExistsAbove S β θ bbar Pstar d' → d ≤ d' → ExistsAbove S β θ bbar Pstar d := by
  have h1β : 0 < 1 - β := by linarith
  have h0 := (exists_zero S hβ0 hβ1 (θ := θ) (bbar := bbar) hPsa hm hPs).1
  have hno : ¬ ExistsAbove S β θ bbar Pstar (-(Ms / (1 - β)) - 1) := by
    intro hex
    have h := exists_imp_pos S hβ0 hβ1 hθ hPsa hm hPs hex
    obtain ⟨ω, hω⟩ := h.exists
    have hs : Summable fun s => β ^ s * Pstar s ω :=
      Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right Ms)
        fun s => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 s),
            abs_of_pos (hm.trans_le (hPs s ω).1)]
          exact mul_le_mul_of_nonneg_left (hPs s ω).2 (pow_pos hβ0 s).le
    have hle : ∑' s, β ^ s * Pstar s ω ≤ Ms / (1 - β) := by
      calc ∑' s, β ^ s * Pstar s ω ≤ ∑' s, β ^ s * Ms :=
            hs.tsum_le_tsum (fun s => mul_le_mul_of_nonneg_left (hPs s ω).2 (pow_pos hβ0 s).le)
              ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right Ms)
        _ = Ms / (1 - β) := by
          rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1, div_eq_inv_mul]
    linarith
  obtain ⟨ω0, -⟩ := (Eventually.of_forall (f := ae S.μ) fun _ : Ω => True.intro).exists
  have hMs : 0 ≤ Ms / (1 - β) := div_nonneg (hm.le.trans ((hPs 0 ω0).1.trans (hPs 0 ω0).2))
    h1β.le
  exact ⟨h0, hno, fun h => hno (h _ 0 h0 (by linarith))⟩

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the counterexample, packaged**): there is a genuine
probability space with news at every date (never resolved) and an adapted target `1 ≤ P* ≤ 2` such
that, for every `0 < β < 1`, `θ ≠ 0` and `b̄`, the target is an equilibrium with `b₀ = b̄`, yet for
**every** `d₀ > 0` there is no equilibrium with prices bounded above and `b₀ = b̄ + θ d₀` — the
conjectured sufficiency of `d₀ ≥ 0` is false. -/
theorem d0_nonneg_not_sufficient {β θ bbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) :
    ∃ (S : MeasExpectationSystem ℕ) (Pstar : ℕ → ℕ → ℝ),
      (∀ T, ¬ EventuallyResolved S T) ∧ StronglyAdapted S.𝓕 Pstar ∧
      (∀ t ω, 1 ≤ Pstar t ω ∧ Pstar t ω ≤ 2) ∧ ExistsAbove S β θ bbar Pstar 0 ∧
      ∀ d0, 0 < d0 → ¬ ExistsAbove S β θ bbar Pstar d0 := by
  have hp0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hp1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨h0, hno, -⟩ := existsAbove_not_upward_closed hp0 hp1 hβ0 hβ1 hθ (σ := 2) (bbar := bbar)
    (by norm_num)
  exact ⟨gSys hp0 hp1, tgtS 2, not_resolved hp0 hp1, tgtS_adapted hp0 hp1 2,
    tgtS_bounds (by norm_num), h0, hno⟩

end Cochrane.AssetsRulesBalanceSheets.TidyR5NoExist
