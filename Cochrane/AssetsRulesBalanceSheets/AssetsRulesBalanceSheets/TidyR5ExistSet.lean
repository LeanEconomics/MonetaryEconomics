/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.TidyR5NoExist

/-!
# Theorem FR (d) on the settle-or-continue target: the exact existence set

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.2,
eqs. (9.8)–(9.12), pp. 266–267 (Theorem FR; stochastic target, `b₀ = b̄ + θ d₀`).

The module TidyR5NoExist (`TidyR5NoExist.no_eqm_pos`) shows that on the settle-or-continue
system (`gSys`, target `tgtS σ`, `σ > 1`) no equilibrium with prices bounded above exists for
`d₀ > 0`, and that with prices also bounded away from zero only `d₀ = 0` works. Here the negative
side is settled: **every** `d₀ ∈ (−1/(1 − β), 0)` admits an equilibrium with prices bounded above
(its continuation prices are not bounded away from zero), and none exists for `d₀ ≤ −1/(1 − β)`.
So the existence set is exactly `(−1/(1 − β), 0]` (`existsAbove_iff`), for every `0 < p < 1`,
`σ > 1`. The lower end is minus the infimum over paths of the realised present value of the
target.

## Construction

The continuation path is a forward orbit of the two-dimensional map given by the flow and (9.12).
It is built backwards: the backward map `bstep` (`D_t = x_t − 1 + β D_{t+1}`,
`x_t = γ/(p/(σ + (1 − β) D_{t+1}) + (1 − p)/x_{t+1})`) maps the box
`[−1/(1 − β), 0] × (0, 1]` into itself (`bstep_mem`). For each horizon `N` the intermediate
value theorem gives a terminal point whose `N`-fold backward image starts at `d₀`
(`finite_orbit`); the continuation prices stay uniformly positive at each date
(`finite_orbit_lower`); a convergent subsequence in the compact product
`∏_t [−1/(1 − β), 0] × [0, 1]` gives an infinite orbit (`infinite_orbit`), and `orbit_eqm` turns
it into an equilibrium of the rule.
-/

namespace Cochrane.AssetsRulesBalanceSheets.TidyR5ExistSet

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure FiscalRulesMeasure FiscalRulesTargetMeasure FiscalRulesTargetFinal
open TidyR5NoExist

/-- Cochrane (2023), eq. (9.12), p. 267: the target's real-rate factor at a continue node of the
settle-or-continue target, `γ = p/σ + (1 − p)`. -/
noncomputable def gam (p σ : ℝ) : ℝ := p / σ + (1 - p)

/-- Cochrane (2023), eq. (9.9), p. 266: `D* = −1/(1 − β)`, minus the present value of the target
along the path that never settles. -/
noncomputable def Dst (β : ℝ) : ℝ := -(1 / (1 - β))

/-- Cochrane (2023), eq. (9.12), p. 267: the date-`t` continuation price implied by (9.12) from
the date-`t + 1` debt deviation `D` and continuation price `x`. -/
noncomputable def bx (p β σ D x : ℝ) : ℝ := gam p σ / (p / (σ + (1 - β) * D) + (1 - p) / x)

/-- Cochrane (2023), eqs. (9.8), (9.12), pp. 266–267: the backward map
`(D_{t+1}, x_{t+1}) ↦ (D_t, x_t)` of the continuation path. -/
noncomputable def bstep (p β σ : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (bx p β σ z.1 z.2 - 1 + β * z.1, bx p β σ z.1 z.2)

/-- Cochrane (2023), §9.3.2, p. 267: the box `[D*, 0] × (0, 1]`. -/
def Box (β : ℝ) : Set (ℝ × ℝ) := {z | Dst β ≤ z.1 ∧ z.1 ≤ 0 ∧ 0 < z.2 ∧ z.2 ≤ 1}

variable {p β σ : ℝ}

/-- Cochrane (2023), eq. (9.9), p. 266: `−1 + β D* = D*` and `σ + (1 − β) D* = σ − 1`. -/
theorem Dst_props (hβ1 : β < 1) : -1 + β * Dst β = Dst β ∧ (1 - β) * Dst β = -1 := by
  have : 1 - β ≠ 0 := by linarith
  constructor
  · simp only [Dst]
    field_simp
    ring
  · simp only [Dst]
    field_simp

/-- Cochrane (2023), eqs. (9.8), (9.12), pp. 266–267 (**the box is invariant under the backward
map**): for `z ∈ [D*, 0] × (0, 1]`, the settled price `σ + (1 − β) D` lies in `[σ − 1, σ]`, the
denominator of `bx` is at least `γ`, `0 < bx ≤ 1`, `bx ≤ γ x/(1 − p)`, and `bstep z` is in the box
with `D`-coordinate `> D*`. -/
theorem bstep_mem (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ)
    {z : ℝ × ℝ} (hz : z ∈ Box β) :
    σ - 1 ≤ σ + (1 - β) * z.1 ∧ gam p σ ≤ p / (σ + (1 - β) * z.1) + (1 - p) / z.2 ∧
      0 < bx p β σ z.1 z.2 ∧ bx p β σ z.1 z.2 ≤ 1 ∧
      bx p β σ z.1 z.2 ≤ gam p σ / (1 - p) * z.2 ∧ bstep p β σ z ∈ Box β ∧
      Dst β < (bstep p β σ z).1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  obtain ⟨e1, e2⟩ := Dst_props hβ1
  have h1β : 0 < 1 - β := by linarith
  have hy : σ - 1 ≤ σ + (1 - β) * z.1 := by nlinarith
  have hyσ : σ + (1 - β) * z.1 ≤ σ := by nlinarith
  have hy0 : 0 < σ + (1 - β) * z.1 := by linarith
  have hγ : 0 < gam p σ := by
    unfold gam
    have : 0 < p / σ := by positivity
    linarith
  have hden : gam p σ ≤ p / (σ + (1 - β) * z.1) + (1 - p) / z.2 := by
    unfold gam
    have a1 : p / σ ≤ p / (σ + (1 - β) * z.1) := div_le_div_of_nonneg_left hp0.le hy0 hyσ
    have a2 : 1 - p ≤ (1 - p) / z.2 := by
      rw [le_div_iff₀ h3]; nlinarith
    linarith
  have hden0 : 0 < p / (σ + (1 - β) * z.1) + (1 - p) / z.2 := hγ.trans_le hden
  have hbx0 : 0 < bx p β σ z.1 z.2 := div_pos hγ hden0
  have hbx1 : bx p β σ z.1 z.2 ≤ 1 := (div_le_one hden0).2 hden
  have hbxx : bx p β σ z.1 z.2 ≤ gam p σ / (1 - p) * z.2 := by
    unfold bx
    have hq : (1 - p) / z.2 ≤ p / (σ + (1 - β) * z.1) + (1 - p) / z.2 := by
      have : 0 ≤ p / (σ + (1 - β) * z.1) := by positivity
      linarith
    calc gam p σ / (p / (σ + (1 - β) * z.1) + (1 - p) / z.2) ≤ gam p σ / ((1 - p) / z.2) :=
          div_le_div_of_nonneg_left hγ.le (by have : 0 < 1 - p := (by linarith); positivity) hq
      _ = gam p σ / (1 - p) * z.2 := by
          have : 1 - p ≠ 0 := by linarith
          field_simp
  refine ⟨hy, hden, hbx0, hbx1, hbxx, ⟨?_, ?_, hbx0, hbx1⟩, ?_⟩
  · simp only [bstep]; nlinarith
  · simp only [bstep]; nlinarith
  · simp only [bstep]; nlinarith

/-- Cochrane (2023), eq. (9.12), p. 267: the backward map is continuous at every point with
`x > 0` and settled price `σ + (1 − β) D > 0`. -/
theorem bstep_continuousAt (hp0 : 0 < p) (hp1 : p < 1) {z : ℝ × ℝ} (hy : 0 < σ + (1 - β) * z.1)
    (hx : 0 < z.2) : ContinuousAt (bstep p β σ) z := by
  have hden0 : 0 < p / (σ + (1 - β) * z.1) + (1 - p) / z.2 := by
    have : 0 < 1 - p := by linarith
    positivity
  have hbx : ContinuousAt (fun z : ℝ × ℝ => bx p β σ z.1 z.2) z := by
    unfold bx
    refine continuousAt_const.div ?_ hden0.ne'
    refine (continuousAt_const.div (continuousAt_const.add
      (continuousAt_const.mul continuousAt_fst)) hy.ne').add
      (continuousAt_const.div continuousAt_snd hx.ne')
  exact ((hbx.sub continuousAt_const).add (continuousAt_const.mul continuousAt_fst)).prodMk hbx

/-- Cochrane (2023), §9.3.2, p. 267: the terminal points `(D*(1 − ξ), ξ)`, `0 < ξ ≤ 1`. -/
noncomputable def term (β ξ : ℝ) : ℝ × ℝ := (Dst β * (1 - ξ), ξ)

/-- Cochrane (2023), §9.3.2, p. 267: the `k`-fold backward image of the terminal point. -/
noncomputable def itr (p β σ ξ : ℝ) : ℕ → ℝ × ℝ
  | 0 => term β ξ
  | k + 1 => bstep p β σ (itr p β σ ξ k)

/-- Cochrane (2023), §9.3.2, p. 267: the backward images stay in the box. -/
theorem itr_mem (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ)
    {ξ : ℝ} (hξ : ξ ∈ Set.Ioc (0 : ℝ) 1) (k : ℕ) : itr p β σ ξ k ∈ Box β := by
  induction k with
  | zero =>
    have hD : Dst β ≤ 0 := by
      have : 0 < 1 / (1 - β) := by have : 0 < 1 - β := (by linarith); positivity
      simp only [Dst]; linarith
    refine ⟨?_, ?_, hξ.1, hξ.2⟩
    · simp only [itr, term]; nlinarith [hξ.1, hξ.2]
    · simp only [itr, term]; nlinarith [hξ.1, hξ.2]
  | succ k ih => exact (bstep_mem hp0 hp1 hβ0 hβ1 hσ ih).2.2.2.2.2.1

/-- Cochrane (2023), §9.3.2, p. 267: each backward image depends continuously on `ξ ∈ (0, 1]`. -/
theorem itr_continuousOn (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ)
    (k : ℕ) : ContinuousOn (fun ξ => itr p β σ ξ k) (Set.Ioc 0 1) := by
  induction k with
  | zero =>
    exact ((continuous_const.mul (continuous_const.sub continuous_id)).prodMk
      continuous_id).continuousOn
  | succ k ih =>
    intro ξ hξ
    have hz := itr_mem hp0 hp1 hβ0 hβ1 hσ hξ k
    have hy := (bstep_mem hp0 hp1 hβ0 hβ1 hσ hz).1
    have hc := (bstep_continuousAt (p := p) (β := β) (σ := σ) hp0 hp1 (by linarith)
      hz.2.2.1).comp_continuousWithinAt (f := fun ξ => itr p β σ ξ k) (ih ξ hξ)
    exact hc

/-- Cochrane (2023), §9.3.2, p. 267: from `ξ = 1` the backward images stay at the target point
`(0, 1)`. -/
theorem itr_one (hp0 : 0 < p) (hp1 : p < 1) (hσ : 1 < σ) (k : ℕ) : itr p β σ 1 k = (0, 1) := by
  induction k with
  | zero => simp [itr, term]
  | succ k ih =>
    have hγ : 0 < p / σ + (1 - p) := by
      have : 0 < p / σ := by have : (0 : ℝ) < σ := (by linarith); positivity
      linarith
    simp only [itr, ih, bstep, bx, gam, mul_zero, add_zero, div_one, div_self hγ.ne']
    simp


/-- Cochrane (2023), eq. (9.12), p. 267: the backward images grow at most geometrically from the
terminal point: with `ρ = γ/(1 − p)`, `x_k ≤ ρᵏ ξ` and `D_k − D* ≤ ξ (−D* + k ρᵏ)`. -/
theorem itr_bounds (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ)
    {ξ : ℝ} (hξ : ξ ∈ Set.Ioc (0 : ℝ) 1) (k : ℕ) :
    (itr p β σ ξ k).2 ≤ (gam p σ / (1 - p)) ^ k * ξ ∧
      (itr p β σ ξ k).1 - Dst β ≤ ξ * (-Dst β + k * (gam p σ / (1 - p)) ^ k) := by
  have hρ : 1 ≤ gam p σ / (1 - p) := by
    rw [le_div_iff₀ (by linarith), one_mul]
    unfold gam
    have : 0 ≤ p / σ := by have : (0 : ℝ) < σ := (by linarith); positivity
    linarith
  obtain ⟨e1, -⟩ := Dst_props hβ1
  induction k with
  | zero =>
    simp only [itr, term, pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero, le_refl,
      true_and]
    nlinarith
  | succ k ih =>
    have hz := itr_mem hp0 hp1 hβ0 hβ1 hσ hξ k
    obtain ⟨-, -, hb0, -, hbx, -, -⟩ := bstep_mem hp0 hp1 hβ0 hβ1 hσ hz
    have hρk : (gam p σ / (1 - p)) ^ k ≤ (gam p σ / (1 - p)) ^ (k + 1) :=
      pow_le_pow_right₀ hρ (Nat.le_succ k)
    have hx1 : (itr p β σ ξ (k + 1)).2 ≤ (gam p σ / (1 - p)) ^ (k + 1) * ξ := by
      change bx p β σ (itr p β σ ξ k).1 (itr p β σ ξ k).2 ≤ _
      calc bx p β σ (itr p β σ ξ k).1 (itr p β σ ξ k).2
          ≤ gam p σ / (1 - p) * (itr p β σ ξ k).2 := hbx
        _ ≤ gam p σ / (1 - p) * ((gam p σ / (1 - p)) ^ k * ξ) :=
          mul_le_mul_of_nonneg_left ih.1 (by linarith)
        _ = (gam p σ / (1 - p)) ^ (k + 1) * ξ := by ring
    refine ⟨hx1, ?_⟩
    have he : (itr p β σ ξ (k + 1)).1 - Dst β =
        (itr p β σ ξ (k + 1)).2 + β * ((itr p β σ ξ k).1 - Dst β) := by
      change bx p β σ _ _ - 1 + β * (itr p β σ ξ k).1 - Dst β = bx p β σ _ _ + _
      linarith
    have hek : 0 ≤ (itr p β σ ξ k).1 - Dst β := by linarith [hz.1]
    rw [he]
    have h2 : β * ((itr p β σ ξ k).1 - Dst β) ≤ (itr p β σ ξ k).1 - Dst β := by nlinarith
    have h3 : ξ * (k * (gam p σ / (1 - p)) ^ k) ≤ ξ * (k * (gam p σ / (1 - p)) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hρk (Nat.cast_nonneg k)) hξ.1.le
    have h4 := ih.2
    push_cast
    nlinarith

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**finite-horizon orbits**): for `D* < d₀ < 0` and every
horizon `N` there is a terminal point `ξ ∈ (0, 1]` whose `N`-fold backward image starts at `d₀`
(intermediate value theorem). -/
theorem finite_orbit (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ)
    {d0 : ℝ} (hd : Dst β < d0) (hd0 : d0 < 0) (N : ℕ) :
    ∃ ξ ∈ Set.Ioc (0 : ℝ) 1, (itr p β σ ξ N).1 = d0 := by
  set ρ := gam p σ / (1 - p) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (by unfold gam; have : 0 ≤ p / σ := by
    { have : (0 : ℝ) < σ := (by linarith); positivity }; linarith) (by linarith)
  have hDst : 0 < -Dst β := by
    simp only [Dst, neg_neg]; have : 0 < 1 - β := (by linarith); positivity
  set C := -Dst β + N * ρ ^ N with hC
  have hC0 : 0 < C := by have : 0 ≤ (N : ℝ) * ρ ^ N := by positivity
                         linarith
  set ξ1 := min 1 ((d0 - Dst β) / (2 * C)) with hξ1
  have hξ1p : 0 < ξ1 := lt_min one_pos (div_pos (by linarith) (by linarith))
  have hξ1 : ξ1 ∈ Set.Ioc (0 : ℝ) 1 := ⟨hξ1p, min_le_left _ _⟩
  have hf1 : (itr p β σ ξ1 N).1 < d0 := by
    have hb := (itr_bounds hp0 hp1 hβ0 hβ1 hσ hξ1 N).2
    have : ξ1 * C ≤ (d0 - Dst β) / 2 := by
      calc ξ1 * C ≤ (d0 - Dst β) / (2 * C) * C :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hC0.le
        _ = (d0 - Dst β) / 2 := by field_simp
    linarith
  have hcont : ContinuousOn (fun ξ => (itr p β σ ξ N).1) (Set.Icc ξ1 1) :=
    (continuous_fst.comp_continuousOn (itr_continuousOn hp0 hp1 hβ0 hβ1 hσ N)).mono
      fun ξ hξ => ⟨hξ1p.trans_le hξ.1, hξ.2⟩
  have hone : (itr p β σ 1 N).1 = 0 := by rw [itr_one hp0 hp1 hσ]
  obtain ⟨ξ, hξ, hξd⟩ := intermediate_value_Icc hξ1.2 hcont
    ⟨hf1.le, by rw [hone]; exact hd0.le⟩
  exact ⟨ξ, ⟨hξ1p.trans_le hξ.1, hξ.2⟩, hξd⟩

/-- Cochrane (2023), eq. (9.12), p. 267: if the continuation price implied one date earlier is at
most `(σ − 1)/σ`, the continuation price does not rise going forward: `x ≤ bx`. -/
theorem x_le_bx (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ)
    {z : ℝ × ℝ} (hz : z ∈ Box β) (h : bx p β σ z.1 z.2 ≤ (σ - 1) / σ) :
    z.2 ≤ bx p β σ z.1 z.2 := by
  obtain ⟨hy, hden, hb0, -, -, -, -⟩ := bstep_mem hp0 hp1 hβ0 hβ1 hσ hz
  by_contra hc
  push Not at hc
  have hσ0 : 0 < σ := by linarith
  have hy0 : 0 < σ + (1 - β) * z.1 := by linarith
  have hx0 := hz.2.2.1
  set y := σ + (1 - β) * z.1
  set b := bx p β σ z.1 z.2
  have hden0 : 0 < p / y + (1 - p) / z.2 := (by
    have : 0 < 1 - p := (by linarith)
    positivity)
  have hbd : b * (p / y + (1 - p) / z.2) = gam p σ := by
    change gam p σ / (p / y + (1 - p) / z.2) * (p / y + (1 - p) / z.2) = gam p σ
    exact div_mul_cancel₀ _ hden0.ne'
  -- `(1 − p)/x < (1 − p)/b`, so `γ < b (p/y) + (1 − p)`, i.e. `b > y/σ`
  have h1 : (1 - p) / z.2 < (1 - p) / b := div_lt_div_of_pos_left (by linarith) hb0 hc
  have h2 : gam p σ < b * (p / y) + (1 - p) := by
    have : b * ((1 - p) / z.2) < b * ((1 - p) / b) := mul_lt_mul_of_pos_left h1 hb0
    rw [mul_div_cancel₀ _ hb0.ne'] at this
    nlinarith
  unfold gam at h2
  have h3 : y / σ < b := by
    have : p / σ < b * (p / y) := by linarith
    rw [div_lt_iff₀ hσ0] at this
    have e : b * (p / y) * σ = p * (b * σ / y) := by field_simp
    rw [e] at this
    have : 1 < b * σ / y := by nlinarith
    rw [lt_div_iff₀ hy0, one_mul] at this
    rw [div_lt_iff₀ hσ0]
    linarith
  have h4 : (σ - 1) / σ ≤ y / σ := div_le_div_of_nonneg_right hy hσ0.le
  linarith

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the date-0 continuation price is bounded below
uniformly in the horizon**): if the `N`-fold backward image of `ξ` starts at `d₀ > D*` and
`βᴺ (−D*) ≤ (d₀ − D*)/2`, its continuation price is at least
`min((σ − 1)/σ, (1 − β)(d₀ − D*)/2)`. -/
theorem finite_orbit_lower (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 1 < σ) {ξ d0 : ℝ} (hξ : ξ ∈ Set.Ioc (0 : ℝ) 1) {N : ℕ} (hN : (itr p β σ ξ N).1 = d0)
    (hβN : β ^ N * (-Dst β) ≤ (d0 - Dst β) / 2) :
    min ((σ - 1) / σ) ((1 - β) * (d0 - Dst β) / 2) ≤ (itr p β σ ξ N).2 := by
  obtain ⟨e1, -⟩ := Dst_props hβ1
  have h1β : 0 < 1 - β := by linarith
  by_cases hbig : (σ - 1) / σ < (itr p β σ ξ N).2
  · exact (min_le_left _ _).trans hbig.le
  push Not at hbig
  set xN := (itr p β σ ξ N).2
  -- going forward (down the backward index) the price does not rise
  have hmono : ∀ m, m ≤ N → (itr p β σ ξ (N - m)).2 ≤ xN := by
    intro m
    induction m with
    | zero => intro _; simp [xN]
    | succ m ih =>
      intro hm
      have hk : N - m = (N - (m + 1)) + 1 := by omega
      have hle := ih (by omega)
      rw [hk] at hle
      have hz := itr_mem hp0 hp1 hβ0 hβ1 hσ hξ (N - (m + 1))
      have hle' : bx p β σ (itr p β σ ξ (N - (m + 1))).1 (itr p β σ ξ (N - (m + 1))).2 ≤ xN :=
        hle
      exact (x_le_bx hp0 hp1 hβ0 hβ1 hσ hz (hle'.trans hbig)).trans hle'
  have hmono' : ∀ k, k ≤ N → (itr p β σ ξ k).2 ≤ xN := fun k hk => by
    have := hmono (N - k) (by omega)
    rwa [show N - (N - k) = k by omega] at this
  have hDst : 0 < -Dst β := by
    simp only [Dst, neg_neg]; have : 0 < 1 - β := (by linarith); positivity
  have hxN0 : 0 ≤ xN := (itr_mem hp0 hp1 hβ0 hβ1 hσ hξ N).2.2.1.le
  have hsum : ∀ k, k ≤ N → (itr p β σ ξ k).1 - Dst β ≤ xN / (1 - β) + β ^ k * (-Dst β) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [itr, term, pow_zero, one_mul]
      have : 0 ≤ xN / (1 - β) := div_nonneg hxN0 h1β.le
      nlinarith [hξ.1, hξ.2]
    | succ k ih =>
      intro hk
      have he : (itr p β σ ξ (k + 1)).1 - Dst β =
          (itr p β σ ξ (k + 1)).2 + β * ((itr p β σ ξ k).1 - Dst β) := by
        change bx p β σ _ _ - 1 + β * (itr p β σ ξ k).1 - Dst β = bx p β σ _ _ + _
        linarith
      rw [he]
      have h1 := hmono' (k + 1) hk
      have h2 := ih (by omega)
      have e : xN + β * (xN / (1 - β) + β ^ k * (-Dst β)) =
          xN / (1 - β) + β ^ (k + 1) * (-Dst β) := by
        field_simp
        ring
      nlinarith
  have hN' := hsum N le_rfl
  rw [hN] at hN'
  have : (1 - β) * (d0 - Dst β) / 2 ≤ xN := by
    have h3 : (d0 - Dst β) / 2 ≤ xN / (1 - β) := by linarith
    rw [le_div_iff₀ h1β] at h3
    linarith
  exact (min_le_right _ _).trans this

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**an infinite continuation path for every
`D* < d₀ < 0`**): there are sequences `D` (debt deviation) and `x` (continuation price) with
`D_0 = d₀`, `D* ≤ D ≤ 0`, `0 < x ≤ 1`, the flow `D_t = x_t − 1 + β D_{t+1}` and the interest-rate
target `x_t (p/(σ + (1 − β) D_{t+1}) + (1 − p)/x_{t+1}) = γ`. Proof: the finite orbits of
`finite_orbit`, padded, lie in the compact product `∏_t [D*, 0] × [0, 1]`; a convergent subsequence
has a limit whose continuation prices stay positive (`finite_orbit_lower` and
`x_{t+1} ≥ ((1 − p)/γ) x_t`), so the backward map passes to the limit. -/
theorem infinite_orbit (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ)
    {d0 : ℝ} (hd : Dst β < d0) (hd0 : d0 < 0) :
    ∃ D x : ℕ → ℝ, D 0 = d0 ∧ (∀ t, Dst β ≤ D t ∧ D t ≤ 0 ∧ 0 < x t ∧ x t ≤ 1) ∧
      (∀ t, D t = x t - 1 + β * D (t + 1)) ∧
      ∀ t, x t * (p / (σ + (1 - β) * D (t + 1)) + (1 - p) / x (t + 1)) = gam p σ := by
  have hγ : 0 < gam p σ := by
    unfold gam
    have : 0 < p / σ := by have : (0 : ℝ) < σ := (by linarith); positivity
    linarith
  set qC := (1 - p) / gam p σ with hqC
  have hqC0 : 0 < qC := div_pos (by linarith) hγ
  have hDst : 0 < -Dst β := by
    simp only [Dst, neg_neg]; have : 0 < 1 - β := (by linarith); positivity
  choose ξ hξ hξd using fun N => finite_orbit hp0 hp1 hβ0 hβ1 hσ hd hd0 N
  obtain ⟨N0, hN0⟩ := exists_pow_lt_of_lt_one
    (show 0 < (d0 - Dst β) / 2 / (-Dst β) by apply div_pos <;> linarith) hβ1
  set c0 := min ((σ - 1) / σ) ((1 - β) * (d0 - Dst β) / 2) with hc0
  have hc0p : 0 < c0 := lt_min (div_pos (by linarith) (by linarith))
    (by have : 0 < 1 - β := (by linarith); have : 0 < d0 - Dst β := (by linarith); positivity)
  set Z : ℕ → ℕ → ℝ × ℝ := fun N t => if t ≤ N then itr p β σ (ξ N) (N - t) else (0, 1)
    with hZ
  set K : Set (ℕ → ℝ × ℝ) := Set.pi Set.univ fun _ => Set.Icc (Dst β) 0 ×ˢ Set.Icc (0 : ℝ) 1
    with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc.prod isCompact_Icc
  have hboxK : ∀ z ∈ Box β, z ∈ Set.Icc (Dst β) 0 ×ˢ Set.Icc (0 : ℝ) 1 := fun z hz =>
    ⟨⟨hz.1, hz.2.1⟩, ⟨hz.2.2.1.le, hz.2.2.2⟩⟩
  have hZK : ∀ N, Z N ∈ K := fun N t _ => by
    simp only [hZ]
    split_ifs
    · exact hboxK _ (itr_mem hp0 hp1 hβ0 hβ1 hσ (hξ N) _)
    · exact ⟨⟨by linarith, le_rfl⟩, ⟨zero_le_one, le_rfl⟩⟩
  obtain ⟨a, haK, φ, hφ, hlim⟩ := hKc.tendsto_subseq hZK
  have hcoord : ∀ t, Tendsto (fun k => Z (φ k) t) atTop (𝓝 (a t)) := fun t =>
    ((continuous_apply t).tendsto a).comp hlim
  have hφt := hφ.tendsto_atTop
  -- the relation along the finite orbits
  have hrel : ∀ N t, t + 1 ≤ N → Z N t = bstep p β σ (Z N (t + 1)) := fun N t ht => by
    simp only [hZ, show t ≤ N by omega, ht, ↓reduceIte]
    rw [show N - t = (N - (t + 1)) + 1 by omega]
    rfl
  -- lower bounds on the finite orbits
  have hlow : ∀ N t, N0 ≤ N → t ≤ N → qC ^ t * c0 ≤ (Z N t).2 := by
    intro N t hN ht
    have hβN : β ^ N * (-Dst β) ≤ (d0 - Dst β) / 2 := by
      have h1 : β ^ N ≤ β ^ N0 := pow_le_pow_of_le_one hβ0.le hβ1.le hN
      have h2 : β ^ N0 * (-Dst β) < (d0 - Dst β) / 2 := by
        rw [lt_div_iff₀ hDst] at hN0; linarith
      nlinarith
    have h0 := finite_orbit_lower hp0 hp1 hβ0 hβ1 hσ (hξ N) (hξd N) hβN
    induction t with
    | zero =>
      simp only [hZ, Nat.zero_le, ↓reduceIte, Nat.sub_zero, pow_zero, one_mul]
      exact h0
    | succ t ih =>
      have ih' := ih (by omega)
      have hr := hrel N t ht
      have hz := itr_mem hp0 hp1 hβ0 hβ1 hσ (hξ N) (N - (t + 1))
      have hzZ : Z N (t + 1) = itr p β σ (ξ N) (N - (t + 1)) := by simp [hZ, ht]
      have hbx := (bstep_mem hp0 hp1 hβ0 hβ1 hσ hz).2.2.2.2.1
      rw [hr] at ih'
      change qC ^ t * c0 ≤ bx p β σ (Z N (t + 1)).1 (Z N (t + 1)).2 at ih'
      rw [← hzZ] at hbx
      have : qC ^ t * c0 ≤ gam p σ / (1 - p) * (Z N (t + 1)).2 := ih'.trans hbx
      have e : qC * (gam p σ / (1 - p)) = 1 := by
        have : 1 - p ≠ 0 := by linarith
        simp only [hqC]; field_simp
      calc qC ^ (t + 1) * c0 = qC * (qC ^ t * c0) := by ring
        _ ≤ qC * (gam p σ / (1 - p) * (Z N (t + 1)).2) :=
          mul_le_mul_of_nonneg_left this hqC0.le
        _ = (Z N (t + 1)).2 := by rw [← mul_assoc, e, one_mul]
  -- properties of the limit
  have hapos : ∀ t, qC ^ t * c0 ≤ (a t).2 := fun t =>
    ge_of_tendsto ((continuous_snd.tendsto _).comp (hcoord t)) (by
      filter_upwards [hφt.eventually_ge_atTop (N0 + t)] with k hk
      exact hlow (φ k) t (by omega) (by omega))
  have hx0 : ∀ t, 0 < (a t).2 := fun t =>
    (mul_pos (pow_pos hqC0 t) hc0p).trans_le (hapos t)
  have hmemK : ∀ t, Dst β ≤ (a t).1 ∧ (a t).1 ≤ 0 ∧ (a t).2 ≤ 1 := fun t => by
    have := haK t (Set.mem_univ _)
    exact ⟨this.1.1, this.1.2, this.2.2⟩
  have hstep : ∀ t, a t = bstep p β σ (a (t + 1)) := fun t => by
    have hy : 0 < σ + (1 - β) * (a (t + 1)).1 := by
      obtain ⟨-, e2⟩ := Dst_props hβ1
      have := (hmemK (t + 1)).1
      nlinarith
    have hc := (bstep_continuousAt hp0 hp1 hy (hx0 (t + 1))).tendsto.comp (hcoord (t + 1))
    refine tendsto_nhds_unique (hcoord t) (hc.congr' ?_)
    filter_upwards [hφt.eventually_ge_atTop (t + 1)] with k hk
    exact (hrel (φ k) t hk).symm
  have hd00 : (a 0).1 = d0 := by
    have h1 : Tendsto (fun k => (Z (φ k) 0).1) atTop (𝓝 (a 0).1) :=
      (continuous_fst.tendsto _).comp (hcoord 0)
    have h2 : ∀ k, (Z (φ k) 0).1 = d0 := fun k => by
      simp only [hZ, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
      exact hξd (φ k)
    simp only [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  refine ⟨fun t => (a t).1, fun t => (a t).2, hd00, fun t => ⟨(hmemK t).1, (hmemK t).2.1,
    hx0 t, (hmemK t).2.2⟩, fun t => ?_, fun t => ?_⟩
  · have := congrArg Prod.fst (hstep t)
    simp only [bstep] at this
    have e2 := congrArg Prod.snd (hstep t)
    simp only [bstep] at e2
    change (a t).1 = (a t).2 - 1 + β * (a (t + 1)).1
    rw [this, ← e2]
  · have e2 := congrArg Prod.snd (hstep t)
    simp only [bstep, bx] at e2
    have hy : 0 < σ + (1 - β) * (a (t + 1)).1 := by
      obtain ⟨-, e3⟩ := Dst_props hβ1
      have := (hmemK (t + 1)).1
      nlinarith
    have hden : 0 < p / (σ + (1 - β) * (a (t + 1)).1) + (1 - p) / (a (t + 1)).2 := by
      have := hx0 (t + 1)
      have : 0 < 1 - p := (by linarith)
      positivity
    change (a t).2 * (p / (σ + (1 - β) * (a (t + 1)).1) + (1 - p) / (a (t + 1)).2) = gam p σ
    rw [e2, div_mul_cancel₀ _ hden.ne']

/-! ### The equilibrium built from a continuation path -/

/-- Cochrane (2023), §9.3.2, p. 267: the price process built from a continuation path — `x_t` on
the states not yet settled at `t`, the settled price `σ + (1 − β) D_{ω+1}` on the state that
settled at `ω + 1 ≤ t`. -/
noncomputable def Pc (σ β : ℝ) (D x : ℕ → ℝ) (t ω : ℕ) : ℝ :=
  if t ≤ ω then x t else σ + (1 - β) * D (ω + 1)

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the continuation path is an equilibrium**): sequences
`D, x` as in `infinite_orbit` give, through `Pc`, an equilibrium of the rule on `gSys` with
target `tgtS σ`, prices bounded above by `σ`, integrable `1/P` and `b₀ = b̄ + θ d₀`. -/
theorem orbit_eqm (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ)
    (θ bbar : ℝ) {d0 : ℝ} {D x : ℕ → ℝ} (hD0 : D 0 = d0)
    (hDx : ∀ t, Dst β ≤ D t ∧ D t ≤ 0 ∧ 0 < x t ∧ x t ≤ 1)
    (hflow : ∀ t, D t = x t - 1 + β * D (t + 1))
    (hrate : ∀ t, x t * (p / (σ + (1 - β) * D (t + 1)) + (1 - p) / x (t + 1)) = gam p σ) :
    ExistsAbove (gSys hp0 hp1) β θ bbar (tgtS σ) d0 := by
  obtain ⟨e1, e2⟩ := Dst_props hβ1
  have h1β : 0 < 1 - β := by linarith
  have hy : ∀ m, σ - 1 ≤ σ + (1 - β) * D m ∧ σ + (1 - β) * D m ≤ σ := fun m => by
    have := hDx m
    constructor <;> nlinarith
  set P := Pc σ β D x with hPdef
  have hPb : ∀ t ω, min (x t) (σ - 1) ≤ P t ω ∧ P t ω ≤ σ := fun t ω => by
    simp only [hPdef, Pc]
    split_ifs
    · exact ⟨min_le_left _ _, by linarith [(hDx t).2.2.2]⟩
    · exact ⟨(min_le_right _ _).trans (hy _).1, (hy _).2⟩
  have hmin : ∀ t, 0 < min (x t) (σ - 1) := fun t => lt_min (hDx t).2.2.1 (by linarith)
  have hP : ∀ t ω, 0 < P t ω := fun t ω => (hmin t).trans_le (hPb t ω).1
  have hPa : StronglyAdapted (gSys hp0 hp1).𝓕 P := fun t => by
    set G : Option ℕ → ℝ := fun o => o.elim (x t) fun m => σ + (1 - β) * D m with hG
    have e : P t = fun ω => G (SunspotMeasure.node t ω) := by
      funext ω
      rcases Nat.lt_or_ge ω t with h | h
      · simp [hPdef, Pc, hG, SunspotMeasure.node_of_lt h, Nat.not_le.mpr h]
      · simp [hPdef, Pc, hG, SunspotMeasure.node_of_le h, h]
    rw [e]
    have : Measurable[(gSys hp0 hp1).𝓕 t] (fun ω => G (SunspotMeasure.node t ω)) :=
      fun U _ => MeasurableSpace.measurableSet_comap.2
        ⟨G ⁻¹' U, MeasurableSpace.measurableSet_top, rfl⟩
    exact this.stronglyMeasurable
  have hprob : IsProbabilityMeasure (gMeasure p) := ⟨gMeasure_univ hp0 hp1⟩
  have hbint : ∀ {X : ℕ → ℝ} (C : ℝ), (∀ ω, |X ω| ≤ C) → Integrable X (gMeasure p) :=
    fun C hC => Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  have hratio : ∀ t, Integrable (P t / P (t + 1)) (gMeasure p) := fun t =>
    hbint (σ / min (x (t + 1)) (σ - 1)) fun ω => by
      simp only [Pi.div_apply]
      rw [abs_of_pos (div_pos (hP t ω) (hP (t + 1) ω))]
      exact div_le_div₀ (by linarith) (hPb t ω).2 (hmin _) (hPb (t + 1) ω).1
  have hTratio : ∀ t, Integrable (tgtS σ t / tgtS σ (t + 1)) (gMeasure p) := fun t =>
    hbint σ fun ω => by
      have h1 := tgtS_bounds hσ.le t ω
      have h2 := tgtS_bounds hσ.le (t + 1) ω
      simp only [Pi.div_apply]
      rw [abs_of_pos (div_pos (by linarith) (by linarith)), div_le_iff₀ (by linarith)]
      nlinarith
  have hrateE : ∀ t, (gSys hp0 hp1).E t (P t / P (t + 1)) =ᵐ[(gSys hp0 hp1).μ]
      (gSys hp0 hp1).E t (tgtS σ t / tgtS σ (t + 1)) := fun t => by
    refine EventuallyEq.of_eq (funext fun ω => ?_)
    rcases Nat.lt_or_ge ω t with h | h
    · rw [g_E_settled hp0 hp1 h (hratio t), g_E_settled hp0 hp1 h (hTratio t)]
      simp only [Pi.div_apply, hPdef, Pc, tgtS, Nat.not_le.mpr h,
        Nat.not_le.mpr (Nat.lt_succ_of_lt h), ↓reduceIte]
      rw [div_self (by linarith [(hy (ω + 1)).1]), div_self (by linarith)]
    · have hcX : ∀ k, t + 1 ≤ k → (P t / P (t + 1)) k = (P t / P (t + 1)) (t + 1) :=
        fun k hk => by
          simp only [Pi.div_apply, hPdef, Pc, show t ≤ k by omega, hk, ↓reduceIte,
            show t ≤ t + 1 by omega, le_refl]
      have hcT : ∀ k, t + 1 ≤ k → (tgtS σ t / tgtS σ (t + 1)) k =
          (tgtS σ t / tgtS σ (t + 1)) (t + 1) := fun k hk => by
        simp only [Pi.div_apply, tgtS, show t ≤ k by omega, hk, ↓reduceIte,
          show t ≤ t + 1 by omega, le_refl]
      rw [g_E_cont hp0 hp1 h (hratio t) hcX, g_E_cont hp0 hp1 h (hTratio t) hcT]
      simp only [Pi.div_apply, hPdef, Pc, tgtS, le_refl, ↓reduceIte,
        show t ≤ t + 1 by omega, show ¬ t + 1 ≤ t by omega, div_one]
      have h' := hrate t
      unfold gam at h'
      rw [show p * (1 / σ) + (1 - p) * 1 = p / σ + (1 - p) by ring, ← h']
      ring
  -- the forward debt is the continuation path's debt, frozen after settlement
  have hfwd : ∀ t ω, fwdDebt β d0 (tgtS σ) P t ω = if t ≤ ω + 1 then D t else D (ω + 1) := by
    intro t ω
    induction t with
    | zero => simp [fwdDebt, hD0]
    | succ t ih =>
      simp only [fwdDebt]
      rw [ih]
      rcases Nat.lt_or_ge ω t with h | h
      · simp only [show ¬ t ≤ ω by omega, show ¬ t + 1 ≤ ω + 1 by omega, hPdef, Pc, tgtS,
          ↓reduceIte]
        by_cases ht : t ≤ ω + 1
        · simp only [ht, ↓reduceIte]
          have : t = ω + 1 := by omega
          subst this
          field_simp
          ring
        · simp only [ht, ↓reduceIte]
          field_simp
          ring
      · simp only [show t ≤ ω + 1 by omega, show t ≤ ω by omega, show t + 1 ≤ ω + 1 by omega,
          hPdef, Pc, tgtS, ↓reduceIte]
        rw [hflow t]
        field_simp
        ring
  have hDK : ∀ t, ∀ᵐ ω ∂(gSys hp0 hp1).μ, |fwdDebt β d0 (tgtS σ) P t ω| ≤ -Dst β := fun t =>
    Eventually.of_forall fun ω => by
      rw [hfwd]
      split_ifs
      · have := hDx t; rw [abs_le]; constructor <;> linarith
      · have := hDx (ω + 1); rw [abs_le]; constructor <;> linarith
  have hE := eqm_of_bdd (gSys hp0 hp1) hβ0 hβ1 (θ := θ) (bbar := bbar) (d0 := d0)
    (tgtS_adapted hp0 hp1 σ) one_pos (fun t ω => tgtS_bounds hσ.le t ω) hP hPa
    (fun t ω => (hPb t ω).2) hrateE hDK
  refine ⟨P, _, σ, hE, fun t ω => (hPb t ω).2, fun t => ?_, fun ω => rfl⟩
  exact hbint (1 / min (x t) (σ - 1)) fun ω => by
    rw [abs_of_pos (one_div_pos.2 (hP t ω))]
    exact one_div_le_one_div_of_le (hmin t) (hPb t ω).1

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the lower end**): every equilibrium of the rule on
`gSys` with prices bounded above and `b₀ = b̄ + θ d₀` has `d₀ > −1/(1 − β)`: the scaled debt
deviation on the continuation path is `∑ βˢ (x_s − 1) > −1/(1 − β)`. -/
theorem lower_end {p β θ bbar σ M d0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) {P b : ℕ → ℕ → ℝ}
    (hE : RuleEqm (gSys hp0 hp1) β θ bbar (tgtS σ) P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hb0 : ∀ ω, b 0 ω = bbar + θ * d0) : Dst β < d0 := by
  obtain ⟨e1, e2⟩ := Dst_props hβ1
  have h1β : 0 < 1 - β := by linarith
  obtain ⟨h1, h2, -, -⟩ := continuation_relations hp0 hp1 hβ0 hβ1 hθ hσ.le hE hPM
  have hP := hE.1
  set a := aC θ bbar b with ha
  set e : ℕ → ℝ := fun t => a t - Dst β with he
  have hrec : ∀ t, e t = P t t + β * e (t + 1) := fun t => by
    simp only [he]; rw [h1 t]; linarith
  set m := -(σ / (1 - β)) - Dst β with hm
  have hlow : ∀ t, m ≤ e (t + 1) := fun t => by
    have hy := hP (t + 1) t
    rw [h2 t] at hy
    simp only [he, hm]
    have : -(σ / (1 - β)) ≤ a (t + 1) := by
      rw [neg_le, le_div_iff₀ h1β]; nlinarith
    linarith
  have hdec : ∀ n t, β ^ n * e (t + n) ≤ e t := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      have h3 := hrec (t + n)
      have h4 := hP (t + n) (t + n)
      calc β ^ (n + 1) * e (t + (n + 1)) = β ^ n * (β * e (t + n + 1)) := by
            rw [pow_succ, show t + (n + 1) = t + n + 1 by ring]; ring
        _ ≤ β ^ n * e (t + n) := mul_le_mul_of_nonneg_left (by linarith) (pow_pos hβ0 n).le
        _ ≤ e t := ih t
  have hb : ∀ n, P 0 0 + β ^ (n + 1) * m ≤ e 0 := fun n => by
    have h3 := hrec 0
    have h4 := hdec n 1
    have h5 := hlow n
    rw [show 1 + n = n + 1 by ring] at h4
    have : β ^ (n + 1) * m ≤ β * e 1 := by
      calc β ^ (n + 1) * m = β * (β ^ n * m) := by ring
        _ ≤ β * (β ^ n * e (n + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 (pow_pos hβ0 n).le) hβ0.le
        _ ≤ β * e 1 := mul_le_mul_of_nonneg_left h4 hβ0.le
    linarith
  have hlim : Tendsto (fun n => P 0 0 + β ^ (n + 1) * m) atTop (𝓝 (P 0 0)) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
      (tendsto_add_atTop_nat 1)).mul_const m
    simpa using this.const_add (P 0 0)
  have he0 : P 0 0 ≤ e 0 := le_of_tendsto' hlim hb
  have ha0 : a 0 = d0 := by
    simp only [ha, aC, hb0 0]
    field_simp
    ring
  have := hP 0 0
  simp only [he] at he0
  linarith

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the exact existence set on the settle-or-continue
target**): for `0 < β < 1`, `0 < p < 1`, `σ > 1`, `θ ≠ 0`, an equilibrium of the rule with prices
bounded above (and integrable `1/P`) and `b₀ = b̄ + θ d₀` exists **iff**
`−1/(1 − β) < d₀ ≤ 0`. For `d₀ < 0` its prices are not bounded away from zero
(`d0_neg_not_bounded_below`). -/
theorem existsAbove_iff {p β θ bbar σ d0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) :
    ExistsAbove (gSys hp0 hp1) β θ bbar (tgtS σ) d0 ↔ -(1 / (1 - β)) < d0 ∧ d0 ≤ 0 := by
  constructor
  · rintro ⟨P, b, M, hE, hPM, -, hb0⟩
    exact ⟨lower_end hp0 hp1 hβ0 hβ1 hθ hσ hE hPM hb0,
      no_eqm_pos hp0 hp1 hβ0 hβ1 hθ hσ hE hPM hb0⟩
  · rintro ⟨hl, hu⟩
    rcases hu.lt_or_eq with hneg | rfl
    · obtain ⟨D, x, hD0, hDx, hflow, hrate⟩ :=
        infinite_orbit hp0 hp1 hβ0 hβ1 hσ (d0 := d0) hl hneg
      exact orbit_eqm hp0 hp1 hβ0 hβ1 hσ θ bbar hD0 hDx hflow hrate
    · exact (exists_zero _ hβ0 hβ1 (tgtS_adapted hp0 hp1 σ) one_pos
        (fun t ω => tgtS_bounds hσ.le t ω)).1

/-- Cochrane (2023), §9.3.2, pp. 266–267: the existence set as a set,
`{d₀ | ExistsAbove} = (−1/(1 − β), 0]`. -/
theorem existsAbove_set {p β θ bbar σ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) :
    {d0 | ExistsAbove (gSys hp0 hp1) β θ bbar (tgtS σ) d0} = Set.Ioc (-(1 / (1 - β))) 0 := by
  ext d0
  simp only [Set.mem_ofPred_eq, Set.mem_Ioc]
  exact existsAbove_iff hp0 hp1 hβ0 hβ1 hθ hσ

/-- Cochrane (2023), §9.3.2, pp. 266–267: for `−1/(1 − β) < d₀ < 0` equilibria with prices bounded
above exist, but none of them has prices bounded away from zero (`TidyR5NoExist.no_eqm_neg`). -/
theorem d0_neg_not_bounded_below {p β θ bbar σ d0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) (hneg : d0 < 0) {P b : ℕ → ℕ → ℝ}
    {M : ℝ} (hE : RuleEqm (gSys hp0 hp1) β θ bbar (tgtS σ) P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hb0 : ∀ ω, b 0 ω = bbar + θ * d0) : ¬ ∃ mP, 0 < mP ∧ ∀ t ω, mP ≤ P t ω := by
  rintro ⟨mP, hmP, hPm⟩
  have := no_eqm_neg hp0 hp1 hβ0 hβ1 hθ hσ hE hPM hmP hPm hb0
  linarith

end Cochrane.AssetsRulesBalanceSheets.TidyR5ExistSet
