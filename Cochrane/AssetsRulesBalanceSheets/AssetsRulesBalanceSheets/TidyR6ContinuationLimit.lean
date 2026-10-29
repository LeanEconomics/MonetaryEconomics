/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.TidyR5ExistSet

/-!
# Theorem FR (d) on the settle-or-continue target: the continuation prices tend to zero

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.2,
eqs. (9.8)–(9.12), pp. 266–267 (Theorem FR; stochastic target, `b₀ = b̄ + θ d₀`).

The module TidyR5ExistSet proves that on the settle-or-continue system (`gSys`, target
`tgtS σ`, `σ > 1`) an equilibrium with prices bounded above exists iff `−1/(1 − β) < d₀ ≤ 0`, and
(`TidyR5ExistSet.d0_neg_not_bounded_below`) that for `d₀ < 0` no such equilibrium has prices
bounded away from zero. Here the behaviour of **every** such equilibrium is pinned down exactly.

## Main results

* `settled_ge_price` (the key inequality): along the continuation path the continuation price
  never exceeds the price the target would settle at next period divided by `σ`,
  `σ x_t ≤ σ + (1 − β) D_{t+1}`. If it did, the gap `δ_t = σ/(σ + (1 − β) D_{t+1}) − 1/x_t`
  would grow (`δ_{t+1} ≥ (1 + c) δ_t`, `c = p/(σ(1 − p))`) and `1/x_t` would fall by at least
  `c δ_{t₀}` per period, eventually below zero.
* `price_antitone`, `debt_antitone`: hence the continuation price `x_t` and the scaled debt
  deviation `D_t` are both nonincreasing, and `x_t ≤ 1`.
* `orbit_limits` (**the continuation prices tend to zero**): if `D_0 < 0` then `x_t → 0` and
  `D_t → D* = −1/(1 − β)`; the only other possible limit, the fixed point `(D, x) = (0, 1)`, is
  excluded because `D` is nonincreasing from `D_0 < 0`. Moreover `x_{t+1}/x_t → (1 − p)/γ`
  (`orbit_ratio`), so the decay is asymptotically geometric at the rate of the continue
  probability divided by the target real-rate factor `γ = p/σ + 1 − p`.
* `orbit_zero`: if `D_0 = 0` the continuation path is the target, `x ≡ 1`, `D ≡ 0`.
* `eqm_continuation_tendsto_zero`, `eqm_settled_tendsto`, `eqm_ratio_tendsto`,
  `eqm_continuation_antitone`, `eqm_zero_target` (**the equilibrium statements**): in every
  equilibrium of the rule on `gSys` with prices bounded above and `b₀ = b̄ + θ d₀`, `d₀ < 0`, the
  continuation prices `P_t(continue)` decrease monotonically to `0` at the asymptotic rate
  `(1 − p)/γ`, the scaled debt tends to `D*`, and the price on settlement tends to `σ − 1`; for
  `d₀ = 0` the continuation price is `1` and the settled price `σ` at every date.
* `exists_and_tendsto_zero`: for every `d₀ ∈ (−1/(1 − β), 0)` an equilibrium exists and every
  equilibrium has continuation prices tending to zero.
-/

namespace Cochrane.AssetsRulesBalanceSheets.TidyR6ContinuationLimit

open Filter Topology
open FiscalRulesMeasure TidyR5NoExist TidyR5ExistSet

variable {β σ p : ℝ}

/-- Cochrane (2023), §9.3.2, pp. 266–267: along the continuation path (hypotheses of
`TidyR5NoExist.orbit_nonpos`) the scaled debt deviation is nonpositive at **every** date, by
`TidyR5NoExist.orbit_nonpos` applied to the shifted path. -/
theorem orbit_all_nonpos (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ) (hp0 : 0 < p) (hp1 : p < 1)
    {M K : ℝ} {a x : ℕ → ℝ} (hx : ∀ t, 0 < x t) (hy : ∀ t, 0 < σ + (1 - β) * a (t + 1))
    (hflow : ∀ t, a t = x t - 1 + β * a (t + 1))
    (hrate : ∀ t, x t * (p / (σ + (1 - β) * a (t + 1)) + (1 - p) / x (t + 1)) = p / σ + (1 - p))
    (hxM : ∀ t, x t ≤ M) (haK : ∀ t, a t ≤ K) (s : ℕ) : a s ≤ 0 := by
  have e : ∀ t, t + s + 1 = t + 1 + s := fun t => by omega
  have := orbit_nonpos hβ0 hβ1 hσ hp0 hp1 (a := fun t => a (t + s)) (x := fun t => x (t + s))
    (M := M) (K := K) (fun t => hx _) (fun t => by simpa only [e] using hy (t + s))
    (fun t => by simpa only [e] using hflow (t + s))
    (fun t => by simpa only [e] using hrate (t + s)) (fun t => hxM _) (fun t => haK _)
  simpa using this

/-- Cochrane (2023), eq. (9.12), p. 267: with `u_t = 1/x_t`, `W_t = σ/(σ + (1 − β) D_t)` and
`c = p/(σ(1 − p))`, the interest-rate target on the continuation path reads
`u_{t+1} = u_t − c (W_{t+1} − u_t)`. -/
theorem rate_inv (hσ : 1 < σ) (hp1 : p < 1) {a x : ℕ → ℝ} (hx : ∀ t, 0 < x t)
    (hy : ∀ t, 0 < σ + (1 - β) * a (t + 1))
    (hrate : ∀ t, x t * (p / (σ + (1 - β) * a (t + 1)) + (1 - p) / x (t + 1)) = p / σ + (1 - p))
    (t : ℕ) :
    1 / x (t + 1) = 1 / x t - p / (σ * (1 - p)) *
      (σ / (σ + (1 - β) * a (t + 1)) - 1 / x t) := by
  have hσ0 : σ ≠ 0 := by positivity
  have h1p : 1 - p ≠ 0 := by linarith
  have hX := (hx t).ne'
  have hZ := (hx (t + 1)).ne'
  have hY := (hy t).ne'
  have h := hrate t
  generalize x t = X at h hX ⊢
  generalize x (t + 1) = Z at h hZ ⊢
  generalize σ + (1 - β) * a (t + 1) = Y at h hY ⊢
  field_simp at h ⊢
  linear_combination h

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the key inequality**): on a bounded continuation path
(hypotheses of `TidyR5NoExist.orbit_nonpos`) the continuation price never exceeds the next
period's settled price divided by `σ`: `σ x_t ≤ σ + (1 − β) D_{t+1}`. -/
theorem settled_ge_price (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ) (hp0 : 0 < p) (hp1 : p < 1)
    {M K : ℝ} {a x : ℕ → ℝ} (hx : ∀ t, 0 < x t) (hy : ∀ t, 0 < σ + (1 - β) * a (t + 1))
    (hflow : ∀ t, a t = x t - 1 + β * a (t + 1))
    (hrate : ∀ t, x t * (p / (σ + (1 - β) * a (t + 1)) + (1 - p) / x (t + 1)) = p / σ + (1 - p))
    (hxM : ∀ t, x t ≤ M) (haK : ∀ t, a t ≤ K) (t : ℕ) :
    σ * x t ≤ σ + (1 - β) * a (t + 1) := by
  have hnp := orbit_all_nonpos hβ0 hβ1 hσ hp0 hp1 hx hy hflow hrate hxM haK
  have hσ0 : 0 < σ := by linarith
  have h1β : 0 < 1 - β := by linarith
  set c : ℝ := p / (σ * (1 - p)) with hc
  have hc0 : 0 < c := div_pos hp0 (mul_pos hσ0 (by linarith))
  set u : ℕ → ℝ := fun t => 1 / x t with hu
  set W : ℕ → ℝ := fun t => σ / (σ + (1 - β) * a t) with hW
  have hu0 : ∀ t, 0 < u t := fun t => one_div_pos.2 (hx t)
  have hrec : ∀ t, u (t + 1) = u t - c * (W (t + 1) - u t) := fun t =>
    rate_inv hσ hp1 hx hy hrate t
  -- `δ > 0` means `σ x > y`
  have hδ : ∀ s, 0 < W (s + 1) - u s → σ + (1 - β) * a (s + 1) < σ * x s := fun s h => by
    have hy1 := hy s
    have hxs := hx s
    simp only [hW, hu] at h
    rw [sub_pos, div_lt_div_iff₀ hxs hy1] at h
    linarith
  by_contra hcon
  push Not at hcon
  set t0 := t with ht0
  set δ0 := W (t0 + 1) - u t0 with hδ0
  have hδ0p : 0 < δ0 := by
    simp only [hδ0, hW, hu]
    rw [sub_pos, div_lt_div_iff₀ (hx t0) (hy t0)]
    linarith
  have claim : ∀ n : ℕ, δ0 ≤ W (t0 + n + 1) - u (t0 + n) ∧
      u (t0 + n) ≤ u t0 - n * (c * δ0) := by
    intro n
    induction n with
    | zero => simp [hδ0]
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      set s := t0 + n with hs
      have es : t0 + (n + 1) = s + 1 := by omega
      rw [es]
      have hδs : 0 < W (s + 1) - u s := hδ0p.trans_le h1
      have hus : u (s + 1) = u s - c * (W (s + 1) - u s) := hrec s
      -- the continuation price rises
      have hxx : x s < x (s + 1) := by
        have : u (s + 1) < u s := by rw [hus]; nlinarith
        simp only [hu] at this
        rwa [div_lt_div_iff₀ (hx (s + 1)) (hx s), one_mul, one_mul] at this
      -- the price exceeds next period's settled price over `σ`
      have hxy := hδ s hδs
      -- the debt falls
      have hna := hnp (s + 1)
      have hfl := hflow (s + 1)
      have hdeb : a (s + 1 + 1) < a (s + 1) := by
        have h3 : (1 - β) * a (s + 1) ≤ (1 - β) * a (s + 1) / σ := by
          rw [le_div_iff₀ hσ0]
          have : (1 - β) * a (s + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1β.le hna
          nlinarith
        have h4 : 1 + (1 - β) * a (s + 1) < x (s + 1) := by
          have : σ + (1 - β) * a (s + 1) = σ * (1 + (1 - β) * a (s + 1) / σ) := by
            field_simp
          rw [this] at hxy
          have h5 : 1 + (1 - β) * a (s + 1) / σ < x s := by
            by_contra hh
            push Not at hh
            nlinarith
          linarith
        nlinarith
      have hW2 : W (s + 1) ≤ W (s + 1 + 1) := by
        simp only [hW]
        have hp2 := hy (s + 1)
        exact div_le_div_of_nonneg_left hσ0.le hp2 (by nlinarith)
      constructor
      · have : W (s + 1) - u (s + 1) = (1 + c) * (W (s + 1) - u s) := by rw [hus]; ring
        nlinarith
      · rw [hus]
        push_cast
        nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (u t0 / (c * δ0))
  have h2 := (claim n).2
  have hcd : 0 < c * δ0 := mul_pos hc0 hδ0p
  rw [div_lt_iff₀ hcd] at hn
  linarith [hu0 (t0 + n)]

/-- Cochrane (2023), §9.3.2, pp. 266–267: on a bounded continuation path the continuation price is
nonincreasing, `x_{t+1} ≤ x_t`, and `x_t ≤ 1`. -/
theorem price_antitone (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ) (hp0 : 0 < p) (hp1 : p < 1)
    {M K : ℝ} {a x : ℕ → ℝ} (hx : ∀ t, 0 < x t) (hy : ∀ t, 0 < σ + (1 - β) * a (t + 1))
    (hflow : ∀ t, a t = x t - 1 + β * a (t + 1))
    (hrate : ∀ t, x t * (p / (σ + (1 - β) * a (t + 1)) + (1 - p) / x (t + 1)) = p / σ + (1 - p))
    (hxM : ∀ t, x t ≤ M) (haK : ∀ t, a t ≤ K) (t : ℕ) :
    x (t + 1) ≤ x t ∧ x t ≤ 1 := by
  have hσ0 : 0 < σ := by linarith
  have h1β : 0 < 1 - β := by linarith
  have hkey := settled_ge_price hβ0 hβ1 hσ hp0 hp1 hx hy hflow hrate hxM haK t
  have hnp := orbit_all_nonpos hβ0 hβ1 hσ hp0 hp1 hx hy hflow hrate hxM haK (t + 1)
  have hrec := rate_inv hσ hp1 hx hy hrate t
  have hc0 : 0 < p / (σ * (1 - p)) := div_pos hp0 (mul_pos hσ0 (by linarith))
  have hδ : σ / (σ + (1 - β) * a (t + 1)) - 1 / x t ≤ 0 := by
    rw [sub_nonpos, div_le_div_iff₀ (hy t) (hx t)]
    linarith
  constructor
  · have : 1 / x t ≤ 1 / x (t + 1) := by rw [hrec]; nlinarith
    rwa [div_le_div_iff₀ (hx t) (hx (t + 1)), one_mul, one_mul] at this
  · nlinarith

/-- Cochrane (2023), §9.3.2, pp. 266–267: on a bounded continuation path the scaled debt
deviation is nonincreasing, `D_{t+1} ≤ D_t`. If it rose once, `η_t = (1 − β) D_t + 1 − x_t`
(`β (D_{t+1} − D_t) = η_t`) would stay above its initial positive value and `D` would become
positive, contradicting `orbit_all_nonpos`. -/
theorem debt_antitone (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ) (hp0 : 0 < p) (hp1 : p < 1)
    {M K : ℝ} {a x : ℕ → ℝ} (hx : ∀ t, 0 < x t) (hy : ∀ t, 0 < σ + (1 - β) * a (t + 1))
    (hflow : ∀ t, a t = x t - 1 + β * a (t + 1))
    (hrate : ∀ t, x t * (p / (σ + (1 - β) * a (t + 1)) + (1 - p) / x (t + 1)) = p / σ + (1 - p))
    (hxM : ∀ t, x t ≤ M) (haK : ∀ t, a t ≤ K) (t : ℕ) : a (t + 1) ≤ a t := by
  have hnp := orbit_all_nonpos hβ0 hβ1 hσ hp0 hp1 hx hy hflow hrate hxM haK
  have hxa := price_antitone hβ0 hβ1 hσ hp0 hp1 hx hy hflow hrate hxM haK
  have h1β : 0 < 1 - β := by linarith
  have hstep : ∀ s, β * (a (s + 1) - a s) = (1 - β) * a s + 1 - x s := fun s => by
    have := hflow s
    linarith
  by_contra hcon
  push Not at hcon
  set η0 := (1 - β) * a t + 1 - x t with hη0
  have hη0p : 0 < η0 := by
    have := hstep t
    rw [← hη0] at this
    have : 0 < β * (a (t + 1) - a t) := mul_pos hβ0 (by linarith)
    linarith
  have claim : ∀ n : ℕ, η0 ≤ (1 - β) * a (t + n) + 1 - x (t + n) ∧
      a t + n * (η0 / β) ≤ a (t + n) := by
    intro n
    induction n with
    | zero => simp [hη0]
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      set s := t + n with hs
      have es : t + (n + 1) = s + 1 := by omega
      rw [es]
      have hd := hstep s
      have hd' : a (s + 1) - a s = ((1 - β) * a s + 1 - x s) / β := by
        field_simp
        linarith
      have hx1 := (hxa s).1
      have hpos : 0 ≤ (1 - β) * a s + 1 - x s := hη0p.le.trans h1
      have hq : η0 / β ≤ ((1 - β) * a s + 1 - x s) / β :=
        div_le_div_of_nonneg_right h1 hβ0.le
      constructor
      · have : 0 ≤ (1 - β) * (a (s + 1) - a s) := by
          rw [hd']
          exact mul_nonneg h1β.le (div_nonneg hpos hβ0.le)
        nlinarith
      · push_cast
        nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (-a t / (η0 / β))
  have hq : 0 < η0 / β := div_pos hη0p hβ0
  rw [div_lt_iff₀ hq] at hn
  have := (claim n).2
  linarith [hnp (t + n)]

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the continuation prices tend to zero**): on a bounded
continuation path with `D_0 < 0`, the continuation price tends to `0` and the scaled debt
deviation tends to `D* = −1/(1 − β)`. Both are monotone (`price_antitone`, `debt_antitone`); a
positive limit price would make the limit a fixed point of the flow and (9.12), whose only fixed
point is `(D, x) = (0, 1)`, impossible as `D` is nonincreasing from `D_0 < 0`. -/
theorem orbit_limits (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ) (hp0 : 0 < p) (hp1 : p < 1)
    {M K : ℝ} {a x : ℕ → ℝ} (hx : ∀ t, 0 < x t) (hy : ∀ t, 0 < σ + (1 - β) * a (t + 1))
    (hflow : ∀ t, a t = x t - 1 + β * a (t + 1))
    (hrate : ∀ t, x t * (p / (σ + (1 - β) * a (t + 1)) + (1 - p) / x (t + 1)) = p / σ + (1 - p))
    (hxM : ∀ t, x t ≤ M) (haK : ∀ t, a t ≤ K) (ha0 : a 0 < 0) :
    Tendsto x atTop (𝓝 0) ∧ Tendsto a atTop (𝓝 (Dst β)) := by
  have hσ0 : 0 < σ := by linarith
  have h1β : 0 < 1 - β := by linarith
  have hxa : Antitone x := antitone_nat_of_succ_le fun t =>
    (price_antitone hβ0 hβ1 hσ hp0 hp1 hx hy hflow hrate hxM haK t).1
  have haa : Antitone a := antitone_nat_of_succ_le fun t =>
    debt_antitone hβ0 hβ1 hσ hp0 hp1 hx hy hflow hrate hxM haK t
  -- lower bounds
  have hxB : BddBelow (Set.range x) := ⟨0, by rintro _ ⟨t, rfl⟩; exact (hx t).le⟩
  have haL : ∀ t, -(σ / (1 - β)) ≤ a t := fun t => by
    have h1 := hy t
    have h2 := haa (Nat.le_succ t)
    have : -(σ / (1 - β)) < a (t + 1) := by
      rw [neg_lt, lt_div_iff₀ h1β]
      nlinarith
    linarith
  have haB : BddBelow (Set.range a) := ⟨-(σ / (1 - β)), by rintro _ ⟨t, rfl⟩; exact haL t⟩
  set L := ⨅ t, x t with hL
  set A := ⨅ t, a t with hA
  have hxL : Tendsto x atTop (𝓝 L) := tendsto_atTop_ciInf hxa hxB
  have haA : Tendsto a atTop (𝓝 A) := tendsto_atTop_ciInf haa haB
  have hxL1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 L) := hxL.comp (tendsto_add_atTop_nat 1)
  have haA1 : Tendsto (fun t => a (t + 1)) atTop (𝓝 A) := haA.comp (tendsto_add_atTop_nat 1)
  have hL0 : 0 ≤ L := le_ciInf fun t => (hx t).le
  have hAa0 : A ≤ a 0 := ciInf_le haB 0
  -- the flow in the limit
  have hflowL : A = L - 1 + β * A := by
    have h1 : Tendsto (fun t => x t - 1 + β * a (t + 1)) atTop (𝓝 (L - 1 + β * A)) :=
      (hxL.sub_const 1).add (haA1.const_mul β)
    have h2 : Tendsto (fun t => x t - 1 + β * a (t + 1)) atTop (𝓝 A) :=
      haA.congr fun t => hflow t
    exact tendsto_nhds_unique h2 h1
  have hLz : L = 0 := by
    by_contra hne
    have hLp : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hne)
    have hyA : 0 < σ + (1 - β) * A := by nlinarith
    have hT : Tendsto (fun t => x t * (p / (σ + (1 - β) * a (t + 1)) + (1 - p) / x (t + 1)))
        atTop (𝓝 (L * (p / (σ + (1 - β) * A) + (1 - p) / L))) :=
      hxL.mul (((tendsto_const_nhds.add (haA1.const_mul (1 - β))).inv₀ hyA.ne'
        |>.const_mul p |>.congr fun t => by simp [div_eq_mul_inv]).add
        ((hxL1.inv₀ hLp.ne').const_mul (1 - p) |>.congr fun t => by simp [div_eq_mul_inv]))
    have hT2 : L * (p / (σ + (1 - β) * A) + (1 - p) / L) = p / σ + (1 - p) :=
      tendsto_nhds_unique hT (tendsto_const_nhds.congr fun t => (hrate t).symm)
    have e : (1 - β) * A = L - 1 := by linarith
    rw [e] at hT2 hyA
    have hy' : 0 < σ + (L - 1) := hyA
    field_simp at hT2
    have : (σ - 1) * (L - 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · have hL1 : L = 1 := by linarith
      rw [hL1] at e
      have : A = 0 := by
        have : (1 - β) * A = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact h
      linarith
  refine ⟨hLz ▸ hxL, ?_⟩
  have : A = Dst β := by
    rw [hLz] at hflowL
    simp only [Dst]
    field_simp
    linarith
  exact this ▸ haA

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the rate of decay**): on a bounded continuation path
with `D_0 < 0` the continuation price falls asymptotically geometrically,
`x_{t+1}/x_t → (1 − p)/γ` with `γ = p/σ + 1 − p` (`TidyR5ExistSet.gam`). -/
theorem orbit_ratio (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ) (hp0 : 0 < p) (hp1 : p < 1)
    {M K : ℝ} {a x : ℕ → ℝ} (hx : ∀ t, 0 < x t) (hy : ∀ t, 0 < σ + (1 - β) * a (t + 1))
    (hflow : ∀ t, a t = x t - 1 + β * a (t + 1))
    (hrate : ∀ t, x t * (p / (σ + (1 - β) * a (t + 1)) + (1 - p) / x (t + 1)) = p / σ + (1 - p))
    (hxM : ∀ t, x t ≤ M) (haK : ∀ t, a t ≤ K) (ha0 : a 0 < 0) :
    Tendsto (fun t => x (t + 1) / x t) atTop (𝓝 ((1 - p) / gam p σ)) := by
  have hσ0 : 0 < σ := by linarith
  have h1β : 0 < 1 - β := by linarith
  obtain ⟨hx0, haD⟩ := orbit_limits hβ0 hβ1 hσ hp0 hp1 hx hy hflow hrate hxM haK ha0
  obtain ⟨-, e2⟩ := Dst_props hβ1
  have haD1 : Tendsto (fun t => a (t + 1)) atTop (𝓝 (Dst β)) :=
    haD.comp (tendsto_add_atTop_nat 1)
  have hyD : σ + (1 - β) * Dst β = σ - 1 := by rw [e2]; ring
  have hy1 : Tendsto (fun t => σ + (1 - β) * a (t + 1)) atTop (𝓝 (σ - 1)) := by
    rw [← hyD]
    exact tendsto_const_nhds.add (haD1.const_mul (1 - β))
  -- `x_{t+1}/x_t = (1 - p) / (γ - p x_t / y_{t+1})`
  have hform : ∀ t, x (t + 1) / x t =
      (1 - p) / (gam p σ - p * x t / (σ + (1 - β) * a (t + 1))) := fun t => by
    have h := hrate t
    have hX := (hx t).ne'
    have hZ := (hx (t + 1)).ne'
    have hY := (hy t).ne'
    have hden : gam p σ - p * x t / (σ + (1 - β) * a (t + 1)) = (1 - p) * x t / x (t + 1) := by
      unfold gam
      rw [← h]
      field_simp
      ring
    rw [hden]
    have h1p : 1 - p ≠ 0 := by linarith
    field_simp
  have hden : Tendsto (fun t => gam p σ - p * x t / (σ + (1 - β) * a (t + 1))) atTop
      (𝓝 (gam p σ)) := by
    have : Tendsto (fun t => p * x t / (σ + (1 - β) * a (t + 1))) atTop (𝓝 (p * 0 / (σ - 1))) :=
      (hx0.const_mul p).div hy1 (by linarith)
    simpa using (tendsto_const_nhds (x := gam p σ)).sub this
  have hγ : 0 < gam p σ := by unfold gam; have : 0 < p / σ := div_pos hp0 hσ0; linarith
  exact (tendsto_const_nhds.div hden hγ.ne').congr fun t => (hform t).symm

/-- Cochrane (2023), §9.3.2, pp. 266–267: on a bounded continuation path with `D_0 = 0` the path
is the target's, `x ≡ 1` and `D ≡ 0`. -/
theorem orbit_zero (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ) (hp0 : 0 < p) (hp1 : p < 1)
    {M K : ℝ} {a x : ℕ → ℝ} (hx : ∀ t, 0 < x t) (hy : ∀ t, 0 < σ + (1 - β) * a (t + 1))
    (hflow : ∀ t, a t = x t - 1 + β * a (t + 1))
    (hrate : ∀ t, x t * (p / (σ + (1 - β) * a (t + 1)) + (1 - p) / x (t + 1)) = p / σ + (1 - p))
    (hxM : ∀ t, x t ≤ M) (haK : ∀ t, a t ≤ K) (ha0 : a 0 = 0) :
    ∀ t, a t = 0 ∧ x t = 1 := by
  have hnp := orbit_all_nonpos hβ0 hβ1 hσ hp0 hp1 hx hy hflow hrate hxM haK
  have hxa := price_antitone hβ0 hβ1 hσ hp0 hp1 hx hy hflow hrate hxM haK
  have haa := debt_antitone hβ0 hβ1 hσ hp0 hp1 hx hy hflow hrate hxM haK
  have hA : ∀ t, a t = 0 := by
    intro t
    induction t with
    | zero => exact ha0
    | succ t ih =>
      have h1 := hflow t
      have h2 := (hxa t).2
      have h3 := hnp (t + 1)
      rw [ih] at h1
      nlinarith
  intro t
  refine ⟨hA t, ?_⟩
  have := hflow t
  rw [hA t, hA (t + 1)] at this
  linarith

/-! ### The equilibrium statements -/

/-- Cochrane (2023), §9.3.2, pp. 266–267: in an equilibrium of the rule on `gSys` with target
`tgtS σ`, prices bounded above and `b₀ = b̄ + θ d₀`, the continuation path `(aC, P_t(t))`
satisfies all the hypotheses of `TidyR5NoExist.orbit_nonpos`, with `aC_0 = d₀`. -/
theorem eqm_orbit {θ bbar M d0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) (hσ : 1 < σ) {P b : ℕ → ℕ → ℝ}
    (hE : RuleEqm (gSys hp0 hp1) β θ bbar (tgtS σ) P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hb0 : ∀ ω, b 0 ω = bbar + θ * d0) :
    (∀ t, 0 < P t t) ∧ (∀ t, 0 < σ + (1 - β) * aC θ bbar b (t + 1)) ∧
      (∀ t, aC θ bbar b t = P t t - 1 + β * aC θ bbar b (t + 1)) ∧
      (∀ t, P t t * (p / (σ + (1 - β) * aC θ bbar b (t + 1)) + (1 - p) / P (t + 1) (t + 1)) =
        p / σ + (1 - p)) ∧ (∀ t, P (t + 1) t = σ + (1 - β) * aC θ bbar b (t + 1)) ∧
      (∃ K, ∀ t, aC θ bbar b t ≤ K) ∧ aC θ bbar b 0 = d0 := by
  obtain ⟨h1, h2, h3, K, hK⟩ := continuation_relations hp0 hp1 hβ0 hβ1 hθ hσ.le hE hPM
  have hP := hE.1
  refine ⟨fun t => hP t t, fun t => by rw [← h2 t]; exact hP _ _, h1, h3, h2, ⟨K, hK⟩, ?_⟩
  simp only [aC, hb0 0]
  field_simp
  ring

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the continuation prices tend to zero**): on the
settle-or-continue system (`σ > 1`, `0 < p < 1`, `0 < β < 1`, `θ ≠ 0`), every equilibrium of the
rule with prices bounded above and initial debt `b₀ = b̄ + θ d₀`, `d₀ < 0`, has continuation
prices `P_t` (on the path not yet settled) tending to `0` and scaled debt deviation tending to
`D* = −1/(1 − β)`. -/
theorem eqm_continuation_tendsto_zero {θ bbar M d0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) (hneg : d0 < 0) {P b : ℕ → ℕ → ℝ}
    (hE : RuleEqm (gSys hp0 hp1) β θ bbar (tgtS σ) P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hb0 : ∀ ω, b 0 ω = bbar + θ * d0) :
    Tendsto (fun t => P t t) atTop (𝓝 0) ∧ Tendsto (aC θ bbar b) atTop (𝓝 (Dst β)) := by
  obtain ⟨hx, hy, hfl, hr, -, ⟨K, hK⟩, h0⟩ := eqm_orbit hp0 hp1 hβ0 hβ1 hθ hσ hE hPM hb0
  exact orbit_limits hβ0 hβ1 hσ hp0 hp1 (x := fun t => P t t) hx hy hfl hr (fun t => hPM t t) hK
    (h0 ▸ hneg)

/-- Cochrane (2023), §9.3.2, pp. 266–267: in the same situation, the price on settlement at date
`t + 1` tends to `σ − 1`: a late settlement inherits the minimal debt `D*`. -/
theorem eqm_settled_tendsto {θ bbar M d0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) (hneg : d0 < 0) {P b : ℕ → ℕ → ℝ}
    (hE : RuleEqm (gSys hp0 hp1) β θ bbar (tgtS σ) P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hb0 : ∀ ω, b 0 ω = bbar + θ * d0) :
    Tendsto (fun t => P (t + 1) t) atTop (𝓝 (σ - 1)) := by
  obtain ⟨-, -, -, -, hset, -, -⟩ := eqm_orbit hp0 hp1 hβ0 hβ1 hθ hσ hE hPM hb0
  have hD := (eqm_continuation_tendsto_zero hp0 hp1 hβ0 hβ1 hθ hσ hneg hE hPM hb0).2
  obtain ⟨-, e2⟩ := Dst_props hβ1
  have h := tendsto_const_nhds (x := σ) |>.add ((hD.comp (tendsto_add_atTop_nat 1)).const_mul
    (1 - β))
  rw [e2] at h
  exact (h.congr fun t => (hset t).symm).trans (le_of_eq (by ring_nf))

/-- Cochrane (2023), §9.3.2, pp. 266–267: in the same situation the continuation prices decay
asymptotically geometrically, `P_{t+1}(continue)/P_t(continue) → (1 − p)/γ`, `γ = p/σ + 1 − p`. -/
theorem eqm_ratio_tendsto {θ bbar M d0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) (hneg : d0 < 0) {P b : ℕ → ℕ → ℝ}
    (hE : RuleEqm (gSys hp0 hp1) β θ bbar (tgtS σ) P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hb0 : ∀ ω, b 0 ω = bbar + θ * d0) :
    Tendsto (fun t => P (t + 1) (t + 1) / P t t) atTop (𝓝 ((1 - p) / gam p σ)) := by
  obtain ⟨hx, hy, hfl, hr, -, ⟨K, hK⟩, h0⟩ := eqm_orbit hp0 hp1 hβ0 hβ1 hθ hσ hE hPM hb0
  exact orbit_ratio hβ0 hβ1 hσ hp0 hp1 (x := fun t => P t t) hx hy hfl hr (fun t => hPM t t) hK
    (h0 ▸ hneg)

/-- Cochrane (2023), §9.3.2, pp. 266–267: in every equilibrium with prices bounded above (any
`d₀`), the continuation price is nonincreasing and at most `1`, and the scaled debt deviation is
nonincreasing. -/
theorem eqm_continuation_antitone {θ bbar M d0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) {P b : ℕ → ℕ → ℝ}
    (hE : RuleEqm (gSys hp0 hp1) β θ bbar (tgtS σ) P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hb0 : ∀ ω, b 0 ω = bbar + θ * d0) (t : ℕ) :
    P (t + 1) (t + 1) ≤ P t t ∧ P t t ≤ 1 ∧ aC θ bbar b (t + 1) ≤ aC θ bbar b t := by
  obtain ⟨hx, hy, hfl, hr, -, ⟨K, hK⟩, -⟩ := eqm_orbit hp0 hp1 hβ0 hβ1 hθ hσ hE hPM hb0
  exact ⟨(price_antitone hβ0 hβ1 hσ hp0 hp1 (x := fun t => P t t) hx hy hfl hr
      (fun t => hPM t t) hK t).1,
    (price_antitone hβ0 hβ1 hσ hp0 hp1 (x := fun t => P t t) hx hy hfl hr
      (fun t => hPM t t) hK t).2,
    debt_antitone hβ0 hβ1 hσ hp0 hp1 (x := fun t => P t t) hx hy hfl hr (fun t => hPM t t) hK t⟩

/-- Cochrane (2023), §9.3.2, pp. 266–267: with `d₀ = 0` every equilibrium with prices bounded
above follows the target on the continuation path and on settlement: `P_t(continue) = 1`,
`P_{t+1}(settle at t + 1) = σ`, `D ≡ 0`. -/
theorem eqm_zero_target {θ bbar M : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) {P b : ℕ → ℕ → ℝ}
    (hE : RuleEqm (gSys hp0 hp1) β θ bbar (tgtS σ) P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hb0 : ∀ ω, b 0 ω = bbar + θ * 0) (t : ℕ) :
    P t t = 1 ∧ P (t + 1) t = σ ∧ aC θ bbar b t = 0 := by
  obtain ⟨hx, hy, hfl, hr, hset, ⟨K, hK⟩, h0⟩ := eqm_orbit hp0 hp1 hβ0 hβ1 hθ hσ hE hPM hb0
  have h := orbit_zero hβ0 hβ1 hσ hp0 hp1 (x := fun t => P t t) hx hy hfl hr (fun t => hPM t t)
    hK h0
  refine ⟨(h t).2, ?_, (h t).1⟩
  rw [hset t, (h (t + 1)).1]
  ring

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**existence and the limit, together**): on the
settle-or-continue system, for every `d₀ ∈ (−1/(1 − β), 0)` an equilibrium with prices bounded
above and `b₀ = b̄ + θ d₀` exists (`TidyR5ExistSet.existsAbove_iff`), and in every such
equilibrium the continuation prices tend to `0`. -/
theorem exists_and_tendsto_zero {θ bbar d0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) (hl : -(1 / (1 - β)) < d0)
    (hneg : d0 < 0) :
    ExistsAbove (gSys hp0 hp1) β θ bbar (tgtS σ) d0 ∧
      ∀ (P b : ℕ → ℕ → ℝ) (M : ℝ), RuleEqm (gSys hp0 hp1) β θ bbar (tgtS σ) P b →
        (∀ t ω, P t ω ≤ M) → (∀ ω, b 0 ω = bbar + θ * d0) →
        Tendsto (fun t => P t t) atTop (𝓝 0) :=
  ⟨(existsAbove_iff hp0 hp1 hβ0 hβ1 hθ hσ).2 ⟨hl, hneg.le⟩, fun _ _ _ hE hPM hb0 =>
    (eqm_continuation_tendsto_zero hp0 hp1 hβ0 hβ1 hθ hσ hneg hE hPM hb0).1⟩

end Cochrane.AssetsRulesBalanceSheets.TidyR6ContinuationLimit
