/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.TidyR6CriticalCriterion
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Composition

/-!
# Analytic critical directions: the higher-order terms always decide

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 632–634. For the scalar forward system
`E_t[x_{t+1} − g(x_t)] = 0` with a critical root `g'(0) = σ = ±1`,
`TidyR6CriticalCriterion.coin_sunspots_iff` decides the sunspot question whenever `g ∘ g − id`
has a nonzero leading term, and `TidyR6CriticalCriterion.flat_undecided` shows that for `C^∞`
maps the Taylor jet can vanish while the answer still depends on the map. For **analytic** `g`
neither gap remains: either `g ∘ g` is the identity near the steady state (then every small orbit
is periodic and random sunspots exist), or `g ∘ g − id` has a nonzero leading term `c xᵐ`,
`m ≥ 2`, and the criterion applies. This is a complete characterisation in the higher-order
terms.

## Main results

* `coinSunspots_of_involutive`: `g ∘ g = id` near `0` ⟹ random sunspots at every scale.
* `analytic_dichotomy`: for analytic `g`, `g ∘ g = id` near `0` or
  `g(g(x)) = x + c xᵐ + o(xᵐ)` with `c ≠ 0`, `m ≥ 2`.
* `analytic_coin_sunspots_iff` (**the characterisation**): for analytic `g` with `g(0) = 0`,
  `g'(0) = ±1`, random sunspots exist at every scale on the coin tree **iff** `g ∘ g = id` near
  the steady state, or the leading coefficient `c` of `g ∘ g − id` is negative, or its order is
  even.
-/

namespace Woodford.PriceLevelDetermination.TidyR6CriticalAnalytic

open scoped Topology
open Asymptotics Filter
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic TidyR6ForwardSunspots
open TidyR6CriticalCriterion (lift norm_fin1 CoinSunspots near_lip coin_sunspots_iff)

/-- **Random sunspots when `g ∘ g` is the identity near the steady state** (Woodford (2003),
App. A.3, pp. 632–634): if `g(0) = 0`, `g'(0) = σ`, `σ² = 1`, and `g(g(x)) = x` near `0`, the
scalar forward system has random sunspots at every scale on the coin tree (`x_1 = ±a`, then the
orbit is periodic). -/
theorem coinSunspots_of_involutive {g : ℝ → ℝ} {σ : ℝ} (hσ : σ * σ = 1) (hg0 : g 0 = 0)
    (hd : HasDerivAt g σ 0) (hinv : ∀ᶠ x in 𝓝 0, g (g x) = x) : CoinSunspots g := by
  intro ε hε
  obtain ⟨r, hr, hrP⟩ := Metric.eventually_nhds_iff.mp hinv
  obtain ⟨δ1, hδ1, hL⟩ := near_lip hσ hg0 hd
  set ρ := min r δ1 / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ < r := by have := min_le_left r δ1; linarith
  have hρδ : ρ < δ1 := by have := min_le_right r δ1; linarith
  set A : Set (Fin 1 → ℝ) := {v | |v 0| ≤ ρ} with hA
  have hgg : ∀ v ∈ A, lift g (lift g v) = v := by
    intro v hv
    funext i
    fin_cases i
    exact hrP (show dist (v 0) 0 < r by rw [Real.dist_0_eq_abs]; linarith [hv.out])
  have hAinv : ∀ v ∈ A, lift g (lift g v) ∈ A ∧ ‖lift g (lift g v)‖ ≤ ‖v‖ :=
    fun v hv => by rw [hgg v hv]; exact ⟨hv, le_rfl⟩
  have hAL : ∀ v ∈ A, ‖lift g v‖ ≤ 2 * ‖v‖ := by
    intro v hv
    rw [norm_fin1, norm_fin1]
    exact (hL (v 0) (lt_of_le_of_lt hv.out hρδ)).2
  set a := min ρ (ε / 2) with ha
  have ha0 : 0 < a := lt_min hρ0 (by positivity)
  have hy1 : (fun _ => a : Fin 1 → ℝ) ∈ A := by
    change |a| ≤ ρ
    rw [abs_of_pos ha0]
    exact min_le_left _ _
  have hy2 : (fun _ => -a : Fin 1 → ℝ) ∈ A := by
    change |-a| ≤ ρ
    rw [abs_neg, abs_of_pos ha0]
    exact min_le_left _ _
  have hne : (fun _ => a : Fin 1 → ℝ) ≠ fun _ => -a := by
    intro h
    have := congrFun h 0
    linarith
  have hc : lift g 0 = (1 / 2 : ℝ) • ((fun _ => a : Fin 1 → ℝ) + fun _ => -a) := by
    funext i
    simp [lift, hg0]
  obtain ⟨x, hx, hxn, hxr⟩ := coin_sunspot_of_pair (by norm_num : (1 : ℝ) ≤ 2) hAinv hAL hy1
    hy2 hne hc
  refine ⟨x, hx, hxn.trans ?_, hxr⟩
  rw [norm_zero, norm_fin1, norm_fin1]
  simp only [abs_neg, max_self, abs_of_pos ha0]
  have : a ≤ ε / 2 := min_le_right _ _
  exact max_le hε.le (by linarith)

/-- Woodford (2003), App. A.3, p. 634 (tool): a local factorisation `F(x) = xᵐ q(x)` with `q`
continuous at `0` is the expansion `F(x) = q(0) xᵐ + o(xᵐ)`. -/
theorem expansion_of_factor {F q : ℝ → ℝ} {m : ℕ} (hq : ContinuousAt q 0)
    (h : ∀ᶠ x in 𝓝 0, F x = x ^ m * q x) :
    (fun x => F x - q 0 * x ^ m) =o[𝓝 0] fun x => x ^ m := by
  have h1 : (fun x => q x - q 0) =o[𝓝 0] fun _ => (1 : ℝ) := by
    rw [isLittleO_one_iff]
    have := hq.tendsto
    simpa using this.sub_const (q 0)
  have h2 := (isBigO_refl (fun x : ℝ => x ^ m) (𝓝 0)).mul_isLittleO h1
  simp only [mul_one] at h2
  refine h2.congr' ?_ EventuallyEq.rfl
  filter_upwards [h] with x hx
  rw [hx]
  ring

/-- **The analytic dichotomy** (Woodford (2003), App. A.3, pp. 632–634): if `g` is analytic at
the steady state with `g(0) = 0` and `g'(0) = σ`, `σ² = 1`, then either `g ∘ g` is the identity
near `0`, or `g(g(x)) = x + c xᵐ + o(xᵐ)` with `c ≠ 0` and `m ≥ 2`. -/
theorem analytic_dichotomy {g : ℝ → ℝ} {σ : ℝ} (hσ : σ * σ = 1) (hg0 : g 0 = 0)
    (hd : HasDerivAt g σ 0) (han : AnalyticAt ℝ g 0) :
    (∀ᶠ x in 𝓝 0, g (g x) = x) ∨ ∃ c : ℝ, ∃ m : ℕ, c ≠ 0 ∧ 2 ≤ m ∧
      (fun x => g (g x) - x - c * x ^ m) =o[𝓝 0] fun x => x ^ m := by
  set F : ℝ → ℝ := fun x => g (g x) - x with hF
  have han' : AnalyticAt ℝ g (g 0) := by rw [hg0]; exact han
  have hFan : AnalyticAt ℝ F 0 := (han'.comp han).sub analyticAt_id
  have hGd : HasDerivAt (fun x => g (g x)) (σ * σ) 0 := by
    have hd' : HasDerivAt g σ (g 0) := by rw [hg0]; exact hd
    exact hd'.comp 0 hd
  have hFd : HasDerivAt F 0 0 := by
    have := hGd.sub (hasDerivAt_id 0)
    rw [hσ, sub_self] at this
    exact this
  by_cases hz : ∀ᶠ x in 𝓝 0, F x = 0
  · left
    filter_upwards [hz] with x hx
    exact sub_eq_zero.mp hx
  · right
    obtain ⟨n, q, hqan, hq0, hfac⟩ := hFan.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz
    have hfac' : ∀ᶠ x in 𝓝 0, F x = x ^ n * q x := by
      filter_upwards [hfac] with x hx
      rw [hx, sub_zero, smul_eq_mul]
    have hF0 : F 0 = 0 := by simp only [hF, hg0, sub_zero]
    have hn2 : 2 ≤ n := by
      by_contra hn
      push Not at hn
      interval_cases n
      · have h0 := hfac'.self_of_nhds
        rw [hF0, pow_zero, one_mul] at h0
        exact hq0 h0.symm
      · have hq' : HasDerivAt (fun x => x ^ 1 * q x) (q 0) 0 := by
          have h1 := (hasDerivAt_id' (x := (0 : ℝ))).mul hqan.differentiableAt.hasDerivAt
          simp only [one_mul, zero_mul, add_zero] at h1
          simp only [pow_one]
          exact h1
        have hFd' : HasDerivAt (fun x => x ^ 1 * q x) 0 0 :=
          hFd.congr_of_eventuallyEq (hfac'.mono fun x hx => hx.symm)
        exact hq0 (hq'.unique hFd')
    refine ⟨q 0, n, hq0, hn2, ?_⟩
    have := expansion_of_factor hqan.continuousAt hfac'
    refine this.congr_left fun x => ?_
    simp only [hF]

/-- **For analytic maps the higher-order terms always decide** (Woodford (2003), App. A.3,
pp. 632–634; the complete characterisation on a one-dimensional critical direction): let `g` be
analytic at the steady state with `g(0) = 0` and `g'(0) = σ`, `σ = ±1`. The scalar forward system
`E_t[x_{t+1} − g(x_t)] = 0` has random sunspot equilibria at every scale on the coin tree **iff**
`g ∘ g` is the identity near `0`, or `g(g(x)) = x + c xᵐ + o(xᵐ)` with `c ≠ 0`, `m ≥ 2` and
(`c < 0` or `m` even). (By `analytic_dichotomy` one of the two expansions always exists; by
`TidyR6CriticalCriterion.flat_undecided` analyticity cannot be weakened to `C^∞`.) -/
theorem analytic_coin_sunspots_iff {g : ℝ → ℝ} {σ : ℝ} (hσ : σ * σ = 1) (hg0 : g 0 = 0)
    (hd : HasDerivAt g σ 0) (han : AnalyticAt ℝ g 0) :
    CoinSunspots g ↔ ((∀ᶠ x in 𝓝 0, g (g x) = x) ∨ ∃ c : ℝ, ∃ m : ℕ, c ≠ 0 ∧ 2 ≤ m ∧
      ((fun x => g (g x) - x - c * x ^ m) =o[𝓝 0] fun x => x ^ m) ∧ (c < 0 ∨ Even m)) := by
  constructor
  · intro hsun
    rcases analytic_dichotomy hσ hg0 hd han with h | ⟨c, m, hc, hm, hexp⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, m, hc, hm, hexp, (coin_sunspots_iff hσ hg0 hd hm hc hexp).mp hsun⟩
  · rintro (h | ⟨c, m, hc, hm, hexp, hcrit⟩)
    · exact coinSunspots_of_involutive hσ hg0 hd h
    · exact (coin_sunspots_iff hσ hg0 hd hm hc hexp).mpr hcrit

end Woodford.PriceLevelDetermination.TidyR6CriticalAnalytic
