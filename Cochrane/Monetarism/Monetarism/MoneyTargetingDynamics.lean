/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.MoneyInUtility
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Monetary targeting dynamics: the global phase diagram of money in utility

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.3.2, pp. 441–445
(eqs. (19.17)–(19.23), Figure 19.1). Restated from the Woodford Chapter 2 project
(`GlobalDynamics` survey lemma L5 and `MoneyTargetingDynamics`, Woodford (2003), §4.1,
eqs. (4.7)–(4.9), pp. 123–133), adapted to this namespace, plus the global dynamics of
Cochrane's power example. Perfect foresight throughout.

## Restated from the Woodford Chapter 2 project

* One-dimensional maps: `orbit_monotone_of_le`, `orbit_antitone_of_ge`, `fixed_of_tendsto`,
  `monotone_orbit_atTop_or_fixed`, `antitone_orbit_atBot_or_fixed`, `sign_near_of_deriv_pos`,
  `repelling_of_one_lt_abs_deriv`, `attracting_of_abs_deriv_lt_one`.
* General utility (19.17): `Ffun`, `Gfun`, `eq48_iff_fisher`. Separable utility (19.18):
  `sepF`, `sepMap`, `eq48_sep_iff`, `sepF_pos`, `sepF_strictMonoOn`, `sepF_tendsto_zero`,
  `sepMap_tendsto_zero` (the second steady state at zero real balances), `sepMap_fixed_iff`
  ((19.19)), `sep_exists_steady_state`, `sep_single_crossing` (cuts from below),
  `IsSepPath`, `sep_path_exists_unique` (one equilibrium per initial price level),
  `sep_inflation_path`, `sep_deflation_path`.
* Satiation (p. 443): `IsPath48`, `Satiation`, `satiated_path`, `money_tvc_violated`,
  `sep_deflation_violates_tvc`, `money_contraction_continuum`.
  (Woodford's Taylor-rule transversality section, E4, the Obstfeld–Rogoff section and the
  convexity counterexample E7 are not restated: they concern interest-rate rules, Appendix A3
  (chain B) and a Woodford-specific claim.)

## New for Cochrane

* `miuPath_iff_sepPath`: Cochrane's (19.18) with constant money growth is Woodford's separable
  map with `μ̄ = 1 + µ`, `c = u_c(y)`, `v' = u_m`.
* Power example (19.23), Figure 19.1: `nextX_fixed`, `nextX_pos`, `nextX_lt_iff`,
  `power_steady_repelling` (the inflationary steady state is unstable), `fig191_repelling`,
  `power_deflation_orbit` (every path started below `x̄` converges to the deflationary steady
  state `x = 0` with `x_{t+1}/x_t → β/(1 + µ)`), `power_deflation_inflation`
  (`P_{t+1}/P_t → β = 1/(1 + δ)`), `power_inflation_exits` (every path started above `x̄` reaches
  `θx^γ ≥ 1`, i.e. `u_m/u_c ≥ 1`, in finite time, so it is not an equilibrium).
* Survey error E13, globally: `e13_no_deflation_attractor` (if `1 + µ ≤ β` no path converges
  to `x = 0`); with `power_deflation_orbit` the deflationary steady state attracts iff
  `1 + µ > β`.
-/

namespace Cochrane.Monetarism.MoneyTargetingDynamics

open Filter Topology
open Cochrane.Monetarism.MoneyInUtility (nextX nextX_hasDerivAt slope_gt_one xbar191
  fig191_steady)

/-! ## L5: one-dimensional monotone maps -/

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Survey lemma L5 (used in Woodford (2003), §4.1–4.3, pp. 123–138): if `g` is monotone on an
invariant set `S` and the orbit `x_{t+1} = g(x_t)` starts in `S` with `x₀ ≤ x₁`, the orbit is
monotone. -/
theorem orbit_monotone_of_le {g : ℝ → ℝ} {S : Set ℝ} (hmono : MonotoneOn g S)
    (hmaps : Set.MapsTo g S S) {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = g (x t)) (h0 : x 0 ∈ S)
    (hle : x 0 ≤ x 1) : Monotone x := by
  have hmem : ∀ t, x t ∈ S := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih => rw [hx]; exact hmaps ih
  refine monotone_nat_of_le_succ fun t => ?_
  induction t with
  | zero => exact hle
  | succ n ih =>
    calc x (n + 1) = g (x n) := hx n
      _ ≤ g (x (n + 1)) := hmono (hmem n) (hmem (n + 1)) ih
      _ = x (n + 1 + 1) := (hx (n + 1)).symm

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Survey lemma L5 (Woodford (2003), §4.1–4.3): if `g` is monotone on an invariant set `S` and
the orbit starts in `S` with `x₁ ≤ x₀`, the orbit is antitone. -/
theorem orbit_antitone_of_ge {g : ℝ → ℝ} {S : Set ℝ} (hmono : MonotoneOn g S)
    (hmaps : Set.MapsTo g S S) {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = g (x t)) (h0 : x 0 ∈ S)
    (hge : x 1 ≤ x 0) : Antitone x := by
  have hmem : ∀ t, x t ∈ S := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih => rw [hx]; exact hmaps ih
  refine antitone_nat_of_succ_le fun t => ?_
  induction t with
  | zero => exact hge
  | succ n ih =>
    calc x (n + 1 + 1) = g (x (n + 1)) := hx (n + 1)
      _ ≤ g (x n) := hmono (hmem (n + 1)) (hmem n) ih
      _ = x (n + 1) := (hx n).symm

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Survey lemma L5 (Woodford (2003), §4.1): a limit of an orbit `x_{t+1} = g(x_t)` at which
`g` is continuous is a fixed point of `g`. -/
theorem fixed_of_tendsto {g : ℝ → ℝ} {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = g (x t)) {L : ℝ}
    (hL : Tendsto x atTop (𝓝 L)) (hc : ContinuousAt g L) : g L = L := by
  have h1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 L) := (tendsto_add_atTop_iff_nat 1).mpr hL
  have h2 : Tendsto (fun t => x (t + 1)) atTop (𝓝 (g L)) := by
    have : (fun t => x (t + 1)) = g ∘ x := funext fun t => hx t
    rw [this]
    exact hc.tendsto.comp hL
  exact tendsto_nhds_unique h2 h1

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Survey lemma L5 (Woodford (2003), §4.1): a monotone orbit either diverges to `+∞` or
converges to a limit bounding it from above, which is a fixed point wherever `g` is
continuous. -/
theorem monotone_orbit_atTop_or_fixed {g : ℝ → ℝ} {x : ℕ → ℝ}
    (hx : ∀ t, x (t + 1) = g (x t)) (hmono : Monotone x) :
    Tendsto x atTop atTop ∨
      ∃ L, Tendsto x atTop (𝓝 L) ∧ (∀ t, x t ≤ L) ∧ (ContinuousAt g L → g L = L) := by
  by_cases hb : BddAbove (Set.range x)
  · right
    refine ⟨⨆ t, x t, tendsto_atTop_ciSup hmono hb, fun t => le_ciSup hb t, fun hc => ?_⟩
    exact fixed_of_tendsto hx (tendsto_atTop_ciSup hmono hb) hc
  · left
    refine tendsto_atTop_atTop_of_monotone hmono fun b => ?_
    rw [not_bddAbove_iff] at hb
    obtain ⟨y, ⟨t, rfl⟩, hy⟩ := hb b
    exact ⟨t, hy.le⟩

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Survey lemma L5 (Woodford (2003), §4.1): an antitone orbit either diverges to `−∞` or
converges to a limit bounding it from below, which is a fixed point wherever `g` is
continuous. -/
theorem antitone_orbit_atBot_or_fixed {g : ℝ → ℝ} {x : ℕ → ℝ}
    (hx : ∀ t, x (t + 1) = g (x t)) (hanti : Antitone x) :
    Tendsto x atTop atBot ∨
      ∃ L, Tendsto x atTop (𝓝 L) ∧ (∀ t, L ≤ x t) ∧ (ContinuousAt g L → g L = L) := by
  by_cases hb : BddBelow (Set.range x)
  · right
    refine ⟨⨅ t, x t, tendsto_atTop_ciInf hanti hb, fun t => ciInf_le hb t, fun hc => ?_⟩
    exact fixed_of_tendsto hx (tendsto_atTop_ciInf hanti hb) hc
  · left
    refine tendsto_atTop_atBot_of_antitone hanti fun b => ?_
    rw [not_bddBelow_iff] at hb
    obtain ⟨y, ⟨t, rfl⟩, hy⟩ := hb b
    exact ⟨t, hy.le⟩

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Survey lemma L5 (Woodford (2003), p. 125): near a point where `f` has a positive derivative,
`f` is below `f x` just to the left and above `f x` just to the right. -/
theorem sign_near_of_deriv_pos {f : ℝ → ℝ} {x c : ℝ} (hd : HasDerivAt f c x) (hc : 0 < c) :
    ∃ δ > 0, (∀ y, x - δ < y → y < x → f y < f x) ∧ (∀ y, x < y → y < x + δ → f x < f y) := by
  have hlo := (hasDerivAt_iff_isLittleO.mp hd).def (half_pos hc)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  refine ⟨δ, hδ, fun y h1 h2 => ?_, fun y h1 h2 => ?_⟩
  · have hy : dist y x < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hball hy
    simp only [Real.norm_eq_abs, smul_eq_mul] at this
    rw [abs_of_neg (by linarith : y - x < 0)] at this
    have := (abs_le.mp this).2
    nlinarith
  · have hy : dist y x < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hball hy
    simp only [Real.norm_eq_abs, smul_eq_mul] at this
    rw [abs_of_pos (by linarith : 0 < y - x)] at this
    have := (abs_le.mp this).1
    nlinarith

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Survey lemma L5, "slope > 1 ⇒ repelling" (Woodford (2003), p. 127): if `g(x*) = x*` and
`|g'(x*)| > 1`, there is `δ > 0` such that every orbit not starting at `x*` eventually lies at
distance at least `δ` from `x*`. -/
theorem repelling_of_one_lt_abs_deriv {g : ℝ → ℝ} {xs d : ℝ} (hfix : g xs = xs)
    (hd : HasDerivAt g d xs) (h1 : 1 < |d|) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = g (x t)) → x 0 ≠ xs →
      ∃ t, δ ≤ |x t - xs| := by
  have hε : 0 < (|d| - 1) / 2 := by linarith
  have hlo := (hasDerivAt_iff_isLittleO.mp hd).def hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  refine ⟨δ, hδ, fun x hx hx0 => ?_⟩
  by_contra hcon
  push Not at hcon
  set k := (|d| + 1) / 2 with hk
  have hk1 : 1 < k := by rw [hk]; linarith
  have hstep : ∀ y, |y - xs| < δ → k * |y - xs| ≤ |g y - xs| := by
    intro y hy
    have h := hball (by rwa [Real.dist_eq])
    simp only [Real.norm_eq_abs, smul_eq_mul, hfix] at h
    have h2 : |(y - xs) * d| ≤ |g y - xs - (y - xs) * d| + |g y - xs| := by
      have := abs_sub (g y - xs) (g y - xs - (y - xs) * d)
      simp only [sub_sub_cancel] at this
      linarith [abs_sub_comm (g y - xs - (y - xs) * d) (g y - xs)]
    rw [abs_mul] at h2
    nlinarith [abs_nonneg (y - xs)]
  have hgrow : ∀ t, k ^ t * |x 0 - xs| ≤ |x t - xs| := by
    intro t
    induction t with
    | zero => simp
    | succ n ih =>
      rw [hx n, pow_succ]
      have := hstep (x n) (hcon n)
      nlinarith [abs_nonneg (x n - xs)]
  have hpos : 0 < |x 0 - xs| := abs_pos.mpr (sub_ne_zero.mpr hx0)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (δ / |x 0 - xs|) hk1
  have h3 : δ < k ^ n * |x 0 - xs| := by rwa [div_lt_iff₀ hpos] at hn
  linarith [hgrow n, hcon n]

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Survey lemma L5 (Woodford (2003), p. 127, "local indeterminacy near `Π**`"): if
`g(x*) = x*` and `|g'(x*)| < 1`, every orbit starting within `δ` of `x*` stays within `δ`,
never moves farther from `x*` than it started, and converges to `x*`. -/
theorem attracting_of_abs_deriv_lt_one {g : ℝ → ℝ} {xs d : ℝ} (hfix : g xs = xs)
    (hd : HasDerivAt g d xs) (h1 : |d| < 1) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = g (x t)) → |x 0 - xs| < δ →
      (∀ t, |x t - xs| < δ) ∧ (∀ t, |x t - xs| ≤ |x 0 - xs|) ∧
        Tendsto x atTop (𝓝 xs) := by
  have hε : 0 < (1 - |d|) / 2 := by linarith
  have hlo := (hasDerivAt_iff_isLittleO.mp hd).def hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  refine ⟨δ, hδ, fun x hx hx0 => ?_⟩
  set k := (|d| + 1) / 2 with hk
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hk1 : k < 1 := by rw [hk]; linarith
  have hstep : ∀ y, |y - xs| < δ → |g y - xs| ≤ k * |y - xs| := by
    intro y hy
    have h := hball (by rwa [Real.dist_eq])
    simp only [Real.norm_eq_abs, smul_eq_mul, hfix] at h
    have h2 : |g y - xs| ≤ |g y - xs - (y - xs) * d| + |(y - xs) * d| := by
      have := abs_add_le (g y - xs - (y - xs) * d) ((y - xs) * d)
      simpa using this
    rw [abs_mul] at h2
    nlinarith [abs_nonneg (y - xs)]
  have hbd : ∀ t, |x t - xs| ≤ k ^ t * |x 0 - xs| ∧ |x t - xs| < δ := by
    intro t
    induction t with
    | zero => exact ⟨by simp, hx0⟩
    | succ n ih =>
      rw [hx n]
      have h := hstep (x n) ih.2
      have hpow : k ^ (n + 1) * |x 0 - xs| = k * (k ^ n * |x 0 - xs|) := by ring
      refine ⟨by rw [hpow]; nlinarith [ih.1], ?_⟩
      nlinarith [ih.2, abs_nonneg (x n - xs)]
  refine ⟨fun t => (hbd t).2, fun t => ?_, ?_⟩
  · have hkt : k ^ t ≤ 1 := pow_le_one₀ hk0 hk1.le
    nlinarith [(hbd t).1, abs_nonneg (x 0 - xs)]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => (hbd t).1) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const |x 0 - xs|


/-! ## (4.7)–(4.8) -/

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.7), p. 129: `F(m) = [U_c(ȳ, m) − U_m(ȳ, m)]m`. -/
def Ffun (Uc Um : ℝ → ℝ) (m : ℝ) : ℝ := (Uc m - Um m) * m

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.7), p. 129: `G(m) = U_c(ȳ, m)m`. -/
def Gfun (Uc : ℝ → ℝ) (m : ℝ) : ℝ := Uc m * m

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.7)–(4.8), p. 129, derivation: at a date with `m_t = M_t/P_t`,
`m_{t+1} = μ̄M_t/P_{t+1}`, the money-demand condition (3.3) `U_m/U_c = i/(1+i)` (`i^m = 0`), and
`U_c > 0`, `U_c − U_m > 0`, the perfect-foresight Fisher equation (1.21) holds iff
`U_c(m_{t+1})m_{t+1} = (μ̄/β)[U_c(m_t) − U_m(m_t)]m_t`, i.e. `G(m_{t+1}) = (μ̄/β)F(m_t)`. -/
theorem eq48_iff_fisher {β μ P P1 M m m1 i uc uc1 um : ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hP : 0 < P) (hP1 : 0 < P1) (hM : 0 < M) (huc : 0 < uc) (huc1 : 0 < uc1)
    (hgap : 0 < uc - um) (hm : m = M / P) (hm1 : m1 = μ * M / P1)
    (h33 : um / uc = i / (1 + i)) (hi : 0 < 1 + i) :
    (1 + i = β⁻¹ * ((uc1 / uc) * (P / P1))⁻¹) ↔ uc1 * m1 = μ / β * ((uc - um) * m) := by
  have hi' : 1 + i = uc / (uc - um) := by
    rw [div_eq_div_iff huc.ne' hi.ne'] at h33
    rw [eq_div_iff hgap.ne']
    linarith
  have hR : β⁻¹ * ((uc1 / uc) * (P / P1))⁻¹ = uc * P1 / (β * uc1 * P) := by
    field_simp
  have eL : uc1 * (μ * M / P1) = (β * uc1 * P) * (μ * M / (β * P * P1)) := by
    field_simp
  have eR : μ / β * ((uc - um) * (M / P)) = ((uc - um) * P1) * (μ * M / (β * P * P1)) := by
    field_simp
  rw [hi', hR, div_eq_div_iff hgap.ne' (by positivity), hm, hm1, eL, eR,
    mul_left_inj' (ne_of_gt (by positivity))]
  constructor
  · intro h
    exact mul_left_cancel₀ huc.ne' (by linarith [h])
  · intro h
    rw [h]; ring

/-! ## The separable case: Figure 2.5 -/

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, additively separable case: `F(m) = (c − v'(m))m`, where `c > 0` is
the (constant) marginal utility of consumption at `ȳ` and `v'(m) = U_m`. -/
def sepF (c : ℝ) (vp : ℝ → ℝ) (m : ℝ) : ℝ := (c - vp m) * m

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), Figure 2.5, p. 130: the graph `m ↦ G⁻¹((μ̄/β)F(m))` for `G(m) = cm`. -/
noncomputable def sepMap (β μ c : ℝ) (vp : ℝ → ℝ) (m : ℝ) : ℝ := μ / β * sepF c vp m / c

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.8), p. 130: in the separable case `G(m) = cm` is linear and can be
inverted, so `G(m') = (μ̄/β)F(m)` iff `m'` is the value of the map of Figure 2.5. -/
theorem eq48_sep_iff {β μ c m m' : ℝ} {vp : ℝ → ℝ} (hc : 0 < c) :
    c * m' = μ / β * sepF c vp m ↔ m' = sepMap β μ c vp m := by
  unfold sepMap
  rw [eq_div_iff hc.ne']
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130: if `U_c − U_m = c − v'(m) > 0` for `m > 0`, then `F(m) > 0`. -/
theorem sepF_pos {c m : ℝ} {vp : ℝ → ℝ} (hgap : c - vp m > 0) (hm : 0 < m) : 0 < sepF c vp m :=
  mul_pos hgap hm

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, "`F(m)` equals `m` times an increasing function of `m`": with `v'`
nonincreasing (concave `v`) and `c − v' > 0`, `F` is strictly increasing on `(0, ∞)`. -/
theorem sepF_strictMonoOn {c : ℝ} {vp : ℝ → ℝ} (hanti : AntitoneOn vp (Set.Ioi 0))
    (hgap : ∀ m, 0 < m → vp m < c) : StrictMonoOn (sepF c vp) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hvp : vp b ≤ vp a := hanti ha hb hab.le
  have h1 := hgap a ha'
  unfold sepF
  nlinarith

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, "takes the limiting value `F(0) = 0`": under the hypotheses of
`sepF_strictMonoOn`, `F(m) → 0` as `m → 0⁺`. -/
theorem sepF_tendsto_zero {c : ℝ} {vp : ℝ → ℝ} (hanti : AntitoneOn vp (Set.Ioi 0))
    (hgap : ∀ m, 0 < m → vp m < c) : Tendsto (sepF c vp) (𝓝[>] 0) (𝓝 0) := by
  have hup : Tendsto (fun m : ℝ => (c - vp 1) * m) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun m : ℝ => (c - vp 1) * m) (𝓝 0) (𝓝 ((c - vp 1) * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with m hm
    exact (sepF_pos (by linarith [hgap m hm]) hm).le
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with m hm hm1
    unfold sepF
    have : vp 1 ≤ vp m := hanti hm (Set.mem_Ioi.mpr one_pos) hm1.2.le
    have hm' : (0 : ℝ) < m := hm
    nlinarith

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, "there is a second steady state, this time at zero real balances":
the map of Figure 2.5 tends to `0` as `m → 0⁺`. -/
theorem sepMap_tendsto_zero {β μ c : ℝ} {vp : ℝ → ℝ} (hanti : AntitoneOn vp (Set.Ioi 0))
    (hgap : ∀ m, 0 < m → vp m < c) : Tendsto (sepMap β μ c vp) (𝓝[>] 0) (𝓝 0) := by
  have := ((sepF_tendsto_zero hanti hgap).const_mul (μ / β)).div_const c
  rw [mul_zero, zero_div] at this
  exact this

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130: the steady states of (4.8) are the `m > 0` with
`v'(m)/c = 1 − β/μ̄`, i.e. `U_m/U_c = Δ` at `1 + i = μ̄/β`, so `m* = L[ȳ, (μ̄ − β)/β]`. -/
theorem sepMap_fixed_iff {β μ c m : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ) (hc : 0 < c)
    (hm : 0 < m) : sepMap β μ c vp m = m ↔ vp m = c * (1 - β / μ) := by
  unfold sepMap sepF
  rw [div_eq_iff hc.ne']
  constructor
  · intro h
    field_simp at h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130 and fn. 38: if `v'` is continuous on `(0, ∞)` and takes values on
both sides of `c(1 − β/μ̄)`, the steady state `m* > 0` exists. -/
theorem sep_exists_steady_state {β μ c a b : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hcont : ContinuousOn vp (Set.Ioi 0)) (ha : 0 < a) (hab : a ≤ b)
    (hva : c * (1 - β / μ) ≤ vp a) (hvb : vp b ≤ c * (1 - β / μ)) :
    ∃ ms, a ≤ ms ∧ ms ≤ b ∧ sepMap β μ c vp ms = ms := by
  obtain ⟨ms, hms, hv⟩ := intermediate_value_Icc' hab
    (hcont.mono fun z hz => (by linarith [hz.1] : (0 : ℝ) < z)) ⟨hvb, hva⟩
  exact ⟨ms, hms.1, hms.2, (sepMap_fixed_iff hβ hμ hc (by linarith [hms.1])).mpr hv⟩

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, "at this point the curve necessarily cuts the diagonal from below"
(single crossing, without any convexity): if `v'` is nonincreasing and `m*` is the only
`m > 0` with `v'(m) = v'(m*)` (e.g. `v'` strictly decreasing), then the map is below the
diagonal on `(0, m*)` and above it on `(m*, ∞)`. -/
theorem sep_single_crossing {β μ c ms : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ) (hc : 0 < c)
    (hanti : AntitoneOn vp (Set.Ioi 0)) (hms : 0 < ms) (hfix : sepMap β μ c vp ms = ms)
    (huniq : ∀ m, 0 < m → vp m = vp ms → m = ms) :
    (∀ m, 0 < m → m < ms → sepMap β μ c vp m < m) ∧
      (∀ m, ms < m → m < sepMap β μ c vp m) := by
  have hv := (sepMap_fixed_iff hβ hμ hc hms).mp hfix
  have key : ∀ m, 0 < m →
      sepMap β μ c vp m - m = m * (c * (1 - β / μ) - vp m) * μ / (β * c) := by
    intro m _
    unfold sepMap sepF
    field_simp
    ring
  have hpos : ∀ m, 0 < m → 0 < m * μ / (β * c) := fun m hm => by positivity
  constructor
  · intro m hm hlt
    have h1 : vp ms ≤ vp m := hanti hm hms hlt.le
    have h2 : vp m ≠ vp ms := fun h => by linarith [huniq m hm h]
    have h3 : c * (1 - β / μ) - vp m < 0 := by
      rw [← hv]; exact sub_neg.mpr (lt_of_le_of_ne h1 h2.symm)
    have := key m hm
    have h4 : m * (c * (1 - β / μ) - vp m) * μ / (β * c) =
        (m * μ / (β * c)) * (c * (1 - β / μ) - vp m) := by ring
    rw [h4] at this
    nlinarith [hpos m hm]
  · intro m hlt
    have hm : 0 < m := by linarith
    have h1 : vp m ≤ vp ms := hanti hms hm hlt.le
    have h2 : vp m ≠ vp ms := fun h => by linarith [huniq m hm h]
    have h3 : 0 < c * (1 - β / μ) - vp m := by
      rw [← hv]; exact sub_pos.mpr (lt_of_le_of_ne h1 h2)
    have := key m hm
    have h4 : m * (c * (1 - β / μ) - vp m) * μ / (β * c) =
        (m * μ / (β * c)) * (c * (1 - β / μ) - vp m) := by ring
    rw [h4] at this
    nlinarith [hpos m hm]

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.8), p. 130: a perfect-foresight path of real balances in the separable
case: positive with `c m_{t+1} = (μ̄/β)F(m_t)` at all dates. -/
def IsSepPath (β μ c : ℝ) (vp : ℝ → ℝ) (m : ℕ → ℝ) : Prop :=
  (∀ t, 0 < m t) ∧ ∀ t, c * m (t + 1) = μ / β * sepF c vp (m t)

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, "a distinct perfect-foresight equilibrium corresponding to each
possible value of `m₀`": from every `m₀ > 0` the orbit of the map is a path, and a path is the
orbit of its initial value. -/
theorem sep_path_exists_unique {β μ c : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ) (hc : 0 < c)
    (hgap : ∀ m, 0 < m → vp m < c) {m0 : ℝ} (hm0 : 0 < m0) :
    IsSepPath β μ c vp (fun t => (sepMap β μ c vp)^[t] m0) ∧
      ∀ m : ℕ → ℝ, IsSepPath β μ c vp m → m 0 = m0 → m = fun t => (sepMap β μ c vp)^[t] m0 := by
  have hsucc : ∀ t, (sepMap β μ c vp)^[t + 1] m0 = sepMap β μ c vp ((sepMap β μ c vp)^[t] m0) :=
    fun t => Function.iterate_succ_apply' _ _ _
  have hpos : ∀ t, 0 < (sepMap β μ c vp)^[t] m0 := by
    intro t
    induction t with
    | zero => exact hm0
    | succ n ih =>
      rw [hsucc]
      have := sepF_pos (c := c) (vp := vp) (by linarith [hgap _ ih]) ih
      unfold sepMap
      positivity
  refine ⟨⟨hpos, fun t => (eq48_sep_iff hc).mpr (hsucc t)⟩, fun m hm h0 => funext fun t => ?_⟩
  induction t with
  | zero => exact h0
  | succ n ih => rw [(eq48_sep_iff hc).mp (hm.2 n), ih, hsucc]

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, "if `m₀ < m*`, real balances must be expected to decrease over
time …, converging to zero asymptotically. This corresponds to a self-fulfilling inflation":
strictly decreasing, tending to `0`. -/
theorem sep_inflation_path {β μ c ms : ℝ} {vp : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hanti : AntitoneOn vp (Set.Ioi 0)) (hcont : ContinuousOn vp (Set.Ioi 0))
    (hms : 0 < ms) (hfix : sepMap β μ c vp ms = ms)
    (huniq : ∀ m, 0 < m → vp m = vp ms → m = ms) (hpath : IsSepPath β μ c vp m)
    (h0 : m 0 < ms) : StrictAnti m ∧ Tendsto m atTop (𝓝 0) := by
  have hsc := (sep_single_crossing hβ hμ hc hanti hms hfix huniq).1
  have hrec : ∀ t, m (t + 1) = sepMap β μ c vp (m t) := fun t => (eq48_sep_iff hc).mp (hpath.2 t)
  have hstep : ∀ t, m t < ms ∧ m (t + 1) < m t := by
    intro t
    induction t with
    | zero => exact ⟨h0, by rw [hrec]; exact hsc _ (hpath.1 0) h0⟩
    | succ n ih =>
      have h1 : m (n + 1) < ms := by linarith [ih.1, ih.2]
      exact ⟨h1, by rw [hrec (n + 1)]; exact hsc _ (hpath.1 _) h1⟩
  have hsa : StrictAnti m := strictAnti_nat_of_succ_lt fun t => (hstep t).2
  refine ⟨hsa, ?_⟩
  rcases antitone_orbit_atBot_or_fixed hrec hsa.antitone with h | ⟨L, hL, hbd, hfixL⟩
  · exfalso
    obtain ⟨t, ht⟩ := (h.eventually (eventually_le_atBot (0 : ℝ))).exists
    linarith [hpath.1 t]
  · have hL0 : 0 ≤ L := ge_of_tendsto hL (Eventually.of_forall fun t => (hpath.1 t).le)
    rcases hL0.lt_or_eq with hLpos | hL0
    · exfalso
      have hcL : ContinuousAt (sepMap β μ c vp) L := by
        have : ContinuousAt vp L := hcont.continuousAt (Ioi_mem_nhds hLpos)
        unfold sepMap sepF
        exact ((continuousAt_const.mul ((continuousAt_const.sub this).mul continuousAt_id))).div
          continuousAt_const hc.ne'
      have hf := hfixL hcL
      have hLms : L < ms := lt_of_le_of_lt (hbd 0) h0
      have := hsc L hLpos hLms
      linarith
    · rw [← hL0] at hL; exact hL

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 131, "if instead `m₀ > m*`, real balances must increase over time,
eventually increasing without bound" (the self-fulfilling deflation of monetary targeting). -/
theorem sep_deflation_path {β μ c ms : ℝ} {vp : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hanti : AntitoneOn vp (Set.Ioi 0)) (hcont : ContinuousOn vp (Set.Ioi 0))
    (hms : 0 < ms) (hfix : sepMap β μ c vp ms = ms)
    (huniq : ∀ m, 0 < m → vp m = vp ms → m = ms) (hpath : IsSepPath β μ c vp m)
    (h0 : ms < m 0) : StrictMono m ∧ Tendsto m atTop atTop := by
  have hsc := (sep_single_crossing hβ hμ hc hanti hms hfix huniq).2
  have hrec : ∀ t, m (t + 1) = sepMap β μ c vp (m t) := fun t => (eq48_sep_iff hc).mp (hpath.2 t)
  have hstep : ∀ t, ms < m t ∧ m t < m (t + 1) := by
    intro t
    induction t with
    | zero => exact ⟨h0, by rw [hrec]; exact hsc _ h0⟩
    | succ n ih =>
      have h1 : ms < m (n + 1) := by linarith [ih.1, ih.2]
      exact ⟨h1, by rw [hrec (n + 1)]; exact hsc _ h1⟩
  have hsm : StrictMono m := strictMono_nat_of_lt_succ fun t => (hstep t).2
  refine ⟨hsm, ?_⟩
  rcases monotone_orbit_atTop_or_fixed hrec hsm.monotone with h | ⟨L, _, hbd, hfixL⟩
  · exact h
  · exfalso
    have hLpos : 0 < L := by linarith [hbd 0]
    have hcL : ContinuousAt (sepMap β μ c vp) L := by
      have : ContinuousAt vp L := hcont.continuousAt (Ioi_mem_nhds hLpos)
      unfold sepMap sepF
      exact ((continuousAt_const.mul ((continuousAt_const.sub this).mul continuousAt_id))).div
        continuousAt_const hc.ne'
    have hf := hfixL hcL
    have := hsc L (by linarith [hbd 0])
    linarith


/-! ## (4.9): satiation and the transversality condition under monetary targeting -/

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.8), p. 129, general (possibly nonseparable) utility: a perfect-foresight
path of real balances, positive with `G(m_{t+1}) = (μ̄/β)F(m_t)`. -/
def IsPath48 (β μ : ℝ) (Uc Um : ℝ → ℝ) (m : ℕ → ℝ) : Prop :=
  (∀ t, 0 < m t) ∧ ∀ t, Gfun Uc (m (t + 1)) = μ / β * Ffun Uc Um (m t)

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), pp. 131–132: satiation at `m̄`: for `m ≥ m̄`, `U_m = 0` and `U_c` is constant
(`F = G` there). -/
def Satiation (Uc Um : ℝ → ℝ) (msat : ℝ) : Prop := ∀ m, msat ≤ m → Um m = 0 ∧ Uc m = Uc msat

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 131, "(4.8) requires that `m_{t+1} = μ̄/β m_t` each period, after real
balances exceed the satiation level": with `G` strictly increasing, `μ̄ ≥ β` and satiation at
`m̄`, a path that reaches `m̄` at `t₀` satisfies `m_{t₀+n} = (μ̄/β)ⁿ m_{t₀} ≥ m̄` for all `n`. -/
theorem satiated_path {β μ msat : ℝ} {Uc Um : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμβ : β ≤ μ)
    (hsat : Satiation Uc Um msat) (hUc : 0 < Uc msat) (hmsat : 0 < msat)
    (hG : StrictMonoOn (Gfun Uc) (Set.Ioi 0)) (hpath : IsPath48 β μ Uc Um m) {t0 : ℕ}
    (ht0 : msat ≤ m t0) : ∀ n, msat ≤ m (t0 + n) ∧ m (t0 + n) = (μ / β) ^ n * m t0 := by
  intro n
  induction n with
  | zero => simp [ht0]
  | succ n ih =>
    have hs := hsat _ ih.1
    have heq := hpath.2 (t0 + n)
    unfold Gfun Ffun at heq
    rw [hs.1, hs.2, sub_zero] at heq
    have hratio : 1 ≤ μ / β := (one_le_div hβ).mpr hμβ
    have hge : msat ≤ m (t0 + n + 1) := by
      by_contra hcon
      push Not at hcon
      have h1 : Gfun Uc (m (t0 + n + 1)) < Gfun Uc msat :=
        hG (hpath.1 _) (Set.mem_Ioi.mpr hmsat) hcon
      unfold Gfun at h1
      rw [heq] at h1
      have h2 : Uc msat * msat ≤ Uc msat * m (t0 + n) := mul_le_mul_of_nonneg_left ih.1 hUc.le
      have h3 : Uc msat * m (t0 + n) ≤ μ / β * (Uc msat * m (t0 + n)) :=
        le_mul_of_one_le_left (by nlinarith [hpath.1 (t0 + n)]) hratio
      linarith
    have hs1 := hsat _ hge
    rw [hs1.2] at heq
    have hm1 : m (t0 + n + 1) = μ / β * m (t0 + n) :=
      mul_left_cancel₀ hUc.ne' (by rw [heq]; ring)
    refine ⟨by rw [← add_assoc]; exact hge, ?_⟩
    rw [← add_assoc, hm1, ih.2, pow_succ]
    ring

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.9), p. 132, "the transversality condition is violated in the case of
any such path": with `0 < β`, `μ̄ ≥ 1`, satiation at `m̄ > 0`, `G` strictly increasing and a path
reaching `m̄`, `β^T U_c(m_T)m_T = β^{t₀}μ̄^{T−t₀}U_c m_{t₀} ≥ β^{t₀}U_c m_{t₀} > 0` for `T ≥ t₀`, so
`β^T U_c(m_T) m_T` does not tend to `0`. -/
theorem money_tvc_violated {β μ msat : ℝ} {Uc Um : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hμ : 1 ≤ μ) (hsat : Satiation Uc Um msat) (hUc : 0 < Uc msat)
    (hmsat : 0 < msat) (hG : StrictMonoOn (Gfun Uc) (Set.Ioi 0)) (hpath : IsPath48 β μ Uc Um m)
    {t0 : ℕ} (ht0 : msat ≤ m t0) :
    (∀ n, β ^ (t0 + n) * Uc (m (t0 + n)) * m (t0 + n) =
        β ^ t0 * μ ^ n * Uc (m t0) * m t0) ∧
      ¬ Tendsto (fun T => β ^ T * Uc (m T) * m T) atTop (𝓝 0) := by
  have hsp := satiated_path hβ (by linarith) hsat hUc hmsat hG hpath ht0
  have hval : ∀ n, β ^ (t0 + n) * Uc (m (t0 + n)) * m (t0 + n) =
      β ^ t0 * μ ^ n * Uc (m t0) * m t0 := by
    intro n
    rw [(hsat _ (hsp n).1).2, (hsat _ ht0).2, (hsp n).2, pow_add, div_pow]
    field_simp
  refine ⟨hval, fun h => ?_⟩
  have hpos : 0 < β ^ t0 * Uc (m t0) * m t0 := by
    rw [(hsat _ ht0).2]; have := hpath.1 t0; positivity
  have hev : ∀ᶠ T in atTop, β ^ t0 * Uc (m t0) * m t0 ≤ β ^ T * Uc (m T) * m T := by
    filter_upwards [eventually_ge_atTop t0] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    rw [hval n]
    have h1 : 1 ≤ μ ^ n := one_le_pow₀ hμ
    have : β ^ t0 * Uc (m t0) * m t0 * 1 ≤ β ^ t0 * Uc (m t0) * m t0 * μ ^ n :=
      mul_le_mul_of_nonneg_left h1 hpos.le
    linarith
  have := ge_of_tendsto h hev
  linarith

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), pp. 131–132, combined: in the separable model with satiation at `m̄`
(`v' = 0` on `[m̄, ∞)`) and `μ̄ ≥ 1`, every deflationary path (`m₀ > m*`) violates the
transversality condition (4.9), so it is not an equilibrium. -/
theorem sep_deflation_violates_tvc {β μ c ms msat : ℝ} {vp : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hμ : 1 ≤ μ) (hc : 0 < c) (hanti : AntitoneOn vp (Set.Ioi 0))
    (hcont : ContinuousOn vp (Set.Ioi 0)) (hms : 0 < ms) (hfix : sepMap β μ c vp ms = ms)
    (huniq : ∀ m, 0 < m → vp m = vp ms → m = ms) (hmsat : 0 < msat)
    (hsat : ∀ m, msat ≤ m → vp m = 0) (hpath : IsSepPath β μ c vp m) (h0 : ms < m 0) :
    ¬ Tendsto (fun T => β ^ T * (fun _ : ℝ => c) (m T) * m T) atTop (𝓝 0) := by
  have hdef := sep_deflation_path hβ (by linarith) hc hanti hcont hms hfix huniq hpath h0
  obtain ⟨t0, ht0⟩ := (hdef.2.eventually (eventually_ge_atTop msat)).exists
  refine (money_tvc_violated (Uc := fun _ => c) (Um := vp) hβ hβ1 hμ
    (fun m hm => ⟨hsat m hm, rfl⟩) hc hmsat
    (fun a _ b _ hab => by unfold Gfun; nlinarith) ⟨hpath.1, fun t => ?_⟩ ht0).2
  have := hpath.2 t
  unfold Gfun Ffun
  unfold sepF at this
  linarith

/-- Cochrane (2023), §19.3, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 133, "under the monetary targeting regime … the previous argument …
fails when `μ̄ < 1`. In this case, the transversality condition is satisfied by all of the
solutions to (4.8) that involve inflation rates eventually falling to the level `Π_t = β`, and
so a continuum of perfect-foresight equilibria … exists": with satiation at `m̄ > 0`, `U_c` constant
above `m̄` and `β < μ̄ < 1`, each `m₀ ≥ m̄` starts the path `m_t = (μ̄/β)^t m₀` of (4.8), distinct
for distinct `m₀`; along it inflation `μ̄m_t/m_{t+1}` equals `β`, the transversality condition
holds and the bound (3.4) converges. -/
theorem money_contraction_continuum {β μ msat ybar : ℝ} {Uc Um : ℝ → ℝ} (hβ : 0 < β)
    (hβμ : β < μ) (hμ1 : μ < 1) (hsat : Satiation Uc Um msat) {m0 : ℝ} (hm0 : msat ≤ m0)
    (hmsat : 0 < msat) :
    IsPath48 β μ Uc Um (fun t => (μ / β) ^ t * m0) ∧
      (∀ t, μ * ((μ / β) ^ t * m0) / ((μ / β) ^ (t + 1) * m0) = β) ∧
      Tendsto (fun T => β ^ T * Uc ((μ / β) ^ T * m0) * ((μ / β) ^ T * m0)) atTop (𝓝 0) ∧
      Summable (fun T => β ^ T * (Uc ((μ / β) ^ T * m0) * ybar +
        Um ((μ / β) ^ T * m0) * ((μ / β) ^ T * m0))) := by
  have hm0pos : 0 < m0 := by linarith
  have hr : 1 ≤ μ / β := (one_le_div hβ).mpr hβμ.le
  have hge : ∀ t, msat ≤ (μ / β) ^ t * m0 := fun t =>
    le_trans hm0 (le_mul_of_one_le_left hm0pos.le (one_le_pow₀ hr))
  have hμ0 : 0 < μ := by linarith
  refine ⟨⟨fun t => by positivity, fun t => ?_⟩, fun t => ?_, ?_, ?_⟩
  · unfold Gfun Ffun
    rw [(hsat _ (hge t)).1, (hsat _ (hge (t + 1))).2, (hsat _ (hge t)).2]
    simp only [pow_succ]
    ring
  · rw [pow_succ]
    field_simp
  · have hcongr : (fun T => β ^ T * Uc ((μ / β) ^ T * m0) * ((μ / β) ^ T * m0)) =
        fun T => μ ^ T * (Uc msat * m0) := by
      funext T
      rw [(hsat _ (hge T)).2, div_pow]
      field_simp
    rw [hcongr]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hμ0.le hμ1).mul_const (Uc msat * m0)
  · have hcongr : (fun T => β ^ T * (Uc ((μ / β) ^ T * m0) * ybar +
        Um ((μ / β) ^ T * m0) * ((μ / β) ^ T * m0))) = fun T => β ^ T * (Uc msat * ybar) := by
      funext T
      rw [(hsat _ (hge T)).1, (hsat _ (hge T)).2]
      ring
    rw [hcongr]
    exact (summable_geometric_of_lt_one hβ.le (by linarith)).mul_right _


/-! ## Cochrane's (19.18) is the separable map -/

/-- Cochrane (2023), eq. (19.18), p. 442: with money growth `M_{t+1} = (1 + µ)M_t`, a path of
(19.18) is exactly a path of the separable map with `μ̄ = 1 + µ`, `c = u_c(y)`, `v' = u_m`. -/
theorem miuPath_iff_sepPath {β ucy μg : ℝ} {um : ℝ → ℝ} {M m : ℕ → ℝ} (hβ : 0 < β)
    (hucy : 0 < ucy) (hM : ∀ t, 0 < M t) (hg : ∀ t, M (t + 1) = μg * M t) :
    MoneyInUtility.IsMIUPath β ucy um M m ↔ IsSepPath β μg ucy um m := by
  have hμ : μg ≠ 0 := by
    intro h
    have := hg 0
    rw [h, zero_mul] at this
    exact (hM 1).ne' this
  constructor
  · intro h
    refine ⟨fun t => (h t).1, fun t => ?_⟩
    have h1 := (h t).2
    have hm := (h t).1
    have hMt := hM t
    rw [hg t] at h1
    unfold sepF
    have e : um (m t) = ucy * (1 - β * (m (t + 1) / m t) * (M t / (μg * M t))) := by
      field_simp at h1 ⊢
      linarith
    rw [e]
    field_simp
    ring
  · intro h t
    refine ⟨h.1 t, ?_⟩
    have h1 := h.2 t
    have hm := h.1 t
    have hMt := hM t
    rw [hg t]
    unfold sepF at h1
    field_simp
    field_simp at h1
    linarith

/-! ## The power example (19.23) and Figure 19.1 -/

/-- Cochrane (2023), eq. (19.23), p. 444: `x̄` is a fixed point of (19.23) when
`1 − θx̄^γ ≠ 0`. -/
theorem nextX_fixed {θ γ xb : ℝ} (hK : 1 - θ * xb ^ γ ≠ 0) : nextX θ γ xb xb = xb := by
  unfold nextX
  field_simp

/-- Cochrane (2023), eq. (19.23), p. 444: the map sends positive `x` with `θx^γ < 1` (the
domain where `u_m/u_c < 1`) to a positive value. -/
theorem nextX_pos {θ γ xb x : ℝ} (hK : 0 < 1 - θ * xb ^ γ) (hx : 0 < x) (hd : θ * x ^ γ < 1) :
    0 < nextX θ γ xb x := by
  unfold nextX
  exact div_pos (mul_pos hx hK) (by linarith)

/-- Cochrane (2023), Figure 19.1, p. 444 (single crossing): on the domain `θx^γ < 1`, (19.23)
lies below the diagonal exactly for `x < x̄` and above it exactly for `x > x̄`. -/
theorem nextX_lt_iff {θ γ xb x : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hxb : 0 < xb)
    (hx : 0 < x) (hd : θ * x ^ γ < 1) :
    (nextX θ γ xb x < x ↔ x < xb) ∧ (x < nextX θ γ xb x ↔ xb < x) := by
  have hD : 0 < 1 - θ * x ^ γ := by linarith
  have k1 : nextX θ γ xb x < x ↔ θ * x ^ γ < θ * xb ^ γ := by
    unfold nextX
    rw [div_lt_iff₀ hD]
    constructor <;> intro h <;> nlinarith
  have k2 : x < nextX θ γ xb x ↔ θ * xb ^ γ < θ * x ^ γ := by
    unfold nextX
    rw [lt_div_iff₀ hD]
    constructor <;> intro h <;> nlinarith
  have k3 : ∀ a b : ℝ, 0 < a → 0 < b → (θ * a ^ γ < θ * b ^ γ ↔ a < b) := fun a b ha hb =>
    ⟨fun h => (Real.rpow_lt_rpow_iff ha.le hb.le hγ).mp (lt_of_mul_lt_mul_left h hθ.le),
      fun h => mul_lt_mul_of_pos_left ((Real.rpow_lt_rpow_iff ha.le hb.le hγ).mpr h) hθ⟩
  exact ⟨k1.trans (k3 x xb hx hxb), k2.trans (k3 xb x hxb hx)⟩

/-- Cochrane (2023), p. 444 ("Therefore, `Py/M` is an unstable unique locally bounded
equilibrium"): for `θ, γ > 0`, `x̄ > 0`, `0 < 1 − θx̄^γ`, the steady state of (19.23) is
repelling: there is `δ > 0` such that every other path eventually lies at least `δ` away. -/
theorem power_steady_repelling {θ γ xb : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hxb : 0 < xb)
    (hK : 0 < 1 - θ * xb ^ γ) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = nextX θ γ xb (x t)) → x 0 ≠ xb →
      ∃ t, δ ≤ |x t - xb| := by
  have hs := slope_gt_one hθ hγ hxb hK
  exact repelling_of_one_lt_abs_deriv (nextX_fixed hK.ne') (nextX_hasDerivAt hxb hK.ne')
    (by rw [abs_of_pos (by linarith)]; exact hs)

/-- Cochrane (2023), Figure 19.1, p. 444: with `δ = µ = 0.2`, `γ = 2`, `θ = 0.01` the
inflationary steady state `x̄ ≈ 5.53` is repelling. -/
theorem fig191_repelling :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = nextX (1 / 100) 2 xbar191 (x t)) →
      x 0 ≠ xbar191 → ∃ t, δ ≤ |x t - xbar191| := by
  have hpos : 0 < xbar191 := Real.sqrt_pos.mpr (by norm_num)
  have hs := fig191_steady.2
  exact power_steady_repelling (by norm_num) (by norm_num) hpos (by rw [hs]; norm_num)

/-- Cochrane (2023), p. 444 ("The figure shows the second steady state at `P_ty/M_t = 0` …
This steady state is stable; multiple equilibria in this neighborhood stay nearby"): every
path of (19.23) started at `0 < x_0 < x̄` is strictly decreasing, stays positive, converges to
`0`, and `x_{t+1}/x_t → 1 − θx̄^γ` (`= β/(1 + µ)`). -/
theorem power_deflation_orbit {θ γ xb : ℝ} {x : ℕ → ℝ} (hθ : 0 < θ) (hγ : 0 < γ)
    (hxb : 0 < xb) (hK : 0 < 1 - θ * xb ^ γ) (hrec : ∀ t, x (t + 1) = nextX θ γ xb (x t))
    (h0 : 0 < x 0) (h0' : x 0 < xb) :
    StrictAnti x ∧ (∀ t, 0 < x t) ∧ Tendsto x atTop (𝓝 0) ∧
      Tendsto (fun t => x (t + 1) / x t) atTop (𝓝 (1 - θ * xb ^ γ)) := by
  have hdom : ∀ z, 0 < z → z < xb → θ * z ^ γ < 1 := fun z hz hzb => by
    have := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hz.le hzb hγ) hθ
    linarith
  have hinv : ∀ t, 0 < x t ∧ x t < xb ∧ x (t + 1) < x t := by
    intro t
    induction t with
    | zero =>
      refine ⟨h0, h0', ?_⟩
      rw [hrec 0]
      exact ((nextX_lt_iff hθ hγ hxb h0 (hdom _ h0 h0')).1).mpr h0'
    | succ n ih =>
      have hp : 0 < x (n + 1) := by
        rw [hrec n]; exact nextX_pos hK ih.1 (hdom _ ih.1 ih.2.1)
      have hl : x (n + 1) < xb := lt_trans ih.2.2 ih.2.1
      refine ⟨hp, hl, ?_⟩
      rw [hrec (n + 1)]
      exact ((nextX_lt_iff hθ hγ hxb hp (hdom _ hp hl)).1).mpr hl
  have hsa : StrictAnti x := strictAnti_nat_of_succ_lt fun t => (hinv t).2.2
  have hlim : Tendsto x atTop (𝓝 0) := by
    rcases antitone_orbit_atBot_or_fixed hrec hsa.antitone with h | ⟨L, hL, hbd, hfixL⟩
    · exfalso
      obtain ⟨t, ht⟩ := (h.eventually (eventually_le_atBot (0 : ℝ))).exists
      linarith [(hinv t).1]
    · have hL0 : 0 ≤ L := ge_of_tendsto hL (Eventually.of_forall fun t => (hinv t).1.le)
      rcases hL0.lt_or_eq with hLpos | hL0
      · exfalso
        have hLxb : L < xb := lt_of_le_of_lt (hbd 0) h0'
        have hdL := hdom L hLpos hLxb
        have hcL : ContinuousAt (nextX θ γ xb) L := by
          have hc : ContinuousAt (fun z : ℝ => z ^ γ) L :=
            Real.continuousAt_rpow_const L γ (Or.inl hLpos.ne')
          unfold nextX
          exact (continuousAt_id.mul continuousAt_const).div
            (continuousAt_const.sub (continuousAt_const.mul hc)) (by linarith)
        have hf := hfixL hcL
        have := ((nextX_lt_iff hθ hγ hxb hLpos hdL).1).mpr hLxb
        linarith
      · rw [← hL0] at hL; exact hL
  refine ⟨hsa, fun t => (hinv t).1, hlim, ?_⟩
  have hratio : ∀ t, x (t + 1) / x t = (1 - θ * xb ^ γ) / (1 - θ * x t ^ γ) := by
    intro t
    have hxt := (hinv t).1
    rw [hrec t]
    unfold nextX
    field_simp
  have hc0 : Tendsto (fun t => x t ^ γ) atTop (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto.comp hlim
    rwa [Real.zero_rpow hγ.ne'] at hc
  have hden : Tendsto (fun t => 1 - θ * x t ^ γ) atTop (𝓝 (1 - θ * 0)) :=
    (hc0.const_mul θ).const_sub 1
  rw [mul_zero, sub_zero] at hden
  have h2 := (tendsto_const_nhds (x := 1 - θ * xb ^ γ)).div hden one_ne_zero
  rw [div_one] at h2
  exact h2.congr fun t => (hratio t).symm

/-- Cochrane (2023), p. 444 (`lim P_{t+1}/P_t = 1/(1 + δ)`): along such a path, gross inflation
`P_{t+1}/P_t = (1 + µ)x_{t+1}/x_t` tends to `β` when `θx̄^γ = 1 − β/(1 + µ)`. -/
theorem power_deflation_inflation {θ γ xb β μg : ℝ} {x : ℕ → ℝ} (hθ : 0 < θ) (hγ : 0 < γ)
    (hxb : 0 < xb) (hK : 0 < 1 - θ * xb ^ γ) (hμ : μg ≠ 0) (hss : θ * xb ^ γ = 1 - β / μg)
    (hrec : ∀ t, x (t + 1) = nextX θ γ xb (x t)) (h0 : 0 < x 0) (h0' : x 0 < xb) :
    Tendsto (fun t => μg * (x (t + 1) / x t)) atTop (𝓝 β) := by
  have h := ((power_deflation_orbit hθ hγ hxb hK hrec h0 h0').2.2.2).const_mul μg
  have e : μg * (1 - θ * xb ^ γ) = β := by rw [hss]; field_simp; ring
  rwa [e] at h

/-- Cochrane (2023), Figure 19.1, p. 444 (paths to the right of `x̄`; cf. Online Appendix A3):
every path of (19.23) started at `x_0 > x̄` reaches `θx_t^γ ≥ 1` in finite time. There
`u_m/u_c = θx^γ ≥ 1 > i/(1 + i)`, so no such path is an equilibrium. -/
theorem power_inflation_exits {θ γ xb : ℝ} {x : ℕ → ℝ} (hθ : 0 < θ) (hγ : 0 < γ)
    (hxb : 0 < xb) (hK : 0 < 1 - θ * xb ^ γ)
    (hrec : ∀ t, θ * x t ^ γ < 1 → x (t + 1) = nextX θ γ xb (x t)) (h0 : xb < x 0) :
    ∃ t, 1 ≤ θ * x t ^ γ := by
  by_contra hcon
  push Not at hcon
  have hrec' : ∀ t, x (t + 1) = nextX θ γ xb (x t) := fun t => hrec t (hcon t)
  have hinv : ∀ t, xb < x t ∧ x t < x (t + 1) := by
    intro t
    induction t with
    | zero =>
      refine ⟨h0, ?_⟩
      rw [hrec' 0]
      exact ((nextX_lt_iff hθ hγ hxb (by linarith) (hcon 0)).2).mpr h0
    | succ n ih =>
      have hl : xb < x (n + 1) := lt_trans ih.1 ih.2
      refine ⟨hl, ?_⟩
      rw [hrec' (n + 1)]
      exact ((nextX_lt_iff hθ hγ hxb (by linarith) (hcon _)).2).mpr hl
  have hsm : StrictMono x := strictMono_nat_of_lt_succ fun t => (hinv t).2
  rcases monotone_orbit_atTop_or_fixed hrec' hsm.monotone with h | ⟨L, hL, hbd, -⟩
  · have hr : Tendsto (fun t => θ * x t ^ γ) atTop atTop :=
      ((tendsto_rpow_atTop hγ).comp h).const_mul_atTop hθ
    obtain ⟨t, ht⟩ := (hr.eventually (eventually_ge_atTop 1)).exists
    linarith [hcon t]
  · have hLxb : xb < L := lt_of_lt_of_le h0 (hbd 0)
    have hLpos : 0 < L := lt_trans hxb hLxb
    have hid : ∀ t, x (t + 1) * (1 - θ * x t ^ γ) = x t * (1 - θ * xb ^ γ) := by
      intro t
      have hD : 1 - θ * x t ^ γ ≠ 0 := by linarith [hcon t]
      rw [hrec' t]
      unfold nextX
      field_simp
    have hc : Tendsto (fun t => x t ^ γ) atTop (𝓝 (L ^ γ)) :=
      (Real.continuousAt_rpow_const L γ (Or.inl hLpos.ne')).tendsto.comp hL
    have h1 : Tendsto (fun t => x (t + 1) * (1 - θ * x t ^ γ)) atTop
        (𝓝 (L * (1 - θ * L ^ γ))) :=
      ((tendsto_add_atTop_iff_nat 1).mpr hL).mul ((hc.const_mul θ).const_sub 1)
    have h2 : Tendsto (fun t => x t * (1 - θ * xb ^ γ)) atTop (𝓝 (L * (1 - θ * xb ^ γ))) :=
      hL.mul_const _
    have heq : L * (1 - θ * L ^ γ) = L * (1 - θ * xb ^ γ) :=
      tendsto_nhds_unique (h1.congr hid) h2
    have heq2 : θ * L ^ γ = θ * xb ^ γ := by
      have := mul_left_cancel₀ hLpos.ne' heq
      linarith
    have := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hxb.le hLxb hγ) hθ
    linarith

/-- Cochrane (2023), pp. 444–445, survey error E13 (global form): if `1 − θx̄^γ = β/(1 + µ) ≥ 1`,
i.e. `1 + µ ≤ β`, no path of (19.23) staying in the domain `0 < x`, `θx^γ < 1` converges to the
deflationary steady state `x = 0`. With `power_deflation_orbit` (`1 + µ > β`), the zero-rate
steady state attracts iff `1 + µ > β`, not `1 + µ > 1/β` as printed. -/
theorem e13_no_deflation_attractor {θ γ xb : ℝ} {x : ℕ → ℝ} (hθ : 0 < θ)
    (hK1 : 1 ≤ 1 - θ * xb ^ γ) (hrec : ∀ t, x (t + 1) = nextX θ γ xb (x t))
    (hdom : ∀ t, 0 < x t ∧ θ * x t ^ γ < 1) : ¬ Tendsto x atTop (𝓝 0) := by
  have hstep : ∀ t, x t < x (t + 1) := by
    intro t
    have hx := (hdom t).1
    have hd := (hdom t).2
    have hpos : 0 < θ * x t ^ γ := mul_pos hθ (Real.rpow_pos_of_pos hx γ)
    rw [hrec t]
    unfold nextX
    rw [lt_div_iff₀ (by linarith)]
    nlinarith
  have hsm : StrictMono x := strictMono_nat_of_lt_succ hstep
  intro h
  have hge : ∀ t, x 0 ≤ x t := fun t => hsm.monotone (Nat.zero_le t)
  have := ge_of_tendsto h (Eventually.of_forall hge)
  linarith [(hdom 0).1]

end Cochrane.Monetarism.MoneyTargetingDynamics
