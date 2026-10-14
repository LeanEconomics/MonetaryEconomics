/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Global multiplicity despite local determinacy

Woodford (2003), *Interest and Prices*, Chapter 2, §4.1, pp. 123–131 (with the
one-dimensional dynamics lemma L5 of the chapter survey). Everything here is
perfect foresight: plain real sequences.

* **L5 (monotone one-dimensional maps).** `orbit_monotone_of_le`,
  `orbit_antitone_of_ge`: orbits of a map monotone on an invariant set are monotone;
  `monotone_orbit_atTop_or_fixed`, `antitone_orbit_atBot_or_fixed`: a monotone orbit
  diverges or converges, and its limit is a fixed point wherever the map is continuous;
  `repelling_of_one_lt_abs_deriv`: slope of modulus > 1 at a fixed point makes it
  repelling; `attracting_of_abs_deriv_lt_one`: slope of modulus < 1 makes it attracting.
* **(4.2), p. 124.** The fiscal rule `T = αW − ΔM` gives `Q_{t,t+1}W_{t+1} = (1−α)W_t`
  (`ricardian_step`), hence `Q_{t,T}W_T = (1−α)^{T−t}W_t → 0` (`ricardian_tvc`) for
  `0 < α ≤ 1`; for `α = 0` the TVC can fail (`ricardian_tvc_fails_of_alpha_zero`).
* **(4.5)–(4.6), p. 125.** `eq45_iff_fisher` derives (4.5) from the Fisher equation (4.3);
  `isPath45_iff_isPath46_of_const` gives (4.6) when `λ` is constant.
* **p. 125, fn. 58.** Every initial inflation rate starts a solution of (4.6)
  (`orbit46_isPath`), solutions are pinned down by `Π₀` (`isPath46_eq_orbit`), and
  (4.4) holds along any interest path when `λ` and `iL(i)` are bounded
  (`bound44_summable`): a continuum of perfect-foresight equilibria
  (`continuum_pf_equilibria`).
* **p. 125.** The Taylor coefficient at `Π*` is the slope of the map
  (`taylorCoeff_eq_slope`); under the local Taylor principle there is a second steady
  state `Π** ∈ [β, Π*)` at which the Taylor principle fails (`second_steady_state`).
* **p. 126.** Self-fulfilling deflations converge to `β` (`self_fulfilling_deflation46`,
  `deflation46_strictAnti`, `deflation46_eventually_deflation`), and the deflationary
  steady state is locally indeterminate (`deflationary_steady_state_indeterminate`).
* **p. 127, error E6.** "Inflation above target always rises without bound" needs a
  global hypothesis: `inflation_unbounded46` proves it when `φ(Π) > Π/β − 1` above `Π*`,
  `inflation_unbounded_iff` shows that this (no steady state above `Π*`) is exactly what
  is needed, and `e6_counterexample` gives a continuous increasing `φ ≥ 0` satisfying
  the Taylor principle at `Π*` with a bounded path starting above target.
* **p. 127.** Every path other than `Π*` leaves a neighbourhood of `Π*`
  (`target_locally_repelling`).
* **p. 127.** With real-balance effects: `λ` decreasing makes `Π/λ(φ(Π))` strictly
  increasing (`ratio_strictMonoOn`); then (4.5) has the same steady states
  (`steady_state45_iff`), at most one solution per `Π₀` (`isPath45_unique`), a solution for
  every `Π₀ ∈ (β, Π*)` (`deflation45_exists`), each converging to `β`
  (`self_fulfilling_deflation45`) and satisfying (4.4) (`deflation45_bound44`).
* **p. 127, fn. 61, "`λ` not too strongly increasing".** Without monotonicity of `λ`, the same
  holds under (H1) `Π/λ(φ(Π))` strictly increasing and (H2) `λ(i) ≤ (1 + i)λ(0)`
  (`step45_down_gen`, `self_fulfilling_deflation45_gen`, `deflation45_exists_gen`;
  `antitone_lam_gives_gen` shows the `u_cm > 0` case is included), and
  `deflation45_counterexample` shows a restriction is needed (`λ(i) = 1 + i`: a path starting
  in `(β, Π*)` jumps to `Π*`).
* **pp. 127–128, (4.4) along self-fulfilling deflations of (4.5)**, with no bound on `λ`
  assumed: `deflation45_bound44_gen` (via `bound44_summable_path`); boundedness of `λ` along the
  path is derived from continuity on the compact range `[0, φ(Π₀)]` of interest rates.
-/

namespace Woodford.PriceLevelDetermination.GlobalDynamics

open Filter Topology

/-! ## L5: one-dimensional monotone maps -/

/-- Survey lemma L5 (used in Woodford (2003), §4.1–4.3, pp. 123–138): if `g` is monotone on an
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

/-- Survey lemma L5 (Woodford (2003), §4.1–4.3): if `g` is monotone on an invariant set `S` and
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

/-- Survey lemma L5 (Woodford (2003), §4.1): a limit of an orbit `x_{t+1} = g(x_t)` at which
`g` is continuous is a fixed point of `g`. -/
theorem fixed_of_tendsto {g : ℝ → ℝ} {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = g (x t)) {L : ℝ}
    (hL : Tendsto x atTop (𝓝 L)) (hc : ContinuousAt g L) : g L = L := by
  have h1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 L) := (tendsto_add_atTop_iff_nat 1).mpr hL
  have h2 : Tendsto (fun t => x (t + 1)) atTop (𝓝 (g L)) := by
    have : (fun t => x (t + 1)) = g ∘ x := funext fun t => hx t
    rw [this]
    exact hc.tendsto.comp hL
  exact tendsto_nhds_unique h2 h1

/-- Survey lemma L5 (Woodford (2003), §4.1): a monotone orbit either diverges to `+∞` or
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

/-- Survey lemma L5 (Woodford (2003), §4.1): an antitone orbit either diverges to `−∞` or
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

/-- Survey lemma L5 (Woodford (2003), p. 125): near a point where `f` has a positive derivative,
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

/-- Survey lemma L5, "slope > 1 ⇒ repelling" (Woodford (2003), p. 127): if `g(x*) = x*` and
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

/-- Survey lemma L5 (Woodford (2003), p. 127, "local indeterminacy near `Π**`"): if
`g(x*) = x*` and `|g'(x*)| < 1`, every orbit starting within `δ` of `x*` stays within `δ` and
converges to `x*`. -/
theorem attracting_of_abs_deriv_lt_one {g : ℝ → ℝ} {xs d : ℝ} (hfix : g xs = xs)
    (hd : HasDerivAt g d xs) (h1 : |d| < 1) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = g (x t)) → |x 0 - xs| < δ →
      (∀ t, |x t - xs| < δ) ∧ Tendsto x atTop (𝓝 xs) := by
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
  refine ⟨fun t => (hbd t).2, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => (hbd t).1) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const |x 0 - xs|

/-! ## (4.2): a Ricardian fiscal rule -/

/-- Woodford (2003), eq. (1.8), p. 67: the opportunity cost of money
`Δ_t = (i_t − i^m_t)/(1 + i_t)`; with `i^m = 0` (as in (4.2)) it is `i/(1+i)`. -/
noncomputable def oppCost (i im : ℝ) : ℝ := (i - im) / (1 + i)

/-- Woodford (2003), (4.2), p. 124: with `i^m = 0` the opportunity cost is `i/(1+i)`. -/
theorem oppCost_zero (i : ℝ) : oppCost i 0 = i / (1 + i) := by
  simp [oppCost]

/-- Woodford (2003), §1, p. 66: the perfect-foresight discount factor
`Q_{t,T} = ∏_{s=t}^{T-1} Q_{s,s+1}`. -/
def discount (q : ℕ → ℝ) (t T : ℕ) : ℝ := ∏ s ∈ Finset.Ico t T, q s

/-- Woodford (2003), (4.2), p. 124 with the government flow budget constraint (1.25), p. 73
(the text cites (1.7), error E9): under `T_t = αW_t − Δ_tM_t` the government budget gives
`Q_{t,t+1}W_{t+1} = (1 − α)W_t`. -/
theorem ricardian_step {q W Tx Δ M : ℕ → ℝ} {α : ℝ} (t : ℕ)
    (hgov : q t * W (t + 1) = W t - Tx t - Δ t * M t)
    (hrule : Tx t = α * W t - Δ t * M t) : q t * W (t + 1) = (1 - α) * W t := by
  rw [hgov, hrule]; ring

/-- Woodford (2003), (4.2), p. 124: iterating, `Q_{t,t+n}W_{t+n} = (1 − α)ⁿ W_t`. -/
theorem ricardian_discounted {q W Tx Δ M : ℕ → ℝ} {α : ℝ}
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = α * W s - Δ s * M s) (t n : ℕ) :
    discount q t (t + n) * W (t + n) = (1 - α) ^ n * W t := by
  induction n with
  | zero => simp [discount]
  | succ n ih =>
    have hd : discount q t (t + (n + 1)) = discount q t (t + n) * q (t + n) := by
      simp only [discount, ← add_assoc]
      exact Finset.prod_Ico_succ_top (Nat.le_add_right t n) q
    rw [hd, mul_assoc, ← add_assoc, ricardian_step (t + n) (hgov _) (hrule _), ← mul_assoc,
      mul_comm (discount q t (t + n)), mul_assoc, ih]
    ring

/-- Woodford (2003), (4.2), p. 124, "the transversality condition (1.18) necessarily holds":
for `0 < α ≤ 1`, `Q_{t,T}W_T → 0` as `T → ∞`, whatever the paths of the other variables. -/
theorem ricardian_tvc {q W Tx Δ M : ℕ → ℝ} {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = α * W s - Δ s * M s) (t : ℕ) :
    Tendsto (fun T => discount q t T * W T) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T => (1 - α) ^ (T - t) * W t) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0 : ℝ) ≤ 1 - α)
      (by linarith)).comp (tendsto_sub_atTop_nat t)).mul_const (W t)
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
  rw [ricardian_discounted hgov hrule t n]
  simp

/-- Woodford (2003), (4.2), p. 124: the hypothesis `α > 0` is needed; with `α = 0`,
`Q_{t,T}W_T = W_t` for all `T ≥ t`, so the transversality condition fails whenever `W_t ≠ 0`. -/
theorem ricardian_tvc_fails_of_alpha_zero {q W Tx Δ M : ℕ → ℝ}
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = 0 * W s - Δ s * M s) (t : ℕ) (hW : W t ≠ 0) :
    ¬ Tendsto (fun T => discount q t T * W T) atTop (𝓝 0) := by
  intro h
  have hconst : Tendsto (fun T => discount q t T * W T) atTop (𝓝 (W t)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop t] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    rw [ricardian_discounted hgov hrule t n]
    simp
  exact hW (tendsto_nhds_unique hconst h)

/-! ## (4.3) ⇒ (4.5) ⇒ (4.6) -/

/-- Woodford (2003), (4.3) ⇔ (4.5), pp. 124–125: with constant output and no shocks the
perfect-foresight Fisher equation `1 + i_t = β⁻¹ [λ_{t+1}/λ_t · P_t/P_{t+1}]⁻¹` is equivalent to
`Π_{t+1}/λ_{t+1} = β(1 + i_t)/λ_t`, where `Π_{t+1} = P_{t+1}/P_t`. -/
theorem eq45_iff_fisher {β lt lt1 Pt Pt1 it : ℝ} (hβ : 0 < β) (hl : 0 < lt) (hl1 : 0 < lt1)
    (hP : 0 < Pt) (hP1 : 0 < Pt1) :
    (1 + it = β⁻¹ * ((lt1 / lt) * (Pt / Pt1))⁻¹) ↔ (Pt1 / Pt) / lt1 = β * (1 + it) / lt := by
  have hβ' := hβ.ne'
  have hl' := hl.ne'
  have hl1' := hl1.ne'
  have hP' := hP.ne'
  have hP1' := hP1.ne'
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    have h2 : Pt1 * lt = β * (1 + it) * lt1 * Pt := by
      rw [div_eq_div_iff (by positivity) hl', div_mul_eq_mul_div, div_eq_iff hP'] at h
      linarith
    rw [show β⁻¹ * ((lt1 / lt) * (Pt / Pt1))⁻¹ = lt * Pt1 / (β * lt1 * Pt) by
      field_simp, eq_div_iff (by positivity)]
    linear_combination (-1 : ℝ) * h2

/-- Woodford (2003), eq. (4.5), p. 125: a perfect-foresight inflation path under the rule
`i_t = φ(Π_t)`: positive inflation with
`Π_{t+1}/λ(φ(Π_{t+1})) = β(1 + φ(Π_t))/λ(φ(Π_t))` at all dates. -/
def IsPath45 (β : ℝ) (lam φ : ℝ → ℝ) (Pi_ : ℕ → ℝ) : Prop :=
  (∀ t, 0 < Pi_ t) ∧
    ∀ t, Pi_ (t + 1) / lam (φ (Pi_ (t + 1))) = β * (1 + φ (Pi_ t)) / lam (φ (Pi_ t))

/-- Woodford (2003), eq. (4.6), p. 125: the cashless/separable dynamics
`Π_{t+1} = β(1 + φ(Π_t))` with positive inflation. -/
def IsPath46 (β : ℝ) (φ : ℝ → ℝ) (Pi_ : ℕ → ℝ) : Prop :=
  (∀ t, 0 < Pi_ t) ∧ ∀ t, Pi_ (t + 1) = β * (1 + φ (Pi_ t))

/-- Woodford (2003), (4.3) ⇒ (4.5), pp. 124–125, for whole paths: if `P > 0`,
`Π_{t+1} = P_{t+1}/P_t`, `i_t = φ(Π_t)` and `λ > 0`, the Fisher equation (4.3) at every date is
equivalent to (4.5) at every date. -/
theorem fisher_path_iff_eq45 {β : ℝ} {lam φ : ℝ → ℝ} {P Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hP : ∀ t, 0 < P t) (hPi : ∀ t, Pi_ (t + 1) = P (t + 1) / P t)
    (hlam : ∀ t, 0 < lam (φ (Pi_ t))) :
    (∀ t, 1 + φ (Pi_ t) =
        β⁻¹ * ((lam (φ (Pi_ (t + 1))) / lam (φ (Pi_ t))) * (P t / P (t + 1)))⁻¹) ↔
      ∀ t, Pi_ (t + 1) / lam (φ (Pi_ (t + 1))) = β * (1 + φ (Pi_ t)) / lam (φ (Pi_ t)) := by
  refine forall_congr' fun t => ?_
  rw [show Pi_ (t + 1) / lam (φ (Pi_ (t + 1))) = (P (t + 1) / P t) / lam (φ (Pi_ (t + 1))) by
    rw [← hPi t]]
  exact eq45_iff_fisher hβ (hlam t) (hlam (t + 1)) (hP t) (hP (t + 1))

/-- Woodford (2003), (4.5) ⇒ (4.6), p. 125: in the cashless limit / separable case `λ` is a
positive constant and (4.5) reduces to (4.6). -/
theorem isPath45_iff_isPath46_of_const {β c : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hc : 0 < c) :
    IsPath45 β (fun _ => c) φ Pi_ ↔ IsPath46 β φ Pi_ := by
  unfold IsPath45 IsPath46
  refine and_congr Iff.rfl (forall_congr' fun t => ?_)
  rw [div_left_inj' hc.ne']

/-! ## Existence of solutions and the bound (4.4) -/

/-- Woodford (2003), eq. (4.6), p. 125: the map `Π ↦ β(1 + φ(Π))` (the solid curve of
Figure 2.4). -/
def map46 (β : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun x => β * (1 + φ x)

/-- Woodford (2003), p. 125: the solution of (4.6) started from `Π₀`. -/
def orbit46 (β : ℝ) (φ : ℝ → ℝ) (Pi0 : ℝ) : ℕ → ℝ := fun t => (map46 β φ)^[t] Pi0

/-- Woodford (2003), p. 125: the orbit obeys (4.6). -/
theorem orbit46_succ (β : ℝ) (φ : ℝ → ℝ) (Pi0 : ℝ) (t : ℕ) :
    orbit46 β φ Pi0 (t + 1) = map46 β φ (orbit46 β φ Pi0 t) :=
  Function.iterate_succ_apply' _ _ _

/-- Woodford (2003), p. 125, "starting from any arbitrarily chosen initial inflation rate
`Π₀ > 0`, I can construct a sequence `{Π_t}` that satisfies (4.6)": for `β > 0` and `φ ≥ 0` the
orbit from any `Π₀ > 0` is a positive solution of (4.6). -/
theorem orbit46_isPath {β : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    {Pi0 : ℝ} (h0 : 0 < Pi0) : IsPath46 β φ (orbit46 β φ Pi0) := by
  have hpos : ∀ t, 0 < orbit46 β φ Pi0 t := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih =>
      rw [orbit46_succ]
      have := hφ0 _ ih
      simp only [map46]
      positivity
  exact ⟨hpos, fun t => orbit46_succ β φ Pi0 t⟩

/-- Woodford (2003), p. 125: a solution of (4.6) is pinned down by its initial inflation
rate. -/
theorem isPath46_eq_orbit {β : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (h : IsPath46 β φ Pi_) :
    Pi_ = orbit46 β φ (Pi_ 0) := by
  funext t
  induction t with
  | zero => rfl
  | succ n ih => rw [h.2 n, orbit46_succ, ih]; rfl

/-- Woodford (2003), eq. (4.4), p. 124: the summand `β^T λ(i_T)[ȳ + i_T/(1+i_T) L(i_T)]`. -/
noncomputable def bound44Term (β ybar : ℝ) (lam L : ℝ → ℝ) (i : ℕ → ℝ) (T : ℕ) : ℝ :=
  β ^ T * (lam (i T) * (ybar + i T / (1 + i T) * L (i T)))

/-- Woodford (2003), (4.4), p. 125 and fn. 58: if `λ` is bounded along the path and `i L(i)` is
bounded (e.g. satiation in real balances), the bound (4.4) holds for every nonnegative interest
path: the series has nonnegative terms and converges. -/
theorem bound44_summable {β ybar Λ K : ℝ} {lam L : ℝ → ℝ} {i : ℕ → ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hy : 0 ≤ ybar) (hi : ∀ T, 0 ≤ i T) (hlam0 : ∀ T, 0 < lam (i T))
    (hlamΛ : ∀ T, lam (i T) ≤ Λ) (hL0 : ∀ j, 0 ≤ j → 0 ≤ L j) (hLK : ∀ j, 0 ≤ j → j * L j ≤ K) :
    (∀ T, 0 ≤ bound44Term β ybar lam L i T) ∧ Summable (bound44Term β ybar lam L i) := by
  have hterm : ∀ T, 0 ≤ i T / (1 + i T) * L (i T) ∧ i T / (1 + i T) * L (i T) ≤ K := by
    intro T
    have h1 : 0 < 1 + i T := by linarith [hi T]
    have hL := hL0 _ (hi T)
    refine ⟨mul_nonneg (div_nonneg (hi T) h1.le) hL, ?_⟩
    have : i T / (1 + i T) * L (i T) ≤ i T * L (i T) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h1]
      nlinarith [mul_nonneg (mul_nonneg (hi T) hL) (hi T)]
    linarith [hLK _ (hi T)]
  have hnn : ∀ T, 0 ≤ bound44Term β ybar lam L i T := by
    intro T
    unfold bound44Term
    have := (hterm T).1
    have := (hlam0 T).le
    positivity
  refine ⟨hnn, Summable.of_nonneg_of_le hnn (fun T => ?_)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (Λ * (ybar + K)))⟩
  unfold bound44Term
  have hb : 0 ≤ β ^ T := pow_nonneg hβ0 T
  have h2 : lam (i T) * (ybar + i T / (1 + i T) * L (i T)) ≤ Λ * (ybar + K) := by
    have h3 := (hterm T).2
    have h4 := (hterm T).1
    have h5 := (hlam0 T).le
    calc lam (i T) * (ybar + i T / (1 + i T) * L (i T)) ≤ lam (i T) * (ybar + K) := by
          gcongr
      _ ≤ Λ * (ybar + K) := mul_le_mul_of_nonneg_right (hlamΛ T) (by linarith)
  exact mul_le_mul_of_nonneg_left h2 hb

/-- Woodford (2003), p. 125, "there exists a continuum of perfect-foresight equilibria, one
corresponding to each possible initial inflation rate `Π₀`": in the separable case
(`λ ≡ c > 0`), with `φ ≥ 0` and `iL(i)` bounded, every `Π₀ > 0` starts a solution of (4.6)
whose interest path `i_t = φ(Π_t)` satisfies (4.4), and distinct `Π₀` give distinct paths. -/
theorem continuum_pf_equilibria {β ybar c K : ℝ} {φ L : ℝ → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hy : 0 ≤ ybar) (hc : 0 < c) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hL0 : ∀ j, 0 ≤ j → 0 ≤ L j)
    (hLK : ∀ j, 0 ≤ j → j * L j ≤ K) :
    Set.InjOn (orbit46 β φ) (Set.Ioi 0) ∧
      ∀ Pi0, 0 < Pi0 → IsPath46 β φ (orbit46 β φ Pi0) ∧
        Summable (bound44Term β ybar (fun _ => c) L (fun t => φ (orbit46 β φ Pi0 t))) := by
  refine ⟨fun a _ b _ hab => by simpa [orbit46] using congrFun hab 0, fun Pi0 h0 => ?_⟩
  have hp := orbit46_isPath hβ0 hφ0 h0
  refine ⟨hp, (bound44_summable (Λ := c) hβ0.le hβ1 hy (fun T => hφ0 _ (hp.1 T))
    (fun _ => hc) (fun _ => le_rfl) hL0 hLK).2⟩

/-! ## Steady states -/

/-- Woodford (2003), p. 124: the target `Π*` with `φ(Π*) = β⁻¹Π* − 1` is a steady state of
(4.6). -/
theorem target_isFixed {β Pis : ℝ} {φ : ℝ → ℝ} (hβ : β ≠ 0) (htarget : φ Pis = Pis / β - 1) :
    map46 β φ Pis = Pis := by
  simp only [map46, htarget]
  field_simp
  ring

/-- Woodford (2003), p. 125: the derivative of the map (4.6) is `βφ'`. -/
theorem hasDerivAt_map46 {β d x : ℝ} {φ : ℝ → ℝ} (hd : HasDerivAt φ d x) :
    HasDerivAt (map46 β φ) (β * d) x := by
  have h := ((hasDerivAt_const x (1 : ℝ)).add hd).const_mul β
  rw [zero_add] at h
  exact h

/-- Woodford (2003), p. 125: the Taylor coefficient `φ_π = Π*φ'(Π*)/(1 + φ(Π*))` (the elasticity
of `1 + i` with respect to `Π` at the target) equals `βφ'(Π*)`, the slope of the curve of
Figure 2.4 at `Π*`; so "the Taylor principle" `φ_π > 1` is "the curve cuts the diagonal from
below". -/
theorem taylorCoeff_eq_slope {β Pis d : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β) (hPis : 0 < Pis)
    (htarget : φ Pis = Pis / β - 1) : Pis * d / (1 + φ Pis) = β * d := by
  rw [htarget, show 1 + (Pis / β - 1) = Pis / β by ring]
  field_simp

/-- Woodford (2003), p. 125, "the fact that `φ(Π) ≥ 0` for all `Π` implies that there also must
be another steady state … at some lower rate of inflation. At this lower steady state, the
curve must cut the diagonal from above; thus … the Taylor principle cannot be globally valid":
under the local Taylor principle `βφ'(Π*) > 1` there is a steady state `Π** ∈ [β, Π*)` with the
curve strictly above the diagonal on `(0, Π**)`, and the Taylor principle fails weakly there
(`βφ'(Π**) ≤ 1` whenever `φ` is differentiable at `Π**`). -/
theorem second_steady_state {β Pis d : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β) (hPis : β < Pis)
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0))
    (htarget : φ Pis = Pis / β - 1) (hd : HasDerivAt φ d Pis) (htaylor : 1 < β * d) :
    ∃ Pss, β ≤ Pss ∧ Pss < Pis ∧ map46 β φ Pss = Pss ∧
      (∀ x, 0 < x → x < Pss → x < map46 β φ x) ∧
      (∀ d', HasDerivAt φ d' Pss → β * d' ≤ 1) := by
  set f : ℝ → ℝ := fun x => map46 β φ x - x with hf
  have hfd : ∀ {x e}, HasDerivAt φ e x → HasDerivAt f (β * e - 1) x :=
    fun h => (hasDerivAt_map46 h).sub (hasDerivAt_id _)
  have hfPis : f Pis = 0 := by simp [hf, target_isFixed hβ.ne' htarget]
  have hfcont : ∀ a b, 0 < a → ContinuousOn f (Set.Icc a b) := by
    intro a b ha
    have hφc : ContinuousOn φ (Set.Icc a b) :=
      hcont.mono fun y hy => lt_of_lt_of_le ha hy.1
    exact (continuousOn_const.mul (continuousOn_const.add hφc)).sub continuousOn_id
  have hfβ : 0 ≤ f β := by
    simp only [hf, map46]
    nlinarith [hφ0 β hβ]
  -- a point just left of `Π*` where the curve is below the diagonal
  obtain ⟨δ, hδ, hleft, -⟩ := sign_near_of_deriv_pos (hfd hd) (by linarith)
  set y1 := max β (Pis - δ / 2) with hy1
  have hy1lt : y1 < Pis := max_lt hPis (by linarith)
  have hfy1 : f y1 < 0 := by
    have := hleft y1 (by rw [hy1]; exact lt_max_of_lt_right (by linarith)) hy1lt
    rwa [hfPis] at this
  have hβy1 : β ≤ y1 := le_max_left _ _
  set S := Set.Icc β y1 ∩ f ⁻¹' {0} with hS
  have hSne : S.Nonempty := by
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hβy1 (hfcont β y1 hβ) ⟨hfy1.le, hfβ⟩
    exact ⟨c, hc, hfc⟩
  have hSclosed : IsClosed S :=
    (hfcont β y1 hβ).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSbdd : BddBelow S := ⟨β, fun z hz => hz.1.1⟩
  have hmem := hSclosed.csInf_mem hSne hSbdd
  set Pss := sInf S with hPss
  have hPssβ : β ≤ Pss := hmem.1.1
  have hPssfix : f Pss = 0 := hmem.2
  have habove : ∀ x, 0 < x → x < Pss → x < map46 β φ x := by
    intro x hx0 hxP
    by_cases hxβ : x < β
    · simp only [map46]
      nlinarith [hφ0 x hx0]
    · push Not at hxβ
      by_contra hcon
      push Not at hcon
      have hfx : f x ≤ 0 := by simp only [hf]; linarith
      obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hxβ (hfcont β x hβ) ⟨hfx, hfβ⟩
      have hcS : c ∈ S := ⟨⟨hc.1, by linarith [hc.2, hmem.1.2]⟩, hfc⟩
      have := csInf_le hSbdd hcS
      linarith [hc.2]
  refine ⟨Pss, hPssβ, by linarith [hmem.1.2], by simpa [hf, sub_eq_zero] using hPssfix,
    habove, fun d' hd' => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, hl, -⟩ := sign_near_of_deriv_pos (hfd hd') (by linarith)
  set y := max (Pss / 2) (Pss - ε / 2) with hy
  have hPss0 : 0 < Pss := by linarith
  have hyP : y < Pss := max_lt (by linarith) (by linarith)
  have hy0 : 0 < y := lt_max_of_lt_left (by linarith)
  have h1 := hl y (lt_max_of_lt_right (by linarith)) hyP
  have h2 := habove y hy0 hyP
  simp only [hf] at h1 hPssfix
  linarith

/-! ## Self-fulfilling deflations (Figure 2.4) -/

/-- Woodford (2003), p. 126: under `φ(β) = 0` and `φ(Π) < β⁻¹Π − 1` on `(β, Π*)`, the map (4.6)
sends `[β, Π*)` into itself, weakly downward. -/
theorem map46_step_down {β Pis x : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β)
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hx : β ≤ x) (hxP : x < Pis) :
    β ≤ map46 β φ x ∧ map46 β φ x ≤ x := by
  simp only [map46]
  refine ⟨by nlinarith [hφ0 x (by linarith)], ?_⟩
  rcases hx.lt_or_eq with hlt | heq
  · have h := hbelow x hlt hxP
    have : β * φ x < β * (x / β - 1) := mul_lt_mul_of_pos_left h hβ
    rw [mul_sub, mul_div_cancel₀ x hβ.ne'] at this
    linarith
  · rw [← heq, hφβ]; simp

/-- Woodford (2003), p. 126, Figure 2.4, "a self-fulfilling deflation": if `φ ≥ 0` is continuous,
`φ(β) = 0` and `φ(Π) < β⁻¹Π − 1` on `(β, Π*)`, every solution of (4.6) starting in `(β, Π*)` is
nonincreasing, stays in `[β, Π₀]` and converges to the Friedman rate `Π** = β`. -/
theorem self_fulfilling_deflation46 {β Pis : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hpath : IsPath46 β φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) :
    Antitone Pi_ ∧ (∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0) ∧ Tendsto Pi_ atTop (𝓝 β) := by
  have hstep : ∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0 ∧ Pi_ (t + 1) ≤ Pi_ t := by
    intro t
    induction t with
    | zero =>
      have := map46_step_down hβ hφ0 hφβ hbelow h0.1.le h0.2
      exact ⟨h0.1.le, le_rfl, by rw [hpath.2 0]; exact this.2⟩
    | succ n ih =>
      have hb : β ≤ Pi_ (n + 1) := by
        rw [hpath.2 n]
        exact (map46_step_down hβ hφ0 hφβ hbelow ih.1 (by linarith [h0.2, ih.2.1])).1
      have hle : Pi_ (n + 1) ≤ Pi_ 0 := le_trans ih.2.2 ih.2.1
      refine ⟨hb, hle, ?_⟩
      rw [hpath.2 (n + 1)]
      exact (map46_step_down hβ hφ0 hφβ hbelow hb (by linarith [h0.2])).2
  have hanti : Antitone Pi_ := antitone_nat_of_succ_le fun t => (hstep t).2.2
  refine ⟨hanti, fun t => ⟨(hstep t).1, (hstep t).2.1⟩, ?_⟩
  have hbdd : BddBelow (Set.range Pi_) := ⟨β, by rintro _ ⟨t, rfl⟩; exact (hstep t).1⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ t, Pi_ t with hL
  have hLβ : β ≤ L := le_ciInf fun t => (hstep t).1
  have hL0 : L ≤ Pi_ 0 := ciInf_le hbdd 0
  have hcontL : ContinuousAt (map46 β φ) L := by
    have : ContinuousAt φ L := hcont.continuousAt (Ioi_mem_nhds (by linarith))
    exact continuousAt_const.mul (continuousAt_const.add this)
  have hfix := fixed_of_tendsto hpath.2 hlim hcontL
  rcases hLβ.lt_or_eq with hlt | heq
  · exfalso
    have := (map46_step_down hβ hφ0 hφβ hbelow hLβ (by linarith [h0.2])).2
    have h := hbelow L hlt (by linarith [h0.2])
    have : β * φ L < β * (L / β - 1) := mul_lt_mul_of_pos_left h hβ
    rw [mul_sub, mul_div_cancel₀ L hβ.ne'] at this
    simp only [map46] at hfix
    linarith
  · rw [← heq] at hlim; exact hlim

/-- Woodford (2003), p. 126: if moreover `φ > 0` on `(β, Π*)`, inflation declines strictly
monotonically and never reaches `β` ("approaching the value `Π** = β` asymptotically"). -/
theorem deflation46_strictAnti {β Pis : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hφpos : ∀ x, β < x → x < Pis → 0 < φ x)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hpath : IsPath46 β φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) : StrictAnti Pi_ ∧ ∀ t, β < Pi_ t := by
  have hstep : ∀ t, β < Pi_ t ∧ Pi_ t ≤ Pi_ 0 ∧ Pi_ (t + 1) < Pi_ t := by
    intro t
    induction t with
    | zero =>
      refine ⟨h0.1, le_rfl, ?_⟩
      have h := hbelow _ h0.1 h0.2
      have : β * φ (Pi_ 0) < β * (Pi_ 0 / β - 1) := mul_lt_mul_of_pos_left h hβ
      rw [mul_sub, mul_div_cancel₀ _ hβ.ne'] at this
      rw [hpath.2 0]; linarith
    | succ n ih =>
      have hb : β < Pi_ (n + 1) := by
        rw [hpath.2 n]
        have := hφpos _ ih.1 (by linarith [h0.2, ih.2.1])
        nlinarith
      have hle : Pi_ (n + 1) ≤ Pi_ 0 := le_trans ih.2.2.le ih.2.1
      refine ⟨hb, hle, ?_⟩
      have h := hbelow _ hb (by linarith [h0.2])
      have : β * φ (Pi_ (n + 1)) < β * (Pi_ (n + 1) / β - 1) := mul_lt_mul_of_pos_left h hβ
      rw [mul_sub, mul_div_cancel₀ _ hβ.ne'] at this
      rw [hpath.2 (n + 1)]; linarith
  exact ⟨strictAnti_nat_of_succ_lt fun t => (hstep t).2.2, fun t => (hstep t).1⟩

/-- Woodford (2003), p. 126, "eventually, actual deflation": with `β < 1`, inflation along a
self-fulfilling deflation is eventually below one. -/
theorem deflation46_eventually_deflation {β Pis : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0))
    (hφβ : φ β = 0) (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1)
    (hpath : IsPath46 β φ Pi_) (h0 : Pi_ 0 ∈ Set.Ioo β Pis) : ∀ᶠ t in atTop, Pi_ t < 1 :=
  (self_fulfilling_deflation46 hβ hφ0 hcont hφβ hbelow hpath h0).2.2.eventually
    (gt_mem_nhds hβ1)

/-- Woodford (2003), p. 127, "equilibrium is indeterminate even locally, near the
deflationary steady state; for any neighborhood of `Π**`, there exists a continuum of distinct
equilibria in which inflation remains forever within this range": for every `ε > 0` each
`Π₀ ∈ (β, min(Π*, β + ε))` starts a solution of (4.6) that stays within `ε` of `β`, and distinct
`Π₀` give distinct solutions. -/
theorem deflationary_steady_state_indeterminate {β Pis : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β)
    (hPis : β < Pis) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0))
    (hφβ : φ β = 0) (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) {ε : ℝ} (hε : 0 < ε) :
    (Set.Ioo β (min Pis (β + ε))).Nonempty ∧
      Set.InjOn (orbit46 β φ) (Set.Ioo β (min Pis (β + ε))) ∧
      ∀ Pi0 ∈ Set.Ioo β (min Pis (β + ε)),
        IsPath46 β φ (orbit46 β φ Pi0) ∧ ∀ t, |orbit46 β φ Pi0 t - β| < ε := by
  refine ⟨⟨(β + min Pis (β + ε)) / 2, by
      constructor <;> linarith [lt_min hPis (by linarith : β < β + ε)]⟩,
    fun a _ b _ hab => by simpa [orbit46] using congrFun hab 0, fun Pi0 hP => ?_⟩
  have h1 : Pi0 < Pis := lt_of_lt_of_le hP.2 (min_le_left _ _)
  have h2 : Pi0 < β + ε := lt_of_lt_of_le hP.2 (min_le_right _ _)
  have hp := orbit46_isPath hβ hφ0 (by linarith [hP.1] : 0 < Pi0)
  refine ⟨hp, fun t => ?_⟩
  have hd := self_fulfilling_deflation46 hβ hφ0 hcont hφβ hbelow hp
    (by simpa [orbit46] using (⟨hP.1, h1⟩ : Pi0 ∈ Set.Ioo β Pis))
  have hb := hd.2.1 t
  have h00 : orbit46 β φ Pi0 0 = Pi0 := rfl
  rw [abs_lt]
  constructor <;> linarith [hb.1, hb.2]

/-! ## Self-fulfilling inflations (error E6) -/

/-- Woodford (2003), p. 127, corrected (error E6): if `φ(Π) > β⁻¹Π − 1` for every `Π > Π*`
(no steady state above the target) and `φ` is continuous, every solution of (4.6) starting
above `Π*` is strictly increasing and grows without bound. -/
theorem inflation_unbounded46 {β Pis : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hcont : ContinuousOn φ (Set.Ioi 0)) (habove : ∀ x, Pis < x → x / β - 1 < φ x)
    (hpath : IsPath46 β φ Pi_) (h0 : Pis < Pi_ 0) :
    StrictMono Pi_ ∧ Tendsto Pi_ atTop atTop := by
  have hup : ∀ x, Pis < x → x < map46 β φ x := by
    intro x hx
    have : β * (x / β - 1) < β * φ x := mul_lt_mul_of_pos_left (habove x hx) hβ
    rw [mul_sub, mul_div_cancel₀ x hβ.ne'] at this
    simp only [map46]; linarith
  have hstep : ∀ t, Pis < Pi_ t ∧ Pi_ t < Pi_ (t + 1) := by
    intro t
    induction t with
    | zero => exact ⟨h0, by rw [hpath.2 0]; exact hup _ h0⟩
    | succ n ih =>
      have h1 : Pis < Pi_ (n + 1) := by linarith [ih.1, ih.2]
      exact ⟨h1, by rw [hpath.2 (n + 1)]; exact hup _ h1⟩
  have hsm : StrictMono Pi_ := strictMono_nat_of_lt_succ fun t => (hstep t).2
  refine ⟨hsm, ?_⟩
  rcases monotone_orbit_atTop_or_fixed (g := map46 β φ) hpath.2 hsm.monotone with
    h | ⟨L, hL, hbd, hfix⟩
  · exact h
  · exfalso
    have hL0 : Pi_ 0 ≤ L := hbd 0
    have hcL : ContinuousAt (map46 β φ) L :=
      continuousAt_const.mul (continuousAt_const.add
        (hcont.continuousAt (Ioi_mem_nhds (by linarith [hpath.1 0]))))
    have hf := hfix hcL
    have hu := hup L (by linarith)
    simp only [map46] at hf hu
    linarith

/-- Woodford (2003), p. 127, error E6, exact form: under continuity, `φ ≥ 0`, the target
condition and the local Taylor principle `βφ'(Π*) > 1`, *every* solution of (4.6) starting
above `Π*` grows without bound if and only if (4.6) has no steady state above `Π*`. -/
theorem inflation_unbounded_iff {β Pis d : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β) (hPis : 0 < Pis)
    (hcont : ContinuousOn φ (Set.Ioi 0))
    (htarget : φ Pis = Pis / β - 1) (hd : HasDerivAt φ d Pis) (htaylor : 1 < β * d) :
    (∀ Pi_ : ℕ → ℝ, IsPath46 β φ Pi_ → Pis < Pi_ 0 → Tendsto Pi_ atTop atTop) ↔
      ∀ x, Pis < x → map46 β φ x ≠ x := by
  constructor
  · intro h x hx hfix
    have hp : IsPath46 β φ (fun _ => x) := ⟨fun _ => by linarith, fun _ => hfix.symm⟩
    have := (h _ hp hx).eventually (eventually_ge_atTop (x + 1))
    obtain ⟨t, ht⟩ := this.exists
    linarith
  · intro hno Pi_ hp h0
    set f : ℝ → ℝ := fun x => map46 β φ x - x with hf
    have hfd : HasDerivAt f (β * d - 1) Pis := (hasDerivAt_map46 hd).sub (hasDerivAt_id _)
    have hfPis : f Pis = 0 := by simp [hf, target_isFixed hβ.ne' htarget]
    obtain ⟨δ, hδ, -, hright⟩ := sign_near_of_deriv_pos hfd (by linarith)
    have habove : ∀ x, Pis < x → x / β - 1 < φ x := by
      intro x hx
      have hfx : 0 < f x := by
        by_contra hcon
        push Not at hcon
        have hne : f x ≠ 0 := by simp only [hf]; exact sub_ne_zero.mpr (hno x hx)
        have hneg : f x < 0 := lt_of_le_of_ne hcon hne
        set y := min (Pis + δ / 2) ((Pis + x) / 2) with hy
        have hyP : Pis < y := lt_min (by linarith) (by linarith)
        have hyx : y ≤ x := le_trans (min_le_right _ _) (by linarith)
        have hfy : 0 < f y := by
          have := hright y hyP (lt_of_le_of_lt (min_le_left _ _) (by linarith))
          rwa [hfPis] at this
        have hfc : ContinuousOn f (Set.Icc y x) := by
          have hφc : ContinuousOn φ (Set.Icc y x) :=
            hcont.mono fun z hz => (by linarith [hz.1] : (0 : ℝ) < z)
          exact (continuousOn_const.mul (continuousOn_const.add hφc)).sub continuousOn_id
        obtain ⟨c, hc, hfc0⟩ := intermediate_value_Icc' hyx hfc ⟨hneg.le, hfy.le⟩
        exact hno c (by linarith [hc.1]) (by simpa [hf, sub_eq_zero] using hfc0)
      simp only [hf, map46] at hfx
      have : x < β * (1 + φ x) := by linarith
      rw [div_sub_one hβ.ne', div_lt_iff₀ hβ]
      linarith
    exact (inflation_unbounded46 hβ hcont habove hp h0).2

/-- Woodford (2003), p. 127, error E6: the policy function of the counterexample,
`φ(Π) = max(0, min(3Π − 2, 2))` (with `β = 1/2`, `Π* = 1`): it saturates at `2`, so the curve of
Figure 2.4 crosses the diagonal again at `Π = 3/2`. -/
noncomputable def phiCE (x : ℝ) : ℝ := max 0 (min (3 * x - 2) 2)

/-- Woodford (2003), p. 127, error E6, counterexample: `φ = phiCE` is continuous, increasing and
nonnegative, hits the target `φ(Π*) = β⁻¹Π* − 1` at `Π* = 1` with `β = 1/2`, satisfies the Taylor
principle there (`βφ'(Π*) = 3/2 > 1`), and yet the constant path `Π_t = 3/2 > Π*` solves (4.6):
inflation above target need not rise, let alone without bound. -/
theorem e6_counterexample :
    Continuous phiCE ∧ Monotone phiCE ∧ (∀ x, 0 ≤ phiCE x) ∧ phiCE 1 = 1 / (1 / 2) - 1 ∧
      HasDerivAt phiCE 3 1 ∧ 1 < (1 / 2 : ℝ) * 3 ∧
      IsPath46 (1 / 2) phiCE (fun _ => 3 / 2) ∧ (1 : ℝ) < 3 / 2 ∧
      ¬ Tendsto (fun _ : ℕ => (3 / 2 : ℝ)) atTop atTop := by
  refine ⟨by unfold phiCE; fun_prop, ?_, fun x => le_max_left _ _, ?_, ?_, by norm_num,
    ⟨fun _ => by norm_num, fun _ => ?_⟩, by norm_num, ?_⟩
  · intro a b hab
    unfold phiCE
    exact max_le_max le_rfl (min_le_min (by linarith) le_rfl)
  · unfold phiCE; norm_num
  · have h : HasDerivAt (fun x : ℝ => 3 * x - 2) 3 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).const_mul 3).sub_const 2
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (by norm_num : (2 / 3 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 4 / 3)] with x hx
    unfold phiCE
    rw [min_eq_left (by linarith [hx.2]), max_eq_right (by linarith [hx.1])]
  · unfold phiCE; norm_num
  · intro h
    obtain ⟨t, ht⟩ := (h.eventually (eventually_ge_atTop (2 : ℝ))).exists
    norm_num at ht

/-! ## Local repulsion at the target -/

/-- Woodford (2003), p. 127, "any deterministic equilibrium other than the one with `Π_t = Π*`
forever involves an inflation rate that diverges further and further from the target …
every other equilibrium eventually leaves a neighborhood of `Π*`": under the local Taylor
principle `βφ'(Π*) > 1` there is `δ > 0` such that every solution of (4.6) with `Π₀ ≠ Π*` is at
some date at distance at least `δ` from `Π*`. -/
theorem target_locally_repelling {β Pis d : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β)
    (htarget : φ Pis = Pis / β - 1) (hd : HasDerivAt φ d Pis) (htaylor : 1 < β * d) :
    ∃ δ > 0, ∀ Pi_ : ℕ → ℝ, IsPath46 β φ Pi_ → Pi_ 0 ≠ Pis → ∃ t, δ ≤ |Pi_ t - Pis| := by
  obtain ⟨δ, hδ, h⟩ := repelling_of_one_lt_abs_deriv (target_isFixed hβ.ne' htarget)
    (hasDerivAt_map46 hd) (by rw [abs_of_pos (by linarith)]; exact htaylor)
  exact ⟨δ, hδ, fun Pi_ hp h0 => h Pi_ hp.2 h0⟩

/-- Woodford (2003), p. 127: consequently, under the local Taylor principle, the only solution
of (4.6) that remains forever in a small enough neighbourhood of `Π*` is `Π_t ≡ Π*`
(local determinacy). -/
theorem target_locally_unique {β Pis d : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β)
    (htarget : φ Pis = Pis / β - 1) (hd : HasDerivAt φ d Pis) (htaylor : 1 < β * d) :
    ∃ δ > 0, ∀ Pi_ : ℕ → ℝ, IsPath46 β φ Pi_ → (∀ t, |Pi_ t - Pis| < δ) → ∀ t, Pi_ t = Pis := by
  obtain ⟨δ, hδ, h⟩ := target_locally_repelling hβ htarget hd htaylor
  refine ⟨δ, hδ, fun Pi_ hp hin => ?_⟩
  have h0 : Pi_ 0 = Pis := by
    by_contra hne
    obtain ⟨t, ht⟩ := h Pi_ hp hne
    linarith [hin t]
  intro t
  rw [isPath46_eq_orbit hp, h0]
  induction t with
  | zero => rfl
  | succ n ih => rw [orbit46_succ, ih, target_isFixed hβ.ne' htarget]

/-! ## Real-balance effects: (4.5) -/

/-- Woodford (2003), p. 127, "in the case that real balances are complementary with private
expenditure (`u_cm > 0`) … `λ(i)` is a decreasing function, and this condition is necessarily
satisfied": if `λ > 0` is nonincreasing on `[0, ∞)` and `φ ≥ 0` is nondecreasing, then
`Π ↦ Π/λ(φ(Π))` is strictly increasing on `(0, ∞)`. -/
theorem ratio_strictMonoOn {lam φ : ℝ → ℝ} (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hanti : AntitoneOn lam (Set.Ici 0)) (hmono : MonotoneOn φ (Set.Ioi 0))
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) :
    StrictMonoOn (fun x => x / lam (φ x)) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have hφab : φ a ≤ φ b := hmono ha hb hab.le
  have hl : lam (φ b) ≤ lam (φ a) :=
    hanti (Set.mem_Ici.mpr (hφ0 a ha')) (Set.mem_Ici.mpr (hφ0 b hb')) hφab
  have hla := hlam _ (hφ0 a ha')
  have hlb := hlam _ (hφ0 b hb')
  calc a / lam (φ a) < b / lam (φ a) := div_lt_div_of_pos_right hab hla
    _ ≤ b / lam (φ b) := div_le_div_of_nonneg_left hb'.le hlb hl

/-- Woodford (2003), (4.5), p. 127: the steady states of (4.5) are those of (4.6), since `λ`
cancels at a constant inflation rate. -/
theorem steady_state45_iff {β x : ℝ} {lam φ : ℝ → ℝ} (hl : 0 < lam (φ x)) :
    x / lam (φ x) = β * (1 + φ x) / lam (φ x) ↔ map46 β φ x = x := by
  rw [div_left_inj' hl.ne', map46, eq_comm]

/-- Woodford (2003), p. 127: when `Π/λ(φ(Π))` is strictly increasing, a solution of (4.5) is
pinned down by its initial inflation rate. -/
theorem isPath45_unique {β : ℝ} {lam φ : ℝ → ℝ} {Pi_ Pi' : ℕ → ℝ}
    (hinj : StrictMonoOn (fun x => x / lam (φ x)) (Set.Ioi 0)) (h1 : IsPath45 β lam φ Pi_)
    (h2 : IsPath45 β lam φ Pi') (h0 : Pi_ 0 = Pi' 0) : Pi_ = Pi' := by
  funext t
  induction t with
  | zero => exact h0
  | succ n ih =>
    have e1 := h1.2 n
    have e2 := h2.2 n
    rw [ih] at e1
    refine hinj.injOn (h1.1 (n + 1)) (h2.1 (n + 1)) ?_
    show Pi_ (n + 1) / lam (φ (Pi_ (n + 1))) = Pi' (n + 1) / lam (φ (Pi' (n + 1)))
    rw [e1, e2]

/-- Woodford (2003), p. 127: under `λ > 0` nonincreasing, `φ(β) = 0` and `φ(Π) < β⁻¹Π − 1` on
`(β, Π*)`, the successor `Π'` of any `Π ∈ [β, Π*)` under (4.5) lies in `[β, Π]`. -/
theorem step45_down {β Pis x y : ℝ} {lam φ : ℝ → ℝ} (hβ : 0 < β)
    (hlam : ∀ j, 0 ≤ j → 0 < lam j) (hanti : AntitoneOn lam (Set.Ici 0))
    (hmono : MonotoneOn φ (Set.Ioi 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hx : β ≤ x) (hxP : x < Pis)
    (hy : 0 < y) (heq : y / lam (φ y) = β * (1 + φ x) / lam (φ x)) : β ≤ y ∧ y ≤ x := by
  have hsm := ratio_strictMonoOn hlam hanti hmono hφ0
  have hx0 : 0 < x := by linarith
  have hφx := hφ0 x hx0
  have hlx := hlam _ hφx
  have hdown := map46_step_down hβ hφ0 hφβ hbelow hx hxP
  have hl0 : lam (φ x) ≤ lam 0 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hφx) hφx
  have hlam0 := hlam 0 le_rfl
  constructor
  · by_contra hcon
    push Not at hcon
    have h1 : y / lam (φ y) < β / lam (φ β) := hsm hy hβ hcon
    rw [hφβ, heq] at h1
    have h2 : β / lam 0 ≤ β / lam (φ x) := div_le_div_of_nonneg_left hβ.le hlx hl0
    have h3 : β / lam (φ x) ≤ β * (1 + φ x) / lam (φ x) :=
      div_le_div_of_nonneg_right (by nlinarith) hlx.le
    linarith
  · by_contra hcon
    push Not at hcon
    have h1 : x / lam (φ x) < y / lam (φ y) := hsm hx0 hy hcon
    rw [heq] at h1
    have h2 : β * (1 + φ x) / lam (φ x) ≤ x / lam (φ x) :=
      div_le_div_of_nonneg_right hdown.2 hlx.le
    linarith

/-- Woodford (2003), p. 127, "this suffices to imply the existence of a continuum of solutions
to (4.5) involving self-fulfilling deflation" (convergence part): if `λ > 0` is continuous and
nonincreasing on `[0, ∞)`, `φ ≥ 0` is continuous and nondecreasing, `φ(β) = 0` and
`φ(Π) < β⁻¹Π − 1` on `(β, Π*)`, every solution of (4.5) starting in `(β, Π*)` is nonincreasing,
stays in `[β, Π₀]` and converges to `β`. -/
theorem self_fulfilling_deflation45 {β Pis : ℝ} {lam φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hlam : ∀ j, 0 ≤ j → 0 < lam j) (hanti : AntitoneOn lam (Set.Ici 0))
    (hlamc : ContinuousOn lam (Set.Ici 0)) (hmono : MonotoneOn φ (Set.Ioi 0))
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hpath : IsPath45 β lam φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) :
    Antitone Pi_ ∧ (∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0) ∧ Tendsto Pi_ atTop (𝓝 β) := by
  have hstep : ∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0 ∧ Pi_ (t + 1) ≤ Pi_ t := by
    intro t
    induction t with
    | zero =>
      have := step45_down hβ hlam hanti hmono hφ0 hφβ hbelow h0.1.le h0.2 (hpath.1 1)
        (hpath.2 0)
      exact ⟨h0.1.le, le_rfl, this.2⟩
    | succ n ih =>
      have h1 := step45_down hβ hlam hanti hmono hφ0 hφβ hbelow ih.1
        (by linarith [h0.2, ih.2.1]) (hpath.1 (n + 1)) (hpath.2 n)
      have hle : Pi_ (n + 1) ≤ Pi_ 0 := le_trans ih.2.2 ih.2.1
      have h2 := step45_down hβ hlam hanti hmono hφ0 hφβ hbelow h1.1
        (by linarith [h0.2]) (hpath.1 (n + 1 + 1)) (hpath.2 (n + 1))
      exact ⟨h1.1, hle, h2.2⟩
  have hanti' : Antitone Pi_ := antitone_nat_of_succ_le fun t => (hstep t).2.2
  refine ⟨hanti', fun t => ⟨(hstep t).1, (hstep t).2.1⟩, ?_⟩
  have hbdd : BddBelow (Set.range Pi_) := ⟨β, by rintro _ ⟨t, rfl⟩; exact (hstep t).1⟩
  have hlim := tendsto_atTop_ciInf hanti' hbdd
  set L := ⨅ t, Pi_ t with hL
  have hLβ : β ≤ L := le_ciInf fun t => (hstep t).1
  have hL0 : L ≤ Pi_ 0 := ciInf_le hbdd 0
  have hLpos : 0 < L := by linarith
  have hlc : ContinuousOn (fun x => lam (φ x)) (Set.Ioi 0) :=
    hlamc.comp hcont fun x hx => Set.mem_Ici.mpr (hφ0 x hx)
  have hlcL : ContinuousAt (fun x => lam (φ x)) L := hlc.continuousAt (Ioi_mem_nhds hLpos)
  have hφcL : ContinuousAt φ L := hcont.continuousAt (Ioi_mem_nhds hLpos)
  have hlL := hlam _ (hφ0 L hLpos)
  have hhc : ContinuousAt (fun x => x / lam (φ x)) L := continuousAt_id.div hlcL hlL.ne'
  have hRc : ContinuousAt (fun x => β * (1 + φ x) / lam (φ x)) L :=
    (continuousAt_const.mul (continuousAt_const.add hφcL)).div hlcL hlL.ne'
  have hA : Tendsto (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) atTop
      (𝓝 (L / lam (φ L))) :=
    hhc.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have hB : Tendsto (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) atTop
      (𝓝 (β * (1 + φ L) / lam (φ L))) := by
    have : (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) =
        (fun x => β * (1 + φ x) / lam (φ x)) ∘ Pi_ := funext fun t => hpath.2 t
    rw [this]
    exact hRc.tendsto.comp hlim
  have hfix : map46 β φ L = L := (steady_state45_iff hlL).mp (tendsto_nhds_unique hA hB)
  rcases hLβ.lt_or_eq with hlt | heq
  · exfalso
    have h := hbelow L hlt (by linarith [h0.2])
    have : β * φ L < β * (L / β - 1) := mul_lt_mul_of_pos_left h hβ
    rw [mul_sub, mul_div_cancel₀ L hβ.ne'] at this
    simp only [map46] at hfix
    linarith
  · rw [← heq] at hlim; exact hlim

/-- Woodford (2003), p. 127 (existence part): under the hypotheses of
`self_fulfilling_deflation45`, every `Π₀ ∈ (β, Π*)` starts a solution of (4.5); with
`isPath45_unique` this is a continuum of self-fulfilling deflations indexed by `Π₀`. -/
theorem deflation45_exists {β Pis : ℝ} {lam φ : ℝ → ℝ} (hβ : 0 < β)
    (hlam : ∀ j, 0 ≤ j → 0 < lam j) (hanti : AntitoneOn lam (Set.Ici 0))
    (hlamc : ContinuousOn lam (Set.Ici 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) {Pi0 : ℝ} (h0 : Pi0 ∈ Set.Ioo β Pis) :
    ∃ Pi_ : ℕ → ℝ, IsPath45 β lam φ Pi_ ∧ Pi_ 0 = Pi0 := by
  have hlc : ContinuousOn (fun x => lam (φ x)) (Set.Ioi 0) :=
    hlamc.comp hcont fun x hx => Set.mem_Ici.mpr (hφ0 x hx)
  have hsucc : ∀ x : ℝ, ∃ y : ℝ, x ∈ Set.Ico β Pis →
      y ∈ Set.Icc β x ∧ y / lam (φ y) = β * (1 + φ x) / lam (φ x) := by
    intro x
    by_cases hx : x ∈ Set.Ico β Pis
    · have hx0 : 0 < x := by linarith [hx.1]
      have hφx := hφ0 x hx0
      have hlx := hlam _ hφx
      have hl0 : lam (φ x) ≤ lam 0 :=
        hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hφx) hφx
      have hdown := map46_step_down hβ hφ0 hφβ hbelow hx.1 hx.2
      have hcI : ContinuousOn (fun z => z / lam (φ z)) (Set.Icc β x) := by
        refine continuousOn_id.div (hlc.mono fun z hz => (by linarith [hz.1] : (0 : ℝ) < z))
          fun z hz => (hlam _ (hφ0 z (by linarith [hz.1]))).ne'
      have hlo : β / lam (φ β) ≤ β * (1 + φ x) / lam (φ x) := by
        rw [hφβ]
        calc β / lam 0 ≤ β / lam (φ x) := div_le_div_of_nonneg_left hβ.le hlx hl0
          _ ≤ β * (1 + φ x) / lam (φ x) := div_le_div_of_nonneg_right (by nlinarith) hlx.le
      have hhi : β * (1 + φ x) / lam (φ x) ≤ x / lam (φ x) :=
        div_le_div_of_nonneg_right hdown.2 hlx.le
      obtain ⟨y, hy, hyeq⟩ := intermediate_value_Icc hx.1 hcI ⟨hlo, hhi⟩
      exact ⟨y, fun _ => ⟨hy, hyeq⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose g hg using hsucc
  set Pi_ : ℕ → ℝ := fun t => g^[t] Pi0 with hPi
  have hsuccP : ∀ t, Pi_ (t + 1) = g (Pi_ t) := fun t => Function.iterate_succ_apply' _ _ _
  have hmem : ∀ t, Pi_ t ∈ Set.Ico β Pis := by
    intro t
    induction t with
    | zero => exact ⟨h0.1.le, h0.2⟩
    | succ n ih =>
      rw [hsuccP]
      have := (hg _ ih).1
      exact ⟨this.1, lt_of_le_of_lt this.2 ih.2⟩
  refine ⟨Pi_, ⟨fun t => by linarith [(hmem t).1], fun t => ?_⟩, rfl⟩
  rw [hsuccP]
  exact (hg _ (hmem t)).2

/-- Woodford (2003), pp. 127–128, "these solutions also satisfy (4.4) … as long as `iL(ȳ, i; 0)`
has a finite bound": along a self-fulfilling deflation of (4.5) with `λ` nonincreasing, the
interest path `i_t = φ(Π_t)` satisfies (4.4), because `λ(i_t) ≤ λ(0)`. -/
theorem deflation45_bound44 {β ybar K : ℝ} {lam φ L : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hy : 0 ≤ ybar) (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hanti : AntitoneOn lam (Set.Ici 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hL0 : ∀ j, 0 ≤ j → 0 ≤ L j) (hLK : ∀ j, 0 ≤ j → j * L j ≤ K)
    (hpath : IsPath45 β lam φ Pi_) :
    Summable (bound44Term β ybar lam L (fun t => φ (Pi_ t))) :=
  (bound44_summable (Λ := lam 0) hβ.le hβ1 hy (fun T => hφ0 _ (hpath.1 T))
    (fun T => hlam _ (hφ0 _ (hpath.1 T)))
    (fun T => hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (hφ0 _ (hpath.1 T)))
      (hφ0 _ (hpath.1 T))) hL0 hLK).2

/-! ## Real-balance effects without `λ` decreasing ("not too strongly increasing") -/

/-- Woodford (2003), p. 127, fn. 61, "it suffices that `λ` not be too strongly increasing in
`i`": the two conditions used. (H1) `Π ↦ Π/λ(φ(Π))` is strictly increasing on `(0, ∞)` (the text's
monotonicity condition); (H2) `λ(i) ≤ (1 + i)λ(0)` for `i ≥ 0` (implied by an elasticity of `λ`
with respect to `1 + i` of at most one). Under them the successor of `Π ∈ [β, Π*)` lies in
`[β, Π]`. -/
theorem step45_down_gen {β Pis x y : ℝ} {lam φ : ℝ → ℝ} (hβ : 0 < β)
    (hlam : ∀ j, 0 ≤ j → 0 < lam j) (hsm : StrictMonoOn (fun x => x / lam (φ x)) (Set.Ioi 0))
    (hgrow : ∀ j, 0 ≤ j → lam j ≤ (1 + j) * lam 0) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hφβ : φ β = 0) (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hx : β ≤ x)
    (hxP : x < Pis) (hy : 0 < y) (heq : y / lam (φ y) = β * (1 + φ x) / lam (φ x)) :
    β ≤ y ∧ y ≤ x := by
  have hx0 : 0 < x := by linarith
  have hφx := hφ0 x hx0
  have hlx := hlam _ hφx
  have hlam0 := hlam 0 le_rfl
  have hdown := map46_step_down hβ hφ0 hφβ hbelow hx hxP
  have hR : β / lam 0 ≤ β * (1 + φ x) / lam (φ x) := by
    rw [div_le_div_iff₀ hlam0 hlx]
    have := hgrow _ hφx
    nlinarith
  constructor
  · by_contra hcon
    push Not at hcon
    have h1 : y / lam (φ y) < β / lam (φ β) := hsm hy hβ hcon
    rw [hφβ, heq] at h1
    linarith
  · by_contra hcon
    push Not at hcon
    have h1 : x / lam (φ x) < y / lam (φ y) := hsm hx0 hy hcon
    rw [heq] at h1
    have h2 : β * (1 + φ x) / lam (φ x) ≤ x / lam (φ x) :=
      div_le_div_of_nonneg_right hdown.2 hlx.le
    linarith

/-- Woodford (2003), p. 127 and fn. 61, the "not too strongly increasing" variant of the
self-fulfilling deflation result for (4.5): with `λ > 0` continuous on `[0, ∞)`, `φ ≥ 0`
continuous, `φ(β) = 0`, `φ(Π) < β⁻¹Π − 1` on `(β, Π*)`, and the conditions (H1), (H2) of
`step45_down_gen` (no monotonicity of `λ` assumed), every solution of (4.5) starting in
`(β, Π*)` is nonincreasing, stays in `[β, Π₀]` and converges to `β`. -/
theorem self_fulfilling_deflation45_gen {β Pis : ℝ} {lam φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hβ : 0 < β) (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hsm : StrictMonoOn (fun x => x / lam (φ x)) (Set.Ioi 0))
    (hgrow : ∀ j, 0 ≤ j → lam j ≤ (1 + j) * lam 0) (hlamc : ContinuousOn lam (Set.Ici 0))
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hpath : IsPath45 β lam φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) :
    Antitone Pi_ ∧ (∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0) ∧ Tendsto Pi_ atTop (𝓝 β) := by
  have hstep : ∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0 ∧ Pi_ (t + 1) ≤ Pi_ t := by
    intro t
    induction t with
    | zero =>
      have := step45_down_gen hβ hlam hsm hgrow hφ0 hφβ hbelow h0.1.le h0.2 (hpath.1 1)
        (hpath.2 0)
      exact ⟨h0.1.le, le_rfl, this.2⟩
    | succ n ih =>
      have h1 := step45_down_gen hβ hlam hsm hgrow hφ0 hφβ hbelow ih.1
        (by linarith [h0.2, ih.2.1]) (hpath.1 (n + 1)) (hpath.2 n)
      have hle : Pi_ (n + 1) ≤ Pi_ 0 := le_trans ih.2.2 ih.2.1
      have h2 := step45_down_gen hβ hlam hsm hgrow hφ0 hφβ hbelow h1.1
        (by linarith [h0.2]) (hpath.1 (n + 1 + 1)) (hpath.2 (n + 1))
      exact ⟨h1.1, hle, h2.2⟩
  have hanti' : Antitone Pi_ := antitone_nat_of_succ_le fun t => (hstep t).2.2
  refine ⟨hanti', fun t => ⟨(hstep t).1, (hstep t).2.1⟩, ?_⟩
  have hbdd : BddBelow (Set.range Pi_) := ⟨β, by rintro _ ⟨t, rfl⟩; exact (hstep t).1⟩
  have hlim := tendsto_atTop_ciInf hanti' hbdd
  set L := ⨅ t, Pi_ t with hL
  have hLβ : β ≤ L := le_ciInf fun t => (hstep t).1
  have hL0 : L ≤ Pi_ 0 := ciInf_le hbdd 0
  have hLpos : 0 < L := by linarith
  have hlc : ContinuousOn (fun x => lam (φ x)) (Set.Ioi 0) :=
    hlamc.comp hcont fun x hx => Set.mem_Ici.mpr (hφ0 x hx)
  have hlcL : ContinuousAt (fun x => lam (φ x)) L := hlc.continuousAt (Ioi_mem_nhds hLpos)
  have hφcL : ContinuousAt φ L := hcont.continuousAt (Ioi_mem_nhds hLpos)
  have hlL := hlam _ (hφ0 L hLpos)
  have hhc : ContinuousAt (fun x => x / lam (φ x)) L := continuousAt_id.div hlcL hlL.ne'
  have hRc : ContinuousAt (fun x => β * (1 + φ x) / lam (φ x)) L :=
    (continuousAt_const.mul (continuousAt_const.add hφcL)).div hlcL hlL.ne'
  have hA : Tendsto (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) atTop
      (𝓝 (L / lam (φ L))) :=
    hhc.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have hB : Tendsto (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) atTop
      (𝓝 (β * (1 + φ L) / lam (φ L))) := by
    have : (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) =
        (fun x => β * (1 + φ x) / lam (φ x)) ∘ Pi_ := funext fun t => hpath.2 t
    rw [this]
    exact hRc.tendsto.comp hlim
  have hfix : map46 β φ L = L := (steady_state45_iff hlL).mp (tendsto_nhds_unique hA hB)
  rcases hLβ.lt_or_eq with hlt | heq
  · exfalso
    have h := hbelow L hlt (by linarith [h0.2])
    have : β * φ L < β * (L / β - 1) := mul_lt_mul_of_pos_left h hβ
    rw [mul_sub, mul_div_cancel₀ L hβ.ne'] at this
    simp only [map46] at hfix
    linarith
  · rw [← heq] at hlim; exact hlim

/-- Woodford (2003), p. 127 and fn. 61 (existence part of the "not too strongly increasing"
variant): under (H2) and continuity, every `Π₀ ∈ (β, Π*)` starts a solution of (4.5) (unique
under (H1), by `isPath45_unique`). -/
theorem deflation45_exists_gen {β Pis : ℝ} {lam φ : ℝ → ℝ} (hβ : 0 < β)
    (hlam : ∀ j, 0 ≤ j → 0 < lam j) (hgrow : ∀ j, 0 ≤ j → lam j ≤ (1 + j) * lam 0)
    (hlamc : ContinuousOn lam (Set.Ici 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) {Pi0 : ℝ} (h0 : Pi0 ∈ Set.Ioo β Pis) :
    ∃ Pi_ : ℕ → ℝ, IsPath45 β lam φ Pi_ ∧ Pi_ 0 = Pi0 := by
  have hlc : ContinuousOn (fun x => lam (φ x)) (Set.Ioi 0) :=
    hlamc.comp hcont fun x hx => Set.mem_Ici.mpr (hφ0 x hx)
  have hsucc : ∀ x : ℝ, ∃ y : ℝ, x ∈ Set.Ico β Pis →
      y ∈ Set.Icc β x ∧ y / lam (φ y) = β * (1 + φ x) / lam (φ x) := by
    intro x
    by_cases hx : x ∈ Set.Ico β Pis
    · have hx0 : 0 < x := by linarith [hx.1]
      have hφx := hφ0 x hx0
      have hlx := hlam _ hφx
      have hlam0 := hlam 0 le_rfl
      have hdown := map46_step_down hβ hφ0 hφβ hbelow hx.1 hx.2
      have hcI : ContinuousOn (fun z => z / lam (φ z)) (Set.Icc β x) := by
        refine continuousOn_id.div (hlc.mono fun z hz => (by linarith [hz.1] : (0 : ℝ) < z))
          fun z hz => (hlam _ (hφ0 z (by linarith [hz.1]))).ne'
      have hlo : β / lam (φ β) ≤ β * (1 + φ x) / lam (φ x) := by
        rw [hφβ, div_le_div_iff₀ hlam0 hlx]
        have := hgrow _ hφx
        nlinarith
      have hhi : β * (1 + φ x) / lam (φ x) ≤ x / lam (φ x) :=
        div_le_div_of_nonneg_right hdown.2 hlx.le
      obtain ⟨y, hy, hyeq⟩ := intermediate_value_Icc hx.1 hcI ⟨hlo, hhi⟩
      exact ⟨y, fun _ => ⟨hy, hyeq⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose g hg using hsucc
  set Pi_ : ℕ → ℝ := fun t => g^[t] Pi0 with hPi
  have hsuccP : ∀ t, Pi_ (t + 1) = g (Pi_ t) := fun t => Function.iterate_succ_apply' _ _ _
  have hmem : ∀ t, Pi_ t ∈ Set.Ico β Pis := by
    intro t
    induction t with
    | zero => exact ⟨h0.1.le, h0.2⟩
    | succ n ih =>
      rw [hsuccP]
      have := (hg _ ih).1
      exact ⟨this.1, lt_of_le_of_lt this.2 ih.2⟩
  refine ⟨Pi_, ⟨fun t => by linarith [(hmem t).1], fun t => ?_⟩, rfl⟩
  rw [hsuccP]
  exact (hg _ (hmem t)).2

/-- Woodford (2003), p. 127: the case `u_cm > 0` (`λ` nonincreasing, `φ` nondecreasing) satisfies
the conditions (H1), (H2) of the general variant. -/
theorem antitone_lam_gives_gen {lam φ : ℝ → ℝ} (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hanti : AntitoneOn lam (Set.Ici 0)) (hmono : MonotoneOn φ (Set.Ioi 0))
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) :
    StrictMonoOn (fun x => x / lam (φ x)) (Set.Ioi 0) ∧
      ∀ j, 0 ≤ j → lam j ≤ (1 + j) * lam 0 := by
  refine ⟨ratio_strictMonoOn hlam hanti hmono hφ0, fun j hj => ?_⟩
  have h1 : lam j ≤ lam 0 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hj) hj
  nlinarith [hlam 0 le_rfl]

/-- Woodford (2003), p. 127: the policy rule of the counterexample showing that some restriction
on how strongly `λ` increases is needed: `φ(Π) = max(0, 3Π − 2)` (`β = 1/2`, `Π* = 1`). -/
noncomputable def phiCE45 (x : ℝ) : ℝ := max 0 (3 * x - 2)

/-- Woodford (2003), p. 127, "it suffices that `λ` not be too strongly increasing": some such
restriction is needed. With `β = 1/2`, `Π* = 1`, `φ = phiCE45` (continuous, nondecreasing,
`≥ 0`, `φ(β) = 0`, `φ(Π) < β⁻¹Π − 1` on `(β, Π*)`, `φ(Π*) = β⁻¹Π* − 1`) and the increasing
`λ(i) = 1 + i` (positive, continuous, satisfying (H2) with equality), `Π/λ(φ(Π))` is not
increasing (it takes the value `1/2` at both `β` and `Π*`), and the path `Π₀ = 3/5 ∈ (β, Π*)`,
`Π_t = 1` for `t ≥ 1` solves (4.5) but does not converge to `β` (it is not a self-fulfilling
deflation). -/
theorem deflation45_counterexample :
    Continuous phiCE45 ∧ Monotone phiCE45 ∧ (∀ x, 0 ≤ phiCE45 x) ∧ phiCE45 (1 / 2) = 0 ∧
      (∀ x, 1 / 2 < x → x < 1 → phiCE45 x < x / (1 / 2) - 1) ∧
      phiCE45 1 = 1 / (1 / 2) - 1 ∧
      (∀ j : ℝ, 0 ≤ j → 0 < 1 + j ∧ 1 + j ≤ (1 + j) * (1 + 0)) ∧
      (1 / 2) / (1 + phiCE45 (1 / 2)) = 1 / (1 + phiCE45 1) ∧
      IsPath45 (1 / 2) (fun i => 1 + i) phiCE45 (fun t => if t = 0 then 3 / 5 else 1) ∧
      ¬ Tendsto (fun t : ℕ => if t = 0 then (3 / 5 : ℝ) else 1) atTop (𝓝 (1 / 2)) := by
  have h35 : phiCE45 (3 / 5) = 0 := by unfold phiCE45; norm_num
  have h1 : phiCE45 1 = 1 := by unfold phiCE45; norm_num
  refine ⟨by unfold phiCE45; fun_prop, fun a b hab => max_le_max le_rfl (by linarith),
    fun x => le_max_left _ _, by unfold phiCE45; norm_num, fun x hx1 hx2 => ?_,
    by rw [h1]; norm_num,
    fun j hj => ⟨by linarith, by linarith⟩, by unfold phiCE45; norm_num,
    ⟨fun t => by
      change (0 : ℝ) < if t = 0 then 3 / 5 else 1
      split_ifs <;> norm_num, fun t => ?_⟩, ?_⟩
  · unfold phiCE45
    exact max_lt (by linarith) (by linarith)
  · rcases t with _ | t
    · norm_num [h1, h35]
    · norm_num [h1]
  · intro h
    have h2 : Tendsto (fun t : ℕ => if t = 0 then (3 / 5 : ℝ) else 1) atTop (𝓝 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with t ht
      have ht' : t ≠ 0 := by omega
      simp [ht']
    have := tendsto_nhds_unique h h2
    norm_num at this

/-- Woodford (2003), (4.4), p. 124, path-wise version: if along the interest path `λ(i_T) ≤ Λ`,
`L(i_T) ≥ 0` and `i_T L(i_T) ≤ K`, the series in (4.4) has nonnegative terms and converges. -/
theorem bound44_summable_path {β ybar Λ K : ℝ} {lam L : ℝ → ℝ} {i : ℕ → ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hy : 0 ≤ ybar) (hi : ∀ T, 0 ≤ i T) (hlam0 : ∀ T, 0 < lam (i T))
    (hlamΛ : ∀ T, lam (i T) ≤ Λ) (hL0 : ∀ T, 0 ≤ L (i T)) (hLK : ∀ T, i T * L (i T) ≤ K) :
    Summable (bound44Term β ybar lam L i) := by
  have hterm : ∀ T, 0 ≤ i T / (1 + i T) * L (i T) ∧ i T / (1 + i T) * L (i T) ≤ K := by
    intro T
    have h1 : 0 < 1 + i T := by linarith [hi T]
    refine ⟨mul_nonneg (div_nonneg (hi T) h1.le) (hL0 T), ?_⟩
    have : i T / (1 + i T) * L (i T) ≤ i T * L (i T) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h1]
      nlinarith [mul_nonneg (mul_nonneg (hi T) (hL0 T)) (hi T)]
    linarith [hLK T]
  have hnn : ∀ T, 0 ≤ bound44Term β ybar lam L i T := by
    intro T
    unfold bound44Term
    have := (hterm T).1
    have := (hlam0 T).le
    positivity
  refine Summable.of_nonneg_of_le hnn (fun T => ?_)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (Λ * (ybar + K)))
  unfold bound44Term
  have hb : 0 ≤ β ^ T := pow_nonneg hβ0 T
  have h2 : lam (i T) * (ybar + i T / (1 + i T) * L (i T)) ≤ Λ * (ybar + K) := by
    have h3 := (hterm T).2
    have h4 := (hterm T).1
    have h5 := (hlam0 T).le
    calc lam (i T) * (ybar + i T / (1 + i T) * L (i T)) ≤ lam (i T) * (ybar + K) := by
          gcongr
      _ ≤ Λ * (ybar + K) := mul_le_mul_of_nonneg_right (hlamΛ T) (by linarith)
  exact mul_le_mul_of_nonneg_left h2 hb

/-- Woodford (2003), pp. 127–128, "these solutions also satisfy (4.4), and hence represent
perfect-foresight equilibria, as long as … `iL(ȳ, i; 0)` has a finite bound for `i` near zero",
with no bound on `λ` assumed: along any self-fulfilling deflation of (4.5) (hypotheses of
`self_fulfilling_deflation45_gen`, plus `φ` nondecreasing) the interest rate stays in
`[0, φ(Π₀)]`, so `λ`, continuous on `[0, ∞)`, is bounded along the path; if moreover `L ≥ 0` and
`iL(i)` is bounded on bounded sets of `i ≥ 0`, (4.4) holds. -/
theorem deflation45_bound44_gen {β Pis ybar : ℝ} {lam φ L : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hy : 0 ≤ ybar) (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hsm : StrictMonoOn (fun x => x / lam (φ x)) (Set.Ioi 0))
    (hgrow : ∀ j, 0 ≤ j → lam j ≤ (1 + j) * lam 0) (hlamc : ContinuousOn lam (Set.Ici 0))
    (hmono : MonotoneOn φ (Set.Ioi 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hL0 : ∀ j, 0 ≤ j → 0 ≤ L j)
    (hLK : ∀ b, ∃ K, ∀ j, 0 ≤ j → j ≤ b → j * L j ≤ K) (hpath : IsPath45 β lam φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) :
    Summable (bound44Term β ybar lam L (fun t => φ (Pi_ t))) := by
  have hd := self_fulfilling_deflation45_gen hβ hlam hsm hgrow hlamc hφ0 hcont hφβ hbelow
    hpath h0
  set b := φ (Pi_ 0) with hb
  have hi : ∀ T, 0 ≤ φ (Pi_ T) ∧ φ (Pi_ T) ≤ b := fun T =>
    ⟨hφ0 _ (hpath.1 T), hmono (hpath.1 T) (hpath.1 0) (hd.2.1 T).2⟩
  obtain ⟨Λ, hΛ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn
    (hlamc.mono fun z hz => Set.mem_Ici.mpr hz.1)
  obtain ⟨K, hK⟩ := hLK b
  refine bound44_summable_path (Λ := Λ) (K := K) hβ.le hβ1 hy (fun T => (hi T).1)
    (fun T => hlam _ (hi T).1) (fun T => ?_) (fun T => hL0 _ (hi T).1)
    (fun T => hK _ (hi T).1 (hi T).2)
  have := hΛ _ ⟨(hi T).1, (hi T).2⟩
  rw [Real.norm_eq_abs] at this
  exact le_trans (le_abs_self _) this

end Woodford.PriceLevelDetermination.GlobalDynamics
