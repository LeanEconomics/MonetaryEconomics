/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.ForwardSolution
import ZeroBound.GlobalDynamics
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.IntermediateValue

/-!
# An active rule that hits the zero bound

Cochrane (2023), Chapter 20, §20.2.1 "Removing sunspots?", pp. 471–474, and Figure 20.3.

The static-IS model of §16.1, `x_t = −σ(i_t − E_tπ_{t+1} − u_{r,t})`, `π_t = E_tπ_{t+1} + κx_t`,
with the kinked rule (20.1) `i_t = max[π* + φ(π_t − π*), 0]`, for an arbitrary
`ExpectationSystem`.

## Main results

* (20.2): `eq20_2_iff`; in map form `E_tπ_{t+1} = f_u(π_t)`, `eq20_2_iff_map`, with
  `f_u(π) = (π + σκ·max[π* + φ(π − π*), 0] − σκu)/(1 + σκ)` (`fmap`).
* (20.3)/(20.4) with the CORRECTED kink (survey E1, confirmed): the zero-bound branch applies iff
  `π ≤ π*(φ − 1)/φ` (`kink_iff`, `eq20_3`, `eq20_4`); the printed threshold `π* + (φ − 1)` is
  false (`e1_printed_threshold_false`: at the Figure 20.3 values `π = 1.5 < 3` but (20.3) fails).
* The map: continuous, strictly increasing, onto (`fmap_continuous`, `fmap_strictMono`,
  `fmap_surjective`), with slopes `1/(1 + σκ) < 1` and `(1 + φσκ)/(1 + σκ)`, `> 1 ↔ φ > 1`
  (`hasDerivAt_fmap_left`, `hasDerivAt_fmap_right`, `slope_left_lt_one`, `slope_right_gt_one_iff`).
* Steady states (p. 472): `fixed_iff`, `steady_exists_iff` (a steady state exists iff
  `−u ≤ π*(φ − 1)/φ`, then `−u` and `π* + u/(φ − 1)` are the steady states), `fixed_u_zero` (with
  `u = 0`: exactly `0` and `π*`), `steady_states_pushed_in`, `lower_attracting`, `upper_repelling`.
  Survey E2, confirmed: at the Figure 20.3 calibration there is NO steady state during the shock,
  `f_u(π) − π ≥ 1/3` for all `π` (`fig203_no_steady_state`, `fig203_printed_steady_states_false`).
* Global vs local (pp. 473–474), `u = 0`: orbits starting above `π*` explode
  (`orbit_above`), orbits starting below converge to zero inflation and zero rates
  (`orbit_below_tendsto_zero`, `orbit_below_rate_zero`),
  so the bounded orbits are exactly those with `π₀ ≤ π*` (`bounded_orbits_eq`), a continuum,
  while `π*` is the only locally bounded one (`locally_bounded_unique`), also under any
  `ExpectationSystem` (`locally_bounded_unique_E`).
* Figure 20.3 (pp. 472–473): selection by the future rule. `backward_unique`,
  `backward_exists` (for any `ExpectationSystem` the path before `T` is pinned and
  deterministic once `π_T` is), `fig203_selection` (`π_t = π*` for `t ≥ T`, and
  `π₉ = 3/2, π₈ = 9/8, π₇ = 11/16, π₆ = 1/32`), and survey E3, confirmed: the rate lifts off two
  periods before `T`, `i₉ = 1`, `i₈ = 1/4` (`fig203_early_liftoff`). Forward contraction on the
  zero-bound branch and expansion on the active branch (`zlb_branch_contraction`,
  `active_branch_expansion`).
-/

namespace Cochrane.ZeroBound.ZLBRule

open Filter Topology
open Cochrane.ZeroBound

/-- Cochrane (2023), eq. (20.1), p. 472: the rule `i = max[π* + φ(π − π*), 0]`. -/
noncomputable def rule (φ πs π : ℝ) : ℝ := max (πs + φ * (π - πs)) 0

/-- Cochrane (2023), eq. (20.2), p. 472, solved for expected inflation:
`E_tπ_{t+1} = (π_t + σκ i(π_t) − σκu_t)/(1 + σκ)`. -/
noncomputable def fmap (σ κ φ πs u : ℝ) (π : ℝ) : ℝ :=
  (π + σ * κ * rule φ πs π - σ * κ * u) / (1 + σ * κ)

/-- Cochrane (2023), eqs. (20.3)–(20.4), p. 472 (corrected, survey E1): the kink of the map,
`π*(φ − 1)/φ`, where `π* + φ(π − π*) = 0`. -/
noncomputable def kink (φ πs : ℝ) : ℝ := πs * (φ - 1) / φ

/-- Cochrane (2023), eq. (20.4), p. 472: the slope `(1 + φσκ)/(1 + σκ)` of the active branch. -/
noncomputable def slopeR (σ κ φ : ℝ) : ℝ := (1 + φ * (σ * κ)) / (1 + σ * κ)

/-! ## The model and (20.2) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §20.2.1, p. 471 and eq. (20.1), p. 472: `i_t = max[π* + φ(π_t − π*), 0]`,
`x_t = −σ(i_t − E_tπ_{t+1} − u_{r,t})`, `π_t = E_tπ_{t+1} + κx_t`, at every date and state. -/
def ZLBEq (σ κ φ πs : ℝ) (u x π i : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, i t ω = rule φ πs (π t ω) ∧
    x t ω = -σ * (i t ω - 𝔼.E t (π (t + 1)) ω - u t ω) ∧
    π t ω = 𝔼.E t (π (t + 1)) ω + κ * x t ω

/-- Cochrane (2023), eq. (20.2), p. 472: eliminating `x`, the model is
`max[π* + φ(π_t − π*), 0] = −π_t/(σκ) + ((1 + σκ)/(σκ))E_tπ_{t+1} + u_{r,t}` (with
`x_t = (π_t − E_tπ_{t+1})/κ`). -/
theorem eq20_2_iff {σ κ φ πs : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (u x π i : ℕ → Ω → ℝ) :
    ZLBEq 𝔼 σ κ φ πs u x π i ↔ ∀ t ω, i t ω = rule φ πs (π t ω) ∧
      x t ω = (π t ω - 𝔼.E t (π (t + 1)) ω) / κ ∧
      rule φ πs (π t ω) = -(1 / (σ * κ)) * π t ω +
        ((1 + σ * κ) / (σ * κ)) * 𝔼.E t (π (t + 1)) ω + u t ω := by
  have hs : σ * κ ≠ 0 := mul_ne_zero hσ hκ
  have e : ∀ a b c : ℝ, -(1 / (σ * κ)) * a + ((1 + σ * κ) / (σ * κ)) * b + c =
      (-a + (1 + σ * κ) * b + σ * κ * c) / (σ * κ) := fun a b c => by
    field_simp
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  rw [e, eq_div_iff hs]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hx : x t ω = (π t ω - 𝔼.E t (π (t + 1)) ω) / κ := by
      field_simp
      linarith
    refine ⟨h1, hx, ?_⟩
    rw [← h1]
    linear_combination h3 + κ * h2
  · rintro ⟨h1, h2, h3⟩
    have h2' : κ * x t ω = π t ω - 𝔼.E t (π (t + 1)) ω := by
      rw [h2]
      field_simp
    refine ⟨h1, ?_, by linarith⟩
    rw [← h1] at h3
    apply mul_left_cancel₀ hκ
    linear_combination h2' + h3

/-- Cochrane (2023), eq. (20.2), p. 472: in map form, the model is
`E_tπ_{t+1} = f_{u_t}(π_t)` together with the rule and `x_t = (π_t − E_tπ_{t+1})/κ`. -/
theorem eq20_2_iff_map {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (u x π i : ℕ → Ω → ℝ) :
    ZLBEq 𝔼 σ κ φ πs u x π i ↔ ∀ t ω, i t ω = rule φ πs (π t ω) ∧
      x t ω = (π t ω - 𝔼.E t (π (t + 1)) ω) / κ ∧
      𝔼.E t (π (t + 1)) ω = fmap σ κ φ πs (u t ω) (π t ω) := by
  have hσ : σ ≠ 0 := by rintro rfl; simp at hσκ
  have hκ : κ ≠ 0 := by rintro rfl; simp at hσκ
  rw [eq20_2_iff 𝔼 hσ hκ]
  refine forall_congr' fun t => forall_congr' fun ω => and_congr_right fun _ =>
    and_congr_right fun _ => ?_
  unfold fmap
  have h1 : (1 + σ * κ) ≠ 0 := by linarith
  constructor
  · intro h
    field_simp
    field_simp at h
    linarith
  · intro h
    field_simp at h
    field_simp
    linarith

/-! ## The branches (20.3)–(20.4) and survey error E1 -/

/-- Cochrane (2023), eqs. (20.3)–(20.4), p. 472 (survey E1): for `φ > 0` the rule is at the
bound, `π* + φ(π − π*) ≤ 0`, iff `π ≤ π*(φ − 1)/φ`. -/
theorem kink_iff {φ πs π : ℝ} (hφ : 0 < φ) : πs + φ * (π - πs) ≤ 0 ↔ π ≤ kink φ πs := by
  unfold kink
  rw [le_div_iff₀ hφ]
  constructor <;> intro h <;> nlinarith

/-- Cochrane (2023), eq. (20.3), p. 472: on the zero-bound branch
`E_tπ_{t+1} = π_t/(1 + σκ) − σκu/(1 + σκ)`. -/
theorem eq20_3 {σ κ φ πs u π : ℝ} (h : πs + φ * (π - πs) ≤ 0) :
    fmap σ κ φ πs u π = 1 / (1 + σ * κ) * π - σ * κ / (1 + σ * κ) * u := by
  unfold fmap rule
  rw [max_eq_right h]
  ring

/-- Cochrane (2023), eq. (20.4), p. 472: on the active branch
`E_tπ_{t+1} − π* = ((1 + φσκ)/(1 + σκ))(π_t − π*) − σκu/(1 + σκ)`. -/
theorem eq20_4 {σ κ φ πs u π : ℝ} (hσκ : 0 < σ * κ) (h : 0 ≤ πs + φ * (π - πs)) :
    fmap σ κ φ πs u π - πs = slopeR σ κ φ * (π - πs) - σ * κ / (1 + σ * κ) * u := by
  unfold fmap rule slopeR
  rw [max_eq_left h]
  have : (1 + σ * κ) ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), Figure 20.3 values (`φ = 2`, `π* = 2`): the true kink is `1`, while the
printed threshold `π* + (φ − 1)` is `3`. -/
theorem kink_fig203 : kink 2 2 = 1 ∧ (2 : ℝ) + (2 - 1) = 3 := by
  unfold kink
  norm_num

/-- Cochrane (2023), eq. (20.3), p. 472, survey error E1: the printed side condition
"(20.3) when `π_t < π* + (φ − 1)`" is false. At the Figure 20.3 values (`σ = 1`, `κ = 1/2`,
`φ = 2`, `π* = 2`, `u = 0`), `π = 3/2 < 3` but `E_tπ_{t+1} = 4/3 ≠ 1`, the (20.3) value. -/
theorem e1_printed_threshold_false :
    (3 / 2 : ℝ) < 2 + (2 - 1) ∧ fmap 1 (1 / 2) 2 2 0 (3 / 2) = 4 / 3 ∧
      fmap 1 (1 / 2) 2 2 0 (3 / 2) ≠
        1 / (1 + 1 * (1 / 2)) * (3 / 2) - 1 * (1 / 2) / (1 + 1 * (1 / 2)) * 0 := by
  have h : fmap 1 (1 / 2) 2 2 0 (3 / 2) = 4 / 3 := by
    unfold fmap rule
    rw [max_eq_left (by norm_num)]
    norm_num
  refine ⟨by norm_num, h, ?_⟩
  rw [h]
  norm_num

/-! ## Properties of the map -/

/-- Cochrane (2023), eq. (20.2), p. 472: the map `f_u` is continuous. -/
theorem fmap_continuous (σ κ φ πs u : ℝ) : Continuous (fmap σ κ φ πs u) := by
  unfold fmap rule
  fun_prop

/-- Cochrane (2023), eq. (20.2), p. 472: for `φ ≥ 0` and `σκ > 0` the map is strictly
increasing (both slopes positive). -/
theorem fmap_strictMono {σ κ φ πs u : ℝ} (hφ : 0 ≤ φ) (hσκ : 0 < σ * κ) :
    StrictMono (fmap σ κ φ πs u) := by
  intro a b hab
  unfold fmap
  have hr : rule φ πs a ≤ rule φ πs b := by
    unfold rule
    exact max_le_max (by nlinarith) le_rfl
  apply div_lt_div_of_pos_right _ (by linarith)
  nlinarith

/-- Cochrane (2023), eq. (20.2), p. 472: the map is onto, so every `E_tπ_{t+1}` is reached
by exactly one `π_t` (with `fmap_strictMono`). -/
theorem fmap_surjective {σ κ φ πs u : ℝ} (hφ : 0 ≤ φ) (hσκ : 0 < σ * κ) :
    Function.Surjective (fmap σ κ φ πs u) := by
  intro y
  set s := σ * κ
  set R := max πs 0
  set b := (1 + s) * y + s * u
  set a := min πs (b - s * R)
  have hab : a ≤ b := by
    have : 0 ≤ s * R := mul_nonneg hσκ.le (le_max_right _ _)
    exact (min_le_right _ _).trans (by linarith)
  have hfa : fmap σ κ φ πs u a ≤ y := by
    unfold fmap
    have hra : rule φ πs a ≤ R := by
      unfold rule
      refine max_le_max ?_ le_rfl
      have : a ≤ πs := min_le_left _ _
      nlinarith
    have : a ≤ b - s * R := min_le_right _ _
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hfb : y ≤ fmap σ κ φ πs u b := by
    unfold fmap
    have : 0 ≤ rule φ πs b := le_max_right _ _
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  obtain ⟨c, -, hc⟩ :=
    intermediate_value_Icc hab (fmap_continuous σ κ φ πs u).continuousOn ⟨hfa, hfb⟩
  exact ⟨c, hc⟩

/-- Cochrane (2023), eq. (20.3), p. 472: left of the kink the map has slope `1/(1 + σκ)`. -/
theorem hasDerivAt_fmap_left {σ κ φ πs u π : ℝ} (hφ : 0 < φ) (h : π < kink φ πs) :
    HasDerivAt (fmap σ κ φ πs u) (1 / (1 + σ * κ)) π := by
  have hd : HasDerivAt (fun y => 1 / (1 + σ * κ) * y - σ * κ / (1 + σ * κ) * u)
      (1 / (1 + σ * κ)) π := by
    simpa using ((hasDerivAt_id' π).const_mul (1 / (1 + σ * κ))).sub_const
      (σ * κ / (1 + σ * κ) * u)
  refine hd.congr_of_eventuallyEq (Filter.eventually_of_mem (Iio_mem_nhds h) fun y hy => ?_)
  exact eq20_3 ((kink_iff hφ).mpr (le_of_lt hy))

/-- Cochrane (2023), eq. (20.4), p. 472: right of the kink the map has slope
`(1 + φσκ)/(1 + σκ)`. -/
theorem hasDerivAt_fmap_right {σ κ φ πs u π : ℝ} (hφ : 0 < φ) (hσκ : 0 < σ * κ)
    (h : kink φ πs < π) : HasDerivAt (fmap σ κ φ πs u) (slopeR σ κ φ) π := by
  have hd : HasDerivAt (fun y => πs + slopeR σ κ φ * (y - πs) - σ * κ / (1 + σ * κ) * u)
      (slopeR σ κ φ) π := by
    simpa using (((hasDerivAt_id' π).sub_const πs).const_mul (slopeR σ κ φ)).const_add
      πs |>.sub_const (σ * κ / (1 + σ * κ) * u)
  refine hd.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioi_mem_nhds h) fun y hy => ?_)
  have hy' : 0 ≤ πs + φ * (y - πs) := by
    by_contra hc
    push Not at hc
    have := (kink_iff hφ).mp hc.le
    exact absurd hy (not_lt.mpr this)
  have := eq20_4 (u := u) hσκ hy'
  simp only
  linarith

/-- Cochrane (2023), p. 472 ("slope less than one"): `1/(1 + σκ) < 1`. -/
theorem slope_left_lt_one {σ κ : ℝ} (hσκ : 0 < σ * κ) : 1 / (1 + σ * κ) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

/-- Cochrane (2023), p. 472 ("slope greater than one"): `(1 + φσκ)/(1 + σκ) > 1 ↔ φ > 1`. -/
theorem slope_right_gt_one_iff {σ κ φ : ℝ} (hσκ : 0 < σ * κ) : 1 < slopeR σ κ φ ↔ 1 < φ := by
  unfold slopeR
  rw [one_lt_div (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- Cochrane (2023), eq. (20.4), p. 472: at or above the kink the rule is not at the bound. -/
theorem active_of_kink_le {φ πs π : ℝ} (hφ : 0 < φ) (h : kink φ πs ≤ π) :
    0 ≤ πs + φ * (π - πs) := by
  unfold kink at h
  rw [div_le_iff₀ hφ] at h
  nlinarith

/-- Cochrane (2023), §20.2.1, p. 473 ("converging as time goes forward"): two points on the
zero-bound branch are brought closer, `|f(x) − f(y)| = |x − y|/(1 + σκ)`. -/
theorem zlb_branch_contraction {σ κ φ πs u x y : ℝ} (hσκ : 0 < σ * κ) (hφ : 0 < φ)
    (hx : x ≤ kink φ πs) (hy : y ≤ kink φ πs) :
    |fmap σ κ φ πs u x - fmap σ κ φ πs u y| = |x - y| / (1 + σ * κ) := by
  rw [eq20_3 ((kink_iff hφ).mpr hx), eq20_3 ((kink_iff hφ).mpr hy)]
  rw [show 1 / (1 + σ * κ) * x - σ * κ / (1 + σ * κ) * u -
      (1 / (1 + σ * κ) * y - σ * κ / (1 + σ * κ) * u) = (x - y) / (1 + σ * κ) by ring,
    abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + σ * κ)]

/-- Cochrane (2023), §20.2.1, p. 472 ("alternative equilibria diverge"): two points on the
active branch are pushed apart, `|f(x) − f(y)| = ((1 + φσκ)/(1 + σκ))|x − y|`. -/
theorem active_branch_expansion {σ κ φ πs u x y : ℝ} (hσκ : 0 < σ * κ) (hφ : 0 < φ)
    (hx : kink φ πs ≤ x) (hy : kink φ πs ≤ y) :
    |fmap σ κ φ πs u x - fmap σ κ φ πs u y| = slopeR σ κ φ * |x - y| := by
  have h1 := active_of_kink_le hφ hx
  have h2 := active_of_kink_le hφ hy
  have ex := eq20_4 (u := u) hσκ h1
  have ey := eq20_4 (u := u) hσκ h2
  have hpos : 0 < slopeR σ κ φ := by
    unfold slopeR
    apply div_pos _ (by linarith)
    nlinarith
  rw [show fmap σ κ φ πs u x - fmap σ κ φ πs u y = slopeR σ κ φ * (x - y) by linarith,
    abs_mul, abs_of_pos hpos]

/-! ## Steady states (p. 472) and survey error E2 -/

/-- Cochrane (2023), p. 472: the steady states of `f_u` (for `φ > 1`, `σκ > 0`) are `−u`, when
it lies on the zero-bound branch, and `π* + u/(φ − 1)`, when it lies on the active branch. -/
theorem fixed_iff {σ κ φ πs u π : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) :
    fmap σ κ φ πs u π = π ↔ (π = -u ∧ -u ≤ kink φ πs) ∨
      (π = πs + u / (φ - 1) ∧ kink φ πs ≤ πs + u / (φ - 1)) := by
  have hφ0 : 0 < φ := by linarith
  have hφ1 : φ - 1 ≠ 0 := by linarith
  have hs1 : (1 + σ * κ) ≠ 0 := by linarith
  have hσκ' : σ * κ ≠ 0 := hσκ.ne'
  constructor
  · intro h
    by_cases hk : π ≤ kink φ πs
    · rw [eq20_3 ((kink_iff hφ0).mpr hk)] at h
      field_simp at h
      have : π = -u := by
        apply mul_left_cancel₀ hσκ'
        linarith
      exact Or.inl ⟨this, this ▸ hk⟩
    · push Not at hk
      have := eq20_4 (u := u) hσκ (active_of_kink_le hφ0 hk.le)
      rw [h] at this
      unfold slopeR at this
      field_simp at this
      have hp : π = πs + u / (φ - 1) := by
        field_simp
        apply mul_left_cancel₀ hσκ'
        linarith
      exact Or.inr ⟨hp, hp ▸ hk.le⟩
  · rintro (⟨rfl, hk⟩ | ⟨rfl, hk⟩)
    · rw [eq20_3 ((kink_iff hφ0).mpr hk)]
      field_simp
      ring
    · have := eq20_4 (u := u) hσκ (active_of_kink_le hφ0 hk)
      unfold slopeR at this
      have e : fmap σ κ φ πs u (πs + u / (φ - 1)) - (πs + u / (φ - 1)) = 0 := by
        rw [show fmap σ κ φ πs u (πs + u / (φ - 1)) - (πs + u / (φ - 1)) =
          (fmap σ κ φ πs u (πs + u / (φ - 1)) - πs) - u / (φ - 1) by ring, this]
        field_simp
        ring
      linarith

/-- Cochrane (2023), p. 472: the two candidate steady states lie on their branches under the
same condition: `π* + u/(φ − 1) ≥ π*(φ − 1)/φ ↔ −u ≤ π*(φ − 1)/φ`. -/
theorem upper_on_branch_iff {φ πs u : ℝ} (hφ : 1 < φ) :
    kink φ πs ≤ πs + u / (φ - 1) ↔ -u ≤ kink φ πs := by
  have hφ0 : 0 < φ := by linarith
  have hφ1 : 0 < φ - 1 := by linarith
  unfold kink
  rw [div_le_iff₀ hφ0, le_div_iff₀ hφ0]
  have e : (πs + u / (φ - 1)) * φ = πs * φ + u * φ / (φ - 1) := by ring
  rw [e]
  constructor
  · intro h
    have : πs * (φ - 1) - πs * φ ≤ u * φ / (φ - 1) := by linarith
    rw [le_div_iff₀ hφ1] at this
    nlinarith
  · intro h
    have : πs * (φ - 1) - πs * φ ≤ u * φ / (φ - 1) := by
      rw [le_div_iff₀ hφ1]
      nlinarith
    linarith

/-- Cochrane (2023), p. 472, corrected (survey E2): a steady state exists iff
`−u ≤ π*(φ − 1)/φ`; then both `−u` and `π* + u/(φ − 1)` are steady states. -/
theorem steady_exists_iff {σ κ φ πs u : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) :
    (∃ π, fmap σ κ φ πs u π = π) ↔ -u ≤ kink φ πs := by
  constructor
  · rintro ⟨π, h⟩
    rcases (fixed_iff hφ hσκ).mp h with ⟨-, hk⟩ | ⟨-, hk⟩
    · exact hk
    · exact (upper_on_branch_iff hφ).mp hk
  · intro h
    exact ⟨-u, (fixed_iff hφ hσκ).mpr (Or.inl ⟨rfl, h⟩)⟩

/-- Cochrane (2023), p. 472: when `−u ≤ π*(φ − 1)/φ`, both `−u` and `π* + u/(φ − 1)` are steady
states. -/
theorem both_steady {σ κ φ πs u : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (h : -u ≤ kink φ πs) :
    fmap σ κ φ πs u (-u) = -u ∧ fmap σ κ φ πs u (πs + u / (φ - 1)) = πs + u / (φ - 1) :=
  ⟨(fixed_iff hφ hσκ).mpr (Or.inl ⟨rfl, h⟩),
    (fixed_iff hφ hσκ).mpr (Or.inr ⟨rfl, (upper_on_branch_iff hφ).mpr h⟩)⟩

/-- Cochrane (2023), p. 472 ("with `u_{r,t} = 0`, a stable steady state at `π = 0` … and an
unstable … steady state at `π = π*`"): for `φ > 1`, `π* > 0`, the steady states are exactly
`0` and `π*`. -/
theorem fixed_u_zero {σ κ φ πs π : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hπs : 0 < πs) :
    fmap σ κ φ πs 0 π = π ↔ π = 0 ∨ π = πs := by
  have hk : 0 ≤ kink φ πs := by
    unfold kink
    apply div_nonneg _ (by linarith)
    nlinarith
  rw [fixed_iff hφ hσκ]
  simp only [neg_zero, zero_div, add_zero]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨h, hk⟩
    · refine Or.inr ⟨h, ?_⟩
      have := (upper_on_branch_iff (πs := πs) (u := 0) hφ).mpr (by simpa using hk)
      simpa using this

/-- Cochrane (2023), p. 472 ("a negative `u_{r,t}` … pushes the steady states in"): for
`u < 0` the lower steady state `−u` lies above `0` and the upper one below `π*`. -/
theorem steady_states_pushed_in {φ πs u : ℝ} (hφ : 1 < φ) (hu : u < 0) :
    0 < -u ∧ πs + u / (φ - 1) < πs := by
  refine ⟨by linarith, ?_⟩
  have : u / (φ - 1) < 0 := div_neg_of_neg_of_pos hu (by linarith)
  linarith

/-- Cochrane (2023), p. 472 ("a stable steady state … where the phase diagram has slope less
than one"): if `−u` lies strictly on the zero-bound branch, it is locally attracting. -/
theorem lower_attracting {σ κ φ πs u : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (h : -u < kink φ πs) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = fmap σ κ φ πs u (x t)) → |x 0 - -u| < δ →
      (∀ t, |x t - -u| < δ) ∧ Tendsto x atTop (𝓝 (-u)) := by
  refine GlobalDynamics.attracting_of_abs_deriv_lt_one (both_steady hφ hσκ h.le).1
    (hasDerivAt_fmap_left (by linarith) h) ?_
  rw [abs_of_pos (by apply div_pos one_pos; linarith)]
  exact slope_left_lt_one hσκ

/-- Cochrane (2023), p. 472 ("an unstable locally-determinate steady state … slope greater
than one"): if `π* + u/(φ − 1)` lies strictly on the active branch, it is repelling. -/
theorem upper_repelling {σ κ φ πs u : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ)
    (h : kink φ πs < πs + u / (φ - 1)) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = fmap σ κ φ πs u (x t)) →
      x 0 ≠ πs + u / (φ - 1) → ∃ t, δ ≤ |x t - (πs + u / (φ - 1))| := by
  refine GlobalDynamics.repelling_of_one_lt_abs_deriv
    (both_steady hφ hσκ ((upper_on_branch_iff hφ).mp h.le)).2
    (hasDerivAt_fmap_right (by linarith) hσκ h) ?_
  have := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ
  rw [abs_of_pos (by linarith)]
  exact this

/-- Cochrane (2023), p. 472, survey error E2: at the Figure 20.3 calibration (`σ = 1`,
`κ = 1/2`, `φ = 2`, `π* = 2`, `u_r = −2`) there is no steady state during the shock:
`f_u(π) − π ≥ 1/3` for every `π`. -/
theorem fig203_no_steady_state (π : ℝ) : 1 / 3 ≤ fmap 1 (1 / 2) 2 2 (-2) π - π := by
  unfold fmap rule
  rcases le_total (2 + 2 * (π - 2)) 0 with h | h
  · rw [max_eq_right h, le_sub_iff_add_le, le_div_iff₀ (by norm_num)]
    linarith
  · rw [max_eq_left h, le_sub_iff_add_le, le_div_iff₀ (by norm_num)]
    linarith

/-- Cochrane (2023), p. 472, survey error E2: the printed steady states "`π = −u_{r,t}`" and
"`π = π* + u_{r,t}/(φ − 1)`" are not steady states at the Figure 20.3 values (`2` and `0`). -/
theorem fig203_printed_steady_states_false :
    fmap 1 (1 / 2) 2 2 (-2) 2 ≠ 2 ∧
      fmap 1 (1 / 2) 2 2 (-2) (2 + (-2) / (2 - 1)) ≠ 2 + (-2) / (2 - 1) := by
  constructor <;> intro h <;> linarith [fig203_no_steady_state 2, fig203_no_steady_state 0,
    show (2 : ℝ) + (-2) / (2 - 1) = 0 by norm_num]

/-! ## Global versus local (pp. 473–474), `u = 0` -/

/-- Cochrane (2023), eq. (20.4), p. 472, with `u = 0`: on the active branch
`f(π) − π* = ((1 + φσκ)/(1 + σκ))(π − π*)`. -/
theorem active_affine {σ κ φ πs π : ℝ} (hσκ : 0 < σ * κ) (hφ : 0 < φ) (h : kink φ πs ≤ π) :
    fmap σ κ φ πs 0 π - πs = slopeR σ κ φ * (π - πs) := by
  have := eq20_4 (u := 0) hσκ (active_of_kink_le hφ h)
  simpa using this

/-- Cochrane (2023), p. 472: the kink lies strictly between `0` and `π*` (`φ > 1`, `π* > 0`). -/
theorem kink_mem {φ πs : ℝ} (hφ : 1 < φ) (hπs : 0 < πs) : 0 < kink φ πs ∧ kink φ πs < πs := by
  unfold kink
  constructor
  · apply div_pos _ (by linarith)
    nlinarith
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith

/-- Cochrane (2023), p. 473 ("alternative equilibria diverge from the inflation target"):
with `u = 0`, an orbit starting above `π*` satisfies `π_t − π* = cᵗ(π₀ − π*)` and explodes. -/
theorem orbit_above {σ κ φ πs : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hπs : 0 < πs)
    {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = fmap σ κ φ πs 0 (x t)) (h0 : πs < x 0) :
    (∀ t, x t - πs = slopeR σ κ φ ^ t * (x 0 - πs)) ∧ Tendsto x atTop atTop := by
  have hc := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ
  have hk := kink_mem hφ hπs
  have key : ∀ t, x t - πs = slopeR σ κ φ ^ t * (x 0 - πs) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hpos : 0 < x t - πs := by
        rw [ih]; exact mul_pos (pow_pos (by linarith) t) (by linarith)
      rw [hx t, active_affine hσκ (by linarith) (by linarith), ih, pow_succ]
      ring
  refine ⟨key, ?_⟩
  have hp := (tendsto_pow_atTop_atTop_of_one_lt hc).atTop_mul_const (sub_pos.mpr h0)
  have e : x = fun t => slopeR σ κ φ ^ t * (x 0 - πs) + πs := by
    funext t
    linarith [key t]
  rw [e]
  exact tendsto_atTop_add_const_right _ _ hp

/-- Cochrane (2023), p. 473 ("Equilibria in which inflation undershoots … return back to zero
inflation and zero interest rates"): with `u = 0`, every orbit starting below `π*` converges to
`0`. -/
theorem orbit_below_tendsto_zero {σ κ φ πs : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hπs : 0 < πs)
    {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = fmap σ κ φ πs 0 (x t)) (h0 : x 0 < πs) :
    Tendsto x atTop (𝓝 0) := by
  have hφ0 : 0 < φ := by linarith
  have hc := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ
  have hk := kink_mem hφ hπs
  have hfix : fmap σ κ φ πs 0 πs = πs := (fixed_u_zero hφ hσκ hπs).mpr (Or.inr rfl)
  have hbelow : ∀ t, x t < πs := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      rw [hx t]
      have := fmap_strictMono (πs := πs) (u := 0) hφ0.le hσκ ih
      rwa [hfix] at this
  -- some date reaches the zero-bound branch
  have hT : ∃ T, x T ≤ kink φ πs := by
    by_contra hcon
    push Not at hcon
    have key : ∀ t, x t - πs = slopeR σ κ φ ^ t * (x 0 - πs) := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        rw [hx t, active_affine hσκ hφ0 (hcon t).le, ih, pow_succ]
        ring
    have hp := (tendsto_pow_atTop_atTop_of_one_lt hc).eventually
      (eventually_gt_atTop ((πs - kink φ πs) / (πs - x 0)))
    obtain ⟨t, ht⟩ := hp.exists
    have h1 := key t
    have h2 := hcon t
    have hd : 0 < πs - x 0 := by linarith
    rw [div_lt_iff₀ hd] at ht
    nlinarith
  obtain ⟨T, hT⟩ := hT
  have hinv : ∀ y, y ≤ kink φ πs → fmap σ κ φ πs 0 y = (1 + σ * κ)⁻¹ * y := by
    intro y hy
    rw [eq20_3 ((kink_iff hφ0).mpr hy)]
    ring
  have hstay : ∀ n, x (T + n) = (1 + σ * κ)⁻¹ ^ n * x T := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hle : x (T + n) ≤ kink φ πs := by
        rw [ih]
        rcases le_or_gt 0 (x T) with h | h
        · calc (1 + σ * κ)⁻¹ ^ n * x T ≤ 1 * x T := by
                gcongr
                exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
            _ ≤ kink φ πs := by linarith
        · have : (1 + σ * κ)⁻¹ ^ n * x T ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) h.le
          linarith
      rw [← add_assoc, hx, hinv _ hle, ih, pow_succ]
      ring
  have hlim : Tendsto (fun n => x (T + n)) atTop (𝓝 0) := by
    have hr : Tendsto (fun n : ℕ => (1 + σ * κ)⁻¹ ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
    have := hr.mul_const (x T)
    simp only [zero_mul] at this
    refine this.congr fun n => ?_
    rw [hstay n]
  have e : (fun n => x (T + n)) = fun n => x (n + T) := by
    funext n; rw [add_comm]
  rw [e] at hlim
  exact (tendsto_add_atTop_iff_nat T).mp hlim

/-- Cochrane (2023), p. 473 ("return back to zero inflation and zero interest rates"): with
`u = 0`, along every orbit starting below `π*` the interest rate is eventually zero. -/
theorem orbit_below_rate_zero {σ κ φ πs : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hπs : 0 < πs)
    {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = fmap σ κ φ πs 0 (x t)) (h0 : x 0 < πs) :
    ∀ᶠ t in atTop, rule φ πs (x t) = 0 :=
  ((orbit_below_tendsto_zero hφ hσκ hπs hx h0).eventually
    (Iio_mem_nhds (kink_mem hφ hπs).1)).mono fun _ ht =>
      max_eq_right ((kink_iff (by linarith)).mpr (le_of_lt ht))

/-- Cochrane (2023), pp. 473–474 ("the only locally bounded equilibrium, but … not the only
globally bounded one"): with `u = 0`, the orbit from `π₀` is bounded iff `π₀ ≤ π*` — a
continuum of bounded paths. -/
theorem bounded_orbits_eq {σ κ φ πs : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hπs : 0 < πs) :
    {π0 : ℝ | ∃ M, ∀ t, |(fmap σ κ φ πs 0)^[t] π0| ≤ M} = Set.Iic πs := by
  have hfix : fmap σ κ φ πs 0 πs = πs := (fixed_u_zero hφ hσκ hπs).mpr (Or.inr rfl)
  ext π0
  simp only [Set.mem_ofPred_eq, Set.mem_Iic]
  have hx : ∀ t, (fmap σ κ φ πs 0)^[t + 1] π0 = fmap σ κ φ πs 0 ((fmap σ κ φ πs 0)^[t] π0) :=
    fun t => Function.iterate_succ_apply' _ _ _
  constructor
  · rintro ⟨M, hM⟩
    by_contra hc
    push Not at hc
    have := (orbit_above (x := fun t => (fmap σ κ φ πs 0)^[t] π0) hφ hσκ hπs hx
      (by simpa using hc)).2
    obtain ⟨t, ht⟩ := (this.eventually (eventually_gt_atTop M)).exists
    linarith [le_abs_self ((fmap σ κ φ πs 0)^[t] π0), hM t]
  · intro h
    rcases h.lt_or_eq with h | h
    · have hl := orbit_below_tendsto_zero (x := fun t => (fmap σ κ φ πs 0)^[t] π0) hφ hσκ hπs
        hx (by simpa using h)
      obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ hl).exists_norm_le
      exact ⟨M, fun t => by simpa using hM _ ⟨t, rfl⟩⟩
    · refine ⟨|πs|, fun t => ?_⟩
      rw [h, Function.iterate_fixed hfix]

/-- Cochrane (2023), p. 473 ("`π_t = π*` is the only locally bounded equilibrium"): with
`u = 0`, an orbit that stays within `π* − π*(φ − 1)/φ` of `π*` is constant at `π*`. -/
theorem locally_bounded_unique {σ κ φ πs : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ)
    {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = fmap σ κ φ πs 0 (x t))
    (hb : ∀ t, |x t - πs| < πs - kink φ πs) : ∀ t, x t = πs := by
  have hφ0 : 0 < φ := by linarith
  have hc := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ
  have hon : ∀ t, kink φ πs ≤ x t := fun t => by
    have := hb t
    rw [abs_lt] at this
    linarith
  have key : ∀ t, x t - πs = slopeR σ κ φ ^ t * (x 0 - πs) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hx t, active_affine hσκ hφ0 (hon t), ih, pow_succ]
      ring
  have h0 : x 0 = πs := by
    by_contra hne
    have hd : 0 < |x 0 - πs| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hc).eventually
      (eventually_gt_atTop ((πs - kink φ πs) / |x 0 - πs|))).exists
    have := hb t
    rw [key t, abs_mul, abs_of_pos (pow_pos (by linarith) t)] at this
    rw [div_lt_iff₀ hd] at ht
    linarith
  intro t
  have := key t
  rw [h0, sub_self, mul_zero] at this
  linarith

/-- Cochrane (2023), §20.2.1, p. 472: the expectation system shifted to start at date `T`,
`E'_t = E_{T+t}`. -/
def shiftE (T : ℕ) : ExpectationSystem Ω where
  E := fun t => 𝔼.E (T + t)
  const := fun t c => 𝔼.const (T + t) c
  mono := fun t _ _ h => 𝔼.mono (T + t) h
  tower := fun hst x => 𝔼.tower (by omega) x
  known := fun hst x => 𝔼.known (by omega) x

/-- Cochrane (2023), p. 473 ("`π_t = π*` is the only locally bounded equilibrium"), under any
`ExpectationSystem`: if from date `T` on `u = 0`, `E_tπ_{t+1} = f(π_t)` and `π` stays within
`ε < π* − π*(φ − 1)/φ` of `π*`, then `π_t = π*` for all `t ≥ T`. -/
theorem locally_bounded_unique_E {σ κ φ πs ε : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (T : ℕ)
    {π : ℕ → Ω → ℝ} (h : ∀ t ω, T ≤ t → 𝔼.E t (π (t + 1)) ω = fmap σ κ φ πs 0 (π t ω))
    (hε : ε < πs - kink φ πs) (hb : ∀ t ω, T ≤ t → |π t ω - πs| ≤ ε) :
    ∀ t, T ≤ t → π t = fun _ => πs := by
  have hφ0 : 0 < φ := by linarith
  have hc := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ
  have hc0 : 0 < slopeR σ κ φ := by linarith
  set d : ℕ → Ω → ℝ := fun t ω => π (T + t) ω - πs with hd
  have hstep : ∀ t, d t = (slopeR σ κ φ)⁻¹ • (shiftE 𝔼 T).E t (d (t + 1)) +
      (0 : ℕ → Ω → ℝ) t := by
    intro t
    funext ω
    have hon : kink φ πs ≤ π (T + t) ω := by
      have := hb (T + t) ω (by omega)
      rw [abs_le] at this
      linarith
    have he := h (T + t) ω (by omega)
    have hE : (shiftE 𝔼 T).E t (d (t + 1)) ω = 𝔼.E (T + t) (π (T + t + 1)) ω - πs := by
      change 𝔼.E (T + t) (π (T + (t + 1)) - fun _ => πs) ω = _
      rw [map_sub, 𝔼.const, ← add_assoc]
      rfl
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, hd]
    rw [hE, he, active_affine hσκ hφ0 hon]
    field_simp
  have hinv : |(slopeR σ κ φ)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos hc0]
    exact inv_lt_one_of_one_lt₀ hc
  have h0 := (shiftE 𝔼 T).forward_unique hinv (u := 0) (z₁ := d) (z₂ := 0) hstep
    (fun t => by simp) ⟨ε, fun t ω => hb (T + t) ω (by omega)⟩ ⟨0, fun _ _ => by simp⟩
  intro t ht
  funext ω
  have := congrFun (congrFun h0 (t - T)) ω
  simp only [hd, Pi.zero_apply, show T + (t - T) = t by omega] at this
  linarith

/-! ## Figure 20.3: selection by the future rule -/

/-- Cochrane (2023), §20.2.1, p. 472: backward uniqueness. For any `ExpectationSystem`, any
deterministic natural-rate path `u`, `φ ≥ 0`, `σκ > 0`: two processes satisfying
`E_tπ_{t+1} = f_{u_t}(π_t)` that share the same deterministic date-`T` value agree at every
earlier date and are deterministic there. -/
theorem backward_unique {σ κ φ πs : ℝ} (hφ : 0 ≤ φ) (hσκ : 0 < σ * κ) (u : ℕ → ℝ) (T : ℕ)
    {π π' : ℕ → Ω → ℝ} (h : ∀ t ω, 𝔼.E t (π (t + 1)) ω = fmap σ κ φ πs (u t) (π t ω))
    (h' : ∀ t ω, 𝔼.E t (π' (t + 1)) ω = fmap σ κ φ πs (u t) (π' t ω)) {c : ℝ}
    (hT : ∀ ω, π T ω = c) (hT' : ∀ ω, π' T ω = c) :
    ∀ k, k ≤ T → ∃ b, ∀ ω, π (T - k) ω = b ∧ π' (T - k) ω = b := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨c, fun ω => ⟨hT ω, hT' ω⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨b, hb⟩ := ih (by omega)
    obtain ⟨b', hb'⟩ := fmap_surjective (u := u (T - (k + 1))) (πs := πs) hφ hσκ b
    have hconst : π (T - (k + 1) + 1) = fun _ => b := by
      funext ω; rw [show T - (k + 1) + 1 = T - k by omega]; exact (hb ω).1
    have hconst' : π' (T - (k + 1) + 1) = fun _ => b := by
      funext ω; rw [show T - (k + 1) + 1 = T - k by omega]; exact (hb ω).2
    refine ⟨b', fun ω => ⟨?_, ?_⟩⟩
    · have := h (T - (k + 1)) ω
      rw [hconst, 𝔼.const, ← hb'] at this
      exact ((fmap_strictMono hφ hσκ).injective this).symm
    · have := h' (T - (k + 1)) ω
      rw [hconst', 𝔼.const, ← hb'] at this
      exact ((fmap_strictMono hφ hσκ).injective this).symm

/-- Cochrane (2023), §20.2.1, p. 472: existence of the selected path. For `φ > 1`, a
natural-rate path with `u_t = 0` for `t ≥ T` and target `π*`, there is a deterministic path with
`π_t = π*` for `t ≥ T` and `π_{t+1} = f_{u_t}(π_t)` at every date; it solves the model under any
`ExpectationSystem`. -/
theorem backward_exists {σ κ φ πs : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hπs : 0 < πs)
    (u : ℕ → ℝ) (T : ℕ) (hu : ∀ t, T ≤ t → u t = 0) :
    ∃ p : ℕ → ℝ, (∀ t, T ≤ t → p t = πs) ∧ (∀ t, p (t + 1) = fmap σ κ φ πs (u t) (p t)) ∧
      ∀ t ω, 𝔼.E t (fun _ => p (t + 1)) ω = fmap σ κ φ πs (u t) ((fun _ => p t) ω) := by
  have hφ0 : 0 ≤ φ := by linarith
  have hsurj := fun t => fmap_surjective (u := u t) (πs := πs) hφ0 hσκ
  -- `b k` is the value at date `T - k`
  let b : ℕ → ℝ := fun k => Nat.rec πs (fun k bk => Function.surjInv (hsurj (T - (k + 1))) bk) k
  have hb : ∀ k, fmap σ κ φ πs (u (T - (k + 1))) (b (k + 1)) = b k := fun k =>
    Function.surjInv_eq (hsurj (T - (k + 1))) (b k)
  have hfix : fmap σ κ φ πs 0 πs = πs := (fixed_u_zero hφ hσκ hπs).mpr (Or.inr rfl)
  let p : ℕ → ℝ := fun t => if T ≤ t then πs else b (T - t)
  have hstep : ∀ t, p (t + 1) = fmap σ κ φ πs (u t) (p t) := by
    intro t
    by_cases ht : T ≤ t
    · simp only [p, ht, show T ≤ t + 1 by omega, ↓reduceIte]
      rw [hu t ht, hfix]
    · simp only [p, ht, ↓reduceIte]
      by_cases ht1 : T ≤ t + 1
      · have hTt : T = t + 1 := by omega
        simp only [ht1, ↓reduceIte]
        have := hb 0
        rw [show T - (0 + 1) = t by omega] at this
        rw [show T - t = 0 + 1 by omega, this]
        rfl
      · simp only [ht1, ↓reduceIte]
        have := hb (T - (t + 1))
        rw [show T - (T - (t + 1) + 1) = t by omega, show T - (t + 1) + 1 = T - t by omega]
          at this
        exact this.symm
  refine ⟨p, fun t ht => by simp [p, ht], hstep, fun t ω => ?_⟩
  rw [𝔼.const, hstep t]

/-- Cochrane (2023), Figure 20.3, p. 473: the natural rate, `u_r = −2` before `T = 10` and `0`
from `T` on (the reading under which `π_t = π*` for `t ≥ T` solves the model). -/
noncomputable def uFig (t : ℕ) : ℝ := if t < 10 then -2 else 0

/-- Cochrane (2023), Figure 20.3, pp. 472–473: selection by the future rule. For any
`ExpectationSystem`, if `π` solves the model with `σ = 1`, `κ = 1/2`, `φ = 2`, `π* = 2` and the
natural-rate path `uFig`, and stays within `ε < 1` of `π* = 2` from `T = 10` on (local
boundedness under the active rule), then `π_t = 2` for `t ≥ 10` and, at every state,
`π₉ = 3/2`, `π₈ = 9/8`, `π₇ = 11/16`, `π₆ = 1/32`. -/
theorem fig203_selection {π : ℕ → Ω → ℝ} {ε : ℝ}
    (h : ∀ t ω, 𝔼.E t (π (t + 1)) ω = fmap 1 (1 / 2) 2 2 (uFig t) (π t ω)) (hε : ε < 1)
    (hb : ∀ t ω, 10 ≤ t → |π t ω - 2| ≤ ε) :
    (∀ t, 10 ≤ t → π t = fun _ => 2) ∧ ∀ ω, π 9 ω = 3 / 2 ∧ π 8 ω = 9 / 8 ∧
      π 7 ω = 11 / 16 ∧ π 6 ω = 1 / 32 := by
  have hσκ : (0 : ℝ) < 1 * (1 / 2) := by norm_num
  have hk : kink 2 2 = 1 := kink_fig203.1
  have hsel := locally_bounded_unique_E 𝔼 (σ := 1) (κ := 1 / 2) (φ := 2) (πs := 2)
    (by norm_num) hσκ 10 (π := π) (fun t ω ht => by
      have := h t ω
      rw [show uFig t = 0 by simp [uFig]; omega] at this
      exact this) (by rw [hk]; linarith) hb
  refine ⟨hsel, ?_⟩
  have inj := (fmap_strictMono (σ := 1) (κ := 1 / 2) (φ := 2) (πs := 2) (u := -2) (by norm_num)
    hσκ).injective
  have hu : ∀ t, t < 10 → uFig t = -2 := fun t ht => by simp [uFig, ht]
  have step : ∀ t c d, t < 10 → (π (t + 1) = fun _ => c) →
      fmap 1 (1 / 2) 2 2 (-2) d = c → π t = fun _ => d := by
    intro t c d ht hc hd
    funext ω
    have := h t ω
    rw [hc, 𝔼.const, hu t ht, ← hd] at this
    exact (inj this).symm
  have v9 : fmap 1 (1 / 2) 2 2 (-2) (3 / 2) = 2 := by
    unfold fmap rule; rw [max_eq_left (by norm_num)]; norm_num
  have v8 : fmap 1 (1 / 2) 2 2 (-2) (9 / 8) = 3 / 2 := by
    unfold fmap rule; rw [max_eq_left (by norm_num)]; norm_num
  have v7 : fmap 1 (1 / 2) 2 2 (-2) (11 / 16) = 9 / 8 := by
    unfold fmap rule; rw [max_eq_right (by norm_num)]; norm_num
  have v6 : fmap 1 (1 / 2) 2 2 (-2) (1 / 32) = 11 / 16 := by
    unfold fmap rule; rw [max_eq_right (by norm_num)]; norm_num
  have p9 := step 9 2 (3 / 2) (by norm_num) (hsel 10 le_rfl) v9
  have p8 := step 8 (3 / 2) (9 / 8) (by norm_num) p9 v8
  have p7 := step 7 (9 / 8) (11 / 16) (by norm_num) p8 v7
  have p6 := step 6 (11 / 16) (1 / 32) (by norm_num) p7 v6
  intro ω
  exact ⟨by rw [p9], by rw [p8], by rw [p7], by rw [p6]⟩

/-- Cochrane (2023), p. 472, survey error E3 ("Before `t = T`, while the nominal rate remains
stuck at zero"): on the selected path of Figure 20.3 the rate lifts off two periods before
`T = 10`: `i₉ = 1`, `i₈ = 1/4`, while `i₇ = i₆ = 0`. -/
theorem fig203_early_liftoff :
    rule 2 2 (3 / 2) = 1 ∧ rule 2 2 (9 / 8) = 1 / 4 ∧ rule 2 2 (11 / 16) = 0 ∧
      rule 2 2 (1 / 32) = 0 := by
  unfold rule
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [max_eq_left (by norm_num)]; norm_num
  · rw [max_eq_left (by norm_num)]; norm_num
  · rw [max_eq_right (by norm_num)]
  · rw [max_eq_right (by norm_num)]

end Cochrane.ZeroBound.ZLBRule
