/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.ZLBSelection

/-!
# Forward guidance at the zero bound

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.4, pp. 478–480.

In the Werning experiment the equilibria are indexed by end-of-trap inflation `π_T`. Selecting
by `π_T` ("forward guidance" about inflation at `T`) gives promises enormous power.

## Main results

* `dpi0_dpiT`: across the family, `π_0 − π_0' = e^{λ^b T}(π_T − π_T')`; more generally
  `dpi_dpiT` at every date `t ≤ T`, `e^{λ^b(T−t)}`.
* `piTnj_eq`: the no-jump equilibrium has `π_T = −π_0^{NK} e^{−λ^b T}`, and `glide_path`: the
  required "glide path" `0 < π_T < −u` is bounded by the size of the shock, while the deflation
  it removes is unbounded (`pi0NK_tendsto_kappa`).
* "Promises further in the future matter more": `sensitivity_strictMono_T`,
  `sensitivity_tendsto_T`. "Less sticky ⇒ greater effect": `sensitivity_strictMono_kappa`,
  `sensitivity_tendsto_kappa`. "No effect at the limit point": `frictionless_unique`.
* Delayed lift-off (Woodford 2012, Werning 2012; p. 479): with a positive post-trap natural rate
  `u₂` and the rate held at zero until `L = T + τ`, the `π_L = 0` equilibrium `delayPi`
  (`delay_isPath`, `delay_bdd`, `delay_after`, `delay_unique`) has
  `π_0 = −u(1 − h(T)) + u₂(h(T+τ) − h(T))` (`delay_pi0`), strictly increasing in the delay
  (`delay_pi0_strictMono`) and unbounded (`delay_pi0_tendsto`): committing to delay the rate
  rise has the same power as promising time-`T` inflation.
-/

namespace Cochrane.ZeroBound.ForwardGuidance

open Filter Topology MeasureTheory
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.ZLBSelection

/-! ## Sensitivity of `π_0` to `π_T` -/

/-- Cochrane (2023), §20.2.4, p. 479 ("inflation at time 0 is sensitive to its expectation at
time T"): at every date `t`, `π_t(π_T) − π_t(π_T') = e^{λ^b(T−t)}(π_T − π_T')`. -/
theorem dpi_dpiT (σ κ ρ T u g πT πT' t : ℝ) :
    wPi σ κ ρ T u g πT t - wPi σ κ ρ T u g πT' t =
      Real.exp (lamb ρ κ σ * (T - t)) * (πT - πT') := by
  rw [wPi_shift σ κ ρ T u g πT, wPi_shift σ κ ρ T u g πT']
  ring

/-- Cochrane (2023), §20.2.4, p. 479: **`π_0 − π_0' = e^{λ^b T}(π_T − π_T')`**. -/
theorem dpi0_dpiT (σ κ ρ T u g πT πT' : ℝ) :
    wPi σ κ ρ T u g πT 0 - wPi σ κ ρ T u g πT' 0 =
      Real.exp (lamb ρ κ σ * T) * (πT - πT') := by
  rw [dpi_dpiT, sub_zero]

/-- Cochrane (2023), §20.2.4, p. 479: `π_0` is an affine function of the promise `π_T` with
derivative `e^{λ^b T}` (an exact derivative). -/
theorem hasDerivAt_pi0_piT (σ κ ρ T u g πT : ℝ) :
    HasDerivAt (fun p => wPi σ κ ρ T u g p 0) (Real.exp (lamb ρ κ σ * T)) πT := by
  have h : (fun p => wPi σ κ ρ T u g p 0) =
      fun p => wPi σ κ ρ T u g 0 0 + p * Real.exp (lamb ρ κ σ * (T - 0)) :=
    funext fun p => wPi_shift σ κ ρ T u g p 0
  rw [h, sub_zero]
  exact ((hasDerivAt_id πT).mul_const _).const_add _ |>.congr_deriv (by simp)

/-- Cochrane (2023), §20.2.4, p. 479: the no-jump equilibrium's end-of-trap inflation is
`π_T = −π_0^{NK} e^{−λ^b T}`. -/
theorem piTnj_eq {σ κ ρ T u : ℝ} (hT : 0 ≤ T) :
    piTnj σ κ ρ T u = -pi0NK σ κ ρ T u * Real.exp (-(lamb ρ κ σ * T)) := by
  rw [pi0NK_eq hT, piTnj]
  ring

/-- Cochrane (2023), §20.2.4, p. 479 ("if only the central bank could allow a small amount of
time-T inflation, a glide path back to its target, then the huge deflation … would be solved"):
the glide path that removes the deflation jump satisfies `0 < π_T < −u` for every `κ` and `T`
(bounded by the size of the shock), although the deflation it removes is unbounded
(`pi0NK_tendsto_kappa`, `pi0NK_tendsto_T`). -/
theorem glide_path {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (hT : 0 < T) :
    0 < piTnj σ κ ρ T u ∧ piTnj σ κ ρ T u < -u ∧ wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) 0 = 0 :=
  ⟨(piTnj_bounds hσ hκ hu hT).1, (piTnj_bounds hσ hκ hu hT).2, nj_pi0 hT.le⟩

/-- Cochrane (2023), §20.2.4, p. 479 ("promises about actions further in the future have greater
effects today"): the sensitivity `e^{λ^b T}` is strictly increasing in the horizon `T`. -/
theorem sensitivity_strictMono_T {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    StrictMono fun T => Real.exp (lamb ρ κ σ * T) := fun _ _ h =>
  Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left h (lamb_pos hκ hσ))

/-- Cochrane (2023), §20.2.4, p. 479: the sensitivity `e^{λ^b T}` is unbounded in `T`. -/
theorem sensitivity_tendsto_T {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    Tendsto (fun T => Real.exp (lamb ρ κ σ * T)) atTop atTop :=
  tendsto_expPos (lamb_pos hκ hσ)

/-- Cochrane (2023), §20.2.4, p. 479 ("as prices become less sticky … forward guidance has
greater and greater effect"): the sensitivity is strictly increasing in `κ` (`T > 0`). -/
theorem sensitivity_strictMono_kappa {σ ρ T κ κ' : ℝ} (hσ : 0 < σ) (hT : 0 < T) (hκ : 0 < κ)
    (hlt : κ < κ') : Real.exp (lamb ρ κ σ * T) < Real.exp (lamb ρ κ' σ * T) :=
  Real.exp_lt_exp.2 (mul_lt_mul_of_pos_right (lamb_strictMono hσ hκ hlt) hT)

/-- Cochrane (2023), §20.2.4, p. 479: the sensitivity is unbounded as `κ → ∞` (`T > 0`). -/
theorem sensitivity_tendsto_kappa {σ ρ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    Tendsto (fun κ => Real.exp (lamb ρ κ σ * T)) atTop atTop :=
  expLamb_tendsto_kappa hσ hT

/-- Cochrane (2023), §20.2.4, p. 479 ("until all of a sudden at the flexible-price limit point,
forward guidance has no effect at all"): in the frictionless model there is no free constant —
any two solutions coincide (`x` on `[0, ∞)`, `π` off the date `T`), so nothing announced about
`π_T` or later can move `π_0`. -/
theorem frictionless_unique {σ T u g : ℝ} (hσ : σ ≠ 0) {x π x' π' : ℝ → ℝ}
    (h : IsFrictionless σ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π)
    (h' : IsFrictionless σ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x' π') :
    (∀ t, 0 ≤ t → x t = x' t) ∧ ∀ t, 0 < t → t ≠ T → π t = π' t := by
  obtain ⟨a, b⟩ := (frictionless_iff hσ).1 h
  obtain ⟨a', b'⟩ := (frictionless_iff hσ).1 h'
  exact ⟨fun t ht => by rw [a t ht, a' t ht], fun t ht htT => by rw [b t ht htT, b' t ht htT]⟩

/-! ## Delayed lift-off (p. 479) -/

/-- Cochrane (2023), (20.5)–(20.6): the model depends on `i` and `u_r` only through `i − u_r`. -/
theorem isPath_congr_forcing {σ ρ κ : ℝ} {i u g i' u' g' x π : ℝ → ℝ} {S : Set ℝ}
    (h : IsPath σ ρ κ i u g S x π) (hiu : ∀ t, 0 < t → t ∉ S → i t - u t = i' t - u' t)
    (hg : ∀ t, 0 < t → t ∉ S → g t = g' t) : IsPath σ ρ κ i' u' g' S x π := by
  refine ⟨h.1, h.2.1, fun t ht hS => ?_⟩
  obtain ⟨a, b⟩ := h.2.2 t ht hS
  refine ⟨a.congr_deriv ?_, b.congr_deriv ?_⟩
  · have := hiu t ht hS
    linear_combination σ * this
  · rw [hg t ht hS]

/-- Cochrane (2023), §20.2.4, p. 479: the delayed-lift-off interest rate: `0` until `L`, then
the post-trap natural rate `u₂`. -/
noncomputable def delayI (u2 L t : ℝ) : ℝ := if t < L then 0 else u2

/-- Cochrane (2023), §20.2.4, p. 479: the natural rate: `u` during the trap, `u₂` afterwards. -/
noncomputable def delayU (u u2 T t : ℝ) : ℝ := if t < T then u else u2

/-- Cochrane (2023), §20.2.4, p. 479: the `π_L = 0` inflation path under delayed lift-off,
the superposition of a trap of length `T` with forcing `u₂ − u` and one of length `L` with
forcing `−u₂`. -/
noncomputable def delayPi (σ κ ρ T L u u2 t : ℝ) : ℝ :=
  wPi σ κ ρ T (u - u2) 0 0 t + wPi σ κ ρ L u2 0 0 t

/-- Cochrane (2023), §20.2.4, p. 479: the corresponding output gap. -/
noncomputable def delayX (σ κ ρ T L u u2 t : ℝ) : ℝ :=
  wX σ κ ρ T (u - u2) 0 0 t + wX σ κ ρ L u2 0 0 t

/-- Cochrane (2023), §20.2.4, p. 479: the delayed-lift-off path solves (20.5)–(20.6) with
`i = delayI`, `u_r = delayU`, `g = 0` (off `{T, L}`). -/
theorem delay_isPath {σ κ ρ T L u u2 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    IsPath σ ρ κ (delayI u2 L) (delayU u u2 T) (fun _ => 0) ({T} ∪ {L})
      (delayX σ κ ρ T L u u2) (delayPi σ κ ρ T L u u2) := by
  have h := (wPath_isPath (ρ := ρ) hκ hσ T (u - u2) 0 0).add
    (wPath_isPath (ρ := ρ) hκ hσ L u2 0 0)
  refine isPath_congr_forcing h (fun t _ _ => ?_) (fun t _ _ => by simp [trapStep])
  simp only [delayI, delayU, trapStep]
  split_ifs <;> ring

/-- Cochrane (2023), §20.2.4, p. 479: the delayed-lift-off path is bounded. -/
theorem delay_bdd {σ κ ρ T L u u2 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    BddOnIci (delayX σ κ ρ T L u u2) ∧ BddOnIci (delayPi σ κ ρ T L u u2) := by
  obtain ⟨⟨K1, h1⟩, ⟨K2, h2⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ T (u - u2) 0 0
  obtain ⟨⟨K3, h3⟩, ⟨K4, h4⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ L u2 0 0
  exact ⟨⟨K1 + K3, fun t ht => (abs_add_le _ _).trans (add_le_add (h1 t ht) (h3 t ht))⟩,
    ⟨K2 + K4, fun t ht => (abs_add_le _ _).trans (add_le_add (h2 t ht) (h4 t ht))⟩⟩

/-- Cochrane (2023), §20.2.4, p. 479: inflation and output are zero from lift-off on. -/
theorem delay_after {σ κ ρ T L u u2 t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hTL : T ≤ L)
    (ht : L ≤ t) : delayPi σ κ ρ T L u u2 t = 0 ∧ delayX σ κ ρ T L u u2 t = 0 := by
  obtain ⟨a1, b1⟩ := nk_after (ρ := ρ) (u := u - u2) hσ hκ (le_trans hTL ht)
  obtain ⟨a2, b2⟩ := nk_after (ρ := ρ) (u := u2) hσ hκ ht
  simp only [delayPi, delayX, a1, b1, a2, b2, add_zero, and_self]

/-- Cochrane (2023), §20.2.4, p. 479: **uniqueness of the `π_L = 0` equilibrium under delayed
lift-off**: any bounded path of the delayed experiment with `π_L = 0` is `delayPi`. -/
theorem delay_unique {σ κ ρ T L u u2 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hTL : T ≤ L)
    (hL : 0 ≤ L) {x π : ℝ → ℝ}
    (h : IsPath σ ρ κ (delayI u2 L) (delayU u u2 T) (fun _ => 0) ({T} ∪ {L}) x π)
    (hx : BddOnIci x) (hπ : BddOnIci π) (hπL : π L = 0) :
    ∀ t, 0 ≤ t → π t = delayPi σ κ ρ T L u u2 t ∧ x t = delayX σ κ ρ T L u u2 t := by
  obtain ⟨⟨Kx, hKx⟩, ⟨Kπ, hKπ⟩⟩ := (⟨hx, hπ⟩ : BddOnIci x ∧ BddOnIci π)
  obtain ⟨⟨Kx0, hKx0⟩, ⟨Kπ0, hKπ0⟩⟩ := delay_bdd (ρ := ρ) (T := T) (L := L) (u := u)
    (u2 := u2) hσ hκ
  have hS : ({T} ∪ {L} ∪ ({T} ∪ {L}) : Set ℝ).Countable :=
    ((Set.countable_singleton T).union (Set.countable_singleton L)).union
      ((Set.countable_singleton T).union (Set.countable_singleton L))
  have hh := homog_bdd hσ hκ hS (h.sub (delay_isPath (ρ := ρ) hσ hκ))
    ⟨Kx + Kx0, fun t ht => (abs_sub _ _).trans (add_le_add (hKx t ht) (hKx0 t ht))⟩
    ⟨Kπ + Kπ0, fun t ht => (abs_sub _ _).trans (add_le_add (hKπ t ht) (hKπ0 t ht))⟩
  have hc : π 0 - delayPi σ κ ρ T L u u2 0 = 0 := by
    have := (hh L hL).1
    rw [hπL, (delay_after (ρ := ρ) (u := u) (u2 := u2) hσ hκ hTL le_rfl).1, sub_zero] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h (Real.exp_pos _).ne'
    · exact h
  intro t ht
  obtain ⟨h1, h2⟩ := hh t ht
  rw [hc, mul_zero] at h1
  have h1' : π t = delayPi σ κ ρ T L u u2 t := by linarith
  refine ⟨h1', ?_⟩
  rw [h1', sub_self, mul_zero] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h hκ.ne'
  · linarith

/-- Cochrane (2023), §20.2.4, p. 479: initial inflation under delayed lift-off,
`π_0 = −u(1 − h(T)) + u₂(h(L) − h(T))`. -/
theorem delay_pi0 {σ κ ρ T L u u2 : ℝ} (hT : 0 ≤ T) (hTL : T ≤ L) :
    delayPi σ κ ρ T L u u2 0 = -u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) T) +
      u2 * (hh (lamf ρ κ σ) (lamb ρ κ σ) L - hh (lamf ρ κ σ) (lamb ρ κ σ) T) := by
  rw [delayPi, nk_pi_eq hT, nk_pi_eq (le_trans hT hTL), sub_zero, sub_zero]
  ring

/-- Cochrane (2023), §20.2.4, p. 479 ("a policy that commits to delaying an interest-rate rise …
has the same effect"): with a positive post-trap natural rate `u₂ > 0`, initial inflation is
strictly increasing in the delay `τ ≥ 0` (lift-off at `T + τ`). -/
theorem delay_pi0_strictMono {σ κ ρ T u u2 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 ≤ T)
    (hu2 : 0 < u2) :
    StrictMonoOn (fun τ => delayPi σ κ ρ T (T + τ) u u2 0) (Set.Ici 0) := by
  intro τ1 h1 τ2 h2 hlt
  simp only
  rw [delay_pi0 hT (by linarith [Set.mem_Ici.1 h1]),
    delay_pi0 hT (by linarith [Set.mem_Ici.1 h2])]
  have := hh_strictMonoOn (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ)
    (Set.mem_Ici.2 (by linarith [Set.mem_Ici.1 h1] : (0 : ℝ) ≤ T + τ1))
    (Set.mem_Ici.2 (by linarith [Set.mem_Ici.1 h2] : (0 : ℝ) ≤ T + τ2))
    (by linarith : T + τ1 < T + τ2)
  nlinarith

/-- Cochrane (2023), §20.2.4, p. 479: with no delay the `π_L = 0` equilibrium is the standard
`π_T = 0` one: `π_0 = π_0^{NK}`. -/
theorem delay_zero {σ κ ρ T u u2 : ℝ} (hT : 0 ≤ T) :
    delayPi σ κ ρ T (T + 0) u u2 0 = pi0NK σ κ ρ T u := by
  rw [delay_pi0 hT (by linarith), add_zero, pi0NK_eq hT]
  ring

/-- Cochrane (2023), §20.2.4, p. 479: a long enough delay produces any initial inflation:
`π_0 → ∞` as the delay `τ → ∞` (`u₂ > 0`). -/
theorem delay_pi0_tendsto {σ κ ρ T u u2 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 ≤ T)
    (hu2 : 0 < u2) : Tendsto (fun τ => delayPi σ κ ρ T (T + τ) u u2 0) atTop atTop := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  set c0 := -u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) T) -
    u2 * hh (lamf ρ κ σ) (lamb ρ κ σ) T
  have hE : Tendsto (fun τ => u2 * (lamf ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ)) *
      Real.exp (lamb ρ κ σ * (T + τ))) atTop atTop := by
    have : Tendsto (fun τ => Real.exp (lamb ρ κ σ * (T + τ))) atTop atTop :=
      Real.tendsto_exp_atTop.comp ((tendsto_atTop_add_const_left atTop T tendsto_id).const_mul_atTop
        hb)
    exact this.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_left atTop c0 hE)
  filter_upwards [eventually_ge_atTop 0] with τ hτ
  rw [delay_pi0 hT (by linarith)]
  have := hh_ge hf hb (T + τ)
  have e : lamf ρ κ σ * Real.exp (lamb ρ κ σ * (T + τ)) / (lamf ρ κ σ + lamb ρ κ σ) =
      lamf ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * Real.exp (lamb ρ κ σ * (T + τ)) := by ring
  rw [e] at this
  simp only [c0]
  nlinarith

end Cochrane.ZeroBound.ForwardGuidance
