/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.LiftoffTiming
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# The commitment optimum: existence, uniqueness and the shape of the zero-rate spell

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.4 (pp. 478–480),
compared with Galí (2015), §5.4.2 (pp. 148–152), in the model of `LinksGaliWoodford`.
Continues `LiftoffTiming` (the zero bound binds on the whole shock, `t_C ≥ t_Z`).

* Existence (`exists_optimal`, `optimal_exists_unique`): paths are coded in the Hilbert space
  `ℓ²(ℕ ⊕ ℕ)` (`PathSpace`, `enc`, `decX`, `decP`) so that the loss is the squared norm
  (`loss_dec`); the feasible codes form a nonempty closed convex set (`feasSet_closed`,
  `feasSet_convex`), and the minimal-norm element is the optimum (`ρ ≥ 0`, any `t_Z`).
* No re-binding (`no_return`): once the zero-bound multiplier vanishes after the shock it stays
  zero (a maximum principle for `(σκ/ϑ − 1)π`).
* Finite lift-off (`exists_slack_after`, `ρ > 0`): binding forever would drive inflation to the
  deflation steady state (`two_root`) and the multipliers would explode or turn negative.
* Galí's closed form after lift-off is necessary (`post_form`).
* `optimal_binding`, `optimal_liftoff`: there is `t_C ≥ t_Z` with `i = 0` exactly on `[0, t_C]`
  and `i > 0` afterwards; `optimal_algorithm_form`: the optimum satisfies every hypothesis of
  Galí's algorithm; `commitment_characterisation`: existence, uniqueness and this shape.
* `ρ = 0` (`liftoff_rates`, `rho_zero_structure`): either the rate is zero at every date, or
  `σκ ≠ ϑ` and the shape above holds; at `σκ = ϑ` the rate never lifts off
  (`rho_zero_unit_ratio`, `rho_zero_no_liftoff`, exact instance `rho_zero_instance`), so `ρ > 0`
  in `commitment_characterisation` is necessary.
-/

namespace Cochrane.ZeroBound.LiftoffStructure

open Filter Topology
open Cochrane.ZeroBound Cochrane.ZeroBound.LinksGaliWoodford Cochrane.ZeroBound.LiftoffTiming

/-! ## Auxiliary algebra -/

/-- Cochrane (2023), p. 479: `comb` is homogeneous in the sequence. -/
theorem comb_smul (β a c : ℝ) (u : ℕ → ℝ) (t : ℕ) :
    comb β a (fun n => c * u n) t = c * comb β a u t := by
  unfold comb; ring

/-- Cochrane (2023), p. 479: `comb` shifts by constants. -/
theorem comb_add_const (β a c : ℝ) (u : ℕ → ℝ) (t : ℕ) :
    comb β a (fun n => u n + c) t = comb β a u t + c := by
  unfold comb; ring

/-- Galí (2015), (15), p. 136; Cochrane (2023), p. 479: `δ` solves
`βδ² − (1 + β + κ²/ϑ)δ + 1 = 0`. -/
theorem del_root {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    β * del β κ ϑ ^ 2 - (1 + β + κ ^ 2 / ϑ) * del β κ ϑ + 1 = 0 := by
  have hg := gam_pos (κ := κ) hβ hϑ
  have hq := del_quad (κ := κ) hβ hβ1 hϑ
  have hm := gam_mul_denom (κ := κ) hβ hϑ
  have h : gam β κ ϑ * (β * del β κ ϑ ^ 2 - (1 + β + κ ^ 2 / ϑ) * del β κ ϑ + 1) = 0 := by
    have e : gam β κ ϑ * (1 + β + κ ^ 2 / ϑ) = 1 := by
      have : gam β κ ϑ * (1 + β + κ ^ 2 / ϑ) = gam β κ ϑ * (ϑ * (1 + β) + κ ^ 2) / ϑ := by
        field_simp
      rw [this, hm, div_self hϑ.ne']
    linear_combination hq - del β κ ϑ * e
  exact (mul_eq_zero.mp h).resolve_left hg.ne'

/-- Cochrane (2023), §5.7.1 and p. 479: **the bounded solutions of a two-root recursion**. If
`β u_{n+2} − (1+β+k) u_{n+1} + u_n = 0` from `n₀` on, `0 < μ < 1` is the stable root
(`βμ² − (1+β+k)μ + 1 = 0`) and `β^n u_n² → 0`, then `u_{n+1} = μ u_n` from `n₀` on (the other
root `1/(βμ)` violates the growth bound). -/
theorem two_root {β k μ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hq : β * μ ^ 2 - (1 + β + k) * μ + 1 = 0) {u : ℕ → ℝ} {n0 : ℕ}
    (hrec : ∀ n, n0 ≤ n → β * u (n + 2) - (1 + β + k) * u (n + 1) + u n = 0)
    (hT : Tendsto (fun n => β ^ n * u n ^ 2) atTop (𝓝 0)) :
    ∀ n, n0 ≤ n → u (n + 1) = μ * u n := by
  set f : ℕ → ℝ := fun n => u (n + 1) - μ * u n with hf
  have hμinv : μ * (1 / μ) = 1 := by field_simp
  have hk : 1 + β + k = β * μ + 1 / μ := by
    have e : β * μ + 1 / μ - (1 + β + k) = (β * μ ^ 2 - (1 + β + k) * μ + 1) * (1 / μ) := by
      linear_combination ((1 + β + k) - β * μ) * hμinv
    rw [hq, zero_mul] at e
    linarith
  have hstep : ∀ n, n0 ≤ n → f (n + 1) = f n / (β * μ) := by
    intro n hn
    have h := hrec n hn
    simp only [hf]
    rw [hk] at h
    rw [eq_div_iff (by positivity)]
    linear_combination μ * h + u (n + 1) * hμinv
  have hfT : Tendsto (fun n => β ^ n * f n ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => β ^ (n + 1) * u (n + 1) ^ 2) atTop (𝓝 0) :=
      hT.comp (tendsto_add_atTop_nat 1)
    have h2 := ((h1.const_mul (2 / β)).add (hT.const_mul 2))
    rw [mul_zero, mul_zero, add_zero] at h2
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) h2
    simp only [hf]
    have hp : 0 < β ^ n := pow_pos hβ0 n
    have e1 : 2 / β * (β ^ (n + 1) * u (n + 1) ^ 2) = 2 * (β ^ n * u (n + 1) ^ 2) := by
      rw [pow_succ]; field_simp
    rw [e1]
    have : (u (n + 1) - μ * u n) ^ 2 ≤ 2 * u (n + 1) ^ 2 + 2 * u n ^ 2 := by
      have : μ ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (u (n + 1) + μ * u n), sq_nonneg (u n)]
    nlinarith
  intro n hn
  by_contra hne
  have hfn : f n ≠ 0 := fun h => hne (by simp only [hf] at h; linarith)
  have hpow : ∀ j, f (n + j) = f n * (1 / (β * μ)) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show n + (j + 1) = (n + j) + 1 by omega, hstep _ (by omega), ih, pow_succ]
      ring
  have hc : 0 < β ^ n * f n ^ 2 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 hfT).2 _ hc)
  have key := hN (n + N) (by omega)
  rw [hpow N] at key
  have hb : 1 ≤ (1 / (β * μ ^ 2)) ^ N := one_le_pow₀ (by
    rw [le_div_iff₀ (by positivity), one_mul]
    nlinarith [mul_lt_mul_of_pos_left hμ1 hμ0])
  have hq2 : β * (1 / (β * μ)) ^ 2 = 1 / (β * μ ^ 2) := by field_simp
  have e : β ^ (n + N) * (f n * (1 / (β * μ)) ^ N) ^ 2 =
      β ^ n * f n ^ 2 * (1 / (β * μ ^ 2)) ^ N := by
    rw [← hq2]
    ring
  rw [e] at key
  nlinarith

/-! ## No return to the zero bound after a slack date following the shock -/

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), p. 150: **once the zero-bound multiplier
vanishes after the shock it stays zero** (no re-binding): if `(x, π)` is optimal, `t_Z < s` and
`ξ₂,s = 0`, then `ξ₂,t = 0` for every `t ≥ s` (any `ρ ≥ 0`). A maximum principle for
`v = (σκ/ϑ − 1)π` gives `v ≤ ρ` after `s`, hence the multiplier combination is `≤ 0` there, and
`mult_zero_right` applies. -/
theorem no_return {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) {s : ℕ} (hs : tZ < s)
    (h0 : mxi2 β κ σ ϑ x π s = 0) : ∀ t, s ≤ t → mxi2 β κ σ ϑ x π t = 0 := by
  obtain ⟨⟨hF, hK⟩, hlim⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  set ξ2 := mxi2 β κ σ ϑ x π with hξ2
  have hN : ∀ t, NKPC β κ x π t := fun t => (hF t).1
  have hS := tendsto_pi_sq hβ hϑ hopt.2.1
  have hmult : ∀ t, κ * lam κ ϑ x π t =
      (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β :=
    fun t => lam_mult hκ.ne' (hK (t + 1)).1 (hK t).2.1 (hK (t + 1)).2.1
  have hpos : ∀ t, 0 ≤ ξ2 t := fun t => (hK t).2.2.1
  have hslack : ∀ t, ξ2 t = 0 → lam κ ϑ x π t ≤ 0 := by
    intro t ht
    have hl : 0 ≤ lag ξ2 t := by
      cases t with
      | zero => simp
      | succ n => simpa using hpos n
    have hk : κ * lam κ ϑ x π t ≤ 0 := by
      rw [hmult t, ht]
      have := div_nonneg hl hβ.le
      have := hpos (t + 1)
      linarith
    by_contra hc
    push Not at hc
    linarith [mul_pos hκ hc]
  have hbind : ∀ t, tZ < t → 0 < ξ2 t → gap σ x π t = -ρ := by
    intro t ht h
    have := (mul_eq_zero.mp (hK t).2.2.2).resolve_left h.ne'
    rw [impliedRate_eq_gap, natRate_of_lt ht] at this
    linarith
  have hfeas : ∀ t, tZ < t → -ρ ≤ gap σ x π t := by
    intro t ht
    have := rate_nonneg hσ hF t
    rw [impliedRate_eq_gap, natRate_of_lt ht] at this
    linarith
  set r := σ * κ / ϑ with hrdef
  have hr0 : 0 < r := by positivity
  have hgl : ∀ t, gap σ x π t = r * lam κ ϑ x π t - (r - 1) * π (t + 1) :=
    fun t => gap_lam hκ.ne' hϑ.ne' x π t
  set v : ℕ → ℝ := fun n => (r - 1) * π n with hv
  have hvs : ∀ t, tZ < t → ξ2 t = 0 → v (t + 1) ≤ ρ := by
    intro t ht h
    have h1 := hfeas t ht
    have h2 := hslack t h
    rw [hgl t] at h1
    have : r * lam κ ϑ x π t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0.le h2
    simp only [hv]
    linarith
  have hvc : ∀ t, tZ < t → 0 < ξ2 t → comb β (σ / κ) v t ≤ ρ := by
    intro t ht h
    rw [comb_smul, ← gap_comb hκ.ne' (hN t) (hN (t + 1)), hbind t ht h]
    have : 0 ≤ r * ρ := mul_nonneg hr0.le hρ
    nlinarith
  have hvT : Tendsto (fun n => β ^ n * v n ^ 2) atTop (𝓝 0) := by
    have := hS.const_mul ((r - 1) ^ 2)
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    simp only [hv]
    ring
  have hsk : 0 < σ / κ := by positivity
  have hV : ∀ n, s + 1 ≤ n → v n ≤ ρ := by
    intro m hm
    by_contra hcon
    push Not at hcon
    obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image (Finset.Icc (s + 1) m) v
      ⟨m, Finset.mem_Icc.mpr ⟨hm, le_rfl⟩⟩
    rw [Finset.mem_Icc] at hm0
    have hpm : ρ < v m0 := lt_of_lt_of_le hcon (hmax m (Finset.mem_Icc.mpr ⟨hm, le_rfl⟩))
    have hne : m0 ≠ s + 1 := by
      rintro rfl
      linarith [hvs s hs h0]
    obtain ⟨j, rfl⟩ : ∃ j, m0 = j + 1 := ⟨m0 - 1, by omega⟩
    have hj : v j ≤ v (j + 1) := hmax j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hbj : ∀ n, tZ < n → ρ < v (n + 1) → 0 < ξ2 n := by
      intro n hn hvn
      rcases (hpos n).eq_or_lt with h | h
      · linarith [hvs n hn h.symm]
      · exact h
    have hup : v (j + 1) < v (j + 2) :=
      comb_up hβ hsk (hvc j (by omega) (hbj j (by omega) hpm)) hpm hj
    refine not_tendsto_sq hβ hβ1.le hρ (n0 := j + 1) (fun n hn hb _ => ?_) (hpm.trans hup)
      hup hvT
    exact comb_step hβ hsk (hvc n (by omega) (hbj n (by omega) hb)) hb.le
  have hlam : ∀ t, s ≤ t → lam κ ϑ x π t ≤ 0 := by
    intro t ht
    rcases (hpos t).eq_or_lt with h | h
    · exact hslack t h.symm
    · have hg := hbind t (by omega) h
      rw [hgl t] at hg
      have := hV (t + 1) (by omega)
      simp only [hv] at this
      have hrl : r * lam κ ϑ x π t ≤ 0 := by linarith
      by_contra hc
      push Not at hc
      linarith [mul_pos hr0 hc]
  have hcc : 1 + 1 / β < 1 + 1 / β + κ / (β * σ) := by
    have : 0 < κ / (β * σ) := by positivity
    linarith
  exact mult_zero_right hβ hcc hpos h0 (fun t ht => by
    rw [← hmult t]
    exact mul_nonpos_of_nonneg_of_nonpos hκ.le (hlam t ht.le)) hlim

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), p. 152: **the rate lifts off in finite time**
(`ρ > 0`): some date after the shock has a zero multiplier. If the bound bound forever, inflation
would converge to the deflation steady state `−ρ` (`two_root`), the multiplier combination would
stay below `−ρ/2`, and the multipliers would either explode (violating `β^t ξ₂,t → 0`) or turn
negative. -/
theorem exists_slack_after {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) :
    ∃ s, tZ < s ∧ mxi2 β κ σ ϑ x π s = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨hF, hK⟩, hlim⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  set ξ2 := mxi2 β κ σ ϑ x π with hξ2
  have hN : ∀ t, NKPC β κ x π t := fun t => (hF t).1
  have hS := tendsto_pi_sq hβ hϑ hopt.2.1
  have hmult : ∀ t, κ * lam κ ϑ x π t =
      (1 + 1 / β + κ / (β * σ)) * ξ2 t - ξ2 (t + 1) - lag ξ2 t / β :=
    fun t => lam_mult hκ.ne' (hK (t + 1)).1 (hK t).2.1 (hK (t + 1)).2.1
  have hpos : ∀ t, 0 ≤ ξ2 t := fun t => (hK t).2.2.1
  have hb : ∀ t, tZ < t → 0 < ξ2 t :=
    fun t ht => lt_of_le_of_ne (hpos t) (Ne.symm (hcon t ht))
  have hgap : ∀ t, tZ < t → gap σ x π t = -ρ := by
    intro t ht
    have := (mul_eq_zero.mp (hK t).2.2.2).resolve_left (hb t ht).ne'
    rw [impliedRate_eq_gap, natRate_of_lt ht] at this
    linarith
  set e : ℕ → ℝ := fun n => π n + ρ with he
  have hab : σ / κ * (κ / σ) = 1 := by field_simp
  have hrec : ∀ n, tZ + 1 ≤ n → β * e (n + 2) - (1 + β + κ / σ) * e (n + 1) + e n = 0 := by
    intro n hn
    have h := hgap n (by omega)
    rw [gap_comb hκ.ne' (hN n) (hN (n + 1))] at h
    unfold comb at h
    simp only [he]
    linear_combination (-(κ / σ)) * h +
      ((π (n + 1) - π n) + β * (π (n + 1) - π (n + 2))) * hab
  have heT : Tendsto (fun n => β ^ n * e n ^ 2) atTop (𝓝 0) := by
    have h2 := (hS.const_mul 2).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).const_mul (2 * ρ ^ 2))
    rw [mul_zero, mul_zero, add_zero] at h2
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) h2
    simp only [he]
    have hp : 0 ≤ β ^ n := pow_nonneg hβ.le n
    have : (π n + ρ) ^ 2 ≤ 2 * π n ^ 2 + 2 * ρ ^ 2 := by nlinarith [sq_nonneg (π n - ρ)]
    nlinarith
  have hks : 0 < κ * σ := by positivity
  set μ := del β κ (κ * σ) with hμ
  have hμ0 : 0 < μ := del_pos hβ hks
  have hμ1 : μ < 1 := (del_lt_one_iff hβ hβ1 hks).mpr hκ.ne'
  have hq : β * μ ^ 2 - (1 + β + κ / σ) * μ + 1 = 0 := by
    have := del_root (κ := κ) hβ hβ1 hks
    rw [show κ ^ 2 / (κ * σ) = κ / σ by field_simp] at this
    exact this
  have hgeo := two_root hβ hβ1 hμ0 hμ1 hq hrec heT
  have hpow : ∀ j, e (tZ + 1 + j) = μ ^ j * e (tZ + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show tZ + 1 + (j + 1) = (tZ + 1 + j) + 1 by omega, hgeo _ (by omega), ih, pow_succ]
      ring
  set r := σ * κ / ϑ with hrdef
  have hr0 : 0 < r := by positivity
  have hlamf : ∀ t, tZ < t → lam κ ϑ x π t = -ρ + (r - 1) / r * e (t + 1) := by
    intro t ht
    have h := gap_lam (σ := σ) hκ.ne' hϑ.ne' x π t
    rw [hgap t ht] at h
    simp only [he]
    field_simp
    linarith
  have hT : Tendsto (fun t => (r - 1) / r * e (t + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℕ => μ ^ (t - tZ)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hμ0.le hμ1).comp (tendsto_sub_atTop_nat tZ)
    have h2 := h1.const_mul ((r - 1) / r * e (tZ + 1))
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop tZ] with t ht
    rw [show t + 1 = tZ + 1 + (t - tZ) by omega, hpow]
    ring
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp ((tendsto_order.1 hT).2 (ρ / 2) (by linarith))
  set T0 := max N1 (tZ + 1) with hT0
  have hlamT : ∀ t, T0 ≤ t → κ * lam κ ϑ x π t < -(κ * ρ / 2) := by
    intro t ht
    rw [hlamf t (by omega)]
    have := hN1 t (by omega)
    nlinarith
  have hcc : 0 < κ / (β * σ) := by positivity
  by_cases hA : ∃ t0, T0 ≤ t0 ∧ ξ2 t0 < ξ2 (t0 + 1)
  · obtain ⟨t0, ht0, hlt⟩ := hA
    refine not_tendsto_lin hβ hpos (n0 := t0) (fun n hn _ _ => ?_)
      (lt_of_le_of_lt (hpos t0) hlt) hlt hlim
    have h1 := hlamT (n + 1) (by omega)
    rw [hmult (n + 1)] at h1
    simp only [lag_succ] at h1
    rw [show n + 1 + 1 = n + 2 by omega] at h1
    have h2 : 0 ≤ κ / (β * σ) * ξ2 (n + 1) := mul_nonneg hcc.le (hpos _)
    have e1 : (ξ2 (n + 1) - ξ2 n) / β = 1 / β * ξ2 (n + 1) - ξ2 n / β := by ring
    rw [e1]
    nlinarith
  · push Not at hA
    have hdec : ∀ t, T0 ≤ t → ξ2 (t + 1) - ξ2 t ≤ -(β * κ * ρ / 2) := by
      intro t ht
      have h1 := hlamT (t + 1) (by omega)
      rw [hmult (t + 1)] at h1
      simp only [lag_succ] at h1
      have h3 := hA (t + 1) (by omega)
      have h2 : 0 ≤ κ / (β * σ) * ξ2 (t + 1) := mul_nonneg hcc.le (hpos _)
      have h4 : (ξ2 (t + 1) - ξ2 t) / β < -(κ * ρ / 2) := by
        have e1 : (ξ2 (t + 1) - ξ2 t) / β = 1 / β * ξ2 (t + 1) - ξ2 t / β := by ring
        rw [e1]
        nlinarith
      rw [div_lt_iff₀ hβ] at h4
      nlinarith
    have hlin : ∀ k : ℕ, ξ2 (T0 + k) ≤ ξ2 T0 - k * (β * κ * ρ / 2) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have := hdec (T0 + k) (by omega)
        rw [show T0 + (k + 1) = T0 + k + 1 by omega]
        push_cast
        linarith
    have hd : 0 < β * κ * ρ / 2 := by positivity
    obtain ⟨k, hk⟩ := exists_nat_gt (ξ2 T0 / (β * κ * ρ / 2))
    have h1 := hlin k
    have h2 : ξ2 T0 < k * (β * κ * ρ / 2) := by rwa [div_lt_iff₀ hd] at hk
    linarith [hpos (T0 + k)]

/-! ## Galí's closed form after lift-off is necessary -/

/-- Galí (2015), eqs. (37)–(43), pp. 149–150; Cochrane (2023), p. 479: **after the last binding
date `t_B` the optimum follows Galí's closed form**: if the multipliers vanish from `t_B + 1` on,
then `ξ₁,t_B+1+k = δᵏ ξ`, `π_{t_B+2+k} = (1 − δ)δᵏ ξ`, `x_{t_B+2+k} = κδ^{k+1}ξ/ϑ` with
`ξ = ξ₁,t_B+1` (the unstable root is excluded by the finite loss, `two_root`). -/
theorem post_form {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    {rn x π : ℕ → ℝ} (hopt : Optimal β κ σ ϑ rn x π) {tB : ℕ}
    (hz : ∀ t, tB + 1 ≤ t → mxi2 β κ σ ϑ x π t = 0) (k : ℕ) :
    x (tB + k + 2) = postX β κ ϑ (mxi1 β κ σ ϑ x π (tB + 1)) k ∧
      π (tB + k + 2) = postPi β κ ϑ (mxi1 β κ σ ϑ x π (tB + 1)) k ∧
      mxi1 β κ σ ϑ x π (tB + k + 2) = postXi β κ ϑ (mxi1 β κ σ ϑ x π (tB + 1)) (k + 1) ∧
      mxi2 β κ σ ϑ x π (tB + k + 2) = 0 := by
  have h35 := foc35_mult β κ σ ϑ x π
  have h36 := foc36_mult β κ σ ϑ x π
  set ξ1 := mxi1 β κ σ ϑ x π with hξ1
  set ξ2 := mxi2 β κ σ ϑ x π with hξ2
  have hN : ∀ t, NKPC β κ x π t := fun t => (hopt.1 t).1
  have hx : ∀ n, tB + 1 ≤ n → x (n + 1) = κ / ϑ * ξ1 (n + 1) := by
    intro n hn
    have h := h36 (n + 1)
    unfold FOC36 at h
    rw [lag_succ, hz n hn, hz (n + 1) (by omega)] at h
    simp only [zero_div, sub_zero, add_zero] at h
    field_simp
    linarith
  have hp : ∀ n, tB + 1 ≤ n → π (n + 1) = ξ1 n - ξ1 (n + 1) := by
    intro n hn
    have h := h35 (n + 1)
    unfold FOC35 at h
    rw [lag_succ, lag_succ, hz n hn] at h
    simp only [zero_div, sub_zero] at h
    linarith
  have hrec : ∀ n, tB + 1 ≤ n →
      β * ξ1 (n + 2) - (1 + β + κ ^ 2 / ϑ) * ξ1 (n + 1) + ξ1 n = 0 := by
    intro n hn
    have h := hN (n + 1)
    unfold NKPC at h
    rw [hp n hn, hp (n + 1) (by omega), hx n hn] at h
    rw [show n + 1 + 1 = n + 2 by omega] at h
    linear_combination h
  have hT : Tendsto (fun n => β ^ n * ξ1 n ^ 2) atTop (𝓝 0) := by
    have hxs : Summable (fun n => β ^ n * x n ^ 2) := by
      refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
        (hopt.2.1.div_const ϑ)
      unfold lossTerm
      rw [le_div_iff₀ hϑ]
      have : 0 ≤ β ^ t * π t ^ 2 * ϑ := by positivity
      nlinarith
    have h1 := hxs.tendsto_atTop_zero.const_mul ((ϑ / κ) ^ 2)
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (tB + 2)] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hx m (by omega)]
    field_simp
  have hδ0 := del_pos (κ := κ) hβ hϑ
  have hδ1 := (del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  have hgeo := two_root hβ hβ1 hδ0 hδ1 (del_root hβ hβ1 hϑ) hrec hT
  have hpow : ∀ j, ξ1 (tB + 1 + j) = del β κ ϑ ^ j * ξ1 (tB + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show tB + 1 + (j + 1) = (tB + 1 + j) + 1 by omega, hgeo _ (by omega), ih, pow_succ]
      ring
  have e1 : ξ1 (tB + k + 2) = del β κ ϑ ^ (k + 1) * ξ1 (tB + 1) := by
    rw [show tB + k + 2 = tB + 1 + (k + 1) by omega, hpow]
  have e0 : ξ1 (tB + k + 1) = del β κ ϑ ^ k * ξ1 (tB + 1) := by
    rw [show tB + k + 1 = tB + 1 + k by omega, hpow]
  refine ⟨?_, ?_, ?_, hz _ (by omega)⟩
  · rw [show tB + k + 2 = (tB + k + 1) + 1 by omega, hx _ (by omega),
      show tB + k + 1 + 1 = tB + k + 2 by omega, e1]
    unfold postX
    ring
  · rw [show tB + k + 2 = (tB + k + 1) + 1 by omega, hp _ (by omega),
      show tB + k + 1 + 1 = tB + k + 2 by omega, e1, e0]
    unfold postPi
    ring
  · rw [e1]
    unfold postXi
    ring

/-! ## The zero-rate spell is an initial interval -/

/-- Cochrane (2023), §20.2.4, pp. 478–479, Galí (2015), §5.4.2 (`ρ, η > 0`): **the binding set
of the optimum**. There is `t_B ≥ t_Z` such that the zero-bound multiplier is positive
exactly on `[0, t_B]` (so `i = 0` there), and the interest rate is strictly positive at every
date after `t_B + 1`. -/
theorem optimal_binding {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) :
    ∃ tB, tZ ≤ tB ∧ (∀ t, t ≤ tB → 0 < mxi2 β κ σ ϑ x π t) ∧
      (∀ t, tB < t → mxi2 β κ σ ϑ x π t = 0) ∧
      (∀ t, t ≤ tB → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      (∀ t, tB + 1 < t → 0 < impliedRate σ (natRate ρ η tZ) x π t) := by
  classical
  obtain ⟨⟨hF, hK⟩, -⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  have hex := exists_slack_after hβ hβ1 hκ hσ hϑ hρ hopt
  set s0 := Nat.find hex with hs0
  obtain ⟨hs0Z, hs0z⟩ := Nat.find_spec hex
  obtain ⟨tB, htB⟩ : ∃ tB, s0 = tB + 1 := ⟨s0 - 1, by omega⟩
  have htBZ : tZ ≤ tB := by omega
  have hposB : ∀ t, t ≤ tB → 0 < mxi2 β κ σ ϑ x π t := by
    intro t ht
    rcases le_or_gt t tZ with h | h
    · exact (optimal_trap_binds hβ hβ1 hκ hσ hϑ hρ.le hη hopt t h).2
    · have hmin := Nat.find_min hex (show t < Nat.find hex by omega)
      push Not at hmin
      exact lt_of_le_of_ne (hK t).2.2.1 (Ne.symm (hmin h))
  have hzero : ∀ t, tB < t → mxi2 β κ σ ϑ x π t = 0 := by
    intro t ht
    have := no_return hβ hβ1 hκ hσ hϑ hρ.le hopt hs0Z hs0z
    exact this t (by omega)
  have hrate0 : ∀ t, t ≤ tB → impliedRate σ (natRate ρ η tZ) x π t = 0 :=
    fun t ht => (mul_eq_zero.mp (hK t).2.2.2).resolve_left (hposB t ht).ne'
  refine ⟨tB, htBZ, hposB, hzero, hrate0, fun t ht => ?_⟩
  have hpost := post_form hβ hβ1 hκ hϑ hopt (tB := tB) fun t ht => hzero t (by omega)
  set ξ := mxi1 β κ σ ϑ x π (tB + 1) with hξ
  set δ := del β κ ϑ with hδ
  have hδ0 : 0 < δ := del_pos hβ hϑ
  have hδ1 : δ < 1 := (del_lt_one_iff hβ hβ1 hϑ).mpr hκ.ne'
  set A := (1 - δ) * (1 - σ * κ / ϑ) * ξ with hA
  have hrk : ∀ k, impliedRate σ (natRate ρ η tZ) x π (tB + k + 2) = ρ + A * δ ^ (k + 1) := by
    intro k
    rw [post_rate hϑ.ne' htBZ (fun k => (hpost k).1) (fun k => (hpost k).2.1) k, hA]
    ring
  have hr1 : impliedRate σ (natRate ρ η tZ) x π (tB + 1) < ρ + A := by
    have h36 := foc36_mult β κ σ ϑ x π (tB + 1)
    unfold FOC36 at h36
    rw [lag_succ, hzero (tB + 1) (by omega), ← hξ] at h36
    have hx1 : x (tB + 1) = (κ * ξ + mxi2 β κ σ ϑ x π tB / β) / ϑ := by
      rw [eq_div_iff hϑ.ne']
      linarith
    have hp := hposB tB le_rfl
    have e1 : impliedRate σ (natRate ρ η tZ) x π (tB + 1) =
        ρ + A - σ * (mxi2 β κ σ ϑ x π tB / β) / ϑ := by
      unfold impliedRate
      rw [natRate_of_lt (by omega), show tB + 1 + 1 = tB + 0 + 2 by omega, (hpost 0).1,
        (hpost 0).2.1, hx1, hA]
      unfold postX postPi
      field_simp
      ring
    rw [e1]
    have : 0 < σ * (mxi2 β κ σ ϑ x π tB / β) / ϑ := by positivity
    linarith
  obtain ⟨k, rfl⟩ : ∃ k, t = tB + k + 2 := ⟨t - tB - 2, by omega⟩
  rw [hrk k]
  by_contra hc
  push Not at hc
  have hprev : A * δ ^ k < -ρ := by
    by_contra h'
    push Not at h'
    have e : A * δ ^ (k + 1) = A * δ ^ k * δ := by ring
    rw [e] at hc
    rcases le_or_gt 0 (A * δ ^ k) with h0 | h0
    · have : 0 ≤ A * δ ^ k * δ := mul_nonneg h0 hδ0.le
      linarith
    · have : -ρ * δ ≤ A * δ ^ k * δ := mul_le_mul_of_nonneg_right h' hδ0.le
      nlinarith
  rcases k with _ | j
  · have := rate_nonneg hσ hF (tB + 1)
    simp only [pow_zero, mul_one] at hprev
    linarith
  · have := rate_nonneg hσ hF (tB + j + 2)
    rw [hrk j] at this
    rw [show j + 1 = j + 1 from rfl] at hprev
    linarith

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), p. 152 (`ρ, η > 0`): **the zero-rate spell
is an initial interval**: there is `t_C ≥ t_Z` with `i_t = 0` exactly for `t ≤ t_C` and
`i_t > 0` for every `t > t_C` (no re-binding after lift-off). -/
theorem optimal_liftoff {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) :
    ∃ tC, tZ ≤ tC ∧ (∀ t, t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      ∀ t, tC < t → 0 < impliedRate σ (natRate ρ η tZ) x π t := by
  obtain ⟨tB, htB, -, -, h0, hpos⟩ := optimal_binding hβ hβ1 hκ hσ hϑ hρ hη hopt
  rcases (rate_nonneg hσ hopt.1 (tB + 1)).eq_or_lt with h | h
  · refine ⟨tB + 1, by omega, fun t ht => ?_, fun t ht => hpos t ht⟩
    rcases ht.eq_or_lt with rfl | ht'
    · exact h.symm
    · exact h0 t (by omega)
  · refine ⟨tB, htB, h0, fun t ht => ?_⟩
    rcases (show tB + 1 = t ∨ tB + 1 < t by omega) with rfl | ht'
    · exact h
    · exact hpos t ht'

/-- Galí (2015), p. 152; Cochrane (2023), p. 479 (`ρ, η > 0`): **the optimum is always found by
Galí's algorithm**: with the multipliers `mult` and `t_C` the last binding date, every hypothesis
of `algorithm_verification` holds — `t_Z ≤ t_C`, (48), (49), (35)–(36) on `[0, t_C + 1]`, (46),
`ξ₂,t_C+1 = 0`, the closed form (42)–(43) after lift-off, `ξ₂ ≥ 0` on `[0, t_C]`, and
`i ≥ 0` at `t_C + 1`, `t_C + 2`. -/
theorem optimal_algorithm_form {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) :
    ∃ tC, tZ ≤ tC ∧
      (∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1))) ∧
      (∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1))) ∧
      (∀ t, t ≤ tC + 1 → FOC35 β σ π (mxi1 β κ σ ϑ x π) (mxi2 β κ σ ϑ x π) t ∧
        FOC36 β κ ϑ x (mxi1 β κ σ ϑ x π) (mxi2 β κ σ ϑ x π) t) ∧
      NKPC β κ x π (tC + 1) ∧ mxi2 β κ σ ϑ x π (tC + 1) = 0 ∧
      (∀ k, x (tC + k + 2) = postX β κ ϑ (mxi1 β κ σ ϑ x π (tC + 1)) k ∧
        π (tC + k + 2) = postPi β κ ϑ (mxi1 β κ σ ϑ x π (tC + 1)) k ∧
        mxi1 β κ σ ϑ x π (tC + k + 2) = postXi β κ ϑ (mxi1 β κ σ ϑ x π (tC + 1)) (k + 1) ∧
        mxi2 β κ σ ϑ x π (tC + k + 2) = 0) ∧
      (∀ t, t ≤ tC → 0 ≤ mxi2 β κ σ ϑ x π t) ∧
      0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 1) ∧
      0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 2) := by
  obtain ⟨tB, htB, hpos, hz, h0, -⟩ := optimal_binding hβ hβ1 hκ hσ hϑ hρ hη hopt
  refine ⟨tB, htB, optimal_h48 hβ hβ1 hκ hσ hϑ hρ.le hη hopt, fun t h1 h2 => ?_,
    fun t _ => ⟨foc35_mult β κ σ ϑ x π t, foc36_mult β κ σ ϑ x π t⟩, (hopt.1 _).1,
    hz _ (by omega), post_form hβ hβ1 hκ hϑ hopt fun t ht => hz t (by omega),
    fun t ht => (hpos t ht).le, rate_nonneg hσ hopt.1 _, rate_nonneg hσ hopt.1 _⟩
  refine backStep_of_rate hσ.ne' (rn := natRate ρ η tZ) (hopt.1 t).1 ?_
  rw [h0 t h2, natRate_of_lt h1]
  ring

/-! ## Existence of the commitment optimum -/

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: the Hilbert space `ℓ²(ℕ ⊕ ℕ)` of weighted
paths, whose squared norm is the loss (`loss_dec`). -/
abbrev PathSpace : Type := lp (fun _ : ℕ ⊕ ℕ => ℝ) 2

/-- Galí (2015), p. 148: the inflation path coded by `z`, `π_t = z(inl t)/√β^t`. -/
noncomputable def decP (β : ℝ) (z : ℕ ⊕ ℕ → ℝ) (t : ℕ) : ℝ := z (Sum.inl t) / Real.sqrt β ^ t

/-- Galí (2015), p. 148: the output-gap path coded by `z`, `x_t = z(inr t)/(√β^t √ϑ)`. -/
noncomputable def decX (β ϑ : ℝ) (z : ℕ ⊕ ℕ → ℝ) (t : ℕ) : ℝ :=
  z (Sum.inr t) / (Real.sqrt β ^ t * Real.sqrt ϑ)

/-- Galí (2015), p. 148: the code of a path `(x, π)`. -/
noncomputable def enc (β ϑ : ℝ) (x π : ℕ → ℝ) : ℕ ⊕ ℕ → ℝ :=
  Sum.elim (fun t => Real.sqrt β ^ t * π t) (fun t => Real.sqrt β ^ t * Real.sqrt ϑ * x t)

/-- Galí (2015), p. 148: `(√β^t)² = β^t`. -/
theorem sqrt_pow_sq {β : ℝ} (hβ : 0 ≤ β) (t : ℕ) : (Real.sqrt β ^ t) ^ 2 = β ^ t := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hβ]

/-- Galí (2015), p. 148: decoding a code returns the inflation path. -/
theorem decP_enc {β : ℝ} (hβ : 0 < β) (ϑ : ℝ) (x π : ℕ → ℝ) : decP β (enc β ϑ x π) = π := by
  funext t
  have : Real.sqrt β ^ t ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.mpr hβ).ne'
  simp only [decP, enc, Sum.elim_inl]
  field_simp

/-- Galí (2015), p. 148: decoding a code returns the output-gap path. -/
theorem decX_enc {β ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) (x π : ℕ → ℝ) :
    decX β ϑ (enc β ϑ x π) = x := by
  funext t
  have : Real.sqrt β ^ t ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.mpr hβ).ne'
  have : Real.sqrt ϑ ≠ 0 := (Real.sqrt_pos.mpr hϑ).ne'
  simp only [decX, enc, Sum.elim_inr]
  field_simp

/-- Galí (2015), p. 148: the loss term of a decoded path is `z(inl t)² + z(inr t)²`. -/
theorem lossTerm_dec {β ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) (z : ℕ ⊕ ℕ → ℝ) (t : ℕ) :
    lossTerm β ϑ (decX β ϑ z) (decP β z) t = z (Sum.inl t) ^ 2 + z (Sum.inr t) ^ 2 := by
  have h1 : Real.sqrt β ^ t ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.mpr hβ).ne'
  have h2 : Real.sqrt ϑ ≠ 0 := (Real.sqrt_pos.mpr hϑ).ne'
  unfold lossTerm decX decP
  rw [div_pow, div_pow, mul_pow, sqrt_pow_sq hβ.le, Real.sq_sqrt hϑ.le]
  have : β ^ t ≠ 0 := pow_ne_zero _ hβ.ne'
  field_simp

/-- Galí (2015), p. 148: the squares of an `ℓ²` element are summable. -/
theorem summable_sq (z : PathSpace) : Summable (fun i => z i ^ 2) := by
  have h := (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).1 (lp.memℓp z)
  refine h.congr fun i => ?_
  rw [Real.norm_eq_abs, show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two, sq_abs]

/-- Galí (2015), p. 148: `‖z‖² = ∑ z_i²`. -/
theorem norm_sq_eq (z : PathSpace) : ‖z‖ ^ 2 = ∑' i, z i ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) z
  rw [show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two] at h
  rw [h]
  congr 1
  funext i
  rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]

/-- Galí (2015), p. 148; Cochrane (2023), p. 485: **the loss of a decoded path is the squared
norm**, and it is finite. -/
theorem loss_dec {β ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) (z : PathSpace) :
    Summable (lossTerm β ϑ (decX β ϑ z) (decP β z)) ∧
      loss β ϑ (decX β ϑ z) (decP β z) = ‖z‖ ^ 2 := by
  set f : ℕ ⊕ ℕ → ℝ := fun i => z i ^ 2 with hf
  have hs : Summable f := summable_sq z
  have h1 : Summable (f ∘ Sum.inl) := hs.comp_injective Sum.inl_injective
  have h2 : Summable (f ∘ Sum.inr) := hs.comp_injective Sum.inr_injective
  have e : lossTerm β ϑ (decX β ϑ z) (decP β z) = fun t => (f ∘ Sum.inl) t + (f ∘ Sum.inr) t :=
    funext fun t => lossTerm_dec hβ hϑ z t
  refine ⟨by rw [e]; exact h1.add h2, ?_⟩
  have h3 : ∑' i, f i = ∑' t, (f ∘ Sum.inl) t + ∑' t, (f ∘ Sum.inr) t := Summable.tsum_sum h1 h2
  unfold loss
  rw [e, h1.tsum_add h2, norm_sq_eq, ← h3]

/-- Galí (2015), p. 148: a path with finite loss has an `ℓ²` code. -/
theorem memℓp_enc {β ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {x π : ℕ → ℝ}
    (hs : Summable (lossTerm β ϑ x π)) : Memℓp (enc β ϑ x π) 2 := by
  refine (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).2 ?_
  have e : (fun i => ‖enc β ϑ x π i‖ ^ (2 : ENNReal).toReal) = fun i => enc β ϑ x π i ^ 2 := by
    funext i
    rw [Real.norm_eq_abs, show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two,
      sq_abs]
  rw [e]
  refine Summable.sum _ ?_ ?_
  · refine Summable.of_nonneg_of_le (fun t => sq_nonneg _) (fun t => ?_) hs
    simp only [Function.comp, enc, Sum.elim_inl, lossTerm]
    rw [mul_pow, sqrt_pow_sq hβ.le]
    have : 0 ≤ β ^ t * (ϑ * x t ^ 2) := by positivity
    nlinarith
  · refine Summable.of_nonneg_of_le (fun t => sq_nonneg _) (fun t => ?_) hs
    simp only [Function.comp, enc, Sum.elim_inr, lossTerm]
    rw [mul_pow, mul_pow, sqrt_pow_sq hβ.le, Real.sq_sqrt hϑ.le]
    have : 0 ≤ β ^ t * π t ^ 2 := by positivity
    nlinarith

/-- Galí (2015), p. 149: a convex combination of feasible paths is feasible. -/
theorem feasible_convex {β κ σ a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {rn x π y q : ℕ → ℝ} (hab : a + b = 1)
    (h1 : Feasible β κ σ rn x π) (h2 : Feasible β κ σ rn y q) :
    Feasible β κ σ rn (fun t => a * x t + b * y t) (fun t => a * π t + b * q t) := by
  intro t
  obtain ⟨n1, u1⟩ := h1 t
  obtain ⟨n2, u2⟩ := h2 t
  unfold NKPC at n1 n2 ⊢
  unfold ups1 at u1 u2 ⊢
  simp only
  refine ⟨by rw [n1, n2]; ring, ?_⟩
  have e : a * x (t + 1) + b * y (t + 1) + (a * π (t + 1) + b * q (t + 1) + rn t) / σ =
      a * (x (t + 1) + (π (t + 1) + rn t) / σ) + b * (y (t + 1) + (q (t + 1) + rn t) / σ) := by
    linear_combination (-(rn t / σ)) * hab
  rw [e]
  have := mul_le_mul_of_nonneg_left u1 ha
  have := mul_le_mul_of_nonneg_left u2 hb
  linarith

/-- Galí (2015), p. 149: the codes of feasible paths. -/
def feasSet (β κ σ ϑ : ℝ) (rn : ℕ → ℝ) : Set PathSpace :=
  {z | Feasible β κ σ rn (decX β ϑ z) (decP β z)}

/-- Galí (2015), p. 148: evaluation at a coordinate is continuous on `ℓ²`. -/
theorem coord_continuous (i : ℕ ⊕ ℕ) : Continuous fun z : PathSpace => z i :=
  (continuous_apply i).comp lp.uniformContinuous_coe.continuous

/-- Galí (2015), p. 149: the feasible set (Phillips curve and `i ≥ 0` at every date) is closed. -/
theorem feasSet_closed (β κ σ ϑ : ℝ) (rn : ℕ → ℝ) : IsClosed (feasSet β κ σ ϑ rn) := by
  have hP : ∀ t, Continuous fun z : PathSpace => decP β z t := fun t => by
    simp only [decP]; exact (coord_continuous _).div_const _
  have hX : ∀ t, Continuous fun z : PathSpace => decX β ϑ z t := fun t => by
    simp only [decX]; exact (coord_continuous _).div_const _
  have e : feasSet β κ σ ϑ rn = ⋂ t, ({z : PathSpace |
      decP β z t = β * decP β z (t + 1) + κ * decX β ϑ z t} ∩
      {z | decX β ϑ z t ≤ decX β ϑ z (t + 1) + (decP β z (t + 1) + rn t) / σ}) := by
    ext z
    simp only [feasSet, Feasible, NKPC, ups1, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [e]
  exact isClosed_iInter fun t =>
    (isClosed_eq (hP t) (((hP _).const_mul β).add ((hX t).const_mul κ))).inter
      (isClosed_le (hX t) ((hX _).add (((hP _).add continuous_const).div_const σ)))

/-- Galí (2015), p. 149: the feasible set is convex. -/
theorem feasSet_convex (β κ σ ϑ : ℝ) (rn : ℕ → ℝ) : Convex ℝ (feasSet β κ σ ϑ rn) := by
  intro z hz w hw a b ha hb hab
  have eP : decP β ⇑(a • z + b • w) = fun t => a * decP β z t + b * decP β w t := by
    funext t
    simp only [decP, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eX : decX β ϑ ⇑(a • z + b • w) = fun t => a * decX β ϑ z t + b * decX β ϑ w t := by
    funext t
    simp only [decX, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  change Feasible β κ σ rn (decX β ϑ ⇑(a • z + b • w)) (decP β ⇑(a • z + b • w))
  rw [eP, eX]
  exact feasible_convex ha hb hab hz hw

/-- Galí (2015), p. 148; Cochrane (2023), §20.2.4, p. 479: **existence of the commitment
optimum** for any natural-rate path for which some feasible path has finite loss: the loss is the
squared norm of the code in `ℓ²`, the feasible codes form a nonempty closed convex set, and the
element of minimal norm (projection of `0`, `exists_norm_eq_iInf_of_complete_convex`) is
optimal. -/
theorem exists_optimal {β κ σ ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hne : ∃ y q, Feasible β κ σ rn y q ∧ Summable (lossTerm β ϑ y q)) :
    ∃ x π, Optimal β κ σ ϑ rn x π := by
  obtain ⟨y0, q0, hF0, hS0⟩ := hne
  have hmem : ∀ y q, Feasible β κ σ rn y q → ∀ hs : Summable (lossTerm β ϑ y q),
      (⟨enc β ϑ y q, memℓp_enc hβ hϑ hs⟩ : PathSpace) ∈ feasSet β κ σ ϑ rn := by
    intro y q hy hs
    change Feasible β κ σ rn (decX β ϑ (enc β ϑ y q)) (decP β (enc β ϑ y q))
    rw [decX_enc hβ hϑ, decP_enc hβ]
    exact hy
  obtain ⟨v, hvK, hv⟩ := exists_norm_eq_iInf_of_complete_convex ⟨_, hmem y0 q0 hF0 hS0⟩
    (feasSet_closed β κ σ ϑ rn).isComplete (feasSet_convex β κ σ ϑ rn) 0
  obtain ⟨hsv, hlv⟩ := loss_dec hβ hϑ v
  refine ⟨decX β ϑ v, decP β v, hvK, hsv, fun y q hy hsy => ?_⟩
  set w : PathSpace := ⟨enc β ϑ y q, memℓp_enc hβ hϑ hsy⟩ with hw
  have hwK := hmem y q hy hsy
  have hle : ‖v‖ ≤ ‖w‖ := by
    have h1 : ‖(0 : PathSpace) - v‖ ≤ ‖(0 : PathSpace) - w‖ := by
      rw [hv]
      exact ciInf_le ⟨0, by rintro _ ⟨u, rfl⟩; exact norm_nonneg _⟩
        (⟨w, hwK⟩ : feasSet β κ σ ϑ rn)
    simpa only [zero_sub, norm_neg] using h1
  obtain ⟨-, hlw⟩ := loss_dec hβ hϑ w
  have e1 : decX β ϑ ⇑w = y := decX_enc hβ hϑ y q
  have e2 : decP β ⇑w = q := decP_enc hβ ϑ y q
  rw [e1, e2] at hlw
  rw [hlv, hlw]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-! ## The commitment optimum, fully characterised -/

/-- Galí (2015), §5.4.2, Cochrane (2023), §20.2.4: **the commitment optimum exists and is
unique** for all `β > 0`, `σ, ϑ > 0`, any `κ, η`, `ρ ≥ 0` and `t_Z` (discretion is feasible
with finite loss). -/
theorem optimal_exists_unique {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    (hρ : 0 ≤ ρ) (tZ : ℕ) :
    ∃ x π, Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      ∀ y q, Optimal β κ σ ϑ (natRate ρ η tZ) y q → y = x ∧ q = π := by
  obtain ⟨hF, hS⟩ := disc_feasible_summable (κ := κ) (ϑ := ϑ) (η := η) hσ hρ tZ
  obtain ⟨x, π, hopt⟩ := exists_optimal (κ := κ) (σ := σ) hβ hϑ ⟨_, _, hF, hS⟩
  exact ⟨x, π, hopt, fun y q h => optimal_unique hβ hϑ h hopt⟩

/-- Cochrane (2023), §20.2.4, pp. 478–480, and Galí (2015), §5.4.2, pp. 148–152: **the
commitment optimum, fully characterised** (`β ∈ (0,1)`, `κ, σ, ϑ, ρ, η > 0`, any `t_Z`): it
exists, it is unique, and there is a lift-off date `t_C ≥ t_Z` such that the interest rate is
zero exactly on `[0, t_C]` and strictly positive at every later date. Moreover it satisfies all
the conditions of Galí's algorithm (`optimal_algorithm_form`). -/
theorem commitment_characterisation {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) (tZ : ℕ) :
    ∃ x π, Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      (∀ y q, Optimal β κ σ ϑ (natRate ρ η tZ) y q → y = x ∧ q = π) ∧
      ∃ tC, tZ ≤ tC ∧ (∀ t, t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
        ∀ t, tC < t → 0 < impliedRate σ (natRate ρ η tZ) x π t := by
  obtain ⟨x, π, hopt, huniq⟩ := optimal_exists_unique (κ := κ) (η := η) hβ hσ hϑ hρ.le tZ
  exact ⟨x, π, hopt, huniq, optimal_liftoff hβ hβ1 hκ hσ hϑ hρ hη hopt⟩

/-! ## A zero post-shock natural rate (`ρ = 0`) -/

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), p. 152 (`ρ ≥ 0`): **rates after a finite
lift-off**. If some date after the shock has a zero multiplier, then with `t_B` the last binding
date (`t_Z ≤ t_B`, `ξ₂ > 0` exactly on `[0, t_B]`, `i = 0` there) and
`A = (1 − δ)(1 − σκ/ϑ) ξ₁,t_B+1`: `i_{t_B+1} < ρ + A` and `i_{t_B+2+k} = ρ + A δ^{k+1}`. -/
theorem liftoff_rates {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 ≤ ρ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π)
    (hex : ∃ s, tZ < s ∧ mxi2 β κ σ ϑ x π s = 0) :
    ∃ tB, tZ ≤ tB ∧ (∀ t, t ≤ tB → 0 < mxi2 β κ σ ϑ x π t) ∧
      (∀ t, tB < t → mxi2 β κ σ ϑ x π t = 0) ∧
      (∀ t, t ≤ tB → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      impliedRate σ (natRate ρ η tZ) x π (tB + 1) <
        ρ + (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * mxi1 β κ σ ϑ x π (tB + 1) ∧
      ∀ k, impliedRate σ (natRate ρ η tZ) x π (tB + k + 2) =
        ρ + (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * mxi1 β κ σ ϑ x π (tB + 1) *
          del β κ ϑ ^ (k + 1) := by
  classical
  obtain ⟨⟨-, hK⟩, -⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  set s0 := Nat.find hex with hs0
  obtain ⟨hs0Z, hs0z⟩ := Nat.find_spec hex
  obtain ⟨tB, htB⟩ : ∃ tB, s0 = tB + 1 := ⟨s0 - 1, by omega⟩
  have htBZ : tZ ≤ tB := by omega
  have hposB : ∀ t, t ≤ tB → 0 < mxi2 β κ σ ϑ x π t := by
    intro t ht
    rcases le_or_gt t tZ with h | h
    · exact (optimal_trap_binds hβ hβ1 hκ hσ hϑ hρ hη hopt t h).2
    · have hmin := Nat.find_min hex (show t < Nat.find hex by omega)
      push Not at hmin
      exact lt_of_le_of_ne (hK t).2.2.1 (Ne.symm (hmin h))
  have hzero : ∀ t, tB < t → mxi2 β κ σ ϑ x π t = 0 := by
    intro t ht
    exact no_return hβ hβ1 hκ hσ hϑ hρ hopt hs0Z hs0z t (by omega)
  have hrate0 : ∀ t, t ≤ tB → impliedRate σ (natRate ρ η tZ) x π t = 0 :=
    fun t ht => (mul_eq_zero.mp (hK t).2.2.2).resolve_left (hposB t ht).ne'
  have hpost := post_form hβ hβ1 hκ hϑ hopt (tB := tB) fun t ht => hzero t (by omega)
  set ξ := mxi1 β κ σ ϑ x π (tB + 1) with hξ
  set A := (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * ξ with hA
  refine ⟨tB, htBZ, hposB, hzero, hrate0, ?_, fun k => ?_⟩
  · have h36 := foc36_mult β κ σ ϑ x π (tB + 1)
    unfold FOC36 at h36
    rw [lag_succ, hzero (tB + 1) (by omega), ← hξ] at h36
    have hx1 : x (tB + 1) = (κ * ξ + mxi2 β κ σ ϑ x π tB / β) / ϑ := by
      rw [eq_div_iff hϑ.ne']
      linarith
    have hp := hposB tB le_rfl
    have e1 : impliedRate σ (natRate ρ η tZ) x π (tB + 1) =
        ρ + A - σ * (mxi2 β κ σ ϑ x π tB / β) / ϑ := by
      unfold impliedRate
      rw [natRate_of_lt (by omega), show tB + 1 + 1 = tB + 0 + 2 by omega, (hpost 0).1,
        (hpost 0).2.1, hx1, hA]
      unfold postX postPi
      field_simp
      ring
    rw [e1]
    have : 0 < σ * (mxi2 β κ σ ϑ x π tB / β) / ϑ := by positivity
    linarith
  · rw [post_rate hϑ.ne' htBZ (fun k => (hpost k).1) (fun k => (hpost k).2.1) k, hξ]
    ring

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), §5.4.2: **the binding set when the
post-shock natural rate is zero** (`ρ = 0`; the optimum exists and is unique,
`optimal_exists_unique`). The zero bound still binds on the whole shock and never re-binds after
a lift-off (`optimal_trap_binds`, `no_return`), and exactly one of the following holds: either
the rate is zero at every date, or `σκ ≠ ϑ` and there is `t_C ≥ t_Z` with `i = 0` exactly on
`[0, t_C]` and `i > 0` afterwards. -/
theorem rho_zero_structure {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hη : 0 < η) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate 0 η tZ) x π) :
    (∀ t, impliedRate σ (natRate 0 η tZ) x π t = 0) ∨
      (σ * κ ≠ ϑ ∧ ∃ tC, tZ ≤ tC ∧ (∀ t, t ≤ tC → impliedRate σ (natRate 0 η tZ) x π t = 0) ∧
        ∀ t, tC < t → 0 < impliedRate σ (natRate 0 η tZ) x π t) := by
  obtain ⟨⟨hF, hK⟩, -⟩ := kkt_necessary hβ hβ1 hκ hσ hϑ hopt
  by_cases hex : ∃ s, tZ < s ∧ mxi2 β κ σ ϑ x π s = 0
  · right
    obtain ⟨tB, htB, -, -, h0, h1, hk⟩ := liftoff_rates hβ hβ1 hκ hσ hϑ le_rfl hη hopt hex
    set A := (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * mxi1 β κ σ ϑ x π (tB + 1) with hA
    have hδ0 : 0 < del β κ ϑ := del_pos hβ hϑ
    have hApos : 0 < A := by
      have := rate_nonneg hσ hF (tB + 1)
      linarith
    have hr : σ * κ ≠ ϑ := by
      intro h
      rw [hA, h, div_self hϑ.ne', sub_self, mul_zero, zero_mul] at hApos
      exact lt_irrefl _ hApos
    have hpos : ∀ t, tB + 1 < t → 0 < impliedRate σ (natRate 0 η tZ) x π t := by
      intro t ht
      obtain ⟨k, rfl⟩ : ∃ k, t = tB + k + 2 := ⟨t - tB - 2, by omega⟩
      rw [hk k, zero_add]
      positivity
    refine ⟨hr, ?_⟩
    rcases (rate_nonneg hσ hF (tB + 1)).eq_or_lt with h | h
    · refine ⟨tB + 1, by omega, fun t ht => ?_, fun t ht => hpos t ht⟩
      rcases ht.eq_or_lt with rfl | ht'
      · exact h.symm
      · exact h0 t (by omega)
    · refine ⟨tB, htB, h0, fun t ht => ?_⟩
      rcases (show tB + 1 = t ∨ tB + 1 < t by omega) with rfl | ht'
      · exact h
      · exact hpos t ht'
  · left
    push Not at hex
    intro t
    rcases le_or_gt t tZ with h | h
    · exact (optimal_trap_binds hβ hβ1 hκ hσ hϑ le_rfl hη hopt t h).1
    · exact (mul_eq_zero.mp (hK t).2.2.2).resolve_left
        (lt_of_le_of_ne (hK t).2.2.1 (Ne.symm (hex t h))).ne'

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), p. 152: **with `ρ = 0` and `σκ = ϑ` the
optimal interest rate is zero at every date** — the rate never lifts off. -/
theorem rho_zero_unit_ratio {β κ σ ϑ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hη : 0 < η) (hr : σ * κ = ϑ) {tZ : ℕ} {x π : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ (natRate 0 η tZ) x π) (t : ℕ) :
    impliedRate σ (natRate 0 η tZ) x π t = 0 := by
  rcases rho_zero_structure hβ hβ1 hκ hσ hϑ hη hopt with h | ⟨h, -⟩
  · exact h t
  · exact absurd hr h

/-- Cochrane (2023), §20.2.4 and Galí (2015), §5.4.2: **the hypothesis `ρ > 0` of
`commitment_characterisation` cannot be dropped**: for every `β ∈ (0,1)`, `κ, σ, η > 0`, `t_Z`,
with `ρ = 0` and `ϑ = σκ` the optimum exists and is unique, but no `t_C` has `i > 0` after it. -/
theorem rho_zero_no_liftoff {β κ σ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hη : 0 < η) (tZ : ℕ) :
    ∃ x π, Optimal β κ σ (σ * κ) (natRate 0 η tZ) x π ∧
      (∀ y q, Optimal β κ σ (σ * κ) (natRate 0 η tZ) y q → y = x ∧ q = π) ∧
      ¬ ∃ tC, ∀ t, tC < t → 0 < impliedRate σ (natRate 0 η tZ) x π t := by
  have hϑ : 0 < σ * κ := by positivity
  obtain ⟨x, π, hopt, hu⟩ := optimal_exists_unique (κ := κ) (η := η) hβ hσ hϑ le_rfl tZ
  refine ⟨x, π, hopt, hu, fun ⟨tC, h⟩ => ?_⟩
  have := h (tC + 1) (by omega)
  rw [rho_zero_unit_ratio hβ hβ1 hκ hσ hϑ hη rfl hopt] at this
  exact lt_irrefl _ this

/-- Cochrane (2023), §20.2.4, Galí (2015), §5.4.2: an exact instance (`β = 1/2`,
`κ = σ = ϑ = 1`, `η = 1`, `ρ = 0`, `t_Z = 0`): the unique optimum keeps the rate at zero forever. -/
theorem rho_zero_instance :
    ∃ x π, Optimal (1 / 2) 1 1 1 (natRate 0 1 0) x π ∧
      (∀ y q, Optimal (1 / 2) 1 1 1 (natRate 0 1 0) y q → y = x ∧ q = π) ∧
      ∀ t, impliedRate 1 (natRate 0 1 0) x π t = 0 := by
  obtain ⟨x, π, hopt, hu⟩ := optimal_exists_unique (β := (1 : ℝ) / 2) (κ := 1) (σ := 1)
    (ϑ := 1) (η := 1) (by norm_num) one_pos one_pos le_rfl 0
  exact ⟨x, π, hopt, hu, rho_zero_unit_ratio (by norm_num) (by norm_num) one_pos one_pos
    one_pos one_pos (by norm_num) hopt⟩

end Cochrane.ZeroBound.LiftoffStructure
