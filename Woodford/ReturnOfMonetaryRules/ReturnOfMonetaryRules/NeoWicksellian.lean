/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ReturnOfMonetaryRules.Expectations

/-!
# Neo-Wicksellian price-level determination

Woodford (2003), *Interest and Prices*, Chapter 1, §4.3, pp. 49–52.

The flexible-price IS (Fisher) relation (4.9) `p_t = E_t p_{t+1} + r_t − i_t` and the
Wicksellian rule (4.10) `i_t = ī_t + φ p_t` combine into (4.11)
`p_t = α E_t p_{t+1} + α(r_t − ī_t)`, `α = 1/(1 + φ)`. For `φ > 0` and bounded exogenous
`{r_t, ī_t}` the unique bounded solution is (4.12)
`p_t = ∑_{j ≥ 0} α^{j+1} E_t(r_{t+j} − ī_{t+j})`.

All statements hold for an arbitrary `ExpectationSystem`, so under perfect foresight and under
genuine uncertainty. A bounded equilibrium need not be assumed adapted.

## Main results

* `equilibrium_iff_reduced`: (4.9) + (4.10) ⇔ (4.11) whenever `1 + φ ≠ 0`; `alpha_mem`:
  `0 < α < 1` for `φ > 0`.
* `priceLevel_equilibrium`, `eq_priceLevel`, `existsUnique_priceLevel`: (4.12) is a bounded,
  adapted equilibrium and the only bounded one (via the core `forwardSeries_solves`,
  `eq_forwardSeries`).
* `priceLevel_const`: for constant `r̄, ī` the price level is `p̄ = φ⁻¹(r̄ − ī)`;
  `abs_sub_longRun_le`: the price level stays within `K/φ` of `p̄` when `r_t − ī_t` stays within
  `K` of `r̄ − ī`; `tendsto_longRun`: it converges (uniformly) to `p̄` when `r_t − ī_t` does to
  `r̄ − ī`.
* `equilibrium_mono` (p. 51): the price level rises with `r` and falls with `ī`.
* The role of `φ > 0`: `homog_equilibrium`, `not_unique_of_mem_Icc` (for `−2 ≤ φ ≤ 0`, every
  bounded equilibrium has a continuum of bounded companions, including the exogenous-rate
  case `φ = 0` and the degenerate `φ = −1`), `peg_no_bounded` (for `φ = 0` with a constant
  nonzero `r − ī` there is no bounded equilibrium at all) and the exact characterisation
  `existsUnique_iff`: a unique bounded equilibrium exists for every bounded adapted
  `{r, ī}` if and only if `φ > 0` or `φ < −2`. The book's sufficient condition `φ > 0` is thus
  not necessary (strongly negative responses `φ < −2` also determine an oscillating price
  level); this is recorded as a precision, not an error.

Footnote 44 and (4.13) (sticky prices, the Taylor principle) are forward pointers to
Chapters 2 and 4 and are not formalised here.
-/

namespace Woodford.ReturnOfMonetaryRules.NeoWicksellian

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eq. (4.9), p. 50: the flexible-price IS (Fisher) relation
`p_t = E_t p_{t+1} + r_t − i_t`. -/
def Fisher (r i p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, p t = 𝔼.E t (p (t + 1)) + r t - i t

/-- Woodford (2003), eq. (4.10), p. 50: an equilibrium price path under the Wicksellian rule
`i_t = ī_t + φ p_t`, i.e. (4.9) with the rule substituted for `i_t`. -/
def Equilibrium (φ : ℝ) (r ibar p : ℕ → Ω → ℝ) : Prop :=
  Fisher 𝔼 r (fun t => ibar t + φ • p t) p

/-- Woodford (2003), eq. (4.11), p. 51: `p_t = α E_t p_{t+1} + α(r_t − ī_t)`. -/
def Reduced (α : ℝ) (r ibar p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, p t = α • 𝔼.E t (p (t + 1)) + α • (r t - ibar t)

/-- Woodford (2003), eq. (4.12), p. 51: the forward solution
`p_t = ∑_{j ≥ 0} α^{j+1} E_t(r_{t+j} − ī_{t+j})`, `α = (1 + φ)⁻¹`. -/
noncomputable def priceLevel (φ : ℝ) (r ibar : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, (1 + φ)⁻¹ ^ (j + 1) * 𝔼.E t (r (t + j) - ibar (t + j)) ω

/-- Woodford (2003), p. 51: the coefficient `α = 1/(1 + φ)` satisfies `0 < α < 1` for `φ > 0`. -/
theorem alpha_mem {φ : ℝ} (hφ : 0 < φ) : 0 < (1 + φ)⁻¹ ∧ (1 + φ)⁻¹ < 1 :=
  ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ (by linarith)⟩

/-- Woodford (2003), (4.9)–(4.11), pp. 50–51: substituting the rule (4.10) into (4.9) gives
(4.11) with `α = 1/(1 + φ)`, and conversely (both directions; needs only `1 + φ ≠ 0`). -/
theorem equilibrium_iff_reduced {φ : ℝ} (hφ : 1 + φ ≠ 0) (r ibar p : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 φ r ibar p ↔ Reduced 𝔼 (1 + φ)⁻¹ r ibar p := by
  unfold Equilibrium Fisher Reduced
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← mul_add, eq_inv_mul_iff_mul_eq₀ hφ]
  constructor
  · intro h; linear_combination (1 + φ) * h - φ * h
  · intro h; linear_combination h

/-! ### Equation (4.12): the unique bounded solution -/

/-- Woodford (2003), eq. (4.12), p. 51: the series (4.12) is the core forward series of (4.11),
`∑ αᵏ E_t u_{t+k}` with `u = α(r − ī)`. -/
theorem priceLevel_eq_forwardSeries (φ : ℝ) (r ibar : ℕ → Ω → ℝ) :
    priceLevel 𝔼 φ r ibar = 𝔼.forwardSeries (1 + φ)⁻¹ (fun t => (1 + φ)⁻¹ • (r t - ibar t)) := by
  funext t ω
  unfold priceLevel ExpectationSystem.forwardSeries
  refine tsum_congr fun j => ?_
  rw [ExpectationSystem.E_smul, Pi.smul_apply, smul_eq_mul, pow_succ]
  ring

/-- Woodford (2003), p. 51: the forcing term `α(r − ī)` of (4.11) is bounded by `M_r + M_i`
when `|α| ≤ 1`. -/
theorem forcing_bounded {α Mr Mi : ℝ} (hα : |α| ≤ 1) {r ibar : ℕ → Ω → ℝ}
    (hr : ∀ t ω, |r t ω| ≤ Mr) (hi : ∀ t ω, |ibar t ω| ≤ Mi) (t : ℕ) (ω : Ω) :
    |((fun t => α • (r t - ibar t)) t) ω| ≤ Mr + Mi := by
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
  calc |α| * |r t ω - ibar t ω| ≤ 1 * |r t ω - ibar t ω| := by gcongr
    _ ≤ Mr + Mi := by rw [one_mul]; exact (abs_sub _ _).trans (add_le_add (hr t ω) (hi t ω))

/-- Woodford (2003), p. 51: the forcing term `α(r − ī)` of (4.11) is adapted when `r` and `ī`
are. -/
theorem forcing_adapted (α : ℝ) {r ibar : ℕ → Ω → ℝ} (har : 𝔼.Adapted r)
    (hai : 𝔼.Adapted ibar) : 𝔼.Adapted (fun t => α • (r t - ibar t)) := by
  intro t
  simp only [map_smul, map_sub, har t, hai t]

/-- Woodford (2003), eq. (4.12), p. 51 (existence): for `φ > 0` and bounded adapted `{r, ī}`,
the price level (4.12) is an equilibrium, bounded and adapted. -/
theorem priceLevel_equilibrium {φ Mr Mi : ℝ} (hφ : 0 < φ) {r ibar : ℕ → Ω → ℝ}
    (hr : ∀ t ω, |r t ω| ≤ Mr) (hi : ∀ t ω, |ibar t ω| ≤ Mi) (har : 𝔼.Adapted r)
    (hai : 𝔼.Adapted ibar) :
    Equilibrium 𝔼 φ r ibar (priceLevel 𝔼 φ r ibar) ∧ BoundedProc (priceLevel 𝔼 φ r ibar) ∧
      𝔼.Adapted (priceLevel 𝔼 φ r ibar) := by
  obtain ⟨h0, h1⟩ := alpha_mem hφ
  have hα : |(1 + φ)⁻¹| ≤ 1 := by rw [abs_of_pos h0]; exact h1.le
  have hu := forcing_bounded hα hr hi
  have hua := forcing_adapted 𝔼 (1 + φ)⁻¹ har hai
  rw [priceLevel_eq_forwardSeries]
  refine ⟨(equilibrium_iff_reduced 𝔼 (by linarith) r ibar _).mpr fun t => ?_,
    𝔼.forwardSeries_bounded h0.le h1 hu, 𝔼.forwardSeries_adapted h0.le h1 hu⟩
  exact 𝔼.forwardSeries_solves h0.le h1 hu hua t

/-- Woodford (2003), eq. (4.12), p. 51 (uniqueness): for `φ > 0` and bounded adapted `{r, ī}`,
every bounded equilibrium price path is (4.12). -/
theorem eq_priceLevel {φ Mr Mi : ℝ} (hφ : 0 < φ) {r ibar p : ℕ → Ω → ℝ}
    (hr : ∀ t ω, |r t ω| ≤ Mr) (hi : ∀ t ω, |ibar t ω| ≤ Mi) (har : 𝔼.Adapted r)
    (hai : 𝔼.Adapted ibar) (hp : Equilibrium 𝔼 φ r ibar p) (hpb : BoundedProc p) :
    p = priceLevel 𝔼 φ r ibar := by
  obtain ⟨h0, h1⟩ := alpha_mem hφ
  have hα : |(1 + φ)⁻¹| ≤ 1 := by rw [abs_of_pos h0]; exact h1.le
  rw [priceLevel_eq_forwardSeries]
  exact 𝔼.eq_forwardSeries h0.le h1 (forcing_bounded hα hr hi)
    (forcing_adapted 𝔼 (1 + φ)⁻¹ har hai)
    ((equilibrium_iff_reduced 𝔼 (by linarith) r ibar p).mp hp) hpb

/-- Woodford (2003), eq. (4.12), p. 51: for `φ > 0` and bounded adapted `{r, ī}` there is
exactly one bounded equilibrium price path. -/
theorem existsUnique_priceLevel {φ : ℝ} (hφ : 0 < φ) {r ibar : ℕ → Ω → ℝ}
    (hrb : BoundedProc r) (hib : BoundedProc ibar) (har : 𝔼.Adapted r) (hai : 𝔼.Adapted ibar) :
    ∃! p, BoundedProc p ∧ Equilibrium 𝔼 φ r ibar p := by
  obtain ⟨Mr, hr⟩ := hrb
  obtain ⟨Mi, hi⟩ := hib
  obtain ⟨he, hb, -⟩ := priceLevel_equilibrium 𝔼 hφ hr hi har hai
  exact ⟨_, ⟨hb, he⟩, fun p hp => eq_priceLevel 𝔼 hφ hr hi har hai hp.2 hp.1⟩

/-! ### The long-run price level `p̄ = φ⁻¹(r̄ − ī)` -/

/-- Woodford (2003), p. 51: an a-priori bound for forward equations. If `z` is bounded,
`z_t = a E_t z_{t+1} + u_t` with `|a| < 1`, and `|u_t| ≤ K` from date `N` on, then
`|z_t| ≤ K/(1 − |a|)` from date `N` on (no adaptedness needed). -/
theorem abs_le_of_forward {a M K : ℝ} (ha : |a| < 1) {z u : ℕ → Ω → ℝ} (N : ℕ)
    (hz : ∀ t, z t = a • 𝔼.E t (z (t + 1)) + u t) (hM : ∀ t ω, |z t ω| ≤ M)
    (hK : ∀ t, N ≤ t → ∀ ω, |u t ω| ≤ K) (t : ℕ) (ht : N ≤ t) (ω : Ω) :
    |z t ω| ≤ K / (1 - |a|) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK t ht ω)
  have h1 : 0 < 1 - |a| := by linarith
  have hKa : 0 ≤ K / (1 - |a|) := div_nonneg hK0 h1.le
  have key : ∀ n : ℕ, ∀ s, N ≤ s → ∀ ω', |z s ω'| ≤ |a| ^ n * M + K / (1 - |a|) := by
    intro n
    induction n with
    | zero =>
      intro s _ ω'
      have := hM s ω'
      rw [pow_zero, one_mul]
      linarith
    | succ n ih =>
      intro s hs ω'
      have hE := 𝔼.abs_E_le (fun ω'' => ih (s + 1) (by omega) ω'') s ω'
      rw [hz s]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |a * 𝔼.E s (z (s + 1)) ω' + u s ω'|
          ≤ |a| * |𝔼.E s (z (s + 1)) ω'| + |u s ω'| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ |a| * (|a| ^ n * M + K / (1 - |a|)) + K := by
            gcongr
            exact hK s hs ω'
        _ = |a| ^ (n + 1) * M + K / (1 - |a|) := by
            field_simp
            ring
  have hlim : Tendsto (fun n : ℕ => |a| ^ n * M + K / (1 - |a|)) atTop
      (𝓝 (K / (1 - |a|))) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const M).add_const
      (K / (1 - |a|))
  exact ge_of_tendsto' hlim fun n => key n t ht ω

/-- Woodford (2003), p. 51: deviations of an equilibrium price level from `c₀/φ` satisfy the
forward equation (4.11) with forcing `α(r_t − ī_t − c₀)`. -/
theorem deviation_reduced {φ : ℝ} (hφ : 0 < φ) {r ibar p : ℕ → Ω → ℝ}
    (hp : Equilibrium 𝔼 φ r ibar p) (c₀ : ℝ) (t : ℕ) :
    p t - (fun _ => c₀ / φ) = (1 + φ)⁻¹ • 𝔼.E t (p (t + 1) - fun _ => c₀ / φ) +
      (1 + φ)⁻¹ • (r t - ibar t - fun _ => c₀) := by
  funext ω
  have h := congrFun (hp t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  have h1 : (1 + φ)⁻¹ * (1 + φ) = 1 := inv_mul_cancel₀ (by linarith)
  have h2 : c₀ / φ * φ = c₀ := div_mul_cancel₀ c₀ hφ.ne'
  rw [map_sub, 𝔼.const]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (1 + φ)⁻¹ * h + (c₀ / φ - p t ω) * h1 - (1 + φ)⁻¹ * h2

/-- Woodford (2003), p. 51: "the equilibrium price level fluctuates in a bounded interval around
the long-run average value `p̄ ≡ φ⁻¹(r̄ − ī)`". Precisely: if `|r_t − ī_t − (r̄ − ī)| ≤ K`
always, every bounded equilibrium satisfies `|p_t − p̄| ≤ K/φ`. -/
theorem abs_sub_longRun_le {φ rbar ib K : ℝ} (hφ : 0 < φ) {r ibar p : ℕ → Ω → ℝ}
    (hp : Equilibrium 𝔼 φ r ibar p) (hpb : BoundedProc p)
    (hK : ∀ t ω, |r t ω - ibar t ω - (rbar - ib)| ≤ K) (t : ℕ) (ω : Ω) :
    |p t ω - (rbar - ib) / φ| ≤ K / φ := by
  obtain ⟨h0, h1⟩ := alpha_mem hφ
  obtain ⟨M, hM⟩ := hpb
  have hz := deviation_reduced 𝔼 hφ hp (rbar - ib)
  have hzb : ∀ t ω, |((p t - fun _ => (rbar - ib) / φ : Ω → ℝ)) ω| ≤ M + |(rbar - ib) / φ| :=
    fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) le_rfl)
  have hu : ∀ t, 0 ≤ t → ∀ ω,
      |(((1 + φ)⁻¹ • (r t - ibar t - fun _ => rbar - ib) : Ω → ℝ)) ω| ≤ (1 + φ)⁻¹ * K := by
    intro t _ ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_of_pos h0]
    exact mul_le_mul_of_nonneg_left (hK t ω) h0.le
  have hα : |(1 + φ)⁻¹| < 1 := by rw [abs_of_pos h0]; exact h1
  have := abs_le_of_forward 𝔼 hα 0 hz hzb hu t (Nat.zero_le t) ω
  rw [abs_of_pos h0] at this
  have hφ0 : φ ≠ 0 := hφ.ne'
  have hφ1 : 1 + φ ≠ 0 := by linarith
  have he : (1 + φ)⁻¹ * K / (1 - (1 + φ)⁻¹) = K / φ := by
    field_simp
    rw [add_sub_cancel_left, mul_div_assoc, mul_div_cancel₀ K hφ0]
  simpa [he] using this

/-- Woodford (2003), p. 51: with constant `r_t = r̄` and `ī_t = ī`, the unique bounded
equilibrium is the constant `p̄ = φ⁻¹(r̄ − ī)`. -/
theorem priceLevel_const {φ rbar ib : ℝ} (hφ : 0 < φ) {p : ℕ → Ω → ℝ}
    (hp : Equilibrium 𝔼 φ (fun _ _ => rbar) (fun _ _ => ib) p) (hpb : BoundedProc p) :
    ∀ t ω, p t ω = φ⁻¹ * (rbar - ib) := by
  intro t ω
  have h := abs_sub_longRun_le 𝔼 (rbar := rbar) (ib := ib) (K := 0) hφ hp hpb
    (fun _ _ => by simp) t ω
  rw [zero_div, abs_nonpos_iff, sub_eq_zero] at h
  rw [h, div_eq_inv_mul]

/-- Woodford (2003), p. 51: the constant `p̄ = φ⁻¹(r̄ − ī)` is indeed an equilibrium for
constant `r̄, ī` (so `priceLevel_const` is not vacuous). -/
theorem longRun_equilibrium {φ : ℝ} (hφ : 0 < φ) (rbar ib : ℝ) :
    Equilibrium 𝔼 φ (fun _ _ => rbar) (fun _ _ => ib) (fun _ _ => φ⁻¹ * (rbar - ib)) := by
  intro t
  rw [𝔼.const]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Woodford (2003), p. 51: if `r_t − ī_t` converges (uniformly over states) to `r̄ − ī`, every
bounded equilibrium price level converges uniformly to `p̄ = φ⁻¹(r̄ − ī)`. -/
theorem tendsto_longRun {φ rbar ib : ℝ} (hφ : 0 < φ) {r ibar p : ℕ → Ω → ℝ}
    (hp : Equilibrium 𝔼 φ r ibar p) (hpb : BoundedProc p)
    (hconv : ∀ ε > 0, ∃ N, ∀ t, N ≤ t → ∀ ω, |r t ω - ibar t ω - (rbar - ib)| ≤ ε) :
    ∀ ε > 0, ∃ N, ∀ t, N ≤ t → ∀ ω, |p t ω - (rbar - ib) / φ| ≤ ε := by
  intro ε hε
  obtain ⟨h0, h1⟩ := alpha_mem hφ
  obtain ⟨M, hM⟩ := hpb
  obtain ⟨N, hN⟩ := hconv (φ * ε) (mul_pos hφ hε)
  refine ⟨N, fun t ht ω => ?_⟩
  have hz := deviation_reduced 𝔼 hφ hp (rbar - ib)
  have hzb : ∀ t ω, |((p t - fun _ => (rbar - ib) / φ : Ω → ℝ)) ω| ≤ M + |(rbar - ib) / φ| :=
    fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) le_rfl)
  have hu : ∀ t, N ≤ t → ∀ ω,
      |(((1 + φ)⁻¹ • (r t - ibar t - fun _ => rbar - ib) : Ω → ℝ)) ω| ≤ (1 + φ)⁻¹ * (φ * ε) := by
    intro t ht ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_of_pos h0]
    exact mul_le_mul_of_nonneg_left (hN t ht ω) h0.le
  have hα : |(1 + φ)⁻¹| < 1 := by rw [abs_of_pos h0]; exact h1
  have := abs_le_of_forward 𝔼 hα N hz hzb hu t ht ω
  rw [abs_of_pos h0] at this
  have hφ0 : φ ≠ 0 := hφ.ne'
  have hφ1 : 1 + φ ≠ 0 := by linarith
  have he : (1 + φ)⁻¹ * (φ * ε) / (1 - (1 + φ)⁻¹) = ε := by
    field_simp
    rw [add_sub_cancel_left, div_self hφ0]
  simpa [he] using this

/-! ### Comparative statics (p. 51) -/

/-- Woodford (2003), p. 51: a comparison principle for forward equations. If `z` is bounded,
`z_t = a E_t z_{t+1} + u_t` with `0 ≤ a < 1` and `u ≥ 0`, then `z ≥ 0`. -/
theorem nonneg_of_forward {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {z u : ℕ → Ω → ℝ}
    (hz : ∀ t, z t = a • 𝔼.E t (z (t + 1)) + u t) (hM : ∀ t ω, |z t ω| ≤ M)
    (hu : ∀ t ω, 0 ≤ u t ω) (t : ℕ) (ω : Ω) : 0 ≤ z t ω := by
  have key : ∀ n : ℕ, ∀ s ω', -(a ^ n * M) ≤ z s ω' := by
    intro n
    induction n with
    | zero =>
      intro s ω'
      have := neg_abs_le (z s ω')
      rw [pow_zero, one_mul]
      linarith [hM s ω']
    | succ n ih =>
      intro s ω'
      have hle : (fun _ => -(a ^ n * M)) ≤ z (s + 1) := fun ω'' => ih (s + 1) ω''
      have hE : -(a ^ n * M) ≤ 𝔼.E s (z (s + 1)) ω' := by
        have := 𝔼.mono s hle ω'
        rwa [𝔼.const] at this
      rw [hz s]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := mul_le_mul_of_nonneg_left hE ha0
      have hp : a * -(a ^ n * M) = -(a ^ (n + 1) * M) := by ring
      linarith [hu s ω']
  have hlim : Tendsto (fun n : ℕ => -(a ^ n * M)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const M).neg
  exact le_of_tendsto' hlim fun n => key n t ω

/-- Woodford (2003), p. 51: the equilibrium price level is increased by a rise in the real rate
`r` not matched by policy, and by a loosening of policy (a lower intercept `ī`): if
`r ≤ r'` and `ī' ≤ ī` in every date and state, the bounded equilibria satisfy `p ≤ p'`. -/
theorem equilibrium_mono {φ : ℝ} (hφ : 0 < φ) {r r' ibar ibar' p p' : ℕ → Ω → ℝ}
    (hp : Equilibrium 𝔼 φ r ibar p) (hp' : Equilibrium 𝔼 φ r' ibar' p')
    (hpb : BoundedProc p) (hpb' : BoundedProc p') (hr : ∀ t ω, r t ω ≤ r' t ω)
    (hi : ∀ t ω, ibar' t ω ≤ ibar t ω) (t : ℕ) (ω : Ω) : p t ω ≤ p' t ω := by
  obtain ⟨h0, h1⟩ := alpha_mem hφ
  obtain ⟨M, hM⟩ := hpb
  obtain ⟨M', hM'⟩ := hpb'
  have e := (equilibrium_iff_reduced 𝔼 (by linarith) r ibar p).mp hp
  have e' := (equilibrium_iff_reduced 𝔼 (by linarith) r' ibar' p').mp hp'
  have hz : ∀ s, (p' s - p s) = (1 + φ)⁻¹ • 𝔼.E s (p' (s + 1) - p (s + 1)) +
      (1 + φ)⁻¹ • ((r' s - ibar' s) - (r s - ibar s)) := by
    intro s
    rw [map_sub]
    funext ω
    have h1 := congrFun (e s) ω
    have h2 := congrFun (e' s) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    linear_combination h2 - h1
  have hzb : ∀ s ω, |(p' s - p s) ω| ≤ M' + M :=
    fun s ω => (abs_sub _ _).trans (add_le_add (hM' s ω) (hM s ω))
  have hu : ∀ s ω, 0 ≤ ((1 + φ)⁻¹ • ((r' s - ibar' s) - (r s - ibar s))) ω := by
    intro s ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    exact mul_nonneg h0.le (by linarith [hr s ω, hi s ω])
  have := nonneg_of_forward 𝔼 h0.le h1 hz hzb hu t ω
  simp only [Pi.sub_apply] at this
  linarith

/-- Woodford (2003), eq. (4.12), p. 51: every weight `α^{j+1}` in (4.12) is positive, so news of
a higher future real rate or a lower future intercept raises the price level immediately. -/
theorem weights_pos {φ : ℝ} (hφ : 0 < φ) (j : ℕ) : 0 < (1 + φ)⁻¹ ^ (j + 1) :=
  pow_pos (alpha_mem hφ).1 _

/-! ### The role of `φ > 0`: indeterminacy and the exact determinacy region -/

/-- Woodford (2003), pp. 38, 51: the homogeneous path `q_t = (1 + φ)ᵗ`. -/
def homog (φ : ℝ) : ℕ → Ω → ℝ := fun t _ => (1 + φ) ^ t

/-- Woodford (2003), (4.9)–(4.10): `q_t = (1 + φ)ᵗ` solves the equilibrium conditions with
`r = ī = 0`, for every `φ` (for `φ = −1` it is `1, 0, 0, …`). -/
theorem homog_equilibrium (φ : ℝ) :
    Equilibrium 𝔼 φ (fun _ _ => 0) (fun _ _ => 0) (homog φ) := by
  intro t
  unfold homog
  rw [𝔼.const]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (4.9)–(4.10): adding any multiple of the homogeneous path to an equilibrium
gives another equilibrium. -/
theorem equilibrium_add_homog {φ : ℝ} {r ibar p : ℕ → Ω → ℝ}
    (hp : Equilibrium 𝔼 φ r ibar p) (c : ℝ) :
    Equilibrium 𝔼 φ r ibar (p + c • homog φ) := by
  intro t
  have hq := homog_equilibrium 𝔼 φ t
  have hpt := hp t
  funext ω
  have h1 := congrFun hpt ω
  have h2 := congrFun hq ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add,
    map_smul] at h1 h2 ⊢
  linear_combination h1 + c * h2

/-- Woodford (2003), p. 51: the homogeneous path is bounded exactly when `−2 ≤ φ ≤ 0`
(this direction: it is bounded by `1` there). -/
theorem homog_bounded {φ : ℝ} (h1 : -2 ≤ φ) (h2 : φ ≤ 0) : BoundedProc (homog (Ω := Ω) φ) := by
  refine ⟨1, fun t _ => ?_⟩
  unfold homog
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- Woodford (2003), pp. 38, 51 (the role of `φ > 0`): for `−2 ≤ φ ≤ 0` — in particular for an
exogenous interest-rate path, `φ = 0` — every bounded equilibrium `p` has the bounded
companions `p + c (1 + φ)ᵗ`, all distinct: the price level is indeterminate. -/
theorem not_unique_of_mem_Icc [Nonempty Ω] {φ : ℝ} (h1 : -2 ≤ φ) (h2 : φ ≤ 0)
    {r ibar p : ℕ → Ω → ℝ} (hp : Equilibrium 𝔼 φ r ibar p) (hpb : BoundedProc p) (c : ℝ) :
    Equilibrium 𝔼 φ r ibar (p + c • homog φ) ∧ BoundedProc (p + c • homog φ) ∧
      (c ≠ 0 → p + c • homog φ ≠ p) := by
  refine ⟨equilibrium_add_homog 𝔼 hp c, ?_, fun hc h => ?_⟩
  · obtain ⟨M, hM⟩ := hpb
    obtain ⟨Mq, hMq⟩ := homog_bounded (Ω := Ω) h1 h2
    refine ⟨M + |c| * Mq, fun t ω => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMq t ω) (abs_nonneg c)
  · obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun h 0) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, homog, pow_zero, mul_one,
      add_eq_left] at this
    exact hc this

/-- Woodford (2003), p. 38 and §4.3: with an exogenous interest-rate path (`φ = 0`) and a
constant nonzero gap `r_t − ī_t = κ`, there is no bounded equilibrium at all (`E₀ p_t` drifts by
`−κ` each period). Together with `not_unique_of_mem_Icc` this shows that under an interest-rate
peg a bounded equilibrium either fails to exist or is not unique. -/
theorem peg_no_bounded [Nonempty Ω] {κ : ℝ} (hκ : κ ≠ 0) {r ibar p : ℕ → Ω → ℝ}
    (hgap : ∀ t, r t - ibar t = fun _ => κ) (hp : Equilibrium 𝔼 0 r ibar p) :
    ¬ BoundedProc p := by
  rintro ⟨M, hM⟩
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have hstep : ∀ t, 𝔼.E 0 (p t) = 𝔼.E 0 (p (t + 1)) + fun _ => κ := by
    intro t
    have h : p t = 𝔼.E t (p (t + 1)) + (r t - ibar t) := by
      rw [hp t]; simp only [zero_smul, add_zero]; abel
    rw [hgap t] at h
    conv_lhs => rw [h]
    rw [map_add, 𝔼.tower (Nat.zero_le t), 𝔼.const]
  have hdrift : ∀ t : ℕ, 𝔼.E 0 (p t) ω = 𝔼.E 0 (p 0) ω - t * κ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have := congrFun (hstep t) ω
      simp only [Pi.add_apply] at this
      push_cast
      linarith
  have hb : ∀ t, |𝔼.E 0 (p t) ω| ≤ M := fun t => 𝔼.abs_E_le (hM t) 0 ω
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * M / |κ|)
  have hκ' : 0 < |κ| := abs_pos.mpr hκ
  have h1 := hb n
  have h2 := hb 0
  rw [hdrift n] at h1
  have h3 : |(n : ℝ) * κ| ≤ 2 * M := by
    calc |(n : ℝ) * κ| = |𝔼.E 0 (p 0) ω - (𝔼.E 0 (p 0) ω - n * κ)| := by ring_nf
      _ ≤ |𝔼.E 0 (p 0) ω| + |𝔼.E 0 (p 0) ω - n * κ| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  rw [abs_mul, Nat.abs_cast] at h3
  rw [div_lt_iff₀ hκ'] at hn
  linarith

/-- Woodford (2003), p. 51 (general `|a| < 1`): the forward series solves
`z_t = a E_t z_{t+1} + u_t` for bounded adapted `u` and any `|a| < 1`, including negative `a`
(the core `forwardSeries_solves` covers `0 ≤ a < 1`; this extends its proof). -/
theorem forwardSeries_solves_abs {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hadapt : 𝔼.Adapted u) (t : ℕ) :
    𝔼.forwardSeries a u t = a • 𝔼.E t (𝔼.forwardSeries a u (t + 1)) + u t := by
  have ha0 : 0 ≤ |a| := abs_nonneg a
  have hsum : ∀ s ω, Summable (fun k => a ^ k * 𝔼.E s (u (s + k)) ω) := fun s ω =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha).mul_right M) (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (s + k)) s ω) (pow_nonneg ha0 k))
  funext ω
  have hE : 𝔼.E t (𝔼.forwardSeries a u (t + 1)) ω =
      ∑' k, a ^ k * 𝔼.E t (u (t + 1 + k)) ω := by
    have hb : ∀ k ω', |a ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω'| ≤ |a| ^ k * M := by
      intro k ω'
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + 1 + k)) (t + 1) ω')
        (pow_nonneg ha0 k)
    change 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω') ω = _
    rw [𝔼.E_tsum ha0 ha hb t ω]
    refine tsum_congr fun k => ?_
    change 𝔼.E t (a ^ k • 𝔼.E (t + 1) (u (t + 1 + k))) ω = _
    rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω = _
  rw [hE, (hsum t ω).tsum_eq_zero_add, pow_zero, one_mul, add_zero, hadapt t,
    ← tsum_mul_left, add_comm]
  congr 1
  refine tsum_congr fun k => ?_
  rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
  ring

/-- Woodford (2003), p. 51 (general `|a| < 1`): the forward series of a bounded process is
bounded by `M/(1 − |a|)`. -/
theorem forwardSeries_bounded_abs {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) : BoundedProc (𝔼.forwardSeries a u) := by
  refine ⟨M / (1 - |a|), fun t ω => ?_⟩
  have hg : HasSum (fun k : ℕ => M * |a| ^ k) (M / (1 - |a|)) := by
    have := (hasSum_geometric_of_lt_one (abs_nonneg a) ha).mul_left M
    simpa [div_eq_mul_inv] using this
  have := tsum_of_norm_bounded hg (f := fun k => a ^ k * 𝔼.E t (u (t + k)) ω) fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm M]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω) (pow_nonneg (abs_nonneg a) k)
  simpa [ExpectationSystem.forwardSeries, Real.norm_eq_abs] using this

/-- Woodford (2003), §4.3, pp. 50–51 (exact determinacy region, sharpening the book's `φ > 0`):
for every bounded adapted `{r, ī}` there is exactly one bounded equilibrium price path if and
only if `φ > 0` or `φ < −2`, i.e. `|1 + φ| > 1`. -/
theorem existsUnique_iff [Nonempty Ω] (φ : ℝ) :
    (∀ r ibar : ℕ → Ω → ℝ, BoundedProc r → BoundedProc ibar → 𝔼.Adapted r →
      𝔼.Adapted ibar → ∃! p, BoundedProc p ∧ Equilibrium 𝔼 φ r ibar p) ↔
      (0 < φ ∨ φ < -2) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hz : 𝔼.Adapted (fun _ _ => (0 : ℝ)) := fun t => 𝔼.const t 0
    have hzb : BoundedProc (fun _ _ => (0 : ℝ) : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
    obtain ⟨p, -, hu⟩ := h _ _ hzb hzb hz hz
    have h0 : Equilibrium 𝔼 φ (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) := by
      intro t
      rw [𝔼.const]
      funext ω
      simp
    have e0 := hu _ ⟨hzb, h0⟩
    have eq := hu _ ⟨homog_bounded hc2 hc1, homog_equilibrium 𝔼 φ⟩
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (eq.trans e0.symm) 0) ω
    simp [homog] at this
  · intro hφ r ibar ⟨Mr, hr⟩ ⟨Mi, hi⟩ har hai
    have hne : 1 + φ ≠ 0 := by rcases hφ with h | h <;> intro h' <;> linarith
    have hα : |(1 + φ)⁻¹| < 1 := by
      rw [abs_inv]
      refine inv_lt_one_of_one_lt₀ ?_
      rcases hφ with h | h
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
    have hu := forcing_bounded hα.le hr hi
    have hua := forcing_adapted 𝔼 (1 + φ)⁻¹ har hai
    refine ⟨𝔼.forwardSeries (1 + φ)⁻¹ (fun t => (1 + φ)⁻¹ • (r t - ibar t)),
      ⟨forwardSeries_bounded_abs 𝔼 hα hu, (equilibrium_iff_reduced 𝔼 hne r ibar _).mpr
        fun t => forwardSeries_solves_abs 𝔼 hα hu hua t⟩, fun p hp => ?_⟩
    exact 𝔼.forward_unique hα ((equilibrium_iff_reduced 𝔼 hne r ibar p).mp hp.2)
      (fun t => forwardSeries_solves_abs 𝔼 hα hu hua t) hp.1 (forwardSeries_bounded_abs 𝔼 hα hu)

end Woodford.ReturnOfMonetaryRules.NeoWicksellian
