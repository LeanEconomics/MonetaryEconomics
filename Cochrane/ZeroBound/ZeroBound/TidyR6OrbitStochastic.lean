/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.ZLBRule
import ZeroBound.TidyR6ExpectationsMeasureIID
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Stochastic versions of the global orbit results of §20.2.1

Cochrane (2023), Chapter 20, §20.2.1, pp. 472–474 ("Equilibria in which inflation undershoots
the time-`T` target `π*` return back to zero inflation and zero interest rates … `π_t = π*` is
the only locally bounded equilibrium, but … not the only globally bounded one").

`ZLBRule` proves the global statements for orbits `π_{t+1} = f(π_t)` (perfect foresight) of the
map `f = ZLBRule.fmap σ κ φ π* 0`: orbits above `π*` explode (`ZLBRule.orbit_above`), orbits
below converge to zero inflation and zero rates (`ZLBRule.orbit_below_tendsto_zero`,
`ZLBRule.orbit_below_rate_zero`), and the bounded orbits are exactly `π₀ ≤ π*`
(`ZLBRule.bounded_orbits_eq`). Here the model is `E_tπ_{t+1} = f(π_t)` with genuine uncertainty.

## Main results

For every `ExpectationSystem`:
* `fmap_eq_max`: `f = max(ℓ, z)`, the maximum of the active line `ℓ` and the zero-bound line `z`.
* `stoch_line_ge`, `stoch_explodes` (stochastic `ZLBRule.orbit_above`):
  `E_tπ_{t+k} − π* ≥ cᵏ(π_t − π*)`, so if `π_t > π*` in some state, expected inflation explodes
  there; `bounded_le_target`: every bounded solution has `π_t ≤ π*` in every state.
* `stoch_jensen`: `E_tπ_{t+k} ≥ fᵏ(π_t)` (the expected path lies above the deterministic orbit),
  and `stoch_expected_eventually` (what survives of `ZLBRule.orbit_below_tendsto_zero`): along every
  bounded solution expected inflation is eventually in `[−ε, π*]` for every `ε > 0`.
* `bounded_init_iff` (stochastic `ZLBRule.bounded_orbits_eq`): a bounded solution from a
  deterministic `π₀` exists iff `π₀ ≤ π*`.
* `resolved_dichotomy`: once uncertainty is resolved (`E_tπ_{t+1} = π_{t+1}` from some date on),
  each state's path either sits at `π*` or converges to zero inflation with the rate eventually
  zero; every finite event tree resolves its uncertainty (`finiteTree_stabilises`), so the
  deterministic results hold on every finite tree (`finiteTree_dichotomy`).

On a genuine probability space (`TidyR6ExpectationsMeasure`), with the a.e. equations:
* `meas_line_ge`, `meas_bounded_le_target`, `meas_jensen`, `meas_expected_eventually`: the same
  statements almost surely.
* **Counterexamples** (`cex_solves`, `cex_mean`, `cex_rate_mean`, `cex_not_ae_tendsto_zero`,
  `cex_not_ae_rate_zero`, `cex_not_ae_expected_zero`): at the Figure 20.3 calibration
  (`σ = 1`, `κ = 1/2`, `φ = 2`, `π* = 2`, `u = 0`) and i.i.d. Bernoulli(1/12) shocks, the
  process that starts at `π₀ = 3/2 < π*` and switches between `3/2` and `−1/2` when the shock
  hits is a bounded adapted solution, with `E[π_t] = 1/2 + (5/6)ᵗ → 1/2` and
  `E[i_t] = P(i_t > 0) = 1/2 + (5/6)ᵗ/2 → 1/2`. Hence the stochastic versions of
  `ZLBRule.orbit_below_tendsto_zero` and `ZLBRule.orbit_below_rate_zero` are false: `π_t ↛ 0`
  a.e., the rate is
  not eventually zero a.e., and `E_0π_t ↛ 0` a.e.

The continuous-time results of §§20.2.2–20.2.5 have no stochastic version here: that would need
Itô calculus (stochastic differential equations), which Mathlib does not provide.
-/

namespace Cochrane.ZeroBound.TidyR6OrbitStochastic

open Filter Topology MeasureTheory
open Cochrane.ZeroBound Cochrane.ZeroBound.ZLBRule

/-! ## The map as a maximum of two lines -/

/-- Cochrane (2023), eqs. (20.3)–(20.4), p. 472: the map is the maximum of the active line
`π* + c(π − π*) − σκu/(1 + σκ)` and the zero-bound line `π/(1 + σκ) − σκu/(1 + σκ)`. -/
theorem fmap_eq_max {σ κ φ πs u : ℝ} (hσκ : 0 < σ * κ) (x : ℝ) :
    fmap σ κ φ πs u x = max (πs + slopeR σ κ φ * (x - πs) - σ * κ / (1 + σ * κ) * u)
      (1 / (1 + σ * κ) * x - σ * κ / (1 + σ * κ) * u) := by
  have h1 : 0 < 1 + σ * κ := by linarith
  have e1 : πs + slopeR σ κ φ * (x - πs) - σ * κ / (1 + σ * κ) * u =
      (x + σ * κ * (πs + φ * (x - πs)) - σ * κ * u) / (1 + σ * κ) := by
    unfold slopeR; field_simp; ring
  have e2 : 1 / (1 + σ * κ) * x - σ * κ / (1 + σ * κ) * u =
      (x + σ * κ * 0 - σ * κ * u) / (1 + σ * κ) := by
    field_simp; ring
  rw [e1, e2, max_div_div_right h1.le]
  unfold fmap rule
  congr 1
  rw [mul_max_of_nonneg _ _ hσκ.le]
  rcases le_total (σ * κ * (πs + φ * (x - πs))) (σ * κ * 0) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
  · rw [max_eq_left h, max_eq_left (by linarith)]

/-- Cochrane (2023), eq. (20.4), p. 472, `u = 0`: the active line lies below the map,
`π* + c(π − π*) ≤ f(π)`. -/
theorem line_le_fmap {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (x : ℝ) :
    πs + slopeR σ κ φ * (x - πs) ≤ fmap σ κ φ πs 0 x := by
  rw [fmap_eq_max hσκ, mul_zero, sub_zero, sub_zero]
  exact le_max_left _ _

/-! ## Every `ExpectationSystem` -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §20.2.1, p. 472: expectations of an affine function,
`E_t[a + bx] = a + bE_tx`. -/
theorem E_affine (t : ℕ) (a b : ℝ) (x : Ω → ℝ) :
    𝔼.E t (fun ω => a + b * x ω) = fun ω => a + b * 𝔼.E t x ω := by
  have e : (fun ω => a + b * x ω) = (fun _ => a) + b • x := by
    funext ω; simp
  rw [e, map_add, map_smul, 𝔼.const]
  funext ω
  simp

/-- Cochrane (2023), §20.2.1, p. 472: the model `E_tπ_{t+1} = f(π_t)` with `u = 0`, in every
state. -/
def Solves (σ κ φ πs : ℝ) (π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (π (t + 1)) = fun ω => fmap σ κ φ πs 0 (π t ω)

/-- Cochrane (2023), p. 473 ("alternative equilibria diverge from the inflation target"), for
every `ExpectationSystem`: `E_tπ_{t+k} − π* ≥ cᵏ(π_t − π*)`. -/
theorem stoch_line_ge {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π : ℕ → Ω → ℝ}
    (ha : 𝔼.Adapted π) (h : Solves 𝔼 σ κ φ πs π) (t k : ℕ) (ω : Ω) :
    πs + slopeR σ κ φ ^ k * (π t ω - πs) ≤ 𝔼.E t (π (t + k)) ω := by
  have hc : 0 < slopeR σ κ φ := by
    have := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ; linarith
  induction k generalizing ω with
  | zero => simp [ha t]
  | succ k ih =>
    have h1 : 𝔼.E t (π (t + (k + 1))) = 𝔼.E t (fun ω => fmap σ κ φ πs 0 (π (t + k) ω)) := by
      rw [← h (t + k), 𝔼.tower (by omega), show t + k + 1 = t + (k + 1) by ring]
    have h2 : 𝔼.E t (fun ω => (πs - slopeR σ κ φ * πs) + slopeR σ κ φ * π (t + k) ω) ≤
        𝔼.E t (fun ω => fmap σ κ φ πs 0 (π (t + k) ω)) :=
      𝔼.mono t fun ω => by have := line_le_fmap (φ := φ) (πs := πs) hσκ (π (t + k) ω); linarith
    rw [E_affine] at h2
    have h3 := h2 ω
    rw [h1]
    have := mul_le_mul_of_nonneg_left (ih ω) hc.le
    simp only at h3
    rw [pow_succ]
    nlinarith

/-- Cochrane (2023), p. 473, stochastic `ZLBRule.orbit_above`: if `π_t > π*` in some state, the
expected inflation path explodes there, `E_tπ_{t+k} → ∞` as `k → ∞`. -/
theorem stoch_explodes {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π : ℕ → Ω → ℝ}
    (ha : 𝔼.Adapted π) (h : Solves 𝔼 σ κ φ πs π) {t : ℕ} {ω : Ω} (hω : πs < π t ω) :
    Tendsto (fun k => 𝔼.E t (π (t + k)) ω) atTop atTop := by
  have hc := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ
  have hp := ((tendsto_pow_atTop_atTop_of_one_lt hc).atTop_mul_const (sub_pos.mpr hω)).atTop_add
    (tendsto_const_nhds (x := πs))
  refine tendsto_atTop_mono (fun k => ?_) hp
  have := stoch_line_ge 𝔼 hσκ hφ ha h t k ω
  linarith

/-- Cochrane (2023), pp. 473–474, stochastic `ZLBRule.bounded_orbits_eq` (⊆): every bounded
adapted solution has `π_t ≤ π*` at every date and in every state. -/
theorem bounded_le_target {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π : ℕ → Ω → ℝ}
    (hb : BoundedProc π) (ha : 𝔼.Adapted π) (h : Solves 𝔼 σ κ φ πs π) (t : ℕ) (ω : Ω) :
    π t ω ≤ πs := by
  obtain ⟨M, hM⟩ := hb
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := ((stoch_explodes 𝔼 hσκ hφ ha h hcon).eventually_gt_atTop M).exists
  have := 𝔼.abs_E_le (fun ω => hM (t + k) ω) t ω
  linarith [le_abs_self (𝔼.E t (π (t + k)) ω)]

/-- Cochrane (2023), p. 473, for every `ExpectationSystem` (Jensen for the convex map
`f = max(ℓ, z)`): the expected path lies above the deterministic orbit,
`fᵏ(π_t) ≤ E_tπ_{t+k}`. -/
theorem stoch_jensen {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π : ℕ → Ω → ℝ}
    (ha : 𝔼.Adapted π) (h : Solves 𝔼 σ κ φ πs π) (t k : ℕ) (ω : Ω) :
    (fmap σ κ φ πs 0)^[k] (π t ω) ≤ 𝔼.E t (π (t + k)) ω := by
  have hmono := fmap_strictMono (σ := σ) (κ := κ) (φ := φ) (πs := πs) (u := 0) (by linarith) hσκ
  induction k generalizing ω with
  | zero => simp [ha t]
  | succ k ih =>
    have h1 : 𝔼.E t (π (t + (k + 1))) = 𝔼.E t (fun ω => fmap σ κ φ πs 0 (π (t + k) ω)) := by
      rw [← h (t + k), 𝔼.tower (by omega), show t + k + 1 = t + (k + 1) by ring]
    have hA : 𝔼.E t (fun ω => (πs - slopeR σ κ φ * πs) + slopeR σ κ φ * π (t + k) ω) ≤
        𝔼.E t (fun ω => fmap σ κ φ πs 0 (π (t + k) ω)) :=
      𝔼.mono t fun ω => by
        have := line_le_fmap (φ := φ) (πs := πs) hσκ (π (t + k) ω); linarith
    have hZ : 𝔼.E t (fun ω => 0 + 1 / (1 + σ * κ) * π (t + k) ω) ≤
        𝔼.E t (fun ω => fmap σ κ φ πs 0 (π (t + k) ω)) :=
      𝔼.mono t fun ω => by
        have := le_max_right (πs + slopeR σ κ φ * (π (t + k) ω - πs) - σ * κ / (1 + σ * κ) * 0)
          (1 / (1 + σ * κ) * π (t + k) ω - σ * κ / (1 + σ * κ) * 0)
        rw [← fmap_eq_max hσκ] at this
        simpa using this
    rw [E_affine] at hA hZ
    have hA' := hA ω
    have hZ' := hZ ω
    simp only at hA' hZ'
    have hf : fmap σ κ φ πs 0 (𝔼.E t (π (t + k)) ω) ≤ 𝔼.E t (π (t + (k + 1))) ω := by
      rw [h1, fmap_eq_max hσκ]
      refine max_le ?_ ?_ <;> simp only [mul_zero, sub_zero] <;> linarith
    rw [Function.iterate_succ_apply']
    exact le_trans (hmono.monotone (ih ω)) hf

/-- Cochrane (2023), p. 473 ("return back to zero inflation"), what survives under uncertainty:
along every bounded adapted solution, for every `ε > 0`, expected inflation `E_tπ_{t+k}` is
eventually in `[−ε, π*]`. -/
theorem stoch_expected_eventually {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    {π : ℕ → Ω → ℝ} (hb : BoundedProc π) (ha : 𝔼.Adapted π) (h : Solves 𝔼 σ κ φ πs π) (t : ℕ)
    (ω : Ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, -ε ≤ 𝔼.E t (π (t + k)) ω ∧ 𝔼.E t (π (t + k)) ω ≤ πs := by
  have hup : ∀ k, 𝔼.E t (π (t + k)) ω ≤ πs := fun k => by
    have := 𝔼.mono t (fun ω => bounded_le_target 𝔼 hσκ hφ hb ha h (t + k) ω :
      π (t + k) ≤ fun _ => πs) ω
    rwa [𝔼.const] at this
  have hfix : fmap σ κ φ πs 0 πs = πs := (fixed_u_zero hφ hσκ hπs).mpr (Or.inr rfl)
  have hx : ∀ k, (fmap σ κ φ πs 0)^[k + 1] (π t ω) =
      fmap σ κ φ πs 0 ((fmap σ κ φ πs 0)^[k] (π t ω)) := fun k =>
    Function.iterate_succ_apply' _ _ _
  have hlow : ∀ᶠ k in atTop, -ε ≤ (fmap σ κ φ πs 0)^[k] (π t ω) := by
    rcases (bounded_le_target 𝔼 hσκ hφ hb ha h t ω).lt_or_eq with hlt | heq
    · exact ((orbit_below_tendsto_zero (x := fun k => (fmap σ κ φ πs 0)^[k] (π t ω)) hφ hσκ hπs
        hx (by simpa using hlt)).eventually (Ioi_mem_nhds (by linarith : -ε < 0))).mono
        fun _ hk => le_of_lt hk
    · exact Eventually.of_forall fun k => by
        rw [heq, Function.iterate_fixed hfix]; linarith
  filter_upwards [hlow] with k hk
  exact ⟨le_trans hk (stoch_jensen 𝔼 hσκ hφ ha h t k ω), hup k⟩

/-- Cochrane (2023), pp. 473–474, stochastic `ZLBRule.bounded_orbits_eq`: for every
`ExpectationSystem` (with at least one state), a bounded adapted solution starting from the
deterministic value `π₀` exists iff `π₀ ≤ π*`. -/
theorem bounded_init_iff [Nonempty Ω] {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ)
    (hπs : 0 < πs) (p0 : ℝ) :
    (∃ π : ℕ → Ω → ℝ, BoundedProc π ∧ 𝔼.Adapted π ∧ Solves 𝔼 σ κ φ πs π ∧
      π 0 = fun _ => p0) ↔ p0 ≤ πs := by
  constructor
  · rintro ⟨π, hb, ha, h, h0⟩
    have := bounded_le_target 𝔼 hσκ hφ hb ha h 0 (Classical.arbitrary Ω)
    rwa [h0] at this
  · intro hp
    have hmem : p0 ∈ {π0 : ℝ | ∃ M, ∀ t, |(fmap σ κ φ πs 0)^[t] π0| ≤ M} := by
      rw [bounded_orbits_eq hφ hσκ hπs]; exact hp
    obtain ⟨M, hM⟩ := hmem
    refine ⟨fun t _ => (fmap σ κ φ πs 0)^[t] p0, ⟨M, fun t _ => hM t⟩,
      fun t => 𝔼.const t _, fun t => ?_, rfl⟩
    rw [𝔼.const]
    funext ω
    exact Function.iterate_succ_apply' _ _ _

/-- Cochrane (2023), p. 473, under uncertainty that is resolved from date `T₀` on
(`E_tπ_{t+1} = π_{t+1}` for `t ≥ T₀`): in every state, the bounded solution either stays at `π*`
from `T₀` on, or converges to zero inflation with the rate eventually zero. -/
theorem resolved_dichotomy {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    {π : ℕ → Ω → ℝ} (hb : BoundedProc π) (ha : 𝔼.Adapted π) (h : Solves 𝔼 σ κ φ πs π) {T0 : ℕ}
    (hres : ∀ t, T0 ≤ t → 𝔼.E t (π (t + 1)) = π (t + 1)) (ω : Ω) :
    (∀ t, T0 ≤ t → π t ω = πs) ∨
      (Tendsto (fun t => π t ω) atTop (𝓝 0) ∧ ∀ᶠ t in atTop, rule φ πs (π t ω) = 0) := by
  set x : ℕ → ℝ := fun k => π (T0 + k) ω with hxd
  have hx : ∀ k, x (k + 1) = fmap σ κ φ πs 0 (x k) := fun k => by
    have := congrFun (h (T0 + k)) ω
    rw [hres (T0 + k) (by omega)] at this
    simpa [hxd, ← add_assoc] using this
  have hfix : fmap σ κ φ πs 0 πs = πs := (fixed_u_zero hφ hσκ hπs).mpr (Or.inr rfl)
  rcases (bounded_le_target 𝔼 hσκ hφ hb ha h T0 ω).lt_or_eq with hlt | heq
  · right
    have h0 : x 0 < πs := by simpa [hxd] using hlt
    have ht := orbit_below_tendsto_zero hφ hσκ hπs hx h0
    have hr := orbit_below_rate_zero hφ hσκ hπs hx h0
    refine ⟨(tendsto_add_atTop_iff_nat T0).mp ?_, ?_⟩
    · refine ht.congr fun k => ?_
      simp [hxd, add_comm]
    · obtain ⟨N, hN⟩ := eventually_atTop.mp hr
      refine eventually_atTop.mpr ⟨T0 + N, fun t ht => ?_⟩
      have := hN (t - T0) (by omega)
      simpa [hxd, show T0 + (t - T0) = t by omega] using this
  · left
    intro t ht
    have hxk : ∀ k, x k = πs := by
      intro k
      induction k with
      | zero => simpa [hxd] using heq
      | succ k ih => rw [hx, ih, hfix]
    have := hxk (t - T0)
    simpa [hxd, show T0 + (t - T0) = t by omega] using this

/-! ## Finite event trees resolve their uncertainty -/

/-- Cochrane (2023), p. 473 (the finite-tree instances of the core): the information partitions
of a finite event tree stabilise — from some date `T₀` on, `ω ~_t ω'` iff `ω ~_{T₀} ω'`. -/
theorem finiteTree_stabilises {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω') :
    ∃ T0, ∀ t, T0 ≤ t → ∀ a b, T.info t a b ↔ T.info T0 a b := by
  classical
  let g : ℕ → ℕ := fun t => (Finset.univ.filter fun p : Ω' × Ω' => T.info t p.1 p.2).card
  have hanti : ∀ {s t}, s ≤ t → (Finset.univ.filter fun p : Ω' × Ω' => T.info t p.1 p.2) ⊆
      Finset.univ.filter fun p : Ω' × Ω' => T.info s p.1 p.2 := fun hst p hp => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact T.refines hst _ _ hp
  obtain ⟨T0, hT0⟩ : ∃ T0, ∀ t, g T0 ≤ g t := by
    obtain ⟨T0, hT0⟩ := Nat.sInf_mem (⟨g 0, 0, rfl⟩ : (Set.range g).Nonempty)
    exact ⟨T0, fun t => hT0 ▸ Nat.sInf_le ⟨t, rfl⟩⟩
  refine ⟨T0, fun t ht a b => ⟨fun h => T.refines ht a b h, fun h => ?_⟩⟩
  have heq := Finset.eq_of_subset_of_card_le (hanti ht) (hT0 t)
  have hmem : (a, b) ∈ Finset.univ.filter fun p : Ω' × Ω' => T.info T0 p.1 p.2 := by
    simpa using h
  rw [← heq] at hmem
  simpa using hmem

/-- Cochrane (2023), pp. 472–474 on every finite event tree (the core's genuine-uncertainty
instances): every bounded adapted solution is, in every state, either at `π*` from some date on
or converging to zero inflation with the rate eventually zero — the deterministic global results
survive, because a finite tree's uncertainty is resolved after finitely many dates. -/
theorem finiteTree_dichotomy {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω')
    {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs) {π : ℕ → Ω' → ℝ}
    (hb : BoundedProc π) (ha : T.toExpectationSystem.Adapted π)
    (h : Solves T.toExpectationSystem σ κ φ πs π) :
    ∃ T0, ∀ ω, (∀ t, T0 ≤ t → π t ω = πs) ∨
      (Tendsto (fun t => π t ω) atTop (𝓝 0) ∧ ∀ᶠ t in atTop, rule φ πs (π t ω) = 0) := by
  obtain ⟨T0, hT0⟩ := finiteTree_stabilises T
  refine ⟨T0, resolved_dichotomy _ hσκ hφ hπs hb ha h fun t ht => ?_⟩
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  funext ω
  refine T.condE_of_const_on_cell fun ω' hω' => ?_
  have hcell : T.info (t + 1) ω' ω := by
    rw [hT0 (t + 1) (by omega)]
    exact (hT0 t ht ω' ω).mp hω'
  have := ha (t + 1)
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at this
  rw [← this, T.condE_congr _ hcell]

/-! ## A genuine probability space: the a.e. versions -/

open TidyR6ExpectationsMeasure TidyR6ExpectationsMeasureIID ProbabilityTheory

variable {Ωm : Type*} [MeasurableSpace Ωm] (S : MeasExpectationSystem Ωm)

/-- Cochrane (2023), §20.2.1, p. 472, on a probability space: the model
`E_tπ_{t+1} = f(π_t)` (`u = 0`) almost surely, `E_t = μ[· | 𝓕_t]`. -/
def MeasSolves (σ κ φ πs : ℝ) (π : ℕ → Ωm → ℝ) : Prop :=
  ∀ t, S.E t (π (t + 1)) =ᵐ[S.μ] fun ω => fmap σ κ φ πs 0 (π t ω)

/-- Cochrane (2023), §20.2.1, p. 472, on a probability space: conditional expectations of an
affine function, `E_t[a + bx] = a + bE_tx` a.e. -/
theorem meas_E_affine {x : Ωm → ℝ} (hx : Integrable x S.μ) (t : ℕ) (a b : ℝ) :
    S.E t (fun ω => a + b * x ω) =ᵐ[S.μ] fun ω => a + b * S.E t x ω := by
  have e : (fun ω => a + b * x ω) = (fun _ => a) + b • x := by
    funext ω; simp
  rw [e]
  have h1 := S.E_add (integrable_const a) (hx.smul b) t
  have h2 := S.E_smul b x t
  filter_upwards [h1, h2] with ω h1 h2
  rw [h1, Pi.add_apply, h2, S.E_const]
  simp

/-- Cochrane (2023), §20.2.1: a bounded adapted process is integrable at every date. -/
theorem integrable_of_bdd {π : ℕ → Ωm → ℝ} (had : StronglyAdapted S.𝓕 π) (hb : BoundedProc π)
    (t : ℕ) : Integrable (π t) S.μ := by
  obtain ⟨M, hM⟩ := hb
  exact Integrable.of_bound ((had t).mono (S.𝓕.le t)).aestronglyMeasurable M
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hM t ω)

/-- Cochrane (2023), p. 473, on a probability space: `E_tπ_{t+k} − π* ≥ cᵏ(π_t − π*)` a.e. -/
theorem meas_line_ge {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π : ℕ → Ωm → ℝ}
    (had : StronglyAdapted S.𝓕 π) (hb : BoundedProc π) (h : MeasSolves S σ κ φ πs π)
    (t k : ℕ) : ∀ᵐ ω ∂S.μ, πs + slopeR σ κ φ ^ k * (π t ω - πs) ≤ S.E t (π (t + k)) ω := by
  have hc : 0 < slopeR σ κ φ := by
    have := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ; linarith
  have hint := integrable_of_bdd S had hb
  induction k with
  | zero =>
    have := S.E_of_stronglyMeasurable (had t) (hint t)
    exact Eventually.of_forall fun ω => by simp [this]
  | succ k ih =>
    have hT : S.E t (π (t + (k + 1))) =ᵐ[S.μ] S.E t (S.E (t + k) (π (t + k + 1))) := by
      rw [show t + (k + 1) = t + k + 1 by ring]
      exact (S.E_tower (by omega) _).symm
    have hC := S.E_congr (h (t + k)) t
    have hfi : Integrable (fun ω => fmap σ κ φ πs 0 (π (t + k) ω)) S.μ :=
      (S.integrable_E (t + k) _).congr (h (t + k))
    have hli : Integrable (fun ω => (πs - slopeR σ κ φ * πs) + slopeR σ κ φ * π (t + k) ω)
        S.μ := (integrable_const _).add ((hint (t + k)).const_mul _)
    have hM := S.E_mono hli hfi (Eventually.of_forall fun ω => by
      have := line_le_fmap (φ := φ) (πs := πs) hσκ (π (t + k) ω); simp only; linarith) t
    have hA := meas_E_affine S (hint (t + k)) t (πs - slopeR σ κ φ * πs) (slopeR σ κ φ)
    filter_upwards [hT, hC, hM, hA, ih] with ω h1 h2 h3 h4 h5
    rw [h1, h2]
    rw [h4] at h3
    have := mul_le_mul_of_nonneg_left h5 hc.le
    rw [pow_succ]
    nlinarith

/-- Cochrane (2023), pp. 473–474, on a probability space: every bounded adapted solution has
`π_t ≤ π*` almost surely. -/
theorem meas_bounded_le_target {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ)
    {π : ℕ → Ωm → ℝ} (had : StronglyAdapted S.𝓕 π) (hb : BoundedProc π)
    (h : MeasSolves S σ κ φ πs π) (t : ℕ) : ∀ᵐ ω ∂S.μ, π t ω ≤ πs := by
  obtain ⟨M, hM⟩ := hb
  have hc := (slope_right_gt_one_iff (φ := φ) hσκ).mpr hφ
  have hall := ae_all_iff.mpr (meas_line_ge S hσκ hφ had ⟨M, hM⟩ h t)
  have hbd : ∀ᵐ ω ∂S.μ, ∀ k, |S.E t (π (t + k)) ω| ≤ M :=
    ae_all_iff.mpr fun k => S.abs_E_le (Eventually.of_forall (hM (t + k))) t
  filter_upwards [hall, hbd] with ω h1 h2
  by_contra hcon
  push Not at hcon
  have hp := ((tendsto_pow_atTop_atTop_of_one_lt hc).atTop_mul_const (sub_pos.mpr hcon))
  obtain ⟨k, hk⟩ := (hp.eventually_gt_atTop (M - πs)).exists
  linarith [h1 k, le_abs_self (S.E t (π (t + k)) ω), h2 k]

/-- Cochrane (2023), p. 473, on a probability space (Jensen for `f = max(ℓ, z)`):
`fᵏ(π_t) ≤ E_tπ_{t+k}` a.e. -/
theorem meas_jensen {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π : ℕ → Ωm → ℝ}
    (had : StronglyAdapted S.𝓕 π) (hb : BoundedProc π) (h : MeasSolves S σ κ φ πs π)
    (t k : ℕ) : ∀ᵐ ω ∂S.μ, (fmap σ κ φ πs 0)^[k] (π t ω) ≤ S.E t (π (t + k)) ω := by
  have hmono := fmap_strictMono (σ := σ) (κ := κ) (φ := φ) (πs := πs) (u := 0) (by linarith) hσκ
  have hint := integrable_of_bdd S had hb
  induction k with
  | zero =>
    have := S.E_of_stronglyMeasurable (had t) (hint t)
    exact Eventually.of_forall fun ω => by simp [this]
  | succ k ih =>
    have hT : S.E t (π (t + (k + 1))) =ᵐ[S.μ] S.E t (S.E (t + k) (π (t + k + 1))) := by
      rw [show t + (k + 1) = t + k + 1 by ring]
      exact (S.E_tower (by omega) _).symm
    have hC := S.E_congr (h (t + k)) t
    have hfi : Integrable (fun ω => fmap σ κ φ πs 0 (π (t + k) ω)) S.μ :=
      (S.integrable_E (t + k) _).congr (h (t + k))
    have hli : Integrable (fun ω => (πs - slopeR σ κ φ * πs) + slopeR σ κ φ * π (t + k) ω)
        S.μ := (integrable_const _).add ((hint (t + k)).const_mul _)
    have hzi : Integrable (fun ω => 0 + 1 / (1 + σ * κ) * π (t + k) ω) S.μ :=
      (integrable_const _).add ((hint (t + k)).const_mul _)
    have hMA := S.E_mono hli hfi (Eventually.of_forall fun ω => by
      have := line_le_fmap (φ := φ) (πs := πs) hσκ (π (t + k) ω); simp only; linarith) t
    have hMZ := S.E_mono hzi hfi (Eventually.of_forall fun ω => by
      have := le_max_right (πs + slopeR σ κ φ * (π (t + k) ω - πs) - σ * κ / (1 + σ * κ) * 0)
        (1 / (1 + σ * κ) * π (t + k) ω - σ * κ / (1 + σ * κ) * 0)
      rw [← fmap_eq_max hσκ] at this
      simp only
      linarith) t
    have hA := meas_E_affine S (hint (t + k)) t (πs - slopeR σ κ φ * πs) (slopeR σ κ φ)
    have hZ := meas_E_affine S (hint (t + k)) t 0 (1 / (1 + σ * κ))
    filter_upwards [hT, hC, hMA, hMZ, hA, hZ, ih] with ω h1 h2 h3 h4 h5 h6 h7
    rw [h5] at h3
    rw [h6] at h4
    have hf : fmap σ κ φ πs 0 (S.E t (π (t + k)) ω) ≤ S.E t (π (t + (k + 1))) ω := by
      rw [h1, h2, fmap_eq_max hσκ]
      refine max_le ?_ ?_ <;> simp only [mul_zero, sub_zero] at h3 h4 ⊢ <;> linarith
    rw [Function.iterate_succ_apply']
    exact le_trans (hmono.monotone h7) hf

/-- Cochrane (2023), p. 473, on a probability space: along every bounded adapted solution,
almost surely, for every `ε > 0` expected inflation `E_tπ_{t+k}` is eventually in `[−ε, π*]`. -/
theorem meas_expected_eventually {σ κ φ πs : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hπs : 0 < πs)
    {π : ℕ → Ωm → ℝ} (had : StronglyAdapted S.𝓕 π) (hb : BoundedProc π)
    (h : MeasSolves S σ κ φ πs π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ ε, 0 < ε →
      ∀ᶠ k in atTop, -ε ≤ S.E t (π (t + k)) ω ∧ S.E t (π (t + k)) ω ≤ πs := by
  have hint := integrable_of_bdd S had hb
  have hup : ∀ᵐ ω ∂S.μ, ∀ k, S.E t (π (t + k)) ω ≤ πs := ae_all_iff.mpr fun k => by
    have := S.E_mono (hint (t + k)) (integrable_const πs)
      (meas_bounded_le_target S hσκ hφ had hb h (t + k)) t
    rwa [S.E_const] at this
  filter_upwards [ae_all_iff.mpr (meas_jensen S hσκ hφ had hb h t),
    meas_bounded_le_target S hσκ hφ had hb h t, hup] with ω h1 h2 h3 ε hε
  have hfix : fmap σ κ φ πs 0 πs = πs := (fixed_u_zero hφ hσκ hπs).mpr (Or.inr rfl)
  have hx : ∀ k, (fmap σ κ φ πs 0)^[k + 1] (π t ω) =
      fmap σ κ φ πs 0 ((fmap σ κ φ πs 0)^[k] (π t ω)) := fun k =>
    Function.iterate_succ_apply' _ _ _
  have hlow : ∀ᶠ k in atTop, -ε ≤ (fmap σ κ φ πs 0)^[k] (π t ω) := by
    rcases h2.lt_or_eq with hlt | heq
    · exact ((orbit_below_tendsto_zero (x := fun k => (fmap σ κ φ πs 0)^[k] (π t ω)) hφ hσκ hπs
        hx (by simpa using hlt)).eventually (Ioi_mem_nhds (by linarith : -ε < 0))).mono
        fun _ hk => le_of_lt hk
    · exact Eventually.of_forall fun k => by
        rw [heq, Function.iterate_fixed hfix]; linarith
  filter_upwards [hlow] with k hk
  exact ⟨le_trans hk (h1 k), h3 k⟩

/-! ## The counterexample on the i.i.d. space -/

/-- Cochrane (2023), §20.2.1 (counterexample): the Bernoulli(1/12) law
`(1/12)δ₁ + (11/12)δ₀` as a measure. -/
noncomputable def bernMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / 12) • Measure.dirac 1 + ENNReal.ofReal (11 / 12) • Measure.dirac 0

/-- Cochrane (2023), §20.2.1: the Bernoulli law has total mass one. -/
theorem bernMeasure_univ : bernMeasure Set.univ = 1 := by
  simp only [bernMeasure, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- Cochrane (2023), §20.2.1: the Bernoulli(1/12) law as a probability measure. -/
noncomputable def bern : ProbabilityMeasure ℝ := ⟨bernMeasure, ⟨bernMeasure_univ⟩⟩

/-- Cochrane (2023), §20.2.1: `∫ f d(Bernoulli) = f(1)/12 + 11f(0)/12`. -/
theorem integral_bern (f : ℝ → ℝ) :
    ∫ x, f x ∂(bern : Measure ℝ) = 1 / 12 * f 1 + 11 / 12 * f 0 := by
  change ∫ x, f x ∂bernMeasure = _
  rw [bernMeasure, integral_add_measure
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num), smul_eq_mul,
    smul_eq_mul]

/-- Cochrane (2023), §20.2.1: the switch indicator `g(y) = 1` if `y = 1`, `0` otherwise. -/
noncomputable def gsw (y : ℝ) : ℝ := if y = 1 then 1 else 0

/-- Cochrane (2023), §20.2.1: the switch indicator is measurable. -/
theorem gsw_measurable : Measurable gsw :=
  Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const

/-- Cochrane (2023), §20.2.1 (counterexample): inflation starts at `3/2` and switches between
`3/2` and `−1/2` (`π ↦ 1 − π`) whenever the shock equals `1`. -/
noncomputable def cexPi : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 3 / 2
  | t + 1 => fun ω => cexPi t ω + gsw (ω (t + 1)) * (1 - 2 * cexPi t ω)

/-- Cochrane (2023), §20.2.1: the counterexample takes only the values `−1/2` and `3/2`. -/
theorem cexPi_values (t : ℕ) (ω : ℕ → ℝ) : cexPi t ω = -1 / 2 ∨ cexPi t ω = 3 / 2 := by
  induction t with
  | zero => right; rfl
  | succ t ih =>
    simp only [cexPi, gsw]
    split_ifs <;> rcases ih with h | h <;> rw [h] <;> norm_num

/-- Cochrane (2023), §20.2.1: the counterexample is bounded by `3/2`. -/
theorem cexPi_bdd (t : ℕ) (ω : ℕ → ℝ) : |cexPi t ω| ≤ 3 / 2 := by
  rcases cexPi_values t ω with h | h <;> rw [h] <;> norm_num [abs_of_pos, abs_of_neg]

/-- Cochrane (2023), §20.2.1: the counterexample is adapted to the natural filtration. -/
theorem cexPi_meas (t : ℕ) : Measurable[(iidSystem bern).𝓕 t] (cexPi t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have h1 : Measurable[(iidSystem bern).𝓕 (t + 1)] (cexPi t) :=
      ih.mono ((iidSystem bern).𝓕.mono (Nat.le_succ t)) le_rfl
    have h2 : Measurable[(iidSystem bern).𝓕 (t + 1)] (fun ω : ℕ → ℝ => gsw (ω (t + 1))) :=
      gsw_measurable.comp (measurable_shock bern le_rfl)
    exact h1.add (h2.mul (measurable_const.sub (measurable_const.mul h1)))

/-- Cochrane (2023), Figure 20.3 calibration, `u = 0`: on `{−1/2, 3/2}` the map is affine,
`f(π) = (5/6)π + 1/12`. -/
theorem fmap_cex (x : ℝ) (hx : x = -1 / 2 ∨ x = 3 / 2) :
    fmap 1 (1 / 2) 2 2 0 x = 5 / 6 * x + 1 / 12 := by
  rcases hx with rfl | rfl
  · unfold fmap rule; rw [max_eq_right (by norm_num)]; norm_num
  · unfold fmap rule; rw [max_eq_left (by norm_num)]; norm_num

/-- Cochrane (2023), §20.2.1 (counterexample): `E_tπ_{t+1} = (5/6)π_t + 1/12` a.e. -/
theorem cex_E (t : ℕ) : (iidSystem bern).E t (cexPi (t + 1)) =ᵐ[(iidSystem bern).μ]
    fun ω => 5 / 6 * cexPi t ω + 1 / 12 := by
  set S := iidSystem bern
  have hm : StronglyMeasurable[S.𝓕 t] (cexPi t) := (cexPi_meas t).stronglyMeasurable
  have hi : Integrable (cexPi t) S.μ :=
    Integrable.of_bound (hm.mono (S.𝓕.le t)).aestronglyMeasurable (3 / 2)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact cexPi_bdd t ω)
  have hg : Integrable (fun ω : ℕ → ℝ => gsw (ω (t + 1))) S.μ :=
    Integrable.of_bound (gsw_measurable.comp (measurable_pi_apply (t + 1))).aestronglyMeasurable
      1 (Eventually.of_forall fun ω => by unfold gsw; split_ifs <;> norm_num)
  have hfm : StronglyMeasurable[S.𝓕 t] (fun ω => 1 - 2 * cexPi t ω) :=
    (measurable_const.sub (measurable_const.mul (cexPi_meas t))).stronglyMeasurable
  have hprod := S.E_pullOut hfm (C := 2) (Eventually.of_forall fun ω => by
    rcases cexPi_values t ω with h | h <;> rw [h] <;> norm_num) hg
  have hsh := E_shock_fun bern t gsw_measurable
  have hint : ∫ x, gsw x ∂(bern : Measure ℝ) = 1 / 12 := by
    rw [integral_bern]; simp [gsw]
  have e : cexPi (t + 1) = cexPi t + (fun ω => 1 - 2 * cexPi t ω) * fun ω => gsw (ω (t + 1)) := by
    funext ω; simp only [cexPi, Pi.add_apply, Pi.mul_apply]; ring
  rw [e]
  have hpi : Integrable ((fun ω => 1 - 2 * cexPi t ω) * fun ω => gsw (ω (t + 1))) S.μ :=
    hg.bdd_mul (c := 2) (hfm.mono (S.𝓕.le t)).aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      rcases cexPi_values t ω with h | h <;> norm_num [h])
  have hadd := S.E_add hi hpi t
  rw [S.E_of_stronglyMeasurable hm hi] at hadd
  filter_upwards [hadd, hprod, hsh] with ω h1 h2 h3
  rw [h1, Pi.add_apply, h2, Pi.mul_apply, h3, hint]
  ring

/-- Cochrane (2023), §20.2.1, pp. 473–474 (counterexample on a genuine probability space):
at the Figure 20.3 calibration with `u = 0`, the switching process is a bounded adapted solution
of `E_tπ_{t+1} = f(π_t)`, starting from the deterministic `π₀ = 3/2 < π* = 2`. -/
theorem cex_solves :
    StronglyAdapted (iidSystem bern).𝓕 cexPi ∧ BoundedProc cexPi ∧
      MeasSolves (iidSystem bern) 1 (1 / 2) 2 2 cexPi ∧ cexPi 0 = (fun _ => 3 / 2) := by
  refine ⟨fun t => (cexPi_meas t).stronglyMeasurable, ⟨3 / 2, cexPi_bdd⟩, fun t => ?_, rfl⟩
  filter_upwards [cex_E t] with ω h
  rw [h, fmap_cex _ (cexPi_values t ω)]

/-- Cochrane (2023), §20.2.1 (counterexample): mean inflation is `E[π_t] = 1/2 + (5/6)ᵗ`, which
tends to `1/2`, not to zero. -/
theorem cex_mean (t : ℕ) : ∫ ω, cexPi t ω ∂(iidSystem bern).μ = 1 / 2 + (5 / 6) ^ t := by
  set S := iidSystem bern
  induction t with
  | zero => simp [cexPi]; norm_num
  | succ t ih =>
    have hi : Integrable (cexPi t) S.μ :=
      Integrable.of_bound (((cexPi_meas t).mono (S.𝓕.le t) le_rfl).aestronglyMeasurable) (3 / 2)
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact cexPi_bdd t ω)
    rw [← S.integral_E t, integral_congr_ae (cex_E t), integral_add (hi.const_mul _)
      (integrable_const _), integral_const_mul, ih, integral_const]
    simp
    ring

/-- Cochrane (2023), §20.2.1 (counterexample): the rate `i_t = max[π* + φ(π_t − π*), 0]` takes
only the values `0` and `1`, `i_t = (π_t + 1/2)/2`, so its mean is the probability that the rate
is positive, `E[i_t] = 1/2 + (5/6)ᵗ/2 → 1/2`. -/
theorem cex_rate_mean (t : ℕ) :
    (∀ ω, rule 2 2 (cexPi t ω) = (cexPi t ω + 1 / 2) / 2 ∧
      (rule 2 2 (cexPi t ω) = 0 ∨ rule 2 2 (cexPi t ω) = 1)) ∧
    ∫ ω, rule 2 2 (cexPi t ω) ∂(iidSystem bern).μ = 1 / 2 + (5 / 6) ^ t / 2 := by
  have hval : ∀ ω, rule 2 2 (cexPi t ω) = (cexPi t ω + 1 / 2) / 2 ∧
      (rule 2 2 (cexPi t ω) = 0 ∨ rule 2 2 (cexPi t ω) = 1) := fun ω => by
    rcases cexPi_values t ω with h | h <;> rw [h] <;> unfold rule
    · rw [max_eq_right (by norm_num)]; norm_num
    · rw [max_eq_left (by norm_num)]; norm_num
  refine ⟨hval, ?_⟩
  have hi : Integrable (cexPi t) (iidSystem bern).μ :=
    Integrable.of_bound
      (((cexPi_meas t).mono ((iidSystem bern).𝓕.le t) le_rfl).aestronglyMeasurable) (3 / 2)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact cexPi_bdd t ω)
  rw [integral_congr_ae (Eventually.of_forall fun ω => (hval ω).1)]
  simp only [div_eq_mul_inv]
  rw [integral_mul_const, integral_add hi (integrable_const _), integral_const]
  have := cex_mean t
  simp only [div_eq_mul_inv] at this
  rw [this]
  simp
  ring

/-- Cochrane (2023), §20.2.1: dominated convergence for the counterexample, `|F_t| ≤ 3/2`. -/
theorem cex_dct {F : ℕ → (ℕ → ℝ) → ℝ} {l : ℝ}
    (hm : ∀ t, AEStronglyMeasurable (F t) (iidSystem bern).μ)
    (hb : ∀ t, ∀ᵐ ω ∂(iidSystem bern).μ, |F t ω| ≤ 3 / 2)
    (hl : ∀ᵐ ω ∂(iidSystem bern).μ, Tendsto (fun t => F t ω) atTop (𝓝 l)) :
    Tendsto (fun t => ∫ ω, F t ω ∂(iidSystem bern).μ) atTop (𝓝 l) := by
  have := tendsto_integral_of_dominated_convergence (fun _ => (3 / 2 : ℝ)) hm
    (integrable_const _) (fun t => (hb t).mono fun ω h => by rwa [Real.norm_eq_abs]) hl
  simpa using this

/-- Cochrane (2023), p. 473, survey of the global results: **the stochastic version of
`ZLBRule.orbit_below_tendsto_zero` is false.** In the counterexample, inflation does not
converge to zero almost surely (although `π₀ < π*` and the solution is bounded). -/
theorem cex_not_ae_tendsto_zero :
    ¬ ∀ᵐ ω ∂(iidSystem bern).μ, Tendsto (fun t => cexPi t ω) atTop (𝓝 0) := by
  intro h
  have h1 := cex_dct (fun t => ((cexPi_meas t).mono ((iidSystem bern).𝓕.le t)
    le_rfl).aestronglyMeasurable) (fun t => Eventually.of_forall (cexPi_bdd t)) h
  have h2 : Tendsto (fun t => ∫ ω, cexPi t ω ∂(iidSystem bern).μ) atTop (𝓝 (1 / 2)) := by
    simp only [cex_mean]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 5 / 6)
      (by norm_num)).const_add (1 / 2 : ℝ)
  have := tendsto_nhds_unique h1 h2
  norm_num at this

/-- Cochrane (2023), p. 473 ("return back to … zero interest rates"): **the stochastic version
of `ZLBRule.orbit_below_rate_zero` is false.** In the counterexample the rate is not eventually
zero almost surely; indeed `P(i_t > 0) = E[i_t] → 1/2`. -/
theorem cex_not_ae_rate_zero :
    ¬ ∀ᵐ ω ∂(iidSystem bern).μ, ∀ᶠ t in atTop, rule 2 2 (cexPi t ω) = 0 := by
  intro h
  have hl : ∀ᵐ ω ∂(iidSystem bern).μ, Tendsto (fun t => rule 2 2 (cexPi t ω)) atTop (𝓝 0) :=
    h.mono fun ω hω => tendsto_const_nhds.congr' (hω.mono fun t ht => ht.symm)
  have hrm : ∀ t, Measurable (fun ω => rule 2 2 (cexPi t ω)) := fun t => by
    have := (cexPi_meas t).mono ((iidSystem bern).𝓕.le t) le_rfl
    unfold rule
    exact (measurable_const.add (measurable_const.mul (this.sub measurable_const))).max
      measurable_const
  have h1 := cex_dct (fun t => (hrm t).aestronglyMeasurable) (fun t => Eventually.of_forall
    fun ω => by
      rcases ((cex_rate_mean t).1 ω).2 with h | h <;> rw [h] <;> norm_num) hl
  have h2 : Tendsto (fun t => ∫ ω, rule 2 2 (cexPi t ω) ∂(iidSystem bern).μ) atTop
      (𝓝 (1 / 2)) := by
    simp only [fun t => (cex_rate_mean t).2]
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 5 / 6)
      (by norm_num)).div_const 2).const_add (1 / 2 : ℝ)
  have := tendsto_nhds_unique h1 h2
  norm_num at this

/-- Cochrane (2023), p. 473: **expected inflation does not return to zero either**: in the
counterexample `E_0π_t ↛ 0` almost surely (its mean is `E[π_t] → 1/2`). -/
theorem cex_not_ae_expected_zero :
    ¬ ∀ᵐ ω ∂(iidSystem bern).μ,
      Tendsto (fun t => (iidSystem bern).E 0 (cexPi t) ω) atTop (𝓝 0) := by
  intro h
  have h1 := cex_dct (fun t => ((iidSystem bern).integrable_E 0 (cexPi t)).aestronglyMeasurable)
    (fun t => (iidSystem bern).abs_E_le (Eventually.of_forall (cexPi_bdd t)) 0) h
  have h2 : Tendsto (fun t => ∫ ω, (iidSystem bern).E 0 (cexPi t) ω ∂(iidSystem bern).μ) atTop
      (𝓝 (1 / 2)) := by
    simp only [(iidSystem bern).integral_E, cex_mean]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 5 / 6)
      (by norm_num)).const_add (1 / 2 : ℝ)
  have := tendsto_nhds_unique h1 h2
  norm_num at this

end Cochrane.ZeroBound.TidyR6OrbitStochastic
