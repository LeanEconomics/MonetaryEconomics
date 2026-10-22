/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.InertialBoundary

/-!
# The inertial rule on the boundary: existence with small disturbances

Woodford (2003), *Interest and Prices*, Prop. 2.8, p. 96, and App. A.3, pp. 632–634.
`InertialBoundary` proves that the rules `φ_π π + h(î_{−1})` with an expanding diagonal
(`unique_affine`) and `ρ î_{−1} + σπ³` (`unique_cube`) have **at most one** bounded equilibrium for
every initial rate and disturbance process, and exactly one without disturbances. This module
proves **existence for small disturbances**, hence `∃!`, with the size of the equilibrium of
order `‖e‖^{1/3}` — and, for the resonant shock, exactly the cube root.

## Main results

* `exists_expanding` (**the engine**): for any informationally closed expectation system on a
  nonempty state space and maps `Γ_t(ω, ·)` that are continuous, uniformly expanding
  (`|Γ(a) − Γ(b)| ≥ |a − b| + κ|a − b|³`), known at `t`, with `|Γ_t(ω, 0)| ≤ κR³`, there is a
  known-at-`t` process `|i_t| ≤ R` with `E_t i_{t+1} = Γ_t(i_t)`. Construction: solve backwards
  from `i_{t+k} = 0` (`backW`), and let `k → ∞`; the backward map is a weak contraction, the
  sup-distance `d_k` between horizons satisfies `d_{k+1} + κ d_{k+1}³ ≤ d_k`, so `d_k → 0`
  uniformly in `ω` (`backW_cauchy`). `unique_expanding`: such a process is unique.
* `exists_unique_affine`: for the rule `φ_π π + h(î_{−1})` (`φ_π ≠ 0`, `h` continuous, expanding
  diagonal) under informational closure: for every initial rate and every disturbance process
  with `(1 + |φ_π|)‖e‖ ≤ κR³` there is **exactly one** bounded adapted equilibrium, and its
  interest rate stays within `R`. This covers perfect foresight and every finite event tree.
* `resonant_cube_root`: for the repelling cubic rule `φ_π π + ρ i + σ i³` (`σ = φ_π + ρ`,
  `σ² = 1`) and the resonant shock `ν_t = δσᵗ` of `InertialBoundary.no_eq_unit` (which destroys
  existence for the linear rule), every equilibrium has `î_t = σᵗ ∛(−δ)`: the equilibrium
  responds to the shock size like `δ^{1/3}`, not differentiably.
* `exists_unique_cube_pf`: for `ρ î_{−1} + σπ³` (`φ_π = 0`, `σ² = 1`, `σρ ≥ 1`) under perfect
  foresight: exactly one bounded equilibrium for every initial rate and every disturbance
  sequence with `‖e‖ + ‖e‖³ ≤ R³/4`.
-/

namespace Woodford.PriceLevelDetermination.InertialBoundaryExist

open scoped Topology Matrix
open Filter
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic SunspotsBoundedBelow
open SunspotsNotOntoExamples (known_comp)
open LocalIFTSystems (Arg cbrt cbrt_pow)
open LocalIFTSystemsApps (Finert)
open InertialBoundary (eq0_of_solves eq1_of_solves lag_known unique_affine unique_cube
  resShock ruleCubI expand_cubic)

/-! ### Expanding maps -/

/-- Woodford (2003), App. A.3, p. 634 (tool): `x ↦ x + κx³` is monotone. -/
theorem phi_mono {κ : ℝ} (hκ : 0 ≤ κ) : Monotone fun x : ℝ => x + κ * x ^ 3 := by
  intro a b hab
  have h : a ^ 3 ≤ b ^ 3 := by
    nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b, mul_nonneg (sub_nonneg.mpr hab)
      (add_nonneg (sq_nonneg (a + b)) (add_nonneg (sq_nonneg a) (sq_nonneg b)))]
  simp only
  nlinarith

/-- Woodford (2003), App. A.3, p. 634 (tool): an expanding map is one-to-one. -/
theorem injective_of_expanding {Γ : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hexp : ∀ a b, |a - b| + κ * |a - b| ^ 3 ≤ |Γ a - Γ b|) : Function.Injective Γ := by
  intro a b h
  have := hexp a b
  rw [h, sub_self, abs_zero] at this
  have h3 : 0 ≤ κ * |a - b| ^ 3 := by positivity
  have : |a - b| = 0 := le_antisymm (by linarith) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp this)

/-- Woodford (2003), App. A.3, p. 634 (tool): **a continuous expanding map of `ℝ` is onto**
(it is strictly monotone and moves `±M` at least `M` away from `Γ(0)`). -/
theorem surjective_of_expanding {Γ : ℝ → ℝ} (hc : Continuous Γ) {κ : ℝ} (hκ : 0 < κ)
    (hexp : ∀ a b, |a - b| + κ * |a - b| ^ 3 ≤ |Γ a - Γ b|) : Function.Surjective Γ := by
  intro y
  set M := |y| + |Γ 0| with hM
  have hM0 : 0 ≤ M := by positivity
  have h1 : M ≤ |Γ M - Γ 0| := by
    have := hexp M 0
    rw [sub_zero, abs_of_nonneg hM0] at this
    nlinarith [pow_nonneg hM0 3]
  have h2 : M ≤ |Γ (-M) - Γ 0| := by
    have := hexp (-M) 0
    rw [sub_zero, abs_neg, abs_of_nonneg hM0] at this
    nlinarith [pow_nonneg hM0 3]
  have hy : |y - Γ 0| ≤ M := (abs_sub _ _).trans (by rw [hM])
  have hmem : y ∈ Set.uIcc (Γ (-M)) (Γ M) := by
    rcases hc.strictMono_of_inj (injective_of_expanding hκ hexp) with hm | ha
    · have a1 : Γ (-M) ≤ Γ 0 := hm.monotone (by linarith)
      have a2 : Γ 0 ≤ Γ M := hm.monotone hM0
      rw [abs_of_nonneg (by linarith)] at h1
      rw [abs_of_nonpos (by linarith)] at h2
      rw [Set.uIcc_of_le (by linarith)]
      rw [abs_le] at hy
      exact ⟨by linarith, by linarith⟩
    · have a1 : Γ 0 ≤ Γ (-M) := ha.antitone (by linarith)
      have a2 : Γ M ≤ Γ 0 := ha.antitone hM0
      rw [abs_of_nonpos (by linarith)] at h1
      rw [abs_of_nonneg (by linarith)] at h2
      rw [Set.uIcc_of_ge (by linarith)]
      rw [abs_le] at hy
      exact ⟨by linarith, by linarith⟩
  obtain ⟨z, -, hz⟩ := intermediate_value_uIcc hc.continuousOn hmem
  exact ⟨z, hz⟩

/-- Woodford (2003), App. A.3, p. 634 (tool): the inverse of an expanding continuous map
(well defined by `surjective_of_expanding`). -/
noncomputable def gInv {Ω : Type*} (Γ : ℕ → Ω → ℝ → ℝ) (hs : ∀ t ω, Function.Surjective (Γ t ω))
    (t : ℕ) (ω : Ω) (y : ℝ) : ℝ :=
  Classical.choose (hs t ω y)

/-- Woodford (2003), App. A.3, p. 634 (tool): `Γ(Γ⁻¹ y) = y`. -/
theorem gInv_spec {Ω : Type*} (Γ : ℕ → Ω → ℝ → ℝ) (hs : ∀ t ω, Function.Surjective (Γ t ω))
    (t : ℕ) (ω : Ω) (y : ℝ) : Γ t ω (gInv Γ hs t ω y) = y :=
  Classical.choose_spec (hs t ω y)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), App. A.3, p. 634 (the construction): the backward solution with horizon
`t + k`: `backW 0 t = 0`, `backW (k + 1) t = Γ_t⁻¹(E_t backW k (t + 1))`. -/
noncomputable def backW (Γ : ℕ → Ω → ℝ → ℝ) (hs : ∀ t ω, Function.Surjective (Γ t ω)) :
    ℕ → ℕ → Ω → ℝ
  | 0, _ => fun _ => 0
  | k + 1, t => fun ω => gInv Γ hs t ω (𝔼.E t (backW Γ hs k (t + 1)) ω)

/-- Woodford (2003), App. A.3, p. 634 (tool): the backward step,
`Γ_t(backW (k+1) t) = E_t backW k (t+1)`. -/
theorem backW_spec (Γ : ℕ → Ω → ℝ → ℝ) (hs : ∀ t ω, Function.Surjective (Γ t ω)) (k t : ℕ)
    (ω : Ω) : Γ t ω (backW 𝔼 Γ hs (k + 1) t ω) = 𝔼.E t (backW 𝔼 Γ hs k (t + 1)) ω :=
  gInv_spec Γ hs t ω _

/-- Woodford (2003), App. A.3, p. 634 (tool): the backward solutions stay within `R`. -/
theorem abs_backW_le {Γ : ℕ → Ω → ℝ → ℝ} (hs : ∀ t ω, Function.Surjective (Γ t ω)) {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 ≤ R) (hexp : ∀ t ω a b, |a - b| + κ * |a - b| ^ 3 ≤ |Γ t ω a - Γ t ω b|)
    (hsmall : ∀ t ω, |Γ t ω 0| ≤ κ * R ^ 3) (k : ℕ) :
    ∀ t ω, |backW 𝔼 Γ hs k t ω| ≤ R := by
  induction k with
  | zero =>
    intro t ω
    change |(0 : ℝ)| ≤ R
    simpa using hR
  | succ k ih =>
    intro t ω
    have hy := 𝔼.abs_E_le (fun ω' => ih (t + 1) ω') t ω
    have he := hexp t ω (backW 𝔼 Γ hs (k + 1) t ω) 0
    rw [sub_zero, backW_spec 𝔼 Γ hs k t ω] at he
    have hb : |𝔼.E t (backW 𝔼 Γ hs k (t + 1)) ω - Γ t ω 0| ≤ R + κ * R ^ 3 :=
      (abs_sub _ _).trans (add_le_add hy (hsmall t ω))
    by_contra hc
    push Not at hc
    have h3 : R ^ 3 < |backW 𝔼 Γ hs (k + 1) t ω| ^ 3 :=
      pow_lt_pow_left₀ hc hR (by norm_num)
    nlinarith

/-- Woodford (2003), App. A.3, p. 634 (tool): under informational closure the backward solutions
are known at their date. -/
theorem backW_known (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {Γ : ℕ → Ω → ℝ → ℝ}
    (hs : ∀ t ω, Function.Surjective (Γ t ω)) {κ : ℝ} (hκ : 0 < κ)
    (hexp : ∀ t ω a b, |a - b| + κ * |a - b| ^ 3 ≤ |Γ t ω a - Γ t ω b|)
    (hcell : ∀ t ω ω', LocalIFTStochastic.Ops.Indist 𝔼 t ω ω' → Γ t ω = Γ t ω') (k t : ℕ) :
    𝔼.E t (backW 𝔼 Γ hs k t) = backW 𝔼 Γ hs k t := by
  cases k with
  | zero => exact 𝔼.const t 0
  | succ k =>
    refine hcl t _ fun ω ω' h => ?_
    apply injective_of_expanding hκ (hexp t ω)
    rw [backW_spec 𝔼 Γ hs k t ω, hcell t ω ω' h, backW_spec 𝔼 Γ hs k t ω']
    exact LocalIFTStochastic.Ops.cellConst_E 𝔼 t _ ω ω' h

/-- Woodford (2003), App. A.3, p. 634 (the contraction): the sup-distance between horizons `k` and
`k + m` at every date and state. -/
noncomputable def dist_k (Γ : ℕ → Ω → ℝ → ℝ) (hs : ∀ t ω, Function.Surjective (Γ t ω))
    (k : ℕ) : ℝ :=
  ⨆ p : ℕ × Ω × ℕ, |backW 𝔼 Γ hs k p.1 p.2.1 - backW 𝔼 Γ hs (k + p.2.2) p.1 p.2.1|

/-- **The backward solutions converge uniformly** (Woodford (2003), App. A.3, p. 634):
`|backW k t − backW (k + m) t| ≤ d_k` with `d_k → 0`, uniformly in `t`, `ω`, `m`. -/
theorem backW_cauchy [Nonempty Ω] {Γ : ℕ → Ω → ℝ → ℝ} (hs : ∀ t ω, Function.Surjective (Γ t ω))
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 ≤ R)
    (hexp : ∀ t ω a b, |a - b| + κ * |a - b| ^ 3 ≤ |Γ t ω a - Γ t ω b|)
    (hsmall : ∀ t ω, |Γ t ω 0| ≤ κ * R ^ 3) :
    (∀ k t ω m, |backW 𝔼 Γ hs k t ω - backW 𝔼 Γ hs (k + m) t ω| ≤ dist_k 𝔼 Γ hs k) ∧
      Tendsto (dist_k 𝔼 Γ hs) atTop (𝓝 0) ∧ ∀ k, 0 ≤ dist_k 𝔼 Γ hs k := by
  have hb := abs_backW_le 𝔼 hs hκ hR hexp hsmall
  have hbdd : ∀ k, BddAbove (Set.range fun p : ℕ × Ω × ℕ =>
      |backW 𝔼 Γ hs k p.1 p.2.1 - backW 𝔼 Γ hs (k + p.2.2) p.1 p.2.1|) := fun k =>
    ⟨2 * R, by
      rintro _ ⟨p, rfl⟩
      exact (abs_sub _ _).trans (by linarith [hb k p.1 p.2.1, hb (k + p.2.2) p.1 p.2.1])⟩
  have hle : ∀ k t ω m, |backW 𝔼 Γ hs k t ω - backW 𝔼 Γ hs (k + m) t ω| ≤ dist_k 𝔼 Γ hs k :=
    fun k t ω m => le_ciSup (hbdd k) (t, ω, m)
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  have hd0 : ∀ k, 0 ≤ dist_k 𝔼 Γ hs k := fun k => (abs_nonneg _).trans (hle k 0 ω₀ 0)
  set Φ : ℝ → ℝ := fun x => x + κ * x ^ 3 with hΦ
  have hΦm : Monotone Φ := phi_mono hκ.le
  have hΦc : Continuous Φ := by fun_prop
  -- the key step `Φ(d_{k+1}) ≤ d_k`
  have hstep : ∀ k, Φ (dist_k 𝔼 Γ hs (k + 1)) ≤ dist_k 𝔼 Γ hs k := by
    intro k
    rw [dist_k, hΦm.map_ciSup_of_continuousAt hΦc.continuousAt (hbdd (k + 1))]
    refine ciSup_le fun p => ?_
    obtain ⟨t, ω, m⟩ := p
    have he := hexp t ω (backW 𝔼 Γ hs (k + 1) t ω) (backW 𝔼 Γ hs (k + m + 1) t ω)
    rw [backW_spec 𝔼 Γ hs k t ω, backW_spec 𝔼 Γ hs (k + m) t ω] at he
    have hE : 𝔼.E t (backW 𝔼 Γ hs k (t + 1)) ω - 𝔼.E t (backW 𝔼 Γ hs (k + m) (t + 1)) ω =
        𝔼.E t (backW 𝔼 Γ hs k (t + 1) - backW 𝔼 Γ hs (k + m) (t + 1)) ω := by
      rw [map_sub]
      rfl
    rw [hE] at he
    have h2 := he.trans (𝔼.abs_E_le (fun ω' => hle k (t + 1) ω' m) t ω)
    change Φ |backW 𝔼 Γ hs (k + 1) t ω - backW 𝔼 Γ hs (k + 1 + m) t ω| ≤ _
    rw [show k + 1 + m = k + m + 1 by omega]
    exact h2
  have hanti : Antitone (dist_k 𝔼 Γ hs) := antitone_nat_of_succ_le fun k => by
    have := hstep k
    have : 0 ≤ κ * dist_k 𝔼 Γ hs (k + 1) ^ 3 := mul_nonneg hκ.le (pow_nonneg (hd0 _) 3)
    simp only [hΦ] at *
    linarith
  have hbb : BddBelow (Set.range (dist_k 𝔼 Γ hs)) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hd0 k⟩
  set L := ⨅ k, dist_k 𝔼 Γ hs k with hL
  have hL0 : 0 ≤ L := le_ciInf hd0
  have hΦL : Φ L ≤ L := le_ciInf fun k =>
    (hΦm (ciInf_le hbb (k + 1))).trans (hstep k)
  have hLz : L = 0 := by
    simp only [hΦ] at hΦL
    have : κ * L ^ 3 ≤ 0 := by linarith
    rcases hL0.lt_or_eq with h | h
    · linarith [mul_pos hκ (pow_pos h 3)]
    · exact h.symm
  refine ⟨hle, ?_, hd0⟩
  rw [← hLz]
  exact tendsto_atTop_ciInf hanti hbb

/-- **Existence for expanding forward recursions** (Woodford (2003), App. A.3, p. 634): for an
informationally closed expectation system on a nonempty state space and maps `Γ_t(ω, ·)` that
are continuous, uniformly expanding, known at `t`, with `|Γ_t(ω, 0)| ≤ κR³`, there is a process
`i`, known at every date, with `|i_t| ≤ R` and `E_t i_{t+1} = Γ_t(i_t)`. -/
theorem exists_expanding [Nonempty Ω] (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼)
    {Γ : ℕ → Ω → ℝ → ℝ} {κ R : ℝ} (hκ : 0 < κ) (hR : 0 ≤ R) (hc : ∀ t ω, Continuous (Γ t ω))
    (hexp : ∀ t ω a b, |a - b| + κ * |a - b| ^ 3 ≤ |Γ t ω a - Γ t ω b|)
    (hsmall : ∀ t ω, |Γ t ω 0| ≤ κ * R ^ 3)
    (hcell : ∀ t ω ω', LocalIFTStochastic.Ops.Indist 𝔼 t ω ω' → Γ t ω = Γ t ω') :
    ∃ i : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (i t) = i t) ∧ (∀ t ω, |i t ω| ≤ R) ∧
      ∀ t, 𝔼.E t (i (t + 1)) = fun ω => Γ t ω (i t ω) := by
  have hs : ∀ t ω, Function.Surjective (Γ t ω) := fun t ω =>
    surjective_of_expanding (hc t ω) hκ (hexp t ω)
  obtain ⟨hle, hd, -⟩ := backW_cauchy 𝔼 hs hκ hR hexp hsmall
  have hcs : ∀ t ω, CauchySeq fun k => backW 𝔼 Γ hs k t ω := fun t ω =>
    cauchySeq_of_le_tendsto_0 (fun N => 2 * dist_k 𝔼 Γ hs N) (fun n m N hn hm => by
      rw [Real.dist_eq]
      have h1 := hle N t ω (n - N)
      have h2 := hle N t ω (m - N)
      rw [show N + (n - N) = n by omega] at h1
      rw [show N + (m - N) = m by omega] at h2
      refine (abs_sub_le _ (backW 𝔼 Γ hs N t ω) _).trans ?_
      rw [abs_sub_comm (backW 𝔼 Γ hs n t ω)]
      linarith) (by simpa using hd.const_mul 2)
  choose lim hlim using fun t ω => cauchySeq_tendsto_of_complete (hcs t ω)
  have hunif : ∀ k t ω, |backW 𝔼 Γ hs k t ω - lim t ω| ≤ dist_k 𝔼 Γ hs k := by
    intro k t ω
    have ht : Tendsto (fun m => |backW 𝔼 Γ hs k t ω - backW 𝔼 Γ hs (m + k) t ω|) atTop
        (𝓝 |backW 𝔼 Γ hs k t ω - lim t ω|) :=
      (tendsto_const_nhds.sub ((hlim t ω).comp (tendsto_add_atTop_nat k))).abs
    refine le_of_tendsto' ht fun m => ?_
    have := hle k t ω m
    rwa [add_comm k m] at this
  have hW := backW_known 𝔼 hcl hs hκ hexp hcell
  refine ⟨lim, fun t => ?_, fun t ω => ?_, fun t => ?_⟩
  · funext ω
    have hb : ∀ k, |𝔼.E t (lim t) ω - lim t ω| ≤ 2 * dist_k 𝔼 Γ hs k := by
      intro k
      have h1 : |𝔼.E t (lim t - backW 𝔼 Γ hs k t) ω| ≤ dist_k 𝔼 Γ hs k :=
        𝔼.abs_E_le (fun ω' => by
          simp only [Pi.sub_apply]
          rw [abs_sub_comm]
          exact hunif k t ω') t ω
      have e : 𝔼.E t (lim t) ω - lim t ω =
          𝔼.E t (lim t - backW 𝔼 Γ hs k t) ω + (backW 𝔼 Γ hs k t ω - lim t ω) := by
        rw [map_sub, hW k t]
        simp only [Pi.sub_apply]
        ring
      rw [e]
      exact (abs_add_le _ _).trans (by linarith [hunif k t ω])
    have h0 := ge_of_tendsto' (hd.const_mul 2) hb
    rw [mul_zero] at h0
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)
  · exact le_of_tendsto' (hlim t ω).abs fun k => abs_backW_le 𝔼 hs hκ hR hexp hsmall k t ω
  · funext ω
    have ha : Tendsto (fun k => Γ t ω (backW 𝔼 Γ hs (k + 1) t ω)) atTop
        (𝓝 (Γ t ω (lim t ω))) :=
      ((hc t ω).tendsto _).comp ((hlim t ω).comp (tendsto_add_atTop_nat 1))
    have hb : Tendsto (fun k => 𝔼.E t (backW 𝔼 Γ hs k (t + 1)) ω) atTop
        (𝓝 (𝔼.E t (lim (t + 1)) ω)) := by
      refine tendsto_iff_dist_tendsto_zero.mpr
        (squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hd)
      rw [Real.dist_eq]
      have e : 𝔼.E t (backW 𝔼 Γ hs k (t + 1)) ω - 𝔼.E t (lim (t + 1)) ω =
          𝔼.E t (backW 𝔼 Γ hs k (t + 1) - lim (t + 1)) ω := by
        rw [map_sub]
        rfl
      rw [e]
      exact 𝔼.abs_E_le (fun ω' => hunif k (t + 1) ω') t ω
    have hab : (fun k => Γ t ω (backW 𝔼 Γ hs (k + 1) t ω)) =
        fun k => 𝔼.E t (backW 𝔼 Γ hs k (t + 1)) ω :=
      funext fun k => backW_spec 𝔼 Γ hs k t ω
    rw [hab] at ha
    exact tendsto_nhds_unique hb ha

/-- **Uniqueness for expanding forward recursions** (Woodford (2003), App. A.3, p. 634): two
bounded processes known at every date with `E_t i_{t+1} = Γ_t(i_t)`, `Γ` uniformly expanding,
coincide. -/
theorem unique_expanding {Γ : ℕ → Ω → ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hexp : ∀ t ω a b, |a - b| + κ * |a - b| ^ 3 ≤ |Γ t ω a - Γ t ω b|) {i j : ℕ → Ω → ℝ}
    (hib : ∃ B, ∀ t ω, |i t ω| ≤ B) (hjb : ∃ B, ∀ t ω, |j t ω| ≤ B)
    (hi : ∀ t, 𝔼.E t (i (t + 1)) = fun ω => Γ t ω (i t ω))
    (hj : ∀ t, 𝔼.E t (j (t + 1)) = fun ω => Γ t ω (j t ω)) : i = j := by
  obtain ⟨Bi, hBi⟩ := hib
  obtain ⟨Bj, hBj⟩ := hjb
  have hz : ∀ p : ℕ × Ω, i p.1 p.2 - j p.1 p.2 = 0 := by
    refine eq_zero_of_push (fun p : ℕ × Ω => i p.1 p.2 - j p.1 p.2) ⟨Bi + Bj, fun p => ?_⟩
      (inv_pos.mpr hκ) fun B hB p => ?_
    · exact (abs_sub _ _).trans (add_le_add (hBi _ _) (hBj _ _))
    · obtain ⟨t, ω⟩ := p
      have hb := 𝔼.abs_E_le (fun ω' => hB (t + 1, ω')) t ω
      have e : 𝔼.E t (fun ω' => i (t + 1) ω' - j (t + 1) ω') ω = Γ t ω (i t ω) - Γ t ω (j t ω) := by
        have := map_sub (𝔼.E t) (i (t + 1)) (j (t + 1))
        rw [show (fun ω' => i (t + 1) ω' - j (t + 1) ω') = i (t + 1) - j (t + 1) from rfl, this,
          hi, hj]
        rfl
      change |𝔼.E t (fun ω' => i (t + 1) ω' - j (t + 1) ω') ω| ≤ B at hb
      rw [e] at hb
      have he := (hexp t ω (i t ω) (j t ω)).trans hb
      change |i t ω - j t ω| ^ 3 ≤ κ⁻¹ * (B - |i t ω - j t ω|)
      rw [inv_mul_eq_div, le_div_iff₀ hκ]
      linarith
  funext t ω
  exact sub_eq_zero.mp (hz (t, ω))

/-! ### The affine-in-inflation rule: existence and uniqueness with small disturbances -/

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): the composite disturbance
`f_t = E_t ν_{t+1} − φ_π E_t r̂_t` driving the interest rate, `E_t î_{t+1} = g(î_t) + f_t`. -/
noncomputable def forceA (φ : ℝ) (e : LocalIFTStochastic.BFun (ℕ × Ω) (Fin 2 → ℝ)) (t : ℕ) :
    Ω → ℝ :=
  𝔼.E t (fun ω => e (t + 1, ω) 1) - φ • 𝔼.E t (fun ω => e (t, ω) 0)

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): the composite disturbance is known at `t`. -/
theorem forceA_known (φ : ℝ) (e : LocalIFTStochastic.BFun (ℕ × Ω) (Fin 2 → ℝ)) (t : ℕ) :
    𝔼.E t (forceA 𝔼 φ e t) = forceA 𝔼 φ e t := by
  rw [forceA, map_sub, map_smul, 𝔼.E_E_self, 𝔼.E_E_self]

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): `|f_t| ≤ (1 + |φ_π|)‖e‖`. -/
theorem abs_forceA_le (φ : ℝ) (e : LocalIFTStochastic.BFun (ℕ × Ω) (Fin 2 → ℝ)) (t : ℕ)
    (ω : Ω) : |forceA 𝔼 φ e t ω| ≤ (1 + |φ|) * ‖e‖ := by
  have habs : ∀ p j, |e p j| ≤ ‖e‖ := fun p j => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ j).trans (LocalIFTStochastic.norm_apply_le e p)
  have h1 := 𝔼.abs_E_le (fun ω' => habs (t + 1, ω') 1) t ω
  have h2 := 𝔼.abs_E_le (fun ω' => habs (t, ω') 0) t ω
  simp only [forceA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  nlinarith [abs_nonneg φ]

/-- Woodford (2003), Prop. 2.8, p. 96, under uncertainty (tool): **in every equilibrium of the
rule `φ_π π + h(î_{−1})` (informational closure), `E_t î_{t+1} = φ_π î_t + h(î_t) + f_t`.** -/
theorem affine_i_rec (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {Ψ : ℝ × ℝ → ℝ} {φ : ℝ}
    {h : ℝ → ℝ} (hΨ : ∀ π i, Ψ (π, i) = φ * π + h i) {u : ParS (Fin 2) (Fin 2 → ℝ) Ω}
    {x : SProcV (Fin 2) Ω} (hx : SolvesSV 𝔼 (Finert Ψ) u x) (t : ℕ) :
    𝔼.E t (toP x (t + 1) 1) =
      fun ω => φ * toP x t 1 ω + h (toP x t 1 ω) + forceA 𝔼 φ u.2 t ω := by
  have e1 := eq1_of_solves hx (t + 1)
  have hΨf : (fun ω => Ψ (x (t + 1, ω) 0, lagV u.1 (fun s => x (s, ω)) (t + 1) 1)) =
      φ • toP x (t + 1) 0 + fun ω => h (toP x t 1 ω) := by
    funext ω
    simp only [hΨ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, lagV_succ]
    rfl
  have hk1 : 𝔼.E (t + 1) (fun ω => h (toP x t 1 ω)) = fun ω => h (toP x t 1 ω) :=
    known_comp hcl (lag_known hx (t + 1)) h
  rw [hΨf, map_add, map_smul, hx.1 (t + 1) 0, hk1] at e1
  have hk0 : 𝔼.E t (fun ω => h (toP x t 1 ω)) = fun ω => h (toP x t 1 ω) :=
    known_comp hcl (hx.1 t 1) h
  rw [e1, map_add, map_add, map_smul, 𝔼.tower (Nat.le_succ t), hk0, eq0_of_solves hx t]
  funext ω
  simp only [forceA, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- **Existence and uniqueness on the boundary with small disturbances, `φ_π ≠ 0`** (Woodford
(2003), Prop. 2.8, p. 96; App. A.3, pp. 632–634): under informational closure on a nonempty state
space (perfect foresight, every finite event tree), for the rule `Ψ(π, i) = φ_π π + h(i)` with
`φ_π ≠ 0`, `h` continuous, `h(0) = 0` and an expanding diagonal, for every initial rate and every
disturbance process with `(1 + |φ_π|)‖e‖ ≤ κR³` there is **exactly one** bounded adapted
equilibrium, and its interest rate stays within `R` of the steady state (so within
`((1 + |φ_π|)‖e‖/κ)^{1/3}`). -/
theorem exists_unique_affine [Nonempty Ω] (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼)
    {Ψ : ℝ × ℝ → ℝ} {φ κ R : ℝ} {h : ℝ → ℝ} (hΨ : ∀ π i, Ψ (π, i) = φ * π + h i) (hφ : φ ≠ 0)
    (hκ : 0 < κ) (hR : 0 ≤ R) (hhc : Continuous h) (hh0 : h 0 = 0)
    (hexp : ∀ i i', |i - i'| + κ * |i - i'| ^ 3 ≤ |(φ * i + h i) - (φ * i' + h i')|)
    (xm : Fin 2 → ℝ) (e : LocalIFTStochastic.BFun (ℕ × Ω) (Fin 2 → ℝ))
    (he : (1 + |φ|) * ‖e‖ ≤ κ * R ^ 3) :
    ∃ x : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert Ψ) (xm, e) x ∧ (∀ t ω, |x (t, ω) 1| ≤ R) ∧
      ∀ y : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert Ψ) (xm, e) y → y = x := by
  set Γ : ℕ → Ω → ℝ → ℝ := fun t ω z => φ * z + h z + forceA 𝔼 φ e t ω with hΓ
  have hc : ∀ t ω, Continuous (Γ t ω) := fun t ω =>
    ((continuous_const.mul continuous_id).add hhc).add continuous_const
  have hexp' : ∀ t ω a b, |a - b| + κ * |a - b| ^ 3 ≤ |Γ t ω a - Γ t ω b| := by
    intro t ω a b
    have : Γ t ω a - Γ t ω b = (φ * a + h a) - (φ * b + h b) := by simp only [hΓ]; ring
    rw [this]
    exact hexp a b
  have hsmall : ∀ t ω, |Γ t ω 0| ≤ κ * R ^ 3 := fun t ω => by
    simp only [hΓ, mul_zero, hh0, zero_add]
    exact (abs_forceA_le 𝔼 φ e t ω).trans he
  have hcell : ∀ t ω ω', LocalIFTStochastic.Ops.Indist 𝔼 t ω ω' → Γ t ω = Γ t ω' :=
    fun t ω ω' hi => by
      funext z
      simp only [hΓ]
      rw [LocalIFTStochastic.Ops.cellConst_of_known 𝔼 (forceA_known 𝔼 φ e t) ω ω' hi]
  obtain ⟨i, hik, hib, hirec⟩ := exists_expanding 𝔼 hcl hκ hR hc hexp' hsmall hcell
  -- the lagged rate, inflation, and their bounds
  set lagI : ℕ → Ω → ℝ := fun t ω => lagV (xm 1) (fun s => i s ω) t with hlagI
  set ν : ℕ → Ω → ℝ := fun t ω => e (t, ω) 1 with hν
  set pz : ℕ → Ω → ℝ := fun t ω => (i t ω - h (lagI t ω) - 𝔼.E t (ν t) ω) / φ with hpz
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hhc.continuousOn
  have hhl : ∀ t ω, |h (lagI t ω)| ≤ max C |h (xm 1)| := by
    intro t ω
    cases t with
    | zero => exact le_max_right _ _
    | succ t =>
      have := hC (i t ω) (abs_le.mp (hib t ω) |> fun h' => ⟨h'.1, h'.2⟩)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
  have habs : ∀ p j, |e p j| ≤ ‖e‖ := fun p j => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ j).trans (LocalIFTStochastic.norm_apply_le e p)
  set Bp := (R + max C |h (xm 1)| + ‖e‖) / |φ| with hBp
  have hpzb : ∀ t ω, |pz t ω| ≤ Bp := by
    intro t ω
    have h3 := 𝔼.abs_E_le (fun ω' => habs (t, ω') 1) t ω
    simp only [hpz, abs_div]
    rw [hBp]
    refine div_le_div_of_nonneg_right ((abs_sub _ _).trans ?_) (abs_nonneg φ)
    exact add_le_add ((abs_sub _ _).trans (add_le_add (hib t ω) (hhl t ω))) h3
  set x : SProcV (Fin 2) Ω := LocalIFTStochastic.mkB (fun p => ![pz p.1 p.2, i p.1 p.2])
    ⟨max Bp R, fun p => (pi_norm_le_iff_of_nonneg ((abs_nonneg _).trans
      ((hib p.1 p.2).trans (le_max_right _ _)))).mpr fun j => by
        rw [Real.norm_eq_abs]
        fin_cases j
        · exact (hpzb p.1 p.2).trans (le_max_left _ _)
        · exact (hib p.1 p.2).trans (le_max_right _ _)⟩ with hx
  have hx0 : ∀ t, toP x t 0 = pz t := fun _ => rfl
  have hx1 : ∀ t, toP x t 1 = i t := fun _ => rfl
  have hlagk : ∀ t, 𝔼.E t (fun ω => h (lagI t ω)) = fun ω => h (lagI t ω) := by
    intro t
    cases t with
    | zero =>
      change 𝔼.E 0 (fun _ => h (xm 1)) = fun _ => h (xm 1)
      exact 𝔼.const 0 _
    | succ s =>
      have hk : 𝔼.E (s + 1) (i s) = i s := by
        conv_lhs => rw [← hik s]
        rw [𝔼.known (Nat.le_succ s), hik s]
      exact known_comp hcl hk h
  have hpzf : ∀ t, pz t = φ⁻¹ • (i t - (fun ω => h (lagI t ω)) - 𝔼.E t (ν t)) := by
    intro t
    funext ω
    simp only [hpz, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [div_eq_inv_mul]
  have hpzk : ∀ t, 𝔼.E t (pz t) = pz t := by
    intro t
    rw [hpzf, map_smul, map_sub, map_sub, hik, hlagk, 𝔼.E_E_self]
  have hsol : SolvesSV 𝔼 (Finert Ψ) (xm, e) x := by
    refine ⟨fun t j => ?_, fun t j => ?_⟩
    · fin_cases j
      · exact hpzk t
      · exact hik t
    · fin_cases j
      · -- the Fisher equation
        have hf : (fun ω => Finert Ψ (ptS (((xm, e) : ParS (Fin 2) (Fin 2 → ℝ) Ω), x) (t, ω)) 0) =
            i t - pz (t + 1) - fun ω => e (t, ω) 0 := rfl
        change 𝔼.E t (fun ω => Finert Ψ (ptS (((xm, e) : ParS (Fin 2) (Fin 2 → ℝ) Ω), x)
          (t, ω)) 0) = 0
        have hEpz : 𝔼.E t (pz (t + 1)) = i t - 𝔼.E t (fun ω => e (t, ω) 0) := by
          have hk : 𝔼.E t (fun ω => h (lagI (t + 1) ω)) = fun ω => h (lagI (t + 1) ω) :=
            known_comp hcl (hik t) h
          rw [hpzf, map_smul, map_sub, map_sub, hirec, hk, 𝔼.tower (Nat.le_succ t)]
          funext ω
          simp only [hΓ, forceA, hν, hlagI, lagV_succ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          field_simp
          ring
        rw [hf, map_sub, map_sub, hik, hEpz]
        funext ω
        simp
      · -- the rule
        have hf : (fun ω => Finert Ψ (ptS (((xm, e) : ParS (Fin 2) (Fin 2 → ℝ) Ω), x) (t, ω)) 1) =
            i t - (φ • pz t + fun ω => h (lagI t ω)) - ν t := by
          funext ω
          have hl : lagV xm (fun s => x (s, ω)) t 1 = lagI t ω := by
            cases t <;> rfl
          simp only [Finert, ptS, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.sub_apply,
            Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [hl, hΨ]
          rfl
        change 𝔼.E t (fun ω => Finert Ψ (ptS (((xm, e) : ParS (Fin 2) (Fin 2 → ℝ) Ω), x)
          (t, ω)) 1) = 0
        rw [hf, map_sub, map_sub, map_add, map_smul, hik, hpzk, hlagk]
        funext ω
        simp only [hpz, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        field_simp
        ring
  exact ⟨x, hsol, fun t ω => hib t ω, fun y hy => unique_affine hcl hΨ hφ hκ hexp hy hsol⟩

/-- **The resonant shock: an explicit cube-root equilibrium** (Woodford (2003), Prop. 2.8, p. 96;
App. A.3, p. 634): let `σ = φ_π + ρ` with `σ² = 1` and `φ_π ≠ 0`. For the repelling cubic rule
`φ_π π + ρ i + σ i³` and the policy shock `ν_t = δσᵗ` (for which the linear rule has no bounded
equilibrium, `InertialBoundary.no_eq_unit`), under informational closure every bounded
equilibrium has `î_t = σᵗ ∛(−δ)`: the response to the shock is of order `|δ|^{1/3}`. -/
theorem resonant_cube_root (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {φ ρ : ℝ}
    (hσ : (φ + ρ) * (φ + ρ) = 1) {δ : ℝ} (xm : Fin 2 → ℝ) {x : SProcV (Fin 2) Ω}
    (hx : SolvesSV 𝔼 (Finert (ruleCubI φ ρ (φ + ρ))) (xm, resShock δ (φ + ρ) hσ) x) :
    ∀ t ω, x (t, ω) 1 = (φ + ρ) ^ t * cbrt (-δ) := by
  set σ := φ + ρ with hσdef
  have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  have hΨ : ∀ π i, ruleCubI φ ρ σ (π, i) = φ * π + (ρ * i + σ * i ^ 3) := fun π i => by
    simp only [ruleCubI]
    ring
  have hfA : ∀ t, forceA 𝔼 φ (resShock δ σ hσ) t = fun _ => δ * σ ^ (t + 1) := by
    intro t
    have h1 : 𝔼.E t (fun ω => (resShock (Ω := Ω) δ σ hσ) (t + 1, ω) 1) =
        fun _ => δ * σ ^ (t + 1) := by
      change 𝔼.E t (fun _ => δ * σ ^ (t + 1)) = _
      exact 𝔼.const t _
    have h0 : 𝔼.E t (fun ω => (resShock (Ω := Ω) δ σ hσ) (t, ω) 0) = 0 := by
      change 𝔼.E t (fun _ => 0) = 0
      exact 𝔼.const t 0
    rw [forceA, h1, h0, smul_zero, sub_zero]
  set Γ : ℕ → Ω → ℝ → ℝ := fun t _ z => σ * (z + z ^ 3) + δ * σ ^ (t + 1) with hΓ
  have hexp : ∀ t ω a b, |a - b| + 1 / 4 * |a - b| ^ 3 ≤ |Γ t ω a - Γ t ω b| := by
    intro t ω a b
    have : Γ t ω a - Γ t ω b = σ * (a + a ^ 3) - σ * (b + b ^ 3) := by simp only [hΓ]; ring
    rw [this]
    exact expand_cubic hσ a b
  set c := cbrt (-δ) with hc
  have hpow : ∀ t, σ ^ t * σ ^ t = 1 := fun t => by rw [← mul_pow, hσ, one_pow]
  have hi : ∀ t, 𝔼.E t (toP x (t + 1) 1) = fun ω => Γ t ω (toP x t 1 ω) := by
    intro t
    have h := affine_i_rec 𝔼 hcl hΨ hx t
    change _ = fun ω => φ * toP x t 1 ω + (ρ * toP x t 1 ω + σ * toP x t 1 ω ^ 3) +
      forceA 𝔼 φ (resShock δ σ hσ) t ω at h
    rw [h, hfA]
    funext ω
    simp only [hΓ, hσdef]
    ring
  have hj : ∀ t, 𝔼.E t (fun _ : Ω => σ ^ (t + 1) * c) =
      fun ω => Γ t ω ((fun _ : Ω => σ ^ t * c) ω) := by
    intro t
    rw [𝔼.const]
    funext ω
    simp only [hΓ]
    have hc3 : c ^ 3 = -δ := cbrt_pow _
    have e : (σ ^ t * c) ^ 3 = σ ^ t * (σ ^ t * σ ^ t) * c ^ 3 := by ring
    rw [e, hpow, hc3, pow_succ]
    ring
  have heq := unique_expanding 𝔼 (by norm_num : (0 : ℝ) < 1 / 4) hexp
    (i := fun t => toP x t 1) (j := fun t _ => σ ^ t * c)
    ⟨‖x‖, fun t ω => abs_apply_le x t ω 1⟩
    ⟨|c|, fun t ω => by rw [abs_mul, abs_pow, hs, one_pow, one_mul]⟩ hi hj
  intro t ω
  exact congrFun (congrFun heq t) ω

/-! ### The cubic response to inflation (`φ_π = 0`) under perfect foresight -/

/-- **Existence and uniqueness on the boundary with small disturbances, `φ_π = 0`, perfect
foresight** (Woodford (2003), Prop. 2.8, p. 96; App. A.3, pp. 632–634): for the rule
`ρ î_{−1} + σπ³` with `σ² = 1`, `σρ ≥ 1`, for every initial rate and every disturbance sequence
with `‖e‖ + ‖e‖³ ≤ R³/4` there is exactly one bounded perfect-foresight equilibrium, and its
interest rate stays within `R`. -/
theorem exists_unique_cube_pf {ρ σ R : ℝ} (hσ : σ * σ = 1) (hτ : 1 ≤ σ * ρ) (hR : 0 ≤ R)
    (xm : Fin 2 → ℝ) (e : LocalIFTStochastic.BFun (ℕ × Unit) (Fin 2 → ℝ))
    (he : ‖e‖ + ‖e‖ ^ 3 ≤ 1 / 4 * R ^ 3) :
    ∃ x : SProcV (Fin 2) Unit,
      SolvesSV perfectForesight (Finert (InertialBoundary.ruleCubPi ρ σ)) (xm, e) x ∧
      (∀ t, |x (t, ()) 1| ≤ R) ∧ ∀ y : SProcV (Fin 2) Unit,
        SolvesSV perfectForesight (Finert (InertialBoundary.ruleCubPi ρ σ)) (xm, e) y → y = x := by
  have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  have habs : ∀ p j, |e p j| ≤ ‖e‖ := fun p j => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ j).trans (LocalIFTStochastic.norm_apply_le e p)
  set r : ℕ → ℝ := fun t => e (t, ()) 0 with hr
  set ν : ℕ → ℝ := fun t => e (t, ()) 1 with hν
  set Γ : ℕ → Unit → ℝ → ℝ := fun t _ z => ρ * z + σ * (z - r t) ^ 3 + ν (t + 1) with hΓ
  have hc : ∀ t u, Continuous (Γ t u) := fun t u => by
    simp only [hΓ]
    fun_prop
  have hexp : ∀ t u a b, |a - b| + 1 / 4 * |a - b| ^ 3 ≤ |Γ t u a - Γ t u b| := by
    intro t u a b
    set Q := (a - r t) ^ 2 + (a - r t) * (b - r t) + (b - r t) ^ 2 with hQ
    have e1 : Γ t u a - Γ t u b = σ * ((a - b) * (σ * ρ + Q)) := by
      simp only [hΓ, hQ]
      linear_combination (-(ρ * (a - b))) * hσ
    have hQ4 : (a - b) ^ 2 / 4 ≤ Q := by nlinarith [sq_nonneg (a + b - 2 * r t)]
    rw [e1, abs_mul, hs, one_mul, abs_mul, abs_of_pos (by nlinarith [sq_nonneg (a - b)] :
      (0 : ℝ) < σ * ρ + Q)]
    have h3 : |a - b| ^ 3 = |a - b| * (a - b) ^ 2 := by
      rw [pow_succ', ← sq_abs (a - b)]
    rw [h3]
    nlinarith [abs_nonneg (a - b)]
  have hsmall : ∀ t u, |Γ t u 0| ≤ 1 / 4 * R ^ 3 := by
    intro t u
    simp only [hΓ, mul_zero, zero_add, zero_sub]
    have h1 : |σ * (-r t) ^ 3| ≤ ‖e‖ ^ 3 := by
      rw [abs_mul, hs, one_mul, abs_pow, abs_neg]
      exact pow_le_pow_left₀ (abs_nonneg _) (habs _ 0) 3
    have h2 : |ν (t + 1)| ≤ ‖e‖ := habs _ 1
    exact (abs_add_le _ _).trans (by linarith)
  obtain ⟨i, -, hib, hirec⟩ := exists_expanding perfectForesight
    LocalIFTStochastic.perfectForesight_infoClosed (by norm_num : (0 : ℝ) < 1 / 4) hR hc hexp
    hsmall (fun t u u' _ => by rw [Subsingleton.elim u u'])
  have hrec : ∀ t, i (t + 1) () = Γ t () (i t ()) := fun t => congrFun (hirec t) ()
  set pz : ℕ → ℝ := fun t => match t with
    | 0 => cbrt (σ * (i 0 () - ρ * xm 1 - ν 0))
    | t + 1 => i t () - r t with hpz
  have hpzb : ∀ t, |pz t| ≤ max |pz 0| (R + ‖e‖) := by
    intro t
    cases t with
    | zero => exact le_max_left _ _
    | succ t =>
      refine le_trans ?_ (le_max_right _ _)
      exact (abs_sub _ _).trans (add_le_add (hib t ()) (habs _ 0))
  set x : SProcV (Fin 2) Unit := LocalIFTStochastic.mkB (fun p => ![pz p.1, i p.1 p.2])
    ⟨max (max |pz 0| (R + ‖e‖)) R, fun p => (pi_norm_le_iff_of_nonneg ((abs_nonneg _).trans
      ((hib p.1 p.2).trans (le_max_right _ _)))).mpr fun j => by
        rw [Real.norm_eq_abs]
        fin_cases j
        · exact (hpzb p.1).trans (le_max_left _ _)
        · exact (hib p.1 p.2).trans (le_max_right _ _)⟩ with hx
  have hsol : SolvesSV perfectForesight (Finert (InertialBoundary.ruleCubPi ρ σ)) (xm, e) x := by
    refine ⟨fun t j => rfl, fun t j => ?_⟩
    change (fun u => Finert (InertialBoundary.ruleCubPi ρ σ)
      (ptS (((xm, e) : ParS (Fin 2) (Fin 2 → ℝ) Unit), x) (t, u)) j) = 0
    funext u
    obtain rfl : u = () := Subsingleton.elim _ _
    fin_cases j
    · change i t () - pz (t + 1) - r t = 0
      simp only [hpz]
      ring
    · cases t with
      | zero =>
        change i 0 () - (ρ * xm 1 + σ * pz 0 ^ 3) - ν 0 = 0
        simp only [hpz]
        rw [cbrt_pow]
        linear_combination (-(i 0 () - ρ * xm 1 - ν 0)) * hσ
      | succ t =>
        change i (t + 1) () - (ρ * i t () + σ * pz (t + 1) ^ 3) - ν (t + 1) = 0
        rw [hrec t]
        simp only [hpz, hΓ]
        ring
  refine ⟨x, hsol, fun t => hib t (), fun y hy => unique_cube
    LocalIFTStochastic.perfectForesight_infoClosed (fun π i => rfl) hσ hτ hy hsol⟩

end Woodford.PriceLevelDetermination.InertialBoundaryExist
