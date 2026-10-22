/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.InertialBoundaryExist

/-!
# The boundary rule `ρ î_{−1} + σπ³` under uncertainty: existence with small disturbances

Woodford (2003), *Interest and Prices*, Prop. 2.8, p. 96, and App. A.3, pp. 632–634. For the
`φ_π = 0` boundary rule `Ψ(π, i) = ρ i + σπ³` (`σ² = 1`, `σρ ≥ 1`), `InertialBoundary.unique_cube`
gives uniqueness for every expectation system with informational closure, and
`InertialBoundaryExist.exists_unique_cube_pf` gives existence under perfect foresight. Here
existence is proved for **every informationally closed expectation system**.

## The construction: choosing the inflation innovations

The rule gives `σπ_t³ = î_t − ρ î_{t−1} − E_t ν_t`, so inflation is a function of the
interest-rate path, `π_{t+1} = ∛(σ(î_{t+1} − ρ î_t − E_{t+1}ν_{t+1}))`, and the Fisher equation
becomes the backward condition
`E_t ∛(σ(î_{t+1} − ρ î_t − E_{t+1}ν_{t+1})) = î_t − E_t r̂_t` (see `rel_Tcube`). Given `î_{t+1}`,
this has exactly one solution `î_t` in every state (`Tcube`; the left side is decreasing in
`î_t`), the solution is known at `t` (informational closure), it stays within `R` for small
disturbances (`abs_Tcube_le`), and the map is a weak contraction in the sup norm:
`|δ| + |δ|³/4 ≤ D` (`Tcube_contract`). Iterating backwards from a far horizon and letting the
horizon go to infinity (`exists_limit_backward`, a uniform-limit engine) gives a bounded,
adapted interest-rate path solving this relation at every date; inflation surprises are whatever the
cube root of the interest-rate and policy-shock surprises makes them.

The one step that needs care: `E_t` of a nonlinear function of a known variable `x` and an
unknown `c` equals, in state `ω`, `E_t` of the same function with `x` frozen at `x(ω)`
(`E_eq_of_eqOn_cell`) — this follows from informational closure alone (the indicator of an
information cell is known), for bounded functions.

## Main results

* `exists_unique_cube`: under informational closure on a nonempty state space, for every
  initial rate and every disturbance process with `‖e‖ ≤ R/2` and `‖e‖ ≤ R³/8`, there is
  **exactly one** bounded adapted equilibrium, with `|î_t| ≤ R` (so `|î_t| ≤ 2‖e‖^{1/3}` for
  small shocks), and `π_0 = ∛(σ(î_0 − ρ î_{−1} − E_0 ν_0))`.
* `resonant_cube_root_pi`: for `ρ = σ` and the resonant shock `ν_t = δσᵗ`, every equilibrium has
  `î_t = σᵗ ∛(−δ)` — the response is of order `|δ|^{1/3}`, not differentiable in `δ`.
-/

namespace Woodford.PriceLevelDetermination.InertialBoundaryExistCube

open scoped Topology Matrix
open Filter
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic SunspotsBoundedBelow
open LocalIFTSystems (Arg cbrt cbrt_pow abs_le_of_pow_three)
open LocalIFTSystemsApps (Finert)
open InertialBoundary (eq0_of_solves eq1_of_solves unique_cube ruleCubPi sub_le_cbrt
  pow_le_of_le_cbrt resShock)
open InertialBoundaryExist (phi_mono)

/-! ### Cube roots -/

/-- Woodford (2003), App. A.3, p. 634 (tool): the real cube root is strictly increasing. -/
theorem cbrt_strictMono : StrictMono cbrt := by
  intro a b hab
  by_contra h
  push Not at h
  have := (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).monotone h
  simp only [cbrt_pow] at this
  linarith

/-- Woodford (2003), App. A.3, p. 634 (tool): `∛(x³) = x`. -/
theorem cbrt_cube (x : ℝ) : cbrt (x ^ 3) = x :=
  (Odd.pow_injective (by decide : Odd 3)) (cbrt_pow _)

/-- Woodford (2003), App. A.3, p. 634 (tool): `∛(−u) = −∛u`. -/
theorem cbrt_neg (u : ℝ) : cbrt (-u) = -cbrt u := by
  have h : (-cbrt u) ^ 3 = -u := by rw [neg_pow, cbrt_pow]; ring
  rw [← h, cbrt_cube]

/-- Woodford (2003), App. A.3, p. 634 (tool): `u ≤ ε³` implies `∛u ≤ ε`. -/
theorem cbrt_le_of_le_pow {u ε : ℝ} (hu : u ≤ ε ^ 3) : cbrt u ≤ ε :=
  (cbrt_strictMono.monotone hu).trans_eq (cbrt_cube ε)

/-- Woodford (2003), App. A.3, p. 634 (tool): **the cube root is uniformly Hölder**,
`|∛a − ∛b| ≤ ∛(4|a − b|)`. -/
theorem abs_cbrt_sub_le (a b : ℝ) : |cbrt a - cbrt b| ≤ cbrt (4 * |a - b|) := by
  have h1 : cbrt a - cbrt b ≤ cbrt (4 * max (a - b) 0) :=
    sub_le_cbrt (by rw [cbrt_pow, cbrt_pow])
  have h2 : cbrt b - cbrt a ≤ cbrt (4 * max (b - a) 0) :=
    sub_le_cbrt (by rw [cbrt_pow, cbrt_pow])
  have m1 : cbrt (4 * max (a - b) 0) ≤ cbrt (4 * |a - b|) :=
    cbrt_strictMono.monotone (by
      have := max_le (le_abs_self (a - b)) (abs_nonneg (a - b))
      linarith)
  have m2 : cbrt (4 * max (b - a) 0) ≤ cbrt (4 * |a - b|) :=
    cbrt_strictMono.monotone (by
      have h0 : b - a ≤ |a - b| := by rw [abs_sub_comm]; exact le_abs_self _
      have := max_le h0 (abs_nonneg (a - b))
      linarith)
  rw [abs_le]
  constructor <;> linarith

/-! ### Freezing a known variable inside a conditional expectation -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), p. 633 (tool): **under informational closure, a conditional expectation in
state `ω` depends only on the values on the information cell of `ω`** (for bounded
differences): the indicator of the cell is known, so `E_t` puts all its weight there. -/
theorem E_eq_of_eqOn_cell (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {t : ℕ} {f g : Ω → ℝ}
    {ω : Ω} {M : ℝ} (hM : ∀ ω', |f ω' - g ω'| ≤ M)
    (hfg : ∀ ω', LocalIFTStochastic.Ops.Indist 𝔼 t ω ω' → f ω' = g ω') :
    𝔼.E t f ω = 𝔼.E t g ω := by
  classical
  set C : Ω → ℝ := fun ω' => if LocalIFTStochastic.Ops.Indist 𝔼 t ω ω' then 1 else 0 with hC
  have hCk : 𝔼.E t C = C := by
    refine hcl t C fun ω₁ ω₂ h12 => ?_
    have e : LocalIFTStochastic.Ops.Indist 𝔼 t ω ω₁ ↔ LocalIFTStochastic.Ops.Indist 𝔼 t ω ω₂ :=
      ⟨fun h z => (h z).trans (h12 z), fun h z => (h z).trans (h12 z).symm⟩
    simp only [hC, e]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM ω)
  have hb : ∀ ω', |f ω' - g ω'| ≤ M * (1 - C ω') := by
    intro ω'
    by_cases h : LocalIFTStochastic.Ops.Indist 𝔼 t ω ω'
    · simp only [hC, h, ↓reduceIte, sub_self, mul_zero, hfg ω' h, abs_nonpos_iff]
    · simp only [hC, h, ↓reduceIte, sub_zero, mul_one]
      exact hM ω'
  set U : Ω → ℝ := M • ((fun _ => (1 : ℝ)) - C) with hU
  have hEU : 𝔼.E t U ω = 0 := by
    rw [hU, map_smul, map_sub, 𝔼.const, hCk]
    simp [hC, show LocalIFTStochastic.Ops.Indist 𝔼 t ω ω from fun _ => rfl]
  have hup : f - g ≤ U := fun ω' => by
    have := (abs_le.mp (hb ω')).2
    simpa [hU] using this
  have hlo : -U ≤ f - g := fun ω' => by
    have := (abs_le.mp (hb ω')).1
    simp only [hU, Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linarith
  have h1 := 𝔼.mono t hup ω
  have h2 := 𝔼.mono t hlo ω
  rw [map_sub] at h1 h2
  rw [map_neg] at h2
  simp only [Pi.sub_apply, Pi.neg_apply, hEU, neg_zero] at h1 h2
  linarith

/-! ### A uniform-limit engine for backward maps -/

/-- Woodford (2003), App. A.3, p. 634 (construction): iterating a backward map `T_t` from the
horizon `t + k` with terminal value `0`. -/
noncomputable def iterB (T : ℕ → (Ω → ℝ) → (Ω → ℝ)) : ℕ → ℕ → Ω → ℝ
  | 0, _ => fun _ => 0
  | k + 1, t => T t (iterB T k (t + 1))

/-- Woodford (2003), App. A.3, p. 634: **the backward iterates of a bounded weak contraction
converge uniformly**: if `T_t` maps the `R`-ball to itself and
`|T y − T y'| + κ|T y − T y'|³ ≤ sup|y − y'|` there, the iterates converge, uniformly in the
date and the state, to a process bounded by `R`. -/
theorem exists_limit_backward [Nonempty Ω] {T : ℕ → (Ω → ℝ) → (Ω → ℝ)} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 ≤ R)
    (hTb : ∀ t y, (∀ ω, |y ω| ≤ R) → ∀ ω, |T t y ω| ≤ R)
    (hTc : ∀ t y y' D, (∀ ω, |y ω| ≤ R) → (∀ ω, |y' ω| ≤ R) → (∀ ω, |y ω - y' ω| ≤ D) →
      ∀ ω, |T t y ω - T t y' ω| + κ * |T t y ω - T t y' ω| ^ 3 ≤ D) :
    ∃ i : ℕ → Ω → ℝ, ∃ d : ℕ → ℝ, Tendsto d atTop (𝓝 0) ∧ (∀ t ω, |i t ω| ≤ R) ∧
      ∀ k t ω, |iterB T k t ω - i t ω| ≤ d k := by
  have hb : ∀ k t ω, |iterB T k t ω| ≤ R := by
    intro k
    induction k with
    | zero => intro t ω; change |(0 : ℝ)| ≤ R; simpa using hR
    | succ k ih => exact fun t => hTb t _ (ih (t + 1))
  set d : ℕ → ℝ := fun k => ⨆ p : ℕ × Ω × ℕ, |iterB T k p.1 p.2.1 - iterB T (k + p.2.2) p.1 p.2.1|
    with hd
  have hbdd : ∀ k, BddAbove (Set.range fun p : ℕ × Ω × ℕ =>
      |iterB T k p.1 p.2.1 - iterB T (k + p.2.2) p.1 p.2.1|) := fun k =>
    ⟨2 * R, by
      rintro _ ⟨p, rfl⟩
      exact (abs_sub _ _).trans (by linarith [hb k p.1 p.2.1, hb (k + p.2.2) p.1 p.2.1])⟩
  have hle : ∀ k t ω m, |iterB T k t ω - iterB T (k + m) t ω| ≤ d k :=
    fun k t ω m => le_ciSup (hbdd k) (t, ω, m)
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  have hd0 : ∀ k, 0 ≤ d k := fun k => (abs_nonneg _).trans (hle k 0 ω₀ 0)
  set Φ : ℝ → ℝ := fun x => x + κ * x ^ 3 with hΦ
  have hΦm : Monotone Φ := phi_mono hκ.le
  have hΦc : Continuous Φ := by fun_prop
  have hstep : ∀ k, Φ (d (k + 1)) ≤ d k := by
    intro k
    rw [hd]
    dsimp only
    rw [hΦm.map_ciSup_of_continuousAt hΦc.continuousAt (hbdd (k + 1))]
    refine ciSup_le fun p => ?_
    obtain ⟨t, ω, m⟩ := p
    have h := hTc t (iterB T k (t + 1)) (iterB T (k + m) (t + 1)) (d k) (hb k (t + 1))
      (hb (k + m) (t + 1)) (fun ω' => hle k (t + 1) ω' m) ω
    change Φ |iterB T (k + 1) t ω - iterB T (k + 1 + m) t ω| ≤ _
    rw [show k + 1 + m = k + m + 1 by omega]
    exact h
  have hanti : Antitone d := antitone_nat_of_succ_le fun k => by
    have := hstep k
    have : 0 ≤ κ * d (k + 1) ^ 3 := mul_nonneg hκ.le (pow_nonneg (hd0 _) 3)
    simp only [hΦ] at *
    linarith
  have hbb : BddBelow (Set.range d) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hd0 k⟩
  set L := ⨅ k, d k with hL
  have hL0 : 0 ≤ L := le_ciInf hd0
  have hΦL : Φ L ≤ L := le_ciInf fun k => (hΦm (ciInf_le hbb (k + 1))).trans (hstep k)
  have hLz : L = 0 := by
    simp only [hΦ] at hΦL
    rcases hL0.lt_or_eq with h | h
    · linarith [mul_pos hκ (pow_pos h 3)]
    · exact h.symm
  have hdt : Tendsto d atTop (𝓝 0) := by
    rw [← hLz]
    exact tendsto_atTop_ciInf hanti hbb
  have hcs : ∀ t ω, CauchySeq fun k => iterB T k t ω := fun t ω =>
    cauchySeq_of_le_tendsto_0 (fun N => 2 * d N) (fun n m N hn hm => by
      rw [Real.dist_eq]
      have h1 := hle N t ω (n - N)
      have h2 := hle N t ω (m - N)
      rw [show N + (n - N) = n by omega] at h1
      rw [show N + (m - N) = m by omega] at h2
      refine (abs_sub_le _ (iterB T N t ω) _).trans ?_
      rw [abs_sub_comm (iterB T n t ω)]
      linarith) (by simpa using hdt.const_mul 2)
  choose lim hlim using fun t ω => cauchySeq_tendsto_of_complete (hcs t ω)
  refine ⟨lim, d, hdt, fun t ω => ?_, fun k t ω => ?_⟩
  · exact le_of_tendsto' (hlim t ω).abs fun k => hb k t ω
  · have ht : Tendsto (fun m => |iterB T k t ω - iterB T (m + k) t ω|) atTop
        (𝓝 |iterB T k t ω - lim t ω|) :=
      (tendsto_const_nhds.sub ((hlim t ω).comp (tendsto_add_atTop_nat k))).abs
    refine le_of_tendsto' ht fun m => ?_
    have := hle k t ω m
    rwa [add_comm k m] at this

/-! ### The backward map of the cubic rule -/

/-- Woodford (2003), Prop. 2.8, p. 96 (construction): the residual of the Fisher equation at
date `t` in state `ω` when `î_t = s` and `î_{t+1} = y`:
`E_t ∛(σ(y − ρ s − E_{t+1}ν_{t+1}))(ω) − s + E_t r̂_t(ω)`. -/
noncomputable def hres (ρ σ : ℝ) (nt rt : ℕ → Ω → ℝ) (t : ℕ) (y : Ω → ℝ) (ω : Ω) (s : ℝ) :
    ℝ :=
  𝔼.E t (fun ω' => cbrt (σ * (y ω' - ρ * s - nt (t + 1) ω'))) ω - s + rt t ω

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): the residual decreases at least at rate one. -/
theorem hres_anti {ρ σ : ℝ} (hτ : 1 ≤ σ * ρ) (nt rt : ℕ → Ω → ℝ) (t : ℕ) (y : Ω → ℝ) (ω : Ω)
    {s s' : ℝ} (h : s ≤ s') : hres 𝔼 ρ σ nt rt t y ω s' + (s' - s) ≤ hres 𝔼 ρ σ nt rt t y ω s := by
  have hm : (fun ω' => cbrt (σ * (y ω' - ρ * s' - nt (t + 1) ω'))) ≤
      fun ω' => cbrt (σ * (y ω' - ρ * s - nt (t + 1) ω')) := fun ω' =>
    cbrt_strictMono.monotone (by
      have : σ * ρ * s ≤ σ * ρ * s' := mul_le_mul_of_nonneg_left h (by linarith)
      nlinarith [this])
  have := 𝔼.mono t hm ω
  simp only [hres]
  linarith

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): `|h(s) − h(s')| ≤ ∛(4σρ|s − s'|) + |s − s'|`. -/
theorem hres_lip {ρ σ : ℝ} (hτ : 1 ≤ σ * ρ) (nt rt : ℕ → Ω → ℝ) (t : ℕ) (y : Ω → ℝ) (ω : Ω)
    (s s' : ℝ) : |hres 𝔼 ρ σ nt rt t y ω s - hres 𝔼 ρ σ nt rt t y ω s'| ≤
      cbrt (4 * (σ * ρ * |s - s'|)) + |s - s'| := by
  have hpt : ∀ ω', |(fun ω' => cbrt (σ * (y ω' - ρ * s - nt (t + 1) ω'))) ω' -
      (fun ω' => cbrt (σ * (y ω' - ρ * s' - nt (t + 1) ω'))) ω'| ≤
        cbrt (4 * (σ * ρ * |s - s'|)) := fun ω' => by
    refine (abs_cbrt_sub_le _ _).trans (cbrt_strictMono.monotone ?_)
    have e : σ * (y ω' - ρ * s - nt (t + 1) ω') - σ * (y ω' - ρ * s' - nt (t + 1) ω') =
        σ * ρ * (s' - s) := by ring
    rw [e, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < σ * ρ), abs_sub_comm]
  have h1 : |𝔼.E t ((fun ω' => cbrt (σ * (y ω' - ρ * s - nt (t + 1) ω'))) -
      (fun ω' => cbrt (σ * (y ω' - ρ * s' - nt (t + 1) ω')))) ω| ≤
        cbrt (4 * (σ * ρ * |s - s'|)) := 𝔼.abs_E_le hpt t ω
  rw [map_sub] at h1
  simp only [Pi.sub_apply] at h1
  simp only [hres]
  have e : 𝔼.E t (fun ω' => cbrt (σ * (y ω' - ρ * s - nt (t + 1) ω'))) ω - s + rt t ω -
      (𝔼.E t (fun ω' => cbrt (σ * (y ω' - ρ * s' - nt (t + 1) ω'))) ω - s' + rt t ω) =
      (𝔼.E t (fun ω' => cbrt (σ * (y ω' - ρ * s - nt (t + 1) ω'))) ω -
        𝔼.E t (fun ω' => cbrt (σ * (y ω' - ρ * s' - nt (t + 1) ω'))) ω) - (s - s') := by ring
  rw [e]
  exact (abs_sub _ _).trans (add_le_add h1 le_rfl)

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): the residual is continuous in `s`. -/
theorem hres_continuous {ρ σ : ℝ} (hτ : 1 ≤ σ * ρ) (nt rt : ℕ → Ω → ℝ) (t : ℕ) (y : Ω → ℝ)
    (ω : Ω) : Continuous (hres 𝔼 ρ σ nt rt t y ω) := by
  rw [Metric.continuous_iff]
  intro s ε hε
  have hτ0 : 0 < σ * ρ := by linarith
  refine ⟨min (ε / 2) ((ε / 2) ^ 3 / (4 * (σ * ρ))), lt_min (by positivity) (by positivity),
    fun s' hs' => ?_⟩
  rw [Real.dist_eq] at hs' ⊢
  have h1 : |s' - s| < ε / 2 := lt_of_lt_of_le hs' (min_le_left _ _)
  have h2 : 4 * (σ * ρ * |s' - s|) ≤ (ε / 2) ^ 3 := by
    have := (lt_of_lt_of_le hs' (min_le_right _ _)).le
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have h3 := cbrt_le_of_le_pow h2
  have := hres_lip 𝔼 hτ nt rt t y ω s' s
  linarith

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): for a bounded `î_{t+1}` the residual has a root
(it is continuous, decreasing, positive at `−(K + η)` and negative at `K + η`). -/
theorem hres_root {ρ σ : ℝ} (hσ : σ * σ = 1) (hτ : 1 ≤ σ * ρ) {nt rt : ℕ → Ω → ℝ} {η : ℝ}
    (hn : ∀ t ω, |nt t ω| ≤ η) (hr : ∀ t ω, |rt t ω| ≤ η) (t : ℕ) {y : Ω → ℝ} {Y : ℝ}
    (hY : ∀ ω, |y ω| ≤ Y) (ω : Ω) : ∃ s, hres 𝔼 ρ σ nt rt t y ω s = 0 := by
  have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  obtain ⟨ω₀⟩ : Nonempty Ω := ⟨ω⟩
  have hY0 : 0 ≤ Y := (abs_nonneg _).trans (hY ω)
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hn 0 ω)
  set K := max 1 (Y + η) with hK
  have hcK : cbrt (Y + η) ≤ K := (le_abs_self _).trans
    ((abs_le_of_pow_three (cbrt_pow _)).trans (by rw [abs_of_nonneg (by linarith)]))
  have hσy : ∀ ω', |σ * y ω'| ≤ Y := fun ω' => by rw [abs_mul, hs, one_mul]; exact hY ω'
  have hσn : ∀ ω', |σ * nt (t + 1) ω'| ≤ η := fun ω' => by
    rw [abs_mul, hs, one_mul]; exact hn _ ω'
  have hτ0 : 0 ≤ σ * ρ := by linarith
  have hKη : 0 ≤ K + η := by have := le_max_left 1 (Y + η); linarith
  have hup : hres 𝔼 ρ σ nt rt t y ω (K + η) ≤ 0 := by
    have hm : (fun ω' => cbrt (σ * (y ω' - ρ * (K + η) - nt (t + 1) ω'))) ≤ fun _ => K :=
      fun ω' => by
        refine (cbrt_strictMono.monotone ?_).trans hcK
        have := (abs_le.mp (hσy ω')).2
        have := (abs_le.mp (hσn ω')).1
        nlinarith [mul_nonneg hτ0 hKη]
    have := 𝔼.mono t hm ω
    rw [𝔼.const] at this
    have := (abs_le.mp (hr t ω)).2
    simp only [hres]
    linarith
  have hlo : 0 ≤ hres 𝔼 ρ σ nt rt t y ω (-(K + η)) := by
    have hm : (fun _ => -K) ≤ fun ω' => cbrt (σ * (y ω' - ρ * (-(K + η)) - nt (t + 1) ω')) :=
      fun ω' => by
        refine le_trans ?_ (cbrt_strictMono.monotone (b := σ * (y ω' - ρ * (-(K + η)) -
          nt (t + 1) ω')) (a := -(Y + η)) ?_)
        · rw [cbrt_neg]; linarith
        · have := (abs_le.mp (hσy ω')).1
          have := (abs_le.mp (hσn ω')).2
          nlinarith [mul_nonneg hτ0 hKη]
    have := 𝔼.mono t hm ω
    rw [𝔼.const] at this
    have := (abs_le.mp (hr t ω)).1
    simp only [hres]
    linarith
  obtain ⟨s, -, hs0⟩ := intermediate_value_Icc' (by linarith : -(K + η) ≤ K + η)
    (hres_continuous 𝔼 hτ nt rt t y ω).continuousOn ⟨hup, hlo⟩
  exact ⟨s, hs0⟩

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): the residual has at most one root. -/
theorem hres_inj {ρ σ : ℝ} (hτ : 1 ≤ σ * ρ) (nt rt : ℕ → Ω → ℝ) (t : ℕ) (y : Ω → ℝ) (ω : Ω)
    {s s' : ℝ} (h : hres 𝔼 ρ σ nt rt t y ω s = 0) (h' : hres 𝔼 ρ σ nt rt t y ω s' = 0) :
    s = s' := by
  rcases le_total s s' with hle | hle
  · have := hres_anti 𝔼 hτ nt rt t y ω hle
    linarith
  · have := hres_anti 𝔼 hτ nt rt t y ω hle
    linarith

/-- Woodford (2003), Prop. 2.8, p. 96 (construction): **the backward map**: `î_t` solving the
Fisher equation given `î_{t+1} = y`, state by state. -/
noncomputable def Tcube (ρ σ : ℝ) (nt rt : ℕ → Ω → ℝ) (t : ℕ) (y : Ω → ℝ) (ω : Ω) : ℝ :=
  by classical exact if h : ∃ s, hres 𝔼 ρ σ nt rt t y ω s = 0 then Classical.choose h else 0

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): `Tcube` is a root when one exists. -/
theorem Tcube_spec {ρ σ : ℝ} (nt rt : ℕ → Ω → ℝ) (t : ℕ) (y : Ω → ℝ) (ω : Ω)
    (h : ∃ s, hres 𝔼 ρ σ nt rt t y ω s = 0) :
    hres 𝔼 ρ σ nt rt t y ω (Tcube 𝔼 ρ σ nt rt t y ω) = 0 := by
  unfold Tcube
  split_ifs
  exact Classical.choose_spec h

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): `Tcube` is constant on information cells. -/
theorem Tcube_cell {ρ σ : ℝ} (hτ : 1 ≤ σ * ρ) (nt rt : ℕ → Ω → ℝ)
    (hrk : ∀ t, 𝔼.E t (rt t) = rt t) (t : ℕ) (y : Ω → ℝ)
    (hex : ∀ ω, ∃ s, hres 𝔼 ρ σ nt rt t y ω s = 0) {ω ω' : Ω}
    (hi : LocalIFTStochastic.Ops.Indist 𝔼 t ω ω') :
    Tcube 𝔼 ρ σ nt rt t y ω = Tcube 𝔼 ρ σ nt rt t y ω' := by
  have hsame : ∀ s, hres 𝔼 ρ σ nt rt t y ω s = hres 𝔼 ρ σ nt rt t y ω' s := fun s => by
    simp only [hres]
    rw [hi, LocalIFTStochastic.Ops.cellConst_of_known 𝔼 (hrk t) ω ω' hi]
  refine hres_inj 𝔼 hτ nt rt t y ω (Tcube_spec 𝔼 nt rt t y ω (hex ω)) ?_
  rw [hsame]
  exact Tcube_spec 𝔼 nt rt t y ω' (hex ω')

/-- Woodford (2003), Prop. 2.8, p. 96: **the backward map keeps `î` within `R`** when
`‖disturbances‖ ≤ R/2` and `≤ (R/2)³`. -/
theorem abs_Tcube_le {ρ σ : ℝ} (hσ : σ * σ = 1) (hτ : 1 ≤ σ * ρ) {nt rt : ℕ → Ω → ℝ} {η R : ℝ}
    (hn : ∀ t ω, |nt t ω| ≤ η) (hr : ∀ t ω, |rt t ω| ≤ η) (hη1 : η ≤ R / 2)
    (hη3 : η ≤ (R / 2) ^ 3) (t : ℕ) {y : Ω → ℝ} (hY : ∀ ω, |y ω| ≤ R) (ω : Ω) :
    |Tcube 𝔼 ρ σ nt rt t y ω| ≤ R := by
  have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hY ω)
  have hroot := Tcube_spec 𝔼 nt rt t y ω (hres_root 𝔼 hσ hτ hn hr t hY ω)
  set x := Tcube 𝔼 ρ σ nt rt t y ω with hx
  have hcη : cbrt η ≤ R / 2 := cbrt_le_of_le_pow hη3
  have hσy : ∀ ω', |σ * y ω'| ≤ R := fun ω' => by rw [abs_mul, hs, one_mul]; exact hY ω'
  have hσn : ∀ ω', |σ * nt (t + 1) ω'| ≤ η := fun ω' => by
    rw [abs_mul, hs, one_mul]; exact hn _ ω'
  simp only [hres] at hroot
  rw [abs_le]
  constructor
  · by_contra hc
    push Not at hc
    have hm : (fun _ => cbrt (-R - η - x)) ≤
        fun ω' => cbrt (σ * (y ω' - ρ * x - nt (t + 1) ω')) := fun ω' =>
      cbrt_strictMono.monotone (by
        have := (abs_le.mp (hσy ω')).1
        have := (abs_le.mp (hσn ω')).2
        have : σ * ρ * x ≤ x := by nlinarith
        nlinarith)
    have h1 := 𝔼.mono t hm ω
    rw [𝔼.const] at h1
    have h2 : cbrt (-η) < cbrt (-R - η - x) := cbrt_strictMono (by linarith)
    rw [cbrt_neg] at h2
    have := (abs_le.mp (hr t ω)).1
    linarith
  · by_contra hc
    push Not at hc
    have hm : (fun ω' => cbrt (σ * (y ω' - ρ * x - nt (t + 1) ω'))) ≤
        fun _ => cbrt (R + η - x) := fun ω' =>
      cbrt_strictMono.monotone (by
        have := (abs_le.mp (hσy ω')).2
        have := (abs_le.mp (hσn ω')).1
        have : x ≤ σ * ρ * x := by nlinarith
        nlinarith)
    have h1 := 𝔼.mono t hm ω
    rw [𝔼.const] at h1
    have h2 : cbrt (R + η - x) < cbrt η := cbrt_strictMono (by linarith)
    have := (abs_le.mp (hr t ω)).2
    linarith

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): one side of the contraction estimate. -/
theorem contract_aux {ρ σ : ℝ} (hσ : σ * σ = 1) (hτ : 1 ≤ σ * ρ) (nt rt : ℕ → Ω → ℝ) (t : ℕ)
    {y y' : Ω → ℝ} {D : ℝ} (hD : ∀ ω, |y ω - y' ω| ≤ D) (ω : Ω) {x x' : ℝ}
    (hx : hres 𝔼 ρ σ nt rt t y ω x = 0) (hx' : hres 𝔼 ρ σ nt rt t y' ω x' = 0)
    (hxx : x' ≤ x) : (x - x') + 1 / 4 * (x - x') ^ 3 ≤ D := by
  have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  set δ := x - x' with hδ
  have hδ0 : 0 ≤ δ := by linarith
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD ω)
  have hpt : (fun ω' => cbrt (σ * (y ω' - ρ * x - nt (t + 1) ω'))) -
      (fun ω' => cbrt (σ * (y' ω' - ρ * x' - nt (t + 1) ω'))) ≤
        fun _ => cbrt (4 * max (D - δ) 0) := fun ω' => by
    simp only [Pi.sub_apply]
    refine (sub_le_cbrt (by rw [cbrt_pow, cbrt_pow])).trans (cbrt_strictMono.monotone ?_)
    have h1 : |σ * (y ω' - y' ω')| ≤ D := by rw [abs_mul, hs, one_mul]; exact hD ω'
    have h2 : δ ≤ σ * ρ * δ := by nlinarith
    have h3 : σ * (y ω' - ρ * x - nt (t + 1) ω') - σ * (y' ω' - ρ * x' - nt (t + 1) ω') ≤
        D - δ := by
      have := (abs_le.mp h1).2
      nlinarith
    have := max_le_max h3 (le_refl (0 : ℝ))
    linarith
  have hE := 𝔼.mono t hpt ω
  rw [map_sub, 𝔼.const] at hE
  simp only [Pi.sub_apply] at hE
  simp only [hres] at hx hx'
  have hδc : δ ≤ cbrt (4 * max (D - δ) 0) := by linarith
  have h3 := pow_le_of_le_cbrt hδ0 hδc
  by_cases hδD : δ ≤ D
  · rw [max_eq_left (by linarith)] at h3
    linarith
  · push Not at hδD
    rw [max_eq_right (by linarith)] at h3
    have : δ ^ 3 ≤ 0 := by linarith
    have : δ = 0 := by
      rcases hδ0.lt_or_eq with h | h
      · linarith [pow_pos h 3]
      · exact h.symm
    linarith

/-- Woodford (2003), Prop. 2.8, p. 96: **the backward map is a weak contraction**,
`|δ| + |δ|³/4 ≤ D` whenever the continuation values differ by at most `D`. -/
theorem Tcube_contract {ρ σ : ℝ} (hσ : σ * σ = 1) (hτ : 1 ≤ σ * ρ) {nt rt : ℕ → Ω → ℝ} {η : ℝ}
    (hn : ∀ t ω, |nt t ω| ≤ η) (hr : ∀ t ω, |rt t ω| ≤ η) (t : ℕ) {y y' : Ω → ℝ} {R D : ℝ}
    (hY : ∀ ω, |y ω| ≤ R) (hY' : ∀ ω, |y' ω| ≤ R) (hD : ∀ ω, |y ω - y' ω| ≤ D) (ω : Ω) :
    |Tcube 𝔼 ρ σ nt rt t y ω - Tcube 𝔼 ρ σ nt rt t y' ω| +
      1 / 4 * |Tcube 𝔼 ρ σ nt rt t y ω - Tcube 𝔼 ρ σ nt rt t y' ω| ^ 3 ≤ D := by
  have h1 := Tcube_spec 𝔼 nt rt t y ω (hres_root 𝔼 hσ hτ hn hr t hY ω)
  have h2 := Tcube_spec 𝔼 nt rt t y' ω (hres_root 𝔼 hσ hτ hn hr t hY' ω)
  rcases le_total (Tcube 𝔼 ρ σ nt rt t y' ω) (Tcube 𝔼 ρ σ nt rt t y ω) with h | h
  · rw [abs_of_nonneg (by linarith)]
    exact contract_aux 𝔼 hσ hτ nt rt t hD ω h1 h2 h
  · rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact contract_aux 𝔼 hσ hτ nt rt t (fun ω' => by rw [abs_sub_comm]; exact hD ω') ω h2 h1 h

/-- Woodford (2003), Prop. 2.8, p. 96: **the backward map solves the Fisher equation as a
function of the state** (`E_t ∛(σ(y − ρ x − E_{t+1}ν_{t+1})) = x − E_t r̂_t` for `x = Tcube y`),
using informational closure to freeze the known `x` inside `E_t`. -/
theorem rel_Tcube (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {ρ σ : ℝ} (hσ : σ * σ = 1)
    (hτ : 1 ≤ σ * ρ) {nt rt : ℕ → Ω → ℝ} {η R : ℝ} (hn : ∀ t ω, |nt t ω| ≤ η)
    (hr : ∀ t ω, |rt t ω| ≤ η) (hrk : ∀ t, 𝔼.E t (rt t) = rt t) (hη1 : η ≤ R / 2)
    (hη3 : η ≤ (R / 2) ^ 3) (t : ℕ) {y : Ω → ℝ} (hY : ∀ ω, |y ω| ≤ R) :
    𝔼.E t (fun ω' => cbrt (σ * (y ω' - ρ * Tcube 𝔼 ρ σ nt rt t y ω' - nt (t + 1) ω'))) =
      fun ω => Tcube 𝔼 ρ σ nt rt t y ω - rt t ω := by
  funext ω
  have hex : ∀ ω, ∃ s, hres 𝔼 ρ σ nt rt t y ω s = 0 := fun ω => hres_root 𝔼 hσ hτ hn hr t hY ω
  have hxb : ∀ ω, |Tcube 𝔼 ρ σ nt rt t y ω| ≤ R := abs_Tcube_le 𝔼 hσ hτ hn hr hη1 hη3 t hY
  have hroot := Tcube_spec 𝔼 nt rt t y ω (hex ω)
  simp only [hres] at hroot
  have hsub : 𝔼.E t (fun ω' => cbrt (σ * (y ω' - ρ * Tcube 𝔼 ρ σ nt rt t y ω' -
      nt (t + 1) ω'))) ω = 𝔼.E t (fun ω' => cbrt (σ * (y ω' - ρ * Tcube 𝔼 ρ σ nt rt t y ω -
        nt (t + 1) ω'))) ω := by
    refine E_eq_of_eqOn_cell 𝔼 hcl (M := max 1 (4 * (|ρ| * (2 * R)))) (fun ω' => ?_)
      (fun ω' hi => by rw [← Tcube_cell 𝔼 hτ nt rt hrk t y hex hi])
    refine (abs_cbrt_sub_le _ _).trans ((le_abs_self _).trans
      ((abs_le_of_pow_three (cbrt_pow _)).trans (max_le_max le_rfl ?_)))
    have e : σ * (y ω' - ρ * Tcube 𝔼 ρ σ nt rt t y ω' - nt (t + 1) ω') -
        σ * (y ω' - ρ * Tcube 𝔼 ρ σ nt rt t y ω - nt (t + 1) ω') =
        σ * (ρ * (Tcube 𝔼 ρ σ nt rt t y ω - Tcube 𝔼 ρ σ nt rt t y ω')) := by ring
    have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
    rw [e, abs_mul, abs_abs, abs_mul, hs, one_mul, abs_mul]
    have : |Tcube 𝔼 ρ σ nt rt t y ω - Tcube 𝔼 ρ σ nt rt t y ω'| ≤ 2 * R :=
      (abs_sub _ _).trans (by linarith [hxb ω, hxb ω'])
    have h4 : |(4 : ℝ)| = 4 := by norm_num
    rw [h4]
    nlinarith [abs_nonneg ρ]
  rw [hsub]
  linarith

/-! ### Existence and uniqueness under uncertainty -/

/-- **Existence and uniqueness on the boundary with small disturbances, `φ_π = 0`, under
uncertainty** (Woodford (2003), Prop. 2.8, p. 96; App. A.3, pp. 632–634): for every
informationally closed expectation system on a nonempty state space (perfect foresight, every
finite event tree), for the rule `ρ î_{−1} + σπ³` with `σ² = 1`, `σρ ≥ 1`, and for every initial
rate and every disturbance process with `‖e‖ ≤ R/2` and `‖e‖ ≤ (R/2)³`, there is **exactly one**
bounded adapted equilibrium; its interest rate stays within `R` (so within `2‖e‖^{1/3}` for small
shocks), and initial inflation is the cube root `π_0 = ∛(σ(î_0 − ρ î_{−1} − E_0 ν_0))`. -/
theorem exists_unique_cube [Nonempty Ω] (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼)
    {ρ σ R : ℝ} (hσ : σ * σ = 1) (hτ : 1 ≤ σ * ρ) (xm : Fin 2 → ℝ)
    (e : LocalIFTStochastic.BFun (ℕ × Ω) (Fin 2 → ℝ)) (he1 : ‖e‖ ≤ R / 2)
    (he3 : ‖e‖ ≤ (R / 2) ^ 3) :
    ∃ x : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert (ruleCubPi ρ σ)) (xm, e) x ∧
      (∀ t ω, |x (t, ω) 1| ≤ R) ∧
      (∀ ω, x (0, ω) 0 = cbrt (σ * (x (0, ω) 1 - ρ * xm 1 - 𝔼.E 0 (fun ω' => e (0, ω') 1) ω))) ∧
      ∀ y : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert (ruleCubPi ρ σ)) (xm, e) y → y = x := by
  have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  have habs : ∀ p j, |e p j| ≤ ‖e‖ := fun p j => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ j).trans (LocalIFTStochastic.norm_apply_le e p)
  have hR0 : 0 ≤ R := by linarith [norm_nonneg e]
  set η := ‖e‖ with hη
  set nt : ℕ → Ω → ℝ := fun t => 𝔼.E t (fun ω => e (t, ω) 1) with hnt
  set rt : ℕ → Ω → ℝ := fun t => 𝔼.E t (fun ω => e (t, ω) 0) with hrt
  have hn : ∀ t ω, |nt t ω| ≤ η := fun t ω => 𝔼.abs_E_le (fun ω' => habs _ 1) t ω
  have hr : ∀ t ω, |rt t ω| ≤ η := fun t ω => 𝔼.abs_E_le (fun ω' => habs _ 0) t ω
  have hnk : ∀ t, 𝔼.E t (nt t) = nt t := fun t => 𝔼.E_E_self t _
  have hrk : ∀ t, 𝔼.E t (rt t) = rt t := fun t => 𝔼.E_E_self t _
  set T := Tcube 𝔼 ρ σ nt rt with hT
  have hTb : ∀ t y, (∀ ω, |y ω| ≤ R) → ∀ ω, |T t y ω| ≤ R := fun t y hy =>
    abs_Tcube_le 𝔼 hσ hτ hn hr he1 he3 t hy
  have hTc : ∀ t y y' D, (∀ ω, |y ω| ≤ R) → (∀ ω, |y' ω| ≤ R) → (∀ ω, |y ω - y' ω| ≤ D) →
      ∀ ω, |T t y ω - T t y' ω| + 1 / 4 * |T t y ω - T t y' ω| ^ 3 ≤ D :=
    fun t y y' D hy hy' hD => Tcube_contract 𝔼 hσ hτ hn hr t hy hy' hD
  obtain ⟨i, d, hd, hib, hunif⟩ := exists_limit_backward (by norm_num : (0 : ℝ) < 1 / 4) hR0
    hTb hTc
  have hb : ∀ k t ω, |iterB T k t ω| ≤ R := by
    intro k
    induction k with
    | zero => intro t ω; change |(0 : ℝ)| ≤ R; simpa using hR0
    | succ k ih => exact fun t => hTb t _ (ih (t + 1))
  -- the iterates and the limit are known
  have hWk : ∀ k t, 𝔼.E t (iterB T k t) = iterB T k t := by
    intro k t
    cases k with
    | zero => exact 𝔼.const t 0
    | succ k =>
      exact hcl t _ fun ω ω' hi => Tcube_cell 𝔼 hτ nt rt hrk t _
        (fun ω => hres_root 𝔼 hσ hτ hn hr t (hb k (t + 1)) ω) hi
  have hik : ∀ t, 𝔼.E t (i t) = i t := by
    intro t
    funext ω
    have hbk : ∀ k, |𝔼.E t (i t) ω - i t ω| ≤ 2 * d k := by
      intro k
      have h1 : |𝔼.E t (i t - iterB T k t) ω| ≤ d k :=
        𝔼.abs_E_le (fun ω' => by
          simp only [Pi.sub_apply]
          rw [abs_sub_comm]
          exact hunif k t ω') t ω
      have e1 : 𝔼.E t (i t) ω - i t ω =
          𝔼.E t (i t - iterB T k t) ω + (iterB T k t ω - i t ω) := by
        rw [map_sub, hWk k t]
        simp only [Pi.sub_apply]
        ring
      rw [e1]
      exact (abs_add_le _ _).trans (by linarith [hunif k t ω])
    have h0 := ge_of_tendsto' (hd.const_mul 2) hbk
    rw [mul_zero] at h0
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)
  -- the Fisher equation in the limit
  have hrel : ∀ t, 𝔼.E t (fun ω' => cbrt (σ * (i (t + 1) ω' - ρ * i t ω' - nt (t + 1) ω'))) =
      fun ω => i t ω - rt t ω := by
    intro t
    funext ω
    set c := |𝔼.E t (fun ω' => cbrt (σ * (i (t + 1) ω' - ρ * i t ω' - nt (t + 1) ω'))) ω -
      (i t ω - rt t ω)| with hc
    have hck : ∀ k, c ≤ cbrt (4 * (d k + |ρ| * d (k + 1))) + d (k + 1) := by
      intro k
      have hR := rel_Tcube 𝔼 hcl hσ hτ hn hr hrk he1 he3 t (hb k (t + 1))
      have hRω := congrFun hR ω
      change 𝔼.E t (fun ω' => cbrt (σ * (iterB T k (t + 1) ω' - ρ * iterB T (k + 1) t ω' -
        nt (t + 1) ω'))) ω = iterB T (k + 1) t ω - rt t ω at hRω
      have hpt : ∀ ω', |(fun ω' => cbrt (σ * (i (t + 1) ω' - ρ * i t ω' - nt (t + 1) ω'))) ω' -
          (fun ω' => cbrt (σ * (iterB T k (t + 1) ω' - ρ * iterB T (k + 1) t ω' -
            nt (t + 1) ω'))) ω'| ≤ cbrt (4 * (d k + |ρ| * d (k + 1))) := fun ω' => by
        refine (abs_cbrt_sub_le _ _).trans (cbrt_strictMono.monotone ?_)
        have e2 : σ * (i (t + 1) ω' - ρ * i t ω' - nt (t + 1) ω') -
            σ * (iterB T k (t + 1) ω' - ρ * iterB T (k + 1) t ω' - nt (t + 1) ω') =
            σ * ((i (t + 1) ω' - iterB T k (t + 1) ω') - ρ * (i t ω' - iterB T (k + 1) t ω')) := by
          ring
        rw [e2, abs_mul, hs, one_mul]
        have h1 : |i (t + 1) ω' - iterB T k (t + 1) ω'| ≤ d k := by
          rw [abs_sub_comm]; exact hunif k (t + 1) ω'
        have h2 : |i t ω' - iterB T (k + 1) t ω'| ≤ d (k + 1) := by
          rw [abs_sub_comm]; exact hunif (k + 1) t ω'
        have h3 : |ρ * (i t ω' - iterB T (k + 1) t ω')| ≤ |ρ| * d (k + 1) := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg ρ)
        have := (abs_sub _ _).trans (add_le_add h1 h3)
        linarith
      have hE : |𝔼.E t ((fun ω' => cbrt (σ * (i (t + 1) ω' - ρ * i t ω' - nt (t + 1) ω'))) -
          (fun ω' => cbrt (σ * (iterB T k (t + 1) ω' - ρ * iterB T (k + 1) t ω' -
            nt (t + 1) ω')))) ω| ≤ cbrt (4 * (d k + |ρ| * d (k + 1))) := 𝔼.abs_E_le hpt t ω
      rw [map_sub, Pi.sub_apply, hRω] at hE
      have hu := hunif (k + 1) t ω
      rw [hc]
      calc _ = |(𝔼.E t (fun ω' => cbrt (σ * (i (t + 1) ω' - ρ * i t ω' - nt (t + 1) ω'))) ω -
            (iterB T (k + 1) t ω - rt t ω)) + (iterB T (k + 1) t ω - i t ω)| := by
              congr 1
              ring
        _ ≤ _ := (abs_add_le _ _).trans (add_le_add hE hu)
    have he : Tendsto (fun k => 4 * (d k + |ρ| * d (k + 1))) atTop (𝓝 0) := by
      simpa using ((hd.add ((hd.comp (tendsto_add_atTop_nat 1)).const_mul |ρ|)).const_mul 4)
    have hd1 : Tendsto (fun k => d (k + 1)) atTop (𝓝 0) := hd.comp (tendsto_add_atTop_nat 1)
    by_contra hne
    have hcpos : 0 < c := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨k, hk1, hk2⟩ :=
      ((he.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < (c / 3) ^ 3))).and
        (hd1.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < c / 3)))).exists
    have := hck k
    have := cbrt_le_of_le_pow hk1
    linarith
  -- inflation and the equilibrium
  set lagI : ℕ → Ω → ℝ := fun t ω => lagV (xm 1) (fun s => i s ω) t with hlagI
  set pz : ℕ → Ω → ℝ := fun t ω => cbrt (σ * (i t ω - ρ * lagI t ω - nt t ω)) with hpz
  have hlagb : ∀ t ω, |lagI t ω| ≤ R + |xm 1| := by
    intro t ω
    cases t with
    | zero => change |xm 1| ≤ _; linarith
    | succ t => change |i t ω| ≤ _; linarith [hib t ω, abs_nonneg (xm 1)]
  set Bp := max 1 (R + |ρ| * (R + |xm 1|) + η) with hBp
  have hpzb : ∀ t ω, |pz t ω| ≤ Bp := by
    intro t ω
    refine (abs_le_of_pow_three (cbrt_pow _)).trans (max_le_max le_rfl ?_)
    rw [abs_mul, hs, one_mul]
    refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (hib t ω) ?_))
      (hn t ω))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hlagb t ω) (abs_nonneg ρ)
  set x : SProcV (Fin 2) Ω := LocalIFTStochastic.mkB (fun p => ![pz p.1 p.2, i p.1 p.2])
    ⟨max Bp R, fun p => (pi_norm_le_iff_of_nonneg ((abs_nonneg _).trans
      ((hib p.1 p.2).trans (le_max_right _ _)))).mpr fun j => by
        rw [Real.norm_eq_abs]
        fin_cases j
        · exact (hpzb p.1 p.2).trans (le_max_left _ _)
        · exact (hib p.1 p.2).trans (le_max_right _ _)⟩ with hx
  have hlagk : ∀ t ω ω', LocalIFTStochastic.Ops.Indist 𝔼 t ω ω' → lagI t ω = lagI t ω' := by
    intro t ω ω' hi
    cases t with
    | zero => rfl
    | succ s =>
      have hk : 𝔼.E (s + 1) (i s) = i s := by
        conv_lhs => rw [← hik s]
        rw [𝔼.known (Nat.le_succ s), hik s]
      exact LocalIFTStochastic.Ops.cellConst_of_known 𝔼 hk ω ω' hi
  have hpzk : ∀ t, 𝔼.E t (pz t) = pz t := fun t => hcl t _ fun ω ω' hi => by
    simp only [hpz]
    rw [LocalIFTStochastic.Ops.cellConst_of_known 𝔼 (hik t) ω ω' hi, hlagk t ω ω' hi,
      LocalIFTStochastic.Ops.cellConst_of_known 𝔼 (hnk t) ω ω' hi]
  have hsol : SolvesSV 𝔼 (Finert (ruleCubPi ρ σ)) (xm, e) x := by
    refine ⟨fun t j => ?_, fun t j => ?_⟩
    · fin_cases j
      · exact hpzk t
      · exact hik t
    · fin_cases j
      · have hf : (fun ω => Finert (ruleCubPi ρ σ)
            (ptS (((xm, e) : ParS (Fin 2) (Fin 2 → ℝ) Ω), x) (t, ω)) 0) =
            i t - (fun ω' => cbrt (σ * (i (t + 1) ω' - ρ * i t ω' - nt (t + 1) ω'))) -
              fun ω => e (t, ω) 0 := rfl
        change 𝔼.E t (fun ω => Finert (ruleCubPi ρ σ)
          (ptS (((xm, e) : ParS (Fin 2) (Fin 2 → ℝ) Ω), x) (t, ω)) 0) = 0
        rw [hf, map_sub, map_sub, hik, hrel]
        funext ω
        simp only [Pi.sub_apply, Pi.zero_apply, hrt]
        ring
      · have hf : (fun ω => Finert (ruleCubPi ρ σ)
            (ptS (((xm, e) : ParS (Fin 2) (Fin 2 → ℝ) Ω), x) (t, ω)) 1) =
            nt t - fun ω => e (t, ω) 1 := by
          funext ω
          have hl : lagV xm (fun s => x (s, ω)) t 1 = lagI t ω := by cases t <;> rfl
          change i t ω - ruleCubPi ρ σ (pz t ω, lagV xm (fun s => x (s, ω)) t 1) - e (t, ω) 1 =
            nt t ω - e (t, ω) 1
          rw [hl]
          simp only [ruleCubPi, hpz]
          rw [cbrt_pow]
          linear_combination (-(i t ω - ρ * lagI t ω - nt t ω)) * hσ
        change 𝔼.E t (fun ω => Finert (ruleCubPi ρ σ)
          (ptS (((xm, e) : ParS (Fin 2) (Fin 2 → ℝ) Ω), x) (t, ω)) 1) = 0
        rw [hf, map_sub, hnk]
        exact sub_self _
  exact ⟨x, hsol, fun t ω => hib t ω, fun ω => rfl,
    fun y hy => unique_cube hcl (fun π i => rfl) hσ hτ hy hsol⟩

/-! ### The resonant shock: an explicit cube root -/

/-- Woodford (2003), Prop. 2.8, p. 96 (example): the explicit equilibrium path for `ρ = σ` and
`ν_t = δσᵗ`: `î_t = σᵗ ∛(−δ)`, `π_{t+1} = î_t`, `π_0 = ∛(σ(î_0 − σ î_{−1} − δ))`. -/
noncomputable def zRes (σ δ xm1 : ℝ) : ℕ → Fin 2 → ℝ
  | 0 => ![cbrt (σ * (cbrt (-δ) - σ * xm1 - δ)), cbrt (-δ)]
  | t + 1 => ![σ ^ t * cbrt (-δ), σ ^ (t + 1) * cbrt (-δ)]

/-- **The resonant shock under uncertainty: an explicit cube-root equilibrium** (Woodford (2003),
Prop. 2.8, p. 96; App. A.3, p. 634): for `ρ = σ` (`σ² = 1`, so `|ρ| = 1`, `φ_π = 0`) and the
policy shock `ν_t = δσᵗ`, under informational closure every bounded equilibrium has
`î_t = σᵗ ∛(−δ)`: the response to the shock is of order `|δ|^{1/3}`, not differentiable. -/
theorem resonant_cube_root_pi (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {σ : ℝ}
    (hσ : σ * σ = 1) {δ : ℝ} (xm : Fin 2 → ℝ) {x : SProcV (Fin 2) Ω}
    (hx : SolvesSV 𝔼 (Finert (ruleCubPi σ σ)) (xm, resShock δ σ hσ) x) :
    ∀ t ω, x (t, ω) 1 = σ ^ t * cbrt (-δ) := by
  have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  set c := cbrt (-δ) with hc
  have hc3 : c ^ 3 = -δ := cbrt_pow _
  have hpow : ∀ t, σ ^ t * σ ^ t = 1 := fun t => by rw [← mul_pow, hσ, one_pow]
  set B := max |cbrt (σ * (c - σ * xm 1 - δ))| |c| with hB
  have hzb : ∀ t, ‖zRes σ δ (xm 1) t‖ ≤ B := by
    intro t
    refine (pi_norm_le_iff_of_nonneg ((abs_nonneg c).trans (le_max_right _ _))).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    cases t with
    | zero =>
      fin_cases j
      · exact le_max_left _ _
      · exact le_max_right _ _
    | succ t =>
      fin_cases j
      · change |σ ^ t * c| ≤ B
        rw [abs_mul, abs_pow, hs, one_pow, one_mul]
        exact le_max_right _ _
      · change |σ ^ (t + 1) * c| ≤ B
        rw [abs_mul, abs_pow, hs, one_pow, one_mul]
        exact le_max_right _ _
  set z : SProcV (Fin 2) Ω := LocalIFTStochastic.mkB (fun p => zRes σ δ (xm 1) p.1)
    ⟨B, fun p => hzb p.1⟩ with hz
  have hlag : ∀ t, (zRes σ δ (xm 1) t) 1 = σ ^ t * c := by
    intro t
    cases t with
    | zero => change c = σ ^ 0 * c; ring
    | succ t => rfl
  have hval : ∀ t ω j, Finert (ruleCubPi σ σ)
      (ptS (((xm, resShock δ σ hσ) : ParS (Fin 2) (Fin 2 → ℝ) Ω), z) (t, ω)) j = 0 := by
    intro t ω j
    fin_cases j
    · change (zRes σ δ (xm 1) t) 1 - (zRes σ δ (xm 1) (t + 1)) 0 - 0 = 0
      rw [hlag]
      change σ ^ t * c - σ ^ t * c - 0 = 0
      ring
    · cases t with
      | zero =>
        change c - ruleCubPi σ σ (cbrt (σ * (c - σ * xm 1 - δ)), xm 1) - δ * σ ^ 0 = 0
        simp only [ruleCubPi]
        rw [cbrt_pow]
        linear_combination (-(c - σ * xm 1 - δ)) * hσ
      | succ t =>
        change σ ^ (t + 1) * c - ruleCubPi σ σ (σ ^ t * c, (zRes σ δ (xm 1) t) 1) -
          δ * σ ^ (t + 1) = 0
        rw [hlag]
        simp only [ruleCubPi]
        have e : (σ ^ t * c) ^ 3 = σ ^ t * (σ ^ t * σ ^ t) * c ^ 3 := by ring
        rw [e, hpow, hc3, pow_succ]
        ring
  have hzs : SolvesSV 𝔼 (Finert (ruleCubPi σ σ)) (xm, resShock δ σ hσ) z := by
    refine ⟨fun t j => ?_, fun t j => ?_⟩
    · change 𝔼.E t (fun _ => zRes σ δ (xm 1) t j) = fun _ => zRes σ δ (xm 1) t j
      exact 𝔼.const t _
    have : (fun ω => Finert (ruleCubPi σ σ)
        (ptS (((xm, resShock δ σ hσ) : ParS (Fin 2) (Fin 2 → ℝ) Ω), z) (t, ω)) j) =
        fun _ => 0 := funext fun ω => hval t ω j
    rw [this]
    exact 𝔼.const t 0
  have heq := unique_cube hcl (fun π i => rfl) hσ (by linarith) hx hzs
  intro t ω
  rw [heq]
  exact hlag t

end Woodford.PriceLevelDetermination.InertialBoundaryExistCube
