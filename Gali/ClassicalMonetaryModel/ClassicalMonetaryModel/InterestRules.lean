/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ClassicalMonetaryModel.Expectations
import ClassicalMonetaryModel.ExpectationsFiniteTree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Interest-rate rules and price-level determination in the classical model

Galí (2015), Chapter 2, §2.4.1–2.4.2, pp. 24–28. The real block of the classical
model (the natural real rate `r_t = ρ + r̂_t`, output `y_t`) is determined independently
of monetary policy (§2.3), so here it is taken as an exogenous bounded adapted process,
as the book does in §2.4. Every statement holds for an arbitrary `ExpectationSystem`, so
both under perfect foresight and under genuine uncertainty.

## Main results

* `Fisher`, `fisher_steadyState_iff`: the Fisherian equation (22), p. 24, and its
  steady state `i = ρ + π`, p. 25.
* §2.4.1, exogenous nominal rate `i_t = i + v_t`: `exo_equilibrium_iff` — an adapted
  inflation process is an equilibrium iff `π_t = π + v_{t−1} − r̂_{t−1} + ξ_t` for a
  martingale-difference sunspot `ξ` (p. 26). `exo_two_equilibria` (any expectation
  system, in particular perfect foresight, where the free variable is initial
  inflation: `perfectForesight_exo_pinned`) and `coin_exo_sunspot` (a genuine sunspot at
  date 1 in the coin-flip tree) exhibit two distinct bounded equilibria.
* §2.4.2, the rule `i_t = ρ + π + φ_π(π_t − π) + v_t`: `rule_fisher_iff_eq24` gives (24);
  `eq25_unique_bounded`: for `φ_π > 1` the forward series (25) is the unique bounded
  equilibrium; `inflation_ar1_closed_form`, `inflation_closed_form_book`: the AR(1)
  closed form on p. 27; `hasDerivAt_inflImpact`, `hasDerivAt_rateImpact`,
  `hasDerivAt_moneyImpact`: the monetary-shock derivatives on p. 27;
  `liquidity_effect_iff`: a liquidity effect iff `η ρ_v > 1` (given `φ_π > ρ_v`).
* (26) and fn. 7, p. 28: `path26_eq24`, `path26_bounded`: for `|φ_π| < 1` every bounded
  martingale-difference `ξ` gives a bounded equilibrium; `eq24_iff_path26`: every adapted
  equilibrium is of that form; `path26_injective`: distinct sunspots give distinct
  equilibria; `isMDS_fn7`: the fn. 7 combinations are martingale differences.
* The Taylor principle, p. 28: `taylor_principle` — for `φ_π ≥ 0`, (24) is determinate
  iff `φ_π > 1`. This includes the case `φ_π = 1`, which the book omits: then the
  equilibrium is never unique (`not_unique_of_le_one`), and it may fail to exist
  (`phi_one_no_bounded_solution`).
* Correction C2-3: `c2_3_forward_converges_not_unique` — for AR(1) drivers with
  `|ρ| < φ_π < 1` the forward series (25) converges (to `(r̂_t − v_t)/(φ_π − ρ)`) and
  solves (24), but it is not the unique bounded solution; `printed_divergence_false`:
  the printed claim "(25) does not converge for `φ_π < 1`" is false for every `φ_π > 0`.
-/

namespace Gali.ClassicalMonetaryModel.InterestRules

open ExpectationsFiniteTree

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Preliminaries -/

/-- Galí (2015), §2.4, p. 24 (information): a random variable known at date `s` is known at
every later date `t ≥ s`. -/
theorem E_of_known {s t : ℕ} {x : Ω → ℝ} (h : 𝔼.E s x = x) (hst : s ≤ t) :
    𝔼.E t x = x := by
  rw [← h, 𝔼.known hst]

/-- Galí (2015), §2.4, p. 24 (information): an adapted process is known at all later dates. -/
theorem E_of_adapted_le {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) {s t : ℕ} (hst : s ≤ t) :
    𝔼.E t (x s) = x s :=
  E_of_known 𝔼 (hx s) hst

/-- Galí (2015), (25) p. 27 and (28) p. 29: the forward series is adapted (it is a
date-`t` forecast). Proved here; the core module lacks it. -/
theorem forwardSeries_adapted {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) : 𝔼.Adapted (𝔼.forwardSeries a u) := by
  intro t
  funext ω
  have hb : ∀ k ω', |a ^ k * 𝔼.E t (u (t + k)) ω'| ≤ a ^ k * M := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω') (pow_nonneg ha0 k)
  change 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω') ω =
    ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω
  rw [𝔼.E_tsum ha0 ha1 hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (a ^ k • 𝔼.E t (u (t + k))) ω = _
  rw [map_smul, 𝔼.E_E_self, Pi.smul_apply, smul_eq_mul]

/-- Galí (2015), p. 27 (impact derivatives): an affine map `e ↦ α + β e` has derivative `β`. -/
theorem hasDerivAt_affine (α β x : ℝ) : HasDerivAt (fun e => α + β * e) β x := by
  simpa using HasDerivAt.const_add α (HasDerivAt.const_mul β (hasDerivAt_id x))

/-! ### The Fisherian equation (22) -/

/-- Galí (2015), eq. (22), p. 24: the Fisherian equation `i_t = E_t{π_{t+1}} + r_t`. -/
def Fisher (i infl r : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (infl (t + 1)) + r t

/-- Galí (2015), p. 25: in a steady state with `r = ρ`, constant `i` and `π` satisfy the
Fisherian equation (22) iff `i = ρ + π`. -/
theorem fisher_steadyState_iff [Nonempty Ω] (ibar πbar ρ : ℝ) :
    Fisher 𝔼 (fun _ _ => ibar) (fun _ _ => πbar) (fun _ _ => ρ) ↔ ibar = ρ + πbar := by
  constructor
  · intro h
    have := congrFun (h 0) (Classical.arbitrary Ω)
    simp only [𝔼.const, Pi.add_apply] at this
    linarith
  · intro h t
    funext ω
    simp only [𝔼.const, Pi.add_apply]
    linarith

/-- Galí (2015), p. 26: the real rate `r_t = ρ + r̂_t`, with `r̂_t` the deviation from the
steady-state value `ρ`. -/
def realRate (ρ : ℝ) (rhat : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => (fun _ => ρ) + rhat t

/-! ### §2.4.1 An exogenous path for the nominal interest rate -/

/-- Galí (2015), p. 26: a martingale-difference (sunspot) process: adapted, with
`E_{t−1}{ξ_t} = 0` for all `t ≥ 1` (written `E_t{ξ_{t+1}} = 0`). -/
def IsMDS (ξ : ℕ → Ω → ℝ) : Prop := 𝔼.Adapted ξ ∧ ∀ t, 𝔼.E t (ξ (t + 1)) = 0

/-- Galí (2015), p. 26: the inflation path `π_t = π + v_{t−1} − r̂_{t−1} + ξ_t` under the
exogenous rate `i_t = i + v_t`; at date 0 (no date −1) it is `π_0 = π + ξ_0`. -/
def exoPath (πbar : ℝ) (v rhat ξ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => (fun _ : Ω => πbar) + ξ 0
  | t + 1 => (fun _ : Ω => πbar) + v t - rhat t + ξ (t + 1)

/-- Galí (2015), p. 26: the sunspot implicit in an inflation process,
`ξ_0 = π_0 − π` and `ξ_{t+1} = π_{t+1} − E_t{π_{t+1}}`. -/
def innov (πbar : ℝ) (infl : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => infl 0 - fun _ : Ω => πbar
  | t + 1 => infl (t + 1) - 𝔼.E t (infl (t + 1))

/-- Galí (2015), p. 26: the sunspot implicit in an adapted inflation process is a
martingale difference. -/
theorem innov_isMDS {πbar : ℝ} {infl : ℕ → Ω → ℝ} (h : 𝔼.Adapted infl) :
    IsMDS 𝔼 (innov 𝔼 πbar infl) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · cases t with
    | zero => simp only [innov, map_sub, h 0, 𝔼.const]
    | succ t => simp only [innov, map_sub, h (t + 1), 𝔼.known (Nat.le_succ t)]
  · simp only [innov, map_sub, 𝔼.E_E_self, sub_self]

/-- Galí (2015), p. 26 (sufficiency): for every martingale-difference `ξ`, the path
`π_t = π + v_{t−1} − r̂_{t−1} + ξ_t` satisfies the Fisherian equation (22) under the rule
`i_t = ρ + π + v_t`. -/
theorem exoPath_fisher {ρ πbar : ℝ} {v rhat ξ : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v)
    (hr : 𝔼.Adapted rhat) (hξ : IsMDS 𝔼 ξ) :
    Fisher 𝔼 (fun t => (fun _ => ρ + πbar) + v t) (exoPath πbar v rhat ξ)
      (realRate ρ rhat) := by
  intro t
  simp only [exoPath, realRate, map_add, map_sub, 𝔼.const, hv t, hr t, hξ.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
  ring

/-- Galí (2015), §2.4.1, p. 26 (**indeterminacy**, necessity and sufficiency): under the
exogenous rate `i_t = i + v_t` with `i = ρ + π`, an adapted inflation process is an
equilibrium iff `π_t = π + v_{t−1} − r̂_{t−1} + ξ_t` for some martingale-difference `ξ`. -/
theorem exo_equilibrium_iff {ρ πbar : ℝ} {v rhat infl : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v)
    (hr : 𝔼.Adapted rhat) (hinfl : 𝔼.Adapted infl) :
    Fisher 𝔼 (fun t => (fun _ => ρ + πbar) + v t) infl (realRate ρ rhat) ↔
      ∃ ξ, IsMDS 𝔼 ξ ∧ infl = exoPath πbar v rhat ξ := by
  constructor
  · intro hF
    refine ⟨innov 𝔼 πbar infl, innov_isMDS 𝔼 hinfl, ?_⟩
    funext t ω
    cases t with
    | zero => simp [exoPath, innov]
    | succ t =>
      have h := congrFun (hF t) ω
      simp only [realRate, Pi.add_apply] at h
      simp only [exoPath, innov, Pi.add_apply, Pi.sub_apply]
      linarith
  · rintro ⟨ξ, hξ, rfl⟩
    exact exoPath_fisher 𝔼 hv hr hξ

/-- Galí (2015), p. 26: the equivalent price-level form
`p_t = π + p_{t−1} + v_{t−1} − r̂_{t−1} + ξ_t`, given `p_t = p_{t−1} + π_t`. -/
theorem price_exoPath {πbar : ℝ} {v rhat ξ p : ℕ → Ω → ℝ}
    (hp : ∀ t, p (t + 1) = p t + exoPath πbar v rhat ξ (t + 1)) (t : ℕ) :
    p (t + 1) = (fun _ => πbar) + p t + v t - rhat t + ξ (t + 1) := by
  rw [hp t]
  funext ω
  simp only [exoPath, Pi.add_apply, Pi.sub_apply]
  ring

/-- Galí (2015), p. 26: the inflation path is bounded when `v`, `r̂` and `ξ` are. -/
theorem exoPath_bounded {πbar : ℝ} {v rhat ξ : ℕ → Ω → ℝ} (hv : BoundedProc v)
    (hr : BoundedProc rhat) (hξ : BoundedProc ξ) : BoundedProc (exoPath πbar v rhat ξ) := by
  obtain ⟨Mv, hMv⟩ := hv
  obtain ⟨Mr, hMr⟩ := hr
  obtain ⟨Mξ, hMξ⟩ := hξ
  refine ⟨|πbar| + Mv + Mr + Mξ, fun t ω => ?_⟩
  have hv0 : 0 ≤ Mv := (abs_nonneg _).trans (hMv 0 ω)
  have hr0 : 0 ≤ Mr := (abs_nonneg _).trans (hMr 0 ω)
  have hp1 := le_abs_self πbar
  have hp2 := neg_abs_le πbar
  cases t with
  | zero =>
    simp only [exoPath, Pi.add_apply]
    have h3 := abs_le.mp (hMξ 0 ω)
    rw [abs_le]
    constructor <;> linarith
  | succ t =>
    simp only [exoPath, Pi.add_apply, Pi.sub_apply]
    have h1 := abs_le.mp (hMv t ω)
    have h2 := abs_le.mp (hMr t ω)
    have h3 := abs_le.mp (hMξ (t + 1) ω)
    rw [abs_le]
    constructor <;> linarith

/-- Galí (2015), p. 26: the inflation path is adapted when `v`, `r̂` and `ξ` are. -/
theorem exoPath_adapted {πbar : ℝ} {v rhat ξ : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v)
    (hr : 𝔼.Adapted rhat) (hξ : 𝔼.Adapted ξ) : 𝔼.Adapted (exoPath πbar v rhat ξ) := by
  intro t
  cases t with
  | zero => simp only [exoPath, map_add, 𝔼.const, hξ 0]
  | succ t =>
    simp only [exoPath, map_add, map_sub, 𝔼.const, hξ (t + 1),
      E_of_adapted_le 𝔼 hv (Nat.le_succ t), E_of_adapted_le 𝔼 hr (Nat.le_succ t)]

/-- Galí (2015), p. 26: the zero process is a martingale difference. -/
theorem zero_isMDS : IsMDS 𝔼 0 :=
  ⟨fun t => by simp, fun t => by simp⟩

/-- Galí (2015), p. 26: a deterministic sunspot that moves only date-0 inflation. -/
def dateZeroShock : ℕ → Ω → ℝ := fun t _ => if t = 0 then 1 else 0

/-- Galí (2015), p. 26: the date-0 sunspot is a martingale difference (under any
expectation system, including perfect foresight). -/
theorem dateZeroShock_isMDS : IsMDS 𝔼 dateZeroShock := by
  refine ⟨fun t => 𝔼.const t _, fun t => ?_⟩
  change 𝔼.E t (fun _ => if t + 1 = 0 then (1 : ℝ) else 0) = 0
  rw [𝔼.const]
  funext ω
  simp

/-- Galí (2015), p. 26: the date-0 sunspot is bounded. -/
theorem dateZeroShock_bounded : BoundedProc (dateZeroShock (Ω := Ω)) :=
  ⟨1, fun t ω => by unfold dateZeroShock; split_ifs <;> simp⟩

/-- Galí (2015), §2.4.1, p. 26 (**two distinct bounded equilibria**, any expectation system,
in particular perfect foresight): under an exogenous nominal rate there are two different
bounded adapted equilibrium inflation processes. -/
theorem exo_two_equilibria [Nonempty Ω] {ρ πbar : ℝ} {v rhat : ℕ → Ω → ℝ}
    (hv : 𝔼.Adapted v) (hr : 𝔼.Adapted rhat) (hvb : BoundedProc v) (hrb : BoundedProc rhat) :
    ∃ π₁ π₂ : ℕ → Ω → ℝ,
      Fisher 𝔼 (fun t => (fun _ => ρ + πbar) + v t) π₁ (realRate ρ rhat) ∧
      Fisher 𝔼 (fun t => (fun _ => ρ + πbar) + v t) π₂ (realRate ρ rhat) ∧
      BoundedProc π₁ ∧ BoundedProc π₂ ∧ 𝔼.Adapted π₁ ∧ 𝔼.Adapted π₂ ∧ π₁ ≠ π₂ := by
  refine ⟨exoPath πbar v rhat 0, exoPath πbar v rhat dateZeroShock,
    exoPath_fisher 𝔼 hv hr (zero_isMDS 𝔼), exoPath_fisher 𝔼 hv hr (dateZeroShock_isMDS 𝔼),
    exoPath_bounded hvb hrb ⟨0, fun t ω => by simp⟩,
    exoPath_bounded hvb hrb dateZeroShock_bounded,
    exoPath_adapted 𝔼 hv hr (zero_isMDS 𝔼).1,
    exoPath_adapted 𝔼 hv hr (dateZeroShock_isMDS 𝔼).1, fun h => ?_⟩
  have := congrFun (congrFun h 0) (Classical.arbitrary Ω)
  simp [exoPath, dateZeroShock] at this

/-- Galí (2015), p. 26, under perfect foresight: a martingale difference vanishes from
date 1 on (there is no news to be surprised by). -/
theorem perfectForesight_isMDS {ξ : ℕ → Unit → ℝ} (h : IsMDS perfectForesight ξ) (t : ℕ) :
    ξ (t + 1) = 0 :=
  h.2 t

/-- Galí (2015), §2.4.1, p. 26, under perfect foresight: every equilibrium satisfies
`π_{t+1} = π + v_t − r̂_t`, so the only indeterminacy is initial inflation `π_0`
(equivalently the initial price level); `exo_two_equilibria` shows it is indeed free. -/
theorem perfectForesight_exo_pinned {ρ πbar : ℝ} {v rhat infl : ℕ → Unit → ℝ}
    (h : Fisher perfectForesight (fun t => (fun _ => ρ + πbar) + v t) infl (realRate ρ rhat))
    (t : ℕ) : infl (t + 1) = (fun _ => πbar) + v t - rhat t := by
  funext ω
  have := congrFun (h t) ω
  change ρ + πbar + v t ω = infl (t + 1) ω + (ρ + rhat t ω) at this
  simp only [Pi.add_apply, Pi.sub_apply]
  linarith

/-- Galí (2015), p. 26 (uncertainty example): the coin-flip innovation is a martingale
difference. -/
theorem coinShock_isMDS : IsMDS coinSystem coinShock := by
  refine ⟨fun t => ?_, coinShock_mean_zero⟩
  funext ω
  rw [coinSystem, FiniteTree.toExpectationSystem_E]
  exact coinTree.condE_of_const_on_cell fun _ h => coinShock_measurable t h

/-- Galí (2015), p. 26 (uncertainty example): the coin-flip innovation is bounded by 1. -/
theorem coinShock_bounded : BoundedProc coinShock :=
  ⟨1, fun t ω => by unfold coinShock; split_ifs <;> simp⟩

/-- Galí (2015), §2.4.1, p. 26 (**a genuine sunspot** in the coin-flip tree): under an
exogenous nominal rate, the fundamental path (`ξ = 0`) and the sunspot path (`ξ` = the coin
flip) are both bounded adapted equilibria; they agree at date 0 but differ at date 1 by a
coin flip unrelated to fundamentals. -/
theorem coin_exo_sunspot {ρ πbar : ℝ} {v rhat : ℕ → Bool × Bool → ℝ}
    (hv : coinSystem.Adapted v) (hr : coinSystem.Adapted rhat)
    (hvb : BoundedProc v) (hrb : BoundedProc rhat) :
    Fisher coinSystem (fun t => (fun _ => ρ + πbar) + v t) (exoPath πbar v rhat 0)
        (realRate ρ rhat) ∧
      Fisher coinSystem (fun t => (fun _ => ρ + πbar) + v t)
        (exoPath πbar v rhat coinShock) (realRate ρ rhat) ∧
      BoundedProc (exoPath πbar v rhat 0) ∧ BoundedProc (exoPath πbar v rhat coinShock) ∧
      coinSystem.Adapted (exoPath πbar v rhat 0) ∧
      coinSystem.Adapted (exoPath πbar v rhat coinShock) ∧
      exoPath πbar v rhat coinShock 0 = exoPath πbar v rhat 0 0 ∧
      exoPath πbar v rhat coinShock 1 (true, true) =
        exoPath πbar v rhat 0 1 (true, true) + 1 := by
  refine ⟨exoPath_fisher _ hv hr (zero_isMDS _), exoPath_fisher _ hv hr coinShock_isMDS,
    exoPath_bounded hvb hrb ⟨0, fun t ω => by simp⟩, exoPath_bounded hvb hrb coinShock_bounded,
    exoPath_adapted _ hv hr (zero_isMDS _).1, exoPath_adapted _ hv hr coinShock_isMDS.1,
    ?_, ?_⟩
  · funext ω
    simp [exoPath, coinShock]
  · simp [exoPath, coinShock]

/-! ### §2.4.2 A simple interest-rate rule -/

/-- Galí (2015), p. 26: the rule `i_t = ρ + π + φ_π(π_t − π) + v_t`. -/
def Rule (ρ πbar φ : ℝ) (i infl v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ + πbar) + φ • (infl t - fun _ => πbar) + v t

/-- Galí (2015), p. 27: the inflation gap `π̂_t = π_t − π`. -/
def gap (πbar : ℝ) (infl : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => infl t - fun _ => πbar

/-- Galí (2015), eq. (24), p. 27: `φ_π π̂_t = E_t{π̂_{t+1}} + r̂_t − v_t`. -/
def Eq24 (φ : ℝ) (z rhat v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, φ • z t = 𝔼.E t (z (t + 1)) + rhat t - v t

/-- Galí (2015), eq. (24), p. 27: given the rule, the Fisherian equation (22) holds iff the
inflation gap satisfies (24). -/
theorem rule_fisher_iff_eq24 {ρ πbar φ : ℝ} {i infl v rhat : ℕ → Ω → ℝ}
    (hR : Rule ρ πbar φ i infl v) :
    Fisher 𝔼 i infl (realRate ρ rhat) ↔ Eq24 𝔼 φ (gap πbar infl) rhat v := by
  constructor
  · intro hF t
    funext ω
    have h1 := congrFun (hF t) ω
    have h2 := congrFun (hR t) ω
    simp only [gap, realRate, map_sub, 𝔼.const, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at h1 h2 ⊢
    linarith
  · intro hE t
    funext ω
    have h1 := congrFun (hE t) ω
    have h2 := congrFun (hR t) ω
    simp only [gap, realRate, map_sub, 𝔼.const, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at h1 h2 ⊢
    linarith

/-- Galí (2015), eq. (25), p. 27: the forward solution
`π̂_t = ∑_{k ≥ 0} φ_π^{−(k+1)} E_t{r̂_{t+k} − v_{t+k}}`. -/
noncomputable def fwd25 (φ : ℝ) (rhat v : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, φ⁻¹ ^ (k + 1) * 𝔼.E t (rhat (t + k) - v (t + k)) ω

/-- Galí (2015), eq. (24), p. 27: the forcing `φ_π^{−1}(r̂_t − v_t)` of (24) written as
`π̂_t = φ_π^{−1} E_t{π̂_{t+1}} + φ_π^{−1}(r̂_t − v_t)`. -/
noncomputable def forcing25 (φ : ℝ) (rhat v : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => φ⁻¹ • (rhat t - v t)

/-- Galí (2015), eq. (25), p. 27: (25) is the core forward series with `a = 1/φ_π`. -/
theorem fwd25_eq_forwardSeries (φ : ℝ) (rhat v : ℕ → Ω → ℝ) :
    fwd25 𝔼 φ rhat v = 𝔼.forwardSeries φ⁻¹ (forcing25 φ rhat v) := by
  funext t ω
  simp only [fwd25, ExpectationSystem.forwardSeries, forcing25, map_smul, Pi.smul_apply,
    smul_eq_mul]
  refine tsum_congr fun k => ?_
  ring

/-- Galí (2015), eq. (24), p. 27: for `φ_π ≠ 0`, (24) is the forward equation
`π̂_t = φ_π^{−1} E_t{π̂_{t+1}} + φ_π^{−1}(r̂_t − v_t)`. -/
theorem eq24_iff_forward {φ : ℝ} (hφ : φ ≠ 0) {z rhat v : ℕ → Ω → ℝ} :
    Eq24 𝔼 φ z rhat v ↔
      ∀ t, z t = φ⁻¹ • 𝔼.E t (z (t + 1)) + forcing25 φ rhat v t := by
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    simp only [forcing25, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [← mul_add, ← add_sub_assoc, ← h1, ← mul_assoc, inv_mul_cancel₀ hφ, one_mul]
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    simp only [forcing25, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [h1, ← mul_add, ← mul_assoc, mul_inv_cancel₀ hφ, one_mul, add_sub_assoc]

/-- Galí (2015), eq. (24), p. 27: the forcing is bounded when `r̂` and `v` are. -/
theorem forcing25_bound {φ M₁ M₂ : ℝ} (hφ : 0 < φ) {rhat v : ℕ → Ω → ℝ}
    (hr : ∀ t ω, |rhat t ω| ≤ M₁) (hv : ∀ t ω, |v t ω| ≤ M₂) (t : ℕ) (ω : Ω) :
    |forcing25 φ rhat v t ω| ≤ φ⁻¹ * (M₁ + M₂) := by
  simp only [forcing25, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hφ)]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hr t ω) (hv t ω)))
    (inv_pos.mpr hφ).le

/-- Galí (2015), eq. (24), p. 27: the forcing is adapted when `r̂` and `v` are. -/
theorem forcing25_adapted {φ : ℝ} {rhat v : ℕ → Ω → ℝ} (hr : 𝔼.Adapted rhat)
    (hv : 𝔼.Adapted v) : 𝔼.Adapted (forcing25 φ rhat v) := by
  intro t
  simp only [forcing25, map_smul, map_sub, hr t, hv t]

/-- Galí (2015), eqs. (24)–(25), p. 27 (**determinacy for `φ_π > 1`**): with bounded adapted
`r̂` and `v`, the forward series (25) converges, is bounded and adapted, solves (24), and is
the unique bounded solution of (24). -/
theorem eq25_unique_bounded {φ : ℝ} (hφ : 1 < φ) {rhat v : ℕ → Ω → ℝ}
    (hrb : BoundedProc rhat) (hvb : BoundedProc v) (hra : 𝔼.Adapted rhat)
    (hva : 𝔼.Adapted v) :
    Eq24 𝔼 φ (fwd25 𝔼 φ rhat v) rhat v ∧ BoundedProc (fwd25 𝔼 φ rhat v) ∧
      𝔼.Adapted (fwd25 𝔼 φ rhat v) ∧
      ∀ z, Eq24 𝔼 φ z rhat v → BoundedProc z → z = fwd25 𝔼 φ rhat v := by
  obtain ⟨M₁, hM₁⟩ := hrb
  obtain ⟨M₂, hM₂⟩ := hvb
  have hφ0 : 0 < φ := one_pos.trans hφ
  have ha0 : 0 ≤ φ⁻¹ := (inv_pos.mpr hφ0).le
  have ha1 : φ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hφ
  have hu := forcing25_bound hφ0 hM₁ hM₂
  have hua := forcing25_adapted 𝔼 (φ := φ) hra hva
  rw [fwd25_eq_forwardSeries]
  refine ⟨(eq24_iff_forward 𝔼 hφ0.ne').mpr (𝔼.forwardSeries_solves ha0 ha1 hu hua),
    𝔼.forwardSeries_bounded ha0 ha1 hu, forwardSeries_adapted 𝔼 ha0 ha1 hu, fun z hz hzb => ?_⟩
  exact 𝔼.eq_forwardSeries ha0 ha1 hu hua ((eq24_iff_forward 𝔼 hφ0.ne').mp hz) hzb

/-- Galí (2015), p. 27 (AR(1) closed form): if `r̂_t = c_a a_t + c_z z_t` with `a`, `z`, `v`
bounded AR(1) processes with persistences `ρ_a, ρ_z, ρ_v ≤ 1 < φ_π`, the forward solution
(25) is `π̂_t = c_a/(φ_π − ρ_a) a_t + c_z/(φ_π − ρ_z) z_t − v_t/(φ_π − ρ_v)`. -/
theorem inflation_ar1_closed_form {φ ρa ρz ρv ca cz : ℝ} (hφ : 1 < φ) (hρa : ρa ≤ 1)
    (hρz : ρz ≤ 1) (hρv : ρv ≤ 1) {a z v rhat : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hz : 𝔼.IsAR1 ρz z) (hv : 𝔼.IsAR1 ρv v) (hab : BoundedProc a) (hzb : BoundedProc z)
    (hvb : BoundedProc v) (hr : ∀ t, rhat t = ca • a t + cz • z t) :
    fwd25 𝔼 φ rhat v =
      fun t => (ca / (φ - ρa)) • a t + (cz / (φ - ρz)) • z t - (φ - ρv)⁻¹ • v t := by
  have hda : φ - ρa ≠ 0 := by linarith
  have hdz : φ - ρz ≠ 0 := by linarith
  have hdv : φ - ρv ≠ 0 := by linarith
  obtain ⟨Ma, hMa⟩ := hab
  obtain ⟨Mz, hMz⟩ := hzb
  obtain ⟨Mv, hMv⟩ := hvb
  have hra : 𝔼.Adapted rhat := fun t => by
    rw [hr t, map_add, map_smul, map_smul, ha.1 t, hz.1 t]
  have hrb : BoundedProc rhat := by
    refine ⟨|ca| * Ma + |cz| * Mz, fun t ω => ?_⟩
    rw [hr t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul_of_nonneg_left (hMa t ω) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hMz t ω) (abs_nonneg _)
  obtain ⟨-, -, -, huniq⟩ := eq25_unique_bounded 𝔼 hφ hrb ⟨Mv, hMv⟩ hra hv.1
  refine (huniq _ (fun t => ?_) ?_).symm
  · funext ω
    have h1 := congrFun (ha.2 t) ω
    have h2 := congrFun (hz.2 t) ω
    have h3 := congrFun (hv.2 t) ω
    have h4 := congrFun (hr t) ω
    simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at h1 h2 h3 h4 ⊢
    rw [h1, h2, h3, h4]
    field_simp
    ring
  · refine ⟨|ca / (φ - ρa)| * Ma + |cz / (φ - ρz)| * Mz + |(φ - ρv)⁻¹| * Mv,
      fun t ω => ?_⟩
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
      rw [abs_mul]
    · exact mul_le_mul_of_nonneg_left (hMa t ω) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hMz t ω) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hMv t ω) (abs_nonneg _)

/-- Galí (2015), (20) p. 23 and p. 27: a real rate `r̂_t = c_a a_t + c_z z_t` built from
bounded adapted drivers is bounded and adapted. -/
theorem combo_bounded_adapted {ca cz : ℝ} {a z rhat : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a)
    (hz : 𝔼.Adapted z) (hab : BoundedProc a) (hzb : BoundedProc z)
    (hr : ∀ t, rhat t = ca • a t + cz • z t) : BoundedProc rhat ∧ 𝔼.Adapted rhat := by
  obtain ⟨Ma, hMa⟩ := hab
  obtain ⟨Mz, hMz⟩ := hzb
  refine ⟨⟨|ca| * Ma + |cz| * Mz, fun t ω => ?_⟩, fun t => ?_⟩
  · rw [hr t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul_of_nonneg_left (hMa t ω) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hMz t ω) (abs_nonneg _)
  · rw [hr t, map_add, map_smul, map_smul, ha t, hz t]

/-- Galí (2015), p. 27 (closed form of every bounded equilibrium): if `r̂_t = c_a a_t + c_z z_t`
with bounded AR(1) drivers and `ρ_a, ρ_z, ρ_v ≤ 1 < φ_π`, every bounded solution of (24) has
`π_t = π + c_a/(φ_π − ρ_a) a_t + c_z/(φ_π − ρ_z) z_t − v_t/(φ_π − ρ_v)`. -/
theorem infl_closed_form {φ ρa ρz ρv ca cz πbar : ℝ} (hφ : 1 < φ) (hρa : ρa ≤ 1)
    (hρz : ρz ≤ 1) (hρv : ρv ≤ 1) {a z v rhat infl : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hz : 𝔼.IsAR1 ρz z) (hv : 𝔼.IsAR1 ρv v) (hab : BoundedProc a) (hzb : BoundedProc z)
    (hvb : BoundedProc v) (hr : ∀ t, rhat t = ca • a t + cz • z t)
    (heq : Eq24 𝔼 φ (gap πbar infl) rhat v) (hb : BoundedProc (gap πbar infl)) (t : ℕ)
    (ω : Ω) :
    infl t ω = πbar + ca / (φ - ρa) * a t ω + cz / (φ - ρz) * z t ω - (φ - ρv)⁻¹ * v t ω := by
  have hc := inflation_ar1_closed_form 𝔼 hφ hρa hρz hρv ha hz hv hab hzb hvb hr
  obtain ⟨hrb, hra⟩ := combo_bounded_adapted 𝔼 ha.1 hz.1 hab hzb hr
  obtain ⟨-, -, -, huniq⟩ := eq25_unique_bounded 𝔼 hφ hrb hvb hra hv.1
  have h := congrFun (congrFun ((huniq _ heq hb).trans hc) t) ω
  simp only [gap, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  linarith

/-- Galí (2015), p. 27 (the printed closed form): with the real rate of (20),
`r̂_t = −σ(1 − ρ_a)ψ_ya a_t + (1 − ρ_z) z_t`, every bounded equilibrium of the rule has
`π_t = π − σ(1−ρ_a)ψ_ya/(φ_π−ρ_a) a_t + (1−ρ_z)/(φ_π−ρ_z) z_t − v_t/(φ_π−ρ_v)`. -/
theorem inflation_closed_form_book {φ ρa ρz ρv σ ψya πbar : ℝ} (hφ : 1 < φ) (hρa : ρa ≤ 1)
    (hρz : ρz ≤ 1) (hρv : ρv ≤ 1) {a z v rhat infl : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hz : 𝔼.IsAR1 ρz z) (hv : 𝔼.IsAR1 ρv v) (hab : BoundedProc a) (hzb : BoundedProc z)
    (hvb : BoundedProc v) (hr : ∀ t, rhat t = (-(σ * (1 - ρa) * ψya)) • a t + (1 - ρz) • z t)
    (heq : Eq24 𝔼 φ (gap πbar infl) rhat v) (hb : BoundedProc (gap πbar infl)) (t : ℕ)
    (ω : Ω) :
    infl t ω = πbar - σ * (1 - ρa) * ψya / (φ - ρa) * a t ω + (1 - ρz) / (φ - ρz) * z t ω -
      1 / (φ - ρv) * v t ω := by
  rw [infl_closed_form 𝔼 hφ hρa hρz hρv ha hz hv hab hzb hvb hr heq hb t ω]
  ring

/-! ### Responses to a monetary policy shock, p. 27 -/

/-- Galí (2015), p. 27: equilibrium inflation `π_t = A − v_t/(φ_π − ρ_v)` as a function of the
date-`t` policy innovation `ε^v_t`, with `v_t = ρ_v v_{t−1} + ε^v_t` and everything not
depending on `ε^v_t` collected in `A`. -/
noncomputable def inflImpact (φ ρv A vprev ε : ℝ) : ℝ := A - (ρv * vprev + ε) / (φ - ρv)

/-- Galí (2015), p. 27: the equilibrium nominal rate `i_t = B − ρ_v v_t/(φ_π − ρ_v)` as a
function of the innovation `ε^v_t`. -/
noncomputable def rateImpact (φ ρv B vprev ε : ℝ) : ℝ := B - ρv / (φ - ρv) * (ρv * vprev + ε)

/-- Galí (2015), p. 27 with (11): money `m_t = p_{t−1} + π_t + y_t − η i_t` as a function of
the innovation `ε^v_t` (`C = p_{t−1} + y_t` does not depend on it). -/
noncomputable def moneyImpact (η φ ρv C A B vprev ε : ℝ) : ℝ :=
  C + inflImpact φ ρv A vprev ε - η * rateImpact φ ρv B vprev ε

/-- Galí (2015), p. 27: with `φ_π > 1`, the equilibrium date-`t` inflation, nominal rate and
money supply (from (11), `m_t = p_t + y_t − η i_t`, and `p_t = p_{t−1} + π_t`) are the impact
maps evaluated at the innovation `ε^v_t = v_t − ρ_v v_{t−1}`; everything else (`a_t`, `z_t`,
`v_{t−1}`, `p_{t−1}`, `y_t`) enters only through `A`, `B`, `C`. -/
theorem impact_representation {ρ πbar η φ ρa ρz ρv ca cz : ℝ} (hφ : 1 < φ) (hρa : ρa ≤ 1)
    (hρz : ρz ≤ 1) (hρv : ρv ≤ 1) {a z v rhat infl i m p y : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hz : 𝔼.IsAR1 ρz z) (hv : 𝔼.IsAR1 ρv v) (hab : BoundedProc a)
    (hzb : BoundedProc z) (hvb : BoundedProc v) (hr : ∀ t, rhat t = ca • a t + cz • z t)
    (hR : Rule ρ πbar φ i infl v) (hF : Fisher 𝔼 i infl (realRate ρ rhat))
    (hb : BoundedProc (gap πbar infl)) (hm : ∀ t, m t = p t + y t - η • i t)
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (t : ℕ) (ω : Ω) :
    infl (t + 1) ω = inflImpact φ ρv
        (πbar + ca / (φ - ρa) * a (t + 1) ω + cz / (φ - ρz) * z (t + 1) ω) (v t ω)
        (v (t + 1) ω - ρv * v t ω) ∧
      i (t + 1) ω = rateImpact φ ρv
        (ρ + πbar + φ * (ca / (φ - ρa)) * a (t + 1) ω + φ * (cz / (φ - ρz)) * z (t + 1) ω)
        (v t ω) (v (t + 1) ω - ρv * v t ω) ∧
      m (t + 1) ω = moneyImpact η φ ρv (p t ω + y (t + 1) ω)
        (πbar + ca / (φ - ρa) * a (t + 1) ω + cz / (φ - ρz) * z (t + 1) ω)
        (ρ + πbar + φ * (ca / (φ - ρa)) * a (t + 1) ω + φ * (cz / (φ - ρz)) * z (t + 1) ω)
        (v t ω) (v (t + 1) ω - ρv * v t ω) := by
  have hdv : φ - ρv ≠ 0 := by linarith
  have heq := (rule_fisher_iff_eq24 𝔼 hR).mp hF
  have hc := infl_closed_form 𝔼 hφ hρa hρz hρv ha hz hv hab hzb hvb hr heq hb (t + 1) ω
  have hi := congrFun (hR (t + 1)) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
  have hinfl : infl (t + 1) ω = inflImpact φ ρv
      (πbar + ca / (φ - ρa) * a (t + 1) ω + cz / (φ - ρz) * z (t + 1) ω) (v t ω)
      (v (t + 1) ω - ρv * v t ω) := by
    rw [hc]
    unfold inflImpact
    ring
  have hrate : i (t + 1) ω = rateImpact φ ρv
      (ρ + πbar + φ * (ca / (φ - ρa)) * a (t + 1) ω + φ * (cz / (φ - ρz)) * z (t + 1) ω)
      (v t ω) (v (t + 1) ω - ρv * v t ω) := by
    rw [hi, hc]
    unfold rateImpact
    field_simp
    ring
  refine ⟨hinfl, hrate, ?_⟩
  have hm1 := congrFun (hm (t + 1)) ω
  have hp1 := congrFun (hp t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hm1 hp1
  rw [hm1, hp1, hinfl, hrate]
  unfold moneyImpact
  ring

/-- Galí (2015), p. 27: `∂π_t/∂ε^v_t = −1/(φ_π − ρ_v)`. -/
theorem hasDerivAt_inflImpact (φ ρv A vprev ε : ℝ) :
    HasDerivAt (inflImpact φ ρv A vprev) (-1 / (φ - ρv)) ε := by
  have h : inflImpact φ ρv A vprev =
      fun e => inflImpact φ ρv A vprev 0 + -1 / (φ - ρv) * e := by
    funext e
    unfold inflImpact
    ring
  rw [h]
  exact hasDerivAt_affine _ _ _

/-- Galí (2015), p. 27: `∂i_t/∂ε^v_t = −ρ_v/(φ_π − ρ_v)`. -/
theorem hasDerivAt_rateImpact (φ ρv B vprev ε : ℝ) :
    HasDerivAt (rateImpact φ ρv B vprev) (-ρv / (φ - ρv)) ε := by
  have h : rateImpact φ ρv B vprev =
      fun e => rateImpact φ ρv B vprev 0 + -ρv / (φ - ρv) * e := by
    funext e
    unfold rateImpact
    ring
  rw [h]
  exact hasDerivAt_affine _ _ _

/-- Galí (2015), p. 27: `∂m_t/∂ε^v_t = (η ρ_v − 1)/(φ_π − ρ_v)`. -/
theorem hasDerivAt_moneyImpact (η φ ρv C A B vprev ε : ℝ) :
    HasDerivAt (moneyImpact η φ ρv C A B vprev) ((η * ρv - 1) / (φ - ρv)) ε := by
  have h : moneyImpact η φ ρv C A B vprev =
      fun e => moneyImpact η φ ρv C A B vprev 0 + (η * ρv - 1) / (φ - ρv) * e := by
    funext e
    unfold moneyImpact inflImpact rateImpact
    ring
  rw [h]
  exact hasDerivAt_affine _ _ _

/-- Galí (2015), p. 27: a monetary tightening lowers inflation, `−1/(φ_π − ρ_v) < 0`, for
`φ_π > ρ_v`. -/
theorem inflation_falls {φ ρv : ℝ} (hφ : ρv < φ) : -1 / (φ - ρv) < 0 :=
  div_neg_of_neg_of_pos (by norm_num) (by linarith)

/-- Galí (2015), p. 27: the nominal rate falls after a tightening, `−ρ_v/(φ_π − ρ_v) < 0`,
iff the shock is persistent, `ρ_v > 0` (given `φ_π > ρ_v`). -/
theorem rate_falls_iff {φ ρv : ℝ} (hφ : ρv < φ) : -ρv / (φ - ρv) < 0 ↔ 0 < ρv := by
  have hd : 0 < φ - ρv := by linarith
  rw [div_neg_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, hd⟩

/-- Galí (2015), p. 27 (**liquidity effect iff `η ρ_v > 1`**): for `η ≥ 0` and `φ_π > ρ_v`,
the nominal rate falls and the money supply rises after a policy shock
(`∂i_t/∂ε^v_t < 0 < ∂m_t/∂ε^v_t`) iff `η ρ_v > 1`. -/
theorem liquidity_effect_iff {η φ ρv : ℝ} (hη : 0 ≤ η) (hφ : ρv < φ) :
    (-ρv / (φ - ρv) < 0 ∧ 0 < (η * ρv - 1) / (φ - ρv)) ↔ 1 < η * ρv := by
  have hd : 0 < φ - ρv := by linarith
  rw [div_pos_iff_of_pos_right hd]
  constructor
  · rintro ⟨-, h⟩
    linarith
  · intro h
    refine ⟨(rate_falls_iff hφ).mpr ?_, by linarith⟩
    by_contra hρ
    push Not at hρ
    nlinarith

/-! ### (26): multiplicity for `φ_π < 1`, p. 28 -/

/-- Galí (2015), eq. (26), p. 28, in gaps: `π̂_0 = ξ_0`,
`π̂_{t+1} = φ_π π̂_t − r̂_t + v_t + ξ_{t+1}`. -/
def path26 (φ : ℝ) (rhat v ξ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => ξ 0
  | t + 1 => φ • path26 φ rhat v ξ t - rhat t + v t + ξ (t + 1)

/-- Galí (2015), p. 28: the surprise component of a process, `z_0` at date 0 and
`z_{t+1} − E_t{z_{t+1}}` afterwards. -/
def surprise (z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => z 0
  | t + 1 => z (t + 1) - 𝔼.E t (z (t + 1))

/-- Galí (2015), p. 28: the surprise of an adapted process is a martingale difference. -/
theorem surprise_isMDS {z : ℕ → Ω → ℝ} (h : 𝔼.Adapted z) : IsMDS 𝔼 (surprise 𝔼 z) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · cases t with
    | zero => exact h 0
    | succ t => simp only [surprise, map_sub, h (t + 1), 𝔼.known (Nat.le_succ t)]
  · simp only [surprise, map_sub, 𝔼.E_E_self, sub_self]

/-- Galí (2015), eq. (26), p. 28: the path (26) is adapted. -/
theorem path26_adapted {φ : ℝ} {rhat v ξ : ℕ → Ω → ℝ} (hr : 𝔼.Adapted rhat)
    (hv : 𝔼.Adapted v) (hξ : 𝔼.Adapted ξ) : 𝔼.Adapted (path26 φ rhat v ξ) := by
  intro t
  induction t with
  | zero => exact hξ 0
  | succ t ih =>
    simp only [path26, map_add, map_sub, map_smul, hξ (t + 1), E_of_known 𝔼 ih (Nat.le_succ t),
      E_of_adapted_le 𝔼 hr (Nat.le_succ t), E_of_adapted_le 𝔼 hv (Nat.le_succ t)]

/-- Galí (2015), eq. (26), p. 28 (sufficiency, any `φ_π`): for every martingale-difference
`ξ`, the path (26) solves (24). -/
theorem path26_eq24 {φ : ℝ} {rhat v ξ : ℕ → Ω → ℝ} (hr : 𝔼.Adapted rhat) (hv : 𝔼.Adapted v)
    (hξ : IsMDS 𝔼 ξ) : Eq24 𝔼 φ (path26 φ rhat v ξ) rhat v := by
  intro t
  have ha := path26_adapted 𝔼 (φ := φ) hr hv hξ.1 t
  simp only [path26, map_add, map_sub, map_smul, ha, hr t, hv t, hξ.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (26), p. 28 (boundedness): for `|φ_π| < 1` and bounded `r̂`, `v`, `ξ`,
the path (26) is bounded (by `max M_ξ (B/(1 − |φ_π|))`, `B = M_r + M_v + M_ξ`). -/
theorem path26_bounded {φ : ℝ} (hφ : |φ| < 1) {rhat v ξ : ℕ → Ω → ℝ}
    (hrb : BoundedProc rhat) (hvb : BoundedProc v) (hξb : BoundedProc ξ) :
    BoundedProc (path26 φ rhat v ξ) := by
  obtain ⟨Mr, hMr⟩ := hrb
  obtain ⟨Mv, hMv⟩ := hvb
  obtain ⟨Mξ, hMξ⟩ := hξb
  have hpos : 0 < 1 - |φ| := by linarith
  set K := max Mξ ((Mr + Mv + Mξ) / (1 - |φ|)) with hK
  have hBK : Mr + Mv + Mξ ≤ (1 - |φ|) * K := by
    calc Mr + Mv + Mξ = (1 - |φ|) * ((Mr + Mv + Mξ) / (1 - |φ|)) := by field_simp
      _ ≤ (1 - |φ|) * K := mul_le_mul_of_nonneg_left (le_max_right _ _) hpos.le
  refine ⟨K, fun t => ?_⟩
  induction t with
  | zero => exact fun ω => (hMξ 0 ω).trans (le_max_left _ _)
  | succ t ih =>
    intro ω
    simp only [path26, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : |φ * path26 φ rhat v ξ t ω| ≤ |φ| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (ih ω) (abs_nonneg _)
    have h1' := abs_le.mp h1
    have h2 := abs_le.mp (hMr t ω)
    have h3 := abs_le.mp (hMv t ω)
    have h4 := abs_le.mp (hMξ (t + 1) ω)
    rw [abs_le]
    constructor <;> nlinarith

/-- Galí (2015), p. 28: the surprise of the path (26) is the sunspot `ξ` itself. -/
theorem surprise_path26 {φ : ℝ} {rhat v ξ : ℕ → Ω → ℝ} (hr : 𝔼.Adapted rhat)
    (hv : 𝔼.Adapted v) (hξ : IsMDS 𝔼 ξ) : surprise 𝔼 (path26 φ rhat v ξ) = ξ := by
  funext t
  cases t with
  | zero => rfl
  | succ t =>
    have ha := path26_adapted 𝔼 (φ := φ) hr hv hξ.1 t
    simp only [surprise, path26, map_add, map_sub, map_smul, ha, hr t, hv t, hξ.2 t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring

/-- Galí (2015), eq. (26), p. 28 (**necessity and sufficiency**, any `φ_π`): an adapted
process solves (24) iff it is the path (26) for some martingale-difference `ξ`. -/
theorem eq24_iff_path26 {φ : ℝ} {z rhat v : ℕ → Ω → ℝ} (hr : 𝔼.Adapted rhat)
    (hv : 𝔼.Adapted v) (hz : 𝔼.Adapted z) :
    Eq24 𝔼 φ z rhat v ↔ ∃ ξ, IsMDS 𝔼 ξ ∧ z = path26 φ rhat v ξ := by
  constructor
  · intro h
    refine ⟨surprise 𝔼 z, surprise_isMDS 𝔼 hz, ?_⟩
    funext t
    induction t with
    | zero => rfl
    | succ t ih =>
      funext ω
      have h1 := congrFun (h t) ω
      have h2 := congrFun ih ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
      simp only [path26, surprise, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [← h2]
      linarith
  · rintro ⟨ξ, hξ, rfl⟩
    exact path26_eq24 𝔼 hr hv hξ

/-- Galí (2015), p. 28: distinct sunspots give distinct equilibria (26). -/
theorem path26_injective {φ : ℝ} {rhat v ξ ξ' : ℕ → Ω → ℝ} (hr : 𝔼.Adapted rhat)
    (hv : 𝔼.Adapted v) (hξ : IsMDS 𝔼 ξ) (hξ' : IsMDS 𝔼 ξ')
    (h : path26 φ rhat v ξ = path26 φ rhat v ξ') : ξ = ξ' := by
  rw [← surprise_path26 𝔼 (φ := φ) hr hv hξ, ← surprise_path26 𝔼 (φ := φ) hr hv hξ', h]

/-- Galí (2015), eq. (26), p. 28, in levels: with `π_t = π + π̂_t`,
`π_{t+1} = (1 − φ_π)π + φ_π π_t − r̂_t + v_t + ξ_{t+1}`. -/
theorem eq26_levels {πbar φ : ℝ} {rhat v ξ infl : ℕ → Ω → ℝ}
    (h : ∀ s, infl s = (fun _ => πbar) + path26 φ rhat v ξ s) (t : ℕ) :
    infl (t + 1) = (fun _ => (1 - φ) * πbar) + φ • infl t - rhat t + v t + ξ (t + 1) := by
  rw [h (t + 1), h t]
  funext ω
  simp only [path26, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (26) and p. 28 (**multiplicity for `|φ_π| < 1`**): every bounded
martingale-difference `ξ` gives a bounded adapted solution of (24), and different sunspots
give different solutions. -/
theorem eq26_multiplicity {φ : ℝ} (hφ : |φ| < 1) {rhat v : ℕ → Ω → ℝ}
    (hr : 𝔼.Adapted rhat) (hv : 𝔼.Adapted v) (hrb : BoundedProc rhat) (hvb : BoundedProc v) :
    (∀ ξ, IsMDS 𝔼 ξ → BoundedProc ξ →
      Eq24 𝔼 φ (path26 φ rhat v ξ) rhat v ∧ BoundedProc (path26 φ rhat v ξ) ∧
        𝔼.Adapted (path26 φ rhat v ξ)) ∧
      ∀ ξ ξ', IsMDS 𝔼 ξ → IsMDS 𝔼 ξ' → ξ ≠ ξ' → path26 φ rhat v ξ ≠ path26 φ rhat v ξ' :=
  ⟨fun _ hξ hξb => ⟨path26_eq24 𝔼 hr hv hξ, path26_bounded hφ hrb hvb hξb,
      path26_adapted 𝔼 hr hv hξ.1⟩,
    fun _ _ hξ hξ' hne h => hne (path26_injective 𝔼 hr hv hξ hξ' h)⟩

/-- Galí (2015), fn. 7, p. 28: `ξ_t = τ_a ε^a_t + τ_z ε^z_t + τ_v ε^v_t + ξ*_t` is a
martingale difference for every choice of `τ_a, τ_z, τ_v` when the fundamental innovations
and the pure sunspot `ξ*` are. -/
theorem isMDS_fn7 {τa τz τv : ℝ} {εa εz εv ξs : ℕ → Ω → ℝ} (ha : IsMDS 𝔼 εa)
    (hz : IsMDS 𝔼 εz) (hv : IsMDS 𝔼 εv) (hs : IsMDS 𝔼 ξs) :
    IsMDS 𝔼 (fun t => τa • εa t + τz • εz t + τv • εv t + ξs t) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simp only [map_add, map_smul, ha.1 t, hz.1 t, hv.1 t, hs.1 t]
  · simp only [map_add, map_smul, ha.2 t, hz.2 t, hv.2 t, hs.2 t, smul_zero, add_zero]

/-- Galí (2015), fn. 7, p. 28 (**indeterminate responses**): in the equilibrium (26) built on
the sunspot of fn. 7, the inflation surprise at `t + 1` is
`τ_a ε^a_{t+1} + τ_z ε^z_{t+1} + τ_v ε^v_{t+1} + ξ*_{t+1}`, so its response to each
fundamental shock is the arbitrary coefficient `τ`. -/
theorem fn7_surprise {φ τa τz τv : ℝ} {rhat v εa εz εv ξs : ℕ → Ω → ℝ}
    (hr : 𝔼.Adapted rhat) (hv : 𝔼.Adapted v) (ha : IsMDS 𝔼 εa)
    (hz : IsMDS 𝔼 εz) (hve : IsMDS 𝔼 εv) (hs : IsMDS 𝔼 ξs) (t : ℕ) :
    surprise 𝔼 (path26 φ rhat v (fun s => τa • εa s + τz • εz s + τv • εv s + ξs s)) (t + 1) =
      τa • εa (t + 1) + τz • εz (t + 1) + τv • εv (t + 1) + ξs (t + 1) := by
  rw [surprise_path26 𝔼 hr hv (isMDS_fn7 𝔼 ha hz hve hs)]

/-! ### The Taylor principle, p. 28, including `φ_π = 1` -/

/-- Galí (2015), p. 28: (24) is determinate when, for all bounded adapted `r̂`, `v`, it has
exactly one bounded adapted solution. -/
def Determinate24 (φ : ℝ) : Prop :=
  ∀ rhat v : ℕ → Ω → ℝ, BoundedProc rhat → BoundedProc v → 𝔼.Adapted rhat → 𝔼.Adapted v →
    ∃! z, Eq24 𝔼 φ z rhat v ∧ BoundedProc z ∧ 𝔼.Adapted z

/-- Galí (2015), p. 28: the deterministic self-fulfilling path `φ_π^t c` of the homogeneous
equation `φ_π d_t = E_t{d_{t+1}}`. -/
def homPath (φ c : ℝ) : ℕ → Ω → ℝ := fun t _ => φ ^ t * c

/-- Galí (2015), p. 28: the self-fulfilling path is deterministic, hence known at every date. -/
theorem E_homPath (φ c : ℝ) (t s : ℕ) : 𝔼.E t (homPath φ c s) = homPath φ c s :=
  𝔼.const t _

/-- Galí (2015), p. 28: adding `φ_π^t c` to a solution of (24) gives another solution. -/
theorem eq24_add_homPath {φ c : ℝ} {z rhat v : ℕ → Ω → ℝ} (hz : Eq24 𝔼 φ z rhat v) :
    Eq24 𝔼 φ (fun t => z t + homPath φ c t) rhat v := by
  intro t
  funext ω
  have h1 := congrFun (hz t) ω
  simp only [map_add, E_homPath, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul] at h1 ⊢
  simp only [homPath, pow_succ]
  linear_combination h1

/-- Galí (2015), p. 28 (**non-uniqueness for `0 ≤ φ_π ≤ 1`**, including `φ_π = 1`): next to
every bounded adapted solution of (24) there is a different one. -/
theorem not_unique_of_le_one [Nonempty Ω] {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ 1)
    {z rhat v : ℕ → Ω → ℝ} (hz : Eq24 𝔼 φ z rhat v) (hzb : BoundedProc z)
    (hza : 𝔼.Adapted z) :
    ∃ z', Eq24 𝔼 φ z' rhat v ∧ BoundedProc z' ∧ 𝔼.Adapted z' ∧ z' ≠ z := by
  obtain ⟨M, hM⟩ := hzb
  refine ⟨fun t => z t + homPath φ 1 t, eq24_add_homPath 𝔼 hz, ⟨M + 1, fun t ω => ?_⟩,
    fun t => ?_, fun h => ?_⟩
  · simp only [homPath, Pi.add_apply, mul_one]
    refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
    rw [abs_of_nonneg (pow_nonneg h0 t)]
    exact pow_le_one₀ h0 h1
  · simp only [map_add, hza t, E_homPath]
  · have := congrFun (congrFun h 0) (Classical.arbitrary Ω)
    simp [homPath] at this

/-- Galí (2015), p. 28 (**the Taylor principle**, with the `φ_π = 1` case decided): for
`φ_π ≥ 0`, (24) is determinate iff `φ_π > 1`. -/
theorem taylor_principle [Nonempty Ω] {φ : ℝ} (hφ : 0 ≤ φ) : Determinate24 𝔼 φ ↔ 1 < φ := by
  constructor
  · intro hD
    by_contra hle
    push Not at hle
    obtain ⟨z, ⟨hz, hzb, hza⟩, huniq⟩ :=
      hD 0 0 ⟨0, fun t ω => by simp⟩ ⟨0, fun t ω => by simp⟩ (fun t => by simp)
        (fun t => by simp)
    obtain ⟨z', h1, h2, h3, hne⟩ := not_unique_of_le_one 𝔼 hφ hle hz hzb hza
    exact hne (huniq z' ⟨h1, h2, h3⟩)
  · intro h rhat v hrb hvb hra hva
    obtain ⟨hs, hb, ha, hu⟩ := eq25_unique_bounded 𝔼 h hrb hvb hra hva
    exact ⟨fwd25 𝔼 φ rhat v, ⟨hs, hb, ha⟩, fun z hz => hu z hz.1 hz.2.1⟩

/-- Galí (2015), p. 28, the case `φ_π = 1` omitted by the book (**existence can fail**): with
`r̂_t − v_t ≡ c ≠ 0`, (24) with `φ_π = 1` has no bounded solution at all, since
`π̂_0 = E_0{π̂_{k+1}} + (k + 1)c` for every `k`. -/
theorem phi_one_no_bounded_solution [Nonempty Ω] {c : ℝ} (hc : c ≠ 0) {z : ℕ → Ω → ℝ}
    (hz : Eq24 𝔼 1 z (fun _ _ => c) 0) : ¬ BoundedProc z := by
  rintro ⟨M, hM⟩
  have hstep : ∀ t ω, z t ω = 𝔼.E t (z (t + 1)) ω + c := fun t ω => by
    have := congrFun (hz t) ω
    simpa using this
  have hiter : ∀ k : ℕ, ∀ ω, z 0 ω = 𝔼.E 0 (z (k + 1)) ω + ((k : ℝ) + 1) * c := by
    intro k
    induction k with
    | zero => intro ω; simpa using hstep 0 ω
    | succ k ih =>
      intro ω
      have hzk : z (k + 1) = 𝔼.E (k + 1) (z (k + 1 + 1)) + fun _ => c := by
        funext ω'
        simp only [Pi.add_apply]
        exact hstep (k + 1) ω'
      rw [ih ω, hzk, map_add, 𝔼.tower (Nat.zero_le _), 𝔼.const]
      simp only [Pi.add_apply]
      push_cast
      ring
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * M / |c|)
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have ω := Classical.arbitrary Ω
  have h1 := hiter k ω
  have h2 := abs_le.mp (hM 0 ω)
  have h3 := abs_le.mp (𝔼.abs_E_le (hM (k + 1)) 0 ω)
  have h4 : ((k : ℝ) + 1) * |c| ≤ 2 * M := by
    rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1), ← abs_mul, abs_le]
    constructor <;> linarith
  have h5 : 2 * M < (k : ℝ) * |c| := by rwa [div_lt_iff₀ hcpos] at hk
  nlinarith

/-! ### Correction C2-3: the forward series can converge when `φ_π < 1` -/

/-- Galí (2015), (25) p. 27 and p. 28 (correction C2-3): for an AR(1) driver
`r̂_t − v_t` with persistence `|ρ| < φ_π`, the forward series (25) converges, with sum
`(r̂_t − v_t)/(φ_π − ρ)`, whether or not `φ_π > 1`. -/
theorem fwd25_ar1_hasSum {φ ρ : ℝ} (hφ : 0 < φ) (hρ : |ρ| < φ) {rhat v : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ (fun t => rhat t - v t)) (t : ℕ) (ω : Ω) :
    HasSum (fun k => φ⁻¹ ^ (k + 1) * 𝔼.E t (rhat (t + k) - v (t + k)) ω)
      ((rhat t ω - v t ω) / (φ - ρ)) := by
  have hq : |ρ / φ| < 1 := by
    rw [abs_div, abs_of_pos hφ, div_lt_one hφ]
    exact hρ
  have hd : φ - ρ ≠ 0 := by
    have := le_abs_self ρ
    linarith
  have hg := (hasSum_geometric_of_abs_lt_one hq).mul_left (φ⁻¹ * (rhat t ω - v t ω))
  have hf : (fun k => φ⁻¹ ^ (k + 1) * 𝔼.E t (rhat (t + k) - v (t + k)) ω) =
      fun k => φ⁻¹ * (rhat t ω - v t ω) * (ρ / φ) ^ k := by
    funext k
    have h := congrFun (𝔼.ar1_iterate hu t k) ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h
    rw [h, div_eq_mul_inv, mul_pow]
    ring
  rw [hf]
  convert hg using 1
  field_simp

/-- Galí (2015), p. 28: for an AR(1) driver, `(r̂_t − v_t)/(φ_π − ρ)` solves (24) for every
`φ_π ≠ ρ`. -/
theorem ar1_solution_eq24 {φ ρ : ℝ} (hd : φ - ρ ≠ 0) {rhat v : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ (fun t => rhat t - v t)) :
    Eq24 𝔼 φ (fun t => (φ - ρ)⁻¹ • (rhat t - v t)) rhat v := by
  intro t
  have h2 : 𝔼.E t (rhat (t + 1) - v (t + 1)) = ρ • (rhat t - v t) := hu.2 t
  rw [map_smul, h2]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), p. 28 (**correction C2-3**): for `0 < φ_π ≤ 1` and a bounded AR(1) driver
`r̂_t − v_t` with `|ρ| < φ_π`, the forward series (25) converges, equals
`(r̂_t − v_t)/(φ_π − ρ)`, and is a bounded adapted solution of (24) — but it is not the
unique one: another bounded adapted solution exists. -/
theorem c2_3_forward_converges_not_unique [Nonempty Ω] {φ ρ : ℝ} (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hρ : |ρ| < φ) {rhat v : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ (fun t => rhat t - v t))
    (hub : BoundedProc (fun t => rhat t - v t)) :
    (∀ t ω, Summable (fun k => φ⁻¹ ^ (k + 1) * 𝔼.E t (rhat (t + k) - v (t + k)) ω)) ∧
      fwd25 𝔼 φ rhat v = (fun t => (φ - ρ)⁻¹ • (rhat t - v t)) ∧
      Eq24 𝔼 φ (fwd25 𝔼 φ rhat v) rhat v ∧ BoundedProc (fwd25 𝔼 φ rhat v) ∧
      𝔼.Adapted (fwd25 𝔼 φ rhat v) ∧
      ∃ z, Eq24 𝔼 φ z rhat v ∧ BoundedProc z ∧ 𝔼.Adapted z ∧ z ≠ fwd25 𝔼 φ rhat v := by
  have hd0 : 0 < φ - ρ := by
    have := le_abs_self ρ
    linarith
  have hfeq : fwd25 𝔼 φ rhat v = (fun t => (φ - ρ)⁻¹ • (rhat t - v t)) := by
    funext t ω
    rw [fwd25, (fwd25_ar1_hasSum 𝔼 hφ hρ hu t ω).tsum_eq]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [div_eq_inv_mul]
  have hsol : Eq24 𝔼 φ (fwd25 𝔼 φ rhat v) rhat v := by
    rw [hfeq]
    exact ar1_solution_eq24 𝔼 hd0.ne' hu
  have hb : BoundedProc (fwd25 𝔼 φ rhat v) := by
    obtain ⟨M, hM⟩ := hub
    refine ⟨(φ - ρ)⁻¹ * M, fun t ω => ?_⟩
    rw [hfeq]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hd0)]
    exact mul_le_mul_of_nonneg_left (hM t ω) (inv_pos.mpr hd0).le
  have ha : 𝔼.Adapted (fwd25 𝔼 φ rhat v) := by
    intro t
    rw [hfeq]
    simp only [map_smul]
    rw [hu.1 t]
  obtain ⟨z, h1, h2, h3, h4⟩ := not_unique_of_le_one 𝔼 hφ.le hφ1 hsol hb ha
  exact ⟨fun t ω => (fwd25_ar1_hasSum 𝔼 hφ hρ hu t ω).summable, hfeq, hsol, hb, ha,
    z, h1, h2, h3, h4⟩

/-- Galí (2015), p. 28: the printed claim "if `φ_π < 1`, the forward solution (25) does not
converge", read as: for every bounded adapted `r̂`, `v` the series (25) diverges somewhere. -/
def PrintedDivergence (φ : ℝ) : Prop :=
  ∀ rhat v : ℕ → Ω → ℝ, BoundedProc rhat → BoundedProc v → 𝔼.Adapted rhat → 𝔼.Adapted v →
    ∃ t ω, ¬ Summable (fun k => φ⁻¹ ^ (k + 1) * 𝔼.E t (rhat (t + k) - v (t + k)) ω)

/-- Galí (2015), p. 28 (**the printed claim is false**, correction C2-3): in the coin-flip
tree, for every `φ_π > 0` (in particular every `φ_π ∈ (0, 1)`), the serially uncorrelated
real-rate shock `r̂_t = ε_t` (an AR(1) with `ρ = 0`) gives a convergent series (25). -/
theorem printed_divergence_false {φ : ℝ} (hφ : 0 < φ) :
    ¬ PrintedDivergence coinSystem φ := by
  intro h
  have hz : (fun t => coinShock t - (0 : ℕ → Bool × Bool → ℝ) t) = coinShock := by
    funext t ω
    simp
  have hu : coinSystem.IsAR1 0 (fun t => coinShock t - (0 : ℕ → Bool × Bool → ℝ) t) := by
    rw [hz]
    exact ⟨coinShock_isMDS.1, fun t => by rw [coinShock_mean_zero, zero_smul]⟩
  obtain ⟨t, ω, hns⟩ := h coinShock 0 coinShock_bounded ⟨0, fun t ω => by simp⟩
    coinShock_isMDS.1 (fun t => by simp)
  exact hns (fwd25_ar1_hasSum coinSystem hφ (by simpa using hφ) hu t ω).summable

end Gali.ClassicalMonetaryModel.InterestRules
