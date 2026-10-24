/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.Valuation

/-!
# The starred-form policy rules

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.6, eqs. (16.20)–(16.24),
p. 373; Chapter 22, §22.1, eqs. (22.1)–(22.2), p. 495, and §22.3, eqs. (22.7)–(22.11), p. 501;
Chapter 23, eqs. (23.1)–(23.4), p. 512; Chapter 24, eqs. (24.1)–(24.2), p. 520.

The frictionless model `i_t = E_t π_{t+1}`, `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` is closed
by monetary and fiscal policy written around a *target* path `(π*, i*, v*, s̃*)` (the starred
variables):

* `i_t = i*_t + φ (π_t − π*_t)` ((16.19), (22.1); with `i*_t = θπ*_t + u_{i,t}`, (22.8)),
* `s̃_{t+1} = s̃*_{t+1} + γ (v_t − v*_t)` with `s̃*_{t+1} = α v*_t + u_{s,t+1}` ((22.1), (22.9)),

where the target is itself consistent with the Fisher equation and the flow condition
((16.21), (22.10)). `φ` and `γ` describe behaviour *off* the target: they are the
equilibrium-selection parameters.

## Reading of the starred debt equation

As printed, (16.21) and (22.1)/(22.10) drive the starred debt `v*` with the *actual* surplus
`s̃_{t+1}`. Here the target is an exogenous consistent path: `v*` is driven by the target surplus
`s̃*_{t+1} = α v*_t + u_{s,t+1}` (`Consistent`, `StarredSurplus`). On the target both readings
coincide; off the target they differ. Under the printed reading `γ` drops out of the gap
dynamics and fiscal policy is passive iff `γ = α` (`LeeperRegions.literal_tvc_iff`); under the
reading used here fiscal policy is passive iff `0 < γ < 2` (`Equivalence.unique_iff`).

## Timing and the initial condition

Dates are `t : ℕ`. The flow condition links `v_t, i_t` to `π_{t+1}, v_{t+1}, s̃_{t+1}` for
`t ≥ 0`. At date 0 the inherited nominal debt and the date-0 surplus are common to every
candidate path, so the date-0 flow condition `ρ v_0 = v_{−1} + i_{−1} − π_0 − s̃_0` becomes the
initial condition `ρ v_0 + π_0 = ρ v*_0 + π*_0` (`Eqm`): a date-0 jump in inflation must be
matched by a change in the value of debt. This keeps the date-0 unexpected inflation of the book
in the model even under perfect foresight. The condition `π_0 = π*_0` is not imposed: in the
determinate regions it is derived (`Equivalence.unique_of_determinate`).

## Main definitions and results

* `Outcome`: a path `(π, i, v, s̃)`; `Consistent`: the target obeys the Fisher equation and the
  flow condition; `Admissible`: adapted, bounded inflation, transversality condition for debt.
* `Eqm`: an equilibrium of the `(φ, γ)` starred system around a target.
* `StarredSurplus`, `ThetaRule`: the parametrisations `s̃*_{t+1} = α v*_t + u_{s,t+1}` and
  `i*_t = θπ*_t + u_{i,t}`; `eq22_8`, `eq22_9`, `consistent_iff_eq22_10`, `eq23_4_starred`.
* `starred_eqm`: the target is an equilibrium for every `(φ, γ)`.
* `deviation_dynamics`: deviations `e = π − π*`, `d = v − v*` obey `E_t e_{t+1} = φ e_t`,
  `ρ d_{t+1} = (1 − γ) d_t − ΔE_{t+1} e_{t+1}`, `ρ d_0 + e_0 = 0`; `ofDev`, `ofDev_eqm`,
  `eq_ofDev`: every solution of these deviation equations gives an equilibrium and every
  equilibrium arises this way.
* `observables_eq16_23_24`: on the target the observables obey (16.23)–(16.24).
* `valuation_all_regimes` (p. 497): every admissible equilibrium of every `(φ, γ)` system
  satisfies the government debt valuation equation.
* `LeeperEqm`, `eq23_4`: the unstarred Leeper model (22.3)–(22.6) = (23.1)–(23.4) (with the `ρ`
  that (22.6) omits, survey error E13) and the substitution (23.4) of p. 512.
* `rule24_1_printed` (survey error E14): the printed rule (24.1) `i = θπ_t + φ(π_t − π*_t) + u` is
  the starred rule with target rate `θπ*_t + u` and off-target coefficient `θ + φ`.
-/

namespace Cochrane.ObservationalEquivalence.StarredModel

open Filter Topology
open Cochrane.ObservationalEquivalence.Valuation

variable (Ω : Type*)

/-- Cochrane (2023), (22.1)–(22.2), p. 495: a path of the observables — inflation `π_t`, the
nominal rate `i_t`, the real value of debt `v_t` and the real primary surplus `s̃_t`. -/
structure Outcome where
  /-- Inflation `π_t`. -/
  pi : ℕ → Ω → ℝ
  /-- The nominal interest rate `i_t`. -/
  i : ℕ → Ω → ℝ
  /-- The real value of government debt at the end of date `t`, `v_t`. -/
  v : ℕ → Ω → ℝ
  /-- The real primary surplus `s̃_t`. -/
  s : ℕ → Ω → ℝ

variable {Ω} (𝔼 : ExpectationSystem Ω)

omit 𝔼 in
/-- Cochrane (2023), (22.1), p. 495: two paths are equal when their four components are. -/
theorem outcome_ext {x y : Outcome Ω} (h1 : x.pi = y.pi) (h2 : x.i = y.i) (h3 : x.v = y.v)
    (h4 : x.s = y.s) : x = y := by
  cases x
  cases y
  simp only at h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-! ### Definitions -/

/-- Cochrane (2023), (16.21), p. 373, and (22.10), p. 501: the target path is consistent with
the model — `i*_t = E_t π*_{t+1}` and `ρ v*_{t+1} = v*_t + i*_t − π*_{t+1} − s̃*_{t+1}`. -/
def Consistent (ρ : ℝ) (tg : Outcome Ω) : Prop :=
  Fisher 𝔼 tg.i tg.pi ∧ Flow ρ tg.v tg.i tg.pi tg.s

/-- Cochrane (2023), §22.1, p. 495 (the equilibrium criterion): inflation and debt are adapted,
inflation is bounded ("the rule against nominal explosions", p. 508) and debt satisfies the
transversality condition. -/
def Admissible (ρ : ℝ) (x : Outcome Ω) : Prop :=
  𝔼.Adapted x.pi ∧ 𝔼.Adapted x.v ∧ BoundedProc x.pi ∧ TVC 𝔼 ρ x.v

/-- Cochrane (2023), (16.20)–(16.22), p. 373, and (22.1)–(22.2), p. 495: `x` is an equilibrium of
the starred system with off-target coefficients `φ` (money) and `γ` (fiscal) around the target
`tg`: the Fisher equation, `i_t = i*_t + φ(π_t − π*_t)`,
`s̃_{t+1} = s̃*_{t+1} + γ(v_t − v*_t)` (`s̃_0 = s̃*_0`), the flow condition, and the common
inherited debt at date 0, `ρ v_0 + π_0 = ρ v*_0 + π*_0`. -/
def Eqm (ρ φ γ : ℝ) (tg x : Outcome Ω) : Prop :=
  Fisher 𝔼 x.i x.pi ∧ (∀ t, x.i t = tg.i t + φ • (x.pi t - tg.pi t)) ∧ x.s 0 = tg.s 0 ∧
    (∀ t, x.s (t + 1) = tg.s (t + 1) + γ • (x.v t - tg.v t)) ∧ Flow ρ x.v x.i x.pi x.s ∧
    ρ • x.v 0 + x.pi 0 = ρ • tg.v 0 + tg.pi 0

/-- Cochrane (2023), (22.1), p. 495, and (22.9), p. 501: the starred surplus
`s̃*_{t+1} = α v*_t + u_{s,t+1}`. -/
def StarredSurplus (α : ℝ) (vS us sS : ℕ → Ω → ℝ) : Prop :=
  ∀ t, sS (t + 1) = α • vS t + us (t + 1)

/-- Cochrane (2023), (22.8), p. 501: the target interest rate `i*_t = θπ*_t + u_{i,t}`. -/
def ThetaRule (θ : ℝ) (piS ui iS : ℕ → Ω → ℝ) : Prop :=
  ∀ t, iS t = θ • piS t + ui t

/-! ### The equations of the starred system -/

omit 𝔼 in
/-- Cochrane (2023), eq. (22.8), p. 501: with `i*_t = θπ*_t + u_{i,t}` the monetary rule reads
`i_t = θπ*_t + φ(π_t − π*_t) + u_{i,t}`. -/
theorem eq22_8 {φ θ : ℝ} {tg x : Outcome Ω} {ui : ℕ → Ω → ℝ} (hθ : ThetaRule θ tg.pi ui tg.i)
    (hm : ∀ t, x.i t = tg.i t + φ • (x.pi t - tg.pi t)) (t : ℕ) :
    x.i t = θ • tg.pi t + φ • (x.pi t - tg.pi t) + ui t := by
  rw [hm t, hθ t]
  abel

omit 𝔼 in
/-- Cochrane (2023), eq. (22.9), p. 501 (and (24.2), p. 520): with `s̃*_{t+1} = α v*_t + u_{s,t+1}`
the fiscal rule reads `s̃_{t+1} = α v*_t + γ(v_t − v*_t) + u_{s,t+1}`. -/
theorem eq22_9 {γ α : ℝ} {tg x : Outcome Ω} {us : ℕ → Ω → ℝ} (hα : StarredSurplus α tg.v us tg.s)
    (hs : ∀ t, x.s (t + 1) = tg.s (t + 1) + γ • (x.v t - tg.v t)) (t : ℕ) :
    x.s (t + 1) = α • tg.v t + γ • (x.v t - tg.v t) + us (t + 1) := by
  rw [hs t, hα t]
  abel

/-- Cochrane (2023), eq. (22.10), p. 501 (and (16.21), p. 373): a target obeying the Fisher
equation is consistent iff `ρ v*_{t+1} = v*_t − ΔE_{t+1}π*_{t+1} − s̃*_{t+1}`. -/
theorem consistent_iff_eq22_10 {ρ : ℝ} {tg : Outcome Ω} (hF : Fisher 𝔼 tg.i tg.pi) :
    Consistent 𝔼 ρ tg ↔
      ∀ t, ρ • tg.v (t + 1) = tg.v t - surprise 𝔼 tg.pi t - tg.s (t + 1) := by
  unfold Consistent
  rw [flow_iff_surprise 𝔼 hF]
  exact ⟨fun h => h.2, fun h => ⟨hF, h⟩⟩

/-- Cochrane (2023), (22.10), p. 501, and the substitution of (23.4), p. 512, for the target:
`ρ v*_{t+1} = (1 − α) v*_t − ΔE_{t+1}π*_{t+1} − u_{s,t+1}`. -/
theorem eq23_4_starred {ρ α : ℝ} {tg : Outcome Ω} {us : ℕ → Ω → ℝ} (hc : Consistent 𝔼 ρ tg)
    (hα : StarredSurplus α tg.v us tg.s) (t : ℕ) :
    ρ • tg.v (t + 1) = (1 - α) • tg.v t - surprise 𝔼 tg.pi t - us (t + 1) := by
  rw [((consistent_iff_eq22_10 𝔼 hc.1).mp hc) t, hα t, sub_smul, one_smul]
  abel

/-- Cochrane (2023), §16.6, p. 373, and §22.1, p. 495 ("in equilibrium, starred variables equal
their unstarred counterparts"): a consistent target is an equilibrium for every `φ` and `γ`. -/
theorem starred_eqm {ρ : ℝ} (φ γ : ℝ) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg) :
    Eqm 𝔼 ρ φ γ tg tg :=
  ⟨hc.1, fun t => by simp, rfl, fun t => by simp, hc.2, rfl⟩

/-- Cochrane (2023), (16.23)–(16.24), p. 373: in an equilibrium on the target debt path the
observables obey
`i_t = E_t π_{t+1}`, `s̃_{t+1} = α v_t + u_{s,t+1}`, `ρ v_{t+1} = v_t − ΔE_{t+1}π_{t+1} − s̃_{t+1}`;
neither `φ` nor `γ` appears. -/
theorem observables_eq16_23_24 {ρ φ γ α : ℝ} {tg x : Outcome Ω} {us : ℕ → Ω → ℝ}
    (hα : StarredSurplus α tg.v us tg.s) (hx : Eqm 𝔼 ρ φ γ tg x) (hv : x.v = tg.v) :
    Fisher 𝔼 x.i x.pi ∧ (∀ t, x.s (t + 1) = α • x.v t + us (t + 1)) ∧
      ∀ t, ρ • x.v (t + 1) = x.v t - surprise 𝔼 x.pi t - x.s (t + 1) := by
  obtain ⟨hF, -, -, hs, hflow, -⟩ := hx
  refine ⟨hF, fun t => ?_, (flow_iff_surprise 𝔼 hF).mp hflow⟩
  rw [hs t, hv, sub_self, smul_zero, add_zero, hα t]

/-! ### Deviation dynamics -/

/-- Cochrane (2023), (22.1), p. 495: the deviation equations. In any equilibrium,
`e = π − π*` and `d = v − v*` satisfy `E_t e_{t+1} = φ e_t`,
`ρ d_{t+1} = (1 − γ) d_t − ΔE_{t+1}e_{t+1}` and `ρ d_0 + e_0 = 0`. -/
theorem deviation_dynamics {ρ φ γ : ℝ} {tg x : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (hx : Eqm 𝔼 ρ φ γ tg x) :
    (∀ t, 𝔼.E t (x.pi (t + 1) - tg.pi (t + 1)) = φ • (x.pi t - tg.pi t)) ∧
      (∀ t, ρ • (x.v (t + 1) - tg.v (t + 1)) =
        (1 - γ) • (x.v t - tg.v t) - surprise 𝔼 (fun t => x.pi t - tg.pi t) t) ∧
      ρ • (x.v 0 - tg.v 0) + (x.pi 0 - tg.pi 0) = 0 := by
  obtain ⟨hF, hm, -, hs, hflow, h0⟩ := hx
  obtain ⟨hFt, hflowt⟩ := hc
  have he : ∀ t, 𝔼.E t (x.pi (t + 1) - tg.pi (t + 1)) = φ • (x.pi t - tg.pi t) := by
    intro t
    rw [map_sub, ← hF t, ← hFt t, hm t, add_sub_cancel_left]
  refine ⟨he, fun t => ?_, ?_⟩
  · funext ω
    have h1 := congrFun (hflow t) ω
    have h2 := congrFun (hflowt t) ω
    have h3 := congrFun (hm t) ω
    have h4 := congrFun (hs t) ω
    have h5 := congrFun (he t) ω
    simp only [surprise, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 h5 ⊢
    rw [h5]
    linear_combination h1 - h2 + h3 - h4
  · rw [smul_sub]
    rw [← sub_eq_zero] at h0
    rw [← h0]
    abel

/-- Cochrane (2023), (22.1), p. 495: the lagged deviation `d_{t−1}` entering the surplus at
date `t` (zero at date 0, when the surplus is the target surplus). -/
def lag (d : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => d t

/-- Cochrane (2023), (22.1), p. 495: the path built from the target and deviations `e`, `d`:
`π = π* + e`, `i = i* + φ e`, `v = v* + d`, `s̃_{t+1} = s̃*_{t+1} + γ d_t`. -/
def ofDev (φ γ : ℝ) (tg : Outcome Ω) (e d : ℕ → Ω → ℝ) : Outcome Ω where
  pi := fun t => tg.pi t + e t
  i := fun t => tg.i t + φ • e t
  v := fun t => tg.v t + d t
  s := fun t => tg.s t + γ • lag d t

/-- Cochrane (2023), (22.1), p. 495 (converse of `deviation_dynamics`): any deviations obeying
the deviation equations give an equilibrium of the `(φ, γ)` system. -/
theorem ofDev_eqm {ρ φ γ : ℝ} {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg) {e d : ℕ → Ω → ℝ}
    (he : ∀ t, 𝔼.E t (e (t + 1)) = φ • e t)
    (hd : ∀ t, ρ • d (t + 1) = (1 - γ) • d t - surprise 𝔼 e t) (h0 : ρ • d 0 + e 0 = 0) :
    Eqm 𝔼 ρ φ γ tg (ofDev φ γ tg e d) := by
  obtain ⟨hFt, hflowt⟩ := hc
  refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_, fun t => ?_, ?_⟩
  · change tg.i t + φ • e t = 𝔼.E t (tg.pi (t + 1) + e (t + 1))
    rw [map_add, he t, hFt t]
  · change tg.i t + φ • e t = tg.i t + φ • (tg.pi t + e t - tg.pi t)
    rw [add_sub_cancel_left]
  · change tg.s 0 + γ • (0 : Ω → ℝ) = tg.s 0
    rw [smul_zero, add_zero]
  · change tg.s (t + 1) + γ • d t = tg.s (t + 1) + γ • (tg.v t + d t - tg.v t)
    rw [add_sub_cancel_left]
  · change ρ • (tg.v (t + 1) + d (t + 1)) =
      (tg.v t + d t) + (tg.i t + φ • e t) - (tg.pi (t + 1) + e (t + 1)) -
        (tg.s (t + 1) + γ • d t)
    funext ω
    have h1 := congrFun (hflowt t) ω
    have h2 := congrFun (hd t) ω
    have h3 := congrFun (he t) ω
    simp only [surprise, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 ⊢
    rw [h3] at h2
    linear_combination h1 + h2
  · change ρ • (tg.v 0 + d 0) + (tg.pi 0 + e 0) = ρ • tg.v 0 + tg.pi 0
    rw [smul_add, ← sub_eq_zero]
    rw [← h0]
    abel

/-- Cochrane (2023), (22.1), p. 495: every equilibrium is the path built from its own
deviations, `x = ofDev φ γ tg (π − π*) (v − v*)`. -/
theorem eq_ofDev {ρ φ γ : ℝ} {tg x : Outcome Ω} (hx : Eqm 𝔼 ρ φ γ tg x) :
    x = ofDev φ γ tg (fun t => x.pi t - tg.pi t) (fun t => x.v t - tg.v t) := by
  obtain ⟨-, hm, hs0, hs, -, -⟩ := hx
  refine outcome_ext ?_ ?_ ?_ ?_
  · funext t; simp [ofDev]
  · funext t; simp only [ofDev]; rw [hm t]
  · funext t; simp [ofDev]
  · funext t
    rcases t with _ | t
    · simp only [ofDev, lag, smul_zero, add_zero]; exact hs0
    · simp only [ofDev, lag]; rw [hs t]

omit 𝔼 in
/-- Cochrane (2023), (22.1), p. 495: zero deviations give back the target. -/
theorem ofDev_zero (φ γ : ℝ) (tg : Outcome Ω) : ofDev φ γ tg 0 0 = tg := by
  refine outcome_ext ?_ ?_ ?_ ?_
  · funext t; simp [ofDev]
  · funext t; simp [ofDev]
  · funext t; simp [ofDev]
  · funext t
    rcases t with _ | t <;> simp [ofDev, lag]

/-- Cochrane (2023), §22.1, p. 495: the deviations of an admissible equilibrium from an
admissible target are adapted, inflation deviations are bounded, and debt deviations satisfy the
transversality condition. -/
theorem dev_admissible {ρ : ℝ} {tg x : Outcome Ω} (htg : Admissible 𝔼 ρ tg)
    (hx : Admissible 𝔼 ρ x) :
    𝔼.Adapted (fun t => x.pi t - tg.pi t) ∧ BoundedProc (fun t => x.pi t - tg.pi t) ∧
      𝔼.Adapted (fun t => x.v t - tg.v t) ∧ TVC 𝔼 ρ (fun t => x.v t - tg.v t) := by
  obtain ⟨hpa, hva, ⟨M, hM⟩, htvc⟩ := hx
  obtain ⟨hpa', hva', ⟨M', hM'⟩, htvc'⟩ := htg
  refine ⟨fun t => ?_, ⟨M + M', fun t ω => ?_⟩, fun t => ?_, tvc_sub 𝔼 htvc htvc'⟩
  · simp only [map_sub, hpa t, hpa' t]
  · simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM t ω) (hM' t ω))
  · simp only [map_sub, hva t, hva' t]

/-- Cochrane (2023), §22.1, p. 495: a path built from an admissible target and adapted
deviations, with bounded `e` and `d` satisfying the transversality condition, is admissible. -/
theorem ofDev_admissible {ρ φ γ : ℝ} {tg : Outcome Ω} (htg : Admissible 𝔼 ρ tg)
    {e d : ℕ → Ω → ℝ} (hea : 𝔼.Adapted e) (heb : BoundedProc e) (hda : 𝔼.Adapted d)
    (hdt : TVC 𝔼 ρ d) : Admissible 𝔼 ρ (ofDev φ γ tg e d) := by
  obtain ⟨hpa, hva, ⟨M, hM⟩, htvc⟩ := htg
  obtain ⟨K, hK⟩ := heb
  refine ⟨fun t => ?_, fun t => ?_, ⟨M + K, fun t ω => ?_⟩, tvc_add 𝔼 htvc hdt⟩
  · change 𝔼.E t (tg.pi t + e t) = tg.pi t + e t
    rw [map_add, hpa t, hea t]
  · change 𝔼.E t (tg.v t + d t) = tg.v t + d t
    rw [map_add, hva t, hda t]
  · change |tg.pi t ω + e t ω| ≤ M + K
    exact (abs_add_le _ _).trans (add_le_add (hM t ω) (hK t ω))

/-! ### The valuation equation holds in every regime -/

/-- Cochrane (2023), §22.1, p. 497 ("the government debt valuation equation is an equilibrium
condition for all of these models"): every admissible equilibrium of every `(φ, γ)` system —
active money, active fiscal or otherwise — with bounded adapted surpluses satisfies
`v_t = ∑ ρʲ E_t s̃_{t+1+j}` and `ΔE_{t+1}π_{t+1} = −ΔE_{t+1} ∑ ρʲ s̃_{t+1+j}`. -/
theorem valuation_all_regimes {ρ φ γ M : ℝ} (hρ : |ρ| < 1) {tg x : Outcome Ω}
    (hx : Eqm 𝔼 ρ φ γ tg x) (hadm : Admissible 𝔼 ρ x) (hs : ∀ t ω, |x.s t ω| ≤ M)
    (hsa : 𝔼.Adapted x.s) :
    (∀ t, x.v t = pvE 𝔼 ρ x.s t t) ∧
      ∀ t, surprise 𝔼 x.pi t = -(pvE 𝔼 ρ x.s (t + 1) t - pvE 𝔼 ρ x.s t t) :=
  ⟨fun t => valuation_tsum 𝔼 hρ hs hx.1 hx.2.2.2.2.1 hadm.2.1 hadm.2.2.2 t,
    fun t => unexpected_inflation 𝔼 hρ hs hsa hx.1 hx.2.2.2.2.1 hadm.2.1 hadm.2.2.2 t⟩

/-! ### The unstarred Leeper model, (22.3)–(22.6) = (23.1)–(23.4) -/

/-- Cochrane (2023), eqs. (22.3)–(22.6), p. 500, and (23.1)–(23.4), p. 512 (with the `ρ` of (23.4);
(22.6) omits it, survey error E13): `i_t = E_t π_{t+1}`, `i_t = φπ_t + u_{i,t}`,
`s̃_{t+1} = γ v_t + u_{s,t+1}` (`s̃_0 = u_{s,0}`), `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`,
and the inherited debt at date 0, `ρ v_0 + π_0 = K` with `K` known at date 0. -/
def LeeperEqm (ρ φ γ : ℝ) (ui us : ℕ → Ω → ℝ) (K : Ω → ℝ) (x : Outcome Ω) : Prop :=
  Fisher 𝔼 x.i x.pi ∧ (∀ t, x.i t = φ • x.pi t + ui t) ∧ x.s 0 = us 0 ∧
    (∀ t, x.s (t + 1) = γ • x.v t + us (t + 1)) ∧ Flow ρ x.v x.i x.pi x.s ∧
    ρ • x.v 0 + x.pi 0 = K

/-- Cochrane (2023), p. 512 (the substitution after (23.4), verified): in the Leeper model
`ρ v_{t+1} = (1 − γ) v_t − ΔE_{t+1}π_{t+1} − u_{s,t+1}`. -/
theorem eq23_4 {ρ φ γ : ℝ} {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (t : ℕ) :
    ρ • x.v (t + 1) = (1 - γ) • x.v t - surprise 𝔼 x.pi t - us (t + 1) := by
  obtain ⟨hF, -, -, hs, hflow, -⟩ := hx
  rw [((flow_iff_surprise 𝔼 hF).mp hflow) t, hs t, sub_smul, one_smul]
  abel

/-- Cochrane (2023), (23.2), p. 512, with the Fisher equation (23.1): in the Leeper model expected
inflation follows `E_t π_{t+1} = φ π_t + u_{i,t}`. -/
theorem leeper_expected_inflation {ρ φ γ : ℝ} {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (t : ℕ) :
    𝔼.E t (x.pi (t + 1)) = φ • x.pi t + ui t := by
  rw [← hx.1 t, hx.2.1 t]

/-- Cochrane (2023), §22.3, p. 500, and (22.1), p. 495: the Leeper model is the starred system in
which the target is chosen as the equilibrium itself — an equilibrium of (22.3)–(22.6) is an
equilibrium of the starred system around itself for every `(φ', γ')`. -/
theorem leeper_is_starred {ρ φ γ : ℝ} {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (φ' γ' : ℝ) :
    Consistent 𝔼 ρ x ∧ Eqm 𝔼 ρ φ' γ' x x :=
  ⟨⟨hx.1, hx.2.2.2.2.1⟩, starred_eqm 𝔼 φ' γ' ⟨hx.1, hx.2.2.2.2.1⟩⟩

/-! ### The printed rule (24.1) -/

omit 𝔼 in
/-- Cochrane (2023), eq. (24.1), p. 520 (survey error E14): the printed rule
`i_t = θπ_t + φ(π_t − π*_t) + u_{i,t}` is the starred rule with target rate
`i*_t = θπ*_t + u_{i,t}` and off-target coefficient `θ + φ` (not `φ`); (22.8) has `θπ*_t`. -/
theorem rule24_1_printed (θ φ : ℝ) (π piS ui i : ℕ → Ω → ℝ) :
    (∀ t, i t = θ • π t + φ • (π t - piS t) + ui t) ↔
      ∀ t, i t = (θ • piS t + ui t) + (θ + φ) • (π t - piS t) := by
  refine forall_congr' fun t => ?_
  constructor <;> intro h <;> rw [h] <;> funext ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring

end Cochrane.ObservationalEquivalence.StarredModel
