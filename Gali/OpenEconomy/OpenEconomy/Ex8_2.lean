/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OpenEconomy.TaylorRule
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Ring.GeomSum

/-!
# Exercise 8.2: technology shocks in the small open economy

Galí (2015), Chapter 8, Exercise 8.2, pp. 259–260. Domestic inflation and the output gap obey
`π_{H,t} = β E_t π_{H,t+1} + κ_υ ỹ_t` and
`ỹ_t = E_t ỹ_{t+1} − σ_υ⁻¹ (i_t − E_t π_{H,t+1} − r^n_t)`, with `r^n_t = ρ − ψ_{ra} a_t`,
natural output `y^n_t = ψ_{ya} a_t` and technology an AR(1), `E_t a_{t+1} = ρ_a a_t`. With
`y* = p* = 0` (and no preference shocks), eq. (27) gives the terms of trade `s_t = σ_υ y_t`
and eq. (14) the nominal exchange rate `e_t = s_t + p_{H,t}`, where
`π_{H,t} = p_{H,t} − p_{H,t−1}` and `p_{H,−1}` is given. By eq. (38), p. 239,
`ψ_{ra} = σ_υ (1 − ρ_a) ψ_{ya}` (with `ψ_{ya} = Γ_a`); the closed forms are given for general
`ψ_{ra}` and specialised under this relation (`h38`).

## Part (a): the rule `i_t = ρ + φ_π π_{H,t}`

* `nk_iff_structural` (with `TaylorRule.Structural`, `TaylorRule.schurStable_AU_iff`,
  `TaylorRule.msv_unique`, imported from `TaylorRule`): the Ch. 3
  machinery (restated from the Chapter 3 project) with `σ ↦ σ_υ`, `κ ↦ κ_υ`, `φ_y = 0`.
* `taylor_determinate_iff`: the system is determinate iff `φ_π > 1` (Bullard–Mitra).
* `taylor_iff`, `taylor_exists`, `taylor_unique`: under `φ_π > 1` the equilibrium with bounded
  adapted `(ỹ, π_H)` exists and is unique:
  `ỹ_t = −(1 − βρ_a) Λ_a ψ_{ra} a_t`, `π_{H,t} = −κ_υ Λ_a ψ_{ra} a_t`,
  `Λ_a = 1/((1 − βρ_a) σ_υ (1 − ρ_a) + κ_υ (φ_π − ρ_a))`, `y_t = ỹ_t + ψ_{ya} a_t`,
  `s_t = σ_υ y_t`, `p_{H,t} = p_{H,−1} + ∑_{k ≤ t} π_{H,k}`, `e_t = s_t + p_{H,t}`.
* `taylor_closed_forms_38`: under (38), `y_t = κ_υ (φ_π − ρ_a) Λ_a ψ_{ya} a_t`,
  `s_t = σ_υ κ_υ (φ_π − ρ_a) Λ_a ψ_{ya} a_t`,
  `e_t = p_{H,−1} + σ_υ κ_υ Λ_a ψ_{ya} [(φ_π − ρ_a) a_t − (1 − ρ_a) ∑_{k ≤ t} a_k]`,
  `i_t = ρ − φ_π σ_υ κ_υ (1 − ρ_a) Λ_a ψ_{ya} a_t`; `taylor_signs_38`: for `ψ_{ya} > 0` a
  positive shock lowers `ỹ` and `π_H` and raises `y` and `s`.
* `taylor_irf_38`: for a one-time shock (`a_t = ρ_aᵗ a_0`),
  `e_t = p_{H,−1} + σ_υ κ_υ Λ_a ψ_{ya} (φ_π ρ_aᵗ − 1) a_0`: a nominal depreciation on impact
  (`φ_π > 1`) and a long-run appreciation (`taylor_irf_tendsto`), with the domestic price level
  permanently lower.

## Part (b): the peg `e_t = 0`

The peg gives `σ_υ ỹ_t = −p_{H,t} − σ_υ ψ_{ya} a_t`, and the Phillips curve becomes the
second-order equation `β E_t p_{H,t+1} − (1 + β + κ_υ/σ_υ) p_{H,t} + p_{H,t−1} = κ_υ ψ_{ya} a_t`
with `p_{H,t−1}` predetermined.

* `charQ`, `exists_root`, `root_unique`, `other_root`: `σ_υ β λ² − (σ_υ (1 + β) + κ_υ) λ + σ_υ`
  has exactly one root `λ ∈ (0, 1)`; the other root is `1/(βλ) > 1`.
* `peg_nkpc_iff` (**the factorisation**): with `w_t = p_{H,t} − λ p_{H,t−1}`, the Phillips curve
  holds iff `w_t = βλ E_t w_{t+1} − λ κ_υ ψ_{ya} a_t`, a forward equation with `0 < βλ < 1`.
* `peg_iff`, `peg_exists`, `peg_unique`: the bounded equilibrium exists and is unique:
  `p_{H,t} = λ p_{H,t−1} + θ a_t`, `θ = −λ κ_υ ψ_{ya}/(1 − βλρ_a)`,
  `ỹ_t = −σ_υ⁻¹ p_{H,t} − ψ_{ya} a_t`, `y_t = −σ_υ⁻¹ p_{H,t}`, `s_t = −p_{H,t}`,
  `i_t = ρ + (σ_υ (1 − ρ_a) ψ_{ya} − ψ_{ra}) a_t` (`= ρ = i*` under (38), `peg_rate_38`).
* `pegP_closed`: `p_{H,t} = λ^{t+1} p_{H,−1} + θ ∑_{k ≤ t} λ^{t−k} a_k`; `peg_irf_signs`: after a
  positive shock (`p_{H,−1} = 0`, `ψ_{ya} > 0`) the domestic price level falls and output and
  the terms of trade rise at every date.
-/

namespace Gali.OpenEconomy.Ex8_2

open Filter Topology
open Gali.OpenEconomy.TaylorRule (Structural AU msvDen msvLambda msvPsiY msvPsiPi msvDen_pos
  isAR1_smul boundedProc_smul msv_structural msv_unique schurStable_AU_iff)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model -/

/-- Galí (2015), Ex. 8.2, p. 259: the lagged domestic price level `p_{H,t−1}`, with
`p_{H,−1}` given. -/
def lagP (pm1 : Ω → ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => pm1
  | t + 1 => p t

/-- Galí (2015), Ex. 8.2, p. 260: the natural rate `r^n_t = ρ − ψ_{ra} a_t`. -/
def natRate (ρ ψra : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (fun _ => ρ) - ψra • a t

/-- Galí (2015), Ex. 8.2, pp. 259–260, with eqs. (14) and (27), p. 230 and p. 235: the
non-policy block: the Phillips curve, the dynamic IS equation, `y_t = ỹ_t + ψ_{ya} a_t`,
`s_t = σ_υ y_t` (`y* = 0`), `π_{H,t} = p_{H,t} − p_{H,t−1}` and `e_t = s_t + p_{H,t}`
(`p* = 0`). -/
def Block (β σv κv ρ ψra ψya : ℝ) (a : ℕ → Ω → ℝ) (pm1 : Ω → ℝ)
    (ygap piH i y s pH e : ℕ → Ω → ℝ) : Prop :=
  ∀ t, piH t = β • 𝔼.E t (piH (t + 1)) + κv • ygap t ∧
    ygap t = 𝔼.E t (ygap (t + 1)) - σv⁻¹ • (i t - 𝔼.E t (piH (t + 1)) - natRate ρ ψra a t) ∧
    y t = ygap t + ψya • a t ∧ s t = σv • y t ∧ piH t = pH t - lagP pm1 pH t ∧
    e t = s t + pH t

/-- Galí (2015), Ex. 8.2(a), p. 260: an equilibrium under the rule `i_t = ρ + φ_π π_{H,t}`. -/
def TaylorEq (β σv κv ρ φπ ψra ψya : ℝ) (a : ℕ → Ω → ℝ) (pm1 : Ω → ℝ)
    (ygap piH i y s pH e : ℕ → Ω → ℝ) : Prop :=
  Block 𝔼 β σv κv ρ ψra ψya a pm1 ygap piH i y s pH e ∧ ∀ t, i t = (fun _ => ρ) + φπ • piH t

/-- Galí (2015), Ex. 8.2(b), p. 260: an equilibrium under the exchange-rate peg `e_t = 0`. -/
def PegEq (β σv κv ρ ψra ψya : ℝ) (a : ℕ → Ω → ℝ) (pm1 : Ω → ℝ)
    (ygap piH i y s pH e : ℕ → Ω → ℝ) : Prop :=
  Block 𝔼 β σv κv ρ ψra ψya a pm1 ygap piH i y s pH e ∧ ∀ t, e t = 0

/-- Galí (2015), Ex. 8.2: an initial condition known at date 0 is known at every date. -/
theorem known_pm1 {pm1 : Ω → ℝ} (h : 𝔼.E 0 pm1 = pm1) (t : ℕ) : 𝔼.E t pm1 = pm1 := by
  have := 𝔼.known (Nat.zero_le t) pm1
  rwa [h] at this

/-- Galí (2015), Ex. 8.2: `π_{H,t} = p_{H,t} − p_{H,t−1}` for all `t` iff
`p_{H,t} = p_{H,−1} + ∑_{k ≤ t} π_{H,k}`. -/
theorem cumsum_iff {pm1 : Ω → ℝ} {piH pH : ℕ → Ω → ℝ} :
    (∀ t, piH t = pH t - lagP pm1 pH t) ↔
      pH = fun t => pm1 + ∑ k ∈ Finset.range (t + 1), piH k := by
  constructor
  · intro h
    funext t
    induction t with
    | zero =>
      have := h 0
      simp only [lagP] at this
      simp [this]
    | succ t ih =>
      have := h (t + 1)
      simp only [lagP] at this
      rw [Finset.sum_range_succ, ← add_assoc, ← ih, this]
      abel
  · intro h t
    rw [h]
    cases t with
    | zero => simp [lagP]
    | succ t =>
      simp only [lagP]
      rw [Finset.sum_range_succ]
      abel

/-! ### Part (a): the Chapter 3 system

The structural equations, the matrices `A_υ`, `B_υ` (`TaylorRule.Structural`,
`TaylorRule.AU`, `TaylorRule.BU`, `TaylorRule.omegaU`), Bullard–Mitra
(`TaylorRule.schurStable_AU_iff`) and the MSV solution (`TaylorRule.msvDen`,
`TaylorRule.msvLambda`, `TaylorRule.msvPsiY`, `TaylorRule.msvPsiPi`,
`TaylorRule.msv_structural`, `TaylorRule.msv_unique`) are imported from `TaylorRule`; here
`σ ↦ σ_υ`, `κ ↦ κ_υ`, `φ_y = 0`. -/

/-! ### Part (a): the technology shock under `i_t = ρ + φ_π π_{H,t}` -/

/-- Galí (2015), Ex. 8.2(a): the composite shock `u_t = r^n_t − ρ = −ψ_{ra} a_t`. -/
def shock (ψra : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (-ψra) • a t

/-- Galí (2015), Ex. 8.2(a): under `i_t = ρ + φ_π π_{H,t}` the Phillips curve and the dynamic
IS equation hold iff the structural equations hold with `φ_y = 0` and `u_t = −ψ_{ra} a_t`. -/
theorem nk_iff_structural {β σv κv ρ φπ ψra : ℝ} (hσ : σv ≠ 0)
    {a ygap piH i : ℕ → Ω → ℝ} (hrule : ∀ t, i t = (fun _ => ρ) + φπ • piH t) :
    (∀ t, piH t = β • 𝔼.E t (piH (t + 1)) + κv • ygap t ∧
      ygap t = 𝔼.E t (ygap (t + 1)) - σv⁻¹ • (i t - 𝔼.E t (piH (t + 1)) - natRate ρ ψra a t))
      ↔ Structural 𝔼 β σv κv φπ 0 (shock ψra a) ygap piH := by
  have hinv : σv * σv⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · intro h t
    refine ⟨?_, (h t).1⟩
    funext ω
    have e := congrFun (h t).2 ω
    have r := congrFun (hrule t) ω
    simp only [shock, natRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ⊢
    linear_combination σv * e - r -
      (i t ω - 𝔼.E t (piH (t + 1)) ω - (ρ - ψra * a t ω)) * hinv
  · intro h t
    refine ⟨(h t).2, ?_⟩
    funext ω
    have e := congrFun (h t).1 ω
    have r := congrFun (hrule t) ω
    simp only [shock, natRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ⊢
    linear_combination σv⁻¹ * e + σv⁻¹ * r - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- **Determinacy** (Galí 2015, eq. (41), p. 240, with `φ_y = 0`; Ex. 8.2(a)): the system has at
most one bounded adapted solution for every forcing process iff `φ_π > 1`. -/
theorem taylor_determinate_iff [Nonempty Ω] {β σv κv φπ : ℝ} (hσ : 0 < σv) (hκ : 0 < κv)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) :
    𝔼.Determinate (AU β σv κv φπ 0) ↔ 1 < φπ := by
  rw [𝔼.determinate_iff, schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ le_rfl]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Ex. 8.2(a)** (Galí 2015, p. 260): under `φ_π > 1`, a tuple with bounded adapted output gap
and domestic inflation is an equilibrium iff `ỹ_t = (1 − βρ_a) Λ_a u_t`, `π_{H,t} = κ_υ Λ_a u_t`
(`u_t = −ψ_{ra} a_t`), `i_t = ρ + φ_π π_{H,t}`, `y_t = ỹ_t + ψ_{ya} a_t`, `s_t = σ_υ y_t`,
`p_{H,t} = p_{H,−1} + ∑_{k ≤ t} π_{H,k}` and `e_t = s_t + p_{H,t}`. -/
theorem taylor_iff {β σv κv ρ φπ ψra ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : 1 < φπ) (hρ1 : ρa < 1) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) {pm1 : Ω → ℝ} {ygap piH i y s pH e : ℕ → Ω → ℝ}
    (hyA : 𝔼.Adapted ygap) (hpA : 𝔼.Adapted piH) (hyB : BoundedProc ygap)
    (hpB : BoundedProc piH) :
    TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap piH i y s pH e ↔
      ygap = (fun t => msvPsiY β σv κv φπ 0 ρa • shock ψra a t) ∧
        piH = (fun t => msvPsiPi β σv κv φπ 0 ρa • shock ψra a t) ∧
        i = (fun t => (fun _ => ρ) + φπ • piH t) ∧ y = (fun t => ygap t + ψya • a t) ∧
        s = (fun t => σv • y t) ∧
        pH = (fun t => pm1 + ∑ k ∈ Finset.range (t + 1), piH k) ∧
        e = (fun t => s t + pH t) := by
  have h28 : 0 < κv * (φπ - 1) + (1 - β) * 0 := by nlinarith
  have hu : 𝔼.IsAR1 ρa (shock ψra a) := isAR1_smul 𝔼 ha (-ψra)
  have hub : BoundedProc (shock ψra a) := boundedProc_smul hab (-ψra)
  constructor
  · rintro ⟨hB, hrule⟩
    have hs := (nk_iff_structural 𝔼 hσ.ne' hrule).1 fun t => ⟨(hB t).1, (hB t).2.1⟩
    obtain ⟨h1, h2⟩ := msv_unique 𝔼 hσ hκ hβ0 hβ1 (by linarith) le_rfl hρ1 h28 hu hub hs
      hyA hpA hyB hpB
    exact ⟨h1, h2, funext hrule, funext fun t => (hB t).2.2.1,
      funext fun t => (hB t).2.2.2.1, cumsum_iff.1 fun t => (hB t).2.2.2.2.1,
      funext fun t => (hB t).2.2.2.2.2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    have hrule : ∀ t, i t = (fun _ => ρ) + φπ • piH t := fun t => by rw [h3]
    have hD := (msvDen_pos hσ hκ hβ0 hβ1 le_rfl hρ1 h28).ne'
    have hs : Structural 𝔼 β σv κv φπ 0 (shock ψra a) ygap piH := by
      rw [h1, h2]; exact msv_structural 𝔼 hD hu
    have hnk := (nk_iff_structural 𝔼 hσ.ne' hrule).2 hs
    have hcum := cumsum_iff.2 h6
    exact ⟨fun t => ⟨(hnk t).1, (hnk t).2, by rw [h4], by rw [h5], hcum t, by rw [h7]⟩, hrule⟩

/-- **Ex. 8.2(a), existence** (Galí 2015, p. 260): under `φ_π > 1` the MSV tuple is an
equilibrium with bounded adapted output gap and domestic inflation. -/
theorem taylor_exists {β σv κv ρ φπ ψra ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : 1 < φπ) (hρ1 : ρa < 1) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) (pm1 : Ω → ℝ) :
    ∃ ygap piH i y s pH e, TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap piH i y s pH e ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted piH ∧ BoundedProc ygap ∧ BoundedProc piH := by
  have hu : 𝔼.IsAR1 ρa (shock ψra a) := isAR1_smul 𝔼 ha (-ψra)
  have hub : BoundedProc (shock ψra a) := boundedProc_smul hab (-ψra)
  set ygap : ℕ → Ω → ℝ := fun t => msvPsiY β σv κv φπ 0 ρa • shock ψra a t
  set piH : ℕ → Ω → ℝ := fun t => msvPsiPi β σv κv φπ 0 ρa • shock ψra a t
  set y : ℕ → Ω → ℝ := fun t => ygap t + ψya • a t
  set s : ℕ → Ω → ℝ := fun t => σv • y t
  set pH : ℕ → Ω → ℝ := fun t => pm1 + ∑ k ∈ Finset.range (t + 1), piH k
  have hyA : 𝔼.Adapted ygap := (isAR1_smul 𝔼 hu _).1
  have hpA : 𝔼.Adapted piH := (isAR1_smul 𝔼 hu _).1
  have hyB : BoundedProc ygap := boundedProc_smul hub _
  have hpB : BoundedProc piH := boundedProc_smul hub _
  refine ⟨ygap, piH, fun t => (fun _ => ρ) + φπ • piH t, y, s, pH, fun t => s t + pH t,
    (taylor_iff 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 ha hab hyA hpA hyB hpB).2
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hyA, hpA, hyB, hpB⟩

/-- **Ex. 8.2(a), uniqueness** (Galí 2015, p. 260): under `φ_π > 1` two equilibria with bounded
adapted output gap and domestic inflation, driven by the same technology and initial price
level, coincide in every variable. -/
theorem taylor_unique {β σv κv ρ φπ ψra ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : 1 < φπ) (hρ1 : ρa < 1) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) {pm1 : Ω → ℝ}
    {ygap piH i y s pH e ygap' piH' i' y' s' pH' e' : ℕ → Ω → ℝ}
    (h : TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap piH i y s pH e)
    (h' : TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap' piH' i' y' s' pH' e')
    (hyA : 𝔼.Adapted ygap) (hpA : 𝔼.Adapted piH) (hyB : BoundedProc ygap)
    (hpB : BoundedProc piH) (hyA' : 𝔼.Adapted ygap') (hpA' : 𝔼.Adapted piH')
    (hyB' : BoundedProc ygap') (hpB' : BoundedProc piH') :
    ygap = ygap' ∧ piH = piH' ∧ i = i' ∧ y = y' ∧ s = s' ∧ pH = pH' ∧ e = e' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ :=
    (taylor_iff 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 ha hab hyA hpA hyB hpB).1 h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ :=
    (taylor_iff 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 ha hab hyA' hpA' hyB' hpB').1 h'
  have e1 : ygap = ygap' := a1.trans b1.symm
  have e2 : piH = piH' := a2.trans b2.symm
  have e3 : i = i' := by rw [a3, b3, e2]
  have e4 : y = y' := by rw [a4, b4, e1]
  have e5 : s = s' := by rw [a5, b5, e4]
  have e6 : pH = pH' := by rw [a6, b6, e2]
  exact ⟨e1, e2, e3, e4, e5, e6, by rw [a7, b7, e5, e6]⟩

/-- Galí (2015), p. 241, with `φ_y = 0`: `Λ_a msvDen = 1` when the denominator is nonzero. -/
theorem lambda_mul_den {β σv κv φπ ρa : ℝ} (hD : msvDen β σv κv φπ 0 ρa ≠ 0) :
    msvLambda β σv κv φπ 0 ρa * ((1 - β * ρa) * σv * (1 - ρa) + κv * (φπ - ρa)) = 1 := by
  have : (1 - β * ρa) * σv * (1 - ρa) + κv * (φπ - ρa) = msvDen β σv κv φπ 0 ρa := by
    unfold msvDen; ring
  rw [this]
  unfold msvLambda
  field_simp

/-- **Ex. 8.2(a), closed forms under (38)** (Galí 2015, p. 260, with `ψ_{ra} = σ_υ (1 − ρ_a)
ψ_{ya}`): in the equilibrium of `taylor_iff`, with `Λ_a = msvLambda`,
`ỹ_t = −σ_υ (1 − ρ_a)(1 − βρ_a) Λ_a ψ_{ya} a_t`, `π_{H,t} = −σ_υ κ_υ (1 − ρ_a) Λ_a ψ_{ya} a_t`,
`y_t = κ_υ (φ_π − ρ_a) Λ_a ψ_{ya} a_t`, `s_t = σ_υ κ_υ (φ_π − ρ_a) Λ_a ψ_{ya} a_t`,
`i_t = ρ − φ_π σ_υ κ_υ (1 − ρ_a) Λ_a ψ_{ya} a_t` and
`e_t = p_{H,−1} + σ_υ κ_υ Λ_a ψ_{ya} [(φ_π − ρ_a) a_t − (1 − ρ_a) ∑_{k ≤ t} a_k]`. -/
theorem taylor_closed_forms_38 {β σv κv ρ φπ ψra ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 1 < φπ) (hρ1 : ρa < 1)
    (h38 : ψra = σv * (1 - ρa) * ψya) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) {pm1 : Ω → ℝ} {ygap piH i y s pH e : ℕ → Ω → ℝ}
    (h : TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap piH i y s pH e)
    (hyA : 𝔼.Adapted ygap) (hpA : 𝔼.Adapted piH) (hyB : BoundedProc ygap)
    (hpB : BoundedProc piH) (t : ℕ) (ω : Ω) :
    ygap t ω = -(σv * (1 - ρa) * (1 - β * ρa) * msvLambda β σv κv φπ 0 ρa * ψya) * a t ω ∧
      piH t ω = -(σv * κv * (1 - ρa) * msvLambda β σv κv φπ 0 ρa * ψya) * a t ω ∧
      y t ω = κv * (φπ - ρa) * msvLambda β σv κv φπ 0 ρa * ψya * a t ω ∧
      s t ω = σv * κv * (φπ - ρa) * msvLambda β σv κv φπ 0 ρa * ψya * a t ω ∧
      i t ω = ρ - φπ * σv * κv * (1 - ρa) * msvLambda β σv κv φπ 0 ρa * ψya * a t ω ∧
      e t ω = pm1 ω + σv * κv * msvLambda β σv κv φπ 0 ρa * ψya *
        ((φπ - ρa) * a t ω - (1 - ρa) * ∑ k ∈ Finset.range (t + 1), a k ω) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    (taylor_iff 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 ha hab hyA hpA hyB hpB).1 h
  have h28 : 0 < κv * (φπ - 1) + (1 - β) * 0 := by nlinarith
  have hΛ := lambda_mul_den (msvDen_pos hσ hκ hβ0 hβ1 le_rfl hρ1 h28).ne'
  set Λ := msvLambda β σv κv φπ 0 ρa with hΛdef
  have hyg : ∀ t ω, ygap t ω = -(σv * (1 - ρa) * (1 - β * ρa) * Λ * ψya) * a t ω := by
    intro t ω
    rw [h1]
    simp only [shock, Pi.smul_apply, smul_eq_mul, msvPsiY, h38, ← hΛdef]
    ring
  have hpi : ∀ t ω, piH t ω = -(σv * κv * (1 - ρa) * Λ * ψya) * a t ω := by
    intro t ω
    rw [h2]
    simp only [shock, Pi.smul_apply, smul_eq_mul, msvPsiPi, h38, ← hΛdef]
    ring
  have hy : ∀ t ω, y t ω = κv * (φπ - ρa) * Λ * ψya * a t ω := by
    intro t ω
    rw [h4]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hyg]
    linear_combination (-(ψya * a t ω)) * hΛ
  have hs : ∀ t ω, s t ω = σv * κv * (φπ - ρa) * Λ * ψya * a t ω := by
    intro t ω
    rw [h5]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hy]; ring
  have hsum : ∀ t ω, ∑ k ∈ Finset.range (t + 1), piH k ω =
      -(σv * κv * (1 - ρa) * Λ * ψya) * ∑ k ∈ Finset.range (t + 1), a k ω := by
    intro t ω
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => hpi k ω
  refine ⟨hyg t ω, hpi t ω, hy t ω, hs t ω, ?_, ?_⟩
  · rw [h3]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hpi]; ring
  · rw [h7]
    simp only [Pi.add_apply]
    rw [h6]
    simp only [Pi.add_apply, Finset.sum_apply]
    rw [hs, hsum]; ring

/-- **Ex. 8.2(a), signs** (Galí 2015, p. 260): with `ψ_{ya} > 0`, `ρ_a < 1` and `φ_π > 1`, the
coefficients on `a_t` are negative for the output gap and domestic inflation and positive for
output and the terms of trade (a real depreciation). -/
theorem taylor_signs_38 {β σv κv φπ ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : 1 < φπ) (hρ1 : ρa < 1) (hψ : 0 < ψya) :
    -(σv * (1 - ρa) * (1 - β * ρa) * msvLambda β σv κv φπ 0 ρa * ψya) < 0 ∧
      -(σv * κv * (1 - ρa) * msvLambda β σv κv φπ 0 ρa * ψya) < 0 ∧
      0 < κv * (φπ - ρa) * msvLambda β σv κv φπ 0 ρa * ψya ∧
      0 < σv * κv * (φπ - ρa) * msvLambda β σv κv φπ 0 ρa * ψya := by
  have h28 : 0 < κv * (φπ - 1) + (1 - β) * 0 := by nlinarith
  have hΛ : 0 < msvLambda β σv κv φπ 0 ρa :=
    one_div_pos.2 (msvDen_pos hσ hκ hβ0 hβ1 le_rfl hρ1 h28)
  have h1 : 0 < 1 - ρa := by linarith
  have h2 : 0 < 1 - β * ρa := by nlinarith
  have h3 : 0 < φπ - ρa := by linarith
  refine ⟨?_, ?_, by positivity, by positivity⟩
  · have : 0 < σv * (1 - ρa) * (1 - β * ρa) * msvLambda β σv κv φπ 0 ρa * ψya := by positivity
    linarith
  · have : 0 < σv * κv * (1 - ρa) * msvLambda β σv κv φπ 0 ρa * ψya := by positivity
    linarith

/-- **Ex. 8.2(a), impulse response of the exchange rate** (Galí 2015, p. 260): for a one-time
shock `a_t = ρ_aᵗ a_0`, `e_t = p_{H,−1} + σ_υ κ_υ Λ_a ψ_{ya} (φ_π ρ_aᵗ − 1) a_0` and
`p_{H,t} = p_{H,−1} − σ_υ κ_υ Λ_a ψ_{ya} (1 − ρ_a^{t+1}) a_0`. -/
theorem taylor_irf_38 {β σv κv ρ φπ ψra ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 1 < φπ) (hρ1 : ρa < 1)
    (h38 : ψra = σv * (1 - ρa) * ψya) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) {a0 : Ω → ℝ} (hirf : ∀ k ω, a k ω = ρa ^ k * a0 ω) {pm1 : Ω → ℝ}
    {ygap piH i y s pH e : ℕ → Ω → ℝ}
    (h : TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap piH i y s pH e)
    (hyA : 𝔼.Adapted ygap) (hpA : 𝔼.Adapted piH) (hyB : BoundedProc ygap)
    (hpB : BoundedProc piH) (t : ℕ) (ω : Ω) :
    e t ω = pm1 ω + σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * (φπ * ρa ^ t - 1) * a0 ω ∧
      pH t ω = pm1 ω - σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * (1 - ρa ^ (t + 1)) * a0 ω := by
  have hcf := taylor_closed_forms_38 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 h38 ha hab h hyA hpA hyB hpB t ω
  have hgeo : (1 - ρa) * ∑ k ∈ Finset.range (t + 1), a k ω = (1 - ρa ^ (t + 1)) * a0 ω := by
    rw [← mul_neg_geom_sum, mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hirf k ω
  obtain ⟨-, hpi, -, hs, -, he⟩ := hcf
  obtain ⟨-, -, -, -, -, h6, h7⟩ :=
    (taylor_iff 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 ha hab hyA hpA hyB hpB).1 h
  refine ⟨?_, ?_⟩
  · rw [he, hgeo, hirf, pow_succ]; ring
  · have hp := (taylor_closed_forms_38 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 h38 ha hab h hyA hpA hyB hpB)
    have hsum : ∑ k ∈ Finset.range (t + 1), piH k ω =
        -(σv * κv * msvLambda β σv κv φπ 0 ρa * ψya) *
          ((1 - ρa) * ∑ k ∈ Finset.range (t + 1), a k ω) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [(hp k ω).2.1]; ring
    rw [h6]
    simp only [Pi.add_apply, Finset.sum_apply]
    rw [hsum, hgeo]; ring

/-- **Ex. 8.2(a), long run** (Galí 2015, p. 260): after a one-time shock with `0 ≤ ρ_a < 1`, the
nominal exchange rate converges to `p_{H,−1} − σ_υ κ_υ Λ_a ψ_{ya} a_0`: a permanent nominal
appreciation, after the depreciation on impact `e_0 − p_{H,−1} = σ_υ κ_υ Λ_a ψ_{ya}(φ_π − 1) a_0`
(positive for `a_0 > 0`, `ψ_{ya} > 0`). -/
theorem taylor_irf_tendsto {β σv κv ρ φπ ψra ψya ρa : ℝ} (hσ : 0 < σv) (hκ : 0 < κv)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 1 < φπ) (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1)
    (h38 : ψra = σv * (1 - ρa) * ψya) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) {a0 : Ω → ℝ} (hirf : ∀ k ω, a k ω = ρa ^ k * a0 ω) {pm1 : Ω → ℝ}
    {ygap piH i y s pH e : ℕ → Ω → ℝ}
    (h : TaylorEq 𝔼 β σv κv ρ φπ ψra ψya a pm1 ygap piH i y s pH e)
    (hyA : 𝔼.Adapted ygap) (hpA : 𝔼.Adapted piH) (hyB : BoundedProc ygap)
    (hpB : BoundedProc piH) (ω : Ω) :
    e 0 ω - pm1 ω = σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * (φπ - 1) * a0 ω ∧
      Tendsto (fun t => e t ω) atTop
        (𝓝 (pm1 ω - σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * a0 ω)) := by
  have hirfE := fun t => (taylor_irf_38 𝔼 hσ hκ hβ0 hβ1 hφ hρ1 h38 ha hab hirf h hyA hpA hyB
    hpB t ω).1
  refine ⟨by rw [hirfE 0]; ring, ?_⟩
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have hlim : Tendsto (fun t => pm1 ω + σv * κv * msvLambda β σv κv φπ 0 ρa * ψya *
      (φπ * ρa ^ t - 1) * a0 ω) atTop
      (𝓝 (pm1 ω + σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * (φπ * 0 - 1) * a0 ω)) := by
    refine tendsto_const_nhds.add (((tendsto_const_nhds.mul
      ((tendsto_const_nhds.mul hpow).sub tendsto_const_nhds))).mul tendsto_const_nhds)
  rw [show pm1 ω + σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * (φπ * 0 - 1) * a0 ω =
    pm1 ω - σv * κv * msvLambda β σv κv φπ 0 ρa * ψya * a0 ω by ring] at hlim
  exact hlim.congr fun t => (hirfE t).symm

/-! ### Part (b): the peg — the characteristic polynomial -/

/-- Galí (2015), Ex. 8.2(b): the characteristic polynomial of the peg dynamics,
`Q(λ) = σ_υ β λ² − (σ_υ (1 + β) + κ_υ) λ + σ_υ` (`σ_υ` times
`βλ² − (1 + β + κ_υ/σ_υ) λ + 1`). -/
def charQ (β σv κv r : ℝ) : ℝ := σv * β * r ^ 2 - (σv * (1 + β) + κv) * r + σv

/-- Galí (2015), Ex. 8.2(b): `Q(0) = σ_υ > 0` and `Q(1) = −κ_υ < 0`, so `Q` has a root in
`(0, 1)`. -/
theorem exists_root {β σv κv : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) :
    ∃ r, 0 < r ∧ r < 1 ∧ charQ β σv κv r = 0 := by
  have hc : Continuous (charQ β σv κv) := by unfold charQ; fun_prop
  have h := intermediate_value_Ioo' (zero_le_one' ℝ) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (charQ β σv κv 1) (charQ β σv κv 0) by
      unfold charQ; constructor <;> nlinarith)
  obtain ⟨r, ⟨h0, h1⟩, hr⟩ := h
  exact ⟨r, h0, h1, hr⟩

/-- Galí (2015), Ex. 8.2(b): for `0 < β < 1`, `σ_υ, κ_υ > 0`, `Q` has at most one root below 1;
in particular the root in `(0, 1)` is unique. -/
theorem root_unique {β σv κv r r' : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hr1 : r < 1) (hr'1 : r' < 1)
    (hQ : charQ β σv κv r = 0) (hQ' : charQ β σv κv r' = 0) : r = r' := by
  by_contra hne
  have hsub : r - r' ≠ 0 := sub_ne_zero.2 hne
  have hsum : σv * β * (r + r') = σv * (1 + β) + κv := by
    apply mul_right_cancel₀ hsub
    unfold charQ at hQ hQ'
    linear_combination hQ - hQ'
  have h1 : σv * β * (r + r') < σv * β * 2 :=
    mul_lt_mul_of_pos_left (by linarith) (mul_pos hσ hβ0)
  nlinarith

/-- Galí (2015), Ex. 8.2(b): if `λ ∈ (0, 1)` is a root, the other root is `1/(βλ) > 1`: the
peg dynamics have exactly one stable and one unstable root (saddle path). -/
theorem other_root {β σv κv r : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hQ : charQ β σv κv r = 0) : charQ β σv κv (1 / (β * r)) = 0 ∧ 1 < 1 / (β * r) := by
  have hbr : 0 < β * r := mul_pos hβ0 hr0
  refine ⟨?_, ?_⟩
  · unfold charQ at hQ ⊢
    field_simp
    linear_combination hQ
  · rw [lt_div_iff₀ hbr]; nlinarith

/-! ### Part (b): the factorisation -/

/-- **The factorisation** (Galí 2015, Ex. 8.2(b), pointwise algebra): at a root `λ ≠ 0` of `Q`,
and given the peg relation `σ_υ ỹ_t + p_{H,t} + σ_υ ψ_{ya} a_t = 0`, the Phillips curve
`p_{H,t} − p_{H,t−1} = β (E_t p_{H,t+1} − p_{H,t}) + κ_υ ỹ_t` holds iff
`p_{H,t} − λ p_{H,t−1} = βλ (E_t p_{H,t+1} − λ p_{H,t}) − λ κ_υ ψ_{ya} a_t`. -/
theorem peg_nkpc_iff {β σv κv ψya r : ℝ} (hσ : σv ≠ 0) (hr : r ≠ 0)
    (hQ : charQ β σv κv r = 0) {p l Ep yg at' : ℝ} (hpeg : σv * yg + p + σv * ψya * at' = 0) :
    p - l = β * (Ep - p) + κv * yg ↔
      p - r * l = β * r * (Ep - r * p) + -(r * κv * ψya) * at' := by
  unfold charQ at hQ
  constructor
  · intro hN
    apply mul_left_cancel₀ hσ
    linear_combination (r * σv) * hN + (r * κv) * hpeg + p * hQ
  · intro hG
    apply mul_left_cancel₀ (mul_ne_zero hr hσ)
    linear_combination σv * hG - (r * κv) * hpeg - p * hQ

/-- Galí (2015), Ex. 8.2(b): the quasi-difference `w_t = p_{H,t} − λ p_{H,t−1}`. -/
def wseq (r : ℝ) (pm1 : Ω → ℝ) (pH : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := pH t - r • lagP pm1 pH t

/-- Galí (2015), Ex. 8.2(b): the forcing `−λ κ_υ ψ_{ya} a_t` of the forward equation for `w`. -/
def pegShock (r κv ψya : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (-(r * κv * ψya)) • a t

/-- Galí (2015), Ex. 8.2(b): the response coefficient `θ = (1 − βλρ_a)⁻¹ (−λ κ_υ ψ_{ya})`. -/
noncomputable def pegTheta (β κv ψya ρa r : ℝ) : ℝ := (1 - β * r * ρa)⁻¹ * (-(r * κv * ψya))

/-- Galí (2015), Ex. 8.2(b): `θ = −λ κ_υ ψ_{ya}/(1 − βλρ_a)`. -/
theorem pegTheta_eq (β κv ψya ρa r : ℝ) :
    pegTheta β κv ψya ρa r = -(r * κv * ψya) / (1 - β * r * ρa) := by
  unfold pegTheta; ring

/-- Galí (2015), Ex. 8.2(b): the candidate domestic price level, `p_{H,0} = λ p_{H,−1} + θ a_0`,
`p_{H,t+1} = λ p_{H,t} + θ a_{t+1}`. -/
def pegP (r θ : ℝ) (pm1 : Ω → ℝ) (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => r • pm1 + θ • a 0
  | t + 1 => r • pegP r θ pm1 a t + θ • a (t + 1)

/-- Galí (2015), Ex. 8.2(b): `p_{H,t} = λ p_{H,t−1} + θ a_t` for all `t` iff `p_H = pegP`. -/
theorem pegP_iff {r θ : ℝ} {pm1 : Ω → ℝ} {a pH : ℕ → Ω → ℝ} :
    (∀ t, pH t = r • lagP pm1 pH t + θ • a t) ↔ pH = pegP r θ pm1 a := by
  constructor
  · intro h
    funext t
    induction t with
    | zero => rw [h 0]; rfl
    | succ t ih => rw [h (t + 1)]; simp only [lagP, pegP]; rw [ih]
  · rintro rfl t
    cases t <;> rfl

/-- Galí (2015), Ex. 8.2(b) (**closed form**): `p_{H,t} = λ^{t+1} p_{H,−1} + θ ∑_{k ≤ t}
λ^{t−k} a_k`. -/
theorem pegP_closed (r θ : ℝ) (pm1 : Ω → ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    pegP r θ pm1 a t ω =
      r ^ (t + 1) * pm1 ω + θ * ∑ k ∈ Finset.range (t + 1), r ^ (t - k) * a k ω := by
  induction t with
  | zero => simp [pegP]
  | succ t ih =>
    have hrec : pegP r θ pm1 a (t + 1) ω = r * pegP r θ pm1 a t ω + θ * a (t + 1) ω := rfl
    have hs : ∑ k ∈ Finset.range (t + 1), r ^ (t + 1 - k) * a k ω =
        r * ∑ k ∈ Finset.range (t + 1), r ^ (t - k) * a k ω := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have : t + 1 - k = t - k + 1 := by have := Finset.mem_range.1 hk; omega
      rw [this, pow_succ]; ring
    rw [hrec, ih, Finset.sum_range_succ (fun k => r ^ (t + 1 - k) * a k ω) (t + 1), hs,
      Nat.sub_self, pow_zero]
    ring

/-- Galí (2015), Ex. 8.2(b): `pegP` is adapted when `p_{H,−1}` is known at date 0. -/
theorem pegP_adapted {r θ ρa : ℝ} {pm1 : Ω → ℝ} {a : ℕ → Ω → ℝ} (hpm : 𝔼.E 0 pm1 = pm1)
    (ha : 𝔼.IsAR1 ρa a) : 𝔼.Adapted (pegP r θ pm1 a) := by
  intro t
  induction t with
  | zero =>
    change 𝔼.E 0 (r • pm1 + θ • a 0) = r • pm1 + θ • a 0
    rw [map_add, map_smul, map_smul, hpm, ha.1 0]
  | succ t ih =>
    change 𝔼.E (t + 1) (r • pegP r θ pm1 a t + θ • a (t + 1)) = _
    rw [map_add, map_smul, map_smul, ha.1 (t + 1)]
    have := 𝔼.known (Nat.le_succ t) (pegP r θ pm1 a t)
    rw [ih] at this
    rw [this]
    rfl

/-- Galí (2015), Ex. 8.2(b): `pegP` is bounded for `0 < λ < 1` and bounded `p_{H,−1}`, `a`. -/
theorem pegP_bounded {r θ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {pm1 : Ω → ℝ} {a : ℕ → Ω → ℝ}
    (hpmb : ∃ M, ∀ ω, |pm1 ω| ≤ M) (hab : BoundedProc a) : BoundedProc (pegP r θ pm1 a) := by
  obtain ⟨M0, hM0⟩ := hpmb
  obtain ⟨Ma, hMa⟩ := hab
  set K := |θ| * |Ma| / (1 - r) with hK
  have h1r : 0 < 1 - r := by linarith
  have hKeq : (1 - r) * K = |θ| * |Ma| := by rw [hK]; field_simp
  have hKnn : 0 ≤ K := by positivity
  have hθa : ∀ t ω, |θ * a t ω| ≤ |θ| * |Ma| := fun t ω => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hMa t ω).trans (le_abs_self Ma)) (abs_nonneg θ)
  refine ⟨|M0| + K, fun t ω => ?_⟩
  induction t generalizing ω with
  | zero =>
    change |r * pm1 ω + θ * a 0 ω| ≤ _
    have h1 : |r * pm1 ω| ≤ r * |M0| := by
      rw [abs_mul, abs_of_pos hr0]
      exact mul_le_mul_of_nonneg_left ((hM0 ω).trans (le_abs_self M0)) hr0.le
    have h2 := hθa 0 ω
    have h3 : r * |M0| ≤ |M0| := by nlinarith [abs_nonneg M0]
    have h4 : |θ| * |Ma| ≤ K := by nlinarith
    linarith [abs_add_le (r * pm1 ω) (θ * a 0 ω)]
  | succ t ih =>
    change |r * pegP r θ pm1 a t ω + θ * a (t + 1) ω| ≤ _
    have h1 : |r * pegP r θ pm1 a t ω| ≤ r * (|M0| + K) := by
      rw [abs_mul, abs_of_pos hr0]
      exact mul_le_mul_of_nonneg_left (ih ω) hr0.le
    have h2 := hθa (t + 1) ω
    have h3 : r * (|M0| + K) + |θ| * |Ma| ≤ |M0| + K := by nlinarith [abs_nonneg M0]
    linarith [abs_add_le (r * pegP r θ pm1 a t ω) (θ * a (t + 1) ω)]

/-! ### Part (b): existence and uniqueness of the bounded equilibrium under the peg -/

/-- Galí (2015), Ex. 8.2(b): the response coefficient `θ` makes `w_t = θ a_t` the forward
solution: `θ a_t = βλ E_t(θ a_{t+1}) − λ κ_υ ψ_{ya} a_t`. -/
theorem theta_solves {β κv ψya ρa r : ℝ} (hden : 1 - β * r * ρa ≠ 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (t : ℕ) :
    pegTheta β κv ψya ρa r • a t =
      (β * r) • 𝔼.E t (pegTheta β κv ψya ρa r • a (t + 1)) + pegShock r κv ψya a t := by
  have h := 𝔼.forward_ar1_solves hden (isAR1_smul 𝔼 ha (-(r * κv * ψya))) t
  simp only [smul_smul] at h
  unfold pegTheta pegShock
  exact h

/-- **Ex. 8.2(b)** (Galí 2015, p. 260): under the peg, with `λ` the root of `Q` in `(0, 1)`,
a tuple with bounded adapted domestic price level is an equilibrium iff
`p_{H,t} = λ p_{H,t−1} + θ a_t`, `ỹ_t = −σ_υ⁻¹ p_{H,t} − ψ_{ya} a_t`, `y_t = −σ_υ⁻¹ p_{H,t}`,
`s_t = −p_{H,t}`, `e_t = 0`, `π_{H,t} = p_{H,t} − p_{H,t−1}` and
`i_t = ρ + (σ_υ (1 − ρ_a) ψ_{ya} − ψ_{ra}) a_t`. -/
theorem peg_iff {β σv κv ρ ψra ψya ρa r : ℝ} (hσ : 0 < σv) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ1 : ρa < 1) (hr0 : 0 < r) (hr1 : r < 1) (hQ : charQ β σv κv r = 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hab : BoundedProc a) {pm1 : Ω → ℝ}
    (hpmb : ∃ M, ∀ ω, |pm1 ω| ≤ M) {ygap piH i y s pH e : ℕ → Ω → ℝ}
    (hpA : 𝔼.Adapted pH) (hpB : BoundedProc pH) :
    PegEq 𝔼 β σv κv ρ ψra ψya a pm1 ygap piH i y s pH e ↔
      (∀ t, pH t = r • lagP pm1 pH t + pegTheta β κv ψya ρa r • a t) ∧
        ygap = (fun t => (-σv⁻¹) • pH t - ψya • a t) ∧ y = (fun t => (-σv⁻¹) • pH t) ∧
        s = (fun t => -pH t) ∧ e = (fun _ => 0) ∧ piH = (fun t => pH t - lagP pm1 pH t) ∧
        i = (fun t => (fun _ => ρ) + (σv * (1 - ρa) * ψya - ψra) • a t) := by
  have hinv : σv * σv⁻¹ = 1 := mul_inv_cancel₀ hσ.ne'
  have hbr : 0 < β * r := mul_pos hβ0 hr0
  have hbr1 : β * r < 1 := by nlinarith
  have hden : 1 - β * r * ρa ≠ 0 := by
    have : β * r * ρa < 1 := by
      rcases le_or_gt ρa 0 with h | h
      · nlinarith
      · nlinarith
    linarith
  -- expectations of the lagged and future price level
  have hEpi : ∀ t, 𝔼.E t (pH (t + 1) - lagP pm1 pH (t + 1)) = 𝔼.E t (pH (t + 1)) - pH t := by
    intro t
    change 𝔼.E t (pH (t + 1) - pH t) = _
    rw [map_sub, hpA t]
  -- the forward equation for `w` and the explicit solution
  have hfwd : ∀ (ygap' : ℕ → Ω → ℝ),
      (∀ t ω, σv * ygap' t ω + pH t ω + σv * ψya * a t ω = 0) →
      ((∀ t, (pH t - lagP pm1 pH t) =
          β • 𝔼.E t (pH (t + 1) - lagP pm1 pH (t + 1)) + κv • ygap' t) ↔
        ∀ t, wseq r pm1 pH t =
          (β * r) • 𝔼.E t (wseq r pm1 pH (t + 1)) + pegShock r κv ψya a t) := by
    intro ygap' hpeg
    have hEw : ∀ t, 𝔼.E t (wseq r pm1 pH (t + 1)) = 𝔼.E t (pH (t + 1)) - r • pH t := by
      intro t
      change 𝔼.E t (pH (t + 1) - r • pH t) = _
      rw [map_sub, map_smul, hpA t]
    constructor
    · intro hN t
      funext ω
      have e := congrFun (hN t) ω
      rw [hEpi] at e
      rw [hEw]
      simp only [wseq, pegShock, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
      exact (peg_nkpc_iff hσ.ne' hr0.ne' hQ (hpeg t ω)).1 e
    · intro hG t
      funext ω
      have e := congrFun (hG t) ω
      rw [hEw] at e
      rw [hEpi]
      simp only [wseq, pegShock, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
      exact (peg_nkpc_iff hσ.ne' hr0.ne' hQ (hpeg t ω)).2 e
  -- boundedness of `w` and of the candidate `θ a`
  have hlagB : BoundedProc (lagP pm1 pH) := by
    obtain ⟨M0, hM0⟩ := hpmb
    obtain ⟨Mp, hMp⟩ := hpB
    refine ⟨|M0| + |Mp|, fun t ω => ?_⟩
    cases t with
    | zero =>
      change |pm1 ω| ≤ _
      linarith [hM0 ω, le_abs_self M0, abs_nonneg Mp]
    | succ t =>
      change |pH t ω| ≤ _
      linarith [hMp t ω, le_abs_self Mp, abs_nonneg M0]
  have hwB : BoundedProc (wseq r pm1 pH) := by
    obtain ⟨M1, hM1⟩ := hpB
    obtain ⟨M2, hM2⟩ := hlagB
    refine ⟨M1 + |r| * M2, fun t ω => ?_⟩
    simp only [wseq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h2 : |r * lagP pm1 pH t ω| ≤ |r| * M2 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM2 t ω) (abs_nonneg r)
    linarith [abs_sub (pH t ω) (r * lagP pm1 pH t ω), hM1 t ω]
  have hbrabs : |β * r| < 1 := by rw [abs_of_pos hbr]; exact hbr1
  have hθsol := theta_solves 𝔼 (κv := κv) (ψya := ψya) hden ha
  -- the DIS equation, given the peg relation for `ỹ`
  have hdis : ∀ (ygap' i' : ℕ → Ω → ℝ), (∀ t, ygap' t = (-σv⁻¹) • pH t - ψya • a t) →
      ((∀ t, ygap' t = 𝔼.E t (ygap' (t + 1)) -
          σv⁻¹ • (i' t - 𝔼.E t (pH (t + 1) - lagP pm1 pH (t + 1)) - natRate ρ ψra a t)) ↔
        i' = fun t => (fun _ => ρ) + (σv * (1 - ρa) * ψya - ψra) • a t) := by
    intro ygap' i' hyg
    have hEy : ∀ t, 𝔼.E t (ygap' (t + 1)) = (-σv⁻¹) • 𝔼.E t (pH (t + 1)) - (ψya * ρa) • a t := by
      intro t
      rw [hyg (t + 1), map_sub, map_smul, map_smul, ha.2 t, smul_smul]
    constructor
    · intro hD
      funext t ω
      have e := congrFun (hD t) ω
      rw [hEy, hEpi, hyg t] at e
      simp only [natRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
      linear_combination σv * e -
        (i' t ω - (𝔼.E t (pH (t + 1)) ω - pH t ω) - (ρ - ψra * a t ω) - pH t ω +
          𝔼.E t (pH (t + 1)) ω) * hinv
    · intro hi t
      funext ω
      rw [hEy, hEpi, hyg t, hi]
      simp only [natRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (ψya * a t ω * (1 - ρa)) * hinv
  constructor
  · rintro ⟨hB, hpeg⟩
    have hyg : ∀ t, ygap t = (-σv⁻¹) • pH t - ψya • a t := by
      intro t
      obtain ⟨-, -, h3, h4, -, h6⟩ := hB t
      funext ω
      have e3 := congrFun h3 ω
      have e4 := congrFun h4 ω
      have e6 := congrFun h6 ω
      have e0 := congrFun (hpeg t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply]
        at e3 e4 e6 e0 ⊢
      linear_combination -σv⁻¹ * (e6 - e0) - σv⁻¹ * e4 - σv⁻¹ * σv * e3 -
        (ygap t ω + ψya * a t ω) * hinv
    have hpegrel : ∀ t ω, σv * ygap t ω + pH t ω + σv * ψya * a t ω = 0 := by
      intro t ω
      rw [hyg t]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(pH t ω)) * hinv
    have hpiH : ∀ t, piH t = pH t - lagP pm1 pH t := fun t => (hB t).2.2.2.2.1
    have hN : ∀ t, (pH t - lagP pm1 pH t) =
        β • 𝔼.E t (pH (t + 1) - lagP pm1 pH (t + 1)) + κv • ygap t := by
      intro t
      have := (hB t).1
      rw [hpiH t, hpiH (t + 1)] at this
      exact this
    have hw := (hfwd ygap hpegrel).1 hN
    have hweq := 𝔼.forward_unique hbrabs hw hθsol hwB (boundedProc_smul hab _)
    have hrec : ∀ t, pH t = r • lagP pm1 pH t + pegTheta β κv ψya ρa r • a t := by
      intro t
      have := congrFun hweq t
      simp only [wseq] at this
      rw [← this]; abel
    refine ⟨hrec, funext hyg, funext fun t => ?_, funext fun t => ?_, funext hpeg,
      funext hpiH, (hdis ygap i hyg).1 fun t => ?_⟩
    · obtain ⟨-, -, h3, -, -, -⟩ := hB t
      rw [h3, hyg t]; abel
    · obtain ⟨-, -, -, -, -, h6⟩ := hB t
      rw [hpeg t] at h6
      funext ω
      have := congrFun h6 ω
      simp only [Pi.zero_apply, Pi.add_apply] at this
      simp only [Pi.neg_apply]
      linarith
    · have := (hB t).2.1
      rw [hpiH (t + 1)] at this
      exact this
  · rintro ⟨hrec, hyg, hy, hs, he, hpiH, hi⟩
    have hyg' : ∀ t, ygap t = (-σv⁻¹) • pH t - ψya • a t := fun t => by rw [hyg]
    have hpegrel : ∀ t ω, σv * ygap t ω + pH t ω + σv * ψya * a t ω = 0 := by
      intro t ω
      rw [hyg' t]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(pH t ω)) * hinv
    have hweq : wseq r pm1 pH = fun t => pegTheta β κv ψya ρa r • a t := by
      funext t
      simp only [wseq]
      rw [hrec t]; abel
    have hw : ∀ t, wseq r pm1 pH t =
        (β * r) • 𝔼.E t (wseq r pm1 pH (t + 1)) + pegShock r κv ψya a t := by
      rw [hweq]; exact hθsol
    have hN := (hfwd ygap hpegrel).2 hw
    have hD := (hdis ygap i hyg').2 hi
    refine ⟨fun t => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun t => by rw [he]⟩
    · rw [hpiH]; exact hN t
    · rw [hpiH]; exact hD t
    · rw [hy, hyg]; simp only [sub_add_cancel]
    · rw [hs, hy]
      funext ω
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (pH t ω) * hinv
    · rw [hpiH]
    · rw [he, hs]; simp

/-- **Ex. 8.2(b), existence** (Galí 2015, p. 260): under the peg there is an equilibrium with a
bounded adapted domestic price level, `p_H = pegP` (for `λ` the root of `Q` in `(0, 1)`). -/
theorem peg_exists {β σv κv ρ ψra ψya ρa r : ℝ} (hσ : 0 < σv) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ1 : ρa < 1) (hr0 : 0 < r) (hr1 : r < 1) (hQ : charQ β σv κv r = 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hab : BoundedProc a) {pm1 : Ω → ℝ} (hpm : 𝔼.E 0 pm1 = pm1)
    (hpmb : ∃ M, ∀ ω, |pm1 ω| ≤ M) :
    ∃ ygap piH i y s pH e, PegEq 𝔼 β σv κv ρ ψra ψya a pm1 ygap piH i y s pH e ∧
      pH = pegP r (pegTheta β κv ψya ρa r) pm1 a ∧ 𝔼.Adapted pH ∧ BoundedProc pH := by
  set pH := pegP r (pegTheta β κv ψya ρa r) pm1 a
  have hpA : 𝔼.Adapted pH := pegP_adapted 𝔼 hpm ha
  have hpB : BoundedProc pH := pegP_bounded hr0 hr1 hpmb hab
  refine ⟨fun t => (-σv⁻¹) • pH t - ψya • a t, fun t => pH t - lagP pm1 pH t,
    fun t => (fun _ => ρ) + (σv * (1 - ρa) * ψya - ψra) • a t, fun t => (-σv⁻¹) • pH t,
    fun t => -pH t, pH, fun _ => 0, ?_, rfl, hpA, hpB⟩
  exact (peg_iff 𝔼 hσ hβ0 hβ1 hρ1 hr0 hr1 hQ ha hab hpmb hpA hpB).2
    ⟨pegP_iff.2 rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Ex. 8.2(b), uniqueness** (Galí 2015, p. 260): under the peg, every equilibrium with a
bounded adapted domestic price level has `p_H = pegP` and coincides with the one of
`peg_exists` in every variable. -/
theorem peg_unique {β σv κv ρ ψra ψya ρa r : ℝ} (hσ : 0 < σv) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ1 : ρa < 1) (hr0 : 0 < r) (hr1 : r < 1) (hQ : charQ β σv κv r = 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hab : BoundedProc a) {pm1 : Ω → ℝ}
    (hpmb : ∃ M, ∀ ω, |pm1 ω| ≤ M)
    {ygap piH i y s pH e ygap' piH' i' y' s' pH' e' : ℕ → Ω → ℝ}
    (h : PegEq 𝔼 β σv κv ρ ψra ψya a pm1 ygap piH i y s pH e)
    (h' : PegEq 𝔼 β σv κv ρ ψra ψya a pm1 ygap' piH' i' y' s' pH' e')
    (hpA : 𝔼.Adapted pH) (hpB : BoundedProc pH) (hpA' : 𝔼.Adapted pH')
    (hpB' : BoundedProc pH') :
    pH = pegP r (pegTheta β κv ψya ρa r) pm1 a ∧
      ygap = ygap' ∧ piH = piH' ∧ i = i' ∧ y = y' ∧ s = s' ∧ pH = pH' ∧ e = e' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ :=
    (peg_iff 𝔼 hσ hβ0 hβ1 hρ1 hr0 hr1 hQ ha hab hpmb hpA hpB).1 h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ :=
    (peg_iff 𝔼 hσ hβ0 hβ1 hρ1 hr0 hr1 hQ ha hab hpmb hpA' hpB').1 h'
  have hp : pH = pegP r (pegTheta β κv ψya ρa r) pm1 a := pegP_iff.1 a1
  have hp' : pH' = pegP r (pegTheta β κv ψya ρa r) pm1 a := pegP_iff.1 b1
  have e6 : pH = pH' := hp.trans hp'.symm
  refine ⟨hp, by rw [a2, b2, e6], by rw [a6, b6, e6], by rw [a7, b7], by rw [a3, b3, e6],
    by rw [a4, b4, e6], e6, by rw [a5, b5]⟩

/-- Galí (2015), Ex. 8.2(b), with (38) (`ψ_{ra} = σ_υ (1 − ρ_a) ψ_{ya}`): under the peg the
nominal rate is constant, `i_t = ρ = i*` — consistent with uncovered interest parity (18). -/
theorem peg_rate_38 {σv ρ ψra ψya ρa : ℝ} (h38 : ψra = σv * (1 - ρa) * ψya)
    (a : ℕ → Ω → ℝ) :
    (fun t => (fun _ => ρ) + (σv * (1 - ρa) * ψya - ψra) • a t) = fun _ => fun _ => ρ := by
  funext t
  rw [h38, sub_self, zero_smul, add_zero]

/-- Galí (2015), Ex. 8.2(b): for `ψ_{ya} > 0` (and `κ_υ > 0`, `0 < λ < 1`) the response
coefficient `θ` is negative: a positive technology shock lowers the domestic price level. -/
theorem pegTheta_neg {β κv ψya ρa r : ℝ} (hκ : 0 < κv) (hψ : 0 < ψya) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ1 : ρa < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    pegTheta β κv ψya ρa r < 0 := by
  rw [pegTheta_eq]
  have hbr : β * r < 1 := by nlinarith
  have hden : 0 < 1 - β * r * ρa := by
    rcases le_or_gt ρa 0 with h | h
    · nlinarith [mul_pos hβ0 hr0]
    · nlinarith [mul_pos hβ0 hr0]
  exact div_neg_of_neg_of_pos (by have := mul_pos (mul_pos hr0 hκ) hψ; linarith) hden

/-- **Ex. 8.2(b), impulse responses** (Galí 2015, p. 260): after a one-time positive shock
(`a_t = ρ_aᵗ a_0`, `a_0 > 0`, `0 ≤ ρ_a < 1`) from `p_{H,−1} = 0`, with `ψ_{ya} > 0`, the domestic
price level is `p_{H,t} = θ (∑_{k ≤ t} λ^{t−k} ρ_aᵏ) a_0 < 0` at every date, so output
`y_t = −σ_υ⁻¹ p_{H,t}` and the terms of trade `s_t = −p_{H,t}` rise at every date. -/
theorem peg_irf_signs {β σv κv ψya ρa r : ℝ} (hσ : 0 < σv) (hκ : 0 < κv) (hψ : 0 < ψya)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hr0 : 0 < r) (hr1 : r < 1)
    {a : ℕ → Ω → ℝ} {a0 : Ω → ℝ} (hirf : ∀ k ω, a k ω = ρa ^ k * a0 ω) (t : ℕ) (ω : Ω)
    (ha0 : 0 < a0 ω) :
    pegP r (pegTheta β κv ψya ρa r) (fun _ => 0) a t ω =
        pegTheta β κv ψya ρa r * (∑ k ∈ Finset.range (t + 1), r ^ (t - k) * ρa ^ k) * a0 ω ∧
      pegP r (pegTheta β κv ψya ρa r) (fun _ => 0) a t ω < 0 ∧
      0 < -σv⁻¹ * pegP r (pegTheta β κv ψya ρa r) (fun _ => 0) a t ω ∧
      0 < -pegP r (pegTheta β κv ψya ρa r) (fun _ => 0) a t ω := by
  have hθ := pegTheta_neg hκ hψ hβ0 hβ1 hρ1 hr0 hr1
  have hform : pegP r (pegTheta β κv ψya ρa r) (fun _ => 0) a t ω =
      pegTheta β κv ψya ρa r * (∑ k ∈ Finset.range (t + 1), r ^ (t - k) * ρa ^ k) * a0 ω := by
    rw [pegP_closed, mul_zero, zero_add, mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [hirf]; ring
  have hsum : 0 < ∑ k ∈ Finset.range (t + 1), r ^ (t - k) * ρa ^ k := by
    have hle : r ^ (t - 0) * ρa ^ 0 ≤ ∑ k ∈ Finset.range (t + 1), r ^ (t - k) * ρa ^ k :=
      Finset.single_le_sum (f := fun k => r ^ (t - k) * ρa ^ k)
        (fun k _ => by positivity) (Finset.mem_range.2 (Nat.succ_pos t))
    have : 0 < r ^ (t - 0) * ρa ^ 0 := by positivity
    linarith
  have hneg : pegP r (pegTheta β κv ψya ρa r) (fun _ => 0) a t ω < 0 := by
    rw [hform]
    have : 0 < -pegTheta β κv ψya ρa r * (∑ k ∈ Finset.range (t + 1), r ^ (t - k) * ρa ^ k) *
        a0 ω := by
      have : 0 < -pegTheta β κv ψya ρa r := by linarith
      positivity
    linarith
  refine ⟨hform, hneg, ?_, by linarith⟩
  have : 0 < σv⁻¹ := inv_pos.2 hσ
  nlinarith

end Gali.OpenEconomy.Ex8_2
