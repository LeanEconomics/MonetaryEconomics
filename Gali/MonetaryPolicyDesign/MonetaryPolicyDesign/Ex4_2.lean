/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.Ex4_1
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Exercise 4.2: inflation targeting with noisy data

Galí (2015), Chapter 4, Exercise 4.2, p. 121. The economy is
`π_t = β E_t π_{t+1} + κ ỹ_t` and `ỹ_t = −σ⁻¹ (i_t − E_t π_{t+1} − r^n_t) + E_t ỹ_{t+1}`,
with natural rate `r^n_t = ρ + r̂_t`, `r̂_t` an AR(1) with persistence `ρ_r ∈ [0, 1)`.
Inflation is measured with an i.i.d. error, `π^o_t = π_t + ξ_t` (`E_t ξ_{t+1} = 0`), and the
central bank sets `i_t = ρ + φ_π π^o_t`.

## Main results

* **(a)** `ex4_2a_equilibrium_iff`: for `φ_π > 1` the unique equilibrium with bounded adapted
  output gap and inflation is the MSV solution
  `π_t = a_r r̂_t + a_ξ ξ_t`, `ỹ_t = b_r r̂_t + b_ξ ξ_t` with
  `a_r = κ/D_r`, `b_r = (1 − βρ_r)/D_r`, `D_r = (1 − βρ_r) σ (1 − ρ_r) + κ (φ_π − ρ_r)`,
  `a_ξ = −φ_π κ/(σ + κ φ_π)`, `b_ξ = −φ_π/(σ + κ φ_π)`. `ex4_2a_exists` gives existence
  whenever the denominators are nonzero, and `ex4_2a_not_unique` gives multiplicity for
  `φ_π ≤ 1`. `ex4_2a_rate` gives the nominal rate.
* **(b)** `ex4_2b_coefficients`, `ex4_2b_limits`: as `φ_π → ∞`, `π_t → −ξ_t`, measured
  inflation `π^o_t → 0`, `ỹ_t → −ξ_t/κ` and `i_t → r^n_t + (σ/κ) ξ_t`.
* **(c)** With a covariance form `B` (`bilin_quad`, `stationary_var_ar1`,
  `ex4_2c_variance`), `var π_t = a_r² var r̂ + a_ξ² var ξ =: V(φ_π)`. Over the determinacy
  region `φ_π > 1`, `V` is minimised as follows (with `h(φ) = φ (D_r(φ)/(σ + κφ))³`):
  `ex4_2c_interior`: if `σ var ξ · h(1) < κ var r̂`, there is a unique `φ* > 1` with
  `σ var ξ · h(φ*) = κ var r̂`, and it is the unique minimiser;
  `ex4_2c_corner`: otherwise `V` is strictly increasing on `[1, ∞)` and has no minimiser on
  `φ_π > 1`; `ex4_2c_no_noise`: without noise `V` is strictly decreasing and tends to `0`;
  `ex4_2c_iid`: for `ρ_r = 0`, `φ* = κ var r̂/(σ var ξ)` in closed form.
-/

namespace Gali.MonetaryPolicyDesign.Ex4_2

open Filter Topology Gali.MonetaryPolicyDesign.Ex4_1

/-! ### The MSV coefficients -/

/-- Galí (2015), Exercise 4.2(a), p. 121: the denominator
`D_r(φ_π) = (1 − βρ_r) σ (1 − ρ_r) + κ (φ_π − ρ_r)`. -/
def Dr (β σ κ ρr φ : ℝ) : ℝ := (1 - β * ρr) * σ * (1 - ρr) + κ * (φ - ρr)

/-- Galí (2015), Exercise 4.2(a): the inflation response to the natural rate, `κ/D_r`. -/
noncomputable def aR (β σ κ ρr φ : ℝ) : ℝ := κ / Dr β σ κ ρr φ

/-- Galí (2015), Exercise 4.2(a): the output-gap response to the natural rate,
`(1 − βρ_r)/D_r`. -/
noncomputable def bR (β σ κ ρr φ : ℝ) : ℝ := (1 - β * ρr) / Dr β σ κ ρr φ

/-- Galí (2015), Exercise 4.2(a): the inflation response to the measurement error,
`−φ_π κ/(σ + κ φ_π)`. -/
noncomputable def aXi (σ κ φ : ℝ) : ℝ := -(φ * κ) / (σ + κ * φ)

/-- Galí (2015), Exercise 4.2(a): the output-gap response to the measurement error,
`−φ_π/(σ + κ φ_π)`. -/
noncomputable def bXi (σ κ φ : ℝ) : ℝ := -φ / (σ + κ * φ)

/-- Galí (2015), Exercise 4.2: `D_r(φ) = c + κ φ` with `c = (1 − βρ_r) σ (1 − ρ_r) − κ ρ_r`. -/
theorem Dr_eq (β σ κ ρr φ : ℝ) :
    Dr β σ κ ρr φ = ((1 - β * ρr) * σ * (1 - ρr) - κ * ρr) + κ * φ := by
  unfold Dr
  ring

/-- Galí (2015), Exercise 4.2: `D_r(φ) > 0` for `φ ≥ 1`. -/
theorem Dr_pos {β σ κ ρr φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ1 : ρr < 1) (hφ : 1 ≤ φ) : 0 < Dr β σ κ ρr φ := by
  unfold Dr
  have h1 : 0 < 1 - β * ρr := by nlinarith
  have h2 : 0 < (1 - β * ρr) * σ * (1 - ρr) := by
    have := mul_pos h1 hσ
    exact mul_pos this (by linarith)
  nlinarith

/-- Galí (2015), Exercise 4.2: `D_r(φ) ≤ σ + κ φ`. -/
theorem Dr_le {β σ κ ρr φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) : Dr β σ κ ρr φ ≤ σ + κ * φ := by
  unfold Dr
  have h0 : 0 ≤ ρr * (1 + β - β * ρr) := mul_nonneg hρ0 (by nlinarith)
  have h1 : (1 - β * ρr) * (1 - ρr) ≤ 1 := by nlinarith
  nlinarith

/-! ### The model -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 4.2, p. 121: the natural rate `r^n_t = ρ + r̂_t`. -/
def natRate (ρ : ℝ) (rhat : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => (fun _ => ρ) + rhat t

/-- Galí (2015), Exercise 4.2, p. 121: the rule `i_t = ρ + φ_π π^o_t`,
with measured inflation `π^o_t = π_t + ξ_t`. -/
def Rule (ρ φ : ℝ) (i infl ξ : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φ • (infl t + ξ t)

/-- Galí (2015), Exercise 4.2, p. 121: an equilibrium: the NKPC, the DIS equation and the
rule. -/
def Equilibrium (β σ κ ρ φ : ℝ) (rhat ξ ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl (natRate ρ rhat) ∧ Rule ρ φ i infl ξ

/-- Galí (2015), Exercise 4.2: the composite forcing `u_t = r̂_t − φ_π ξ_t`. -/
def forcingU (φ : ℝ) (rhat ξ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => rhat t - φ • ξ t

/-- Galí (2015), Exercise 4.2, p. 121: an equilibrium is a solution of the structural
system with `φ_y = 0` and forcing `r̂_t − φ_π ξ_t`, together with the rule. -/
theorem equilibrium_iff {β σ κ ρ φ : ℝ} (hσ : σ ≠ 0) {rhat ξ ygap infl i : ℕ → Ω → ℝ} :
    Equilibrium 𝔼 β σ κ ρ φ rhat ξ ygap infl i ↔
      Structural 𝔼 β σ κ φ 0 (forcingU φ rhat ξ) ygap infl ∧ Rule ρ φ i infl ξ := by
  constructor
  · rintro ⟨hp, hd, hr⟩
    have hr' : ∀ t, i t = natRate ρ rhat t + φ • infl t + (0 : ℝ) • ygap t
        - forcingU φ rhat ξ t := fun t => by
      rw [hr t]
      funext ω
      simp only [natRate, forcingU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact ⟨(equilibrium_iff_structural 𝔼 hσ hr').mp ⟨hp, hd⟩, hr⟩
  · rintro ⟨hs, hr⟩
    have hr' : ∀ t, i t = natRate ρ rhat t + φ • infl t + (0 : ℝ) • ygap t
        - forcingU φ rhat ξ t := fun t => by
      rw [hr t]
      funext ω
      simp only [natRate, forcingU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨hp, hd⟩ := (equilibrium_iff_structural 𝔼 hσ hr').mpr hs
    exact ⟨hp, hd, hr⟩

/-- Galí (2015), Exercise 4.2(a): the MSV processes solve the structural system, for an
AR(1) natural rate and a serially uncorrelated measurement error. -/
theorem msv_structural {β σ κ ρr φ : ℝ} (hD : Dr β σ κ ρr φ ≠ 0) (hS : σ + κ * φ ≠ 0)
    {rhat ξ : ℕ → Ω → ℝ} (hr : 𝔼.IsAR1 ρr rhat) (hξ : 𝔼.IsAR1 0 ξ) :
    Structural 𝔼 β σ κ φ 0 (forcingU φ rhat ξ)
      (fun t => bR β σ κ ρr φ • rhat t + bXi σ κ φ • ξ t)
      (fun t => aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t) := by
  have c1 : (σ + 0) * bR β σ κ ρr φ + φ * aR β σ κ ρr φ
      = σ * (bR β σ κ ρr φ * ρr) + aR β σ κ ρr φ * ρr + 1 := by
    unfold bR aR
    field_simp
    unfold Dr
    ring
  have hinv : (σ + κ * φ) * (σ + κ * φ)⁻¹ = 1 := mul_inv_cancel₀ hS
  have c2 : (σ + 0) * bXi σ κ φ + φ * aXi σ κ φ = -φ := by
    unfold bXi aXi
    linear_combination (-φ) * hinv
  have c3 : aR β σ κ ρr φ = β * (aR β σ κ ρr φ * ρr) + κ * bR β σ κ ρr φ := by
    unfold aR bR
    field_simp
    ring
  have c4 : aXi σ κ φ = κ * bXi σ κ φ := by
    unfold aXi bXi
    ring
  intro t
  simp only [map_add, map_smul, hr.2 t, hξ.2 t, smul_smul, zero_smul, smul_zero, add_zero]
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · simp only [forcingU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination rhat t ω * c1 + ξ t ω * c2
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination rhat t ω * c3 + ξ t ω * c4

/-- Galí (2015), Exercise 4.2(a): `a • x + b • z` built from adapted processes is
adapted. -/
theorem adapted_comb {x z : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hz : 𝔼.Adapted z) (a b : ℝ) :
    𝔼.Adapted (fun t => a • x t + b • z t) := fun t => by
  simp only [map_add, map_smul, hx t, hz t]

/-- Galí (2015), Exercise 4.2(a): `a • x + b • z` built from bounded processes is
bounded. -/
theorem bounded_comb {x z : ℕ → Ω → ℝ} (hx : BoundedProc x) (hz : BoundedProc z) (a b : ℝ) :
    BoundedProc (fun t => a • x t + b • z t) :=
  boundedProc_add (boundedProc_smul hx a) (boundedProc_smul hz b)

/-- **Exercise 4.2(a), existence** (Galí 2015, p. 121): whenever `D_r ≠ 0` and
`σ + κ φ_π ≠ 0`, the MSV processes together with the rule form an equilibrium with bounded
adapted output gap and inflation. -/
theorem ex4_2a_exists {β σ κ ρ ρr φ : ℝ} (hσ : σ ≠ 0) (hD : Dr β σ κ ρr φ ≠ 0)
    (hS : σ + κ * φ ≠ 0) {rhat ξ : ℕ → Ω → ℝ} (hr : 𝔼.IsAR1 ρr rhat) (hξ : 𝔼.IsAR1 0 ξ)
    (hrb : BoundedProc rhat) (hξb : BoundedProc ξ) :
    Equilibrium 𝔼 β σ κ ρ φ rhat ξ (fun t => bR β σ κ ρr φ • rhat t + bXi σ κ φ • ξ t)
      (fun t => aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t)
      (fun t => (fun _ => ρ) + φ • ((aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t) + ξ t)) ∧
    𝔼.Adapted (fun t => bR β σ κ ρr φ • rhat t + bXi σ κ φ • ξ t) ∧
    𝔼.Adapted (fun t => aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t) ∧
    BoundedProc (fun t => bR β σ κ ρr φ • rhat t + bXi σ κ φ • ξ t) ∧
    BoundedProc (fun t => aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t) :=
  ⟨(equilibrium_iff 𝔼 hσ).mpr ⟨msv_structural 𝔼 hD hS hr hξ, fun _ => rfl⟩,
    adapted_comb 𝔼 hr.1 hξ.1 _ _, adapted_comb 𝔼 hr.1 hξ.1 _ _,
    bounded_comb hrb hξb _ _, bounded_comb hrb hξb _ _⟩

/-- **Exercise 4.2(a), the unique equilibrium** (Galí 2015, p. 121): for `σ, κ > 0`,
`0 < β < 1`, `ρ_r < 1` (the book has `ρ_r ∈ [0, 1)`) and `φ_π > 1`, with bounded AR(1)
`r̂` and bounded serially uncorrelated `ξ`, a triple `(ỹ, π, i)` with bounded adapted
`ỹ, π` is an equilibrium iff it is the MSV solution `ỹ_t = b_r r̂_t + b_ξ ξ_t`,
`π_t = a_r r̂_t + a_ξ ξ_t`, with `i` given by the rule. -/
theorem ex4_2a_equilibrium_iff {β σ κ ρ ρr φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ1 : ρr < 1) (hφ : 1 < φ) {rhat ξ : ℕ → Ω → ℝ}
    (hr : 𝔼.IsAR1 ρr rhat) (hξ : 𝔼.IsAR1 0 ξ) (hrb : BoundedProc rhat) (hξb : BoundedProc ξ)
    {ygap infl i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl)
    (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ ρ φ rhat ξ ygap infl i ↔
      ygap = (fun t => bR β σ κ ρr φ • rhat t + bXi σ κ φ • ξ t) ∧
      infl = (fun t => aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t) ∧
      i = fun t => (fun _ => ρ) + φ • (infl t + ξ t) := by
  have hD := (Dr_pos hσ hκ hβ0 hβ1 hρ1 hφ.le).ne'
  have hS : σ + κ * φ ≠ 0 := by positivity
  rw [equilibrium_iff 𝔼 hσ.ne']
  constructor
  · rintro ⟨hs, hrule⟩
    obtain ⟨h1, h2⟩ := structural_unique 𝔼 hσ hκ hβ0 hβ1 (by linarith) le_rfl
      (by nlinarith) hs (msv_structural 𝔼 hD hS hr hξ) ha hb (adapted_comb 𝔼 hr.1 hξ.1 _ _)
      (adapted_comb 𝔼 hr.1 hξ.1 _ _) hba hbb (bounded_comb hrb hξb _ _)
      (bounded_comb hrb hξb _ _)
    exact ⟨h1, h2, funext hrule⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2]
    refine ⟨msv_structural 𝔼 hD hS hr hξ, fun t => ?_⟩
    rw [h3, h2]

/-- **Exercise 4.2(a), the nominal rate** (Galí 2015, p. 121): in the MSV equilibrium
`i_t = ρ + φ_π a_r r̂_t + (φ_π σ/(σ + κ φ_π)) ξ_t`. -/
theorem ex4_2a_rate {β σ κ ρ ρr φ : ℝ} (hS : σ + κ * φ ≠ 0) (rhat ξ : ℕ → Ω → ℝ) (t : ℕ) :
    (fun _ => ρ) + φ • ((aR β σ κ ρr φ • rhat t + aXi σ κ φ • ξ t) + ξ t)
      = (fun _ => ρ) + (φ * aR β σ κ ρr φ) • rhat t + (φ * σ / (σ + κ * φ)) • ξ t := by
  have hinv : (σ + κ * φ) * (σ + κ * φ)⁻¹ = 1 := mul_inv_cancel₀ hS
  have hc : φ * (aXi σ κ φ + 1) = φ * σ / (σ + κ * φ) := by
    unfold aXi
    linear_combination (-φ) * hinv
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination ξ t ω * hc

/-- **Exercise 4.2(a), multiplicity for `φ_π ≤ 1`** (Galí 2015, pp. 106, 121): if
`0 ≤ φ_π ≤ 1`, next to any equilibrium with bounded adapted output gap and inflation there
is a second one. -/
theorem ex4_2a_not_unique [Nonempty Ω] {β σ κ ρ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) {rhat ξ ygap infl i : ℕ → Ω → ℝ}
    (he : Equilibrium 𝔼 β σ κ ρ φ rhat ξ ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    ∃ ygap' infl' i', Equilibrium 𝔼 β σ κ ρ φ rhat ξ ygap' infl' i' ∧ 𝔼.Adapted ygap' ∧
      𝔼.Adapted infl' ∧ BoundedProc ygap' ∧ BoundedProc infl' ∧
      (ygap' ≠ ygap ∨ infl' ≠ infl) := by
  obtain ⟨hs, -⟩ := (equilibrium_iff 𝔼 hσ.ne').mp he
  obtain ⟨y', p', hs', ha', hb', hba', hbb', hne⟩ := structural_not_unique 𝔼 hσ hκ hβ0 hβ1
    hφ0 le_rfl (by nlinarith) hs ha hb hba hbb
  exact ⟨y', p', fun t => (fun _ => ρ) + φ • (p' t + ξ t),
    (equilibrium_iff 𝔼 hσ.ne').mpr ⟨hs', fun _ => rfl⟩, ha', hb', hba', hbb', hne⟩

/-! ### Exercise 4.2(b): `φ_π → ∞` -/

/-- Galí (2015), Exercise 4.2(b): `d/(c + κ φ) → 0` as `φ → ∞`, for `κ > 0`. -/
theorem tendsto_div_affine (d c : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun φ : ℝ => d / (c + κ * φ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_left _ c (Tendsto.const_mul_atTop hκ tendsto_id))

/-- **Exercise 4.2(b), coefficients** (Galí 2015, p. 121): as `φ_π → ∞`,
`a_r → 0`, `b_r → 0`, `a_ξ → −1`, `b_ξ → −1/κ`, `1 + a_ξ → 0` (measured inflation),
`φ_π a_r → 1` and `φ_π (1 + a_ξ) → σ/κ` (the nominal rate). -/
theorem ex4_2b_coefficients (β : ℝ) {σ κ : ℝ} (ρr : ℝ) (hκ : 0 < κ) :
    Tendsto (aR β σ κ ρr) atTop (𝓝 0) ∧ Tendsto (bR β σ κ ρr) atTop (𝓝 0) ∧
    Tendsto (aXi σ κ) atTop (𝓝 (-1)) ∧ Tendsto (bXi σ κ) atTop (𝓝 (-1 / κ)) ∧
    Tendsto (fun φ => 1 + aXi σ κ φ) atTop (𝓝 0) ∧
    Tendsto (fun φ => φ * aR β σ κ ρr φ) atTop (𝓝 1) ∧
    Tendsto (fun φ => φ * (1 + aXi σ κ φ)) atTop (𝓝 (σ / κ)) := by
  set c := (1 - β * ρr) * σ * (1 - ρr) - κ * ρr
  have hDr : ∀ φ, Dr β σ κ ρr φ = c + κ * φ := Dr_eq β σ κ ρr
  -- eventually both denominators are positive
  have hev : ∀ᶠ φ in atTop, 0 < c + κ * φ ∧ 0 < σ + κ * φ := by
    have h1 := (tendsto_atTop_add_const_left _ c
      (Tendsto.const_mul_atTop hκ tendsto_id)).eventually_gt_atTop 0
    have h2 := (tendsto_atTop_add_const_left _ σ
      (Tendsto.const_mul_atTop hκ tendsto_id)).eventually_gt_atTop 0
    exact h1.and h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := tendsto_div_affine κ c hκ
    refine this.congr fun φ => ?_
    simp only [aR, hDr]
  · have := tendsto_div_affine (1 - β * ρr) c hκ
    refine this.congr fun φ => ?_
    simp only [bR, hDr]
  · have := (tendsto_div_affine σ σ hκ).const_add (-1)
    rw [add_zero] at this
    refine this.congr' (hev.mono fun φ hφ => ?_)
    have hS := mul_inv_cancel₀ hφ.2.ne'
    simp only [aXi]
    linear_combination hS
  · have := (tendsto_div_affine (σ / κ) σ hκ).const_add (-1 / κ)
    rw [add_zero] at this
    refine this.congr' (hev.mono fun φ hφ => ?_)
    have hS := mul_inv_cancel₀ hφ.2.ne'
    have hk := mul_inv_cancel₀ hκ.ne'
    simp only [bXi]
    linear_combination κ⁻¹ * hS - φ * (σ + κ * φ)⁻¹ * hk
  · have := tendsto_div_affine σ σ hκ
    refine this.congr' (hev.mono fun φ hφ => ?_)
    have hS := mul_inv_cancel₀ hφ.2.ne'
    simp only [aXi]
    linear_combination hS
  · have := (tendsto_div_affine (-c) c hκ).const_add 1
    rw [add_zero] at this
    refine this.congr' (hev.mono fun φ hφ => ?_)
    have hD := mul_inv_cancel₀ hφ.1.ne'
    simp only [aR, hDr]
    linear_combination -hD
  · have := (tendsto_div_affine (-(σ ^ 2 / κ)) σ hκ).const_add (σ / κ)
    rw [add_zero] at this
    refine this.congr' (hev.mono fun φ hφ => ?_)
    have hS := mul_inv_cancel₀ hφ.2.ne'
    have hk := mul_inv_cancel₀ hκ.ne'
    simp only [aXi]
    linear_combination σ * φ * (σ + κ * φ)⁻¹ * hk - (σ * κ⁻¹ - φ) * hS

/-- **Exercise 4.2(b)** (Galí 2015, p. 121): along the MSV equilibria, as `φ_π → ∞`,
inflation tends to `−ξ_t`, measured inflation `π^o_t` to `0`, the output gap to `−ξ_t/κ`, and
the nominal rate to `r^n_t + (σ/κ) ξ_t`, at every date and state. -/
theorem ex4_2b_limits (β : ℝ) {σ κ : ℝ} (ρ ρr : ℝ) (hκ : 0 < κ) (rhat ξ : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    Tendsto (fun φ => aR β σ κ ρr φ * rhat t ω + aXi σ κ φ * ξ t ω) atTop
        (𝓝 (-ξ t ω)) ∧
    Tendsto (fun φ => aR β σ κ ρr φ * rhat t ω + aXi σ κ φ * ξ t ω + ξ t ω) atTop (𝓝 0) ∧
    Tendsto (fun φ => bR β σ κ ρr φ * rhat t ω + bXi σ κ φ * ξ t ω) atTop
        (𝓝 (-ξ t ω / κ)) ∧
    Tendsto (fun φ => ρ + φ * (aR β σ κ ρr φ * rhat t ω + aXi σ κ φ * ξ t ω + ξ t ω))
        atTop (𝓝 ((ρ + rhat t ω) + σ / κ * ξ t ω)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ex4_2b_coefficients β ρr hκ (σ := σ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (h1.mul_const (rhat t ω)).add (h3.mul_const (ξ t ω))
    convert this using 2
    ring
  · have := (h1.mul_const (rhat t ω)).add (h5.mul_const (ξ t ω))
    convert this using 2
    · ring
    · ring
  · have := (h2.mul_const (rhat t ω)).add (h4.mul_const (ξ t ω))
    convert this using 2
    ring
  · have := ((h6.mul_const (rhat t ω)).add (h7.mul_const (ξ t ω))).const_add ρ
    convert this using 2
    · ring
    · ring

/-! ### Exercise 4.2(c): the variance of inflation -/

/-- Galí (2015), Exercise 4.2(c): for a bilinear covariance form `B` and uncorrelated
`x, z`, `var (a x + b z) = a² var x + b² var z`. -/
theorem bilin_quad (B : LinearMap.BilinForm ℝ (Ω → ℝ)) (a b : ℝ) (x z : Ω → ℝ)
    (h1 : B x z = 0) (h2 : B z x = 0) :
    B (a • x + b • z) (a • x + b • z) = a ^ 2 * B x x + b ^ 2 * B z z := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2]
  ring

/-- Galí (2015), Exercise 4.2(c): the stationary variance of an AR(1),
`r̂_{t+1} = ρ_r r̂_t + ε_{t+1}` with `ε_{t+1}` uncorrelated with `r̂_t`: if
`var r̂_{t+1} = var r̂_t` then `var r̂_t = var ε/(1 − ρ_r²)`. -/
theorem stationary_var_ar1 (B : LinearMap.BilinForm ℝ (Ω → ℝ)) {ρr sε : ℝ}
    (hρ : ρr ^ 2 < 1) {rhat ε : ℕ → Ω → ℝ} {t : ℕ}
    (hlaw : rhat (t + 1) = ρr • rhat t + ε (t + 1)) (h1 : B (rhat t) (ε (t + 1)) = 0)
    (h2 : B (ε (t + 1)) (rhat t) = 0) (hε : B (ε (t + 1)) (ε (t + 1)) = sε)
    (hstat : B (rhat (t + 1)) (rhat (t + 1)) = B (rhat t) (rhat t)) :
    B (rhat t) (rhat t) = sε / (1 - ρr ^ 2) := by
  have h := bilin_quad B ρr 1 (rhat t) (ε (t + 1)) h1 h2
  rw [one_smul, ← hlaw, hstat, hε] at h
  have hne : 1 - ρr ^ 2 ≠ 0 := by linarith
  field_simp
  linarith

/-- Galí (2015), Exercise 4.2(c): the variance of inflation in the MSV equilibrium as a
function of `φ_π`, `V(φ_π) = a_r² var r̂ + a_ξ² var ξ`. -/
noncomputable def varInfl (β σ κ ρr sr sξ φ : ℝ) : ℝ :=
  aR β σ κ ρr φ ^ 2 * sr + aXi σ κ φ ^ 2 * sξ

/-- Galí (2015), Exercise 4.2(c): the variance of the output gap in the MSV equilibrium,
`b_r² var r̂ + b_ξ² var ξ`. -/
noncomputable def varGap (β σ κ ρr sr sξ φ : ℝ) : ℝ :=
  bR β σ κ ρr φ ^ 2 * sr + bXi σ κ φ ^ 2 * sξ

/-- **Exercise 4.2(c), variances** (Galí 2015, p. 121): in the unique equilibrium
(`φ_π > 1`), if `r̂_t` and `ξ_t` are uncorrelated under the covariance form `B`, then
`var π_t = V(φ_π)` and `var ỹ_t = b_r² var r̂_t + b_ξ² var ξ_t`. -/
theorem ex4_2c_variance (B : LinearMap.BilinForm ℝ (Ω → ℝ)) {β σ κ ρ ρr φ : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρr < 1)
    (hφ : 1 < φ) {rhat ξ : ℕ → Ω → ℝ} (hr : 𝔼.IsAR1 ρr rhat) (hξ : 𝔼.IsAR1 0 ξ)
    (hrb : BoundedProc rhat) (hξb : BoundedProc ξ) {ygap infl i : ℕ → Ω → ℝ}
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) (he : Equilibrium 𝔼 β σ κ ρ φ rhat ξ ygap infl i) (t : ℕ)
    (h1 : B (rhat t) (ξ t) = 0) (h2 : B (ξ t) (rhat t) = 0) :
    B (infl t) (infl t) = varInfl β σ κ ρr (B (rhat t) (rhat t)) (B (ξ t) (ξ t)) φ ∧
      B (ygap t) (ygap t) = varGap β σ κ ρr (B (rhat t) (rhat t)) (B (ξ t) (ξ t)) φ := by
  obtain ⟨hy, hp, -⟩ := (ex4_2a_equilibrium_iff 𝔼 hσ hκ hβ0 hβ1 hρ1 hφ hr hξ hrb hξb ha hb
    hba hbb).mp he
  rw [hy, hp]
  exact ⟨bilin_quad B _ _ _ _ h1 h2, bilin_quad B _ _ _ _ h1 h2⟩

/-- Galí (2015), Exercise 4.2(c): the function `h(φ) = φ (D_r(φ)/(σ + κ φ))³` whose level
set `σ var ξ · h(φ) = κ var r̂` is the first-order condition. -/
noncomputable def hcrit (β σ κ ρr φ : ℝ) : ℝ := φ * (Dr β σ κ ρr φ / (σ + κ * φ)) ^ 3

/-- Galí (2015), Exercise 4.2(c): the ratio `D_r(φ)/(σ + κ φ)` is positive and nondecreasing
on `φ ≥ 1`. -/
theorem ratio_mono {β σ κ ρr x y : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) (hx : 1 ≤ x) (hxy : x ≤ y) :
    0 < Dr β σ κ ρr x / (σ + κ * x) ∧
      Dr β σ κ ρr x / (σ + κ * x) ≤ Dr β σ κ ρr y / (σ + κ * y) := by
  have hDx := Dr_pos hσ hκ hβ0 hβ1 hρ1 hx
  have hSx : 0 < σ + κ * x := by nlinarith
  have hSy : 0 < σ + κ * y := by nlinarith
  have hle := Dr_le (φ := x) hσ hκ hβ0 hβ1 hρ0 hρ1
  have hDy : Dr β σ κ ρr y = Dr β σ κ ρr x + κ * (y - x) := by
    unfold Dr
    ring
  refine ⟨div_pos hDx hSx, ?_⟩
  rw [div_le_div_iff₀ hSx hSy, hDy]
  have : 0 ≤ κ * (y - x) := mul_nonneg hκ.le (by linarith)
  nlinarith

/-- Galí (2015), Exercise 4.2(c): `h` is strictly increasing on `[1, ∞)`. -/
theorem hcrit_strictMonoOn {β σ κ ρr : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) :
    StrictMonoOn (hcrit β σ κ ρr) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx' : (1 : ℝ) ≤ x := hx
  have hy' : (1 : ℝ) ≤ y := hy
  obtain ⟨hq0, hq⟩ := ratio_mono (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1 hx' hxy.le
  have hqy : 0 < Dr β σ κ ρr y / (σ + κ * y) := (ratio_mono (β := β) (ρr := ρr) hσ hκ hβ0
    hβ1 hρ0 hρ1 hy' le_rfl).1
  have h3 : (Dr β σ κ ρr x / (σ + κ * x)) ^ 3 ≤ (Dr β σ κ ρr y / (σ + κ * y)) ^ 3 :=
    pow_le_pow_left₀ hq0.le hq 3
  have h3y : 0 < (Dr β σ κ ρr y / (σ + κ * y)) ^ 3 := pow_pos hqy 3
  unfold hcrit
  calc x * (Dr β σ κ ρr x / (σ + κ * x)) ^ 3 ≤ x * (Dr β σ κ ρr y / (σ + κ * y)) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
    _ < y * (Dr β σ κ ρr y / (σ + κ * y)) ^ 3 := mul_lt_mul_of_pos_right hxy h3y

/-- Galí (2015), Exercise 4.2(c): `h(φ) ≥ φ h(1)` for `φ ≥ 1`, so `h` is unbounded. -/
theorem hcrit_ge {β σ κ ρr φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) (hφ : 1 ≤ φ) :
    φ * hcrit β σ κ ρr 1 ≤ hcrit β σ κ ρr φ := by
  obtain ⟨hq0, hq⟩ := ratio_mono (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1 le_rfl hφ
  unfold hcrit
  rw [one_mul]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0.le hq 3) (by linarith)

/-- Galí (2015), Exercise 4.2(c): `h(1) > 0`. -/
theorem hcrit_one_pos {β σ κ ρr : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) : 0 < hcrit β σ κ ρr 1 := by
  unfold hcrit
  rw [one_mul]
  exact pow_pos (ratio_mono (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1 le_rfl le_rfl).1 3

/-- Galí (2015), Exercise 4.2(c): `h` is continuous on `[1, ∞)`. -/
theorem hcrit_continuousOn {β σ κ ρr : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ContinuousOn (hcrit β σ κ ρr) (Set.Ici 1) := by
  unfold hcrit Dr
  apply ContinuousOn.mul continuousOn_id
  apply ContinuousOn.pow
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  have hx' : (1 : ℝ) ≤ x := hx
  have : 0 < σ + κ * x := by nlinarith
  exact this.ne'

/-- **The derivative of the inflation variance** (Galí 2015, Exercise 4.2(c)):
`V'(φ) = 2κ² (σ var ξ · h(φ) − κ var r̂)/D_r(φ)³` wherever `D_r(φ) ≠ 0 ≠ σ + κ φ`. -/
theorem hasDerivAt_varInfl {β σ κ ρr sr sξ x : ℝ} (hD : Dr β σ κ ρr x ≠ 0)
    (hS : σ + κ * x ≠ 0) :
    HasDerivAt (varInfl β σ κ ρr sr sξ)
      (2 * κ ^ 2 * (σ * sξ * hcrit β σ κ ρr x - κ * sr) / Dr β σ κ ρr x ^ 3) x := by
  have hDr : HasDerivAt (fun y => Dr β σ κ ρr y) κ x := by
    have := (((hasDerivAt_id' x).sub_const ρr).const_mul κ).const_add
      ((1 - β * ρr) * σ * (1 - ρr))
    simpa [Dr] using this
  have hS' : HasDerivAt (fun y => σ + κ * y) κ x := by
    simpa using ((hasDerivAt_id' x).const_mul κ).const_add σ
  have hN : HasDerivAt (fun y => -κ * y) (-κ) x := by
    simpa using (hasDerivAt_id' x).const_mul (-κ)
  have hA := (hasDerivAt_const x κ).fun_div hDr hD
  have hX := hN.fun_div hS' hS
  have hV := ((hA.mul hA).mul_const sr).add ((hX.mul hX).mul_const sξ)
  have hfun : varInfl β σ κ ρr sr sξ = fun y => κ / Dr β σ κ ρr y * (κ / Dr β σ κ ρr y) * sr
      + -κ * y / (σ + κ * y) * (-κ * y / (σ + κ * y)) * sξ := by
    funext y
    unfold varInfl aR aXi
    ring
  rw [hfun]
  refine hV.congr_deriv ?_
  unfold hcrit
  field_simp
  ring

/-- Galí (2015), Exercise 4.2(c): `V` is continuous on `[1, ∞)`. -/
theorem varInfl_continuousOn {β σ κ ρr sr sξ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ1 : ρr < 1) (s : Set ℝ) (hs : s ⊆ Set.Ici 1) :
    ContinuousOn (varInfl β σ κ ρr sr sξ) s := by
  intro x hx
  have hx' : (1 : ℝ) ≤ x := hs hx
  have hD := (Dr_pos hσ hκ hβ0 hβ1 hρ1 hx').ne'
  have hS : σ + κ * x ≠ 0 := by nlinarith
  exact (hasDerivAt_varInfl (sr := sr) (sξ := sξ) hD hS).continuousAt.continuousWithinAt

/-- Galí (2015), Exercise 4.2(c): the sign of `V'` on `(1, ∞)` is the sign of
`σ var ξ · h(φ) − κ var r̂`. -/
theorem deriv_varInfl_eq {β σ κ ρr sr sξ x : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ1 : ρr < 1) (hx : 1 ≤ x) :
    deriv (varInfl β σ κ ρr sr sξ) x
      = 2 * κ ^ 2 * (σ * sξ * hcrit β σ κ ρr x - κ * sr) / Dr β σ κ ρr x ^ 3 ∧
      0 < 2 * κ ^ 2 / Dr β σ κ ρr x ^ 3 := by
  have hDp := Dr_pos hσ hκ hβ0 hβ1 hρ1 hx
  have hS : σ + κ * x ≠ 0 := by nlinarith
  exact ⟨(hasDerivAt_varInfl hDp.ne' hS).deriv, by positivity⟩

/-- **Exercise 4.2(c), interior optimum** (Galí 2015, p. 121): let `var ξ > 0` and
`σ var ξ · h(1) < κ var r̂`. Then there is a unique `φ* > 1` with
`σ var ξ · h(φ*) = κ var r̂`, and `φ*` is the unique minimiser of `var π` over the
determinacy region `φ_π > 1`. -/
theorem ex4_2c_interior {β σ κ ρr sr sξ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) (hsξ : 0 < sξ)
    (hlt : σ * sξ * hcrit β σ κ ρr 1 < κ * sr) :
    ∃ φs, 1 < φs ∧ σ * sξ * hcrit β σ κ ρr φs = κ * sr ∧
      (∀ φ, 1 < φ → σ * sξ * hcrit β σ κ ρr φ = κ * sr → φ = φs) ∧
      ∀ φ, 1 < φ → φ ≠ φs → varInfl β σ κ ρr sr sξ φs < varInfl β σ κ ρr sr sξ φ := by
  have hss : 0 < σ * sξ := mul_pos hσ hsξ
  have h1pos := hcrit_one_pos (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1
  have hmono := hcrit_strictMonoOn (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1
  have hg : StrictMonoOn (fun φ => σ * sξ * hcrit β σ κ ρr φ) (Set.Ici 1) :=
    fun x hx y hy hxy => mul_lt_mul_of_pos_left (hmono hx hy hxy) hss
  -- a point where `σ var ξ · h ≥ κ var r̂`
  set M := max 1 (κ * sr / (σ * sξ * hcrit β σ κ ρr 1)) + 1 with hM
  have hM1 : 1 ≤ M := by
    have := le_max_left 1 (κ * sr / (σ * sξ * hcrit β σ κ ρr 1))
    linarith
  have hMge : κ * sr ≤ σ * sξ * hcrit β σ κ ρr M := by
    have hge := hcrit_ge (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1 hM1
    have hpos : 0 < σ * sξ * hcrit β σ κ ρr 1 := mul_pos hss h1pos
    have hM2 : κ * sr / (σ * sξ * hcrit β σ κ ρr 1) ≤ M := by
      have := le_max_right 1 (κ * sr / (σ * sξ * hcrit β σ κ ρr 1))
      linarith
    rw [div_le_iff₀ hpos] at hM2
    nlinarith
  have hcont : ContinuousOn (fun φ => σ * sξ * hcrit β σ κ ρr φ) (Set.Icc 1 M) :=
    ((hcrit_continuousOn hσ hκ).mono Set.Icc_subset_Ici_self).const_smul (σ * sξ)
  obtain ⟨φs, ⟨hφs1, -⟩, hφs⟩ := intermediate_value_Icc hM1 hcont ⟨hlt.le, hMge⟩
  have hφs1' : 1 < φs := by
    rcases hφs1.lt_or_eq with h | h
    · exact h
    · subst h
      simp only at hφs
      linarith
  refine ⟨φs, hφs1', hφs, fun φ hφ hφeq => ?_, fun φ hφ hne => ?_⟩
  · exact hg.injOn (Set.mem_Ici.mpr hφ.le) (Set.mem_Ici.mpr hφs1) (hφeq.trans hφs.symm)
  · -- `V` decreases on `[1, φ*]` and increases on `[φ*, ∞)`
    have hanti : StrictAntiOn (varInfl β σ κ ρr sr sξ) (Set.Icc 1 φs) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc 1 φs)
        (varInfl_continuousOn hσ hκ hβ0 hβ1 hρ1 _ Set.Icc_subset_Ici_self) fun x hx => ?_
      rw [interior_Icc] at hx
      obtain ⟨hd, hp⟩ := deriv_varInfl_eq (sr := sr) (sξ := sξ) hσ hκ hβ0 hβ1 hρ1
        hx.1.le
      have hlt' : σ * sξ * hcrit β σ κ ρr x < κ * sr := by
        rw [← hφs]
        exact hg (Set.mem_Ici.mpr hx.1.le) (Set.mem_Ici.mpr hφs1) hx.2
      rw [hd, mul_div_right_comm]
      exact mul_neg_of_pos_of_neg hp (by linarith)
    have hmono' : StrictMonoOn (varInfl β σ κ ρr sr sξ) (Set.Ici φs) := by
      refine strictMonoOn_of_deriv_pos (convex_Ici φs)
        (varInfl_continuousOn hσ hκ hβ0 hβ1 hρ1 _ (Set.Ici_subset_Ici.mpr hφs1)) fun x hx => ?_
      rw [interior_Ici] at hx
      have hx' : φs < x := hx
      obtain ⟨hd, hp⟩ := deriv_varInfl_eq (sr := sr) (sξ := sξ) hσ hκ hβ0 hβ1 hρ1
        (hφs1.trans hx'.le)
      have hgt : κ * sr < σ * sξ * hcrit β σ κ ρr x := by
        rw [← hφs]
        exact hg (Set.mem_Ici.mpr hφs1) (Set.mem_Ici.mpr (hφs1.trans hx'.le)) hx'
      rw [hd, mul_div_right_comm]
      exact mul_pos hp (by linarith)
    rcases lt_or_gt_of_ne hne with h | h
    · exact hanti ⟨hφ.le, h.le⟩ ⟨hφs1, le_rfl⟩ h
    · exact hmono' ((Set.mem_Ici.mpr le_rfl)) (Set.mem_Ici.mpr h.le) h

/-- **Exercise 4.2(c), corner case** (Galí 2015, p. 121): if `var ξ > 0` and
`κ var r̂ ≤ σ var ξ · h(1)`, then `var π` is strictly increasing on `[1, ∞)`, so it has no
minimiser on the determinacy region `φ_π > 1`: every `φ_π > 1` is beaten by a smaller one. -/
theorem ex4_2c_corner {β σ κ ρr sr sξ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ0 : 0 ≤ ρr) (hρ1 : ρr < 1) (hsξ : 0 < sξ)
    (hge : κ * sr ≤ σ * sξ * hcrit β σ κ ρr 1) :
    StrictMonoOn (varInfl β σ κ ρr sr sξ) (Set.Ici 1) ∧
      ∀ φ, 1 < φ → ∃ φ', 1 < φ' ∧ φ' < φ ∧
        varInfl β σ κ ρr sr sξ φ' < varInfl β σ κ ρr sr sξ φ := by
  have hss : 0 < σ * sξ := mul_pos hσ hsξ
  have hmono := hcrit_strictMonoOn (β := β) (ρr := ρr) hσ hκ hβ0 hβ1 hρ0 hρ1
  have hV : StrictMonoOn (varInfl β σ κ ρr sr sξ) (Set.Ici 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 1)
      (varInfl_continuousOn hσ hκ hβ0 hβ1 hρ1 _ le_rfl) fun x hx => ?_
    rw [interior_Ici] at hx
    have hx' : 1 < x := hx
    obtain ⟨hd, hp⟩ := deriv_varInfl_eq (sr := sr) (sξ := sξ) hσ hκ hβ0 hβ1 hρ1 hx'.le
    have hgt : σ * sξ * hcrit β σ κ ρr 1 < σ * sξ * hcrit β σ κ ρr x :=
      mul_lt_mul_of_pos_left (hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx'.le) hx') hss
    rw [hd, mul_div_right_comm]
    exact mul_pos hp (by linarith)
  refine ⟨hV, fun φ hφ => ⟨(1 + φ) / 2, by linarith, by linarith, ?_⟩⟩
  exact hV (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr hφ.le) (by linarith)

/-- **Exercise 4.2(c), no measurement error** (Galí 2015, p. 121 and fn. 10, p. 114): if
`var ξ = 0`, `var r̂ > 0` and `ρ_r < 1`, then `var π` is strictly decreasing on `[1, ∞)`
and tends to `0` as `φ_π → ∞`; there is no minimiser. -/
theorem ex4_2c_no_noise {β σ κ ρr sr : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ1 : ρr < 1) (hsr : 0 < sr) :
    StrictAntiOn (varInfl β σ κ ρr sr 0) (Set.Ici 1) ∧
      Tendsto (varInfl β σ κ ρr sr 0) atTop (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · refine strictAntiOn_of_deriv_neg (convex_Ici 1)
      (varInfl_continuousOn hσ hκ hβ0 hβ1 hρ1 _ le_rfl) fun x hx => ?_
    rw [interior_Ici] at hx
    have hx' : 1 < x := hx
    obtain ⟨hd, hp⟩ := deriv_varInfl_eq (sr := sr) (sξ := 0) hσ hκ hβ0 hβ1 hρ1 hx'.le
    rw [hd, mul_div_right_comm]
    exact mul_neg_of_pos_of_neg hp (by nlinarith)
  · have h := (ex4_2b_coefficients β ρr hκ (σ := σ)).1
    have := (h.pow 2).mul_const sr
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
    refine this.congr fun φ => ?_
    simp [varInfl]

/-- Galí (2015), Exercise 4.2(c), hint (`ρ_r = 0`): then `h(φ) = φ`. -/
theorem hcrit_iid {β σ κ φ : ℝ} (hS : σ + κ * φ ≠ 0) : hcrit β σ κ 0 φ = φ := by
  unfold hcrit Dr
  have : (1 - β * 0) * σ * (1 - 0) + κ * (φ - 0) = σ + κ * φ := by ring
  rw [this, div_self hS, one_pow, mul_one]

/-- **Exercise 4.2(c), i.i.d. natural rate** (Galí 2015, p. 121, hint `ρ_r = 0`): with
`var ξ > 0` and `φ* = κ var r̂/(σ var ξ) > 1`, `φ*` is the unique minimiser of `var π` over
`φ_π > 1`. -/
theorem ex4_2c_iid {β σ κ sr sξ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hsξ : 0 < sξ) (h1 : 1 < κ * sr / (σ * sξ)) :
    ∀ φ, 1 < φ → φ ≠ κ * sr / (σ * sξ) →
      varInfl β σ κ 0 sr sξ (κ * sr / (σ * sξ)) < varInfl β σ κ 0 sr sξ φ := by
  have hss : 0 < σ * sξ := mul_pos hσ hsξ
  have hlt : σ * sξ * hcrit β σ κ 0 1 < κ * sr := by
    rw [hcrit_iid (by positivity), mul_one]
    rwa [one_lt_div hss] at h1
  obtain ⟨φs, hφs1, hφs, huniq, hmin⟩ := ex4_2c_interior hσ hκ hβ0 hβ1 le_rfl one_pos hsξ hlt
  have hK : σ * sξ * hcrit β σ κ 0 (κ * sr / (σ * sξ)) = κ * sr := by
    rw [hcrit_iid (by positivity)]
    field_simp
  have heq : κ * sr / (σ * sξ) = φs := huniq _ h1 hK
  rw [heq]
  intro φ hφ hne
  exact hmin φ hφ hne

end Gali.MonetaryPolicyDesign.Ex4_2
