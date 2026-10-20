/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.StarredModel
import ObservationalEquivalence.ExpectationsFiniteTree

/-!
# Observational equivalence of interest-rate regimes

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, pp. 495–497 (the
box on p. 495, the bullets on pp. 496–497 and the "recipe" of p. 497), and Chapter 16, §16.6,
pp. 372–374 ((16.20)–(16.24)).

The theorem the book states verbally: in the starred system, the target path `(π*, i*, v*, s̃*)`
is an equilibrium whatever the off-target coefficients `(φ, γ)`; in the active-money and in the
active-fiscal regions it is the *only* equilibrium; so equilibrium time series cannot tell the
regimes apart.

## The corrected regime boundaries (survey error E12)

Under the book's equilibrium criterion (bounded inflation, transversality condition for debt):

* `unique_of_active_money`: `|φ| > 1` (not only `φ > 1`) gives uniqueness, for every `γ`;
* `unique_of_active_fiscal`: `|1 − γ| ≥ 1`, i.e. `γ ≤ 0` or `γ ≥ 2` (not only `γ = 0`), gives
  uniqueness, for every `φ`;
* `continuum_double_passive`: `|φ| ≤ 1` and `0 < γ < 2` give a continuum of equilibria (indexed
  by the date-0 inflation jump, under any expectation system, even perfect foresight);
  `sunspot_eqm`: also every bounded martingale-difference sunspot gives an equilibrium, and on the
  coin-flip tree (`coin_sunspot_eqm`) such equilibria are genuinely random.
* `unique_iff`: the target is the unique admissible equilibrium **iff**
  `|φ| > 1 ∨ γ ≤ 0 ∨ γ ≥ 2`. In particular "both active" (`|φ| > 1`, `γ = 0`) is determinate in
  the starred form (`unique_double_active`, survey error E19), and `γ ≥ 2` is not passive.

## Observational equivalence, both ways (pp. 496–497)

* `recipe`: any path satisfying the equilibrium conditions common to all models (Fisher, flow,
  bounded inflation, transversality) is the unique equilibrium of the starred system around
  itself for every determinate `(φ, γ)` — the recipe that turns any new-Keynesian or monetarist
  equilibrium into a fiscal-theory equilibrium "without changing any of its implications for
  observable time series", and conversely (`oe_both_ways`, `leeper_recipe`).

## The new-Keynesian AR(1) example (§16.6, pp. 372–373)

* `nk_solution`, `nk_unique`, `nk_observables` ((16.15)–(16.18)): with `i_t = φπ_t + u_t`,
  `u` an AR(1) with persistence `η` and `|φ| > 1`, the unique bounded equilibrium is
  `π_t = −u_t/(φ − η)`; `i_t = ηπ_t` and `π_{t+1} = ηπ_t − ε_{t+1}/(φ − η)`.
* `ftpl_eq_nk`: the fiscal-theory equilibrium with rule `i_t = θπ_t`, `θ = η`, and fiscal shock
  `ε^Σ_{s,t+1} = ε_{t+1}/(φ − η)` is the same process.
* `nk_passive_fiscal_news`: in the new-Keynesian equilibrium the valuation equation forces the
  "passive" fiscal news `ΔE_{t+1} ∑ ρʲ s̃_{t+1+j} = ε_{t+1}/(φ − η)` — the fiscal theorist's shock.
-/

namespace Cochrane.ObservationalEquivalence.Equivalence

open Filter Topology
open Cochrane.ObservationalEquivalence.Valuation Cochrane.ObservationalEquivalence.StarredModel
open Cochrane.ObservationalEquivalence.FiscalRec
open Cochrane.ObservationalEquivalence.ExpectationTools (innov pvExPost)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §22.1, p. 495 ("unique" equilibrium): the target is the only admissible
equilibrium of the `(φ, γ)` starred system. -/
def UniqueEqm (ρ φ γ : ℝ) (tg : Outcome Ω) : Prop :=
  ∀ x, Eqm 𝔼 ρ φ γ tg x → Admissible 𝔼 ρ x → x = tg

/-- Cochrane (2023), p. 495 (regime labels, corrected per survey error E12): the determinate set
under the transversality criterion, `|φ| > 1` (active money) or `|1 − γ| ≥ 1` (active fiscal). -/
def Determinate (φ γ : ℝ) : Prop := 1 < |φ| ∨ 1 ≤ |1 - γ|

/-! ### Existence -/

/-- Cochrane (2023), §22.1, p. 495, and §16.6, p. 373: the target is an admissible equilibrium of
the `(φ, γ)` system for every `φ` and `γ`. -/
theorem starred_admissible_eqm {ρ : ℝ} (φ γ : ℝ) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) : Eqm 𝔼 ρ φ γ tg tg ∧ Admissible 𝔼 ρ tg :=
  ⟨starred_eqm 𝔼 φ γ hc, htg⟩

/-! ### Deviation lemmas -/

/-- Cochrane (2023), (22.1), p. 495: if inflation is on target (`e = 0`) the debt deviation
obeys `ρ d_{t+1} = (1 − γ) d_t` from `d_0 = 0`, so it is zero. -/
theorem d_zero_of_e_zero {ρ γ : ℝ} (hρ : ρ ≠ 0) {e d : ℕ → Ω → ℝ} (he : e = 0)
    (hd : ∀ t, ρ • d (t + 1) = (1 - γ) • d t - surprise 𝔼 e t) (h0 : ρ • d 0 + e 0 = 0) :
    d = 0 := by
  subst he
  have hs : ∀ t, surprise 𝔼 (0 : ℕ → Ω → ℝ) t = 0 := fun t => by
    simp [surprise]
  funext t
  induction t with
  | zero =>
    simp only [Pi.zero_apply, add_zero] at h0
    exact (smul_eq_zero.mp h0).resolve_left hρ
  | succ t ih =>
    have := hd t
    rw [ih, hs] at this
    simp only [Pi.zero_apply, smul_zero, sub_zero] at this ⊢
    exact (smul_eq_zero.mp this).resolve_left hρ

/-- Cochrane (2023), (22.1), p. 495: if debt is on target (`d = 0`), there is no surprise
inflation and no date-0 jump, so `e_{t+1} = φ e_t` from `e_0 = 0`, hence `e = 0`. -/
theorem e_zero_of_d_zero {ρ φ γ : ℝ} {e d : ℕ → Ω → ℝ} (hd0 : d = 0)
    (he : ∀ t, 𝔼.E t (e (t + 1)) = φ • e t)
    (hd : ∀ t, ρ • d (t + 1) = (1 - γ) • d t - surprise 𝔼 e t) (h0 : ρ • d 0 + e 0 = 0) :
    e = 0 := by
  subst hd0
  funext t
  induction t with
  | zero => simpa using h0
  | succ t ih =>
    have h1 := hd t
    simp only [Pi.zero_apply, smul_zero, zero_sub] at h1
    have h2 : surprise 𝔼 e t = 0 := neg_eq_zero.mp h1.symm
    rw [surprise, sub_eq_zero, he t, ih] at h2
    simp only [Pi.zero_apply, smul_zero] at h2 ⊢
    exact h2

/-- Cochrane (2023), (23.4), p. 512: with `ρ ≠ 0`, an adapted debt deviation obeying
`ρ d_{t+1} = (1 − γ) d_t − w_{t+1}` with unforecastable `w` is an AR(1),
`E_t d_{t+1} = ((1 − γ)/ρ) d_t`. -/
theorem isAR1_of_dyn {ρ γ : ℝ} (hρ : ρ ≠ 0) {d w : ℕ → Ω → ℝ} (hda : 𝔼.Adapted d)
    (hd : ∀ t, ρ • d (t + 1) = (1 - γ) • d t - w t) (hw : ∀ t, 𝔼.E t (w t) = 0) :
    𝔼.IsAR1 ((1 - γ) / ρ) d := by
  refine ⟨hda, fun t => ?_⟩
  have h := congrArg (𝔼.E t) (hd t)
  rw [map_smul, map_sub, map_smul, hda t, hw t, sub_zero] at h
  rw [div_eq_inv_mul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hρ, one_smul]

/-- Cochrane (2023), p. 513: for an AR(1) debt deviation, `ρᵀ E_t d_{t+T} = (1 − γ)ᵀ d_t`. -/
theorem pow_mul_E_ar1 {ρ γ : ℝ} (hρ : ρ ≠ 0) {d : ℕ → Ω → ℝ} (hAR : 𝔼.IsAR1 ((1 - γ) / ρ) d)
    (t T : ℕ) (ω : Ω) : ρ ^ T * 𝔼.E t (d (t + T)) ω = (1 - γ) ^ T * d t ω := by
  rw [𝔼.ar1_iterate hAR t T, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← mul_pow,
    mul_div_cancel₀ _ hρ]

/-- Cochrane (2023), p. 513 ("if `γ > 0` … any unexpected inflation is consistent with the
transversality condition", corrected to `0 < γ < 2`): an AR(1) debt deviation with
`|1 − γ| < 1` satisfies the transversality condition. -/
theorem tvc_of_ar1 {ρ γ : ℝ} (hρ : ρ ≠ 0) (hγ : |1 - γ| < 1) {d : ℕ → Ω → ℝ}
    (hAR : 𝔼.IsAR1 ((1 - γ) / ρ) d) : TVC 𝔼 ρ d := by
  intro t ω
  simp_rw [pow_mul_E_ar1 𝔼 hρ hAR t _ ω]
  exact (tendsto_pow_mul_iff _ _).mpr (Or.inl hγ)

/-- Cochrane (2023), p. 513 ("if `γ = 0`, then only one value of unexpected inflation keeps
debt from exploding", generalised to `|1 − γ| ≥ 1`): an AR(1) debt deviation satisfying the
transversality condition is zero. -/
theorem zero_of_ar1_tvc {ρ γ : ℝ} (hρ : ρ ≠ 0) (hγ : 1 ≤ |1 - γ|) {d : ℕ → Ω → ℝ}
    (hAR : 𝔼.IsAR1 ((1 - γ) / ρ) d) (htvc : TVC 𝔼 ρ d) : d = 0 := by
  funext t ω
  have h := htvc t ω
  simp_rw [pow_mul_E_ar1 𝔼 hρ hAR t _ ω] at h
  exact eq_zero_of_tendsto_pow_mul hγ h

/-! ### Uniqueness in the determinate regions -/

/-- Cochrane (2023), §22.1, p. 495, and §16.5–16.6, pp. 371–373 (active money, `|φ| > 1`; survey
error E12: `φ < −1` is also active): the target is the unique admissible equilibrium, for every
fiscal coefficient `γ`. -/
theorem unique_of_active_money {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hφ : 1 < |φ|) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) : UniqueEqm 𝔼 ρ φ γ tg := by
  intro x hx hadm
  obtain ⟨he, hd, h0⟩ := deviation_dynamics 𝔼 hc hx
  obtain ⟨-, heb, -, -⟩ := dev_admissible 𝔼 htg hadm
  have e0 : (fun t => x.pi t - tg.pi t) = 0 := zero_of_E_succ_eq_smul 𝔼 hφ heb he
  have d0 := d_zero_of_e_zero 𝔼 (d := fun t => x.v t - tg.v t) hρ e0 hd h0
  rw [eq_ofDev 𝔼 hx, e0, d0, ofDev_zero]

/-- Cochrane (2023), §22.1, p. 495, and §16.6, p. 373 (active fiscal; survey error E12: every
`γ` with `|1 − γ| ≥ 1`, i.e. `γ ≤ 0` or `γ ≥ 2`, not only `γ = 0`): the target is the unique
admissible equilibrium, for every monetary coefficient `φ`. -/
theorem unique_of_active_fiscal {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hγ : 1 ≤ |1 - γ|) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) : UniqueEqm 𝔼 ρ φ γ tg := by
  intro x hx hadm
  obtain ⟨he, hd, h0⟩ := deviation_dynamics 𝔼 hc hx
  obtain ⟨-, -, hda, htvc⟩ := dev_admissible 𝔼 htg hadm
  have hAR := isAR1_of_dyn 𝔼 (d := fun t => x.v t - tg.v t) hρ hda hd
    (fun t => E_surprise 𝔼 _ t)
  have d0 := zero_of_ar1_tvc 𝔼 hρ hγ hAR htvc
  have e0 := e_zero_of_d_zero 𝔼 (e := fun t => x.pi t - tg.pi t) d0 he hd h0
  rw [eq_ofDev 𝔼 hx, e0, d0, ofDev_zero]

/-- Cochrane (2023), §22.1, p. 495 (the box): in the determinate set the target is the unique
admissible equilibrium. -/
theorem unique_of_determinate {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (h : Determinate φ γ) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) : UniqueEqm 𝔼 ρ φ γ tg := by
  rcases h with h | h
  · exact unique_of_active_money 𝔼 hρ h hc htg
  · exact unique_of_active_fiscal 𝔼 hρ h hc htg

/-- Cochrane (2023), §16.6, p. 373, and §22.1, p. 495 (the book's active-fiscal regime `γ = 0`,
any `φ`, most simply `φ = 0`): the target is the unique admissible equilibrium. -/
theorem unique_of_gamma_zero {ρ φ : ℝ} (hρ : ρ ≠ 0) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) : UniqueEqm 𝔼 ρ φ 0 tg :=
  unique_of_active_fiscal 𝔼 hρ (by norm_num) hc htg

/-- Cochrane (2023), §22.7, p. 508 (survey error E19, confirmed): "if `φ > 1` and `γ = 0` both
policies are active … no equilibrium can form" is false in the starred form — the coordinated
target is an equilibrium and it is the unique one. -/
theorem unique_double_active {ρ φ : ℝ} (hρ : ρ ≠ 0) (hφ : 1 < φ) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) :
    (Eqm 𝔼 ρ φ 0 tg tg ∧ Admissible 𝔼 ρ tg) ∧ UniqueEqm 𝔼 ρ φ 0 tg :=
  ⟨starred_admissible_eqm 𝔼 φ 0 hc htg,
    unique_of_active_money 𝔼 hρ (by rw [abs_of_pos (by linarith)]; exact hφ) hc htg⟩

/-! ### The double-passive continuum -/

/-- Cochrane (2023), §22.7, pp. 508–509 (double passive): the inflation deviation `e_t = c φᵗ`
of a date-0 jump `c`. -/
def famE (φ c : ℝ) : ℕ → Ω → ℝ := fun t _ => c * φ ^ t

/-- Cochrane (2023), §22.7, pp. 508–509 (double passive): the debt deviation
`d_t = −(c/ρ) ((1 − γ)/ρ)ᵗ` matching a date-0 inflation jump `c`. -/
noncomputable def famD (ρ γ c : ℝ) : ℕ → Ω → ℝ := fun t _ => -(c / ρ) * ((1 - γ) / ρ) ^ t

/-- Cochrane (2023), §22.7, pp. 508–509: the equilibrium with date-0 inflation jump `c`. -/
noncomputable def famPath (ρ φ γ : ℝ) (tg : Outcome Ω) (c : ℝ) : Outcome Ω :=
  ofDev φ γ tg (famE φ c) (famD ρ γ c)

/-- Cochrane (2023), §22.7, pp. 508–509: the path with date-0 jump `c` is an equilibrium of the
`(φ, γ)` system for every `φ`, `γ` and `c` (`ρ ≠ 0`). -/
theorem famPath_eqm {ρ φ γ : ℝ} (hρ : ρ ≠ 0) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (c : ℝ) : Eqm 𝔼 ρ φ γ tg (famPath ρ φ γ tg c) := by
  have hs : ∀ t, surprise 𝔼 (famE φ c) t = 0 := fun t => by
    rw [surprise]
    change (fun _ => c * φ ^ (t + 1)) - 𝔼.E t (fun _ => c * φ ^ (t + 1)) = 0
    rw [𝔼.const, sub_self]
  refine ofDev_eqm 𝔼 hc (fun t => ?_) (fun t => ?_) ?_
  · change 𝔼.E t (fun _ => c * φ ^ (t + 1)) = φ • fun _ => c * φ ^ t
    rw [𝔼.const]
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · rw [hs, sub_zero]
    funext ω
    simp only [famD, Pi.smul_apply, smul_eq_mul]
    have hq : ρ * ((1 - γ) / ρ) = 1 - γ := mul_div_cancel₀ _ hρ
    rw [pow_succ]
    linear_combination (-(c / ρ) * ((1 - γ) / ρ) ^ t) * hq
  · funext ω
    simp only [famD, famE, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring

/-- Cochrane (2023), §22.7, pp. 508–509 (double passive, `|φ| ≤ 1`, `0 < γ < 2`): the path with
date-0 jump `c` is admissible (bounded inflation, transversality condition). -/
theorem famPath_admissible {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hφ : |φ| ≤ 1) (hγ : |1 - γ| < 1)
    {tg : Outcome Ω} (htg : Admissible 𝔼 ρ tg) (c : ℝ) :
    Admissible 𝔼 ρ (famPath ρ φ γ tg c) := by
  refine ofDev_admissible 𝔼 htg (fun t => 𝔼.const t _) ⟨|c|, fun t ω => ?_⟩
    (fun t => 𝔼.const t _) (fun t ω => ?_)
  · simp only [famE, abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg c) (pow_le_one₀ (abs_nonneg φ) hφ)
  · have e : ∀ T : ℕ, ρ ^ T * 𝔼.E t (famD ρ γ c (t + T)) ω =
        (1 - γ) ^ T * (-(c / ρ) * ((1 - γ) / ρ) ^ t) := by
      intro T
      change ρ ^ T * 𝔼.E t (fun _ => -(c / ρ) * ((1 - γ) / ρ) ^ (t + T)) ω = _
      rw [𝔼.const, pow_add, div_pow (1 - γ) ρ T]
      field_simp
    simp_rw [e]
    exact (tendsto_pow_mul_iff _ _).mpr (Or.inl hγ)

/-- Cochrane (2023), §22.7, pp. 508–509: different date-0 jumps give different paths. -/
theorem famPath_injective [Nonempty Ω] (ρ φ γ : ℝ) (tg : Outcome Ω) :
    Function.Injective (famPath ρ φ γ tg) := by
  intro c₁ c₂ h
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := congrFun (congrFun (congrArg Outcome.pi h) 0) ω
  simpa [famPath, ofDev, famE] using this

/-- Cochrane (2023), §22.7, pp. 508–509 ("if … φ < 1 … and fiscal policy is also passive, γ > 0,
then we are back to indeterminacy"; corrected to `|φ| ≤ 1`, `0 < γ < 2`): the admissible
equilibria form an uncountable set. -/
theorem continuum_double_passive [Nonempty Ω] {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hφ : |φ| ≤ 1)
    (hγ : 0 < γ ∧ γ < 2) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) :
    ¬ {x | Eqm 𝔼 ρ φ γ tg x ∧ Admissible 𝔼 ρ x}.Countable := by
  intro hcount
  have hγ' : |1 - γ| < 1 := (abs_one_sub_lt_one_iff γ).mpr hγ
  have hmaps : Set.MapsTo (famPath ρ φ γ tg) Set.univ
      {x | Eqm 𝔼 ρ φ γ tg x ∧ Admissible 𝔼 ρ x} := fun c _ =>
    ⟨famPath_eqm 𝔼 hρ hc c, famPath_admissible 𝔼 hρ hφ hγ' htg c⟩
  exact Cardinal.not_countable_real
    (hmaps.countable_of_injOn (famPath_injective ρ φ γ tg).injOn hcount)

/-- Cochrane (2023), §22.7, pp. 508–509: in the double-passive region the target is not the
unique admissible equilibrium. -/
theorem not_unique_of_passive [Nonempty Ω] {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hφ : |φ| ≤ 1)
    (hγ : |1 - γ| < 1) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) :
    ¬ UniqueEqm 𝔼 ρ φ γ tg := by
  intro hu
  have h1 := hu _ (famPath_eqm 𝔼 hρ hc 1) (famPath_admissible 𝔼 hρ hφ hγ htg 1)
  have h0 : famPath ρ φ γ tg 0 = tg := by
    rw [famPath]
    have e1 : famE φ 0 = (0 : ℕ → Ω → ℝ) := by funext t ω; simp [famE]
    have e2 : famD ρ γ 0 = (0 : ℕ → Ω → ℝ) := by funext t ω; simp [famD]
    rw [e1, e2, ofDev_zero]
  have := famPath_injective ρ φ γ tg (h1.trans h0.symm)
  norm_num at this

/-- Cochrane (2023), §22.1, p. 495, and §22.7, pp. 508–509 (the complete classification under the
transversality criterion): for a consistent admissible target, the target is the unique
admissible equilibrium iff `|φ| > 1` or `|1 − γ| ≥ 1`. -/
theorem unique_iff [Nonempty Ω] {ρ φ γ : ℝ} (hρ : ρ ≠ 0) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) :
    UniqueEqm 𝔼 ρ φ γ tg ↔ Determinate φ γ := by
  refine ⟨fun hu => ?_, fun h => unique_of_determinate 𝔼 hρ h hc htg⟩
  by_contra hd
  simp only [Determinate, not_or, not_lt, not_le] at hd
  exact not_unique_of_passive 𝔼 hρ hd.1 hd.2 hc htg hu

/-- Cochrane (2023), pp. 495, 501, 512 (survey error E12): the determinate set is
`|φ| > 1 ∨ γ ≤ 0 ∨ γ ≥ 2`. -/
theorem determinate_iff (φ γ : ℝ) : Determinate φ γ ↔ 1 < |φ| ∨ γ ≤ 0 ∨ 2 ≤ γ := by
  rw [Determinate, one_le_abs_one_sub_iff]

/-- Cochrane (2023), p. 495 (survey error E12, counterexample to the printed "`φ < 1`, `γ > 0`
is passive–passive"): `φ = −2 < 1` with `γ = 1 > 0` is determinate. -/
theorem printed_phi_lt_one_determinate : Determinate (-2) 1 := Or.inl (by norm_num)

/-- Cochrane (2023), p. 495 (survey error E12, counterexample to the printed "`γ > 0` is passive
fiscal"): `γ = 3 > 0` with `φ = 1/2 < 1` is determinate (fiscal policy is active). -/
theorem printed_gamma_pos_determinate : Determinate (1 / 2) 3 := Or.inr (by norm_num)

/-! ### Sunspot equilibria -/

/-- Cochrane (2023), §22.7, pp. 508–509 ("indeterminate … even if the ingredient is sunspots"):
in the double-passive region (`|φ| < 1`, `0 < γ < 2`), every bounded adapted martingale
difference `ν` (`E_t ν_{t+1} = 0`) and every date-0 jump `c` give an admissible equilibrium
with inflation deviation `e_{t+1} = φ e_t + ν_{t+1}`, `e_0 = c`. -/
theorem sunspot_eqm {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hφ : |φ| < 1) (hγ : |1 - γ| < 1)
    {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) {ν : ℕ → Ω → ℝ}
    (hνa : 𝔼.Adapted ν) (hνb : BoundedProc ν) (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0) (c : ℝ) :
    Eqm 𝔼 ρ φ γ tg (ofDev φ γ tg (dRec φ (fun t => ν (t + 1)) (fun _ => c))
        (dRec ((1 - γ) / ρ) (fun t => (-ρ⁻¹) • ν (t + 1)) (fun _ => -(c / ρ)))) ∧
      Admissible 𝔼 ρ (ofDev φ γ tg (dRec φ (fun t => ν (t + 1)) (fun _ => c))
        (dRec ((1 - γ) / ρ) (fun t => (-ρ⁻¹) • ν (t + 1)) (fun _ => -(c / ρ)))) := by
  set e := dRec φ (fun t => ν (t + 1)) (fun _ => c) with he_def
  set d := dRec ((1 - γ) / ρ) (fun t => (-ρ⁻¹) • ν (t + 1)) (fun _ => -(c / ρ)) with hd_def
  have hea : 𝔼.Adapted e := dRec_adapted_of_succ 𝔼 (𝔼.const 0 c) (fun t => hνa (t + 1))
  have hda : 𝔼.Adapted d := dRec_adapted_of_succ 𝔼 (𝔼.const 0 _) (fun t => by
    rw [map_smul, hνa (t + 1)])
  have hE : ∀ t, 𝔼.E t (e (t + 1)) = φ • e t := fun t => by
    change 𝔼.E t (φ • e t + ν (t + 1)) = φ • e t
    rw [map_add, map_smul, hea t, hmd t, add_zero]
  have hsur : ∀ t, surprise 𝔼 e t = ν (t + 1) := fun t => by
    rw [surprise, hE t]
    change φ • e t + ν (t + 1) - φ • e t = ν (t + 1)
    abel
  have hdyn : ∀ t, ρ • d (t + 1) = (1 - γ) • d t - surprise 𝔼 e t := fun t => by
    rw [hsur t]
    change ρ • (((1 - γ) / ρ) • d t + (-ρ⁻¹) • ν (t + 1)) = _
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hρ, mul_neg, mul_inv_cancel₀ hρ,
      neg_one_smul]
    exact (sub_eq_add_neg _ _).symm
  have h0 : ρ • d 0 + e 0 = 0 := by
    funext ω
    change ρ * -(c / ρ) + c = 0
    field_simp
    ring
  refine ⟨ofDev_eqm 𝔼 hc hE hdyn h0, ofDev_admissible 𝔼 htg hea ?_ hda ?_⟩
  · obtain ⟨M, hM⟩ := hνb
    exact ⟨|c| + |M| / (1 - |φ|), rec_bounded hφ (abs_nonneg c) (abs_nonneg M)
      (fun t ω => (hM (t + 1) ω).trans (le_abs_self M)) (fun t => rfl) (fun ω => le_rfl)⟩
  · have hAR := isAR1_of_dyn 𝔼 hρ hda hdyn (fun t => E_surprise 𝔼 e t)
    exact tvc_of_ar1 𝔼 hρ hγ hAR

/-- The coin-flip shock is adapted (used for Cochrane (2023), §22.7, p. 509: genuinely random
sunspot equilibria exist). -/
theorem coinShock_adapted :
    ExpectationsFiniteTree.coinSystem.Adapted ExpectationsFiniteTree.coinShock := fun t => by
  funext ω
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h =>
    ExpectationsFiniteTree.coinShock_measurable t h

/-- The coin-flip shock is bounded by one (Cochrane (2023), §22.7, p. 509). -/
theorem coinShock_bounded : BoundedProc ExpectationsFiniteTree.coinShock :=
  ⟨1, fun t ω => by
    unfold ExpectationsFiniteTree.coinShock
    split_ifs <;> norm_num⟩

/-- Cochrane (2023), §22.7, pp. 508–509, and survey §3.2 (OE-1 (3)): on the coin-flip tree, in
the double-passive region, there is an admissible equilibrium whose date-1 inflation differs
from the target by the coin flip `±1` — a genuinely random sunspot equilibrium. -/
theorem coin_sunspot_eqm {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (hφ : |φ| < 1) (hγ : |1 - γ| < 1)
    {tg : Outcome (Bool × Bool)} (hc : Consistent ExpectationsFiniteTree.coinSystem ρ tg)
    (htg : Admissible ExpectationsFiniteTree.coinSystem ρ tg) :
    ∃ x, Eqm ExpectationsFiniteTree.coinSystem ρ φ γ tg x ∧
      Admissible ExpectationsFiniteTree.coinSystem ρ x ∧ x.pi 0 = tg.pi 0 ∧
      x.pi 1 = tg.pi 1 + ExpectationsFiniteTree.coinShock 1 := by
  obtain ⟨h1, h2⟩ := sunspot_eqm ExpectationsFiniteTree.coinSystem hρ hφ hγ hc htg
    coinShock_adapted coinShock_bounded ExpectationsFiniteTree.coinShock_mean_zero 0
  refine ⟨_, h1, h2, ?_, ?_⟩
  · funext ω
    simp [ofDev, dRec]
  · funext ω
    simp [ofDev, dRec]

/-! ### Perfect foresight -/

/-- Cochrane (2023), §22.7, p. 509 (under perfect foresight the only indeterminacy is the date-0
jump): every equilibrium of the `(φ, γ)` system under perfect foresight is the path `famPath c`
with `c = π_0 − π*_0`. -/
theorem perfectForesight_eq_famPath {ρ φ γ : ℝ} (hρ : ρ ≠ 0) {tg x : Outcome Unit}
    (hc : Consistent perfectForesight ρ tg) (hx : Eqm perfectForesight ρ φ γ tg x) :
    x = famPath ρ φ γ tg (x.pi 0 () - tg.pi 0 ()) := by
  obtain ⟨he, hd, h0⟩ := deviation_dynamics perfectForesight hc hx
  set c := x.pi 0 () - tg.pi 0 () with hc_def
  have hs : ∀ t, surprise perfectForesight (fun t => x.pi t - tg.pi t) t = 0 := fun t => by
    rw [surprise]
    change _ - (x.pi (t + 1) - tg.pi (t + 1)) = 0
    rw [sub_self]
  have hE : ∀ t, (fun t => x.pi t - tg.pi t) t = famE φ c t := by
    intro t
    induction t with
    | zero => funext u; simp [famE, hc_def]
    | succ t ih =>
      have h := he t
      change x.pi (t + 1) - tg.pi (t + 1) = _ at h
      change x.pi (t + 1) - tg.pi (t + 1) = _
      rw [h]
      change x.pi t - tg.pi t = _ at ih
      rw [ih]
      funext u
      simp only [famE, Pi.smul_apply, smul_eq_mul]
      ring
  have hD : ∀ t, (fun t => x.v t - tg.v t) t = famD ρ γ c t := by
    intro t
    induction t with
    | zero =>
      have h := congrFun h0 ()
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      funext u
      simp only [famD, pow_zero, mul_one]
      change x.v 0 () - tg.v 0 () = _
      rw [hc_def]
      field_simp
      linarith
    | succ t ih =>
      have h := hd t
      rw [hs t, sub_zero] at h
      change x.v t - tg.v t = _ at ih
      rw [ih] at h
      change x.v (t + 1) - tg.v (t + 1) = _
      funext u
      have h' := congrFun h u
      simp only [famD, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h' ⊢
      have hq : ρ * ((1 - γ) / ρ) = 1 - γ := mul_div_cancel₀ _ hρ
      apply mul_left_cancel₀ hρ
      rw [h', pow_succ]
      linear_combination (c / ρ * ((1 - γ) / ρ) ^ t) * hq
  rw [eq_ofDev perfectForesight hx, famPath]
  congr 1
  · funext t; exact hE t
  · funext t; exact hD t

/-! ### The recipe: observational equivalence goes both ways -/

/-- Cochrane (2023), §22.2.1, p. 497 ("a recipe by which one can transform any monetarist or
new-Keynesian model into a fiscal theory model, without changing any of its implications for
observable time series"): any path obeying the Fisher equation and the flow condition, with
bounded adapted inflation, adapted debt and the transversality condition, is the unique
admissible equilibrium of the starred system around itself for every determinate `(φ, γ)` —
in particular for active fiscal policy `φ = 0, γ = 0` and for active money `φ = 2`. -/
theorem recipe {ρ : ℝ} (hρ : ρ ≠ 0) {x : Outcome Ω} (hF : Fisher 𝔼 x.i x.pi)
    (hflow : Flow ρ x.v x.i x.pi x.s) (hadm : Admissible 𝔼 ρ x) :
    ∀ φ γ, Determinate φ γ → Eqm 𝔼 ρ φ γ x x ∧ UniqueEqm 𝔼 ρ φ γ x :=
  fun φ γ h => ⟨starred_eqm 𝔼 φ γ ⟨hF, hflow⟩,
    unique_of_determinate 𝔼 hρ h ⟨hF, hflow⟩ hadm⟩

/-- Cochrane (2023), §22.1, p. 496 ("any time series produced by an active-money/passive fiscal
regime can be produced by an active-fiscal/passive-money regime and vice versa"): an admissible
equilibrium of any `(φ₁, γ₁)` system is the unique admissible equilibrium of the `(φ₂, γ₂)`
system around itself, for every determinate `(φ₂, γ₂)`. -/
theorem oe_both_ways {ρ φ₁ γ₁ φ₂ γ₂ : ℝ} (hρ : ρ ≠ 0) {tg x : Outcome Ω}
    (hx : Eqm 𝔼 ρ φ₁ γ₁ tg x) (hadm : Admissible 𝔼 ρ x) (h₂ : Determinate φ₂ γ₂) :
    Eqm 𝔼 ρ φ₂ γ₂ x x ∧ UniqueEqm 𝔼 ρ φ₂ γ₂ x :=
  recipe 𝔼 hρ hx.1 hx.2.2.2.2.1 hadm φ₂ γ₂ h₂

/-- Cochrane (2023), §22.3, p. 500, and §22.2.1, p. 497: an admissible equilibrium of the Leeper
model (22.3)–(22.6) with any coefficients (active money `φ > 1, γ > 0` included) is the unique
admissible equilibrium of the active-fiscal starred system (`φ = 0`, `γ = 0`) around itself. -/
theorem leeper_recipe {ρ φ γ : ℝ} (hρ : ρ ≠ 0) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    {x : Outcome Ω} (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (hadm : Admissible 𝔼 ρ x) :
    Eqm 𝔼 ρ 0 0 x x ∧ UniqueEqm 𝔼 ρ 0 0 x :=
  recipe 𝔼 hρ hx.1 hx.2.2.2.2.1 hadm 0 0 (Or.inr (by norm_num))

/-! ### §16.6: the new-Keynesian AR(1) model and its fiscal-theory twin -/

/-- Cochrane (2023), (16.10), p. 370, and (16.15), p. 371: with `i_t = φπ_t + u_t`, `u` an AR(1)
with persistence `η ≠ φ`, the process `π_t = −u_t/(φ − η)` solves `E_t π_{t+1} = φπ_t + u_t`. -/
theorem nk_solution {φ η : ℝ} (hφη : φ ≠ η) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) (t : ℕ) :
    𝔼.E t ((-(φ - η)⁻¹) • u (t + 1)) = φ • ((-(φ - η)⁻¹) • u t) + u t := by
  have h : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  rw [map_smul, hu.2 t]
  funext ω
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), §16.5, p. 371 (active money, `|φ| > 1`): `π_t = −u_t/(φ − η)` is the unique
bounded solution of `E_t π_{t+1} = φπ_t + u_t`. -/
theorem nk_unique {φ η : ℝ} (hφ : 1 < |φ|) (hφη : φ ≠ η) {u π : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u)
    (hub : BoundedProc u) (hπb : BoundedProc π) (hπ : ∀ t, 𝔼.E t (π (t + 1)) = φ • π t + u t) :
    π = fun t => (-(φ - η)⁻¹) • u t := by
  obtain ⟨M, hM⟩ := hπb
  obtain ⟨K, hK⟩ := hub
  have hδ : (fun t => π t - (-(φ - η)⁻¹) • u t) = 0 := by
    refine zero_of_E_succ_eq_smul 𝔼 hφ ⟨M + |(φ - η)⁻¹| * K, fun t ω => ?_⟩ (fun t => ?_)
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_sub _ _).trans (add_le_add (hM t ω) ?_)
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hK t ω) (abs_nonneg _)
    · rw [map_sub, hπ t, nk_solution 𝔼 hφη hu t]
      rw [smul_sub]
      abel
  funext t
  have h : π t - (-(φ - η)⁻¹) • u t = 0 := congrFun hδ t
  exact sub_eq_zero.mp h

/-- Cochrane (2023), (16.15)–(16.18), p. 371: in the new-Keynesian equilibrium the observables
are `i_t = ηπ_t`, `π_{t+1} = ηπ_t − ε_{t+1}/(φ − η)` and `ΔE_{t+1}π_{t+1} = −ε_{t+1}/(φ − η)`,
where `ε_{t+1} = u_{t+1} − ηu_t`; `φ` enters only through the shock scaling. -/
theorem nk_observables {φ η : ℝ} (hφη : φ ≠ η) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) (t : ℕ) :
    φ • ((-(φ - η)⁻¹) • u t) + u t = η • ((-(φ - η)⁻¹) • u t) ∧
      (-(φ - η)⁻¹) • u (t + 1) =
        η • ((-(φ - η)⁻¹) • u t) - (φ - η)⁻¹ • (u (t + 1) - η • u t) ∧
      surprise 𝔼 (fun t => (-(φ - η)⁻¹) • u t) t = -((φ - η)⁻¹ • (u (t + 1) - η • u t)) := by
  have h : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  refine ⟨?_, ?_, ?_⟩
  · funext ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    ring
  · funext ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · rw [surprise, map_smul, hu.2 t]
    funext ω
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), §16.6, p. 372 (observational equivalence of the AR(1) example): a
fiscal-theory equilibrium with rule `i_t = θπ_t`, `θ = η` (so `E_t π_{t+1} = ηπ_t`) and fiscal
shock `ΔE_{t+1}π_{t+1} = −ε^Σ_{s,t+1}`, `ε^Σ_{s,t+1} = ε_{t+1}/(φ − η)`, starting from the same
`π_0`, produces exactly the new-Keynesian inflation process. -/
theorem ftpl_eq_nk {φ η : ℝ} (hφη : φ ≠ η) {u π : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u)
    (hE : ∀ t, 𝔼.E t (π (t + 1)) = η • π t)
    (hs : ∀ t, surprise 𝔼 π t = -((φ - η)⁻¹ • (u (t + 1) - η • u t)))
    (h0 : π 0 = (-(φ - η)⁻¹) • u 0) : π = fun t => (-(φ - η)⁻¹) • u t := by
  funext t
  induction t with
  | zero => exact h0
  | succ t ih =>
    have h1 := hs t
    rw [surprise, hE t, ih] at h1
    rw [sub_eq_iff_eq_add.mp h1, (nk_observables 𝔼 hφη hu t).2.1]
    abel

/-- Cochrane (2023), §16.6, p. 372 ("after the central bank engineers a monetary contraction,
fiscal policy 'passively' raises surpluses by `ε^Σ_{s,t+1} = −ΔE_{t+1}π_{t+1} = ε_{t+1}/(φ − η)`"):
in the new-Keynesian equilibrium, any surplus and debt paths satisfying the flow condition and
the transversality condition carry the news `ΔE_{t+1} ∑ ρʲ s̃_{t+1+j} = ε_{t+1}/(φ − η)`. -/
theorem nk_passive_fiscal_news {ρ φ η M : ℝ} (hρ : |ρ| < 1) (hφη : φ ≠ η)
    {u i v s : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hF : Fisher 𝔼 i (fun t => (-(φ - η)⁻¹) • u t))
    (hflow : Flow ρ v i (fun t => (-(φ - η)⁻¹) • u t) s) (hv : 𝔼.Adapted v)
    (htvc : TVC 𝔼 ρ v) (t : ℕ) :
    innov 𝔼 t (pvExPost ρ s t) = (φ - η)⁻¹ • (u (t + 1) - η • u t) := by
  have h1 := unexpected_inflation_news 𝔼 hρ hs hsa hF hflow hv htvc t
  rw [(nk_observables 𝔼 hφη hu t).2.2] at h1
  exact (neg_inj.mp h1).symm

end Cochrane.ObservationalEquivalence.Equivalence
