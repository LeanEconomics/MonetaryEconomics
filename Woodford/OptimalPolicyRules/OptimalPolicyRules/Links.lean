/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InflationInertiaRepresentations
import OptimalPolicyRules.InflationInertiaRules
import OptimalPolicyRules.IRulePredetermined
import OptimalPolicyRules.IRuleBasic
import OptimalPolicyRules.InflTargetInertia
import OptimalPolicyRules.InflTargetPredetermined

/-!
# Links between the parts of Chapter 8

Woodford (2003), *Interest and Prices*, Chapter 8, §3.1–§3.3 (pp. 582–606) and Appendix G.4–G.10
(pp. 721–745).

The chapter was formalised in separate parts. This module proves that the parts fit together.

* **Proposition 8.7 discharges the root hypotheses** of Propositions 8.9–8.11:
  `inertiaRoots_of_standing` (the canonical roots of `CubicRoots` satisfy `InertiaRoots`), hence
  the unconditional `prop_8_9_ruleI_standing`, `prop_8_9_ruleII_standing`,
  `prop_8_9_ruleIII_standing`, `prop_8_10_standing`, `prop_8_11_standing`, the limits
  `prop_8_9_ruleI_limit_standing`, `prop_8_11_limit_zero_standing` (`γ → 0`),
  `prop_8_9_ruleIII_limit_one_standing`, `prop_8_11_limit_one_standing` (`γ → 1`), and the
  numbers of Figures 8.3–8.5 for the actual roots (`gamma_bar_standing`,
  `fig_8_4_mean_horizon_standing`, `fig_8_4_abs_weight_ratio_standing`,
  `gamma_one_coeffs_standing`). Only parameter hypotheses remain.
* **The same objects**: `apoly_eq_apolyC`, `chi_eq_precip`, `modelDisc_eq_deltaG` (the two
  discriminants), `qtil_eq_qtilde`, `fbig_eq_fhat`, `euler_iff_euler` (the two Euler equations
  (3.21)), `ruleIReal_iff_kernelRule`, `ruleIIIReal_iff_kernelRule` (the rules (3.22)–(3.24) of
  Proposition 8.8 are the kernel rules of Proposition 8.9); `prop_8_8_kernelRuleIII` (Prop 8.8
  for the kernel form of Rule III) and `ruleIII_iff_targetRule` (Rule III commits to the same
  plans as the pure targeting rule (3.26)).
* **Predetermined decisions** (§3.3, pp. 604–606): Propositions 8.9–8.11 applied to the delayed
  expectation system `delay 𝔼 d`. `euler316_levels_iff` identifies (3.16) for an expectation
  system with the Euler equation (3.21) of Propositions 8.9–8.11; `prop_8_10_delay`,
  `prop_8_11_delay`, `eq316_delay_iff_target331` and `prop_8_9_ruleIII_delay` give the optimal
  rules (3.30)–(3.31) under predetermined decisions, as the book claims on p. 606.
* **Shared roots and workhorse**: `irule_roots_eq` (the roots of (3.10) in `IRuleBasic` are
  `QuadraticRoots.lam1, lam2`), `prev_eq_lagW`, `secondOrder_iff`, `ysol_eq_secondOrderSol` (the
  two formalisations of the second-order workhorse have the same unique bounded solution),
  `foc34_delay_zero`, `foc35_delay_zero` ((3.4'), (3.5') with `d = 0` are (3.4), (3.5)).
* **The model equations**: `as_basic_iff`, `as_inertia_zero_iff`, `is_inertia_iff`, `asInd_iff`
  (the corrected (2.6) of §2.1 and §3.2 are the same relation), `as_predetermined_zero_iff`
  ((2.28) with `d = 0`).
* **The basic model as the `γ = 0` case** (Proposition 8.5 vs. p. 593):
  `euler_gamma_zero_iff_rule` and `inertia_system_gamma_zero`: at `γ = 0` the equilibrium under
  rule (3.7) of `IRuleBasic` solves the rule system (2.6), (3.1), (3.16) of
  `InflationInertiaRules`, and (faithful expectations with the pull-out property) it is the only
  bounded solution with its history. This supplies the existence half that the `γ > 0`
  determinacy result `InflationInertiaRules.rule_system_determinate` leaves as a hypothesis.
-/

namespace Woodford.OptimalPolicyRules.Links

open Filter Topology
open InflationInertiaRepresentations
open CubicRoots (lam1 lam2 lam3 lam2r lam3r sumS prodP discQ)
open CubicRoots.Assumptions (Standing)

variable {β γ κ σ : ℝ}

/-! ### Proposition 8.7 discharges the root hypotheses -/

/-- **Proposition 8.7 supplies the hypotheses of Propositions 8.9–8.11** (Woodford (2003),
p. 594, App. G.6, pp. 724–727): under `σ, κ > 0`, `0 < β < 1`, `0 < γ ≤ 1`, the canonical roots
`λ₁, λ₂, λ₃` of the cubic (3.17) satisfy `InertiaRoots`: `0 < λ₁ < 1`, `λ₂, λ₃` real above one
or a conjugate pair with real part above one, and the Vieta relations (G.18)–(G.20). -/
theorem inertiaRoots_of_standing (h : Standing β γ κ σ) :
    InertiaRoots β γ κ σ (lam1 β γ κ σ) (lam2 β γ κ σ) (lam3 β γ κ σ) := by
  refine ⟨(CubicRoots.lam1_spec h).1, (CubicRoots.lam1_spec h).2.1, ?_, CubicRoots.vieta_G20 h,
    ?_, ?_⟩
  · rcases le_or_gt 0 (discQ β γ κ σ) with hD | hD
    · left
      rw [CubicRoots.lam2_eq_ofReal rfl hD, CubicRoots.lam3_eq_ofReal rfl hD]
      exact ⟨Complex.ofReal_im _, Complex.ofReal_im _,
        by rw [Complex.ofReal_re]; exact CubicRoots.one_lt_lam2r h,
        by rw [Complex.ofReal_re]; exact CubicRoots.one_lt_lam3r h⟩
    · right
      exact ⟨CubicRoots.lam3_eq_conj hD, (CubicRoots.lam2_complex h hD).2.2⟩
  · rw [CubicRoots.vieta_G18_pair h]
    unfold CubicRoots.coefA2
    push_cast
    ring
  · have e' : ((β * γ * lam1 β γ κ σ * prodP β γ κ σ : ℝ) : ℂ) = ((β⁻¹ : ℝ) : ℂ) := by
      rw [CubicRoots.vieta_const h]
    push_cast at e'
    rw [mul_assoc (lam1 β γ κ σ : ℂ), CubicRoots.lam2_mul_lam3]
    linear_combination e' - Complex.ofReal_inv β

/-- Woodford (2003), Proposition 8.7, p. 594, three real roots (`S² − 4P₂₃ ≥ 0`): the real
canonical roots `λ₁, λ₂ ≤ λ₃` satisfy `InertiaRoots`. -/
theorem inertiaRoots_real (h : Standing β γ κ σ) (hD : 0 ≤ discQ β γ κ σ) :
    InertiaRoots β γ κ σ (lam1 β γ κ σ) (lam2r β γ κ σ : ℂ) (lam3r β γ κ σ : ℂ) := by
  have := inertiaRoots_of_standing h
  rwa [CubicRoots.lam2_eq_ofReal rfl hD, CubicRoots.lam3_eq_ofReal rfl hD] at this

/-- Woodford (2003), (G.20), p. 725: `s = λ₂ + λ₃` of `InflationInertiaRepresentations` is the
`S` of `CubicRoots` for the canonical roots. -/
@[simp] theorem sR_canonical (β γ κ σ : ℝ) :
    sR (lam2 β γ κ σ) (lam3 β γ κ σ) = sumS β γ κ σ := by
  unfold sR
  rw [CubicRoots.lam2_add_lam3, Complex.ofReal_re]

/-- Woodford (2003), (G.18), p. 725: `p = λ₂λ₃` of `InflationInertiaRepresentations` is the
`P₂₃` of `CubicRoots` for the canonical roots. -/
@[simp] theorem pR_canonical (β γ κ σ : ℝ) :
    pR (lam2 β γ κ σ) (lam3 β γ κ σ) = prodP β γ κ σ := by
  unfold pR
  rw [CubicRoots.lam2_mul_lam3, Complex.ofReal_re]

/-- Woodford (2003), (G.20), p. 725, real roots: `λ₂ + λ₃ = S`. -/
theorem sR_real (β γ κ σ : ℝ) (hD : 0 ≤ discQ β γ κ σ) :
    sR (lam2r β γ κ σ : ℂ) (lam3r β γ κ σ : ℂ) = sumS β γ κ σ := by
  rw [← CubicRoots.lam2_eq_ofReal rfl hD, ← CubicRoots.lam3_eq_ofReal rfl hD, sR_canonical]

/-- Woodford (2003), (G.18), p. 725, real roots: `λ₂λ₃ = P₂₃`. -/
theorem pR_real (β γ κ σ : ℝ) (hD : 0 ≤ discQ β γ κ σ) :
    pR (lam2r β γ κ σ : ℂ) (lam3r β γ κ σ : ℂ) = prodP β γ κ σ := by
  rw [← CubicRoots.lam2_eq_ofReal rfl hD, ← CubicRoots.lam3_eq_ofReal rfl hD, pR_canonical]

/-! ### The same polynomials and discriminants -/

/-- Woodford (2003), (3.17), p. 593: the cubic `A(z)` of `InflationInertiaRepresentations` is the
cubic `ApolyC` of `CubicRoots`. -/
theorem apoly_eq_apolyC (β γ κ σ : ℝ) (z : ℂ) :
    Apoly β γ κ σ z = CubicRoots.ApolyC β γ κ σ z := by
  unfold Apoly CubicRoots.ApolyC CubicRoots.coefA0 CubicRoots.coefA1 CubicRoots.coefA2
    CubicRoots.coefA3
  push_cast
  ring

/-- Woodford (2003), (G.17)–(G.18), p. 724, and App. G.6, p. 725: the characteristic polynomial
`χ_γ(λ) = λ³A(λ⁻¹)` of `InflationInertiaRepresentations` is the reciprocal cubic `P(λ)` of
`CubicRoots`. -/
theorem chi_eq_precip (β γ κ σ l : ℝ) : chi β γ κ σ l = CubicRoots.Precip β γ κ σ l := by
  unfold chi CubicRoots.Precip CubicRoots.coefA2
  ring

/-- Woodford (2003), App. G.6, pp. 726–727: the cubic discriminant of `χ_γ` used in
`InflationInertiaRepresentations` (`modelDisc`) and the book's `Δ(γ) = 27B₀² + 4B₁³` used in
`CubicRoots` (`deltaG`) differ by the negative factor `−β⁻⁴`, so they have opposite signs. -/
theorem modelDisc_eq_deltaG (hβ : β ≠ 0) :
    modelDisc β γ κ σ = -(β⁻¹) ^ 4 * CubicRoots.deltaG β γ κ σ := by
  unfold modelDisc cubicDisc CubicRoots.deltaG CubicRoots.depB0 CubicRoots.depB1
    CubicRoots.coefA0 CubicRoots.coefA1 CubicRoots.coefA2 CubicRoots.coefA3
  field_simp
  ring

/-! ### Propositions 8.9–8.11 without root hypotheses -/

/-- Woodford (2003), (3.24), p. 595: the Rule III forecast kernel `½(λ₂^{−j−1} + λ₃^{−j−1})` for
the canonical roots of Proposition 8.7. -/
noncomputable abbrev wIII (β γ κ σ : ℝ) : ℕ → ℝ := ruleIIIker (sumS β γ κ σ) (prodP β γ κ σ)

/-- Woodford (2003), (3.26), p. 601: the double-forward-inverse kernel
`K_j = ∑_{k≤j} λ₂^{−k}λ₃^{−(j−k)}` for the canonical roots of Proposition 8.7. -/
noncomputable abbrev kIII (β γ κ σ : ℝ) : ℕ → ℝ := Kker (sumS β γ κ σ) (prodP β γ κ σ)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- **Proposition 8.10, unconditional** (Woodford (2003), p. 601; App. G.9, pp. 737–739): under
the standing assumptions of Proposition 8.7 only, a pair of bounded adapted processes
`{ı̂_t, f̂_t}` satisfies the pure targeting rule (3.26) with the canonical roots at all dates
`t ≥ t₀` iff it satisfies the Euler equation (3.21) at those dates. -/
theorem prop_8_10_standing (h : Standing β γ κ σ) {i f : ℕ → Ω → ℝ} (hib : BoundedProc i)
    (hia : 𝔼.Adapted i) (hfb : BoundedProc f) (hfa : 𝔼.Adapted f) {t0 : ℕ} (ht0 : 2 ≤ t0) :
    (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ i f t) ↔
      (∀ t, t0 ≤ t → TargetRule 𝔼 β γ (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ) i f t) := by
  have := prop_8_10 𝔼 h.beta_pos h.gamma_pos (inertiaRoots_of_standing h) hib hia hfb hfa ht0
  simpa only [sR_canonical, pR_canonical] using this

/-- **Proposition 8.9 for Rule III, unconditional** (Woodford (2003), p. 597; App. G.8,
pp. 735–737): under the standing assumptions and `λₓ, λᵢ > 0`, Rule III (3.24) with the
canonical roots (real or a complex pair) is equivalent to the representation (3.25) with
`ρ₁ > 1`, `ρ₂ > 0`, `0 < θ_π ≤ φ_π`, `0 < θₓ = φₓ` and forecast weights summing to one. -/
theorem prop_8_9_ruleIII_standing {lx li : ℝ} (h : Standing β γ κ σ) (hlx : 0 < lx)
    (hli : 0 < li) {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl) (hπa : 𝔼.Adapted infl)
    (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) :
    (∀ n, KernelRule 𝔼 (lam1 β γ κ σ) (sumS β γ κ σ / 2) (β * γ)⁻¹ (wIII β γ κ σ) i
        (fhat 𝔼 β γ κ σ lx li infl x) (n + 2) ↔
      Rep325 𝔼 (rho1 (lam1 β γ κ σ) (sumS β γ κ σ / 2)) (rho2 (lam1 β γ κ σ) (sumS β γ κ σ / 2))
        (phiPi β γ κ σ li (β * γ)⁻¹ (wIII β γ κ σ)) (phiX σ lx li (β * γ)⁻¹ (wIII β γ κ σ))
        (thetaPi γ κ σ li (β * γ)⁻¹ (wIII β γ κ σ)) (thetaX σ lx li (β * γ)⁻¹ (wIII β γ κ σ))
        (alphaPi β γ (wIII β γ κ σ)) (alphaX β γ (wIII β γ κ σ)) i infl x (n + 2)) ∧
    1 < rho1 (lam1 β γ κ σ) (sumS β γ κ σ / 2) ∧ 0 < rho2 (lam1 β γ κ σ) (sumS β γ κ σ / 2) ∧
    0 < thetaPi γ κ σ li (β * γ)⁻¹ (wIII β γ κ σ) ∧
    thetaPi γ κ σ li (β * γ)⁻¹ (wIII β γ κ σ) ≤ phiPi β γ κ σ li (β * γ)⁻¹ (wIII β γ κ σ) ∧
    0 < phiX σ lx li (β * γ)⁻¹ (wIII β γ κ σ) ∧
    thetaX σ lx li (β * γ)⁻¹ (wIII β γ κ σ) = phiX σ lx li (β * γ)⁻¹ (wIII β γ κ σ) ∧
    HasSum (alphaPi β γ (wIII β γ κ σ)) 1 ∧ HasSum (alphaX β γ (wIII β γ κ σ)) 1 := by
  have := prop_8_9_ruleIII 𝔼 (i := i) h.beta_pos h.beta_lt_one h.gamma_pos h.gamma_le_one
    h.kappa_pos
    h.sigma_pos hlx hli (inertiaRoots_of_standing h) hπb hπa hxb hxa
  simpa only [sR_canonical, pR_canonical] using this

/-- **Proposition 8.9 for Rule I, unconditional** (Woodford (2003), p. 597; App. G.8,
pp. 730–734): under the standing assumptions, `λₓ, λᵢ > 0` and three real roots
(`S² − 4P₂₃ ≥ 0`, i.e. `γ ≤ γ̄`), Rule I (3.22) has the representation (3.25) with `ρ₁ > 1`,
`ρ₂ > 0`, `0 < θ_π ≤ φ_π`, `0 < θₓ = φₓ` and forecast weights summing to one. -/
theorem prop_8_9_ruleI_standing {lx li : ℝ} (h : Standing β γ κ σ) (hD : 0 ≤ discQ β γ κ σ)
    (hlx : 0 < lx) (hli : 0 < li) {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl)
    (hπa : 𝔼.Adapted infl) (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) :
    (∀ n, KernelRule 𝔼 (lam1 β γ κ σ) (lam2r β γ κ σ) (β * γ * lam3r β γ κ σ)⁻¹
        (geomKer (lam3r β γ κ σ)⁻¹) i (fhat 𝔼 β γ κ σ lx li infl x) (n + 2) ↔
      Rep325 𝔼 (rho1 (lam1 β γ κ σ) (lam2r β γ κ σ)) (rho2 (lam1 β γ κ σ) (lam2r β γ κ σ))
        (phiPi β γ κ σ li (β * γ * lam3r β γ κ σ)⁻¹ (geomKer (lam3r β γ κ σ)⁻¹))
        (phiX σ lx li (β * γ * lam3r β γ κ σ)⁻¹ (geomKer (lam3r β γ κ σ)⁻¹))
        (thetaPi γ κ σ li (β * γ * lam3r β γ κ σ)⁻¹ (geomKer (lam3r β γ κ σ)⁻¹))
        (thetaX σ lx li (β * γ * lam3r β γ κ σ)⁻¹ (geomKer (lam3r β γ κ σ)⁻¹))
        (alphaPi β γ (geomKer (lam3r β γ κ σ)⁻¹)) (alphaX β γ (geomKer (lam3r β γ κ σ)⁻¹))
        i infl x (n + 2)) ∧
    1 < rho1 (lam1 β γ κ σ) (lam2r β γ κ σ) ∧ 0 < rho2 (lam1 β γ κ σ) (lam2r β γ κ σ) ∧
    0 < thetaPi γ κ σ li (β * γ * lam3r β γ κ σ)⁻¹ (geomKer (lam3r β γ κ σ)⁻¹) ∧
    thetaPi γ κ σ li (β * γ * lam3r β γ κ σ)⁻¹ (geomKer (lam3r β γ κ σ)⁻¹) ≤
      phiPi β γ κ σ li (β * γ * lam3r β γ κ σ)⁻¹ (geomKer (lam3r β γ κ σ)⁻¹) ∧
    0 < phiX σ lx li (β * γ * lam3r β γ κ σ)⁻¹ (geomKer (lam3r β γ κ σ)⁻¹) ∧
    thetaX σ lx li (β * γ * lam3r β γ κ σ)⁻¹ (geomKer (lam3r β γ κ σ)⁻¹) =
      phiX σ lx li (β * γ * lam3r β γ κ σ)⁻¹ (geomKer (lam3r β γ κ σ)⁻¹) ∧
    HasSum (alphaPi β γ (geomKer (lam3r β γ κ σ)⁻¹)) 1 ∧
    HasSum (alphaX β γ (geomKer (lam3r β γ κ σ)⁻¹)) 1 :=
  prop_8_9_ruleI 𝔼 h.beta_pos h.beta_lt_one h.gamma_pos h.gamma_le_one h.kappa_pos h.sigma_pos
    hlx hli (inertiaRoots_real h hD) hπb hπa hxb hxa

/-- **Proposition 8.9 for Rule II, unconditional** (Woodford (2003), p. 597; App. G.8,
pp. 734–735): under the standing assumptions, `λₓ, λᵢ > 0` and three real roots, Rule II (3.23)
has the representation (3.25) with `ρ₁ > 1`, `ρ₂ > 0`, `0 < θ_π ≤ φ_π`, `0 < θₓ = φₓ`. -/
theorem prop_8_9_ruleII_standing {lx li : ℝ} (h : Standing β γ κ σ) (hD : 0 ≤ discQ β γ κ σ)
    (hlx : 0 < lx) (hli : 0 < li) {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl)
    (hπa : 𝔼.Adapted infl) (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) :
    (∀ n, KernelRule 𝔼 (lam1 β γ κ σ) (lam3r β γ κ σ) (β * γ * lam2r β γ κ σ)⁻¹
        (geomKer (lam2r β γ κ σ)⁻¹) i (fhat 𝔼 β γ κ σ lx li infl x) (n + 2) ↔
      Rep325 𝔼 (rho1 (lam1 β γ κ σ) (lam3r β γ κ σ)) (rho2 (lam1 β γ κ σ) (lam3r β γ κ σ))
        (phiPi β γ κ σ li (β * γ * lam2r β γ κ σ)⁻¹ (geomKer (lam2r β γ κ σ)⁻¹))
        (phiX σ lx li (β * γ * lam2r β γ κ σ)⁻¹ (geomKer (lam2r β γ κ σ)⁻¹))
        (thetaPi γ κ σ li (β * γ * lam2r β γ κ σ)⁻¹ (geomKer (lam2r β γ κ σ)⁻¹))
        (thetaX σ lx li (β * γ * lam2r β γ κ σ)⁻¹ (geomKer (lam2r β γ κ σ)⁻¹))
        (alphaPi β γ (geomKer (lam2r β γ κ σ)⁻¹)) (alphaX β γ (geomKer (lam2r β γ κ σ)⁻¹))
        i infl x (n + 2)) ∧
    1 < rho1 (lam1 β γ κ σ) (lam3r β γ κ σ) ∧ 0 < rho2 (lam1 β γ κ σ) (lam3r β γ κ σ) ∧
    0 < thetaPi γ κ σ li (β * γ * lam2r β γ κ σ)⁻¹ (geomKer (lam2r β γ κ σ)⁻¹) ∧
    thetaPi γ κ σ li (β * γ * lam2r β γ κ σ)⁻¹ (geomKer (lam2r β γ κ σ)⁻¹) ≤
      phiPi β γ κ σ li (β * γ * lam2r β γ κ σ)⁻¹ (geomKer (lam2r β γ κ σ)⁻¹) ∧
    0 < phiX σ lx li (β * γ * lam2r β γ κ σ)⁻¹ (geomKer (lam2r β γ κ σ)⁻¹) ∧
    thetaX σ lx li (β * γ * lam2r β γ κ σ)⁻¹ (geomKer (lam2r β γ κ σ)⁻¹) =
      phiX σ lx li (β * γ * lam2r β γ κ σ)⁻¹ (geomKer (lam2r β γ κ σ)⁻¹) ∧
    HasSum (alphaPi β γ (geomKer (lam2r β γ κ σ)⁻¹)) 1 ∧
    HasSum (alphaX β γ (geomKer (lam2r β γ κ σ)⁻¹)) 1 :=
  prop_8_9_ruleII 𝔼 h.beta_pos h.beta_lt_one h.gamma_pos h.gamma_le_one h.kappa_pos h.sigma_pos
    hlx hli (inertiaRoots_real h hD) hπb hπa hxb hxa

/-- **Proposition 8.11, unconditional** (Woodford (2003), p. 602; App. G.10, pp. 739–745): under
the standing assumptions and `λₓ, λᵢ > 0`, the pure targeting rule (3.26) with the canonical
roots is equivalent to the target criterion (3.27) with `φₓ = θₓ > 0`, `0 < θ_π ≤ 1`,
`θᵢ, θ_Δ > 0` and forecast weights summing to one. -/
theorem prop_8_11_standing {lx li : ℝ} (h : Standing β γ κ σ) (hlx : 0 < lx) (hli : 0 < li)
    {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl) (hπa : 𝔼.Adapted infl)
    (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) :
    (∀ n, TargetRule 𝔼 β γ (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ) i
        (fhat 𝔼 β γ κ σ lx li infl x) (n + 2) ↔
      Rep327 𝔼 (phiX327 β γ κ lx (sumS β γ κ σ) (prodP β γ κ σ))
        (thetaPi327 β γ (sumS β γ κ σ) (prodP β γ κ σ))
        (thetaX327 β γ κ lx (sumS β γ κ σ) (prodP β γ κ σ))
        (thetaI327 β γ κ σ li (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ))
        (thetaD327 β γ κ σ li (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ))
        (alphaPi β γ (kIII β γ κ σ)) (alphaX β γ (kIII β γ κ σ)) i infl x (n + 2)) ∧
    thetaX327 β γ κ lx (sumS β γ κ σ) (prodP β γ κ σ) =
      phiX327 β γ κ lx (sumS β γ κ σ) (prodP β γ κ σ) ∧
    0 < phiX327 β γ κ lx (sumS β γ κ σ) (prodP β γ κ σ) ∧
    0 < thetaPi327 β γ (sumS β γ κ σ) (prodP β γ κ σ) ∧
    thetaPi327 β γ (sumS β γ κ σ) (prodP β γ κ σ) ≤ 1 ∧
    0 < thetaI327 β γ κ σ li (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ) ∧
    0 < thetaD327 β γ κ σ li (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ) ∧
    HasSum (alphaPi β γ (kIII β γ κ σ)) 1 ∧ HasSum (alphaX β γ (kIII β γ κ σ)) 1 := by
  have := prop_8_11 𝔼 (i := i) h.beta_pos h.beta_lt_one h.gamma_pos h.gamma_le_one h.kappa_pos
    h.sigma_pos hlx hli (inertiaRoots_of_standing h) hπb hπa hxb hxa
  simpa only [sR_canonical, pR_canonical] using this

/-! ### The limits `γ → 0` and `γ → 1` for the actual roots -/

/-- Woodford (2003), Proposition 8.7 and Lemma G.2: for every `0 < γ < γ₀` (some `γ₀ ∈ (0, 1]`)
the canonical roots are three distinct reals, satisfy `InertiaRoots` in real form, and
`λ₂ ≤ λ₃`. -/
theorem exists_real_family (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ γ0 : ℝ, 0 < γ0 ∧ γ0 ≤ 1 ∧ ∀ γ ∈ Set.Ioo 0 γ0,
      InertiaRoots β γ κ σ (lam1 β γ κ σ) (lam2r β γ κ σ : ℂ) (lam3r β γ κ σ : ℂ) := by
  obtain ⟨ε, hε, hsmall⟩ := CubicRoots.three_real_roots_small_gamma hσ hκ hβ0 hβ1
  refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, fun γ hγ => ?_⟩
  have hS : Standing β γ κ σ :=
    ⟨hσ, hκ, hβ0, hβ1, hγ.1, (hγ.2.trans_le (min_le_right _ _)).le⟩
  obtain ⟨-, h2, h3, -, -⟩ := hsmall γ hγ.1 (hγ.2.trans_le (min_le_left _ _))
  have := inertiaRoots_of_standing hS
  rwa [h2, h3] at this

/-- Woodford (2003), (3.10), p. 588, and Lemma G.2: the roots `μ₁ < μ₂` of the `γ = 0`
quadratic satisfy the relations used by the limit theorems of `InflationInertiaRepresentations`:
`μ₁ + μ₂ = 1 + β⁻¹(1 + κσ)`, `μ₁μ₂ = β⁻¹`. -/
theorem mu_relations (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) :
    CubicRoots.mu1 β κ σ + CubicRoots.mu2 β κ σ = 1 + (1 + κ * σ) / β ∧
      CubicRoots.mu1 β κ σ * CubicRoots.mu2 β κ σ = β⁻¹ ∧
      CubicRoots.mu1 β κ σ < CubicRoots.mu2 β κ σ := by
  have hκσ := mul_pos hκ hσ
  obtain ⟨-, h1, h2⟩ := CubicRoots.mu_bounds hβ0 hκσ
  refine ⟨?_, CubicRoots.mu_prod hβ0 hκσ, h1.trans h2⟩
  rw [CubicRoots.mu_sum hβ0]
  field_simp
  ring

/-- **Proposition 8.9, `γ → 0`, for the actual roots** (Woodford (2003), p. 597, App. G.8,
p. 734, and p. 596 with fn 44): along the canonical (real) roots, as `γ → 0⁺`, `θ_π → 0`,
`φ_π → κσ/λᵢ > 0`, `φₓ → 4λₓσ/λᵢ`, and Rule I tends to (3.10): `(βγλ₃)⁻¹ → 1`,
`ρ₁ → 1 + κσ/β`, `ρ₂ → β⁻¹`. -/
theorem prop_8_9_ruleI_limit_standing {lx li : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hli : 0 < li) :
    Tendsto (fun γ => thetaPi γ κ σ li (β * γ * lam3r β γ κ σ)⁻¹ (geomKer (lam3r β γ κ σ)⁻¹))
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun γ => phiPi β γ κ σ li (β * γ * lam3r β γ κ σ)⁻¹ (geomKer (lam3r β γ κ σ)⁻¹))
      (𝓝[>] 0) (𝓝 (κ * σ / li)) ∧ 0 < κ * σ / li ∧
    Tendsto (fun γ => phiX σ lx li (β * γ * lam3r β γ κ σ)⁻¹ (geomKer (lam3r β γ κ σ)⁻¹))
      (𝓝[>] 0) (𝓝 (4 * lx * σ / li)) ∧
    Tendsto (fun γ => (β * γ * lam3r β γ κ σ)⁻¹) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun γ => rho1 (lam1 β γ κ σ) (lam2r β γ κ σ)) (𝓝[>] 0) (𝓝 (1 + κ * σ / β)) ∧
    Tendsto (fun γ => rho2 (lam1 β γ κ σ) (lam2r β γ κ σ)) (𝓝[>] 0) (𝓝 β⁻¹) := by
  obtain ⟨γ0, h0, h1, hR⟩ := exists_real_family hσ hκ hβ0 hβ1
  obtain ⟨hm1, hm2, hm12⟩ := mu_relations hσ hκ hβ0
  exact prop_8_9_ruleI_limit (lx := lx) hβ0 hκ hσ hli h0 h1 hR
    (fun γ _ => CubicRoots.lam2r_le_lam3r) hm1 hm2 hm12

/-- **Proposition 8.11, `γ → 0`, for the actual roots** (Woodford (2003), p. 602; App. G.10,
p. 743): along the canonical roots, as `γ → 0⁺`, `S_π → (1 − 1/μ₂)⁻¹`, `θ_π → 0`, and `φₓ = θₓ`,
`θᵢ`, `θ_Δ` and the weights approach the values of the target criterion (3.13), where
`μ₁ < μ₂` are the roots of (3.10). -/
theorem prop_8_11_limit_zero_standing {lx li : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hli : 0 < li) :
    Tendsto (fun γ => SpiK β γ (kIII β γ κ σ)) (𝓝[>] 0)
      (𝓝 (1 - (CubicRoots.mu2 β κ σ)⁻¹)⁻¹) ∧
    Tendsto (fun γ => thetaPi327 β γ (sumS β γ κ σ) (prodP β γ κ σ)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun γ => phiX327 β γ κ lx (sumS β γ κ σ) (prodP β γ κ σ)) (𝓝[>] 0)
      (𝓝 (4 * (1 - (CubicRoots.mu2 β κ σ)⁻¹) * lx / κ)) ∧
    Tendsto (fun γ => thetaI327 β γ κ σ li (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ))
      (𝓝[>] 0) (𝓝 (CubicRoots.mu2 β κ σ * (1 - CubicRoots.mu1 β κ σ) *
        (1 - (CubicRoots.mu2 β κ σ)⁻¹) * li / (κ * σ))) ∧
    Tendsto (fun γ => thetaD327 β γ κ σ li (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ))
      (𝓝[>] 0) (𝓝 (CubicRoots.mu1 β κ σ * CubicRoots.mu2 β κ σ *
        (1 - (CubicRoots.mu2 β κ σ)⁻¹) * li / (κ * σ))) ∧
    (∀ j, Tendsto (fun γ => alphaPi β γ (kIII β γ κ σ) j) (𝓝[>] 0)
      (𝓝 ((1 - (CubicRoots.mu2 β κ σ)⁻¹) * (CubicRoots.mu2 β κ σ)⁻¹ ^ j))) ∧
    (∀ j, Tendsto (fun γ => alphaX β γ (kIII β γ κ σ) j) (𝓝[>] 0)
      (𝓝 ((1 - (CubicRoots.mu2 β κ σ)⁻¹) * (CubicRoots.mu2 β κ σ)⁻¹ ^ j))) := by
  obtain ⟨γ0, h0, h1, hR⟩ := exists_real_family hσ hκ hβ0 hβ1
  obtain ⟨hm1, hm2, hm12⟩ := mu_relations hσ hκ hβ0
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := prop_8_11_limit_zero (lx := lx) hβ0 hκ hσ hli h0 h1 hR
    (fun γ _ => CubicRoots.lam2r_le_lam3r) hm1 hm2 hm12
  have hev : ∀ᶠ γ in 𝓝[>] (0 : ℝ), sR (lam2r β γ κ σ : ℂ) (lam3r β γ κ σ : ℂ) = sumS β γ κ σ ∧
      pR (lam2r β γ κ σ : ℂ) (lam3r β γ κ σ : ℂ) = prodP β γ κ σ := by
    filter_upwards [CubicRoots.eventually_discQ_pos hσ hκ hβ0 hβ1] with γ hD
    exact ⟨sR_real _ _ _ _ hD.le, pR_real _ _ _ _ hD.le⟩
  refine ⟨t1.congr' ?_, t2.congr' ?_, t3.congr' ?_, t4.congr' ?_, t5.congr' ?_,
    fun j => (t6 j).congr' ?_, fun j => (t7 j).congr' ?_⟩ <;>
  · filter_upwards [hev] with γ hγ
    simp only [hγ.1, hγ.2]

/-- Woodford (2003), Proposition 8.7: for every `γ ∈ (0, 1]` the canonical roots satisfy
`InertiaRoots` (the family used by the `γ → 1` limits). -/
theorem roots_on_Ioc (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ γ ∈ Set.Ioc (0 : ℝ) 1,
      InertiaRoots β γ κ σ (lam1 β γ κ σ) (lam2 β γ κ σ) (lam3 β γ κ σ) :=
  fun _ hγ => inertiaRoots_of_standing ⟨hσ, hκ, hβ0, hβ1, hγ.1, hγ.2⟩

/-- **Proposition 8.9, `γ → 1`, Rule III, for the actual roots** (Woodford (2003), p. 597;
App. G.8, p. 737): as `γ → 1⁻`, the Rule III coefficients `θ_π` and `φ_π` converge to the same
positive limit `(κσ/(λᵢβ))(S/P₂₃)/2` evaluated at `γ = 1`. -/
theorem prop_8_9_ruleIII_limit_one_standing {li : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hli : 0 < li) :
    Tendsto (fun γ => thetaPi γ κ σ li (β * γ)⁻¹ (wIII β γ κ σ)) (𝓝[<] 1)
      (𝓝 (κ * σ / (li * β) * (sumS β 1 κ σ / prodP β 1 κ σ / 2))) ∧
    Tendsto (fun γ => phiPi β γ κ σ li (β * γ)⁻¹ (wIII β γ κ σ)) (𝓝[<] 1)
      (𝓝 (κ * σ / (li * β) * (sumS β 1 κ σ / prodP β 1 κ σ / 2))) ∧
    0 < κ * σ / (li * β) * (sumS β 1 κ σ / prodP β 1 κ σ / 2) := by
  have := prop_8_9_ruleIII_limit_one (L1 := fun γ => lam1 β γ κ σ) (L2 := fun γ => lam2 β γ κ σ)
    (L3 := fun γ => lam3 β γ κ σ) hβ0 hκ hσ hli zero_lt_one le_rfl (roots_on_Ioc hσ hκ hβ0 hβ1)
  simpa only [sR_canonical, pR_canonical] using this

/-- **Proposition 8.11, `γ → 1`, for the actual roots** (Woodford (2003), p. 602; App. G.10,
p. 743): as `γ → 1⁻`, `S_π → 1`, `θ_π → 1` and `φₓ = θₓ → 4λₓ/κ`. -/
theorem prop_8_11_limit_one_standing {lx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) :
    Tendsto (fun γ => SpiK β γ (kIII β γ κ σ)) (𝓝[<] 1) (𝓝 1) ∧
    Tendsto (fun γ => thetaPi327 β γ (sumS β γ κ σ) (prodP β γ κ σ)) (𝓝[<] 1) (𝓝 1) ∧
    Tendsto (fun γ => phiX327 β γ κ lx (sumS β γ κ σ) (prodP β γ κ σ)) (𝓝[<] 1)
      (𝓝 (4 * lx / κ)) := by
  have := prop_8_11_limit_one (lx := lx) (L1 := fun γ => lam1 β γ κ σ)
    (L2 := fun γ => lam2 β γ κ σ) (L3 := fun γ => lam3 β γ κ σ) hβ0 hκ zero_lt_one le_rfl
    (roots_on_Ioc hσ hκ hβ0 hβ1)
  simpa only [sR_canonical, pR_canonical] using this

/-! ### Figures 8.3–8.5 for the actual roots -/

/-- Woodford (2003), Table 6.1, p. 431: `β = 0.99`, `γ = 1` with `κ, σ > 0` satisfy the standing
assumptions of Proposition 8.7. -/
theorem standing_table61 (hκ : 0 < κ) (hσ : 0 < σ) : Standing 0.99 1 κ σ :=
  ⟨hσ, hκ, by norm_num, by norm_num, one_pos, le_rfl⟩

/-- **Figure 8.3 for the actual roots** (Woodford (2003), p. 599): at the Table 6.1 values
`β = 0.99`, `κσ = 0.15`, the canonical roots `λ₂, λ₃` of Proposition 8.7 are real for
`γ ∈ (0, 0.353]` and a genuinely complex conjugate pair for `γ ∈ [0.354, 1]`, so `γ̄ ≈ .35`. -/
theorem gamma_bar_standing (hκ : 0 < κ) (hσ : 0 < σ) (hκσ : κ * σ = 0.15) :
    (∀ γ ∈ Set.Ioc (0 : ℝ) 0.353,
      (lam2 0.99 γ κ σ).im = 0 ∧ (lam3 0.99 γ κ σ).im = 0) ∧
    (∀ γ ∈ Set.Icc (0.354 : ℝ) 1,
      lam3 0.99 γ κ σ = (starRingEnd ℂ) (lam2 0.99 γ κ σ) ∧ (lam2 0.99 γ κ σ).im ≠ 0) := by
  obtain ⟨h1, h2⟩ := gamma_bar_table61 hκσ
  refine ⟨fun γ hγ => h1 γ hγ _ _ _ (inertiaRoots_of_standing
    ⟨hσ, hκ, by norm_num, by norm_num, hγ.1, hγ.2.trans (by norm_num)⟩),
    fun γ hγ => h2 γ hγ _ _ _ (inertiaRoots_of_standing
    ⟨hσ, hκ, by norm_num, by norm_num, lt_of_lt_of_le (by norm_num) hγ.1, hγ.2⟩)⟩

/-- **Figure 8.4, mean horizon, for the actual roots** (Woodford (2003), p. 600): at the
Table 6.1 values and `γ = 1`, the stable root lies in `(0.564, 0.565)` and the mean horizon of
the Rule III forecast weights lies in `(2.2, 2.25)`. -/
theorem fig_8_4_mean_horizon_standing (hκ : 0 < κ) (hσ : 0 < σ) (hκσ : κ * σ = 0.15) :
    0.564 < lam1 0.99 1 κ σ ∧ lam1 0.99 1 κ σ < 0.565 ∧
      alphaX 0.99 1 (wIII 0.99 1 κ σ) = alphaPi 0.99 1 (wIII 0.99 1 κ σ) ∧
      2.2 < meanHorizon (alphaPi 0.99 1 (wIII 0.99 1 κ σ)) ∧
      meanHorizon (alphaPi 0.99 1 (wIII 0.99 1 κ σ)) < 2.25 := by
  have := fig_8_4_mean_horizon hκσ (inertiaRoots_of_standing (standing_table61 hκ hσ))
  simpa only [sR_canonical, pR_canonical] using this

/-- **Figure 8.4, relative weight on future forecasts, for the actual roots** (Woodford (2003),
p. 600, "equal to only 0.39"): at the Table 6.1 values and `γ = 1`,
`0.386 < ∑_{j>0} |α_j| / α_0 < 0.389` for the Rule III weights. -/
theorem fig_8_4_abs_weight_ratio_standing (hκ : 0 < κ) (hσ : 0 < σ) (hκσ : κ * σ = 0.15) :
    0.386 < absWeightRatio (alphaPi 0.99 1 (wIII 0.99 1 κ σ)) ∧
      absWeightRatio (alphaPi 0.99 1 (wIII 0.99 1 κ σ)) < 0.389 := by
  have := fig_8_4_abs_weight_ratio hκσ (inertiaRoots_of_standing (standing_table61 hκ hσ))
  simpa only [sR_canonical, pR_canonical] using this

/-- **Figure 8.5 for the actual roots** (Woodford (2003), p. 603): at `γ = 1`, `S_π = 1`,
`θ_π = 1` and `φₓ = θₓ = 4λₓ/κ` for the target criterion (3.27). -/
theorem gamma_one_coeffs_standing {lx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) :
    SpiK β 1 (kIII β 1 κ σ) = 1 ∧ thetaPi327 β 1 (sumS β 1 κ σ) (prodP β 1 κ σ) = 1 ∧
      phiX327 β 1 κ lx (sumS β 1 κ σ) (prodP β 1 κ σ) = 4 * lx / κ := by
  have := (inertiaRoots_of_standing ⟨hσ, hκ, hβ0, hβ1, one_pos, le_rfl⟩).gamma_one_coeffs
    (lx := lx)
  simpa only [sR_canonical, pR_canonical] using this

/-! ### Proposition 8.8's rules are the kernel rules of Propositions 8.9–8.10 -/

/-- Woodford (2003), eq. (3.19), p. 593: `q̃` of `InflationInertiaRules` is `q̃` of
`InflationInertiaRepresentations`. -/
theorem qtil_eq_qtilde (γ κ σ lx li : ℝ) (π x : ℕ → Ω → ℝ) (k : ℕ) :
    InflationInertiaRules.qtil γ κ σ lx li π x k = qtilde γ κ σ lx li π x k := by
  funext ω
  simp only [InflationInertiaRules.qtil, qtilde, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    smul_eq_mul]

/-- Woodford (2003), eq. (3.18), p. 593: `f = q̃ − βγE q̃'` of `InflationInertiaRules` is `f̂` of
`InflationInertiaRepresentations`. -/
theorem fbig_eq_fhat (β γ κ σ lx li : ℝ) (π x : ℕ → Ω → ℝ) (k : ℕ) :
    InflationInertiaRules.fbig 𝔼 β γ κ σ lx li π x k = fhat 𝔼 β γ κ σ lx li π x k := by
  funext ω
  simp only [InflationInertiaRules.fbig, fhat, qtil_eq_qtilde, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]

/-- Woodford (2003), eq. (3.21), p. 594: for an adapted `ı̂`, the Euler equation of
`InflationInertiaRules` at `t` (date `t + 2`) is the Euler equation of
`InflationInertiaRepresentations` at date `t + 2`. -/
theorem euler_iff_euler {ı f : ℕ → Ω → ℝ} (hı : 𝔼.Adapted ı) (t : ℕ) :
    InflationInertiaRules.Euler 𝔼 β γ κ σ ı f t ↔ Euler 𝔼 β γ κ σ ı f (t + 2) := by
  have k1 : 𝔼.E (t + 2) (ı (t + 1)) = ı (t + 1) :=
    ForwardSolution.E_of_known 𝔼 (by omega) (hı _)
  have k0 : 𝔼.E (t + 2) (ı t) = ı t := ForwardSolution.E_of_known 𝔼 (by omega) (hı _)
  have hA : InflationInertiaRules.ALi β γ κ σ ı t = (β * γ) • ı (t + 3) +
      (-(1 + γ + β * γ)) • ı (t + 2) + CubicRoots.coefA2 β γ κ σ • ı (t + 1) +
      (-β⁻¹) • ı t := by
    funext ω
    simp only [InflationInertiaRules.ALi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold InflationInertiaRules.Euler Euler
  rw [hA, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, hı (t + 2), k1, k0,
    show t + 2 - 1 = t + 1 by omega, show t + 2 - 2 = t by omega,
    show t + 2 + 1 = t + 3 from rfl]
  unfold CubicRoots.coefA2
  constructor
  · intro h
    funext ω
    have := h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at this ⊢
    linear_combination this
  · intro h ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at this ⊢
    linear_combination this

/-- Woodford (2003), eq. (3.22), p. 595: the real-valued Rule I of Proposition 8.8 is the kernel
rule `(1 − λ₁L)(1 − r₂L)ı̂_n = (βγr₃)⁻¹ ∑ r₃^{−j} E_n f̂_{n+j}` of Proposition 8.9 (with the
geometric kernel). -/
theorem ruleIReal_iff_kernelRule (l1 r2 r3 : ℝ) (ı f : ℕ → Ω → ℝ) (t : ℕ) :
    InflationInertiaRules.RuleIReal 𝔼 β γ l1 r2 r3 ı f t ↔
      KernelRule 𝔼 l1 r2 (β * γ * r3)⁻¹ (geomKer r3⁻¹) ı f (t + 2) := by
  unfold InflationInertiaRules.RuleIReal KernelRule fwd geomKer
  rw [show t + 2 - 1 = t + 1 by omega, show t + 2 - 2 = t by omega]
  constructor
  · intro h
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact h ω
  · intro h ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this

/-- Woodford (2003), (3.24), p. 595: the real Rule III weights `ψⱼ` of Proposition 8.8 are
`(βγ)⁻¹` times the Rule III kernel `½(λ₂^{−j−1} + λ₃^{−j−1})` of Proposition 8.9. -/
theorem psiIII_re {l1 : ℝ} {l2 l3 : ℂ} (h : InertiaRoots β γ κ σ l1 l2 l3) (j : ℕ) :
    (InflationInertiaRules.psiIII β γ l2 l3 j).re =
      (β * γ)⁻¹ * ruleIIIker (sR l2 l3) (pR l2 l3) j := by
  have e : InflationInertiaRules.psiIII β γ l2 l3 j =
      (((β * γ)⁻¹ * ruleIIIker (sR l2 l3) (pR l2 l3) j : ℝ) : ℂ) := by
    push_cast
    rw [h.ruleIIIker_eq]
    unfold InflationInertiaRules.psiIII
    ring
  rw [e, Complex.ofReal_re]

/-- Woodford (2003), eq. (3.24), p. 595: the real-coefficient Rule III of Proposition 8.8 is the
kernel Rule III of Proposition 8.9, `(1 − λ₁L)(1 − ½(λ₂ + λ₃)L)ı̂_n = (βγ)⁻¹ ∑ w_j E_n f̂_{n+j}`. -/
theorem ruleIIIReal_iff_kernelRule {l1 : ℝ} {l2 l3 : ℂ} (h : InertiaRoots β γ κ σ l1 l2 l3)
    (ı f : ℕ → Ω → ℝ) (t : ℕ) :
    InflationInertiaRules.RuleIIIReal 𝔼 l1 (sR l2 l3)
        (fun j => (InflationInertiaRules.psiIII β γ l2 l3 j).re) ı f t ↔
      KernelRule 𝔼 l1 (sR l2 l3 / 2) (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) ı f
        (t + 2) := by
  unfold InflationInertiaRules.RuleIIIReal KernelRule fwd
  simp only [psiIII_re h, mul_assoc, tsum_mul_left]
  rw [show t + 2 - 1 = t + 1 by omega, show t + 2 - 2 = t by omega]
  constructor
  · intro h'
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h' ω
  · intro h' ω
    have := congrFun h' ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination this

/-- **Proposition 8.8 for the kernel form of Rule III** (Woodford (2003), p. 595; App. G.7): under
the standing assumptions, for bounded adapted `ı̂, f̂`, the Rule III of Proposition 8.9
(canonical roots, real coefficients, both cases) holds at all dates `n + 2`, `n ≥ t₀`, iff the
Euler equation (3.21) does. -/
theorem prop_8_8_kernelRuleIII (h : Standing β γ κ σ) {ı f : ℕ → Ω → ℝ} (hı : 𝔼.Adapted ı)
    (hf : 𝔼.Adapted f) (hıb : BoundedProc ı) (hfb : BoundedProc f) (t0 : ℕ) :
    (∀ t, t0 ≤ t → KernelRule 𝔼 (lam1 β γ κ σ) (sumS β γ κ σ / 2) (β * γ)⁻¹ (wIII β γ κ σ)
        ı f (t + 2)) ↔ (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ ı f (t + 2)) := by
  obtain ⟨Mı, hMı⟩ := hıb
  obtain ⟨Mf, hMf⟩ := hfb
  have hE := InflationInertiaRules.prop_8_8_ruleIII_real 𝔼 h hı hf hMı hMf t0
  have hR := fun t => ruleIIIReal_iff_kernelRule 𝔼 (inertiaRoots_of_standing h) ı f t
  simp only [sR_canonical, pR_canonical] at hR
  simp only [hR, euler_iff_euler 𝔼 hı] at hE
  exact hE

/-- **Rule III and the pure targeting rule (3.26) are the same commitment** (Woodford (2003),
Propositions 8.8 and 8.10, pp. 595 and 601): under the standing assumptions, for bounded adapted
`ı̂, f̂`, the real-coefficient Rule III of Proposition 8.8 holds at all dates `t + 2`, `t ≥ t₀`,
iff the pure targeting rule (3.26) of Proposition 8.10 holds at all dates `≥ t₀ + 2`. -/
theorem ruleIII_iff_targetRule (h : Standing β γ κ σ) {ı f : ℕ → Ω → ℝ} (hı : 𝔼.Adapted ı)
    (hf : 𝔼.Adapted f) (hıb : BoundedProc ı) (hfb : BoundedProc f) (t0 : ℕ) :
    (∀ t, t0 ≤ t → InflationInertiaRules.RuleIIIReal 𝔼 (lam1 β γ κ σ) (sumS β γ κ σ)
        (fun j => (InflationInertiaRules.psiIII β γ (lam2 β γ κ σ) (lam3 β γ κ σ) j).re) ı f t) ↔
      (∀ t, t0 + 2 ≤ t →
        TargetRule 𝔼 β γ (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ) ı f t) := by
  obtain ⟨Mı, hMı⟩ := hıb
  obtain ⟨Mf, hMf⟩ := hfb
  rw [InflationInertiaRules.prop_8_8_ruleIII_real 𝔼 h hı hf hMı hMf t0,
    ← prop_8_10_standing 𝔼 h ⟨Mı, hMı⟩ hı ⟨Mf, hMf⟩ hf (by omega : 2 ≤ t0 + 2)]
  constructor
  · intro H t ht
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t - 2, by omega⟩
    exact (euler_iff_euler 𝔼 hı n).mp (H n (by omega))
  · intro H t ht
    exact (euler_iff_euler 𝔼 hı t).mpr (H (t + 2) (by omega))

/-! ### Predetermined decisions: Propositions 8.9–8.11 for the delayed system (§3.3) -/

/-- Woodford (2003), (3.19), p. 593, and (3.29), p. 605: `q̃` of `IRulePredetermined` (written
with `π^{qd}`) is `q̃` of `InflationInertiaRepresentations`. -/
theorem qtilC_eq_qtilde (κ σ lami lamx γ : ℝ) (π x : ℕ → Ω → ℝ) (t : ℕ) :
    IRulePredetermined.qtil κ σ lami lamx γ π x t = qtilde γ κ σ lamx lami π x t := by
  funext ω
  simp only [IRulePredetermined.qtil, InflTargetPredetermined.qd_apply, qtilde, Pi.smul_apply,
    Pi.add_apply, Pi.sub_apply, smul_eq_mul]

/-- Woodford (2003), p. 597: a process in levels `z̄ + ẑ_t` is bounded when `ẑ` is. -/
theorem levelOf_bounded {c : ℝ} {y : ℕ → Ω → ℝ} (hy : BoundedProc y) :
    BoundedProc (levelOf c y) := by
  obtain ⟨M, hM⟩ := hy
  exact ⟨|c| + M, fun t ω => (abs_add_le _ _).trans (add_le_add le_rfl (hM t ω))⟩

/-- Woodford (2003), (3.19), p. 593: `q̃` is bounded for bounded `π̂, x̂`. -/
theorem qtilde_bounded {γ κ σ lx li : ℝ} {infl x : ℕ → Ω → ℝ} (hπ : BoundedProc infl)
    (hx : BoundedProc x) : BoundedProc (qtilde γ κ σ lx li infl x) := by
  obtain ⟨M, hM⟩ := hπ
  obtain ⟨N, hN⟩ := hx
  refine ⟨|κ * σ / li| * (M + |γ| * M + |lx / κ| * (N + N)), fun t ω => ?_⟩
  simp only [qtilde, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 : |γ * infl (t - 1) ω| ≤ |γ| * M := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM _ ω) (abs_nonneg _)
  have h2 : |lx / κ * (x t ω - x (t - 1) ω)| ≤ |lx / κ| * (N + N) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hN t ω) (hN _ ω)))
      (abs_nonneg _)
  calc |infl t ω - γ * infl (t - 1) ω + lx / κ * (x t ω - x (t - 1) ω)|
      ≤ |infl t ω - γ * infl (t - 1) ω| + |lx / κ * (x t ω - x (t - 1) ω)| := abs_add_le _ _
    _ ≤ (|infl t ω| + |γ * infl (t - 1) ω|) + |lx / κ * (x t ω - x (t - 1) ω)| :=
        add_le_add (abs_sub _ _) le_rfl
    _ ≤ M + |γ| * M + |lx / κ| * (N + N) := by linarith [hM t ω]

/-- Woodford (2003), (3.18), p. 593: `f̂ = q̃ − βγE q̃'` is bounded for bounded `π̂, x̂`. -/
theorem fhat_bounded {β γ κ σ lx li : ℝ} {infl x : ℕ → Ω → ℝ} (hπ : BoundedProc infl)
    (hx : BoundedProc x) : BoundedProc (fhat 𝔼 β γ κ σ lx li infl x) := by
  obtain ⟨B, hB⟩ := qtilde_bounded (γ := γ) (κ := κ) (σ := σ) (lx := lx) (li := li) hπ hx
  refine ⟨B + |β * γ| * B, fun t ω => ?_⟩
  simp only [fhat, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have h2 : |β * γ * 𝔼.E t (qtilde γ κ σ lx li infl x (t + 1)) ω| ≤ |β * γ| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hB (t + 1)) t ω) (abs_nonneg _)
  exact (abs_sub _ _).trans (add_le_add (hB t ω) h2)

/-- Woodford (2003), (3.19), p. 593: `q̃_t` is known at `t` when `π̂, x̂` are adapted. -/
theorem qtilde_adapted {γ κ σ lx li : ℝ} {infl x : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted infl)
    (hx : 𝔼.Adapted x) : 𝔼.Adapted (qtilde γ κ σ lx li infl x) := by
  intro t
  have kπ : 𝔼.E t (infl (t - 1)) = infl (t - 1) :=
    ForwardSolution.E_of_known 𝔼 (by omega) (hπ _)
  have kx : 𝔼.E t (x (t - 1)) = x (t - 1) := ForwardSolution.E_of_known 𝔼 (by omega) (hx _)
  simp only [qtilde, map_smul, map_add, map_sub, hπ t, hx t, kπ, kx]

/-- Woodford (2003), (3.18), p. 593: `f̂_t` is known at `t` when `π̂, x̂` are adapted. -/
theorem fhat_adapted {β γ κ σ lx li : ℝ} {infl x : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted infl)
    (hx : 𝔼.Adapted x) : 𝔼.Adapted (fhat 𝔼 β γ κ σ lx li infl x) := by
  intro t
  simp only [fhat, map_sub, map_smul, qtilde_adapted 𝔼 hπ hx t, 𝔼.E_E_self]

/-- Woodford (2003), (3.16), p. 592, and (3.21), p. 594, for an arbitrary expectation system:
written in levels `i = ī + ı̂`, `π = π̄ + π̂`, `x = x̄ + x̂`, the Euler equation (3.16) of
`IRulePredetermined` is the Euler equation (3.21) of `InflationInertiaRepresentations` in
deviations, given the steady-state relation `A(1)(ī − i*) = −f̄`
(`κσ/β (ī − i*) = −(κσ/λᵢ)(1 − βγ)(1 − γ)π̄`) and `ı̂` adapted. -/
theorem euler316_levels_iff (𝔼' : ExpectationSystem Ω) {lami lamx istar ibar pibar xbar : ℝ}
    (hss : κ * σ / β * (ibar - istar) = -(κ * σ / lami * (1 - β * γ) * (1 - γ) * pibar))
    {i infl x : ℕ → Ω → ℝ} (hia : 𝔼'.Adapted i) (t : ℕ) (ht : 2 ≤ t) :
    IRulePredetermined.Euler316 𝔼' β γ κ σ lami lamx istar (levelOf pibar infl)
        (levelOf xbar x) (levelOf ibar i) t ↔
      Euler 𝔼' β γ κ σ i (fhat 𝔼' β γ κ σ lamx lami infl x) t := by
  have hq : ∀ s, IRulePredetermined.qtil κ σ lami lamx γ (levelOf pibar infl) (levelOf xbar x) s
      = qtilde γ κ σ lamx lami infl x s + fun _ => κ * σ / lami * (1 - γ) * pibar := by
    intro s
    funext ω
    simp only [IRulePredetermined.qtil, InflTargetPredetermined.qd_apply, qtilde, levelOf,
      Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hL : (β * γ) • (levelOf ibar i (t + 1) - fun _ => istar) +
      CubicRoots.coefA1 β γ • (levelOf ibar i t - fun _ => istar) +
      CubicRoots.coefA2 β γ κ σ • (levelOf ibar i (t - 1) - fun _ => istar) +
      CubicRoots.coefA3 β • (levelOf ibar i (t - 2) - fun _ => istar) =
      (β * γ) • i (t + 1) + CubicRoots.coefA1 β γ • i t +
        CubicRoots.coefA2 β γ κ σ • i (t - 1) + CubicRoots.coefA3 β • i (t - 2) +
        fun _ => (β * γ + CubicRoots.coefA1 β γ + CubicRoots.coefA2 β γ κ σ +
          CubicRoots.coefA3 β) * (ibar - istar) := by
    funext ω
    simp only [levelOf, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have k1 : 𝔼'.E t (i (t - 1)) = i (t - 1) := ForwardSolution.E_of_known 𝔼' (by omega) (hia _)
  have k2 : 𝔼'.E t (i (t - 2)) = i (t - 2) := ForwardSolution.E_of_known 𝔼' (by omega) (hia _)
  unfold IRulePredetermined.Euler316 Euler fhat
  rw [hL, hq, hq, map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    map_add, 𝔼'.const, 𝔼'.const, hia t, k1, k2]
  simp only [CubicRoots.coefA1, CubicRoots.coefA2, CubicRoots.coefA3] at *
  constructor
  · intro h
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at this ⊢
    linear_combination this - hss
  · intro h
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at this ⊢
    linear_combination this + hss

/-- **Proposition 8.10 with predetermined decisions** (Woodford (2003), p. 605: "(3.29) is
identical to (3.16) except for the conditioning information set"; Proposition 8.10, p. 601):
under the standing assumptions and the steady-state relation, for processes predetermined `d`
periods in advance (adapted for `delay 𝔼 d`) and bounded, the Euler equation (3.16) for the
delayed expectations holds in levels at all dates `≥ t₀` iff the pure targeting rule (3.26)
with `E_{t−d}` holds in deviations at those dates. -/
theorem prop_8_10_delay (h : Standing β γ κ σ) {lami lamx istar ibar pibar xbar : ℝ}
    (hss : κ * σ / β * (ibar - istar) = -(κ * σ / lami * (1 - β * γ) * (1 - γ) * pibar))
    {d : ℕ} {i infl x : ℕ → Ω → ℝ} (hib : BoundedProc i)
    (hia : (IRulePredetermined.delay 𝔼 d).Adapted i) (hπb : BoundedProc infl)
    (hπa : (IRulePredetermined.delay 𝔼 d).Adapted infl) (hxb : BoundedProc x)
    (hxa : (IRulePredetermined.delay 𝔼 d).Adapted x) {t0 : ℕ} (ht0 : 2 ≤ t0) :
    (∀ t, t0 ≤ t → IRulePredetermined.Euler316 (IRulePredetermined.delay 𝔼 d) β γ κ σ lami lamx
        istar (levelOf pibar infl) (levelOf xbar x) (levelOf ibar i) t) ↔
      (∀ t, t0 ≤ t → TargetRule (IRulePredetermined.delay 𝔼 d) β γ (lam1 β γ κ σ)
        (sumS β γ κ σ) (prodP β γ κ σ) i
        (fhat (IRulePredetermined.delay 𝔼 d) β γ κ σ lamx lami infl x) t) := by
  rw [← prop_8_10_standing (IRulePredetermined.delay 𝔼 d) h hib hia
    (fhat_bounded _ hπb hxb) (fhat_adapted _ hπa hxa) ht0]
  exact forall₂_congr fun t ht => euler316_levels_iff _ hss hia t (ht0.trans ht)

/-- **Proposition 8.11 with predetermined decisions: the target criterion (3.31)** (Woodford
(2003), (3.31), p. 606, and Proposition 8.11, p. 602): under the standing assumptions,
`λₓ, λᵢ > 0` and the steady-state relation, for bounded processes predetermined `d` periods in
advance, the pure targeting rule (3.26) with `E_{t−d}` holds at date `n + 2` iff the levels
target criterion (3.31), `E_{t−d}F_t(π) + (φₓ/4)E_{t−d}F_t(x) = θ_π π_{t−1} + …`, does, with the
coefficients and weights of Proposition 8.11. -/
theorem prop_8_11_delay {lx li istar ibar pibar xbar : ℝ} (h : Standing β γ κ σ) (hlx : 0 < lx)
    (hli : 0 < li)
    (hss : κ * σ / β * (ibar - istar) = -(κ * σ / li * (1 - β * γ) * (1 - γ) * pibar))
    {d : ℕ} {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl)
    (hπa : (IRulePredetermined.delay 𝔼 d).Adapted infl) (hxb : BoundedProc x)
    (hxa : (IRulePredetermined.delay 𝔼 d).Adapted x) (n : ℕ) :
    TargetRule (IRulePredetermined.delay 𝔼 d) β γ (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ)
        i (fhat (IRulePredetermined.delay 𝔼 d) β γ κ σ lx li infl x) (n + 2) ↔
      IRulePredetermined.Target331 𝔼 (phiX327 β γ κ lx (sumS β γ κ σ) (prodP β γ κ σ))
        (thetaPi327 β γ (sumS β γ κ σ) (prodP β γ κ σ))
        (thetaX327 β γ κ lx (sumS β γ κ σ) (prodP β γ κ σ))
        (thetaI327 β γ κ σ li (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ))
        (thetaD327 β γ κ σ li (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ)) istar
        (alphaPi β γ (kIII β γ κ σ)) (alphaX β γ (kIII β γ κ σ)) d (levelOf pibar infl)
        (levelOf xbar x) (levelOf ibar i) (n + 2) := by
  have hR := inertiaRoots_of_standing h
  have h1 := prop_8_11_levels (IRulePredetermined.delay 𝔼 d) (i := i) (xbar := xbar) h.beta_pos
    h.beta_lt_one
    h.gamma_pos h.gamma_le_one h.kappa_pos h.sigma_pos hlx hli hR hss hπb hπa hxb hxa n
  have hK := hR.summable_abs_Kker
  simp only [sR_canonical, pR_canonical] at h1 hK
  rw [h1]
  exact IRulePredetermined.target331_iff 𝔼 (summable_abs_alphaPi hK) (summable_abs_alphaX hK)
    (levelOf_bounded hπb) (levelOf_bounded hxb) (n + 2)

/-- **The optimal target criterion with predetermined decisions** (Woodford (2003), pp. 605–606:
(3.29), projected on date-`(t − d)` information, is equivalent to (3.31)): under the standing
assumptions, `λₓ, λᵢ > 0` and the steady-state relation, for bounded processes predetermined `d`
periods in advance, the Euler equation (3.16) for the delayed expectations holds in levels at all
dates `≥ t₀` iff the target criterion (3.31) holds at all those dates. -/
theorem eq316_delay_iff_target331 {lx li istar ibar pibar xbar : ℝ} (h : Standing β γ κ σ)
    (hlx : 0 < lx) (hli : 0 < li)
    (hss : κ * σ / β * (ibar - istar) = -(κ * σ / li * (1 - β * γ) * (1 - γ) * pibar))
    {d : ℕ} {i infl x : ℕ → Ω → ℝ} (hib : BoundedProc i)
    (hia : (IRulePredetermined.delay 𝔼 d).Adapted i) (hπb : BoundedProc infl)
    (hπa : (IRulePredetermined.delay 𝔼 d).Adapted infl) (hxb : BoundedProc x)
    (hxa : (IRulePredetermined.delay 𝔼 d).Adapted x) {t0 : ℕ} (ht0 : 2 ≤ t0) :
    (∀ t, t0 ≤ t → IRulePredetermined.Euler316 (IRulePredetermined.delay 𝔼 d) β γ κ σ li lx
        istar (levelOf pibar infl) (levelOf xbar x) (levelOf ibar i) t) ↔
      (∀ t, t0 ≤ t → IRulePredetermined.Target331 𝔼
        (phiX327 β γ κ lx (sumS β γ κ σ) (prodP β γ κ σ))
        (thetaPi327 β γ (sumS β γ κ σ) (prodP β γ κ σ))
        (thetaX327 β γ κ lx (sumS β γ κ σ) (prodP β γ κ σ))
        (thetaI327 β γ κ σ li (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ))
        (thetaD327 β γ κ σ li (lam1 β γ κ σ) (sumS β γ κ σ) (prodP β γ κ σ)) istar
        (alphaPi β γ (kIII β γ κ σ)) (alphaX β γ (kIII β γ κ σ)) d (levelOf pibar infl)
        (levelOf xbar x) (levelOf ibar i) t) := by
  rw [prop_8_10_delay 𝔼 h hss hib hia hπb hπa hxb hxa ht0]
  refine forall₂_congr fun t ht => ?_
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t - 2, by omega⟩
  exact prop_8_11_delay 𝔼 h hlx hli hss hπb hπa hxb hxa n

/-- **Proposition 8.9 (Rule III) with predetermined decisions: the instrument rule (3.30)**
(Woodford (2003), (3.30), p. 606, and Proposition 8.9, p. 597): under the standing assumptions,
`λₓ, λᵢ > 0` and the steady-state relation, for bounded processes predetermined `d` periods in
advance, Rule III with `E_{t−d}` holds at date `n + 2` iff the levels instrument rule (3.30)
`i_t = (1 − ρ₁)i* + ρ₁i_{t−1} + ρ₂Δi_{t−1} + φ_π E_{t−d}F_t(π) + …` does, with the coefficients of
Proposition 8.9. -/
theorem prop_8_9_ruleIII_delay {lx li istar ibar pibar xbar : ℝ} (h : Standing β γ κ σ)
    (hlx : 0 < lx) (hli : 0 < li)
    (hss : κ * σ / β * (ibar - istar) = -(κ * σ / li * (1 - β * γ) * (1 - γ) * pibar))
    {d : ℕ} {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl)
    (hπa : (IRulePredetermined.delay 𝔼 d).Adapted infl) (hxb : BoundedProc x)
    (hxa : (IRulePredetermined.delay 𝔼 d).Adapted x) (n : ℕ) :
    KernelRule (IRulePredetermined.delay 𝔼 d) (lam1 β γ κ σ) (sumS β γ κ σ / 2) (β * γ)⁻¹
        (wIII β γ κ σ) i (fhat (IRulePredetermined.delay 𝔼 d) β γ κ σ lx li infl x) (n + 2) ↔
      IRulePredetermined.Rule330 𝔼 (rho1 (lam1 β γ κ σ) (sumS β γ κ σ / 2))
        (rho2 (lam1 β γ κ σ) (sumS β γ κ σ / 2)) (phiPi β γ κ σ li (β * γ)⁻¹ (wIII β γ κ σ))
        (phiX σ lx li (β * γ)⁻¹ (wIII β γ κ σ)) (thetaPi γ κ σ li (β * γ)⁻¹ (wIII β γ κ σ))
        (thetaX σ lx li (β * γ)⁻¹ (wIII β γ κ σ)) istar (alphaPi β γ (wIII β γ κ σ))
        (alphaX β γ (wIII β γ κ σ)) d (levelOf pibar infl) (levelOf xbar x) (levelOf ibar i)
        (n + 2) := by
  have hR := inertiaRoots_of_standing h
  have h1 := prop_8_9_ruleIII_levels (IRulePredetermined.delay 𝔼 d) (i := i) (xbar := xbar)
    h.beta_pos
    h.beta_lt_one h.gamma_pos h.gamma_le_one h.kappa_pos h.sigma_pos hlx hli hR hss hπb hπa hxb
    hxa n
  have hK := hR.summable_abs_ruleIIIker
  simp only [sR_canonical, pR_canonical] at h1 hK
  rw [h1]
  exact IRulePredetermined.rule330_iff 𝔼 (summable_abs_alphaPi hK) (summable_abs_alphaX hK)
    (levelOf_bounded hπb) (levelOf_bounded hxb) (n + 2)

/-! ### The basic model is the `γ = 0` case of the inertia model (Prop 8.5 vs. p. 593) -/

/-- Woodford (2003), p. 593 ("in the limiting case `γ = 0` … coincide[s] with the optimal
instrument rule (3.7)") and (3.7)–(3.9), p. 584: for adapted `i`, the Euler equation (3.16) of
`InflationInertiaRules` at `γ = 0` and `t` (date `t + 2`) is exactly the instrument rule (3.7) of
`IRuleBasic` at date `t + 2`, with `ρ₁ = 1 + κσ/β`, `ρ₂ = β⁻¹`, `φ_π = κσ/λᵢ`, `φₓ = 4σλₓ/λᵢ`
(for any pre-sample history, which (3.7) does not use from date 2 on). -/
theorem euler_gamma_zero_iff_rule (c : IRuleBasic.Calib) (hκ : c.κ ≠ 0) {π x i : ℕ → Ω → ℝ}
    (hia : 𝔼.Adapted i) (xm1 im1 im2 : ℝ) (t : ℕ) :
    InflationInertiaRules.Euler 𝔼 c.β 0 c.κ c.σ (fun k ω => i k ω - c.istar)
        (InflationInertiaRules.fbig 𝔼 c.β 0 c.κ c.σ c.lx c.li π x) t ↔
      IRuleBasic.Rule c xm1 im1 im2 π x i (t + 2) := by
  have hı : 𝔼.Adapted (fun k ω => i k ω - c.istar) := fun k => by
    change 𝔼.E k (i k - fun _ => c.istar) = i k - fun _ => c.istar
    rw [map_sub, 𝔼.const, hia k]
  rw [InflationInertiaRules.euler_gamma_zero 𝔼 hı t]
  unfold IRuleBasic.Rule
  simp only [InflationInertiaRules.fbig_gamma_zero 𝔼 hκ, show t + 2 - 1 = t + 1 by omega]
  have l1 : IRuleBasic.lag im1 i (t + 2) = i (t + 1) := rfl
  have l2 : IRuleBasic.lag im2 (IRuleBasic.lag im1 i) (t + 2) = i t := rfl
  have l3 : IRuleBasic.lag xm1 x (t + 2) = x (t + 1) := rfl
  rw [l1, l2, l3]
  constructor
  · intro h
    funext ω
    have := h ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, IRuleBasic.rho1,
      IRuleBasic.rho2, IRuleBasic.phiPi, IRuleBasic.phiX]
    linear_combination this
  · intro h ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, IRuleBasic.rho1,
      IRuleBasic.rho2, IRuleBasic.phiPi, IRuleBasic.phiX] at this
    linear_combination this

/-- Woodford (2003), App. A: a bounded process in the sense of `BoundedProc` is bounded in the sense
of `InflationInertiaRules.Bnd` (a nonnegative bound). -/
theorem bnd_of_boundedProc {y : ℕ → Ω → ℝ} (hy : BoundedProc y) : InflationInertiaRules.Bnd y := by
  obtain ⟨M, hM⟩ := hy
  exact ⟨max M 0, le_max_right _ _, fun k ω => (hM k ω).trans (le_max_left _ _)⟩

/-- **Determinacy of the rule system at `γ = 0`: Proposition 8.5 meets p. 593** (Woodford (2003),
Prop 8.5, p. 584, and p. 593). For the basic model (`γ = 0`), every bounded adapted disturbance
pair and every history `x_{−1}, i_{−1}, i_{−2}`, the bounded equilibrium under the optimal rule
(3.7) of `IRuleBasic` (Proposition 8.5) solves the rule system (2.6), (3.1), (3.16) of
`InflationInertiaRules` at `γ = 0`; and (faithful expectations with the pull-out property) every
bounded adapted solution of that system with the same date-0 and date-1 history coincides with
it from date 1 on. So the rule system of p. 593 is determinate at `γ = 0` — existence included,
which `InflationInertiaRules.rule_system_determinate` assumes. -/
theorem inertia_system_gamma_zero (c : IRuleBasic.Calib) (hc : c.Adm) (hpull : 𝔼.PullOut)
    (hfaith : ExpectationTools.Faithful 𝔼) {rn u : ℕ → Ω → ℝ} (hrb : BoundedProc rn)
    (hra : 𝔼.Adapted rn) (hub : BoundedProc u) (hua : 𝔼.Adapted u) (xm1 im1 im2 : ℝ) :
    ∃ π x i : ℕ → Ω → ℝ, IRuleBasic.RuleEqm 𝔼 c rn u xm1 im1 im2 π x i ∧
      𝔼.Adapted π ∧ 𝔼.Adapted x ∧ 𝔼.Adapted i ∧
      BoundedProc π ∧ BoundedProc x ∧ BoundedProc i ∧
      (∀ k, 2 ≤ k → InflationInertiaRules.AS 𝔼 c.β 0 c.κ u π x k) ∧
      (∀ k, 2 ≤ k → InflationInertiaRules.IS 𝔼 c.σ rn π x i k) ∧
      (∀ t, InflationInertiaRules.Euler 𝔼 c.β 0 c.κ c.σ (fun k ω => i k ω - c.istar)
        (InflationInertiaRules.fbig 𝔼 c.β 0 c.κ c.σ c.lx c.li π x) t) ∧
      ∀ π' x' i' : ℕ → Ω → ℝ, 𝔼.Adapted π' → 𝔼.Adapted x' → 𝔼.Adapted i' →
        BoundedProc π' → BoundedProc x' → BoundedProc i' →
        (∀ k, 2 ≤ k → InflationInertiaRules.AS 𝔼 c.β 0 c.κ u π' x' k) →
        (∀ k, 2 ≤ k → InflationInertiaRules.IS 𝔼 c.σ rn π' x' i' k) →
        (∀ t, InflationInertiaRules.Euler 𝔼 c.β 0 c.κ c.σ (fun k ω => i' k ω - c.istar)
          (InflationInertiaRules.fbig 𝔼 c.β 0 c.κ c.σ c.lx c.li π' x') t) →
        (∀ ω, π' 1 ω = π 1 ω) → (∀ ω, x' 1 ω = x 1 ω) → (∀ ω, i' 1 ω = i 1 ω) →
        (∀ ω, i' 0 ω = i 0 ω) →
        ∀ k, 1 ≤ k → ∀ ω, π' k ω = π k ω ∧ x' k ω = x k ω ∧ i' k ω = i k ω := by
  obtain ⟨⟨π, x, i⟩, ⟨hEq, ⟨hπa, hxa, hia⟩, ⟨hπb, hxb, hib⟩⟩, -⟩ :=
    IRuleBasic.rule_determinate 𝔼 c hc hrb hra hub hua xm1 im1 im2
  obtain ⟨hβ0, hβ1, hσ, hκ, hlx, hli⟩ := hc
  have hAS : ∀ k, 2 ≤ k → InflationInertiaRules.AS 𝔼 c.β 0 c.κ u π x k := fun k _ ω => by
    have := congrFun (hEq k).1 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [zero_mul, sub_zero]
    exact this
  have hIS : ∀ k, 2 ≤ k → InflationInertiaRules.IS 𝔼 c.σ rn π x i k := fun k _ ω => by
    have := congrFun (hEq k).2.1 ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hE : ∀ t, InflationInertiaRules.Euler 𝔼 c.β 0 c.κ c.σ (fun k ω => i k ω - c.istar)
      (InflationInertiaRules.fbig 𝔼 c.β 0 c.κ c.σ c.lx c.li π x) t := fun t =>
    (euler_gamma_zero_iff_rule 𝔼 c hκ.ne' hia xm1 im1 im2 t).mpr (hEq (t + 2)).2.2
  refine ⟨π, x, i, hEq, hπa, hxa, hia, hπb, hxb, hib, hAS, hIS, hE, ?_⟩
  intro π' x' i' hπa' hxa' hia' hπb' hxb' hib' hAS' hIS' hE' h1π h1x h1i h0i
  exact InflationInertiaRules.rule_system_unique 𝔼 hpull hfaith hβ0 hβ1 hκ.ne' hσ.ne' hli
    hlx.le hπa' hxa' hia' hπa hxa hia (bnd_of_boundedProc hπb') (bnd_of_boundedProc hxb')
    (bnd_of_boundedProc hib') (bnd_of_boundedProc hπb) (bnd_of_boundedProc hxb)
    (bnd_of_boundedProc hib) hAS' hAS hIS' hIS hE' hE h1π h1x h1i h0i

/-- Woodford (2003), (3.10) and fn 35, pp. 586–588: the roots `λ₁ < λ₂` of
`z² − (ρ₁ + ρ₂)z + ρ₂` used in `IRuleBasic`, at the optimal coefficients (3.8)
`ρ₁ = 1 + κσ/β`, `ρ₂ = β⁻¹`, are the roots `QuadraticRoots.lam1, lam2` of
`βμ² − (1 + β + κσ)μ + 1` (and so the `μ₁, μ₂` of Lemma G.2 in `CubicRoots`). -/
theorem irule_roots_eq (hβ : 0 < β) :
    IRuleBasic.lam1 (IRuleBasic.rho1 β σ κ) (IRuleBasic.rho2 β) = QuadraticRoots.lam1 β (κ * σ) ∧
      IRuleBasic.lam2 (IRuleBasic.rho1 β σ κ) (IRuleBasic.rho2 β) =
        QuadraticRoots.lam2 β (κ * σ) := by
  have hs : (IRuleBasic.rho1 β σ κ + IRuleBasic.rho2 β) ^ 2 - 4 * IRuleBasic.rho2 β =
      QuadraticRoots.charDisc β (κ * σ) / β ^ 2 := by
    unfold IRuleBasic.rho1 IRuleBasic.rho2 QuadraticRoots.charDisc
    field_simp
    ring
  have hr : Real.sqrt (QuadraticRoots.charDisc β (κ * σ) / β ^ 2) =
      Real.sqrt (QuadraticRoots.charDisc β (κ * σ)) / β := by
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hβ.le]
  have hsum : IRuleBasic.rho1 β σ κ + IRuleBasic.rho2 β = (1 + β + κ * σ) / β := by
    unfold IRuleBasic.rho1 IRuleBasic.rho2
    field_simp
    ring
  unfold IRuleBasic.lam1 IRuleBasic.lam2 QuadraticRoots.lam1 QuadraticRoots.lam2
  rw [hs, hr, hsum]
  constructor <;> field_simp

/-- Woodford (2003), (3.4) and (3.4'), pp. 584 and 605: with no delay (`d = 0`) the first-order
condition (3.4') of `IRulePredetermined` is (3.4) of `InflationInertiaRules`. -/
theorem foc34_delay_zero (β κ lamx xs : ℝ) (x φ1 φ2 : ℕ → Ω → ℝ) (t : ℕ) :
    IRulePredetermined.FOC34 β κ lamx xs 0 x φ1 φ2 t ↔
      InflationInertiaRules.FOC34 β κ lamx xs x φ1 φ2 t := by
  simp only [IRulePredetermined.FOC34, InflationInertiaRules.FOC34, Nat.sub_zero]

/-- Woodford (2003), (3.5) and (3.5'), pp. 584 and 605: with no delay (`d = 0`) the first-order
condition (3.5') of `IRulePredetermined` is (3.5) of `InflationInertiaRules`. -/
theorem foc35_delay_zero (σ lami istar : ℝ) (i φ1 : ℕ → Ω → ℝ) (t : ℕ) :
    IRulePredetermined.FOC35 σ lami istar 0 i φ1 t ↔
      InflationInertiaRules.FOC35 σ lami istar i φ1 t := by
  simp only [IRulePredetermined.FOC35, InflationInertiaRules.FOC35, Nat.sub_zero]

/-! ### The two copies of the second-order workhorse (survey §4.3) -/

/-- Woodford (2003), §2.1, p. 561, and Ch. 3 (2.16)–(2.18): the lag with a given date-`(−1)`
value of `InflTargetPredetermined` (`prev`) is that of `InflTargetInertia` (`lagW`). -/
theorem prev_eq_lagW (x0 : Ω → ℝ) (x : ℕ → Ω → ℝ) :
    InflTargetPredetermined.prev x0 x = InflTargetInertia.lagW x0 x := by
  funext t
  cases t <;> rfl

/-- Woodford (2003), survey §4.3 (the workhorse `βE_t y_{t+1} − (1 + β + c)y_t + y_{t−1} = f_t`,
used for (2.5), (2.9) and (2.32)): the equation of `InflTargetPredetermined` with forcing `−z` is
the equation of `InflTargetInertia` with forcing `f = −z`. -/
theorem secondOrder_iff (β c : ℝ) (ℓm1 : Ω → ℝ) (z ℓ : ℕ → Ω → ℝ) :
    InflTargetPredetermined.SecondOrder 𝔼 β c ℓm1 z ℓ ↔
      InflTargetInertia.SecondOrder 𝔼 β c ℓm1 (fun t ω => -z t ω) ℓ := by
  unfold InflTargetPredetermined.SecondOrder InflTargetInertia.SecondOrder
  rw [prev_eq_lagW]
  constructor
  · intro h t ω
    have := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at this
    exact this
  · intro h t
    funext ω
    have := h t ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    exact this

/-- Woodford (2003), survey §4.3 (uniqueness of the bounded solution of the workhorse): for
`0 < β < 1`, `c > 0`, bounded adapted `z` and a bounded date-0 initial value, the explicit solution
`secondOrderSol` of `InflTargetPredetermined` and the solution `ysol` of `InflTargetInertia` (with
forcing `−z`) are the same process. -/
theorem ysol_eq_secondOrderSol {β c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c)
    {z : ℕ → Ω → ℝ} (hz : BoundedProc z) (hza : 𝔼.Adapted z) {ℓm1 : Ω → ℝ} {K : ℝ}
    (hK : ∀ ω, |ℓm1 ω| ≤ K) (hm0 : 𝔼.E 0 ℓm1 = ℓm1) :
    InflTargetInertia.ysol 𝔼 β c ℓm1 (fun t ω => -z t ω) =
      InflTargetPredetermined.secondOrderSol 𝔼 β c ℓm1 z := by
  obtain ⟨hs, hb, ha, -⟩ :=
    InflTargetPredetermined.secondOrder_existsUnique 𝔼 hβ0 hc hz hza hK hm0
  obtain ⟨M, hM⟩ := hz
  have hfa : 𝔼.Adapted (fun t ω => -z t ω) := fun t => by
    change 𝔼.E t (-z t) = -z t
    rw [map_neg, hza t]
  have hfb : ∀ t ω, |(fun t ω => -z t ω) t ω| ≤ M := fun t ω => by
    simp only [abs_neg]
    exact hM t ω
  exact ((InflTargetInertia.secondOrder_existsUnique 𝔼 hβ0 hβ1 hc hfb hfa hK hm0).2 _
    ((secondOrder_iff 𝔼 β c ℓm1 z _).mp hs) ha hb).symm

/-! ### The model equations of the different parts -/

/-- Woodford (2003), (2.1), p. 560: the aggregate-supply relation of `InflTargetInertia` (§2.1) is
that of `IRuleBasic` (§3.1) at every date. -/
theorem as_basic_iff (c : IRuleBasic.Calib) (u π x : ℕ → Ω → ℝ) :
    InflTargetInertia.AS 𝔼 c.β c.κ u π x ↔ ∀ t, IRuleBasic.AS 𝔼 c u π x t := by
  unfold InflTargetInertia.AS IRuleBasic.AS
  constructor
  · intro h t
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h t ω
  · intro h t ω
    have := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this

/-- Woodford (2003), (2.6), p. 562 (corrected) with `γ = 0`, and (2.1), p. 560: the indexation
aggregate-supply relation of `InflationInertiaRules` at `γ = 0` is that of `IRuleBasic`. -/
theorem as_inertia_zero_iff (c : IRuleBasic.Calib) (u π x : ℕ → Ω → ℝ) (k : ℕ) :
    InflationInertiaRules.AS 𝔼 c.β 0 c.κ u π x k ↔ IRuleBasic.AS 𝔼 c u π x k := by
  unfold InflationInertiaRules.AS IRuleBasic.AS
  simp only [zero_mul, sub_zero]
  constructor
  · intro h
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h ω
  · intro h ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this

/-- Woodford (2003), (3.1), p. 583: the IS relation of `InflationInertiaRules` is that of
`IRuleBasic`. -/
theorem is_inertia_iff (c : IRuleBasic.Calib) (rn π x i : ℕ → Ω → ℝ) (k : ℕ) :
    InflationInertiaRules.IS 𝔼 c.σ rn π x i k ↔ IRuleBasic.IS 𝔼 c rn π x i k := by
  unfold InflationInertiaRules.IS IRuleBasic.IS
  constructor
  · intro h
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact h ω
  · intro h ω
    have := congrFun h ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this

/-- Woodford (2003), (2.6), p. 562 (corrected; the same misprint is recorded in both parts): the
indexation aggregate-supply relation `ASind` of `InflTargetInertia` (§2.1) holds iff it holds at
date 0 (with the pre-sample `π₀`) and the relation `AS` of `InflationInertiaRules` (§3.2) holds at
every date `k ≥ 1`. -/
theorem asInd_iff (β κ γ : ℝ) (π₀ : Ω → ℝ) (u π x : ℕ → Ω → ℝ) :
    InflTargetInertia.ASind 𝔼 β κ γ π₀ u π x ↔
      (∀ ω, π 0 ω - γ * π₀ ω =
        κ * x 0 ω + β * 𝔼.E 0 (fun ω => π 1 ω - γ * π 0 ω) ω + u 0 ω) ∧
      ∀ k, 1 ≤ k → InflationInertiaRules.AS 𝔼 β γ κ u π x k := by
  unfold InflTargetInertia.ASind InflationInertiaRules.AS
  constructor
  · intro h
    refine ⟨h 0, fun k hk => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    exact h (n + 1)
  · rintro ⟨h0, h⟩ t
    cases t with
    | zero => exact h0
    | succ n => exact h (n + 1) (by omega)

/-- Woodford (2003), (2.28), p. 570 with `d = 0`, and (2.6), p. 562: for adapted `x, u`, the
aggregate-supply relation of `InflTargetPredetermined` without a delay is the relation `AS` of
`InflationInertiaRules` at every date `k ≥ t₀`. -/
theorem as_predetermined_zero_iff (κ β γ : ℝ) (t0 : ℕ) {u π x : ℕ → Ω → ℝ} (hxa : 𝔼.Adapted x)
    (hua : 𝔼.Adapted u) :
    InflTargetPredetermined.AS 𝔼 κ β γ 0 t0 u π x ↔
      ∀ k, t0 ≤ k → InflationInertiaRules.AS 𝔼 β γ κ u π x k := by
  unfold InflTargetPredetermined.AS InflationInertiaRules.AS
  simp only [add_zero, Nat.sub_zero]
  refine forall₂_congr fun k _ => ?_
  have hq : InflTargetPredetermined.qd γ π (k + 1) = fun ω => π (k + 1) ω - γ * π k ω := by
    funext ω
    rw [InflTargetPredetermined.qd_apply, Nat.add_sub_cancel]
  rw [hq, hxa k, hua k]
  constructor
  · intro h ω
    have := congrFun h ω
    simp only [InflTargetPredetermined.qd_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at this
    exact this
  · intro h
    funext ω
    simp only [InflTargetPredetermined.qd_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h ω

end Woodford.OptimalPolicyRules.Links
