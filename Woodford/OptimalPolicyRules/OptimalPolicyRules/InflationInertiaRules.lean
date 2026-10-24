/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.CubicRoots
import OptimalPolicyRules.ExpectationTools
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Optimal instrument rules with inflation inertia

Woodford (2003), *Interest and Prices*, Chapter 8, §3.2, pp. 592–598, eqs. (3.14)–(3.24),
Proposition 8.8, and Appendix G, §G.7 (proof of Proposition 8.8, pp. 727–730).

Dates: processes are indexed by `ℕ`; the Euler equation and the rules are stated at date
`n = t + 2` (so that two lags exist). All results hold for an arbitrary `ExpectationSystem`.

## Main results

* The forward-inverse lemma over `ℂ` with a date shift `m`: `fwdC`, `fwdC_solves`, `eq_fwdC`,
  `solves_iff_fwdC`, `eq_zero_of_homog` (any complex `‖a‖ < 1`; the complexified expectation
  `EC` itself is `ExpectationTools.EC`).
* The Euler equation (3.21) `Euler`, the rules `RuleI`, `RuleII`, `RuleIII` (3.22)–(3.24)
  (complex coefficients in general) and their real forms `RuleIReal`, `RuleIIReal`,
  `RuleIIIReal` (with the real weights `psiIII`, `psiIII_conj`).
* **Proposition 8.8**: `ruleI_iff_euler`, `ruleII_iff_euler`, `ruleIII_iff_euler` (for
  arbitrary roots with `|λ₂|, |λ₃| > 1`, `|λ₂ + λ₃| > 2`, real OR complex), and for the roots of
  Proposition 8.7: `prop_8_8_ruleI`, `prop_8_8_ruleII`, `prop_8_8_ruleIII`,
  `prop_8_8_ruleIII_real` (real coefficients, both cases), `prop_8_8_real` (three real roots).
* p. 597: `rules_coincide`, `rules_coincide_at_bifurcation`; pp. 596–597:
  `ruleI_lag_coeffs_limit`, `ruleI_lead_coeff_limit`, `ruleI_rhs_limit` (Rule I → (3.10)),
  `other_rules_unbounded`, `continuousOn_rule_coeffs`, `continuousOn_ruleI_weights`.
* The model (3.14)–(3.19): `AS` (2.6) (corrected; `ASprinted_iff` records the misprint), `IS`
  (3.1), `periodLoss` (3.14), `FOC315`, `FOC34`, `FOC35`, `qtil`, `fbig`; `foc315_iff_euler`
  ((3.15) ⇔ (3.16) given (3.4), (3.5)), `euler_hat_iff` ((3.16) ⇔ (3.21)), `fbig_gamma_zero`,
  `euler_gamma_zero` (`γ = 0` gives (3.10)).
* Lagrangian sufficiency: `foTerm_eq`, `loss_gap` (exact loss decomposition),
  `optimalCommitment_of_foc`, `timelesslyOptimal_of_foc` (definitions `OptimalCommitment`,
  `TimelesslyOptimal`), `unique_of_foc_perfectForesight`; `timelesslyOptimal_of_euler`
  ((3.16) implements the timelessly optimal plan) and `ruleI_timelesslyOptimal`,
  `ruleII_timelesslyOptimal`, `ruleIII_timelesslyOptimal`.
* Determinacy of the rule system (p. 593): `rule_system_unique` (for ALL admissible parameters,
  at most one bounded adapted solution with given history `(π₁, x₁, i₁, i₀)`, faithful
  expectations `Faithful`), `rule_system_determinate` (the Prop 8.5 analogue: a bounded solution
  of the optimal-plan FOC system solves the rule system and is its unique bounded solution); the
  characteristic polynomial `charD = det charMat` (`det_charMat`), the reciprocal pairing
  `charD_reciprocal`, `charD_root_pair`, and `charD_one_ne_zero`.
-/

namespace Woodford.OptimalPolicyRules.InflationInertiaRules

open Filter Topology
open Woodford.OptimalPolicyRules.CubicRoots Woodford.OptimalPolicyRules.CubicRoots.Assumptions
open ExpectationTools (Faithful EC EC_re EC_im E_fun_add E_fun_sub E_fun_mul E_fun_zero EC_ofReal
  EC_add EC_add_fun EC_const_mul EC_sub_fun EC_zero_fun EC_tower EC_known norm_EC_le EC_tsum)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The forward-inverse lemma over `ℂ`

The complexified expectation `EC` and its algebra are in `ExpectationTools`. The forward series
here carries a date shift `m` (information dated `t + m`). -/

/-- Woodford (2003), App. G.7, p. 728: the forward series
`∑ⱼ aʲ EC_{t+m} u_{t+j}`, i.e. `E_t (1 − aL⁻¹)⁻¹ u_t` with information dated `t + m`. -/
noncomputable def fwdC (m : ℕ) (a : ℂ) (u : ℕ → Ω → ℂ) (t : ℕ) (ω : Ω) : ℂ :=
  ∑' j, a ^ j * EC 𝔼 (t + m) (u (t + j)) ω

/-- The terms of the forward series are dominated by `‖a‖ʲ (2M)` (Woodford (2003), App. G.7). -/
theorem norm_fwdC_term_le {m : ℕ} {a : ℂ} {u : ℕ → Ω → ℂ} {M : ℝ} (hu : ∀ t ω, ‖u t ω‖ ≤ M)
    (t j : ℕ) (ω : Ω) : ‖a ^ j * EC 𝔼 (t + m) (u (t + j)) ω‖ ≤ ‖a‖ ^ j * (2 * M) := by
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (norm_EC_le 𝔼 (hu (t + j)) _ ω) (by positivity)

/-- The forward series converges for `‖a‖ < 1` and bounded `u` (Woodford (2003), App. G.7). -/
theorem summable_fwdC {m : ℕ} {a : ℂ} (ha : ‖a‖ < 1) {u : ℕ → Ω → ℂ} {M : ℝ}
    (hu : ∀ t ω, ‖u t ω‖ ≤ M) (t : ℕ) (ω : Ω) :
    Summable (fun j => a ^ j * EC 𝔼 (t + m) (u (t + j)) ω) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg a) ha).mul_right _)
    (fun j => norm_fwdC_term_le 𝔼 hu t j ω)

/-- The forward series is bounded: `‖∑ aʲ EC u‖ ≤ (1 − ‖a‖)⁻¹ 2M` (Woodford (2003), App. G.7,
p. 728: "a bounded stochastic process in the case of any bounded process"). -/
theorem norm_fwdC_le {m : ℕ} {a : ℂ} (ha : ‖a‖ < 1) {u : ℕ → Ω → ℂ} {M : ℝ}
    (hu : ∀ t ω, ‖u t ω‖ ≤ M) (t : ℕ) (ω : Ω) :
    ‖fwdC 𝔼 m a u t ω‖ ≤ (1 - ‖a‖)⁻¹ * (2 * M) :=
  tsum_of_norm_bounded ((hasSum_geometric_of_lt_one (norm_nonneg a) ha).mul_right _)
    (fun j => norm_fwdC_term_le 𝔼 hu t j ω)

/-- Woodford (2003), App. G.7, p. 728: the forward series solves
`y_t = a EC_{t+m} y_{t+1} + u_t` when `u_t` is known at `t + m`. -/
theorem fwdC_solves {m : ℕ} {a : ℂ} (ha : ‖a‖ < 1) {u : ℕ → Ω → ℂ} {M : ℝ}
    (hu : ∀ t ω, ‖u t ω‖ ≤ M) (hua : ∀ t, EC 𝔼 (t + m) (u t) = u t) (t : ℕ) (ω : Ω) :
    fwdC 𝔼 m a u t ω = a * EC 𝔼 (t + m) (fwdC 𝔼 m a u (t + 1)) ω + u t ω := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hu 0 ω)
  have hgeo : Summable (fun j : ℕ => ‖a‖ ^ j * (2 * M)) :=
    (summable_geometric_of_lt_one (norm_nonneg a) ha).mul_right _
  have hE : EC 𝔼 (t + m) (fwdC 𝔼 m a u (t + 1)) ω =
      ∑' j, a ^ j * EC 𝔼 (t + m) (u (t + 1 + j)) ω := by
    have h1 := EC_tsum 𝔼 hgeo (f := fun j ω' => a ^ j * EC 𝔼 (t + 1 + m) (u (t + 1 + j)) ω')
      (fun j ω' => norm_fwdC_term_le 𝔼 hu (t + 1) j ω') (t + m) ω
    unfold fwdC
    rw [h1]
    refine tsum_congr fun j => ?_
    rw [EC_const_mul, EC_tower 𝔼 (by omega)]
  rw [hE, ← tsum_mul_left]
  unfold fwdC
  rw [(summable_fwdC 𝔼 ha hu t ω).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, add_zero, hua t]
  rw [add_comm]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ, show t + (j + 1) = t + 1 + j by ring]
  ring

/-- Woodford (2003), App. G.7, p. 728 (forward uniqueness over `ℂ`): for `‖a‖ < 1`, a bounded
process satisfying `y_t = a EC_{t+m} y_{t+1} + u_t` at every date `t ≥ t₀` equals the forward
series at those dates. -/
theorem eq_fwdC {m : ℕ} {a : ℂ} (ha : ‖a‖ < 1) {u y : ℕ → Ω → ℂ} {M K : ℝ}
    (hu : ∀ t ω, ‖u t ω‖ ≤ M) (hua : ∀ t, EC 𝔼 (t + m) (u t) = u t)
    (hy : ∀ t ω, ‖y t ω‖ ≤ K) {t0 : ℕ}
    (hsol : ∀ t, t0 ≤ t → ∀ ω, y t ω = a * EC 𝔼 (t + m) (y (t + 1)) ω + u t ω) :
    ∀ t, t0 ≤ t → ∀ ω, y t ω = fwdC 𝔼 m a u t ω := by
  set d : ℕ → Ω → ℂ := fun t ω => y t ω - fwdC 𝔼 m a u t ω with hd
  have hdrec : ∀ t, t0 ≤ t → ∀ ω, d t ω = a * EC 𝔼 (t + m) (d (t + 1)) ω := by
    intro t ht ω
    have e : d (t + 1) = fun ω => y (t + 1) ω - fwdC 𝔼 m a u (t + 1) ω := rfl
    rw [e, EC_sub_fun]
    simp only [hd]
    rw [hsol t ht ω, fwdC_solves 𝔼 ha hu hua t ω]
    ring
  set B := K + (1 - ‖a‖)⁻¹ * (2 * M) with hB
  have hdb : ∀ t ω, ‖d t ω‖ ≤ B := fun t ω =>
    (norm_sub_le _ _).trans (add_le_add (hy t ω) (norm_fwdC_le 𝔼 ha hu t ω))
  have hit : ∀ n t, t0 ≤ t → ∀ ω, d t ω = a ^ (n + 1) * EC 𝔼 (t + m) (d (t + n + 1)) ω := by
    intro n
    induction n with
    | zero =>
      intro t ht ω
      simpa using hdrec t ht ω
    | succ n ih =>
      intro t ht ω
      rw [ih t ht ω]
      have e : d (t + n + 1) = fun ω' => a * EC 𝔼 (t + n + 1 + m) (d (t + n + 1 + 1)) ω' :=
        funext fun ω' => hdrec (t + n + 1) (by omega) ω'
      rw [e, EC_const_mul, EC_tower 𝔼 (by omega), pow_succ,
        show t + (n + 1) + 1 = t + n + 1 + 1 by ring]
      ring
  intro t ht ω
  have hle : ∀ n : ℕ, ‖d t ω‖ ≤ ‖a‖ ^ (n + 1) * (2 * B) := by
    intro n
    rw [hit n t ht ω, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (norm_EC_le 𝔼 (hdb _) _ ω) (by positivity)
  have hlim : Tendsto (fun n : ℕ => ‖a‖ ^ (n + 1) * (2 * B)) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg a) ha).comp
      (tendsto_add_atTop_nat 1)
    simpa using h.mul_const (2 * B)
  have h0 : ‖d t ω‖ ≤ 0 := ge_of_tendsto' hlim hle
  have : d t ω = 0 := norm_le_zero_iff.mp h0
  simpa [hd, sub_eq_zero] using this

/-- Woodford (2003), App. G.7, p. 728 (the forward-inverse lemma over `ℂ`): for `‖a‖ < 1`,
bounded `u` known at `t + m` and bounded `y`, `y_t = a EC_{t+m} y_{t+1} + u_t` for all
`t ≥ t₀` iff `y_t = ∑ aʲ EC_{t+m} u_{t+j}` for all `t ≥ t₀`. -/
theorem solves_iff_fwdC {m : ℕ} {a : ℂ} (ha : ‖a‖ < 1) {u y : ℕ → Ω → ℂ} {M K : ℝ}
    (hu : ∀ t ω, ‖u t ω‖ ≤ M) (hua : ∀ t, EC 𝔼 (t + m) (u t) = u t)
    (hy : ∀ t ω, ‖y t ω‖ ≤ K) (t0 : ℕ) :
    (∀ t, t0 ≤ t → ∀ ω, y t ω = a * EC 𝔼 (t + m) (y (t + 1)) ω + u t ω) ↔
      (∀ t, t0 ≤ t → ∀ ω, y t ω = fwdC 𝔼 m a u t ω) := by
  constructor
  · exact eq_fwdC 𝔼 ha hu hua hy
  · intro h t ht ω
    have e : y (t + 1) = fwdC 𝔼 m a u (t + 1) := funext fun ω' => h (t + 1) (by omega) ω'
    rw [h t ht ω, e]
    exact fwdC_solves 𝔼 ha hu hua t ω

/-- Woodford (2003), App. G.7, p. 730 (the last step of the Rule III converse): for `‖a‖ < 1`,
a bounded process with `e_t = a EC_{t+m} e_{t+1}` at all `t ≥ t₀` vanishes at those dates. -/
theorem eq_zero_of_homog {m : ℕ} {a : ℂ} (ha : ‖a‖ < 1) {e : ℕ → Ω → ℂ} {K : ℝ}
    (he : ∀ t ω, ‖e t ω‖ ≤ K) {t0 : ℕ}
    (hsol : ∀ t, t0 ≤ t → ∀ ω, e t ω = a * EC 𝔼 (t + m) (e (t + 1)) ω) :
    ∀ t, t0 ≤ t → ∀ ω, e t ω = 0 := by
  have h := eq_fwdC 𝔼 (u := fun _ _ => 0) (M := 0) ha (fun _ _ => by simp)
    (fun t => EC_zero_fun 𝔼 (t + m)) he (fun t ht ω => by rw [hsol t ht ω, add_zero])
  intro t ht ω
  rw [h t ht ω]
  unfold fwdC
  simp [EC_zero_fun]

/-! ### The Euler equation (3.21) and the rules (3.22)–(3.24) -/

/-- Woodford (2003), eq. (3.17)/(3.21), p. 594: `A(L) ı̂_{n+1}` at date `n = t + 2`,
`βγ ı̂_{t+3} − (1 + γ + βγ) ı̂_{t+2} + A₂ ı̂_{t+1} − β⁻¹ ı̂_t`. -/
noncomputable def ALi (β γ κ σ : ℝ) (ı : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β * γ * ı (t + 3) ω - (1 + γ + β * γ) * ı (t + 2) ω + coefA2 β γ κ σ * ı (t + 1) ω -
    β⁻¹ * ı t ω

/-- Woodford (2003), eq. (3.21), p. 594 (= (G.24), p. 727): `E_n[A(L) ı̂_{n+1}] = −f̂_n` at date
`n = t + 2`. -/
def Euler (β γ κ σ : ℝ) (ı f : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, 𝔼.E (t + 2) (ALi β γ κ σ ı t) ω = -f (t + 2) ω

/-- Woodford (2003), eqs. (3.22)–(3.24), p. 595: `(1 − λ₁L)(1 − μL) ı̂_n` at date `n = t + 2`. -/
noncomputable def lagQ (l1 μ : ℂ) (ı : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℂ :=
  (ı (t + 2) ω : ℂ) - (l1 + μ) * (ı (t + 1) ω : ℂ) + l1 * μ * (ı t ω : ℂ)

/-- Woodford (2003), eqs. (3.22)–(3.24), p. 595:
`E_n[(1 − μ⁻¹L⁻¹)⁻¹ f̂_n] = ∑ⱼ μ⁻ʲ E_n f̂_{n+j}`. -/
noncomputable def fsum (μ : ℂ) (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℂ :=
  ∑' j, (μ⁻¹) ^ j * (𝔼.E n (f (n + j)) ω : ℂ)

/-- Woodford (2003), eq. (3.22) = (G.21), p. 595, **Rule I** at date `n = t + 2`:
`(1 − λ₁L)(1 − λ₂L) ı̂_n = (βγλ₃)⁻¹ E_n[(1 − λ₃⁻¹L⁻¹)⁻¹ f̂_n]` (complex-valued in general). -/
def RuleI (β γ : ℝ) (l1 l2 l3 : ℂ) (ı f : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, lagQ l1 l2 ı t ω = ((β * γ : ℂ) * l3)⁻¹ * fsum 𝔼 l3 f (t + 2) ω

/-- Woodford (2003), eq. (3.23) = (G.22), p. 595, **Rule II**:
`(1 − λ₁L)(1 − λ₃L) ı̂_n = (βγλ₂)⁻¹ E_n[(1 − λ₂⁻¹L⁻¹)⁻¹ f̂_n]`. -/
def RuleII (β γ : ℝ) (l1 l2 l3 : ℂ) (ı f : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, lagQ l1 l3 ı t ω = ((β * γ : ℂ) * l2)⁻¹ * fsum 𝔼 l2 f (t + 2) ω

/-- Woodford (2003), eq. (3.24) = (G.23), p. 595, **Rule III**:
`(1 − λ₁L)(1 − ½(λ₂ + λ₃)L) ı̂_n = ½(βγλ₃)⁻¹ E_n[…λ₃…] + ½(βγλ₂)⁻¹ E_n[…λ₂…]`. -/
def RuleIII (β γ : ℝ) (l1 l2 l3 : ℂ) (ı f : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, lagQ l1 ((l2 + l3) / 2) ı t ω =
    ((β * γ : ℂ) * l3)⁻¹ * fsum 𝔼 l3 f (t + 2) ω / 2 +
      ((β * γ : ℂ) * l2)⁻¹ * fsum 𝔼 l2 f (t + 2) ω / 2

/-- Woodford (2003), App. G.7, p. 728: Rule II is Rule I with `λ₂` and `λ₃` interchanged. -/
theorem ruleII_eq_ruleI (β γ : ℝ) (l1 l2 l3 : ℂ) (ı f : ℕ → Ω → ℝ) (t : ℕ) :
    RuleII 𝔼 β γ l1 l2 l3 ı f t ↔ RuleI 𝔼 β γ l1 l3 l2 ı f t := Iff.rfl

/-- `EC_t` of a complex combination of three real random variables (Woodford (2003), App. G.7). -/
theorem EC_comb (t : ℕ) (c d : ℂ) (x y z : Ω → ℝ) :
    EC 𝔼 t (fun ω => (x ω : ℂ) - c * (y ω : ℂ) + d * (z ω : ℂ)) =
      fun ω => (𝔼.E t x ω : ℂ) - c * (𝔼.E t y ω : ℂ) + d * (𝔼.E t z ω : ℂ) := by
  rw [EC_add_fun 𝔼 t (fun ω => (x ω : ℂ) - c * (y ω : ℂ)) (fun ω => d * (z ω : ℂ)),
    EC_sub_fun 𝔼 t (fun ω => (x ω : ℂ)) (fun ω => c * (y ω : ℂ)), EC_const_mul, EC_const_mul,
    EC_ofReal, EC_ofReal, EC_ofReal]

/-- Woodford (2003), App. G.7: `(1 − λ₁L)(1 − μL) ı̂_n` is known at date `n` when `ı̂` is
adapted. -/
theorem EC_lagQ {ı : ℕ → Ω → ℝ} (hı : 𝔼.Adapted ı) (l1 μ : ℂ) (t : ℕ) :
    EC 𝔼 (t + 2) (lagQ l1 μ ı t) = lagQ l1 μ ı t := by
  have e : lagQ l1 μ ı t = fun ω => (ı (t + 2) ω : ℂ) - (l1 + μ) * (ı (t + 1) ω : ℂ) +
      l1 * μ * (ı t ω : ℂ) := rfl
  rw [e, EC_comb, hı (t + 2), ForwardSolution.E_of_known 𝔼 (by omega) (hı (t + 1)),
    ForwardSolution.E_of_known 𝔼 (by omega) (hı t)]

/-- Woodford (2003), App. G.7: `E_n[(1 − λ₁L)(1 − μL) ı̂_{n+1}]`. -/
theorem EC_lagQ_succ {ı : ℕ → Ω → ℝ} (hı : 𝔼.Adapted ı) (l1 μ : ℂ) (t : ℕ) (ω : Ω) :
    EC 𝔼 (t + 2) (lagQ l1 μ ı (t + 1)) ω = (𝔼.E (t + 2) (ı (t + 3)) ω : ℂ) -
      (l1 + μ) * (ı (t + 2) ω : ℂ) + l1 * μ * (ı (t + 1) ω : ℂ) := by
  have e : lagQ l1 μ ı (t + 1) = fun ω => (ı (t + 3) ω : ℂ) - (l1 + μ) * (ı (t + 2) ω : ℂ) +
      l1 * μ * (ı (t + 1) ω : ℂ) := rfl
  rw [e, EC_comb, hı (t + 2), ForwardSolution.E_of_known 𝔼 (by omega) (hı (t + 1))]

/-- `(1 − λ₁L)(1 − μL) ı̂` is bounded when `ı̂` is (Woodford (2003), App. G.7). -/
theorem norm_lagQ_le {ı : ℕ → Ω → ℝ} {M : ℝ} (hb : ∀ t ω, |ı t ω| ≤ M) (l1 μ : ℂ) (t : ℕ)
    (ω : Ω) : ‖lagQ l1 μ ı t ω‖ ≤ (1 + ‖l1 + μ‖ + ‖l1 * μ‖) * M := by
  unfold lagQ
  have h1 : ‖(ı (t + 2) ω : ℂ)‖ ≤ M := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hb _ _
  have h2 : ‖(ı (t + 1) ω : ℂ)‖ ≤ M := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hb _ _
  have h3 : ‖(ı t ω : ℂ)‖ ≤ M := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hb _ _
  calc ‖(ı (t + 2) ω : ℂ) - (l1 + μ) * (ı (t + 1) ω : ℂ) + l1 * μ * (ı t ω : ℂ)‖
      ≤ ‖(ı (t + 2) ω : ℂ)‖ + ‖l1 + μ‖ * ‖(ı (t + 1) ω : ℂ)‖ + ‖l1 * μ‖ * ‖(ı t ω : ℂ)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        exact add_le_add_left (norm_sub_le _ _ |>.trans (by rw [norm_mul])) _
    _ ≤ M + ‖l1 + μ‖ * M + ‖l1 * μ‖ * M := by gcongr
    _ = (1 + ‖l1 + μ‖ + ‖l1 * μ‖) * M := by ring

/-- Woodford (2003), (3.20) and App. G.7, p. 728: with the factorization
`A(L) = βγ(1 − λ₁L)(1 − λ₂L)(1 − λ₃L)`,
`A(L) ı̂_{n+1} = βγ[(1 − λ₁L)(1 − λ₂L) ı̂_{n+1} − λ₃ (1 − λ₁L)(1 − λ₂L) ı̂_n]`. -/
theorem ALi_factor {β γ κ σ : ℝ} {l1 l2 l3 : ℂ}
    (hfac : ∀ z : ℂ, ApolyC β γ κ σ z = (β * γ : ℝ) * (1 - l1 * z) * (1 - l2 * z) *
      (1 - l3 * z)) (ı : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (ALi β γ κ σ ı t ω : ℂ) =
      (β * γ : ℂ) * (lagQ l1 l2 ı (t + 1) ω - l3 * lagQ l1 l2 ı t ω) := by
  obtain ⟨v1, v2, v3⟩ := vieta_of_factor hfac
  unfold ALi lagQ
  push_cast
  linear_combination (ı (t + 2) ω : ℂ) * v1 - (ı (t + 1) ω : ℂ) * v2 + (ı t ω : ℂ) * v3

/-- Woodford (2003), App. G.7, p. 728: the Euler equation (G.24) at date `n` is equivalent to the
first-order forward recursion
`(1 − λ₁L)(1 − λ₂L) ı̂_n = λ₃⁻¹ E_n[(1 − λ₁L)(1 − λ₂L) ı̂_{n+1}] + (βγλ₃)⁻¹ f̂_n`. -/
theorem euler_iff_recursion {β γ κ σ : ℝ} {l1 l2 l3 : ℂ}
    (hfac : ∀ z : ℂ, ApolyC β γ κ σ z = (β * γ : ℝ) * (1 - l1 * z) * (1 - l2 * z) *
      (1 - l3 * z)) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hl3 : l3 ≠ 0) {ı f : ℕ → Ω → ℝ}
    (hı : 𝔼.Adapted ı) (t : ℕ) :
    Euler 𝔼 β γ κ σ ı f t ↔ ∀ ω, lagQ l1 l2 ı t ω =
      l3⁻¹ * EC 𝔼 (t + 2) (lagQ l1 l2 ı (t + 1)) ω + ((β * γ : ℂ) * l3)⁻¹ * (f (t + 2) ω : ℂ) := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have key : ∀ ω, (𝔼.E (t + 2) (ALi β γ κ σ ı t) ω : ℂ) = (β * γ : ℂ) *
      (EC 𝔼 (t + 2) (lagQ l1 l2 ı (t + 1)) ω - l3 * lagQ l1 l2 ı t ω) := by
    intro ω
    have e1 : (fun ω' => (ALi β γ κ σ ı t ω' : ℂ)) = fun ω' => (β * γ : ℂ) *
        (lagQ l1 l2 ı (t + 1) ω' - l3 * lagQ l1 l2 ı t ω') :=
      funext fun ω' => ALi_factor hfac ı t ω'
    have e2 := congrFun (EC_ofReal 𝔼 (t + 2) (ALi β γ κ σ ı t)) ω
    rw [← e2, e1, EC_const_mul, EC_sub_fun, EC_const_mul, EC_lagQ 𝔼 hı]
  constructor
  · intro h ω
    have h1 := key ω
    rw [h ω] at h1
    field_simp
    push_cast at h1
    linear_combination h1
  · intro h ω
    have h1 := key ω
    rw [h ω] at h1
    have : ((𝔼.E (t + 2) (ALi β γ κ σ ı t) ω : ℝ) : ℂ) = ((-f (t + 2) ω : ℝ) : ℂ) := by
      rw [h1]
      push_cast
      field_simp
      ring
    exact_mod_cast this

/-- The forcing term `u_t = c f̂_{t+2}` of the forward recursion (Woodford (2003), App. G.7). -/
noncomputable def fC (c : ℂ) (f : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℂ := c * (f (t + 2) ω : ℂ)

/-- The forward series of `c f̂` is `c ∑ μ⁻ʲ E_n f̂_{n+j}` (Woodford (2003), App. G.7, p. 728). -/
theorem fwdC_fC (c μ : ℂ) (f : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    fwdC 𝔼 2 μ⁻¹ (fC c f) t ω = c * fsum 𝔼 μ f (t + 2) ω := by
  unfold fwdC fsum fC
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [EC_const_mul, EC_ofReal, show t + j + 2 = t + 2 + j by ring]
  ring

/-- `c f̂_{t+2}` is known at `t + 2` (Woodford (2003), App. G.7). -/
theorem EC_fC {f : ℕ → Ω → ℝ} (hf : 𝔼.Adapted f) (c : ℂ) (t : ℕ) :
    EC 𝔼 (t + 2) (fC c f t) = fC c f t := by
  unfold fC
  rw [EC_const_mul, EC_ofReal, hf (t + 2)]

/-- `c f̂` is bounded when `f̂` is (Woodford (2003), App. G.7). -/
theorem norm_fC_le {f : ℕ → Ω → ℝ} {M : ℝ} (hb : ∀ t ω, |f t ω| ≤ M) (c : ℂ) (t : ℕ)
    (ω : Ω) : ‖fC c f t ω‖ ≤ ‖c‖ * M := by
  unfold fC
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hb _ _) (norm_nonneg _)

/-- Woodford (2003), **Proposition 8.8, Rule I** (App. G.7, p. 728): if `|λ₃| > 1` (real or
complex), bounded adapted `{ı̂, f̂}` satisfy (3.22) at all dates `≥ t₀` iff they satisfy (3.21)
at all those dates. -/
theorem ruleI_iff_euler {β γ κ σ : ℝ} {l1 l2 l3 : ℂ}
    (hfac : ∀ z : ℂ, ApolyC β γ κ σ z = (β * γ : ℝ) * (1 - l1 * z) * (1 - l2 * z) *
      (1 - l3 * z)) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hl3 : 1 < ‖l3‖) {ı f : ℕ → Ω → ℝ}
    (hı : 𝔼.Adapted ı) (hf : 𝔼.Adapted f) {Mı Mf : ℝ} (hıb : ∀ t ω, |ı t ω| ≤ Mı)
    (hfb : ∀ t ω, |f t ω| ≤ Mf) (t0 : ℕ) :
    (∀ t, t0 ≤ t → RuleI 𝔼 β γ l1 l2 l3 ı f t) ↔ (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ ı f t) := by
  have hl3' : l3 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hl3
    linarith
  have ha : ‖l3⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hl3
  have hrec := solves_iff_fwdC 𝔼 ha (u := fC ((β * γ : ℂ) * l3)⁻¹ f) (y := lagQ l1 l2 ı)
    (norm_fC_le hfb _) (EC_fC 𝔼 hf _) (norm_lagQ_le hıb l1 l2) t0
  simp only [fwdC_fC] at hrec
  constructor
  · intro h t ht
    rw [euler_iff_recursion 𝔼 hfac hβ hγ hl3' hı]
    exact hrec.mpr (fun t ht ω => h t ht ω) t ht
  · intro h t ht ω
    exact hrec.mp (fun t ht => (euler_iff_recursion 𝔼 hfac hβ hγ hl3' hı t).mp (h t ht)) t ht ω

/-- Woodford (2003), **Proposition 8.8, Rule II** (App. G.7, p. 729: "replacing `λ₂` with `λ₃`
and vice versa"): if `|λ₂| > 1`, (3.23) at all dates `≥ t₀` iff (3.21) at all those dates. -/
theorem ruleII_iff_euler {β γ κ σ : ℝ} {l1 l2 l3 : ℂ}
    (hfac : ∀ z : ℂ, ApolyC β γ κ σ z = (β * γ : ℝ) * (1 - l1 * z) * (1 - l2 * z) *
      (1 - l3 * z)) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hl2 : 1 < ‖l2‖) {ı f : ℕ → Ω → ℝ}
    (hı : 𝔼.Adapted ı) (hf : 𝔼.Adapted f) {Mı Mf : ℝ} (hıb : ∀ t ω, |ı t ω| ≤ Mı)
    (hfb : ∀ t ω, |f t ω| ≤ Mf) (t0 : ℕ) :
    (∀ t, t0 ≤ t → RuleII 𝔼 β γ l1 l2 l3 ı f t) ↔ (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ ı f t) := by
  have hfac' : ∀ z : ℂ, ApolyC β γ κ σ z = (β * γ : ℝ) * (1 - l1 * z) * (1 - l3 * z) *
      (1 - l2 * z) := fun z => by rw [hfac z]; ring
  exact ruleI_iff_euler 𝔼 hfac' hβ hγ hl2 hı hf hıb hfb t0

/-- `EC_t` as a `ℂ`-linear map (Woodford (2003), App. G.7: the complexification of `E_t`). -/
noncomputable def ECL (t : ℕ) : (Ω → ℂ) →ₗ[ℂ] (Ω → ℂ) :=
  { toFun := EC 𝔼 t
    map_add' := fun z w => EC_add 𝔼 t z w
    map_smul' := fun c z => EC_const_mul 𝔼 t c z }

/-- `ECL t` applied is `EC t` (Woodford (2003), App. G.7). -/
theorem ECL_apply (t : ℕ) (z : Ω → ℂ) : ECL 𝔼 t z = EC 𝔼 t z := rfl

/-- The forward series is known at `t + m` (Woodford (2003), App. G.7: "describes a bounded
stochastic process" adapted to the information set). -/
theorem EC_fwdC {m : ℕ} {a : ℂ} (ha : ‖a‖ < 1) {u : ℕ → Ω → ℂ} {M : ℝ}
    (hu : ∀ t ω, ‖u t ω‖ ≤ M) (t : ℕ) : EC 𝔼 (t + m) (fwdC 𝔼 m a u t) = fwdC 𝔼 m a u t := by
  funext ω
  have hgeo : Summable (fun j : ℕ => ‖a‖ ^ j * (2 * M)) :=
    (summable_geometric_of_lt_one (norm_nonneg a) ha).mul_right _
  have h1 := EC_tsum 𝔼 hgeo (f := fun j ω' => a ^ j * EC 𝔼 (t + m) (u (t + j)) ω')
    (fun j ω' => norm_fwdC_term_le 𝔼 hu t j ω') (t + m) ω
  unfold fwdC
  rw [h1]
  refine tsum_congr fun j => ?_
  rw [EC_const_mul, EC_known 𝔼 le_rfl]

/-- `|A(L) ı̂_{n+1}|` is bounded when `ı̂` is (Woodford (2003), App. G.7). -/
theorem abs_ALi_le {β γ κ σ : ℝ} {ı : ℕ → Ω → ℝ} {M : ℝ} (hb : ∀ t ω, |ı t ω| ≤ M) (t : ℕ)
    (ω : Ω) : |ALi β γ κ σ ı t ω| ≤
      (|β * γ| + |1 + γ + β * γ| + |coefA2 β γ κ σ| + |β⁻¹|) * M := by
  unfold ALi
  have h1 := hb (t + 3) ω
  have h2 := hb (t + 2) ω
  have h3 := hb (t + 1) ω
  have h4 := hb t ω
  calc |β * γ * ı (t + 3) ω - (1 + γ + β * γ) * ı (t + 2) ω + coefA2 β γ κ σ * ı (t + 1) ω -
        β⁻¹ * ı t ω|
      ≤ |β * γ| * |ı (t + 3) ω| + |1 + γ + β * γ| * |ı (t + 2) ω| +
          |coefA2 β γ κ σ| * |ı (t + 1) ω| + |β⁻¹| * |ı t ω| := by
        simp only [← abs_mul]
        exact (abs_sub _ _).trans (add_le_add_left ((abs_add_le _ _).trans
          (add_le_add_left (abs_sub _ _) _)) _) |>.trans (by linarith)
    _ ≤ |β * γ| * M + |1 + γ + β * γ| * M + |coefA2 β γ κ σ| * M + |β⁻¹| * M := by gcongr
    _ = _ := by ring

/-- Woodford (2003), App. G.7, p. 729: the polynomial identity behind the Rule III converse,
`(1 − ½(λ₂+λ₃)L) A(L) ı̂_{n+2} = βγ(1 − λ₂L)(1 − λ₃L)[(1 − λ₁L)(1 − ½(λ₂+λ₃)L) ı̂_{n+2}]`. -/
theorem ALi_ruleIII_identity {β γ κ σ : ℝ} {l1 l2 l3 : ℂ}
    (hfac : ∀ z : ℂ, ApolyC β γ κ σ z = (β * γ : ℝ) * (1 - l1 * z) * (1 - l2 * z) *
      (1 - l3 * z)) (ı : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (ALi β γ κ σ ı (t + 1) ω : ℂ) - (l2 + l3) / 2 * (ALi β γ κ σ ı t ω : ℂ) =
      (β * γ : ℂ) * (lagQ l1 ((l2 + l3) / 2) ı (t + 2) ω -
        (l2 + l3) * lagQ l1 ((l2 + l3) / 2) ı (t + 1) ω +
          l2 * l3 * lagQ l1 ((l2 + l3) / 2) ı t ω) := by
  obtain ⟨v1, v2, v3⟩ := vieta_of_factor hfac
  unfold ALi lagQ
  push_cast
  linear_combination ((ı (t + 3) ω : ℂ) - (l2 + l3) / 2 * (ı (t + 2) ω : ℂ)) * v1 -
    ((ı (t + 2) ω : ℂ) - (l2 + l3) / 2 * (ı (t + 1) ω : ℂ)) * v2 +
    ((ı (t + 1) ω : ℂ) - (l2 + l3) / 2 * (ı t ω : ℂ)) * v3

/-- Woodford (2003), App. G.7, p. 729: for the forward solution `F = (βγμ)⁻¹ E(1 − μ⁻¹L⁻¹)⁻¹f̂`
and any `ν`, `E_n[βγ(1 − νL)(1 − μL) F_{n+2}] = −(E_n f̂_{n+1} − ν f̂_n)`. -/
theorem EC_quad_fwd {β γ : ℝ} (hβ : β ≠ 0) (hγ : γ ≠ 0) {μ : ℂ} (hμ : 1 < ‖μ‖) (ν : ℂ)
    {f : ℕ → Ω → ℝ} (hf : 𝔼.Adapted f) {Mf : ℝ} (hfb : ∀ t ω, |f t ω| ≤ Mf) (t : ℕ)
    (ω : Ω) :
    (β * γ : ℂ) * EC 𝔼 (t + 2) (fun ω' =>
      fwdC 𝔼 2 μ⁻¹ (fC ((β * γ : ℂ) * μ)⁻¹ f) (t + 2) ω' -
        (ν + μ) * fwdC 𝔼 2 μ⁻¹ (fC ((β * γ : ℂ) * μ)⁻¹ f) (t + 1) ω' +
          ν * μ * fwdC 𝔼 2 μ⁻¹ (fC ((β * γ : ℂ) * μ)⁻¹ f) t ω') ω =
      -((𝔼.E (t + 2) (f (t + 3)) ω : ℂ) - ν * (f (t + 2) ω : ℂ)) := by
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hμ
    linarith
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have ha : ‖μ⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hμ
  set F := fwdC 𝔼 2 μ⁻¹ (fC ((β * γ : ℂ) * μ)⁻¹ f) with hFdef
  have hu := norm_fC_le hfb ((β * γ : ℂ) * μ)⁻¹
  have hua := EC_fC 𝔼 hf ((β * γ : ℂ) * μ)⁻¹
  have hrec : ∀ n ω', F n ω' = μ⁻¹ * EC 𝔼 (n + 2) (F (n + 1)) ω' +
      ((β * γ : ℂ) * μ)⁻¹ * (f (n + 2) ω' : ℂ) := fun n ω' => fwdC_solves 𝔼 ha hu hua n ω'
  have hEF : ∀ n ω', EC 𝔼 (n + 2) (F (n + 1)) ω' =
      μ * F n ω' - (β * γ : ℂ)⁻¹ * (f (n + 2) ω' : ℂ) := by
    intro n ω'
    rw [hrec n ω']
    field_simp
    ring
  have hFa : EC 𝔼 (t + 2) (F t) = F t := EC_fwdC 𝔼 ha hu t
  have hF2 : EC 𝔼 (t + 2) (F (t + 2)) ω = μ * EC 𝔼 (t + 2) (F (t + 1)) ω -
      (β * γ : ℂ)⁻¹ * (𝔼.E (t + 2) (f (t + 3)) ω : ℂ) := by
    rw [← EC_tower 𝔼 (show t + 2 ≤ t + 1 + 2 by omega) (F (t + 2))]
    have e : EC 𝔼 (t + 1 + 2) (F (t + 1 + 1)) = fun ω' =>
        μ * F (t + 1) ω' + (-(β * γ : ℂ)⁻¹) * (f (t + 1 + 2) ω' : ℂ) := by
      funext ω'
      rw [hEF (t + 1) ω']
      ring
    rw [e, EC_add_fun, EC_const_mul, EC_const_mul, EC_ofReal]
    simp only
    rw [show t + 1 + 2 = t + 3 by ring]
    ring
  have e : (fun ω' => F (t + 2) ω' - (ν + μ) * F (t + 1) ω' + ν * μ * F t ω') =
      fun ω' => (F (t + 2) ω' + (-(ν + μ)) * F (t + 1) ω') + ν * μ * F t ω' := by
    funext ω'
    ring
  rw [e, EC_add_fun, EC_add_fun, EC_const_mul, EC_const_mul, hFa]
  simp only
  rw [hF2, hEF t ω]
  field_simp
  ring

/-- Woodford (2003), **Proposition 8.8, Rule III, "(G.24) ⇒ (G.23)"** (App. G.7, p. 729): the
Euler equation implies (3.24), by averaging Rules I and II (needs `|λ₂|, |λ₃| > 1`). -/
theorem ruleIII_of_euler {β γ κ σ : ℝ} {l1 l2 l3 : ℂ}
    (hfac : ∀ z : ℂ, ApolyC β γ κ σ z = (β * γ : ℝ) * (1 - l1 * z) * (1 - l2 * z) *
      (1 - l3 * z)) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hl2 : 1 < ‖l2‖) (hl3 : 1 < ‖l3‖)
    {ı f : ℕ → Ω → ℝ} (hı : 𝔼.Adapted ı) (hf : 𝔼.Adapted f) {Mı Mf : ℝ}
    (hıb : ∀ t ω, |ı t ω| ≤ Mı) (hfb : ∀ t ω, |f t ω| ≤ Mf) (t0 : ℕ)
    (h : ∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ ı f t) : ∀ t, t0 ≤ t → RuleIII 𝔼 β γ l1 l2 l3 ı f t := by
  have h1 := (ruleI_iff_euler 𝔼 hfac hβ hγ hl3 hı hf hıb hfb t0).mpr h
  have h2 := (ruleII_iff_euler 𝔼 hfac hβ hγ hl2 hı hf hıb hfb t0).mpr h
  intro t ht ω
  have e : lagQ l1 ((l2 + l3) / 2) ı t ω = (lagQ l1 l2 ı t ω + lagQ l1 l3 ı t ω) / 2 := by
    unfold lagQ
    ring
  rw [e, h1 t ht ω, h2 t ht ω]
  ring

/-- Woodford (2003), **Proposition 8.8, Rule III, "(G.23) ⇒ (G.24)"** (App. G.7, pp. 729–730):
if `|λ₂|, |λ₃| > 1` and `α = 2/(λ₂ + λ₃)` has `|α| < 1`, then (3.24) at all dates `≥ t₀` implies
the Euler equation (3.21) at all those dates. -/
theorem euler_of_ruleIII {β γ κ σ : ℝ} {l1 l2 l3 : ℂ}
    (hfac : ∀ z : ℂ, ApolyC β γ κ σ z = (β * γ : ℝ) * (1 - l1 * z) * (1 - l2 * z) *
      (1 - l3 * z)) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hl2 : 1 < ‖l2‖) (hl3 : 1 < ‖l3‖)
    (hs : 2 < ‖l2 + l3‖) {ı f : ℕ → Ω → ℝ} (hf : 𝔼.Adapted f)
    {Mı Mf : ℝ} (hıb : ∀ t ω, |ı t ω| ≤ Mı) (hfb : ∀ t ω, |f t ω| ≤ Mf) (t0 : ℕ)
    (h : ∀ t, t0 ≤ t → RuleIII 𝔼 β γ l1 l2 l3 ı f t) : ∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ ı f t := by
  have hs0 : l2 + l3 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hs
    linarith
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  set F3 := fwdC 𝔼 2 l3⁻¹ (fC ((β * γ : ℂ) * l3)⁻¹ f) with hF3
  set F2 := fwdC 𝔼 2 l2⁻¹ (fC ((β * γ : ℂ) * l2)⁻¹ f) with hF2
  have hvG : ∀ t, t0 ≤ t → ∀ ω, lagQ l1 ((l2 + l3) / 2) ı t ω = (F3 t ω + F2 t ω) / 2 := by
    intro t ht ω
    rw [h t ht ω, hF3, hF2, fwdC_fC, fwdC_fC]
    ring
  -- `e_n = E_n[A(L) ı̂_{n+1}] + f̂_n`
  set e : ℕ → Ω → ℂ := fun n ω => ((𝔼.E (n + 2) (ALi β γ κ σ ı n) ω + f (n + 2) ω : ℝ) : ℂ)
    with he
  have hKey : ∀ t, t0 ≤ t → ∀ ω, e t ω = (2 / (l2 + l3)) * EC 𝔼 (t + 2) (e (t + 1)) ω := by
    intro t ht ω
    -- expectation of the polynomial identity
    have hpoly : (fun ω' => (ALi β γ κ σ ı (t + 1) ω' : ℂ) +
        (-((l2 + l3) / 2)) * (ALi β γ κ σ ı t ω' : ℂ)) = fun ω' =>
        (1 / 2 : ℂ) * ((β * γ : ℂ) * (F3 (t + 2) ω' - (l2 + l3) * F3 (t + 1) ω' +
          l2 * l3 * F3 t ω')) + (1 / 2 : ℂ) * ((β * γ : ℂ) * (F2 (t + 2) ω' -
          (l3 + l2) * F2 (t + 1) ω' + l3 * l2 * F2 t ω')) := by
      funext ω'
      have hid := ALi_ruleIII_identity hfac ı t ω'
      have g2 := hvG (t + 2) (by omega) ω'
      have g1 := hvG (t + 1) (by omega) ω'
      have g0 := hvG t ht ω'
      linear_combination hid + (β * γ : ℂ) * g2 - (β * γ : ℂ) * (l2 + l3) * g1 +
        (β * γ : ℂ) * l2 * l3 * g0
    have hL := congrFun (congrArg (EC 𝔼 (t + 2)) hpoly) ω
    rw [EC_add_fun, EC_const_mul, EC_ofReal, EC_ofReal, EC_add_fun, EC_const_mul, EC_const_mul,
      EC_const_mul, EC_const_mul] at hL
    simp only at hL
    have q3 := EC_quad_fwd 𝔼 hβ hγ hl3 l2 hf hfb t ω
    have q2 := EC_quad_fwd 𝔼 hβ hγ hl2 l3 hf hfb t ω
    rw [← hF3] at q3
    rw [← hF2] at q2
    rw [q3, q2] at hL
    -- `E_{t+2} A(L) ı̂_{t+4} = E_{t+2} E_{t+3} A(L) ı̂_{t+4}`
    have hT : 𝔼.E (t + 2) (ALi β γ κ σ ı (t + 1)) ω =
        𝔼.E (t + 2) (𝔼.E (t + 1 + 2) (ALi β γ κ σ ı (t + 1))) ω := by
      rw [𝔼.tower (show t + 2 ≤ t + 1 + 2 by omega)]
    have hEe : EC 𝔼 (t + 2) (e (t + 1)) ω = ((𝔼.E (t + 2) (ALi β γ κ σ ı (t + 1)) ω +
        𝔼.E (t + 2) (f (t + 3)) ω : ℝ) : ℂ) := by
      have : e (t + 1) = fun ω' => ((𝔼.E (t + 1 + 2) (ALi β γ κ σ ı (t + 1)) ω' +
          f (t + 1 + 2) ω' : ℝ) : ℂ) := rfl
      rw [this, EC_ofReal, E_fun_add]
      simp only
      rw [← hT, show t + 1 + 2 = t + 3 by ring]
    rw [hEe]
    simp only [he]
    push_cast
    field_simp
    linear_combination (-2 : ℂ) * hL
  have hKb : ∀ n ω, ‖e n ω‖ ≤
      (|β * γ| + |1 + γ + β * γ| + |coefA2 β γ κ σ| + |β⁻¹|) * Mı + Mf := by
    intro n ω
    simp only [he, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (add_le_add (𝔼.abs_E_le (abs_ALi_le hıb n) _ ω) (hfb _ _))
  have hα : ‖2 / (l2 + l3)‖ < 1 := by
    rw [norm_div, div_lt_one (by linarith)]
    simpa using hs
  have h0 := eq_zero_of_homog 𝔼 hα hKb hKey
  intro t ht ω
  have := h0 t ht ω
  simp only [he] at this
  have h' : 𝔼.E (t + 2) (ALi β γ κ σ ı t) ω + f (t + 2) ω = 0 := by exact_mod_cast this
  linarith

/-- Woodford (2003), **Proposition 8.8, Rule III** (App. G.7, pp. 729–730): (3.24) at all dates
`≥ t₀` iff (3.21) at all those dates, for real roots or a complex pair (`|λ₂|, |λ₃| > 1`,
`|λ₂ + λ₃| > 2`). -/
theorem ruleIII_iff_euler {β γ κ σ : ℝ} {l1 l2 l3 : ℂ}
    (hfac : ∀ z : ℂ, ApolyC β γ κ σ z = (β * γ : ℝ) * (1 - l1 * z) * (1 - l2 * z) *
      (1 - l3 * z)) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hl2 : 1 < ‖l2‖) (hl3 : 1 < ‖l3‖)
    (hs : 2 < ‖l2 + l3‖) {ı f : ℕ → Ω → ℝ} (hı : 𝔼.Adapted ı) (hf : 𝔼.Adapted f)
    {Mı Mf : ℝ} (hıb : ∀ t ω, |ı t ω| ≤ Mı) (hfb : ∀ t ω, |f t ω| ≤ Mf) (t0 : ℕ) :
    (∀ t, t0 ≤ t → RuleIII 𝔼 β γ l1 l2 l3 ı f t) ↔ (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ ı f t) :=
  ⟨euler_of_ruleIII 𝔼 hfac hβ hγ hl2 hl3 hs hf hıb hfb t0,
    ruleIII_of_euler 𝔼 hfac hβ hγ hl2 hl3 hı hf hıb hfb t0⟩

/-! ### Real-coefficient forms of the rules -/

/-- Woodford (2003), eq. (3.22), p. 595, with real roots `1 < r₂ ≤ r₃` (the real-valued Rule I):
`ı̂_n − (λ₁ + r₂)ı̂_{n−1} + λ₁r₂ ı̂_{n−2} = (βγr₃)⁻¹ ∑ⱼ r₃⁻ʲ E_n f̂_{n+j}`. -/
def RuleIReal (β γ l1 r2 r3 : ℝ) (ı f : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, ı (t + 2) ω - (l1 + r2) * ı (t + 1) ω + l1 * r2 * ı t ω =
    (β * γ * r3)⁻¹ * ∑' j, (r3⁻¹) ^ j * 𝔼.E (t + 2) (f (t + 2 + j)) ω

/-- Woodford (2003), eq. (3.23), p. 595: the real-valued Rule II (Rule I with `r₂ ↔ r₃`). -/
def RuleIIReal (β γ l1 r2 r3 : ℝ) (ı f : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  RuleIReal 𝔼 β γ l1 r3 r2 ı f t

/-- Woodford (2003), eq. (3.22), p. 595: the real Rule I is Rule I with real roots. -/
theorem ruleIReal_iff (β γ l1 r2 r3 : ℝ) (ı f : ℕ → Ω → ℝ) (t : ℕ) :
    RuleIReal 𝔼 β γ l1 r2 r3 ı f t ↔ RuleI 𝔼 β γ (l1 : ℂ) (r2 : ℂ) (r3 : ℂ) ı f t := by
  unfold RuleIReal RuleI lagQ fsum
  refine forall_congr' fun ω => ?_
  rw [← Complex.ofReal_inj]
  push_cast
  rfl

/-- Woodford (2003), eq. (3.24), p. 595: the forward weights of Rule III,
`ψⱼ = ½[(βγλ₃)⁻¹λ₃⁻ʲ + (βγλ₂)⁻¹λ₂⁻ʲ]` (real for real roots and for a conjugate pair). -/
noncomputable def psiIII (β γ : ℝ) (l2 l3 : ℂ) (j : ℕ) : ℂ :=
  (((β * γ : ℂ) * l3)⁻¹ * (l3⁻¹) ^ j + ((β * γ : ℂ) * l2)⁻¹ * (l2⁻¹) ^ j) / 2

/-- Woodford (2003), eq. (3.24), p. 595: Rule III written with real coefficients,
`ı̂_n − (λ₁ + s/2)ı̂_{n−1} + λ₁(s/2) ı̂_{n−2} = ∑ⱼ ψⱼ E_n f̂_{n+j}` with `s = λ₂ + λ₃`. -/
def RuleIIIReal (l1 sR : ℝ) (ψ : ℕ → ℝ) (ı f : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, ı (t + 2) ω - (l1 + sR / 2) * ı (t + 1) ω + l1 * (sR / 2) * ı t ω =
    ∑' j, ψ j * 𝔼.E (t + 2) (f (t + 2 + j)) ω

/-- Summability of `μ⁻ʲ E_n f̂_{n+j}` for `|μ| > 1` and bounded `f̂` (Woodford (2003), p. 595:
the right-hand sides are well defined). -/
theorem summable_fsum_terms {μ : ℂ} (hμ : 1 < ‖μ‖) {f : ℕ → Ω → ℝ} {Mf : ℝ}
    (hfb : ∀ t ω, |f t ω| ≤ Mf) (n : ℕ) (ω : Ω) :
    Summable (fun j => (μ⁻¹) ^ j * (𝔼.E n (f (n + j)) ω : ℂ)) := by
  have ha : ‖μ⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hμ
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg _) ha).mul_right Mf)
    (fun j => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hfb _) n ω) (by positivity)

/-- Woodford (2003), eq. (3.24), p. 595: the right-hand side of Rule III is `∑ⱼ ψⱼ E_n f̂_{n+j}`. -/
theorem ruleIII_rhs {β γ : ℝ} {l2 l3 : ℂ} (hl2 : 1 < ‖l2‖) (hl3 : 1 < ‖l3‖)
    {f : ℕ → Ω → ℝ} {Mf : ℝ} (hfb : ∀ t ω, |f t ω| ≤ Mf) (n : ℕ) (ω : Ω) :
    ((β * γ : ℂ) * l3)⁻¹ * fsum 𝔼 l3 f n ω / 2 + ((β * γ : ℂ) * l2)⁻¹ * fsum 𝔼 l2 f n ω / 2 =
      ∑' j, psiIII β γ l2 l3 j * (𝔼.E n (f (n + j)) ω : ℂ) := by
  have s3 := (summable_fsum_terms 𝔼 hl3 hfb n ω).mul_left (((β * γ : ℂ) * l3)⁻¹ / 2)
  have s2 := (summable_fsum_terms 𝔼 hl2 hfb n ω).mul_left (((β * γ : ℂ) * l2)⁻¹ / 2)
  unfold fsum
  rw [mul_div_right_comm, mul_div_right_comm (((β * γ : ℂ) * l2)⁻¹), ← tsum_mul_left,
    ← tsum_mul_left, ← s3.tsum_add s2]
  refine tsum_congr fun j => ?_
  unfold psiIII
  ring

/-- Woodford (2003), p. 595: with real roots the weights `ψⱼ` are real. -/
theorem psiIII_ofReal (β γ r2 r3 : ℝ) (j : ℕ) :
    psiIII β γ (r2 : ℂ) (r3 : ℂ) j =
      (((β * γ * r3)⁻¹ * (r3⁻¹) ^ j + (β * γ * r2)⁻¹ * (r2⁻¹) ^ j) / 2 : ℝ) := by
  unfold psiIII
  push_cast
  ring

/-- Woodford (2003), p. 595 ("relation (3.24) … has real coefficients on all leads and lags in
the case that `λ₂, λ₃` are a complex pair"): for `λ₃ = conj λ₂` the weights `ψⱼ` are real. -/
theorem psiIII_conj {β γ : ℝ} {l2 l3 : ℂ} (hc : l3 = (starRingEnd ℂ) l2) (j : ℕ) :
    psiIII β γ l2 l3 j = ((psiIII β γ l2 l3 j).re : ℂ) := by
  set w := ((β * γ : ℂ) * l2)⁻¹ * (l2⁻¹) ^ j with hw
  have hcw : ((β * γ : ℂ) * l3)⁻¹ * (l3⁻¹) ^ j = (starRingEnd ℂ) w := by
    rw [hc, hw]
    simp only [map_mul, map_inv₀, map_pow, Complex.conj_ofReal]
  have e : psiIII β γ l2 l3 j = ((starRingEnd ℂ) w + w) / 2 := by
    unfold psiIII
    rw [hcw]
  apply Complex.ext
  · simp
  · rw [e]
    simp [Complex.div_ofNat_im]

/-- Woodford (2003), eq. (3.24), p. 595: the real form of Rule III is equivalent to the complex
form whenever `λ₂ + λ₃` and all `ψⱼ` are real. -/
theorem ruleIIIReal_iff {β γ : ℝ} {l1 sR : ℝ} {l2 l3 : ℂ} {ψ : ℕ → ℝ}
    (hs : l2 + l3 = (sR : ℂ)) (hψ : ∀ j, psiIII β γ l2 l3 j = (ψ j : ℂ))
    (hl2 : 1 < ‖l2‖) (hl3 : 1 < ‖l3‖) {ı f : ℕ → Ω → ℝ} {Mf : ℝ}
    (hfb : ∀ t ω, |f t ω| ≤ Mf) (t : ℕ) :
    RuleIIIReal 𝔼 l1 sR ψ ı f t ↔ RuleIII 𝔼 β γ (l1 : ℂ) l2 l3 ı f t := by
  unfold RuleIIIReal RuleIII
  refine forall_congr' fun ω => ?_
  rw [ruleIII_rhs 𝔼 hl2 hl3 hfb, hs]
  simp only [hψ]
  rw [← Complex.ofReal_inj]
  unfold lagQ
  push_cast
  rfl

/-- Woodford (2003), p. 597 ("when `γ = γ̄`, rules I, II, and III are all identical"): if
`λ₂ = λ₃` the three rules coincide. -/
theorem rules_coincide {β γ : ℝ} {l1 l2 l3 : ℂ} (hl : l2 = l3) (ı f : ℕ → Ω → ℝ) (t : ℕ) :
    (RuleI 𝔼 β γ l1 l2 l3 ı f t ↔ RuleII 𝔼 β γ l1 l2 l3 ı f t) ∧
      (RuleI 𝔼 β γ l1 l2 l3 ı f t ↔ RuleIII 𝔼 β γ l1 l2 l3 ı f t) := by
  subst hl
  refine ⟨Iff.rfl, ?_⟩
  unfold RuleI RuleIII
  have e : (l2 + l2) / 2 = l2 := by ring
  rw [e]
  refine forall_congr' fun ω => ?_
  rw [add_halves]

/-! ### Proposition 8.8 for the roots of Proposition 8.7 -/

variable {β γ κ σ : ℝ}

/-- Woodford (2003), **Proposition 8.8** (Rule I), p. 595, with the canonical roots of
Proposition 8.7 (valid for real roots, and over `ℂ` for a complex pair). -/
theorem prop_8_8_ruleI (h : Standing β γ κ σ) {ı f : ℕ → Ω → ℝ} (hı : 𝔼.Adapted ı)
    (hf : 𝔼.Adapted f) {Mı Mf : ℝ} (hıb : ∀ t ω, |ı t ω| ≤ Mı) (hfb : ∀ t ω, |f t ω| ≤ Mf)
    (t0 : ℕ) :
    (∀ t, t0 ≤ t → RuleI 𝔼 β γ (lam1 β γ κ σ) (lam2 β γ κ σ) (lam3 β γ κ σ) ı f t) ↔
      (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ ı f t) :=
  ruleI_iff_euler 𝔼 (ApolyC_factor h) h.beta_pos.ne' h.gamma_pos.ne' (one_lt_norm_lam3 h) hı hf
    hıb hfb t0

/-- Woodford (2003), **Proposition 8.8** (Rule II), p. 595, with the canonical roots. -/
theorem prop_8_8_ruleII (h : Standing β γ κ σ) {ı f : ℕ → Ω → ℝ} (hı : 𝔼.Adapted ı)
    (hf : 𝔼.Adapted f) {Mı Mf : ℝ} (hıb : ∀ t ω, |ı t ω| ≤ Mı) (hfb : ∀ t ω, |f t ω| ≤ Mf)
    (t0 : ℕ) :
    (∀ t, t0 ≤ t → RuleII 𝔼 β γ (lam1 β γ κ σ) (lam2 β γ κ σ) (lam3 β γ κ σ) ı f t) ↔
      (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ ı f t) :=
  ruleII_iff_euler 𝔼 (ApolyC_factor h) h.beta_pos.ne' h.gamma_pos.ne' (one_lt_norm_lam2 h) hı hf
    hıb hfb t0

/-- Woodford (2003), App. G.7, p. 730: `|λ₂ + λ₃| = S > 2`, i.e. `α = 2/(λ₂ + λ₃) < 1`. -/
theorem two_lt_norm_lam2_add_lam3 (h : Standing β γ κ σ) :
    2 < ‖lam2 β γ κ σ + lam3 β γ κ σ‖ := by
  rw [lam2_add_lam3, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith [two_lt_sumS h])]
  exact two_lt_sumS h

/-- Woodford (2003), **Proposition 8.8** (Rule III), p. 595, complex form, canonical roots. -/
theorem prop_8_8_ruleIII (h : Standing β γ κ σ) {ı f : ℕ → Ω → ℝ} (hı : 𝔼.Adapted ı)
    (hf : 𝔼.Adapted f) {Mı Mf : ℝ} (hıb : ∀ t ω, |ı t ω| ≤ Mı) (hfb : ∀ t ω, |f t ω| ≤ Mf)
    (t0 : ℕ) :
    (∀ t, t0 ≤ t → RuleIII 𝔼 β γ (lam1 β γ κ σ) (lam2 β γ κ σ) (lam3 β γ κ σ) ı f t) ↔
      (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ ı f t) :=
  ruleIII_iff_euler 𝔼 (ApolyC_factor h) h.beta_pos.ne' h.gamma_pos.ne' (one_lt_norm_lam2 h)
    (one_lt_norm_lam3 h) (two_lt_norm_lam2_add_lam3 h) hı hf hıb hfb t0

/-- Woodford (2003), p. 595: the canonical Rule III weights `ψⱼ` are real (both cases). -/
theorem psiIII_canonical_real (j : ℕ) :
    psiIII β γ (lam2 β γ κ σ) (lam3 β γ κ σ) j =
      ((psiIII β γ (lam2 β γ κ σ) (lam3 β γ κ σ) j).re : ℂ) := by
  rcases le_or_gt 0 (discQ β γ κ σ) with hD | hD
  · rw [lam2_eq_ofReal rfl hD, lam3_eq_ofReal rfl hD, psiIII_ofReal, Complex.ofReal_re]
  · exact psiIII_conj (lam3_eq_conj hD) j

/-- Woodford (2003), **Proposition 8.8** (Rule III, real coefficients), p. 595: in BOTH cases
(three real roots, or a complex pair), the real-coefficient rule (3.24)
`ı̂_n − (λ₁ + S/2)ı̂_{n−1} + λ₁(S/2) ı̂_{n−2} = ∑ⱼ ψⱼ E_n f̂_{n+j}` holds at all dates `≥ t₀` iff
(3.21) does. -/
theorem prop_8_8_ruleIII_real (h : Standing β γ κ σ) {ı f : ℕ → Ω → ℝ} (hı : 𝔼.Adapted ı)
    (hf : 𝔼.Adapted f) {Mı Mf : ℝ} (hıb : ∀ t ω, |ı t ω| ≤ Mı) (hfb : ∀ t ω, |f t ω| ≤ Mf)
    (t0 : ℕ) :
    (∀ t, t0 ≤ t → RuleIIIReal 𝔼 (lam1 β γ κ σ) (sumS β γ κ σ)
        (fun j => (psiIII β γ (lam2 β γ κ σ) (lam3 β γ κ σ) j).re) ı f t) ↔
      (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ ı f t) := by
  rw [← prop_8_8_ruleIII 𝔼 h hı hf hıb hfb t0]
  refine forall_congr' fun t => forall_congr' fun _ => ?_
  exact ruleIIIReal_iff 𝔼 lam2_add_lam3 psiIII_canonical_real (one_lt_norm_lam2 h)
    (one_lt_norm_lam3 h) hfb t

/-- Woodford (2003), **Proposition 8.8** (three real roots), p. 595: when `S² − 4P₂₃ ≥ 0`
(equivalently `Δ ≤ 0`), each of the real-valued rules (3.22) and (3.23) holds at all dates
`≥ t₀` iff (3.21) does. -/
theorem prop_8_8_real (h : Standing β γ κ σ) (hD : 0 ≤ discQ β γ κ σ) {ı f : ℕ → Ω → ℝ}
    (hı : 𝔼.Adapted ı) (hf : 𝔼.Adapted f) {Mı Mf : ℝ} (hıb : ∀ t ω, |ı t ω| ≤ Mı)
    (hfb : ∀ t ω, |f t ω| ≤ Mf) (t0 : ℕ) :
    ((∀ t, t0 ≤ t → RuleIReal 𝔼 β γ (lam1 β γ κ σ) (lam2r β γ κ σ) (lam3r β γ κ σ) ı f t) ↔
      (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ ı f t)) ∧
    ((∀ t, t0 ≤ t → RuleIIReal 𝔼 β γ (lam1 β γ κ σ) (lam2r β γ κ σ) (lam3r β γ κ σ) ı f t) ↔
      (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ ı f t)) := by
  constructor
  · rw [← prop_8_8_ruleI 𝔼 h hı hf hıb hfb t0, lam2_eq_ofReal rfl hD, lam3_eq_ofReal rfl hD]
    exact forall_congr' fun t => forall_congr' fun _ => ruleIReal_iff 𝔼 _ _ _ _ _ ı f t
  · rw [← prop_8_8_ruleII 𝔼 h hı hf hıb hfb t0, lam2_eq_ofReal rfl hD, lam3_eq_ofReal rfl hD]
    exact forall_congr' fun t => forall_congr' fun _ => ruleIReal_iff 𝔼 _ _ _ _ _ ı f t

/-- Woodford (2003), p. 597: at a bifurcation point (`Δ(γ) = 0`) the canonical rules I, II and
III coincide. -/
theorem rules_coincide_at_bifurcation (h : Standing β γ κ σ) (hΔ : deltaG β γ κ σ = 0)
    (ı f : ℕ → Ω → ℝ) (t : ℕ) :
    (RuleI 𝔼 β γ (lam1 β γ κ σ) (lam2 β γ κ σ) (lam3 β γ κ σ) ı f t ↔
        RuleII 𝔼 β γ (lam1 β γ κ σ) (lam2 β γ κ σ) (lam3 β γ κ σ) ı f t) ∧
      (RuleI 𝔼 β γ (lam1 β γ κ σ) (lam2 β γ κ σ) (lam3 β γ κ σ) ı f t ↔
        RuleIII 𝔼 β γ (lam1 β γ κ σ) (lam2 β γ κ σ) (lam3 β γ κ σ) ı f t) :=
  rules_coincide 𝔼 ((repeated_root_iff h).mp hΔ) ı f t

/-! ### The limit `γ → 0` (pp. 596–597) and continuity in `γ` -/

/-- Woodford (2003), p. 596 and fn 44: as `γ → 0⁺` the lag coefficients of Rule I converge to
those of (3.10): `λ₁ + λ₂ → ρ₁ + ρ₂ = 1 + κσ/β + β⁻¹` and `λ₁λ₂ → ρ₂ = β⁻¹` (cf. (3.8)). -/
theorem ruleI_lag_coeffs_limit (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun γ => lam1 β γ κ σ + lam2r β γ κ σ) (𝓝[>] 0) (𝓝 (1 + κ * σ / β + β⁻¹)) ∧
      Tendsto (fun γ => lam1 β γ κ σ * lam2r β γ κ σ) (𝓝[>] 0) (𝓝 β⁻¹) := by
  have h1 := tendsto_lam1_zero hσ hκ hβ hβ1
  have h2 := tendsto_lam2r_zero hσ hκ hβ hβ1
  constructor
  · rw [← mu_sum hβ]
    exact h1.add h2
  · rw [← mu_prod hβ (mul_pos hκ hσ)]
    exact h1.mul h2

/-- Woodford (2003), p. 596 and fn 44: the Rule I lead coefficient `(βγλ₃)⁻¹ → 1` as `γ → 0⁺`. -/
theorem ruleI_lead_coeff_limit (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun γ => (β * γ * lam3r β γ κ σ)⁻¹) (𝓝[>] 0) (𝓝 1) := by
  have h := ((tendsto_gamma_mul_lam3r hσ hκ hβ hβ1).const_mul β).inv₀
    (by rw [mul_inv_cancel₀ hβ.ne']; exact one_ne_zero)
  rw [mul_inv_cancel₀ hβ.ne', inv_one] at h
  refine h.congr fun γ => ?_
  ring_nf

/-- Woodford (2003), p. 596 (Rule I as `γ → 0` "reduces to `(1 − λ₁L)(1 − λ₂L)ı̂_t = f̂_t`"): for a
bounded adapted `f̂`, the right-hand side of Rule I converges to `f̂_n`. -/
theorem ruleI_rhs_limit (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1)
    {f : ℕ → Ω → ℝ} (hf : 𝔼.Adapted f) {Mf : ℝ} (hfb : ∀ t ω, |f t ω| ≤ Mf) (n : ℕ) (ω : Ω) :
    Tendsto (fun γ => (β * γ * lam3r β γ κ σ)⁻¹ *
      ∑' j, ((lam3r β γ κ σ)⁻¹) ^ j * 𝔼.E n (f (n + j)) ω) (𝓝[>] 0) (𝓝 (f n ω)) := by
  have hc := ruleI_lead_coeff_limit hσ hκ hβ hβ1
  have hq : Tendsto (fun γ => (lam3r β γ κ σ)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_lam3r_atTop hσ hκ hβ hβ1).inv_tendsto_atTop
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfb 0 ω)
  -- the series minus `f̂_n` is bounded by `qM/(1 − q)`
  have hbd : Tendsto (fun γ => (lam3r β γ κ σ)⁻¹ * Mf / (1 - (lam3r β γ κ σ)⁻¹)) (𝓝[>] 0)
      (𝓝 0) := by
    have := (hq.mul_const Mf).div (tendsto_const_nhds.sub hq) (by simp : (1 : ℝ) - 0 ≠ 0)
    rw [zero_mul, zero_div] at this
    exact this
  have hS : Tendsto (fun γ => ∑' j, ((lam3r β γ κ σ)⁻¹) ^ j * 𝔼.E n (f (n + j)) ω) (𝓝[>] 0)
      (𝓝 (f n ω)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbd
    filter_upwards [eventually_standing hσ hκ hβ hβ1] with γ hS
    have hl := one_lt_lam3r hS
    set q := (lam3r β γ κ σ)⁻¹ with hqdef
    have hq0 : 0 < q := inv_pos.mpr (by linarith)
    have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hl
    have hsum : Summable (fun j => q ^ j * 𝔼.E n (f (n + j)) ω) :=
      Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0.le hq1).mul_right Mf)
        (fun j => by
          rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hq0]
          exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hfb _) n ω) (by positivity))
    rw [hsum.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero, hf n]
    rw [add_sub_cancel_left]
    refine (tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hq0.le hq1).mul_left (q * Mf))
      (fun j => ?_)).trans (le_of_eq ?_)
    · rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hq0]
      calc q ^ (j + 1) * |𝔼.E n (f (n + (j + 1))) ω| ≤ q ^ (j + 1) * Mf :=
            mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hfb _) n ω) (by positivity)
        _ = q * Mf * q ^ j := by ring
    · rw [div_eq_mul_inv]
  have := hc.mul hS
  rwa [one_mul] at this

/-- Woodford (2003), p. 596 ("in the case of any of the other rules, the coefficients on lagged
interest rates become unboundedly large as `γ` approaches zero"): the lag coefficient
`λ₁ + λ₃` of Rule II and `λ₁ + (λ₂ + λ₃)/2` of Rule III tend to `+∞`. -/
theorem other_rules_unbounded (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun γ => lam1 β γ κ σ + lam3r β γ κ σ) (𝓝[>] 0) atTop ∧
      Tendsto (fun γ => lam1 β γ κ σ + sumS β γ κ σ / 2) (𝓝[>] 0) atTop := by
  have h1 := tendsto_lam1_zero hσ hκ hβ hβ1
  have h2 := tendsto_lam2r_zero hσ hκ hβ hβ1
  have h3 := tendsto_lam3r_atTop hσ hκ hβ hβ1
  refine ⟨h1.add_atTop h3, h1.add_atTop ?_⟩
  have hs : Tendsto (fun γ => sumS β γ κ σ) (𝓝[>] 0) atTop := by
    refine (h2.add_atTop h3).congr fun γ => ?_
    unfold lam2r lam3r
    ring
  exact hs.atTop_div_const two_pos

/-- Woodford (2003), pp. 596–597 ("all coefficients of the policy rule continuous functions of
`γ`"): the lag coefficients `λ₁ + λ₂`, `λ₁λ₂` (Rule I) and `λ₁ + (λ₂+λ₃)/2`, `λ₁(λ₂+λ₃)/2`
(Rule III) are continuous on `(0, 1]`; they coincide wherever `Δ(γ) = 0`
(`rules_coincide_at_bifurcation`). -/
theorem continuousOn_rule_coeffs (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (fun γ => (lam1 β γ κ σ : ℂ) + lam2 β γ κ σ) (Set.Ioc 0 1) ∧
    ContinuousOn (fun γ => (lam1 β γ κ σ : ℂ) * lam2 β γ κ σ) (Set.Ioc 0 1) ∧
    ContinuousOn (fun γ => (lam1 β γ κ σ : ℂ) + (lam2 β γ κ σ + lam3 β γ κ σ) / 2)
      (Set.Ioc 0 1) ∧
    ContinuousOn (fun γ => (lam1 β γ κ σ : ℂ) * ((lam2 β γ κ σ + lam3 β γ κ σ) / 2))
      (Set.Ioc 0 1) := by
  have h1 : ContinuousOn (fun γ => (lam1 β γ κ σ : ℂ)) (Set.Ioc 0 1) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_lam1 hσ hκ hβ hβ1)
  have h2 := continuousOn_lam2 hσ hκ hβ hβ1
  have h3 := continuousOn_lam3 hσ hκ hβ hβ1
  exact ⟨h1.add h2, h1.mul h2, h1.add ((h2.add h3).div_const 2),
    h1.mul ((h2.add h3).div_const 2)⟩

/-- Woodford (2003), pp. 596–597: the forward weights `(βγλ₃)⁻¹λ₃⁻ʲ` of Rule I are continuous
in `γ ∈ (0, 1]`. -/
theorem continuousOn_ruleI_weights (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1)
    (j : ℕ) : ContinuousOn (fun γ : ℝ => (((β * γ : ℝ) : ℂ) * lam3 β γ κ σ)⁻¹ *
      ((lam3 β γ κ σ)⁻¹) ^ j) (Set.Ioc 0 1) := by
  have h3 := continuousOn_lam3 hσ hκ hβ hβ1
  have hne : ∀ γ ∈ Set.Ioc (0 : ℝ) 1, lam3 β γ κ σ ≠ 0 := by
    intro γ hγ h0
    have := one_lt_norm_lam3 (⟨hσ, hκ, hβ, hβ1, hγ.1, hγ.2⟩ : Standing β γ κ σ)
    rw [h0, norm_zero] at this
    linarith
  have hb : ContinuousOn (fun γ : ℝ => ((β * γ : ℝ) : ℂ)) (Set.Ioc 0 1) :=
    Complex.continuous_ofReal.comp_continuousOn (by fun_prop)
  refine ContinuousOn.mul (ContinuousOn.inv₀ ?_ ?_) ((h3.inv₀ hne).pow j)
  · exact hb.mul h3
  · intro γ hγ
    refine mul_ne_zero ?_ (hne γ hγ)
    exact_mod_cast (mul_pos hβ hγ.1).ne'

/-! ### The inflation-inertia model (3.14)–(3.19) and the Euler equation (3.16) -/

/-- `E_t` of an affine combination of four random variables (Woodford (2003), App. G.7:
linearity of `E_t` and `E_t c = c`). -/
theorem E_lin4 (t : ℕ) (a b c d e : ℝ) (y1 y2 y3 y4 : Ω → ℝ) :
    𝔼.E t (fun ω => a * y1 ω + b * y2 ω + c * y3 ω + d * y4 ω + e) =
      fun ω => a * 𝔼.E t y1 ω + b * 𝔼.E t y2 ω + c * 𝔼.E t y3 ω + d * 𝔼.E t y4 ω + e := by
  change 𝔼.E t (a • y1 + b • y2 + c • y3 + d • y4 + fun _ => e) = _
  rw [map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, 𝔼.const]
  rfl

variable {lamx lami xstar istar : ℝ}

/-- Woodford (2003), eq. (2.6), p. 562, CORRECTED as in Chapter 3, eq. (3.6), p. 215:
`π_k − γπ_{k−1} = κx_k + βE_k[π_{k+1} − γπ_k] + u_k` (date `k ≥ 1`). -/
def AS (β γ κ : ℝ) (u π x : ℕ → Ω → ℝ) (k : ℕ) : Prop :=
  ∀ ω, π k ω - γ * π (k - 1) ω =
    κ * x k ω + β * 𝔼.E k (fun ω' => π (k + 1) ω' - γ * π k ω') ω + u k ω

/-- Woodford (2003), eq. (2.6) AS PRINTED, p. 562: `… + βE_k[π_{k+1} − π_k] + u_k`. -/
def ASprinted (β γ κ : ℝ) (u π x : ℕ → Ω → ℝ) (k : ℕ) : Prop :=
  ∀ ω, π k ω - γ * π (k - 1) ω =
    κ * x k ω + β * 𝔼.E k (fun ω' => π (k + 1) ω' - π k ω') ω + u k ω

/-- Woodford (2003), eq. (2.6), p. 562 (misprint): the printed relation is the indexation
Phillips curve with the cost-push term `u_k` replaced by `u_k − β(1 − γ)π_k`; it agrees with
Chapter 3's (3.6) (and with the FOC (3.15), whose coefficient `1 + βγ` requires `γπ_t`) only
when `γ = 1`. -/
theorem ASprinted_iff {β γ κ : ℝ} {u π x : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (k : ℕ) :
    ASprinted 𝔼 β γ κ u π x k ↔
      AS 𝔼 β γ κ (fun k ω => u k ω - β * (1 - γ) * π k ω) π x k := by
  unfold ASprinted AS
  refine forall_congr' fun ω => ?_
  have e1 := congrFun (E_fun_sub 𝔼 k (π (k + 1)) (π k)) ω
  have e2 := congrFun (E_fun_sub 𝔼 k (π (k + 1)) (fun ω' => γ * π k ω')) ω
  rw [E_fun_mul, hπ k] at e2
  simp only at e1 e2
  rw [e1, e2, hπ k]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), eq. (3.1), p. 583: the intertemporal IS relation
`x_k = E_k x_{k+1} − σ(i_k − E_kπ_{k+1} − rⁿ_k)`. -/
def IS (σ : ℝ) (rn π x i : ℕ → Ω → ℝ) (k : ℕ) : Prop :=
  ∀ ω, x k ω = 𝔼.E k (x (k + 1)) ω - σ * (i k ω - 𝔼.E k (π (k + 1)) ω - rn k ω)

/-- Woodford (2003), eq. (3.14), p. 592: the period loss
`L_k = (π_k − γπ_{k−1})² + λₓ(x_k − x*)² + λᵢ(i_k − i*)²`. -/
def periodLoss (γ lamx lami xstar istar : ℝ) (π x i : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (π k ω - γ * π (k - 1) ω) ^ 2 + lamx * (x k ω - xstar) ^ 2 + lami * (i k ω - istar) ^ 2

/-- Woodford (2003), eq. (3.15), p. 592, at date `k ≥ 1`:
`π^qd_k − βγE_kπ^qd_{k+1} − β⁻¹σΞ₁,k−1 − βγE_kΞ₂,k+1 + (1 + βγ)Ξ₂k − Ξ₂,k−1 = 0`. -/
def FOC315 (β γ σ : ℝ) (π Ξ1 Ξ2 : ℕ → Ω → ℝ) (k : ℕ) : Prop :=
  ∀ ω, π k ω - γ * π (k - 1) ω - β * γ * 𝔼.E k (fun ω' => π (k + 1) ω' - γ * π k ω') ω -
    β⁻¹ * σ * Ξ1 (k - 1) ω - β * γ * 𝔼.E k (Ξ2 (k + 1)) ω + (1 + β * γ) * Ξ2 k ω -
      Ξ2 (k - 1) ω = 0

/-- Woodford (2003), eq. (3.4), p. 584, at date `k ≥ 1`:
`λₓ(x_k − x*) + Ξ₁k − β⁻¹Ξ₁,k−1 − κΞ₂k = 0`. -/
def FOC34 (β κ lamx xstar : ℝ) (x Ξ1 Ξ2 : ℕ → Ω → ℝ) (k : ℕ) : Prop :=
  ∀ ω, lamx * (x k ω - xstar) + Ξ1 k ω - β⁻¹ * Ξ1 (k - 1) ω - κ * Ξ2 k ω = 0

/-- Woodford (2003), eq. (3.5), p. 584: `λᵢ(i_k − i*) + σΞ₁k = 0`. -/
def FOC35 (σ lami istar : ℝ) (i Ξ1 : ℕ → Ω → ℝ) (k : ℕ) : Prop :=
  ∀ ω, lami * (i k ω - istar) + σ * Ξ1 k ω = 0

/-- Woodford (2003), eq. (3.19), p. 593: `q̃_k = (κσ/λᵢ)[π^qd_k + (λₓ/κ)Δx_k]`. -/
noncomputable def qtil (γ κ σ lamx lami : ℝ) (π x : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  κ * σ / lami * ((π k ω - γ * π (k - 1) ω) + lamx / κ * (x k ω - x (k - 1) ω))

/-- Woodford (2003), eq. (3.18), p. 593: `f_k = q̃_k − βγE_k q̃_{k+1}`. -/
noncomputable def fbig (β γ κ σ lamx lami : ℝ) (π x : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  qtil γ κ σ lamx lami π x k ω - β * γ * 𝔼.E k (qtil γ κ σ lamx lami π x (k + 1)) ω

/-- Woodford (2003), p. 593 (after (3.19)): at `γ = 0`, `f_k = q̃_k = q_k = φπ π_k + (φₓ/4)Δx_k`
with the coefficients (3.9) `φπ = κσ/λᵢ`, `φₓ = 4σλₓ/λᵢ`. -/
theorem fbig_gamma_zero {β κ σ : ℝ} (hκ : κ ≠ 0) (π x : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    fbig 𝔼 β 0 κ σ lamx lami π x k ω =
      κ * σ / lami * π k ω + (4 * σ * lamx / lami) / 4 * (x k ω - x (k - 1) ω) := by
  unfold fbig qtil
  field_simp
  ring

/-- Woodford (2003), eqs. (3.15), (3.4), (3.5) ⇒ (3.16), pp. 592–593 (and conversely): given
(3.5) at dates `t, …, t+3` and (3.4) at dates `t+1, …, t+3`, the FOC (3.15) at date `t + 2`
holds iff the Euler equation `E_{t+2}[A(L)(i_{t+3} − i*)] = −f_{t+2}` (3.16) holds. -/
theorem foc315_iff_euler {β γ κ σ : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (hσ : σ ≠ 0) (hli : lami ≠ 0)
    {π x i Ξ1 Ξ2 : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hx : 𝔼.Adapted x) (hi : 𝔼.Adapted i)
    (hΞ1 : 𝔼.Adapted Ξ1) (t : ℕ)
    (h5 : ∀ k, t ≤ k → k ≤ t + 3 → FOC35 σ lami istar i Ξ1 k)
    (h4 : ∀ k, t + 1 ≤ k → k ≤ t + 3 → FOC34 β κ lamx xstar x Ξ1 Ξ2 k) :
    FOC315 𝔼 β γ σ π Ξ1 Ξ2 (t + 2) ↔
      Euler 𝔼 β γ κ σ (fun k ω => i k ω - istar) (fbig 𝔼 β γ κ σ lamx lami π x) t := by
  -- the multipliers in terms of the target variables
  have hX1 : ∀ k, t ≤ k → k ≤ t + 3 → Ξ1 k = fun ω => -(lami / σ) * (i k ω - istar) := by
    intro k hk1 hk2
    funext ω
    have := h5 k hk1 hk2 ω
    field_simp
    linarith
  have hX2 : ∀ k, t + 1 ≤ k → k ≤ t + 3 →
      Ξ2 k = fun ω => (lamx * (x k ω - xstar) + Ξ1 k ω - β⁻¹ * Ξ1 (k - 1) ω) / κ := by
    intro k hk1 hk2
    funext ω
    have := h4 k hk1 hk2 ω
    rw [eq_div_iff hκ]
    linarith
  have hk3 : t + 3 - 1 = t + 2 := by omega
  have hk2 : t + 2 - 1 = t + 1 := by omega
  have hk1 : t + 1 - 1 = t := by omega
  -- expectations at `t + 2`
  have hEΞ2 : ∀ ω, 𝔼.E (t + 2) (Ξ2 (t + 3)) ω = lamx / κ * 𝔼.E (t + 2) (x (t + 3)) ω +
      (-(lami / σ) / κ) * 𝔼.E (t + 2) (i (t + 3)) ω + (-(β⁻¹) / κ) * Ξ1 (t + 2) ω +
      0 * Ξ1 (t + 2) ω + (-(lamx * xstar) / κ + lami / σ * istar / κ) := by
    intro ω
    have e : Ξ2 (t + 3) = fun ω => lamx / κ * x (t + 3) ω + (-(lami / σ) / κ) * i (t + 3) ω +
        (-(β⁻¹) / κ) * Ξ1 (t + 2) ω + 0 * Ξ1 (t + 2) ω +
          (-(lamx * xstar) / κ + lami / σ * istar / κ) := by
      rw [hX2 (t + 3) (by omega) le_rfl, hk3, hX1 (t + 3) (by omega) le_rfl]
      funext ω
      field_simp
      ring
    rw [e, E_lin4, hΞ1 (t + 2)]
  have hEπ : ∀ ω, 𝔼.E (t + 2) (fun ω' => π (t + 2 + 1) ω' - γ * π (t + 2) ω') ω =
      𝔼.E (t + 2) (π (t + 3)) ω - γ * π (t + 2) ω := by
    intro ω
    have e : (fun ω' => π (t + 2 + 1) ω' - γ * π (t + 2) ω') = fun ω' => 1 * π (t + 3) ω' +
        (-γ) * π (t + 2) ω' + 0 * π (t + 2) ω' + 0 * π (t + 2) ω' + 0 := by
      funext ω'
      ring
    rw [e, E_lin4, hπ (t + 2)]
    ring
  have hEq : ∀ ω, 𝔼.E (t + 2) (qtil γ κ σ lamx lami π x (t + 2 + 1)) ω =
      κ * σ / lami * ((𝔼.E (t + 2) (π (t + 3)) ω - γ * π (t + 2) ω) +
        lamx / κ * (𝔼.E (t + 2) (x (t + 3)) ω - x (t + 2) ω)) := by
    intro ω
    have e : qtil γ κ σ lamx lami π x (t + 2 + 1) = fun ω' =>
        κ * σ / lami * π (t + 3) ω' + (-(κ * σ / lami * γ)) * π (t + 2) ω' +
          κ * σ / lami * (lamx / κ) * x (t + 3) ω' +
            (-(κ * σ / lami * (lamx / κ))) * x (t + 2) ω' + 0 := by
      funext ω'
      unfold qtil
      rw [show t + 2 + 1 - 1 = t + 2 by omega, show t + 2 + 1 = t + 3 by ring]
      ring
    rw [e, E_lin4, hπ (t + 2), hx (t + 2)]
    ring
  have hEA : ∀ ω, 𝔼.E (t + 2) (ALi β γ κ σ (fun k ω => i k ω - istar) t) ω =
      β * γ * (𝔼.E (t + 2) (i (t + 3)) ω - istar) - (1 + γ + β * γ) * (i (t + 2) ω - istar) +
        coefA2 β γ κ σ * (i (t + 1) ω - istar) - β⁻¹ * (i t ω - istar) := by
    intro ω
    have e : ALi β γ κ σ (fun k ω => i k ω - istar) t = fun ω' =>
        β * γ * i (t + 3) ω' + (-(1 + γ + β * γ)) * i (t + 2) ω' +
          coefA2 β γ κ σ * i (t + 1) ω' + (-β⁻¹) * i t ω' +
            (-(β * γ) * istar + (1 + γ + β * γ) * istar - coefA2 β γ κ σ * istar +
              β⁻¹ * istar) := by
      funext ω'
      unfold ALi
      ring
    rw [e, E_lin4, hi (t + 2), ForwardSolution.E_of_known 𝔼 (by omega) (hi (t + 1)),
      ForwardSolution.E_of_known 𝔼 (by omega) (hi t)]
    ring
  unfold FOC315 Euler fbig
  rw [hk2]
  refine forall_congr' fun ω => ?_
  rw [hEπ ω, hEΞ2 ω, hEq ω, hEA ω, hX2 (t + 2) (by omega) (by omega), hk2,
    hX2 (t + 1) le_rfl (by omega), hk1, hX1 (t + 2) (by omega) (by omega),
    hX1 (t + 1) (by omega) (by omega), hX1 t le_rfl (by omega)]
  unfold qtil coefA2
  rw [hk2]
  simp only
  constructor
  · intro h
    field_simp at h ⊢
    linear_combination h
  · intro h
    field_simp at h ⊢
    linear_combination h

/-- Woodford (2003), eqs. (3.16) and (3.21), p. 594: in deviations from long-run values
`ī, f̄` with `A(1)(ī − i*) = −f̄` (here `A(1) = β⁻¹κσ`), (3.16) holds iff (3.21) does. -/
theorem euler_hat_iff {β γ κ σ : ℝ} {i f : ℕ → Ω → ℝ} {ibar fbar : ℝ}
    (hss : β⁻¹ * (κ * σ) * (ibar - istar) = -fbar) (t : ℕ) :
    Euler 𝔼 β γ κ σ (fun k ω => i k ω - istar) f t ↔
      Euler 𝔼 β γ κ σ (fun k ω => i k ω - ibar) (fun k ω => f k ω - fbar) t := by
  have e : ALi β γ κ σ (fun k ω => i k ω - istar) t = fun ω =>
      1 * ALi β γ κ σ (fun k ω => i k ω - ibar) t ω + 0 * f 0 ω + 0 * f 0 ω + 0 * f 0 ω +
        β⁻¹ * (κ * σ) * (ibar - istar) := by
    funext ω
    unfold ALi coefA2
    ring
  unfold Euler
  rw [e, E_lin4]
  refine forall_congr' fun ω => ?_
  rw [hss]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 593: "in the limiting case `γ = 0`, (3.16) ceases to involve any
dependence upon `E_t i_{t+1}` and … coincide[s] with the optimal instrument rule (3.7)": for
adapted `ı̂`, (3.21) at `γ = 0` is `ı̂_n − (ρ₁ + ρ₂)ı̂_{n−1} + ρ₂ ı̂_{n−2} = f̂_n` with
`ρ₁ = 1 + κσ/β`, `ρ₂ = β⁻¹` (3.8), i.e. (3.10). -/
theorem euler_gamma_zero {β κ σ : ℝ} {ı f : ℕ → Ω → ℝ} (hı : 𝔼.Adapted ı) (t : ℕ) :
    Euler 𝔼 β 0 κ σ ı f t ↔
      ∀ ω, ı (t + 2) ω - (1 + κ * σ / β + β⁻¹) * ı (t + 1) ω + β⁻¹ * ı t ω = f (t + 2) ω := by
  have e : ALi β 0 κ σ ı t = fun ω => 0 * ı (t + 3) ω + (-1) * ı (t + 2) ω +
      (1 + κ * σ / β + β⁻¹) * ı (t + 1) ω + (-β⁻¹) * ı t ω + 0 := by
    funext ω
    unfold ALi coefA2
    ring
  unfold Euler
  rw [e, E_lin4, hı (t + 2), ForwardSolution.E_of_known 𝔼 (by omega) (hı (t + 1)),
    ForwardSolution.E_of_known 𝔼 (by omega) (hı t)]
  refine forall_congr' fun ω => ?_
  constructor <;> intro h <;> linarith

/-! ### Lagrangian sufficiency: the FOCs (3.15), (3.4), (3.5) characterize the optimum -/

/-- `E_k` fixes a linear combination of two variables known at `k` (Woodford (2003), App. G). -/
theorem E_known_lin2 {k : ℕ} {y1 y2 : Ω → ℝ} (h1 : 𝔼.E k y1 = y1) (h2 : 𝔼.E k y2 = y2)
    (a b : ℝ) : 𝔼.E k (fun ω => a * y1 ω + b * y2 ω) = fun ω => a * y1 ω + b * y2 ω := by
  change 𝔼.E k (a • y1 + b • y2) = a • y1 + b • y2
  rw [map_add, map_smul, map_smul, h1, h2]

/-- Woodford (2003), §3.2, p. 592 (with (3.14)): the first-order term of the loss difference
between a plan `(π, x, i)` and the candidate `(π*, x*, i*)`,
`π*^qd_k dπ^qd_k + λₓ(x*_k − x*)dx_k + λᵢ(i*_k − i*)di_k`. -/
noncomputable def foTerm (γ lamx lami xstar istar : ℝ) (π x i πs xs is : ℕ → Ω → ℝ) (k : ℕ)
    (ω : Ω) : ℝ :=
  (πs k ω - γ * πs (k - 1) ω) * ((π k ω - πs k ω) - γ * (π (k - 1) ω - πs (k - 1) ω)) +
    lamx * (xs k ω - xstar) * (x k ω - xs k ω) + lami * (is k ω - istar) * (i k ω - is k ω)

/-- Woodford (2003), §3.2 (Lagrangian method): the telescoping term
`W_k = β⁻¹[(σΞ₁,k−1 + βΞ₂,k−1)dπ_k + Ξ₁,k−1 dx_k] − γπ*^qd_k dπ_{k−1} − γΞ₂k dπ_{k−1}`. -/
noncomputable def wTerm (β γ σ : ℝ) (π x πs xs Ξ1 Ξ2 : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  β⁻¹ * ((σ * Ξ1 (k - 1) ω + β * Ξ2 (k - 1) ω) * (π k ω - πs k ω) +
      Ξ1 (k - 1) ω * (x k ω - xs k ω)) -
    γ * (πs k ω - γ * πs (k - 1) ω) * (π (k - 1) ω - πs (k - 1) ω) -
      γ * Ξ2 k ω * (π (k - 1) ω - πs (k - 1) ω)

/-- Woodford (2003), §3.2, p. 592 (the Lagrangian sufficiency identity, period by period): if
both plans satisfy (2.6) and (3.1) at date `k` and the candidate satisfies (3.15), (3.4),
(3.5) at `k`, then the first-order term telescopes: `FO_k = W_k − β E_k W_{k+1}` (uses the
pull-out property). -/
theorem foTerm_eq {β γ κ σ : ℝ} (hpull : 𝔼.PullOut) (hβ : β ≠ 0)
    {u rn π x i πs xs is Ξ1 Ξ2 : ℕ → Ω → ℝ} {k : ℕ}
    (hπ : 𝔼.E k (π k) = π k) (hπs : 𝔼.E k (πs k) = πs k) (hΞ1 : 𝔼.E k (Ξ1 k) = Ξ1 k)
    (hΞ2 : 𝔼.E k (Ξ2 k) = Ξ2 k) (hAS : AS 𝔼 β γ κ u π x k) (hASs : AS 𝔼 β γ κ u πs xs k)
    (hIS : IS 𝔼 σ rn π x i k) (hISs : IS 𝔼 σ rn πs xs is k)
    (hF15 : FOC315 𝔼 β γ σ πs Ξ1 Ξ2 k) (hF4 : FOC34 β κ lamx xstar xs Ξ1 Ξ2 k)
    (hF5 : FOC35 σ lami istar is Ξ1 k) (ω : Ω) :
    foTerm γ lamx lami xstar istar π x i πs xs is k ω =
      wTerm β γ σ π x πs xs Ξ1 Ξ2 k ω - β * 𝔼.E k (wTerm β γ σ π x πs xs Ξ1 Ξ2 (k + 1)) ω := by
  have hk1 : k + 1 - 1 = k := by omega
  -- the coefficients known at `k`
  have ha1 := E_known_lin2 𝔼 hΞ1 hΞ2 (β⁻¹ * σ) (β⁻¹ * β)
  have ha2 := E_known_lin2 𝔼 hΞ1 hΞ1 β⁻¹ 0
  have ha3 := E_known_lin2 𝔼 hπ hπs (-γ) γ
  have e : wTerm β γ σ π x πs xs Ξ1 Ξ2 (k + 1) =
      (fun ω => β⁻¹ * σ * Ξ1 k ω + β⁻¹ * β * Ξ2 k ω) * (fun ω => π (k + 1) ω - πs (k + 1) ω) +
      (fun ω => β⁻¹ * Ξ1 k ω + 0 * Ξ1 k ω) * (fun ω => x (k + 1) ω - xs (k + 1) ω) +
      (fun ω => -γ * π k ω + γ * πs k ω) * (fun ω => πs (k + 1) ω - γ * πs k ω) +
      (fun ω => -γ * π k ω + γ * πs k ω) * Ξ2 (k + 1) := by
    funext ω
    simp only [wTerm, hk1, Pi.add_apply, Pi.mul_apply]
    ring
  have hEW : 𝔼.E k (wTerm β γ σ π x πs xs Ξ1 Ξ2 (k + 1)) ω =
      (β⁻¹ * σ * Ξ1 k ω + β⁻¹ * β * Ξ2 k ω) * (𝔼.E k (π (k + 1)) ω - 𝔼.E k (πs (k + 1)) ω) +
      (β⁻¹ * Ξ1 k ω + 0 * Ξ1 k ω) * (𝔼.E k (x (k + 1)) ω - 𝔼.E k (xs (k + 1)) ω) +
      (-γ * π k ω + γ * πs k ω) * (𝔼.E k (πs (k + 1)) ω - γ * πs k ω) +
      (-γ * π k ω + γ * πs k ω) * 𝔼.E k (Ξ2 (k + 1)) ω := by
    rw [e, map_add, map_add, map_add, hpull k _ _ ha1, hpull k _ _ ha2, hpull k _ _ ha3,
      hpull k _ _ ha3, E_fun_sub, E_fun_sub, E_fun_sub, E_fun_mul, hπs]
    rfl
  have hEπ : ∀ (p : ℕ → Ω → ℝ), 𝔼.E k (p k) = p k →
      𝔼.E k (fun ω' => p (k + 1) ω' - γ * p k ω') ω = 𝔼.E k (p (k + 1)) ω - γ * p k ω := by
    intro p hp
    rw [E_fun_sub, E_fun_mul, hp]
  have h1 := hAS ω
  have h2 := hASs ω
  have h3 := hIS ω
  have h4 := hISs ω
  have h5 := hF15 ω
  have h6 := hF4 ω
  have h7 := hF5 ω
  rw [hEπ π hπ] at h1
  rw [hEπ πs hπs] at h2 h5
  rw [hEW]
  unfold foTerm wTerm
  have hb : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ
  linear_combination (π k ω - πs k ω) * h5 + (x k ω - xs k ω) * h6 +
    (i k ω - is k ω) * h7 - Ξ2 k ω * (h1 - h2) - Ξ1 k ω * (h3 - h4) +
    ((πs k ω - π k ω) * Ξ2 (k - 1) ω - Ξ2 k ω * β * (𝔼.E k (πs (k + 1)) ω -
      𝔼.E k (π (k + 1)) ω) - σ * Ξ1 k ω * 𝔼.E k (πs (k + 1)) ω -
      Ξ1 k ω * 𝔼.E k (xs (k + 1)) ω + σ * Ξ1 k ω * 𝔼.E k (π (k + 1)) ω +
      Ξ1 k ω * 𝔼.E k (x (k + 1)) ω) * hb

/-- A process bounded by a nonnegative constant (Woodford (2003), Ch. 8: "bounded" plans). -/
def Bnd (g : ℕ → Ω → ℝ) : Prop := ∃ C, 0 ≤ C ∧ ∀ k ω, |g k ω| ≤ C

/-- Woodford (2003), Ch. 8 (bounded plans): constants are bounded. -/
theorem Bnd.const (c : ℝ) : Bnd (fun (_ : ℕ) (_ : Ω) => c) :=
  ⟨|c|, abs_nonneg c, fun _ _ => le_rfl⟩

/-- Woodford (2003), Ch. 8 (bounded plans): sums of bounded processes are bounded. -/
theorem Bnd.add {g h : ℕ → Ω → ℝ} (hg : Bnd g) (hh : Bnd h) :
    Bnd (fun k ω => g k ω + h k ω) := by
  obtain ⟨C, hC, hgC⟩ := hg
  obtain ⟨D, hD, hhD⟩ := hh
  exact ⟨C + D, by positivity, fun k ω => (abs_add_le _ _).trans (add_le_add (hgC k ω) (hhD k ω))⟩

/-- Woodford (2003), Ch. 8 (bounded plans): differences of bounded processes are bounded. -/
theorem Bnd.sub {g h : ℕ → Ω → ℝ} (hg : Bnd g) (hh : Bnd h) :
    Bnd (fun k ω => g k ω - h k ω) := by
  obtain ⟨C, hC, hgC⟩ := hg
  obtain ⟨D, hD, hhD⟩ := hh
  exact ⟨C + D, by positivity, fun k ω => (abs_sub _ _).trans (add_le_add (hgC k ω) (hhD k ω))⟩

/-- Woodford (2003), Ch. 8 (bounded plans): products of bounded processes are bounded. -/
theorem Bnd.mul {g h : ℕ → Ω → ℝ} (hg : Bnd g) (hh : Bnd h) :
    Bnd (fun k ω => g k ω * h k ω) := by
  obtain ⟨C, hC, hgC⟩ := hg
  obtain ⟨D, hD, hhD⟩ := hh
  refine ⟨C * D, by positivity, fun k ω => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hgC k ω) (hhD k ω) (abs_nonneg _) hC

/-- Woodford (2003), Ch. 8 (bounded plans): squares of bounded processes are bounded. -/
theorem Bnd.sq {g : ℕ → Ω → ℝ} (hg : Bnd g) : Bnd (fun k ω => g k ω ^ 2) := by
  have := hg.mul hg
  simpa [pow_two] using this

/-- Woodford (2003), Ch. 8 (bounded plans): a reindexed bounded process is bounded. -/
theorem Bnd.comp {g : ℕ → Ω → ℝ} (hg : Bnd g) (f : ℕ → ℕ) : Bnd (fun k ω => g (f k) ω) := by
  obtain ⟨C, hC, hgC⟩ := hg
  exact ⟨C, hC, fun k ω => hgC (f k) ω⟩

/-- Woodford (2003), Ch. 8 (bounded plans): conditional expectations of a bounded process are
bounded. -/
theorem Bnd.E {g : ℕ → Ω → ℝ} (hg : Bnd g) (f : ℕ → ℕ) :
    Bnd (fun k ω => 𝔼.E (f k) (g k) ω) := by
  obtain ⟨C, hC, hgC⟩ := hg
  exact ⟨C, hC, fun k ω => 𝔼.abs_E_le (hgC k) _ ω⟩

/-- The expected discounted loss `E₁ ∑ₙ βⁿ L_{1+n}`, written as `∑ₙ βⁿ E₁ L_{1+n}`
(Woodford (2003), eq. (2.2), p. 560, from the initial date `t₀ = 1`). -/
noncomputable def Jobj (β : ℝ) (L : ℕ → Ω → ℝ) (ω : Ω) : ℝ := ∑' n, β ^ n * 𝔼.E 1 (L (n + 1)) ω

/-- Woodford (2003), eq. (2.2): the objective converges for bounded losses and `0 ≤ β < 1`. -/
theorem summable_Jobj {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {L : ℕ → Ω → ℝ} (hL : Bnd L)
    (ω : Ω) : Summable (fun n => β ^ n * 𝔼.E 1 (L (n + 1)) ω) := by
  obtain ⟨C, _, hC⟩ := hL
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right C)
    (fun n => ?_)
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hC (n + 1)) 1 ω) (by positivity)

/-- Woodford (2003), §3.2 (Lagrangian sufficiency): the discounted telescoping sum
`∑ₙ βⁿ (w_{n+1} − β w_{n+2}) = w₁` for bounded `w`. -/
theorem tsum_telescope {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {w : ℕ → ℝ} {C : ℝ}
    (hw : ∀ n, |w n| ≤ C) : ∑' n, β ^ n * (w (n + 1) - β * w (n + 2)) = w 1 := by
  have hg := (summable_geometric_of_lt_one hβ0 hβ1).mul_right C
  have s1 : Summable (fun n => β ^ n * w (n + 1)) := Summable.of_norm_bounded hg (fun n => by
    rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hw _) (by positivity))
  have s2 : Summable (fun n => β ^ (n + 1) * w (n + 1 + 1)) :=
    (summable_nat_add_iff 1).mpr s1
  have e : (fun n => β ^ n * (w (n + 1) - β * w (n + 2))) =
      fun n => β ^ n * w (n + 1) - β ^ (n + 1) * w (n + 1 + 1) := by
    funext n
    ring
  rw [e, s1.tsum_sub s2, s1.tsum_eq_zero_add]
  simp

/-- Woodford (2003), eq. (3.14): the second-order term `(dπ^qd)² + λₓ dx² + λᵢ di²` of the loss
difference. -/
noncomputable def soTerm (γ lamx lami : ℝ) (π x i πs xs is : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ((π k ω - πs k ω) - γ * (π (k - 1) ω - πs (k - 1) ω)) ^ 2 + lamx * (x k ω - xs k ω) ^ 2 +
    lami * (i k ω - is k ω) ^ 2

/-- Woodford (2003), eq. (3.14): `L_k(plan) = L_k(π*, x*, i*) + 2 FO_k + SO_k` (the loss is
quadratic, so its second-order expansion is exact). -/
theorem periodLoss_expand (γ lamx lami xstar istar : ℝ) (π x i πs xs is : ℕ → Ω → ℝ) (k : ℕ)
    (ω : Ω) : periodLoss γ lamx lami xstar istar π x i k ω =
      periodLoss γ lamx lami xstar istar πs xs is k ω +
        2 * foTerm γ lamx lami xstar istar π x i πs xs is k ω +
          soTerm γ lamx lami π x i πs xs is k ω := by
  unfold periodLoss foTerm soTerm
  ring

/-- Woodford (2003), §3.2, p. 592 (**Lagrangian sufficiency, exact form**): if `(π*, x*, i*)` is
feasible ((2.6), (3.1) at all dates `≥ 1`) and satisfies the FOCs (3.15), (3.4), (3.5) at all
dates `≥ 1` with bounded multipliers, then for every bounded feasible adapted plan with the same
`π₀`, `J(plan) = J(π*, x*, i*) + E₁∑βⁿ SO_{1+n} + 2E₁W₁`, where `W₁` only involves the initial
multipliers `Ξ₀` and `dπ₁, dx₁`. -/
theorem loss_gap {β γ κ σ : ℝ} (hpull : 𝔼.PullOut) (hβ0 : 0 < β) (hβ1 : β < 1)
    {u rn π x i πs xs is Ξ1 Ξ2 : ℕ → Ω → ℝ}
    (hπ : ∀ k, 1 ≤ k → 𝔼.E k (π k) = π k) (hπs : ∀ k, 1 ≤ k → 𝔼.E k (πs k) = πs k)
    (hΞ1 : ∀ k, 1 ≤ k → 𝔼.E k (Ξ1 k) = Ξ1 k) (hΞ2 : ∀ k, 1 ≤ k → 𝔼.E k (Ξ2 k) = Ξ2 k)
    (bπ : Bnd π) (bx : Bnd x) (bi : Bnd i) (bπs : Bnd πs) (bxs : Bnd xs) (bis : Bnd is)
    (bΞ1 : Bnd Ξ1) (bΞ2 : Bnd Ξ2)
    (hAS : ∀ k, 1 ≤ k → AS 𝔼 β γ κ u π x k) (hASs : ∀ k, 1 ≤ k → AS 𝔼 β γ κ u πs xs k)
    (hIS : ∀ k, 1 ≤ k → IS 𝔼 σ rn π x i k) (hISs : ∀ k, 1 ≤ k → IS 𝔼 σ rn πs xs is k)
    (hF15 : ∀ k, 1 ≤ k → FOC315 𝔼 β γ σ πs Ξ1 Ξ2 k)
    (hF4 : ∀ k, 1 ≤ k → FOC34 β κ lamx xstar xs Ξ1 Ξ2 k)
    (hF5 : ∀ k, 1 ≤ k → FOC35 σ lami istar is Ξ1 k) (ω : Ω) :
    Jobj 𝔼 β (periodLoss γ lamx lami xstar istar π x i) ω =
      Jobj 𝔼 β (periodLoss γ lamx lami xstar istar πs xs is) ω +
        Jobj 𝔼 β (soTerm γ lamx lami π x i πs xs is) ω +
          2 * 𝔼.E 1 (wTerm β γ σ π x πs xs Ξ1 Ξ2 1) ω := by
  -- boundedness
  have bLs : Bnd (periodLoss γ lamx lami xstar istar πs xs is) :=
    ((bπs.sub ((Bnd.const γ).mul (bπs.comp (· - 1)))).sq.add
      ((Bnd.const lamx).mul (bxs.sub (Bnd.const xstar)).sq)).add
      ((Bnd.const lami).mul (bis.sub (Bnd.const istar)).sq)
  have bSO : Bnd (soTerm γ lamx lami π x i πs xs is) :=
    (((bπ.sub bπs).sub ((Bnd.const γ).mul ((bπ.comp (· - 1)).sub (bπs.comp (· - 1))))).sq.add
      ((Bnd.const lamx).mul (bx.sub bxs).sq)).add ((Bnd.const lami).mul (bi.sub bis).sq)
  have bW : Bnd (wTerm β γ σ π x πs xs Ξ1 Ξ2) :=
    (((Bnd.const β⁻¹).mul (((((Bnd.const σ).mul (bΞ1.comp (· - 1))).add
      ((Bnd.const β).mul (bΞ2.comp (· - 1)))).mul (bπ.sub bπs)).add
        ((bΞ1.comp (· - 1)).mul (bx.sub bxs)))).sub
      (((Bnd.const γ).mul (bπs.sub ((Bnd.const γ).mul (bπs.comp (· - 1))))).mul
        ((bπ.comp (· - 1)).sub (bπs.comp (· - 1))))).sub
      (((Bnd.const γ).mul bΞ2).mul ((bπ.comp (· - 1)).sub (bπs.comp (· - 1))))
  obtain ⟨CW, _, hCW⟩ := bW
  -- per-period decomposition of the expected loss
  have hper : ∀ n, β ^ n * 𝔼.E 1 (periodLoss γ lamx lami xstar istar π x i (n + 1)) ω =
      β ^ n * 𝔼.E 1 (periodLoss γ lamx lami xstar istar πs xs is (n + 1)) ω +
        β ^ n * 𝔼.E 1 (soTerm γ lamx lami π x i πs xs is (n + 1)) ω +
          2 * (β ^ n * (𝔼.E 1 (wTerm β γ σ π x πs xs Ξ1 Ξ2 (n + 1)) ω -
            β * 𝔼.E 1 (wTerm β γ σ π x πs xs Ξ1 Ξ2 (n + 2)) ω)) := by
    intro n
    have hk : 1 ≤ n + 1 := by omega
    have hFO : foTerm γ lamx lami xstar istar π x i πs xs is (n + 1) = fun ω' =>
        1 * wTerm β γ σ π x πs xs Ξ1 Ξ2 (n + 1) ω' +
          (-β) * 𝔼.E (n + 1) (wTerm β γ σ π x πs xs Ξ1 Ξ2 (n + 2)) ω' +
            0 * π 0 ω' + 0 * π 0 ω' + 0 := by
      funext ω'
      have := foTerm_eq 𝔼 hpull hβ0.ne' (hπ _ hk) (hπs _ hk) (hΞ1 _ hk) (hΞ2 _ hk) (hAS _ hk)
        (hASs _ hk) (hIS _ hk) (hISs _ hk) (hF15 _ hk) (hF4 _ hk) (hF5 _ hk) ω'
      rw [this]
      ring
    have hL : periodLoss γ lamx lami xstar istar π x i (n + 1) = fun ω' =>
        1 * periodLoss γ lamx lami xstar istar πs xs is (n + 1) ω' +
          2 * foTerm γ lamx lami xstar istar π x i πs xs is (n + 1) ω' +
            1 * soTerm γ lamx lami π x i πs xs is (n + 1) ω' + 0 * π 0 ω' + 0 := by
      funext ω'
      rw [periodLoss_expand]
      ring
    have e1 := congrFun (E_lin4 𝔼 1 1 2 1 0 0 (periodLoss γ lamx lami xstar istar πs xs is (n + 1))
      (foTerm γ lamx lami xstar istar π x i πs xs is (n + 1))
      (soTerm γ lamx lami π x i πs xs is (n + 1)) (π 0)) ω
    have e2 := congrFun (E_lin4 𝔼 1 1 (-β) 0 0 0 (wTerm β γ σ π x πs xs Ξ1 Ξ2 (n + 1))
      (𝔼.E (n + 1) (wTerm β γ σ π x πs xs Ξ1 Ξ2 (n + 2))) (π 0) (π 0)) ω
    rw [𝔼.tower hk, ← hFO] at e2
    rw [← hL] at e1
    rw [e1, e2]
    ring
  unfold Jobj
  rw [tsum_congr hper]
  have sL := summable_Jobj 𝔼 hβ0.le hβ1 bLs ω
  have sS := summable_Jobj 𝔼 hβ0.le hβ1 bSO ω
  have sT : Summable (fun n => 2 * (β ^ n * (𝔼.E 1 (wTerm β γ σ π x πs xs Ξ1 Ξ2 (n + 1)) ω -
      β * 𝔼.E 1 (wTerm β γ σ π x πs xs Ξ1 Ξ2 (n + 2)) ω))) := by
    have hb : ∀ n, ‖β ^ n * (𝔼.E 1 (wTerm β γ σ π x πs xs Ξ1 Ξ2 (n + 1)) ω -
        β * 𝔼.E 1 (wTerm β γ σ π x πs xs Ξ1 Ξ2 (n + 2)) ω)‖ ≤ β ^ n * (CW + β * CW) := by
      intro n
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hβ0.le]
      refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add
        (𝔼.abs_E_le (hCW _) 1 ω) ?_)) (by positivity)
      rw [abs_mul, abs_of_pos hβ0]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hCW _) 1 ω) hβ0.le
    have s0 : Summable (fun n => β ^ n * (𝔼.E 1 (wTerm β γ σ π x πs xs Ξ1 Ξ2 (n + 1)) ω -
        β * 𝔼.E 1 (wTerm β γ σ π x πs xs Ξ1 Ξ2 (n + 2)) ω)) :=
      Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right
        (CW + β * CW)) hb
    exact s0.mul_left 2
  rw [(sL.add sS).tsum_add sT, sL.tsum_add sS, tsum_mul_left,
    tsum_telescope hβ0.le hβ1 (w := fun k => 𝔼.E 1 (wTerm β γ σ π x πs xs Ξ1 Ξ2 k) ω)
      (C := CW) (fun k => 𝔼.abs_E_le (hCW k) 1 ω)]

/-- Woodford (2003), §3.2: with a common initial `π₀`, the boundary term is
`W₁ = β⁻¹[(σΞ₁₀ + βΞ₂₀)dπ₁ + Ξ₁₀ dx₁]`. -/
theorem wTerm_one {β γ σ : ℝ} {π x πs xs Ξ1 Ξ2 : ℕ → Ω → ℝ} (h0 : ∀ ω, π 0 ω = πs 0 ω)
    (ω : Ω) : wTerm β γ σ π x πs xs Ξ1 Ξ2 1 ω =
      β⁻¹ * ((σ * Ξ1 0 ω + β * Ξ2 0 ω) * (π 1 ω - πs 1 ω) + Ξ1 0 ω * (x 1 ω - xs 1 ω)) := by
  unfold wTerm
  simp only [Nat.sub_self, h0 ω, sub_self, mul_zero, sub_zero]

/-- Woodford (2003), eq. (3.14) with `λₓ, λᵢ ≥ 0`: the second-order part of the objective is
nonnegative. -/
theorem Jobj_soTerm_nonneg {β γ lamx lami : ℝ} (hβ0 : 0 ≤ β) (hlx : 0 ≤ lamx) (hli : 0 ≤ lami)
    (π x i πs xs is : ℕ → Ω → ℝ) (ω : Ω) :
    0 ≤ Jobj 𝔼 β (soTerm γ lamx lami π x i πs xs is) ω := by
  unfold Jobj
  refine tsum_nonneg fun n => mul_nonneg (pow_nonneg hβ0 n) ?_
  have hle : (fun _ => (0 : ℝ)) ≤ soTerm γ lamx lami π x i πs xs is (n + 1) := by
    intro ω'
    unfold soTerm
    positivity
  have := 𝔼.mono 1 hle ω
  rw [𝔼.const] at this
  exact this

/-- Woodford (2003), §3.2: a feasible plan — `π` adapted, `(π, x, i)` bounded, (2.6) and (3.1) at
every date `k ≥ 1`. -/
def Feasible (β γ κ σ : ℝ) (u rn π x i : ℕ → Ω → ℝ) : Prop :=
  (∀ k, 1 ≤ k → 𝔼.E k (π k) = π k) ∧ Bnd π ∧ Bnd x ∧ Bnd i ∧
    (∀ k, 1 ≤ k → AS 𝔼 β γ κ u π x k) ∧ (∀ k, 1 ≤ k → IS 𝔼 σ rn π x i k)

/-- Woodford (2003), §3.2, p. 592 ("the optimal once-and-for-all commitment to apply from date
`t = 0` onward"): `(π*, x*, i*)` is feasible and minimizes `E₁∑βⁿL_{1+n}` among all feasible plans
with the same initial `π₀`. -/
def OptimalCommitment (β γ κ σ lamx lami xstar istar : ℝ) (u rn πs xs is : ℕ → Ω → ℝ) :
    Prop :=
  Feasible 𝔼 β γ κ σ u rn πs xs is ∧ ∀ π x i, Feasible 𝔼 β γ κ σ u rn π x i →
    (∀ ω, π 0 ω = πs 0 ω) → ∀ ω, Jobj 𝔼 β (periodLoss γ lamx lami xstar istar πs xs is) ω ≤
      Jobj 𝔼 β (periodLoss γ lamx lami xstar istar π x i) ω

/-- Woodford (2003), §3.2 with (3.6), p. 584, and §1.1 of Ch. 8 (**optimal from a timeless
perspective**): `(π*, x*, i*)` is feasible and minimizes `E₁∑βⁿL_{1+n}` among all feasible plans
with the same `π₀` that also satisfy the initial constraints (3.6) `π₁ = π*₁`, `x₁ = x*₁`. -/
def TimelesslyOptimal (β γ κ σ lamx lami xstar istar : ℝ) (u rn πs xs is : ℕ → Ω → ℝ) :
    Prop :=
  Feasible 𝔼 β γ κ σ u rn πs xs is ∧ ∀ π x i, Feasible 𝔼 β γ κ σ u rn π x i →
    (∀ ω, π 0 ω = πs 0 ω) → (∀ ω, π 1 ω = πs 1 ω) → (∀ ω, x 1 ω = xs 1 ω) →
      ∀ ω, Jobj 𝔼 β (periodLoss γ lamx lami xstar istar πs xs is) ω ≤
        Jobj 𝔼 β (periodLoss γ lamx lami xstar istar π x i) ω

/-- Woodford (2003), §3.2, p. 592: (Lagrangian sufficiency) a feasible plan satisfying (3.15),
(3.4), (3.5) at all dates `≥ 1` with bounded adapted multipliers and NO prior commitments
(`Ξ₁₀ = Ξ₂₀ = 0`) is the optimal once-and-for-all commitment (`λₓ, λᵢ ≥ 0`, `0 < β < 1`, pull-out
property). -/
theorem optimalCommitment_of_foc {β γ κ σ : ℝ} (hpull : 𝔼.PullOut) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlx : 0 ≤ lamx) (hli : 0 ≤ lami) {u rn πs xs is Ξ1 Ξ2 : ℕ → Ω → ℝ}
    (hs : Feasible 𝔼 β γ κ σ u rn πs xs is)
    (hΞ1 : ∀ k, 1 ≤ k → 𝔼.E k (Ξ1 k) = Ξ1 k) (hΞ2 : ∀ k, 1 ≤ k → 𝔼.E k (Ξ2 k) = Ξ2 k)
    (bΞ1 : Bnd Ξ1) (bΞ2 : Bnd Ξ2) (h10 : ∀ ω, Ξ1 0 ω = 0) (h20 : ∀ ω, Ξ2 0 ω = 0)
    (hF15 : ∀ k, 1 ≤ k → FOC315 𝔼 β γ σ πs Ξ1 Ξ2 k)
    (hF4 : ∀ k, 1 ≤ k → FOC34 β κ lamx xstar xs Ξ1 Ξ2 k)
    (hF5 : ∀ k, 1 ≤ k → FOC35 σ lami istar is Ξ1 k) :
    OptimalCommitment 𝔼 β γ κ σ lamx lami xstar istar u rn πs xs is := by
  refine ⟨hs, fun π x i hp h0 ω => ?_⟩
  obtain ⟨hπ, bπ, bx, bi, hAS, hIS⟩ := hp
  obtain ⟨hπs, bπs, bxs, bis, hASs, hISs⟩ := hs
  rw [loss_gap 𝔼 hpull hβ0 hβ1 hπ hπs hΞ1 hΞ2 bπ bx bi bπs bxs bis bΞ1 bΞ2 hAS hASs hIS hISs
    hF15 hF4 hF5 ω]
  have hW : wTerm β γ σ π x πs xs Ξ1 Ξ2 1 = fun _ => 0 := by
    funext ω'
    rw [wTerm_one h0, h10, h20]
    ring
  rw [hW, 𝔼.const]
  have := Jobj_soTerm_nonneg 𝔼 hβ0.le hlx hli (γ := γ) π x i πs xs is ω
  linarith

/-- Woodford (2003), §3.2 with (3.6) (**timeless optimality**): a feasible plan satisfying
(3.15), (3.4), (3.5) at all dates `≥ 1` with bounded multipliers (adapted at dates `≥ 1`, and ANY
bounded initial multipliers `Ξ₀`) is optimal from a timeless perspective. -/
theorem timelesslyOptimal_of_foc {β γ κ σ : ℝ} (hpull : 𝔼.PullOut) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlx : 0 ≤ lamx) (hli : 0 ≤ lami) {u rn πs xs is Ξ1 Ξ2 : ℕ → Ω → ℝ}
    (hs : Feasible 𝔼 β γ κ σ u rn πs xs is)
    (hΞ1 : ∀ k, 1 ≤ k → 𝔼.E k (Ξ1 k) = Ξ1 k) (hΞ2 : ∀ k, 1 ≤ k → 𝔼.E k (Ξ2 k) = Ξ2 k)
    (bΞ1 : Bnd Ξ1) (bΞ2 : Bnd Ξ2)
    (hF15 : ∀ k, 1 ≤ k → FOC315 𝔼 β γ σ πs Ξ1 Ξ2 k)
    (hF4 : ∀ k, 1 ≤ k → FOC34 β κ lamx xstar xs Ξ1 Ξ2 k)
    (hF5 : ∀ k, 1 ≤ k → FOC35 σ lami istar is Ξ1 k) :
    TimelesslyOptimal 𝔼 β γ κ σ lamx lami xstar istar u rn πs xs is := by
  refine ⟨hs, fun π x i hp h0 h1 hx1 ω => ?_⟩
  obtain ⟨hπ, bπ, bx, bi, hAS, hIS⟩ := hp
  obtain ⟨hπs, bπs, bxs, bis, hASs, hISs⟩ := hs
  rw [loss_gap 𝔼 hpull hβ0 hβ1 hπ hπs hΞ1 hΞ2 bπ bx bi bπs bxs bis bΞ1 bΞ2 hAS hASs hIS hISs
    hF15 hF4 hF5 ω]
  have hW : wTerm β γ σ π x πs xs Ξ1 Ξ2 1 = fun _ => 0 := by
    funext ω'
    rw [wTerm_one h0, h1, hx1]
    ring
  rw [hW, 𝔼.const]
  have := Jobj_soTerm_nonneg 𝔼 hβ0.le hlx hli (γ := γ) π x i πs xs is ω
  linarith

/-- Woodford (2003), §3.2 (uniqueness by strict convexity, perfect foresight): with
`λₓ, λᵢ > 0`, if a feasible plan with the same `π₀` attains the same value and the boundary term
vanishes (`Ξ₀ = 0`, or the initial constraints (3.6)), then it coincides with `(π*, x*, i*)` at
every date `≥ 1`. -/
theorem unique_of_foc_perfectForesight {β γ κ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlx : 0 < lamx) (hli : 0 < lami) {u rn π x i πs xs is Ξ1 Ξ2 : ℕ → Unit → ℝ}
    (hp : Feasible perfectForesight β γ κ σ u rn π x i)
    (hs : Feasible perfectForesight β γ κ σ u rn πs xs is)
    (bΞ1 : Bnd Ξ1) (bΞ2 : Bnd Ξ2)
    (hF15 : ∀ k, 1 ≤ k → FOC315 perfectForesight β γ σ πs Ξ1 Ξ2 k)
    (hF4 : ∀ k, 1 ≤ k → FOC34 β κ lamx xstar xs Ξ1 Ξ2 k)
    (hF5 : ∀ k, 1 ≤ k → FOC35 σ lami istar is Ξ1 k) (h0 : ∀ ω, π 0 ω = πs 0 ω)
    (hW : wTerm β γ σ π x πs xs Ξ1 Ξ2 1 () = 0)
    (heq : Jobj perfectForesight β (periodLoss γ lamx lami xstar istar π x i) () =
      Jobj perfectForesight β (periodLoss γ lamx lami xstar istar πs xs is) ()) :
    ∀ k, 1 ≤ k → π k () = πs k () ∧ x k () = xs k () ∧ i k () = is k () := by
  obtain ⟨hπ, bπ, bx, bi, hAS, hIS⟩ := hp
  obtain ⟨hπs, bπs, bxs, bis, hASs, hISs⟩ := hs
  have hgap := loss_gap perfectForesight perfectForesight_pullOut hβ0 hβ1 hπ hπs
    (fun _ _ => rfl) (fun _ _ => rfl) bπ bx bi bπs bxs bis bΞ1 bΞ2 hAS hASs hIS hISs hF15 hF4
    hF5 ()
  have hW' : perfectForesight.E 1 (wTerm β γ σ π x πs xs Ξ1 Ξ2 1) () = 0 := hW
  rw [hW', heq] at hgap
  have hJ : Jobj perfectForesight β (soTerm γ lamx lami π x i πs xs is) () = 0 := by linarith
  have bSO : Bnd (soTerm γ lamx lami π x i πs xs is) :=
    (((bπ.sub bπs).sub ((Bnd.const γ).mul ((bπ.comp (· - 1)).sub (bπs.comp (· - 1))))).sq.add
      ((Bnd.const lamx).mul (bx.sub bxs).sq)).add ((Bnd.const lami).mul (bi.sub bis).sq)
  have hsum := summable_Jobj perfectForesight hβ0.le hβ1 bSO ()
  have hnn : ∀ n, 0 ≤ β ^ n * perfectForesight.E 1 (soTerm γ lamx lami π x i πs xs is (n + 1)) ()
    := fun n => mul_nonneg (pow_nonneg hβ0.le n) (by
      change 0 ≤ soTerm γ lamx lami π x i πs xs is (n + 1) ()
      unfold soTerm
      positivity)
  have hzero := (hasSum_zero_iff_of_nonneg hnn).mp (by
    unfold Jobj at hJ
    rw [← hJ]
    exact hsum.hasSum)
  have hSO : ∀ n, soTerm γ lamx lami π x i πs xs is (n + 1) () = 0 := by
    intro n
    have := congrFun hzero n
    simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
      false_or] at this
    exact this
  have hparts : ∀ n, (π (n + 1) () - πs (n + 1) ()) - γ * (π n () - πs n ()) = 0 ∧
      x (n + 1) () = xs (n + 1) () ∧ i (n + 1) () = is (n + 1) () := by
    intro n
    have h := hSO n
    unfold soTerm at h
    simp only [Nat.add_sub_cancel] at h
    have a1 := sq_nonneg ((π (n + 1) () - πs (n + 1) ()) - γ * (π n () - πs n ()))
    have a2 := mul_nonneg hlx.le (sq_nonneg (x (n + 1) () - xs (n + 1) ()))
    have a3 := mul_nonneg hli.le (sq_nonneg (i (n + 1) () - is (n + 1) ()))
    refine ⟨?_, ?_, ?_⟩
    · nlinarith
    · have : lamx * (x (n + 1) () - xs (n + 1) ()) ^ 2 = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hlx.ne'
      linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this]
    · have : lami * (i (n + 1) () - is (n + 1) ()) ^ 2 = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hli.ne'
      linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this]
  have hπeq : ∀ n, π n () = πs n () := by
    intro n
    induction n with
    | zero => exact h0 ()
    | succ n ih =>
      have := (hparts n).1
      rw [ih, sub_self, mul_zero, sub_zero] at this
      linarith
  intro k hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact ⟨hπeq (n + 1), (hparts n).2.1, (hparts n).2.2⟩

/-! ### The Euler equation (3.16) and the rules implement the timelessly optimal plan -/

/-- Woodford (2003), eq. (3.5), p. 584: the multiplier `Ξ₁k = −(λᵢ/σ)(i_k − i*)`. -/
noncomputable def xi1Of (σ lami istar : ℝ) (is : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  -(lami / σ) * (is k ω - istar)

/-- Woodford (2003), eq. (3.4), p. 584: the multiplier
`Ξ₂k = (λₓ(x_k − x*) + Ξ₁k − β⁻¹Ξ₁,k−1)/κ`. -/
noncomputable def xi2Pos (β κ σ lamx lami xstar istar : ℝ) (xs is : ℕ → Ω → ℝ) (k : ℕ)
    (ω : Ω) : ℝ :=
  (lamx * (xs k ω - xstar) + xi1Of σ lami istar is k ω - β⁻¹ * xi1Of σ lami istar is (k - 1) ω) /
    κ

/-- Woodford (2003), §3.1, p. 585 (multipliers "inferred from the historical values"): the
multipliers `Ξ₂k` (`k ≥ 1`), with the initial `Ξ₂₀` chosen so that (3.15) holds at date 1. -/
noncomputable def xi2Of (β γ κ σ lamx lami xstar istar : ℝ) (πs xs is : ℕ → Ω → ℝ) (k : ℕ)
    (ω : Ω) : ℝ :=
  if k = 0 then
    πs 1 ω - γ * πs 0 ω - β * γ * 𝔼.E 1 (fun ω' => πs 2 ω' - γ * πs 1 ω') ω -
      β⁻¹ * σ * xi1Of σ lami istar is 0 ω -
        β * γ * 𝔼.E 1 (xi2Pos β κ σ lamx lami xstar istar xs is 2) ω +
          (1 + β * γ) * xi2Pos β κ σ lamx lami xstar istar xs is 1 ω
  else xi2Pos β κ σ lamx lami xstar istar xs is k ω

/-- Woodford (2003), §3.2: `xi2Of` agrees with `xi2Pos` at dates `k ≥ 1`. -/
theorem xi2Of_pos {β γ κ σ : ℝ} {πs xs is : ℕ → Ω → ℝ} {k : ℕ} (hk : 1 ≤ k) :
    xi2Of 𝔼 β γ κ σ lamx lami xstar istar πs xs is k =
      xi2Pos β κ σ lamx lami xstar istar xs is k := by
  funext ω
  unfold xi2Of
  split_ifs with h
  · omega
  · rfl

/-- Woodford (2003), (3.16) ⇒ optimality (pp. 592–593: "(3.16) … implicitly defining a policy
rule … robustly optimal"): a feasible adapted plan satisfying the Euler equation (3.16) at every
date `≥ 2` is optimal from a timeless perspective (multipliers constructed by (3.4), (3.5); needs
`σ, κ ≠ 0`, `λᵢ > 0`, `λₓ ≥ 0`, `0 < β < 1` and the pull-out property). -/
theorem timelesslyOptimal_of_euler {β γ κ σ : ℝ} (hpull : 𝔼.PullOut) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : κ ≠ 0) (hσ : σ ≠ 0) (hli : 0 < lami) (hlx : 0 ≤ lamx)
    {u rn πs xs is : ℕ → Ω → ℝ} (hs : Feasible 𝔼 β γ κ σ u rn πs xs is)
    (hπa : 𝔼.Adapted πs) (hxa : 𝔼.Adapted xs) (hia : 𝔼.Adapted is)
    (hE : ∀ t, Euler 𝔼 β γ κ σ (fun k ω => is k ω - istar)
      (fbig 𝔼 β γ κ σ lamx lami πs xs) t) :
    TimelesslyOptimal 𝔼 β γ κ σ lamx lami xstar istar u rn πs xs is := by
  have bπs : Bnd πs := hs.2.1
  have bxs : Bnd xs := hs.2.2.1
  have bis : Bnd is := hs.2.2.2.1
  set Ξ1 := xi1Of σ lami istar is with hΞ1def
  set Ξ2 := xi2Of 𝔼 β γ κ σ lamx lami xstar istar πs xs is with hΞ2def
  have hΞ1a : 𝔼.Adapted Ξ1 := by
    intro k
    have e : Ξ1 k = fun ω => (-(lami / σ)) * is k ω + 0 * is k ω + 0 * is k ω + 0 * is k ω +
        lami / σ * istar := by
      funext ω
      simp only [hΞ1def, xi1Of]
      ring
    rw [e, E_lin4, hia k]
  have hΞ2a : ∀ k, 1 ≤ k → 𝔼.E k (Ξ2 k) = Ξ2 k := by
    intro k hk
    rw [hΞ2def, xi2Of_pos 𝔼 hk]
    have e : xi2Pos β κ σ lamx lami xstar istar xs is k = fun ω =>
        lamx / κ * xs k ω + (-(lami / σ) / κ) * is k ω + (β⁻¹ * (lami / σ) / κ) * is (k - 1) ω +
          0 * is k ω + (-(lamx * xstar) / κ + lami / σ * istar / κ - β⁻¹ * (lami / σ) * istar / κ)
            := by
      funext ω
      simp only [xi2Pos, xi1Of]
      field_simp
      ring
    rw [e, E_lin4, hxa k, hia k, ForwardSolution.E_of_known 𝔼 (by omega) (hia (k - 1))]
  have bΞ1 : Bnd Ξ1 := (Bnd.const (-(lami / σ))).mul (bis.sub (Bnd.const istar))
  have bP : Bnd (xi2Pos β κ σ lamx lami xstar istar xs is) :=
    ((((Bnd.const lamx).mul (bxs.sub (Bnd.const xstar))).add bΞ1).sub
      ((Bnd.const β⁻¹).mul (bΞ1.comp (· - 1)))).mul (Bnd.const κ⁻¹) |>.comp id |> fun h => by
        obtain ⟨C, hC, hCb⟩ := h
        exact ⟨C, hC, fun k ω => by
          have := hCb k ω
          simpa [xi2Pos, div_eq_mul_inv] using this⟩
  have bΞ2 : Bnd Ξ2 := by
    have b0 : Bnd (fun (_ : ℕ) ω => Ξ2 0 ω) := by
      have hb : Bnd (fun (_ : ℕ) ω => πs 1 ω - γ * πs 0 ω -
          β * γ * 𝔼.E 1 (fun ω' => πs 2 ω' - γ * πs 1 ω') ω -
          β⁻¹ * σ * xi1Of σ lami istar is 0 ω -
            β * γ * 𝔼.E 1 (xi2Pos β κ σ lamx lami xstar istar xs is 2) ω +
              (1 + β * γ) * xi2Pos β κ σ lamx lami xstar istar xs is 1 ω) := by
        exact (((((bπs.comp (fun _ => 1)).sub ((Bnd.const γ).mul (bπs.comp (fun _ => 0)))).sub
          ((Bnd.const (β * γ)).mul (Bnd.E 𝔼 ((bπs.comp (fun _ => 2)).sub
            ((Bnd.const γ).mul (bπs.comp (fun _ => 1)))) (fun _ => 1)))).sub
          ((Bnd.const (β⁻¹ * σ)).mul (bΞ1.comp (fun _ => 0)))).sub
          ((Bnd.const (β * γ)).mul (Bnd.E 𝔼 (bP.comp (fun _ => 2)) (fun _ => 1)))).add
          ((Bnd.const (1 + β * γ)).mul (bP.comp (fun _ => 1)))
      refine hb.comp id |> fun h => ?_
      obtain ⟨E0, hE0, hE0b⟩ := h
      exact ⟨E0, hE0, fun k ω => by
        have := hE0b k ω
        simpa [hΞ2def, xi2Of] using this⟩
    obtain ⟨C0, hC0, hC0b⟩ := b0
    obtain ⟨C, hC, hCb⟩ := bP
    refine ⟨max C C0, le_max_of_le_left hC, fun k ω => ?_⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      exact (hC0b 0 ω).trans (le_max_right _ _)
    · rw [hΞ2def, xi2Of_pos 𝔼 hk]
      exact (hCb k ω).trans (le_max_left _ _)
  have hF5 : ∀ k, FOC35 σ lami istar is Ξ1 k := by
    intro k ω
    simp only [hΞ1def, xi1Of]
    field_simp
    ring
  have hF4 : ∀ k, 1 ≤ k → FOC34 β κ lamx xstar xs Ξ1 Ξ2 k := by
    intro k hk ω
    rw [hΞ2def, xi2Of_pos 𝔼 hk]
    simp only [xi2Pos]
    field_simp
    ring
  have hF15 : ∀ k, 1 ≤ k → FOC315 𝔼 β γ σ πs Ξ1 Ξ2 k := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      intro ω
      have e2 : Ξ2 (1 + 1) = xi2Pos β κ σ lamx lami xstar istar xs is 2 := xi2Of_pos 𝔼 (by omega)
      have e1 : Ξ2 1 = xi2Pos β κ σ lamx lami xstar istar xs is 1 := xi2Of_pos 𝔼 le_rfl
      have e0 : Ξ2 (1 - 1) ω = πs 1 ω - γ * πs 0 ω -
          β * γ * 𝔼.E 1 (fun ω' => πs 2 ω' - γ * πs 1 ω') ω -
          β⁻¹ * σ * xi1Of σ lami istar is 0 ω -
            β * γ * 𝔼.E 1 (xi2Pos β κ σ lamx lami xstar istar xs is 2) ω +
              (1 + β * γ) * xi2Pos β κ σ lamx lami xstar istar xs is 1 ω := by
        simp [hΞ2def, xi2Of]
      rw [e2, e1, e0, Nat.sub_self]
      ring
    · obtain ⟨t, rfl⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
      exact (foc315_iff_euler 𝔼 hβ0.ne' hκ hσ hli.ne' hπa hxa hia hΞ1a t
        (fun k _ _ => hF5 k) (fun k hk1 _ => hF4 k (by omega))).mpr (hE t)
  exact timelesslyOptimal_of_foc 𝔼 hpull hβ0 hβ1 hlx hli.le hs (fun k _ => hΞ1a k) hΞ2a bΞ1 bΞ2
    hF15 hF4 (fun k _ => hF5 k)

/-- Woodford (2003), eq. (3.19): `q̃_k` is known at `k` for adapted `π, x`. -/
theorem qtil_adapted {γ κ σ : ℝ} {π x : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hx : 𝔼.Adapted x)
    (k : ℕ) : 𝔼.E k (qtil γ κ σ lamx lami π x k) = qtil γ κ σ lamx lami π x k := by
  have e : qtil γ κ σ lamx lami π x k = fun ω =>
      κ * σ / lami * π k ω + (-(κ * σ / lami * γ)) * π (k - 1) ω +
        κ * σ / lami * (lamx / κ) * x k ω + (-(κ * σ / lami * (lamx / κ))) * x (k - 1) ω + 0 := by
    funext ω
    unfold qtil
    ring
  rw [e, E_lin4, hπ k, hx k, ForwardSolution.E_of_known 𝔼 (by omega) (hπ (k - 1)),
    ForwardSolution.E_of_known 𝔼 (by omega) (hx (k - 1))]

/-- Woodford (2003), eq. (3.18): `f_k` is known at `k` for adapted `π, x`. -/
theorem fbig_adapted {β γ κ σ : ℝ} {π x : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hx : 𝔼.Adapted x) :
    𝔼.Adapted (fbig 𝔼 β γ κ σ lamx lami π x) := by
  intro k
  have e : fbig 𝔼 β γ κ σ lamx lami π x k = fun ω =>
      1 * qtil γ κ σ lamx lami π x k ω +
        (-(β * γ)) * 𝔼.E k (qtil γ κ σ lamx lami π x (k + 1)) ω + 0 * π k ω + 0 * π k ω + 0 := by
    funext ω
    unfold fbig
    ring
  rw [e, E_lin4, qtil_adapted 𝔼 hπ hx, 𝔼.E_E_self, hπ k]

/-- Woodford (2003), eq. (3.18): `f` is bounded for bounded `π, x`. -/
theorem fbig_bnd {β γ κ σ : ℝ} {π x : ℕ → Ω → ℝ} (hπ : Bnd π) (hx : Bnd x) :
    Bnd (fbig 𝔼 β γ κ σ lamx lami π x) := by
  have hq : Bnd (qtil γ κ σ lamx lami π x) :=
    (Bnd.const (κ * σ / lami)).mul ((hπ.sub ((Bnd.const γ).mul (hπ.comp (· - 1)))).add
      ((Bnd.const (lamx / κ)).mul (hx.sub (hx.comp (· - 1)))))
  exact hq.sub ((Bnd.const (β * γ)).mul (Bnd.E 𝔼 (hq.comp (· + 1)) id))

/-- Woodford (2003), §3.2: the deviation `ı̂_k = i_k − ī` is adapted and bounded. -/
theorem hat_adapted_bnd {i : ℕ → Ω → ℝ} (hia : 𝔼.Adapted i) (bi : Bnd i) (c : ℝ) :
    𝔼.Adapted (fun k ω => i k ω - c) ∧ ∃ M, ∀ k ω, |i k ω - c| ≤ M := by
  refine ⟨fun k => ?_, ?_⟩
  · have e : (fun ω => i k ω - c) = fun ω => 1 * i k ω + 0 * i k ω + 0 * i k ω + 0 * i k ω +
        (-c) := by
      funext ω
      ring
    change 𝔼.E k (fun ω => i k ω - c) = fun ω => i k ω - c
    rw [e, E_lin4, hia k]
  · obtain ⟨C, _, hC⟩ := bi.sub (Bnd.const c)
    exact ⟨C, hC⟩

/-- Woodford (2003), p. 596 ("each represents an optimal policy rule from a timeless
perspective"): if the deviations `ı̂ = i − ī`, `f̂ = f − f̄` (with `A(1)(ī − i*) = −f̄`) satisfy
the Euler equation (3.21) at every date, the plan is optimal from a timeless perspective. -/
theorem timelesslyOptimal_of_euler_hat {β γ κ σ : ℝ} (h : Standing β γ κ σ)
    (hpull : 𝔼.PullOut) (hli : 0 < lami) (hlx : 0 ≤ lamx) {u rn πs xs is : ℕ → Ω → ℝ}
    (hs : Feasible 𝔼 β γ κ σ u rn πs xs is) (hπa : 𝔼.Adapted πs) (hxa : 𝔼.Adapted xs)
    (hia : 𝔼.Adapted is) {ibar fbar : ℝ} (hss : β⁻¹ * (κ * σ) * (ibar - istar) = -fbar)
    (hE : ∀ t, Euler 𝔼 β γ κ σ (fun k ω => is k ω - ibar)
      (fun k ω => fbig 𝔼 β γ κ σ lamx lami πs xs k ω - fbar) t) :
    TimelesslyOptimal 𝔼 β γ κ σ lamx lami xstar istar u rn πs xs is :=
  timelesslyOptimal_of_euler 𝔼 hpull h.beta_pos h.beta_lt_one h.kappa_pos.ne' h.sigma_pos.ne'
    hli hlx hs hπa hxa hia fun t => (euler_hat_iff 𝔼 hss t).mpr (hE t)

/-- Woodford (2003), **Proposition 8.8 + p. 596**: commitment to the real-coefficient Rule III
(3.24) — defined for real roots AND for a complex pair — at every date implements the timelessly
optimal plan. -/
theorem ruleIII_timelesslyOptimal {β γ κ σ : ℝ} (h : Standing β γ κ σ) (hpull : 𝔼.PullOut)
    (hli : 0 < lami) (hlx : 0 ≤ lamx) {u rn πs xs is : ℕ → Ω → ℝ}
    (hs : Feasible 𝔼 β γ κ σ u rn πs xs is) (hπa : 𝔼.Adapted πs) (hxa : 𝔼.Adapted xs)
    (hia : 𝔼.Adapted is) {ibar fbar : ℝ} (hss : β⁻¹ * (κ * σ) * (ibar - istar) = -fbar)
    (hR : ∀ t, RuleIIIReal 𝔼 (lam1 β γ κ σ) (sumS β γ κ σ)
      (fun j => (psiIII β γ (lam2 β γ κ σ) (lam3 β γ κ σ) j).re) (fun k ω => is k ω - ibar)
      (fun k ω => fbig 𝔼 β γ κ σ lamx lami πs xs k ω - fbar) t) :
    TimelesslyOptimal 𝔼 β γ κ σ lamx lami xstar istar u rn πs xs is := by
  obtain ⟨hıa, Mı, hıb⟩ := hat_adapted_bnd 𝔼 hia hs.2.2.2.1 ibar
  obtain ⟨hfa, Mf, hfb⟩ := hat_adapted_bnd 𝔼 (fbig_adapted 𝔼 hπa hxa)
    (fbig_bnd 𝔼 hs.2.1 hs.2.2.1) fbar
  have hE := (prop_8_8_ruleIII_real 𝔼 h hıa hfa hıb hfb 0).mp (fun t _ => hR t)
  exact timelesslyOptimal_of_euler_hat 𝔼 h hpull hli hlx hs hπa hxa hia hss
    fun t => hE t (Nat.zero_le t)

/-- Woodford (2003), **Proposition 8.8 + p. 596** (three real roots): commitment to the real
Rule I (3.22) at every date implements the timelessly optimal plan. -/
theorem ruleI_timelesslyOptimal {β γ κ σ : ℝ} (h : Standing β γ κ σ)
    (hD : 0 ≤ discQ β γ κ σ) (hpull : 𝔼.PullOut) (hli : 0 < lami) (hlx : 0 ≤ lamx)
    {u rn πs xs is : ℕ → Ω → ℝ} (hs : Feasible 𝔼 β γ κ σ u rn πs xs is)
    (hπa : 𝔼.Adapted πs) (hxa : 𝔼.Adapted xs) (hia : 𝔼.Adapted is) {ibar fbar : ℝ}
    (hss : β⁻¹ * (κ * σ) * (ibar - istar) = -fbar)
    (hR : ∀ t, RuleIReal 𝔼 β γ (lam1 β γ κ σ) (lam2r β γ κ σ) (lam3r β γ κ σ)
      (fun k ω => is k ω - ibar) (fun k ω => fbig 𝔼 β γ κ σ lamx lami πs xs k ω - fbar) t) :
    TimelesslyOptimal 𝔼 β γ κ σ lamx lami xstar istar u rn πs xs is := by
  obtain ⟨hıa, Mı, hıb⟩ := hat_adapted_bnd 𝔼 hia hs.2.2.2.1 ibar
  obtain ⟨hfa, Mf, hfb⟩ := hat_adapted_bnd 𝔼 (fbig_adapted 𝔼 hπa hxa)
    (fbig_bnd 𝔼 hs.2.1 hs.2.2.1) fbar
  have hE := ((prop_8_8_real 𝔼 h hD hıa hfa hıb hfb 0).1).mp (fun t _ => hR t)
  exact timelesslyOptimal_of_euler_hat 𝔼 h hpull hli hlx hs hπa hxa hia hss
    fun t => hE t (Nat.zero_le t)

/-- Woodford (2003), **Proposition 8.8 + p. 596** (three real roots): commitment to the real
Rule II (3.23) at every date implements the timelessly optimal plan. -/
theorem ruleII_timelesslyOptimal {β γ κ σ : ℝ} (h : Standing β γ κ σ)
    (hD : 0 ≤ discQ β γ κ σ) (hpull : 𝔼.PullOut) (hli : 0 < lami) (hlx : 0 ≤ lamx)
    {u rn πs xs is : ℕ → Ω → ℝ} (hs : Feasible 𝔼 β γ κ σ u rn πs xs is)
    (hπa : 𝔼.Adapted πs) (hxa : 𝔼.Adapted xs) (hia : 𝔼.Adapted is) {ibar fbar : ℝ}
    (hss : β⁻¹ * (κ * σ) * (ibar - istar) = -fbar)
    (hR : ∀ t, RuleIIReal 𝔼 β γ (lam1 β γ κ σ) (lam2r β γ κ σ) (lam3r β γ κ σ)
      (fun k ω => is k ω - ibar) (fun k ω => fbig 𝔼 β γ κ σ lamx lami πs xs k ω - fbar) t) :
    TimelesslyOptimal 𝔼 β γ κ σ lamx lami xstar istar u rn πs xs is := by
  obtain ⟨hıa, Mı, hıb⟩ := hat_adapted_bnd 𝔼 hia hs.2.2.2.1 ibar
  obtain ⟨hfa, Mf, hfb⟩ := hat_adapted_bnd 𝔼 (fbig_adapted 𝔼 hπa hxa)
    (fbig_bnd 𝔼 hs.2.1 hs.2.2.1) fbar
  have hE := ((prop_8_8_real 𝔼 h hD hıa hfa hıb hfb 0).2).mp (fun t _ => hR t)
  exact timelesslyOptimal_of_euler_hat 𝔼 h hpull hli hlx hs hπa hxa hia hss
    fun t => hE t (Nat.zero_le t)

/-! ### Determinacy of the rule system (3.16) + (2.6) + (3.1) (p. 593) -/

/-- Woodford (2003), eq. (3.5): the multiplier `Ξ₁` built from `i` is adapted. -/
theorem xi1Of_adapted {σ : ℝ} {is : ℕ → Ω → ℝ} (hia : 𝔼.Adapted is) :
    𝔼.Adapted (xi1Of σ lami istar is) := by
  intro k
  have e : xi1Of σ lami istar is k = fun ω => (-(lami / σ)) * is k ω + 0 * is k ω +
      0 * is k ω + 0 * is k ω + lami / σ * istar := by
    funext ω
    simp only [xi1Of]
    ring
  rw [e, E_lin4, hia k]

/-- Woodford (2003), eq. (3.4): the multiplier `Ξ₂k` built from `x, i` is known at `k ≥ 1`. -/
theorem xi2Pos_known {β κ σ : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) {xs is : ℕ → Ω → ℝ}
    (hxa : 𝔼.Adapted xs) (hia : 𝔼.Adapted is) {k : ℕ} (hk : 1 ≤ k) :
    𝔼.E k (xi2Pos β κ σ lamx lami xstar istar xs is k) =
      xi2Pos β κ σ lamx lami xstar istar xs is k := by
  have e : xi2Pos β κ σ lamx lami xstar istar xs is k = fun ω =>
      lamx / κ * xs k ω + (-(lami / σ) / κ) * is k ω + (β⁻¹ * (lami / σ) / κ) * is (k - 1) ω +
        0 * is k ω + (-(lamx * xstar) / κ + lami / σ * istar / κ - β⁻¹ * (lami / σ) * istar / κ)
          := by
    funext ω
    simp only [xi2Pos, xi1Of]
    field_simp
    ring
  rw [e, E_lin4, hxa k, hia k, ForwardSolution.E_of_known 𝔼 (by omega) (hia (k - 1))]

/-- Woodford (2003), eq. (3.5) holds for `Ξ₁ = xi1Of` (`σ ≠ 0`). -/
theorem foc35_xi1Of {σ : ℝ} (hσ : σ ≠ 0) (is : ℕ → Ω → ℝ) (k : ℕ) :
    FOC35 σ lami istar is (xi1Of σ lami istar is) k := by
  intro ω
  simp only [xi1Of]
  field_simp
  ring

/-- Woodford (2003), eq. (3.4) holds for `Ξ₂ = xi2Pos` (`κ ≠ 0`). -/
theorem foc34_xi2Pos {β κ σ : ℝ} (hκ : κ ≠ 0) (xs is : ℕ → Ω → ℝ) (k : ℕ) :
    FOC34 β κ lamx xstar xs (xi1Of σ lami istar is)
      (xi2Pos β κ σ lamx lami xstar istar xs is) k := by
  intro ω
  simp only [xi2Pos]
  field_simp
  ring

/-- Woodford (2003), (2.6): the difference of two solutions solves the homogeneous (2.6). -/
theorem AS_sub {β γ κ : ℝ} {u π x π' x' : ℕ → Ω → ℝ} {k : ℕ} (h : AS 𝔼 β γ κ u π x k)
    (h' : AS 𝔼 β γ κ u π' x' k) :
    AS 𝔼 β γ κ (fun _ _ => 0) (fun k ω => π k ω - π' k ω) (fun k ω => x k ω - x' k ω) k := by
  intro ω
  have e : (fun ω' => (π (k + 1) ω' - π' (k + 1) ω') - γ * (π k ω' - π' k ω')) =
      fun ω' => (π (k + 1) ω' - γ * π k ω') - (π' (k + 1) ω' - γ * π' k ω') := by
    funext ω'
    ring
  have h1 := h ω
  have h2 := h' ω
  simp only
  rw [e, E_fun_sub]
  simp only
  linarith

/-- Woodford (2003), (3.1): the difference of two solutions solves the homogeneous (3.1). -/
theorem IS_sub {σ : ℝ} {rn π x i π' x' i' : ℕ → Ω → ℝ} {k : ℕ} (h : IS 𝔼 σ rn π x i k)
    (h' : IS 𝔼 σ rn π' x' i' k) :
    IS 𝔼 σ (fun _ _ => 0) (fun k ω => π k ω - π' k ω) (fun k ω => x k ω - x' k ω)
      (fun k ω => i k ω - i' k ω) k := by
  intro ω
  have h1 := h ω
  have h2 := h' ω
  simp only
  rw [E_fun_sub, E_fun_sub]
  simp only
  linarith

/-- Woodford (2003), (3.16): the difference of two solutions solves the homogeneous (3.16). -/
theorem Euler_sub {β γ κ σ : ℝ} {π x i π' x' i' : ℕ → Ω → ℝ} {t : ℕ}
    (h : Euler 𝔼 β γ κ σ (fun k ω => i k ω - istar) (fbig 𝔼 β γ κ σ lamx lami π x) t)
    (h' : Euler 𝔼 β γ κ σ (fun k ω => i' k ω - istar) (fbig 𝔼 β γ κ σ lamx lami π' x') t) :
    Euler 𝔼 β γ κ σ (fun k ω => (i k ω - i' k ω) - 0)
      (fbig 𝔼 β γ κ σ lamx lami (fun k ω => π k ω - π' k ω) (fun k ω => x k ω - x' k ω)) t := by
  intro ω
  have eA : ALi β γ κ σ (fun k ω => (i k ω - i' k ω) - 0) t = fun ω =>
      ALi β γ κ σ (fun k ω => i k ω - istar) t ω - ALi β γ κ σ (fun k ω => i' k ω - istar) t ω := by
    funext ω
    unfold ALi
    ring
  have eq : qtil γ κ σ lamx lami (fun k ω => π k ω - π' k ω) (fun k ω => x k ω - x' k ω)
      (t + 2 + 1) = fun ω => qtil γ κ σ lamx lami π x (t + 2 + 1) ω -
        qtil γ κ σ lamx lami π' x' (t + 2 + 1) ω := by
    funext ω
    unfold qtil
    ring
  have h1 := h ω
  have h2 := h' ω
  unfold fbig at h1 h2 ⊢
  rw [eA, E_fun_sub, eq, E_fun_sub]
  simp only
  unfold qtil at h1 h2 ⊢
  linarith

/-- The zero plan satisfies the homogeneous (2.6) (Woodford (2003), p. 593). -/
theorem AS_zero {β γ κ : ℝ} (k : ℕ) :
    AS 𝔼 β γ κ (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) k := by
  intro ω
  have e : (fun _ : Ω => (0 : ℝ) - γ * 0) = fun _ => 0 := by
    funext
    ring
  simp only
  rw [e, E_fun_zero]
  ring

/-- The zero plan satisfies the homogeneous (3.1) (Woodford (2003), p. 593). -/
theorem IS_zero {σ : ℝ} (k : ℕ) :
    IS 𝔼 σ (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) k := by
  intro ω
  simp only [E_fun_zero]
  ring

/-- Woodford (2003), p. 593 (**determinacy of the rule (3.16), uniqueness part**): for ALL
admissible parameters (`0 < β < 1`, `κ, σ ≠ 0`, `λᵢ > 0`, `λₓ ≥ 0`, any `γ`), two bounded adapted
solutions of (2.6), (3.1) (dates `≥ 2`) and (3.16) (dates `≥ 2`) with the same history
`(π₁, x₁, i₁, i₀)` coincide at every date `≥ 1` (faithful expectations, pull-out property).
The proof uses strict convexity of the loss (3.14): the difference solves the FOCs of the
homogeneous problem and its discounted loss equals a boundary term that the history kills. -/
theorem rule_system_unique {β γ κ σ : ℝ} (hpull : 𝔼.PullOut) (hfaith : Faithful 𝔼)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hσ : σ ≠ 0) (hli : 0 < lami) (hlx : 0 ≤ lamx)
    {u rn π x i π' x' i' : ℕ → Ω → ℝ}
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) (hia : 𝔼.Adapted i)
    (hπa' : 𝔼.Adapted π') (hxa' : 𝔼.Adapted x') (hia' : 𝔼.Adapted i')
    (bπ : Bnd π) (bx : Bnd x) (bi : Bnd i) (bπ' : Bnd π') (bx' : Bnd x') (bi' : Bnd i')
    (hAS : ∀ k, 2 ≤ k → AS 𝔼 β γ κ u π x k) (hAS' : ∀ k, 2 ≤ k → AS 𝔼 β γ κ u π' x' k)
    (hIS : ∀ k, 2 ≤ k → IS 𝔼 σ rn π x i k) (hIS' : ∀ k, 2 ≤ k → IS 𝔼 σ rn π' x' i' k)
    (hE : ∀ t, Euler 𝔼 β γ κ σ (fun k ω => i k ω - istar) (fbig 𝔼 β γ κ σ lamx lami π x) t)
    (hE' : ∀ t, Euler 𝔼 β γ κ σ (fun k ω => i' k ω - istar)
      (fbig 𝔼 β γ κ σ lamx lami π' x') t)
    (h1π : ∀ ω, π 1 ω = π' 1 ω) (h1x : ∀ ω, x 1 ω = x' 1 ω) (h1i : ∀ ω, i 1 ω = i' 1 ω)
    (h0i : ∀ ω, i 0 ω = i' 0 ω) :
    ∀ k, 1 ≤ k → ∀ ω, π k ω = π' k ω ∧ x k ω = x' k ω ∧ i k ω = i' k ω := by
  set dπ : ℕ → Ω → ℝ := fun k ω => π k ω - π' k ω with hdπ
  set dx : ℕ → Ω → ℝ := fun k ω => x k ω - x' k ω with hdx
  set di : ℕ → Ω → ℝ := fun k ω => i k ω - i' k ω with hdi
  set Z : ℕ → Ω → ℝ := fun _ _ => 0 with hZ
  have hda : ∀ {p p' : ℕ → Ω → ℝ}, 𝔼.Adapted p → 𝔼.Adapted p' →
      𝔼.Adapted (fun k ω => p k ω - p' k ω) := by
    intro p p' hp hp' k
    rw [E_fun_sub, hp k, hp' k]
  have hdπa : 𝔼.Adapted dπ := hda hπa hπa'
  have hdxa : 𝔼.Adapted dx := hda hxa hxa'
  have hdia : 𝔼.Adapted di := hda hia hia'
  set Ξ1 := xi1Of σ lami (0 : ℝ) di with hΞ1
  set Ξ2 := xi2Pos β κ σ lamx lami (0 : ℝ) (0 : ℝ) dx di with hΞ2
  have hΞ1a : 𝔼.Adapted Ξ1 := xi1Of_adapted 𝔼 hdia
  have hF5 : ∀ k, FOC35 σ lami 0 di Ξ1 k := fun k => foc35_xi1Of hσ di k
  have hF4 : ∀ k, FOC34 β κ lamx 0 dx Ξ1 Ξ2 k := fun k => foc34_xi2Pos hκ dx di k
  have hF15 : ∀ k, 2 ≤ k → FOC315 𝔼 β γ σ dπ Ξ1 Ξ2 k := by
    intro k hk
    obtain ⟨t, rfl⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
    exact (foc315_iff_euler 𝔼 hβ0.ne' hκ hσ hli.ne' hdπa hdxa hdia hΞ1a t
      (fun k _ _ => hF5 k) (fun k _ _ => hF4 k)).mpr (Euler_sub 𝔼 (hE t) (hE' t))
  -- the per-period identity `L_k(d) = −W_k + β E_k W_{k+1}`
  have hid : ∀ k, 2 ≤ k → ∀ ω, (periodLoss γ lamx lami 0 0 dπ dx di) k ω = -(wTerm β γ σ Z Z dπ
      dx Ξ1 Ξ2) k ω + β * 𝔼.E k ((wTerm β γ σ Z Z dπ dx Ξ1 Ξ2) (k + 1)) ω := by
    intro k hk ω
    have hk1 : 1 ≤ k := by omega
    have := foTerm_eq 𝔼 hpull hβ0.ne' (u := Z) (rn := Z) (π := Z) (x := Z) (i := Z)
      (πs := dπ) (xs := dx) (is := di) (Ξ1 := Ξ1) (Ξ2 := Ξ2) (k := k)
      (by simp only [hZ, E_fun_zero]) (hdπa k) (hΞ1a k)
      (xi2Pos_known 𝔼 hκ hσ hdxa hdia hk1) (AS_zero 𝔼 k) (AS_sub 𝔼 (hAS k hk) (hAS' k hk))
      (IS_zero 𝔼 k) (IS_sub 𝔼 (hIS k hk) (hIS' k hk)) (hF15 k hk) (hF4 k) (hF5 k) ω
    have hfo : foTerm γ lamx lami 0 0 Z Z Z dπ dx di k ω = -(periodLoss γ lamx lami 0 0 dπ dx
        di) k ω := by
      simp only [foTerm, periodLoss, hZ]
      ring
    linarith
  -- boundedness
  have bdπ : Bnd dπ := bπ.sub bπ'
  have bdx : Bnd dx := bx.sub bx'
  have bdi : Bnd di := bi.sub bi'
  have bΞ1 : Bnd Ξ1 := (Bnd.const (-(lami / σ))).mul (bdi.sub (Bnd.const 0))
  have bΞ2 : Bnd Ξ2 :=
    ((((Bnd.const lamx).mul (bdx.sub (Bnd.const 0))).add bΞ1).sub
      ((Bnd.const β⁻¹).mul (bΞ1.comp (· - 1)))).mul (Bnd.const κ⁻¹) |> fun h => by
        obtain ⟨C, hC, hCb⟩ := h
        exact ⟨C, hC, fun k ω => by
          have := hCb k ω
          simpa [hΞ2, xi2Pos, div_eq_mul_inv] using this⟩
  have bW : Bnd ((wTerm β γ σ Z Z dπ dx Ξ1 Ξ2)) :=
    (((Bnd.const β⁻¹).mul (((((Bnd.const σ).mul (bΞ1.comp (· - 1))).add
      ((Bnd.const β).mul (bΞ2.comp (· - 1)))).mul ((Bnd.const 0).sub bdπ)).add
        ((bΞ1.comp (· - 1)).mul ((Bnd.const 0).sub bdx)))).sub
      (((Bnd.const γ).mul (bdπ.sub ((Bnd.const γ).mul (bdπ.comp (· - 1))))).mul
        ((Bnd.const 0).sub (bdπ.comp (· - 1))))).sub
      (((Bnd.const γ).mul bΞ2).mul ((Bnd.const 0).sub (bdπ.comp (· - 1))))
  have bL : Bnd ((periodLoss γ lamx lami 0 0 dπ dx di)) :=
    ((bdπ.sub ((Bnd.const γ).mul (bdπ.comp (· - 1)))).sq.add
      ((Bnd.const lamx).mul (bdx.sub (Bnd.const 0)).sq)).add
      ((Bnd.const lami).mul (bdi.sub (Bnd.const 0)).sq)
  obtain ⟨CW, _, hCW⟩ := bW
  obtain ⟨CL, _, hCL⟩ := bL
  -- the boundary term vanishes by the common history
  have hW2 : (wTerm β γ σ Z Z dπ dx Ξ1 Ξ2) 2 = fun _ => 0 := by
    funext ω
    have e1 : dπ 1 ω = 0 := by simp [hdπ, h1π ω]
    have e2 : dx 1 ω = 0 := by simp [hdx, h1x ω]
    have e3 : di 1 ω = 0 := by simp [hdi, h1i ω]
    have e4 : di 0 ω = 0 := by simp [hdi, h0i ω]
    simp only [wTerm, hΞ2, hΞ1, xi2Pos, xi1Of, show (2 : ℕ) - 1 = 1 from rfl,
      show (1 : ℕ) - 1 = 0 from rfl, e1, e2, e3, e4, hZ]
    ring
  -- the discounted sum of expected losses from date 2 vanishes
  have hsum : ∀ ω, ∑' n, β ^ n * 𝔼.E 2 ((periodLoss γ lamx lami 0 0 dπ dx di) (n + 2)) ω = 0 := by
    intro ω
    have hper : ∀ n, β ^ n * 𝔼.E 2 ((periodLoss γ lamx lami 0 0 dπ dx di) (n + 2)) ω =
        -(β ^ n * (𝔼.E 2 ((wTerm β γ σ Z Z dπ dx Ξ1 Ξ2) (n + 1 + 1)) ω - β * 𝔼.E 2 ((wTerm β γ σ
            Z Z dπ dx Ξ1 Ξ2) (n + 2 + 1)) ω)) := by
      intro n
      have hfun : (periodLoss γ lamx lami 0 0 dπ dx di) (n + 2) = fun ω' => (-1) * (wTerm β γ σ
          Z Z dπ dx Ξ1 Ξ2) (n + 2) ω' +
          β * 𝔼.E (n + 2) ((wTerm β γ σ Z Z dπ dx Ξ1 Ξ2) (n + 2 + 1)) ω' + 0 * (wTerm β γ σ Z Z
              dπ dx Ξ1 Ξ2) 0 ω' + 0 * (wTerm β γ σ Z Z dπ dx Ξ1 Ξ2) 0 ω' + 0 := by
        funext ω'
        rw [hid (n + 2) (by omega) ω']
        ring
      have e := congrFun (E_lin4 𝔼 2 (-1) β 0 0 0 ((wTerm β γ σ Z Z dπ dx Ξ1 Ξ2) (n + 2))
        (𝔼.E (n + 2) ((wTerm β γ σ Z Z dπ dx Ξ1 Ξ2) (n + 2 + 1))) ((wTerm β γ σ Z Z dπ dx Ξ1 Ξ2)
            0) ((wTerm β γ σ Z Z dπ dx Ξ1 Ξ2) 0)) ω
      rw [𝔼.tower (show 2 ≤ n + 2 by omega), ← hfun] at e
      rw [e]
      ring
    have ht := tsum_telescope hβ0.le hβ1 (w := fun m => 𝔼.E 2 ((wTerm β γ σ Z Z dπ dx Ξ1 Ξ2) (m
        + 1)) ω) (C := CW)
      (fun m => 𝔼.abs_E_le (hCW _) 2 ω)
    beta_reduce at ht
    rw [tsum_congr hper, tsum_neg, ht, hW2, E_fun_zero, neg_zero]
  have hle : ∀ n, (fun _ => (0 : ℝ)) ≤ (periodLoss γ lamx lami 0 0 dπ dx di) (n + 2) := fun n ω'
      => by
    simp only [periodLoss]
    positivity
  have hnn : ∀ n ω, 0 ≤ β ^ n * 𝔼.E 2 ((periodLoss γ lamx lami 0 0 dπ dx di) (n + 2)) ω := fun n
      ω => mul_nonneg
    (pow_nonneg hβ0.le n) (by
      have := 𝔼.mono 2 (hle n) ω
      rw [𝔼.const] at this
      exact this)
  have hsm : ∀ ω, Summable (fun n => β ^ n * 𝔼.E 2 ((periodLoss γ lamx lami 0 0 dπ dx di) (n +
      2)) ω) := fun ω =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right CL)
      (fun n => by
        rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hβ0.le]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hCL _) 2 ω) (by positivity))
  have hEL : ∀ n ω, 𝔼.E 2 ((periodLoss γ lamx lami 0 0 dπ dx di) (n + 2)) ω = 0 := by
    intro n ω
    have hz := (hasSum_zero_iff_of_nonneg (fun n => hnn n ω)).mp
      (by have h := (hsm ω).hasSum; rw [hsum ω] at h; exact h)
    have := congrFun hz n
    simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
      false_or] at this
    exact this
  have hL0 : ∀ k, 2 ≤ k → ∀ ω, (periodLoss γ lamx lami 0 0 dπ dx di) k ω = 0 := by
    intro k hk ω
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    exact hfaith.eq_zero (t := 2) (y := (periodLoss γ lamx lami 0 0 dπ dx di) (n + 2)) (hle n)
      (funext (hEL n)) ω
  have hpart : ∀ k, 2 ≤ k → ∀ ω, dπ k ω - γ * dπ (k - 1) ω = 0 ∧ di k ω = 0 := by
    intro k hk ω
    have h := hL0 k hk ω
    simp only [periodLoss, sub_zero] at h
    have a1 := sq_nonneg (dπ k ω - γ * dπ (k - 1) ω)
    have a2 := mul_nonneg hlx (sq_nonneg (dx k ω))
    have a3 := mul_nonneg hli.le (sq_nonneg (di k ω))
    constructor
    · have : (dπ k ω - γ * dπ (k - 1) ω) ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    · have : lami * di k ω ^ 2 = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hli.ne'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hπ0 : ∀ k, 1 ≤ k → ∀ ω, dπ k ω = 0 := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ n ih =>
      intro _ ω
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp [hdπ, h1π ω]
      · have := (hpart (n + 1) (by omega) ω).1
        simp only [Nat.add_sub_cancel] at this
        rw [ih hn ω, mul_zero, sub_zero] at this
        exact this
  have hx0 : ∀ k, 2 ≤ k → ∀ ω, dx k ω = 0 := by
    intro k hk ω
    have h := AS_sub 𝔼 (hAS k hk) (hAS' k hk) ω
    have e : (fun ω' => (π (k + 1) ω' - π' (k + 1) ω') - γ * (π k ω' - π' k ω')) =
        fun _ => 0 := by
      funext ω'
      have a := hπ0 (k + 1) (by omega) ω'
      have b := hπ0 k (by omega) ω'
      simp only [hdπ] at a b
      rw [a, b]
      ring
    simp only at h
    rw [e, E_fun_zero] at h
    simp only at h
    have a := hπ0 k (by omega) ω
    have b := hπ0 (k - 1) (by omega) ω
    simp only [hdπ] at a b
    rw [a, b, mul_zero] at h
    have : κ * (x k ω - x' k ω) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hκ
    simp only [hdx]
    exact this
  intro k hk ω
  have hπk := hπ0 k hk ω
  simp only [hdπ] at hπk
  refine ⟨by linarith, ?_, ?_⟩
  · rcases Nat.lt_or_ge k 2 with h2 | h2
    · obtain rfl : k = 1 := by omega
      exact h1x ω
    · have := hx0 k h2 ω
      simp only [hdx] at this
      linarith
  · rcases Nat.lt_or_ge k 2 with h2 | h2
    · obtain rfl : k = 1 := by omega
      exact h1i ω
    · have := (hpart k h2 ω).2
      simp only [hdi] at this
      linarith

/-- Woodford (2003), p. 593 (**the Prop 8.5 analogue**): if the optimal-plan system — (2.6),
(3.1) and the FOCs (3.15) (dates `≥ 2`), (3.4) (dates `≥ 1`), (3.5) (all dates), with multipliers
whose date-1 values are inferred from history — has a bounded adapted solution, then that plan
solves the rule system (2.6), (3.1), (3.16), and it is the ONLY bounded adapted solution of the
rule system with its history `(π₁, x₁, i₁, i₀)` (determinacy; faithful expectations). -/
theorem rule_system_determinate {β γ κ σ : ℝ} (hpull : 𝔼.PullOut) (hfaith : Faithful 𝔼)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hσ : σ ≠ 0) (hli : 0 < lami) (hlx : 0 ≤ lamx)
    {u rn πs xs is Ξ1 Ξ2 : ℕ → Ω → ℝ}
    (hπa : 𝔼.Adapted πs) (hxa : 𝔼.Adapted xs) (hia : 𝔼.Adapted is) (hΞ1 : 𝔼.Adapted Ξ1)
    (bπ : Bnd πs) (bx : Bnd xs) (bi : Bnd is)
    (hAS : ∀ k, 2 ≤ k → AS 𝔼 β γ κ u πs xs k) (hIS : ∀ k, 2 ≤ k → IS 𝔼 σ rn πs xs is k)
    (hF5 : ∀ k, FOC35 σ lami istar is Ξ1 k) (hF4 : ∀ k, 1 ≤ k → FOC34 β κ lamx xstar xs Ξ1 Ξ2 k)
    (hF15 : ∀ k, 2 ≤ k → FOC315 𝔼 β γ σ πs Ξ1 Ξ2 k) :
    (∀ t, Euler 𝔼 β γ κ σ (fun k ω => is k ω - istar) (fbig 𝔼 β γ κ σ lamx lami πs xs) t) ∧
    ∀ π x i : ℕ → Ω → ℝ, 𝔼.Adapted π → 𝔼.Adapted x → 𝔼.Adapted i → Bnd π → Bnd x → Bnd i →
      (∀ k, 2 ≤ k → AS 𝔼 β γ κ u π x k) → (∀ k, 2 ≤ k → IS 𝔼 σ rn π x i k) →
      (∀ t, Euler 𝔼 β γ κ σ (fun k ω => i k ω - istar) (fbig 𝔼 β γ κ σ lamx lami π x) t) →
      (∀ ω, π 1 ω = πs 1 ω) → (∀ ω, x 1 ω = xs 1 ω) → (∀ ω, i 1 ω = is 1 ω) →
      (∀ ω, i 0 ω = is 0 ω) →
      ∀ k, 1 ≤ k → ∀ ω, π k ω = πs k ω ∧ x k ω = xs k ω ∧ i k ω = is k ω := by
  have hE : ∀ t, Euler 𝔼 β γ κ σ (fun k ω => is k ω - istar)
      (fbig 𝔼 β γ κ σ lamx lami πs xs) t := fun t =>
    (foc315_iff_euler 𝔼 hβ0.ne' hκ hσ hli.ne' hπa hxa hia hΞ1 t (fun k _ _ => hF5 k)
      (fun k hk _ => hF4 k (by omega))).mp (hF15 (t + 2) (by omega))
  refine ⟨hE, fun π x i ha hb hc b1 b2 b3 hAS' hIS' hE' h1 h2 h3 h4 => ?_⟩
  exact rule_system_unique 𝔼 hpull hfaith hβ0 hβ1 hκ hσ hli hlx ha hb hc hπa hxa hia b1 b2 b3
    bπ bx bi hAS' hAS hIS' hIS hE' hE h1 h2 h3 h4

/-! ### The characteristic polynomial of the rule system (p. 593, cf. App. G.4) -/

/-- Woodford (2003), App. G.6: `R(μ) = μ³A(μ⁻¹) = βγμ³ − (1 + γ + βγ)μ² + A₂μ − β⁻¹` (complex). -/
noncomputable def recipC (β γ κ σ : ℝ) (μ : ℂ) : ℂ :=
  (coefA0 β γ : ℂ) * μ ^ 3 + (coefA1 β γ : ℂ) * μ ^ 2 + (coefA2 β γ κ σ : ℂ) * μ + coefA3 β

/-- Woodford (2003), p. 593 with App. G.4, (G.10)–(G.11): the symbol of the homogeneous system
(2.6), (3.1), (3.16) at `z_t = μᵗ v` (rows: (2.6)·(−μ), (3.1), (3.16)·μ^{2−t}; columns π, x, i). -/
noncomputable def charMat (β γ κ σ lamx lami : ℝ) (μ : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![((β : ℂ) * μ - 1) * (μ - γ), (κ : ℂ) * μ, 0;
    -(σ : ℂ) * μ, 1 - μ, σ;
    ((κ * σ / lami : ℝ) : ℂ) * μ * (1 - β * γ * μ) * (μ - γ),
      ((σ * lamx / lami : ℝ) : ℂ) * μ * (1 - β * γ * μ) * (μ - 1), recipC β γ κ σ μ]

/-- Woodford (2003), p. 593 (cf. (G.11)): the characteristic polynomial (degree 6) of the rule
system, `D(μ) = (βμ − 1)(μ − γ)(1 − μ)[R(μ) + σ(σλₓ/λᵢ)μ(1 − βγμ)] + κσμ²R(μ)
+ κσ(κσ/λᵢ)μ²(1 − βγμ)(μ − γ)`. -/
noncomputable def charD (β γ κ σ lamx lami : ℝ) (μ : ℂ) : ℂ :=
  ((β : ℂ) * μ - 1) * (μ - γ) * (1 - μ) *
      (recipC β γ κ σ μ + σ * ((σ * lamx / lami : ℝ) : ℂ) * μ * (1 - β * γ * μ)) +
    κ * σ * μ ^ 2 * recipC β γ κ σ μ +
      κ * σ * ((κ * σ / lami : ℝ) : ℂ) * μ ^ 2 * (1 - β * γ * μ) * (μ - γ)

/-- Woodford (2003), p. 593: `D(μ) = det` of the symbol `charMat`. -/
theorem det_charMat (β γ κ σ lamx lami : ℝ) (μ : ℂ) :
    (charMat β γ κ σ lamx lami μ).det = charD β γ κ σ lamx lami μ := by
  rw [Matrix.det_fin_three]
  simp only [charMat, charD, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  ring

/-- Woodford (2003), App. G.4, (G.13) (reciprocal pairing), for the inflation-inertia rule
system: `D(μ) = β³μ⁶ D(1/(βμ))`, so `μ` is a root iff `(βμ)⁻¹` is. -/
theorem charD_reciprocal {β γ κ σ lamx lami : ℝ} (hβ : β ≠ 0) {μ : ℂ} (hμ : μ ≠ 0) :
    charD β γ κ σ lamx lami μ =
      (β : ℂ) ^ 3 * μ ^ 6 * charD β γ κ σ lamx lami (((β : ℂ) * μ)⁻¹) := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  unfold charD recipC coefA0 coefA1 coefA2 coefA3
  push_cast
  field_simp
  ring

/-- Woodford (2003), App. G.4, (G.13): roots of `D` pair as `μ ↔ (βμ)⁻¹`. -/
theorem charD_root_pair {β γ κ σ lamx lami : ℝ} (hβ : β ≠ 0) {μ : ℂ} (hμ : μ ≠ 0)
    (h : charD β γ κ σ lamx lami μ = 0) : charD β γ κ σ lamx lami (((β : ℂ) * μ)⁻¹) = 0 := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  rw [charD_reciprocal hβ hμ] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 (mul_ne_zero (pow_ne_zero _ hβc) (pow_ne_zero _ hμ))
  · exact h1

/-- Woodford (2003), App. G.4 (no root on the annulus boundary): `D(1) = κσ(κσ/β +
(κσ/λᵢ)(1 − βγ)(1 − γ)) > 0` under the standing assumptions (`λᵢ > 0`). -/
theorem charD_one {β γ κ σ lamx lami : ℝ} (hβ : β ≠ 0) :
    charD β γ κ σ lamx lami 1 =
      ((κ * σ * (κ * σ / β + κ * σ / lami * (1 - β * γ) * (1 - γ)) : ℝ) : ℂ) := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  unfold charD recipC coefA0 coefA1 coefA2 coefA3
  push_cast
  field_simp
  ring

/-- Woodford (2003), App. G.4: `D(1) ≠ 0` and `D(β⁻¹) ≠ 0`, i.e. neither real boundary point of
the annulus `1 ≤ |μ| ≤ β⁻¹` is a root (standing assumptions, `λᵢ > 0`). -/
theorem charD_one_ne_zero {β γ κ σ lamx lami : ℝ} (h : Standing β γ κ σ) (hli : 0 < lami) :
    charD β γ κ σ lamx lami 1 ≠ 0 ∧ charD β γ κ σ lamx lami ((β : ℂ)⁻¹) ≠ 0 := by
  have hβ := h.beta_pos
  have hks := h.kappa_sigma_pos
  have hpos : 0 < κ * σ * (κ * σ / β + κ * σ / lami * (1 - β * γ) * (1 - γ)) := by
    have h1 : 0 ≤ 1 - β * γ := by nlinarith [h.beta_lt_one, h.gamma_le_one, h.gamma_pos]
    have h2 : 0 ≤ 1 - γ := by linarith [h.gamma_le_one]
    have : 0 ≤ κ * σ / lami * (1 - β * γ) * (1 - γ) := by positivity
    have : 0 < κ * σ / β := by positivity
    positivity
  have hD1 : charD β γ κ σ lamx lami 1 ≠ 0 := by
    rw [charD_one hβ.ne']
    exact_mod_cast hpos.ne'
  refine ⟨hD1, fun h0 => hD1 ?_⟩
  have := charD_root_pair (lamx := lamx) (lami := lami) (κ := κ) (σ := σ) (γ := γ) hβ.ne'
    (inv_ne_zero (by exact_mod_cast hβ.ne')) h0
  rwa [mul_inv_cancel₀ (by exact_mod_cast hβ.ne'), inv_one] at this

end Woodford.OptimalPolicyRules.InflationInertiaRules
