/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.Noninertial
import GainsFromCommitment.SecondOrderRE
import GainsFromCommitment.ExpectationsFiniteTree

/-!
# The optimal state-contingent instrument path as a policy rule

Woodford (2003), *Interest and Prices*, Chapter 7, §4 (pp. 517–521).

## Setting

The policy problem of Prop. 7.6 (loss (1.2), cost-push shocks (2.1)) with an AR(1) disturbance
(2.18). `μ₁ < 1 < μ₂` are the roots of `βμ² − (1 + β + κ²/λ)μ + 1 = 0` (`mu1`, `mu2`,
`mu_facts`). Dates `t ≥ 0` are the dates from `t₀ = 0` on, at which the expectation system acts;
the disturbances before `t₀` enter only through their (bounded, date-0-known) history
`hist j = u_{−1−j}` (`histU`).

## Main results

* (4.1) from (2.10): with AR(1) forecasts the double sums of (2.10) collapse,
  `∑_j μ₂^{−j−1} ρʲ = 1/(μ₂ − ρ)` (`hasSum_mu2_rho`, `eq_4_1_of_2_10`).
* The (4.1) inflation path `piPath`, with the output gap `xPath` obtained from (2.1), satisfies
  (2.1) (`piPath_AS`) and the timeless target criterion (5.1) `π_t + (λ/κ)(x_t − x_{t−1}) = 0`
  (`piPath_target`); both are bounded and adapted (`paths_bdd_adapted`). The history sums satisfy
  `S_{t+1} = u_t + μ₁ S_t` (`histSum_succ`, `mu1_histSum`, `tsum_histU_eq`).
* **Proposition 7.14, corrected** (survey E12): the interest rate satisfying (2.23) along this
  equilibrium is
  `i_t = rⁿ_t + (1 − κ/(λσ)) [(μ₁ + ρ − 1) u_t − (1 − μ₁) ∑_{k≥1} μ₁ᵏ u_{t−k}] / (β(μ₂ − ρ))`
  (`prop_7_14`); the printed (4.2), whose sum starts at `k = 0`, differs from it by
  `(1 − κ/(λσ))(1 − μ₁) u_t/(β(μ₂ − ρ))` and so is wrong whenever `κ ≠ λσ` and `u_t ≠ 0`
  (`e12_printed_sub`, `e12_printed_ne`, `e12_printed_not_IS`).
* p. 519: under an exogenous interest-rate path the model is a forward system whose matrix fails
  the Schur–Cohn condition (`exoM_not_schurStable`), so the optimal equilibrium is one of a
  continuum of bounded adapted equilibria with the same interest-rate path (`p519_continuum`,
  restating Ch. 4, Prop. 4.2; for the optimal path (4.2) itself, `p519_optimal`); every bounded
  adapted martingale-difference process `ξ` drives a stochastic sunspot equilibrium, injectively
  in `ξ` and different from the fundamental one iff `ξ ≠ 0` (`p519_sunspot`), and such `ξ` exist
  under genuine uncertainty (`p519_sunspot_coin`). Least-squares learnability is not formalised.
* (4.3): composite disturbances `u_t = ∑_j ∑_k ψ_{jk} ε^j_{t−k}` are bounded for absolutely
  summable weights (`compositeShock_bdd`), and the AR(1) process (2.18) is the case of one type with
  `ψ_k = ρᵏ` (`ar1_as_composite`).
-/

namespace Woodford.GainsFromCommitment.InstrumentPath

open Filter Topology
open Noninertial (AS IS)
open Sequences (summable_disc)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The roots `μ₁ < 1 < μ₂` of (1.11) -/

/-- Woodford (2003), (1.11), p. 472: the smaller root `μ₁` of `βμ² − (1 + β + κ²/λ)μ + 1 = 0`,
the shared `SecondOrderRE.mu1` with `c = κ²/λ`. -/
noncomputable def mu1 (β κ lam : ℝ) : ℝ := SecondOrderRE.mu1 β (κ ^ 2 / lam)

/-- Woodford (2003), (1.11), p. 472: the larger root `μ₂`, the shared `SecondOrderRE.mu2` with
`c = κ²/λ`. -/
noncomputable def mu2 (β κ lam : ℝ) : ℝ := SecondOrderRE.mu2 β (κ ^ 2 / lam)

/-- Woodford (2003), (1.11), p. 472 ("two real roots `0 < μ₁ < 1 < μ₂`"): for `0 < β`,
`κ, λ > 0`, `β(μ₁ + μ₂) = 1 + β + κ²/λ`, `β μ₁ μ₂ = 1`, and `0 < μ₁ < 1 < μ₂` (the shared
`SecondOrderRE` root facts). -/
theorem mu_facts {β κ lam : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) :
    β * (mu1 β κ lam + mu2 β κ lam) = 1 + β + κ ^ 2 / lam ∧
      β * (mu1 β κ lam * mu2 β κ lam) = 1 ∧ 0 < mu1 β κ lam ∧ mu1 β κ lam < 1 ∧
      1 < mu2 β κ lam := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  exact ⟨SecondOrderRE.beta_mul_sum hβ0, SecondOrderRE.beta_mul_prod hβ0 hc,
    SecondOrderRE.mu1_pos hβ0 hc, SecondOrderRE.mu1_lt_one hβ0 hc, SecondOrderRE.one_lt_mu2 hβ0 hc⟩

/-! ### (4.1) from (2.10) under AR(1) disturbances -/

/-- Woodford (2003), p. 518 (substituting (2.18) into (2.10)): for `|ρ| < μ₂`,
`∑_{j≥0} μ₂^{−j−1} ρʲ = 1/(μ₂ − ρ)`. -/
theorem hasSum_mu2_rho {m ρ : ℝ} (hm : 0 < m) (hρ : |ρ| < m) :
    HasSum (fun j : ℕ => (m ^ (j + 1))⁻¹ * ρ ^ j) (1 / (m - ρ)) := by
  have hq : ‖ρ / m‖ < 1 := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hm, div_lt_one hm]; exact hρ
  have hg := (hasSum_geometric_of_norm_lt_one hq).mul_left (1 / m)
  have hmρ : m - ρ ≠ 0 := by have := (abs_lt.mp hρ).2; linarith
  convert hg using 1
  · funext j
    rw [div_pow, pow_succ]
    field_simp
  · field_simp

/-- Woodford (2003), p. 518, (2.10) ⇒ (4.1): when every forecast in (2.10) is the AR(1) forecast
`E_s u_{s+j} = ρʲ u_s` (s = t and s = t − k), the two series of (2.10),
`β⁻¹ ∑_j μ₂^{−j−1} ρʲ u_t − β⁻¹(1 − μ₁) ∑_{k≥1} μ₁^{k−1} ∑_j μ₂^{−j−1} ρʲ u_{t−k}`, sum to
`[u_t − (1 − μ₁) ∑_{k≥1} μ₁^{k−1} u_{t−k}]/(β(μ₂ − ρ))`, eq. (4.1). Here `h k = u_{t−1−k}` is any
bounded history. -/
theorem eq_4_1_of_2_10 {β m1 m2 ρ : ℝ} (hβ : β ≠ 0) (hm2 : 0 < m2) (hρ : |ρ| < m2) (ut : ℝ)
    (h : ℕ → ℝ) :
    β⁻¹ * (∑' j : ℕ, (m2 ^ (j + 1))⁻¹ * (ρ ^ j * ut)) -
        β⁻¹ * (1 - m1) * ∑' k : ℕ, m1 ^ k * ∑' j : ℕ, (m2 ^ (j + 1))⁻¹ * (ρ ^ j * h k) =
      (ut - (1 - m1) * ∑' k : ℕ, m1 ^ k * h k) / (β * (m2 - ρ)) := by
  have hS := (hasSum_mu2_rho hm2 hρ).tsum_eq
  have hmρ : m2 - ρ ≠ 0 := by have := (abs_lt.mp hρ).2; linarith
  have e1 : ∀ a : ℝ, (∑' j : ℕ, (m2 ^ (j + 1))⁻¹ * (ρ ^ j * a)) = a / (m2 - ρ) := by
    intro a
    have : (fun j : ℕ => (m2 ^ (j + 1))⁻¹ * (ρ ^ j * a)) =
        fun j => ((m2 ^ (j + 1))⁻¹ * ρ ^ j) * a := by funext j; ring
    rw [this, tsum_mul_right, hS]
    ring
  simp only [e1]
  rw [show (∑' k : ℕ, m1 ^ k * (h k / (m2 - ρ))) = (∑' k : ℕ, m1 ^ k * h k) / (m2 - ρ) by
    rw [← tsum_div_const]; exact tsum_congr fun k => by ring]
  field_simp

/-! ### The timelessly optimal paths under AR(1) shocks -/

/-- Woodford (2003), p. 518: the disturbance history at date `t`, `u_{t−k}`: for `k ≤ t` it is
`u_{t−k}`; earlier values come from the pre-`t₀` history `hist j = u_{−1−j}`. -/
noncomputable def histU (u hist : ℕ → Ω → ℝ) (t k : ℕ) : Ω → ℝ :=
  if k ≤ t then u (t - k) else hist (k - t - 1)

/-- Woodford (2003), p. 518: the geometrically weighted history
`S_t = ∑_{k≥1} μ₁^{k−1} u_{t−k} = ∑_{j≥0} μ₁ʲ u_{t−1−j}`. -/
noncomputable def histSum (m1 : ℝ) (u hist : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k : ℕ, m1 ^ k * histU u hist t (k + 1) ω

/-- Woodford (2003), p. 518 (tool): the history is bounded by the bounds of `u` and `hist`. -/
theorem histU_bdd {u hist : ℕ → Ω → ℝ} {M : ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hh : ∀ j ω, |hist j ω| ≤ M) (t k : ℕ) (ω : Ω) : |histU u hist t k ω| ≤ M := by
  unfold histU
  split_ifs
  · exact hu _ ω
  · exact hh _ ω

/-- Woodford (2003), p. 518 (the recursion behind (4.1)–(4.2)):
`S_{t+1} = u_t + μ₁ S_t`, i.e. `∑_{k≥0} μ₁ᵏ u_{t−k} = u_t + μ₁ ∑_{k≥1} μ₁^{k−1} u_{t−k}`. -/
theorem histSum_succ {m1 : ℝ} (hm0 : 0 ≤ m1) (hm1 : m1 < 1) {u hist : ℕ → Ω → ℝ} {M : ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hh : ∀ j ω, |hist j ω| ≤ M) (t : ℕ) :
    histSum m1 u hist (t + 1) = u t + m1 • histSum m1 u hist t := by
  funext ω
  have hshift : ∀ k, histU u hist (t + 1) (k + 1) = histU u hist t k := by
    intro k
    unfold histU
    by_cases hk : k ≤ t
    · simp only [show k + 1 ≤ t + 1 by omega, hk, ↓reduceIte]; congr 1; omega
    · simp only [show ¬ k + 1 ≤ t + 1 by omega, hk, ↓reduceIte]; congr 1; omega
  have hsum : Summable (fun k : ℕ => m1 ^ k * histU u hist t k ω) :=
    summable_disc hm0 hm1 (fun k => histU_bdd hu hh t k ω)
  have h0 : histU u hist t 0 ω = u t ω := by simp [histU]
  calc histSum m1 u hist (t + 1) ω = ∑' k : ℕ, m1 ^ k * histU u hist t k ω := by
        simp only [histSum, hshift]
    _ = m1 ^ 0 * histU u hist t 0 ω + ∑' k : ℕ, m1 ^ (k + 1) * histU u hist t (k + 1) ω :=
        hsum.tsum_eq_zero_add
    _ = u t ω + m1 * ∑' k : ℕ, m1 ^ k * histU u hist t (k + 1) ω := by
        rw [h0, pow_zero, one_mul, ← tsum_mul_left]
        congr 1
        exact tsum_congr fun k => by ring
    _ = (u t + m1 • histSum m1 u hist t) ω := by
        simp only [histSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), p. 518 (tool): `|S_t| ≤ M/(1 − μ₁)`. -/
theorem histSum_bdd {m1 : ℝ} (hm0 : 0 ≤ m1) (hm1 : m1 < 1) {u hist : ℕ → Ω → ℝ} {M : ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hh : ∀ j ω, |hist j ω| ≤ M) (t : ℕ) (ω : Ω) :
    |histSum m1 u hist t ω| ≤ M / (1 - m1) := by
  have hg : HasSum (fun k : ℕ => m1 ^ k * M) (M / (1 - m1)) := by
    have := (hasSum_geometric_of_lt_one hm0 hm1).mul_right M
    rwa [← div_eq_inv_mul] at this
  have := tsum_of_norm_bounded hg (f := fun k : ℕ => m1 ^ k * histU u hist t (k + 1) ω)
    (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hm0 k)]
      exact mul_le_mul_of_nonneg_left (histU_bdd hu hh t (k + 1) ω) (pow_nonneg hm0 k))
  rw [Real.norm_eq_abs] at this
  exact this

/-- Woodford (2003), p. 518 (tool): `S_t` is known at date `t` when `u` is adapted and the
pre-`t₀` history is known at date 0. -/
theorem histSum_adapted {m1 : ℝ} (hm0 : 0 ≤ m1) (hm1 : m1 < 1) {u hist : ℕ → Ω → ℝ} {M : ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hh : ∀ j ω, |hist j ω| ≤ M) (hua : 𝔼.Adapted u)
    (hha : ∀ j, 𝔼.E 0 (hist j) = hist j) : 𝔼.Adapted (histSum m1 u hist) := by
  intro t
  induction t with
  | zero =>
    funext ω
    have hb : ∀ k ω', |m1 ^ k * histU u hist 0 (k + 1) ω'| ≤ m1 ^ k * M := by
      intro k ω'
      rw [abs_mul, abs_of_nonneg (pow_nonneg hm0 k)]
      exact mul_le_mul_of_nonneg_left (histU_bdd hu hh 0 (k + 1) ω') (pow_nonneg hm0 k)
    rw [show histSum m1 u hist 0 = fun ω' => ∑' k : ℕ, m1 ^ k * histU u hist 0 (k + 1) ω' from
      rfl, 𝔼.E_tsum hm0 hm1 hb 0 ω]
    refine tsum_congr fun k => ?_
    have : (fun ω' => m1 ^ k * histU u hist 0 (k + 1) ω') = m1 ^ k • hist k := by
      funext ω'; simp [histU]
    rw [this, map_smul, hha k]
    simp [histU]
  | succ t ih =>
    have h1 : 𝔼.E (t + 1) (u t) = u t := by
      conv_lhs => rw [← hua t]
      rw [𝔼.known (Nat.le_succ t), hua t]
    have h2 : 𝔼.E (t + 1) (histSum m1 u hist t) = histSum m1 u hist t := by
      conv_lhs => rw [← ih]
      rw [𝔼.known (Nat.le_succ t), ih]
    rw [histSum_succ hm0 hm1 hu hh t, map_add, map_smul, h1, h2]


/-- Woodford (2003), eq. (4.1), p. 518: the timelessly optimal inflation path under AR(1)
cost-push shocks, `π_t = [u_t − (1 − μ₁) ∑_{k≥1} μ₁^{k−1} u_{t−k}]/(β(μ₂ − ρ))`. -/
noncomputable def piPath (β κ lam ρ : ℝ) (u hist : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (u t ω - (1 - mu1 β κ lam) * histSum (mu1 β κ lam) u hist t ω) /
    (β * (mu2 β κ lam - ρ))

/-- Woodford (2003), p. 518 ("I may substitute this in turn into (2.1) to obtain a similar solution
for `x_t`"): `x_t = −(κ/λ) ∑_{k≥0} μ₁ᵏ u_{t−k}/(β(μ₂ − ρ))`. -/
noncomputable def xPath (β κ lam ρ : ℝ) (u hist : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => -(κ / lam) * histSum (mu1 β κ lam) u hist (t + 1) ω / (β * (mu2 β κ lam - ρ))

/-- Woodford (2003), eq. (4.2) corrected (survey E12), p. 518: the interest rate
`i_t = rⁿ_t + (1 − κ/(λσ)) [(μ₁ + ρ − 1) u_t − (1 − μ₁) ∑_{k≥1} μ₁ᵏ u_{t−k}]/(β(μ₂ − ρ))`. -/
noncomputable def iPath (β κ lam σ ρ : ℝ) (u hist rn : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => rn t ω + (1 - κ / (lam * σ)) * ((mu1 β κ lam + ρ - 1) * u t ω -
    (1 - mu1 β κ lam) * (mu1 β κ lam * histSum (mu1 β κ lam) u hist t ω)) /
      (β * (mu2 β κ lam - ρ))

/-- Woodford (2003), eq. (4.2) as printed, p. 518 (sum from `k = 0`): `i_t = rⁿ_t +
(1 − κ/(λσ)) {(μ₁ + ρ − 1)u_t/(β(μ₂ − ρ)) − (1 − μ₁)/(β(μ₂ − ρ)) ∑_{k≥0} μ₁ᵏ u_{t−k}}`. -/
noncomputable def iPrinted (β κ lam σ ρ : ℝ) (u hist rn : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ω => rn t ω + (1 - κ / (lam * σ)) * ((mu1 β κ lam + ρ - 1) / (β * (mu2 β κ lam - ρ)) *
    u t ω - (1 - mu1 β κ lam) / (β * (mu2 β κ lam - ρ)) *
      ∑' k : ℕ, mu1 β κ lam ^ k * histU u hist t k ω)

/-- Woodford (2003), p. 518: `μ₁ S_t = ∑_{k≥1} μ₁ᵏ u_{t−k}`, the sum in the corrected (4.2). -/
theorem mu1_histSum (m1 : ℝ) (u hist : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    m1 * histSum m1 u hist t ω = ∑' k : ℕ, m1 ^ (k + 1) * histU u hist t (k + 1) ω := by
  unfold histSum
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by ring

/-- Woodford (2003), p. 518 (tool): `∑_{k≥0} μ₁ᵏ u_{t−k} = S_{t+1}`, the sum in the printed
(4.2). -/
theorem tsum_histU_eq (m1 : ℝ) (u hist : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    ∑' k : ℕ, m1 ^ k * histU u hist t k ω = histSum m1 u hist (t + 1) ω := by
  unfold histSum
  refine tsum_congr fun k => ?_
  congr 1
  unfold histU
  by_cases hk : k ≤ t
  · simp only [show k + 1 ≤ t + 1 by omega, hk, ↓reduceIte]; congr 1; omega
  · simp only [show ¬ k + 1 ≤ t + 1 by omega, hk, ↓reduceIte]; congr 1; omega

/-- Woodford (2003), p. 518 (tool): `S_{t+1}` is known at date `t`. -/
theorem histSum_succ_known {m1 : ℝ} (hm0 : 0 ≤ m1) (hm1 : m1 < 1) {u hist : ℕ → Ω → ℝ} {M : ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hh : ∀ j ω, |hist j ω| ≤ M) (hua : 𝔼.Adapted u)
    (hha : ∀ j, 𝔼.E 0 (hist j) = hist j) (t : ℕ) :
    𝔼.E t (histSum m1 u hist (t + 1)) = histSum m1 u hist (t + 1) := by
  rw [histSum_succ hm0 hm1 hu hh t, map_add, map_smul, hua t,
    histSum_adapted 𝔼 hm0 hm1 hu hh hua hha t]

/-- Woodford (2003), p. 518: the inflation forecast along (4.1),
`E_t π_{t+1} = (ρ u_t − (1 − μ₁) S_{t+1})/(β(μ₂ − ρ))`. -/
theorem E_piPath {β κ lam ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    {u hist : ℕ → Ω → ℝ} {M : ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : ∀ t ω, |u t ω| ≤ M)
    (hh : ∀ j ω, |hist j ω| ≤ M) (hha : ∀ j, 𝔼.E 0 (hist j) = hist j) (t : ℕ) :
    𝔼.E t (piPath β κ lam ρ u hist (t + 1)) = fun ω => (ρ * u t ω - (1 - mu1 β κ lam) *
      histSum (mu1 β κ lam) u hist (t + 1) ω) / (β * (mu2 β κ lam - ρ)) := by
  obtain ⟨-, -, h1pos, h1lt, -⟩ := mu_facts hβ0 hκ hlam
  have e : piPath β κ lam ρ u hist (t + 1) = (1 / (β * (mu2 β κ lam - ρ))) •
      (u (t + 1) - (1 - mu1 β κ lam) • histSum (mu1 β κ lam) u hist (t + 1)) := by
    funext ω; simp only [piPath, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [e, map_smul, map_sub, map_smul, hu.2 t,
    histSum_succ_known 𝔼 h1pos.le h1lt hub hh hu.1 hha t]
  funext ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 518: the output-gap forecast,
`E_t x_{t+1} = −(κ/λ)(ρ u_t + μ₁ S_{t+1})/(β(μ₂ − ρ))`. -/
theorem E_xPath {β κ lam ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    {u hist : ℕ → Ω → ℝ} {M : ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : ∀ t ω, |u t ω| ≤ M)
    (hh : ∀ j ω, |hist j ω| ≤ M) (hha : ∀ j, 𝔼.E 0 (hist j) = hist j) (t : ℕ) :
    𝔼.E t (xPath β κ lam ρ u hist (t + 1)) = fun ω => -(κ / lam) * (ρ * u t ω +
      mu1 β κ lam * histSum (mu1 β κ lam) u hist (t + 1) ω) / (β * (mu2 β κ lam - ρ)) := by
  obtain ⟨-, -, h1pos, h1lt, -⟩ := mu_facts hβ0 hκ hlam
  have e : xPath β κ lam ρ u hist (t + 1) = (-(κ / lam) / (β * (mu2 β κ lam - ρ))) •
      (u (t + 1) + mu1 β κ lam • histSum (mu1 β κ lam) u hist (t + 1)) := by
    rw [← histSum_succ h1pos.le h1lt hub hh (t + 1)]
    funext ω; simp only [xPath, Pi.smul_apply, smul_eq_mul]; ring
  rw [e, map_smul, map_add, map_smul, hu.2 t,
    histSum_succ_known 𝔼 h1pos.le h1lt hub hh hu.1 hha t]
  funext ω
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 518: along (4.1) with the output gap `xPath`, the aggregate-supply
relation (2.1) holds at every date (so `xPath` is the gap obtained by substituting (4.1) into
(2.1)). -/
theorem piPath_AS {β κ lam ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (hρ : ρ < 1) {u hist : ℕ → Ω → ℝ} {M : ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : ∀ t ω, |u t ω| ≤ M)
    (hh : ∀ j ω, |hist j ω| ≤ M) (hha : ∀ j, 𝔼.E 0 (hist j) = hist j) :
    AS 𝔼 β κ (piPath β κ lam ρ u hist) (xPath β κ lam ρ u hist) u := by
  obtain ⟨hsum, hprod, h1pos, h1lt, h2⟩ := mu_facts hβ0 hκ hlam
  intro t
  rw [E_piPath 𝔼 hβ0 hκ hlam hu hub hh hha t]
  funext ω
  simp only [piPath, xPath, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hS := congrFun (histSum_succ h1pos.le h1lt hub hh t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hS
  rw [hS]
  set m1 := mu1 β κ lam
  set m2 := mu2 β κ lam
  set S := histSum m1 u hist t ω
  have hsum' : lam * (β * (m1 + m2)) = lam * (1 + β) + κ ^ 2 := by
    rw [hsum]; field_simp
  have hmρ : m2 - ρ ≠ 0 := by linarith
  have hβ' := hβ0.ne'
  field_simp
  linear_combination -(u t ω + m1 * S) * hsum' + lam * S * hprod

/-- Woodford (2003), eq. (5.1), p. 522 (the timeless target criterion, characterising the
equilibrium of Props. 7.6–7.7 and 7.15): along (4.1) and `xPath`,
`π_{t+1} + (λ/κ)(x_{t+1} − x_t) = 0` for every `t ≥ 0`, and at `t₀ = 0` with the lagged gap
`x_{−1} = −(κ/λ) S₀/(β(μ₂ − ρ))` implied by the shock history. -/
theorem piPath_target {β κ lam ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ : ρ < 1) {u hist : ℕ → Ω → ℝ} {M : ℝ} (hub : ∀ t ω, |u t ω| ≤ M)
    (hh : ∀ j ω, |hist j ω| ≤ M) (t : ℕ) :
    (∀ ω, piPath β κ lam ρ u hist (t + 1) ω + lam / κ *
      (xPath β κ lam ρ u hist (t + 1) ω - xPath β κ lam ρ u hist t ω) = 0) ∧
    ∀ ω, piPath β κ lam ρ u hist 0 ω + lam / κ * (xPath β κ lam ρ u hist 0 ω -
      (-(κ / lam) * histSum (mu1 β κ lam) u hist 0 ω / (β * (mu2 β κ lam - ρ)))) = 0 := by
  obtain ⟨-, -, h1pos, h1lt, h2⟩ := mu_facts hβ0 hκ hlam
  have hmρ : mu2 β κ lam - ρ ≠ 0 := by linarith
  have hβ' := hβ0.ne'
  have hκ' := hκ.ne'
  have hl' := hlam.ne'
  refine ⟨fun ω => ?_, fun ω => ?_⟩
  · have hS := congrFun (histSum_succ h1pos.le h1lt hub hh (t + 1)) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hS
    simp only [piPath, xPath]
    rw [hS]
    field_simp
    ring
  · have hS := congrFun (histSum_succ h1pos.le h1lt hub hh 0) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hS
    simp only [piPath, xPath]
    rw [hS]
    field_simp
    ring

/-- Woodford (2003), p. 518: the paths (4.1) and `xPath` are bounded and adapted (for a bounded
AR(1) disturbance and a bounded, date-0-known history). -/
theorem paths_bdd_adapted {β κ lam ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ : ρ < 1) {u hist : ℕ → Ω → ℝ} {M : ℝ} (hua : 𝔼.Adapted u)
    (hub : ∀ t ω, |u t ω| ≤ M) (hh : ∀ j ω, |hist j ω| ≤ M)
    (hha : ∀ j, 𝔼.E 0 (hist j) = hist j) :
    BoundedProc (piPath β κ lam ρ u hist) ∧ 𝔼.Adapted (piPath β κ lam ρ u hist) ∧
      BoundedProc (xPath β κ lam ρ u hist) ∧ 𝔼.Adapted (xPath β κ lam ρ u hist) := by
  obtain ⟨-, -, h1pos, h1lt, h2⟩ := mu_facts hβ0 hκ hlam
  have hc : 0 < β * (mu2 β κ lam - ρ) := mul_pos hβ0 (by linarith)
  have hSb := histSum_bdd h1pos.le h1lt hub hh
  have hSa := histSum_adapted 𝔼 h1pos.le h1lt hub hh hua hha
  have h1 : 0 < 1 - mu1 β κ lam := by linarith
  refine ⟨⟨2 * M / (β * (mu2 β κ lam - ρ)), fun t ω => ?_⟩, fun t => ?_,
    ⟨κ / lam * (M / (1 - mu1 β κ lam)) / (β * (mu2 β κ lam - ρ)), fun t ω => ?_⟩, fun t => ?_⟩
  · have hM : 0 ≤ M := (abs_nonneg _).trans (hub t ω)
    simp only [piPath]
    rw [abs_div, abs_of_pos hc]
    gcongr
    calc |u t ω - (1 - mu1 β κ lam) * histSum (mu1 β κ lam) u hist t ω|
        ≤ |u t ω| + (1 - mu1 β κ lam) * |histSum (mu1 β κ lam) u hist t ω| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_of_pos h1]
      _ ≤ M + (1 - mu1 β κ lam) * (M / (1 - mu1 β κ lam)) := by
          gcongr
          · exact hub t ω
          · exact hSb t ω
      _ = 2 * M := by field_simp; ring
  · have e : piPath β κ lam ρ u hist t = (1 / (β * (mu2 β κ lam - ρ))) •
        (u t - (1 - mu1 β κ lam) • histSum (mu1 β κ lam) u hist t) := by
      funext ω; simp only [piPath, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    rw [e, map_smul, map_sub, map_smul, hua t, hSa t]
  · simp only [xPath]
    rw [abs_div, abs_of_pos hc, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < κ / lam)]
    gcongr
    exact hSb (t + 1) ω
  · have e : xPath β κ lam ρ u hist t = (-(κ / lam) / (β * (mu2 β κ lam - ρ))) •
        histSum (mu1 β κ lam) u hist (t + 1) := by
      funext ω; simp only [xPath, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, map_smul, histSum_succ_known 𝔼 h1pos.le h1lt hub hh hua hha t]

/-- **Proposition 7.14, corrected** (Woodford (2003), p. 518; survey E12): in the timelessly
optimal equilibrium under AR(1) cost-push shocks — inflation (4.1), the output gap from (2.1) —
an interest-rate process satisfies the IS relation (2.23) (σ > 0) iff it is
`i_t = rⁿ_t + (1 − κ/(λσ)) [(μ₁ + ρ − 1) u_t − (1 − μ₁) ∑_{k≥1} μ₁ᵏ u_{t−k}]/(β(μ₂ − ρ))`. -/
theorem prop_7_14 {β κ lam σ ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hlam : 0 < lam) (hσ : 0 < σ) (hρ : ρ < 1) {u hist : ℕ → Ω → ℝ} {M : ℝ}
    (hu : 𝔼.IsAR1 ρ u) (hub : ∀ t ω, |u t ω| ≤ M) (hh : ∀ j ω, |hist j ω| ≤ M)
    (hha : ∀ j, 𝔼.E 0 (hist j) = hist j) (rn i : ℕ → Ω → ℝ) :
    IS 𝔼 σ (piPath β κ lam ρ u hist) (xPath β κ lam ρ u hist) i rn ↔
      i = iPath β κ lam σ ρ u hist rn := by
  obtain ⟨-, -, h1pos, h1lt, h2⟩ := mu_facts hβ0 hκ hlam
  have hmρ : mu2 β κ lam - ρ ≠ 0 := by linarith
  have hβ' := hβ0.ne'
  have hκ' := hκ.ne'
  have hl' := hlam.ne'
  have hσ' := hσ.ne'
  have key : ∀ t ω, (xPath β κ lam ρ u hist t ω =
      𝔼.E t (xPath β κ lam ρ u hist (t + 1)) ω -
        σ * (i t ω - 𝔼.E t (piPath β κ lam ρ u hist (t + 1)) ω - rn t ω)) ↔
      i t ω = iPath β κ lam σ ρ u hist rn t ω := by
    intro t ω
    rw [E_xPath 𝔼 hβ0 hκ hlam hu hub hh hha t, E_piPath 𝔼 hβ0 hκ hlam hu hub hh hha t]
    have hS := congrFun (histSum_succ h1pos.le h1lt hub hh t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hS
    simp only [xPath, iPath]
    rw [hS]
    constructor
    · intro h
      field_simp at h ⊢
      linear_combination h
    · intro h
      rw [h]
      field_simp
      ring
  constructor
  · intro h
    funext t ω
    exact (key t ω).mp (by
      have := congrFun (h t) ω
      simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this)
  · rintro rfl t
    funext ω
    have := (key t ω).mpr rfl
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this

/-- Survey E12 (Woodford (2003), p. 518, (4.2), confirmed): the printed formula, whose sum runs
from `k = 0`, differs from the correct interest rate by
`−(1 − κ/(λσ))(1 − μ₁) u_t/(β(μ₂ − ρ))` (the `k = 0` term is counted twice). -/
theorem e12_printed_sub {β κ lam σ ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ : ρ < 1) {u hist : ℕ → Ω → ℝ} {M : ℝ} (hub : ∀ t ω, |u t ω| ≤ M)
    (hh : ∀ j ω, |hist j ω| ≤ M) (rn : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    iPrinted β κ lam σ ρ u hist rn t ω - iPath β κ lam σ ρ u hist rn t ω =
      -((1 - κ / (lam * σ)) * (1 - mu1 β κ lam) * u t ω / (β * (mu2 β κ lam - ρ))) := by
  obtain ⟨-, -, h1pos, h1lt, h2⟩ := mu_facts hβ0 hκ hlam
  have hmρ : mu2 β κ lam - ρ ≠ 0 := by linarith
  have hβ' := hβ0.ne'
  have hS := congrFun (histSum_succ h1pos.le h1lt hub hh t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hS
  simp only [iPrinted, iPath]
  rw [tsum_histU_eq, hS]
  field_simp
  ring

/-- Survey E12 (confirmed): whenever `κ ≠ λσ` and `u_t ≠ 0` the printed (4.2) gives a different
interest rate from the correct one. -/
theorem e12_printed_ne {β κ lam σ ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ : ρ < 1) (hne : κ ≠ lam * σ) {u hist : ℕ → Ω → ℝ} {M : ℝ}
    (hub : ∀ t ω, |u t ω| ≤ M) (hh : ∀ j ω, |hist j ω| ≤ M) (rn : ℕ → Ω → ℝ) {t : ℕ} {ω : Ω}
    (hu : u t ω ≠ 0) :
    iPrinted β κ lam σ ρ u hist rn t ω ≠ iPath β κ lam σ ρ u hist rn t ω := by
  obtain ⟨-, -, -, h1lt, h2⟩ := mu_facts hβ0 hκ hlam
  intro h
  have e := e12_printed_sub (σ := σ) hβ0 hκ hlam hρ hub hh rn t ω
  rw [h, sub_self] at e
  have hc : 0 < β * (mu2 β κ lam - ρ) := mul_pos hβ0 (by linarith)
  have hk : 1 - κ / (lam * σ) ≠ 0 := by
    intro h0
    have hls : lam * σ ≠ 0 := by
      intro h'; rw [h', div_zero, sub_zero] at h0; exact one_ne_zero h0
    have h1 : κ / (lam * σ) = 1 := by linarith
    exact hne ((div_eq_one_iff_eq hls).mp h1)
  have : (1 - κ / (lam * σ)) * (1 - mu1 β κ lam) * u t ω / (β * (mu2 β κ lam - ρ)) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero hk (by linarith)) hu) hc.ne'
  exact this (by linarith)

/-- Survey E12 (confirmed): in particular the printed (4.2) does not satisfy the IS relation
(2.23) along the optimal equilibrium, as soon as `κ ≠ λσ` and the disturbance is not identically
zero. -/
theorem e12_printed_not_IS {β κ lam σ ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hlam : 0 < lam) (hσ : 0 < σ) (hρ : ρ < 1) (hne : κ ≠ lam * σ) {u hist : ℕ → Ω → ℝ}
    {M : ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : ∀ t ω, |u t ω| ≤ M) (hh : ∀ j ω, |hist j ω| ≤ M)
    (hha : ∀ j, 𝔼.E 0 (hist j) = hist j) (rn : ℕ → Ω → ℝ) {t : ℕ} {ω : Ω} (hu0 : u t ω ≠ 0) :
    ¬ IS 𝔼 σ (piPath β κ lam ρ u hist) (xPath β κ lam ρ u hist)
      (iPrinted β κ lam σ ρ u hist rn) rn := by
  intro h
  have e := (prop_7_14 𝔼 hβ0 hκ hlam hσ hρ hu hub hh hha rn _).mp h
  exact e12_printed_ne hβ0 hκ hlam hρ hne hub hh rn hu0 (congrFun (congrFun e t) ω)

/-! ### p. 519: an exogenous interest-rate path implies indeterminacy -/

/-- Woodford (2003), Ch. 4, (2.5) (restated): with an exogenous interest-rate process, (2.1) and
(2.23) are the forward system `z_t = M E_t z_{t+1} + w_t` with `M = [[β + κσ, κ], [σ, 1]]`. -/
noncomputable def exoM (β κ σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![β + κ * σ, κ; σ, 1]

/-- Woodford (2003), p. 519 and Ch. 4, Prop. 4.2 (restated): `M` fails the Schur–Cohn condition
(`tr M = 1 + β + κσ ≥ 1 + det M = 1 + β` for `κσ ≥ 0`). -/
theorem exoM_not_schurStable {β κ σ : ℝ} (hκ : 0 ≤ κ) (hσ : 0 ≤ σ) :
    ¬ SchurStable (tr2 (exoM β κ σ)) (det2 (exoM β κ σ)) := by
  rintro ⟨-, h2⟩
  have ht : tr2 (exoM β κ σ) = 1 + β + κ * σ := by
    simp only [exoM, tr2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  have hd : det2 (exoM β κ σ) = β := by
    simp only [exoM, det2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  rw [ht, hd] at h2
  have := le_abs_self (1 + β + κ * σ)
  have : 0 ≤ κ * σ := mul_nonneg hκ hσ
  linarith

/-- **p. 519 — Proposition 4.2 restated** (Woodford (2003), pp. 518–519): under any exogenous
interest-rate path `i` (for example (4.2)), if `(π, x)` is a bounded adapted equilibrium of (2.1),
(2.23), then so is `(π, x) + c·s` for every real `c`, where `s` is a fixed nonzero bounded
self-fulfilling deterministic path: a continuum (indexed injectively by `ℝ`) of bounded adapted
equilibria with the same interest-rate path. -/
theorem p519_continuum [Nonempty Ω] {β κ σ : ℝ} (hκ : 0 ≤ κ) (hσ : 0 ≤ σ)
    {u rn i π x : ℕ → Ω → ℝ}
    (hA : AS 𝔼 β κ π x u) (hI : IS 𝔼 σ π x i rn) (hπb : BoundedProc π) (hxb : BoundedProc x)
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) :
    ∃ f : ℝ → (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), Function.Injective f ∧ f 0 = (π, x) ∧
      ∀ c, AS 𝔼 β κ (f c).1 (f c).2 u ∧ IS 𝔼 σ (f c).1 (f c).2 i rn ∧ BoundedProc (f c).1 ∧
        BoundedProc (f c).2 ∧ 𝔼.Adapted (f c).1 ∧ 𝔼.Adapted (f c).2 := by
  obtain ⟨s, hs, ⟨C, hC⟩, hs0⟩ := exists_bounded_homogeneous (exoM_not_schurStable (β := β) hκ hσ)
  have hcomp : ∀ t, s t 0 = (β + κ * σ) * s (t + 1) 0 + κ * s (t + 1) 1 ∧
      s t 1 = σ * s (t + 1) 0 + s (t + 1) 1 := by
    intro t
    exact ⟨by simpa [exoM, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun (hs t) 0,
      by simpa [exoM, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun (hs t) 1⟩
  obtain ⟨t0, i0, hti⟩ : ∃ t i, s t i ≠ 0 := by
    by_contra h
    push Not at h
    exact hs0 (funext fun t => funext fun i => h t i)
  obtain ⟨ω0⟩ := ‹Nonempty Ω›
  refine ⟨fun c => (fun t => π t + fun _ => c * s t 0, fun t => x t + fun _ => c * s t 1),
    fun c c' h => ?_, ?_, fun c => ⟨fun t => ?_, fun t => ?_, ?_, ?_, fun t => ?_, fun t => ?_⟩⟩
  · simp only [Prod.mk.injEq] at h
    have h0 := congrFun (congrFun h.1 t0) ω0
    have h1 := congrFun (congrFun h.2 t0) ω0
    simp only [Pi.add_apply, add_right_inj] at h0 h1
    fin_cases i0
    · exact mul_right_cancel₀ hti h0
    · exact mul_right_cancel₀ hti h1
  · simp only [zero_mul]
    ext t ω <;> simp
  · dsimp only
    rw [hA t]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, 𝔼.const]
    linear_combination c * (hcomp t).1 - c * κ * (hcomp t).2
  · dsimp only
    rw [hI t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, 𝔼.const]
    linear_combination c * (hcomp t).2
  · obtain ⟨M, hM⟩ := hπb
    exact ⟨M + |c| * C, fun t ω => (abs_add_le _ _).trans (add_le_add (hM t ω)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC t 0) (abs_nonneg _)))⟩
  · obtain ⟨M, hM⟩ := hxb
    exact ⟨M + |c| * C, fun t ω => (abs_add_le _ _).trans (add_le_add (hM t ω)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC t 1) (abs_nonneg _)))⟩
  · simp only [map_add, hπa t, 𝔼.const]
  · simp only [map_add, hxa t, 𝔼.const]

/-- Woodford (2003), pp. 518–519: if the central bank commits to the interest-rate path (4.2)
(corrected) as an exogenous process, the optimal equilibrium (4.1) is an equilibrium — and so is
a continuum of other bounded adapted processes with the same interest-rate path: the rule does not
determine the optimal equilibrium. -/
theorem p519_optimal [Nonempty Ω] {β κ lam σ ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hlam : 0 < lam) (hσ : 0 < σ) (hρ : ρ < 1) {u hist : ℕ → Ω → ℝ} {M : ℝ}
    (hu : 𝔼.IsAR1 ρ u) (hub : ∀ t ω, |u t ω| ≤ M) (hh : ∀ j ω, |hist j ω| ≤ M)
    (hha : ∀ j, 𝔼.E 0 (hist j) = hist j) (rn : ℕ → Ω → ℝ) :
    ∃ f : ℝ → (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), Function.Injective f ∧
      f 0 = (piPath β κ lam ρ u hist, xPath β κ lam ρ u hist) ∧
      ∀ c, AS 𝔼 β κ (f c).1 (f c).2 u ∧ IS 𝔼 σ (f c).1 (f c).2 (iPath β κ lam σ ρ u hist rn) rn ∧
        BoundedProc (f c).1 ∧ BoundedProc (f c).2 ∧ 𝔼.Adapted (f c).1 ∧ 𝔼.Adapted (f c).2 := by
  obtain ⟨b1, a1, b2, a2⟩ := paths_bdd_adapted 𝔼 hβ0 hκ hlam hρ hu.1 hub hh hha
  exact p519_continuum 𝔼 hκ.le hσ.le (piPath_AS 𝔼 hβ0 hκ hlam hρ hu hub hh hha)
    ((prop_7_14 𝔼 hβ0 hκ hlam hσ hρ hu hub hh hha rn _).mpr rfl) b1 b2 a1 a2

/-! ### (4.3): composite disturbances -/

/-- Woodford (2003), eq. (4.3), p. 520: a cost-push disturbance composed of `J` types of shocks,
`u_t = ∑_j ∑_{k≥0} ψ_{jk} ε^j_{t−k}` (shock histories indexed by `ℤ`). -/
noncomputable def compositeShock {J : ℕ} (ψ : Fin J → ℕ → ℝ) (ε : Fin J → ℤ → Ω → ℝ) (t : ℤ) :
    Ω → ℝ :=
  fun ω => ∑ j, ∑' k : ℕ, ψ j k * ε j (t - k) ω

/-- Woodford (2003), eq. (4.3), p. 520: with absolutely summable weights and bounded shocks the
composite disturbance is bounded, `|u_t| ≤ ∑_j (∑_k |ψ_{jk}|) M`. -/
theorem compositeShock_bdd {J : ℕ} {ψ : Fin J → ℕ → ℝ} {ε : Fin J → ℤ → Ω → ℝ} {M : ℝ}
    (hψ : ∀ j, Summable fun k => |ψ j k|) (hε : ∀ j s ω, |ε j s ω| ≤ M) (t : ℤ) (ω : Ω) :
    |compositeShock ψ ε t ω| ≤ ∑ j, (∑' k, |ψ j k|) * M := by
  unfold compositeShock
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hg : HasSum (fun k => |ψ j k| * M) ((∑' k, |ψ j k|) * M) := (hψ j).hasSum.mul_right M
  have := tsum_of_norm_bounded hg (f := fun k : ℕ => ψ j k * ε j (t - k) ω) (fun k => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hε j _ ω) (abs_nonneg _))
  rwa [Real.norm_eq_abs] at this

/-- Woodford (2003), eqs. (2.18) and (4.3): the AR(1) disturbance is the composite of a single
type with weights `ψ_k = ρᵏ` (`|ρ| < 1`, bounded innovations): `u_t = ε_t + ρ u_{t−1}`. -/
theorem ar1_as_composite {ρ M : ℝ} (hρ : |ρ| < 1) {ε : Fin 1 → ℤ → Ω → ℝ}
    (hε : ∀ j s ω, |ε j s ω| ≤ M) (t : ℤ) :
    compositeShock (fun _ k => ρ ^ k) ε t = ε 0 t + ρ • compositeShock (fun _ k => ρ ^ k) ε (t - 1)
    := by
  funext ω
  have hs : Summable fun k : ℕ => ρ ^ k * ε 0 (t - k) ω := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right M)
      (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hε 0 _ ω) (pow_nonneg (abs_nonneg ρ) k)
  simp only [compositeShock, Fin.sum_univ_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
  congr 1
  refine tsum_congr fun k => ?_
  rw [pow_succ]
  have : t - ((k + 1 : ℕ) : ℤ) = t - 1 - k := by push_cast; ring
  rw [this]
  ring


/-! ### p. 519: stochastic sunspot equilibria under an exogenous interest-rate path

Restating the martingale-difference part of Ch. 4, Prop. 4.2. With `L > 1` the unstable root of
`μ² − (1 + β + κσ)μ + β = 0` and `a = 1/L`, every bounded adapted martingale-difference process
`ξ` (`E_t ξ_{t+1} = 0`) drives the sunspot `s_{t+1} = a s_t + ξ_{t+1}`, `s₀ = ξ₀`, and
`(π + (L − 1)s, x + σ s)` is again a bounded adapted equilibrium with the same interest-rate path.
Distinct `ξ` give distinct equilibria, with no further nondegeneracy hypothesis (`ξ` is recovered
from `s`). A genuinely stochastic instance exists on the coin-flip tree (`p519_sunspot_coin`).
Least-squares learnability (p. 519, second paragraph) is not formalised. -/

/-- Woodford (2003), Ch. 4, (2.6), restated for p. 519: the larger root
`L = (1 + β + κσ + √((1 + β + κσ)² − 4β))/2` of `μ² − (1 + β + κσ)μ + β = 0`. -/
noncomputable def lamL (β κ σ : ℝ) : ℝ :=
  ((1 + β + κ * σ) + Real.sqrt ((1 + β + κ * σ) ^ 2 - 4 * β)) / 2

/-- Woodford (2003), Ch. 4, (2.6): `L` is a root and `L > 1` (for `0 < β`, `κ, σ > 0`). -/
theorem lamL_facts {β κ σ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) :
    lamL β κ σ ^ 2 - (1 + β + κ * σ) * lamL β κ σ + β = 0 ∧ 1 < lamL β κ σ := by
  have hks : 0 < κ * σ := mul_pos hκ hσ
  have hd : 0 ≤ (1 + β + κ * σ) ^ 2 - 4 * β := by nlinarith [sq_nonneg (1 - β)]
  have hss := Real.mul_self_sqrt hd
  have hs0 := Real.sqrt_nonneg ((1 + β + κ * σ) ^ 2 - 4 * β)
  unfold lamL
  constructor
  · linear_combination hss / 4
  · have : (1 - β - κ * σ) < Real.sqrt ((1 + β + κ * σ) ^ 2 - 4 * β) := by
      by_cases h : 1 - β - κ * σ < 0
      · linarith
      · push Not at h
        nlinarith
    linarith

/-- Woodford (2003), p. 519: the sunspot state `s₀ = ξ₀`, `s_{t+1} = a s_t + ξ_{t+1}`. -/
noncomputable def sunS (a : ℝ) (ξ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => ξ 0
  | t + 1 => a • sunS a ξ t + ξ (t + 1)

/-- Woodford (2003), p. 519: the sunspot state is adapted when `ξ` is. -/
theorem sunS_adapted {a : ℝ} {ξ : ℕ → Ω → ℝ} (hξ : 𝔼.Adapted ξ) : 𝔼.Adapted (sunS a ξ) := by
  intro t
  induction t with
  | zero => exact hξ 0
  | succ t ih =>
    have h1 : 𝔼.E (t + 1) (sunS a ξ t) = sunS a ξ t := by
      conv_lhs => rw [← ih]
      rw [𝔼.known (Nat.le_succ t), ih]
    simp only [sunS]
    rw [map_add, map_smul, h1, hξ (t + 1)]

/-- Woodford (2003), p. 519: for a martingale difference `ξ`, `E_t s_{t+1} = a s_t`. -/
theorem sunS_E {a : ℝ} {ξ : ℕ → Ω → ℝ} (hξ : 𝔼.Adapted ξ) (hmd : ∀ t, 𝔼.E t (ξ (t + 1)) = 0)
    (t : ℕ) : 𝔼.E t (sunS a ξ (t + 1)) = a • sunS a ξ t := by
  simp only [sunS]
  rw [map_add, map_smul, sunS_adapted 𝔼 hξ t, hmd t, add_zero]

/-- Woodford (2003), p. 519: for `0 ≤ a < 1` and `|ξ| ≤ M`, `|s_t| ≤ M/(1 − a)`. -/
theorem sunS_bdd {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {ξ : ℕ → Ω → ℝ}
    (hξ : ∀ t ω, |ξ t ω| ≤ M) (t : ℕ) (ω : Ω) : |sunS a ξ t ω| ≤ M / (1 - a) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hξ 0 ω)
  have h1 : 0 < 1 - a := by linarith
  induction t with
  | zero =>
    simp only [sunS]
    refine (hξ 0 ω).trans ?_
    rw [le_div_iff₀ h1]; nlinarith
  | succ t ih =>
    simp only [sunS, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg ha0]
    have := hξ (t + 1) ω
    calc a * |sunS a ξ t ω| + |ξ (t + 1) ω| ≤ a * (M / (1 - a)) + M := by gcongr
      _ = M / (1 - a) := by field_simp; ring

/-- Woodford (2003), p. 519: the sunspot state determines its driving process: `ξ ↦ s` is
injective. -/
theorem sunS_injective {a : ℝ} {ξ ξ' : ℕ → Ω → ℝ} (h : sunS a ξ = sunS a ξ') : ξ = ξ' := by
  funext t
  cases t with
  | zero => simpa [sunS] using congrFun h 0
  | succ t =>
    have h1 := congrFun h (t + 1)
    have h0 := congrFun h t
    simp only [sunS] at h1
    rw [h0] at h1
    exact add_left_cancel h1

/-- **p. 519 — Proposition 4.2 (sunspots) restated** (Woodford (2003), pp. 518–519): under an
exogenous interest-rate path, let `(π, x)` be a bounded adapted equilibrium of (2.1), (2.23)
(`0 < β`, `κ, σ > 0`). For every bounded adapted martingale-difference process `ξ`
(`E_t ξ_{t+1} = 0`), `(π + (L − 1)s, x + σ s)` with `s = sunS (1/L) ξ` is a bounded adapted
equilibrium with the same interest-rate path; it differs from `(π, x)` iff `ξ ≠ 0`; and distinct
`ξ` give distinct equilibria. -/
theorem p519_sunspot {β κ σ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ)
    {u rn i π x : ℕ → Ω → ℝ} (hA : AS 𝔼 β κ π x u) (hI : IS 𝔼 σ π x i rn)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) :
    let f : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) := fun ξ =>
      (fun t => π t + (lamL β κ σ - 1) • sunS (lamL β κ σ)⁻¹ ξ t,
        fun t => x t + σ • sunS (lamL β κ σ)⁻¹ ξ t)
    (∀ ξ, 𝔼.Adapted ξ → BoundedProc ξ → (∀ t, 𝔼.E t (ξ (t + 1)) = 0) →
      AS 𝔼 β κ (f ξ).1 (f ξ).2 u ∧ IS 𝔼 σ (f ξ).1 (f ξ).2 i rn ∧ BoundedProc (f ξ).1 ∧
        BoundedProc (f ξ).2 ∧ 𝔼.Adapted (f ξ).1 ∧ 𝔼.Adapted (f ξ).2 ∧
        ((f ξ).1 = π ↔ ξ = 0)) ∧
    Function.Injective f := by
  obtain ⟨hroot, hL⟩ := lamL_facts hβ0 hκ hσ
  set L := lamL β κ σ with hLdef
  intro f
  have hL0 : L ≠ 0 := by linarith
  have hLinv : L * L⁻¹ = 1 := mul_inv_cancel₀ hL0
  have hL1 : L - 1 ≠ 0 := by linarith
  have hinj1 : ∀ ξ ξ' : ℕ → Ω → ℝ, (f ξ).1 = (f ξ').1 → ξ = ξ' := by
    intro ξ ξ' h
    apply sunS_injective (a := L⁻¹)
    funext t ω
    have := congrFun (congrFun h t) ω
    simp only [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at this
    exact mul_left_cancel₀ hL1 this
  have hzero : sunS L⁻¹ (0 : ℕ → Ω → ℝ) = 0 := by
    funext t
    induction t with
    | zero => rfl
    | succ t ih => simp only [sunS, ih, smul_zero, Pi.zero_apply, add_zero]
  have hf0 : (f 0).1 = π := by
    funext t ω
    simp [f, hzero]
  refine ⟨fun ξ hξa hξb hmd => ?_, fun ξ ξ' h => hinj1 ξ ξ' (congrArg Prod.fst h)⟩
  have hE := sunS_E 𝔼 (a := L⁻¹) hξa hmd
  have hSa := sunS_adapted 𝔼 (a := L⁻¹) hξa
  obtain ⟨M, hM⟩ := hξb
  have ha0 : 0 ≤ L⁻¹ := inv_nonneg.mpr (by linarith)
  have ha1 : L⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL
  have hSb := sunS_bdd ha0 ha1 hM
  refine ⟨fun t => ?_, fun t => ?_, ?_, ?_, fun t => ?_, fun t => ?_, ⟨fun h => ?_, ?_⟩⟩
  · simp only [f]
    rw [hA t, map_add, map_smul, hE t]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (sunS L⁻¹ ξ t ω * L⁻¹) * hroot -
      sunS L⁻¹ ξ t ω * (L - 1 - κ * σ) * hLinv
  · simp only [f]
    rw [hI t, map_add, map_add, map_smul, map_smul, hE t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-σ * sunS L⁻¹ ξ t ω) * hLinv
  · obtain ⟨N, hN⟩ := hπb
    exact ⟨N + |L - 1| * (M / (1 - L⁻¹)), fun t ω => (abs_add_le _ _).trans
      (add_le_add (hN t ω) (by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hSb t ω) (abs_nonneg _)))⟩
  · obtain ⟨N, hN⟩ := hxb
    exact ⟨N + |σ| * (M / (1 - L⁻¹)), fun t ω => (abs_add_le _ _).trans
      (add_le_add (hN t ω) (by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hSb t ω) (abs_nonneg _)))⟩
  · simp only [f]; rw [map_add, map_smul, hπa t, hSa t]
  · simp only [f]; rw [map_add, map_smul, hxa t, hSa t]
  · exact hinj1 ξ 0 (h.trans hf0.symm)
  · rintro rfl
    exact hf0

/-- Woodford (2003), p. 519 ("paths in which inflation and output are affected by pure sunspot
states"): the martingale-difference hypothesis is satisfiable under genuine uncertainty. On the
coin-flip tree of `ExpectationsFiniteTree`, `ξ = coinAR1 0` is a bounded adapted martingale
difference that is not deterministic: `ξ₁` is `+1` or `−1` according to the first flip, while
`E₀ ξ₁ = 0`. -/
theorem p519_sunspot_coin :
    ExpectationsFiniteTree.coinSystem.Adapted (ExpectationsFiniteTree.coinAR1 0) ∧
      BoundedProc (ExpectationsFiniteTree.coinAR1 0) ∧
      (∀ t, ExpectationsFiniteTree.coinSystem.E t (ExpectationsFiniteTree.coinAR1 0 (t + 1)) = 0)
      ∧ ExpectationsFiniteTree.coinAR1 0 1 (true, true) ≠
        ExpectationsFiniteTree.coinAR1 0 1 (false, true) := by
  have h := ExpectationsFiniteTree.coinAR1_isAR1 0
  obtain ⟨n1, n2, -⟩ := ExpectationsFiniteTree.coinAR1_nondegenerate 0
  refine ⟨h.1, ⟨1, fun t ω => ?_⟩, fun t => by rw [h.2 t, zero_smul], by rw [n1, n2]; norm_num⟩
  cases t with
  | zero => simp [ExpectationsFiniteTree.coinAR1]
  | succ t =>
    simp only [ExpectationsFiniteTree.coinAR1, zero_mul, zero_add, ExpectationsFiniteTree.coinShock]
    split_ifs <;> simp

end Woodford.GainsFromCommitment.InstrumentPath
