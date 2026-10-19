/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.TargetingRule

/-!
# Implementation of a targeting rule

Woodford (2003), *Interest and Prices*, Chapter 7, §5.2 "Implementation of a Targeting Rule",
pp. 527–533.

The structural model is (2.1) (`VarianceFrontier.AS`) and the IS relation (2.23) (`IS`); the
equilibrium of the target criterion (5.1) is `TargetingRule.piStar`, `TargetingRule.xStar`
(Proposition 7.15). Everything holds for an arbitrary `ExpectationSystem`, with bounded adapted
disturbances `u, rⁿ` that are otherwise unrestricted.

## Main results

* Private-sector forecasts (p. 528): `forecast_pi_apply` (as printed) and `forecast_x` — the
  output-gap line carries a **minus** sign (survey E13: the printed `+` is a misprint;
  `printed_forecast_x_iff`: the printed line holds iff the forward sum vanishes;
  `printed_forecast_x_false`: it fails at every date under perfect foresight with `u ≡ 1`).
* Conditional forecasts (p. 529): `S` (`∑_{j ≥ 1} μ₂^{−j} E_t u_{t+j}`), `E_fwdU_succ`,
  `fwdU_eq_mu1`, `E_forecast_pi`, `E_forecast_x`.
* The projection identity (p. 529): `identity_529a` (`κ² + λ + β(1 − μ₁)λ = λ/μ₁`),
  `identity_529b` (`1 − μ₁ − μ₂ = −(κ² + λ)/(βλ)`), `projection_eq` (for `κ ≠ σλ`) and
  `projection_singular` (at `κ = σλ` the projected IS relation does not involve `x_t` and holds
  iff `i_t = rⁿ_t`, so the projection, and the derivation of (5.4), break down).
* (5.4): `rate54`, `eq54_iff` (equating the projection to `(λ/κ)x_{t−1}` ⟺ (5.4)),
  `eq54_equilibrium` (in the desired equilibrium (2.23) holds iff `i_t` follows (5.4), for all
  parameters), and **indeterminacy** `eq54_indeterminate`: for every parameter vector with
  `σλ < κ` a commitment to (5.4) admits a second bounded equilibrium (perfect foresight, any
  bounded shocks) — the book's "for many parameter values, it does not" (citing Evans and
  Honkapohja), proved via `cubic54_factor`, `exists_quad54_root`, `exists_homog54`.
* (5.5): `projection55`, `r55`, `eq55_iff`, `RF55`, `rf55_iff_crit` ((5.5) ∧ (2.1) ∧ (2.23) ⟺
  (5.1) ∧ (2.1) ∧ (2.23)).
* **Proposition 7.17**: `prop_7_17` (determinate equilibrium `(π*, x*, i*)`, equal to
  Proposition 7.7's paths) and `prop_7_17_timeless` (optimal from a timeless perspective).
* Long-run responses (p. 531): `psiPi`, `psiX`, `r55_long_run`, `psiPi_gt_one`
  (`Ψ_π = 1 + βκ/(σ(κ² + λ)) > 1`), `psiX_div_four` (`Ψ_x/4 = κ²/(σ(κ² + λ))`), `psiX_pos`, and
  the Taylor principle (3.9) `taylor_principle`.

**Out of scope.** The learnability claims of pp. 528 and 532–533 (E-stability of the
equilibrium under (5.4) and (5.5) with least-squares learning, after Evans and Honkapohja
(2002a) and Preston (2002b)) concern adaptive-learning dynamics with subjective expectations,
not rational-expectations equilibria; they are cited results and are not formalised here.
-/

namespace Woodford.GainsFromCommitment.Implementation

open Filter Topology TargetingRule
open SecondOrderRE (mu1 mu2 beta_mul_prod beta_mul_sum inv_beta_mul_mu2 inv_mu2 mu1_lt_one mu1_pos
  one_lt_mu2)
open Sequences (lagged lagged_zero lagged_succ)
open VarianceFrontier (AS)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The IS relation and the private-sector forecasts (p. 528) -/

/-- Woodford (2003), eq. (2.23), p. 506: the intertemporal IS relation
`x_t = E_t x_{t+1} − σ(i_t − E_t π_{t+1} − rⁿ_t)` at every date `t ≥ t₀`. -/
def IS (σ : ℝ) (rn i π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ • (i t - 𝔼.E t (π (t + 1)) - rn t)

/-- Woodford (2003), p. 528: the private sector's forecast of inflation in the equilibrium of
Proposition 7.15, `π_{t+1} = (1 − μ₁)(λ/κ) x_t + β⁻¹ ∑ⱼ μ₂^{−j−1} E_{t+1} u_{t+j+1}`. -/
theorem forecast_pi {κ lam : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0) (β : ℝ) (xm1 : Ω → ℝ)
    (u : ℕ → Ω → ℝ) (t : ℕ) :
    piStar 𝔼 β κ lam xm1 u (t + 1) = ((1 - mu1 β (κ ^ 2 / lam)) * (lam / κ)) •
      xStar 𝔼 β κ lam xm1 u t + fwdU 𝔼 β κ lam u (t + 1) := by
  rw [piStar_eq 𝔼 hκ hlam, lagged_succ]

/-- Woodford (2003), p. 528, **corrected (survey E13)**: the private sector's forecast of the
output gap is `x_{t+1} = μ₁ x_t − (κ/(βλ)) ∑ⱼ μ₂^{−j−1} E_{t+1} u_{t+j+1}` (this is (F.10) at
`t + 1`; a cost-push shock lowers the gap). The book prints `+`. -/
theorem forecast_x (β κ lam : ℝ) (xm1 : Ω → ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    xStar 𝔼 β κ lam xm1 u (t + 1) ω = mu1 β (κ ^ 2 / lam) * xStar 𝔼 β κ lam xm1 u t ω
      - κ / (β * lam) * ∑' j, (mu2 β (κ ^ 2 / lam) ^ (j + 1))⁻¹ *
        𝔼.E (t + 1) (u (t + 1 + j)) ω := by
  have h := congrFun (xStar_eq 𝔼 β κ lam xm1 u (t + 1)) ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lagged_succ] at h
  rw [h, fwdU_apply]
  field_simp

/-- Woodford (2003), p. 528, the inflation forecast in the printed form
`π_{t+1} = (1 − μ₁)(λ/κ) x_t + β⁻¹ ∑ⱼ μ₂^{−j−1} E_{t+1} u_{t+j+1}` (correct as printed). -/
theorem forecast_pi_apply {κ lam : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0) (β : ℝ) (xm1 : Ω → ℝ)
    (u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    piStar 𝔼 β κ lam xm1 u (t + 1) ω = (1 - mu1 β (κ ^ 2 / lam)) * (lam / κ) *
      xStar 𝔼 β κ lam xm1 u t ω + β⁻¹ * ∑' j, (mu2 β (κ ^ 2 / lam) ^ (j + 1))⁻¹ *
        𝔼.E (t + 1) (u (t + 1 + j)) ω := by
  rw [forecast_pi 𝔼 hκ hlam]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [fwdU_apply]

/-- Woodford (2003), p. 528, **survey E13 (sign misprint)**: the printed output-gap forecast
`x_{t+1} = μ₁ x_t + (κ/(βλ)) ∑ⱼ μ₂^{−j−1} E_{t+1} u_{t+j+1}` holds in the equilibrium of
Proposition 7.15 iff the forward sum is zero. -/
theorem printed_forecast_x_iff {κ lam : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0) (β : ℝ)
    (xm1 : Ω → ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    xStar 𝔼 β κ lam xm1 u (t + 1) =
        mu1 β (κ ^ 2 / lam) • xStar 𝔼 β κ lam xm1 u t + (κ / lam) • fwdU 𝔼 β κ lam u (t + 1) ↔
      fwdU 𝔼 β κ lam u (t + 1) = 0 := by
  rw [xStar_eq, lagged_succ]
  constructor
  · intro h
    funext ω
    have h' := congrFun h ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h' ⊢
    have : κ / lam * fwdU 𝔼 β κ lam u (t + 1) ω = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (div_ne_zero hκ hlam)
  · intro h
    rw [h]
    simp

/-- Woodford (2003), p. 528: with the constant cost-push process `u ≡ 1`, the forward sum is
`β⁻¹/(μ₂ − 1) > 0` at every date (perfect foresight). -/
theorem fwdU_one_pos {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) (t : ℕ) :
    0 < fwdU perfectForesight β κ lam (fun _ _ => 1) t () := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have h2 := one_lt_mu2 hβ hc
  have hs := ForwardSolution.hasSum_geometric_ratio (A := mu2 β (κ ^ 2 / lam)) (B := 1) 1
    (by rw [abs_one, abs_of_pos (by linarith)]; exact h2)
  rw [fwdU_apply]
  have e : (fun j : ℕ => (mu2 β (κ ^ 2 / lam) ^ (j + 1))⁻¹ *
      perfectForesight.E t ((fun _ _ => (1 : ℝ)) (t + j)) ()) =
      fun j : ℕ => 1 * 1 ^ j / mu2 β (κ ^ 2 / lam) ^ (j + 1) := by
    funext j
    change (mu2 β (κ ^ 2 / lam) ^ (j + 1))⁻¹ * 1 = _
    simp [div_eq_mul_inv]
  rw [e, hs.tsum_eq]
  exact mul_pos (inv_pos.mpr hβ) (div_pos one_pos (by linarith))

/-- Woodford (2003), p. 528, **survey E13 (counterexample)**: under perfect foresight with
`u ≡ 1`, the printed output-gap forecast fails at every date, for every `x_{t₀−1}`. -/
theorem printed_forecast_x_false {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (xm1 : Unit → ℝ) (t : ℕ) :
    xStar perfectForesight β κ lam xm1 (fun _ _ => 1) (t + 1) ≠
      mu1 β (κ ^ 2 / lam) • xStar perfectForesight β κ lam xm1 (fun _ _ => 1) t +
        (κ / lam) • fwdU perfectForesight β κ lam (fun _ _ => 1) (t + 1) := by
  intro h
  have h0 := (printed_forecast_x_iff perfectForesight hκ.ne' hlam.ne' β xm1 _ t).mp h
  have := fwdU_one_pos hβ hκ hlam (t + 1)
  rw [h0] at this
  exact lt_irrefl _ this

/-! ### Conditional forecasts at date `t` -/

/-- Woodford (2003), p. 529: the forward sum `∑_{j ≥ 1} μ₂^{−j} E_t u_{t+j}`, written
`∑_{j ≥ 0} μ₂^{−(j+1)} E_t u_{t+1+j}`. -/
noncomputable def S (β κ lam : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, (mu2 β (κ ^ 2 / lam) ^ (j + 1))⁻¹ * 𝔼.E t (u (t + 1 + j)) ω

/-- Woodford (2003), p. 529 ("taking the expectations of these two expressions conditional upon
period `t` information"): `E_t[β⁻¹ ∑ⱼ μ₂^{−j−1} E_{t+1} u_{t+1+j}] = β⁻¹ ∑_{j ≥ 1} μ₂^{−j} E_t
u_{t+j}`, by the law of iterated expectations and dominated interchange. -/
theorem E_fwdU_succ {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) {u : ℕ → Ω → ℝ}
    (hu : BoundedProc u) (t : ℕ) :
    𝔼.E t (fwdU 𝔼 β κ lam u (t + 1)) = β⁻¹ • S 𝔼 β κ lam u t := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  obtain ⟨M, hM⟩ := hu
  set m := mu2 β (κ ^ 2 / lam) with hm
  have h2 : 1 < m := one_lt_mu2 hβ hc
  have ha0 : 0 ≤ m⁻¹ := inv_nonneg.mpr (by linarith)
  have ha1 : m⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2
  have hb : ∀ k ω', |m⁻¹ ^ k * 𝔼.E (t + 1) ((β * m)⁻¹ • u (t + 1 + k)) ω'| ≤
      m⁻¹ ^ k * (|(β * m)⁻¹| * M) := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg ha0]
    refine mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω'' => ?_) _ ω') (pow_nonneg ha0 k)
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _ ω'') (abs_nonneg _)
  funext ω
  change 𝔼.E t (fun ω' => ∑' k, m⁻¹ ^ k * 𝔼.E (t + 1) ((β * m)⁻¹ • u (t + 1 + k)) ω') ω = _
  rw [𝔼.E_tsum ha0 ha1 hb t ω]
  simp only [S, Pi.smul_apply, smul_eq_mul, ← hm]
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (m⁻¹ ^ k • 𝔼.E (t + 1) ((β * m)⁻¹ • u (t + 1 + k))) ω = _
  rw [map_smul, 𝔼.tower (Nat.le_succ t), map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [pow_succ, mul_inv, mul_inv, inv_pow]
  ring

/-- Woodford (2003), p. 529: the forward sum satisfies `β⁻¹ ∑ⱼ μ₂^{−j−1} E_t u_{t+j} =
μ₁ (u_t + ∑_{j ≥ 1} μ₂^{−j} E_t u_{t+j})`. -/
theorem fwdU_eq_mu1 {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) {u : ℕ → Ω → ℝ}
    (hu : BoundedProc u) (hua : 𝔼.Adapted u) (t : ℕ) :
    fwdU 𝔼 β κ lam u t = mu1 β (κ ^ 2 / lam) • (u t + S 𝔼 β κ lam u t) := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have h2 := one_lt_mu2 hβ hc
  have ha : |(mu2 β (κ ^ 2 / lam))⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]
    exact inv_lt_one_of_one_lt₀ h2
  obtain ⟨M, hM⟩ := hu
  have hub : ∀ t ω, |((β * mu2 β (κ ^ 2 / lam))⁻¹ • u t) ω| ≤
      |(β * mu2 β (κ ^ 2 / lam))⁻¹| * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)
  have hua' : 𝔼.Adapted (fun t => (β * mu2 β (κ ^ 2 / lam))⁻¹ • u t) := fun t => by
    simp only [map_smul, hua t]
  have hsol := ForwardSolution.forwardSeries_solves_abs 𝔼 ha hub hua' t
  have hE := E_fwdU_succ 𝔼 hβ hκ hlam ⟨M, hM⟩ t
  unfold fwdU fwdPart at hE ⊢
  rw [hsol, hE, inv_beta_mul_mu2 hβ hc, inv_mu2 hβ hc, smul_smul, smul_add]
  rw [mul_comm β, mul_assoc, mul_inv_cancel₀ hβ.ne', mul_one, add_comm]

/-- Woodford (2003), p. 529: `E_t π_{t+1} = (1 − μ₁)(λ/κ) x_t + β⁻¹ ∑_{j ≥ 1} μ₂^{−j} E_t u_{t+j}`
in the equilibrium of Proposition 7.15. -/
theorem E_forecast_pi {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    {u : ℕ → Ω → ℝ} (hu : BoundedProc u) (hua : 𝔼.Adapted u) {xm1 : Ω → ℝ} {K : ℝ}
    (hK : ∀ ω, |xm1 ω| ≤ K) (hm0 : 𝔼.E 0 xm1 = xm1) (t : ℕ) :
    𝔼.E t (piStar 𝔼 β κ lam xm1 u (t + 1)) = ((1 - mu1 β (κ ^ 2 / lam)) * (lam / κ)) •
      xStar 𝔼 β κ lam xm1 u t + β⁻¹ • S 𝔼 β κ lam u t := by
  obtain ⟨⟨-, -, -, -, -, hxa⟩, -⟩ := prop_7_15 𝔼 hβ hκ hlam hu hua hK hm0
  rw [forecast_pi 𝔼 hκ.ne' hlam.ne', map_add, map_smul, hxa t, E_fwdU_succ 𝔼 hβ hκ hlam hu]

/-- Woodford (2003), p. 529: `E_t x_{t+1} = μ₁ x_t − (κ/(βλ)) ∑_{j ≥ 1} μ₂^{−j} E_t u_{t+j}` in the
equilibrium of Proposition 7.15. -/
theorem E_forecast_x {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    {u : ℕ → Ω → ℝ} (hu : BoundedProc u) (hua : 𝔼.Adapted u) {xm1 : Ω → ℝ} {K : ℝ}
    (hK : ∀ ω, |xm1 ω| ≤ K) (hm0 : 𝔼.E 0 xm1 = xm1) (t : ℕ) :
    𝔼.E t (xStar 𝔼 β κ lam xm1 u (t + 1)) = mu1 β (κ ^ 2 / lam) • xStar 𝔼 β κ lam xm1 u t -
      (κ / (β * lam)) • S 𝔼 β κ lam u t := by
  obtain ⟨⟨-, -, -, -, -, hxa⟩, -⟩ := prop_7_15 𝔼 hβ hκ hlam hu hua hK hm0
  rw [xStar_eq, lagged_succ, map_sub, map_smul, map_smul, hxa t, E_fwdU_succ 𝔼 hβ hκ hlam hu,
    smul_smul]
  congr 2
  field_simp

/-! ### The projection identity (p. 529) and its singular case -/

/-- Woodford (2003), p. 529: `βμ₁² = (1 + β + κ²/λ)μ₁ − 1` (`μ₁` is a root of (1.11)). -/
theorem mu1_sq {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) :
    β * mu1 β (κ ^ 2 / lam) ^ 2 = (1 + β + κ ^ 2 / lam) * mu1 β (κ ^ 2 / lam) - 1 := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have hs := beta_mul_sum (c := κ ^ 2 / lam) hβ
  have hp := beta_mul_prod hβ hc
  linear_combination mu1 β (κ ^ 2 / lam) * hs - hp

/-- Woodford (2003), p. 529 (the identity used for the projection):
`κ² + λ + β(1 − μ₁)λ = λ/μ₁`. -/
theorem identity_529a {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) :
    κ ^ 2 + lam + β * (1 - mu1 β (κ ^ 2 / lam)) * lam = lam / mu1 β (κ ^ 2 / lam) := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have hμ := (mu1_pos hβ hc).ne'
  have h := mu1_sq hβ hκ hlam
  rw [eq_div_iff hμ]
  field_simp at h
  linear_combination -h

/-- Woodford (2003), p. 529 (the second identity used for the projection):
`1 − μ₁ − μ₂ = −(κ² + λ)/(βλ)`. -/
theorem identity_529b {β κ lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) :
    1 - mu1 β (κ ^ 2 / lam) - mu2 β (κ ^ 2 / lam) = -(κ ^ 2 + lam) / (β * lam) := by
  have hs := beta_mul_sum (c := κ ^ 2 / lam) hβ
  rw [eq_div_iff (by positivity)]
  field_simp at hs
  linear_combination -hs

/-- Woodford (2003), p. 529 (**the bank's projection**): if the private sector expects
`E_t π_{t+1} = (1 − μ₁)(λ/κ)x_t + β⁻¹S` and `E_t x_{t+1} = μ₁x_t − (κ/(βλ))S` (with
`S = ∑_{j ≥ 1} μ₂^{−j} E_t u_{t+j}`), and `π_t, x_t` solve (2.1) and (2.23) given `i_t`, then,
provided `κ ≠ σλ`, the projected target is
`π_t + (λ/κ)x_t = −σ/((λ⁻¹κ − σ)μ₁(1 − μ₁)) (i_t − rⁿ_t) + u_t − (κ² + λ)/(β(1 − μ₁)λ) S`. -/
theorem projection_eq {β κ lam σ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (hsing : κ ≠ σ * lam) {x π i rn u S : ℝ}
    (hIS : x = (mu1 β (κ ^ 2 / lam) * x - κ / (β * lam) * S) -
      σ * (i - ((1 - mu1 β (κ ^ 2 / lam)) * (lam / κ) * x + β⁻¹ * S) - rn))
    (hAS : π = κ * x + β * ((1 - mu1 β (κ ^ 2 / lam)) * (lam / κ) * x + β⁻¹ * S) + u) :
    π + lam / κ * x = -σ / (lam⁻¹ * κ - σ) * (1 / (mu1 β (κ ^ 2 / lam) *
      (1 - mu1 β (κ ^ 2 / lam)))) * (i - rn) + u -
        1 / (β * (1 - mu1 β (κ ^ 2 / lam))) * ((κ ^ 2 + lam) / lam) * S := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  set μ := mu1 β (κ ^ 2 / lam) with hμdef
  have hμ0 : μ ≠ 0 := (mu1_pos hβ hc).ne'
  have hμ1 : 1 - μ ≠ 0 := by have := mu1_lt_one hβ hc; linarith
  have hd : κ - σ * lam ≠ 0 := sub_ne_zero.mpr hsing
  have hd' : lam⁻¹ * κ - σ ≠ 0 := by
    intro h
    apply hd
    field_simp at h
    linarith
  have I1 := identity_529a hβ hκ hlam
  rw [← hμdef] at I1
  have hx : x * ((1 - μ) * (κ - σ * lam)) =
      κ * (-σ * (i - rn) + (σ - κ / lam) / β * S) := by
    field_simp at hIS ⊢
    linear_combination hIS
  have hT : π + lam / κ * x = lam / (μ * κ) * x + S + u := by
    rw [hAS]
    field_simp at I1 ⊢
    linear_combination x * I1
  rw [hT]
  field_simp at hx I1 ⊢
  linear_combination lam * hx + S * κ * (κ - σ * lam) * I1

/-- Woodford (2003), p. 529 (**the singularity at `κ = σλ`**): if `κ = σλ`, the projected IS
relation does not involve `x_t` at all — it holds iff `i_t = rⁿ_t`, for every `x_t` — so the
projection of p. 529 (whose coefficient `−σ/(λ⁻¹κ − σ)` is then undefined) does not exist. -/
theorem projection_singular {β κ lam σ : ℝ} (hβ : β ≠ 0) (hσ : σ ≠ 0) (hlam : lam ≠ 0)
    (hsing : κ = σ * lam) (μ x i rn S : ℝ) :
    x = (μ * x - κ / (β * lam) * S) - σ * (i - ((1 - μ) * (lam / κ) * x + β⁻¹ * S) - rn) ↔
      i = rn := by
  subst hsing
  have key : (μ * x - σ * lam / (β * lam) * S) -
      σ * (i - ((1 - μ) * (lam / (σ * lam)) * x + β⁻¹ * S) - rn) - x = -σ * (i - rn) := by
    field_simp
    ring
  constructor
  · intro h
    have : -σ * (i - rn) = 0 := by rw [← key]; linarith
    have := (mul_eq_zero.mp this).resolve_left (neg_ne_zero.mpr hσ)
    linarith
  · intro h
    rw [h, sub_self, mul_zero] at key
    rw [h]
    linarith

/-- Woodford (2003), p. 529: the bank's projection of its target `π_t + (λ/κ)x_t` as a function
of its instrument `i_t` (the right side of `projection_eq`). -/
noncomputable def proj529 (β κ lam σ i rn u S : ℝ) : ℝ :=
  -σ / (lam⁻¹ * κ - σ) * (1 / (mu1 β (κ ^ 2 / lam) * (1 - mu1 β (κ ^ 2 / lam)))) * (i - rn) + u
    - 1 / (β * (1 - mu1 β (κ ^ 2 / lam))) * ((κ ^ 2 + lam) / lam) * S

/-- Woodford (2003), eq. (5.4), p. 529: the right side of the fundamentals-based reaction
function, `rⁿ_t + μ₁(1 − λσ/κ){(1 − μ₁)κ/(λσ) u_t − κ/(βλσ)(1 + κ²/λ) S − (1 − μ₁)/σ x_{t−1}}`
with `S = ∑_{j ≥ 1} μ₂^{−j} E_t u_{t+j}`. -/
noncomputable def rate54 (β κ lam σ rn u xprev S : ℝ) : ℝ :=
  rn + mu1 β (κ ^ 2 / lam) * (1 - lam * σ / κ) *
    ((1 - mu1 β (κ ^ 2 / lam)) * κ / (lam * σ) * u - κ / (β * lam * σ) * (1 + κ ^ 2 / lam) * S
      - (1 - mu1 β (κ ^ 2 / lam)) / σ * xprev)

/-- Woodford (2003), eq. (5.4), p. 529 (derivation): when `κ ≠ σλ`, equating the projection to
`(λ/κ)x_{t−1}` (as (5.1) requires) is equivalent to setting `i_t` by (5.4). -/
theorem eq54_iff {β κ lam σ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) (hσ : σ ≠ 0)
    (hsing : κ ≠ σ * lam) (i rn u xprev S : ℝ) :
    proj529 β κ lam σ i rn u S = lam / κ * xprev ↔ i = rate54 β κ lam σ rn u xprev S := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  set μ := mu1 β (κ ^ 2 / lam) with hμdef
  have hμ0 : μ ≠ 0 := (mu1_pos hβ hc).ne'
  have hμ1 : 1 - μ ≠ 0 := by have := mu1_lt_one hβ hc; linarith
  have hd : κ - σ * lam ≠ 0 := sub_ne_zero.mpr hsing
  have hd' : lam⁻¹ * κ - σ ≠ 0 := by
    intro h
    apply hd
    field_simp at h
    linarith
  have hA : -σ / (lam⁻¹ * κ - σ) * (1 / (μ * (1 - μ))) ≠ 0 := by
    have : -σ ≠ 0 := neg_ne_zero.mpr hσ
    positivity
  have key : proj529 β κ lam σ i rn u S - lam / κ * xprev =
      -σ / (lam⁻¹ * κ - σ) * (1 / (μ * (1 - μ))) * (i - rate54 β κ lam σ rn u xprev S) := by
    simp only [proj529, rate54, ← hμdef]
    field_simp
    ring
  constructor
  · intro h
    rw [h, sub_self] at key
    have := (mul_eq_zero.mp key.symm).resolve_left hA
    linarith
  · intro h
    rw [h, sub_self, mul_zero, sub_eq_zero] at key
    rw [h]
    exact key

/-- Woodford (2003), eq. (5.4), p. 529 (pointwise form of the equilibrium check): with
`x_t = μ₁x_{t−1} − (κ/λ)μ₁(u_t + S)` and the expectations of p. 529, the IS relation (2.23)
holds iff `i_t` is given by (5.4) — for all parameter values, including `κ = σλ`. -/
theorem is_iff_rate54 {β κ lam σ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) (hσ : σ ≠ 0)
    (xprev u S i rn : ℝ) :
    (mu1 β (κ ^ 2 / lam) * xprev - κ / lam * mu1 β (κ ^ 2 / lam) * (u + S) =
      (mu1 β (κ ^ 2 / lam) * (mu1 β (κ ^ 2 / lam) * xprev - κ / lam * mu1 β (κ ^ 2 / lam) *
        (u + S)) - κ / (β * lam) * S) - σ * (i - ((1 - mu1 β (κ ^ 2 / lam)) * (lam / κ) *
          (mu1 β (κ ^ 2 / lam) * xprev - κ / lam * mu1 β (κ ^ 2 / lam) * (u + S)) + β⁻¹ * S)
            - rn)) ↔ i = rate54 β κ lam σ rn u xprev S := by
  have hpoly := mu1_sq hβ hκ hlam
  set μ := mu1 β (κ ^ 2 / lam) with hμdef
  have key : (μ * (μ * xprev - κ / lam * μ * (u + S)) - κ / (β * lam) * S) - σ * (i - ((1 - μ) *
      (lam / κ) * (μ * xprev - κ / lam * μ * (u + S)) + β⁻¹ * S) - rn) -
      (μ * xprev - κ / lam * μ * (u + S)) = -σ * (i - rate54 β κ lam σ rn u xprev S) := by
    simp only [rate54, ← hμdef]
    field_simp
    field_simp at hpoly
    linear_combination S * κ * (lam * σ - κ) * hpoly
  constructor
  · intro h
    have : -σ * (i - rate54 β κ lam σ rn u xprev S) = 0 := by rw [← key]; linarith
    have := (mul_eq_zero.mp this).resolve_left (neg_ne_zero.mpr hσ)
    linarith
  · intro h
    rw [h, sub_self, mul_zero] at key
    rw [h]
    linarith

/-- Woodford (2003), eq. (5.4), p. 529 ("this relation is consistent with the desired
state-contingent evolution of the interest rate"): in the equilibrium of Proposition 7.15 the IS
relation (2.23) holds iff the interest rate follows the fundamentals-based reaction function
(5.4) at every date and state (for all parameter values, including `κ = σλ`). -/
theorem eq54_equilibrium {β κ lam σ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (hσ : σ ≠ 0) {u : ℕ → Ω → ℝ} (hu : BoundedProc u) (hua : 𝔼.Adapted u) {xm1 : Ω → ℝ}
    {K : ℝ} (hK : ∀ ω, |xm1 ω| ≤ K) (hm0 : 𝔼.E 0 xm1 = xm1) (rn i : ℕ → Ω → ℝ) :
    IS 𝔼 σ rn i (piStar 𝔼 β κ lam xm1 u) (xStar 𝔼 β κ lam xm1 u) ↔
      ∀ t ω, i t ω = rate54 β κ lam σ (rn t ω) (u t ω)
        (lagged xm1 (xStar 𝔼 β κ lam xm1 u) t ω) (S 𝔼 β κ lam u t ω) := by
  have hx : ∀ t ω, xStar 𝔼 β κ lam xm1 u t ω = mu1 β (κ ^ 2 / lam) *
      lagged xm1 (xStar 𝔼 β κ lam xm1 u) t ω - κ / lam * mu1 β (κ ^ 2 / lam) *
        (u t ω + S 𝔼 β κ lam u t ω) := by
    intro t ω
    have h := congrFun (xStar_eq 𝔼 β κ lam xm1 u t) ω
    rw [fwdU_eq_mu1 𝔼 hβ hκ hlam hu hua] at h
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h
    rw [h]
    ring
  have hE : ∀ t ω, 𝔼.E t (xStar 𝔼 β κ lam xm1 u (t + 1)) ω = mu1 β (κ ^ 2 / lam) *
      xStar 𝔼 β κ lam xm1 u t ω - κ / (β * lam) * S 𝔼 β κ lam u t ω := fun t ω => by
    rw [E_forecast_x 𝔼 hβ hκ hlam hu hua hK hm0]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hP : ∀ t ω, 𝔼.E t (piStar 𝔼 β κ lam xm1 u (t + 1)) ω = (1 - mu1 β (κ ^ 2 / lam)) *
      (lam / κ) * xStar 𝔼 β κ lam xm1 u t ω + β⁻¹ * S 𝔼 β κ lam u t ω := fun t ω => by
    rw [E_forecast_pi 𝔼 hβ hκ hlam hu hua hK hm0]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h t ω
    have e := congrFun (h t) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hE, hP] at e
    rw [hx t ω] at e
    exact (is_iff_rate54 hβ hκ hlam hσ _ _ _ _ _).mp (by linarith [e])
  · intro h t
    funext ω
    have e := (is_iff_rate54 hβ hκ hlam hσ _ _ _ _ _).mpr (h t ω)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hE, hP]
    rw [hx t ω]
    linarith [e]

/-! ### The expectations-based reaction function (5.5) and Proposition 7.17 -/

/-- Woodford (2003), p. 530 (the bank's projection with observed expectations): if `π_t, x_t`
solve (2.1) and (2.23) given `i_t` and the expectations `E_t π_{t+1}, E_t x_{t+1}`, then
`π_t + (λ/κ)x_t = −σ(κ² + λ)/κ (i_t − rⁿ_t) + u_t + (β + σ(κ² + λ)/κ) E_t π_{t+1}
+ (κ² + λ)/κ E_t x_{t+1}`. -/
theorem projection55 {β κ lam σ : ℝ} (hκ : κ ≠ 0) {x π i rn u Eπ Ex : ℝ}
    (hIS : x = Ex - σ * (i - Eπ - rn)) (hAS : π = κ * x + β * Eπ + u) :
    π + lam / κ * x = -σ * ((κ ^ 2 + lam) / κ) * (i - rn) + u +
      (β + σ * ((κ ^ 2 + lam) / κ)) * Eπ + (κ ^ 2 + lam) / κ * Ex := by
  subst hAS hIS
  field_simp
  ring

/-- Woodford (2003), eq. (5.5), p. 530: the right side of the expectations-based reaction
function, `rⁿ_t + κ/(σ(κ² + λ)) u_t + (1 + βκ/(σ(κ² + λ))) E_t π_{t+1} + σ⁻¹ E_t x_{t+1}
− λ/(σ(κ² + λ)) x_{t−1}`. -/
noncomputable def r55 (β κ lam σ rn u Eπ Ex xprev : ℝ) : ℝ :=
  rn + κ / (σ * (κ ^ 2 + lam)) * u + (1 + β * κ / (σ * (κ ^ 2 + lam))) * Eπ + σ⁻¹ * Ex
    - lam / (σ * (κ ^ 2 + lam)) * xprev

/-- Woodford (2003), eq. (5.5), p. 530 (derivation, and "this just reverses the steps",
p. 531): given (2.1) and (2.23), the target criterion (5.1) holds at `t` iff `i_t` is set by
(5.5). -/
theorem eq55_iff {β κ lam σ : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) (hσ : σ ≠ 0)
    {x π i rn u Eπ Ex xprev : ℝ} (hIS : x = Ex - σ * (i - Eπ - rn))
    (hAS : π = κ * x + β * Eπ + u) :
    π + lam / κ * (x - xprev) = 0 ↔ i = r55 β κ lam σ rn u Eπ Ex xprev := by
  have hpos : 0 < κ ^ 2 + lam := by positivity
  have hA : -σ * ((κ ^ 2 + lam) / κ) ≠ 0 := by
    have : -σ ≠ 0 := neg_ne_zero.mpr hσ
    positivity
  have key : π + lam / κ * (x - xprev) =
      -σ * ((κ ^ 2 + lam) / κ) * (i - r55 β κ lam σ rn u Eπ Ex xprev) := by
    have h := projection55 (lam := lam) hκ.ne' hIS hAS
    have e : π + lam / κ * (x - xprev) = (π + lam / κ * x) - lam / κ * xprev := by ring
    rw [e, h]
    simp only [r55]
    field_simp
    ring
  rw [key]
  constructor
  · intro h
    have := (mul_eq_zero.mp h).resolve_left hA
    linarith
  · intro h
    rw [h, sub_self, mul_zero]

/-- Woodford (2003), eq. (5.5), p. 530: the central bank sets `i_t` by the expectations-based
reaction function at every date `t ≥ t₀` (and every state). -/
def RF55 (β κ lam σ : ℝ) (rn u : ℕ → Ω → ℝ) (xm1 : Ω → ℝ) (i π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, i t ω = r55 β κ lam σ (rn t ω) (u t ω) (𝔼.E t (π (t + 1)) ω) (𝔼.E t (x (t + 1)) ω)
    (lagged xm1 x t ω)

/-- Woodford (2003), p. 531 ("Equation (5.5), together with (2.1) and (2.23), implies that (5.1)
must hold in each period"), with the converse: under (2.1) and (2.23), (5.5) at every date is
equivalent to (5.1) at every date. -/
theorem rf55_iff_crit {β κ lam σ : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) (hσ : σ ≠ 0)
    {rn u π x i : ℕ → Ω → ℝ} {xm1 : Ω → ℝ} (hIS : IS 𝔼 σ rn i π x)
    (hAS : AS 𝔼 β κ u π x) :
    RF55 𝔼 β κ lam σ rn u xm1 i π x ↔ Crit lam κ xm1 π x := by
  have hpt : ∀ t ω, π t ω + lam / κ * (x t ω - lagged xm1 x t ω) = 0 ↔
      i t ω = r55 β κ lam σ (rn t ω) (u t ω) (𝔼.E t (π (t + 1)) ω) (𝔼.E t (x (t + 1)) ω)
        (lagged xm1 x t ω) := by
    intro t ω
    have e1 := congrFun (hIS t) ω
    have e2 := congrFun (hAS t) ω
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e1 e2
    exact eq55_iff hκ hlam hσ e1 e2
  constructor
  · intro h t
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
    exact (hpt t ω).mpr (h t ω)
  · intro h t ω
    refine (hpt t ω).mp ?_
    have := congrFun (h t) ω
    simpa only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
      using this

/-- Woodford (2003), eq. (2.23), p. 506: given `π, x`, the IS relation pins down the interest
rate, `i_t = rⁿ_t + E_t π_{t+1} + σ⁻¹(E_t x_{t+1} − x_t)`. -/
theorem is_iff_rate {σ : ℝ} (hσ : σ ≠ 0) {rn i π x : ℕ → Ω → ℝ} :
    IS 𝔼 σ rn i π x ↔
      ∀ t, i t = rn t + 𝔼.E t (π (t + 1)) + σ⁻¹ • (𝔼.E t (x (t + 1)) - x t) := by
  refine forall_congr' fun t => ?_
  constructor
  · intro h
    funext ω
    have := congrFun h ω
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this ⊢
    field_simp
    linarith
  · intro h
    funext ω
    have := congrFun h ω
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this ⊢
    rw [this]
    field_simp
    ring

/-- Woodford (2003), p. 531: the interest-rate path of the equilibrium of Proposition 7.15,
solved from (2.23), `i_t = rⁿ_t + E_t π_{t+1} + σ⁻¹(E_t x_{t+1} − x_t)`. -/
noncomputable def iStar (β κ lam σ : ℝ) (rn u : ℕ → Ω → ℝ) (xm1 : Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => rn t + 𝔼.E t (piStar 𝔼 β κ lam xm1 u (t + 1)) +
    σ⁻¹ • (𝔼.E t (xStar 𝔼 β κ lam xm1 u (t + 1)) - xStar 𝔼 β κ lam xm1 u t)

/-- Woodford (2003), **Proposition 7.17**, p. 530: if the central bank sets `i_t` by (5.5) at
every `t ≥ t₀`, then for bounded adapted disturbances `u, rⁿ` (otherwise unrestricted) there is
a determinate equilibrium: `(π*, x*, i*)` is a bounded adapted solution of (2.1), (2.23) and
(5.5), and it is the only one (with bounded adapted output gap); `(π*, x*)` are the paths of
Proposition 7.7 (`piStar_eq`, `crit_isConstrainedOpt`). -/
theorem prop_7_17 {β κ lam σ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) (hσ : 0 < σ)
    {u rn : ℕ → Ω → ℝ} (hu : BoundedProc u) (hua : 𝔼.Adapted u) (hrn : BoundedProc rn)
    (hrna : 𝔼.Adapted rn) {xm1 : Ω → ℝ} {K : ℝ} (hK : ∀ ω, |xm1 ω| ≤ K)
    (hm0 : 𝔼.E 0 xm1 = xm1) :
    (AS 𝔼 β κ u (piStar 𝔼 β κ lam xm1 u) (xStar 𝔼 β κ lam xm1 u) ∧
      IS 𝔼 σ rn (iStar 𝔼 β κ lam σ rn u xm1) (piStar 𝔼 β κ lam xm1 u) (xStar 𝔼 β κ lam xm1 u) ∧
      RF55 𝔼 β κ lam σ rn u xm1 (iStar 𝔼 β κ lam σ rn u xm1) (piStar 𝔼 β κ lam xm1 u)
        (xStar 𝔼 β κ lam xm1 u) ∧
      BoundedProc (piStar 𝔼 β κ lam xm1 u) ∧ BoundedProc (xStar 𝔼 β κ lam xm1 u) ∧
      BoundedProc (iStar 𝔼 β κ lam σ rn u xm1) ∧ 𝔼.Adapted (piStar 𝔼 β κ lam xm1 u) ∧
      𝔼.Adapted (xStar 𝔼 β κ lam xm1 u) ∧ 𝔼.Adapted (iStar 𝔼 β κ lam σ rn u xm1)) ∧
    ∀ π x i : ℕ → Ω → ℝ, AS 𝔼 β κ u π x → IS 𝔼 σ rn i π x →
      RF55 𝔼 β κ lam σ rn u xm1 i π x → BoundedProc x → 𝔼.Adapted x →
        π = piStar 𝔼 β κ lam xm1 u ∧ x = xStar 𝔼 β κ lam xm1 u ∧
          i = iStar 𝔼 β κ lam σ rn u xm1 := by
  obtain ⟨⟨hAS, hC, hpb, hxb, hpa, hxa⟩, huniq⟩ := prop_7_15 𝔼 hβ hκ hlam hu hua hK hm0
  have hIS : IS 𝔼 σ rn (iStar 𝔼 β κ lam σ rn u xm1) (piStar 𝔼 β κ lam xm1 u)
      (xStar 𝔼 β κ lam xm1 u) := (is_iff_rate 𝔼 hσ.ne').mpr fun t => rfl
  have hib : BoundedProc (iStar 𝔼 β κ lam σ rn u xm1) := by
    obtain ⟨Mr, hMr⟩ := hrn
    obtain ⟨Mp, hMp⟩ := hpb
    obtain ⟨Mx, hMx⟩ := hxb
    refine ⟨Mr + Mp + |σ⁻¹| * (Mx + Mx), fun t ω => ?_⟩
    simp only [iStar, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add (hMr t ω) (𝔼.abs_E_le (hMp (t + 1)) t ω))) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
      (add_le_add (𝔼.abs_E_le (hMx (t + 1)) t ω) (hMx t ω))) (abs_nonneg _)
  have hia : 𝔼.Adapted (iStar 𝔼 β κ lam σ rn u xm1) := fun t => by
    simp only [iStar, map_add, map_smul, map_sub, 𝔼.E_E_self, hrna t, hxa t]
  refine ⟨⟨hAS, hIS, (rf55_iff_crit 𝔼 hκ hlam hσ.ne' hIS hAS).mpr hC, hpb, hxb, hib, hpa, hxa,
    hia⟩, fun π x i hA hI hR hxb' hxa' => ?_⟩
  obtain ⟨hπ, hx⟩ := huniq π x hA ((rf55_iff_crit 𝔼 hκ hlam hσ.ne' hI hA).mp hR) hxb' hxa'
  refine ⟨hπ, hx, ?_⟩
  funext t
  rw [(is_iff_rate 𝔼 hσ.ne').mp hI t, hπ, hx]
  rfl

/-- Woodford (2003), **Proposition 7.17**, p. 530 ("Hence such a policy is optimal from a
timeless perspective"): every bounded adapted equilibrium under (5.5) is optimal from a timeless
perspective, with the self-consistent constraint rule (2.11). -/
theorem prop_7_17_timeless {β κ lam σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hσ : 0 < σ) (hpo : 𝔼.PullOut) (xs : ℝ) {u rn : ℕ → Ω → ℝ}
    (hu : BoundedProc u) (hua : 𝔼.Adapted u) (hrn : BoundedProc rn) (hrna : 𝔼.Adapted rn)
    {xm1 : Ω → ℝ} {K : ℝ} (hK : ∀ ω, |xm1 ω| ≤ K) (hm0 : 𝔼.E 0 xm1 = xm1)
    {π x i : ℕ → Ω → ℝ} (hA : AS 𝔼 β κ u π x) (hI : IS 𝔼 σ rn i π x)
    (hR : RF55 𝔼 β κ lam σ rn u xm1 i π x) (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) :
    TimelesslyOptimal 𝔼 β κ lam xs u (rule211 𝔼 β κ lam u xm1 x) π x := by
  obtain ⟨-, huniq⟩ := prop_7_17 𝔼 hβ hκ hlam hσ hu hua hrn hrna hK hm0
  obtain ⟨hπ, hx, -⟩ := huniq π x i hA hI hR hxb hxa
  rw [hπ, hx]
  exact prop_7_15_timeless 𝔼 hβ hβ1 hκ hlam hpo xs hu hua hK hm0

/-! ### Long-run response coefficients (p. 531) -/

/-- Woodford (2003), p. 531: the long-run response of (5.5) to inflation,
`Ψ_π = 1 + βκ/(σ(κ² + λ))` (the coefficient on `E_t π_{t+1}`). -/
noncomputable def psiPi (β κ lam σ : ℝ) : ℝ := 1 + β * κ / (σ * (κ ^ 2 + lam))

/-- Woodford (2003), p. 531: the long-run response of (5.5) to the output gap, annualised as in
Chapter 4 (`Ψ_x/4` is the sum `σ⁻¹ − λ/(σ(κ² + λ))` of the coefficients on `E_t x_{t+1}` and
`x_{t−1}`). -/
noncomputable def psiX (κ lam σ : ℝ) : ℝ := 4 * (σ⁻¹ - lam / (σ * (κ ^ 2 + lam)))

/-- Woodford (2003), p. 531: in a steady state with constant `E_t π_{t+1} = π̄` and
`E_t x_{t+1} = x_{t−1} = x̄`, the reaction function (5.5) responds with
`rⁿ + κ/(σ(κ² + λ)) u + Ψ_π π̄ + (Ψ_x/4) x̄`. -/
theorem r55_long_run (β κ lam σ rn u pibar xbar : ℝ) :
    r55 β κ lam σ rn u pibar xbar xbar =
      rn + κ / (σ * (κ ^ 2 + lam)) * u + psiPi β κ lam σ * pibar + psiX κ lam σ / 4 * xbar := by
  simp only [r55, psiPi, psiX]
  ring

/-- Woodford (2003), p. 531: `Ψ_π = 1 + βκ/(σ(κ² + λ)) > 1`. -/
theorem psiPi_gt_one {β κ lam σ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (hσ : 0 < σ) : 1 < psiPi β κ lam σ := by
  unfold psiPi
  have : 0 < β * κ / (σ * (κ ^ 2 + lam)) := by positivity
  linarith

/-- Woodford (2003), p. 531: `Ψ_x/4 = κ²/(σ(κ² + λ))`. -/
theorem psiX_div_four {κ lam σ : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) (hσ : 0 < σ) :
    psiX κ lam σ / 4 = κ ^ 2 / (σ * (κ ^ 2 + lam)) := by
  unfold psiX
  field_simp
  ring

/-- Woodford (2003), p. 531: `Ψ_x/4 > 0`. -/
theorem psiX_pos {κ lam σ : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) (hσ : 0 < σ) :
    0 < psiX κ lam σ / 4 := by
  rw [psiX_div_four hκ hlam hσ]
  positivity

/-- Woodford (2003), p. 531 ("the optimal interest-rate rule satisfies the Taylor principle"):
the long-run coefficients satisfy (3.9), `Ψ_π + (1 − β)/(4κ) Ψ_x > 1`, for `0 < β ≤ 1`. -/
theorem taylor_principle {β κ lam σ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hσ : 0 < σ) :
    1 < psiPi β κ lam σ + (1 - β) / (4 * κ) * psiX κ lam σ := by
  have h1 := psiPi_gt_one hβ hκ hlam hσ
  have h2 := psiX_pos hκ hlam hσ
  have h3 : 0 ≤ (1 - β) / (4 * κ) := div_nonneg (by linarith) (by positivity)
  nlinarith

/-! ### The fundamentals-based rule (5.4) need not determine the equilibrium (p. 529)

Under (5.4) the interest rate depends on endogenous variables only through `x_{t−1}`, with
coefficient `a = −μ₁(1 − λσ/κ)(1 − μ₁)/σ` (fn. 43: only this coefficient matters for
determinacy). Deviations `(dπ, dx)` from an equilibrium solve the homogeneous system
`dπ_t = κ dx_t + β dπ_{t+1}`, `dx_t = dx_{t+1} − σ(a dx_{t−1} − dπ_{t+1})`, `dx_{t₀−1} = 0`, whose
characteristic cubic is `(w − μ₁) q(w)` with `q(0) > 0 > q(1)` when `κ > σλ`. So a second stable
root exists and the equilibrium is indeterminate: we prove this for every parameter vector with
`σλ < κ`, under perfect foresight and for arbitrary bounded disturbances. -/

/-- Woodford (2003), eq. (5.4), p. 529: the coefficient of `x_{t−1}` in (5.4). -/
noncomputable def a54 (β κ lam σ : ℝ) : ℝ :=
  -(mu1 β (κ ^ 2 / lam) * (1 - lam * σ / κ) * ((1 - mu1 β (κ ^ 2 / lam)) / σ))

/-- Woodford (2003), eq. (5.4), p. 529: (5.4) is affine in `x_{t−1}` with slope `a54`. -/
theorem rate54_add (β κ lam σ rn u xprev d S : ℝ) :
    rate54 β κ lam σ rn u (xprev + d) S = rate54 β κ lam σ rn u xprev S + a54 β κ lam σ * d := by
  simp only [rate54, a54]
  ring

/-- Woodford (2003), p. 529 (fn. 43): the characteristic cubic of the homogeneous system under
(5.4), `βw³ − (1 + β + σκ)w² + (1 − βσa)w + σa`. -/
def cubic54 (β κ σ a w : ℝ) : ℝ :=
  β * w ^ 3 - (1 + β + σ * κ) * w ^ 2 + (1 - β * σ * a) * w + σ * a

/-- Woodford (2003), p. 529: the quadratic cofactor `q(w) = βw² + (βμ₁ − 1 − β − σκ)w
+ (1 − μ₁)(1 − λσ/κ)` of the cubic. -/
noncomputable def quad54 (β κ lam σ w : ℝ) : ℝ :=
  β * w ^ 2 + (β * mu1 β (κ ^ 2 / lam) - 1 - β - σ * κ) * w
    + (1 - mu1 β (κ ^ 2 / lam)) * (1 - lam * σ / κ)

/-- Woodford (2003), p. 529: the cubic factors as `(w − μ₁) q(w)` (so `μ₁`, the root of the
desired equilibrium, is one root). -/
theorem cubic54_factor {β κ lam σ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (hσ : σ ≠ 0) (w : ℝ) :
    cubic54 β κ σ (a54 β κ lam σ) w = (w - mu1 β (κ ^ 2 / lam)) * quad54 β κ lam σ w := by
  have hpoly := mu1_sq hβ hκ hlam
  set μ := mu1 β (κ ^ 2 / lam) with hμdef
  simp only [cubic54, a54, quad54, ← hμdef]
  field_simp
  field_simp at hpoly
  linear_combination w * σ * hpoly

/-- Woodford (2003), p. 529: the derivative of the cubic, `3βw² − 2(1 + β + σκ)w + (1 − βσa)`. -/
def cubic54' (β κ σ a w : ℝ) : ℝ := 3 * β * w ^ 2 - 2 * (1 + β + σ * κ) * w + (1 - β * σ * a)

/-- Woodford (2003), p. 529: the derivative of `(w − μ₁) q(w)`, so at `w = μ₁` the cubic has a
double root iff `q(μ₁) = 0`. -/
theorem cubic54'_factor {β κ lam σ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (hσ : σ ≠ 0) (w : ℝ) :
    cubic54' β κ σ (a54 β κ lam σ) w = quad54 β κ lam σ w + (w - mu1 β (κ ^ 2 / lam)) *
      (2 * β * w + (β * mu1 β (κ ^ 2 / lam) - 1 - β - σ * κ)) := by
  have hpoly := mu1_sq hβ hκ hlam
  set μ := mu1 β (κ ^ 2 / lam) with hμdef
  simp only [cubic54', a54, quad54, ← hμdef]
  field_simp
  field_simp at hpoly
  linear_combination σ * hpoly

/-- Woodford (2003), p. 529: a root `w` of the cubic gives the homogeneous solution
`dx_t = w^{t+1}`, `dπ_t = κ w^{t+1}/(1 − βw)` of (2.1) and of (2.23) under (5.4) (with
`dx_{t−1} = wᵗ`). -/
theorem geom_homog {β κ σ a w : ℝ} (hD : 1 - β * w ≠ 0) (hC : cubic54 β κ σ a w = 0) (t : ℕ) :
    κ * w ^ (t + 1) / (1 - β * w) = κ * w ^ (t + 1) + β * (κ * w ^ (t + 1 + 1) / (1 - β * w)) ∧
      w ^ (t + 1) = w ^ (t + 1 + 1) - σ * (a * w ^ t - κ * w ^ (t + 1 + 1) / (1 - β * w)) := by
  constructor
  · field_simp
    ring
  · unfold cubic54 at hC
    field_simp
    linear_combination w ^ t * hC

/-- Woodford (2003), p. 529: a double root `w` of the cubic gives the homogeneous solution
`dx_t = (t + 1)w^{t+1}`, `dπ_t = κ w^{t+1}((t + 1)/(1 − βw) + βw/(1 − βw)²)` (with
`dx_{t−1} = t wᵗ`). -/
theorem double_homog {β κ σ a w : ℝ} (hD : 1 - β * w ≠ 0) (hC : cubic54 β κ σ a w = 0)
    (hC' : cubic54' β κ σ a w = 0) (t : ℕ) :
    κ * w ^ (t + 1) * ((t + 1) / (1 - β * w) + β * w / (1 - β * w) ^ 2) =
        κ * ((t + 1) * w ^ (t + 1)) + β * (κ * w ^ (t + 1 + 1) *
          ((t + 1 + 1) / (1 - β * w) + β * w / (1 - β * w) ^ 2)) ∧
      (t + 1) * w ^ (t + 1) = (t + 1 + 1) * w ^ (t + 1 + 1) - σ * (a * (t * w ^ t) -
        κ * w ^ (t + 1 + 1) * ((t + 1 + 1) / (1 - β * w) + β * w / (1 - β * w) ^ 2)) := by
  constructor
  · field_simp
    ring
  · unfold cubic54 at hC
    unfold cubic54' at hC'
    field_simp
    linear_combination ((t : ℝ) * w ^ t * (1 - β * w) + β * w * w ^ t) * hC
      + ((1 - β * w) * w * w ^ t) * hC'

/-- Woodford (2003), p. 529: `q(0) = (1 − μ₁)(1 − λσ/κ) > 0` when `σλ < κ`. -/
theorem quad54_zero_pos {β κ lam σ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (hsl : σ * lam < κ) : 0 < quad54 β κ lam σ 0 := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have h1 := mu1_lt_one hβ hc
  have h2 : lam * σ / κ < 1 := by rw [div_lt_one hκ]; linarith
  simp only [quad54]
  have : 0 < (1 - mu1 β (κ ^ 2 / lam)) * (1 - lam * σ / κ) :=
    mul_pos (by linarith) (by linarith)
  linarith [this]

/-- Woodford (2003), p. 529: `q(1) = βμ₁ − μ₁ − σκ − (1 − μ₁)λσ/κ < 0`. -/
theorem quad54_one_neg {β κ lam σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hσ : 0 < σ) : quad54 β κ lam σ 1 < 0 := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have h0 := mu1_pos hβ hc
  have h1 := mu1_lt_one hβ hc
  have e : quad54 β κ lam σ 1 = -((1 - β) * mu1 β (κ ^ 2 / lam)) - σ * κ -
      (1 - mu1 β (κ ^ 2 / lam)) * (lam * σ / κ) := by
    simp only [quad54]; ring
  rw [e]
  have : 0 < (1 - β) * mu1 β (κ ^ 2 / lam) := mul_pos (by linarith) h0
  have : 0 < (1 - mu1 β (κ ^ 2 / lam)) * (lam * σ / κ) := mul_pos (by linarith) (by positivity)
  nlinarith

/-- Woodford (2003), p. 529: when `σλ < κ` the cofactor `q` has a root `z ∈ (0, 1)`, a second
stable root of the characteristic cubic of the system under (5.4). -/
theorem exists_quad54_root {β κ lam σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hσ : 0 < σ) (hsl : σ * lam < κ) :
    ∃ z, 0 < z ∧ z < 1 ∧ quad54 β κ lam σ z = 0 := by
  have hcont : ContinuousOn (fun w => quad54 β κ lam σ w) (Set.Icc 0 1) := by
    unfold quad54
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Ioo (quad54 β κ lam σ 1) (quad54 β κ lam σ 0) :=
    ⟨quad54_one_neg hβ hβ1 hκ hlam hσ, quad54_zero_pos hβ hκ hlam hsl⟩
  obtain ⟨z, ⟨hz0, hz1⟩, hz⟩ := intermediate_value_Ioo' zero_le_one hcont hmem
  exact ⟨z, hz0, hz1, hz⟩

/-- Woodford (2003), p. 529 (an auxiliary bound): `(t + 1) wᵗ ≤ 1/(1 − w)` for `0 ≤ w < 1`. -/
theorem succ_mul_pow_le {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) (t : ℕ) :
    ((t : ℝ) + 1) * w ^ t ≤ 1 / (1 - w) := by
  have hs : ∑ _i ∈ Finset.range (t + 1), w ^ t ≤ ∑ i ∈ Finset.range (t + 1), w ^ i :=
    Finset.sum_le_sum fun i hi =>
      pow_le_pow_of_le_one h0 h1.le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, geom_sum_eq h1.ne] at hs
  push_cast at hs
  refine hs.trans ?_
  have e : (w ^ (t + 1) - 1) / (w - 1) = (1 - w ^ (t + 1)) / (1 - w) := by
    rw [← neg_div_neg_eq, neg_sub, neg_sub]
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith [pow_nonneg h0 (t + 1)]) (by linarith)

/-- Woodford (2003), p. 529: when `σλ < κ` (and `0 < β < 1`, `κ, λ, σ > 0`), the homogeneous
system under (5.4) — `dπ_t = κ dx_t + β dπ_{t+1}`, `dx_t = dx_{t+1} − σ(a dx_{t−1} − dπ_{t+1})`,
`dx_{t₀−1} = 0` — has a bounded solution with `dx_{t₀} ≠ 0`: built from the two stable roots
`μ₁` and `z` of the cubic (`z^{t+1} − μ₁^{t+1}`), or from the double root `μ₁`
(`(t + 1)μ₁^{t+1}`). -/
theorem exists_homog54 {β κ lam σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hσ : 0 < σ) (hsl : σ * lam < κ) :
    ∃ dπ dx : ℕ → ℝ, (∀ t, dπ t = κ * dx t + β * dπ (t + 1)) ∧
      (∀ t, dx t = dx (t + 1) - σ * (a54 β κ lam σ * lagged 0 dx t - dπ (t + 1))) ∧
      (∃ M, ∀ t, |dπ t| ≤ M) ∧ (∃ M, ∀ t, |dx t| ≤ M) ∧ dx 0 ≠ 0 := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  obtain ⟨z, hz0, hz1, hz⟩ := exists_quad54_root hβ hβ1 hκ hlam hσ hsl
  set μ := mu1 β (κ ^ 2 / lam) with hμdef
  have hμ0 : 0 < μ := mu1_pos hβ hc
  have hμ1 : μ < 1 := mu1_lt_one hβ hc
  have hCμ : cubic54 β κ σ (a54 β κ lam σ) μ = 0 := by
    rw [cubic54_factor hβ hκ hlam hσ.ne', ← hμdef, sub_self, zero_mul]
  have hDμ : 0 < 1 - β * μ := by nlinarith
  by_cases hzμ : z = μ
  · -- double root
    have hq : quad54 β κ lam σ μ = 0 := by rw [← hzμ]; exact hz
    have hC' : cubic54' β κ σ (a54 β κ lam σ) μ = 0 := by
      rw [cubic54'_factor hβ hκ hlam hσ.ne', ← hμdef, hq, sub_self, zero_mul, add_zero]
    set D := 1 - β * μ with hD
    refine ⟨fun t => κ * μ ^ (t + 1) * (((t : ℝ) + 1) / D + β * μ / D ^ 2),
      fun t => ((t : ℝ) + 1) * μ ^ (t + 1), fun t => ?_, fun t => ?_, ?_, ?_, ?_⟩
    · have h := (double_homog hDμ.ne' hCμ hC' t).1
      simp only [Nat.cast_add, Nat.cast_one]
      linear_combination h
    · have h := (double_homog hDμ.ne' hCμ hC' t).2
      have hp : lagged 0 (fun t => ((t : ℝ) + 1) * μ ^ (t + 1)) t = (t : ℝ) * μ ^ t := by
        cases t with
        | zero => simp
        | succ t => simp
      rw [hp]
      simp only [Nat.cast_add, Nat.cast_one]
      linear_combination h
    · refine ⟨κ * ((1 / (1 - μ)) / D + β * μ / D ^ 2), fun t => ?_⟩
      have hb := succ_mul_pow_le hμ0.le hμ1 t
      have hpow : μ ^ (t + 1) ≤ μ ^ t := pow_le_pow_of_le_one hμ0.le hμ1.le (Nat.le_succ t)
      have hp1 : μ ^ (t + 1) ≤ 1 := pow_le_one₀ hμ0.le hμ1.le
      have hnn : 0 ≤ κ * μ ^ (t + 1) * (((t : ℝ) + 1) / D + β * μ / D ^ 2) := by positivity
      rw [abs_of_nonneg hnn]
      have h1 : ((t : ℝ) + 1) * μ ^ (t + 1) ≤ 1 / (1 - μ) :=
        le_trans (mul_le_mul_of_nonneg_left hpow (by positivity)) hb
      have e : κ * μ ^ (t + 1) * (((t : ℝ) + 1) / D + β * μ / D ^ 2) =
          κ * ((((t : ℝ) + 1) * μ ^ (t + 1)) / D + μ ^ (t + 1) * (β * μ / D ^ 2)) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hκ.le
      · exact div_le_div_of_nonneg_right h1 hDμ.le
      · have : 0 ≤ β * μ / D ^ 2 := by positivity
        nlinarith
    · refine ⟨1 / (1 - μ), fun t => ?_⟩
      have hb := succ_mul_pow_le hμ0.le hμ1 t
      have hpow : μ ^ (t + 1) ≤ μ ^ t := pow_le_pow_of_le_one hμ0.le hμ1.le (Nat.le_succ t)
      rw [abs_of_nonneg (by positivity)]
      exact le_trans (mul_le_mul_of_nonneg_left hpow (by positivity)) hb
    · simp only [Nat.cast_zero, zero_add, one_mul, pow_one]
      exact hμ0.ne'
  · -- two distinct stable roots
    have hCz : cubic54 β κ σ (a54 β κ lam σ) z = 0 := by
      rw [cubic54_factor hβ hκ hlam hσ.ne', hz, mul_zero]
    have hDz : 0 < 1 - β * z := by nlinarith
    refine ⟨fun t => κ * z ^ (t + 1) / (1 - β * z) - κ * μ ^ (t + 1) / (1 - β * μ),
      fun t => z ^ (t + 1) - μ ^ (t + 1), fun t => ?_, fun t => ?_, ?_, ?_, ?_⟩
    · have h1 := (geom_homog hDz.ne' hCz t).1
      have h2 := (geom_homog hDμ.ne' hCμ t).1
      linear_combination h1 - h2
    · have h1 := (geom_homog hDz.ne' hCz t).2
      have h2 := (geom_homog hDμ.ne' hCμ t).2
      have hp : lagged 0 (fun t => z ^ (t + 1) - μ ^ (t + 1)) t = z ^ t - μ ^ t := by
        cases t with
        | zero => simp
        | succ t => simp
      rw [hp]
      linear_combination h1 - h2
    · refine ⟨κ / (1 - β * z) + κ / (1 - β * μ), fun t => ?_⟩
      have hz' : z ^ (t + 1) ≤ 1 := pow_le_one₀ hz0.le hz1.le
      have hμ' : μ ^ (t + 1) ≤ 1 := pow_le_one₀ hμ0.le hμ1.le
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_of_nonneg (by positivity)]
        exact div_le_div_of_nonneg_right (by nlinarith [pow_nonneg hz0.le (t + 1)]) hDz.le
      · rw [abs_of_nonneg (by positivity)]
        exact div_le_div_of_nonneg_right (by nlinarith [pow_nonneg hμ0.le (t + 1)]) hDμ.le
    · refine ⟨2, fun t => ?_⟩
      have hz' : z ^ (t + 1) ≤ 1 := pow_le_one₀ hz0.le hz1.le
      have hμ' : μ ^ (t + 1) ≤ 1 := pow_le_one₀ hμ0.le hμ1.le
      have := pow_nonneg hz0.le (t + 1)
      have := pow_nonneg hμ0.le (t + 1)
      rw [abs_le]
      constructor <;> linarith
    · simp only [zero_add, pow_one]
      exact sub_ne_zero.mpr hzμ

/-- Woodford (2003), eq. (5.4), p. 529: the central bank sets `i_t` by the fundamentals-based
reaction function at every date `t ≥ t₀` (and every state). -/
def RF54 (β κ lam σ : ℝ) (rn u : ℕ → Ω → ℝ) (xm1 : Ω → ℝ) (i x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, i t ω = rate54 β κ lam σ (rn t ω) (u t ω) (lagged xm1 x t ω) (S 𝔼 β κ lam u t ω)

/-- Woodford (2003), p. 529 (**(5.4) does not imply determinacy**): under perfect foresight, for
every parameter vector with `σλ < κ` (and `0 < β < 1`, `κ, λ, σ > 0`), every bounded `u, rⁿ`
and every `x_{t₀−1}`, the desired equilibrium `(π*, x*, i*)` satisfies (2.1), (2.23) and (5.4),
but so does a second, different bounded triple. -/
theorem eq54_indeterminate {β κ lam σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hσ : 0 < σ) (hsl : σ * lam < κ) {u rn : ℕ → Unit → ℝ}
    (hu : BoundedProc u) (hrn : BoundedProc rn) (xm1 : Unit → ℝ) :
    (AS perfectForesight β κ u (piStar perfectForesight β κ lam xm1 u)
        (xStar perfectForesight β κ lam xm1 u) ∧
      IS perfectForesight σ rn (iStar perfectForesight β κ lam σ rn u xm1)
        (piStar perfectForesight β κ lam xm1 u) (xStar perfectForesight β κ lam xm1 u) ∧
      RF54 perfectForesight β κ lam σ rn u xm1 (iStar perfectForesight β κ lam σ rn u xm1)
        (xStar perfectForesight β κ lam xm1 u)) ∧
    ∃ π' x' i' : ℕ → Unit → ℝ, AS perfectForesight β κ u π' x' ∧
      IS perfectForesight σ rn i' π' x' ∧ RF54 perfectForesight β κ lam σ rn u xm1 i' x' ∧
      BoundedProc π' ∧ BoundedProc x' ∧ BoundedProc i' ∧
      x' ≠ xStar perfectForesight β κ lam xm1 u := by
  set pf := perfectForesight with hpf
  have hua : pf.Adapted u := fun _ => rfl
  have hrna : pf.Adapted rn := fun _ => rfl
  have hK : ∀ ω, |xm1 ω| ≤ |xm1 ()| := fun ω => by cases ω; exact le_rfl
  have hm0 : pf.E 0 xm1 = xm1 := rfl
  obtain ⟨⟨hAS, hIS, -, hpb, hxb, hib, -, -, -⟩, -⟩ :=
    prop_7_17 pf hβ hκ hlam hσ hu hua hrn hrna hK hm0
  have hRF : RF54 pf β κ lam σ rn u xm1 (iStar pf β κ lam σ rn u xm1) (xStar pf β κ lam xm1 u) :=
    (eq54_equilibrium pf hβ hκ hlam hσ.ne' hu hua hK hm0 rn _).mp hIS
  refine ⟨⟨hAS, hIS, hRF⟩, ?_⟩
  obtain ⟨dπ, dx, hdA, hdI, ⟨Mπ, hMπ⟩, ⟨Mx, hMx⟩, hd0⟩ :=
    exists_homog54 hβ hβ1 hκ hlam hσ hsl
  have hE : ∀ t (y : Unit → ℝ), pf.E t y = y := fun _ _ => rfl
  refine ⟨fun t ω => piStar pf β κ lam xm1 u t ω + dπ t,
    fun t ω => xStar pf β κ lam xm1 u t ω + dx t,
    fun t ω => iStar pf β κ lam σ rn u xm1 t ω + a54 β κ lam σ * lagged 0 dx t,
    fun t => ?_, fun t => ?_, fun t ω => ?_, ?_, ?_, ?_, ?_⟩
  · funext ω
    have h := congrFun (hAS t) ω
    simp only [hE, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
    rw [h, hdA t]
    ring
  · funext ω
    have h := congrFun (hIS t) ω
    simp only [hE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
    rw [hdI t] at ⊢
    linear_combination h
  · have hp : lagged xm1 (fun t ω => xStar pf β κ lam xm1 u t ω + dx t) t ω =
        lagged xm1 (xStar pf β κ lam xm1 u) t ω + lagged 0 dx t := by
      cases t with
      | zero => simp
      | succ t => simp
    dsimp only
    rw [hp, rate54_add, ← hRF t ω]
  · obtain ⟨M, hM⟩ := hpb
    exact ⟨M + Mπ, fun t ω => (abs_add_le _ _).trans (add_le_add (hM t ω) (hMπ t))⟩
  · obtain ⟨M, hM⟩ := hxb
    exact ⟨M + Mx, fun t ω => (abs_add_le _ _).trans (add_le_add (hM t ω) (hMx t))⟩
  · obtain ⟨M, hM⟩ := hib
    refine ⟨M + |a54 β κ lam σ| * (Mx + 0), fun t ω => (abs_add_le _ _).trans
      (add_le_add (hM t ω) ?_)⟩
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    cases t with
    | zero => simp only [lagged_zero, abs_zero, add_zero]; exact (abs_nonneg _).trans (hMx 0)
    | succ t => simp only [lagged_succ, add_zero]; exact hMx t
  · intro h
    have h0 : xStar pf β κ lam xm1 u 0 () + dx 0 = xStar pf β κ lam xm1 u 0 () :=
      congrFun (congrFun h 0) ()
    exact hd0 (by linarith)

end Woodford.GainsFromCommitment.Implementation
