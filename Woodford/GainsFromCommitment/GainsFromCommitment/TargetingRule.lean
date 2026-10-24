/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.ForwardSolution
import GainsFromCommitment.SecondOrderRE
import GainsFromCommitment.VarianceFrontier
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Robustly optimal target criteria

Woodford (2003), *Interest and Prices*, Chapter 7, §5.1 "Robustly Optimal Target Criteria",
pp. 521–527, with Appendix F.5–F.6, pp. 714–715.

Time is `ℕ` with `t₀ = 0`; the predetermined values at `t₀ − 1` (`x_{t₀−1}`, `p_{t₀−1}`,
`φ_{t₀−1}`) are random variables known at `t₀`. Every equation holds for an arbitrary
`ExpectationSystem` (perfect foresight or uncertainty); "unique" means unique among bounded
adapted processes. The cost-push process `u` is only assumed bounded and adapted, which is the
book's robustness claim (p. 524).

## Main results

* The roots `0 < μ₁ < 1 < μ₂` of (1.11) (the shared `SecondOrderRE.mu1`, `mu2`) and the
  workhorse second-order equation (2.6)/(F.10) (`SecondOrder`, the shared
  `SecondOrderRE.SecondOrderEq` with forcing `−z`): `secondOrder_existsUnique`,
  `secondOrderSol_sub`.
* (2.1) (the shared `VarianceFrontier.AS`), (5.1), (1.7)–(1.8): `Crit`, `FOC`. Elimination of
  `φ`: `crit_succ_of_foc` ((5.1) at every `t ≥ t₀ + 1`); `crit_zero_iff_of_foc` ((5.1) at `t₀`
  iff (5.2)); **(5.2)** `crit_iff_foc`.
* **Proposition 7.15**: `prop_7_15` (unique bounded solution of (2.1) and (5.1), via
  `as_crit_iff` and (F.10) `xStar_eq`), `piStar_eq` ((2.12)), `piStar_eq_forward`;
  identification with Proposition 7.7: `crit_isConstrainedOpt` (the equilibrium solves the
  problem with constraint (2.11)), `foc_eq211_eq_star` (the FOC system with constraint (2.11) has
  only this solution — the "easily characterized" step of App. F.5, filled through (5.2)),
  `eq_star_of_isConstrainedOpt` (unique optimum for faithful `E_{t₀}`), and
  `prop_7_15_timeless` (optimal from a timeless perspective, `TimelesslyOptimal`).
* Lagrangian sufficiency (survey §4.4): the exact identity `loss_eq_add`, `loss_le_of_foc`,
  `eq_of_loss_le`, `isConstrainedOpt_of_foc`, `isT0Opt_of_foc`, `eq_of_isConstrainedOpt`,
  `eq_of_isT0Opt`; existence `exists_isConstrainedOpt`, `exists_isT0Opt`.
* "(5.1) must hold for each `t ≥ t₀ + 1` under any timelessly optimal policy (and indeed under a
  `t₀`-optimal commitment as well)", p. 523: `crit_succ_of_isConstrainedOpt`,
  `crit_succ_of_isT0Opt`.
* (5.3) and **Proposition 7.16**: `priceRule_iff_crit` (the fictitious initial condition (F.11)),
  `prop_7_16`, `xStar_fictX_zero` (the formula for `x_{t₀}` in App. F.6), `eq215` ((2.15) of
  Proposition 7.8), `piStar_fictX_zero` ((2.13)), `prop_7_16_optimal`, `prop_7_16_timeless`.
* p. 527: `priceRule_theta` (`λ = κ/θ` ⇒ target `p_t + θ⁻¹x_t`), `theta_weight`,
  `crit_iff_priceRule` ((5.1) from `t₀` ≡ (5.3) with `p̄ = p_{t₀−1} + (λ/κ)x_{t₀−1}`),
  `xStar_sub`, `piStar_sub`, `tendsto_xStar_sub` (different `p̄` differ only transitorily).

The loss is `∑_t βᵗ E_{t₀}[π_t² + λ(x_t − x*)²]`. Optimality is proved by Lagrangian sufficiency
under the pull-out property (`ExpectationSystem.PullOut`, true for perfect foresight and every
finite event tree); uniqueness of the optimum needs `E_{t₀}` to be faithful (`Faithful`), which
perfect foresight is. The approximation-order qualifier "up to `O(‖·‖²)`" of the book refers to
the Chapter 6 welfare approximation and is not part of the LQ statements here.
-/

namespace Woodford.GainsFromCommitment.TargetingRule

open Filter Topology
open SecondOrderRE (charPoly disc mu1 mu2 disc_pos mu1_add_mu2 mu1_mul_mu2 beta_mul_sum
  beta_mul_prod charPoly_factor charPoly_mu1 mu1_lt_mu2 between_roots_of_neg charPoly_one
  mu1_lt_one one_lt_mu2 mu1_pos inv_mu2 inv_beta_mul_mu2 SecondOrderEq eq_of_secondOrderEq
  shiftSys shiftSys_pullOut)
open Sequences (lagged lagged_zero lagged_succ summable_disc)
open VarianceFrontier (AS)

/-! ### The workhorse: `β E_t y_{t+1} − (1 + β + c) y_t + y_{t−1} = −z_t`

The roots `0 < μ₁ < 1 < μ₂` of (1.11), the second-order equation `SecondOrderEq` and its
uniqueness theorem are the shared `SecondOrderRE` objects; the lag `lagged x₋₁ x` (with
`x_{−1} = x₋₁`) is the shared `Sequences.lagged`. -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eqs. (2.6) p. 488 and (F.10) p. 714: the second-order expectational
difference equation `β E_t y_{t+1} − (1 + β + c) y_t + y_{t−1} = −z_t` for all `t ≥ 0`, with
`y_{−1} = ym1`: the shared `SecondOrderRE.SecondOrderEq` with forcing `f = −z`. -/
def SecondOrder (β c : ℝ) (ym1 : Ω → ℝ) (z y : ℕ → Ω → ℝ) : Prop :=
  SecondOrderEq 𝔼 β c (fun t => -z t) ym1 y

/-- Woodford (2003), p. 489: the factorised form. If `y_t = μ₁ y_{t−1} + e_t` with
`e_t = μ₂⁻¹ E_t e_{t+1} + (βμ₂)⁻¹ z_t` and `y` adapted, then `y` solves the equation. -/
theorem secondOrder_of_factor {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {ym1 : Ω → ℝ}
    {z y e : ℕ → Ω → ℝ} (hya : 𝔼.Adapted y)
    (hy : ∀ t, y t = mu1 β c • lagged ym1 y t + e t)
    (he : ∀ t, e t = (mu2 β c)⁻¹ • 𝔼.E t (e (t + 1)) + (β * mu2 β c)⁻¹ • z t) :
    SecondOrder 𝔼 β c ym1 z y := by
  intro t
  have hl2 : mu2 β c ≠ 0 := (lt_trans one_pos (one_lt_mu2 hβ hc)).ne'
  have hE : 𝔼.E t (y (t + 1)) = mu1 β c • y t + 𝔼.E t (e (t + 1)) := by
    rw [hy (t + 1), map_add, map_smul, lagged_succ, hya t]
  rw [hE]
  funext ω
  have h1 := congrFun (he t) ω
  have h2 := congrFun (hy t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply] at h1 h2 ⊢
  have hp := beta_mul_prod hβ hc
  have hs := beta_mul_sum (c := c) hβ
  have h1' : β * 𝔼.E t (e (t + 1)) ω = β * mu2 β c * e t ω - z t ω := by
    rw [h1]
    field_simp
    ring
  linear_combination h1' - β * mu2 β c * h2 + y t ω * hs - lagged ym1 y t ω * hp

/-- Woodford (2003), p. 489 and App. F.5, p. 714: **uniqueness** — two bounded adapted solutions
with the same `y_{−1}` coincide (`0 < μ₁ < 1 < μ₂`; the shared `SecondOrderRE.eq_of_secondOrderEq`,
which needs no hypothesis on the forcing). -/
theorem secondOrder_unique {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {ym1 : Ω → ℝ}
    {z y y' : ℕ → Ω → ℝ} (h : SecondOrder 𝔼 β c ym1 z y) (h' : SecondOrder 𝔼 β c ym1 z y')
    (ha : 𝔼.Adapted y) (ha' : 𝔼.Adapted y') (hb : BoundedProc y) (hb' : BoundedProc y') :
    y = y' :=
  eq_of_secondOrderEq 𝔼 hβ hc h h' ha ha' hb hb'

/-- Woodford (2003), eq. (2.7), p. 489, and (F.10), p. 714: the forward component
`F_t = ∑ₖ μ₂^{−k} E_t[(βμ₂)⁻¹ z_{t+k}] = β⁻¹ ∑ⱼ μ₂^{−j−1} E_t z_{t+j}`. -/
noncomputable def fwdPart (β c : ℝ) (z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries (mu2 β c)⁻¹ (fun t => (β * mu2 β c)⁻¹ • z t)

/-- Woodford (2003), eq. (2.7), p. 489, and (F.10), p. 714: the solution
`y_t = μ₁ y_{t−1} + β⁻¹ ∑ⱼ μ₂^{−j−1} E_t z_{t+j}`, defined recursively from `y_{−1}`. -/
noncomputable def secondOrderSol (β c : ℝ) (ym1 : Ω → ℝ) (z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => mu1 β c • ym1 + fwdPart 𝔼 β c z 0
  | t + 1 => mu1 β c • secondOrderSol β c ym1 z t + fwdPart 𝔼 β c z (t + 1)

/-- Woodford (2003), eq. (F.10), p. 714: `y_t = μ₁ y_{t−1} + F_t` at every date. -/
theorem secondOrderSol_eq (β c : ℝ) (ym1 : Ω → ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) :
    secondOrderSol 𝔼 β c ym1 z t =
      mu1 β c • lagged ym1 (secondOrderSol 𝔼 β c ym1 z) t + fwdPart 𝔼 β c z t := by
  cases t <;> rfl

/-- Woodford (2003), eq. (2.7), p. 489: the forward component in the printed form
`β⁻¹ ∑ⱼ μ₂^{−j−1} E_t z_{t+j}`. -/
theorem fwdPart_apply (β c : ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    fwdPart 𝔼 β c z t ω = β⁻¹ * ∑' j, (mu2 β c ^ (j + 1))⁻¹ * 𝔼.E t (z (t + j)) ω := by
  unfold fwdPart ExpectationSystem.forwardSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [ExpectationSystem.E_smul, Pi.smul_apply, smul_eq_mul, pow_succ, mul_inv, mul_inv,
    inv_pow]
  ring

/-- Woodford (2003), eq. (F.10), p. 714: the forward component is linear in the forcing,
`F[a z] = a F[z]`. -/
theorem fwdPart_smul (β c a : ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) :
    fwdPart 𝔼 β c (fun s => a • z s) t = a • fwdPart 𝔼 β c z t := by
  funext ω
  unfold fwdPart ExpectationSystem.forwardSeries
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [smul_smul, mul_comm (β * mu2 β c)⁻¹ a, ← smul_smul, map_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- Woodford (2003), eq. (2.7), p. 489 (**existence and uniqueness**): for `β > 0`, `c > 0`, a
bounded adapted forcing process `z` and a bounded `y_{−1}` known at date 0, the process (2.7)
is a bounded adapted solution, and it is the only one. -/
theorem secondOrder_existsUnique {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {z : ℕ → Ω → ℝ}
    (hz : BoundedProc z) (hza : 𝔼.Adapted z) {ym1 : Ω → ℝ} {K : ℝ}
    (hK : ∀ ω, |ym1 ω| ≤ K) (hm0 : 𝔼.E 0 ym1 = ym1) :
    SecondOrder 𝔼 β c ym1 z (secondOrderSol 𝔼 β c ym1 z) ∧
      BoundedProc (secondOrderSol 𝔼 β c ym1 z) ∧ 𝔼.Adapted (secondOrderSol 𝔼 β c ym1 z) ∧
      ∀ y, SecondOrder 𝔼 β c ym1 z y → BoundedProc y → 𝔼.Adapted y →
        y = secondOrderSol 𝔼 β c ym1 z := by
  obtain ⟨Mz, hMz⟩ := hz
  have hl2 : 1 < mu2 β c := one_lt_mu2 hβ hc
  have ha : |(mu2 β c)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (lt_trans one_pos hl2)]
    exact inv_lt_one_of_one_lt₀ hl2
  set u : ℕ → Ω → ℝ := fun t => (β * mu2 β c)⁻¹ • z t with hu
  have hub : ∀ t ω, |u t ω| ≤ |(β * mu2 β c)⁻¹| * Mz := fun t ω => by
    simp only [hu, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hMz t ω) (abs_nonneg _)
  have hua : 𝔼.Adapted u := fun t => by simp only [hu, map_smul, hza t]
  have hFs := ForwardSolution.forwardSeries_solves_abs 𝔼 ha hub hua
  obtain ⟨BF, hBF⟩ := ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hub
  have hFa := ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hub
  set y := secondOrderSol 𝔼 β c ym1 z with hydef
  have hl1 := mu1_pos hβ hc
  have hl1' := mu1_lt_one hβ hc
  have hadapt : 𝔼.Adapted y := by
    intro t
    induction t with
    | zero =>
      change 𝔼.E 0 (mu1 β c • ym1 + fwdPart 𝔼 β c z 0) = _
      rw [map_add, map_smul, hm0]
      exact congrArg _ (hFa 0)
    | succ t ih =>
      change 𝔼.E (t + 1) (mu1 β c • y t + fwdPart 𝔼 β c z (t + 1))
        = mu1 β c • y t + fwdPart 𝔼 β c z (t + 1)
      rw [map_add, map_smul, ← ih, 𝔼.known (Nat.le_succ t), ih]
      congr 1
      exact hFa (t + 1)
  have hbdd : BoundedProc y := by
    set B := max K (BF / (1 - mu1 β c)) with hB
    have hKB : K ≤ B := le_max_left _ _
    have hFB : BF ≤ (1 - mu1 β c) * B := by
      have := le_max_right K (BF / (1 - mu1 β c))
      rw [← hB, div_le_iff₀ (by linarith)] at this
      linarith
    refine ⟨B, fun t => ?_⟩
    induction t with
    | zero =>
      intro ω
      have e : y 0 ω = mu1 β c * ym1 ω + 𝔼.forwardSeries (mu2 β c)⁻¹ u 0 ω := rfl
      rw [e]
      have h1 : |mu1 β c * ym1 ω| ≤ mu1 β c * B := by
        rw [abs_mul, abs_of_pos hl1]
        exact mul_le_mul_of_nonneg_left ((hK ω).trans hKB) hl1.le
      calc |mu1 β c * ym1 ω + 𝔼.forwardSeries (mu2 β c)⁻¹ u 0 ω|
          ≤ |mu1 β c * ym1 ω| + |𝔼.forwardSeries (mu2 β c)⁻¹ u 0 ω| := abs_add_le _ _
        _ ≤ mu1 β c * B + BF := add_le_add h1 (hBF 0 ω)
        _ ≤ B := by linarith
    | succ t ih =>
      intro ω
      have e : y (t + 1) ω = mu1 β c * y t ω + 𝔼.forwardSeries (mu2 β c)⁻¹ u (t + 1) ω := rfl
      rw [e]
      have h1 : |mu1 β c * y t ω| ≤ mu1 β c * B := by
        rw [abs_mul, abs_of_pos hl1]
        exact mul_le_mul_of_nonneg_left (ih ω) hl1.le
      calc |mu1 β c * y t ω + 𝔼.forwardSeries (mu2 β c)⁻¹ u (t + 1) ω|
          ≤ |mu1 β c * y t ω| + |𝔼.forwardSeries (mu2 β c)⁻¹ u (t + 1) ω| := abs_add_le _ _
        _ ≤ mu1 β c * B + BF := add_le_add h1 (hBF (t + 1) ω)
        _ ≤ B := by linarith
  have hsol : SecondOrder 𝔼 β c ym1 z y :=
    secondOrder_of_factor 𝔼 hβ hc hadapt (e := 𝔼.forwardSeries (mu2 β c)⁻¹ u)
      (fun t => secondOrderSol_eq 𝔼 β c ym1 z t) (fun t => hFs t)
  exact ⟨hsol, hbdd, hadapt, fun y' h' hb' ha' =>
    secondOrder_unique 𝔼 hβ hc h' hsol ha' hadapt hb' hbdd⟩

/-- Woodford (2003), p. 527 and fn. 19, p. 490: two solutions (F.10) with different initial
values differ by a deterministic, geometrically vanishing component,
`y_t − y'_t = μ₁^{t+1}(y_{−1} − y'_{−1})`. -/
theorem secondOrderSol_sub (β c : ℝ) (ym1 ym1' : Ω → ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) :
    secondOrderSol 𝔼 β c ym1 z t - secondOrderSol 𝔼 β c ym1' z t =
      mu1 β c ^ (t + 1) • (ym1 - ym1') := by
  induction t with
  | zero =>
    change mu1 β c • ym1 + fwdPart 𝔼 β c z 0 - (mu1 β c • ym1' + fwdPart 𝔼 β c z 0) = _
    rw [zero_add, pow_one, smul_sub]
    abel
  | succ t ih =>
    change mu1 β c • secondOrderSol 𝔼 β c ym1 z t + fwdPart 𝔼 β c z (t + 1)
      - (mu1 β c • secondOrderSol 𝔼 β c ym1' z t + fwdPart 𝔼 β c z (t + 1)) = _
    rw [add_sub_add_right_eq_sub, ← smul_sub, ih, smul_smul, ← pow_succ']

/-! ### The model: aggregate supply (2.1) and the target criterion (5.1) -/

/-- Woodford (2003), eq. (5.1), p. 523: the target criterion
`π_t + (λ/κ)(x_t − x_{t−1}) = 0` at every date `t ≥ t₀`, with `x_{t₀−1} = xm1`. -/
def Crit (lam κ : ℝ) (xm1 : Ω → ℝ) (π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t + (lam / κ) • (x t - lagged xm1 x t) = 0

/-- Woodford (2003), eqs. (1.7)–(1.8), p. 470 (and p. 488 for the stochastic problem): the
first-order conditions `π_t + φ_t − φ_{t−1} = 0` and `λ(x_t − x*) − κφ_t = 0` for all `t ≥ t₀`,
with initial multiplier `φ_{t₀−1} = φm1`. -/
def FOC (lam κ xs : ℝ) (φm1 : Ω → ℝ) (π x φ : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t + φ t - lagged φm1 φ t = 0 ∧ ∀ ω, lam * (x t ω - xs) - κ * φ t ω = 0

/-- Woodford (2003), eq. (2.12), p. 491 (and (F.10), p. 714): the forward component
`β⁻¹ ∑ⱼ μ₂^{−j−1} E_t u_{t+j}` of the cost-push shock, with `μ₂` the larger root of (1.11) at
`c = κ²/λ`. -/
noncomputable def fwdU (β κ lam : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fwdPart 𝔼 β (κ ^ 2 / lam) u

/-- Woodford (2003), eq. (2.12), p. 491: `fwdU` in the printed form. -/
theorem fwdU_apply (β κ lam : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    fwdU 𝔼 β κ lam u t ω =
      β⁻¹ * ∑' j, (mu2 β (κ ^ 2 / lam) ^ (j + 1))⁻¹ * 𝔼.E t (u (t + j)) ω :=
  fwdPart_apply 𝔼 β _ u t ω

/-- Woodford (2003), eq. (F.10), p. 714: the output-gap process
`x_t = μ₁ x_{t−1} − (κ/λ) β⁻¹ ∑ⱼ μ₂^{−j−1} E_t u_{t+j}` started from `x_{t₀−1} = xm1`. -/
noncomputable def xStar (β κ lam : ℝ) (xm1 : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  secondOrderSol 𝔼 β (κ ^ 2 / lam) xm1 (fun t => -(κ / lam) • u t)

/-- Woodford (2003), App. F.5, p. 714: the inflation process obtained by substituting (F.10)
into (5.1), `π_t = (λ/κ)(x_{t−1} − x_t)`. -/
noncomputable def piStar (β κ lam : ℝ) (xm1 : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (lam / κ) • (lagged xm1 (xStar 𝔼 β κ lam xm1 u) t - xStar 𝔼 β κ lam xm1 u t)

/-- Woodford (2003), eq. (F.10), p. 714: `x_t = μ₁ x_{t−1} − (κ/λ) β⁻¹ ∑ⱼ μ₂^{−j−1} E_t u_{t+j}`. -/
theorem xStar_eq (β κ lam : ℝ) (xm1 : Ω → ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    xStar 𝔼 β κ lam xm1 u t = mu1 β (κ ^ 2 / lam) • lagged xm1 (xStar 𝔼 β κ lam xm1 u) t
      - (κ / lam) • fwdU 𝔼 β κ lam u t := by
  unfold xStar fwdU
  rw [secondOrderSol_eq, fwdPart_smul, neg_smul, sub_eq_add_neg]

/-- Woodford (2003), eq. (2.12), p. 491 (Proposition 7.7), for the equilibrium of (5.1):
`π_t = (1 − μ₁)(λ/κ) x_{t−1} + β⁻¹ ∑ⱼ μ₂^{−j−1} E_t u_{t+j}`. -/
theorem piStar_eq {κ lam : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0) (β : ℝ) (xm1 : Ω → ℝ)
    (u : ℕ → Ω → ℝ) (t : ℕ) :
    piStar 𝔼 β κ lam xm1 u t = ((1 - mu1 β (κ ^ 2 / lam)) * (lam / κ)) •
      lagged xm1 (xStar 𝔼 β κ lam xm1 u) t + fwdU 𝔼 β κ lam u t := by
  unfold piStar
  rw [xStar_eq 𝔼 β κ lam xm1 u t]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- Woodford (2003), App. F.5, p. 714 (the elimination step): pointwise, given
`π_t = (λ/κ)(x_{t−1} − x_t)` and `E_t π_{t+1} = (λ/κ)(x_t − E_t x_{t+1})`, the AS relation (2.1)
holds iff `β E_t x_{t+1} − (1 + β + κ²/λ) x_t + x_{t−1} = (κ/λ) u_t`. -/
theorem as_iff_secondOrder_real {β κ lam : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0)
    (xp x Ex u : ℝ) :
    lam / κ * (xp - x) = κ * x + β * (lam / κ * (x - Ex)) + u ↔
      β * Ex - (1 + β + κ ^ 2 / lam) * x + xp = -(-(κ / lam) * u) := by
  constructor
  · intro h
    field_simp at h ⊢
    linear_combination h
  · intro h
    field_simp at h ⊢
    linear_combination h

/-- Woodford (2003), App. F.5, p. 714: for an adapted output gap, (2.1) together with (5.1) is
equivalent to the second-order equation `β E_t x_{t+1} − (1 + β + κ²/λ) x_t + x_{t−1} =
(κ/λ) u_t` together with `π_t = (λ/κ)(x_{t−1} − x_t)`. -/
theorem as_crit_iff {β κ lam : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0) {xm1 : Ω → ℝ}
    {u π x : ℕ → Ω → ℝ} (hxa : 𝔼.Adapted x) :
    (AS 𝔼 β κ u π x ∧ Crit lam κ xm1 π x) ↔
      (SecondOrder 𝔼 β (κ ^ 2 / lam) xm1 (fun t => -(κ / lam) • u t) x ∧
        ∀ t, π t = (lam / κ) • (lagged xm1 x t - x t)) := by
  have hcrit : Crit lam κ xm1 π x ↔ ∀ t, π t = (lam / κ) • (lagged xm1 x t - x t) := by
    refine forall_congr' fun t => ?_
    constructor
    · intro h
      funext ω
      have := congrFun h ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
        at this ⊢
      linarith
    · intro h
      rw [h]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
      ring
  rw [hcrit]
  constructor
  · rintro ⟨hAS, hπ⟩
    refine ⟨fun t => ?_, hπ⟩
    have hE : 𝔼.E t (π (t + 1)) = (lam / κ) • (x t - 𝔼.E t (x (t + 1))) := by
      rw [hπ (t + 1), map_smul, map_sub, lagged_succ, hxa t]
    have h := hAS t
    rw [hE, hπ t] at h
    funext ω
    have h' := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.neg_apply] at h' ⊢
    exact (as_iff_secondOrder_real hκ hlam _ _ _ _).mp h'
  · rintro ⟨hSO, hπ⟩
    refine ⟨fun t => ?_, hπ⟩
    have hE : 𝔼.E t (π (t + 1)) = (lam / κ) • (x t - 𝔼.E t (x (t + 1))) := by
      rw [hπ (t + 1), map_smul, map_sub, lagged_succ, hxa t]
    rw [hE, hπ t]
    funext ω
    have h' := congrFun (hSO t) ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.neg_apply] at h' ⊢
    exact (as_iff_secondOrder_real hκ hlam _ _ _ _).mpr h'

/-- Woodford (2003), App. F.5, p. 714: the lag of an adapted process with a date-0-known
initial value is known at each date. -/
theorem lagged_adapted {xm1 : Ω → ℝ} {x : ℕ → Ω → ℝ} (hm0 : 𝔼.E 0 xm1 = xm1)
    (hxa : 𝔼.Adapted x) (t : ℕ) : 𝔼.E t (lagged xm1 x t) = lagged xm1 x t := by
  cases t with
  | zero => exact hm0
  | succ t =>
    rw [lagged_succ, ← hxa t, 𝔼.known (Nat.le_succ t)]

/-- Woodford (2003), App. F.5, p. 714: the lag of a bounded process with a bounded initial
value is bounded. -/
theorem lagged_bounded {xm1 : Ω → ℝ} {x : ℕ → Ω → ℝ} {K M : ℝ} (hK : ∀ ω, |xm1 ω| ≤ K)
    (hM : ∀ t ω, |x t ω| ≤ M) (t : ℕ) (ω : Ω) : |lagged xm1 x t ω| ≤ max K M := by
  cases t with
  | zero => exact (hK ω).trans (le_max_left _ _)
  | succ t => exact (hM t ω).trans (le_max_right _ _)

/-- Woodford (2003), **Proposition 7.15**, p. 523, determinacy part (App. F.5, p. 714): if the
central bank ensures (5.1) at every date `t ≥ t₀`, then for any bounded adapted cost-push
process `u` (otherwise unrestricted) and any bounded `x_{t₀−1}` known at `t₀`, the processes
`(π*, x*)` of (F.10) are a bounded adapted solution of (2.1) and (5.1), and they are the only
bounded adapted output-gap process (with its inflation) solving (2.1) and (5.1). -/
theorem prop_7_15 {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) {u : ℕ → Ω → ℝ}
    (hu : BoundedProc u) (hua : 𝔼.Adapted u) {xm1 : Ω → ℝ} {K : ℝ} (hK : ∀ ω, |xm1 ω| ≤ K)
    (hm0 : 𝔼.E 0 xm1 = xm1) :
    (AS 𝔼 β κ u (piStar 𝔼 β κ lam xm1 u) (xStar 𝔼 β κ lam xm1 u) ∧
      Crit lam κ xm1 (piStar 𝔼 β κ lam xm1 u) (xStar 𝔼 β κ lam xm1 u) ∧
      BoundedProc (piStar 𝔼 β κ lam xm1 u) ∧ BoundedProc (xStar 𝔼 β κ lam xm1 u) ∧
      𝔼.Adapted (piStar 𝔼 β κ lam xm1 u) ∧ 𝔼.Adapted (xStar 𝔼 β κ lam xm1 u)) ∧
    ∀ π x : ℕ → Ω → ℝ, AS 𝔼 β κ u π x → Crit lam κ xm1 π x → BoundedProc x → 𝔼.Adapted x →
      π = piStar 𝔼 β κ lam xm1 u ∧ x = xStar 𝔼 β κ lam xm1 u := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have hz : BoundedProc (fun t => -(κ / lam) • u t) := by
    obtain ⟨M, hM⟩ := hu
    refine ⟨|κ / lam| * M, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)
  have hza : 𝔼.Adapted (fun t => -(κ / lam) • u t) := fun t => by
    simp only [map_smul, hua t]
  obtain ⟨hSO, hbd, had, huniq⟩ := secondOrder_existsUnique 𝔼 hβ hc hz hza hK hm0
  change BoundedProc (xStar 𝔼 β κ lam xm1 u) at hbd
  change 𝔼.Adapted (xStar 𝔼 β κ lam xm1 u) at had
  have hpiA : 𝔼.Adapted (piStar 𝔼 β κ lam xm1 u) := fun t => by
    unfold piStar
    rw [map_smul, map_sub, lagged_adapted 𝔼 hm0 had t]
    exact congrArg _ (congrArg _ (had t))
  have hpiB : BoundedProc (piStar 𝔼 β κ lam xm1 u) := by
    obtain ⟨M, hM⟩ := hbd
    refine ⟨|lam / κ| * (max K M + M), fun t ω => ?_⟩
    unfold piStar
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
      (add_le_add (lagged_bounded hK hM t ω) (hM t ω))) (abs_nonneg _)
  have hboth := (as_crit_iff 𝔼 hκ.ne' hlam.ne' (xm1 := xm1) (u := u)
    (π := piStar 𝔼 β κ lam xm1 u) had).mpr ⟨hSO, fun t => rfl⟩
  refine ⟨⟨hboth.1, hboth.2, hpiB, hbd, hpiA, had⟩, fun π x hAS hC hxb hxa => ?_⟩
  obtain ⟨hSOx, hπ⟩ := (as_crit_iff 𝔼 hκ.ne' hlam.ne' hxa).mp ⟨hAS, hC⟩
  have hx : x = xStar 𝔼 β κ lam xm1 u := huniq x hSOx hxb hxa
  refine ⟨?_, hx⟩
  funext t
  rw [hπ t, hx]
  rfl

/-- Woodford (2003), App. F.5, p. 715: given the output-gap process, inflation is uniquely
determined by solving (2.1) forward, `π_t = ∑ₖ βᵏ E_t[κ x_{t+k} + u_{t+k}]`. -/
theorem piStar_eq_forward {β κ lam : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) {u : ℕ → Ω → ℝ} (hu : BoundedProc u) (hua : 𝔼.Adapted u) {xm1 : Ω → ℝ}
    {K : ℝ} (hK : ∀ ω, |xm1 ω| ≤ K) (hm0 : 𝔼.E 0 xm1 = xm1) :
    piStar 𝔼 β κ lam xm1 u =
      𝔼.forwardSeries β (fun t => κ • xStar 𝔼 β κ lam xm1 u t + u t) := by
  obtain ⟨⟨hAS, -, hpB, hxB, -, hxA⟩, -⟩ := prop_7_15 𝔼 hβ hκ hlam hu hua hK hm0
  obtain ⟨Mx, hMx⟩ := hxB
  obtain ⟨Mu, hMu⟩ := hu
  refine 𝔼.eq_forwardSeries hβ.le hβ1 (M := |κ| * Mx + Mu) (fun t ω => ?_) (fun t => ?_)
    (fun t => ?_) hpB
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hMu t ω))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMx t ω) (abs_nonneg _)
  · simp only [map_add, map_smul, hxA t, hua t]
  · rw [hAS t]
    abel

/-! ### Lagrangian sufficiency (survey §4.4)

A plan satisfying the first-order conditions (1.7)–(1.8) with bounded adapted multipliers
minimises the expected discounted loss among all bounded adapted plans satisfying (2.1) with the
same initial constraint. The proof is the exact identity `loss_eq_add`: the loss of any feasible
plan equals the loss of the FOC plan plus the expected discounted loss of the difference. -/

/-- Woodford (2003), eq. (1.2), p. 469: the period loss `π_t² + λ(x_t − x*)²`. -/
def periodLoss (lam xs : ℝ) (π x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => π t ω ^ 2 + lam * (x t ω - xs) ^ 2

/-- Woodford (2003), eq. (1.2), p. 469, and the expected value minimised in §2.1, p. 488: the
expected discounted loss `E_{t₀} ∑_{t ≥ t₀} β^{t−t₀} [π_t² + λ(x_t − x*)²]` conditional on
date-`t₀` information, written `∑_t βᵗ E_{t₀}[π_t² + λ(x_t − x*)²]` (for bounded plans the two
coincide by `ExpectationSystem.E_tsum`). -/
noncomputable def loss (β lam xs : ℝ) (π x : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑' t, β ^ t * 𝔼.E 0 (periodLoss lam xs π x t) ω

/-- Woodford (2003), eq. (1.2), p. 469: the period loss of a bounded plan is bounded. -/
theorem abs_periodLoss_le {lam xs A B : ℝ} {π x : ℕ → Ω → ℝ} (hA : ∀ t ω, |π t ω| ≤ A)
    (hB : ∀ t ω, |x t ω| ≤ B) (t : ℕ) (ω : Ω) :
    |periodLoss lam xs π x t ω| ≤ A ^ 2 + |lam| * (B + |xs|) ^ 2 := by
  unfold periodLoss
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hA t ω) 2
  · rw [abs_mul, abs_pow]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add (hB t ω) le_rfl)) 2

/-- Woodford (2003), eq. (1.2), p. 469: the period loss is nonnegative when `λ ≥ 0`. -/
theorem periodLoss_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (xs : ℝ) (π x : ℕ → Ω → ℝ) (t : ℕ) :
    0 ≤ periodLoss lam xs π x t := fun ω => by
  unfold periodLoss
  positivity

/-- Woodford (2003), eq. (1.2), p. 469: the expected discounted loss is nonnegative. -/
theorem loss_nonneg {β lam : ℝ} (hβ0 : 0 ≤ β) (hlam : 0 ≤ lam) (xs : ℝ) (π x : ℕ → Ω → ℝ)
    (ω : Ω) : 0 ≤ loss 𝔼 β lam xs π x ω := by
  refine tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ0 t) ?_
  have h := 𝔼.mono 0 (periodLoss_nonneg hlam xs π x t) ω
  simpa using h

/-- Woodford (2003), §2.1, pp. 488–489 (the Lagrangian method, made exact): **the loss
identity**. Let `(π°, x°)` satisfy (2.1) and the first-order conditions (1.7)–(1.8) with bounded
adapted multipliers `φ`, and let `(π, x)` be any bounded plan satisfying (2.1) with
`φ_{t₀−1}(π_{t₀} − π°_{t₀}) = 0` (the initial constraints coincide, or `φ_{t₀−1} = 0`). Given the
pull-out property, the loss of `(π, x)` equals the loss of `(π°, x°)` plus the expected
discounted loss `∑ βᵗ E_{t₀}[(π_t − π°_t)² + λ(x_t − x°_t)²]` of the difference. The cross terms
telescope by the law of iterated expectations (`E_{t₀}[φ_t E_t π_{t+1}] = E_{t₀}[φ_t π_{t+1}]`,
p. 488). -/
theorem loss_eq_add {β κ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hpo : 𝔼.PullOut)
    {u π x πo xo φ : ℕ → Ω → ℝ} {φm1 : Ω → ℝ}
    (hAS : AS 𝔼 β κ u π x) (hASo : AS 𝔼 β κ u πo xo) (hfoc : FOC lam κ xs φm1 πo xo φ)
    (hφa : 𝔼.Adapted φ) (hφb : BoundedProc φ) (hinit : φm1 * (π 0 - πo 0) = 0)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (hπob : BoundedProc πo)
    (hxob : BoundedProc xo) (ω : Ω) :
    loss 𝔼 β lam xs π x ω = loss 𝔼 β lam xs πo xo ω + loss 𝔼 β lam 0 (π - πo) (x - xo) ω := by
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mπo, hMπo⟩ := hπob
  obtain ⟨Mxo, hMxo⟩ := hxob
  obtain ⟨Mφ, hMφ⟩ := hφb
  set a : ℕ → Ω → ℝ := fun t => 𝔼.E 0 (lagged φm1 φ t * (π - πo) t) with ha
  -- the per-date identity
  have hpt : ∀ t, 𝔼.E 0 (periodLoss lam xs π x t) = 𝔼.E 0 (periodLoss lam xs πo xo t)
      + (2 : ℝ) • a t - (2 * β) • a (t + 1) + 𝔼.E 0 (periodLoss lam 0 (π - πo) (x - xo) t) := by
    intro t
    have hfun : periodLoss lam xs π x t = periodLoss lam xs πo xo t
        + (2 : ℝ) • (lagged φm1 φ t * (π - πo) t)
        - (2 * β) • (φ t * 𝔼.E t ((π - πo) (t + 1)))
        + periodLoss lam 0 (π - πo) (x - xo) t := by
      funext ω
      have e17 := congrFun (hfoc t).1 ω
      have e18 := (hfoc t).2 ω
      have eAS := congrFun (hAS t) ω
      have eASo := congrFun (hASo t) ω
      simp only [periodLoss, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
        smul_eq_mul, Pi.zero_apply, map_sub] at e17 eAS eASo ⊢
      linear_combination 2 * (π t ω - πo t ω) * e17 + 2 * (x t ω - xo t ω) * e18
        - 2 * φ t ω * (eAS - eASo)
    have hkey : 𝔼.E 0 (φ t * 𝔼.E t ((π - πo) (t + 1))) = a (t + 1) := by
      rw [← hpo t (φ t) ((π - πo) (t + 1)) (hφa t), 𝔼.tower (Nat.zero_le t)]
      rfl
    rw [hfun, map_add, map_sub, map_add, map_smul, map_smul, hkey]
  -- bounds
  have hdπ : ∀ t ω, |(π - πo) t ω| ≤ Mπ + Mπo := fun t ω => by
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hMπ t ω) (hMπo t ω))
  have hdx : ∀ t ω, |(x - xo) t ω| ≤ Mx + Mxo := fun t ω => by
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hMx t ω) (hMxo t ω))
  have hS1 := summable_disc hβ0 hβ1 (fun t =>
    𝔼.abs_E_le (abs_periodLoss_le (lam := lam) (xs := xs) hMπ hMx t) 0 ω)
  have hS2 := summable_disc hβ0 hβ1 (fun t =>
    𝔼.abs_E_le (abs_periodLoss_le (lam := lam) (xs := xs) hMπo hMxo t) 0 ω)
  have hS3 := summable_disc hβ0 hβ1 (fun t =>
    𝔼.abs_E_le (abs_periodLoss_le (lam := lam) (xs := 0) hdπ hdx t) 0 ω)
  -- the telescoping terms
  set A : ℕ → ℝ := fun t => β ^ t * a t ω with hA
  have hA0 : A 0 = 0 := by
    simp only [hA, ha, pow_zero, one_mul, lagged_zero]
    change 𝔼.E 0 (φm1 * (π 0 - πo 0)) ω = 0
    rw [hinit, map_zero]
    rfl
  have hC : 0 ≤ Mφ * (Mπ + Mπo) :=
    mul_nonneg ((abs_nonneg _).trans (hMφ 0 ω)) ((abs_nonneg _).trans (hdπ 0 ω))
  have hab : ∀ t, |a t ω| ≤ Mφ * (Mπ + Mπo) := by
    intro t
    cases t with
    | zero =>
      have : a 0 ω = 0 := by simpa [hA] using hA0
      rw [this, abs_zero]
      exact hC
    | succ t =>
      refine 𝔼.abs_E_le (fun ω' => ?_) 0 ω
      simp only [Pi.mul_apply, lagged_succ, abs_mul]
      exact mul_le_mul (hMφ t ω') (hdπ (t + 1) ω') (abs_nonneg _)
        ((abs_nonneg _).trans (hMφ 0 ω))
  have hAlim : Tendsto A atTop (𝓝 0) := by
    have hg : Tendsto (fun t : ℕ => β ^ t * (Mφ * (Mπ + Mπo))) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (Mφ * (Mπ + Mπo))
    refine squeeze_zero_norm (fun t => ?_) hg
    rw [Real.norm_eq_abs, hA, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hab t) (pow_nonneg hβ0 t)
  -- partial sums
  have hterm : ∀ t, β ^ t * 𝔼.E 0 (periodLoss lam xs π x t) ω =
      β ^ t * 𝔼.E 0 (periodLoss lam xs πo xo t) ω + 2 * (A t - A (t + 1))
        + β ^ t * 𝔼.E 0 (periodLoss lam 0 (π - πo) (x - xo) t) ω := by
    intro t
    rw [hpt t]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hA, pow_succ]
    ring
  have hpartial : ∀ N, ∑ t ∈ Finset.range N, β ^ t * 𝔼.E 0 (periodLoss lam xs π x t) ω =
      ∑ t ∈ Finset.range N, β ^ t * 𝔼.E 0 (periodLoss lam xs πo xo t) ω + 2 * (A 0 - A N)
        + ∑ t ∈ Finset.range N, β ^ t * 𝔼.E 0 (periodLoss lam 0 (π - πo) (x - xo) t) ω := by
    intro N
    rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub']
  have hlim : Tendsto (fun N => ∑ t ∈ Finset.range N, β ^ t * 𝔼.E 0 (periodLoss lam xs π x t) ω)
      atTop (𝓝 (loss 𝔼 β lam xs πo xo ω + 2 * (A 0 - 0) + loss 𝔼 β lam 0 (π - πo) (x - xo) ω)) := by
    simp only [hpartial]
    exact (hS2.hasSum.tendsto_sum_nat.add (tendsto_const_nhds.mul
      (tendsto_const_nhds.sub hAlim))).add hS3.hasSum.tendsto_sum_nat
  have := tendsto_nhds_unique hS1.hasSum.tendsto_sum_nat hlim
  rw [hA0] at this
  change loss 𝔼 β lam xs π x ω = _ at this
  rw [this]
  ring

/-- Woodford (2003), §2.1, p. 489 (sufficiency): under the hypotheses of `loss_eq_add` with
`λ ≥ 0`, the FOC plan has no larger loss than any other feasible plan. -/
theorem loss_le_of_foc {β κ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hlam : 0 ≤ lam)
    (hpo : 𝔼.PullOut) {u π x πo xo φ : ℕ → Ω → ℝ} {φm1 : Ω → ℝ}
    (hAS : AS 𝔼 β κ u π x) (hASo : AS 𝔼 β κ u πo xo) (hfoc : FOC lam κ xs φm1 πo xo φ)
    (hφa : 𝔼.Adapted φ) (hφb : BoundedProc φ) (hinit : φm1 * (π 0 - πo 0) = 0)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (hπob : BoundedProc πo)
    (hxob : BoundedProc xo) (ω : Ω) :
    loss 𝔼 β lam xs πo xo ω ≤ loss 𝔼 β lam xs π x ω := by
  rw [loss_eq_add 𝔼 hβ0 hβ1 hpo hAS hASo hfoc hφa hφb hinit hπb hxb hπob hxob ω]
  linarith [loss_nonneg 𝔼 hβ0 hlam 0 (π - πo) (x - xo) ω]

/-- Woodford (2003), §2.1, p. 489 (uniqueness of the optimum): the expectation `E_{t₀}` is
*faithful* if a nonnegative random variable with zero conditional expectation is zero. Perfect
foresight is faithful (`perfectForesight_faithful`); for a general conditional expectation the
optimum is unique only up to events of zero conditional probability. -/
def Faithful : Prop := ∀ y : Ω → ℝ, 0 ≤ y → 𝔼.E 0 y = 0 → y = 0

/-- Woodford (2003), p. 469 (the deterministic problem): perfect foresight is faithful. -/
theorem perfectForesight_faithful : Faithful perfectForesight := fun _ _ h => h

/-- Woodford (2003), §2.1, p. 489: with a faithful `E_{t₀}`, `β > 0` and `λ > 0`, a bounded
difference plan with zero expected discounted loss is zero. -/
theorem eq_zero_of_loss_eq_zero {β lam : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hf : Faithful 𝔼) {dπ dx : ℕ → Ω → ℝ} (hπb : BoundedProc dπ) (hxb : BoundedProc dx)
    (h0 : ∀ ω, loss 𝔼 β lam 0 dπ dx ω = 0) : dπ = 0 ∧ dx = 0 := by
  obtain ⟨A, hA⟩ := hπb
  obtain ⟨B, hB⟩ := hxb
  have hq : ∀ t, 𝔼.E 0 (periodLoss lam 0 dπ dx t) = 0 := by
    intro t
    funext ω
    have hS := summable_disc hβ.le hβ1 (fun s =>
      𝔼.abs_E_le (abs_periodLoss_le (lam := lam) (xs := 0) hA hB s) 0 ω)
    have hnn : ∀ s, 0 ≤ β ^ s * 𝔼.E 0 (periodLoss lam 0 dπ dx s) ω := fun s =>
      mul_nonneg (pow_nonneg hβ.le s) (by
        have h := 𝔼.mono 0 (periodLoss_nonneg hlam.le 0 dπ dx s) ω
        simpa using h)
    have hsum : HasSum (fun s => β ^ s * 𝔼.E 0 (periodLoss lam 0 dπ dx s) ω) 0 := by
      have := hS.hasSum
      rwa [show (∑' s, β ^ s * 𝔼.E 0 (periodLoss lam 0 dπ dx s) ω) = 0 from h0 ω] at this
    have hz := congrFun ((hasSum_zero_iff_of_nonneg hnn).mp hsum) t
    simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ.ne', false_and, false_or] at hz
    exact hz
  have hpt : ∀ t ω, dπ t ω = 0 ∧ dx t ω = 0 := by
    intro t ω
    have := congrFun (hf _ (periodLoss_nonneg hlam.le 0 dπ dx t) (hq t)) ω
    simp only [periodLoss, Pi.zero_apply, sub_zero] at this
    have h1 : dπ t ω ^ 2 = 0 := by nlinarith [sq_nonneg (dπ t ω), sq_nonneg (dx t ω)]
    have h2 : dx t ω ^ 2 = 0 := by nlinarith [sq_nonneg (dπ t ω), sq_nonneg (dx t ω)]
    exact ⟨pow_eq_zero_iff (two_ne_zero) |>.mp h1, pow_eq_zero_iff (two_ne_zero) |>.mp h2⟩
  exact ⟨funext fun t => funext fun ω => (hpt t ω).1, funext fun t => funext fun ω => (hpt t ω).2⟩

/-- Woodford (2003), §2.1, p. 489 (uniqueness): with a faithful `E_{t₀}`, a feasible plan whose
loss is nowhere larger than the FOC plan's coincides with it. -/
theorem eq_of_loss_le {β κ lam xs : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hpo : 𝔼.PullOut) (hf : Faithful 𝔼) {u π x πo xo φ : ℕ → Ω → ℝ} {φm1 : Ω → ℝ}
    (hAS : AS 𝔼 β κ u π x) (hASo : AS 𝔼 β κ u πo xo) (hfoc : FOC lam κ xs φm1 πo xo φ)
    (hφa : 𝔼.Adapted φ) (hφb : BoundedProc φ) (hinit : φm1 * (π 0 - πo 0) = 0)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (hπob : BoundedProc πo)
    (hxob : BoundedProc xo) (hle : ∀ ω, loss 𝔼 β lam xs π x ω ≤ loss 𝔼 β lam xs πo xo ω) :
    π = πo ∧ x = xo := by
  have h0 : ∀ ω, loss 𝔼 β lam 0 (π - πo) (x - xo) ω = 0 := fun ω => by
    have e := loss_eq_add 𝔼 hβ.le hβ1 hpo hAS hASo hfoc hφa hφb hinit hπb hxb hπob hxob ω
    have := loss_nonneg 𝔼 hβ.le hlam.le 0 (π - πo) (x - xo) ω
    linarith [hle ω]
  have hdb : ∀ {p q : ℕ → Ω → ℝ}, BoundedProc p → BoundedProc q → BoundedProc (p - q) := by
    intro p q ⟨M, hM⟩ ⟨M', hM'⟩
    exact ⟨M + M', fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hM t ω) (hM' t ω))⟩
  obtain ⟨h1, h2⟩ := eq_zero_of_loss_eq_zero 𝔼 hβ hβ1 hlam hf (hdb hπb hπob) (hdb hxb hxob) h0
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

/-! ### The constrained and unconstrained (t₀-optimal) problems -/

/-- Woodford (2003), §2.1, p. 488: a plan is *feasible* (without initial constraint) if it is
bounded, adapted and satisfies (2.1) at every date `t ≥ t₀`. -/
def FeasibleFree (β κ : ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  BoundedProc π ∧ BoundedProc x ∧ 𝔼.Adapted π ∧ 𝔼.Adapted x ∧ AS 𝔼 β κ u π x

/-- Woodford (2003), eq. (2.8), p. 489: a feasible plan satisfying the initial constraint
`π_{t₀} = π̄_{t₀}`. -/
def Feasible (β κ : ℝ) (u : ℕ → Ω → ℝ) (πbar : Ω → ℝ) (π x : ℕ → Ω → ℝ) : Prop :=
  FeasibleFree 𝔼 β κ u π x ∧ π 0 = πbar

/-- Woodford (2003), §2.1, p. 489: `(π, x)` solves the problem of minimising the expected
discounted loss (1.2) subject to (2.1) and the initial constraint (2.8), state by state. -/
def IsConstrainedOpt (β κ lam xs : ℝ) (u : ℕ → Ω → ℝ) (πbar : Ω → ℝ) (π x : ℕ → Ω → ℝ) :
    Prop :=
  Feasible 𝔼 β κ u πbar π x ∧ ∀ π' x', Feasible 𝔼 β κ u πbar π' x' →
    ∀ ω, loss 𝔼 β lam xs π x ω ≤ loss 𝔼 β lam xs π' x' ω

/-- Woodford (2003), §2.1, p. 488: `(π, x)` is the `t₀`-optimal commitment (minimises the
expected discounted loss subject to (2.1) only). -/
def IsT0Opt (β κ lam xs : ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  FeasibleFree 𝔼 β κ u π x ∧ ∀ π' x', FeasibleFree 𝔼 β κ u π' x' →
    ∀ ω, loss 𝔼 β lam xs π x ω ≤ loss 𝔼 β lam xs π' x' ω

/-- Woodford (2003), §2.1, p. 489 (**sufficiency**, constrained problem): a feasible plan that
satisfies (1.7)–(1.8) with bounded adapted multipliers (any `φ_{t₀−1}`) is a solution of the
constrained problem (2.8). -/
theorem isConstrainedOpt_of_foc {β κ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hlam : 0 ≤ lam)
    (hpo : 𝔼.PullOut) {u πo xo φ : ℕ → Ω → ℝ} {φm1 πbar : Ω → ℝ}
    (hF : Feasible 𝔼 β κ u πbar πo xo) (hfoc : FOC lam κ xs φm1 πo xo φ) (hφa : 𝔼.Adapted φ)
    (hφb : BoundedProc φ) : IsConstrainedOpt 𝔼 β κ lam xs u πbar πo xo := by
  refine ⟨hF, fun π x hF' ω => ?_⟩
  have hinit : φm1 * (π 0 - πo 0) = 0 := by rw [hF'.2, hF.2, sub_self, mul_zero]
  exact loss_le_of_foc 𝔼 hβ0 hβ1 hlam hpo hF'.1.2.2.2.2 hF.1.2.2.2.2 hfoc hφa hφb hinit
    hF'.1.1 hF'.1.2.1 hF.1.1 hF.1.2.1 ω

/-- Woodford (2003), eq. (2.5), p. 488 (**sufficiency**, `t₀`-optimal problem): a feasible plan
satisfying (1.7)–(1.8) with `φ_{t₀−1} = 0` is the `t₀`-optimal commitment. -/
theorem isT0Opt_of_foc {β κ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hlam : 0 ≤ lam)
    (hpo : 𝔼.PullOut) {u πo xo φ : ℕ → Ω → ℝ} (hF : FeasibleFree 𝔼 β κ u πo xo)
    (hfoc : FOC lam κ xs 0 πo xo φ) (hφa : 𝔼.Adapted φ) (hφb : BoundedProc φ) :
    IsT0Opt 𝔼 β κ lam xs u πo xo :=
  ⟨hF, fun _ _ hF' ω => loss_le_of_foc 𝔼 hβ0 hβ1 hlam hpo hF'.2.2.2.2 hF.2.2.2.2 hfoc hφa hφb
    (zero_mul _) hF'.1 hF'.2.1 hF.1 hF.2.1 ω⟩

/-- Woodford (2003), §2.1, p. 489 (**uniqueness**, constrained problem): with a faithful
`E_{t₀}`, every solution of the constrained problem coincides with the FOC plan. -/
theorem eq_of_isConstrainedOpt {β κ lam xs : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hpo : 𝔼.PullOut) (hf : Faithful 𝔼) {u π x πo xo φ : ℕ → Ω → ℝ} {φm1 πbar : Ω → ℝ}
    (hopt : IsConstrainedOpt 𝔼 β κ lam xs u πbar π x) (hF : Feasible 𝔼 β κ u πbar πo xo)
    (hfoc : FOC lam κ xs φm1 πo xo φ) (hφa : 𝔼.Adapted φ) (hφb : BoundedProc φ) :
    π = πo ∧ x = xo := by
  have hinit : φm1 * (π 0 - πo 0) = 0 := by rw [hopt.1.2, hF.2, sub_self, mul_zero]
  exact eq_of_loss_le 𝔼 hβ hβ1 hlam hpo hf hopt.1.1.2.2.2.2 hF.1.2.2.2.2 hfoc hφa hφb hinit
    hopt.1.1.1 hopt.1.1.2.1 hF.1.1 hF.1.2.1 (hopt.2 πo xo hF)

/-- Woodford (2003), eq. (2.5), p. 488 (**uniqueness**, `t₀`-optimal problem): with a faithful
`E_{t₀}`, every `t₀`-optimal plan coincides with the FOC plan with `φ_{t₀−1} = 0`. -/
theorem eq_of_isT0Opt {β κ lam xs : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hpo : 𝔼.PullOut) (hf : Faithful 𝔼) {u π x πo xo φ : ℕ → Ω → ℝ}
    (hopt : IsT0Opt 𝔼 β κ lam xs u π x) (hF : FeasibleFree 𝔼 β κ u πo xo)
    (hfoc : FOC lam κ xs 0 πo xo φ) (hφa : 𝔼.Adapted φ) (hφb : BoundedProc φ) :
    π = πo ∧ x = xo :=
  eq_of_loss_le 𝔼 hβ hβ1 hlam hpo hf hopt.1.2.2.2.2 hF.2.2.2.2 hfoc hφa hφb (zero_mul _)
    hopt.1.1 hopt.1.2.1 hF.1 hF.2.1 (hopt.2 πo xo hF)

/-! ### Eliminating the multiplier: (5.1) and (5.2) -/

/-- Woodford (2003), eq. (1.8), p. 470: the multiplier is pinned down by the output gap,
`φ_t = (λ/κ)(x_t − x*)`. -/
theorem foc_phi_eq {lam κ xs : ℝ} (hκ : κ ≠ 0) {φm1 : Ω → ℝ} {π x φ : ℕ → Ω → ℝ}
    (hfoc : FOC lam κ xs φm1 π x φ) (t : ℕ) (ω : Ω) : φ t ω = lam / κ * (x t ω - xs) := by
  have h := (hfoc t).2 ω
  field_simp
  linarith

/-- Woodford (2003), eq. (5.1), p. 523 (**elimination of φ**): if (1.7)–(1.8) hold for all
`t ≥ t₀` (for any initial multiplier `φ_{t₀−1}`), then (5.1) holds at every `t ≥ t₀ + 1`. -/
theorem crit_succ_of_foc {lam κ xs : ℝ} (hκ : κ ≠ 0) {φm1 : Ω → ℝ} {π x φ : ℕ → Ω → ℝ}
    (hfoc : FOC lam κ xs φm1 π x φ) (t : ℕ) :
    π (t + 1) + (lam / κ) • (x (t + 1) - x t) = 0 := by
  funext ω
  have h := congrFun (hfoc (t + 1)).1 ω
  simp only [Pi.add_apply, Pi.sub_apply, lagged_succ, Pi.zero_apply] at h
  rw [foc_phi_eq hκ hfoc, foc_phi_eq hκ hfoc] at h
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
  linear_combination h

/-- Woodford (2003), p. 523: (5.1) need not hold at `t = t₀`. Under (1.7)–(1.8), (5.1) holds at
`t₀` iff the initial multiplier is `φ_{t₀−1} = (λ/κ)(x_{t₀−1} − x*)`, eq. (5.2); in particular
the `t₀`-optimal plan (`φ_{t₀−1} = 0`) violates (5.1) at `t₀` unless `x_{t₀−1} = x*`. -/
theorem crit_zero_iff_of_foc {lam κ xs : ℝ} (hκ : κ ≠ 0) {φm1 xm1 : Ω → ℝ}
    {π x φ : ℕ → Ω → ℝ} (hfoc : FOC lam κ xs φm1 π x φ) :
    π 0 + (lam / κ) • (x 0 - xm1) = 0 ↔ φm1 = fun ω => lam / κ * (xm1 ω - xs) := by
  have h := (hfoc 0).1
  constructor
  · intro hc
    funext ω
    have h1 := congrFun h ω
    have h2 := congrFun hc ω
    simp only [Pi.add_apply, Pi.sub_apply, lagged_zero, Pi.zero_apply, Pi.smul_apply,
      smul_eq_mul] at h1 h2
    rw [foc_phi_eq hκ hfoc] at h1
    linear_combination h2 - h1
  · intro hm
    funext ω
    have h1 := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, lagged_zero, Pi.zero_apply, Pi.smul_apply,
      smul_eq_mul, hm] at h1 ⊢
    rw [foc_phi_eq hκ hfoc] at h1
    linear_combination h1

/-- Woodford (2003), eq. (5.2), p. 524: (5.1) at every `t ≥ t₀` is **equivalent** to (1.7)–(1.8)
at every `t ≥ t₀` with the initial multiplier `φ_{t₀−1} = (λ/κ)(x_{t₀−1} − x*)` (the multiplier
is then `φ_t = (λ/κ)(x_t − x*)`). -/
theorem crit_iff_foc {lam κ : ℝ} (hκ : κ ≠ 0) (xs : ℝ) {xm1 : Ω → ℝ} {π x : ℕ → Ω → ℝ} :
    Crit lam κ xm1 π x ↔ FOC lam κ xs (fun ω => lam / κ * (xm1 ω - xs)) π x
      (fun t ω => lam / κ * (x t ω - xs)) := by
  constructor
  · intro hC t
    refine ⟨?_, fun ω => by field_simp; ring⟩
    funext ω
    have h := congrFun (hC t) ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
    cases t with
    | zero => simp only [lagged_zero] at h ⊢; linear_combination h
    | succ t => simp only [lagged_succ] at h ⊢; linear_combination h
  · intro hF t
    funext ω
    have h := congrFun (hF t).1 ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
    cases t with
    | zero => simp only [lagged_zero] at h ⊢; linear_combination h
    | succ t => simp only [lagged_succ] at h ⊢; linear_combination h

/-- Woodford (2003), App. F.5, p. 714: an affine transformation `a(x_t − b)` of an adapted
process is adapted. -/
theorem affine_adapted (a b : ℝ) {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) :
    𝔼.Adapted (fun t ω => a * (x t ω - b)) := by
  intro t
  have e : (fun ω => a * (x t ω - b)) = a • x t - (fun _ => a * b) := by
    funext ω; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  change 𝔼.E t (fun ω => a * (x t ω - b)) = fun ω => a * (x t ω - b)
  rw [e, map_sub, map_smul, 𝔼.const, hx t]

/-- Woodford (2003), App. F.5, p. 714: an affine transformation of a bounded process is
bounded. -/
theorem affine_bounded (a b : ℝ) {x : ℕ → Ω → ℝ} (hx : BoundedProc x) :
    BoundedProc (fun t ω => a * (x t ω - b)) := by
  obtain ⟨M, hM⟩ := hx
  refine ⟨|a| * (M + |b|), fun t ω => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hM t ω) le_rfl))
    (abs_nonneg _)

/-! ### Proposition 7.15: optimality and identification with Proposition 7.7 -/

/-- Woodford (2003), eq. (2.11), p. 490: the self-consistent initial constraint
`π̄_{t₀} = (1 − μ₁)(λ/κ) x_{t₀−1} + β⁻¹ ∑ⱼ μ₂^{−j−1} E_{t₀} u_{t₀+j}`. -/
noncomputable def eq211 (β κ lam : ℝ) (u : ℕ → Ω → ℝ) (xm1 : Ω → ℝ) : Ω → ℝ :=
  ((1 - mu1 β (κ ^ 2 / lam)) * (lam / κ)) • xm1 + fwdU 𝔼 β κ lam u 0

/-- Woodford (2003), **Proposition 7.15**, p. 523 (optimality): every bounded adapted solution
of (2.1) and (5.1) (with `x_{t₀−1}` bounded and known at `t₀`) solves the problem of Proposition
7.7 — it minimises the expected discounted loss (1.2), for any target `x*`, among all bounded
adapted plans satisfying (2.1) and the initial constraint (2.8) with `π̄_{t₀}` given by (2.11).
The multiplier is `φ_t = (λ/κ)(x_t − x*)` with `φ_{t₀−1}` given by (5.2). -/
theorem crit_isConstrainedOpt {β κ lam : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hpo : 𝔼.PullOut) (xs : ℝ) {u : ℕ → Ω → ℝ} (hu : BoundedProc u)
    (hua : 𝔼.Adapted u) {xm1 : Ω → ℝ} {K : ℝ} (hK : ∀ ω, |xm1 ω| ≤ K)
    (hm0 : 𝔼.E 0 xm1 = xm1) {π x : ℕ → Ω → ℝ} (hAS : AS 𝔼 β κ u π x)
    (hC : Crit lam κ xm1 π x) (hπb : BoundedProc π) (hxb : BoundedProc x)
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) :
    IsConstrainedOpt 𝔼 β κ lam xs u (eq211 𝔼 β κ lam u xm1) π x := by
  obtain ⟨-, huniq⟩ := prop_7_15 𝔼 hβ hκ hlam hu hua hK hm0
  obtain ⟨hπ, hx⟩ := huniq π x hAS hC hxb hxa
  have h0 : π 0 = eq211 𝔼 β κ lam u xm1 := by
    rw [hπ, piStar_eq 𝔼 hκ.ne' hlam.ne', lagged_zero]
    rfl
  exact isConstrainedOpt_of_foc 𝔼 hβ.le hβ1 hlam.le hpo ⟨⟨hπb, hxb, hπa, hxa, hAS⟩, h0⟩
    ((crit_iff_foc hκ.ne' xs).mp hC) (affine_adapted 𝔼 _ _ hxa) (affine_bounded _ _ hxb)

/-- Woodford (2003), **Proposition 7.15**, p. 523, and App. F.5, pp. 714–715 (identification
with Proposition 7.7, the "easily characterized" step filled via (5.2)): any bounded adapted plan
satisfying (2.1) and the first-order conditions (1.7)–(1.8) for some bounded initial multiplier
`φ_{t₀−1}` known at `t₀`, together with the initial constraint (2.11), *is* the equilibrium
`(π*, x*)` of the target criterion (5.1). (The initial constraint forces `φ_{t₀−1}` to be (5.2).) -/
theorem foc_eq211_eq_star {β κ lam xs : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    {u : ℕ → Ω → ℝ} (hu : BoundedProc u) (hua : 𝔼.Adapted u) {xm1 φm1 : Ω → ℝ} {K L : ℝ}
    (hK : ∀ ω, |xm1 ω| ≤ K) (hm0 : 𝔼.E 0 xm1 = xm1) (hL : ∀ ω, |φm1 ω| ≤ L)
    (hφ0 : 𝔼.E 0 φm1 = φm1) {π x φ : ℕ → Ω → ℝ} (hAS : AS 𝔼 β κ u π x)
    (hfoc : FOC lam κ xs φm1 π x φ) (hxb : BoundedProc x) (hxa : 𝔼.Adapted x)
    (h0 : π 0 = eq211 𝔼 β κ lam u xm1) :
    π = piStar 𝔼 β κ lam xm1 u ∧ x = xStar 𝔼 β κ lam xm1 u := by
  set c := κ ^ 2 / lam with hc_def
  have hc : 0 < c := by positivity
  obtain ⟨⟨hAS', hC', -, hxb', -, hxa'⟩, huniq⟩ := prop_7_15 𝔼 hβ hκ hlam hu hua hK hm0
  set ψm1 : Ω → ℝ := fun ω => lam / κ * (xm1 ω - xs) with hψm1
  set ψ : ℕ → Ω → ℝ := fun t ω => lam / κ * (xStar 𝔼 β κ lam xm1 u t ω - xs) with hψ
  have hfoc' : FOC lam κ xs ψm1 (piStar 𝔼 β κ lam xm1 u) (xStar 𝔼 β κ lam xm1 u) ψ :=
    (crit_iff_foc hκ.ne' xs).mp hC'
  -- any FOC plan: the multiplier solves (2.6)
  have hSO : ∀ {m : Ω → ℝ} {p y q : ℕ → Ω → ℝ}, AS 𝔼 β κ u p y → FOC lam κ xs m p y q →
      𝔼.Adapted y → SecondOrder 𝔼 β c m (fun t ω => -(κ * xs + u t ω)) q := by
    intro m p y q hA hF hya t
    have hqa : 𝔼.Adapted q := by
      have e : q = fun t ω => lam / κ * (y t ω - xs) := by
        funext t ω; exact foc_phi_eq hκ.ne' hF t ω
      rw [e]; exact affine_adapted 𝔼 _ _ hya
    have hp : ∀ s, p s = lagged m q s - q s := fun s => by
      funext ω
      have := congrFun (hF s).1 ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at this ⊢
      linarith
    have hEp : 𝔼.E t (p (t + 1)) = q t - 𝔼.E t (q (t + 1)) := by
      rw [hp (t + 1), map_sub, lagged_succ, hqa t]
    have hA' := hA t
    rw [hEp, hp t] at hA'
    funext ω
    have e1 := congrFun hA' ω
    have e2 := (hF t).2 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at e1 ⊢
    have e3 : y t ω = xs + κ / lam * q t ω := by field_simp; linarith
    rw [e3] at e1
    rw [hc_def]
    linear_combination e1
  have hS1 := hSO hAS hfoc hxa
  have hS2 := hSO hAS' hfoc' hxa'
  -- the difference of the multipliers solves the homogeneous equation
  set δ : Ω → ℝ := φm1 - ψm1 with hδ
  have hφa : 𝔼.Adapted φ := by
    have e : φ = fun t ω => lam / κ * (x t ω - xs) := by
      funext t ω; exact foc_phi_eq hκ.ne' hfoc t ω
    rw [e]; exact affine_adapted 𝔼 _ _ hxa
  have hφb : BoundedProc φ := by
    have e : φ = fun t ω => lam / κ * (x t ω - xs) := by
      funext t ω; exact foc_phi_eq hκ.ne' hfoc t ω
    rw [e]; exact affine_bounded _ _ hxb
  have hψa : 𝔼.Adapted ψ := affine_adapted 𝔼 _ _ hxa'
  have hψb : BoundedProc ψ := affine_bounded _ _ hxb'
  have hSd : SecondOrder 𝔼 β c δ 0 (φ - ψ) := by
    intro t
    have e1 := hS1 t
    have e2 := hS2 t
    have hpv : lagged δ (φ - ψ) t = lagged φm1 φ t - lagged ψm1 ψ t := by
      cases t <;> rfl
    rw [hpv]
    simp only [Pi.sub_apply, map_sub, smul_sub, Pi.zero_apply, neg_zero]
    rw [show β • 𝔼.E t (φ (t + 1)) - β • 𝔼.E t (ψ (t + 1)) - ((1 + β + c) • φ t
      - (1 + β + c) • ψ t) + (lagged φm1 φ t - lagged ψm1 ψ t) =
      (β • 𝔼.E t (φ (t + 1)) - (1 + β + c) • φ t + lagged φm1 φ t)
      - (β • 𝔼.E t (ψ (t + 1)) - (1 + β + c) • ψ t + lagged ψm1 ψ t) by abel, e1, e2, sub_self]
  have hδK : ∀ ω, |δ ω| ≤ L + |lam / κ| * (K + |xs|) := fun ω => by
    simp only [hδ, hψm1, Pi.sub_apply]
    refine (abs_sub _ _).trans (add_le_add (hL ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hK ω) le_rfl))
      (abs_nonneg _)
  have hδ0 : 𝔼.E 0 δ = δ := by
    have e : ψm1 = (lam / κ) • xm1 - (fun _ => lam / κ * xs) := by
      funext ω; simp only [hψm1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    simp only [hδ, map_sub, hφ0, e, map_smul, 𝔼.const, hm0]
  obtain ⟨-, -, -, hd⟩ := secondOrder_existsUnique 𝔼 hβ hc (z := 0) ⟨0, fun _ _ => by simp⟩
    (fun t => by simp) hδK hδ0
  have hdeq := hd (φ - ψ) hSd
    (by obtain ⟨M, hM⟩ := hφb; obtain ⟨M', hM'⟩ := hψb
        exact ⟨M + M', fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) (hM' t ω))⟩)
    (fun t => by simp only [Pi.sub_apply, map_sub, hφa t, hψa t])
  have hfz : fwdPart 𝔼 β c 0 0 = 0 := by
    have := fwdPart_smul 𝔼 β c 0 0 0
    simp only [zero_smul] at this
    rw [show (fun _ : ℕ => (0 : Ω → ℝ)) = 0 from rfl] at this
    exact this
  have hd0 : φ 0 - ψ 0 = mu1 β c • δ := by
    have := congrFun hdeq 0
    simp only [Pi.sub_apply] at this
    rw [this]
    change mu1 β c • δ + fwdPart 𝔼 β c 0 0 = _
    rw [hfz, add_zero]
  -- the initial constraint forces δ = 0
  have hπ0 : π 0 = piStar 𝔼 β κ lam xm1 u 0 := by
    rw [h0, piStar_eq 𝔼 hκ.ne' hlam.ne', lagged_zero]
    rfl
  have hμ : mu1 β c < 1 := mu1_lt_one hβ hc
  have hδz : δ = 0 := by
    funext ω
    have e1 := congrFun (hfoc 0).1 ω
    have e2 := congrFun (hfoc' 0).1 ω
    have e3 := congrFun hπ0 ω
    have e4 := congrFun hd0 ω
    simp only [Pi.add_apply, Pi.sub_apply, lagged_zero, Pi.zero_apply, Pi.smul_apply,
      smul_eq_mul, hδ] at e1 e2 e3 e4 ⊢
    have : (1 - mu1 β c) * (φm1 ω - ψm1 ω) = 0 := by linear_combination e2 - e1 + e3 + e4
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by linarith)
    · exact h
  have hm : φm1 = ψm1 := by
    funext ω; have := congrFun hδz ω; simp only [hδ, Pi.sub_apply, Pi.zero_apply] at this
    linarith
  rw [hm] at hfoc hS1
  have hφψ : φ = ψ := secondOrder_unique 𝔼 hβ hc hS1 hS2 hφa hψa hφb hψb
  have hx : x = xStar 𝔼 β κ lam xm1 u := by
    funext t ω
    have h1 := foc_phi_eq hκ.ne' hfoc t ω
    have h2 : φ t ω = ψ t ω := by rw [hφψ]
    simp only [hψ] at h2
    rw [h1] at h2
    have : lam / κ ≠ 0 := div_ne_zero hlam.ne' hκ.ne'
    have := mul_left_cancel₀ this h2
    linarith
  have hφe : φ = fun t ω => lam / κ * (x t ω - xs) := by
    funext t ω; exact foc_phi_eq hκ.ne' hfoc t ω
  rw [hφe] at hfoc
  exact ⟨(huniq π x hAS ((crit_iff_foc hκ.ne' xs).mpr hfoc) hxb hxa).1, hx⟩

/-! ### (5.1) holds at every `t ≥ t₀ + 1` under any optimal commitment

The FOC plan with a given initial multiplier exists (it is built from the workhorse solution
(2.7) of (2.6)); every initial constraint `π̄_{t₀}` is met by a suitable `φ_{t₀−1}`; by
sufficiency it is optimal, and by uniqueness (faithful `E_{t₀}`) it is the only optimum. -/

/-- Woodford (2003), eq. (2.7), p. 489: the multiplier process solving (2.6),
`β E_t φ_{t+1} − (1 + β + κ²/λ) φ_t + φ_{t−1} = κ x* + u_t`, from `φ_{t₀−1} = φm1`. -/
noncomputable def phiPlan (β κ lam xs : ℝ) (u : ℕ → Ω → ℝ) (φm1 : Ω → ℝ) : ℕ → Ω → ℝ :=
  secondOrderSol 𝔼 β (κ ^ 2 / lam) φm1 (fun t ω => -(κ * xs + u t ω))

/-- Woodford (2003), eq. (1.8), p. 470: the output gap `x_t = x* + (κ/λ) φ_t` of the FOC plan. -/
noncomputable def xPlan (β κ lam xs : ℝ) (u : ℕ → Ω → ℝ) (φm1 : Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => xs + κ / lam * phiPlan 𝔼 β κ lam xs u φm1 t ω

/-- Woodford (2003), eq. (1.7), p. 470: inflation `π_t = φ_{t−1} − φ_t` of the FOC plan. -/
noncomputable def piPlan (β κ lam xs : ℝ) (u : ℕ → Ω → ℝ) (φm1 : Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => lagged φm1 (phiPlan 𝔼 β κ lam xs u φm1) t - phiPlan 𝔼 β κ lam xs u φm1 t

/-- Woodford (2003), p. 489: the forcing `−(κx* + u_t)` of (2.6) is bounded and adapted. -/
theorem forcing_bounded_adapted (κ xs : ℝ) {u : ℕ → Ω → ℝ} (hu : BoundedProc u)
    (hua : 𝔼.Adapted u) :
    BoundedProc (fun t ω => -(κ * xs + u t ω)) ∧ 𝔼.Adapted (fun t ω => -(κ * xs + u t ω)) := by
  have e : (fun t ω => -(κ * xs + u t ω)) = fun t ω => (-1) * (u t ω - -(κ * xs)) := by
    funext t ω; ring
  rw [e]
  exact ⟨affine_bounded _ _ hu, affine_adapted 𝔼 _ _ hua⟩

/-- Woodford (2003), pp. 488–489: the FOC plan built from (2.7) is bounded, adapted, satisfies
(2.1), and satisfies (1.7)–(1.8) with initial multiplier `φm1`; its multiplier is bounded and
adapted. -/
theorem focPlan_spec {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) (xs : ℝ)
    {u : ℕ → Ω → ℝ} (hu : BoundedProc u) (hua : 𝔼.Adapted u) {φm1 : Ω → ℝ} {L : ℝ}
    (hL : ∀ ω, |φm1 ω| ≤ L) (hφ0 : 𝔼.E 0 φm1 = φm1) :
    FeasibleFree 𝔼 β κ u (piPlan 𝔼 β κ lam xs u φm1) (xPlan 𝔼 β κ lam xs u φm1) ∧
      FOC lam κ xs φm1 (piPlan 𝔼 β κ lam xs u φm1) (xPlan 𝔼 β κ lam xs u φm1)
        (phiPlan 𝔼 β κ lam xs u φm1) ∧
      𝔼.Adapted (phiPlan 𝔼 β κ lam xs u φm1) ∧ BoundedProc (phiPlan 𝔼 β κ lam xs u φm1) := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  obtain ⟨hzb, hza⟩ := forcing_bounded_adapted 𝔼 κ xs hu hua
  obtain ⟨hSO, hb, ha, -⟩ := secondOrder_existsUnique 𝔼 hβ hc hzb hza hL hφ0
  change SecondOrder 𝔼 β (κ ^ 2 / lam) φm1 _ (phiPlan 𝔼 β κ lam xs u φm1) at hSO
  change BoundedProc (phiPlan 𝔼 β κ lam xs u φm1) at hb
  change 𝔼.Adapted (phiPlan 𝔼 β κ lam xs u φm1) at ha
  set q := phiPlan 𝔼 β κ lam xs u φm1 with hq
  have hxa : 𝔼.Adapted (xPlan 𝔼 β κ lam xs u φm1) := by
    have e : xPlan 𝔼 β κ lam xs u φm1 = fun t ω => κ / lam * (q t ω - -(lam / κ * xs)) := by
      funext t ω; simp only [xPlan, hq]; field_simp; ring
    rw [e]; exact affine_adapted 𝔼 _ _ ha
  have hxb : BoundedProc (xPlan 𝔼 β κ lam xs u φm1) := by
    have e : xPlan 𝔼 β κ lam xs u φm1 = fun t ω => κ / lam * (q t ω - -(lam / κ * xs)) := by
      funext t ω; simp only [xPlan, hq]; field_simp; ring
    rw [e]; exact affine_bounded _ _ hb
  have hpa : 𝔼.Adapted (piPlan 𝔼 β κ lam xs u φm1) := fun t => by
    change 𝔼.E t (lagged φm1 q t - q t) = lagged φm1 q t - q t
    rw [map_sub, lagged_adapted 𝔼 hφ0 ha t, ha t]
  have hpb : BoundedProc (piPlan 𝔼 β κ lam xs u φm1) := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨max L M + M, fun t ω => (abs_sub _ _).trans
      (add_le_add (lagged_bounded hL hM t ω) (hM t ω))⟩
  refine ⟨⟨hpb, hxb, hpa, hxa, fun t => ?_⟩, fun t => ⟨?_, fun ω => ?_⟩, ha, hb⟩
  · have hEp : 𝔼.E t (piPlan 𝔼 β κ lam xs u φm1 (t + 1)) = q t - 𝔼.E t (q (t + 1)) := by
      simp only [piPlan, map_sub, lagged_succ, ← hq, ha t]
    rw [hEp]
    funext ω
    have e := congrFun (hSO t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, piPlan,
      xPlan, ← hq, neg_neg] at e ⊢
    linear_combination e
  · simp only [piPlan, ← hq]
    abel
  · simp only [xPlan, ← hq]
    field_simp
    ring

/-- Woodford (2003), p. 489: the FOC plan's initial inflation,
`π_{t₀} = (1 − μ₁) φ_{t₀−1} − F_{t₀}` where `F` is the forward component of (2.7). -/
theorem piPlan_zero (β κ lam xs : ℝ) (u : ℕ → Ω → ℝ) (φm1 : Ω → ℝ) :
    piPlan 𝔼 β κ lam xs u φm1 0 = (1 - mu1 β (κ ^ 2 / lam)) • φm1
      - fwdPart 𝔼 β (κ ^ 2 / lam) (fun t ω => -(κ * xs + u t ω)) 0 := by
  change φm1 - (mu1 β (κ ^ 2 / lam) • φm1
    + fwdPart 𝔼 β (κ ^ 2 / lam) (fun t ω => -(κ * xs + u t ω)) 0) = _
  rw [sub_smul, one_smul]
  abel

/-- Woodford (2003), eq. (2.8), p. 489: the initial multiplier that meets the initial constraint
`π_{t₀} = π̄_{t₀}`, `φ_{t₀−1} = (1 − μ₁)⁻¹ (π̄_{t₀} + F_{t₀})`. -/
noncomputable def phiInit (β κ lam xs : ℝ) (u : ℕ → Ω → ℝ) (πbar : Ω → ℝ) : Ω → ℝ :=
  (1 - mu1 β (κ ^ 2 / lam))⁻¹ •
    (πbar + fwdPart 𝔼 β (κ ^ 2 / lam) (fun t ω => -(κ * xs + u t ω)) 0)

/-- Woodford (2003), eq. (2.8), p. 489: with `φ_{t₀−1}` from `phiInit` the FOC plan meets the
initial constraint, and `φ_{t₀−1}` is bounded and known at `t₀`. -/
theorem phiInit_spec {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) (xs : ℝ)
    {u : ℕ → Ω → ℝ} (hu : BoundedProc u) (hua : 𝔼.Adapted u) {πbar : Ω → ℝ} {P : ℝ}
    (hP : ∀ ω, |πbar ω| ≤ P) (hπ0 : 𝔼.E 0 πbar = πbar) :
    piPlan 𝔼 β κ lam xs u (phiInit 𝔼 β κ lam xs u πbar) 0 = πbar ∧
      (∃ L, ∀ ω, |phiInit 𝔼 β κ lam xs u πbar ω| ≤ L) ∧
      𝔼.E 0 (phiInit 𝔼 β κ lam xs u πbar) = phiInit 𝔼 β κ lam xs u πbar := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have hμ := mu1_lt_one hβ hc
  have hne : 1 - mu1 β (κ ^ 2 / lam) ≠ 0 := by linarith
  obtain ⟨hzb, hza⟩ := forcing_bounded_adapted 𝔼 κ xs hu hua
  obtain ⟨Mz, hMz⟩ := hzb
  have hl2 : 1 < mu2 β (κ ^ 2 / lam) := one_lt_mu2 hβ hc
  have ha : |(mu2 β (κ ^ 2 / lam))⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (lt_trans one_pos hl2)]
    exact inv_lt_one_of_one_lt₀ hl2
  have hub : ∀ t ω, |((β * mu2 β (κ ^ 2 / lam))⁻¹ • fun ω => -(κ * xs + u t ω)) ω| ≤
      |(β * mu2 β (κ ^ 2 / lam))⁻¹| * Mz := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hMz t ω) (abs_nonneg _)
  have hua' : 𝔼.Adapted (fun t => (β * mu2 β (κ ^ 2 / lam))⁻¹ •
      fun ω => -(κ * xs + u t ω)) := fun t => by
    simp only [map_smul]
    exact congrArg _ (hza t)
  obtain ⟨BF, hBF⟩ := ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hub
  have hFa := ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hub
  refine ⟨?_, ⟨|(1 - mu1 β (κ ^ 2 / lam))⁻¹| * (P + BF), fun ω => ?_⟩, ?_⟩
  · rw [piPlan_zero, phiInit, smul_smul, mul_inv_cancel₀ hne, one_smul]
    abel
  · simp only [phiInit, Pi.smul_apply, Pi.add_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add (hP ω) (hBF 0 ω)))
      (abs_nonneg _)
  · simp only [phiInit, map_smul, map_add, hπ0]
    exact congrArg _ (congrArg _ (hFa 0))

/-- Woodford (2003), §2.1, p. 489: for every bounded initial constraint `π̄_{t₀}` known at `t₀`
the constrained problem (2.8) **has a solution** (the FOC plan with `φ_{t₀−1}` from
`phiInit`). -/
theorem exists_isConstrainedOpt {β κ lam : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hpo : 𝔼.PullOut) (xs : ℝ) {u : ℕ → Ω → ℝ} (hu : BoundedProc u)
    (hua : 𝔼.Adapted u) {πbar : Ω → ℝ} {P : ℝ} (hP : ∀ ω, |πbar ω| ≤ P)
    (hπ0 : 𝔼.E 0 πbar = πbar) :
    IsConstrainedOpt 𝔼 β κ lam xs u πbar (piPlan 𝔼 β κ lam xs u (phiInit 𝔼 β κ lam xs u πbar))
      (xPlan 𝔼 β κ lam xs u (phiInit 𝔼 β κ lam xs u πbar)) := by
  obtain ⟨h0, ⟨L, hL⟩, hφ0⟩ := phiInit_spec 𝔼 hβ hκ hlam xs hu hua hP hπ0
  obtain ⟨hF, hfoc, ha, hb⟩ := focPlan_spec 𝔼 hβ hκ hlam xs hu hua hL hφ0
  exact isConstrainedOpt_of_foc 𝔼 hβ.le hβ1 hlam.le hpo ⟨hF, h0⟩ hfoc ha hb

/-- Woodford (2003), eq. (5.1), p. 523 (**(5.1) under any timelessly optimal policy**): with a
faithful `E_{t₀}`, any solution of the constrained problem (2.8) — whatever the bounded initial
constraint `π̄_{t₀}` known at `t₀`, hence under any policy that is optimal from a timeless
perspective — satisfies (5.1) at every date `t ≥ t₀ + 1`. -/
theorem crit_succ_of_isConstrainedOpt {β κ lam xs : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hlam : 0 < lam) (hpo : 𝔼.PullOut) (hf : Faithful 𝔼) {u : ℕ → Ω → ℝ}
    (hu : BoundedProc u) (hua : 𝔼.Adapted u) {πbar : Ω → ℝ} {P : ℝ}
    (hP : ∀ ω, |πbar ω| ≤ P) (hπ0 : 𝔼.E 0 πbar = πbar) {π x : ℕ → Ω → ℝ}
    (hopt : IsConstrainedOpt 𝔼 β κ lam xs u πbar π x) (t : ℕ) :
    π (t + 1) + (lam / κ) • (x (t + 1) - x t) = 0 := by
  obtain ⟨h0, ⟨L, hL⟩, hφ0⟩ := phiInit_spec 𝔼 hβ hκ hlam xs hu hua hP hπ0
  obtain ⟨hF, hfoc, ha, hb⟩ := focPlan_spec 𝔼 hβ hκ hlam xs hu hua hL hφ0
  obtain ⟨hπ, hx⟩ := eq_of_isConstrainedOpt 𝔼 hβ hβ1 hlam hpo hf hopt ⟨hF, h0⟩ hfoc ha hb
  rw [hπ, hx]
  exact crit_succ_of_foc hκ.ne' hfoc t

/-- Woodford (2003), eq. (2.5), p. 488: the `t₀`-optimal commitment exists (the FOC plan with
`φ_{t₀−1} = 0`). -/
theorem exists_isT0Opt {β κ lam : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hpo : 𝔼.PullOut) (xs : ℝ) {u : ℕ → Ω → ℝ} (hu : BoundedProc u)
    (hua : 𝔼.Adapted u) :
    IsT0Opt 𝔼 β κ lam xs u (piPlan 𝔼 β κ lam xs u 0) (xPlan 𝔼 β κ lam xs u 0) := by
  obtain ⟨hF, hfoc, ha, hb⟩ := focPlan_spec 𝔼 hβ hκ hlam xs hu hua (φm1 := 0) (L := 0)
    (fun _ => by simp) (by simp)
  exact isT0Opt_of_foc 𝔼 hβ.le hβ1 hlam.le hpo hF hfoc ha hb

/-- Woodford (2003), p. 523 ("and indeed, under a `t₀`-optimal commitment as well"): with a
faithful `E_{t₀}`, the `t₀`-optimal commitment satisfies (5.1) at every `t ≥ t₀ + 1`. -/
theorem crit_succ_of_isT0Opt {β κ lam xs : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hpo : 𝔼.PullOut) (hf : Faithful 𝔼) {u : ℕ → Ω → ℝ}
    (hu : BoundedProc u) (hua : 𝔼.Adapted u) {π x : ℕ → Ω → ℝ}
    (hopt : IsT0Opt 𝔼 β κ lam xs u π x) (t : ℕ) :
    π (t + 1) + (lam / κ) • (x (t + 1) - x t) = 0 := by
  obtain ⟨hF, hfoc, ha, hb⟩ := focPlan_spec 𝔼 hβ hκ hlam xs hu hua (φm1 := 0) (L := 0)
    (fun _ => by simp) (by simp)
  obtain ⟨hπ, hx⟩ := eq_of_isT0Opt 𝔼 hβ hβ1 hlam hpo hf hopt hF hfoc ha hb
  rw [hπ, hx]
  exact crit_succ_of_foc hκ.ne' hfoc t

/-- Woodford (2003), **Proposition 7.15**, p. 523 (uniqueness of the optimum): with a faithful
`E_{t₀}`, the equilibrium `(π*, x*)` of (5.1) is the *only* solution of the problem of
Proposition 7.7 (constraint (2.11)). -/
theorem eq_star_of_isConstrainedOpt {β κ lam xs : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hpo : 𝔼.PullOut) (hf : Faithful 𝔼) {u : ℕ → Ω → ℝ}
    (hu : BoundedProc u) (hua : 𝔼.Adapted u) {xm1 : Ω → ℝ} {K : ℝ} (hK : ∀ ω, |xm1 ω| ≤ K)
    (hm0 : 𝔼.E 0 xm1 = xm1) {π x : ℕ → Ω → ℝ}
    (hopt : IsConstrainedOpt 𝔼 β κ lam xs u (eq211 𝔼 β κ lam u xm1) π x) :
    π = piStar 𝔼 β κ lam xm1 u ∧ x = xStar 𝔼 β κ lam xm1 u := by
  obtain ⟨⟨hAS, hC, hpb, hxb, hpa, hxa⟩, -⟩ := prop_7_15 𝔼 hβ hκ hlam hu hua hK hm0
  have hopt' := crit_isConstrainedOpt 𝔼 hβ hβ1 hκ hlam hpo xs hu hua hK hm0 hAS hC hpb hxb hpa
    hxa
  exact eq_of_isConstrainedOpt 𝔼 hβ hβ1 hlam hpo hf hopt hopt'.1
    ((crit_iff_foc hκ.ne' xs).mp hC) (affine_adapted 𝔼 _ _ hxa) (affine_bounded _ _ hxb)

/-! ### Optimality from a timeless perspective

The problem started at a later date `s` is the same problem for the shifted expectation system
`E'_t = E_{s+t}` and shifted processes. A policy is optimal from a timeless perspective
(p. 489) if its continuation from **every** date `s` solves the constrained problem started at
`s`, with an initial constraint `π̄_s` given by a time-invariant rule. -/

/-- Woodford (2003), p. 489: a process seen from date `s`. -/
def shiftP (s : ℕ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => x (s + t)

/-- Woodford (2003), p. 489: the lagged value of a process seen from date `s` is the lag of the
original process, with `x_{s−1}` as the initial value. -/
theorem lagged_shiftP (xm1 : Ω → ℝ) (x : ℕ → Ω → ℝ) (s t : ℕ) :
    lagged (lagged xm1 x s) (shiftP s x) t = lagged xm1 x (s + t) := by
  cases t <;> rfl

/-- Woodford (2003), p. 489 ("optimal from a timeless perspective"): for every date `s ≥ t₀`
the continuation of `(π, x)` from `s` minimises the expected discounted loss (1.2) from `s`
among all bounded adapted plans satisfying (2.1) from `s` and the initial constraint
`π_s = π̄_s`, where `π̄_s = πbarAt s` is given by a time-invariant rule. -/
def TimelesslyOptimal (β κ lam xs : ℝ) (u : ℕ → Ω → ℝ) (πbarAt : ℕ → Ω → ℝ)
    (π x : ℕ → Ω → ℝ) : Prop :=
  ∀ s, IsConstrainedOpt (shiftSys 𝔼 s) β κ lam xs (shiftP s u) (πbarAt s) (shiftP s π) (shiftP s x)

/-- Woodford (2003), eq. (2.11), p. 490, as a time-invariant rule: at each date `s` the
constraint value is (2.11) computed from date-`s` information and `x_{s−1}`. -/
noncomputable def rule211 (β κ lam : ℝ) (u : ℕ → Ω → ℝ) (xm1 : Ω → ℝ) (x : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun s => eq211 (shiftSys 𝔼 s) β κ lam (shiftP s u) (lagged xm1 x s)

/-- Woodford (2003), p. 489: the shifted problem inherits boundedness, adaptedness, (2.1),
(5.1) (with initial value `x_{s−1}`) and a bounded initial value known at `s`. -/
theorem shift_crit {β κ lam : ℝ} {u π x : ℕ → Ω → ℝ} {xm1 : Ω → ℝ} {K M : ℝ}
    (hAS : AS 𝔼 β κ u π x) (hC : Crit lam κ xm1 π x) (hua : 𝔼.Adapted u)
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) (hK : ∀ ω, |xm1 ω| ≤ K)
    (hM : ∀ t ω, |x t ω| ≤ M) (hm0 : 𝔼.E 0 xm1 = xm1) (s : ℕ) :
    AS (shiftSys 𝔼 s) β κ (shiftP s u) (shiftP s π) (shiftP s x) ∧
      Crit lam κ (lagged xm1 x s) (shiftP s π) (shiftP s x) ∧
      (shiftSys 𝔼 s).Adapted (shiftP s u) ∧ (shiftSys 𝔼 s).Adapted (shiftP s π) ∧
      (shiftSys 𝔼 s).Adapted (shiftP s x) ∧ (∀ ω, |lagged xm1 x s ω| ≤ max K M) ∧
      (shiftSys 𝔼 s).E 0 (lagged xm1 x s) = lagged xm1 x s := by
  refine ⟨fun t => hAS (s + t), fun t => ?_, fun t => hua (s + t), fun t => hπa (s + t),
    fun t => hxa (s + t), fun ω => lagged_bounded hK hM s ω, lagged_adapted 𝔼 hm0 hxa s⟩
  rw [lagged_shiftP]
  exact hC (s + t)

/-- Woodford (2003), **Proposition 7.15**, p. 523 ("Thus the proposed policy rule is optimal from
a timeless perspective"): the equilibrium of (5.1) is optimal from a timeless perspective, with
the self-consistent constraint rule (2.11): at every date `s` its continuation solves the
problem of Proposition 7.7 started at `s`. -/
theorem prop_7_15_timeless {β κ lam : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hpo : 𝔼.PullOut) (xs : ℝ) {u : ℕ → Ω → ℝ} (hu : BoundedProc u)
    (hua : 𝔼.Adapted u) {xm1 : Ω → ℝ} {K : ℝ} (hK : ∀ ω, |xm1 ω| ≤ K)
    (hm0 : 𝔼.E 0 xm1 = xm1) :
    TimelesslyOptimal 𝔼 β κ lam xs u (rule211 𝔼 β κ lam u xm1 (xStar 𝔼 β κ lam xm1 u))
      (piStar 𝔼 β κ lam xm1 u) (xStar 𝔼 β κ lam xm1 u) := by
  obtain ⟨⟨hAS, hC, hpb, hxb, hpa, hxa⟩, -⟩ := prop_7_15 𝔼 hβ hκ hlam hu hua hK hm0
  intro s
  obtain ⟨M, hM⟩ := hxb
  obtain ⟨Mp, hMp⟩ := hpb
  obtain ⟨Mu, hMu⟩ := hu
  obtain ⟨hAS', hC', hua', hpa', hxa', hK', hm0'⟩ :=
    shift_crit 𝔼 hAS hC hua hpa hxa hK hM hm0 s
  exact crit_isConstrainedOpt (shiftSys 𝔼 s) hβ hβ1 hκ hlam (shiftSys_pullOut 𝔼 hpo) xs
    ⟨Mu, fun t ω => hMu (s + t) ω⟩ hua' hK' hm0' hAS' hC' ⟨Mp, fun t ω => hMp (s + t) ω⟩
    ⟨M, fun t ω => hM (s + t) ω⟩ hpa' hxa'

/-! ### The price-level target (5.3) and Proposition 7.16 -/

/-- Woodford (2003), p. 491: the log price level `p_t = p_{t−1} + π_t`, from `p_{t₀−1} = pm1`. -/
def priceLevel (pm1 : Ω → ℝ) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => pm1 + π 0
  | t + 1 => priceLevel pm1 π t + π (t + 1)

/-- Woodford (2003), p. 491: `p_t = p_{t−1} + π_t` at every date. -/
theorem priceLevel_eq (pm1 : Ω → ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) :
    priceLevel pm1 π t = lagged pm1 (priceLevel pm1 π) t + π t := by
  cases t <;> rfl

/-- Woodford (2003), eq. (5.3), p. 526: the flexible price-level target
`p_t + (λ/κ) x_t = p̄` at every date `t ≥ t₀` (`p̄` known at `t₀`). -/
def PriceRule (lam κ : ℝ) (pm1 pbar : Ω → ℝ) (π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, priceLevel pm1 π t + (lam / κ) • x t = pbar

/-- Woodford (2003), App. F.6, eq. (F.11), p. 715: the fictitious initial output gap
`x_{t₀−1} = (κ/λ)(p̄ − p_{t₀−1})` that makes (5.1) hold at `t₀`. -/
noncomputable def fictX (lam κ : ℝ) (pm1 pbar : Ω → ℝ) : Ω → ℝ := (κ / lam) • (pbar - pm1)

/-- Woodford (2003), App. F.6, p. 715 (**the fictitious-initial-condition argument**): (5.3) at
every `t ≥ t₀` is equivalent to (5.1) at every `t ≥ t₀` with the fictitious initial value
`x_{t₀−1} = (κ/λ)(p̄ − p_{t₀−1})`. (In particular (5.3) implies (5.1) at every `t ≥ t₀ + 1`,
since `x_{t₀−1}` only enters (5.1) at `t₀`.) -/
theorem priceRule_iff_crit {lam κ : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0) (pm1 pbar : Ω → ℝ)
    (π x : ℕ → Ω → ℝ) :
    PriceRule lam κ pm1 pbar π x ↔ Crit lam κ (fictX lam κ pm1 pbar) π x := by
  constructor
  · intro hP t
    funext ω
    cases t with
    | zero =>
      have h := congrFun (hP 0) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, priceLevel] at h
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, lagged_zero, fictX,
        Pi.zero_apply]
      have e : lam / κ * (κ / lam) = 1 := by field_simp
      linear_combination h - (pbar ω - pm1 ω) * e
    | succ t =>
      have h1 := congrFun (hP t) ω
      have h2 := congrFun (hP (t + 1)) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, priceLevel] at h1 h2
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, lagged_succ,
        Pi.zero_apply]
      linear_combination h2 - h1
  · intro hC t
    induction t with
    | zero =>
      funext ω
      have h := congrFun (hC 0) ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, lagged_zero, fictX,
        Pi.zero_apply] at h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, priceLevel]
      have e : lam / κ * (κ / lam) = 1 := by field_simp
      linear_combination h + (pbar ω - pm1 ω) * e
    | succ t ih =>
      funext ω
      have h := congrFun (hC (t + 1)) ω
      have h1 := congrFun ih ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, lagged_succ,
        Pi.zero_apply] at h h1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, priceLevel]
      linear_combination h + h1

/-- Woodford (2003), p. 527: committing to (5.1) from `t₀` is equivalent to committing to (5.3)
with the price-level target `p̄ = p_{t₀−1} + (λ/κ) x_{t₀−1}`. -/
theorem crit_iff_priceRule {lam κ : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0) (pm1 xm1 : Ω → ℝ)
    (π x : ℕ → Ω → ℝ) :
    Crit lam κ xm1 π x ↔ PriceRule lam κ pm1 (pm1 + (lam / κ) • xm1) π x := by
  have e : fictX lam κ pm1 (pm1 + (lam / κ) • xm1) = xm1 := by
    funext ω
    simp only [fictX, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    ring
  rw [priceRule_iff_crit hκ hlam, e]

/-- Woodford (2003), p. 527: with the welfare-theoretic weight `λ = κ/θ` (Chapter 6), the
optimal flexible price-level target stabilises `p_t + θ⁻¹ x_t`. -/
theorem priceRule_theta {κ θ : ℝ} (hκ : κ ≠ 0) (hθ : θ ≠ 0) (pm1 pbar : Ω → ℝ)
    (π x : ℕ → Ω → ℝ) :
    PriceRule (κ / θ) κ pm1 pbar π x ↔ ∀ t, priceLevel pm1 π t + θ⁻¹ • x t = pbar := by
  have e : κ / θ / κ = θ⁻¹ := by field_simp
  simp only [PriceRule, e]

/-- Woodford (2003), p. 527: with `θ > 1` the weight `θ⁻¹` on the output gap lies in `(0, 1)`,
a small fraction of the unit weight on the price level when `θ` is large. -/
theorem theta_weight {θ : ℝ} (hθ : 1 < θ) : 0 < θ⁻¹ ∧ θ⁻¹ < 1 :=
  ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ hθ⟩

/-- Woodford (2003), eq. (2.13), p. 491: the price-level form of the self-consistent
constraint, `π̄_{t₀} = −(1 − μ₁)(p_{t₀−1} − p̄) + β⁻¹ ∑ⱼ μ₂^{−j−1} E_{t₀} u_{t₀+j}`. -/
noncomputable def eq213 (β κ lam : ℝ) (u : ℕ → Ω → ℝ) (pm1 pbar : Ω → ℝ) : Ω → ℝ :=
  -(1 - mu1 β (κ ^ 2 / lam)) • (pm1 - pbar) + fwdU 𝔼 β κ lam u 0

/-- Woodford (2003), App. F.6, p. 715: (2.13) is (2.11) at the fictitious initial gap. -/
theorem eq211_fictX {κ lam : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0) (β : ℝ) (u : ℕ → Ω → ℝ)
    (pm1 pbar : Ω → ℝ) :
    eq211 𝔼 β κ lam u (fictX lam κ pm1 pbar) = eq213 𝔼 β κ lam u pm1 pbar := by
  funext ω
  simp only [eq211, eq213, fictX, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- Woodford (2003), **Proposition 7.16**, p. 526, and App. F.6, p. 715: if the central bank
ensures (5.3) at every `t ≥ t₀` (bounded `p_{t₀−1}`, `p̄` known at `t₀`), then
`(π*, x*)` started from the fictitious initial gap `(κ/λ)(p̄ − p_{t₀−1})` is a bounded adapted
solution of (2.1) and (5.3), the only one; the price level is then bounded too. -/
theorem prop_7_16 {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    {u : ℕ → Ω → ℝ} (hu : BoundedProc u) (hua : 𝔼.Adapted u) {pm1 pbar : Ω → ℝ} {K : ℝ}
    (hK : ∀ ω, |pbar ω - pm1 ω| ≤ K) (hp0 : 𝔼.E 0 pm1 = pm1) (hb0 : 𝔼.E 0 pbar = pbar) :
    (AS 𝔼 β κ u (piStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u)
        (xStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u) ∧
      PriceRule lam κ pm1 pbar (piStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u)
        (xStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u) ∧
      BoundedProc (piStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u) ∧
      BoundedProc (xStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u) ∧
      𝔼.Adapted (piStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u) ∧
      𝔼.Adapted (xStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u)) ∧
    (∀ π x : ℕ → Ω → ℝ, AS 𝔼 β κ u π x → PriceRule lam κ pm1 pbar π x → BoundedProc x →
      𝔼.Adapted x →
        π = piStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u ∧
          x = xStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u) := by
  have hfK : ∀ ω, |fictX lam κ pm1 pbar ω| ≤ |κ / lam| * K := fun ω => by
    simp only [fictX, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hK ω) (abs_nonneg _)
  have hf0 : 𝔼.E 0 (fictX lam κ pm1 pbar) = fictX lam κ pm1 pbar := by
    simp only [fictX, map_smul, map_sub, hp0, hb0]
  obtain ⟨⟨hAS, hC, h3⟩, huniq⟩ := prop_7_15 𝔼 hβ hκ hlam hu hua hfK hf0
  refine ⟨⟨hAS, (priceRule_iff_crit hκ.ne' hlam.ne' _ _ _ _).mpr hC, h3⟩,
    fun π x hA hP hxb hxa => huniq π x hA ((priceRule_iff_crit hκ.ne' hlam.ne' _ _ _ _).mp hP)
      hxb hxa⟩

/-- Woodford (2003), App. F.6, p. 715: under (5.3) the initial output gap is
`x_{t₀} = −μ₁(κ/λ)(p_{t₀−1} − p̄) − (κ/λ) β⁻¹ ∑ⱼ μ₂^{−j−1} E_{t₀} u_{t₀+j}`. -/
theorem xStar_fictX_zero (β κ lam : ℝ) (u : ℕ → Ω → ℝ) (pm1 pbar : Ω → ℝ) :
    xStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u 0 =
      -(mu1 β (κ ^ 2 / lam) * (κ / lam)) • (pm1 - pbar) - (κ / lam) • fwdU 𝔼 β κ lam u 0 := by
  rw [xStar_eq, lagged_zero]
  funext ω
  simp only [fictX, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), App. F.6, p. 715: along a solution of (5.3), `(λ/κ) x_{t−1} = p̄ − p_{t−1}`
at every date (with the fictitious `x_{t₀−1}`). -/
theorem lagged_gap_of_priceRule {lam κ : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0) {pm1 pbar : Ω → ℝ}
    {π x : ℕ → Ω → ℝ} (hP : PriceRule lam κ pm1 pbar π x) (t : ℕ) :
    (lam / κ) • lagged (fictX lam κ pm1 pbar) x t = pbar - lagged pm1 (priceLevel pm1 π) t := by
  cases t with
  | zero =>
    funext ω
    simp only [lagged_zero, fictX, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  | succ t =>
    rw [lagged_succ, lagged_succ, ← hP t]
    abel

/-- Woodford (2003), **Proposition 7.8**, eq. (2.15), p. 491, reached through Proposition 7.16:
under (5.3) the price level satisfies `p_t = (1 − μ₁) p̄ + μ₁ p_{t−1} + β⁻¹ ∑ⱼ μ₂^{−j−1}
E_t u_{t+j}` at every date (the printed left side "p̄_t" should read `p_t`). -/
theorem eq215 {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) {u : ℕ → Ω → ℝ}
    (hu : BoundedProc u) (hua : 𝔼.Adapted u) {pm1 pbar : Ω → ℝ} {K : ℝ}
    (hK : ∀ ω, |pbar ω - pm1 ω| ≤ K) (hp0 : 𝔼.E 0 pm1 = pm1) (hb0 : 𝔼.E 0 pbar = pbar)
    (t : ℕ) :
    priceLevel pm1 (piStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u) t =
      (1 - mu1 β (κ ^ 2 / lam)) • pbar + mu1 β (κ ^ 2 / lam) •
        lagged pm1 (priceLevel pm1 (piStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u)) t
        + fwdU 𝔼 β κ lam u t := by
  obtain ⟨⟨-, hP, -⟩, -⟩ := prop_7_16 𝔼 hβ hκ hlam hu hua hK hp0 hb0
  have hl := lagged_gap_of_priceRule hκ.ne' hlam.ne' hP t
  rw [priceLevel_eq, piStar_eq 𝔼 hκ.ne' hlam.ne', mul_smul, hl]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Woodford (2003), eq. (2.13), p. 491: under (5.3), initial inflation is (2.13). -/
theorem piStar_fictX_zero {κ lam : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0) (β : ℝ)
    (u : ℕ → Ω → ℝ) (pm1 pbar : Ω → ℝ) :
    piStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u 0 = eq213 𝔼 β κ lam u pm1 pbar := by
  rw [piStar_eq 𝔼 hκ hlam, lagged_zero, ← eq211_fictX 𝔼 hκ hlam]
  rfl

/-- Woodford (2003), **Proposition 7.16**, p. 527 (optimality, identification with
Proposition 7.8): the equilibrium of (5.3) solves the problem of Proposition 7.8 — minimising
(1.2) subject to (2.1) and the initial constraint (2.13). -/
theorem prop_7_16_optimal {β κ lam : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hpo : 𝔼.PullOut) (xs : ℝ) {u : ℕ → Ω → ℝ} (hu : BoundedProc u)
    (hua : 𝔼.Adapted u) {pm1 pbar : Ω → ℝ} {K : ℝ} (hK : ∀ ω, |pbar ω - pm1 ω| ≤ K)
    (hp0 : 𝔼.E 0 pm1 = pm1) (hb0 : 𝔼.E 0 pbar = pbar) :
    IsConstrainedOpt 𝔼 β κ lam xs u (eq213 𝔼 β κ lam u pm1 pbar)
      (piStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u) (xStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u) := by
  have hfK : ∀ ω, |fictX lam κ pm1 pbar ω| ≤ |κ / lam| * K := fun ω => by
    simp only [fictX, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hK ω) (abs_nonneg _)
  have hf0 : 𝔼.E 0 (fictX lam κ pm1 pbar) = fictX lam κ pm1 pbar := by
    simp only [fictX, map_smul, map_sub, hp0, hb0]
  obtain ⟨⟨hAS, hC, hpb, hxb, hpa, hxa⟩, -⟩ := prop_7_15 𝔼 hβ hκ hlam hu hua hfK hf0
  rw [← eq211_fictX 𝔼 hκ.ne' hlam.ne']
  exact crit_isConstrainedOpt 𝔼 hβ hβ1 hκ hlam hpo xs hu hua hfK hf0 hAS hC hpb hxb hpa hxa

/-- Woodford (2003), eq. (2.13)–(2.14), p. 491, as a time-invariant rule: at each date `s` the
constraint value is (2.13) computed from date-`s` information and `p_{s−1}`. -/
noncomputable def rule213 (β κ lam : ℝ) (u : ℕ → Ω → ℝ) (pm1 pbar : Ω → ℝ)
    (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun s => eq213 (shiftSys 𝔼 s) β κ lam (shiftP s u) (lagged pm1 (priceLevel pm1 π) s) pbar

/-- Woodford (2003), **Proposition 7.16**, p. 527 ("Thus the proposed policy rule is optimal from
a timeless perspective"): the equilibrium of (5.3) is optimal from a timeless perspective with
the self-consistent constraint rule (2.13). -/
theorem prop_7_16_timeless {β κ lam : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hpo : 𝔼.PullOut) (xs : ℝ) {u : ℕ → Ω → ℝ} (hu : BoundedProc u)
    (hua : 𝔼.Adapted u) {pm1 pbar : Ω → ℝ} {K : ℝ} (hK : ∀ ω, |pbar ω - pm1 ω| ≤ K)
    (hp0 : 𝔼.E 0 pm1 = pm1) (hb0 : 𝔼.E 0 pbar = pbar) :
    TimelesslyOptimal 𝔼 β κ lam xs u
      (rule213 𝔼 β κ lam u pm1 pbar (piStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u))
      (piStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u) (xStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u) := by
  have hfK : ∀ ω, |fictX lam κ pm1 pbar ω| ≤ |κ / lam| * K := fun ω => by
    simp only [fictX, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hK ω) (abs_nonneg _)
  have hf0 : 𝔼.E 0 (fictX lam κ pm1 pbar) = fictX lam κ pm1 pbar := by
    simp only [fictX, map_smul, map_sub, hp0, hb0]
  obtain ⟨⟨-, hP, -⟩, -⟩ := prop_7_16 𝔼 hβ hκ hlam hu hua hK hp0 hb0
  have h := prop_7_15_timeless 𝔼 hβ hβ1 hκ hlam hpo xs hu hua hfK hf0
  intro s
  have e : rule213 𝔼 β κ lam u pm1 pbar (piStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u) s =
      rule211 𝔼 β κ lam u (fictX lam κ pm1 pbar)
        (xStar 𝔼 β κ lam (fictX lam κ pm1 pbar) u) s := by
    have hl := lagged_gap_of_priceRule hκ.ne' hlam.ne' hP s
    funext ω
    have hl' := congrFun hl ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hl'
    simp only [rule213, rule211, eq213, eq211, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]
    rw [mul_assoc, hl']
    ring
  rw [e]
  exact h s

/-- Woodford (2003), p. 527: rules in the family (5.3) with different `p̄` (equivalently,
different initial gaps) lead to equilibria that differ only by a transitory component known at
`t₀`: `x_t − x'_t = μ₁^{t+1}(x_{t₀−1} − x'_{t₀−1})`, which vanishes as `t → ∞`; in particular
they have the same responses to shocks. -/
theorem xStar_sub (β κ lam : ℝ) (xm1 xm1' : Ω → ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    xStar 𝔼 β κ lam xm1 u t - xStar 𝔼 β κ lam xm1' u t =
      mu1 β (κ ^ 2 / lam) ^ (t + 1) • (xm1 - xm1') :=
  secondOrderSol_sub 𝔼 β _ xm1 xm1' _ t

/-- Woodford (2003), p. 527: the inflation paths of two rules in the family differ by
`(λ/κ)(1 − μ₁) μ₁ᵗ (x_{t₀−1} − x'_{t₀−1})`. -/
theorem piStar_sub (β κ lam : ℝ) (xm1 xm1' : Ω → ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    piStar 𝔼 β κ lam xm1 u t - piStar 𝔼 β κ lam xm1' u t =
      ((lam / κ) * (1 - mu1 β (κ ^ 2 / lam)) * mu1 β (κ ^ 2 / lam) ^ t) • (xm1 - xm1') := by
  have hp : lagged xm1 (xStar 𝔼 β κ lam xm1 u) t - lagged xm1' (xStar 𝔼 β κ lam xm1' u) t =
      mu1 β (κ ^ 2 / lam) ^ t • (xm1 - xm1') := by
    cases t with
    | zero => simp
    | succ t => exact xStar_sub 𝔼 β κ lam xm1 xm1' u t
  have hx := xStar_sub 𝔼 β κ lam xm1 xm1' u t
  unfold piStar
  rw [← smul_sub, sub_sub_sub_comm, hp, hx]
  funext ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 527: the transitory component vanishes, `x_t − x'_t → 0`. -/
theorem tendsto_xStar_sub {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (xm1 xm1' : Ω → ℝ) (u : ℕ → Ω → ℝ) (ω : Ω) :
    Tendsto (fun t => xStar 𝔼 β κ lam xm1 u t ω - xStar 𝔼 β κ lam xm1' u t ω) atTop (𝓝 0) := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have h0 := (mu1_pos hβ hc).le
  have h1 := mu1_lt_one hβ hc
  have e : (fun t => xStar 𝔼 β κ lam xm1 u t ω - xStar 𝔼 β κ lam xm1' u t ω) =
      fun t => mu1 β (κ ^ 2 / lam) ^ (t + 1) * (xm1 ω - xm1' ω) := by
    funext t
    have := congrFun (xStar_sub 𝔼 β κ lam xm1 xm1' u t) ω
    simpa using this
  rw [e]
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp (tendsto_add_atTop_nat 1)).mul_const
    (xm1 ω - xm1' ω)
  simpa using this

end Woodford.GainsFromCommitment.TargetingRule
