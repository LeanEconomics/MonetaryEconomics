/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DiscretionCommitment.Commitment

/-!
# Commitment versus discretion

Galí (2015), Section 5.2, pp. 130–137. Under discretion the central bank follows the targeting
rule `x_t = −(κ/ϑ) π_t` ((4), p. 130), and with an AR(1) cost-push shock the (minimal state
variable) equilibrium is `π_t = ϑ/(κ² + ϑ(1 − βρ_u)) u_t`, `x_t = −κ/(κ² + ϑ(1 − βρ_u)) u_t`
((5)–(6), p. 130). This module compares it with the optimal policy under commitment of the module
`Commitment`.

## Main results

* `disc_nkpc`, `disc_targeting`, `disc_unique`: the discretionary path solves the Phillips curve,
  satisfies (4), and is the unique bounded adapted plan doing so.
* `commitment_le_discretion` (p. 137): commitment weakly beats discretion, state by state,
  because the discretionary plan is feasible for the commitment problem;
  `commitment_lt_discretion`: strictly wherever `u_0 ≠ 0`.
* `del_lt_disc_coef`: `δ < ϑ/(ϑ + κ²)`, the source of the stabilisation gain.
* `impact_inflation`, `impact_gap` (p. 137): for every `|ρ_u| < 1`, commitment lowers the impact
  response of inflation and of the absolute output gap; `impact_rho0` gives the closed forms for
  `ρ_u = 0`: `π_0 = δ u_0` vs `ϑ/(κ² + ϑ) u_0` and `x_0 = −(κδ/ϑ) u_0` vs `−κ/(κ² + ϑ) u_0`.
* `impulse_rho0` (p. 136): after a one-time shock, commitment keeps the price level, inflation and
  the output gap away from zero for ever (`p̂_t = δ^{t+1} u_0`), while under discretion inflation
  and the output gap return to zero one period after the shock.
-/

namespace Gali.DiscretionCommitment.CommitmentVsDiscretion

open Gali.DiscretionCommitment.Commitment

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The discretionary equilibrium -/

/-- Galí (2015), (5), p. 130: the discretionary inflation coefficient
`ϑ/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiPi (β κ ϑ ρ : ℝ) : ℝ := ϑ / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- Galí (2015), (6), p. 130: the discretionary output-gap coefficient
`−κ/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiX (β κ ϑ ρ : ℝ) : ℝ := -κ / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- Galí (2015), (5), p. 130: discretionary inflation `π_t = ϑ/(κ² + ϑ(1 − βρ_u)) u_t`. -/
noncomputable def inflDisc (β κ ϑ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  psiPi β κ ϑ ρ • u t

/-- Galí (2015), (6), p. 130: the discretionary output gap `x_t = −κ/(κ² + ϑ(1 − βρ_u)) u_t`. -/
noncomputable def gapDisc (β κ ϑ ρ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  psiX β κ ϑ ρ • u t

/-- Galí (2015), (5)–(6), p. 130: `1 − βρ_u > 0` for `|ρ_u| < 1`, so the discretionary
denominator `κ² + ϑ(1 − βρ_u)` is positive. -/
theorem denom_pos {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1) :
    0 < 1 - β * ρ ∧ 0 < κ ^ 2 + ϑ * (1 - β * ρ) := by
  have h1 : β * ρ < 1 := by
    have := le_abs_self ρ
    have : β * ρ ≤ β * |ρ| := mul_le_mul_of_nonneg_left this hβ0.le
    have : β * |ρ| < 1 := by nlinarith [abs_nonneg ρ]
    linarith
  have h2 : 0 < 1 - β * ρ := by linarith
  exact ⟨h2, by positivity⟩

/-- Galí (2015), (4), p. 130: the discretionary path satisfies the targeting rule
`x_t = −(κ/ϑ) π_t`. -/
theorem disc_targeting {β κ ϑ ρ : ℝ} (hϑ : 0 < ϑ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    gapDisc β κ ϑ ρ u t = (-(κ / ϑ)) • inflDisc β κ ϑ ρ u t := by
  rw [gapDisc, inflDisc, smul_smul, psiX, psiPi]
  congr 1
  field_simp

/-- Galí (2015), (5)–(6), p. 130: the discretionary path solves the Phillips curve (2) with an
AR(1) cost-push shock. -/
theorem disc_nkpc {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1)
    {u : ℕ → Ω → ℝ} (har : 𝔼.IsAR1 ρ u) :
    NKPC 𝔼 β κ u (inflDisc β κ ϑ ρ u) (gapDisc β κ ϑ ρ u) := by
  obtain ⟨-, hD⟩ := denom_pos (κ := κ) hβ0 hβ1 hϑ hρ
  intro t
  funext ω
  simp only [inflDisc, gapDisc, map_smul, har.2 t, smul_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [psiPi, psiX]
  field_simp
  ring

/-- Galí (2015), (5)–(6), p. 130: the discretionary path is a bounded adapted plan. -/
theorem disc_plan {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) :
    Plan 𝔼 β κ u (inflDisc β κ ϑ ρ u) (gapDisc β κ ϑ ρ u) := by
  refine ⟨disc_nkpc 𝔼 hβ0 hβ1 hϑ hρ har, fun t => ?_, fun t => ?_, ⟨|psiPi β κ ϑ ρ| * M,
    fun t ω => ?_⟩, ⟨|psiX β κ ϑ ρ| * M, fun t ω => ?_⟩⟩
  · simp only [inflDisc, map_smul, har.1 t]
  · simp only [gapDisc, map_smul, har.1 t]
  · simp only [inflDisc, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hu t ω) (abs_nonneg _)
  · simp only [gapDisc, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hu t ω) (abs_nonneg _)

/-- **Galí (2015), (5)–(6), p. 130**: the discretionary path is the only bounded adapted plan
that satisfies the Phillips curve and the discretionary targeting rule (4)
(`π_t = (ϑβ/(ϑ + κ²)) E_t π_{t+1} + (ϑ/(ϑ + κ²)) u_t` has a unique bounded solution). -/
theorem disc_unique {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) {π x : ℕ → Ω → ℝ}
    (hn : NKPC 𝔼 β κ u π x) (hπb : BoundedProc π)
    (ht : ∀ t, x t = (-(κ / ϑ)) • π t) :
    π = inflDisc β κ ϑ ρ u ∧ x = gapDisc β κ ϑ ρ u := by
  have hD : 0 < ϑ + κ ^ 2 := by positivity
  set a := ϑ / (ϑ + κ ^ 2) with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hD]; nlinarith [sq_nonneg κ]
  have hab : |a * β| < 1 := by
    rw [abs_of_pos (by positivity)]
    nlinarith
  have hred : ∀ (p : ℕ → Ω → ℝ), NKPC 𝔼 β κ u p (fun t => (-(κ / ϑ)) • p t) →
      ∀ t, p t = (a * β) • 𝔼.E t (p (t + 1)) + a • u t := fun p hp t => by
    funext ω
    have e := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    rw [ha]
    field_simp at e ⊢
    linarith
  have hx : x = fun t => (-(κ / ϑ)) • π t := funext ht
  have hdisc : NKPC 𝔼 β κ u (inflDisc β κ ϑ ρ u) (fun t => (-(κ / ϑ)) • inflDisc β κ ϑ ρ u t) := by
    have := disc_nkpc (κ := κ) 𝔼 hβ0 hβ1 hϑ hρ har
    intro t
    rw [this t, disc_targeting hϑ u t]
  obtain ⟨-, -, -, hdb, -⟩ := disc_plan (κ := κ) 𝔼 hβ0 hβ1 hϑ hρ hu har
  have heq := 𝔼.forward_unique hab (hred π (hx ▸ hn)) (hred _ hdisc) hπb hdb
  refine ⟨heq, ?_⟩
  rw [hx, heq]
  funext t
  exact (disc_targeting hϑ u t).symm

/-! ### The stabilisation gain: `δ < ϑ/(ϑ + κ²)` -/

/-- **Galí (2015), p. 137 (key inequality)**: for `κ ≠ 0`, `δ < ϑ/(ϑ + κ²)`. The characteristic
polynomial `γβz² − z + γ` equals `γβa(a − 1) < 0` at `a = ϑ/(ϑ + κ²)`, so `a` lies strictly between
its roots `δ` and `1/(βδ)`. -/
theorem del_lt_disc_coef {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0) :
    del β κ ϑ < ϑ / (ϑ + κ ^ 2) := by
  have hκ2 : 0 < κ ^ 2 := by positivity
  have hD : 0 < ϑ + κ ^ 2 := by positivity
  set a := ϑ / (ϑ + κ ^ 2) with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a < 1 := by rw [ha, div_lt_one hD]; linarith
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hval : gam β κ ϑ * β * a ^ 2 - a + gam β κ ϑ = gam β κ ϑ * β * a * (a - 1) := by
    rw [ha, gam]
    have : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
    field_simp
    ring
  rw [quad_factor hβ0 hβ1 hϑ a] at hval
  have hd := del_pos (κ := κ) hβ0 hϑ
  obtain ⟨-, hroot⟩ := quad_roots hβ0 hβ1 hϑ hκ
  have hneg : gam β κ ϑ * β * a * (a - 1) < 0 := by
    have : 0 < gam β κ ϑ * β * a := by positivity
    nlinarith
  have h2 : a - 1 / (β * del β κ ϑ) < 0 := by linarith
  have hgb : 0 < gam β κ ϑ * β := by positivity
  by_contra hc
  push Not at hc
  have h3 : 0 ≤ (a - del β κ ϑ) * (a - 1 / (β * del β κ ϑ)) := by nlinarith
  nlinarith [mul_nonneg hgb.le h3]

/-- Galí (2015), p. 137: the commitment impact coefficient of inflation is below the
discretionary one, `δ/(1 − δβρ_u) < ϑ/(κ² + ϑ(1 − βρ_u))`, for every `|ρ_u| < 1`. -/
theorem commit_coef_lt {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) :
    0 < del β κ ϑ / (1 - del β κ ϑ * β * ρ) ∧
      del β κ ϑ / (1 - del β κ ϑ * β * ρ) < psiPi β κ ϑ ρ := by
  have hd := del_pos (κ := κ) hβ0 hϑ
  have h1 := one_sub_dbr_pos hβ0 hβ1 hϑ hκ hρ
  obtain ⟨-, hD⟩ := denom_pos (κ := κ) hβ0 hβ1 hϑ hρ
  have hlt := del_lt_disc_coef hβ0 hβ1 hϑ hκ
  refine ⟨div_pos hd h1, ?_⟩
  rw [psiPi, div_lt_div_iff₀ h1 hD]
  rw [lt_div_iff₀ (by positivity)] at hlt
  nlinarith

/-! ### Welfare: commitment beats discretion -/

/-- **Galí (2015), p. 137 (welfare ranking)**: with an AR(1) cost-push shock, the expected loss
under commitment is no larger than under discretion, state by state, since the discretionary plan
is feasible for the commitment problem. -/
theorem commitment_le_discretion (hpo : PullOut 𝔼) {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0) (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (ω : Ω) :
    expLoss 𝔼 β ϑ (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) ω ≤
      expLoss 𝔼 β ϑ (inflDisc β κ ϑ ρ u) (gapDisc β κ ϑ ρ u) ω :=
  ((commitment_optimal 𝔼 hpo hβ0 hβ1 hϑ hκ hu har.1).2 _ _
    (disc_plan 𝔼 hβ0 hβ1 hϑ hρ hu har) ω).1

/-- Galí (2015), (15), p. 136: commitment inflation on impact is `π_0 = δ/(1 − δβρ_u) u_0`. -/
theorem inflC_zero {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) :
    inflC 𝔼 β κ ϑ u 0 = (del β κ ϑ / (1 - del β κ ϑ * β * ρ)) • u 0 := by
  change pHat 𝔼 β κ ϑ u 0 - lag (pHat 𝔼 β κ ϑ u) 0 = _
  rw [pHat_ar1 𝔼 hβ0 hβ1 hϑ hκ hρ hu har 0]
  simp

/-- **Galí (2015), p. 137 (strict welfare gain)**: wherever the initial cost-push shock is
nonzero, commitment yields a strictly lower expected loss than discretion. -/
theorem commitment_lt_discretion (hpo : PullOut 𝔼) {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0) (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (ω : Ω) (hu0 : u 0 ω ≠ 0) :
    expLoss 𝔼 β ϑ (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) ω <
      expLoss 𝔼 β ϑ (inflDisc β κ ϑ ρ u) (gapDisc β κ ϑ ρ u) ω := by
  obtain ⟨hplan, hopt⟩ := commitment_optimal 𝔼 hpo hβ0 hβ1 hϑ hκ hu har.1
  obtain ⟨hle, heq⟩ := hopt _ _ (disc_plan 𝔼 hβ0 hβ1 hϑ hρ hu har) ω
  refine lt_of_le_of_ne hle fun h => ?_
  have h0 := (heq h.symm 0).1
  set c := psiPi β κ ϑ ρ - del β κ ϑ / (1 - del β κ ϑ * β * ρ) with hc
  have hc0 : c ≠ 0 := by
    have := (commit_coef_lt hβ0 hβ1 hϑ hκ hρ).2
    rw [hc]; linarith
  have hfun : (fun ω => (inflDisc β κ ϑ ρ u 0 ω - inflC 𝔼 β κ ϑ u 0 ω) ^ 2) =
      c ^ 2 • (u 0 * u 0) := by
    funext ω'
    rw [inflC_zero 𝔼 hβ0 hβ1 hϑ hκ hρ hu har]
    simp only [inflDisc, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, hc]
    ring
  rw [hfun, map_smul, hpo 0 _ _ (har.1 0), har.1 0] at h0
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, mul_eq_zero, pow_eq_zero_iff',
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true, or_self] at h0
  rcases h0 with h0 | h0
  · exact hc0 h0
  · exact hu0 h0

/-! ### Impact responses (p. 137) -/

/-- **Galí (2015), p. 137**: on impact, inflation is closer to zero under commitment than under
discretion, `|π_0^C| ≤ |π_0^D|`, strictly when `u_0 ≠ 0`, for every `|ρ_u| < 1`. -/
theorem impact_inflation {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (ω : Ω) :
    |inflC 𝔼 β κ ϑ u 0 ω| ≤ |inflDisc β κ ϑ ρ u 0 ω| ∧
      (u 0 ω ≠ 0 → |inflC 𝔼 β κ ϑ u 0 ω| < |inflDisc β κ ϑ ρ u 0 ω|) := by
  obtain ⟨h0, h1⟩ := commit_coef_lt hβ0 hβ1 hϑ hκ hρ
  rw [inflC_zero 𝔼 hβ0 hβ1 hϑ hκ hρ hu har]
  simp only [inflDisc, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos h0,
    abs_of_pos (h0.trans h1)]
  refine ⟨mul_le_mul_of_nonneg_right h1.le (abs_nonneg _), fun hu0 => ?_⟩
  exact mul_lt_mul_of_pos_right h1 (abs_pos.2 hu0)

/-- **Galí (2015), p. 137**: on impact, the output gap is smaller in absolute value under
commitment than under discretion, `|x_0^C| ≤ |x_0^D|`, strictly when `u_0 ≠ 0`. -/
theorem impact_gap {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (ω : Ω) :
    |gapC 𝔼 β κ ϑ u 0 ω| ≤ |gapDisc β κ ϑ ρ u 0 ω| ∧
      (u 0 ω ≠ 0 → |gapC 𝔼 β κ ϑ u 0 ω| < |gapDisc β κ ϑ ρ u 0 ω|) := by
  have hC : gapC 𝔼 β κ ϑ u 0 ω = -(κ / ϑ) * inflC 𝔼 β κ ϑ u 0 ω := by
    change -(κ / ϑ) * pHat 𝔼 β κ ϑ u 0 ω =
      -(κ / ϑ) * (pHat 𝔼 β κ ϑ u 0 ω - lag (pHat 𝔼 β κ ϑ u) 0 ω)
    simp
  have hD : gapDisc β κ ϑ ρ u 0 ω = -(κ / ϑ) * inflDisc β κ ϑ ρ u 0 ω := by
    rw [disc_targeting hϑ u 0]; rfl
  obtain ⟨h1, h2⟩ := impact_inflation 𝔼 hβ0 hβ1 hϑ hκ hρ hu har ω
  have hk : 0 < |κ / ϑ| := abs_pos.2 (div_ne_zero hκ hϑ.ne')
  rw [hC, hD, abs_mul, abs_mul, abs_neg]
  exact ⟨mul_le_mul_of_nonneg_left h1 hk.le, fun hu0 => mul_lt_mul_of_pos_left (h2 hu0) hk⟩

/-- **Galí (2015), p. 137 (closed forms for `ρ_u = 0`)**: on impact, `π_0 = δ u_0` and
`x_0 = −(κδ/ϑ) u_0` under commitment, against `π_0 = ϑ/(κ² + ϑ) u_0` and
`x_0 = −κ/(κ² + ϑ) u_0` under discretion, with `δ < ϑ/(κ² + ϑ)`. -/
theorem impact_rho0 {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 0 u) :
    inflC 𝔼 β κ ϑ u 0 = del β κ ϑ • u 0 ∧
      gapC 𝔼 β κ ϑ u 0 = (-(κ * del β κ ϑ / ϑ)) • u 0 ∧
      inflDisc β κ ϑ 0 u 0 = (ϑ / (κ ^ 2 + ϑ)) • u 0 ∧
      gapDisc β κ ϑ 0 u 0 = (-κ / (κ ^ 2 + ϑ)) • u 0 ∧
      del β κ ϑ < ϑ / (κ ^ 2 + ϑ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [inflC_zero 𝔼 hβ0 hβ1 hϑ hκ (by simp) hu har]; simp
  · rw [gapC_zero 𝔼 hβ0 hβ1 hϑ hκ (by simp) hu har]; simp
  · simp [inflDisc, psiPi]
  · simp [gapDisc, psiX]
  · rw [add_comm]; exact del_lt_disc_coef hβ0 hβ1 hϑ hκ

/-! ### Persistence after a one-time shock (p. 136) -/

/-- **Galí (2015), p. 136 (Figure 5.1, transitory shock)**: if `u_0` is the only shock
(`ρ_u = 0`, `u_t = 0` for `t ≥ 1`), then under commitment `p̂_t = δ^{t+1} u_0`,
`π_{t+1} = −(1 − δ) δ^{t+1} u_0` and `x_t = −(κ/ϑ) δ^{t+1} u_0` (deviations persist, decaying
geometrically, and the price level returns to its initial level), while under discretion
`π_{t+1} = x_{t+1} = 0`. -/
theorem impulse_rho0 {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 0 u)
    (himp : ∀ t, u (t + 1) = 0) (t : ℕ) :
    pHat 𝔼 β κ ϑ u t = del β κ ϑ ^ (t + 1) • u 0 ∧
      inflC 𝔼 β κ ϑ u (t + 1) = (-((1 - del β κ ϑ) * del β κ ϑ ^ (t + 1))) • u 0 ∧
      gapC 𝔼 β κ ϑ u t = (-(κ / ϑ) * del β κ ϑ ^ (t + 1)) • u 0 ∧
      inflDisc β κ ϑ 0 u (t + 1) = 0 ∧ gapDisc β κ ϑ 0 u (t + 1) = 0 := by
  have hp : ∀ s, pHat 𝔼 β κ ϑ u s = del β κ ϑ ^ (s + 1) • u 0 := by
    intro s
    rw [pHat_rho0_sum 𝔼 hβ0 hβ1 hϑ hκ hu har s, Finset.sum_eq_single s]
    · simp
    · intro k hk hks
      have : s - k = (s - k - 1) + 1 := by
        have := Finset.mem_range.1 hk
        omega
      rw [this, himp, smul_zero]
    · intro h; exact absurd (Finset.self_mem_range_succ s) h
  refine ⟨hp t, ?_, ?_, ?_, ?_⟩
  · change pHat 𝔼 β κ ϑ u (t + 1) - pHat 𝔼 β κ ϑ u t = _
    rw [hp, hp, ← sub_smul]
    congr 1
    ring
  · change (-(κ / ϑ)) • pHat 𝔼 β κ ϑ u t = _
    rw [hp, smul_smul]
  · simp [inflDisc, himp]
  · simp [gapDisc, himp]

end Gali.DiscretionCommitment.CommitmentVsDiscretion
