/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OpenEconomy.Supply

/-!
# Equilibrium dynamics under an interest-rate rule in the small open economy

Galí (2015), Chapter 8, §8.3, pp. 239–243. The non-policy block of the small
open economy is the domestic-inflation Phillips curve (37),
`π_{H,t} = β E_t π_{H,t+1} + κ_υ ỹ_t`, and the dynamic IS equation (29),
`ỹ_t = E_t ỹ_{t+1} − σ_υ⁻¹ (i_t − E_t π_{H,t+1} − r^n_t)`, with
`σ_υ = σ / (1 + υ(ϖ − 1))`, `ϖ = ση + (1 − υ)(ση − 1)` and
`κ_υ = λ (σ_υ + (φ + α)/(1 − α))`. Policy follows the Taylor rule (39). The
system is the closed-economy system of Chapter 3 with `σ ↦ σ_υ`, `κ ↦ κ_υ`;
the closed-economy results are restated here from the Chapter 3 project
(`TaylorRuleSystem`, `ShockResponses`) for general `σ_υ, κ_υ > 0`.

## Main results

* `equilibrium_iff_solves`: (29), (37), (39) ⇔ the system (40)
  `x_t = A_υ E_t x_{t+1} + B_υ u_t`.
* `schurStable_AU_iff`, `determinate_iff_41`, `equilibrium_unique`,
  `equilibrium_not_unique`: determinacy ⇔ (41) `κ_υ(φ_π − 1) + (1 − β)φ_y > 0`.
* `equilibrium_iff_msv`, `monetary_shock`: the unique bounded equilibrium after a
  monetary shock (p. 241), `ỹ = −(1 − βρ_v)Λ_v v`, `π_H = −κ_υΛ_v v`, with the
  nominal and real rate responses; `msvLambda_pos`: `Λ_v > 0` under (41).
* `monetary_tot`, `monetary_exchangeRate`: `s = σ_υ ỹ` and `Δe_t` (pp. 241–242).
* `expected_inflation_hasSum`, `priceLevel_longRun`, `exchangeRate_longRun_change`:
  the permanent price-level fall `κ_υΛ_v/(1 − ρ_v)` (p. 242).
* `overshoot_iff`, `overshoot_iff_nominal_rises`: overshooting ⇔
  `σ_υ(1 − βρ_v)(1 − ρ_v) > κ_υρ_v` ⇔ the nominal rate rises on impact.
* `lambdaV_lt_of_slope_pos`, `lambdaV_strictMonoOn` (corrected p. 241 claim) and
  `counterexample_strictAntiOn`, `printed_monotonicity_false` (survey error 3):
  `ση > 1` alone does not make `Λ_v` increasing in openness.
* `closed_economy_equivalence`, `closed_economy_responses` (p. 243): with
  `ση = 1` (in particular `σ = η = 1`) the output-gap and domestic-inflation
  responses are those of the closed economy.
-/

namespace Gali.OpenEconomy.TaylorRule

open Filter Topology
open Gali.OpenEconomy.AggregateDemand (varpi Phi sigmaU varpi_sub_one one_add_mul_varpi_pos
  sigmaU_pos sigmaU_of_sigma_mul_eta sigmaU_strictAntiOn)
open Gali.OpenEconomy.Supply (kappaU)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Open-economy coefficients in terms of primitives

`ϖ`, `Φ`, `σ_υ = σΦ` and their properties are `AggregateDemand.varpi`, `AggregateDemand.Phi`,
`AggregateDemand.sigmaU`; `κ_υ = λ(σ_υ + (φ + α)/(1 − α))` is `Supply.kappaU`. -/

/-- Galí (2015), p. 238: `κ_υ > 0` for `λ > 0`, `φ ≥ 0`, `0 ≤ α < 1`. -/
theorem kappaU_pos {lamC σ η υ varphi α : ℝ} (hlam : 0 < lamC) (hσ : 0 < σ) (hη : 0 < η)
    (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1) (hφ : 0 ≤ varphi) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < kappaU lamC σ η υ varphi α := by
  have h1 := sigmaU_pos hσ hη hυ0 hυ1
  have h2 : 0 ≤ (varphi + α) / (1 - α) := div_nonneg (by linarith) (by linarith)
  unfold kappaU
  positivity

/-- Galí (2015), p. 238: if `ση = 1` then `κ_υ = κ ≡ λ(σ + (φ + α)/(1 − α))`. -/
theorem kappaU_of_mul_eq_one {lamC σ η varphi α : ℝ} (h : σ * η = 1) (υ : ℝ) :
    kappaU lamC σ η υ varphi α = lamC * (σ + (varphi + α) / (1 - α)) := by
  rw [kappaU, sigmaU_of_sigma_mul_eta h]

/-! ### The non-policy block and the rule -/

/-- Galí (2015), p. 240: the real interest rate in terms of domestic goods,
`r_t ≡ i_t − E_t π_{H,t+1}`. -/
def realRate (i infl : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => i t - 𝔼.E t (infl (t + 1))

/-- Galí (2015), eq. (37), p. 238: the domestic-inflation Phillips curve
`π_{H,t} = β E_t π_{H,t+1} + κ_υ ỹ_t` (`kU` is `κ_υ`). -/
def NKPC (β kU : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + kU • ygap t

/-- Galí (2015), eq. (29), p. 236: the open-economy DIS equation in gap form,
`ỹ_t = E_t ỹ_{t+1} − σ_υ⁻¹ (i_t − E_t π_{H,t+1} − r^n_t)` (`sU` is `σ_υ`). -/
def DISGap (sU : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = -sU⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t) + 𝔼.E t (ygap (t + 1))

/-- Galí (2015), eq. (39), p. 239: `i_t = ρ + φ_π π_{H,t} + φ_y y_t + v_t`. -/
def InterestRule (ρ φπ φy : ℝ) (i infl y v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φπ • infl t + φy • y t + v t

/-- Galí (2015), p. 240: the rule (39) with `y_t = ỹ_t + y^n_t`,
`i_t = ρ + φ_π π_{H,t} + φ_y ỹ_t + φ_y y^n_t + v_t`. -/
def InterestRuleGap (ρ φπ φy : ℝ) (i infl ygap yn v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φπ • infl t + φy • ygap t + φy • yn t + v t

/-- Galí (2015), p. 240: since `y_t = ỹ_t + y^n_t`, rule (39) is the same as its
output-gap form. -/
theorem taylorRule_iff_gap {ρ φπ φy : ℝ} {i infl y ygap yn v : ℕ → Ω → ℝ}
    (hy : ∀ t, y t = ygap t + yn t) :
    InterestRule ρ φπ φy i infl y v ↔ InterestRuleGap ρ φπ φy i infl ygap yn v := by
  simp only [InterestRule, InterestRuleGap, hy, smul_add, add_assoc]

/-- Galí (2015), p. 240: the composite shock of (40),
`u_t ≡ r̂^n_t − φ_y y^n_t − v_t` with `r̂^n_t = r^n_t − ρ`. -/
def shockU (ρ φy : ℝ) (rn yn v : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => rn t - (fun _ => ρ) - φy • yn t - v t

/-- Galí (2015), §8.3, pp. 239–240: an equilibrium under rule (39): the NKPC (37),
the DIS (29) and the rule in gap form. -/
def Equilibrium (β sU kU ρ φπ φy : ℝ) (rn yn v ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β kU ygap infl ∧ DISGap 𝔼 sU ygap i infl rn ∧
    InterestRuleGap ρ φπ φy i infl ygap yn v

/-- Galí (2015), p. 240: the equilibrium conditions with the interest rate
substituted out, `(σ_υ + φ_y) ỹ_t + φ_π π_{H,t} = σ_υ E_t ỹ_{t+1} + E_t π_{H,t+1} + u_t`
together with the NKPC (37). -/
def Structural (β sU kU φπ φy : ℝ) (u ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (sU + φy) • ygap t + φπ • infl t
      = sU • 𝔼.E t (ygap (t + 1)) + 𝔼.E t (infl (t + 1)) + u t ∧
    infl t = β • 𝔼.E t (infl (t + 1)) + kU • ygap t

/-- Galí (2015), p. 240: `Ω_υ ≡ 1/(σ_υ + φ_y + κ_υ φ_π)`. -/
noncomputable def omegaU (sU kU φπ φy : ℝ) : ℝ := 1 / (sU + φy + kU * φπ)

/-- Galí (2015), eq. (40), p. 240:
`A_υ ≡ Ω_υ [[σ_υ, 1 − βφ_π], [σ_υκ_υ, κ_υ + β(σ_υ + φ_y)]]`. -/
noncomputable def AU (β sU kU φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![omegaU sU kU φπ φy * sU, omegaU sU kU φπ φy * (1 - β * φπ);
    omegaU sU kU φπ φy * (sU * kU), omegaU sU kU φπ φy * (kU + β * (sU + φy))]

/-- Galí (2015), eq. (40), p. 240: `B_υ ≡ Ω_υ (1, κ_υ)`. -/
noncomputable def BU (sU kU φπ φy : ℝ) : Fin 2 → ℝ :=
  ![omegaU sU kU φπ φy, omegaU sU kU φπ φy * kU]

/-- Galí (2015), eq. (40): the stacked vector `x_t = (ỹ_t, π_{H,t})`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

/-- Galí (2015), eq. (40): the forcing term `B_υ u_t`. -/
def forcing (b : Fin 2 → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t j => b j • u t

/-- Galí (2015), p. 240: with the rule in gap form, (37) and (29) hold if and only
if the structural equations hold with `u_t = r̂^n_t − φ_y y^n_t − v_t`
(restated from the Chapter 3 project). -/
theorem nk_iff_structural {β sU kU ρ φπ φy : ℝ} (hσ : sU ≠ 0)
    {rn yn v ygap infl i : ℕ → Ω → ℝ} (hrule : InterestRuleGap ρ φπ φy i infl ygap yn v) :
    (NKPC 𝔼 β kU ygap infl ∧ DISGap 𝔼 sU ygap i infl rn) ↔
      Structural 𝔼 β sU kU φπ φy (shockU ρ φy rn yn v) ygap infl := by
  have hinv : sU * sU⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t
    refine ⟨?_, hp t⟩
    funext ω
    have e := congrFun (hd t) ω
    have r := congrFun (hrule t) ω
    simp only [shockU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ⊢
    linear_combination sU * e - r - (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hinv
  · intro h
    refine ⟨fun t => (h t).2, fun t => ?_⟩
    funext ω
    have e := congrFun (h t).1 ω
    have r := congrFun (hrule t) ω
    simp only [shockU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ⊢
    linear_combination sU⁻¹ * e + sU⁻¹ * r
      - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- Galí (2015), eq. (40), p. 240: the structural equations are equivalent to
`x_t = A_υ E_t x_{t+1} + B_υ u_t`, provided `σ_υ + φ_y + κ_υ φ_π ≠ 0`. -/
theorem structural_iff_solves {β sU kU φπ φy : ℝ} (hS : sU + φy + kU * φπ ≠ 0)
    (u ygap infl : ℕ → Ω → ℝ) :
    Structural 𝔼 β sU kU φπ φy u ygap infl ↔
      𝔼.Solves (AU β sU kU φπ φy) (forcing (BU sU kU φπ φy) u) (stack ygap infl) := by
  constructor
  · intro h t j
    obtain ⟨h1, h2⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    fin_cases j
    · simp [stack, forcing, AU, BU, omegaU]
      field_simp
      linear_combination e1 - φπ * e2
    · simp [stack, forcing, AU, BU, omegaU]
      field_simp
      linear_combination kU * e1 + (sU + φy) * e2
  · intro h t
    have h0 := h t 0
    have h1 := h t 1
    simp only [stack, Fin.isValue, Matrix.cons_val_zero, AU, omegaU, one_div, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, forcing, BU] at h0 h1
    refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination (sU + φy) * e0 + φπ * e1
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination e1 - kU * e0

/-- Galí (2015), eq. (40), p. 240: with the rule (39) in gap form, `(ỹ, π_H)`
satisfies (37) and (29) if and only if it solves `x_t = A_υ E_t x_{t+1} + B_υ u_t`. -/
theorem equilibrium_iff_solves {β sU kU ρ φπ φy : ℝ} (hσ : sU ≠ 0)
    (hS : sU + φy + kU * φπ ≠ 0) {rn yn v ygap infl i : ℕ → Ω → ℝ}
    (hrule : InterestRuleGap ρ φπ φy i infl ygap yn v) :
    Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap infl i ↔
      𝔼.Solves (AU β sU kU φπ φy) (forcing (BU sU kU φπ φy) (shockU ρ φy rn yn v))
        (stack ygap infl) := by
  rw [← structural_iff_solves 𝔼 hS, ← nk_iff_structural 𝔼 hσ hrule]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hrule⟩⟩

/-- Galí (2015), p. 240: `tr A_υ = (σ_υ(1 + β) + κ_υ + βφ_y)/(σ_υ + φ_y + κ_υφ_π)`. -/
theorem tr2_AU {β sU kU φπ φy : ℝ} (hS : sU + φy + kU * φπ ≠ 0) :
    tr2 (AU β sU kU φπ φy) = (sU * (1 + β) + kU + β * φy) / (sU + φy + kU * φπ) := by
  simp only [tr2, AU, omegaU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), p. 240: `det A_υ = σ_υβ/(σ_υ + φ_y + κ_υφ_π)`. -/
theorem det2_AU {β sU kU φπ φy : ℝ} (hS : sU + φy + kU * φπ ≠ 0) :
    det2 (AU β sU kU φπ φy) = sU * β / (sU + φy + kU * φπ) := by
  simp only [det2, AU, omegaU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), eq. (41), p. 240 (Bullard–Mitra): for `σ_υ, κ_υ > 0`, `0 < β < 1`
and `φ_π, φ_y ≥ 0`, both eigenvalues of `A_υ` lie inside the unit circle if and
only if `κ_υ(φ_π − 1) + (1 − β)φ_y > 0`. -/
theorem schurStable_AU_iff {β sU kU φπ φy : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    SchurStable (tr2 (AU β sU kU φπ φy)) (det2 (AU β sU kU φπ φy)) ↔
      0 < kU * (φπ - 1) + (1 - β) * φy := by
  have hS : 0 < sU + φy + kU * φπ := by positivity
  rw [tr2_AU hS.ne', det2_AU hS.ne']
  have hD0 : 0 < sU * β / (sU + φy + kU * φπ) := by positivity
  have hD1 : sU * β / (sU + φy + kU * φπ) < 1 := by
    rw [div_lt_one hS]; nlinarith
  have hT0 : 0 < (sU * (1 + β) + kU + β * φy) / (sU + φy + kU * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0]
  have key : (sU * (1 + β) + kU + β * φy) / (sU + φy + kU * φπ)
        < 1 + sU * β / (sU + φy + kU * φπ)
      ↔ sU * (1 + β) + kU + β * φy < sU + φy + kU * φπ + sU * β := by
    rw [one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  rw [key]
  constructor
  · rintro ⟨-, h⟩; linarith
  · intro h; exact ⟨hD1, by linarith⟩

/-- Galí (2015), eq. (41), p. 240: the system (40) is determinate (at most one
bounded adapted solution for every forcing process) if and only if
`κ_υ(φ_π − 1) + (1 − β)φ_y > 0`. -/
theorem determinate_iff_41 [Nonempty Ω] {β sU kU φπ φy : ℝ} (hσ : 0 < sU) (hκ : 0 < kU)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AU β sU kU φπ φy) ↔ 0 < kU * (φπ - 1) + (1 - β) * φy :=
  (𝔼.determinate_iff _).trans (schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ hφy)

/-- Galí (2015), eq. (41) in primitives: determinacy of (40) with
`σ_υ = σ/(1 + υ(ϖ − 1))` and `κ_υ = λ(σ_υ + (φ + α)/(1 − α))`. -/
theorem determinate_iff_41_primitives [Nonempty Ω] {β lamC σ η υ varphi α φπ φy : ℝ}
    (hlam : 0 < lamC) (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1)
    (hφ : 0 ≤ varphi) (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AU β (sigmaU σ η υ) (kappaU lamC σ η υ varphi α) φπ φy) ↔
      0 < kappaU lamC σ η υ varphi α * (φπ - 1) + (1 - β) * φy :=
  determinate_iff_41 𝔼 (sigmaU_pos hσ hη hυ0 hυ1)
    (kappaU_pos hlam hσ hη hυ0 hυ1 hφ hα0 hα1) hβ0 hβ1 hφπ hφy

/-- Two bounded processes stack to a bounded vector process. -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Two adapted processes stack to an adapted vector process. -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-- Galí (2015), p. 240: under (41), two equilibria with bounded adapted output gap
and domestic inflation, driven by the same exogenous processes, coincide (output
gap, domestic inflation and the nominal rate). -/
theorem equilibrium_unique {β sU kU ρ φπ φy : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy)
    {rn yn v ygap infl i ygap' infl' i' : ℕ → Ω → ℝ}
    (he : Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap infl i)
    (he' : Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap' infl' i')
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (ha' : 𝔼.Adapted ygap')
    (hb' : 𝔼.Adapted infl') (hba : BoundedProc ygap) (hbb : BoundedProc infl)
    (hba' : BoundedProc ygap') (hbb' : BoundedProc infl') :
    ygap = ygap' ∧ infl = infl' ∧ i = i' := by
  have hS : sU + φy + kU * φπ ≠ 0 := by positivity
  have hx := (equilibrium_iff_solves 𝔼 hσ.ne' hS he.2.2).mp he
  have hy := (equilibrium_iff_solves 𝔼 hσ.ne' hS he'.2.2).mp he'
  have heq := 𝔼.system_unique ((schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h41) hx hy
    (adaptedVec_stack 𝔼 ha hb) (adaptedVec_stack 𝔼 ha' hb')
    (boundedVec_stack hba hbb) (boundedVec_stack hba' hbb')
  have h1 : ygap = ygap' := funext fun t => by
    simpa [stack] using congrFun (congrFun heq t) 0
  have h2 : infl = infl' := funext fun t => by
    simpa [stack] using congrFun (congrFun heq t) 1
  refine ⟨h1, h2, funext fun t => ?_⟩
  rw [he.2.2 t, he'.2.2 t, h1, h2]

/-- Galí (2015), p. 240: if (41) fails, next to any equilibrium with bounded adapted
output gap and domestic inflation there is a second one. -/
theorem equilibrium_not_unique [Nonempty Ω] {β sU kU ρ φπ φy : ℝ} (hσ : 0 < sU)
    (hκ : 0 < kU) (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (h41 : kU * (φπ - 1) + (1 - β) * φy ≤ 0) {rn yn v ygap infl i : ℕ → Ω → ℝ}
    (he : Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap infl i)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) :
    ∃ ygap' infl' i', Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap' infl' i' ∧
      𝔼.Adapted ygap' ∧ 𝔼.Adapted infl' ∧ BoundedProc ygap' ∧ BoundedProc infl' ∧
      (ygap' ≠ ygap ∨ infl' ≠ infl) := by
  have hS : sU + φy + kU * φπ ≠ 0 := by positivity
  have hns : ¬ SchurStable (tr2 (AU β sU kU φπ φy)) (det2 (AU β sU kU φπ φy)) := by
    rw [schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ hφy]; linarith
  have hx := (equilibrium_iff_solves 𝔼 hσ.ne' hS he.2.2).mp he
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns hx
    (adaptedVec_stack 𝔼 ha hb) (boundedVec_stack hba hbb)
  set ygap' : ℕ → Ω → ℝ := fun t => y t 0
  set infl' : ℕ → Ω → ℝ := fun t => y t 1
  have hst : stack ygap' infl' = y := by
    funext t j
    fin_cases j <;> rfl
  have hrule' : InterestRuleGap ρ φπ φy
      (fun t => (fun _ => ρ) + φπ • infl' t + φy • ygap' t + φy • yn t + v t)
      infl' ygap' yn v := fun t => rfl
  refine ⟨ygap', infl', _, (equilibrium_iff_solves 𝔼 hσ.ne' hS hrule').mpr (hst ▸ hy),
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-! ### The minimum-state-variable solution -/

/-- Galí (2015), p. 241: the denominator
`(1 − βρ_v)[σ_υ(1 − ρ_v) + φ_y] + κ_υ(φ_π − ρ_v)` of `Λ_v`. -/
def msvDen (β sU kU φπ φy ρv : ℝ) : ℝ := (1 - β * ρv) * (sU * (1 - ρv) + φy) + kU * (φπ - ρv)

/-- Galí (2015), p. 241: `Λ_v ≡ 1/((1 − βρ_v)[σ_υ(1 − ρ_v) + φ_y] + κ_υ(φ_π − ρ_v))`. -/
noncomputable def msvLambda (β sU kU φπ φy ρv : ℝ) : ℝ := 1 / msvDen β sU kU φπ φy ρv

/-- Galí (2015), p. 241: the MSV output-gap coefficient `(1 − βρ_u)Λ_u`. -/
noncomputable def msvPsiY (β sU kU φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * msvLambda β sU kU φπ φy ρu

/-- Galí (2015), p. 241: the MSV domestic-inflation coefficient `κ_υΛ_u`. -/
noncomputable def msvPsiPi (β sU kU φπ φy ρu : ℝ) : ℝ := kU * msvLambda β sU kU φπ φy ρu

/-- Galí (2015), p. 241: the denominator of `Λ_v` equals
`(1 − ρ_v)((1 − βρ_v)σ_υ + κ_υ + βφ_y) + [κ_υ(φ_π − 1) + (1 − β)φ_y]`. -/
theorem msvDen_eq (β sU kU φπ φy ρv : ℝ) :
    msvDen β sU kU φπ φy ρv
      = (1 - ρv) * ((1 - β * ρv) * sU + kU + β * φy) + (kU * (φπ - 1) + (1 - β) * φy) := by
  unfold msvDen; ring

/-- Galí (2015), p. 241: under (41) and `ρ_v < 1` the denominator of `Λ_v` is
positive. -/
theorem msvDen_pos {β sU kU φπ φy ρv : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) : 0 < msvDen β sU kU φπ φy ρv := by
  rw [msvDen_eq]
  have hbr : β * ρv < 1 := by nlinarith
  have h1 : 0 ≤ (1 - β * ρv) * sU := by nlinarith
  have h2 : 0 ≤ (1 - ρv) * ((1 - β * ρv) * sU + kU + β * φy) := by
    apply mul_nonneg <;> nlinarith
  linarith

/-- Galí (2015), p. 241: "as long as (41) is satisfied, `Λ_v > 0`" (for `ρ_v < 1`). -/
theorem msvLambda_pos {β sU kU φπ φy ρv : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) : 0 < msvLambda β sU kU φπ φy ρv :=
  one_div_pos.mpr (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h41)

/-- A scalar multiple of an AR(1) process is AR(1) with the same persistence. -/
theorem isAR1_smul {ρu : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) (c : ℝ) :
    𝔼.IsAR1 ρu (fun t => c • u t) :=
  ⟨fun t => by simp only [map_smul, hu.1 t], fun t => by
    simp only [map_smul, hu.2 t, smul_comm c ρu]⟩

/-- A scalar multiple of a bounded process is bounded. -/
theorem boundedProc_smul {s : ℕ → Ω → ℝ} (hs : BoundedProc s) (c : ℝ) :
    BoundedProc (fun t => c • s t) := by
  obtain ⟨M, hM⟩ := hs
  exact ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩

/-- Galí (2015), p. 241 (undetermined coefficients): for an AR(1) composite shock
the MSV processes `ỹ_t = (1 − βρ_u)Λ_u u_t`, `π_{H,t} = κ_υΛ_u u_t` satisfy the
structural equations (existence). -/
theorem msv_structural {β sU kU φπ φy ρu : ℝ} (hD : msvDen β sU kU φπ φy ρu ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) :
    Structural 𝔼 β sU kU φπ φy u (fun t => msvPsiY β sU kU φπ φy ρu • u t)
      (fun t => msvPsiPi β sU kU φπ φy ρu • u t) := by
  have c1 : (sU + φy) * msvPsiY β sU kU φπ φy ρu + φπ * msvPsiPi β sU kU φπ φy ρu
      = sU * (msvPsiY β sU kU φπ φy ρu * ρu) + msvPsiPi β sU kU φπ φy ρu * ρu + 1 := by
    unfold msvPsiY msvPsiPi msvLambda
    field_simp
    unfold msvDen
    ring
  have c2 : msvPsiPi β sU kU φπ φy ρu
      = β * (msvPsiPi β sU kU φπ φy ρu * ρu) + kU * msvPsiY β sU kU φπ φy ρu := by
    unfold msvPsiY msvPsiPi
    ring
  intro t
  simp only [map_smul, hu.2 t, smul_smul]
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c1
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c2

/-- Galí (2015), p. 241: under (41), for a bounded AR(1) composite shock with
`ρ_u < 1`, every bounded adapted solution of the structural equations is the MSV
solution (uniqueness). -/
theorem msv_unique {β sU kU φπ φy ρu : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) {u ygap infl : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρu u) (hub : BoundedProc u)
    (hs : Structural 𝔼 β sU kU φπ φy u ygap infl) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    ygap = (fun t => msvPsiY β sU kU φπ φy ρu • u t) ∧
      infl = (fun t => msvPsiPi β sU kU φπ φy ρu • u t) := by
  have hS : sU + φy + kU * φπ ≠ 0 := by positivity
  have hD := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h41).ne'
  have heq := 𝔼.system_unique ((schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h41)
    ((structural_iff_solves 𝔼 hS _ _ _).mp hs)
    ((structural_iff_solves 𝔼 hS _ _ _).mp (msv_structural 𝔼 hD hu))
    (adaptedVec_stack 𝔼 ha hb)
    (adaptedVec_stack 𝔼 (isAR1_smul 𝔼 hu _).1 (isAR1_smul 𝔼 hu _).1)
    (boundedVec_stack hba hbb) (boundedVec_stack (boundedProc_smul hub _)
      (boundedProc_smul hub _))
  exact ⟨funext fun t => by simpa [stack] using congrFun (congrFun heq t) 0,
    funext fun t => by simpa [stack] using congrFun (congrFun heq t) 1⟩

/-- Galí (2015), pp. 240–241: under (41), with a bounded AR(1) composite shock of
persistence `ρ_u < 1`, a triple `(ỹ, π_H, i)` with bounded adapted `ỹ`, `π_H` is an
equilibrium if and only if it is the MSV solution with `i` given by the rule; the
MSV triple is bounded and adapted, so it is the unique bounded equilibrium. -/
theorem equilibrium_iff_msv {β sU kU ρ φπ φy ρu : ℝ} (hσ : 0 < sU) (hκ : 0 < kU)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) {rn yn v : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρu (shockU ρ φy rn yn v)) (hub : BoundedProc (shockU ρ φy rn yn v))
    {ygap infl i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl)
    (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap infl i ↔
      ygap = (fun t => msvPsiY β sU kU φπ φy ρu • shockU ρ φy rn yn v t) ∧
      infl = (fun t => msvPsiPi β sU kU φπ φy ρu • shockU ρ φy rn yn v t) ∧
      i = fun t => (fun _ => ρ) + φπ • infl t + φy • ygap t + φy • yn t + v t := by
  have hD := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h41).ne'
  constructor
  · intro he
    obtain ⟨h1, h2⟩ := msv_unique 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h41 hu hub
      ((nk_iff_structural 𝔼 hσ.ne' he.2.2).mp ⟨he.1, he.2.1⟩) ha hb hba hbb
    exact ⟨h1, h2, funext he.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    have hrule : InterestRuleGap ρ φπ φy i infl ygap yn v := fun t => by rw [h3]
    have hs := (nk_iff_structural 𝔼 (β := β) (kU := kU) (rn := rn) hσ.ne' hrule).mpr
      (h1 ▸ h2 ▸ msv_structural 𝔼 hD hu)
    exact ⟨hs.1, hs.2, hrule⟩

/-! ### Monetary policy shock (§8.3.1, pp. 241–242) -/

/-- Galí (2015), p. 241: output-gap response `−(1 − βρ_v)Λ_v`. -/
noncomputable def monYgapCoef (β sU kU φπ φy ρv : ℝ) : ℝ :=
  -((1 - β * ρv) * msvLambda β sU kU φπ φy ρv)

/-- Galí (2015), p. 241: domestic-inflation response `−κ_υΛ_v`. -/
noncomputable def monInflCoef (β sU kU φπ φy ρv : ℝ) : ℝ := -(kU * msvLambda β sU kU φπ φy ρv)

/-- Galí (2015), p. 241: real-rate response; the book's bracket
`1 − Λ_v((φ_π − ρ_v)κ_υ + φ_y(1 − βρ_v))` equals `Λ_v(1 − βρ_v)σ_υ(1 − ρ_v)`
(`monRealCoef_eq_book`). -/
noncomputable def monRealCoef (β sU kU φπ φy ρv : ℝ) : ℝ :=
  msvLambda β sU kU φπ φy ρv * (1 - β * ρv) * sU * (1 - ρv)

/-- Galí (2015), p. 241: nominal-rate response; the book's bracket
`1 − Λ_v(φ_πκ_υ + φ_y(1 − βρ_v))` equals `Λ_v[σ_υ(1 − βρ_v)(1 − ρ_v) − κ_υρ_v]`
(`monNomCoef_eq_book`). -/
noncomputable def monNomCoef (β sU kU φπ φy ρv : ℝ) : ℝ :=
  msvLambda β sU kU φπ φy ρv * (sU * (1 - β * ρv) * (1 - ρv) - kU * ρv)

/-- Galí (2015), p. 241: the real-rate bracket in the book's form,
`1 − Λ_v((φ_π − ρ_v)κ_υ + φ_y(1 − βρ_v)) = Λ_v(1 − βρ_v)σ_υ(1 − ρ_v)`. -/
theorem monRealCoef_eq_book {β sU kU φπ φy ρv : ℝ} (hD : msvDen β sU kU φπ φy ρv ≠ 0) :
    1 - msvLambda β sU kU φπ φy ρv * ((φπ - ρv) * kU + φy * (1 - β * ρv))
      = monRealCoef β sU kU φπ φy ρv := by
  unfold monRealCoef msvLambda
  field_simp
  unfold msvDen
  ring

/-- Galí (2015), p. 241: the nominal-rate bracket in the book's form,
`1 − Λ_v(φ_πκ_υ + φ_y(1 − βρ_v)) = Λ_v[σ_υ(1 − βρ_v)(1 − ρ_v) − κ_υρ_v]`. -/
theorem monNomCoef_eq_book {β sU kU φπ φy ρv : ℝ} (hD : msvDen β sU kU φπ φy ρv ≠ 0) :
    1 - msvLambda β sU kU φπ φy ρv * (φπ * kU + φy * (1 - β * ρv))
      = monNomCoef β sU kU φπ φy ρv := by
  unfold monNomCoef msvLambda
  field_simp
  unfold msvDen
  ring

/-- Galí (2015), p. 241: "the real rate increases unambiguously ... because the term
in square brackets is always positive": `Λ_v(1 − βρ_v)σ_υ(1 − ρ_v) > 0` under (41). -/
theorem monRealCoef_pos {β sU kU φπ φy ρv : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) : 0 < monRealCoef β sU kU φπ φy ρv := by
  have hL := msvLambda_pos hσ hκ hβ0 hβ1 hφy hρ1 h41
  have hbr : 0 < 1 - β * ρv := by nlinarith
  have h1 : 0 < 1 - ρv := by linarith
  unfold monRealCoef
  positivity

/-- **Monetary policy shock** (Galí 2015, p. 241): with `r^n_t = ρ` and `y^n_t = 0`,
an AR(1) monetary shock `v` with `ρ_v < 1` and (41), every equilibrium with bounded
adapted `ỹ`, `π_H` has `ỹ_t = −(1 − βρ_v)Λ_v v_t`, `π_{H,t} = −κ_υΛ_v v_t`,
`r_t − ρ = Λ_v(1 − βρ_v)σ_υ(1 − ρ_v) v_t` and
`i_t − ρ = Λ_v[σ_υ(1 − βρ_v)(1 − ρ_v) − κ_υρ_v] v_t`. -/
theorem monetary_shock {β sU kU ρ φπ φy ρv : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) {rn yn v ygap infl i : ℕ → Ω → ℝ}
    (hv : 𝔼.IsAR1 ρv v) (hvb : BoundedProc v) (hrn : ∀ t, rn t = fun _ => ρ)
    (hyn : ∀ t, yn t = 0) (he : Equilibrium 𝔼 β sU kU ρ φπ φy rn yn v ygap infl i)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) :
    (∀ t, ygap t = monYgapCoef β sU kU φπ φy ρv • v t) ∧
      (∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t) ∧
      (∀ t, realRate 𝔼 i infl t - (fun _ => ρ) = monRealCoef β sU kU φπ φy ρv • v t) ∧
      (∀ t, i t - (fun _ => ρ) = monNomCoef β sU kU φπ φy ρv • v t) := by
  have hU : shockU ρ φy rn yn v = fun t => (-1 : ℝ) • v t := by
    funext t
    simp [shockU, hrn, hyn]
  have hu : 𝔼.IsAR1 ρv (shockU ρ φy rn yn v) := by rw [hU]; exact isAR1_smul 𝔼 hv _
  have hub : BoundedProc (shockU ρ φy rn yn v) := by rw [hU]; exact boundedProc_smul hvb _
  obtain ⟨h1, h2, -⟩ :=
    (equilibrium_iff_msv 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h41 hu hub ha hb hba hbb).mp he
  have hy : ∀ t, ygap t = monYgapCoef β sU kU φπ φy ρv • v t := fun t => by
    rw [h1, hU]; simp only [smul_smul, monYgapCoef, msvPsiY, mul_neg_one]
  have hp : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t := fun t => by
    rw [h2, hU]; simp only [smul_smul, monInflCoef, msvPsiPi, mul_neg_one]
  have hD := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h41).ne'
  have hLD : msvLambda β sU kU φπ φy ρv * msvDen β sU kU φπ φy ρv = 1 := by
    unfold msvLambda; field_simp
  have hinv : sU * sU⁻¹ = 1 := mul_inv_cancel₀ hσ.ne'
  have hr : ∀ t, realRate 𝔼 i infl t - (fun _ => ρ) = monRealCoef β sU kU φπ φy ρv • v t := by
    intro t
    have hd := he.2.1 t
    rw [hy t, hy (t + 1), map_smul, hv.2 t, hrn t] at hd
    funext ω
    have e := congrFun hd ω
    simp only [realRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    simp only [monYgapCoef, monRealCoef] at e ⊢
    linear_combination sU * e - (i t ω - (𝔼.E t) (infl (t + 1)) ω - ρ) * hinv
  refine ⟨hy, hp, hr, fun t => ?_⟩
  have h := hr t
  rw [realRate, hp (t + 1), map_smul, hv.2 t] at h
  funext ω
  have e := congrFun h ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  simp only [monInflCoef, monRealCoef, monNomCoef] at e ⊢
  linear_combination e

/-- Galí (2015), p. 241: under (41) a monetary tightening lowers the output gap and
domestic inflation and raises the real rate. -/
theorem monetary_signs {β sU kU φπ φy ρv : ℝ} (hσ : 0 < sU) (hκ : 0 < kU) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1) (h41 : 0 < kU * (φπ - 1) + (1 - β) * φy) :
    monYgapCoef β sU kU φπ φy ρv < 0 ∧ monInflCoef β sU kU φπ φy ρv < 0 ∧
      0 < monRealCoef β sU kU φπ φy ρv := by
  have hL := msvLambda_pos hσ hκ hβ0 hβ1 hφy hρ1 h41
  have hbr : 0 < 1 - β * ρv := by nlinarith
  refine ⟨?_, ?_, monRealCoef_pos hσ hκ hβ0 hβ1 hφy hρ1 h41⟩
  · unfold monYgapCoef; nlinarith [mul_pos hbr hL]
  · unfold monInflCoef; nlinarith [mul_pos hκ hL]

/-- Galí (2015), pp. 241–242, using (27) with `y^n = y* = 0` and no preference
shock: the terms of trade are `s_t = σ_υ ỹ_t = −σ_υ(1 − βρ_v)Λ_v v_t`. -/
theorem monetary_tot {sU β kU φπ φy ρv : ℝ} {ygap s v : ℕ → Ω → ℝ}
    (hs : ∀ t, s t = sU • ygap t) (hy : ∀ t, ygap t = monYgapCoef β sU kU φπ φy ρv • v t)
    (t : ℕ) : s t = (-(sU * (1 - β * ρv) * msvLambda β sU kU φπ φy ρv)) • v t := by
  rw [hs, hy, smul_smul, monYgapCoef]
  congr 1
  ring

/-- Galí (2015), p. 242: with the terms of trade `s_t = e_t − p_{H,t}` (eq. (14),
`p* = 0`) and `p_{H,t+1} = p_{H,t} + π_{H,t+1}`, the nominal exchange rate moves by
`Δe_{t+1} = −Λ_v[σ_υ(1 − βρ_v) + κ_υ]v_{t+1} + σ_υ(1 − βρ_v)Λ_v v_t`. -/
theorem monetary_exchangeRate {sU β kU φπ φy ρv : ℝ} {ygap infl s e pH v : ℕ → Ω → ℝ}
    (hs : ∀ t, s t = sU • ygap t) (hy : ∀ t, ygap t = monYgapCoef β sU kU φπ φy ρv • v t)
    (hp : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t)
    (h14 : ∀ t, s t = e t - pH t) (hpH : ∀ t, pH (t + 1) = pH t + infl (t + 1)) (t : ℕ) :
    e (t + 1) - e t
      = (-(msvLambda β sU kU φπ φy ρv * (sU * (1 - β * ρv) + kU))) • v (t + 1)
        + (sU * (1 - β * ρv) * msvLambda β sU kU φπ φy ρv) • v t := by
  have e1 : e (t + 1) = s (t + 1) + pH (t + 1) := by rw [h14]; abel
  have e0 : e t = s t + pH t := by rw [h14]; abel
  rw [e1, e0, hpH, monetary_tot hs hy, monetary_tot hs hy, hp]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, monInflCoef]
  ring

/-! ### Long-run price level and exchange-rate overshooting (p. 242) -/

/-- Galí (2015), p. 242: the domestic price level is the sum of inflation,
`p_{H,t+1+k} = p_{H,t} + Σ_{j ≤ k} π_{H,t+1+j}`. -/
theorem priceLevel_sum {pH infl : ℕ → Ω → ℝ} (hp : ∀ t, pH (t + 1) = pH t + infl (t + 1))
    (t k : ℕ) :
    pH (t + 1 + k) = pH t + ∑ j ∈ Finset.range (k + 1), infl (t + 1 + j) := by
  induction k with
  | zero => simp [hp t]
  | succ k ih =>
    have h : t + 1 + (k + 1) = (t + 1 + k) + 1 := by omega
    rw [h, hp, ih, Finset.sum_range_succ _ (k + 1), add_assoc, ← h]

/-- Galí (2015), p. 242: the expected price-level path after a monetary shock,
`E_{t+1} p_{H,t+1+k} = p_{H,t} + (Σ_{j ≤ k} c ρ_vʲ) v_{t+1}` when `π_H = c v`. -/
theorem expected_priceLevel {ρv c : ℝ} {pH infl v : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted pH)
    (hp : ∀ t, pH (t + 1) = pH t + infl (t + 1)) (hinfl : ∀ t, infl t = c • v t)
    (hv : 𝔼.IsAR1 ρv v) (t k : ℕ) :
    𝔼.E (t + 1) (pH (t + 1 + k))
      = pH t + (∑ j ∈ Finset.range (k + 1), c * ρv ^ j) • v (t + 1) := by
  have h0 : 𝔼.E (t + 1) (pH t) = pH t := by
    have := 𝔼.known (Nat.le_succ t) (pH t)
    rwa [hpa t] at this
  rw [priceLevel_sum hp, map_add, h0, map_sum, Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hinfl, map_smul, 𝔼.ar1_iterate hv, smul_smul]

/-- Galí (2015), p. 242: the expected cumulative domestic inflation after a monetary
shock converges: `Σ_k E_t π_{H,t+k} = −κ_υΛ_v/(1 − ρ_v) · v_t` (for `0 ≤ ρ_v < 1`). -/
theorem expected_inflation_hasSum {β sU kU φπ φy ρv : ℝ} (hρ0 : 0 ≤ ρv) (hρ1 : ρv < 1)
    {infl v : ℕ → Ω → ℝ} (hinfl : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t)
    (hv : 𝔼.IsAR1 ρv v) (t : ℕ) (ω : Ω) :
    HasSum (fun k => 𝔼.E t (infl (t + k)) ω)
      (-(kU * msvLambda β sU kU φπ φy ρv) / (1 - ρv) * v t ω) := by
  have hg := ((hasSum_geometric_of_lt_one hρ0 hρ1).mul_left
    (monInflCoef β sU kU φπ φy ρv)).mul_right (v t ω)
  convert hg using 1
  · funext k
    rw [hinfl, map_smul, 𝔼.ar1_iterate hv, smul_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
  · rw [monInflCoef, div_eq_mul_inv]

/-- Galí (2015), p. 242: the tsum form of the permanent price-level fall,
`∑' k, E_t π_{H,t+k} = −κ_υΛ_v/(1 − ρ_v) · v_t`. -/
theorem expected_inflation_tsum {β sU kU φπ φy ρv : ℝ} (hρ0 : 0 ≤ ρv) (hρ1 : ρv < 1)
    {infl v : ℕ → Ω → ℝ} (hinfl : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t)
    (hv : 𝔼.IsAR1 ρv v) (t : ℕ) (ω : Ω) :
    ∑' k, 𝔼.E t (infl (t + k)) ω = -(kU * msvLambda β sU kU φπ φy ρv) / (1 - ρv) * v t ω :=
  (expected_inflation_hasSum 𝔼 hρ0 hρ1 hinfl hv t ω).tsum_eq

/-- Galí (2015), p. 242: the permanent decrease in the domestic price level,
`E_{t+1} p_{H,t+1+k} → p_{H,t} − κ_υΛ_v/(1 − ρ_v) · v_{t+1}` as `k → ∞`. -/
theorem priceLevel_longRun {β sU kU φπ φy ρv : ℝ} (hρ0 : 0 ≤ ρv) (hρ1 : ρv < 1)
    {pH infl v : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted pH) (hp : ∀ t, pH (t + 1) = pH t + infl (t + 1))
    (hinfl : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t) (hv : 𝔼.IsAR1 ρv v)
    (t : ℕ) (ω : Ω) :
    Tendsto (fun k => 𝔼.E (t + 1) (pH (t + 1 + k)) ω) atTop
      (𝓝 (pH t ω + -(kU * msvLambda β sU kU φπ φy ρv) / (1 - ρv) * v (t + 1) ω)) := by
  have hg := ((hasSum_geometric_of_lt_one hρ0 hρ1).mul_left
    (monInflCoef β sU kU φπ φy ρv)).tendsto_sum_nat
  have hg' := ((hg.comp (tendsto_add_atTop_nat 1)).mul_const (v (t + 1) ω)).const_add (pH t ω)
  rw [monInflCoef, ← div_eq_mul_inv] at hg'
  refine hg'.congr fun k => ?_
  rw [expected_priceLevel 𝔼 hpa hp hinfl hv t k]
  simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, monInflCoef]

/-- Galí (2015), p. 242: the impact response of the nominal exchange rate to a unit
shock from rest, `−Λ_v[σ_υ(1 − βρ_v) + κ_υ]`. -/
noncomputable def eImpact (β sU kU φπ φy ρv : ℝ) : ℝ :=
  -(msvLambda β sU kU φπ φy ρv * (sU * (1 - β * ρv) + kU))

/-- Galí (2015), p. 242: the long-run response of the nominal exchange rate (equal to
the price-level response), `−κ_υΛ_v/(1 − ρ_v)`. -/
noncomputable def eLongRun (β sU kU φπ φy ρv : ℝ) : ℝ :=
  -(kU * msvLambda β sU kU φπ φy ρv) / (1 - ρv)

/-- Galí (2015), p. 242: starting from rest (`v_t = 0`) the exchange rate jumps on
impact by `eImpact · v_{t+1}`. -/
theorem exchangeRate_impact {sU β kU φπ φy ρv : ℝ} {ygap infl s e pH v : ℕ → Ω → ℝ}
    (hs : ∀ t, s t = sU • ygap t) (hy : ∀ t, ygap t = monYgapCoef β sU kU φπ φy ρv • v t)
    (hp : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t)
    (h14 : ∀ t, s t = e t - pH t) (hpH : ∀ t, pH (t + 1) = pH t + infl (t + 1)) (t : ℕ)
    (hv0 : v t = 0) : e (t + 1) - e t = eImpact β sU kU φπ φy ρv • v (t + 1) := by
  rw [monetary_exchangeRate hs hy hp h14 hpH t, hv0, smul_zero, add_zero, eImpact]

/-- Galí (2015), p. 242: the terms of trade revert, so the expected exchange rate
converges to the expected price level: starting from rest (`v_t = 0`),
`E_{t+1} e_{t+1+k} − e_t → −κ_υΛ_v/(1 − ρ_v) · v_{t+1}`. -/
theorem exchangeRate_longRun_change {β sU kU φπ φy ρv : ℝ} (hρ0 : 0 ≤ ρv) (hρ1 : ρv < 1)
    {ygap infl s e pH v : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted pH)
    (hs : ∀ t, s t = sU • ygap t) (hy : ∀ t, ygap t = monYgapCoef β sU kU φπ φy ρv • v t)
    (hp : ∀ t, infl t = monInflCoef β sU kU φπ φy ρv • v t)
    (h14 : ∀ t, s t = e t - pH t) (hpH : ∀ t, pH (t + 1) = pH t + infl (t + 1))
    (hv : 𝔼.IsAR1 ρv v) (t : ℕ) (hv0 : v t = 0) (ω : Ω) :
    Tendsto (fun k => 𝔼.E (t + 1) (e (t + 1 + k)) ω - e t ω) atTop
      (𝓝 (eLongRun β sU kU φπ φy ρv * v (t + 1) ω)) := by
  let cs := -(sU * (1 - β * ρv) * msvLambda β sU kU φπ φy ρv)
  have hee : ∀ n, e n = s n + pH n := fun n => by rw [h14]; abel
  have het : e t ω = pH t ω := by
    rw [hee, monetary_tot hs hy t, hv0]; simp
  have hS : ∀ k, 𝔼.E (t + 1) (s (t + 1 + k)) ω = cs * ρv ^ k * v (t + 1) ω := fun k => by
    rw [monetary_tot hs hy, map_smul, 𝔼.ar1_iterate hv, smul_smul]
    simp only [Pi.smul_apply, smul_eq_mul, cs]
  have hsl : Tendsto (fun k => cs * ρv ^ k * v (t + 1) ω) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul cs).mul_const
      (v (t + 1) ω)
  have hpl := priceLevel_longRun 𝔼 hρ0 hρ1 hpa hpH hp hv t ω
  have hsum := (hsl.add hpl).sub_const (pH t ω)
  rw [zero_add, add_sub_cancel_left] at hsum
  rw [eLongRun]
  refine hsum.congr fun k => ?_
  rw [het, hee, map_add, Pi.add_apply, hS]

/-- Galí (2015), p. 242: the exchange rate **overshoots** (appreciates on impact by
more than in the long run) if and only if `σ_υ(1 − βρ_v)(1 − ρ_v) > κ_υρ_v`. -/
theorem overshoot_iff {β sU kU φπ φy ρv : ℝ} (hL : 0 < msvLambda β sU kU φπ φy ρv)
    (hρ1 : ρv < 1) :
    eImpact β sU kU φπ φy ρv < eLongRun β sU kU φπ φy ρv ↔
      kU * ρv < sU * (1 - β * ρv) * (1 - ρv) := by
  have h1 : 0 < 1 - ρv := by linarith
  unfold eImpact eLongRun
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ h1]
  constructor
  · intro h
    have : 0 < msvLambda β sU kU φπ φy ρv * (sU * (1 - β * ρv) * (1 - ρv) - kU * ρv) := by
      nlinarith
    have := pos_of_mul_pos_right this hL.le
    linarith
  · intro h
    have := mul_pos hL (show 0 < sU * (1 - β * ρv) * (1 - ρv) - kU * ρv by linarith)
    nlinarith

/-- Galí (2015), p. 242: the overshooting condition "corresponds to that for an
increase in the nominal interest rate": overshooting ⇔ `i` rises on impact. -/
theorem overshoot_iff_nominal_rises {β sU kU φπ φy ρv : ℝ}
    (hL : 0 < msvLambda β sU kU φπ φy ρv) (hρ1 : ρv < 1) :
    eImpact β sU kU φπ φy ρv < eLongRun β sU kU φπ φy ρv ↔
      0 < monNomCoef β sU kU φπ φy ρv := by
  rw [overshoot_iff hL hρ1, monNomCoef]
  constructor
  · intro h; exact mul_pos hL (by linarith)
  · intro h; have := pos_of_mul_pos_right h hL.le; linarith

/-! ### `Λ_v` and the degree of openness (p. 241; survey error 3) -/

/-- Galí (2015), p. 241: `Λ_v` as a function of the primitives, with
`σ_υ = σ/(1 + υ(ϖ − 1))` and `κ_υ = λ(σ_υ + (φ + α)/(1 − α))`. -/
noncomputable def lambdaV (β lamC σ η varphi α φπ φy ρv υ : ℝ) : ℝ :=
  msvLambda β (sigmaU σ η υ) (kappaU lamC σ η υ varphi α) φπ φy ρv

/-- Galí (2015), p. 241: `1/Λ_v` is affine in `σ_υ` with slope
`(1 − βρ_v)(1 − ρ_v) + λ(φ_π − ρ_v)`. -/
theorem msvDen_affine (β lamC sU m φπ φy ρv : ℝ) :
    msvDen β sU (lamC * (sU + m)) φπ φy ρv
      = sU * ((1 - β * ρv) * (1 - ρv) + lamC * (φπ - ρv))
        + ((1 - β * ρv) * φy + lamC * m * (φπ - ρv)) := by
  unfold msvDen; ring

/-- **Corrected p. 241 claim** (pairwise): if `ση > 1` and
`(1 − βρ_v)(1 − ρ_v) + λ(φ_π − ρ_v) > 0`, then for `0 ≤ υ₁ < υ₂ ≤ 1` with (41) at
`υ₂`, `Λ_v(υ₁) < Λ_v(υ₂)`: more openness amplifies the monetary shock. -/
theorem lambdaV_lt_of_slope_pos {β lamC σ η varphi α φπ φy ρv υ₁ υ₂ : ℝ} (hlam : 0 < lamC)
    (hσ : 0 < σ) (hη : 0 < η) (hση : 1 < σ * η) (hφ : 0 ≤ varphi) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (hslope : 0 < (1 - β * ρv) * (1 - ρv) + lamC * (φπ - ρv))
    (h1 : υ₁ ∈ Set.Icc (0 : ℝ) 1) (h2 : υ₂ ∈ Set.Icc (0 : ℝ) 1) (h12 : υ₁ < υ₂)
    (h41 : 0 < kappaU lamC σ η υ₂ varphi α * (φπ - 1) + (1 - β) * φy) :
    lambdaV β lamC σ η varphi α φπ φy ρv υ₁ < lambdaV β lamC σ η varphi α φπ φy ρv υ₂ := by
  have hD2 := msvDen_pos (sigmaU_pos hσ hη h2.1 h2.2)
    (kappaU_pos hlam hσ hη h2.1 h2.2 hφ hα0 hα1) hβ0 hβ1 hφy hρ1 h41
  have hs := sigmaU_strictAntiOn hσ hη hση h1 h2 h12
  unfold lambdaV msvLambda
  unfold kappaU at hD2 ⊢
  simp only [msvDen_affine] at hD2 ⊢
  apply one_div_lt_one_div_of_lt hD2
  nlinarith

/-- **Corrected p. 241 claim**: if `ση > 1`, `(1 − βρ_v)(1 − ρ_v) + λ(φ_π − ρ_v) > 0`
(e.g. `φ_π ≥ ρ_v`) and (41) holds on `[0, 1]`, then `Λ_v` is strictly increasing in
the degree of openness `υ ∈ [0, 1]`. -/
theorem lambdaV_strictMonoOn {β lamC σ η varphi α φπ φy ρv : ℝ} (hlam : 0 < lamC)
    (hσ : 0 < σ) (hη : 0 < η) (hση : 1 < σ * η) (hφ : 0 ≤ varphi) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (hslope : 0 < (1 - β * ρv) * (1 - ρv) + lamC * (φπ - ρv))
    (h41 : ∀ υ ∈ Set.Icc (0 : ℝ) 1,
      0 < kappaU lamC σ η υ varphi α * (φπ - 1) + (1 - β) * φy) :
    StrictMonoOn (lambdaV β lamC σ η varphi α φπ φy ρv) (Set.Icc 0 1) :=
  fun _ h1 υ₂ h2 h12 => lambdaV_lt_of_slope_pos hlam hσ hη hση hφ hα0 hα1 hβ0 hβ1 hφy hρ1
    hslope h1 h2 h12 (h41 υ₂ h2)

/-- Galí (2015), p. 241 (survey error 3): if `ση > 1` but
`(1 − βρ_v)(1 − ρ_v) + λ(φ_π − ρ_v) < 0`, then for `0 ≤ υ₁ < υ₂ ≤ 1` with (41) at
`υ₁`, `Λ_v(υ₂) < Λ_v(υ₁)`: openness *dampens* the monetary shock. -/
theorem lambdaV_lt_of_slope_neg {β lamC σ η varphi α φπ φy ρv υ₁ υ₂ : ℝ} (hlam : 0 < lamC)
    (hσ : 0 < σ) (hη : 0 < η) (hση : 1 < σ * η) (hφ : 0 ≤ varphi) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (hslope : (1 - β * ρv) * (1 - ρv) + lamC * (φπ - ρv) < 0)
    (h1 : υ₁ ∈ Set.Icc (0 : ℝ) 1) (h2 : υ₂ ∈ Set.Icc (0 : ℝ) 1) (h12 : υ₁ < υ₂)
    (h41 : 0 < kappaU lamC σ η υ₁ varphi α * (φπ - 1) + (1 - β) * φy) :
    lambdaV β lamC σ η varphi α φπ φy ρv υ₂ < lambdaV β lamC σ η varphi α φπ φy ρv υ₁ := by
  have hD1 := msvDen_pos (sigmaU_pos hσ hη h1.1 h1.2)
    (kappaU_pos hlam hσ hη h1.1 h1.2 hφ hα0 hα1) hβ0 hβ1 hφy hρ1 h41
  have hs := sigmaU_strictAntiOn hσ hη hση h1 h2 h12
  unfold lambdaV msvLambda
  unfold kappaU at hD1 ⊢
  simp only [msvDen_affine] at hD1 ⊢
  apply one_div_lt_one_div_of_lt hD1
  nlinarith

/-- Survey error 3: for `υ ∈ [0, 1]` and `ση = 2`, `σ = 1`, `σ_υ ≤ 1`. -/
theorem counterexample_sigmaU_le (υ : ℝ) (hυ : υ ∈ Set.Icc (0 : ℝ) 1) :
    sigmaU 1 2 υ ≤ 1 := by
  have hD := one_add_mul_varpi_pos (σ := 1) (η := 2) one_pos two_pos hυ.1 hυ.2
  unfold sigmaU Phi
  rw [one_mul, div_le_one hD, varpi_sub_one]
  have : 0 ≤ υ * (2 - υ) := mul_nonneg hυ.1 (by linarith [hυ.2])
  nlinarith

/-- **Counterexample to the p. 241 claim** (survey error 3): with `σ = 1`, `η = 2`
(`ση = 2 > 1`), `β = 0.99`, `λ = 17/300`, `φ = 1`, `α = 1/4`, `φ_π = 0`, `φ_y = 30`
and `ρ_v = 0.99`, condition (41) holds for every `υ ∈ [0, 1]` and yet `Λ_v` is
strictly *decreasing* in openness on `[0, 1]`. -/
theorem counterexample_strictAntiOn :
    (∀ υ ∈ Set.Icc (0 : ℝ) 1,
      0 < kappaU (17 / 300) 1 2 υ 1 (1 / 4) * (0 - 1) + (1 - 99 / 100) * 30) ∧
    StrictAntiOn (lambdaV (99 / 100) (17 / 300) 1 2 1 (1 / 4) 0 30 (99 / 100))
      (Set.Icc 0 1) := by
  have h41 : ∀ υ ∈ Set.Icc (0 : ℝ) 1,
      0 < kappaU (17 / 300) 1 2 υ 1 (1 / 4) * (0 - 1) + (1 - 99 / 100) * 30 := by
    intro υ hυ
    have := counterexample_sigmaU_le υ hυ
    unfold kappaU
    norm_num
    linarith
  refine ⟨h41, fun υ₁ h1 υ₂ h2 h12 => ?_⟩
  exact lambdaV_lt_of_slope_neg (by norm_num) one_pos two_pos (by norm_num) zero_le_one
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h1 h2 h12 (h41 υ₁ h1)

/-- Survey error 3, a concrete strict decrease: in the counterexample economy
`Λ_v(υ = 1/2) < Λ_v(υ = 0)`, with (41) holding at both values. -/
theorem counterexample_values :
    lambdaV (99 / 100) (17 / 300) 1 2 1 (1 / 4) 0 30 (99 / 100) (1 / 2)
      < lambdaV (99 / 100) (17 / 300) 1 2 1 (1 / 4) 0 30 (99 / 100) 0 :=
  counterexample_strictAntiOn.2 ⟨le_refl 0, zero_le_one⟩ ⟨by norm_num, by norm_num⟩
    (by norm_num)

/-- **The printed claim is false** (Galí 2015, p. 241; survey error 3): it is not true
that `ση > 1` (with the standard restrictions on the other parameters and (41))
makes `Λ_v` increasing in the degree of openness. -/
theorem printed_monotonicity_false :
    ¬ ∀ β lamC σ η varphi α φπ φy ρv υ₁ υ₂ : ℝ, 0 < β → β < 1 → 0 < lamC → 0 < σ → 0 < η →
      1 < σ * η → 0 ≤ varphi → 0 ≤ α → α < 1 → 0 ≤ φπ → 0 ≤ φy → 0 ≤ ρv → ρv < 1 →
      0 ≤ υ₁ → υ₁ < υ₂ → υ₂ ≤ 1 →
      0 < kappaU lamC σ η υ₁ varphi α * (φπ - 1) + (1 - β) * φy →
      0 < kappaU lamC σ η υ₂ varphi α * (φπ - 1) + (1 - β) * φy →
      lambdaV β lamC σ η varphi α φπ φy ρv υ₁ ≤ lambdaV β lamC σ η varphi α φπ φy ρv υ₂ := by
  intro h
  have hc := counterexample_values
  have := h (99 / 100) (17 / 300) 1 2 1 (1 / 4) 0 30 (99 / 100) 0 (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) one_pos two_pos (by norm_num) zero_le_one (by norm_num)
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
    (by norm_num) (counterexample_strictAntiOn.1 0 ⟨le_refl 0, zero_le_one⟩)
    (counterexample_strictAntiOn.1 (1 / 2) ⟨by norm_num, by norm_num⟩)
  linarith

/-! ### The case `σ = η = 1` (p. 243) -/

/-- Galí (2015), p. 243 (with `ση = 1`, in particular `σ = η = 1`): the open-economy
equilibrium conditions under rule (39) coincide with the closed-economy ones
(`σ_υ = σ`, `κ_υ = κ = λ(σ + (φ + α)/(1 − α))`), for every degree of openness. -/
theorem closed_economy_equivalence {β lamC σ η υ varphi α ρ φπ φy : ℝ} (h : σ * η = 1)
    (rn yn v ygap infl i : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β (sigmaU σ η υ) (kappaU lamC σ η υ varphi α) ρ φπ φy rn yn v ygap infl i ↔
      Equilibrium 𝔼 β σ (lamC * (σ + (varphi + α) / (1 - α))) ρ φπ φy rn yn v ygap infl i := by
  rw [sigmaU_of_sigma_mul_eta h, kappaU_of_mul_eq_one h]

/-- Galí (2015), p. 243: with `ση = 1` (in particular `σ = η = 1`) the output-gap and
domestic-inflation responses to a monetary shock do not depend on openness and equal
those of the closed economy (`υ = 0`). -/
theorem closed_economy_responses {β lamC σ η υ varphi α φπ φy ρv : ℝ} (h : σ * η = 1) :
    monYgapCoef β (sigmaU σ η υ) (kappaU lamC σ η υ varphi α) φπ φy ρv
        = monYgapCoef β (sigmaU σ η 0) (kappaU lamC σ η 0 varphi α) φπ φy ρv ∧
      monInflCoef β (sigmaU σ η υ) (kappaU lamC σ η υ varphi α) φπ φy ρv
        = monInflCoef β (sigmaU σ η 0) (kappaU lamC σ η 0 varphi α) φπ φy ρv := by
  rw [sigmaU_of_sigma_mul_eta h, sigmaU_of_sigma_mul_eta h, kappaU_of_mul_eq_one h,
    kappaU_of_mul_eq_one h]
  exact ⟨rfl, rfl⟩

/-- Galí (2015), p. 243, the book's case `σ = η = 1`: `σ_υ = 1` and
`κ_υ = λ(1 + (φ + α)/(1 − α))` for every degree of openness. -/
theorem sigma_eta_one (lamC υ varphi α : ℝ) :
    sigmaU 1 1 υ = 1 ∧ kappaU lamC 1 1 υ varphi α = lamC * (1 + (varphi + α) / (1 - α)) :=
  ⟨sigmaU_of_sigma_mul_eta (by norm_num) υ, kappaU_of_mul_eq_one (by norm_num) υ⟩

end Gali.OpenEconomy.TaylorRule
