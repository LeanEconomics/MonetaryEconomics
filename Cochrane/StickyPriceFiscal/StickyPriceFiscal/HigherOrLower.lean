/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.LongTermDebt

/-!
# Higher or lower inflation?

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.3, pp. 130–133.

§5.3 is a verbal list of "it depends" clauses. The precise ones are formalised here,
mostly as corollaries of the closed forms of §§5.1–5.2.

## Main results

* The Fisher identity (p. 131): `realRate`, `fisher_identity`, `lower_expected_inflation_iff`
  (a rate rise lowers expected inflation iff the real rate rises more than one for one).
* Interest costs (pp. 131–132): `interest_cost_change`, `interest_cost_100`, `interest_cost_10`,
  `interest_cost_mono`.
* The Fisherian long run (p. 132): `fisherian_steady_state` (constant equilibria have
  `i = π`), `fisherian_long_run` (after a permanent rise inflation converges to the new rate,
  with one-period or long-term debt).
* Preconditions for a disinflationary rate rise (p. 131): `needs_long_debt` (with one-period
  debt there is no impact disinflation), `anticipated_rise_no_disinflation` (an anticipated
  rise, already in bond prices, gives the one-period-debt path), `stickier_less_disinflation`
  (if a rise is disinflationary at some κ it is so at every larger κ: stickier prices make a
  rise "more likely" to raise inflation).
* Joint monetary–fiscal contraction (p. 132): `joint_contraction` (a permanent rise with a
  contemporaneous surplus increase of present value `S` gives `π₁ = 1 − (1 − ρ/λ₁)(1 + S)`),
  `joint_contraction_disinflation_iff`, `joint_contraction_strictAnti`.
-/

namespace Cochrane.StickyPriceFiscal.HigherOrLower

open Filter Topology NKModel FiscalNK LongTermDebt

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The Fisher identity -/

/-- Cochrane (2023), p. 131: the ex-ante real rate `r_t = i_t − E_t π_{t+1}`. -/
def realRate (i π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := i t - 𝔼.E t (π (t + 1))

/-- Cochrane (2023), p. 131: `i_t = r_t + E_t π_{t+1}`. -/
theorem fisher_identity (i π : ℕ → Ω → ℝ) (t : ℕ) :
    i t = realRate 𝔼 i π t + 𝔼.E t (π (t + 1)) := by
  unfold realRate; abel

/-- Cochrane (2023), p. 131: comparing two rate settings `i < i'` (with real rates `r = i − Eπ`,
`r' = i' − Eπ'`), expected inflation falls, `Eπ' < Eπ`, iff the real rate rises by more than
the nominal rate, `r' − r > i' − i`. -/
theorem lower_expected_inflation_iff (i i' Eπ Eπ' : ℝ) :
    Eπ' < Eπ ↔ (i' - Eπ') - (i - Eπ) > i' - i := by
  constructor <;> intro h <;> linarith

/-! ### Interest costs -/

/-- Cochrane (2023), pp. 131–132: with debt `b` (as a fraction of GDP), a rise `Δr` in the real
rate changes real interest costs by `b Δr` (fraction of GDP). -/
theorem interest_cost_change (b r Δr : ℝ) : b * (r + Δr) - b * r = b * Δr := by ring

/-- Cochrane (2023), p. 131: "At 100% debt-to-GDP ratio, each one percentage point rise in real
interest rates adds 1% of GDP to interest costs." -/
theorem interest_cost_100 : (1 : ℝ) * (1 / 100) = 1 / 100 := by norm_num

/-- Cochrane (2023), p. 131: "At 10% of GDP, the same rate rise only adds 0.1% of GDP." -/
theorem interest_cost_10 : (1 / 10 : ℝ) * (1 / 100) = 1 / 1000 := by norm_num

/-- Cochrane (2023), pp. 131–132: the interest-cost effect of a real-rate rise `Δr > 0` is
strictly larger for more indebted countries. -/
theorem interest_cost_mono {b b' Δr : ℝ} (hb : b < b') (hr : 0 < Δr) : b * Δr < b' * Δr :=
  mul_lt_mul_of_pos_right hb hr

/-! ### The Fisherian long run -/

/-- Cochrane (2023), p. 132 ("All models have a Fisherian steady state, i = r + π"): in the
model, constant equilibria have `i = π`. -/
theorem fisherian_steady_state [Nonempty Ω] {σ β κ ib xb πb : ℝ} (hσ : σ ≠ 0)
    (h : NK 𝔼 σ β κ (fun _ _ => ib) (fun _ _ => xb) (fun _ _ => πb)) : ib = πb :=
  ((nk_const_iff 𝔼 hσ).mp h).1

/-- Cochrane (2023), pp. 128 and 132 (stability of the peg: "inflation will converge to that
higher rate"): after an unexpected permanent rise, inflation converges to the new rate with
one-period debt and with long-term debt. -/
theorem fisherian_long_run {σ β κ ρ om : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    Tendsto (fun t : ℕ => 1 - (1 - ρ * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ t) atTop (𝓝 1) ∧
    Tendsto (fun t : ℕ => 1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - om) * (lam1 σ β κ)⁻¹ ^ t) atTop
      (𝓝 1) :=
  ⟨perm_rise_tendsto_one hσ hκ hβ, ltd_tendsto_one hσ hκ hβ⟩

/-! ### Preconditions for a disinflationary rate rise (p. 131) -/

/-- Cochrane (2023), p. 131 ("there must be long-term debt outstanding"): with one-period debt
(`ω̃ = 0`) a permanent rise never lowers inflation on impact; any impact disinflation requires
`ω̃ > ρ/λ₁ > 0`. -/
theorem needs_long_debt {σ β κ ρ om : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hom1 : om < 1) :
    ¬ (1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - 0) < 0) ∧
      (1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - om) < 0 → 0 < om) := by
  have hq := (perm_rise_pi0_pos hσ hκ hβ hρ0).2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [ltd_disinflation_iff (by norm_num)] at h
    linarith
  · rw [ltd_disinflation_iff hom1] at h
    linarith

/-- Cochrane (2023), p. 131 ("If the rate rise is expected, bond prices will have already declined
and the deflationary effect will have passed"): if a permanent rise to `i ≡ 1` was anticipated
before date 0, so that the pre-sample bond price already reflects it
(`q_{−1} = ω̃ q_0 − i_{−1}` with `i_{−1} = 0`, i.e. `q_{−1} = −ω̃/(1 − ω̃)`), then every bounded
long-term-debt equilibrium has the one-period-debt path `π_{1+j} = 1 − (1 − ρ/λ₁)λ₁^{−j}`, with
positive impact inflation `ρ/λ₁`. -/
theorem anticipated_rise_no_disinflation {σ β κ ρ om : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1)
    {x π v q rn : ℕ → Ω → ℝ}
    (h : LTD 𝔼 σ β κ ρ om (fun _ _ => 1) (fun _ _ => 0) 0 (fun _ => -om / (1 - om)) x π v q rn)
    (hqa : 𝔼.Adapted q) (hπb : BoundedProc π) (hvb : BoundedProc v) (hqb : BoundedProc q)
    (t : ℕ) (ω : Ω) :
    π t ω = 1 - (1 - ρ * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ t ∧ 0 < π 0 ω := by
  have hom : 1 - om ≠ 0 := by linarith
  have hqc := perm_bond_price 𝔼 hom0 hom1 hqa hqb h.2.2.2.1 h.2.2.2.2.1
  have hsadj : sAdj (fun _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ)) rn = fun _ _ => 0 := by
    funext t ω'
    cases t with
    | zero =>
      simp only [sAdj, Pi.sub_apply]
      rw [h.2.2.2.2.2, hqc]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    | succ t =>
      simp only [sAdj, Pi.add_apply, Pi.sub_apply]
      rw [h.2.2.2.2.1 t, hqc]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  have hft := ltd_to_ftplnk 𝔼 h
  rw [hsadj] at hft
  have key := ((perm_rise 𝔼 hσ hκ hβ hρ0 hρ1).2 x π v (by exact hft) hπb hvb)
  refine ⟨(key t ω).1, ?_⟩
  rw [(key 0 ω).1, (perm_rise_pi0_pos hσ hκ hβ hρ0).1]
  exact (perm_rise_pi0_pos hσ hκ hβ hρ0).2

/-- Cochrane (2023), pp. 129 and 132 ("The stickier prices, then, the more likely it is that
higher interest rates raise inflation"): if a permanent rise is disinflationary on impact at
`κ₁`, it is disinflationary at every `κ₂ > κ₁`. -/
theorem stickier_less_disinflation {σ β ρ om κ₁ κ₂ : ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hom1 : om < 1) (hκ₁ : 0 < κ₁) (hlt : κ₁ < κ₂)
    (h : 1 - (1 - ρ * (lam1 σ β κ₁)⁻¹) / (1 - om) < 0) :
    1 - (1 - ρ * (lam1 σ β κ₂)⁻¹) / (1 - om) < 0 :=
  (ltd_pi0_strictAnti_kappa hσ hβ hρ0 hom1 hκ₁ (hκ₁.trans hlt) hlt).trans h

/-! ### Joint monetary–fiscal contraction (p. 132) -/

/-- Cochrane (2023), p. 132 ("If the fiscal authorities cooperate with a joint monetary-fiscal
contraction, then the inflation decline can be larger"): with one-period debt, a permanent rise
`i ≡ 1` accompanied by deterministic surpluses of present value `S` gives, in every bounded
equilibrium, `π_{1+j} = 1 − (1 − ρ/λ₁)(1 + S)λ₁^{−j}`. -/
theorem joint_contraction {σ β κ ρ Ms : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {s : ℕ → ℝ} (hsb : ∀ j, |s j| ≤ Ms) {x π v : ℕ → Ω → ℝ}
    (h : FTPLNK 𝔼 σ β κ ρ (fun _ _ => 1) (fun t _ => s t) (fun _ => 0) x π v)
    (hπb : BoundedProc π) (hvb : BoundedProc v) (t : ℕ) (ω : Ω) :
    π t ω = 1 - (1 - ρ * (lam1 σ β κ)⁻¹) * (1 + pvS ρ s) * (lam1 σ β κ)⁻¹ ^ t := by
  obtain ⟨_, hπ, _⟩ := det_unique 𝔼 hσ hκ hβ hρ0 hρ1 1 0 hsb h hπb hvb
  rw [hπ]
  simp only [piDet]
  ring

/-- Cochrane (2023), p. 131 ("With … a contemporaneous fiscal shock, a higher nominal rate can
lower unexpected inflation"): the joint contraction is disinflationary on impact iff
`S > (ρ/λ₁)/(1 − ρ/λ₁)`. -/
theorem joint_contraction_disinflation_iff {ρq S : ℝ} (h1 : ρq < 1) :
    1 - (1 - ρq) * (1 + S) * 1 < 0 ↔ ρq / (1 - ρq) < S := by
  have h : 0 < 1 - ρq := by linarith
  rw [div_lt_iff₀ h, mul_one]
  constructor <;> intro hh <;> nlinarith

/-- Cochrane (2023), p. 132: the impact response of the joint contraction is strictly decreasing
in the fiscal contraction `S`. -/
theorem joint_contraction_strictAnti {ρq : ℝ} (h1 : ρq < 1) :
    StrictAnti (fun S : ℝ => 1 - (1 - ρq) * (1 + S)) := by
  intro S₁ S₂ hlt
  have h : 0 < 1 - ρq := by linarith
  simp only
  nlinarith

end Cochrane.StickyPriceFiscal.HigherOrLower
