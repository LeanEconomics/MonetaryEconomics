/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.Calibration

/-!
# The short-period limit

Woodford (2003), *Interest and Prices*, Chapter 2, §3.4, pp. 120–123 ((3.24)–(3.26),
Propositions 2.14–2.15), and Appendix A, §§A.14–A.15, pp. 646–648.

The period length is `Δ > 0`; we study the limit `Δ → 0⁺` (the filter `𝓝[>] 0`). The calendar-time
parameters are fixed: the semielasticity `η̃_i = η_i Δ` (so `η_i = η̃_i/Δ`), the rate of time
preference `δ = −log β/Δ` (so `β = e^{−δΔ}`) and, for Prop. 2.15, the adjustment rate
`ψ = −log ρ/Δ` (so `ρ = e^{−ψΔ}`) and the long-run response `Φ_π = φ_π/(1 − ρ)`.

* **(3.24)**, p. 121: `chi_limit` — if `χ(Δ)` is calibrated as in (3.23) at each period length,
  `χ(Δ) = s_m(β(Δ)η_y/((1 − β(Δ))η_i(Δ)) − σ⁻¹)`, then `χ(Δ) → χ̄ = s_m(η_y/(δη̃_i) − σ⁻¹)`.
  (The book obtains (3.24) by "the same reasoning"; we prove the limit from the calibration
  identity, and Props. 2.14–2.15 below only assume `χ(Δ) → χ̄`.)
* **Proposition 2.14** (A.14): `prop_2_14` — for the contemporaneous rule (`ρ = 0`), `φ_π > 0`,
  `φ_π ≠ 1`, `χ̄ ≠ 0`: for all small `Δ`, equilibrium is determinate iff
  (`φ_π > 1` and `χ̄ > 0`) or (`φ_π < 1` and `χ̄ < 0`); `prop_2_14_eventually` and
  `prop_2_14_eventually_not` restate "for all small enough `Δ` … but not otherwise";
  `tendsto_delta_gamma` is (A.34) (`Δγ₀, Δγ₁ → η̃_iχ̄φ_π`); `fn55` — for `χ̄ < 0`, (3.16) fails
  for all small `Δ`.
* **Proposition 2.15** (A.15): `prop_2_15` — with `Φ_π, ψ > 0` and (3.25), for all small `Δ`
  equilibrium is determinate iff `Φ_π > 1`; `rate_A36` — the unique bounded interest rate has the
  form (3.26)/(A.36) with coefficients `LambdaC`, `GammaC`, `GammaT` and decay factor
  `γ = γ₁/γ₀`; `prop_2_15_limits` — `Λ → 1/(1 + η̃_iχ̄Φ_πψ)` (**E3 corrected**),
  `Γ = Φ_π/(Φ_π − 1)`, `Γ̃ → Γ(1 + η̃_iχ̄ψ)/(1 + η̃_iχ̄Φ_πψ)`, and `ξ = −log γ/Δ →
  (Φ_π − 1)ψ/(1 + η̃_iχ̄Φ_πψ)`; `limits_continuousOn` and `limits_pos` — the limits are
  continuous in `χ̄` on the region (3.25) and positive.
* **E3** (p. 648): `LambdaC_sub` (`Λ − Γ̃(1 − γ) = ρ/γ₀`, the correct identity), `LambdaC_eq`
  (`Λ = 1/γ₁`), `book_identity_false` (the printed `Λ + Γ(1 − γ) − 1 = (1 + η_iχ)φ_π/γ₀` fails),
  `book_Lambda_limit_wrong` (the printed limit `1 + η̃χ̄Φψ/(1 + η̃χ̄Φψ)` is wrong for every
  `χ̄ ≠ 0`) and `E3_numbers` (`0.9137` against the book's `1.0863`).
-/

namespace Woodford.PriceLevelDetermination.ShortPeriod

open Filter Topology
open Woodford.PriceLevelDetermination.MoneyGrowth Woodford.PriceLevelDetermination.NonSeparable
open Woodford.PriceLevelDetermination.ForwardSolution (scalarSol scalarSol_apply)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Elementary limits -/

/-- Woodford (2003), pp. 121–122: `(1 − e^{−aΔ})/Δ → a` as `Δ → 0⁺` (so `(1 − β)/Δ → δ` and
`(1 − ρ)/Δ → ψ`). -/
theorem tendsto_one_sub_exp_div (a : ℝ) :
    Tendsto (fun Δ : ℝ => (1 - Real.exp (-(a * Δ))) / Δ) (𝓝[>] 0) (𝓝 a) := by
  have hd : HasDerivAt (fun x : ℝ => Real.exp (-(a * x))) (-a) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul a).neg.exp
    simpa using this
  have h := hd.tendsto_slope_zero_right.neg
  rw [neg_neg] at h
  refine h.congr' (Eventually.of_forall fun Δ => ?_)
  simp only [smul_eq_mul, zero_add, mul_zero, neg_zero, Real.exp_zero]
  rw [div_eq_inv_mul]
  ring

/-- Woodford (2003), pp. 121–122: `e^{−aΔ} → 1` as `Δ → 0⁺`. -/
theorem tendsto_exp_neg (a : ℝ) :
    Tendsto (fun Δ : ℝ => Real.exp (-(a * Δ))) (𝓝[>] 0) (𝓝 1) := by
  have : Tendsto (fun Δ : ℝ => Real.exp (-(a * Δ))) (𝓝 0) (𝓝 (Real.exp (-(a * 0)))) :=
    ((continuous_const.mul continuous_id).neg.rexp).tendsto 0
  rw [mul_zero, neg_zero, Real.exp_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- Woodford (2003), pp. 121–122: `e^{−aΔ} < 1` for `a, Δ > 0`. -/
theorem exp_neg_lt_one {a Δ : ℝ} (ha : 0 < a) (hΔ : 0 < Δ) : Real.exp (-(a * Δ)) < 1 := by
  have h : -(a * Δ) < 0 := by have := mul_pos ha hΔ; linarith
  have := Real.exp_lt_exp.mpr h
  rwa [Real.exp_zero] at this

/-! ### (3.24): the limiting value of `χ` -/

/-- Woodford (2003), **(3.24)**, p. 121: if at each period length `Δ > 0` the elasticity `χ(Δ)`
satisfies the calibration identity behind (3.23),
`χ(Δ) = s_m(β η_y/((1 − β)η_i) − σ⁻¹)` with `β = e^{−δΔ}` and `η_i = η̃_i/Δ` (`δ, η̃_i > 0`), then
`χ(Δ) → χ̄ = s_m(η_y/(δη̃_i) − σ⁻¹)` as `Δ → 0⁺`. -/
theorem chi_limit {sm σinv ηy δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) {χ : ℝ → ℝ}
    (hχ : ∀ Δ, 0 < Δ → χ Δ = sm * (Real.exp (-(δ * Δ)) * ηy /
      ((1 - Real.exp (-(δ * Δ))) * (η / Δ)) - σinv)) :
    Tendsto χ (𝓝[>] 0) (𝓝 (sm * (ηy / (δ * η) - σinv))) := by
  have h1 := tendsto_exp_neg δ
  have h2 := tendsto_one_sub_exp_div δ
  have h3 : Tendsto (fun Δ => Real.exp (-(δ * Δ)) * ηy / ((1 - Real.exp (-(δ * Δ))) / Δ * η))
      (𝓝[>] 0) (𝓝 (1 * ηy / (δ * η))) :=
    (h1.mul_const ηy).div (h2.mul_const η) (by positivity)
  rw [one_mul] at h3
  have h4 := (h3.sub_const σinv).const_mul sm
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Δ hΔ
  rw [hχ Δ hΔ]
  congr 3
  have : Δ ≠ 0 := ne_of_gt hΔ
  field_simp

/-! ### Proposition 2.14: a contemporaneous Taylor rule -/

/-- Woodford (2003), **(A.34)**, p. 647: with `η_i = η̃_i/Δ` and `χ(Δ) → χ̄`,
`Δγ₀ → η̃_iχ̄φ_π` and `Δγ₁ → η̃_iχ̄φ_π` (for `ρ = 0`; both `γ`'s themselves diverge). -/
theorem tendsto_delta_gamma {η φπ χbar : ℝ} {χ : ℝ → ℝ}
    (hlim : Tendsto χ (𝓝[>] 0) (𝓝 χbar)) :
    Tendsto (fun Δ => Δ * gamma0 (η / Δ) (χ Δ) φπ 0) (𝓝[>] 0) (𝓝 (η * χbar * φπ)) ∧
      Tendsto (fun Δ => Δ * gamma1 (η / Δ) (χ Δ) φπ) (𝓝[>] 0) (𝓝 (η * χbar * φπ)) := by
  have hid : Tendsto (fun Δ : ℝ => Δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun Δ => Δ * φπ + η * χ Δ * φπ) (𝓝[>] 0) (𝓝 (0 * φπ + η * χbar * φπ)) :=
    (hid.mul_const φπ).add ((hlim.const_mul η).mul_const φπ)
  have hB : Tendsto (fun Δ => Δ + η * χ Δ * φπ) (𝓝[>] 0) (𝓝 (0 + η * χbar * φπ)) :=
    hid.add ((hlim.const_mul η).mul_const φπ)
  rw [zero_mul, zero_add] at hA
  rw [zero_add] at hB
  constructor
  · refine hA.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with Δ hΔ
    have : Δ ≠ 0 := ne_of_gt hΔ
    unfold gamma0
    field_simp
    ring
  · refine hB.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with Δ hΔ
    have : Δ ≠ 0 := ne_of_gt hΔ
    unfold gamma1
    field_simp

/-- Woodford (2003), **Proposition 2.14**, p. 121 and A.14, pp. 646–647: for the contemporaneous
Taylor rule (2.4) (`ρ = 0`), zero interest on money, a fixed `φ_π > 0`, `φ_π ≠ 1`, `η_i = η̃_i/Δ`
(`η̃_i > 0`) and `χ(Δ) → χ̄ ≠ 0`, for all small enough `Δ` equilibrium is determinate iff
(`φ_π > 1` and `χ̄ > 0`) or (`0 < φ_π < 1` and `χ̄ < 0`). -/
theorem prop_2_14 [Nonempty Ω] {η φπ χbar : ℝ} {χ : ℝ → ℝ} (hη : 0 < η) (hφ : 0 < φπ)
    (hχbar : χbar ≠ 0) (hlim : Tendsto χ (𝓝[>] 0) (𝓝 χbar)) :
    ∀ᶠ Δ in 𝓝[>] 0, (Det213 𝔼 (η / Δ) (χ Δ) φπ 0 ↔
      ((1 < φπ ∧ 0 < χbar) ∨ (φπ < 1 ∧ χbar < 0))) := by
  obtain ⟨h0, h1⟩ := tendsto_delta_gamma (η := η) (φπ := φπ) hlim
  have hsub : ∀ Δ, gamma0 (η / Δ) (χ Δ) φπ 0 - gamma1 (η / Δ) (χ Δ) φπ = φπ - 1 := fun Δ => by
    rw [gamma_sub]; ring
  rcases lt_or_gt_of_ne hχbar with hneg | hpos
  · have hL : η * χbar * φπ < 0 := by
      have := mul_neg_of_pos_of_neg hη hneg
      exact mul_neg_of_neg_of_pos this hφ
    filter_upwards [h0.eventually (gt_mem_nhds hL), h1.eventually (gt_mem_nhds hL),
      self_mem_nhdsWithin] with Δ e0 e1 hΔ
    have g0 : gamma0 (η / Δ) (χ Δ) φπ 0 < 0 := by
      by_contra h; push Not at h
      have := mul_nonneg (le_of_lt (Set.mem_Ioi.mp hΔ)) h; linarith
    have g1 : gamma1 (η / Δ) (χ Δ) φπ < 0 := by
      by_contra h; push Not at h
      have := mul_nonneg (le_of_lt (Set.mem_Ioi.mp hΔ)) h; linarith
    rw [det213_iff 𝔼 hφ.ne', abs_of_neg g0, abs_of_neg g1]
    have := hsub Δ
    constructor
    · intro h; right; exact ⟨by linarith, hneg⟩
    · rintro (h | h)
      · exact absurd h.2 (by linarith)
      · linarith [h.1]
  · have hL : 0 < η * χbar * φπ := by positivity
    filter_upwards [h0.eventually (lt_mem_nhds hL), h1.eventually (lt_mem_nhds hL),
      self_mem_nhdsWithin] with Δ e0 e1 hΔ
    have g0 : 0 < gamma0 (η / Δ) (χ Δ) φπ 0 := by
      by_contra h; push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Set.mem_Ioi.mp hΔ)) h; linarith
    have g1 : 0 < gamma1 (η / Δ) (χ Δ) φπ := by
      by_contra h; push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Set.mem_Ioi.mp hΔ)) h; linarith
    rw [det213_iff 𝔼 hφ.ne', abs_of_pos g0, abs_of_pos g1]
    have := hsub Δ
    constructor
    · intro h; left; exact ⟨by linarith, hpos⟩
    · rintro (h | h)
      · linarith [h.1]
      · exact absurd h.2 (by linarith)

/-- Woodford (2003), Proposition 2.14, p. 121 ("determinate for all small enough values of Δ if
… but not otherwise"): determinacy holds for all small `Δ` iff the sign condition holds. -/
theorem prop_2_14_eventually [Nonempty Ω] {η φπ χbar : ℝ} {χ : ℝ → ℝ} (hη : 0 < η)
    (hφ : 0 < φπ) (hχbar : χbar ≠ 0) (hlim : Tendsto χ (𝓝[>] 0) (𝓝 χbar)) :
    (∀ᶠ Δ in 𝓝[>] 0, Det213 𝔼 (η / Δ) (χ Δ) φπ 0) ↔
      ((1 < φπ ∧ 0 < χbar) ∨ (φπ < 1 ∧ χbar < 0)) := by
  have h := prop_2_14 𝔼 hη hφ hχbar hlim
  constructor
  · intro hd
    obtain ⟨Δ, h1, h2⟩ := (hd.and h).exists
    exact h2.mp h1
  · intro hc
    filter_upwards [h] with Δ hΔ
    exact hΔ.mpr hc

/-- Woodford (2003), Proposition 2.14, p. 121 ("but not otherwise"): when the sign condition fails,
equilibrium is indeterminate for all small enough `Δ`. -/
theorem prop_2_14_eventually_not [Nonempty Ω] {η φπ χbar : ℝ} {χ : ℝ → ℝ} (hη : 0 < η)
    (hφ : 0 < φπ) (hχbar : χbar ≠ 0) (hlim : Tendsto χ (𝓝[>] 0) (𝓝 χbar))
    (hc : ¬ ((1 < φπ ∧ 0 < χbar) ∨ (φπ < 1 ∧ χbar < 0))) :
    ∀ᶠ Δ in 𝓝[>] 0, ¬ Det213 𝔼 (η / Δ) (χ Δ) φπ 0 := by
  filter_upwards [prop_2_14 𝔼 hη hφ hχbar hlim] with Δ hΔ
  rw [hΔ]
  exact hc

/-- Woodford (2003), fn 55, p. 121: when `χ̄ < 0`, the bound (3.16) `χ > −1/(2η_i)` fails for all
small enough `Δ` (since `η_i = η̃_i/Δ → ∞`), so Prop. 2.13 does not apply and there is no
contradiction with Prop. 2.14. -/
theorem fn55 {η χbar : ℝ} {χ : ℝ → ℝ} (hη : 0 < η) (hneg : χbar < 0)
    (hlim : Tendsto χ (𝓝[>] 0) (𝓝 χbar)) :
    ∀ᶠ Δ in 𝓝[>] 0, ¬ (-1 / (2 * (η / Δ)) < χ Δ) := by
  have hb : Tendsto (fun Δ : ℝ => -Δ / (2 * η)) (𝓝[>] 0) (𝓝 (-0 / (2 * η))) :=
    ((tendsto_id.mono_left nhdsWithin_le_nhds).neg).div_const _
  rw [neg_zero, zero_div] at hb
  have hc : χbar / 2 < 0 := by linarith
  filter_upwards [hlim.eventually (gt_mem_nhds (show χbar < χbar / 2 by linarith)),
    hb.eventually (lt_mem_nhds hc), self_mem_nhdsWithin] with Δ e1 e2 hΔ
  have hΔ' : Δ ≠ 0 := ne_of_gt hΔ
  have : -1 / (2 * (η / Δ)) = -Δ / (2 * η) := by field_simp
  rw [this]
  intro h
  exact lt_irrefl _ ((e2.trans h).trans e1)

/-! ### Proposition 2.15: an inertial rule with fixed calendar-time coefficients -/

/-- Woodford (2003), p. 122: `ρ = e^{−ψΔ}`. -/
noncomputable def rhoD (ψ Δ : ℝ) : ℝ := Real.exp (-(ψ * Δ))

/-- Woodford (2003), p. 122: `ρ = e^{−ψΔ} < 1` for `ψ, Δ > 0`. -/
theorem rhoD_lt_one {ψ Δ : ℝ} (hψ : 0 < ψ) (hΔ : 0 < Δ) : rhoD ψ Δ < 1 :=
  exp_neg_lt_one hψ hΔ

/-- Woodford (2003), p. 122: `φ_π = Φ_π(1 − ρ)`. -/
noncomputable def phiD (Φ ψ Δ : ℝ) : ℝ := Φ * (1 - rhoD ψ Δ)

/-- Woodford (2003), A.15, p. 648: the limit `1 + η̃_iχ̄Φ_πψ` of `γ₀` and `γ₁`. -/
def Glim (η χbar Φ ψ : ℝ) : ℝ := 1 + η * χbar * Φ * ψ

/-- Woodford (2003), (3.25)/(A.35), p. 122: for `η̃_i, Φ_π, ψ > 0`, the condition
`χ̄ > −1/(ψΦ_πη̃_i)` is exactly `1 + η̃_iχ̄Φ_πψ > 0`. -/
theorem cond325_iff {η χbar Φ ψ : ℝ} (hη : 0 < η) (hΦ : 0 < Φ) (hψ : 0 < ψ) :
    -1 / (ψ * Φ * η) < χbar ↔ 0 < Glim η χbar Φ ψ := by
  unfold Glim
  rw [div_lt_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), A.15, p. 648: `η_iχφ_π = η̃_i χ(Δ) Φ_π (1 − ρ)/Δ → η̃_iχ̄Φ_πψ`. -/
theorem tendsto_eta_chi_phi {η Φ ψ χbar : ℝ} {χ : ℝ → ℝ} (hlim : Tendsto χ (𝓝[>] 0) (𝓝 χbar)) :
    Tendsto (fun Δ => η / Δ * χ Δ * phiD Φ ψ Δ) (𝓝[>] 0) (𝓝 (η * χbar * Φ * ψ)) := by
  have h := ((hlim.const_mul η).mul_const Φ).mul (tendsto_one_sub_exp_div ψ)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Δ hΔ
  have : Δ ≠ 0 := ne_of_gt hΔ
  unfold phiD rhoD
  field_simp

/-- Woodford (2003), A.15, p. 648: `γ₀ → 1 + η̃_iχ̄Φ_πψ` and `γ₁ → 1 + η̃_iχ̄Φ_πψ`. -/
theorem tendsto_gammas {η Φ ψ χbar : ℝ} {χ : ℝ → ℝ} (hlim : Tendsto χ (𝓝[>] 0) (𝓝 χbar)) :
    Tendsto (fun Δ => gamma0 (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ)) (𝓝[>] 0)
        (𝓝 (Glim η χbar Φ ψ)) ∧
      Tendsto (fun Δ => gamma1 (η / Δ) (χ Δ) (phiD Φ ψ Δ)) (𝓝[>] 0) (𝓝 (Glim η χbar Φ ψ)) := by
  have hk := tendsto_eta_chi_phi (η := η) (Φ := Φ) (ψ := ψ) hlim
  have hρ := tendsto_exp_neg ψ
  have hφ : Tendsto (fun Δ => phiD Φ ψ Δ) (𝓝[>] 0) (𝓝 (Φ * (1 - 1))) :=
    (hρ.const_sub 1).const_mul Φ
  rw [sub_self, mul_zero] at hφ
  constructor
  · have := (hφ.add hk).add hρ
    rw [zero_add, add_comm] at this
    refine this.congr' (Eventually.of_forall fun Δ => ?_)
    simp only [gamma0, rhoD]
    ring
  · have := hk.const_add 1
    refine this.congr' (Eventually.of_forall fun Δ => ?_)
    simp only [gamma1]

/-- Woodford (2003), A.15, p. 648: `γ₀ − γ₁ = (Φ_π − 1)(1 − ρ)`. -/
theorem gamma_sub_D (η χ Φ ψ Δ : ℝ) :
    gamma0 (η / Δ) χ (phiD Φ ψ Δ) (rhoD ψ Δ) - gamma1 (η / Δ) χ (phiD Φ ψ Δ) =
      (Φ - 1) * (1 - rhoD ψ Δ) := by
  rw [gamma_sub]; unfold phiD; ring

/-- Woodford (2003), **Proposition 2.15**, p. 122 and A.15, pp. 647–648: with `η̃_i, Φ_π, ψ > 0`,
`ρ = e^{−ψΔ}`, `φ_π = Φ_π(1 − ρ)`, `η_i = η̃_i/Δ`, `χ(Δ) → χ̄` and (3.25)
(`1 + η̃_iχ̄Φ_πψ > 0`), for all small enough `Δ` equilibrium is determinate iff `Φ_π > 1`. -/
theorem prop_2_15 [Nonempty Ω] {η Φ ψ χbar : ℝ} {χ : ℝ → ℝ} (hΦ : 0 < Φ) (hψ : 0 < ψ)
    (h325 : 0 < Glim η χbar Φ ψ) (hlim : Tendsto χ (𝓝[>] 0) (𝓝 χbar)) :
    ∀ᶠ Δ in 𝓝[>] 0,
      (Det213 𝔼 (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ) ↔ 1 < Φ) := by
  obtain ⟨h0, h1⟩ := tendsto_gammas (η := η) (Φ := Φ) (ψ := ψ) hlim
  filter_upwards [h0.eventually (lt_mem_nhds h325), h1.eventually (lt_mem_nhds h325),
    self_mem_nhdsWithin] with Δ g0 g1 hΔ
  have hρ1 : rhoD ψ Δ < 1 := exp_neg_lt_one hψ hΔ
  have hφ : phiD Φ ψ Δ ≠ 0 := by
    unfold phiD
    have : 0 < 1 - rhoD ψ Δ := by linarith
    positivity
  rw [det213_iff 𝔼 hφ, abs_of_pos g0, abs_of_pos g1]
  have hs := gamma_sub_D η (χ Δ) Φ ψ Δ
  have hpos : 0 < 1 - rhoD ψ Δ := by linarith
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : (Φ - 1) * (1 - rhoD ψ Δ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
    linarith
  · intro h
    have : 0 < (Φ - 1) * (1 - rhoD ψ Δ) := mul_pos (by linarith) hpos
    linarith

/-- Woodford (2003), (A.36), p. 647: the decay factor `γ = γ₁/γ₀`. -/
noncomputable def gammaR (ηi χ φπ ρ : ℝ) : ℝ := gamma1 ηi χ φπ / gamma0 ηi χ φπ ρ

/-- Woodford (2003), (3.22), p. 117: `κ = 1 + (1 − ρ)η_iχ`. -/
def kappa (ηi χ ρ : ℝ) : ℝ := 1 + (1 - ρ) * ηi * χ

/-- Woodford (2003), (A.36), p. 648: `Γ = φ_π/(γ₀ − γ₁)`. -/
noncomputable def GammaC (ηi χ φπ ρ : ℝ) : ℝ :=
  φπ / (gamma0 ηi χ φπ ρ - gamma1 ηi χ φπ)

/-- Woodford (2003), (A.36), p. 648: `Γ̃ = Γ κ/(1 + η_iχφ_π)`. -/
noncomputable def GammaT (ηi χ φπ ρ : ℝ) : ℝ :=
  GammaC ηi χ φπ ρ * kappa ηi χ ρ / gamma1 ηi χ φπ

/-- Woodford (2003), (A.36), p. 648: `Λ`, identified from the coefficient `ρ/γ₀` of `ī_t` in the
solution: `Λ = ρ/γ₀ + Γ̃(1 − γ)`. -/
noncomputable def LambdaC (ηi χ φπ ρ : ℝ) : ℝ :=
  ρ / gamma0 ηi χ φπ ρ + GammaT ηi χ φπ ρ * (1 - gammaR ηi χ φπ ρ)

/-- Woodford (2003), A.15, p. 648 (**E3**, the correct identity): `Λ − Γ̃(1 − γ) = ρ/γ₀`. -/
theorem LambdaC_sub (ηi χ φπ ρ : ℝ) :
    LambdaC ηi χ φπ ρ - GammaT ηi χ φπ ρ * (1 - gammaR ηi χ φπ ρ) = ρ / gamma0 ηi χ φπ ρ := by
  unfold LambdaC; ring

/-- Woodford (2003), A.15: in fact `Λ = 1/γ₁ = 1/(1 + η_iχφ_π)` (when `γ₀, γ₁ ≠ 0`, `γ₀ ≠ γ₁`). -/
theorem LambdaC_eq {ηi χ φπ ρ : ℝ} (h0 : gamma0 ηi χ φπ ρ ≠ 0) (h1 : gamma1 ηi χ φπ ≠ 0)
    (h01 : gamma0 ηi χ φπ ρ - gamma1 ηi χ φπ ≠ 0) :
    LambdaC ηi χ φπ ρ = 1 / gamma1 ηi χ φπ := by
  unfold LambdaC GammaT GammaC gammaR kappa
  have e0 : gamma0 ηi χ φπ ρ = (1 + ηi * χ) * φπ + ρ := rfl
  have e1 : gamma1 ηi χ φπ = 1 + ηi * χ * φπ := rfl
  have hsub : 1 - gamma1 ηi χ φπ / gamma0 ηi χ φπ ρ =
      (gamma0 ηi χ φπ ρ - gamma1 ηi χ φπ) / gamma0 ηi χ φπ ρ := by field_simp
  rw [hsub]
  field_simp
  rw [e0, e1]
  ring

/-- Woodford (2003), **(3.26)/(A.36)**, pp. 122, 647–648: if `|γ₁| < |γ₀|` and `γ₁ ≠ 0`, the unique
bounded solution `î` of (A.33) is
`î_t = Λ ī_t + Γ(1 − γ) ∑ γʲ E_t r̃_{t+j} − Γ̃(1 − γ) ∑ γʲ E_t ī_{t+j}`, `γ = γ₁/γ₀`. -/
theorem rate_A36 {ηi χ φπ ρ K1 K2 : ℝ} (hg : |gamma1 ηi χ φπ| < |gamma0 ηi χ φπ ρ|)
    (hg1 : gamma1 ηi χ φπ ≠ 0) {rt ibar : ℕ → Ω → ℝ} (h1 : ∀ t ω, |rt t ω| ≤ K1)
    (h2 : ∀ t ω, |ibar t ω| ≤ K2) (haib : 𝔼.Adapted ibar) (t : ℕ) (ω : Ω) :
    scalarSol 𝔼 (gamma0 ηi χ φπ ρ) (gamma1 ηi χ φπ) (f213 𝔼 φπ ρ rt ibar) t ω =
      LambdaC ηi χ φπ ρ * ibar t ω +
        GammaC ηi χ φπ ρ * (1 - gammaR ηi χ φπ ρ) *
          ∑' j, gammaR ηi χ φπ ρ ^ j * 𝔼.E t (rt (t + j)) ω -
        GammaT ηi χ φπ ρ * (1 - gammaR ηi χ φπ ρ) *
          ∑' j, gammaR ηi χ φπ ρ ^ j * 𝔼.E t (ibar (t + j)) ω := by
  have hA0 : gamma0 ηi χ φπ ρ ≠ 0 := abs_pos.mp (lt_of_le_of_lt (abs_nonneg _) hg)
  have hne : gamma0 ηi χ φπ ρ - gamma1 ηi χ φπ ≠ 0 := fun h0 => by
    have : gamma0 ηi χ φπ ρ = gamma1 ηi χ φπ := by linarith
    rw [this] at hg
    exact lt_irrefl _ hg
  have hL := LambdaC_eq hA0 hg1 hne
  have e0 : gamma0 ηi χ φπ ρ = (1 + ηi * χ) * φπ + ρ := rfl
  have e1 : gamma1 ηi χ φπ = 1 + ηi * χ * φπ := rfl
  unfold GammaT GammaC gammaR kappa
  rw [hL]
  set g0 := gamma0 ηi χ φπ ρ with hg0
  set g1 := gamma1 ηi χ φπ with hg1'
  clear_value g0 g1
  set R : ℕ → ℝ := fun j => 𝔼.E t (rt (t + j)) ω with hR
  set N : ℕ → ℝ := fun j => 𝔼.E t (ibar (t + j)) ω with hN
  have hRb : ∀ j, |R j| ≤ K1 := fun j => 𝔼.abs_E_le (fun ω' => h1 (t + j) ω') t ω
  have hNb : ∀ j, |N j| ≤ K2 := fun j => 𝔼.abs_E_le (fun ω' => h2 (t + j) ω') t ω
  have hNb1 : ∀ j, |N (j + 1)| ≤ K2 := fun j => hNb (j + 1)
  set c : ℕ → ℝ := fun j => g1 ^ j / g0 ^ (j + 1) with hc
  have hs2 : Summable (fun j => c j * R j) := summable_c_bdd hg hRb
  have hs3 : Summable (fun j => c j * N j) := summable_c_bdd hg hNb
  have hs4 : Summable (fun j => c j * N (j + 1)) := summable_c_bdd hg hNb1
  have hcs : ∀ j, c (j + 1) = g1 / g0 * c j := fun j => by
    simp only [hc]; field_simp; ring
  have hEf : ∀ j, 𝔼.E t (f213 𝔼 φπ ρ rt ibar (t + j)) ω = φπ * R j + ρ * N j - N (j + 1) :=
    fun j => by
    simp only [f213, hR, hN, map_add, map_sub, map_smul, 𝔼.tower (Nat.le_add_right t j),
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show t + (j + 1) = t + j + 1 by omega]
  have hI : scalarSol 𝔼 g0 g1 (f213 𝔼 φπ ρ rt ibar) t ω =
      φπ * ∑' j, c j * R j + ρ * ∑' j, c j * N j - ∑' j, c j * N (j + 1) := by
    rw [scalarSol_apply]
    have H := ((hs2.hasSum.mul_left φπ).add (hs3.hasSum.mul_left ρ)).sub hs4.hasSum
    refine HasSum.tsum_eq ?_
    convert H using 1
    funext j
    rw [hEf j]
    simp only [hc]
    ring
  have hgam : ∀ j, (g1 / g0) ^ j = g0 * c j := fun j => by
    simp only [hc]; rw [div_pow]; field_simp; ring
  have hR' : ∑' j, (g1 / g0) ^ j * R j = g0 * ∑' j, c j * R j := by
    rw [← tsum_mul_left]; exact tsum_congr fun j => by rw [hgam j]; ring
  have hN' : ∑' j, (g1 / g0) ^ j * N j = g0 * ∑' j, c j * N j := by
    rw [← tsum_mul_left]; exact tsum_congr fun j => by rw [hgam j]; ring
  have hS3 : ∑' j, c j * N j = N 0 / g0 + g1 / g0 * ∑' j, c j * N (j + 1) := by
    rw [hs3.tsum_eq_zero_add, ← tsum_mul_left]
    congr 1
    · simp only [hc]; ring
    · exact tsum_congr fun j => by rw [hcs j]; ring
  have hN0 : N 0 = ibar t ω := by simp only [hN, add_zero, haib t]
  change scalarSol 𝔼 g0 g1 (f213 𝔼 φπ ρ rt ibar) t ω = 1 / g1 * ibar t ω +
    φπ / (g0 - g1) * (1 - g1 / g0) * ∑' j, (g1 / g0) ^ j * R j -
    φπ / (g0 - g1) * (1 + (1 - ρ) * ηi * χ) / g1 * (1 - g1 / g0) * ∑' j, (g1 / g0) ^ j * N j
  have hc1 : φπ / (g0 - g1) * (1 - g1 / g0) = φπ / g0 := by field_simp
  have hc2 : φπ / (g0 - g1) * (1 + (1 - ρ) * ηi * χ) / g1 * (1 - g1 / g0) =
      φπ * (1 + (1 - ρ) * ηi * χ) / (g0 * g1) := by field_simp
  rw [hc1, hc2, hI, hR', hN', hS3, ← hN0]
  have hρ : ρ = g0 - (1 + ηi * χ) * φπ := by linarith [e0]
  subst hρ
  rw [e1] at hg1 hne ⊢
  have hg1n : 1 + φπ * ηi * χ ≠ 0 := by intro h; apply hg1; linear_combination h
  field_simp
  ring

/-- Woodford (2003), **A.15**, p. 648 (limits of the coefficients, **E3 corrected**): with
`Φ_π > 1`, `ψ > 0`, (3.25) and `χ(Δ) → χ̄`, as `Δ → 0⁺`:
`Λ → 1/(1 + η̃_iχ̄Φ_πψ)`, `Γ = Φ_π/(Φ_π − 1)` for every `Δ > 0`,
`Γ̃ → (Φ_π/(Φ_π − 1))(1 + η̃_iχ̄ψ)/(1 + η̃_iχ̄Φ_πψ)` and
`ξ = −log γ/Δ → (Φ_π − 1)ψ/(1 + η̃_iχ̄Φ_πψ)`. -/
theorem prop_2_15_limits {η Φ ψ χbar : ℝ} {χ : ℝ → ℝ} (hΦ : 1 < Φ) (hψ : 0 < ψ)
    (h325 : 0 < Glim η χbar Φ ψ) (hlim : Tendsto χ (𝓝[>] 0) (𝓝 χbar)) :
    Tendsto (fun Δ => LambdaC (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ)) (𝓝[>] 0)
        (𝓝 (1 / Glim η χbar Φ ψ)) ∧
      (∀ Δ, 0 < Δ → GammaC (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ) = Φ / (Φ - 1)) ∧
      Tendsto (fun Δ => GammaT (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ)) (𝓝[>] 0)
        (𝓝 (Φ / (Φ - 1) * (1 + η * χbar * ψ) / Glim η χbar Φ ψ)) ∧
      Tendsto (fun Δ => -Real.log (gammaR (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ)) / Δ)
        (𝓝[>] 0) (𝓝 ((Φ - 1) * ψ / Glim η χbar Φ ψ)) := by
  obtain ⟨h0, h1⟩ := tendsto_gammas (η := η) (Φ := Φ) (ψ := ψ) hlim
  have hG : Glim η χbar Φ ψ ≠ 0 := h325.ne'
  have ev : ∀ᶠ Δ in 𝓝[>] (0 : ℝ), 0 < Δ ∧ 0 < gamma0 (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ) ∧
      0 < gamma1 (η / Δ) (χ Δ) (phiD Φ ψ Δ) := by
    filter_upwards [h0.eventually (lt_mem_nhds h325), h1.eventually (lt_mem_nhds h325),
      self_mem_nhdsWithin] with Δ g0 g1 hΔ
    exact ⟨hΔ, g0, g1⟩
  have hGam : ∀ Δ, 0 < Δ → GammaC (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ) = Φ / (Φ - 1) := by
    intro Δ hΔ
    unfold GammaC
    rw [gamma_sub_D]
    have : 0 < 1 - rhoD ψ Δ := by linarith [rhoD_lt_one hψ hΔ]
    have : Φ - 1 ≠ 0 := by linarith
    unfold phiD
    field_simp
  have hsub_ne : ∀ Δ, 0 < Δ → gamma0 (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ) -
      gamma1 (η / Δ) (χ Δ) (phiD Φ ψ Δ) ≠ 0 := fun Δ hΔ => by
    rw [gamma_sub_D]
    have : 0 < 1 - rhoD ψ Δ := by linarith [rhoD_lt_one hψ hΔ]
    have : 0 < Φ - 1 := by linarith
    positivity
  refine ⟨?_, hGam, ?_, ?_⟩
  · -- `Λ = 1/γ₁ → 1/G`
    have := h1.inv₀ hG
    rw [← one_div] at this
    refine (this.congr' ?_)
    filter_upwards [ev] with Δ ⟨hΔ, g0, g1⟩
    rw [LambdaC_eq g0.ne' g1.ne' (hsub_ne Δ hΔ), one_div]
  · -- `Γ̃ = Γ κ/γ₁`
    have hκ : Tendsto (fun Δ => kappa (η / Δ) (χ Δ) (rhoD ψ Δ)) (𝓝[>] 0)
        (𝓝 (1 + η * χbar * ψ)) := by
      have h := ((hlim.const_mul η).mul (tendsto_one_sub_exp_div ψ)).const_add 1
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with Δ hΔ
      have : Δ ≠ 0 := ne_of_gt hΔ
      unfold kappa rhoD
      field_simp
    have h := ((tendsto_const_nhds (x := Φ / (Φ - 1))).mul hκ).div h1 hG
    refine h.congr' ?_
    filter_upwards [ev] with Δ ⟨hΔ, _, _⟩
    simp only [Pi.div_apply]
    unfold GammaT
    rw [hGam Δ hΔ]
  · -- `ξ = −log γ/Δ`
    have hγ : Tendsto (fun Δ => gammaR (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ)) (𝓝[>] 0)
        (𝓝[≠] 1) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have := h1.div h0 hG
        rw [div_self hG] at this
        exact this
      · filter_upwards [ev] with Δ ⟨hΔ, g0, _⟩
        intro h
        have h' : gamma1 (η / Δ) (χ Δ) (phiD Φ ψ Δ) =
            gamma0 (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ) := by
          have := (div_eq_one_iff_eq g0.ne').mp h
          exact this
        exact hsub_ne Δ hΔ (by rw [h']; ring)
    have hlog : Tendsto (fun x => Real.log x / (x - 1)) (𝓝[≠] 1) (𝓝 1) := by
      have := (Real.hasDerivAt_log (one_ne_zero (α := ℝ))).tendsto_slope
      rw [inv_one] at this
      refine this.congr' (Eventually.of_forall fun x => ?_)
      rw [slope_def_field, Real.log_one, sub_zero]
    have hA := hlog.comp hγ
    have hB : Tendsto (fun Δ => (1 - gammaR (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ)) / Δ)
        (𝓝[>] 0) (𝓝 ((Φ - 1) * ψ / Glim η χbar Φ ψ)) := by
      have h := ((tendsto_one_sub_exp_div ψ).const_mul (Φ - 1)).div h0 hG
      refine h.congr' ?_
      filter_upwards [ev] with Δ ⟨hΔ, g0, _⟩
      simp only [Pi.div_apply]
      have hd : 1 - gammaR (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ) =
          (Φ - 1) * (1 - rhoD ψ Δ) / gamma0 (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ) := by
        rw [← gamma_sub_D η (χ Δ) Φ ψ Δ]
        unfold gammaR
        field_simp
      rw [hd]
      unfold rhoD
      have : Δ ≠ 0 := ne_of_gt hΔ
      field_simp
    have h := hA.mul hB
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [ev] with Δ ⟨hΔ, g0, _⟩
    have hne1 : gammaR (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ) - 1 ≠ 0 := by
      intro h'
      apply hsub_ne Δ hΔ
      unfold gammaR at h'
      have := (div_eq_one_iff_eq g0.ne').mp (sub_eq_zero.mp h')
      rw [this]; ring
    have : 1 - gammaR (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ) =
        -(gammaR (η / Δ) (χ Δ) (phiD Φ ψ Δ) (rhoD ψ Δ) - 1) := by ring
    simp only [Function.comp_apply]
    rw [this]
    field_simp

/-- Woodford (2003), A.15, p. 648: the limiting values `1/G`, `Φ_π/(Φ_π − 1)`,
`(Φ_π/(Φ_π − 1))(1 + η̃_iχ̄ψ)/G` and `(Φ_π − 1)ψ/G`, `G = 1 + η̃_iχ̄Φ_πψ`, are continuous in `χ̄`
on the region (3.25) `G > 0` (which contains a neighbourhood of `χ̄ = 0`). -/
theorem limits_continuousOn (η Φ ψ : ℝ) :
    ContinuousOn (fun χbar => 1 / Glim η χbar Φ ψ) {χbar | 0 < Glim η χbar Φ ψ} ∧
      ContinuousOn (fun _ : ℝ => Φ / (Φ - 1)) {χbar | 0 < Glim η χbar Φ ψ} ∧
      ContinuousOn (fun χbar => Φ / (Φ - 1) * (1 + η * χbar * ψ) / Glim η χbar Φ ψ)
        {χbar | 0 < Glim η χbar Φ ψ} ∧
      ContinuousOn (fun χbar => (Φ - 1) * ψ / Glim η χbar Φ ψ) {χbar | 0 < Glim η χbar Φ ψ} := by
  have hc : Continuous (fun χbar => Glim η χbar Φ ψ) := by unfold Glim; fun_prop
  have hne : ∀ χbar ∈ {χbar | 0 < Glim η χbar Φ ψ}, Glim η χbar Φ ψ ≠ 0 :=
    fun χbar h => ne_of_gt h
  refine ⟨continuousOn_const.div hc.continuousOn hne, continuousOn_const, ?_, ?_⟩
  · exact (Continuous.continuousOn (by fun_prop)).div hc.continuousOn hne
  · exact continuousOn_const.div hc.continuousOn hne

/-- Woodford (2003), A.15, p. 648: under `Φ_π > 1`, `ψ > 0`, `η̃_i > 0` and (3.25) all limiting
values are positive (in particular `Γ̃ > 0` also for modestly negative `χ̄`). -/
theorem limits_pos {η Φ ψ χbar : ℝ} (hη : 0 < η) (hΦ : 1 < Φ) (hψ : 0 < ψ)
    (h325 : 0 < Glim η χbar Φ ψ) :
    0 < 1 / Glim η χbar Φ ψ ∧ 0 < Φ / (Φ - 1) ∧
      0 < Φ / (Φ - 1) * (1 + η * χbar * ψ) / Glim η χbar Φ ψ ∧
      0 < (Φ - 1) * ψ / Glim η χbar Φ ψ := by
  have h1 : 0 < Φ - 1 := by linarith
  have h2 : 0 < 1 + η * χbar * ψ := by
    unfold Glim at h325
    rcases le_or_gt 0 χbar with h | h
    · have : 0 ≤ η * χbar * ψ := by positivity
      linarith
    · have : η * χbar * Φ * ψ < η * χbar * ψ := by
        have hn : η * χbar * ψ < 0 := by
          have := mul_neg_of_pos_of_neg hη h
          exact mul_neg_of_neg_of_pos this hψ
        nlinarith
      linarith
  refine ⟨by positivity, by positivity, by positivity, by positivity⟩

/-- Woodford (2003), A.15, p. 648 (**E3**): the printed identity
`Λ + Γ(1 − γ) − 1 = (1 + η_iχ)φ_π/((1 + η_iχ)φ_π + ρ)` is false — e.g. for `η_iχ = 1`
(`η_i = χ = 1`), `φ_π = 1`, `ρ = 1/2` the left side is `−1/10` and the right side `4/5`. -/
theorem book_identity_false :
    LambdaC 1 1 1 (1 / 2) + GammaC 1 1 1 (1 / 2) * (1 - gammaR 1 1 1 (1 / 2)) - 1 = -1 / 10 ∧
      (1 + 1 * 1) * 1 / ((1 + 1 * 1) * 1 + 1 / 2) = (4 : ℝ) / 5 := by
  simp only [LambdaC, GammaT, GammaC, gammaR, kappa, gamma0, gamma1]
  norm_num

/-- Woodford (2003), A.15, p. 648 (**E3**): the printed limit `Λ → 1 + (G − 1)/G`,
`G = 1 + η̃_iχ̄Φ_πψ > 0`, differs from the true limit `1/G` unless `G = 1`, i.e. unless `χ̄ = 0`
(for `η̃_i, Φ_π, ψ ≠ 0`). -/
theorem book_Lambda_limit_wrong {G : ℝ} (hG : 0 < G) (hG1 : G ≠ 1) :
    1 / G ≠ 1 + (G - 1) / G := by
  intro h
  rw [eq_comm, ← sub_eq_zero] at h
  have : 1 + (G - 1) / G - 1 / G = 2 * (G - 1) / G := by field_simp; ring
  rw [this, div_eq_zero_iff] at h
  rcases h with h | h
  · exact hG1 (by linarith)
  · exact hG.ne' h

/-- Woodford (2003), A.15 (**E3**, survey example): `η̃_i = 7`, `χ̄ = 0.01`, `Φ_π = 1.5`, `ψ = 0.9`
give `G = 1.0945`; the true limit `1/G ≈ 0.9137`, the printed one `≈ 1.0863`. -/
theorem E3_numbers :
    Glim 7 0.01 1.5 0.9 = 1.0945 ∧ (0.9136 : ℝ) < 1 / Glim 7 0.01 1.5 0.9 ∧
      1 / Glim 7 0.01 1.5 0.9 < 0.9137 ∧
      (1.0863 : ℝ) < 1 + (Glim 7 0.01 1.5 0.9 - 1) / Glim 7 0.01 1.5 0.9 ∧
      1 + (Glim 7 0.01 1.5 0.9 - 1) / Glim 7 0.01 1.5 0.9 < 1.0864 := by
  simp only [Glim]
  norm_num

end Woodford.PriceLevelDetermination.ShortPeriod
