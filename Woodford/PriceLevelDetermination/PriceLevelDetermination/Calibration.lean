/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.NonSeparable

/-!
# Calibrating the real-balance effect `χ`

Woodford (2003), *Interest and Prices*, Chapter 2, §3.4, pp. 117–120: equation (3.23), the
numerical bounds on `χ`, the parameters of Figure 2.2 and the closed form behind Figure 2.3.

* p. 117: `hasFDerivAt_logMRS` — linearising the money-demand condition (3.3),
  `log(u_m/u_c)(Ȳe^ŷ, m̄e^m̂)` has derivative `(σ⁻¹ + υ) ŷ + (m̄u_mm/u_m − χ) m̂` (exact), and
  `hasDerivAt_logSpread` — with no interest on money `log Δ(ī e^ĵ)` has derivative `β`; so
  `m̂ ∝ (σ⁻¹ + υ) Ŷ − β log(i/ī)` and the ratio of income to interest elasticity is
  `β⁻¹(σ⁻¹ + υ)` (`elasticity_ratio`).
* **(3.23)**, p. 118: `chi_calibrated` — a ratio of 2 gives `χ = s_m(2β − σ⁻¹)`.
* **E8** (p. 118, "if σ is greater than 0.5 … χ > 0"): `chi_pos_iff_sigma` — the correct
  condition is `σ > 1/(2β)`; `sigma_threshold_bounds` (`≈ 0.505` at `β = 0.99`) and
  `book_sigma_claim_false` (counterexample `σ = 0.502`).
* p. 118: `chi_lt_two_sm` (`χ < 2 s_m`), `sm_value` (`s_m = 0.0025`), `chi_le_005`,
  `semilog_ratio_bounds` (`1/0.28 ≈ 3.6`), `chi_semilog_lt` (`χ < 3.6 s_m = 0.009 ≤ 0.01`).
* Figure 2.2, p. 119: `fig22_parameters` (`Φ_π = 1.5`, determinacy, (3.16)), `fig22_phiT0`
  (the larger weight on the current intercept at `χ = 0.02`).
* Figure 2.3, pp. 119–120: `hasSum_weights_geom` and `impact_AR1` — for an AR(1) `r̃` with
  coefficient `ρ_r`, `∑ ϕ_j E_t r̃_{t+j} = r̃_t/(A − Bρ_r)` with `A = (1 + η_iχ)φ_π + ρ`,
  `B = 1 + η_iχφ_π`; `fig23_check` (the value `2.5` at `χ = 0`, `ρ_r → 1`).
-/

namespace Woodford.PriceLevelDetermination.Calibration

open Filter Topology
open Woodford.PriceLevelDetermination.MoneyGrowth Woodford.PriceLevelDetermination.NonSeparable

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Linearising the money-demand condition (3.3) -/

/-- Woodford (2003), p. 117: the log marginal rate of substitution
`log(u_m/u_c)(Ȳ e^{ŷ}, m̄ e^{m̂})` (relative to the steady state). -/
noncomputable def logMRS (Um Uc : ℝ × ℝ → ℝ) (Ybar mbar : ℝ) (x : ℝ × ℝ) : ℝ :=
  logMU Um Ybar mbar x - logMU Uc Ybar mbar x

/-- Woodford (2003), p. 117 (exact derivative): with `u_m, u_c > 0` differentiable at
`(Ȳ, m̄)`, `logMRS` has derivative `(υ + σ⁻¹) ŷ + (m̄ u_mm/u_m − χ) m̂`, where
`υ = Ȳu_mc/u_m`, `σ⁻¹ = −Ȳu_cc/u_c`, `χ = m̄u_cm/u_c` (`u_mc = Um'(1,0)`, `u_mm = Um'(0,1)`,
`u_cc = Uc'(1,0)`, `u_cm = Uc'(0,1)`). -/
theorem hasFDerivAt_logMRS {Um Uc : ℝ × ℝ → ℝ} {Um' Uc' : ℝ × ℝ →L[ℝ] ℝ} {Ybar mbar : ℝ}
    (hUm : HasFDerivAt Um Um' (Ybar, mbar)) (hUc : HasFDerivAt Uc Uc' (Ybar, mbar))
    (hm : 0 < Um (Ybar, mbar)) (hc : 0 < Uc (Ybar, mbar)) :
    ∃ G' : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (logMRS Um Uc Ybar mbar) G' 0 ∧
      ∀ v, G' v = (upsilon Ybar (Um (Ybar, mbar)) (Um' (1, 0)) +
          -(Uc' (1, 0)) * Ybar / Uc (Ybar, mbar)) * v.1 +
        (mbar * Um' (0, 1) / Um (Ybar, mbar) - chi mbar (Uc (Ybar, mbar)) (Uc' (0, 1))) * v.2 := by
  obtain ⟨G1, h1, e1⟩ := hasFDerivAt_logMU hUm hm
  obtain ⟨G2, h2, e2⟩ := hasFDerivAt_logMU hUc hc
  refine ⟨G1 - G2, h1.sub h2, fun v => ?_⟩
  rw [sub_apply, e1, e2]
  unfold upsilon chi
  ring

/-- Woodford (2003), p. 117: the interest differential with no interest on money,
`Δ = i/(1 + i)`, as a function of `ĵ = log(i/ī)`: `log Δ(ī e^{ĵ})`. -/
noncomputable def logSpread (ibar : ℝ) (j : ℝ) : ℝ :=
  Real.log (ibar * Real.exp j / (1 + ibar * Real.exp j))

/-- Woodford (2003), p. 117 (exact derivative): with `1 + ī = β⁻¹`, `ī > 0`, the derivative of
`log Δ` with respect to `log i` at the steady state is `β = 1/(1 + ī)`. -/
theorem hasDerivAt_logSpread {ibar : ℝ} (hi : 0 < ibar) :
    HasDerivAt (logSpread ibar) (1 / (1 + ibar)) 0 := by
  have h1 : HasDerivAt (fun j => ibar * Real.exp j) (ibar * Real.exp 0) 0 :=
    (Real.hasDerivAt_exp 0).const_mul ibar
  have h2 : HasDerivAt (fun j => 1 + ibar * Real.exp j) (ibar * Real.exp 0) 0 :=
    h1.const_add 1
  have hne : 1 + ibar * Real.exp 0 ≠ 0 := by rw [Real.exp_zero]; linarith
  have h3 := h1.div h2 hne
  have hpos : ibar * Real.exp 0 / (1 + ibar * Real.exp 0) ≠ 0 := by
    rw [Real.exp_zero]; positivity
  have h4 := h3.log hpos
  unfold logSpread
  convert h4 using 1
  simp only [Pi.div_apply, Real.exp_zero, mul_one]
  field_simp
  ring

/-- Woodford (2003), p. 117: if the linearised condition reads
`κ m̂ = (σ⁻¹ + υ) Ŷ − β ĵ` (`κ ≠ 0`), the income elasticity of money demand is `(σ⁻¹ + υ)/κ`,
the elasticity with respect to `i` is `β/κ`, and their ratio is `β⁻¹(σ⁻¹ + υ)`. -/
theorem elasticity_ratio {κ σinv υ β : ℝ} (hκ : κ ≠ 0) (hβ : β ≠ 0) :
    ((σinv + υ) / κ) / (β / κ) = (σinv + υ) / β := by
  field_simp

/-- Woodford (2003), **(3.23)**, p. 118: if the ratio of income to interest elasticity is
`ratio = β⁻¹(σ⁻¹ + υ)`, then `υ = ratio·β − σ⁻¹`; with Lucas's ratio `2`, `χ = s_m υ =
s_m(2β − σ⁻¹)`. -/
theorem chi_calibrated {sm σinv υ β χ : ℝ} (hβ : β ≠ 0) (hχ : χ = sm * υ)
    (hratio : (σinv + υ) / β = 2) : χ = sm * (2 * β - σinv) := by
  rw [div_eq_iff hβ] at hratio
  rw [hχ]
  congr 1
  linarith

/-- Woodford (2003), p. 118 (**E8 corrected**): with `s_m > 0`, `σ > 0`, `β > 0`,
`χ = s_m(2β − σ⁻¹) > 0` if and only if `σ > 1/(2β)` (not `σ > 0.5`). -/
theorem chi_pos_iff_sigma {sm σ β : ℝ} (hsm : 0 < sm) (hσ : 0 < σ) (hβ : 0 < β) :
    0 < sm * (2 * β - σ⁻¹) ↔ 1 / (2 * β) < σ := by
  rw [mul_pos_iff_of_pos_left hsm, sub_pos, div_lt_iff₀ (by positivity),
    inv_lt_iff_one_lt_mul₀ hσ]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 118 (E8): at `β = 0.99` the threshold `1/(2β)` lies in `(0.505, 0.506)`,
strictly above the book's `0.5`. -/
theorem sigma_threshold_bounds :
    (0.505 : ℝ) < 1 / (2 * 0.99) ∧ 1 / (2 * (0.99 : ℝ)) < 0.506 ∧ (0.5 : ℝ) < 1 / (2 * 0.99) := by
  norm_num

/-- Woodford (2003), p. 118 (**E8, counterexample**): `σ = 0.502 > 0.5` with `β = 0.99` gives
`2β − σ⁻¹ < 0`, hence `χ < 0` for every `s_m > 0` — the printed claim "σ > 0.5 ⇒ χ > 0" is
false. -/
theorem book_sigma_claim_false {sm : ℝ} (hsm : 0 < sm) :
    (0.5 : ℝ) < 0.502 ∧ sm * (2 * 0.99 - (0.502 : ℝ)⁻¹) < 0 := by
  refine ⟨by norm_num, mul_neg_of_pos_of_neg hsm (by norm_num)⟩

/-- Woodford (2003), p. 118: "no matter how large σ is assumed to be, the factor in parentheses
in (3.23) cannot exceed 2": for `σ > 0`, `0 < β ≤ 1`, `χ = s_m(2β − σ⁻¹) < 2 s_m`. -/
theorem chi_lt_two_sm {sm σ β : ℝ} (hsm : 0 < sm) (hσ : 0 < σ) (hβ : β ≤ 1) :
    sm * (2 * β - σ⁻¹) < 2 * sm := by
  have : 0 < σ⁻¹ := inv_pos.mpr hσ
  nlinarith

/-- Woodford (2003), p. 118: with zero interest on money `Δ̄ = 1 − β = 0.01` (`β = 0.99`) and a
monetary base of 25 percent of quarterly GDP, `s_m = Δ̄ m̄/Ȳ = 0.0025`. -/
theorem sm_value : (1 - (0.99 : ℝ)) * 0.25 = 0.0025 := by norm_num

/-- Woodford (2003), p. 118: hence `χ < 2 s_m = 0.005` (for any `σ > 0`, `β = 0.99`). -/
theorem chi_le_005 {σ : ℝ} (hσ : 0 < σ) : (0.0025 : ℝ) * (2 * 0.99 - σ⁻¹) < 0.005 := by
  have := chi_lt_two_sm (sm := 0.0025) (β := 0.99) (by norm_num) hσ (by norm_num)
  linarith

/-- Woodford (2003), p. 118 (semilog money demand, `η_y = 1`, `η_i = 28` quarters): the ratio
`η_y/((1 − β)η_i) = 1/0.28` lies in `(3.57, 3.6)`. -/
theorem semilog_ratio_bounds :
    (3.57 : ℝ) < 1 / ((1 - 0.99) * 28) ∧ 1 / ((1 - (0.99 : ℝ)) * 28) < 3.6 := by
  norm_num

/-- Woodford (2003), p. 118: with the semilog ratio `1/0.28`, `υ = β/0.28 − σ⁻¹` and
`χ = s_m υ < 3.6 s_m = 0.009 ≤ 0.01`; the multiple of `s_m` (`< 3.6`) is less than twice the
earlier `2`. -/
theorem chi_semilog_lt {σ : ℝ} (hσ : 0 < σ) :
    (0.0025 : ℝ) * (0.99 / ((1 - 0.99) * 28) - σ⁻¹) < 3.6 * 0.0025 ∧
      (3.6 : ℝ) * 0.0025 ≤ 0.01 ∧ (3.6 : ℝ) < 2 * 2 := by
  have : 0 < σ⁻¹ := inv_pos.mpr hσ
  refine ⟨?_, by norm_num, by norm_num⟩
  have h : (0.99 : ℝ) / ((1 - 0.99) * 28) < 3.6 := by norm_num
  nlinarith

/-! ### Figures 2.2 and 2.3 -/

/-- Woodford (2003), Figure 2.2, p. 118–119: `ρ = 0.8`, `φ_π = 0.3` give the long-run response
`Φ_π = φ_π/(1 − ρ) = 1.5`; the Taylor principle `φ_π + ρ > 1` holds and `χ = 0.02` satisfies
(3.16) with `η_i = 28`. -/
theorem fig22_parameters :
    (0.3 : ℝ) / (1 - 0.8) = 1.5 ∧ (1 : ℝ) < 0.3 + 0.8 ∧ -1 / (2 * (28 : ℝ)) < 0.02 := by
  norm_num

/-- Woodford (2003), Figure 2.2 and p. 119: the weight on the current intercept is
`ϕ̃_0 = 1/1.1` at `χ = 0` and `1.56/1.268` at `χ = 0.02` (`η_i = 28`), the latter larger
("a slightly larger relative weight on the current period's intercept"). -/
theorem fig22_phiT0 :
    phiT213 28 0 0.3 0.8 0 = 1 / 1.1 ∧ phiT213 28 0.02 0.3 0.8 0 = 1.56 / 1.268 ∧
      phiT213 28 0 0.3 0.8 0 < phiT213 28 0.02 0.3 0.8 0 := by
  simp only [phiT213, gamma0]
  norm_num

/-- Woodford (2003), Figure 2.3, pp. 119–120 (survey L2): for `|Bρ_r| < |A|`,
`∑_j Bʲ/A^{j+1} ρ_rʲ = 1/(A − Bρ_r)` (the case `c = 1`, `B ↦ Bρ_r` of
`ForwardSolution.hasSum_geometric_ratio`). -/
theorem hasSum_weights_geom {A B ρr : ℝ} (h : |B * ρr| < |A|) :
    HasSum (fun j : ℕ => B ^ j / A ^ (j + 1) * ρr ^ j) (1 / (A - B * ρr)) :=
  (ForwardSolution.hasSum_geometric_ratio 1 h).congr_fun fun j => by ring

/-- Woodford (2003), Figure 2.3, p. 119–120: if `r̃` is AR(1) with coefficient `|ρ_r| ≤ 1`
and the economy of Prop. 2.13 is determinate (`|γ₁| < |γ₀|`), the response of inflation to
`r̃_t` is `∑ ϕ_j E_t r̃_{t+j} = r̃_t/(A − Bρ_r)` with `A = (1 + η_iχ)φ_π + ρ` and
`B = 1 + η_iχφ_π` (the impact effect of a unit innovation is `1/(A − Bρ_r)`). -/
theorem impact_AR1 {ηi χ φπ ρ ρr : ℝ} (hg : |gamma1 ηi χ φπ| < |gamma0 ηi χ φπ ρ|)
    (hρr : |ρr| ≤ 1) {r : ℕ → Ω → ℝ} (hr : 𝔼.IsAR1 ρr r) (t : ℕ) (ω : Ω) :
    ∑' j, phi213 ηi χ φπ ρ j * 𝔼.E t (r (t + j)) ω =
      r t ω / (gamma0 ηi χ φπ ρ - gamma1 ηi χ φπ * ρr) := by
  have h : |gamma1 ηi χ φπ * ρr| < |gamma0 ηi χ φπ ρ| := by
    rw [abs_mul]
    calc |gamma1 ηi χ φπ| * |ρr| ≤ |gamma1 ηi χ φπ| * 1 :=
          mul_le_mul_of_nonneg_left hρr (abs_nonneg _)
      _ < _ := by rw [mul_one]; exact hg
  have hs := (hasSum_weights_geom h).mul_right (r t ω)
  rw [div_mul_eq_mul_div, one_mul] at hs
  rw [← hs.tsum_eq]
  refine tsum_congr fun j => ?_
  rw [𝔼.ar1_iterate hr t j, Pi.smul_apply, smul_eq_mul, phi213]
  ring

/-- Woodford (2003), Figure 2.3, top panel, p. 120: at `χ = 0`, `φ_π = 0.3`, `ρ = 0.8`, the impact
response tends to `1/(1.1 − 1) = 10` as `ρ_r → 1`, i.e. `0.25 × 10 = 2.5` for a shock of one
percentage point per annum in a quarterly model (fn 53: `r̃` jumps by `Δ = 0.25`). -/
theorem fig23_check :
    (1 : ℝ) / (gamma0 28 0 0.3 0.8 - gamma1 28 0 0.3 * 1) = 10 ∧
      (0.25 : ℝ) * (1 / (gamma0 28 0 0.3 0.8 - gamma1 28 0 0.3 * 1)) = 2.5 := by
  simp only [gamma0, gamma1]
  norm_num

end Woodford.PriceLevelDetermination.Calibration
