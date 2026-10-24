/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InflTargetPredetermined

/-!
# Optimal policy for the Giannoni–Woodford quantitative model

Woodford (2003), *Interest and Prices*, Chapter 8, §2.5, pp. 573–582: eqs. (2.35)–(2.45), for the
model of Giannoni and Woodford (2003b) (Ch. 5 §2.2, Table 5.3).

## Main results

* (2.35)–(2.38): `lossGW`, `lamP`, `lamW`, `lamX`, `kappaGW`; `lamP_pos`, `lamW_pos`,
  `lamP_add_lamW` (`λp + λw = 1`), `lamX_pos`, `kappaGW_pos`.
* (2.39): `deltaPoly`, `deltaGW` (the smaller root, explicitly), `deltaPoly_deltaGW`,
  `deltaGW_pos`, `deltaGW_lt_eta`, `deltaPoly_factor`, `deltaGW_mul_deltaBig` (product of the
  roots is `β⁻¹`), `deltaGW_unique` (the only root in `[0, η]`),
  `deltaGW_strictAnti_omega` (smaller for larger `ω`), `deltaGW_strictMono_eta` (increasing in
  `η ≤ 1`, p. 568).
* The numbers (p. 574) from Table 5.3 (`θp = 1 + 1/0.004`, `θw = 1 + 1/0.54`, `φ⁻¹ = 0.75`,
  `ξp = 0.0020`, `ξw = 0.0042`, `ϕ = 0.75`, `η = 1`, `β = 0.99`, `ω = ωw + ωp = 19.93`):
  `lamP_table` (`λp = 13554/13609 ≈ 0.99596`, prints as `.9960`), `lamW_table`
  (`λw = 55/13609 ≈ 0.00404`, prints as `.0040`), `deltaGW_table` (`0.03505 < δ < 0.03506`, prints
  as `.035`), `lamX_table` (`λx ≈ 0.000170` in the model's quarterly units and
  `16λx ∈ (0.002716, 0.002718)` in annualised-inflation units: the printed `0.0026` is **not** an
  exact consequence of the table — see the report).
* (2.40): `forecastable_of_optimal` (for any problem in which replacing `i_t` by `E_{t−d} i_t`
  preserves feasibility and the other losses, an optimal plan has `E_{t0}(i_t − E_{t−d} i_t)² = 0`)
  and its `d = 1` case `eq240_of_optimal`; `gwIS_fcst_iff` (Ch. 5 (2.4) involves `i` only through
  forecasts made a quarter or more earlier).
* (2.41)–(2.45): `Fc` (the weighted forecast (2.42)), `Fc_add_const` (weights summing to one),
  `Fc_known`; `eq243_of_eq241` (a predetermined target in (2.41) must be (2.43)),
  `eq241_243_iff` ((2.41) with (2.43) says the left side of (2.41) is forecastable a quarter
  ahead), `sr_invariant`; `eq244_245_simplified` (footnote 28), `lr_invariant` (only differences
  matter, p. 577), `lrTarget_predetermined` (`π*_t` is a predetermined target).

The numerical target-criterion coefficients `φw = 0.565`, `φ*w = 0.258`, `φ*x = 0.135`,
`θ*π = 0.580`, `θ*w = 0.252`, `θ*x = 0.125` and the weights of Figs. 8.1–8.2 come from the technical
appendix of Giannoni and Woodford (2003b), which also contains the model's first-order conditions;
they are not derivable from the book.
-/

namespace Woodford.OptimalPolicyRules.GWModel

open Filter Topology
open InflTargetPredetermined (fcst iLoss iLoss_decomp summable_weighted)

/-! ### The loss function (2.35)–(2.38) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eq. (2.35), p. 573: the period loss
`λp(πt − γp πt−1)² + λw(πʷt − γw πt−1)² + λx(xt − δxt−1 − x̂*)²`. -/
noncomputable def lossGW (lp lw lx γp γw δ xh : ℝ) (π πw x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => lp * (π t ω - γp * π (t - 1) ω) ^ 2 + lw * (πw t ω - γw * π (t - 1) ω) ^ 2 +
    lx * (x t ω - δ * x (t - 1) ω - xh) ^ 2

/-- Woodford (2003), eq. (2.36), p. 573: `λp = θp ξp⁻¹ / (θp ξp⁻¹ + θw φ⁻¹ ξw⁻¹)`. -/
noncomputable def lamP (θp ξp θw φ ξw : ℝ) : ℝ :=
  θp * ξp⁻¹ / (θp * ξp⁻¹ + θw * φ⁻¹ * ξw⁻¹)

/-- Woodford (2003), eq. (2.36), p. 573: `λw = θw φ⁻¹ ξw⁻¹ / (θp ξp⁻¹ + θw φ⁻¹ ξw⁻¹)`. -/
noncomputable def lamW (θp ξp θw φ ξw : ℝ) : ℝ :=
  θw * φ⁻¹ * ξw⁻¹ / (θp * ξp⁻¹ + θw * φ⁻¹ * ξw⁻¹)

/-- Woodford (2003), eq. (2.38), p. 573: `κ ≡ ξp η ϕ / δ`. -/
noncomputable def kappaGW (ξp η vphi δ : ℝ) : ℝ := ξp * η * vphi / δ

/-- Woodford (2003), eq. (2.37), p. 573: `λx = λp κ / θp`. -/
noncomputable def lamX (θp ξp θw φ ξw κ : ℝ) : ℝ := lamP θp ξp θw φ ξw * κ / θp

/-- Woodford (2003), eq. (2.36), p. 573: `λp > 0`. -/
theorem lamP_pos {θp ξp θw φ ξw : ℝ} (h1 : 0 < θp) (h2 : 0 < ξp) (h3 : 0 < θw) (h4 : 0 < φ)
    (h5 : 0 < ξw) : 0 < lamP θp ξp θw φ ξw := by
  unfold lamP; positivity

/-- Woodford (2003), eq. (2.36), p. 573: `λw > 0`. -/
theorem lamW_pos {θp ξp θw φ ξw : ℝ} (h1 : 0 < θp) (h2 : 0 < ξp) (h3 : 0 < θw) (h4 : 0 < φ)
    (h5 : 0 < ξw) : 0 < lamW θp ξp θw φ ξw := by
  unfold lamW; positivity

/-- Woodford (2003), eq. (2.36), p. 573: the two inflation weights sum to one, `λp + λw = 1`
(consistent with the printed `.9960 + .0040 = 1`). -/
theorem lamP_add_lamW {θp ξp θw φ ξw : ℝ} (h1 : 0 < θp) (h2 : 0 < ξp) (h3 : 0 < θw)
    (h4 : 0 < φ) (h5 : 0 < ξw) : lamP θp ξp θw φ ξw + lamW θp ξp θw φ ξw = 1 := by
  unfold lamP lamW
  have : 0 < θp * ξp⁻¹ + θw * φ⁻¹ * ξw⁻¹ := by positivity
  rw [← add_div, div_self this.ne']

/-- Woodford (2003), eq. (2.38), p. 573: `κ > 0`. -/
theorem kappaGW_pos {ξp η vphi δ : ℝ} (h1 : 0 < ξp) (h2 : 0 < η) (h3 : 0 < vphi) (h4 : 0 < δ) :
    0 < kappaGW ξp η vphi δ := by
  unfold kappaGW; positivity

/-- Woodford (2003), eq. (2.37), p. 573: `λx > 0`. -/
theorem lamX_pos {θp ξp θw φ ξw κ : ℝ} (h1 : 0 < θp) (h2 : 0 < ξp) (h3 : 0 < θw) (h4 : 0 < φ)
    (h5 : 0 < ξw) (h6 : 0 < κ) : 0 < lamX θp ξp θw φ ξw κ := by
  unfold lamX
  have := lamP_pos h1 h2 h3 h4 h5
  positivity

/-! ### The habit coefficient `δ`: the smaller root of (2.39) -/

/-- Woodford (2003), eq. (2.39), p. 573: `ηϕ(1 + βδ²) − [ω + ϕ(1 + βη²)]δ`; (2.39) says this
vanishes. -/
def deltaPoly (η vphi ω β x : ℝ) : ℝ :=
  η * vphi * (1 + β * x ^ 2) - (ω + vphi * (1 + β * η ^ 2)) * x

/-- Woodford (2003), p. 573: the coefficient `B = ω + ϕ(1 + βη²)` of (2.39). -/
def coefB (η vphi ω β : ℝ) : ℝ := ω + vphi * (1 + β * η ^ 2)

/-- Woodford (2003), p. 573: the discriminant `B² − 4β(ηϕ)²` of (2.39). -/
def discGW (η vphi ω β : ℝ) : ℝ := coefB η vphi ω β ^ 2 - 4 * β * (η * vphi) ^ 2

/-- Woodford (2003), eq. (2.39), p. 573: the smaller root `δ = (B − √(B² − 4β(ηϕ)²))/(2βηϕ)`. -/
noncomputable def deltaGW (η vphi ω β : ℝ) : ℝ :=
  (coefB η vphi ω β - Real.sqrt (discGW η vphi ω β)) / (2 * β * η * vphi)

/-- Woodford (2003), p. 573: the larger root `(B + √(B² − 4β(ηϕ)²))/(2βηϕ)` of (2.39). -/
noncomputable def deltaBig (η vphi ω β : ℝ) : ℝ :=
  (coefB η vphi ω β + Real.sqrt (discGW η vphi ω β)) / (2 * β * η * vphi)

/-- Woodford (2003), p. 573: for `η, ϕ, ω, β > 0` the discriminant of (2.39) is positive. -/
theorem discGW_pos {η vphi ω β : ℝ} (hη : 0 < η) (hv : 0 < vphi) (hω : 0 < ω) (hβ : 0 < β) :
    0 < discGW η vphi ω β := by
  unfold discGW coefB
  have h1 : 0 < vphi * (1 + β * η ^ 2) := by positivity
  have h2 : 4 * β * (η * vphi) ^ 2 ≤ (vphi * (1 + β * η ^ 2)) ^ 2 := by
    nlinarith [sq_nonneg (vphi * (1 - β * η ^ 2)), sq_nonneg vphi]
  nlinarith

/-- Woodford (2003), p. 573: `√D < B`, so both roots of (2.39) are positive. -/
theorem sqrt_lt_coefB {η vphi ω β : ℝ} (hη : 0 < η) (hv : 0 < vphi) (hω : 0 < ω) (hβ : 0 < β) :
    Real.sqrt (discGW η vphi ω β) < coefB η vphi ω β := by
  have hB : 0 < coefB η vphi ω β := by unfold coefB; positivity
  rw [Real.sqrt_lt' hB]
  unfold discGW
  have : 0 < 4 * β * (η * vphi) ^ 2 := by positivity
  linarith

/-- Woodford (2003), p. 573 (Vieta): the roots of (2.39) multiply to `β⁻¹`. -/
theorem deltaGW_mul_deltaBig {η vphi ω β : ℝ} (hη : 0 < η) (hv : 0 < vphi) (hω : 0 < ω)
    (hβ : 0 < β) : deltaGW η vphi ω β * deltaBig η vphi ω β = β⁻¹ := by
  have h := Real.sq_sqrt (discGW_pos hη hv hω hβ).le
  unfold deltaGW deltaBig
  rw [div_mul_div_comm]
  set sq := Real.sqrt (discGW η vphi ω β) with hsq
  have hm : (coefB η vphi ω β - sq) * (coefB η vphi ω β + sq) = 4 * β * (η * vphi) ^ 2 := by
    unfold discGW at h
    linear_combination (-1 : ℝ) * h
  rw [hm]
  field_simp
  ring

/-- Woodford (2003), p. 573 (Vieta): the roots of (2.39) add up to `B/(βηϕ)`. -/
theorem deltaGW_add_deltaBig (η vphi ω β : ℝ) :
    deltaGW η vphi ω β + deltaBig η vphi ω β = coefB η vphi ω β / (β * η * vphi) := by
  unfold deltaGW deltaBig
  by_cases h : β * η * vphi = 0
  · have h2 : 2 * β * η * vphi = 0 := by linear_combination 2 * h
    simp [h, h2]
  · field_simp
    ring

/-- Woodford (2003), p. 573: the factorisation
`βηϕδ² − Bδ + ηϕ = βηϕ(δ − δ₁)(δ − δ₂)` of the polynomial in (2.39). -/
theorem deltaPoly_factor {η vphi ω β : ℝ} (hη : 0 < η) (hv : 0 < vphi) (hω : 0 < ω)
    (hβ : 0 < β) (x : ℝ) :
    deltaPoly η vphi ω β x =
      β * η * vphi * (x - deltaGW η vphi ω β) * (x - deltaBig η vphi ω β) := by
  have hs := deltaGW_add_deltaBig η vphi ω β
  have hp := deltaGW_mul_deltaBig hη hv hω hβ
  have hne : β * η * vphi ≠ 0 := by positivity
  have e : β * η * vphi * (x - deltaGW η vphi ω β) * (x - deltaBig η vphi ω β) =
      β * η * vphi * x ^ 2 - β * η * vphi * (deltaGW η vphi ω β + deltaBig η vphi ω β) * x +
        β * η * vphi * (deltaGW η vphi ω β * deltaBig η vphi ω β) := by ring
  rw [e, hs, hp, deltaPoly]
  unfold coefB
  field_simp
  ring

/-- Woodford (2003), eq. (2.39), p. 573: `δ` solves (2.39). -/
theorem deltaPoly_deltaGW {η vphi ω β : ℝ} (hη : 0 < η) (hv : 0 < vphi) (hω : 0 < ω)
    (hβ : 0 < β) : deltaPoly η vphi ω β (deltaGW η vphi ω β) = 0 := by
  rw [deltaPoly_factor hη hv hω hβ]; ring

/-- Woodford (2003), p. 573: `δ > 0`. -/
theorem deltaGW_pos {η vphi ω β : ℝ} (hη : 0 < η) (hv : 0 < vphi) (hω : 0 < ω) (hβ : 0 < β) :
    0 < deltaGW η vphi ω β := by
  unfold deltaGW
  have := sqrt_lt_coefB hη hv hω hβ
  apply div_pos (by linarith); positivity

/-- Woodford (2003), p. 573: `δ < δ₂`. -/
theorem deltaGW_lt_deltaBig {η vphi ω β : ℝ} (hη : 0 < η) (hv : 0 < vphi) (hω : 0 < ω)
    (hβ : 0 < β) : deltaGW η vphi ω β < deltaBig η vphi ω β := by
  unfold deltaGW deltaBig
  have := Real.sqrt_pos.mpr (discGW_pos hη hv hω hβ)
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

/-- Woodford (2003), p. 573: the polynomial of (2.39) is negative exactly between its roots. -/
theorem deltaPoly_neg_iff {η vphi ω β : ℝ} (hη : 0 < η) (hv : 0 < vphi) (hω : 0 < ω)
    (hβ : 0 < β) (x : ℝ) :
    deltaPoly η vphi ω β x < 0 ↔ deltaGW η vphi ω β < x ∧ x < deltaBig η vphi ω β := by
  rw [deltaPoly_factor hη hv hω hβ]
  have hlt := deltaGW_lt_deltaBig hη hv hω hβ
  have hc : 0 < β * η * vphi := by positivity
  constructor
  · intro h
    by_contra hn
    rcases not_and_or.1 hn with h1 | h1 <;> push Not at h1
    · have : 0 ≤ β * η * vphi * (x - deltaGW η vphi ω β) * (x - deltaBig η vphi ω β) :=
        mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith))
          (by linarith)
      linarith
    · have : 0 ≤ β * η * vphi * (x - deltaGW η vphi ω β) * (x - deltaBig η vphi ω β) :=
        mul_nonneg (mul_nonneg hc.le (by linarith)) (by linarith)
      linarith
  · rintro ⟨h1, h2⟩
    exact mul_neg_of_pos_of_neg (mul_pos hc (by linarith)) (by linarith)

/-- Woodford (2003), p. 573: `deltaPoly(η) = −ωη < 0`. -/
theorem deltaPoly_eta (η vphi ω β : ℝ) : deltaPoly η vphi ω β η = -(ω * η) := by
  unfold deltaPoly; ring

/-- Woodford (2003), p. 573: `δ < η` (in fact `0 < δ < η < δ₂`; the book's `0 ≤ δ ≤ η` holds
strictly when `ω > 0`). -/
theorem deltaGW_lt_eta {η vphi ω β : ℝ} (hη : 0 < η) (hv : 0 < vphi) (hω : 0 < ω)
    (hβ : 0 < β) : deltaGW η vphi ω β < η ∧ η < deltaBig η vphi ω β :=
  (deltaPoly_neg_iff hη hv hω hβ η).mp (by rw [deltaPoly_eta]; nlinarith)

/-- Woodford (2003), p. 573: `η < δ₂`, so `δ` is the only root of (2.39) in `[0, η]`: any `r` with
`0 ≤ r ≤ η` and `deltaPoly r = 0` equals `δ`. -/
theorem deltaGW_unique {η vphi ω β r : ℝ} (hη : 0 < η) (hv : 0 < vphi) (hω : 0 < ω)
    (hβ : 0 < β) (hr : r ≤ η) (h : deltaPoly η vphi ω β r = 0) : r = deltaGW η vphi ω β := by
  rw [deltaPoly_factor hη hv hω hβ] at h
  have hne : β * η * vphi ≠ 0 := by positivity
  rcases mul_eq_zero.mp h with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hne
    · exact sub_eq_zero.mp h2
  · have := (deltaGW_lt_eta hη hv hω hβ).2
    have := sub_eq_zero.mp h1
    linarith

/-- Woodford (2003), p. 568 and p. 574: `δ` is strictly decreasing in `ω` ("the greater the
relative importance of the increasing marginal disutility of supplying output, … the smaller the
value of δ"). -/
theorem deltaGW_strictAnti_omega {η vphi β ω₁ ω₂ : ℝ} (hη : 0 < η) (hv : 0 < vphi) (hβ : 0 < β)
    (h₁ : 0 < ω₁) (h₁₂ : ω₁ < ω₂) : deltaGW η vphi ω₂ β < deltaGW η vphi ω₁ β := by
  have h₂ : 0 < ω₂ := by linarith
  set d₁ := deltaGW η vphi ω₁ β
  have hd₁ := deltaPoly_deltaGW hη hv h₁ hβ
  have hpos := deltaGW_pos hη hv h₁ hβ
  have hneg : deltaPoly η vphi ω₂ β d₁ < 0 := by
    have : deltaPoly η vphi ω₂ β d₁ = deltaPoly η vphi ω₁ β d₁ - (ω₂ - ω₁) * d₁ := by
      unfold deltaPoly; ring
    rw [this, hd₁]
    nlinarith
  exact ((deltaPoly_neg_iff hη hv h₂ hβ d₁).mp hneg).1

/-- Woodford (2003), p. 568: `δ` is strictly increasing in the habit parameter `η` on `(0, 1]`. -/
theorem deltaGW_strictMono_eta {vphi ω β η₁ η₂ : ℝ} (hv : 0 < vphi) (hω : 0 < ω) (hβ : 0 < β)
    (hβ1 : β < 1) (h₁ : 0 < η₁) (h₁₂ : η₁ < η₂) (h₂1 : η₂ ≤ 1) :
    deltaGW η₁ vphi ω β < deltaGW η₂ vphi ω β := by
  have h₂ : 0 < η₂ := by linarith
  set d₁ := deltaGW η₁ vphi ω β
  have hd₁ := deltaPoly_deltaGW h₁ hv hω hβ
  have hpos := deltaGW_pos h₁ hv hω hβ
  have hlt := (deltaGW_lt_eta h₁ hv hω hβ).1
  have key : η₁ * deltaPoly η₂ vphi ω β d₁ =
      d₁ * (η₂ - η₁) * ((ω + vphi) - vphi * β * η₁ * η₂) := by
    unfold deltaPoly at hd₁ ⊢
    linear_combination η₂ * hd₁
  have hprod : η₁ * η₂ < 1 := by nlinarith
  have hfac : 0 < (ω + vphi) - vphi * β * η₁ * η₂ := by
    have : vphi * β * (η₁ * η₂) < vphi := by
      have hb : β * (η₁ * η₂) < 1 := by nlinarith [mul_pos h₁ h₂]
      nlinarith
    nlinarith
  have hposP : 0 < deltaPoly η₂ vphi ω β d₁ := by
    have : 0 < η₁ * deltaPoly η₂ vphi ω β d₁ := by
      rw [key]; exact mul_pos (mul_pos hpos (by linarith)) hfac
    exact pos_of_mul_pos_right this h₁.le
  by_contra hcon
  push Not at hcon
  rcases eq_or_lt_of_le hcon with heq | hlt'
  · rw [← heq, deltaPoly_deltaGW h₂ hv hω hβ] at hposP
    exact lt_irrefl _ hposP
  · have hbig := (deltaGW_lt_eta h₂ hv hω hβ).2
    have : deltaPoly η₂ vphi ω β d₁ < 0 :=
      (deltaPoly_neg_iff h₂ hv hω hβ d₁).mpr ⟨hlt', by linarith⟩
    linarith

/-! ### The numbers on p. 574 (Table 5.3 of Chapter 5) -/

/-- Woodford (2003), Table 5.3, p. 350, and (2.36), p. 573: with `(θp − 1)⁻¹ = 0.004`,
`(θw − 1)⁻¹ = 0.54`, `φ⁻¹ = 0.75`, `ξp = 0.0020`, `ξw = 0.0042` taken as exact,
`λp = 13554/13609 ∈ (0.99595, 0.99596)`, which prints as `.9960`. -/
theorem lamP_table :
    lamP (1 + 1 / 0.004) 0.002 (1 + 1 / 0.54) (1 / 0.75) 0.0042 = 13554 / 13609 ∧
      (0.99595 : ℝ) < 13554 / 13609 ∧ (13554 / 13609 : ℝ) < 0.99596 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  unfold lamP
  norm_num

/-- Woodford (2003), Table 5.3 and (2.36): `λw = 55/13609 ∈ (0.00404, 0.00405)`, which prints as
`.0040`. -/
theorem lamW_table :
    lamW (1 + 1 / 0.004) 0.002 (1 + 1 / 0.54) (1 / 0.75) 0.0042 = 55 / 13609 ∧
      (0.00404 : ℝ) < 55 / 13609 ∧ (55 / 13609 : ℝ) < 0.00405 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  unfold lamW
  norm_num

/-- Woodford (2003), Table 5.3 and (2.39), p. 574: with `η = 1`, `ϕ = 0.75`, `β = 0.99` and
`ω = ωw + ωp = 19.6 + 0.33` (Ch. 5, p. 355), `0.03505 < δ < 0.03506`, which prints as `.035`. -/
theorem deltaGW_table :
    (0.03505 : ℝ) < deltaGW 1 0.75 (19.6 + 0.33) 0.99 ∧
      deltaGW 1 0.75 (19.6 + 0.33) 0.99 < 0.03506 := by
  have hη : (0 : ℝ) < 1 := one_pos
  have hv : (0 : ℝ) < 0.75 := by norm_num
  have hω : (0 : ℝ) < 19.6 + 0.33 := by norm_num
  have hβ : (0 : ℝ) < 0.99 := by norm_num
  have hlt := deltaGW_lt_eta hη hv hω hβ
  constructor
  · -- `deltaPoly(0.03505) > 0` and `0.03505 < η < δ₂`, so `0.03505 < δ`
    by_contra h
    push Not at h
    have hp : deltaPoly 1 0.75 (19.6 + 0.33) 0.99 0.03505 < 0 := by
      rcases eq_or_lt_of_le h with h' | h'
      · exfalso
        have := deltaPoly_deltaGW hη hv hω hβ
        rw [h'] at this
        norm_num [deltaPoly] at this
      · exact (deltaPoly_neg_iff hη hv hω hβ _).mpr ⟨h', by linarith [hlt.2]⟩
    norm_num [deltaPoly] at hp
  · have hp : deltaPoly 1 0.75 (19.6 + 0.33) 0.99 0.03506 < 0 := by norm_num [deltaPoly]
    exact ((deltaPoly_neg_iff hη hv hω hβ _).mp hp).1

/-- Woodford (2003), (2.37)–(2.38), p. 574 (**the printed `λx = 0.0026` checked**): with the
Table 5.3 values taken as exact, `λx = λp ξp η ϕ / (δ θp)` lies in `(0.0001697, 0.0001699)` in the
model's units (quarterly inflation), and `16 λx ∈ (0.002716, 0.002718)` when inflation is measured
at annual rates (cf. footnote 31). Neither equals the printed `0.0026` to the printed precision. -/
theorem lamX_table :
    let δ := deltaGW 1 0.75 (19.6 + 0.33) 0.99
    let lx := lamX (1 + 1 / 0.004) 0.002 (1 + 1 / 0.54) (1 / 0.75) 0.0042
      (kappaGW 0.002 1 0.75 δ)
    (0.0001697 : ℝ) < lx ∧ lx < 0.0001699 ∧ (0.002716 : ℝ) < 16 * lx ∧ 16 * lx < 0.002718 := by
  intro δ lx
  obtain ⟨h1, h2⟩ := deltaGW_table
  have hP := lamP_table.1
  have hδ : 0 < δ := by
    change (0 : ℝ) < deltaGW 1 0.75 (19.6 + 0.33) 0.99
    linarith
  have hlx : lx = 13554 / 13609 * (0.002 * 1 * 0.75 / δ) / (1 + 1 / 0.004) := by
    simp only [lx, lamX, kappaGW, hP]
  have hlx' : lx = (13554 / 13609 * 0.0015 / 251) / δ := by
    rw [hlx]; field_simp; norm_num
  set K : ℝ := 13554 / 13609 * 0.0015 / 251 with hK
  have hKpos : 0 < K := by norm_num [hK]
  have lo : K / 0.03506 < K / δ := div_lt_div_of_pos_left hKpos hδ h2
  have hi : K / δ < K / 0.03505 := div_lt_div_of_pos_left hKpos (by norm_num) h1
  have c1 : (0.0001697 : ℝ) < K / 0.03506 := by norm_num [hK]
  have c2 : K / 0.03505 < (0.0001699 : ℝ) := by norm_num [hK]
  have c3 : (0.002716 : ℝ) < 16 * (K / 0.03506) := by norm_num [hK]
  have c4 : 16 * (K / 0.03505) < (0.002718 : ℝ) := by norm_num [hK]
  rw [hlx']
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### (2.40): interest rates forecastable a quarter in advance -/

/-- Woodford (2003), pp. 572, 575 (**forecastability of the optimal interest rate, general form**):
consider any policy problem whose loss is `W(y) + E_{t0}∑ βᵗ(λᵢ/2)(i_t − i*)²` with `W` not
depending
on the interest-rate path, and in which replacing `i_t` by `E_{t−d} i_t` preserves feasibility
(the structural equations involve the interest rate only through forecasts made `d` or more
periods earlier). Then for `λᵢ > 0` every optimal plan has `E_{t0}(i_t − E_{t−d} i_t)² = 0` at
every date `t ≥ t0 + d`. -/
theorem forecastable_of_optimal {Y : Type*} {β lami istar : ℝ} {d t0 : ℕ} (hβ : 0 < β)
    (hβ1 : β < 1) (hlami : 0 < lami) (hPO : 𝔼.PullOut) (Feas : Y → (ℕ → Ω → ℝ) → Prop)
    (W : Y → Ω → ℝ) (hFeas : ∀ y i, Feas y i → Feas y (fcst 𝔼 d i)) {y : Y}
    {i : ℕ → Ω → ℝ} (hF : Feas y i) (hi : BoundedProc i)
    (hopt : ∀ y' i', Feas y' i' → BoundedProc i' → ∀ ω,
      W y ω + iLoss 𝔼 β lami istar d t0 i ω ≤ W y' ω + iLoss 𝔼 β lami istar d t0 i' ω)
    (n : ℕ) (ω : Ω) :
    𝔼.E t0 (fun ω' => (i (t0 + d + n) ω' - 𝔼.E (t0 + n) (i (t0 + d + n)) ω') ^ 2) ω = 0 := by
  have hfb := InflTargetPredetermined.fcst_bounded 𝔼 (d := d) hi
  have hle := hopt y (fcst 𝔼 d i) (hFeas y i hF) hfb ω
  have hdec := iLoss_decomp 𝔼 (lami := lami) (istar := istar) (d := d) (t0 := t0) hβ.le hβ1 hPO
    hi ω
  set v : ℕ → ℝ := fun m => 𝔼.E t0 (fun ω' => (i (t0 + d + m) ω'
    - fcst 𝔼 d i (t0 + d + m) ω') ^ 2) ω with hv
  have hv0 : ∀ m, 0 ≤ v m := by
    intro m
    have := 𝔼.mono t0 (show (0 : Ω → ℝ) ≤ fun ω' =>
      (i (t0 + d + m) ω' - fcst 𝔼 d i (t0 + d + m) ω') ^ 2 from fun ω' => sq_nonneg _) ω
    simpa using this
  obtain ⟨B, hB⟩ := hi
  have hvb : ∀ m, |lami / 2 * v m| ≤ lami / 2 * (B + B) ^ 2 := by
    intro m
    rw [abs_of_nonneg (mul_nonneg (by linarith) (hv0 m))]
    gcongr
    refine (le_abs_self _).trans (𝔼.abs_E_le (fun ω' => ?_) t0 ω)
    have h1 : |i (t0 + d + m) ω' - fcst 𝔼 d i (t0 + d + m) ω'| ≤ B + B :=
      (abs_sub _ _).trans (add_le_add (hB _ ω') (𝔼.abs_E_le (hB _) _ ω'))
    have := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at this
    rwa [abs_of_nonneg (sq_nonneg _)]
  have hs := summable_weighted hβ.le hβ1 (t0 + d) hvb
  have hnn : ∀ m, 0 ≤ β ^ (t0 + d + m) * (lami / 2 * v m) :=
    fun m => mul_nonneg (pow_nonneg hβ.le _) (mul_nonneg (by linarith) (hv0 m))
  have hsum0 : ∑' m, β ^ (t0 + d + m) * (lami / 2 * v m) = 0 := by
    have h0 : 0 ≤ ∑' m, β ^ (t0 + d + m) * (lami / 2 * v m) := tsum_nonneg hnn
    simp only [hv] at hdec h0 ⊢
    linarith
  have hS : HasSum (fun m => β ^ (t0 + d + m) * (lami / 2 * v m)) 0 := by
    have := hs.hasSum
    rwa [hsum0] at this
  have hz := congrFun ((hasSum_zero_iff_of_nonneg hnn).mp hS) n
  simp only [Pi.zero_apply] at hz
  have h1 := (mul_eq_zero.mp hz).resolve_left (pow_pos hβ _).ne'
  have h2 := (mul_eq_zero.mp h1).resolve_left (by positivity)
  simp only [hv, fcst, show t0 + d + n - d = t0 + n by omega] at h2
  exact h2

/-- Woodford (2003), eq. (2.40), p. 575: in the Giannoni–Woodford model wages, prices and output
are predetermined at least one quarter, so the structural equations involve the interest rate only
through forecasts made a quarter or more earlier; the loss (2.35) does not involve `i`. Hence for
any `λᵢ > 0` an optimal plan has `i_t = E_{t−1} i_t` (in mean square). -/
theorem eq240_of_optimal {Y : Type*} {β lami istar : ℝ} {t0 : ℕ} (hβ : 0 < β) (hβ1 : β < 1)
    (hlami : 0 < lami) (hPO : 𝔼.PullOut) (Feas : Y → (ℕ → Ω → ℝ) → Prop) (W : Y → Ω → ℝ)
    (hFeas : ∀ y i, Feas y i → Feas y (fcst 𝔼 1 i)) {y : Y} {i : ℕ → Ω → ℝ}
    (hF : Feas y i) (hi : BoundedProc i)
    (hopt : ∀ y' i', Feas y' i' → BoundedProc i' → ∀ ω,
      W y ω + iLoss 𝔼 β lami istar 1 t0 i ω ≤ W y' ω + iLoss 𝔼 β lami istar 1 t0 i' ω)
    (n : ℕ) (ω : Ω) :
    𝔼.E t0 (fun ω' => (i (t0 + 1 + n) ω' - 𝔼.E (t0 + 1 + n - 1) (i (t0 + 1 + n)) ω') ^ 2) ω
      = 0 := by
  rw [show t0 + 1 + n - 1 = t0 + n by omega]
  exact forecastable_of_optimal 𝔼 hβ hβ1 hlami hPO Feas W hFeas hF hi hopt n ω

/-- Woodford (2003), Ch. 5, eq. (2.4), p. 348: the Giannoni–Woodford IS relation for the
predictable component, `E_{t−2} x̃_t = E_{t−2} x̃_{t+1} − ϕ⁻¹ E_{t−2}(î_t − π_{t+1} − r̂ⁿ_t)`. -/
def gwIS (vphi : ℝ) (rn π xt i : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  𝔼.E (t - 2) (xt t) = 𝔼.E (t - 2) (xt (t + 1)) - vphi⁻¹ • 𝔼.E (t - 2) (i t - π (t + 1) - rn t)

/-- Woodford (2003), p. 575 with Ch. 5 (2.4): the IS block involves the interest rate only through
forecasts made at least a quarter in advance — it holds for `i` iff it holds for `E_{t−1} i`.
(The wage equation, Ch. 5 (2.7), also involves `i` only through `E_{t−1} µ_t`; the generalised
`µ_t` is not printed in the book.) -/
theorem gwIS_fcst_iff (vphi : ℝ) (rn π xt i : ℕ → Ω → ℝ) (t : ℕ) :
    gwIS 𝔼 vphi rn π xt i t ↔ gwIS 𝔼 vphi rn π xt (fcst 𝔼 1 i) t := by
  unfold gwIS fcst
  rw [map_sub, map_sub (𝔼.E (t - 2)) (𝔼.E (t - 1) (i t) - π (t + 1)), map_sub,
    map_sub (𝔼.E (t - 2)) (𝔼.E (t - 1) (i t)), 𝔼.tower (by omega : t - 2 ≤ t - 1)]

/-! ### The target criteria (2.41)–(2.45) -/

/-- Woodford (2003), eq. (2.42), p. 576: the weighted forecast
`F_t(z) = ∑_{k ≥ 1} α_k E_t z_{t+k}` (here `α k` is the weight on horizon `k + 1`). -/
noncomputable def Fc (α : ℕ → ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, α k * 𝔼.E t (z (t + (k + 1))) ω

/-- Woodford (2003), (2.42): with absolutely summable weights and a bounded process the series
defining `F_t(z)` converges. -/
theorem Fc_summable {α : ℕ → ℝ} (hα : Summable (fun k => |α k|)) {z : ℕ → Ω → ℝ} {M : ℝ}
    (hz : ∀ t ω, |z t ω| ≤ M) (t : ℕ) (ω : Ω) :
    Summable (fun k => α k * 𝔼.E t (z (t + (k + 1))) ω) := by
  refine Summable.of_norm_bounded (hα.mul_right M) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hz _) t ω) (abs_nonneg _)

/-- Woodford (2003), (2.42), p. 576: since the weights sum to one, adding a constant `c` to `z`
adds `c` to `F_t(z)`. -/
theorem Fc_add_const {α : ℕ → ℝ} (hα : Summable (fun k => |α k|)) (h1 : HasSum α 1)
    {z : ℕ → Ω → ℝ} (hz : BoundedProc z) (c : ℝ) (t : ℕ) :
    Fc 𝔼 α (fun s => z s + fun _ => c) t = Fc 𝔼 α z t + fun _ => c := by
  obtain ⟨M, hM⟩ := hz
  funext ω
  simp only [Fc, map_add, 𝔼.const, Pi.add_apply, mul_add]
  rw [(Fc_summable 𝔼 hα hM t ω).tsum_add (h1.summable.mul_right c), tsum_mul_right,
    h1.tsum_eq, one_mul]

/-- Woodford (2003), (2.42): `F_t(z)` is known at date `t` (`E_t` commutes with the absolutely
convergent series). -/
theorem Fc_known {α : ℕ → ℝ} (hα : Summable (fun k => |α k|)) {z : ℕ → Ω → ℝ}
    (hz : BoundedProc z) (t : ℕ) : 𝔼.E t (Fc 𝔼 α z t) = Fc 𝔼 α z t := by
  obtain ⟨M, hM⟩ := hz
  funext ω
  have hf : ∀ k ω', |α k * 𝔼.E t (z (t + (k + 1))) ω'| ≤ |α k| * M := fun k ω' => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM _) t ω') (abs_nonneg _)
  have h := ForwardSolution.E_tsum_dom 𝔼 (hα.mul_right M) hf t ω
  unfold Fc
  rw [h]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (α k • 𝔼.E t (z (t + (k + 1)))) ω = _
  rw [map_smul, 𝔼.E_E_self]
  rfl

/-- Woodford (2003), eq. (2.41), p. 576: the left-hand side `F_t(π) + φw[F_t(w) − w_t]` of the
short-run target criterion. -/
noncomputable def srLHS (απ αw : ℕ → ℝ) (φw : ℝ) (π w : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  Fc 𝔼 απ π t + φw • (Fc 𝔼 αw w t - w t)

/-- Woodford (2003), (2.41)–(2.43), p. 576: if the short-run criterion (2.41) holds with a target
`π̄_t` known at date `t − 1`, then the target is (2.43),
`π̄_t = E_{t−1}[F_t(π) + φw(F_t(w) − w_t)]`. -/
theorem eq243_of_eq241 {απ αw : ℕ → ℝ} {φw : ℝ} {π w πbar : ℕ → Ω → ℝ} {t : ℕ}
    (h41 : srLHS 𝔼 απ αw φw π w t = πbar t) (hpre : 𝔼.E (t - 1) (πbar t) = πbar t) :
    πbar t = 𝔼.E (t - 1) (srLHS 𝔼 απ αw φw π w t) := by
  rw [h41, hpre]

/-- Woodford (2003), p. 576: (2.41) with the target (2.43) holds iff the left-hand side of (2.41)
is forecastable a quarter in advance — the criterion restricts only the surprise component. -/
theorem eq241_243_iff {απ αw : ℕ → ℝ} {φw : ℝ} {π w πbar : ℕ → Ω → ℝ} {t : ℕ}
    (h43 : πbar t = 𝔼.E (t - 1) (srLHS 𝔼 απ αw φw π w t)) :
    srLHS 𝔼 απ αw φw π w t = πbar t ↔
      srLHS 𝔼 απ αw φw π w t = 𝔼.E (t - 1) (srLHS 𝔼 απ αw φw π w t) := by
  rw [h43]

/-- Woodford (2003), p. 577 and footnote 27 (**only differences matter, short-run criterion**):
with weights summing to one, adding constants to the inflation and real-wage paths leaves the
condition "the left side of (2.41) is forecastable a quarter ahead" unchanged. -/
theorem sr_invariant {απ αw : ℕ → ℝ} (hαπ : Summable (fun k => |απ k|)) (h1π : HasSum απ 1)
    (hαw : Summable (fun k => |αw k|)) (h1w : HasSum αw 1) (φw : ℝ) {π w : ℕ → Ω → ℝ}
    (hπ : BoundedProc π) (hw : BoundedProc w) (c c' : ℝ) (t : ℕ) :
    (srLHS 𝔼 απ αw φw (fun s => π s + fun _ => c) (fun s => w s + fun _ => c') t =
        𝔼.E (t - 1) (srLHS 𝔼 απ αw φw (fun s => π s + fun _ => c)
          (fun s => w s + fun _ => c') t)) ↔
      (srLHS 𝔼 απ αw φw π w t = 𝔼.E (t - 1) (srLHS 𝔼 απ αw φw π w t)) := by
  have e : srLHS 𝔼 απ αw φw (fun s => π s + fun _ => c) (fun s => w s + fun _ => c') t =
      srLHS 𝔼 απ αw φw π w t + fun _ => c := by
    unfold srLHS
    rw [Fc_add_const 𝔼 hαπ h1π hπ, Fc_add_const 𝔼 hαw h1w hw]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [e, map_add, 𝔼.const]
  constructor
  · intro h; simpa using h
  · intro h; rw [← h]

/-- Woodford (2003), eq. (2.44), p. 576: the left-hand side
`F*_t(π) + φ*w[F*_t(w) − w_t] + φ*x[F*_t(x) − x_t]` of the long-run criterion. -/
noncomputable def lrLHS (aπ aw ax : ℕ → ℝ) (φw φx : ℝ) (π w x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  Fc 𝔼 aπ π t + φw • (Fc 𝔼 aw w t - w t) + φx • (Fc 𝔼 ax x t - x t)

/-- Woodford (2003), eq. (2.45), p. 577: the target value
`π*_t = F¹_{t−1}(π) + φ*w[F¹_{t−1}(w) − w_t] + φ*x[F¹_{t−1}(x) − x_t]
  + θ*π[F¹_{t−1}(π) − F²_{t−2}(π)] + θ*w[F¹_{t−1}(w) − F²_{t−2}(w)]
  + θ*x[F¹_{t−1}(x) − F²_{t−2}(x)]`. -/
noncomputable def lrTarget (bπ bw bx cπ cw cx : ℕ → ℝ) (φw φx θπ θw θx : ℝ) (π w x : ℕ → Ω → ℝ)
    (t : ℕ) : Ω → ℝ :=
  Fc 𝔼 bπ π (t - 1) + φw • (Fc 𝔼 bw w (t - 1) - w t) + φx • (Fc 𝔼 bx x (t - 1) - x t) +
    θπ • (Fc 𝔼 bπ π (t - 1) - Fc 𝔼 cπ π (t - 2)) + θw • (Fc 𝔼 bw w (t - 1) - Fc 𝔼 cw w (t - 2)) +
    θx • (Fc 𝔼 bx x (t - 1) - Fc 𝔼 cx x (t - 2))

/-- Woodford (2003), footnote 28, p. 577: the `−φ*w w_t − φ*x x_t` terms on both sides of
(2.44)–(2.45) cancel; the criterion is equivalent to
`F*(π) + φ*w F*(w) + φ*x F*(x) = F¹(π) + φ*w F¹(w) + φ*x F¹(x) + θ-terms`. -/
theorem eq244_245_simplified (aπ aw ax bπ bw bx cπ cw cx : ℕ → ℝ) (φw φx θπ θw θx : ℝ)
    (π w x : ℕ → Ω → ℝ) (t : ℕ) :
    lrLHS 𝔼 aπ aw ax φw φx π w x t = lrTarget 𝔼 bπ bw bx cπ cw cx φw φx θπ θw θx π w x t ↔
      Fc 𝔼 aπ π t + φw • Fc 𝔼 aw w t + φx • Fc 𝔼 ax x t =
        Fc 𝔼 bπ π (t - 1) + φw • Fc 𝔼 bw w (t - 1) + φx • Fc 𝔼 bx x (t - 1) +
        θπ • (Fc 𝔼 bπ π (t - 1) - Fc 𝔼 cπ π (t - 2)) +
        θw • (Fc 𝔼 bw w (t - 1) - Fc 𝔼 cw w (t - 2)) +
        θx • (Fc 𝔼 bx x (t - 1) - Fc 𝔼 cx x (t - 2)) := by
  unfold lrLHS lrTarget
  constructor <;> intro h <;> funext ω <;> have := congrFun h ω <;>
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢ <;> linarith

/-- Woodford (2003), p. 577 (**only differences matter, long-run criterion**): when every family
of weights sums to one, adding constants to the paths of inflation, the real wage and the output
gap leaves the long-run criterion (2.44)–(2.45) unchanged. -/
theorem lr_invariant {aπ aw ax bπ bw bx cπ cw cx : ℕ → ℝ}
    (s1 : Summable (fun k => |aπ k|)) (s2 : Summable (fun k => |aw k|))
    (s3 : Summable (fun k => |ax k|)) (s4 : Summable (fun k => |bπ k|))
    (s5 : Summable (fun k => |bw k|)) (s6 : Summable (fun k => |bx k|))
    (s7 : Summable (fun k => |cπ k|)) (s8 : Summable (fun k => |cw k|))
    (s9 : Summable (fun k => |cx k|))
    (o1 : HasSum aπ 1) (o2 : HasSum aw 1) (o3 : HasSum ax 1) (o4 : HasSum bπ 1)
    (o5 : HasSum bw 1) (o6 : HasSum bx 1) (o7 : HasSum cπ 1) (o8 : HasSum cw 1)
    (o9 : HasSum cx 1) (φw φx θπ θw θx : ℝ) {π w x : ℕ → Ω → ℝ} (hπ : BoundedProc π)
    (hw : BoundedProc w) (hx : BoundedProc x) (c1 c2 c3 : ℝ) (t : ℕ) :
    (lrLHS 𝔼 aπ aw ax φw φx (fun s => π s + fun _ => c1) (fun s => w s + fun _ => c2)
        (fun s => x s + fun _ => c3) t =
      lrTarget 𝔼 bπ bw bx cπ cw cx φw φx θπ θw θx (fun s => π s + fun _ => c1)
        (fun s => w s + fun _ => c2) (fun s => x s + fun _ => c3) t) ↔
    (lrLHS 𝔼 aπ aw ax φw φx π w x t = lrTarget 𝔼 bπ bw bx cπ cw cx φw φx θπ θw θx π w x t) := by
  unfold lrLHS lrTarget
  simp only [Fc_add_const 𝔼 s1 o1 hπ, Fc_add_const 𝔼 s2 o2 hw, Fc_add_const 𝔼 s3 o3 hx,
    Fc_add_const 𝔼 s4 o4 hπ, Fc_add_const 𝔼 s5 o5 hw, Fc_add_const 𝔼 s6 o6 hx,
    Fc_add_const 𝔼 s7 o7 hπ, Fc_add_const 𝔼 s8 o8 hw, Fc_add_const 𝔼 s9 o9 hx]
  constructor <;> intro h <;> funext ω <;> have := congrFun h ω <;>
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢ <;> linarith

/-- Woodford (2003), p. 576: the long-run target `π*_t` of (2.45) is predetermined — known at
`t − 1` — when the real wage and the output gap are (as in the Giannoni–Woodford model). -/
theorem lrTarget_predetermined {bπ bw bx cπ cw cx : ℕ → ℝ} (s4 : Summable (fun k => |bπ k|))
    (s5 : Summable (fun k => |bw k|)) (s6 : Summable (fun k => |bx k|))
    (s7 : Summable (fun k => |cπ k|)) (s8 : Summable (fun k => |cw k|))
    (s9 : Summable (fun k => |cx k|)) (φw φx θπ θw θx : ℝ) {π w x : ℕ → Ω → ℝ}
    (hπ : BoundedProc π) (hw : BoundedProc w) (hx : BoundedProc x) {t : ℕ}
    (hwt : 𝔼.E (t - 1) (w t) = w t) (hxt : 𝔼.E (t - 1) (x t) = x t) :
    𝔼.E (t - 1) (lrTarget 𝔼 bπ bw bx cπ cw cx φw φx θπ θw θx π w x t) =
      lrTarget 𝔼 bπ bw bx cπ cw cx φw φx θπ θw θx π w x t := by
  have k2 : ∀ (c : ℕ → ℝ) (z : ℕ → Ω → ℝ), Summable (fun k => |c k|) → BoundedProc z →
      𝔼.E (t - 1) (Fc 𝔼 c z (t - 2)) = Fc 𝔼 c z (t - 2) := fun c z hc hz =>
    ForwardSolution.E_of_known 𝔼 (by omega) (Fc_known 𝔼 hc hz (t - 2))
  unfold lrTarget
  simp only [map_add, map_sub, map_smul, Fc_known 𝔼 s4 hπ, Fc_known 𝔼 s5 hw, Fc_known 𝔼 s6 hx,
    k2 cπ π s7 hπ, k2 cw w s8 hw, k2 cx x s9 hx, hwt, hxt]

end Woodford.OptimalPolicyRules.GWModel
