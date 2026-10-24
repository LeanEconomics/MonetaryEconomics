/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OpenEconomy.Welfare

/-!
# Simple monetary policy rules for the small open economy

Galí (2015), Chapter 8, §8.5, pp. 250–252, Table 8.1 and footnotes 14–15.

## Main results

* **The regimes** (p. 250): `SDIT` (`π_H ≡ 0`), `SCIT` (`π ≡ 0`), `PEG` (`e ≡ 0`), `FDIT`
  (`i = ρ + 1.5π_H + 0.125y`), `FCIT` (`i = ρ + 1.5π + 0.125y`). `peg_rate`: under the UIP
  condition (18), a peg forces `i = i*` (p. 250).
* **Table 8.1, loss row** (pp. 251–252). `lambda_calibration` (`λ = 103/4800`, **including**
  `Θ = 1/4`), `tableLoss_eq_avgLoss44` (the row is (44) in percent of steady-state
  consumption), `tableLoss_values` (recomputed from the printed standard deviations:
  0.0559, 0.1745, 0.6037, 0.4325 against the printed .05, .17, .61, .43),
  `tableLoss_consistent` (each printed loss is attained by standard deviations that round to the
  printed ones), `tableLoss_noTheta_inconsistent` (with `λ` **without** `Θ` the FDIT loss
  would be below 0.2 for every admissible rounding, so the table uses `λ` with `Θ`),
  `tot_eq_output` (the `σ(s)` and `σ(y)` rows coincide since `s = y` here).
* **Survey error 6** (p. 251): `peg_not_most_volatile_inflation` (PEG does not have the largest
  `σ(π_H)`: FDIT and FCIT do), `peg_most_volatile_strict` (true among SDIT, SCIT, PEG),
  `peg_most_volatile_gap` (true for the output gap).
* **Survey error 7** (fn. 14): `world_output_effects`: with `σ = η = 1`, `yⁿ` (hence `ỹ`, `π_H`)
  does not depend on `y*`, but `sⁿ` has coefficient `−1` on `y*`, and `c`, the CPI under SDIT
  and `e^{DIT}` all move with `y*`.
* **Survey error 8** (fn. 15). `exchange_rate_identity` (`e = s + p_H − p* = (1−υ)s + p − p*`);
  `sdit_meanReverting`, `scit_meanReverting`, `peg_meanReverting`: under SDIT, SCIT and PEG
  the level of `e` is a fixed function of stationary variables and its response to a
  transitory shock dies out; `fdit_solution`, `fdit_unique`: the FDIT equilibrium response to
  an AR(1) technology shock (for any expectation system); `fdit_unit_root`,
  `fdit_permanent_shift`: under FDIT the
  level of `e` converges to `B a₀/(1−ρ_a) ≠ 0` after a one-time technology shock (a permanent
  shift, i.e. a unit root) while `Δe → 0`; `fcit_cumulative`: under FCIT the same accounting
  (`e_{T+1} − e_0 = φ_π(p_T − p_{−1}) + φ_y ∑ y_t`).
-/

namespace Gali.OpenEconomy.SimpleRules

open Filter Topology

/-! ### The regimes (p. 250) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 250: strict domestic inflation targeting, `π_{H,t} = 0` for all `t`. -/
def SDIT (inflH : ℕ → Ω → ℝ) : Prop := ∀ t, inflH t = 0

/-- Galí (2015), p. 250: strict CPI inflation targeting, `π_t = 0` for all `t`. -/
def SCIT (infl : ℕ → Ω → ℝ) : Prop := ∀ t, infl t = 0

/-- Galí (2015), p. 250: an exchange-rate peg, `e_t = 0` for all `t`. -/
def PEG (e : ℕ → Ω → ℝ) : Prop := ∀ t, e t = 0

/-- Galí (2015), p. 250: a Taylor-type rule `i_t = ρ + φ_π x_t + φ_y y_t` reacting to an
inflation measure `x` and to output `y`. -/
def TaylorType (rho φπ φy : ℝ) (i x y : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => rho) + φπ • x t + φy • y t

/-- Galí (2015), p. 250: FDIT, `i_t = 0.01 + 1.5 π_{H,t} + 0.125 y_t`. -/
def FDIT (i inflH y : ℕ → Ω → ℝ) : Prop := TaylorType (1 / 100) (3 / 2) (1 / 8) i inflH y

/-- Galí (2015), p. 250: FCIT, `i_t = 0.01 + 1.5 π_t + 0.125 y_t`. -/
def FCIT (i infl y : ℕ → Ω → ℝ) : Prop := TaylorType (1 / 100) (3 / 2) (1 / 8) i infl y

/-- Galí (2015), eq. (18), p. 232: uncovered interest parity
`i_t = i*_t + E_t{Δe_{t+1}}` (with `e` adapted). -/
def UIP (i istar e : ℕ → Ω → ℝ) : Prop := ∀ t, i t = istar t + (𝔼.E t (e (t + 1)) - e t)

/-- Galí (2015), p. 250: under UIP (18), a peg `e ≡ 0` "in turn requires that `i_t = i*_t`". -/
theorem peg_rate {i istar e : ℕ → Ω → ℝ} (huip : UIP 𝔼 i istar e) (hpeg : PEG e) :
    ∀ t, i t = istar t := by
  intro t
  rw [huip t, hpeg (t + 1), hpeg t, map_zero, sub_zero, add_zero]

/-! ### Table 8.1: the loss row (pp. 251–252) -/

/-- Galí (2015), p. 233 and the Ch. 3 baseline (p. 58: `β = 0.99`, `θ = 3/4`, `α = 1/4`,
`ε = 9`): `λ = (1−θ)(1−βθ)Θ/θ = 103/4800`, with `Θ = 1/4`. -/
theorem lambda_calibration :
    Supply.bigTheta (1 / 4) 9 = 1 / 4 ∧
      Welfare.lambdaH (99 / 100) (3 / 4) (1 / 4) 9 = 103 / 4800 := by
  unfold Welfare.lambdaH Supply.bigTheta
  norm_num

/-- Galí (2015), Table 8.1, p. 251: the welfare loss (44) in percent of steady-state
consumption, as a function of the standard deviations (in percent) of `ỹ` and `π_H`, at the
baseline `υ = 0.4`, `φ = 5`, `α = 1/4`, `ε = 9`, `ε/λ = 43200/103`. -/
noncomputable def tableLoss (sy sp : ℝ) : ℝ := 3 / 10 * (8 * sy ^ 2 + 43200 / 103 * sp ^ 2) / 100

/-- Galí (2015), Table 8.1 and eq. (44): `tableLoss` is `100 · 𝕍` with variances
`(sy/100)²`, `(sp/100)²` at the baseline calibration. -/
theorem tableLoss_eq_avgLoss44 (sy sp : ℝ) :
    tableLoss sy sp = 100 * Welfare.avgLoss44 (99 / 100) (3 / 4) (2 / 5) 5 (1 / 4) 9
      ((sy / 100) ^ 2) ((sp / 100) ^ 2) := by
  unfold Welfare.avgLoss44
  rw [lambda_calibration.2]
  unfold tableLoss
  ring

/-- Galí (2015), Table 8.1 (loss row recomputed): from the printed standard deviations the
losses are SDIT 0, SCIT ≈ 0.0559, PEG ≈ 0.1745, FDIT ≈ 0.6037, FCIT ≈ 0.4325 (printed: 0, .05,
.17, .61, .43). -/
theorem tableLoss_values :
    tableLoss 0 0 = 0 ∧
      (0.0558 < tableLoss 0.66 0.19 ∧ tableLoss 0.66 0.19 < 0.0559) ∧
      (0.1744 < tableLoss 0.92 0.35 ∧ tableLoss 0.92 0.35 < 0.1745) ∧
      (0.6036 < tableLoss 0.44 0.69 ∧ tableLoss 0.44 0.69 < 0.6038) ∧
      (0.4325 < tableLoss 0.62 0.58 ∧ tableLoss 0.62 0.58 < 0.4326) := by
  unfold tableLoss
  norm_num

/-- Galí (2015), Table 8.1 (**consistency with (44)**): for every regime there are standard
deviations that round (to two decimals) to the printed ones and whose loss rounds to the
printed loss: SCIT `(0.66, 0.186) ↦ 0.0540 ∈ [0.045, 0.055)`, PEG `(0.92, 0.35) ↦ 0.1745`,
FDIT `(0.44, 0.692) ↦ 0.6072 ∈ [0.605, 0.615)`, FCIT `(0.62, 0.58) ↦ 0.4325`. -/
theorem tableLoss_consistent :
    (0.045 ≤ tableLoss 0.66 0.186 ∧ tableLoss 0.66 0.186 < 0.055) ∧
      (0.165 ≤ tableLoss 0.92 0.35 ∧ tableLoss 0.92 0.35 < 0.175) ∧
      (0.605 ≤ tableLoss 0.44 0.692 ∧ tableLoss 0.44 0.692 < 0.615) ∧
      (0.425 ≤ tableLoss 0.62 0.58 ∧ tableLoss 0.62 0.58 < 0.435) := by
  unfold tableLoss
  norm_num

/-- Galí (2015), Table 8.1 with `λ` computed **without** `Θ` (`ε/λ = 10800/103`). -/
noncomputable def tableLossNoTheta (sy sp : ℝ) : ℝ :=
  3 / 10 * (8 * sy ^ 2 + 10800 / 103 * sp ^ 2) / 100

/-- Galí (2015), Table 8.1 (**the table uses `λ` with `Θ`**, p. 233): with `λ` lacking `Θ`,
every pair of standard deviations rounding to FDIT's printed `(0.44, 0.69)` gives a loss
below 0.2, far from the printed 0.61. -/
theorem tableLoss_noTheta_inconsistent {sy sp : ℝ} (hy0 : 0 ≤ sy) (hy1 : sy ≤ 0.445)
    (hp0 : 0 ≤ sp) (hp1 : sp ≤ 0.695) : tableLossNoTheta sy sp < 0.2 := by
  unfold tableLossNoTheta
  have h1 : sy ^ 2 ≤ 0.445 ^ 2 := pow_le_pow_left₀ hy0 hy1 2
  have h2 : sp ^ 2 ≤ 0.695 ^ 2 := pow_le_pow_left₀ hp0 hp1 2
  norm_num at h1 h2 ⊢
  nlinarith

/-- Galí (2015), Table 8.1 (rows `σ(y)` and `σ(s)` coincide): with `σ = η = 1`, technology
shocks only (`y* = z = 0`), eq. (27) gives `s = σ_υ(y − y*) − (1−υ)Φz = y`. -/
theorem tot_eq_output (υ y : ℝ) :
    AggregateDemand.sigmaU 1 1 υ * (y - 0) - (1 - υ) * AggregateDemand.Phi 1 1 υ * 0 = y := by
  obtain ⟨-, -, hS, -⟩ := OptimalPolicy.special_case υ 0 0 le_rfl
  rw [hS]
  ring

/-! ### Survey error 6: the volatility ranking (p. 251) -/

/-- Galí (2015), Table 8.1: `σ(π_H)` by regime, in the order SDIT, SCIT, PEG, FDIT, FCIT. -/
noncomputable def sdInflH : Fin 5 → ℝ := ![0, 0.19, 0.35, 0.69, 0.58]

/-- Galí (2015), Table 8.1: `σ(ỹ)` by regime, in the order SDIT, SCIT, PEG, FDIT, FCIT. -/
noncomputable def sdGap : Fin 5 → ℝ := ![0, 0.66, 0.92, 0.44, 0.62]

/-- Galí (2015), p. 251 (**survey error 6**): "the PEG regime is the one that amplifies …
domestic inflation volatility to the largest extent" is inconsistent with Table 8.1: FDIT
(0.69) and FCIT (0.58) have larger `σ(π_H)` than PEG (0.35). -/
theorem peg_not_most_volatile_inflation :
    ¬ (∀ r, sdInflH r ≤ sdInflH 2) ∧ sdInflH 2 < sdInflH 3 ∧ sdInflH 2 < sdInflH 4 := by
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have := h 3
    simp [sdInflH] at this
    norm_num at this
  · simp [sdInflH]; norm_num
  · simp [sdInflH]; norm_num

/-- Galí (2015), p. 251 (corrected reading): among the three strict regimes SDIT, SCIT, PEG,
PEG has the largest `σ(π_H)`. -/
theorem peg_most_volatile_strict : ∀ r : Fin 5, r.val ≤ 2 → sdInflH r ≤ sdInflH 2 := by
  intro r hr
  fin_cases r <;> simp [sdInflH] at hr ⊢ <;> norm_num

/-- Galí (2015), p. 251: PEG does have the largest output-gap volatility among all five. -/
theorem peg_most_volatile_gap : ∀ r : Fin 5, sdGap r ≤ sdGap 2 := by
  intro r
  fin_cases r <;> simp [sdGap] <;> norm_num

/-! ### Survey error 7: world output (fn. 14) -/

/-- Galí (2015), fn. 14, p. 251 (**survey error 7**): with `σ = η = 1` (and `z = 0`), natural
output `yⁿ = Γ_a a + Γ_* y*` does not depend on `y*` (so neither do `ỹ`, `π_H` under any
rule); but the natural terms of trade `sⁿ = σ_υΓ_a a + σ_υ(Γ_* − 1)y* = a − y*`, consumption
`c = (1−υ)y + υy*`, the CPI under SDIT `p = υsⁿ` and `e^{DIT} = sⁿ − p*` all move with `y*`
(for `υ > 0`): world output does affect the domestic economy. -/
theorem world_output_effects {υ φ α : ℝ} (hφ : 0 ≤ φ) (hυ : 0 < υ) (a y ystar ystar' pstar : ℝ)
    (hne : ystar ≠ ystar') :
    (Supply.GammaA 1 1 υ φ α * a + Supply.GammaStar 1 1 υ φ α * ystar
        = Supply.GammaA 1 1 υ φ α * a + Supply.GammaStar 1 1 υ φ α * ystar') ∧
      (AggregateDemand.sigmaU 1 1 υ * Supply.GammaA 1 1 υ φ α * a +
          AggregateDemand.sigmaU 1 1 υ * (Supply.GammaStar 1 1 υ φ α - 1) * ystar
        = a - ystar) ∧
      a - ystar ≠ a - ystar' ∧
      (1 - υ) * y + υ * ystar ≠ (1 - υ) * y + υ * ystar' ∧
      υ * (a - ystar) ≠ υ * (a - ystar') ∧
      (a - ystar) - pstar ≠ (a - ystar') - pstar := by
  obtain ⟨-, -, hS, hA, hst, -, -⟩ := OptimalPolicy.special_case υ φ α hφ
  refine ⟨by rw [hst]; ring, by rw [hS, hA, hst]; ring, fun h => hne (by linarith),
    fun h => hne ?_, fun h => hne ?_, fun h => hne (by linarith)⟩
  · have : υ * (ystar - ystar') = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hυ.ne'
    linarith
  · have : υ * (ystar' - ystar) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hυ.ne'
    linarith

/-! ### Survey error 8: stationarity of the nominal exchange rate (fn. 15) -/

/-- Galí (2015), eqs. (12) and (14), pp. 229–230: `e = s + p_H − p* = (1−υ)s + p − p*`. -/
theorem exchange_rate_identity {υ s e pstar pH p : ℝ} (h14 : s = e + pstar - pH)
    (h12 : p = pH + υ * s) : e = s + pH - pstar ∧ e = (1 - υ) * s + p - pstar := by
  constructor <;> linarith

/-- Galí (2015), fn. 15 (SDIT): with `p_H ≡ 0` and constant `p*`, `e_t = sⁿ_t − p*`, so the level
of `e` mean-reverts whenever the natural terms of trade do. -/
theorem sdit_meanReverting {sn e : ℕ → ℝ} {pstar : ℝ} (he : ∀ t, e t = sn t - pstar)
    (hs : Tendsto sn atTop (𝓝 0)) : Tendsto e atTop (𝓝 (-pstar)) := by
  have := hs.sub_const pstar
  simp only [zero_sub] at this
  exact this.congr fun t => (he t).symm

/-- Galí (2015), fn. 15 (SCIT): with `π ≡ 0` the CPI is constant (`p ≡ p_{−1} = 0`), so by (12)
`p_H = −υs` and `e = (1−υ)s − p*`; `e` mean-reverts whenever the terms of trade do. -/
theorem scit_meanReverting {υ pstar : ℝ} {s e p pH infl : ℕ → ℝ} (hp0 : p 0 = infl 0)
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (hscit : ∀ t, infl t = 0)
    (h14 : ∀ t, s t = e t + pstar - pH t) (h12 : ∀ t, p t = pH t + υ * s t)
    (hs : Tendsto s atTop (𝓝 0)) :
    (∀ t, e t = (1 - υ) * s t - pstar) ∧ Tendsto e atTop (𝓝 (-pstar)) := by
  have hp0' : ∀ t, p t = 0 := by
    intro t
    induction t with
    | zero => rw [hp0, hscit]
    | succ n ih => rw [hp n, ih, hscit]; ring
  have he : ∀ t, e t = (1 - υ) * s t - pstar := by
    intro t
    have := h12 t
    have := h14 t
    rw [hp0' t] at *
    linarith
  refine ⟨he, ?_⟩
  have := (hs.const_mul (1 - υ)).sub_const pstar
  simp only [mul_zero, zero_sub] at this
  exact this.congr fun t => (he t).symm

/-- Galí (2015), fn. 15 (PEG): `e ≡ 0` is trivially stationary. -/
theorem peg_meanReverting {e : ℕ → ℝ} (hpeg : ∀ t, e t = 0) : Tendsto e atTop (𝓝 0) := by
  have : e = fun _ => 0 := funext hpeg
  rw [this]
  exact tendsto_const_nhds

/-- Galí (2015), §8.5, technology shocks with `σ = η = 1`, `y* = z = 0`: the natural rate
(38) is `rⁿ_t = ρ − (1 − ρ_a)a_t` (`σ_υΓ_a = 1`) and natural output is `yⁿ = a`. -/
def natRate (rho ρa : ℝ) (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => (fun _ => rho) - (1 - ρa) • a t

/-- Galí (2015), §8.5: the FDIT response coefficient
`Λ = 1/((1 − βρ_a)(1 − ρ_a + φ_y) + κ(φ_π − ρ_a))`. -/
noncomputable def bigLambda (β κ φπ φy ρa : ℝ) : ℝ :=
  1 / ((1 - β * ρa) * (1 - ρa + φy) + κ * (φπ - ρa))

/-- Galí (2015), §8.5 (FDIT, technology shock, `σ_υ = 1`): with `g = φ_y + 1 − ρ_a`, the
output gap `ỹ = −g(1 − βρ_a)Λ a` and domestic inflation `π_H = −gκΛ a`, together with the rule
`i = ρ + φ_π π_H + φ_y(ỹ + a)` (output `y = ỹ + yⁿ = ỹ + a`), satisfy the NKPC (37) and the DIS
(29) for every expectation system, when `a` is AR(1) with persistence `ρ_a` and the
denominator of `Λ` is nonzero. -/
theorem fdit_solution {β κ φπ φy ρa rho : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hD : (1 - β * ρa) * (1 - ρa + φy) + κ * (φπ - ρa) ≠ 0) :
    OptimalPolicy.Equilibrium 𝔼 β 1 κ (natRate rho ρa a)
      (fun t => (-(φy + 1 - ρa) * (1 - β * ρa) * bigLambda β κ φπ φy ρa) • a t)
      (fun t => (-(φy + 1 - ρa) * κ * bigLambda β κ φπ φy ρa) • a t)
      (fun t => (fun _ => rho) + φπ • ((-(φy + 1 - ρa) * κ * bigLambda β κ φπ φy ρa) • a t) +
        φy • ((-(φy + 1 - ρa) * (1 - β * ρa) * bigLambda β κ φπ φy ρa) • a t + a t)) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simp only [map_smul, ha.2 t]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold bigLambda
    field_simp
    ring
  · have hLD : bigLambda β κ φπ φy ρa * ((1 - β * ρa) * (1 - ρa + φy) + κ * (φπ - ρa)) = 1 := by
      unfold bigLambda
      field_simp
    simp only [map_smul, ha.2 t, natRate]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, inv_one, one_mul]
    linear_combination (-(a t ω) * (φy + 1 - ρa)) * hLD

/-- Galí (2015), §8.5 (FDIT determinacy, eq. (41) with `σ_υ = 1`): any two equilibria under the
rule `i = ρ + φ_π π_H + φ_y(ỹ + a)` with bounded adapted output gap and domestic inflation
coincide, when `κ(φ_π − 1) + (1 − β)φ_y > 0` (at the FDIT values `φ_π = 1.5`, `φ_y = 0.125`,
for any `κ > 0`, `0 < β < 1`). -/
theorem fdit_unique {β κ φπ φy rho ρa : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h41 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    {a y₁ y₂ π₁ π₂ i₁ i₂ : ℕ → Ω → ℝ}
    (he₁ : OptimalPolicy.Equilibrium 𝔼 β 1 κ (natRate rho ρa a) y₁ π₁ i₁)
    (he₂ : OptimalPolicy.Equilibrium 𝔼 β 1 κ (natRate rho ρa a) y₂ π₂ i₂)
    (hr₁ : ∀ t, i₁ t = (fun _ => rho) + φπ • π₁ t + φy • (y₁ t + a t))
    (hr₂ : ∀ t, i₂ t = (fun _ => rho) + φπ • π₂ t + φy • (y₂ t + a t))
    (ha₁ : 𝔼.Adapted y₁) (ha₂ : 𝔼.Adapted y₂) (hb₁ : 𝔼.Adapted π₁) (hb₂ : 𝔼.Adapted π₂)
    (hB₁ : BoundedProc y₁) (hB₂ : BoundedProc y₂) (hC₁ : BoundedProc π₁)
    (hC₂ : BoundedProc π₂) : y₁ = y₂ ∧ π₁ = π₂ := by
  have heq : OptimalPolicy.Equilibrium 𝔼 β 1 κ 0 (y₁ - y₂) (π₁ - π₂) (i₁ - i₂) := by
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [Pi.sub_apply, he₁.1 t, he₂.1 t]
      simp only [Pi.sub_apply, map_sub, smul_sub]
      abel
    · rw [Pi.sub_apply, he₁.2 t, he₂.2 t]
      simp only [Pi.sub_apply, Pi.zero_apply, map_sub, smul_sub, sub_zero]
      abel
  have hr : OptimalPolicy.TaylorRule φπ φy (i₁ - i₂) 0 (π₁ - π₂) (y₁ - y₂) := by
    intro t
    simp only [Pi.sub_apply, Pi.zero_apply, hr₁ t, hr₂ t, smul_sub, smul_add]
    abel
  have hbd : ∀ {x z : ℕ → Ω → ℝ}, BoundedProc x → BoundedProc z → BoundedProc (x - z) := by
    intro x z ⟨M, hM⟩ ⟨M', hM'⟩
    refine ⟨M + M', fun t ω => ?_⟩
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM t ω) (hM' t ω))
  have had : ∀ {x z : ℕ → Ω → ℝ}, 𝔼.Adapted x → 𝔼.Adapted z → 𝔼.Adapted (x - z) := by
    intro x z hx hz t
    simp only [Pi.sub_apply, map_sub, hx t, hz t]
  obtain ⟨h1, h2, -⟩ := (OptimalPolicy.equilibrium_iff_zero 𝔼 one_pos hκ hβ0 hβ1 hφπ hφy h41
    (had ha₁ ha₂) (had hb₁ hb₂) (hbd hB₁ hB₂) (hbd hC₁ hC₂)).1 ⟨heq, hr⟩
  exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2⟩

/-- Galí (2015), §8.5 at the FDIT coefficients: `g = φ_y + 1 − ρ_a > 0`, `Λ > 0`, hence the
inflation coefficient `B = −gκΛ` is **nonzero** (negative), for `κ > 0`, `0 ≤ β < 1`,
`ρ_a < 1`. -/
theorem fdit_coeff_neg {β κ ρa : ℝ} (hκ : 0 < κ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ1 : ρa < 1) :
    -(1 / 8 + 1 - ρa) * κ * bigLambda β κ (3 / 2) (1 / 8) ρa < 0 := by
  have hb : 0 < 1 - β * ρa := by nlinarith
  have hL : 0 < bigLambda β κ (3 / 2) (1 / 8) ρa := by
    unfold bigLambda
    have : 0 < (1 - β * ρa) * (1 - ρa + 1 / 8) + κ * (3 / 2 - ρa) :=
      add_pos (mul_pos hb (by linarith)) (mul_pos hκ (by linarith))
    positivity
  have : 0 < (1 / 8 + 1 - ρa) * κ * bigLambda β κ (3 / 2) (1 / 8) ρa :=
    mul_pos (mul_pos (by linarith) hκ) hL
  linarith

/-- Galí (2015), fn. 15 (**the unit root under FDIT**, perfect foresight): after a one-time
technology shock `a_t = ρ_aᵗ a₀` (`0 ≤ ρ_a < 1`), with `π_{H,t} = B a_t`, `ỹ_t = A a_t`,
`s_t = y_t = ỹ_t + a_t` (eq. (27), `σ_υ = 1`), `p_{H,t} = ∑_{k ≤ t} π_{H,k}` (`p_{H,−1} = 0`) and
`p* = 0`, the level `e_t = s_t + p_{H,t}` converges to `B a₀/(1 − ρ_a)` — a permanent shift
(nonzero when `B a₀ ≠ 0`, `fdit_coeff_neg`) — while the depreciation `Δe_t → 0`. -/
theorem fdit_unit_root {A B ρa a0 : ℝ} (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) {e pH : ℕ → ℝ}
    (hpH : ∀ t, pH t = ∑ k ∈ Finset.range (t + 1), B * (ρa ^ k * a0))
    (he : ∀ t, e t = (A * (ρa ^ t * a0) + ρa ^ t * a0) + pH t) :
    Tendsto e atTop (𝓝 (B * a0 / (1 - ρa))) ∧
      Tendsto (fun t => e (t + 1) - e t) atTop (𝓝 0) ∧
      (B * a0 ≠ 0 → B * a0 / (1 - ρa) ≠ 0) := by
  have hg : Tendsto (fun t : ℕ => ρa ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have hsum : Tendsto (fun n => ∑ k ∈ Finset.range n, ρa ^ k) atTop (𝓝 (1 - ρa)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0 hρ1).tendsto_sum_nat
  have hp : Tendsto pH atTop (𝓝 (B * a0 / (1 - ρa))) := by
    have h1 := ((hsum.comp (tendsto_add_atTop_nat 1)).const_mul (B * a0))
    refine h1.congr' (Eventually.of_forall fun t => ?_) |>.trans ?_
    · simp only [Function.comp_apply]
      rw [hpH t, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    · rw [div_eq_mul_inv]
  have hs : Tendsto (fun t => A * (ρa ^ t * a0) + ρa ^ t * a0) atTop (𝓝 0) := by
    have := ((hg.mul_const a0).const_mul A).add (hg.mul_const a0)
    simpa using this
  have hE : Tendsto e atTop (𝓝 (B * a0 / (1 - ρa))) := by
    have := hs.add hp
    rw [zero_add] at this
    exact this.congr fun t => (he t).symm
  refine ⟨hE, ?_, fun h => div_ne_zero h (by linarith)⟩
  have := (hE.comp (tendsto_add_atTop_nat 1)).sub hE
  rw [sub_self] at this
  exact this

/-- Galí (2015), fn. 15 (**FDIT: the level of `e` shifts permanently**): at the FDIT
coefficients, with the equilibrium responses of `fdit_solution` (`B = −gκΛ`,
`A = −g(1 − βρ_a)Λ`, unique by `fdit_unique`), a one-time technology shock `a₀ ≠ 0` moves the
nominal exchange rate permanently: `e_t → B a₀/(1 − ρ_a) ≠ 0`, while `Δe_t → 0`. -/
theorem fdit_permanent_shift {β κ ρa a0 : ℝ} (hκ : 0 < κ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (ha0 : a0 ≠ 0) {e pH : ℕ → ℝ}
    (hpH : ∀ t, pH t = ∑ k ∈ Finset.range (t + 1),
      (-(1 / 8 + 1 - ρa) * κ * bigLambda β κ (3 / 2) (1 / 8) ρa) * (ρa ^ k * a0))
    (he : ∀ t, e t = ((-(1 / 8 + 1 - ρa) * (1 - β * ρa) * bigLambda β κ (3 / 2) (1 / 8) ρa) *
      (ρa ^ t * a0) + ρa ^ t * a0) + pH t) :
    Tendsto e atTop (𝓝 ((-(1 / 8 + 1 - ρa) * κ * bigLambda β κ (3 / 2) (1 / 8) ρa) * a0 /
        (1 - ρa))) ∧
      (-(1 / 8 + 1 - ρa) * κ * bigLambda β κ (3 / 2) (1 / 8) ρa) * a0 / (1 - ρa) ≠ 0 ∧
      Tendsto (fun t => e (t + 1) - e t) atTop (𝓝 0) := by
  obtain ⟨h1, h2, h3⟩ := fdit_unit_root hρ0 hρ1 hpH he
  exact ⟨h1, h3 (mul_ne_zero (fdit_coeff_neg hκ hβ0 hβ1 hρ1).ne ha0), h2⟩

/-- Galí (2015), fn. 15 (FCIT accounting, perfect foresight): if UIP holds as
`i_t = i* + e_{t+1} − e_t` with constant `i* = ρ` and the FCIT rule
`i_t = ρ + φ_π π_t + φ_y y_t` with `π_t = p_t − p_{t−1}`, then for every `T`,
`e_{T+1} − e_0 = φ_π (p_T − p_{−1}) + φ_y ∑_{t ≤ T} y_t`: the exchange rate inherits the
cumulated CPI drift, which an inflation (not price-level) target does not undo. -/
theorem fcit_cumulative {rho φπ φy : ℝ} {i e p y : ℕ → ℝ} {pinit : ℝ}
    (huip : ∀ t, i t = rho + (e (t + 1) - e t))
    (hrule0 : i 0 = rho + φπ * (p 0 - pinit) + φy * y 0)
    (hrule : ∀ t, i (t + 1) = rho + φπ * (p (t + 1) - p t) + φy * y (t + 1)) (T : ℕ) :
    e (T + 1) - e 0 = φπ * (p T - pinit) + φy * ∑ t ∈ Finset.range (T + 1), y t := by
  induction T with
  | zero =>
    have h := huip 0
    rw [hrule0] at h
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    linarith
  | succ n ih =>
    have h := huip (n + 1)
    rw [hrule n] at h
    rw [Finset.sum_range_succ]
    linarith

end Gali.OpenEconomy.SimpleRules
