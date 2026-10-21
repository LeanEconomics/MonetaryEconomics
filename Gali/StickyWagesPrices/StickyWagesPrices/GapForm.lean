/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.Expectations
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The sticky wage and price model in gap form

Galí (2015), Chapter 6, §6.2, pp. 170–173 and §6.4.3, pp. 183–184. The price
inflation equation (6) and the wage inflation equation (15) are rewritten in
terms of the output gap `ỹ = y − yⁿ` and the real wage gap `ω̃ = ω − ωⁿ`, where
natural levels refer to the equilibrium with flexible prices AND flexible wages.

The price NKPC (6), `π^p_t = β E_t π^p_{t+1} − λ_p μ̂^p_t`, and the wage NKPC
(15), `π^w_t = β E_t π^w_{t+1} − λ_w μ̂^w_t`, are taken as model equations with
parameters `λ_p, λ_w`. All equations hold for an arbitrary `ExpectationSystem`,
so every result holds under perfect foresight and under uncertainty.

## Main results

* `psiWA_eq`, `psiWA_pos`: `ψ_wa = (1 − α ψ_ya)/(1 − α) = (σ + φ)/(σ (1 − α) + φ + α) > 0`
  for `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1` (p. 171).
* `natural_allocation_iff`: the flexible price and wage allocation, solved exactly;
  the natural real wage is (16) up to the additive constant `−α ψ_y/(1 − α)`
  (`natWage_constant_ne_zero`: the constant printed in (16) is incomplete).
* `priceMarkup_gap`, `wageMarkup_gap`: eqs. (17) and (19).
* `priceNKPC_iff_gap`, `wageNKPC_iff_gap`: (6) ⇔ (18) and (15) ⇔ (20), with
  `κ_p = α λ_p/(1 − α)` and `κ_w = λ_w (σ + φ/(1 − α))`.
* `wageGap_identity`: the identity (21).
* `euler_iff_disGap_ar1`: the Euler equation (9) is equivalent to the DIS in
  gaps (22) with `rⁿ_t = ρ − σ (1 − ρ_a) ψ_ya a_t + (1 − ρ_z) z_t`.
* `composite_nkpc`, `kappaBar_eq`: the composite NKPC (36) holds for ALL parameter
  values with slope `κ̄ = (λ_w κ_p + λ_p κ_w)/(λ_p + λ_w) = λ_p λ_w Θ_y/(λ_p + λ_w)`,
  `Θ_y = σ + (φ + α)/(1 − α)`; `kappaBar_strictly_between`: when `κ_p ≠ κ_w` the
  slope lies strictly between them, so the book's `κ` (defined only for
  `κ_p = κ_w`) is not the general slope.
* `kappa_common`: footnote 6, `κ_p = κ_w = κ ⇒ κ = λ_p λ_w Θ_y/(λ_p + λ_w)`.
-/

namespace Gali.StickyWagesPrices.GapForm

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Parameters -/

/-- Galí (2015), p. 171 (ch. 3, eq. (20)): the elasticity of natural output with
respect to technology, `ψ_ya = (1 + φ)/(σ (1 − α) + φ + α)`. -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- Galí (2015), eq. (16), p. 171: the elasticity of the natural real wage with
respect to technology, `ψ_wa = (1 − α ψ_ya)/(1 − α)`. -/
noncomputable def psiWA (σ φ α : ℝ) : ℝ := (1 - α * psiYA σ φ α) / (1 - α)

/-- Galí (2015), p. 171: the constant of natural output with flexible prices and
wages, `ψ_y = (1 − α)(log(1 − α) − μ^p − μ^w)/(σ (1 − α) + φ + α)`
(ch. 3's constant with the total markup `μ^p + μ^w`). -/
noncomputable def psiY (σ φ α μp μw : ℝ) : ℝ :=
  (1 - α) * (Real.log (1 - α) - μp - μw) / (σ * (1 - α) + φ + α)

/-- Galí (2015), p. 174 and fn. 6, p. 183: `Θ_y = σ + (φ + α)/(1 − α)`. -/
noncomputable def thetaY (σ φ α : ℝ) : ℝ := σ + (φ + α) / (1 - α)

/-- Galí (2015), eq. (18), p. 172: `κ_p = α λ_p/(1 − α)`. -/
noncomputable def kappaP (α lamP : ℝ) : ℝ := α * lamP / (1 - α)

/-- Galí (2015), eq. (20), p. 172: `κ_w = λ_w (σ + φ/(1 − α))`. -/
noncomputable def kappaW (σ φ α lamW : ℝ) : ℝ := lamW * (σ + φ / (1 - α))

/-- Galí (2015), p. 171: the denominator `σ (1 − α) + φ + α` is positive under
`σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`. -/
theorem denom_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < σ * (1 - α) + φ + α := by
  have : 0 < σ * (1 - α) := mul_pos hσ (by linarith)
  linarith

/-- Galí (2015), eq. (16), p. 171: `ψ_wa = (σ + φ)/(σ (1 − α) + φ + α)`. -/
theorem psiWA_eq {σ φ α : ℝ} (hD : σ * (1 - α) + φ + α ≠ 0) (hα1 : α ≠ 1) :
    psiWA σ φ α = (σ + φ) / (σ * (1 - α) + φ + α) := by
  have h1 : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα1)
  unfold psiWA psiYA
  field_simp
  ring

/-- Galí (2015), eq. (16), p. 171: `ψ_wa > 0` for `σ > 0`, `φ ≥ 0`,
`0 ≤ α < 1` (equivalently `α ψ_ya < 1`). -/
theorem psiWA_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < psiWA σ φ α := by
  rw [psiWA_eq (denom_pos hσ hφ hα0 hα1).ne' hα1.ne]
  exact div_pos (by linarith) (denom_pos hσ hφ hα0 hα1)

/-- Galí (2015), p. 171: `α ψ_ya < 1` under `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`. -/
theorem alpha_psiYA_lt_one {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) : α * psiYA σ φ α < 1 := by
  have h := psiWA_pos hσ hφ hα0 hα1
  unfold psiWA at h
  have h1 : 0 < 1 - α := by linarith
  have := (div_pos_iff_of_pos_right h1).mp h
  linarith

/-- Galí (2015), p. 174: `Θ_y = σ + (φ + α)/(1 − α) > 0`. -/
theorem thetaY_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < thetaY σ φ α := by
  unfold thetaY
  have : 0 ≤ (φ + α) / (1 - α) := div_nonneg (by linarith) (by linarith)
  linarith

/-- Galí (2015), eq. (18), p. 172: `κ_p ≥ 0` for `λ_p ≥ 0`, `0 ≤ α < 1`. -/
theorem kappaP_nonneg {α lamP : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hlamP : 0 ≤ lamP) :
    0 ≤ kappaP α lamP :=
  div_nonneg (mul_nonneg hα0 hlamP) (by linarith)

/-- Galí (2015), eq. (20), p. 172: `κ_w > 0` for `λ_w > 0`, `σ > 0`, `φ ≥ 0`,
`α < 1`. -/
theorem kappaW_pos {σ φ α lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα1 : α < 1) (hlamW : 0 < lamW) :
    0 < kappaW σ φ α lamW := by
  unfold kappaW
  have : 0 ≤ φ / (1 - α) := div_nonneg hφ (by linarith)
  exact mul_pos hlamW (by linarith)

/-! ### The natural allocation and the natural real wage (16) -/

/-- Galí (2015), eq. (16), p. 171: the allocation with flexible prices and
wages. With labour demand `(1 − α) n = y − a`, the price-setting condition
`ω = mpn − μ^p = log(1 − α) + (a − α n) − μ^p` and the wage-setting condition
`ω = mrs + μ^w = σ y + φ n + μ^w`, the natural allocation is unique:
`yⁿ = ψ_ya a + ψ_y`, `nⁿ = (yⁿ − a)/(1 − α)` and
`ωⁿ = log(1 − α) + ψ_wa a − μ^p − α ψ_y/(1 − α)`. -/
theorem natural_allocation_iff {σ φ α μp μw : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (a y n w : ℝ) :
    ((1 - α) * n = y - a ∧ w = Real.log (1 - α) + (a - α * n) - μp ∧
        w = σ * y + φ * n + μw) ↔
      (y = psiYA σ φ α * a + psiY σ φ α μp μw ∧ n = (y - a) / (1 - α) ∧
        w = Real.log (1 - α) + psiWA σ φ α * a - μp - α / (1 - α) * psiY σ φ α μp μw) := by
  have hD := denom_pos hσ hφ hα0 hα1
  have h1 : 1 - α ≠ 0 := by linarith
  set L := Real.log (1 - α)
  constructor
  · rintro ⟨hn, hp, hw⟩
    have hy : y * (σ * (1 - α) + φ + α) = (1 + φ) * a + (1 - α) * (L - μp - μw) := by
      linear_combination (1 - α) * (hp - hw) - (φ + α) * hn
    have hy' : y = psiYA σ φ α * a + psiY σ φ α μp μw := by
      unfold psiYA psiY
      field_simp
      linear_combination hy
    have hn' : n = (y - a) / (1 - α) := by
      field_simp
      linear_combination hn
    refine ⟨hy', hn', ?_⟩
    rw [hp, hn']
    rw [hy']
    unfold psiWA psiYA
    field_simp
    ring
  · rintro ⟨hy, hn, hw⟩
    have hn' : (1 - α) * n = y - a := by
      rw [hn]
      field_simp
    refine ⟨hn', ?_, ?_⟩
    · rw [hw, hn, hy]
      unfold psiWA psiYA
      field_simp
      ring
    · rw [hw, hn, hy]
      unfold psiWA psiYA psiY
      field_simp
      ring

/-- Galí (2015), eq. (16), p. 171 (correction): the printed second line
`ωⁿ = log(1 − α) + ψ_wa a − μ^p` omits the constant `−α ψ_y/(1 − α)`. It is
nonzero in general: at `α = 1/2`, `σ = φ = 1`, `μ^p = μ^w = 0` it equals
`−log(1/2)/4 ≠ 0`. (The omission is harmless for the dynamics: only `Δωⁿ` and
deviations enter (21)–(24).) -/
theorem natWage_constant_ne_zero :
    (1 / 2 : ℝ) / (1 - 1 / 2) * psiY 1 1 (1 / 2) 0 0 ≠ 0 := by
  unfold psiY
  have hlog : Real.log (1 - 1 / 2 : ℝ) ≠ 0 := by
    have : Real.log (1 - 1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
    exact this.ne
  have : (1 - 1 / 2 : ℝ) * (Real.log (1 - 1 / 2) - 0 - 0) / (1 * (1 - 1 / 2) + 1 + 1 / 2) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (by simpa using hlog)) (by norm_num)
  exact mul_ne_zero (by norm_num) this

/-! ### Markups in gap form: (17) and (19) -/

/-- Galí (2015), eq. (17), p. 172: with labour demand `(1 − α) n = y − a` (also at
the natural allocation) and the natural real wage (16) in its first form
`ωⁿ = log(1 − α) + (a − α nⁿ) − μ^p`, the price markup gap
`μ̂^p = (mpn − ω) − μ^p` equals `−α/(1 − α) ỹ − ω̃`. -/
theorem priceMarkup_gap {α L a y yn n nn w wn μp : ℝ} (hα1 : α ≠ 1)
    (hn : (1 - α) * n = y - a) (hnn : (1 - α) * nn = yn - a)
    (hwn : wn = L + (a - α * nn) - μp) :
    (L + (a - α * n) - w) - μp = -(α / (1 - α)) * (y - yn) - (w - wn) := by
  have h1 : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα1)
  have hy : y - yn = (1 - α) * (n - nn) := by linear_combination -hn + hnn
  have hq : α / (1 - α) * (y - yn) = α * (n - nn) := by
    rw [hy]
    field_simp
  rw [neg_mul, hq, hwn]
  ring

/-- Galí (2015), eq. (19), p. 172: with `mrs = σ y + φ n`, labour demand
`(1 − α) n = y − a` (also at the natural allocation) and the natural real wage
`ωⁿ = σ yⁿ + φ nⁿ + μ^w`, the wage markup gap `μ̂^w = (ω − mrs) − μ^w` equals
`ω̃ − (σ + φ/(1 − α)) ỹ`. -/
theorem wageMarkup_gap {σ φ α a y yn n nn w wn μw : ℝ} (hα1 : α ≠ 1)
    (hn : (1 - α) * n = y - a) (hnn : (1 - α) * nn = yn - a)
    (hwn : wn = σ * yn + φ * nn + μw) :
    (w - (σ * y + φ * n)) - μw = (w - wn) - (σ + φ / (1 - α)) * (y - yn) := by
  have h1 : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα1)
  have hy : y - yn = (1 - α) * (n - nn) := by linear_combination -hn + hnn
  have hq : φ / (1 - α) * (y - yn) = φ * (n - nn) := by
    rw [hy]
    field_simp
  rw [add_mul, hq, hwn]
  ring

/-! ### Inflation equations in gap form: (18) and (20) -/

/-- Galí (2015), eq. (6), p. 165: the price NKPC
`π^p_t = β E_t π^p_{t+1} − λ_p μ̂^p_t`. -/
def PriceNKPC (β lamP : ℝ) (pp muP : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pp t = β • 𝔼.E t (pp (t + 1)) - lamP • muP t

/-- Galí (2015), eq. (15), p. 170: the wage NKPC
`π^w_t = β E_t π^w_{t+1} − λ_w μ̂^w_t`. -/
def WageNKPC (β lamW : ℝ) (pw muW : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) - lamW • muW t

/-- Galí (2015), eq. (18), p. 172: price inflation in gaps,
`π^p_t = β E_t π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`. -/
def PriceGapNKPC (β κp lamP : ℝ) (pp ygap wgap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pp t = β • 𝔼.E t (pp (t + 1)) + κp • ygap t + lamP • wgap t

/-- Galí (2015), eq. (20), p. 172: wage inflation in gaps,
`π^w_t = β E_t π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`. -/
def WageGapNKPC (β κw lamW : ℝ) (pw ygap wgap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) + κw • ygap t - lamW • wgap t

/-- Galí (2015), eqs. (6), (17), (18), p. 172: given the markup relation (17)
`μ̂^p_t = −α/(1 − α) ỹ_t − ω̃_t` at every date, the price NKPC (6) is equivalent
to (18) with `κ_p = α λ_p/(1 − α)`. -/
theorem priceNKPC_iff_gap {α β lamP : ℝ} {pp muP ygap wgap : ℕ → Ω → ℝ}
    (hmu : ∀ t, muP t = -(α / (1 - α)) • ygap t - wgap t) :
    PriceNKPC 𝔼 β lamP pp muP ↔ PriceGapNKPC 𝔼 β (kappaP α lamP) lamP pp ygap wgap := by
  unfold PriceNKPC PriceGapNKPC kappaP
  constructor
  · intro h t
    rw [h t, hmu t]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro h t
    rw [h t, hmu t]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Galí (2015), eqs. (15), (19), (20), p. 172: given the markup relation (19)
`μ̂^w_t = ω̃_t − (σ + φ/(1 − α)) ỹ_t` at every date, the wage NKPC (15) is
equivalent to (20) with `κ_w = λ_w (σ + φ/(1 − α))`. -/
theorem wageNKPC_iff_gap {σ φ α β lamW : ℝ} {pw muW ygap wgap : ℕ → Ω → ℝ}
    (hmu : ∀ t, muW t = wgap t - (σ + φ / (1 - α)) • ygap t) :
    WageNKPC 𝔼 β lamW pw muW ↔ WageGapNKPC 𝔼 β (kappaW σ φ α lamW) lamW pw ygap wgap := by
  unfold WageNKPC WageGapNKPC kappaW
  constructor
  · intro h t
    rw [h t, hmu t]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro h t
    rw [h t, hmu t]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Galí (2015), eqs. (6), (17), (18), p. 172, from the levels: if at every date
labour demand holds (`(1 − α) n = y − a`, also at the natural allocation), the
natural real wage is (16) in its first form and the price markup gap is
`μ̂^p = (mpn − ω) − μ^p` with `mpn = log(1 − α) + a − α n`, then (6) is equivalent
to (18). -/
theorem priceNKPC_iff_gap_of_levels {α β lamP μp : ℝ} (hα1 : α ≠ 1)
    {pp muP a y yn n nn w wn : ℕ → Ω → ℝ}
    (hn : ∀ t, (1 - α) • n t = y t - a t) (hnn : ∀ t, (1 - α) • nn t = yn t - a t)
    (hwn : ∀ t, wn t = (fun _ => Real.log (1 - α)) + (a t - α • nn t) - fun _ => μp)
    (hmu : ∀ t, muP t = ((fun _ => Real.log (1 - α)) + (a t - α • n t) - w t) - fun _ => μp) :
    PriceNKPC 𝔼 β lamP pp muP ↔
      PriceGapNKPC 𝔼 β (kappaP α lamP) lamP pp (fun t => y t - yn t) (fun t => w t - wn t) := by
  apply priceNKPC_iff_gap
  intro t
  rw [hmu t]
  funext x
  have e1 := congrFun (hn t) x
  have e2 := congrFun (hnn t) x
  have e3 := congrFun (hwn t) x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
  exact priceMarkup_gap hα1 e1 e2 e3

/-- Galí (2015), eqs. (15), (19), (20), p. 172, from the levels: if at every date
labour demand holds (also at the natural allocation), the natural real wage is
`ωⁿ = σ yⁿ + φ nⁿ + μ^w` and the wage markup gap is `μ̂^w = (ω − mrs) − μ^w` with
`mrs = σ y + φ n`, then (15) is equivalent to (20). -/
theorem wageNKPC_iff_gap_of_levels {σ φ α β lamW μw : ℝ} (hα1 : α ≠ 1)
    {pw muW a y yn n nn w wn : ℕ → Ω → ℝ}
    (hn : ∀ t, (1 - α) • n t = y t - a t) (hnn : ∀ t, (1 - α) • nn t = yn t - a t)
    (hwn : ∀ t, wn t = σ • yn t + φ • nn t + fun _ => μw)
    (hmu : ∀ t, muW t = (w t - (σ • y t + φ • n t)) - fun _ => μw) :
    WageNKPC 𝔼 β lamW pw muW ↔
      WageGapNKPC 𝔼 β (kappaW σ φ α lamW) lamW pw (fun t => y t - yn t) (fun t => w t - wn t) := by
  apply wageNKPC_iff_gap
  intro t
  rw [hmu t]
  funext x
  have e1 := congrFun (hn t) x
  have e2 := congrFun (hnn t) x
  have e3 := congrFun (hwn t) x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
  exact wageMarkup_gap hα1 e1 e2 e3

/-! ### The real wage gap identity (21) -/

/-- Galí (2015), eq. (21), p. 172: with `ω_t = w_t − p_t`, `π^w_t = w_t − w_{t−1}`,
`π^p_t = p_t − p_{t−1}`, `ω̃_t = ω_t − ωⁿ_t` and `Δωⁿ_t = ωⁿ_t − ωⁿ_{t−1}`, the
real wage gap satisfies `ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`. -/
theorem wageGap_identity (wlev plev wn : ℕ → Ω → ℝ) (t : ℕ) :
    (wlev (t + 1) - plev (t + 1)) - wn (t + 1)
      = ((wlev t - plev t) - wn t) + (wlev (t + 1) - wlev t) - (plev (t + 1) - plev t)
        - (wn (t + 1) - wn t) := by
  abel

/-! ### The dynamic IS equation in gaps (22)

Restated from the Chapter 3 project (`DIS.lean`): the Euler equation (9) with
the preference shock, natural output, the natural rate and the DIS in gaps. -/

/-- Galí (2015), eq. (9), p. 167, with `y = c` (p. 170): the Euler equation in
output, `y_t = E_t y_{t+1} − σ⁻¹ (i_t − E_t π^p_{t+1} − ρ) + σ⁻¹ (1 − ρ_z) z_t`. -/
def EulerOutput (σ ρ ρz : ℝ) (y i pp z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (pp (t + 1)) - fun _ => ρ)
    + (σ⁻¹ * (1 - ρz)) • z t

/-- Galí (2015), p. 171 (ch. 3, eq. (20)): natural output `yⁿ_t = ψ_ya a_t + ψ_y`. -/
def natOutput (ψya ψy : ℝ) (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => ψya • a t + fun _ => ψy

/-- Galí (2015), p. 173: the natural rate of interest, the real rate supporting
natural output in the Euler equation,
`rⁿ_t = ρ + σ (E_t yⁿ_{t+1} − yⁿ_t) + (1 − ρ_z) z_t`. -/
def natRate (σ ρ ρz : ℝ) (yn z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun _ => ρ) + σ • (𝔼.E t (yn (t + 1)) - yn t) + (1 - ρz) • z t

/-- Galí (2015), eq. (22), p. 173: the dynamic IS equation in gaps,
`ỹ_t = −σ⁻¹ (i_t − E_t π^p_{t+1} − rⁿ_t) + E_t ỹ_{t+1}`. -/
def DISGap (σ : ℝ) (ygap i pp rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = -σ⁻¹ • (i t - 𝔼.E t (pp (t + 1)) - rn t) + 𝔼.E t (ygap (t + 1))

/-- Galí (2015), p. 173: for AR(1) technology with persistence `ρ_a` and natural
output `yⁿ_t = ψ_ya a_t + ψ_y`, the natural rate is
`rⁿ_t = ρ − σ (1 − ρ_a) ψ_ya a_t + (1 − ρ_z) z_t`. -/
theorem natRate_ar1 {σ ρ ρz ρa ψya ψy : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (z : ℕ → Ω → ℝ) (t : ℕ) :
    natRate 𝔼 σ ρ ρz (natOutput ψya ψy a) z t
      = (fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t + (1 - ρz) • z t := by
  unfold natRate natOutput
  rw [map_add, map_smul, 𝔼.const, ha.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (22), p. 173: with `ỹ_t = y_t − yⁿ_t`, the Euler equation (9)
is equivalent to the DIS in gaps with the natural rate `rⁿ`. -/
theorem euler_iff_disGap {σ ρ ρz : ℝ} (hσ : σ ≠ 0) {y yn ygap i pp z : ℕ → Ω → ℝ}
    (hgap : ∀ t, ygap t = y t - yn t) :
    EulerOutput 𝔼 σ ρ ρz y i pp z ↔ DISGap 𝔼 σ ygap i pp (natRate 𝔼 σ ρ ρz yn z) := by
  unfold EulerOutput DISGap natRate
  simp only [hgap, map_sub]
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e ⊢
    linear_combination e
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e ⊢
    linear_combination e

/-- Galí (2015), eq. (22), p. 173: for AR(1) technology and natural output
`yⁿ = ψ_ya a + ψ_y`, the Euler equation (9) is equivalent to the DIS in gaps
with `rⁿ_t = ρ − σ (1 − ρ_a) ψ_ya a_t + (1 − ρ_z) z_t`. -/
theorem euler_iff_disGap_ar1 {σ ρ ρz ρa ψya ψy : ℝ} (hσ : σ ≠ 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) {y ygap i pp z : ℕ → Ω → ℝ}
    (hgap : ∀ t, ygap t = y t - natOutput ψya ψy a t) :
    EulerOutput 𝔼 σ ρ ρz y i pp z ↔ DISGap 𝔼 σ ygap i pp
      (fun t => (fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t + (1 - ρz) • z t) := by
  have hrn : natRate 𝔼 σ ρ ρz (natOutput ψya ψy a) z
      = fun t => (fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t + (1 - ρz) • z t :=
    funext (natRate_ar1 𝔼 ha z)
  rw [← hrn]
  exact euler_iff_disGap 𝔼 hσ hgap

/-! ### Composite inflation and the composite NKPC (36) -/

/-- Galí (2015), p. 184: composite inflation
`π̄_t = λ_w/(λ_p + λ_w) π^p_t + λ_p/(λ_p + λ_w) π^w_t`. -/
noncomputable def compositeInfl (lamP lamW : ℝ) (pp pw : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (lamW / (lamP + lamW)) • pp t + (lamP / (lamP + lamW)) • pw t

/-- Galí (2015), eq. (36), p. 184 (corrected): the slope of the composite NKPC,
`κ̄ = (λ_w κ_p + λ_p κ_w)/(λ_p + λ_w)`. -/
noncomputable def kappaBar (lamP lamW κp κw : ℝ) : ℝ := (lamW * κp + lamP * κw) / (lamP + lamW)

/-- Galí (2015), eq. (36), p. 184: for ANY parameter values (only `λ_p + λ_w ≠ 0`
is needed), (18) and (20) imply the composite NKPC
`π̄_t = β E_t π̄_{t+1} + κ̄ ỹ_t` with `κ̄ = (λ_w κ_p + λ_p κ_w)/(λ_p + λ_w)`. -/
theorem composite_nkpc {β κp κw lamP lamW : ℝ} (hsum : lamP + lamW ≠ 0)
    {pp pw ygap wgap : ℕ → Ω → ℝ} (h18 : PriceGapNKPC 𝔼 β κp lamP pp ygap wgap)
    (h20 : WageGapNKPC 𝔼 β κw lamW pw ygap wgap) (t : ℕ) :
    compositeInfl lamP lamW pp pw t
      = β • 𝔼.E t (compositeInfl lamP lamW pp pw (t + 1)) + kappaBar lamP lamW κp κw • ygap t := by
  unfold compositeInfl kappaBar
  rw [map_add, map_smul, map_smul, h18 t, h20 t]
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), eq. (36) and fn. 6, pp. 183–184: with `κ_p = α λ_p/(1 − α)` and
`κ_w = λ_w (σ + φ/(1 − α))`, the composite slope is
`κ̄ = λ_p λ_w Θ_y/(λ_p + λ_w)`, `Θ_y = σ + (φ + α)/(1 − α)`, for all parameters. -/
theorem kappaBar_eq (σ φ α lamP lamW : ℝ) :
    kappaBar lamP lamW (kappaP α lamP) (kappaW σ φ α lamW)
      = lamP * lamW * thetaY σ φ α / (lamP + lamW) := by
  unfold kappaBar kappaP kappaW thetaY
  ring

/-- Galí (2015), eq. (36), p. 184: the composite NKPC in the model's parameters,
`π̄_t = β E_t π̄_{t+1} + λ_p λ_w Θ_y/(λ_p + λ_w) ỹ_t`, for all parameter values
with `λ_p + λ_w ≠ 0`. -/
theorem composite_nkpc_explicit {σ φ α β lamP lamW : ℝ} (hsum : lamP + lamW ≠ 0)
    {pp pw ygap wgap : ℕ → Ω → ℝ} (h18 : PriceGapNKPC 𝔼 β (kappaP α lamP) lamP pp ygap wgap)
    (h20 : WageGapNKPC 𝔼 β (kappaW σ φ α lamW) lamW pw ygap wgap) (t : ℕ) :
    compositeInfl lamP lamW pp pw t = β • 𝔼.E t (compositeInfl lamP lamW pp pw (t + 1))
      + (lamP * lamW * thetaY σ φ α / (lamP + lamW)) • ygap t := by
  rw [← kappaBar_eq]
  exact composite_nkpc 𝔼 hsum h18 h20 t

/-- Galí (2015), eq. (36), p. 184: `κ̄ > 0` for `λ_p, λ_w > 0` and the standard
restrictions `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`. -/
theorem kappaBar_pos {σ φ α lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hlamP : 0 < lamP) (hlamW : 0 < lamW) :
    0 < kappaBar lamP lamW (kappaP α lamP) (kappaW σ φ α lamW) := by
  rw [kappaBar_eq]
  exact div_pos (mul_pos (mul_pos hlamP hlamW) (thetaY_pos hσ hφ hα0 hα1)) (by linarith)

/-- Galí (2015), eq. (36), p. 184 (correction): the book writes the slope of (36)
as `κ`, which is defined (fn. 6) only when `κ_p = κ_w`. In general `κ̄` is a
weighted average of `κ_p` and `κ_w`; when `κ_p < κ_w` it lies strictly between
them, so it coincides with neither. -/
theorem kappaBar_strictly_between {lamP lamW κp κw : ℝ} (hlamP : 0 < lamP) (hlamW : 0 < lamW)
    (hκ : κp < κw) : κp < kappaBar lamP lamW κp κw ∧ kappaBar lamP lamW κp κw < κw := by
  unfold kappaBar
  have hs : 0 < lamP + lamW := by linarith
  constructor
  · rw [lt_div_iff₀ hs]
    nlinarith
  · rw [div_lt_iff₀ hs]
    nlinarith

/-- Galí (2015), fn. 6, p. 183: when `κ_p = κ_w = κ`, the common slope is
`κ = λ_p λ_w/(λ_p + λ_w) · (σ + (φ + α)/(1 − α))`; it is then also the
composite slope `κ̄` of (36). -/
theorem kappa_common {σ φ α lamP lamW κ : ℝ} (hsum : lamP + lamW ≠ 0)
    (hp : kappaP α lamP = κ) (hw : kappaW σ φ α lamW = κ) :
    κ = lamP * lamW / (lamP + lamW) * thetaY σ φ α ∧ kappaBar lamP lamW κ κ = κ := by
  have hbar : kappaBar lamP lamW κ κ = κ := by
    unfold kappaBar
    field_simp
    ring
  refine ⟨?_, hbar⟩
  have h := kappaBar_eq σ φ α lamP lamW
  rw [hp, hw, hbar] at h
  rw [h]
  ring

end Gali.StickyWagesPrices.GapForm
