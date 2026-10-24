/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.Expectations
import StickyWagesPrices.Welfare

/-!
# Limiting cases: flexible wages, flexible prices, and strict targeting

Galí (2015), Chapter 6, §6.3, p. 180.

## Flexible wages (the limiting model, survey error 7)

With flexible wages the wage markup is constant, so the real-wage gap equals the MRS gap,
`ω̃ = σ ỹ + φ ñ = (σ + φ/(1−α)) ỹ` (`flexWage_realWageGap`), and (18) becomes the Chapter 3
NKPC `π^p = β E π^p' + κ_p ỹ` with `κ_p = λ_p (σ + (φ+α)/(1−α))` (`flexWage_nkpc`). This is
stated for the **limiting model** (constant wage markup), not as a limit of (28): with
`θ_w = 0` the Calvo wage recursion leaves no wage dispersion at all
(`flexWage_no_wage_dispersion`), so the wage term of the welfare loss is absent; separately
`lambdaW_tendsto_atTop` (`λ_w → ∞` as `θ_w → 0⁺`) and `wageWeight_tendsto_zero` (the weight
`ε_w(1−α)/λ_w → 0`) give the book's limit statement. In that model `π^p = ỹ = 0` is feasible
and optimal (`flexWage_optimal`), strict price-inflation targeting forces `ỹ = 0`
(`flexWage_strictPrice_forces_zero_gap`), and under perfect foresight the optimum is unique
(`nk_zero_unique_pf`).

## Flexible prices

Symmetrically `ω̃ = −(α/(1−α)) ỹ` (`flexPrice_realWageGap`), (20) becomes
`π^w = β E π^w' + λ_w (σ + (φ+α)/(1−α)) ỹ` (`flexPrice_nkpc`), and `π^w = ỹ = 0` is optimal
(`flexPrice_optimal`); `lambdaP_tendsto_atTop`, `priceWeight_tendsto_zero`.

## Strict targeting is suboptimal with both rigidities

In the perfect-foresight model (18), (20), (21) with `ω̃_{−1} = 0` and loss (28):
* `strict_price_targeting_suboptimal`: there is a technology-shock path `Δωⁿ` (nonzero only
  at `t = 0, 1`) for which a path with `π^p ≡ 0` exists, it is **unique** among paths with
  `∑ βᵗ ỹ_t² < ∞`, and it has **strictly higher loss** than another feasible path.
* `strict_wage_targeting_suboptimal`: the same for `π^w ≡ 0`.
* `strict_price_targeting_suboptimal_model`, `strict_wage_targeting_suboptimal_model`: the
  same with the model's coefficients `κ_p = αλ_p/(1−α)`, `κ_w = λ_w(σ + φ/(1−α))` and weights
  `σ + (φ+α)/(1−α)`, `ε_p/λ_p`, `ε_w(1−α)/λ_w`, for all `θ_p, θ_w ∈ (0, 1)`.

The improving direction is an explicit two-period feasible perturbation (`dirY`, `dirP`, `dirW`,
`dirOm`); uniqueness of the strict-targeting path uses the exponential growth of the homogeneous
real-wage-gap dynamics (`growth`).
-/

namespace Gali.StickyWagesPrices.LimitingCases

open Filter Topology
open Gali.StickyWagesPrices.Welfare Gali.StickyWagesPrices.WageDispersion

/-! ### The gap equations under a general expectation system -/

/-- Galí (2015), eq. (18), p. 172: the price NKPC in gaps,
`π^p_t = β E_t π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`. -/
def PricePC {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κp lamP : ℝ) (y pp om : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t, pp t = β • 𝔼.E t (pp (t + 1)) + κp • y t + lamP • om t

/-- Galí (2015), eq. (20), p. 172: the wage NKPC in gaps,
`π^w_t = β E_t π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`. -/
def WagePC {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κw lamW : ℝ) (y pw om : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) + κw • y t - lamW • om t

/-- Galí (2015), p. 180 (and ch. 3): a New Keynesian Phillips curve
`x_t = β E_t x_{t+1} + κ ỹ_t`. -/
def NKPC {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κ : ℝ) (y x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = β • 𝔼.E t (x (t + 1)) + κ • y t

/-- Galí (2015), eq. (18), p. 172: `κ_p = α λ_p/(1 − α)`. -/
noncomputable def kappaP (α lamP : ℝ) : ℝ := α * lamP / (1 - α)

/-- Galí (2015), eq. (20), p. 172: `κ_w = λ_w (σ + φ/(1 − α))`. -/
noncomputable def kappaW (σ φ α lamW : ℝ) : ℝ := lamW * (σ + φ / (1 - α))

/-- Galí (2015), p. 180: `κ_p + λ_p (σ + φ/(1−α)) = λ_p (σ + (φ+α)/(1−α))`. -/
theorem kappaP_add {σ φ α lamP : ℝ} (hα : α ≠ 1) :
    kappaP α lamP + lamP * (σ + φ / (1 - α)) = lamP * gapCoeff σ φ α := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold kappaP gapCoeff
  field_simp
  ring

/-- Galí (2015), p. 180: `κ_w + λ_w α/(1−α) = λ_w (σ + (φ+α)/(1−α))`. -/
theorem kappaW_add {σ φ α lamW : ℝ} (hα : α ≠ 1) :
    kappaW σ φ α lamW + lamW * (α / (1 - α)) = lamW * gapCoeff σ φ α := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold kappaW gapCoeff
  field_simp
  ring

/-! ### Flexible wages (pp. 180) -/

/-- Galí (2015), p. 180: with a constant wage markup the real-wage gap equals the MRS gap,
`ω̃ = σ ỹ + φ ñ`; with `(1 − α) ñ = ỹ` (first-order employment gap) this is
`ω̃ = (σ + φ/(1−α)) ỹ`. -/
theorem flexWage_realWageGap {σ φ α y n om : ℝ} (hα : α ≠ 1) (hom : om = σ * y + φ * n)
    (hn : (1 - α) * n = y) : om = (σ + φ / (1 - α)) * y := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hn' : n = y / (1 - α) := by
    field_simp
    linarith
  rw [hom, hn']
  ring

/-- Galí (2015), p. 180 (**flexible wages**): if (18) holds and the wage markup is constant,
`ω̃_t = (σ + φ/(1−α)) ỹ_t`, then price inflation follows the Chapter 3 NKPC
`π^p_t = β E_t π^p_{t+1} + λ_p (σ + (φ+α)/(1−α)) ỹ_t`, for any expectation system. -/
theorem flexWage_nkpc {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β σ φ α lamP : ℝ} (hα : α ≠ 1)
    {y pp om : ℕ → Ω → ℝ} (hP : PricePC 𝔼 β (kappaP α lamP) lamP y pp om)
    (hom : ∀ t, om t = (σ + φ / (1 - α)) • y t) :
    NKPC 𝔼 β (lamP * gapCoeff σ φ α) y pp := by
  intro t
  rw [hP t, hom t, smul_smul, ← kappaP_add (σ := σ) (φ := φ) (lamP := lamP) hα]
  ext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), p. 180 (survey error 7): in the limiting flexible-wage model (`θ_w = 0`) the
Calvo wage cross-section has no dispersion: the recursion
`V_{t+1} = θ_w V_t + (θ_w/(1−θ_w)) (π^w_t)²` gives `V_{t+1} = 0`, so the wage term of the
welfare loss is exactly absent (rather than being the `λ_w → ∞` limit of (28)). -/
theorem flexWage_no_wage_dispersion {V q : ℕ → ℝ}
    (hrec : ∀ t, V (t + 1) = 0 * V t + 0 / (1 - 0) * q t) : ∀ t, V (t + 1) = 0 := by
  intro t
  rw [hrec t]
  ring

/-- Galí (2015), p. 180: **`λ_w → +∞` as `θ_w → 0⁺`** (for `1 + ε_w φ > 0`). -/
theorem lambdaW_tendsto_atTop {β φ εw : ℝ} (hφε : 0 < 1 + εw * φ) :
    Tendsto (fun θ => lambdaW β θ φ εw) (𝓝[>] 0) atTop := by
  have heq : (fun θ => lambdaW β θ φ εw)
      = fun θ => (1 - θ) * (1 - β * θ) / (1 + εw * φ) * θ⁻¹ := by
    funext θ
    simp only [lambdaW, div_eq_mul_inv, mul_inv]
    ring
  rw [heq]
  have hc : Continuous fun θ : ℝ => (1 - θ) * (1 - β * θ) / (1 + εw * φ) := by fun_prop
  have hf : Tendsto (fun θ : ℝ => (1 - θ) * (1 - β * θ) / (1 + εw * φ)) (𝓝[>] 0)
      (𝓝 (1 / (1 + εw * φ))) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  exact hf.pos_mul_atTop (by positivity) tendsto_inv_nhdsGT_zero

/-- Galí (2015), p. 180: **`λ_p → +∞` as `θ_p → 0⁺`** (for `0 ≤ α < 1`, `ε_p > 0`). -/
theorem lambdaP_tendsto_atTop {β α εp : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) :
    Tendsto (fun θ => lambdaP β θ α εp) (𝓝[>] 0) atTop := by
  have hΘ : 0 < bigTheta α εp := div_pos (by linarith) (by nlinarith)
  have heq : (fun θ => lambdaP β θ α εp)
      = fun θ => (1 - θ) * (1 - β * θ) * bigTheta α εp * θ⁻¹ := by
    funext θ
    simp only [lambdaP, div_eq_mul_inv]
    ring
  rw [heq]
  have hc : Continuous fun θ : ℝ => (1 - θ) * (1 - β * θ) * bigTheta α εp := by fun_prop
  have hf : Tendsto (fun θ : ℝ => (1 - θ) * (1 - β * θ) * bigTheta α εp) (𝓝[>] 0)
      (𝓝 (bigTheta α εp)) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  exact hf.pos_mul_atTop hΘ tendsto_inv_nhdsGT_zero

/-- Galí (2015), p. 180: as `θ_w → 0⁺` the wage-inflation weight `ε_w(1−α)/λ_w → 0` ("wage
inflation is no longer costly"). -/
theorem wageWeight_tendsto_zero {β α φ εw : ℝ} (hφε : 0 < 1 + εw * φ) :
    Tendsto (fun θ => wageWeight β θ α φ εw) (𝓝[>] 0) (𝓝 0) :=
  tendsto_const_nhds.div_atTop (lambdaW_tendsto_atTop hφε)

/-- Galí (2015), p. 180: as `θ_p → 0⁺` the price-inflation weight `ε_p/λ_p → 0`. -/
theorem priceWeight_tendsto_zero {β α εp : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) :
    Tendsto (fun θ => priceWeight β θ α εp) (𝓝[>] 0) (𝓝 0) :=
  tendsto_const_nhds.div_atTop (lambdaP_tendsto_atTop hα0 hα1 hεp)

/-! ### Flexible prices (p. 180) -/

/-- Galí (2015), p. 180: with a constant price markup the real-wage gap equals the gap in the
marginal product of labour, `ω̃ = ỹ − ñ`; with `(1 − α) ñ = ỹ` this is `ω̃ = −(α/(1−α)) ỹ`. -/
theorem flexPrice_realWageGap {α y n om : ℝ} (hα : α ≠ 1) (hom : om = y - n)
    (hn : (1 - α) * n = y) : om = -(α / (1 - α)) * y := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hn' : n = y / (1 - α) := by
    field_simp
    linarith
  rw [hom, hn']
  field_simp
  ring

/-- Galí (2015), p. 180 (**flexible prices**): if (20) holds and the price markup is constant,
`ω̃_t = −(α/(1−α)) ỹ_t`, then `π^w_t = β E_t π^w_{t+1} + λ_w (σ + (φ+α)/(1−α)) ỹ_t`. (The book
calls this slope `κ_w`, which clashes with the `κ_w = λ_w(σ + φ/(1−α))` of (20).) -/
theorem flexPrice_nkpc {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β σ φ α lamW : ℝ} (hα : α ≠ 1)
    {y pw om : ℕ → Ω → ℝ} (hW : WagePC 𝔼 β (kappaW σ φ α lamW) lamW y pw om)
    (hom : ∀ t, om t = (-(α / (1 - α))) • y t) :
    NKPC 𝔼 β (lamW * gapCoeff σ φ α) y pw := by
  intro t
  rw [hW t, hom t, smul_smul, ← kappaW_add (σ := σ) (φ := φ) (lamW := lamW) hα]
  ext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The optimum in the one-rigidity models -/

/-- Galí (2015), pp. 179–180: the welfare loss of a one-rigidity model,
`E_0 ½ ∑ βᵗ [Θ_y ỹ_t² + c x_t²]` (`x = π^p`, `c = ε_p/λ_p` with flexible wages;
`x = π^w`, `c = ε_w(1−α)/λ_w` with flexible prices). -/
noncomputable def nkLoss {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β Θy c : ℝ)
    (y x : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' t, β ^ t * 𝔼.E 0 (fun ω' => (Θy * y t ω' ^ 2 + c * x t ω' ^ 2) / 2) ω

/-- Galí (2015), p. 180: the loss is nonnegative (`β, Θ_y, c ≥ 0`). -/
theorem nkLoss_nonneg {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β Θy c : ℝ} (hβ : 0 ≤ β)
    (hΘ : 0 ≤ Θy) (hc : 0 ≤ c) (y x : ℕ → Ω → ℝ) (ω : Ω) : 0 ≤ nkLoss 𝔼 β Θy c y x ω := by
  refine tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ t) ?_
  have hle : (0 : Ω → ℝ) ≤ fun ω' => (Θy * y t ω' ^ 2 + c * x t ω' ^ 2) / 2 := fun ω' => by
    have := mul_nonneg hΘ (sq_nonneg (y t ω'))
    have := mul_nonneg hc (sq_nonneg (x t ω'))
    simp only [Pi.zero_apply]
    linarith
  have := 𝔼.mono 0 hle ω
  rwa [map_zero] at this

/-- Galí (2015), p. 180: the zero path `ỹ = x = 0` has zero loss. -/
theorem nkLoss_zero {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β Θy c : ℝ) (ω : Ω) :
    nkLoss 𝔼 β Θy c (fun _ _ => 0) (fun _ _ => 0) ω = 0 := by
  have h : (fun _ : Ω => (Θy * (0 : ℝ) ^ 2 + c * (0 : ℝ) ^ 2) / 2) = 0 := by
    funext ω'
    simp
  simp only [nkLoss, h, map_zero, Pi.zero_apply, mul_zero, tsum_zero]

/-- Galí (2015), p. 180: the zero path satisfies any NKPC. -/
theorem nkpc_zero {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β κ : ℝ) :
    NKPC 𝔼 β κ (fun _ _ => 0) (fun _ _ => 0) := by
  intro t
  have h : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
  rw [h, map_zero]
  simp

/-- Galí (2015), p. 180 (**the optimum with one rigidity**): `x = ỹ = 0` satisfies the NKPC
and attains the lower bound zero of the loss, so it is optimal among all paths. -/
theorem nk_zero_optimal {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β Θy c : ℝ} (hβ : 0 ≤ β)
    (hΘ : 0 ≤ Θy) (hc : 0 ≤ c) (κ : ℝ) :
    NKPC 𝔼 β κ (fun _ _ => 0) (fun _ _ => 0) ∧
      ∀ (y x : ℕ → Ω → ℝ) (ω : Ω),
        nkLoss 𝔼 β Θy c (fun _ _ => 0) (fun _ _ => 0) ω ≤ nkLoss 𝔼 β Θy c y x ω :=
  ⟨nkpc_zero 𝔼 β κ, fun y x ω => by
    rw [nkLoss_zero]
    exact nkLoss_nonneg 𝔼 hβ hΘ hc y x ω⟩

/-- Galí (2015), p. 180 (**uniqueness of the optimum, perfect foresight**): with `β, Θ_y, c > 0`
and a summable loss, zero loss forces `ỹ_t = x_t = 0` at every date. -/
theorem nk_zero_unique_pf {β Θy c : ℝ} (hβ : 0 < β) (hΘ : 0 < Θy) (hc : 0 < c)
    {y x : ℕ → Unit → ℝ}
    (hs : Summable fun t => β ^ t * ((Θy * y t () ^ 2 + c * x t () ^ 2) / 2))
    (h0 : nkLoss perfectForesight β Θy c y x () = 0) : ∀ t, y t () = 0 ∧ x t () = 0 := by
  have hpf : nkLoss perfectForesight β Θy c y x ()
      = ∑' t, β ^ t * ((Θy * y t () ^ 2 + c * x t () ^ 2) / 2) := rfl
  rw [hpf] at h0
  have hnn : ∀ t, 0 ≤ β ^ t * ((Θy * y t () ^ 2 + c * x t () ^ 2) / 2) := fun t =>
    mul_nonneg (pow_nonneg hβ.le t) (by positivity)
  intro t
  have hle := hs.le_tsum t (fun j _ => hnn j)
  rw [h0] at hle
  have ht : β ^ t * ((Θy * y t () ^ 2 + c * x t () ^ 2) / 2) = 0 := le_antisymm hle (hnn t)
  have hβt : 0 < β ^ t := pow_pos hβ t
  have hq : Θy * y t () ^ 2 + c * x t () ^ 2 = 0 := by
    rcases mul_eq_zero.1 ht with h | h
    · exact absurd h hβt.ne'
    · linarith
  have h1 : Θy * y t () ^ 2 = 0 := by
    have := mul_nonneg hΘ.le (sq_nonneg (y t ()))
    have := mul_nonneg hc.le (sq_nonneg (x t ()))
    linarith
  have h2 : c * x t () ^ 2 = 0 := by linarith
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 h1).resolve_left hΘ.ne'),
    pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 h2).resolve_left hc.ne')⟩

/-- Galí (2015), p. 180 (**flexible wages: the optimum**): in the limiting flexible-wage model,
the path `π^p = ỹ = ω̃ = 0` satisfies (18) and the constant-wage-markup condition, and attains
zero loss `E_0 ½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ² + (ε_p/λ_p)(π^p)²]`, the lower bound for every
path. -/
theorem flexWage_optimal {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β σ φ α lamP εp : ℝ}
    (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlamP : 0 < lamP)
    (hεp : 0 ≤ εp) :
    PricePC 𝔼 β (kappaP α lamP) lamP (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) ∧
      (∀ t, (fun _ _ => 0 : ℕ → Ω → ℝ) t = (σ + φ / (1 - α)) • (fun _ _ => 0 : ℕ → Ω → ℝ) t) ∧
      ∀ (y pp : ℕ → Ω → ℝ) (ω : Ω),
        nkLoss 𝔼 β (gapCoeff σ φ α) (εp / lamP) (fun _ _ => 0) (fun _ _ => 0) ω
          ≤ nkLoss 𝔼 β (gapCoeff σ φ α) (εp / lamP) y pp ω := by
  have hΘ : 0 ≤ gapCoeff σ φ α := by
    unfold gapCoeff
    have := div_nonneg (by linarith : 0 ≤ φ + α) (by linarith : (0 : ℝ) ≤ 1 - α)
    linarith
  refine ⟨fun t => ?_, fun t => by ext; simp, (nk_zero_optimal 𝔼 hβ hΘ
    (div_nonneg hεp hlamP.le) 0).2⟩
  have h : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
  rw [h, map_zero]
  simp

/-- Galí (2015), p. 180: in the flexible-wage model, **strict price-inflation targeting forces a
zero output gap**: if `π^p ≡ 0` satisfies the NKPC with slope `κ ≠ 0` then `ỹ ≡ 0`; together
with `flexWage_optimal`, strict price-inflation targeting is optimal when wages are flexible. -/
theorem flexWage_strictPrice_forces_zero_gap {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ : ℝ}
    (hκ : κ ≠ 0) {y : ℕ → Ω → ℝ} (h : NKPC 𝔼 β κ y (fun _ _ => 0)) : ∀ t, y t = 0 := by
  intro t
  have ht := h t
  have h0 : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
  rw [h0, map_zero, smul_zero, zero_add] at ht
  have := congrArg (fun f => κ⁻¹ • f) ht
  simp only [smul_zero, smul_smul, inv_mul_cancel₀ hκ, one_smul] at this
  exact this.symm

/-- Galí (2015), p. 180 (**flexible prices: the optimum**): in the limiting flexible-price model
the path `π^w = ỹ = ω̃ = 0` satisfies (20) and the constant-price-markup condition and attains
zero loss `E_0 ½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ² + (ε_w(1−α)/λ_w)(π^w)²]`. -/
theorem flexPrice_optimal {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β σ φ α lamW εw : ℝ}
    (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlamW : 0 < lamW)
    (hεw : 0 ≤ εw) :
    WagePC 𝔼 β (kappaW σ φ α lamW) lamW (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) ∧
      (∀ t, (fun _ _ => 0 : ℕ → Ω → ℝ) t = (-(α / (1 - α))) • (fun _ _ => 0 : ℕ → Ω → ℝ) t) ∧
      ∀ (y pw : ℕ → Ω → ℝ) (ω : Ω),
        nkLoss 𝔼 β (gapCoeff σ φ α) (εw * (1 - α) / lamW) (fun _ _ => 0) (fun _ _ => 0) ω
          ≤ nkLoss 𝔼 β (gapCoeff σ φ α) (εw * (1 - α) / lamW) y pw ω := by
  have hΘ : 0 ≤ gapCoeff σ φ α := by
    unfold gapCoeff
    have := div_nonneg (by linarith : 0 ≤ φ + α) (by linarith : (0 : ℝ) ≤ 1 - α)
    linarith
  refine ⟨fun t => ?_, fun t => by ext; simp, (nk_zero_optimal 𝔼 hβ hΘ
    (div_nonneg (mul_nonneg hεw (by linarith)) hlamW.le) 0).2⟩
  have h : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
  rw [h, map_zero]
  simp

/-! ### Strict targeting with sticky wages and prices (perfect foresight) -/

/-- Galí (2015), eqs. (18), (20), (21), pp. 172–173, under perfect foresight with
`ω̃_{−1} = 0`: a path `(ỹ, π^p, π^w, ω̃)` is feasible given the natural-real-wage changes
`Δωⁿ` (`dn`). -/
def Feasible (β κp κw lamP lamW : ℝ) (dn y pp pw om : ℕ → ℝ) : Prop :=
  (∀ t, pp t = β * pp (t + 1) + κp * y t + lamP * om t) ∧
    (∀ t, pw t = β * pw (t + 1) + κw * y t - lamW * om t) ∧
    om 0 = pw 0 - pp 0 - dn 0 ∧ ∀ t, om (t + 1) = om t + pw (t + 1) - pp (t + 1) - dn (t + 1)

/-- Galí (2015), eq. (28), p. 179, perfect foresight: the welfare loss
`½ ∑ βᵗ [Θ_y ỹ_t² + c_p (π^p_t)² + c_w (π^w_t)²]`. -/
noncomputable def loss (β Θy cp cw : ℝ) (y pp pw : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * ((Θy * y t ^ 2 + cp * pp t ^ 2 + cw * pw t ^ 2) / 2)

/-- Galí (2015), p. 180: the improving direction, output-gap component
`(1 + β + λ_p + λ_w, −1, 0, 0, …)`. -/
def dirY (β lamP lamW : ℝ) : ℕ → ℝ
  | 0 => 1 + β + (lamP + lamW)
  | 1 => -1
  | _ + 2 => 0

/-- Galí (2015), p. 180: the improving direction, price-inflation component
`(κ_p + M, −κ_p, 0, …)`, `M = κ_p λ_w + λ_p κ_w`. -/
def dirP (κp κw lamP lamW : ℝ) : ℕ → ℝ
  | 0 => κp + (κp * lamW + lamP * κw)
  | 1 => -κp
  | _ + 2 => 0

/-- Galí (2015), p. 180: the improving direction, wage-inflation component
`(κ_w + M, −κ_w, 0, …)`. -/
def dirW (κp κw lamP lamW : ℝ) : ℕ → ℝ
  | 0 => κw + (κp * lamW + lamP * κw)
  | 1 => -κw
  | _ + 2 => 0

/-- Galí (2015), p. 180: the improving direction, real-wage-gap component
`(κ_w − κ_p, 0, 0, …)`. -/
def dirOm (κp κw : ℝ) : ℕ → ℝ
  | 0 => κw - κp
  | _ + 1 => 0

/-- Galí (2015), p. 180: the two-period direction is feasible for the homogeneous system
(`Δωⁿ ≡ 0`, `ω̃_{−1} = 0`). -/
theorem feasible_dir (β κp κw lamP lamW : ℝ) :
    Feasible β κp κw lamP lamW (fun _ => 0) (dirY β lamP lamW) (dirP κp κw lamP lamW)
      (dirW κp κw lamP lamW)
      (dirOm κp κw) := by
  refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_⟩
  · match t with
    | 0 => simp only [dirP, dirY, dirOm]; ring
    | 1 => simp only [dirP, dirY, dirOm]; ring
    | n + 2 => simp only [dirP, dirY, dirOm]; ring
  · match t with
    | 0 => simp only [dirW, dirY, dirOm]; ring
    | 1 => simp only [dirW, dirY, dirOm]; ring
    | n + 2 => simp only [dirW, dirY, dirOm]; ring
  · simp only [dirW, dirP, dirOm]
    ring
  · match t with
    | 0 => simp only [dirW, dirP, dirOm]; ring
    | n + 1 => simp only [dirW, dirP, dirOm]; ring

/-- Galí (2015), p. 180: feasibility is preserved by adding a multiple of a homogeneous
feasible direction. -/
theorem feasible_add {β κp κw lamP lamW : ℝ} {dn y pp pw om hy hp hw ho : ℕ → ℝ} (τ : ℝ)
    (hx : Feasible β κp κw lamP lamW dn y pp pw om)
    (hh : Feasible β κp κw lamP lamW (fun _ => 0) hy hp hw ho) :
    Feasible β κp κw lamP lamW dn (fun t => y t + τ * hy t) (fun t => pp t + τ * hp t)
      (fun t => pw t + τ * hw t) (fun t => om t + τ * ho t) := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨g1, g2, g3, g4⟩ := hh
  refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_⟩
  · linear_combination h1 t + τ * g1 t
  · linear_combination h2 t + τ * g2 t
  · beta_reduce at g3
    linear_combination h3 + τ * g3
  · beta_reduce at g4
    linear_combination h4 t + τ * g4 t

/-- Galí (2015), p. 180: the loss of a path that vanishes from `t = 2` on is a finite sum. -/
theorem loss_two {β Θy cp cw : ℝ} {y pp pw : ℕ → ℝ} (hy : ∀ t, y (t + 2) = 0)
    (hp : ∀ t, pp (t + 2) = 0) (hw : ∀ t, pw (t + 2) = 0) :
    loss β Θy cp cw y pp pw = (Θy * y 0 ^ 2 + cp * pp 0 ^ 2 + cw * pw 0 ^ 2) / 2 +
      β * ((Θy * y 1 ^ 2 + cp * pp 1 ^ 2 + cw * pw 1 ^ 2) / 2) := by
  rw [loss, tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ]
  · intro t ht
    have h2 : 2 ≤ t := by
      simp only [Finset.mem_range, not_lt] at ht
      exact ht
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h2
    simp [hy n, hp n, hw n]

/-- Galí (2015), p. 180 (elementary): for `B ≠ 0`, `Q ≥ 0` and `τ = −B/(Q + 1)`,
`τ B + τ² Q < 0`, so a quadratic loss can be lowered along any direction with nonzero slope. -/
theorem quad_improve {B Q : ℝ} (hB : B ≠ 0) (hQ : 0 ≤ Q) :
    (-B / (Q + 1)) * B + (-B / (Q + 1)) ^ 2 * Q < 0 := by
  have hQ1 : 0 < Q + 1 := by linarith
  have hB2 : 0 < B ^ 2 := by positivity
  have e : (-B / (Q + 1)) * B + (-B / (Q + 1)) ^ 2 * Q = -(B ^ 2 / (Q + 1) ^ 2) := by
    field_simp
    ring
  rw [e]
  exact neg_lt_zero.2 (by positivity)

/-- Galí (2015), p. 180 (the growth argument behind uniqueness): if `δ_0 = D_0 > 0`,
`D_{t+1} = D_t + δ_{t+1}` and `β δ_{t+1} = δ_t + m D_t` with `0 < β ≤ 1`, `m ≥ 0`, then
`δ_t ≥ 0`, `D_0 ≤ βᵗ δ_t` and `δ_t ≤ D_t` for all `t` (the real-wage gap explodes
geometrically). -/
theorem growth {β m : ℝ} (hβ0 : 0 < β) (hm : 0 ≤ m) {D δ : ℕ → ℝ} (h0 : δ 0 = D 0)
    (hD : ∀ t, D (t + 1) = D t + δ (t + 1)) (hδ : ∀ t, β * δ (t + 1) = δ t + m * D t)
    (hc : 0 < D 0) : ∀ t, 0 ≤ δ t ∧ D 0 ≤ β ^ t * δ t ∧ δ t ≤ D t := by
  intro t
  induction t with
  | zero => exact ⟨by linarith, by simp [h0], by linarith⟩
  | succ t ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have hDt : 0 ≤ D t := le_trans i1 i3
    have hstep : δ t ≤ β * δ (t + 1) := by rw [hδ t]; nlinarith
    have hpos : 0 ≤ δ (t + 1) := by
      by_contra hneg
      push Not at hneg
      nlinarith
    refine ⟨hpos, ?_, ?_⟩
    · calc D 0 ≤ β ^ t * δ t := i2
        _ ≤ β ^ t * (β * δ (t + 1)) := mul_le_mul_of_nonneg_left hstep (pow_nonneg hβ0.le t)
        _ = β ^ (t + 1) * δ (t + 1) := by ring
    · rw [hD t]
      linarith

/-- Galí (2015), p. 180: in the setting of `growth`, `D_0 = 0` forces `D ≡ δ ≡ 0`. -/
theorem zero_of_growth {β m : ℝ} (hβ0 : 0 < β) {D δ : ℕ → ℝ} (h0 : δ 0 = D 0)
    (hD : ∀ t, D (t + 1) = D t + δ (t + 1)) (hδ : ∀ t, β * δ (t + 1) = δ t + m * D t)
    (hc : D 0 = 0) : ∀ t, D t = 0 ∧ δ t = 0 := by
  intro t
  induction t with
  | zero => exact ⟨hc, by rw [h0, hc]⟩
  | succ t ih =>
    have h1 : β * δ (t + 1) = 0 := by rw [hδ t, ih.1, ih.2]; ring
    have h2 : δ (t + 1) = 0 := (mul_eq_zero.1 h1).resolve_left hβ0.ne'
    exact ⟨by rw [hD t, ih.1, h2]; ring, h2⟩

/-- Galí (2015), p. 180: in the setting of `growth` with `β ≤ 1` and any `D_0`,
`D_0² ≤ βᵗ D_t²` for every `t`. -/
theorem sq_le_of_growth {β m : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hm : 0 ≤ m) {D δ : ℕ → ℝ}
    (h0 : δ 0 = D 0) (hD : ∀ t, D (t + 1) = D t + δ (t + 1))
    (hδ : ∀ t, β * δ (t + 1) = δ t + m * D t) : ∀ t, D 0 ^ 2 ≤ β ^ t * D t ^ 2 := by
  have key : ∀ {D δ : ℕ → ℝ}, δ 0 = D 0 → (∀ t, D (t + 1) = D t + δ (t + 1)) →
      (∀ t, β * δ (t + 1) = δ t + m * D t) → 0 < D 0 → ∀ t, D 0 ^ 2 ≤ β ^ t * D t ^ 2 := by
    intro D δ h0 hD hδ hc t
    obtain ⟨i1, i2, i3⟩ := growth hβ0 hm h0 hD hδ hc t
    have hbt : 0 < β ^ t := pow_pos hβ0 t
    have hbt1 : β ^ t ≤ 1 := pow_le_one₀ hβ0.le hβ1
    have hDt : 0 ≤ D t := le_trans i1 i3
    have h1 : D 0 ≤ β ^ t * D t := le_trans i2 (mul_le_mul_of_nonneg_left i3 hbt.le)
    have h2 : β ^ t * D t ≤ D t := by nlinarith
    nlinarith
  intro t
  rcases lt_trichotomy (D 0) 0 with hneg | hzero | hpos
  · have := key (D := fun t => -D t) (δ := fun t => -δ t) (by rw [h0])
      (fun t => by rw [hD t]; ring)
      (fun t => by linear_combination (-1 : ℝ) * hδ t)
      (by linarith) t
    simpa using this
  · calc D 0 ^ 2 = 0 := by rw [hzero]; ring
      _ ≤ β ^ t * D t ^ 2 := by positivity
  · exact key h0 hD hδ hpos t

/-- Galí (2015), p. 180: a sequence whose discounted squares are summable cannot stay above a
positive bound from `t = 1` on. -/
theorem not_summable_of_ge {f : ℕ → ℝ} {k : ℝ} (hk : 0 < k) (hf : ∀ t, k ≤ f (t + 1))
    (hs : Summable f) : False := by
  have h := ((summable_nat_add_iff 1).2 hs).tendsto_atTop_zero
  obtain ⟨t, ht⟩ := (h.eventually (gt_mem_nhds hk)).exists
  linarith [hf t]

/-- Galí (2015), p. 180: `M = κ_p λ_w + λ_p κ_w`, the coefficient of the strict-targeting paths. -/
noncomputable def bigM (κp κw lamP lamW : ℝ) : ℝ := κp * lamW + lamP * κw

/-- Galí (2015), p. 180: the technology-shock path (changes in the natural real wage) used for
strict price-inflation targeting: `Δωⁿ = ((M + κ_p)/λ_p, −κ_p/λ_p, 0, …)`. -/
noncomputable def priceShock (κp κw lamP lamW : ℝ) : ℕ → ℝ
  | 0 => (bigM κp κw lamP lamW + κp) / lamP
  | 1 => -κp / lamP
  | _ + 2 => 0

/-- Galí (2015), p. 180: the strict price-inflation-targeting path for `priceShock`: output gap
`(1, 0, …)`. -/
def spY : ℕ → ℝ
  | 0 => 1
  | _ + 1 => 0

/-- Galí (2015), p. 180: the strict price-targeting path, wage inflation `(M/λ_p, 0, …)`. -/
noncomputable def spW (κp κw lamP lamW : ℝ) : ℕ → ℝ
  | 0 => bigM κp κw lamP lamW / lamP
  | _ + 1 => 0

/-- Galí (2015), p. 180: the strict price-targeting path, real-wage gap `(−κ_p/λ_p, 0, …)`. -/
noncomputable def spOm (κp lamP : ℝ) : ℕ → ℝ
  | 0 => -κp / lamP
  | _ + 1 => 0

/-- Galí (2015), p. 180: `π^p ≡ 0`, `ỹ = spY`, `π^w = spW`, `ω̃ = spOm` is feasible for the
technology shock `priceShock`. -/
theorem feasible_sp {β κp κw lamP lamW : ℝ} (hlamP : 0 < lamP) :
    Feasible β κp κw lamP lamW (priceShock κp κw lamP lamW) spY (fun _ => 0) (spW κp κw lamP lamW)
      (spOm κp lamP) := by
  have hl : lamP ≠ 0 := hlamP.ne'
  refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_⟩
  · match t with
    | 0 => simp only [spY, spOm]; field_simp; ring
    | n + 1 => simp only [spY, spOm]; ring
  · match t with
    | 0 => simp only [spY, spOm, spW, bigM]; field_simp; ring
    | n + 1 => simp only [spY, spOm, spW]; ring
  · simp only [spOm, spW, priceShock, bigM]
    field_simp
    ring
  · match t with
    | 0 => simp only [spOm, spW, priceShock]; ring
    | n + 1 => simp only [spOm, spW, priceShock]; ring

/-- Galí (2015), p. 180 (**uniqueness of the strict price-targeting path**): with
`0 < β ≤ 1`, `κ_p ≥ 0`, `λ_p, λ_w > 0`, every feasible path for `priceShock` with `π^p ≡ 0` and
`∑ βᵗ ỹ_t² < ∞` is the explicit path `(spY, 0, spW, spOm)` (`κ_w > 0`). -/
theorem sp_unique {β κp κw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hκp : 0 ≤ κp)
    (hlamP : 0 < lamP) (hlamW : 0 < lamW) (hκw : 0 < κw) {y pw om : ℕ → ℝ}
    (hF : Feasible β κp κw lamP lamW (priceShock κp κw lamP lamW) y (fun _ => 0) pw om)
    (hs : Summable fun t => β ^ t * y t ^ 2) :
    y = spY ∧ pw = spW κp κw lamP lamW ∧ om = spOm κp lamP := by
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := feasible_sp (β := β) (κp := κp) (κw := κw) (lamW := lamW) hlamP
  set D : ℕ → ℝ := fun t => om t - spOm κp lamP t with hDdef
  set δ : ℕ → ℝ := fun t => pw t - spW κp κw lamP lamW t with hδdef
  set dY : ℕ → ℝ := fun t => y t - spY t with hdYdef
  have e18 : ∀ t, κp * dY t + lamP * D t = 0 := fun t => by
    have a := f1 t
    have b := g1 t
    simp only [hDdef, hdYdef]
    linarith
  have e0 : δ 0 = D 0 := by
    simp only [hDdef, hδdef]
    linarith
  have eD : ∀ t, D (t + 1) = D t + δ (t + 1) := fun t => by
    have a := f4 t
    have b := g4 t
    simp only [hDdef, hδdef]
    linarith
  have e20 : ∀ t, δ t = β * δ (t + 1) + κw * dY t - lamW * D t := fun t => by
    have a := f2 t
    have b := g2 t
    simp only [hDdef, hδdef, hdYdef]
    linarith
  -- the output-gap difference is summable in the discounted-square sense from `t = 1` on
  have hsY : ∀ t, β ^ (t + 1) * dY (t + 1) ^ 2 = β ^ (t + 1) * y (t + 1) ^ 2 := fun t => by
    simp [hdYdef, spY]
  have hzero : D = 0 ∧ δ = 0 ∧ dY = 0 := by
    rcases hκp.lt_or_eq with hκpos | hκ0
    · -- `κ_p > 0`: `ỹ` is proportional to `ω̃`, and the homogeneous dynamics explode
      set m := κw * lamP / κp + lamW with hm
      have hm0 : 0 ≤ m := by positivity
      have hdY : ∀ t, dY t = -(lamP / κp) * D t := fun t => by
        have := e18 t
        field_simp
        linarith
      have eδ : ∀ t, β * δ (t + 1) = δ t + m * D t := fun t => by
        have := e20 t
        rw [hdY t] at this
        rw [hm]
        field_simp at this ⊢
        linarith
      rcases eq_or_ne (D 0) 0 with hD0 | hD0
      · have hz := zero_of_growth hβ0 e0 eD eδ hD0
        refine ⟨funext fun t => (hz t).1, funext fun t => (hz t).2, funext fun t => ?_⟩
        rw [hdY t, (hz t).1]
        simp
      · exfalso
        have hsq := sq_le_of_growth hβ0 hβ1 hm0 e0 eD eδ
        have hk : 0 < (lamP / κp) ^ 2 * D 0 ^ 2 := by positivity
        refine not_summable_of_ge hk (fun t => ?_) hs
        have h1 := hsq (t + 1)
        have h2 : β ^ (t + 1) * y (t + 1) ^ 2
            = (lamP / κp) ^ 2 * (β ^ (t + 1) * D (t + 1) ^ 2) := by
          rw [← hsY t, hdY (t + 1)]
          ring
        rw [h2]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    · -- `κ_p = 0`: `ω̃` is pinned at its strict-targeting value
      have hD : ∀ t, D t = 0 := fun t => by
        have := e18 t
        rw [← hκ0, zero_mul, zero_add] at this
        exact (mul_eq_zero.1 this).resolve_left hlamP.ne'
      have hδ : ∀ t, δ t = 0 := fun t => by
        cases t with
        | zero => rw [e0, hD 0]
        | succ t => have := eD t; rw [hD (t + 1), hD t] at this; linarith
      refine ⟨funext hD, funext hδ, funext fun t => ?_⟩
      have := e20 t
      rw [hδ t, hδ (t + 1), hD t] at this
      have h : κw * dY t = 0 := by linarith
      exact (mul_eq_zero.1 h).resolve_left hκw.ne'
  obtain ⟨hD, hδ, hdY⟩ := hzero
  refine ⟨funext fun t => ?_, funext fun t => ?_, funext fun t => ?_⟩
  · have := congrFun hdY t
    simp only [hdYdef, Pi.zero_apply] at this
    linarith
  · have := congrFun hδ t
    simp only [hδdef, Pi.zero_apply] at this
    linarith
  · have := congrFun hD t
    simp only [hDdef, Pi.zero_apply] at this
    linarith

/-- Galí (2015), p. 180 (**strict price-inflation targeting is suboptimal with sticky wages**):
for `0 < β ≤ 1`, `κ_p ≥ 0`, `κ_w, λ_p, λ_w, Θ_y > 0` and weights `c_p, c_w ≥ 0`, there is a
technology-shock path `Δωⁿ` (`priceShock`, zero from `t = 2` on) for which a path with
`π^p ≡ 0` exists; every such path with `∑ βᵗ ỹ_t² < ∞` has **strictly higher loss** (28) than
some other feasible path. -/
theorem strict_price_targeting_suboptimal {β κp κw lamP lamW Θy cp cw : ℝ} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hκp : 0 ≤ κp) (hκw : 0 < κw) (hlamP : 0 < lamP) (hlamW : 0 < lamW)
    (hΘ : 0 < Θy) (hcp : 0 ≤ cp) (hcw : 0 ≤ cw) :
    (∀ t, priceShock κp κw lamP lamW (t + 2) = 0) ∧
      Feasible β κp κw lamP lamW (priceShock κp κw lamP lamW) spY (fun _ => 0)
        (spW κp κw lamP lamW) (spOm κp lamP) ∧
      ∀ y pw om : ℕ → ℝ,
        Feasible β κp κw lamP lamW (priceShock κp κw lamP lamW) y (fun _ => 0) pw om →
        Summable (fun t => β ^ t * y t ^ 2) →
        ∃ y' pp' pw' om' : ℕ → ℝ,
          Feasible β κp κw lamP lamW (priceShock κp κw lamP lamW) y' pp' pw' om' ∧
            loss β Θy cp cw y' pp' pw' < loss β Θy cp cw y (fun _ => 0) pw := by
  refine ⟨fun t => rfl, feasible_sp hlamP, fun y pw om hF hs => ?_⟩
  obtain ⟨rfl, rfl, rfl⟩ := sp_unique hβ0 hβ1 hκp hlamP hlamW hκw hF hs
  have hM : 0 ≤ bigM κp κw lamP lamW := by unfold bigM; positivity
  have hB : 0 < Θy * (1 + β + (lamP + lamW)) +
      cw * (bigM κp κw lamP lamW / lamP) * (κw + bigM κp κw lamP lamW) := by
    have h1 : 0 < Θy * (1 + β + (lamP + lamW)) := mul_pos hΘ (by linarith)
    have h2 : 0 ≤ cw * (bigM κp κw lamP lamW / lamP) * (κw + bigM κp κw lamP lamW) := by
      positivity
    linarith
  have hQ : 0 ≤ (Θy * (1 + β + (lamP + lamW)) ^ 2 + cp * (κp + bigM κp κw lamP lamW) ^ 2 +
      cw * (κw + bigM κp κw lamP lamW) ^ 2) / 2 + β * ((Θy + cp * κp ^ 2 + cw * κw ^ 2) / 2) := by
    positivity
  have himp := quad_improve hB.ne' hQ
  set τ := -(Θy * (1 + β + (lamP + lamW)) +
      cw * (bigM κp κw lamP lamW / lamP) * (κw + bigM κp κw lamP lamW)) /
    ((Θy * (1 + β + (lamP + lamW)) ^ 2 + cp * (κp + bigM κp κw lamP lamW) ^ 2 +
      cw * (κw + bigM κp κw lamP lamW) ^ 2) / 2 + β * ((Θy + cp * κp ^ 2 + cw * κw ^ 2) / 2) + 1)
    with hτ
  refine ⟨_, _, _, _, feasible_add τ (feasible_sp (β := β) (κw := κw) (lamW := lamW) hlamP)
    (feasible_dir β κp κw lamP lamW), ?_⟩
  rw [loss_two (fun t => by simp [spY, dirY]) (fun t => by simp [dirP])
      (fun t => by simp [spW, dirW]),
    loss_two (fun t => by simp [spY]) (fun _ => rfl) (fun t => by simp [spW])]
  simp only [spY, spW, dirY, dirP, dirW]
  simp only [bigM] at himp ⊢
  linear_combination himp

/-- Galí (2015), p. 180: the technology-shock path used for strict wage-inflation targeting,
`Δωⁿ = (−(M + κ_w)/λ_w, κ_w/λ_w, 0, …)`. -/
noncomputable def wageShock (κp κw lamP lamW : ℝ) : ℕ → ℝ
  | 0 => -(bigM κp κw lamP lamW + κw) / lamW
  | 1 => κw / lamW
  | _ + 2 => 0

/-- Galí (2015), p. 180: the strict wage-targeting path, price inflation `(M/λ_w, 0, …)`. -/
noncomputable def swP (κp κw lamP lamW : ℝ) : ℕ → ℝ
  | 0 => bigM κp κw lamP lamW / lamW
  | _ + 1 => 0

/-- Galí (2015), p. 180: the strict wage-targeting path, real-wage gap `(κ_w/λ_w, 0, …)`. -/
noncomputable def swOm (κw lamW : ℝ) : ℕ → ℝ
  | 0 => κw / lamW
  | _ + 1 => 0

/-- Galí (2015), p. 180: `π^w ≡ 0`, `ỹ = spY`, `π^p = swP`, `ω̃ = swOm` is feasible for the
technology shock `wageShock`. -/
theorem feasible_sw {β κp κw lamP lamW : ℝ} (hlamW : 0 < lamW) :
    Feasible β κp κw lamP lamW (wageShock κp κw lamP lamW) spY (swP κp κw lamP lamW)
      (fun _ => 0) (swOm κw lamW) := by
  have hl : lamW ≠ 0 := hlamW.ne'
  refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_⟩
  · match t with
    | 0 => simp only [spY, swOm, swP, bigM]; field_simp; ring
    | n + 1 => simp only [spY, swOm, swP]; ring
  · match t with
    | 0 => simp only [spY, swOm]; field_simp; ring
    | n + 1 => simp only [spY, swOm]; ring
  · simp only [swOm, swP, wageShock, bigM]
    field_simp
    ring
  · match t with
    | 0 => simp only [swOm, swP, wageShock]; ring
    | n + 1 => simp only [swOm, swP, wageShock]; ring

/-- Galí (2015), p. 180 (**uniqueness of the strict wage-targeting path**): with `0 < β ≤ 1`,
`κ_p ≥ 0`, `κ_w, λ_p, λ_w > 0`, every feasible path for `wageShock` with `π^w ≡ 0` and
`∑ βᵗ ỹ_t² < ∞` is the explicit path `(spY, swP, 0, swOm)`. -/
theorem sw_unique {β κp κw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hκp : 0 ≤ κp)
    (hκw : 0 < κw) (hlamP : 0 < lamP) (hlamW : 0 < lamW) {y pp om : ℕ → ℝ}
    (hF : Feasible β κp κw lamP lamW (wageShock κp κw lamP lamW) y pp (fun _ => 0) om)
    (hs : Summable fun t => β ^ t * y t ^ 2) :
    y = spY ∧ pp = swP κp κw lamP lamW ∧ om = swOm κw lamW := by
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := feasible_sw (β := β) (κp := κp) (κw := κw) (lamP := lamP) hlamW
  set D : ℕ → ℝ := fun t => om t - swOm κw lamW t with hDdef
  set δ : ℕ → ℝ := fun t => swP κp κw lamP lamW t - pp t with hδdef
  set dY : ℕ → ℝ := fun t => y t - spY t with hdYdef
  set m := κp * lamW / κw + lamP with hm
  have hm0 : 0 ≤ m := by positivity
  have hdY : ∀ t, dY t = lamW / κw * D t := fun t => by
    have a := f2 t
    have b := g2 t
    simp only [hDdef, hdYdef]
    field_simp
    linarith
  have e0 : δ 0 = D 0 := by
    simp only [hDdef, hδdef]
    linarith
  have eD : ∀ t, D (t + 1) = D t + δ (t + 1) := fun t => by
    have a := f4 t
    have b := g4 t
    simp only [hDdef, hδdef]
    linarith
  have eδ : ∀ t, β * δ (t + 1) = δ t + m * D t := fun t => by
    have a := f1 t
    have b := g1 t
    have c := hdY t
    simp only [hDdef, hδdef, hdYdef] at c ⊢
    rw [hm]
    field_simp at c ⊢
    nlinarith
  have hsY : ∀ t, β ^ (t + 1) * dY (t + 1) ^ 2 = β ^ (t + 1) * y (t + 1) ^ 2 := fun t => by
    simp [hdYdef, spY]
  have hzero : ∀ t, D t = 0 ∧ δ t = 0 := by
    rcases eq_or_ne (D 0) 0 with hD0 | hD0
    · exact zero_of_growth hβ0 e0 eD eδ hD0
    · exfalso
      have hsq := sq_le_of_growth hβ0 hβ1 hm0 e0 eD eδ
      have hk : 0 < (lamW / κw) ^ 2 * D 0 ^ 2 := by positivity
      refine not_summable_of_ge hk (fun t => ?_) hs
      have h1 := hsq (t + 1)
      have h2 : β ^ (t + 1) * y (t + 1) ^ 2
          = (lamW / κw) ^ 2 * (β ^ (t + 1) * D (t + 1) ^ 2) := by
        rw [← hsY t, hdY (t + 1)]
        ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
  refine ⟨funext fun t => ?_, funext fun t => ?_, funext fun t => ?_⟩
  · have h := hdY t
    rw [(hzero t).1, mul_zero] at h
    simp only [hdYdef] at h
    linarith
  · have h := (hzero t).2
    simp only [hδdef] at h
    linarith
  · have h := (hzero t).1
    simp only [hDdef] at h
    linarith

/-- Galí (2015), p. 180 (**strict wage-inflation targeting is suboptimal with sticky prices**):
for `0 < β ≤ 1`, `κ_p ≥ 0`, `κ_w, λ_p, λ_w, Θ_y > 0` and weights `c_p, c_w ≥ 0`, there is a
technology-shock path `Δωⁿ` (`wageShock`) for which a path with `π^w ≡ 0` exists; every such
path with `∑ βᵗ ỹ_t² < ∞` has **strictly higher loss** (28) than some other feasible path. -/
theorem strict_wage_targeting_suboptimal {β κp κw lamP lamW Θy cp cw : ℝ} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hκp : 0 ≤ κp) (hκw : 0 < κw) (hlamP : 0 < lamP) (hlamW : 0 < lamW)
    (hΘ : 0 < Θy) (hcp : 0 ≤ cp) (hcw : 0 ≤ cw) :
    (∀ t, wageShock κp κw lamP lamW (t + 2) = 0) ∧
      Feasible β κp κw lamP lamW (wageShock κp κw lamP lamW) spY (swP κp κw lamP lamW)
        (fun _ => 0) (swOm κw lamW) ∧
      ∀ y pp om : ℕ → ℝ,
        Feasible β κp κw lamP lamW (wageShock κp κw lamP lamW) y pp (fun _ => 0) om →
        Summable (fun t => β ^ t * y t ^ 2) →
        ∃ y' pp' pw' om' : ℕ → ℝ,
          Feasible β κp κw lamP lamW (wageShock κp κw lamP lamW) y' pp' pw' om' ∧
            loss β Θy cp cw y' pp' pw' < loss β Θy cp cw y pp (fun _ => 0) := by
  refine ⟨fun t => rfl, feasible_sw hlamW, fun y pp om hF hs => ?_⟩
  obtain ⟨rfl, rfl, rfl⟩ := sw_unique hβ0 hβ1 hκp hκw hlamP hlamW hF hs
  have hM : 0 ≤ bigM κp κw lamP lamW := by unfold bigM; positivity
  have hB : 0 < Θy * (1 + β + (lamP + lamW)) +
      cp * (bigM κp κw lamP lamW / lamW) * (κp + bigM κp κw lamP lamW) := by
    have h1 : 0 < Θy * (1 + β + (lamP + lamW)) := mul_pos hΘ (by linarith)
    have h2 : 0 ≤ cp * (bigM κp κw lamP lamW / lamW) * (κp + bigM κp κw lamP lamW) := by
      positivity
    linarith
  have hQ : 0 ≤ (Θy * (1 + β + (lamP + lamW)) ^ 2 + cp * (κp + bigM κp κw lamP lamW) ^ 2 +
      cw * (κw + bigM κp κw lamP lamW) ^ 2) / 2 + β * ((Θy + cp * κp ^ 2 + cw * κw ^ 2) / 2) := by
    positivity
  have himp := quad_improve hB.ne' hQ
  set τ := -(Θy * (1 + β + (lamP + lamW)) +
      cp * (bigM κp κw lamP lamW / lamW) * (κp + bigM κp κw lamP lamW)) /
    ((Θy * (1 + β + (lamP + lamW)) ^ 2 + cp * (κp + bigM κp κw lamP lamW) ^ 2 +
      cw * (κw + bigM κp κw lamP lamW) ^ 2) / 2 + β * ((Θy + cp * κp ^ 2 + cw * κw ^ 2) / 2) + 1)
    with hτ
  refine ⟨_, _, _, _, feasible_add τ (feasible_sw (β := β) (κp := κp) (lamP := lamP) hlamW)
    (feasible_dir β κp κw lamP lamW), ?_⟩
  rw [loss_two (fun t => by simp [spY, dirY]) (fun t => by simp [swP, dirP])
      (fun t => by simp [dirW]),
    loss_two (fun t => by simp [spY]) (fun t => by simp [swP]) (fun _ => rfl)]
  simp only [spY, swP, dirY, dirP, dirW]
  simp only [bigM] at himp ⊢
  linear_combination himp

/-- Galí (2015), p. 180: the model's coefficients are admissible: for `0 < β < 1`, `σ > 0`,
`φ ≥ 0`, `0 ≤ α < 1`, `ε_p, ε_w > 0`, `θ_p, θ_w ∈ (0, 1)`: `λ_p, λ_w > 0`, `κ_p ≥ 0`, `κ_w > 0`,
`σ + (φ+α)/(1−α) > 0` and the inflation weights are nonnegative. -/
theorem model_coefficients {β σ φ α εp εw θp θw : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw) (hθp0 : 0 < θp)
    (hθp1 : θp < 1) (hθw0 : 0 < θw) (hθw1 : θw < 1) :
    0 < lambdaP β θp α εp ∧ 0 < lambdaW β θw φ εw ∧ 0 ≤ kappaP α (lambdaP β θp α εp) ∧
      0 < kappaW σ φ α (lambdaW β θw φ εw) ∧ 0 < gapCoeff σ φ α ∧
      0 ≤ priceWeight β θp α εp ∧ 0 ≤ wageWeight β θw α φ εw := by
  have h1 : (0 : ℝ) < 1 - α := by linarith
  have hΘ : 0 < bigTheta α εp := div_pos h1 (by nlinarith)
  have hβθp : 0 < 1 - β * θp := by nlinarith
  have hβθw : 0 < 1 - β * θw := by nlinarith
  have hlp : 0 < lambdaP β θp α εp :=
    mul_pos (div_pos (mul_pos (by linarith) hβθp) hθp0) hΘ
  have hlw : 0 < lambdaW β θw φ εw :=
    div_pos (mul_pos (by linarith) hβθw) (mul_pos hθw0 (by nlinarith))
  have hg : 0 < gapCoeff σ φ α := by
    unfold gapCoeff
    have := div_nonneg (by linarith : 0 ≤ φ + α) h1.le
    linarith
  refine ⟨hlp, hlw, div_nonneg (mul_nonneg hα0 hlp.le) h1.le,
    mul_pos hlw (by have := div_nonneg hφ h1.le; linarith), hg,
    div_nonneg hεp.le hlp.le, div_nonneg (mul_nonneg hεw.le h1.le) hlw.le⟩

/-- Galí (2015), p. 180 (**strict price-inflation targeting is suboptimal, model form**): with
the model's `κ_p = αλ_p/(1−α)`, `κ_w = λ_w(σ + φ/(1−α))`, `λ_p`, `λ_w` and the weights of (28),
for every `θ_p, θ_w ∈ (0, 1)` there is a technology-shock path for which the (unique) strict
price-inflation-targeting path is strictly beaten by another feasible path. -/
theorem strict_price_targeting_suboptimal_model {β σ φ α εp εw θp θw : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp)
    (hεw : 0 < εw) (hθp0 : 0 < θp) (hθp1 : θp < 1) (hθw0 : 0 < θw) (hθw1 : θw < 1) :
    ∃ dn : ℕ → ℝ, (∀ t, dn (t + 2) = 0) ∧
      (∃ y pw om : ℕ → ℝ, Feasible β (kappaP α (lambdaP β θp α εp))
        (kappaW σ φ α (lambdaW β θw φ εw)) (lambdaP β θp α εp) (lambdaW β θw φ εw) dn y
          (fun _ => 0) pw om) ∧
      ∀ y pw om : ℕ → ℝ, Feasible β (kappaP α (lambdaP β θp α εp))
          (kappaW σ φ α (lambdaW β θw φ εw)) (lambdaP β θp α εp) (lambdaW β θw φ εw) dn y
            (fun _ => 0) pw om →
        Summable (fun t => β ^ t * y t ^ 2) →
        ∃ y' pp' pw' om' : ℕ → ℝ, Feasible β (kappaP α (lambdaP β θp α εp))
            (kappaW σ φ α (lambdaW β θw φ εw)) (lambdaP β θp α εp) (lambdaW β θw φ εw) dn
              y' pp' pw' om' ∧
          loss β (gapCoeff σ φ α) (priceWeight β θp α εp) (wageWeight β θw α φ εw) y' pp' pw'
            < loss β (gapCoeff σ φ α) (priceWeight β θp α εp) (wageWeight β θw α φ εw) y
              (fun _ => 0) pw := by
  obtain ⟨hlp, hlw, hkp, hkw, hg, hcp, hcw⟩ := model_coefficients hβ0 hβ1 hσ hφ hα0 hα1 hεp
    hεw hθp0 hθp1 hθw0 hθw1
  obtain ⟨h1, h2, h3⟩ := strict_price_targeting_suboptimal (Θy := gapCoeff σ φ α)
    (cp := priceWeight β θp α εp) (cw := wageWeight β θw α φ εw) hβ0 hβ1.le hkp hkw hlp hlw hg
    hcp hcw
  exact ⟨_, h1, ⟨_, _, _, h2⟩, h3⟩

/-- Galí (2015), p. 180 (**strict wage-inflation targeting is suboptimal, model form**): for
every `θ_p, θ_w ∈ (0, 1)` there is a technology-shock path for which the (unique) strict
wage-inflation-targeting path is strictly beaten by another feasible path. -/
theorem strict_wage_targeting_suboptimal_model {β σ φ α εp εw θp θw : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp)
    (hεw : 0 < εw) (hθp0 : 0 < θp) (hθp1 : θp < 1) (hθw0 : 0 < θw) (hθw1 : θw < 1) :
    ∃ dn : ℕ → ℝ, (∀ t, dn (t + 2) = 0) ∧
      (∃ y pp om : ℕ → ℝ, Feasible β (kappaP α (lambdaP β θp α εp))
        (kappaW σ φ α (lambdaW β θw φ εw)) (lambdaP β θp α εp) (lambdaW β θw φ εw) dn y pp
          (fun _ => 0) om) ∧
      ∀ y pp om : ℕ → ℝ, Feasible β (kappaP α (lambdaP β θp α εp))
          (kappaW σ φ α (lambdaW β θw φ εw)) (lambdaP β θp α εp) (lambdaW β θw φ εw) dn y pp
            (fun _ => 0) om →
        Summable (fun t => β ^ t * y t ^ 2) →
        ∃ y' pp' pw' om' : ℕ → ℝ, Feasible β (kappaP α (lambdaP β θp α εp))
            (kappaW σ φ α (lambdaW β θw φ εw)) (lambdaP β θp α εp) (lambdaW β θw φ εw) dn
              y' pp' pw' om' ∧
          loss β (gapCoeff σ φ α) (priceWeight β θp α εp) (wageWeight β θw α φ εw) y' pp' pw'
            < loss β (gapCoeff σ φ α) (priceWeight β θp α εp) (wageWeight β θw α φ εw) y pp
              (fun _ => 0) := by
  obtain ⟨hlp, hlw, hkp, hkw, hg, hcp, hcw⟩ := model_coefficients hβ0 hβ1 hσ hφ hα0 hα1 hεp
    hεw hθp0 hθp1 hθw0 hθw1
  obtain ⟨h1, h2, h3⟩ := strict_wage_targeting_suboptimal (Θy := gapCoeff σ φ α)
    (cp := priceWeight β θp α εp) (cw := wageWeight β θw α φ εw) hβ0 hβ1.le hkp hkw hlp hlw hg
    hcp hcw
  exact ⟨_, h1, ⟨_, _, _, h2⟩, h3⟩

end Gali.StickyWagesPrices.LimitingCases
