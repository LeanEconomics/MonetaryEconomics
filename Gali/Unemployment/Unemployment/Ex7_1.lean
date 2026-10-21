/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Unemployment.Expectations
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Exercise 7.1: unemployment and monetary policy with flexible prices

Galí (2015), Chapter 7, Exercise 7.1, p. 220. The model of chapters 6–7 with technology
`Y_t = N_t`, flexible prices and an employment subsidy offsetting the goods-market distortion.

## (a) The price-inflation equation

* `profit_isMaxOn_iff`: with demand `(P/P̄)^{−ε_p} C` and marginal cost `m`, the profit-maximising
  price is exactly `M_p m`, `M_p = ε_p/(ε_p − 1)` (necessary and sufficient; Bernoulli's
  inequality). `subsidy_offsets`, `flexPrice_eq_wage`: with the subsidy `τ = 1/ε_p` and `Y = N`
  (marginal cost `(1 − τ) W`), every symmetric flexible-price equilibrium has `P_t = W_t`.
* `infl_eq_of_realWage_const`: a constant real wage gives `π^p = π^w`.
* `markup_eq_phi_u`: eqs. (6)–(8), `μ^w_t = φ u_t` (exact algebra).
* `ex7_1a`, `ex7_1a_from_primitives`: `π^p_t = β E_t π^p_{t+1} − φλ_w (u_t − uⁿ)`.

## (b) The welfare loss

* `ch6PeriodLoss` (the Chapter 6 loss (28), restated), `priceWeight_tendsto_zero` (with
  flexible prices, `θ_p → 0`, the price-inflation weight `ε_p/λ_p → 0`),
  `ch6PeriodLoss_tendsto_flex`.
* `efficient_output_iff`, `phi_u_eq_gap`: `φ u_t = −(σ + φ)(y_t − yᵉ_t)` (exact).
* `alphaU`, `flexLoss_eq`: the loss is `(ε_w/(2λ_w)) [α_u u² + π²]`,
  `α_u = φ²λ_w/(ε_w(σ + φ))`; `welfare_tsum_eq`, `welfare_hasSum_iff`, `expected_welfare_eq`
  for the infinite discounted sum (and its expectation).
* Survey error 2 (the printed `β^k`): `printed_sum_not_summable`.
* Survey error 3 (the steady state is not efficient): `distortion_eq`, `distortion_calibration`
  (`Φ = 1 − e^{−φuⁿ} ∈ (0.22, 0.23)` at `φ = 5`, `uⁿ = 0.05`).

## (c) Discretion

`period_problem_iff`, `discretionEq_iff`, `discretionEq_iff_const` (existence and uniqueness
among bounded processes), `inflationBias_pos`, `expected_inflation_eq` (`E_t π_{t+k} = π* > 0`),
`piStar_primitives`, `uStar_primitives`, `uStar_lt_un`, and the ways to remove the bias
(`inflationBias_zero_iff`, `inflationBias_strictMonoOn`, `tendsto_inflationBias_zero`).

## (d) An implementing rule

`rule_implements` (for `φ_π > 1`, the rule `i_t = rᵉ_t + π* + φ_π (π_t − π*)` makes the
discretionary outcome the unique bounded equilibrium), `rule_indeterminate` (`φ_π ≤ 1`).

## (e) Commitment

`isOptimal_iff` (deterministic Lagrangian sufficiency and uniqueness, as in Chapter 5),
`commitment_tendsto` (no long-run bias: `π_t → 0`, `u_t → uⁿ`), `commInfl_lt_piStar`,
`commitment_beats_discretion`.
-/

namespace Gali.Unemployment.Ex7_1

open Filter Topology

/-! ### (a) Flexible price setting with the optimal subsidy -/

/-- Galí (2015), Exercise 7.1, p. 220 (with eq. (2), p. 203): the profit of a firm charging `P`
when the price index is `P̄`, demand is `(P/P̄)^{−ε_p} C` and marginal cost is `m` (with
`Y = N`, marginal cost is the subsidised wage `(1 − τ) W`). -/
noncomputable def profit (εp Pbar C m P : ℝ) : ℝ := (P - m) * ((P / Pbar) ^ (-εp) * C)

/-- Galí (2015), Exercise 7.1(a), p. 220 (Bernoulli's inequality): for `ε > 1`, `s > 0`,
`s ≠ 1`, `(εs − ε + 1) s^{−ε} < 1`. -/
theorem bernoulli_key {ε s : ℝ} (hε : 1 < ε) (hs : 0 < s) (hs1 : s ≠ 1) :
    (ε * s - ε + 1) * s ^ (-ε) < 1 := by
  have hb := one_add_mul_self_lt_rpow_one_add (s := s - 1) (by linarith)
    (sub_ne_zero.mpr hs1) hε
  have e1 : (1 : ℝ) + (s - 1) = s := by ring
  rw [e1] at hb
  have hpos : 0 < s ^ (-ε) := Real.rpow_pos_of_pos hs _
  have hone : s ^ ε * s ^ (-ε) = 1 := by
    rw [Real.rpow_neg hs.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hs ε).ne']
  calc (ε * s - ε + 1) * s ^ (-ε) < s ^ ε * s ^ (-ε) :=
        mul_lt_mul_of_pos_right (by linarith) hpos
    _ = 1 := hone

/-- Galí (2015), Exercise 7.1(a), p. 220 (flexible prices): any price other than `M_p m`,
`M_p = ε_p/(ε_p − 1)`, gives strictly lower profits. -/
theorem profit_lt_opt {εp Pbar C m P : ℝ} (hε : 1 < εp) (hPbar : 0 < Pbar) (hC : 0 < C)
    (hm : 0 < m) (hP : 0 < P) (hne : P ≠ εp / (εp - 1) * m) :
    profit εp Pbar C m P < profit εp Pbar C m (εp / (εp - 1) * m) := by
  have hε1 : 0 < εp - 1 := by linarith
  have hPs0 : 0 < εp / (εp - 1) * m := by positivity
  have hs : 0 < P / (εp / (εp - 1) * m) := div_pos hP hPs0
  have hs1 : P / (εp / (εp - 1) * m) ≠ 1 := fun h => hne ((div_eq_one_iff_eq hPs0.ne').mp h)
  have hK : 0 < (εp / (εp - 1) * m / Pbar) ^ (-εp) * C := by positivity
  have hsplit : (P / Pbar) ^ (-εp) =
      (P / (εp / (εp - 1) * m)) ^ (-εp) * (εp / (εp - 1) * m / Pbar) ^ (-εp) := by
    rw [← Real.mul_rpow hs.le (div_pos hPs0 hPbar).le]
    congr 1
    field_simp
  have h1 : profit εp Pbar C m P = m / (εp - 1) * ((εp / (εp - 1) * m / Pbar) ^ (-εp) * C) *
      ((εp * (P / (εp / (εp - 1) * m)) - εp + 1) * (P / (εp / (εp - 1) * m)) ^ (-εp)) := by
    unfold profit
    rw [hsplit]
    field_simp
    ring
  have h2 : profit εp Pbar C m (εp / (εp - 1) * m) =
      m / (εp - 1) * ((εp / (εp - 1) * m / Pbar) ^ (-εp) * C) := by
    unfold profit
    field_simp
    ring
  rw [h1, h2]
  have hkey := bernoulli_key hε hs hs1
  have hc : 0 < m / (εp - 1) * ((εp / (εp - 1) * m / Pbar) ^ (-εp) * C) := by positivity
  nlinarith

/-- Galí (2015), Exercise 7.1(a), p. 220 (**flexible price setting, necessary and
sufficient**): for `ε_p > 1` and positive `P̄`, `C`, `m`, a price `P > 0` maximises profits over
all positive prices iff `P = M_p m` with `M_p = ε_p/(ε_p − 1)`. -/
theorem profit_isMaxOn_iff {εp Pbar C m P : ℝ} (hε : 1 < εp) (hPbar : 0 < Pbar) (hC : 0 < C)
    (hm : 0 < m) (hP : 0 < P) :
    IsMaxOn (profit εp Pbar C m) (Set.Ioi 0) P ↔ P = εp / (εp - 1) * m := by
  have hε1 : 0 < εp - 1 := by linarith
  have hPs0 : 0 < εp / (εp - 1) * m := by positivity
  constructor
  · intro h
    by_contra hne
    have h1 := profit_lt_opt hε hPbar hC hm hP hne
    have h2 := isMaxOn_iff.mp h _ (Set.mem_Ioi.mpr hPs0)
    linarith
  · rintro rfl
    refine isMaxOn_iff.mpr fun x hx => ?_
    by_cases hxe : x = εp / (εp - 1) * m
    · rw [hxe]
    · exact (profit_lt_opt hε hPbar hC hm hx hxe).le

/-- Galí (2015), Exercise 7.1, p. 220 (**the optimal subsidy**): `τ = 1/ε_p` exactly offsets the
goods-market markup, `M_p (1 − τ) = 1`. -/
theorem subsidy_offsets {εp : ℝ} (hε : 1 < εp) : εp / (εp - 1) * (1 - 1 / εp) = 1 := by
  have hε1 : εp - 1 ≠ 0 := by linarith
  have hε0 : εp ≠ 0 := by linarith
  field_simp

/-- Galí (2015), Exercise 7.1(a), p. 220 (**symmetric flexible-price equilibrium**): if at every
date and state the common price `P_t` maximises profits given the price index `P_t`, demand `C_t`
and marginal cost `(1 − τ) W_t` with `τ = 1/ε_p` (with `Y = N` one unit of labour per unit of
output), then `P_t = W_t`: the real wage is constant and equal to one. -/
theorem flexPrice_eq_wage {Ω : Type*} {εp : ℝ} (hε : 1 < εp) {P W C : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hW : ∀ t ω, 0 < W t ω) (hC : ∀ t ω, 0 < C t ω)
    (hopt : ∀ t ω, IsMaxOn (profit εp (P t ω) (C t ω) ((1 - 1 / εp) * W t ω)) (Set.Ioi 0)
      (P t ω)) : P = W := by
  have hτ : 0 < 1 - 1 / εp := by
    have : 1 / εp < 1 := by rw [div_lt_one (by linarith)]; exact hε
    linarith
  funext t ω
  have h := (profit_isMaxOn_iff hε (hP t ω) (hC t ω) (mul_pos hτ (hW t ω)) (hP t ω)).mp
    (hopt t ω)
  rw [h, ← mul_assoc, subsidy_offsets hε, one_mul]

/-- Galí (2015), Exercise 7.1(a), p. 220: inflation of a log-level process `p`, indexed from
date `−1` (`p 0 = p_{−1}`, `p (t + 1) = p_t`): `π_t = p_t − p_{t−1}`. -/
def inflOf {Ω : Type*} (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := p (t + 1) - p t

/-- Galí (2015), Exercise 7.1(a), p. 220: if the (log) real wage `w_t − p_t` is constant, price
and wage inflation coincide, `π^p = π^w`. -/
theorem infl_eq_of_realWage_const {Ω : Type*} {p w : ℕ → Ω → ℝ} {c : Ω → ℝ}
    (h : ∀ t, w t - p t = c) : inflOf p = inflOf w := by
  funext t ω
  have h1 := congrFun (h (t + 1)) ω
  have h0 := congrFun (h t) ω
  simp only [inflOf, Pi.sub_apply] at h1 h0 ⊢
  linarith

/-- Galí (2015), eqs. (6)–(8), pp. 204–205 (**exact algebra**): with the average markup
`μ^w = (w − p) − (σc + φn + ξ)`, the participation equation (6) `w − p = σc + φl + ξ` and the
unemployment rate (7) `u = l − n`, the markup is `μ^w = φu`. -/
theorem markup_eq_phi_u {σ φ ξ ω c n l u μ : ℝ} (hμ : μ = ω - (σ * c + φ * n + ξ))
    (h6 : ω = σ * c + φ * l + ξ) (h7 : u = l - n) : μ = φ * u := by
  rw [hμ, h6, h7]
  ring

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 7.1(a), p. 220 (**the price-inflation equation**): with a constant
real wage, the wage-inflation equation (4) `π^w_t = β E_t π^w_{t+1} − λ_w (μ^w_t − μ^w)`, the
markup–unemployment relation (8) `μ^w_t = φ u_t` and the natural rate (10) `μ^w = φuⁿ`, price
inflation satisfies `π^p_t = β E_t π^p_{t+1} − φλ_w (u_t − uⁿ)`. -/
theorem ex7_1a {β lamW φ μbar un : ℝ} (hun : μbar = φ * un) {p w μ u : ℕ → Ω → ℝ}
    {c : Ω → ℝ} (hrw : ∀ t, w t - p t = c)
    (h4 : ∀ t, inflOf w t = β • 𝔼.E t (inflOf w (t + 1)) - lamW • (μ t - fun _ => μbar))
    (h8 : ∀ t, μ t = φ • u t) :
    ∀ t, inflOf p t = β • 𝔼.E t (inflOf p (t + 1)) - (φ * lamW) • (u t - fun _ => un) := by
  rw [infl_eq_of_realWage_const hrw]
  intro t
  rw [h4 t, h8 t, hun]
  funext ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), Exercise 7.1(a), p. 220 (**from the primitives**): flexible prices with the
optimal subsidy (`flexPrice_eq_wage`), log prices and wages `p = log P`, `w = log W`, the
wage-inflation equation (4), the markup definition, participation (6), unemployment (7) and
the natural rate (10) give `π^p_t = β E_t π^p_{t+1} − φλ_w (u_t − uⁿ)`. -/
theorem ex7_1a_from_primitives {εp β lamW σ φ μbar un : ℝ} (hε : 1 < εp) (hun : μbar = φ * un)
    {P W C : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hW : ∀ t ω, 0 < W t ω)
    (hC : ∀ t ω, 0 < C t ω)
    (hopt : ∀ t ω, IsMaxOn (profit εp (P t ω) (C t ω) ((1 - 1 / εp) * W t ω)) (Set.Ioi 0)
      (P t ω))
    {p w μ u c n l ξ : ℕ → Ω → ℝ} (hp : ∀ t ω, p t ω = Real.log (P t ω))
    (hw : ∀ t ω, w t ω = Real.log (W t ω))
    (h4 : ∀ t, inflOf w t = β • 𝔼.E t (inflOf w (t + 1)) - lamW • (μ t - fun _ => μbar))
    (hμ : ∀ t ω, μ t ω = (w (t + 1) ω - p (t + 1) ω) - (σ * c t ω + φ * n t ω + ξ t ω))
    (h6 : ∀ t ω, w (t + 1) ω - p (t + 1) ω = σ * c t ω + φ * l t ω + ξ t ω)
    (h7 : ∀ t ω, u t ω = l t ω - n t ω) :
    ∀ t, inflOf p t = β • 𝔼.E t (inflOf p (t + 1)) - (φ * lamW) • (u t - fun _ => un) := by
  have hPW := flexPrice_eq_wage hε hP hW hC hopt
  have hrw : ∀ t, w t - p t = fun _ => 0 := fun t => by
    funext ω
    simp [hp, hw, hPW]
  refine ex7_1a 𝔼 hun hrw h4 fun t => ?_
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  exact markup_eq_phi_u (hμ t ω) (h6 t ω) (h7 t ω)

/-! ### (b) The welfare loss -/

/-- Galí (2015), p. 166 with `α = 0` (so `Θ = 1`): `λ_p = (1 − θ_p)(1 − βθ_p)/θ_p`. -/
noncomputable def lambdaP (β θp : ℝ) : ℝ := (1 - θp) * (1 - β * θp) / θp

/-- Galí (2015), eq. (28), p. 179 (the Chapter 6 period loss, restated from the Chapter 6
project): `½[(σ + (φ+α)/(1−α)) ỹ² + (ε_p/λ_p)(π^p)² + (ε_w(1−α)/λ_w)(π^w)²]`. -/
noncomputable def ch6PeriodLoss (σ φ α εp εw lamP lamW ygap pp pw : ℝ) : ℝ :=
  ((σ + (φ + α) / (1 - α)) * ygap ^ 2 + εp / lamP * pp ^ 2 + εw * (1 - α) / lamW * pw ^ 2) / 2

/-- Galí (2015), Exercise 7.1(b), p. 220: the Chapter 6 period loss with `α = 0` and without
the price-dispersion term (flexible prices): `½[(σ + φ) ỹ² + (ε_w/λ_w)(π^w)²]`. -/
noncomputable def flexLoss (σ φ εw lamW ygap pw : ℝ) : ℝ :=
  ((σ + φ) * ygap ^ 2 + εw / lamW * pw ^ 2) / 2

/-- Galí (2015), Exercise 7.1(b), p. 220: at `α = 0` the Chapter 6 loss is the flexible-price
loss plus the price-dispersion term `(ε_p/λ_p)(π^p)²/2`. -/
theorem ch6PeriodLoss_alpha_zero (σ φ εp εw lamP lamW ygap pp pw : ℝ) :
    ch6PeriodLoss σ φ 0 εp εw lamP lamW ygap pp pw =
      flexLoss σ φ εw lamW ygap pw + εp / lamP * pp ^ 2 / 2 := by
  unfold ch6PeriodLoss flexLoss
  simp only [add_zero, sub_zero, div_one, mul_one]
  ring

/-- Galí (2015), Exercise 7.1(b), p. 220 (**flexible prices remove the price-inflation term**):
as the Calvo parameter `θ_p → 0`, the weight `ε_p/λ_p = ε_p θ_p/((1 − θ_p)(1 − βθ_p)) → 0`. -/
theorem priceWeight_tendsto_zero (β εp : ℝ) :
    Tendsto (fun θ => εp / lambdaP β θ) (𝓝[>] 0) (𝓝 0) := by
  have he : (fun θ => εp / lambdaP β θ) = fun θ : ℝ => εp * θ / ((1 - θ) * (1 - β * θ)) := by
    funext θ
    rw [lambdaP, div_div_eq_mul_div]
  have hc : ContinuousAt (fun θ : ℝ => εp * θ / ((1 - θ) * (1 - β * θ))) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    norm_num
  have ht := hc.tendsto
  simp only [mul_zero, zero_div] at ht
  rw [he]
  exact ht.mono_left nhdsWithin_le_nhds

/-- Galí (2015), Exercise 7.1(b), p. 220: as `θ_p → 0` the Chapter 6 period loss with `α = 0`
converges, for any values of the arguments, to the flexible-price loss. -/
theorem ch6PeriodLoss_tendsto_flex (β σ φ εp εw lamW ygap pp pw : ℝ) :
    Tendsto (fun θ => ch6PeriodLoss σ φ 0 εp εw (lambdaP β θ) lamW ygap pp pw) (𝓝[>] 0)
      (𝓝 (flexLoss σ φ εw lamW ygap pw)) := by
  simp only [ch6PeriodLoss_alpha_zero]
  have h := ((priceWeight_tendsto_zero β εp).mul_const (pp ^ 2)).div_const 2
  simp only [zero_mul, zero_div] at h
  simpa using (tendsto_const_nhds (x := flexLoss σ φ εw lamW ygap pw)).add h

/-- Galí (2015), Exercise 7.1(b), p. 220: with `Y = N`, the efficient allocation equates the
marginal rate of substitution `σy + φy + ξ` to the (log) marginal product of labour `0`, i.e.
`yᵉ = −ξ/(σ + φ)`. -/
theorem efficient_output_iff {σ φ ξ y : ℝ} (hσφ : σ + φ ≠ 0) :
    σ * y + φ * y + ξ = 0 ↔ y = -ξ / (σ + φ) := by
  rw [eq_div_iff hσφ]
  constructor <;> intro h <;> linarith

/-- Galí (2015), Exercise 7.1(b), p. 220 (**`φ u = −(σ + φ)(y − yᵉ)`, exact**): with flexible
prices and the subsidy the log real wage is `0` (`flexPrice_eq_wage`); with `C = Y = N`, the
markup definition and (8), `φ u_t = −(σ + φ)(y_t − yᵉ_t)` with `yᵉ_t = −ξ_t/(σ + φ)`. -/
theorem phi_u_eq_gap {σ φ ξ ω c n y u μ : ℝ} (hσφ : σ + φ ≠ 0) (hω : ω = 0) (hc : c = y)
    (hn : n = y) (hμ : μ = ω - (σ * c + φ * n + ξ)) (h8 : μ = φ * u) :
    φ * u = -(σ + φ) * (y - -ξ / (σ + φ)) := by
  rw [← h8, hμ, hω, hc, hn]
  field_simp
  ring

/-- Galí (2015), Exercise 7.1(b), p. 220: the weight `α_u = φ²λ_w/(ε_w(σ + φ))`. -/
noncomputable def alphaU (σ φ εw lamW : ℝ) : ℝ := φ ^ 2 * lamW / (εw * (σ + φ))

/-- Galí (2015), Exercise 7.1(b), p. 220: `α_u > 0`. -/
theorem alphaU_pos {σ φ εw lamW : ℝ} (hσ : 0 < σ) (hφ : 0 < φ) (hεw : 0 < εw)
    (hlam : 0 < lamW) : 0 < alphaU σ φ εw lamW := by
  unfold alphaU
  positivity

/-- Galí (2015), Exercise 7.1(b), p. 220 (**the period loss, exact algebra**): if
`φ u = −(σ + φ) ỹ` and `π^w = π`, the flexible-price loss equals
`(ε_w/(2λ_w)) [α_u u² + π²]` with `α_u = φ²λ_w/(ε_w(σ + φ))`. -/
theorem flexLoss_eq {σ φ εw lamW ygap u infl : ℝ} (hσφ : σ + φ ≠ 0) (hεw : εw ≠ 0)
    (hlam : lamW ≠ 0) (hgap : φ * u = -(σ + φ) * ygap) :
    flexLoss σ φ εw lamW ygap infl = εw / (2 * lamW) * (alphaU σ φ εw lamW * u ^ 2 + infl ^ 2) := by
  have hy : ygap = -(φ * u) / (σ + φ) := by
    rw [eq_div_iff hσφ]
    linarith
  unfold flexLoss alphaU
  rw [hy]
  field_simp

/-- Galí (2015), Exercise 7.1(b), p. 220 (**the discounted loss, up to a positive scalar**):
along any path with `φ u_t = −(σ + φ) ỹ_t`,
`∑ βᵗ L_t = (ε_w/(2λ_w)) ∑ βᵗ [α_u u_t² + π_t²]` (an identity of `tsum`s, valid whether or not
the sums converge, since the summands are proportional). -/
theorem welfare_tsum_eq {β σ φ εw lamW : ℝ} (hσφ : σ + φ ≠ 0) (hεw : εw ≠ 0)
    (hlam : lamW ≠ 0) {ygap u infl : ℕ → ℝ} (hgap : ∀ t, φ * u t = -(σ + φ) * ygap t) :
    ∑' t, β ^ t * flexLoss σ φ εw lamW (ygap t) (infl t) =
      εw / (2 * lamW) * ∑' t, β ^ t * (alphaU σ φ εw lamW * u t ^ 2 + infl t ^ 2) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun t => ?_
  rw [flexLoss_eq hσφ hεw hlam (hgap t)]
  ring

/-- Galí (2015), Exercise 7.1(b), p. 220 (convergence): along any path with
`φ u_t = −(σ + φ) ỹ_t`, the discounted Chapter 6 loss converges to `(ε_w/(2λ_w)) S` iff
`∑ βᵗ [α_u u_t² + π_t²]` converges to `S`. -/
theorem welfare_hasSum_iff {β σ φ εw lamW S : ℝ} (hσφ : σ + φ ≠ 0) (hεw : εw ≠ 0)
    (hlam : lamW ≠ 0) {ygap u infl : ℕ → ℝ} (hgap : ∀ t, φ * u t = -(σ + φ) * ygap t) :
    HasSum (fun t => β ^ t * flexLoss σ φ εw lamW (ygap t) (infl t)) (εw / (2 * lamW) * S) ↔
      HasSum (fun t => β ^ t * (alphaU σ φ εw lamW * u t ^ 2 + infl t ^ 2)) S := by
  have hc : εw / (2 * lamW) ≠ 0 := div_ne_zero hεw (mul_ne_zero two_ne_zero hlam)
  have he : (fun t => β ^ t * flexLoss σ φ εw lamW (ygap t) (infl t)) =
      fun t => εw / (2 * lamW) * (β ^ t * (alphaU σ φ εw lamW * u t ^ 2 + infl t ^ 2)) := by
    funext t
    rw [flexLoss_eq hσφ hεw hlam (hgap t)]
    ring
  rw [he]
  exact hasSum_mul_left_iff hc

/-- Galí (2015), Exercise 7.1(b), p. 220 (**the expected loss**): for stochastic paths with
`φ u_t = −(σ + φ) ỹ_t` state by state,
`E_0 ∑ βᵗ L_t = (ε_w/(2λ_w)) E_0 ∑ βᵗ [α_u u_t² + π_t²]`. -/
theorem expected_welfare_eq {β σ φ εw lamW : ℝ} (hσφ : σ + φ ≠ 0) (hεw : εw ≠ 0)
    (hlam : lamW ≠ 0) {ygap u infl : ℕ → Ω → ℝ}
    (hgap : ∀ t ω, φ * u t ω = -(σ + φ) * ygap t ω) :
    𝔼.E 0 (fun ω => ∑' t, β ^ t * flexLoss σ φ εw lamW (ygap t ω) (infl t ω)) =
      (εw / (2 * lamW)) •
        𝔼.E 0 (fun ω => ∑' t, β ^ t * (alphaU σ φ εw lamW * u t ω ^ 2 + infl t ω ^ 2)) := by
  rw [← map_smul]
  congr 1
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  exact welfare_tsum_eq hσφ hεw hlam (fun t => hgap t ω)

/-- Galí (2015), Exercise 7.1(b), p. 220 (**survey error 2: the printed `β^k`**): the printed
loss `E_0 ∑_t β^k [α_u u_t² + π_t²]` has a discount factor that does not depend on the summation
index. Along any path with a constant nonzero period loss (e.g. the discretionary equilibrium
of part (c), `discretionEq_iff_const`), the printed sum diverges for every `k`, while the
intended `∑_t βᵗ [⋯]` converges (`correct_sum_hasSum`). -/
theorem printed_sum_not_summable {β L : ℝ} (hβ : 0 < β) (hL : 0 < L) (k : ℕ) :
    ¬ Summable (fun _ : ℕ => β ^ k * L) := by
  rw [summable_const_iff]
  exact (mul_pos (pow_pos hβ k) hL).ne'

/-- Galí (2015), Exercise 7.1(b), p. 220 (the corrected discounting `βᵗ`): a constant period
loss `L` has the finite discounted sum `L/(1 − β)`. -/
theorem correct_sum_hasSum {β L : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    HasSum (fun t : ℕ => β ^ t * L) (L / (1 - β)) := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right L
  convert h using 1
  field_simp

/-- Galí (2015), p. 209 and Exercise 7.1(b) (**survey error 3, the size of the steady-state
distortion**): with the goods-market distortion offset, the remaining steady-state distortion is
the wage markup, `Φ = 1 − 1/M_w`, `M_w = ε_w/(ε_w − 1)`; so `Φ = 1/ε_w`, and with
`M_w = exp(μ^w) = exp(φuⁿ)` (eq. (10)), `Φ = 1 − e^{−φuⁿ}`. -/
theorem distortion_eq {εw φ un : ℝ} (hεw : 1 < εw)
    (hMw : Real.log (εw / (εw - 1)) = φ * un) :
    1 - 1 / (εw / (εw - 1)) = 1 / εw ∧ 1 - 1 / (εw / (εw - 1)) = 1 - Real.exp (-(φ * un)) := by
  have hε1 : 0 < εw - 1 := by linarith
  have hM : 0 < εw / (εw - 1) := div_pos (by linarith) hε1
  refine ⟨by field_simp; ring, ?_⟩
  rw [← hMw, Real.exp_neg, Real.exp_log hM, one_div]

/-- Galí (2015), p. 209 and Exercise 7.1(b) (**survey error 3, numerically**): at the Chapter 7
calibration `φ = 5`, `uⁿ = 0.05`, the steady-state distortion `Φ = 1 − e^{−φuⁿ}` lies in
`(0.22, 0.23)`: it is not small. The Chapter 6 loss "taken as a starting point" was derived
around an efficient steady state (or for a small distortion), so the exercise's `α_u` holds
only under that approximation; with `Φ ≈ 0.22` a second-order approximation around the
distorted steady state (Benigno–Woodford) would in general change the weights. -/
theorem distortion_calibration :
    (0.22 : ℝ) < 1 - Real.exp (-((5 : ℝ) * 0.05)) ∧
      1 - Real.exp (-((5 : ℝ) * 0.05)) < (0.23 : ℝ) := by
  have e : -((5 : ℝ) * 0.05) = -(1 / 4) := by norm_num
  rw [e]
  have h := Real.exp_bound (x := -(1 / 4)) (by norm_num [abs_div]) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  constructor <;> norm_num <;> linarith

/-! ### (c) Optimal discretionary policy -/

/-- Galí (2015), Exercise 7.1(c), p. 220: the period objective `π² + ϑ u²` (`ϑ = α_u`) after
substituting the constraint `π = −κ u + v` (`κ = φλ_w`, `v = β E_t π_{t+1} + κ uⁿ` taken as
given under discretion). -/
def periodObj (κ ϑ v u : ℝ) : ℝ := (-(κ * u) + v) ^ 2 + ϑ * u ^ 2

/-- Galí (2015), Exercise 7.1(c), p. 220 (completing the square). -/
theorem periodObj_sub (κ ϑ v u u' : ℝ) :
    periodObj κ ϑ v u' - periodObj κ ϑ v u
      = (κ ^ 2 + ϑ) * (u' - u) ^ 2 + 2 * (u' - u) * ((κ ^ 2 + ϑ) * u - κ * v) := by
  unfold periodObj
  ring

/-- Galí (2015), Exercise 7.1(c), p. 220 (**necessary and sufficient**, adapted from the
Chapter 5 project): for `ϑ > 0`, `u` minimises the period objective iff
`u = (κ/ϑ)(−κ u + v)`. -/
theorem periodObj_isMinOn_iff {κ ϑ v u : ℝ} (hϑ : 0 < ϑ) :
    IsMinOn (periodObj κ ϑ v) Set.univ u ↔ u = κ / ϑ * (-(κ * u) + v) := by
  have hA : 0 < κ ^ 2 + ϑ := by positivity
  have hfoc : u = κ / ϑ * (-(κ * u) + v) ↔ (κ ^ 2 + ϑ) * u - κ * v = 0 := by
    constructor
    · intro h
      field_simp at h
      linarith
    · intro h
      field_simp
      linarith
  rw [hfoc]
  constructor
  · intro h
    set g := (κ ^ 2 + ϑ) * u - κ * v
    have hle := isMinOn_iff.mp h (u - g / (κ ^ 2 + ϑ)) (Set.mem_univ _)
    have hd := periodObj_sub κ ϑ v u (u - g / (κ ^ 2 + ϑ))
    have hval : (κ ^ 2 + ϑ) * (u - g / (κ ^ 2 + ϑ) - u) ^ 2 +
        2 * (u - g / (κ ^ 2 + ϑ) - u) * g = -(g ^ 2 / (κ ^ 2 + ϑ)) := by
      field_simp
      ring
    have hg2 : g ^ 2 / (κ ^ 2 + ϑ) ≤ 0 := by linarith
    have : g ^ 2 ≤ 0 := by
      rwa [div_le_iff₀ hA, zero_mul] at hg2
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg g))
  · intro h
    refine isMinOn_iff.mpr fun u' _ => ?_
    have hd := periodObj_sub κ ϑ v u u'
    rw [h, mul_zero, add_zero] at hd
    have : 0 ≤ (κ ^ 2 + ϑ) * (u' - u) ^ 2 := by positivity
    linarith

/-- Galí (2015), Exercise 7.1(c), p. 220 (**the period problem under discretion, necessary and
sufficient**): for `ϑ > 0`, `(π, u)` minimises `π² + ϑ u²` subject to `π = −κ u + v` iff it is
feasible and satisfies the targeting rule `u = (κ/ϑ) π`. -/
theorem period_problem_iff {κ ϑ v infl u : ℝ} (hϑ : 0 < ϑ) :
    (infl = -(κ * u) + v ∧ ∀ π' u', π' = -(κ * u') + v →
        infl ^ 2 + ϑ * u ^ 2 ≤ π' ^ 2 + ϑ * u' ^ 2) ↔
      (infl = -(κ * u) + v ∧ u = κ / ϑ * infl) := by
  constructor
  · rintro ⟨hc, hmin⟩
    refine ⟨hc, ?_⟩
    have : IsMinOn (periodObj κ ϑ v) Set.univ u := isMinOn_iff.mpr fun u' _ => by
      have := hmin _ u' rfl
      rw [hc] at this
      simpa [periodObj] using this
    rw [hc]
    exact (periodObj_isMinOn_iff hϑ).mp this
  · rintro ⟨hc, hu⟩
    refine ⟨hc, fun π' u' hc' => ?_⟩
    rw [hc] at hu
    have := isMinOn_iff.mp ((periodObj_isMinOn_iff hϑ).mpr hu) u' (Set.mem_univ u')
    simp only [periodObj] at this
    rw [hc, hc']
    exact this

/-- Galí (2015), Exercise 7.1(a), p. 220: the price-inflation equation in unemployment,
`π_t = β E_t π_{t+1} − κ (u_t − uⁿ)`, `κ = φλ_w`. -/
def NKPCu (β κ un : ℝ) (u infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) - κ • (u t - fun _ => un)

/-- Galí (2015), Exercise 7.1(c), p. 220: a **discretionary equilibrium**: the price-inflation
equation holds and, at each date and in each state, `(π_t, u_t)` minimises the period loss
`π² + ϑ u²` (`ϑ = α_u`) over the line `π = −κ u + v_t`, taking
`v_t = β E_t π_{t+1} + κ uⁿ` as given. -/
def DiscretionEq (β κ ϑ un : ℝ) (u infl : ℕ → Ω → ℝ) : Prop :=
  NKPCu 𝔼 β κ un u infl ∧ ∀ t ω, ∀ π' u' : ℝ,
    π' = -(κ * u') + (β * 𝔼.E t (infl (t + 1)) ω + κ * un) →
      infl t ω ^ 2 + ϑ * u t ω ^ 2 ≤ π' ^ 2 + ϑ * u' ^ 2

/-- Galí (2015), Exercise 7.1(c), p. 220: the discretionary targeting rule
`u_t = (κ/ϑ) π_t`. -/
def TargetingRule (κ ϑ : ℝ) (u infl : ℕ → Ω → ℝ) : Prop := ∀ t, u t = (κ / ϑ) • infl t

/-- Galí (2015), Exercise 7.1(c), p. 220: for `ϑ > 0` a discretionary equilibrium is exactly a
pair satisfying the price-inflation equation and the targeting rule `u = (κ/ϑ) π`. -/
theorem discretionEq_iff {β κ ϑ un : ℝ} (hϑ : 0 < ϑ) {u infl : ℕ → Ω → ℝ} :
    DiscretionEq 𝔼 β κ ϑ un u infl ↔ NKPCu 𝔼 β κ un u infl ∧ TargetingRule κ ϑ u infl := by
  have hpt : ∀ (h : NKPCu 𝔼 β κ un u infl) t ω,
      infl t ω = -(κ * u t ω) + (β * 𝔼.E t (infl (t + 1)) ω + κ * un) := fun h t ω => by
    have := congrFun (h t) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  constructor
  · rintro ⟨h, hmin⟩
    refine ⟨h, fun t => funext fun ω => ?_⟩
    have := ((period_problem_iff hϑ).mp ⟨hpt h t ω, hmin t ω⟩).2
    simpa using this
  · rintro ⟨h, hr⟩
    refine ⟨h, fun t ω => ((period_problem_iff hϑ).mpr ⟨hpt h t ω, ?_⟩).2⟩
    have := congrFun (hr t) ω
    simpa using this

/-- Galí (2015), Exercise 7.1(c), p. 220: the discount factor of the discretionary inflation
equation, `a = ϑβ/(ϑ + κ²)`. -/
noncomputable def aDisc (β κ ϑ : ℝ) : ℝ := ϑ * β / (ϑ + κ ^ 2)

/-- Galí (2015), Exercise 7.1(c), p. 220: `0 ≤ a < 1` for `ϑ > 0`, `0 ≤ β < 1`. -/
theorem aDisc_mem {β κ ϑ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    0 ≤ aDisc β κ ϑ ∧ aDisc β κ ϑ < 1 := by
  unfold aDisc
  have hA : 0 < ϑ + κ ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hA]
  nlinarith [sq_nonneg κ]

/-- Galí (2015), Exercise 7.1(c), p. 220: under the targeting rule the price-inflation equation
is equivalent to `π_t = (ϑβ/(ϑ + κ²)) E_t π_{t+1} + ϑκuⁿ/(ϑ + κ²)`. -/
theorem inflation_forward_iff {β κ ϑ un : ℝ} (hϑ : 0 < ϑ) {u infl : ℕ → Ω → ℝ}
    (hr : TargetingRule κ ϑ u infl) :
    NKPCu 𝔼 β κ un u infl ↔
      ∀ t, infl t = aDisc β κ ϑ • 𝔼.E t (infl (t + 1)) + fun _ => ϑ * κ * un / (ϑ + κ ^ 2) := by
  have hA : ϑ + κ ^ 2 ≠ 0 := by positivity
  have hϑ' : ϑ ≠ 0 := hϑ.ne'
  constructor
  · intro h t
    funext ω
    have p := congrFun (h t) ω
    have r := congrFun (hr t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at p r ⊢
    rw [r] at p
    unfold aDisc
    field_simp
    field_simp at p
    linarith
  · intro h t
    funext ω
    have p := congrFun (h t) ω
    have r := congrFun (hr t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at p r ⊢
    rw [r]
    unfold aDisc at p
    field_simp at p
    field_simp
    linarith

/-- Galí (2015), Exercise 7.1(c), p. 220 (**discretionary inflation**):
`π* = ϑκuⁿ/(κ² + ϑ(1 − β))`. -/
noncomputable def piStar (β κ ϑ un : ℝ) : ℝ := ϑ * κ * un / (κ ^ 2 + ϑ * (1 - β))

/-- Galí (2015), Exercise 7.1(c), p. 220 (**discretionary unemployment**):
`u* = (κ/ϑ) π* = κ² uⁿ/(κ² + ϑ(1 − β))`. -/
noncomputable def uStar (β κ ϑ un : ℝ) : ℝ := κ ^ 2 * un / (κ ^ 2 + ϑ * (1 - β))

/-- Galí (2015), Exercise 7.1(c), p. 220: `κ² + ϑ(1 − β) > 0`. -/
theorem den_pos {β κ ϑ : ℝ} (hϑ : 0 < ϑ) (hβ1 : β < 1) : 0 < κ ^ 2 + ϑ * (1 - β) := by
  have : 0 < ϑ * (1 - β) := mul_pos hϑ (by linarith)
  positivity

/-- Galí (2015), Exercise 7.1(c), p. 220: `u* = (κ/ϑ) π*` (the targeting rule). -/
theorem uStar_eq {β κ ϑ un : ℝ} (hϑ : 0 < ϑ) :
    uStar β κ ϑ un = κ / ϑ * piStar β κ ϑ un := by
  unfold uStar piStar
  field_simp

/-- Galí (2015), Exercise 7.1(c), p. 220: the constants satisfy the price-inflation equation,
`π* = β π* − κ(u* − uⁿ)`. -/
theorem piStar_nkpc {β κ ϑ un : ℝ} (hϑ : 0 < ϑ) (hβ1 : β < 1) :
    piStar β κ ϑ un = β * piStar β κ ϑ un - κ * (uStar β κ ϑ un - un) := by
  have hD := den_pos (κ := κ) hϑ hβ1
  unfold piStar uStar
  field_simp
  ring

/-- Galí (2015), Exercise 7.1(c), p. 220 (**existence**): the constant pair `(u*, π*)` is a
discretionary equilibrium. -/
theorem discretion_const_isEq {β κ ϑ un : ℝ} (hϑ : 0 < ϑ) (hβ1 : β < 1) :
    DiscretionEq 𝔼 β κ ϑ un (fun _ _ => uStar β κ ϑ un) (fun _ _ => piStar β κ ϑ un) := by
  rw [discretionEq_iff 𝔼 hϑ]
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [𝔼.const]
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact piStar_nkpc hϑ hβ1
  · funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    exact uStar_eq hϑ

/-- Galí (2015), Exercise 7.1(c), p. 220 (**existence and uniqueness of the discretionary
equilibrium**): for `ϑ > 0`, `0 ≤ β < 1`, a pair `(u, π)` with `π` bounded is a discretionary
equilibrium iff `π_t = π*` and `u_t = u*` at every date and state. -/
theorem discretionEq_iff_const {β κ ϑ un : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u infl : ℕ → Ω → ℝ} (hpb : BoundedProc infl) :
    DiscretionEq 𝔼 β κ ϑ un u infl ↔
      infl = (fun _ _ => piStar β κ ϑ un) ∧ u = (fun _ _ => uStar β κ ϑ un) := by
  obtain ⟨ha0, ha1⟩ := aDisc_mem (κ := κ) hϑ hβ0 hβ1
  have ha : |aDisc β κ ϑ| < 1 := by rw [abs_of_nonneg ha0]; exact ha1
  have hc := discretion_const_isEq 𝔼 (κ := κ) (un := un) hϑ hβ1
  have hcb : BoundedProc (fun (_ : ℕ) (_ : Ω) => piStar β κ ϑ un) :=
    ⟨|piStar β κ ϑ un|, fun _ _ => le_rfl⟩
  constructor
  · intro h
    obtain ⟨hn, hr⟩ := (discretionEq_iff 𝔼 hϑ).mp h
    obtain ⟨hn', hr'⟩ := (discretionEq_iff 𝔼 hϑ).mp hc
    have hf := (inflation_forward_iff 𝔼 hϑ hr).mp hn
    have hf' := (inflation_forward_iff 𝔼 hϑ hr').mp hn'
    have hp : infl = fun _ _ => piStar β κ ϑ un := 𝔼.forward_unique ha hf hf' hpb hcb
    refine ⟨hp, funext fun t => ?_⟩
    rw [hr t, hp]
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (uStar_eq hϑ).symm
  · rintro ⟨rfl, rfl⟩
    exact hc

/-- Galí (2015), Exercise 7.1(c), p. 220 (**the inflation bias is positive**): for `κ, ϑ > 0`,
`β < 1` and a positive natural rate `uⁿ > 0`, `π* > 0`. -/
theorem inflationBias_pos {β κ ϑ un : ℝ} (hκ : 0 < κ) (hϑ : 0 < ϑ) (hβ1 : β < 1)
    (hun : 0 < un) : 0 < piStar β κ ϑ un := by
  have hD := den_pos (κ := κ) hϑ hβ1
  unfold piStar
  positivity

/-- Galí (2015), Exercise 7.1(c), p. 220 (**average inflation is positive**): in the unique
bounded discretionary equilibrium, `E_t π_{t+k} = π* > 0` for every date `t`, horizon `k` and
state (so in particular the unconditional mean is `π*`). -/
theorem expected_inflation_eq {β κ ϑ un : ℝ} (hκ : 0 < κ) (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hun : 0 < un) {u infl : ℕ → Ω → ℝ} (hpb : BoundedProc infl)
    (h : DiscretionEq 𝔼 β κ ϑ un u infl) (t k : ℕ) (ω : Ω) :
    𝔼.E t (infl (t + k)) ω = piStar β κ ϑ un ∧ 0 < 𝔼.E t (infl (t + k)) ω := by
  obtain ⟨hp, -⟩ := (discretionEq_iff_const 𝔼 hϑ hβ0 hβ1 hpb).mp h
  subst hp
  rw [𝔼.const]
  exact ⟨rfl, inflationBias_pos hκ hϑ hβ1 hun⟩

/-- Galí (2015), Exercise 7.1(c), p. 220: discretionary unemployment lies strictly between `0`
and the natural rate, `0 < u* < uⁿ` (for `κ ≠ 0`, `ϑ > 0`, `β < 1`, `uⁿ > 0`). -/
theorem uStar_lt_un {β κ ϑ un : ℝ} (hκ : κ ≠ 0) (hϑ : 0 < ϑ) (hβ1 : β < 1) (hun : 0 < un) :
    0 < uStar β κ ϑ un ∧ uStar β κ ϑ un < un := by
  have hD := den_pos (κ := κ) hϑ hβ1
  have hk : 0 < κ ^ 2 := by positivity
  have h1 : 0 < ϑ * (1 - β) := mul_pos hϑ (by linarith)
  unfold uStar
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ hD]
  nlinarith

/-- Galí (2015), Exercise 7.1(c), p. 220 (**closed form in the primitives**): with `κ = φλ_w`
and `ϑ = α_u = φ²λ_w/(ε_w(σ + φ))`, `π* = φλ_w uⁿ/(1 − β + λ_w ε_w (σ + φ))`. -/
theorem piStar_primitives {β σ φ εw lamW un : ℝ} (hσ : 0 < σ) (hφ : 0 < φ) (hεw : 0 < εw)
    (hlam : 0 < lamW) (hβ1 : β < 1) :
    piStar β (φ * lamW) (alphaU σ φ εw lamW) un =
      φ * lamW * un / (1 - β + lamW * εw * (σ + φ)) := by
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 - β + lamW * εw * (σ + φ) := by positivity
  have hD := den_pos (κ := φ * lamW) (alphaU_pos hσ hφ hεw hlam) hβ1
  unfold piStar
  unfold alphaU at hD ⊢
  field_simp
  ring

/-- Galí (2015), Exercise 7.1(c), p. 220 (**closed form in the primitives**):
`u* = λ_w ε_w (σ + φ) uⁿ/(1 − β + λ_w ε_w (σ + φ))`. -/
theorem uStar_primitives {β σ φ εw lamW un : ℝ} (hσ : 0 < σ) (hφ : 0 < φ) (hεw : 0 < εw)
    (hlam : 0 < lamW) (hβ1 : β < 1) :
    uStar β (φ * lamW) (alphaU σ φ εw lamW) un =
      lamW * εw * (σ + φ) * un / (1 - β + lamW * εw * (σ + φ)) := by
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 - β + lamW * εw * (σ + φ) := by positivity
  have hD := den_pos (κ := φ * lamW) (alphaU_pos hσ hφ hεw hlam) hβ1
  unfold uStar
  unfold alphaU at hD ⊢
  field_simp
  ring

/-- Galí (2015), Exercise 7.1(c), p. 220 (**removing the bias: eliminate the wage markup**): for
`κ, ϑ > 0`, `β < 1`, the bias vanishes iff `uⁿ = 0`. -/
theorem inflationBias_zero_iff {β κ ϑ un : ℝ} (hκ : 0 < κ) (hϑ : 0 < ϑ) (hβ1 : β < 1) :
    piStar β κ ϑ un = 0 ↔ un = 0 := by
  have hD := den_pos (κ := κ) hϑ hβ1
  unfold piStar
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' hϑ.ne'
        · exact absurd h'' hκ.ne'
      · exact h'
    · exact absurd h hD.ne'
  · intro h
    left
    rw [h, mul_zero]

/-- Galí (2015), Exercise 7.1(c), p. 220 (**an employment subsidy removes the wage markup**): a
subsidy `τ_w = 1/ε_w` makes the effective desired wage markup `log(M_w (1 − τ_w)) = 0`, hence
`uⁿ = 0` (eq. (10)) and no inflation bias. -/
theorem wageSubsidy_markup_zero {εw : ℝ} (hεw : 1 < εw) :
    Real.log (εw / (εw - 1) * (1 - 1 / εw)) = 0 := by
  rw [subsidy_offsets hεw, Real.log_one]

/-- Galí (2015), Exercise 7.1(c), p. 220 (**removing the bias: a conservative central
banker**): for `κ > 0`, `uⁿ > 0`, `β < 1`, the bias `π*` is strictly increasing in the weight
`ϑ` placed on unemployment. -/
theorem inflationBias_strictMonoOn {β κ un : ℝ} (hκ : 0 < κ) (hβ1 : β < 1) (hun : 0 < un) :
    StrictMonoOn (fun ϑ => piStar β κ ϑ un) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 < a := ha
  have hb0 : 0 < b := hb
  have hDa := den_pos (κ := κ) ha0 hβ1
  have hDb := den_pos (κ := κ) hb0 hβ1
  simp only [piStar]
  rw [div_lt_div_iff₀ hDa hDb]
  have hk : 0 < κ ^ 2 * (κ * un) := by positivity
  nlinarith [mul_lt_mul_of_pos_right hab hk]

/-- Galí (2015), Exercise 7.1(c), p. 220 (**the bias vanishes as the weight on unemployment
goes to zero**): `π* → 0` as `ϑ → 0⁺` (for `κ ≠ 0`). -/
theorem tendsto_inflationBias_zero {β κ un : ℝ} (hκ : κ ≠ 0) :
    Tendsto (fun ϑ => piStar β κ ϑ un) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun ϑ : ℝ => ϑ * κ * un / (κ ^ 2 + ϑ * (1 - β))) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simpa using pow_ne_zero 2 hκ
  have ht := hc.tendsto
  simp only [zero_mul, zero_div] at ht
  exact ht.mono_left nhdsWithin_le_nhds

/-! ### (d) An interest-rate rule implementing the discretionary outcome -/

/-- Galí (2015), Exercise 7.1(d), p. 220 (with `C = Y` and the Euler equation (3), p. 203): the
dynamic IS equation in a gap `x` with real rate `r`,
`x_t = E_t x_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − r_t)` (restated from the Chapter 5 project). -/
def DIS (σ : ℝ) (x i infl r : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - r t)

/-- Galí (2015), Exercise 7.1(d), p. 220: the real rate consistent with an output path `y^v`,
`r_t = ζ_t + σ E_t{Δy^v_{t+1}}` (restated from the Chapter 5 project). -/
def rateOf (σ : ℝ) (ζ yv : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => ζ t + σ • (𝔼.E t (yv (t + 1)) - yv t)

/-- Galí (2015), Exercise 7.1(d), p. 220 (**exact**, restated from the Chapter 5 project): for
`σ ≠ 0`, the DIS in `y − y^n` with rate `r^n` holds iff the DIS in the welfare-relevant gap
`y − yᵉ` with the efficient rate `rᵉ` holds. With `y^n = 0` and `ζ ≡ ρ` this turns the Euler
equation `y_t = E_t y_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ρ)` into the DIS in `y − yᵉ`. -/
theorem dis_gap_iff {σ : ℝ} (hσ : σ ≠ 0) {y yn ye i infl ζ : ℕ → Ω → ℝ} :
    DIS 𝔼 σ (fun t => y t - yn t) i infl (rateOf 𝔼 σ ζ yn) ↔
      DIS 𝔼 σ (fun t => y t - ye t) i infl (rateOf 𝔼 σ ζ ye) := by
  have hinv : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [rateOf, map_sub, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    linear_combination e - (𝔼.E t (ye (t + 1)) ω - ye t ω - 𝔼.E t (yn (t + 1)) ω + yn t ω) *
      hinv
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [rateOf, map_sub, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    linear_combination e - (𝔼.E t (yn (t + 1)) ω - yn t ω - 𝔼.E t (ye (t + 1)) ω + ye t ω) *
      hinv

/-- Galí (2015), Exercise 7.1(d), p. 220: the price-inflation equation in an output gap `x`
with slope `κ` and a forcing term `c`, `π_t = β E_t π_{t+1} + κ x_t + c_t`. -/
def NKPCx (β κ : ℝ) (x c infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + c t

/-- Galí (2015), Exercise 7.1(d), p. 220: the stacked vector `(x_t, π_t)` (restated from the
Chapter 5 project). -/
def stack (x infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![x t, infl t]

/-- Two bounded processes stack to a bounded vector process (restated from the Chapter 5
project; Galí 2015, Exercise 7.1(d), p. 220). -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Two adapted processes stack to an adapted vector process (restated from the Chapter 5
project; Galí 2015, Exercise 7.1(d), p. 220). -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-- Galí (2015), Exercise 7.1(d), p. 220 (the system under a rule responding to inflation with
`φ_π`; ch. 4, eq. (13) with `φ_y = 0`; restated from the Chapter 5 project):
`A_T = (σ + κφ_π)⁻¹ [[σ, 1 − βφ_π], [σκ, κ + βσ]]`. -/
noncomputable def AT (β σ κ φπ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ / (σ + κ * φπ), (1 - β * φπ) / (σ + κ * φπ);
    σ * κ / (σ + κ * φπ), (κ + β * σ) / (σ + κ * φπ)]

/-- Galí (2015), Exercise 7.1(d), p. 220: the forcing of the system under a rule
`i_t = r_t + ψ c_t + φ_π π_t` (restated from the Chapter 5 project). -/
noncomputable def wT (σ κ φπ ψ : ℝ) (c : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![(-(ψ + φπ) / (σ + κ * φπ)) • c t, ((σ - κ * ψ) / (σ + κ * φπ)) • c t]

/-- Galí (2015), Exercise 7.1(d), p. 220 (**exact**, restated from the Chapter 5 project): under
a rule `i_t = r_t + ψ c_t + φ_π π_t`, the Phillips curve and the DIS hold iff `(x, π)` solves
`(x_t, π_t) = A_T E_t (x_{t+1}, π_{t+1}) + w_t`. -/
theorem rule_iff_solves {β σ κ φπ ψ : ℝ} (hσ : σ ≠ 0) (hS : σ + κ * φπ ≠ 0)
    {c x infl i r : ℕ → Ω → ℝ} (hrule : ∀ t, i t = r t + ψ • c t + φπ • infl t) :
    (NKPCx 𝔼 β κ x c infl ∧ DIS 𝔼 σ x i infl r) ↔
      𝔼.Solves (AT β σ κ φπ) (wT σ κ φπ ψ c) (stack x infl) := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    simp only [hrule t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p
    have s : σ * x t ω + φπ * infl t ω
        = σ * 𝔼.E t (x (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω - ψ * c t ω := by
      linear_combination σ * e -
        (ψ * c t ω + φπ * infl t ω - 𝔼.E t (infl (t + 1)) ω) * hinv
    fin_cases j
    · simp [stack, AT, wT]
      field_simp
      linear_combination s - φπ * p
    · simp [stack, AT, wT]
      field_simp
      linear_combination κ * s + σ * p
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AT, wT] at e0 e1
      field_simp at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      apply mul_left_cancel₀ hS
      linear_combination e1 - κ * e0
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AT, wT] at e0 e1
      field_simp at e0 e1
      simp only [hrule t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have s : σ * x t ω + φπ * infl t ω
          = σ * 𝔼.E t (x (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω - ψ * c t ω := by
        apply mul_left_cancel₀ hS
        linear_combination σ * e0 + φπ * e1
      linear_combination σ⁻¹ * s - (x t ω - 𝔼.E t (x (t + 1)) ω) * hinv

/-- Galí (2015), Exercise 7.1(d), p. 220: `tr A_T = (σ(1 + β) + κ)/(σ + κφ_π)`. -/
theorem tr2_AT {β σ κ φπ : ℝ} (hS : σ + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ) = (σ * (1 + β) + κ) / (σ + κ * φπ) := by
  simp only [tr2, AT, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), Exercise 7.1(d), p. 220: `det A_T = σβ/(σ + κφ_π)`. -/
theorem det2_AT {β σ κ φπ : ℝ} (hS : σ + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ) = σ * β / (σ + κ * φπ) := by
  simp only [det2, AT, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), Exercise 7.1(d), p. 220 (**the Taylor principle**, restated from the Chapter 5
project): for `σ, κ > 0`, `0 < β < 1`, `φ_π ≥ 0`, both eigenvalues of `A_T` lie inside the unit
circle iff `φ_π > 1`. -/
theorem AT_schurStable_iff {β σ κ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) :
    SchurStable (tr2 (AT β σ κ φπ)) (det2 (AT β σ κ φπ)) ↔ 1 < φπ := by
  have hS : 0 < σ + κ * φπ := by positivity
  rw [tr2_AT hS.ne', det2_AT hS.ne']
  have hD0 : 0 < σ * β / (σ + κ * φπ) := by positivity
  have hD1 : σ * β / (σ + κ * φπ) < 1 := by
    rw [div_lt_one hS]; nlinarith
  have hT0 : 0 < (σ * (1 + β) + κ) / (σ + κ * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0]
  have key : (σ * (1 + β) + κ) / (σ + κ * φπ) < 1 + σ * β / (σ + κ * φπ)
      ↔ σ * (1 + β) + κ < σ + κ * φπ + σ * β := by
    rw [one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  rw [key]
  constructor
  · rintro ⟨-, h⟩
    nlinarith
  · intro h
    exact ⟨hD1, by nlinarith⟩

/-- Galí (2015), Exercise 7.1(d), p. 220: the rule
`i_t = rᵉ_t + π* + φ_π (π_t − π*)`. -/
def RuleD (πs φπ : ℝ) (re infl i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = re t + (fun _ => πs) + φπ • (infl t - fun _ => πs)

/-- Galí (2015), Exercise 7.1(d), p. 220 (**the system in deviations, exact**): with
`ψ = φ/(σ + φ)` (the output gap is `y − yᵉ = −ψ u`, `phi_u_eq_gap`), `κ = φλ_w` and the rule
`i_t = rᵉ_t + π* + φ_π (π_t − π*)`, the price-inflation equation and the DIS in `−ψ u` hold iff
the deviations `x̂_t = −ψ(u_t − u*)`, `π̂_t = π_t − π*` solve
`(x̂_t, π̂_t) = A_T(β, σ, κ/ψ, φ_π) E_t (x̂_{t+1}, π̂_{t+1})`. -/
theorem dev_iff_solves {β σ κ ϑ ψ φπ un : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hψ : 0 < ψ) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) {u infl i re : ℕ → Ω → ℝ}
    (hrule : RuleD (piStar β κ ϑ un) φπ re infl i) :
    (NKPCu 𝔼 β κ un u infl ∧ DIS 𝔼 σ (fun t => (-ψ) • u t) i infl re) ↔
      𝔼.Solves (AT β σ (κ / ψ) φπ) (wT σ (κ / ψ) φπ 0 0)
        (stack (fun t => (-ψ) • (u t - fun _ => uStar β κ ϑ un))
          (fun t => infl t - fun _ => piStar β κ ϑ un)) := by
  have hS : σ + κ / ψ * φπ ≠ 0 := by positivity
  set πs := piStar β κ ϑ un
  set us := uStar β κ ϑ un
  have hpn : πs = β * πs - κ * (us - un) := piStar_nkpc hϑ hβ1
  have hσ' : σ ≠ 0 := hσ.ne'
  have hψ' : ψ ≠ 0 := hψ.ne'
  have hinv : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ'
  have hdev : ∀ t, (fun t => φπ • (infl t - fun _ => πs)) t =
      (0 : ℕ → Ω → ℝ) t + (0 : ℝ) • (0 : ℕ → Ω → ℝ) t +
        φπ • (fun t => infl t - fun _ => πs) t := fun t => by simp
  rw [← rule_iff_solves 𝔼 hσ' hS hdev]
  have hEx : ∀ t ω, 𝔼.E t ((-ψ) • (u (t + 1) - fun _ => us)) ω =
      -ψ * 𝔼.E t (u (t + 1)) ω + ψ * us := fun t ω => by
    simp only [map_smul, map_sub, 𝔼.const, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hEp : ∀ t ω, 𝔼.E t (infl (t + 1) - fun _ => πs) ω = 𝔼.E t (infl (t + 1)) ω - πs :=
    fun t ω => by simp only [map_sub, 𝔼.const, Pi.sub_apply]
  have hEx' : ∀ t ω, 𝔼.E t ((-ψ) • u (t + 1)) ω = -ψ * 𝔼.E t (u (t + 1)) ω := fun t ω => by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨hn, hd⟩
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have p := congrFun (hn t) ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at p
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        hEp]
      field_simp
      linear_combination p - hpn
    · have e := congrFun (hd t) ω
      have r := congrFun (hrule t) ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hEx'] at e
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hEx, hEp]
      rw [r] at e
      linear_combination e
  · rintro ⟨hn, hd⟩
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have p := congrFun (hn t) ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        hEp] at p
      field_simp at p
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination p + hpn
    · have e := congrFun (hd t) ω
      have r := congrFun (hrule t) ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hEx, hEp] at e
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hEx']
      rw [r]
      linear_combination e

/-- Galí (2015), Exercise 7.1(d), p. 220 (**the rule implements the discretionary outcome
uniquely**): for `σ, κ, ϑ, ψ > 0`, `0 < β < 1` and `φ_π > 1`, bounded adapted `(u, π)` and a
nominal rate `i` satisfy the price-inflation equation, the DIS (gap `−ψ u`, efficient rate
`rᵉ`) and the rule `i_t = rᵉ_t + π* + φ_π(π_t − π*)` iff `u ≡ u*`, `π ≡ π*` (the discretionary
equilibrium of part (c)) and `i_t = rᵉ_t + π*`. -/
theorem rule_implements {β σ κ ϑ ψ φπ un : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hψ : 0 < ψ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 1 < φπ) {u infl i re : ℕ → Ω → ℝ}
    (hua : 𝔼.Adapted u) (hpa : 𝔼.Adapted infl) (hub : BoundedProc u)
    (hpb : BoundedProc infl) :
    (NKPCu 𝔼 β κ un u infl ∧ DIS 𝔼 σ (fun t => (-ψ) • u t) i infl re ∧
        RuleD (piStar β κ ϑ un) φπ re infl i) ↔
      (u = (fun _ _ => uStar β κ ϑ un) ∧ infl = (fun _ _ => piStar β κ ϑ un) ∧
        ∀ t, i t = re t + fun _ => piStar β κ ϑ un) := by
  set πs := piStar β κ ϑ un
  set us := uStar β κ ϑ un
  have hκψ : 0 < κ / ψ := div_pos hκ hψ
  have hz : 𝔼.Solves (AT β σ (κ / ψ) φπ) (wT σ (κ / ψ) φπ 0 0) (fun _ _ => 0) := by
    intro t j
    fin_cases j <;> simp [wT]
  have hza : 𝔼.AdaptedVec (fun _ _ => (0 : Ω → ℝ)) := fun t j => by
    simp
  have hzb : BoundedVec (fun (_ : ℕ) (_ : Fin 2) (_ : Ω) => (0 : ℝ)) :=
    ⟨0, fun _ _ _ => by simp⟩
  constructor
  · rintro ⟨hn, hd, hr⟩
    have hs := (dev_iff_solves 𝔼 hσ hκ hϑ hψ hβ1 (by linarith) hr).mp ⟨hn, hd⟩
    have hxa : 𝔼.Adapted (fun t => (-ψ) • (u t - fun _ => us)) := fun t => by
      rw [map_smul, map_sub, hua t, 𝔼.const]
    have hpa' : 𝔼.Adapted (fun t => infl t - fun _ => πs) := fun t => by
      rw [map_sub, hpa t, 𝔼.const]
    have hxb : BoundedProc (fun t => (-ψ) • (u t - fun _ => us)) := by
      obtain ⟨M, hM⟩ := hub
      refine ⟨|ψ| * (M + |us|), fun t ω => ?_⟩
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith [hM t ω]))
        (abs_nonneg _)
    have hpb' : BoundedProc (fun t => infl t - fun _ => πs) := by
      obtain ⟨M, hM⟩ := hpb
      exact ⟨M + |πs|, fun t ω => (abs_sub _ _).trans (by simp only; linarith [hM t ω])⟩
    have heq := 𝔼.system_unique ((AT_schurStable_iff hσ hκψ hβ0 hβ1 (by linarith)).mpr hφ)
      hs hz (adaptedVec_stack 𝔼 hxa hpa') hza (boundedVec_stack hxb hpb') hzb
    have h0 : ∀ t ω, -ψ * (u t ω - us) = 0 := fun t ω => by
      simpa [stack] using congrFun (congrFun (congrFun heq t) 0) ω
    have h1 : ∀ t ω, infl t ω - πs = 0 := fun t ω => by
      simpa [stack] using congrFun (congrFun (congrFun heq t) 1) ω
    have hu' : u = fun _ _ => us := by
      funext t ω
      have := h0 t ω
      have hψ0 : -ψ ≠ 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hψ0
      linarith
    have hp' : infl = fun _ _ => πs := by
      funext t ω
      linarith [h1 t ω]
    refine ⟨hu', hp', fun t => ?_⟩
    rw [hr t, hp']
    funext ω
    simp
  · rintro ⟨rfl, rfl, hi⟩
    have hr : RuleD πs φπ re (fun _ _ => πs) i := fun t => by
      rw [hi t]
      funext ω
      simp
    refine ⟨((discretionEq_iff 𝔼 hϑ).mp (discretion_const_isEq 𝔼 hϑ hβ1)).1, ?_, hr⟩
    intro t
    funext ω
    simp only [hi t, map_smul, 𝔼.const, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- Galí (2015), Exercise 7.1(d), p. 220 (**the Taylor principle is needed**): for
`0 ≤ φ_π ≤ 1` the rule `i_t = rᵉ_t + π* + φ_π(π_t − π*)` does not determine the equilibrium:
there are bounded adapted `(u, π)` and a rate `i` satisfying the price-inflation equation, the
DIS and the rule, other than the discretionary outcome. -/
theorem rule_indeterminate [Nonempty Ω] {β σ κ ϑ ψ φπ un : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hψ : 0 < ψ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφ0 : 0 ≤ φπ) (hφ1 : φπ ≤ 1)
    (re : ℕ → Ω → ℝ) :
    ∃ u infl i : ℕ → Ω → ℝ, NKPCu 𝔼 β κ un u infl ∧
      DIS 𝔼 σ (fun t => (-ψ) • u t) i infl re ∧ RuleD (piStar β κ ϑ un) φπ re infl i ∧
      𝔼.Adapted u ∧ 𝔼.Adapted infl ∧ BoundedProc u ∧ BoundedProc infl ∧
      (u ≠ (fun _ _ => uStar β κ ϑ un) ∨ infl ≠ (fun _ _ => piStar β κ ϑ un)) := by
  set πs := piStar β κ ϑ un
  set us := uStar β κ ϑ un
  have hκψ : 0 < κ / ψ := div_pos hκ hψ
  have hz : 𝔼.Solves (AT β σ (κ / ψ) φπ) (wT σ (κ / ψ) φπ 0 0) (fun _ _ => 0) := by
    intro t j
    fin_cases j <;> simp [wT]
  have hza : 𝔼.AdaptedVec (fun _ _ => (0 : Ω → ℝ)) := fun t j => by
    simp
  have hzb : BoundedVec (fun (_ : ℕ) (_ : Fin 2) (_ : Ω) => (0 : ℝ)) :=
    ⟨0, fun _ _ _ => by simp⟩
  have hns : ¬ SchurStable (tr2 (AT β σ (κ / ψ) φπ)) (det2 (AT β σ (κ / ψ) φπ)) := by
    rw [AT_schurStable_iff hσ hκψ hβ0 hβ1 hφ0]
    linarith
  obtain ⟨y, hy, hay, ⟨B, hB⟩, hne⟩ := 𝔼.system_not_unique hns hz hza hzb
  set u : ℕ → Ω → ℝ := fun t => (fun _ => us) - ψ⁻¹ • y t 0
  set infl : ℕ → Ω → ℝ := fun t => y t 1 + fun _ => πs
  set i : ℕ → Ω → ℝ := fun t => re t + (fun _ => πs) + φπ • (infl t - fun _ => πs)
  have hr : RuleD πs φπ re infl i := fun _ => rfl
  have hψ' : ψ ≠ 0 := hψ.ne'
  have hst : stack (fun t => (-ψ) • (u t - fun _ => us)) (fun t => infl t - fun _ => πs) = y := by
    funext t j
    fin_cases j
    · funext ω
      simp [stack, u, smul_smul, hψ']
    · funext ω
      simp [stack, infl]
  obtain ⟨hn, hd⟩ := (dev_iff_solves 𝔼 hσ hκ hϑ hψ hβ1 hφ0 hr).mpr (hst ▸ hy)
  refine ⟨u, infl, i, hn, hd, hr, fun t => ?_, fun t => ?_, ?_, ?_, ?_⟩
  · simp only [u, map_sub, map_smul, 𝔼.const, hay t 0]
  · simp only [infl, map_add, 𝔼.const, hay t 1]
  · refine ⟨|us| + |ψ⁻¹| * B, fun t ω => ?_⟩
    simp only [u, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    linarith [mul_le_mul_of_nonneg_left (hB t 0 ω) (abs_nonneg ψ⁻¹)]
  · refine ⟨B + |πs|, fun t ω => ?_⟩
    simp only [infl, Pi.add_apply]
    exact (abs_add_le _ _).trans (by linarith [hB t 1 ω])
  · by_contra hcon
    push Not at hcon
    apply hne
    rw [← hst, hcon.1, hcon.2]
    funext t j
    fin_cases j <;> funext ω <;> simp [stack]

/-! ### (e) Optimal policy under commitment

Exercise 7.1 has no exogenous shocks (`Y = N`, constant desired markups), so the commitment
problem is deterministic: choose `{π_t, u_t}` to minimise `∑ βᵗ (π_t² + ϑ u_t²)` subject to
`π_t = β π_{t+1} − κ (u_t − uⁿ)` for all `t ≥ 0`. The Lagrangian argument and the coefficient
`δ` are restated from the Chapter 5 project (with `x = −u` and a constant cost-push term
`κuⁿ`). -/

namespace Commit

/-- Galí (2015), Ch. 5, (14), p. 135 (restated): `γ ≡ ϑ / (ϑ(1 + β) + κ²)`. -/
noncomputable def gam (β κ ϑ : ℝ) : ℝ := ϑ / (ϑ * (1 + β) + κ ^ 2)

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `δ ≡ (1 − √(1 − 4βγ²)) / (2γβ)`. -/
noncomputable def del (β κ ϑ : ℝ) : ℝ :=
  (1 - √(1 - 4 * β * gam β κ ϑ ^ 2)) / (2 * gam β κ ϑ * β)

/-- Galí (2015), Ch. 5, (14), p. 135 (restated): `γ > 0`. -/
theorem gam_pos {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : 0 < gam β κ ϑ := by
  unfold gam; positivity

/-- Galí (2015), Ch. 5, (14), p. 135 (restated): `γ (ϑ(1 + β) + κ²) = ϑ`. -/
theorem gam_mul_denom {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    gam β κ ϑ * (ϑ * (1 + β) + κ ^ 2) = ϑ := by
  unfold gam
  have : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  field_simp

/-- Galí (2015), Ch. 5, (14), p. 135 (restated): `γ (1 + β) ≤ 1`. -/
theorem gam_mul_le {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : gam β κ ϑ * (1 + β) ≤ 1 := by
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  rw [gam, div_mul_eq_mul_div, div_le_one hD]
  nlinarith [sq_nonneg κ]

/-- Galí (2015), Ch. 5, (14)–(15) (restated): `γ (1 + β) < 1` iff `κ ≠ 0`. -/
theorem gam_mul_lt_iff {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    gam β κ ϑ * (1 + β) < 1 ↔ κ ≠ 0 := by
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  rw [gam, div_mul_eq_mul_div, div_lt_one hD]
  constructor
  · intro h hκ
    rw [hκ] at h
    linarith
  · intro hκ
    have := pow_pos (abs_pos.2 hκ) 2
    rw [sq_abs] at this
    linarith

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `4βγ² < 1`. -/
theorem four_beta_gam_sq_lt_one {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    4 * β * gam β κ ϑ ^ 2 < 1 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hle := gam_mul_le (κ := κ) hβ0 hϑ
  have h1 : (gam β κ ϑ * (1 + β)) ^ 2 ≤ 1 := by
    have : 0 ≤ gam β κ ϑ * (1 + β) := by positivity
    nlinarith
  have h2 : 0 < gam β κ ϑ ^ 2 * (1 - β) ^ 2 := by
    have : 0 < 1 - β := by linarith
    positivity
  nlinarith

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `√(1 − 4βγ²)² = 1 − 4βγ²`. -/
theorem sqrt_sq_eq {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    √(1 - 4 * β * gam β κ ϑ ^ 2) ^ 2 = 1 - 4 * β * gam β κ ϑ ^ 2 :=
  Real.sq_sqrt (by linarith [four_beta_gam_sq_lt_one (κ := κ) hβ0 hβ1 hϑ])

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `√(1 − 4βγ²) < 1`. -/
theorem sqrt_lt_one {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    √(1 - 4 * β * gam β κ ϑ ^ 2) < 1 := by
  rw [Real.sqrt_lt' one_pos]
  have := gam_pos (κ := κ) hβ0 hϑ
  have : 0 < 4 * β * gam β κ ϑ ^ 2 := by positivity
  linarith

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `δ · 2γβ = 1 − √(1 − 4βγ²)`. -/
theorem del_mul {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    del β κ ϑ * (2 * gam β κ ϑ * β) = 1 - √(1 - 4 * β * gam β κ ϑ ^ 2) := by
  have := gam_pos (κ := κ) hβ0 hϑ
  unfold del
  field_simp

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `δ > 0`. -/
theorem del_pos {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : 0 < del β κ ϑ := by
  have := gam_pos (κ := κ) hβ0 hϑ
  have := sqrt_lt_one (κ := κ) hβ0 hϑ
  unfold del
  apply div_pos <;> [linarith; positivity]

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `γβδ² − δ + γ = 0`. -/
theorem del_quad {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    gam β κ ϑ * β * del β κ ϑ ^ 2 - del β κ ϑ + gam β κ ϑ = 0 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hδ := del_mul (κ := κ) hβ0 hϑ
  have hs2 := sqrt_sq_eq (κ := κ) hβ0 hβ1 hϑ
  set g := gam β κ ϑ
  set s := √(1 - 4 * β * g ^ 2)
  set d := del β κ ϑ
  have h4 : (4 * g * β) * (g * β * d ^ 2 - d + g) = 0 := by
    linear_combination (2 * g * β * d + (1 - s) - 2) * hδ + hs2
  rcases mul_eq_zero.1 h4 with h | h
  · exfalso; have : 0 < 4 * g * β := by positivity
    linarith
  · exact h

/-- Galí (2015), Ch. 5, (15), p. 136 (restated): `δ < 1` iff `κ ≠ 0`. -/
theorem del_lt_one_iff {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    del β κ ϑ < 1 ↔ κ ≠ 0 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hle := gam_mul_le (κ := κ) hβ0 hϑ
  have hiff := gam_mul_lt_iff (κ := κ) hβ0 hϑ
  set g := gam β κ ϑ
  have h0 : 0 ≤ 1 - 2 * g * β := by nlinarith
  have hgb : 0 < g * β := by positivity
  rw [del, div_lt_one (by positivity), ← hiff]
  constructor
  · intro h
    have h1 : 1 - 2 * g * β < √(1 - 4 * β * g ^ 2) := by linarith
    have h2 := (Real.lt_sqrt h0).1 h1
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hgb.le (sub_nonneg.2 hc)]
  · intro h
    have h2 : (1 - 2 * g * β) ^ 2 < 1 - 4 * β * g ^ 2 := by nlinarith
    have := (Real.lt_sqrt h0).2 h2
    linarith

/-- Galí (2015), Ch. 5, p. 143 (restated): `κ²δ/ϑ = (1 − δ)(1 − βδ)`. -/
theorem kappa_sq_del {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    κ ^ 2 * del β κ ϑ / ϑ = (1 - del β κ ϑ) * (1 - β * del β κ ϑ) := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hq := del_quad (κ := κ) hβ0 hβ1 hϑ
  have hm := gam_mul_denom (κ := κ) hβ0 hϑ
  rw [div_eq_iff hϑ.ne']
  apply mul_left_cancel₀ hg.ne'
  linear_combination del β κ ϑ * hm - ϑ * hq

/-- Galí (2015), Ch. 5, p. 135 (restated): the lag operator with zero initial condition,
`(lag p)_0 = 0`, `(lag p)_{t+1} = p_t` (encodes `ξ_{−1} = 0`). -/
def lag (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => p t

/-- Galí (2015), Ch. 5, p. 135 (restated): `(lag p)_0 = 0`. -/
@[simp] theorem lag_zero (p : ℕ → ℝ) : lag p 0 = 0 := rfl

/-- Galí (2015), Ch. 5, p. 135 (restated): `(lag p)_{t+1} = p_t`. -/
@[simp] theorem lag_succ (p : ℕ → ℝ) (t : ℕ) : lag p (t + 1) = p t := rfl

/-- Galí (2015), Ch. 5, p. 135: the price-level gap `p̂_t = p_t − p_{−1} = ∑_{s ≤ t} π_s`. -/
def priceGap (infl : ℕ → ℝ) (t : ℕ) : ℝ := ∑ s ∈ Finset.range (t + 1), infl s

/-- Galí (2015), Ch. 5, p. 134 (restated; the Lagrangian argument, abstract form): if
`g_t = D_t + 2 (h_t − h_{t+1})` with `D_t ≥ 0`, `h_0 = 0` and `h_t → 0`, and `∑ g_t = G`, then
`∑ D_t = G`. -/
theorem hasSum_of_telescope {g D h : ℕ → ℝ} {G : ℝ} (hg : HasSum g G) (hD : ∀ t, 0 ≤ D t)
    (hgt : ∀ t, g t = D t + 2 * (h t - h (t + 1))) (h0 : h 0 = 0)
    (hh : Tendsto h atTop (𝓝 0)) : HasSum D G := by
  rw [hasSum_iff_tendsto_nat_of_nonneg hD]
  have hpart : (fun n => ∑ t ∈ Finset.range n, D t) =
      fun n => ∑ t ∈ Finset.range n, g t + 2 * h n := by
    funext n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hgt n]; ring
  rw [hpart]
  simpa using hg.tendsto_sum_nat.add (hh.const_mul 2)

/-- Galí (2015), Exercise 7.1(e), p. 220: the constraints `π_t = β π_{t+1} − κ (u_t − uⁿ)`,
`t ≥ 0` (perfect foresight; there are no shocks). -/
def Feasible (β κ un : ℝ) (infl u : ℕ → ℝ) : Prop :=
  ∀ t, infl t = β * infl (t + 1) - κ * (u t - un)

/-- Galí (2015), Exercise 7.1(b),(e), p. 220: the discounted period loss
`βᵗ (π_t² + ϑ u_t²)` (`ϑ = α_u`, correct discounting `βᵗ`). -/
def lossTerm (β ϑ : ℝ) (infl u : ℕ → ℝ) (t : ℕ) : ℝ := β ^ t * (infl t ^ 2 + ϑ * u t ^ 2)

/-- Galí (2015), Exercise 7.1(e), p. 220: the loss is finite. -/
def FiniteLoss (β ϑ : ℝ) (infl u : ℕ → ℝ) : Prop := Summable (lossTerm β ϑ infl u)

/-- Galí (2015), Exercise 7.1(e), p. 220: the loss `∑_{t ≥ 0} βᵗ (π_t² + ϑ u_t²)` (used on
finite-loss paths). -/
noncomputable def loss (β ϑ : ℝ) (infl u : ℕ → ℝ) : ℝ := ∑' t, lossTerm β ϑ infl u t

/-- Galí (2015), Exercise 7.1(e), p. 220: `(π, u)` solves the commitment problem: feasible,
finite loss, and loss no larger than that of any feasible finite-loss path. -/
def IsOptimal (β κ ϑ un : ℝ) (infl u : ℕ → ℝ) : Prop :=
  Feasible β κ un infl u ∧ FiniteLoss β ϑ infl u ∧
    ∀ π' u', Feasible β κ un π' u' → FiniteLoss β ϑ π' u' → loss β ϑ infl u ≤ loss β ϑ π' u'

/-- Galí (2015), Exercise 7.1(e), p. 220: the first-order conditions of the commitment
problem, `ϑ u_t = −κ ξ_t` and `π_t + ξ_t − ξ_{t−1} = 0`, `ξ_{−1} = 0`. -/
def FOC (κ ϑ : ℝ) (infl u ξ : ℕ → ℝ) : Prop :=
  ∀ t, ϑ * u t = -(κ * ξ t) ∧ infl t + ξ t - lag ξ t = 0

/-- Galí (2015), Exercise 7.1(e), p. 220 (**the targeting rule under commitment**): the
first-order conditions hold for some multipliers iff `u_t = (κ/ϑ) p̂_t` with
`p̂_t = ∑_{s ≤ t} π_s` (a rule in the price **level**, versus `u_t = (κ/ϑ) π_t` under
discretion). -/
theorem foc_iff_targeting {κ ϑ : ℝ} (hϑ : ϑ ≠ 0) (infl u : ℕ → ℝ) :
    (∃ ξ, FOC κ ϑ infl u ξ) ↔ ∀ t, u t = κ / ϑ * priceGap infl t := by
  constructor
  · rintro ⟨ξ, hξ⟩
    have hξp : ∀ t, ξ t = -priceGap infl t := by
      intro t
      induction t with
      | zero =>
        have := (hξ 0).2
        simp only [lag_zero] at this
        simp only [priceGap, zero_add, Finset.range_one, Finset.sum_singleton]
        linarith
      | succ t ih =>
        have := (hξ (t + 1)).2
        simp only [lag_succ] at this
        rw [priceGap, Finset.sum_range_succ, ← priceGap]
        linarith
    intro t
    have := (hξ t).1
    rw [hξp t] at this
    field_simp
    linarith
  · intro h
    refine ⟨fun t => -priceGap infl t, fun t => ⟨?_, ?_⟩⟩
    · rw [h t]; field_simp
    · cases t with
      | zero => simp [priceGap]
      | succ t =>
        simp only [lag_succ, priceGap, Finset.sum_range_succ _ (t + 1)]
        ring

/-- Galí (2015), Exercise 7.1(e), p. 220 (restated from Chapter 5; transversality): on a
finite-loss path `βᵗ π_t² → 0` and `βᵗ u_t² → 0`. -/
theorem tendsto_disc_sq {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hϑ : 0 < ϑ) {infl u : ℕ → ℝ}
    (hl : FiniteLoss β ϑ infl u) :
    Tendsto (fun t => β ^ t * infl t ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun t => β ^ t * u t ^ 2) atTop (𝓝 0) := by
  have hL := hl.tendsto_atTop_zero
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL
      (fun t => by positivity) (fun t => ?_)
    have : 0 ≤ β ^ t * (ϑ * u t ^ 2) := by positivity
    simp only [lossTerm]
    nlinarith
  · have hL' := hL.div_const ϑ
    rw [zero_div] at hL'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL'
      (fun t => by positivity) (fun t => ?_)
    have : 0 ≤ β ^ t * infl t ^ 2 := by positivity
    simp only [lossTerm]
    rw [le_div_iff₀ hϑ]
    nlinarith

/-- **Galí (2015), Exercise 7.1(e), p. 220 (sufficiency of the first-order conditions,
Lagrangian identity; adapted from the Chapter 5 project)**: if a feasible finite-loss path
`(π*, u*)` satisfies the first-order conditions with multipliers `ξ` (`ξ_{−1} = 0`), then for
every feasible finite-loss path `(π, u)`,
`L(π, u) − L(π*, u*) = ∑ βᵗ ((π_t − π*_t)² + ϑ (u_t − u*_t)²)`. -/
theorem loss_sub_hasSum {β κ ϑ un : ℝ} (hβ0 : 0 ≤ β) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {infl u πs us ξ : ℕ → ℝ} (hf : Feasible β κ un infl u) (hl : FiniteLoss β ϑ infl u)
    (hfs : Feasible β κ un πs us) (hls : FiniteLoss β ϑ πs us) (hξ : FOC κ ϑ πs us ξ) :
    HasSum (fun t => β ^ t * ((infl t - πs t) ^ 2 + ϑ * (u t - us t) ^ 2))
      (loss β ϑ infl u - loss β ϑ πs us) := by
  have hξx : ∀ t, ξ t = -(ϑ / κ) * us t := fun t => by
    field_simp; linarith [(hξ t).1]
  obtain ⟨hπ0, -⟩ := tendsto_disc_sq hβ0 hϑ hl
  obtain ⟨hπs0, hxs0⟩ := tendsto_disc_sq hβ0 hϑ hls
  have hξ0 : Tendsto (fun t => β ^ t * ξ t ^ 2) atTop (𝓝 0) := by
    have : (fun t => β ^ t * ξ t ^ 2) = fun t => (ϑ / κ) ^ 2 * (β ^ t * us t ^ 2) := by
      funext t; rw [hξx t]; ring
    rw [this]
    simpa using hxs0.const_mul ((ϑ / κ) ^ 2)
  have hlag0 : Tendsto (fun t => β ^ t * lag ξ t ^ 2) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have : (fun t => β ^ (t + 1) * lag ξ (t + 1) ^ 2) = fun t => β * (β ^ t * ξ t ^ 2) := by
      funext t; rw [lag_succ, pow_succ]; ring
    rw [this]
    simpa using hξ0.const_mul β
  have hd0 : Tendsto (fun t => β ^ t * (infl t - πs t) ^ 2) atTop (𝓝 0) := by
    have hup := (hπ0.const_mul 2).add (hπs0.const_mul 2)
    rw [mul_zero, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun t => by positivity) (fun t => ?_)
    have hb : 0 ≤ β ^ t := pow_nonneg hβ0 t
    have : (infl t - πs t) ^ 2 ≤ 2 * infl t ^ 2 + 2 * πs t ^ 2 := by
      nlinarith [sq_nonneg (infl t + πs t)]
    have := mul_le_mul_of_nonneg_left this hb
    simp only
    nlinarith
  refine hasSum_of_telescope (hl.hasSum.sub hls.hasSum)
    (fun t => by positivity) (h := fun t => β ^ t * lag ξ t * (infl t - πs t))
    (fun t => ?_) (by simp) ?_
  · have n1 := hf t
    have n2 := hfs t
    have f1 := (hξ t).1
    have f2 := (hξ t).2
    simp only [lossTerm, lag_succ]
    linear_combination β ^ t * (2 * (infl t - πs t) * f2 + 2 * (u t - us t) * f1 -
      2 * ξ t * (n1 - n2))
  · have hup := hlag0.add hd0
    rw [add_zero] at hup
    refine squeeze_zero_norm (fun t => ?_) hup
    have hb : 0 ≤ β ^ t := pow_nonneg hβ0 t
    have hab : |lag ξ t * (infl t - πs t)| ≤ lag ξ t ^ 2 + (infl t - πs t) ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (lag ξ t + (infl t - πs t)),
        sq_nonneg (lag ξ t - (infl t - πs t))]
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg hb]
    nlinarith [mul_le_mul_of_nonneg_left hab hb]

/-- **Galí (2015), Exercise 7.1(e), p. 220 (optimality)**: a feasible finite-loss path satisfying
the first-order conditions is optimal. -/
theorem isOptimal_of_foc {β κ ϑ un : ℝ} (hβ0 : 0 ≤ β) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {πs us ξ : ℕ → ℝ} (hfs : Feasible β κ un πs us) (hls : FiniteLoss β ϑ πs us)
    (hξ : FOC κ ϑ πs us ξ) : IsOptimal β κ ϑ un πs us :=
  ⟨hfs, hls, fun _ _ hf hl => sub_nonneg.1
    ((loss_sub_hasSum hβ0 hϑ hκ hf hl hfs hls hξ).nonneg (fun t => by positivity))⟩

/-- **Galí (2015), Exercise 7.1(e), p. 220 (uniqueness)**: a feasible finite-loss path with the
same loss as a path satisfying the first-order conditions coincides with it. -/
theorem eq_of_loss_eq {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {infl u πs us ξ : ℕ → ℝ} (hf : Feasible β κ un infl u) (hl : FiniteLoss β ϑ infl u)
    (hfs : Feasible β κ un πs us) (hls : FiniteLoss β ϑ πs us) (hξ : FOC κ ϑ πs us ξ)
    (heq : loss β ϑ infl u = loss β ϑ πs us) : infl = πs ∧ u = us := by
  have hs := loss_sub_hasSum hβ0.le hϑ hκ hf hl hfs hls hξ
  rw [heq, sub_self] at hs
  have hz := (hasSum_zero_iff_of_nonneg (fun t => by positivity)).1 hs
  have ht : ∀ t, (infl t - πs t) ^ 2 + ϑ * (u t - us t) ^ 2 = 0 := fun t => by
    have := congrFun hz t
    simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
      false_or] at this
    exact this
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · have h1 := ht t
    have : (infl t - πs t) ^ 2 = 0 := by
      nlinarith [sq_nonneg (infl t - πs t), sq_nonneg (u t - us t)]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · have h1 := ht t
    have h2 : ϑ * (u t - us t) ^ 2 = 0 := by
      nlinarith [sq_nonneg (infl t - πs t), sq_nonneg (u t - us t)]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hϑ.ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      linarith

/-- Galí (2015), Exercise 7.1(e), p. 220 (restated from Chapter 5): a bounded path has finite
loss. -/
theorem finiteLoss_of_bounded {β ϑ A B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ)
    {infl u : ℕ → ℝ} (hπ : ∀ t, |infl t| ≤ A) (hu : ∀ t, |u t| ≤ B) :
    FiniteLoss β ϑ infl u := by
  refine Summable.of_nonneg_of_le (fun t => by unfold lossTerm; positivity) (fun t => ?_)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (A ^ 2 + ϑ * B ^ 2))
  have h1 : infl t ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hπ t) 2
  have h2 : u t ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hu t) 2
  unfold lossTerm
  exact mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left h2 hϑ])
    (pow_nonneg hβ0 t)

/-- Galí (2015), Exercise 7.1(e), p. 220: the long-run price-level gap under commitment,
`p̄ = ϑuⁿ/κ`. -/
noncomputable def pbar (κ ϑ un : ℝ) : ℝ := ϑ * un / κ

/-- Galí (2015), Exercise 7.1(e), p. 220 (**commitment inflation**):
`π_t = p̄ (1 − δ) δᵗ`. -/
noncomputable def commInfl (β κ ϑ un : ℝ) (t : ℕ) : ℝ :=
  pbar κ ϑ un * (1 - del β κ ϑ) * del β κ ϑ ^ t

/-- Galí (2015), Exercise 7.1(e), p. 220 (**commitment unemployment**):
`u_t = uⁿ (1 − δ^{t+1})`. -/
noncomputable def commU (β κ ϑ un : ℝ) (t : ℕ) : ℝ := un * (1 - del β κ ϑ ^ (t + 1))

/-- Galí (2015), Exercise 7.1(e), p. 220: under commitment the price-level gap is
`p̂_t = p̄ (1 − δ^{t+1})`, and `u_t = (κ/ϑ) p̂_t`. -/
theorem priceGap_commInfl {β κ ϑ un : ℝ} (hκ : κ ≠ 0) (hϑ : 0 < ϑ) (t : ℕ) :
    priceGap (commInfl β κ ϑ un) t = pbar κ ϑ un * (1 - del β κ ϑ ^ (t + 1)) ∧
      commU β κ ϑ un t = κ / ϑ * priceGap (commInfl β κ ϑ un) t := by
  have hg : priceGap (commInfl β κ ϑ un) t = pbar κ ϑ un * (1 - del β κ ϑ ^ (t + 1)) := by
    induction t with
    | zero => simp [priceGap, commInfl]
    | succ t ih =>
      rw [priceGap, Finset.sum_range_succ, ← priceGap, ih, commInfl]
      ring
  refine ⟨hg, ?_⟩
  rw [hg, commU, pbar]
  field_simp

/-- Galí (2015), Exercise 7.1(e), p. 220: the commitment path is feasible. -/
theorem comm_feasible {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ) :
    Feasible β κ un (commInfl β κ ϑ un) (commU β κ ϑ un) := by
  intro t
  have hk := kappa_sq_del (κ := κ) hβ0 hβ1 hϑ
  set d := del β κ ϑ
  have hk' : κ ^ 2 * d = ϑ * ((1 - d) * (1 - β * d)) := by
    rw [div_eq_iff hϑ.ne'] at hk
    linarith
  simp only [commInfl, commU, pbar, pow_succ]
  field_simp
  linear_combination (-(un * d ^ t)) * hk'

/-- Galí (2015), Exercise 7.1(e), p. 220: the commitment path satisfies the first-order
conditions with `ξ_t = −p̂_t = −p̄(1 − δ^{t+1})`. -/
theorem comm_foc {β κ ϑ un : ℝ} (hκ : κ ≠ 0) (hϑ : 0 < ϑ) :
    FOC κ ϑ (commInfl β κ ϑ un) (commU β κ ϑ un)
      (fun t => -(pbar κ ϑ un * (1 - del β κ ϑ ^ (t + 1)))) := by
  intro t
  refine ⟨?_, ?_⟩
  · simp only [commU, pbar]
    field_simp
  · cases t with
    | zero => simp [commInfl]
    | succ t =>
      simp only [lag_succ, commInfl]
      ring

/-- Galí (2015), Exercise 7.1(e), p. 220: `δ ∈ (0, 1)` for `κ ≠ 0`. -/
theorem del_mem {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ) :
    0 < del β κ ϑ ∧ del β κ ϑ < 1 :=
  ⟨del_pos hβ0 hϑ, (del_lt_one_iff hβ0 hβ1 hϑ).2 hκ⟩

/-- Galí (2015), Exercise 7.1(e), p. 220: the commitment path has finite loss. -/
theorem comm_finiteLoss {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hϑ : 0 < ϑ) : FiniteLoss β ϑ (commInfl β κ ϑ un) (commU β κ ϑ un) := by
  obtain ⟨hd0, hd1⟩ := del_mem hβ0 hβ1 hκ hϑ
  refine finiteLoss_of_bounded hβ0.le hβ1 hϑ.le (A := |pbar κ ϑ un|) (B := |un|)
    (fun t => ?_) (fun t => ?_)
  · have h1 : |(1 - del β κ ϑ) * del β κ ϑ ^ t| ≤ 1 := by
      rw [abs_mul, abs_of_pos (by linarith), abs_of_pos (pow_pos hd0 t)]
      have : del β κ ϑ ^ t ≤ 1 := pow_le_one₀ hd0.le hd1.le
      nlinarith [pow_pos hd0 t]
    simp only [commInfl, mul_assoc]
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) h1
  · have h1 : |1 - del β κ ϑ ^ (t + 1)| ≤ 1 := by
      have h2 : 0 < del β κ ϑ ^ (t + 1) := pow_pos hd0 _
      have h3 : del β κ ϑ ^ (t + 1) ≤ 1 := pow_le_one₀ hd0.le hd1.le
      rw [abs_le]
      constructor <;> linarith
    simp only [commU]
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) h1

/-- **Galí (2015), Exercise 7.1(e), p. 220 (THE OPTIMAL POLICY UNDER COMMITMENT)**: for
`κ ≠ 0`, `ϑ > 0`, `0 < β < 1`, the path `π_t = p̄(1 − δ)δᵗ`, `u_t = uⁿ(1 − δ^{t+1})` is optimal,
and it is the **only** optimal path. -/
theorem isOptimal_iff {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    (infl u : ℕ → ℝ) :
    IsOptimal β κ ϑ un infl u ↔ infl = commInfl β κ ϑ un ∧ u = commU β κ ϑ un := by
  have hc : IsOptimal β κ ϑ un (commInfl β κ ϑ un) (commU β κ ϑ un) :=
    isOptimal_of_foc hβ0.le hϑ hκ (comm_feasible hβ0 hβ1 hκ hϑ) (comm_finiteLoss hβ0 hβ1 hκ hϑ)
      (comm_foc hκ hϑ)
  constructor
  · rintro ⟨hf, hl, hmin⟩
    have h1 := hmin _ _ hc.1 hc.2.1
    have h2 := hc.2.2 _ _ hf hl
    exact eq_of_loss_eq hβ0 hϑ hκ hf hl hc.1 hc.2.1 (comm_foc hκ hϑ) (le_antisymm h1 h2)
  · rintro ⟨rfl, rfl⟩
    exact hc

/-- **Galí (2015), Exercise 7.1(e), p. 220 (first-order conditions necessary and
sufficient)**: a feasible finite-loss path is optimal iff it satisfies the targeting rule
`u_t = (κ/ϑ) p̂_t`. -/
theorem isOptimal_iff_targeting {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hϑ : 0 < ϑ) {infl u : ℕ → ℝ} (hf : Feasible β κ un infl u) (hl : FiniteLoss β ϑ infl u) :
    IsOptimal β κ ϑ un infl u ↔ ∀ t, u t = κ / ϑ * priceGap infl t := by
  rw [← foc_iff_targeting hϑ.ne']
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ := (isOptimal_iff hβ0 hβ1 hκ hϑ infl u).1 h
    exact ⟨_, comm_foc hκ hϑ⟩
  · rintro ⟨ξ, hξ⟩
    exact isOptimal_of_foc hβ0.le hϑ hκ hf hl hξ

/-- Galí (2015), Exercise 7.1(e), p. 220 (**no long-run inflation bias under commitment**):
`π_t → 0` and `u_t → uⁿ`. -/
theorem commitment_tendsto {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hϑ : 0 < ϑ) :
    Tendsto (commInfl β κ ϑ un) atTop (𝓝 0) ∧ Tendsto (commU β κ ϑ un) atTop (𝓝 un) := by
  obtain ⟨hd0, hd1⟩ := del_mem hβ0 hβ1 hκ hϑ
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hd0.le hd1
  constructor
  · have h := hp.const_mul (pbar κ ϑ un * (1 - del β κ ϑ))
    rw [mul_zero] at h
    exact h
  · have hp1 : Tendsto (fun t : ℕ => del β κ ϑ ^ (t + 1)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).2 hp
    have h := (hp1.const_sub 1).const_mul un
    rw [sub_zero, mul_one] at h
    exact h

/-- Galí (2015), Exercise 7.1(e), p. 220: with `uⁿ > 0`, `κ, ϑ > 0`, commitment inflation is
positive and strictly decreasing, and commitment unemployment rises strictly towards `uⁿ`. -/
theorem commitment_monotone {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hun : 0 < un) :
    (∀ t, 0 < commInfl β κ ϑ un t) ∧ StrictAnti (commInfl β κ ϑ un) ∧
      StrictMono (commU β κ ϑ un) ∧ ∀ t, commU β κ ϑ un t < un := by
  obtain ⟨hd0, hd1⟩ := del_mem hβ0 hβ1 hκ.ne' hϑ
  have hp : 0 < pbar κ ϑ un := by unfold pbar; positivity
  have hc : 0 < pbar κ ϑ un * (1 - del β κ ϑ) := mul_pos hp (by linarith)
  refine ⟨fun t => by unfold commInfl; positivity, ?_, ?_, fun t => ?_⟩
  · refine strictAnti_nat_of_succ_lt fun t => ?_
    simp only [commInfl, pow_succ]
    have := pow_pos hd0 t
    nlinarith [mul_pos hc this]
  · refine strictMono_nat_of_lt_succ fun t => ?_
    simp only [commU, pow_succ]
    have := pow_pos hd0 t
    nlinarith [mul_pos (mul_pos this hd0) hun]
  · simp only [commU]
    have := pow_pos hd0 (t + 1)
    nlinarith

/-- Galí (2015), Exercise 7.1(e), p. 220 (**commitment inflation is below discretionary
inflation at every date**): for `κ, ϑ > 0`, `0 < β < 1`, `uⁿ > 0`, `π^c_t < π*` for all `t`. -/
theorem commInfl_lt_piStar {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hun : 0 < un) (t : ℕ) : commInfl β κ ϑ un t < piStar β κ ϑ un := by
  obtain ⟨hd0, hd1⟩ := del_mem hβ0 hβ1 hκ.ne' hϑ
  have hk := kappa_sq_del (κ := κ) hβ0 hβ1 hϑ
  set d := del β κ ϑ
  have hk' : κ ^ 2 * d = ϑ * ((1 - d) * (1 - β * d)) := by
    rw [div_eq_iff hϑ.ne'] at hk
    linarith
  have hD := den_pos (κ := κ) hϑ hβ1
  have h0 : commInfl β κ ϑ un t ≤ commInfl β κ ϑ un 0 := by
    have := (commitment_monotone hβ0 hβ1 hκ hϑ hun).2.1.antitone (Nat.zero_le t)
    exact this
  refine h0.trans_lt ?_
  simp only [commInfl, pbar, pow_zero, mul_one, piStar]
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ hκ hD]
  -- `d((1 − d)(κ² + ϑ(1 − β)) − κ²) = −ϑβd(1 − d)²`, using `κ²d = ϑ(1 − d)(1 − βd)`
  have key : d * ((1 - d) * (κ ^ 2 + ϑ * (1 - β)) - κ ^ 2) = -(ϑ * β * d * (1 - d) ^ 2) := by
    linear_combination (-d) * hk'
  have hneg : (1 - d) * (κ ^ 2 + ϑ * (1 - β)) - κ ^ 2 < 0 := by
    have hr : 0 < ϑ * β * d * (1 - d) ^ 2 := by
      have : 0 < 1 - d := by linarith
      positivity
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hd0.le hc]
  have hpos : 0 < ϑ * un * κ := by positivity
  nlinarith [mul_lt_mul_of_pos_left hneg hpos]

/-- Galí (2015), Exercise 7.1(c),(e), p. 220: the discretionary path `(π*, u*)` is feasible in
the commitment problem and has finite loss. -/
theorem disc_feasible {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    Feasible β κ un (fun _ => piStar β κ ϑ un) (fun _ => uStar β κ ϑ un) ∧
      FiniteLoss β ϑ (fun _ => piStar β κ ϑ un) (fun _ => uStar β κ ϑ un) :=
  ⟨fun _ => piStar_nkpc hϑ hβ1,
    finiteLoss_of_bounded hβ0.le hβ1 hϑ.le (fun _ => le_rfl) (fun _ => le_rfl)⟩

/-- **Galí (2015), Exercise 7.1(e), p. 220 (commitment versus discretion)**: for `κ, ϑ > 0`,
`0 < β < 1`, `uⁿ > 0`, the commitment path has strictly lower loss than the discretionary path;
commitment inflation is below `π*` at every date and converges to `0` (no long-run bias), while
under discretion `π_t = π* > 0` forever and `u_t = u* < uⁿ` forever (unemployment is held
permanently below its natural rate at the cost of permanently positive inflation). -/
theorem commitment_beats_discretion {β κ ϑ un : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hun : 0 < un) :
    loss β ϑ (commInfl β κ ϑ un) (commU β κ ϑ un) <
        loss β ϑ (fun _ => piStar β κ ϑ un) (fun _ => uStar β κ ϑ un) ∧
      (∀ t, commInfl β κ ϑ un t < piStar β κ ϑ un) ∧
      Tendsto (commInfl β κ ϑ un) atTop (𝓝 0) ∧ 0 < piStar β κ ϑ un ∧
      Tendsto (commU β κ ϑ un) atTop (𝓝 un) ∧ uStar β κ ϑ un < un := by
  have hc := (isOptimal_iff (un := un) hβ0 hβ1 hκ.ne' hϑ _ _).2 ⟨rfl, rfl⟩
  obtain ⟨hdf, hdl⟩ := disc_feasible (κ := κ) (un := un) hβ0 hβ1 hϑ
  have hle := hc.2.2 _ _ hdf hdl
  refine ⟨lt_of_le_of_ne hle fun heq => ?_, commInfl_lt_piStar hβ0 hβ1 hκ hϑ hun,
    (commitment_tendsto hβ0 hβ1 hκ.ne' hϑ).1, inflationBias_pos hκ hϑ hβ1 hun,
    (commitment_tendsto hβ0 hβ1 hκ.ne' hϑ).2, (uStar_lt_un hκ.ne' hϑ hβ1 hun).2⟩
  obtain ⟨h1, -⟩ := eq_of_loss_eq hβ0 hϑ hκ.ne' hdf hdl hc.1 hc.2.1 (comm_foc hκ.ne' hϑ)
    heq.symm
  have := commInfl_lt_piStar hβ0 hβ1 hκ hϑ hun 0
  rw [← h1] at this
  exact lt_irrefl _ this

end Commit

end Gali.Unemployment.Ex7_1
