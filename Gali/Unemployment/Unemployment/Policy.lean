/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Unemployment.Expectations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Monetary policy design and unemployment fluctuations

Galí (2015), Section 7.3, pp. 208–216.

## Main results

* **Calibration, p. 209**: `markup_eq_exp` (`M_w = exp(φ uⁿ)` from (10)),
  `epsW_markup_iff` (`ε_w/(ε_w − 1) = M ⇔ ε_w = M/(M − 1)`), `exp_quarter_bounds`,
  `calibration_epsW` (`ε_w ∈ (4.5, 4.55)`), `calibration_markup` (net markup `∈ (0.28, 0.29)`),
  `calibration_book_epsW` (the printed `ε_w = 4.5` is a rounding: survey error 6).
* **Labour-force wealth effect, (17) and Fig. 7.2**: the participation equation (6) solved for `l`
  (`laborForce`), its exact derivative `hasDerivAt_laborForce` (`∂l/∂c = −σ/φ < 0` given the real
  wage), `laborForce_strictAnti`; the nonlinear marginal participant (5)
  (`marginalParticipant_eq5`, `log_marginalParticipant`, `hasDerivAt_log_marginalParticipant`).
* **fn. 12** (`θ_w → 0` kills unemployment fluctuations): `abs_unemp_le` (pathwise bound
  `|û_t| ≤ (1 + β) B/(λ_w φ)` from (14)), `tendsto_lamWOf_atTop` (`λ_w → ∞` as `θ_w → 0⁺`),
  `unemployment_vanishes` (uniformly along uniformly bounded `π^w` paths),
  `unemployment_volatility_vanishes` (conditional second moments), the counterexample
  `unemployment_need_not_vanish` (the uniform bound cannot be dropped), and the flexible-wage limit
  model `flexible_wages_no_unemployment_gap`.
* **Optimal policy, (18)–(21)**: the Chapter 6 deterministic commitment theory is restated
  (`Det.isOptimal_of_foc`, `Det.isOptimal_iff_foc`, `Det.demand_zero_optimal`, ...); fn. 8
  `fn8_wage_pc`; `feasible7_iff` (constraints (13)–(16) ⇔ Chapter 6 constraints + (16) for `û`);
  `isOptimal7_iff` (the Chapter 7 problem is the Chapter 6 problem); `foc7_iff_ch6` (the printed
  (18)–(21) ARE the Chapter 6 conditions (30)–(33): survey error 1, "chapter 3" on p. 212);
  `isOptimal7_iff_eq`, `existsUnique_optimal7`, `isOptimal7_iff_foc` (the optimum is the Chapter 6
  optimum with `û = (ω̃ − (σ + φ/(1 − α)) ỹ)/φ`).
* **p. 213, technology under `σ = 1`**: `psiYA_sigma_one`, `psiWA_sigma_one`,
  `participation_consistent` ((6) holds for `l = n + u`), `efficient_technology_sigma_one`
  (`y = a`, `n = l = û = 0`, real wage `= a`), `efficient_employment_zero_iff` (`n = 0` at the
  efficient allocation iff `σ = 1`).
* **p. 214, demand shocks**: `demand_shock_optimal_iff`, `demand_shock_labour_market` (all
  labour-market variables fully insulated).
* **(22)**: `rule22_level_iff_gap`, `rule22_book_intercept`, `rule22_level_not_steady`,
  `rule22_gap_steady`, `rule22_deviation` (the level/gap intercept imprecision, survey error 5).

Table 7.1 and Figures 7.2–7.6 are numerical simulations and are not formalised.
-/

namespace Gali.Unemployment.Policy

open Filter Topology

/-! ### Coefficients and lags -/

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (18), (20), (28), pp. 172, 179: the coefficients of the optimal-policy problem:
the discount factor, the slopes `κ_p, κ_w, λ_p, λ_w` of the price and wage Phillips curves, and the
loss weights `a_y, a_p, a_w` on `ỹ², (π^p)², (π^w)²` (in the book `a_y = σ + (φ + α)/(1 − α)`,
`a_p = ε_p/λ_p`, `a_w = ε_w(1 − α)/λ_w`, see `bookCoef`). -/
structure Coef where
  /-- The discount factor `β`. -/
  β : ℝ
  /-- The output-gap slope `κ_p` of the price Phillips curve (18). -/
  kapP : ℝ
  /-- The output-gap slope `κ_w` of the wage Phillips curve (20). -/
  kapW : ℝ
  /-- The real-wage-gap slope `λ_p` of (18). -/
  lamP : ℝ
  /-- The real-wage-gap slope `λ_w` of (20). -/
  lamW : ℝ
  /-- The loss weight on `ỹ²`. -/
  ay : ℝ
  /-- The loss weight on `(π^p)²`. -/
  ap : ℝ
  /-- The loss weight on `(π^w)²`. -/
  aw : ℝ

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (18), (20), (28), pp. 172, 179: the book's coefficients, with
`κ_p = αλ_p/(1 − α)`, `κ_w = λ_w(σ + φ/(1 − α))`, `a_y = σ + (φ + α)/(1 − α)`, `a_p = ε_p/λ_p`,
`a_w = ε_w(1 − α)/λ_w`. -/
noncomputable def bookCoef (β σ φ α εp εw lamP lamW : ℝ) : Coef where
  β := β
  kapP := α * lamP / (1 - α)
  kapW := lamW * (σ + φ / (1 - α))
  lamP := lamP
  lamW := lamW
  ay := σ + (φ + α) / (1 - α)
  ap := εp / lamP
  aw := εw * (1 - α) / lamW

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (21), p. 172: the lag `x_{t−1}` of a sequence with initial value `x_{−1} = x0`
(used for `ω̃_{t−1}` with `ω̃_{−1}` given, and for the multipliers with `ζ_{−1} = 0`). -/
def prev {α : Type*} (x0 : α) (x : ℕ → α) : ℕ → α
  | 0 => x0
  | t + 1 => x t

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181: `x_{−1} = x0`. -/
@[simp] theorem prev_zero {α : Type*} (x0 : α) (x : ℕ → α) : prev x0 x 0 = x0 := rfl

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181: the lag at date `t + 1` is the date-`t` value. -/
@[simp] theorem prev_succ {α : Type*} (x0 : α) (x : ℕ → α) (t : ℕ) : prev x0 x (t + 1) = x t :=
  rfl

/-! ### The Lagrangian identity -/

/-- Restated from the Chapter 6 project.
**Galí (2015), ch. 6, (30)–(33), p. 181 (the Lagrangian identity, one period)**:
if `(ỹ*, π^p*, π^w*,
ω̃*)` satisfies the constraints (18), (20), (21) and the first-order conditions (30)–(33) with
multipliers `ζ₁, ζ₂, ζ₃`, and `(ỹ, π^p, π^w, ω̃)` satisfies the same constraints, then the excess
period loss is the quadratic form in the deviations plus a telescoping term. Here `Ep` stands for
(the conditional expectation of) next period's price inflation, etc. -/
theorem lagrangian_alg (c : Coef) {y p q w wl ys ps qs ws wsl Ep Eq Eps Eqs dn z1 z1l z2 z2l z3
    Ez3 : ℝ}
    (c1 : p = c.β * Ep + c.kapP * y + c.lamP * w) (c2 : q = c.β * Eq + c.kapW * y - c.lamW * w)
    (c3 : w = wl + q - p - dn) (c1s : ps = c.β * Eps + c.kapP * ys + c.lamP * ws)
    (c2s : qs = c.β * Eqs + c.kapW * ys - c.lamW * ws) (c3s : ws = wsl + qs - ps - dn)
    (f1 : c.ay * ys + c.kapP * z1 + c.kapW * z2 = 0) (f2 : c.ap * ps - (z1 - z1l) + z3 = 0)
    (f3 : c.aw * qs - (z2 - z2l) - z3 = 0)
    (f4 : c.lamP * z1 - c.lamW * z2 + z3 - c.β * Ez3 = 0) :
    (c.ay * y ^ 2 + c.ap * p ^ 2 + c.aw * q ^ 2) / 2 -
        (c.ay * ys ^ 2 + c.ap * ps ^ 2 + c.aw * qs ^ 2) / 2 =
      (c.ay * (y - ys) ^ 2 + c.ap * (p - ps) ^ 2 + c.aw * (q - qs) ^ 2) / 2 +
        c.β * (z1 * (Ep - Eps) + z2 * (Eq - Eqs) + (w - ws) * Ez3) -
          (z1l * (p - ps) + z2l * (q - qs) + (wl - wsl) * z3) := by
  linear_combination (y - ys) * f1 + (p - ps) * f2 + (q - qs) * f3 + z1 * (c1 - c1s) +
    z2 * (c2 - c2s) - z3 * (c3 - c3s) + (w - ws) * f4

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181 (the Lagrangian argument, abstract form): if `g_t = D_t + (h_{t+1} − h_t)`
with `D_t ≥ 0`, `h_0 = 0` (`ζ_{1,−1} = ζ_{2,−1} = 0`, common `ω̃_{−1}`) and `h_t → 0`
(transversality), and `∑ g_t = G`, then `∑ D_t = G`. -/
theorem hasSum_of_telescope {g D h : ℕ → ℝ} {G : ℝ} (hg : HasSum g G) (hD : ∀ t, 0 ≤ D t)
    (hgt : ∀ t, g t = D t + (h (t + 1) - h t)) (h0 : h 0 = 0)
    (hh : Tendsto h atTop (𝓝 0)) : HasSum D G := by
  rw [hasSum_iff_tendsto_nat_of_nonneg hD]
  have hpart : (fun n => ∑ t ∈ Finset.range n, D t) =
      fun n => ∑ t ∈ Finset.range n, g t - h n := by
    funext n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hgt n]; ring
  rw [hpart]
  simpa using hg.tendsto_sum_nat.sub hh

/-! ### Weighted square summability -/

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181 (transversality): if `∑ βᵗ x_t²` converges, `0 ≤ β < 1`, then
`βᵗ |x_t| → 0`. -/
theorem tendsto_disc_abs {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ}
    (hs : Summable (fun t => β ^ t * x t ^ 2)) :
    Tendsto (fun t => β ^ t * |x t|) atTop (𝓝 0) := by
  have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1
  have h2 := hs.tendsto_atTop_zero
  have hup := (h1.add h2).div_const 2
  rw [add_zero, zero_div] at hup
  refine squeeze_zero (fun t => by positivity) (fun t => ?_) hup
  have hb : 0 ≤ β ^ t := pow_nonneg hβ0 t
  have hx : |x t| ≤ (1 + x t ^ 2) / 2 := by
    nlinarith [sq_nonneg (|x t| - 1), sq_abs (x t)]
  have := mul_le_mul_of_nonneg_left hx hb
  linarith

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181 (transversality for the predetermined real wage gap): if
`∑ βᵗ e_t²` converges, `0 < β < 1`, then `βᵗ ∑_{s<t} |e_s| → 0` (Cauchy–Schwarz:
`(∑_{s<t} |e_s|)² ≤ (∑ βˢ e_s²)(∑_{s<t} β⁻ˢ)`). -/
theorem tendsto_disc_partial {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {e : ℕ → ℝ}
    (hs : Summable (fun t => β ^ t * e t ^ 2)) :
    Tendsto (fun t => β ^ t * ∑ s ∈ Finset.range t, |e s|) atTop (𝓝 0) := by
  set S := ∑' t, β ^ t * e t ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun t => by positivity
  have hbi : 1 < β⁻¹ := one_lt_inv_iff₀.2 ⟨hβ0, hβ1⟩
  set K := S / (β⁻¹ - 1) with hK
  have hK0 : 0 ≤ K := div_nonneg hS0 (by linarith)
  have hbound : ∀ t, (β ^ t * ∑ s ∈ Finset.range t, |e s|) ^ 2 ≤ K * β ^ t := by
    intro t
    have hcs : (∑ s ∈ Finset.range t, |e s|) ^ 2 ≤
        (∑ s ∈ Finset.range t, β ^ s * e s ^ 2) * ∑ s ∈ Finset.range t, β⁻¹ ^ s :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun s _ => by positivity)
        (fun s _ => by positivity) (fun s _ => by
          rw [sq_abs, mul_right_comm, ← mul_pow, mul_inv_cancel₀ hβ0.ne', one_pow, one_mul])
    have h1 : ∑ s ∈ Finset.range t, β ^ s * e s ^ 2 ≤ S :=
      hs.sum_le_tsum _ (fun s _ => by positivity)
    have h2 : ∑ s ∈ Finset.range t, β⁻¹ ^ s ≤ β⁻¹ ^ t / (β⁻¹ - 1) := by
      rw [geom_sum_eq hbi.ne']
      gcongr
      linarith
    have h3 : (∑ s ∈ Finset.range t, |e s|) ^ 2 ≤ S * (β⁻¹ ^ t / (β⁻¹ - 1)) :=
      hcs.trans (mul_le_mul h1 h2 (Finset.sum_nonneg fun s _ => by positivity) hS0)
    have hpow : (β ^ t) ^ 2 * β⁻¹ ^ t = β ^ t := by
      rw [inv_pow, sq]; field_simp
    calc (β ^ t * ∑ s ∈ Finset.range t, |e s|) ^ 2
        = (β ^ t) ^ 2 * (∑ s ∈ Finset.range t, |e s|) ^ 2 := by ring
      _ ≤ (β ^ t) ^ 2 * (S * (β⁻¹ ^ t / (β⁻¹ - 1))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = K * ((β ^ t) ^ 2 * β⁻¹ ^ t) := by rw [hK]; ring
      _ = K * β ^ t := by rw [hpow]
  have hlim : Tendsto (fun t => Real.sqrt (K * β ^ t)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul K).sqrt
    simpa using this
  refine squeeze_zero (fun t => by positivity) (fun t => ?_) hlim
  have hnn : 0 ≤ β ^ t * ∑ s ∈ Finset.range t, |e s| := by positivity
  rw [← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt (hbound t)

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181: `∑ βᵗ (a_t − b_t)²` converges when `∑ βᵗ a_t²` and `∑ βᵗ b_t²` do. -/
theorem summable_sub_sq {β : ℝ} (hβ0 : 0 ≤ β) {a b : ℕ → ℝ}
    (ha : Summable (fun t => β ^ t * a t ^ 2)) (hb : Summable (fun t => β ^ t * b t ^ 2)) :
    Summable (fun t => β ^ t * (a t - b t) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
    ((ha.mul_left 2).add (hb.mul_left 2))
  have hp : 0 ≤ β ^ t := pow_nonneg hβ0 t
  have : (a t - b t) ^ 2 ≤ 2 * a t ^ 2 + 2 * b t ^ 2 := by nlinarith [sq_nonneg (a t + b t)]
  have := mul_le_mul_of_nonneg_left this hp
  linarith

/-! ### The deterministic commitment problem -/

namespace Det

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (18), (20), (21), p. 172 (perfect foresight): the constraints
`π^p_t = β π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`, `π^w_t = β π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`,
`ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`, `t ≥ 0`, with `ω̃_{−1} = w0` given. -/
def Feasible (c : Coef) (dn : ℕ → ℝ) (w0 : ℝ) (y pp pw w : ℕ → ℝ) : Prop :=
  ∀ t, pp t = c.β * pp (t + 1) + c.kapP * y t + c.lamP * w t ∧
    pw t = c.β * pw (t + 1) + c.kapW * y t - c.lamW * w t ∧
    w t = prev w0 w t + pw t - pp t - dn t

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (30)–(33), p. 181 (perfect foresight): the first-order conditions with
multipliers `ζ₁, ζ₂, ζ₃` and `ζ_{1,−1} = ζ_{2,−1} = 0`. -/
def FOC (c : Coef) (y pp pw z1 z2 z3 : ℕ → ℝ) : Prop :=
  ∀ t, c.ay * y t + c.kapP * z1 t + c.kapW * z2 t = 0 ∧
    c.ap * pp t - (z1 t - prev 0 z1 t) + z3 t = 0 ∧
    c.aw * pw t - (z2 t - prev 0 z2 t) - z3 t = 0 ∧
    c.lamP * z1 t - c.lamW * z2 t + z3 t - c.β * z3 (t + 1) = 0

/-- Restated from the Chapter 6 project.
Galí (2015), p. 181: the multipliers are bounded. -/
def BoundedMult (z1 z2 z3 : ℕ → ℝ) : Prop := ∃ Z, ∀ t, |z1 t| ≤ Z ∧ |z2 t| ≤ Z ∧ |z3 t| ≤ Z

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (28), p. 179: the discounted period loss
`βᵗ ½ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)`. -/
noncomputable def lossTerm (c : Coef) (y pp pw : ℕ → ℝ) (t : ℕ) : ℝ :=
  c.β ^ t * ((c.ay * y t ^ 2 + c.ap * pp t ^ 2 + c.aw * pw t ^ 2) / 2)

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (28), p. 179: the loss is finite. -/
def FiniteLoss (c : Coef) (y pp pw : ℕ → ℝ) : Prop := Summable (lossTerm c y pp pw)

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (28), p. 179: the loss `½ ∑ βᵗ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)`
(used on finite-loss paths). -/
noncomputable def loss (c : Coef) (y pp pw : ℕ → ℝ) : ℝ := ∑' t, lossTerm c y pp pw t

/-- Restated from the Chapter 6 project.
Galí (2015), §6.4, p. 181: `(ỹ, π^p, π^w, ω̃)` solves the commitment problem: it is feasible,
has finite loss, and no feasible finite-loss path has a smaller loss. -/
def IsOptimal (c : Coef) (dn : ℕ → ℝ) (w0 : ℝ) (y pp pw w : ℕ → ℝ) : Prop :=
  Feasible c dn w0 y pp pw w ∧ FiniteLoss c y pp pw ∧
    ∀ y' pp' pw' w', Feasible c dn w0 y' pp' pw' w' → FiniteLoss c y' pp' pw' →
      loss c y pp pw ≤ loss c y' pp' pw'

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (28), p. 179: on a finite-loss path `∑ βᵗ ỹ_t²`, `∑ βᵗ (π^p_t)²` and
`∑ βᵗ (π^w_t)²` converge (positive weights). -/
theorem summable_sq {c : Coef} (hβ0 : 0 ≤ c.β) (hay : 0 < c.ay) (hap : 0 < c.ap)
    (haw : 0 < c.aw) {y pp pw : ℕ → ℝ} (hl : FiniteLoss c y pp pw) :
    Summable (fun t => c.β ^ t * y t ^ 2) ∧ Summable (fun t => c.β ^ t * pp t ^ 2) ∧
      Summable (fun t => c.β ^ t * pw t ^ 2) := by
  have key : ∀ t, 0 ≤ c.β ^ t * (c.ay * y t ^ 2) ∧ 0 ≤ c.β ^ t * (c.ap * pp t ^ 2) ∧
      0 ≤ c.β ^ t * (c.aw * pw t ^ 2) := fun t => ⟨by positivity, by positivity, by positivity⟩
  refine ⟨?_, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_) (hl.mul_left (2 / c.ay))
    rw [div_mul_eq_mul_div, le_div_iff₀ hay]
    unfold lossTerm
    nlinarith [key t]
  · refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_) (hl.mul_left (2 / c.ap))
    rw [div_mul_eq_mul_div, le_div_iff₀ hap]
    unfold lossTerm
    nlinarith [key t]
  · refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_) (hl.mul_left (2 / c.aw))
    rw [div_mul_eq_mul_div, le_div_iff₀ haw]
    unfold lossTerm
    nlinarith [key t]

/-- Restated from the Chapter 6 project.
Galí (2015), ch. 6, (21), p. 172: two feasible paths with the same `ω̃_{−1}` and the same shocks
have lagged real wage gaps differing by the accumulated relative wage-price inflation:
`ω̃_{t−1} − ω̃*_{t−1} = ∑_{s<t} ((π^w_s − π^w*_s) − (π^p_s − π^p*_s))`. -/
theorem prev_sub_eq_sum {c : Coef} {dn : ℕ → ℝ} {w0 : ℝ} {y pp pw w ys pps pws ws : ℕ → ℝ}
    (hf : Feasible c dn w0 y pp pw w) (hfs : Feasible c dn w0 ys pps pws ws) (t : ℕ) :
    prev w0 w t - prev w0 ws t =
      ∑ s ∈ Finset.range t, ((pw s - pws s) - (pp s - pps s)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih, prev_succ, prev_succ]
    have h1 := (hf t).2.2
    have h2 := (hfs t).2.2
    linarith

/-- Restated from the Chapter 6 project.
**Galí (2015), ch. 6, (30)–(33), p. 181 (sufficiency of the first-order conditions,
deterministic)**: if a feasible finite-loss path `(ỹ*, π^p*, π^w*, ω̃*)` satisfies (30)–(33) with
bounded multipliers (`ζ_{1,−1} = ζ_{2,−1} = 0`), then for every feasible finite-loss path
`L − L* = ½ ∑ βᵗ (a_y (ỹ_t − ỹ*_t)² + a_p (π^p_t − π^p*_t)² + a_w (π^w_t − π^w*_t)²)`: the
Lagrangian cross terms telescope, and the transversality term vanishes. -/
theorem loss_sub_hasSum {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → ℝ} {w0 : ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hf : Feasible c dn w0 y pp pw w) (hl : FiniteLoss c y pp pw)
    (hfs : Feasible c dn w0 ys pps pws ws) (hls : FiniteLoss c ys pps pws)
    (hξ : FOC c ys pps pws z1 z2 z3) (hZ : BoundedMult z1 z2 z3) :
    HasSum (fun t => c.β ^ t * ((c.ay * (y t - ys t) ^ 2 + c.ap * (pp t - pps t) ^ 2 +
        c.aw * (pw t - pws t) ^ 2) / 2)) (loss c y pp pw - loss c ys pps pws) := by
  obtain ⟨Z, hZ⟩ := hZ
  have hZ0 : 0 ≤ Z := (abs_nonneg _).trans (hZ 0).1
  obtain ⟨-, sp, sq⟩ := summable_sq hβ0.le hay hap haw hl
  obtain ⟨-, sps, sqs⟩ := summable_sq hβ0.le hay hap haw hls
  have sdp := summable_sub_sq hβ0.le sp sps
  have sdq := summable_sub_sq hβ0.le sq sqs
  have sde := summable_sub_sq hβ0.le sdq sdp
  have a1 := tendsto_disc_abs hβ0.le hβ1 sdp
  have a2 := tendsto_disc_abs hβ0.le hβ1 sdq
  have a3 := tendsto_disc_partial hβ0 hβ1 sde
  refine hasSum_of_telescope (hl.hasSum.sub hls.hasSum) (fun t => by positivity)
    (h := fun t => c.β ^ t * (prev 0 z1 t * (pp t - pps t) + prev 0 z2 t * (pw t - pws t) +
      (prev w0 w t - prev w0 ws t) * z3 t)) (fun t => ?_) (by simp) ?_
  · have key := lagrangian_alg c (hf t).1 (hf t).2.1 (hf t).2.2 (hfs t).1 (hfs t).2.1
      (hfs t).2.2 (hξ t).1 (hξ t).2.1 (hξ t).2.2.1 (hξ t).2.2.2
    simp only [lossTerm, prev_succ, pow_succ]
    linear_combination c.β ^ t * key
  · have hup := ((a1.add a2).add a3).const_mul Z
    rw [add_zero, add_zero, mul_zero] at hup
    refine squeeze_zero_norm (fun t => ?_) hup
    have hb : 0 ≤ c.β ^ t := pow_nonneg hβ0.le t
    have hz1 : |prev 0 z1 t| ≤ Z := by cases t <;> simp [hZ0, (hZ _).1]
    have hz2 : |prev 0 z2 t| ≤ Z := by cases t <;> simp [hZ0, (hZ _).2.1]
    have hz3 : |z3 t| ≤ Z := (hZ t).2.2
    have hW : |prev w0 w t - prev w0 ws t| ≤
        ∑ s ∈ Finset.range t, |(pw s - pws s) - (pp s - pps s)| := by
      rw [prev_sub_eq_sum hf hfs t]
      exact Finset.abs_sum_le_sum_abs _ _
    have e1 : |prev 0 z1 t * (pp t - pps t)| ≤ Z * |pp t - pps t| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hz1 (abs_nonneg _)
    have e2 : |prev 0 z2 t * (pw t - pws t)| ≤ Z * |pw t - pws t| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hz2 (abs_nonneg _)
    have e3 : |(prev w0 w t - prev w0 ws t) * z3 t| ≤
        Z * ∑ s ∈ Finset.range t, |(pw s - pws s) - (pp s - pps s)| := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul hz3 hW (abs_nonneg _) hZ0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb]
    have htri := abs_add_three (prev 0 z1 t * (pp t - pps t)) (prev 0 z2 t * (pw t - pws t))
      ((prev w0 w t - prev w0 ws t) * z3 t)
    have hle := mul_le_mul_of_nonneg_left (htri.trans (add_le_add (add_le_add e1 e2) e3)) hb
    linarith

/-- Restated from the Chapter 6 project.
**Galí (2015), §6.4, p. 181 (optimality, deterministic)**: a feasible finite-loss path
satisfying the first-order conditions (30)–(33) with bounded multipliers solves the commitment
problem. -/
theorem isOptimal_of_foc {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → ℝ} {w0 : ℝ} {ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hfs : Feasible c dn w0 ys pps pws ws) (hls : FiniteLoss c ys pps pws)
    (hξ : FOC c ys pps pws z1 z2 z3) (hZ : BoundedMult z1 z2 z3) :
    IsOptimal c dn w0 ys pps pws ws :=
  ⟨hfs, hls, fun _ _ _ _ hf hl => sub_nonneg.1
    ((loss_sub_hasSum hβ0 hβ1 hay hap haw hf hl hfs hls hξ hZ).nonneg
      (fun t => by positivity))⟩

/-- Restated from the Chapter 6 project.
**Galí (2015), §6.4, p. 181 (uniqueness, deterministic)**: a feasible finite-loss path with
the same loss as a path satisfying (30)–(33) with bounded multipliers coincides with it (all
four variables; the real wage gap by (21)). -/
theorem eq_of_loss_eq {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → ℝ} {w0 : ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hf : Feasible c dn w0 y pp pw w) (hl : FiniteLoss c y pp pw)
    (hfs : Feasible c dn w0 ys pps pws ws) (hls : FiniteLoss c ys pps pws)
    (hξ : FOC c ys pps pws z1 z2 z3) (hZ : BoundedMult z1 z2 z3)
    (heq : loss c y pp pw = loss c ys pps pws) : y = ys ∧ pp = pps ∧ pw = pws ∧ w = ws := by
  have hs := loss_sub_hasSum hβ0 hβ1 hay hap haw hf hl hfs hls hξ hZ
  rw [heq, sub_self] at hs
  have hz := (hasSum_zero_iff_of_nonneg (fun t => by positivity)).1 hs
  have ht : ∀ t, y t = ys t ∧ pp t = pps t ∧ pw t = pws t := fun t => by
    have h := congrFun hz t
    simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
      false_or] at h
    have k1 := mul_nonneg hay.le (sq_nonneg (y t - ys t))
    have k2 := mul_nonneg hap.le (sq_nonneg (pp t - pps t))
    have k3 := mul_nonneg haw.le (sq_nonneg (pw t - pws t))
    have e1 : c.ay * (y t - ys t) ^ 2 = 0 := by linarith
    have e2 : c.ap * (pp t - pps t) ^ 2 = 0 := by linarith
    have e3 : c.aw * (pw t - pws t) ^ 2 = 0 := by linarith
    simp only [mul_eq_zero, hay.ne', hap.ne', haw.ne', false_or, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff, sub_eq_zero] at e1 e2 e3
    exact ⟨e1, e2, e3⟩
  have hw : ∀ t, prev w0 w t = prev w0 ws t := fun t => by
    have := prev_sub_eq_sum hf hfs t
    rw [Finset.sum_eq_zero (fun s _ => by rw [(ht s).2.1, (ht s).2.2]; ring)] at this
    linarith
  refine ⟨funext fun t => (ht t).1, funext fun t => (ht t).2.1, funext fun t => (ht t).2.2,
    funext fun t => ?_⟩
  have := hw (t + 1)
  simpa using this

/-- Restated from the Chapter 6 project.
**Galí (2015), §6.4, p. 181 (necessity and sufficiency of the first-order conditions,
deterministic)**: if some feasible finite-loss path satisfies (30)–(33) with bounded multipliers
(the problem has a Lagrangian solution), then a feasible finite-loss path is optimal iff it
satisfies (30)–(33) with bounded multipliers, and the optimum is unique. -/
theorem isOptimal_iff_foc {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → ℝ} {w0 : ℝ} {ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hfs : Feasible c dn w0 ys pps pws ws) (hls : FiniteLoss c ys pps pws)
    (hξ : FOC c ys pps pws z1 z2 z3) (hZ : BoundedMult z1 z2 z3) {y pp pw w : ℕ → ℝ}
    (hf : Feasible c dn w0 y pp pw w) (hl : FiniteLoss c y pp pw) :
    (IsOptimal c dn w0 y pp pw w ↔
      ∃ z1' z2' z3', FOC c y pp pw z1' z2' z3' ∧ BoundedMult z1' z2' z3') ∧
    (IsOptimal c dn w0 y pp pw w ↔ y = ys ∧ pp = pps ∧ pw = pws ∧ w = ws) := by
  have hopt := isOptimal_of_foc hβ0 hβ1 hay hap haw hfs hls hξ hZ
  have h2 : IsOptimal c dn w0 y pp pw w ↔ y = ys ∧ pp = pps ∧ pw = pws ∧ w = ws := by
    constructor
    · rintro ⟨-, -, hmin⟩
      exact eq_of_loss_eq hβ0 hβ1 hay hap haw hf hl hfs hls hξ hZ
        (le_antisymm (hmin _ _ _ _ hfs hls) (hopt.2.2 _ _ _ _ hf hl))
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      exact hopt
  refine ⟨⟨fun h => ?_, fun ⟨z1', z2', z3', h1, h2⟩ =>
    isOptimal_of_foc hβ0 hβ1 hay hap haw hf hl h1 h2⟩, h2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h2.1 h
  exact ⟨z1, z2, z3, hξ, hZ⟩

/-- Restated from the Chapter 6 project.
**Galí (2015), §6.4, p. 181 (existence and uniqueness, deterministic)**: if the first-order
conditions have a feasible finite-loss solution with bounded multipliers, the commitment problem
has exactly one solution. -/
theorem existsUnique_optimal {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → ℝ} {w0 : ℝ} {ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hfs : Feasible c dn w0 ys pps pws ws) (hls : FiniteLoss c ys pps pws)
    (hξ : FOC c ys pps pws z1 z2 z3) (hZ : BoundedMult z1 z2 z3) :
    ∃! p : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ), IsOptimal c dn w0 p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  refine ⟨(ys, pps, pws, ws), isOptimal_of_foc hβ0 hβ1 hay hap haw hfs hls hξ hZ, ?_⟩
  rintro ⟨y, pp, pw, w⟩ h
  obtain ⟨h1, h2, h3, h4⟩ := (isOptimal_iff_foc hβ0 hβ1 hay hap haw hfs hls hξ hZ h.1 h.2.1).2.1 h
  simp only at h1 h2 h3 h4
  rw [h1, h2, h3, h4]

end Det
namespace Det

/-- Restated from the Chapter 6 project.
**Galí (2015), §6.4.1, p. 181 (demand shocks, deterministic)**: with demand shocks only the
natural real wage does not move (`Δωⁿ ≡ 0`, since `ωⁿ` depends on technology only, (16)); then,
starting from `ω̃_{−1} = 0`, the zero path (`x_t = 0` for all `t`) is the unique solution of the
commitment problem: it is feasible with zero loss, every loss is nonnegative, and it satisfies
(30)–(33) with zero multipliers. -/
theorem demand_zero_optimal {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hap : 0 < c.ap) (haw : 0 < c.aw) :
    IsOptimal c 0 0 0 0 0 0 ∧ loss c 0 0 0 = 0 ∧
      ∀ y pp pw w, IsOptimal c 0 0 y pp pw w ↔ y = 0 ∧ pp = 0 ∧ pw = 0 ∧ w = 0 := by
  have hf : Feasible c 0 0 0 0 0 0 := fun t => by cases t <;> simp
  have hl : FiniteLoss c 0 0 0 := by
    have : lossTerm c 0 0 0 = 0 := by funext t; simp [lossTerm]
    rw [FiniteLoss, this]; exact summable_zero
  have hξ : FOC c 0 0 0 0 0 0 := fun t => by cases t <;> simp
  have hZ : BoundedMult (0 : ℕ → ℝ) 0 0 := ⟨0, fun t => by simp⟩
  refine ⟨isOptimal_of_foc hβ0 hβ1 hay hap haw hf hl hξ hZ, by simp [loss, lossTerm],
    fun y pp pw w => ⟨fun h => ?_, ?_⟩⟩
  · exact (isOptimal_iff_foc hβ0 hβ1 hay hap haw hf hl hξ hZ h.1 h.2.1).2.1 h
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact isOptimal_of_foc hβ0 hβ1 hay hap haw hf hl hξ hZ

end Det

/-! ### Calibration, p. 209 -/

/-- Galí (2015), (10), p. 206, and p. 209: with `uⁿ = μ^w/φ` and `μ^w = log M_w` (`φ ≠ 0`), the
gross desired wage markup is `M_w = exp(φ uⁿ)`. -/
theorem markup_eq_exp {φ un Mw : ℝ} (hM : 0 < Mw) (hφ : φ ≠ 0)
    (h10 : un = Real.log Mw / φ) : Mw = Real.exp (φ * un) := by
  have h : φ * (Real.log Mw / φ) = Real.log Mw := by field_simp
  rw [h10, h, Real.exp_log hM]

/-- Galí (2015), p. 209: for `ε_w > 1` and `M > 1`, `M_w ≡ ε_w/(ε_w − 1) = M` holds iff
`ε_w = M/(M − 1)`. -/
theorem epsW_markup_iff {εw M : ℝ} (hε : 1 < εw) (hM : 1 < M) :
    εw / (εw - 1) = M ↔ εw = M / (M - 1) := by
  have h1 : εw - 1 ≠ 0 := (sub_pos.2 hε).ne'
  have h2 : M - 1 ≠ 0 := (sub_pos.2 hM).ne'
  rw [div_eq_iff h1, eq_div_iff h2]
  constructor <;> intro h <;> linarith

/-- Galí (2015), p. 209 (numerics): `1.2836 < e^{1/4} < 1.2841` (Taylor polynomial of degree 3
with Mathlib's remainder bound `Real.exp_bound`). -/
theorem exp_quarter_bounds : (1.2836 : ℝ) < Real.exp (1 / 4) ∧ Real.exp (1 / 4) < 1.2841 := by
  have h := Real.exp_bound (x := 1 / 4) (by norm_num [abs_of_pos]) (n := 4) (by norm_num)
  have h2 := abs_le.1 h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  constructor <;> linarith [h2.1, h2.2]

/-- **Galí (2015), p. 209 (calibration of `ε_w`)**: with `φ = 5` and `uⁿ = 0.05`, the condition
`ε_w/(ε_w − 1) = exp(φ uⁿ)` (with `ε_w > 1`) gives `ε_w = e^{1/4}/(e^{1/4} − 1) ∈ (4.5, 4.55)`. -/
theorem calibration_epsW {εw : ℝ} (hε : 1 < εw)
    (h : εw / (εw - 1) = Real.exp (5 * 0.05)) :
    εw = Real.exp (1 / 4) / (Real.exp (1 / 4) - 1) ∧ 4.5 < εw ∧ εw < 4.55 := by
  have hq : (5 : ℝ) * 0.05 = 1 / 4 := by norm_num
  rw [hq] at h
  obtain ⟨hl, hu⟩ := exp_quarter_bounds
  have he := (epsW_markup_iff hε (by linarith)).1 h
  have hpos : 0 < Real.exp (1 / 4) - 1 := by linarith
  refine ⟨he, ?_, ?_⟩
  · rw [he, lt_div_iff₀ hpos]; linarith
  · rw [he, div_lt_iff₀ hpos]; linarith

/-- **Galí (2015), p. 209 (average wage markup)**: at `φ = 5`, `uⁿ = 0.05` the net wage markup
`M_w − 1 = e^{1/4} − 1` lies in `(0.28, 0.29)` ("28 percent"). -/
theorem calibration_markup :
    (0.28 : ℝ) < Real.exp (5 * 0.05) - 1 ∧ Real.exp (5 * 0.05) - 1 < 0.29 := by
  have hq : (5 : ℝ) * 0.05 = 1 / 4 := by norm_num
  rw [hq]
  obtain ⟨hl, hu⟩ := exp_quarter_bounds
  constructor <;> linarith

/-- **Galí (2015), p. 209 (survey error 6: rounding)**: the printed `ε_w = 4.5` does not satisfy
the calibration condition exactly (`4.5/3.5 = 9/7 ≠ e^{1/4}`); it implies a net markup
`2/7 ≈ 28.6%`, while the exact calibration gives `ε_w ≈ 4.52` and a markup `≈ 28.4%`. The log
markup `μ^w = φ uⁿ` is exactly `0.25`. -/
theorem calibration_book_epsW :
    (4.5 : ℝ) / (4.5 - 1) - 1 = 2 / 7 ∧ (4.5 : ℝ) / (4.5 - 1) ≠ Real.exp (5 * 0.05) ∧
      (5 : ℝ) * 0.05 = 0.25 := by
  have hq : (5 : ℝ) * 0.05 = 1 / 4 := by norm_num
  obtain ⟨-, hu⟩ := exp_quarter_bounds
  refine ⟨by norm_num, ?_, by norm_num⟩
  rw [hq]
  intro h
  have : (4.5 : ℝ) / (4.5 - 1) = 9 / 7 := by norm_num
  rw [this] at h
  linarith

/-! ### The labour-force wealth effect, (17) and Fig. 7.2 -/

/-- Galí (2015), (6), p. 204: the participation equation `w − p = σ c + φ l + ξ` solved for the
labour force, `l = (ω − σ c − ξ)/φ`, given the real wage `ω = w − p` and consumption `c`. -/
noncomputable def laborForce (σ φ ξ ω c : ℝ) : ℝ := (ω - σ * c - ξ) / φ

/-- Galí (2015), (6), p. 204: `laborForce` satisfies (6), and is its unique solution
(`φ ≠ 0`). -/
theorem laborForce_iff {σ φ ξ ω c l : ℝ} (hφ : φ ≠ 0) :
    ω = σ * c + φ * l + ξ ↔ l = laborForce σ φ ξ ω c := by
  unfold laborForce
  rw [eq_div_iff hφ]
  constructor <;> intro h <;> linarith

/-- **Galí (2015), p. 210 (the wealth effect on participation)**: given the real wage,
`∂l/∂c = −σ/φ` (exact derivative of (6)). -/
theorem hasDerivAt_laborForce (σ φ ξ ω c : ℝ) :
    HasDerivAt (fun c => laborForce σ φ ξ ω c) (-σ / φ) c := by
  have h := HasDerivAt.div_const
    (HasDerivAt.sub_const ξ (HasDerivAt.const_sub ω (HasDerivAt.const_mul σ (hasDerivAt_id' c)))) φ
  exact HasDerivAt.congr_deriv h (by ring)

/-- **Galí (2015), p. 210 (countercyclical labour force)**: for `σ, φ > 0` the wealth effect is
negative, `−σ/φ < 0`, and the labour force is strictly decreasing in consumption at a given real
wage: a consumption decline (a monetary tightening, Fig. 7.2) raises participation. -/
theorem laborForce_strictAnti {σ φ ξ ω : ℝ} (hσ : 0 < σ) (hφ : 0 < φ) :
    -σ / φ < 0 ∧ StrictAnti (laborForce σ φ ξ ω) := by
  refine ⟨div_neg_of_neg_of_pos (by linarith) hφ, fun c c' hc => ?_⟩
  unfold laborForce
  rw [div_lt_div_iff_of_pos_right hφ]
  nlinarith

/-- Galí (2015), (5), p. 204: the marginal supplier of a labour type,
`L = (ω/(χ C^σ))^{1/φ}`, given the real wage `ω = W/P > 0` and consumption `C > 0`. -/
noncomputable def marginalParticipant (σ φ χ ω C : ℝ) : ℝ := (ω / (χ * C ^ σ)) ^ (1 / φ)

/-- **Galí (2015), (5), p. 204**: the marginal participant satisfies `ω = χ C^σ L^φ`. -/
theorem marginalParticipant_eq5 {σ φ χ ω C : ℝ} (hφ : φ ≠ 0) (hχ : 0 < χ) (hω : 0 < ω)
    (hC : 0 < C) : ω = χ * C ^ σ * marginalParticipant σ φ χ ω C ^ φ := by
  have hd : 0 < χ * C ^ σ := mul_pos hχ (Real.rpow_pos_of_pos hC σ)
  unfold marginalParticipant
  rw [← Real.rpow_mul (div_pos hω hd).le, one_div_mul_cancel hφ, Real.rpow_one]
  field_simp

/-- **Galí (2015), (5)–(6), p. 204 (exactness of (6) in `c`)**: with `c = log C`,
`log L = (log ω − σ c − log χ)/φ`, i.e. the log of the marginal participant is exactly
`laborForce` with `ξ = log χ`. -/
theorem log_marginalParticipant {σ φ χ ω : ℝ} (hχ : 0 < χ) (hω : 0 < ω) (c : ℝ) :
    Real.log (marginalParticipant σ φ χ ω (Real.exp c)) =
      laborForce σ φ (Real.log χ) (Real.log ω) c := by
  have hp : 0 < Real.exp c ^ σ := Real.rpow_pos_of_pos (Real.exp_pos c) σ
  unfold marginalParticipant laborForce
  rw [Real.log_rpow (div_pos hω (mul_pos hχ hp)), Real.log_div hω.ne' (mul_pos hχ hp).ne',
    Real.log_mul hχ.ne' hp.ne', Real.log_rpow (Real.exp_pos c), Real.log_exp]
  ring

/-- **Galí (2015), p. 210 (wealth effect, nonlinear model)**: the elasticity of the marginal
participant (5) with respect to consumption, at a given real wage, is `−σ/φ`:
`d log L / d log C = −σ/φ`. -/
theorem hasDerivAt_log_marginalParticipant {σ φ χ ω : ℝ} (hχ : 0 < χ) (hω : 0 < ω) (c : ℝ) :
    HasDerivAt (fun c => Real.log (marginalParticipant σ φ χ ω (Real.exp c))) (-σ / φ) c := by
  have h : (fun c => Real.log (marginalParticipant σ φ χ ω (Real.exp c))) =
      fun c => laborForce σ φ (Real.log χ) (Real.log ω) c :=
    funext fun c => log_marginalParticipant hχ hω c
  rw [h]
  exact hasDerivAt_laborForce _ _ _ _ c

/-! ### fn. 12: as `θ_w → 0` unemployment fluctuations vanish -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), (14), p. 207: the wage Phillips curve in the unemployment gap,
`π^w_t = β E_t π^w_{t+1} − λ_w φ û_t`. -/
def WagePC (β lamW φ : ℝ) (pw u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) - (lamW * φ) • u t

/-- **Galí (2015), (14), p. 207 (pathwise bound)**: if `|π^w_t| ≤ B` for all dates and states,
then (14) forces `|û_t| ≤ (1 + β) B/(λ_w φ)`. -/
theorem abs_unemp_le {β lamW φ B : ℝ} (hβ : 0 ≤ β) (hl : 0 < lamW) (hφ : 0 < φ)
    {pw u : ℕ → Ω → ℝ} (h14 : WagePC 𝔼 β lamW φ pw u) (hB : ∀ t ω, |pw t ω| ≤ B) (t : ℕ)
    (ω : Ω) : |u t ω| ≤ (1 + β) * B / (lamW * φ) := by
  have hk : 0 < lamW * φ := mul_pos hl hφ
  have e := congrFun (h14 t) ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
  have hE := abs_le.1 (𝔼.abs_E_le (hB (t + 1)) t ω)
  have hp := abs_le.1 (hB t ω)
  have hu : u t ω * (lamW * φ) = β * 𝔼.E t (pw (t + 1)) ω - pw t ω := by linarith
  rw [le_div_iff₀ hk, ← abs_of_pos hk, ← abs_mul, hu]
  refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [hE.1, hE.2, hp.1, hp.2]

/-- Galí (2015), p. 204: the wage Phillips curve slope as a function of the Calvo parameter,
`λ_w(θ_w) = (1 − θ_w)(1 − βθ_w)/(θ_w(1 + ε_w φ))`. -/
noncomputable def lamWOf (β εw φ θw : ℝ) : ℝ := (1 - θw) * (1 - β * θw) / θw / (1 + εw * φ)

/-- **Galí (2015), fn. 12, p. 211**: `λ_w → ∞` as `θ_w → 0⁺` (`1 + ε_w φ > 0`). -/
theorem tendsto_lamWOf_atTop {β εw φ : ℝ} (hd : 0 < 1 + εw * φ) :
    Tendsto (lamWOf β εw φ) (𝓝[>] 0) atTop := by
  have hc : Continuous (fun θ : ℝ => (1 - θ) * (1 - β * θ)) := by fun_prop
  have h1 : Tendsto (fun θ : ℝ => (1 - θ) * (1 - β * θ)) (𝓝[>] 0) (𝓝 1) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have h3 := (Tendsto.pos_mul_atTop one_pos h1 tendsto_inv_nhdsGT_zero).atTop_div_const hd
  refine Tendsto.congr (fun θ => ?_) h3
  simp [lamWOf, div_eq_mul_inv]

/-- **Galí (2015), fn. 12, p. 211 (unemployment fluctuations vanish as `θ_w → 0`)**: let, for each
`θ_w ∈ (0, 1)`, `(π^w(θ_w), û(θ_w))` satisfy (14) with slope `λ_w(θ_w)`, and let the wage
inflation paths be uniformly bounded, `|π^w_t(θ_w)| ≤ B`. Then `û(θ_w) → 0` as `θ_w → 0⁺`,
uniformly in dates and states. -/
theorem unemployment_vanishes {β εw φ B : ℝ} (hβ : 0 ≤ β) (hφ : 0 < φ) (hεw : 0 ≤ εw)
    (pw u : ℝ → ℕ → Ω → ℝ)
    (h14 : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, WagePC 𝔼 β (lamWOf β εw φ θ) φ (pw θ) (u θ))
    (hB : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, ∀ t ω, |pw θ t ω| ≤ B) :
    ∀ ε > 0, ∀ᶠ θ in 𝓝[>] 0, ∀ t ω, |u θ t ω| ≤ ε := by
  intro ε hε
  have hd : 0 < 1 + εw * φ := by positivity
  have hev := (tendsto_lamWOf_atTop (β := β) hd).eventually_ge_atTop
    (max 1 ((1 + β) * B / (φ * ε)))
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ hmem t ω
  have hl : 0 < lamWOf β εw φ θ := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hθ)
  refine (abs_unemp_le 𝔼 hβ hl hφ (h14 θ hmem) (hB θ hmem) t ω).trans ?_
  rw [div_le_iff₀ (mul_pos hl hφ)]
  have h2 : (1 + β) * B / (φ * ε) ≤ lamWOf β εw φ θ := (le_max_right _ _).trans hθ
  rw [div_le_iff₀ (mul_pos hφ hε)] at h2
  linarith [show lamWOf β εw φ θ * (φ * ε) = ε * (lamWOf β εw φ θ * φ) by ring]

/-- **Galí (2015), fn. 12, p. 211 (volatility)**: under the hypotheses of
`unemployment_vanishes`, the conditional second moments `E_s û_t²` converge to zero as
`θ_w → 0⁺`, uniformly in `s`, `t` and the state. -/
theorem unemployment_volatility_vanishes {β εw φ B : ℝ} (hβ : 0 ≤ β) (hφ : 0 < φ)
    (hεw : 0 ≤ εw) (pw u : ℝ → ℕ → Ω → ℝ)
    (h14 : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, WagePC 𝔼 β (lamWOf β εw φ θ) φ (pw θ) (u θ))
    (hB : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, ∀ t ω, |pw θ t ω| ≤ B) :
    ∀ ε > 0, ∀ᶠ θ in 𝓝[>] 0, ∀ s t ω, |𝔼.E s (fun ω' => u θ t ω' ^ 2) ω| ≤ ε := by
  intro ε hε
  have hm : 0 < min 1 ε := lt_min one_pos hε
  filter_upwards [unemployment_vanishes 𝔼 hβ hφ hεw pw u h14 hB (min 1 ε) hm] with θ hθ s t ω
  refine 𝔼.abs_E_le (fun ω' => ?_) s ω
  have h1 := hθ t ω'
  have h2 : |u θ t ω' ^ 2| ≤ min 1 ε ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : min 1 ε ^ 2 ≤ min 1 ε := by
    rw [sq]; exact mul_le_of_le_one_left hm.le (min_le_left _ _)
  exact h2.trans (h3.trans (min_le_right _ _))

/-- **Galí (2015), fn. 12, p. 211 (the uniform bound cannot be dropped)**: for every slope
`λ_w` (so for every `θ_w`), `û ≡ 1` with the constant, bounded wage inflation
`π^w ≡ −λ_w φ/(1 − β)` solves (14): without a bound on `π^w` uniform in `θ_w`, unemployment
fluctuations need not vanish. -/
theorem unemployment_need_not_vanish {β φ : ℝ} (hβ1 : β < 1) (lamW : ℝ) :
    WagePC 𝔼 β lamW φ (fun _ _ => -(lamW * φ) / (1 - β)) (fun _ _ => 1) := by
  intro t
  rw [𝔼.const t]
  funext ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  have h : (1 : ℝ) - β ≠ 0 := (sub_pos.2 hβ1).ne'
  field_simp
  ring

/-- **Galí (2015), (16), p. 208 and p. 206 (the flexible-wage limit)**: with flexible wages the
wage markup is at its desired value, `μ̂^w ≡ 0`, and then `φ û_t = μ̂^w_t` gives `û ≡ 0`: no
unemployment fluctuations (`φ ≠ 0`). -/
theorem flexible_wages_no_unemployment_gap {φ : ℝ} (hφ : φ ≠ 0) (mu u : ℕ → Ω → ℝ)
    (h16 : ∀ t, φ • u t = mu t) (hflex : ∀ t, mu t = 0) (t : ℕ) : u t = 0 := by
  have h := h16 t
  rw [hflex t, smul_eq_zero] at h
  exact h.resolve_left hφ

/-! ### Optimal policy, (18)–(21) -/

/-- Galí (2015), (13)–(16), pp. 207–208 (perfect foresight): the constraints of the Chapter 7
optimal-policy problem, `t ≥ 0`, `ω̃_{−1} = w0`:
(13) `π^p_t = β π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`, (14) `π^w_t = β π^w_{t+1} − λ_w φ û_t`,
(15) `ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`, (16) `φ û_t = ω̃_t − s_y ỹ_t`
(in the book `s_y = σ + φ/(1 − α)`). -/
def Feasible7 (c : Coef) (φ sy : ℝ) (dn : ℕ → ℝ) (w0 : ℝ) (y pp pw w u : ℕ → ℝ) : Prop :=
  ∀ t, pp t = c.β * pp (t + 1) + c.kapP * y t + c.lamP * w t ∧
    pw t = c.β * pw (t + 1) - c.lamW * φ * u t ∧
    w t = prev w0 w t + pw t - pp t - dn t ∧
    φ * u t = w t - sy * y t

/-- **Galí (2015), fn. 8, p. 208**: (14) and (16) combine into the Chapter 6 wage Phillips curve
`π^w_t = β π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`, `κ_w = λ_w s_y`. -/
theorem fn8_wage_pc {c : Coef} {φ sy : ℝ} (hk : c.kapW = c.lamW * sy) {pw pw' y w u : ℝ}
    (h14 : pw = c.β * pw' - c.lamW * φ * u) (h16 : φ * u = w - sy * y) :
    pw = c.β * pw' + c.kapW * y - c.lamW * w := by
  linear_combination h14 - y * hk - c.lamW * h16

/-- **Galí (2015), §7.2, pp. 207–208 (the Chapter 7 constraints are the Chapter 6 constraints
plus (16))**: for `κ_w = λ_w s_y` and `φ ≠ 0`, a path satisfies (13)–(16) iff it satisfies the
Chapter 6 constraints (18), (20), (21) and `û_t = (ω̃_t − s_y ỹ_t)/φ`. -/
theorem feasible7_iff {c : Coef} {φ sy : ℝ} (hk : c.kapW = c.lamW * sy) (hφ : φ ≠ 0)
    {dn : ℕ → ℝ} {w0 : ℝ} {y pp pw w u : ℕ → ℝ} :
    Feasible7 c φ sy dn w0 y pp pw w u ↔
      Det.Feasible c dn w0 y pp pw w ∧ u = fun t => (w t - sy * y t) / φ := by
  constructor
  · intro h
    refine ⟨fun t => ⟨(h t).1, fn8_wage_pc hk (h t).2.1 (h t).2.2.2, (h t).2.2.1⟩,
      funext fun t => ?_⟩
    rw [eq_div_iff hφ, mul_comm]
    exact (h t).2.2.2
  · rintro ⟨h, rfl⟩ t
    have h16 : φ * ((w t - sy * y t) / φ) = w t - sy * y t := by field_simp
    refine ⟨(h t).1, ?_, (h t).2.2, h16⟩
    linear_combination (h t).2.1 + y t * hk + c.lamW * h16

/-- Galí (2015), §7.3.2, p. 212: `(ỹ, π^p, π^w, ω̃, û)` solves the Chapter 7 commitment problem:
it satisfies (13)–(16), has finite loss, and no path satisfying (13)–(16) with finite loss has a
smaller loss. The loss is the Chapter 6 loss (unemployment does not enter it, p. 212). -/
def IsOptimal7 (c : Coef) (φ sy : ℝ) (dn : ℕ → ℝ) (w0 : ℝ) (y pp pw w u : ℕ → ℝ) : Prop :=
  Feasible7 c φ sy dn w0 y pp pw w u ∧ Det.FiniteLoss c y pp pw ∧
    ∀ y' pp' pw' w' u', Feasible7 c φ sy dn w0 y' pp' pw' w' u' →
      Det.FiniteLoss c y' pp' pw' → Det.loss c y pp pw ≤ Det.loss c y' pp' pw'

/-- **Galí (2015), §7.3.2, p. 212 (the Chapter 7 problem is the Chapter 6 problem)**: a path
solves the Chapter 7 problem iff `(ỹ, π^p, π^w, ω̃)` solves the Chapter 6 problem and unemployment
is given by (16), `û_t = (ω̃_t − s_y ỹ_t)/φ`. -/
theorem isOptimal7_iff {c : Coef} {φ sy : ℝ} (hk : c.kapW = c.lamW * sy) (hφ : φ ≠ 0)
    {dn : ℕ → ℝ} {w0 : ℝ} {y pp pw w u : ℕ → ℝ} :
    IsOptimal7 c φ sy dn w0 y pp pw w u ↔
      Det.IsOptimal c dn w0 y pp pw w ∧ u = fun t => (w t - sy * y t) / φ := by
  constructor
  · rintro ⟨hf, hl, hmin⟩
    obtain ⟨hf6, hu⟩ := (feasible7_iff hk hφ).1 hf
    exact ⟨⟨hf6, hl, fun y' pp' pw' w' hf' hl' =>
      hmin y' pp' pw' w' _ ((feasible7_iff hk hφ).2 ⟨hf', rfl⟩) hl'⟩, hu⟩
  · rintro ⟨⟨hf6, hl, hmin⟩, hu⟩
    exact ⟨(feasible7_iff hk hφ).2 ⟨hf6, hu⟩, hl, fun y' pp' pw' w' _ hf' hl' =>
      hmin y' pp' pw' w' ((feasible7_iff hk hφ).1 hf').1 hl'⟩

/-- Galí (2015), (18)–(21), p. 212, as printed (perfect foresight, `Δζ_t = ζ_t − ζ_{t−1}`,
`ζ_{−1} = 0`), with `κ_p = αλ_p/(1 − α)` and `κ_w = λ_w(σ + φ/(1 − α))`. -/
def FOC7 (β σ φ α εp εw lamP lamW : ℝ) (y pp pw z1 z2 z3 : ℕ → ℝ) : Prop :=
  ∀ t, (σ + (φ + α) / (1 - α)) * y t + α * lamP / (1 - α) * z1 t +
      lamW * (σ + φ / (1 - α)) * z2 t = 0 ∧
    εp / lamP * pp t - (z1 t - prev 0 z1 t) + z3 t = 0 ∧
    εw * (1 - α) / lamW * pw t - (z2 t - prev 0 z2 t) - z3 t = 0 ∧
    lamP * z1 t - lamW * z2 t + z3 t - β * z3 (t + 1) = 0

/-- **Galí (2015), (18)–(21), p. 212 (survey error 1)**: the printed optimality conditions are
exactly the Chapter 6 conditions (30)–(33) for the book's coefficients. The text says they are
"identical to those derived in chapter 3"; it should say chapter 6 (as the paragraph's first
sentence does). Also, the multipliers pair with the constraints as `ζ₁` ↔ (13), `ζ₂` ↔ (14) and
(16) combined (the Chapter 6 wage curve, fn. 8), `ζ₃` ↔ (15); the printed attribution "(13),
(14), and (15) and (16) combined" groups (16) with the wrong constraint. -/
theorem foc7_iff_ch6 (β σ φ α εp εw lamP lamW : ℝ) (y pp pw z1 z2 z3 : ℕ → ℝ) :
    FOC7 β σ φ α εp εw lamP lamW y pp pw z1 z2 z3 ↔
      Det.FOC (bookCoef β σ φ α εp εw lamP lamW) y pp pw z1 z2 z3 :=
  Iff.rfl

/-- Galí (2015), (28), p. 179, and p. 212: the loss weights `a_y = σ + (φ + α)/(1 − α)`,
`a_p = ε_p/λ_p`, `a_w = ε_w(1 − α)/λ_w` are positive. -/
theorem bookCoef_weights_pos {β σ φ α εp εw lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw) (hlp : 0 < lamP)
    (hlw : 0 < lamW) :
    0 < (bookCoef β σ φ α εp εw lamP lamW).ay ∧ 0 < (bookCoef β σ φ α εp εw lamP lamW).ap ∧
      0 < (bookCoef β σ φ α εp εw lamP lamW).aw := by
  have h1 : 0 < 1 - α := by linarith
  exact ⟨add_pos_of_pos_of_nonneg hσ (div_nonneg (by linarith) h1.le), div_pos hεp hlp,
    div_pos (mul_pos hεw h1) hlw⟩

/-- **Galí (2015), §7.3.2, p. 212 (the Chapter 7 optimum)**: if the Chapter 6 conditions, i.e.
the printed (18)–(21), have a solution `(ỹ*, π^p*, π^w*, ω̃*)` satisfying the Chapter 6
constraints with finite loss and bounded multipliers, then a path solves the Chapter 7 problem
iff it is that path together with `û*_t = (ω̃*_t − (σ + φ/(1 − α)) ỹ*_t)/φ`. -/
theorem isOptimal7_iff_eq {β σ φ α εp εw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw)
    (hlp : 0 < lamP) (hlw : 0 < lamW) {dn : ℕ → ℝ} {w0 : ℝ} {ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hfs : Det.Feasible (bookCoef β σ φ α εp εw lamP lamW) dn w0 ys pps pws ws)
    (hls : Det.FiniteLoss (bookCoef β σ φ α εp εw lamP lamW) ys pps pws)
    (hξ : FOC7 β σ φ α εp εw lamP lamW ys pps pws z1 z2 z3) (hZ : Det.BoundedMult z1 z2 z3)
    (y pp pw w u : ℕ → ℝ) :
    IsOptimal7 (bookCoef β σ φ α εp εw lamP lamW) φ (σ + φ / (1 - α)) dn w0 y pp pw w u ↔
      y = ys ∧ pp = pps ∧ pw = pws ∧ w = ws ∧
        u = fun t => (ws t - (σ + φ / (1 - α)) * ys t) / φ := by
  obtain ⟨hay, hap, haw⟩ := bookCoef_weights_pos (β := β) hσ hφ.le hα0 hα1 hεp hεw hlp hlw
  rw [isOptimal7_iff rfl hφ.ne']
  constructor
  · rintro ⟨hopt, rfl⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ :=
      (Det.isOptimal_iff_foc hβ0 hβ1 hay hap haw hfs hls hξ hZ hopt.1 hopt.2.1).2.1 hopt
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨Det.isOptimal_of_foc hβ0 hβ1 hay hap haw hfs hls hξ hZ, rfl⟩

/-- **Galí (2015), §7.3.2, p. 212 (existence and uniqueness)**: under the hypotheses of
`isOptimal7_iff_eq`, the Chapter 7 commitment problem has exactly one solution
`(ỹ, π^p, π^w, ω̃, û)`. -/
theorem existsUnique_optimal7 {β σ φ α εp εw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw)
    (hlp : 0 < lamP) (hlw : 0 < lamW) {dn : ℕ → ℝ} {w0 : ℝ} {ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hfs : Det.Feasible (bookCoef β σ φ α εp εw lamP lamW) dn w0 ys pps pws ws)
    (hls : Det.FiniteLoss (bookCoef β σ φ α εp εw lamP lamW) ys pps pws)
    (hξ : FOC7 β σ φ α εp εw lamP lamW ys pps pws z1 z2 z3) (hZ : Det.BoundedMult z1 z2 z3) :
    ∃! p : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ),
      IsOptimal7 (bookCoef β σ φ α εp εw lamP lamW) φ (σ + φ / (1 - α)) dn w0
        p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have key := isOptimal7_iff_eq hβ0 hβ1 hσ hφ hα0 hα1 hεp hεw hlp hlw hfs hls hξ hZ
  refine ⟨(ys, pps, pws, ws, fun t => (ws t - (σ + φ / (1 - α)) * ys t) / φ),
    (key _ _ _ _ _).2 ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  rintro ⟨y, pp, pw, w, u⟩ h
  obtain ⟨h1, h2, h3, h4, h5⟩ := (key _ _ _ _ _).1 h
  simp only at h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5]

/-- **Galí (2015), §7.3.2, p. 212 (necessity and sufficiency of (18)–(21))**: if the printed
conditions (18)–(21) have a Chapter 6-feasible finite-loss solution with bounded multipliers,
then a path satisfying (13)–(16) with finite loss is optimal iff it satisfies (18)–(21) with
bounded multipliers. -/
theorem isOptimal7_iff_foc {β σ φ α εp εw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw)
    (hlp : 0 < lamP) (hlw : 0 < lamW) {dn : ℕ → ℝ} {w0 : ℝ} {ys pps pws ws z1 z2 z3 : ℕ → ℝ}
    (hfs : Det.Feasible (bookCoef β σ φ α εp εw lamP lamW) dn w0 ys pps pws ws)
    (hls : Det.FiniteLoss (bookCoef β σ φ α εp εw lamP lamW) ys pps pws)
    (hξ : FOC7 β σ φ α εp εw lamP lamW ys pps pws z1 z2 z3) (hZ : Det.BoundedMult z1 z2 z3)
    {y pp pw w u : ℕ → ℝ}
    (hf : Feasible7 (bookCoef β σ φ α εp εw lamP lamW) φ (σ + φ / (1 - α)) dn w0 y pp pw w u)
    (hl : Det.FiniteLoss (bookCoef β σ φ α εp εw lamP lamW) y pp pw) :
    IsOptimal7 (bookCoef β σ φ α εp εw lamP lamW) φ (σ + φ / (1 - α)) dn w0 y pp pw w u ↔
      ∃ z1' z2' z3', FOC7 β σ φ α εp εw lamP lamW y pp pw z1' z2' z3' ∧
        Det.BoundedMult z1' z2' z3' := by
  obtain ⟨hay, hap, haw⟩ := bookCoef_weights_pos (β := β) hσ hφ.le hα0 hα1 hεp hεw hlp hlw
  obtain ⟨hf6, hu⟩ := (feasible7_iff rfl hφ.ne').1 hf
  rw [isOptimal7_iff rfl hφ.ne']
  have h := (Det.isOptimal_iff_foc hβ0 hβ1 hay hap haw hfs hls hξ hZ hf6 hl).1
  exact ⟨fun h' => h.1 h'.1, fun h' => ⟨h.2 h', hu⟩⟩

/-! ### p. 213: the efficient response to technology under `σ = 1` -/

/-- Galí (2015), p. 208: `ψ_ya = (1 + φ)/(σ(1 − α) + φ + α)`. -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- Galí (2015), p. 208: `ψ_wa = (1 − α ψ_ya)/(1 − α)`. -/
noncomputable def psiWA (σ φ α : ℝ) : ℝ := (1 - α * psiYA σ φ α) / (1 - α)

/-- **Galí (2015), p. 213**: under `σ = 1`, `ψ_ya = 1` (`φ ≥ 0`). -/
theorem psiYA_sigma_one {φ α : ℝ} (hφ : 0 ≤ φ) : psiYA 1 φ α = 1 := by
  unfold psiYA
  rw [show (1 : ℝ) * (1 - α) + φ + α = 1 + φ by ring, div_self (by linarith)]

/-- **Galí (2015), p. 213**: under `σ = 1`, `ψ_wa = 1` (the natural real wage moves one-for-one
with technology). -/
theorem psiWA_sigma_one {φ α : ℝ} (hφ : 0 ≤ φ) (hα : α ≠ 1) : psiWA 1 φ α = 1 := by
  unfold psiWA
  rw [psiYA_sigma_one hφ, mul_one, div_self (sub_ne_zero.2 (Ne.symm hα))]

/-- Galí (2015), p. 208: output (log deviation from steady state) `ŷ = ψ_ya a + ỹ`. -/
noncomputable def outputDev (σ φ α a ygap : ℝ) : ℝ := psiYA σ φ α * a + ygap

/-- Galí (2015), (9), p. 206: employment `n̂ = (ŷ − a)/(1 − α)`. -/
noncomputable def employmentDev (σ φ α a ygap : ℝ) : ℝ := (outputDev σ φ α a ygap - a) / (1 - α)

/-- Galí (2015), (16), p. 208: the unemployment gap `û = (ω̃ − (σ + φ/(1 − α)) ỹ)/φ`. -/
noncomputable def unempGap (σ φ α wgap ygap : ℝ) : ℝ := (wgap - (σ + φ / (1 - α)) * ygap) / φ

/-- Galí (2015), (7), p. 205: the labour force `l̂ = n̂ + û`. -/
noncomputable def laborForceDev (σ φ α a wgap ygap : ℝ) : ℝ :=
  employmentDev σ φ α a ygap + unempGap σ φ α wgap ygap

/-- Galí (2015), p. 208: the real wage `ω̂ = ψ_wa a + ω̃`. -/
noncomputable def realWageDev (σ φ α a wgap : ℝ) : ℝ := psiWA σ φ α * a + wgap

/-- **Galí (2015), (6), (7), (9), (16), pp. 204–208 (consistency of participation)**: the labour
force `l̂ = n̂ + û` satisfies the participation equation (6) in deviations, with `c = y`:
`ω̂ = σ ŷ + φ l̂` (`φ ≠ 0`, `α ≠ 1`, `σ(1 − α) + φ + α ≠ 0`). -/
theorem participation_consistent {σ φ α a wgap ygap : ℝ} (hφ : φ ≠ 0) (hα : α ≠ 1)
    (hD : σ * (1 - α) + φ + α ≠ 0) :
    realWageDev σ φ α a wgap =
      σ * outputDev σ φ α a ygap + φ * laborForceDev σ φ α a wgap ygap := by
  have h1 : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold realWageDev outputDev laborForceDev employmentDev unempGap outputDev psiWA psiYA
  field_simp
  ring

/-- **Galí (2015), p. 213 (the efficient response to technology under `σ = 1`)**: at the efficient
allocation (zero output and real wage gaps), `ψ_ya = ψ_wa = 1`, output moves one-for-one with
technology (`ŷ = a`), employment and participation do not respond (`n̂ = l̂ = 0`), the unemployment
gap is zero, and the real wage moves one-for-one (`ω̂ = a`). -/
theorem efficient_technology_sigma_one {φ α : ℝ} (hφ : 0 < φ) (hα : α ≠ 1) (a : ℝ) :
    psiYA 1 φ α = 1 ∧ psiWA 1 φ α = 1 ∧ outputDev 1 φ α a 0 = a ∧ employmentDev 1 φ α a 0 = 0 ∧
      unempGap 1 φ α 0 0 = 0 ∧ laborForceDev 1 φ α a 0 0 = 0 ∧ realWageDev 1 φ α a 0 = a := by
  have hy := psiYA_sigma_one (α := α) hφ.le
  have hw := psiWA_sigma_one hφ.le hα
  have ho : outputDev 1 φ α a 0 = a := by simp [outputDev, hy]
  have hn : employmentDev 1 φ α a 0 = 0 := by simp [employmentDev, ho]
  have hu : unempGap 1 φ α 0 0 = 0 := by simp [unempGap]
  refine ⟨hy, hw, ho, hn, hu, by simp [laborForceDev, hn, hu], by simp [realWageDev, hw]⟩

/-- **Galí (2015), p. 213 (`σ = 1` is what makes employment unresponsive)**: for a nonzero
technology shock (`a ≠ 0`, `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`), employment at the efficient allocation
does not respond iff `σ = 1`. -/
theorem efficient_employment_zero_iff {σ φ α a : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (ha : a ≠ 0) : employmentDev σ φ α a 0 = 0 ↔ σ = 1 := by
  have h1 : 0 < 1 - α := by linarith
  have hD : 0 < σ * (1 - α) + φ + α := by positivity
  unfold employmentDev outputDev psiYA
  rw [div_eq_zero_iff, or_iff_left h1.ne', add_zero, sub_eq_zero, div_mul_eq_mul_div,
    div_eq_iff hD.ne']
  constructor
  · intro h
    have h2 : (1 + φ) = σ * (1 - α) + φ + α := mul_right_cancel₀ ha (by linarith)
    have h3 : (σ - 1) * (1 - α) = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h | h
    · linarith
    · linarith
  · rintro rfl
    ring

/-! ### p. 214: demand shocks -/

/-- **Galí (2015), p. 214 (demand shocks, optimal policy)**: with demand shocks only, technology
is constant, so `Δωⁿ ≡ 0` (`ωⁿ = ψ_wa a`, p. 208), and starting from `ω̃_{−1} = 0` the Chapter 7
optimum is unique and equal to zero in every variable, `û` included (Chapter 6 §6.4.1 plus (16)).
The demand shifter only moves `rⁿ`, which enters the dynamic IS equation (12), not the problem. -/
theorem demand_shock_optimal_iff {β σ φ α εp εw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw)
    (hlp : 0 < lamP) (hlw : 0 < lamW) (y pp pw w u : ℕ → ℝ) :
    IsOptimal7 (bookCoef β σ φ α εp εw lamP lamW) φ (σ + φ / (1 - α)) 0 0 y pp pw w u ↔
      y = 0 ∧ pp = 0 ∧ pw = 0 ∧ w = 0 ∧ u = 0 := by
  obtain ⟨hay, hap, haw⟩ := bookCoef_weights_pos (β := β) hσ hφ.le hα0 hα1 hεp hεw hlp hlw
  rw [isOptimal7_iff rfl hφ.ne', (Det.demand_zero_optimal hβ0 hβ1 hay hap haw).2.2 y pp pw w]
  constructor
  · rintro ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    funext t
    simp
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    funext t
    simp

/-- **Galí (2015), p. 214 (full insulation of the labour market)**: under the optimal policy,
with demand shocks only (`a ≡ 0`), output, employment, the labour force, the unemployment rate
and the real wage do not respond at any date. -/
theorem demand_shock_labour_market {β σ φ α εp εw lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw)
    (hlp : 0 < lamP) (hlw : 0 < lamW) {y pp pw w u : ℕ → ℝ}
    (h : IsOptimal7 (bookCoef β σ φ α εp εw lamP lamW) φ (σ + φ / (1 - α)) 0 0 y pp pw w u)
    (t : ℕ) :
    u t = 0 ∧ unempGap σ φ α (w t) (y t) = 0 ∧ outputDev σ φ α 0 (y t) = 0 ∧
      employmentDev σ φ α 0 (y t) = 0 ∧ laborForceDev σ φ α 0 (w t) (y t) = 0 ∧
      realWageDev σ φ α 0 (w t) = 0 := by
  obtain ⟨rfl, -, -, rfl, rfl⟩ :=
    (demand_shock_optimal_iff hβ0 hβ1 hσ hφ hα0 hα1 hεp hεw hlp hlw y pp pw w u).1 h
  simp [unempGap, outputDev, employmentDev, laborForceDev, realWageDev]

/-! ### (22): the simple rule with unemployment -/

/-- Galí (2015), (22), p. 214, as printed: `i_t = 0.01 + 1.5 π^p_t − 0.5 u_t`, with `u_t` the
unemployment rate in levels. -/
def Rule22Level (i pp u : ℝ) : Prop := i = 0.01 + 1.5 * pp - 0.5 * u

/-- **Galí (2015), (22), p. 214 (survey error 5)**: with `u_t = uⁿ + û_t`, the printed rule is the
gap rule `i_t = (0.01 − 0.5 uⁿ) + 1.5 π^p_t − 0.5 û_t`: the level/gap choice shifts the
intercept by `0.5 uⁿ`. -/
theorem rule22_level_iff_gap {un i pp uhat : ℝ} :
    Rule22Level i pp (un + uhat) ↔ i = (0.01 - 0.5 * un) + 1.5 * pp - 0.5 * uhat := by
  unfold Rule22Level
  constructor <;> intro h <;> linarith

/-- Galí (2015), (22), p. 214: at `uⁿ = 0.05` the implied gap-rule intercept is `−0.015`. -/
theorem rule22_book_intercept : (0.01 : ℝ) - 0.5 * 0.05 = -0.015 := by norm_num

/-- **Galí (2015), (22), p. 214 (survey error 5)**: read in levels, the rule is inconsistent with
the zero-inflation steady state `i = ρ ≈ 0.01`, `π^p = 0`, `u = uⁿ = 0.05`. -/
theorem rule22_level_not_steady : ¬ Rule22Level 0.01 0 0.05 := by
  unfold Rule22Level
  norm_num

/-- Galí (2015), (22), p. 214: read in the gap `û`, the rule is consistent with the zero-inflation
steady state (`i = 0.01`, `π^p = 0`, `û = 0`). -/
theorem rule22_gap_steady : (0.01 : ℝ) = 0.01 + 1.5 * 0 - 0.5 * 0 := by norm_num

/-- **Galí (2015), (22), p. 214 (the intercept is irrelevant for the impulse responses)**:
deviations from any reference point satisfying the rule obey `î = 1.5 π̂^p − 0.5 û`, whatever
the intercept; so Figs. 7.5–7.6 are unaffected by survey error 5. -/
theorem rule22_deviation {i pp u i' pp' u' : ℝ} (h : Rule22Level i pp u)
    (h' : Rule22Level i' pp' u') : i - i' = 1.5 * (pp - pp') - 0.5 * (u - u') := by
  unfold Rule22Level at h h'
  rw [h, h']
  ring

end Gali.Unemployment.Policy
