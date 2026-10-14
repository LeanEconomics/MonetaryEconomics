/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.Expectations
import StickyWagesPrices.Determinacy4
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum

/-!
# Optimal monetary policy with sticky wages and prices

Galí (2015), Section 6.4, pp. 181–185, and Appendix 6.2, p. 192.

The central bank minimises the welfare loss (28),
`𝕎 = ½ E_0 ∑ βᵗ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)` with `a_y = σ + (φ + α)/(1 − α)`,
`a_p = ε_p/λ_p`, `a_w = ε_w(1 − α)/λ_w`, subject to (18), (20), (21) for `t ≥ 0`, given
`ω̃_{−1}`. The model equations and the loss are stated here directly (no other chain imported);
the coefficients are bundled in `Coef`, the book's values in `bookCoef`. Equations hold for an
arbitrary `ExpectationSystem`, so results cover perfect foresight and genuine uncertainty.

## Main results

* **Commitment, deterministic** (`Det`, all feasible paths with finite loss): the Lagrangian
  identity `lagrangian_alg`; transversality for the predetermined real wage gap
  (`tendsto_disc_partial`, Cauchy–Schwarz); `Det.loss_sub_hasSum` (the excess loss is the
  discounted quadratic form of the deviations); SUFFICIENCY `Det.isOptimal_of_foc`, UNIQUENESS
  `Det.eq_of_loss_eq`, NECESSITY (whenever (30)–(33) have a bounded-multiplier solution)
  `Det.isOptimal_iff_foc`, `Det.existsUnique_optimal`.
* **Commitment, stochastic** (`Stoch`, bounded adapted plans, pull-out property):
  `Stoch.period_identity`, `Stoch.E0_identity`, `Stoch.expLoss_sub_hasSum`,
  `Stoch.commitment_optimal` (optimal state by state; unique in conditional mean square).
* **Appendix 6.2**: `Stoch.matrix_form_iff` — (18), (20), (21), (30)–(33) ⇔
  `A₀* x_t = A₁* E_t x_{t+1} + B₀* Δa_t` for the printed 7 × 7 matrices.
* **§6.4.1**: `Det.demand_zero_optimal`, `Stoch.demand_zero_optimal` (zero path optimal and
  unique); `Stoch.rule_implements` (the rule `i_t = rⁿ_t + φ_p π^p_t` supports it, uniquely under
  `RuleDeterminate`); determinacy for `φ_p > 1` and general parameters from the p. 174 theorem
  (`Determinacy4`): `Stoch.rule_isSol`, `Stoch.ruleDeterminate_of_phiP`,
  `Stoch.ruleDeterminate_book`, and the unconditional `Stoch.rule_implements_book`; for
  `κ_p = κ_w` an elementary proof and the converse: `Stoch.ruleDeterminate_of_kap_eq`,
  `Stoch.not_ruleDeterminate`, `Stoch.ruleDeterminate_iff` (determinate iff `φ_p > 1`), via the
  relative-inflation block `Stoch.block_zero` and the Chapter 3 system `schur_ruleA_iff`.
* **fn. 6, (34)–(36)**: `book_fn6`, `book_composite_slope`, `Stoch.composite_nkpc` (36) with the
  general slope `κ̄ = (λ_w κ_p + λ_p κ_w)/(λ_p + λ_w)` (survey error 3), `Det.composite_foc`,
  `Stoch.composite_foc` (34)–(35).
* **p. 184, special case optimality** (survey Note N6.1 separation, replacing the book's argument,
  which checks only the necessary conditions (34)–(35): survey error 2,
  `composite_path_satisfies_34_35`): `separation`, `Stoch.proj_plan`,
  `Stoch.periodLoss_sub_proj` (pathwise), `Stoch.composite_targeting_optimal`,
  `Stoch.exists_composite_plan`, `Stoch.composite_targeting_solves` (under `E_0`, by
  monotonicity); `Det.block_zero_finite`, `Det.composite_targeting_optimal`,
  `Det.composite_targeting_existsUnique` (among all finite-loss paths).
* **Composite weights and targeting**: `wage_weight_strictMonoOn`, `price_weight_strictMonoOn`;
  `Stoch.composite_zero_iff` (strict composite targeting ⇔ `ỹ ≡ 0`, all parameters).
-/

namespace Gali.StickyWagesPrices.OptimalPolicy

open Filter Topology

/-! ### Coefficients and lags -/

/-- Galí (2015), (18), (20), (28), pp. 172, 179: the coefficients of the optimal-policy problem:
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

/-- Galí (2015), (18), (20), (28), pp. 172, 179: the book's coefficients, with
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

/-- Galí (2015), (21), p. 172: the lag `x_{t−1}` of a sequence with initial value `x_{−1} = x0`
(used for `ω̃_{t−1}` with `ω̃_{−1}` given, and for the multipliers with `ζ_{−1} = 0`). -/
def prev {α : Type*} (x0 : α) (x : ℕ → α) : ℕ → α
  | 0 => x0
  | t + 1 => x t

/-- Galí (2015), p. 181: `x_{−1} = x0`. -/
@[simp] theorem prev_zero {α : Type*} (x0 : α) (x : ℕ → α) : prev x0 x 0 = x0 := rfl

/-- Galí (2015), p. 181: the lag at date `t + 1` is the date-`t` value. -/
@[simp] theorem prev_succ {α : Type*} (x0 : α) (x : ℕ → α) (t : ℕ) : prev x0 x (t + 1) = x t :=
  rfl

/-- Galí (2015), p. 181: the lag of a difference with common initial value starts at zero. -/
theorem prev_sub {α : Type*} [AddGroup α] (x0 : α) (x x' : ℕ → α) (t : ℕ) :
    prev x0 x t - prev x0 x' t = prev 0 (fun s => x s - x' s) t := by
  cases t <;> simp

/-! ### The Lagrangian identity -/

/-- **Galí (2015), (30)–(33), p. 181 (the Lagrangian identity, one period)**: if `(ỹ*, π^p*, π^w*,
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

/-- Galí (2015), p. 181 (the Lagrangian argument, abstract form): if `g_t = D_t + (h_{t+1} − h_t)`
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

/-- Galí (2015), p. 181 (transversality): if `∑ βᵗ x_t²` converges, `0 ≤ β < 1`, then
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

/-- Galí (2015), p. 181 (transversality for the predetermined real wage gap): if
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

/-- Galí (2015), p. 181: `∑ βᵗ (a_t − b_t)²` converges when `∑ βᵗ a_t²` and `∑ βᵗ b_t²` do. -/
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

/-- Galí (2015), (18), (20), (21), p. 172 (perfect foresight): the constraints
`π^p_t = β π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`, `π^w_t = β π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`,
`ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`, `t ≥ 0`, with `ω̃_{−1} = w0` given. -/
def Feasible (c : Coef) (dn : ℕ → ℝ) (w0 : ℝ) (y pp pw w : ℕ → ℝ) : Prop :=
  ∀ t, pp t = c.β * pp (t + 1) + c.kapP * y t + c.lamP * w t ∧
    pw t = c.β * pw (t + 1) + c.kapW * y t - c.lamW * w t ∧
    w t = prev w0 w t + pw t - pp t - dn t

/-- Galí (2015), (30)–(33), p. 181 (perfect foresight): the first-order conditions with
multipliers `ζ₁, ζ₂, ζ₃` and `ζ_{1,−1} = ζ_{2,−1} = 0`. -/
def FOC (c : Coef) (y pp pw z1 z2 z3 : ℕ → ℝ) : Prop :=
  ∀ t, c.ay * y t + c.kapP * z1 t + c.kapW * z2 t = 0 ∧
    c.ap * pp t - (z1 t - prev 0 z1 t) + z3 t = 0 ∧
    c.aw * pw t - (z2 t - prev 0 z2 t) - z3 t = 0 ∧
    c.lamP * z1 t - c.lamW * z2 t + z3 t - c.β * z3 (t + 1) = 0

/-- Galí (2015), p. 181: the multipliers are bounded. -/
def BoundedMult (z1 z2 z3 : ℕ → ℝ) : Prop := ∃ Z, ∀ t, |z1 t| ≤ Z ∧ |z2 t| ≤ Z ∧ |z3 t| ≤ Z

/-- Galí (2015), (28), p. 179: the discounted period loss
`βᵗ ½ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)`. -/
noncomputable def lossTerm (c : Coef) (y pp pw : ℕ → ℝ) (t : ℕ) : ℝ :=
  c.β ^ t * ((c.ay * y t ^ 2 + c.ap * pp t ^ 2 + c.aw * pw t ^ 2) / 2)

/-- Galí (2015), (28), p. 179: the loss is finite. -/
def FiniteLoss (c : Coef) (y pp pw : ℕ → ℝ) : Prop := Summable (lossTerm c y pp pw)

/-- Galí (2015), (28), p. 179: the loss `½ ∑ βᵗ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)`
(used on finite-loss paths). -/
noncomputable def loss (c : Coef) (y pp pw : ℕ → ℝ) : ℝ := ∑' t, lossTerm c y pp pw t

/-- Galí (2015), §6.4, p. 181: `(ỹ, π^p, π^w, ω̃)` solves the commitment problem: it is feasible,
has finite loss, and no feasible finite-loss path has a smaller loss. -/
def IsOptimal (c : Coef) (dn : ℕ → ℝ) (w0 : ℝ) (y pp pw w : ℕ → ℝ) : Prop :=
  Feasible c dn w0 y pp pw w ∧ FiniteLoss c y pp pw ∧
    ∀ y' pp' pw' w', Feasible c dn w0 y' pp' pw' w' → FiniteLoss c y' pp' pw' →
      loss c y pp pw ≤ loss c y' pp' pw'

/-- Galí (2015), (28), p. 179: on a finite-loss path `∑ βᵗ ỹ_t²`, `∑ βᵗ (π^p_t)²` and
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

/-- Galí (2015), (21), p. 172: two feasible paths with the same `ω̃_{−1}` and the same shocks
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

/-- **Galí (2015), (30)–(33), p. 181 (sufficiency of the first-order conditions,
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

/-- **Galí (2015), §6.4, p. 181 (optimality, deterministic)**: a feasible finite-loss path
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

/-- **Galí (2015), §6.4, p. 181 (uniqueness, deterministic)**: a feasible finite-loss path with
the same loss as a path satisfying (30)–(33) with bounded multipliers coincides with it (all four
variables; the real wage gap by (21)). -/
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

/-- **Galí (2015), §6.4, p. 181 (necessity and sufficiency of the first-order conditions,
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

/-- **Galí (2015), §6.4, p. 181 (existence and uniqueness, deterministic)**: if the first-order
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

/-! ### The commitment problem under uncertainty -/

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), (18), (20), (21), p. 172: the constraints of the policy problem, for an arbitrary
expectation system: `π^p_t = β E_t π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`,
`π^w_t = β E_t π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`, `ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`, with
`ω̃_{−1} = w0` given. -/
def Constr (c : Coef) (dn : ℕ → Ω → ℝ) (w0 : Ω → ℝ) (y pp pw w : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pp t = c.β • 𝔼.E t (pp (t + 1)) + c.kapP • y t + c.lamP • w t ∧
    pw t = c.β • 𝔼.E t (pw (t + 1)) + c.kapW • y t - c.lamW • w t ∧
    w t = prev w0 w t + pw t - pp t - dn t

/-- Galí (2015), §6.4, p. 181: an admissible plan: bounded adapted output gap, price and wage
inflation and real wage gap satisfying the constraints (18), (20), (21). -/
def Plan (c : Coef) (dn : ℕ → Ω → ℝ) (w0 : Ω → ℝ) (y pp pw w : ℕ → Ω → ℝ) : Prop :=
  Constr 𝔼 c dn w0 y pp pw w ∧ 𝔼.Adapted y ∧ 𝔼.Adapted pp ∧ 𝔼.Adapted pw ∧ 𝔼.Adapted w ∧
    BoundedProc y ∧ BoundedProc pp ∧ BoundedProc pw ∧ BoundedProc w

/-- Galí (2015), (30)–(33), p. 181: the first-order conditions of the commitment problem,
`a_y ỹ_t + κ_p ζ_{1,t} + κ_w ζ_{2,t} = 0`, `a_p π^p_t − Δζ_{1,t} + ζ_{3,t} = 0`,
`a_w π^w_t − Δζ_{2,t} − ζ_{3,t} = 0`, `λ_p ζ_{1,t} − λ_w ζ_{2,t} + ζ_{3,t} − β E_t ζ_{3,t+1} = 0`,
with `ζ_{1,−1} = ζ_{2,−1} = 0`. -/
def FOCs (c : Coef) (y pp pw z1 z2 z3 : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c.ay • y t + c.kapP • z1 t + c.kapW • z2 t = 0 ∧
    c.ap • pp t - (z1 t - prev 0 z1 t) + z3 t = 0 ∧
    c.aw • pw t - (z2 t - prev 0 z2 t) - z3 t = 0 ∧
    c.lamP • z1 t - c.lamW • z2 t + z3 t - c.β • 𝔼.E t (z3 (t + 1)) = 0

/-- Galí (2015), (28), p. 179: the period loss `½ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)`. -/
noncomputable def periodLoss (c : Coef) (y pp pw : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (c.ay * y t ω ^ 2 + c.ap * pp t ω ^ 2 + c.aw * pw t ω ^ 2) / 2

/-- Galí (2015), (28), p. 179: the welfare loss `𝕎 = E_0 ∑ βᵗ ½ (a_y ỹ_t² + a_p (π^p_t)² +
a_w (π^w_t)²)` (a date-0 random variable). -/
noncomputable def expLoss (c : Coef) (y pp pw : ℕ → Ω → ℝ) : Ω → ℝ :=
  𝔼.E 0 (fun ω => ∑' t, c.β ^ t * periodLoss c y pp pw t ω)

/-- Galí (2015), (28), p. 179: the period loss of the deviations of one plan from another. -/
noncomputable def devLoss (c : Coef) (y pp pw ys pps pws : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (c.ay * (y t ω - ys t ω) ^ 2 + c.ap * (pp t ω - pps t ω) ^ 2 +
    c.aw * (pw t ω - pws t ω) ^ 2) / 2

/-- Galí (2015), p. 181: the date-`t` Lagrangian cross term
`ζ_{1,t−1} dπ^p_t + ζ_{2,t−1} dπ^w_t + dω̃_{t−1} ζ_{3,t}`. -/
def cross (y0 : Ω → ℝ) (pp pw w pps pws ws z1 z2 z3 : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  prev 0 z1 t * (pp t - pps t) + prev 0 z2 t * (pw t - pws t) +
    (prev y0 w t - prev y0 ws t) * z3 t

/-- Galí (2015), p. 181: `E_t` of a nonnegative random variable is nonnegative. -/
theorem E_nonneg {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (t : ℕ) (ω : Ω) : 0 ≤ 𝔼.E t f ω := by
  have := 𝔼.mono t (show (0 : Ω → ℝ) ≤ f from hf) ω
  rwa [map_zero] at this

/-- Galí (2015), (28), p. 179: for a bounded plan the welfare loss is the genuine infinite sum
`∑ βᵗ E_0 ½ (a_y ỹ_t² + a_p (π^p_t)² + a_w (π^w_t)²)` (`E_0` commutes with the geometrically
dominated series). -/
theorem expLoss_hasSum {c : Coef} (hβ0 : 0 ≤ c.β) (hβ1 : c.β < 1) (hay : 0 ≤ c.ay)
    (hap : 0 ≤ c.ap) (haw : 0 ≤ c.aw) {y pp pw : ℕ → Ω → ℝ} (hy : BoundedProc y)
    (hpp : BoundedProc pp) (hpw : BoundedProc pw) (ω : Ω) :
    HasSum (fun t => c.β ^ t * 𝔼.E 0 (periodLoss c y pp pw t) ω) (expLoss 𝔼 c y pp pw ω) := by
  obtain ⟨A, hA⟩ := hy
  obtain ⟨B, hB⟩ := hpp
  obtain ⟨C, hC⟩ := hpw
  set K := (c.ay * A ^ 2 + c.ap * B ^ 2 + c.aw * C ^ 2) / 2 with hK
  have hpl : ∀ t ω, |periodLoss c y pp pw t ω| ≤ K := by
    intro t ω
    have h1 : y t ω ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hA t ω) 2
    have h2 : pp t ω ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB t ω) 2
    have h3 : pw t ω ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC t ω) 2
    unfold periodLoss
    rw [abs_of_nonneg (by positivity), hK]
    have := mul_le_mul_of_nonneg_left h1 hay
    have := mul_le_mul_of_nonneg_left h2 hap
    have := mul_le_mul_of_nonneg_left h3 haw
    linarith
  have hf : ∀ k ω, |c.β ^ k * periodLoss c y pp pw k ω| ≤ c.β ^ k * K := by
    intro k ω
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    exact mul_le_mul_of_nonneg_left (hpl k ω) (pow_nonneg hβ0 k)
  have hE : 𝔼.E 0 (fun ω' => ∑' k, c.β ^ k * periodLoss c y pp pw k ω') ω =
      ∑' k, 𝔼.E 0 (fun ω' => c.β ^ k * periodLoss c y pp pw k ω') ω := 𝔼.E_tsum hβ0 hβ1 hf 0 ω
  have heq : ∀ k, 𝔼.E 0 (fun ω' => c.β ^ k * periodLoss c y pp pw k ω') ω =
      c.β ^ k * 𝔼.E 0 (periodLoss c y pp pw k) ω := fun k => by
    have : (fun ω' => c.β ^ k * periodLoss c y pp pw k ω') = c.β ^ k • periodLoss c y pp pw k :=
      rfl
    rw [this, map_smul]; rfl
  have hs : Summable (fun t => c.β ^ t * 𝔼.E 0 (periodLoss c y pp pw t) ω) :=
    Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_right K) (fun k => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hpl k) 0 ω) (pow_nonneg hβ0 k))
  convert hs.hasSum using 1
  change 𝔼.E 0 (fun ω' => ∑' k, c.β ^ k * periodLoss c y pp pw k ω') ω = _
  rw [hE]
  exact tsum_congr heq

/-- **Galí (2015), (30)–(33), p. 181 (the Lagrangian identity, one period, state by state)**: for
a plan satisfying the first-order conditions and any other solution of the constraints,
`ℓ_t − ℓ*_t = ½ Q(d_t) + β (ζ_{1,t} E_t dπ^p_{t+1} + ζ_{2,t} E_t dπ^w_{t+1} +
dω̃_t E_t ζ_{3,t+1}) − (cross term at t)`. -/
theorem period_identity {c : Coef} {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → Ω → ℝ}
    (hc : Constr 𝔼 c dn w0 y pp pw w) (hcs : Constr 𝔼 c dn w0 ys pps pws ws)
    (hfoc : FOCs 𝔼 c ys pps pws z1 z2 z3) (t : ℕ) :
    periodLoss c y pp pw t - periodLoss c ys pps pws t =
      devLoss c y pp pw ys pps pws t +
        c.β • (z1 t * (𝔼.E t (pp (t + 1)) - 𝔼.E t (pps (t + 1))) +
          z2 t * (𝔼.E t (pw (t + 1)) - 𝔼.E t (pws (t + 1))) +
            (w t - ws t) * 𝔼.E t (z3 (t + 1))) -
        cross w0 pp pw w pps pws ws z1 z2 z3 t := by
  funext ω
  have c1 := congrFun (hc t).1 ω
  have c2 := congrFun (hc t).2.1 ω
  have c3 := congrFun (hc t).2.2 ω
  have c1s := congrFun (hcs t).1 ω
  have c2s := congrFun (hcs t).2.1 ω
  have c3s := congrFun (hcs t).2.2 ω
  have f1 := congrFun (hfoc t).1 ω
  have f2 := congrFun (hfoc t).2.1 ω
  have f3 := congrFun (hfoc t).2.2.1 ω
  have f4 := congrFun (hfoc t).2.2.2 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    at c1 c2 c3 c1s c2s c3s f1 f2 f3 f4
  simp only [periodLoss, devLoss, cross, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.mul_apply]
  exact lagrangian_alg c c1 c2 c3 c1s c2s c3s f1 f2 f3 f4

/-- **Galí (2015), p. 181 (the Lagrangian identity under `E_0`)**: with the law of iterated
expectations and the pull-out property, the expected excess period loss is
`E_0 ½ Q(d_t) + β E_0 (cross term at t + 1) − E_0 (cross term at t)`. -/
theorem E0_identity (hpo : 𝔼.PullOut) {c : Coef} {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → Ω → ℝ}
    (hc : Constr 𝔼 c dn w0 y pp pw w) (hcs : Constr 𝔼 c dn w0 ys pps pws ws)
    (hfoc : FOCs 𝔼 c ys pps pws z1 z2 z3) (hwa : 𝔼.Adapted w) (hwsa : 𝔼.Adapted ws)
    (hz1 : 𝔼.Adapted z1) (hz2 : 𝔼.Adapted z2) (t : ℕ) (ω : Ω) :
    𝔼.E 0 (periodLoss c y pp pw t) ω - 𝔼.E 0 (periodLoss c ys pps pws t) ω =
      𝔼.E 0 (devLoss c y pp pw ys pps pws t) ω +
        c.β * 𝔼.E 0 (cross w0 pp pw w pps pws ws z1 z2 z3 (t + 1)) ω -
          𝔼.E 0 (cross w0 pp pw w pps pws ws z1 z2 z3 t) ω := by
  have hdw : 𝔼.E t (w t - ws t) = w t - ws t := by rw [map_sub, hwa t, hwsa t]
  have hpull : z1 t * (𝔼.E t (pp (t + 1)) - 𝔼.E t (pps (t + 1))) +
      z2 t * (𝔼.E t (pw (t + 1)) - 𝔼.E t (pws (t + 1))) + (w t - ws t) * 𝔼.E t (z3 (t + 1)) =
      𝔼.E t (cross w0 pp pw w pps pws ws z1 z2 z3 (t + 1)) := by
    rw [← map_sub, ← map_sub, ← hpo t _ _ (hz1 t), ← hpo t _ _ (hz2 t), ← hpo t _ _ hdw,
      ← map_add, ← map_add]
    rfl
  have h := congrArg (fun f => 𝔼.E 0 f ω) (period_identity 𝔼 hc hcs hfoc t)
  simp only [map_sub, map_add, map_smul, hpull, 𝔼.tower (Nat.zero_le t), Pi.sub_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  exact h

/-- Galí (2015), p. 181: `E_0` of the deviation loss is nonnegative (nonnegative weights). -/
theorem E0_devLoss_nonneg {c : Coef} (hay : 0 ≤ c.ay) (hap : 0 ≤ c.ap) (haw : 0 ≤ c.aw)
    (y pp pw ys pps pws : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ 𝔼.E 0 (devLoss c y pp pw ys pps pws t) ω :=
  E_nonneg 𝔼 (fun ω => by unfold devLoss; positivity) 0 ω

/-- **Galí (2015), §6.4, p. 181 (sufficiency of the first-order conditions, stochastic)**: if a
plan satisfies (30)–(33) with bounded multipliers, `ζ₁, ζ₂` adapted, then for every other plan the
excess welfare loss is the genuine infinite sum
`𝕎 − 𝕎* = ∑ βᵗ E_0 ½ (a_y (ỹ_t − ỹ*_t)² + a_p (π^p_t − π^p*_t)² + a_w (π^w_t − π^w*_t)²)`. -/
theorem expLoss_sub_hasSum (hpo : 𝔼.PullOut) {c : Coef} (hβ0 : 0 ≤ c.β) (hβ1 : c.β < 1)
    (hay : 0 ≤ c.ay) (hap : 0 ≤ c.ap) (haw : 0 ≤ c.aw) {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → Ω → ℝ}
    (hp : Plan 𝔼 c dn w0 y pp pw w) (hps : Plan 𝔼 c dn w0 ys pps pws ws)
    (hfoc : FOCs 𝔼 c ys pps pws z1 z2 z3) (hz1 : 𝔼.Adapted z1) (hz2 : 𝔼.Adapted z2)
    (hb1 : BoundedProc z1) (hb2 : BoundedProc z2) (hb3 : BoundedProc z3) (ω : Ω) :
    HasSum (fun t => c.β ^ t * 𝔼.E 0 (devLoss c y pp pw ys pps pws t) ω)
      (expLoss 𝔼 c y pp pw ω - expLoss 𝔼 c ys pps pws ω) := by
  obtain ⟨hc, -, -, -, hwa, hyb, hppb, hpwb, ⟨Mw, hMw⟩⟩ := hp
  obtain ⟨hcs, -, -, -, hwsa, hysb, hppsb, hpwsb, ⟨Mws, hMws⟩⟩ := hps
  obtain ⟨Bp, hBp⟩ := hppb
  obtain ⟨Bq, hBq⟩ := hpwb
  obtain ⟨Bps, hBps⟩ := hppsb
  obtain ⟨Bqs, hBqs⟩ := hpwsb
  obtain ⟨Z1, hZ1⟩ := hb1
  obtain ⟨Z2, hZ2⟩ := hb2
  obtain ⟨Z3, hZ3⟩ := hb3
  have hZ10 : 0 ≤ Z1 := (abs_nonneg _).trans (hZ1 0 ω)
  have hZ20 : 0 ≤ Z2 := (abs_nonneg _).trans (hZ2 0 ω)
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ω)
  have hMws0 : 0 ≤ Mws := (abs_nonneg _).trans (hMws 0 ω)
  set K := Z1 * (Bp + Bps) + Z2 * (Bq + Bqs) + (Mw + Mws) * Z3 with hK
  have hH : ∀ t ω, |cross w0 pp pw w pps pws ws z1 z2 z3 t ω| ≤ K := by
    intro t ω
    have hz1 : |prev 0 z1 t ω| ≤ Z1 := by cases t <;> simp [hZ10, hZ1 _ ω]
    have hz2 : |prev 0 z2 t ω| ≤ Z2 := by cases t <;> simp [hZ20, hZ2 _ ω]
    have hdw : |prev w0 w t ω - prev w0 ws t ω| ≤ Mw + Mws := by
      cases t with
      | zero => simpa using add_nonneg hMw0 hMws0
      | succ t => exact (abs_sub _ _).trans (add_le_add (hMw t ω) (hMws t ω))
    have e1 : |prev 0 z1 t ω * (pp t ω - pps t ω)| ≤ Z1 * (Bp + Bps) := by
      rw [abs_mul]
      exact mul_le_mul hz1 ((abs_sub _ _).trans (add_le_add (hBp t ω) (hBps t ω)))
        (abs_nonneg _) hZ10
    have e2 : |prev 0 z2 t ω * (pw t ω - pws t ω)| ≤ Z2 * (Bq + Bqs) := by
      rw [abs_mul]
      exact mul_le_mul hz2 ((abs_sub _ _).trans (add_le_add (hBq t ω) (hBqs t ω)))
        (abs_nonneg _) hZ20
    have e3 : |(prev w0 w t ω - prev w0 ws t ω) * z3 t ω| ≤ (Mw + Mws) * Z3 := by
      rw [abs_mul]
      exact mul_le_mul hdw (hZ3 t ω) (abs_nonneg _) (by positivity)
    simp only [cross, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    exact (abs_add_three _ _ _).trans (by rw [hK]; linarith)
  refine hasSum_of_telescope
    ((expLoss_hasSum 𝔼 hβ0 hβ1 hay hap haw hyb ⟨Bp, hBp⟩ ⟨Bq, hBq⟩ ω).sub
      (expLoss_hasSum 𝔼 hβ0 hβ1 hay hap haw hysb ⟨Bps, hBps⟩ ⟨Bqs, hBqs⟩ ω))
    (fun t => mul_nonneg (pow_nonneg hβ0 t) (E0_devLoss_nonneg 𝔼 hay hap haw _ _ _ _ _ _ t ω))
    (h := fun t => c.β ^ t * 𝔼.E 0 (cross w0 pp pw w pps pws ws z1 z2 z3 t) ω)
    (fun t => ?_) ?_ ?_
  · rw [← mul_sub, E0_identity 𝔼 hpo hc hcs hfoc hwa hwsa hz1 hz2 t ω, pow_succ]
    ring
  · have : cross w0 pp pw w pps pws ws z1 z2 z3 0 = 0 := by
      funext ω; simp [cross]
    simp [this]
  · refine squeeze_zero_norm (a := fun t => c.β ^ t * K) (fun t => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hH t) 0 ω) (pow_nonneg hβ0 t)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const K

/-- **Galí (2015), §6.4, p. 181 (optimality, stochastic)**: a plan satisfying the first-order
conditions (30)–(33) with bounded multipliers (`ζ₁, ζ₂` adapted) has the smallest welfare loss
among all plans, state by state. -/
theorem expLoss_le_of_foc (hpo : 𝔼.PullOut) {c : Coef} (hβ0 : 0 ≤ c.β) (hβ1 : c.β < 1)
    (hay : 0 ≤ c.ay) (hap : 0 ≤ c.ap) (haw : 0 ≤ c.aw) {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → Ω → ℝ}
    (hp : Plan 𝔼 c dn w0 y pp pw w) (hps : Plan 𝔼 c dn w0 ys pps pws ws)
    (hfoc : FOCs 𝔼 c ys pps pws z1 z2 z3) (hz1 : 𝔼.Adapted z1) (hz2 : 𝔼.Adapted z2)
    (hb1 : BoundedProc z1) (hb2 : BoundedProc z2) (hb3 : BoundedProc z3) (ω : Ω) :
    expLoss 𝔼 c ys pps pws ω ≤ expLoss 𝔼 c y pp pw ω :=
  sub_nonneg.1 ((expLoss_sub_hasSum 𝔼 hpo hβ0 hβ1 hay hap haw hp hps hfoc hz1 hz2 hb1 hb2 hb3
    ω).nonneg (fun t => mul_nonneg (pow_nonneg hβ0 t)
      (E0_devLoss_nonneg 𝔼 hay hap haw _ _ _ _ _ _ t ω)))

/-- **Galí (2015), §6.4, p. 181 (uniqueness of the optimum, stochastic)**: a plan attaining at
`ω` the same welfare loss as a plan satisfying (30)–(33) with bounded multipliers coincides with
it in conditional mean square: `E_0 (ỹ_t − ỹ*_t)² = E_0 (π^p_t − π^p*_t)² =
E_0 (π^w_t − π^w*_t)² = 0` at `ω` for every `t` (under perfect foresight: equal paths). -/
theorem eq_of_expLoss_eq (hpo : 𝔼.PullOut) {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1)
    (hay : 0 < c.ay) (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w ys pps pws ws z1 z2 z3 : ℕ → Ω → ℝ}
    (hp : Plan 𝔼 c dn w0 y pp pw w) (hps : Plan 𝔼 c dn w0 ys pps pws ws)
    (hfoc : FOCs 𝔼 c ys pps pws z1 z2 z3) (hz1 : 𝔼.Adapted z1) (hz2 : 𝔼.Adapted z2)
    (hb1 : BoundedProc z1) (hb2 : BoundedProc z2) (hb3 : BoundedProc z3) (ω : Ω)
    (heq : expLoss 𝔼 c y pp pw ω = expLoss 𝔼 c ys pps pws ω) (t : ℕ) :
    𝔼.E 0 (fun ω => (y t ω - ys t ω) ^ 2) ω = 0 ∧
      𝔼.E 0 (fun ω => (pp t ω - pps t ω) ^ 2) ω = 0 ∧
        𝔼.E 0 (fun ω => (pw t ω - pws t ω) ^ 2) ω = 0 := by
  have hs := expLoss_sub_hasSum 𝔼 hpo hβ0.le hβ1 hay.le hap.le haw.le hp hps hfoc hz1 hz2 hb1
    hb2 hb3 ω
  rw [heq, sub_self] at hs
  have hz := (hasSum_zero_iff_of_nonneg (fun t => mul_nonneg (pow_nonneg hβ0.le t)
    (E0_devLoss_nonneg 𝔼 hay.le hap.le haw.le _ _ _ _ _ _ t ω))).1 hs
  have ht := congrFun hz t
  simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
    false_or] at ht
  have hsplit : devLoss c y pp pw ys pps pws t =
      (1 / 2 : ℝ) • (c.ay • (fun ω => (y t ω - ys t ω) ^ 2) +
        c.ap • (fun ω => (pp t ω - pps t ω) ^ 2) + c.aw • (fun ω => (pw t ω - pws t ω) ^ 2)) := by
    funext ω; simp only [devLoss, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  rw [hsplit, map_smul, map_add, map_add, map_smul, map_smul, map_smul] at ht
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht
  have h1 := E_nonneg 𝔼 (f := fun ω => (y t ω - ys t ω) ^ 2) (fun ω => by positivity) 0 ω
  have h2 := E_nonneg 𝔼 (f := fun ω => (pp t ω - pps t ω) ^ 2) (fun ω => by positivity) 0 ω
  have h3 := E_nonneg 𝔼 (f := fun ω => (pw t ω - pws t ω) ^ 2) (fun ω => by positivity) 0 ω
  have k1 := mul_nonneg hay.le h1
  have k2 := mul_nonneg hap.le h2
  have k3 := mul_nonneg haw.le h3
  refine ⟨?_, ?_, ?_⟩
  · have : c.ay * 𝔼.E 0 (fun ω => (y t ω - ys t ω) ^ 2) ω = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hay.ne'
  · have : c.ap * 𝔼.E 0 (fun ω => (pp t ω - pps t ω) ^ 2) ω = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hap.ne'
  · have : c.aw * 𝔼.E 0 (fun ω => (pw t ω - pws t ω) ^ 2) ω = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left haw.ne'

/-- **Galí (2015), §6.4, p. 181 (THE OPTIMAL POLICY UNDER COMMITMENT, stochastic)**: a plan
satisfying the first-order conditions (30)–(33) with `ζ_{1,−1} = ζ_{2,−1} = 0` and bounded
multipliers (`ζ₁, ζ₂` adapted) minimises the welfare loss (28) among all bounded adapted plans,
state by state; any plan with the same loss at `ω` coincides with it in conditional mean square.
Requires the pull-out property (true for perfect foresight and every finite event tree). -/
theorem commitment_optimal (hpo : 𝔼.PullOut) {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1)
    (hay : 0 < c.ay) (hap : 0 < c.ap) (haw : 0 < c.aw) {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {ys pps pws ws z1 z2 z3 : ℕ → Ω → ℝ} (hps : Plan 𝔼 c dn w0 ys pps pws ws)
    (hfoc : FOCs 𝔼 c ys pps pws z1 z2 z3) (hz1 : 𝔼.Adapted z1) (hz2 : 𝔼.Adapted z2)
    (hb1 : BoundedProc z1) (hb2 : BoundedProc z2) (hb3 : BoundedProc z3) :
    ∀ y pp pw w, Plan 𝔼 c dn w0 y pp pw w → ∀ ω,
      expLoss 𝔼 c ys pps pws ω ≤ expLoss 𝔼 c y pp pw ω ∧
        (expLoss 𝔼 c y pp pw ω = expLoss 𝔼 c ys pps pws ω → ∀ t,
          𝔼.E 0 (fun ω => (y t ω - ys t ω) ^ 2) ω = 0 ∧
            𝔼.E 0 (fun ω => (pp t ω - pps t ω) ^ 2) ω = 0 ∧
              𝔼.E 0 (fun ω => (pw t ω - pws t ω) ^ 2) ω = 0) :=
  fun _ _ _ _ hp ω => ⟨expLoss_le_of_foc 𝔼 hpo hβ0.le hβ1 hay.le hap.le haw.le hp hps hfoc hz1
    hz2 hb1 hb2 hb3 ω, fun heq t => eq_of_expLoss_eq 𝔼 hpo hβ0 hβ1 hay hap haw hp hps hfoc hz1
      hz2 hb1 hb2 hb3 ω heq t⟩

end Stoch

/-! ### The matrix form (Appendix 6.2) -/

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Appendix 6.2, p. 192: the matrix `A₀*`. -/
def A0 (c : Coef) : Matrix (Fin 7) (Fin 7) ℝ :=
  !![-c.kapP, 1, 0, 0, 0, 0, 0;
     -c.kapW, 0, 1, 0, 0, 0, 0;
     0, -1, 1, 1, 0, 0, 0;
     c.ay, 0, 0, 0, 0, 0, 0;
     0, c.ap, 0, 0, 1, 0, 1;
     0, 0, c.aw, 0, 0, 1, -1;
     0, 0, 0, 0, 0, 0, 1]

/-- Galí (2015), Appendix 6.2, p. 192: the matrix `A₁*`. -/
def A1 (c : Coef) : Matrix (Fin 7) (Fin 7) ℝ :=
  !![0, c.β, 0, c.lamP, 0, 0, 0;
     0, 0, c.β, -c.lamW, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, -c.kapP, -c.kapW, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, -c.lamP, c.lamW, c.β]

/-- Galí (2015), Appendix 6.2, p. 192: the vector `B₀* = (0, 0, ψ_wa, 0, 0, 0, 0)'`. -/
def B0 (ψ : ℝ) : Fin 7 → ℝ := ![0, 0, ψ, 0, 0, 0, 0]

/-- Galí (2015), p. 181: the state vector
`x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1}, ζ_{1,t−1}, ζ_{2,t−1}, ζ_{3,t})`. -/
def stateVec (w0 : Ω → ℝ) (y pp pw w z1 z2 z3 : ℕ → Ω → ℝ) (t : ℕ) : Fin 7 → Ω → ℝ :=
  ![y t, pp t, pw t, prev w0 w t, prev 0 z1 t, prev 0 z2 t, z3 t]

/-- Galí (2015), p. 181: the dynamical system `A₀* x_t = A₁* E_t x_{t+1} + B₀* Δa_t`. -/
def MatrixSystem (c : Coef) (ψ : ℝ) (da : ℕ → Ω → ℝ) (x : ℕ → Fin 7 → Ω → ℝ) : Prop :=
  ∀ t i, ∑ j, A0 c i j • x t j = ∑ j, A1 c i j • 𝔼.E t (x (t + 1) j) + B0 ψ i • da t

/-- **Galí (2015), p. 181 and Appendix 6.2, p. 192 (the matrix form)**: with `Δωⁿ_t = ψ_wa Δa_t`
and `ω̃, ζ₁, ζ₂` adapted, the constraints (18), (20), (21) together with the first-order conditions
(30)–(33) hold at every date iff the state vector `x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1},
ζ_{1,t−1}, ζ_{2,t−1}, ζ_{3,t})` (with `ζ_{1,−1} = ζ_{2,−1} = 0`) solves
`A₀* x_t = A₁* E_t x_{t+1} + B₀* Δa_t` with the matrices printed in Appendix 6.2 (all seven rows
check). -/
theorem matrix_form_iff (c : Coef) (ψ : ℝ) (da : ℕ → Ω → ℝ) (w0 : Ω → ℝ)
    {y pp pw w z1 z2 z3 : ℕ → Ω → ℝ}
    (hwa : 𝔼.Adapted w) (hz1 : 𝔼.Adapted z1) (hz2 : 𝔼.Adapted z2) :
    (Constr 𝔼 c (fun t => ψ • da t) w0 y pp pw w ∧ FOCs 𝔼 c y pp pw z1 z2 z3) ↔
      MatrixSystem 𝔼 c ψ da (stateVec w0 y pp pw w z1 z2 z3) := by
  simp only [MatrixSystem, stateVec, Constr, FOCs, ← forall_and]
  refine forall_congr' fun t => ?_
  simp only [funext_iff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply,
    A0, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Fin.sum_univ_seven,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, A1, prev_succ,
    hwa t, hz1 t, hz2 t, B0, Fin.forall_fin_succ, neg_mul, one_mul, zero_mul, add_zero, zero_add,
    Matrix.cons_val_succ, forall_const]
  constructor
  · rintro ⟨⟨e1, e2, e3⟩, f1, f2, f3, f4⟩
    exact ⟨fun x => by linarith [e1 x], fun x => by linarith [e2 x], fun x => by linarith [e3 x],
      fun x => by linarith [f1 x], fun x => by linarith [f2 x], fun x => by linarith [f3 x],
      fun x => by linarith [f4 x]⟩
  · rintro ⟨r1, r2, r3, r4, r5, r6, r7⟩
    exact ⟨⟨fun x => by linarith [r1 x], fun x => by linarith [r2 x], fun x => by linarith [r3 x]⟩,
      fun x => by linarith [r4 x], fun x => by linarith [r5 x], fun x => by linarith [r6 x],
      fun x => by linarith [r7 x]⟩

end Stoch

/-! ### §6.4.1: demand shocks -/

namespace Det

/-- **Galí (2015), §6.4.1, p. 181 (demand shocks, deterministic)**: with demand shocks only the
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

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), (28), p. 179: the welfare loss is nonnegative (nonnegative weights). -/
theorem expLoss_nonneg {c : Coef} (hβ0 : 0 ≤ c.β) (hay : 0 ≤ c.ay) (hap : 0 ≤ c.ap)
    (haw : 0 ≤ c.aw) (y pp pw : ℕ → Ω → ℝ) (ω : Ω) : 0 ≤ expLoss 𝔼 c y pp pw ω :=
  E_nonneg 𝔼 (fun ω => tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ0 t)
    (by unfold periodLoss; positivity)) 0 ω

/-- Galí (2015), §6.4.1, p. 181: the zero allocation has zero welfare loss. -/
theorem expLoss_zero (c : Coef) : expLoss 𝔼 c 0 0 0 = 0 := by
  have : (fun ω => ∑' t, c.β ^ t * periodLoss c (0 : ℕ → Ω → ℝ) 0 0 t ω) = 0 := by
    funext ω; simp [periodLoss]
  rw [expLoss, this, map_zero]

/-- Galí (2015), §6.4.1, p. 181: with `Δωⁿ ≡ 0` and `ω̃_{−1} = 0` the zero allocation is a plan. -/
theorem zero_plan (c : Coef) : Plan 𝔼 c 0 0 0 0 0 0 := by
  refine ⟨fun t => ?_, fun t => map_zero _, fun t => map_zero _, fun t => map_zero _,
    fun t => map_zero _, ⟨0, fun t ω => by simp⟩, ⟨0, fun t ω => by simp⟩, ⟨0, fun t ω => by simp⟩,
    ⟨0, fun t ω => by simp⟩⟩
  cases t <;> simp

/-- **Galí (2015), §6.4.1, p. 181 (demand shocks, stochastic)**: when demand shocks are the only
source of fluctuations (`Δωⁿ ≡ 0`) and `ω̃_{−1} = 0`, the zero allocation is optimal: it is a plan
with zero loss and every plan has a nonnegative loss; it satisfies (30)–(33) with zero multipliers,
and any plan with the same loss at `ω` has `E_0 ỹ_t² = E_0 (π^p_t)² = E_0 (π^w_t)² = 0` there. -/
theorem demand_zero_optimal (hpo : 𝔼.PullOut) {c : Coef} (hβ0 : 0 < c.β) (hβ1 : c.β < 1)
    (hay : 0 < c.ay) (hap : 0 < c.ap) (haw : 0 < c.aw) :
    Plan 𝔼 c 0 0 0 0 0 0 ∧ FOCs 𝔼 c 0 0 0 0 0 0 ∧ expLoss 𝔼 c 0 0 0 = 0 ∧
      ∀ y pp pw w, Plan 𝔼 c 0 0 y pp pw w → ∀ ω, 0 ≤ expLoss 𝔼 c y pp pw ω ∧
        (expLoss 𝔼 c y pp pw ω = 0 → ∀ t, 𝔼.E 0 (fun ω => y t ω ^ 2) ω = 0 ∧
          𝔼.E 0 (fun ω => pp t ω ^ 2) ω = 0 ∧ 𝔼.E 0 (fun ω => pw t ω ^ 2) ω = 0) := by
  have hfoc : FOCs 𝔼 c 0 0 0 0 0 0 := fun t => by cases t <;> simp
  have hb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun t ω => by simp⟩
  have ha : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => map_zero _
  refine ⟨zero_plan 𝔼 c, hfoc, expLoss_zero 𝔼 c, fun y pp pw w hp ω =>
    ⟨expLoss_nonneg 𝔼 hβ0.le hay.le hap.le haw.le y pp pw ω, fun h0 t => ?_⟩⟩
  have h := (commitment_optimal 𝔼 hpo hβ0 hβ1 hay hap haw (zero_plan 𝔼 c) hfoc ha ha hb hb hb
    y pp pw w hp ω).2 (by rw [h0, expLoss_zero]; rfl) t
  simpa using h

/-! ### §6.4.1: implementation by an interest-rate rule -/

/-- Galí (2015), (22), p. 173: the dynamic IS equation in gaps,
`ỹ_t = −(1/σ)(i_t − E_t π^p_{t+1} − rⁿ_t) + E_t ỹ_{t+1}`. -/
def DIS (σ : ℝ) (rn i y pp : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = -(1 / σ) • (i t - 𝔼.E t (pp (t + 1)) - rn t) + 𝔼.E t (y (t + 1))

/-- Galí (2015), §6.4.1, p. 182: an equilibrium under the rule `i_t = rⁿ_t + φ_p π^p_t` with demand
shocks only (`Δωⁿ ≡ 0`) and `ω̃_{−1} = 0`: the DIS (22), the rule, and a plan (bounded adapted
solution of (18), (20), (21)). -/
def RuleEqm (c : Coef) (σ φp : ℝ) (rn y pp pw w i : ℕ → Ω → ℝ) : Prop :=
  DIS 𝔼 σ rn i y pp ∧ (∀ t, i t = rn t + φp • pp t) ∧ Plan 𝔼 c 0 0 y pp pw w

/-- Galí (2015), §6.4.1, p. 182 (and p. 174 with `φ_w = φ_y = 0`): the rule is determinate: the
only bounded adapted solution of `σ ỹ_t = σ E_t ỹ_{t+1} − φ_p π^p_t + E_t π^p_{t+1}`, (18), (20),
(21) with `Δωⁿ ≡ 0` and `ω̃_{−1} = 0` is zero. -/
def RuleDeterminate (c : Coef) (σ φp : ℝ) : Prop :=
  ∀ y pp pw w : ℕ → Ω → ℝ,
    (∀ t, σ • y t = σ • 𝔼.E t (y (t + 1)) - φp • pp t + 𝔼.E t (pp (t + 1))) →
      Plan 𝔼 c 0 0 y pp pw w → y = 0 ∧ pp = 0 ∧ pw = 0 ∧ w = 0

/-- **Galí (2015), §6.4.1, p. 182 (implementation)**: under demand shocks the rule
`i_t = rⁿ_t + φ_p π^p_t` supports the optimal (zero) allocation with `i_t = rⁿ_t`; if the rule is
determinate, this is the only equilibrium. (Determinacy holds for `φ_p > 1` when `κ_p = κ_w`,
`ruleDeterminate_of_kap_eq`, and for general parameters with `φ_p > 1` by
`ruleDeterminate_of_phiP` / `ruleDeterminate_book`; the unconditional statement is
`rule_implements_book`.) -/
theorem rule_implements {c : Coef} {σ φp : ℝ} (hσ : 0 < σ) (rn : ℕ → Ω → ℝ) :
    RuleEqm 𝔼 c σ φp rn 0 0 0 0 rn ∧
      (RuleDeterminate 𝔼 c σ φp → ∀ y pp pw w i, RuleEqm 𝔼 c σ φp rn y pp pw w i →
        y = 0 ∧ pp = 0 ∧ pw = 0 ∧ w = 0 ∧ i = rn) := by
  refine ⟨⟨fun t => ?_, fun t => by simp, zero_plan 𝔼 c⟩, fun hdet y pp pw w i h => ?_⟩
  · simp
  obtain ⟨hdis, hrule, hp⟩ := h
  have hs : ∀ t, σ • y t = σ • 𝔼.E t (y (t + 1)) - φp • pp t + 𝔼.E t (pp (t + 1)) := by
    intro t
    funext ω
    have h1 := congrFun (hdis t) ω
    have h2 := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h2] at h1
    field_simp at h1
    linarith
  obtain ⟨h1, h2, h3, h4⟩ := hdet y pp pw w hs hp
  refine ⟨h1, h2, h3, h4, funext fun t => ?_⟩
  rw [hrule t, h2]
  simp

end Stoch

/-! ### The relative-inflation block and determinacy when `κ_p = κ_w` -/

/-- Galí (2015), Note N6.1 (survey): the characteristic polynomial
`β r² − (1 + β + k) r + 1` of the relative-inflation block has a root in `(0, 1)` for `k > 0`
(it is `1` at `r = 0` and `−k` at `r = 1`). -/
theorem exists_block_root {β k : ℝ} (hk : 0 < k) :
    ∃ r, 0 < r ∧ r < 1 ∧ β * r ^ 2 - (1 + β + k) * r + 1 = 0 := by
  have hcont : Continuous (fun r : ℝ => β * r ^ 2 - (1 + β + k) * r + 1) := by fun_prop
  have h := intermediate_value_Ioo' (zero_le_one' ℝ) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (β * 1 ^ 2 - (1 + β + k) * 1 + 1) (β * 0 ^ 2 - (1 + β + k) * 0 + 1) by
      constructor <;> nlinarith)
  obtain ⟨r, ⟨h0, h1⟩, hr⟩ := h
  exact ⟨r, h0, h1, hr⟩

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- **Galí (2015), Note N6.1 (survey) (the relative-inflation block is determinate)**: with
`0 < β < 1` and `k > 0`, the only bounded adapted solution of `D_t = β E_t D_{t+1} − k ω̃_t`,
`ω̃_t = ω̃_{t−1} + D_t`, `ω̃_{−1} = 0` is zero. Proof: for the root `r ∈ (0, 1)` of
`β r² − (1 + β + k) r + 1`, `v_t = ω̃_t − r ω̃_{t−1}` solves `v_t = β r E_t v_{t+1}`, so `v = 0`,
and then `ω̃_t = r ω̃_{t−1}` with `ω̃_{−1} = 0`. -/
theorem block_zero {β k : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hk : 0 < k) {D w : ℕ → Ω → ℝ}
    (hwa : 𝔼.Adapted w) (hwb : BoundedProc w)
    (h1 : ∀ t, D t = β • 𝔼.E t (D (t + 1)) - k • w t) (h2 : ∀ t, w t = prev 0 w t + D t) :
    D = 0 ∧ w = 0 := by
  obtain ⟨r, hr0, hr1, hr⟩ := exists_block_root (β := β) hk
  set v : ℕ → Ω → ℝ := fun t => w t - r • prev 0 w t with hv_def
  have hv : ∀ t, v t = (β * r) • 𝔼.E t (v (t + 1)) + (0 : ℕ → Ω → ℝ) t := by
    intro t
    have hED : 𝔼.E t (D (t + 1)) = 𝔼.E t (w (t + 1)) - w t := by
      have := congrArg (𝔼.E t) (h2 (t + 1))
      rw [map_add, prev_succ, hwa t] at this
      rw [this]; abel
    have hEv : 𝔼.E t (v (t + 1)) = 𝔼.E t (w (t + 1)) - r • w t := by
      simp only [hv_def, prev_succ, map_sub, map_smul, hwa t]
    funext ω
    have a := congrFun (h1 t) ω
    have b := congrFun (h2 t) ω
    have c := congrFun hED ω
    have d := congrFun hEv ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c d
    simp only [hv_def, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      add_zero]
    rw [d]
    rw [c] at a
    linear_combination r * a + r * b + (w t ω) * hr
  obtain ⟨Mw, hMw⟩ := hwb
  have hvb : BoundedProc v := ⟨Mw + |r| * Mw, fun t ω => by
    have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ω)
    have hp : |prev 0 w t ω| ≤ Mw := by cases t <;> simp [hMw0, hMw _ ω]
    simp only [hv_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hMw t ω) ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hp (abs_nonneg r)⟩
  have hβr : |β * r| < 1 := by
    rw [abs_of_pos (mul_pos hβ0 hr0)]; nlinarith
  have hzero : ∀ t, (0 : ℕ → Ω → ℝ) t = (β * r) • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) +
      (0 : ℕ → Ω → ℝ) t := fun t => by simp
  have hv0 := 𝔼.forward_unique hβr hv hzero hvb ⟨0, fun t ω => by simp⟩
  have hw : ∀ t, w t = 0 := by
    intro t
    induction t with
    | zero =>
      have := congrFun hv0 0
      simpa [hv_def] using this
    | succ t ih =>
      have := congrFun hv0 (t + 1)
      simp only [hv_def, prev_succ, ih, smul_zero, sub_zero, Pi.zero_apply] at this
      exact this
  refine ⟨funext fun t => ?_, funext hw⟩
  have := h2 t
  rw [hw t] at this
  cases t with
  | zero => simpa using this.symm
  | succ t => simpa [hw t] using this.symm

end Stoch

/-- Galí (2015), §6.4.1, p. 182 (with `κ_p = κ_w = κ`, once `ω̃ ≡ 0` and `π^w = π^p`): the
coefficient matrix of `(ỹ_t, π^p_t) = A E_t (ỹ_{t+1}, π^p_{t+1})` under the rule
`i_t = rⁿ_t + φ_p π^p_t`, `A = (σ + κφ_p)⁻¹ [[σ, 1 − βφ_p], [κσ, κ + βσ]]` (as in Chapter 3). -/
noncomputable def ruleA (σ κ β φp : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ / (σ + κ * φp), (1 - β * φp) / (σ + κ * φp);
     κ * σ / (σ + κ * φp), (κ + β * σ) / (σ + κ * φp)]

/-- Galí (2015), p. 182 (as in Chapter 3): `det A = βσ/(σ + κφ_p)`. -/
theorem det2_ruleA {σ κ β φp : ℝ} (hΩ : 0 < σ + κ * φp) :
    det2 (ruleA σ κ β φp) = β * σ / (σ + κ * φp) := by
  simp only [det2, ruleA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue]
  field_simp
  ring

/-- Galí (2015), p. 182 (as in Chapter 3): `tr A = (σ + κ + βσ)/(σ + κφ_p)`. -/
theorem tr2_ruleA (σ κ β φp : ℝ) :
    tr2 (ruleA σ κ β φp) = (σ + κ + β * σ) / (σ + κ * φp) := by
  simp only [tr2, ruleA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue]
  ring

/-- **Galí (2015), p. 182 (the Taylor principle for the composite system)**: for `σ, κ > 0`,
`0 < β < 1`, `φ_p ≥ 0`, both eigenvalues of `A` lie inside the unit circle iff `φ_p > 1`. -/
theorem schur_ruleA_iff {σ κ β φp : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 0 ≤ φp) : SchurStable (tr2 (ruleA σ κ β φp)) (det2 (ruleA σ κ β φp)) ↔ 1 < φp := by
  have hΩ : 0 < σ + κ * φp := by positivity
  rw [tr2_ruleA, det2_ruleA hΩ, SchurStable]
  have hd : 0 < β * σ / (σ + κ * φp) := by positivity
  have hd1 : β * σ / (σ + κ * φp) < 1 := by
    rw [div_lt_one hΩ]; nlinarith [mul_nonneg hκ.le hφ]
  have ht : 0 < (σ + κ + β * σ) / (σ + κ * φp) := by positivity
  rw [abs_of_pos hd, abs_of_pos ht, one_add_div hΩ.ne', div_lt_div_iff_of_pos_right hΩ]
  constructor
  · rintro ⟨-, h⟩
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    exact ⟨hd1, by nlinarith⟩

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 182: the stacked vector `(ỹ_t, π^p_t)`. -/
def stack (a b : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![a t, b t]

/-- Galí (2015), p. 182: with `κ_p = κ_w = κ`, `ω̃ ≡ 0`, `π^w = π^p`, the DIS under the rule and
(18) are equivalent to `(ỹ_t, π^p_t) = A E_t (ỹ_{t+1}, π^p_{t+1})`. -/
theorem solves_ruleA_iff {σ κ β φp : ℝ} (hΩ : 0 < σ + κ * φp) (y pp : ℕ → Ω → ℝ) :
    ((∀ t, σ • y t = σ • 𝔼.E t (y (t + 1)) - φp • pp t + 𝔼.E t (pp (t + 1))) ∧
      ∀ t, pp t = β • 𝔼.E t (pp (t + 1)) + κ • y t) ↔
      𝔼.Solves (ruleA σ κ β φp) 0 (stack y pp) := by
  have hΩ' := hΩ.ne'
  constructor
  · rintro ⟨h1, h2⟩ t i
    funext ω
    have e1 := congrFun (h1 t) ω
    have e2 := congrFun (h2 t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    fin_cases i
    · simp only [stack, ruleA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
      field_simp
      linear_combination e1 - φp * e2
    · simp only [stack, ruleA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
      field_simp
      linear_combination (σ + κ * φp) * e2 + κ * (e1 - φp * e2)
  · intro h
    have r : ∀ t ω, (σ + κ * φp) * y t ω =
          σ * 𝔼.E t (y (t + 1)) ω + (1 - β * φp) * 𝔼.E t (pp (t + 1)) ω ∧
        (σ + κ * φp) * pp t ω =
          κ * σ * 𝔼.E t (y (t + 1)) ω + (κ + β * σ) * 𝔼.E t (pp (t + 1)) ω := by
      intro t ω
      have r0 := congrFun (h t 0) ω
      have r1 := congrFun (h t 1) ω
      simp only [stack, ruleA, Fin.isValue, Matrix.cons_val_zero, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at r0 r1
      rw [r0, r1]
      constructor <;> field_simp
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · obtain ⟨r0, r1⟩ := r t ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine mul_left_cancel₀ hΩ' ?_
      linear_combination σ * r0 + φp * r1
    · obtain ⟨r0, r1⟩ := r t ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine mul_left_cancel₀ hΩ' ?_
      linear_combination r1 - κ * r0

/-- **Galí (2015), §6.4.1, p. 182 (determinacy of the implementing rule when `κ_p = κ_w`)**: with
`κ_p = κ_w = κ > 0`, `λ_p + λ_w > 0`, `σ > 0`, `0 < β < 1` and `φ_p > 1`, the rule
`i_t = rⁿ_t + φ_p π^p_t` is determinate. The system factors: `D = π^w − π^p` and `ω̃` form the
block `D_t = β E_t D_{t+1} − (λ_p + λ_w) ω̃_t`, `ω̃_t = ω̃_{t−1} + D_t` (`block_zero`), and then
`(ỹ, π^p)` solves the Chapter 3 system with the Taylor principle. -/
theorem ruleDeterminate_of_kap_eq {c : Coef} {σ φp : ℝ} (hk : c.kapP = c.kapW)
    (hκ : 0 < c.kapP) (hl : 0 < c.lamP + c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hσ : 0 < σ)
    (hφ : 1 < φp) : RuleDeterminate 𝔼 c σ φp := by
  intro y pp pw w hs hp
  obtain ⟨hc, hya, hppa, -, hwa, ⟨My, hMy⟩, ⟨Mp, hMp⟩, -, hwb⟩ := hp
  set D : ℕ → Ω → ℝ := fun t => pw t - pp t with hD_def
  have h1 : ∀ t, D t = c.β • 𝔼.E t (D (t + 1)) - (c.lamP + c.lamW) • w t := by
    intro t
    funext ω
    have e1 := congrFun (hc t).1 ω
    have e2 := congrFun (hc t).2.1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    simp only [hD_def, map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hk] at e1
    linarith
  have h2 : ∀ t, w t = prev 0 w t + D t := by
    intro t
    funext ω
    have e3 := congrFun (hc t).2.2 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, sub_zero] at e3
    simp only [hD_def, Pi.add_apply, Pi.sub_apply]
    linarith
  obtain ⟨hD, hw⟩ := block_zero 𝔼 hβ0 hβ1 hl hwa hwb h1 h2
  have hpw : pw = pp := funext fun t => funext fun ω => by
    have := congrFun (congrFun hD t) ω
    simp only [hD_def, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
    exact this
  have h18 : ∀ t, pp t = c.β • 𝔼.E t (pp (t + 1)) + c.kapP • y t := by
    intro t
    have := (hc t).1
    rw [hw] at this
    simpa using this
  have hΩ : 0 < σ + c.kapP * φp := by positivity
  have hsol := (solves_ruleA_iff 𝔼 hΩ y pp).1 ⟨hs, h18⟩
  have hA := (schur_ruleA_iff hσ hκ hβ0 hβ1 (by linarith)).2 hφ
  have hzero : 𝔼.Solves (ruleA σ c.kapP c.β φp) 0 0 := fun t i => by simp
  have heq := 𝔼.system_unique hA hsol hzero
    (fun t i => by fin_cases i <;> simp [stack, hya t, hppa t]) (fun t i => by simp)
    ⟨My + Mp, fun t i ω => by
      have := abs_nonneg (y t ω)
      have := abs_nonneg (pp t ω)
      fin_cases i
      · simp only [stack, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        linarith [hMy t ω, hMp t ω]
      · simp only [stack, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        linarith [hMy t ω, hMp t ω]⟩ ⟨0, fun t i ω => by simp⟩
  have hy : y = 0 := funext fun t => by simpa [stack] using congrFun (congrFun heq t) 0
  have hpp : pp = 0 := funext fun t => by simpa [stack] using congrFun (congrFun heq t) 1
  exact ⟨hy, hpp, hpw.trans hpp, hw⟩

/-- **Galí (2015), §6.4.1, p. 182 (indeterminacy for `φ_p ≤ 1` when `κ_p = κ_w`)**: with
`0 ≤ φ_p ≤ 1` the rule admits a nonzero bounded adapted equilibrium (with `ω̃ ≡ 0`,
`π^w = π^p`), built from a self-fulfilling solution of the Chapter 3 system. -/
theorem not_ruleDeterminate [Nonempty Ω] {c : Coef} {σ φp : ℝ} (hk : c.kapP = c.kapW)
    (hκ : 0 < c.kapP) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hσ : 0 < σ) (hφ0 : 0 ≤ φp)
    (hφ1 : φp ≤ 1) : ¬ RuleDeterminate 𝔼 c σ φp := by
  intro hdet
  have hΩ : 0 < σ + c.kapP * φp := by positivity
  have hA : ¬ SchurStable (tr2 (ruleA σ c.kapP c.β φp)) (det2 (ruleA σ c.kapP c.β φp)) :=
    fun h => by linarith [(schur_ruleA_iff hσ hκ hβ0 hβ1 hφ0).1 h]
  obtain ⟨Y, hY, hYa, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hA (w := 0) (x := 0)
    (fun t i => by simp) (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
  set y : ℕ → Ω → ℝ := fun t => Y t 0 with hy_def
  set pp : ℕ → Ω → ℝ := fun t => Y t 1 with hpp_def
  have hst : stack y pp = Y := by
    funext t i
    fin_cases i <;> rfl
  rw [← hst] at hY
  obtain ⟨h1, h2⟩ := (solves_ruleA_iff 𝔼 hΩ y pp).2 hY
  have hplan : Plan 𝔼 c 0 0 y pp pp 0 := by
    refine ⟨fun t => ⟨?_, ?_, ?_⟩, fun t => hYa t 0, fun t => hYa t 1, fun t => hYa t 1,
      fun t => map_zero _, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩,
      ⟨M, fun t ω => hM t 1 ω⟩, ⟨0, fun t ω => by simp⟩⟩
    · simpa using h2 t
    · rw [← hk]; simpa using h2 t
    · cases t <;> simp
  obtain ⟨hy0, hpp0, -, -⟩ := hdet y pp pp 0 h1 hplan
  apply hne
  funext t i
  fin_cases i
  · exact congrFun hy0 t
  · exact congrFun hpp0 t

/-- **Galí (2015), §6.4.1, p. 182 (the implementing rule, `κ_p = κ_w`)**: the rule
`i_t = rⁿ_t + φ_p π^p_t` (`φ_p ≥ 0`) is determinate iff `φ_p > 1`. -/
theorem ruleDeterminate_iff [Nonempty Ω] {c : Coef} {σ φp : ℝ} (hk : c.kapP = c.kapW)
    (hκ : 0 < c.kapP) (hl : 0 < c.lamP + c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hσ : 0 < σ)
    (hφ0 : 0 ≤ φp) : RuleDeterminate 𝔼 c σ φp ↔ 1 < φp := by
  constructor
  · intro h
    by_contra hc
    exact not_ruleDeterminate 𝔼 hk hκ hβ0 hβ1 hσ hφ0 (not_lt.1 hc) h
  · exact ruleDeterminate_of_kap_eq 𝔼 hk hκ hl hβ0 hβ1 hσ

end Stoch

/-! ### The implementing rule for general parameters (via `Determinacy4`) -/

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), (24), p. 173, with `φ_w = φ_y = 0`: the parameters of system (24) under the rule
`i_t = rⁿ_t + φ_p π^p_t`, read off the policy-problem coefficients. -/
def rulePar (c : Coef) (σ φp : ℝ) : Determinacy4.Par :=
  ⟨c.β, σ, c.kapP, c.kapW, c.lamP, c.lamW, φp, 0, 0⟩

/-- Galí (2015), §6.4.1, p. 182: the rule system as system (24): a bounded adapted solution of
`σ ỹ_t = σ E_t ỹ_{t+1} − φ_p π^p_t + E_t π^p_{t+1}` (the DIS (22) after the `rⁿ` cancellation),
(18), (20), (21) with `Δωⁿ ≡ 0`, `ω̃_{−1} = 0` gives the solution
`x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1})` of (24) with zero forcing and zero initial condition. -/
theorem rule_isSol {c : Coef} {σ φp : ℝ} {y pp pw w : ℕ → Ω → ℝ}
    (hs : ∀ t, σ • y t = σ • 𝔼.E t (y (t + 1)) - φp • pp t + 𝔼.E t (pp (t + 1)))
    (hp : Plan 𝔼 c 0 0 y pp pw w) :
    Determinacy4.Dyn.IsSol 𝔼 (rulePar c σ φp) 0 0 (fun t => ![y t, pp t, pw t, prev 0 w t]) ∧
      Determinacy4.Fwd.VBounded (fun t => ![y t, pp t, pw t, prev 0 w t]) := by
  obtain ⟨hc, hya, hppa, hpwa, hwa, ⟨My, hMy⟩, ⟨Mp, hMp⟩, ⟨Mq, hMq⟩, ⟨Mw, hMw⟩⟩ := hp
  have hpa : ∀ t, 𝔼.E t (prev 0 w t) = prev 0 w t := by
    intro t
    cases t with
    | zero => exact map_zero _
    | succ t => simp only [prev_succ]; rw [← hwa t, 𝔼.known (Nat.le_succ t)]
  refine ⟨⟨fun t => ?_, rfl, fun t i => ?_, fun t => ?_⟩, ⟨My + Mp + Mq + Mw, fun t i ω => ?_⟩⟩
  · refine (Determinacy4.Dyn.eq24_iff 𝔼 (rulePar c σ φp)
      (fun t => ![y t, pp t, pw t, prev 0 w t]) 0 t).2 fun ω => ?_
    have e0 := congrFun (hs t) ω
    have e1 := congrFun (hc t).1 ω
    have e2 := congrFun (hc t).2.1 ω
    have e3 := congrFun (hc t).2.2 ω
    have hw := congrFun (hwa t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      at e0 e1 e2 e3
    simp only [rulePar, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.isValue, prev_succ, hw, Pi.zero_apply]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · fin_cases i
    · exact hya t
    · exact hppa t
    · exact hpwa t
    · exact hpa t
  · simp only [Matrix.cons_val, Fin.isValue, prev_succ]
    exact hwa t
  · have h0 := (abs_nonneg (y t ω)).trans (hMy t ω)
    have h1 := (abs_nonneg (pp t ω)).trans (hMp t ω)
    have h2 := (abs_nonneg (pw t ω)).trans (hMq t ω)
    have h3 := (abs_nonneg (w t ω)).trans (hMw t ω)
    have hpw : |prev 0 w t ω| ≤ Mw := by cases t <;> simp [h3, hMw _ ω]
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val]; linarith [hMy t ω]
    · simp only [Fin.mk_one, Matrix.cons_val]; linarith [hMp t ω]
    · simp only [Fin.reduceFinMk, Matrix.cons_val]; linarith [hMq t ω]
    · simp only [Fin.reduceFinMk, Matrix.cons_val]; linarith

/-- **Galí (2015), §6.4.1, p. 182 (determinacy of the implementing rule, general parameters)**:
with `0 < β < 1`, `σ > 0`, `κ_p, κ_w ≥ 0`, `λ_p, λ_w > 0`, `λ_w κ_p + λ_p κ_w > 0` and
`φ_p > 1`, the rule `i_t = rⁿ_t + φ_p π^p_t` is determinate. This is the `φ_w = φ_y = 0` case of
the p. 174 determinacy theorem (`Determinacy4.Dyn.determinate_of_pos`, whose condition reads
`φ_p > 1` here): the rule system is system (24) with zero forcing (`rule_isSol`), and zero is
its unique bounded solution. -/
theorem ruleDeterminate_of_phiP {c : Coef} {σ φp : ℝ} (hβ0 : 0 < c.β) (hβ1 : c.β < 1)
    (hσ : 0 < σ) (hkp : 0 ≤ c.kapP) (hkw : 0 ≤ c.kapW) (hlp : 0 < c.lamP) (hlw : 0 < c.lamW)
    (hΨ : 0 < c.lamW * c.kapP + c.lamP * c.kapW) (hφ : 1 < φp) : RuleDeterminate 𝔼 c σ φp := by
  intro y pp pw w hs hp
  have hP : (rulePar c σ φp).Adm :=
    ⟨hβ0, hβ1, hσ, hkp, hkw, hlp, hlw, show (0 : ℝ) ≤ φp by linarith, le_rfl, le_rfl⟩
  have hΨ' : 0 < (rulePar c σ φp).Ψ := hΨ
  have h1 : 0 < (rulePar c σ φp).qr 1 := by
    rw [Determinacy4.Par.qr_one_pos_iff hΨ']
    simpa [Determinacy4.Par.Lhs, rulePar] using hφ
  have hdet := Determinacy4.Dyn.determinate_of_pos 𝔼 hP hΨ' h1
  obtain ⟨x, -, huniq⟩ := hdet 0 0 ⟨0, fun t i ω => by simp⟩ (fun t i => by simp)
    ⟨0, fun ω => by simp⟩ (map_zero _)
  obtain ⟨hsol, hbd⟩ := rule_isSol 𝔼 hs hp
  have hz : Determinacy4.Dyn.IsSol 𝔼 (rulePar c σ φp) 0 0 (fun _ => ![0, 0, 0, 0]) ∧
      Determinacy4.Fwd.VBounded (fun (_ : ℕ) => (![0, 0, 0, 0] : Fin 4 → Ω → ℝ)) := by
    have := rule_isSol 𝔼 (y := 0) (pp := 0) (pw := 0) (w := 0) (c := c) (σ := σ) (φp := φp)
      (fun t => by simp) (zero_plan 𝔼 c)
    have hpz : ∀ t, prev (0 : Ω → ℝ) (0 : ℕ → Ω → ℝ) t = 0 := fun t => by cases t <;> rfl
    simpa [hpz] using this
  have heq := (huniq _ ⟨hsol, hbd⟩).trans (huniq _ hz).symm
  have hcomp : ∀ t (i : Fin 4), ![y t, pp t, pw t, prev 0 w t] i = (0 : Ω → ℝ) := fun t i => by
    have := congrFun (congrFun heq t) i
    fin_cases i <;> simpa using this
  refine ⟨funext fun t => hcomp t 0, funext fun t => hcomp t 1, funext fun t => hcomp t 2,
    funext fun t => ?_⟩
  simpa using hcomp (t + 1) 3

/-- **Galí (2015), §6.4.1, p. 182 (determinacy for the book's coefficients)**: with `0 < β < 1`,
`σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`, `λ_p, λ_w > 0`, the rule `i_t = rⁿ_t + φ_p π^p_t` with `φ_p > 1`
is determinate for any `ε_p, ε_w` (the loss weights do not enter). -/
theorem ruleDeterminate_book {β σ φ α εp εw lamP lamW φp : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW)
    (hφp : 1 < φp) : RuleDeterminate 𝔼 (bookCoef β σ φ α εp εw lamP lamW) σ φp := by
  have h1α : 0 < 1 - α := by linarith
  have hkp : 0 ≤ (bookCoef β σ φ α εp εw lamP lamW).kapP := by
    simp only [bookCoef]; positivity
  have hkw : 0 < (bookCoef β σ φ α εp εw lamP lamW).kapW := by
    simp only [bookCoef]; positivity
  refine ruleDeterminate_of_phiP 𝔼 hβ0 hβ1 hσ hkp hkw.le hlp hlw ?_ hφp
  have : 0 ≤ (bookCoef β σ φ α εp εw lamP lamW).lamW *
      (bookCoef β σ φ α εp εw lamP lamW).kapP := mul_nonneg hlw.le hkp
  have : 0 < (bookCoef β σ φ α εp εw lamP lamW).lamP *
      (bookCoef β σ φ α εp εw lamP lamW).kapW := mul_pos hlp hkw
  linarith

/-- **Galí (2015), §6.4.1, p. 182 (implementation, unconditional)**: for the book's coefficients
(`0 < β < 1`, `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`, `λ_p, λ_w > 0`) and `φ_p > 1`, under demand shocks
(`Δωⁿ ≡ 0`, `ω̃_{−1} = 0`) the rule `i_t = rⁿ_t + φ_p π^p_t` has the optimal zero allocation with
`i_t = rⁿ_t` as an equilibrium, and it is the only bounded adapted equilibrium. -/
theorem rule_implements_book {β σ φ α εp εw lamP lamW φp : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW)
    (hφp : 1 < φp) (rn : ℕ → Ω → ℝ) :
    RuleEqm 𝔼 (bookCoef β σ φ α εp εw lamP lamW) σ φp rn 0 0 0 0 rn ∧
      ∀ y pp pw w i, RuleEqm 𝔼 (bookCoef β σ φ α εp εw lamP lamW) σ φp rn y pp pw w i →
        y = 0 ∧ pp = 0 ∧ pw = 0 ∧ w = 0 ∧ i = rn := by
  obtain ⟨h1, h2⟩ := rule_implements 𝔼 (c := bookCoef β σ φ α εp εw lamP lamW) (φp := φp) hσ rn
  exact ⟨h1, h2 (ruleDeterminate_book 𝔼 hβ0 hβ1 hσ hφ hα0 hα1 hlp hlw hφp)⟩

end Stoch

/-! ### Composite inflation, footnote 6 and (34)–(36) -/

/-- Galí (2015), fn. 6, p. 183, and (36), p. 184 (survey error 3): for the book's coefficients,
`λ_w κ_p + λ_p κ_w = λ_p λ_w (σ + (φ + α)/(1 − α))`. -/
theorem book_composite_slope {β σ φ α εp εw lamP lamW : ℝ} (hα : α ≠ 1) :
    (bookCoef β σ φ α εp εw lamP lamW).lamW * (bookCoef β σ φ α εp εw lamP lamW).kapP +
        (bookCoef β σ φ α εp εw lamP lamW).lamP * (bookCoef β σ φ α εp εw lamP lamW).kapW =
      lamP * lamW * (σ + (φ + α) / (1 - α)) := by
  have h : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  simp only [bookCoef]
  field_simp
  ring

/-- **Galí (2015), fn. 6, p. 183**: if `κ_p = κ_w ≡ κ` then
`κ = λ_p λ_w/(λ_p + λ_w) · (σ + (φ + α)/(1 − α))`. -/
theorem book_fn6 {β σ φ α εp εw lamP lamW : ℝ} (hα : α ≠ 1) (hl : lamP + lamW ≠ 0)
    (hk : (bookCoef β σ φ α εp εw lamP lamW).kapP = (bookCoef β σ φ α εp εw lamP lamW).kapW) :
    (bookCoef β σ φ α εp εw lamP lamW).kapP =
      lamP * lamW / (lamP + lamW) * (σ + (φ + α) / (1 - α)) := by
  have h := book_composite_slope (β := β) (σ := σ) (φ := φ) (εp := εp) (εw := εw)
    (lamP := lamP) (lamW := lamW) hα
  rw [← hk] at h
  simp only [bookCoef] at h ⊢
  rw [div_mul_eq_mul_div, eq_div_iff hl]
  linear_combination h

/-- Galí (2015), (28), p. 179: under `0 ≤ α < 1`, `σ > 0`, `φ ≥ 0`, `ε_p, ε_w > 0`,
`λ_p, λ_w > 0`, the book's loss weights are positive and `κ_p ≥ 0`, `κ_w > 0`. -/
theorem bookCoef_pos {β σ φ α εp εw lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hεp : 0 < εp) (hεw : 0 < εw) (hlp : 0 < lamP) (hlw : 0 < lamW) :
    0 < (bookCoef β σ φ α εp εw lamP lamW).ay ∧ 0 < (bookCoef β σ φ α εp εw lamP lamW).ap ∧
      0 < (bookCoef β σ φ α εp εw lamP lamW).aw ∧
        0 ≤ (bookCoef β σ φ α εp εw lamP lamW).kapP ∧
          0 < (bookCoef β σ φ α εp εw lamP lamW).kapW := by
  have h1 : 0 < 1 - α := by linarith
  simp only [bookCoef]
  refine ⟨by positivity, by positivity, by positivity, by positivity, by positivity⟩

/-- Galí (2015), (34)–(35), pp. 183–184 (the algebra): from (30) at `t` and `t − 1`, (31) and
(32) with `a_p = ε/λ_p`, `a_w = ε/λ_w`, `κ_p = κ_w = κ` and `κ (λ_p + λ_w) = λ_p λ_w a_y`
(fn. 6), composite inflation is `π̄_t = −(1/ε)(ỹ_t − ỹ_{t−1})`. -/
theorem composite_alg {ay κ lp lw ε y yl p q z1 z1l z2 z2l z3 : ℝ} (hlp : 0 < lp)
    (hlw : 0 < lw) (hε : ε ≠ 0) (hκ : κ ≠ 0) (hkey : κ * (lp + lw) = lp * lw * ay)
    (f1 : ay * y + κ * z1 + κ * z2 = 0) (f1l : ay * yl + κ * z1l + κ * z2l = 0)
    (f2 : ε / lp * p - (z1 - z1l) + z3 = 0) (f3 : ε / lw * q - (z2 - z2l) - z3 = 0) :
    lw / (lp + lw) * p + lp / (lp + lw) * q = -(1 / ε) * (y - yl) := by
  have g2 : ε * p = lp * (z1 - z1l - z3) := by
    have : ε / lp * p = z1 - z1l - z3 := by linarith
    rw [div_mul_eq_mul_div, div_eq_iff hlp.ne'] at this
    linarith
  have g3 : ε * q = lw * (z2 - z2l + z3) := by
    have : ε / lw * q = z2 - z2l + z3 := by linarith
    rw [div_mul_eq_mul_div, div_eq_iff hlw.ne'] at this
    linarith
  have h : κ * (ε * (lw * p + lp * q)) = κ * (-(lp + lw) * (y - yl)) := by
    linear_combination (κ * lw) * g2 + (κ * lp) * g3 + (lp * lw) * (f1 - f1l) + (y - yl) * hkey
  have h' := mul_left_cancel₀ hκ h
  have hs : 0 < lp + lw := by linarith
  field_simp
  linear_combination h'

/-- Galí (2015), (34)–(35): `κ (λ_p + λ_w) = λ_p λ_w a_y` with `a_y > 0`, `λ_p, λ_w > 0` forces
`κ ≠ 0`. -/
theorem kap_ne_zero {ay κ lp lw : ℝ} (hay : 0 < ay) (hlp : 0 < lp) (hlw : 0 < lw)
    (hkey : κ * (lp + lw) = lp * lw * ay) : κ ≠ 0 := by
  rintro rfl
  have : 0 < lp * lw * ay := by positivity
  linarith

/-- Galí (2015), N6.1 (survey) (the separation identity): with
`π̄ = (λ_w π^p + λ_p π^w)/(λ_p + λ_w)` and `D = π^w − π^p`,
`(ε/λ_p)(π^p)² + (ε/λ_w)(π^w)² = ε(λ_p + λ_w)/(λ_p λ_w) π̄² + ε/(λ_p + λ_w) D²`. -/
theorem separation {lp lw : ℝ} (hlp : 0 < lp) (hlw : 0 < lw) (ε p q : ℝ) :
    ε / lp * p ^ 2 + ε / lw * q ^ 2 =
      ε * (lp + lw) / (lp * lw) * (lw / (lp + lw) * p + lp / (lp + lw) * q) ^ 2 +
        ε / (lp + lw) * (q - p) ^ 2 := by
  have hs : 0 < lp + lw := by linarith
  field_simp
  ring

namespace Det

/-- **Galí (2015), (34)–(35), pp. 183–184 (deterministic)**: in the special case `κ_p = κ_w`,
`ε_p = ε_w(1 − α) = ε` (so `a_p = ε/λ_p`, `a_w = ε/λ_w`) with `κ(λ_p + λ_w) = λ_p λ_w a_y`
(fn. 6), the first-order conditions (30)–(32) imply `π̄_t = −(1/ε) Δỹ_t` for `t ≥ 1` (34) and
`π̄_0 = −(1/ε) ỹ_0` (35) (`ỹ_{−1} := 0`). -/
theorem composite_foc {c : Coef} {ε : ℝ} (hk : c.kapP = c.kapW)
    (hkey : c.kapP * (c.lamP + c.lamW) = c.lamP * c.lamW * c.ay) (hay : 0 < c.ay)
    (hlp : 0 < c.lamP) (hlw : 0 < c.lamW) (hε : ε ≠ 0) (hap : c.ap = ε / c.lamP)
    (haw : c.aw = ε / c.lamW) {y pp pw z1 z2 z3 : ℕ → ℝ} (hfoc : FOC c y pp pw z1 z2 z3)
    (t : ℕ) :
    c.lamW / (c.lamP + c.lamW) * pp t + c.lamP / (c.lamP + c.lamW) * pw t =
      -(1 / ε) * (y t - prev 0 y t) := by
  have hκ := kap_ne_zero hay hlp hlw hkey
  have f1l : c.ay * prev 0 y t + c.kapP * prev 0 z1 t + c.kapP * prev 0 z2 t = 0 := by
    cases t with
    | zero => simp
    | succ s => have := (hfoc s).1; rw [← hk] at this; simpa using this
  have f1 := (hfoc t).1
  rw [← hk] at f1
  have f2 := (hfoc t).2.1
  have f3 := (hfoc t).2.2.1
  rw [hap] at f2
  rw [haw] at f3
  exact composite_alg hlp hlw hε hκ hkey f1 f1l f2 f3

end Det

namespace Stoch

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 184: composite inflation `π̄_t = (λ_w π^p_t + λ_p π^w_t)/(λ_p + λ_w)`. -/
noncomputable def pibar (c : Coef) (pp pw : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (c.lamW / (c.lamP + c.lamW)) • pp t + (c.lamP / (c.lamP + c.lamW)) • pw t

/-- **Galí (2015), (36), p. 184 (composite Phillips curve, all parameters)**: combining (18) and
(20), `π̄_t = β E_t π̄_{t+1} + κ̄ ỹ_t` with `κ̄ = (λ_w κ_p + λ_p κ_w)/(λ_p + λ_w)` (the book writes
`κ`, defined only when `κ_p = κ_w`; survey error 3; for the book's coefficients
`κ̄ = λ_p λ_w (σ + (φ + α)/(1 − α))/(λ_p + λ_w)`, `book_composite_slope`). -/
theorem composite_nkpc {c : Coef} (hl : c.lamP + c.lamW ≠ 0) {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w : ℕ → Ω → ℝ} (hc : Constr 𝔼 c dn w0 y pp pw w) (t : ℕ) :
    pibar c pp pw t = c.β • 𝔼.E t (pibar c pp pw (t + 1)) +
      ((c.lamW * c.kapP + c.lamP * c.kapW) / (c.lamP + c.lamW)) • y t := by
  funext ω
  have e1 := congrFun (hc t).1 ω
  have e2 := congrFun (hc t).2.1 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
  simp only [pibar, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination c.lamW * e1 + c.lamP * e2

/-- **Galí (2015), (34)–(35), pp. 183–184**: in the special case `κ_p = κ_w`, `ε_p = ε_w(1 − α) =
ε` (`a_p = ε/λ_p`, `a_w = ε/λ_w`, and fn. 6: `κ(λ_p + λ_w) = λ_p λ_w a_y`), the first-order
conditions (30)–(32) imply `π̄_t = −(1/ε)(ỹ_t − ỹ_{t−1})` for `t ≥ 1` (34) and
`π̄_0 = −(1/ε) ỹ_0` (35). -/
theorem composite_foc {c : Coef} {ε : ℝ} (hk : c.kapP = c.kapW)
    (hkey : c.kapP * (c.lamP + c.lamW) = c.lamP * c.lamW * c.ay) (hay : 0 < c.ay)
    (hlp : 0 < c.lamP) (hlw : 0 < c.lamW) (hε : ε ≠ 0) (hap : c.ap = ε / c.lamP)
    (haw : c.aw = ε / c.lamW) {y pp pw z1 z2 z3 : ℕ → Ω → ℝ}
    (hfoc : FOCs 𝔼 c y pp pw z1 z2 z3) (t : ℕ) :
    pibar c pp pw t = -(1 / ε) • (y t - prev 0 y t) := by
  have hκ := kap_ne_zero hay hlp hlw hkey
  funext ω
  have f1l : c.ay * prev 0 y t ω + c.kapP * prev 0 z1 t ω + c.kapP * prev 0 z2 t ω = 0 := by
    cases t with
    | zero => simp
    | succ s =>
      have := congrFun (hfoc s).1 ω
      rw [← hk] at this
      simpa using this
  have f1 := congrFun (hfoc t).1 ω
  have f2 := congrFun (hfoc t).2.1 ω
  have f3 := congrFun (hfoc t).2.2.1 ω
  rw [← hk] at f1
  rw [hap] at f2
  rw [haw] at f3
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at f1 f2 f3
  simp only [pibar, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact composite_alg hlp hlw hε hκ hkey f1 f1l f2 f3

/-! ### The special case: strict composite inflation targeting is optimal (p. 184) -/

/-- Galí (2015), N6.1 (survey): the price inflation of the projected plan,
`−λ_p/(λ_p + λ_w) · (π^w_t − π^p_t)` (composite inflation zero, same `D = π^w − π^p`). -/
noncomputable def projP (c : Coef) (pp pw : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (-(c.lamP / (c.lamP + c.lamW))) • (pw t - pp t)

/-- Galí (2015), N6.1 (survey): the wage inflation of the projected plan,
`λ_w/(λ_p + λ_w) · (π^w_t − π^p_t)`. -/
noncomputable def projW (c : Coef) (pp pw : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (c.lamW / (c.lamP + c.lamW)) • (pw t - pp t)

/-- Galí (2015), N6.1 (survey): with `κ_p = κ_w`, (18) − (20) and (21) give the
relative-inflation block `D_t = β E_t D_{t+1} − (λ_p + λ_w) ω̃_t`,
`ω̃_t = ω̃_{t−1} + D_t − Δωⁿ_t`, which does not involve `ỹ` or `π̄`. -/
theorem block_of_constr {c : Coef} (hk : c.kapP = c.kapW) {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ}
    {y pp pw w : ℕ → Ω → ℝ} (hc : Constr 𝔼 c dn w0 y pp pw w) (t : ℕ) :
    pw t - pp t = c.β • 𝔼.E t (pw (t + 1) - pp (t + 1)) - (c.lamP + c.lamW) • w t ∧
      w t = prev w0 w t + (pw t - pp t) - dn t := by
  constructor
  · funext ω
    have e1 := congrFun (hc t).1 ω
    have e2 := congrFun (hc t).2.1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    simp only [map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hk] at e1
    linarith
  · rw [(hc t).2.2]; abel

/-- **Galí (2015), N6.1 (survey) (feasibility of the projection)**: with `κ_p = κ_w`, replacing
`(ỹ, π̄)` by `(0, 0)` and keeping `D = π^w − π^p` and `ω̃` maps plans to plans. -/
theorem proj_plan {c : Coef} (hk : c.kapP = c.kapW) (hl : 0 < c.lamP + c.lamW)
    {dn : ℕ → Ω → ℝ} {w0 : Ω → ℝ} {y pp pw w : ℕ → Ω → ℝ} (hp : Plan 𝔼 c dn w0 y pp pw w) :
    Plan 𝔼 c dn w0 0 (projP c pp pw) (projW c pp pw) w := by
  obtain ⟨hc, -, hppa, hpwa, hwa, -, ⟨Bp, hBp⟩, ⟨Bq, hBq⟩, hwb⟩ := hp
  have hl' := hl.ne'
  refine ⟨fun t => ⟨?_, ?_, ?_⟩, fun t => map_zero _, fun t => ?_, fun t => ?_, hwa,
    ⟨0, fun t ω => by simp⟩, ⟨|c.lamP / (c.lamP + c.lamW)| * (Bq + Bp), fun t ω => ?_⟩,
    ⟨|c.lamW / (c.lamP + c.lamW)| * (Bq + Bp), fun t ω => ?_⟩, hwb⟩
  · funext ω
    have e := congrFun (block_of_constr 𝔼 hk hc t).1 ω
    simp only [map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    simp only [projP, map_smul, map_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_zero, add_zero]
    field_simp
    linear_combination (-c.lamP) * e
  · funext ω
    have e := congrFun (block_of_constr 𝔼 hk hc t).1 ω
    simp only [map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    simp only [projW, map_smul, map_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_zero, add_zero]
    field_simp
    linear_combination c.lamW * e
  · funext ω
    have e := congrFun (block_of_constr 𝔼 hk hc t).2 ω
    simp only [Pi.add_apply, Pi.sub_apply] at e
    simp only [projP, projW, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    field_simp
    ring
  · simp only [projP, map_smul, map_sub, hppa t, hpwa t]
  · simp only [projW, map_smul, map_sub, hppa t, hpwa t]
  · simp only [projP, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hBq t ω) (hBp t ω)))
      (abs_nonneg _)
  · simp only [projW, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hBq t ω) (hBp t ω)))
      (abs_nonneg _)

/-- **Galí (2015), N6.1 (survey) (the projection lowers the loss pathwise)**: with
`a_p = ε/λ_p`, `a_w = ε/λ_w`, the period loss of a plan exceeds that of its projection by
`½ (a_y ỹ_t² + ε(λ_p + λ_w)/(λ_p λ_w) π̄_t²) ≥ 0`, state by state. -/
theorem periodLoss_sub_proj {c : Coef} {ε : ℝ} (hlp : 0 < c.lamP) (hlw : 0 < c.lamW)
    (hap : c.ap = ε / c.lamP) (haw : c.aw = ε / c.lamW) (y pp pw : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    periodLoss c y pp pw t ω - periodLoss c 0 (projP c pp pw) (projW c pp pw) t ω =
      (c.ay * y t ω ^ 2 + ε * (c.lamP + c.lamW) / (c.lamP * c.lamW) * pibar c pp pw t ω ^ 2) /
        2 := by
  have hs := separation hlp hlw ε (pp t ω) (pw t ω)
  have hl : 0 < c.lamP + c.lamW := by linarith
  simp only [periodLoss, projP, projW, pibar, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, Pi.zero_apply, hap, haw]
  field_simp
  field_simp at hs
  linear_combination hs

/-- Galí (2015), p. 184: with composite inflation zero, price and wage inflation are the
projections of `D = π^w − π^p`. -/
theorem eq_proj_of_pibar {c : Coef} (hl : 0 < c.lamP + c.lamW) {pp pw : ℕ → Ω → ℝ} (t : ℕ)
    (h : pibar c pp pw t = 0) : pp t = projP c pp pw t ∧ pw t = projW c pp pw t := by
  constructor <;> funext ω <;> have e := congrFun h ω <;>
    simp only [pibar, projP, projW, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Pi.zero_apply] at e ⊢ <;> field_simp at e ⊢ <;> linarith

/-- **Galí (2015), p. 184 (strict composite inflation targeting is OPTIMAL)**: in the special case
`κ_p = κ_w`, `ε_p = ε_w(1 − α) = ε` (`a_p = ε/λ_p`, `a_w = ε/λ_w`), any plan with `ỹ ≡ 0` and
`π̄ ≡ 0` minimises the welfare loss among all plans, state by state; and any plan with the same
loss at `ω` has `E_0 ỹ_t² = E_0 π̄_t² = 0` there. Proof (survey Note N6.1, replacing the book's
argument, which checks only the necessary conditions (34)–(35): survey error 2): every plan's
projection (same `D`, `ω̃`, with `ỹ = π̄ = 0`) is a plan with pathwise lower loss; by
determinacy of the relative-inflation block all projections coincide with the candidate. No
pull-out property is needed. -/
theorem composite_targeting_optimal {c : Coef} {ε : ℝ} (hk : c.kapP = c.kapW)
    (hlp : 0 < c.lamP) (hlw : 0 < c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hε : 0 < ε) (hap : c.ap = ε / c.lamP) (haw : c.aw = ε / c.lamW) {dn : ℕ → Ω → ℝ}
    {w0 : Ω → ℝ} {ys pps pws ws : ℕ → Ω → ℝ} (hC : Plan 𝔼 c dn w0 ys pps pws ws)
    (hy0 : ys = 0) (hpi : ∀ t, pibar c pps pws t = 0) :
    ∀ y pp pw w, Plan 𝔼 c dn w0 y pp pw w → ∀ ω,
      expLoss 𝔼 c ys pps pws ω ≤ expLoss 𝔼 c y pp pw ω ∧
        (expLoss 𝔼 c y pp pw ω = expLoss 𝔼 c ys pps pws ω → ∀ t,
          𝔼.E 0 (fun ω => y t ω ^ 2) ω = 0 ∧ 𝔼.E 0 (fun ω => pibar c pp pw t ω ^ 2) ω = 0) := by
  intro y pp pw w hp ω
  have hl : 0 < c.lamP + c.lamW := by linarith
  have hapos : 0 ≤ c.ap := by rw [hap]; positivity
  have hawpos : 0 ≤ c.aw := by rw [haw]; positivity
  have hP := proj_plan 𝔼 hk hl hp
  have hyb := hp.2.2.2.2.2.1
  have hppb := hp.2.2.2.2.2.2.1
  have hpwb := hp.2.2.2.2.2.2.2.1
  -- the projection coincides with the candidate
  obtain ⟨hc, -, -, -, hwa, -, -, -, ⟨Mw, hMw⟩⟩ := hp
  obtain ⟨hcs, -, -, -, hwsa, -, -, -, ⟨Mws, hMws⟩⟩ := hC
  set Dd : ℕ → Ω → ℝ := fun t => (pw t - pp t) - (pws t - pps t) with hDd
  set wd : ℕ → Ω → ℝ := fun t => w t - ws t with hwd
  have hb1 : ∀ t, Dd t = c.β • 𝔼.E t (Dd (t + 1)) - (c.lamP + c.lamW) • wd t := by
    intro t
    funext ω
    have e := congrFun (block_of_constr 𝔼 hk hc t).1 ω
    have es := congrFun (block_of_constr 𝔼 hk hcs t).1 ω
    simp only [map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e es
    simp only [hDd, hwd, map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hb2 : ∀ t, wd t = prev 0 wd t + Dd t := by
    intro t
    have e := (block_of_constr 𝔼 hk hc t).2
    have es := (block_of_constr 𝔼 hk hcs t).2
    have hp' := prev_sub w0 w ws t
    simp only [hDd, hwd]
    rw [← hp']
    conv_lhs => rw [e, es]
    abel
  have hwda : 𝔼.Adapted wd := fun t => by simp only [hwd, map_sub, hwa t, hwsa t]
  obtain ⟨hD0, -⟩ := block_zero 𝔼 hβ0 hβ1 hl hwda
    ⟨Mw + Mws, fun t ω => (abs_sub _ _).trans (add_le_add (hMw t ω) (hMws t ω))⟩ hb1 hb2
  have hDeq : ∀ t, pw t - pp t = pws t - pps t := fun t => by
    have := congrFun hD0 t
    simp only [hDd, Pi.zero_apply] at this
    exact sub_eq_zero.1 this
  have hpp : projP c pp pw = pps := funext fun t => by
    rw [(eq_proj_of_pibar hl t (hpi t)).1]; simp only [projP, hDeq t]
  have hpw : projW c pp pw = pws := funext fun t => by
    rw [(eq_proj_of_pibar hl t (hpi t)).2]; simp only [projW, hDeq t]
  rw [hpp, hpw] at hP
  -- the excess loss as a series of nonnegative terms
  have hpl := hP
  obtain ⟨-, -, -, -, -, hysb, hppsb, hpwsb, -⟩ := hpl
  have hS := (expLoss_hasSum 𝔼 hβ0.le hβ1 hay.le hapos hawpos hyb hppb hpwb ω).sub
    (expLoss_hasSum 𝔼 hβ0.le hβ1 hay.le hapos hawpos hysb hppsb hpwsb ω)
  set K := ε * (c.lamP + c.lamW) / (c.lamP * c.lamW) with hK
  have hK0 : 0 < K := by positivity
  have hterm : ∀ t, c.β ^ t * 𝔼.E 0 (periodLoss c y pp pw t) ω -
      c.β ^ t * 𝔼.E 0 (periodLoss c 0 pps pws t) ω =
      c.β ^ t * ((c.ay / 2) * 𝔼.E 0 (fun ω => y t ω ^ 2) ω +
        (K / 2) * 𝔼.E 0 (fun ω => pibar c pp pw t ω ^ 2) ω) := by
    intro t
    have hf : periodLoss c y pp pw t - periodLoss c 0 pps pws t =
        (c.ay / 2) • (fun ω => y t ω ^ 2) + (K / 2) • (fun ω => pibar c pp pw t ω ^ 2) := by
      funext ω'
      have := periodLoss_sub_proj hlp hlw hap haw y pp pw t ω'
      rw [hpp, hpw] at this
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [this, hK]
      ring
    rw [← mul_sub, ← Pi.sub_apply (𝔼.E 0 _), ← map_sub, hf, map_add, map_smul, map_smul]
    rfl
  rw [hy0]
  simp only [hterm] at hS
  have hnn : ∀ t, 0 ≤ c.β ^ t * ((c.ay / 2) * 𝔼.E 0 (fun ω => y t ω ^ 2) ω +
      (K / 2) * 𝔼.E 0 (fun ω => pibar c pp pw t ω ^ 2) ω) := fun t => by
    have h1 := E_nonneg 𝔼 (f := fun ω => y t ω ^ 2) (fun ω => by positivity) 0 ω
    have h2 := E_nonneg 𝔼 (f := fun ω => pibar c pp pw t ω ^ 2) (fun ω => by positivity) 0 ω
    positivity
  refine ⟨sub_nonneg.1 (hS.nonneg hnn), fun heq t => ?_⟩
  rw [heq, sub_self] at hS
  have hz := congrFun ((hasSum_zero_iff_of_nonneg hnn).1 hS) t
  simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
    false_or] at hz
  have h1 := E_nonneg 𝔼 (f := fun ω => y t ω ^ 2) (fun ω => by positivity) 0 ω
  have h2 := E_nonneg 𝔼 (f := fun ω => pibar c pp pw t ω ^ 2) (fun ω => by positivity) 0 ω
  have k1 := mul_nonneg (half_pos hay).le h1
  have k2 := mul_nonneg (half_pos hK0).le h2
  constructor
  · have : c.ay / 2 * 𝔼.E 0 (fun ω => y t ω ^ 2) ω = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (half_pos hay).ne'
  · have : K / 2 * 𝔼.E 0 (fun ω => pibar c pp pw t ω ^ 2) ω = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (half_pos hK0).ne'

/-- Galí (2015), N6.1 (survey): the real wage gap of the candidate plan,
`ω̃_t = r ω̃_{t−1} + v_t` with `ω̃_{−1} = w0`. -/
def wSeq (r : ℝ) (w0 : Ω → ℝ) (v : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => r • w0 + v 0
  | t + 1 => r • wSeq r w0 v t + v (t + 1)

/-- Galí (2015), N6.1 (survey): `ω̃_t = r ω̃_{t−1} + v_t`. -/
theorem wSeq_eq (r : ℝ) (w0 : Ω → ℝ) (v : ℕ → Ω → ℝ) (t : ℕ) :
    wSeq r w0 v t = r • prev w0 (wSeq r w0 v) t + v t := by
  cases t <;> rfl

/-- Galí (2015), p. 181: the lag of an adapted process with a date-0-known initial value is
adapted. -/
theorem prev_adapted {w0 : Ω → ℝ} {w : ℕ → Ω → ℝ} (hw0 : 𝔼.E 0 w0 = w0) (hwa : 𝔼.Adapted w) :
    𝔼.Adapted (prev w0 w) := by
  intro t
  cases t with
  | zero => exact hw0
  | succ t => simp only [prev_succ]; rw [← hwa t, 𝔼.known (Nat.le_succ t)]

/-- **Galí (2015), p. 184 (existence of the strict composite-targeting plan)**: with
`λ_p, λ_w > 0`, `0 < β < 1`, a bounded adapted `Δωⁿ` and a bounded date-0-known `ω̃_{−1}`, there
is a plan with `ỹ ≡ 0` and `π̄ ≡ 0`: `ω̃_t = r ω̃_{t−1} + v_t` where `r ∈ (0, 1)` is the stable
root of the relative-inflation block and `v` the forward solution of
`v_t = β r E_t v_{t+1} + r (β E_t Δωⁿ_{t+1} − Δωⁿ_t)`, `D_t = ω̃_t − ω̃_{t−1} + Δωⁿ_t`,
`π^p = −λ_p D/(λ_p + λ_w)`, `π^w = λ_w D/(λ_p + λ_w)`. -/
theorem exists_composite_plan {c : Coef} (hlp : 0 < c.lamP)
    (hlw : 0 < c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) {dn : ℕ → Ω → ℝ} {Md : ℝ}
    (hdb : ∀ t ω, |dn t ω| ≤ Md) (hda : 𝔼.Adapted dn) {w0 : Ω → ℝ} {M0 : ℝ}
    (hw0 : 𝔼.E 0 w0 = w0) (hw0b : ∀ ω, |w0 ω| ≤ M0) :
    ∃ pp pw w, Plan 𝔼 c dn w0 0 pp pw w ∧ ∀ t, pibar c pp pw t = 0 := by
  set k := c.lamP + c.lamW with hk_def
  have hkpos : 0 < k := by positivity
  obtain ⟨r, hr0, hr1, hr⟩ := exists_block_root (β := c.β) hkpos
  set f : ℕ → Ω → ℝ := fun t => c.β • 𝔼.E t (dn (t + 1)) - dn t with hf_def
  set u : ℕ → Ω → ℝ := fun t => r • f t with hu_def
  have hub : ∀ t ω, |u t ω| ≤ r * (c.β * Md + Md) := by
    intro t ω
    simp only [hu_def, hf_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul,
      abs_of_pos hr0]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ (hdb t ω))) hr0.le
    rw [abs_mul, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdb (t + 1)) t ω) hβ0.le
  have hua : 𝔼.Adapted u := fun t => by
    simp only [hu_def, hf_def, map_smul, map_sub, 𝔼.E_E_self, hda t]
  have ha0 : 0 ≤ c.β * r := by positivity
  have ha1 : c.β * r < 1 := by nlinarith
  set v := 𝔼.forwardSeries (c.β * r) u with hv_def
  have hv : ∀ t, v t = (c.β * r) • 𝔼.E t (v (t + 1)) + u t :=
    𝔼.forwardSeries_solves ha0 ha1 hub hua
  have hva : 𝔼.Adapted v := 𝔼.forwardSeries_adapted ha0 ha1 hub
  obtain ⟨V, hV⟩ := 𝔼.forwardSeries_bounded ha0 ha1 hub
  set w := wSeq r w0 v with hw_def
  have hwa : 𝔼.Adapted w := by
    intro t
    induction t with
    | zero =>
      change 𝔼.E 0 (r • w0 + v 0) = r • w0 + v 0
      rw [map_add, map_smul, hw0, hva 0]
    | succ t ih =>
      change 𝔼.E (t + 1) (r • w t + v (t + 1)) = r • w t + v (t + 1)
      rw [map_add, map_smul, hva (t + 1), ← ih, 𝔼.known (Nat.le_succ t)]
  have hpa := prev_adapted 𝔼 hw0 hwa
  set B := |M0| + |V| / (1 - r) with hB
  have hB1 : |V| ≤ (1 - r) * B := by
    rw [hB, mul_add, mul_div_cancel₀ _ (by linarith : (1 - r) ≠ 0)]
    nlinarith [abs_nonneg M0]
  have hwb : ∀ t ω, |w t ω| ≤ B := by
    have hstep : ∀ t ω, |prev w0 w t ω| ≤ B → |w t ω| ≤ B := by
      intro t ω h
      have := congrFun (wSeq_eq r w0 v t) ω
      rw [← hw_def] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hr0]
      have h1 := mul_le_mul_of_nonneg_left h hr0.le
      have h2 := (hV t ω).trans (le_abs_self V)
      linarith
    intro t
    induction t with
    | zero => exact fun ω => hstep 0 ω (by
        simp only [prev_zero]
        have := abs_nonneg V
        have : 0 ≤ |V| / (1 - r) := div_nonneg (abs_nonneg V) (by linarith)
        linarith [hw0b ω, le_abs_self M0])
    | succ t ih => exact fun ω => hstep (t + 1) ω (ih ω)
  have hpb : ∀ t ω, |prev w0 w t ω| ≤ B := by
    intro t ω
    cases t with
    | zero =>
      have : 0 ≤ |V| / (1 - r) := div_nonneg (abs_nonneg V) (by linarith)
      simp only [prev_zero]
      linarith [hw0b ω, le_abs_self M0]
    | succ t => exact hwb t ω
  set D : ℕ → Ω → ℝ := fun t => w t - prev w0 w t + dn t with hD_def
  have hblock : ∀ t, D t = c.β • 𝔼.E t (D (t + 1)) - k • w t := by
    intro t
    have hEw : 𝔼.E t (w (t + 1)) = r • w t + 𝔼.E t (v (t + 1)) := by
      change 𝔼.E t (r • w t + v (t + 1)) = _
      rw [map_add, map_smul, hwa t]
    have hED : 𝔼.E t (D (t + 1)) = 𝔼.E t (w (t + 1)) - w t + 𝔼.E t (dn (t + 1)) := by
      simp only [hD_def, prev_succ, map_add, map_sub, hwa t]
    funext ω
    have e1 := congrFun hEw ω
    have e2 := congrFun hED ω
    have e3 := congrFun (hv t) ω
    have e4 := congrFun (wSeq_eq r w0 v t) ω
    rw [← hw_def] at e4
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4
    simp only [hu_def, hf_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e3
    simp only [hD_def, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hD_def] at e2
    simp only at e2
    rw [e2]
    refine mul_left_cancel₀ hr0.ne' ?_
    linear_combination e4 + (-r * c.β) * e1 + e3 - (w t ω) * hr
  have hl' := hkpos.ne'
  refine ⟨fun t => (-(c.lamP / k)) • D t, fun t => (c.lamW / k) • D t, w,
    ⟨fun t => ⟨?_, ?_, ?_⟩, fun t => map_zero _, fun t => ?_, fun t => ?_, hwa,
      ⟨0, fun t ω => by simp⟩, ⟨c.lamP / k * (B + B + Md), fun t ω => ?_⟩,
      ⟨c.lamW / k * (B + B + Md), fun t ω => ?_⟩, ⟨B, hwb⟩⟩, fun t => ?_⟩
  · funext ω
    have e := congrFun (hblock t) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    simp only [map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
      add_zero]
    rw [e]
    field_simp
    ring
  · funext ω
    have e := congrFun (hblock t) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    simp only [map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      mul_zero, add_zero]
    rw [e]
    field_simp
  · funext ω
    simp only [hD_def, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · simp only [hD_def, map_smul, map_add, map_sub, hwa t, hpa t, hda t]
  · simp only [hD_def, map_smul, map_add, map_sub, hwa t, hpa t, hda t]
  · have hDb : |D t ω| ≤ B + B + Md := by
      simp only [hD_def, Pi.add_apply, Pi.sub_apply]
      refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
        (add_le_add (hwb t ω) (hpb t ω))) (hdb t ω))
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos (div_pos hlp hkpos)]
    exact mul_le_mul_of_nonneg_left hDb (div_pos hlp hkpos).le
  · have hDb : |D t ω| ≤ B + B + Md := by
      simp only [hD_def, Pi.add_apply, Pi.sub_apply]
      refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
        (add_le_add (hwb t ω) (hpb t ω))) (hdb t ω))
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (div_pos hlw hkpos)]
    exact mul_le_mul_of_nonneg_left hDb (div_pos hlw hkpos).le
  · funext ω
    simp only [pibar, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ← hk_def]
    field_simp
    ring

/-- **Galí (2015), §6.4.3, pp. 183–184 (THE OPTIMAL POLICY IN THE SPECIAL CASE)**: with
`κ_p = κ_w`, `ε_p = ε_w(1 − α) = ε`, `λ_p, λ_w > 0`, `0 < β < 1`, a bounded adapted `Δωⁿ` and a
bounded date-0-known `ω̃_{−1}`, there is a plan with `ỹ ≡ 0` and `π̄ ≡ 0` (strict composite
inflation targeting), it minimises the welfare loss among all plans state by state, and any plan
with the same loss at `ω` has `E_0 ỹ_t² = E_0 π̄_t² = 0` there. -/
theorem composite_targeting_solves {c : Coef} {ε : ℝ} (hk : c.kapP = c.kapW)
    (hlp : 0 < c.lamP) (hlw : 0 < c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hε : 0 < ε) (hap : c.ap = ε / c.lamP) (haw : c.aw = ε / c.lamW) {dn : ℕ → Ω → ℝ}
    {Md : ℝ} (hdb : ∀ t ω, |dn t ω| ≤ Md) (hda : 𝔼.Adapted dn) {w0 : Ω → ℝ} {M0 : ℝ}
    (hw0 : 𝔼.E 0 w0 = w0) (hw0b : ∀ ω, |w0 ω| ≤ M0) :
    ∃ pp pw w, Plan 𝔼 c dn w0 0 pp pw w ∧ (∀ t, pibar c pp pw t = 0) ∧
      ∀ y' pp' pw' w', Plan 𝔼 c dn w0 y' pp' pw' w' → ∀ ω,
        expLoss 𝔼 c 0 pp pw ω ≤ expLoss 𝔼 c y' pp' pw' ω ∧
          (expLoss 𝔼 c y' pp' pw' ω = expLoss 𝔼 c 0 pp pw ω → ∀ t,
            𝔼.E 0 (fun ω => y' t ω ^ 2) ω = 0 ∧
              𝔼.E 0 (fun ω => pibar c pp' pw' t ω ^ 2) ω = 0) := by
  obtain ⟨pp, pw, w, hC, hpi⟩ := exists_composite_plan 𝔼 hlp hlw hβ0 hβ1 hdb hda hw0 hw0b
  exact ⟨pp, pw, w, hC, hpi,
    composite_targeting_optimal 𝔼 hk hlp hlw hβ0 hβ1 hay hε hap haw hC rfl hpi⟩

/-- **Galí (2015), pp. 184–185 (strict composite targeting ⇔ output-gap stabilisation, ALL
parameters)**: for a plan (bounded adapted solution of (18), (20), (21)), with `λ_p + λ_w > 0`,
`λ_w κ_p + λ_p κ_w ≠ 0` and `|β| < 1`: `π̄ ≡ 0` iff `ỹ ≡ 0` (`⇒` from (36); `⇐`: the only bounded
solution of `π̄_t = β E_t π̄_{t+1}` is zero). -/
theorem composite_zero_iff {c : Coef} (hl : 0 < c.lamP + c.lamW)
    (hkb : c.lamW * c.kapP + c.lamP * c.kapW ≠ 0) (hβ : |c.β| < 1) {dn : ℕ → Ω → ℝ}
    {w0 : Ω → ℝ} {y pp pw w : ℕ → Ω → ℝ} (hp : Plan 𝔼 c dn w0 y pp pw w) :
    (∀ t, pibar c pp pw t = 0) ↔ y = 0 := by
  obtain ⟨hc, -, -, -, -, -, ⟨Bp, hBp⟩, ⟨Bq, hBq⟩, -⟩ := hp
  have hn := composite_nkpc 𝔼 hl.ne' hc
  have hkb' : (c.lamW * c.kapP + c.lamP * c.kapW) / (c.lamP + c.lamW) ≠ 0 :=
    div_ne_zero hkb hl.ne'
  constructor
  · intro h
    funext t ω
    have := congrFun (hn t) ω
    rw [h t, h (t + 1), map_zero] at this
    simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero,
      zero_add] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hkb'
  · rintro rfl
    have hb : BoundedProc (pibar c pp pw) := ⟨|c.lamW / (c.lamP + c.lamW)| * Bp +
        |c.lamP / (c.lamP + c.lamW)| * Bq, fun t ω => by
      simp only [pibar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_mul_of_nonneg_left (hBp t ω) (abs_nonneg _)
      · exact mul_le_mul_of_nonneg_left (hBq t ω) (abs_nonneg _)⟩
    have h1 : ∀ t, pibar c pp pw t = c.β • 𝔼.E t (pibar c pp pw (t + 1)) +
        (0 : ℕ → Ω → ℝ) t := fun t => by
      rw [hn t]; simp
    have h2 : ∀ t, (0 : ℕ → Ω → ℝ) t = c.β • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) +
        (0 : ℕ → Ω → ℝ) t := fun t => by simp
    have := 𝔼.forward_unique hβ h1 h2 hb ⟨0, fun t ω => by simp⟩
    exact fun t => congrFun this t

end Stoch

/-! ### Composite weights (p. 184) -/

/-- Galí (2015), (6), p. 165, and (15), p. 170: the Calvo slope factor `(1 − θ)(1 − βθ)/θ`
(`λ_p = Θ · calvo β θ_p`, `λ_w = calvo β θ_w/(1 + ε_w φ)`). -/
noncomputable def calvo (β θ : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ

/-- Galí (2015), p. 170: `λ_w = (1 − θ_w)(1 − βθ_w)/(θ_w(1 + ε_w φ))`. -/
noncomputable def lamWOf (β εw φ θw : ℝ) : ℝ := calvo β θw / (1 + εw * φ)

/-- Galí (2015), p. 165: `λ_p = (1 − θ_p)(1 − βθ_p)/θ_p · (1 − α)/(1 − α + αε_p)`. -/
noncomputable def lamPOf (β α εp θp : ℝ) : ℝ := calvo β θp * ((1 - α) / (1 - α + α * εp))

/-- Galí (2015), p. 170: the Calvo slope factor is positive for `θ ∈ (0, 1)`, `β ≤ 1`. -/
theorem calvo_pos {β θ : ℝ} (hβ1 : β ≤ 1) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) :
    0 < calvo β θ := by
  obtain ⟨h0, h1⟩ := hθ
  unfold calvo
  have : 0 < 1 - β * θ := by nlinarith
  have : 0 < 1 - θ := by linarith
  positivity

/-- Galí (2015), pp. 179, 184: the Calvo slope factor is strictly decreasing in the degree of
stickiness `θ` on `(0, 1)` (`β ≤ 1`). -/
theorem calvo_strictAntiOn {β : ℝ} (hβ1 : β ≤ 1) :
    StrictAntiOn (calvo β) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  unfold calvo
  rw [div_lt_div_iff₀ hb0 ha0]
  have hab1 : β * (a * b) < 1 := by
    have : a * b < 1 := by nlinarith
    nlinarith [mul_pos ha0 hb0]
  nlinarith [mul_pos (sub_pos.2 hab) (sub_pos.2 hab1)]

/-- **Galí (2015), p. 184 (composite weights)**: the weight `λ_p/(λ_p + λ_w)` on wage inflation
in composite inflation is strictly increasing in the degree of wage stickiness `θ_w ∈ (0, 1)`
(`λ_p > 0`, `1 + ε_w φ > 0`, `β ≤ 1`). -/
theorem wage_weight_strictMonoOn {β εw φ lamP : ℝ} (hβ1 : β ≤ 1)
    (hlp : 0 < lamP) (hd : 0 < 1 + εw * φ) :
    StrictMonoOn (fun θw => lamP / (lamP + lamWOf β εw φ θw)) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  have hpa := calvo_pos hβ1 ha
  have hpb := calvo_pos hβ1 hb
  have hlt := calvo_strictAntiOn hβ1 ha hb hab
  simp only [lamWOf]
  have h1 : 0 < calvo β b / (1 + εw * φ) := div_pos hpb hd
  apply div_lt_div_of_pos_left hlp (by positivity)
  have := div_lt_div_of_pos_right hlt hd
  linarith

/-- **Galí (2015), p. 184 (composite weights)**: the weight `λ_w/(λ_p + λ_w)` on price inflation
in composite inflation is strictly increasing in the degree of price stickiness `θ_p ∈ (0, 1)`
(`λ_w > 0`, `α < 1`, `1 − α + αε_p > 0`, `β ≤ 1`). -/
theorem price_weight_strictMonoOn {β α εp lamW : ℝ} (hβ1 : β ≤ 1)
    (hlw : 0 < lamW) (hα1 : α < 1) (hd : 0 < 1 - α + α * εp) :
    StrictMonoOn (fun θp => lamW / (lamPOf β α εp θp + lamW)) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  have hpa := calvo_pos hβ1 ha
  have hpb := calvo_pos hβ1 hb
  have hlt := calvo_strictAntiOn hβ1 ha hb hab
  have hΘ : 0 < (1 - α) / (1 - α + α * εp) := div_pos (by linarith) hd
  simp only [lamPOf]
  have h1 : 0 < calvo β b * ((1 - α) / (1 - α + α * εp)) := mul_pos hpb hΘ
  apply div_lt_div_of_pos_left hlw (by positivity)
  have := mul_lt_mul_of_pos_right hlt hΘ
  linarith

/-! ### The special case under perfect foresight, among all finite-loss paths -/

namespace Det

/-- **Galí (2015), N6.1 (survey) (the relative-inflation block, finite-loss version)**: with
`0 < β < 1`, `k > 0`, the only solution of `D_t = β D_{t+1} − k ω̃_t`, `ω̃_t = ω̃_{t−1} + D_t`,
`ω̃_{−1} = 0`, with `∑ βᵗ D_t² < ∞` is zero. -/
theorem block_zero_finite {β k : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hk : 0 < k) {D w : ℕ → ℝ}
    (hs : Summable (fun t => β ^ t * D t ^ 2)) (h1 : ∀ t, D t = β * D (t + 1) - k * w t)
    (h2 : ∀ t, w t = prev 0 w t + D t) : D = 0 ∧ w = 0 := by
  obtain ⟨r, hr0, hr1, hr⟩ := exists_block_root (β := β) hk
  set v : ℕ → ℝ := fun t => w t - r * prev 0 w t with hv_def
  have hv : ∀ t, v t = β * r * v (t + 1) := by
    intro t
    have a := h1 t
    have b := h2 t
    have b' := h2 (t + 1)
    simp only [hv_def, prev_succ] at b' ⊢
    linear_combination r * a + r * b - r * β * b' + (w t) * hr
  -- `βᵗ ω̃_t² → 0`
  have hD0 := hs.tendsto_atTop_zero
  have hD1 : Tendsto (fun t => β ^ (t + 1) * D (t + 1) ^ 2) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 hD0
  have hw0 : Tendsto (fun t => β ^ t * w t ^ 2) atTop (𝓝 0) := by
    have hup := (hD1.add hD0).const_mul (2 / k ^ 2)
    rw [add_zero, mul_zero] at hup
    refine squeeze_zero (fun t => by positivity) (fun t => ?_) hup
    have hwt : k * w t = β * D (t + 1) - D t := by linarith [h1 t]
    have hb : 0 ≤ β ^ t := pow_nonneg hβ0.le t
    have hsq : k ^ 2 * w t ^ 2 ≤ 2 * (β * D (t + 1)) ^ 2 + 2 * D t ^ 2 := by
      rw [← mul_pow, hwt]; nlinarith [sq_nonneg (β * D (t + 1) + D t)]
    have hβD : β ^ t * (β * D (t + 1)) ^ 2 ≤ β ^ (t + 1) * D (t + 1) ^ 2 := by
      have hX : 0 ≤ β ^ (t + 1) * D (t + 1) ^ 2 := by positivity
      have : β ^ t * (β * D (t + 1)) ^ 2 = β * (β ^ (t + 1) * D (t + 1) ^ 2) := by ring
      rw [this]
      nlinarith
    rw [show 2 / k ^ 2 * (β ^ (t + 1) * D (t + 1) ^ 2 + β ^ t * D t ^ 2) =
      (2 * (β ^ (t + 1) * D (t + 1) ^ 2) + 2 * (β ^ t * D t ^ 2)) / k ^ 2 by ring,
      le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hsq hb
    nlinarith
  have hp0 : Tendsto (fun t => β ^ t * prev 0 w t ^ 2) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have : (fun t => β ^ (t + 1) * prev 0 w (t + 1) ^ 2) = fun t => β * (β ^ t * w t ^ 2) := by
      funext t; rw [prev_succ, pow_succ]; ring
    rw [this]
    simpa using hw0.const_mul β
  have hvt : Tendsto (fun t => β ^ t * v t ^ 2) atTop (𝓝 0) := by
    have hup := (hw0.const_mul 2).add (hp0.const_mul 2)
    rw [mul_zero, add_zero] at hup
    refine squeeze_zero (fun t => by positivity) (fun t => ?_) hup
    have hb : 0 ≤ β ^ t := pow_nonneg hβ0.le t
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    have : v t ^ 2 ≤ 2 * w t ^ 2 + 2 * prev 0 w t ^ 2 := by
      simp only [hv_def]
      nlinarith [sq_nonneg (w t + r * prev 0 w t), sq_nonneg (prev 0 w t),
        mul_le_mul_of_nonneg_right hr2 (sq_nonneg (prev 0 w t))]
    nlinarith [mul_le_mul_of_nonneg_left this hb]
  have hvz : ∀ s, v s = 0 := by
    intro s
    have hit : ∀ n, β ^ s * v s ^ 2 = (β * r ^ 2) ^ n * (β ^ (s + n) * v (s + n) ^ 2) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [ih, hv (s + n), ← add_assoc]
        ring
    have hle : ∀ n, β ^ s * v s ^ 2 ≤ β ^ (s + n) * v (s + n) ^ 2 := by
      intro n
      rw [hit n]
      have h1 : (β * r ^ 2) ^ n ≤ 1 := pow_le_one₀ (by positivity) (by nlinarith)
      have h2 : 0 ≤ β ^ (s + n) * v (s + n) ^ 2 := by positivity
      nlinarith
    have hlim : Tendsto (fun n => β ^ (s + n) * v (s + n) ^ 2) atTop (𝓝 0) := by
      have := (tendsto_add_atTop_iff_nat s).2 hvt
      simpa [add_comm] using this
    have h0 : β ^ s * v s ^ 2 ≤ 0 := ge_of_tendsto' hlim hle
    have hbs : 0 < β ^ s := pow_pos hβ0 s
    have : v s ^ 2 = 0 := by nlinarith [sq_nonneg (v s)]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  have hw : ∀ t, w t = 0 := by
    intro t
    induction t with
    | zero => have := hvz 0; simpa [hv_def] using this
    | succ t ih =>
      have := hvz (t + 1)
      simp only [hv_def, prev_succ, ih, mul_zero, sub_zero] at this
      exact this
  refine ⟨funext fun t => ?_, funext hw⟩
  have := h2 t
  rw [hw t] at this
  cases t with
  | zero => simpa using this.symm
  | succ t => simpa [hw t] using this.symm

/-- Galí (2015), N6.1 (survey): the projected price inflation `−λ_p/(λ_p + λ_w) · D_t`. -/
noncomputable def projP (c : Coef) (pp pw : ℕ → ℝ) (t : ℕ) : ℝ :=
  -(c.lamP / (c.lamP + c.lamW)) * (pw t - pp t)

/-- Galí (2015), N6.1 (survey): the projected wage inflation `λ_w/(λ_p + λ_w) · D_t`. -/
noncomputable def projW (c : Coef) (pp pw : ℕ → ℝ) (t : ℕ) : ℝ :=
  c.lamW / (c.lamP + c.lamW) * (pw t - pp t)

/-- Galí (2015), p. 184: composite inflation (perfect foresight). -/
noncomputable def pibar (c : Coef) (pp pw : ℕ → ℝ) (t : ℕ) : ℝ :=
  c.lamW / (c.lamP + c.lamW) * pp t + c.lamP / (c.lamP + c.lamW) * pw t

/-- **Galí (2015), N6.1 (survey) (feasibility of the projection, deterministic)**: with
`κ_p = κ_w`, replacing `(ỹ, π̄)` by `(0, 0)` and keeping `D`, `ω̃` preserves (18), (20), (21). -/
theorem proj_feasible {c : Coef} (hk : c.kapP = c.kapW) (hl : 0 < c.lamP + c.lamW)
    {dn : ℕ → ℝ} {w0 : ℝ} {y pp pw w : ℕ → ℝ} (hf : Feasible c dn w0 y pp pw w) :
    Feasible c dn w0 0 (projP c pp pw) (projW c pp pw) w := by
  intro t
  obtain ⟨e1, e2, e3⟩ := hf t
  have hl' := hl.ne'
  rw [hk] at e1
  refine ⟨?_, ?_, ?_⟩
  · simp only [projP, Pi.zero_apply, mul_zero, add_zero]
    field_simp
    linear_combination (-c.lamP) * (e2 - e1)
  · simp only [projW, Pi.zero_apply, mul_zero, add_zero]
    field_simp
    linear_combination c.lamW * (e2 - e1)
  · simp only [projP, projW]
    rw [e3]
    field_simp
    ring

/-- **Galí (2015), N6.1 (survey) (the projection lowers the loss, period by period)**: with
`a_p = ε/λ_p`, `a_w = ε/λ_w`, the discounted period loss exceeds that of the projection by
`βᵗ ½ (a_y ỹ_t² + ε(λ_p + λ_w)/(λ_p λ_w) π̄_t²)`. -/
theorem lossTerm_sub_proj {c : Coef} {ε : ℝ} (hlp : 0 < c.lamP) (hlw : 0 < c.lamW)
    (hap : c.ap = ε / c.lamP) (haw : c.aw = ε / c.lamW) (y pp pw : ℕ → ℝ) (t : ℕ) :
    lossTerm c y pp pw t - lossTerm c 0 (projP c pp pw) (projW c pp pw) t =
      c.β ^ t * ((c.ay * y t ^ 2 +
        ε * (c.lamP + c.lamW) / (c.lamP * c.lamW) * pibar c pp pw t ^ 2) / 2) := by
  have hs := separation hlp hlw ε (pp t) (pw t)
  have hl : 0 < c.lamP + c.lamW := by linarith
  simp only [lossTerm, projP, projW, pibar, Pi.zero_apply, hap, haw]
  field_simp
  field_simp at hs
  linear_combination c.β ^ t * hs

/-- **Galí (2015), §6.4.3, p. 184 (strict composite targeting is OPTIMAL, deterministic)**: in the
special case `κ_p = κ_w`, `ε_p = ε_w(1 − α) = ε`, a feasible finite-loss path with `ỹ ≡ 0` and
`π̄ ≡ 0` solves the commitment problem (among all feasible finite-loss paths), and it is the
unique solution. The proof is the separation argument of survey Note N6.1 (the book's argument
only checks the necessary conditions (34)–(35): survey error 2). -/
theorem composite_targeting_optimal {c : Coef} {ε : ℝ} (hk : c.kapP = c.kapW)
    (hlp : 0 < c.lamP) (hlw : 0 < c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hε : 0 < ε) (hap : c.ap = ε / c.lamP) (haw : c.aw = ε / c.lamW) {dn : ℕ → ℝ} {w0 : ℝ}
    {pps pws ws : ℕ → ℝ} (hC : Feasible c dn w0 0 pps pws ws) (hCl : FiniteLoss c 0 pps pws)
    (hpi : ∀ t, pibar c pps pws t = 0) :
    IsOptimal c dn w0 0 pps pws ws ∧
      ∀ y pp pw w, IsOptimal c dn w0 y pp pw w ↔ y = 0 ∧ pp = pps ∧ pw = pws ∧ w = ws := by
  have hl : 0 < c.lamP + c.lamW := by linarith
  have hapos : 0 < c.ap := by rw [hap]; positivity
  have hawpos : 0 < c.aw := by rw [haw]; positivity
  set K := ε * (c.lamP + c.lamW) / (c.lamP * c.lamW) with hK
  have hK0 : 0 < K := by positivity
  have hCproj : ∀ t, pps t = projP c pps pws t ∧ pws t = projW c pps pws t := by
    intro t
    have e := hpi t
    simp only [pibar, projP, projW] at e ⊢
    constructor <;> field_simp at e ⊢ <;> linarith
  -- every feasible finite-loss path projects onto the candidate
  have key : ∀ y pp pw w, Feasible c dn w0 y pp pw w → FiniteLoss c y pp pw →
      projP c pp pw = pps ∧ projW c pp pw = pws ∧ w = ws ∧
        HasSum (fun t => c.β ^ t * ((c.ay * y t ^ 2 + K * pibar c pp pw t ^ 2) / 2))
          (loss c y pp pw - loss c 0 pps pws) := by
    intro y pp pw w hf hfl
    obtain ⟨-, sp, sq⟩ := summable_sq hβ0.le hay hapos hawpos hfl
    obtain ⟨-, sps, sqs⟩ := summable_sq hβ0.le hay hapos hawpos hCl
    have sD := summable_sub_sq hβ0.le (summable_sub_sq hβ0.le sq sp)
      (summable_sub_sq hβ0.le sqs sps)
    have hb1 : ∀ t, (pw t - pp t) - (pws t - pps t) =
        c.β * ((pw (t + 1) - pp (t + 1)) - (pws (t + 1) - pps (t + 1))) -
          (c.lamP + c.lamW) * (w t - ws t) := by
      intro t
      obtain ⟨e1, e2, -⟩ := hf t
      obtain ⟨f1, f2, -⟩ := hC t
      simp only [Pi.zero_apply, mul_zero, add_zero] at f1 f2
      rw [hk] at e1
      linear_combination e2 - e1 - f2 + f1
    have hb2 : ∀ t, w t - ws t = prev 0 (fun s => w s - ws s) t +
        ((pw t - pp t) - (pws t - pps t)) := by
      intro t
      obtain ⟨-, -, e3⟩ := hf t
      obtain ⟨-, -, f3⟩ := hC t
      rw [← prev_sub w0 w ws t]
      linear_combination e3 - f3
    obtain ⟨hD0, hw0⟩ := block_zero_finite hβ0 hβ1 hl sD hb1 hb2
    have hDeq : ∀ t, pw t - pp t = pws t - pps t := fun t => by
      have := congrFun hD0 t
      simp only [Pi.zero_apply] at this
      linarith
    have hpp : projP c pp pw = pps := funext fun t => by
      rw [(hCproj t).1]; simp only [projP, hDeq t]
    have hpw : projW c pp pw = pws := funext fun t => by
      rw [(hCproj t).2]; simp only [projW, hDeq t]
    have hww : w = ws := funext fun t => by
      have := congrFun hw0 t
      simp only [Pi.zero_apply] at this
      linarith
    refine ⟨hpp, hpw, hww, ?_⟩
    have hS := hfl.hasSum.sub hCl.hasSum
    have hfun : (fun t => c.β ^ t * ((c.ay * y t ^ 2 + K * pibar c pp pw t ^ 2) / 2)) =
        fun t => lossTerm c y pp pw t - lossTerm c 0 pps pws t := by
      funext t
      have := lossTerm_sub_proj hlp hlw hap haw y pp pw t
      rw [hpp, hpw] at this
      rw [this, hK]
    rw [hfun]
    exact hS
  have hopt : IsOptimal c dn w0 0 pps pws ws := by
    refine ⟨hC, hCl, fun y pp pw w hf hfl => ?_⟩
    obtain ⟨-, -, -, hS⟩ := key y pp pw w hf hfl
    exact sub_nonneg.1 (hS.nonneg fun t => by positivity)
  refine ⟨hopt, fun y pp pw w => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨hf, hfl, hmin⟩ := h
    obtain ⟨hpp, hpw, hww, hS⟩ := key y pp pw w hf hfl
    have heq : loss c y pp pw = loss c 0 pps pws :=
      le_antisymm (hmin _ _ _ _ hC hCl) (hopt.2.2 _ _ _ _ hf hfl)
    rw [heq, sub_self] at hS
    have hz := (hasSum_zero_iff_of_nonneg (fun t => by positivity)).1 hS
    have ht : ∀ t, y t = 0 ∧ pibar c pp pw t = 0 := fun t => by
      have h := congrFun hz t
      simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
        false_or] at h
      have k1 := mul_nonneg hay.le (sq_nonneg (y t))
      have k2 := mul_nonneg hK0.le (sq_nonneg (pibar c pp pw t))
      have e1 : c.ay * y t ^ 2 = 0 := by linarith
      have e2 : K * pibar c pp pw t ^ 2 = 0 := by linarith
      simp only [mul_eq_zero, hay.ne', hK0.ne', false_or, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_eq_zero_iff] at e1 e2
      exact ⟨e1, e2⟩
    have hproj : ∀ t, pp t = projP c pp pw t ∧ pw t = projW c pp pw t := by
      intro t
      have e := (ht t).2
      simp only [pibar, projP, projW] at e ⊢
      constructor <;> field_simp at e ⊢ <;> linarith
    refine ⟨funext fun t => (ht t).1, funext fun t => ?_, funext fun t => ?_, hww⟩
    · rw [(hproj t).1, hpp]
    · rw [(hproj t).2, hpw]
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact hopt

/-- Galí (2015), (28), p. 179: a bounded path has finite loss (`0 ≤ β < 1`, nonnegative
weights). -/
theorem finiteLoss_of_bounded {c : Coef} (hβ0 : 0 ≤ c.β) (hβ1 : c.β < 1) (hay : 0 ≤ c.ay)
    (hap : 0 ≤ c.ap) (haw : 0 ≤ c.aw) {y pp pw : ℕ → ℝ} {A B C : ℝ} (hy : ∀ t, |y t| ≤ A)
    (hp : ∀ t, |pp t| ≤ B) (hq : ∀ t, |pw t| ≤ C) : FiniteLoss c y pp pw := by
  refine Summable.of_nonneg_of_le (fun t => by unfold lossTerm; positivity) (fun t => ?_)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right ((c.ay * A ^ 2 + c.ap * B ^ 2 +
      c.aw * C ^ 2) / 2))
  have h1 : y t ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hy t) 2
  have h2 : pp t ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hp t) 2
  have h3 : pw t ^ 2 ≤ C ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hq t) 2
  unfold lossTerm
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
  have := mul_le_mul_of_nonneg_left h1 hay
  have := mul_le_mul_of_nonneg_left h2 hap
  have := mul_le_mul_of_nonneg_left h3 haw
  linarith

/-- **Galí (2015), §6.4.3, pp. 183–184 (THE OPTIMAL POLICY IN THE SPECIAL CASE, deterministic)**:
with `κ_p = κ_w`, `ε_p = ε_w(1 − α) = ε`, `λ_p, λ_w > 0`, `0 < β < 1` and a bounded known path
`Δωⁿ`, the commitment problem has exactly one solution, and it has `ỹ ≡ 0` and `π̄ ≡ 0`. -/
theorem composite_targeting_existsUnique {c : Coef} {ε : ℝ} (hk : c.kapP = c.kapW)
    (hlp : 0 < c.lamP) (hlw : 0 < c.lamW) (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hay : 0 < c.ay)
    (hε : 0 < ε) (hap : c.ap = ε / c.lamP) (haw : c.aw = ε / c.lamW) {dn : ℕ → ℝ} {Md : ℝ}
    (hdb : ∀ t, |dn t| ≤ Md) (w0 : ℝ) :
    ∃! p : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ),
      IsOptimal c dn w0 p.1 p.2.1 p.2.2.1 p.2.2.2 ∧ p.1 = 0 ∧
        ∀ t, pibar c p.2.1 p.2.2.1 t = 0 := by
  obtain ⟨pp, pw, w, hP, hpi⟩ := Stoch.exists_composite_plan perfectForesight (c := c) hlp hlw
    hβ0 hβ1 (dn := fun t _ => dn t) (fun t _ => hdb t) (fun _ => rfl) (w0 := fun _ => w0)
    (M0 := |w0|) rfl (fun _ => le_rfl)
  obtain ⟨hc, -, -, -, -, -, ⟨Bp, hBp⟩, ⟨Bq, hBq⟩, -⟩ := hP
  set pp' : ℕ → ℝ := fun t => pp t () with hpp'
  set pw' : ℕ → ℝ := fun t => pw t () with hpw'
  set w' : ℕ → ℝ := fun t => w t () with hw'
  have hprev : ∀ t, prev (fun _ => w0) w t () = prev w0 w' t := fun t => by cases t <;> rfl
  have hf : Feasible c dn w0 0 pp' pw' w' := by
    intro t
    obtain ⟨e1, e2, e3⟩ := hc t
    have e1' := congrFun e1 ()
    have e2' := congrFun e2 ()
    have e3' := congrFun e3 ()
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      hprev] at e1' e2' e3'
    simp only [mul_zero, add_zero] at e1' e2'
    refine ⟨?_, ?_, e3'⟩
    · simp only [Pi.zero_apply, mul_zero, add_zero]
      exact e1'
    · simp only [Pi.zero_apply, mul_zero, add_zero]
      exact e2'
  have hfl : FiniteLoss c 0 pp' pw' := by
    have hapos : 0 ≤ c.ap := by rw [hap]; positivity
    have hawpos : 0 ≤ c.aw := by rw [haw]; positivity
    exact finiteLoss_of_bounded hβ0.le hβ1 hay.le hapos hawpos (A := 0) (fun t => by simp)
      (fun t => hBp t ()) (fun t => hBq t ())
  have hpi' : ∀ t, pibar c pp' pw' t = 0 := fun t => by
    have := congrFun (hpi t) ()
    simpa [Stoch.pibar, pibar] using this
  obtain ⟨hopt, hiff⟩ := composite_targeting_optimal hk hlp hlw hβ0 hβ1 hay hε hap haw hf hfl hpi'
  refine ⟨(0, pp', pw', w'), ⟨hopt, rfl, hpi'⟩, ?_⟩
  rintro ⟨y, a, b, d⟩ ⟨h, -, -⟩
  obtain ⟨h1, h2, h3, h4⟩ := (hiff y a b d).1 h
  rw [h1, h2, h3, h4]

end Det

/-- Galí (2015), §6.4.3, p. 183: for the book's coefficients, the special case `ε_p = ε_w(1 − α)
= ε` gives `a_p = ε/λ_p`, `a_w = ε/λ_w`, and (fn. 6) `κ_p = κ_w` gives
`κ_p (λ_p + λ_w) = λ_p λ_w a_y`: the hypotheses of `Stoch.composite_foc`,
`Stoch.composite_targeting_solves` and `Det.composite_targeting_existsUnique`. -/
theorem book_special_case {β σ φ α εp εw lamP lamW ε : ℝ} (hα : α ≠ 1)
    (hεp : εp = ε) (hεw : εw * (1 - α) = ε)
    (hk : (bookCoef β σ φ α εp εw lamP lamW).kapP = (bookCoef β σ φ α εp εw lamP lamW).kapW) :
    (bookCoef β σ φ α εp εw lamP lamW).ap = ε / (bookCoef β σ φ α εp εw lamP lamW).lamP ∧
      (bookCoef β σ φ α εp εw lamP lamW).aw = ε / (bookCoef β σ φ α εp εw lamP lamW).lamW ∧
        (bookCoef β σ φ α εp εw lamP lamW).kapP *
            ((bookCoef β σ φ α εp εw lamP lamW).lamP + (bookCoef β σ φ α εp εw lamP lamW).lamW) =
          (bookCoef β σ φ α εp εw lamP lamW).lamP * (bookCoef β σ φ α εp εw lamP lamW).lamW *
            (bookCoef β σ φ α εp εw lamP lamW).ay := by
  refine ⟨by simp only [bookCoef, hεp], by simp only [bookCoef, hεw], ?_⟩
  have h := book_composite_slope (β := β) (σ := σ) (φ := φ) (εp := εp) (εw := εw)
    (lamP := lamP) (lamW := lamW) hα
  rw [← hk] at h
  simp only [bookCoef] at h ⊢
  linear_combination h

/-- **Galí (2015), p. 184 (what the book checks; survey error 2)**: the strict composite-targeting
path satisfies the conditions (34)–(35) (`π̄_t = −(1/ε)(ỹ_t − ỹ_{t−1})`, `ỹ_{−1} = 0`) trivially.
These are only NECESSARY conditions (obtained by eliminating the multipliers from (30)–(32)); the
book's "optimal since it satisfies the optimality conditions (34) and (35)" is completed by the
separation argument `Det.composite_targeting_optimal` / `Stoch.composite_targeting_optimal`. -/
theorem composite_path_satisfies_34_35 (c : Coef) (ε : ℝ) {pp pw : ℕ → ℝ}
    (hpi : ∀ t, Det.pibar c pp pw t = 0) (t : ℕ) :
    Det.pibar c pp pw t = -(1 / ε) * ((0 : ℕ → ℝ) t - prev 0 (0 : ℕ → ℝ) t) := by
  rw [hpi t]
  cases t <;> simp

end Gali.StickyWagesPrices.OptimalPolicy
