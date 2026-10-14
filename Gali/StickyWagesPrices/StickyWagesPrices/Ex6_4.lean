/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.Expectations
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.LinearCombination

/-!
# Exercise 6.4: monetary policy and real wage rigidities

Galí (2015), Chapter 6, Exercise 6.4, pp. 197–198. Utility `U(C, N) = C − N²/2`, technology
`Y = A N`, all output consumed, Calvo pricing giving `π_t = β E_t π_{t+1} − λ μ̂_t` with
`μ̂_t = μ_t − μ` the markup gap.

## (a) Efficient output: `efficient_hours_iff`, `hasDerivAt_planner`, `efficient_output_log`
The planner's `A N − N²/2` is uniquely maximised at `N = A`, so `Yᵉ = A²`, `yᵉ = 2a`.

## (b) The wage schedule: `hasDerivAt_utility_C`, `hasDerivAt_utility_N`,
`competitive_supply_log`, `real_wage_schedule`, `real_rigidity`
Competitive labour markets give `W/P = −U_N/U_C = N`, i.e. `w − p = n`; under the schedule
`w = p + n/(1 + δ)` the real wage moves by only `1/(1 + δ) < 1` per unit of employment: a
real rigidity.

## (c)–(d) The natural level and the markup gap
`hasDerivAt_cost` (marginal cost `W/A`), `markup_eq` (`μ_t = a_t − (y_t − a_t)/(1 + δ)`),
`natural_iff` (`μ_t = μ` iff `y_t = yⁿ_t = (2 + δ) a_t − (1 + δ) μ`), `markup_gap`
(`μ̂_t = −(y_t − yⁿ_t)/(1 + δ)`).

## (e) The inflation equation and the tradeoff
* `nkpc_iff`: `π = β E π' + (λ/(1+δ))(y − yᵉ) + (λ/(1+δ))(yᵉ − yⁿ)`; `cost_push`:
  `yᵉ − yⁿ = −δ a + (1 + δ) μ`.
* `divine_iff`, `divine_iff_mu0`, `tradeoff_iff_delta`, `strict_inflation_gap`: zero inflation
  and a zero welfare gap are jointly attainable iff the cost-push term vanishes; with `μ = 0`
  and nonzero productivity this holds iff `δ = 0`, so `δ > 0` creates a tradeoff (keeping
  `π ≡ 0` forces `y − yᵉ = δ a`).

## (f) Discretion with i.i.d. productivity
The loss's `y*_t` is undefined in the exercise (survey error 10): we read it as `yᵉ_t`, and
the "infinitesimally small" desired markup as `μ = 0` exactly.
* `period_problem_iff` (restated from the Chapter 5 project), `discretionEq_iff`: the
  discretionary equilibrium is the NKPC plus the targeting rule `x = −(κ/α_y) π`.
* `discretion_iid_iff`: with `a` i.i.d. (`E_t a_{t+1} = 0`) and bounded, the unique bounded
  discretionary equilibrium is `π_t = −α_y κ δ a_t/(α_y + κ²)`, `y_t − yᵉ_t = κ² δ a_t/(α_y + κ²)`,
  `κ = λ/(1 + δ)`; `discretion_output` gives `y_t = (2 + κ²δ/(α_y + κ²)) a_t`.
* `perfect_competition`: with `δ = 0` (competitive labour market) `π ≡ 0`, `y = yᵉ = 2a`.
-/

namespace Gali.StickyWagesPrices.Ex6_4

/-! ### (a) Efficient output -/

/-- Galí (2015), Exercise 6.4(a), p. 197: the planner's objective `A N − N²/2` (consumption
equals output `A N`) has derivative `A − N`. -/
theorem hasDerivAt_planner (A N : ℝ) :
    HasDerivAt (fun N' => A * N' - N' ^ 2 / 2) (A - N) N := by
  have h := HasDerivAt.sub ((hasDerivAt_id' N).const_mul A) ((hasDerivAt_pow 2 N).div_const 2)
  exact h.congr_deriv (by norm_num)

/-- Galí (2015), Exercise 6.4(a), p. 197 (**necessary and sufficient**): `N` maximises
`A N − N²/2` iff `N = A` (since `A N − N²/2 = A²/2 − (N − A)²/2`). -/
theorem efficient_hours_iff {A N : ℝ} :
    (∀ N', A * N' - N' ^ 2 / 2 ≤ A * N - N ^ 2 / 2) ↔ N = A := by
  constructor
  · intro h
    have h1 := h A
    have h2 : (N - A) ^ 2 ≤ 0 := by nlinarith
    have : N - A = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (le_antisymm h2 (sq_nonneg _))
    linarith
  · intro hN N'
    rw [hN]
    nlinarith [sq_nonneg (N' - A)]

/-- Galí (2015), Exercise 6.4(a), p. 197: efficient output `Yᵉ = A · A` gives `yᵉ = 2a`. -/
theorem efficient_output_log {A : ℝ} (hA : 0 < A) : Real.log (A * A) = 2 * Real.log A := by
  rw [Real.log_mul hA.ne' hA.ne']
  ring

/-! ### (b) The wage schedule -/

/-- Galí (2015), Exercise 6.4(b), p. 197: the marginal utility of consumption is one. -/
theorem hasDerivAt_utility_C (C N : ℝ) : HasDerivAt (fun C' => C' - N ^ 2 / 2) 1 C := by
  exact (hasDerivAt_id' C).sub_const (N ^ 2 / 2)

/-- Galí (2015), Exercise 6.4(b), p. 197: the marginal disutility of hours is `N`, so the
marginal rate of substitution `−U_N/U_C` is `N`. -/
theorem hasDerivAt_utility_N (C N : ℝ) : HasDerivAt (fun N' => C - N' ^ 2 / 2) (-N) N := by
  have h := ((hasDerivAt_pow 2 N).div_const 2).const_sub C
  exact h.congr_deriv (by norm_num)

/-- Galí (2015), Exercise 6.4(b), p. 197: competitive labour supply `W/P = N` is exactly
`w − p = n` in logs. -/
theorem competitive_supply_log {W P N : ℝ} (hW : 0 < W) (hP : 0 < P) (hN : 0 < N) :
    W / P = N ↔ Real.log W - Real.log P = Real.log N := by
  rw [← Real.log_div hW.ne' hP.ne']
  constructor
  · intro h
    rw [h]
  · intro h
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr hN) h

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 6.4(b), p. 197: the wage schedule `w_t = p_t + n_t/(1 + δ)`. -/
def Schedule (δ : ℝ) (n w p : ℕ → Ω → ℝ) : Prop := ∀ t, w t = p t + (1 + δ)⁻¹ • n t

/-- Galí (2015), Exercise 6.4, p. 197: technology in logs, `y = a + n`. -/
def Tech (a n y : ℕ → Ω → ℝ) : Prop := ∀ t, y t = a t + n t

/-- Galí (2015), Exercise 6.4(b), p. 197: under the schedule the real wage is
`w − p = n/(1 + δ) = (y − a)/(1 + δ)`, against `w − p = n` with a competitive labour market. -/
theorem real_wage_schedule {δ : ℝ} {a n y w p : ℕ → Ω → ℝ} (hs : Schedule δ n w p)
    (ht : Tech a n y) (t : ℕ) :
    w t - p t = (1 + δ)⁻¹ • n t ∧ w t - p t = (1 + δ)⁻¹ • (y t - a t) := by
  have h1 : w t - p t = (1 + δ)⁻¹ • n t := by rw [hs t]; abel
  refine ⟨h1, ?_⟩
  rw [h1, ht t]
  abel_nf

/-- Galí (2015), Exercise 6.4(b), p. 197 (**real rigidity**): for `δ > 0` the response of the
real wage to employment, `1/(1 + δ)`, is below the competitive response `1`, so the real wage
moves strictly less than under competition whenever employment moves. -/
theorem real_rigidity {δ x : ℝ} (hδ : 0 < δ) (hx : x ≠ 0) :
    (1 + δ)⁻¹ < 1 ∧ |(1 + δ)⁻¹ * x| < |x| := by
  have h1 : (1 + δ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h0 : 0 < (1 + δ)⁻¹ := by positivity
  refine ⟨h1, ?_⟩
  rw [abs_mul, abs_of_pos h0]
  have := abs_pos.mpr hx
  nlinarith

/-! ### (c)–(d) The natural level of output and the markup gap -/

/-- Galí (2015), Exercise 6.4(c), p. 197: with `Y = A N`, the cost of output `Y` is
`W Y/A`, so nominal marginal cost is `W/A` (`mc = w − a` in logs). -/
theorem hasDerivAt_cost (W A Y : ℝ) : HasDerivAt (fun Y' => W * (Y' / A)) (W / A) Y := by
  have h := ((hasDerivAt_id' Y).div_const A).const_mul W
  exact h.congr_deriv (by ring)

/-- Galí (2015), Exercise 6.4, p. 197: the (log) average markup `μ_t = p_t − (w_t − a_t)`,
price over nominal marginal cost. -/
def markup (a w p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := p t - (w t - a t)

/-- Galí (2015), Exercise 6.4(c), p. 197: the natural level of output
`yⁿ_t = (2 + δ) a_t − (1 + δ) μ`. -/
def yn (δ μ : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (2 + δ) • a t - fun _ => (1 + δ) * μ

/-- Galí (2015), Exercise 6.4(a), p. 197: efficient output `yᵉ_t = 2 a_t`. -/
def ye (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (2 : ℝ) • a t

/-- Galí (2015), Exercise 6.4(c), p. 197: under the schedule, `μ_t = a_t − (y_t − a_t)/(1 + δ)`. -/
theorem markup_eq {δ : ℝ} {a n y w p : ℕ → Ω → ℝ} (hs : Schedule δ n w p) (ht : Tech a n y)
    (t : ℕ) : markup a w p t = a t - (1 + δ)⁻¹ • (y t - a t) := by
  unfold markup
  rw [hs t, ht t]
  abel_nf

/-- Galí (2015), Exercise 6.4(c), p. 197 (**necessary and sufficient**): the markup is at its
desired level `μ` iff output is at its natural level `yⁿ = (2 + δ) a − (1 + δ) μ`. -/
theorem natural_iff {δ μ : ℝ} (hδ : 1 + δ ≠ 0) {a n y w p : ℕ → Ω → ℝ} (hs : Schedule δ n w p)
    (ht : Tech a n y) (t : ℕ) : markup a w p t = (fun _ => μ) ↔ y t = yn δ μ a t := by
  rw [markup_eq hs ht t]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    unfold yn
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e
    linarith
  · intro h
    funext ω
    have e := congrFun h ω
    unfold yn at e
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    rw [e]
    field_simp
    ring

/-- Galí (2015), Exercise 6.4(d), p. 197: the markup gap is `μ̂_t = −(y_t − yⁿ_t)/(1 + δ)`. -/
theorem markup_gap {δ μ : ℝ} (hδ : 1 + δ ≠ 0) {a n y w p : ℕ → Ω → ℝ} (hs : Schedule δ n w p)
    (ht : Tech a n y) (t : ℕ) :
    markup a w p t - (fun _ => μ) = -((1 + δ)⁻¹ • (y t - yn δ μ a t)) := by
  rw [markup_eq hs ht t]
  funext ω
  unfold yn
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  field_simp
  ring

/-! ### (e) The inflation equation and the tradeoff -/

/-- Galí (2015), Exercise 6.4, p. 197: the Calvo inflation equation
`π_t = β E_t π_{t+1} − λ μ̂_t`. -/
def NKPCmu (β lam μ : ℝ) (a w p infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) - lam • (markup a w p t - fun _ => μ)

/-- Galí (2015), Exercise 6.4(e), p. 197: the inflation equation in the welfare-relevant gap,
`π_t = β E_t π_{t+1} + (λ/(1+δ))(y_t − yᵉ_t) + (λ/(1+δ))(yᵉ_t − yⁿ_t)`. -/
def NKPCgap (β lam δ μ : ℝ) (a y infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + (lam / (1 + δ)) • (y t - ye a t) +
    (lam / (1 + δ)) • (ye a t - yn δ μ a t)

/-- Galí (2015), Exercise 6.4(e), p. 197 (**equivalence**): under the wage schedule the Calvo
equation is the inflation equation in the welfare-relevant output gap. -/
theorem nkpc_iff {β lam δ μ : ℝ} (hδ : 1 + δ ≠ 0) {a n y w p infl : ℕ → Ω → ℝ}
    (hs : Schedule δ n w p) (ht : Tech a n y) :
    NKPCmu 𝔼 β lam μ a w p infl ↔ NKPCgap 𝔼 β lam δ μ a y infl := by
  refine forall_congr' fun t => ?_
  rw [markup_gap hδ hs ht t]
  have e : -(lam • -((1 + δ)⁻¹ • (y t - yn δ μ a t))) =
      (lam / (1 + δ)) • (y t - ye a t) + (lam / (1 + δ)) • (ye a t - yn δ μ a t) := by
    funext ω
    unfold ye yn
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply]
    field_simp
    ring
  rw [sub_eq_add_neg, e, add_assoc]

/-- Galí (2015), Exercise 6.4(e), p. 197: the cost-push term is
`yᵉ_t − yⁿ_t = −δ a_t + (1 + δ) μ`. -/
theorem cost_push (δ μ : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) :
    ye a t - yn δ μ a t = (-δ) • a t + fun _ => (1 + δ) * μ := by
  funext ω
  unfold ye yn
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), Exercise 6.4(e), p. 197 (**no tradeoff iff no cost push**): for `λ ≠ 0`,
`1 + δ ≠ 0`, zero inflation together with `y = yᵉ` satisfies the inflation equation iff
`yᵉ − yⁿ ≡ 0`. -/
theorem divine_iff {β lam δ μ : ℝ} (hlam : lam ≠ 0) (hδ : 1 + δ ≠ 0) {a : ℕ → Ω → ℝ} :
    NKPCgap 𝔼 β lam δ μ a (ye a) 0 ↔ ∀ t, ye a t - yn δ μ a t = 0 := by
  have hc : lam / (1 + δ) ≠ 0 := div_ne_zero hlam hδ
  refine forall_congr' fun t => ?_
  simp only [Pi.zero_apply, map_zero, smul_zero, sub_self, zero_add]
  constructor
  · intro h
    exact (smul_eq_zero.mp h.symm).resolve_left hc
  · intro h
    rw [h, smul_zero]

/-- Galí (2015), Exercise 6.4(e), p. 197: with `μ = 0`, zero inflation and `y = yᵉ` are
jointly attainable iff `δ a_t = 0` at every date. -/
theorem divine_iff_mu0 {β lam δ : ℝ} (hlam : lam ≠ 0) (hδ : 1 + δ ≠ 0) {a : ℕ → Ω → ℝ} :
    NKPCgap 𝔼 β lam δ 0 a (ye a) 0 ↔ ∀ t, δ • a t = 0 := by
  rw [divine_iff 𝔼 hlam hδ]
  refine forall_congr' fun t => ?_
  rw [cost_push]
  simp only [mul_zero]
  constructor
  · intro h
    have : (-δ) • a t = 0 := by
      rw [← add_zero ((-δ) • a t)]
      exact h
    rwa [neg_smul, neg_eq_zero] at this
  · intro h
    rw [neg_smul, h, neg_zero, zero_add]
    rfl

/-- Galí (2015), Exercise 6.4(e), p. 198 (**the tradeoff**): with `μ = 0`, `λ ≠ 0`,
`1 + δ ≠ 0` and productivity not identically zero, zero inflation and a zero welfare-relevant
gap are jointly attainable iff `δ = 0`; real wage rigidity `δ > 0` creates a tradeoff. -/
theorem tradeoff_iff_delta {β lam δ : ℝ} (hlam : lam ≠ 0) (hδ : 1 + δ ≠ 0) {a : ℕ → Ω → ℝ}
    (ha : ∃ t ω, a t ω ≠ 0) : NKPCgap 𝔼 β lam δ 0 a (ye a) 0 ↔ δ = 0 := by
  rw [divine_iff_mu0 𝔼 hlam hδ]
  constructor
  · intro h
    obtain ⟨t, ω, hne⟩ := ha
    have := congrFun (h t) ω
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_right hne
  · intro h t
    rw [h, zero_smul]

/-- Galí (2015), Exercise 6.4(e), p. 198: fully stabilising inflation (`π ≡ 0`) forces the
welfare-relevant gap `y_t − yᵉ_t = −(yᵉ_t − yⁿ_t) = δ a_t − (1 + δ) μ`. -/
theorem strict_inflation_gap {β lam δ μ : ℝ} (hlam : lam ≠ 0) (hδ : 1 + δ ≠ 0)
    {a y : ℕ → Ω → ℝ} (h : NKPCgap 𝔼 β lam δ μ a y 0) (t : ℕ) :
    y t - ye a t = δ • a t - fun _ => (1 + δ) * μ := by
  have hc : lam / (1 + δ) ≠ 0 := div_ne_zero hlam hδ
  have e := h t
  simp only [Pi.zero_apply, map_zero, smul_zero, zero_add] at e
  rw [← smul_add] at e
  have e2 := (smul_eq_zero.mp e.symm).resolve_left hc
  rw [cost_push] at e2
  funext ω
  have e3 := congrFun e2 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e3 ⊢
  linarith

/-! ### (f) Optimal discretionary policy with i.i.d. productivity -/

/-- Galí (2015), Exercise 6.4(f), p. 198: the period objective after substituting the
constraint `π = κ x + υ`: `(κ x + υ)² + α_y x²` (restated from the Chapter 5 project). -/
def periodObj (κ αy υ x : ℝ) : ℝ := (κ * x + υ) ^ 2 + αy * x ^ 2

/-- Galí (2015), Exercise 6.4(f), p. 198 (completing the square; restated from the Chapter 5
project). -/
theorem periodObj_sub (κ αy υ x x' : ℝ) :
    periodObj κ αy υ x' - periodObj κ αy υ x
      = (κ ^ 2 + αy) * (x' - x) ^ 2 + 2 * (x' - x) * ((κ ^ 2 + αy) * x + κ * υ) := by
  unfold periodObj
  ring

/-- Galí (2015), Exercise 6.4(f), p. 198 (**necessary and sufficient**; restated from the
Chapter 5 project): for `α_y > 0`, `x` minimises the period objective iff
`x = −(κ/α_y)(κ x + υ)`. -/
theorem periodObj_isMinOn_iff {κ αy υ x : ℝ} (hαy : 0 < αy) :
    IsMinOn (periodObj κ αy υ) Set.univ x ↔ x = -(κ / αy) * (κ * x + υ) := by
  have hA : 0 < κ ^ 2 + αy := by positivity
  have hfoc : x = -(κ / αy) * (κ * x + υ) ↔ (κ ^ 2 + αy) * x + κ * υ = 0 := by
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
    set g := (κ ^ 2 + αy) * x + κ * υ
    have hle := h (Set.mem_univ (x - g / (κ ^ 2 + αy)))
    simp only [Set.mem_ofPred_eq] at hle
    have hd := periodObj_sub κ αy υ x (x - g / (κ ^ 2 + αy))
    have hval : (κ ^ 2 + αy) * (x - g / (κ ^ 2 + αy) - x) ^ 2 +
        2 * (x - g / (κ ^ 2 + αy) - x) * g = -(g ^ 2 / (κ ^ 2 + αy)) := by
      field_simp
      ring
    have hg2 : g ^ 2 / (κ ^ 2 + αy) ≤ 0 := by linarith
    have : g ^ 2 ≤ 0 := by
      rwa [div_le_iff₀ hA, zero_mul] at hg2
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg g))
  · intro h x' _
    have hd := periodObj_sub κ αy υ x x'
    rw [h, mul_zero, add_zero] at hd
    have : 0 ≤ (κ ^ 2 + αy) * (x' - x) ^ 2 := by positivity
    simp only [Set.mem_ofPred_eq]
    linarith

/-- Galí (2015), Exercise 6.4(f), p. 198 (**the period problem, necessary and sufficient**;
restated from the Chapter 5 project): for `α_y > 0`, `(π, x)` minimises `π² + α_y x²` subject
to `π = κ x + υ` iff it is feasible and `x = −(κ/α_y) π`. -/
theorem period_problem_iff {κ αy υ π x : ℝ} (hαy : 0 < αy) :
    (π = κ * x + υ ∧ ∀ π' x', π' = κ * x' + υ → π ^ 2 + αy * x ^ 2 ≤ π' ^ 2 + αy * x' ^ 2) ↔
      (π = κ * x + υ ∧ x = -(κ / αy) * π) := by
  constructor
  · rintro ⟨hc, hmin⟩
    refine ⟨hc, ?_⟩
    have : IsMinOn (periodObj κ αy υ) Set.univ x := fun x' _ => by
      have := hmin _ x' rfl
      rw [hc] at this
      simpa [periodObj] using this
    rw [hc]
    exact (periodObj_isMinOn_iff hαy).mp this
  · rintro ⟨hc, hx⟩
    refine ⟨hc, fun π' x' hc' => ?_⟩
    rw [hc] at hx
    have := (periodObj_isMinOn_iff hαy).mpr hx (Set.mem_univ x')
    simp only [Set.mem_ofPred_eq, periodObj] at this
    rw [hc, hc']
    exact this

/-- Galí (2015), Exercise 6.4(e)–(f), pp. 197–198: the inflation equation in the gap
`x = y − yᵉ` with slope `κ = λ/(1 + δ)` and cost push `κ g`, `g = yᵉ − yⁿ`. -/
def NKPCx (β κ : ℝ) (g x infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + κ • g t

/-- Galí (2015), Exercise 6.4(f), p. 198: a **discretionary equilibrium** for the loss
`E_0 ∑ βᵗ [α_y (y_t − yᵉ_t)² + π_t²]` (the book's undefined `y*_t` read as `yᵉ_t`): the
inflation equation holds and, date by date and state by state, `(π_t, x_t)` minimises
`π² + α_y x²` on `π = κ x + υ_t`, taking `υ_t = β E_t π_{t+1} + κ g_t` as given. -/
def DiscretionEq (β κ αy : ℝ) (g x infl : ℕ → Ω → ℝ) : Prop :=
  NKPCx 𝔼 β κ g x infl ∧ ∀ t ω, ∀ π' x' : ℝ,
    π' = κ * x' + (β * 𝔼.E t (infl (t + 1)) ω + κ * g t ω) →
      infl t ω ^ 2 + αy * x t ω ^ 2 ≤ π' ^ 2 + αy * x' ^ 2

/-- Galí (2015), Exercise 6.4(f), p. 198: for `α_y > 0` a discretionary equilibrium is exactly
the inflation equation plus the targeting rule `x_t = −(κ/α_y) π_t`. -/
theorem discretionEq_iff {β κ αy : ℝ} (hαy : 0 < αy) {g x infl : ℕ → Ω → ℝ} :
    DiscretionEq 𝔼 β κ αy g x infl ↔
      NKPCx 𝔼 β κ g x infl ∧ ∀ t, x t = (-(κ / αy)) • infl t := by
  have hpt : ∀ (_ : NKPCx 𝔼 β κ g x infl) t ω,
      infl t ω = κ * x t ω + (β * 𝔼.E t (infl (t + 1)) ω + κ * g t ω) := fun h t ω => by
    have := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  constructor
  · rintro ⟨h, hmin⟩
    refine ⟨h, fun t => funext fun ω => ?_⟩
    have := ((period_problem_iff hαy).mp ⟨hpt h t ω, hmin t ω⟩).2
    simpa using this
  · rintro ⟨h, hr⟩
    refine ⟨h, fun t ω => ((period_problem_iff hαy).mpr ⟨hpt h t ω, ?_⟩).2⟩
    have := congrFun (hr t) ω
    simpa using this

/-- Galí (2015), Exercise 6.4(f), p. 198: with `μ = 0` the cost-push term is `g = −δ a`. -/
theorem cost_push_mu0 (δ : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : ye a t - yn δ 0 a t = (-δ) • a t := by
  rw [cost_push, mul_zero]
  funext ω
  simp

/-- Galí (2015), Exercise 6.4(f), p. 198 (**existence and uniqueness**): with `α_y > 0`,
`0 ≤ β < 1`, `μ = 0` (cost push `g = −δ a`) and i.i.d. bounded productivity
(`E_t a_{t+1} = 0`), a bounded `(x, π)` is a discretionary equilibrium iff
`π_t = −α_y κ δ a_t/(α_y + κ²)` and `x_t = κ² δ a_t/(α_y + κ²)`. -/
theorem discretion_iid_iff {β κ αy δ : ℝ} (hαy : 0 < αy) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {a x infl : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 0 a) (hab : BoundedProc a) (hpb : BoundedProc infl) :
    DiscretionEq 𝔼 β κ αy (fun t => (-δ) • a t) x infl ↔
      ∀ t, infl t = (-(αy * κ * δ / (αy + κ ^ 2))) • a t ∧
        x t = (κ ^ 2 * δ / (αy + κ ^ 2)) • a t := by
  have hA : 0 < αy + κ ^ 2 := by positivity
  have hEa : ∀ t, 𝔼.E t (a (t + 1)) = 0 := fun t => by rw [ha.2 t, zero_smul]
  rw [discretionEq_iff 𝔼 hαy]
  set c := -(αy * κ * δ / (αy + κ ^ 2)) with hc
  constructor
  · rintro ⟨h, hr⟩
    -- the forward equation for inflation
    have hf : ∀ t, infl t = (αy * β / (αy + κ ^ 2)) • 𝔼.E t (infl (t + 1)) +
        (αy * κ / (αy + κ ^ 2)) • (-δ • a t) := by
      intro t
      funext ω
      have p := congrFun (h t) ω
      have r := congrFun (hr t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at p r ⊢
      rw [r] at p
      field_simp
      field_simp at p
      linarith
    have hs : ∀ t, c • a t = (αy * β / (αy + κ ^ 2)) • 𝔼.E t (c • a (t + 1)) +
        (αy * κ / (αy + κ ^ 2)) • (-δ • a t) := by
      intro t
      rw [map_smul, hEa t, smul_zero, smul_zero, zero_add, smul_smul, hc]
      congr 1
      field_simp
    have habs : |αy * β / (αy + κ ^ 2)| < 1 := by
      rw [abs_of_nonneg (by positivity), div_lt_one hA]
      nlinarith [sq_nonneg κ]
    have hcb : BoundedProc fun t => c • a t := by
      obtain ⟨B, hB⟩ := hab
      refine ⟨|c| * B, fun t ω => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)
    have heq : infl = fun t => c • a t := 𝔼.forward_unique habs hf hs hpb hcb
    intro t
    have hi : infl t = c • a t := by rw [heq]
    refine ⟨hi, ?_⟩
    rw [hr t, hi, smul_smul, hc]
    congr 1
    field_simp
  · intro h
    have hi : ∀ t, infl t = c • a t := fun t => (h t).1
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [hi (t + 1), map_smul, hEa t, smul_zero, smul_zero, zero_add, hi t, (h t).2]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc]
      field_simp
      ring
    · rw [(h t).2, hi t, smul_smul, hc]
      congr 1
      field_simp

/-- Galí (2015), Exercise 6.4(f), p. 198: in the discretionary equilibrium output is
`y_t = yᵉ_t + x_t = (2 + κ² δ/(α_y + κ²)) a_t` (and employment `n = y − a`). -/
theorem discretion_output {β κ αy δ : ℝ} (hαy : 0 < αy) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {a y infl : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 0 a) (hab : BoundedProc a) (hpb : BoundedProc infl) :
    DiscretionEq 𝔼 β κ αy (fun t => (-δ) • a t) (fun t => y t - ye a t) infl ↔
      ∀ t, infl t = (-(αy * κ * δ / (αy + κ ^ 2))) • a t ∧
        y t = (2 + κ ^ 2 * δ / (αy + κ ^ 2)) • a t := by
  rw [discretion_iid_iff 𝔼 hαy hβ0 hβ1 ha hab hpb]
  refine forall_congr' fun t => and_congr_right fun _ => ?_
  unfold ye
  rw [add_smul, sub_eq_iff_eq_add]
  constructor
  · intro h
    rw [h, add_comm]
  · intro h
    rw [h, add_comm]

/-- Galí (2015), Exercise 6.4(f), p. 198 (**perfect competition in the labour market**,
`δ = 0`): the unique bounded discretionary equilibrium has `π ≡ 0` and `y = yᵉ = 2a`; there is
no tradeoff. -/
theorem perfect_competition {β κ αy : ℝ} (hαy : 0 < αy) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {a y infl : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 0 a) (hab : BoundedProc a) (hpb : BoundedProc infl) :
    DiscretionEq 𝔼 β κ αy (fun t => (-(0 : ℝ)) • a t) (fun t => y t - ye a t) infl ↔
      ∀ t, infl t = 0 ∧ y t = ye a t := by
  rw [discretion_output 𝔼 hαy hβ0 hβ1 ha hab hpb]
  simp only [mul_zero, zero_div, neg_zero, zero_smul, add_zero]
  rfl

end Gali.StickyWagesPrices.Ex6_4
