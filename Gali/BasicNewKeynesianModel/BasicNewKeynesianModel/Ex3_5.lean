/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.Expectations
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.BigOperators.Field

/-!
# Exercise 3.5: optimal price setting and dynamics in the Taylor model

Galí (2015), Chapter 3, Exercise 3.5, pp. 92–93. Each period a fraction `1/N`
of firms sets a price that stays fixed for `N` periods (Taylor 1980).

* (a) `hasDerivAt_objective`, `foc_of_isLocalMax`: the first-order condition of
  the price setter, derived as an exact derivative of the `N`-period objective.
  `isMaxOn_iff_foc`: the condition is also sufficient, and it has a unique
  root, the global maximiser. The condition as printed in the book omits the
  factor `1/P_{t+k}` of the objective; `printed_foc_counterexample` shows that
  the printed condition fails at the true optimum.
* (b) `hasDerivAt_focLHS_path`, `pricing_rule_iff`: the exact linearisation of
  the first-order condition at the zero-inflation steady state gives
  `p*_t = μ + ∑ₖ ωₖ E_t ψ_{t+k}`, with weights `ωₖ = βᵏ(1−β)/(1−β^N)`
  (`taylorWeight_eq`) that sum to one (`sum_taylorWeight`) and tend to `1/N`
  as `β → 1` (`tendsto_taylorWeight`).
* (c) `hasDerivAt_log_priceIndex`: `p_t = N⁻¹ ∑ₖ p*_{t−k}` to first order.
* (d) `taylor_two_period_rule`: with `N = 2` and `β = 1`,
  `p*_t = ½ p*_{t−1} + ½ E_t p*_{t+1} + δ (ỹ_t + E_t ỹ_{t+1})`, `δ = σ + φ`.
* (e) `gap_equation`, `taylor_equilibrium`: with random-walk money and
  technology, the reset price relative to `m − yⁿ` follows an AR(1) with the
  stable root `λ = (1 − √δ)/(1 + √δ)` of a quadratic; this is the unique
  bounded solution (one predetermined variable, general lemmas
  `predetermined_solves`, `predetermined_unique`). Closed forms for the output
  gap, output, employment and the price level: `taylor_gap_closed`,
  `taylor_model_closed_form`.
* (f) `taylorRoot_strictAntiOn`: persistence `λ` is strictly *decreasing* in
  `δ`; `λ → 1` as `δ → 0` and `λ < 0` (oscillation) for `δ > 1`.

Dates are natural numbers, so equations with a lag are stated at date `t + 1`.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_5

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (a) The first-order condition -/

/-- The desired gross markup `M = ε/(ε − 1)` (Galí (2015), Ex. 3.5(a), p. 92). -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- The log desired markup `μ = log M` (Galí (2015), Ex. 3.5(b), p. 93). -/
noncomputable def logMarkup (ε : ℝ) : ℝ := Real.log (markup ε)

/-- The desired markup is positive for `ε > 1` (Galí (2015), p. 92). -/
theorem markup_pos {ε : ℝ} (hε : 1 < ε) : 0 < markup ε :=
  div_pos (by linarith) (by linarith)

/-- `(1 − ε) M = −ε` (Galí (2015), p. 92). -/
theorem one_sub_mul_markup {ε : ℝ} (hε : 1 < ε) : (1 - ε) * markup ε = -ε := by
  unfold markup
  have : ε - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Demand for a good priced at `P*`, `Y_{t+k|t} = (P*/P_{t+k})^{−ε} C_{t+k}`
(Galí (2015), Ex. 3.5, p. 92), as a random variable. -/
noncomputable def demand (ε x : ℝ) (P C : Ω → ℝ) : Ω → ℝ :=
  fun ω => (x / P ω) ^ (-ε) * C ω

/-- With technology `Y = A N` and a competitive wage `W`, the nominal cost of
producing `Y` is `W (Y/A)` (Galí (2015), Ex. 3.5, p. 92). -/
noncomputable def cost (W A Y : ℝ) : ℝ := W * (Y / A)

/-- The nominal marginal cost is `Ψ = W/A`, independent of the firm's output
(Galí (2015), Ex. 3.5(a), p. 92), and the cost is `Ψ Y`. -/
theorem cost_eq_and_hasDerivAt (W A Y : ℝ) :
    cost W A Y = W / A * Y ∧ HasDerivAt (fun Y' => cost W A Y') (W / A) Y := by
  refine ⟨by unfold cost; ring, ?_⟩
  have h := ((hasDerivAt_id Y).div_const A).const_mul W
  refine h.congr_deriv ?_
  simp [div_eq_mul_inv]

/-- Real profits at horizon `k` of a firm that set the price `x` at date `t`,
`Λ_{t,t+k} (1/P_{t+k}) (x Y_{t+k|t} − Ψ_{t+k} Y_{t+k|t})` (Galí (2015),
Ex. 3.5, p. 92), with the linear cost of `cost_eq_and_hasDerivAt`. -/
noncomputable def profit (ε : ℝ) (Λ P C Ψ : Ω → ℝ) (x : ℝ) : Ω → ℝ :=
  fun ω => Λ ω / P ω * (x * demand ε x P C ω - Ψ ω * demand ε x P C ω)

/-- **The Taylor price setter's objective** (Galí (2015), Ex. 3.5, p. 92):
`∑_{k<N} E_t[Λ_{t,t+k}(1/P_{t+k})(P* Y_{t+k|t} − C_{t+k}(Y_{t+k|t}))]`. The
horizon-`k` variables `Λ k, P k, C k, Ψ k` are the date-`t+k` values. -/
noncomputable def objective (N : ℕ) (ε : ℝ) (Λ P C Ψ : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) :
    Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.range N, 𝔼.E t (profit ε (Λ k) (P k) (C k) (Ψ k) x) ω

/-- The summand of the first-order condition,
`Λ_{t,t+k} (1/P_{t+k}) Y_{t+k|t} (P* − M Ψ_{t+k})` (Galí (2015), Ex. 3.5(a)). -/
noncomputable def focTerm (ε : ℝ) (Λ P C Ψ : Ω → ℝ) (x : ℝ) : Ω → ℝ :=
  fun ω => Λ ω / P ω * demand ε x P C ω * (x - markup ε * Ψ ω)

/-- The left-hand side of the first-order condition (Galí (2015), Ex. 3.5(a)):
`∑_{k<N} E_t[Λ_{t,t+k} (1/P_{t+k}) Y_{t+k|t} (P* − M Ψ_{t+k})]`. -/
noncomputable def focSum (N : ℕ) (ε : ℝ) (Λ P C Ψ : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) : Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.range N, 𝔼.E t (focTerm ε (Λ k) (P k) (C k) (Ψ k) x) ω

/-- The demand weight `Λ P^{ε−1} C`, so that `Λ (1/P) Y = x^{−ε} · Λ P^{ε−1} C`
(Galí (2015), Ex. 3.5, p. 92). -/
noncomputable def wgt (ε : ℝ) (Λ P C : Ω → ℝ) : Ω → ℝ :=
  fun ω => Λ ω / P ω * (P ω ^ ε * C ω)

/-- Demand factorises as `x^{−ε} P^ε C` (Galí (2015), Ex. 3.5, p. 92). -/
theorem demand_eq {ε x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    demand ε x P C ω = x ^ (-ε) * (P ω ^ ε * C ω) := by
  unfold demand
  rw [Real.div_rpow hx.le (hP ω).le, Real.rpow_neg (hP ω).le ε, div_inv_eq_mul]
  ring

/-- Expected profits in closed form: `E_t[profit] = x^{−ε} x E_t[w] − x^{−ε} E_t[w Ψ]`
for the weight `w = Λ P^{ε−1} C` (Galí (2015), Ex. 3.5, p. 92). -/
theorem E_profit_eq {ε x : ℝ} (hx : 0 < x) {Λ P C Ψ : Ω → ℝ} (hP : ∀ ω, 0 < P ω)
    (t : ℕ) (ω : Ω) :
    𝔼.E t (profit ε Λ P C Ψ x) ω
      = x ^ (-ε) * x * 𝔼.E t (wgt ε Λ P C) ω - x ^ (-ε) * 𝔼.E t (wgt ε Λ P C * Ψ) ω := by
  have h : profit ε Λ P C Ψ x
      = (x ^ (-ε) * x) • wgt ε Λ P C - x ^ (-ε) • (wgt ε Λ P C * Ψ) := by
    funext ω'
    simp only [profit, wgt, demand_eq hx hP, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
      smul_eq_mul]
    ring
  rw [h, map_sub, map_smul, map_smul]
  rfl

/-- The first-order term in closed form:
`E_t[focTerm] = x^{−ε} x E_t[w] − x^{−ε} M E_t[w Ψ]` (Galí (2015), Ex. 3.5(a)). -/
theorem E_focTerm_eq {ε x : ℝ} (hx : 0 < x) {Λ P C Ψ : Ω → ℝ} (hP : ∀ ω, 0 < P ω)
    (t : ℕ) (ω : Ω) :
    𝔼.E t (focTerm ε Λ P C Ψ x) ω = x ^ (-ε) * x * 𝔼.E t (wgt ε Λ P C) ω
      - x ^ (-ε) * markup ε * 𝔼.E t (wgt ε Λ P C * Ψ) ω := by
  have h : focTerm ε Λ P C Ψ x
      = (x ^ (-ε) * x) • wgt ε Λ P C - (x ^ (-ε) * markup ε) • (wgt ε Λ P C * Ψ) := by
    funext ω'
    simp only [focTerm, wgt, demand_eq hx hP, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
      smul_eq_mul]
    ring
  rw [h, map_sub, map_smul, map_smul]
  rfl

/-- The derivative of `z ↦ z^{−ε} z a − z^{−ε} b` at `x > 0` equals
`((1 − ε)/x)(x^{−ε} x a − x^{−ε} M b)` (Galí (2015), Ex. 3.5(a)). -/
theorem hasDerivAt_closedForm {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x) (a b : ℝ) :
    HasDerivAt (fun z => z ^ (-ε) * z * a - z ^ (-ε) * b)
      ((1 - ε) / x * (x ^ (-ε) * x * a - x ^ (-ε) * markup ε * b)) x := by
  have hr := Real.hasDerivAt_rpow_const (p := -ε) (Or.inl hx.ne')
  have h := HasDerivAt.sub (((hr.mul (hasDerivAt_id x)).mul_const a)) (hr.mul_const b)
  refine h.congr_deriv ?_
  rw [Real.rpow_sub_one hx.ne']
  unfold markup
  have h1 : ε - 1 ≠ 0 := by linarith
  have h2 : x ≠ 0 := hx.ne'
  simp only [id]
  field_simp
  ring

/-- **The derivative of the Taylor objective** (Galí (2015), Ex. 3.5(a), p. 92):
at every price `x > 0`, the objective has derivative
`((1 − ε)/x) ∑_{k<N} E_t[Λ_{t,t+k}(1/P_{t+k}) Y_{t+k|t}(x − M Ψ_{t+k})]`. -/
theorem hasDerivAt_objective {N : ℕ} {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x)
    {Λ P C Ψ : ℕ → Ω → ℝ} (hP : ∀ k ω, 0 < P k ω) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => objective 𝔼 N ε Λ P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 N ε Λ P C Ψ t x ω) x := by
  unfold objective focSum
  rw [Finset.mul_sum]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := hasDerivAt_closedForm hε hx (𝔼.E t (wgt ε (Λ k) (P k) (C k)) ω)
    (𝔼.E t (wgt ε (Λ k) (P k) (C k) * Ψ k) ω)
  rw [E_focTerm_eq 𝔼 hx (hP k)]
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hx] with z hz
  exact E_profit_eq 𝔼 hz (hP k) t ω

/-- **The first-order condition is necessary** (Galí (2015), Ex. 3.5(a), p. 92):
a locally optimal reset price `P* > 0` satisfies
`∑_{k<N} E_t[Λ_{t,t+k}(1/P_{t+k}) Y_{t+k|t}(P* − M Ψ_{t+k})] = 0`. -/
theorem foc_of_isLocalMax {N : ℕ} {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x)
    {Λ P C Ψ : ℕ → Ω → ℝ} (hP : ∀ k ω, 0 < P k ω) {t : ℕ} {ω : Ω}
    (hmax : IsLocalMax (fun z => objective 𝔼 N ε Λ P C Ψ t z ω) x) :
    focSum 𝔼 N ε Λ P C Ψ t x ω = 0 := by
  have h := hmax.hasDerivAt_eq_zero (hasDerivAt_objective 𝔼 hε hx hP t ω)
  have hc : (1 - ε) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  exact (mul_eq_zero.mp h).resolve_left hc

/-- The objective in closed form: `x^{−ε} x A − x^{−ε} B` with
`A = ∑ E_t[wₖ]`, `B = ∑ E_t[wₖ Ψₖ]` (Galí (2015), Ex. 3.5(a)). -/
theorem objective_eq {N : ℕ} {ε x : ℝ} (hx : 0 < x) {Λ P C Ψ : ℕ → Ω → ℝ}
    (hP : ∀ k ω, 0 < P k ω) (t : ℕ) (ω : Ω) :
    objective 𝔼 N ε Λ P C Ψ t x ω
      = x ^ (-ε) * x * (∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k)) ω)
        - x ^ (-ε) * (∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k) * Ψ k) ω) := by
  unfold objective
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => E_profit_eq 𝔼 hx (hP k) t ω

/-- The first-order sum in closed form: `x^{−ε}(x A − M B)` (Galí (2015), Ex. 3.5(a)). -/
theorem focSum_eq {N : ℕ} {ε x : ℝ} (hx : 0 < x) {Λ P C Ψ : ℕ → Ω → ℝ}
    (hP : ∀ k ω, 0 < P k ω) (t : ℕ) (ω : Ω) :
    focSum 𝔼 N ε Λ P C Ψ t x ω
      = x ^ (-ε) * (x * (∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k)) ω)
        - markup ε * (∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k) * Ψ k) ω)) := by
  unfold focSum
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [E_focTerm_eq 𝔼 hx (hP k) t ω]
  ring

/-- **The first-order condition is also sufficient, and has a unique root**
(Galí (2015), Ex. 3.5(a), p. 92). If the expected demand weights and the
expected weighted marginal costs are positive, then a price `x > 0` maximises
the objective over all positive prices if and only if it satisfies the
first-order condition. The proof is Bernoulli's inequality
`u^ε ≥ 1 + ε (u − 1)`. -/
theorem isMaxOn_iff_foc {N : ℕ} {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x)
    {Λ P C Ψ : ℕ → Ω → ℝ} (hP : ∀ k ω, 0 < P k ω) {t : ℕ} {ω : Ω}
    (hA : 0 < ∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k)) ω)
    (hB : 0 < ∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k) * Ψ k) ω) :
    IsMaxOn (fun z => objective 𝔼 N ε Λ P C Ψ t z ω) (Set.Ioi 0) x ↔
      focSum 𝔼 N ε Λ P C Ψ t x ω = 0 := by
  set A := ∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k)) ω with hAdef
  set B := ∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k) * Ψ k) ω with hBdef
  have hM := markup_pos hε
  set xs := markup ε * B / A with hxs
  have hxs0 : 0 < xs := by positivity
  -- the objective at `xs u`, relative to its value at `xs`
  have key : ∀ u, 0 < u → objective 𝔼 N ε Λ P C Ψ t (xs * u) ω
      = xs ^ (-ε) * xs * A * (u ^ (-ε) * (u - (ε - 1) / ε)) := by
    intro u hu
    rw [objective_eq 𝔼 (by positivity) hP, Real.mul_rpow hxs0.le hu.le]
    have hB' : B = xs * A * ((ε - 1) / ε) := by
      rw [hxs]; unfold markup
      have : ε - 1 ≠ 0 := by linarith
      have : ε ≠ 0 := by linarith
      field_simp
    rw [← hAdef, ← hBdef, hB']
    ring
  have hbern : ∀ u, 0 < u → u ^ (-ε) * (u - (ε - 1) / ε) ≤ 1 / ε := by
    intro u hu
    have hb := one_add_mul_self_le_rpow_one_add (s := u - 1) (by linarith) hε.le
    rw [add_sub_cancel] at hb
    have hue : 0 < u ^ ε := Real.rpow_pos_of_pos hu ε
    rw [Real.rpow_neg hu.le, ← div_eq_inv_mul, div_le_div_iff₀ hue (by linarith)]
    have hε0 : 0 < ε := by linarith
    rw [div_eq_mul_inv]
    have : (u - (ε - 1) * ε⁻¹) * ε = ε * u - (ε - 1) := by field_simp
    nlinarith [this]
  have hbern' : ∀ u, 0 < u → u ≠ 1 → u ^ (-ε) * (u - (ε - 1) / ε) < 1 / ε := by
    intro u hu hu1
    have hb := one_add_mul_self_lt_rpow_one_add (s := u - 1) (by linarith)
      (sub_ne_zero.mpr hu1) hε
    rw [add_sub_cancel] at hb
    have hue : 0 < u ^ ε := Real.rpow_pos_of_pos hu ε
    rw [Real.rpow_neg hu.le, ← div_eq_inv_mul, div_lt_div_iff₀ hue (by linarith)]
    have : (u - (ε - 1) / ε) * ε = ε * u - (ε - 1) := by field_simp
    nlinarith [this]
  have hfoc : focSum 𝔼 N ε Λ P C Ψ t x ω = 0 ↔ x = xs := by
    rw [focSum_eq 𝔼 hx hP, ← hAdef, ← hBdef]
    have hxe : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hx _
    constructor
    · intro h
      have := (mul_eq_zero.mp h).resolve_left hxe.ne'
      rw [hxs]; field_simp; linarith
    · intro h
      rw [h, hxs]; field_simp; ring
  rw [hfoc]
  have hc0 : 0 < xs ^ (-ε) * xs * A := by positivity
  have hval1 : objective 𝔼 N ε Λ P C Ψ t xs ω = xs ^ (-ε) * xs * A * (1 / ε) := by
    have := key 1 one_pos
    rw [mul_one] at this
    rw [this, Real.one_rpow, one_mul]
    have : ε ≠ 0 := by linarith
    field_simp
    ring
  constructor
  · intro hmax
    by_contra hne
    have hu : 0 < x / xs := div_pos hx hxs0
    have hu1 : x / xs ≠ 1 := fun h => hne ((div_eq_one_iff_eq hxs0.ne').mp h)
    have h1 := hmax (Set.mem_Ioi.mpr hxs0)
    have h2 := key (x / xs) hu
    rw [mul_div_cancel₀ x hxs0.ne'] at h2
    change objective 𝔼 N ε Λ P C Ψ t xs ω ≤ objective 𝔼 N ε Λ P C Ψ t x ω at h1
    rw [h2, hval1] at h1
    have := hbern' _ hu hu1
    nlinarith
  · intro h z hz
    rw [h]
    have hz0 : 0 < z := hz
    have h2 := key (z / xs) (div_pos hz0 hxs0)
    rw [mul_div_cancel₀ z hxs0.ne'] at h2
    change objective 𝔼 N ε Λ P C Ψ t z ω ≤ objective 𝔼 N ε Λ P C Ψ t xs ω
    rw [h2, hval1]
    exact mul_le_mul_of_nonneg_left (hbern _ (div_pos hz0 hxs0)) hc0.le

/-- The first-order condition **as printed** (Galí (2015), Ex. 3.5(a), p. 92):
`∑_{k<N} E_t[Λ_{t,t+k} Y_{t+k|t}(P* − M Ψ_{t+k})] = 0`, without the factor
`1/P_{t+k}` that the objective carries. -/
noncomputable def printedFocSum (N : ℕ) (ε : ℝ) (Λ P C Ψ : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) :
    Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.range N,
    𝔼.E t (fun ω' => Λ k ω' * demand ε x (P k) (C k) ω' * (x - markup ε * Ψ k ω')) ω

/-- **The printed condition is not the first-order condition** (Galí (2015),
Ex. 3.5(a), p. 92). Under perfect foresight with `N = 2`, `ε = 2`, `Λ ≡ 1`,
`C ≡ 1`, `P = (1, 2)` and `Ψ = (1, 2)`, the objective is maximised at
`P* = 10/3`, where the correct condition holds but the printed one does not
(it would give `P* = 18/5`). The two conditions agree to first order around a
zero-inflation steady state (`hasDerivAt_focLHS_path` allows any weights). -/
theorem printed_foc_counterexample :
    let P : ℕ → Unit → ℝ := fun k _ => (k : ℝ) + 1
    let Ψ : ℕ → Unit → ℝ := fun k _ => (k : ℝ) + 1
    IsMaxOn (fun z => objective perfectForesight 2 2 (fun _ _ => 1) P (fun _ _ => 1) Ψ 0 z ())
        (Set.Ioi 0) (10 / 3) ∧
      focSum perfectForesight 2 2 (fun _ _ => 1) P (fun _ _ => 1) Ψ 0 (10 / 3) () = 0 ∧
      printedFocSum perfectForesight 2 2 (fun _ _ => 1) P (fun _ _ => 1) Ψ 0 (10 / 3) () ≠ 0 := by
  intro P Ψ
  have hP : ∀ k ω, 0 < P k ω := fun k _ => by positivity
  have hfoc : focSum perfectForesight 2 2 (fun _ _ => 1) P (fun _ _ => 1) Ψ 0 (10 / 3) () = 0 := by
    simp only [focSum, focTerm, demand, perfectForesight, LinearMap.id_apply, markup,
      Finset.sum_range_succ, Finset.sum_range_zero, P, Ψ]
    rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num]
    simp only [Real.rpow_intCast]
    norm_num
  refine ⟨?_, hfoc, ?_⟩
  · refine (isMaxOn_iff_foc perfectForesight (by norm_num) (by norm_num) hP ?_ ?_).mpr hfoc
    · simp only [wgt, perfectForesight, LinearMap.id_apply, Finset.sum_range_succ,
        Finset.sum_range_zero, P]
      positivity
    · simp only [wgt, perfectForesight, LinearMap.id_apply, Finset.sum_range_succ,
        Finset.sum_range_zero, P, Ψ, Pi.mul_apply]
      positivity
  · simp only [printedFocSum, demand, perfectForesight, LinearMap.id_apply, markup,
      Finset.sum_range_succ, Finset.sum_range_zero, P, Ψ]
    rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num]
    simp only [Real.rpow_intCast]
    norm_num

/-! ### (b) The log-linear pricing rule -/

/-- **Differentiation under `E_t`.** If the second-order remainder of `z ↦ g z`
at `x` is bounded by `C h²` uniformly in the state, then `z ↦ E_t[g z]` has
derivative `E_t[g']` at `x`. A local copy of the argument used for eq. (10) of
Galí (2015), p. 56; needed for the linearisation in Ex. 3.5(b). -/
theorem hasDerivAt_E_of_remainder {g : ℝ → Ω → ℝ} {g' : Ω → ℝ} {x C δ : ℝ} (hδ : 0 < δ)
    (hrem : ∀ h, |h| < δ → ∀ ω, |g (x + h) ω - g x ω - h * g' ω| ≤ C * h ^ 2)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t g' ω) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h => 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω)
      =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    have hh' : |h| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hh
    have key : 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω
        = 𝔼.E t (g (x + h) - g x - h • g') ω := by
      simp [map_sub, map_smul]
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    exact 𝔼.abs_E_le (fun ω' => by simpa [smul_eq_mul] using hrem h hh' ω') t ω
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

/-- Differentiating `E_t[exp(s g)]` in `s` for a bounded random variable `g`:
the derivative is `E_t[g exp(s g)]` (Galí (2015), Ex. 3.5(b), p. 93). -/
theorem hasDerivAt_E_exp {g : Ω → ℝ} {B : ℝ} (hg : ∀ ω, |g ω| ≤ B) (t : ℕ) (ω : Ω) (s : ℝ) :
    HasDerivAt (fun r => 𝔼.E t (fun ω' => Real.exp (r * g ω')) ω)
      (𝔼.E t (fun ω' => g ω' * Real.exp (s * g ω')) ω) s := by
  refine hasDerivAt_E_of_remainder 𝔼 (g := fun r ω' => Real.exp (r * g ω'))
    (δ := 1 / (|B| + 1)) (C := Real.exp (|s| * |B|) * B ^ 2) (by positivity)
    (fun h hh ω' => ?_) t ω
  have hgB : |g ω'| ≤ |B| := (hg ω').trans (le_abs_self B)
  have hhB : |h| * |B| ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hh
    nlinarith [abs_nonneg B, abs_nonneg h]
  have hhg : |h * g ω'| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hgB (abs_nonneg h)).trans hhB
  have hexp := Real.abs_exp_sub_one_sub_id_le hhg
  have key : Real.exp ((s + h) * g ω') - Real.exp (s * g ω') - h * (g ω' * Real.exp (s * g ω'))
      = Real.exp (s * g ω') * (Real.exp (h * g ω') - 1 - h * g ω') := by
    rw [add_mul, Real.exp_add]; ring
  rw [key, abs_mul, abs_of_pos (Real.exp_pos _)]
  have e1 : Real.exp (s * g ω') ≤ Real.exp (|s| * |B|) := by
    rw [Real.exp_le_exp]
    calc s * g ω' ≤ |s * g ω'| := le_abs_self _
      _ = |s| * |g ω'| := abs_mul _ _
      _ ≤ |s| * |B| := mul_le_mul_of_nonneg_left hgB (abs_nonneg s)
  have e2 : (h * g ω') ^ 2 ≤ B ^ 2 * h ^ 2 := by
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (sq_le_sq.mpr (by simpa using hgB)) (sq_nonneg h)
  calc Real.exp (s * g ω') * |Real.exp (h * g ω') - 1 - h * g ω'|
      ≤ Real.exp (|s| * |B|) * (B ^ 2 * h ^ 2) :=
        mul_le_mul e1 (hexp.trans e2) (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (|s| * |B|) * B ^ 2 * h ^ 2 := by ring

/-- The first-order condition of Ex. 3.5(a) written with general weights
`wₖ` (Galí (2015), p. 92): `∑_{k<N} E_t[wₖ (P* − M Ψ_{t+k})]`. -/
noncomputable def focLHS (N : ℕ) (ε : ℝ) (w : ℕ → Ω → ℝ) (x : ℝ) (Ψ : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.range N, 𝔼.E t (fun ω' => w k ω' * (x - markup ε * Ψ k ω')) ω

/-- The first-order sum is `focLHS` with weights `Λ_{t,t+k} Y_{t+k|t}/P_{t+k}`
(Galí (2015), Ex. 3.5(a), p. 92). -/
theorem focSum_eq_focLHS (N : ℕ) (ε : ℝ) (Λ P C Ψ : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) :
    focSum 𝔼 N ε Λ P C Ψ t x
      = focLHS 𝔼 N ε (fun k ω => Λ k ω / P k ω * demand ε x (P k) (C k) ω) x Ψ t := rfl

/-- **Exact linearisation of the first-order condition** at the zero-inflation
steady state (Galí (2015), Ex. 3.5(b), p. 93). Perturb along an arbitrary
bounded direction: weights `wₖ = βᵏ w̄ exp(s ŵₖ)` (discount factor, demand and
`1/P` combined), reset price `P* = exp(p̄ + s x̂)` and marginal costs
`Ψ_{t+k} = exp(p̄ − μ + s ψ̂ₖ)`, where `p̄ = μ + ψ̄` is the steady state. The
derivative at `s = 0` is `w̄ e^{p̄} ∑_{k<N} βᵏ (x̂ − E_t ψ̂ₖ)`. -/
theorem hasDerivAt_focLHS_path {N : ℕ} {β ε wbar pbar xhat B : ℝ} (hε : 1 < ε)
    {what ψhat : ℕ → Ω → ℝ} (hw : ∀ k ω, |what k ω| ≤ B) (hψ : ∀ k ω, |ψhat k ω| ≤ B)
    (hxB : |xhat| ≤ B) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => focLHS 𝔼 N ε (fun k ω' => β ^ k * wbar * Real.exp (s * what k ω'))
        (Real.exp (pbar + s * xhat))
        (fun k ω' => Real.exp (pbar - logMarkup ε + s * ψhat k ω')) t ω)
      (wbar * Real.exp pbar * ∑ k ∈ Finset.range N, β ^ k * (xhat - 𝔼.E t (ψhat k) ω)) 0 := by
  set c := wbar * Real.exp pbar with hc
  set a : ℕ → Ω → ℝ := fun k ω' => what k ω' + xhat with ha
  set b : ℕ → Ω → ℝ := fun k ω' => what k ω' + ψhat k ω' with hb
  have haB : ∀ k ω', |a k ω'| ≤ 2 * B := fun k ω' =>
    (abs_add_le _ _).trans (by linarith [hw k ω'])
  have hbB : ∀ k ω', |b k ω'| ≤ 2 * B := fun k ω' =>
    (abs_add_le _ _).trans (by linarith [hw k ω', hψ k ω'])
  have hfun : (fun s => focLHS 𝔼 N ε (fun k ω' => β ^ k * wbar * Real.exp (s * what k ω'))
        (Real.exp (pbar + s * xhat))
        (fun k ω' => Real.exp (pbar - logMarkup ε + s * ψhat k ω')) t ω)
      = fun s => ∑ k ∈ Finset.range N, β ^ k * (c * (𝔼.E t (fun ω' => Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => Real.exp (s * b k ω')) ω)) := by
    funext s
    unfold focLHS
    refine Finset.sum_congr rfl fun k _ => ?_
    have hint : (fun ω' => β ^ k * wbar * Real.exp (s * what k ω') *
          (Real.exp (pbar + s * xhat)
            - markup ε * Real.exp (pbar - logMarkup ε + s * ψhat k ω')))
        = (β ^ k * c) • ((fun ω' => Real.exp (s * a k ω'))
            - fun ω' => Real.exp (s * b k ω')) := by
      funext ω'
      have hM : markup ε * Real.exp (pbar - logMarkup ε + s * ψhat k ω')
          = Real.exp (pbar + s * ψhat k ω') := by
        rw [logMarkup, show pbar - Real.log (markup ε) + s * ψhat k ω'
            = (pbar + s * ψhat k ω') + -Real.log (markup ε) by ring, Real.exp_add,
          Real.exp_neg, Real.exp_log (markup_pos hε)]
        have := (markup_pos hε).ne'
        field_simp
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hM]
      simp only [ha, hb, hc, mul_add, Real.exp_add]
      ring
    rw [hint, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hfun, Finset.mul_sum]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := ((HasDerivAt.sub (hasDerivAt_E_exp 𝔼 (haB k) t ω 0)
    (hasDerivAt_E_exp 𝔼 (hbB k) t ω 0)).const_mul c).const_mul (β ^ k)
  refine h.congr_deriv ?_
  have hab : (fun ω' => a k ω' * Real.exp (0 * a k ω'))
      - (fun ω' => b k ω' * Real.exp (0 * b k ω')) = (fun _ => xhat) - ψhat k := by
    funext ω'; simp [ha, hb]
  rw [← Pi.sub_apply (𝔼.E t _), ← map_sub, hab, map_sub, 𝔼.const]
  simp only [Pi.sub_apply]
  ring

/-- The Taylor weights `ωₖ = βᵏ / ∑_{j<N} βʲ` (Galí (2015), Ex. 3.5(b), p. 93),
written so that they are defined at `β = 1` too. -/
noncomputable def taylorWeight (β : ℝ) (N k : ℕ) : ℝ := β ^ k / ∑ j ∈ Finset.range N, β ^ j

/-- `∑_{j<N} βʲ ≥ 1` for `β ≥ 0` and `N ≥ 1` (Galí (2015), Ex. 3.5(b)). -/
theorem one_le_geomSum {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N) :
    1 ≤ ∑ j ∈ Finset.range N, β ^ j := by
  have := Finset.single_le_sum (f := fun j => β ^ j) (fun j _ => pow_nonneg hβ j)
    (Finset.mem_range.mpr hN)
  simpa using this

/-- **The book's weights** (Galí (2015), Ex. 3.5(b), p. 93): for `β ≠ 1`,
`ωₖ = βᵏ(1 − β)/(1 − β^N)`. -/
theorem taylorWeight_eq {β : ℝ} (hβ : β ≠ 1) (N k : ℕ) :
    taylorWeight β N k = β ^ k * (1 - β) / (1 - β ^ N) := by
  unfold taylorWeight
  rw [geom_sum_eq hβ, div_div_eq_mul_div, ← neg_div_neg_eq]
  ring_nf

/-- **The weights sum to one** (Galí (2015), Ex. 3.5(b), p. 93). -/
theorem sum_taylorWeight {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ Finset.range N, taylorWeight β N k = 1 := by
  unfold taylorWeight
  rw [← Finset.sum_div, div_self (by linarith [one_le_geomSum hβ hN])]

/-- The weights are positive (Galí (2015), Ex. 3.5(b)). -/
theorem taylorWeight_pos {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) (k : ℕ) :
    0 < taylorWeight β N k :=
  div_pos (pow_pos hβ k) (by linarith [one_le_geomSum hβ.le hN])

/-- Without discounting the weights are `1/N` (Galí (2015), Ex. 3.5(b), p. 93). -/
theorem taylorWeight_one (N k : ℕ) : taylorWeight 1 N k = 1 / N := by
  simp [taylorWeight]

/-- **The limit `β → 1`** (Galí (2015), Ex. 3.5(b), p. 93): the book's weights
`βᵏ(1 − β)/(1 − β^N)` tend to `1/N` as `β → 1`. -/
theorem tendsto_taylorWeight {N : ℕ} (hN : 0 < N) (k : ℕ) :
    Tendsto (fun β : ℝ => β ^ k * (1 - β) / (1 - β ^ N)) (𝓝[≠] 1) (𝓝 (1 / N)) := by
  have hS : (∑ j ∈ Finset.range N, (1 : ℝ) ^ j) ≠ 0 := by
    have := one_le_geomSum (le_refl (0 : ℝ) |>.trans zero_le_one) hN
    linarith
  have hcont : ContinuousAt (fun β : ℝ => taylorWeight β N k) 1 := by
    unfold taylorWeight
    exact ContinuousAt.div (by fun_prop) (by fun_prop) hS
  have h1 := hcont.tendsto
  rw [taylorWeight_one] at h1
  refine (h1.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact taylorWeight_eq hβ N k

/-- **The log-linear pricing rule** (Galí (2015), Ex. 3.5(b), p. 93). The
first-order term of the first-order condition vanishes if and only if
`p*_t = μ + ∑_{k<N} ωₖ E_t ψ_{t+k}`, where `p*_t = p̄ + x̂` and
`ψ_{t+k} = (p̄ − μ) + ψ̂ₖ`. -/
theorem pricing_rule_iff {N : ℕ} (hN : 0 < N) {β ε wbar pbar xhat : ℝ} (hβ : 0 ≤ β)
    (hwbar : 0 < wbar) (ψhat : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    wbar * Real.exp pbar * ∑ k ∈ Finset.range N, β ^ k * (xhat - 𝔼.E t (ψhat k) ω) = 0 ↔
      pbar + xhat = logMarkup ε + ∑ k ∈ Finset.range N,
        taylorWeight β N k * 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω := by
  set S := ∑ j ∈ Finset.range N, β ^ j with hS
  have hS1 : 1 ≤ S := one_le_geomSum hβ hN
  set T := ∑ k ∈ Finset.range N, β ^ k * 𝔼.E t (ψhat k) ω with hT
  have h1 : ∑ k ∈ Finset.range N, β ^ k * (xhat - 𝔼.E t (ψhat k) ω) = S * xhat - T := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hE : ∀ k, 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω
      = (pbar - logMarkup ε) + 𝔼.E t (ψhat k) ω := by
    intro k
    have hf : (fun ω' => (pbar - logMarkup ε) + ψhat k ω')
        = (fun _ => pbar - logMarkup ε) + ψhat k := rfl
    rw [hf, map_add, 𝔼.const]; rfl
  have h2 : ∑ k ∈ Finset.range N,
      taylorWeight β N k * 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω
      = (S * (pbar - logMarkup ε) + T) / S := by
    simp_rw [hE]
    unfold taylorWeight
    rw [← hS]
    calc ∑ k ∈ Finset.range N, β ^ k / S * (pbar - logMarkup ε + 𝔼.E t (ψhat k) ω)
        = (∑ k ∈ Finset.range N, β ^ k * (pbar - logMarkup ε + 𝔼.E t (ψhat k) ω)) / S := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = (S * (pbar - logMarkup ε) + T) / S := by
          congr 1
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [h1, h2]
  have hc : wbar * Real.exp pbar ≠ 0 := (mul_pos hwbar (Real.exp_pos _)).ne'
  have hS0 : S ≠ 0 := by linarith
  constructor
  · intro h
    have h3 := (mul_eq_zero.mp h).resolve_left hc
    field_simp
    linarith
  · intro h
    have h3 : S * xhat - T = 0 := by
      field_simp at h
      linarith
    rw [h3, mul_zero]

/-- **The pricing rule without discounting** (Galí (2015), Ex. 3.5(b), p. 93):
with `β = 1`, `p*_t = μ + N⁻¹ ∑_{k<N} E_t ψ_{t+k}`. -/
theorem pricing_rule_iff_undiscounted {N : ℕ} (hN : 0 < N) {ε wbar pbar xhat : ℝ}
    (hwbar : 0 < wbar) (ψhat : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    wbar * Real.exp pbar * ∑ k ∈ Finset.range N, (1 : ℝ) ^ k * (xhat - 𝔼.E t (ψhat k) ω) = 0 ↔
      pbar + xhat = logMarkup ε + 1 / N * ∑ k ∈ Finset.range N,
        𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω := by
  rw [pricing_rule_iff 𝔼 hN (ε := ε) zero_le_one hwbar ψhat t ω, Finset.mul_sum]
  simp only [taylorWeight_one]

/-! ### (c) The price level -/

/-- The aggregate price index of the Taylor model (Galí (2015), Ex. 3.5(c),
p. 93): a share `1/N` of firms charges each of the last `N` reset prices,
so `P_t = (N⁻¹ ∑_{k<N} (P*_{t−k})^{1−ε})^{1/(1−ε)}`; `Pstar k` is `P*_{t−k}`. -/
noncomputable def priceIndex (ε : ℝ) (N : ℕ) (Pstar : ℕ → ℝ) : ℝ :=
  ((1 / N) * ∑ k ∈ Finset.range N, Pstar k ^ (1 - ε)) ^ (1 / (1 - ε))

/-- The log price index along a path of reset prices `P*_{t−k} = exp(p̄ + s x̂ₖ)`
(Galí (2015), Ex. 3.5(c)). -/
theorem log_priceIndex_path {ε : ℝ} {N : ℕ} (hN : 0 < N) (pbar : ℝ) (xhat : ℕ → ℝ) (s : ℝ) :
    Real.log (priceIndex ε N (fun k => Real.exp (pbar + s * xhat k)))
      = 1 / (1 - ε) * Real.log ((1 / N) * ∑ k ∈ Finset.range N,
          Real.exp ((pbar + s * xhat k) * (1 - ε))) := by
  unfold priceIndex
  simp_rw [← Real.exp_mul]
  have hpos : 0 < (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, Real.exp ((pbar + s * xhat k) * (1 - ε)) :=
    mul_pos (by positivity) (Finset.sum_pos (fun k _ => Real.exp_pos _)
      (Finset.nonempty_range_iff.mpr hN.ne'))
  rw [Real.log_rpow hpos]

/-- At the zero-inflation steady state all reset prices equal `P = e^{p̄}` and
the price level is `p̄` (Galí (2015), Ex. 3.5(c)). -/
theorem log_priceIndex_steady {ε : ℝ} (hε : ε ≠ 1) {N : ℕ} (hN : 0 < N) (pbar : ℝ) :
    Real.log (priceIndex ε N (fun _ => Real.exp pbar)) = pbar := by
  have h := log_priceIndex_path (ε := ε) hN pbar (fun _ => 0) 0
  simp only [mul_zero, add_zero] at h
  rw [h, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    one_div_mul_cancel (by exact_mod_cast hN.ne'), one_mul, Real.log_exp]
  have : 1 - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm hε)
  field_simp

/-- **The price level is the average of the last `N` reset prices**
(Galí (2015), Ex. 3.5(c), p. 93): along any path `p*_{t−k} = p̄ + s x̂ₖ`, the
derivative of the log price level at the zero-inflation steady state is
`N⁻¹ ∑_{k<N} x̂ₖ`; that is, `p_t = N⁻¹ ∑_{k<N} p*_{t−k}` to first order. -/
theorem hasDerivAt_log_priceIndex {ε : ℝ} (hε : ε ≠ 1) {N : ℕ} (hN : 0 < N) (pbar : ℝ)
    (xhat : ℕ → ℝ) :
    HasDerivAt (fun s => Real.log (priceIndex ε N (fun k => Real.exp (pbar + s * xhat k))))
      (1 / N * ∑ k ∈ Finset.range N, xhat k) 0 := by
  have hfun := funext (log_priceIndex_path (ε := ε) hN pbar xhat)
  rw [hfun]
  have hε' : 1 - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm hε)
  have hk : ∀ k ∈ Finset.range N, HasDerivAt (fun s => Real.exp ((pbar + s * xhat k) * (1 - ε)))
      (Real.exp ((pbar + 0 * xhat k) * (1 - ε)) * (xhat k * (1 - ε))) 0 := by
    intro k _
    have h1 : HasDerivAt (fun s : ℝ => (pbar + s * xhat k) * (1 - ε)) (xhat k * (1 - ε)) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (xhat k)).const_add pbar).mul_const
        (1 - ε)
    exact h1.exp
  have hg := (HasDerivAt.fun_sum hk).const_mul (1 / (N : ℝ))
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hval : (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, Real.exp ((pbar + 0 * xhat k) * (1 - ε))
      = Real.exp (pbar * (1 - ε)) := by
    simp only [zero_mul, add_zero]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, one_div_mul_cancel hN',
      one_mul]
  have hl := (hg.log (by rw [hval]; exact (Real.exp_pos _).ne')).const_mul (1 / (1 - ε))
  refine hl.congr_deriv ?_
  rw [hval]
  simp only [zero_mul, add_zero]
  have hsum : ∑ k ∈ Finset.range N, Real.exp (pbar * (1 - ε)) * (xhat k * (1 - ε))
      = Real.exp (pbar * (1 - ε)) * (1 - ε) * ∑ k ∈ Finset.range N, xhat k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum]
  have := (Real.exp_pos (pbar * (1 - ε))).ne'
  field_simp

/-! ### (d) Two-period contracts without discounting -/

/-- **Natural output in levels** (Galí (2015), Ex. 3.5(d), p. 93): with flexible
prices `P = M W/A`, labour supply `W/P = C^σ N^φ`, `C = Y` and `Y = A N`,
`log Y = ((1 + φ) log A − μ)/(σ + φ)` exactly. -/
theorem natural_output_levels {σ φ ε P W A C Y Nl : ℝ} (hε : 1 < ε) (hδ : 0 < σ + φ)
    (hP : 0 < P) (hA : 0 < A) (hN : 0 < Nl) (hflex : P = markup ε * (W / A))
    (hls : W / P = C ^ σ * Nl ^ φ) (hc : C = Y) (hy : Y = A * Nl) :
    Real.log Y = ((1 + φ) * Real.log A - logMarkup ε) / (σ + φ) := by
  have hM := markup_pos hε
  have hWA : 0 < W / A := pos_of_mul_pos_right (hflex ▸ hP) hM.le
  have hW0 : 0 < W := by
    have := mul_pos hWA hA
    rwa [div_mul_cancel₀ W hA.ne'] at this
  have hW : W / P = A / markup ε := by
    rw [hflex]; field_simp
  rw [hW, hc, hy] at hls
  have hY : 0 < A * Nl := mul_pos hA hN
  have h1 := congrArg Real.log hls
  rw [Real.log_div hA.ne' hM.ne', Real.log_mul (Real.rpow_pos_of_pos hY σ).ne'
    (Real.rpow_pos_of_pos hN φ).ne', Real.log_rpow hY, Real.log_rpow hN,
    Real.log_mul hA.ne' hN.ne'] at h1
  rw [hy, Real.log_mul hA.ne' hN.ne', eq_div_iff hδ.ne']
  unfold logMarkup
  linear_combination (-1 : ℝ) * h1

/-- **Natural output in logs** (Galí (2015), Ex. 3.5(d), p. 93): with flexible
prices `p = μ + ψ`, `ψ = w − a`, labour supply `w − p = σ c + φ n`, `c = y` and
`n = y − a`, natural output is `yⁿ = ((1 + φ) a − μ)/(σ + φ)`. -/
theorem natural_output {σ φ μ p w a y n c : ℝ} (hδ : σ + φ ≠ 0) (hflex : p = μ + (w - a))
    (hls : w - p = σ * c + φ * n) (hc : c = y) (hn : n = y - a) :
    y = ((1 + φ) * a - μ) / (σ + φ) := by
  rw [eq_div_iff hδ]
  subst hc hn
  linear_combination (-1 : ℝ) * hls + (-1 : ℝ) * hflex

/-- Nominal marginal cost in terms of the output gap (Galí (2015), Ex. 3.5(d)):
`ψ_t = p_t + δ ỹ_t − μ` with `δ = σ + φ`. -/
theorem psi_eq_gap {σ φ μ : ℝ} (hδ : σ + φ ≠ 0) {p ψ w a c y n yn ytil : Ω → ℝ}
    (hψ : ψ = w - a) (hls : w - p = σ • c + φ • n) (hc : c = y) (hn : n = y - a)
    (hyn : yn = (σ + φ)⁻¹ • ((1 + φ) • a - fun _ => μ)) (hgap : ytil = y - yn) :
    ψ = p + (σ + φ) • ytil - fun _ => μ := by
  funext ω
  have h1 := congrFun hψ ω
  have h2 := congrFun hls ω
  have h3 := congrFun hc ω
  have h4 := congrFun hn ω
  have h5 := congrFun hyn ω
  have h6 := congrFun hgap ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 h5 h6 ⊢
  have h5' : (σ + φ) * yn ω = (1 + φ) * a ω - μ := by
    rw [h5]; field_simp
  linear_combination h1 + h2 + σ * h3 + φ * h4 - (σ + φ) * h6 + h5'

/-- **The two-period Taylor pricing equation** (Galí (2015), Ex. 3.5(d), p. 93).
With `N = 2` and `β = 1` the rule of (b) is `p*_t = μ + ½(E_t ψ_t + E_t ψ_{t+1})`
and the price level is `p_t = ½(p*_t + p*_{t−1})` by (c). With labour supply
`w − p = σ c + φ n`, `c = y`, `n = y − a`, `ψ = w − a`, natural output from
`natural_output`, and adapted `p*` and `ψ`:
`p*_t = ½ p*_{t−1} + ½ E_t p*_{t+1} + δ (ỹ_t + E_t ỹ_{t+1})`, `δ = σ + φ`
(stated at date `t + 1`). -/
theorem taylor_two_period_rule {σ φ μ : ℝ} (hδ : σ + φ ≠ 0)
    {pstar p ψ w a c y n yn ytil : ℕ → Ω → ℝ}
    (hrule : ∀ t, pstar t = (fun _ => μ) + (1 / 2 : ℝ) • (𝔼.E t (ψ t) + 𝔼.E t (ψ (t + 1))))
    (hindex : ∀ t, p (t + 1) = (1 / 2 : ℝ) • (pstar (t + 1) + pstar t))
    (hψ : ∀ t, ψ t = w t - a t) (hls : ∀ t, w t - p t = σ • c t + φ • n t)
    (hc : ∀ t, c t = y t) (hn : ∀ t, n t = y t - a t)
    (hyn : ∀ t, yn t = (σ + φ)⁻¹ • ((1 + φ) • a t - fun _ => μ))
    (hgap : ∀ t, ytil t = y t - yn t) (hpa : 𝔼.Adapted pstar) (hψa : 𝔼.Adapted ψ) (t : ℕ) :
    pstar (t + 1) = (1 / 2 : ℝ) • pstar t + (1 / 2 : ℝ) • 𝔼.E (t + 1) (pstar (t + 2))
      + (σ + φ) • (ytil (t + 1) + 𝔼.E (t + 1) (ytil (t + 2))) := by
  have hψ' : ∀ s, ψ s = p s + (σ + φ) • ytil s - fun _ => μ := fun s =>
    psi_eq_gap hδ (hψ s) (hls s) (hc s) (hn s) (hyn s) (hgap s)
  have hEψ2 : 𝔼.E (t + 1) (ψ (t + 2))
      = 𝔼.E (t + 1) (p (t + 2)) + (σ + φ) • 𝔼.E (t + 1) (ytil (t + 2)) - fun _ => μ := by
    rw [hψ' (t + 2), map_sub, map_add, map_smul, 𝔼.const]
  have hEp2 : 𝔼.E (t + 1) (p (t + 2))
      = (1 / 2 : ℝ) • (𝔼.E (t + 1) (pstar (t + 2)) + pstar (t + 1)) := by
    rw [hindex (t + 1), map_smul, map_add, hpa (t + 1)]
  have hR := hrule (t + 1)
  rw [hψa (t + 1)] at hR
  funext ω
  have e1 := congrFun hR ω
  have e2 := congrFun (hψ' (t + 1)) ω
  have e3 := congrFun hEψ2 ω
  have e4 := congrFun hEp2 ω
  have e5 := congrFun (hindex t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4 e5 ⊢
  linear_combination 2 * e1 + e2 + e3 + e5 + e4

/-! ### One predetermined variable: existence and uniqueness -/

/-- A process `q` solves the second-order expectational difference equation
`q_{t+1} = A q_t + B E_{t+1} q_{t+2} + f_{t+1}` with one predetermined variable
(Galí (2015), Ex. 3.5(e), p. 93). -/
def SolvesPre (A B : ℝ) (f q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, q (t + 1) = A • q t + B • 𝔼.E (t + 1) (q (t + 2)) + f (t + 1)

/-- The AR(1) path `q_0 = q₀`, `q_{t+1} = λ q_t + g_{t+1}` (Galí (2015),
Ex. 3.5(e)). -/
noncomputable def ar1Path (lam : ℝ) (g : ℕ → Ω → ℝ) (q0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => q0
  | t + 1 => lam • ar1Path lam g q0 t + g (t + 1)

/-- The AR(1) path is adapted (Galí (2015), Ex. 3.5(e)). -/
theorem ar1Path_adapted {lam : ℝ} {g : ℕ → Ω → ℝ} {q0 : Ω → ℝ} (hg : 𝔼.Adapted g)
    (hq0 : 𝔼.E 0 q0 = q0) : 𝔼.Adapted (ar1Path lam g q0) := by
  intro t
  induction t with
  | zero => exact hq0
  | succ t ih =>
    have h : 𝔼.E (t + 1) (ar1Path lam g q0 t) = ar1Path lam g q0 t := by
      calc 𝔼.E (t + 1) (ar1Path lam g q0 t) = 𝔼.E (t + 1) (𝔼.E t (ar1Path lam g q0 t)) := by
            rw [ih]
        _ = 𝔼.E t (ar1Path lam g q0 t) := 𝔼.known (Nat.le_succ t) _
        _ = ar1Path lam g q0 t := ih
    change 𝔼.E (t + 1) (lam • ar1Path lam g q0 t + g (t + 1))
      = lam • ar1Path lam g q0 t + g (t + 1)
    rw [map_add, map_smul, h, hg (t + 1)]

/-- The AR(1) path is bounded when `|λ| < 1` and the innovations are bounded:
`|q_t| ≤ M₀ + K/(1 − |λ|)` (Galí (2015), Ex. 3.5(e)). -/
theorem ar1Path_bounded {lam K M0 : ℝ} (hlam : |lam| < 1) {g : ℕ → Ω → ℝ}
    (hg : ∀ t ω, |g t ω| ≤ K) {q0 : Ω → ℝ} (hq0 : ∀ ω, |q0 ω| ≤ M0) (t : ℕ) (ω : Ω) :
    |ar1Path lam g q0 t ω| ≤ M0 + K / (1 - |lam|) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hg 0 ω)
  have hM : 0 ≤ M0 := (abs_nonneg _).trans (hq0 ω)
  have hl : 0 < 1 - |lam| := by linarith
  have hR : 0 ≤ K / (1 - |lam|) := div_nonneg hK hl.le
  have hRe : |lam| * (K / (1 - |lam|)) + K = K / (1 - |lam|) := by
    field_simp; ring
  induction t with
  | zero => exact (hq0 ω).trans (by linarith)
  | succ t ih =>
    change |lam * ar1Path lam g q0 t ω + g (t + 1) ω| ≤ _
    calc |lam * ar1Path lam g q0 t ω + g (t + 1) ω|
        ≤ |lam| * |ar1Path lam g q0 t ω| + K := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul]
          linarith [hg (t + 1) ω]
      _ ≤ |lam| * (M0 + K / (1 - |lam|)) + K := by
          gcongr
      _ ≤ M0 + K / (1 - |lam|) := by
          have : |lam| * M0 ≤ M0 := by
            have := abs_nonneg lam
            nlinarith
          nlinarith

/-- **Existence** (Galí (2015), Ex. 3.5(e)). Let `λ` be a root of
`B λ² − λ + A = 0`, i.e. `A = λ(1 − Bλ)`, with `1 − Bλ ≠ 0`, and let the
forcing be unpredictable, `E_t f_{t+1} = 0`. Then the AR(1) path
`q_{t+1} = λ q_t + f_{t+1}/(1 − Bλ)` solves the equation. -/
theorem predetermined_solves {A B lam : ℝ} (hA : A = lam * (1 - B * lam))
    (hd : 1 - B * lam ≠ 0) {f : ℕ → Ω → ℝ} (hfa : 𝔼.Adapted f)
    (hf0 : ∀ t, 𝔼.E t (f (t + 1)) = 0) {q0 : Ω → ℝ} (hq0 : 𝔼.E 0 q0 = q0) :
    SolvesPre 𝔼 A B f (ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0) := by
  have hga : 𝔼.Adapted (fun t => (1 - B * lam)⁻¹ • f t) := fun t => by
    simp only [map_smul, hfa t]
  have hqa := ar1Path_adapted 𝔼 (lam := lam) hga hq0
  intro t
  have hE : 𝔼.E (t + 1) (ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0 (t + 2))
      = lam • ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0 (t + 1) := by
    change 𝔼.E (t + 1) (lam • ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0 (t + 1)
      + (1 - B * lam)⁻¹ • f (t + 1 + 1)) = _
    rw [map_add, map_smul, map_smul, hf0 (t + 1), hqa (t + 1), smul_zero, add_zero]
  rw [hE]
  change lam • ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0 t + (1 - B * lam)⁻¹ • f (t + 1)
    = A • ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0 t
      + B • (lam • (lam • ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0 t
        + (1 - B * lam)⁻¹ • f (t + 1))) + f (t + 1)
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hA]
  have hd' : 1 - lam * B ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

/-- **Uniqueness** (Galí (2015), Ex. 3.5(e)). With `A = λ(1 − Bλ)`,
`1 − Bλ ≠ 0` and `|B/(1 − Bλ)| < 1` (the other root `1/γ` lies outside the
unit circle), two bounded adapted solutions with the same initial value of the
predetermined variable coincide. The proof factors the equation: the
quasi-difference `q_{t+1} − λ q_t` obeys the stable forward equation
`r_t = γ E_{t+1} r_{t+1}`, so it vanishes for bounded processes. -/
theorem predetermined_unique {A B lam : ℝ} (hA : A = lam * (1 - B * lam))
    (hd : 1 - B * lam ≠ 0) (hγ : |B / (1 - B * lam)| < 1) {f q q' : ℕ → Ω → ℝ}
    (hq : SolvesPre 𝔼 A B f q) (hq' : SolvesPre 𝔼 A B f q') (ha : 𝔼.Adapted q)
    (ha' : 𝔼.Adapted q') (hb : BoundedProc q) (hb' : BoundedProc q') (h0 : q 0 = q' 0) :
    q = q' := by
  obtain ⟨M₁, hM₁⟩ := hb
  obtain ⟨M₂, hM₂⟩ := hb'
  set d : ℕ → Ω → ℝ := fun t => q t - q' t with hd_def
  have hdeq : ∀ t, d (t + 1) = A • d t + B • 𝔼.E (t + 1) (d (t + 2)) := by
    intro t
    simp only [hd_def, map_sub, smul_sub]
    rw [hq t, hq' t]; abel
  have hda : ∀ t, 𝔼.E t (d t) = d t := by
    intro t; simp only [hd_def, map_sub, ha t, ha' t]
  have hdb : ∀ t ω, |d t ω| ≤ M₁ + M₂ := fun t ω => by
    simp only [hd_def, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM₁ t ω) (hM₂ t ω))
  set γ := B / (1 - B * lam) with hγdef
  set r : ℕ → Ω → ℝ := fun t => d (t + 1) - lam • d t with hr_def
  have hr : ∀ t, r t = γ • 𝔼.E (t + 1) (r (t + 1)) := by
    intro t
    have e1 : 𝔼.E (t + 1) (r (t + 1)) = 𝔼.E (t + 1) (d (t + 2)) - lam • d (t + 1) := by
      simp only [hr_def, map_sub, map_smul, hda (t + 1)]
    rw [e1]
    funext ω
    have h := congrFun (hdeq t) ω
    simp only [hr_def, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h ⊢
    rw [hA] at h
    rw [hγdef, div_mul_eq_mul_div, eq_div_iff hd]
    linear_combination h
  have hrb : ∀ t ω, |r t ω| ≤ (1 + |lam|) * (M₁ + M₂) := fun t ω => by
    simp only [hr_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    nlinarith [hdb (t + 1) ω, hdb t ω, abs_nonneg lam]
  set z : ℕ → Ω → ℝ := fun t => 𝔼.E t (r t) with hz_def
  have hz : ∀ t, z t = γ • 𝔼.E t (z (t + 1)) + 0 := by
    intro t
    simp only [hz_def, add_zero]
    conv_lhs => rw [hr t]
    rw [map_smul, 𝔼.tower (Nat.le_succ t)]
  have hz0 : ∀ t, (0 : ℕ → Ω → ℝ) t = γ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := by
    intro t; simp
  have hzb : BoundedProc z := ⟨(1 + |lam|) * (M₁ + M₂), fun t ω => 𝔼.abs_E_le (hrb t) t ω⟩
  have hzz := 𝔼.forward_unique hγ hz hz0 hzb ⟨0, fun t ω => by simp⟩
  have hr0 : ∀ t, r t = 0 := by
    intro t
    rw [hr t]
    have : 𝔼.E (t + 1) (r (t + 1)) = z (t + 1) := rfl
    rw [this, hzz]
    simp
  have hd0 : ∀ t, d t = 0 := by
    intro t
    induction t with
    | zero => simp [hd_def, h0]
    | succ t ih =>
      have := hr0 t
      simp only [hr_def, ih, smul_zero, sub_zero] at this
      exact this
  funext t ω
  have := congrFun (hd0 t) ω
  simpa [hd_def, sub_eq_zero] using this

/-- The AR(1) path in closed form: `q_t = λᵗ q₀ + ∑_{j<t} λʲ g_{t−j}`
(Galí (2015), Ex. 3.5(e)). -/
theorem ar1Path_closed (lam : ℝ) (g : ℕ → Ω → ℝ) (q0 : Ω → ℝ) (t : ℕ) :
    ar1Path lam g q0 t = lam ^ t • q0 + ∑ j ∈ Finset.range t, lam ^ j • g (t - j) := by
  induction t with
  | zero => simp [ar1Path]
  | succ t ih =>
    change lam • ar1Path lam g q0 t + g (t + 1) = _
    rw [ih, Finset.sum_range_succ', smul_add, smul_smul, ← pow_succ', Finset.smul_sum]
    simp only [smul_smul, ← pow_succ', pow_zero, one_smul, Nat.sub_zero]
    have : ∀ j ∈ Finset.range t,
        lam ^ (j + 1) • g (t - j) = lam ^ (j + 1) • g (t + 1 - (j + 1)) := by
      intro j _; rw [Nat.add_sub_add_right]
    rw [Finset.sum_congr rfl this]
    abel

/-! ### (e) Random-walk money and technology -/

/-- The persistence parameter of the Taylor model, `λ = (1 − √δ)/(1 + √δ)`
(Galí (2015), Ex. 3.5(e), p. 93): the stable root of `c λ² − λ + c = 0`. -/
noncomputable def taylorRoot (δ : ℝ) : ℝ := (1 - Real.sqrt δ) / (1 + Real.sqrt δ)

/-- The coefficient `c = (1 − δ)/(2(1 + δ))` of the reset-price equation
`x_t = c x_{t−1} + c E_t x_{t+1} − c Δz_t` (Galí (2015), Ex. 3.5(e)). -/
noncomputable def taylorCoeff (δ : ℝ) : ℝ := (1 - δ) / (2 * (1 + δ))

/-- `λ` solves `c λ² − λ + c = 0`, i.e. `c = λ(1 − cλ)` (Galí (2015), Ex. 3.5(e)). -/
theorem taylorCoeff_eq {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorCoeff δ = taylorRoot δ * (1 - taylorCoeff δ * taylorRoot δ) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ δ = s ^ 2 := ⟨_, Real.sqrt_nonneg δ, (Real.sq_sqrt hδ).symm⟩
  unfold taylorCoeff taylorRoot
  rw [Real.sqrt_sq hs]
  have h1 : 1 + s ≠ 0 := by positivity
  have h2 : 1 + s ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- `1 − cλ = (1 + √δ)²/(2(1 + δ)) > 0` (Galí (2015), Ex. 3.5(e)). -/
theorem one_sub_taylor_pos {δ : ℝ} (hδ : 0 ≤ δ) : 0 < 1 - taylorCoeff δ * taylorRoot δ := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ δ = s ^ 2 := ⟨_, Real.sqrt_nonneg δ, (Real.sq_sqrt hδ).symm⟩
  unfold taylorCoeff taylorRoot
  rw [Real.sqrt_sq hs]
  have h : 1 - (1 - s ^ 2) / (2 * (1 + s ^ 2)) * ((1 - s) / (1 + s))
      = (1 + s) ^ 2 / (2 * (1 + s ^ 2)) := by
    have h1 : 1 + s ≠ 0 := by positivity
    have h2 : 1 + s ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [h]
  positivity

/-- `c/(1 − cλ) = λ` (Galí (2015), Ex. 3.5(e)). -/
theorem taylor_gamma {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorCoeff δ / (1 - taylorCoeff δ * taylorRoot δ) = taylorRoot δ := by
  rw [div_eq_iff (one_sub_taylor_pos hδ).ne']
  exact taylorCoeff_eq hδ

/-- `|λ| < 1` for `δ > 0` (Galí (2015), Ex. 3.5(e)). -/
theorem abs_taylorRoot_lt_one {δ : ℝ} (hδ : 0 < δ) : |taylorRoot δ| < 1 := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  unfold taylorRoot
  have h1 : 0 < 1 + Real.sqrt δ := by linarith
  rw [abs_lt, lt_div_iff₀ h1, div_lt_iff₀ h1]
  constructor <;> linarith

/-- **The reset-price equation** (Galí (2015), Ex. 3.5(e), p. 93). With money
demand `m − p = y`, the output gap is `ỹ = z − p` for `z = m − yⁿ`. If `z` is a
random walk (`E_t z_{t+1} = z_t`; true when `m` and `a` are), then
`x = p* − z` satisfies `x_t = c x_{t−1} + c E_t x_{t+1} − c Δz_t`,
`c = (1 − δ)/(2(1 + δ))`. -/
theorem gap_equation {δ : ℝ} (hδ : 0 < δ) {pstar p z ytil : ℕ → Ω → ℝ}
    (hrule2 : ∀ t, pstar (t + 1) = (1 / 2 : ℝ) • pstar t
      + (1 / 2 : ℝ) • 𝔼.E (t + 1) (pstar (t + 2)) + δ • (ytil (t + 1) + 𝔼.E (t + 1) (ytil (t + 2))))
    (hindex : ∀ t, p (t + 1) = (1 / 2 : ℝ) • (pstar (t + 1) + pstar t))
    (hgap : ∀ t, ytil t = z t - p t) (hzrw : ∀ t, 𝔼.E t (z (t + 1)) = z t)
    (hpa : 𝔼.Adapted pstar) :
    SolvesPre 𝔼 (taylorCoeff δ) (taylorCoeff δ)
      (fun t => -taylorCoeff δ • (z t - z (t - 1))) (fun t => pstar t - z t) := by
  intro t
  have hEy : 𝔼.E (t + 1) (ytil (t + 2))
      = z (t + 1) - (1 / 2 : ℝ) • (𝔼.E (t + 1) (pstar (t + 2)) + pstar (t + 1)) := by
    rw [hgap (t + 2), map_sub, hzrw (t + 1), hindex (t + 1), map_smul, map_add, hpa (t + 1)]
  have hEx : 𝔼.E (t + 1) (pstar (t + 2) - z (t + 2))
      = 𝔼.E (t + 1) (pstar (t + 2)) - z (t + 1) := by
    rw [map_sub, hzrw (t + 1)]
  have hc : taylorCoeff δ * (2 * (1 + δ)) = 1 - δ := by
    unfold taylorCoeff; field_simp
  change pstar (t + 1) - z (t + 1) = taylorCoeff δ • (pstar t - z t)
    + taylorCoeff δ • 𝔼.E (t + 1) (pstar (t + 2) - z (t + 2))
    + -taylorCoeff δ • (z (t + 1) - z (t + 1 - 1))
  rw [hEx, Nat.add_sub_cancel]
  funext ω
  have e1 := congrFun (hrule2 t) ω
  have e2 := congrFun (hgap (t + 1)) ω
  have e3 := congrFun (hindex t) ω
  have e4 := congrFun hEy ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4 ⊢
  have h2 : (2 * (1 + δ)) ≠ 0 := by positivity
  apply mul_left_cancel₀ h2
  linear_combination 2 * e1 + 2 * δ * e2 - 2 * δ * e3 + 2 * δ * e4
    - (pstar t ω + 𝔼.E (t + 1) (pstar (t + 2)) ω - 2 * z (t + 1) ω) * hc

/-- The equilibrium reset-price gap path `x_t = p*_t − z_t`:
`x_{t+1} = λ x_t − λ Δz_{t+1}` from `x₀` (Galí (2015), Ex. 3.5(e)). -/
noncomputable def taylorPath (δ : ℝ) (z : ℕ → Ω → ℝ) (x0 : Ω → ℝ) : ℕ → Ω → ℝ :=
  ar1Path (taylorRoot δ) (fun t => -taylorRoot δ • (z t - z (t - 1))) x0

/-- **Existence and uniqueness of the equilibrium of the Taylor model**
(Galí (2015), Ex. 3.5(e), p. 93). With `δ > 0`, a random walk `z = m − yⁿ`
with bounded innovations, and a given initial reset-price gap `x₀`, the
reset-price equation of `gap_equation` has exactly one bounded adapted solution
with `x 0 = x₀`, namely `x_{t+1} = λ x_t − λ (z_{t+1} − z_t)`, `λ = (1 − √δ)/(1 + √δ)`. -/
theorem taylor_equilibrium {δ : ℝ} (hδ : 0 < δ) {z : ℕ → Ω → ℝ} (hza : 𝔼.Adapted z)
    (hzrw : ∀ t, 𝔼.E t (z (t + 1)) = z t) {K : ℝ} (hK : ∀ t ω, |z (t + 1) ω - z t ω| ≤ K)
    {x0 : Ω → ℝ} (hx0 : 𝔼.E 0 x0 = x0) {M0 : ℝ} (hM0 : ∀ ω, |x0 ω| ≤ M0) :
    (SolvesPre 𝔼 (taylorCoeff δ) (taylorCoeff δ) (fun t => -taylorCoeff δ • (z t - z (t - 1)))
        (taylorPath δ z x0) ∧ 𝔼.Adapted (taylorPath δ z x0) ∧
        BoundedProc (taylorPath δ z x0) ∧ taylorPath δ z x0 0 = x0) ∧
      ∀ x, SolvesPre 𝔼 (taylorCoeff δ) (taylorCoeff δ)
          (fun t => -taylorCoeff δ • (z t - z (t - 1))) x →
        𝔼.Adapted x → BoundedProc x → x 0 = x0 → x = taylorPath δ z x0 := by
  set c := taylorCoeff δ with hc
  set lam := taylorRoot δ with hlam
  have hA : c = lam * (1 - c * lam) := taylorCoeff_eq hδ.le
  have hd : 1 - c * lam ≠ 0 := (one_sub_taylor_pos hδ.le).ne'
  have hγ : c / (1 - c * lam) = lam := taylor_gamma hδ.le
  have hfa : 𝔼.Adapted (fun t => -c • (z t - z (t - 1))) := by
    intro t
    have : 𝔼.E t (z (t - 1)) = z (t - 1) := by
      rw [← hza (t - 1), 𝔼.known (Nat.sub_le t 1)]
    simp only [map_smul, map_sub, hza t, this]
  have hf0 : ∀ t, 𝔼.E t ((fun t => -c • (z t - z (t - 1))) (t + 1)) = 0 := by
    intro t
    simp only [Nat.add_sub_cancel, map_smul, map_sub, hzrw t, hza t, sub_self, smul_zero]
  have hg : (fun t => (1 - c * lam)⁻¹ • (fun t => -c • (z t - z (t - 1))) t)
      = fun t => -lam • (z t - z (t - 1)) := by
    funext t
    rw [smul_smul]
    congr 1
    rw [show -lam = -(c / (1 - c * lam)) by rw [hγ]]
    ring
  have hsol := predetermined_solves 𝔼 hA hd hfa hf0 (q0 := x0) hx0
  rw [hg] at hsol
  have hga : 𝔼.Adapted (fun t => -lam • (z t - z (t - 1))) := by
    intro t
    have : 𝔼.E t (z (t - 1)) = z (t - 1) := by
      rw [← hza (t - 1), 𝔼.known (Nat.sub_le t 1)]
    simp only [map_smul, map_sub, hza t, this]
  have hgb : ∀ t ω, |(fun t => -lam • (z t - z (t - 1))) t ω| ≤ K := by
    intro t ω
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ω)
    have hl := (abs_taylorRoot_lt_one hδ).le
    cases t with
    | zero => simp [hK0]
    | succ t =>
      simp only [Nat.add_sub_cancel, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_neg]
      calc |lam| * |z (t + 1) ω - z t ω| ≤ 1 * K :=
            mul_le_mul hl (hK t ω) (abs_nonneg _) zero_le_one
        _ = K := one_mul K
  refine ⟨⟨hsol, ar1Path_adapted 𝔼 hga hx0,
    ⟨M0 + K / (1 - |lam|), ar1Path_bounded (abs_taylorRoot_lt_one hδ) hgb hM0⟩, rfl⟩, ?_⟩
  intro x hx hxa hxb hx0'
  refine predetermined_unique 𝔼 hA hd ?_ hx hsol hxa (ar1Path_adapted 𝔼 hga hx0) hxb
    ⟨M0 + K / (1 - |lam|), ar1Path_bounded (abs_taylorRoot_lt_one hδ) hgb hM0⟩ hx0'
  rw [hγ]
  exact abs_taylorRoot_lt_one hδ

/-- The innovation `z_{t+1} − z_t` of `z = m − yⁿ` in terms of the money and
technology innovations `εᵐ`, `εᵃ` (Galí (2015), Ex. 3.5(e), p. 93):
`Δz = εᵐ − ((1 + φ)/δ) εᵃ`. -/
theorem z_innovation {σ φ μ : ℝ} {m a yn : ℕ → Ω → ℝ}
    (hyn : ∀ t, yn t = (σ + φ)⁻¹ • ((1 + φ) • a t - fun _ => μ)) (t : ℕ) (ω : Ω) :
    (m (t + 1) - yn (t + 1)) ω - (m t - yn t) ω
      = (m (t + 1) ω - m t ω) - (1 + φ) / (σ + φ) * (a (t + 1) ω - a t ω) := by
  simp only [Pi.sub_apply, hyn, Pi.smul_apply, smul_eq_mul]
  ring

/-- With random-walk money and technology, `z = m − yⁿ` is a random walk
(Galí (2015), Ex. 3.5(e), p. 93). -/
theorem z_randomWalk {σ φ μ : ℝ} {m a yn : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 1 m) (ha : 𝔼.IsAR1 1 a)
    (hyn : ∀ t, yn t = (σ + φ)⁻¹ • ((1 + φ) • a t - fun _ => μ)) :
    𝔼.Adapted (fun t => m t - yn t) ∧ ∀ t, 𝔼.E t (m (t + 1) - yn (t + 1)) = m t - yn t := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simp only [hyn, map_sub, map_smul, 𝔼.const, hm.1 t, ha.1 t]
  · simp only [hyn, map_sub, map_smul, 𝔼.const, hm.2 t, ha.2 t, one_smul]

/-- The quasi-difference of the equilibrium path in closed form
(Galí (2015), Ex. 3.5(e)): with `vᵢ = z_{i+1} − z_i`,
`v_t − x_t = ∑_{j≤t} λʲ v_{t−j} − λᵗ x₀`. -/
theorem taylorPath_closed (δ : ℝ) (z : ℕ → Ω → ℝ) (x0 : Ω → ℝ) (t : ℕ) (ω : Ω) :
    (z (t + 1) ω - z t ω) - taylorPath δ z x0 t ω
      = ∑ j ∈ Finset.range (t + 1), taylorRoot δ ^ j * (z (t - j + 1) ω - z (t - j) ω)
        - taylorRoot δ ^ t * x0 ω := by
  set lam := taylorRoot δ with hlam
  induction t with
  | zero => simp [taylorPath, ar1Path]
  | succ t ih =>
    have hx : taylorPath δ z x0 (t + 1) ω
        = lam * taylorPath δ z x0 t ω - lam * (z (t + 1) ω - z t ω) := by
      simp only [taylorPath, ar1Path, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
        Nat.add_sub_cancel, ← hlam]
      ring
    rw [Finset.sum_range_succ']
    have hs : ∑ j ∈ Finset.range (t + 1),
        lam ^ (j + 1) * (z (t + 1 - (j + 1) + 1) ω - z (t + 1 - (j + 1)) ω)
        = lam * ∑ j ∈ Finset.range (t + 1), lam ^ j * (z (t - j + 1) ω - z (t - j) ω) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.add_sub_add_right]
      ring
    rw [hs, hx]
    simp only [Nat.sub_zero, pow_zero, one_mul]
    linear_combination lam * ih

/-- **Closed form for the output gap** (Galí (2015), Ex. 3.5(e), p. 93). Along
the equilibrium (`p*_t − z_t = x_t`), with `p_{t+1} = ½(p*_{t+1} + p*_t)` and
`ỹ = z − p`,
`ỹ_{t+1} = ((1 + λ)/2) (∑_{j≤t} λʲ v_{t−j} − λᵗ x₀)`, `vᵢ = z_{i+1} − z_i`:
an innovation in `z` moves the gap by `(1 + λ)/2` on impact, decaying at rate `λ`. -/
theorem taylor_gap_closed {δ : ℝ} {pstar p z ytil : ℕ → Ω → ℝ} {x0 : Ω → ℝ}
    (hindex : ∀ t, p (t + 1) = (1 / 2 : ℝ) • (pstar (t + 1) + pstar t))
    (hgap : ∀ t, ytil t = z t - p t) (heq : ∀ t, pstar t - z t = taylorPath δ z x0 t)
    (t : ℕ) (ω : Ω) :
    ytil (t + 1) ω = (1 + taylorRoot δ) / 2 *
      (∑ j ∈ Finset.range (t + 1), taylorRoot δ ^ j * (z (t - j + 1) ω - z (t - j) ω)
        - taylorRoot δ ^ t * x0 ω) := by
  have hc := taylorPath_closed δ z x0 t ω
  have hx : taylorPath δ z x0 (t + 1) ω
      = taylorRoot δ * taylorPath δ z x0 t ω - taylorRoot δ * (z (t + 1) ω - z t ω) := by
    simp only [taylorPath, ar1Path, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      Nat.add_sub_cancel]
    ring
  have e1 := congrFun (hgap (t + 1)) ω
  have e2 := congrFun (hindex t) ω
  have e3 := congrFun (heq (t + 1)) ω
  have e4 := congrFun (heq t) ω
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e1 e2 e3 e4
  rw [← hc]
  linear_combination e1 - e2 - (1 / 2 : ℝ) * e3 - (1 / 2 : ℝ) * e4 - (1 / 2 : ℝ) * hx

/-- **The Taylor model's equilibrium in closed form** (Galí (2015), Ex. 3.5(e),
p. 93). Suppose the pricing equation of (d) holds, `p_{t+1} = ½(p*_{t+1} + p*_t)`,
money demand gives `ỹ = z − p` with `z = m − yⁿ` a random walk with bounded
innovations, `p*` is adapted and `p* − z` is bounded. Then `p* − z` is the
unique equilibrium path `taylorPath` and the output gap, output `y = yⁿ + ỹ`,
employment `n = y − a` and the price level `p = m − y` are given in closed form
by the innovations `v` and the initial gap `x₀ = p*₀ − z₀`. -/
theorem taylor_model_closed_form {δ : ℝ} (hδ : 0 < δ) {pstar p z ytil yn m a n y : ℕ → Ω → ℝ}
    (hrule2 : ∀ t, pstar (t + 1) = (1 / 2 : ℝ) • pstar t
      + (1 / 2 : ℝ) • 𝔼.E (t + 1) (pstar (t + 2)) + δ • (ytil (t + 1) + 𝔼.E (t + 1) (ytil (t + 2))))
    (hindex : ∀ t, p (t + 1) = (1 / 2 : ℝ) • (pstar (t + 1) + pstar t))
    (hgap : ∀ t, ytil t = z t - p t) (hza : 𝔼.Adapted z) (hzrw : ∀ t, 𝔼.E t (z (t + 1)) = z t)
    {K : ℝ} (hK : ∀ t ω, |z (t + 1) ω - z t ω| ≤ K) (hpa : 𝔼.Adapted pstar)
    (hb : BoundedProc fun t => pstar t - z t)
    (hy : ∀ t, y t = yn t + ytil t) (hn : ∀ t, n t = y t - a t) (hp : ∀ t, p t = m t - y t)
    (t : ℕ) (ω : Ω) :
    let lam := taylorRoot δ
    let gap := (1 + lam) / 2 * (∑ j ∈ Finset.range (t + 1),
        lam ^ j * (z (t - j + 1) ω - z (t - j) ω) - lam ^ t * (pstar 0 ω - z 0 ω))
    ytil (t + 1) ω = gap ∧ y (t + 1) ω = yn (t + 1) ω + gap ∧
      n (t + 1) ω = yn (t + 1) ω + gap - a (t + 1) ω ∧
      p (t + 1) ω = m (t + 1) ω - yn (t + 1) ω - gap := by
  intro lam gap
  have hx0 : 𝔼.E 0 (pstar 0 - z 0) = pstar 0 - z 0 := by rw [map_sub, hpa 0, hza 0]
  obtain ⟨M, hM⟩ := hb
  have hsol := gap_equation 𝔼 hδ hrule2 hindex hgap hzrw hpa
  have hxa : 𝔼.Adapted fun t => pstar t - z t := fun t => by simp only [map_sub, hpa t, hza t]
  have huniq := (taylor_equilibrium 𝔼 hδ hza hzrw hK hx0 (M0 := M) (hM 0)).2
    (fun t => pstar t - z t) hsol hxa ⟨M, hM⟩ rfl
  have heq : ∀ t, pstar t - z t = taylorPath δ z (pstar 0 - z 0) t := fun t => congrFun huniq t
  have hg := taylor_gap_closed hindex hgap heq t ω
  simp only [Pi.sub_apply] at hg
  refine ⟨hg, ?_, ?_, ?_⟩
  · rw [hy, Pi.add_apply, hg]
  · rw [hn, Pi.sub_apply, hy, Pi.add_apply, hg]
  · rw [hp, Pi.sub_apply, hy, Pi.add_apply, hg]; ring

/-! ### (f) Persistence and the degree of strategic complementarity -/

/-- **Persistence falls with `δ`** (Galí (2015), Ex. 3.5(f), p. 93): the
autoregressive root `λ(δ) = (1 − √δ)/(1 + √δ)` is strictly decreasing on
`[0, ∞)`. Strong strategic complementarity (small `δ`) makes the effects of a
monetary shock long-lived. -/
theorem taylorRoot_strictAntiOn : StrictAntiOn taylorRoot (Set.Ici 0) := by
  intro a ha b hb hab
  have hs := Real.sqrt_lt_sqrt (Set.mem_Ici.mp ha) hab
  have h0 := Real.sqrt_nonneg a
  unfold taylorRoot
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `λ > 0` exactly when `δ < 1` (strategic complementarity) (Galí (2015),
Ex. 3.5(f)). -/
theorem taylorRoot_pos_iff (δ : ℝ) : 0 < taylorRoot δ ↔ δ < 1 := by
  unfold taylorRoot
  have h0 := Real.sqrt_nonneg δ
  rw [div_pos_iff_of_pos_right (by positivity), sub_pos, Real.sqrt_lt' one_pos, one_pow]

/-- `λ = 0` at `δ = 1`: the effects of a monetary shock last only as long as
the contracts (Galí (2015), Ex. 3.5(f)). -/
theorem taylorRoot_one : taylorRoot 1 = 0 := by
  simp [taylorRoot]

/-- `λ < 0` for `δ > 1`: strategic substitutability makes responses
oscillate (Galí (2015), Ex. 3.5(f)). -/
theorem taylorRoot_neg {δ : ℝ} (hδ : 1 < δ) : taylorRoot δ < 0 := by
  unfold taylorRoot
  have h1 : 1 < Real.sqrt δ := by
    rw [Real.lt_sqrt zero_le_one, one_pow]; exact hδ
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)

/-- `λ → 1` as `δ → 0`: near-complete persistence under extreme strategic
complementarity (Galí (2015), Ex. 3.5(f)). -/
theorem tendsto_taylorRoot_zero : Tendsto taylorRoot (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt taylorRoot 0 := by
    unfold taylorRoot
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
  have h := hc.tendsto
  have h1 : taylorRoot 0 = 1 := by simp [taylorRoot]
  rw [h1] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- The impulse response of the output gap to a unit innovation in `z` (money)
at horizon `j`: `((1 + λ)/2) λʲ` (Galí (2015), Ex. 3.5(e)–(f)). -/
noncomputable def gapIRF (δ : ℝ) (j : ℕ) : ℝ := (1 + taylorRoot δ) / 2 * taylorRoot δ ^ j

/-- **The output-gap response is uniformly more persistent for smaller `δ`**
(Galí (2015), Ex. 3.5(f), p. 93): for `0 ≤ δ₁ < δ₂ ≤ 1` the response at every
horizon `j ≥ 1` is strictly larger under `δ₁`. -/
theorem gapIRF_lt {δ₁ δ₂ : ℝ} (h1 : 0 ≤ δ₁) (h12 : δ₁ < δ₂) (h2 : δ₂ ≤ 1) {j : ℕ}
    (hj : 0 < j) : gapIRF δ₂ j < gapIRF δ₁ j := by
  have hlt := taylorRoot_strictAntiOn (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr (h1.trans h12.le)) h12
  have hnn : 0 ≤ taylorRoot δ₂ := by
    rcases h2.lt_or_eq with h | h
    · exact ((taylorRoot_pos_iff δ₂).mpr h).le
    · rw [h, taylorRoot_one]
  have hp : taylorRoot δ₂ ^ j < taylorRoot δ₁ ^ j := pow_lt_pow_left₀ hlt hnn hj.ne'
  unfold gapIRF
  have : 0 ≤ taylorRoot δ₂ ^ j := pow_nonneg hnn j
  nlinarith

end Gali.BasicNewKeynesianModel.Ex3_5
