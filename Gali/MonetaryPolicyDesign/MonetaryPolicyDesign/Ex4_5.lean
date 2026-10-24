/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Exercise 4.5: optimal monetary policy with price setting in advance

Galí (2015), Chapter 4, Exercise 4.5, pp. 123–125. Money in the utility function with period
utility `log C + log (M/P) − N^{1+φ}/(1+φ)` (eq. (21)), monopolistically competitive firms
with `Y(i) = A N(i)` (eq. (22)), technology `A_t/A_{t−1} = (1 + γ_a) e^{ε^a_t}` and money
`M_t/M_{t−1} = (1 + γ_m) e^{ε^m_t}` (eq. (23)) with Gaussian innovations. The money rules of
part (g) are `ε^m_t = φ_a ε^a_t + φ_v ν_t`, `ν_t ~ N(0, 1)` independent of `ε^a`; the
exogenous rule (23) with `ε^m` independent of `ε^a` is the case `φ_a = 0`.

The shocks live on a genuine probability space with a filtration (`ShockPair`: the pair
`(ε^a_t, ν_t)` is adapted, has law `N(0, σ_a²) ⊗ N(0, 1)`, and the date-`t+1` pair is independent
of `ℱ_t`); `concreteShocks` builds one on `Measure.infinitePi`, so nothing is vacuous.

## (a) Household
`hasDerivAt_utility_C/_m/_N`, `labour_optimum_iff` (`W/P = C N^φ`), `money_optimum_iff`
(`C = (1 − Q) M/P`), and the Euler equation with a genuine conditional expectation (`eulerRHS`);
restated from the Chapter 2 project.

## (b)–(c) Flexible prices
* `price_optimum_iff`: the firm maximises `Y(i)(P(i) − W/A)` iff `P(i) = 𝓜 W/A`,
  `𝓜 = ε/(ε − 1)` (Bernoulli's inequality, `markup_pricing_le/_lt`).
* `flex_employment`: `N_t = 𝓜^{−1/(1+φ)}` in every equilibrium, state by state; `flex_output`;
  `flex_velocity`: `V = 1 − β e^{σ_m²/2}/(1 + γ_m)`, `σ_m² = φ_a² σ_a² + φ_v²`
  (`condExp_money_ratio`, Gaussian MGF); `flex_candidate`: the exact equilibrium exists;
  `flex_inflation`: `P_{t+1}/P_t = (1 + γ_m)/(1 + γ_a) e^{ε^m_{t+1} − ε^a_{t+1}}`.

## (d) Welfare and the Friedman rule
`hasSum_flex_welfare`: `∑ βᵗ E[U_t] = welfareFlex`, which depends on policy only through
`−log V/(1 − β)`; welfare falls with `γ_m`, rises with `σ_m²`, and as a function of the nominal
rate `i > 0` is strictly decreasing and unbounded as `i → 0⁺` (`welfare_rate_strictAnti`,
`tendsto_welfare_rate`); `not_optimal_of_equilibrium`: every policy with `i > 0` is strictly
improved upon, so the optimum must satisfy the Friedman rule `1 + γ_m = β e^{σ_m²/2}`
(`friedman_iff`) — any `(γ_m, σ_m²)` on that locus supports it. **Imprecision**: at the Friedman
rule there is no equilibrium (`not_equilibrium_at_friedman`); it is a supremum, not a maximum.

## (e) Prices set one period in advance
* `sticky_objective_eq`: the book's objective with `Λ_{t−1,t} = β C_{t−1}/C_t` (deflated by
  `P_t`; the printed `P_{t+1}` is a typo) is `β C_{t−1} P_t^{ε−1} P_t(i)^{−ε}(P_t(i) − W_t/A_t)`.
* `sticky_price_optimal`, `sticky_price_unique`: with genuine conditional expectations, the
  optimal preset price is `P_t(i) = 𝓜 E_{t−1}[W_t/A_t]` (sufficiency and necessity);
  `pricing_iff`: in equilibrium this is `E_{t−1}[N_t^{1+φ}] = 1/𝓜`.
* `sticky_employment`: in every sticky-price equilibrium with constant velocity,
  `N_{t+1} = 𝓜^{−1/(1+φ)} e^{(ε^m_{t+1} − ε^a_{t+1}) − (1+φ) s²/2}` a.s.,
  `s² = (φ_a − 1)² σ_a² + φ_v²`; `sticky_employment_zero`, `sticky_velocity`,
  `sticky_output_balances` (`Y = A N`, `M/P = A N/V`); `sticky_candidate`: existence.

## (f) Expected utility
`sticky_expected_utility_succ`, `hasSum_sticky_welfare`, `integral_tsum_sticky_welfare`:
`E[∑ βᵗ U_t] = ∑ βᵗ E[U_t] = welfareFlex(V) − (1 + φ) s² β/(1 − β)` (`stickyWelfare`).

## (g) The optimal money rule
`stabilization_optimal`, `stabilization_improves`: for every nominal rate the rule
`φ_a = 1, φ_v = 0` is at least as good as any `(φ_a, φ_v)` and strictly better unless
`(φ_a, φ_v) = (1, 0)` (for `σ_a² > 0`, `varX_eq_zero_iff`); `policy_not_optimal`
(**correction**): no rule is optimal, since lowering `γ_m` towards the Friedman level always
helps; `tendsto_policyWelfare_friedman`: with `φ_a = 1, φ_v = 0` welfare tends to `+∞` as
`1 + γ_m ↓ β e^{σ_a²/2}`, so the book's answer (`γ_m` at the Friedman level, `φ_a = 1`,
`φ_v = 0`) is the supremum; `stickyN_replicates`, `sticky_replicates_flex`,
`sticky_employment_replicates`, `policyWelfare_replicates`: under `φ_a = 1, φ_v = 0` the
sticky-price equilibrium replicates the flexible-price allocation and welfare.
-/

namespace Gali.MonetaryPolicyDesign.Ex4_5

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-! ### (a) Optimality conditions -/

/-- Galí (2015), Ex. 4.5, eq. (21), p. 123: period utility `log C + log m − N^{1+φ}/(1+φ)`,
with real balances `m = M/P`. -/
noncomputable def utility (φ C m N : ℝ) : ℝ :=
  Real.log C + Real.log m - N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), Ex. 4.5(a), p. 124: the marginal utility of consumption is `U_c = 1/C`. -/
theorem hasDerivAt_utility_C (φ m N : ℝ) {C : ℝ} (hC : C ≠ 0) :
    HasDerivAt (fun C' => utility φ C' m N) C⁻¹ C := by
  have := ((Real.hasDerivAt_log hC).add_const (Real.log m)).sub_const (N ^ (1 + φ) / (1 + φ))
  simpa [utility] using this

/-- Galí (2015), Ex. 4.5(a), p. 124: the marginal utility of real balances is `U_m = 1/m`. -/
theorem hasDerivAt_utility_m (φ C N : ℝ) {m : ℝ} (hm : m ≠ 0) :
    HasDerivAt (fun m' => utility φ C m' N) m⁻¹ m := by
  have := ((Real.hasDerivAt_log hm).const_add (Real.log C)).sub_const (N ^ (1 + φ) / (1 + φ))
  simpa [utility] using this

/-- Galí (2015), Ex. 4.5(a), p. 124: the marginal disutility of labour is `−U_n = N^φ`. -/
theorem hasDerivAt_utility_N {φ : ℝ} (hφ : 0 ≤ φ) (C m N : ℝ) :
    HasDerivAt (fun N' => utility φ C m N') (-N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  have hd : HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
    refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).congr_deriv ?_
    rw [show (1 : ℝ) + φ - 1 = φ by ring]
    field_simp
  have := hd.const_sub (Real.log C + Real.log m)
  simpa [utility] using this

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangent lines (restated from the Chapter 2 project; used for the concavity of (21)). -/
theorem le_tangent {f f' : ℝ → ℝ} {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hcont : ContinuousOn f (Set.uIcc x y)) (hd : ∀ z, 0 < z → HasDerivAt f (f' z) z)
    (hanti : AntitoneOn f' (Set.Ioi 0)) : f y ≤ f x + f' x * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_le hxy.le] at hcont) (fun z hz => hd z (hx.trans hz.1))
    have hle : f' c ≤ f' x := hanti hx (hx.trans hc.1) hc.1.le
    have hpos : 0 < y - x := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith
  · simp
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_ge hxy.le] at hcont) (fun z hz => hd z (lt_of_le_of_lt hy hz.1))
    have hle : f' x ≤ f' c := hanti (lt_of_le_of_lt hy hc.1) hx hc.2.le
    have hpos : 0 < x - y := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith

/-- Galí (2015), p. 18: the disutility of labour is convex for `φ ≥ 0`, in tangent-line form
`x^{1+φ}/(1+φ) + x^φ (y − x) ≤ y^{1+φ}/(1+φ)` (restated from the Chapter 2 project). -/
theorem disutil_tangent_le {φ : ℝ} (hφ : 0 ≤ φ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    x ^ (1 + φ) / (1 + φ) + x ^ φ * (y - x) ≤ y ^ (1 + φ) / (1 + φ) := by
  have hd : ∀ z : ℝ, HasDerivAt (fun N : ℝ => N ^ (1 + φ) / (1 + φ)) (z ^ φ) z := by
    intro z
    refine ((Real.hasDerivAt_rpow_const (x := z) (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).congr_deriv ?_
    rw [show (1 : ℝ) + φ - 1 = φ by ring]
    field_simp
  have h := le_tangent (f := fun N => -(N ^ (1 + φ) / (1 + φ))) (f' := fun N => -N ^ φ) hx hy
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
      (1 + φ)).neg.continuousOn) (fun z _ => (hd z).neg)
    (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
  linarith

/-- Galí (2015), p. 21: the marginal disutility of labour, `d/dN [N^{1+φ}/(1+φ)] = N^φ`. -/
theorem hasDerivAt_disutil {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), Ex. 4.5(a) (concavity of (21)): the tangent-line inequality for `log`,
`log y ≤ log x + (y − x)/x` for `x, y > 0`. -/
theorem log_le_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y ≤ Real.log x + (y - x) / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have : y / x - 1 = (y - x) / x := by field_simp
  linarith

/-- Galí (2015), Ex. 4.5(a), with eq. (4), p. 19 (**necessity**): if hours `N` are a local
optimum along the budget line `P C = W N + X` (real balances `m` fixed) with `C > 0`, then
`W/P = C N^φ`. -/
theorem labour_foc_necessary {φ P W X m C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hC : 0 < C)
    (hbud : P * C = W * N + X)
    (hloc : IsLocalMax (fun N' => utility φ ((W * N' + X) / P) m N') N) :
    W / P = C * N ^ φ := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hin : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
    have := (((hasDerivAt_id N).const_mul W).add_const X).div_const P
    simpa using this
  have hg : HasDerivAt (fun N' => utility φ ((W * N' + X) / P) m N') (C⁻¹ * (W / P) - N ^ φ)
      N := by
    have h1 : HasDerivAt (fun N' => Real.log ((W * N' + X) / P)) (C⁻¹ * (W / P)) N := by
      have := (Real.hasDerivAt_log (by rw [hCeq]; exact hC.ne')).comp N hin
      rw [hCeq] at this
      exact this
    have h2 : HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N :=
      hasDerivAt_disutil hφ N
    exact HasDerivAt.sub (h1.add_const (Real.log m)) h2
  have h0 := hloc.hasDerivAt_eq_zero hg
  field_simp at h0
  field_simp
  linarith

/-- Galí (2015), Ex. 4.5(a), p. 19 (**sufficiency**, by concavity): if `W/P = C N^φ` at a
point with `C, N > 0` on the budget line `P C = W N + X`, it maximises (21) among all feasible
`N' ≥ 0` with `C' = (W N' + X)/P > 0`. -/
theorem labour_foc_sufficient {φ P W X m C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hN : 0 < N)
    (hC : 0 < C) (hbud : P * C = W * N + X) (hfoc : W / P = C * N ^ φ) {N' : ℝ}
    (hN' : 0 ≤ N') (hC' : 0 < (W * N' + X) / P) :
    utility φ ((W * N' + X) / P) m N' ≤ utility φ C m N := by
  have hu := log_le_tangent hC hC'
  have hv := disutil_tangent_le hφ hN hN'
  have hdiff : (W * N' + X) / P - C = W / P * (N' - N) := by
    rw [show C = (W * N + X) / P by rw [← hbud]; field_simp]
    field_simp
    ring
  have h3 : ((W * N' + X) / P - C) / C = N ^ φ * (N' - N) := by
    rw [hdiff, hfoc]; field_simp
  unfold utility
  linarith

/-- Galí (2015), Ex. 4.5(a), eq. (4), p. 19: a point with `C, N > 0` on the budget line solves
the labour-supply problem iff `W/P = C N^φ`. -/
theorem labour_optimum_iff {φ P W X m C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hN : 0 < N)
    (hC : 0 < C) (hbud : P * C = W * N + X) :
    (∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      utility φ ((W * N' + X) / P) m N' ≤ utility φ C m N) ↔ W / P = C * N ^ φ := by
  constructor
  · intro h
    refine labour_foc_necessary (m := m) hφ hP hC hbud ?_
    have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
    have hcont : Continuous fun N' : ℝ => (W * N' + X) / P := by fun_prop
    have h1 : ∀ᶠ N' in 𝓝 N, 0 < (W * N' + X) / P :=
      (hcont.tendsto N).eventually_const_lt (by rw [hCeq]; exact hC)
    filter_upwards [h1, eventually_gt_nhds hN] with N' h1' h2'
    rw [hCeq]
    exact h N' h2'.le h1'
  · intro h N' hN' hC'
    exact labour_foc_sufficient hφ hP hN hC hbud h hN' hC'

/-- Galí (2015), Ex. 4.5(a), with eq. (33), p. 32 (**necessity**): holding total financial
wealth fixed, the budget (32) reads `P C + (1 − Q) P m = X`. If real balances `m > 0` are a
local optimum along it with `C > 0`, then `C = (1 − Q) m`: velocity `P C/M` equals `1 − Q`. -/
theorem money_foc_necessary {φ P Q X m C N : ℝ} (hP : 0 < P) (hC : 0 < C) (hm : 0 < m)
    (hbud : P * C + (1 - Q) * P * m = X)
    (hloc : IsLocalMax (fun m' => utility φ ((X - (1 - Q) * P * m') / P) m' N) m) :
    C = (1 - Q) * m := by
  have hCeq : (X - (1 - Q) * P * m) / P = C := by rw [← hbud]; field_simp; ring
  have hin : HasDerivAt (fun m' : ℝ => (X - (1 - Q) * P * m') / P) (-(1 - Q)) m := by
    have := (((hasDerivAt_id' m).const_mul ((1 - Q) * P)).const_sub X).div_const P
    convert this using 1
    field_simp
  have hg : HasDerivAt (fun m' => utility φ ((X - (1 - Q) * P * m') / P) m' N)
      (C⁻¹ * (-(1 - Q)) + m⁻¹) m := by
    have h1 : HasDerivAt (fun m' => Real.log ((X - (1 - Q) * P * m') / P)) (C⁻¹ * (-(1 - Q)))
        m := by
      have := (Real.hasDerivAt_log (by rw [hCeq]; exact hC.ne')).comp m hin
      rw [hCeq] at this
      exact this
    have := (h1.add (Real.hasDerivAt_log hm.ne')).sub_const (N ^ (1 + φ) / (1 + φ))
    simpa [utility] using this
  have h0 := hloc.hasDerivAt_eq_zero hg
  field_simp at h0
  linarith

/-- Galí (2015), Ex. 4.5(a), eq. (33), p. 32 (**sufficiency**, by concavity of `log`): if
`C = (1 − Q) m` at a point with `C, m > 0` on the budget line `P C + (1 − Q) P m = X`, it
maximises (21) among all `m' > 0` with `C' > 0`. -/
theorem money_foc_sufficient {φ P Q X m C N : ℝ} (hP : 0 < P) (hC : 0 < C) (hm : 0 < m)
    (hbud : P * C + (1 - Q) * P * m = X) (hfoc : C = (1 - Q) * m) {m' : ℝ} (hm' : 0 < m')
    (hC' : 0 < (X - (1 - Q) * P * m') / P) :
    utility φ ((X - (1 - Q) * P * m') / P) m' N ≤ utility φ C m N := by
  have h1 := log_le_tangent hC hC'
  have h2 := log_le_tangent hm hm'
  have hdiff : (X - (1 - Q) * P * m') / P - C = -(1 - Q) * (m' - m) := by
    rw [← hbud]; field_simp; ring
  have hsum : ((X - (1 - Q) * P * m') / P - C) / C + (m' - m) / m = 0 := by
    rw [hdiff, hfoc]
    have hm0 : m ≠ 0 := hm.ne'
    by_cases hQ : 1 - Q = 0
    · rw [hQ] at hfoc; linarith
    · field_simp; ring
  unfold utility
  linarith

/-- Galí (2015), Ex. 4.5(a), eq. (33), p. 32: on the budget line, `(C, m)` with `C, m > 0`
solves the portfolio problem iff `C = (1 − Q) m`. -/
theorem money_optimum_iff {φ P Q X m C N : ℝ} (hP : 0 < P) (hC : 0 < C) (hm : 0 < m)
    (hbud : P * C + (1 - Q) * P * m = X) :
    (∀ m', 0 < m' → 0 < (X - (1 - Q) * P * m') / P →
      utility φ ((X - (1 - Q) * P * m') / P) m' N ≤ utility φ C m N) ↔ C = (1 - Q) * m := by
  constructor
  · intro h
    refine money_foc_necessary (φ := φ) (N := N) hP hC hm hbud ?_
    have hCeq : (X - (1 - Q) * P * m) / P = C := by rw [← hbud]; field_simp; ring
    have hcont : Continuous fun m' : ℝ => (X - (1 - Q) * P * m') / P := by fun_prop
    have h1 : ∀ᶠ m' in 𝓝 m, 0 < (X - (1 - Q) * P * m') / P :=
      (hcont.tendsto m).eventually_const_lt (by rw [hCeq]; exact hC)
    filter_upwards [h1, eventually_gt_nhds hm] with m' h1' h2'
    rw [hCeq]
    exact h m' h2' h1'
  · intro h m' hm' hC'
    exact money_foc_sufficient hP hC hm hbud h hm' hC'


/-! ### (b) Monopolistic price setting -/

/-- Galí (2015), Ex. 4.5(b), p. 124: the gross markup `𝓜 = ε/(ε − 1)`. -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- Galí (2015), Ex. 4.5(b): `𝓜 > 0` for `ε > 1`. -/
theorem markup_pos {ε : ℝ} (hε : 1 < ε) : 0 < markup ε :=
  div_pos (by linarith) (by linarith)

/-- Galí (2015), Ex. 4.5(b): `𝓜 > 1` for `ε > 1`. -/
theorem one_lt_markup {ε : ℝ} (hε : 1 < ε) : 1 < markup ε := by
  rw [markup, one_lt_div (by linarith)]; linarith

/-- Galí (2015), Ex. 4.5(b): the real profit `x^{−ε} (x − c)` of a price `x` per unit of
`P^ε Y`, for marginal cost `c` (Bernoulli's inequality): it is maximised at `x = 𝓜 c`,
`x^{−ε}(x − c) ≤ (𝓜c)^{−ε}(𝓜c − c)` for every `x > 0`. -/
theorem markup_pricing_le {ε c x : ℝ} (hε : 1 < ε) (hc : 0 < c) (hx : 0 < x) :
    x ^ (-ε) * (x - c) ≤ (markup ε * c) ^ (-ε) * (markup ε * c - c) := by
  set a := markup ε * c with ha
  have hapos : 0 < a := mul_pos (markup_pos hε) hc
  have hε1 : ε - 1 ≠ 0 := by linarith
  have hε0 : ε ≠ 0 := by linarith
  have hac : a - c = a / ε := by
    rw [ha, markup]; field_simp; ring
  have hB := one_add_mul_self_le_rpow_one_add (s := x / a - 1) (by
    have := div_pos hx hapos; linarith) hε.le
  rw [show 1 + (x / a - 1) = x / a by ring, Real.div_rpow hx.le hapos.le] at hB
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx ε
  have hae : 0 < a ^ ε := Real.rpow_pos_of_pos hapos ε
  rw [Real.rpow_neg hx.le, Real.rpow_neg hapos.le, hac]
  have key : ε * (x - c) * a ^ ε ≤ a * x ^ ε := by
    have h1 : (1 + ε * (x / a - 1)) * a ^ ε ≤ x ^ ε := by
      rwa [le_div_iff₀ hae] at hB
    have h2 : (1 + ε * (x / a - 1)) * a = ε * (x - c) := by
      have : ε * c = (ε - 1) * a := by rw [ha, markup]; field_simp
      field_simp
      linear_combination this
    nlinarith
  rw [inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀ hxe hae, div_mul_eq_mul_div,
    le_div_iff₀ (by linarith)]
  nlinarith

/-- Galí (2015), Ex. 4.5(b): the maximiser is unique: for `x > 0`, `x ≠ 𝓜 c`,
`x^{−ε}(x − c) < (𝓜c)^{−ε}(𝓜c − c)`. -/
theorem markup_pricing_lt {ε c x : ℝ} (hε : 1 < ε) (hc : 0 < c) (hx : 0 < x)
    (hne : x ≠ markup ε * c) :
    x ^ (-ε) * (x - c) < (markup ε * c) ^ (-ε) * (markup ε * c - c) := by
  set a := markup ε * c with ha
  have hapos : 0 < a := mul_pos (markup_pos hε) hc
  have hε1 : ε - 1 ≠ 0 := by linarith
  have hε0 : ε ≠ 0 := by linarith
  have hac : a - c = a / ε := by
    rw [ha, markup]; field_simp; ring
  have hs : x / a - 1 ≠ 0 := by
    intro h
    apply hne
    rw [sub_eq_zero, div_eq_one_iff_eq hapos.ne'] at h
    exact h
  have hB := one_add_mul_self_lt_rpow_one_add (s := x / a - 1) (by
    have := div_pos hx hapos; linarith) hs hε
  rw [show 1 + (x / a - 1) = x / a by ring, Real.div_rpow hx.le hapos.le] at hB
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx ε
  have hae : 0 < a ^ ε := Real.rpow_pos_of_pos hapos ε
  rw [Real.rpow_neg hx.le, Real.rpow_neg hapos.le, hac]
  have key : ε * (x - c) * a ^ ε < a * x ^ ε := by
    have h1 : (1 + ε * (x / a - 1)) * a ^ ε < x ^ ε := by
      rwa [lt_div_iff₀ hae] at hB
    have h2 : (1 + ε * (x / a - 1)) * a = ε * (x - c) := by
      have : ε * c = (ε - 1) * a := by rw [ha, markup]; field_simp
      field_simp
      linear_combination this
    nlinarith
  rw [inv_mul_eq_div, inv_mul_eq_div, div_lt_div_iff₀ hxe hae, div_mul_eq_mul_div,
    lt_div_iff₀ (by linarith)]
  nlinarith

/-- Galí (2015), Ex. 4.5(b), p. 124: the profit `Y(i)(P(i) − W/A)` with demand
`Y(i) = (P(i)/P)^{−ε} Y` equals `P^ε Y · P(i)^{−ε}(P(i) − W/A)`. -/
theorem profit_eq {ε P Y x c : ℝ} (hP : 0 < P) (hx : 0 < x) :
    (x / P) ^ (-ε) * Y * (x - c) = P ^ ε * Y * (x ^ (-ε) * (x - c)) := by
  rw [Real.div_rpow hx.le hP.le, Real.rpow_neg hP.le, div_inv_eq_mul]
  ring

/-- **Ex. 4.5(b)** (Galí 2015, p. 124): the monopolistically competitive firm, setting its price
after observing the shocks, maximises current profit `Y(i)(P(i) − W/A)` subject to
`Y(i) = (P(i)/P)^{−ε} Y` at a price `x > 0` if and only if `x = 𝓜 W/A`, `𝓜 = ε/(ε − 1)`. -/
theorem price_optimum_iff {ε P Y c x : ℝ} (hε : 1 < ε) (hP : 0 < P) (hY : 0 < Y) (hc : 0 < c)
    (hx : 0 < x) :
    (∀ x', 0 < x' → (x' / P) ^ (-ε) * Y * (x' - c) ≤ (x / P) ^ (-ε) * Y * (x - c)) ↔
      x = markup ε * c := by
  have hK : 0 < P ^ ε * Y := mul_pos (Real.rpow_pos_of_pos hP ε) hY
  constructor
  · intro h
    by_contra hne
    have h1 := h (markup ε * c) (mul_pos (markup_pos hε) hc)
    rw [profit_eq hP (mul_pos (markup_pos hε) hc), profit_eq hP hx] at h1
    have h2 := markup_pricing_lt hε hc hx hne
    nlinarith
  · rintro rfl x' hx'
    rw [profit_eq hP hx', profit_eq hP (mul_pos (markup_pos hε) hc)]
    exact mul_le_mul_of_nonneg_left (markup_pricing_le hε hc hx') hK.le

/-- Galí (2015), Ex. 4.5(b): in a symmetric equilibrium `P = 𝓜 W/A`, the real wage is
`W/P = A/𝓜`. -/
theorem real_wage_of_pricing {ε P W A : ℝ} (hε : 1 < ε) (hP : 0 < P) (hA : 0 < A)
    (h : P = markup ε * (W / A)) : W / P = A / markup ε := by
  have hM := markup_pos hε
  have hW : W ≠ 0 := by
    rintro rfl
    rw [zero_div, mul_zero] at h
    exact hP.ne' h
  rw [h]; field_simp

/-! ### (c) The flexible-price equilibrium: employment -/

/-- Galí (2015), Ex. 4.5(c): flexible-price employment `N = 𝓜^{−1/(1+φ)}`. -/
noncomputable def Nflex (φ ε : ℝ) : ℝ := (markup ε)⁻¹ ^ (1 + φ)⁻¹

/-- Galí (2015), Ex. 4.5(c): `N > 0`. -/
theorem Nflex_pos {φ ε : ℝ} (hε : 1 < ε) : 0 < Nflex φ ε :=
  Real.rpow_pos_of_pos (inv_pos.2 (markup_pos hε)) _

/-- Galí (2015), Ex. 4.5(c): `N^{1+φ} = 1/𝓜`. -/
theorem Nflex_rpow {φ ε : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) : Nflex φ ε ^ (1 + φ) = (markup ε)⁻¹ :=
  Real.rpow_inv_rpow (inv_pos.2 (markup_pos hε)).le (by linarith)

/-- Galí (2015), Ex. 4.5(c), p. 124: given labour supply `W/P = C N^φ`, markup pricing
`P = 𝓜 W/A`, technology `Y = A N` and `C = Y`, employment is `N = 𝓜^{−1/(1+φ)}`, state by
state. -/
theorem employment_flex {φ ε P W A C N : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hP : 0 < P) (hA : 0 < A)
    (hN : 0 < N) (hlab : W / P = C * N ^ φ) (hpr : P = markup ε * (W / A)) (hC : C = A * N) :
    N = Nflex φ ε := by
  have hw := real_wage_of_pricing hε hP hA hpr
  rw [hw, hC] at hlab
  have hM := markup_pos hε
  have h1 : N ^ (1 + φ) = (markup ε)⁻¹ := by
    rw [Real.rpow_add hN, Real.rpow_one]
    field_simp at hlab ⊢
    nlinarith [hlab]
  rw [Nflex, ← h1, Real.rpow_rpow_inv hN.le (by linarith)]

/-! ### The stochastic environment -/

variable {Ω : Type*}

/-- Galí (2015), Ex. 4.5, p. 123, and eq. (23): the level `X_t = X₀ (1 + γ)ᵗ e^{ε_1 + ⋯ + ε_t}`
of technology (`X = A`) or of the money supply (`X = M`). -/
noncomputable def level (X₀ γ : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  X₀ * (1 + γ) ^ t * Real.exp (∑ s ∈ Finset.range t, ε (s + 1) ω)

/-- Galí (2015), Ex. 4.5, p. 123, and eq. (23): `X_{t+1}/X_t = (1 + γ) e^{ε_{t+1}}`. -/
theorem level_succ (X₀ γ : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    level X₀ γ ε (t + 1) ω = level X₀ γ ε t ω * ((1 + γ) * Real.exp (ε (t + 1) ω)) := by
  simp only [level, Finset.sum_range_succ, Real.exp_add, pow_succ]
  ring

/-- Galí (2015), Ex. 4.5: levels are positive when `X₀ > 0` and `1 + γ > 0`. -/
theorem level_pos {X₀ γ : ℝ} (hX : 0 < X₀) (hγ : 0 < 1 + γ) (ε : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : 0 < level X₀ γ ε t ω := by
  unfold level
  positivity

/-- Galí (2015), Ex. 4.5: the date-0 level is `X₀`. -/
theorem level_zero (X₀ γ : ℝ) (ε : ℕ → Ω → ℝ) (ω : Ω) : level X₀ γ ε 0 ω = X₀ := by
  simp [level]

/-- Galí (2015), Ex. 4.5: `log X_t = log X₀ + t log(1 + γ) + ε_1 + ⋯ + ε_t`. -/
theorem log_level_eq {X₀ γ : ℝ} (hX : 0 < X₀) (hγ : 0 < 1 + γ) (ε : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : Real.log (level X₀ γ ε t ω) =
      (Real.log X₀ + t * Real.log (1 + γ)) + ∑ s ∈ Finset.range t, ε (s + 1) ω := by
  rw [level, Real.log_mul (mul_pos hX (pow_pos hγ t)).ne' (Real.exp_pos _).ne',
    Real.log_mul hX.ne' (pow_pos hγ t).ne', Real.log_pow, Real.log_exp]

/-- Galí (2015), Ex. 4.5, p. 124: the law of one period's innovations `(ε^a_t, ν_t)`,
independent `N(0, σ_a²)` and `N(0, 1)`. -/
noncomputable abbrev pairLaw (va : ℝ≥0) : Measure (ℝ × ℝ) :=
  (gaussianReal 0 va).prod (gaussianReal 0 1)

/-- Galí (2015), Ex. 4.5 (Gaussian moment generating function): for independent
`ε^a ~ N(0, σ_a²)` and `ν ~ N(0, 1)`, `E e^{a ε^a + b ν} = e^{(a² σ_a² + b²)/2}`. -/
theorem integral_exp_pair (va : ℝ≥0) (a b : ℝ) :
    ∫ q, Real.exp (a * q.1 + b * q.2) ∂(pairLaw va) = Real.exp ((a ^ 2 * va + b ^ 2) / 2) := by
  have h1 : ∫ x, Real.exp (a * x) ∂(gaussianReal 0 va) = Real.exp (va * a ^ 2 / 2) := by
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := va)) a
    simpa [mgf] using this
  have h2 : ∫ x, Real.exp (b * x) ∂(gaussianReal 0 1) = Real.exp (b ^ 2 / 2) := by
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) b
    simpa [mgf] using this
  have hfun : (fun q : ℝ × ℝ => Real.exp (a * q.1 + b * q.2)) =
      fun q => Real.exp (a * q.1) * Real.exp (b * q.2) := by
    funext q; rw [Real.exp_add]
  rw [hfun, integral_prod_mul (fun x => Real.exp (a * x)) (fun y => Real.exp (b * y)), h1, h2,
    ← Real.exp_add]
  congr 1; ring

/-- Galí (2015), Ex. 4.5: `e^{a ε^a + b ν}` is integrable under the law of the innovations. -/
theorem integrable_exp_pair (va : ℝ≥0) (a b : ℝ) :
    Integrable (fun q : ℝ × ℝ => Real.exp (a * q.1 + b * q.2)) (pairLaw va) := by
  have := (integrable_exp_mul_gaussianReal (μ := 0) (v := va) a).mul_prod
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) b)
  refine this.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Real.exp_add]

variable [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (ℱ : Filtration ℕ mΩ)

/-- Galí (2015), Ex. 4.5, pp. 123–124: the shocks. At each date the pair `(ε^a_t, ν_t)` is
`ℱ_t`-measurable with law `N(0, σ_a²) ⊗ N(0, 1)`, and the date-`t+1` pair is independent of
`ℱ_t` (so the pairs are i.i.d. and `ν` is independent of `ε^a` at all leads and lags). -/
structure ShockPair where
  /-- The innovation pair `(ε^a_t, ν_t)`. -/
  Z : ℕ → Ω → ℝ × ℝ
  /-- The technology variance `σ_a²`. -/
  va : ℝ≥0
  /-- The pair is known at date `t`. -/
  adapted : ∀ t, Measurable[ℱ t] (Z t)
  /-- The law of each pair. -/
  hasLaw : ∀ t, HasLaw (Z t) (pairLaw va) μ
  /-- The date-`t+1` pair is independent of the date-`t` information. -/
  indep : ∀ t, Indep (MeasurableSpace.comap (Z (t + 1)) inferInstance) (ℱ t) μ

variable {μ ℱ}

/-- Galí (2015), Ex. 4.5, p. 123: the technology innovation `ε^a_t`. -/
def techShock (S : ShockPair μ ℱ) : ℕ → Ω → ℝ := fun t ω => (S.Z t ω).1

/-- Galí (2015), Ex. 4.5(g), p. 124: the money-growth innovation of the rule class,
`ε^m_t = φ_a ε^a_t + φ_v ν_t`. -/
def moneyShock (φa φv : ℝ) (S : ShockPair μ ℱ) : ℕ → Ω → ℝ :=
  fun t ω => φa * (S.Z t ω).1 + φv * (S.Z t ω).2

/-- Galí (2015), Ex. 4.5(g): the variance `σ_m² = φ_a² σ_a² + φ_v²` of money growth. -/
def varM (va φa φv : ℝ) : ℝ := φa ^ 2 * va + φv ^ 2

/-- Galí (2015), Ex. 4.5(e)–(g): the variance `s² = (φ_a − 1)² σ_a² + φ_v²` of
`ε^m_t − ε^a_t`, the innovation that moves employment when prices are set in advance. -/
def varX (va φa φv : ℝ) : ℝ := (φa - 1) ^ 2 * va + φv ^ 2

/-- Galí (2015), Ex. 4.5: `σ_m² ≥ 0`. -/
theorem varM_nonneg {va : ℝ} (hva : 0 ≤ va) (φa φv : ℝ) : 0 ≤ varM va φa φv := by
  unfold varM; positivity

/-- Galí (2015), Ex. 4.5: `s² ≥ 0`. -/
theorem varX_nonneg {va : ℝ} (hva : 0 ≤ va) (φa φv : ℝ) : 0 ≤ varX va φa φv := by
  unfold varX; positivity

/-- Galí (2015), Ex. 4.5: `E_t g(ε^a_{t+1}, ν_{t+1}) = ∫ g dN(0, σ_a²) ⊗ N(0, 1)` (the
innovation is independent of `ℱ_t`). -/
theorem condExp_shock [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) (t : ℕ) :
    μ[fun ω => g (S.Z (t + 1) ω) | ℱ t] =ᵐ[μ] fun _ => ∫ q, g q ∂(pairLaw S.va) := by
  have hmeas : Measurable (S.Z (t + 1)) := (S.adapted (t + 1)).mono (ℱ.le (t + 1)) le_rfl
  have hsm : StronglyMeasurable[MeasurableSpace.comap (S.Z (t + 1)) inferInstance]
      (fun ω => g (S.Z (t + 1) ω)) := (hg.comp (comap_measurable _)).stronglyMeasurable
  refine (condExp_indep_eq hmeas.comap_le (ℱ.le t) hsm (S.indep t)).trans ?_
  exact Filter.Eventually.of_forall fun _ =>
    (S.hasLaw (t + 1)).integral_comp hg.aestronglyMeasurable

/-- Galí (2015), Ex. 4.5: `E e^{a ε^a_t + b ν_t} = e^{(a² σ_a² + b²)/2}`. -/
theorem integral_exp_shock (S : ShockPair μ ℱ) (a b : ℝ) (t : ℕ) :
    ∫ ω, Real.exp (a * (S.Z t ω).1 + b * (S.Z t ω).2) ∂μ =
      Real.exp ((a ^ 2 * S.va + b ^ 2) / 2) := by
  rw [← integral_exp_pair]
  exact (S.hasLaw t).integral_comp (f := fun q : ℝ × ℝ => Real.exp (a * q.1 + b * q.2))
    (by fun_prop : Continuous fun q : ℝ × ℝ => Real.exp (a * q.1 + b * q.2)).aestronglyMeasurable

/-- Galí (2015), Ex. 4.5: `e^{a ε^a_t + b ν_t}` is integrable. -/
theorem integrable_exp_shock (S : ShockPair μ ℱ) (a b : ℝ) (t : ℕ) :
    Integrable (fun ω => Real.exp (a * (S.Z t ω).1 + b * (S.Z t ω).2)) μ :=
  (S.hasLaw t).integrable_comp (f := fun q : ℝ × ℝ => Real.exp (a * q.1 + b * q.2))
    (integrable_exp_pair S.va a b)

/-- Galí (2015), Ex. 4.5: `ε^a_t ~ N(0, σ_a²)`. -/
theorem hasLaw_fst (S : ShockPair μ ℱ) (t : ℕ) :
    HasLaw (fun ω => (S.Z t ω).1) (gaussianReal 0 S.va) μ :=
  HasLaw.comp (Y := Prod.fst)
    ⟨measurable_fst.aemeasurable, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
    (S.hasLaw t)

/-- Galí (2015), Ex. 4.5: `ν_t ~ N(0, 1)`. -/
theorem hasLaw_snd (S : ShockPair μ ℱ) (t : ℕ) :
    HasLaw (fun ω => (S.Z t ω).2) (gaussianReal 0 1) μ :=
  HasLaw.comp (Y := Prod.snd)
    ⟨measurable_snd.aemeasurable, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩
    (S.hasLaw t)

/-- Galí (2015), Ex. 4.5: linear combinations `a ε^a_t + b ν_t` are integrable. -/
theorem integrable_lin (S : ShockPair μ ℱ) (a b : ℝ) (t : ℕ) :
    Integrable (fun ω => a * (S.Z t ω).1 + b * (S.Z t ω).2) μ :=
  (((hasLaw_fst S t).integrable (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))).const_mul
    a).add (((hasLaw_snd S t).integrable
      (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))).const_mul b)

/-- Galí (2015), Ex. 4.5: `E (a ε^a_t + b ν_t) = 0`. -/
theorem integral_lin (S : ShockPair μ ℱ) (a b : ℝ) (t : ℕ) :
    ∫ ω, (a * (S.Z t ω).1 + b * (S.Z t ω).2) ∂μ = 0 := by
  have h1 := (hasLaw_fst S t).integrable (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))
  have h2 := (hasLaw_snd S t).integrable (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))
  rw [integral_add (h1.const_mul a) (h2.const_mul b), integral_const_mul, integral_const_mul,
    (hasLaw_fst S t).integral_eq, (hasLaw_snd S t).integral_eq, integral_id_gaussianReal,
    integral_id_gaussianReal]
  ring

/-- Galí (2015), Ex. 4.5: expected log technology, `E[log A_t] = log A₀ + t log(1 + γ_a)`. -/
theorem integral_log_tech [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {A₀ γ : ℝ}
    (hA : 0 < A₀) (hγ : 0 < 1 + γ) (t : ℕ) :
    ∫ ω, Real.log (level A₀ γ (techShock S) t ω) ∂μ = Real.log A₀ + t * Real.log (1 + γ) := by
  have hfun : (fun ω => Real.log (level A₀ γ (techShock S) t ω)) = fun ω =>
      (Real.log A₀ + t * Real.log (1 + γ)) +
        ∑ s ∈ Finset.range t, (1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2) := by
    funext ω
    rw [log_level_eq hA hγ]
    simp [techShock]
  rw [hfun, integral_add (integrable_const _) (integrable_finsetSum _ fun s _ =>
    integrable_lin S 1 0 (s + 1)), integral_finsetSum _ fun s _ => integrable_lin S 1 0 (s + 1)]
  simp only [integral_lin, Finset.sum_const_zero, add_zero, integral_const, probReal_univ,
    one_smul]

/-- Galí (2015), Ex. 4.5: `log A_t` is integrable. -/
theorem integrable_log_tech (S : ShockPair μ ℱ) {A₀ γ : ℝ} (hA : 0 < A₀) (hγ : 0 < 1 + γ)
    [IsFiniteMeasure μ] (t : ℕ) :
    Integrable (fun ω => Real.log (level A₀ γ (techShock S) t ω)) μ := by
  have hfun : (fun ω => Real.log (level A₀ γ (techShock S) t ω)) = fun ω =>
      (Real.log A₀ + t * Real.log (1 + γ)) +
        ∑ s ∈ Finset.range t, (1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2) := by
    funext ω
    rw [log_level_eq hA hγ]
    simp [techShock]
  rw [hfun]
  exact (integrable_const _).add (integrable_finsetSum _ fun s _ => integrable_lin S 1 0 (s + 1))

/-- Galí (2015), Ex. 4.5, eq. (23) with Ex. 4.5(g): `E_t[M_t/M_{t+1}] = e^{σ_m²/2}/(1 + γ_m)`
for the money supply `M_{t+1}/M_t = (1 + γ_m) e^{φ_a ε^a_{t+1} + φ_v ν_{t+1}}` (Gaussian MGF,
independence). -/
theorem condExp_money_ratio [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {M₀ γ : ℝ}
    (hM : M₀ ≠ 0) (hγ : 0 < 1 + γ) (φa φv : ℝ) (t : ℕ) :
    μ[fun ω => level M₀ γ (moneyShock φa φv S) t ω / level M₀ γ (moneyShock φa φv S) (t + 1) ω
      | ℱ t] =ᵐ[μ] fun _ => Real.exp (varM S.va φa φv / 2) / (1 + γ) := by
  have hfun : (fun ω => level M₀ γ (moneyShock φa φv S) t ω /
      level M₀ γ (moneyShock φa φv S) (t + 1) ω) = fun ω =>
        (fun q : ℝ × ℝ => (1 + γ)⁻¹ * Real.exp (-φa * q.1 + -φv * q.2)) (S.Z (t + 1) ω) := by
    funext ω
    have h1 : level M₀ γ (moneyShock φa φv S) t ω ≠ 0 :=
      mul_ne_zero (mul_ne_zero hM (pow_ne_zero _ hγ.ne')) (Real.exp_pos _).ne'
    rw [level_succ]
    simp only [moneyShock]
    rw [show -φa * (S.Z (t + 1) ω).1 + -φv * (S.Z (t + 1) ω).2 =
      -(φa * (S.Z (t + 1) ω).1 + φv * (S.Z (t + 1) ω).2) by ring, Real.exp_neg]
    field_simp
  rw [hfun]
  refine (condExp_shock S (g := fun q : ℝ × ℝ => (1 + γ)⁻¹ * Real.exp (-φa * q.1 + -φv * q.2))
    (by fun_prop) t).trans (Filter.Eventually.of_forall fun _ => ?_)
  simp only
  rw [integral_const_mul, integral_exp_pair, varM]
  ring_nf

/-! ### (a)–(c) Equilibrium -/

variable (μ ℱ)

/-- Galí (2015), eq. (5) with `U_c = 1/C` (Ex. 4.5(a)): the right side
`β E_t[(C_t P_t)/(C_{t+1} P_{t+1})]` of the Euler equation, with a genuine conditional
expectation given `ℱ_t`. -/
noncomputable def eulerRHS (β : ℝ) (C P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β * μ[fun ω' => C t ω' * P t ω' / (C (t + 1) ω' * P (t + 1) ω') | ℱ t] ω

variable {μ ℱ}

/-- Galí (2015), Ex. 4.5: the steady bond price `Q* = β e^{σ_m²/2}/(1 + γ_m)`. -/
noncomputable def Qstar (β γ v : ℝ) : ℝ := β * Real.exp (v / 2) / (1 + γ)

/-- Galí (2015), Ex. 4.5: the constant velocity `V = 1 − Q*`. -/
noncomputable def velocity (β γ v : ℝ) : ℝ := 1 - Qstar β γ v

/-- Galí (2015), Ex. 4.5(c): with constant velocity, `C_t P_t = V M_t`, the Euler equation's
right side is the constant `Q* = β e^{σ_m²/2}/(1 + γ_m)`. -/
theorem eulerRHS_of_const_velocity [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) (β : ℝ)
    {M₀ γ V φa φv : ℝ} (hM : M₀ ≠ 0) (hγ : 0 < 1 + γ) (hV : V ≠ 0) {C P : ℕ → Ω → ℝ}
    (hCP : ∀ t ω, C t ω * P t ω = V * level M₀ γ (moneyShock φa φv S) t ω) (t : ℕ) :
    eulerRHS μ ℱ β C P t =ᵐ[μ] fun _ => Qstar β γ (varM S.va φa φv) := by
  have hfun : (fun ω' => C t ω' * P t ω' / (C (t + 1) ω' * P (t + 1) ω'))
      = fun ω' => level M₀ γ (moneyShock φa φv S) t ω' /
        level M₀ γ (moneyShock φa φv S) (t + 1) ω' := by
    funext ω'
    rw [hCP, hCP, mul_div_mul_left _ _ hV]
  filter_upwards [condExp_money_ratio S hM hγ φa φv t] with ω hω
  simp only [eulerRHS]
  rw [hfun, hω, Qstar]
  ring

/-- Galí (2015), Ex. 4.5(c) (the constant-velocity solution): if money demand
`C = (1 − Q) M/P` and the Euler equation hold and velocity `P_t C_t/M_t = V` is constant, then
`V = 1 − β e^{σ_m²/2}/(1 + γ_m)`. -/
theorem velocity_of_euler [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) (β : ℝ)
    {M₀ γ V φa φv : ℝ} (hM : 0 < M₀) (hγ : 0 < 1 + γ) {C P Q : ℕ → Ω → ℝ}
    (hC : ∀ t ω, 0 < C t ω) (hP : ∀ t ω, 0 < P t ω)
    (hmoney : ∀ t ω, C t ω = (1 - Q t ω) * (level M₀ γ (moneyShock φa φv S) t ω / P t ω))
    (heuler : ∀ t, Q t =ᵐ[μ] eulerRHS μ ℱ β C P t)
    (hV : ∀ t ω, P t ω * C t ω / level M₀ γ (moneyShock φa φv S) t ω = V) :
    V = velocity β γ (varM S.va φa φv) := by
  have hMp := level_pos hM hγ (moneyShock φa φv S)
  obtain ⟨ω₀, -⟩ := (heuler 0).exists
  have hVpos : 0 < V := by
    rw [← hV 0 ω₀]
    exact div_pos (mul_pos (hP 0 ω₀) (hC 0 ω₀)) (hMp 0 ω₀)
  have hCP : ∀ t ω, C t ω * P t ω = V * level M₀ γ (moneyShock φa φv S) t ω := fun t ω => by
    rw [← hV t ω]
    field_simp [(hMp t ω).ne']
  have hQ : ∀ ω, Q 0 ω = 1 - V := fun ω => by
    rw [← hV 0 ω, hmoney 0 ω]
    field_simp [(hMp 0 ω).ne', (hP 0 ω).ne']
    ring
  have hae := (heuler 0).trans (eulerRHS_of_const_velocity S β hM.ne' hγ hVpos.ne' hCP 0)
  obtain ⟨ω, hω⟩ := hae.exists
  rw [hQ ω] at hω
  simp only at hω
  rw [velocity]
  linarith

variable (μ ℱ) (β φ ε : ℝ) (A M C N Y P W Q : ℕ → Ω → ℝ)

/-- Galí (2015), Ex. 4.5(a)–(c), pp. 123–124: an equilibrium with flexible prices. The household
conditions are labour supply `W/P = C N^φ`, money demand `C = (1 − Q)(M/P)` and the Euler
equation; firms set `P = 𝓜 W/A` (part (b)); `Y = A N` and `C = Y`. -/
structure IsFlexEquilibrium where
  /-- Consumption is positive. -/
  pos_C : ∀ t ω, 0 < C t ω
  /-- Hours are positive. -/
  pos_N : ∀ t ω, 0 < N t ω
  /-- The price level is positive. -/
  pos_P : ∀ t ω, 0 < P t ω
  /-- Labour supply: `W/P = C N^φ`. -/
  labour : ∀ t ω, W t ω / P t ω = C t ω * N t ω ^ φ
  /-- Money demand: `C = (1 − Q)(M/P)`. -/
  money : ∀ t ω, C t ω = (1 - Q t ω) * (M t ω / P t ω)
  /-- The Euler equation. -/
  euler : ∀ t, Q t =ᵐ[μ] eulerRHS μ ℱ β C P t
  /-- Markup pricing (part (b)): `P = 𝓜 W/A`. -/
  pricing : ∀ t ω, P t ω = markup ε * (W t ω / A t ω)
  /-- Technology: `Y = A N`. -/
  technology : ∀ t ω, Y t ω = A t ω * N t ω
  /-- Goods-market clearing: `C = Y`. -/
  clearing : ∀ t ω, C t ω = Y t ω

variable {μ ℱ β φ ε A M C N Y P W Q}

/-- **Ex. 4.5(c)** (Galí 2015, p. 124): in every flexible-price equilibrium employment is
constant, `N_t = 𝓜^{−1/(1+φ)}`, state by state. -/
theorem flex_employment {β φ ε : ℝ} {A M C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε A M C N Y P W Q) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hA : ∀ t ω, 0 < A t ω) (t : ℕ) (ω : Ω) : N t ω = Nflex φ ε :=
  employment_flex hφ hε (h.pos_P t ω) (hA t ω) (h.pos_N t ω) (h.labour t ω) (h.pricing t ω)
    ((h.clearing t ω).trans (h.technology t ω))

/-- **Ex. 4.5(c)** (Galí 2015, p. 124): flexible-price output and consumption are
`Y_t = C_t = 𝓜^{−1/(1+φ)} A_t`. -/
theorem flex_output {β φ ε : ℝ} {A M C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε A M C N Y P W Q) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hA : ∀ t ω, 0 < A t ω) (t : ℕ) (ω : Ω) :
    Y t ω = A t ω * Nflex φ ε ∧ C t ω = A t ω * Nflex φ ε := by
  have hY : Y t ω = A t ω * Nflex φ ε := by
    rw [h.technology t ω, flex_employment h hφ hε hA t ω]
  exact ⟨hY, (h.clearing t ω).trans hY⟩

/-- **Ex. 4.5(c)** (Galí 2015, p. 124): with constant velocity the flexible-price equilibrium has
`V = 1 − β e^{σ_m²/2}/(1 + γ_m)`. -/
theorem flex_velocity [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {β φ ε M₀ γm φa φv V : ℝ}
    (hM : 0 < M₀) (hγm : 0 < 1 + γm) {A C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε A (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) :
    V = velocity β γm (varM S.va φa φv) :=
  velocity_of_euler S β hM hγm h.pos_C h.pos_P h.money h.euler fun t ω => by
    rw [h.clearing t ω]; exact hV t ω

/-- **Ex. 4.5(c)** (Galí 2015, p. 124, existence): if `β e^{σ_m²/2} < 1 + γ_m`, the allocation
`N = 𝓜^{−1/(1+φ)}`, `C = Y = N A`, `P = V M/(N A)`, `W = P A/𝓜`, `Q = Q*` is an exact
flexible-price equilibrium. -/
theorem flex_candidate [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {β φ ε A₀ γa M₀ γm φa φv : ℝ}
    (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hM : 0 < M₀)
    (hγm : 0 < 1 + γm) (hQ : Qstar β γm (varM S.va φa φv) < 1) :
    IsFlexEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S)) (level M₀ γm (moneyShock φa φv S))
      (fun t ω => level A₀ γa (techShock S) t ω * Nflex φ ε) (fun _ _ => Nflex φ ε)
      (fun t ω => level A₀ γa (techShock S) t ω * Nflex φ ε)
      (fun t ω => velocity β γm (varM S.va φa φv) * level M₀ γm (moneyShock φa φv S) t ω /
        (level A₀ γa (techShock S) t ω * Nflex φ ε))
      (fun t ω => velocity β γm (varM S.va φa φv) * level M₀ γm (moneyShock φa φv S) t ω /
        (Nflex φ ε * markup ε))
      (fun _ _ => Qstar β γm (varM S.va φa φv)) := by
  have hV : 0 < velocity β γm (varM S.va φa φv) := by rw [velocity]; linarith
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hN := Nflex_pos (φ := φ) hε
  have hN1 := Nflex_rpow hφ hε
  have hmk := markup_pos hε
  refine ⟨fun t ω => mul_pos (hAp t ω) hN, fun _ _ => hN, fun t ω => div_pos (mul_pos hV
    (hMp t ω)) (mul_pos (hAp t ω) hN), fun t ω => ?_, fun t ω => ?_, fun t => ?_, fun t ω => ?_,
    fun _ _ => rfl, fun _ _ => rfl⟩
  · have key : Nflex φ ε * Nflex φ ε ^ φ = (markup ε)⁻¹ := by
      rw [← hN1, Real.rpow_add hN, Real.rpow_one]
    field_simp [(hAp t ω).ne', (hMp t ω).ne', hN.ne', hV.ne', hmk.ne']
    rw [show Nflex φ ε * markup ε * Nflex φ ε ^ φ = markup ε * (Nflex φ ε * Nflex φ ε ^ φ) by
      ring, key]
    field_simp
  · rw [show 1 - Qstar β γm (varM S.va φa φv) = velocity β γm (varM S.va φa φv) from rfl]
    field_simp [(hAp t ω).ne', (hMp t ω).ne', hN.ne', hV.ne']
  · refine (eulerRHS_of_const_velocity S β hM.ne' hγm hV.ne' (fun t ω => ?_) t).symm
    field_simp [(hAp t ω).ne', (hMp t ω).ne', hN.ne', hV.ne']
  · field_simp [(hAp t ω).ne', (hMp t ω).ne', hN.ne', hV.ne', hmk.ne']

/-- **Ex. 4.5(c)** (Galí 2015, p. 124): flexible-price inflation is
`P_{t+1}/P_t = (1 + γ_m)/(1 + γ_a) e^{ε^m_{t+1} − ε^a_{t+1}}`, in every equilibrium with
constant velocity. -/
theorem flex_inflation (S : ShockPair μ ℱ) {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ)
    (hε : 1 < ε) (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm)
    {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) (t : ℕ) (ω : Ω) :
    P (t + 1) ω / P t ω = (1 + γm) / (1 + γa) *
      Real.exp (moneyShock φa φv S (t + 1) ω - techShock S (t + 1) ω) := by
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hN := Nflex_pos (φ := φ) hε
  have hPeq : ∀ s, P s ω = V * level M₀ γm (moneyShock φa φv S) s ω /
      (level A₀ γa (techShock S) s ω * Nflex φ ε) := fun s => by
    have h1 := hV s ω
    rw [(flex_output h hφ hε hAp s ω).1] at h1
    rw [← h1]
    field_simp [(hAp s ω).ne', (hMp s ω).ne']
  have hVpos : 0 < V := by
    rw [← hV 0 ω, ← h.clearing 0 ω]
    exact div_pos (mul_pos (h.pos_P 0 ω) (h.pos_C 0 ω)) (hMp 0 ω)
  rw [hPeq, hPeq, level_succ, level_succ, Real.exp_sub]
  field_simp [(hAp t ω).ne', (hMp t ω).ne', hVpos.ne', hγa.ne', hN.ne',
    (Real.exp_pos (techShock S (t + 1) ω)).ne']

/-! ### (d) Welfare under flexible prices and the Friedman rule -/

/-- Galí (2015), Ex. 4.5(d), p. 124: in a flexible-price equilibrium with constant velocity `V`,
period utility is `2 log A_t + 2 log N − log V − 𝓜⁻¹/(1+φ)`, `N = 𝓜^{−1/(1+φ)}`. -/
theorem flex_period_utility {β φ ε : ℝ} {A M C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε A M C N Y P W Q) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hA : ∀ t ω, 0 < A t ω) (hM : ∀ t ω, 0 < M t ω) {V : ℝ}
    (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) (t : ℕ) (ω : Ω) :
    utility φ (C t ω) (M t ω / P t ω) (N t ω) = 2 * Real.log (A t ω) +
      2 * Real.log (Nflex φ ε) - Real.log V - (markup ε)⁻¹ / (1 + φ) := by
  have hY := flex_output h hφ hε hA t ω
  have hN := flex_employment h hφ hε hA t ω
  have hP := h.pos_P t ω
  have hNf := Nflex_pos (φ := φ) hε
  have hVpos : 0 < V := by
    rw [← hV t ω, hY.1]; exact div_pos (mul_pos hP (mul_pos (hA t ω) hNf)) (hM t ω)
  have hmp : M t ω / P t ω = A t ω * Nflex φ ε / V := by
    rw [← hV t ω, hY.1]
    field_simp [(hA t ω).ne', (hM t ω).ne', hP.ne', hNf.ne']
  rw [utility, hY.2, hmp, hN, Nflex_rpow hφ hε,
    Real.log_div (mul_pos (hA t ω) hNf).ne' hVpos.ne',
    Real.log_mul (hA t ω).ne' hNf.ne']
  ring

/-- Galí (2015), Ex. 4.5(d), p. 124: closed-form expected lifetime utility of the flexible-price
equilibrium, `(2 log A₀ + 2 log N − log V − 𝓜⁻¹/(1+φ))/(1 − β) + 2 β log(1 + γ_a)/(1 − β)²`. -/
noncomputable def welfareFlex (β φ ε A₀ γa V : ℝ) : ℝ :=
  (2 * Real.log A₀ + 2 * Real.log (Nflex φ ε) - Real.log V - (markup ε)⁻¹ / (1 + φ)) / (1 - β) +
    2 * Real.log (1 + γa) * β / (1 - β) ^ 2

/-- Galí (2015), Ex. 4.5(d): if `E[U_t] = K + c t`, then `∑ βᵗ E[U_t]` converges to
`K/(1 − β) + c β/(1 − β)²` (for `0 ≤ β < 1`). -/
theorem hasSum_affine {β K c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    HasSum (fun t : ℕ => β ^ t * (K + c * t)) (K / (1 - β) + c * β / (1 - β) ^ 2) := by
  have hg := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left K
  have hn := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)).mul_left c
  have hne : (1 - β) ≠ 0 := by linarith
  convert hg.add hn using 1
  · funext t; ring
  · field_simp

/-- **Ex. 4.5(d)** (Galí 2015, p. 124, infinite horizon): in a flexible-price equilibrium with
constant velocity `V`, expected lifetime utility `∑ₜ βᵗ E[U_t]` converges to `welfareFlex`. -/
theorem hasSum_flex_welfare [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa V : ℝ} (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hφ : 0 ≤ φ) (hε : 1 < ε) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {M C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S)) M C N Y P W Q)
    (hM : ∀ t ω, 0 < M t ω) (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) :
    HasSum (fun t : ℕ => β ^ t * ∫ ω, utility φ (C t ω) (M t ω / P t ω) (N t ω) ∂μ)
      (welfareFlex β φ ε A₀ γa V) := by
  have hAp := level_pos hA hγa (techShock S)
  set K := 2 * Real.log (Nflex φ ε) - Real.log V - (markup ε)⁻¹ / (1 + φ) with hK
  have hE : ∀ t : ℕ, ∫ ω, utility φ (C t ω) (M t ω / P t ω) (N t ω) ∂μ
      = (2 * Real.log A₀ + K) + 2 * Real.log (1 + γa) * t := by
    intro t
    have hfun : (fun ω => utility φ (C t ω) (M t ω / P t ω) (N t ω))
        = fun ω => 2 * Real.log (level A₀ γa (techShock S) t ω) + K := by
      funext ω
      rw [flex_period_utility h hφ hε hAp hM hV t ω, hK]
      ring
    rw [hfun, integral_add ((integrable_log_tech S hA hγa t).const_mul 2) (integrable_const _),
      integral_const_mul, integral_log_tech S hA hγa t]
    simp only [integral_const, probReal_univ, one_smul]
    ring
  have hs := hasSum_affine (K := 2 * Real.log A₀ + K) (c := 2 * Real.log (1 + γa)) hβ0 hβ1
  convert hs using 1
  · funext t; rw [hE t]
  · rw [welfareFlex, hK]; ring

/-- Galí (2015), Ex. 4.5(c): an equilibrium with constant velocity exists only if
`Q* = β e^{σ_m²/2}/(1 + γ_m) < 1`, i.e. only if the nominal rate is strictly positive. -/
theorem flex_qstar_lt_one [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {β φ ε M₀ γm φa φv V : ℝ}
    (hM : 0 < M₀) (hγm : 0 < 1 + γm) {A C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε A (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) :
    Qstar β γm (varM S.va φa φv) < 1 := by
  have hVeq := flex_velocity S hM hγm h hV
  obtain ⟨ω₀, -⟩ := (h.euler 0).exists
  have hVpos : 0 < V := by
    rw [← hV 0 ω₀, ← h.clearing 0 ω₀]
    exact div_pos (mul_pos (h.pos_P 0 ω₀) (h.pos_C 0 ω₀)) (level_pos hM hγm _ 0 ω₀)
  rw [hVeq, velocity] at hVpos
  linarith
/-- Galí (2015), Ex. 4.5(c)–(d), p. 124, and Galí p. 32 (`Q = e^{−i}`): the constant nominal rate
`i = −log Q* = log(1 + γ_m) − log β − σ_m²/2`. -/
theorem nominalRate_eq {β γ v : ℝ} (hβ : 0 < β) (hγ : 0 < 1 + γ) :
    -Real.log (Qstar β γ v) = Real.log (1 + γ) - Real.log β - v / 2 := by
  rw [Qstar, Real.log_div (mul_pos hβ (Real.exp_pos _)).ne' hγ.ne',
    Real.log_mul hβ.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- Galí (2015), Ex. 4.5(d), p. 124: the constraint `Q_t ≤ 1` (a nonnegative nominal rate)
reads `β e^{σ_m²/2} ≤ 1 + γ_m`. -/
theorem qstar_le_one_iff {β γ v : ℝ} (hγ : 0 < 1 + γ) :
    Qstar β γ v ≤ 1 ↔ β * Real.exp (v / 2) ≤ 1 + γ := by
  rw [Qstar, div_le_one hγ]

/-- Galí (2015), Ex. 4.5(d), p. 124: the Friedman rule `i = −log Q* = 0` holds iff `Q* = 1`,
i.e. iff `1 + γ_m = β e^{σ_m²/2}`. -/
theorem friedman_iff {β γ v : ℝ} (hβ : 0 < β) (hγ : 0 < 1 + γ) :
    -Real.log (Qstar β γ v) = 0 ↔ 1 + γ = β * Real.exp (v / 2) := by
  have hQ : 0 < Qstar β γ v := div_pos (mul_pos hβ (Real.exp_pos _)) hγ
  rw [neg_eq_zero, Real.log_eq_zero]
  constructor
  · rintro (h | h | h)
    · exact absurd h hQ.ne'
    · rw [Qstar, div_eq_one_iff_eq hγ.ne'] at h; exact h.symm
    · linarith
  · intro h
    right; left
    rw [Qstar, h, div_self (mul_pos hβ (Real.exp_pos _)).ne']

/-- Galí (2015), Ex. 4.5(d), p. 124 (**imprecision**): at the Friedman rule `Q* = 1` there is no
equilibrium with constant velocity (velocity would be `0`, real balances infinite). -/
theorem not_equilibrium_at_friedman [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε M₀ γm φa φv V : ℝ} (hM : 0 < M₀) (hγm : 0 < 1 + γm)
    (hF : Qstar β γm (varM S.va φa φv) = 1) {A C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsFlexEquilibrium μ ℱ β φ ε A (level M₀ γm (moneyShock φa φv S)) C N Y P W Q) :
    ¬ ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V := fun hV => by
  have := flex_qstar_lt_one S hM hγm h hV
  linarith


/-- Galí (2015), Ex. 4.5(d): `welfareFlex = K − log V/(1 − β)` with `K` independent of
monetary policy. -/
theorem welfareFlex_eq (β φ ε A₀ γa V : ℝ) :
    welfareFlex β φ ε A₀ γa V = welfareFlex β φ ε A₀ γa 1 - Real.log V / (1 - β) := by
  simp only [welfareFlex, Real.log_one, sub_zero]
  ring

/-- Galí (2015), Ex. 4.5(d): welfare is strictly decreasing in velocity: for `V₁, V₂ > 0`,
`welfare(V₂) < welfare(V₁)` iff `V₁ < V₂`. -/
theorem welfareFlex_lt_iff {β φ ε A₀ γa V₁ V₂ : ℝ} (hβ : β < 1) (h1 : 0 < V₁)
    (h2 : 0 < V₂) :
    welfareFlex β φ ε A₀ γa V₂ < welfareFlex β φ ε A₀ γa V₁ ↔ V₁ < V₂ := by
  rw [welfareFlex_eq β φ ε A₀ γa V₂, welfareFlex_eq β φ ε A₀ γa V₁, sub_lt_sub_iff_left,
    div_lt_div_iff_of_pos_right (by linarith), Real.log_lt_log_iff h1 h2]

/-- Galí (2015), Ex. 4.5(d), p. 124: welfare is strictly decreasing in money growth `γ_m`
(among policies with an equilibrium, `Q* < 1`). -/
theorem welfare_strictAnti_gamma {β φ ε A₀ γa v γ₁ γ₂ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ₁ : 0 < 1 + γ₁) (h12 : γ₁ < γ₂) (hQ : Qstar β γ₁ v < 1) :
    welfareFlex β φ ε A₀ γa (velocity β γ₂ v) < welfareFlex β φ ε A₀ γa (velocity β γ₁ v) := by
  have hγ₂ : 0 < 1 + γ₂ := by linarith
  have hlt : Qstar β γ₂ v < Qstar β γ₁ v :=
    div_lt_div_of_pos_left (mul_pos hβ0 (Real.exp_pos _)) hγ₁ (by linarith)
  have hpos : 0 < Qstar β γ₂ v := div_pos (mul_pos hβ0 (Real.exp_pos _)) hγ₂
  rw [welfareFlex_lt_iff hβ1 (by rw [velocity]; linarith) (by rw [velocity]; linarith),
    velocity, velocity]
  linarith

/-- Galí (2015), Ex. 4.5(d), p. 124: welfare is strictly increasing in the variance `σ_m²` of
money growth (among policies with an equilibrium, `Q* < 1`): a higher variance raises
`E_t[M_t/M_{t+1}]`, the bond price and real balances. -/
theorem welfare_strictMono_var {β φ ε A₀ γa γ v₁ v₂ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < 1 + γ) (h12 : v₁ < v₂) (hQ : Qstar β γ v₂ < 1) :
    welfareFlex β φ ε A₀ γa (velocity β γ v₁) < welfareFlex β φ ε A₀ γa (velocity β γ v₂) := by
  have hlt : Qstar β γ v₁ < Qstar β γ v₂ := by
    unfold Qstar
    gcongr
  rw [welfareFlex_lt_iff hβ1 (by rw [velocity]; linarith) (by rw [velocity]; linarith),
    velocity, velocity]
  linarith

/-- Galí (2015), Ex. 4.5(d), p. 124: as a function of the constant nominal rate `i > 0`
(`Q* = e^{−i}`, `V = 1 − e^{−i}`), welfare is strictly decreasing. -/
theorem welfare_rate_strictAnti {β φ ε A₀ γa : ℝ} (hβ : β < 1) :
    StrictAntiOn (fun i => welfareFlex β φ ε A₀ γa (1 - Real.exp (-i))) (Set.Ioi 0) := by
  intro i hi j hj hij
  have hpos : ∀ x : ℝ, 0 < x → 0 < 1 - Real.exp (-x) := fun x hx => by
    have := Real.exp_lt_exp.2 (show -x < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  simp only
  rw [welfareFlex_lt_iff hβ (hpos i hi) (hpos j hj)]
  have := Real.exp_lt_exp.2 (show -j < -i by linarith)
  linarith

/-- Galí (2015), Ex. 4.5(d), p. 124: welfare is unbounded as the nominal rate falls to zero:
`welfare(1 − e^{−i}) → ∞` as `i → 0⁺`. The Friedman rule is a supremum, not attained. -/
theorem tendsto_welfare_rate {β φ ε A₀ γa : ℝ} (hβ : β < 1) :
    Tendsto (fun i => welfareFlex β φ ε A₀ γa (1 - Real.exp (-i))) (𝓝[>] 0) atTop := by
  have hV : Tendsto (fun i : ℝ => 1 - Real.exp (-i)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun i : ℝ => 1 - Real.exp (-i)) (𝓝 0) (𝓝 (1 - Real.exp (-0))) :=
        (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).tendsto 0
      simp only [neg_zero, Real.exp_zero, sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with i hi
      have := Real.exp_lt_exp.2 (show -i < 0 by simp only [Set.mem_Ioi] at hi; linarith)
      rw [Real.exp_zero] at this
      simp only [Set.mem_Ioi]
      linarith
  have hlog : Tendsto (fun i : ℝ => -Real.log (1 - Real.exp (-i)) * (1 - β)⁻¹) (𝓝[>] 0) atTop :=
    (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hV)).atTop_mul_const
      (inv_pos.2 (by linarith))
  refine (tendsto_atTop_add_const_left _ (welfareFlex β φ ε A₀ γa 1) hlog).congr fun i => ?_
  rw [welfareFlex_eq β φ ε A₀ γa (1 - Real.exp (-i))]
  ring

/-- Galí (2015), Ex. 4.5(d), p. 124 (**the optimal policy must satisfy the Friedman rule**):
every policy `(γ_m, σ_m²)` with an equilibrium (`Q* < 1`, i.e. `i > 0`) is strictly improved
upon by another admissible policy with an equilibrium; so no policy with `i > 0` is optimal. -/
theorem not_optimal_of_equilibrium {β φ ε A₀ γa γ v : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < 1 + γ) (hQ : Qstar β γ v < 1) :
    ∃ γ', 0 < 1 + γ' ∧ Qstar β γ' v < 1 ∧
      welfareFlex β φ ε A₀ γa (velocity β γ v) < welfareFlex β φ ε A₀ γa (velocity β γ' v) := by
  set q := Qstar β γ v with hq
  have hqpos : 0 < q := div_pos (mul_pos hβ0 (Real.exp_pos _)) hγ
  set q' := (q + 1) / 2 with hq'
  have hq'pos : 0 < q' := by rw [hq']; linarith
  have hb : 0 < β * Real.exp (v / 2) := mul_pos hβ0 (Real.exp_pos _)
  refine ⟨β * Real.exp (v / 2) / q' - 1, by simp only [add_sub_cancel]; positivity, ?_, ?_⟩
  · have : Qstar β (β * Real.exp (v / 2) / q' - 1) v = q' := by
      rw [Qstar, add_sub_cancel]; field_simp
    rw [this, hq']; linarith
  · have : Qstar β (β * Real.exp (v / 2) / q' - 1) v = q' := by
      rw [Qstar, add_sub_cancel]; field_simp
    rw [welfareFlex_lt_iff hβ1 (by rw [velocity, this, hq']; linarith)
      (by rw [velocity, ← hq]; linarith), velocity, velocity, this, ← hq, hq']
    linarith

/-! ### (e) Prices set one period in advance: the firm's problem -/

/-- Galí (2015), Ex. 4.5(e), p. 124: the firm's discounted real profit
`Λ_{t−1,t} (Y_t(i)/P_t)(P_t(i) − W_t/A_t)` with `Λ_{t−1,t} = β C_{t−1}/C_t`, demand
`Y_t(i) = (P_t(i)/P_t)^{−ε} Y_t` and `Y_t = C_t` equals
`β C_{t−1} P_t^{ε−1} · P_t(i)^{−ε}(P_t(i) − W_t/A_t)`. (The book prints the deflator `P_{t+1}`;
real profit at `t` is deflated by `P_t`.) -/
theorem sticky_objective_eq {β ε Cm Ct Pt x w : ℝ} (hCt : 0 < Ct) (hPt : 0 < Pt) (hx : 0 < x) :
    β * Cm / Ct * ((x / Pt) ^ (-ε) * Ct / Pt) * (x - w) =
      β * Cm * Pt ^ (ε - 1) * (x ^ (-ε) * (x - w)) := by
  rw [Real.div_rpow hx.le hPt.le, Real.rpow_neg hPt.le, Real.rpow_sub_one hPt.ne']
  field_simp

/-- Galí (2015), Ex. 4.5(e) (pull-out): for a price `x` and a factor `K` known at `t − 1`
(measurable for `G = ℱ_{t−1}`), the conditional expected profit is
`E[K x^{−ε}(x − w) | G] = K x^{−ε}(x − E[w | G])`. -/
theorem condExp_objective [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ) {ε : ℝ}
    {K w x : Ω → ℝ} (hK : StronglyMeasurable[G] K) (hx : StronglyMeasurable[G] x)
    (hobj : Integrable (fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω))) μ)
    (h1 : Integrable (fun ω => x ω ^ (-ε) * x ω) μ)
    (h2 : Integrable (fun ω => x ω ^ (-ε) * w ω) μ) (hw : Integrable w μ) :
    μ[fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω)) | G] =ᵐ[μ]
      fun ω => K ω * (x ω ^ (-ε) * (x ω - μ[w | G] ω)) := by
  have hb : StronglyMeasurable[G] (fun ω => x ω ^ (-ε)) :=
    (hx.measurable.pow_const (-ε)).stronglyMeasurable
  have ha : StronglyMeasurable[G] (fun ω => x ω ^ (-ε) * x ω) := hb.mul hx
  have hsplit : (fun ω => x ω ^ (-ε) * (x ω - w ω)) =
      (fun ω => x ω ^ (-ε) * x ω) - fun ω => x ω ^ (-ε) * w ω := by
    funext ω; simp only [Pi.sub_apply]; ring
  have hg : Integrable (fun ω => x ω ^ (-ε) * (x ω - w ω)) μ := by
    rw [hsplit]; exact h1.sub h2
  have e1 : μ[fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω)) | G] =ᵐ[μ]
      fun ω => K ω * μ[fun ω => x ω ^ (-ε) * (x ω - w ω) | G] ω :=
    condExp_mul_of_stronglyMeasurable_left (m := G) (μ := μ) hK hobj hg
  have e2 := condExp_sub h1 h2 G
  have e3 : μ[fun ω => x ω ^ (-ε) * w ω | G] =ᵐ[μ] fun ω => x ω ^ (-ε) * μ[w | G] ω :=
    condExp_mul_of_stronglyMeasurable_left (m := G) (μ := μ) hb h2 hw
  rw [condExp_of_stronglyMeasurable hG ha h1, ← hsplit] at e2
  filter_upwards [e1, e2, e3] with ω h1' h2' h3'
  rw [h1', h2', Pi.sub_apply, h3']
  ring

/-- **Ex. 4.5(e)** (Galí 2015, p. 124, optimality): with the price level and `C_{t−1}` known at
`t − 1`, the price `P_t(i) = 𝓜 E_{t−1}[W_t/A_t]` maximises the conditional expected discounted
profit `E_{t−1}[K P_t(i)^{−ε}(P_t(i) − W_t/A_t)]` (`K = β C_{t−1} P_t^{ε−1} > 0`, see
`sticky_objective_eq`) against every admissible price set at `t − 1`. -/
theorem sticky_price_optimal [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ) {ε : ℝ}
    (hε : 1 < ε) {K w x : Ω → ℝ} (hK : StronglyMeasurable[G] K) (hKpos : ∀ ω, 0 < K ω)
    (hw : Integrable w μ) (hwpos : ∀ᵐ ω ∂μ, 0 < μ[w | G] ω)
    (hx : StronglyMeasurable[G] x) (hxpos : ∀ ω, 0 < x ω)
    (hobj : Integrable (fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω))) μ)
    (h1 : Integrable (fun ω => x ω ^ (-ε) * x ω) μ)
    (h2 : Integrable (fun ω => x ω ^ (-ε) * w ω) μ)
    (hobj' : Integrable (fun ω => K ω * ((markup ε * μ[w | G] ω) ^ (-ε) *
      (markup ε * μ[w | G] ω - w ω))) μ)
    (h1' : Integrable (fun ω => (markup ε * μ[w | G] ω) ^ (-ε) * (markup ε * μ[w | G] ω)) μ)
    (h2' : Integrable (fun ω => (markup ε * μ[w | G] ω) ^ (-ε) * w ω) μ) :
    ∀ᵐ ω ∂μ, μ[fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω)) | G] ω ≤
      μ[fun ω => K ω * ((markup ε * μ[w | G] ω) ^ (-ε) * (markup ε * μ[w | G] ω - w ω)) | G] ω := by
  have hxs : StronglyMeasurable[G] (fun ω => markup ε * μ[w | G] ω) :=
    stronglyMeasurable_condExp.const_mul _
  filter_upwards [condExp_objective (mΩ := mΩ) hG hK hx hobj h1 h2 hw,
    condExp_objective (mΩ := mΩ) hG hK hxs hobj' h1' h2' hw, hwpos] with ω e1 e2 hpos
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left (markup_pricing_le hε hpos (hxpos ω)) (hKpos ω).le

/-- **Ex. 4.5(e)** (Galí 2015, p. 124, the first-order condition is necessary): a price set at
`t − 1` that does at least as well as `𝓜 E_{t−1}[W_t/A_t]` equals it almost surely; the optimal
preset price is `P_t(i) = 𝓜 E_{t−1}[W_t/A_t]`. -/
theorem sticky_price_unique [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ) {ε : ℝ}
    (hε : 1 < ε) {K w x : Ω → ℝ} (hK : StronglyMeasurable[G] K) (hKpos : ∀ ω, 0 < K ω)
    (hw : Integrable w μ) (hwpos : ∀ᵐ ω ∂μ, 0 < μ[w | G] ω)
    (hx : StronglyMeasurable[G] x) (hxpos : ∀ ω, 0 < x ω)
    (hobj : Integrable (fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω))) μ)
    (h1 : Integrable (fun ω => x ω ^ (-ε) * x ω) μ)
    (h2 : Integrable (fun ω => x ω ^ (-ε) * w ω) μ)
    (hobj' : Integrable (fun ω => K ω * ((markup ε * μ[w | G] ω) ^ (-ε) *
      (markup ε * μ[w | G] ω - w ω))) μ)
    (h1' : Integrable (fun ω => (markup ε * μ[w | G] ω) ^ (-ε) * (markup ε * μ[w | G] ω)) μ)
    (h2' : Integrable (fun ω => (markup ε * μ[w | G] ω) ^ (-ε) * w ω) μ)
    (hopt : ∀ᵐ ω ∂μ,
      μ[fun ω => K ω * ((markup ε * μ[w | G] ω) ^ (-ε) * (markup ε * μ[w | G] ω - w ω)) | G] ω ≤
        μ[fun ω => K ω * (x ω ^ (-ε) * (x ω - w ω)) | G] ω) :
    x =ᵐ[μ] fun ω => markup ε * μ[w | G] ω := by
  have hxs : StronglyMeasurable[G] (fun ω => markup ε * μ[w | G] ω) :=
    stronglyMeasurable_condExp.const_mul _
  filter_upwards [condExp_objective (mΩ := mΩ) hG hK hx hobj h1 h2 hw,
    condExp_objective (mΩ := mΩ) hG hK hxs hobj' h1' h2' hw, hwpos, hopt] with ω e1 e2 hpos ho
  rw [e1, e2] at ho
  by_contra hne
  have := mul_lt_mul_of_pos_left (markup_pricing_lt hε hpos (hxpos ω) hne) (hKpos ω)
  linarith

/-- Galí (2015), Ex. 4.5(e): with labour supply `W/P = C N^φ` and `C = A N`, real marginal cost
in nominal terms is `W/A = P N^{1+φ}`. -/
theorem wage_over_tech {φ P W A C N : ℝ} (hP : 0 < P) (hA : 0 < A) (hN : 0 < N)
    (hlab : W / P = C * N ^ φ) (hC : C = A * N) : W / A = P * N ^ (1 + φ) := by
  rw [Real.rpow_add hN, Real.rpow_one]
  rw [div_eq_iff hP.ne'] at hlab
  rw [hlab, hC]
  field_simp

/-- **Ex. 4.5(e)** (Galí 2015, p. 124): in a symmetric equilibrium with the price level `P_t`
known at `t − 1`, the pricing condition `P_t = 𝓜 E_{t−1}[W_t/A_t] = 𝓜 E_{t−1}[P_t N_t^{1+φ}]`
holds iff `E_{t−1}[N_t^{1+φ}] = 1/𝓜`: expected hours are at their flexible-price level. -/
theorem pricing_iff [IsFiniteMeasure μ] {G : MeasurableSpace Ω} {ε : ℝ} (hε : 1 < ε)
    {Pn X : Ω → ℝ} (hPn : StronglyMeasurable[G] Pn) (hPpos : ∀ ω, 0 < Pn ω)
    (hX : Integrable X μ) (hPX : Integrable (fun ω => Pn ω * X ω) μ) :
    (Pn =ᵐ[μ] fun ω => markup ε * μ[fun ω => Pn ω * X ω | G] ω) ↔
      μ[X | G] =ᵐ[μ] fun _ => (markup ε)⁻¹ := by
  have e : μ[fun ω => Pn ω * X ω | G] =ᵐ[μ] fun ω => Pn ω * μ[X | G] ω :=
    condExp_mul_of_stronglyMeasurable_left (m := G) (μ := μ) hPn hPX hX
  have hM := markup_pos hε
  constructor
  · intro h
    filter_upwards [h, e] with ω h1 h2
    rw [h2] at h1
    have hp := hPpos ω
    field_simp
    nlinarith [h1]
  · intro h
    filter_upwards [h, e] with ω h1 h2
    rw [h2, h1]
    field_simp

/-! ### (e) The sticky-price equilibrium -/

omit mΩ in
/-- Galí (2015), Ex. 4.5: levels built from adapted innovations are adapted. -/
theorem measurable_level {m : MeasurableSpace Ω} (ℱ' : Filtration ℕ m) {X₀ γ : ℝ}
    {ε : ℕ → Ω → ℝ} (hε : ∀ s, Measurable[ℱ' s] (ε s)) (t : ℕ) :
    Measurable[ℱ' t] (level X₀ γ ε t) := by
  have hs : Measurable[ℱ' t] fun ω => ∑ s ∈ Finset.range t, ε (s + 1) ω :=
    Finset.measurable_sum _ fun s hs =>
      (hε (s + 1)).mono (ℱ'.mono (by simp only [Finset.mem_range] at hs; omega)) le_rfl
  exact (Real.measurable_exp.comp hs).const_mul _

/-- Galí (2015), Ex. 4.5: technology innovations are adapted. -/
theorem techShock_measurable (S : ShockPair μ ℱ) (s : ℕ) : Measurable[ℱ s] (techShock S s) :=
  measurable_fst.comp (S.adapted s)

/-- Galí (2015), Ex. 4.5: money innovations are adapted. -/
theorem moneyShock_measurable (S : ShockPair μ ℱ) (φa φv : ℝ) (s : ℕ) :
    Measurable[ℱ s] (moneyShock φa φv S s) :=
  ((measurable_fst.comp (S.adapted s)).const_mul φa).add
    ((measurable_snd.comp (S.adapted s)).const_mul φv)

/-- Galí (2015), Ex. 4.5(e): the innovation `ε^m_t − ε^a_t = (φ_a − 1) ε^a_t + φ_v ν_t` that
moves employment when prices are preset. -/
def gapShock (φa φv : ℝ) (S : ShockPair μ ℱ) : ℕ → Ω → ℝ :=
  fun t ω => (φa - 1) * (S.Z t ω).1 + φv * (S.Z t ω).2

/-- Galí (2015), Ex. 4.5(e): `ε^m_t − ε^a_t` is the gap innovation. -/
theorem moneyShock_sub_techShock (S : ShockPair μ ℱ) (φa φv : ℝ) (t : ℕ) (ω : Ω) :
    moneyShock φa φv S t ω - techShock S t ω = gapShock φa φv S t ω := by
  simp only [moneyShock, techShock, gapShock]; ring

variable (μ ℱ β φ ε A M C N Y P W Q)

/-- Galí (2015), Ex. 4.5(e), p. 124: an equilibrium when prices are set one period in advance.
Household conditions as in (a); `C = Y = A N`; the price level `P_{t+1}` is known at `t`
(`P_0` is set before the economy starts); hours are integrable; and the firms' first-order
condition, in the form `E_t[N_{t+1}^{1+φ}] = 1/𝓜` (`pricing_iff`), holds. -/
structure IsStickyEquilibrium where
  /-- Consumption is positive. -/
  pos_C : ∀ t ω, 0 < C t ω
  /-- Hours are positive. -/
  pos_N : ∀ t ω, 0 < N t ω
  /-- The price level is positive. -/
  pos_P : ∀ t ω, 0 < P t ω
  /-- Labour supply: `W/P = C N^φ`. -/
  labour : ∀ t ω, W t ω / P t ω = C t ω * N t ω ^ φ
  /-- Money demand: `C = (1 − Q)(M/P)`. -/
  money : ∀ t ω, C t ω = (1 - Q t ω) * (M t ω / P t ω)
  /-- The Euler equation. -/
  euler : ∀ t, Q t =ᵐ[μ] eulerRHS μ ℱ β C P t
  /-- Prices are set one period in advance: `P_{t+1}` is known at `t`. -/
  preset : ∀ t, Measurable[ℱ t] (P (t + 1))
  /-- The initial price level is set before the shocks: it is deterministic. -/
  preset0 : ∀ ω ω', P 0 ω = P 0 ω'
  /-- Hours to the power `1 + φ` are integrable. -/
  integrable_hours : ∀ t, Integrable (fun ω => N t ω ^ (1 + φ)) μ
  /-- The firms' first-order condition: `E_t[N_{t+1}^{1+φ}] = 1/𝓜`. -/
  pricing : ∀ t, μ[fun ω => N (t + 1) ω ^ (1 + φ) | ℱ t] =ᵐ[μ] fun _ => (markup ε)⁻¹
  /-- The first-order condition at date 0, with no information: `E[N_0^{1+φ}] = 1/𝓜`. -/
  pricing0 : ∫ ω, N 0 ω ^ (1 + φ) ∂μ = (markup ε)⁻¹
  /-- Technology: `Y = A N`. -/
  technology : ∀ t ω, Y t ω = A t ω * N t ω
  /-- Goods-market clearing: `C = Y`. -/
  clearing : ∀ t ω, C t ω = Y t ω

variable {μ ℱ β φ ε A M C N Y P W Q}

/-- **Ex. 4.5(e)** (Galí 2015, p. 124, solving exactly): in a sticky-price equilibrium with
constant velocity `V`, employment is
`N_{t+1} = 𝓜^{−1/(1+φ)} exp((ε^m_{t+1} − ε^a_{t+1}) − (1+φ) s²/2)`, `s² = var(ε^m − ε^a)`,
almost surely. -/
theorem sticky_employment [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) (t : ℕ) :
    N (t + 1) =ᵐ[μ] fun ω => Nflex φ ε *
      Real.exp (gapShock φa φv S (t + 1) ω - (1 + φ) * varX S.va φa φv / 2) := by
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have h1φ : 0 < 1 + φ := by linarith
  obtain ⟨ω₀, -⟩ := (h.euler 0).exists
  have hVpos : 0 < V := by
    rw [← hV 0 ω₀]
    exact div_pos (mul_pos (h.pos_P 0 ω₀) (by rw [← h.clearing]; exact h.pos_C 0 ω₀))
      (hMp 0 ω₀)
  have hNeq : ∀ s ω, N s ω = V * level M₀ γm (moneyShock φa φv S) s ω /
      (P s ω * level A₀ γa (techShock S) s ω) := fun s ω => by
    have e := hV s ω
    rw [h.technology s ω] at e
    rw [← e]
    field_simp [(hMp s ω).ne', (h.pos_P s ω).ne', (hAp s ω).ne']
  set R : Ω → ℝ := fun ω => V * level M₀ γm (moneyShock φa φv S) t ω * (1 + γm) /
      (P (t + 1) ω * (level A₀ γa (techShock S) t ω * (1 + γa)))
    with hR
  have hRpos : ∀ ω, 0 < R ω := fun ω => div_pos (mul_pos (mul_pos hVpos (hMp t ω)) hγm)
    (mul_pos (h.pos_P (t + 1) ω) (mul_pos (hAp t ω) hγa))
  have hNR : ∀ ω, N (t + 1) ω = R ω * Real.exp (gapShock φa φv S (t + 1) ω) := fun ω => by
    rw [hNeq, level_succ, level_succ, ← moneyShock_sub_techShock, Real.exp_sub]
    simp only [hR]
    field_simp [(hAp t ω).ne', (hMp t ω).ne', (h.pos_P (t + 1) ω).ne']
  have hRmeas : Measurable[ℱ t] R :=
    (((measurable_const.mul (measurable_level ℱ (moneyShock_measurable S φa φv) t)).mul_const
      _).div ((h.preset t).mul ((measurable_level ℱ (techShock_measurable S) t).mul_const _)))
  set a := (1 + φ) * (φa - 1) with ha
  set b := (1 + φ) * φv with hb
  have hpow : ∀ ω, N (t + 1) ω ^ (1 + φ) =
      R ω ^ (1 + φ) * Real.exp (a * (S.Z (t + 1) ω).1 + b * (S.Z (t + 1) ω).2) := fun ω => by
    rw [hNR, Real.mul_rpow (hRpos ω).le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    simp only [gapShock, ha, hb]; ring
  have hE := condExp_shock S (g := fun q : ℝ × ℝ => Real.exp (a * q.1 + b * q.2))
    (by fun_prop) t
  have hint := h.integrable_hours (t + 1)
  have hfun : (fun ω => N (t + 1) ω ^ (1 + φ)) =
      (fun ω => R ω ^ (1 + φ)) * fun ω => Real.exp (a * (S.Z (t + 1) ω).1 +
        b * (S.Z (t + 1) ω).2) := by
    funext ω; rw [hpow]; rfl
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := ℱ t) (μ := μ)
    (hRmeas.pow_const (1 + φ)).stronglyMeasurable (hfun ▸ hint) (integrable_exp_shock S a b (t + 1))
  have hpr := h.pricing t
  rw [hfun] at hpr
  filter_upwards [hpull, hE, hpr] with ω e1 e2 e3
  rw [e3, Pi.mul_apply, e2, integral_exp_pair] at e1
  -- e1 : 𝓜⁻¹ = R ω ^ (1+φ) * exp((a² va + b²)/2)
  have hkey : (a ^ 2 * S.va + b ^ 2) / 2 = (1 + φ) ^ 2 * varX S.va φa φv / 2 := by
    simp only [ha, hb, varX]; ring
  rw [hkey] at e1
  have hR1 : R ω ^ (1 + φ) = (markup ε)⁻¹ * Real.exp (-((1 + φ) ^ 2 * varX S.va φa φv / 2)) := by
    rw [Real.exp_neg, e1]
    field_simp
  have hRval : R ω = Nflex φ ε * Real.exp (-((1 + φ) * varX S.va φa φv / 2)) := by
    rw [← Real.rpow_rpow_inv (hRpos ω).le h1φ.ne', hR1,
      Real.mul_rpow (inv_pos.2 (markup_pos hε)).le (Real.exp_pos _).le, ← Real.exp_mul, Nflex]
    congr 2
    field_simp
  rw [hNR, hRval, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Ex. 4.5(e)** (Galí 2015, p. 124): at date 0 (price set with no information and
deterministic initial conditions) employment is at its flexible-price level. -/
theorem sticky_employment_zero [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) (ω : Ω) :
    N 0 ω = Nflex φ ε := by
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hNeq : ∀ ω, N 0 ω = V * M₀ / (P 0 ω * A₀) := fun ω => by
    have e := hV 0 ω
    rw [h.technology 0 ω, level_zero, level_zero] at e
    rw [← e]
    field_simp [hM.ne', (h.pos_P 0 ω).ne', hA.ne']
  have hconst : ∀ ω', N 0 ω' = N 0 ω := fun ω' => by rw [hNeq, hNeq, h.preset0 ω' ω]
  have h0 := h.pricing0
  rw [show (fun ω' => N 0 ω' ^ (1 + φ)) = fun _ => N 0 ω ^ (1 + φ) by
    funext ω'; rw [hconst], integral_const, probReal_univ, one_smul] at h0
  rw [Nflex, ← h0, Real.rpow_rpow_inv (h.pos_N 0 ω).le (by linarith)]

/-- **Ex. 4.5(e)** (Galí 2015, p. 124): in a sticky-price equilibrium with constant velocity,
`V = 1 − β e^{σ_m²/2}/(1 + γ_m)`, as under flexible prices. -/
theorem sticky_velocity [IsProbabilityMeasure μ] (S : ShockPair μ ℱ) {β φ ε M₀ γm φa φv V : ℝ}
    (hM : 0 < M₀) (hγm : 0 < 1 + γm) {A C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε A (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) :
    V = velocity β γm (varM S.va φa φv) :=
  velocity_of_euler S β hM hγm h.pos_C h.pos_P h.money h.euler fun t ω => by
    rw [h.clearing t ω]; exact hV t ω

/-- **Ex. 4.5(e)** (Galí 2015, p. 124): output is `Y_t = A_t N_t` and real balances are
`M_t/P_t = A_t N_t / V`. -/
theorem sticky_output_balances {β φ ε V : ℝ} {A M C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε A M C N Y P W Q) (hM : ∀ t ω, 0 < M t ω)
    (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) (t : ℕ) (ω : Ω) :
    Y t ω = A t ω * N t ω ∧ M t ω / P t ω = A t ω * N t ω / V := by
  refine ⟨h.technology t ω, ?_⟩
  rw [← h.technology t ω, ← hV t ω]
  field_simp [(hM t ω).ne', (h.pos_P t ω).ne']
  have := (h.clearing t ω).symm ▸ h.pos_C t ω
  field_simp [this.ne']

/-- Galí (2015), Ex. 4.5(e): the closed-form sticky-price employment
`N_0 = 𝓜^{−1/(1+φ)}`, `N_{t+1} = 𝓜^{−1/(1+φ)} exp((ε^m_{t+1} − ε^a_{t+1}) − (1+φ) s²/2)`. -/
noncomputable def stickyN (φ ε φa φv : ℝ) (S : ShockPair μ ℱ) : ℕ → Ω → ℝ
  | 0 => fun _ => Nflex φ ε
  | t + 1 => fun ω => Nflex φ ε *
      Real.exp (gapShock φa φv S (t + 1) ω - (1 + φ) * varX S.va φa φv / 2)

/-- Galí (2015), Ex. 4.5(e): sticky-price employment is positive. -/
theorem stickyN_pos {φ ε φa φv : ℝ} (hε : 1 < ε) (S : ShockPair μ ℱ) (t : ℕ) (ω : Ω) :
    0 < stickyN φ ε φa φv S t ω := by
  cases t with
  | zero => exact Nflex_pos hε
  | succ t => exact mul_pos (Nflex_pos hε) (Real.exp_pos _)

/-- Galí (2015), Ex. 4.5(e):
`N_{t+1}^{1+φ} = 𝓜⁻¹ e^{−(1+φ)² s²/2} e^{(1+φ)(φ_a − 1) ε^a_{t+1} + (1+φ) φ_v ν_{t+1}}`. -/
theorem stickyN_rpow_succ {φ ε φa φv : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (S : ShockPair μ ℱ)
    (t : ℕ) (ω : Ω) :
    stickyN φ ε φa φv S (t + 1) ω ^ (1 + φ) =
      (markup ε)⁻¹ * Real.exp (-((1 + φ) ^ 2 * varX S.va φa φv / 2)) *
        Real.exp ((1 + φ) * (φa - 1) * (S.Z (t + 1) ω).1 + (1 + φ) * φv * (S.Z (t + 1) ω).2) := by
  simp only [stickyN]
  rw [Real.mul_rpow (Nflex_pos hε).le (Real.exp_pos _).le, Nflex_rpow hφ hε, ← Real.exp_mul,
    mul_assoc, ← Real.exp_add]
  congr 2
  simp only [gapShock]
  ring

/-- **Ex. 4.5(e)** (Galí 2015, p. 124, existence): if `β e^{σ_m²/2} < 1 + γ_m`, the allocation
`N = stickyN`, `C = Y = A N`, `P = V M/(A N)`, `W = P C N^φ`, `Q = Q*`, `V = 1 − Q*`, is an
exact equilibrium with prices set one period in advance. -/
theorem sticky_candidate [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀) (hγa : 0 < 1 + γa)
    (hM : 0 < M₀) (hγm : 0 < 1 + γm) (hQ : Qstar β γm (varM S.va φa φv) < 1) :
    IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S)) (level M₀ γm (moneyShock φa φv S))
      (fun t ω => level A₀ γa (techShock S) t ω * stickyN φ ε φa φv S t ω)
      (stickyN φ ε φa φv S)
      (fun t ω => level A₀ γa (techShock S) t ω * stickyN φ ε φa φv S t ω)
      (fun t ω => velocity β γm (varM S.va φa φv) * level M₀ γm (moneyShock φa φv S) t ω /
        (level A₀ γa (techShock S) t ω * stickyN φ ε φa φv S t ω))
      (fun t ω => velocity β γm (varM S.va φa φv) * level M₀ γm (moneyShock φa φv S) t ω /
        (level A₀ γa (techShock S) t ω * stickyN φ ε φa φv S t ω) *
          (level A₀ γa (techShock S) t ω * stickyN φ ε φa φv S t ω) *
          stickyN φ ε φa φv S t ω ^ φ)
      (fun _ _ => Qstar β γm (varM S.va φa φv)) := by
  set V := velocity β γm (varM S.va φa φv) with hVdef
  have hV : 0 < V := by rw [hVdef, velocity]; linarith
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hNp := stickyN_pos (φ := φ) (φa := φa) (φv := φv) hε S
  set a := (1 + φ) * (φa - 1) with ha
  set b := (1 + φ) * φv with hb
  set k := (markup ε)⁻¹ * Real.exp (-((1 + φ) ^ 2 * varX S.va φa φv / 2)) with hk
  have hkey : k * Real.exp ((a ^ 2 * S.va + b ^ 2) / 2) = (markup ε)⁻¹ := by
    rw [hk, mul_assoc, ← Real.exp_add]
    rw [show -((1 + φ) ^ 2 * varX S.va φa φv / 2) + (a ^ 2 * S.va + b ^ 2) / 2 = 0 by
      simp only [ha, hb, varX]; ring, Real.exp_zero, mul_one]
  have hpowfun : ∀ t, (fun ω => stickyN φ ε φa φv S (t + 1) ω ^ (1 + φ)) =
      fun ω => (fun q : ℝ × ℝ => k * Real.exp (a * q.1 + b * q.2)) (S.Z (t + 1) ω) := by
    intro t; funext ω; rw [stickyN_rpow_succ hφ hε S t ω]
  refine ⟨fun t ω => mul_pos (hAp t ω) (hNp t ω), hNp, fun t ω => div_pos (mul_pos hV (hMp t ω))
    (mul_pos (hAp t ω) (hNp t ω)), fun t ω => ?_, fun t ω => ?_, fun t => ?_, fun t => ?_,
    fun ω ω' => ?_, fun t => ?_, fun t => ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  · field_simp [(hAp t ω).ne', (hMp t ω).ne', (hNp t ω).ne', hV.ne']
  · rw [show 1 - Qstar β γm (varM S.va φa φv) = V from rfl]
    field_simp [(hAp t ω).ne', (hMp t ω).ne', (hNp t ω).ne', hV.ne']
  · refine (eulerRHS_of_const_velocity S β hM.ne' hγm hV.ne' (fun t ω => ?_) t).symm
    field_simp [(hAp t ω).ne', (hNp t ω).ne']
  · have hfun : (fun ω => V * level M₀ γm (moneyShock φa φv S) (t + 1) ω /
        (level A₀ γa (techShock S) (t + 1) ω * stickyN φ ε φa φv S (t + 1) ω)) =
        fun ω => V * level M₀ γm (moneyShock φa φv S) t ω * (1 + γm) *
          Real.exp ((1 + φ) * varX S.va φa φv / 2) /
          (level A₀ γa (techShock S) t ω * (1 + γa) * Nflex φ ε) := by
      funext ω
      have hsplit : moneyShock φa φv S (t + 1) ω =
          techShock S (t + 1) ω + gapShock φa φv S (t + 1) ω := by
        rw [← moneyShock_sub_techShock]; ring
      simp only [stickyN]
      rw [level_succ, level_succ, hsplit, Real.exp_add, Real.exp_sub]
      field_simp [(hAp t ω).ne', (hMp t ω).ne', (Nflex_pos (φ := φ) hε).ne']
    change Measurable[ℱ t] (fun ω => V * level M₀ γm (moneyShock φa φv S) (t + 1) ω /
        (level A₀ γa (techShock S) (t + 1) ω * stickyN φ ε φa φv S (t + 1) ω))
    rw [hfun]
    exact ((((measurable_level ℱ (moneyShock_measurable S φa φv) t).const_mul V).mul_const
      _).mul_const _).div (((measurable_level ℱ (techShock_measurable S) t).mul_const
        _).mul_const _)
  · simp only [stickyN, level_zero]
  · cases t with
    | zero => exact integrable_const (Nflex φ ε ^ (1 + φ))
    | succ t =>
      rw [hpowfun t]
      exact (integrable_exp_shock S a b (t + 1)).const_mul k
  · rw [hpowfun t]
    refine (condExp_shock S (g := fun q : ℝ × ℝ => k * Real.exp (a * q.1 + b * q.2))
      (by fun_prop) t).trans (Filter.Eventually.of_forall fun _ => ?_)
    simp only
    rw [integral_const_mul, integral_exp_pair, hkey]
  · simp only [stickyN]
    rw [integral_const, probReal_univ, one_smul, Nflex_rpow hφ hε]

/-! ### (f) Expected utility with prices set in advance -/

/-- Galí (2015), Ex. 4.5(f), p. 124: in a sticky-price equilibrium with constant velocity `V`,
period utility is `2 log A_t + 2 log N_t − log V − N_t^{1+φ}/(1+φ)`. -/
theorem sticky_period_utility {β φ ε V : ℝ} {A M C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε A M C N Y P W Q) (hA : ∀ t ω, 0 < A t ω)
    (hM : ∀ t ω, 0 < M t ω) (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) (hVpos : 0 < V)
    (t : ℕ) (ω : Ω) :
    utility φ (C t ω) (M t ω / P t ω) (N t ω) = 2 * Real.log (A t ω) +
      2 * Real.log (N t ω) - Real.log V - N t ω ^ (1 + φ) / (1 + φ) := by
  have hb := (sticky_output_balances h hM hV t ω).2
  have hC : C t ω = A t ω * N t ω := (h.clearing t ω).trans (h.technology t ω)
  have hAN := mul_pos (hA t ω) (h.pos_N t ω)
  rw [utility, hC, hb, Real.log_div hAN.ne' hVpos.ne',
    Real.log_mul (hA t ω).ne' (h.pos_N t ω).ne']
  ring

/-- Galí (2015), Ex. 4.5(f): expected lifetime utility with prices set in advance,
`welfareFlex − (1 + φ) s² β/(1 − β)`: the flexible-price value minus the cost
`(1 + φ) s²` per period of employment fluctuations. -/
noncomputable def stickyWelfare (β φ ε A₀ γa V s2 : ℝ) : ℝ :=
  welfareFlex β φ ε A₀ γa V - (1 + φ) * s2 * β / (1 - β)

/-- **Ex. 4.5(f)** (Galí 2015, p. 124): in a sticky-price equilibrium with constant velocity,
expected utility at date `t + 1` is
`2 E log A_{t+1} + 2 log N − (1+φ) s² − log V − 𝓜⁻¹/(1+φ)` (Gaussian moments). -/
theorem sticky_expected_utility_succ [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) (hVpos : 0 < V)
    (t : ℕ) :
    ∫ ω, utility φ (C (t + 1) ω) (level M₀ γm (moneyShock φa φv S) (t + 1) ω / P (t + 1) ω)
        (N (t + 1) ω) ∂μ =
      2 * (Real.log A₀ + (t + 1 : ℕ) * Real.log (1 + γa)) + 2 * Real.log (Nflex φ ε) -
        (1 + φ) * varX S.va φa φv - Real.log V - (markup ε)⁻¹ / (1 + φ) := by
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hNae := sticky_employment S hφ hε hA hγa hM hγm h hV t
  have hlogN : (fun ω => Real.log (N (t + 1) ω)) =ᵐ[μ] fun ω =>
      (Real.log (Nflex φ ε) - (1 + φ) * varX S.va φa φv / 2) +
        ((φa - 1) * (S.Z (t + 1) ω).1 + φv * (S.Z (t + 1) ω).2) := by
    filter_upwards [hNae] with ω hω
    rw [hω, Real.log_mul (Nflex_pos hε).ne' (Real.exp_pos _).ne', Real.log_exp]
    simp only [gapShock]; ring
  have hlogNint : Integrable (fun ω => Real.log (N (t + 1) ω)) μ :=
    ((integrable_const _).add (integrable_lin S (φa - 1) φv (t + 1))).congr hlogN.symm
  have hlogNE : ∫ ω, Real.log (N (t + 1) ω) ∂μ =
      Real.log (Nflex φ ε) - (1 + φ) * varX S.va φa φv / 2 := by
    rw [integral_congr_ae hlogN, integral_add (integrable_const _)
      (integrable_lin S (φa - 1) φv (t + 1)), integral_lin, integral_const, probReal_univ,
      one_smul, add_zero]
  have hpowE : ∫ ω, N (t + 1) ω ^ (1 + φ) ∂μ = (markup ε)⁻¹ := by
    rw [← integral_condExp (ℱ.le t), integral_congr_ae (h.pricing t), integral_const,
      probReal_univ, one_smul]
  have hfun : (fun ω => utility φ (C (t + 1) ω)
      (level M₀ γm (moneyShock φa φv S) (t + 1) ω / P (t + 1) ω) (N (t + 1) ω)) =
      fun ω => (2 * Real.log (level A₀ γa (techShock S) (t + 1) ω) +
        2 * Real.log (N (t + 1) ω) - Real.log V) - N (t + 1) ω ^ (1 + φ) / (1 + φ) := by
    funext ω
    rw [sticky_period_utility h hAp hMp hV hVpos]
  have i1 : Integrable (fun ω => 2 * Real.log (level A₀ γa (techShock S) (t + 1) ω)) μ :=
    (integrable_log_tech S hA hγa (t + 1)).const_mul 2
  have i2 : Integrable (fun ω => 2 * Real.log (N (t + 1) ω)) μ := hlogNint.const_mul 2
  have i12 : Integrable (fun ω => 2 * Real.log (level A₀ γa (techShock S) (t + 1) ω) +
      2 * Real.log (N (t + 1) ω)) μ := i1.add i2
  have i123 : Integrable (fun ω => 2 * Real.log (level A₀ γa (techShock S) (t + 1) ω) +
      2 * Real.log (N (t + 1) ω) - Real.log V) μ := i12.sub (integrable_const _)
  have i4 : Integrable (fun ω => N (t + 1) ω ^ (1 + φ) / (1 + φ)) μ :=
    (h.integrable_hours (t + 1)).div_const _
  rw [hfun, integral_sub i123 i4, integral_sub i12 (integrable_const _), integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_div, integral_log_tech S hA hγa (t + 1),
    hlogNE, hpowE, integral_const, probReal_univ, one_smul]
  ring

/-- **Ex. 4.5(f)** (Galí 2015, p. 124): at date 0 expected utility is
`2 log A₀ + 2 log N − log V − 𝓜⁻¹/(1+φ)` (employment is at its flexible-price level). -/
theorem sticky_expected_utility_zero [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) (hVpos : 0 < V) :
    ∫ ω, utility φ (C 0 ω) (level M₀ γm (moneyShock φa φv S) 0 ω / P 0 ω) (N 0 ω) ∂μ =
      2 * Real.log A₀ + 2 * Real.log (Nflex φ ε) - Real.log V - (markup ε)⁻¹ / (1 + φ) := by
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hfun : (fun ω => utility φ (C 0 ω) (level M₀ γm (moneyShock φa φv S) 0 ω / P 0 ω)
      (N 0 ω)) = fun _ => 2 * Real.log A₀ + 2 * Real.log (Nflex φ ε) - Real.log V -
        (markup ε)⁻¹ / (1 + φ) := by
    funext ω
    have hN := sticky_employment_zero S hφ hA hγa hM hγm h hV ω
    rw [sticky_period_utility h hAp hMp hV hVpos, hN, level_zero]
    rw [Nflex_rpow hφ hε]
  rw [hfun, integral_const, probReal_univ, one_smul]

/-- **Ex. 4.5(f)** (Galí 2015, p. 124, infinite horizon): in a sticky-price equilibrium with
constant velocity `V`, expected lifetime utility `∑ₜ βᵗ E[U_t]` converges to
`stickyWelfare = welfareFlex − (1 + φ) s² β/(1 − β)`, `s² = (φ_a − 1)² σ_a² + φ_v²`. -/
theorem hasSum_sticky_welfare [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) :
    HasSum (fun t : ℕ => β ^ t * ∫ ω, utility φ (C t ω)
        (level M₀ γm (moneyShock φa φv S) t ω / P t ω) (N t ω) ∂μ)
      (stickyWelfare β φ ε A₀ γa V (varX S.va φa φv)) := by
  have hVpos : 0 < V := by
    obtain ⟨ω₀, -⟩ := (h.euler 0).exists
    rw [← hV 0 ω₀, ← h.clearing 0 ω₀]
    exact div_pos (mul_pos (h.pos_P 0 ω₀) (h.pos_C 0 ω₀)) (level_pos hM hγm _ 0 ω₀)
  set K := 2 * Real.log A₀ + 2 * Real.log (Nflex φ ε) - Real.log V - (markup ε)⁻¹ / (1 + φ)
    with hK
  set c := 2 * Real.log (1 + γa) with hc
  set d := (1 + φ) * varX S.va φa φv with hd
  have hterm : ∀ t : ℕ, β ^ t * ∫ ω, utility φ (C t ω)
      (level M₀ γm (moneyShock φa φv S) t ω / P t ω) (N t ω) ∂μ =
      β ^ t * (K + c * t) - d * β ^ t + d * (if t = 0 then 1 else 0) := by
    intro t
    cases t with
    | zero =>
      rw [sticky_expected_utility_zero S hφ hε hA hγa hM hγm h hV hVpos]
      simp only [pow_zero, one_mul, ↓reduceIte, CharP.cast_eq_zero, mul_zero, add_zero, hK]
      ring
    | succ t =>
      rw [sticky_expected_utility_succ S hφ hε hA hγa hM hγm h hV hVpos t]
      simp only [Nat.succ_ne_zero, ↓reduceIte, mul_zero, add_zero, hK, hc, hd]
      ring
  have h1 := hasSum_affine (K := K) (c := c) hβ0 hβ1
  have h2 := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left d
  have h3 := (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).mul_left d
  have hne : (1 - β) ≠ 0 := by linarith
  convert (h1.sub h2).add h3 using 1
  · funext t
    rw [hterm t]
  · rw [stickyWelfare, welfareFlex, hK, hc, hd]
    field_simp
    ring

/-! ### (g) Optimal monetary policy within the class of money supply rules -/

/-- Galí (2015), Ex. 4.5(g), p. 124: expected lifetime utility under the rule
`(γ_m, φ_a, φ_v)`: velocity `V = 1 − β e^{σ_m²/2}/(1 + γ_m)` with `σ_m² = φ_a² σ_a² + φ_v²`,
and employment variance `s² = (φ_a − 1)² σ_a² + φ_v²`. -/
noncomputable def policyWelfare (β φ ε A₀ γa va γm φa φv : ℝ) : ℝ :=
  stickyWelfare β φ ε A₀ γa (velocity β γm (varM va φa φv)) (varX va φa φv)

/-- Galí (2015), Ex. 4.5(f)–(g): prices set in advance never do better than flexible prices with
the same velocity: `stickyWelfare ≤ welfareFlex`. -/
theorem stickyWelfare_le_flex {β φ ε A₀ γa V s2 : ℝ} (hφ : 0 ≤ φ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hs : 0 ≤ s2) : stickyWelfare β φ ε A₀ γa V s2 ≤ welfareFlex β φ ε A₀ γa V := by
  unfold stickyWelfare
  have : 0 ≤ (1 + φ) * s2 * β / (1 - β) := by
    apply div_nonneg _ (by linarith); positivity
  linarith

/-- Galí (2015), Ex. 4.5(f)–(g): for `0 < β < 1` the sticky-price welfare equals the
flexible-price welfare iff `s² = 0`. -/
theorem stickyWelfare_eq_flex_iff {β φ ε A₀ γa V s2 : ℝ} (hφ : 0 ≤ φ) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    stickyWelfare β φ ε A₀ γa V s2 = welfareFlex β φ ε A₀ γa V ↔ s2 = 0 := by
  unfold stickyWelfare
  have hpos : 0 < (1 + φ) * β / (1 - β) := div_pos (by positivity) (by linarith)
  constructor
  · intro h
    have : (1 + φ) * s2 * β / (1 - β) = 0 := by linarith
    rw [show (1 + φ) * s2 * β / (1 - β) = s2 * ((1 + φ) * β / (1 - β)) by ring] at this
    exact (mul_eq_zero.1 this).resolve_right hpos.ne'
  · rintro rfl; simp

/-- Galí (2015), Ex. 4.5(g): with `σ_a² > 0`, the employment variance vanishes,
`(φ_a − 1)² σ_a² + φ_v² = 0`, iff `φ_a = 1` and `φ_v = 0`. -/
theorem varX_eq_zero_iff {va φa φv : ℝ} (hva : 0 < va) :
    varX va φa φv = 0 ↔ φa = 1 ∧ φv = 0 := by
  unfold varX
  constructor
  · intro h
    have h1 : (φa - 1) ^ 2 * va = 0 := by nlinarith [sq_nonneg (φa - 1), sq_nonneg φv]
    have h2 : φv ^ 2 = 0 := by nlinarith [sq_nonneg (φa - 1), sq_nonneg φv]
    refine ⟨?_, pow_eq_zero_iff (two_ne_zero) |>.1 h2⟩
    have := (mul_eq_zero.1 h1).resolve_right hva.ne'
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linarith
  · rintro ⟨rfl, rfl⟩; ring

/-- Galí (2015), Ex. 4.5(g): for every money growth rate the welfare of the rule is
`welfareFlex(V) − (1 + φ) s² β/(1 − β)`; with the same bond price `Q*` (hence the same nominal
rate and velocity) the rule `φ_a = 1, φ_v = 0` is at least as good as any `(φ_a, φ_v)`, and
strictly better unless `φ_a = 1, φ_v = 0` (for `σ_a² > 0`). -/
theorem stabilization_optimal {β φ ε A₀ γa va γm φa φv γm' : ℝ} (hφ : 0 ≤ φ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hva : 0 < va)
    (hQ : Qstar β γm' (varM va 1 0) = Qstar β γm (varM va φa φv)) :
    policyWelfare β φ ε A₀ γa va γm φa φv ≤ policyWelfare β φ ε A₀ γa va γm' 1 0 ∧
      (¬ (φa = 1 ∧ φv = 0) →
        policyWelfare β φ ε A₀ γa va γm φa φv < policyWelfare β φ ε A₀ γa va γm' 1 0) := by
  have hv : velocity β γm' (varM va 1 0) = velocity β γm (varM va φa φv) := by
    rw [velocity, velocity, hQ]
  have h10 : varX va 1 0 = 0 := by unfold varX; ring
  have hflex : policyWelfare β φ ε A₀ γa va γm' 1 0 =
      welfareFlex β φ ε A₀ γa (velocity β γm (varM va φa φv)) := by
    rw [policyWelfare, hv, h10, (stickyWelfare_eq_flex_iff hφ hβ0 hβ1).2 rfl]
  rw [hflex]
  refine ⟨stickyWelfare_le_flex hφ hβ0.le hβ1 (varX_nonneg hva.le _ _), fun hne => ?_⟩
  refine lt_of_le_of_ne (stickyWelfare_le_flex hφ hβ0.le hβ1 (varX_nonneg hva.le _ _))
    fun heq => hne ?_
  exact (varX_eq_zero_iff hva).1 ((stickyWelfare_eq_flex_iff hφ hβ0 hβ1).1 heq)

/-- Galí (2015), Ex. 4.5(g): any bond price `Q* > 0` can be attained by the rule with
`φ_a = 1, φ_v = 0` (choosing `1 + γ_m = β e^{σ_a²/2}/Q*`). -/
theorem exists_gamma_for_qstar {β va q : ℝ} (hβ0 : 0 < β) (hq : 0 < q) :
    ∃ γm, 0 < 1 + γm ∧ Qstar β γm (varM va 1 0) = q := by
  refine ⟨β * Real.exp (varM va 1 0 / 2) / q - 1, by
    simp only [add_sub_cancel]; positivity, ?_⟩
  rw [Qstar, add_sub_cancel]
  field_simp

/-- **Ex. 4.5(g)** (Galí 2015, p. 124): every rule `(γ_m, φ_a, φ_v)` with `(φ_a, φ_v) ≠ (1, 0)`
and an equilibrium is strictly improved upon by the rule with `φ_a = 1` (money accommodates
technology one for one), `φ_v = 0` (no noise) and the same nominal interest rate. -/
theorem stabilization_improves {β φ ε A₀ γa va γm φa φv : ℝ} (hφ : 0 ≤ φ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hva : 0 < va) (hγm : 0 < 1 + γm) (hne : ¬ (φa = 1 ∧ φv = 0)) :
    ∃ γm', 0 < 1 + γm' ∧ Qstar β γm' (varM va 1 0) = Qstar β γm (varM va φa φv) ∧
      policyWelfare β φ ε A₀ γa va γm φa φv < policyWelfare β φ ε A₀ γa va γm' 1 0 := by
  have hq : 0 < Qstar β γm (varM va φa φv) := div_pos (mul_pos hβ0 (Real.exp_pos _)) hγm
  obtain ⟨γm', hγ', hQ'⟩ := exists_gamma_for_qstar (va := va) hβ0 hq
  exact ⟨γm', hγ', hQ', (stabilization_optimal hφ hβ0 hβ1 hva hQ').2 hne⟩

/-- **Ex. 4.5(g)** (Galí 2015, pp. 124–125; **correction**): no rule is optimal. Every rule with an
equilibrium (`Q* < 1`, i.e. a positive nominal rate) is strictly improved upon by another rule
with an equilibrium: lowering money growth towards the Friedman-rule level raises welfare
without bound. -/
theorem policy_not_optimal {β φ ε A₀ γa va γm φa φv : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγm : 0 < 1 + γm) (hQ : Qstar β γm (varM va φa φv) < 1) :
    ∃ γm', 0 < 1 + γm' ∧ Qstar β γm' (varM va φa φv) < 1 ∧
      policyWelfare β φ ε A₀ γa va γm φa φv < policyWelfare β φ ε A₀ γa va γm' φa φv := by
  obtain ⟨γ', h1, h2, h3⟩ := not_optimal_of_equilibrium (φ := φ) (ε := ε) (A₀ := A₀) (γa := γa)
    hβ0 hβ1 hγm hQ
  refine ⟨γ', h1, h2, ?_⟩
  unfold policyWelfare stickyWelfare
  linarith

/-- Galí (2015), Ex. 4.5(g): along the rules with `φ_a = 1, φ_v = 0`, welfare equals the
flexible-price welfare and is unbounded as money growth falls to the Friedman-rule level
`1 + γ_m = β e^{σ_a²/2}` (`Q* ↑ 1`, nominal rate `↓ 0`): the Friedman rule with
`φ_a = 1, φ_v = 0` is the supremum. -/
theorem tendsto_policyWelfare_friedman {β φ ε A₀ γa va : ℝ} (hφ : 0 ≤ φ) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    Tendsto (fun γm => policyWelfare β φ ε A₀ γa va γm 1 0)
      (𝓝[>] (β * Real.exp (varM va 1 0 / 2) - 1)) atTop := by
  set γF := β * Real.exp (varM va 1 0 / 2) - 1 with hγF
  have hF : 0 < 1 + γF := by rw [hγF]; simp only [add_sub_cancel]; positivity
  have hV : ∀ γm, γF < γm → velocity β γm (varM va 1 0) = (γm - γF) / (1 + γm) := by
    intro γm hγ
    have : 0 < 1 + γm := by linarith
    rw [velocity, Qstar, show β * Real.exp (varM va 1 0 / 2) = 1 + γF by rw [hγF]; ring]
    field_simp
    ring
  have h10 : varX va 1 0 = 0 := by unfold varX; ring
  have hlim : Tendsto (fun γm : ℝ => (γm - γF) / (1 + γm)) (𝓝[>] γF) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun γm : ℝ => (γm - γF) / (1 + γm)) (𝓝 γF) (𝓝 ((γF - γF) / (1 + γF))) :=
        ((continuous_id.sub continuous_const).tendsto γF).div
          ((continuous_const.add continuous_id).tendsto γF) hF.ne'
      rw [sub_self, zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with γm hγ
      simp only [Set.mem_Ioi] at hγ ⊢
      exact div_pos (by linarith) (by linarith)
  have hlog : Tendsto (fun γm : ℝ => -Real.log ((γm - γF) / (1 + γm)) * (1 - β)⁻¹) (𝓝[>] γF)
      atTop :=
    (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hlim)).atTop_mul_const
      (inv_pos.2 (by linarith))
  refine (tendsto_atTop_add_const_left _ (welfareFlex β φ ε A₀ γa 1) hlog).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with γm hγ
  simp only [Set.mem_Ioi] at hγ
  rw [policyWelfare, h10, (stickyWelfare_eq_flex_iff hφ hβ0 hβ1).2 rfl, hV γm hγ,
    welfareFlex_eq β φ ε A₀ γa ((γm - γF) / (1 + γm))]
  ring

/-- **Ex. 4.5(g)** (Galí 2015, p. 125: the optimal rule replicates the flexible-price
equilibrium): with `φ_a = 1` and `φ_v = 0` (`ε^m = ε^a`), sticky-price employment is
`N_t = 𝓜^{−1/(1+φ)}` at every date and state, the flexible-price level. -/
theorem stickyN_replicates (S : ShockPair μ ℱ) (φ ε : ℝ) (t : ℕ) (ω : Ω) :
    stickyN φ ε 1 0 S t ω = Nflex φ ε := by
  cases t with
  | zero => rfl
  | succ t =>
    simp only [stickyN, gapShock, varX]
    ring_nf
    simp

/-- **Ex. 4.5(g)** (Galí 2015, p. 125): under the rule `φ_a = 1, φ_v = 0` the sticky-price
equilibrium allocation (employment, output, consumption, price level, real balances) coincides
with the flexible-price equilibrium allocation, state by state. -/
theorem sticky_replicates_flex (S : ShockPair μ ℱ) {β φ ε A₀ γa M₀ γm : ℝ} (t : ℕ) (ω : Ω) :
    stickyN φ ε 1 0 S t ω = Nflex φ ε ∧
      level A₀ γa (techShock S) t ω * stickyN φ ε 1 0 S t ω =
        level A₀ γa (techShock S) t ω * Nflex φ ε ∧
      velocity β γm (varM S.va 1 0) * level M₀ γm (moneyShock 1 0 S) t ω /
          (level A₀ γa (techShock S) t ω * stickyN φ ε 1 0 S t ω) =
        velocity β γm (varM S.va 1 0) * level M₀ γm (moneyShock 1 0 S) t ω /
          (level A₀ γa (techShock S) t ω * Nflex φ ε) := by
  rw [stickyN_replicates]
  exact ⟨rfl, rfl, rfl⟩

/-- **Ex. 4.5(g)** (Galí 2015, p. 125): in *every* sticky-price equilibrium with constant
velocity under the rule `φ_a = 1, φ_v = 0`, employment is at its flexible-price level almost
surely. -/
theorem sticky_employment_replicates [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock 1 0 S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock 1 0 S) t ω = V) (t : ℕ) :
    N t =ᵐ[μ] fun _ => Nflex φ ε := by
  cases t with
  | zero => exact Filter.Eventually.of_forall fun ω =>
      sticky_employment_zero S hφ hA hγa hM hγm h hV ω
  | succ t =>
    filter_upwards [sticky_employment S hφ hε hA hγa hM hγm h hV t] with ω hω
    rw [hω]
    simp only [gapShock, varX]
    ring_nf
    simp

/-- Galí (2015), Ex. 4.5(g): the rule `φ_a = 1, φ_v = 0` attains the flexible-price welfare. -/
theorem policyWelfare_replicates {β φ ε A₀ γa va γm : ℝ} (hφ : 0 ≤ φ) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    policyWelfare β φ ε A₀ γa va γm 1 0 =
      welfareFlex β φ ε A₀ γa (velocity β γm (varM va 1 0)) := by
  rw [policyWelfare, (stickyWelfare_eq_flex_iff hφ hβ0 hβ1).2 (by unfold varX; ring)]

/-- Galí (2015), Ex. 4.5(g), p. 125: the non-negativity constraint on the nominal rate,
`Q* ≤ 1`, with `φ_a = 1, φ_v = 0` reads `β e^{σ_a²/2} ≤ 1 + γ_m`; the Friedman-rule level is
`1 + γ_m = β e^{σ_a²/2}`. -/
theorem friedman_level_of_replicating {β γm va : ℝ} (hγm : 0 < 1 + γm) :
    Qstar β γm (varM va 1 0) ≤ 1 ↔ β * Real.exp (va / 2) ≤ 1 + γm := by
  rw [qstar_le_one_iff hγm]
  unfold varM
  ring_nf

/-! ### A concrete probability space carrying the shocks (non-vacuity) -/

/-- Galí (2015), Ex. 4.5: the sample space `ℕ → ℝ × ℝ` of innovation sequences with the i.i.d.
product law `⊗ₜ N(0, σ_a²) ⊗ N(0, 1)` (`Measure.infinitePi`). -/
noncomputable abbrev shockMeasure (va : ℝ≥0) : Measure (ℕ → ℝ × ℝ) :=
  Measure.infinitePi fun _ : ℕ => pairLaw va

/-- Galí (2015), Ex. 4.5: the natural filtration `ℱ_t = σ((ε^a_s, ν_s), s ≤ t)`. -/
noncomputable def shockFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ × ℝ)) :=
  Filtration.natural (fun (i : ℕ) (ω : ℕ → ℝ × ℝ) => ω i)
    fun i => (measurable_pi_apply i).stronglyMeasurable

/-- Galí (2015), Ex. 4.5: the date-`t+1` innovation pair is independent of `ℱ_t` under the
product law (restated from the Chapter 2 project). -/
theorem coord_indep (va : ℝ≥0) (t : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω (t + 1)) inferInstance)
      (shockFiltration t) (shockMeasure va) := by
  have hI : iIndep (fun i => MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance)
      (shockMeasure va) :=
    (iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_infinitePi (X := fun _ (x : ℝ × ℝ) => x)
      (P := fun _ : ℕ => pairLaw va) (fun _ => measurable_id))
  have h := indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hI
    (S := {t + 1}) (T := Set.Iic t) (Set.disjoint_singleton_left.2 (by simp))
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left, Set.mem_Iic] at h
  exact h

/-- Galí (2015), Ex. 4.5: `ℱ_t` contains the date-`t` innovations. -/
theorem comap_le_shockFiltration (t : ℕ) :
    MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω t) inferInstance ≤ shockFiltration t :=
  le_iSup₂ (f := fun j (_ : j ≤ t) =>
    MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω j) inferInstance) t le_rfl

/-- Galí (2015), Ex. 4.5: the coordinate process is a `ShockPair` on the concrete space. -/
noncomputable def concreteShocks (va : ℝ≥0) : ShockPair (shockMeasure va) shockFiltration where
  Z := fun t ω => ω t
  va := va
  adapted := fun t => (comap_measurable _).mono (comap_le_shockFiltration t) le_rfl
  hasLaw := fun t => (measurePreserving_eval_infinitePi (fun _ : ℕ => pairLaw va) t).hasLaw
  indep := fun t => coord_indep va t

/-- Galí (2015), Ex. 4.5(c), p. 124 (**non-vacuity**): on the concrete space the exact
flexible-price equilibrium exists whenever `β e^{σ_m²/2} < 1 + γ_m`. -/
theorem exists_flex_equilibrium (va : ℝ≥0) {β φ ε A₀ γa M₀ γm φa φv : ℝ} (hφ : 0 ≤ φ)
    (hε : 1 < ε) (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm)
    (hQ : Qstar β γm (varM va φa φv) < 1) :
    ∃ C N Y P W Q, IsFlexEquilibrium (shockMeasure va) shockFiltration β φ ε
      (level A₀ γa (techShock (concreteShocks va)))
      (level M₀ γm (moneyShock φa φv (concreteShocks va))) C N Y P W Q :=
  ⟨_, _, _, _, _, _, flex_candidate (concreteShocks va) hφ hε hA hγa hM hγm hQ⟩

/-- Galí (2015), Ex. 4.5(e), p. 124 (**non-vacuity**): on the concrete space the exact
equilibrium with prices set in advance exists whenever `β e^{σ_m²/2} < 1 + γ_m`. -/
theorem exists_sticky_equilibrium (va : ℝ≥0) {β φ ε A₀ γa M₀ γm φa φv : ℝ} (hφ : 0 ≤ φ)
    (hε : 1 < ε) (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm)
    (hQ : Qstar β γm (varM va φa φv) < 1) :
    ∃ C N Y P W Q, IsStickyEquilibrium (shockMeasure va) shockFiltration β φ ε
      (level A₀ γa (techShock (concreteShocks va)))
      (level M₀ γm (moneyShock φa φv (concreteShocks va))) C N Y P W Q :=
  ⟨_, _, _, _, _, _, sticky_candidate (concreteShocks va) hφ hε hA hγa hM hγm hQ⟩

/-! ### (f) Expected lifetime utility as the expectation of the infinite sum -/

/-- Galí (2015), Ex. 4.5(f): `log N_{t+1} = log N − (1+φ) s²/2 + (ε^m_{t+1} − ε^a_{t+1})`
almost surely in a sticky-price equilibrium with constant velocity. -/
theorem sticky_logN_succ [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) (t : ℕ) :
    (fun ω => Real.log (N (t + 1) ω)) =ᵐ[μ] fun ω =>
      (Real.log (Nflex φ ε) - (1 + φ) * varX S.va φa φv / 2) +
        ((φa - 1) * (S.Z (t + 1) ω).1 + φv * (S.Z (t + 1) ω).2) := by
  filter_upwards [sticky_employment S hφ hε hA hγa hM hγm h hV t] with ω hω
  rw [hω, Real.log_mul (Nflex_pos hε).ne' (Real.exp_pos _).ne', Real.log_exp]
  simp only [gapShock]; ring

/-- Galí (2015), Ex. 4.5(f): `E|a ε^a_t + b ν_t| = ∫ |a x + b y| dN(0, σ_a²) ⊗ N(0, 1)`, the
same at every date. -/
theorem integral_abs_lin (S : ShockPair μ ℱ) (a b : ℝ) (t : ℕ) :
    ∫ ω, |a * (S.Z t ω).1 + b * (S.Z t ω).2| ∂μ = ∫ q, |a * q.1 + b * q.2| ∂(pairLaw S.va) :=
  (S.hasLaw t).integral_comp (f := fun q : ℝ × ℝ => |a * q.1 + b * q.2|)
    (by fun_prop : Continuous fun q : ℝ × ℝ => |a * q.1 + b * q.2|).aestronglyMeasurable

/-- Galí (2015), Ex. 4.5(f): the bound
`|log A_t| ≤ |log A₀| + t |log(1 + γ_a)| + |ε^a_1| + ⋯ + |ε^a_t|`. -/
theorem abs_log_tech_le (S : ShockPair μ ℱ) {A₀ γa : ℝ} (hA : 0 < A₀) (hγa : 0 < 1 + γa)
    (t : ℕ) (ω : Ω) : |Real.log (level A₀ γa (techShock S) t ω)| ≤
      |Real.log A₀| + t * |Real.log (1 + γa)| +
        ∑ s ∈ Finset.range t, |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2| := by
  rw [log_level_eq hA hγa]
  have h1 := Finset.abs_sum_le_sum_abs (fun s => techShock S (s + 1) ω) (Finset.range t)
  have h2 : |(t : ℝ) * Real.log (1 + γa)| = t * |Real.log (1 + γa)| := by
    rw [abs_mul, Nat.abs_cast]
  have h3 := abs_add_le (Real.log A₀ + t * Real.log (1 + γa))
    (∑ s ∈ Finset.range t, techShock S (s + 1) ω)
  have h4 := abs_add_le (Real.log A₀) (t * Real.log (1 + γa))
  simp only [techShock, one_mul, zero_mul, add_zero] at h1 h3 ⊢
  linarith

/-- **Ex. 4.5(f)** (Galí 2015, p. 124, expected lifetime utility): in a sticky-price
equilibrium with constant velocity, `E[∑ₜ βᵗ U_t] = ∑ₜ βᵗ E[U_t] = stickyWelfare`. The
interchange is justified by the bound `E|βᵗ U_t| ≤ βᵗ (K₀ + K₁ t)`. -/
theorem integral_tsum_sticky_welfare [IsProbabilityMeasure μ] (S : ShockPair μ ℱ)
    {β φ ε A₀ γa M₀ γm φa φv V : ℝ} (hφ : 0 ≤ φ) (hε : 1 < ε) (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {C N Y P W Q : ℕ → Ω → ℝ}
    (h : IsStickyEquilibrium μ ℱ β φ ε (level A₀ γa (techShock S))
      (level M₀ γm (moneyShock φa φv S)) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm (moneyShock φa φv S) t ω = V) :
    ∫ ω, ∑' t : ℕ, β ^ t * utility φ (C t ω)
        (level M₀ γm (moneyShock φa φv S) t ω / P t ω) (N t ω) ∂μ =
      stickyWelfare β φ ε A₀ γa V (varX S.va φa φv) := by
  have hAp := level_pos hA hγa (techShock S)
  have hMp := level_pos hM hγm (moneyShock φa φv S)
  have hVpos : 0 < V := by
    obtain ⟨ω₀, -⟩ := (h.euler 0).exists
    rw [← hV 0 ω₀, ← h.clearing 0 ω₀]
    exact div_pos (mul_pos (h.pos_P 0 ω₀) (h.pos_C 0 ω₀)) (hMp 0 ω₀)
  have h1φ : 0 < 1 + φ := by linarith
  set m₁ := ∫ q, |1 * q.1 + 0 * q.2| ∂(pairLaw S.va) with hm₁
  set m₂ := ∫ q, |(φa - 1) * q.1 + φv * q.2| ∂(pairLaw S.va) with hm₂
  have hm₁0 : 0 ≤ m₁ := integral_nonneg fun q => abs_nonneg _
  have hm₂0 : 0 ≤ m₂ := integral_nonneg fun q => abs_nonneg _
  set L := |Real.log (Nflex φ ε)| + (1 + φ) * varX S.va φa φv / 2 + m₂ with hL
  have hs0 : 0 ≤ (1 + φ) * varX S.va φa φv / 2 := by
    have := varX_nonneg S.va.2 φa φv; positivity
  -- integrability and the bound for `log N_t`
  have hlogN : ∀ t, Integrable (fun ω => Real.log (N t ω)) μ ∧
      ∫ ω, |Real.log (N t ω)| ∂μ ≤ L := by
    intro t
    cases t with
    | zero =>
      have hc : (fun ω => Real.log (N 0 ω)) = fun _ => Real.log (Nflex φ ε) := by
        funext ω; rw [sticky_employment_zero S hφ hA hγa hM hγm h hV ω]
      refine ⟨by rw [hc]; exact integrable_const _, ?_⟩
      rw [show (fun ω => |Real.log (N 0 ω)|) = fun _ => |Real.log (Nflex φ ε)| by
        funext ω; rw [congrFun hc ω], integral_const, probReal_univ, one_smul, hL]
      linarith
    | succ t =>
      have hae := sticky_logN_succ S hφ hε hA hγa hM hγm h hV t
      have hint : Integrable (fun ω => Real.log (N (t + 1) ω)) μ :=
        ((integrable_const _).add (integrable_lin S (φa - 1) φv (t + 1))).congr hae.symm
      refine ⟨hint, ?_⟩
      have hbd : ∀ᵐ ω ∂μ, |Real.log (N (t + 1) ω)| ≤ (|Real.log (Nflex φ ε)| +
          (1 + φ) * varX S.va φa φv / 2) + |(φa - 1) * (S.Z (t + 1) ω).1 +
            φv * (S.Z (t + 1) ω).2| := by
        filter_upwards [hae] with ω hω
        rw [hω]
        refine (abs_add_le _ _).trans ?_
        have := abs_sub (Real.log (Nflex φ ε)) ((1 + φ) * varX S.va φa φv / 2)
        rw [abs_of_nonneg hs0] at this
        linarith
      have hmaj : Integrable (fun ω => (|Real.log (Nflex φ ε)| +
          (1 + φ) * varX S.va φa φv / 2) + |(φa - 1) * (S.Z (t + 1) ω).1 +
            φv * (S.Z (t + 1) ω).2|) μ :=
        (integrable_const _).add (integrable_lin S (φa - 1) φv (t + 1)).abs
      refine (integral_mono_ae hint.abs hmaj hbd).trans (le_of_eq ?_)
      rw [integral_add (integrable_const _) (integrable_lin S (φa - 1) φv (t + 1)).abs,
        integral_const, probReal_univ, one_smul, integral_abs_lin, ← hm₂, hL]
  -- `E N_t^{1+φ} = 𝓜⁻¹`
  have hpowE : ∀ t, ∫ ω, N t ω ^ (1 + φ) ∂μ = (markup ε)⁻¹ := by
    intro t
    cases t with
    | zero => exact h.pricing0
    | succ t =>
      rw [← integral_condExp (ℱ.le t), integral_congr_ae (h.pricing t), integral_const,
        probReal_univ, one_smul]
  set U : ℕ → Ω → ℝ := fun t ω => utility φ (C t ω)
    (level M₀ γm (moneyShock φa φv S) t ω / P t ω) (N t ω) with hU
  have hUeq : ∀ t ω, U t ω = 2 * Real.log (level A₀ γa (techShock S) t ω) +
      2 * Real.log (N t ω) - Real.log V - N t ω ^ (1 + φ) / (1 + φ) := fun t ω =>
    sticky_period_utility h hAp hMp hV hVpos t ω
  have hint : ∀ t : ℕ, Integrable (fun ω => β ^ t * U t ω) μ := by
    intro t
    have : (fun ω => β ^ t * U t ω) = fun ω => β ^ t * (2 * Real.log (level A₀ γa (techShock S)
        t ω) + 2 * Real.log (N t ω) - Real.log V - N t ω ^ (1 + φ) / (1 + φ)) := by
      funext ω; rw [hUeq]
    rw [this]
    exact (((((integrable_log_tech S hA hγa t).const_mul 2).add ((hlogN t).1.const_mul 2)).sub
      (integrable_const _)).sub ((h.integrable_hours t).div_const _)).const_mul _
  set K₀ := 2 * |Real.log A₀| + 2 * L + |Real.log V| + (markup ε)⁻¹ / (1 + φ) with hK₀
  set K₁ := 2 * |Real.log (1 + γa)| + 2 * m₁ with hK₁
  set g : ℕ → ℝ := fun t => β ^ t * (K₀ + K₁ * t) with hg
  have hgs : Summable g := (hasSum_affine (K := K₀) (c := K₁) hβ0 hβ1).summable
  have hbound : ∀ t : ℕ, ∫ ω, ‖β ^ t * U t ω‖ ∂μ ≤ g t := by
    intro t
    have hpt : ∀ ω, ‖β ^ t * U t ω‖ ≤ β ^ t * ((2 * |Real.log A₀| + |Real.log V|) +
        2 * t * |Real.log (1 + γa)| +
        2 * ∑ s ∈ Finset.range t, |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2| +
        2 * |Real.log (N t ω)| + N t ω ^ (1 + φ) / (1 + φ)) := by
      intro ω
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0, hUeq]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
      have h1 := abs_log_tech_le S hA hγa t ω
      have h2 : 0 ≤ N t ω ^ (1 + φ) / (1 + φ) :=
        div_nonneg (Real.rpow_nonneg (h.pos_N t ω).le _) h1φ.le
      have h3 := abs_sub (2 * Real.log (level A₀ γa (techShock S) t ω) +
        2 * Real.log (N t ω) - Real.log V) (N t ω ^ (1 + φ) / (1 + φ))
      have h4 := abs_sub (2 * Real.log (level A₀ γa (techShock S) t ω) +
        2 * Real.log (N t ω)) (Real.log V)
      have h5 := abs_add_le (2 * Real.log (level A₀ γa (techShock S) t ω))
        (2 * Real.log (N t ω))
      rw [abs_of_nonneg h2] at h3
      rw [abs_mul, abs_two] at h5
      rw [abs_mul (2 : ℝ), abs_two] at h5
      linarith
    have hsumint : Integrable (fun ω => ∑ s ∈ Finset.range t,
        |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2|) μ :=
      integrable_finsetSum _ fun s _ => (integrable_lin S 1 0 (s + 1)).abs
    have j1 : Integrable (fun _ : Ω => (2 * |Real.log A₀| + |Real.log V|) +
        2 * t * |Real.log (1 + γa)|) μ := integrable_const _
    have j2 : Integrable (fun ω => 2 * ∑ s ∈ Finset.range t,
        |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2|) μ := hsumint.const_mul 2
    have j3 : Integrable (fun ω => 2 * |Real.log (N t ω)|) μ := (hlogN t).1.abs.const_mul 2
    have j4 : Integrable (fun ω => N t ω ^ (1 + φ) / (1 + φ)) μ :=
      (h.integrable_hours t).div_const _
    have j12 : Integrable (fun ω => (2 * |Real.log A₀| + |Real.log V|) +
        2 * t * |Real.log (1 + γa)| + 2 * ∑ s ∈ Finset.range t,
        |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2|) μ := j1.add j2
    have j123 : Integrable (fun ω => (2 * |Real.log A₀| + |Real.log V|) +
        2 * t * |Real.log (1 + γa)| + 2 * ∑ s ∈ Finset.range t,
        |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2| + 2 * |Real.log (N t ω)|) μ := j12.add j3
    have hrint : Integrable (fun ω => β ^ t * ((2 * |Real.log A₀| + |Real.log V|) +
        2 * t * |Real.log (1 + γa)| +
        2 * ∑ s ∈ Finset.range t, |1 * (S.Z (s + 1) ω).1 + 0 * (S.Z (s + 1) ω).2| +
        2 * |Real.log (N t ω)| + N t ω ^ (1 + φ) / (1 + φ))) μ :=
      (j123.add j4).const_mul _
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _) hrint
      (Filter.Eventually.of_forall hpt)).trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
    rw [integral_add j123 j4, integral_add j12 j3, integral_add j1 j2, integral_const_mul,
      integral_const_mul, integral_div, hpowE t, integral_finsetSum _ fun s _ =>
      (integrable_lin S 1 0 (s + 1)).abs]
    simp only [integral_abs_lin S 1 0, ← hm₁]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const, probReal_univ,
      smul_eq_mul, one_mul]
    have := (hlogN t).2
    rw [hK₀, hK₁]
    nlinarith
  have hsum : Summable fun t : ℕ => ∫ ω, ‖β ^ t * U t ω‖ ∂μ :=
    hgs.of_nonneg_of_le (fun t => integral_nonneg fun ω => norm_nonneg _) hbound
  change ∫ ω, ∑' t : ℕ, β ^ t * U t ω ∂μ = _
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp only [integral_const_mul]
  exact (hasSum_sticky_welfare S hφ hε hA hγa hM hγm hβ0 hβ1 h hV).tsum_eq

end Gali.MonetaryPolicyDesign.Ex4_5
