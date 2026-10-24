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

/-!
# Exercise 2.5: an exact equilibrium of the classical monetary model

Galí (2015), Chapter 2, Exercise 2.5, pp. 48–49. Money in the utility function with period
utility `log C + log (M/P) − N^{1+φ}/(1+φ)` (eq. (52)), a linear technology `Y = A N` with
`A_{t+1}/A_t = (1 + γ_a) e^{ε^a_{t+1}}`, and an exogenous money supply
`M_{t+1}/M_t = (1 + γ_m) e^{ε^m_{t+1}}` (eq. (53)), with i.i.d. Gaussian innovations.

## (a) Optimality conditions

* Marginal utilities (`hasDerivAt_utility_C`, `_m`, `_N`): `U_c = 1/C`, `U_m = 1/(M/P)`,
  `U_n = −N^φ`.
* Labour supply `W/P = C N^φ` (`labour_optimum_iff`, necessity and sufficiency).
* Money demand `C = (1 − Q)(M/P)`, i.e. velocity `P C/M = 1 − Q` (`money_optimum_iff`,
  necessity and sufficiency along the budget line (32) with financial wealth held fixed).
* Firm: `W = P A` (`firm_optimum_iff`).
* Euler equation (5) with `U_c = 1/C`: `Q_t = β E_t[(C_t P_t)/(C_{t+1} P_{t+1})]`, stated with a
  genuine conditional expectation `μ[· | ℱ t]` (`IsEquilibrium.euler`).

## (b) The exact equilibrium

The shocks live on a genuine probability space with a filtration `ℱ`: the innovations are
adapted, `N(0, σ²)` at each date, and `ε_{t+1}` is independent of `ℱ_t`
(`GaussianInnovations`), hence i.i.d.

* `employment_eq_one`: in every equilibrium `N_t = 1`, so `Y_t = C_t = A_t`
  (`output_eq_technology`), state by state, with no guess needed.
* `velocity_eq`: velocity is `P_t Y_t / M_t = 1 − Q_t`.
* `condExp_money_ratio`: `E_t[M_t/M_{t+1}] = e^{σ_m²/2}/(1 + γ_m)` (Gaussian MGF,
  `mgf_gaussianReal`, plus independence, `condExp_indep_eq`).
* `velocity_of_constant`: a constant velocity must be `V = 1 − β e^{σ_m²/2}/(1 + γ_m)`;
  `candidate_isEquilibrium`: conversely, when `β e^{σ_m²/2} < 1 + γ_m` the constant-velocity
  allocation is an exact equilibrium.
* `shockMeasure`, `shockFiltration`, `techInnovations`, `moneyInnovations`: a concrete
  probability space (`Measure.infinitePi` of `N(0, σ_a²) ⊗ N(0, σ_m²)`) with the natural
  filtration carrying i.i.d. Gaussian innovations; `exists_exact_equilibrium`: the exact
  equilibrium genuinely exists on it.
* `inflation_eq`: gross inflation `P_{t+1}/P_t = (1 + γ_m)/(1 + γ_a) e^{ε^m_{t+1} − ε^a_{t+1}}`;
  `nominalRate_eq`: the nominal rate is the constant `i = −log Q`.

## (c) Welfare and optimal policy

* `hasSum_expected_welfare`: expected lifetime utility `∑ βᵗ E[U_t]` equals
  `(2 log A₀ − log V − 1/(1+φ))/(1 − β) + 2 β log(1 + γ_a)/(1 − β)²`. Monetary policy enters
  only through `−log V/(1 − β)`, `V = 1 − β e^{σ_m²/2}/(1 + γ_m)`.
* `integral_tsum_welfare`: welfare is the expectation of lifetime utility,
  `E[∑ₜ βᵗ U_t] = ∑ₜ βᵗ E[U_t]` (dominated convergence with a geometric bound on `E|βᵗ U_t|`).
* `welfare_strictAnti_gamma`, `welfare_strictMono_var`: welfare falls with money growth `γ_m`
  and rises with the variance `σ_m²` (a higher variance raises `E_t[M_t/M_{t+1}]`).
* `welfare_rate_strictAnti`, `tendsto_welfare_rate`: as a function of the constant nominal rate
  `i = −log Q ≥ 0` welfare is strictly decreasing on `i > 0` and unbounded as `i → 0⁺`.
* `not_optimal_of_equilibrium`: every policy with an equilibrium (`i > 0`) is strictly
  improved upon, so an optimal policy must have `i = 0`, i.e. `Q = 1` (the Friedman rule,
  `friedman_iff`).

**Imprecision (reported).** With `log (M/P)` there is no satiation in real balances: at
`Q = 1` velocity would be `V = 0`, the constant-velocity equilibrium does not exist
(`not_equilibrium_at_friedman`) and welfare is unbounded. The Friedman rule is the
supremum, approached as `i → 0⁺`, not an attained maximum.
-/

namespace Gali.ClassicalMonetaryModel.Ex2_5

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-! ### (a) Optimality conditions -/

/-- Galí (2015), Ex. 2.5, eq. (52), p. 49: period utility `log C + log m − N^{1+φ}/(1+φ)`,
with real balances `m = M/P`. -/
noncomputable def utility (φ C m N : ℝ) : ℝ :=
  Real.log C + Real.log m - N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), Ex. 2.5(a), p. 49: the marginal utility of consumption is `U_c = 1/C`. -/
theorem hasDerivAt_utility_C (φ m N : ℝ) {C : ℝ} (hC : C ≠ 0) :
    HasDerivAt (fun C' => utility φ C' m N) C⁻¹ C := by
  have := ((Real.hasDerivAt_log hC).add_const (Real.log m)).sub_const (N ^ (1 + φ) / (1 + φ))
  simpa [utility] using this

/-- Galí (2015), Ex. 2.5(a), p. 49: the marginal utility of real balances is `U_m = 1/m`. -/
theorem hasDerivAt_utility_m (φ C N : ℝ) {m : ℝ} (hm : m ≠ 0) :
    HasDerivAt (fun m' => utility φ C m' N) m⁻¹ m := by
  have := ((Real.hasDerivAt_log hm).const_add (Real.log C)).sub_const (N ^ (1 + φ) / (1 + φ))
  simpa [utility] using this

/-- Galí (2015), Ex. 2.5(a), p. 49: the marginal disutility of labour is `−U_n = N^φ`. -/
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
tangent lines (restated from the Chapter 3 project; used for the concavity of (52)). -/
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
`x^{1+φ}/(1+φ) + x^φ (y − x) ≤ y^{1+φ}/(1+φ)` (restated from the Chapter 3 project). -/
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

/-- Galí (2015), Ex. 2.5(a) (concavity of (52)): the tangent-line inequality for `log`,
`log y ≤ log x + (y − x)/x` for `x, y > 0`. -/
theorem log_le_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y ≤ Real.log x + (y - x) / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have : y / x - 1 = (y - x) / x := by field_simp
  linarith

/-- Galí (2015), Ex. 2.5(a), with eq. (4), p. 19 (**necessity**): if hours `N` are a local
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

/-- Galí (2015), Ex. 2.5(a), p. 19 (**sufficiency**, by concavity): if `W/P = C N^φ` at a
point with `C, N > 0` on the budget line `P C = W N + X`, it maximises (52) among all feasible
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

/-- Galí (2015), Ex. 2.5(a), eq. (4), p. 19: a point with `C, N > 0` on the budget line solves
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

/-- Galí (2015), Ex. 2.5(a), with eq. (33), p. 32 (**necessity**): holding total financial
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

/-- Galí (2015), Ex. 2.5(a), eq. (33), p. 32 (**sufficiency**, by concavity of `log`): if
`C = (1 − Q) m` at a point with `C, m > 0` on the budget line `P C + (1 − Q) P m = X`, it
maximises (52) among all `m' > 0` with `C' > 0`. -/
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

/-- Galí (2015), Ex. 2.5(a), eq. (33), p. 32: on the budget line, `(C, m)` with `C, m > 0`
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

/-- Galí (2015), Ex. 2.5(a), p. 49: the competitive firm with `Y = A N` maximises
`P A N − W N` over `N ≥ 0` at some `N > 0` iff `W = P A`. -/
theorem firm_optimum_iff {P A W N : ℝ} (hN : 0 < N) :
    (∀ N', 0 ≤ N' → P * A * N' - W * N' ≤ P * A * N - W * N) ↔ W = P * A := by
  constructor
  · intro h
    have h1 := h (2 * N) (by linarith)
    have h2 := h 0 le_rfl
    have h3 : (P * A - W) * N = 0 := by nlinarith
    have := (mul_eq_zero.1 h3).resolve_right hN.ne'
    linarith
  · intro h N' _
    rw [h]; ring_nf; rfl

/-! ### The stochastic environment -/


/-! ### (b) The stochastic environment and the exact equilibrium -/

variable {Ω : Type*}

/-- Galí (2015), Ex. 2.5, p. 49, and eq. (53): the level `X_t = X₀ (1 + γ)ᵗ e^{ε_1 + ⋯ + ε_t}`
of technology (`X = A`) or of the money supply (`X = M`). -/
noncomputable def level (X₀ γ : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  X₀ * (1 + γ) ^ t * Real.exp (∑ s ∈ Finset.range t, ε (s + 1) ω)

/-- Galí (2015), Ex. 2.5, p. 49, and eq. (53): `X_{t+1}/X_t = (1 + γ) e^{ε_{t+1}}`. -/
theorem level_succ (X₀ γ : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    level X₀ γ ε (t + 1) ω = level X₀ γ ε t ω * ((1 + γ) * Real.exp (ε (t + 1) ω)) := by
  simp only [level, Finset.sum_range_succ, Real.exp_add, pow_succ]
  ring

/-- Galí (2015), Ex. 2.5, p. 49: levels are positive when `X₀ > 0` and `1 + γ > 0`. -/
theorem level_pos {X₀ γ : ℝ} (hX : 0 < X₀) (hγ : 0 < 1 + γ) (ε : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : 0 < level X₀ γ ε t ω := by
  unfold level
  positivity

variable [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (ℱ : Filtration ℕ mΩ)

/-- Galí (2015), Ex. 2.5, p. 49: i.i.d. Gaussian innovations `ε_t ~ N(0, σ²)` on a probability
space with filtration `ℱ`: `ε_t` is `ℱ_t`-measurable, has law `N(0, σ²)`, and `ε_{t+1}` is
independent of `ℱ_t` (so the sequence is independent and identically distributed). -/
structure GaussianInnovations where
  /-- The innovation at each date. -/
  ε : ℕ → Ω → ℝ
  /-- The variance `σ²`. -/
  var : ℝ≥0
  /-- `ε_t` is known at date `t`. -/
  adapted : ∀ t, Measurable[ℱ t] (ε t)
  /-- `ε_t ~ N(0, σ²)`. -/
  hasLaw : ∀ t, HasLaw (ε t) (gaussianReal 0 var) μ
  /-- `ε_{t+1}` is independent of the date-`t` information. -/
  indep : ∀ t, Indep (MeasurableSpace.comap (ε (t + 1)) inferInstance) (ℱ t) μ

/-- Galí (2015), eq. (5), p. 20, with `U_c = 1/C` (Ex. 2.5(a)): the right side
`β E_t[(C_t P_t)/(C_{t+1} P_{t+1})]` of the Euler equation, with a genuine conditional
expectation given `ℱ_t`. -/
noncomputable def eulerRHS (β : ℝ) (C P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β * μ[fun ω' => C t ω' * P t ω' / (C (t + 1) ω' * P (t + 1) ω') | ℱ t] ω

variable (β φ : ℝ) (A M C N Y P W Q : ℕ → Ω → ℝ)

/-- Galí (2015), Ex. 2.5(a)–(b), pp. 48–49: an equilibrium. The household conditions are
labour supply (4) `W/P = C N^φ`, money demand (33) `C = (1 − Q)(M/P)` and the Euler equation
(5); the firm sets `W = P A`; `Y = A N` and `C = Y`. -/
structure IsEquilibrium where
  /-- Consumption is positive. -/
  pos_C : ∀ t ω, 0 < C t ω
  /-- Hours are positive. -/
  pos_N : ∀ t ω, 0 < N t ω
  /-- The price level is positive. -/
  pos_P : ∀ t ω, 0 < P t ω
  /-- Labour supply, eq. (4): `W/P = C N^φ`. -/
  labour : ∀ t ω, W t ω / P t ω = C t ω * N t ω ^ φ
  /-- Money demand, eq. (33): `C = (1 − Q)(M/P)`. -/
  money : ∀ t ω, C t ω = (1 - Q t ω) * (M t ω / P t ω)
  /-- The Euler equation (5). -/
  euler : ∀ t, Q t =ᵐ[μ] eulerRHS μ ℱ β C P t
  /-- Labour demand of the competitive firm: `W = P A`. -/
  firm : ∀ t ω, W t ω = P t ω * A t ω
  /-- Technology: `Y = A N`. -/
  technology : ∀ t ω, Y t ω = A t ω * N t ω
  /-- Goods-market clearing: `C = Y`. -/
  clearing : ∀ t ω, C t ω = Y t ω

variable {μ ℱ β φ A M C N Y P W Q}

/-- Galí (2015), Ex. 2.5(b), p. 49: in every equilibrium employment is `N_t = 1`, state by
state (no guess is needed: with log utility the income and substitution effects cancel). -/
theorem employment_eq_one (h : IsEquilibrium μ ℱ β φ A M C N Y P W Q) (hφ : 0 ≤ φ)
    (hA : ∀ t ω, 0 < A t ω) (t : ℕ) (ω : Ω) : N t ω = 1 := by
  have hN := h.pos_N t ω
  have hP := h.pos_P t ω
  have hl := h.labour t ω
  rw [h.firm t ω, mul_div_cancel_left₀ _ hP.ne', h.clearing t ω, h.technology t ω] at hl
  have h1 : A t ω * 1 = A t ω * N t ω ^ (1 + φ) := by
    rw [Real.rpow_add hN, Real.rpow_one]
    linarith
  have h2 : N t ω ^ (1 + φ) = 1 := (mul_left_cancel₀ (hA t ω).ne' h1).symm
  have hne : (1 + φ) ≠ 0 := by linarith
  rw [← Real.rpow_rpow_inv hN.le hne, h2, Real.one_rpow]

/-- Galí (2015), Ex. 2.5(b), p. 49: in every equilibrium `Y_t = A_t` and `C_t = A_t`. -/
theorem output_eq_technology (h : IsEquilibrium μ ℱ β φ A M C N Y P W Q) (hφ : 0 ≤ φ)
    (hA : ∀ t ω, 0 < A t ω) (t : ℕ) (ω : Ω) : Y t ω = A t ω ∧ C t ω = A t ω := by
  have hY : Y t ω = A t ω := by rw [h.technology t ω, employment_eq_one h hφ hA t ω, mul_one]
  exact ⟨hY, (h.clearing t ω).trans hY⟩

/-- Galí (2015), Ex. 2.5(b), p. 49: velocity is `P_t Y_t / M_t = 1 − Q_t` in every
equilibrium. -/
theorem velocity_eq (h : IsEquilibrium μ ℱ β φ A M C N Y P W Q) (hM : ∀ t ω, 0 < M t ω)
    (t : ℕ) (ω : Ω) : P t ω * Y t ω / M t ω = 1 - Q t ω := by
  have hP := (h.pos_P t ω).ne'
  have hMt := (hM t ω).ne'
  rw [← h.clearing t ω, h.money t ω]
  field_simp

/-- Galí (2015), Ex. 2.5(b), p. 49, with the Gaussian MGF: for the money supply (53),
`E_t[M_t/M_{t+1}] = e^{σ_m²/2}/(1 + γ_m)`, since `M_t/M_{t+1} = e^{−ε_{t+1}}/(1 + γ_m)` with
`ε_{t+1} ~ N(0, σ_m²)` independent of `ℱ_t`. -/
theorem condExp_money_ratio [IsProbabilityMeasure μ] (G : GaussianInnovations μ ℱ)
    {M₀ γ : ℝ} (hM : M₀ ≠ 0) (hγ : 0 < 1 + γ) (t : ℕ) :
    μ[fun ω => level M₀ γ G.ε t ω / level M₀ γ G.ε (t + 1) ω | ℱ t]
      =ᵐ[μ] fun _ => Real.exp (G.var / 2) / (1 + γ) := by
  have hfun : (fun ω => level M₀ γ G.ε t ω / level M₀ γ G.ε (t + 1) ω)
      = fun ω => (1 + γ)⁻¹ * Real.exp (-G.ε (t + 1) ω) := by
    funext ω
    have h1 : level M₀ γ G.ε t ω ≠ 0 :=
      mul_ne_zero (mul_ne_zero hM (pow_ne_zero _ hγ.ne')) (Real.exp_pos _).ne'
    rw [level_succ, Real.exp_neg]
    field_simp
  rw [hfun]
  have hmeas : Measurable (G.ε (t + 1)) := (G.adapted (t + 1)).mono (ℱ.le (t + 1)) le_rfl
  have hg : Measurable fun x : ℝ => (1 + γ)⁻¹ * Real.exp (-x) := by fun_prop
  have hsm : StronglyMeasurable[MeasurableSpace.comap (G.ε (t + 1)) inferInstance]
      (fun ω => (1 + γ)⁻¹ * Real.exp (-G.ε (t + 1) ω)) :=
    (hg.comp (comap_measurable (G.ε (t + 1)))).stronglyMeasurable
  refine (condExp_indep_eq hmeas.comap_le (ℱ.le t) hsm (G.indep t)).trans ?_
  refine Filter.Eventually.of_forall fun _ => ?_
  have hint : ∫ ω, Real.exp (-G.ε (t + 1) ω) ∂μ = Real.exp (G.var / 2) := by
    have h := mgf_gaussianReal (G.hasLaw (t + 1)) (-1)
    simp only [mgf, neg_one_mul, zero_mul, zero_add, neg_one_sq, mul_one] at h
    exact h
  simp only
  rw [integral_const_mul, hint]
  ring

/-- Galí (2015), Ex. 2.5(b): the steady value `Q* = β e^{σ_m²/2}/(1 + γ_m)` of the bond price. -/
noncomputable def Qstar (β γ v : ℝ) : ℝ := β * Real.exp (v / 2) / (1 + γ)

/-- Galí (2015), Ex. 2.5(b): the constant velocity `V = 1 − β e^{σ_m²/2}/(1 + γ_m)`. -/
noncomputable def velocity (β γ v : ℝ) : ℝ := 1 - Qstar β γ v

/-- Galí (2015), Ex. 2.5(b), p. 49: with constant velocity, `C_t P_t = V M_t`, the Euler
equation's right side is the constant `β e^{σ_m²/2}/(1 + γ_m)`. -/
theorem eulerRHS_of_const_velocity [IsProbabilityMeasure μ] (G : GaussianInnovations μ ℱ)
    {M₀ γ V : ℝ} (hM : M₀ ≠ 0) (hγ : 0 < 1 + γ) (hV : V ≠ 0) {C P : ℕ → Ω → ℝ}
    (hCP : ∀ t ω, C t ω * P t ω = V * level M₀ γ G.ε t ω) (t : ℕ) :
    eulerRHS μ ℱ β C P t =ᵐ[μ] fun _ => Qstar β γ G.var := by
  have hfun : (fun ω' => C t ω' * P t ω' / (C (t + 1) ω' * P (t + 1) ω'))
      = fun ω' => level M₀ γ G.ε t ω' / level M₀ γ G.ε (t + 1) ω' := by
    funext ω'
    rw [hCP, hCP, mul_div_mul_left _ _ hV]
  filter_upwards [condExp_money_ratio G hM hγ t] with ω hω
  simp only [eulerRHS]
  rw [hfun, hω, Qstar]
  ring

/-- Galí (2015), Ex. 2.5(b), p. 49 (the hint): if velocity is constant, `P_t Y_t/M_t = V`,
then necessarily `V = 1 − β e^{σ_m²/2}/(1 + γ_m)`. -/
theorem velocity_of_constant [IsProbabilityMeasure μ] (G : GaussianInnovations μ ℱ)
    {M₀ γ V : ℝ} (hM : 0 < M₀) (hγ : 0 < 1 + γ)
    (h : IsEquilibrium μ ℱ β φ A (level M₀ γ G.ε) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γ G.ε t ω = V) :
    V = velocity β γ G.var := by
  have hMp := level_pos hM hγ G.ε
  obtain ⟨ω₀, -⟩ := (h.euler 0).exists
  have hVpos : 0 < V := by
    rw [← hV 0 ω₀, ← h.clearing 0 ω₀]
    exact div_pos (mul_pos (h.pos_P 0 ω₀) (h.pos_C 0 ω₀)) (hMp 0 ω₀)
  have hCP : ∀ t ω, C t ω * P t ω = V * level M₀ γ G.ε t ω := fun t ω => by
    rw [← hV t ω, ← h.clearing t ω]
    field_simp [(hMp t ω).ne']
  have hQ : ∀ ω, Q 0 ω = 1 - V := fun ω => by
    rw [← hV 0 ω, velocity_eq h hMp 0 ω]
    ring
  have hae := (h.euler 0).trans (eulerRHS_of_const_velocity G hM.ne' hγ hVpos.ne' hCP 0)
  obtain ⟨ω, hω⟩ := hae.exists
  rw [hQ ω] at hω
  simp only at hω
  rw [velocity]
  linarith

/-- Galí (2015), Ex. 2.5(b), p. 49: an equilibrium with constant velocity exists only if
`Q* = β e^{σ_m²/2}/(1 + γ_m) < 1`, i.e. only if the nominal rate is strictly positive. -/
theorem qstar_lt_one_of_equilibrium [IsProbabilityMeasure μ] (G : GaussianInnovations μ ℱ)
    {M₀ γ V : ℝ} (hM : 0 < M₀) (hγ : 0 < 1 + γ)
    (h : IsEquilibrium μ ℱ β φ A (level M₀ γ G.ε) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γ G.ε t ω = V) : Qstar β γ G.var < 1 := by
  have hVeq := velocity_of_constant G hM hγ h hV
  obtain ⟨ω₀, -⟩ := (h.euler 0).exists
  have hVpos : 0 < V := by
    rw [← hV 0 ω₀, ← h.clearing 0 ω₀]
    exact div_pos (mul_pos (h.pos_P 0 ω₀) (h.pos_C 0 ω₀)) (level_pos hM hγ G.ε 0 ω₀)
  rw [hVeq, velocity] at hVpos
  linarith

/-- Galí (2015), Ex. 2.5(b), p. 49 (**existence**): if `β e^{σ_m²/2} < 1 + γ_m`, the
allocation `N_t = 1`, `C_t = Y_t = A_t`, `P_t = V M_t/A_t`, `W_t = P_t A_t`, `Q_t = Q*`, with
`V = 1 − Q*`, is an exact equilibrium. -/
theorem candidate_isEquilibrium [IsProbabilityMeasure μ] (Ga Gm : GaussianInnovations μ ℱ)
    {A₀ γa M₀ γm : ℝ} (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm)
    (hQ : Qstar β γm Gm.var < 1) :
    IsEquilibrium μ ℱ β φ (level A₀ γa Ga.ε) (level M₀ γm Gm.ε) (level A₀ γa Ga.ε)
      (fun _ _ => 1) (level A₀ γa Ga.ε)
      (fun t ω => velocity β γm Gm.var * level M₀ γm Gm.ε t ω / level A₀ γa Ga.ε t ω)
      (fun t ω => velocity β γm Gm.var * level M₀ γm Gm.ε t ω)
      (fun _ _ => Qstar β γm Gm.var) := by
  have hV : 0 < velocity β γm Gm.var := by rw [velocity]; linarith
  have hAp := level_pos hA hγa Ga.ε
  have hMp := level_pos hM hγm Gm.ε
  refine ⟨hAp, fun _ _ => one_pos, fun t ω => div_pos (mul_pos hV (hMp t ω)) (hAp t ω), ?_, ?_,
    ?_, ?_, fun t ω => (mul_one _).symm, fun _ _ => rfl⟩
  · intro t ω
    simp only [Real.one_rpow, mul_one]
    field_simp [(hAp t ω).ne', (hMp t ω).ne', hV.ne']
  · intro t ω
    rw [show 1 - Qstar β γm Gm.var = velocity β γm Gm.var from rfl]
    field_simp [(hAp t ω).ne', (hMp t ω).ne', hV.ne']
  · intro t
    refine (eulerRHS_of_const_velocity Gm hM.ne' hγm hV.ne' (fun t ω => ?_) t).symm
    field_simp [(hAp t ω).ne']
  · intro t ω
    field_simp [(hAp t ω).ne']

/-- Galí (2015), Ex. 2.5(b), p. 49: in an equilibrium with constant velocity, gross inflation is
`P_{t+1}/P_t = (1 + γ_m)/(1 + γ_a) e^{ε^m_{t+1} − ε^a_{t+1}}`. -/
theorem inflation_eq (Ga Gm : GaussianInnovations μ ℱ) {A₀ γa M₀ γm V : ℝ} (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) (hφ : 0 ≤ φ)
    (h : IsEquilibrium μ ℱ β φ (level A₀ γa Ga.ε) (level M₀ γm Gm.ε) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm Gm.ε t ω = V) (t : ℕ) (ω : Ω) :
    P (t + 1) ω / P t ω = (1 + γm) / (1 + γa) * Real.exp (Gm.ε (t + 1) ω - Ga.ε (t + 1) ω) := by
  have hAp := level_pos hA hγa Ga.ε
  have hMp := level_pos hM hγm Gm.ε
  have hPeq : ∀ s, P s ω = V * level M₀ γm Gm.ε s ω / level A₀ γa Ga.ε s ω := fun s => by
    have h1 := hV s ω
    rw [(output_eq_technology h hφ hAp s ω).1] at h1
    rw [← h1]
    field_simp [(hAp s ω).ne', (hMp s ω).ne']
  have hVpos : 0 < V := by
    rw [← hV 0 ω, ← h.clearing 0 ω]
    exact div_pos (mul_pos (h.pos_P 0 ω) (h.pos_C 0 ω)) (hMp 0 ω)
  rw [hPeq, hPeq, level_succ, level_succ, Real.exp_sub]
  field_simp [(hAp t ω).ne', (hMp t ω).ne', hVpos.ne', hγa.ne', (Real.exp_pos (Ga.ε (t + 1) ω)).ne']

/-- Galí (2015), Ex. 2.5(b), p. 49: net inflation `π_{t+1} = log(P_{t+1}/P_t)` equals
`log(1 + γ_m) − log(1 + γ_a) + ε^m_{t+1} − ε^a_{t+1}`. -/
theorem log_inflation_eq (Ga Gm : GaussianInnovations μ ℱ) {A₀ γa M₀ γm V : ℝ} (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) (hφ : 0 ≤ φ)
    (h : IsEquilibrium μ ℱ β φ (level A₀ γa Ga.ε) (level M₀ γm Gm.ε) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm Gm.ε t ω = V) (t : ℕ) (ω : Ω) :
    Real.log (P (t + 1) ω / P t ω) =
      Real.log (1 + γm) - Real.log (1 + γa) + Gm.ε (t + 1) ω - Ga.ε (t + 1) ω := by
  rw [inflation_eq Ga Gm hA hγa hM hγm hφ h hV t ω, Real.log_mul (div_pos hγm hγa).ne'
    (Real.exp_pos _).ne', Real.log_div hγm.ne' hγa.ne', Real.log_exp]
  ring

/-- Galí (2015), Ex. 2.5(b), p. 49, and p. 32 (`Q = e^{−i}`): the constant nominal rate
`i = −log Q* = log(1 + γ_m) − log β − σ_m²/2`. -/
theorem nominalRate_eq {β γ v : ℝ} (hβ : 0 < β) (hγ : 0 < 1 + γ) :
    -Real.log (Qstar β γ v) = Real.log (1 + γ) - Real.log β - v / 2 := by
  rw [Qstar, Real.log_div (mul_pos hβ (Real.exp_pos _)).ne' hγ.ne',
    Real.log_mul hβ.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- Galí (2015), Ex. 2.5(c), p. 49: the constraint `Q_t ≤ 1` (a nonnegative nominal rate)
reads `β e^{σ_m²/2} ≤ 1 + γ_m`. -/
theorem qstar_le_one_iff {β γ v : ℝ} (hγ : 0 < 1 + γ) :
    Qstar β γ v ≤ 1 ↔ β * Real.exp (v / 2) ≤ 1 + γ := by
  rw [Qstar, div_le_one hγ]

/-- Galí (2015), Ex. 2.5(c), p. 49: the Friedman rule `i = −log Q* = 0` holds iff `Q* = 1`,
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

/-- Galí (2015), Ex. 2.5(c), p. 49 (**imprecision**): at the Friedman rule `Q* = 1` there is no
equilibrium with constant velocity (velocity would be `0`, real balances infinite). -/
theorem not_equilibrium_at_friedman [IsProbabilityMeasure μ] (G : GaussianInnovations μ ℱ)
    {M₀ γ V : ℝ} (hM : 0 < M₀) (hγ : 0 < 1 + γ) (hF : Qstar β γ G.var = 1)
    (h : IsEquilibrium μ ℱ β φ A (level M₀ γ G.ε) C N Y P W Q) :
    ¬ ∀ t ω, P t ω * Y t ω / level M₀ γ G.ε t ω = V := fun hV => by
  have := qstar_lt_one_of_equilibrium G hM hγ h hV
  linarith

/-! ### (c) Welfare -/

/-- Galí (2015), Ex. 2.5(c), p. 49: in an equilibrium with constant velocity `V`, period
utility is `2 log A_t − log V − 1/(1+φ)`. -/
theorem period_utility_eq (h : IsEquilibrium μ ℱ β φ A M C N Y P W Q) (hφ : 0 ≤ φ)
    (hA : ∀ t ω, 0 < A t ω) (hM : ∀ t ω, 0 < M t ω) {V : ℝ}
    (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) (t : ℕ) (ω : Ω) :
    utility φ (C t ω) (M t ω / P t ω) (N t ω) =
      2 * Real.log (A t ω) - Real.log V - 1 / (1 + φ) := by
  have hY := output_eq_technology h hφ hA t ω
  have hN := employment_eq_one h hφ hA t ω
  have hP := h.pos_P t ω
  have hVpos : 0 < V := by
    rw [← hV t ω, hY.1]; exact div_pos (mul_pos hP (hA t ω)) (hM t ω)
  have hmp : M t ω / P t ω = A t ω / V := by
    rw [← hV t ω, hY.1]
    field_simp [(hA t ω).ne', (hM t ω).ne', hP.ne']
  rw [utility, hY.2, hmp, hN, Real.one_rpow, Real.log_div (hA t ω).ne' hVpos.ne']
  ring

/-- Galí (2015), Ex. 2.5(c), p. 49: expected log technology,
`E[log A_t] = log A₀ + t log(1 + γ_a)` (the innovations have mean zero). -/
theorem integral_log_level [IsProbabilityMeasure μ] (G : GaussianInnovations μ ℱ) {A₀ γ : ℝ}
    (hA : 0 < A₀) (hγ : 0 < 1 + γ) (t : ℕ) :
    ∫ ω, Real.log (level A₀ γ G.ε t ω) ∂μ = Real.log A₀ + t * Real.log (1 + γ) := by
  have hfun : (fun ω => Real.log (level A₀ γ G.ε t ω))
      = fun ω => (Real.log A₀ + t * Real.log (1 + γ)) + ∑ s ∈ Finset.range t, G.ε (s + 1) ω := by
    funext ω
    rw [level, Real.log_mul (mul_pos hA (pow_pos hγ t)).ne' (Real.exp_pos _).ne',
      Real.log_mul hA.ne' (pow_pos hγ t).ne', Real.log_pow, Real.log_exp]
  have hint : ∀ s, Integrable (G.ε s) μ := fun s =>
    (G.hasLaw s).integrable (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))
  have hzero : ∀ s, ∫ ω, G.ε s ω ∂μ = 0 := fun s => by
    rw [(G.hasLaw s).integral_eq, integral_id_gaussianReal]
  rw [hfun, integral_add (integrable_const _) (integrable_finsetSum _ fun s _ => hint (s + 1)),
    integral_finsetSum _ fun s _ => hint (s + 1)]
  simp [hzero]

/-- Galí (2015), Ex. 2.5(c), p. 49: closed-form expected lifetime utility
`(2 log A₀ − log V − 1/(1+φ))/(1 − β) + 2 β log(1 + γ_a)/(1 − β)²`. -/
noncomputable def welfareValue (β φ A₀ γa V : ℝ) : ℝ :=
  (2 * Real.log A₀ - Real.log V - 1 / (1 + φ)) / (1 - β) + 2 * Real.log (1 + γa) * β / (1 - β) ^ 2

/-- Galí (2015), Ex. 2.5(c), p. 49 (**infinite horizon**): in an equilibrium with constant
velocity `V`, expected lifetime utility `∑ₜ βᵗ E[U_t]` converges to `welfareValue`. -/
theorem hasSum_expected_welfare [IsProbabilityMeasure μ] (Ga : GaussianInnovations μ ℱ)
    {A₀ γa V : ℝ} (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hφ : 0 ≤ φ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (h : IsEquilibrium μ ℱ β φ (level A₀ γa Ga.ε) M C N Y P W Q) (hM : ∀ t ω, 0 < M t ω)
    (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) :
    HasSum (fun t : ℕ => β ^ t * ∫ ω, utility φ (C t ω) (M t ω / P t ω) (N t ω) ∂μ)
      (welfareValue β φ A₀ γa V) := by
  have hAp := level_pos hA hγa Ga.ε
  have hE : ∀ t : ℕ, ∫ ω, utility φ (C t ω) (M t ω / P t ω) (N t ω) ∂μ
      = (2 * Real.log A₀ - Real.log V - 1 / (1 + φ)) + 2 * Real.log (1 + γa) * t := by
    intro t
    have hfun : (fun ω => utility φ (C t ω) (M t ω / P t ω) (N t ω))
        = fun ω => 2 * Real.log (level A₀ γa Ga.ε t ω) - (Real.log V + 1 / (1 + φ)) := by
      funext ω
      rw [period_utility_eq h hφ hAp hM hV t ω]
      ring
    have hint : Integrable (fun ω => Real.log (level A₀ γa Ga.ε t ω)) μ := by
      have hfun' : (fun ω => Real.log (level A₀ γa Ga.ε t ω))
          = fun ω => (Real.log A₀ + t * Real.log (1 + γa)) +
            ∑ s ∈ Finset.range t, Ga.ε (s + 1) ω := by
        funext ω
        rw [level, Real.log_mul (mul_pos hA (pow_pos hγa t)).ne' (Real.exp_pos _).ne',
          Real.log_mul hA.ne' (pow_pos hγa t).ne', Real.log_pow, Real.log_exp]
      rw [hfun']
      exact (integrable_const _).add (integrable_finsetSum _ fun s _ =>
        (Ga.hasLaw (s + 1)).integrable (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1)))
    rw [hfun, integral_sub (hint.const_mul 2) (integrable_const _), integral_const_mul,
      integral_log_level Ga hA hγa t]
    simp
    ring
  have hg := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left
    (2 * Real.log A₀ - Real.log V - 1 / (1 + φ))
  have hn := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)).mul_left (2 * Real.log (1 + γa))
  have hsum := hg.add hn
  have hne : (1 - β) ≠ 0 := by linarith
  convert hsum using 1
  · funext t
    rw [hE t]
    ring
  · rw [welfareValue]
    field_simp

/-- Galí (2015), Ex. 2.5(c): `welfareValue = K − log V/(1 − β)` with `K` independent of
monetary policy. -/
theorem welfareValue_eq (β φ A₀ γa V : ℝ) :
    welfareValue β φ A₀ γa V = welfareValue β φ A₀ γa 1 - Real.log V / (1 - β) := by
  simp only [welfareValue, Real.log_one, sub_zero]
  ring

/-- Galí (2015), Ex. 2.5(c): welfare is strictly decreasing in velocity: for `V₁, V₂ > 0`,
`welfare(V₂) < welfare(V₁)` iff `V₁ < V₂`. -/
theorem welfareValue_lt_iff {β φ A₀ γa V₁ V₂ : ℝ} (hβ : β < 1) (h1 : 0 < V₁) (h2 : 0 < V₂) :
    welfareValue β φ A₀ γa V₂ < welfareValue β φ A₀ γa V₁ ↔ V₁ < V₂ := by
  rw [welfareValue_eq β φ A₀ γa V₂, welfareValue_eq β φ A₀ γa V₁, sub_lt_sub_iff_left,
    div_lt_div_iff_of_pos_right (by linarith), Real.log_lt_log_iff h1 h2]

/-- Galí (2015), Ex. 2.5(c), p. 49: welfare is strictly decreasing in money growth `γ_m`
(among policies with an equilibrium, `Q* < 1`). -/
theorem welfare_strictAnti_gamma {β φ A₀ γa v γ₁ γ₂ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ₁ : 0 < 1 + γ₁) (h12 : γ₁ < γ₂) (hQ : Qstar β γ₁ v < 1) :
    welfareValue β φ A₀ γa (velocity β γ₂ v) < welfareValue β φ A₀ γa (velocity β γ₁ v) := by
  have hγ₂ : 0 < 1 + γ₂ := by linarith
  have hlt : Qstar β γ₂ v < Qstar β γ₁ v :=
    div_lt_div_of_pos_left (mul_pos hβ0 (Real.exp_pos _)) hγ₁ (by linarith)
  have hpos : 0 < Qstar β γ₂ v := div_pos (mul_pos hβ0 (Real.exp_pos _)) hγ₂
  rw [welfareValue_lt_iff hβ1 (by rw [velocity]; linarith) (by rw [velocity]; linarith),
    velocity, velocity]
  linarith

/-- Galí (2015), Ex. 2.5(c), p. 49: welfare is strictly increasing in the variance `σ_m²` of
money growth (among policies with an equilibrium, `Q* < 1`): a higher variance raises
`E_t[M_t/M_{t+1}]`, the bond price and real balances. -/
theorem welfare_strictMono_var {β φ A₀ γa γ v₁ v₂ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < 1 + γ) (h12 : v₁ < v₂) (hQ : Qstar β γ v₂ < 1) :
    welfareValue β φ A₀ γa (velocity β γ v₁) < welfareValue β φ A₀ γa (velocity β γ v₂) := by
  have hlt : Qstar β γ v₁ < Qstar β γ v₂ := by
    unfold Qstar
    gcongr
  rw [welfareValue_lt_iff hβ1 (by rw [velocity]; linarith) (by rw [velocity]; linarith),
    velocity, velocity]
  linarith

/-- Galí (2015), Ex. 2.5(c), p. 49: as a function of the constant nominal rate `i > 0`
(`Q* = e^{−i}`, `V = 1 − e^{−i}`), welfare is strictly decreasing. -/
theorem welfare_rate_strictAnti {β φ A₀ γa : ℝ} (hβ : β < 1) :
    StrictAntiOn (fun i => welfareValue β φ A₀ γa (1 - Real.exp (-i))) (Set.Ioi 0) := by
  intro i hi j hj hij
  have hpos : ∀ x : ℝ, 0 < x → 0 < 1 - Real.exp (-x) := fun x hx => by
    have := Real.exp_lt_exp.2 (show -x < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  simp only
  rw [welfareValue_lt_iff hβ (hpos i hi) (hpos j hj)]
  have := Real.exp_lt_exp.2 (show -j < -i by linarith)
  linarith

/-- Galí (2015), Ex. 2.5(c), p. 49: welfare is unbounded as the nominal rate falls to zero:
`welfare(1 − e^{−i}) → ∞` as `i → 0⁺`. The Friedman rule is a supremum, not attained. -/
theorem tendsto_welfare_rate {β φ A₀ γa : ℝ} (hβ : β < 1) :
    Tendsto (fun i => welfareValue β φ A₀ γa (1 - Real.exp (-i))) (𝓝[>] 0) atTop := by
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
  refine (tendsto_atTop_add_const_left _ (welfareValue β φ A₀ γa 1) hlog).congr fun i => ?_
  rw [welfareValue_eq β φ A₀ γa (1 - Real.exp (-i))]
  ring

/-- Galí (2015), Ex. 2.5(c), p. 49 (**the optimal policy must satisfy the Friedman rule**):
every policy `(γ_m, σ_m²)` with an equilibrium (`Q* < 1`, i.e. `i > 0`) is strictly improved
upon by another admissible policy with an equilibrium; so no policy with `i > 0` is optimal. -/
theorem not_optimal_of_equilibrium {β φ A₀ γa γ v : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < 1 + γ) (hQ : Qstar β γ v < 1) :
    ∃ γ', 0 < 1 + γ' ∧ Qstar β γ' v < 1 ∧
      welfareValue β φ A₀ γa (velocity β γ v) < welfareValue β φ A₀ γa (velocity β γ' v) := by
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
    rw [welfareValue_lt_iff hβ1 (by rw [velocity, this, hq']; linarith)
      (by rw [velocity, ← hq]; linarith), velocity, velocity, this, ← hq, hq']
    linarith

/-! ### (c) Welfare as the expectation of lifetime utility -/

omit mΩ in
/-- Galí (2015), Ex. 2.5, p. 49: `log A_t = log A₀ + t log(1 + γ) + ε_1 + ⋯ + ε_t`. -/
theorem log_level_eq {A₀ γ : ℝ} (hA : 0 < A₀) (hγ : 0 < 1 + γ) (ε : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : Real.log (level A₀ γ ε t ω) =
      (Real.log A₀ + t * Real.log (1 + γ)) + ∑ s ∈ Finset.range t, ε (s + 1) ω := by
  rw [level, Real.log_mul (mul_pos hA (pow_pos hγ t)).ne' (Real.exp_pos _).ne',
    Real.log_mul hA.ne' (pow_pos hγ t).ne', Real.log_pow, Real.log_exp]

/-- Galí (2015), Ex. 2.5: Gaussian innovations are integrable. -/
theorem integrable_innovation (G : GaussianInnovations μ ℱ) (s : ℕ) : Integrable (G.ε s) μ :=
  (G.hasLaw s).integrable (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))

/-- Galí (2015), Ex. 2.5: `E|ε_s| = ∫ |x| dN(0, σ²)`, the same at every date. -/
theorem integral_abs_innovation (G : GaussianInnovations μ ℱ) (s : ℕ) :
    ∫ ω, |G.ε s ω| ∂μ = ∫ x, |x| ∂(gaussianReal 0 G.var) :=
  (G.hasLaw s).integral_comp (f := fun x : ℝ => |x|) continuous_abs.aestronglyMeasurable

/-- Galí (2015), Ex. 2.5(c), p. 49 (**expected lifetime utility**): in an equilibrium with
constant velocity `V`, `E[∑ₜ βᵗ U_t] = ∑ₜ βᵗ E[U_t] = welfareValue`. The interchange of the
expectation and the infinite sum is justified by the geometric bound
`E|βᵗ U_t| ≤ βᵗ (2(|log A₀| + t|log(1+γ_a)| + t E|ε|) + |log V + 1/(1+φ)|)`. -/
theorem integral_tsum_welfare [IsProbabilityMeasure μ] (Ga : GaussianInnovations μ ℱ)
    {A₀ γa V : ℝ} (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hφ : 0 ≤ φ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (h : IsEquilibrium μ ℱ β φ (level A₀ γa Ga.ε) M C N Y P W Q) (hM : ∀ t ω, 0 < M t ω)
    (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) :
    ∫ ω, ∑' t : ℕ, β ^ t * utility φ (C t ω) (M t ω / P t ω) (N t ω) ∂μ =
      welfareValue β φ A₀ γa V := by
  have hAp := level_pos hA hγa Ga.ε
  set K := Real.log V + 1 / (1 + φ) with hK
  set m₁ := ∫ x, |x| ∂(gaussianReal 0 Ga.var) with hm₁
  have hm₁0 : 0 ≤ m₁ := integral_nonneg fun x => abs_nonneg x
  have hF : ∀ t : ℕ, (fun ω => β ^ t * utility φ (C t ω) (M t ω / P t ω) (N t ω)) =
      fun ω => β ^ t * (2 * ((Real.log A₀ + t * Real.log (1 + γa)) +
        ∑ s ∈ Finset.range t, Ga.ε (s + 1) ω) - K) := by
    intro t
    funext ω
    rw [period_utility_eq h hφ hAp hM hV t ω, log_level_eq hA hγa Ga.ε t ω, hK]
    ring
  have hsumint : ∀ t : ℕ, Integrable (fun ω => ∑ s ∈ Finset.range t, Ga.ε (s + 1) ω) μ :=
    fun t => integrable_finsetSum _ fun s _ => integrable_innovation Ga (s + 1)
  have hint : ∀ t : ℕ, Integrable
      (fun ω => β ^ t * utility φ (C t ω) (M t ω / P t ω) (N t ω)) μ := by
    intro t
    rw [hF t]
    exact (((integrable_const _).add (hsumint t)).const_mul 2 |>.sub
      (integrable_const K)).const_mul (β ^ t)
  set g : ℕ → ℝ := fun t => β ^ t * ((2 * |Real.log A₀| + |K|) +
    (2 * |Real.log (1 + γa)| + 2 * m₁) * t) with hg
  have hgs : Summable g := by
    have h1 := (summable_geometric_of_lt_one hβ0 hβ1).mul_left (2 * |Real.log A₀| + |K|)
    have h2 := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)).summable.mul_left
      (2 * |Real.log (1 + γa)| + 2 * m₁)
    refine (h1.add h2).congr fun t => ?_
    simp only [hg]
    ring
  have hbound : ∀ t : ℕ,
      ∫ ω, ‖β ^ t * utility φ (C t ω) (M t ω / P t ω) (N t ω)‖ ∂μ ≤ g t := by
    intro t
    have hpt : ∀ ω, ‖β ^ t * utility φ (C t ω) (M t ω / P t ω) (N t ω)‖ ≤
        β ^ t * ((2 * |Real.log A₀| + |K|) + 2 * t * |Real.log (1 + γa)| +
          2 * ∑ s ∈ Finset.range t, |Ga.ε (s + 1) ω|) := by
      intro ω
      have e := congrFun (hF t) ω
      rw [e, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
      have h1 := Finset.abs_sum_le_sum_abs (fun s => Ga.ε (s + 1) ω) (Finset.range t)
      have h2 : |(t : ℝ) * Real.log (1 + γa)| = t * |Real.log (1 + γa)| := by
        rw [abs_mul, Nat.abs_cast]
      have h3 := abs_add_le (Real.log A₀ + t * Real.log (1 + γa))
        (∑ s ∈ Finset.range t, Ga.ε (s + 1) ω)
      have h4 := abs_add_le (Real.log A₀) (t * Real.log (1 + γa))
      have h5 := abs_sub (2 * ((Real.log A₀ + t * Real.log (1 + γa)) +
        ∑ s ∈ Finset.range t, Ga.ε (s + 1) ω)) K
      rw [abs_mul, abs_two] at h5
      linarith
    have hrint : Integrable (fun ω => β ^ t * ((2 * |Real.log A₀| + |K|) +
        2 * t * |Real.log (1 + γa)| + 2 * ∑ s ∈ Finset.range t, |Ga.ε (s + 1) ω|)) μ :=
      ((integrable_const _).add ((integrable_finsetSum _ fun s _ =>
        (integrable_innovation Ga (s + 1)).abs).const_mul 2)).const_mul (β ^ t)
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _) hrint
      (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add (integrable_const _) ((integrable_finsetSum _ fun s _ =>
      (integrable_innovation Ga (s + 1)).abs).const_mul 2), integral_const_mul,
      integral_finsetSum _ fun s _ => (integrable_innovation Ga (s + 1)).abs]
    simp only [integral_abs_innovation, ← hm₁, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, integral_const, probReal_univ, smul_eq_mul, one_mul, hg]
    ring
  have hsum : Summable fun t : ℕ =>
      ∫ ω, ‖β ^ t * utility φ (C t ω) (M t ω / P t ω) (N t ω)‖ ∂μ :=
    hgs.of_nonneg_of_le (fun t => integral_nonneg fun ω => norm_nonneg _) hbound
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp only [integral_const_mul]
  exact (hasSum_expected_welfare Ga hA hγa hφ hβ0 hβ1 h hM hV).tsum_eq

/-! ### A concrete probability space carrying the shocks (non-vacuity) -/

/-- Galí (2015), Ex. 2.5, p. 49: the law of one period's innovations `(ε^a_t, ε^m_t)`,
independent `N(0, σ_a²)` and `N(0, σ_m²)`. -/
noncomputable abbrev pairLaw (va vm : ℝ≥0) : Measure (ℝ × ℝ) :=
  (gaussianReal 0 va).prod (gaussianReal 0 vm)

/-- Galí (2015), Ex. 2.5, p. 49: the sample space `ℕ → ℝ × ℝ` of innovation sequences with the
i.i.d. product law `⊗ₜ pairLaw` (`Measure.infinitePi`). -/
noncomputable abbrev shockMeasure (va vm : ℝ≥0) : Measure (ℕ → ℝ × ℝ) :=
  Measure.infinitePi fun _ : ℕ => pairLaw va vm

/-- Galí (2015), Ex. 2.5, p. 49: the natural filtration `ℱ_t = σ((ε^a_s, ε^m_s), s ≤ t)` of the
coordinate process. -/
noncomputable def shockFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ × ℝ)) :=
  Filtration.natural (fun (i : ℕ) (ω : ℕ → ℝ × ℝ) => ω i)
    fun i => (measurable_pi_apply i).stronglyMeasurable

/-- Galí (2015), Ex. 2.5, p. 49: the date-`t+1` innovation pair is independent of `ℱ_t` under
the product law. -/
theorem coord_indep (va vm : ℝ≥0) (t : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω (t + 1)) inferInstance)
      (shockFiltration t) (shockMeasure va vm) := by
  have hI : iIndep (fun i => MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance)
      (shockMeasure va vm) :=
    (iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_infinitePi (X := fun _ (x : ℝ × ℝ) => x)
      (P := fun _ : ℕ => pairLaw va vm) (fun _ => measurable_id))
  have h := indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hI
    (S := {t + 1}) (T := Set.Iic t) (Set.disjoint_singleton_left.2 (by simp))
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left, Set.mem_Iic] at h
  exact h

/-- Galí (2015), Ex. 2.5, p. 49: `ℱ_t` contains the date-`t` innovations. -/
theorem comap_le_shockFiltration (t : ℕ) :
    MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω t) inferInstance ≤ shockFiltration t :=
  le_iSup₂ (f := fun j (_ : j ≤ t) =>
    MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω j) inferInstance) t le_rfl

/-- Galí (2015), Ex. 2.5, p. 49: the technology innovations `ε^a_t = (ω t).1`, an i.i.d.
`N(0, σ_a²)` sequence adapted to the natural filtration (an instance of
`GaussianInnovations`). -/
noncomputable def techInnovations (va vm : ℝ≥0) :
    GaussianInnovations (shockMeasure va vm) shockFiltration where
  ε := fun t ω => (ω t).1
  var := va
  adapted := fun t => measurable_fst.comp ((comap_measurable _).mono
    (comap_le_shockFiltration t) le_rfl)
  hasLaw := fun t => HasLaw.comp (Y := Prod.fst)
    ⟨measurable_fst.aemeasurable, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
    (measurePreserving_eval_infinitePi (fun _ : ℕ => pairLaw va vm) t).hasLaw
  indep := fun t => indep_of_indep_of_le_left (coord_indep va vm t)
    (measurable_fst.comp (comap_measurable _)).comap_le

/-- Galí (2015), Ex. 2.5, p. 49: the money-growth innovations `ε^m_t = (ω t).2`, an i.i.d.
`N(0, σ_m²)` sequence adapted to the natural filtration. -/
noncomputable def moneyInnovations (va vm : ℝ≥0) :
    GaussianInnovations (shockMeasure va vm) shockFiltration where
  ε := fun t ω => (ω t).2
  var := vm
  adapted := fun t => measurable_snd.comp ((comap_measurable _).mono
    (comap_le_shockFiltration t) le_rfl)
  hasLaw := fun t => HasLaw.comp (Y := Prod.snd)
    ⟨measurable_snd.aemeasurable, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩
    (measurePreserving_eval_infinitePi (fun _ : ℕ => pairLaw va vm) t).hasLaw
  indep := fun t => indep_of_indep_of_le_left (coord_indep va vm t)
    (measurable_snd.comp (comap_measurable _)).comap_le

/-- Galí (2015), Ex. 2.5(b), p. 49 (**an exact equilibrium genuinely exists**): on the concrete
space `shockMeasure`, with i.i.d. Gaussian technology and money innovations, if
`β e^{σ_m²/2} < 1 + γ_m` the constant-velocity allocation is an equilibrium. -/
theorem exists_exact_equilibrium (va vm : ℝ≥0) {A₀ γa M₀ γm : ℝ} (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) (hQ : Qstar β γm vm < 1) :
    IsEquilibrium (shockMeasure va vm) shockFiltration β φ
      (level A₀ γa (techInnovations va vm).ε) (level M₀ γm (moneyInnovations va vm).ε)
      (level A₀ γa (techInnovations va vm).ε) (fun _ _ => 1)
      (level A₀ γa (techInnovations va vm).ε)
      (fun t ω => velocity β γm vm * level M₀ γm (moneyInnovations va vm).ε t ω /
        level A₀ γa (techInnovations va vm).ε t ω)
      (fun t ω => velocity β γm vm * level M₀ γm (moneyInnovations va vm).ε t ω)
      (fun _ _ => Qstar β γm vm) :=
  candidate_isEquilibrium (β := β) (techInnovations va vm) (moneyInnovations va vm) hA hγa hM
    hγm hQ

end Gali.ClassicalMonetaryModel.Ex2_5
