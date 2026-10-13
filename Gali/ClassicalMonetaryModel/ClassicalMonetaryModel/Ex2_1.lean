/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ClassicalMonetaryModel.Expectations
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential

/-!
# Exercise 2.1: optimality conditions under nonseparable leisure

Galí (2015), Chapter 2, Exercise 2.1, p. 46. The period utility is
`U(C, N) = ([C (1 − N)^ν]^{1−σ} − 1)/(1 − σ)` (`periodUtility`; its limit
`log C + ν log(1 − N)` for `σ = 1` is included), with `σ > 0`, `ν > 0`, `0 ≤ N < 1`.
The household problem is that of §2.1 (pp. 18–20): budget `P_t C_t + Q_t B_t ≤ B_{t−1} +
W_t N_t + D_t`.

## Marginal utilities (exact derivatives)

`hasDerivAt_periodUtility_C`, `hasDerivAt_periodUtility_N`: `U_C = [C(1−N)^ν]^{−σ}(1−N)^ν`
(`margUtilC`, `= C^{−σ}(1−N)^{ν(1−σ)}` by `margUtilC_eq`) and
`U_N = −[C(1−N)^ν]^{−σ} C ν (1−N)^{ν−1}` (`margUtilN`); `mrs_eq`: `−U_N/U_C = ν C/(1 − N)`.

## The static (labour-supply) condition, eq. (4), p. 19

Hours are perturbed along the budget line `P dC = W dN`.
* `static_foc_necessary`: a local optimum satisfies `U_C (W/P) + U_N = 0`, i.e. eq. (4);
  `static_wage_necessary`: hence `W/P = ν C/(1 − N)`.
* `static_foc_sufficient`: conversely `W/P = ν C/(1 − N)` gives the global optimum over all
  feasible hours (`U` is a strictly increasing function of `C(1 − N)^ν`, whose logarithm is
  concave along the budget line; this works for every `σ > 0`, although `U` itself is not
  jointly concave when `σ < 1` and `(1 − σ)(1 + ν) > 1`). `static_optimum_iff` combines both.
* `labour_supply_log_iff` (**exact**): `w − p = c + log ν − log(1 − N)`.
* `hasDerivAt_labourSupply_family` (**first order**): along `c = c̄ + s ĉ`, `n = n̄ + s n̂`
  the right-hand side has derivative `ĉ + (N/(1 − N)) n̂` at `s = 0`: the log-linear labour
  supply `ŵ − p̂ = ĉ + (N/(1−N)) n̂`, with `N = e^{n̄}`.

## The Euler equation, eq. (5), p. 19

General tools, stated for an arbitrary `ExpectationSystem`:
* `hasDerivAt_E_of_uniform`: if `F(δ)(ω') − F(0)(ω') − δ L(ω') = o(δ)` uniformly in `ω'`,
  then `δ ↦ E_t F(δ)` has derivative `E_t L` (the abstract `E_t` only needs to be linear,
  monotone and constant-preserving).
* `uniform_of_concave`: for concave utilities the uniformity follows from a uniform modulus of
  continuity of marginal utility, which always holds with finitely many states
  (`uniformCont_of_finite`).
* `euler_necessary_generic`, `euler_sufficient_generic`: first-order condition of the
  one-period bond perturbation, necessary (local optimum) and sufficient (concavity).

For Exercise 2.1: `euler_necessary` (necessity under the uniform-continuity hypothesis),
`euler_necessary_finite` (finitely many states, no extra hypothesis), `euler_sufficient`, and
`EulerEq`, the book's eq. (5) `Q_t = β E_t[(U_{C,t+1}/U_{C,t})(P_t/P_{t+1})]` written as
`Q_t U_{C,t}/P_t = β E_t[U_{C,t+1}/P_{t+1}]`.

## Log-linear Euler equation

* `eulerEq_iff_moment` (**exact**): with `Q = e^{−i}`, `β = e^{−ρ}`, `C = e^c`, `P = e^p`,
  `1 − N = e^ℓ`: `E_t[exp(i_t − ρ − σΔc_{t+1} − Δp_{t+1} + ν(1−σ)Δℓ_{t+1})] = 1`.
* `pf_eulerEq_iff` (**exact**, perfect foresight):
  `i_t − π_{t+1} − ρ = σΔc_{t+1} − ν(1−σ)Δℓ_{t+1}`.
* `hasDerivAt_moment_family` (**first order**, uncertainty): along `i = ρ + s î`,
  `c = c̄ + s ĉ`, `p = p̄ + s p̂`, `n = n̄ + s n̂` (bounded deviations; `ℓ = log(1 − e^n)`), the
  Euler moment has derivative `E_t` of `linearisedEuler` at `s = 0`;
  `linearisedEuler_zero_iff`: this vanishes iff
  `ĉ_t = E_t ĉ_{t+1} − σ^{−1}(î_t − E_t π̂_{t+1}) + σ^{−1} ν (1 − σ) (N/(1 − N)) E_t Δn̂_{t+1}`,
  the log-linear Euler equation with the nonseparable-leisure term.
-/

namespace Gali.ClassicalMonetaryModel.Ex2_1

open Filter Topology

/-! ### Utility -/

/-- Galí (2015), Exercise 2.1, p. 46: the outer transformation `g(x) = (x^{1−σ} − 1)/(1 − σ)`
of the composite `x = C(1 − N)^ν`, and its limit `log x` for `σ = 1` (restated from the
Chapter 3 project, `utilC`). -/
noncomputable def utilC (σ x : ℝ) : ℝ :=
  if σ = 1 then Real.log x else (x ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), Exercise 2.1, p. 46: `g'(x) = x^{−σ}` for `x > 0`, in both the `σ ≠ 1` and
the log case (restated from the Chapter 3 project). -/
theorem hasDerivAt_utilC (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (utilC σ) (x ^ (-σ)) x := by
  by_cases hσ : σ = 1
  · have hfun : utilC σ = Real.log := funext fun x => by simp [utilC, hσ]
    rw [hfun, hσ, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hx.ne'
  · have hfun : utilC σ = fun x => (x ^ (1 - σ) - 1) / (1 - σ) :=
      funext fun x => by simp [utilC, hσ]
    have hs : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    rw [hfun]
    refine (((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hx.ne')).sub_const 1).div_const
      (1 - σ)).congr_deriv ?_
    rw [show (1 : ℝ) - σ - 1 = -σ by ring]
    field_simp

/-- Galí (2015), Exercise 2.1, p. 46: `g` is strictly increasing on `(0, ∞)`. -/
theorem utilC_strictMonoOn (σ : ℝ) : StrictMonoOn (utilC σ) (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (fun x hx => ?_) (fun x hx => ?_)
  · exact (hasDerivAt_utilC σ hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi] at hx
    rw [(hasDerivAt_utilC σ hx).deriv]
    exact Real.rpow_pos_of_pos hx _

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangent lines (Galí (2015), p. 18, concavity of utility; restated from the Chapter 3
project). -/
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

/-- Galí (2015), p. 18 (concavity): a function differentiable on `(0, ∞)` with nonincreasing
derivative satisfies the tangent inequality `f y ≤ f x + f'(x)(y − x)` for `x, y > 0`. -/
theorem tangent_of_deriv {f f' : ℝ → ℝ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hd : ∀ z, 0 < z → HasDerivAt f (f' z) z) (hanti : AntitoneOn f' (Set.Ioi 0)) :
    f y ≤ f x + f' x * (y - x) := by
  refine le_tangent hx hy.le (fun z hz => ?_) hd hanti
  have hz0 : 0 < z := by
    rcases Set.mem_uIcc.1 hz with h | h
    · exact lt_of_lt_of_le hx h.1
    · exact lt_of_lt_of_le hy h.1
  exact (hd z hz0).continuousAt.continuousWithinAt

/-- Galí (2015), Exercise 2.1, p. 46: period utility `U(C, N) = g(C (1 − N)^ν)`. -/
noncomputable def periodUtility (σ ν C N : ℝ) : ℝ := utilC σ (C * (1 - N) ^ ν)

/-- Galí (2015), Exercise 2.1, p. 46: marginal utility of consumption
`U_C = [C(1 − N)^ν]^{−σ} (1 − N)^ν`. -/
noncomputable def margUtilC (σ ν C N : ℝ) : ℝ := (C * (1 - N) ^ ν) ^ (-σ) * (1 - N) ^ ν

/-- Galí (2015), Exercise 2.1, p. 46: marginal utility of hours
`U_N = −[C(1 − N)^ν]^{−σ} C ν (1 − N)^{ν−1}`. -/
noncomputable def margUtilN (σ ν C N : ℝ) : ℝ :=
  -((C * (1 - N) ^ ν) ^ (-σ) * (C * (ν * (1 - N) ^ (ν - 1))))

/-- Galí (2015), Exercise 2.1, p. 46 (**exact derivative**): `∂U/∂C = margUtilC`. -/
theorem hasDerivAt_periodUtility_C (σ ν : ℝ) {C N : ℝ} (hC : 0 < C) (hN : N < 1) :
    HasDerivAt (fun C' => periodUtility σ ν C' N) (margUtilC σ ν C N) C := by
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos (by linarith) ν
  exact (hasDerivAt_utilC σ (mul_pos hC hL)).comp C (hasDerivAt_mul_const ((1 - N) ^ ν))

/-- Galí (2015), Exercise 2.1, p. 46: `d/dN (1 − N)^ν = −ν (1 − N)^{ν−1}` for `N < 1`. -/
theorem hasDerivAt_leisure_pow (ν : ℝ) {N : ℝ} (hN : N < 1) :
    HasDerivAt (fun N' => (1 - N') ^ ν) (ν * (1 - N) ^ (ν - 1) * (-1)) N :=
  (Real.hasDerivAt_rpow_const (x := 1 - N) (p := ν) (Or.inl (sub_pos.2 hN).ne')).comp N
    ((hasDerivAt_id N).const_sub 1)

/-- Galí (2015), Exercise 2.1, p. 46 (**exact derivative**): `∂U/∂N = margUtilN`. -/
theorem hasDerivAt_periodUtility_N (σ ν : ℝ) {C N : ℝ} (hC : 0 < C) (hN : N < 1) :
    HasDerivAt (fun N' => periodUtility σ ν C N') (margUtilN σ ν C N) N := by
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos (by linarith) ν
  refine ((hasDerivAt_utilC σ (mul_pos hC hL)).comp N
    ((hasDerivAt_leisure_pow ν hN).const_mul C)).congr_deriv ?_
  unfold margUtilN
  ring

/-- Galí (2015), Exercise 2.1, p. 46: `U_C > 0`. -/
theorem margUtilC_pos (σ ν : ℝ) {C N : ℝ} (hC : 0 < C) (hN : N < 1) :
    0 < margUtilC σ ν C N := by
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos (by linarith) ν
  exact mul_pos (Real.rpow_pos_of_pos (mul_pos hC hL) _) hL

/-- Galí (2015), Exercise 2.1, p. 46: `U_C = C^{−σ} (1 − N)^{ν(1−σ)}`. -/
theorem margUtilC_eq (σ ν : ℝ) {C N : ℝ} (hC : 0 < C) (hN : N < 1) :
    margUtilC σ ν C N = C ^ (-σ) * (1 - N) ^ (ν * (1 - σ)) := by
  have h1 : 0 < 1 - N := by linarith
  unfold margUtilC
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg h1.le ν), ← Real.rpow_mul h1.le, mul_assoc,
    ← Real.rpow_add h1]
  congr 2
  ring

/-- Galí (2015), Exercise 2.1, p. 46, and eq. (4), p. 19: the marginal rate of substitution
`−U_N/U_C = ν C/(1 − N)`. -/
theorem mrs_eq (σ ν : ℝ) {C N : ℝ} (hC : 0 < C) (hN : N < 1) :
    -margUtilN σ ν C N / margUtilC σ ν C N = ν * C / (1 - N) := by
  have h1 : 0 < 1 - N := by linarith
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos h1 ν
  have hX : 0 < (C * (1 - N) ^ ν) ^ (-σ) := Real.rpow_pos_of_pos (mul_pos hC hL) _
  unfold margUtilN margUtilC
  rw [Real.rpow_sub_one h1.ne', neg_neg]
  field_simp

/-! ### The static (labour-supply) problem -/

/-- Galí (2015), eq. (4), p. 19, for Exercise 2.1 (**necessity**): if hours `N` (with
`N < 1`, `C > 0`) are a local optimum along the budget line `P C = W N + X` (perturbation
`P dC = W dN`, everything else unchanged), then `U_C · W/P + U_N = 0`. -/
theorem static_foc_necessary {σ ν P W X C N : ℝ} (hP : 0 < P) (hC : 0 < C) (hN : N < 1)
    (hbud : P * C = W * N + X)
    (hloc : IsLocalMax (fun N' => periodUtility σ ν ((W * N' + X) / P) N') N) :
    margUtilC σ ν C N * (W / P) + margUtilN σ ν C N = 0 := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos (by linarith) ν
  have hin : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
    have := (((hasDerivAt_id N).const_mul W).add_const X).div_const P
    simpa using this
  have hprod := hin.mul (hasDerivAt_leisure_pow ν hN)
  have hu : HasDerivAt (utilC σ) (((W * N + X) / P * (1 - N) ^ ν) ^ (-σ))
      ((W * N + X) / P * (1 - N) ^ ν) := hasDerivAt_utilC σ (by rw [hCeq]; exact mul_pos hC hL)
  have hg := hu.comp N hprod
  have h0 := hloc.hasDerivAt_eq_zero hg
  rw [hCeq] at h0
  unfold margUtilC margUtilN
  linear_combination h0

/-- Galí (2015), eq. (4), p. 19, for Exercise 2.1: a local optimum of hours satisfies
`W/P = ν C/(1 − N)`. -/
theorem static_wage_necessary {σ ν P W X C N : ℝ} (hP : 0 < P) (hC : 0 < C) (hN : N < 1)
    (hbud : P * C = W * N + X)
    (hloc : IsLocalMax (fun N' => periodUtility σ ν ((W * N' + X) / P) N') N) :
    W / P = ν * C / (1 - N) := by
  have h := static_foc_necessary hP hC hN hbud hloc
  have hpos := margUtilC_pos σ ν hC hN
  rw [← mrs_eq σ ν hC hN, eq_div_iff hpos.ne']
  linear_combination h

/-- Galí (2015), Exercise 2.1, p. 46 (**sufficiency**): if `W/P = ν C/(1 − N)` at a point
`(C, N)` on the budget line (`C > 0`, `N < 1`, `ν > 0`), then `(C, N)` maximises utility over
all feasible hours `N' < 1` with `C' = (W N' + X)/P > 0`. -/
theorem static_foc_sufficient {σ ν P W X C N : ℝ} (hν : 0 < ν) (hP : 0 < P) (hC : 0 < C)
    (hN : N < 1) (hbud : P * C = W * N + X) (hfoc : W / P = ν * C / (1 - N)) {N' : ℝ}
    (hN' : N' < 1) (hC' : 0 < (W * N' + X) / P) :
    periodUtility σ ν ((W * N' + X) / P) N' ≤ periodUtility σ ν C N := by
  set C' := (W * N' + X) / P with hC'def
  have h1 : 0 < 1 - N := by linarith
  have h1' : 0 < 1 - N' := by linarith
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos h1 ν
  have hL' : 0 < (1 - N') ^ ν := Real.rpow_pos_of_pos h1' ν
  have hdiff : C' - C = ν * C / (1 - N) * (N' - N) := by
    rw [← hfoc, hC'def, show C = (W * N + X) / P by rw [← hbud]; field_simp]
    field_simp
    ring
  -- `log` of the composite is concave along the budget line
  have hlogC : Real.log C' ≤ Real.log C + (C' / C - 1) := by
    have := Real.log_le_sub_one_of_pos (div_pos hC' hC)
    rw [Real.log_div hC'.ne' hC.ne'] at this
    linarith
  have hlogN : Real.log (1 - N') ≤ Real.log (1 - N) + ((1 - N') / (1 - N) - 1) := by
    have := Real.log_le_sub_one_of_pos (div_pos h1' h1)
    rw [Real.log_div h1'.ne' h1.ne'] at this
    linarith
  have hkey : Real.log (C' * (1 - N') ^ ν) ≤ Real.log (C * (1 - N) ^ ν) := by
    rw [Real.log_mul hC'.ne' hL'.ne', Real.log_mul hC.ne' hL.ne', Real.log_rpow h1',
      Real.log_rpow h1]
    have e1 : C' / C - 1 = ν * ((N' - N) / (1 - N)) := by
      rw [div_sub_one hC.ne', hdiff]
      field_simp
    have e2 : (1 - N') / (1 - N) - 1 = -((N' - N) / (1 - N)) := by
      field_simp
      ring
    rw [e1] at hlogC
    rw [e2] at hlogN
    nlinarith
  have hle : C' * (1 - N') ^ ν ≤ C * (1 - N) ^ ν :=
    (Real.log_le_log_iff (mul_pos hC' hL') (mul_pos hC hL)).1 hkey
  exact (utilC_strictMonoOn σ).monotoneOn (mul_pos hC' hL') (mul_pos hC hL) hle

/-- Galí (2015), p. 19: a global optimum of the static problem over all feasible plans with
`0 < N < 1` and `C > 0` is a local optimum along the budget line. -/
theorem static_isLocalMax_of_optimal {σ ν P W X C N : ℝ} (hP : 0 < P) (hN : N < 1)
    (hC : 0 < C) (hbud : P * C = W * N + X)
    (hopt : ∀ N', N' < 1 → 0 < (W * N' + X) / P →
      periodUtility σ ν ((W * N' + X) / P) N' ≤ periodUtility σ ν C N) :
    IsLocalMax (fun N' => periodUtility σ ν ((W * N' + X) / P) N') N := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hcont : Continuous fun N' : ℝ => (W * N' + X) / P := by fun_prop
  have h1 : ∀ᶠ N' in 𝓝 N, 0 < (W * N' + X) / P :=
    (hcont.tendsto N).eventually_const_lt (by rw [hCeq]; exact hC)
  filter_upwards [h1, eventually_lt_nhds hN] with N' h1' h2'
  rw [hCeq]
  exact hopt N' h2' h1'

/-- Galí (2015), eq. (4), p. 19, for Exercise 2.1: for `ν > 0`, a point with `C > 0`,
`N < 1` on the budget line solves the static problem iff `W/P = ν C/(1 − N)`. -/
theorem static_optimum_iff {σ ν P W X C N : ℝ} (hν : 0 < ν) (hP : 0 < P) (hC : 0 < C)
    (hN : N < 1) (hbud : P * C = W * N + X) :
    (∀ N', N' < 1 → 0 < (W * N' + X) / P →
      periodUtility σ ν ((W * N' + X) / P) N' ≤ periodUtility σ ν C N) ↔
      W / P = ν * C / (1 - N) :=
  ⟨fun h => static_wage_necessary hP hC hN hbud (static_isLocalMax_of_optimal hP hN hC hbud h),
    fun h _ hN' hC' => static_foc_sufficient hν hP hC hN hbud h hN' hC'⟩

/-- Galí (2015), Exercise 2.1 (**exact log form** of the labour-supply condition):
`W/P = ν C/(1 − N)` iff `w − p = c + log ν − log(1 − N)`. -/
theorem labour_supply_log_iff {ν W P C N : ℝ} (hν : 0 < ν) (hW : 0 < W) (hP : 0 < P)
    (hC : 0 < C) (hN : N < 1) :
    W / P = ν * C / (1 - N) ↔
      Real.log W - Real.log P = Real.log C + Real.log ν - Real.log (1 - N) := by
  have h1 : 0 < 1 - N := by linarith
  rw [← Real.log_injOn_pos.eq_iff (div_pos hW hP) (div_pos (mul_pos hν hC) h1),
    Real.log_div hW.ne' hP.ne', Real.log_div (mul_pos hν hC).ne' h1.ne',
    Real.log_mul hν.ne' hC.ne']
  constructor <;> intro h <;> linarith

/-- Galí (2015), Exercise 2.1 (**exact derivative**): with `N = e^n < 1`,
`d/dn [−log(1 − e^n)] = N/(1 − N)`. -/
theorem hasDerivAt_neg_log_one_sub_exp {n : ℝ} (hn : Real.exp n < 1) :
    HasDerivAt (fun x => -Real.log (1 - Real.exp x)) (Real.exp n / (1 - Real.exp n)) n := by
  have h := (((Real.hasDerivAt_exp n).const_sub 1).log (sub_pos.2 hn).ne').neg
  refine h.congr_deriv ?_
  ring

/-- Galí (2015), Exercise 2.1 (**first-order log-linear labour supply**): along
`c = c̄ + s ĉ`, `n = n̄ + s n̂` the map `s ↦ c + log ν − log(1 − e^n)` (the real wage
`w − p` demanded) has derivative `ĉ + (N/(1 − N)) n̂` at `s = 0`, `N = e^{n̄}`. -/
theorem hasDerivAt_labourSupply_family (ν cbar nbar ch nh : ℝ) (hn : Real.exp nbar < 1) :
    HasDerivAt (fun s => (cbar + s * ch) + Real.log ν - Real.log (1 - Real.exp (nbar + s * nh)))
      (ch + Real.exp nbar / (1 - Real.exp nbar) * nh) 0 := by
  have hin : HasDerivAt (fun s : ℝ => nbar + s * nh) nh 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const nh).const_add nbar
  have ho : HasDerivAt (fun x => -Real.log (1 - Real.exp x))
      (Real.exp nbar / (1 - Real.exp nbar)) (nbar + 0 * nh) := by
    rw [zero_mul, add_zero]
    exact hasDerivAt_neg_log_one_sub_exp hn
  have hc : HasDerivAt (fun s : ℝ => cbar + s * ch + Real.log ν) ch 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const ch).const_add cbar).add_const (Real.log ν)
  have := hc.add (ho.comp 0 hin)
  refine this.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · ring
  · exact Eventually.of_forall fun s => by simp [Function.comp_def, sub_eq_add_neg]

/-! ### Differentiating under the abstract expectation -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 19 and App. 2.1, p. 44 (differentiating expected utility): if
`F(δ) − F(0) − δ L = o(δ)` uniformly in the state, then `δ ↦ E_t F(δ)` has derivative
`E_t L` at `0`. Only linearity, monotonicity and constants of `E_t` are used. -/
theorem hasDerivAt_E_of_uniform {F : ℝ → Ω → ℝ} {L : Ω → ℝ}
    (hF : ∀ ε > 0, ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ ω, |F δ ω - F 0 ω - δ * L ω| ≤ ε * |δ|)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun δ => 𝔼.E t (F δ) ω) (𝔼.E t L ω) 0 := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [hF ε hε] with δ hδ
  have e : 𝔼.E t (F δ) ω - 𝔼.E t (F 0) ω - (δ - 0) • 𝔼.E t L ω
      = 𝔼.E t (F δ - F 0 - δ • L) ω := by
    simp [map_sub, map_smul]
  rw [e, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero]
  exact 𝔼.abs_E_le (fun ω' => by simpa using hδ ω') t ω

/-- Galí (2015), p. 19 (one-period bond perturbation, concave utility): if the date-`t+1`
utilities `u ω` are differentiable on `(0, ∞)` with nonincreasing marginal utility `D ω`,
`c, p > 0` with a uniform lower bound `m ≤ p c`, and marginal utility has a uniform modulus of
continuity, then `δ ↦ u(c + δ/p)` is differentiable at `0` uniformly in the state, with
derivative `D(c)/p`. -/
theorem uniform_of_concave {u D : Ω → ℝ → ℝ} {c p : Ω → ℝ} {m : ℝ} (hm : 0 < m)
    (hp : ∀ ω, 0 < p ω) (hmpc : ∀ ω, m ≤ p ω * c ω)
    (hd : ∀ ω x, 0 < x → HasDerivAt (u ω) (D ω x) x)
    (hanti : ∀ ω, AntitoneOn (D ω) (Set.Ioi 0))
    (huc : ∀ ε > 0, ∀ᶠ h in 𝓝 (0 : ℝ), ∀ ω, |D ω (c ω + h / p ω) - D ω (c ω)| / p ω ≤ ε) :
    ∀ ε > 0, ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ ω,
      |u ω (c ω + δ / p ω) - u ω (c ω + 0 / p ω) - δ * (D ω (c ω) / p ω)| ≤ ε * |δ| := by
  intro ε hε
  have hball : ∀ᶠ δ in 𝓝 (0 : ℝ), |δ| < m := by
    simpa using eventually_abs_sub_lt (0 : ℝ) hm
  filter_upwards [huc ε hε, hball] with δ hδ hδm ω
  have hpω := hp ω
  have hc : 0 < c ω := by
    have := hmpc ω
    by_contra h
    push Not at h
    nlinarith
  have hy : 0 < c ω + δ / p ω := by
    have h1 : |δ / p ω| < c ω := by
      rw [abs_div, abs_of_pos hpω, div_lt_iff₀ hpω]
      nlinarith [hmpc ω]
    have := neg_abs_le (δ / p ω)
    linarith
  rw [zero_div, add_zero]
  have t1 := tangent_of_deriv hc hy (hd ω) (hanti ω)
  have t2 := tangent_of_deriv hy hc (hd ω) (hanti ω)
  have e1 : D ω (c ω) * (c ω + δ / p ω - c ω) = δ * (D ω (c ω) / p ω) := by
    field_simp
    ring
  have e2 : D ω (c ω + δ / p ω) * (c ω - (c ω + δ / p ω))
      = -(δ * (D ω (c ω + δ / p ω) / p ω)) := by
    field_simp
    ring
  rw [e1] at t1
  rw [e2] at t2
  have hdiff : |δ * (D ω (c ω + δ / p ω) / p ω) - δ * (D ω (c ω) / p ω)| ≤ ε * |δ| := by
    rw [← mul_sub, ← sub_div, abs_mul, abs_div, abs_of_pos hpω, mul_comm]
    exact mul_le_mul_of_nonneg_right (hδ ω) (abs_nonneg δ)
  rw [abs_le] at hdiff ⊢
  constructor <;> linarith [hdiff.1, hdiff.2]

/-- Galí (2015), p. 19: with finitely many states the uniform modulus of continuity of marginal
utility required by `uniform_of_concave` holds automatically. -/
theorem uniformCont_of_finite [Finite Ω] {D : Ω → ℝ → ℝ} {c p : Ω → ℝ}
    (hcont : ∀ ω, ContinuousAt (D ω) (c ω)) :
    ∀ ε > 0, ∀ᶠ h in 𝓝 (0 : ℝ), ∀ ω, |D ω (c ω + h / p ω) - D ω (c ω)| / p ω ≤ ε := by
  intro ε hε
  rw [Filter.eventually_all]
  intro ω
  have hin : Tendsto (fun h : ℝ => c ω + h / p ω) (𝓝 0) (𝓝 (c ω)) := by
    have : Continuous (fun h : ℝ => c ω + h / p ω) := by fun_prop
    simpa using this.tendsto 0
  have hlim : Tendsto (fun h : ℝ => |D ω (c ω + h / p ω) - D ω (c ω)| / p ω) (𝓝 0)
      (𝓝 (|D ω (c ω) - D ω (c ω)| / p ω)) :=
    (((hcont ω).tendsto.comp hin).sub_const _).abs.div_const _
  rw [sub_self, abs_zero, zero_div] at hlim
  exact hlim.eventually (Iic_mem_nhds hε)

/-- Galí (2015), eq. (5), p. 19 (**necessity**, generic form): if the date-`t` value
`f(δ) + β E_t G(δ)` of a perturbation `δ` has a local maximum at `δ = 0`, where `f` has
derivative `f'` and `G(δ) − G(0) − δ L = o(δ)` uniformly in the state, then
`f' + β E_t L = 0`. -/
theorem euler_necessary_generic {f : ℝ → ℝ} {f' β : ℝ} {G : ℝ → Ω → ℝ} {L : Ω → ℝ}
    (hf : HasDerivAt f f' 0)
    (hG : ∀ ε > 0, ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ ω, |G δ ω - G 0 ω - δ * L ω| ≤ ε * |δ|)
    (t : ℕ) (ω : Ω) (hloc : IsLocalMax (fun δ => f δ + β * 𝔼.E t (G δ) ω) 0) :
    f' + β * 𝔼.E t L ω = 0 :=
  hloc.hasDerivAt_eq_zero (hf.add ((hasDerivAt_E_of_uniform 𝔼 hG t ω).const_mul β))

/-- Galí (2015), eq. (5), p. 19 (**sufficiency**, generic form): if the date-`t` term lies
below its tangent `f(δ) ≤ f(0) + δ a`, each date-`t+1` term lies below its tangent
`G(δ) ≤ G(0) + δ L`, `β ≥ 0`, and the first-order condition `a + β E_t L = 0` holds, then the
perturbation `δ` does not raise the date-`t` value. -/
theorem euler_sufficient_generic {f : ℝ → ℝ} {a β δ : ℝ} {G : ℝ → Ω → ℝ} {L : Ω → ℝ}
    (hβ : 0 ≤ β) (hf : f δ ≤ f 0 + δ * a) (hG : ∀ ω', G δ ω' ≤ G 0 ω' + δ * L ω')
    (t : ℕ) (ω : Ω) (hfoc : a + β * 𝔼.E t L ω = 0) :
    f δ + β * 𝔼.E t (G δ) ω ≤ f 0 + β * 𝔼.E t (G 0) ω := by
  have hle : G δ ≤ G 0 + δ • L := fun ω' => by simpa using hG ω'
  have hE := 𝔼.mono t hle ω
  rw [map_add, map_smul] at hE
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hE
  have := mul_le_mul_of_nonneg_left hE hβ
  have e : δ * a + β * (δ * 𝔼.E t L ω) = δ * (a + β * 𝔼.E t L ω) := by ring
  rw [hfoc, mul_zero] at e
  nlinarith

/-! ### The Euler equation for Exercise 2.1 -/

/-- Galí (2015), eq. (5), p. 19, for Exercise 2.1, node by node:
`Q_t U_{C,t}/P_t = β E_t[U_{C,t+1}/P_{t+1}]`, i.e.
`Q_t = β E_t[(U_{C,t+1}/U_{C,t})(P_t/P_{t+1})]`. -/
def EulerEq (β σ ν : ℝ) (Q C N P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Q t ω * margUtilC σ ν (C t ω) (N t ω) / P t ω =
    β * 𝔼.E t (fun ω' => margUtilC σ ν (C (t + 1) ω') (N (t + 1) ω') / P (t + 1) ω') ω

/-- Galí (2015), p. 19, for Exercise 2.1: expected utility as of node `ω` at date `t` of the
perturbation that buys `δ` more bonds at `t` (consumption falls by `Q_t δ/P_t`) and consumes
the payoff at `t + 1` (consumption rises by `δ/P_{t+1}`), hours unchanged. -/
noncomputable def perturbedValue (β σ ν : ℝ) (Q C N P : ℕ → Ω → ℝ) (t : ℕ) (δ : ℝ) :
    Ω → ℝ :=
  fun ω => periodUtility σ ν (C t ω - Q t ω * δ / P t ω) (N t ω)
    + β * 𝔼.E t (fun ω' => periodUtility σ ν (C (t + 1) ω' + δ / P (t + 1) ω') (N (t + 1) ω')) ω

/-- Galí (2015), Exercise 2.1: `U_C` is nonincreasing in `C` for `σ > 0`. -/
theorem margUtilC_antitoneOn {σ : ℝ} (hσ : 0 < σ) (ν : ℝ) {N : ℝ} (hN : N < 1) :
    AntitoneOn (fun C => margUtilC σ ν C N) (Set.Ioi 0) := by
  intro a ha b _ hab
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos (by linarith) ν
  have ha' : (0 : ℝ) < a * (1 - N) ^ ν := mul_pos ha hL
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ha'
    (mul_le_mul_of_nonneg_right hab hL.le) (by linarith)) hL.le

/-- Galí (2015), Exercise 2.1: `U_C` is continuous in `C` at `C > 0`. -/
theorem margUtilC_continuousAt (σ ν : ℝ) {C N : ℝ} (hC : 0 < C) (hN : N < 1) :
    ContinuousAt (fun C' => margUtilC σ ν C' N) C := by
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos (by linarith) ν
  exact ((continuousAt_id.mul continuousAt_const).rpow_const
    (Or.inl (mul_pos hC hL).ne')).mul continuousAt_const

/-- Galí (2015), eq. (5), p. 19, for Exercise 2.1 (**necessity of the Euler equation**): if at
every date-`t` node no small bond perturbation is profitable, the Euler equation holds.
Hypotheses: `σ > 0`, positive prices and consumption, `N < 1`, a uniform lower bound
`m ≤ P_{t+1} C_{t+1}`, and a uniform modulus of continuity of next period's marginal utility
(automatic with finitely many states, `euler_necessary_finite`). -/
theorem euler_necessary {β σ ν : ℝ} {Q C N P : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ)
    (hC : ∀ ω, 0 < C t ω) (hN : ∀ ω, N t ω < 1) (hP : ∀ ω, 0 < P t ω)
    (hN1 : ∀ ω, N (t + 1) ω < 1) (hP1 : ∀ ω, 0 < P (t + 1) ω)
    {m : ℝ} (hm : 0 < m) (hmPC : ∀ ω, m ≤ P (t + 1) ω * C (t + 1) ω)
    (huc : ∀ ε > 0, ∀ᶠ h in 𝓝 (0 : ℝ), ∀ ω,
      |margUtilC σ ν (C (t + 1) ω + h / P (t + 1) ω) (N (t + 1) ω)
        - margUtilC σ ν (C (t + 1) ω) (N (t + 1) ω)| / P (t + 1) ω ≤ ε)
    (hopt : ∀ ω, IsLocalMax (fun δ => perturbedValue 𝔼 β σ ν Q C N P t δ ω) 0) :
    EulerEq 𝔼 β σ ν Q C N P t := by
  intro ω
  have hG := uniform_of_concave (u := fun ω' c => periodUtility σ ν c (N (t + 1) ω'))
    (D := fun ω' c => margUtilC σ ν c (N (t + 1) ω')) hm hP1 hmPC
    (fun ω' x hx => hasDerivAt_periodUtility_C σ ν hx (hN1 ω'))
    (fun ω' => margUtilC_antitoneOn hσ ν (hN1 ω')) huc
  have hin : HasDerivAt (fun δ : ℝ => C t ω - Q t ω * δ / P t ω) (-(Q t ω / P t ω)) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (Q t ω)).div_const (P t ω)).const_sub (C t ω)
    simpa [mul_div_assoc] using this
  have hu : HasDerivAt (fun c => periodUtility σ ν c (N t ω)) (margUtilC σ ν (C t ω) (N t ω))
      (C t ω - Q t ω * 0 / P t ω) := by
    simpa using hasDerivAt_periodUtility_C σ ν (hC ω) (hN ω)
  have h := euler_necessary_generic 𝔼 (hu.comp 0 hin) hG t ω (hopt ω)
  have hP0 := (hP ω).ne'
  have e : Q t ω * margUtilC σ ν (C t ω) (N t ω) / P t ω
      = -(margUtilC σ ν (C t ω) (N t ω) * -(Q t ω / P t ω)) := by
    field_simp
  rw [e]
  linarith

/-- Galí (2015), eq. (5), p. 19, for Exercise 2.1 (**necessity**, finitely many states): no
profitable small bond perturbation at any date-`t` node implies the Euler equation. -/
theorem euler_necessary_finite [Finite Ω] {β σ ν : ℝ} {Q C N P : ℕ → Ω → ℝ} {t : ℕ}
    (hσ : 0 < σ) (hC : ∀ ω, 0 < C t ω) (hN : ∀ ω, N t ω < 1) (hP : ∀ ω, 0 < P t ω)
    (hC1 : ∀ ω, 0 < C (t + 1) ω) (hN1 : ∀ ω, N (t + 1) ω < 1) (hP1 : ∀ ω, 0 < P (t + 1) ω)
    (hopt : ∀ ω, IsLocalMax (fun δ => perturbedValue 𝔼 β σ ν Q C N P t δ ω) 0) :
    EulerEq 𝔼 β σ ν Q C N P t := by
  obtain ⟨m, hm, hmPC⟩ : ∃ m, 0 < m ∧ ∀ ω, m ≤ P (t + 1) ω * C (t + 1) ω := by
    rcases isEmpty_or_nonempty Ω with hΩ | hΩ
    · exact ⟨1, one_pos, fun ω => (IsEmpty.false ω).elim⟩
    · obtain ⟨ω₀, h₀⟩ := Finite.exists_min fun ω => P (t + 1) ω * C (t + 1) ω
      exact ⟨_, mul_pos (hP1 ω₀) (hC1 ω₀), h₀⟩
  exact euler_necessary 𝔼 hσ hC hN hP hN1 hP1 hm hmPC
    (uniformCont_of_finite (D := fun ω' c => margUtilC σ ν c (N (t + 1) ω'))
      (fun ω' => margUtilC_continuousAt σ ν (hC1 ω') (hN1 ω'))) hopt

/-- Galí (2015), eq. (5), p. 19, for Exercise 2.1 (**sufficiency**, by concavity in
consumption): if the Euler equation holds at date `t` and `β ≥ 0`, no feasible bond
perturbation `δ` (one keeping consumption positive) raises expected utility at any node. -/
theorem euler_sufficient {β σ ν : ℝ} {Q C N P : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ) (hβ : 0 ≤ β)
    (hC : ∀ ω, 0 < C t ω) (hN : ∀ ω, N t ω < 1) (hP : ∀ ω, 0 < P t ω)
    (hC1 : ∀ ω, 0 < C (t + 1) ω) (hN1 : ∀ ω, N (t + 1) ω < 1)
    (heul : EulerEq 𝔼 β σ ν Q C N P t) {δ : ℝ} (ω : Ω)
    (hfeas : 0 < C t ω - Q t ω * δ / P t ω)
    (hfeas1 : ∀ ω', 0 < C (t + 1) ω' + δ / P (t + 1) ω') :
    perturbedValue 𝔼 β σ ν Q C N P t δ ω ≤ perturbedValue 𝔼 β σ ν Q C N P t 0 ω := by
  have hP0 := (hP ω).ne'
  have hf := tangent_of_deriv (hC ω) hfeas
    (fun x hx => hasDerivAt_periodUtility_C σ ν hx (hN ω)) (margUtilC_antitoneOn hσ ν (hN ω))
  have hG : ∀ ω', periodUtility σ ν (C (t + 1) ω' + δ / P (t + 1) ω') (N (t + 1) ω')
      ≤ periodUtility σ ν (C (t + 1) ω' + 0 / P (t + 1) ω') (N (t + 1) ω')
        + δ * (margUtilC σ ν (C (t + 1) ω') (N (t + 1) ω') / P (t + 1) ω') := by
    intro ω'
    have := tangent_of_deriv (hC1 ω') (hfeas1 ω')
      (fun x hx => hasDerivAt_periodUtility_C σ ν hx (hN1 ω'))
      (margUtilC_antitoneOn hσ ν (hN1 ω'))
    rw [zero_div, add_zero]
    have e : margUtilC σ ν (C (t + 1) ω') (N (t + 1) ω')
        * (C (t + 1) ω' + δ / P (t + 1) ω' - C (t + 1) ω')
        = δ * (margUtilC σ ν (C (t + 1) ω') (N (t + 1) ω') / P (t + 1) ω') := by ring
    linarith
  have hfoc : -(margUtilC σ ν (C t ω) (N t ω) * Q t ω / P t ω)
      + β * 𝔼.E t (fun ω' => margUtilC σ ν (C (t + 1) ω') (N (t + 1) ω') / P (t + 1) ω') ω
      = 0 := by
    have := heul ω
    rw [← this]
    ring
  have h := euler_sufficient_generic 𝔼
    (f := fun δ => periodUtility σ ν (C t ω - Q t ω * δ / P t ω) (N t ω))
    (G := fun δ ω' => periodUtility σ ν (C (t + 1) ω' + δ / P (t + 1) ω') (N (t + 1) ω'))
    (a := -(margUtilC σ ν (C t ω) (N t ω) * Q t ω / P t ω)) hβ ?_ hG t ω hfoc
  · exact h
  · simp only [mul_zero, zero_div, sub_zero]
    have e : margUtilC σ ν (C t ω) (N t ω) * (C t ω - Q t ω * δ / P t ω - C t ω)
        = δ * -(margUtilC σ ν (C t ω) (N t ω) * Q t ω / P t ω) := by ring
    linarith

/-! ### Log forms of the Euler equation -/

/-- Galí (2015), Exercise 2.1 and App. 2.1, p. 44: the Euler moment at node `ω` in logs,
`E_t[exp(i_t − ρ − σ(c_{t+1} − c_t) − (p_{t+1} − p_t) + ν(1−σ)(ℓ_{t+1} − ℓ_t))]` with
`ℓ = log(1 − N)`; date-`t` values enter as numbers. -/
noncomputable def eulerMoment (σ ν ρ : ℝ) (i c p ℓ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  𝔼.E t (fun ω' => Real.exp (i t ω - ρ - σ * (c (t + 1) ω' - c t ω)
    - (p (t + 1) ω' - p t ω) + ν * (1 - σ) * (ℓ (t + 1) ω' - ℓ t ω))) ω

/-- Galí (2015), Exercise 2.1: in logs, `U_C(e^c, 1 − e^ℓ) = exp(−σ c + ν(1 − σ) ℓ)`. -/
theorem margUtilC_exp (σ ν c ℓ : ℝ) :
    margUtilC σ ν (Real.exp c) (1 - Real.exp ℓ) = Real.exp (-σ * c + ν * (1 - σ) * ℓ) := by
  unfold margUtilC
  rw [sub_sub_cancel, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- Galí (2015), Exercise 2.1 (**exact**): with `Q = e^{−i}`, `β = e^{−ρ}`, `C = e^c`,
`P = e^p`, `1 − N = e^ℓ`, the Euler equation at date `t` holds iff the Euler moment equals one
at every node. -/
theorem eulerEq_iff_moment (σ ν ρ : ℝ) (i c p ℓ : ℕ → Ω → ℝ) (t : ℕ) :
    EulerEq 𝔼 (Real.exp (-ρ)) σ ν (fun t ω => Real.exp (-i t ω)) (fun t ω => Real.exp (c t ω))
        (fun t ω => 1 - Real.exp (ℓ t ω)) (fun t ω => Real.exp (p t ω)) t ↔
      ∀ ω, eulerMoment 𝔼 σ ν ρ i c p ℓ t ω = 1 := by
  set G : Ω → ℝ := fun ω' =>
    Real.exp (-σ * c (t + 1) ω' + ν * (1 - σ) * ℓ (t + 1) ω' - p (t + 1) ω') with hGdef
  have hmom : ∀ ω, eulerMoment 𝔼 σ ν ρ i c p ℓ t ω
      = Real.exp (i t ω - ρ + σ * c t ω + p t ω - ν * (1 - σ) * ℓ t ω) * 𝔼.E t G ω := by
    intro ω
    have hfun : (fun ω' => Real.exp (i t ω - ρ - σ * (c (t + 1) ω' - c t ω)
        - (p (t + 1) ω' - p t ω) + ν * (1 - σ) * (ℓ (t + 1) ω' - ℓ t ω)))
        = Real.exp (i t ω - ρ + σ * c t ω + p t ω - ν * (1 - σ) * ℓ t ω) • G := by
      funext ω'
      simp only [Pi.smul_apply, smul_eq_mul, hGdef]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [eulerMoment, hfun, map_smul, Pi.smul_apply, smul_eq_mul]
  have hG : (fun ω' => margUtilC σ ν (Real.exp (c (t + 1) ω')) (1 - Real.exp (ℓ (t + 1) ω'))
      / Real.exp (p (t + 1) ω')) = G := by
    funext ω'
    rw [margUtilC_exp, hGdef, ← Real.exp_sub]
  unfold EulerEq
  refine forall_congr' fun ω => ?_
  rw [hmom ω, hG, margUtilC_exp, ← Real.exp_add, ← Real.exp_sub]
  set A := -i t ω + (-σ * c t ω + ν * (1 - σ) * ℓ t ω) - p t ω with hA
  have e : Real.exp (i t ω - ρ + σ * c t ω + p t ω - ν * (1 - σ) * ℓ t ω)
      = Real.exp (-ρ) * (Real.exp A)⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add, hA]
    congr 1
    ring
  rw [e]
  have hpos := Real.exp_pos A
  constructor
  · intro h
    rw [mul_assoc, mul_comm ((Real.exp A)⁻¹), ← mul_assoc, ← h, mul_inv_cancel₀ hpos.ne']
  · intro h
    field_simp at h
    linarith

/-- Galí (2015), Exercise 2.1 (**exact, perfect foresight**): the Euler equation holds at
date `t` iff `i_t − (p_{t+1} − p_t) − ρ = σ(c_{t+1} − c_t) − ν(1 − σ)(ℓ_{t+1} − ℓ_t)`,
`ℓ = log(1 − N)`. -/
theorem pf_eulerEq_iff (σ ν ρ : ℝ) (i c p ℓ : ℕ → Unit → ℝ) (t : ℕ) :
    EulerEq perfectForesight (Real.exp (-ρ)) σ ν (fun t ω => Real.exp (-i t ω))
        (fun t ω => Real.exp (c t ω)) (fun t ω => 1 - Real.exp (ℓ t ω))
        (fun t ω => Real.exp (p t ω)) t ↔
      ∀ ω, i t ω - (p (t + 1) ω - p t ω) - ρ
        = σ * (c (t + 1) ω - c t ω) - ν * (1 - σ) * (ℓ (t + 1) ω - ℓ t ω) := by
  rw [eulerEq_iff_moment]
  refine forall_congr' fun ω => ?_
  simp only [eulerMoment, perfectForesight, LinearMap.id_apply]
  rw [← Real.exp_zero, Real.exp_eq_exp]
  constructor <;> intro h <;> linarith

/-! ### The first-order approximation under uncertainty -/

/-- Galí (2015), App. 2.1, p. 44 (uniform first-order expansion): if `ℓ` has derivative `ℓ'`
at `x`, then `ℓ(x + s b) − ℓ(x) − s b ℓ' = o(s)` uniformly over `|b| ≤ M`. -/
theorem uniform_comp_line {ℓ : ℝ → ℝ} {ℓ' x M : ℝ} (hℓ : HasDerivAt ℓ ℓ' x) (hM : 0 ≤ M) :
    ∀ ε > 0, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ b : ℝ, |b| ≤ M →
      |ℓ (x + s * b) - ℓ x - s * b * ℓ'| ≤ ε * |s| := by
  intro ε hε
  have hM1 : 0 < M + 1 := by linarith
  have h := (Asymptotics.isLittleO_iff.1 (hasDerivAt_iff_isLittleO.1 hℓ))
    (div_pos hε hM1)
  obtain ⟨η, hη, hη'⟩ := Metric.eventually_nhds_iff.1 h
  have hs : ∀ᶠ s in 𝓝 (0 : ℝ), |s| < η / (M + 1) := by
    simpa using eventually_abs_sub_lt (0 : ℝ) (div_pos hη hM1)
  filter_upwards [hs] with s hs b hb
  have hsb : |s * b| ≤ |s| * (M + 1) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s)
  have hd : dist (x + s * b) x < η := by
    rw [Real.dist_eq, add_sub_cancel_left]
    have := (lt_div_iff₀ hM1).1 hs
    linarith
  have h2 := hη' hd
  rw [add_sub_cancel_left, Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul] at h2
  calc |ℓ (x + s * b) - ℓ x - s * b * ℓ'| ≤ ε / (M + 1) * |s * b| := h2
    _ ≤ ε / (M + 1) * (|s| * (M + 1)) := by gcongr
    _ = ε * |s| := by field_simp

/-- Galí (2015), App. 2.1, p. 44 (uniform first-order expansion of `exp`): if
`g(s) − s L = o(s)` uniformly, `g(0) = 0` and `L` is bounded, then
`exp(g(s)) − exp(g(0)) − s L = o(s)` uniformly. -/
theorem uniform_exp {g : ℝ → Ω → ℝ} {L : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K) (hL : ∀ ω, |L ω| ≤ K)
    (hg0 : ∀ ω, g 0 ω = 0)
    (hg : ∀ ε > 0, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ ω, |g s ω - s * L ω| ≤ ε * |s|) :
    ∀ ε > 0, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ ω,
      |Real.exp (g s ω) - Real.exp (g 0 ω) - s * L ω| ≤ ε * |s| := by
  intro ε hε
  have hK1 : 0 < K + 1 := by linarith
  set r := min (1 / (K + 1)) (ε / (2 * (K + 1) ^ 2)) with hr
  have hr0 : 0 < r := lt_min (by positivity) (by positivity)
  have hε1 : 0 < min (ε / 2) 1 := lt_min (by linarith) one_pos
  have hs : ∀ᶠ s in 𝓝 (0 : ℝ), |s| < r := by
    simpa using eventually_abs_sub_lt (0 : ℝ) hr0
  filter_upwards [hg _ hε1, hs] with s h1 h2 ω
  have h1 := h1 ω
  rw [hg0 ω, Real.exp_zero]
  have hm1 : min (ε / 2) 1 ≤ 1 := min_le_right _ _
  have hm2 : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
  have hsL : |s * L ω| ≤ K * |s| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hL ω) (abs_nonneg s)
  have hs0 := abs_nonneg s
  have hgb : |g s ω| ≤ (K + 1) * |s| := by
    have := abs_sub_abs_le_abs_sub (g s ω) (s * L ω)
    nlinarith
  have hsr1 : |s| ≤ 1 / (K + 1) := h2.le.trans (min_le_left _ _)
  have hsr2 : |s| ≤ ε / (2 * (K + 1) ^ 2) := h2.le.trans (min_le_right _ _)
  have hg1 : |g s ω| ≤ 1 := by
    calc |g s ω| ≤ (K + 1) * |s| := hgb
      _ ≤ (K + 1) * (1 / (K + 1)) := by gcongr
      _ = 1 := by field_simp
  have hexp := Real.abs_exp_sub_one_sub_id_le hg1
  have hsq : g s ω ^ 2 ≤ ε / 2 * |s| := by
    calc g s ω ^ 2 = |g s ω| ^ 2 := (sq_abs _).symm
      _ ≤ ((K + 1) * |s|) ^ 2 := by gcongr
      _ = (K + 1) ^ 2 * |s| * |s| := by ring
      _ ≤ (K + 1) ^ 2 * (ε / (2 * (K + 1) ^ 2)) * |s| := by gcongr
      _ = ε / 2 * |s| := by field_simp
  have htri : |Real.exp (g s ω) - 1 - s * L ω|
      ≤ |Real.exp (g s ω) - 1 - g s ω| + |g s ω - s * L ω| := by
    have := abs_add_le (Real.exp (g s ω) - 1 - g s ω) (g s ω - s * L ω)
    rwa [show Real.exp (g s ω) - 1 - g s ω + (g s ω - s * L ω)
      = Real.exp (g s ω) - 1 - s * L ω by ring] at this
  nlinarith

/-- Galí (2015), Exercise 2.1 and App. 2.1, p. 44: the linearised Euler expression at node
`ω`, `î_t − σ(ĉ_{t+1} − ĉ_t) − (p̂_{t+1} − p̂_t) − ν(1 − σ)(N/(1 − N))(n̂_{t+1} − n̂_t)` as a
date-`t+1` random variable (date-`t` values enter as numbers). -/
noncomputable def linearisedEuler (σ ν Nbar : ℝ) (ih ch ph nh : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Ω → ℝ :=
  fun ω' => ih t ω - σ * (ch (t + 1) ω' - ch t ω) - (ph (t + 1) ω' - ph t ω)
    - ν * (1 - σ) * (Nbar / (1 - Nbar)) * (nh (t + 1) ω' - nh t ω)

/-- Galí (2015), Exercise 2.1: at `s = 0` the family of paths `i = ρ`, `c = c̄`, `p = p̄`,
`n = n̄` is a steady state: the Euler moment equals one. -/
theorem eulerMoment_family_zero (σ ν ρ cbar pbar nbar : ℝ) (ih ch ph nh : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    eulerMoment 𝔼 σ ν ρ (fun t ω => ρ + 0 * ih t ω) (fun t ω => cbar + 0 * ch t ω)
      (fun t ω => pbar + 0 * ph t ω)
      (fun t ω => Real.log (1 - Real.exp (nbar + 0 * nh t ω))) t ω = 1 := by
  simp [eulerMoment, 𝔼.const]

/-- Galí (2015), Exercise 2.1 and App. 2.1, p. 44 (**first-order log-linearisation of the
Euler equation under uncertainty**): along `i = ρ + s î`, `c = c̄ + s ĉ`, `p = p̄ + s p̂`,
`n = n̄ + s n̂` (bounded deviations, `N = e^{n̄} < 1`, `ℓ = log(1 − e^n)`), the Euler moment
has derivative `E_t[linearisedEuler]` at `s = 0`. -/
theorem hasDerivAt_moment_family (σ ν ρ cbar pbar nbar : ℝ) (hn : Real.exp nbar < 1)
    {ih ch ph nh : ℕ → Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t ω, |ih t ω| ≤ M ∧ |ch t ω| ≤ M ∧ |ph t ω| ≤ M ∧ |nh t ω| ≤ M)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => eulerMoment 𝔼 σ ν ρ (fun t ω => ρ + s * ih t ω)
        (fun t ω => cbar + s * ch t ω) (fun t ω => pbar + s * ph t ω)
        (fun t ω => Real.log (1 - Real.exp (nbar + s * nh t ω))) t ω)
      (𝔼.E t (linearisedEuler σ ν (Real.exp nbar) ih ch ph nh t ω) ω) 0 := by
  set ℓf : ℝ → ℝ := fun x => Real.log (1 - Real.exp x) with hℓf
  set ℓ' := -(Real.exp nbar / (1 - Real.exp nbar)) with hℓ'
  have hℓ : HasDerivAt ℓf ℓ' nbar := by
    have h := ((Real.hasDerivAt_exp nbar).const_sub 1).log (sub_pos.2 hn).ne'
    exact h.congr_deriv (by rw [hℓ']; ring)
  set κ := ν * (1 - σ) with hκ
  set d := nh t ω with hd
  set a : Ω → ℝ := fun ω' =>
    ih t ω - σ * (ch (t + 1) ω' - ch t ω) - (ph (t + 1) ω' - ph t ω) with ha
  set g : ℝ → Ω → ℝ := fun s ω' =>
    s * a ω' + κ * (ℓf (nbar + s * nh (t + 1) ω') - ℓf (nbar + s * d)) with hg
  set L := linearisedEuler σ ν (Real.exp nbar) ih ch ph nh t ω with hLdef
  have hL : ∀ ω', L ω' = a ω' + κ * ℓ' * (nh (t + 1) ω' - d) := fun ω' => by
    simp only [hLdef, linearisedEuler, ha, hℓ', hκ, hd]
    ring
  have hfun : ∀ s, eulerMoment 𝔼 σ ν ρ (fun t ω => ρ + s * ih t ω)
      (fun t ω => cbar + s * ch t ω) (fun t ω => pbar + s * ph t ω)
      (fun t ω => Real.log (1 - Real.exp (nbar + s * nh t ω))) t ω
      = 𝔼.E t (fun ω' => Real.exp (g s ω')) ω := by
    intro s
    unfold eulerMoment
    refine congrArg (fun F => 𝔼.E t F ω) (funext fun ω' => ?_)
    congr 1
    simp only [hg, ha, hκ, hℓf, hd]
    ring
  have hg0 : ∀ ω', g 0 ω' = 0 := by
    intro ω'
    simp [hg]
  have hgu : ∀ ε > 0, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ ω', |g s ω' - s * L ω'| ≤ ε * |s| := by
    intro ε hε
    have hκ1 : 0 < 2 * |κ| + 1 := by positivity
    filter_upwards [uniform_comp_line hℓ hM (ε / (2 * |κ| + 1)) (div_pos hε hκ1)]
      with s hs ω'
    have h1 := hs (nh (t + 1) ω') (hb (t + 1) ω').2.2.2
    have h2 := hs d (hb t ω).2.2.2
    have e : g s ω' - s * L ω' = κ * ((ℓf (nbar + s * nh (t + 1) ω') - ℓf nbar
        - s * nh (t + 1) ω' * ℓ') - (ℓf (nbar + s * d) - ℓf nbar - s * d * ℓ')) := by
      rw [hL]
      simp only [hg]
      ring
    have hfrac : 2 * |κ| / (2 * |κ| + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) hκ1.le
    rw [e, abs_mul]
    calc |κ| * |ℓf (nbar + s * nh (t + 1) ω') - ℓf nbar - s * nh (t + 1) ω' * ℓ'
          - (ℓf (nbar + s * d) - ℓf nbar - s * d * ℓ')|
        ≤ |κ| * (ε / (2 * |κ| + 1) * |s| + ε / (2 * |κ| + 1) * |s|) := by
          gcongr
          exact (abs_sub _ _).trans (add_le_add h1 h2)
      _ = 2 * |κ| / (2 * |κ| + 1) * (ε * |s|) := by
          field_simp
          ring
      _ ≤ 1 * (ε * |s|) := mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = ε * |s| := one_mul _
  set K := M + |σ| * (2 * M) + 2 * M + |κ * ℓ'| * (2 * M) with hK
  have hLb : ∀ ω', |L ω'| ≤ K := by
    intro ω'
    obtain ⟨hi, hc0, hp0, hn0⟩ := hb t ω
    obtain ⟨-, hc1, hp1, hn1⟩ := hb (t + 1) ω'
    have hc : |ch (t + 1) ω' - ch t ω| ≤ 2 * M := (abs_sub _ _).trans (by linarith)
    have hp : |ph (t + 1) ω' - ph t ω| ≤ 2 * M := (abs_sub _ _).trans (by linarith)
    have hnn : |nh (t + 1) ω' - d| ≤ 2 * M := (abs_sub _ _).trans (by rw [hd]; linarith)
    have h3 : |σ * (ch (t + 1) ω' - ch t ω)| ≤ |σ| * (2 * M) := by
      rw [abs_mul]; gcongr
    have h4 : |κ * ℓ' * (nh (t + 1) ω' - d)| ≤ |κ * ℓ'| * (2 * M) := by
      rw [abs_mul]; gcongr
    have ha' : |a ω'| ≤ M + |σ| * (2 * M) + 2 * M := by
      have e1 := abs_sub (ih t ω - σ * (ch (t + 1) ω' - ch t ω)) (ph (t + 1) ω' - ph t ω)
      have e2 := abs_sub (ih t ω) (σ * (ch (t + 1) ω' - ch t ω))
      simp only [ha]
      linarith
    rw [hL]
    have := abs_add_le (a ω') (κ * ℓ' * (nh (t + 1) ω' - d))
    linarith
  have hK0 : 0 ≤ K := by positivity
  have hexp := uniform_exp hK0 hLb hg0 hgu
  have hder := hasDerivAt_E_of_uniform 𝔼 (F := fun s ω' => Real.exp (g s ω')) hexp t ω
  exact hder.congr_of_eventuallyEq (Eventually.of_forall fun s => hfun s)

/-- Galí (2015), Exercise 2.1: the expectation of the linearised Euler expression,
`î_t − σ(E_t ĉ_{t+1} − ĉ_t) − (E_t p̂_{t+1} − p̂_t) − ν(1 − σ)(N/(1 − N))(E_t n̂_{t+1} − n̂_t)`,
by linearity of `E_t` only. -/
theorem E_linearisedEuler (σ ν Nbar : ℝ) (ih ch ph nh : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    𝔼.E t (linearisedEuler σ ν Nbar ih ch ph nh t ω) ω
      = ih t ω - σ * (𝔼.E t (ch (t + 1)) ω - ch t ω) - (𝔼.E t (ph (t + 1)) ω - ph t ω)
        - ν * (1 - σ) * (Nbar / (1 - Nbar)) * (𝔼.E t (nh (t + 1)) ω - nh t ω) := by
  set k := ν * (1 - σ) * (Nbar / (1 - Nbar)) with hk
  have hfun : linearisedEuler σ ν Nbar ih ch ph nh t ω
      = (fun _ => ih t ω + σ * ch t ω + ph t ω + k * nh t ω) + (-σ) • ch (t + 1)
        + (-1 : ℝ) • ph (t + 1) + (-k) • nh (t + 1) := by
    funext ω'
    simp only [linearisedEuler, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hk]
    ring
  rw [hfun]
  simp only [map_add, map_smul, 𝔼.const, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), Exercise 2.1 (**log-linear Euler equation**): for `σ ≠ 0` the derivative of
the Euler moment vanishes at node `ω` iff
`ĉ_t = E_t ĉ_{t+1} − σ^{−1}(î_t − E_t π̂_{t+1}) + σ^{−1} ν(1 − σ)(N/(1 − N))(E_t n̂_{t+1} − n̂_t)`,
`π̂_{t+1} = p̂_{t+1} − p̂_t`. -/
theorem linearisedEuler_zero_iff {σ : ℝ} (hσ : σ ≠ 0) (ν Nbar : ℝ) (ih ch ph nh : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    𝔼.E t (linearisedEuler σ ν Nbar ih ch ph nh t ω) ω = 0 ↔
      ch t ω = 𝔼.E t (ch (t + 1)) ω - σ⁻¹ * (ih t ω - (𝔼.E t (ph (t + 1)) ω - ph t ω))
        + σ⁻¹ * (ν * (1 - σ) * (Nbar / (1 - Nbar))) * (𝔼.E t (nh (t + 1)) ω - nh t ω) := by
  rw [E_linearisedEuler]
  set R := 𝔼.E t (ch (t + 1)) ω - σ⁻¹ * (ih t ω - (𝔼.E t (ph (t + 1)) ω - ph t ω))
    + σ⁻¹ * (ν * (1 - σ) * (Nbar / (1 - Nbar))) * (𝔼.E t (nh (t + 1)) ω - nh t ω) with hR
  have key : ih t ω - σ * (𝔼.E t (ch (t + 1)) ω - ch t ω) - (𝔼.E t (ph (t + 1)) ω - ph t ω)
      - ν * (1 - σ) * (Nbar / (1 - Nbar)) * (𝔼.E t (nh (t + 1)) ω - nh t ω)
      = -σ * (R - ch t ω) := by
    rw [hR]
    field_simp
    ring
  rw [key]
  constructor
  · intro h
    have := (mul_eq_zero.1 h).resolve_left (neg_ne_zero.2 hσ)
    linarith
  · intro h
    rw [← h, sub_self, mul_zero]

end Gali.ClassicalMonetaryModel.Ex2_1
