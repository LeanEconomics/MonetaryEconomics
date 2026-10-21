/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.DIS
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The household problem and the Euler equation

Galí (2015), Chapter 3, §3.1 (pp. 52–54), eqs. (2)–(3), reusing Chapter 2, §2.1
(pp. 18–22), eqs. (4)–(5) and (7)–(10); the goods-market link to eq. (13), p. 58; and the
production side of eq. (14), p. 59.

## The household

Period utility (p. 54) is `U(C, N; Z) = ((C^{1−σ} − 1)/(1 − σ) − N^{1+φ}/(1+φ)) Z` for
`σ ≠ 1` and `(log C − N^{1+φ}/(1+φ)) Z` for `σ = 1`, with `σ > 0`, `φ ≥ 0`, `Z > 0`
(`periodUtility`). Both optimality conditions are derived from Galí's variational argument
(pp. 19–20).

* **Static problem** (labour supply). Holding everything else fixed, a change of hours is
  financed one-for-one in consumption, `P dC = W dN`: the household chooses `N ≥ 0` on the
  budget line `P C = W N + X` (`X` collects the unchanged bond and dividend terms).
  `static_foc_necessary`: a local optimum with `C, N > 0` satisfies `W/P = N^φ C^σ` (ch. 2,
  eq. (7)); `static_foc_sufficient`: by concavity the condition implies a global optimum;
  `static_optimum_iff` combines them. `labour_supply_log_iff`: eq. (2), `w − p = σ c + φ n`,
  exactly in logs.
* **Intertemporal problem** (Euler equation). Buying `δ` more bonds at date `t` lowers
  consumption by `Q_t δ/P_t` and raises date-`t+1` consumption by `δ/P_{t+1}` in every state
  (`perturbedValue`). `euler_necessary`: if no small perturbation is profitable at any
  date-`t` node, then `Q_t = β (C_t^σ P_t/Z_t) E_t[C_{t+1}^{−σ} Z_{t+1}/P_{t+1}]` at every
  node (`EulerEq`), i.e. `Q_t = β E_t[(C_{t+1}/C_t)^{−σ}(Z_{t+1}/Z_t)(P_t/P_{t+1})]`
  (`eulerEq_ratio_form`). `euler_sufficient`: conversely no feasible perturbation is
  profitable when the Euler equation holds.

## Expectations

Everything is stated for an arbitrary `ExpectationSystem` (a linear, monotone,
constant-preserving `E_t` with the tower property), so the results hold under perfect
foresight and under uncertainty. The abstract `E_t` cannot be assumed to commute with
limits, so the Euler necessity proof never differentiates under `E_t`: it sandwiches the
date-`t+1` utility gain between tangent lines of the concave utility (only monotonicity and
linearity of `E_t` are used) under a uniform lower bound `m ≤ P_{t+1} C_{t+1}` on next
period's nominal expenditure; such a bound always exists when `Ω` is finite
(`exists_expenditure_lower_bound`, `euler_necessary_finite`). Date-`t` variables enter
`EulerEq` as numbers at the node `ω`, which is how a node-by-node optimality condition reads
and avoids any "taking out what is known" property that `ExpectationSystem` does not provide.

## Log-linear forms

* `eulerEq_iff_moment` (**exact**): with `Q = e^{−i}`, `β = e^{−ρ}`, `C = e^c`, `P = e^p`,
  `Z = e^z`, the Euler equation is `E_t[exp(i_t − ρ − σΔc_{t+1} − Δp_{t+1} + Δz_{t+1})] = 1`.
* `pf_eulerEq_iff` (**exact**, perfect foresight):
  `i_t − π_{t+1} − ρ = σ(c_{t+1} − c_t) − (z_{t+1} − z_t)`; `pf_eulerEq_iff_noshock`: with no
  preference shock, `i_t − π_{t+1} − ρ = σ(c_{t+1} − c_t)`.
* `hasDerivAt_log_E_exp`, `hasDerivAt_log_eulerMoment_family` (**first order**, uncertainty):
  along the family of paths `i = ρ + s î`, `c = c̄ + s ĉ`, `p = p̄ + s p̂`, `z = s ẑ` (bounded
  deviations, zero-inflation steady state at `s = 0`, `eulerMoment_family_zero`), the map
  `s ↦ log E_t[exp(i_t − ρ − σΔc − Δp + Δz)]` has derivative at `0` equal to
  `î_t − σ(E_t ĉ_{t+1} − ĉ_t) − E_t π̂_{t+1} + (E_t ẑ_{t+1} − ẑ_t)`
  (`linearisedEuler`, `linearisedEuler_eq`), and `linearisedEuler_eq_zero_iff`: for AR(1)
  `ẑ` this derivative vanishes at every date iff eq. (3) holds (`EulerLogLinear`).
* `pf_eulerEq_imp_eulerLogLinear`: under perfect foresight eq. (3) holds exactly.

## Goods market and production

* `eulerOutput_iff_of_clearing`: with `Y_t = C_t` (eq. (12)) eq. (3) is exactly
  `DIS.EulerOutput`, eq. (13); `pf_eulerEq_imp_eulerOutput` chains the nonlinear Euler
  equation under perfect foresight into (13).
* `employment_log_identity`: `Y(i) = A N(i)^{1−α}` on the demand schedule gives exactly
  `(1 − α) n = y − a + d`, `d = (1 − α) log ∫ (P(i)/P)^{−ε/(1−α)} di` (p. 59).
-/

namespace Gali.BasicNewKeynesianModel.Household

open Filter Topology MeasureTheory

/-! ### Period utility -/

/-- Galí (2015), p. 54 (and ch. 2, p. 20): utility of consumption, `(C^{1−σ} − 1)/(1 − σ)`
for `σ ≠ 1` and `log C` for `σ = 1`. -/
noncomputable def utilC (σ C : ℝ) : ℝ :=
  if σ = 1 then Real.log C else (C ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 54: disutility of labour `N^{1+φ}/(1+φ)`. -/
noncomputable def disutilN (φ N : ℝ) : ℝ := N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 54: period utility `U(C, N; Z) = (u(C) − N^{1+φ}/(1+φ)) Z`. -/
noncomputable def periodUtility (σ φ C N Z : ℝ) : ℝ := (utilC σ C - disutilN φ N) * Z

/-- Galí (2015), ch. 2, eq. (7), p. 21: marginal utility of consumption, `u'(C) = C^{−σ}`,
in both the `σ ≠ 1` and the log case. -/
theorem hasDerivAt_utilC (σ : ℝ) {C : ℝ} (hC : 0 < C) :
    HasDerivAt (utilC σ) (C ^ (-σ)) C := by
  by_cases hσ : σ = 1
  · have hfun : utilC σ = Real.log := funext fun x => by simp [utilC, hσ]
    rw [hfun, hσ, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hC.ne'
  · have hfun : utilC σ = fun x => (x ^ (1 - σ) - 1) / (1 - σ) :=
      funext fun x => by simp [utilC, hσ]
    have hs : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    rw [hfun]
    refine (((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hC.ne')).sub_const 1).div_const
      (1 - σ)).congr_deriv ?_
    rw [show (1 : ℝ) - σ - 1 = -σ by ring]
    field_simp

/-- Galí (2015), ch. 2, eq. (7), p. 21: marginal disutility of labour, `N^φ`. -/
theorem hasDerivAt_disutilN {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (disutilN φ) (N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), ch. 2, p. 18 (`U_cc ≤ 0`): marginal utility `C^{−σ}` is nonincreasing for
`σ > 0`. -/
theorem antitoneOn_margUtil {σ : ℝ} (hσ : 0 < σ) :
    AntitoneOn (fun C : ℝ => C ^ (-σ)) (Set.Ioi 0) :=
  fun _ ha _ _ hab => Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangent lines (used for Galí (2015), ch. 2, p. 18, concavity of utility). -/
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

/-- Galí (2015), ch. 2, p. 18: the utility of consumption is concave for `σ > 0`, in the
tangent-line form `u(y) ≤ u(x) + x^{−σ}(y − x)` for `x, y > 0`. -/
theorem utilC_le_tangent {σ : ℝ} (hσ : 0 < σ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    utilC σ y ≤ utilC σ x + x ^ (-σ) * (y - x) := by
  refine le_tangent (f' := fun C => C ^ (-σ)) hx hy.le ?_ (fun z hz => hasDerivAt_utilC σ hz)
    (antitoneOn_margUtil hσ)
  intro z hz
  have hz0 : 0 < z := by
    rcases Set.mem_uIcc.1 hz with h | h
    · exact lt_of_lt_of_le hx h.1
    · exact lt_of_lt_of_le hy h.1
  exact (hasDerivAt_utilC σ hz0).continuousAt.continuousWithinAt

/-- Galí (2015), ch. 2, p. 18: the disutility of labour is convex for `φ ≥ 0`, in the
tangent-line form `v(x) + x^φ (y − x) ≤ v(y)` for `x > 0`, `y ≥ 0`. -/
theorem disutilN_tangent_le {φ : ℝ} (hφ : 0 ≤ φ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    disutilN φ x + x ^ φ * (y - x) ≤ disutilN φ y := by
  have h := le_tangent (f := fun N => -disutilN φ N) (f' := fun N => -N ^ φ) hx hy
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
      (1 + φ)).neg.continuousOn) (fun z _ => (hasDerivAt_disutilN hφ z).neg)
    (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
  linarith

/-! ### The static (labour-supply) problem -/

/-- Galí (2015), ch. 2, eq. (4), p. 19, and eq. (7), p. 21 (**necessity**): if hours `N > 0`
are a local optimum along the budget line `P C = W N + X` (a perturbation `P dC = W dN`,
everything else unchanged) with `C > 0`, then `W/P = N^φ C^σ`. -/
theorem static_foc_necessary {σ φ P W X Z C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hZ : 0 < Z)
    (hC : 0 < C) (hbud : P * C = W * N + X)
    (hloc : IsLocalMax (fun N' => periodUtility σ φ ((W * N' + X) / P) N' Z) N) :
    W / P = N ^ φ * C ^ σ := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hin : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
    have := (((hasDerivAt_id N).const_mul W).add_const X).div_const P
    simpa using this
  have hu : HasDerivAt (utilC σ) (((W * N + X) / P) ^ (-σ)) ((W * N + X) / P) :=
    hasDerivAt_utilC σ (by rw [hCeq]; exact hC)
  have hg : HasDerivAt (fun N' => periodUtility σ φ ((W * N' + X) / P) N' Z)
      ((C ^ (-σ) * (W / P) - N ^ φ) * Z) N := by
    have := (HasDerivAt.sub (hu.comp N hin) (hasDerivAt_disutilN hφ N)).mul_const Z
    rw [hCeq] at this
    exact this
  have h0 := hloc.hasDerivAt_eq_zero hg
  have h1 : C ^ (-σ) * (W / P) = N ^ φ := by
    have := (mul_eq_zero.1 h0).resolve_right hZ.ne'
    linarith
  have hCs : C ^ σ * C ^ (-σ) = 1 := by
    rw [Real.rpow_neg hC.le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hC σ).ne'
  calc W / P = (C ^ σ * C ^ (-σ)) * (W / P) := by rw [hCs, one_mul]
    _ = N ^ φ * C ^ σ := by rw [mul_assoc, h1, mul_comm]

/-- Galí (2015), ch. 2, p. 19: a global optimum of the static problem over all feasible
plans (`N' ≥ 0`, `C' = (W N' + X)/P > 0`) with `N, C > 0` is a local optimum along the budget
line. -/
theorem static_isLocalMax_of_optimal {σ φ P W X Z C N : ℝ} (hP : 0 < P) (hN : 0 < N)
    (hC : 0 < C) (hbud : P * C = W * N + X)
    (hopt : ∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      periodUtility σ φ ((W * N' + X) / P) N' Z ≤ periodUtility σ φ C N Z) :
    IsLocalMax (fun N' => periodUtility σ φ ((W * N' + X) / P) N' Z) N := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hcont : Continuous fun N' : ℝ => (W * N' + X) / P := by fun_prop
  have h1 : ∀ᶠ N' in 𝓝 N, 0 < (W * N' + X) / P :=
    (hcont.tendsto N).eventually_const_lt (by rw [hCeq]; exact hC)
  filter_upwards [h1, eventually_gt_nhds hN] with N' h1' h2'
  rw [hCeq]
  exact hopt N' h2'.le h1'

/-- Galí (2015), ch. 2, eq. (7), p. 21 (**sufficiency**, by concavity): if `W/P = N^φ C^σ`
at a point `(C, N)` with `C, N > 0` on the budget line, then `(C, N)` maximises utility
among all feasible plans `N' ≥ 0`, `C' = (W N' + X)/P > 0`. -/
theorem static_foc_sufficient {σ φ P W X Z C N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hP : 0 < P)
    (hZ : 0 < Z) (hN : 0 < N) (hC : 0 < C) (hbud : P * C = W * N + X)
    (hfoc : W / P = N ^ φ * C ^ σ) {N' : ℝ} (hN' : 0 ≤ N') (hC' : 0 < (W * N' + X) / P) :
    periodUtility σ φ ((W * N' + X) / P) N' Z ≤ periodUtility σ φ C N Z := by
  have hu := utilC_le_tangent hσ hC hC'
  have hv := disutilN_tangent_le hφ hN hN'
  have hdiff : (W * N' + X) / P - C = W / P * (N' - N) := by
    rw [show C = (W * N + X) / P by rw [← hbud]; field_simp]
    field_simp
    ring
  have hkey : C ^ (-σ) * (W / P) = N ^ φ := by
    rw [hfoc, Real.rpow_neg hC.le]
    field_simp [(Real.rpow_pos_of_pos hC σ).ne']
  unfold periodUtility
  apply mul_le_mul_of_nonneg_right _ hZ.le
  rw [hdiff] at hu
  nlinarith

/-- Galí (2015), ch. 2, eqs. (4) and (7), pp. 19–21: for `σ > 0`, `φ ≥ 0`, a point with
`C, N > 0` on the budget line solves the static problem iff `W/P = N^φ C^σ`. -/
theorem static_optimum_iff {σ φ P W X Z C N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hP : 0 < P)
    (hZ : 0 < Z) (hN : 0 < N) (hC : 0 < C) (hbud : P * C = W * N + X) :
    (∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      periodUtility σ φ ((W * N' + X) / P) N' Z ≤ periodUtility σ φ C N Z) ↔
      W / P = N ^ φ * C ^ σ :=
  ⟨fun h => static_foc_necessary hφ hP hZ hC hbud
      (static_isLocalMax_of_optimal hP hN hC hbud h),
    fun h _ hN' hC' => static_foc_sufficient hσ hφ hP hZ hN hC hbud h hN' hC'⟩

/-- Galí (2015), eq. (2), p. 54 (ch. 2, eq. (9), p. 21), **exact**: for positive levels,
`W/P = N^φ C^σ` iff `w − p = σ c + φ n` in logs. -/
theorem labour_supply_log_iff {σ φ W P C N : ℝ} (hW : 0 < W) (hP : 0 < P) (hC : 0 < C)
    (hN : 0 < N) :
    W / P = N ^ φ * C ^ σ ↔
      Real.log W - Real.log P = σ * Real.log C + φ * Real.log N := by
  have h1 : (0 : ℝ) < W / P := div_pos hW hP
  have h2 : (0 : ℝ) < N ^ φ * C ^ σ :=
    mul_pos (Real.rpow_pos_of_pos hN φ) (Real.rpow_pos_of_pos hC σ)
  rw [← Real.log_injOn_pos.eq_iff h1 h2, Real.log_div hW.ne' hP.ne',
    Real.log_mul (Real.rpow_pos_of_pos hN φ).ne' (Real.rpow_pos_of_pos hC σ).ne',
    Real.log_rpow hN, Real.log_rpow hC]
  constructor <;> intro h <;> linarith

/-! ### The intertemporal problem: the Euler equation -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 54 (ch. 2, eqs. (5) and (8), pp. 19–21): the consumption Euler equation
at date `t`, node by node, with the date-`t` variables taken out of `E_t` as numbers:
`Q_t = β (C_t^σ P_t / Z_t) E_t[C_{t+1}^{−σ} Z_{t+1} / P_{t+1}]`. -/
def EulerEq (β σ : ℝ) (Q C P Z : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Q t ω = β * (C t ω ^ σ * P t ω / Z t ω) *
    𝔼.E t (fun ω' => C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω') ω

/-- Galí (2015), p. 54 (ch. 2, eq. (8), p. 21): at each node the Euler equation reads
`Q_t = β E_t[(C_{t+1}/C_t)^{−σ} (Z_{t+1}/Z_t) (P_t/P_{t+1})]`, the book's printed form. -/
theorem eulerEq_ratio_form {β σ : ℝ} {Q C P Z : ℕ → Ω → ℝ} {t : ℕ}
    (hC : ∀ ω, 0 < C t ω) (hC1 : ∀ ω, 0 ≤ C (t + 1) ω) (hZ : ∀ ω, 0 < Z t ω) :
    EulerEq 𝔼 β σ Q C P Z t ↔ ∀ ω, Q t ω = β * 𝔼.E t (fun ω' =>
      (C (t + 1) ω' / C t ω) ^ (-σ) * (Z (t + 1) ω' / Z t ω) * (P t ω / P (t + 1) ω')) ω := by
  have key : ∀ ω, (fun ω' =>
      (C (t + 1) ω' / C t ω) ^ (-σ) * (Z (t + 1) ω' / Z t ω) * (P t ω / P (t + 1) ω'))
      = (C t ω ^ σ * P t ω / Z t ω) •
        (fun ω' => C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω') := by
    intro ω
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Real.div_rpow (hC1 ω') (hC ω).le, Real.rpow_neg (hC ω).le]
    have := (Real.rpow_pos_of_pos (hC ω) σ).ne'
    have := (hZ ω).ne'
    field_simp
  unfold EulerEq
  refine forall_congr' fun ω => ?_
  rw [key ω, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Galí (2015), ch. 2, p. 20: expected utility as of date `t` (node `ω`) of the one-period
perturbation that buys `δ` more bonds at `t` (consumption falls by `Q_t δ/P_t`) and consumes
the payoff `δ` at `t + 1` (consumption rises by `δ/P_{t+1}` in every state); hours and all
other dates are unchanged, so by separability only these two terms of
`E_t ∑ β^k U_{t+k}` change. -/
noncomputable def perturbedValue (β σ : ℝ) (Q C P Z : ℕ → Ω → ℝ) (t : ℕ) (δ : ℝ) :
    Ω → ℝ :=
  fun ω => Z t ω * utilC σ (C t ω - Q t ω * δ / P t ω)
    + β * 𝔼.E t (fun ω' => Z (t + 1) ω' * utilC σ (C (t + 1) ω' + δ / P (t + 1) ω')) ω

/-- The concavity sandwich behind Galí (2015), ch. 2, p. 20: for `|δ| < m ≤ P C`, the
date-`t+1` utility gain of the bond perturbation is at least
`(1 + δ/m)^{−σ} δ C^{−σ} Z / P` in every state. -/
theorem utility_gain_lower {σ m δ c p z : ℝ} (hσ : 0 < σ) (hm : 0 < m) (hc : 0 < c)
    (hp : 0 < p) (hz : 0 ≤ z) (hmpc : m ≤ p * c) (hδ : |δ| < m) :
    (1 + δ / m) ^ (-σ) * δ * (c ^ (-σ) * z / p)
      ≤ z * utilC σ (c + δ / p) - z * utilC σ (c + 0 / p) := by
  rw [zero_div, add_zero]
  have hδm := abs_lt.1 hδ
  have hk : 0 < 1 + δ / m := by
    have : -1 < δ / m := by rw [lt_div_iff₀ hm]; linarith
    linarith
  have hcp : 0 < c * (1 + δ / m) := mul_pos hc hk
  -- position of `c + δ/p` relative to `c (1 + δ/m)`
  have hrel : (0 ≤ δ → c + δ / p ≤ c * (1 + δ / m)) ∧ (δ < 0 → c * (1 + δ / m) ≤ c + δ / p) := by
    constructor
    · intro h0
      have : δ / p ≤ δ * c / m := by
        rw [div_le_div_iff₀ hp hm]; nlinarith
      have e : c * (1 + δ / m) = c + δ * c / m := by field_simp
      linarith
    · intro h0
      have : δ * c / m ≤ δ / p := by
        rw [div_le_div_iff₀ hm hp]; nlinarith
      have e : c * (1 + δ / m) = c + δ * c / m := by field_simp
      linarith
  have ha : 0 < c + δ / p := by
    rcases le_or_gt 0 δ with h0 | h0
    · have : 0 ≤ δ / p := div_nonneg h0 hp.le
      linarith
    · linarith [hrel.2 h0]
  -- tangent at `a = c + δ/p` evaluated at `c`
  have htan := utilC_le_tangent hσ ha hc
  have hsplit : (c * (1 + δ / m)) ^ (-σ) = c ^ (-σ) * (1 + δ / m) ^ (-σ) :=
    Real.mul_rpow hc.le hk.le
  have hmain : (1 + δ / m) ^ (-σ) * c ^ (-σ) * (δ / p) ≤ (c + δ / p) ^ (-σ) * (δ / p) := by
    rcases le_or_gt 0 δ with h0 | h0
    · have hle : (c * (1 + δ / m)) ^ (-σ) ≤ (c + δ / p) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos ha (hrel.1 h0) (by linarith)
      rw [hsplit] at hle
      exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg h0 hp.le)
    · have hle : (c + δ / p) ^ (-σ) ≤ (c * (1 + δ / m)) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hcp (hrel.2 h0) (by linarith)
      rw [hsplit] at hle
      exact mul_le_mul_of_nonpos_right (by linarith) (div_nonpos_of_nonpos_of_nonneg h0.le hp.le)
  have hgain : (c + δ / p) ^ (-σ) * (δ / p) ≤ utilC σ (c + δ / p) - utilC σ c := by
    have : c - (c + δ / p) = -(δ / p) := by ring
    rw [this] at htan
    linarith
  have e : (1 + δ / m) ^ (-σ) * δ * (c ^ (-σ) * z / p)
      = z * ((1 + δ / m) ^ (-σ) * c ^ (-σ) * (δ / p)) := by
    field_simp
  rw [e, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (hmain.trans hgain) hz

/-- Galí (2015), ch. 2, eqs. (5) and (8), pp. 19–21 (**necessity of the Euler equation**):
if at every date-`t` node no small bond perturbation `δ` is profitable, then the Euler
equation holds at date `t`. Hypotheses: `σ, β > 0`, positive `C_t, P_t, Z_t`, positive
`C_{t+1}, P_{t+1}`, `Z_{t+1} ≥ 0`, and a uniform lower bound `m > 0` on next period's nominal
expenditure `P_{t+1} C_{t+1}` (automatic for finitely many states). -/
theorem euler_necessary {β σ : ℝ} {Q C P Z : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ) (hβ : 0 < β)
    (hC : ∀ ω, 0 < C t ω) (hP : ∀ ω, 0 < P t ω) (hZ : ∀ ω, 0 < Z t ω)
    (hC1 : ∀ ω, 0 < C (t + 1) ω) (hP1 : ∀ ω, 0 < P (t + 1) ω) (hZ1 : ∀ ω, 0 ≤ Z (t + 1) ω)
    {m : ℝ} (hm : 0 < m) (hmPC : ∀ ω, m ≤ P (t + 1) ω * C (t + 1) ω)
    (hopt : ∀ ω, ∀ᶠ δ in 𝓝 0,
      perturbedValue 𝔼 β σ Q C P Z t δ ω ≤ perturbedValue 𝔼 β σ Q C P Z t 0 ω) :
    EulerEq 𝔼 β σ Q C P Z t := by
  intro ω
  set G : Ω → ℝ := fun ω' => C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω' with hGdef
  set B := β * 𝔼.E t G ω with hB
  set A := Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω) with hA
  set f : ℝ → ℝ := fun δ => Z t ω * utilC σ (C t ω - Q t ω * δ / P t ω) with hfdef
  set g : ℝ → Ω → ℝ :=
    fun δ ω' => Z (t + 1) ω' * utilC σ (C (t + 1) ω' + δ / P (t + 1) ω') with hgdef
  set k : ℝ → ℝ := fun δ => (1 + δ / m) ^ (-σ) with hkdef
  -- derivative of the date-`t` term
  have hf : HasDerivAt f (-A) 0 := by
    have hin : HasDerivAt (fun δ : ℝ => C t ω - Q t ω * δ / P t ω) (-(Q t ω / P t ω)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul (Q t ω)).div_const (P t ω)).const_sub
        (C t ω)
      simpa [mul_div_assoc] using this
    have hu : HasDerivAt (utilC σ) ((C t ω - Q t ω * 0 / P t ω) ^ (-σ))
        (C t ω - Q t ω * 0 / P t ω) := hasDerivAt_utilC σ (by simpa using hC ω)
    have := (hu.comp 0 hin).const_mul (Z t ω)
    refine this.congr_deriv ?_
    simp [hA]
    ring
  -- the lower bound on the change of the date-`t` value
  have hlow : ∀ δ, |δ| < m →
      perturbedValue 𝔼 β σ Q C P Z t δ ω - perturbedValue 𝔼 β σ Q C P Z t 0 ω
        ≥ f δ - f 0 + k δ * δ * B := by
    intro δ hδ
    have hpt : (k δ * δ) • G ≤ g δ - g 0 := by
      intro ω'
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hgdef, hGdef, hkdef]
      exact utility_gain_lower hσ hm (hC1 ω') (hP1 ω') (hZ1 ω') (hmPC ω') hδ
    have hE := 𝔼.mono t hpt ω
    rw [map_smul, map_sub] at hE
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hE
    have hβE := mul_le_mul_of_nonneg_left hE hβ.le
    simp only [perturbedValue, ge_iff_le]
    change f δ - f 0 + k δ * δ * B ≤ f δ + β * 𝔼.E t (g δ) ω - (f 0 + β * 𝔼.E t (g 0) ω)
    rw [hB]
    nlinarith
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), f δ - f 0 + k δ * δ * B ≤ 0 := by
    have hball : ∀ᶠ δ in 𝓝 (0 : ℝ), |δ| < m := by
      have : Tendsto (fun δ : ℝ => |δ|) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_abs.tendsto (0 : ℝ))
      exact this.eventually (gt_mem_nhds hm)
    filter_upwards [hopt ω, hball] with δ h1 h2
    have := hlow δ h2
    linarith
  have hk : Tendsto k (𝓝 0) (𝓝 1) := by
    have hca : ContinuousAt k 0 :=
      (continuousAt_const.add (continuousAt_id.div_const m)).rpow_const (Or.inl (by simp))
    simpa [hkdef] using hca.tendsto
  have hlimR : Tendsto (fun δ => δ⁻¹ * (f δ - f 0) + k δ * B) (𝓝[>] 0) (𝓝 (-A + 1 * B)) := by
    have h1 := hf.tendsto_slope_zero_right
    simp only [zero_add, smul_eq_mul] at h1
    exact h1.add ((hk.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds)
  have hlimL : Tendsto (fun δ => δ⁻¹ * (f δ - f 0) + k δ * B) (𝓝[<] 0) (𝓝 (-A + 1 * B)) := by
    have h1 := hf.tendsto_slope_zero_left
    simp only [zero_add, smul_eq_mul] at h1
    exact h1.add ((hk.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds)
  have hsplit : ∀ δ : ℝ, δ ≠ 0 →
      δ⁻¹ * (f δ - f 0) + k δ * B = δ⁻¹ * (f δ - f 0 + k δ * δ * B) := by
    intro δ hδ
    field_simp
  have hR : -A + 1 * B ≤ 0 := by
    refine le_of_tendsto hlimR ?_
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with δ h1 h2
    rw [hsplit δ (ne_of_gt h2)]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (le_of_lt h2)) h1
  have hL : 0 ≤ -A + 1 * B := by
    refine ge_of_tendsto hlimL ?_
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with δ h1 h2
    rw [hsplit δ (ne_of_lt h2)]
    exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.2 (le_of_lt h2)) h1
  have hAB : A = B := by linarith
  rw [hA, hB] at hAB
  have hCs : C t ω ^ σ * C t ω ^ (-σ) = 1 := by
    rw [Real.rpow_neg (hC ω).le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos (hC ω) σ).ne'
  have hZ0 := (hZ ω).ne'
  have hP0 := (hP ω).ne'
  calc Q t ω = (C t ω ^ σ * C t ω ^ (-σ)) * Q t ω := by rw [hCs, one_mul]
    _ = C t ω ^ σ * P t ω / Z t ω * (Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω)) := by
        field_simp
    _ = β * (C t ω ^ σ * P t ω / Z t ω) * 𝔼.E t G ω := by rw [hAB]; ring

/-- Galí (2015), ch. 2, p. 20: with finitely many states, positive `C_{t+1}` and `P_{t+1}`
have a uniform lower bound `m > 0` on next period's nominal expenditure `P_{t+1} C_{t+1}`. -/
theorem exists_expenditure_lower_bound [Finite Ω] {C P : Ω → ℝ} (hC : ∀ ω, 0 < C ω)
    (hP : ∀ ω, 0 < P ω) : ∃ m, 0 < m ∧ ∀ ω, m ≤ P ω * C ω := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact ⟨1, one_pos, fun ω => (IsEmpty.false ω).elim⟩
  · obtain ⟨ω₀, h₀⟩ := Finite.exists_min fun ω => P ω * C ω
    exact ⟨P ω₀ * C ω₀, mul_pos (hP ω₀) (hC ω₀), h₀⟩

/-- Galí (2015), ch. 2, eqs. (5) and (8), pp. 19–21 (**necessity**, finitely many states):
no profitable small bond perturbation at any date-`t` node implies the Euler equation. -/
theorem euler_necessary_finite [Finite Ω] {β σ : ℝ} {Q C P Z : ℕ → Ω → ℝ} {t : ℕ}
    (hσ : 0 < σ) (hβ : 0 < β) (hC : ∀ ω, 0 < C t ω) (hP : ∀ ω, 0 < P t ω)
    (hZ : ∀ ω, 0 < Z t ω) (hC1 : ∀ ω, 0 < C (t + 1) ω) (hP1 : ∀ ω, 0 < P (t + 1) ω)
    (hZ1 : ∀ ω, 0 ≤ Z (t + 1) ω)
    (hopt : ∀ ω, ∀ᶠ δ in 𝓝 0,
      perturbedValue 𝔼 β σ Q C P Z t δ ω ≤ perturbedValue 𝔼 β σ Q C P Z t 0 ω) :
    EulerEq 𝔼 β σ Q C P Z t := by
  obtain ⟨m, hm, hmPC⟩ := exists_expenditure_lower_bound hC1 hP1
  exact euler_necessary 𝔼 hσ hβ hC hP hZ hC1 hP1 hZ1 hm hmPC hopt

/-- Galí (2015), ch. 2, eqs. (5) and (8), pp. 19–21 (**sufficiency** for one-period
perturbations, by concavity): if the Euler equation holds at date `t`, no feasible bond
perturbation `δ` (one keeping consumption positive) raises expected utility at any node. -/
theorem euler_sufficient {β σ : ℝ} {Q C P Z : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ) (hβ : 0 ≤ β)
    (hC : ∀ ω, 0 < C t ω) (hP : ∀ ω, 0 < P t ω) (hZ : ∀ ω, 0 < Z t ω)
    (hC1 : ∀ ω, 0 < C (t + 1) ω) (hZ1 : ∀ ω, 0 ≤ Z (t + 1) ω)
    (heul : EulerEq 𝔼 β σ Q C P Z t) {δ : ℝ} (ω : Ω)
    (hfeas : 0 < C t ω - Q t ω * δ / P t ω) (hfeas1 : ∀ ω', 0 < C (t + 1) ω' + δ / P (t + 1) ω') :
    perturbedValue 𝔼 β σ Q C P Z t δ ω ≤ perturbedValue 𝔼 β σ Q C P Z t 0 ω := by
  set G : Ω → ℝ := fun ω' => C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω' with hGdef
  have hpt : (fun ω' => Z (t + 1) ω' * utilC σ (C (t + 1) ω' + δ / P (t + 1) ω'))
      ≤ (fun ω' => Z (t + 1) ω' * utilC σ (C (t + 1) ω' + 0 / P (t + 1) ω')) + δ • G := by
    intro ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_div, add_zero, hGdef]
    have h := utilC_le_tangent hσ (hC1 ω') (hfeas1 ω')
    have h2 := mul_le_mul_of_nonneg_left h (hZ1 ω')
    have e : Z (t + 1) ω' * (C (t + 1) ω' ^ (-σ) * (C (t + 1) ω' + δ / P (t + 1) ω'
        - C (t + 1) ω')) = δ * (C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω') := by
      ring
    nlinarith
  have hE := 𝔼.mono t hpt ω
  rw [map_add, map_smul] at hE
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hE
  have h0 := utilC_le_tangent hσ (hC ω) hfeas
  have h0' := mul_le_mul_of_nonneg_left h0 (hZ ω).le
  have he : Q t ω = β * (C t ω ^ σ * P t ω / Z t ω) * 𝔼.E t G ω := heul ω
  have hCs : C t ω ^ σ * C t ω ^ (-σ) = 1 := by
    rw [Real.rpow_neg (hC ω).le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos (hC ω) σ).ne'
  -- `Z_t C_t^{−σ} Q_t / P_t = β E_t G`
  have hAB : Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω) = β * 𝔼.E t G ω := by
    have hZ0 := (hZ ω).ne'
    have hP0 := (hP ω).ne'
    calc Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω)
        = (C t ω ^ σ * C t ω ^ (-σ)) * β * 𝔼.E t G ω * (Z t ω / Z t ω) * (P t ω / P t ω) := by
          rw [he]; ring
      _ = β * 𝔼.E t G ω := by rw [hCs, div_self hZ0, div_self hP0]; ring
  have e1 : Z t ω * (C t ω ^ (-σ) * (C t ω - Q t ω * δ / P t ω - C t ω))
      = -(δ * (Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω))) := by ring
  rw [mul_add, e1] at h0'
  have hβE := mul_le_mul_of_nonneg_left hE hβ
  have hδ : δ * (Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω)) = δ * (β * 𝔼.E t G ω) := by rw [hAB]
  simp only [perturbedValue, mul_zero, zero_div, sub_zero]
  simp only [zero_div] at hβE
  nlinarith

/-! ### Log forms of the Euler equation -/

/-- Galí (2015), p. 54 and ch. 2, App. 2.1, p. 44: the Euler moment at node `ω`,
`E_t[exp(i_t − ρ − σ(c_{t+1} − c_t) − (p_{t+1} − p_t) + (z_{t+1} − z_t))]`, all variables
in logs, date-`t` values entering as numbers. -/
noncomputable def eulerMoment (σ ρ : ℝ) (i c p z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  𝔼.E t (fun ω' => Real.exp (i t ω - ρ - σ * (c (t + 1) ω' - c t ω)
    - (p (t + 1) ω' - p t ω) + (z (t + 1) ω' - z t ω))) ω

/-- Galí (2015), p. 54 (ch. 2, eq. (8), p. 21), **exact**: with `Q = e^{−i}`, `β = e^{−ρ}`,
`C = e^c`, `P = e^p`, `Z = e^z`, the Euler equation at date `t` is equivalent to the Euler
moment being equal to one at every node. -/
theorem eulerEq_iff_moment (σ ρ : ℝ) (i c p z : ℕ → Ω → ℝ) (t : ℕ) :
    EulerEq 𝔼 (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω)) (fun t ω => Real.exp (c t ω))
        (fun t ω => Real.exp (p t ω)) (fun t ω => Real.exp (z t ω)) t ↔
      ∀ ω, eulerMoment 𝔼 σ ρ i c p z t ω = 1 := by
  set G : Ω → ℝ := fun ω' => Real.exp (c (t + 1) ω') ^ (-σ) * Real.exp (z (t + 1) ω')
    / Real.exp (p (t + 1) ω') with hGdef
  have hmom : ∀ ω, eulerMoment 𝔼 σ ρ i c p z t ω
      = Real.exp (i t ω - ρ + σ * c t ω + p t ω - z t ω) * 𝔼.E t G ω := by
    intro ω
    have hfun : (fun ω' => Real.exp (i t ω - ρ - σ * (c (t + 1) ω' - c t ω)
        - (p (t + 1) ω' - p t ω) + (z (t + 1) ω' - z t ω)))
        = Real.exp (i t ω - ρ + σ * c t ω + p t ω - z t ω) • G := by
      funext ω'
      simp only [Pi.smul_apply, smul_eq_mul, hGdef]
      rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring
    rw [eulerMoment, hfun, map_smul, Pi.smul_apply, smul_eq_mul]
  unfold EulerEq
  refine forall_congr' fun ω => ?_
  rw [hmom ω]
  simp only
  rw [← hGdef]
  have e1 : Real.exp (c t ω) ^ σ * Real.exp (p t ω) / Real.exp (z t ω)
      = Real.exp (σ * c t ω + p t ω - z t ω) := by
    rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_sub, mul_comm (c t ω)]
  have e2 : Real.exp (i t ω - ρ + σ * c t ω + p t ω - z t ω)
      = Real.exp (i t ω) * (Real.exp (-ρ) * Real.exp (σ * c t ω + p t ω - z t ω)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [e1, e2]
  have hi : Real.exp (i t ω) * Real.exp (-i t ω) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  constructor
  · intro h
    rw [mul_assoc, ← h, hi]
  · intro h
    have hpos := Real.exp_pos (i t ω)
    have : Real.exp (-i t ω) = Real.exp (-i t ω) * (Real.exp (i t ω) *
        (Real.exp (-ρ) * Real.exp (σ * c t ω + p t ω - z t ω) * 𝔼.E t G ω)) := by
      rw [← mul_assoc (Real.exp (i t ω)), h, mul_one]
    rw [this, ← mul_assoc, mul_comm (Real.exp (-i t ω)), hi, one_mul]

/-- Galí (2015), p. 54 and ch. 2, p. 21 (**exact, perfect foresight**): under perfect
foresight the Euler equation holds at date `t` iff, in logs,
`i_t − (p_{t+1} − p_t) − ρ = σ (c_{t+1} − c_t) − (z_{t+1} − z_t)`. -/
theorem pf_eulerEq_iff (σ ρ : ℝ) (i c p z : ℕ → Unit → ℝ) (t : ℕ) :
    EulerEq perfectForesight (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω))
        (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (p t ω))
        (fun t ω => Real.exp (z t ω)) t ↔
      ∀ ω, i t ω - (p (t + 1) ω - p t ω) - ρ
        = σ * (c (t + 1) ω - c t ω) - (z (t + 1) ω - z t ω) := by
  rw [eulerEq_iff_moment]
  refine forall_congr' fun ω => ?_
  simp only [eulerMoment, perfectForesight, LinearMap.id_apply]
  rw [← Real.exp_zero, Real.exp_eq_exp]
  constructor <;> intro h <;> linarith

/-- Galí (2015), p. 54 (**exact, perfect foresight, no preference shock**): with `Z ≡ 1` the
Euler equation is exactly `i_t − π_{t+1} − ρ = σ (c_{t+1} − c_t)` in logs. -/
theorem pf_eulerEq_iff_noshock (σ ρ : ℝ) (i c p : ℕ → Unit → ℝ) (t : ℕ) :
    EulerEq perfectForesight (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω))
        (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (p t ω)) (fun _ _ => 1) t ↔
      ∀ ω, i t ω - (p (t + 1) ω - p t ω) - ρ = σ * (c (t + 1) ω - c t ω) := by
  have h := pf_eulerEq_iff σ ρ i c p (fun _ _ => 0) t
  simp only [Real.exp_zero, sub_self, sub_zero] at h
  exact h

/-! ### The first-order approximation under uncertainty -/

/-- Galí (2015), ch. 2, App. 2.1, p. 44 (the first-order step): for a bounded random variable
`Y`, `s ↦ E_t[exp(s Y)](ω)` has derivative `E_t Y (ω)` at `s = 0`. Only linearity,
monotonicity and constants of `E_t` are used: the remainder `exp(sY) − 1 − sY` is bounded by
`s² M²` uniformly, and `|E_t x| ≤ sup |x|`. -/
theorem hasDerivAt_E_exp {Y : Ω → ℝ} {M : ℝ} (hY : ∀ ω, |Y ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω) (𝔼.E t Y ω) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  simp only [sub_zero]
  have hO : (fun s : ℝ => 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω
      - 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω - s • 𝔼.E t Y ω) =O[𝓝 0]
      fun s : ℝ => s ^ 2 := by
    apply Asymptotics.IsBigO.of_bound (M ^ 2)
    have hcont : Continuous (fun s : ℝ => |s| * M) := by fun_prop
    have hlim : Tendsto (fun s : ℝ => |s| * M) (𝓝 0) (𝓝 0) := by
      have := hcont.tendsto 0
      rwa [abs_zero, zero_mul] at this
    filter_upwards [hlim.eventually (ge_mem_nhds one_pos)] with s hs
    have key : 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω
        - 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω - s • 𝔼.E t Y ω
        = 𝔼.E t (fun ω' => Real.exp (s * Y ω') - 1 - s * Y ω') ω := by
      have h1 : (fun ω' => Real.exp (s * Y ω') - 1 - s * Y ω')
          = (fun ω' => Real.exp (s * Y ω')) - (fun _ => (1 : ℝ)) - s • Y := by
        funext ω'
        simp
      have h2 : (fun ω' => Real.exp (0 * Y ω')) = fun _ => (1 : ℝ) := by
        funext ω'
        simp
      rw [h1, h2, map_sub, map_sub, map_smul, 𝔼.const]
      simp
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs]
    apply 𝔼.abs_E_le
    intro ω'
    have hy : |s * Y ω'| ≤ 1 := by
      rw [abs_mul]
      calc |s| * |Y ω'| ≤ |s| * M := mul_le_mul_of_nonneg_left (hY ω') (abs_nonneg s)
        _ ≤ 1 := hs
    have hsq : (s * Y ω') ^ 2 ≤ M ^ 2 * |s ^ 2| := by
      rw [abs_pow, sq_abs, mul_pow, mul_comm]
      have : Y ω' ^ 2 ≤ M ^ 2 := by
        have := hY ω'
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg s)
    exact (Real.abs_exp_sub_one_sub_id_le hy).trans hsq
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

/-- Galí (2015), ch. 2, App. 2.1, p. 44: for a bounded `Y`,
`s ↦ log E_t[exp(s Y)](ω)` has derivative `E_t Y (ω)` at `s = 0`. -/
theorem hasDerivAt_log_E_exp {Y : Ω → ℝ} {M : ℝ} (hY : ∀ ω, |Y ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => Real.log (𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω))
      (𝔼.E t Y ω) 0 := by
  have h1 : 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω = 1 := by
    have : (fun ω' => Real.exp (0 * Y ω')) = fun _ => (1 : ℝ) := by
      funext ω'
      simp
    rw [this, 𝔼.const]
  have := (hasDerivAt_E_exp 𝔼 hY t ω).log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at this
  exact this

/-- Galí (2015), p. 54, eq. (3): the linear expression obtained by linearising the Euler
moment around the zero-inflation steady state, in deviations (hats):
`î_t − σ (E_t ĉ_{t+1} − ĉ_t) − (E_t p̂_{t+1} − p̂_t) + (E_t ẑ_{t+1} − ẑ_t)`. -/
noncomputable def linearisedEuler (σ : ℝ) (ih ch ph zh : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ih t ω - σ * (𝔼.E t (ch (t + 1)) ω - ch t ω) - (𝔼.E t (ph (t + 1)) ω - ph t ω)
    + (𝔼.E t (zh (t + 1)) ω - zh t ω)

/-- Galí (2015), p. 55: at the zero-inflation steady state (`i = ρ`, constant `c̄`, `p̄`,
`z = 0`), the Euler moment equals one: the steady state satisfies the Euler equation. -/
theorem eulerMoment_family_zero (σ ρ cbar pbar : ℝ) (ih ch ph zh : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    eulerMoment 𝔼 σ ρ (fun t ω => ρ + 0 * ih t ω) (fun t ω => cbar + 0 * ch t ω)
      (fun t ω => pbar + 0 * ph t ω) (fun t ω => 0 * zh t ω) t ω = 1 := by
  simp only [eulerMoment, zero_mul, add_zero, sub_self, mul_zero, Real.exp_zero]
  rw [𝔼.const]

/-- Galí (2015), p. 54, eq. (3), as an **exact derivative** (ch. 2, App. 2.1, p. 44): along
the family of stochastic paths `i = ρ + s î`, `c = c̄ + s ĉ`, `p = p̄ + s p̂`, `z = s ẑ` around
the zero-inflation steady state, with bounded deviations, the log Euler residual
`s ↦ log E_t[exp(i_t − ρ − σΔc − Δp + Δz)](ω)` has derivative at `s = 0` equal to
`linearisedEuler σ î ĉ p̂ ẑ t ω`. -/
theorem hasDerivAt_log_eulerMoment_family (σ ρ cbar pbar : ℝ) {ih ch ph zh : ℕ → Ω → ℝ}
    (hc : BoundedProc ch) (hp : BoundedProc ph) (hz : BoundedProc zh) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => Real.log (eulerMoment 𝔼 σ ρ (fun t ω => ρ + s * ih t ω)
        (fun t ω => cbar + s * ch t ω) (fun t ω => pbar + s * ph t ω)
        (fun t ω => s * zh t ω) t ω))
      (linearisedEuler 𝔼 σ ih ch ph zh t ω) 0 := by
  obtain ⟨Mc, hMc⟩ := hc
  obtain ⟨Mp, hMp⟩ := hp
  obtain ⟨Mz, hMz⟩ := hz
  set a : ℝ := ih t ω + σ * ch t ω + ph t ω - zh t ω with ha
  set Y : Ω → ℝ := fun ω' => a + (-σ * ch (t + 1) ω' - ph (t + 1) ω' + zh (t + 1) ω') with hY
  have hbd : ∀ ω', |Y ω'| ≤ |a| + |σ| * Mc + Mp + Mz := by
    intro ω'
    have h1 := abs_le.1 (show |σ * ch (t + 1) ω'| ≤ |σ| * Mc by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMc _ _) (abs_nonneg σ))
    have h2 := abs_le.1 (hMp (t + 1) ω')
    have h3 := abs_le.1 (hMz (t + 1) ω')
    have h4 := abs_le.1 (le_refl |a|)
    rw [abs_le]
    simp only [hY]
    constructor <;> linarith
  have hfam : ∀ s : ℝ, eulerMoment 𝔼 σ ρ (fun t ω => ρ + s * ih t ω)
      (fun t ω => cbar + s * ch t ω) (fun t ω => pbar + s * ph t ω)
      (fun t ω => s * zh t ω) t ω = 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω := by
    intro s
    unfold eulerMoment
    refine congrArg (fun x => 𝔼.E t x ω) (funext fun ω' => ?_)
    congr 1
    simp only [hY, ha]
    ring
  simp_rw [hfam]
  have hval : 𝔼.E t Y ω = linearisedEuler 𝔼 σ ih ch ph zh t ω := by
    have hfun : Y = (fun _ => a) + ((-σ) • ch (t + 1) - ph (t + 1) + zh (t + 1)) := by
      funext ω'
      simp [hY, smul_eq_mul]
    rw [hfun, map_add, 𝔼.const, map_add, map_sub, map_smul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, linearisedEuler, ha]
    ring
  rw [← hval]
  exact hasDerivAt_log_E_exp 𝔼 hbd t ω

/-- Galí (2015), p. 54, eq. (3): the log-linear Euler equation as a model equation,
`c_t = E_t c_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ) + σ⁻¹ (1 − ρ_z) z_t`. -/
def EulerLogLinear (σ ρ ρz : ℝ) (c i infl z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)
    + (σ⁻¹ * (1 - ρz)) • z t

/-- Galí (2015), p. 54: for an adapted (log) price level `p̂` with inflation
`π̂_{t+1} = p̂_{t+1} − p̂_t`, the linearised Euler expression is
`î_t − σ (E_t ĉ_{t+1} − ĉ_t) − E_t π̂_{t+1} + (E_t ẑ_{t+1} − ẑ_t)`. -/
theorem linearisedEuler_eq (σ : ℝ) {ih ch ph zh infl : ℕ → Ω → ℝ} (hp : 𝔼.Adapted ph)
    (hinfl : ∀ t, infl (t + 1) = ph (t + 1) - ph t) (t : ℕ) :
    linearisedEuler 𝔼 σ ih ch ph zh t = ih t - σ • (𝔼.E t (ch (t + 1)) - ch t)
      - 𝔼.E t (infl (t + 1)) + (𝔼.E t (zh (t + 1)) - zh t) := by
  funext ω
  rw [hinfl, map_sub, hp t]
  simp [linearisedEuler]

/-- Galí (2015), p. 54, eq. (3) (**the first-order condition is exactly (3)**): for `σ ≠ 0`,
an adapted price level and an AR(1) preference shifter (`E_t ẑ_{t+1} = ρ_z ẑ_t`), the
linearised Euler expression vanishes at every date and node iff eq. (3) holds for the
deviations with `i_t = ρ + î_t`. -/
theorem linearisedEuler_eq_zero_iff {σ ρ ρz : ℝ} (hσ : σ ≠ 0) {ih ch ph zh infl : ℕ → Ω → ℝ}
    (hp : 𝔼.Adapted ph) (hinfl : ∀ t, infl (t + 1) = ph (t + 1) - ph t)
    (hzar : 𝔼.IsAR1 ρz zh) :
    (∀ t, linearisedEuler 𝔼 σ ih ch ph zh t = 0) ↔
      EulerLogLinear 𝔼 σ ρ ρz ch (fun t => (fun _ => ρ) + ih t) infl zh := by
  unfold EulerLogLinear
  refine forall_congr' fun t => ?_
  rw [linearisedEuler_eq 𝔼 σ hp hinfl t, hzar.2 t]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    field_simp
    linear_combination e
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    field_simp at e
    linear_combination e

/-- Galí (2015), p. 54, eq. (3): (3) for log consumption `c̄ + ĉ` is equivalent to (3) for
the deviation `ĉ`, since `E_t` leaves constants unchanged. -/
theorem eulerLogLinear_add_const_iff (σ ρ ρz cbar : ℝ) (ch i infl z : ℕ → Ω → ℝ) :
    EulerLogLinear 𝔼 σ ρ ρz (fun t => (fun _ => cbar) + ch t) i infl z ↔
      EulerLogLinear 𝔼 σ ρ ρz ch i infl z := by
  unfold EulerLogLinear
  refine forall_congr' fun t => ?_
  rw [map_add, 𝔼.const]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    linarith
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    linarith

/-- Galí (2015), p. 54, eq. (3) (**exact under perfect foresight**): if the nonlinear Euler
equation holds at every date, `π_{t+1} = p_{t+1} − p_t`, and the preference shifter follows
`z_{t+1} = ρ_z z_t`, then (3) holds exactly (`σ ≠ 0`). -/
theorem pf_eulerEq_imp_eulerLogLinear {σ ρ ρz : ℝ} (hσ : σ ≠ 0) {i c p z infl : ℕ → Unit → ℝ}
    (heul : ∀ t, EulerEq perfectForesight (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω))
      (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (p t ω))
      (fun t ω => Real.exp (z t ω)) t)
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t) (hz : ∀ t, z (t + 1) = ρz • z t) :
    EulerLogLinear perfectForesight σ ρ ρz c i infl z := by
  intro t
  have h := (pf_eulerEq_iff σ ρ i c p z t).1 (heul t)
  funext ω
  have e := h ω
  have ez := congrFun (hz t) ω
  have ei := congrFun (hinfl t) ω
  simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul] at e ez ei ⊢
  rw [ei]
  rw [ez] at e
  field_simp
  linear_combination e

/-! ### Goods-market clearing and the Euler equation in output -/

/-- Galí (2015), eqs. (12)–(13), p. 58 (**exact**): with goods-market clearing `Y_t = C_t`
(so `y_t = c_t` in logs), the log-linear Euler equation (3) in consumption is exactly the
Euler equation in output `DIS.EulerOutput`, eq. (13). -/
theorem eulerOutput_iff_of_clearing {σ ρ ρz : ℝ} {Y C y c i infl z : ℕ → Ω → ℝ}
    (hclear : ∀ t, Y t = C t) (hy : ∀ t ω, y t ω = Real.log (Y t ω))
    (hc : ∀ t ω, c t ω = Real.log (C t ω)) :
    DIS.EulerOutput 𝔼 σ ρ ρz y i infl z ↔ EulerLogLinear 𝔼 σ ρ ρz c i infl z := by
  have hyc : y = c := by
    funext t ω
    rw [hy, hc, hclear]
  subst hyc
  rfl

/-- Galí (2015), eqs. (3), (12) and (13), pp. 54 and 58: the log-linear Euler equation (3)
together with goods-market clearing `Y_t = C_t` implies the Euler equation in output (13). -/
theorem eulerOutput_of_eulerLogLinear {σ ρ ρz : ℝ} {Y C y c i infl z : ℕ → Ω → ℝ}
    (hclear : ∀ t, Y t = C t) (hy : ∀ t ω, y t ω = Real.log (Y t ω))
    (hc : ∀ t ω, c t ω = Real.log (C t ω)) (h3 : EulerLogLinear 𝔼 σ ρ ρz c i infl z) :
    DIS.EulerOutput 𝔼 σ ρ ρz y i infl z :=
  (eulerOutput_iff_of_clearing 𝔼 hclear hy hc).2 h3

/-- Galí (2015), eq. (13), p. 58 (**exact under perfect foresight**): the nonlinear Euler
equation at every date, `π_{t+1} = p_{t+1} − p_t` and an AR(1) preference shifter give
exactly the Euler equation in output (13) for `y = c`, i.e. under goods-market clearing
`Y_t = C_t` (see `eulerOutput_iff_of_clearing`). -/
theorem pf_eulerEq_imp_eulerOutput {σ ρ ρz : ℝ} (hσ : σ ≠ 0) {i c p z infl : ℕ → Unit → ℝ}
    (heul : ∀ t, EulerEq perfectForesight (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω))
      (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (p t ω))
      (fun t ω => Real.exp (z t ω)) t)
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t) (hz : ∀ t, z (t + 1) = ρz • z t) :
    DIS.EulerOutput perfectForesight σ ρ ρz c i infl z :=
  pf_eulerEq_imp_eulerLogLinear hσ heul hinfl hz

/-! ### The production side of eq. (14) -/

/-- Galí (2015), p. 59 (**exact**): with firms forming a measure space `(F, μ)`, production
`Y(i) = A N(i)^{1−α}` (eq. (5)), output on the demand schedule `Y(i) = (P(i)/P)^{−ε} Y` and
aggregate employment `N = ∫ N(i) di`, one has exactly
`(1 − α) log N = log Y − log A + d`, with the dispersion term
`d = (1 − α) log ∫ (P(i)/P)^{−ε/(1−α)} di`. Here `P > 0` is any aggregate price level. -/
theorem employment_log_identity {F : Type*} [MeasurableSpace F] {μ : Measure F}
    {α ε A Y P : ℝ} {Pi Yi Ni : F → ℝ} (hα : α < 1) (hA : 0 < A) (hY : 0 < Y) (hP : 0 < P)
    (hPi : ∀ i, 0 < Pi i) (hN : ∀ i, 0 ≤ Ni i)
    (hdem : ∀ i, Yi i = (Pi i / P) ^ (-ε) * Y) (hprod : ∀ i, Yi i = A * Ni i ^ (1 - α))
    (hD : 0 < ∫ i, (Pi i / P) ^ (-ε / (1 - α)) ∂μ) :
    (1 - α) * Real.log (∫ i, Ni i ∂μ)
      = Real.log Y - Real.log A + (1 - α) * Real.log (∫ i, (Pi i / P) ^ (-ε / (1 - α)) ∂μ) := by
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  have hpt : ∀ i, Ni i = (Y / A) ^ (1 - α)⁻¹ * (Pi i / P) ^ (-ε / (1 - α)) := by
    intro i
    have ha : 0 < Pi i / P := div_pos (hPi i) hP
    have h1 : Ni i ^ (1 - α) = (Pi i / P) ^ (-ε) * (Y / A) := by
      have := (hdem i).symm.trans (hprod i)
      field_simp
      linarith
    rw [← Real.rpow_rpow_inv (hN i) hsub, h1, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul ha.le, div_eq_mul_inv (-ε), mul_comm]
  simp_rw [hpt]
  rw [integral_const_mul, Real.log_mul (by positivity) hD.ne', Real.log_rpow (by positivity),
    Real.log_div hY.ne' hA.ne']
  field_simp

end Gali.BasicNewKeynesianModel.Household
