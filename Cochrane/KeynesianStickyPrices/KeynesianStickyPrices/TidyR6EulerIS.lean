/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6HouseholdMeasureTVC
import KeynesianStickyPrices.FullModel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The household problem behind the IS curve (17.15)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4, p. 407, eqs.
(17.15)–(17.16), and Chapter 5, §5.1, p. 118: "To derive (5.1), start from consumer first-order
conditions, `1 = E_t[β(C_{t+1}/C_t)^{−γ}(1 + i_t)P_t/P_{t+1}]`. Linearize and approximate to
`E_t(c_{t+1} − c_t) = −σδ + σ(i_t − E_tπ_{t+1})` where `c_t = log C_t`, `σ = 1/γ` and
`δ = −log β`. Suppressing constants and with consumption equal to output `c_t = x_t` we get
(5.1)", which is (17.15).

The household problem is the one of the Chapter 2 model (restated in TidyR6HouseholdMeasure and
TidyR6HouseholdMeasureTVC): it maximises `E ∑ βᵗu(C_t)` subject to
`B_{t−1} + P_ty = P_tC_t + P_ts_t + Q_tB_t`, `B_t ≥ 0`, on a genuine probability space whose
information may grow forever. Its income (sales of output, net of taxes) enters through `y` and
`s`, which the household takes as given.

## The variables

Output is `Y_t = Ȳe^{x_t}` (`outp`; `x` is the log output gap), the price level is
`P_t = exp(p_{−1} + ∑_{s≤t} π_s)` (`price`; `π` is inflation), and the bond price is
`Q_t = βe^{−i_t}` (`bondPrice`), so `i_t` is the deviation of the log gross nominal rate from
`δ = −log β`. Utility is CRRA, `u′(C) = C^{−γ}`, on `C ≥ a > 0`; `crraU` is a concrete concave,
increasing, everywhere differentiable utility with this marginal utility (`crraMU`), so the
hypotheses below are satisfiable.

## Main results

* `expEuler_eq_book`: the integrand `exp z_{t+1}`, `z_{t+1} = i_t − γ(x_{t+1} − x_t) − π_{t+1}`
  (`sdfGap`), is the book's `β(C_{t+1}/C_t)^{−γ}(1 + i_t)P_t/P_{t+1}` with `1 + i_t = 1/Q_t`.
* `euler_iff_expEuler`: the household's Euler equation `Q_tu′(C_t)/P_t = βE_t[u′(C_{t+1})/P_{t+1}]`
  holds almost surely iff the exact nonlinear form `E_t exp z_{t+1} = 1` does.
* `expEuler_iff_IS`, `euler_iff_IS`: **exactly**, `E_t exp z_{t+1} = 1` iff
  `x_t = E_tx_{t+1} − σ(i_t − E_tπ_{t+1}) + u_{x,t}` with the explicit remainder
  `u_{x,t} = −σE_t[expRem z_{t+1}]` (`isRem`), `expRem z = e^z − 1 − z`. The remainder is
  second order: `expRem ≥ 0`, `expRem 0 = 0`, `expRem′(0) = 0` (`hasDerivAt_expRem_zero`), and
  `−σE_t z²_{t+1} ≤ u_{x,t} ≤ 0` when `|z_{t+1}| ≤ 1` (`isRem_bounds`).
* `IS_of_optimal` (**necessity**) and `optimal_of_IS` (**sufficiency**, with the transversality
  condition), `optimal_iff_IS`: the household plan `C = Y` is optimal iff (17.15)–(17.16) hold at
  every date with that remainder (`ISM`, `FisherM`).
* Finite trees: `Tree.tree_optimal_iff_IS`: on a finite event tree, optimality is equivalent to the
  project's `FullModel.IS` and `FullModel.Fisher` for the tree's core expectation system, in every
  state, with `u_x` the remainder.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6EulerIS

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6HouseholdMeasureTVC

/-! ### CRRA utility with a consumption floor -/

/-- Cochrane (2023), p. 118 (`u′(C) = C^{−γ}`): CRRA marginal utility, frozen below the floor `a`,
`u′(C) = max(C, a)^{−γ}`. -/
noncomputable def crraMU (γ a x : ℝ) : ℝ := (max x a) ^ (-γ)

/-- Cochrane (2023), p. 118: a CRRA utility defined on all of `ℝ`, `u(C) = ∫_a^C u′`. -/
noncomputable def crraU (γ a x : ℝ) : ℝ := ∫ s in a..x, crraMU γ a s

/-- Cochrane (2023), p. 118: above the floor the marginal utility is `C^{−γ}`. -/
theorem crraMU_of_le {γ a x : ℝ} (h : a ≤ x) : crraMU γ a x = x ^ (-γ) := by
  simp only [crraMU, max_eq_left h]

/-- Cochrane (2023), p. 118: marginal utility is positive. -/
theorem crraMU_pos {γ a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < crraMU γ a x :=
  Real.rpow_pos_of_pos (lt_max_of_lt_right ha) _

/-- Cochrane (2023), p. 118: marginal utility is continuous. -/
theorem continuous_crraMU {γ a : ℝ} (ha : 0 < a) : Continuous (crraMU γ a) :=
  (continuous_id.max continuous_const).rpow_const fun _ =>
    Or.inl (ne_of_gt (lt_max_of_lt_right ha))

/-- Cochrane (2023), p. 118: `u′` is the derivative of `u` everywhere. -/
theorem hasDerivAt_crraU {γ a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (crraU γ a) (crraMU γ a x) x :=
  ((continuous_crraMU ha).integral_hasStrictDerivAt a x).hasDerivAt

/-- Cochrane (2023), p. 118: marginal utility is decreasing (`γ ≥ 0`). -/
theorem antitone_crraMU {γ a : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) : Antitone (crraMU γ a) :=
  fun _ _ hxy => Real.rpow_le_rpow_of_nonpos (lt_max_of_lt_right ha) (max_le_max hxy le_rfl)
    (by linarith)

/-- Cochrane (2023), p. 118: the utility is concave. -/
theorem concaveOn_crraU {γ a : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) :
    ConcaveOn ℝ Set.univ (crraU γ a) := by
  refine AntitoneOn.concaveOn_of_deriv convex_univ
    (continuous_iff_continuousAt.2 fun x => (hasDerivAt_crraU ha x).continuousAt).continuousOn
    (fun x _ => (hasDerivAt_crraU ha x).differentiableAt.differentiableWithinAt) ?_
  intro x _ y _ hxy
  rw [(hasDerivAt_crraU ha x).deriv, (hasDerivAt_crraU ha y).deriv]
  exact antitone_crraMU ha hγ hxy

/-- Cochrane (2023), p. 118: the utility is increasing. -/
theorem monotone_crraU {γ a : ℝ} (ha : 0 < a) : Monotone (crraU γ a) :=
  monotone_of_deriv_nonneg (fun x => (hasDerivAt_crraU ha x).differentiableAt) fun x => by
    rw [(hasDerivAt_crraU ha x).deriv]
    exact (crraMU_pos ha x).le

/-! ### The exponential remainder -/

/-- Cochrane (2023), p. 118 ("Linearize and approximate"): the remainder of the linearisation of
the exponential, `e^z − 1 − z`. -/
noncomputable def expRem (z : ℝ) : ℝ := Real.exp z - 1 - z

/-- Cochrane (2023), p. 118: the remainder is nonnegative. -/
theorem expRem_nonneg (z : ℝ) : 0 ≤ expRem z := by
  unfold expRem
  linarith [Real.add_one_le_exp z]

/-- Cochrane (2023), p. 118: the remainder vanishes at the steady state. -/
theorem expRem_zero : expRem 0 = 0 := by simp [expRem]

/-- Cochrane (2023), p. 118: the remainder has zero derivative at the steady state (the
linearisation is the exact derivative). -/
theorem hasDerivAt_expRem_zero : HasDerivAt expRem 0 0 := by
  have h := ((Real.hasDerivAt_exp 0).sub_const 1).sub (hasDerivAt_id (0 : ℝ))
  simp only [Real.exp_zero, sub_self] at h
  exact h

/-- Cochrane (2023), p. 118: the remainder is second order, `0 ≤ e^z − 1 − z ≤ z²` for
`|z| ≤ 1`. -/
theorem expRem_le_sq {z : ℝ} (h : |z| ≤ 1) : expRem z ≤ z ^ 2 :=
  (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le h)

/-! ### The variables of the log-linear model -/

variable {Ω : Type*}

/-- Cochrane (2023), p. 118 ("consumption equal to output", `c_t = x_t` in logs): output and
consumption `Y_t = Ȳe^{x_t}`. -/
noncomputable def outp (Ybar : ℝ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => Ybar * Real.exp (x t ω)

/-- Cochrane (2023), p. 407: the log price level `p_t = p_{−1} + ∑_{s≤t} π_s`. -/
def logPrice (pm : Ω → ℝ) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => pm ω + ∑ s ∈ Finset.range (t + 1), π s ω

/-- Cochrane (2023), p. 118: the price level `P_t = e^{p_t}`. -/
noncomputable def price (pm : Ω → ℝ) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => Real.exp (logPrice pm π t ω)

/-- Cochrane (2023), p. 118: the bond price `Q_t = 1/(1 + i_t^{gross}) = βe^{−i_t}`, so `i_t` is
the log nominal rate less `δ = −log β`. -/
noncomputable def bondPrice (β : ℝ) (i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => β * Real.exp (-(i t ω))

/-- Cochrane (2023), p. 118: the log of the household's discounted real return,
`z_{t+1} = i_t − γ(x_{t+1} − x_t) − π_{t+1}`. -/
def sdfGap (γ : ℝ) (i x π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => i t ω - γ * (x (t + 1) ω - x t ω) - π (t + 1) ω

/-- Cochrane (2023), p. 407: inflation is the change in the log price level,
`p_{t+1} = p_t + π_{t+1}`. -/
theorem logPrice_succ (pm : Ω → ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    logPrice pm π (t + 1) ω = logPrice pm π t ω + π (t + 1) ω := by
  simp only [logPrice, Finset.sum_range_succ (n := t + 1)]
  ring

/-- Cochrane (2023), p. 118: the book's integrand. With `1 + i_t = 1/Q_t`,
`β(Y_{t+1}/Y_t)^{−γ}(1 + i_t)P_t/P_{t+1} = exp z_{t+1}`. -/
theorem expEuler_eq_book {β γ Ybar : ℝ} (hβ : 0 < β) (hY : 0 < Ybar) (i x π : ℕ → Ω → ℝ)
    (pm : Ω → ℝ) (t : ℕ) (ω : Ω) :
    β * (outp Ybar x (t + 1) ω / outp Ybar x t ω) ^ (-γ) * (bondPrice β i t ω)⁻¹ *
      (price pm π t ω / price pm π (t + 1) ω) = Real.exp (sdfGap γ i x π t ω) := by
  have hq : outp Ybar x (t + 1) ω / outp Ybar x t ω = Real.exp (x (t + 1) ω - x t ω) := by
    simp only [outp, Real.exp_sub]
    field_simp
  rw [hq, ← Real.exp_mul]
  simp only [bondPrice, price, logPrice_succ, sdfGap, Real.exp_add, Real.exp_neg,
    Real.exp_sub]
  have h1 := Real.exp_pos (i t ω)
  have h2 := Real.exp_pos (logPrice pm π t ω)
  have h3 := Real.exp_pos (π (t + 1) ω)
  have h4 := Real.exp_pos (γ * (x (t + 1) ω - x t ω))
  rw [mul_comm (x (t + 1) ω - x t ω) (-γ), neg_mul, Real.exp_neg]
  field_simp

/-! ### The exact nonlinear Euler equation and its log-linearisation -/

variable [MeasurableSpace Ω]

/-- Cochrane (2023), eq. (17.16), p. 407: the real rate defined by the Fisher equation,
`r_t = i_t − E_tπ_{t+1}`. -/
noncomputable def realRate (S : MeasExpectationSystem Ω) (i π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => i t - S.E t (π (t + 1))

/-- Cochrane (2023), eq. (17.15), p. 407 and p. 118: the explicit remainder of the log-linear IS
curve, `u_{x,t} = −σE_t[e^{z_{t+1}} − 1 − z_{t+1}]` with `σ = 1/γ`. -/
noncomputable def isRem (S : MeasExpectationSystem Ω) (γ : ℝ) (i x π : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω => -γ⁻¹ * S.E t (fun ω => expRem (sdfGap γ i x π t ω)) ω

/-- Cochrane (2023), eq. (17.15), p. 407, on a probability space, at date `t`: almost surely
`x_t = E_tx_{t+1} − σr_t + u_{x,t}`. -/
def ISM (S : MeasExpectationSystem Ω) (σ : ℝ) (ux r x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  x t =ᵐ[S.μ] S.E t (x (t + 1)) - σ • r t + ux t

/-- Cochrane (2023), eq. (17.16), p. 407, on a probability space, at date `t`: almost surely
`i_t = r_t + E_tπ_{t+1}`. -/
def FisherM (S : MeasExpectationSystem Ω) (i r π : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  i t =ᵐ[S.μ] r t + S.E t (π (t + 1))

/-- Cochrane (2023), eq. (17.16), p. 407: the real rate `realRate` satisfies the Fisher
equation. -/
theorem fisherM_realRate (S : MeasExpectationSystem Ω) (i π : ℕ → Ω → ℝ) (t : ℕ) :
    FisherM S i (realRate S i π) π t :=
  Eventually.of_forall fun ω => by simp [realRate]

variable {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), p. 118 ("Linearize and approximate"), **exactly**: given integrable
variables with `i_t`, `x_t` known at `t` and `γ ≠ 0`, the nonlinear Euler equation
`E_t exp z_{t+1} = 1` holds almost surely iff the IS curve (17.15) holds almost surely with the
real rate (17.16) and the remainder `u_{x,t} = −σE_t[expRem z_{t+1}]`. -/
theorem expEuler_iff_IS {γ : ℝ} (hγ : γ ≠ 0) {i x π : ℕ → Ω → ℝ} {t : ℕ}
    (hit : StronglyMeasurable[S.𝓕 t] (i t)) (hxt : StronglyMeasurable[S.𝓕 t] (x t))
    (hii : Integrable (i t) S.μ) (hxi : Integrable (x t) S.μ)
    (hx1 : Integrable (x (t + 1)) S.μ) (hπ1 : Integrable (π (t + 1)) S.μ)
    (hexp : Integrable (fun ω => Real.exp (sdfGap γ i x π t ω)) S.μ) :
    (∀ᵐ ω ∂S.μ, S.E t (fun ω => Real.exp (sdfGap γ i x π t ω)) ω = 1) ↔
      ISM S γ⁻¹ (isRem S γ i x π) (realRate S i π) x t := by
  set z := sdfGap γ i x π t with hzdef
  have hK : Integrable (fun ω => i t ω + γ * x t ω) S.μ := hii.add (hxi.const_mul γ)
  have hO : Integrable (γ • x (t + 1) + π (t + 1)) S.μ := (hx1.smul γ).add hπ1
  have ez : z = (fun ω => i t ω + γ * x t ω) - (γ • x (t + 1) + π (t + 1)) := by
    funext ω
    simp only [hzdef, sdfGap, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hz : Integrable z S.μ := ez ▸ hK.sub hO
  have hR : Integrable (fun ω => expRem (z ω)) S.μ :=
    ((hexp.sub (integrable_const 1)).sub hz).congr (Eventually.of_forall fun ω => by
      simp only [Pi.sub_apply, expRem])
  have e1 : (fun ω => Real.exp (z ω)) = ((fun _ => (1 : ℝ)) + z) + fun ω => expRem (z ω) := by
    funext ω
    simp only [Pi.add_apply, expRem]
    ring
  have hknown : S.E t (fun ω => i t ω + γ * x t ω) = fun ω => i t ω + γ * x t ω :=
    S.E_of_stronglyMeasurable (hit.add (hxt.const_mul γ)) hK
  have hdec : ∀ᵐ ω ∂S.μ, S.E t (fun ω => Real.exp (z ω)) ω =
      1 + (i t ω + γ * x t ω - (γ * S.E t (x (t + 1)) ω + S.E t (π (t + 1)) ω)) +
        S.E t (fun ω => expRem (z ω)) ω := by
    rw [e1]
    filter_upwards [S.E_add ((integrable_const 1).add hz) hR t,
      S.E_add (integrable_const 1) hz t, S.E_sub hK hO t, S.E_add (hx1.smul γ) hπ1 t,
      S.E_smul γ (x (t + 1)) t] with ω h1 h2 h3 h4 h5
    have hEz : S.E t z ω = i t ω + γ * x t ω - (γ * S.E t (x (t + 1)) ω + S.E t (π (t + 1)) ω) := by
      rw [ez, h3, Pi.sub_apply, hknown, h4, Pi.add_apply, h5, Pi.smul_apply, smul_eq_mul]
    rw [h1, Pi.add_apply, h2, Pi.add_apply, S.E_const t 1, hEz]
  have hg : γ⁻¹ * γ = 1 := inv_mul_cancel₀ hγ
  constructor
  · intro h
    filter_upwards [h, hdec] with ω h1 h2
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, realRate, isRem]
    rw [← hzdef]
    linear_combination (-γ⁻¹) * h2 + γ⁻¹ * h1 - (x t ω - S.E t (x (t + 1)) ω) * hg
  · intro h
    filter_upwards [h, hdec] with ω h1 h2
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, realRate, isRem] at h1
    rw [← hzdef] at h1
    have h3 : γ * γ⁻¹ = 1 := mul_inv_cancel₀ hγ
    rw [h2]
    linear_combination γ * h1 + (S.E t (π (t + 1)) ω - i t ω -
      S.E t (fun ω => expRem (z ω)) ω) * h3

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: with CRRA marginal utility, `u′(Y_t)/P_t = Ȳ^{−γ}e^{−γx_t − p_t}`. -/
theorem margUtil_eq {γ a Ybar : ℝ} (hY : 0 < Ybar) {u' : ℝ → ℝ}
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x π : ℕ → Ω → ℝ} {pm : Ω → ℝ} {t : ℕ} {ω : Ω}
    (ha : a ≤ outp Ybar x t ω) :
    u' (outp Ybar x t ω) / price pm π t ω =
      Ybar ^ (-γ) * Real.exp (-(γ * x t ω) - logPrice pm π t ω) := by
  rw [hu' _ ha]
  simp only [outp, price]
  rw [Real.mul_rpow hY.le (Real.exp_pos _).le, ← Real.exp_mul, Real.exp_sub, mul_comm (x t ω),
    neg_mul]
  ring

/-- Cochrane (2023), p. 118: the household's Euler equation
`Q_tu′(Y_t)/P_t = βE_t[u′(Y_{t+1})/P_{t+1}]` holds almost surely iff the exact nonlinear Euler
equation `E_t exp z_{t+1} = 1` does (CRRA marginal utility above the floor `a`, output above the
floor, the multiplier `e^{i_t + γx_t + p_t}` known at `t`, both payoffs integrable). -/
theorem euler_iff_expEuler {β γ a Ybar : ℝ} (hβ : 0 < β) (hY : 0 < Ybar) {u' : ℝ → ℝ}
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {i x π : ℕ → Ω → ℝ} {pm : Ω → ℝ} {t : ℕ}
    (ha : ∀ᵐ ω ∂S.μ, a ≤ outp Ybar x t ω) (ha1 : ∀ᵐ ω ∂S.μ, a ≤ outp Ybar x (t + 1) ω)
    (hm : StronglyMeasurable[S.𝓕 t] fun ω => Real.exp (i t ω + γ * x t ω + logPrice pm π t ω))
    (hW : Integrable (fun ω => u' (outp Ybar x (t + 1) ω) / price pm π (t + 1) ω) S.μ)
    (hexp : Integrable (fun ω => Real.exp (sdfGap γ i x π t ω)) S.μ) :
    ((fun ω => bondPrice β i t ω * (u' (outp Ybar x t ω) / price pm π t ω)) =ᵐ[S.μ]
        β • S.E t (fun ω => u' (outp Ybar x (t + 1) ω) / price pm π (t + 1) ω)) ↔
      ∀ᵐ ω ∂S.μ, S.E t (fun ω => Real.exp (sdfGap γ i x π t ω)) ω = 1 := by
  set W : Ω → ℝ := fun ω => u' (outp Ybar x (t + 1) ω) / price pm π (t + 1) ω with hWdef
  set m : Ω → ℝ := fun ω => Ybar ^ γ * Real.exp (i t ω + γ * x t ω + logPrice pm π t ω)
    with hmdef
  have hYY : Ybar ^ γ * Ybar ^ (-γ) = 1 := by
    rw [Real.rpow_neg hY.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hY γ).ne']
  have hmW : (m * W) =ᵐ[S.μ] fun ω => Real.exp (sdfGap γ i x π t ω) := by
    filter_upwards [ha1] with ω h
    simp only [Pi.mul_apply, hmdef, hWdef, margUtil_eq hY hu' h, sdfGap, logPrice_succ]
    rw [mul_mul_mul_comm, hYY, one_mul, ← Real.exp_add]
    ring_nf
  have hmm : StronglyMeasurable[S.𝓕 t] m := hm.const_mul _
  have hpo : S.E t (m * W) =ᵐ[S.μ] m * S.E t W :=
    condExp_mul_of_stronglyMeasurable_left hmm (hexp.congr hmW.symm) hW
  have hE : S.E t (fun ω => Real.exp (sdfGap γ i x π t ω)) =ᵐ[S.μ] m * S.E t W :=
    (S.E_congr hmW.symm t).trans hpo
  have hlhs : ∀ᵐ ω ∂S.μ, bondPrice β i t ω * (u' (outp Ybar x t ω) / price pm π t ω) =
      β * (m ω)⁻¹ := by
    filter_upwards [ha] with ω h
    rw [margUtil_eq hY hu' h]
    simp only [bondPrice, hmdef, mul_inv, Real.rpow_neg hY.le, ← Real.exp_neg]
    rw [mul_mul_mul_comm, ← Real.exp_add]
    ring_nf
  have hmpos : ∀ ω, 0 < m ω := fun ω =>
    mul_pos (Real.rpow_pos_of_pos hY γ) (Real.exp_pos _)
  constructor
  · intro h
    filter_upwards [h, hE, hlhs] with ω h1 h2 h3
    rw [h2, Pi.mul_apply]
    rw [h3, Pi.smul_apply, smul_eq_mul] at h1
    have := (hmpos ω).ne'
    field_simp at h1
    linarith
  · intro h
    filter_upwards [h, hE, hlhs] with ω h1 h2 h3
    rw [h3, Pi.smul_apply, smul_eq_mul]
    rw [h2, Pi.mul_apply] at h1
    have := (hmpos ω).ne'
    field_simp
    linarith

/-- Cochrane (2023), p. 118: the remainder is second order: `−σE_t z²_{t+1} ≤ u_{x,t} ≤ 0` almost
surely when `|z_{t+1}| ≤ 1` (`γ > 0`). -/
theorem isRem_bounds {γ : ℝ} (hγ : 0 < γ) {i x π : ℕ → Ω → ℝ} {t : ℕ}
    (hzm : AEStronglyMeasurable (sdfGap γ i x π t) S.μ)
    (hz1 : ∀ᵐ ω ∂S.μ, |sdfGap γ i x π t ω| ≤ 1) :
    ∀ᵐ ω ∂S.μ, -γ⁻¹ * S.E t (fun ω => sdfGap γ i x π t ω ^ 2) ω ≤ isRem S γ i x π t ω ∧
      isRem S γ i x π t ω ≤ 0 := by
  set z := sdfGap γ i x π t
  have hRm : AEStronglyMeasurable (fun ω => expRem (z ω)) S.μ :=
    ((Real.continuous_exp.sub continuous_const).sub continuous_id).comp_aestronglyMeasurable hzm
  have hRb : ∀ᵐ ω ∂S.μ, ‖expRem (z ω)‖ ≤ 1 := by
    filter_upwards [hz1] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (expRem_nonneg _)]
    refine (expRem_le_sq h).trans ?_
    nlinarith [abs_nonneg (z ω), sq_abs (z ω)]
  have hRi : Integrable (fun ω => expRem (z ω)) S.μ := Integrable.of_bound hRm 1 hRb
  have hqi : Integrable (fun ω => z ω ^ 2) S.μ := by
    refine Integrable.of_bound (hzm.pow 2) 1 ?_
    filter_upwards [hz1] with ω h
    rw [Real.norm_eq_abs, abs_pow]
    nlinarith [abs_nonneg (z ω)]
  have hlo := S.E_mono (integrable_zero _ _ _) hRi
    (Eventually.of_forall fun ω => expRem_nonneg (z ω)) t
  have hhi := S.E_mono hRi hqi (hz1.mono fun ω h => expRem_le_sq h) t
  rw [S.E_zero] at hlo
  filter_upwards [hlo, hhi] with ω h1 h2
  have hg := inv_pos.2 hγ
  simp only [Pi.zero_apply] at h1
  refine ⟨?_, ?_⟩ <;> simp only [isRem] <;> nlinarith

/-! ### The household's regularity -/

variable (S) in
/-- Cochrane (2023), §17.4, p. 407: the regularity of the log-linear variables used throughout:
`x`, `i`, `π` adapted and essentially bounded at every date, `p_{−1}` known at date `0` and
essentially bounded. -/
def LogRegular (x i π : ℕ → Ω → ℝ) (pm : Ω → ℝ) : Prop :=
  StronglyAdapted S.𝓕 x ∧ StronglyAdapted S.𝓕 i ∧ StronglyAdapted S.𝓕 π ∧
    StronglyMeasurable[S.𝓕 0] pm ∧ (∀ t, BddAt S (x t)) ∧ (∀ t, BddAt S (i t)) ∧
      (∀ t, BddAt S (π t)) ∧ BddAt S pm

/-- Cochrane (2023), p. 407: the log price level is known at `t`. -/
theorem logPrice_sm {x i π : ℕ → Ω → ℝ} {pm : Ω → ℝ} (h : LogRegular S x i π pm) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (logPrice pm π t) := by
  obtain ⟨-, -, hπ, hpm, -⟩ := h
  have hs : Measurable[S.𝓕 t] fun ω => ∑ s ∈ Finset.range (t + 1), π s ω :=
    Finset.measurable_fun_sum _ fun s hs =>
      ((hπ s).mono (S.𝓕.mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)))).measurable
  exact ((hpm.mono (S.𝓕.mono (Nat.zero_le t))).measurable.add hs).stronglyMeasurable

/-- Cochrane (2023), p. 407: the log price level is essentially bounded at every date. -/
theorem logPrice_bdd {x i π : ℕ → Ω → ℝ} {pm : Ω → ℝ} (h : LogRegular S x i π pm) (t : ℕ) :
    BddAt S (logPrice pm π t) := by
  obtain ⟨-, -, -, -, -, -, hπ, hpm⟩ := h
  induction t with
  | zero =>
    have e : logPrice pm π 0 = fun ω => pm ω + π 0 ω := by
      funext ω
      simp [logPrice]
    rw [e]
    exact hpm.add (hπ 0)
  | succ n ih =>
    have e : logPrice pm π (n + 1) = fun ω => logPrice pm π n ω + π (n + 1) ω := by
      funext ω
      exact logPrice_succ pm π n ω
    rw [e]
    exact ih.add (hπ (n + 1))

/-- Cochrane (2023), p. 118: the price level is adapted. -/
theorem price_adapted {x i π : ℕ → Ω → ℝ} {pm : Ω → ℝ} (h : LogRegular S x i π pm) :
    StronglyAdapted S.𝓕 (price pm π) := fun t =>
  (Real.continuous_exp.measurable.comp (logPrice_sm h t).measurable).stronglyMeasurable

/-- Cochrane (2023), p. 118: output is adapted. -/
theorem outp_adapted {x i π : ℕ → Ω → ℝ} {pm : Ω → ℝ} (h : LogRegular S x i π pm) (Ybar : ℝ) :
    StronglyAdapted S.𝓕 (outp Ybar x) := fun t =>
  ((Real.continuous_exp.measurable.comp (h.1 t).measurable).const_mul Ybar).stronglyMeasurable

/-- Cochrane (2023), p. 118: the bond price is known at `t`. -/
theorem bondPrice_sm {x i π : ℕ → Ω → ℝ} {pm : Ω → ℝ} (h : LogRegular S x i π pm) (β : ℝ)
    (t : ℕ) : StronglyMeasurable[S.𝓕 t] (bondPrice β i t) :=
  ((Real.continuous_exp.measurable.comp (h.2.1 t).measurable.neg).const_mul β).stronglyMeasurable

/-- Cochrane (2023), p. 118: a process adapted and essentially bounded at a date is integrable
there. -/
theorem integrable_of_reg {f : ℕ → Ω → ℝ} (hf : StronglyAdapted S.𝓕 f) (hb : ∀ t, BddAt S (f t))
    (t : ℕ) : Integrable (f t) S.μ :=
  (hb t).integrable ((hf t).mono (S.𝓕.le t)).aestronglyMeasurable

/-- Cochrane (2023), p. 21 and p. 118: the household's `EulerRegular` holds at every date. -/
theorem eulerRegular_of {x i π : ℕ → Ω → ℝ} {pm : Ω → ℝ} (h : LogRegular S x i π pm)
    (β Ybar : ℝ) (t : ℕ) : EulerRegular S (price pm π) (bondPrice β i) (outp Ybar x) t := by
  have hx := h.2.2.2.2.1
  have hi := h.2.2.2.2.2.1
  have hc : Continuous fun y => Ybar * Real.exp y := continuous_const.mul Real.continuous_exp
  have hq : Continuous fun y => β * Real.exp (-y) :=
    continuous_const.mul (Real.continuous_exp.comp continuous_neg)
  have hp : Continuous fun y => (Real.exp y)⁻¹ :=
    Real.continuous_exp.inv₀ fun y => (Real.exp_pos y).ne'
  exact ⟨BddAt.comp hc (hx t), BddAt.comp hc (hx (t + 1)), BddAt.comp hq (hi t),
    BddAt.comp hp (logPrice_bdd h t), BddAt.comp hp (logPrice_bdd h (t + 1))⟩

/-- Cochrane (2023), p. 118: `z_{t+1}` is essentially bounded and measurable. -/
theorem sdfGap_reg {γ : ℝ} {x i π : ℕ → Ω → ℝ} {pm : Ω → ℝ} (h : LogRegular S x i π pm)
    (t : ℕ) : BddAt S (sdfGap γ i x π t) ∧ AEStronglyMeasurable (sdfGap γ i x π t) S.μ := by
  obtain ⟨hxa, hia, hπa, -, hxb, hib, hπb, -⟩ := h
  refine ⟨?_, ?_⟩
  · have := ((hib t).add (((BddAt.const (S := S) γ).mul ((hxb (t + 1)).add
      (hxb t).neg)).neg)).add (hπb (t + 1)).neg
    have e : sdfGap γ i x π t = fun ω => i t ω + -(γ * (x (t + 1) ω + -x t ω)) + -π (t + 1) ω := by
      funext ω
      simp only [sdfGap]
      ring
    rw [e]
    exact this
  · have m1 : Measurable (i t) := ((hia t).mono (S.𝓕.le t)).measurable
    have m2 : Measurable (x (t + 1)) := ((hxa (t + 1)).mono (S.𝓕.le (t + 1))).measurable
    have m3 : Measurable (x t) := ((hxa t).mono (S.𝓕.le t)).measurable
    have m4 : Measurable (π (t + 1)) := ((hπa (t + 1)).mono (S.𝓕.le (t + 1))).measurable
    exact ((m1.sub ((m2.sub m3).const_mul γ)).sub m4).aestronglyMeasurable

/-- Cochrane (2023), p. 21: the discounted marginal utility of a dollar, `u′(Y_n)/P_n`, is
integrable at every date. -/
theorem margUtil_integrable_at {x i π : ℕ → Ω → ℝ} {pm : Ω → ℝ} (h : LogRegular S x i π pm)
    {u' : ℝ → ℝ} (hu'c : Continuous u') (β Ybar : ℝ) (n : ℕ) :
    Integrable (fun ω => u' (outp Ybar x n ω) / price pm π n ω) S.μ := by
  have hreg := eulerRegular_of h β Ybar n
  have hb := (BddAt.comp hu'c hreg.1).mul hreg.2.2.2.1
  refine (show BddAt S (fun ω => u' (outp Ybar x n ω) / price pm π n ω) by
    simpa [div_eq_mul_inv] using hb).integrable ?_
  exact (((hu'c.measurable.comp (outp_adapted h Ybar n).measurable).div
    (price_adapted h n).measurable).stronglyMeasurable.mono (S.𝓕.le n)).aestronglyMeasurable

/-- Cochrane (2023), p. 118 and eqs. (17.15)–(17.16), p. 407, **exactly**: under `LogRegular`,
with CRRA marginal utility `u′(C) = C^{−γ}` above the floor `a` and output above the floor, the
household's Euler equation `Q_tu′(Y_t)/P_t = βE_t[u′(Y_{t+1})/P_{t+1}]` holds almost surely iff
the IS curve `x_t = E_tx_{t+1} − σr_t + u_{x,t}` does, with `r_t = i_t − E_tπ_{t+1}` and the
explicit remainder `u_{x,t} = −σE_t[expRem z_{t+1}]`. -/
theorem euler_iff_IS {β γ a Ybar : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hY : 0 < Ybar)
    {u' : ℝ → ℝ} (hu'c : Continuous u') (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ))
    {x i π : ℕ → Ω → ℝ} {pm : Ω → ℝ} (h : LogRegular S x i π pm)
    (hfl : ∀ t, ∀ᵐ ω ∂S.μ, a ≤ outp Ybar x t ω) (t : ℕ) :
    ((fun ω => bondPrice β i t ω * (u' (outp Ybar x t ω) / price pm π t ω)) =ᵐ[S.μ]
        β • S.E t (fun ω => u' (outp Ybar x (t + 1) ω) / price pm π (t + 1) ω)) ↔
      ISM S γ⁻¹ (isRem S γ i x π) (realRate S i π) x t := by
  obtain ⟨hzb, hzm⟩ := sdfGap_reg (γ := γ) h t
  have hexp : Integrable (fun ω => Real.exp (sdfGap γ i x π t ω)) S.μ :=
    (BddAt.comp Real.continuous_exp hzb).integrable
      (Real.continuous_exp.comp_aestronglyMeasurable hzm)
  have mi : Measurable[S.𝓕 t] (i t) := (h.2.1 t).measurable
  have mx : Measurable[S.𝓕 t] (x t) := (h.1 t).measurable
  have hm : StronglyMeasurable[S.𝓕 t]
      fun ω => Real.exp (i t ω + γ * x t ω + logPrice pm π t ω) :=
    (Real.continuous_exp.measurable.comp ((mi.add (mx.const_mul γ)).add
      (logPrice_sm h t).measurable)).stronglyMeasurable
  have hW := margUtil_integrable_at h hu'c β Ybar (t + 1)
  rw [euler_iff_expEuler hβ hY hu' (hfl t) (hfl (t + 1)) hm hW hexp]
  exact expEuler_iff_IS hγ.ne' (h.2.1 t) (h.1 t) (integrable_of_reg h.2.1 h.2.2.2.2.2.1 t)
    (integrable_of_reg h.1 h.2.2.2.2.1 t) (integrable_of_reg h.1 h.2.2.2.2.1 (t + 1))
    (integrable_of_reg h.2.2.1 h.2.2.2.2.2.2.1 (t + 1)) hexp

/-- Cochrane (2023), p. 118 and eq. (17.15), p. 407, **necessity**: if consuming output `Y` is
optimal for the household (utility differentiable with continuous `u′`, CRRA above the floor),
under `LogRegular` and with the household holding bonds at `t` (`B_t > 0`), the IS curve (17.15)
holds almost surely at `t` with the real rate (17.16) and the remainder `isRem`. -/
theorem IS_of_optimal {β γ a Ybar y : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hY : 0 < Ybar)
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b : ℕ → Ω → ℝ} {pm b₀ : Ω → ℝ}
    (h : LogRegular S x i π pm) (hfl : ∀ t, ∀ᵐ ω ∂S.μ, a ≤ outp Ybar x t ω)
    (hopt : Optimal S β y u (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b) {t : ℕ}
    (hb : ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω) :
    ISM S γ⁻¹ (isRem S γ i x π) (realRate S i π) x t :=
  (euler_iff_IS hβ hγ hY hu'c hu' h hfl t).1
    (euler_of_pos hβ hu hu'c hopt (price_adapted h)
      (fun _ => Eventually.of_forall fun _ => Real.exp_pos _) (bondPrice_sm h β t)
      (eulerRegular_of h β Ybar t) hb)

/-- Cochrane (2023), p. 118 and eq. (17.15), p. 407, **sufficiency**: a feasible, admissible
household plan consuming output `Y`, with concave increasing CRRA utility, `LogRegular`, integrable
marginal-utility-weighted bond positions, the IS curve (17.15) with the remainder `isRem` at every
date, and the transversality condition `β^N E[u′(Y_N)B_{N−1}/P_N] → 0`, is optimal. -/
theorem optimal_of_IS {β γ a Ybar y : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hY : 0 < Ybar)
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b : ℕ → Ω → ℝ} {pm b₀ : Ω → ℝ}
    (h : LogRegular S x i π pm) (hfl : ∀ t, ∀ᵐ ω ∂S.μ, a ≤ outp Ybar x t ω)
    (hfeas : Feasible S y (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b)
    (hadm : Admissible S β u (outp Ybar x))
    (hWb : ∀ n, Integrable (fun ω => u' (outp Ybar x n ω) * b n ω / price pm π n ω) S.μ)
    (hIS : ∀ t, ISM S γ⁻¹ (isRem S γ i x π) (realRate S i π) x t)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, u' (outp Ybar x N ω) * b N ω / price pm π N ω ∂S.μ)
      atTop (𝓝 0)) :
    Optimal S β y u (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b := by
  refine optimal_of_euler_tvc hβ hu hconc hmono hfeas hadm
    (fun _ => Eventually.of_forall fun _ => Real.exp_pos _)
    (margUtil_integrable_at h hu'c β Ybar) hWb (fun n => ?_) htvc
  filter_upwards [(euler_iff_IS hβ hγ hY hu'c hu' h hfl n).2 (hIS n)] with ω hω
  simpa using hω

/-- Cochrane (2023), p. 118 and eqs. (17.15)–(17.16), p. 407: under the hypotheses of both
directions (the household holding bonds at every date), consuming output is optimal for the
household iff the IS curve (17.15) holds at every date with the real rate (17.16) and the
explicit remainder `u_{x,t} = −σE_t[expRem z_{t+1}]`. -/
theorem optimal_iff_IS {β γ a Ybar y : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hY : 0 < Ybar)
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b : ℕ → Ω → ℝ} {pm b₀ : Ω → ℝ}
    (h : LogRegular S x i π pm) (hfl : ∀ t, ∀ᵐ ω ∂S.μ, a ≤ outp Ybar x t ω)
    (hfeas : Feasible S y (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b)
    (hadm : Admissible S β u (outp Ybar x)) (hb : ∀ t, ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω)
    (hWb : ∀ n, Integrable (fun ω => u' (outp Ybar x n ω) * b n ω / price pm π n ω) S.μ)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, u' (outp Ybar x N ω) * b N ω / price pm π N ω ∂S.μ)
      atTop (𝓝 0)) :
    Optimal S β y u (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b ↔
      ∀ t, ISM S γ⁻¹ (isRem S γ i x π) (realRate S i π) x t ∧
        FisherM S i (realRate S i π) π t :=
  ⟨fun hopt t => ⟨IS_of_optimal hβ hγ hY hu hu'c hu' h hfl hopt (hb t),
      fisherM_realRate S i π t⟩,
    fun hIS => optimal_of_IS hβ hγ hY hu hu'c hconc hmono hu' h hfl hfeas hadm hWb
      (fun t => (hIS t).1) htvc⟩

/-- Cochrane (2023), p. 118: the concrete CRRA utility `crraU` satisfies every hypothesis on `u`
used above (`γ ≥ 0`, floor `a > 0`): differentiable with continuous positive derivative,
concave, increasing, and `u′(C) = C^{−γ}` for `C ≥ a`. -/
theorem crraU_regular {γ a : ℝ} (hγ : 0 ≤ γ) (ha : 0 < a) :
    (∀ c, HasDerivAt (crraU γ a) (crraMU γ a c) c) ∧ Continuous (crraMU γ a) ∧
      (∀ c, 0 < crraMU γ a c) ∧ ConcaveOn ℝ Set.univ (crraU γ a) ∧ Monotone (crraU γ a) ∧
        ∀ c, a ≤ c → crraMU γ a c = c ^ (-γ) :=
  ⟨hasDerivAt_crraU ha, continuous_crraMU ha, crraMU_pos ha, concaveOn_crraU ha hγ,
    monotone_crraU ha, fun _ h => crraMU_of_le h⟩

/-! ### Finite event trees -/

namespace Tree

open ExpectationsFiniteTree TreeBridge Link

variable {Ω' : Type*}

/-- Cochrane (2023), eq. (17.16), p. 407, for a core expectation system: the real rate
`r_t = i_t − E_tπ_{t+1}`. -/
def coreRealRate (𝔼 : ExpectationSystem Ω') (i π : ℕ → Ω' → ℝ) : ℕ → Ω' → ℝ :=
  fun t => i t - 𝔼.E t (π (t + 1))

/-- Cochrane (2023), eq. (17.15), p. 407 and p. 118, for a core expectation system: the IS
remainder `u_{x,t} = −σE_t[expRem z_{t+1}]`. -/
noncomputable def coreIsRem (𝔼 : ExpectationSystem Ω') (γ : ℝ) (i x π : ℕ → Ω' → ℝ) :
    ℕ → Ω' → ℝ :=
  fun t => (-γ⁻¹) • 𝔼.E t (fun ω => expRem (sdfGap γ i x π t ω))

/-- Cochrane (2023), eq. (17.16), p. 407: the core real rate satisfies the project's
`FullModel.Fisher`. -/
theorem fisher_coreRealRate (𝔼 : ExpectationSystem Ω') (i π : ℕ → Ω' → ℝ) :
    FullModel.Fisher 𝔼 i (coreRealRate 𝔼 i π) π := fun t => by
  simp [coreRealRate]

variable [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω'] (T : FiniteTree Ω')

/-- Cochrane (2023), eq. (17.15), p. 407: on a finite tree, the almost-sure IS curve with the
remainder at every date is exactly the project's `FullModel.IS` for the tree's core expectation
system, with `u_x = coreIsRem` and `r = coreRealRate`, in every state. -/
theorem ISM_iff_IS (γ : ℝ) (i x π : ℕ → Ω' → ℝ) :
    (∀ t, ISM (treeSystem T) γ⁻¹ (isRem (treeSystem T) γ i x π) (realRate (treeSystem T) i π)
      x t) ↔
      FullModel.IS T.toExpectationSystem γ⁻¹ (coreIsRem T.toExpectationSystem γ i x π)
        (coreRealRate T.toExpectationSystem i π) x := by
  constructor
  · intro h t
    rw [(treeSystem T).eq_of_ae_eq (treeSystem_fullSupport T) (h t)]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, isRem, realRate,
      coreIsRem, coreRealRate, treeE]
  · intro h t
    refine Eventually.of_forall fun ω => ?_
    rw [h t]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, isRem, realRate,
      coreIsRem, coreRealRate, treeE]

/-- Cochrane (2023), §17.4, p. 407: on a finite tree, adapted variables are `LogRegular` (all
random variables are bounded). -/
theorem logRegular_tree {x i π : ℕ → Ω' → ℝ} {pm : Ω' → ℝ}
    (hx : StronglyAdapted (treeSystem T).𝓕 x) (hi : StronglyAdapted (treeSystem T).𝓕 i)
    (hπ : StronglyAdapted (treeSystem T).𝓕 π) (hpm : StronglyMeasurable[(treeSystem T).𝓕 0] pm) :
    LogRegular (treeSystem T) x i π pm :=
  ⟨hx, hi, hπ, hpm, fun _ => bddAt_tree T _, fun _ => bddAt_tree T _, fun _ => bddAt_tree T _,
    bddAt_tree T _⟩


/-- Cochrane (2023), p. 118 and eqs. (17.15)–(17.16), p. 407, **on a finite event tree**: with
the household problem posed on the tree, adapted variables, CRRA utility above the floor (output
above the floor in every state), bonds held in every state and the transversality condition,
consuming output is optimal iff the project's `FullModel.IS` and `FullModel.Fisher` hold exactly,
in every state, for the tree's core expectation system, with `u_x = coreIsRem`. -/
theorem tree_optimal_iff_IS {β γ a Ybar y : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hY : 0 < Ybar)
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b : ℕ → Ω' → ℝ} {pm b₀ : Ω' → ℝ}
    (hx : StronglyAdapted (treeSystem T).𝓕 x) (hi : StronglyAdapted (treeSystem T).𝓕 i)
    (hπ : StronglyAdapted (treeSystem T).𝓕 π) (hpm : StronglyMeasurable[(treeSystem T).𝓕 0] pm)
    (hfl : ∀ t ω, a ≤ outp Ybar x t ω)
    (hfeas : Feasible (treeSystem T) y (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b)
    (hadm : Admissible (treeSystem T) β u (outp Ybar x)) (hb : ∀ t ω, 0 < b (t + 1) ω)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, u' (outp Ybar x N ω) * b N ω / price pm π N ω
      ∂(treeSystem T).μ) atTop (𝓝 0)) :
    Optimal (treeSystem T) β y u (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b ↔
      FullModel.IS T.toExpectationSystem γ⁻¹ (coreIsRem T.toExpectationSystem γ i x π)
          (coreRealRate T.toExpectationSystem i π) x ∧
        FullModel.Fisher T.toExpectationSystem i (coreRealRate T.toExpectationSystem i π) π := by
  rw [optimal_iff_IS hβ hγ hY hu hu'c hconc hmono hu' (logRegular_tree T hx hi hπ hpm)
    (fun t => Eventually.of_forall (hfl t)) hfeas hadm (fun t => Eventually.of_forall (hb t))
    (fun _ => Integrable.of_finite) htvc, ← ISM_iff_IS]
  exact ⟨fun h => ⟨fun t => (h t).1, fisher_coreRealRate _ i π⟩,
    fun h t => ⟨h.1 t, fisherM_realRate _ i π t⟩⟩

end Tree

end Cochrane.KeynesianStickyPrices.TidyR6EulerIS
