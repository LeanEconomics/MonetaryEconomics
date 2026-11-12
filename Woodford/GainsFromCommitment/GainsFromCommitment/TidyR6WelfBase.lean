/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.ForwardSolution
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Asymptotics
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Order.Compact

/-!
# Chapter 6 welfare machinery for Chapter 7 (I): Taylor steps, CES, dispersion

Woodford (2003), *Interest and Prices*, Chapter 6, §§1–2 and §4.1 (pp. 383–405, 420–426) and
Appendix E.1–E.4 (pp. 692–699): the second-order welfare machinery that Chapter 7 uses
("the approximation to welfare of Chapter 6", Woodford (2003), p. 471, fn. 6), restated from
the Woodford Chapter 6 StabilizationWelfare project with the namespace renamed (the original
module names are kept as nested namespaces; that project's Sequences is SeqW here).
Only the declarations needed by the Chapter 7 welfare bridge are copied; proofs are verbatim.
-/

namespace Woodford.GainsFromCommitment.TidyR6WelfBase

namespace OneParamTaylor

open Filter Topology Asymptotics
/-- Woodford (2003), eq. (1.2), p. 385 (the analytic core): if `f′ = f1`, `f1′ = f2` on the
closed ball of radius `r` about `0`, and `|f2 x − f2 0| ≤ C` there, then the second-order
Taylor remainder at `0` satisfies `|f ε − (f 0 + ε f1 0 + ε²/2 f2 0)| ≤ C ε²` for `|ε| ≤ r`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem taylor2_remainder_le {f f1 f2 : ℝ → ℝ} {r C : ℝ}
    (hf : ∀ x ∈ Metric.closedBall (0 : ℝ) r, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x ∈ Metric.closedBall (0 : ℝ) r, HasDerivAt f1 (f2 x) x)
    (hC : ∀ x ∈ Metric.closedBall (0 : ℝ) r, |f2 x - f2 0| ≤ C) {ε : ℝ} (hε : |ε| ≤ r) :
    |f ε - (f 0 + ε * f1 0 + ε ^ 2 / 2 * f2 0)| ≤ C * ε ^ 2 := by
  have hr : 0 ≤ r := (abs_nonneg ε).trans hε
  have h0 : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) r := Metric.mem_closedBall_self hr
  have hC0 : 0 ≤ C := by simpa using hC 0 h0
  have hh : ∀ x ∈ Metric.closedBall (0 : ℝ) r, |f1 x - f1 0 - x * f2 0| ≤ C * |x| := by
    intro x hx
    have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun y => f1 y - f1 0 - y * f2 0) (f' := fun y => f2 y - f2 0)
      (s := Metric.closedBall 0 r) (C := C) (fun y hy => ?_) (fun y hy => ?_)
      (convex_closedBall 0 r) h0 hx
    · simpa [Real.norm_eq_abs] using key
    · have h1 := HasDerivAt.sub ((hf1 y hy).sub_const (f1 0))
        ((hasDerivAt_id y).mul_const (f2 0))
      exact (h1.congr_deriv (by simp)).hasDerivWithinAt
    · simpa [Real.norm_eq_abs] using hC y hy
  have hsub : Metric.closedBall (0 : ℝ) |ε| ⊆ Metric.closedBall (0 : ℝ) r :=
    Metric.closedBall_subset_closedBall hε
  have h0' : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) |ε| := Metric.mem_closedBall_self (abs_nonneg ε)
  have hε' : ε ∈ Metric.closedBall (0 : ℝ) |ε| := by simp
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y => f y - (f 0 + y * f1 0 + y ^ 2 / 2 * f2 0))
    (f' := fun y => f1 y - f1 0 - y * f2 0)
    (s := Metric.closedBall 0 |ε|) (C := C * |ε|) (fun y hy => ?_) (fun y hy => ?_)
    (convex_closedBall 0 |ε|) h0' hε'
  · have e : |ε| * |ε| = ε ^ 2 := by rw [abs_mul_abs_self, sq]
    simpa [Real.norm_eq_abs, mul_assoc, e] using key
  · have h1 := HasDerivAt.sub (hf y (hsub hy))
      (HasDerivAt.add (HasDerivAt.add (hasDerivAt_const y (f 0))
        ((hasDerivAt_id y).mul_const (f1 0)))
        (((hasDerivAt_pow 2 y).div_const 2).mul_const (f2 0)))
    refine (h1.congr_deriv ?_).hasDerivWithinAt
    simp only [Nat.cast_ofNat]
    ring
  · have hy' : |y| ≤ |ε| := by simpa using hy
    calc ‖f1 y - f1 0 - y * f2 0‖ ≤ C * |y| := by
          simpa [Real.norm_eq_abs] using hh y (hsub hy)
      _ ≤ C * |ε| := mul_le_mul_of_nonneg_left hy' hC0

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Woodford (2003), §1, pp. 386–389 (the use made of a second-order approximation), general
filter form: if `W_A − W_B − q = O(s³)` where the quadratic gap satisfies `q ≥ c s²` with
`c > 0`, `s → 0` and `s ≠ 0` eventually, then `W_B < W_A` eventually.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem eventually_lt_of_quadratic_gap {α : Type*} {l : Filter α} {s WA WB q : α → ℝ} {c : ℝ}
    (hs : Tendsto s l (𝓝 0)) (hc : 0 < c) (hq : ∀ᶠ a in l, c * s a ^ 2 ≤ q a)
    (hne : ∀ᶠ a in l, s a ≠ 0) (hR : (fun a => WA a - WB a - q a) =O[l] (fun a => s a ^ 3)) :
    ∀ᶠ a in l, WB a < WA a := by
  have h3 : (fun a => s a ^ 3) =o[l] (fun a => s a ^ 2) := by
    have := ((isLittleO_one_iff ℝ).2 hs).mul_isBigO (isBigO_refl (fun a => s a ^ 2) l)
    refine this.congr' (Eventually.of_forall fun a => by simp only; ring)
      (Eventually.of_forall fun a => by simp)
  have hlo := hR.trans_isLittleO h3
  filter_upwards [isLittleO_iff.1 hlo (half_pos hc), hq, hne] with a ha hqa hna
  have hp : 0 < s a ^ 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp] at ha
  have := neg_abs_le (WA a - WB a - q a)
  nlinarith

/-- Woodford (2003), §1, pp. 386–389 (welfare ranking, one-parameter form): if welfare under
policies `A` and `B` has expansions `w0 + ε w1 + ε²/2 a_X + O(ε³)` with common zeroth- and
first-order terms and `a_B < a_A`, then `A` is strictly better for every small `ε ≠ 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem welfare_ranking {WA WB : ℝ → ℝ} {w0 w1 aA aB : ℝ}
    (hA : (fun ε => WA ε - (w0 + ε * w1 + ε ^ 2 / 2 * aA)) =O[𝓝 0] (fun ε => ε ^ 3))
    (hB : (fun ε => WB ε - (w0 + ε * w1 + ε ^ 2 / 2 * aB)) =O[𝓝 0] (fun ε => ε ^ 3))
    (h : aB < aA) : ∀ᶠ ε in 𝓝[≠] 0, WB ε < WA ε := by
  refine eventually_lt_of_quadratic_gap (s := id) (q := fun ε => ε ^ 2 / 2 * (aA - aB))
    (c := (aA - aB) / 2) (tendsto_id.mono_left nhdsWithin_le_nhds) (by linarith)
    (Eventually.of_forall fun ε => by simp only [id]; nlinarith [sq_nonneg ε])
    self_mem_nhdsWithin ?_
  refine ((hA.sub hB).mono nhdsWithin_le_nhds).congr_left fun ε => ?_
  ring

/-- Woodford (2003), §1, pp. 386–389: the welfare ranking for small positive amplitudes,
`∀ᶠ ε in 𝓝[>] 0` (the shock amplitude `ε` is a positive number).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem welfare_ranking_pos {WA WB : ℝ → ℝ} {w0 w1 aA aB : ℝ}
    (hA : (fun ε => WA ε - (w0 + ε * w1 + ε ^ 2 / 2 * aA)) =O[𝓝 0] (fun ε => ε ^ 3))
    (hB : (fun ε => WB ε - (w0 + ε * w1 + ε ^ 2 / 2 * aB)) =O[𝓝 0] (fun ε => ε ^ 3))
    (h : aB < aA) : ∀ᶠ ε in 𝓝[>] 0, WB ε < WA ε :=
  (welfare_ranking hA hB h).filter_mono (nhdsWithin_mono _ fun _ hε => ne_of_gt hε)

/-- Woodford (2003), §1, pp. 386–389, and §2 (quadratic loss functions): if welfare under each
policy is `w0 + ε w1 − (k/2) ε² L_X + O(ε³)` with `k > 0` (e.g. `k = Ȳ u_c`) and the
quadratic losses satisfy `L_A < L_B`, then `W_A ε > W_B ε` for all small `ε > 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem welfare_ranking_of_loss {WA WB : ℝ → ℝ} {w0 w1 k LA LB : ℝ} (hk : 0 < k)
    (hA : (fun ε => WA ε - (w0 + ε * w1 + ε ^ 2 / 2 * (-(k * LA)))) =O[𝓝 0] (fun ε => ε ^ 3))
    (hB : (fun ε => WB ε - (w0 + ε * w1 + ε ^ 2 / 2 * (-(k * LB)))) =O[𝓝 0] (fun ε => ε ^ 3))
    (hL : LA < LB) : ∀ᶠ ε in 𝓝[>] 0, WB ε < WA ε :=
  welfare_ranking_pos hA hB (by nlinarith)

variable {Ω : Type*} [Fintype Ω] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Woodford (2003), §1, p. 385: the expectation `E[f] = ∑_ω p ω • f ω` of a (vector-valued)
random variable on a finite state space with probabilities `p`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
def expect (p : Ω → ℝ) (f : Ω → V) : V := ∑ ω, p ω • f ω

/-- Woodford (2003), §1, p. 385: over a finite state space a remainder that is `O(g)` state by
state is `O(g)` in expectation.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem isBigO_expect {α : Type*} {l : Filter α} (p : Ω → ℝ) {f : Ω → α → V} {g : α → ℝ}
    (h : ∀ ω, f ω =O[l] g) : (fun a => expect p fun ω => f ω a) =O[l] g := by
  unfold expect
  have := IsBigO.sum (s := Finset.univ) fun ω _ => (h ω).const_smul_left (p ω)
  refine this.congr_left fun a => ?_
  simp

/-- Woodford (2003), App. E, p. 693 (bookkeeping of orders): a real function tending to `0`
dominates its own higher powers, `f^{n+1} = O(f)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem pow_succ_isBigO_self {α : Type*} {l : Filter α} {f : α → ℝ} (hf : Tendsto f l (𝓝 0))
    (n : ℕ) : (fun a => f a ^ (n + 1)) =O[l] f := by
  have h1 : (fun a => f a ^ n) =O[l] (fun _ => (1 : ℝ)) := (hf.pow n).isBigO_one ℝ
  refine (h1.mul (isBigO_refl f l)).congr (fun a => by ring) (fun a => by simp)

/-- Woodford (2003), §1, footnote 7, p. 386: `a² ≠ O(a³)` as `a → 0`; a second-order term is
not a third-order residual.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem sq_not_isBigO_cube : ¬ (fun a : ℝ => a ^ 2) =O[𝓝 0] (fun a => a ^ 3) := by
  intro h
  have hlo : (fun a : ℝ => a ^ 3) =o[𝓝 0] (fun a => a ^ 2) := by
    have := ((isLittleO_one_iff ℝ).2 (tendsto_id : Tendsto (fun a : ℝ => a) (𝓝 0) (𝓝 0))).mul_isBigO
      (isBigO_refl (fun a : ℝ => a ^ 2) (𝓝 0))
    exact this.congr (fun a => by simp only [id]; ring) (fun a => by simp)
  refine hlo.not_isBigO ?_ h
  have : ∀ᶠ a in 𝓝[≠] (0 : ℝ), a ^ 3 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact pow_ne_zero 3 ha
  exact this.frequently.filter_mono nhdsWithin_le_nhds

/-- Woodford (2003), p. 394 (first-order Taylor expansion with a quadratic remainder,
adapted from the Galí Chapter 4 project's taylor_two): if `f` is `C²` near `x₀`, then
`f x − f x₀ − f'(x₀)(x − x₀) = O((x − x₀)²)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem taylor_one_bigO {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContDiffAt ℝ 2 f x₀) :
    (fun x => f x - f x₀ - deriv f x₀ * (x - x₀)) =O[𝓝 x₀] fun x => (x - x₀) ^ 2 := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hs : ContDiffOn ℝ 2 f (Metric.ball x₀ r) := hfU.mono hball
  have hT := taylor_isLittleO (convex_ball x₀ r) (Metric.mem_ball_self hr) hs
  rw [nhdsWithin_eq_nhds.2 (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] at hT
  have hx0 := Metric.mem_ball_self hr (x := x₀)
  have e1 := iteratedDerivWithin_of_isOpen (n := 1) (f := f) Metric.isOpen_ball hx0
  have e2 := iteratedDerivWithin_of_isOpen (n := 2) (f := f) Metric.isOpen_ball hx0
  have heq : (fun x => f x - f x₀ - deriv f x₀ * (x - x₀))
      = fun x => (f x - taylorWithinEval f 2 (Metric.ball x₀ r) x₀ x) +
        iteratedDeriv 2 f x₀ / 2 * (x - x₀) ^ 2 := by
    funext x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_zero, e1, e2,
      iteratedDeriv_one, smul_eq_mul]
    norm_num [Nat.factorial]
    ring
  rw [heq]
  exact hT.isBigO.add ((isBigO_refl _ _).const_mul_left _)

end OneParamTaylor

namespace ExpLogCES

open Filter Topology Asymptotics
open OneParamTaylor (pow_succ_isBigO_self)
/-- Woodford (2003), App. E, eq. (E.5), p. 693 (ingredient (T2)): for `|x| ≤ 1`,
`|eˣ − (1 + x + x²/2)| ≤ (2/9)|x|³`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem abs_exp_sub_taylor2_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ 2 / 9 * |x| ^ 3 := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  have e : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [e] at h
  have e2 : ((Nat.succ 3 : ℕ) : ℝ) / ((Nat.factorial 3 : ℕ) * (3 : ℕ)) = 2 / 9 := by
    norm_num [Nat.factorial]
  rw [e2] at h
  linarith

/-- Woodford (2003), App. E, p. 693: the exact remainder of `eˣ = 1 + x + x²/2 + O(x³)`,
`expRem x = eˣ − 1 − x − x²/2` (an atom of weight three, abs_expRem_le); it gives
`Y/Ȳ − 1 = Ŷ + Ŷ²/2 + expRem Ŷ` exactly.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def expRem (x : ℝ) : ℝ := Real.exp x - 1 - x - x ^ 2 / 2

/-- Woodford (2003), App. E, p. 693: `eˣ − 1 = x + x²/2 + expRem x` exactly.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem exp_sub_one_eq (x : ℝ) : Real.exp x - 1 = x + x ^ 2 / 2 + expRem x := by
  unfold expRem; ring

/-- Woodford (2003), App. E, p. 693: the logarithmic remainder
`rlog u = log(1 + u) − u + u²/2` (an atom of weight three, `abs_rlog_le`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def rlog (u : ℝ) : ℝ := Real.log (1 + u) - u + u ^ 2 / 2

/-- Woodford (2003), App. E, p. 693: the logarithmic remainder is of third order,
`|rlog u| ≤ |u|³/(1 − |u|)` for `|u| < 1`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem abs_rlog_le {u : ℝ} (hu : |u| < 1) : |rlog u| ≤ |u| ^ 3 / (1 - |u|) := by
  have hu' : |-u| < 1 := by rwa [abs_neg]
  have h := Real.abs_log_sub_add_sum_range_le hu' 2
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.cast_zero, Nat.cast_one, pow_one, abs_neg, sub_neg_eq_add] at h
  have he : rlog u = -u / (0 + 1) + (-u) ^ 2 / (1 + 1) + Real.log (1 + u) := by
    unfold rlog; ring
  rw [he]
  simpa using h

/-- Woodford (2003), App. E, eq. (E.5), p. 693: `eˣ − (1 + x + x²/2) = O(x³)` as `x → 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem exp_taylor2_isBigO :
    (fun x => Real.exp x - (1 + x + x ^ 2 / 2)) =O[𝓝 0] (fun x => x ^ 3) := by
  refine IsBigO.of_bound (2 / 9) ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with x hx
  have hx' : |x| ≤ 1 := by simpa using hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  exact abs_exp_sub_taylor2_le hx'

/-- Woodford (2003), App. E, p. 693 (log counterpart of (T2)): for `|u| ≤ 1/2`,
`|log(1 + u) − (u − u²/2)| ≤ 2|u|³`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem abs_log_one_add_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - (u - u ^ 2 / 2)| ≤ 2 * |u| ^ 3 := by
  have hpos : 0 < 1 - |u| := by linarith
  have h := abs_rlog_le (by linarith : |u| < 1)
  have e : Real.log (1 + u) - (u - u ^ 2 / 2) = rlog u := by unfold rlog; ring
  rw [e]
  refine h.trans ?_
  rw [div_le_iff₀ hpos]
  have : 0 ≤ |u| ^ 3 := by positivity
  nlinarith

/-- Woodford (2003), App. E, p. 693: `log(1 + u) − (u − u²/2) = O(u³)` as `u → 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem log_taylor2_isBigO :
    (fun u => Real.log (1 + u) - (u - u ^ 2 / 2)) =O[𝓝 0] (fun u => u ^ 3) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
  have hu' : |u| ≤ 1 / 2 := by simpa using hu
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  exact abs_log_one_add_sub_le hu'

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), App. E, p. 693: the cross-sectional mean `E_i y = ∑ w_i y_i` over a finite
set of goods with weights `w`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
def crossMean (w y : ι → ℝ) : ℝ := ∑ i, w i * y i

/-- Woodford (2003), App. E, p. 693: the cross-sectional variance
`var_i y = ∑ w_i (y_i − E_i y)²`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
def crossVar (w y : ι → ℝ) : ℝ := ∑ i, w i * (y i - crossMean w y) ^ 2

/-- Woodford (2003), App. E, p. 693: `var_i y = E_i y² − (E_i y)²` when the weights sum to one.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem crossVar_eq {w : ι → ℝ} (hw1 : ∑ i, w i = 1) (y : ι → ℝ) :
    crossVar w y = crossMean w (fun i => y i ^ 2) - crossMean w y ^ 2 := by
  unfold crossVar
  have h : ∀ i, w i * (y i - crossMean w y) ^ 2 =
      w i * y i ^ 2 - 2 * crossMean w y * (w i * y i) + crossMean w y ^ 2 * w i :=
    fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hw1]
  simp only [crossMean]
  ring

/-- Woodford (2003), §2, eq. (2.12), p. 396 (scaling): `E_i(a y) = a E_i y`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem crossMean_mul (w : ι → ℝ) (a : ℝ) (y : ι → ℝ) :
    crossMean w (fun i => a * y i) = a * crossMean w y := by
  simp only [crossMean, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Woodford (2003), App. E, p. 693: `|E_i y| ≤ ‖y‖∞` for probability weights.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem abs_crossMean_le {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (y : ι → ℝ) : |crossMean w y| ≤ ‖y‖ := by
  unfold crossMean
  calc |∑ i, w i * y i| ≤ ∑ i, |w i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i * ‖y‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm y i) (hw i)
    _ = ‖y‖ := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Woodford (2003), App. E, p. 693: `0 ≤ E_i y² ≤ ‖y‖∞²` for probability weights.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem crossMean_sq_le {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (y : ι → ℝ) :
    0 ≤ crossMean w (fun i => y i ^ 2) ∧ crossMean w (fun i => y i ^ 2) ≤ ‖y‖ ^ 2 := by
  unfold crossMean
  refine ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _), ?_⟩
  calc ∑ i, w i * y i ^ 2 ≤ ∑ i, w i * ‖y‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        refine mul_le_mul_of_nonneg_left ?_ (hw i)
        have h := norm_le_pi_norm y i
        rw [Real.norm_eq_abs] at h
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = ‖y‖ ^ 2 := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Woodford (2003), App. E, p. 693: `0 ≤ var_i y ≤ ‖y‖∞²` for probability weights.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem crossVar_le {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (y : ι → ℝ) :
    0 ≤ crossVar w y ∧ crossVar w y ≤ ‖y‖ ^ 2 := by
  refine ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _), ?_⟩
  rw [crossVar_eq hw1]
  have := (crossMean_sq_le hw hw1 y).2
  nlinarith [sq_nonneg (crossMean w y)]

/-- Woodford (2003), eq. (2.6), p. 393: the exponential moment `E_i[exp(r y)] = ∑ w_i e^{r y_i}`
underlying a Dixit–Stiglitz aggregate with exponent `r`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def cesMoment (w : ι → ℝ) (r : ℝ) (y : ι → ℝ) : ℝ := ∑ i, w i * Real.exp (r * y i)

/-- Woodford (2003), eq. (2.6), p. 393: the normalised cumulant
`(1/r) log E_i[exp(r y)]` (the log of a Dixit–Stiglitz aggregate of `e^{y}`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def cumulant (w : ι → ℝ) (r : ℝ) (y : ι → ℝ) : ℝ :=
  1 / r * Real.log (cesMoment w r y)

/-- Woodford (2003), eq. (2.6), p. 393: the exponential moment is positive for probability
weights.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem cesMoment_pos {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (r : ℝ)
    (y : ι → ℝ) : 0 < cesMoment w r y := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hw1]; exact one_ne_zero)
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ i, mul_pos (lt_of_le_of_ne (hw i) (Ne.symm hi)) (Real.exp_pos _)⟩

/-- Woodford (2003), App. E, eq. (E.5), p. 693 and survey (T4): the CES / cumulant expansion
for a finite weighted cross-section,
`(1/r) log E_i[exp(r y)] = E_i y + (r/2) var_i y + O(‖y‖∞³)` as `y → 0`, for any `r ≠ 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem cumulant_expansion {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {r : ℝ}
    (hr : r ≠ 0) :
    (fun y => cumulant w r y - (crossMean w y + r / 2 * crossVar w y)) =O[𝓝 0]
      (fun y => ‖y‖ ^ 3) := by
  have hN : Tendsto (fun y : ι → ℝ => ‖y‖) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : ι → ℝ))
  have hE1 : (fun y => crossMean w y) =O[𝓝 (0 : ι → ℝ)] (fun y => ‖y‖) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using abs_crossMean_le hw hw1 y)
  have hE2 : (fun y => crossMean w (fun i => y i ^ 2)) =O[𝓝 (0 : ι → ℝ)] (fun y => ‖y‖ ^ 2) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun y => by
      have h := crossMean_sq_le hw hw1 y
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h.1, abs_of_nonneg (by positivity)]
      linarith [h.2])
  -- the remainder of the exponential moment
  have hA : (fun y => (cesMoment w r y - 1) - (r * crossMean w y +
      r ^ 2 / 2 * crossMean w (fun i => y i ^ 2))) =O[𝓝 (0 : ι → ℝ)] (fun y => ‖y‖ ^ 3) := by
    refine IsBigO.of_bound (2 / 9 * |r| ^ 3) ?_
    have hrpos : 0 < 1 / |r| := by positivity
    filter_upwards [Metric.closedBall_mem_nhds (0 : ι → ℝ) hrpos] with y hy
    have hy' : |r| * ‖y‖ ≤ 1 := by
      have : ‖y‖ ≤ 1 / |r| := by simpa using hy
      rw [le_div_iff₀ (abs_pos.2 hr)] at this
      linarith
    have key : (cesMoment w r y - 1) - (r * crossMean w y +
        r ^ 2 / 2 * crossMean w (fun i => y i ^ 2)) =
        ∑ i, w i * (Real.exp (r * y i) - (1 + r * y i + (r * y i) ^ 2 / 2)) := by
      have h1 : ∀ i, w i * (Real.exp (r * y i) - (1 + r * y i + (r * y i) ^ 2 / 2)) =
          w i * Real.exp (r * y i) - w i - r * (w i * y i) - r ^ 2 / 2 * (w i * y i ^ 2) :=
        fun i => by ring
      rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1]
      simp only [cesMoment, crossMean]
      ring
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_norm]
    calc |∑ i, w i * (Real.exp (r * y i) - (1 + r * y i + (r * y i) ^ 2 / 2))|
        ≤ ∑ i, |w i * (Real.exp (r * y i) - (1 + r * y i + (r * y i) ^ 2 / 2))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, w i * (2 / 9 * |r| ^ 3 * ‖y‖ ^ 3) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg (hw i)]
          refine mul_le_mul_of_nonneg_left ?_ (hw i)
          have hyi : |y i| ≤ ‖y‖ := by simpa using norm_le_pi_norm y i
          have hri : |r * y i| ≤ |r| * ‖y‖ := by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left hyi (abs_nonneg r)
          calc _ ≤ 2 / 9 * |r * y i| ^ 3 := abs_exp_sub_taylor2_le (hri.trans hy')
            _ ≤ 2 / 9 * (|r| * ‖y‖) ^ 3 := by gcongr
            _ = 2 / 9 * |r| ^ 3 * ‖y‖ ^ 3 := by ring
      _ = 2 / 9 * |r| ^ 3 * ‖y‖ ^ 3 := by rw [← Finset.sum_mul, hw1, one_mul]
  have h31 : (fun y : ι → ℝ => ‖y‖ ^ 3) =O[𝓝 0] (fun y => ‖y‖) := pow_succ_isBigO_self hN 2
  have h21 : (fun y : ι → ℝ => ‖y‖ ^ 2) =O[𝓝 0] (fun y => ‖y‖) := pow_succ_isBigO_self hN 1
  have h32 : (fun y : ι → ℝ => ‖y‖ ^ 3) =O[𝓝 0] (fun y => ‖y‖ ^ 2) := by
    refine ((hN.isBigO_one ℝ).mul (isBigO_refl (fun y : ι → ℝ => ‖y‖ ^ 2) _)).congr
      (fun y => by ring) (fun y => by ring)
  -- `u = E[exp(r y)] − 1` is first order
  have hu : (fun y => cesMoment w r y - 1) =O[𝓝 (0 : ι → ℝ)] (fun y => ‖y‖) := by
    refine ((hA.trans h31).add ((hE1.const_mul_left r).add
      ((hE2.trans h21).const_mul_left (r ^ 2 / 2)))).congr_left fun y => ?_
    ring
  have hut : Tendsto (fun y => cesMoment w r y - 1) (𝓝 (0 : ι → ℝ)) (𝓝 0) :=
    hu.trans_tendsto hN
  have hL : (fun y => Real.log (1 + (cesMoment w r y - 1)) -
      ((cesMoment w r y - 1) - (cesMoment w r y - 1) ^ 2 / 2)) =O[𝓝 (0 : ι → ℝ)]
      (fun y => ‖y‖ ^ 3) :=
    (log_taylor2_isBigO.comp_tendsto hut).trans (hu.pow 3)
  have hP : (fun y => ((cesMoment w r y - 1) - r * crossMean w y) *
      ((cesMoment w r y - 1) + r * crossMean w y)) =O[𝓝 (0 : ι → ℝ)] (fun y => ‖y‖ ^ 3) := by
    have h1 : (fun y => (cesMoment w r y - 1) - r * crossMean w y) =O[𝓝 (0 : ι → ℝ)]
        (fun y => ‖y‖ ^ 2) := by
      refine ((hA.trans h32).add (hE2.const_mul_left (r ^ 2 / 2))).congr_left fun y => ?_
      ring
    exact (h1.mul (hu.add (hE1.const_mul_left r))).congr_right fun y => by ring
  refine (((hL.add hA).sub (hP.const_mul_left (1 / 2))).const_mul_left (1 / r)).congr_left
    fun y => ?_
  rw [crossVar_eq hw1, cumulant]
  have e : 1 + (cesMoment w r y - 1) = cesMoment w r y := by ring
  rw [e]
  field_simp
  ring

/-- Woodford (2003), eq. (2.6), p. 393 (and the price index, Ch. 3 eq. (1.3)): the
Dixit–Stiglitz aggregate `(∑ w_i p_iʳ)^{1/r}` with exponent `r` (`r = 1 − θ` for the price
index, `r = (θ − 1)/θ` for the output aggregate).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def cesIndex (w : ι → ℝ) (r : ℝ) (p : ι → ℝ) : ℝ :=
  (∑ i, w i * p i ^ r) ^ (1 / r)

/-- Woodford (2003), eq. (2.6), p. 393: the log of a Dixit–Stiglitz aggregate of `e^{q}` is
the normalised cumulant `(1/r) log E_i[exp(r q)]`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem log_cesIndex_exp {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (r : ℝ)
    (q : ι → ℝ) : Real.log (cesIndex w r (fun i => Real.exp (q i))) = cumulant w r q := by
  have e : ∑ i, w i * Real.exp (q i) ^ r = cesMoment w r q := by
    unfold cesMoment
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm (q i) r]
  unfold cesIndex cumulant
  rw [e, Real.log_rpow (cesMoment_pos hw hw1 r q)]

/-- Woodford (2003), App. E, eq. (E.5), p. 693: with `ŷ_i = log(y_i/Ȳ)` and
`Ŷ = log(Y/Ȳ)`, `Y` the Dixit–Stiglitz aggregate (2.6) with elasticity `θ ≠ 1` (the book has
`θ > 1`),
`Ŷ = E_i ŷ + ½(1 − θ⁻¹) var_i ŷ + O(‖ŷ‖³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem log_outputIndex_expansion {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {θ : ℝ} (hθ1 : θ ≠ 1) :
    (fun yhat => Real.log (cesIndex w (1 - θ⁻¹) (fun i => Real.exp (yhat i))) -
      (crossMean w yhat + 1 / 2 * (1 - θ⁻¹) * crossVar w yhat)) =O[𝓝 0]
      (fun yhat => ‖yhat‖ ^ 3) := by
  have hr : 1 - θ⁻¹ ≠ 0 := by
    intro h
    apply hθ1
    have : θ⁻¹ = 1 := by linarith
    simpa using congrArg (·⁻¹) this
  refine (cumulant_expansion hw hw1 hr).congr_left fun yhat => ?_
  rw [log_cesIndex_exp hw hw1]
  ring

end ExpLogCES

namespace Moments

open ExpLogCES
variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), App. E.1, p. 694: `E_i z² = var_i z + (E_i z)²` (weights summing to
one).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem sum_sq_eq {w : ι → ℝ} (hw : ∑ i, w i = 1) (z : ι → ℝ) :
    ∑ i, w i * z i ^ 2 = crossVar w z + crossMean w z ^ 2 := by
  rw [crossVar_eq hw]
  unfold crossMean
  ring

/-- Woodford (2003), App. E.1, p. 694 ("integrating this expression over the differentiated
goods"): the cross-sectional average of a quadratic `a z + b z²` is
`a E z + b((E z)² + var z)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem mean_quadratic {w : ι → ℝ} (hw : ∑ i, w i = 1) (a b : ℝ) (z : ι → ℝ) :
    ∑ i, w i * (a * z i + b * z i ^ 2) =
      a * crossMean w z + b * (crossMean w z ^ 2 + crossVar w z) := by
  have h : ∀ i, w i * (a * z i + b * z i ^ 2) = a * (w i * z i) + b * (w i * z i ^ 2) :=
    fun i => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_sq_eq hw]
  unfold crossMean
  ring

/-- Woodford (2003), p. 400: the Calvo coefficient `α/[(1 − α)(1 − αβ)]` of the discounted
dispersion.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def calvoK (α β : ℝ) : ℝ := α / ((1 - α) * (1 - α * β))

/-- Woodford (2003), Ch. 3, eq. (2.19), restated: the slope of the New Keynesian Phillips curve
with Calvo pricing and firm-specific inputs, `κ = (1−α)(1−αβ)/α · (ω+σ⁻¹)/(1+ωθ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def calvoKappa (α β ω θ σ : ℝ) : ℝ :=
  (1 - α) * (1 - α * β) / α * ((ω + σ) / (1 + ω * θ))

end Moments

namespace SeqW

open Filter Topology
/-- Woodford (2003), App. E.3, p. 697 (discounted sums of bounded sequences): a real family is
bounded.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
def Bdd {ι : Type*} (a : ι → ℝ) : Prop := ∃ M, ∀ i, |a i| ≤ M

namespace Bdd

variable {ι κ : Type*}

/-- Woodford (2003), App. E.3, p. 697: constants are bounded.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem const (c : ℝ) : Bdd (fun _ : ι => c) := ⟨|c|, fun _ => le_rfl⟩

/-- Woodford (2003), App. E.3, p. 697: the bound may be taken nonnegative.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem nonneg_bound {a : ι → ℝ} (ha : Bdd a) : ∃ M, 0 ≤ M ∧ ∀ i, |a i| ≤ M := by
  obtain ⟨M, hM⟩ := ha
  exact ⟨max M 0, le_max_right _ _, fun i => le_max_of_le_left (hM i)⟩

/-- Woodford (2003), App. E.3, p. 697: sums of bounded families are bounded.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem add {a b : ι → ℝ} (ha : Bdd a) (hb : Bdd b) : Bdd (fun i => a i + b i) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A + B, fun i => (abs_add_le _ _).trans (add_le_add (hA i) (hB i))⟩

/-- Woodford (2003), App. E.3, p. 697: negatives of bounded families are bounded.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem neg {a : ι → ℝ} (ha : Bdd a) : Bdd (fun i => -a i) := by
  obtain ⟨A, hA⟩ := ha
  exact ⟨A, fun i => by rw [abs_neg]; exact hA i⟩

/-- Woodford (2003), App. E.3, p. 697: differences of bounded families are bounded.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem sub {a b : ι → ℝ} (ha : Bdd a) (hb : Bdd b) : Bdd (fun i => a i - b i) := by
  simpa [sub_eq_add_neg] using ha.add hb.neg

/-- Woodford (2003), App. E.3, p. 697: products of bounded families are bounded.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem mul {a b : ι → ℝ} (ha : Bdd a) (hb : Bdd b) : Bdd (fun i => a i * b i) := by
  obtain ⟨A, hA0, hA⟩ := ha.nonneg_bound
  obtain ⟨B, -, hB⟩ := hb.nonneg_bound
  exact ⟨A * B, fun i => by
    rw [abs_mul]; exact mul_le_mul (hA i) (hB i) (abs_nonneg _) hA0⟩

/-- Woodford (2003), App. E.3, p. 697: quotients by a constant are bounded.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem div_const {a : ι → ℝ} (ha : Bdd a) (c : ℝ) : Bdd (fun i => a i / c) := by
  simpa [div_eq_mul_inv] using ha.mul (const c⁻¹)

/-- Woodford (2003), App. E.3, p. 697: powers of bounded families are bounded.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem pow {a : ι → ℝ} (ha : Bdd a) (n : ℕ) : Bdd (fun i => a i ^ n) := by
  induction n with
  | zero => simpa using const (ι := ι) 1
  | succ n ih => simpa [pow_succ] using ih.mul ha

/-- Woodford (2003), (2.21): linear combinations of bounded families are bounded.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem lin {a b : ι → ℝ} (ha : Bdd a) (hb : Bdd b) (c d : ℝ) :
    Bdd fun i => c * a i + d * b i :=
  ((const c).mul ha).add ((const d).mul hb)

/-- Woodford (2003), App. E.3, p. 697: reindexing a bounded family keeps it bounded.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem comp {a : ι → ℝ} (ha : Bdd a) (f : κ → ι) : Bdd (fun j => a (f j)) := by
  obtain ⟨A, hA⟩ := ha
  exact ⟨A, fun j => hA (f j)⟩

end Bdd

/-- Woodford (2003), (2.21), p. 400: geometrically weighted bounded sequences are summable
(`|β| < 1`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem summable_geom_bdd {β M : ℝ} (hβ : |β| < 1) {a : ℕ → ℝ} (ha : ∀ t, |a t| ≤ M) :
    Summable (fun t => β ^ t * a t) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg β) hβ).mul_right M)
    (fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (ha t) (pow_nonneg (abs_nonneg β) t))

/-- Woodford (2003), (2.21), p. 400: absolute summability of `βᵗ a_t` for a bounded sequence
(`|β| < 1`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem summable_norm_geom_bdd {β M : ℝ} (hβ : |β| < 1) {a : ℕ → ℝ} (ha : ∀ t, |a t| ≤ M) :
    Summable (fun t => ‖β ^ t * a t‖) := by
  have h := summable_geom_bdd (β := |β|) (a := fun t => |a t|) (by rwa [abs_abs]) (fun t => by
    rw [abs_abs]; exact ha t)
  refine h.congr fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]

/-- Woodford (2003), App. E.3, p. 697: a bounded sequence is summable against `βᵗ`,
`0 ≤ β < 1`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem Bdd.summable {a : ℕ → ℝ} (ha : Bdd a) {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) :
    Summable (fun t => β ^ t * a t) := by
  obtain ⟨A, hA⟩ := ha
  exact summable_geom_bdd (by rwa [abs_of_nonneg h0]) hA

/-- Woodford (2003), (2.21): `|∑ βᵗ f_t| ≤ B/(1 − β)` when `|f_t| ≤ B` (`0 ≤ β < 1`; survey
error 25: a uniform bound `B = O(ε³)` gives an `O(ε³)` discounted remainder).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem abs_tsum_le {f : ℕ → ℝ} {B β : ℝ} (hf : ∀ t, |f t| ≤ B) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    |∑' t, β ^ t * f t| ≤ B / (1 - β) := by
  have hs := Bdd.summable (a := f) ⟨B, hf⟩ hβ0 hβ1
  have hg := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left B
  have h1 : |∑' t, β ^ t * f t| ≤ ∑' t, |β ^ t * f t| := by
    have := norm_tsum_le_tsum_norm (f := fun t => β ^ t * f t)
      (by simpa only [Real.norm_eq_abs] using hs.abs)
    simpa only [Real.norm_eq_abs] using this
  have h2 : ∑' t, |β ^ t * f t| ≤ ∑' t, B * β ^ t := by
    refine hs.abs.tsum_le_tsum (fun t => ?_) hg.summable
    rw [abs_mul, abs_pow, abs_of_nonneg hβ0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hf t) (pow_nonneg hβ0 t)
  rw [hg.tsum_eq] at h2
  calc _ ≤ _ := h1.trans h2
    _ = B / (1 - β) := by rw [div_eq_mul_inv]

/-- Woodford (2003), p. 400 (integrating (2.20) forward, exact): if
`V_{t+1} = α V_t + c q_t` then `V_{t+1} = α^{t+1} V_0 + ∑_{s ≤ t} α^{t−s} c q_s`
(with `V_0 = Δ_{−1}` the inherited dispersion).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem disp_integrated {α c : ℝ} {V q : ℕ → ℝ} (hrec : ∀ t, V (t + 1) = α * V t + c * q t)
    (t : ℕ) :
    V (t + 1) = α ^ (t + 1) * V 0 + ∑ s ∈ Finset.range (t + 1), α ^ (t - s) * (c * q s) := by
  induction t with
  | zero => simp [hrec 0]
  | succ t ih =>
    rw [hrec (t + 1), ih, Finset.sum_range_succ _ (t + 1), Nat.sub_self, pow_zero, one_mul,
      mul_add, Finset.mul_sum]
    have : ∀ s ∈ Finset.range (t + 1), α * (α ^ (t - s) * (c * q s)) =
        α ^ (t + 1 - s) * (c * q s) := by
      intro s hs
      rw [Finset.mem_range] at hs
      rw [Nat.sub_add_comm (Nat.lt_succ_iff.mp hs), pow_succ]
      ring
    rw [Finset.sum_congr rfl this]
    ring

/-- Woodford (2003), p. 400 (**the discounted sum, exact, genuine `tsum`s**): if
`V_{t+1} = α V_t + c q_t`, `0 ≤ α`, `0 ≤ β`, `αβ < 1` and `∑ βᵗ q_t` converges absolutely,
then `∑ βᵗ V_{t+1}` converges and equals `(α V_0 + c ∑ βᵗ q_t)/(1 − αβ)` (a Cauchy product
of `∑ (αβ)ᵏ` with `∑ βˢ q_s`; no bound on `V` is needed).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem disp_discounted_hasSum {α β c : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α * β < 1)
    {V q : ℕ → ℝ} (hrec : ∀ t, V (t + 1) = α * V t + c * q t)
    (hq : Summable fun t => ‖β ^ t * q t‖) :
    HasSum (fun t => β ^ t * V (t + 1)) ((α * V 0 + c * ∑' t, β ^ t * q t) / (1 - α * β)) := by
  set f : ℕ → ℝ := fun k => (α * β) ^ k with hfdef
  set g : ℕ → ℝ := fun s => β ^ s * q s with hgdef
  have hab0 : 0 ≤ α * β := mul_nonneg hα hβ
  have hf : Summable fun k => ‖f k‖ := by
    simpa [hfdef, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hab0 _)] using
      summable_geometric_of_lt_one hab0 hαβ
  have hcp := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hq
  have hcs := (summable_norm_sum_mul_range_of_summable_norm hf hq).of_norm
  have hterm : ∀ t, β ^ t * V (t + 1) = (α * V 0) * f t +
      c * ∑ k ∈ Finset.range (t + 1), f k * g (t - k) := by
    intro t
    rw [disp_integrated hrec t]
    have hr := Finset.sum_range_reflect (fun k => f k * g (t - k)) (t + 1)
    simp only [Nat.add_sub_cancel] at hr
    rw [← hr, mul_add, Finset.mul_sum, Finset.mul_sum]
    have : ∀ s ∈ Finset.range (t + 1), β ^ t * (α ^ (t - s) * (c * q s)) =
        c * (f (t - s) * g (t - (t - s))) := by
      intro s hs
      rw [Finset.mem_range] at hs
      have hst : s ≤ t := Nat.lt_succ_iff.mp hs
      rw [Nat.sub_sub_self hst]
      simp only [hfdef, hgdef]
      have : β ^ t = β ^ (t - s) * β ^ s := by rw [← pow_add, Nat.sub_add_cancel hst]
      rw [this, mul_pow]
      ring
    rw [Finset.sum_congr rfl this, pow_succ]
    simp only [hfdef]
    ring
  have hgeo : HasSum f (1 - α * β)⁻¹ := hasSum_geometric_of_lt_one hab0 hαβ
  have hA : HasSum (fun t => (α * V 0) * f t) ((α * V 0) * (1 - α * β)⁻¹) := hgeo.mul_left _
  have hB : HasSum (fun t => c * ∑ k ∈ Finset.range (t + 1), f k * g (t - k))
      (c * ((∑' k, f k) * ∑' s, g s)) := by
    rw [hcp]
    exact hcs.hasSum.mul_left c
  have h := hA.add hB
  rw [hgeo.tsum_eq] at h
  have hpos : (1 : ℝ) - α * β ≠ 0 := by linarith
  convert h using 1
  · funext t
    exact hterm t
  · field_simp

variable {Ω : Type*}

variable (𝔼 : ExpectationSystem Ω)

end SeqW

namespace Prop61

open MeasureTheory Filter Topology Asymptotics
open OneParamTaylor (taylor_one_bigO)
open ExpLogCES (expRem)
variable {G : Type*} [MeasurableSpace G]

/-- Woodford (2003), p. 393: `ω = Ȳ ṽ_yy/ṽ_y`, the elasticity of `ṽ_y` (of real marginal cost
with respect to own output).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def omegaEl (Ybar vy vyy : ℝ) : ℝ := Ybar * vyy / vy

/-- Woodford (2003), p. 393: `σ⁻¹ = −Ȳ u_cc/u_c`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def sigmaInvEl (Ybar uc ucc : ℝ) : ℝ := -(Ybar * ucc / uc)

/-- Woodford (2003), App. E, p. 693: `g_t = −u_cξ ξ̃_t/(Ȳ u_cc)` (here Cu is the value of
`u_cξ ξ̃_t`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def gShock (Ybar ucc Cu : ℝ) : ℝ := -(Cu / (Ybar * ucc))

/-- Woodford (2003), App. E, p. 693: `q_t = −v_yξ ξ̃_t/(Ȳ v_yy)` (here Cv is the value of
`v_yξ ξ̃_t`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def qShock (Ybar vyy Cv : ℝ) : ℝ := -(Cv / (Ybar * vyy))

/-- Woodford (2003), p. 394 and imprecision 26 of the survey: the quadratic form of (2.10),
`(σ⁻¹ + ω) X² + (θ⁻¹ + ω) V`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def lossQ (sinv omega θ X V : ℝ) : ℝ := (sinv + omega) * X ^ 2 + (θ⁻¹ + omega) * V

/-- Woodford (2003), p. 693: `Ỹ = Y − Ȳ = Ȳ (Ŷ + Ŷ²/2 + expRem Ŷ)` exactly, `Y = Ȳ e^Ŷ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem levelDev_eq (Ybar Y : ℝ) :
    Ybar * Real.exp Y - Ybar = Ybar * (Y + Y ^ 2 / 2 + expRem Y) := by
  rw [← ExpLogCES.exp_sub_one_eq]
  ring

/-- Woodford (2003), eq. (E.2), first line, p. 692: the second-order Taylor polynomial of
`ũ(Y; ξ̃)` at `(Ȳ, 0)` in the level deviation `Ỹ`, with `Lu = u_ξ ξ̃`, `Cu = u_cξ ξ̃`,
`Qu = ξ̃' u_ξξ ξ̃`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def uTaylor (ubar uc ucc Lu Cu Qu Ytil : ℝ) : ℝ :=
  ubar + uc * Ytil + Lu + ucc / 2 * Ytil ^ 2 + Cu * Ytil + Qu / 2

/-- Woodford (2003), eq. (E.2), last line: the policy-relevant part
`Ŷ + ½(1 − σ⁻¹) Ŷ² + σ⁻¹ g Ŷ` (normalised by `Ȳ u_c`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def Tu (sinv g Y : ℝ) : ℝ := Y + (1 - sinv) / 2 * Y ^ 2 + sinv * g * Y

/-- Woodford (2003), eq. (E.2): the explicit remainder of (E.2) (normalised by `Ȳ u_c`), with
`r = expRem Ŷ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def Ru (sinv g Y r : ℝ) : ℝ :=
  r - sinv / 2 * ((Y + Y ^ 2 / 2 + r) ^ 2 - Y ^ 2) + sinv * g * (Y ^ 2 / 2 + r)

/-- Woodford (2003), eq. (E.2), p. 692 (**exact, in terms of the coefficients**): if
`u_cc = −σ⁻¹u_c/Ȳ` and `u_cξ ξ̃ = σ⁻¹u_c g` (the definitions of `σ⁻¹` and `g`), then at
`Ỹ = Ȳ(Ŷ + Ŷ²/2 + r)`, `ũ-Taylor = (ū + u_ξ ξ̃ + ½ ξ̃' u_ξξ ξ̃) + Ȳ u_c [Tu + Ru]`; the first
bracket is t.i.p. No nondegeneracy (not even `Ȳ ≠ 0`) is needed.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem uTaylor_eq_of_coeffs {ubar uc ucc Lu Cu Qu Ybar sinv g Y r : ℝ}
    (hucc : ucc = -(sinv * uc / Ybar)) (hCu : Cu = sinv * uc * g) :
    uTaylor ubar uc ucc Lu Cu Qu (Ybar * (Y + Y ^ 2 / 2 + r)) =
      (ubar + Lu + Qu / 2) + Ybar * uc * (Tu sinv g Y + Ru sinv g Y r) := by
  subst hucc hCu
  unfold uTaylor Tu Ru
  field_simp
  ring

/-- Woodford (2003), eq. (E.2), p. 692 (**exact**): with `σ⁻¹ = −Ȳ u_cc/u_c`,
`g = −u_cξ ξ̃/(Ȳ u_cc)` and `Ỹ = Ȳ(Ŷ + Ŷ²/2 + r)`,
`ũ-Taylor = (ū + u_ξ ξ̃ + ½ ξ̃' u_ξξ ξ̃) + Ȳ u_c [Tu + Ru]`; the first bracket is t.i.p.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem uTaylor_eq {ubar uc ucc Lu Cu Qu Ybar Y r : ℝ} (hY : Ybar ≠ 0) (huc : uc ≠ 0)
    (hucc : ucc ≠ 0) :
    uTaylor ubar uc ucc Lu Cu Qu (Ybar * (Y + Y ^ 2 / 2 + r)) =
      (ubar + Lu + Qu / 2) + Ybar * uc *
        (Tu (sigmaInvEl Ybar uc ucc) (gShock Ybar ucc Cu) Y +
          Ru (sigmaInvEl Ybar uc ucc) (gShock Ybar ucc Cu) Y r) :=
  uTaylor_eq_of_coeffs (by unfold sigmaInvEl; field_simp)
    (by unfold sigmaInvEl gShock; field_simp)

/-- Woodford (2003), eq. (E.3), first line, p. 693: the second-order Taylor polynomial of
`ṽ(y; ξ̃)` at `(Ȳ, 0)` in the level deviation `ỹ`, with `Lv = v_ξ ξ̃`, `Cv = v_yξ ξ̃`,
`Qv = ξ̃' v_ξξ ξ̃`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def vTaylor (vbar vy vyy Lv Cv Qv ytil : ℝ) : ℝ :=
  vbar + vy * ytil + Lv + vyy / 2 * ytil ^ 2 + Cv * ytil + Qv / 2

/-- Woodford (2003), eq. (E.3), last line: the policy-relevant part
`(1 − Φ) ŷ + ½(1 + ω) ŷ² − ω q ŷ` (normalised by `Ȳ u_c`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def Tv (Φ omega q y : ℝ) : ℝ := (1 - Φ) * y + (1 + omega) / 2 * y ^ 2 - omega * q * y

/-- Woodford (2003), eq. (E.3): the explicit remainder (normalised by `Ȳ u_c`), including the
dropped `Φ × (quadratic)` terms ("terms of higher than second order given that `Φ` is an
expansion parameter", p. 694).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def Rv (Φ omega q y r : ℝ) : ℝ :=
  (1 - Φ) * (r + omega / 2 * ((y + y ^ 2 / 2 + r) ^ 2 - y ^ 2) - omega * q * (y ^ 2 / 2 + r)) -
    Φ * ((1 + omega) / 2 * y ^ 2 - omega * q * y)

/-- Woodford (2003), eq. (E.3), p. 693 (**exact, in terms of the coefficients**): with the
steady-state condition `ṽ_y = (1 − Φ) u_c` ((2.7)–(2.8)), `v_yy = ωv_y/Ȳ`,
`v_yξ ξ̃ = −ωv_y q` (the definitions of `ω` and `q`) and `ỹ = Ȳ(ŷ + ŷ²/2 + r)`,
`ṽ-Taylor = (v̄ + v_ξ ξ̃ + ½ ξ̃' v_ξξ ξ̃) + Ȳ u_c [Tv + Rv]`; no nondegeneracy is needed.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem vTaylor_eq_of_coeffs {vbar vy vyy Lv Cv Qv Ybar uc Φ omega q y r : ℝ}
    (hvy : vy = (1 - Φ) * uc) (hvyy : vyy = omega * vy / Ybar)
    (hCv : Cv = -(omega * vy * q)) :
    vTaylor vbar vy vyy Lv Cv Qv (Ybar * (y + y ^ 2 / 2 + r)) =
      (vbar + Lv + Qv / 2) + Ybar * uc * (Tv Φ omega q y + Rv Φ omega q y r) := by
  subst hvyy hCv
  subst hvy
  unfold vTaylor Tv Rv
  field_simp
  ring

/-- Woodford (2003), eq. (E.3), p. 693 (**exact**): with the steady-state condition
`ṽ_y = (1 − Φ) u_c` ((2.7)–(2.8)), `ω = Ȳ ṽ_yy/ṽ_y`, `q = −v_yξ ξ̃/(Ȳ v_yy)` and
`ỹ = Ȳ(ŷ + ŷ²/2 + r)`, `ṽ-Taylor = (v̄ + v_ξ ξ̃ + ½ ξ̃' v_ξξ ξ̃) + Ȳ u_c [Tv + Rv]`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem vTaylor_eq {vbar vy vyy Lv Cv Qv Ybar uc Φ y r : ℝ} (hY : Ybar ≠ 0)
    (hvy : vy = (1 - Φ) * uc) (hvy0 : vy ≠ 0) (hvyy : vyy ≠ 0) :
    vTaylor vbar vy vyy Lv Cv Qv (Ybar * (y + y ^ 2 / 2 + r)) =
      (vbar + Lv + Qv / 2) + Ybar * uc *
        (Tv Φ (omegaEl Ybar vy vyy) (qShock Ybar vyy Cv) y +
          Rv Φ (omegaEl Ybar vy vyy) (qShock Ybar vyy Cv) y r) :=
  vTaylor_eq_of_coeffs hvy (by unfold omegaEl; field_simp)
    (by unfold omegaEl qShock; field_simp)

/-- Woodford (2003), (E.6), p. 694: the first-order natural rate
`Ŷⁿ = (σ⁻¹ g + ω q)/(σ⁻¹ + ω)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def natLin (sinv omega g q : ℝ) : ℝ := (sinv * g + omega * q) / (sinv + omega)

/-- Woodford (2003), (2.9)/(2.17): the first-order efficient gap `x* = Φ/(σ⁻¹ + ω)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def xStarLin (sinv omega Φ : ℝ) : ℝ := Φ / (sinv + omega)

/-- Woodford (2003), (E.1): the terms independent of policy produced by completing the square,
`½(σ⁻¹ + ω)(Ŷⁿ + x*)²`, a function of the exogenous `g`, `q`, `Φ` only.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def tipA (sinv omega g q Φ : ℝ) : ℝ :=
  (sinv + omega) / 2 * (natLin sinv omega g q + xStarLin sinv omega Φ) ^ 2

/-- Woodford (2003), (E.1)–(E.6) (**the explicit remainder of Theorem A1**). Arguments:
`Y = Ŷ`, `V = var_i ŷ`, `e` the (E.5) error (`E_i ŷ = Ŷ − ½(1−θ⁻¹)V − e`), `n` the error in
(E.6) (true natural rate `= natLin + n`), `k` the error in (2.9) (true `x* = xStarLin + k`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def R3 (sinv omega θ g q Φ Y V e n k : ℝ) : ℝ :=
  -Φ * ((1 - θ⁻¹) / 2 * V + e) + e -
    (1 + omega) / 2 * ((Y - (1 - θ⁻¹) / 2 * V - e) ^ 2 - Y ^ 2) -
    omega * q * ((1 - θ⁻¹) / 2 * V + e) -
    (sinv + omega) * (Y - natLin sinv omega g q - xStarLin sinv omega Φ) * (n + k) +
    (sinv + omega) / 2 * (n + k) ^ 2

/-- Woodford (2003), Prop. 6.1, App. E.1 (**Theorem A1, exact**): with
`E_i ŷ = Ŷ − ½(1 − θ⁻¹) var_i ŷ − e`, the true natural rate `Ŷⁿ = natLin + n`, the true
efficient gap `x* = xStarLin + k` and `x = Ŷ − Ŷⁿ`,
`Tu(Ŷ) − E_i Tv(ŷ) = −½[(σ⁻¹ + ω)(x − x*)² + (θ⁻¹ + ω) var_i ŷ] + tipA(g, q, Φ) + R3`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem thmA1 {sinv omega θ g q Φ Y V e n k : ℝ} (hden : sinv + omega ≠ 0) :
    Tu sinv g Y - ((1 - Φ) * (Y - (1 - θ⁻¹) / 2 * V - e) +
        (1 + omega) / 2 * (V + (Y - (1 - θ⁻¹) / 2 * V - e) ^ 2) -
        omega * q * (Y - (1 - θ⁻¹) / 2 * V - e)) =
      -(1 / 2) * lossQ sinv omega θ
          ((Y - (natLin sinv omega g q + n)) - (xStarLin sinv omega Φ + k)) V +
        tipA sinv omega g q Φ + R3 sinv omega θ g q Φ Y V e n k := by
  unfold Tu lossQ tipA R3 natLin xStarLin
  field_simp
  ring

/-- Woodford (2003), eq. (2.13), p. 396: `(θ⁻¹ + ω) θ² = θ(1 + ωθ)`, so with
`var_i ŷ = θ² var_i log p` ((2.12)) the loss becomes
`(σ⁻¹ + ω)(x − x*)² + θ(1 + ωθ) var_i log p`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem lossQ_disp {sinv omega θ X Δ : ℝ} (hθ : θ ≠ 0) :
    lossQ sinv omega θ X (θ ^ 2 * Δ) = (sinv + omega) * X ^ 2 + θ * (1 + omega * θ) * Δ := by
  unfold lossQ
  field_simp

end Prop61

namespace PriceDispersion

open MeasureTheory Filter Topology
open Prop61
open Moments (calvoKappa)
open SeqW (summable_norm_geom_bdd disp_discounted_hasSum)
variable {G : Type*} [MeasurableSpace G]

/-- Woodford (2003), Prop. 6.4, p. 400: the factor
`Θ = ½ θ(1 + ωθ) α/((1−α)(1−αβ))` multiplying the loss (in units of `Ȳ u_c`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def ThetaCalvo (α β θ omega : ℝ) : ℝ :=
  θ * (1 + omega * θ) / 2 * (α / ((1 - α) * (1 - α * β)))

/-- Woodford (2003), Prop. 6.4: `Θ > 0` for `0 < α < 1`, `β < 1`, `θ > 0`, `1 + ωθ > 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem ThetaCalvo_pos {α β θ omega : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ1 : β < 1) (hθ : 0 < θ) (hd : 0 < 1 + omega * θ) : 0 < ThetaCalvo α β θ omega := by
  unfold ThetaCalvo
  have : 0 < 1 - α := by linarith
  have : 0 < 1 - α * β := by nlinarith
  positivity

/-- Woodford (2003), Props. 6.4–6.5, (2.21), p. 400 (**the discounted loss, Layer A, genuine
`tsum`s**). Suppose the dispersion recursion `Δ_t = α Δ_{t−1} + (α/(1−α)) qd_t² + R_t` (index
`t+1` is date `t`; `qd_t = π_t` for Prop. 6.4, `π_t − γπ_{t−1}` for Prop. 6.5) and period
welfare (in units of `Ȳ u_c`) `W_t = −½[(σ⁻¹+ω) X_t² + θ(1+ωθ) Δ_t] + tip_t + rem_t` (the form of
(2.13), `X_t = x_t − x*`), with all sequences bounded. Then `∑ βᵗ W_t` converges and equals
`−Θ ∑ βᵗ (qd_t² + (κ/θ) X_t²) + TIP + REM`, where
`TIP = ∑ βᵗ tip_t − ½θ(1+ωθ) α Δ_{−1}/(1−αβ)` depends only on exogenous terms and the initial
dispersion, and `REM = ∑ βᵗ rem_t − ½θ(1+ωθ)/(1−αβ) ∑ βᵗ R_t`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem calvo_welfare_sum {α β θ omega sinv M : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hd : 1 + omega * θ ≠ 0)
    {D qd X tip rem R W : ℕ → ℝ}
    (hrec : ∀ t, D (t + 1) = α * D t + α / (1 - α) * qd t ^ 2 + R t)
    (hW : ∀ t, W t = -(1 / 2) * ((sinv + omega) * X t ^ 2 + θ * (1 + omega * θ) * D (t + 1)) +
      tip t + rem t)
    (hqd : ∀ t, |qd t| ≤ M) (hX : ∀ t, |X t| ≤ M) (hR : ∀ t, |R t| ≤ M)
    (htip : ∀ t, |tip t| ≤ M) (hrem : ∀ t, |rem t| ≤ M) :
    HasSum (fun t => β ^ t * W t)
      (-ThetaCalvo α β θ omega *
          ∑' t, β ^ t * (qd t ^ 2 + calvoKappa α β omega θ sinv / θ * X t ^ 2) +
        (∑' t, β ^ t * tip t - θ * (1 + omega * θ) / 2 * (α * D 0 / (1 - α * β))) +
        (∑' t, β ^ t * rem t -
          θ * (1 + omega * θ) / 2 / (1 - α * β) * ∑' t, β ^ t * R t)) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hX 0)
  have hβ : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  have hαβ : α * β < 1 := by nlinarith
  have hne1 : (1 : ℝ) - α ≠ 0 := by linarith
  have hne2 : (1 : ℝ) - α * β ≠ 0 := by linarith
  have hq2 : ∀ t, |qd t ^ 2| ≤ M ^ 2 := fun t => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hqd t) 2
  have hX2 : ∀ t, |X t ^ 2| ≤ M ^ 2 := fun t => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hX t) 2
  have sq := (summable_norm_geom_bdd hβ hq2).of_norm
  have sX := (summable_norm_geom_bdd hβ hX2).of_norm
  have sR := (summable_norm_geom_bdd hβ hR).of_norm
  have stip := (summable_norm_geom_bdd hβ htip).of_norm
  have srem := (summable_norm_geom_bdd hβ hrem).of_norm
  -- the dispersion sum
  have hQ : ∀ t, |α / (1 - α) * qd t ^ 2 + R t| ≤ α / (1 - α) * M ^ 2 + M := fun t => by
    have hc : 0 ≤ α / (1 - α) := div_nonneg hα0.le (by linarith)
    have := abs_add_le (α / (1 - α) * qd t ^ 2) (R t)
    rw [abs_mul, abs_of_nonneg hc] at this
    have := mul_le_mul_of_nonneg_left (hq2 t) hc
    linarith [hR t]
  have hD := disp_discounted_hasSum (c := 1) (V := D) hα0.le hβ0 hαβ
    (q := fun t => α / (1 - α) * qd t ^ 2 + R t) (fun t => by rw [hrec t]; ring)
    (summable_norm_geom_bdd hβ hQ)
  have hQsum : ∑' t, β ^ t * (α / (1 - α) * qd t ^ 2 + R t) =
      α / (1 - α) * ∑' t, β ^ t * qd t ^ 2 + ∑' t, β ^ t * R t := by
    have : (fun t => β ^ t * (α / (1 - α) * qd t ^ 2 + R t)) =
        fun t => α / (1 - α) * (β ^ t * qd t ^ 2) + β ^ t * R t := by
      funext t; ring
    rw [this, (sq.mul_left _).tsum_add sR, tsum_mul_left]
  rw [hQsum] at hD
  -- assemble
  have hsum := ((((sX.hasSum.mul_left (-(1 / 2) * (sinv + omega))).add
    (hD.mul_left (-(1 / 2) * (θ * (1 + omega * θ))))).add stip.hasSum).add srem.hasSum)
  have hL : ∑' t, β ^ t * (qd t ^ 2 + calvoKappa α β omega θ sinv / θ * X t ^ 2) =
      ∑' t, β ^ t * qd t ^ 2 + calvoKappa α β omega θ sinv / θ * ∑' t, β ^ t * X t ^ 2 := by
    have : (fun t => β ^ t * (qd t ^ 2 + calvoKappa α β omega θ sinv / θ * X t ^ 2)) =
        fun t => β ^ t * qd t ^ 2 + calvoKappa α β omega θ sinv / θ * (β ^ t * X t ^ 2) := by
      funext t; ring
    rw [this, sq.tsum_add (sX.mul_left _), tsum_mul_left]
  rw [hL]
  convert hsum using 1
  · funext t
    rw [hW t]
    ring
  · unfold ThetaCalvo calvoKappa
    have hα : α ≠ 0 := hα0.ne'
    have hd' : 1 + θ * omega ≠ 0 := by rwa [mul_comm]
    field_simp
    ring

end PriceDispersion

namespace ApproxTheory

open Filter Topology Asymptotics
open OneParamTaylor
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Woodford (2003), eq. (1.2), p. 385: the quadratic approximation
`Ū + U_z z + ½ z′U_zz z` to `U(z̄ + z)` with coefficients u0, `L`, `B`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def quadApprox (u0 : ℝ) (L : F →L[ℝ] ℝ) (B : F →L[ℝ] F →L[ℝ] ℝ) (z : F) : ℝ :=
  u0 + L z + 1 / 2 * B z z

/-- Woodford (2003), eq. (1.2), p. 385 (analytic core): if `U` has first and second derivatives
`U1`, U2 along the segment `[z̄, z̄ + z]` and `‖U2(z̄ + s z) − U2 z̄‖ ≤ C` there, then
`|U(z̄ + z) − (Ū + U_z z + ½ z′U_zz z)| ≤ C ‖z‖²`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem taylor2_multivar_segment_le {U : F → ℝ} {U1 : F → F →L[ℝ] ℝ}
    {U2 : F → F →L[ℝ] F →L[ℝ] ℝ} {zbar z : F} {C : ℝ}
    (hU : ∀ s : ℝ, |s| ≤ 1 → HasFDerivAt U (U1 (zbar + s • z)) (zbar + s • z))
    (hU1 : ∀ s : ℝ, |s| ≤ 1 → HasFDerivAt U1 (U2 (zbar + s • z)) (zbar + s • z))
    (hC : ∀ s : ℝ, |s| ≤ 1 → ‖U2 (zbar + s • z) - U2 zbar‖ ≤ C) :
    |U (zbar + z) - quadApprox (U zbar) (U1 zbar) (U2 zbar) z| ≤ C * ‖z‖ ^ 2 := by
  have hpath : ∀ s : ℝ, HasDerivAt (fun s : ℝ => zbar + s • z) z s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const z).const_add zbar
  have key := taylor2_remainder_le (r := 1) (C := C * ‖z‖ ^ 2) (ε := 1)
    (f := fun s => U (zbar + s • z)) (f1 := fun s => U1 (zbar + s • z) z)
    (f2 := fun s => U2 (zbar + s • z) z z)
    (fun s hs => ?_) (fun s hs => ?_) (fun s hs => ?_) (by simp)
  · simpa [quadApprox] using key
  · have hs' : |s| ≤ 1 := by simpa using hs
    exact (hU s hs').comp_hasDerivAt s (hpath s)
  · have hs' : |s| ≤ 1 := by simpa using hs
    have h1 : HasDerivAt (fun s : ℝ => U1 (zbar + s • z)) (U2 (zbar + s • z) z) s :=
      (hU1 s hs').comp_hasDerivAt s (hpath s)
    have h2 := HasDerivAt.clm_apply (c := fun s : ℝ => U1 (zbar + s • z)) (u := fun _ => z) h1
      (hasDerivAt_const s z)
    refine h2.congr_deriv ?_
    simp
  · have hs' : |s| ≤ 1 := by simpa using hs
    have e : U2 (zbar + s • z) z z - U2 (zbar + (0 : ℝ) • z) z z =
        (U2 (zbar + s • z) - U2 zbar) z z := by simp
    rw [e]
    calc |(U2 (zbar + s • z) - U2 zbar) z z|
        ≤ ‖U2 (zbar + s • z) - U2 zbar‖ * ‖z‖ * ‖z‖ := by
          simpa [Real.norm_eq_abs] using
            ContinuousLinearMap.le_opNorm₂ (U2 (zbar + s • z) - U2 zbar) z z
      _ ≤ C * ‖z‖ * ‖z‖ := by gcongr; exact hC s hs'
      _ = C * ‖z‖ ^ 2 := by ring

/-- Woodford (2003), eq. (1.2), p. 385, with a Lipschitz Hessian: if on the ball `B(z̄, δ)`
`U` has derivatives `U1`, U2 with `‖U2 w − U2 z̄‖ ≤ K ‖w − z̄‖` (`K ≥ 0`), then for
`‖z‖ < δ`, `|U(z̄ + z) − (Ū + U_z z + ½ z′U_zz z)| ≤ K ‖z‖³`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem taylor2_multivar_bound {U : F → ℝ} {U1 : F → F →L[ℝ] ℝ}
    {U2 : F → F →L[ℝ] F →L[ℝ] ℝ} {zbar : F} {δ K : ℝ} (hK0 : 0 ≤ K)
    (hU : ∀ w ∈ Metric.ball zbar δ, HasFDerivAt U (U1 w) w)
    (hU1 : ∀ w ∈ Metric.ball zbar δ, HasFDerivAt U1 (U2 w) w)
    (hK : ∀ w ∈ Metric.ball zbar δ, ‖U2 w - U2 zbar‖ ≤ K * ‖w - zbar‖)
    {z : F} (hz : ‖z‖ < δ) :
    |U (zbar + z) - quadApprox (U zbar) (U1 zbar) (U2 zbar) z| ≤ K * ‖z‖ ^ 3 := by
  have hmem : ∀ s : ℝ, |s| ≤ 1 → zbar + s • z ∈ Metric.ball zbar δ := fun s hs => by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |s| * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < δ := by simpa using hz
  have key := taylor2_multivar_segment_le (C := K * ‖z‖)
    (fun s hs => hU _ (hmem s hs)) (fun s hs => hU1 _ (hmem s hs)) (fun s hs => ?_)
  · calc _ ≤ K * ‖z‖ * ‖z‖ ^ 2 := key
      _ = K * ‖z‖ ^ 3 := by ring
  · calc ‖U2 (zbar + s • z) - U2 zbar‖ ≤ K * ‖zbar + s • z - zbar‖ := hK _ (hmem s hs)
      _ = K * (|s| * ‖z‖) := by rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      _ ≤ K * (1 * ‖z‖) := by gcongr
      _ = K * ‖z‖ := by ring

/-- Woodford (2003), eq. (1.2), p. 385, for `C³` welfare: the second-order Taylor remainder
`U(z̄ + z) − (Ū + U_z z + ½ z′U_zz z)` is `O(‖z‖³)` as `z → 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem taylor2_multivar_isBigO_of_contDiff {U : F → ℝ} (hU : ContDiff ℝ 3 U) (zbar : F) :
    (fun z => U (zbar + z) - quadApprox (U zbar) (fderiv ℝ U zbar)
      (fderiv ℝ (fderiv ℝ U) zbar) z) =O[𝓝 0] (fun z => ‖z‖ ^ 3) := by
  have h1 : ContDiff ℝ 2 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ U)) := h1.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h2.contDiffAt.exists_lipschitzOnWith (x := zbar)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht
  refine IsBigO.of_bound K ?_
  filter_upwards [Metric.ball_mem_nhds (0 : F) hδ] with z hz
  have hz' : ‖z‖ < δ := by simpa using hz
  have key := taylor2_multivar_bound (U1 := fderiv ℝ U) (U2 := fderiv ℝ (fderiv ℝ U))
    (zbar := zbar) (δ := δ) K.coe_nonneg
    (fun w _ => (hU.differentiable (by norm_num) w).hasFDerivAt)
    (fun w _ => (h1.differentiable (by norm_num) w).hasFDerivAt) (fun w hw => ?_) hz'
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_norm]
    exact key
  · have := hK.dist_le_mul w (hball hw) zbar (hball (Metric.mem_ball_self hδ))
    simpa [dist_eq_norm] using this

variable {Ω : Type*} [Fintype Ω]

variable {X Ξ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- Woodford (2003), eq. (1.4), p. 386: the linear approximation `x̃⁽¹⁾ = x̃⁰ + A ξ`, paired
with the disturbance: `z⁽¹⁾ = (x̃⁰ + A ξ, ξ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
def linSol (x0 : X) (A : Ξ →L[ℝ] X) (ξ : Ω → Ξ) (ω : Ω) : X × Ξ := (x0 + A (ξ ω), ξ ω)

/-- Woodford (2003), p. 386, CORRECTED: `U⁽¹⁾` is the expected quadratic approximation evaluated
at the linear solution, `E[Ū + U_z z⁽¹⁾ + ½ z⁽¹⁾′U_zz z⁽¹⁾]`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def U1 (p : Ω → ℝ) (u0 : ℝ) (L : X × Ξ →L[ℝ] ℝ)
    (B : X × Ξ →L[ℝ] X × Ξ →L[ℝ] ℝ) (x0 : X) (A : Ξ →L[ℝ] X) (ξ : Ω → Ξ) : ℝ :=
  expect p (fun ω => quadApprox u0 L B (linSol x0 A ξ ω))

end ApproxTheory

namespace TwoSectorWelfare

open Filter Topology
open SeqW
open ExpLogCES (crossMean crossVar crossVar_eq cesMoment cesMoment_pos cesIndex log_cesIndex_exp
    cumulant)
open Moments (mean_quadratic sum_sq_eq calvoKappa)
open Prop61 (Tu Tv xStarLin)
variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), App. E.6, p. 704: (E.29) integrated over a sector, in terms of the
sectoral mean `m = E_iʲ ŷ` and variance `V = var_iʲ ŷ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def TvSec (ω Phi q m V : ℝ) : ℝ :=
  (1 - Phi) * m + (1 + ω) / 2 * (m ^ 2 + V) - ω * q * m

/-- Woodford (2003), App. E.6, p. 704 ("integrating (E.29) over the goods `i` belonging to
sector `j`"): `∑ w_i Tv(ŷ_i) = TvSec(E ŷ, var ŷ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem sum_Tv {w : ι → ℝ} (hw : ∑ i, w i = 1) (ω Phi q : ℝ) (y : ι → ℝ) :
    ∑ i, w i * Tv Phi ω q (y i) = TvSec ω Phi q (crossMean w y) (crossVar w y) := by
  have h : ∀ i, w i * Tv Phi ω q (y i) =
      w i * ((1 - Phi - ω * q) * y i + (1 + ω) / 2 * y i ^ 2) := fun i => by unfold Tv; ring
  simp only [h, mean_quadratic hw]
  unfold TvSec; ring

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

end TwoSectorWelfare

namespace Links

open Filter Topology Asymptotics MeasureTheory
open SeqW (Bdd)
namespace CES

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), eq. (E.5), p. 694: the CES atom
`r_C = E_i ŷ − [Ŷ − ½(1 − θ⁻¹) var_i ŷ]`, where `Ŷ = log(Y/Ȳ)` is the log of the Dixit–Stiglitz
index (exponent `1 − θ⁻¹`) of `y(i)/Ȳ = e^{ŷ(i)}`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def cesAtom (w : ι → ℝ) (θ : ℝ) (yh : ι → ℝ) : ℝ :=
  ExpLogCES.crossMean w yh -
    (Real.log (ExpLogCES.cesIndex w (1 - θ⁻¹) (fun i => Real.exp (yh i))) -
      (1 - θ⁻¹) / 2 * ExpLogCES.crossVar w yh)

/-- Woodford (2003), eq. (E.5), p. 694 (exact, by definition of the atom):
`E_i ŷ = Ŷ − ½(1 − θ⁻¹) var_i ŷ + r_C`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem ces_relation (w : ι → ℝ) (θ : ℝ) (yh : ι → ℝ) :
    ExpLogCES.crossMean w yh =
      Real.log (ExpLogCES.cesIndex w (1 - θ⁻¹) (fun i => Real.exp (yh i))) -
        (1 - θ⁻¹) / 2 * ExpLogCES.crossVar w yh + cesAtom w θ yh := by
  unfold cesAtom; ring

/-- Woodford (2003), eq. (E.5), p. 694 (the "O(‖ŷ‖³)" of the CES expansion): the atom r_C is
of third order, from `ExpLogCES.log_outputIndex_expansion`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem cesAtom_isBigO {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ}
    (hθ1 : θ ≠ 1) : cesAtom w θ =O[𝓝 0] fun yh => ‖yh‖ ^ 3 :=
  (ExpLogCES.log_outputIndex_expansion hw hw1 hθ1).neg_left.congr_left fun yh => by
    unfold cesAtom; ring

end CES

variable {G : Type*} [MeasurableSpace G]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

end Links

end Woodford.GainsFromCommitment.TidyR6WelfBase
