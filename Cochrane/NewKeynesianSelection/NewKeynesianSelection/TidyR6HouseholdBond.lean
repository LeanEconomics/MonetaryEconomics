/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.TidyR6ExpectationsMeasureIID
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Convex.Deriv
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The household problem under uncertainty on a genuine probability space

Restated from the Cochrane IntertemporalModel project (its module HouseholdMeasure, with the
three lemmas it uses from its module Valuation) with the namespace renamed, for the household
problem behind Cochrane (2023), eq. (16.25), p. 377 (module TidyR6Household16_25).

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1, pp. 21–22 (the
household maximises `E ∑ β^t u(c_t)` subject to (2.2); "the consumer's first-order conditions"
give the bond price (2.3)), in the measure-theoretic setting of TidyR6ExpectationsMeasure: a
probability space with a filtration, `E_t = μ[· | 𝓕_t]`, and every constraint holding almost
surely. Information may grow forever, as in the i.i.d. economy of
TidyR6ExpectationsMeasureIID.

## The household problem

* `Feasible`: consumption adapted, bonds bought at `n` known at `n`, the flow constraint
  `B_{n−1} + P_n y = P_n c_n + P_n s_n + Q_n B_n` (bonds, endowment, taxes) almost surely at
  every date, and `B_n ≥ 0` almost surely.
* `Admissible`: expected discounted utility converges absolutely,
  `E ∑_n β^n |u(c_n)| < ∞`; `expUtil` is then the genuine integral `E ∑_n β^n u(c_n)`.
* `Optimal`: feasible, admissible, and no feasible admissible plan has higher expected utility.

## Main results

* `admissible_modify`: changing a plan at finitely many dates changes expected utility by the
  integrals of the utility changes at those dates.
* `foc_le`: the variational inequality along every bounded `𝓕_t`-measurable deviation of bond
  holdings that keeps debt nonnegative for small steps (differentiation under the integral sign).
* `euler_kkt`: the Euler inequality `Q_t u'(c_t)/P_t ≥ β E_t[u'(c_{t+1})/P_{t+1}]` holds almost
  surely at every date (buying more bonds is always feasible); `euler_interior`: the Euler
  equation holds almost surely on the event `{B_t > 0}`; `euler_of_pos`: it holds almost surely
  when `B_t > 0` almost surely.
* `E_pos`: the conditional expectation of an almost surely positive integrable variable is
  almost surely positive. Hence `bondPrice_pos`: optimisation forces `Q_t > 0` almost surely at
  every date, interior or not; `bondPrice_formula`: on `{B_t > 0}`,
  `Q_t = β E_t[u'(c_{t+1})/u'(c_t) · P_t/P_{t+1}]`; `bondPrice_pos_of_formula`,
  `rate_gt_neg_one_of_formula`: any bond price of that form is positive, so `i_t > −1`.
-/

namespace Cochrane.NewKeynesianSelection.TidyR6HouseholdBond

open MeasureTheory ProbabilityTheory Filter Topology TidyR6ExpectationsMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Restated from the Chapter 2 project (its module Valuation) -/

/-- Cochrane (2023), p. 22 (modifying a plan at finitely many dates): if `f'` agrees with the
summable `f` off a finite set `S`, then `∑ f' = ∑ f + ∑_{n ∈ S} (f' n − f n)`. -/
theorem hasSum_of_eq_off_finset {f f' : ℕ → ℝ} (hf : Summable f) (S : Finset ℕ)
    (h : ∀ n ∉ S, f' n = f n) : HasSum f' (∑' n, f n + ∑ n ∈ S, (f' n - f n)) := by
  have h2 : HasSum (fun n => f' n - f n) (∑ n ∈ S, (f' n - f n)) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by rw [h n hn, sub_self]
  convert hf.hasSum.add h2 using 1
  funext n
  ring

/-- Cochrane (2023), Online Appendix A1.1, p. 556 (concave utility): for `u` concave on `ℝ` with
derivative `g` at `x`, the tangent line lies above the graph, `u c ≤ u x + g (c − x)`. -/
theorem concave_le_tangent {u : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ u) {x g : ℝ}
    (hg : HasDerivAt u g x) (c : ℝ) : u c ≤ u x + g * (c - x) := by
  rcases lt_trichotomy c x with h | h | h
  · have := hc.le_slope_of_hasDerivAt (Set.mem_univ c) (Set.mem_univ x) h hg
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith
  · subst h
    simp
  · have := hc.slope_le_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ c) h hg
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

/-- Cochrane (2023), Online Appendix A1.1, p. 556: a monotone function has a nonnegative
derivative wherever it is differentiable. -/
theorem deriv_nonneg_of_monotone {u : ℝ → ℝ} (hm : Monotone u) {x g : ℝ}
    (hg : HasDerivAt u g x) : 0 ≤ g := by
  have h := hg.tendsto_slope_zero_right
  refine ge_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) < t := ht
  have : u x ≤ u (x + t) := hm (by linarith)
  have : 0 ≤ t⁻¹ * (u (x + t) - u x) :=
    mul_nonneg (inv_nonneg.mpr ht'.le) (by linarith)
  simpa [smul_eq_mul] using this


/-! ### Measure-theoretic tools -/

/-- Cochrane (2023), p. 21 (expected discounted utility is an infinite sum): an almost surely
convergent series of a.e. strongly measurable variables is a.e. strongly measurable. -/
theorem aestronglyMeasurable_tsum {μ : Measure Ω} {f : ℕ → Ω → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (f n) μ) (hs : ∀ᵐ ω ∂μ, Summable fun n => f n ω) :
    AEStronglyMeasurable (fun ω => ∑' n, f n ω) μ :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun N ω => ∑ n ∈ Finset.range N, f n ω)
    (fun _ => Finset.aestronglyMeasurable_fun_sum _ fun n _ => hm n)
    (hs.mono fun _ h => h.hasSum.tendsto_sum_nat)

/-- Cochrane (2023), p. 21: a continuous function of an essentially bounded variable is
integrable on a probability space. -/
theorem integrable_comp_of_bdd {μ : Measure Ω} [IsFiniteMeasure μ] {v : ℝ → ℝ}
    (hv : Continuous v) {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {R : ℝ}
    (hR : ∀ᵐ ω ∂μ, |f ω| ≤ R) : Integrable (fun ω => v (f ω)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hv.continuousOn
  exact Integrable.of_bound (hv.comp_aestronglyMeasurable hf) C
    (hR.mono fun ω h => hC _ (Set.mem_Icc.2 (abs_le.1 h)))

/-- Cochrane (2023), p. 21: a continuous function is bounded on `[−R, R]`. -/
theorem exists_abs_le_of_continuous {v : ℝ → ℝ} (hv : Continuous v) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x, |x| ≤ R → |v x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hv.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have := hC x (Set.mem_Icc.2 (abs_le.1 hx))
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- Cochrane (2023), p. 21 ("the consumer's first-order conditions"): differentiation of
expected utility under the integral sign. If `v` is differentiable with continuous derivative
`v'` and `f`, `g` are essentially bounded, then `ε ↦ E v(f + εg)` has derivative `E[v'(f) g]`
at `0`. -/
theorem hasDerivAt_integral_comp {μ : Measure Ω} [IsFiniteMeasure μ] {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : Continuous v') {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {Mf Mg : ℝ}
    (hfM : ∀ᵐ ω ∂μ, |f ω| ≤ Mf) (hgM : ∀ᵐ ω ∂μ, |g ω| ≤ Mg) :
    HasDerivAt (fun ε => ∫ ω, v (f ω + ε * g ω) ∂μ) (∫ ω, v' (f ω) * g ω ∂μ) 0 := by
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun x => (hv x).continuousAt
  obtain ⟨C, hC0, hC⟩ := exists_abs_le_of_continuous hv' (Mf + Mg)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun ε ω => v (f ω + ε * g ω)) (F' := fun ε ω => v' (f ω + ε * g ω) * g ω)
    (bound := fun _ => C * Mg) (s := Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun ε => hvc.comp_aestronglyMeasurable (hf.add (hg.const_mul ε)))
    (by simpa using integrable_comp_of_bdd hvc hf hfM)
    ((hv'.comp_aestronglyMeasurable (hf.add (hg.const_mul 0))).mul hg) ?_
    (integrable_const _) ?_
  · simpa using key.2
  · filter_upwards [hfM, hgM] with ω h1 h2
    intro ε hε
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
    rw [Real.norm_eq_abs, abs_mul]
    have hMg : 0 ≤ Mg := (abs_nonneg _).trans h2
    have hx : |f ω + ε * g ω| ≤ Mf + Mg := by
      calc |f ω + ε * g ω| ≤ |f ω| + |ε| * |g ω| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ Mf + 1 * Mg :=
            add_le_add h1 (mul_le_mul hε.le h2 (abs_nonneg _) zero_le_one)
        _ = Mf + Mg := by ring
    exact mul_le_mul (hC _ hx) h2 (abs_nonneg _) hC0
  · refine Eventually.of_forall fun ω ε _ => ?_
    have h1 : HasDerivAt (fun ε => f ω + ε * g ω) (g ω) ε := by
      simpa using (hasDerivAt_mul_const (g ω)).const_add (f ω)
    exact (hv _).comp ε h1

/-- Cochrane (2023), p. 21 (no profitable deviation in one direction): if `φ(0) = 0`,
`φ(ε) ≤ 0` for small `ε > 0`, and `φ` has derivative `D` at `0`, then `D ≤ 0`. -/
theorem deriv_nonpos_of_le {φ : ℝ → ℝ} {D η : ℝ} (hφ : HasDerivAt φ D 0) (h0 : φ 0 = 0)
    (hη : 0 < η) (hle : ∀ ε, 0 < ε → ε < η → φ ε ≤ 0) : D ≤ 0 := by
  refine le_of_tendsto hφ.tendsto_slope_zero_right ?_
  filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
  simp only [zero_add, h0, sub_zero, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hε.1.le) (hle ε hε.1 hε.2)

/-! ### The household problem -/

variable (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), eq. (2.2), p. 21, under uncertainty on a probability space: a household plan
`(c, b)` (`b n = B_{n−1}`, no money held) is feasible from initial debt `b₀` if consumption is
adapted, the bonds bought at `n` are known at `n`, the flow constraint
`B_{n−1} + P_n y = P_n c_n + P_n s_n + Q_n B_n` (bonds, endowment `y`, taxes net of transfers
`s_n`) holds almost surely at every date, and `B_n ≥ 0` almost surely. -/
def Feasible (y : ℝ) (P s Q : ℕ → Ω → ℝ) (b₀ : Ω → ℝ) (c b : ℕ → Ω → ℝ) : Prop :=
  b 0 = b₀ ∧ StronglyAdapted S.𝓕 c ∧ (∀ n, StronglyMeasurable[S.𝓕 n] (b (n + 1))) ∧
    (∀ n, ∀ᵐ ω ∂S.μ,
      b n ω + P n ω * y = P n ω * c n ω + P n ω * s n ω + Q n ω * b (n + 1) ω) ∧
    ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ b n ω

/-- Cochrane (2023), p. 21, "maximizes `E ∑ β^t u(c_t)`": the plan's expected discounted utility
converges absolutely, `E ∑_n β^n |u(c_n)| < ∞` (each `u(c_n)` a.e. measurable, the series
almost surely convergent and its sum integrable). -/
def Admissible (β : ℝ) (u : ℝ → ℝ) (c : ℕ → Ω → ℝ) : Prop :=
  (∀ n, AEStronglyMeasurable (fun ω => u (c n ω)) S.μ) ∧
    (∀ᵐ ω ∂S.μ, Summable fun n => β ^ n * |u (c n ω)|) ∧
    Integrable (fun ω => ∑' n, β ^ n * |u (c n ω)|) S.μ

/-- Cochrane (2023), p. 21: expected discounted utility `E ∑_t β^t u(c_t)`, a genuine integral
of the realised discounted utility. -/
noncomputable def expUtil (β : ℝ) (u : ℝ → ℝ) (c : ℕ → Ω → ℝ) : ℝ :=
  ∫ ω, ∑' n, β ^ n * u (c n ω) ∂S.μ

/-- Cochrane (2023), p. 21, "A representative household maximizes `E ∑ β^t u(c_t)`": a feasible,
admissible plan that no feasible, admissible plan beats. -/
def Optimal (β y : ℝ) (u : ℝ → ℝ) (P s Q : ℕ → Ω → ℝ) (b₀ : Ω → ℝ) (c b : ℕ → Ω → ℝ) :
    Prop :=
  Feasible S y P s Q b₀ c b ∧ Admissible S β u c ∧
    ∀ c' b', Feasible S y P s Q b₀ c' b' → Admissible S β u c' →
      expUtil S β u c' ≤ expUtil S β u c

variable {S}

/-- Cochrane (2023), p. 21: an admissible plan has an almost surely convergent discounted
utility series. -/
theorem Admissible.summable {β : ℝ} (hβ : 0 ≤ β) {u : ℝ → ℝ} {c : ℕ → Ω → ℝ}
    (h : Admissible S β u c) : ∀ᵐ ω ∂S.μ, Summable fun n => β ^ n * u (c n ω) :=
  h.2.1.mono fun _ hs => Summable.of_norm_bounded hs fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ]

/-- Cochrane (2023), p. 21: in an admissible plan each period's utility is integrable. -/
theorem Admissible.integrable {β : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} {c : ℕ → Ω → ℝ}
    (h : Admissible S β u c) (n : ℕ) : Integrable (fun ω => u (c n ω)) S.μ := by
  refine Integrable.mono' (h.2.2.const_mul (β ^ n)⁻¹) (h.1 n) ?_
  filter_upwards [h.2.1] with ω hs
  have hbn : 0 < β ^ n := pow_pos hβ n
  have hle : β ^ n * |u (c n ω)| ≤ ∑' m, β ^ m * |u (c m ω)| :=
    hs.le_tsum n fun m _ => mul_nonneg (pow_nonneg hβ.le m) (abs_nonneg _)
  rw [Real.norm_eq_abs, le_inv_mul_iff₀ hbn]
  exact hle

/-- Cochrane (2023), p. 21: the realised discounted utility of an admissible plan is integrable,
so `expUtil` is a genuine expectation. -/
theorem Admissible.integrable_sum {β : ℝ} (hβ : 0 ≤ β) {u : ℝ → ℝ} {c : ℕ → Ω → ℝ}
    (h : Admissible S β u c) : Integrable (fun ω => ∑' n, β ^ n * u (c n ω)) S.μ := by
  refine Integrable.mono' h.2.2
    (aestronglyMeasurable_tsum (fun n => (h.1 n).const_mul _) (h.summable hβ)) ?_
  filter_upwards [h.2.1] with ω hs
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · refine hs.congr fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ]
  · refine tsum_congr fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ]

/-- Cochrane (2023), p. 22 (modifying a plan at finitely many dates): if `c'` agrees with the
admissible `c` off the finite set of dates `F` and `u(c'_n)` is integrable for `n ∈ F`, then `c'`
is admissible and `E ∑ β^n u(c'_n) = E ∑ β^n u(c_n) + ∑_{n ∈ F} β^n (E u(c'_n) − E u(c_n))`. -/
theorem admissible_modify {β : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} {c c' : ℕ → Ω → ℝ}
    (hc : Admissible S β u c) (F : Finset ℕ) (heq : ∀ n ∉ F, c' n = c n)
    (hi : ∀ n ∈ F, Integrable (fun ω => u (c' n ω)) S.μ) :
    Admissible S β u c' ∧
      expUtil S β u c' = expUtil S β u c +
        ∑ n ∈ F, β ^ n * (∫ ω, u (c' n ω) ∂S.μ - ∫ ω, u (c n ω) ∂S.μ) := by
  have hci := hc.integrable hβ
  have hm : ∀ n, AEStronglyMeasurable (fun ω => u (c' n ω)) S.μ := fun n => by
    by_cases hn : n ∈ F
    · exact (hi n hn).aestronglyMeasurable
    · rw [heq n hn]
      exact hc.1 n
  have habs : ∀ᵐ ω ∂S.μ, HasSum (fun n => β ^ n * |u (c' n ω)|)
      (∑' n, β ^ n * |u (c n ω)| + ∑ n ∈ F, (β ^ n * |u (c' n ω)| - β ^ n * |u (c n ω)|)) := by
    filter_upwards [hc.2.1] with ω hs
    exact hasSum_of_eq_off_finset hs F fun n hn => by rw [heq n hn]
  have hsgn : ∀ᵐ ω ∂S.μ, HasSum (fun n => β ^ n * u (c' n ω))
      (∑' n, β ^ n * u (c n ω) + ∑ n ∈ F, (β ^ n * u (c' n ω) - β ^ n * u (c n ω))) := by
    filter_upwards [hc.summable hβ.le] with ω hs
    exact hasSum_of_eq_off_finset hs F fun n hn => by rw [heq n hn]
  have hFi : Integrable (fun ω =>
      ∑ n ∈ F, (β ^ n * |u (c' n ω)| - β ^ n * |u (c n ω)|)) S.μ :=
    integrable_finsetSum F fun n hn =>
      (((hi n hn).abs).const_mul _).sub (((hci n).abs).const_mul _)
  refine ⟨⟨hm, habs.mono fun _ h => h.summable, ?_⟩, ?_⟩
  · refine (hc.2.2.add hFi).congr ?_
    filter_upwards [habs] with ω h
    exact h.tsum_eq.symm
  · have hFi' : ∀ n ∈ F, Integrable (fun ω => β ^ n * u (c' n ω) - β ^ n * u (c n ω)) S.μ :=
      fun n hn => ((hi n hn).const_mul _).sub ((hci n).const_mul _)
    unfold expUtil
    rw [integral_congr_ae (hsgn.mono fun _ h => h.tsum_eq), integral_add
      (hc.integrable_sum hβ.le) (integrable_finsetSum F hFi'), integral_finsetSum F hFi']
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [integral_sub ((hi n hn).const_mul _) ((hci n).const_mul _), integral_const_mul,
      integral_const_mul, mul_sub]

/-! ### Essentially bounded variables -/

variable (S)

/-- Cochrane (2023), p. 21: an essentially bounded variable, `|f| ≤ M` almost surely. -/
def BddAt (f : Ω → ℝ) : Prop := ∃ M, ∀ᵐ ω ∂S.μ, |f ω| ≤ M

variable {S}

/-- Cochrane (2023), p. 21: products of essentially bounded variables are essentially bounded. -/
theorem BddAt.mul {f g : Ω → ℝ} (hf : BddAt S f) (hg : BddAt S g) :
    BddAt S (fun ω => f ω * g ω) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M * N, ?_⟩
  filter_upwards [hM, hN] with ω h1 h2
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

/-- Cochrane (2023), p. 21: sums of essentially bounded variables are essentially bounded. -/
theorem BddAt.add {f g : Ω → ℝ} (hf : BddAt S f) (hg : BddAt S g) :
    BddAt S (fun ω => f ω + g ω) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M + N, ?_⟩
  filter_upwards [hM, hN] with ω h1 h2
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- Cochrane (2023), p. 21: negatives of essentially bounded variables are essentially
bounded. -/
theorem BddAt.neg {f : Ω → ℝ} (hf : BddAt S f) : BddAt S (fun ω => -f ω) := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, hM.mono fun ω h => by rwa [abs_neg]⟩

/-- Cochrane (2023), p. 21: constants are essentially bounded. -/
theorem BddAt.const (a : ℝ) : BddAt S (fun _ => a) :=
  ⟨|a|, Eventually.of_forall fun _ => le_rfl⟩

/-- Cochrane (2023), p. 21: a continuous function of an essentially bounded variable is
essentially bounded. -/
theorem BddAt.comp {v : ℝ → ℝ} (hv : Continuous v) {f : Ω → ℝ} (hf : BddAt S f) :
    BddAt S (fun ω => v (f ω)) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨C, -, hC⟩ := exists_abs_le_of_continuous hv M
  exact ⟨C, hM.mono fun ω h => hC _ h⟩

/-- Cochrane (2023), p. 21: forecasts of essentially bounded variables are essentially
bounded. -/
theorem BddAt.E {f : Ω → ℝ} (hf : BddAt S f) (t : ℕ) : BddAt S (S.E t f) := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, S.abs_E_le hM t⟩

/-- Cochrane (2023), p. 21: an a.e. measurable, essentially bounded variable is integrable. -/
theorem BddAt.integrable {f : Ω → ℝ} (hf : BddAt S f) (hm : AEStronglyMeasurable f S.μ) :
    Integrable f S.μ := by
  obtain ⟨M, hM⟩ := hf
  exact Integrable.of_bound hm M (hM.mono fun ω h => by rwa [Real.norm_eq_abs])

/-- Cochrane (2023), p. 21: an essentially bounded variable has a positive bound. -/
theorem BddAt.exists_pos {f : Ω → ℝ} (hf : BddAt S f) : ∃ M, 0 < M ∧ ∀ᵐ ω ∂S.μ, |f ω| ≤ M := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨max M 1, by positivity, hM.mono fun ω h => h.trans (le_max_left _ _)⟩

/-! ### The Euler equation, derived by perturbation -/

/-- Cochrane (2023), p. 21: `∫ z X = ∫ z E_t X` for a bounded `𝓕_t`-measurable `z` and an
integrable `X` (the law of iterated expectations with pull-out). -/
theorem integral_mul_E {t : ℕ} {z X : Ω → ℝ} (hz : StronglyMeasurable[S.𝓕 t] z) {K : ℝ}
    (hzK : ∀ᵐ ω ∂S.μ, |z ω| ≤ K) (hX : Integrable X S.μ) :
    ∫ ω, z ω * X ω ∂S.μ = ∫ ω, z ω * S.E t X ω ∂S.μ := by
  rw [← S.integral_E t (fun ω => z ω * X ω)]
  exact integral_congr_ae (S.E_pullOut hz hzK hX)

variable (S)

/-- Cochrane (2023), p. 21: the regularity used for the Euler equation at date `t`: consumption
at `t` and `t + 1`, the bond price at `t`, and `1/P_t`, `1/P_{t+1}` are essentially bounded. -/
def EulerRegular (P Q c : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  BddAt S (c t) ∧ BddAt S (c (t + 1)) ∧ BddAt S (Q t) ∧ BddAt S (fun ω => (P t ω)⁻¹) ∧
    BddAt S (fun ω => (P (t + 1) ω)⁻¹)

/-- Cochrane (2023), p. 21: the Euler gap `Q_t u'(c_t)/P_t − β E_t[u'(c_{t+1})/P_{t+1}]`, the
marginal utility cost of a bond less its expected discounted marginal utility payoff. -/
noncomputable def eulerGap (β : ℝ) (u' : ℝ → ℝ) (P Q c : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => Q t ω * (u' (c t ω) / P t ω) -
    β * S.E t (fun ω => u' (c (t + 1) ω) / P (t + 1) ω) ω

variable {S}

/-- Cochrane (2023), p. 21: the deviation in consumption, `ε z` fewer bonds bought at `t`:
consume `ε Q_t z/P_t` more at `t` and `ε z/P_{t+1}` less at `t + 1`. -/
noncomputable def devC (P Q c : ℕ → Ω → ℝ) (z : Ω → ℝ) (t : ℕ) (ε : ℝ) : ℕ → Ω → ℝ :=
  fun n ω => if n = t then c t ω + ε * (Q t ω * z ω * (P t ω)⁻¹)
    else if n = t + 1 then c (t + 1) ω + ε * -(z ω * (P (t + 1) ω)⁻¹) else c n ω

/-- Cochrane (2023), p. 21: the deviation in bonds, `B_t − ε z`. -/
noncomputable def devB (b : ℕ → Ω → ℝ) (z : Ω → ℝ) (t : ℕ) (ε : ℝ) : ℕ → Ω → ℝ :=
  fun n ω => if n = t + 1 then b (t + 1) ω - ε * z ω else b n ω

/-- Cochrane (2023), eq. (2.2), p. 21: the deviation `(devC, devB)` satisfies the flow constraint
at every date, is adapted, and is feasible whenever it keeps `B_t − εz ≥ 0` almost surely. -/
theorem dev_feasible {y : ℝ} {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hf : Feasible S y P s Q b₀ c b) (hPad : StronglyAdapted S.𝓕 P) {t : ℕ}
    (hQt : StronglyMeasurable[S.𝓕 t] (Q t)) (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) {z : Ω → ℝ}
    (hz : StronglyMeasurable[S.𝓕 t] z) {ε : ℝ} (hnn : ∀ᵐ ω ∂S.μ, 0 ≤ b (t + 1) ω - ε * z ω) :
    Feasible S y P s Q b₀ (devC P Q c z t ε) (devB b z t ε) := by
  obtain ⟨hb0, hcad, hbad, hflow, hbnn⟩ := hf
  have hz1 : StronglyMeasurable[S.𝓕 (t + 1)] z := hz.mono (S.𝓕.mono (Nat.le_succ t))
  refine ⟨?_, fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_⟩
  · funext ω
    simp only [devB, (show (0 : ℕ) ≠ t + 1 by omega), ↓reduceIte]
    rw [hb0]
  · by_cases hn : n = t
    · subst hn
      have e : devC P Q c z n ε n = fun ω => c n ω + ε * (Q n ω * z ω * (P n ω)⁻¹) := by
        funext ω
        simp [devC]
      rw [e]
      exact (hcad n).add (((hQt.measurable.mul hz.measurable).mul
        (hPad n).measurable.inv).stronglyMeasurable.const_mul ε)
    · by_cases hn1 : n = t + 1
      · subst hn1
        have e : devC P Q c z t ε (t + 1) =
            fun ω => c (t + 1) ω + ε * -(z ω * (P (t + 1) ω)⁻¹) := by
          funext ω
          simp [devC]
        rw [e]
        exact (hcad (t + 1)).add ((hz1.measurable.mul
          (hPad (t + 1)).measurable.inv).neg.stronglyMeasurable.const_mul ε)
      · have e : devC P Q c z t ε n = c n := by
          funext ω
          simp [devC, hn, hn1]
        rw [e]
        exact hcad n
  · by_cases hn : n + 1 = t + 1
    · have hnt : n = t := by omega
      subst hnt
      have e : devB b z n ε (n + 1) = fun ω => b (n + 1) ω - ε * z ω := by
        funext ω
        simp [devB]
      rw [e]
      exact (hbad n).sub (hz.const_mul ε)
    · have hn' : n ≠ t := by omega
      have e : devB b z t ε (n + 1) = b (n + 1) := by
        funext ω
        simp [devB, hn']
      rw [e]
      exact hbad n
  · by_cases hn : n = t
    · subst hn
      filter_upwards [hflow n, hP n] with ω h1 hp
      have hp0 := hp.ne'
      simp only [devC, devB, ↓reduceIte, (show n ≠ n + 1 by omega)]
      field_simp
      linear_combination h1
    · by_cases hn1 : n = t + 1
      · subst hn1
        filter_upwards [hflow (t + 1), hP (t + 1)] with ω h1 hp
        have hp0 := hp.ne'
        simp only [devC, devB, hn, ↓reduceIte, (show t + 1 + 1 ≠ t + 1 by omega)]
        field_simp
        linear_combination h1
      · have hn2 : n + 1 ≠ t + 1 := fun h => hn (by omega)
        filter_upwards [hflow n] with ω h1
        simp only [devC, devB, hn, hn1, hn2, ↓reduceIte]
        exact h1
  · by_cases hn : n = t + 1
    · subst hn
      simp only [devB, ↓reduceIte]
      exact hnn
    · simp only [devB, hn, ↓reduceIte]
      exact hbnn n

/-- Cochrane (2023), p. 21, "the consumer's first-order conditions", in variational form on a
probability space: if `(c, b)` is optimal, `u` is differentiable with continuous derivative
`u'`, prices are positive and adapted, the regularity `EulerRegular` holds at `t`, and the bounded
`𝓕_t`-measurable deviation `z` (sell `εz` bonds at `t`) keeps debt nonnegative for all small
`ε > 0`, then `E[z · (Q_t u'(c_t)/P_t − β E_t[u'(c_{t+1})/P_{t+1}])] ≤ 0`. The proof
differentiates expected utility under the integral sign. -/
theorem foc_le {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : Optimal S β y u P s Q b₀ c b) (hPad : StronglyAdapted S.𝓕 P)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) {t : ℕ} (hQt : StronglyMeasurable[S.𝓕 t] (Q t))
    (hreg : EulerRegular S P Q c t) {z : Ω → ℝ} (hz : StronglyMeasurable[S.𝓕 t] z)
    (hzb : BddAt S z) {η : ℝ} (hη : 0 < η)
    (hfz : ∀ ε, 0 < ε → ε < η → ∀ᵐ ω ∂S.μ, 0 ≤ b (t + 1) ω - ε * z ω) :
    ∫ ω, z ω * eulerGap S β u' P Q c t ω ∂S.μ ≤ 0 := by
  obtain ⟨hc0, hc1, hQb, hPi0, hPi1⟩ := hreg
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  have hfeas := hopt.1
  have hcad := hfeas.2.1
  have hz1 : StronglyMeasurable[S.𝓕 (t + 1)] z := hz.mono (S.𝓕.mono (Nat.le_succ t))
  set a : Ω → ℝ := fun ω => Q t ω * z ω * (P t ω)⁻¹ with ha
  set a' : Ω → ℝ := fun ω => -(z ω * (P (t + 1) ω)⁻¹) with ha'
  have ham : AEStronglyMeasurable a S.μ :=
    ((hQt.measurable.mul hz.measurable).mul (hPad t).measurable.inv).stronglyMeasurable.mono
      (S.𝓕.le t) |>.aestronglyMeasurable
  have ham' : AEStronglyMeasurable a' S.μ :=
    (hz1.measurable.mul (hPad (t + 1)).measurable.inv).neg.stronglyMeasurable.mono
      (S.𝓕.le (t + 1)) |>.aestronglyMeasurable
  have hab : BddAt S a := (hQb.mul hzb).mul hPi0
  have hab' : BddAt S a' := (hzb.mul hPi1).neg
  have hc0m : AEStronglyMeasurable (c t) S.μ := ((hcad t).mono (S.𝓕.le t)).aestronglyMeasurable
  have hc1m : AEStronglyMeasurable (c (t + 1)) S.μ :=
    ((hcad (t + 1)).mono (S.𝓕.le (t + 1))).aestronglyMeasurable
  obtain ⟨Mc0, hMc0⟩ := hc0
  obtain ⟨Mc1, hMc1⟩ := hc1
  obtain ⟨Ma, hMa⟩ := hab
  obtain ⟨Ma', hMa'⟩ := hab'
  -- integrability of the perturbed utilities
  have hint : ∀ (f g : Ω → ℝ) (Mf Mg ε : ℝ), AEStronglyMeasurable f S.μ →
      AEStronglyMeasurable g S.μ → (∀ᵐ ω ∂S.μ, |f ω| ≤ Mf) → (∀ᵐ ω ∂S.μ, |g ω| ≤ Mg) →
      Integrable (fun ω => u (f ω + ε * g ω)) S.μ := by
    intro f g Mf Mg ε hf hg hfM hgM
    refine integrable_comp_of_bdd huc (hf.add (hg.const_mul ε)) (R := Mf + |ε| * Mg) ?_
    filter_upwards [hfM, hgM] with ω h1 h2
    calc |f ω + ε * g ω| ≤ |f ω| + |ε| * |g ω| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ Mf + |ε| * Mg := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg ε))
  -- the utility of the deviation
  set φ : ℝ → ℝ := fun ε =>
    β ^ t * (∫ ω, u (c t ω + ε * a ω) ∂S.μ - ∫ ω, u (c t ω) ∂S.μ) +
      β ^ (t + 1) * (∫ ω, u (c (t + 1) ω + ε * a' ω) ∂S.μ - ∫ ω, u (c (t + 1) ω) ∂S.μ)
    with hφ
  have hval : ∀ ε, Admissible S β u (devC P Q c z t ε) ∧
      expUtil S β u (devC P Q c z t ε) = expUtil S β u c + φ ε := by
    intro ε
    have h := admissible_modify hβ hopt.2.1 {t, t + 1} (c' := devC P Q c z t ε)
      (fun n hn => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
        funext ω
        simp only [devC, hn.1, hn.2, ↓reduceIte])
      (fun n hn => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with rfl | rfl
        · simp only [devC, ↓reduceIte]
          exact hint _ _ _ _ ε hc0m ham hMc0 hMa
        · simp only [devC, (show t + 1 ≠ t by omega), ↓reduceIte]
          exact hint _ _ _ _ ε hc1m ham' hMc1 hMa')
    refine ⟨h.1, h.2.trans ?_⟩
    rw [Finset.sum_pair (show t ≠ t + 1 by omega)]
    simp only [devC, ↓reduceIte, (show t + 1 ≠ t by omega), hφ]
    rfl
  -- the derivative of the utility of the deviation
  have hd0 := hasDerivAt_integral_comp hu hu' hc0m ham hMc0 hMa
  have hd1 := hasDerivAt_integral_comp hu hu' hc1m ham' hMc1 hMa'
  have hD : HasDerivAt φ (β ^ t * ∫ ω, u' (c t ω) * a ω ∂S.μ +
      β ^ (t + 1) * ∫ ω, u' (c (t + 1) ω) * a' ω ∂S.μ) 0 :=
    ((hd0.sub_const _).const_mul (β ^ t)).add ((hd1.sub_const _).const_mul (β ^ (t + 1)))
  have hle := deriv_nonpos_of_le hD (by simp [hφ]) hη fun ε hε hεη => by
    have h1 := hopt.2.2 _ _ (dev_feasible hfeas hPad hQt hP hz (hfz ε hε hεη)) (hval ε).1
    rw [(hval ε).2] at h1
    linarith
  -- rewrite the derivative as `β^t E[z · gap]`
  set X : Ω → ℝ := fun ω => u' (c (t + 1) ω) / P (t + 1) ω with hX
  have hXb : BddAt S X := by
    have := (BddAt.comp hu' ⟨Mc1, hMc1⟩).mul hPi1
    simpa [hX, div_eq_mul_inv] using this
  have hXm : AEStronglyMeasurable X S.μ :=
    ((hu'.measurable.comp (hcad (t + 1)).measurable).div
      (hPad (t + 1)).measurable).stronglyMeasurable.mono (S.𝓕.le (t + 1)) |>.aestronglyMeasurable
  have hXi : Integrable X S.μ := hXb.integrable hXm
  obtain ⟨K, hK⟩ := hzb
  have hzm : AEStronglyMeasurable z S.μ := (hz.mono (S.𝓕.le t)).aestronglyMeasurable
  set A : Ω → ℝ := fun ω => Q t ω * (u' (c t ω) / P t ω) with hA
  have hAb : BddAt S A := by
    have := hQb.mul ((BddAt.comp hu' ⟨Mc0, hMc0⟩).mul hPi0)
    simpa [hA, div_eq_mul_inv] using this
  have hAm : AEStronglyMeasurable A S.μ :=
    (hQt.measurable.mul ((hu'.measurable.comp (hcad t).measurable).div
      (hPad t).measurable)).stronglyMeasurable.mono (S.𝓕.le t) |>.aestronglyMeasurable
  have hzA : Integrable (fun ω => z ω * A ω) S.μ :=
    (BddAt.mul ⟨K, hK⟩ hAb).integrable (hzm.mul hAm)
  have hzE : Integrable (fun ω => z ω * S.E t X ω) S.μ :=
    (BddAt.mul ⟨K, hK⟩ (hXb.E t)).integrable (hzm.mul (S.integrable_E t X).aestronglyMeasurable)
  have e1 : ∫ ω, u' (c t ω) * a ω ∂S.μ = ∫ ω, z ω * A ω ∂S.μ := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [ha, hA, div_eq_mul_inv]
    ring
  have e2 : ∫ ω, u' (c (t + 1) ω) * a' ω ∂S.μ = -∫ ω, z ω * S.E t X ω ∂S.μ := by
    rw [← integral_mul_E hz hK hXi, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [ha', hX, div_eq_mul_inv]
    ring
  have e3 : ∫ ω, z ω * eulerGap S β u' P Q c t ω ∂S.μ =
      ∫ ω, z ω * A ω ∂S.μ - β * ∫ ω, z ω * S.E t X ω ∂S.μ := by
    rw [← integral_const_mul, ← integral_sub hzA (hzE.const_mul β)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [eulerGap, hA, hX]
    ring
  rw [e1, e2] at hle
  rw [e3]
  have hbt : 0 < β ^ t := pow_pos hβ t
  have : β ^ t * (∫ ω, z ω * A ω ∂S.μ - β * ∫ ω, z ω * S.E t X ω ∂S.μ) ≤ 0 := by
    rw [pow_succ] at hle
    linarith
  by_contra hcon
  push Not at hcon
  linarith [mul_pos hbt hcon]

/-- Cochrane (2023), p. 21: the Euler gap is known at `t`. -/
theorem eulerGap_stronglyMeasurable {β : ℝ} {u' : ℝ → ℝ} (hu' : Continuous u')
    {P Q c : ℕ → Ω → ℝ} (hcad : StronglyAdapted S.𝓕 c) (hPad : StronglyAdapted S.𝓕 P) {t : ℕ}
    (hQt : StronglyMeasurable[S.𝓕 t] (Q t)) :
    StronglyMeasurable[S.𝓕 t] (eulerGap S β u' P Q c t) :=
  ((hQt.measurable.mul ((hu'.measurable.comp (hcad t).measurable).div (hPad t).measurable)).sub
    ((S.stronglyMeasurable_E t _).measurable.const_mul β)).stronglyMeasurable

/-- Cochrane (2023), p. 21: the expected discounted marginal utility of a dollar at `t + 1`,
`u'(c_{t+1})/P_{t+1}`, is essentially bounded under `EulerRegular`. -/
theorem margUtil_bdd {u' : ℝ → ℝ} (hu' : Continuous u') {P Q c : ℕ → Ω → ℝ} {t : ℕ}
    (hreg : EulerRegular S P Q c t) : BddAt S (fun ω => u' (c (t + 1) ω) / P (t + 1) ω) := by
  have := (BddAt.comp hu' hreg.2.1).mul hreg.2.2.2.2
  simpa [div_eq_mul_inv] using this

/-- Cochrane (2023), p. 21: `u'(c_{t+1})/P_{t+1}` is integrable under `EulerRegular`. -/
theorem margUtil_integrable {u' : ℝ → ℝ} (hu' : Continuous u') {P Q c : ℕ → Ω → ℝ}
    (hcad : StronglyAdapted S.𝓕 c) (hPad : StronglyAdapted S.𝓕 P) {t : ℕ}
    (hreg : EulerRegular S P Q c t) :
    Integrable (fun ω => u' (c (t + 1) ω) / P (t + 1) ω) S.μ :=
  (margUtil_bdd hu' hreg).integrable
    (((hu'.measurable.comp (hcad (t + 1)).measurable).div
      (hPad (t + 1)).measurable).stronglyMeasurable.mono (S.𝓕.le (t + 1))).aestronglyMeasurable

/-- Cochrane (2023), p. 21: the Euler gap is essentially bounded under `EulerRegular`. -/
theorem eulerGap_bdd {β : ℝ} {u' : ℝ → ℝ} (hu' : Continuous u') {P Q c : ℕ → Ω → ℝ} {t : ℕ}
    (hreg : EulerRegular S P Q c t) : BddAt S (eulerGap S β u' P Q c t) := by
  have h1 := hreg.2.2.1.mul ((BddAt.comp hu' hreg.1).mul hreg.2.2.2.1)
  have h2 := ((BddAt.const (S := S) β).mul ((margUtil_bdd hu' hreg).E t)).neg
  have := h1.add h2
  unfold eulerGap
  simpa [div_eq_mul_inv, sub_eq_add_neg] using this

/-- Cochrane (2023), p. 21, "the consumer's first-order conditions", on a probability space,
**the Euler inequality at every date**: in an optimal plan, under `EulerRegular` at `t`,
`β E_t[u'(c_{t+1})/P_{t+1}] ≤ Q_t u'(c_t)/P_t` almost surely. Buying more bonds (`z ≤ 0`) is
always feasible, so the marginal cost of a bond is at least its expected marginal payoff, even
where the household holds no bonds. -/
theorem euler_kkt {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : Optimal S β y u P s Q b₀ c b) (hPad : StronglyAdapted S.𝓕 P)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) {t : ℕ} (hQt : StronglyMeasurable[S.𝓕 t] (Q t))
    (hreg : EulerRegular S P Q c t) :
    ∀ᵐ ω ∂S.μ, β * S.E t (fun ω => u' (c (t + 1) ω) / P (t + 1) ω) ω ≤
      Q t ω * (u' (c t ω) / P t ω) := by
  set g := eulerGap S β u' P Q c t with hg
  have hgm : StronglyMeasurable[S.𝓕 t] g :=
    eulerGap_stronglyMeasurable hu' hopt.1.2.1 hPad hQt
  obtain ⟨K, -, hK⟩ := (eulerGap_bdd (β := β) hu' hreg).exists_pos
  set z : Ω → ℝ := fun ω => min (g ω) 0 with hzdef
  have hz : StronglyMeasurable[S.𝓕 t] z := (hgm.measurable.min measurable_const).stronglyMeasurable
  have hzK : ∀ᵐ ω ∂S.μ, |z ω| ≤ K := hK.mono fun ω h => by
    rcases le_total (g ω) 0 with h1 | h1
    · simpa [hzdef, min_eq_left h1] using h
    · simp only [hzdef, min_eq_right h1, abs_zero]
      exact (abs_nonneg _).trans h
  have hfz : ∀ ε, 0 < ε → ε < 1 → ∀ᵐ ω ∂S.μ, 0 ≤ b (t + 1) ω - ε * z ω := by
    intro ε hε _
    filter_upwards [hopt.1.2.2.2.2 (t + 1)] with ω hb
    have : z ω ≤ 0 := min_le_right _ _
    nlinarith
  have h := foc_le hβ hu hu' hopt hPad hP hQt hreg hz ⟨K, hzK⟩ one_pos hfz
  have hnn : 0 ≤ᵐ[S.μ] fun ω => z ω * g ω := Eventually.of_forall fun ω => by
    rcases le_total (g ω) 0 with h1 | h1
    · simp only [Pi.zero_apply, hzdef, min_eq_left h1]
      exact mul_self_nonneg _
    · simp [hzdef, min_eq_right h1]
  have hint : Integrable (fun ω => z ω * g ω) S.μ :=
    (BddAt.mul ⟨K, hzK⟩ ⟨K, hK⟩).integrable
      ((hz.mul hgm).mono (S.𝓕.le t)).aestronglyMeasurable
  have h0 : ∫ ω, z ω * g ω ∂S.μ = 0 := le_antisymm h (integral_nonneg_of_ae hnn)
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0] with ω hω
  by_contra hlt
  push Not at hlt
  have hgneg : g ω < 0 := by
    simp only [hg, eulerGap]
    linarith
  have hzg : z ω = g ω := min_eq_left hgneg.le
  have : z ω * g ω = 0 := hω
  rw [hzg] at this
  nlinarith

/-- Cochrane (2023), p. 21, "the consumer's first-order conditions", on a probability space,
**the Euler equation where bonds are held**: in an optimal plan, under `EulerRegular` at `t`,
almost surely on the event `{B_t > 0}`,
`Q_t u'(c_t)/P_t = β E_t[u'(c_{t+1})/P_{t+1}]`. The deviations are `z = 1{B_t ≥ δ}·gap`, bounded
and `𝓕_t`-measurable, feasible in both directions for small steps. -/
theorem euler_interior {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : Optimal S β y u P s Q b₀ c b) (hPad : StronglyAdapted S.𝓕 P)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) {t : ℕ} (hQt : StronglyMeasurable[S.𝓕 t] (Q t))
    (hreg : EulerRegular S P Q c t) :
    ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω →
      Q t ω * (u' (c t ω) / P t ω) = β * S.E t (fun ω => u' (c (t + 1) ω) / P (t + 1) ω) ω := by
  set g := eulerGap S β u' P Q c t with hg
  have hgm : StronglyMeasurable[S.𝓕 t] g :=
    eulerGap_stronglyMeasurable hu' hopt.1.2.1 hPad hQt
  obtain ⟨K, hK0, hK⟩ := (eulerGap_bdd (β := β) hu' hreg).exists_pos
  have key : ∀ k : ℕ, ∀ᵐ ω ∂S.μ, 1 / ((k : ℝ) + 1) ≤ b (t + 1) ω → g ω = 0 := by
    intro k
    set δ : ℝ := 1 / ((k : ℝ) + 1) with hδ
    have hδ0 : 0 < δ := by positivity
    set A : Set Ω := {ω | δ ≤ b (t + 1) ω} with hAdef
    have hA : MeasurableSet[S.𝓕 t] A :=
      measurableSet_le measurable_const (hopt.1.2.2.1 t).measurable
    set z : Ω → ℝ := A.indicator g with hzdef
    have hz : StronglyMeasurable[S.𝓕 t] z := hgm.indicator hA
    have hzK : ∀ᵐ ω ∂S.μ, |z ω| ≤ K := hK.mono fun ω h => by
      by_cases hω : ω ∈ A
      · rwa [hzdef, Set.indicator_of_mem hω]
      · rw [hzdef, Set.indicator_of_notMem hω, abs_zero]
        exact (abs_nonneg _).trans h
    have hfz : ∀ ε, 0 < ε → ε < δ / K → ∀ᵐ ω ∂S.μ, 0 ≤ b (t + 1) ω - ε * z ω := by
      intro ε hε hεδ
      filter_upwards [hK, hopt.1.2.2.2.2 (t + 1)] with ω hk hb
      by_cases hω : ω ∈ A
      · rw [hzdef, Set.indicator_of_mem hω]
        have h1 : ε * g ω ≤ ε * K :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans hk) hε.le
        have h2 : ε * K < δ := by rwa [lt_div_iff₀ hK0] at hεδ
        have h3 : δ ≤ b (t + 1) ω := hω
        linarith
      · rw [hzdef, Set.indicator_of_notMem hω, mul_zero, sub_zero]
        exact hb
    have h := foc_le hβ hu hu' hopt hPad hP hQt hreg hz ⟨K, hzK⟩ (div_pos hδ0 hK0) hfz
    have hnn : 0 ≤ᵐ[S.μ] fun ω => z ω * g ω := Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ A
      · simp only [Pi.zero_apply, hzdef, Set.indicator_of_mem hω]
        exact mul_self_nonneg _
      · simp [hzdef, Set.indicator_of_notMem hω]
    have hint : Integrable (fun ω => z ω * g ω) S.μ :=
      (BddAt.mul ⟨K, hzK⟩ ⟨K, hK⟩).integrable
        ((hz.mul hgm).mono (S.𝓕.le t)).aestronglyMeasurable
    have h0 : ∫ ω, z ω * g ω ∂S.μ = 0 := le_antisymm h (integral_nonneg_of_ae hnn)
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0] with ω hω hδb
    have hzg : z ω = g ω := by rw [hzdef, Set.indicator_of_mem (show ω ∈ A from hδb)]
    have : z ω * g ω = 0 := hω
    rw [hzg] at this
    exact mul_self_eq_zero.1 this
  filter_upwards [ae_all_iff.2 key] with ω h hb
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hb
  have := h k hk.le
  simp only [hg, eulerGap] at this
  linarith

/-- Cochrane (2023), p. 21: if the household holds bonds almost surely, the Euler equation
`Q_t u'(c_t)/P_t = β E_t[u'(c_{t+1})/P_{t+1}]` holds almost surely. -/
theorem euler_of_pos {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : Optimal S β y u P s Q b₀ c b) (hPad : StronglyAdapted S.𝓕 P)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) {t : ℕ} (hQt : StronglyMeasurable[S.𝓕 t] (Q t))
    (hreg : EulerRegular S P Q c t) (hb : ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω) :
    (fun ω => Q t ω * (u' (c t ω) / P t ω)) =ᵐ[S.μ]
      β • S.E t (fun ω => u' (c (t + 1) ω) / P (t + 1) ω) := by
  filter_upwards [euler_interior hβ hu hu' hopt hPad hP hQt hreg, hb] with ω h1 h2
  exact h1 h2

/-! ### Positivity of the bond price -/

/-- Cochrane (2023), p. 22 (`E_t` of a positive payoff is positive): the conditional expectation
of an almost surely positive integrable variable is almost surely positive. -/
theorem E_pos {X : Ω → ℝ} (hX : Integrable X S.μ) (hpos : ∀ᵐ ω ∂S.μ, 0 < X ω) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, 0 < S.E t X ω := by
  set A : Set Ω := {ω | S.E t X ω ≤ 0} with hAdef
  have hA : MeasurableSet[S.𝓕 t] A :=
    measurableSet_le (S.stronglyMeasurable_E t X).measurable measurable_const
  have hA' : MeasurableSet A := S.𝓕.le t A hA
  have h1 : ∫ ω in A, S.E t X ω ∂S.μ = ∫ ω in A, X ω ∂S.μ := setIntegral_condExp (S.𝓕.le t) hX hA
  have h2 : ∫ ω in A, S.E t X ω ∂S.μ ≤ 0 := setIntegral_nonpos hA' fun ω hω => hω
  have hnn : 0 ≤ᵐ[S.μ.restrict A] X := ae_restrict_of_ae (hpos.mono fun ω h => h.le)
  have h3 : ∫ ω in A, X ω ∂S.μ = 0 := le_antisymm (h1 ▸ h2) (integral_nonneg_of_ae hnn)
  have h4 := (setIntegral_eq_zero_iff_of_nonneg_ae hnn hX.integrableOn).1 h3
  have h5 : ∀ᵐ ω ∂S.μ.restrict A, False := by
    filter_upwards [h4, ae_restrict_of_ae hpos] with ω h h'
    rw [h, Pi.zero_apply] at h'
    exact lt_irrefl _ h'
  have h6 : S.μ.restrict A = 0 := ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 h5)
  have h7 : S.μ A = 0 := by
    rw [← Measure.restrict_apply_univ, h6, Measure.coe_zero, Pi.zero_apply]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h7] with ω hω
  exact not_le.1 hω

/-- Cochrane (2023), eq. (2.3), p. 22: **a bond price of asset-pricing form is positive** — if
`q = β E_t W` almost surely for an almost surely positive integrable payoff `W` and `β > 0`,
then `q > 0` almost surely. -/
theorem bondPrice_pos_of_formula {β : ℝ} (hβ : 0 < β) {W q : Ω → ℝ} (hW : Integrable W S.μ)
    (hWpos : ∀ᵐ ω ∂S.μ, 0 < W ω) {t : ℕ} (hq : ∀ᵐ ω ∂S.μ, q ω = β * S.E t W ω) :
    ∀ᵐ ω ∂S.μ, 0 < q ω := by
  filter_upwards [hq, E_pos hW hWpos t] with ω h1 h2
  rw [h1]
  exact mul_pos hβ h2

/-- Cochrane (2023), eq. (2.3), p. 22, derived from optimisation on a probability space: in an
optimal plan with strictly increasing utility (`u' > 0`), positive prices and `EulerRegular` at
`t`, the bond price is almost surely positive, `Q_t > 0`, at every date, whether or not bonds are
held: by `euler_kkt`, `Q_t u'(c_t)/P_t ≥ β E_t[u'(c_{t+1})/P_{t+1}] > 0` (`E_pos`). -/
theorem bondPrice_pos {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') (hu'pos : ∀ x, 0 < u' x) {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : Optimal S β y u P s Q b₀ c b) (hPad : StronglyAdapted S.𝓕 P)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) {t : ℕ} (hQt : StronglyMeasurable[S.𝓕 t] (Q t))
    (hreg : EulerRegular S P Q c t) : ∀ᵐ ω ∂S.μ, 0 < Q t ω := by
  have hX := margUtil_integrable hu' hopt.1.2.1 hPad hreg
  have hXpos : ∀ᵐ ω ∂S.μ, 0 < u' (c (t + 1) ω) / P (t + 1) ω :=
    (hP (t + 1)).mono fun ω h => div_pos (hu'pos _) h
  filter_upwards [euler_kkt hβ hu hu' hopt hPad hP hQt hreg, E_pos hX hXpos t, hP t]
    with ω h1 h2 h3
  have h4 : 0 < u' (c t ω) / P t ω := div_pos (hu'pos _) h3
  by_contra hQ
  push Not at hQ
  nlinarith [mul_pos hβ h2]

/-- Cochrane (2023), eq. (2.3), p. 22, with the stochastic discount factor, derived from
optimisation on a probability space: in an optimal plan with `u' > 0`, positive prices,
`EulerRegular` at `t` and an integrable discount-factor payoff, almost surely on `{B_t > 0}`
`Q_t = β E_t[u'(c_{t+1})/u'(c_t) · P_t/P_{t+1}]`, and this price is positive. -/
theorem bondPrice_formula {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') (hu'pos : ∀ x, 0 < u' x)
    {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ} (hopt : Optimal S β y u P s Q b₀ c b)
    (hPad : StronglyAdapted S.𝓕 P) (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) {t : ℕ}
    (hQt : StronglyMeasurable[S.𝓕 t] (Q t)) (hreg : EulerRegular S P Q c t)
    (hW : Integrable (fun ω => u' (c (t + 1) ω) / u' (c t ω) * (P t ω / P (t + 1) ω)) S.μ) :
    ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω →
      Q t ω = β * S.E t (fun ω => u' (c (t + 1) ω) / u' (c t ω) * (P t ω / P (t + 1) ω)) ω ∧
        0 < β * S.E t (fun ω => u' (c (t + 1) ω) / u' (c t ω) * (P t ω / P (t + 1) ω)) ω := by
  have hcad := hopt.1.2.1
  have hX := margUtil_integrable hu' hcad hPad hreg
  set f : Ω → ℝ := fun ω => P t ω / u' (c t ω) with hf
  have hfm : StronglyMeasurable[S.𝓕 t] f :=
    ((hPad t).measurable.div (hu'.measurable.comp (hcad t).measurable)).stronglyMeasurable
  have hWeq : (fun ω => u' (c (t + 1) ω) / u' (c t ω) * (P t ω / P (t + 1) ω)) =
      f * fun ω => u' (c (t + 1) ω) / P (t + 1) ω := by
    funext ω
    simp only [hf, Pi.mul_apply]
    ring
  have hpo := condExp_mul_of_stronglyMeasurable_left hfm (hWeq ▸ hW) hX
  have hWpos : ∀ᵐ ω ∂S.μ, 0 < u' (c (t + 1) ω) / u' (c t ω) * (P t ω / P (t + 1) ω) := by
    filter_upwards [hP t, hP (t + 1)] with ω h1 h2
    exact mul_pos (div_pos (hu'pos _) (hu'pos _)) (div_pos h1 h2)
  filter_upwards [euler_interior hβ hu hu' hopt hPad hP hQt hreg, hpo, hP t,
    E_pos hW hWpos t] with ω h1 h2 h3 h4 hb
  refine ⟨?_, mul_pos hβ h4⟩
  have e : S.E t (fun ω => u' (c (t + 1) ω) / u' (c t ω) * (P t ω / P (t + 1) ω)) ω =
      f ω * S.E t (fun ω => u' (c (t + 1) ω) / P (t + 1) ω) ω := by
    rw [hWeq]
    exact h2
  rw [e, ← mul_assoc, mul_comm β (f ω), mul_assoc, ← h1 hb]
  have := (hu'pos (c t ω)).ne'
  have := h3.ne'
  simp only [hf]
  field_simp

/-- Cochrane (2023), eq. (2.3), p. 22 ("the interest rate cannot be less than zero" is about
`i ≥ 0`; here the weaker `i > −1` is derived, not assumed): if the bond price has the form
`Q_t = β E_t(P_t/P_{t+1})` almost surely with positive prices and an integrable payoff, then
`Q_t > 0` and the nominal rate `i_t = 1/Q_t − 1 > −1` almost surely. -/
theorem rate_gt_neg_one_of_formula {β : ℝ} (hβ : 0 < β) {P Q : ℕ → Ω → ℝ} {t : ℕ}
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω)
    (hint : Integrable (fun ω => P t ω / P (t + 1) ω) S.μ)
    (hQ : Q t =ᵐ[S.μ] β • S.E t (fun ω => P t ω / P (t + 1) ω)) :
    ∀ᵐ ω ∂S.μ, 0 < Q t ω ∧ -1 < (Q t ω)⁻¹ - 1 := by
  have hpos : ∀ᵐ ω ∂S.μ, 0 < P t ω / P (t + 1) ω := by
    filter_upwards [hP t, hP (t + 1)] with ω h1 h2
    exact div_pos h1 h2
  filter_upwards [bondPrice_pos_of_formula hβ hint hpos (q := Q t)
    (hQ.mono fun ω h => by rw [h]; rfl)] with ω h
  refine ⟨h, ?_⟩
  linarith [inv_pos.2 h]

end Cochrane.NewKeynesianSelection.TidyR6HouseholdBond
