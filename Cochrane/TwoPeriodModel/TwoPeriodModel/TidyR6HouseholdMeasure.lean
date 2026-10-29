/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.TidyR6Household
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The household problem on a probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §1.1, p. 4 (no money is held
after the end of day 1), §1.2, p. 7 (representative agent, constant endowment) and eq. (1.3),
p. 8 (the bond-pricing equation), on a genuine probability space: `(Ω, P)` with a filtration
`𝓕`, `E₀ = P[· | 𝓕 0]` (Mathlib's conditional expectation), and every constraint holding almost
surely. `TidyR6Household` treats the same problem for an abstract `ExpectationSystem`; here the
state space is arbitrary (uncountable, continuous shocks).

The probability space with a filtration (`MeasSystem`) is restated from the IntertemporalModel
project (ExpectationsMeasure.MeasExpectationSystem); the tools `exists_abs_le_of_continuous`,
`integrable_comp_of_bdd` and `hasDerivAt_integral_comp` are restated from its HouseholdMeasure
module.

## The household problem

`MFeasible`: `c₀`, `B₀` are `𝓕 0`-measurable, `c₁`, `M₁` measurable, `B₀` integrable,
`u(c₀)` and `u(c₁)` integrable, `M₁ ≥ 0` a.s., and both budget constraints of `TidyR6Household`
a.s. `expU` is `E[u(c₀) + βu(c₁)]`, a genuine integral; `MOptimal`: feasible and no feasible
plan has higher expected utility.

## Main results

* `m_money_zero_of_optimal`: `M₁ = 0` almost surely in every optimal plan with bounded `c₁`.
* `m_euler_of_optimal` (necessity): `Q₀u'(c₀)/P₀ = βE₀[u'(c₁)/P₁]` almost surely, for every
  `C¹` utility, when `c₀`, `c₁` and `1/P₁` are essentially bounded (no bound on `Q₀/P₀`).
* `m_optimal_of_euler` (sufficiency): concave, weakly increasing `C¹` utility, `M₁ = 0` a.s. and
  the Euler equation a.s. give an optimal plan.
* `m_optimal_iff`: both directions.
* `MEquilibrium`, `MCompEqm`, `m_compEqm_iff_equilibrium`: a competitive equilibrium is exactly
  an almost-sure fiscal-theory equilibrium: the flow condition (1.2), the bond price (1.3) and
  the last-day valuation (1.4) are derived from optimisation; `m_bondPrice_iff`: (1.3) in the
  form `Q₀ = βP₀E₀(1/P₁)` is `Q₀ = βE₀(P₀/P₁)` whenever `P₀/P₁` and `1/P₁` are integrable
  and `P₀` is known at date 0.
-/

namespace Cochrane.TwoPeriodModel.TidyR6HouseholdMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.TwoPeriodModel.TidyR6Household

variable (Ω : Type*) [mΩ : MeasurableSpace Ω]

/-- Cochrane (2023), §1.3, p. 8 (the expectation `E₀` under genuine uncertainty): a probability
space with a filtration (restated from the IntertemporalModel project,
ExpectationsMeasure.MeasExpectationSystem). -/
structure MeasSystem where
  /-- The probability measure. -/
  P : ProbabilityMeasure Ω
  /-- The information available at each date. -/
  𝓕 : Filtration ℕ mΩ

variable {Ω}

namespace MeasSystem

variable (S : MeasSystem Ω)

/-- Cochrane (2023), §1.3, p. 8: the probability measure as a measure. -/
abbrev μ : Measure Ω := S.P

/-- Cochrane (2023), §1.3, p. 8: `E_t x = μ[x | 𝓕 t]`, Mathlib's conditional expectation. -/
noncomputable abbrev E (t : ℕ) (x : Ω → ℝ) : Ω → ℝ := S.μ[x | S.𝓕 t]

end MeasSystem

/-! ### Tools (restated from the IntertemporalModel project) -/

/-- Cochrane (2023), §1.2, p. 7: a continuous function is bounded on `[−R, R]` (restated from
the IntertemporalModel project). -/
theorem exists_abs_le_of_continuous {v : ℝ → ℝ} (hv : Continuous v) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x, |x| ≤ R → |v x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hv.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have := hC x (Set.mem_Icc.2 (abs_le.1 hx))
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- Cochrane (2023), §1.2, p. 7: a continuous function of an essentially bounded variable is
integrable on a probability space (restated from the IntertemporalModel project). -/
theorem integrable_comp_of_bdd {μ : Measure Ω} [IsFiniteMeasure μ] {v : ℝ → ℝ}
    (hv : Continuous v) {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {R : ℝ}
    (hR : ∀ᵐ ω ∂μ, |f ω| ≤ R) : Integrable (fun ω => v (f ω)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hv.continuousOn
  exact Integrable.of_bound (hv.comp_aestronglyMeasurable hf) C
    (hR.mono fun ω h => hC _ (Set.mem_Icc.2 (abs_le.1 h)))

/-- Cochrane (2023), eq. (1.3), p. 8 (differentiating expected utility under the integral
sign): if `v` has continuous derivative `v'` and `f`, `g` are essentially bounded, then
`ε ↦ E v(f + εg)` has derivative `E[v'(f)g]` at `0` (restated from the IntertemporalModel
project). -/
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

/-- Cochrane (2023), eq. (1.3), p. 8 (the law of iterated expectations with pull-out): for `d`
`𝓕 t`-measurable, `X` integrable and `dX` integrable, `E[dX] = E[d E_t X]`. -/
theorem integral_mul_E (S : MeasSystem Ω) {t : ℕ} {d X : Ω → ℝ}
    (hd : StronglyMeasurable[S.𝓕 t] d) (hX : Integrable X S.μ)
    (hdX : Integrable (fun ω => d ω * X ω) S.μ) :
    ∫ ω, d ω * X ω ∂S.μ = ∫ ω, d ω * S.E t X ω ∂S.μ := by
  rw [← integral_condExp (S.𝓕.le t)]
  exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hd hdX hX)

/-! ### The household problem -/

/-- Cochrane (2023), §1.3, pp. 7–8, on a probability space: a feasible plan: `c₀`, `B₀` known
at date 0 (`𝓕 0`-measurable), `c₁`, `M₁` measurable, `B₀` integrable, `u(c₀)`, `u(c₁)`
integrable, `M₁ ≥ 0` a.s., and both budget constraints a.s. -/
def MFeasible (S : MeasSystem Ω) (u : ℝ → ℝ) (e : Env Ω) (p : Plan Ω) : Prop :=
  StronglyMeasurable[S.𝓕 0] p.c0 ∧ StronglyMeasurable[S.𝓕 0] p.B0 ∧
    AEStronglyMeasurable p.c1 S.μ ∧ AEStronglyMeasurable p.M1 S.μ ∧ Integrable p.B0 S.μ ∧
    Integrable (fun ω => u (p.c0 ω)) S.μ ∧ Integrable (fun ω => u (p.c1 ω)) S.μ ∧
    (∀ᵐ ω ∂S.μ, 0 ≤ p.M1 ω) ∧
    (∀ᵐ ω ∂S.μ, e.Bm1 ω + e.P0 ω * e.y0 ω =
      e.P0 ω * p.c0 ω + e.P0 ω * e.s0 ω + e.Q0 ω * p.B0 ω) ∧
    ∀ᵐ ω ∂S.μ, p.B0 ω + e.P1 ω * e.y1 ω = e.P1 ω * p.c1 ω + e.P1 ω * e.s1 ω + p.M1 ω

/-- Cochrane (2023), §1.2, p. 7: expected utility `E[u(c₀) + βu(c₁)]`, a genuine integral. -/
noncomputable def expU (S : MeasSystem Ω) (β : ℝ) (u : ℝ → ℝ) (p : Plan Ω) : ℝ :=
  ∫ ω, (u (p.c0 ω) + β * u (p.c1 ω)) ∂S.μ

/-- Cochrane (2023), §1.2, p. 7, on a probability space: an optimal plan: feasible, and no
feasible plan has higher expected utility. -/
def MOptimal (S : MeasSystem Ω) (β : ℝ) (u : ℝ → ℝ) (e : Env Ω) (p : Plan Ω) : Prop :=
  MFeasible S u e p ∧ ∀ q, MFeasible S u e q → expU S β u q ≤ expU S β u p

/-- Cochrane (2023), eq. (1.3), p. 8 (the first-order condition behind it), almost surely:
`Q₀u'(c₀)/P₀ = βE₀[u'(c₁)/P₁]`. -/
def MEuler (S : MeasSystem Ω) (β : ℝ) (u' : ℝ → ℝ) (e : Env Ω) (p : Plan Ω) : Prop :=
  ∀ᵐ ω ∂S.μ, e.Q0 ω * u' (p.c0 ω) / e.P0 ω = β * S.E 0 (fun ω => u' (p.c1 ω) / e.P1 ω) ω

/-- Cochrane (2023), §1.2, p. 7: an essentially bounded random variable. -/
def BddAt (S : MeasSystem Ω) (f : Ω → ℝ) : Prop := ∃ M, ∀ᵐ ω ∂S.μ, |f ω| ≤ M

/-- Cochrane (2023), §1.2, p. 7: expected utility of plans with integrable utilities splits as
`E u(c₀) + βE u(c₁)`. -/
theorem expU_eq (S : MeasSystem Ω) (β : ℝ) {u : ℝ → ℝ} {p : Plan Ω}
    (h0 : Integrable (fun ω => u (p.c0 ω)) S.μ) (h1 : Integrable (fun ω => u (p.c1 ω)) S.μ) :
    expU S β u p = ∫ ω, u (p.c0 ω) ∂S.μ + β * ∫ ω, u (p.c1 ω) ∂S.μ := by
  unfold expU
  rw [integral_add h0 (h1.const_mul β), integral_const_mul]

/-! ### Zero money at the end of the last day, almost surely -/

/-- Cochrane (2023), §1.1, p. 4 ("nobody wants to hold cash … after the end of day 1"), on a
probability space: with `β > 0`, continuous strictly increasing utility, `P₁ > 0` measurable and
`c₁` essentially bounded, an optimal plan holds no money at the end of the last day almost
surely. -/
theorem m_money_zero_of_optimal (S : MeasSystem Ω) {β : ℝ} (hβ : 0 < β) {u : ℝ → ℝ}
    (hu : StrictMono u) (huc : Continuous u) {e : Env Ω} (hP1 : ∀ ω, 0 < e.P1 ω)
    (hP1m : AEStronglyMeasurable e.P1 S.μ) {p : Plan Ω} (hK : BddAt S p.c1)
    (hopt : MOptimal S β u e p) : ∀ᵐ ω ∂S.μ, p.M1 ω = 0 := by
  obtain ⟨hf, hbest⟩ := hopt
  obtain ⟨hc0, hB0, hc1, hM1m, hB0i, hu0, hu1, hM, hb0, hb1⟩ := hf
  obtain ⟨K, hKb⟩ := hK
  set m : Ω → ℝ := fun ω => min (p.M1 ω / e.P1 ω) 1 with hm
  have hmm : AEStronglyMeasurable m S.μ :=
    ((hM1m.aemeasurable.div hP1m.aemeasurable).min aemeasurable_const).aestronglyMeasurable
  set q : Plan Ω := ⟨p.c0, p.B0, fun ω => p.c1 ω + m ω, fun ω => p.M1 ω - e.P1 ω * m ω⟩
    with hq
  have hm01 : ∀ᵐ ω ∂S.μ, 0 ≤ m ω ∧ m ω ≤ 1 := by
    filter_upwards [hM] with ω h
    exact ⟨le_min (div_nonneg h (hP1 ω).le) zero_le_one, min_le_right _ _⟩
  have hqc1m : AEStronglyMeasurable q.c1 S.μ := hc1.add hmm
  have hqu1 : Integrable (fun ω => u (q.c1 ω)) S.μ := by
    refine integrable_comp_of_bdd huc hqc1m (R := K + 1) ?_
    filter_upwards [hKb, hm01] with ω h1 h2
    exact (abs_add_le _ _).trans (add_le_add h1 (by rw [abs_of_nonneg h2.1]; exact h2.2))
  have hqf : MFeasible S u e q := by
    refine ⟨hc0, hB0, hqc1m, hM1m.sub (hP1m.mul hmm), hB0i, hu0, hqu1, ?_, hb0, ?_⟩
    · filter_upwards [hM] with ω h
      have : e.P1 ω * m ω ≤ p.M1 ω := by
        have h2 : m ω ≤ p.M1 ω / e.P1 ω := min_le_left _ _
        have := mul_le_mul_of_nonneg_left h2 (hP1 ω).le
        rwa [mul_div_cancel₀ _ (hP1 ω).ne'] at this
      simp only [q]
      linarith
    · filter_upwards [hb1] with ω h
      simp only [q]
      linarith
  have hle := hbest q hqf
  rw [expU_eq S β (p := q) hu0 hqu1, expU_eq S β hu0 hu1] at hle
  have hint : ∫ ω, (u (q.c1 ω) - u (p.c1 ω)) ∂S.μ ≤ 0 := by
    rw [integral_sub hqu1 hu1]
    have := le_of_mul_le_mul_left (by linarith : β * ∫ ω, u (q.c1 ω) ∂S.μ ≤
      β * ∫ ω, u (p.c1 ω) ∂S.μ) hβ
    linarith
  have hnn : 0 ≤ᵐ[S.μ] fun ω => u (q.c1 ω) - u (p.c1 ω) := by
    filter_upwards [hm01] with ω h
    simp only [Pi.zero_apply, sub_nonneg, q]
    exact hu.monotone (by linarith [h.1])
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn (hqu1.sub hu1)).mp
    (le_antisymm hint (integral_nonneg_of_ae hnn))
  filter_upwards [hzero, hM] with ω h hMω
  simp only [Pi.zero_apply, sub_eq_zero, q] at h
  have h' := hu.injective h
  have hm0 : m ω = 0 := by linarith
  have hne := (hP1 ω).ne'
  simp only [hm] at hm0
  rcases min_eq_iff.mp hm0 with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [div_eq_zero_iff] at h1
    simpa [hne] using h1
  · exact absurd h1 one_ne_zero


/-! ### Necessity of the Euler equation, almost surely -/

/-- Cochrane (2023), eq. (1.3), p. 8: the bounded weight `x/((1 + |k|)(1 + |x|))` has absolute
value at most one, and so has its product with `k`. -/
theorem abs_weight_le (k x : ℝ) :
    |x / ((1 + |k|) * (1 + |x|))| ≤ 1 ∧ |k * (x / ((1 + |k|) * (1 + |x|)))| ≤ 1 := by
  have h1 : 0 < 1 + |k| := by positivity
  have h2 : 0 < 1 + |x| := by positivity
  rw [abs_div, abs_mul, abs_of_pos h1, abs_of_pos h2, abs_mul, abs_div, abs_mul, abs_of_pos h1,
    abs_of_pos h2]
  constructor
  · rw [div_le_one (mul_pos h1 h2)]
    nlinarith [abs_nonneg k, abs_nonneg x]
  · rw [← mul_div_assoc, div_le_one (mul_pos h1 h2)]
    nlinarith [abs_nonneg k, abs_nonneg x, mul_nonneg (abs_nonneg k) (abs_nonneg x)]

/-- Cochrane (2023), eq. (1.3), p. 8 (**necessity, on a probability space**): an optimal plan
satisfies the Euler equation `Q₀u'(c₀)/P₀ = βE₀[u'(c₁)/P₁]` almost surely, for every utility
with continuous derivative `u'` (no concavity), when `c₀`, `c₁` and `1/P₁` are essentially
bounded (`P₀, P₁ ≠ 0`; `P₀`, `Q₀` known at date 0; `P₁` measurable). No bound on `Q₀/P₀` is
needed: the deviation is scaled by `1/((1 + |Q₀/P₀|)(1 + |gap|))`. -/
theorem m_euler_of_optimal (S : MeasSystem Ω) {β : ℝ} {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') {e : Env Ω}
    (hP0 : ∀ ω, e.P0 ω ≠ 0) (hP1 : ∀ ω, e.P1 ω ≠ 0) (hP0m : StronglyMeasurable[S.𝓕 0] e.P0)
    (hQ0m : StronglyMeasurable[S.𝓕 0] e.Q0) (hP1m : AEStronglyMeasurable e.P1 S.μ)
    (hA : BddAt S (fun ω => 1 / e.P1 ω)) {p : Plan Ω} (hc0b : BddAt S p.c0)
    (hc1b : BddAt S p.c1) (hopt : MOptimal S β u e p) : MEuler S β u' e p := by
  obtain ⟨hf, hbest⟩ := hopt
  obtain ⟨hc0, hB0, hc1, hM1m, hB0i, hu0, hu1, hM, hb0, hb1⟩ := hf
  obtain ⟨A, hAb⟩ := hA
  obtain ⟨K0, hK0⟩ := hc0b
  obtain ⟨K1, hK1⟩ := hc1b
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  obtain ⟨C0, hC00, hC0⟩ := exists_abs_le_of_continuous hu' K0
  obtain ⟨C1, hC10, hC1⟩ := exists_abs_le_of_continuous hu' K1
  have hle0 : S.𝓕 0 ≤ mΩ := S.𝓕.le 0
  set k : Ω → ℝ := fun ω => e.Q0 ω / e.P0 ω with hk
  have hkm : StronglyMeasurable[S.𝓕 0] k :=
    (hQ0m.measurable.div hP0m.measurable).stronglyMeasurable
  set W : Ω → ℝ := fun ω => u' (p.c1 ω) / e.P1 ω with hW
  have hWm : AEStronglyMeasurable W S.μ :=
    ((hu'.measurable.comp_aemeasurable hc1.aemeasurable).div hP1m.aemeasurable).aestronglyMeasurable
  have hWb : ∀ᵐ ω ∂S.μ, |W ω| ≤ C1 * A := by
    filter_upwards [hK1, hAb] with ω h1 h2
    have : W ω = u' (p.c1 ω) * (1 / e.P1 ω) := by simp only [hW]; ring
    rw [this, abs_mul]
    exact mul_le_mul (hC1 _ h1) h2 (abs_nonneg _) hC10
  have hWi : Integrable W S.μ := Integrable.of_bound hWm (C1 * A)
    (hWb.mono fun ω h => by rwa [Real.norm_eq_abs])
  have hEWb : ∀ᵐ ω ∂S.μ, |S.E 0 W ω| ≤ C1 * A := ae_bdd_abs_condExp_of_ae_bdd_abs hWb
  have hu'c0m : StronglyMeasurable[S.𝓕 0] (fun ω => u' (p.c0 ω)) :=
    hu'.comp_stronglyMeasurable hc0
  set G : Ω → ℝ := fun ω => -(k ω * u' (p.c0 ω)) + β * S.E 0 W ω with hG
  have hGm : StronglyMeasurable[S.𝓕 0] G :=
    ((hkm.mul hu'c0m).neg).add (stronglyMeasurable_condExp.const_mul β)
  set z : Ω → ℝ := fun ω => G ω / ((1 + |k ω|) * (1 + |G ω|)) with hz
  have hzm : StronglyMeasurable[S.𝓕 0] z :=
    (hGm.measurable.div ((measurable_const.add (continuous_abs.measurable.comp hkm.measurable)).mul
      (measurable_const.add (continuous_abs.measurable.comp hGm.measurable)))).stronglyMeasurable
  have hzb : ∀ ω, |z ω| ≤ 1 := fun ω => (abs_weight_le (k ω) (G ω)).1
  have hkzb : ∀ ω, |k ω * z ω| ≤ 1 := fun ω => (abs_weight_le (k ω) (G ω)).2
  have hzmu : AEStronglyMeasurable z S.μ := (hzm.mono hle0).aestronglyMeasurable
  have hkmu : AEStronglyMeasurable k S.μ := (hkm.mono hle0).aestronglyMeasurable
  -- the deviation directions
  set g0 : Ω → ℝ := fun ω => -(k ω * z ω) with hg0
  set g1 : Ω → ℝ := fun ω => z ω * (1 / e.P1 ω) with hg1
  have hg0m : StronglyMeasurable[S.𝓕 0] g0 := (hkm.mul hzm).neg
  have hg1m : AEStronglyMeasurable g1 S.μ :=
    (hzmu.aemeasurable.mul (aemeasurable_const.div hP1m.aemeasurable)).aestronglyMeasurable
  have hg0b : ∀ ω, |g0 ω| ≤ 1 := fun ω => by rw [hg0, abs_neg]; exact hkzb ω
  have hg1b : ∀ᵐ ω ∂S.μ, |g1 ω| ≤ 1 * A := by
    filter_upwards [hAb] with ω h
    rw [hg1, abs_mul]
    exact mul_le_mul (hzb ω) h (abs_nonneg _) zero_le_one
  set q : ℝ → Plan Ω := fun ε =>
    ⟨fun ω => p.c0 ω + ε * g0 ω, fun ω => p.B0 ω + ε * z ω, fun ω => p.c1 ω + ε * g1 ω, p.M1⟩
    with hq
  have hqf : ∀ ε, MFeasible S u e (q ε) := by
    intro ε
    refine ⟨hc0.add (hg0m.const_mul ε), hB0.add (hzm.const_mul ε),
      hc1.add (hg1m.const_mul ε), hM1m, hB0i.add ?_, ?_, ?_, hM, ?_, ?_⟩
    · exact Integrable.of_bound (hzmu.const_mul ε) (|ε| * 1)
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (hzb ω) (abs_nonneg ε))
    · refine integrable_comp_of_bdd huc
        ((hc0.mono hle0).aestronglyMeasurable.add
          ((hg0m.mono hle0).aestronglyMeasurable.const_mul ε))
        (R := K0 + |ε| * 1) ?_
      filter_upwards [hK0] with ω h
      refine (abs_add_le _ _).trans (add_le_add h ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hg0b ω) (abs_nonneg ε)
    · refine integrable_comp_of_bdd huc (hc1.add (hg1m.const_mul ε))
        (R := K1 + |ε| * (1 * A)) ?_
      filter_upwards [hK1, hg1b] with ω h h'
      refine (abs_add_le _ _).trans (add_le_add h ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h' (abs_nonneg ε)
    · filter_upwards [hb0] with ω h
      have hne := hP0 ω
      have key : e.P0 ω * (ε * g0 ω) + e.Q0 ω * (ε * z ω) = 0 := by
        simp only [hg0, hk]
        field_simp
        ring
      simp only [q]
      linear_combination h - key
    · filter_upwards [hb1] with ω h
      have hne := hP1 ω
      have key : e.P1 ω * (ε * g1 ω) = ε * z ω := by
        simp only [hg1]
        field_simp
      simp only [q]
      linear_combination h - key
  -- expected utility along the deviation
  set φ : ℝ → ℝ := fun ε => ∫ ω, u (p.c0 ω + ε * g0 ω) ∂S.μ +
    β * ∫ ω, u (p.c1 ω + ε * g1 ω) ∂S.μ with hφ
  have hφq : ∀ ε, φ ε = expU S β u (q ε) := fun ε =>
    (expU_eq S β (hqf ε).2.2.2.2.2.1 (hqf ε).2.2.2.2.2.2.1).symm
  have hφ0 : φ 0 = expU S β u p := by
    rw [expU_eq S β hu0 hu1]
    simp only [hφ, zero_mul, add_zero]
  have hmax : IsLocalMax φ 0 := Eventually.of_forall fun ε => by
    rw [hφq, hφ0]
    exact hbest _ (hqf ε)
  have hd1 := hasDerivAt_integral_comp hu hu' (hc0.mono hle0).aestronglyMeasurable
    (hg0m.mono hle0).aestronglyMeasurable hK0 (Eventually.of_forall hg0b)
  have hd2 := (hasDerivAt_integral_comp hu hu' hc1 hg1m hK1 hg1b).const_mul β
  have hD := hmax.hasDerivAt_eq_zero (hd1.add hd2)
  -- identify the derivative with `E[zG]`
  have hX0 : Integrable (fun ω => z ω * -(k ω * u' (p.c0 ω))) S.μ := by
    refine Integrable.of_bound (hzmu.mul (hkmu.mul
      (hu'c0m.mono hle0).aestronglyMeasurable).neg) C0 ?_
    filter_upwards [hK0] with ω h
    rw [Real.norm_eq_abs]
    have : z ω * -(k ω * u' (p.c0 ω)) = -((k ω * z ω) * u' (p.c0 ω)) := by ring
    rw [this, abs_neg, abs_mul]
    simpa using mul_le_mul (hkzb ω) (hC0 _ h) (abs_nonneg _) zero_le_one
  have hzW : Integrable (fun ω => z ω * W ω) S.μ := by
    refine Integrable.of_bound (hzmu.mul hWm) (1 * (C1 * A)) ?_
    filter_upwards [hWb] with ω h
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hzb ω) h (abs_nonneg _) zero_le_one
  have hzEW : Integrable (fun ω => z ω * S.E 0 W ω) S.μ := by
    refine Integrable.of_bound (hzmu.mul (integrable_condExp).aestronglyMeasurable)
      (1 * (C1 * A)) ?_
    filter_upwards [hEWb] with ω h
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hzb ω) h (abs_nonneg _) zero_le_one
  have e1 : ∫ ω, u' (p.c0 ω) * g0 ω ∂S.μ = ∫ ω, z ω * -(k ω * u' (p.c0 ω)) ∂S.μ := by
    congr 1; funext ω; simp only [hg0]; ring
  have e2 : ∫ ω, u' (p.c1 ω) * g1 ω ∂S.μ = ∫ ω, z ω * S.E 0 W ω ∂S.μ := by
    rw [← integral_mul_E S hzm hWi hzW]
    congr 1; funext ω; simp only [hg1, hW]; ring
  rw [e1, e2, ← integral_const_mul, ← integral_add hX0 (hzEW.const_mul β)] at hD
  have hzG : (fun ω => z ω * -(k ω * u' (p.c0 ω)) + β * (z ω * S.E 0 W ω)) =
      fun ω => G ω ^ 2 / ((1 + |k ω|) * (1 + |G ω|)) := by
    funext ω
    simp only [hz, hG]
    ring
  rw [hzG] at hD
  have hnn : 0 ≤ᵐ[S.μ] fun ω => G ω ^ 2 / ((1 + |k ω|) * (1 + |G ω|)) :=
    Eventually.of_forall fun ω => by
      simp only [Pi.zero_apply]
      positivity
  have hint : Integrable (fun ω => G ω ^ 2 / ((1 + |k ω|) * (1 + |G ω|))) S.μ := by
    rw [← hzG]; exact hX0.add (hzEW.const_mul β)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hD
  filter_upwards [hzero] with ω h
  have hpos : 0 < (1 + |k ω|) * (1 + |G ω|) := by positivity
  simp only [Pi.zero_apply] at h
  rw [div_eq_zero_iff] at h
  have hG0 : G ω = 0 := by
    rcases h with h | h
    · exact (pow_eq_zero_iff two_ne_zero).mp h
    · exact absurd h hpos.ne'
  have e3 : e.Q0 ω * u' (p.c0 ω) / e.P0 ω = k ω * u' (p.c0 ω) := by
    simp only [hk]; ring
  rw [e3]
  simp only [hG] at hG0
  linarith


/-! ### Sufficiency of the Euler equation, almost surely -/

/-- Cochrane (2023), eq. (1.3), p. 8 (**sufficiency, on a probability space**): for concave,
weakly increasing utility with continuous derivative `u'`, `β ≥ 0`, `P₀, P₁ > 0` (`P₀`, `Q₀`
known at date 0, `P₁` measurable, `1/P₁` essentially bounded), a feasible plan with essentially
bounded `c₁`, `M₁ = 0` almost surely and the Euler equation almost surely is optimal. -/
theorem m_optimal_of_euler (S : MeasSystem Ω) {β : ℝ} (hβ : 0 ≤ β) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') (hc : ConcaveOn ℝ Set.univ u)
    (hu'0 : ∀ x, 0 ≤ u' x) {e : Env Ω} (hP0 : ∀ ω, 0 < e.P0 ω) (hP1 : ∀ ω, 0 < e.P1 ω)
    (hP0m : StronglyMeasurable[S.𝓕 0] e.P0) (hQ0m : StronglyMeasurable[S.𝓕 0] e.Q0)
    (hP1m : AEStronglyMeasurable e.P1 S.μ) (hA : BddAt S (fun ω => 1 / e.P1 ω)) {p : Plan Ω}
    (hc1b : BddAt S p.c1) (hp : MFeasible S u e p) (hM : ∀ᵐ ω ∂S.μ, p.M1 ω = 0)
    (hE : MEuler S β u' e p) : MOptimal S β u e p := by
  refine ⟨hp, fun q hq => ?_⟩
  obtain ⟨hc0, hB0, hc1, -, hB0i, hu0, hu1, -, hb0, hb1⟩ := hp
  obtain ⟨-, hB0', -, -, hB0i', hu0', hu1', hM', hb0', hb1'⟩ := hq
  obtain ⟨A, hAb⟩ := hA
  obtain ⟨K1, hK1⟩ := hc1b
  obtain ⟨C1, hC10, hC1⟩ := exists_abs_le_of_continuous hu' K1
  have hle0 : S.𝓕 0 ≤ mΩ := S.𝓕.le 0
  set d : Ω → ℝ := fun ω => q.B0 ω - p.B0 ω with hd
  have hdm : StronglyMeasurable[S.𝓕 0] d := hB0'.sub hB0
  have hdi : Integrable d S.μ := hB0i'.sub hB0i
  set W : Ω → ℝ := fun ω => u' (p.c1 ω) / e.P1 ω with hW
  have hWm : AEStronglyMeasurable W S.μ :=
    ((hu'.measurable.comp_aemeasurable hc1.aemeasurable).div hP1m.aemeasurable).aestronglyMeasurable
  have hWb : ∀ᵐ ω ∂S.μ, |W ω| ≤ C1 * A := by
    filter_upwards [hK1, hAb] with ω h1 h2
    have : W ω = u' (p.c1 ω) * (1 / e.P1 ω) := by simp only [hW]; ring
    rw [this, abs_mul]
    exact mul_le_mul (hC1 _ h1) h2 (abs_nonneg _) hC10
  have hWi : Integrable W S.μ := Integrable.of_bound hWm (C1 * A)
    (hWb.mono fun ω h => by rwa [Real.norm_eq_abs])
  set V : Ω → ℝ := fun ω => e.Q0 ω / e.P0 ω * u' (p.c0 ω) with hV
  have hVm : AEStronglyMeasurable V S.μ :=
    ((((hQ0m.measurable.div hP0m.measurable).mul
      (hu'.measurable.comp hc0.measurable)).mono hle0 le_rfl).aemeasurable).aestronglyMeasurable
  have hVE : ∀ᵐ ω ∂S.μ, V ω = β * S.E 0 W ω := by
    filter_upwards [hE] with ω h
    rw [← h]; simp only [hV]; ring
  have hVb : ∀ᵐ ω ∂S.μ, ‖V ω‖ ≤ β * (C1 * A) := by
    filter_upwards [hVE, ae_bdd_abs_condExp_of_ae_bdd_abs hWb (m := S.𝓕 0)] with ω h1 h2
    rw [Real.norm_eq_abs, h1, abs_mul, abs_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left h2 hβ
  have hdV : Integrable (fun ω => V ω * d ω) S.μ := hdi.bdd_mul hVm hVb
  have hdW : Integrable (fun ω => d ω * W ω) S.μ :=
    hdi.mul_bdd hWm (hWb.mono fun ω h => by rwa [Real.norm_eq_abs])
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂S.μ, u (q.c0 ω) + β * u (q.c1 ω) ≤
      (u (p.c0 ω) + β * u (p.c1 ω)) + (-(V ω * d ω) + β * (d ω * W ω)) := by
    filter_upwards [hb0, hb0', hb1, hb1', hM, hM'] with ω h0 h0' h1 h1' hm hm'
    have hne0 := (hP0 ω).ne'
    have hne1 := (hP1 ω).ne'
    have hc0d : q.c0 ω - p.c0 ω = -(e.Q0 ω / e.P0 ω) * d ω := by
      simp only [hd]
      field_simp
      linear_combination h0 - h0'
    have hc1d : q.c1 ω - p.c1 ω = (d ω - q.M1 ω) / e.P1 ω := by
      simp only [hd]
      field_simp
      linear_combination h1 - h1' + hm
    have t0 := le_tangent hu hc (p.c0 ω) (q.c0 ω)
    have t1 := le_tangent hu hc (p.c1 ω) (q.c1 ω)
    rw [hc0d] at t0
    rw [hc1d] at t1
    have hnn : 0 ≤ u' (p.c1 ω) * (q.M1 ω / e.P1 ω) :=
      mul_nonneg (hu'0 _) (div_nonneg hm' (hP1 ω).le)
    have e1 : u' (p.c1 ω) * ((d ω - q.M1 ω) / e.P1 ω) =
        d ω * W ω - u' (p.c1 ω) * (q.M1 ω / e.P1 ω) := by
      simp only [hW]; ring
    have e0 : u' (p.c0 ω) * (-(e.Q0 ω / e.P0 ω) * d ω) = -(V ω * d ω) := by
      simp only [hV]; ring
    rw [e1] at t1
    rw [e0] at t0
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : u (q.c1 ω) ≤ u (p.c1 ω) + d ω * W ω)
      hβ]
  have I1 : Integrable (fun ω => u (q.c0 ω) + β * u (q.c1 ω)) S.μ :=
    hu0'.add (hu1'.const_mul β)
  have Ip : Integrable (fun ω => u (p.c0 ω) + β * u (p.c1 ω)) S.μ := hu0.add (hu1.const_mul β)
  have Ia : Integrable (fun ω => -(V ω * d ω)) S.μ := hdV.neg
  have Ib : Integrable (fun ω => β * (d ω * W ω)) S.μ := hdW.const_mul β
  have Ir : Integrable (fun ω => -(V ω * d ω) + β * (d ω * W ω)) S.μ := Ia.add Ib
  have Ipr : Integrable (fun ω => (u (p.c0 ω) + β * u (p.c1 ω)) +
      (-(V ω * d ω) + β * (d ω * W ω))) S.μ := Ip.add Ir
  have hint := integral_mono_ae I1 Ipr hpt
  have hzero : ∫ ω, (-(V ω * d ω) + β * (d ω * W ω)) ∂S.μ = 0 := by
    rw [integral_add Ia Ib, integral_neg, integral_const_mul, integral_mul_E S hdm hWi hdW,
      ← integral_const_mul]
    have : ∫ ω, V ω * d ω ∂S.μ = ∫ ω, β * (d ω * S.E 0 W ω) ∂S.μ := by
      refine integral_congr_ae ?_
      filter_upwards [hVE] with ω h
      rw [h]; ring
    rw [this]; ring
  unfold expU
  rw [integral_add Ip Ir, hzero, add_zero] at hint
  exact hint

/-- Cochrane (2023), §1.1, p. 4, and eq. (1.3), p. 8, on a probability space: **the household
problem, necessity and sufficiency.** For concave utility with continuous derivative `u' > 0`,
`β > 0`, `P₀, P₁ > 0` (`P₀`, `Q₀` known at 0, `P₁` measurable, `1/P₁` essentially bounded) and
a plan with essentially bounded `c₀`, `c₁`: the plan is optimal iff it is feasible, `M₁ = 0`
almost surely and the Euler equation holds almost surely. -/
theorem m_optimal_iff (S : MeasSystem Ω) {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') (hc : ConcaveOn ℝ Set.univ u)
    (hu'0 : ∀ x, 0 < u' x) {e : Env Ω} (hP0 : ∀ ω, 0 < e.P0 ω) (hP1 : ∀ ω, 0 < e.P1 ω)
    (hP0m : StronglyMeasurable[S.𝓕 0] e.P0) (hQ0m : StronglyMeasurable[S.𝓕 0] e.Q0)
    (hP1m : AEStronglyMeasurable e.P1 S.μ) (hA : BddAt S (fun ω => 1 / e.P1 ω)) {p : Plan Ω}
    (hc0b : BddAt S p.c0) (hc1b : BddAt S p.c1) :
    MOptimal S β u e p ↔ MFeasible S u e p ∧ (∀ᵐ ω ∂S.μ, p.M1 ω = 0) ∧ MEuler S β u' e p := by
  have hsm : StrictMono u := strictMono_of_deriv_pos fun x => by
    rw [(hu x).deriv]; exact hu'0 x
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  constructor
  · intro hopt
    exact ⟨hopt.1, m_money_zero_of_optimal S hβ hsm huc hP1 hP1m hc1b hopt,
      m_euler_of_optimal S hu hu' (fun ω => (hP0 ω).ne') (fun ω => (hP1 ω).ne') hP0m hQ0m
        hP1m hA hc0b hc1b hopt⟩
  · rintro ⟨hp, hM, hE⟩
    exact m_optimal_of_euler S hβ.le hu hu' hc (fun x => (hu'0 x).le) hP0 hP1 hP0m hQ0m hP1m
      hA hc1b hp hM hE

/-! ### The bond-pricing equation and competitive equilibrium, almost surely -/

/-- Cochrane (2023), eq. (1.3), p. 8, on a probability space, with the date-0 price pulled out
of `E₀`: `Q₀ = βP₀E₀(1/P₁)` almost surely. -/
def MBondPrice (S : MeasSystem Ω) (β : ℝ) (P0 P1 Q0 : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂S.μ, Q0 ω = β * P0 ω * S.E 0 (fun ω => 1 / P1 ω) ω

/-- Cochrane (2023), eq. (1.3), p. 8: when `P₀` is known at date 0 and `P₀/P₁`, `1/P₁` are
integrable, `MBondPrice` is the printed form `Q₀ = βE₀(P₀/P₁)` almost surely. -/
theorem m_bondPrice_iff (S : MeasSystem Ω) (β : ℝ) {P0 P1 Q0 : Ω → ℝ}
    (hP0m : StronglyMeasurable[S.𝓕 0] P0) (hi : Integrable (fun ω => P0 ω / P1 ω) S.μ)
    (hi1 : Integrable (fun ω => 1 / P1 ω) S.μ) :
    MBondPrice S β P0 P1 Q0 ↔ ∀ᵐ ω ∂S.μ, Q0 ω = β * S.E 0 (fun ω => P0 ω / P1 ω) ω := by
  have hfun : (fun ω => P0 ω / P1 ω) = P0 * fun ω => 1 / P1 ω := by
    funext ω; simp only [Pi.mul_apply]; ring
  have hi' : Integrable (P0 * fun ω => 1 / P1 ω) S.μ := by rw [← hfun]; exact hi
  have hpo := condExp_mul_of_stronglyMeasurable_left (μ := S.μ) hP0m hi' hi1
  have key : ∀ᵐ ω ∂S.μ, S.E 0 (fun ω => P0 ω / P1 ω) ω =
      P0 ω * S.E 0 (fun ω => 1 / P1 ω) ω := by
    rw [hfun]
    filter_upwards [hpo] with ω h
    exact h
  constructor
  · intro h
    filter_upwards [h, key] with ω h1 h2
    rw [h1, h2]; ring
  · intro h
    filter_upwards [h, key] with ω h1 h2
    rw [h1, h2]; ring

/-- Cochrane (2023), eq. (1.3), p. 8 (**(1.3) derived, almost surely**): at constant
consumption `c₀ = c₁ = ȳ` with `u'(ȳ) ≠ 0` and `P₀ ≠ 0`, the almost-sure Euler equation is the
almost-sure bond-pricing equation `Q₀ = βP₀E₀(1/P₁)`. -/
theorem m_euler_const_iff (S : MeasSystem Ω) {β : ℝ} {u' : ℝ → ℝ} {ybar : ℝ}
    (hy : u' ybar ≠ 0) {e : Env Ω} (hP0 : ∀ ω, e.P0 ω ≠ 0) {p : Plan Ω}
    (hc0 : p.c0 = fun _ => ybar) (hc1 : p.c1 = fun _ => ybar) :
    MEuler S β u' e p ↔ MBondPrice S β e.P0 e.P1 e.Q0 := by
  have hfun : (fun ω => u' (p.c1 ω) / e.P1 ω) = u' ybar • fun ω => 1 / e.P1 ω := by
    funext ω; rw [hc1]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hsm : ∀ᵐ ω ∂S.μ, S.E 0 (fun ω => u' (p.c1 ω) / e.P1 ω) ω =
      u' ybar * S.E 0 (fun ω => 1 / e.P1 ω) ω := by
    rw [hfun]
    filter_upwards [condExp_smul (μ := S.μ) (m := S.𝓕 0) (u' ybar) (fun ω => 1 / e.P1 ω)]
      with ω h
    simpa using h
  unfold MEuler MBondPrice
  rw [hc0]
  constructor
  · intro h
    filter_upwards [h, hsm] with ω h1 h2
    rw [h2, div_eq_iff (hP0 ω)] at h1
    apply mul_right_cancel₀ hy
    linear_combination h1
  · intro h
    filter_upwards [h, hsm] with ω h1 h2
    rw [h2, h1]
    field_simp [hP0 ω]

/-- Cochrane (2023), §1.3, pp. 7–8, on a probability space: the fiscal-theory equilibrium,
almost surely: positive price levels, `P₀` and `Q₀` known at date 0, `P₁` measurable, the flow
condition (1.2), the bond price (1.3) (`MBondPrice`) and the last-day valuation (1.4) `B₀/P₁ = s₁`,
each almost surely. -/
def MEquilibrium (S : MeasSystem Ω) (β : ℝ) (Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ) : Prop :=
  (∀ ω, 0 < P0 ω) ∧ (∀ ω, 0 < P1 ω) ∧ StronglyMeasurable[S.𝓕 0] P0 ∧
    StronglyMeasurable[S.𝓕 0] Q0 ∧ AEStronglyMeasurable P1 S.μ ∧
    (∀ᵐ ω ∂S.μ, Bm1 ω = P0 ω * s0 ω + Q0 ω * B0 ω) ∧ MBondPrice S β P0 P1 Q0 ∧
    ∀ᵐ ω ∂S.μ, B0 ω / P1 ω = s1 ω

/-- Cochrane (2023), §1.2, p. 7 and §1.3, pp. 7–8, on a probability space: a competitive
equilibrium with constant endowment `ȳ`: positive price levels, `P₀`, `Q₀` known at date 0, `P₁`
measurable, and an optimal household plan that consumes `ȳ` at both dates and buys the bonds
`B₀` the government sells. -/
def MCompEqm (S : MeasSystem Ω) (β : ℝ) (u : ℝ → ℝ) (ybar : ℝ)
    (Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ) : Prop :=
  (∀ ω, 0 < P0 ω) ∧ (∀ ω, 0 < P1 ω) ∧ StronglyMeasurable[S.𝓕 0] P0 ∧
    StronglyMeasurable[S.𝓕 0] Q0 ∧ AEStronglyMeasurable P1 S.μ ∧
    ∃ M1 : Ω → ℝ, MOptimal S β u ⟨Bm1, fun _ => ybar, fun _ => ybar, P0, P1, Q0, s0, s1⟩
      ⟨fun _ => ybar, B0, fun _ => ybar, M1⟩

/-- Cochrane (2023), eqs. (1.1)–(1.4), pp. 4–8, **on a genuine probability space: the
equilibrium conditions are derived from optimisation.** For concave utility with continuous
derivative `u' > 0`, `β > 0`, and `B₀ > 0` known at date 0, integrable, with `s₁/B₀`
essentially bounded, a price triple is a competitive equilibrium iff it is an almost-sure
fiscal-theory equilibrium: (1.2) is the household budget at market clearing, (1.3) the Euler
equation, and (1.4) the last-day budget with the derived `M₁ = 0` (almost surely). -/
theorem m_compEqm_iff_equilibrium (S : MeasSystem Ω) {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') (hc : ConcaveOn ℝ Set.univ u)
    (hu'0 : ∀ x, 0 < u' x) (ybar : ℝ) {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω)
    (hB0m : StronglyMeasurable[S.𝓕 0] B0) (hB0i : Integrable B0 S.μ)
    (hA : BddAt S (fun ω => s1 ω / B0 ω)) :
    MCompEqm S β u ybar Bm1 B0 s0 s1 P0 P1 Q0 ↔ MEquilibrium S β Bm1 B0 s0 s1 P0 P1 Q0 := by
  have hsm : StrictMono u := strictMono_of_deriv_pos fun x => by
    rw [(hu x).deriv]; exact hu'0 x
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  have hcb : BddAt S (fun _ : Ω => ybar) := ⟨|ybar|, Eventually.of_forall fun _ => le_rfl⟩
  obtain ⟨A, hAb⟩ := hA
  constructor
  · rintro ⟨hP0, hP1, hP0m, hQ0m, hP1m, M1, hopt⟩
    have hM := m_money_zero_of_optimal S hβ hsm huc hP1 hP1m hcb hopt
    have hb0 := hopt.1.2.2.2.2.2.2.2.2.1
    have hb1 := hopt.1.2.2.2.2.2.2.2.2.2
    have hB : ∀ᵐ ω ∂S.μ, B0 ω = P1 ω * s1 ω := by
      filter_upwards [hb1, hM] with ω h h0
      linarith
    have hval : ∀ᵐ ω ∂S.μ, B0 ω / P1 ω = s1 ω := by
      filter_upwards [hB] with ω h
      rw [div_eq_iff (hP1 ω).ne', h]; ring
    have hAP : BddAt S (fun ω => 1 / P1 ω) := by
      refine ⟨A, ?_⟩
      filter_upwards [hB, hAb] with ω h h'
      have hne := (hB0 ω).ne'
      have hne1 := (hP1 ω).ne'
      have hs : s1 ω ≠ 0 := fun h0 => hne (by rw [h, h0, mul_zero])
      have : 1 / P1 ω = s1 ω / B0 ω := by rw [h]; field_simp
      rw [this]; exact h'
    have hE := m_euler_of_optimal S hu hu' (fun ω => (hP0 ω).ne') (fun ω => (hP1 ω).ne')
      hP0m hQ0m hP1m hAP hcb hcb hopt
    have hQ := (m_euler_const_iff S (hu'0 ybar).ne'
      (e := ⟨Bm1, fun _ => ybar, fun _ => ybar, P0, P1, Q0, s0, s1⟩)
      (fun ω => (hP0 ω).ne') rfl rfl).mp hE
    refine ⟨hP0, hP1, hP0m, hQ0m, hP1m, ?_, hQ, hval⟩
    filter_upwards [hb0] with ω h
    linarith
  · rintro ⟨hP0, hP1, hP0m, hQ0m, hP1m, hflow, hQ, hval⟩
    refine ⟨hP0, hP1, hP0m, hQ0m, hP1m, 0, ?_⟩
    have hAP : BddAt S (fun ω => 1 / P1 ω) := by
      refine ⟨A, ?_⟩
      filter_upwards [hval, hAb] with ω h h'
      have hne := (hB0 ω).ne'
      have hne1 := (hP1 ω).ne'
      have : 1 / P1 ω = s1 ω / B0 ω := by rw [← h]; field_simp
      rw [this]; exact h'
    have hp : MFeasible S u ⟨Bm1, fun _ => ybar, fun _ => ybar, P0, P1, Q0, s0, s1⟩
        ⟨fun _ => ybar, B0, fun _ => ybar, 0⟩ := by
      refine ⟨stronglyMeasurable_const, hB0m, aestronglyMeasurable_const,
        aestronglyMeasurable_const, hB0i, integrable_const (u ybar), integrable_const (u ybar),
        Eventually.of_forall fun _ => le_rfl, ?_, ?_⟩
      · filter_upwards [hflow] with ω h
        linarith
      · filter_upwards [hval] with ω h
        rw [div_eq_iff (hP1 ω).ne'] at h
        simp only [Pi.zero_apply]
        rw [h]; ring
    have hE := (m_euler_const_iff S (hu'0 ybar).ne'
      (e := ⟨Bm1, fun _ => ybar, fun _ => ybar, P0, P1, Q0, s0, s1⟩)
      (p := ⟨fun _ => ybar, B0, fun _ => ybar, 0⟩) (fun ω => (hP0 ω).ne') rfl rfl).mpr hQ
    exact m_optimal_of_euler S hβ.le hu hu' hc (fun x => (hu'0 x).le) hP0 hP1 hP0m hQ0m hP1m
      hAP hcb hp (Eventually.of_forall fun _ => rfl) hE

end Cochrane.TwoPeriodModel.TidyR6HouseholdMeasure
