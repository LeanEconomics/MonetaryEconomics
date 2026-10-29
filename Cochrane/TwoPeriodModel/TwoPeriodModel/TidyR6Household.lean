/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.TwoPeriod
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The household problem behind (1.3) and `M₁ = 0`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §1.2, p. 7 ("a complete
economic model … representative agent, constant endowment, flexible prices"), §1.1, p. 4
("nobody wants to hold cash or bonds after the end of day 1"), and §1.3, eq. (1.3), p. 8 (the
bond-pricing equation). The chapter imposes (1.3) and zero money at the end of the last day as
equilibrium conditions. This module derives both from the optimisation of a household, under
an arbitrary `ExpectationSystem` (so on every finite event tree, and under perfect foresight).

## The household problem

The household enters date 0 with nominal bonds `B₋₁`, receives the endowment `y₀`, pays the
real surplus (net taxes) `s₀`, consumes `c₀` and buys bonds `B₀` at price `Q₀`:
`B₋₁ + P₀y₀ = P₀c₀ + P₀s₀ + Q₀B₀` (`Budget0`). On the last day it is paid `B₀` dollars, receives
`y₁`, pays `P₁s₁`, consumes `c₁` and is left holding money `M₁ ≥ 0`:
`B₀ + P₁y₁ = P₁c₁ + P₁s₁ + M₁` (`Budget1`). Date-0 choices are known at date 0; date-1 choices
are state contingent. Bond holdings have no sign restriction. The household maximises
`u(c₀) + βE₀u(c₁)` (`value`, a date-0 random variable); a plan is `Optimal` when it is feasible
and no feasible plan has higher value in any state.

## Main results

* `money_zero_of_optimal`: with strictly increasing utility and a faithful `E₀` (every finite tree
  with strictly positive state probabilities, `finiteTree_faithful0`), an optimal plan holds no
  money at the end of the last day, `M₁ = 0`; `money_zero_needs_faithful`: with a null state
  (`pointSystem`) money may be held there in an optimal plan.
* `euler_of_optimal` (necessity): an optimal plan satisfies the Euler equation
  `Q₀u'(c₀)/P₀ = βE₀[u'(c₁)/P₁]`, for every `C¹` utility (concavity not needed), when `c₁` and
  `1/P₁` are bounded (automatic on a finite tree).
* `optimal_of_euler` (sufficiency): for concave, weakly increasing `C¹` utility, a feasible plan
  with `M₁ = 0` and the Euler equation is optimal (no boundedness needed).
* `optimal_iff`: necessity and sufficiency together.
* `euler_const_iff_bondPrice`: at constant consumption the Euler
  equation is exactly (1.3), `Q₀ = βE₀(P₀/P₁)`; `euler_iff_sdf`: with a random endowment it is
  `Q₀ = βE₀[(u'(y₁)/u'(y₀))(P₀/P₁)]`.
* `CompEqm`, `compEqm_iff_equilibrium`: a competitive equilibrium (the household's optimal plan
  consumes the constant endowment and holds the debt sold) is exactly the fiscal-theory
  equilibrium `TwoPeriod.Equilibrium`: (1.2), (1.3) and (1.4) are derived, not imposed.
* `finiteTree_compEqm_iff`, `finiteTree_compEqm_existsUnique`, `coin_compEqm`: on every finite
  tree, without boundedness hypotheses; there is exactly one competitive equilibrium.
-/

namespace Cochrane.TwoPeriodModel.TidyR6Household

open Cochrane.TwoPeriodModel.TwoPeriod Cochrane.TwoPeriodModel.ExpectationsFiniteTree
open Filter Topology

variable (Ω : Type*)

/-- Cochrane (2023), §1.3, pp. 7–8: the environment a household takes as given: initial bonds
`B₋₁`, endowments `y₀, y₁`, price levels `P₀, P₁`, the bond price `Q₀` and real surpluses
(net taxes) `s₀, s₁`. -/
structure Env where
  /-- Nominal bonds held entering date 0, `B₋₁`. -/
  Bm1 : Ω → ℝ
  /-- The date-0 endowment `y₀`. -/
  y0 : Ω → ℝ
  /-- The date-1 endowment `y₁`. -/
  y1 : Ω → ℝ
  /-- The date-0 price level `P₀`. -/
  P0 : Ω → ℝ
  /-- The date-1 price level `P₁`. -/
  P1 : Ω → ℝ
  /-- The date-0 bond price `Q₀`. -/
  Q0 : Ω → ℝ
  /-- The date-0 real surplus (net taxes) `s₀`. -/
  s0 : Ω → ℝ
  /-- The date-1 real surplus (net taxes) `s₁`. -/
  s1 : Ω → ℝ

/-- Cochrane (2023), §1.1, p. 4, and §1.3, p. 8: a household plan: consumption `c₀, c₁`, bonds
bought at date 0, `B₀`, and money held at the end of the last day, `M₁`. -/
structure Plan where
  /-- Date-0 consumption `c₀`. -/
  c0 : Ω → ℝ
  /-- Bonds bought at date 0, `B₀`. -/
  B0 : Ω → ℝ
  /-- Date-1 consumption `c₁`. -/
  c1 : Ω → ℝ
  /-- Money held at the end of the last day, `M₁`. -/
  M1 : Ω → ℝ

variable {Ω}

/-- Cochrane (2023), eq. (1.2), p. 8, household side: the date-0 budget constraint
`B₋₁ + P₀y₀ = P₀c₀ + P₀s₀ + Q₀B₀`. -/
def Budget0 (e : Env Ω) (p : Plan Ω) : Prop :=
  e.Bm1 + e.P0 * e.y0 = e.P0 * p.c0 + e.P0 * e.s0 + e.Q0 * p.B0

/-- Cochrane (2023), eqs. (1.1) and (1.15), pp. 4, 16, household side: the last-day budget
constraint `B₀ + P₁y₁ = P₁c₁ + P₁s₁ + M₁`. -/
def Budget1 (e : Env Ω) (p : Plan Ω) : Prop :=
  p.B0 + e.P1 * e.y1 = e.P1 * p.c1 + e.P1 * e.s1 + p.M1

/-- Cochrane (2023), §1.3, pp. 7–8: a feasible plan: date-0 choices known at date 0, money
holdings nonnegative, and both budget constraints. -/
def Feasible (𝔼 : ExpectationSystem Ω) (e : Env Ω) (p : Plan Ω) : Prop :=
  Known 𝔼 0 p.c0 ∧ Known 𝔼 0 p.B0 ∧ (∀ ω, 0 ≤ p.M1 ω) ∧ Budget0 e p ∧ Budget1 e p

/-- Cochrane (2023), §1.2, p. 7 (representative agent): expected utility `u(c₀) + βE₀u(c₁)`,
a random variable known at date 0. -/
noncomputable def value (𝔼 : ExpectationSystem Ω) (β : ℝ) (u : ℝ → ℝ) (p : Plan Ω) : Ω → ℝ :=
  (fun ω => u (p.c0 ω)) + β • 𝔼.E 0 (fun ω => u (p.c1 ω))

/-- Cochrane (2023), §1.2, p. 7: an optimal plan: feasible, and no feasible plan has higher
expected utility in any date-0 state. -/
def Optimal (𝔼 : ExpectationSystem Ω) (β : ℝ) (u : ℝ → ℝ) (e : Env Ω) (p : Plan Ω) : Prop :=
  Feasible 𝔼 e p ∧ ∀ q, Feasible 𝔼 e q → value 𝔼 β u q ≤ value 𝔼 β u p

/-- Cochrane (2023), eq. (1.3), p. 8 (the first-order condition behind it): the Euler equation
`Q₀u'(c₀)/P₀ = βE₀[u'(c₁)/P₁]`. -/
def Euler (𝔼 : ExpectationSystem Ω) (β : ℝ) (u' : ℝ → ℝ) (e : Env Ω) (p : Plan Ω) : Prop :=
  (fun ω => e.Q0 ω * u' (p.c0 ω) / e.P0 ω) = β • 𝔼.E 0 (fun ω => u' (p.c1 ω) / e.P1 ω)

/-- Cochrane (2023), §1.1, p. 4 ("nobody wants to hold cash"): `E₀` is faithful when a
nonnegative random variable with zero conditional mean vanishes (no null states). -/
def Faithful0 (𝔼 : ExpectationSystem Ω) : Prop :=
  ∀ x : Ω → ℝ, 0 ≤ x → 𝔼.E 0 x = 0 → x = 0

/-! ### Calculus and expectation tools -/

/-- Cochrane (2023), §1.2, p. 7 (concave utility): a differentiable concave function lies below
its tangent lines, `u(y) ≤ u(x) + u'(x)(y − x)`. -/
theorem le_tangent {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hc : ConcaveOn ℝ Set.univ u) (x y : ℝ) : u y ≤ u x + u' x * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have h := hc.slope_le_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y) hxy (hu x)
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    linarith
  · simp
  · have h := hc.le_slope_of_hasDerivAt (Set.mem_univ y) (Set.mem_univ x) hxy (hu x)
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith

/-- Cochrane (2023), §1.3, p. 8 (differentiating `E₀u(c₁)` along a deviation): for a `C¹`
function `u` and bounded `f`, `g`, the map `ε ↦ E_t[u(f + εg)](ω)` has derivative
`E_t[u'(f)g](ω)` at `0`, for every `ExpectationSystem`. -/
theorem hasDerivAt_E_comp (𝔼 : ExpectationSystem Ω) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') {f g : Ω → ℝ} {K A : ℝ}
    (hf : ∀ ω, |f ω| ≤ K) (hg : ∀ ω, |g ω| ≤ A) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (fun ω' => u (f ω' + ε * g ω')) ω)
      (𝔼.E t (fun ω' => u' (f ω') * g ω') ω) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set A' := max A 1 with hA'
  have hA'pos : 0 < A' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set R := K + A' + 1 with hR
  have huc : UniformContinuousOn u' (Set.Icc (-R) R) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hu'.continuousOn
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp huc (c / A') (div_pos hc hA'pos)
  have hball : Metric.ball (0 : ℝ) (min 1 (δ / A')) ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds 0 (lt_min one_pos (div_pos hδ hA'pos))
  filter_upwards [hball] with h hh
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, lt_min_iff] at hh
  obtain ⟨hh1, hh2⟩ := hh
  -- the pointwise remainder bound
  have hrem : ∀ ω', |u (f ω' + h * g ω') - u (f ω') - h * (u' (f ω') * g ω')| ≤
      c * |h| := by
    intro ω'
    set x0 := f ω'
    set r := |h| * A'
    have hr0 : 0 ≤ r := mul_nonneg (abs_nonneg h) hA'pos.le
    have hgA : |g ω'| ≤ A' := (hg ω').trans (le_max_left _ _)
    have hhg : |h * g ω'| ≤ r := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hgA (abs_nonneg h)
    have hrδ : r < δ := by
      have := (lt_div_iff₀ hA'pos).mp hh2
      linarith [this]
    have hr1 : r ≤ A' := by
      have : |h| * A' ≤ 1 * A' := mul_le_mul_of_nonneg_right hh1.le hA'pos.le
      linarith
    have hx0 : |x0| ≤ K := hf ω'
    set k : ℝ → ℝ := fun x => u x - u' x0 * x with hk
    have hkd : ∀ x ∈ Set.Icc (x0 - r) (x0 + r),
        HasDerivWithinAt k (u' x - u' x0) (Set.Icc (x0 - r) (x0 + r)) x := by
      intro x _
      have h2 : HasDerivAt (fun y => u' x0 * y) (u' x0) x := by
        simpa using (hasDerivAt_id x).const_mul (u' x0)
      have h1 : HasDerivAt k (u' x - u' x0) x := HasDerivAt.sub (hu x) h2
      exact h1.hasDerivWithinAt
    have hbd : ∀ x ∈ Set.Icc (x0 - r) (x0 + r), ‖u' x - u' x0‖ ≤ c / A' := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      have hxR : x ∈ Set.Icc (-R) R := by
        have := abs_le.mp hx0
        exact ⟨by linarith, by linarith⟩
      have hx0R : x0 ∈ Set.Icc (-R) R := by
        have := abs_le.mp hx0
        exact ⟨by linarith, by linarith⟩
      have hd : dist x x0 < δ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      have := hδu x hxR x0 hx0R hd
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]
      exact this.le
    have hmem0 : x0 ∈ Set.Icc (x0 - r) (x0 + r) := ⟨by linarith, by linarith⟩
    have hmem1 : x0 + h * g ω' ∈ Set.Icc (x0 - r) (x0 + r) := by
      have := abs_le.mp hhg
      exact ⟨by linarith, by linarith⟩
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hkd hbd (convex_Icc _ _)
      hmem0 hmem1
    simp only [hk, Real.norm_eq_abs] at hmvt
    have e1 : u (x0 + h * g ω') - u x0 - h * (u' x0 * g ω') =
        u (x0 + h * g ω') - u' x0 * (x0 + h * g ω') - (u x0 - u' x0 * x0) := by ring
    rw [e1]
    calc _ ≤ c / A' * |x0 + h * g ω' - x0| := hmvt
      _ = c / A' * |h * g ω'| := by ring_nf
      _ ≤ c / A' * r := mul_le_mul_of_nonneg_left hhg (div_pos hc hA'pos).le
      _ = c * |h| := by simp only [r]; field_simp
  -- linearity of `E_t`
  set F1 : Ω → ℝ := fun ω' => u (f ω' + h * g ω')
  set F0 : Ω → ℝ := fun ω' => u (f ω')
  set F2 : Ω → ℝ := fun ω' => u' (f ω') * g ω'
  have hF0 : (fun ω' => u (f ω' + 0 * g ω')) = F0 := by
    funext ω'; simp [F0]
  have hlin : 𝔼.E t F1 ω - 𝔼.E t F0 ω - h • 𝔼.E t F2 ω = 𝔼.E t (F1 - F0 - h • F2) ω := by
    rw [map_sub, map_sub, map_smul]; rfl
  simp only [zero_add]
  rw [hF0, hlin, Real.norm_eq_abs, Real.norm_eq_abs]
  exact 𝔼.abs_E_le (fun ω' => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, F1, F0, F2]
    exact hrem ω') t ω


/-! ### Zero demand for money at the end of the last day -/

/-- Cochrane (2023), §1.1, p. 4 ("the world ends on day 2, so nobody wants to hold cash … after
the end of day 1"): with `β > 0`, strictly increasing utility, `P₁ > 0` and a faithful `E₀`, an
optimal plan holds no money at the end of the last day, `M₁ = 0`. -/
theorem money_zero_of_optimal (𝔼 : ExpectationSystem Ω) {β : ℝ} (hβ : 0 < β) {u : ℝ → ℝ}
    (hu : StrictMono u) (hF : Faithful0 𝔼) {e : Env Ω} (hP1 : ∀ ω, 0 < e.P1 ω) {p : Plan Ω}
    (hopt : Optimal 𝔼 β u e p) : p.M1 = 0 := by
  obtain ⟨⟨hk0, hkB, hM, hb0, hb1⟩, hbest⟩ := hopt
  set q : Plan Ω := ⟨p.c0, p.B0, fun ω => p.c1 ω + p.M1 ω / e.P1 ω, 0⟩ with hq
  have hqf : Feasible 𝔼 e q := by
    refine ⟨hk0, hkB, fun _ => le_rfl, hb0, ?_⟩
    funext ω
    have h := congrFun hb1 ω
    have hne := (hP1 ω).ne'
    simp only [Pi.add_apply, Pi.mul_apply, Pi.zero_apply, q] at h ⊢
    field_simp
    linarith
  have hle := hbest q hqf
  set x : Ω → ℝ := fun ω => u (q.c1 ω) - u (p.c1 ω) with hx
  have hx0 : 0 ≤ x := fun ω => by
    have : p.c1 ω ≤ q.c1 ω := by
      simp only [q]
      have := div_nonneg (hM ω) (hP1 ω).le
      linarith
    simp only [hx, Pi.zero_apply, sub_nonneg]
    exact hu.monotone this
  have hEx : 𝔼.E 0 x = 0 := by
    funext ω
    have h1 := hle ω
    have h2 := 𝔼.mono 0 hx0 ω
    rw [map_zero] at h2
    have hlin : 𝔼.E 0 x = 𝔼.E 0 (fun ω => u (q.c1 ω)) - 𝔼.E 0 (fun ω => u (p.c1 ω)) := by
      rw [← map_sub]; rfl
    have h3 := congrFun hlin ω
    simp only [value, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Pi.sub_apply] at h3
    simp only [Pi.zero_apply] at h2
    have h4 : 𝔼.E 0 (fun ω => u (q.c1 ω)) ω ≤ 𝔼.E 0 (fun ω => u (p.c1 ω)) ω := by
      have := le_of_mul_le_mul_left (by linarith : β * 𝔼.E 0 (fun ω => u (q.c1 ω)) ω ≤
        β * 𝔼.E 0 (fun ω => u (p.c1 ω)) ω) hβ
      exact this
    simp only [Pi.zero_apply]
    linarith
  have hxz := hF x hx0 hEx
  funext ω
  have h := congrFun hxz ω
  simp only [hx, Pi.zero_apply, sub_eq_zero, q] at h
  have h' := hu.injective h
  have hne := (hP1 ω).ne'
  have : p.M1 ω / e.P1 ω = 0 := by linarith
  rw [div_eq_zero_iff] at this
  simpa [hne] using this

/-- Cochrane (2023), §1.1, p. 4 (why faithfulness is needed): an expectation system on two
states that puts all weight on the state `true`, `E_t x = x(true)`. The state `false` is a null
state. -/
def pointSystem : ExpectationSystem Bool where
  E := fun _ => LinearMap.pi fun _ => LinearMap.proj true
  const := fun _ _ => rfl
  mono := fun _ _ _ h _ => h true
  tower := fun _ _ => rfl
  known := fun _ _ => rfl

/-- Cochrane (2023), §1.1, p. 4 (**the hypothesis `Faithful0` of `money_zero_of_optimal` is
needed**): under `pointSystem` (not faithful), with linear utility, `β = 1`, unit prices and no
debt or surpluses, the plan that holds one dollar at the end of the last day in the null state
`false` is optimal. -/
theorem money_zero_needs_faithful :
    ¬ Faithful0 pointSystem ∧
      Optimal pointSystem 1 (fun c => c) ⟨0, 0, 0, 1, 1, 1, 0, 0⟩
        ⟨0, 0, fun ω => if ω then 0 else -1, fun ω => if ω then 0 else 1⟩ ∧
      (fun ω : Bool => if ω then (0 : ℝ) else 1) ≠ 0 := by
  have hne : (fun ω : Bool => if ω then (0 : ℝ) else 1) ≠ 0 := fun h => by
    have := congrFun h false
    simp at this
  refine ⟨fun hF => hne (hF _ (fun ω => by cases ω <;> simp) ?_), ⟨?_, fun q hq ω => ?_⟩, hne⟩
  · funext ω; rfl
  · refine ⟨rfl, rfl, fun ω => by cases ω <;> simp, ?_, ?_⟩
    · funext ω; simp
    · funext ω; cases ω <;> simp
  · obtain ⟨-, hkB, hM, hb0, hb1⟩ := hq
    have e0 := congrFun hb0 ω
    have e1 := congrFun hb1 true
    have hB : q.B0 ω = q.B0 true := by
      have := congrFun hkB ω
      exact this.symm
    simp only [Pi.add_apply, Pi.mul_apply, Pi.zero_apply, Pi.one_apply] at e0 e1
    simp only [value, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    change q.c0 ω + q.c1 true ≤ 0 + (if true = true then (0 : ℝ) else -1)
    have := hM true
    simp only [↓reduceIte, add_zero]
    linarith

/-! ### Necessity of the Euler equation -/

/-- Cochrane (2023), eq. (1.3), p. 8: the bond deviation: buy `ε` more bonds at date 0, paid
for by consuming `εQ₀/P₀` less, and consume `ε/P₁` more on the last day. -/
noncomputable def dev (e : Env Ω) (p : Plan Ω) (ε : ℝ) : Plan Ω :=
  ⟨p.c0 - ε • (e.Q0 / e.P0), p.B0 + fun _ => ε, p.c1 + ε • (1 / e.P1), p.M1⟩

/-- Cochrane (2023), eq. (1.3), p. 8: the bond deviation of a feasible plan is feasible
(`P₀, P₁ ≠ 0`; `P₀`, `Q₀` known at date 0; `ExpectationSystem.PullOut`). -/
theorem dev_feasible (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {e : Env Ω}
    (hP0 : ∀ ω, e.P0 ω ≠ 0) (hP1 : ∀ ω, e.P1 ω ≠ 0) (hkP0 : Known 𝔼 0 e.P0)
    (hkQ0 : Known 𝔼 0 e.Q0) {p : Plan Ω} (hp : Feasible 𝔼 e p) (ε : ℝ) :
    Feasible 𝔼 e (dev e p ε) := by
  obtain ⟨hk0, hkB, hM, hb0, hb1⟩ := hp
  refine ⟨known_sub 𝔼 hk0 (known_smul 𝔼 ε (known_div 𝔼 hPO hkQ0 hkP0 hP0)),
    known_add 𝔼 hkB (known_const 𝔼 0 ε), hM, ?_, ?_⟩
  · funext ω
    have h := congrFun hb0 ω
    have hne := hP0 ω
    simp only [dev, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.div_apply] at h ⊢
    have key : e.P0 ω * (ε * (e.Q0 ω / e.P0 ω)) = ε * e.Q0 ω := by field_simp
    linear_combination h + key
  · funext ω
    have h := congrFun hb1 ω
    have hne := hP1 ω
    simp only [dev, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.div_apply,
      Pi.one_apply] at h ⊢
    have key : e.P1 ω * (ε * (1 / e.P1 ω)) = ε := by field_simp
    linear_combination h - key

/-- Cochrane (2023), eq. (1.3), p. 8 (**necessity**): an optimal plan satisfies the Euler
equation `Q₀u'(c₀)/P₀ = βE₀[u'(c₁)/P₁]`, for any utility `u` with continuous derivative `u'`
(no concavity), when `c₁` and `1/P₁` are bounded (`P₀, P₁ ≠ 0`; `P₀`, `Q₀` known at 0;
`ExpectationSystem.PullOut`). -/
theorem euler_of_optimal (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β : ℝ} {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') {e : Env Ω}
    (hP0 : ∀ ω, e.P0 ω ≠ 0) (hP1 : ∀ ω, e.P1 ω ≠ 0) (hkP0 : Known 𝔼 0 e.P0)
    (hkQ0 : Known 𝔼 0 e.Q0) {A : ℝ} (hA : ∀ ω, |1 / e.P1 ω| ≤ A) {p : Plan Ω} {K : ℝ}
    (hK : ∀ ω, |p.c1 ω| ≤ K) (hopt : Optimal 𝔼 β u e p) : Euler 𝔼 β u' e p := by
  obtain ⟨hp, hbest⟩ := hopt
  funext ω
  set k := e.Q0 ω / e.P0 ω with hkdef
  set φ : ℝ → ℝ := fun ε => u (p.c0 ω - ε * k) +
    β * 𝔼.E 0 (fun ω' => u (p.c1 ω' + ε * (1 / e.P1 ω'))) ω with hφ
  have hφv : ∀ ε, φ ε = value 𝔼 β u (dev e p ε) ω := fun ε => rfl
  have hφ0 : φ 0 = value 𝔼 β u p ω := by
    simp only [hφ, zero_mul, sub_zero, add_zero, value, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
  have hmax : IsLocalMax φ 0 := Eventually.of_forall fun ε => by
    rw [hφv, hφ0]
    exact hbest _ (dev_feasible 𝔼 hPO hP0 hP1 hkP0 hkQ0 hp ε) ω
  have hd1 : HasDerivAt (fun ε => u (p.c0 ω - ε * k)) (u' (p.c0 ω) * (-k)) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => p.c0 ω - ε * k) (-k) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).const_sub (p.c0 ω)
    have h2 : HasDerivAt (fun ε => u (p.c0 ω - ε * k)) (u' (p.c0 ω - 0 * k) * (-k)) 0 :=
      (hu (p.c0 ω - 0 * k)).comp (0 : ℝ) h1
    convert h2 using 2
    simp
  have hd2 := (hasDerivAt_E_comp 𝔼 hu hu' hK hA 0 ω).const_mul β
  have hd := hd1.add hd2
  have h0 := hmax.hasDerivAt_eq_zero hd
  have hE : 𝔼.E 0 (fun ω' => u' (p.c1 ω') * (1 / e.P1 ω')) =
      𝔼.E 0 (fun ω' => u' (p.c1 ω') / e.P1 ω') := by
    congr 1; funext ω'; ring
  rw [hE] at h0
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hkdef] at h0
  have hne := hP0 ω
  field_simp
  field_simp at h0
  linarith

/-! ### Sufficiency of the Euler equation -/

/-- Cochrane (2023), eq. (1.3), p. 8 (**sufficiency**): for concave, weakly increasing utility
with derivative `u'`, `β ≥ 0`, `P₀, P₁ > 0`, `ExpectationSystem.PullOut`, a feasible plan with
`M₁ = 0` that
satisfies the Euler equation is optimal: no feasible plan has higher expected utility in any
state. No boundedness is needed. -/
theorem optimal_of_euler (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β : ℝ} (hβ : 0 ≤ β)
    {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x) (hc : ConcaveOn ℝ Set.univ u)
    (hu'0 : ∀ x, 0 ≤ u' x) {e : Env Ω} (hP0 : ∀ ω, 0 < e.P0 ω) (hP1 : ∀ ω, 0 < e.P1 ω)
    {p : Plan Ω} (hp : Feasible 𝔼 e p) (hM : p.M1 = 0) (hE : Euler 𝔼 β u' e p) :
    Optimal 𝔼 β u e p := by
  refine ⟨hp, fun q hq ω => ?_⟩
  obtain ⟨-, hkB, -, hb0, hb1⟩ := hp
  obtain ⟨-, hkB', hM', hb0', hb1'⟩ := hq
  set d : Ω → ℝ := q.B0 - p.B0 with hd
  have hkd : Known 𝔼 0 d := known_sub 𝔼 hkB' hkB
  set W : Ω → ℝ := fun ω => u' (p.c1 ω) / e.P1 ω with hW
  -- date 0
  have hc0 : q.c0 ω - p.c0 ω = -(e.Q0 ω / e.P0 ω) * d ω := by
    have h1 := congrFun hb0 ω
    have h2 := congrFun hb0' ω
    have hne := (hP0 ω).ne'
    simp only [Pi.add_apply, Pi.mul_apply] at h1 h2
    simp only [hd, Pi.sub_apply]
    field_simp
    linear_combination h1 - h2
  have hu0 := le_tangent hu hc (p.c0 ω) (q.c0 ω)
  -- date 1, state by state
  have hc1 : ∀ ω', u (q.c1 ω') ≤ u (p.c1 ω') + d ω' * W ω' := by
    intro ω'
    have h1 := congrFun hb1 ω'
    have h2 := congrFun hb1' ω'
    have hne := (hP1 ω').ne'
    have hM0 := congrFun hM ω'
    simp only [Pi.add_apply, Pi.mul_apply, Pi.zero_apply] at h1 h2 hM0
    have hdiff : q.c1 ω' - p.c1 ω' = (d ω' - q.M1 ω') / e.P1 ω' := by
      simp only [hd, Pi.sub_apply]
      field_simp
      linear_combination h1 - h2 + hM0
    have ht := le_tangent hu hc (p.c1 ω') (q.c1 ω')
    rw [hdiff] at ht
    have hnn : 0 ≤ u' (p.c1 ω') * (q.M1 ω' / e.P1 ω') :=
      mul_nonneg (hu'0 _) (div_nonneg (hM' ω') (hP1 ω').le)
    have : u' (p.c1 ω') * ((d ω' - q.M1 ω') / e.P1 ω') =
        d ω' * W ω' - u' (p.c1 ω') * (q.M1 ω' / e.P1 ω') := by
      simp only [hW]; ring
    linarith
  have hmono := 𝔼.mono 0 (fun ω' => hc1 ω') ω
  have hlin : 𝔼.E 0 (fun ω' => u (p.c1 ω') + d ω' * W ω') ω =
      𝔼.E 0 (fun ω' => u (p.c1 ω')) ω + d ω * 𝔼.E 0 W ω := by
    have h1 : (fun ω' => u (p.c1 ω') + d ω' * W ω') = (fun ω' => u (p.c1 ω')) + d * W := rfl
    rw [h1, map_add, hPO 0 d W hkd]
    rfl
  rw [hlin] at hmono
  have hEω := congrFun hE ω
  simp only [Pi.smul_apply, smul_eq_mul] at hEω
  simp only [value, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hc0] at hu0
  have hβm := mul_le_mul_of_nonneg_left hmono hβ
  have hne := (hP0 ω).ne'
  have key : u' (p.c0 ω) * (-(e.Q0 ω / e.P0 ω) * d ω) + β * (d ω * 𝔼.E 0 W ω) = 0 := by
    have : e.Q0 ω / e.P0 ω * u' (p.c0 ω) = β * 𝔼.E 0 W ω := by
      rw [← hEω]; ring
    linear_combination (-(d ω)) * this
  nlinarith

/-- Cochrane (2023), §1.1, p. 4, and eq. (1.3), p. 8: **the household problem, necessity and
sufficiency.** For concave utility with continuous derivative `u' > 0`, `β > 0`, a faithful
`E₀`, `ExpectationSystem.PullOut`, `P₀, P₁ > 0`, `P₀`, `Q₀` known at 0, and bounded `c₁`, `1/P₁`: a
plan is
optimal iff it is feasible, holds no money at the end of the last day, and satisfies the Euler
equation. -/
theorem optimal_iff (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) (hF : Faithful0 𝔼) {β : ℝ}
    (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u')
    (hc : ConcaveOn ℝ Set.univ u) (hu'0 : ∀ x, 0 < u' x) {e : Env Ω}
    (hP0 : ∀ ω, 0 < e.P0 ω) (hP1 : ∀ ω, 0 < e.P1 ω) (hkP0 : Known 𝔼 0 e.P0)
    (hkQ0 : Known 𝔼 0 e.Q0) {A : ℝ} (hA : ∀ ω, |1 / e.P1 ω| ≤ A) {p : Plan Ω} {K : ℝ}
    (hK : ∀ ω, |p.c1 ω| ≤ K) :
    Optimal 𝔼 β u e p ↔ Feasible 𝔼 e p ∧ p.M1 = 0 ∧ Euler 𝔼 β u' e p := by
  have hsm : StrictMono u := strictMono_of_deriv_pos fun x => by
    rw [(hu x).deriv]; exact hu'0 x
  constructor
  · intro hopt
    exact ⟨hopt.1, money_zero_of_optimal 𝔼 hβ hsm hF hP1 hopt,
      euler_of_optimal 𝔼 hPO hu hu' (fun ω => (hP0 ω).ne') (fun ω => (hP1 ω).ne') hkP0 hkQ0
        hA hK hopt⟩
  · rintro ⟨hp, hM, hE⟩
    exact optimal_of_euler 𝔼 hPO hβ.le hu hc (fun x => (hu'0 x).le) hP0 hP1 hp hM hE

/-! ### The bond-pricing equation (1.3) -/

/-- Cochrane (2023), eq. (1.3), p. 8 (**(1.3) derived**): at constant consumption `c₀ = c₁ = ȳ`
with `u'(ȳ) ≠ 0`, the Euler equation is exactly the bond-pricing equation
`Q₀ = βE₀(P₀/P₁)` (`P₀ ≠ 0` known at 0; `ExpectationSystem.PullOut`). -/
theorem euler_const_iff_bondPrice (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β : ℝ}
    {u' : ℝ → ℝ} {ybar : ℝ} (hy : u' ybar ≠ 0) {e : Env Ω} (hP0 : ∀ ω, e.P0 ω ≠ 0)
    (hkP0 : Known 𝔼 0 e.P0) {p : Plan Ω} (hc0 : p.c0 = fun _ => ybar)
    (hc1 : p.c1 = fun _ => ybar) : Euler 𝔼 β u' e p ↔ BondPrice0 𝔼 β e.P0 e.P1 e.Q0 := by
  have hE1 : 𝔼.E 0 (fun ω => u' (p.c1 ω) / e.P1 ω) = u' ybar • 𝔼.E 0 (1 / e.P1) := by
    rw [hc1, ← map_smul]
    congr 1
    funext ω
    simp only [Pi.smul_apply, Pi.div_apply, Pi.one_apply, smul_eq_mul]
    ring
  have hE2 : 𝔼.E 0 (e.P0 / e.P1) = e.P0 * 𝔼.E 0 (1 / e.P1) := by
    rw [← hPO 0 _ _ hkP0]
    congr 1
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply, Pi.one_apply]
    ring
  unfold Euler BondPrice0
  rw [hE1, hE2, hc0]
  constructor
  · intro h
    funext ω
    have h1 := congrFun h ω
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h1 ⊢
    rw [div_eq_iff (hP0 ω)] at h1
    apply mul_right_cancel₀ hy
    linear_combination h1
  · intro h
    funext ω
    have h1 := congrFun h ω
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h1 ⊢
    rw [h1]
    field_simp [hP0 ω]

/-- Cochrane (2023), eq. (1.3), p. 8, and §1.2, p. 7 (why the constant endowment matters): when
the household consumes a random endowment, `c₀ = y₀`, `c₁ = y₁`, the Euler equation is
`Q₀ = βE₀[(u'(y₁)/u'(y₀))(P₀/P₁)]`, the bond price with the stochastic discount factor
`βu'(y₁)/u'(y₀)` (`u' > 0`; `P₀ ≠ 0`; `P₀` and `u'(y₀)` known at 0; `ExpectationSystem.PullOut`). -/
theorem euler_iff_sdf (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β : ℝ} {u' : ℝ → ℝ}
    (hu'0 : ∀ x, 0 < u' x) {e : Env Ω} (hP0 : ∀ ω, e.P0 ω ≠ 0) (hkP0 : Known 𝔼 0 e.P0)
    {p : Plan Ω} (hkm : Known 𝔼 0 (fun ω => u' (p.c0 ω))) :
    Euler 𝔼 β u' e p ↔
      e.Q0 = β • 𝔼.E 0 (fun ω => u' (p.c1 ω) / u' (p.c0 ω) * (e.P0 ω / e.P1 ω)) := by
  have hkr : Known 𝔼 0 (e.P0 / fun ω => u' (p.c0 ω)) :=
    known_div 𝔼 hPO hkP0 hkm fun ω => (hu'0 _).ne'
  have hE : 𝔼.E 0 (fun ω => u' (p.c1 ω) / u' (p.c0 ω) * (e.P0 ω / e.P1 ω)) =
      (e.P0 / fun ω => u' (p.c0 ω)) * 𝔼.E 0 (fun ω => u' (p.c1 ω) / e.P1 ω) := by
    rw [← hPO 0 _ _ hkr]
    congr 1
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    ring
  unfold Euler
  rw [hE]
  constructor
  · intro h
    funext ω
    have h1 := congrFun h ω
    simp only [Pi.smul_apply, Pi.mul_apply, Pi.div_apply, smul_eq_mul] at h1 ⊢
    have hne := (hu'0 (p.c0 ω)).ne'
    rw [div_eq_iff (hP0 ω)] at h1
    field_simp
    linear_combination h1
  · intro h
    funext ω
    have h1 := congrFun h ω
    simp only [Pi.smul_apply, Pi.mul_apply, Pi.div_apply, smul_eq_mul] at h1 ⊢
    have hne := (hu'0 (p.c0 ω)).ne'
    rw [h1]
    field_simp [hP0 ω]

/-! ### Competitive equilibrium = the fiscal-theory equilibrium -/

/-- Cochrane (2023), §1.2, p. 7 and §1.3, pp. 7–8 (the complete model: representative agent,
constant endowment `ȳ`, flexible prices): a competitive equilibrium given fiscal policy and the
debt sale `(B₋₁, B₀, s₀, s₁)` is a price triple `(P₀, P₁, Q₀)` (positive price levels, `P₀`
and `Q₀` known at date 0) at which an optimal household plan consumes the endowment at both
dates (goods markets clear) and buys the bonds `B₀` the government sells. -/
def CompEqm (𝔼 : ExpectationSystem Ω) (β : ℝ) (u : ℝ → ℝ) (ybar : ℝ)
    (Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ) : Prop :=
  (∀ ω, 0 < P0 ω) ∧ (∀ ω, 0 < P1 ω) ∧ Known 𝔼 0 P0 ∧ Known 𝔼 0 Q0 ∧
    ∃ M1 : Ω → ℝ, Optimal 𝔼 β u ⟨Bm1, fun _ => ybar, fun _ => ybar, P0, P1, Q0, s0, s1⟩
      ⟨fun _ => ybar, B0, fun _ => ybar, M1⟩

/-- Cochrane (2023), eqs. (1.1)–(1.4), pp. 4–8: **the equilibrium conditions are derived from
optimisation.** For concave utility with continuous derivative `u' > 0`, `β > 0`, a faithful
`E₀` and `ExpectationSystem.PullOut`, and `B₀ > 0` known at 0 with `s₁/B₀` bounded, a price triple
is a
competitive equilibrium iff it is a fiscal-theory equilibrium (`TwoPeriod.Equilibrium`): the
flow condition (1.2) is the household budget at market clearing, (1.3) is the Euler equation,
and (1.4) is the last-day budget with the derived `M₁ = 0`. -/
theorem compEqm_iff_equilibrium (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) (hF : Faithful0 𝔼)
    {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') (hc : ConcaveOn ℝ Set.univ u) (hu'0 : ∀ x, 0 < u' x) (ybar : ℝ)
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) {A : ℝ}
    (hA : ∀ ω, |s1 ω / B0 ω| ≤ A) :
    CompEqm 𝔼 β u ybar Bm1 B0 s0 s1 P0 P1 Q0 ↔ Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0 := by
  have hsm : StrictMono u := strictMono_of_deriv_pos fun x => by
    rw [(hu x).deriv]; exact hu'0 x
  constructor
  · rintro ⟨hP0, hP1, hkP0, hkQ0, M1, hopt⟩
    have hM := money_zero_of_optimal 𝔼 hβ hsm hF hP1 hopt
    have hb0 := hopt.1.2.2.2.1
    have hb1 := hopt.1.2.2.2.2
    have hflow : Flow0 Bm1 P0 s0 Q0 B0 := by
      funext ω
      have h := congrFun hb0 ω
      simp only [Pi.add_apply, Pi.mul_apply] at h ⊢
      linarith
    have hB : ∀ ω, B0 ω = P1 ω * s1 ω := fun ω => by
      have h := congrFun hb1 ω
      have h0 := congrFun hM ω
      simp only [Pi.add_apply, Pi.mul_apply, Pi.zero_apply] at h h0
      linarith
    have h1 : Valuation1 B0 P1 s1 := by
      funext ω
      simp only [Pi.div_apply]
      rw [div_eq_iff (hP1 ω).ne', hB ω]
      ring
    have hAP : ∀ ω, |1 / P1 ω| ≤ A := fun ω => by
      have hne := (hB0 ω).ne'
      have hne1 := (hP1 ω).ne'
      have hs : s1 ω ≠ 0 := fun h0 => hne (by rw [hB ω, h0, mul_zero])
      have : 1 / P1 ω = s1 ω / B0 ω := by
        rw [hB ω]; field_simp
      rw [this]; exact hA ω
    have hE := euler_of_optimal 𝔼 hPO hu hu' (fun ω => (hP0 ω).ne') (fun ω => (hP1 ω).ne')
      hkP0 hkQ0 hAP (K := |ybar|) (fun _ => le_rfl) hopt
    have hQ := (euler_const_iff_bondPrice 𝔼 hPO (hu'0 ybar).ne'
      (e := ⟨Bm1, fun _ => ybar, fun _ => ybar, P0, P1, Q0, s0, s1⟩)
      (fun ω => (hP0 ω).ne') hkP0 rfl rfl).mp hE
    exact ⟨hP0, hP1, hkP0, hflow, hQ, h1⟩
  · rintro ⟨hP0, hP1, hkP0, hflow, hQ, h1⟩
    have hkQ0 : Known 𝔼 0 Q0 := by
      rw [hQ]; exact known_smul 𝔼 β (known_E 𝔼 0 _)
    refine ⟨hP0, hP1, hkP0, hkQ0, 0, ?_⟩
    have hp : Feasible 𝔼 ⟨Bm1, fun _ => ybar, fun _ => ybar, P0, P1, Q0, s0, s1⟩
        ⟨fun _ => ybar, B0, fun _ => ybar, 0⟩ := by
      refine ⟨known_const 𝔼 0 ybar, hkB0, fun _ => le_rfl, ?_, ?_⟩
      · funext ω
        have h := congrFun hflow ω
        simp only [Pi.add_apply, Pi.mul_apply] at h ⊢
        linarith
      · funext ω
        have h := congrFun h1 ω
        simp only [Pi.div_apply] at h
        rw [div_eq_iff (hP1 ω).ne'] at h
        simp only [Pi.add_apply, Pi.mul_apply, Pi.zero_apply]
        rw [h]
        ring
    have hE := (euler_const_iff_bondPrice 𝔼 hPO (hu'0 ybar).ne'
      (e := ⟨Bm1, fun _ => ybar, fun _ => ybar, P0, P1, Q0, s0, s1⟩)
      (p := ⟨fun _ => ybar, B0, fun _ => ybar, 0⟩)
      (fun ω => (hP0 ω).ne') hkP0 rfl rfl).mpr hQ
    exact optimal_of_euler 𝔼 hPO hβ.le hu hc (fun x => (hu'0 x).le) hP0 hP1 hp rfl hE

/-! ### Finite event trees -/

/-- Cochrane (2023), §1.3, p. 8 (genuine uncertainty): on a finite event tree with strictly
positive state probabilities, `E₀` is faithful. -/
theorem finiteTree_faithful0 [Fintype Ω] (T : FiniteTree Ω) :
    Faithful0 T.toExpectationSystem := by
  classical
  intro x hx h
  funext ω
  have h1 := congrFun h ω
  rw [FiniteTree.toExpectationSystem_E] at h1
  simp only [FiniteTree.condE, Pi.zero_apply, div_eq_zero_iff,
    (T.mass_pos 0 ω).ne', or_false] at h1
  unfold FiniteTree.num at h1
  have hnn : ∀ ω' ∈ Finset.univ,
      (0 : ℝ) ≤ if T.info 0 ω' ω then T.prob ω' * x ω' else 0 := fun ω' _ => by
    split_ifs
    · exact mul_nonneg (T.prob_pos ω').le (hx ω')
    · exact le_rfl
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h1 ω (Finset.mem_univ ω)
  simp only [(T.info 0).refl ω, ↓reduceIte, mul_eq_zero, (T.prob_pos ω).ne', false_or] at h2
  exact h2

/-- Cochrane (2023), eqs. (1.1)–(1.4), pp. 4–8, on every finite event tree: a price triple is a
competitive equilibrium iff it is a fiscal-theory equilibrium (concave `C¹` utility with
`u' > 0`, `β > 0`, `B₀ > 0` known at 0); no boundedness hypothesis is needed. -/
theorem finiteTree_compEqm_iff [Fintype Ω] (T : FiniteTree Ω) {β : ℝ} (hβ : 0 < β)
    {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u')
    (hc : ConcaveOn ℝ Set.univ u) (hu'0 : ∀ x, 0 < u' x) (ybar : ℝ)
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω)
    (hkB0 : Known T.toExpectationSystem 0 B0) :
    CompEqm T.toExpectationSystem β u ybar Bm1 B0 s0 s1 P0 P1 Q0 ↔
      Equilibrium T.toExpectationSystem β Bm1 B0 s0 s1 P0 P1 Q0 :=
  compEqm_iff_equilibrium _ (finiteTree_pullOut T) (finiteTree_faithful0 T) hβ hu hu' hc hu'0
    ybar hB0 hkB0 (A := ∑ ω, |s1 ω / B0 ω|) fun ω =>
      Finset.single_le_sum (f := fun ω => |s1 ω / B0 ω|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ ω)

/-- Cochrane (2023), §1.3, pp. 7–8, on every finite event tree: **there is exactly one
competitive equilibrium**, the fiscal-theory equilibrium `P₁ = B₀/s₁`, `P₀ = B₋₁/(s₀ + βE₀s₁)`
(hypotheses of `TwoPeriod.equilibrium_existsUnique`; concave `C¹` utility with `u' > 0`). -/
theorem finiteTree_compEqm_existsUnique [Fintype Ω] (T : FiniteTree Ω) {β : ℝ} (hβ : 0 < β)
    {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u')
    (hc : ConcaveOn ℝ Set.univ u) (hu'0 : ∀ x, 0 < u' x) (ybar : ℝ) {Bm1 B0 s0 s1 : Ω → ℝ}
    (hBm1 : ∀ ω, 0 < Bm1 ω) (hkBm1 : Known T.toExpectationSystem 0 Bm1)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known T.toExpectationSystem 0 B0)
    (hks0 : Known T.toExpectationSystem 0 s0) (hs1 : ∀ ω, 0 < s1 ω)
    (hpv : ∀ ω, 0 < pv T.toExpectationSystem β s0 s1 ω) :
    ∃! p : (Ω → ℝ) × (Ω → ℝ) × (Ω → ℝ),
      CompEqm T.toExpectationSystem β u ybar Bm1 B0 s0 s1 p.1 p.2.1 p.2.2 := by
  obtain ⟨x, hx, huq⟩ := equilibrium_existsUnique _ (finiteTree_pullOut T) hBm1 hkBm1 hB0 hkB0
    hks0 hs1 hpv
  have key := fun p : (Ω → ℝ) × (Ω → ℝ) × (Ω → ℝ) =>
    finiteTree_compEqm_iff T hβ hu hu' hc hu'0 ybar (s0 := s0) (s1 := s1) (Bm1 := Bm1)
      (P0 := p.1) (P1 := p.2.1) (Q0 := p.2.2) hB0 hkB0
  exact ⟨x, (key x).mpr hx, fun y hy => huq y ((key y).mp hy)⟩

/-- Cochrane (2023), §1.3, p. 8, the coin-flip economy of `TwoPeriod.coin_equilibrium` with
linear utility `u(c) = c`: there is exactly one competitive equilibrium, and in it
`P₁ = 1/2` after heads, `P₁ = 1` after tails and `P₀ = 4/3`. -/
theorem coin_compEqm (ybar : ℝ) :
    (∃! p : (Bool × Bool → ℝ) × (Bool × Bool → ℝ) × (Bool × Bool → ℝ),
      CompEqm coinSystem (1 / 2) (fun c => c) ybar 1 1 0 (1 + firstHeads) p.1 p.2.1 p.2.2) ∧
    ∀ P0 P1 Q0 : Bool × Bool → ℝ,
      CompEqm coinSystem (1 / 2) (fun c => c) ybar 1 1 0 (1 + firstHeads) P0 P1 Q0 →
        P1 (true, true) = 1 / 2 ∧ P1 (false, false) = 1 ∧ ∀ ω, P0 ω = 4 / 3 := by
  have hu : ∀ x : ℝ, HasDerivAt (fun c : ℝ => c) ((fun _ => (1 : ℝ)) x) x :=
    fun x => hasDerivAt_id' x
  have hc : ConcaveOn ℝ Set.univ (fun c : ℝ => c) := concaveOn_id convex_univ
  have hpos : ∀ ω, (0 : ℝ) < (1 : Bool × Bool → ℝ) ω := fun _ => one_pos
  have hk1 : Known coinSystem 0 (1 : Bool × Bool → ℝ) := known_const coinSystem 0 1
  have hE : ∀ ω, coinSystem.E 0 (1 + firstHeads) ω = 3 / 2 := by
    intro ω
    have h1 : coinSystem.E 0 (1 : Bool × Bool → ℝ) = fun _ => 1 := coinSystem.const 0 1
    rw [map_add, Pi.add_apply, h1, coinSystem_E0_firstHeads]
    norm_num
  have hk0 : Known coinSystem 0 (0 : Bool × Bool → ℝ) := known_const coinSystem 0 0
  have hs1 : ∀ ω, 0 < (1 + firstHeads) ω := by
    intro ω
    simp only [Pi.add_apply, Pi.one_apply, firstHeads]
    split_ifs <;> norm_num
  have hpv : ∀ ω, 0 < pv coinSystem (1 / 2) 0 (1 + firstHeads) ω := by
    intro ω
    simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hE]
    norm_num
  refine ⟨finiteTree_compEqm_existsUnique coinTree (by norm_num) hu continuous_const hc
    (fun _ => one_pos) ybar hpos hk1 hpos hk1 hk0 hs1 hpv, fun P0 P1 Q0 h => ?_⟩
  exact coin_equilibrium.2 P0 P1 Q0 ((finiteTree_compEqm_iff coinTree (by norm_num) hu
    continuous_const hc (fun _ => one_pos) ybar hpos hk1).mp h)


end Cochrane.TwoPeriodModel.TidyR6Household
