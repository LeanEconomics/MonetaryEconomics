/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.Links
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Further links: finite-time explosion, the tree household problem, and Galí's money rule

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.2 (pp. 436–438),
§19.3 (pp. 439–445, Figure 19.1, p. 444), §19.5 (pp. 447–454), and Online Appendix A3,
§3.2, eq. (3.3), p. 619. Three bridges left open by `Links`.

## Main results

* **Finite-time explosion, both coordinates.** The statement of
  `MoneyTargetingDynamics.power_inflation_exits` (in `x = Py/M`, Figure 19.1) and that of
  `PruningInflation.finite_time_explosion` (in `m = M/(Py)`, A3 (3.3)) are each derived from the
  other (`explosion_of_exits`, `exits_of_explosion`, `exits_iff_explosion`), with the two
  re-derivations `finite_time_explosion_of_power_exits` and
  `power_exits_of_finite_time_explosion`.
* **The cash-in-advance tree problem is the footnote-1 tree problem.** With `V = 1`, the
  CIA household problem on a finite event tree (`CashInAdvance.TreeEuler.IsOptimal`) is
  `MoneyInUtility.FootnoteTree.TOptimal` with utility independent of money and `ι = 0`, for any
  adapted money plan (`TreeBridge.isOptimal_iff_tOptimal_of_adapted`,
  `TreeBridge.isOptimal_iff_tOptimal`). The Euler results then pass both ways: the CIA Euler
  equation follows from the footnote-tree perturbation lemma, without the positivity of state
  prices that `TreeEuler.euler_necessary` assumes (`TreeBridge.tree_euler_necessary_general`);
  the footnote-tree first-order condition and sufficiency theorem for the money-free problem
  follow from the CIA ones (`TreeBridge.tree_foc_cc_of_cia_euler`,
  `TreeBridge.tree_optimal_of_foc_of_cia`); and the full CIA sufficiency theorem, with
  node-indexed supergradients and non-measurable state prices, follows from
  `FootnoteTree.tree_optimal_of_foc` by averaging over information cells
  (`TreeBridge.euler_sufficient_of_tree_optimal_of_foc`, through `TreeBridge.sum_prob_condE`,
  `TreeBridge.pvCost_condE`, `TreeBridge.isOptimal_condE_iff`).
* **Galí's money rule.** Galí's (2015) money-rule system (34) and its equilibrium notion are
  restated from the Galí Chapter 3/4 projects (`GaliMoneyRule.System34`,
  `GaliMoneyRule.system34_iff`, `GaliMoneyRule.Equil34`). Its money-demand block with a zero
  output gap is Cochrane's Cagan equation (19.5) with `a = η`
  (`GaliMoneyRule.eq32_zero_gap_iff`, `GaliMoneyRule.flexBlock_iff_cagan`). Zero-gap equilibria
  of (34) are exactly the flexible-price equilibria with `π_t = βE_tπ_{t+1}`
  (`GaliMoneyRule.system34_zero_gap_iff`, `GaliMoneyRule.equil34_zero_gap_iff`), and in general
  the flexible-price equilibrium is not one (`GaliMoneyRule.flex_not_zero_gap_eq34`). The
  flexible-price model is determinate in Galí's sense (`GaliMoneyRule.flex_existsUnique`). With
  constant money its equilibrium is Cochrane's steady state
  (`GaliMoneyRule.flex_constant_money_steady`), and Galí's boundedness requirement is exactly
  Cochrane's selection of the bounded Cagan path (`GaliMoneyRule.cagan_realBalances_bounded_iff`).
-/

namespace Cochrane.Monetarism.LinksTidy

/-- Cochrane (2023), Figure 19.1, p. 444: the statement of
`MoneyTargetingDynamics.power_inflation_exits`, as a proposition quantified over all parameters
(every path of (19.23) started above `x̄` reaches `θx_t^γ ≥ 1` in finite time). -/
def ExitsStatement : Prop :=
  ∀ (θ γ xb : ℝ) (x : ℕ → ℝ), 0 < θ → 0 < γ → 0 < xb → 0 < 1 - θ * xb ^ γ →
    (∀ t, θ * x t ^ γ < 1 → x (t + 1) = MoneyInUtility.nextX θ γ xb (x t)) → xb < x 0 →
      ∃ t, 1 ≤ θ * x t ^ γ

/-- Cochrane (2023), Online Appendix eq. (3.3), p. 619: the statement of
`PruningInflation.finite_time_explosion`, as a proposition quantified over all parameters
(every real-balance orbit from `0 < m₀ < m̄` reaches `m_T ≤ m_p` at a first finite date). -/
def ExplosionStatement : Prop :=
  ∀ β μ θ γ ms m0 : ℝ, 0 < β → 0 < 1 + μ → 0 < θ → 0 < γ →
    θ * ms ^ (-γ) = 1 - β / (1 + μ) → 0 < m0 → m0 < ms →
      ∃ T, (PruningDeflation.ratioMap β μ θ γ)^[T] m0 ≤ θ ^ (1 / γ) ∧
        ∀ t < T, θ ^ (1 / γ) < (PruningDeflation.ratioMap β μ θ γ)^[t] m0

/-- Cochrane (2023), Figure 19.1, p. 444 ⇒ Online Appendix (3.3), p. 619: the finite-time
explosion in real balances `m = M/(Py)` follows from the finite-time exit of the (19.23) orbit
in `x = Py/M = 1/m`. If the orbit stayed above `m_p` forever, `x_t = 1/m_t` would be a (19.23)
path above `x̄ = 1/m̄` that never exits; the first explosion date is then `Nat.find`. -/
theorem explosion_of_exits (h : ExitsStatement) : ExplosionStatement := by
  intro β μ θ γ ms m0 hβ hμ hθ hγ hss hm0 hlt
  set g := PruningDeflation.ratioMap β μ θ γ with hg
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  have hms : 0 < ms := hm0.trans hlt
  have hex : ∃ T, g^[T] m0 ≤ θ ^ (1 / γ) := by
    by_contra hcon
    push Not at hcon
    have hpos : ∀ t, 0 < g^[t] m0 := fun t => hwp.trans (hcon t)
    have hdom : ∀ t, θ * (1 / g^[t] m0) ^ γ < 1 := by
      intro t
      have := (PruningInflation.explosion_x_form hθ hγ (hpos t)).not.mp
        (not_le.mpr (hcon t))
      push Not at this
      linarith
    have hxb : θ * (1 / ms) ^ γ = 1 - β / (1 + μ) := by
      rw [Links.one_div_rpow_eq hms, hss]
    have hK : 0 < 1 - θ * (1 / ms) ^ γ := by
      rw [hxb]; have := div_pos hβ hμ; linarith
    obtain ⟨t, ht⟩ := h θ γ (1 / ms) (fun t => 1 / g^[t] m0) hθ hγ (one_div_pos.mpr hms) hK
      (fun t _ => by
        rw [Function.iterate_succ_apply']
        exact (PruningDeflation.eq1923_iff hβ hμ (hpos t) (hdom t).ne hxb).mp rfl)
      (by
        rw [Function.iterate_zero_apply]
        exact one_div_lt_one_div_of_lt hm0 hlt)
    linarith [hdom t]
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun t ht => ?_⟩
  have := Nat.find_min hex ht
  push Not at this
  exact this

/-- Cochrane (2023), Online Appendix (3.3), p. 619 ⇒ Figure 19.1, p. 444: the finite-time exit
of the (19.23) orbit in `x = Py/M` follows from the finite-time explosion of real balances
`m = 1/x`, with `β/(1 + µ) = 1 − θx̄^γ` (take `µ = 0`, `β = 1 − θx̄^γ`) and `m̄ = 1/x̄`. -/
theorem exits_of_explosion (h : ExplosionStatement) : ExitsStatement := by
  intro θ γ xb x hθ hγ hxb hK hrec h0
  by_contra hcon
  push Not at hcon
  have hrec' : ∀ t, x (t + 1) = MoneyInUtility.nextX θ γ xb (x t) := fun t => hrec t (hcon t)
  have hxpos : ∀ t, 0 < x t := by
    intro t
    induction t with
    | zero => exact hxb.trans h0
    | succ n ih => rw [hrec' n]; exact MoneyTargetingDynamics.nextX_pos hK ih (hcon n)
  set β := 1 - θ * xb ^ γ with hβdef
  have hss0 : θ * xb ^ γ = 1 - β / (1 + 0) := by rw [add_zero, div_one, hβdef]; ring
  have hss : θ * (1 / xb) ^ (-γ) = 1 - β / (1 + 0) := by
    rw [← Links.one_div_rpow_eq (one_div_pos.mpr hxb), one_div_one_div]
    exact hss0
  have hμ : (0 : ℝ) < 1 + 0 := by norm_num
  obtain ⟨T, hT, -⟩ := h β 0 θ γ (1 / xb) (1 / x 0) hK hμ hθ hγ hss
    (one_div_pos.mpr (hxpos 0)) (one_div_lt_one_div_of_lt hxb h0)
  have horb : ∀ t, (PruningDeflation.ratioMap β 0 θ γ)^[t] (1 / x 0) = 1 / x t := by
    intro t
    induction t with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      have hden : θ * (1 / (1 / x n)) ^ γ ≠ 1 := by rw [one_div_one_div]; exact (hcon n).ne
      refine ((PruningDeflation.eq1923_iff hK hμ (one_div_pos.mpr (hxpos n)) hden hss0).mpr
        ?_).symm
      rw [one_div_one_div, one_div_one_div]
      exact hrec' n
  rw [horb T] at hT
  have := (PruningInflation.explosion_x_form hθ hγ (one_div_pos.mpr (hxpos T))).mp hT
  rw [one_div_one_div] at this
  linarith [hcon T]

/-- Cochrane (2023), Figure 19.1, p. 444, and Online Appendix (3.3), p. 619: the finite-time
exit of the (19.23) orbit (`power_inflation_exits`) and the finite-time explosion of real
balances (`finite_time_explosion`) are equivalent statements, each derived from the other. -/
theorem exits_iff_explosion : ExitsStatement ↔ ExplosionStatement :=
  ⟨explosion_of_exits, exits_of_explosion⟩

/-- Cochrane (2023), Figure 19.1, p. 444: `MoneyTargetingDynamics.power_inflation_exits` proves
`ExitsStatement`. -/
theorem exitsStatement_holds : ExitsStatement :=
  fun _ _ _ _ hθ hγ hxb hK hrec h0 =>
    MoneyTargetingDynamics.power_inflation_exits hθ hγ hxb hK hrec h0

/-- Cochrane (2023), Online Appendix (3.3), p. 619: `PruningInflation.finite_time_explosion`
proves `ExplosionStatement`. -/
theorem explosionStatement_holds : ExplosionStatement :=
  fun _ _ _ _ _ _ hβ hμ hθ hγ hss hm0 hlt =>
    PruningInflation.finite_time_explosion hβ hμ hθ hγ hss hm0 hlt

/-- Cochrane (2023), Online Appendix (3.3), p. 619: `PruningInflation.finite_time_explosion`
re-derived from `MoneyTargetingDynamics.power_inflation_exits` alone. -/
theorem finite_time_explosion_of_power_exits {β μ θ γ ms m0 : ℝ} (hβ : 0 < β)
    (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hm0 : 0 < m0) (hlt : m0 < ms) :
    ∃ T, (PruningDeflation.ratioMap β μ θ γ)^[T] m0 ≤ θ ^ (1 / γ) ∧
      ∀ t < T, θ ^ (1 / γ) < (PruningDeflation.ratioMap β μ θ γ)^[t] m0 :=
  explosion_of_exits exitsStatement_holds β μ θ γ ms m0 hβ hμ hθ hγ hss hm0 hlt

/-- Cochrane (2023), Figure 19.1, p. 444: `MoneyTargetingDynamics.power_inflation_exits`
re-derived from `PruningInflation.finite_time_explosion` alone. -/
theorem power_exits_of_finite_time_explosion {θ γ xb : ℝ} {x : ℕ → ℝ} (hθ : 0 < θ)
    (hγ : 0 < γ) (hxb : 0 < xb) (hK : 0 < 1 - θ * xb ^ γ)
    (hrec : ∀ t, θ * x t ^ γ < 1 → x (t + 1) = MoneyInUtility.nextX θ γ xb (x t))
    (h0 : xb < x 0) : ∃ t, 1 ≤ θ * x t ^ γ :=
  exits_of_explosion explosionStatement_holds θ γ xb x hθ hγ hxb hK hrec h0

namespace TreeBridge

open ExpectationsFiniteTree

variable {Ω : Type*} [Fintype Ω] (T : FiniteTree Ω)

/-- Cochrane (2023), (19.30), p. 449, and footnote 1, p. 440: with a zero cost of money
(`ι = 0`) the footnote-tree date cost of any money plan `m` is the cash-in-advance present-value
cost `E[Λ_tc_t]`. -/
theorem dateCost_eq_pvCost (Λ c m : ℕ → Ω → ℝ) (k : ℕ) :
    MoneyInUtility.FootnoteTree.dateCost T Λ (fun _ _ => 0) c m k =
      CashInAdvance.TreeEuler.pvCost T Λ c k := by
  simp only [MoneyInUtility.FootnoteTree.dateCost, CashInAdvance.TreeEuler.pvCost, zero_mul,
    add_zero]

/-- Cochrane (2023), §19.5.1, p. 448, and footnote 1, p. 440: with utility independent of
money the footnote-tree date utility of any money plan `m` is the cash-in-advance date term
`βᵗE u(c_t)`. -/
theorem dateUtil_eq (β : ℝ) (u : ℝ → ℝ) (c m : ℕ → Ω → ℝ) (k : ℕ) :
    MoneyInUtility.FootnoteTree.dateUtil T β (fun x _ => u x) c m k =
      β ^ k * ∑ ω, T.prob ω * u (c k ω) := by
  simp only [MoneyInUtility.FootnoteTree.dateUtil]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- Cochrane (2023), §19.5.1, pp. 448–449, and footnote 1, p. 440: the CIA tree plan `c` is
admissible iff, with any adapted money plan `m` at zero cost, `(c, m)` is feasible in the
footnote-tree problem and its utility converges. -/
theorem admissible_iff_tFeasible {β W : ℝ} {u : ℝ → ℝ} {Λ c m : ℕ → Ω → ℝ}
    (hm : MoneyInUtility.FootnoteTree.TAdapted T m) :
    CashInAdvance.TreeEuler.Admissible T β u Λ W c ↔
      MoneyInUtility.FootnoteTree.TFeasible T Λ (fun _ _ => 0) W c m ∧
        Summable (MoneyInUtility.FootnoteTree.dateUtil T β (fun x _ => u x) c m) := by
  have e1 : MoneyInUtility.FootnoteTree.dateCost T Λ (fun _ _ => 0) c m =
      CashInAdvance.TreeEuler.pvCost T Λ c := funext (dateCost_eq_pvCost T Λ c m)
  have e2 : MoneyInUtility.FootnoteTree.dateUtil T β (fun x _ => u x) c m =
      fun k => β ^ k * ∑ ω, T.prob ω * u (c k ω) := funext (dateUtil_eq T β u c m)
  simp only [CashInAdvance.TreeEuler.Admissible, MoneyInUtility.FootnoteTree.TFeasible, e1, e2,
    Links.meas_iff_tAdapted]
  tauto

/-- Cochrane (2023), §19.5.1, p. 449, and footnote 1, p. 440, **the tree bridge**: on a finite
event tree the cash-in-advance household problem with `V = 1` (`TreeEuler.IsOptimal`) is the
footnote-1 time-0 problem (`FootnoteTree.TOptimal`) with utility independent of money and a zero
cost of money (`ι = 0`), for any adapted money plan `m`; the optimality notions coincide. -/
theorem isOptimal_iff_tOptimal_of_adapted {β W : ℝ} {u : ℝ → ℝ} {Λ c m : ℕ → Ω → ℝ}
    (hm : MoneyInUtility.FootnoteTree.TAdapted T m) :
    CashInAdvance.TreeEuler.IsOptimal T β u Λ W c ↔
      MoneyInUtility.FootnoteTree.TOptimal T β (fun x _ => u x) Λ (fun _ _ => 0) W c m := by
  have hz : MoneyInUtility.FootnoteTree.TAdapted T (fun _ _ => (0 : ℝ)) := fun _ _ _ _ => rfl
  have eU : ∀ c' m' : ℕ → Ω → ℝ, ∑' k, MoneyInUtility.FootnoteTree.dateUtil T β
      (fun x _ => u x) c' m' k = CashInAdvance.TreeEuler.expU T β u c' := fun c' m' => by
    simp only [dateUtil_eq, CashInAdvance.TreeEuler.expU]
  constructor
  · rintro ⟨hadm, hmax⟩
    obtain ⟨hf, hs⟩ := (admissible_iff_tFeasible T hm).mp hadm
    refine ⟨hf, hs, fun c' m' hf' hs' => ?_⟩
    rw [eU, eU]
    exact hmax c' ((admissible_iff_tFeasible T hf'.2.1).mpr ⟨hf', hs'⟩)
  · rintro ⟨hf, hs, hmax⟩
    refine ⟨(admissible_iff_tFeasible T hm).mpr ⟨hf, hs⟩, fun c' hc' => ?_⟩
    obtain ⟨hf', hs'⟩ := (admissible_iff_tFeasible T hz).mp hc'
    have := hmax c' _ hf' hs'
    rwa [eU, eU] at this

/-- Cochrane (2023), §19.5.1, p. 449, and footnote 1, p. 440: the tree bridge with no money
(`m = 0`, `ι = 0`), the tree analogue of `CashInAdvance.Euler.isOptimalPlan_iff_optimal`. -/
theorem isOptimal_iff_tOptimal {β W : ℝ} {u : ℝ → ℝ} {Λ c : ℕ → Ω → ℝ} :
    CashInAdvance.TreeEuler.IsOptimal T β u Λ W c ↔
      MoneyInUtility.FootnoteTree.TOptimal T β (fun x _ => u x) Λ (fun _ _ => 0) W c
        (fun _ _ => 0) :=
  isOptimal_iff_tOptimal_of_adapted T fun _ _ _ _ => rfl

/-- Cochrane (2023), (19.31), p. 450, **Fact 1 under uncertainty, necessity, from footnote 1**:
the cash-in-advance tree Euler equation `β^t u'(c_t(ω₀)) Λ_s(ω₁) = β^s u'(c_s(ω₁)) Λ_t(ω₀)`
derived through the tree bridge from the footnote-tree perturbation lemma
`MoneyInUtility.FootnoteTree.tperturb_le`. Differentiability is needed only at the two nodes,
and, unlike `CashInAdvance.TreeEuler.euler_necessary`, no positivity of the state prices. -/
theorem tree_euler_necessary_general {β W : ℝ} {u : ℝ → ℝ} {Λ c : ℕ → Ω → ℝ}
    (hopt : CashInAdvance.TreeEuler.IsOptimal T β u Λ W c)
    (hΛm : CashInAdvance.TreeEuler.Meas T Λ) {t s : ℕ} (hts : t ≠ s) (ω0 ω1 : Ω) {d1 d2 : ℝ}
    (h1 : HasDerivAt u d1 (c t ω0)) (h2 : HasDerivAt u d2 (c s ω1)) :
    β ^ t * d1 * Λ s ω1 = β ^ s * d2 * Λ t ω0 := by
  have hopt' := (isOptimal_iff_tOptimal T).mp hopt
  have hca : MoneyInUtility.FootnoteTree.TAdapted T c := hopt'.1.1
  have hq : MoneyInUtility.FootnoteTree.TAdapted T Λ := (Links.meas_iff_tAdapted T Λ).mp hΛm
  have hz : MoneyInUtility.FootnoteTree.TAdapted T (fun _ _ => (0 : ℝ)) := fun _ _ _ _ => rfl
  set Mt := T.mass t ω0 with hMt
  set Ms := T.mass s ω1 with hMs
  have hMt0 : 0 < Mt := T.mass_pos t ω0
  have hMs0 : 0 < Ms := T.mass_pos s ω1
  set A := Λ s ω1 * Ms with hA
  set B := Λ t ω0 * Mt with hB
  set D : ℝ → ℝ := fun ε => Mt * (β ^ t * u (c t ω0 + ε * A)) +
    Ms * (β ^ s * u (c s ω1 + -(ε * B))) with hD
  have hle : ∀ ε, D ε ≤ D 0 := by
    intro ε
    have hut := MoneyInUtility.FootnoteTree.sum_perturb_cell T (fun _ z => β ^ t * u z) (c t)
      (fun ω h => hca t ω0 ω h) (fun _ _ => rfl) (ε * A)
    have hus := MoneyInUtility.FootnoteTree.sum_perturb_cell T (fun _ z => β ^ s * u z) (c s)
      (fun ω h => hca s ω1 ω h) (fun _ _ => rfl) (-(ε * B))
    have hkt := MoneyInUtility.FootnoteTree.sum_perturb_cell T (fun ω z => Λ t ω * z) (c t)
      (fun ω h => hca t ω0 ω h) (fun ω h => by funext z; rw [hq t ω0 ω h]) (ε * A)
    have hks := MoneyInUtility.FootnoteTree.sum_perturb_cell T (fun ω z => Λ s ω * z) (c s)
      (fun ω h => hca s ω1 ω h) (fun ω h => by funext z; rw [hq s ω1 ω h]) (-(ε * B))
    have h := MoneyInUtility.FootnoteTree.tperturb_le T hopt' hts
      (MoneyInUtility.FootnoteTree.perturb_adapted T hca t s ω0 ω1 (ε * A) (-(ε * B)))
      hz (fun k hkt hks => by funext ω; simp [hkt, hks]) (fun _ _ _ => rfl) (by
        simp only [MoneyInUtility.FootnoteTree.dateCost, hts, Ne.symm hts, ↓reduceIte,
          add_zero, mul_zero]
        rw [← hMt] at hkt
        rw [← hMs] at hks
        rw [hkt, hks]
        simp only [hA, hB]
        ring)
    simp only [MoneyInUtility.FootnoteTree.dateUtil, hts, Ne.symm hts, ↓reduceIte,
      add_zero] at h
    rw [← hMt] at hut
    rw [← hMs] at hus
    rw [hut, hus] at h
    simp only [hD, zero_mul, add_zero, neg_zero]
    linarith
  have hd1 : HasDerivAt (fun ε => c t ω0 + ε * A) A 0 := by
    simpa using (hasDerivAt_mul_const A).const_add (c t ω0)
  have hd2 : HasDerivAt (fun ε => c s ω1 + -(ε * B)) (-B) 0 := by
    simpa using ((hasDerivAt_mul_const B).neg).const_add (c s ω1)
  have hu1 : HasDerivAt (fun ε => u (c t ω0 + ε * A)) (d1 * A) 0 :=
    HasDerivAt.comp_of_eq 0 h1 hd1 (by simp)
  have hu2 : HasDerivAt (fun ε => u (c s ω1 + -(ε * B))) (d2 * -B) 0 :=
    HasDerivAt.comp_of_eq 0 h2 hd2 (by simp)
  have hDd : HasDerivAt D (Mt * (β ^ t * (d1 * A)) + Ms * (β ^ s * (d2 * -B))) 0 :=
    ((hu1.const_mul _).const_mul _).add ((hu2.const_mul _).const_mul _)
  have hmax : IsLocalMax D 0 := Filter.Eventually.of_forall hle
  have h0 := hmax.hasDerivAt_eq_zero hDd
  have hfac : Mt * Ms * (β ^ t * d1 * Λ s ω1 - β ^ s * d2 * Λ t ω0) = 0 := by
    rw [← h0, hA, hB]
    ring
  have := (mul_eq_zero.mp hfac).resolve_left (mul_pos hMt0 hMs0).ne'
  linarith

/-- Cochrane (2023), eq. (19.13), p. 440, under uncertainty, for the money-free footnote-tree
problem (`ι = 0`, `m = 0`, utility independent of money), **from the cash-in-advance Euler
equation**: `MoneyInUtility.FootnoteTree.tree_foc_cc` in this case follows from
`CashInAdvance.TreeEuler.euler_necessary` through the tree bridge (positive state prices). -/
theorem tree_foc_cc_of_cia_euler {β W : ℝ} {u uc : ℝ → ℝ} {Λ c : ℕ → Ω → ℝ}
    (hopt : MoneyInUtility.FootnoteTree.TOptimal T β (fun x _ => u x) Λ (fun _ _ => 0) W c
      (fun _ _ => 0))
    (hq : MoneyInUtility.FootnoteTree.TAdapted T Λ) (hΛ : ∀ t ω, 0 < Λ t ω)
    (huc : ∀ k ω, HasDerivAt u (uc (c k ω)) (c k ω)) {t s : ℕ} (hts : t ≠ s) (ω0 ω1 : Ω) :
    β ^ t * uc (c t ω0) * Λ s ω1 = β ^ s * uc (c s ω1) * Λ t ω0 :=
  CashInAdvance.TreeEuler.euler_necessary T ((isOptimal_iff_tOptimal T).mpr hopt)
    ((Links.meas_iff_tAdapted T Λ).mpr hq) hΛ hts ω0 ω1 (huc t ω0) (huc s ω1)

/-- Cochrane (2023), eqs. (19.13)–(19.14) and footnote 1, p. 440, sufficiency on the tree, for
the money-free problem (`ι = 0`, `m = 0`), **from the cash-in-advance sufficiency theorem**:
the conclusion of `MoneyInUtility.FootnoteTree.tree_optimal_of_foc` in this case follows from
`CashInAdvance.TreeEuler.euler_sufficient` through the tree bridge. -/
theorem tree_optimal_of_foc_of_cia {β W lam : ℝ} {u uc : ℝ → ℝ} {Λ c : ℕ → Ω → ℝ}
    (hβ : 0 ≤ β) (hlam : 0 ≤ lam) (hsup : ∀ k ω x, u x ≤ u (c k ω) + uc (c k ω) * (x - c k ω))
    (hfoc : ∀ k ω, β ^ k * uc (c k ω) = lam * Λ k ω)
    (hfeas : MoneyInUtility.FootnoteTree.TFeasible T Λ (fun _ _ => 0) W c (fun _ _ => 0))
    (hbind : ∑' k, MoneyInUtility.FootnoteTree.dateCost T Λ (fun _ _ => 0) c (fun _ _ => 0) k =
      W)
    (hus : Summable (MoneyInUtility.FootnoteTree.dateUtil T β (fun x _ => u x) c
      (fun _ _ => 0))) :
    MoneyInUtility.FootnoteTree.TOptimal T β (fun x _ => u x) Λ (fun _ _ => 0) W c
      (fun _ _ => 0) := by
  have hadm := (admissible_iff_tFeasible T (fun _ _ _ _ => rfl)).mpr ⟨hfeas, hus⟩
  have hb : ∑' τ, CashInAdvance.TreeEuler.pvCost T Λ c τ = W := by
    rw [← hbind]
    exact tsum_congr fun k => (dateCost_eq_pvCost T Λ c _ k).symm
  exact (isOptimal_iff_tOptimal T).mp (CashInAdvance.TreeEuler.euler_sufficient T
    (du := fun k ω => uc (c k ω)) hβ hlam hsup hfoc hadm hb)

/-- Cochrane (2023), §19.5.1, p. 448 (a general lemma on finite trees, the law of iterated
expectations from date `t` to date `0`'s unconditional mean): `E[E_t h] = E[h]`, i.e.
`∑_ω pr(ω) E_t h(ω) = ∑_ω pr(ω) h(ω)`. -/
theorem sum_prob_condE (t : ℕ) (h : Ω → ℝ) :
    ∑ ω, T.prob ω * T.condE t h ω = ∑ ω, T.prob ω * h ω := by
  classical
  have key : ∀ ω, T.prob ω * T.condE t h ω = ∑ ω', if T.info t ω' ω then
      T.prob ω * T.prob ω' * h ω' / T.mass t ω' else 0 := by
    intro ω
    unfold FiniteTree.condE FiniteTree.num
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    split_ifs with hh
    · rw [T.mass_congr hh]
      ring
    · simp
  rw [Finset.sum_congr rfl fun ω _ => key ω, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  have hm : T.mass t ω' = ∑ ω, if T.info t ω' ω then T.prob ω else 0 := by
    unfold FiniteTree.mass
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hh : T.info t ω ω'
    · have h2 : T.info t ω' ω := (T.info t).symm hh
      simp only [hh, h2, ↓reduceIte]
    · have h2 : ¬ T.info t ω' ω := fun h' => hh ((T.info t).symm h')
      simp only [hh, h2, ↓reduceIte]
  have hpos := (T.mass_pos t ω').ne'
  calc (∑ ω, if T.info t ω' ω then T.prob ω * T.prob ω' * h ω' / T.mass t ω' else 0)
      = (∑ ω, if T.info t ω' ω then T.prob ω else 0) * (T.prob ω' * h ω' / T.mass t ω') := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ω _ => ?_
        split_ifs <;> ring
    _ = T.prob ω' * h ω' := by
        rw [← hm]
        field_simp

/-- Cochrane (2023), (19.30), p. 449: for a measurable plan only the date-`t` conditional mean
of the state-price density matters, `E[Λ_tc_t] = E[E_t(Λ_t)c_t]`. -/
theorem pvCost_condE {Λ c : ℕ → Ω → ℝ} (hc : CashInAdvance.TreeEuler.Meas T c) (τ : ℕ) :
    CashInAdvance.TreeEuler.pvCost T (fun k => T.toExpectationSystem.E k (Λ k)) c τ =
      CashInAdvance.TreeEuler.pvCost T Λ c τ := by
  have hk : T.toExpectationSystem.E τ (c τ) = c τ := by
    rw [FiniteTree.toExpectationSystem_E]
    funext ω
    exact T.condE_of_const_on_cell fun ω' h => hc τ ω' ω h
  have hpo := finiteTree_pullOut T τ (c τ) (Λ τ) hk
  rw [FiniteTree.toExpectationSystem_E, FiniteTree.toExpectationSystem_E] at hpo
  unfold CashInAdvance.TreeEuler.pvCost
  change ∑ ω, T.prob ω * (T.toExpectationSystem.E τ (Λ τ) ω * c τ ω) = _
  rw [FiniteTree.toExpectationSystem_E]
  have e : ∀ ω, T.prob ω * (T.condE τ (Λ τ) ω * c τ ω) =
      T.prob ω * T.condE τ (c τ * Λ τ) ω := fun ω => by
    rw [hpo]
    simp only [Pi.mul_apply]
    ring
  rw [Finset.sum_congr rfl fun ω _ => e ω, sum_prob_condE]
  exact Finset.sum_congr rfl fun ω _ => by simp only [Pi.mul_apply]; ring

/-- Cochrane (2023), (19.30), p. 449: the cash-in-advance tree problem is unchanged when the
state-price density `Λ_t` is replaced by its date-`t` conditional mean `E_tΛ_t`. -/
theorem isOptimal_condE_iff {β W : ℝ} {u : ℝ → ℝ} {Λ c : ℕ → Ω → ℝ} :
    CashInAdvance.TreeEuler.IsOptimal T β u (fun k => T.toExpectationSystem.E k (Λ k)) W c ↔
      CashInAdvance.TreeEuler.IsOptimal T β u Λ W c := by
  have hA : ∀ c', CashInAdvance.TreeEuler.Admissible T β u
      (fun k => T.toExpectationSystem.E k (Λ k)) W c' ↔
      CashInAdvance.TreeEuler.Admissible T β u Λ W c' := by
    intro c'
    constructor
    · rintro ⟨hm, hu, hs, hW⟩
      have e := funext (pvCost_condE T (Λ := Λ) hm)
      rw [e] at hs hW
      exact ⟨hm, hu, hs, hW⟩
    · rintro ⟨hm, hu, hs, hW⟩
      have e := funext (pvCost_condE T (Λ := Λ) hm)
      rw [← e] at hs hW
      exact ⟨hm, hu, hs, hW⟩
  simp only [CashInAdvance.TreeEuler.IsOptimal, hA]

/-- Cochrane (2023), p. 453 ("first order conditions and transversality conditions are
necessary and sufficient"), **sufficiency under uncertainty, from footnote 1**: the full
`CashInAdvance.TreeEuler.euler_sufficient` (node-indexed supergradients `du`, state prices not
assumed measurable) derived from `MoneyInUtility.FootnoteTree.tree_optimal_of_foc`. The
supergradients and state prices are averaged over each information cell (`E_t du_t`,
`E_tΛ_t`), which preserves the supergradient inequality and the first-order conditions; the
averaged supergradient is carried as the (costless, `ι = 0`) money plan `m = E_t du_t`, with
`u_c(c, m) = m`, `u_m = 0`; and averaging `Λ` does not change the problem
(`isOptimal_condE_iff`). -/
theorem euler_sufficient_of_tree_optimal_of_foc {β W lam : ℝ} {u : ℝ → ℝ} {Λ c du : ℕ → Ω → ℝ}
    (hβ : 0 ≤ β) (hlam : 0 ≤ lam) (hconc : ∀ τ ω x, u x ≤ u (c τ ω) + du τ ω * (x - c τ ω))
    (hfoc : ∀ τ ω, β ^ τ * du τ ω = lam * Λ τ ω)
    (hadm : CashInAdvance.TreeEuler.Admissible T β u Λ W c)
    (hbind : ∑' τ, CashInAdvance.TreeEuler.pvCost T Λ c τ = W) :
    CashInAdvance.TreeEuler.IsOptimal T β u Λ W c := by
  set E := T.toExpectationSystem with hE
  set Λ' : ℕ → Ω → ℝ := fun k => E.E k (Λ k) with hΛ'
  set du' : ℕ → Ω → ℝ := fun k => E.E k (du k) with hdu'
  have hcm := hadm.1
  have hdua : MoneyInUtility.FootnoteTree.TAdapted T du' := by
    intro k ω ω' h
    simp only [hdu', hE, FiniteTree.toExpectationSystem_E]
    exact T.condE_congr _ h
  -- the averaged supergradient inequality
  have hconc' : ∀ τ ω x, u x ≤ u (c τ ω) + du' τ ω * (x - c τ ω) := by
    intro τ ω x
    have hk1 : E.E τ (fun ω' => u (c τ ω')) = fun ω' => u (c τ ω') := by
      rw [hE, FiniteTree.toExpectationSystem_E]
      funext ω2
      exact T.condE_of_const_on_cell fun ω' h => by rw [hcm τ ω' ω2 h]
    have hk2 : E.E τ (fun ω' => x - c τ ω') = fun ω' => x - c τ ω' := by
      rw [hE, FiniteTree.toExpectationSystem_E]
      funext ω2
      exact T.condE_of_const_on_cell fun ω' h => by rw [hcm τ ω' ω2 h]
    have hg : (fun ω' => u (c τ ω') + du τ ω' * (x - c τ ω')) =
        (fun ω' => u (c τ ω')) + (fun ω' => x - c τ ω') * du τ := by
      funext ω'
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    have hEg : E.E τ (fun ω' => u (c τ ω') + du τ ω' * (x - c τ ω')) =
        (fun ω' => u (c τ ω')) + (fun ω' => x - c τ ω') * E.E τ (du τ) := by
      rw [hg, map_add, hk1, finiteTree_pullOut T τ _ _ hk2]
    have hmono := E.mono τ (show (fun _ => u x) ≤
        (fun ω' => u (c τ ω') + du τ ω' * (x - c τ ω')) from fun ω' => hconc τ ω' x)
    rw [E.const, hEg] at hmono
    have := hmono ω
    simp only [Pi.add_apply, Pi.mul_apply] at this
    simp only [hdu']
    linarith
  -- the averaged first-order conditions
  have hfoc' : ∀ τ ω, β ^ τ * du' τ ω = lam * Λ' τ ω := by
    intro τ ω
    have hf : (β ^ τ) • du τ = lam • Λ τ := funext fun ω' => by
      simp only [Pi.smul_apply, smul_eq_mul, hfoc]
    have := congrFun (congrArg (E.E τ) hf) ω
    simp only [map_smul, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have ecost : ∀ c' : ℕ → Ω → ℝ, CashInAdvance.TreeEuler.Meas T c' →
      CashInAdvance.TreeEuler.pvCost T Λ' c' = CashInAdvance.TreeEuler.pvCost T Λ c' :=
    fun c' hc' => funext (pvCost_condE T hc')
  have hadm' : CashInAdvance.TreeEuler.Admissible T β u Λ' W c := by
    obtain ⟨hm, hu, hs, hW⟩ := hadm
    rw [← ecost c hm] at hs hW
    exact ⟨hm, hu, hs, hW⟩
  obtain ⟨hfeas, hus⟩ := (admissible_iff_tFeasible T hdua).mp hadm'
  have hbind' : ∑' k, MoneyInUtility.FootnoteTree.dateCost T Λ' (fun _ _ => 0) c du' k = W := by
    rw [← hbind, ← ecost c hcm]
    exact tsum_congr fun k => dateCost_eq_pvCost T Λ' c du' k
  have hopt := MoneyInUtility.FootnoteTree.tree_optimal_of_foc T (u := fun x _ => u x)
    (uc := fun _ z => z) (um := fun _ _ => 0) hβ hlam
    (fun k ω x _ => by have := hconc' k ω x; simp only [zero_mul, add_zero]; exact this)
    (fun k ω => ⟨hfoc' k ω, by simp⟩) hfeas hbind' hus
  exact (isOptimal_condE_iff T).mp ((isOptimal_iff_tOptimal_of_adapted T hdua).mpr hopt)

end TreeBridge

namespace GaliMoneyRule

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Galí's money-rule block, restated from the Galí Chapter 3/4 projects -/

/-- Galí (2015), eq. (22), p. 63 (restated from the Galí Chapter 3 project): the New Keynesian
Phillips curve `π_t = βE_tπ_{t+1} + κỹ_t`; cited in Cochrane (2023), §19.1, p. 435, as the
sticky-price alternative to the monetarist models of Chapter 19. -/
def NKPC (β κ : ℝ) (infl ygap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eq. (32), p. 74 (restated from the Galí Chapter 3 project): the DIS with the
interest rate eliminated through money demand (31),
`(1+ση)ỹ_t = σηE_tỹ_{t+1} + l̂_t + ηE_tπ_{t+1} + ηr̂ⁿ_t − ŷⁿ_t` (`l̂_t = L (t + 1)`); the
money-demand block shared with Cochrane (2023), (19.4)–(19.5), p. 436. -/
def Eq32 (σ η : ℝ) (ygap infl L rn yn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (1 + σ * η) • ygap t = (σ * η) • 𝔼.E t (ygap (t + 1)) + L (t + 1) +
    η • 𝔼.E t (infl (t + 1)) + η • rn t - yn t

omit 𝔼 in
/-- Galí (2015), eq. (33), p. 74 (restated from the Galí Chapter 3 project): the real-balance
identity `l̂_{t−1} = l̂_t + π_t − Δm_t`; the money-growth rule of Cochrane (2023), p. 436. -/
def RealBalanceId (infl L dm : ℕ → Ω → ℝ) : Prop :=
  ∀ t, L t = L (t + 1) + infl t - dm t

/-- Galí (2015), p. 75 (restated from the Galí Chapter 3 project): real balances `l̂_{t−1}` are
predetermined, so `l̂_t` is known at `t`. -/
def Predetermined (L : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (L (t + 1)) = L (t + 1)

/-- Galí (2015), eq. (34), p. 75 (restated from the Galí Chapter 3 project): `A_{M,0}`. -/
def AM0 (σ η κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1 + σ * η, 0, 0; -κ, 1, 0; 0, -1, 1]

/-- Galí (2015), eq. (34), p. 75 (restated from the Galí Chapter 3 project): `A_{M,1}`. -/
def AM1 (σ η β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![σ * η, η, 1; 0, β, 0; 0, 0, 1]

/-- Galí (2015), eq. (34), p. 75 (restated from the Galí Chapter 3 project): `B_M`. -/
def BM (η : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![η, -1, 0; 0, 0, 0; 0, 0, -1]

omit 𝔼 in
/-- Galí (2015), eq. (34), p. 75 (restated from the Galí Chapter 3 project): the state
`x_t = (ỹ_t, π_t, l̂_{t−1})`. -/
def stateVec (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![ygap t ω, infl t ω, L t ω]

/-- Galí (2015), eq. (34), p. 75 (restated from the Galí Chapter 3 project): the forecast
`E_tx_{t+1}`. -/
def expVec (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![𝔼.E t (ygap (t + 1)) ω, 𝔼.E t (infl (t + 1)) ω, 𝔼.E t (L (t + 1)) ω]

omit 𝔼 in
/-- Galí (2015), eq. (34), p. 75 (restated from the Galí Chapter 3 project): the shocks
`(r̂ⁿ_t, ŷⁿ_t, Δm_t)`. -/
def shockVec (rn yn dm : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![rn t ω, yn t ω, dm t ω]

/-- Galí (2015), eq. (34), p. 75 (restated from the Galí Chapter 3 project): the money-rule
system `A_{M,0}x_t = A_{M,1}E_tx_{t+1} + B_Ms_t` in every state. -/
def System34 (σ η β κ : ℝ) (ygap infl L rn yn dm : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, (AM0 σ η κ).mulVec (stateVec ygap infl L t ω) =
    (AM1 σ η β).mulVec (expVec 𝔼 ygap infl L t ω) + (BM η).mulVec (shockVec rn yn dm t ω)

/-- Galí (2015), eq. (34), p. 75 (restated from the Galí Chapter 3 project): with `l̂`
predetermined, (34) is equivalent to (32), the NKPC (22) and the identity (33). -/
theorem system34_iff {σ η β κ : ℝ} {ygap infl L rn yn dm : ℕ → Ω → ℝ}
    (hL : Predetermined 𝔼 L) :
    System34 𝔼 σ η β κ ygap infl L rn yn dm ↔
      Eq32 𝔼 σ η ygap infl L rn yn ∧ NKPC 𝔼 β κ infl ygap ∧ RealBalanceId infl L dm := by
  constructor
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_,
      fun t => funext fun ω => ?_⟩
    · have h0 := congrFun (h t ω) 0
      have hLω := congrFun (hL t) ω
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h0 ⊢
      linarith
    · have h1 := congrFun (h t ω) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h1 ⊢
      linarith
    · have h2 := congrFun (h t ω) 2
      have hLω := congrFun (hL t) ω
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h2 ⊢
      linarith
  · rintro ⟨h32, h22, h33⟩ t ω
    have a := congrFun (h32 t) ω
    have b := congrFun (h22 t) ω
    have c := congrFun (h33 t) ω
    have hLω := congrFun (hL t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c
    funext j
    fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] <;> linarith

/-- Galí (2015), eq. (34), p. 75 (restated from the Galí Chapter 4 project,
`MoneyRuleDeterminacy.Equil34`): a bounded equilibrium of (34) with predetermined real balances
starting at `l̂_{−1} = L0`. Galí's determinacy theorem (`system34_existsUnique` there, p. 75 and
fn. 14) says that for `σ > 0`, `η ≥ 0`, `κ > 0`, `0 < β ≤ 1` and bounded adapted shocks exactly
one such equilibrium exists. -/
def Equil34 (σ η β κ L0 : ℝ) (rn yn dm ygap infl L : ℕ → Ω → ℝ) : Prop :=
  System34 𝔼 σ η β κ ygap infl L rn yn dm ∧ Predetermined 𝔼 L ∧ L 0 = (fun _ => L0) ∧
    𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ 𝔼.Adapted L ∧
    BoundedProc ygap ∧ BoundedProc infl ∧ BoundedProc L

/-! ### The flexible-price money block -/

/-- Cochrane (2023), (19.4)–(19.5), p. 436, in Galí's coordinates (Galí (2015), (32), p. 74,
with a zero output gap): `0 = l̂_t + ηE_tπ_{t+1} + ηr̂ⁿ_t − ŷⁿ_t`, i.e. money demand
`l̂_t − ŷⁿ_t = −η(r̂ⁿ_t + E_tπ_{t+1})` with the Fisher equation. -/
def FlexBlock (η : ℝ) (infl L rn yn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, L (t + 1) + η • 𝔼.E t (infl (t + 1)) + η • rn t - yn t = 0

/-- Cochrane (2023), §19.2, p. 436, and Galí (2015), (32)–(33), p. 74, with flexible prices
(`ỹ ≡ 0`): the money-demand block and the money-growth identity. -/
def FlexSystem (η : ℝ) (infl L rn yn dm : ℕ → Ω → ℝ) : Prop :=
  FlexBlock 𝔼 η infl L rn yn ∧ RealBalanceId infl L dm

/-- Cochrane (2023), §19.2, p. 436, with Galí's (2015) equilibrium notion, p. 75: a bounded
adapted flexible-price equilibrium with predetermined real balances starting at `l̂_{−1} = L0`
(Galí's `Equil34` with `ỹ ≡ 0` and the NKPC row dropped). -/
def FlexEquil (η L0 : ℝ) (rn yn dm infl L : ℕ → Ω → ℝ) : Prop :=
  FlexSystem 𝔼 η infl L rn yn dm ∧ Predetermined 𝔼 L ∧ L 0 = (fun _ => L0) ∧
    𝔼.Adapted infl ∧ 𝔼.Adapted L ∧ BoundedProc infl ∧ BoundedProc L

/-- Cochrane (2023), (19.5), p. 436, and Galí (2015), (32), p. 74: with a zero output gap,
Galí's (32) is the flexible-price money block for every `σ` (`σ` drops out). -/
theorem eq32_zero_gap_iff {σ η : ℝ} {infl L rn yn : ℕ → Ω → ℝ} :
    Eq32 𝔼 σ η (fun _ _ => 0) infl L rn yn ↔ FlexBlock 𝔼 η infl L rn yn := by
  have h0 : ∀ t, 𝔼.E t (fun _ => (0 : ℝ)) = fun _ => 0 := fun t => 𝔼.const t 0
  constructor
  · intro h t
    funext ω
    have a := congrFun (h t) ω
    rw [h0] at a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_zero] at a ⊢
    simp only [Pi.zero_apply]
    linarith
  · intro h t
    funext ω
    have a := congrFun (h t) ω
    rw [h0]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_zero,
      Pi.zero_apply] at a ⊢
    linarith

/-- Galí (2015), (34), p. 75, versus Cochrane (2023), §19.2, p. 436: with real balances
predetermined, the zero-output-gap solutions of Galí's sticky-price money-rule system (34) are
exactly the flexible-price (Cagan) solutions that also satisfy the zero-gap Phillips curve
`π_t = βE_tπ_{t+1}`. -/
theorem system34_zero_gap_iff {σ η β κ : ℝ} {infl L rn yn dm : ℕ → Ω → ℝ}
    (hL : Predetermined 𝔼 L) :
    System34 𝔼 σ η β κ (fun _ _ => 0) infl L rn yn dm ↔
      FlexSystem 𝔼 η infl L rn yn dm ∧ ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) := by
  rw [system34_iff 𝔼 hL, eq32_zero_gap_iff]
  have hN : NKPC 𝔼 β κ infl (fun _ _ => 0) ↔ ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) := by
    unfold NKPC
    have e : κ • (fun _ : Ω => (0 : ℝ)) = 0 := smul_zero κ
    simp only [e, add_zero]
  rw [hN]
  unfold FlexSystem
  tauto

/-- Galí (2015), eq. (34), p. 75 (`Equil34`), versus Cochrane (2023), §19.2, p. 436: a bounded
equilibrium of Galí's system with a zero output gap is exactly a flexible-price equilibrium
that also satisfies `π_t = βE_tπ_{t+1}`. -/
theorem equil34_zero_gap_iff {σ η β κ L0 : ℝ} {rn yn dm infl L : ℕ → Ω → ℝ} :
    Equil34 𝔼 σ η β κ L0 rn yn dm (fun _ _ => 0) infl L ↔
      FlexEquil 𝔼 η L0 rn yn dm infl L ∧ ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) := by
  have hz : 𝔼.Adapted (fun _ _ => (0 : ℝ)) := fun t => 𝔼.const t 0
  have hzb : BoundedProc (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) := ⟨0, fun _ _ => by simp⟩
  constructor
  · rintro ⟨hs, hp, h0, -, ha1, ha2, -, hb1, hb2⟩
    obtain ⟨hf, hn⟩ := (system34_zero_gap_iff 𝔼 hp).mp hs
    exact ⟨⟨hf, hp, h0, ha1, ha2, hb1, hb2⟩, hn⟩
  · rintro ⟨⟨hf, hp, h0, ha1, ha2, hb1, hb2⟩, hn⟩
    exact ⟨(system34_zero_gap_iff 𝔼 hp).mpr ⟨hf, hn⟩, hp, h0, hz, ha1, ha2, hzb, hb1, hb2⟩

/-- Cochrane (2023), (19.5), p. 436: the forcing of the flexible-price real-balance equation,
`ŷⁿ_t − ηr̂ⁿ_t − ηE_tΔm_{t+1}`. -/
noncomputable def flexForcing (η : ℝ) (rn yn dm : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => yn t - η • rn t - η • 𝔼.E t (dm (t + 1))

/-- Cochrane (2023), (19.5) and (19.8), p. 437, in Galí's coordinates: along a flexible-price
solution with predetermined real balances, `l̂_t = L (t + 1)` solves the forward equation
`(1 + η)l̂_t = ηE_tl̂_{t+1} + ŷⁿ_t − ηr̂ⁿ_t − ηE_tΔm_{t+1}`. -/
theorem flex_scalar {η : ℝ} {infl L rn yn dm : ℕ → Ω → ℝ}
    (h : FlexSystem 𝔼 η infl L rn yn dm) (hL : Predetermined 𝔼 L) :
    ForwardSolution.ScalarEq 𝔼 (1 + η) η (flexForcing 𝔼 η rn yn dm) (fun t => L (t + 1)) := by
  intro t
  have hi : infl (t + 1) = L (t + 1) - L (t + 1 + 1) + dm (t + 1) := by
    funext ω
    have := congrFun (h.2 (t + 1)) ω
    simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
    linarith
  have hE : 𝔼.E t (infl (t + 1)) = L (t + 1) - 𝔼.E t (L (t + 1 + 1)) + 𝔼.E t (dm (t + 1)) := by
    rw [hi, map_add, map_sub, hL t]
  funext ω
  have a := congrFun (h.1 t) ω
  have b := congrFun hE ω
  simp only [flexForcing, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] at a b ⊢
  rw [b] at a
  linarith

omit 𝔼 in
/-- Galí (2015), p. 75: the real-balance path with initial condition `l̂_{−1} = L0` and
`l̂_t = ℓ_t` for `t ≥ 0`. -/
def shiftIn (L0 : ℝ) (ℓ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => L0
  | t + 1 => ℓ t

/-- Cochrane (2023), §19.2, pp. 436–437, under Galí's (2015) equilibrium notion, p. 75 and
fn. 14: **determinacy of the flexible-price money-growth model**. For `η ≥ 0`, bounded adapted
shocks `r̂ⁿ, ŷⁿ, Δm` (money GROWTH bounded; the money stock need not be) and any `l̂_{−1}`, there
is exactly one bounded adapted equilibrium `(π, l̂)` with predetermined real balances, for every
`ExpectationSystem`. This is the flexible-price (`ỹ ≡ 0`) counterpart of Galí's
`system34_existsUnique`. -/
theorem flex_existsUnique {η : ℝ} (hη : 0 ≤ η) {rn yn dm : ℕ → Ω → ℝ}
    (hrnb : BoundedProc rn) (hynb : BoundedProc yn) (hdmb : BoundedProc dm)
    (hrna : 𝔼.Adapted rn) (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm) (L0 : ℝ) :
    ∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), FlexEquil 𝔼 η L0 rn yn dm v.1 v.2 := by
  obtain ⟨Kr, hKr⟩ := hrnb
  obtain ⟨Ky, hKy⟩ := hynb
  obtain ⟨Kd, hKd⟩ := hdmb
  set f := flexForcing 𝔼 η rn yn dm with hf
  have hfb : ∀ t ω, |f t ω| ≤ Ky + η * Kr + η * Kd := by
    intro t ω
    simp only [hf, flexForcing, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have e2 : |η * rn t ω| ≤ η * Kr := by
      rw [abs_mul, abs_of_nonneg hη]; exact mul_le_mul_of_nonneg_left (hKr t ω) hη
    have e3 : |η * 𝔼.E t (dm (t + 1)) ω| ≤ η * Kd := by
      rw [abs_mul, abs_of_nonneg hη]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hKd (t + 1)) t ω) hη
    obtain ⟨a1, a2⟩ := abs_le.mp (hKy t ω)
    obtain ⟨b1, b2⟩ := abs_le.mp e2
    obtain ⟨c1, c2⟩ := abs_le.mp e3
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hfa : 𝔼.Adapted f := by
    intro t
    simp only [hf, flexForcing, map_sub, map_smul, hyna t, hrna t, 𝔼.E_E_self]
  have hAB : |η| < |1 + η| := by
    rw [abs_of_nonneg hη, abs_of_nonneg (by linarith)]; linarith
  obtain ⟨hsol, hbd, had, huniq⟩ := ForwardSolution.scalar_existsUnique 𝔼 hAB hfb hfa
  set ℓ := ForwardSolution.scalarSol 𝔼 (1 + η) η f with hℓ
  set L := shiftIn L0 ℓ with hLdef
  set infl : ℕ → Ω → ℝ := fun t => dm t + L t - L (t + 1) with hinfl
  have hLs : ∀ t, L (t + 1) = ℓ t := fun _ => rfl
  have hLa : 𝔼.Adapted L := by
    intro t
    cases t with
    | zero => exact 𝔼.const 0 L0
    | succ k => exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ k) (had k)
  obtain ⟨M, hM⟩ := hbd
  have hLb : ∀ t ω, |L t ω| ≤ max |L0| M := by
    intro t ω
    cases t with
    | zero => exact le_max_left _ _
    | succ k => exact (hM k ω).trans (le_max_right _ _)
  refine ⟨(infl, L), ⟨⟨fun t => ?_, fun t => ?_⟩, fun t => had t, rfl, fun t => ?_, hLa,
    ⟨Kd + 2 * max |L0| M, fun t ω => ?_⟩, ⟨max |L0| M, hLb⟩⟩, ?_⟩
  · have hi : 𝔼.E t (infl (t + 1)) = ℓ t - 𝔼.E t (ℓ (t + 1)) + 𝔼.E t (dm (t + 1)) := by
      have e : infl (t + 1) = dm (t + 1) + ℓ t - ℓ (t + 1) := rfl
      rw [e, map_sub, map_add, had t]
      abel
    funext ω
    have a := congrFun (hsol t) ω
    have b := congrFun hi ω
    simp only [hf, flexForcing, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at a b ⊢
    rw [hLs, b]
    linarith
  · funext ω
    simp only [hinfl, Pi.add_apply, Pi.sub_apply]
    ring
  · change 𝔼.E t (dm t + L t - L (t + 1)) = dm t + L t - L (t + 1)
    rw [map_sub, map_add, hdma t, hLa t, hLs, had t]
  · simp only [hinfl, Pi.add_apply, Pi.sub_apply]
    obtain ⟨a1, a2⟩ := abs_le.mp (hKd t ω)
    obtain ⟨b1, b2⟩ := abs_le.mp (hLb t ω)
    obtain ⟨c1, c2⟩ := abs_le.mp (hLb (t + 1) ω)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rintro ⟨infl', L'⟩ ⟨hsys, hpred, hL0, -, -, -, ⟨M', hM'⟩⟩
    have hs' := flex_scalar 𝔼 hsys hpred
    have hb' : BoundedProc (fun t => L' (t + 1)) := ⟨M', fun t ω => hM' (t + 1) ω⟩
    have hℓ' := huniq _ hs' hb'
    have hLL : L' = L := funext fun t => by
      cases t with
      | zero => exact hL0
      | succ k => exact congrFun hℓ' k
    have hii : infl' = infl := funext fun t => by
      funext ω
      have := congrFun (hsys.2 t) ω
      rw [hLL] at this
      simp only [hinfl, Pi.add_apply, Pi.sub_apply] at this ⊢
      linarith
    simp only [Prod.mk.injEq]
    exact ⟨hii, hLL⟩

/-! ### The flexible-price block is Cochrane's Cagan model; the selections compared -/

/-- Cochrane (2023), eq. (19.5), p. 436, and Galí (2015), (32), p. 74 (zero gap): in levels,
with `l̂_t = m_t − p_t`, `π_{t+1} = p_{t+1} − p_t`, constant natural rate `r` and output `y`, and
an adapted price level, Galí's flexible-price money block is exactly the Cagan equation
`m_t − p_t − y = −η(r + E_tp_{t+1} − p_t)` with semi-elasticity `a = η`. -/
theorem flexBlock_iff_cagan {η y r : ℝ} {m p infl L : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted p)
    (hL : ∀ t, L (t + 1) = m t - p t) (hπ : ∀ t, infl (t + 1) = p (t + 1) - p t) :
    FlexBlock 𝔼 η infl L (fun _ _ => r) (fun _ _ => y) ↔ CaganRE.Cagan 𝔼 η y r m p := by
  have hE : ∀ t, 𝔼.E t (infl (t + 1)) = 𝔼.E t (p (t + 1)) - p t := fun t => by
    rw [hπ, map_sub, hpa t]
  constructor
  · intro h t ω
    have a := congrFun (h t) ω
    rw [hE, hL] at a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a
    linarith
  · intro h t
    funext ω
    have a := h t ω
    rw [hE, hL]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linarith

/-- Cochrane (2023), eq. (19.6), p. 436, under Galí's (2015) equilibrium notion, p. 75: with
constant money (`Δm ≡ 0`), constant `r̂ⁿ = r`, `ŷⁿ = y` and `η ≥ 0`, the unique bounded
flexible-price equilibrium has constant real balances `l̂_t = y − ηr` from date 0 on, whatever
`l̂_{−1}` (the initial price level jumps to absorb `l̂_{−1}`). -/
theorem flex_constant_money {η r y L0 : ℝ} (hη : 0 ≤ η) {infl L : ℕ → Ω → ℝ}
    (h : FlexEquil 𝔼 η L0 (fun _ _ => r) (fun _ _ => y) (fun _ _ => 0) infl L) (t : ℕ) :
    L (t + 1) = fun _ => y - η * r := by
  have h0 : ∀ k, 𝔼.E k (fun _ => (0 : ℝ)) = fun _ => 0 := fun k => 𝔼.const k 0
  have hfc : flexForcing 𝔼 η (fun _ _ => r) (fun _ _ => y) (fun _ _ => 0) =
      fun _ _ => y - η * r := by
    funext k ω
    simp only [flexForcing, h0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_zero, sub_zero]
  have hAB : |η| < |1 + η| := by
    rw [abs_of_nonneg hη, abs_of_nonneg (by linarith)]; linarith
  have hfa : 𝔼.Adapted (fun (_ : ℕ) (_ : Ω) => y - η * r) := fun k => 𝔼.const k _
  obtain ⟨-, -, -, huniq⟩ := ForwardSolution.scalar_existsUnique 𝔼 hAB
    (f := fun _ _ => y - η * r) (K := |y - η * r|) (fun _ _ => le_refl _) hfa
  have hs' := flex_scalar 𝔼 h.1 h.2.1
  rw [hfc] at hs'
  obtain ⟨M, hM⟩ := h.2.2.2.2.2.2
  have h1 := huniq _ hs' ⟨M, fun k ω => hM (k + 1) ω⟩
  have hc : ForwardSolution.ScalarEq 𝔼 (1 + η) η (fun _ _ => y - η * r)
      (fun _ _ => y - η * r) := by
    intro k
    rw [𝔼.const]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h2 := huniq _ hc ⟨|y - η * r|, fun _ _ => le_refl _⟩
  exact congrFun (h1.trans h2.symm) t

/-- Cochrane (2023), eqs. (19.5)–(19.6), p. 436, versus Galí (2015), p. 75: with constant log
money `m̄` (and constant `r`, `y`, `η ≥ 0`), the price level `p_t = m̄ − l̂_t` of the unique
bounded flexible-price equilibrium of Galí's notion is Cochrane's steady state
`p̄ = m̄ − y + ηr` at every date `t ≥ 0`, and it solves the Cagan equation. -/
theorem flex_constant_money_steady {η r y L0 mbar : ℝ} (hη : 0 ≤ η) {infl L : ℕ → Ω → ℝ}
    (h : FlexEquil 𝔼 η L0 (fun _ _ => r) (fun _ _ => y) (fun _ _ => 0) infl L) :
    (fun t ω => mbar - L (t + 1) ω) = (fun _ _ => CaganRE.pbar η y r mbar) ∧
      CaganRE.Cagan 𝔼 η y r (fun _ _ => mbar) (fun _ _ => CaganRE.pbar η y r mbar) := by
  refine ⟨?_, fun t ω => ?_⟩
  · funext t ω
    rw [flex_constant_money 𝔼 hη h t, CaganRE.pbar]
    ring
  · have e := 𝔼.const t (CaganRE.pbar η y r mbar)
    change mbar - CaganRE.pbar η y r mbar - y =
      -η * (r + 𝔼.E t (fun _ => CaganRE.pbar η y r mbar) ω - CaganRE.pbar η y r mbar)
    rw [e, CaganRE.pbar]
    ring

/-- Cochrane (2023), pp. 436–437 (`CaganRE.bounded_iff_steady`) in Galí's (2015) terms, p. 75:
for `η > 0` and constant money `m̄`, a solution of the Cagan equation has bounded real balances
`m̄ − p_t` (Galí's equilibrium requirement) iff it is the steady state. Galí's determinacy
under a money rule is therefore Cochrane's selection of the bounded solution: every other member
of the Cagan family (`CaganRE.caganFamily`, explosive by `CaganRE.pf_explodes`) is excluded by
the boundedness requirement, not by any equilibrium condition. -/
theorem cagan_realBalances_bounded_iff {η y r mbar : ℝ} (hη : 0 < η) {p : ℕ → Ω → ℝ}
    (hp : CaganRE.Cagan 𝔼 η y r (fun _ _ => mbar) p) :
    BoundedProc (fun t ω => mbar - p t ω) ↔ p = fun _ _ => CaganRE.pbar η y r mbar := by
  rw [← CaganRE.bounded_iff_steady 𝔼 hη hp]
  obtain ⟨c1, c2⟩ := abs_le.mp (le_refl |mbar|)
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + |mbar|, fun t ω => ?_⟩
    obtain ⟨a1, a2⟩ := abs_le.mp (hM t ω)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rintro ⟨M, hM⟩
    refine ⟨M + |mbar|, fun t ω => ?_⟩
    obtain ⟨a1, a2⟩ := abs_le.mp (hM t ω)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Galí (2015), (34), p. 75, versus Cochrane (2023), §19.2, p. 436 (the link is not exact):
with sticky prices the flexible-price equilibrium is in general NOT an equilibrium of (34) with
a zero gap. Under perfect foresight, with `Δm ≡ 1`, `r̂ⁿ = ŷⁿ = 0` and `l̂_{−1} = −η`, the path
`π ≡ 1`, `l̂ ≡ −η` is a bounded flexible-price equilibrium for every `η`, but violates the
zero-gap Phillips curve `π_t = βE_tπ_{t+1}` unless `β = 1`. -/
theorem flex_not_zero_gap_eq34 {σ η β κ : ℝ} (hβ : β ≠ 1) :
    FlexEquil perfectForesight η (-η) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1)
        (fun _ _ => 1) (fun _ _ => -η) ∧
      ¬ System34 perfectForesight σ η β κ (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => -η)
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1) := by
  have hpred : Predetermined perfectForesight (fun (_ : ℕ) (_ : Unit) => -η) := fun _ => rfl
  refine ⟨⟨⟨fun t => ?_, fun t => ?_⟩, hpred, rfl, fun _ => rfl, fun _ => rfl,
    ⟨1, fun _ _ => by simp⟩, ⟨|η|, fun _ _ => by simp⟩⟩, fun h => ?_⟩
  · funext u
    change -η + η * 1 + η * 0 - 0 = 0
    ring
  · funext u
    change -η = -η + 1 - 1
    ring
  · have := congrFun (((system34_zero_gap_iff perfectForesight hpred).mp h).2 0) ()
    change (1 : ℝ) = β * 1 at this
    exact hβ (by linarith)

end GaliMoneyRule

end Cochrane.Monetarism.LinksTidy
