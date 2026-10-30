/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.TidyR6MoneyHouseholdEqm
import ObservationalEquivalence.Links

/-!
# The money-model household on finite event trees and under perfect foresight

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, pp. 495–496 (the
money model, OE-2), with the frictionless model (22.2), p. 495, and Chapter 19, §19.1,
pp. 434–435.

`TidyR6MoneyHousehold` and `TidyR6MoneyHouseholdEqm` derive the money model from optimisation on
any probability space. Here the derivation is specialised to every finite event tree
(`ExpectationsFiniteTree.FiniteTree`, made a probability space by
`ExpectationsMeasure.TreeBridge.treeSystem`): every state has positive probability, so the almost
sure statements hold at every node, adaptedness is the core `ExpectationSystem.Adapted`, expected
utility is the finite-state sum `∑ₜβᵗ∑_ωp(ω)c_t(ω)`, and the conditions are those of the core
model `TidyR5MoneyUncertainty.Eqm` in the tree's own expectation system.

## Main results

* Tools: `ae_iff_forall`, `aeEq_iff`, `E_tree`, `adapted_iff`, `pvM_tree`, `expU_tree`,
  `flow_tree_iff`, `constr_tree_iff`, `integ_tree`, `eqmM_tree_iff`.
* `tree_derived_iff`: on every finite tree, with positive debt, derived equilibria are exactly the
  node-by-node imposed equations; `tree_derived_iff_eqm`: when money is costly to hold they are
  exactly the Fisher equation plus `TidyR5MoneyUncertainty.Eqm` for the tree's expectation
  system.
* Perfect foresight (the one-state tree `unitTree`, restated from the NewKeynesianSelection
  project): `pf_derived_iff` — derived equilibria are exactly `Q_t = βP_t/P_{t+1}` plus
  `MoneyRegimes.Eqm`; `pf_derived_linear` — their observable path satisfies the Fisher equation
  and the flow condition (22.2) of the frictionless linear model
  (`StarredModel.Consistent`, through `Links.moneyOutcome`), and the household's bond yield
  `log(1/Q_t)` is exactly `−log β` plus the model's interest rate `i_t = log P_{t+1} − log P_t`.
* `coinTree_derived_eqm`: on the coin-flip tree, a derived equilibrium that is a
  `TidyR5MoneyUncertainty.Eqm` of `coinSystem` and whose date-1 inverse price level is not known
  at date 0.
-/

namespace Cochrane.ObservationalEquivalence.TidyR6MoneyHouseholdTree

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationsMeasure
open Cochrane.ObservationalEquivalence.ExpectationsMeasure.TreeBridge
open Cochrane.ObservationalEquivalence.ExpectationsFiniteTree
open Cochrane.ObservationalEquivalence.TidyR6MoneyHousehold
open Cochrane.ObservationalEquivalence.TidyR6MoneyHouseholdEqm

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  (T : FiniteTree Ω)

/-! ### A finite tree as a probability space -/

/-- Cochrane (2023), §22.1, p. 496 (finite trees): every node has positive probability, so an
almost sure statement holds at every node. -/
theorem ae_iff_forall {p : Ω → Prop} : (∀ᵐ ω ∂(treeSystem T).μ, p ω) ↔ ∀ ω, p ω := by
  refine ⟨fun h ω => ?_, fun h => Eventually.of_forall h⟩
  by_contra hn
  have h0 : (treeSystem T).μ {ω | ¬ p ω} = 0 := ae_iff.1 h
  exact treeSystem_fullSupport T ω (measure_mono_null (fun ω' hω' => by
    rw [Set.mem_singleton_iff.1 hω']; exact hn) h0)

/-- Cochrane (2023), §22.1, p. 496 (finite trees): almost sure equality is equality. -/
theorem aeEq_iff {f g : Ω → ℝ} : f =ᵐ[(treeSystem T).μ] g ↔ f = g :=
  ⟨(treeSystem T).eq_of_ae_eq (treeSystem_fullSupport T), fun h => h ▸ EventuallyEq.rfl⟩

/-- Cochrane (2023), §22.1, p. 496 (finite trees): the measure-theoretic `E_t` is the tree's
cell average, the core expectation. -/
theorem E_tree (t : ℕ) (x : Ω → ℝ) : (treeSystem T).E t x = T.toExpectationSystem.E t x := by
  rw [treeSystem_E, FiniteTree.toExpectationSystem_E]

/-- Cochrane (2023), §22.1, p. 496 (finite trees): a process is adapted to the tree's filtration
iff it is adapted in the core sense, `E_tx_t = x_t`. -/
theorem adapted_iff {x : ℕ → Ω → ℝ} :
    StronglyAdapted (treeSystem T).𝓕 x ↔ T.toExpectationSystem.Adapted x := by
  constructor
  · intro hx t
    rw [← E_tree]
    exact (treeSystem T).E_of_stronglyMeasurable (hx t) Integrable.of_finite
  · intro hx t
    rw [← hx t, ← E_tree]
    exact (treeSystem T).stronglyMeasurable_E t _

/-- Cochrane (2023), §22.1, p. 496 (finite trees): the measure-theoretic present value is the
core present value `TidyR5MoneyUncertainty.pvE` of the tree's expectation system. -/
theorem pvM_tree (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    TidyR5MoneyMeasure.pvM (treeSystem T) β s t =
      TidyR5MoneyUncertainty.pvE T.toExpectationSystem β s t := by
  simp only [TidyR5MoneyMeasure.pvM, MeasExpectationSystem.forwardSol,
    TidyR5MoneyUncertainty.pvE]
  rw [E_tree]
  rfl

/-- Cochrane (2023), §2.1, p. 21 (finite trees): expected discounted utility is the finite-state
sum `∑ₜβᵗ∑_ωp(ω)c_t(ω)`. -/
theorem expU_tree (β : ℝ) (c : ℕ → Ω → ℝ) :
    expU (treeSystem T) β c = ∑' t, β ^ t * ∑ ω, T.prob ω * c t ω := by
  simp only [expU]
  refine tsum_congr fun t => ?_
  congr 1
  exact integral_treeProb T (c t)

/-- Cochrane (2023), eq. (3.9), p. 57 (finite trees): the flow constraint holds almost surely iff
it holds at every node. -/
theorem flow_tree_iff (e : Econ Ω) (p : Plan Ω) :
    Flow (treeSystem T) e p ↔ ∀ t ω, wealth e.W0 p.B p.M t ω + e.P t ω * e.y t ω =
      e.P t ω * p.c t ω + e.P t ω * e.τ t ω + e.Q t ω * p.B t ω + e.Qm t ω * p.M t ω :=
  forall_congr' fun _ => ae_iff_forall T

/-- Cochrane (2023), §19.5.1, p. 448 (finite trees): the no-borrowing and cash constraints hold
almost surely iff they hold at every node. -/
theorem constr_tree_iff (e : Econ Ω) (p : Plan Ω) :
    Constr (treeSystem T) e p ↔ ∀ t ω, 0 ≤ p.B t ω ∧ mmin e t ω ≤ p.M t ω :=
  forall_congr' fun _ => ae_iff_forall T

/-- Cochrane (2023), §19.3, p. 439 (finite trees): on a finite tree every plan has integrable
positions. -/
theorem integ_tree (e : Econ Ω) (p : Plan Ω) : Integ (treeSystem T) e p := fun _ =>
  ⟨Integrable.of_finite, Integrable.of_finite, Integrable.of_finite, Integrable.of_finite,
    Integrable.of_finite⟩

/-- Cochrane (2023), §22.1, pp. 495–496 (finite trees): the measure-theoretic money model
`TidyR5MoneyMeasure.EqmM` of the tree is the core money model `TidyR5MoneyUncertainty.Eqm` of the
tree's expectation system. -/
theorem eqmM_tree_iff (β : ℝ) (V y P M W s : ℕ → Ω → ℝ) :
    TidyR5MoneyMeasure.EqmM (treeSystem T) β V y P M W s ↔
      TidyR5MoneyUncertainty.Eqm T.toExpectationSystem β V y P M W s := by
  refine forall_congr' fun t => ?_
  rw [ae_iff_forall, aeEq_iff, aeEq_iff, pvM_tree]

/-! ### Derived equilibria on finite trees -/

/-- Cochrane (2023), §22.1, pp. 495–496 (**finite trees**): with adapted positions and positive
debt at every node, `(c = y, B, M)` is the household's optimum iff at every node the Fisher
equation `Q_t = βP_tE_t[1/P_{t+1}]` holds, `ι_t ≥ 0`, `M_t ≥ P_ty_t/V_t` with equality where
`ι_t > 0`, and `W_t/P_t = E_t∑βʲs̄_{t+j}` in the tree's expectation system. -/
theorem tree_derived_iff {e : Econ Ω} {B M : ℕ → Ω → ℝ} (hreg : EconReg (treeSystem T) e)
    (hBa : T.toExpectationSystem.Adapted B) (hMa : T.toExpectationSystem.Adapted M)
    (hBpos : ∀ t ω, 0 < B t ω) :
    DerivedEqm (treeSystem T) e B M ↔
      (∀ t ω, e.Q t ω = e.β * e.P t ω * T.toExpectationSystem.E t (invP e (t + 1)) ω) ∧
      (∀ t ω, 0 ≤ iota e t ω) ∧ (∀ t ω, mmin e t ω ≤ M t ω) ∧
      (∀ t ω, 0 < iota e t ω → M t ω = mmin e t ω) ∧
      ∀ t, wealth e.W0 B M t / e.P t =
        TidyR5MoneyUncertainty.pvE T.toExpectationSystem e.β (sbar e M) t := by
  rw [derived_iff_imposed hreg ((adapted_iff T).2 hBa) ((adapted_iff T).2 hMa)
    (fun t => (ae_iff_forall T).2 (hBpos t))]
  simp only [Imposed, Fisher, ae_iff_forall, aeEq_iff, pvM_tree, E_tree]

/-- Cochrane (2023), §22.1, pp. 495–496 (**finite trees, OE-2's conditions derived**): when money
is costly to hold at every node, the derived equilibria are exactly the Fisher equation plus the
core money model `TidyR5MoneyUncertainty.Eqm` of the tree's expectation system. -/
theorem tree_derived_iff_eqm {e : Econ Ω} {B M : ℕ → Ω → ℝ} (hreg : EconReg (treeSystem T) e)
    (hBa : T.toExpectationSystem.Adapted B) (hMa : T.toExpectationSystem.Adapted M)
    (hBpos : ∀ t ω, 0 < B t ω) (hspread : ∀ t ω, 0 < iota e t ω) :
    DerivedEqm (treeSystem T) e B M ↔
      (∀ t ω, e.Q t ω = e.β * e.P t ω * T.toExpectationSystem.E t (invP e (t + 1)) ω) ∧
      TidyR5MoneyUncertainty.Eqm T.toExpectationSystem e.β e.V e.y e.P M (wealth e.W0 B M)
        (sbar e M) := by
  rw [derived_iff_eqmM hreg ((adapted_iff T).2 hBa) ((adapted_iff T).2 hMa)
    (fun t => (ae_iff_forall T).2 (hBpos t)) (fun t => (ae_iff_forall T).2 (hspread t)),
    eqmM_tree_iff]
  simp only [Fisher, ae_iff_forall, E_tree]

/-! ### Perfect foresight: the one-state tree -/

/-- Cochrane (2023), §22.1, p. 496 (perfect foresight): the one-state tree, restated from the
NewKeynesianSelection project (its module TidyR6Household16_25). -/
def unitTree : FiniteTree Unit where
  prob := fun _ => 1
  prob_pos := fun _ => one_pos
  prob_sum := by simp
  info := fun _ => ⊤
  refines := fun _ _ _ _ => trivial

/-- Cochrane (2023), §22.1, p. 496 (perfect foresight): on the one-state tree `E_t` is the
identity, restated from the NewKeynesianSelection project. -/
theorem unitTree_E (t : ℕ) (x : Unit → ℝ) : unitTree.toExpectationSystem.E t x = x := by
  funext ω
  rw [FiniteTree.toExpectationSystem_E]
  exact unitTree.condE_of_const_on_cell fun ω' _ => by rw [Subsingleton.elim ω' ω]

/-- Cochrane (2023), §22.1, p. 496 (perfect foresight): the core money model of the one-state
tree is the perfect-foresight one. -/
theorem eqm_unit_iff (β : ℝ) (V y P M W s : ℕ → Unit → ℝ) :
    TidyR5MoneyUncertainty.Eqm unitTree.toExpectationSystem β V y P M W s ↔
      TidyR5MoneyUncertainty.Eqm perfectForesight β V y P M W s := by
  have h : ∀ t, TidyR5MoneyUncertainty.pvE unitTree.toExpectationSystem β s t =
      TidyR5MoneyUncertainty.pvE perfectForesight β s t := fun t => by
    simp only [TidyR5MoneyUncertainty.pvE, unitTree_E]
    rfl
  simp only [TidyR5MoneyUncertainty.Eqm, h]

/-- Cochrane (2023), §22.1, pp. 495–496 (**perfect foresight**): with positive debt and money
costly to hold, `(c = y, B, M)` is the household's optimum on the one-state tree iff the bond
price is `Q_t = βP_t/P_{t+1}` and the path is an equilibrium of the perfect-foresight money model
`MoneyRegimes.Eqm` with the seigniorage-inclusive surplus. -/
theorem pf_derived_iff {e : Econ Unit} {B M : ℕ → Unit → ℝ}
    (hreg : EconReg (treeSystem unitTree) e) (hBpos : ∀ t, 0 < B t ())
    (hspread : ∀ t, 0 < iota e t ()) :
    DerivedEqm (treeSystem unitTree) e B M ↔
      (∀ t, e.Q t () = e.β * e.P t () / e.P (t + 1) ()) ∧
      MoneyRegimes.Eqm e.β (fun t => e.V t ()) (fun t => e.y t ()) (fun t => e.P t ())
        (fun t => M t ()) (fun t => wealth e.W0 B M t ()) (fun t => sbar e M t ()) := by
  rw [tree_derived_iff_eqm unitTree hreg (fun t => unitTree_E t _) (fun t => unitTree_E t _)
    (fun t ω => by cases ω; exact hBpos t) (fun t ω => by cases ω; exact hspread t),
    eqm_unit_iff, TidyR5MoneyUncertainty.eqm_perfectForesight_iff]
  refine and_congr ⟨fun h t => ?_, fun h t ω => ?_⟩ Iff.rfl
  · rw [h t (), unitTree_E]
    simp only [invP, div_eq_mul_inv]
  · cases ω
    rw [h t, unitTree_E]
    simp only [invP, div_eq_mul_inv]

/-- Cochrane (2023), eq. (22.2), p. 495, and §22.1, p. 496 (**the frictionless model's Fisher
equation and flow condition from optimisation**): under perfect foresight, with positive debt
and money costly to hold, the observable path of a derived equilibrium (inflation
`π_t = log P_t − log P_{t−1}`, the rate `i_t = log P_{t+1} − log P_t`, debt
`v_t = W_{t+1}/P_{t+1}`, the surplus `s̄_t`) satisfies the Fisher equation and the flow condition
(22.2) with `ρ = β` (`StarredModel.Consistent`, via `Links.moneyOutcome`), and the household's
continuously compounded bond yield is exactly `log(1/Q_t) = −log β + i_t`. -/
theorem pf_derived_linear {e : Econ Unit} {B M : ℕ → Unit → ℝ}
    (hreg : EconReg (treeSystem unitTree) e) (hBpos : ∀ t, 0 < B t ())
    (hspread : ∀ t, 0 < iota e t ()) (h : DerivedEqm (treeSystem unitTree) e B M) :
    StarredModel.Consistent perfectForesight e.β (Links.moneyOutcome (fun t => e.P t ())
        (fun t => wealth e.W0 B M t ()) (fun t => sbar e M t ())) ∧
      ∀ t, Real.log (1 / e.Q t ()) = -Real.log e.β + (Links.moneyOutcome (fun t => e.P t ())
        (fun t => wealth e.W0 B M t ()) (fun t => sbar e M t ())).i t () := by
  have hβ0 := hreg.1.1
  obtain ⟨hF, hE⟩ := (pf_derived_iff hreg hBpos hspread).1 h
  obtain ⟨hF', hι, -, hcs, -⟩ :=
    imposed_of_derived hreg (fun t => (ae_iff_forall unitTree).2 fun ω => by
      cases ω; exact hBpos t) h
  obtain ⟨K, hK⟩ := sbar_bdd hreg hF' hι hcs
  have hs : ∀ t, |sbar e M t ()| ≤ K + K := fun t => (ae_iff_forall unitTree).1 (hK t) ()
  refine ⟨Links.moneyOutcome_consistent hβ0.le hreg.1.2 hs hE, fun t => ?_⟩
  have hP := (hE t).1
  have hP1 := (hE (t + 1)).1
  simp only [Links.moneyOutcome]
  rw [hF t, one_div, inv_div, Real.log_div hP1.ne' (mul_pos hβ0 hP).ne',
    Real.log_mul hβ0.ne' hP.ne']
  ring

/-! ### A genuinely random derived equilibrium on the coin-flip tree -/

/-- Cochrane (2023), §22.1, p. 496 (**finite trees, genuine uncertainty**): on the coin-flip tree,
with the coin shock `ε` and `0 < β < 1`, the economy `randEcon β ε` is a derived equilibrium, it
is an equilibrium of the core money model `TidyR5MoneyUncertainty.Eqm` of `coinSystem`, and the
date-1 inverse price level `1/P_1 = 1 ± (1 − β)/2` is not known at date 0. -/
theorem coinTree_derived_eqm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    DerivedEqm (treeSystem coinTree) (randEcon β coinShock) (fun _ _ => 1) (randP β coinShock) ∧
    TidyR5MoneyUncertainty.Eqm coinSystem β (randEcon β coinShock).V (randEcon β coinShock).y
      (randP β coinShock) (randP β coinShock)
      (wealth (fun _ => 2) (fun _ _ => 1) (randP β coinShock))
      (sbar (randEcon β coinShock) (randP β coinShock)) ∧
    coinSystem.E 0 (invP (randEcon β coinShock) 1) ≠ invP (randEcon β coinShock) 1 := by
  have hεa : StronglyAdapted (treeSystem coinTree).𝓕 coinShock := (adapted_iff coinTree).2
    fun t => funext fun ω => by
      rw [FiniteTree.toExpectationSystem_E]
      exact coinTree.condE_of_const_on_cell fun ω' h => coinShock_measurable t h
  have hεb : ∀ t ω, |coinShock t ω| ≤ 1 := fun t ω => by
    unfold coinShock
    split_ifs <;> norm_num
  have hεm : ∀ t, (treeSystem coinTree).E t (coinShock (t + 1)) =ᵐ[(treeSystem coinTree).μ] 0 :=
    fun t => (aeEq_iff coinTree).2 (by rw [E_tree]; exact coinShock_mean_zero t)
  obtain ⟨hD, -, hEqm⟩ := random_derived_eqm hβ0 hβ1 hεa hεb hεm
  refine ⟨hD, (eqmM_tree_iff coinTree _ _ _ _ _ _ _).1 hEqm, fun he => ?_⟩
  have h1 := (aeEq_iff coinTree).1 (rand_E_invP (β := β) hεa hεb hεm 0)
  rw [E_tree] at h1
  have h2 := congrFun (h1.symm.trans he) (true, true)
  rw [rand_invP] at h2
  simp only [coinShock] at h2
  norm_num at h2
  linarith

end Cochrane.ObservationalEquivalence.TidyR6MoneyHouseholdTree
