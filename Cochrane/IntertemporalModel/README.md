# An intertemporal model in Lean

This is the `Cochrane/IntertemporalModel/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Chapter 2, "An intertemporal model" (pp. 20–51), with Online Appendix
A1.1, "The transversality condition" (pp. 554–556). Model equations hold for an arbitrary
expectation operator, so every result covers perfect foresight and genuine uncertainty: random
variables are functions `Ω → ℝ`, processes are `ℕ → Ω → ℝ`, and every equation holds state by
state. The household problem is also solved on a genuine probability space, with Mathlib's
conditional expectation, information that grows forever and equations holding almost surely, and
so are the equilibrium notions, interest-rate targets, the linear model and the family of exact
equilibria whose derivative it is. Present values are genuine infinite sums, and surpluses are signed. The central object is
the fiscal-theory equilibrium: given nominal debt and surpluses, a positive adapted price level
satisfying the bond-pricing equation (2.3), the flow condition (2.4) and the transversality
condition (2.6), or equivalently the valuation equation (2.7) at every date. "The price level is
determined" means that there is exactly one such price level. This is not uniqueness of bounded
solutions, the notion of the Woodford projects. The library contains **764 theorems**, including
the shared core; 548 of them are in the eighteen chapter modules.

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises.

Headline results, in the namespace `Cochrane.IntertemporalModel`:
* **The valuation equation, derived.** The flow condition (2.5) and the transversality condition
  (2.6) at every date hold iff real debt equals the present value of surpluses (2.7) at every
  date, for signed, absolutely summable surpluses (`Valuation.valuation_iff`). With positive debt
  and positive present values there is exactly one equilibrium price level and bond price,
  `P_t = B_{t−1}/pv_t` (`Valuation.existsUnique_eqm`, `Valuation.eqm_price_eq`); with a
  nonpositive present value anywhere there is none (`Valuation.no_eqm_of_pv_nonpos`).
* **The household problem.** The Euler equation and (2.3) are derived from optimisation
  (`Environment.euler_of_optimal`, `Environment.bondPrice_of_optimal`); money is dominated when
  `i > 0` and the rate cannot be negative (`Environment.money_dominated`,
  `Environment.bonds_dominated_of_neg_rate`). Optimisation implies the transversality condition,
  and hence (2.7), under perfect foresight (`Valuation.tvc_of_optimal`,
  `Valuation.valuation_of_optimal`) and under uncertainty with state-contingent plans on a finite
  state space (`Valuation.euler_of_optimal_stoch`, `Valuation.tvc_of_optimal_stoch`,
  `Valuation.valuation_of_optimal_stoch`). The Online Appendix A1.1 argument is proved in full:
  the transversality condition is no-Ponzi plus optimality (`Valuation.tvc_iff_noPonzi_and_optimal`),
  a too-low price level makes debt explode (`Valuation.const_explodes`, `Valuation.const_tvc_iff`),
  and the deviation (1.3) is feasible, improving and optimal for concave increasing utility
  (`Valuation.deviation_feasible`, `Valuation.deviation_improves`,
  `Valuation.deviation_optimal_concave`).
* **Equilibrium formation.** Money is left overnight iff the price level is below
  `B_{t−1}/pv_t` (`EquilibriumFormation.money_overhang_iff`); a too-high price level pushes debt
  negative (`EquilibriumFormation.tooHigh_violates_nonneg_debt`); with `B_{−1} = 0` the price
  level `P_0` is not determined (`EquilibriumFormation.no_initial_debt_not_unique`); under a
  passive surplus rule every price level is an equilibrium
  (`EquilibriumFormation.passive_every_price_eqm`).
* **Fiscal and monetary policy.** Unexpected inflation is determined entirely by present-value
  news (2.13) (`FiscalMonetary.unexpected_inflation`, `FiscalMonetary.no_surprise_iff`). An
  interest-rate target, even a state-contingent one, has exactly one equilibrium
  (`FiscalMonetary.peg_existsUnique`): the target sets expected inflation and fiscal news sets
  unexpected inflation (`FiscalMonetary.inflation_decomposition`). Share splits, equity issues,
  irrelevant future bond sales, the s-shaped surplus and the AR(1) surplus are proved
  (`FiscalMonetary.shareSplit`, `FiscalMonetary.equityIssue_finances_deficit`,
  `FiscalMonetary.future_sales_irrelevant`, `FiscalMonetary.sShape`,
  `FiscalMonetary.ar1_unexpected_inflation`). The central bank and the Treasury together produce
  the flat supply curve (`FlatSupply.twoStep_equilibrium`).
* **The linear fiscal theory of monetary policy.** (2.16) and (2.17) hold exactly, and their
  linear forms are proved as first derivatives at the steady state (`LinearFTMP.fisher_deriv`,
  `LinearFTMP.unexpected_inflation_exact`, `LinearFTMP.linear_217`). Under a peg the solution
  (2.19) exists and is unique for every rate path (`LinearFTMP.peg_existsUnique`); under the rule
  `i_t = θπ_t + u_t` the equilibrium (2.25) exists and is unique for every `θ`, with no Taylor
  principle (`LinearFTMP.rule_existsUnique`). The impulse responses of Figures 2.1 and 2.2 are
  proved in closed form, including the hump and its peak `π_5 = 1.695`
  (`LinearFTMP.fig21_expected_fiscal`, `LinearFTMP.irf_rule`, `LinearFTMP.hump_exists`,
  `LinearFTMP.fig22_peak`).
* **The linear model is the derivative of a family of exact equilibria.** For surpluses
  `s̄ + εŝ_t` and a rate target `i(ε)` the exact nonlinear equilibrium is built in closed form on
  an open neighbourhood of `ε = 0` (`TidyR5Family.famDom`); it is unique, it is the steady state
  at `ε = 0`, it is `C^n` in `ε` for every `n` (analytic included), and its derivative at `0` is
  the unique solution (2.19) of the linear peg model (`TidyR5Family.exp_family_linearization`,
  `TidyR5Family.infl_hasDerivAt`, `TidyR5Family.family_unique`). Under the exact rule
  `log(1 + i_t) = −log β + θπ_t + εu_t` the same holds for every `θ`, with derivative the solution
  (2.25) (`TidyR5FamilyRule.rule_family_linearization`, `TidyR5FamilyRule.rule_unique`). Both hold
  on every finite event tree (`TidyR5Family.tree_family_linearization`,
  `TidyR5FamilyRule.tree_rule_linearization`) and almost surely on a probability space
  (`TidyR5MeasFamily.meas_family_linearization`,
  `TidyR5MeasFamilyRule.mRule_family_linearization`).
* **The bond price is positive.** For `β > 0` a positive payoff has a positive forecast under the
  core `ExpectationSystem` axioms alone, on any state space (`TidyR5BondPrice.E_pos_of_pos`), so
  every equilibrium has `Q_t > 0` and `i_t > −1`, and with pull-out the rate is adapted
  (`TidyR5BondPrice.isEqm_rate_gt`, `TidyR5BondPrice.bondPricing_rate_gt`,
  `TidyR5BondPrice.bondPricing_rate_adapted`). The hypothesis is needed only at `β = 0`
  (`TidyR5BondPrice.beta_zero_counterexample`).
* **One economy, three formalisations.** The equilibrium derived from flow plus transversality,
  the equilibrium defined by the valuation equation, and the peg equilibrium of the Woodford links
  are proved equivalent (`GeneralLinks.equilibrium_iff_isEqm`, `GeneralLinks.equilibrium_iff_pegEqm`),
  so every result about one of them applies to the others (see
  [Three equilibrium notions](#three-equilibrium-notions)); for `β > 0` the first equivalence
  needs no hypothesis on the rate (`TidyR5BondPrice.equilibrium_iff_isEqm_pos`).
* **Links to Woodford.** Woodford's Propositions 2.5 and 2.6 are restated and contrasted with the
  fiscal theory: in the same coin-flip economy a peg has uncountably many solutions of the Fisher
  equation but exactly one fiscal-theory equilibrium (`Links.peg_contrast`), and a rule with
  `|θ| < 1` has uncountably many bounded solutions of Woodford's (2.6) but exactly one equilibrium
  (`Links.taylor_contrast_coin`).
* **Genuine probability models.** The household problem of §2.1 and A1.1 is proved on a
  probability space with a filtration, where `E_t` is Mathlib's conditional expectation and
  information may grow forever (`HouseholdMeasure.Feasible`, `HouseholdMeasure.Optimal`). An
  optimal plan satisfies the Euler inequality almost surely at every date and the Euler equation
  almost surely where bonds are held (`HouseholdMeasure.euler_kkt`,
  `HouseholdMeasure.euler_interior`), and optimisation forces a positive bond price
  (`HouseholdMeasure.bondPrice_pos`, `HouseholdMeasure.bondPrice_formula`,
  `HouseholdMeasure.rate_gt_neg_one_of_formula`). For concave increasing utility, optimisation
  implies the transversality condition with no `Valuation.InfoStable`
  (`HouseholdMeasureTVC.tvc_of_optimal`), the Euler equation plus the transversality condition
  is optimal (`HouseholdMeasureTVC.optimal_of_euler_tvc`), and at `c = y` (2.6) and (2.7) hold
  almost surely at every date (`HouseholdMeasureTVC.valuation_of_optimal_eqm`). In the i.i.d.
  economy, where every history has probability zero, the price level
  `P_t = B̄/(s̄/(1 − β) + σε_t)` is a genuine equilibrium in which real debt carries news
  (`HouseholdMeasureTVC.IID.iid_equilibrium`). On a finite event tree these results return the
  finite-state statements of `Valuation` (`HouseholdMeasureTVC.Link.link_euler`,
  `HouseholdMeasureTVC.Link.link_tvc_valuation`).
* **Equilibrium on a genuine probability space.** Both equilibrium notions are restated with
  equations holding almost surely (`TidyR5Meas.MEquilibrium`, `TidyR5Meas.MIsEqm`), `i > −1`
  almost surely is a theorem (`TidyR5Meas.mEqm_rate_gt`), and the two notions agree
  (`TidyR5Meas.mFlowTvc_iff_valuation`, `TidyR5Meas.mEquilibrium_iff_mIsEqm`). An interest-rate
  target has an equilibrium, unique almost surely at every date
  (`TidyR5Meas.mPeg_existsUnique`, `TidyR5Meas.mPeg_existsUnique_mIsEqm`), with (2.13), (2.15),
  (2.26) and the expected/unexpected inflation decomposition almost surely
  (`TidyR5Meas.mUnexpected_inflation`, `TidyR5Meas.mDebt_eq`, `TidyR5Meas.mFlow`,
  `TidyR5Meas.mInflation_decomposition`). The linear peg and rule models have a solution, unique
  up to null sets, for every `θ` (`TidyR5MeasLinear.mPeg_linear_existsUnique`,
  `TidyR5MeasLinear.mRule_linear_existsUnique`). On a finite event tree each notion is its
  `ExpectationSystem` counterpart (`TidyR5MeasLinear.Link.tree_mEquilibrium_iff`,
  `TidyR5MeasLinear.Link.tree_mIsEqm_iff`, `TidyR5MeasLinear.Link.tree_mPegModel_iff`,
  `TidyR5MeasLinear.Link.tree_mRuleModel_iff`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections are:
* the terminal weight of the iterated flow condition on p. 28 and in A1 (1.2) is `β^{T+1}`, not
  `β^T` (E4);
* the AR(1) formula for unexpected inflation on p. 43 omits the factor `B_{t−1}/P_{t−1}` (E5);
* `ΔE_tπ_t = ΔE_tp_t`, not `ΔE_tp_t − p_{t−1}` (p. 38, E6);
* "borrow, spend, repay has no effect at all on inflation" (p. 50) holds under perfect foresight
  but is false under uncertainty: in a coin-flip economy it changes the date-1 price level in
  every state (`FiscalMonetary.CoinExample.stimulus_not_neutral`);
* the debt-sale formula `Q_tB_t = βE_ts_{t+1}` (p. 24) holds, in real terms, only when the debt
  is retired at `t + 1`;
* "one percent" on pp. 32 and 48 is `1/105` and `1/99` exactly (E7), (2.28) is cited as (2.15)
  (E9), and the no-Ponzi limit in A1.1 is `≥ 0`, not `> 0` (E27).

Not formalised:
* the discursive parts of the chapter: the Apple-share analogy and the run interpretation
  (§2.2), the equilibrium-formation philosophy and the debates with Bassetto and
  Atkeson–Chari–Kehoe (pp. 28–29), the Ricardian debate and the data (pp. 43–44), the
  institutional history of §2.8, the Federal Reserve's operating procedures (§2.9), and the
  historical episodes of §2.10;
* the rest of the chapter on a genuine probability space: the household problem, the i.i.d.
  equilibrium, the equilibrium notions and their equivalence, interest-rate targets with the
  price-level formulas, (2.13), (2.15), (2.26), the linear peg and rule models and the family of
  exact equilibria are measure-theoretic, but the Woodford contrasts of `Links` (Propositions 2.5
  and 2.6, Ricardian transversality), the remaining `FiscalMonetary` and `FlatSupply` corollaries
  (share splits, equity issues, AR(1) surpluses, the s-shape, stimulus, the flat supply curve),
  price-level targets and the impulse responses of Figures 2.1 and 2.2 are stated only for an
  `ExpectationSystem`;
* the measure-theoretic equilibrium results without their explicit hypotheses: target existence
  assumes surpluses bounded almost surely, present values bounded below by `c > 0` almost surely
  and an integrable bond price `1/(1 + i)` (`TidyR5Meas.mPeg_equilibrium`; Mathlib's `condExp`
  is `0` on non-integrable functions); the equivalence of the two notions assumes integrable real
  debt and keeps the rate adapted as a hypothesis, which almost-sure bond pricing does not give
  without a complete filtration (`TidyR5Meas.mEquilibrium_iff_mIsEqm`); the `ε`-families assume
  `ŝ`, `î` and `u` bounded everywhere, and their smoothness and derivatives hold for almost every
  state, because versions of conditional expectations are bounded only almost surely
  (`TidyR5MeasFamily.mFam_contDiffOn`, `TidyR5MeasFamilyRule.mRule_family_linearization`);
* the measure-theoretic household problem without its regularity hypotheses: the Euler equation
  assumes that consumption, the bond price and `1/P` are essentially bounded at the dates
  involved (`HouseholdMeasure.EulerRegular`, per date, automatic on a finite tree) and holds with
  equality only on `{B_t > 0}`; necessity of the transversality condition assumes concave
  increasing utility with continuous `u'`, an admissible after-tax endowment plan and
  integrability of the debt terms (the finite-state proof needs only strictly increasing `u`,
  with `Valuation.InfoStable`); (2.6) and (2.7) at every date assume uniformly essentially
  bounded surpluses;
* the stochastic-discount-factor form of the transversality condition remarked in A1.1, which
  belongs to Chapter 3 (§3.3);
* "an announcement only affects long-term nominal bond prices" (p. 36), since the model has no
  long-term debt, and "the lagged-rate rule has much the same effect" (p. 40), which has no
  precise content;
* Figure 2.1 on its calendar axis: the responses are stated as innovations at a general shock
  date.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](IntertemporalModel/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (shared core, restated from the earlier projects; not used by this chapter) |
| [Expectations](IntertemporalModel/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; bounded adapted processes; forward series; the pull-out property (shared core) |
| [ExpectationsFiniteTree](IntertemporalModel/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; coin-flip examples (shared core) |
| [ForwardSolution](IntertemporalModel/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [ExpectationTools](IntertemporalModel/ExpectationTools.lean) | 28 | Innovations `ΔE_{t+1}` and their algebra; known variables under pull-out; the hypotheses `FunctionsKnown`, `Closed` and `MonotoneConvergence` with their instances |
| [Environment](IntertemporalModel/Environment.lean) | 22 | §2.1: (2.1)–(2.5), the household problem and the Euler equation under perfect foresight, (2.3), money demand, proportional taxes |
| [Valuation](IntertemporalModel/Valuation.lean) | 52 | §2.1 and A1.1: the transversality condition, (2.5)–(2.7) both ways, existence and uniqueness of the price level, (2.8), the A1.1 argument, optimisation implies the TVC under perfect foresight and under uncertainty |
| [EquilibriumFormation](IntertemporalModel/EquilibriumFormation.lean) | 19 | §§2.2–2.3: (2.9)–(2.11), roll-over, passive rules, `B_{−1} = 0`, the money overhang, the p. 28 terminal identity corrected |
| [FiscalMonetary](IntertemporalModel/FiscalMonetary.lean) | 94 | §2.4, §§2.7–2.8, §2.10: (2.12)–(2.15), (2.26)–(2.27), interest-rate targets, real-rate pegs, share splits and equity issues, the s-shape, AR(1) surpluses, fiscal stimulus and its coin-flip counterexample |
| [FlatSupply](IntertemporalModel/FlatSupply.lean) | 13 | §2.9: (2.28), the Treasury rule, the flat supply curve, the two-step process |
| [LinearFTMP](IntertemporalModel/LinearFTMP.lean) | 57 | §§2.5–2.6: (2.16)–(2.19) exact and linear, Figure 2.1, price-level targets, passive fiscal policy, the rule (2.20)–(2.25) for every `θ`, Figure 2.2 and the hump |
| [Links](IntertemporalModel/Links.lean) | 28 | Woodford's Propositions 2.5 and 2.6, Ricardian transversality (4.2) and budget timing (4.1), restated and contrasted with the fiscal theory |
| [GeneralLinks](IntertemporalModel/GeneralLinks.lean) | 16 | The three equilibrium notions and the two present values proved equivalent; the linear model as the derivative of the exact one |
| [ExpectationsMeasure](IntertemporalModel/ExpectationsMeasure.lean) | 71 | Measure-theoretic expectations (shared core, copied from `ObservationalEquivalence`): `MeasExpectationSystem` with Mathlib's `condExp`, the axioms a.e., news, the forward equation and sunspots, AR(1) conditional variance, bridges to and from the core `ExpectationSystem` |
| [ExpectationsMeasureIID](IntertemporalModel/ExpectationsMeasureIID.lean) | 37 | The genuine i.i.d. economy on `ℕ → ℝ` under `ν^ℕ` (shared core): independence, moments, every history null, determinacy iff `\|a\| < 1`, AR(1), the `±1` coin |
| [HouseholdMeasure](IntertemporalModel/HouseholdMeasure.lean) | 32 | §2.1 on a probability space: feasible, admissible and optimal plans, differentiation under the integral, the Euler inequality at every date and the Euler equation on `{B_t > 0}`, the bond price (2.3) derived positive |
| [HouseholdMeasureTVC](IntertemporalModel/HouseholdMeasureTVC.lean) | 32 | §2.1 and A1.1 on a probability space with information growing forever: the TVC from optimisation (Kamihigashi's scaling deviation), sufficiency of Euler plus TVC, (2.5)–(2.7) almost surely at `c = y`, the i.i.d. equilibrium, links to the finite-state `Valuation` results |
| [TidyR5BondPrice](IntertemporalModel/TidyR5BondPrice.lean) | 15 | (2.3): strict positivity of `E_t` from the core axioms; the bond price is positive and `i > −1` in every equilibrium (`β > 0`); the rate conditions of `FiscalMonetary.Equilibrium` and the rate hypotheses of `GeneralLinks.equilibrium_iff_isEqm` are redundant; the `β = 0` counterexample |
| [TidyR5Family](IntertemporalModel/TidyR5Family.lean) | 34 | §§2.4–2.5: the family of exact peg equilibria for surpluses `s̄ + εŝ`, in closed form, unique, `C^n` for every `n`, with the solution (2.19) as its derivative; the canonical rate `β⁻¹exp(εî)`; finite trees |
| [TidyR5FamilyRule](IntertemporalModel/TidyR5FamilyRule.lean) | 17 | §2.6: the same family under the exact rule `log(1 + i_t) = −log β + θπ_t + εu_t`, every `θ`, with the solution (2.25) as its derivative |
| [TidyR5Meas](IntertemporalModel/TidyR5Meas.lean) | 25 | §2.1 and §2.4 on a probability space: both equilibrium notions a.s. and their equivalence, `i > −1` derived, interest-rate targets (existence, a.s. uniqueness), (2.13), (2.15), (2.26), the inflation decomposition |
| [TidyR5MeasLinear](IntertemporalModel/TidyR5MeasLinear.lean) | 19 | §§2.5–2.6 on a probability space: the linear peg and rule models, existence and a.s. uniqueness, the fiscal shock; links of every measure-theoretic notion to its core version on finite trees |
| [TidyR5MeasFamily](IntertemporalModel/TidyR5MeasFamily.lean) | 26 | The family of exact peg equilibria on a probability space: equilibrium and a.s. uniqueness for each `ε`, a.s. smoothness, the derivative (2.19) almost surely; links to `TidyR5Family` on finite trees |
| [TidyR5MeasFamilyRule](IntertemporalModel/TidyR5MeasFamilyRule.lean) | 19 | The rule family on a probability space for every `θ`: bounds, equilibrium, a.s. uniqueness, smoothness, the derivative (2.25); link to `TidyR5FamilyRule` on finite trees |

## Modelling conventions

* **Expectations.** Random variables are `Ω → ℝ`, and every model equation holds as an equality
  of functions, for an arbitrary `ExpectationSystem` (linear, constant-preserving, monotone, with
  the law of iterated expectations). Perfect foresight (`perfectForesight`) and every finite event
  tree (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) are instances. The coin-flip
  tree (`ExpectationsFiniteTree.coinSystem`) supplies the counterexamples under genuine
  uncertainty (`FiscalMonetary.CoinExample.stimulus_not_neutral`, `Links.peg_contrast`,
  `Links.taylor_contrast_coin`).
* **Properties of expectations as hypotheses.** The `ExpectationSystem` axioms do not give every
  property of conditional expectations, so the following are hypotheses where used, each proved
  for perfect foresight and for every finite event tree:
  * `ExpectationSystem.PullOut`: date-`t` factors come out of `E_t`;
  * `ExpectationTools.FunctionsKnown`: functions of date-`t` variables are known at `t`, so that
    `P_t = B_{t−1}/pv_t` is adapted;
  * `ExpectationTools.Closed`: the two-variable version, restated from the Woodford Chapter 2
    project; it implies `FunctionsKnown` (`ExpectationTools.functionsKnown_of_closed`);
  * `ExpectationTools.MonotoneConvergence`: `E_t` commutes with sums of nonnegative terms;
  * `Valuation.Faithful` and `Valuation.InfoStable`: every state has positive probability, and
    information stops growing; used only for optimisation under uncertainty on a finite state
    space.

  On a probability space these properties are theorems about `condExp` rather than hypotheses
  (pull-out, monotone convergence, strict positivity:
  `ExpectationsMeasure.MeasExpectationSystem.E_pullOut`,
  `HouseholdMeasureTVC.integrable_mul_of_E`, `HouseholdMeasure.E_pos`), and the household
  results of `HouseholdMeasure` and `HouseholdMeasureTVC` use neither `Faithful` nor `InfoStable`.
* **Measure-theoretic expectations.** The core `ExpectationSystem` is kept unchanged, and every
  result above stated for it still holds. On a countable `Ω` it forces finitely supported
  forecasts, so it cannot carry an infinite-horizon model with nondegenerate shocks.
  `ExpectationsMeasure` adds, alongside it, a probability space with a filtration
  (`ExpectationsMeasure.MeasExpectationSystem`): `E_t` is Mathlib's conditional expectation
  `condExp`, variables are measurable functions, processes are adapted (Mathlib's
  `StronglyAdapted`) and equations hold almost everywhere. The bridge is additive and runs both
  ways: a finite event tree is a measure system with the same `E_t` at every state
  (`ExpectationsMeasure.TreeBridge.treeSystem_E`), and a measure system on a finite discrete
  state space with full support is a core system with the pull-out property
  (`ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem`,
  `ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_pullOut`). The household
  problem on this space is `HouseholdMeasure.Feasible`, `HouseholdMeasure.Admissible`
  (`E∑βⁿ|u(c_n)| < ∞`) and `HouseholdMeasure.Optimal`, with constraints holding almost surely;
  on a finite tree feasibility is the core `Valuation.SFeasible`
  (`HouseholdMeasureTVC.Link.feasible_iff`) and core optimality implies measure optimality
  (`HouseholdMeasureTVC.Link.optimal_of_core`). The genuine instance is the i.i.d. economy on
  `ℕ → ℝ` under `ν^ℕ`, in which every history has probability zero
  (`ExpectationsMeasureIID.iidSystem`, `ExpectationsMeasureIID.iid_not_finitely_supported`).
* **Timing of debt.** The book's `B_t` is sold at the end of date `t` and matures at `t + 1`.
  `Environment`, `Valuation` and `EquilibriumFormation` index debt by maturity date,
  `Bm t = B_{t−1}`. `FiscalMonetary`, `FlatSupply` and `GeneralLinks` index it by issue date,
  `B t = B_t`, with the initial debt `Bm1 = B_{−1}`. `GeneralLinks.debtPath` converts one into the
  other.
* **Present values.** `Valuation.pv` is `∑_j β^j E_t s_{t+j}`, the core forward series; it is
  controlled by absolute summability (`Valuation.AbsSummable`) because surpluses are signed.
  `FiscalMonetary.pv` is the book's literal `E_t ∑_j β^j s_{t+j}` of the ex-post sum
  `FiscalMonetary.epv`, and `FiscalMonetary.pvEx` starts at `j = 1`. They agree under monotone
  convergence or for bounded surpluses (`GeneralLinks.fm_pv_eq_pv`,
  `GeneralLinks.fm_pv_eq_pv_of_bounded`).
* **Innovations.** `ExpectationTools.innov t x = E_{t+1}x − E_t x` is the book's `ΔE_{t+1}`. A
  shock (`LinearFTMP.IsShock`) is known when it arrives and has zero forecast.
* **The linear model.** In `LinearFTMP` inflation, rates and shocks are deviations from the
  steady state, and solutions are unique given `π_0`, which is set by date-0 fiscal news outside
  the model's date-0 information. No boundedness is imposed; boundedness is proved separately
  (`LinearFTMP.pegSol_bounded`, `LinearFTMP.ruleSol_bounded`, `LinearFTMP.ruleSol_unbounded`).
* **Explicit hypotheses.** Positivity the book leaves implicit is stated in each theorem: positive
  debt, positive present values in every state (and positive `pvEx` under a target), `i > −1`
  (a consequence of (2.3) when `β > 0`, `TidyR5BondPrice.bondPricing_rate_gt`), bounded surpluses where expectations and infinite sums are interchanged, and `|βη| < 1` for
  AR(1) surpluses.

## Three equilibrium notions

The chapter was formalised in three chains that use three definitions of equilibrium. Each is
natural for part of the chapter, and `GeneralLinks` proves that they describe the same economies:
* `Valuation.IsEqm` (§2.1) is the *derived* notion. Given maturing debt `Bm` and surpluses, it
  asks for a positive adapted price level `P` and bond price `Q` satisfying the bond-pricing
  equation (2.3), the flow condition (2.4) and the transversality condition (2.6) at every date.
  The valuation equation is a theorem about it (`Valuation.eqm_realDebt_eq_pv`).
* `FiscalMonetary.Equilibrium` (§§2.4–2.10) is the *valuation-equation* notion. Given surpluses
  and `B_{−1}`, it asks for an adapted positive price level, adapted debt sold `B` and an adapted
  rate `i > −1` satisfying the valuation equation (2.7)/(2.12) and the bond-pricing condition
  (2.3)/(2.14). Debt is indexed by issue date and the bond price is written through `i`, so
  whether `B` or `i` is the policy instrument is a matter of which is given. For `β > 0` and with
  pull-out the conditions "`i` adapted" and "`i > −1`" follow from the others
  (`TidyR5BondPrice.equilibrium_iff_reduced`).
* `Links.PegEqm` (p. 33) is the *peg* notion used against Woodford. It takes an arbitrary
  present-value process and a scalar `B_{−1}`, and asks for prices and debt satisfying Woodford's
  exact Fisher equation (`LinearFTMP.FisherExact`) and the valuation equation.

The equivalences are:
* `GeneralLinks.equilibrium_iff_isEqm`: `FiscalMonetary.Equilibrium` holds iff `Valuation.IsEqm`
  holds with maturing debt `GeneralLinks.debtPath` and bond price `Q_t = 1/(1 + i_t)`, under
  pull-out, monotone convergence, `β ≥ 0`, adapted surpluses absolutely summable in expectation
  and ex post, adapted `B` and an adapted `i > −1`. Consequences:
  `GeneralLinks.equilibrium_price_eq_eqmPrice`, `GeneralLinks.equilibrium_realRevenue` and
  `GeneralLinks.peg_existsUnique_isEqm` (an interest-rate target selects exactly one derived
  equilibrium). For `β > 0` the hypotheses on `i` are redundant
  (`TidyR5BondPrice.equilibrium_iff_isEqm_pos`); at `β = 0` they are needed
  (`TidyR5BondPrice.beta_zero_counterexample`).
* `GeneralLinks.equilibrium_iff_pegEqm`: with present value `FiscalMonetary.pv` and a constant
  initial debt, `Links.PegEqm` is `FiscalMonetary.Equilibrium`, for an adapted `i > −1`. The two
  peg constructions coincide with no hypotheses (`GeneralLinks.ftplPrice_eq_pegP`,
  `GeneralLinks.ftplDebt_eq_pegB`), and so does the two-step process of §2.9
  (`GeneralLinks.twoStep_eq_debtPath`).
* `GeneralLinks.bondPricing_iff_fisherExact`: the bond-pricing condition is the exact Fisher
  equation. Every derived equilibrium satisfies it in logs (`GeneralLinks.isEqm_fisherExact`,
  `GeneralLinks.isEqm_fisher_log`), and every valuation-equation equilibrium satisfies the exact
  (2.17) with the fiscal shock of the linear model (`GeneralLinks.innov_epv_eq_pvNews`,
  `GeneralLinks.equilibrium_pvNews`, `GeneralLinks.equilibrium_debt_218`). The derivatives of
  these exact equations are the linear (2.16) and (2.17) (`LinearFTMP.fisher_deriv`,
  `LinearFTMP.linear_217`).

So every result of `FiscalMonetary` and `FlatSupply` is a result about the equilibria derived
from optimisation, flow and transversality in `Valuation`, and the peg results of `Links` are
results about the same equilibria.

The three notions are stated for an `ExpectationSystem`. The equivalences take an adapted
`i > −1` as a hypothesis, but for `β > 0` it follows from the bond-pricing condition and the core
axioms alone, on any state space (`TidyR5BondPrice.E_pos_of_pos`,
`TidyR5BondPrice.bondPricing_rate_gt`, `TidyR5BondPrice.bondPricing_rate_adapted`). On a genuine
probability space the valuation-equation and derived notions are restated almost surely
(`TidyR5Meas.MEquilibrium`, `TidyR5Meas.MIsEqm`) and proved equivalent with no `i > −1`
hypothesis (`TidyR5Meas.mEquilibrium_iff_mIsEqm`); on a finite event tree they are
`FiscalMonetary.Equilibrium` and `Valuation.IsEqm` (`TidyR5MeasLinear.Link.tree_mEquilibrium_iff`,
`TidyR5MeasLinear.Link.tree_mIsEqm_iff`). Separately, `HouseholdMeasureTVC` proves the
household side of `Valuation.IsEqm` without `Valuation.InfoStable`: at `c = y`, optimisation
gives (2.6) and (2.7) almost surely at every date (`HouseholdMeasureTVC.valuation_of_optimal_eqm`),
and a bond price of the form (2.3) is positive with `i > −1`
(`HouseholdMeasure.rate_gt_neg_one_of_formula`). On a finite event tree this returns the core
`Valuation.TVC` and valuation equation in every state
(`HouseholdMeasureTVC.Link.link_tvc_valuation`).

## Relation to the Woodford projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects, so the project builds on its own; `Determinacy` (Galí 2015,
Chapter 3, and Woodford's Appendix C) is carried for the later Cochrane projects and is not used
here. Nothing is imported from those projects. Three restatements from the Woodford Chapter 2
project (`PriceLevelDetermination`) serve as tools: `ExpectationTools.MonotoneConvergence`,
`ExpectationTools.Closed` and `LinearFTMP.hasDerivAt_E_exp`. `Links` restates the following
Woodford results and proves the contrast with the fiscal theory:
* **Proposition 2.5** (Chapter 2): under an exogenous rate the exact Fisher equation (1.21) has
  uncountably many price paths with the same `P_0` (`Links.FisherExactW`, `Links.Kexp`,
  `Links.grossInfl`, `Links.sunspotPrice`, `Links.sunspot_fisher`, `Links.sunspotPrice_injective`,
  `Links.prop_2_5_uncountable`). Cochrane's (2.3) is (1.21) with `u_c ≡ 1`
  (`Links.fisher_iff_W`). Adding the valuation equation gives exactly one equilibrium for every
  adapted peg and every present value bounded away from zero (`Links.peg_ftpl_existsUnique`). In
  the same coin-flip economy, that equilibrium is one point of Woodford's uncountable set
  (`Links.peg_contrast`): the formal content of "the fiscal theory overturns" the indeterminacy of
  pegs (p. 33).
* **Proposition 2.6** (Chapter 2): (2.6) has a unique bounded solution for all bounded
  disturbances iff `|φ_π| > 1` (`Links.Eq26`, `Links.eq26_iff_solves`, `Links.prop_2_6_iff`,
  `Links.sunspotInfl`, `Links.sunspotInfl_solves`, `Links.sunspotInfl_bounded`). Cochrane's
  (2.24) is Woodford's (2.6) with `φ_π = θ` (`Links.eq26_iff_224`), every fiscal-theory
  equilibrium solves it (`Links.rule_solves_eq26`), and for `|θ| ≤ 1` the rule fails Woodford's
  criterion but has exactly one fiscal-theory equilibrium (`Links.taylor_contrast`,
  `Links.taylor_contrast_coin`).
* **Ricardian transversality, (4.2)** (Chapter 2): under `T = αW − ΔM` with `0 < α ≤ 1` the
  transversality condition holds along every path (`Links.discount`, `Links.ricardian_step`,
  `Links.ricardian_discounted`, `Links.ricardian_tvc`). So under a passive rule the valuation
  equation holds at every initial price level (`Links.passive_any_price`), while with given
  surpluses it pins the price level and any other value violates transversality
  (`Links.active_unique_value`, `Links.active_tvc_fails`). This is the infinite-horizon
  counterpart of the Chapter 1 project's identification of the passive rule with Woodford's
  `α = 1`.
* **Budget timing, (4.1)** (Chapter 4, `NeoWicksellianFramework`): Woodford's `Budget` is
  Cochrane's (2.4) with face value `B_t = (1 + i_t)D_t` and nominal surplus `T_t − P_tG_t`
  (`Links.Budget`, `Links.timing_link`); Woodford's real debt `b_t` is Cochrane's
  `V_t = B_t/P_t` (`Links.timing_real`).

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
