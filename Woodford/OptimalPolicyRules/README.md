# Optimal policy rules in Lean

This is the `Woodford/OptimalPolicyRules/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Woodford (2003), *Interest and Prices*, Chapter 8, "Optimal Monetary
Policy Rules" (pp. 534–623), together with the proofs
in Appendix G (pp. 716–745). Model equations hold for an arbitrary expectation operator, so every
result covers perfect foresight and genuine uncertainty. Losses are genuine infinite discounted
sums over bounded plans. Every optimality claim is proved as optimality: a feasible plan satisfying
the first-order conditions minimises the expected loss over all bounded feasible plans (Lagrangian
sufficiency), with uniqueness from strict convexity. "Optimal from a timeless perspective" and
"robustly optimal" are given precise definitions and proved. "Unique equilibrium" means unique
among bounded adapted processes. The library contains **1180 theorems**, including the shared
core.

The general Giannoni–Woodford theory of §§1.4–1.5 (Propositions 8.1–8.4) is deferred until both
books are finished, by the author's decision. Proposition 8.1's conclusion is a hypothesis
structure and Proposition 8.3 a stated claim, and everything the chapter derives from them is
proved. All the concrete results (§§2–4, Propositions 8.5–8.11, Appendix G.2–G.10) are proved
in full.

Headline results, in the namespace `Woodford.OptimalPolicyRules`:
* **The general framework.** Lagrangian sufficiency for the general LQ problem (1.1)–(1.4) under
  any expectation system with pull-out, as an exact identity (`GeneralFOC.lagrangian_gap`,
  `GeneralFOC.lagrangian_sufficiency`); the timeless and robust optimality definitions
  (`GeneralSetup.LQProblem.TimelesslyOptimalPlan`, `GeneralSetup.RobustlyOptimal`); the root
  pairing of fn 8 and a counterexample to its "exactly half" (`GeneralFOC.Pencil.pencil_det_pairing`,
  `GeneralFOC.Pencil.fn8_counterexample`); the target criterion (1.23) through the adjugate, with
  the corrected degree of `α(L)` (`TargetCriterion.Crit.eq123_adjugate`,
  `Adjugate.natDegree_alpha_le_rank`, `Adjugate.nilpotent_counterexample`); Proposition 8.2
  conditional on Proposition 8.1 (`TargetCriterion.Prop82.prop82_optimal`,
  `TargetCriterion.Prop82.prop82_unique`); the lemma behind (1.30) ⇔ (1.31) for polynomials of any
  degree with complex roots (`TargetCriterion.eq130_iff_eq131`).
* **Optimal inflation targeting rules.** The criterion (2.5) is robustly optimal, and so is (2.9)
  for every `0 ≤ γ ≤ 1` and every (2.10) (`InflTargetInertia.baseline_robustlyOptimal`,
  `InflTargetInertia.indexation_robustlyOptimal`, `InflTargetInertia.rule210_robustlyOptimal`);
  the flexible-wage limit (2.14) as a genuine limit of equilibria
  (`InflTargetStickyWages.flexible_wage_family`); the corrected (2.20) derived and sufficient, and
  determinate exactly when every root of a cubic lies outside an ellipse, which fails for some
  admissible parameters (`InflTargetStickyWages.foc_imp_criterion`,
  `InflTargetStickyWages.criterion_determinacy_iff_stableRoots`,
  `InflTargetStickyWages.P1_criterion_not_determinate`); (2.22) robustly optimal for `κ_w = κ_p`
  (`InflTargetStickyWages.sym_robustlyOptimal`); (2.27) robustly optimal for every `0 ≤ δ < 1`
  (`InflTargetHabit.habit_robustlyOptimal`); (2.32) and (2.34) with predetermined decisions
  (`InflTargetPredetermined.eq232_optimal_rule`, `InflTargetPredetermined.eq234_of_optimal`); the
  Giannoni–Woodford weights and `δ` (`GWModel.deltaGW_unique`, `GWModel.deltaGW_table`).
* **Optimal interest-rate rules.** Proposition 8.5 holds for every admissible parameter vector:
  the model's characteristic polynomial never has a root in `1 ≤ |μ| ≤ β⁻¹`, so the rule is always
  determinate and the book's hypothesis is redundant (`IRuleBasic.rule_determinate`,
  `IRuleBasic.pG_ne_zero_of_annulus`, `IRuleBasic.bounded_optimum_exists`, `IRuleBasic.prop_8_5`);
  the rule equilibrium is the unique optimum (`IRuleBasic.rule_eqm_unique_optimum`);
  Proposition 8.6 and the target criterion (3.13) (`IRuleForwardIntegrated.prop_8_6`,
  `IRuleForwardIntegrated.rule_iff_crit313`); Proposition 8.7 (`CubicRoots.prop_8_7`); the
  rule system of p. 593 is determinate (uniqueness) for every admissible parameter vector, by
  strict convexity rather than a root count (`InflationInertiaRules.rule_system_unique`,
  `InflationInertiaRules.rule_system_determinate`); Propositions 8.8–8.11, unconditional
  (`InflationInertiaRules.prop_8_8_ruleIII`, `Links.prop_8_9_ruleIII_standing`,
  `Links.prop_8_10_standing`, `Links.prop_8_11_standing`), with their limits as `γ → 0` and
  `γ → 1` along the actual roots (`Links.prop_8_9_ruleI_limit_standing`,
  `Links.prop_8_11_limit_one_standing`); the delayed-information versions (3.29)–(3.31)
  (`Links.eq316_delay_iff_target331`); the reaction function (4.1) implements the optimal policy
  (`Reflections.rule41_timelesslyOptimal`).
* **Numbers.** `γ̄ ∈ (.3533, .3534)` (`CubicRoots.calib_gamma_bar`); the Fig. 8.4 mean horizon in
  `(2.2, 2.25)` and the relative weight `∑|α_j|/α₀ ∈ (.386, .389)`, by interval arithmetic
  (`Links.fig_8_4_mean_horizon_standing`, `Links.fig_8_4_abs_weight_ratio_standing`); the
  p. 586 and pp. 590–591 coefficients (`IRuleBasic.p586_numbers`,
  `IRuleForwardIntegrated.p590_numbers`).
* **Cross-links.** The formalisations of the same objects in different modules are proved to
  agree: the canonical roots of Proposition 8.7 satisfy the hypotheses of Propositions 8.9–8.11
  (`Links.inertiaRoots_of_standing`); the two Euler equations, `A(z)` and discriminants coincide
  (`Links.euler_iff_euler`, `Links.modelDisc_eq_deltaG`); at `γ = 0` Proposition 8.5's
  equilibrium is the unique solution of the p. 593 rule system (`Links.inertia_system_gamma_zero`);
  the model equations of the sections agree (`Links.asInd_iff`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections and results:
* the (2.6) misprint `βE_t[π_{t+1} − π_t]` for `βE_t[π_{t+1} − γπ_t]`, found independently in §2.1
  and §3.2; the wrong target criterion (2.20) (E14) and the cross-reference of p. 563 (E15); the
  typo in (2.32) (E16); (2.26) holding only for bounded processes (E17); the degree of `α(L)`
  (E18); the "exactly half" of fn 8 (E19);
* with `κ_w ≠ κ_p` the corrected (2.20) is determinate exactly when every root of
  `P(Z) = λ_xZ(Z + ξ)² + λ_w(κ_wZ + Δ)² + λ_p(κ_pZ + Δ)²` lies outside an explicit ellipse (exact
  region under perfect foresight); the admissible parameters P1 violate it, and then neither the
  optimal plan nor commitment to the criterion is determinate;
* Proposition 8.5 holds for all admissible parameters (E21), and the p. 593 determinacy claim
  holds for all parameters by strict convexity;
* the gaps in Appendix G.6 and Lemma G.2 (E20, E22) and the `γ → 1` limits of Propositions 8.9
  and 8.11, closed;
* the printed `φ_x = .15` of pp. 590–591 is `.164` (S2), and `φ_x = .33` of p. 586 is `.3226`;
  `λ_x = .0026` of p. 574 is `.0027`;
* the Fig. 8.4 ratio `.39` confirmed by the enclosure `(.386, .389)`.

Not formalised:
* the general theory of §§1.4–1.5: Propositions 8.1–8.4 are present only as hypothesis structures
  and conditional theorems (`TargetCriterion.Prop81.Prop81Conclusion`,
  `TargetCriterion.Prop83Claim`, `TargetCriterion.prop84_conditional`), deferred until both books
  are finished (author's decision); with them Assumptions 8.3–8.4 (App. G.1), the claim of
  Proposition 8.2 that the equilibrium has the form (1.5) with (1.24) (so `GeneralSetup.RobustlyOptimal`
  is not instantiated in the general setting), the existence of the bounded forward inverse in
  Proposition 8.4, a general "exactly half" root count for fn 8, and the exogenous-instrument
  determinacy claim of p. 546;
* the specialisation of the general target-criterion machinery of §1 to the concrete models of
  §§2–3, deferred with Propositions 8.1–8.4: the concrete sections prove their own optimality
  directly, and only the faithfulness hypothesis is shared;
* necessity of the first-order conditions (that every optimum satisfies them), which the book
  also asserts without proof; consequently the direction "original ⇒ restated" of (1.11)–(1.12)
  is conditional (`GeneralFOC.LQ.timeless_restated`), and the necessity of the (2.5) criterion is
  proved under perfect foresight only (`InflTargetInertia.timeless_criterion_pf`);
* existence of a bounded solution of the p. 593 rule system for every disturbance and history
  beyond `γ = 0`: uniqueness is proved for all parameters, existence is assumed as in
  Proposition 8.5's hypothesis, and supplied at `γ = 0` by `Links.inertia_system_gamma_zero`;
* the parity remark of p. 727 ("one or three roots" of `Δ` in `(0, 1)`), which nothing uses;
  a root in `(0, 1)` and one in `(1, ∞)` are proved, and at the calibration the root in `(0, 1)` is
  unique;
* the "only if" half of the exact determinacy region for `κ_w ≠ κ_p` on the ellipse boundary,
  proved under perfect foresight only (`InflTargetStickyWages.foc_not_exists_boundary`); existence
  inside the region and failure strictly inside the ellipse hold for every expectation system;
* the derivation of the Giannoni–Woodford criteria (2.41)–(2.45) and their coefficients
  (`φ_w = .565`, `θ* = .580`, …), which need the unprinted structural model; (2.40) is proved under
  the explicit hypothesis that the constraints involve `i` only through forecasts a quarter
  earlier, verified for the IS block;
* convergence of the equilibrium paths as `λ_i → 0` (p. 591): the coefficient limits, the limiting
  criterion and a fixed-plan limit theorem are proved;
* the remark of p. 585 that the rule satisfies the generalised Taylor principle, as a separate
  inequality (determinacy is proved directly); pre-sample values in §3.1 are numbers, not random
  variables;
* Kalman filtering and Svensson–Woodford certainty equivalence beyond (3.32)–(3.35);
* the plotted curves of Figures 8.1–8.6, beyond the specific numbers listed above; and §4 apart
  from (4.1).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](OptimalPolicyRules/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated from the earlier projects) |
| [Expectations](OptimalPolicyRules/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; bounded adapted processes; forward series; the pull-out property |
| [ExpectationsFiniteTree](OptimalPolicyRules/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; coin-flip examples |
| [ForwardSolution](OptimalPolicyRules/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` (restated from the Chapter 2 and 3 projects); sunspot families; summation by parts |
| [QuadraticRoots](OptimalPolicyRules/QuadraticRoots.lean) | 15 | The roots of `βλ² − (1 + β + c)λ + 1` (restated from the Chapter 3 project) |
| [ExpectationTools](OptimalPolicyRules/ExpectationTools.lean) | 32 | Faithful expectations; complexified expectations; the complex forward inverse |
| [GeneralSetup](OptimalPolicyRules/GeneralSetup.lean) | 14 | §§1.1–1.3: the LQ problem (1.1)–(1.4), timeless and robust optimality, rules (1.13)–(1.14), the Sargent–Wallace property |
| [GeneralFOC](OptimalPolicyRules/GeneralFOC.lean) | 48 | §§1.1, 1.4: the Lagrangian (1.7)–(1.9), Lagrangian sufficiency, Assumption 8.1, (1.10)–(1.12), fn 8, the p. 552 selection, (1.18)–(1.19) |
| [Adjugate](OptimalPolicyRules/Adjugate.lean) | 23 | §1.4: (1.22), fn 16, the corrected degrees of `α(L)` and `B(L)` |
| [TargetCriterion](OptimalPolicyRules/TargetCriterion.lean) | 53 | §§1.4–1.5, App. G.2: (1.23), Props 8.1–8.4 conditional, Assumptions 8.5–8.6, (1.28)–(1.31), p. 558 |
| [InflTargetInertia](OptimalPolicyRules/InflTargetInertia.lean) | 67 | §2.1: (2.1)–(2.10), the workhorse, robust optimality of (2.5), (2.9), (2.10) |
| [InflTargetStickyWages](OptimalPolicyRules/InflTargetStickyWages.lean) | 117 | §2.2: (2.11)–(2.22), the flexible-wage limit, the corrected (2.20) and its exact determinacy region |
| [InflTargetHabit](OptimalPolicyRules/InflTargetHabit.lean) | 20 | §2.3: (2.23)–(2.27) |
| [InflTargetPredetermined](OptimalPolicyRules/InflTargetPredetermined.lean) | 54 | §2.4: (2.28)–(2.34) |
| [GWModel](OptimalPolicyRules/GWModel.lean) | 35 | §2.5: (2.35)–(2.45) and the p. 574 numbers |
| [Reflections](OptimalPolicyRules/Reflections.lean) | 6 | §4.1: the reaction function (4.1) |
| [CubicRoots](OptimalPolicyRules/CubicRoots.lean) | 111 | §3.2, App. G.3, G.6: `A(z)`, Proposition 8.7, Lemmas G.1–G.2, the discriminant, `γ̄` |
| [InflationInertiaRules](OptimalPolicyRules/InflationInertiaRules.lean) | 98 | §3.2, App. G.7: (3.14)–(3.24), Proposition 8.8, the determinacy of p. 593 |
| [IRuleBasic](OptimalPolicyRules/IRuleBasic.lean) | 122 | §3.1, App. G.4: (3.1)–(3.9), Proposition 8.5, fn 35, the p. 586 numbers |
| [IRuleForwardIntegrated](OptimalPolicyRules/IRuleForwardIntegrated.lean) | 38 | §3.1, App. G.5: (3.10)–(3.13), Proposition 8.6, the pp. 590–591 numbers |
| [IRulePredetermined](OptimalPolicyRules/IRulePredetermined.lean) | 11 | §3.3: (3.28)–(3.31) |
| [ImperfectInfo](OptimalPolicyRules/ImperfectInfo.lean) | 9 | §3.4: (3.32)–(3.35) |
| [InflationInertiaRepresentations](OptimalPolicyRules/InflationInertiaRepresentations.lean) | 140 | §3.2, App. G.8–G.10: Propositions 8.9–8.11, Lemma G.2, Figures 8.3–8.5 |
| [Links](OptimalPolicyRules/Links.lean) | 59 | Proofs that the different formalisations of the same book objects agree |

## Modelling conventions

* **Expectations.** Random variables are `Ω → ℝ` and processes `ℕ → Ω → ℝ`. Every model equation
  holds at every date as an equality of functions, for an arbitrary `ExpectationSystem` (linear,
  constant-preserving, monotone, with the law of iterated expectations). Perfect foresight
  (`perfectForesight`) and every finite event tree
  (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) are instances; the robust-optimality
  theorems of §2 have finite-tree corollaries (`InflTargetInertia.baseline_robustlyOptimal_finiteTree`,
  `InflTargetStickyWages.sym_robustlyOptimal_finiteTree`). Complex roots are handled by the complexified
  expectation `ExpectationTools.EC`. Shifted and delayed information sets are themselves
  expectation systems (`InflTargetPredetermined.shift`, `IRulePredetermined.delay`).
* **Bounded adapted processes.** Plans, multipliers and disturbances are bounded and adapted;
  pre-sample values (`x_{t₀−1}`, `π_{t₀−1}`, `i_{t₀−1}`, the multiplier history) are bounded and
  known at `t₀`. Uniqueness is uniqueness among bounded adapted processes.
* **Explicit hypotheses.** The optimality theorems take the pull-out property
  (`ExpectationSystem.PullOut`, true for perfect foresight and every finite tree) as a hypothesis.
  Exact uniqueness of an optimum takes faithfulness of the conditional expectation
  (`ExpectationTools.Faithful`, true for perfect foresight); without it the optimum is unique in
  conditional mean square (`InflTargetPredetermined.welfare_eq_imp`). Parameter restrictions the
  book leaves implicit (`0 < β < 1`, `κ, σ, λ > 0`, `0 ≤ γ ≤ 1`, `0 ≤ δ < 1`) are hypotheses.
* **Deferred and supplied results as hypotheses.** Proposition 8.1's conclusion is the structure
  `TargetCriterion.Prop81.Prop81Conclusion`. Proposition 8.7's conclusions enter Propositions
  8.9–8.11 as the structure `InflationInertiaRepresentations.InertiaRoots`, which
  `Links.inertiaRoots_of_standing` discharges, so the Links versions are unconditional.
* **Timeless and robust optimality** are given a precise definition in each setting
  (`GeneralSetup.LQProblem.TimelesslyOptimalPlan`, `GeneralSetup.RobustlyOptimal`,
  `InflTargetInertia.TimelessOptimal`, `InflTargetInertia.RobustlyOptimal`,
  `InflTargetStickyWages.TimelessOptimalSW`, `InflTargetHabit.TimelessOptimalH`,
  `InflTargetPredetermined.TimelesslyOptimal`, `IRuleBasic.OptimalGiven`,
  `InflationInertiaRules.TimelesslyOptimal`) and proved.

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
