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
among bounded adapted processes. The library contains **1679 theorems**, including the shared
core.

The general Giannoni–Woodford theory of §§1.4–1.5 (Propositions 8.1–8.4), which the book states
without proof, is proved in general, in corrected form where the printed statement fails (see
[Propositions 8.1–8.4 in general](#propositions-8184-in-general)). All the concrete results
(§§2–4, Propositions 8.5–8.11, Appendix G.2–G.10) are proved in full, and the general theory is
specialised to the basic and inflation-inertia models.

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

## Propositions 8.1–8.4 in general

Twenty-four modules (499 theorems, from `PencilSplit` to `GeneralTheoryLinks` in the library map)
prove the general theory of §§1.4–1.5 and Appendix G.1–G.2, which the book takes from Giannoni and
Woodford (2002a) without proof.

* **Proposition 8.1 from Assumptions 8.2–8.4**, through a real deflating pair `A J = Î J Ψ` of the
  pencil (1.15) (App. G.1), for any expectation system. Three corrections:
  * *Multipliers known at their date.* The statement needs `M_t` known at `t` (as p. 540 says) and
    adapted plans (`Prop81General.Prop81ConclusionM`, `Prop81General.prop81`,
    `PencilAssumptions.prop81_of_assumptions`). Without this it is false under uncertainty
    (`Prop81General.not_prop81Equiv_coin`); under perfect foresight the original holds
    (`Prop81General.prop81_perfectForesight`).
  * *Repeated roots.* The distinct-root clause of Assumption 8.3 is replaced by selecting whole
    root classes, through generalised eigenspaces (`PencilRepeated.SelWhole`,
    `PencilRepeated.prop81_of_assumptions_general`).
  * *Case (ii) of Assumption 8.2* (one unpaired complex root). The book's Assumption 8.4(ii)
    depends on how the eigenvector is scaled (`Prop81Unique.re_det_rescale_zero`,
    `CaseIIInstance.book_condition_depends_on_scaling`). It is replaced by a normalisation-free
    condition (`CaseIIBasis.Assumption84II`, basis-invariant by `CaseIIBasis.basis_invariance`),
    under which Proposition 8.1 holds (`CaseIIBasis.prop81_caseII`). An explicit system shows the
    condition is not vacuous (`CaseIIInstance.ex82`, `CaseIIInstance.ex84`,
    `CaseIIInstance.ex_prop81`).

  The uniqueness remark of p. 553 holds when no root lies on `|μ| = β⁻¹`
  (`Prop81Unique.remark_p553`), and `deg α = rank Λ = rank Ẽ` (E18) under the assumptions
  (`PencilAssumptions.natDegree_alpha_eq_rank`).
* **Proposition 8.2 without the stability hypothesis**, and with Assumption 8.1 corrected.
  * `TargetCriterion.Recursion.MultStable` fails whenever Assumption 8.7 holds
    (`PencilAssumptions.not_multStable_of_unselected`). Assumption 8.5 is what keeps the
    multipliers bounded (`Prop82General.KrylovBound.boundedV_of_krylov`).
  * The earlier formalisation of Assumption 8.1 cannot hold under uncertainty
    (`NKAssumption81.not_assumption81_coin`). The corrected one takes a bounded initial
    multiplier known at `t₀ − 1` (`Prop82General.Assumption81M`).
  * Proved: existence, uniqueness, optimality subject to (1.27), and the time-invariant multiplier
    rule (1.17) (`Prop82General.Prop82M.prop82M_determinate`,
    `Prop82General.Prop82M.prop82M_optimal`, `Prop82General.Prop82M.prop82M_multiplier_rule`);
    the `d = min(k, n_z − 1)` lags of (1.24) suffice (`MultiplierLags.rule_lags_lt`,
    `MultiplierLags.rule_lags_full`).
  * Robust optimality: `Prop82General.Prop82M.prop82M_robustlyOptimal`, and from the assumptions
    `PencilAssumptions.prop82_of_assumptions`, `PencilRepeated.prop82_of_assumptions_general`,
    `CaseIIBasis.prop82_caseII`.
* **Proposition 8.3 with the no-circle hypothesis.** For every representation of Proposition 8.1,
  `α(L)` has exactly `m` zeros inside the unit circle when no root of (1.15) has `|λ| = β⁻¹`
  (`Prop83.prop83`, `Prop83Links.prop83M`, `Prop83Links.prop83M_const`). Without that hypothesis
  only the bounds hold (`Prop83.prop83_bounds`), and the exact count fails
  (`Prop83.circle_counterexample`). Assumption 8.1 does not exclude roots on the circle
  (`Circle81.assumption81_not_exclude_circle`).
* **Proposition 8.4, unconditional.**
  * The bounded forward inverse exists and is unique exactly when every root is outside the unit
    circle (`Prop84General.forward_inverse_existsUnique`, `Prop84General.forward_inverse_iff`).
  * The factorisation `α = α₁α₂` (`Prop84General.alpha_factorization`).
  * (1.28) ⇔ (1.32) (`Prop84General.prop84`, `Prop84General.prop84_criterion`,
    `Prop83Links.prop84M`). Every hypothesis of the earlier conditional theorem is discharged
    (`GeneralTheoryLinks.Old.prop84_conditional_discharged`).
* **Worked instance: the basic model (§3.1).**
  * Assumptions 8.1–8.5 hold (`NKAssumption81.NK.nk_assumption81M`,
    `GeneralTheoryLinks.NK.nk_assumption82`, `GeneralLinks.nk_assumption83`,
    `GeneralTheoryLinks.NK.nk_assumption84`, `GeneralTheoryLinks.NK.nk_assumption85`).
  * Propositions 8.1 and 8.3 are fully unconditional (`GeneralTheoryLinks.NK.nk_prop81_prop83`).
  * Proposition 8.2 needs only pull-out (`GeneralTheoryLinks.NK.nk_prop82`).
  * The general criterion is the rule (3.7) (`GeneralLinks.nk_crit_iff_rule`), and Propositions
    8.5 (superinertia) and 8.6 follow from the general theory (`GeneralLinks.nk_zerosInside`,
    `GeneralLinks.prop_8_6_from_general`).
* **Worked instance: the inflation-inertia model (§3.2).**
  * Propositions 8.1 and 8.3 hold at every admissible calibration
    (`GeneralTheoryLinks.Inertia.in_props_81_83_all`). This covers the complex case, through the
    corrected Assumption 8.4(ii) (`InertiaProp8182.in_assumption84II`,
    `InertiaProp8182.in_prop81_complex`), and the double root, where Assumption 8.3 fails
    (`GeneralTheoryLinks.Inertia.in_double_props_81_83`).
  * Rules I and II are exactly the general criterion (1.23) for the two deflating splits
    (`InertiaCriterion.crit_iff_ruleI`, `InertiaCriterion.crit_iff_ruleII`).
  * Rule III is not of the form (1.28) for any deflating split (`InertiaSplit.split_classify`,
    `InertiaSplit.split_not_ruleIII`). It is compatible with the homogeneous content of
    Proposition 8.1 (`InertiaRuleIII.ruleIII_homEquiv`).
  * Proposition 8.2 holds in the real case, given the corrected Assumption 8.1
    (`InertiaProp8182.in_prop82_real`).
  * Proposition 8.9's `ρ₁ > 1` and Proposition 8.10 follow from the general theory
    (`InertiaSplit.prop_8_9_rho1_from_general`, `InertiaProp810.prop_8_10_via_prop84`).

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
* the Fig. 8.4 ratio `.39` confirmed by the enclosure `(.386, .389)`;
* in the general theory: Proposition 8.3 needs no root of (1.15) on `|λ| = β⁻¹`, and so does the
  remark of p. 553; Assumption 8.4(ii) is normalisation-dependent in case (ii) and is replaced;
  Assumption 8.3 is sufficient but not necessary; the `MultStable` hypothesis is unnecessary.
  Separately, two hypothesis structures of the earlier formalisation (the original Proposition
  8.1 conclusion and Assumption 8.1) were found unsatisfiable under uncertainty and corrected;
  these are formalisation errors, not the book's.

Not formalised:
* in the general theory:
  * Assumption 8.1 for the inflation-inertia model, so its Proposition 8.2
    (`InertiaProp8182.in_prop82_real`) keeps the corrected assumption as a hypothesis. It would
    need a third-order Blanchard–Kahn theorem with two initial conditions;
  * Proposition 8.2 for the inflation-inertia model in its complex case, which needs Assumption
    8.5 for the `Λ` of the case-(ii) construction;
  * Rule III at the full stochastic level. Only the homogeneous level (`Prop83.HomEquiv`), which is
    all Proposition 8.3 uses, is proved;
  * the claim of Proposition 8.2 that the equilibrium has the linear form (1.5) in `(Z̄_t, s_t)`.
    This needs a finite-dimensional exogenous state and a time-invariant expectation system,
    neither of which is in the framework;
  * repeated roots when the selection takes only part of a root class (`PencilRepeated.SelWhole`
    fails);
  * ∃ ⇒ ∀ for `CaseIIBasis.Assumption84II` when the zero root is not semisimple. It is proved when
    the zero root is semisimple (`CaseIIBasis.all_of_ex_semisimple`);
  * uniqueness of `Λ` and `Υ` in the remark of p. 553 when a root lies on `|μ| = β⁻¹`. Only the
    failure of existence is shown (`Prop81Unique.circle_counterexample`);
  * a counterexample to Proposition 8.3 that satisfies the full Assumption 8.1. The circle
    counterexample is at the level of `Prop83.HomEquiv`;
  * Proposition 8.2 for the case-(ii) example system (`CaseIIInstance.exProblem`), whose
    Assumptions 8.1 and 8.5 are not checked;
* in §1: a general "exactly half" root count for fn 8, and the exogenous-instrument determinacy
  claim of p. 546;
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
| [PencilSplit](OptimalPolicyRules/PencilSplit.lean) | 27 | App. G.1: vector forward solutions (Gelfand decay), the deflating pair `A J = Î J Ψ` (`DeflatingSplit`), the matrices `Λ`, `Υ`, `K` of (1.20)–(1.21) |
| [Prop81General](OptimalPolicyRules/Prop81General.lean) | 17 | Prop 8.1 from any deflating split, corrected so multipliers are known at their date (`Prop81ConclusionM`); the original fails under uncertainty (coin-flip counterexample); rank `Λ` = rank `Ẽ` |
| [Prop82General](OptimalPolicyRules/Prop82General.lean) | 18 | Prop 8.2 without `MultStable`: Assumption 8.5 bounds the multipliers; the multiplier rule (1.17); robust optimality; the corrected Assumption 8.1 (`Assumption81M`) |
| [PencilEigen](OptimalPolicyRules/PencilEigen.lean) | 31 | Assumptions 8.2 and 8.3 as stated; a real deflating pair from eigenvectors, (G.1)–(G.4); the kernel clauses of Assumption 8.3 always hold |
| [PencilAssumptions](OptimalPolicyRules/PencilAssumptions.lean) | 24 | Assumptions 8.4–8.5, (G.6)–(G.7); Props 8.1 and 8.2 from Assumptions 8.1–8.5; `deg α = rank Λ = rank Ẽ` (E18); `MultStable` fails under Assumption 8.7 |
| [Prop81Unique](OptimalPolicyRules/Prop81Unique.lean) | 17 | The remark of p. 553 (unique `Λ`, `Υ`, `Q`, `R` and multipliers) with no root on the circle, and its counterexample; no real split carries an unpaired complex root |
| [PencilRepeated](OptimalPolicyRules/PencilRepeated.lean) | 33 | Prop 8.1 and 8.2 with repeated roots: generalised eigenspaces of the shifted pencil and real descent, for selections of whole root classes |
| [Prop81CaseII](OptimalPolicyRules/Prop81CaseII.lean) | 14 | Props 8.1 and 8.2 in case (ii) of Assumption 8.2 (`QuasiSplit`, residual root `h`), under the basis-universal Assumption 8.4(ii) |
| [MultiplierLags](OptimalPolicyRules/MultiplierLags.lean) | 6 | (1.24): `d = min(k, n_z − 1)` lags of `q` suffice for the multiplier rule; the role of the first part of Assumption 8.5 |
| [CaseIIBasis](OptimalPolicyRules/CaseIIBasis.lean) | 19 | The corrected Assumption 8.4(ii) is basis-invariant; the existential form, ∃ ⇔ ∀ when the zero root is semisimple; Props 8.1 and 8.2 in case (ii) |
| [CaseIIInstance](OptimalPolicyRules/CaseIIInstance.lean) | 20 | Case (ii) with `n_Z = 1`: the residual root as a function of the eigenvector's scaling, the book's normalisation, and a system satisfying Assumptions 8.2(ii) and 8.4(ii) |
| [Prop83](OptimalPolicyRules/Prop83.lean) | 56 | Prop 8.3 for every representation, with no root on `\|λ\| = β⁻¹`; the bounds without it; the Jordan-block counterexample; nonempty sample space needed |
| [Prop84General](OptimalPolicyRules/Prop84General.lean) | 21 | Prop 8.4 unconditional: the bounded forward inverse (exact root condition), the factorisation `α = α₁α₂`, (1.28) ⇔ (1.32) from any date |
| [GeneralLinks](OptimalPolicyRules/GeneralLinks.lean) | 31 | The basic model (§3.1) as a general problem: (1.1), (1.9), `Λ`, `α`, the criterion is the rule (3.7); Props 8.5 and 8.6 from the general theory |
| [GeneralLinksInertia](OptimalPolicyRules/GeneralLinksInertia.lean) | 11 | The inflation-inertia model (§3.2) as a general problem: (1.1), (1.9); Prop 8.10 from the (1.30) ⇔ (1.31) lemma |
| [Prop83Links](OptimalPolicyRules/Prop83Links.lean) | 7 | Props 8.3 and 8.4 for the corrected representation of Prop 8.1; Prop 8.3 without Assumption 8.1 |
| [Circle81](OptimalPolicyRules/Circle81.lean) | 5 | Assumption 8.1 does not exclude roots of (1.15) on `\|μ\| = β⁻¹` |
| [InertiaSplit](OptimalPolicyRules/InertiaSplit.lean) | 54 | The inflation-inertia model: its pencil, every deflating split classified, Prop 8.3 for every representation, Rule III not a split's rule, Prop 8.9's `ρ₁ > 1` |
| [InertiaProp810](OptimalPolicyRules/InertiaProp810.lean) | 5 | Prop 8.10 from the general Prop 8.4 (real case) |
| [InertiaCriterion](OptimalPolicyRules/InertiaCriterion.lean) | 13 | The general criterion (1.23) of the inflation-inertia model is Rule I or Rule II |
| [InertiaRuleIII](OptimalPolicyRules/InertiaRuleIII.lean) | 5 | `Λ` is not pinned down by the homogeneous content of Prop 8.1; Rule III is compatible with it |
| [NKAssumption81](OptimalPolicyRules/NKAssumption81.lean) | 23 | Assumption 8.1 for the basic model (corrected form, any expectation system); the original formalisation fails under uncertainty |
| [InertiaProp8182](OptimalPolicyRules/InertiaProp8182.lean) | 13 | The inflation-inertia model: Assumption 8.5, Prop 8.2 in the real case, Assumptions 8.2(ii) and 8.4(ii) and Prop 8.1 in the complex case |
| [GeneralTheoryLinks](OptimalPolicyRules/GeneralTheoryLinks.lean) | 29 | Links: the bounded-orbit subspace; Props 8.1–8.3 at the double root and at every calibration of the inflation-inertia model; Assumptions 8.2–8.5 and Props 8.1–8.3 for the basic model; old vs corrected structures |

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
* **Supplied results as hypotheses.** The chapter's derivations from Proposition 8.1 take its
  conclusion as the structure `TargetCriterion.Prop81.Prop81Conclusion`. The general theory proves
  the corrected structure `Prop81General.Prop81ConclusionM`, and the original implies it
  (`GeneralTheoryLinks.Old.conclusionM_of_conclusion`). Proposition 8.7's conclusions enter
  Propositions 8.9–8.11 as the structure `InflationInertiaRepresentations.InertiaRoots`, which
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
