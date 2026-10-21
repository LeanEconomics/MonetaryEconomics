# Gains from commitment in Lean

This is the `Woodford/GainsFromCommitment/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Woodford (2003), *Interest and Prices*, Chapter 7, "Gains from
Commitment to a Policy Rule" (pp. 464–533), together with the proofs in Appendix F
(pp. 709–715). Model equations hold for an arbitrary expectation operator, so every result covers
perfect foresight and genuine uncertainty. Losses are genuine infinite discounted sums over
bounded plans, and every optimality claim is proved as optimality: a feasible plan satisfying the
first-order conditions minimises the expected loss over all bounded feasible plans (Lagrangian
sufficiency), with uniqueness from strict convexity. "Unique equilibrium" means unique among
bounded adapted processes. The library contains **946 theorems**, including the shared core.

Every proposition is stated for the exact linear-quadratic problem. The book's qualifiers "up to an
error of order `O(‖·‖²)`" belong to the second-order welfare approximation of Chapter 6 (the
`StabilizationWelfare` project) and are recorded only in docstrings.

Headline results, in the namespace `Woodford.GainsFromCommitment`:
* **The workhorse and Lagrangian sufficiency.** `βE_t y_{t+1} − (1 + β + c)y_t + y_{t−1} = f_t`
  has, for `β, c > 0` and bounded adapted forcing, exactly one bounded adapted solution
  `y_t = μ₁y_{t−1} − β⁻¹∑μ₂^{−j−1}E_t f_{t+j}` (`SecondOrderRE.bounded_solution_unique`,
  `SecondOrderRE.solution_formula`); first-order conditions plus feasibility imply optimality
  for a general discounted LQ problem with lags, leads and an initial commitment
  (`LQSufficiency.expLoss_sub_hasSum`, `LQSufficiency.isOptimalAmong_of_foc`).
* **The inflationary bias.** Proposition 7.1 with uniqueness among all bounded adapted
  sequences of period optima, not only Markov ones (`InflationBias.prop_7_1`,
  `InflationBias.discretion_unique`); the date-zero plan (1.12)–(1.13) is the unique optimum and
  is time-inconsistent (`DateZeroCommitment.dateZero_optimal`,
  `DateZeroCommitment.time_inconsistent`); a precise definition of timeless optimality and
  Proposition 7.2 with the sufficiency and uniqueness the book leaves out (`Timeless.prop_7_2`,
  `Timeless.prop_7_2_everyDate`); the zero bound on the date-zero path needs `λσ ≥ κ` or a small
  `x*` (`Timeless.dateZero_rate_nonneg_iff`, `Timeless.dateZero_rate_counterexample`).
* **Monetary frictions and indexation.** Proposition 7.3 as an equivalence, deterministic and
  under uncertainty, and (1.20) with real-balance effects (`MonetaryFrictions.prop_7_3`,
  `MonetaryFrictions.prop_7_3_uncertainty`, `MonetaryFrictions.eq_1_20`); Proposition 7.4 by a
  change of variables that is bounded only for `γ < 1` (`Indexation.prop_7_4`,
  `Indexation.not_bdd_unqd_one`); the generalised first-order condition of p. 483 corrected
  (`Indexation.hasDerivAt_lagrI_pi`, `Indexation.printed_foc_not_derivative`).
* **Cost-push shocks.** Proposition 7.5 (`Discretion.prop_7_5`); Propositions 7.6–7.8 on
  integer dates, so that the forecasts `E_{t₀−k}u` of (2.9) exist, with (2.9) the only bounded
  self-consistent specification (`CostPushCommitment.prop_7_6`, `CostPushCommitment.prop_7_7`,
  `CostPushCommitment.prop_7_8`, `CostPushCommitment.selfConsistent_iff`); Propositions 7.9–7.10
  with their missing hypothesis `E_t u_T → 0` supplied, shown necessary, and the impulse responses
  (2.16)–(2.17) corrected (`ImpulseResponses.prop_7_9_limits_iff`,
  `ImpulseResponses.tendsto_E_p_iff`, `ImpulseResponses.rev_pi`, `ImpulseResponses.rev_x`);
  the variance frontier (2.22) (`VarianceFrontier.opt_frontier`).
* **Natural-rate disturbances.** The zero-gap policy is optimal under commitment and discretion
  (`NaturalRateCommitment.zero_gap_optimal`), and with an interest-rate term and `κ = 0` the
  partial-adjustment rule (2.29) with (2.30) corrected is optimal
  (`NaturalRateCommitment.eq228_iff_229`, `NaturalRateCommitment.not_printed_230`,
  `NaturalRateCommitment.optimal_plan_kappa0`).
* **Simple rules.** Proposition 7.11 (`Noninertial.prop_7_11`); the F.4 response coefficients
  confirmed and its long-run values corrected (`Noninertial.f4_u_optimal`,
  `Noninertial.f4_corrected`); Proposition 7.12 including the optimality of the Taylor rule among
  determinate Taylor rules and the open set of `(ρ_r, ρ_u)` of p. 515
  (`OptimalTaylor.prop_7_12_optimal`, `OptimalTaylor.prop_7_12_optimal_general`); the false
  claim `φ_π > 1` of p. 515 refuted (`OptimalTaylor.e9_counterexample`); Proposition 7.13
  (`OptimalTaylor.prop_7_13`, `OptimalTaylor.fn37`).
* **Instrument path and targeting rules.** Proposition 7.14 with (4.2) corrected and a continuum
  of stochastic sunspot equilibria under an exogenous rate path (`InstrumentPath.prop_7_14`,
  `InstrumentPath.p519_sunspot`); Propositions 7.15–7.17 with the identification with
  Proposition 7.7 filled in (`TargetingRule.prop_7_15`, `TargetingRule.foc_eq211_eq_star`,
  `TargetingRule.prop_7_16`, `Implementation.prop_7_17`); the indeterminacy of (5.4) proved for
  every `σλ < κ` (`Implementation.eq54_indeterminate`).
* **Cross-links.** The formalisations from different angles are proved to agree: the
  date-zero, timeless, impulse-response and instrument-path plans are all the optimal
  commitment equilibrium of §5 (`Links.dateZero_isT0Opt`, `Links.timeless_plan_eq_star`,
  `Links.impulsePlan_eq_star`, `Links.instrumentPath_isConstrainedOpt`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections: thirteen confirmed errors of the chapter survey
(E1–E13), among them the missing terms of the generalised first-order condition of p. 483 (E3),
the index and the missing factor `κ/λ` in the impulse responses (2.16)–(2.17) and the F.2
recursion (E4–E6), the missing hypothesis of Propositions 7.9–7.10 (E7), the weights of (2.30)
(E8), the false claim `φ_π > 1` of p. 515 (E9), the calibration behind footnote 32 (E10), the
long-run values of App. F.4 (E11), the summation range of (4.2) (E12) and the sign of the
output-gap forecast of p. 528 (E13); the unqualified zero-bound claim of p. 469; and a misprint
in App. F.6.

Not formalised:
* the `O(‖·‖²)` approximation qualifiers of Propositions 7.1–7.5 and 7.15, which belong to the
  Chapter 6 welfare approximation; `λ = κ/θ` (Chapter 6) is a hypothesis where used;
* least-squares learnability and E-stability (pp. 519, 528, 532–533; Evans and Honkapohja,
  Preston), which concern adaptive learning, not rational-expectations equilibria;
* Taylor rules with negative feedback coefficients (fn 33): Proposition 7.12 is stated for
  `φ_π, φ_x ≥ 0`; and the "almost all parameter values" remark of p. 515 beyond the open-set
  statement;
* an exact determinacy criterion for forecast-based rules with horizon `k ≥ 2` in
  Proposition 7.13: indeterminacy is proved beyond an explicit critical horizon, the exact
  criterion only for `k = 1`;
* an expectation system carrying infinitely many nondegenerate innovations: the variance
  results ((3.4), (3.7)–(3.8), Proposition 7.11's `L_stab` form, F.4's `L_stab` optimality) assume
  AR(1) innovations with constant conditional variance and the pull-out property, which hold for
  genuine probability models, but no such instance is built (finite trees cannot carry one;
  `VarianceFrontier.coin_AR1Innov` shows a time-varying-variance version is satisfiable);
* the ℤ→ℕ translation of whole plans between the integer-dated Propositions 7.6–7.8 and the
  `ℕ`-dated equilibrium of §5 (only the AS relation is linked), and a common `L_stab` ranking of
  the inertial commitment plan against the optimal noninertial plan;
* uniqueness of the `κ = 0` natural-rate optimum (2.29) under a general expectation system (only
  optimality; zero-gap uniqueness is proved for faithful systems), the `κ > 0` natural-rate
  dynamics behind Figure 7.6, and the general system (1.16)–(1.18) under natural-rate shocks;
  "I(1)" and "I(2)" on p. 501 are formalised as root multiplicities at `z = 1`;
* necessity in the p. 484 steady state with indexation and frictions (only that it is the unique
  steady state consistent with the first-order conditions, and optimal);
* composite disturbances (4.3) with infinitely many shock types;
* the numerical Figures 7.1–7.6, the calibrated rates −0.4% and −0.2% a year (fn 13), and the
  discretionary and date-zero paths under indexation discussed with Figure 7.2; for Figure 7.1
  only the ordering of the three inflation paths is formalised.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](GainsFromCommitment/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated from the earlier projects) |
| [Expectations](GainsFromCommitment/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; bounded adapted processes; forward series; the pull-out property |
| [ExpectationsFiniteTree](GainsFromCommitment/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; coin-flip examples |
| [ForwardSolution](GainsFromCommitment/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` (restated from the Chapter 2 and 3 projects); dominated series |
| [Sequences](GainsFromCommitment/Sequences.lean) | 20 | Lags with a pre-sample value, bounded sequences, discounted sums and telescoping |
| [SecondOrderRE](GainsFromCommitment/SecondOrderRE.lean) | 51 | (1.10)–(1.12), (2.7), (F.10): the roots of (1.11) and the second-order workhorse, from any start date |
| [LQSufficiency](GainsFromCommitment/LQSufficiency.lean) | 16 | Lagrangian sufficiency for discounted LQ problems with lags, expected leads and an initial multiplier |
| [InflationBias](GainsFromCommitment/InflationBias.lean) | 10 | §1.1: (1.3)–(1.6) and Proposition 7.1 |
| [DateZeroCommitment](GainsFromCommitment/DateZeroCommitment.lean) | 35 | §1.1: the Lagrangian, (1.7)–(1.13), optimality of the date-zero plan, the p. 473 identity, time inconsistency |
| [Timeless](GainsFromCommitment/Timeless.lean) | 24 | §1.1: timeless optimality, Proposition 7.2, Figure 7.1, the zero bound of p. 469 |
| [MonetaryFrictions](GainsFromCommitment/MonetaryFrictions.lean) | 73 | §1.2: (1.14)–(1.20), Lagrangian sufficiency with three constraints, Proposition 7.3, real-balance effects |
| [Indexation](GainsFromCommitment/Indexation.lean) | 43 | §1.2: (1.21)–(1.23), Proposition 7.4, indexation with frictions and the corrected first-order condition |
| [Discretion](GainsFromCommitment/Discretion.lean) | 25 | §2.1: (2.2)–(2.3) and Proposition 7.5 |
| [CostPushCommitment](GainsFromCommitment/CostPushCommitment.lean) | 99 | §2.1, App. F.1: integer-dated expectations, (2.4)–(2.15), Propositions 7.6–7.8 |
| [ImpulseResponses](GainsFromCommitment/ImpulseResponses.lean) | 68 | §2.1, App. F.2–F.3: Propositions 7.9–7.10 corrected, (2.16)–(2.17), p. 501 and fn 22 |
| [VarianceFrontier](GainsFromCommitment/VarianceFrontier.lean) | 33 | §2.1, §3: conditional variances, `L_det + L_stab`, (2.18)–(2.22), (3.2)–(3.4), (3.6)–(3.8) |
| [NaturalRateCommitment](GainsFromCommitment/NaturalRateCommitment.lean) | 29 | §2.2: the zero-gap policy, (2.23)–(2.30) with `κ = 0`, optimality of (2.29) |
| [Noninertial](GainsFromCommitment/Noninertial.lean) | 59 | §3, App. F.4: (3.1), p. 508, (3.5), Proposition 7.11, discretion compared, the F.4 coefficients |
| [OptimalTaylor](GainsFromCommitment/OptimalTaylor.lean) | 78 | §3: (3.9), Propositions 7.12–7.13, the interval of fn 32, forecast-based rules, fn 37 |
| [InstrumentPath](GainsFromCommitment/InstrumentPath.lean) | 31 | §4: (4.1)–(4.3), Proposition 7.14 corrected, sunspot equilibria under an exogenous path |
| [TargetingRule](GainsFromCommitment/TargetingRule.lean) | 64 | §5.1, App. F.5–F.6: (5.1)–(5.3), Propositions 7.15–7.16, the timeless perspective |
| [Implementation](GainsFromCommitment/Implementation.lean) | 40 | §5.2: private forecasts, the projection of p. 529, (5.4)–(5.5), Proposition 7.17, indeterminacy of (5.4) |
| [Links](GainsFromCommitment/Links.lean) | 40 | Proofs that the different formalisations of the same book objects agree |

## Modelling conventions

* **Expectations.** Random variables are `Ω → ℝ` and processes `ℕ → Ω → ℝ`. Every model equation
  holds at every date as an equality of functions, for an arbitrary
  `ExpectationSystem` (linear, constant-preserving, monotone, with the law of iterated
  expectations). Perfect foresight (`perfectForesight`) and every finite event tree
  (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) are instances. Propositions 7.6–7.8
  use an integer-dated system (`CostPushCommitment.ExpSysZ`), because (2.9) needs `E_{t₀−k}` for
  every `k ≥ 1`; any `ExpectationSystem` extends to one (`CostPushCommitment.ExpSysZ.ofNat`).
* **Bounded adapted processes.** Plans and disturbances are bounded and adapted; pre-sample
  values (`x_{t₀−1}`, `p_{t₀−1}`, `φ_{t₀−1}`, the shock history) are bounded and known at `t₀`.
  Uniqueness is uniqueness among bounded adapted processes.
* **Explicit hypotheses.** The optimality theorems take the pull-out property
  (`ExpectationSystem.PullOut`, true for perfect foresight and every finite tree) as a hypothesis.
  Exact uniqueness of an optimum takes faithfulness of `E_{t₀}` (`TargetingRule.Faithful`,
  `CostPushCommitment.ExpSysZ.Faithful`); without it the optimum is unique up to null events
  (`CostPushCommitment.optimal_unique_ae`). Parameter restrictions the book leaves implicit
  (`0 < β < 1`, `κ, λ, σ > 0`, nondegenerate shocks, `φ ≥ 0`) are hypotheses.
* **Timeless optimality** is given a precise definition in each setting
  (`Timeless.TimelesslyOptimal`, `MonetaryFrictions.TimelesslyOptimal`,
  `CostPushCommitment.TimelesslyOptimal`, `TargetingRule.TimelesslyOptimal`) and proved.

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
