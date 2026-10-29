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
bounded adapted processes. The variance results of §3 and Appendix F.4 are also proved with
Mathlib's conditional expectation on a genuine probability space, almost surely. The library
contains **1623 theorems**, including the shared core.

Every proposition is stated for the exact linear-quadratic problem. The book's qualifiers "up to an
error of order `O(‖·‖²)`" come from the second-order welfare approximation of Chapter 6 (the
`StabilizationWelfare` project). Propositions 7.1–7.5 and 7.15 are also proved as statements about
actual welfare to third order, with `λ = κ/θ` derived rather than assumed. These proofs run on a
restated copy of the Chapter 6 machinery (`TidyR6WelfBase`, `TidyR6WelfBridge`,
`TidyR6WelfFrictions`).

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
  (`Indexation.hasDerivAt_lagrI_pi`, `Indexation.printed_foc_not_derivative`); the p. 484 steady
  state with indexation and frictions is necessary as well as sufficient for timeless optimality
  of a constant plan, with no multiplier assumed (`TidyR5IndexationNecessity.ss_ind_necessary`,
  `TidyR5IndexationNecessity.ss_ind_timeless_iff`).
* **Actual welfare up to `O(‖·‖²)`.** Along a one-parameter family of Calvo economies the
  discounted actual utility is `TIP − (ε²/2)Ȳu_c·2Θ·L + O(ε³)` with one constant for all dates and
  states, where `L` is the loss of the first-order plan and its weight `λ = κ/θ` is derived from
  the expansion, not assumed; the same holds for `E₀`-expected welfare
  (`TidyR6WelfCalvo.calvo_bridge_unif`, `TidyR6WelfCalvo.CalvoFamily.bridge`,
  `TidyR6WelfCalvo.SCalvoFamily.bridge`, `TidyR6WelfCalvo.lamW_eq`), and with transactions
  frictions, where `λ_x = κ/θ` and `λ_i` are derived too (`TidyR6WelfProp73.frictions_bridge`). A
  lower first-order loss means at least as good up to `O(ε³)` and strictly better for every small
  `ε ≠ 0`, and conversely (`TidyR6WelfCalvo.weaklyBetter_of_loss_le`,
  `TidyR6WelfCalvo.eventually_lt_of_loss_lt`, `TidyR6WelfCalvo.loss_le_of_weaklyBetter`). So
  Propositions 7.1–7.5 and 7.15 hold as statements about actual welfare, each with a converse
  (`TidyR6WelfProps.prop_7_1_welfare`, `TidyR6WelfProps.prop_7_1_welfare_converse`,
  `TidyR6WelfProps.prop_7_2_welfare`, `TidyR6WelfProps.prop_7_2_welfare_unique`,
  `TidyR6WelfProp73.prop_7_3_welfare`, `TidyR6WelfProp73.prop_7_3_welfare_converse`,
  `TidyR6WelfProps.prop_7_4_welfare`, `TidyR6WelfProps.prop_7_4_welfare_converse`,
  `TidyR6WelfPropsS.prop_7_5_welfare`, `TidyR6WelfPropsS.prop_7_5_welfare_converse`,
  `TidyR6WelfPropsS.prop_7_15_welfare`, `TidyR6WelfPropsS.prop_7_15_welfare_converse`).
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
  `NaturalRateCommitment.optimal_plan_kappa0`), unique when `E_{t₀}` is faithful and not unique
  for a general expectation system (`TidyR5NaturalRateKappa.kappa0_unique_faithful`,
  `TidyR5NaturalRateKappa.kappa0_not_unique`). With `κ > 0` the general system (2.1), (2.23),
  (1.16)–(1.18) has exactly one bounded adapted solution for every bounded adapted `rⁿ`, `u` and
  initial multipliers; it is the `t₀`-optimal and the timelessly optimal commitment, and its
  multipliers follow the partial-adjustment law `Φ_t = XΦ_{t−1} + ψ_t` with `X` Schur-stable and
  `det X > 0` (`TidyR5NaturalRateKappa.foc_system_existsUnique`,
  `TidyR5NaturalRateKappa.t0_optimal`, `TidyR5NaturalRateKappa.timeless_optimal`,
  `TidyR5NaturalRateKappa.partial_adjustment`).
* **Simple rules.** Proposition 7.11 (`Noninertial.prop_7_11`); the F.4 response coefficients
  confirmed and its long-run values corrected (`Noninertial.f4_u_optimal`,
  `Noninertial.f4_corrected`); Proposition 7.12 including the optimality of the Taylor rule among
  determinate Taylor rules and the open set of `(ρ_r, ρ_u)` of p. 515
  (`OptimalTaylor.prop_7_12_optimal`, `OptimalTaylor.prop_7_12_optimal_general`); the false
  claim `φ_π > 1` of p. 515 refuted (`OptimalTaylor.e9_counterexample`); Proposition 7.13
  (`OptimalTaylor.prop_7_13`, `OptimalTaylor.fn37`). For Taylor rules with coefficients of any
  sign (fn 33): the exact determinacy region (`TidyR5TaylorRegion.taylor_determinate_iff_region`),
  no determinate rule beats the optimal noninertial plan
  (`TidyR5TaylorRegion.prop_7_12_optimal_region`), and the plan is implementable by a determinate
  rule iff the consistent coefficients lie in the region (`TidyR5TaylorRegion.oni_implementable_iff`),
  so (3.10) is sufficient but not necessary (`TidyR5TaylorRegion.negative_rule_implements`,
  `TidyR5TaylorRegion.no_rule_implements`); for `λ_i > 0` the singular set of `(ρ_r, ρ_u)` is
  closed and Lebesgue-null (`TidyR5TaylorRegion.detG_zero_null`). At every `(ρ_r, ρ_u)`,
  singular ones included, the plan is implementable iff some solution of the consistency system
  lies in the region (`TidyR6TaylorSingular.oni_implementable_iff_exists`); on the singular set
  this is an explicit rank and one-dimensional Fourier–Motzkin condition
  (`TidyR6TaylorSingular.oni_implementable_singular_iff`); and with `λ_i = 0`, or whenever
  `γ_r = ρ_rκσ`, the plan is the equilibrium of no Taylor rule at all
  (`TidyR6TaylorSingular.not_implementable_li_zero`,
  `TidyR6TaylorSingular.not_implementable_r_row_zero`). Proposition 7.13 exactly for
  every horizon `k ≥ 1`: determinate iff every root of `χ` has `|λ| > 1`
  (`TidyR5ForecastHorizon.forecast_determinate_iff`, `TidyR5ForecastHorizon.scalarDet_iff`).
* **Instrument path and targeting rules.** Proposition 7.14 with (4.2) corrected and a continuum
  of stochastic sunspot equilibria under an exogenous rate path (`InstrumentPath.prop_7_14`,
  `InstrumentPath.p519_sunspot`); Propositions 7.15–7.17 with the identification with
  Proposition 7.7 filled in (`TargetingRule.prop_7_15`, `TargetingRule.foc_eq211_eq_star`,
  `TargetingRule.prop_7_16`, `Implementation.prop_7_17`); the indeterminacy of (5.4) proved for
  every `σλ < κ` (`Implementation.eq54_indeterminate`); composite disturbances (4.3) with
  countably many shock types, for which (5.1) is still determinate and optimal
  (`TidyR5CompositeShocks.compositeInf_bdd`, `TidyR5CompositeShocks.targeting_rule_composite`).
* **Cross-links.** The formalisations from different angles are proved to agree: the
  date-zero, timeless, impulse-response and instrument-path plans are all the optimal
  commitment equilibrium of §5 (`Links.dateZero_isT0Opt`, `Links.timeless_plan_eq_star`,
  `Links.impulsePlan_eq_star`, `Links.instrumentPath_isConstrainedOpt`); the integer-dated
  plans of Propositions 7.6–7.8, re-indexed, are the §5 equilibrium, with feasibility, loss and
  optimality translated exactly (`TidyR5PlanTranslation.isOptimal_iff`,
  `TidyR5PlanTranslation.prop_7_6_eq_star`, `TidyR5PlanTranslation.prop_7_7_eq_star`,
  `TidyR5PlanTranslation.prop_7_8_eq_star`), and the inertial commitment plan has an `L_stab` no
  larger than any bounded feasible plan, the optimal noninertial plan included
  (`TidyR5PlanTranslation.inertial_lstab_gap`, `TidyR5PlanTranslation.prop_7_7_lstab_le_oni`).
* **Genuine probability models.** With `E_t` Mathlib's conditional expectation and conditional
  variances Mathlib's `Var[·; μ | 𝓕 t]`, the stabilization loss is almost surely (3.4) and
  `L_stab,r + L_stab,u` (3.7)–(3.8) (`NoninertialMeasure.lstab12_eq`,
  `NoninertialMeasure.lstab_eq`), and Proposition 7.11 and the F.4 optimality hold almost surely,
  with no pull-out or non-degeneracy hypothesis (`NoninertialMeasure.prop_7_11_lstab`,
  `NoninertialMeasure.f4_lstab`). The hypotheses are met by the i.i.d. economy under `ν^ℕ`, in
  which every history is null, including a two-coin economy with two independent disturbances
  (`NoninertialMeasureIID.iid_prop_7_11`, `NoninertialMeasureIID.iid2_f4_lstab`,
  `NoninertialMeasureIID.twoCoin_f4_lstab`). On a finite state space, and on every finite event
  tree, the innovation variance must be zero, so the core variance theorems have content only on
  such a model (`NoninertialMeasure.finite_innov_degenerate`,
  `NoninertialMeasure.tree_innov_degenerate`); on a finite fully supported space the measure
  hypotheses imply the core ones and the two losses agree (`NoninertialMeasure.prop_7_11_link`,
  `NoninertialMeasure.f4_link`, `NoninertialMeasure.lstab12_agree`). One null set, fixed before
  any plan is chosen, serves every plan for the regular (bilinear) version of `L_stab`
  (`TidyR5UniformNull.regLstab12_uniform`, `TidyR5UniformNull.prop_7_11_uniform`,
  `TidyR5UniformNull.f4_uniform`); the expected losses rank plans with no null set at all
  (`TidyR5UniformNull.prop_7_11_integral`, `TidyR5UniformNull.f4_integral`); but some choice of
  versions admits no uniform null set (`TidyR5UniformNull.versions_no_uniform_null`). The
  "independent" disturbances of p. 512 are genuinely independent processes in the two-coin
  economy, and F.4 follows from independence (`TidyR5Independence.twoCoin_indepDisturbances`,
  `TidyR5Independence.f4_lstab_indep`, `TidyR5Independence.twoCoin_f4_indep`). The orders of
  integration of p. 501 are genuine properties of stochastic processes (`Δᵈp` covariance
  stationary, no lower difference stationary; `TidyR6IntegrationOrder.IntegratedOfOrder`): on the
  i.i.d. coin economy with white-noise cost-push shocks the price level is `I(0)` and `I(1)` under
  optimal policy with `γ = 0` and `γ = 1`, and `I(1)` and `I(2)` under discretion
  (`TidyR6IntegrationPolicy.optimal_gamma0_I0`, `TidyR6IntegrationPolicy.optimal_gamma1_I1`,
  `TidyR6IntegrationPolicy.discretion_gamma0_I1`, `TidyR6IntegrationPolicy.discretion_gamma1_I2`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections: thirteen confirmed errors of the chapter survey
(E1–E13), among them the missing terms of the generalised first-order condition of p. 483 (E3),
the index and the missing factor `κ/λ` in the impulse responses (2.16)–(2.17) and the F.2
recursion (E4–E6), the missing hypothesis of Propositions 7.9–7.10 (E7), the weights of (2.30)
(E8), the false claim `φ_π > 1` of p. 515 (E9), the calibration behind footnote 32 (E10), the
long-run values of App. F.4 (E11), the summation range of (4.2) (E12) and the sign of the
output-gap forecast of p. 528 (E13); the unqualified zero-bound claim of p. 469; the claim of
p. 515 that the coefficients are determined for almost all parameters, which fails with `λ_i = 0`,
where no Taylor rule implements the optimal noninertial plan; and a misprint in App. F.6.

Not formalised:
* existence of the exact nonlinear equilibrium families behind the `O(‖·‖²)` statements: the
  welfare versions of Propositions 7.1–7.5 and 7.15 take the one-parameter families (the
  cross-section, the dispersion law with an `O(ε³)` remainder, the first-order components
  satisfying (1.1), (2.1) or (1.15)) as hypotheses, as Chapter 6 Layer B does, and the necessity
  directions are stated against an explicit comparator family; the existence of exact nonlinear
  equilibrium families implementing each plan (built in the Chapter 6 project's nonlinear
  modules) is not re-proved here;
* for Proposition 7.3 under actual welfare, the money-demand residual of order `O(ε²)`, the
  discounted dispersion identity with its initial term `T₀`, and `π̄ − π = O(ε²)` are hypotheses
  (as in the Chapter 6 `prop68_layerB`), not derived from a population of goods;
* the stochastic welfare results (Propositions 7.5 and 7.15) need every order bound uniform in the
  state, and their converses a faithful `E₀`; the cost-push shock is read as a markup or tax
  disturbance entering only the first-order aggregate-supply relation (Chapter 6 §4.5), not
  through the large-distortion loss of Proposition 6.15, whose weight differs from `κ/θ`;
* least-squares learnability and E-stability (pp. 519, 528, 532–533; Evans and Honkapohja,
  Preston), which concern adaptive learning, not rational-expectations equilibria;
* the orders of integration of p. 501 beyond the i.i.d. coin economy: they are proved for
  white-noise cost-push shocks, with the stationary initial multiplier for exact stationarity
  under optimal policy (the policy followed forever); AR(1) cost-push shocks and arbitrary
  initial multipliers, which give only asymptotic stationarity, are not treated;
* a single null set for arbitrary versions of `L_stab`: one null set uniform over all plans is
  proved for the regular (bilinear) version, and the expected losses need none, but some choice of
  versions admits no uniform null set (`TidyR5UniformNull.versions_no_uniform_null`); Mathlib's
  own `condExp` representative is chosen by `Classical.choice`, so neither statement can be
  proved for that specific function;
* uniqueness of the `κ = 0` natural-rate optimum (2.29) without faithfulness, which is false
  (`TidyR5NaturalRateKappa.kappa0_not_unique`; with faithfulness it is proved);
* the `κ > 0` dynamics of Figure 7.6 as numerical curves: existence, uniqueness, optimality and
  the partial-adjustment law are proved structurally, not the plotted paths;
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
| [ExpectationsMeasure](GainsFromCommitment/ExpectationsMeasure.lean) | 71 | Measure-theoretic expectations (shared core, copied from `ObservationalEquivalence`): `MeasExpectationSystem` with Mathlib's `condExp`, the axioms a.e., news, the forward equation and sunspots, AR(1) conditional variance, bridges to and from the core `ExpectationSystem` |
| [ExpectationsMeasureIID](GainsFromCommitment/ExpectationsMeasureIID.lean) | 37 | The genuine i.i.d. economy on `ℕ → ℝ` under `ν^ℕ` (shared core): independence, moments, every history null, determinacy iff `\|a\| < 1`, AR(1), the `±1` coin |
| [NoninertialMeasure](GainsFromCommitment/NoninertialMeasure.lean) | 43 | §3, App. F.4 with genuine conditional expectations: AR(1) disturbances, conditional variances of the plans, (3.2)–(3.8), Proposition 7.11 and F.4 optimality a.s.; finite spaces force zero innovation variance; links to the core statements |
| [NoninertialMeasureIID](GainsFromCommitment/NoninertialMeasureIID.lean) | 22 | The variance results on the i.i.d. economy: one disturbance, two disturbances driven by functions of the shock, the fair-coin and two-coin economies |
| [TidyR5TaylorRegion](GainsFromCommitment/TidyR5TaylorRegion.lean) | 34 | §3, fn 33, p. 515: the determinacy region for Taylor coefficients of any sign, Proposition 7.12 exactly for any sign, (3.10) sufficient but not necessary, the singular set Lebesgue-null for `λ_i > 0` |
| [TidyR5ForecastHorizon](GainsFromCommitment/TidyR5ForecastHorizon.lean) | 19 | §3, Proposition 7.13: scalar expectational equations of any order, determinate iff all roots lie outside the unit circle; the exact criterion for every horizon `k ≥ 1` |
| [TidyR5UniformNull](GainsFromCommitment/TidyR5UniformNull.lean) | 18 | §3, App. F.4: one null set for all plans (regular version), the expected-loss rankings with no null set, and versions with no uniform null set |
| [TidyR5Independence](GainsFromCommitment/TidyR5Independence.lean) | 14 | p. 512: genuinely independent innovations and disturbances; (3.7)–(3.8) and F.4 from independence; the two-coin economy is independent |
| [TidyR5PlanTranslation](GainsFromCommitment/TidyR5PlanTranslation.lean) | 18 | Propositions 7.6–7.8 re-indexed to `ℕ`: feasibility, loss and optimality agree with §5, the plans are the §5 equilibrium; the common `L_stab` ranking of the inertial plan |
| [TidyR5KappaPosCore](GainsFromCommitment/TidyR5KappaPosCore.lean) | 86 | The `κ > 0` multiplier system (restated from the Chapter 8 project): the palindromic quartic, the real solvent, the second-order Blanchard–Kahn theorem, Lagrangian sufficiency |
| [TidyR5NaturalRateKappa](GainsFromCommitment/TidyR5NaturalRateKappa.lean) | 19 | §2.2 with `κ > 0`: existence and uniqueness for (1.16)–(1.18), `t₀`- and timeless optimality, the partial-adjustment law; uniqueness of (2.29) at `κ = 0` decided |
| [TidyR5IndexationNecessity](GainsFromCommitment/TidyR5IndexationNecessity.lean) | 16 | §1.2, p. 484: necessity of the steady state with indexation and frictions, by an explicit feasible perturbation |
| [TidyR5CompositeShocks](GainsFromCommitment/TidyR5CompositeShocks.lean) | 10 | §4, (4.3): composite disturbances with countably many shock types; superposition; robust optimality of (5.1) |
| [TidyR6IntegrationOrder](GainsFromCommitment/TidyR6IntegrationOrder.lean) | 15 | p. 501: covariance stationarity and integration of order `d` on a probability space, invariant under a.e. equality; the moment calculus of linear coin processes |
| [TidyR6IntegrationPolicy](GainsFromCommitment/TidyR6IntegrationPolicy.lean) | 19 | p. 501, fn 22: the price level is `I(0)`, `I(1)` under optimal policy and `I(1)`, `I(2)` under discretion, on the i.i.d. coin economy |
| [TidyR6TaylorSingular](GainsFromCommitment/TidyR6TaylorSingular.lean) | 9 | §3, p. 515, fn 33: Proposition 7.12 for any sign at every `(ρ_r, ρ_u)`, the singular set exactly; no Taylor rule implements the plan when `λ_i = 0` |
| [TidyR6WelfBase](GainsFromCommitment/TidyR6WelfBase.lean) | 57 | Chapter 6 welfare machinery (restated from `StabilizationWelfare`): Taylor steps, CES and log expansions, moments, bounded sequences, Proposition 6.1, Calvo dispersion |
| [TidyR6WelfBridge](GainsFromCommitment/TidyR6WelfBridge.lean) | 65 | Chapter 6 Layer-B bridge (restated): orders uniform in the date, the utility and disutility sides, Propositions 6.4–6.5 for actual utility and their rankings |
| [TidyR6WelfCalvo](GainsFromCommitment/TidyR6WelfCalvo.lean) | 25 | Welfare to `O(ε³)` for Chapter 7: the ranking engine both ways, the Calvo bridge uniform in the state, expected welfare, `λ = κ/θ` derived |
| [TidyR6WelfFrictions](GainsFromCommitment/TidyR6WelfFrictions.lean) | 42 | Chapter 6 transactions frictions (restated): (4.9)–(4.11), Propositions 6.7–6.8 for actual utility with the one-sided expansion |
| [TidyR6WelfProp73](GainsFromCommitment/TidyR6WelfProp73.lean) | 9 | §1.2: actual welfare with transactions frictions to `O(ε³)`, Proposition 7.3 and its converse |
| [TidyR6WelfProps](GainsFromCommitment/TidyR6WelfProps.lean) | 18 | §1: Propositions 7.1, 7.2 and 7.4 as statements about actual welfare, with converses |
| [TidyR6WelfPropsS](GainsFromCommitment/TidyR6WelfPropsS.lean) | 11 | §2.1, §5.1: Propositions 7.5 and 7.15 as statements about actual expected welfare, with converses |

## Modelling conventions

* **Expectations.** Random variables are `Ω → ℝ` and processes `ℕ → Ω → ℝ`. Every model equation
  holds at every date as an equality of functions, for an arbitrary
  `ExpectationSystem` (linear, constant-preserving, monotone, with the law of iterated
  expectations). Perfect foresight (`perfectForesight`) and every finite event tree
  (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) are instances. Propositions 7.6–7.8
  use an integer-dated system (`CostPushCommitment.ExpSysZ`), because (2.9) needs `E_{t₀−k}` for
  every `k ≥ 1`; any `ExpectationSystem` extends to one (`CostPushCommitment.ExpSysZ.ofNat`).
  The variance results of §3 and F.4 are also stated for a measure-theoretic system (see below).
* **Measure-theoretic expectations.** The core `ExpectationSystem` is kept unchanged, and every
  result above still holds for it; but on a finite state space it cannot carry AR(1) innovations
  with positive conditional variance. `ExpectationsMeasure` adds, alongside it, a probability
  space with a filtration (`ExpectationsMeasure.MeasExpectationSystem`): `E_t` is Mathlib's
  `condExp`, variables are bounded measurable functions and processes, and equations hold almost
  everywhere. The bridge is additive and runs both ways: a finite event tree is a measure system
  with the same `E_t` (`ExpectationsMeasure.TreeBridge.treeSystem_E`), and a measure system on a
  finite discrete space with full support is a core system with the pull-out property
  (`ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_pullOut`). The genuine instance
  is the i.i.d. economy under `ν^ℕ` (`ExpectationsMeasureIID.iidSystem`,
  `ExpectationsMeasureIID.iid_not_finitely_supported`). AR(1) disturbances with constant
  conditional innovation variance are `NoninertialMeasure.MeasAR1Innov`, and `L_stab` is built
  from Mathlib's conditional variance (`NoninertialMeasure.mLstab12`, `NoninertialMeasure.mLstab`).
* **Bounded adapted processes.** Plans and disturbances are bounded and adapted; pre-sample
  values (`x_{t₀−1}`, `p_{t₀−1}`, `φ_{t₀−1}`, the shock history) are bounded and known at `t₀`.
  Uniqueness is uniqueness among bounded adapted processes.
* **Explicit hypotheses.** The optimality theorems take the pull-out property
  (`ExpectationSystem.PullOut`, true for perfect foresight and every finite tree) as a hypothesis;
  in the measure-theoretic versions it is a theorem of `condExp`.
  Exact uniqueness of an optimum takes faithfulness of `E_{t₀}` (`TargetingRule.Faithful`,
  `CostPushCommitment.ExpSysZ.Faithful`); without it the optimum is unique up to null events
  (`CostPushCommitment.optimal_unique_ae`). Parameter restrictions the book leaves implicit
  (`0 < β < 1`, `κ, λ, σ > 0`, nondegenerate shocks, `φ ≥ 0` in `OptimalTaylor`) are
  hypotheses; `TidyR5TaylorRegion` allows Taylor coefficients of any sign.
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
