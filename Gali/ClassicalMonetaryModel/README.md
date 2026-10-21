# The classical monetary model in Lean

This is the `Gali/ClassicalMonetaryModel/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Galí (2015), *Monetary Policy, Inflation, and the
Business Cycle*, 2nd ed., Chapter 2, "A Classical Monetary Model"
(pp. 17–51), with its appendix and exercises. The library contains
**664 theorems** and audits **935 declarations**.

Headline results, in the namespace `Gali.ClassicalMonetaryModel`:
* **Household optimality.** In the infinite-horizon problem, optimality is
  equivalent to the first-order conditions with transversality
  (`Household.optimal_iff`); the log-linear Euler equation is the exact
  derivative of the nonlinear one (`Household.hasDerivAt_log_eulerMoment_family`).
* **Neutrality.** Any two equilibria under any two monetary policies have the
  same real allocation, so all policies are welfare-equivalent
  (`FirmsEquilibrium.neutrality_across_policies`,
  `FirmsEquilibrium.welfare_policy_invariant`).
* **Price-level determination.** An exogenous interest rate leaves the price
  level indeterminate, with genuine sunspots under uncertainty
  (`InterestRules.coin_exo_sunspot`); an inflation rule is determinate iff
  `φ_π > 1`, including the case `φ_π = 1` the book omits
  (`InterestRules.taylor_principle`).
* **Money in the utility function.** `χ`, `k_m`, `ϖ` and the price-level
  forward solution (48); the Friedman rule is efficient only with satiation in
  real balances (`FriedmanRule.decentralised_optimal_iff_friedman`,
  `FriedmanRule.no_planner_optimum_isoelastic`).
* **Exercises.** All nine, including the exact lognormal equilibrium on a
  constructed Gaussian probability space (`Ex2_5.exists_exact_equilibrium`) and
  determinacy with one predetermined variable (`Ex2_3.saddle_unique`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](ClassicalMonetaryModel/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated from the Chapter 3 project) |
| [Expectations](ClassicalMonetaryModel/Expectations.lean) | 18 | Rational expectations as an `ExpectationSystem`; forward series as the unique bounded solution; determinacy iff Schur–Cohn |
| [ExpectationsFiniteTree](ClassicalMonetaryModel/ExpectationsFiniteTree.lean) | 20 | A finite event tree satisfies the expectation axioms; coin-flip examples |
| [Household](ClassicalMonetaryModel/Household.lean) | 77 | §2.1, App. 2.1: household optimality, the infinite-horizon problem with transversality, the Euler equation and its exact linearisation, fn. 5, money demand (11) |
| [FirmsEquilibrium](ClassicalMonetaryModel/FirmsEquilibrium.lean) | 38 | §2.2–2.3, §2.4.4: labour demand, the unique real equilibrium (18)–(21), comparative statics, neutrality, welfare equivalence |
| [InterestRules](ClassicalMonetaryModel/InterestRules.lean) | 57 | §2.4.1–2.4.2: indeterminacy under exogenous rates, (24)–(26), the Taylor principle including `φ_π = 1`, shock responses |
| [MoneySupply](ClassicalMonetaryModel/MoneySupply.lean) | 18 | §2.4.3: (27)–(29), money-growth representation, AR(1) money growth, overshooting |
| [MIUSeparable](ClassicalMonetaryModel/MIUSeparable.lean) | 24 | §2.5.1: money in the utility function, separable case, (32)–(36) |
| [MIUNonseparable](ClassicalMonetaryModel/MIUNonseparable.lean) | 63 | §2.5.2: the nonseparable CES case, `χ`, `k_m`, `ϖ`, (37)–(48), the countercyclical real wage |
| [FriedmanRule](ClassicalMonetaryModel/FriedmanRule.lean) | 25 | §2.5.3: the planner, the Friedman rule, indeterminacy at `i = 0`, fn. 13, the p. 42 rule |
| [Ex2_1](ClassicalMonetaryModel/Ex2_1.lean) | 37 | Exercise 2.1: nonseparable leisure |
| [Ex2_2](ClassicalMonetaryModel/Ex2_2.lean) | 23 | Exercise 2.2: alternative policy rules |
| [Ex2_3](ClassicalMonetaryModel/Ex2_3.lean) | 41 | Exercise 2.3: indeterminacy with one predetermined variable (partial adjustment, moving average) |
| [Ex2_4](ClassicalMonetaryModel/Ex2_4.lean) | 52 | Exercise 2.4: the welfare cost of inflation (Lucas 2000) |
| [Ex2_5](ClassicalMonetaryModel/Ex2_5.lean) | 47 | Exercise 2.5: the exact classical model on a constructed Gaussian probability space |
| [Ex2_6](ClassicalMonetaryModel/Ex2_6.lean) | 16 | Exercise 2.6: uniqueness in the MIU model |
| [Ex2_7](ClassicalMonetaryModel/Ex2_7.lean) | 29 | Exercise 2.7: shopping time |
| [Ex2_8](ClassicalMonetaryModel/Ex2_8.lean) | 39 | Exercise 2.8: cash in advance, transversality and the binding constraint |
| [Ex2_9](ClassicalMonetaryModel/Ex2_9.lean) | 17 | Exercise 2.9: cash and credit goods |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
