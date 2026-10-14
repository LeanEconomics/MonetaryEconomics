# Monetary policy in the open economy in Lean

This is the `Gali/OpenEconomy/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Galí (2015), *Monetary Policy, Inflation, and the
Business Cycle*, 2nd ed., Chapter 8, "Monetary Policy in the Open Economy"
(pp. 223–260), the Galí–Monacelli small open economy, with its appendix and
exercises. The library contains **464 theorems**.

Headline results, in the namespace `Gali.OpenEconomy`:
* **Households.** CES demand and the CPI as the unique expenditure minimiser,
  with the Cobb–Douglas limit as `η → 1` (`Preferences.expenditure_eq_iff`,
  `Preferences.cesIndex_tendsto_cd`); international risk sharing along every
  path of an event tree (`RiskSharing.riskSharing_ratio_const`); uncovered
  interest parity as an exact derivative (`UIP.hasFDerivAt_uipGap`).
* **The small open economy.** The open-economy DIS and NKPC with `σ_υ` and
  `κ_υ` (`AggregateDemand.eq26_iff_eq28`, `Supply.eq37`); determinacy iff
  `κ_υ(φ_π − 1) + (1 − β)φ_y > 0` (`TaylorRule.determinate_iff_41`); exchange-rate
  overshooting iff the nominal rate rises (`TaylorRule.overshoot_iff_nominal_rises`).
* **Optimal policy.** Strict domestic inflation targeting is optimal in the
  special case and implemented uniquely by `φ_π > 1`
  (`OptimalPolicy.optimal_policy`, `OptimalPolicy.rule42_unique`); the book's
  "optimal subsidy" is a 48% employment tax at its own calibration
  (`OptimalPolicy.optSubsidy_calibration`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](OpenEconomy/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated) |
| [Expectations](OpenEconomy/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; forward series; the pull-out property |
| [ExpectationsFiniteTree](OpenEconomy/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out |
| [Preferences](OpenEconomy/Preferences.lean) | 53 | §8.1.1: home-bias CES demand and the CPI as the unique expenditure minimiser; the η → 1 limits; variety demand |
| [Identities](OpenEconomy/Identities.lean) | 14 | §8.1.1.1: (12)–(14) and the real exchange rate, exact and as derivatives |
| [RiskSharing](OpenEconomy/RiskSharing.lean) | 17 | §8.1.1.2: Arrow-security optimality on an event tree, (8)–(10), (15), risk sharing (16)–(17) |
| [UIP](OpenEconomy/UIP.lean) | 12 | §8.1.1.3: exact UIP, (18) as a derivative, (19), the forward solution (20) and its limit condition |
| [AggregateDemand](OpenEconomy/AggregateDemand.lean) | 40 | §8.1.3, §8.2.1: exports, goods-market clearing (24)–(25), σ_υ, the open-economy DIS (26)–(30), net exports (31) |
| [Supply](OpenEconomy/Supply.lean) | 40 | §8.2.2: (32)–(38), natural output and the Γ coefficients, the open-economy NKPC with κ_υ |
| [TaylorRule](OpenEconomy/TaylorRule.lean) | 50 | §8.3: determinacy (41), monetary-shock responses, overshooting, Λ_v and openness (corrected) |
| [OptimalPolicy](OpenEconomy/OptimalPolicy.lean) | 53 | §8.4: the planner, the optimal subsidy (a tax at the calibration), optimality and implementation of SDIT, natural terms of trade |
| [Welfare](OpenEconomy/Welfare.lean) | 40 | §8.4.3, App. 8.1: the second-order welfare criterion (43)–(44), Lemma 2 |
| [SimpleRules](OpenEconomy/SimpleRules.lean) | 21 | §8.5: the regimes, Table 8.1's loss row, fns. 14–15 (exchange-rate unit roots) |
| [Ex8_1](OpenEconomy/Ex8_1.lean) | 32 | Exercise 8.1: financial autarky, flexible prices, an exchange-rate peg |
| [Ex8_2](OpenEconomy/Ex8_2.lean) | 28 | Exercise 8.2: technology shocks under a Taylor rule and under a peg |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
