# Sticky wages and prices in Lean

This is the `Gali/StickyWagesPrices/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Galí (2015), *Monetary Policy, Inflation, and the
Business Cycle*, 2nd ed., Chapter 6, "A Model with Sticky Wages and Prices"
(pp. 163–198), with its appendices and exercises. The library contains
**720 theorems**.

Headline results, in the namespace `Gali.StickyWagesPrices`:
* **The determinacy theorem of p. 174, which the book states without proof.**
  Under a rule responding to price inflation, wage inflation and output, the
  equilibrium is determinate iff
  `φ_p + φ_w + φ_y(1 − β)/Θ_y · (1/λ_p + 1/λ_w) > 1`, equivalently exactly
  three eigenvalues of `(A₀ʷ)⁻¹A₁ʷ` lie inside the unit circle
  (`Determinacy4.determinacy_iff`, `Determinacy4.eigenvalues_iff`). Outside
  the region the failure can be multiplicity or non-existence
  (`Determinacy4.exBase_multiplicity`, `Determinacy4.exNE_no_bounded_solution`).
* **Wage setting.** The union's first-order condition is necessary and
  sufficient with a unique optimum (`WageSetting.union_isMaxOn_iff_foc`); the
  wage NKPC follows exactly from the linearised conditions
  (`WageInflation.eq15_iff`).
* **Optimal policy.** Commitment is optimal by a Lagrangian argument
  (`OptimalPolicy.Stoch.commitment_optimal`); composite inflation targeting is
  optimal in the book's special case, proved by a separation argument
  (`OptimalPolicy.Stoch.composite_targeting_optimal`); the rule
  `i = rⁿ + φ_p π^p` with `φ_p > 1` implements the optimum under demand shocks
  (`OptimalPolicy.Stoch.rule_implements_book`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](StickyWagesPrices/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated) |
| [Expectations](StickyWagesPrices/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; forward series; the pull-out property |
| [ExpectationsFiniteTree](StickyWagesPrices/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out |
| [Determinacy4](StickyWagesPrices/Determinacy4.lean) | 128 | p. 174: the determinacy theorem for the four-variable system in full — argument principle, homotopy root count, Blanchard–Kahn with one predetermined variable; both failure modes of Fig. 6.1 |
| [LaborAggregation](StickyWagesPrices/LaborAggregation.lean) | 55 | §6.1.1: CES labour index, labour demand as the unique cost minimiser, the exact employment identity with wage and price dispersion |
| [WageDispersion](StickyWagesPrices/WageDispersion.lean) | 40 | p. 171, App. 6.1: wage and price dispersion to second order; the wage version of Lemma 2, exact |
| [WageSetting](StickyWagesPrices/WageSetting.lean) | 64 | §6.1.2.1: the union's infinite-horizon problem, (11) necessary and sufficient from primitives, (12)–(13) |
| [WageInflation](StickyWagesPrices/WageInflation.lean) | 28 | §6.1.2.2: the wage-index recursion, (14) as an exact derivative, the wage NKPC (15), `λ_w` |
| [GapForm](StickyWagesPrices/GapForm.lean) | 25 | §6.2: (16)–(22) in gaps, the composite NKPC (36) for all parameters |
| [System](StickyWagesPrices/System.lean) | 18 | §6.2: the matrix form (24), the corrected zero-solution statement, the determinant on the boundary |
| [Efficiency](StickyWagesPrices/Efficiency.lean) | 71 | §6.3: the planner with goods and labour-type aggregators, the optimal subsidy |
| [Welfare](StickyWagesPrices/Welfare.lean) | 36 | §6.3, App. 6.1: the second-order welfare criterion (28) in two layers; loss weights |
| [LimitingCases](StickyWagesPrices/LimitingCases.lean) | 36 | p. 180: flexible wages, flexible prices, suboptimality of strict price or wage targeting |
| [Calibration](StickyWagesPrices/Calibration.lean) | 13 | §6.2.1, §6.5: baseline coefficients, the composite weight 47/55, loss weights, Table 6.1 |
| [OptimalPolicy](StickyWagesPrices/OptimalPolicy.lean) | 75 | §6.4, App. 6.2: optimal commitment (deterministic and stochastic), the 7-variable system, the implementing rule, optimality of composite targeting |
| [Ex6_1](StickyWagesPrices/Ex6_1.lean) | 7 | Exercise 6.1: staggered wage setting |
| [Ex6_2](StickyWagesPrices/Ex6_2.lean) | 17 | Exercise 6.2: wages set in advance |
| [Ex6_3](StickyWagesPrices/Ex6_3.lean) | 17 | Exercise 6.3: Blanchard–Summers hysteresis |
| [Ex6_4](StickyWagesPrices/Ex6_4.lean) | 26 | Exercise 6.4: real wage rigidities and the tradeoff |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
