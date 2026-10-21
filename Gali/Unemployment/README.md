# Unemployment in the New Keynesian model in Lean

This is the `Gali/Unemployment/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Galí (2015), *Monetary Policy, Inflation, and the
Business Cycle*, 2nd ed., Chapter 7, "Unemployment in the New Keynesian Model"
(pp. 199–222), with the exercises. The library contains **412 theorems**,
including the core and the Chapter 6 determinacy theorem it restates.

Headline results, in the namespace `Gali.Unemployment`:
* **Unemployment.** Participation is a threshold rule (`IndivisibleLabor.participation_set_eq`);
  the wage markup equals `φ` times unemployment exactly (`UnemploymentDef.eq8_iff`),
  giving the wage Phillips curve in unemployment (`UnemploymentDef.wageNKPC_iff_eq11`);
  unemployment fluctuates only with nominal wage rigidity
  (`UnemploymentDef.flexible_unemployment_constant`).
* **Equilibrium.** The system is Chapter 6's plus a static equation, so it is
  determinate iff the p. 174 condition holds (`Equilibrium.determinacy_ch7_iff`),
  and the book's rule (17) is determinate (`Equilibrium.rule17_determinate`).
* **Policy.** The optimal policy is Chapter 6's, with unemployment read off (16)
  (`Policy.isOptimal7_iff_eq`); demand shocks leave the labour market untouched
  (`Policy.demand_shock_labour_market`); the labour force falls with consumption
  through the wealth effect (`Policy.laborForce_strictAnti`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](Unemployment/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated) |
| [Expectations](Unemployment/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; forward series; the pull-out property |
| [ExpectationsFiniteTree](Unemployment/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out |
| [Determinacy4](Unemployment/Determinacy4.lean) | 128 | The four-variable determinacy theorem of Chapter 6, p. 174 (restated from the Chapter 6 project) |
| [IndivisibleLabor](Unemployment/IndivisibleLabor.lean) | 15 | §7.1.1: indivisible labour, the disutility integral, participation and the marginal participant (5) |
| [UnemploymentDef](Unemployment/UnemploymentDef.lean) | 25 | §7.1.2: (6) exact and to first order, the unemployment rate (7), `μ^w = φu` (8), `uⁿ` (10), the wage Phillips curve (11), unemployment needs wage rigidity |
| [Equilibrium](Unemployment/Equilibrium.lean) | 9 | §7.2: (12)–(16), the system as Chapter 6's plus (16), determinacy iff the p. 174 condition, rule (17) |
| [Policy](Unemployment/Policy.lean) | 53 | §7.3: calibration, the labour-force wealth effect, fn. 12, optimal policy as Chapter 6's, efficient and demand-shock responses, rule (22) |
| [Ex7_1](Unemployment/Ex7_1.lean) | 86 | Exercise 7.1: flexible prices, the unemployment–inflation loss, discretion, implementation, commitment |
| [Ex7_2](Unemployment/Ex7_2.lean) | 13 | Exercise 7.2: preference and wage-markup shocks, identification |
| [Ex7_3](Unemployment/Ex7_3.lean) | 19 | Exercise 7.3: a dampened wealth effect on participation |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
