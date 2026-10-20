# Monetary policy design in Lean

This is the `Gali/MonetaryPolicyDesign/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Galí (2015), *Monetary Policy, Inflation, and the
Business Cycle*, 2nd ed., Chapter 4, "Monetary Policy Design in the Basic New
Keynesian Model" (pp. 98–125), with its appendix and exercises, plus a
post-book proof of uniqueness under the money rule of Exercise 4.4(c). The
library contains **770 theorems** and audits **1081 declarations**.

Headline results, in the namespace `Gali.MonetaryPolicyDesign`:
* **Efficiency and distortions.** The planner's optimum is symmetric across
  goods (`Efficient.Goods.planner_optimal_iff`); the markup leaves employment
  strictly below efficient and `τ = 1/ε` is the unique corrective subsidy
  (`Distortions.markup_inefficiently_low`, `Distortions.flex_efficient_iff_subsidy`).
* **Optimal policy and rules.** The divine coincidence along bounded equilibria
  (`OptimalPolicy.divine_coincidence`); `i = rⁿ` is indeterminate
  (`RuleExogenous.not_determinate_AO`); determinacy under the Taylor-type rule
  iff (14) and under the forward rule iff (17)–(18), with the corrected matrix
  (`RuleTaylorPrinciple.determinate_iff_14`, `RuleForward.determinate_iff_17_18`).
* **Welfare.** The second-order approximation as an exact identity plus an
  `O(s³)` statement (`Welfare.secondOrderUtility_eq`,
  `Welfare.period_utility_second_order_dispersion`); Lemma 2 exactly, in the
  change of the mean log price (`Welfare.lemma2_calvo`); Table 4.1 from closed
  forms (`SimpleRules.table41_tech_1`).
* **Exercises.** All six, including the exact lognormal model with prices set
  in advance on a constructed probability space (`Ex4_5.exists_sticky_equilibrium`)
  and the corrected determinacy region of the price-level rule
  (`Ex4_6.determinate_iff`).
* **Ex. 4.4(c) uniqueness (post-book).** The optimum `ỹ = π = 0`, `p = p*`,
  `i = rⁿ` is the *unique* bounded equilibrium under the money supply rule, for
  `σ > 0`, `η ≥ 0`, `κ > 0`, `0 < β ≤ 1` and any expectation system
  (`Ex4_4Determinacy.moneyRuleUniqueness_holds`,
  `Ex4_4Determinacy.moneyRule_implements_uniquely`). Every equilibrium under the
  rule solves the Chapter 3 money-rule system (34) with all shocks zero, the
  natural-rate and natural-output terms cancelling
  (`Ex4_4Determinacy.system34_of_moneyRule`), and (34) is determinate
  (`MoneyRuleDeterminacy.system34_existsUnique`, Galí's fn. 14 of Chapter 3,
  proved via the general Blanchard–Kahn theorem `GeneralBK.determinate_iff`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](MonetaryPolicyDesign/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated from the Chapter 2 project) |
| [Expectations](MonetaryPolicyDesign/Expectations.lean) | 18 | Rational expectations as an `ExpectationSystem`; forward series; determinacy iff Schur–Cohn |
| [ExpectationsFiniteTree](MonetaryPolicyDesign/ExpectationsFiniteTree.lean) | 20 | A finite event tree satisfies the expectation axioms |
| [Efficient](MonetaryPolicyDesign/Efficient.lean) | 51 | §4.1: the planner's optimum is symmetric and characterised by MRS = MPN; unique efficient employment |
| [Distortions](MonetaryPolicyDesign/Distortions.lean) | 41 | §4.2: the markup wedge, employment below efficient, the subsidy `τ = 1/ε`, average markups, price dispersion |
| [OptimalPolicy](MonetaryPolicyDesign/OptimalPolicy.lean) | 13 | §4.3: the divine coincidence, `i = rⁿ`, the optimal policy as the unique zero-loss equilibrium |
| [RuleExogenous](MonetaryPolicyDesign/RuleExogenous.lean) | 20 | §4.3.1.1: `i = rⁿ` is indeterminate (`A_O` has one root above 1) |
| [RuleTaylorPrinciple](MonetaryPolicyDesign/RuleTaylorPrinciple.lean) | 14 | §4.3.1.2: determinacy iff (14), the long-run response (15) |
| [RuleForward](MonetaryPolicyDesign/RuleForward.lean) | 20 | §4.3.1.3: the forward-looking rule with the corrected `A_F`, (17)–(18), the strict bound on `φ_π` |
| [Welfare](MonetaryPolicyDesign/Welfare.lean) | 57 | §4.4, App. 4.1: the second-order welfare approximation (exact layer and `O(s³)` layer), Lemmas 1 and 2 (exact), the loss weights |
| [SimpleRules](MonetaryPolicyDesign/SimpleRules.lean) | 49 | §4.4.1–4.4.2: simple rules, MSV losses, fn. 10, the money-growth system, Table 4.1 |
| [Ex4_1](MonetaryPolicyDesign/Ex4_1.lean) | 37 | Exercise 4.1: eigenvalues of `A_O` and `A_T` |
| [Ex4_2](MonetaryPolicyDesign/Ex4_2.lean) | 30 | Exercise 4.2: noisy inflation data |
| [Ex4_3](MonetaryPolicyDesign/Ex4_3.lean) | 17 | Exercise 4.3: technology shocks and employment |
| [Ex4_4](MonetaryPolicyDesign/Ex4_4.lean) | 21 | Exercise 4.4: interest-rate versus money rules |
| [Ex4_5](MonetaryPolicyDesign/Ex4_5.lean) | 105 | Exercise 4.5: prices set in advance, an exact lognormal model on a constructed probability space |
| [Ex4_6](MonetaryPolicyDesign/Ex4_6.lean) | 46 | Exercise 4.6: the price-level rule (corrected determinacy region) |
| [InvariantSplit](MonetaryPolicyDesign/InvariantSplit.lean) | 52 | Post-book (restated from the Woodford Chapter 4 project): eigenvalues with multiplicity, the stable invariant subspace and its dimension, the split into predetermined and non-predetermined coordinates |
| [GeneralBKForward](MonetaryPolicyDesign/GeneralBKForward.lean) | 17 | Post-book (restated from Woodford): forward systems `s_t = K E_t s_{t+1} + w_t` over any finite index type, the unique bounded forward solution |
| [GeneralBK](MonetaryPolicyDesign/GeneralBK.lean) | 39 | Post-book (restated from Woodford): the general Blanchard–Kahn theorem for any `ExpectationSystem`, determinacy iff no unit root, the counting rule and genericity |
| [MoneyRuleSystem](MonetaryPolicyDesign/MoneyRuleSystem.lean) | 14 | Post-book (restated from the Chapter 3 project): the money-rule system (34), its characteristic cubic, the book's determinacy claim (Ch. 3, fn. 14) |
| [MoneyRuleRoots](MonetaryPolicyDesign/MoneyRuleRoots.lean) | 17 | Post-book (restated from Chapter 3): the cubic's root `r > 1` and Schur-stable quadratic factor; fn. 14 proved; root location of `A_M` |
| [MoneyRuleDeterminacy](MonetaryPolicyDesign/MoneyRuleDeterminacy.lean) | 35 | Post-book (restated from Chapter 3): Blanchard–Kahn determinacy of (34) for every forcing, `η > 0` and `η = 0` |
| [Ex4_4Determinacy](MonetaryPolicyDesign/Ex4_4Determinacy.lean) | 14 | Exercise 4.4(c): the money rule reduces to (34) with zero shocks; the optimum is the unique bounded equilibrium |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
