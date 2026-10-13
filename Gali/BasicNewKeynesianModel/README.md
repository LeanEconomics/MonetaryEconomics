# The basic New Keynesian model in Lean

This is the `Gali/BasicNewKeynesianModel/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Galí (2015), *Monetary Policy, Inflation, and the
Business Cycle*, 2nd ed., Chapter 3, "The Basic New Keynesian Model"
(pp. 52–97), with its appendices and exercises. The library contains
**592 theorems** and audits **837 declarations**.

Headline results, in the namespace `Gali.BasicNewKeynesianModel`:
* **Determinacy.** A two-variable rational-expectations system has a unique
  bounded solution iff `A` satisfies the Schur–Cohn condition
  (`ExpectationSystem.determinate_iff`), for any expectation system,
  including perfect foresight and a genuine event tree
  (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`).
* **The Taylor principle.** The equilibrium under a Taylor rule is determinate
  iff `κ(φ_π − 1) + (1 − β)φ_y > 0`, and the MSV solution is then the unique
  bounded equilibrium (`TaylorRuleSystem.determinate_iff_BM`,
  `TaylorRuleSystem.equilibrium_iff_msv`).
* **Microfoundations.** CES demand is the unique cost-minimising allocation
  (`CES.spend_eq_iff`); the Calvo index recursion is exact
  (`CalvoIndex.calvo_recursion`); the reset-price condition (10) is necessary
  and sufficient from primitives (`ResetPrice.isMaxOn_iff_foc_of_primitives`);
  price dispersion is `(ε/2Θ)·var` to second order
  (`PriceDispersion.dispersion_second_order`); the log-linear Euler equation is
  the exact derivative of the nonlinear one
  (`Household.hasDerivAt_log_eulerMoment_family`).
* **Corrections.** Seven printed claims are false or need a missing hypothesis;
  each is proved in corrected form with a counterexample to the printed one.

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [PriceDuration](BasicNewKeynesianModel/PriceDuration.lean) | 5 | §3.2: Calvo price durations, mean duration `1/(1 − θ)`, the bundled parameter `CalvoParam` |
| [Determinacy](BasicNewKeynesianModel/Determinacy.lean) | 23 | p. 65, Woodford Prop. C.1: the Schur–Cohn condition for `2 × 2` matrices through explicit roots, decay of `Aᵏ`, bounded self-fulfilling paths when it fails |
| [Expectations](BasicNewKeynesianModel/Expectations.lean) | 13 | Rational expectations as an `ExpectationSystem`; forward uniqueness; determinacy of two-variable systems iff Schur–Cohn |
| [ExpectationsFiniteTree](BasicNewKeynesianModel/ExpectationsFiniteTree.lean) | 20 | A finite event tree satisfies the expectation axioms; a coin-flip tree and an AR(1) process on it |
| [CES](BasicNewKeynesianModel/CES.lean) | 27 | §3.1, App. 3.1: Dixit–Stiglitz demand as the unique cost-minimising allocation, continuum and finite goods; (12) |
| [CalvoIndex](BasicNewKeynesianModel/CalvoIndex.lean) | 17 | §3.2.1, App. 3.2–3.3: the exact price-index recursion (7) from the cross-section of prices; (8) as an exact derivative |
| [PriceDispersion](BasicNewKeynesianModel/PriceDispersion.lean) | 23 | App. 3.4, (14): price dispersion is nonnegative, zero iff prices are equal, and `(ε/2Θ)·var` to second order |
| [ResetPrice](BasicNewKeynesianModel/ResetPrice.lean) | 56 | §3.2.2, App. 3.3: the reset-price problem over an infinite horizon, (10) necessary and sufficient from primitives, (11) as its linearisation |
| [MarginalCost](BasicNewKeynesianModel/MarginalCost.lean) | 21 | §3.3: (14)–(16), firm and average marginal cost, `Θ`, the reset-price formula and its recursive form |
| [NKPC](BasicNewKeynesianModel/NKPC.lean) | 25 | §3.3: (17)–(22), the NKPC, `λ` monotonicity (corrected in `ε`), natural output with `ψ_y < 0` |
| [DIS](BasicNewKeynesianModel/DIS.lean) | 11 | §3.3: (13), (23)–(25), forward iteration of the Euler equation, the natural rate |
| [Household](BasicNewKeynesianModel/Household.lean) | 32 | §3.1, Ch. 2: household optimality, the nonlinear Euler equation, (2)–(3) exact under perfect foresight and as exact derivatives |
| [TaylorRuleSystem](BasicNewKeynesianModel/TaylorRuleSystem.lean) | 19 | §3.4.1: (26)–(30), the equilibrium system, Bullard–Mitra (28), the unique bounded (MSV) equilibrium |
| [ShockResponses](BasicNewKeynesianModel/ShockResponses.lean) | 29 | §3.4.1.1–3: monetary, discount-rate and technology shocks, with the corrected employment response |
| [Calibration](BasicNewKeynesianModel/Calibration.lean) | 14 | pp. 67–68: the baseline calibration's numbers |
| [MoneyRule](BasicNewKeynesianModel/MoneyRule.lean) | 36 | §3.4.2: the money-supply rule, the `3 × 3` system (34), its characteristic cubic, the interest-rate equation, the price-level rule |
| [Ex3_1](BasicNewKeynesianModel/Ex3_1.lean) | 21 | Exercise 3.1: exponential price durations |
| [Ex3_2](BasicNewKeynesianModel/Ex3_2.lean) | 16 | Exercise 3.2: government purchases with a CES index |
| [Ex3_3](BasicNewKeynesianModel/Ex3_3.lean) | 27 | Exercise 3.3: government purchases and sticky prices, equilibrium iff `φ_π > 1` |
| [Ex3_4](BasicNewKeynesianModel/Ex3_4.lean) | 47 | Exercise 3.4: indexation and the hybrid NKPC |
| [Ex3_5](BasicNewKeynesianModel/Ex3_5.lean) | 54 | Exercise 3.5: Taylor staggered pricing (with the corrected first-order condition) |
| [Ex3_6](BasicNewKeynesianModel/Ex3_6.lean) | 27 | Exercise 3.6: Mankiw–Reis sticky information |
| [Ex3_7](BasicNewKeynesianModel/Ex3_7.lean) | 15 | Exercise 3.7: technology shocks and a Taylor rule |
| [Ex3_8](BasicNewKeynesianModel/Ex3_8.lean) | 6 | Exercise 3.8: utility linear in consumption |
| [Ex3_9](BasicNewKeynesianModel/Ex3_9.lean) | 8 | Exercise 3.9: the Galí–Gertler hybrid NKPC |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
