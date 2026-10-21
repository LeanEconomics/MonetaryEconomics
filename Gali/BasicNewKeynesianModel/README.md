# The basic New Keynesian model in Lean

This is the `Gali/BasicNewKeynesianModel/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Galí (2015), *Monetary Policy, Inflation, and the
Business Cycle*, 2nd ed., Chapter 3, "The Basic New Keynesian Model"
(pp. 52–97), with its appendices and exercises, plus a post-book proof of the
money-rule determinacy claim of p. 75 and fn. 14. The library contains
**753 theorems** and audits **1038 declarations**.

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
* **Money-rule determinacy (post-book).** Galí's claim (p. 75, fn. 14) that
  the equilibrium under an exogenous money supply is always determinate rests on
  numerical evidence only in the book. It is proved here for all `σ ≥ 0`,
  `η ≥ 0`, `κ > 0`, `0 ≤ β ≤ 1`, including Galí's boundary `η = 0`: `A_M` has
  one eigenvalue outside and two inside the unit circle, none on it
  (`MoneyRuleRoots.bookDeterminacyClaim_holds`,
  `MoneyRuleRoots.AM_root_location`). This is genuine Blanchard–Kahn
  determinacy: for `σ > 0` and `0 < β ≤ 1`, system (34) has exactly one bounded
  adapted equilibrium for every bounded adapted shock process and initial real
  balance, for any expectation system (`MoneyRuleDeterminacy.system34_existsUnique`,
  via the general Blanchard–Kahn theorem `GeneralBK.determinate_iff`); for
  `η > 0` the model equations, the nominal rate included, have exactly one
  bounded solution (`MoneyRuleDeterminacy.model_existsUnique`).
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
| [InvariantSplit](BasicNewKeynesianModel/InvariantSplit.lean) | 52 | Post-book (restated from the Woodford Chapter 4 project): eigenvalues with multiplicity, the stable invariant subspace and its dimension, the split into predetermined and non-predetermined coordinates |
| [GeneralBKForward](BasicNewKeynesianModel/GeneralBKForward.lean) | 17 | Post-book (restated from Woodford): forward systems `s_t = K E_t s_{t+1} + w_t` over any finite index type, the unique bounded forward solution |
| [GeneralBK](BasicNewKeynesianModel/GeneralBK.lean) | 39 | Post-book (restated from Woodford): the general Blanchard–Kahn theorem for any `ExpectationSystem`, determinacy iff no unit root, the counting rule and genericity |
| [MoneyRuleRoots](BasicNewKeynesianModel/MoneyRuleRoots.lean) | 17 | p. 75, fn. 14: the characteristic cubic factors with a root `r > 1` and a Schur-stable quadratic; the book's determinacy claim proved; root location of `A_M` |
| [MoneyRuleDeterminacy](BasicNewKeynesianModel/MoneyRuleDeterminacy.lean) | 36 | p. 75: Blanchard–Kahn determinacy of (34) for every forcing (backward form for `η > 0`, exact two-variable reduction for `η = 0`); the model's unique equilibrium for `η > 0` |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
