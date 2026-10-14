# Price-level determination in Lean

This is the `Woodford/PriceLevelDetermination/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Woodford (2003), *Interest and Prices*, Chapter 2, "Price-Level
Determination under Interest-Rate Rules" (pp. 61–138), together with the proofs in Appendix A
(pp. 627–655). Model equations hold for an arbitrary expectation operator, so results cover
perfect foresight and genuine uncertainty; log-linear equations are exact derivatives of the
nonlinear model, and the exact nonlinear model is linked to them by an implicit-function theorem
on bounded sequences. The library contains **851 theorems**, including the shared core.

Headline results, in the namespace `Woodford.PriceLevelDetermination`:
* **Budget constraints and transversality.** Proposition 2.1 in both directions under explicit
  summability hypotheses (`IntertemporalBudget.prop_2_1_iff`), Proposition 2.2
  (`Transversality.prop_2_2`), and no equilibrium when money pays no interest
  (`NoBubble.prop_2_4`).
* **The forward solution.** A unique bounded solution of `z_t = a E_t z_{t+1} + u_t` for every
  bounded adapted `u` exactly when `|a| < 1` (`ForwardSolution.existsUnique_iff`), with the
  continuum (A.17) for `|a| > 1` (`ForwardSolution.eq_sunspotFamily`).
* **Interest-rate rules.** Exact determinacy conditions for Wicksellian, Taylor, inertial and
  money-growth regimes (`Wicksell.determinate_iff`, `TaylorPrinciple.prop_2_6_iff`,
  `InertialRules.determinate8_iff`, `MoneyGrowth.prop_2_11`, `NonSeparable.prop_2_12_iff`,
  `ShortPeriod.prop_2_15`), and uncountably many exact sunspot equilibria under an exogenous
  rate (`ExogenousRate.prop_2_5_uncountable`).
* **The exact nonlinear model.** Local determinacy, smooth dependence and second-order accuracy
  of the log-linear solution on `ℓ∞` (`LocalIFT.local_determinacy_loc`,
  `LocalIFT.second_order_loc`), applied to Propositions 2.3, 2.6–2.8 and 2.11–2.13
  (`LocalIFT.taylor_local_determinacy`, `Nonlinear.nsw_local_determinacy`); the `O(ξ²)` claim
  fails for a merely `C¹` model (`LocalIFT.not_second_order_of_C1`).
* **Global dynamics.** Self-fulfilling deflations under a Taylor rule
  (`GlobalDynamics.self_fulfilling_deflation46`), transversality failures under money targeting
  (`MoneyTargetingDynamics.money_tvc_violated`), and the Schmitt-Grohé–Uribe example, corrected
  (`SchmittGroheUribe.sgu_unique_pf_equilibrium`, `SchmittGroheUribe.e5_counterexample`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise.

Not covered: the stochastic (`L∞` processes with `E_t`) version of the Appendix A.3
implicit-function argument and general `n`-dimensional systems with predetermined variables are
deferred to a later general-theory project, so the exact nonlinear results are for perfect
foresight; Figures 2.1–2.5 are formalised only through their closed forms and spot values; the
uniqueness of the stochastic equilibrium in the Schmitt-Grohé–Uribe example (p. 137) is only
asserted in the book and is not formalised.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](PriceLevelDetermination/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated from the Galí projects) |
| [Expectations](PriceLevelDetermination/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; forward series; the pull-out property |
| [ExpectationsFiniteTree](PriceLevelDetermination/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out |
| [AssetPricing](PriceLevelDetermination/AssetPricing.lean) | 27 | §1.1: riskless returns (1.4)–(1.6), the opportunity cost of money (1.7)–(1.8), the stochastic discount factor and its tower property (A.1), arbitrage (1.11), conditional monotone convergence |
| [IntertemporalBudget](PriceLevelDetermination/IntertemporalBudget.lean) | 17 | §1.1, A.1: Proposition 2.1 in both directions; (1.13) with equality and the transversality condition (1.18)–(1.19) |
| [Equilibrium](PriceLevelDetermination/Equilibrium.lean) | 16 | §1.1: (1.14)–(1.17), (1.20)–(1.23), rational-expectations equilibrium, government purchases (1.26)–(1.27) |
| [Transversality](PriceLevelDetermination/Transversality.lean) | 8 | §1.1, A.2: Proposition 2.2 and 2.2′ |
| [NoBubble](PriceLevelDetermination/NoBubble.lean) | 7 | §1.2, A.5: Proposition 2.4, no equilibrium with `i^m = 0` |
| [ForwardSolution](PriceLevelDetermination/ForwardSolution.lean) | 43 | A.4, A.10: (A.14)–(A.17) for `\|a\| < 1` including `a < 0`, the continuum for `\|a\| ≥ 1`, the exact determinacy condition, the form `A z_t = B E_t z_{t+1} + f_t`, the predetermined variant; summation by parts and the sign lemma |
| [LogLinear](PriceLevelDetermination/LogLinear.lean) | 11 | §1.1–1.2, §2.2: (1.21), (1.32)–(1.34) and (2.4)–(2.5) as exact derivatives |
| [Wicksell](PriceLevelDetermination/Wicksell.lean) | 28 | §1.2: implied taxes (1.29), (1.35)–(1.39), Proposition 2.3 (linear), fn. 17 corrected, pp. 84–85 |
| [ExogenousRate](PriceLevelDetermination/ExogenousRate.lean) | 25 | §2.1, A.6: Proposition 2.5 with exact sunspot equilibria, (2.1)–(2.3), the divergence and worst-case arguments |
| [TaylorPrinciple](PriceLevelDetermination/TaylorPrinciple.lean) | 22 | §2.2: (2.6)–(2.7), Proposition 2.6 both ways, the price level (fn. 25), pp. 92–93 |
| [InertialRules](PriceLevelDetermination/InertialRules.lean) | 83 | §2.3, A.7–A.10: Propositions 2.7–2.10, (2.8)–(2.17), impulse responses, Beveridge–Nelson, (A.23)–(A.25), Proposition 2.9 corrected |
| [MoneyGrowth](PriceLevelDetermination/MoneyGrowth.lean) | 26 | §3.1–3.3, A.11: money demand (3.2)–(3.6), Proposition 2.11, (3.7)–(3.9) |
| [NonSeparable](PriceLevelDetermination/NonSeparable.lean) | 40 | §3.4, A.12–A.13: (3.10)–(3.22), Propositions 2.12–2.13 with exact conditions |
| [Calibration](PriceLevelDetermination/Calibration.lean) | 17 | §3.4: (3.23), the p. 118 numbers, Figures 2.2–2.3 spot values |
| [ShortPeriod](PriceLevelDetermination/ShortPeriod.lean) | 24 | §3.4, A.14–A.15: (3.24), Propositions 2.14–2.15, (3.26), the A.15 limits corrected |
| [GlobalDynamics](PriceLevelDetermination/GlobalDynamics.lean) | 49 | §4.1: (4.2)–(4.6), Figure 2.4, self-fulfilling deflations, monotone one-dimensional maps |
| [MoneyTargetingDynamics](PriceLevelDetermination/MoneyTargetingDynamics.lean) | 32 | §4.1–4.3: (4.7)–(4.10), Figure 2.5, transversality under money targeting and Taylor rules, Obstfeld–Rogoff |
| [Timing](PriceLevelDetermination/Timing.lean) | 22 | A.16: the alternative timing convention (A.37)–(A.49), cash and credit goods |
| [SchmittGroheUribe](PriceLevelDetermination/SchmittGroheUribe.lean) | 37 | §4.3, A.17: (A.53)–(A.56), the functions `A` and `B`, perfect-foresight uniqueness and its counterexample |
| [LocalIFT](PriceLevelDetermination/LocalIFT.lean) | 143 | A.3: the implicit-function theorem on `ℓ∞` for `F(x_t, x_{t+1}, e_t) = 0`, (A.9), second order; Propositions 2.3 and 2.6 for the exact model; the transversality condition near the steady state |
| [Nonlinear](PriceLevelDetermination/Nonlinear.lean) | 110 | A.3 applied: exact Propositions 2.7, 2.8, 2.11–2.13, (3.11) from (1.21) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
