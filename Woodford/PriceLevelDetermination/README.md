# Price-level determination in Lean

This is the `Woodford/PriceLevelDetermination/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Woodford (2003), *Interest and Prices*, Chapter 2, "Price-Level
Determination under Interest-Rate Rules" (pp. 61–138), together with the proofs in Appendix A
(pp. 627–655). Model equations hold for an arbitrary expectation operator, so results cover
perfect foresight and genuine uncertainty; log-linear equations are exact derivatives of the
nonlinear model, and the exact nonlinear model is linked to them by implicit-function theorems
on bounded sequences and on bounded processes under uncertainty, for scalar equations and for
`n`-dimensional systems with predetermined variables. The library contains **1404 theorems**,
including the shared core.

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
* **The implicit-function theorem under uncertainty.** The Appendix A.3 argument for
  `E_t[G(x_t, x_{t+1}, E_t x_{t+1}, e_t)] = 0` on bounded processes: `a + bL` with
  `Lx = (E_t x_{t+1})_t` is invertible iff `|b| < |a|` (`LocalIFTStochastic.Ops.isUnit_TOpS_iff`),
  and the stochastic equilibrium is locally unique, `C¹` in the disturbances, with the linear
  rational-expectations solution as its first-order term
  (`LocalIFTStochastic.Ops.local_determinacyS_loc`). As in the scalar and `n`-dimensional
  settings, `O(‖e‖²)` accuracy holds under `C²` and fails for a `C¹` model (E18)
  (`LocalIFTStochastic.Ops.second_orderS_loc`, `LocalIFTStochastic.Ops.not_second_order_of_C1S`).
  The form `F(x_t, E_t x_{t+1}, e_t) = 0` needs informational closure
  (`LocalIFTStochastic.Ops.solvesS_liftI_iff`, `LocalIFTStochastic.formI_needs_closure`).
* **The Chapter 2 models under uncertainty.** Local determinacy and indeterminacy of the exact
  stochastic models of Propositions 2.3, 2.6–2.8 and 2.11–2.13
  (`LocalIFTStochastic.Models.taylor_local_determinacyS`,
  `LocalIFTStochastic.Models.nsi_local_determinacyS`), genuinely random sunspot equilibria in the
  indeterminate cases (`LocalIFTStochasticModels.random_sunspotII`,
  `LocalIFTStochasticModels.taylor_random_sunspot`), the transversality condition in every state
  (`LocalIFTStochasticModels.stochTVC_of_bounds`, `LocalIFTStochasticModels.taylor_tvcS`), and the
  book's level forms proved equivalent to the log forms
  (`LocalIFTStochasticModels.taylor_solvesS_iff`).
* **The Schmitt-Grohé–Uribe example under uncertainty.** No self-fulfilling inflation on any
  expectation system (`SGUStochastic.stoch_no_hyperinflation`) and a unique equilibrium on every
  finite event tree (`SGUStochastic.sgu_finiteTree_unique`), but the p. 137 claim of uniqueness
  among all stochastic equilibria is refuted by a perpetual sunspot on a geometric probability
  space with Mathlib conditional expectation (`SGUStochasticMeasure.sgu_sunspot_measure`). That
  sunspot cannot live on a core expectation system on `ℕ`, whose conditional expectations are
  finitely supported (`SGUStochasticMeasure.expectationSystem_finite_support`,
  `SGUStochasticMeasure.no_expectationSystem_geomE`).
* **`n`-dimensional systems with predetermined variables.** The root condition (A.9) made exact
  (`LinearSystems.linDeterminate_iff`), with counterexamples to both directions of the printed
  count (`LinearSystems.book_count_not_sufficient`, `LinearSystems.book_count_not_necessary`); a
  root on the unit circle rules out existence for any `f₃`
  (`LinearSystemsUnit.not_surjective_of_unit_root`). The local theorem at any steady state, with
  its converse and second-order bound (`LocalIFTSystemsBar.local_determinacy_at`,
  `LocalIFTSystemsBar.isUnit_iff_local_determinacy_at`, `LocalIFTSystemsBar.second_order_at`);
  the converse is sharp, since `x_t³ = e_t` has exactly one bounded equilibrium although the root
  condition fails (`LocalIFTSystems.cube_unique_without_root_condition`). Applied to the inertial
  rule of Proposition 2.8, where the printed count never holds
  (`LocalIFTSystemsApps.inertial_iff`, `LocalIFTSystemsApps.inert_book_count_fails`), and the
  scalar theorem is recovered as `n = 1`
  (`LocalIFTSystemsApps.scalar_local_determinacy_recovered`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise.

Not covered: systems with `n > 1` equations or predetermined variables under uncertainty; the
stochastic implicit-function theorem is for one forward-looking equation, and the `n`-dimensional
theorem is for perfect foresight. Figures 2.1–2.5 are formalised only through their closed forms
and spot values.

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
| [LocalIFTStochastic](PriceLevelDetermination/LocalIFTStochastic.lean) | 118 | A.3 under uncertainty: the implicit-function theorem on `L∞` processes for `E_t[G(x_t, x_{t+1}, E_t x_{t+1}, e_t)] = 0`, (A.11)–(A.13), first and second order (E18); informational closure; Propositions 2.3, 2.6–2.8 and 2.11–2.13 under uncertainty |
| [LocalIFTStochasticModels](PriceLevelDetermination/LocalIFTStochasticModels.lean) | 38 | Random sunspot equilibria on the coin-flip tree; the transversality condition (1.24) in every state; the models' level forms (1.21) equivalent to their log forms |
| [SGUStochastic](PriceLevelDetermination/SGUStochastic.lean) | 39 | p. 137, A.17 under uncertainty: no self-fulfilling inflation, uniqueness on finite trees, the perpetual-sunspot refutation |
| [SGUStochasticMeasure](PriceLevelDetermination/SGUStochasticMeasure.lean) | 15 | p. 137: the refutation on a geometric probability space with Mathlib conditional expectation; core expectation systems on `ℕ` are finitely supported |
| [SystemsBK](PriceLevelDetermination/SystemsBK.lean) | 108 | The general Blanchard–Kahn theorem (copied from the Chapter 4 project) |
| [SystemsBKPencil](PriceLevelDetermination/SystemsBKPencil.lean) | 56 | Blanchard–Kahn for regular and singular pencils (copied from the Chapter 4 project) |
| [LinearSystems](PriceLevelDetermination/LinearSystems.lean) | 61 | A.3, (A.8)–(A.10): `n`-dimensional linearised systems with predetermined variables, (A.9) made exact, counterexamples to the printed root count, which half fails |
| [LinearSystemsUnit](PriceLevelDetermination/LinearSystemsUnit.lean) | 8 | (A.9)–(A.10): a root on the unit circle rules out existence for any `f₃` |
| [LocalIFTSystems](PriceLevelDetermination/LocalIFTSystems.lean) | 65 | A.3: the implicit-function theorem for `F(x_{t−1}, x_t, x_{t+1}, e_t) = 0` on `ℓ∞(ℕ, ℝⁿ)`; first and second order; the converse; the `x³ = e` example |
| [LocalIFTSystemsBar](PriceLevelDetermination/LocalIFTSystemsBar.lean) | 7 | A.3: local determinacy, the converse and second order at an arbitrary steady state |
| [LocalIFTSystemsApps](PriceLevelDetermination/LocalIFTSystemsApps.lean) | 38 | A.3 applied: the inertial rule (2.12) as a two-dimensional system; the scalar theorem as `n = 1`; E18 in `n` dimensions |

## Relation to the Woodford Chapter 4 project

`SystemsBK` and `SystemsBKPencil` are verbatim copies of five modules of the Chapter 4 project
([NeoWicksellianFramework](../NeoWicksellianFramework/README.md)): `InvariantSplit`,
`GeneralBKForward` and `GeneralBK` in `SystemsBK`, and `GeneralBKPencil` and `GeneralBKSingular`
in `SystemsBKPencil`. Each is nested as a sub-namespace (for example
`SystemsBK.GeneralBK.determinate_iff`); only the namespace and `open` lines are renamed and one
cross-module reference in a proof is fully qualified, so the project builds on its own and
imports nothing from Chapter 4. The docstrings keep the original Appendix C citations. Here they
are tools: `LinearSystems` writes (A.10) as a pencil in `(x_t, x_{t−1})` and makes (A.9) exact
with the singular-pencil theorem `SystemsBKPencil.GeneralBKSingular.determinatePencil_iff_general`,
and `LinearSystemsUnit` adapts the resonance argument `SystemsBK.GeneralBK.no_bounded_resonance`.
`GeneralBKLinks` (Propositions C.1–C.2 and the Proposition 4.4 model) is not copied.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
