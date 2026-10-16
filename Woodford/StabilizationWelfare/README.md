# Inflation stabilization and welfare in Lean

This is the `Woodford/StabilizationWelfare/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Woodford (2003), *Interest and Prices*, Chapter 6, "Inflation
Stabilization and Welfare" (pp. 381–463), together with the proofs in Appendix E
(pp. 692–708). Model equations hold for an arbitrary expectation operator where the book uses
one, discounted sums are genuine infinite sums with proved summability, and every welfare
approximation is stated with its terms independent of policy and its remainder written out
rather than left as "t.i.p." and "O(3)". The library contains **1069 theorems**, including the
shared core.

Each welfare approximation is stated in two layers. **Layer A** is an exact identity: the Taylor
polynomial of period (or discounted) utility equals minus the book's quadratic loss, plus an
explicit function of the exogenous variables and initial conditions, plus an explicit remainder
that a scaling lemma shows to have weighted degree at least three. **Layer B** is the statement
about actual utility: along a one-parameter family of economies of amplitude `ε` (distortions,
shocks and policy deviations all scaled by `ε`), utility equals terms independent of policy
minus `ε²/2` times the loss evaluated at the first-order solution, plus `O(ε³)` uniformly in the
date, and a policy with lower loss gives strictly higher welfare for every small `ε > 0`.

Headline results, in the namespace `Woodford.StabilizationWelfare`:
* **Approximation theory.** (1.2) needs `C³`: twice differentiability gives only `o(‖·‖²)`,
  with `x^{5/2}` as counterexample (`OneParamTaylor.taylor2_isBigO_of_contDiff`,
  `OneParamTaylor.not_taylor2_isBigO_of_contDiff_two`); (1.3), `U⁽¹⁾`, footnote 7 and `V⁽¹⁾`
  corrected (`ApproxTheory.expected_utility_corrected`, `ApproxTheory.printed13_false`,
  `ApproxTheory.expected_utility_eq_U1_add`, `ApproxTheory.fn7_false`,
  `ApproxTheory.benigno_woodford_V1`); the welfare ranking for small `ε`
  (`OneParamTaylor.welfare_ranking_of_loss`).
* **The basic welfare criterion.** Proposition 6.1 in both layers, with the distorted steady
  state from the inverse function theorem (`Prop61.prop61_layerA`, `Prop61.steadyState_family`,
  `BridgeCore.Econ.prop61_bridge`, `BridgeCore.Econ.prop61_ranking`); the exact Calvo dispersion
  law, plain and indexed, and Propositions 6.2–6.5 with `λ = κ/θ`, Layer B derived from a Calvo
  population of goods (`Moments.mix_var_meanChange`, `PriceDispersion.prop64`,
  `BridgeLinks.disc_o`, `BridgeLinks.prop64_goods`, `BridgeLinks.prop65_goods`).
* **Habit persistence.** Proposition 6.6 with the dispersion weight corrected to
  `(1 − βη)(θ⁻¹ + ω)`, so that `λ = κ/θ`; the printed weights give `(1 − βη)κ/θ`, and no
  per-period version exists (`HabitWelfare.prop66_corrected`,
  `HabitWelfare.printed_E9_discounted_false`, `HabitWelfare.printed_E9_per_period_false`,
  `BridgeCore.Econ.prop66_bridge`, `BridgeLinks.Habit.prop66_expected`).
* **The case for price stability.** Zero dispersion iff no initial dispersion and a constant
  price level, exactly (`PriceStability.calvo_zero_dispersion_iff`); zero inflation is the unique
  optimum with an efficient natural rate (`PriceStability.zero_path_optimal`), and the long-run
  claim of p. 415 in its precise form (`PriceStability.commit_limits`).
* **Transactions frictions and the zero bound.** Money demand near satiation exists and is
  locally but not globally unique (`Transactions.Assumption61.moneyDemand_local`,
  `Transactions.cexA_two_solutions`); Propositions 6.7–6.8 with `s_m` and (4.17) corrected
  (`Transactions.prop_6_7_layerA`, `Transactions.loss_4_17`, `BridgeLinks.prop68_primitive`);
  Proposition 6.9 from a proved two-constraint Kuhn–Tucker theorem (`ZLB.kkt_exists`,
  `ZLB.envelope`, `ZLB.prop_6_9`).
* **Asymmetric disturbances and sticky wages.** Propositions 6.10–6.13, with `κ` a harmonic,
  not geometric, mean and Proposition 6.13's omitted proof supplied
  (`TwoSectorWelfare.prop_6_11_calvo`, `TwoSectorWelfare.printed_geometric_average_false`,
  `StickyWageWelfare.prop_6_12_layerA`, `StickyWageWelfare.prop_6_13_calvo`,
  `BridgeLinks.prop611_primitive`, `BridgeLinks.prop613_primitive`).
* **Cost-push shocks and large distortions.** Natural and efficient output from the implicit
  function theorem (`CostPush.implicit_natural_efficient`); (5.1) with its sign corrected
  (`LargeDistortions.eq51_exact`, `LargeDistortions.eq51_printed_false`); the second-order AS
  relation (5.4) derived from the Calvo model (`LargeDistortions.calvoAS_of_primitives`,
  `LargeDistortions.eq54`); Propositions 6.14–6.15 in both layers, with the first-order term of
  6.14 that prevents ranking and its removal in 6.15 (`BridgeExtensions.prop614_first_order`,
  `BridgeExtensions.prop615_layerB`, `BridgeLinks.prop615_goods_layerB`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise.

Not covered: the Chapter 7 material the chapter anticipates (existence and convergence of the
optimal commitment path behind p. 415, the optimality claim of footnote 71, and optimal long-run
inflation for any `Φ`); the numerical Figures 6.1–6.6 and the optimisation outputs behind
Figure 6.1 and Table 6.2, of which only the exact arithmetic claims are formalised; and, for the
Layer B forms of Propositions 6.7, 6.10 and 6.12, the change of variables from the efficient to
the distorted steady state.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](StabilizationWelfare/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated from the Galí projects) |
| [Expectations](StabilizationWelfare/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; forward series; the pull-out property |
| [ExpectationsFiniteTree](StabilizationWelfare/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out |
| [ForwardSolution](StabilizationWelfare/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` for `\|a\| < 1`, the continuum for `\|a\| ≥ 1` (restated from the Chapter 2 and 3 projects); `E_t` and dominated series |
| [OneParamTaylor](StabilizationWelfare/OneParamTaylor.lean) | 38 | §1: one-variable Taylor bounds and the `x^{5/2}` counterexample to (1.2); second derivatives along curves, (1.5)–(1.8); welfare ranking; finite-state expectations; order lemmas |
| [ExpLogCES](StabilizationWelfare/ExpLogCES.lean) | 34 | (2.6), (E.5), App. E.2, p. 425: exponential and logarithm bounds, cross-sectional moments, the CES cumulant expansion, the output and price indices, `i* = −Δ̄ + O(Δ̄²)` |
| [ApproxTheory](StabilizationWelfare/ApproxTheory.lean) | 45 | §1: multivariate (1.2), (1.3) corrected, `U⁽⁰⁾`, `U⁽¹⁾`, footnote 7, (1.5)–(1.8), the Benigno–Woodford form (1.9)–(1.10) and `V⁽¹⁾` |
| [Sequences](StabilizationWelfare/Sequences.lean) | 40 | Bounded sequences, lags, telescoping and discounted sums; the integrated and discounted dispersion recursion of p. 400 |
| [Moments](StabilizationWelfare/Moments.lean) | 13 | (E.8), (2.12), (2.19): the exact Calvo mixture variance, moments of affine maps, the Calvo slope (restated from Chapter 3) |
| [CrossSection](StabilizationWelfare/CrossSection.lean) | 27 | §2.2, App. E.2: moments over a goods probability space, (2.12), two-point dispersion, the indexed Calvo mixture (2.24), the log-mean-exp bounds for (E.5) and p. 695 |
| [Prop61](StabilizationWelfare/Prop61.lean) | 29 | §2.1, App. E.1: (2.2)–(2.9), the steady-state family, (E.2)–(E.6), Proposition 6.1 (Layer A), (2.11), (2.13) |
| [PriceDispersion](StabilizationWelfare/PriceDispersion.lean) | 25 | §2.2, App. E.2: the New Classical model and Proposition 6.2, Propositions 6.3–6.5 (Layer A), footnote 26 |
| [HabitWelfare](StabilizationWelfare/HabitWelfare.lean) | 84 | §2.2, App. E.3: (E.10)–(E.13), the flexible-price relation, Proposition 6.6 corrected, (2.28)–(2.31), the habit root of Chapter 5 restated |
| [PriceStability](StabilizationWelfare/PriceStability.lean) | 53 | §3: the exact Calvo cross-section as measures, price stability and dispersion, §3.1, (3.1)–(3.5), the steady state of p. 415 |
| [Transactions](StabilizationWelfare/Transactions.lean) | 57 | §4.1, App. E.4: Assumption 6.1 and money demand, (4.1)–(4.17), Propositions 6.7–6.8 (Layer A), Tables 6.1–6.2 |
| [ZLB](StabilizationWelfare/ZLB.lean) | 35 | §4.2, App. E.5: the zero-bound constraint, Kuhn–Tucker for two convex constraints, the envelope relation (E.24), Proposition 6.9, (4.22) |
| [TwoSectorWelfare](StabilizationWelfare/TwoSectorWelfare.lean) | 78 | §4.3, App. E.6–E.7: (E.27)–(E.32), Propositions 6.10–6.11 (Layer A), the Calvo recursion on a weighted cross-section, the Aoki and equal-stickiness cases, Table 6.3 |
| [StickyWageWelfare](StabilizationWelfare/StickyWageWelfare.lean) | 38 | §4.4, App. E.8: (E.34)–(E.36), Propositions 6.12–6.13 (Layer A), (4.30), Table 6.4 |
| [CostPush](StabilizationWelfare/CostPush.lean) | 20 | §4.5: natural and efficient output by the implicit function theorem, (4.32)–(4.39), footnotes 67–71 |
| [LargeDistortions](StabilizationWelfare/LargeDistortions.lean) | 84 | §5: (5.1) corrected, Proposition 6.14, Assumption 6.2, the Calvo reset problem and (5.4) derived, Proposition 6.15, (5.9)–(5.11) |
| [Links](StabilizationWelfare/Links.lean) | 18 | App. E.1–E.2: the CES and price-index atoms, a Calvo goods population, the dispersion hypotheses of (2.28)–(2.29), Propositions 6.8 and 6.14 discharged |
| [BridgeCore](StabilizationWelfare/BridgeCore.lean) | 108 | Layer B for Propositions 6.1–6.6: uniform-in-`t` orders, the Taylor step at the efficient steady state, actual utility, discounted and expected forms, rankings |
| [BridgeExtensions](StabilizationWelfare/BridgeExtensions.lean) | 93 | Layer B for (5.1), (5.4) and Propositions 6.7–6.15 along any family, the one-sided expansion at satiation, the first-order term of Proposition 6.14 |
| [BridgeLinks](StabilizationWelfare/BridgeLinks.lean) | 42 | Layer B from primitives: `π̄ − π = O(ε²)` uniformly, Propositions 6.4–6.5 from a goods population, the money-demand residual, Propositions 6.8, 6.11, 6.13–6.15 discharged, Proposition 6.6 under uncertainty |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
