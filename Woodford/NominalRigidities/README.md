# Optimizing models with nominal rigidities in Lean

This is the `Woodford/NominalRigidities/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Woodford (2003), *Interest and Prices*, Chapter 3, "Optimizing Models
with Nominal Rigidities" (pp. 139–236), together with the proofs in Appendix B (pp. 656–669).
Model equations hold for an arbitrary expectation operator, so results cover perfect foresight
and genuine uncertainty; log-linear equations are exact derivatives of the nonlinear model, and
infinite-horizon objectives and forward solutions are genuine series. The library contains
**1182 theorems**, including the shared core.

Headline results, in the namespace `Woodford.NominalRigidities`:
* **Flexible prices and the natural rate.** Dixit–Stiglitz demand as genuine cost minimisation
  (`DixitStiglitz.priceIndex_isLeast_unitCost`), real marginal cost and its elasticities as exact
  derivatives (`MarginalCost.eq_1_15`), and Proposition 3.1 corrected: Assumption 3.1 gives
  neither existence nor uniqueness of the natural rate (`FlexiblePrices.prop_3_1`,
  `FlexiblePrices.twoRoots_counterexample`, `FlexiblePrices.noNaturalRate_baseline`).
* **Prices fixed in advance.** The New Classical Phillips curve (`Predetermined.NC.prop_3_2`) and
  the corrected output formula (1.33) (`Predetermined.PC.output_corrected`,
  `Predetermined.printed_1_33_counterexample`).
* **Strategic complementarity.** The notional supply curve and Proposition 3.3 built from the
  Kimball aggregator and intermediate inputs (`StrategicComplementarity.prop_3_3`,
  `Kimball.prop_3_3_from_psi`), and every entry of Table 3.1
  (`StrategicComplementarity.table31_rounding`).
* **Calvo pricing and the New Keynesian Phillips curve.** Proposition 3.4 with its exact solution
  class and the continuum outside it (`Calvo.prop34_exists_iff`, `Calvo.prop34_continuum`), and
  Proposition 3.5 from the primitives of the baseline model (`Links.prop35_baseline`). With
  `ω̃θ < 0` the solution is unique among all predetermined solutions for every expectation system
  (`TidyR5Prop34Uncertainty.prop34_existsUnique_of_w_neg`); on a genuine probability space it
  exists and is unique in the class with `L¹` forward sums
  (`TidyR5Prop34MeasureExists.prop34_existsUnique_measure`), and without that condition an i.i.d.
  economy has a second solution (`TidyR5Prop34NonUnique.prop34_not_unique_iid`,
  `TidyR5Prop34NonUnique.cex_not_L1Fwd`).
* **Persistence.** Propositions 3.6 and 3.7 for any expectation system
  (`Persistence.prop_3_6_stochastic`, `SpendingGrowth.prop_3_7_stochastic`), the contract
  multiplier and its continuous-time limit (`Persistence.contractMult_tendsto`).
* **Sectors, delays and indexation.** Proposition 3.8 (`TwoSector.prop_3_8_full`), delayed and
  indexed price setting with existence and uniqueness of every impulse response
  (`Delays.irf_existsUnique_nom`, `Delays.cubic_roots_location`), an event-tree equilibrium
  with the Figure 3.12 property (`Delays.fig_3_12_tree_equilibrium`), and the Galí–Gertler hybrid
  model derived for every expectation system, which reproduces the weights of (3.6) iff `γ = 0`
  or `β = 1`, and at `β = 1` reproduces (3.6) exactly for a unique re-chosen Calvo parameter
  (`TidyR5GaliGertler.gg_hybrid_iff`,
  `TidyR5GaliGertler.gg_weights_match_iff`,
  `TidyR5GaliGertlerUnique.gg_identical_beta_one_existsUnique`).
* **Sticky wages.** Proposition 3.9 (`StickyWages.prop_3_9`), the real-wage dynamics (4.22) and
  their flexible limits (`StickyWages.secondOrder_existsUnique`,
  `StickyWages.realWage_flexible_limit`), and the wage- and price-dispersion terms dropped in
  (4.10), exact for isoelastic preferences and technology, and `O(s²)` with zero derivative for
  any `v_h` and `f` with locally Lipschitz derivatives (`TidyR5Dispersion.logv_decomposition`,
  `TidyR5DispersionGeneral.hasDerivAt_hoursGapGen`,
  `TidyR5DispersionGeneral.hasDerivAt_outputGapGen`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise.

Not covered: purely numerical figure shapes and the empirical remarks (the Sbordone fit, VAR
evidence, Galí and Gertler's point estimates) are not formalised.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](NominalRigidities/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated from the Galí projects) |
| [Expectations](NominalRigidities/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; forward series; the pull-out property |
| [ExpectationsFiniteTree](NominalRigidities/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out |
| [ForwardSolution](NominalRigidities/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` for `\|a\| < 1`, the continuum for `\|a\| ≥ 1` (restated from the Chapter 2 project); `E_t` and dominated series |
| [DixitStiglitz](NominalRigidities/DixitStiglitz.lean) | 62 | §1.1, §2.5, §4.1: (1.2)–(1.5) as cost minimisation, finite CES for any `η`, the Cobb–Douglas limit (n. 61), the nested aggregator (2.22)–(2.23), labour demand (4.1)–(4.2) |
| [MarginalCost](NominalRigidities/MarginalCost.lean) | 34 | §1.1: technology (1.7)–(1.9), real marginal cost (1.10)–(1.11), the elasticities (1.15)–(1.16) as exact derivatives |
| [FlexiblePrices](NominalRigidities/FlexiblePrices.lean) | 44 | §1.1: (1.12)–(1.14), (1.18), Assumption 3.1, Proposition 3.1 corrected, the natural rate and its counterexamples |
| [Predetermined](NominalRigidities/Predetermined.lean) | 65 | §1.2–1.3: (1.22)–(1.33), Proposition 3.2, (1.26) on event trees, (1.33) corrected, Figure 3.1 |
| [StrategicComplementarity](NominalRigidities/StrategicComplementarity.lean) | 37 | §1.4: (1.34)–(1.43), the sources of complementarity, Proposition 3.3, Table 3.1 |
| [Kimball](NominalRigidities/Kimball.lean) | 28 | B.1–B.2: Kimball demand (B.1)–(B.5), Leontief inputs (1.42), (B.7)–(B.9), Proposition 3.3 from primitives |
| [QuadraticRoots](NominalRigidities/QuadraticRoots.lean) | 59 | §2.1, B.3: the quadratic `βλ² − (1 + β + c)λ + 1`, its roots and lag factorisation, `ξ` and `κ`, the p. 660 identity corrected |
| [Calvo](NominalRigidities/Calvo.lean) | 85 | §2.1, B.3: the index (2.1), the reset problem (2.2)–(2.8) as exact derivatives, Proposition 3.4 with its solution class |
| [NKPC](NominalRigidities/NKPC.lean) | 25 | §2.2, B.4: (2.12)–(2.14), Proposition 3.5, comparative statics of `κ` |
| [Persistence](NominalRigidities/Persistence.lean) | 116 | §2.3, B.5: (2.16)–(2.20), Proposition 3.6 deterministic and stochastic, the contract multiplier and its limit, the p. 191–196 numbers |
| [SpendingGrowth](NominalRigidities/SpendingGrowth.lean) | 49 | §2.4, B.6: (2.21), Proposition 3.7, (B.22)–(B.26), the hump |
| [TwoSector](NominalRigidities/TwoSector.lean) | 61 | §2.5, B.7: (2.25)–(2.28), Proposition 3.8, (B.27)–(B.33) corrected, under uncertainty |
| [Delays](NominalRigidities/Delays.lean) | 88 | §3: (3.1)–(3.7), delayed and indexed price setting, Figures 3.11–3.15, an event-tree equilibrium |
| [WageSetting](NominalRigidities/WageSetting.lean) | 81 | §4.1: the wage index, (4.3)–(4.7), the price-setter instance behind (4.9), regularity from primitives |
| [StickyWages](NominalRigidities/StickyWages.lean) | 107 | §4.1–4.2: (4.8)–(4.25), Proposition 3.9, the real-wage dynamics and their flexible limits, Figure 3.18 |
| [Links](NominalRigidities/Links.lean) | 19 | §1–§4: the baseline model linked to the Calvo, persistence, delay and sticky-wage modules; Proposition 3.5 from primitives |
| [TidyR5Prop34Uncertainty](NominalRigidities/TidyR5Prop34Uncertainty.lean) | 13 | §2.1, B.3: `E_t` commutes with every pointwise convergent series; Proposition 3.4 with `ω̃θ < 0` unique among all solutions, for every expectation system |
| [TidyR5ExpectationsMeasure](NominalRigidities/TidyR5ExpectationsMeasure.lean) | 17 | Conditional expectations on a probability space, a.e. forms; the bridge to `ExpectationSystem` (restated from the Cochrane projects) |
| [TidyR5ExpectationsMeasureIID](NominalRigidities/TidyR5ExpectationsMeasureIID.lean) | 12 | An i.i.d. economy with its natural filtration; the uniform law (restated from the Cochrane projects) |
| [TidyR5Prop34Measure](NominalRigidities/TidyR5Prop34Measure.lean) | 4 | §2.1, B.3: Proposition 3.4 with `ω̃θ < 0` on a probability space, unique with `L¹` forward sums |
| [TidyR5Prop34NonUnique](NominalRigidities/TidyR5Prop34NonUnique.lean) | 23 | §2.1, B.3: without `L¹` sums a second solution on an i.i.d. economy (a doubling bet); the `L¹` condition is sharp |
| [TidyR5Dispersion](NominalRigidities/TidyR5Dispersion.lean) | 13 | §4.1, (4.10): the hours- and output-dispersion terms, exact for isoelastic primitives, second order |
| [TidyR5GaliGertler](NominalRigidities/TidyR5GaliGertler.lean) | 8 | §3.2, pp. 216–217: the Galí–Gertler hybrid curve from the model; when it reproduces (3.6) |
| [TidyR5Prop34MeasureExists](NominalRigidities/TidyR5Prop34MeasureExists.lean) | 12 | §2.1, B.3: (2.9) on a probability space; existence and uniqueness in the `L¹` class |
| [TidyR5DispersionGeneral](NominalRigidities/TidyR5DispersionGeneral.lean) | 9 | §4.1, (4.10): the dispersion gaps are `O(s²)` with zero derivative for general `v_h` and `f` |
| [TidyR5GaliGertlerUnique](NominalRigidities/TidyR5GaliGertlerUnique.lean) | 3 | §3.2, p. 217: the Galí–Gertler model reproducing (3.6) at `β = 1` is unique |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
