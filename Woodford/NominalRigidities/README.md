# Optimizing models with nominal rigidities in Lean

This is the `Woodford/NominalRigidities/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Woodford (2003), *Interest and Prices*, Chapter 3, "Optimizing Models
with Nominal Rigidities" (pp. 139–236), together with the proofs in Appendix B (pp. 656–669).
Model equations hold for an arbitrary expectation operator, so results cover perfect foresight
and genuine uncertainty; log-linear equations are exact derivatives of the nonlinear model, and
infinite-horizon objectives and forward solutions are genuine series. The library contains
**1068 theorems**, including the shared core.

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
  Proposition 3.5 from the primitives of the baseline model (`Links.prop35_baseline`).
* **Persistence.** Propositions 3.6 and 3.7 for any expectation system
  (`Persistence.prop_3_6_stochastic`, `SpendingGrowth.prop_3_7_stochastic`), the contract
  multiplier and its continuous-time limit (`Persistence.contractMult_tendsto`).
* **Sectors, delays and indexation.** Proposition 3.8 (`TwoSector.prop_3_8_full`), delayed and
  indexed price setting with existence and uniqueness of every impulse response
  (`Delays.irf_existsUnique_nom`, `Delays.cubic_roots_location`), and an event-tree equilibrium
  with the Figure 3.12 property (`Delays.fig_3_12_tree_equilibrium`).
* **Sticky wages.** Proposition 3.9 (`StickyWages.prop_3_9`), the real-wage dynamics (4.22) and
  their flexible limits (`StickyWages.secondOrder_existsUnique`,
  `StickyWages.realWage_flexible_limit`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise.

Not covered: the Galí–Gertler formulas for the share of backward-looking price setters (pp.
216–217), which come from the external paper, are not formalised, only the hybrid form and its
weights; purely numerical figure shapes and the empirical remarks (the Sbordone fit, VAR
evidence) are not formalised; the second-order dispersion terms behind (4.10) are left out, as
the book does not treat them either. For Proposition 3.4 with `ω̃θ < 0`, uniqueness outside the
difference-stationary class is proved only under perfect foresight.

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

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
