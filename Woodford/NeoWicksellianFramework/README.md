# A neo-Wicksellian framework in Lean

This is the `Woodford/NeoWicksellianFramework/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Woodford (2003), *Interest and Prices*, Chapter 4, "A Neo-Wicksellian
Framework for the Analysis of Monetary Policy" (pp. 237–319), together with the proofs in
Appendix C (pp. 670–686). Model equations hold for an arbitrary expectation operator, so results
cover perfect foresight and genuine uncertainty; log-linear equations are exact derivatives of the
nonlinear model, and determinacy means existence and uniqueness of a bounded adapted equilibrium
for every bounded forcing, proved rather than assumed from a root count. The library contains
**1108 theorems**, including the shared core.

Headline results, in the namespace `Woodford.NeoWicksellianFramework`:
* **The basic model and the natural rate.** The IS relation and the Phillips curve as exact
  derivatives of the nonlinear model (`BasicModel.euler_deriv`, `BasicModel.prop35`), the forward
  IS relation exactly when the limit (1.9) exists (`BasicModel.eq18_iff_eq19`), the natural rate
  existing iff a boundary condition holds and `C²` in the disturbances
  (`NaturalRate.natRate_existsUnique_smooth`), and Proposition 4.1 (`NaturalRate.prop41`).
* **Root location and Blanchard–Kahn.** Propositions C.1 and C.2 as exact equivalences
  (`SchurCohn.bothOutside_iff_cases`, `SchurCohn.oneInTwoOut_iff_cases`), and a proved
  determinacy theory: for 2×2 forward systems (`BlanchardKahn.fwdDeterminate_iff`) and for 3×3
  systems with one predetermined variable, where the root count needs a genericity condition the
  book omits (`BlanchardKahn.determinate3_iff`, `BlanchardKahn.diagEx_not_determinate`).
* **General Blanchard–Kahn theorem.** The counting rule the appendix assumes, proved for any
  number of non-predetermined and predetermined variables and any `ExpectationSystem`: determinate
  iff no eigenvalue on the unit circle, a stable subspace of dimension equal to the number of
  predetermined variables, and genericity (`GeneralBK.determinate_iff`,
  `GeneralBK.determinate_iff_count`, `GeneralBKLinks.determinateOn_iff`). The pencil form
  `A₀ E_t y_{t+1} = A₁ y_t + w_t` is covered, including singular `A₀` as in King–Watson and
  Klein (`GeneralBKPencil.determinatePencil_iff_count`,
  `GeneralBKSingular.determinatePencil_iff_general`); the 2×2 and 3×3 theorems are recovered
  from it (`GeneralBKLinks.determinate2_iff_recovered`,
  `GeneralBKLinks.determinate3_iff_recovered`), and the Proposition 4.4 model is determinate for
  every bounded adapted forcing vector (`GeneralBKLinks.prop44_determinate3_iff`).
* **Determinacy under interest-rate rules.** Propositions 4.2 and 4.3 (`Determinacy2.prop_4_2`,
  `Determinacy2.prop_4_3`), Proposition 4.4 corrected: false without feedback
  (`ThreeByThree.prop44`, `ThreeByThree.prop44_printed_false`), Propositions 4.5 and 4.7
  (`Determinacy2Forward.prop_4_5`, `ThreeByThree.prop47`) and necessity in Proposition 4.6
  (`ThreeByThree.prop46_necessity`).
* **Learning.** E-stability under sample-mean and regression learning, Propositions 4.8 and 4.9
  (`Determinacy2Learning.prop_4_8`, `Learning.BullardMitra.prop_4_9`), with every eigenvalue of a
  Kronecker product a product of eigenvalues (`KroneckerSpectrum.isEig_kronecker_iff`), and
  Preston's long-horizon forms with the exact condition for (2.29) (`Learning.Preston.gapIS_iff`).
* **Determinants of inflation and targeting rules.** The forward solution (2.34) with its sign
  corrected (`InflationDeterminants.forwardSys_eq_formula`), unique equilibria under inertial
  rules and inflation inertia, with an exact determinacy condition for the latter
  (`InflationDeterminants.inertial_equilibrium_existsUnique`,
  `InflationDeterminants.inertia_determinate_iff`), and strict versus forecast targeting, also
  under the zero bound (`TargetingRules.strict_targeting_existsUnique`,
  `TargetingRules.forecastTarget_not_countable`, `TargetingRules.forecastTarget_zlb_not_countable`).
* **Money and fiscal policy.** The money-in-utility model with the corrected elasticity (3.12)
  and the continuity of determinacy in `χ` (`Money.mc311`, `Money.fn70`), and Proposition 4.11
  with the non-degeneracy condition the book omits (`Fiscal.prop411_ricardian`,
  `Fiscal.prop411_nonricardian_noTP`, `Fiscal.prop411_printed_fails`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise.

Not covered: sufficiency in Proposition 4.6, which the book omits, and Proposition 4.10 (Preston)
are deferred to a later project on the general theory; the convergence of the E-stability
differential equation and the stochastic-approximation results of pp. 265–266, cited from Evans
and Honkapohja, are not formalised, and E-stability is defined through the eigenvalues of
`DT − I`; the numerical impulse responses and phase diagrams in the figures are not formalised,
only the claims the text makes about them.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](NeoWicksellianFramework/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated from the Galí projects) |
| [Expectations](NeoWicksellianFramework/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; forward series; the pull-out property |
| [ExpectationsFiniteTree](NeoWicksellianFramework/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out |
| [ForwardSolution](NeoWicksellianFramework/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` for `\|a\| < 1`, the continuum for `\|a\| ≥ 1` (restated from the Chapter 2 and 3 projects); `E_t` and dominated series |
| [BasicModel](NeoWicksellianFramework/BasicModel.lean) | 59 | §1: the equilibrium conditions (1.1)–(1.6), (1.7)–(1.11) as exact derivatives, (1.8)–(1.9), n. 12, the gap form (1.12)–(1.15) |
| [NaturalRate](NeoWicksellianFramework/NaturalRate.lean) | 49 | §2.1: zero inflation and natural output, (2.1)–(2.3), existence and smoothness of the natural rate, Proposition 4.1, the p. 251 simple-rule condition |
| [SchurCohn](NeoWicksellianFramework/SchurCohn.lean) | 45 | C.1: Propositions C.1 and C.2 as exact equivalences, (C.15), the printed-proof errors |
| [BlanchardKahn](NeoWicksellianFramework/BlanchardKahn.lean) | 90 | C.1: determinacy of `2 × 2` forward systems and of `3 × 3` systems with one predetermined variable, with genericity |
| [ThreeByThree](NeoWicksellianFramework/ThreeByThree.lean) | 53 | §2.2, C.3, C.5, C.6: Proposition 4.4 corrected, necessity in Proposition 4.6, Proposition 4.7 |
| [Determinacy2](NeoWicksellianFramework/Determinacy2.lean) | 72 | §2.2, C.2: the model under (1.14), (2.5)–(2.7), Propositions 4.2 and 4.3, n. 27, the Taylor numbers |
| [Determinacy2Forward](NeoWicksellianFramework/Determinacy2Forward.lean) | 24 | §2.2, C.4: Proposition 4.5, Figure 4.1, the Clarida–Galí–Gertler numbers, (2.14)–(2.15) |
| [KroneckerSpectrum](NeoWicksellianFramework/KroneckerSpectrum.lean) | 16 | C.7: the spectrum of Kronecker products and block-diagonal matrices, (C.29) |
| [Determinacy2Learning](NeoWicksellianFramework/Determinacy2Learning.lean) | 47 | §2.3: temporary equilibrium (2.16)–(2.18), the sample-mean T-map (2.19)–(2.23), Proposition 4.8, iterative E-stability |
| [Learning](NeoWicksellianFramework/Learning.lean) | 90 | §2.3, C.7: phase diagrams (nn. 38–39), regression learning (2.24)–(2.27), Proposition 4.9, Preston's (2.28)–(2.30) |
| [Money](NeoWicksellianFramework/Money.lean) | 62 | §3: the LM curve (3.1)–(3.3), (3.4)–(3.14) with real-balance effects, nn. 62, 70, 71 |
| [Fiscal](NeoWicksellianFramework/Fiscal.lean) | 47 | §4, C.8: (4.1)–(4.5), locally Ricardian rules, the stacked system, Proposition 4.11 corrected |
| [InflationDeterminants](NeoWicksellianFramework/InflationDeterminants.lean) | 110 | §2.4–2.5: (2.31)–(2.35) with (2.34) corrected, inertial rules, inflation inertia (2.36)–(2.39), n. 47, pp. 287–288 |
| [TargetingRules](NeoWicksellianFramework/TargetingRules.lean) | 34 | §2.6: (2.40)–(2.44), strict and forecast targeting, the zero lower bound |
| [Links](NeoWicksellianFramework/Links.lean) | 11 | §2–§3: the determinacy, learning, inertial-rule, Preston and money modules linked to each other and to the basic model |
| [InvariantSplit](NeoWicksellianFramework/InvariantSplit.lean) | 52 | C.1: eigenvalues with multiplicity, the stable invariant subspace (dimension = stable count), its graph and the block-triangular split |
| [GeneralBKForward](NeoWicksellianFramework/GeneralBKForward.lean) | 17 | C.1: forward systems over any finite index type (restated from `BlanchardKahn`) |
| [GeneralBK](NeoWicksellianFramework/GeneralBK.lean) | 39 | C.1: the general Blanchard–Kahn theorem for any `ExpectationSystem`: sufficiency, and necessity by resonance, multiplicity and non-existence |
| [GeneralBKPencil](NeoWicksellianFramework/GeneralBKPencil.lean) | 7 | C.1: the pencil form `A₀ E_t y_{t+1} = A₁ y_t + w_t` with invertible `A₀` |
| [GeneralBKSingular](NeoWicksellianFramework/GeneralBKSingular.lean) | 49 | C.1: singular `A₀` (King–Watson, Klein): regularity, the Fitting split, infinite eigenvalues counted as unstable |
| [GeneralBKLinks](NeoWicksellianFramework/GeneralBKLinks.lean) | 27 | C.1, C.3: any index type; Propositions C.1 and C.2 recovered; the Proposition 4.4 model determinate for every forcing vector |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
