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
**1437 theorems**, including the shared core.

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
* **Proposition 4.6 corrected, sufficiency included.** The book proves only necessity. Here
  equilibrium under (2.12) is determinate iff (2.9) ∧ (2.13) ∧ (`φ_π > 0 ∨ φ_x > 0`)
  (`Prop46Sufficiency.prop46`). As printed the iff is false: with `φ_π = φ_x = 0` and `ρ > 1`,
  (2.9) and (2.13) hold but the rule makes the interest rate exogenous and equilibrium is not
  determinate (`Prop46Sufficiency.prop46_printed_false`), the same failure as Proposition 4.4.
  Case II of Proposition C.2 alone does not cover the region; for `ρ ≥ β` Case III′ is needed
  (`Prop46Sufficiency.caseII_not_necessary_46`, `Prop46Sufficiency.cases_A46`), via a new
  criterion `|A₀| ≥ 1` (`Prop46Sufficiency.oneInTwoOut_of_abs_A0`). Through the general
  Blanchard–Kahn theorem the same iff holds for every bounded adapted forcing
  (`Prop46Sufficiency.prop46_determinate3_iff`), and the later Clarida–Galí–Gertler rule of
  p. 260 is proved determinate for all admissible `β`, `κ`, `σ`
  (`Prop46Sufficiency.clarida_later_determinate`,
  `Prop46Sufficiency.clarida_later_determinate3`).
* **Learning.** E-stability under sample-mean and regression learning, Propositions 4.8 and 4.9
  (`Determinacy2Learning.prop_4_8`, `Learning.BullardMitra.prop_4_9`), with every eigenvalue of a
  Kronecker product a product of eigenvalues (`KroneckerSpectrum.isEig_kronecker_iff`), and
  Preston's long-horizon forms with the exact condition for (2.29) (`Learning.Preston.gapIS_iff`).
* **Proposition 4.10 (Preston's long-horizon learning).** With every eigenvalue of `C` real and
  inside the unit circle, the r.e.e. is E-stable under Preston's scheme iff (2.7)
  (`Prop410.prop_4_10`, `Prop410.prop_4_10_existsUnique`); necessity holds for every `C`
  (`Prop410.taylor_of_eStableAt`). The real-eigenvalue hypothesis cannot be dropped: with
  complex stationary eigenvalues, (2.7) can hold with the Bullard–Mitra r.e.e. E-stable but
  Preston's not (`Prop410Complex.prop_4_10_needs_real_eigenvalues`). The fixed point is an r.e.e.,
  as the book claims (`Prop410REE.fixed_isREE`). For real `C` the E-stability region is the same
  as for Proposition 4.9 (`Prop410.same_eStability_region`), though the learning dynamics differ
  (`Prop410.bTil_ne_taylorB`), and the intuition of p. 275 is formalised
  (`Prop410.isEig_jacobian_iff`, `Prop410.tHat_eq_Tmap`, `Prop410.eStable_bTil_iff`,
  `Prop410.loci_coincide_iff`). For any stationary `C` the region is characterised exactly: (2.7)
  and a complex Routh–Hurwitz condition on `B̃(ρ)` at every non-real eigenvalue `ρ`
  (`TidyR5ComplexRegion.prop_4_10_complex`, `TidyR5ComplexRegion.prop_4_10_complex_explicit`),
  which can fail or hold (`TidyR5ComplexRegion.prop_4_10_complex_stable_case`).
* **E-stability as the book defines it, and Preston's forecast sums.** For the linear(ised) map,
  E-stability (eigenvalues of `DT − I`) is equivalent to convergence of every solution of the
  differential equation (2.20) and to local stability of the rest point, with no genericity
  assumption (`TidyR5EStabilityODE.eStable_iff_tendsto`,
  `TidyR5EStabilityODE.eStable_iff_locallyStable`); Propositions 4.8 and 4.9 hold for the actual
  (affine) equation (`TidyR5EStabilityProps.prop_4_8_ode`, `TidyR5EStabilityProps.prop_4_9_ode`).
  For any `T` differentiable at the rest point, E-stability implies local asymptotic stability of
  the nonlinear (2.20) (`TidyR5Lyapunov.isLAS_of_eStableAt`). Conversely, for `T` Lipschitz near
  the rest point (or `C¹`) and differentiable there, an eigenvalue of `DT − I` with positive real
  part makes the rest point unstable, through a Chetaev function and global existence of solutions
  (`TidyR6Instability.not_isLASLoc_of_unstable`, `TidyR6Chetaev.exists_chetaev`,
  `TidyR6ODEExistence.fwdComplete_of_lipschitz`); so when no eigenvalue has zero real part
  E-stability is equivalent to local asymptotic stability (`TidyR6Instability.eStableAt_iff_isLASLoc`,
  `TidyR6Instability.eStableAt_iff_isLASLoc_of_contDiffAt`), and for the solutions-on-`[0, ∞)`
  notion `IsLAS` under forward completeness (`TidyR6Instability.eStableAt_iff_isLAS`). Both
  exclusions are needed: the zero-real-part case is not decided by `DT`
  (`TidyR6InstabilityCex.zero_re_undecided`), and without forward completeness `IsLAS` holds at
  an unstable hyperbolic rest point (`TidyR6InstabilityCex.blowup_isLAS_unstable`). For Preston's map the
  equivalence is exact, zero real parts included (`TidyR5PrestonLAS.isLAS_iff_eStable`,
  `TidyR5PrestonLAS.prop_4_10_LAS`, `TidyR5PrestonLAS.prop_4_10_LAS_complex`). The forecast sums
  converge iff the beliefs annihilate the unstable generalised eigenvectors the state excites
  (`TidyR5ForecastSums.fcast_summable_iff`); the spectral condition on `βĈ` is necessary only for
  convergence at every belief and state (`TidyR5ForecastSums.forecast_sums_all_iff`,
  `TidyR5ForecastSums.IS229_sums_all_iff`), and the decision rules and the PLM → ALM step hold
  without it (`TidyR5ForecastSums.decisionRules_iff_exact`, `TidyR5PLMALM.E_succ_eq_tMapP_exact`,
  `TidyR5PLMALM.E_succ_eq_tMapP_without_spectral`).
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

Not covered: the stochastic-approximation and least-squares convergence results of pp. 265–266,
cited from Evans and Honkapohja, are not formalised; for a general nonlinear `T`-map the
instability half of Lyapunov's indirect method assumes `T` Lipschitz near the rest point (or
`C¹`) or the equation forward complete, since for `T` merely continuous the existence of solutions
would need Peano's theorem, which Mathlib lacks (for the maps of Propositions 4.8–4.10 the
equivalence with the book's definition is exact); Preston's other information sets
and policy rules are outside the book's claim; the numerical impulse responses and phase diagrams
in the figures are not formalised, only the claims the text makes about them.

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
| [PrestonLearning](NeoWicksellianFramework/PrestonLearning.lean) | 33 | §2.3, pp. 273–274: Preston's (2.29)–(2.30) with estimated-model forecasts, the forecast sums, the actual law of motion, the T-map and its block Jacobian |
| [Prop410](NeoWicksellianFramework/Prop410.lean) | 59 | §2.3, p. 275: Proposition 4.10 for real eigenvalues of `C`, the fixed point, the comparison with Proposition 4.9, the p. 275 intuition |
| [Prop410Complex](NeoWicksellianFramework/Prop410Complex.lean) | 25 | §2.3: the real-eigenvalue hypothesis of Proposition 4.10 is necessary (a complex-`C` counterexample) |
| [Prop410REE](NeoWicksellianFramework/Prop410REE.lean) | 10 | §2.3, p. 274: the fixed point of Preston's T-map is an r.e.e. |
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
| [Prop46Sufficiency](NeoWicksellianFramework/Prop46Sufficiency.lean) | 20 | §2.2, C.5: Proposition 4.6 corrected (sufficiency and the iff, also for every forcing), the later Clarida–Galí–Gertler rule determinate |
| [TidyR5ForecastSums](NeoWicksellianFramework/TidyR5ForecastSums.lean) | 38 | §2.3, pp. 273–274: the exact convergence condition for Preston's forecast sums and the series (2.29)–(2.30); the spectral condition on `βĈ` necessary only at every belief and state; the decision rules without it |
| [TidyR5ComplexRegion](NeoWicksellianFramework/TidyR5ComplexRegion.lean) | 16 | §2.3: the complex Routh–Hurwitz criterion; Proposition 4.10 for any stationary `C`, an exact region; a complex `C` that is E-stable |
| [TidyR5EStabilityODE](NeoWicksellianFramework/TidyR5EStabilityODE.lean) | 31 | §2.3, pp. 264–266, n. 37: the linear(ised) equation (2.20), its unique solution, E-stability iff convergence iff local stability |
| [TidyR5EStabilityProps](NeoWicksellianFramework/TidyR5EStabilityProps.lean) | 6 | §2.3: Propositions 4.8–4.10 as statements about (2.20) |
| [TidyR5Lyapunov](NeoWicksellianFramework/TidyR5Lyapunov.lean) | 11 | §2.3, pp. 264–266: the Lyapunov equation; E-stability implies local asymptotic stability of the nonlinear (2.20) |
| [TidyR5PrestonLAS](NeoWicksellianFramework/TidyR5PrestonLAS.lean) | 6 | §2.3, p. 274: Proposition 4.10 for the nonlinear (2.20), an exact iff through the invariant set `Ĉ = C` |
| [TidyR5PLMALM](NeoWicksellianFramework/TidyR5PLMALM.lean) | 3 | §2.3, p. 274: the PLM → ALM step without the spectral hypothesis |
| [TidyR6Chetaev](NeoWicksellianFramework/TidyR6Chetaev.lean) | 9 | §2.3, pp. 264–266: the shifted Lyapunov (Sylvester) equation, a Chetaev function, escape from a rest point with an eigenvalue of `DT − I` of positive real part |
| [TidyR6ODEExistence](NeoWicksellianFramework/TidyR6ODEExistence.lean) | 15 | (2.20), p. 265: solutions on finite intervals, global existence for Lipschitz `T` (Picard–Lindelöf and continuation), the clamped modification, first exits |
| [TidyR6Instability](NeoWicksellianFramework/TidyR6Instability.lean) | 20 | §2.3, pp. 264–266, n. 37: the instability half of Lyapunov's indirect method for a general `T`; E-stability iff local asymptotic stability when no eigenvalue has zero real part |
| [TidyR6InstabilityCex](NeoWicksellianFramework/TidyR6InstabilityCex.lean) | 27 | §2.3, n. 37: the zero-real-part case is not decided by `DT` (`θ̇ = ±θ³`); without forward completeness `IsLAS` misses instability (finite-time blow-up) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
