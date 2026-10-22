# Inflation stabilization and welfare in Lean

This is the `Woodford/StabilizationWelfare/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Woodford (2003), *Interest and Prices*, Chapter 6, "Inflation
Stabilization and Welfare" (pp. 381–463), together with the proofs in Appendix E
(pp. 692–708). Model equations hold for an arbitrary expectation operator where the book uses
one, discounted sums are genuine infinite sums with proved summability, and every welfare
approximation is stated with its terms independent of policy and its remainder written out
rather than left as "t.i.p." and "O(3)". The library contains **2631 theorems**, including the
shared core.

Each welfare approximation is stated in two layers. **Layer A** is an exact identity: the Taylor
polynomial of period (or discounted) utility equals minus the book's quadratic loss, plus an
explicit function of the exogenous variables and initial conditions, plus an explicit remainder
that a scaling lemma shows to have weighted degree at least three. **Layer B** is the statement
about actual utility: along a one-parameter family of economies of amplitude `ε` (distortions,
shocks and policy deviations all scaled by `ε`), utility equals terms independent of policy
minus `ε²/2` times the loss evaluated at the first-order solution, plus `O(ε³)` uniformly in the
date, and a policy with lower loss gives strictly higher welfare for every small `ε > 0`. The
family itself is not assumed: it is proved to exist, smooth in `ε`, for the exact nonlinear model
and for a general class of models, and the Layer B statements are re-proved along it.

**Measure-theoretic expectations.** The core `ExpectationSystem` (an operator `E_t` on all
functions `Ω → ℝ`, with exact equalities) is kept unchanged, and every result stated for it still
holds; on a countable `Ω` it forces finitely supported forecasts. `ExpectationsMeasure` adds,
alongside it, a probability space with a filtration (`ExpectationsMeasure.MeasExpectationSystem`):
`E_t` is Mathlib's conditional expectation `condExp`, variables are bounded measurable functions and
processes, and equations hold almost everywhere. The bridge runs both ways: a finite event tree is
a measure system with the same `E_t` (`ExpectationsMeasure.TreeBridge.treeSystem_E`), and a measure
system on a finite discrete space with full support is a core system with the pull-out property
(`ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_pullOut`). The genuine instance is
the i.i.d. economy on `ℕ → ℝ` under `ν^ℕ`, in which every history has probability zero
(`ExpectationsMeasureIID.iidSystem`, `ExpectationsMeasureIID.iid_not_finitely_supported`). The
modules below also use event trees and general Markov operators (`NonlinearNKMarkov.IsMarkov`) as
carriers of `E_t`, and goods probability spaces for the cross-section.

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
  claim of p. 415 in its precise form (`PriceStability.commit_limits`); the date-0 optimal
  commitment of p. 415 exists, is the unique bounded optimum, also under uncertainty, and
  converges geometrically to the timeless plan with long-run inflation zero, unconditionally
  (`TidyR5CommitLQ.date0_optimal`, `TidyR5CommitLQ.date0_optimal_stoch`,
  `TidyR5CommitLQ.date0_geometric`, `TidyR5CommitLQ.longrun_zero`), and `π_t = 0` is optimal
  from a timeless perspective (`TidyR5CommitLQ.timeless_zero_optimal`).
* **Transactions frictions and the zero bound.** Money demand near satiation exists and is
  locally but not globally unique (`Transactions.Assumption61.moneyDemand_local`,
  `Transactions.cexA_two_solutions`); Propositions 6.7–6.8 with `s_m` and (4.17) corrected
  (`Transactions.prop_6_7_layerA`, `Transactions.loss_4_17`, `BridgeLinks.prop68_primitive`), and
  Proposition 6.7 in both layers around the distorted steady state `(Ȳ, m̄)`, constructed by the
  inverse function theorem, with every coefficient evaluated there and small distortions
  `Φ, Δ̄ = O(ε)` (`TidyR5DistortedBranch67.branch67`, `TidyR5DistortedBranch67.prop67_on_branch`,
  `TidyR5DistortedLocal67.prop67_distorted_local`);
  Proposition 6.9 from a proved two-constraint Kuhn–Tucker theorem (`ZLB.kkt_exists`,
  `ZLB.envelope`, `ZLB.prop_6_9`).
* **Asymmetric disturbances and sticky wages.** Propositions 6.10–6.13, with `κ` a harmonic,
  not geometric, mean and Proposition 6.13's omitted proof supplied
  (`TwoSectorWelfare.prop_6_11_calvo`, `TwoSectorWelfare.printed_geometric_average_false`,
  `StickyWageWelfare.prop_6_12_layerA`, `StickyWageWelfare.prop_6_13_calvo`,
  `BridgeLinks.prop611_primitive`, `BridgeLinks.prop613_primitive`); Propositions 6.10 and 6.12
  in both layers around the constructed distorted steady state, with the coefficients of the
  distorted point and `Φ = O(ε)` (`TidyR5DistortedBranch.prop610_on_branch`,
  `TidyR5DistortedBranch.prop612_on_branch`, `TidyR5DistortedLocal.prop610_distorted_local`,
  `TidyR5DistortedLocal612.prop612_distorted_local`).
* **Cost-push shocks and large distortions.** Natural and efficient output from the implicit
  function theorem (`CostPush.implicit_natural_efficient`); (5.1) with its sign corrected
  (`LargeDistortions.eq51_exact`, `LargeDistortions.eq51_printed_false`); the second-order AS
  relation (5.4) derived from the Calvo model (`LargeDistortions.calvoAS_of_primitives`,
  `LargeDistortions.eq54`); Propositions 6.14–6.15 in both layers, with the first-order term of
  6.14 that prevents ranking and its removal in 6.15 (`BridgeExtensions.prop614_first_order`,
  `BridgeExtensions.prop615_layerB`, `BridgeLinks.prop615_goods_layerB`); footnote 71: complete
  stabilisation of `log P_t + φx_t` is the date-0 and the timeless optimal policy for the
  quarterly weight `λ = κφ` (`16κφ` annualised), on any expectation system with pull-out and on
  any filtered probability space without it (`TidyR5CommitLQ.fn71_optimal`,
  `TidyR5CommitLQ.fn71_annualized`, `TidyR5Fn71Measure.mfn71_optimal`,
  `TidyR5Fn71Measure.mfn71_timeless_optimal`); and, for every `Φ ∈ [0, 1)`, the family whose
  first-order component is the footnote-71 plan is optimal up to `O(ε³)`
  (`TidyR5RamseySOC.lq_sufficiency615`).
* **Markov equilibrium of the nonlinear model.** The exact Calvo model with the Euler equation,
  the recursions for `F` and `K` and the exact dispersion law has, under a Taylor rule satisfying
  the Taylor principle, an equilibrium that exists, is locally unique and is `C²` in the amplitude,
  on finite chains and on any state space with radii uniform across them
  (`NonlinearNKMarkov.markov_equilibrium`, `NonlinearNKMarkovGeneral.markov_equilibrium_general`),
  and the Taylor principle is exactly the condition for the linearised operator to be invertible
  on every finite chain (`NonlinearNKMarkovLinks.lop_injective_iff`). On general filtered
  probability spaces with Mathlib's `condExp` the equilibrium is adapted and unique among all
  bounded processes (`NonlinearNKMarkovAE.seq_existence_ae`,
  `NonlinearNKMarkovAEAdapted.seq_existence_ae_adapted`,
  `NonlinearNKMarkovRamseyNonAdapted.taylor_solution_adapted`), with a Markov representation
  `z_t = g(x_t)` for an AR(1) with any bounded innovation law
  (`NonlinearNKMarkovAR1Markov.ar1_markov_representation`); it discharges the Layer B family
  hypothesis (`NonlinearNKMarkovLinks.layerB_discharged`). It also holds with government purchases,
  `s_C < 1`, the solution satisfying the Calvo block `LargeDistortions.CalvoModel.CalvoAS` behind
  (5.4) exactly (`TidyR5GovPurchases.gov_markov_equilibrium`,
  `TidyR5GovPurchases.gov_seq_existence`, `TidyR5GovPurchases.gov_seq_existence_ae`,
  `TidyR5GovPurchases.gov_calvoAS`). The same holds for the timeless Ramsey
  policy: the nine exact conditions are Lagrangian derivatives, the linearisation is the
  commitment system with `λ_x = κ/θ` for every distortion `Φ` and roots `0 < z₁ < 1 < z₂`
  (`NonlinearNKMarkovRamseyLin.key_theta`, `NonlinearNKMarkovRamseyLin.ramsey_root_condition`), and
  the equilibrium exists on every event tree and every filtered probability space, is unique among
  all bounded processes and has a Markov representation in `(Δ_{t−1}, λ_{t−1}, x_t)`
  (`NonlinearNKMarkovRamseyIFT.ramsey_existence`, `NonlinearNKMarkovRamseyAEIFT.ramsey_existence_ae`,
  `NonlinearNKMarkovRamseyNonAdapted.ramsey_unique_all`,
  `NonlinearNKMarkovRamseyAR1.ramsey_ar1_markov`). Every Ramsey steady state has zero inflation
  iff `(1 − Φ)(1 − σ) ≠ 1 + ω`, which holds for every `0 ≤ Φ ≤ 1`, and every convergent Ramsey path
  has long-run inflation zero (`TidyR5RamseyLongRun.ramsey_ss_pi_zero`,
  `TidyR5RamseyLongRun.ramsey_longrun_zero`, `TidyR5RamseyLongRun.ramsey_ss_continuum`). Near the
  steady state and for small `Φ`, the solution of the first-order conditions of the date-0 problem
  exists, is locally unique and converges geometrically to the timeless plan and, without
  disturbances, to zero inflation (`TidyR5RamseyDate0.date0_main`, `TidyR5RamseyDate0.date0_path`).
  Proposition 6.15's Layer B holds over any
  probability space of goods, including the continuum of Calvo reset histories
  (`NonlinearNKMarkovGoodsLayerB.prop615_goods_layerBM`,
  `NonlinearNKMarkovGoodsLayerBFin.prop615_goods_layerB_of_M`).
* **The exact Rotemberg (1982) model.** The quadratic-adjustment-cost model of Chapter 3,
  footnote 44, stated exactly and treated to the same standard as Calvo. A Markov equilibrium
  exists and is locally unique iff the Taylor principle holds in the Rotemberg slope
  `κ_R = θm(σ + ω)/ψ`: on every state space and Markov chain, for every `ExpectationSystem`, and
  almost surely on filtered probability spaces, with a Markov form `z_t = g(x_t)` for an AR(1)
  of any bounded law (`NonlinearRotembergMarkov.markov_equilibrium_general`,
  `NonlinearRotembergMarkov.seq_existence`, `NonlinearRotembergAE.seq_existence_ae_adapted`,
  `NonlinearRotembergAR1.ar1_markov_representation`, `NonlinearRotembergSmooth.lop_injective_iff`).
  Under strict failure there is a continuum of bounded equilibria and recurrent stationary
  sunspot equilibria near the steady state (`NonlinearRotembergIndet.indeterminacy_every_system`,
  `NonlinearRotembergSunspot.stationary_sunspots`). On the boundary no equilibrium is of the order
  of the shock, there is a continuum at the corner `φ_π = 1`, `φ_y = 0`, and the linearisation
  provably does not decide: two exact rules with the same linearisation give opposite answers
  (`NonlinearRotembergBoundary.boundary_no_order_eps`, `NonlinearRotembergBoundary.corner_continuum`,
  `NonlinearRotembergBoundaryPair.modelA_continuum`, `NonlinearRotembergBoundaryPair.modelB_unique`).
  The equilibrium is `C^∞` in the eight parameters and the shock scale
  (`NonlinearRotembergSmooth.markov_equilibrium_smooth`). The timeless Ramsey policy has
  Lagrangian-derived conditions, a zero-inflation steady state for every `Φ` and none with
  positive inflation, the targeting rule
  `ŷ_t − ŷ_{t−1} + θ_Rπ_t = 0` with `θ_R = θ` iff `Φ = 0`, existence and uniqueness among all
  bounded processes, and an AR(1) Markov form in `(λ_{t−1}, x_t)`
  (`NonlinearRotembergRamsey.ramsey_ss_char`, `NonlinearRotembergRamseyLin.targeting_rule`,
  `NonlinearRotembergRamseyLin.thR_eq_theta_iff`, `NonlinearRotembergNonAdapted.ramsey_unique_all`,
  `NonlinearRotembergRamseyAR1.ramsey_ar1_markov`); for `G = 1 + ω − m(1 − σ) ≤ 0` (an
  overshooting subsidy) the exact problem is solved case by case, including exact non-existence
  (`NonlinearRotembergRamseyGenIFT.ramsey_existence_Gzero`,
  `NonlinearRotembergRamseyGenIFT.ramsey_existence_Gneg`,
  `NonlinearRotembergRamseyNonexist.ramsey_nonexist`). Against Calvo: the first-order solutions
  agree state by state under the equivalence map, the discounted second-order costs of inflation
  coincide, and total second-order welfare of trend inflation differs
  (`NonlinearRotembergLinks.first_order_agree`, `NonlinearRotembergWelfare.discounted_cost_equiv`,
  `NonlinearRotembergTrendWelfare.trend_welfare_differ`).
* **Smooth dependence on the shock scale.** For `E_tf(y_{t+1}, y_t, y_{t−1}, x_t, σε_{t+1}) = 0`
  with an invertible linearisation the equilibrium is `Cᵏ` in `σ` and Markov
  (`SmoothInSigma.Model.exists_smooth_solution`, `SmoothInSigma.Model.exists_smooth_policy`);
  certainty equivalence holds, including with lags because determinacy forces `A + B + C` to be
  injective, and under regime switching (`SmoothInSigmaCE.certainty_equivalence_det`,
  `SmoothInSigmaRegimes.certainty_equivalence_regimes`); the `σ²` correction is explicit
  (`SmoothInSigma.Model.second_order_sigma`), in closed form for an illustration
  (`SmoothInSigmaCE.exModel_closed_form`), and nonlinear exogenous laws are covered
  (`SmoothInSigmaExog.exists_exog_solution`). On the genuine i.i.d. space the equilibrium solves
  the model almost surely and is unique among adapted solutions
  (`SmoothInSigmaUnique.exists_unique_equilibrium_iid`), and Propositions 6.1 and 6.7–6.15 hold
  along it (`SmoothInSigmaWelfare.prop61_of_primitives`, `SmoothInSigmaMeasureProps.prop67_measure`,
  `SmoothInSigmaMeasureWelfare.prop610_measure`, `SmoothInSigmaMeasureProps.prop614_measure`,
  `SmoothInSigmaMeasure615.prop615_measure`).
* **Genuine probability models.** All of the above holds on infinite-horizon probability spaces
  with nondegenerate shocks, where every history is null (`NonlinearNKMarkovMeasure.coin_markov_equilibrium`,
  `SmoothInSigmaMeasurePath.exists_equilibrium_iid`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise.

Not covered: the numerical Figures 6.1–6.6 and the optimisation outputs behind Figure 6.1 and
Table 6.2, of which only the exact arithmetic claims are formalised. For the nonlinear date-0
Ramsey problem only the solution of the exact first-order conditions is constructed, near the
steady state and for small `Φ` (`TidyR5RamseyDate0.date0_main`). Welfare optimality up to
`O(ε³)` holds for every `Φ ∈ [0, 1)` (`TidyR5RamseySOC.lq_sufficiency615`), but assumes that the
first-order component of the nonlinear date-0 solution is the footnote-71 plan and that the
competitors' first-order components satisfy the linear AS relation. That link to the LQ plan,
exact local maximality of the nonlinear plan, and existence and convergence for large `Φ` are
not proved; full optimality is proved in the linear-quadratic model (`TidyR5CommitLQ`). Layer B of
Proposition 6.7 around the distorted steady state with `Δ̄ = 0` uses the smooth extension `Ũ`,
since the actual utility does not then determine `m̄` (`TidyR5DistortedBranch67.foc_actual_flat`).
Government purchases (`s_C < 1`) are covered for the Taylor-rule equilibrium; the Ramsey results
keep `s_C = 1`, and the Calvo Ramsey policy assumes `A_uG ≠ 0` (true for `A_u > 0`,
`0 ≤ Φ ≤ 1`). For the Rotemberg model: under the linear Taylor rule on the boundary with
`φ_y > 0`, whether the exact model has a one-sided continuum of equilibria and whether small-shock
equilibria exist at all (a centre-manifold coefficient; the linearisation provably does not
decide, `NonlinearRotembergBoundaryPair`); and the second-order welfare comparison with Calvo
under stochastic fluctuations with second-order paths, the trend-inflation comparison excluding
log utility (`σ = 1`).
Along the perturbation equilibrium, Propositions 6.8, 6.14 and 6.15 take the exact model equations
(for 6.15 the Calvo conditions `hM`) as hypotheses, Proposition 6.15 needs globally `C²`
readouts, and Propositions 6.7–6.8 assume real balances approach satiation from below (`hleft`).

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
| [ExpectationsMeasure](StabilizationWelfare/ExpectationsMeasure.lean) | 71 | Measure-theoretic expectations (shared core, copied from `ObservationalEquivalence`): `MeasExpectationSystem` with Mathlib's `condExp`, the axioms a.e., news, the forward equation and sunspots, AR(1) conditional variance, bridges to and from the core `ExpectationSystem` |
| [ExpectationsMeasureIID](StabilizationWelfare/ExpectationsMeasureIID.lean) | 37 | The genuine i.i.d. economy on `ℕ → ℝ` under `ν^ℕ` (shared core): independence, moments, every history null, determinacy iff `\|a\| < 1`, AR(1), the `±1` coin |
| [NonlinearNKMarkov](StabilizationWelfare/NonlinearNKMarkov.lean) | 55 | §1, §5, App. A.3: the exact NK model under a Taylor rule on a Markov state, the a-priori bound, existence and local uniqueness on a finite chain, the first-order solution |
| [NonlinearNKMarkovLinks](StabilizationWelfare/NonlinearNKMarkovLinks.lean) | 29 | The exact dispersion law, uniqueness uniform over Markov operators, the state `(Δ_{t−1}, s)`, necessity of the Taylor principle, the Layer B family hypothesis discharged |
| [NonlinearNKMarkovGeneral](StabilizationWelfare/NonlinearNKMarkovGeneral.lean) | 40 | Existence on any state space, second-order accuracy, an AR(1) instance, sequence-space determinacy for any `ExpectationSystem` |
| [NonlinearNKMarkovAE](StabilizationWelfare/NonlinearNKMarkovAE.lean) | 52 | The same on a general filtered probability space with `condExp`: the a-priori bound, existence and uniqueness almost surely, an AR(1) with any bounded law |
| [NonlinearNKMarkovAEAdapted](StabilizationWelfare/NonlinearNKMarkovAEAdapted.lean) | 12 | The almost surely unique equilibrium is adapted |
| [NonlinearNKMarkovAR1Markov](StabilizationWelfare/NonlinearNKMarkovAR1Markov.lean) | 20 | The freezing lemma, measurable Markov equilibria, the Markov representation for an AR(1) with any bounded innovation law |
| [NonlinearNKMarkovAdapted](StabilizationWelfare/NonlinearNKMarkovAdapted.lean) | 13 | p. 633: the sequence-space equilibrium is cell-constant, and adapted under informational closure |
| [NonlinearNKMarkovMeasure](StabilizationWelfare/NonlinearNKMarkovMeasure.lean) | 13 | The equilibrium conditions almost surely, the bridge to the core, a Markov equilibrium on the i.i.d. coin space |
| [NonlinearNKMarkovGoods](StabilizationWelfare/NonlinearNKMarkovGoods.lean) | 24 | The Calvo goods population on reset histories: `hD`, `hV`, the price index and dispersion law; why Ramsey needs `Δ_{t−1}` |
| [NonlinearNKMarkovGoodsLayerB](StabilizationWelfare/NonlinearNKMarkovGoodsLayerB.lean) | 18 | (5.1) and Proposition 6.15 (Layer B) over a goods probability space; the finite cross-section as a special case |
| [NonlinearNKMarkovGoodsLayerBFin](StabilizationWelfare/NonlinearNKMarkovGoodsLayerBFin.lean) | 1 | `BridgeLinks.prop615_goods_layerB` derived from the goods-space theorem |
| [NonlinearNKMarkovRamsey](StabilizationWelfare/NonlinearNKMarkovRamsey.lean) | 8 | §5, Ch. 7: the exact timeless Ramsey conditions as Lagrangian derivatives, the zero-inflation steady state for every `Φ` |
| [NonlinearNKMarkovRamseyLin](StabilizationWelfare/NonlinearNKMarkovRamseyLin.lean) | 21 | The linearisation, `λ_x = κ/θ` for every `Φ`, the commitment system and its root condition |
| [NonlinearNKMarkovRamseyTree](StabilizationWelfare/NonlinearNKMarkovRamseyTree.lean) | 42 | Event trees with a lag; the linearised Ramsey operator is invertible with a bound uniform over trees |
| [NonlinearNKMarkovRamseyAE](StabilizationWelfare/NonlinearNKMarkovRamseyAE.lean) | 43 | The same on adapted processes of a filtered probability space |
| [NonlinearNKMarkovRamseyIFT](StabilizationWelfare/NonlinearNKMarkovRamseyIFT.lean) | 7 | Existence and uniqueness of the timeless Ramsey equilibrium on every event tree |
| [NonlinearNKMarkovRamseyAEIFT](StabilizationWelfare/NonlinearNKMarkovRamseyAEIFT.lean) | 6 | Existence, adaptedness and uniqueness on a filtered probability space |
| [NonlinearNKMarkovRamseyAR1](StabilizationWelfare/NonlinearNKMarkovRamseyAR1.lean) | 36 | The Markov representation `G(z_{t−1}, x_t)` for an AR(1) with any bounded law |
| [NonlinearNKMarkovRamseyMarkov](StabilizationWelfare/NonlinearNKMarkovRamseyMarkov.lean) | 5 | The Markov representation on a finite chain, through `(Δ̂, λ̂₁, λ̂₂)` |
| [NonlinearNKMarkovRamseyNonAdapted](StabilizationWelfare/NonlinearNKMarkovRamseyNonAdapted.lean) | 4 | Every bounded solution is adapted; uniqueness among all bounded processes (Ramsey and Taylor rule) |
| [SmoothInSigma](StabilizationWelfare/SmoothInSigma.lean) | 100 | App. E.2: the class `E_tf(·, σε_{t+1}) = 0` on an event tree; `Cᵏ` dependence on `σ`, the Markov policy, certainty equivalence, the `σ²` correction, determinacy, the cut-off |
| [SmoothInSigmaCE](StabilizationWelfare/SmoothInSigmaCE.lean) | 18 | Determinacy implies `A + B + C` injective, so certainty equivalence with lags; the illustration in closed form |
| [SmoothInSigmaMeasure](StabilizationWelfare/SmoothInSigmaMeasure.lean) | 63 | Regime chains and arbitrary bounded-support shock laws on histories; existence, `Cᵏ`, Markov; i.i.d. certainty equivalence and `σ²` |
| [SmoothInSigmaMeasurePath](StabilizationWelfare/SmoothInSigmaMeasurePath.lean) | 19 | The equilibrium on `ν^ℕ` with `condExp`: the freezing lemma, solutions almost surely; finite laws as a special case |
| [SmoothInSigmaExog](StabilizationWelfare/SmoothInSigmaExog.lean) | 13 | Nonlinear exogenous laws with Markov-switching innovations |
| [SmoothInSigmaWelfare](StabilizationWelfare/SmoothInSigmaWelfare.lean) | 23 | Proposition 6.1 (Layer B) along the equilibrium policy on the tree, discounted and from primitives |
| [SmoothInSigmaMeasureWelfare](StabilizationWelfare/SmoothInSigmaMeasureWelfare.lean) | 14 | Bounded fluctuations proved on `ν^ℕ`; Propositions 6.10 and 6.12 along the equilibrium |
| [SmoothInSigmaMeasureProps](StabilizationWelfare/SmoothInSigmaMeasureProps.lean) | 24 | `D = O(ε²)` and `π̄ − π = O(ε²)` derived; Propositions 6.7, 6.8, 6.10 (discounted), 6.11, 6.13, 6.14 along the equilibrium |
| [SmoothInSigmaMeasure615](StabilizationWelfare/SmoothInSigmaMeasure615.lean) | 25 | (5.4) and Propositions 6.14–6.15 with genuine conditional expectations; 6.15 along the equilibrium |
| [SmoothInSigmaRegimes](StabilizationWelfare/SmoothInSigmaRegimes.lean) | 25 | Certainty equivalence and the coupled `σ²` system under regime switching |
| [SmoothInSigmaUnique](StabilizationWelfare/SmoothInSigmaUnique.lean) | 43 | Uniqueness among adapted almost-sure solutions on `ν^ℕ` |
| [NonlinearRotemberg](StabilizationWelfare/NonlinearRotemberg.lean) | 33 | Ch. 3 fn. 44, Ch. 4 §2.2: the exact Rotemberg (1982) model under a Taylor rule, the zero-inflation steady state, the linearisation with slope `κ_R = θm(σ + ω)/ψ`, the equivalence map to Calvo, the Taylor principle as Schur stability, the bounded inverse |
| [NonlinearRotembergNewton](StabilizationWelfare/NonlinearRotembergNewton.lean) | 8 | App. A.3: a quantitative implicit function theorem for any `C¹` forward-looking maps on a Markov state, with an invariant class |
| [NonlinearRotembergAENewton](StabilizationWelfare/NonlinearRotembergAENewton.lean) | 10 | The same on a filtered probability space, almost surely |
| [NonlinearRotembergMarkov](StabilizationWelfare/NonlinearRotembergMarkov.lean) | 17 | Markov and sequence-space equilibria of the Rotemberg model: existence and local uniqueness on every state space and every `ExpectationSystem`, adaptedness, local uniqueness of the steady state, linear determinacy iff the Taylor principle |
| [NonlinearRotembergAE](StabilizationWelfare/NonlinearRotembergAE.lean) | 18 | The Rotemberg model on a general filtered probability space: a.s. existence, uniqueness and adaptedness; an AR(1) with any bounded law |
| [NonlinearRotembergAR1](StabilizationWelfare/NonlinearRotembergAR1.lean) | 4 | The Markov representation `z_t = g(x_t)` for an AR(1) with any bounded innovation law |
| [NonlinearRotembergSmooth](StabilizationWelfare/NonlinearRotembergSmooth.lean) | 22 | The Markov equilibrium is `C^∞` in the parameters and the shock scale; the first-order solution; injectivity on every finite chain iff the Taylor principle |
| [NonlinearRotembergLinks](StabilizationWelfare/NonlinearRotembergLinks.lean) | 8 | Rotemberg and Calvo: first-order agreement under the map, Calvo dispersion is second order, the Rotemberg resource wedge, an explicit second-order difference |
| [NonlinearRotembergBoundary](StabilizationWelfare/NonlinearRotembergBoundary.lean) | 14 | The Taylor-principle boundary: a constant kernel, no exact equilibrium of the order of the shock, a continuum of steady states at the corner |
| [NonlinearRotembergRamsey](StabilizationWelfare/NonlinearRotembergRamsey.lean) | 10 | Ch. 7: the exact Rotemberg Ramsey conditions as Lagrangian derivatives, the Ramsey steady states, the golden rule |
| [NonlinearRotembergRamseyLin](StabilizationWelfare/NonlinearRotembergRamseyLin.lean) | 29 | The linearisation: the commitment system, the targeting rule with `θ_R`, the root condition, `θ_R = θ` iff `Φ = 0` |
| [NonlinearRotembergRamseyTree](StabilizationWelfare/NonlinearRotembergRamseyTree.lean) | 17 | The linearised Rotemberg Ramsey operator on event trees: inverse with a uniform bound |
| [NonlinearRotembergRamseyAE](StabilizationWelfare/NonlinearRotembergRamseyAE.lean) | 12 | The same on adapted processes of a filtered probability space |
| [NonlinearRotembergRamseyDegenerate](StabilizationWelfare/NonlinearRotembergRamseyDegenerate.lean) | 21 | The linearised Ramsey system when `G ≤ 0`: when it occurs, `G = 0`, non-existence, oscillating determinacy and a unit root for `G < 0` |
| [NonlinearRotembergBoundaryPair](StabilizationWelfare/NonlinearRotembergBoundaryPair.lean) | 11 | Two exact rules with the boundary Taylor rule's linearisation and opposite answers: the linearisation does not decide |
| [NonlinearRotembergIndet](StabilizationWelfare/NonlinearRotembergIndet.lean) | 30 | Indeterminacy under strict failure of the Taylor principle: a continuum of bounded equilibria of the exact model, date-0 sunspots, on every expectation system |
| [NonlinearRotembergJets](StabilizationWelfare/NonlinearRotembergJets.lean) | 16 | Second-order jets at zero: sums, products, composition |
| [NonlinearRotembergLevels](StabilizationWelfare/NonlinearRotembergLevels.lean) | 14 | The level model and its equivalence to the log system, the firm's first-order condition, steady-state uniqueness and a second steady state when `φ_y > 0` |
| [NonlinearRotembergRamseyIFT](StabilizationWelfare/NonlinearRotembergRamseyIFT.lean) | 6 | Existence and uniqueness of the timeless Rotemberg Ramsey equilibrium on every event tree |
| [NonlinearRotembergRamseyAEIFT](StabilizationWelfare/NonlinearRotembergRamseyAEIFT.lean) | 6 | Existence, adaptedness and uniqueness on a filtered probability space |
| [NonlinearRotembergNonAdapted](StabilizationWelfare/NonlinearRotembergNonAdapted.lean) | 3 | Every bounded solution is adapted; uniqueness among all bounded processes |
| [NonlinearRotembergRamseyMarkov](StabilizationWelfare/NonlinearRotembergRamseyMarkov.lean) | 4 | The Markov representation on a finite chain, through `λ̂_{t−1}` |
| [NonlinearRotembergRamseyAR1](StabilizationWelfare/NonlinearRotembergRamseyAR1.lean) | 30 | The Markov representation `G(z_{t−1}, x_t)` for an AR(1) with any bounded law, depending on the lag through `λ̂_{t−1}` |
| [NonlinearRotembergRamseyRootsInv](StabilizationWelfare/NonlinearRotembergRamseyRootsInv.lean) | 12 | The linearised Ramsey inverse for any roots `\|z_s\| < 1 < \|z_u\|`, including the oscillating case `G < 0` |
| [NonlinearRotembergRamseyZeroInv](StabilizationWelfare/NonlinearRotembergRamseyZeroInv.lean) | 3 | The linearised Ramsey inverse when `G = 0` |
| [NonlinearRotembergRamseyGenIFT](StabilizationWelfare/NonlinearRotembergRamseyGenIFT.lean) | 5 | The Newton contraction for any inverse; exact existence for `G = 0` and for `G < 0`, `κθ_R < −2(1 + β)` |
| [NonlinearRotembergRamseyNonexist](StabilizationWelfare/NonlinearRotembergRamseyNonexist.lean) | 5 | Exact non-existence near the steady state for `G < 0`, `−2(1 + β) < κθ_R < 0` |
| [NonlinearRotembergSunspot](StabilizationWelfare/NonlinearRotembergSunspot.lean) | 29 | Recurrent stationary sunspot equilibria on a two-state chain under strict failure, by Lyapunov–Schmidt |
| [NonlinearRotembergTrendWelfare](StabilizationWelfare/NonlinearRotembergTrendWelfare.lean) | 17 | Second-order welfare of trend inflation, Rotemberg against Calvo with a distorted steady state: the totals differ |
| [NonlinearRotembergWelfare](StabilizationWelfare/NonlinearRotembergWelfare.lean) | 9 | The Calvo dispersion law in closed form; the discounted second-order costs of inflation coincide under the map |
| [TidyR5CommitLQ](StabilizationWelfare/TidyR5CommitLQ.lean) | 37 | §3.2, p. 415, n. 71: the date-0 optimal commitment exists, is optimal and converges, long-run inflation zero (negative with a unit coefficient), the stochastic case; footnote 71's plan is optimal for `λ = κφ` |
| [TidyR5DistortedTools](StabilizationWelfare/TidyR5DistortedTools.lean) | 14 | Tools for moving the expansion point to the distorted steady state; the distorted steady state to first order |
| [TidyR5Distorted610](StabilizationWelfare/TidyR5Distorted610.lean) | 7 | Proposition 6.10 in both layers around the distorted steady state |
| [TidyR5Distorted612](StabilizationWelfare/TidyR5Distorted612.lean) | 5 | Proposition 6.12 in both layers around the distorted steady state |
| [TidyR5Distorted67](StabilizationWelfare/TidyR5Distorted67.lean) | 8 | The distorted steady state with transactions frictions; Proposition 6.7 in both layers around it |
| [TidyR5DistortedBranch67](StabilizationWelfare/TidyR5DistortedBranch67.lean) | 7 | The branch `(Ȳ, m̄)` by the inverse function theorem; Proposition 6.7 on it; the smooth-extension caveat for the actual utility |
| [TidyR5DistortedBranch](StabilizationWelfare/TidyR5DistortedBranch.lean) | 6 | The branches of distorted steady states by the inverse function theorem; Propositions 6.10 and 6.12 on them |
| [TidyR5DistortedLocal](StabilizationWelfare/TidyR5DistortedLocal.lean) | 8 | Proposition 6.10 with every coefficient at the distorted steady state |
| [TidyR5DistortedLocal612](StabilizationWelfare/TidyR5DistortedLocal612.lean) | 6 | Proposition 6.12 with every coefficient at the distorted steady state |
| [TidyR5DistortedLocal67](StabilizationWelfare/TidyR5DistortedLocal67.lean) | 6 | Proposition 6.7 with every coefficient at the distorted steady state |
| [TidyR5Fn71Measure](StabilizationWelfare/TidyR5Fn71Measure.lean) | 8 | Footnote 71 on any filtered probability space, almost surely, with no pull-out hypothesis |
| [TidyR5GovNewton](StabilizationWelfare/TidyR5GovNewton.lean) | 14 | The Newton step for any model with the New Keynesian linearisation: Markov, sequence space, almost surely |
| [TidyR5GovPurchases](StabilizationWelfare/TidyR5GovPurchases.lean) | 23 | §5: government purchases (`s_C < 1`) in the exact Calvo model: existence and uniqueness, the Euler equation with `C = Y − G`, the Calvo block of (5.4) |
| [TidyR5RamseyWeighted](StabilizationWelfare/TidyR5RamseyWeighted.lean) | 25 | The inverse of the linearised Ramsey operator on spaces of geometrically decaying processes |
| [TidyR5RamseyStability](StabilizationWelfare/TidyR5RamseyStability.lean) | 2 | The influence of the initial commitment on the exact Ramsey solution decays geometrically |
| [TidyR5RamseyDate0](StabilizationWelfare/TidyR5RamseyDate0.lean) | 27 | pp. 413–415, Ch. 7: the date-0 plan of the exact model (first-order conditions) exists for small `Φ` and converges to the timeless plan and to zero inflation |
| [TidyR5RamseyLongRun](StabilizationWelfare/TidyR5RamseyLongRun.lean) | 9 | Every Ramsey steady state has zero inflation iff `(1 − Φ)(1 − σ) ≠ 1 + ω`; convergent paths have long-run inflation zero; the exceptional continuum |
| [TidyR5RamseySOC](StabilizationWelfare/TidyR5RamseySOC.lean) | 3 | Proposition 6.15 with footnote 71: the commitment plan is optimal up to `O(ε³)` for every `Φ ∈ [0, 1)` |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
