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
`n`-dimensional systems with predetermined variables. The library contains **1823 theorems**,
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
* **`n`-dimensional systems under uncertainty.** On every expectation system with a nonempty
  state space, `f₁x_{t−1} + f₂x_t + f₃E_t x_{t+1} = w_t` is determinate exactly when its
  perfect-foresight counterpart is, so the criterion is the same exact root condition
  (`LinearSystemsStochastic.linDeterminateS_iff_pf`), and a determinate system has the
  Blanchard–Kahn decision rule `x_t = Gx_{t−1} + ∑ₖJᵏD⁻¹E_t w_{t+k}`, also for singular `f₃`
  (`LinearSystemsStochastic.decision_rule`). When the condition fails, existence or uniqueness
  fails exactly as under perfect foresight (`LinearSystemsStochastic.failure_cases_stoch`), and
  non-uniqueness gives genuinely random sunspots, linear
  (`LinearSystemsStochastic.coin_random_sunspot`) and, when (A.8) is onto, nonlinear
  (`LocalIFTSystemsStochasticSunspots.random_sunspot_nonlinear`). The local theorem holds in the
  book form `E_t[G(x_{t−1}, x_t, x_{t+1}, e_t)] = 0`
  (`LocalIFTSystemsStochastic.local_determinacyS`) and, under informational closure and
  disturbances known at each date, in the forecast form `F(x_{t−1}, x_t, E_t x_{t+1}, e_t) = 0`
  (`LocalIFTSystemsStochasticFormI.local_determinacyF`), with its converse
  (`LocalIFTSystemsStochastic.isUnit_linOpS_iff_local_determinacyS`) and E18
  (`LocalIFTSystemsStochastic.second_order_locS`,
  `LocalIFTSystemsStochasticApps.not_second_order_C1S`). Applied to the inertial rule under
  uncertainty (`LocalIFTSystemsStochasticApps.inertial_iffS`,
  `LocalIFTSystemsStochasticApps.inertial_random_sunspot`); the scalar stochastic theorem and the
  perfect-foresight theorem are recovered
  (`LocalIFTSystemsStochasticApps.scalar_local_determinacyS_recovered`,
  `LocalIFTSystemsStochastic.pf_local_determinacy_recovered`).
* **Nonlinear sunspots when (A.8) is not onto, and the boundary of Proposition 2.8.** The
  linearisation decides whether random sunspots exist near the steady state exactly when (A.8) is
  onto (they exist iff it is not one-to-one, `SunspotsBoundedBelow.sunspot_iff_of_surjective`)
  or bounded below, onto or not (never, with at most one bounded equilibrium near the steady state
  for every small `(x_{−1}, e)`, `SunspotsBoundedBelow.unique_of_boundedBelow`,
  `SunspotsBoundedBelow.no_sunspot_of_boundedBelow`). The key step transfers the bound from (A.8)
  to (A.12) on every expectation system (`SunspotsBoundedBelow.opS_boundedBelow_iff`). Every
  other shape of (A.8) is undecided, shown by pairs of systems with the same linearisation and
  opposite answers: a unit root, whose range is not closed
  (`SunspotsNotOntoExamples.unit_root_undecided`,
  `SunspotsNotOntoExamples.not_isClosed_range_unit`), a singular pencil
  (`SunspotsNotOntoExamples.singular_pencil_undecided`), one-to-one with non-closed range
  (`SunspotsNotOntoMore.injective_nonclosed_undecided`), and Fredholm but neither one-to-one nor
  onto (`SunspotsNotOntoMore.fredholm_undecided`). On the boundary of Proposition 2.8 for the
  exact inertial rule (`|φ_π + ρ| = 1`, or `φ_π = 0` with `|ρ| > 1`), rules with identical
  slopes give sunspots, non-existence, or a unique equilibrium
  (`InertialBoundary.boundary_unit_circle`, `InertialBoundary.boundary_flat`). The repelling
  rules have exactly one bounded equilibrium for small disturbances under every informationally
  closed expectation system, of order `‖e‖^{1/3}`, so the first-order approximation fails
  (`InertialBoundaryExist.exists_unique_affine`, `InertialBoundaryExistCube.exists_unique_cube`).
  For a resonant shock `ν_t = δσᵗ` the equilibrium is exactly `î_t = σᵗ∛(−δ)`
  (`InertialBoundaryExist.resonant_cube_root`, `InertialBoundaryExistCube.resonant_cube_root_pi`).
* **Nonlinear sunspots decided by the higher-order terms.** On a one-dimensional critical
  direction, `E_t[x_{t+1} − g(x_t)] = 0` with `g'(0) = σ = ±1`, write
  `g(g(x)) = x + c xᵐ + o(xᵐ)` with `c ≠ 0`, `m ≥ 2`: random sunspots exist at every scale on the
  coin tree iff `c < 0` or `m` is even (`TidyR6CriticalCriterion.coin_sunspots_iff`). In `g`'s
  own leading coefficient this gives the unit-root and odd-order flip-root criteria, with
  uniqueness under every informationally closed expectation system in the repelling cases
  (`TidyR6CriticalCriterion.unit_root_criterion`, `TidyR6CriticalCriterion.flip_root_criterion`,
  `TidyR6CriticalCriterion.unique_of_one_step`); at a flip root of even order the criterion must
  be read from `g ∘ g` (`TidyR6CriticalCriterion.flip_even_undecided`). For analytic `g` the
  characterisation is complete (`TidyR6CriticalAnalytic.analytic_coin_sunspots_iff`). No
  criterion in the Taylor jet exists in general: two `C^∞` maps with equal derivatives of every
  order and the same (A.8) give opposite answers (`TidyR6CriticalCriterion.flat_undecided`). In
  `n` dimensions, sign-definite conditions on `g` decide in both directions
  (`TidyR6ForwardSunspots.unique_of_repelAnn`, `TidyR6ForwardSunspots.no_coin_sunspot_of_two_step`,
  `TidyR6ForwardSunspots.coin_sunspot_of_pair`).
* **The boundary of Proposition 2.8 for every rule and every expectation system.** For every rule
  strictly differentiable at the steady state (in particular every `C¹` rule, including rules
  nonlinear in `π`) with `φ_π ≠ 0`, `|φ_π + ρ| = 1`, no shocks and `î_{−1} = 0`, the sunspot
  question is decided by the diagonal `D(y) = Ψ(y, y)`: sunspots iff the leading coefficient of
  `D ∘ D − id` is negative or of even order (`TidyR6InertialEveryRule.inertial_coin_iff`,
  `TidyR6InertialEveryRule.inertial_diag_criterion`,
  `TidyR6InertialEveryRule.inertial_unique_of_repel`), completely for analytic rules
  (`TidyR6InertialAnalytic.inertial_analytic_iff`); for the cubic rules
  `φ_ππ + ρî + κî³`, sunspots iff `(φ_π + ρ)κ < 0` (`TidyR6InertialEveryRule.ruleCubI_criterion`).
  The rule `φ_ππ + h(î_{−1})` needs no informational closure: uniqueness for every expectation
  system when `h` is continuous (`TidyR6InertialAnyExpectation.unique_affine_any`), existence
  and uniqueness for small shocks when `h` is Lipschitz on bounded intervals
  (`TidyR6InertialAnyExist.exists_unique_affine_any`,
  `TidyR6InertialAnyExist.boundary_affine_any_shocks`), including the non-closed `skewSystem`
  (`TidyR6InertialAnyExpectation.unique_affine_skew`), and on a filtered probability space with
  Mathlib conditional expectation (`TidyR6InertialMeasure.unique_affine_measure`,
  `TidyR6InertialMeasureExist.exists_unique_affine_measure`). The cube rule `ρî_{−1} + σπ³` is
  unique whenever cubes of known variables are known, in particular under pull-out
  (`TidyR6InertialAnyExpectation.unique_cube_of_cube_known`,
  `TidyR6InertialAnyExpectation.unique_cube_pullOut`), and on probability spaces
  (`TidyR6InertialMeasure.unique_cube_measure`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise.

Not covered: outside the cases where (A.8) is onto or bounded below, nonlinear sunspots are
characterised by the higher-order terms on a one-dimensional critical direction (completely for
analytic maps) and on the boundary of Proposition 2.8 for every rule with `φ_π ≠ 0`; the affine
boundary rule is settled for every expectation system and on probability spaces. Four gaps
remain. (1) `n`-dimensional systems whose critical direction is coupled to hyperbolic
directions: this needs a stochastic centre-manifold reduction, which fails pointwise because the
hyperbolic components depend on the whole future path, not on the critical coordinate; only the
sign-definite `n`-dimensional conditions of `TidyR6ForwardSunspots` are proved there. (2) The
cube rule `ρî_{−1} + σπ³`: uniqueness for an arbitrary expectation system (it is proved when cubes
of known variables are known and on probability spaces; there is no counterexample), and existence
beyond informational closure, which needs a known variable frozen inside `E_t` of a nonlinear
function. (3) Existence and uniqueness with shocks for rules nonlinear in `π` (covered only for
rules affine in `π`). (4) `φ_π = 0` for every rule: the higher-order terms involve both `π` and
`î`, the answer depends on `î_{−1}`, and only the cube rule is done. A criterion in the Taylor
jet alone is impossible in general (`TidyR6CriticalCriterion.flat_undecided`). Figures 2.1–2.5 are
formalised only through their closed forms and spot values.

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
| [LinearSystemsStochastic](PriceLevelDetermination/LinearSystemsStochastic.lean) | 64 | A.3, (A.12)–(A.13): `n`-dimensional linear RE systems with predetermined variables; determinate iff the perfect-foresight system is; the decision rule; the book form; which half fails; random linear sunspots |
| [LocalIFTSystemsStochastic](PriceLevelDetermination/LocalIFTSystemsStochastic.lean) | 71 | A.3 under uncertainty: the implicit-function theorem for `E_t[G(x_{t−1}, x_t, x_{t+1}, e_t)] = 0` on `ℓ∞(ℕ × Ω, ℝⁿ)`; first and second order; the converse; any steady state; perfect foresight recovered |
| [LocalIFTSystemsStochasticApps](PriceLevelDetermination/LocalIFTSystemsStochasticApps.lean) | 20 | A.3 applied under uncertainty: the inertial rule (2.12), including random sunspots of the exact model; the scalar stochastic theorem as `n = 1`; E18 |
| [LocalIFTSystemsStochasticFormI](PriceLevelDetermination/LocalIFTSystemsStochasticFormI.lean) | 37 | A.3: the form `F(x_{t−1}, x_t, E_t x_{t+1}, e_t) = 0` under informational closure and known disturbances, via the forecast as a variable; local determinacy, first and second order, the converse |
| [LocalIFTSystemsStochasticSunspots](PriceLevelDetermination/LocalIFTSystemsStochasticSunspots.lean) | 14 | A.3: random sunspot equilibria of nonlinear `n`-dimensional systems on the coin-flip tree when (A.8) is onto but not one-to-one |
| [SunspotsBoundedBelow](PriceLevelDetermination/SunspotsBoundedBelow.lean) | 14 | A.3: (A.8) bounded below iff (A.12) bounded below on adapted processes, for every expectation system; local uniqueness and no sunspots when (A.8) is bounded below, onto or not; sunspots iff not one-to-one when onto |
| [SunspotsNotOntoExamples](PriceLevelDetermination/SunspotsNotOntoExamples.lean) | 26 | A.3, scalar examples: bounded below but not onto (unique); a unit root (range not closed) and a singular pencil, each with the same (A.8) and opposite sunspot answers |
| [InertialBoundary](PriceLevelDetermination/InertialBoundary.lean) | 19 | Prop. 2.8 on the boundary `\|φ_π + ρ\| = 1` or `φ_π = 0`, `\|ρ\| > 1`, exact model: sunspots, uniqueness under informational closure and non-existence for rules with identical slopes |
| [SunspotsNotOntoMore](PriceLevelDetermination/SunspotsNotOntoMore.lean) | 27 | A.3, two-dimensional examples: (A.8) one-to-one with non-closed range, and Fredholm neither one-to-one nor onto, each undecided by the linearisation |
| [InertialBoundaryExist](PriceLevelDetermination/InertialBoundaryExist.lean) | 16 | Prop. 2.8 boundary: existence and uniqueness for expanding forward recursions; the affine rule has exactly one equilibrium for small shocks, of order `‖e‖^{1/3}`; the resonant cube root; the cubic-in-π rule under perfect foresight |
| [InertialBoundaryExistCube](PriceLevelDetermination/InertialBoundaryExistCube.lean) | 20 | Prop. 2.8 boundary, `φ_π = 0`: the rule `ρî_{−1} + σπ³` has exactly one equilibrium for small shocks on every informationally closed expectation system; the resonant cube root under uncertainty |
| [TidyR6ForwardSunspots](PriceLevelDetermination/TidyR6ForwardSunspots.lean) | 15 | A.3: sunspots of `n`-dimensional forward systems `E_t[x_{t+1} − g(x_t)] = 0` decided by `g` itself: no sunspots when `g` (or, on the coin tree, `g ∘ g`) repels on annuli; random sunspots from a two-step invariant set |
| [TidyR6CriticalCriterion](PriceLevelDetermination/TidyR6CriticalCriterion.lean) | 25 | A.3: the leading-coefficient criterion on a one-dimensional critical direction (both directions); unit and flip roots; the flip-root even-order and flat `C^∞` counterexamples |
| [TidyR6CriticalAnalytic](PriceLevelDetermination/TidyR6CriticalAnalytic.lean) | 4 | A.3: the complete characterisation for analytic maps; the analytic dichotomy |
| [TidyR6InertialEveryRule](PriceLevelDetermination/TidyR6InertialEveryRule.lean) | 14 | Prop. 2.8 boundary, `φ_π ≠ 0`: every strictly differentiable rule, decided by the diagonal `Ψ(y, y)` in both directions; the cubic rules for all signs |
| [TidyR6InertialAnalytic](PriceLevelDetermination/TidyR6InertialAnalytic.lean) | 2 | Prop. 2.8 boundary: the complete characterisation for analytic rules |
| [TidyR6InertialAnyExpectation](PriceLevelDetermination/TidyR6InertialAnyExpectation.lean) | 9 | Prop. 2.8 boundary without informational closure: uniqueness for the affine rule under every expectation system, the skew system; the cube rule when cubes of known variables are known |
| [TidyR6InertialAnyExist](PriceLevelDetermination/TidyR6InertialAnyExist.lean) | 7 | Prop. 2.8 boundary: existence and uniqueness for the affine rule with small shocks under every expectation system; the backward step `E_t g(y) = w` |
| [TidyR6InertialMeasure](PriceLevelDetermination/TidyR6InertialMeasure.lean) | 11 | Prop. 2.8 boundary on a filtered probability space with Mathlib conditional expectation: uniqueness a.s. for the affine and cube rules |
| [TidyR6InertialMeasureExist](PriceLevelDetermination/TidyR6InertialMeasureExist.lean) | 4 | Prop. 2.8 boundary on a probability space: existence and uniqueness a.s. for the affine rule with small shocks |

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
and `Quot.sound` are allowed). Warnings fail the check. Each compiler run (the build and the
fresh audit) has a timeout of 3600 s.
