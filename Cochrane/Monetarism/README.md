# Monetarism in Lean

This is the `Cochrane/Monetarism/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Chapter 19, "Monetarism" (pp. 433–464), together with the precise claims
of Chapter 11 on open-market operations and elastic currency (pp. 315–318), the helicopter
arithmetic of §14.1 (p. 342), and Online Appendix §1.6 (pp. 567–569), Chapter 3, "Pruning
multiple monetary equilibria" (§§3.1–3.2.4, pp. 612–632), and Chapter 4, "Money in continuous
time" (pp. 635–641). The present-value and Cagan results hold for an arbitrary expectation
operator, so they cover perfect foresight and genuine uncertainty. The nonlinear phase dynamics
are perfect-foresight, as in the book. The household first-order conditions are derived by
optimisation, under perfect foresight and on a finite event tree. Continuous time is
deterministic. The library contains **656 theorems**, including the shared core; 548 of them are
in the thirteen chapter modules.

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises. Survey codes E13–E23 refer to the
survey of Chapters 11–19 (`notes/survey_cochrane_ch11-19.md`), as do V1–V5 and V11 (the precise
claims of the verbal chapters) and NI-7.

Headline results, in the namespace `Cochrane.Monetarism`:
* **Regimes, NI-7 and double passive policy.** Given bond pricing and the money transversality
  condition, the two forms (19.2) and (19.3) of the valuation equation are equivalent
  (`Regimes.eq192_iff_eq193`), and (19.2) holds iff the bond transversality condition does
  (`Regimes.flow_pv_iff_tvc`). Every equilibrium of `MV = Py` and the valuation equation is the
  unique equilibrium of an active-money/passive-fiscal regime and of an active-fiscal/passive-money
  regime with the same observables (NI-7, `Regimes.ni7`). With both policies passive every positive
  price level is an equilibrium (`Regimes.double_passive`). With both active an equilibrium exists
  iff they are coordinated (`Regimes.double_active_iff`).
* **Chapter 11 and the helicopter.** With `i = i^m` an open-market swap leaves the price level
  unchanged (V1, `Regimes.omo_irrelevant`). Below the Laffer peak, raising money growth lowers the
  initial price level; beyond it, raising money growth raises it (V2, `Seigniorage.v2_cagan`). A
  unique interest spread clears money demand (V3, `Regimes.spread_existsUnique`). Both readings of
  an open-market operation describe the same event (V4, `Regimes.omo_equivalence`). Under elastic
  currency any price level clears the money market (V5, `Regimes.elastic_currency`). The
  helicopter drop of p. 342 raises the price level by exactly `1/101` in fiscal theory and doubles
  it in monetarism (`Regimes.helicopter_fiscal`, `Regimes.helicopter_monetarist`).
* **Cagan with rational expectations.** The equilibria of (19.5) with constant money are exactly
  the family `p_t − p̄ = θᵗ(p_0 − p̄) + ∑θ^{t−j}δ_j` with `E_tδ_{t+1} = 0`
  (`CaganRE.caganFamily_solves`, `CaganRE.eq_caganFamily`). All but the steady state explode
  (`CaganRE.pf_explodes`, `CaganRE.bounded_iff_steady`). There are uncountably many
  perfect-foresight paths and sunspots under genuine uncertainty
  (`CaganRE.pf_solutions_uncountable`, `CaganRE.coin_sunspot_ne_steady`). The valuation equation
  selects exactly one path (`CaganRE.fiscal_path_existsUnique`), and the selected path is
  explosive unless `B_{−1} = e^{p̄}∑βʲs_j` (`CaganRE.fiscal_path_bounded_iff`).
* **Money in utility.** The first-order conditions (19.13)–(19.14) are derived from the time-0
  problem of footnote 1 by cost-neutral perturbations, under perfect foresight and on a finite
  event tree, with sufficiency under concavity (`MoneyInUtility.foc_1913_1914`,
  `MoneyInUtility.FootnoteTree.tree_foc_1913_1914`,
  `MoneyInUtility.FootnoteTree.tree_optimal_of_foc`).
  The knownness of `Λ_t/P_t` and `P_t/u_c(t)` follows from adaptedness on any state space
  (`MoneyInUtility.known_div`, `MoneyInUtility.value_of_money_limit_adapted`). The value of a
  dollar is the present value of its liquidity dividends (`MoneyInUtility.value_of_money_limit`).
  Figure 19.1 is certified: `5.52 < x̄ < 5.53`, the slope at `x̄` is exactly `47/25`, and the pole
  is at `x = 10` (`MoneyInUtility.fig191_xbar_bounds`, `MoneyInUtility.fig191_slope`,
  `MoneyInUtility.fig191_pole`). The zero-rate steady state attracts iff `1 + µ > β`, not
  `1 + µ > 1/β` (E13, `MoneyInUtility.e13_corrected`). The calibration of p. 444, `θ` of order
  `0.01`, holds only for `γ = 1` (`MoneyInUtility.calib_ten_gamma_two`).
* **Money-targeting dynamics.** Woodford's global analysis of monetary targeting is restated from
  the Woodford Chapter 2 project, and (19.18) is its separable map
  (`MoneyTargetingDynamics.miuPath_iff_sepPath`). In the power example the inflationary steady
  state repels (`MoneyTargetingDynamics.power_steady_repelling`). Every path below it converges to
  the deflationary steady state with `P_{t+1}/P_t → β`
  (`MoneyTargetingDynamics.power_deflation_orbit`,
  `MoneyTargetingDynamics.power_deflation_inflation`). Every path above it leaves the domain in
  finite time (`MoneyTargetingDynamics.power_inflation_exits`).
* **Unpleasant arithmetic.** With fixed surpluses the present value of seigniorage is fixed, so
  lower money growth now forces higher money growth and inflation later
  (`UnpleasantArithmetic.unpleasant_money_growth`). With nominal debt a fall in the present value
  of surpluses raises the price level with no money at all
  (`UnpleasantArithmetic.nominal_debt_price_anti`).
* **Seigniorage.** Revenue is maximal where the velocity elasticity equals `π/(π + g)`, which is
  one only when `g = 0` (E16, `Seigniorage.revenue_foc_iff`, `Seigniorage.e16_unit_iff`). In the
  Cagan example the unique peak is at `π = 1/a`; above it there is no steady state, below it there
  are two (`Seigniorage.cagan_revenue_lt`, `Seigniorage.no_steady_state_above_max`,
  `Seigniorage.two_steady_states`). Baumol–Tobin gives elasticities of one half
  (`Seigniorage.bt_interest_elasticity`, `Seigniorage.bt_income_elasticity`). A 40% price rise
  devalues nominal debt by 28.6% (E23, `Seigniorage.e23_real_loss`).
* **Pruning deflations.** Along a deflation the transversality condition fails iff `µ ≥ 0`,
  including `µ = 0` (E17, `PruningDeflation.tvc_tendsto_zero_iff`, `PruningDeflation.tvc_mu_zero`).
  For `β < 1 + µ < 1` the deflations are a continuum of equilibria, and for `1 + µ ≤ β` there are
  none (`PruningDeflation.deflation_continuum`, `PruningDeflation.no_deflation_of_le_beta`). E13
  and E17 are one condition (`Links.e13_iff_e17`). With no money demand the price level is
  determinate (`PruningDeflation.price_level_determined`).
* **Pruning inflations.** Paths below the steady state explode in finite time
  (`PruningInflation.finite_time_explosion`). The inflationary equilibria, which demonetise at a
  finite date, are countable and are completely classified
  (`PruningInflation.eqm_initial_iff`, `PruningInflation.inflationary_initial_countable`). With the
  modified utility of p. 620 there is instead a continuum that never explodes
  (`PruningInflation.new_inflationary_continuum`).
* **Obstfeld–Rogoff.** The Figure 3.2 caption should read `v′(m) = m^{−1/2}` (E18,
  `ObstfeldRogoff.e18_no_steady_state`, `ObstfeldRogoff.e18_correct_v`). The redemption dispute is
  resolved precisely. Obstfeld and Rogoff's finite-price theorem holds
  (`ObstfeldRogoff.or_no_hyperinflation`). With a one-time tender of the money carried out of `T`,
  Cochrane's demonetised path is a Walrasian equilibrium
  (`ObstfeldRogoff.cochrane_household_optimal`, `ObstfeldRogoff.fig32_cochrane_optimal`). With a
  standing offer that also redeems dollars bought at a zero value, no household optimum exists
  (`ObstfeldRogoff.standing_redemption_no_optimum`).
* **Nonseparable utility.** The Obstfeld (1984) phase diagram cuts from above iff `b > 1`, but it
  is stable iff `b > 1 + i/2` (E19, `Nonseparable.obs_cuts_from_above_iff`,
  `Nonseparable.obs_stable_iff`, `Nonseparable.e19_counterexample`). The printed partial
  derivatives have sign typos (`Nonseparable.obs_printed_typo`).
* **Cash in advance.** The stochastic Euler equation (19.31) and the bond price (19.32) are derived
  from household optimality on a finite event tree (`CashInAdvance.TreeEuler.sdf_eq`,
  `CashInAdvance.TreeEuler.bond_price_from_optimality`). (19.29) needs the money transversality
  condition (`CashInAdvance.Stochastic.pv_19_29_needs_money_tvc`). (19.38) is corrected to
  `(B_{t−1} + M_{t−1})/P_t` (`CashInAdvance.PF.frictionless_valuation`,
  `CashInAdvance.PF.printed_19_38_counterexample`). The nominal rate is non-negative iff `Q ≤ 1`
  (E14, `CashInAdvance.MoneyDemand.Q_le_one_iff`), and `Q = β` only with a constant price level
  (E15, `CashInAdvance.PF.bondPrice_eq_beta_iff`). For `V ≠ 1` the constraint drives a wedge into
  asset pricing, a suspected imprecision (`CashInAdvance.MoneyDemand.binding_cost_wedge`,
  `CashInAdvance.Euler.sdf_wedge`). The boundary between the cash-in-advance and money-in-utility
  deflations is `1 + µ = β` (`Links.cia_boundary_deflation`).
* **Continuous time.** The present-value budget of Online Appendix Chapter 4 is the present-value
  form of the flow constraint (`ContinuousTime.pv_budget_iff`), and the first-order conditions
  follow by the chain rule (`ContinuousTime.foc_4_1`, `ContinuousTime.foc_4_2`). The CES limits
  are corrected (E20). (4.6) holds only for the normalised aggregator, and with fixed `α` the
  `θ → ∞` limit is `min(c, m)` (`ContinuousTime.ces_norm_limit`, `ContinuousTime.ces_limit_min`).
  The printed `α = 1/V` holds only for `α = 1` (`ContinuousTime.alpha_eq_inv_V_iff`). The IS curve
  with money is stated exactly, restoring the dropped `−δσ` (E21, `ContinuousTime.is_curve_exact`,
  `ContinuousTime.E21_steady_state`). The valuation equations of Online Appendix §1.6 are restated
  (`ContinuousTime.money_interest_iff`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections are:
* `1 + µ > β`, not `1 + µ > 1/β`, on p. 445 (E13), and the same condition `µ > −δ/(1 + δ)` for
  the deflations of the Online Appendix, whose transversality condition fails at `µ = 0` too (E17);
* `Q_t ≤ 1`, not `Q_t ≥ 1`, on p. 453 (E14); `Q = β` only with a constant price level, p. 450
  (E15);
* "inelastic" and "roughly one" on p. 458: the peak elasticity is `π/(π + g)` (E16);
* the Figure 3.2 caption, `v′(m)` for `v(m)` (E18), and `P̄y/M` for `PM/M` on p. 619 (E22);
* stability of the Obstfeld (1984) map needs `b > 1 + i/2`, and the printed coefficient misses
  `1 + i` (E19);
* the CES limits of Online Appendix Chapter 4 (E20) and the dropped `−δσ` in (4.13)–(4.14), with
  `E_tπ_{t+1}` in (4.15) (E21);
* 28.6%, not 40%, on p. 462 (E23).

In addition, the formalisation shows that (19.29) needs the money transversality condition, that
(19.38) must include money, that the partial derivatives on p. 631 have sign typos, and that the
calibration of p. 444 holds only for `γ = 1`.

Not formalised:
* the verbal and historical parts of the chapter: §19.4 beyond the Online Appendix claims, §19.8
  beyond Baumol–Tobin, the LM slope, cash-in-advance elasticities and E23, the literature survey
  of Online Appendix §3.1.4 (including the Buiter–Siebert notation clash of E17), the
  interpretation of §3.2.3, and §3.3 on uniqueness in cash-in-advance models;
* the household problem under uncertainty beyond finite event trees: for a general
  `ExpectationSystem` the first-order conditions and `Λ_t = βᵗu′(y_t)` are equilibrium hypotheses
  (`CashInAdvance.Stochastic.bond_price_19_32`, `MoneyInUtility.value_recursion`); the tree
  derivation of (19.31) takes `V = 1`;
* Pontryagin necessity for the Hamiltonian conditions (4.16)–(4.17): only their consequences are
  proved; and the stochastic `E_td(·)` forms of Online Appendix §1.6;
* uniqueness of the monetary-model price level under active fiscal policy across all paths: it is
  proved only against the zero-rate deflations the book discusses
  (`CashInAdvance.PF.active_fiscal_prunes`);
* the suspected one-period shift of the time axis of Figure 3.2 (E18);
* Woodford's Taylor-rule transversality section, its Obstfeld–Rogoff section and its convexity
  counterexample, which are not restated in `MoneyTargetingDynamics`; and the optional link to
  Galí's money rule;
* some bridges between modules: `MoneyTargetingDynamics.power_inflation_exits` and
  `PruningInflation.finite_time_explosion` are not derived from each other (they are linked on
  the same path by `Links.explosion_same_path`), and the tree admissibility of `CashInAdvance` is
  not bridged to `MoneyInUtility.FootnoteTree.TOptimal` (only the node notion is,
  `Links.meas_iff_tAdapted`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](Monetarism/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (shared core, restated from the earlier projects) |
| [Expectations](Monetarism/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; adapted and bounded processes; forward series; the pull-out property (shared core) |
| [ExpectationsFiniteTree](Monetarism/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; the coin-flip tree and its shock (shared core) |
| [ForwardSolution](Monetarism/ForwardSolution.lean) | 44 | The forward solution of `z_t = aE_tz_{t+1} + u_t` (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [Regimes](Monetarism/Regimes.lean) | 26 | §19.1, (19.1)–(19.3): summation by parts, valuation iff transversality, NI-7, double passive and double active policy; Chapter 11 V1, V3–V5; the helicopter arithmetic of p. 342 |
| [CaganRE](Monetarism/CaganRE.lean) | 35 | §19.2, (19.4)–(19.8): the full solution family, explosions, sunspots, the forward solution, fiscal selection of the price level |
| [MoneyInUtility](Monetarism/MoneyInUtility.lean) | 73 | §19.3, (19.9)–(19.23): budget constraints, first-order conditions by optimisation (perfect foresight and finite tree), knownness, the value of money, power utility, Figure 19.1, E13 |
| [MoneyTargetingDynamics](Monetarism/MoneyTargetingDynamics.lean) | 34 | §19.3.2: global dynamics of monetary targeting (restated from the Woodford Chapter 2 project); the power example globally; E13 |
| [UnpleasantArithmetic](Monetarism/UnpleasantArithmetic.lean) | 13 | §19.6, (19.39)–(19.40): seigniorage, unpleasant arithmetic, nominal versus real debt |
| [Seigniorage](Monetarism/Seigniorage.lean) | 27 | §§19.7–19.8, (19.41): the Laffer limit and E16, the Cagan example, Chapter 11 V2, Baumol–Tobin, E23 |
| [PruningDeflation](Monetarism/PruningDeflation.lean) | 53 | Online Appendix §3.1: deflationary paths, the transversality condition and E17, fiscal theory with no money demand, open-market operations, the last-period condition |
| [PruningInflation](Monetarism/PruningInflation.lean) | 42 | Online Appendix §§3.2–3.2.1, (3.3)–(3.5): finite-time explosion, the countable classification, the modified utility and its continuum |
| [ObstfeldRogoff](Monetarism/ObstfeldRogoff.lean) | 28 | Online Appendix §§3.2.2–3.2.3, (3.6), Figure 3.2: E18, Obstfeld and Rogoff's theorem, Cochrane's demonetised equilibrium and the redemption dispute |
| [Nonseparable](Monetarism/Nonseparable.lean) | 33 | Online Appendix §3.2.4, (3.7)–(3.8): the discount factor, Obstfeld (1984) utility and E19, CES money in utility |
| [CashInAdvance](Monetarism/CashInAdvance.lean) | 78 | §19.5, (19.24)–(19.38): stochastic present-value budgets, money demand by optimisation, the Euler equation (perfect foresight and finite tree), frictionless and monetary equilibria, E14, E15 |
| [ContinuousTime](Monetarism/ContinuousTime.lean) | 82 | Online Appendix §1.6 (restated from the `Generality` project) and Chapter 4, (4.1)–(4.17): the present-value budget, first-order conditions, CES and E20, the IS curve with money and E21, the Hamiltonian |
| [Links](Monetarism/Links.lean) | 24 | The same objects across modules: coordinates `x` and `m`, E13 = E17, MIU and CIA deflations, discrete and continuous first-order conditions, CES, Cagan and seigniorage |

## Modelling conventions

* **Expectations.** Random variables are `Ω → ℝ`, processes `ℕ → Ω → ℝ`, and the present-value
  and Cagan results hold state by state for an arbitrary `ExpectationSystem`. A process is adapted
  when `E_tx_t = x_t` (`ExpectationSystem.Adapted`). Results that take date-`t` quantities out of
  `E_t` assume `ExpectationSystem.PullOut`. Perfect foresight (`perfectForesight`) and every
  finite event tree (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) are instances, and
  the coin-flip tree gives a genuine Cagan sunspot (`CaganRE.coin_sunspot_solves`).
* **Timing.** In `Regimes` and `MoneyInUtility` money and bonds carried into date `t` are indexed
  by `t`, so the book's `M_{t−1}` and `B_{t−1}` are dated `t`. In `CashInAdvance` they are
  `Min t` and `Bin t`, and the bonds and overnight money chosen at `t` are dated `t + 1`.
* **Infinite sums.** The sums `E_t∑` of (19.2), (19.3), (19.11) and (19.12) are limits of `E_t`
  of the partial sums, multiplied through by the known `Λ_t` (`Regimes.partial192`). The
  cash-in-advance budgets use `tsum` with summable flows
  (`CashInAdvance.Stochastic.pv_iff_tvc`), and `Links.flow_pv_tsum_iff_tvc` restates the
  `Regimes` form that way. Unpleasant arithmetic uses genuine `HasSum`.
* **Optimisation.** The household problems are stated as optimisation problems and their
  first-order conditions are derived, not imposed: `MoneyInUtility.Optimal`,
  `MoneyInUtility.FootnoteTree.TOptimal`, `CashInAdvance.Euler.IsOptimalPlan` and
  `CashInAdvance.TreeEuler.IsOptimal`. The cash-in-advance consumption problem is the
  money-in-utility problem without money (`CashInAdvance.Euler.isOptimalPlan_iff_optimal`), and
  overnight money is a linear programme (`CashInAdvance.MoneyDemand.IsOptimalMoney`).
* **Coordinates.** Chapter 19 writes (19.23) in `x = Py/M` (`MoneyInUtility.nextX`); the Online
  Appendix writes it in real balances `m = M/(Py) = 1/x` (`PruningDeflation.ratioMap`). Both are
  kept, and `Links` proves them conjugate (`Links.ratioMap_eq_one_div_nextX`,
  `Links.isMPath_iff_isPowerPath`).
* **Demonetisation.** In the Online Appendix the value of money `q_t = 1/P_t ≥ 0` is the state, so
  an infinite price level is `q_t = 0` (`PruningInflation.IsEqm`, `ObstfeldRogoff.IsORPath`).
* **Continuous time.** Paths are `ℝ → ℝ` with `HasDerivAt`; present values are integrals over
  `(t, ∞)` with `IntegrableOn`; transversality conditions are explicit limits.
* **Explicit hypotheses.** Positivity of prices, money, output and velocity, `0 < β < 1`,
  summability of discounted flows, concavity for sufficiency, and the domain `θx^γ < 1` of the
  power map are stated in each theorem.

## Relation to the Woodford projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects, so the project builds on its own. Nothing is imported from
those projects. Three further blocks come from the Woodford Chapter 2 project
(`PriceLevelDetermination`), and their docstrings say so:
* `MoneyTargetingDynamics` restates that project's survey lemma L5 on one-dimensional maps (from
  its `GlobalDynamics` module) and its analysis of monetary targeting (from its module of the same
  name): the maps `F` and `G`, the separable map of Woodford's Figure 2.5, self-fulfilling
  inflations and deflations, satiation and the transversality condition
  (`MoneyTargetingDynamics.sepMap`, `MoneyTargetingDynamics.sep_deflation_violates_tvc`,
  `MoneyTargetingDynamics.money_contraction_continuum`). Cochrane's (19.18) is that separable map
  with `μ̄ = 1 + µ` (`MoneyTargetingDynamics.miuPath_iff_sepPath`). The module then adds
  Cochrane's power example globally;
* `CaganRE` is adapted from that project's Cagan equation (A.28)–(A.29) (`MoneyGrowth`);
* `MoneyInUtility.lm_unique` and `MoneyInUtility.lm_exists` restate its money-demand lemmas.

The two books use different Obstfeld–Rogoff devices. Woodford's is the boundary condition (4.10)
`lim m v′(m) > 0`, under which no inflationary path is an equilibrium; his `or_*` theorems were
not copied. Cochrane's Online Appendix uses the redemption of money at a floor value `ε`, and
`ObstfeldRogoff` proves that argument directly (`ObstfeldRogoff.or_no_hyperinflation`) together
with Cochrane's demonetised counter-equilibrium. Under the redemption device the outcome depends on
whether the offer is a one-time tender or a standing offer
(`ObstfeldRogoff.cochrane_household_optimal`, `ObstfeldRogoff.standing_redemption_no_optimum`).

## Relation to other Cochrane projects

* **Chapter 3 and Online Appendix §1.6 (`Generality`).** That project owns the valuation equation
  with money in continuous time (its `ContinuousMoney` module). `ContinuousTime` restates (1.28)
  and (1.31)–(1.37) from it (`ContinuousTime.money_printing_iff`,
  `ContinuousTime.money_interest_iff`, `ContinuousTime.money_mixed_iff`), together with the
  misdated integrand of p. 568, which that project found first
  (`ContinuousTime.printed_index_counterexample`).
* **Chapter 2 (`IntertemporalModel`).** The tangent-line inequality for concave functions is
  restated from it (`MoneyInUtility.concave_le_tangent`).
* **Chapter 22 (`ObservationalEquivalence`).** That project owns the general equivalence of money
  regimes, OE-2 (its `MoneyRegimes.oe2`). This project proves the §19.1 statement NI-7
  (`Regimes.ni7`) for the valuation equation `B_{t−1} + M_{t−1} = P_tW_t` with an arbitrary
  expectation operator, and V4 as its open-market special case (`Regimes.omo_equivalence`).

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
