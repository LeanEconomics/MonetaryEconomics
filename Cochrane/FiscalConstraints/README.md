# Fiscal constraints in Lean

This is the `Cochrane/FiscalConstraints/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Chapter 6, "Fiscal constraints" (pp. 187–211). Most of the chapter is
deterministic and set in continuous time: present values are genuine improper integrals on
`(0, ∞)`, laws of motion are exact derivatives (`HasDerivAt`), and a present value that the book
calls infinite is proved to be a non-integrable integrand, not a junk value. The stochastic parts
use two different tools. The debt limit with random surpluses (§6.4.1) is proved on a probability
space with independent surpluses and the second Borel–Cantelli lemma. Aggregate uncertainty
(§§6.4.6–6.4.7) is stated for an arbitrary `ExpectationSystem` with the pull-out property, with a
two-state i.i.d. coin tree as a witness under genuine uncertainty. Both are then re-proved on
genuine infinite-horizon i.i.d. processes with Mathlib's conditional expectation: i.i.d. surplus
processes for §6.4.1, and i.i.d. growth processes, including a constructed lognormal process and
an infinite coin process for Bohn's example, for §6.4.7. The library contains **676 theorems**,
including the shared core; 460 of them are in the eighteen chapter modules.

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises.

Headline results, in the namespace `Cochrane.FiscalConstraints`:
* **r versus g: indeterminacy, not infinity.** The debt-to-GDP ratio obeys (6.4),
  `x' = (r − g)x − s/y` (`LinearODE.debt_gdp_ode`). For `r > g` the forward present value of
  surpluses is the unique bounded solution, and the transversality condition holds exactly for it
  (`RvsG.existsUnique_bdd`, `RvsG.bddOn_iff`, `RvsG.tvc_levels_iff`), so nominal debt determines the
  price level (`RvsG.nominal_determinacy`). For `r < g` every solution is bounded and any two
  converge, so every price level gives a bounded debt path (`RvsG.bddOn_of_neg`,
  `RvsG.tendsto_sub_of_neg`, `RvsG.nominal_indeterminacy`), while the transversality condition
  fails for every price level when the surplus ratio is a nonzero constant
  (`RvsG.tvc_fails_of_neg`). `r = g` is the knife edge (`RvsG.bddOn_iff_zero`). A temporary
  period of `r < g` restores a unique bounded solution, given by the corrected 20-year formula
  (`RvsG.step_existsUnique`, `RvsG.book_twenty_year_formula`). So do finitely many regimes of
  any signs, with a general 20-year formula, and `r > g` after the last switch is necessary as
  well as sufficient (`TidyR5PiecewiseRvsG.pw_existsUnique`, `TidyR5PiecewiseRvsG.pwPV0_eq_sum`,
  `TidyR5PiecewiseRvsG.pw_unique_iff_last_pos`). The same dichotomy holds in
  discrete time (`RvsG.eq_pvD_of_bddD`, `RvsG.nominal_determinacy_D`,
  `RvsG.nominal_indeterminacy_D`).
* **The backward solution (6.5) corrected.** The solution of (6.4) is
  `x_t = e^{(r−g)t}x₀ − ∫₀^t e^{(r−g)τ}σ_{t−τ}dτ`, unique by the fundamental theorem of calculus
  (`LinearODE.corrected_6_5`, `LinearODE.eq_vocFrom`). The printed formula fails in both its sign
  and its exponent (`LinearODE.printed_6_5_wrong_sign`, `LinearODE.printed_6_5_wrong_exponent`).
* **A debt limit with stochastic surpluses (Theorem S).** With permanent `r < g`, independent
  surpluses bounded above and a probability of a deficit of size `c` bounded away from zero, debt
  exceeds every level below `c/(1 − γ)` infinitely often, almost surely
  (`DebtLimitStochastic.frequently_exceeds`), so no initial debt is sustainable
  (`DebtLimitStochastic.not_sustainable`). With i.i.d. integrable surpluses that allow deficits of
  every size, and no upper bound on surpluses, debt is almost surely unbounded
  (`DebtLimitStochasticMeasure.iid_unbounded_of_integrable`), in particular with i.i.d. Gaussian
  surpluses (`DebtLimitStochasticMeasure.gaussian_process_unbounded`,
  `DebtLimitStochasticMeasure.gaussian_process_not_sustainable`). The same holds for a
  constructed Gaussian AR(1) surplus, which is not bounded above, so Theorem S does not apply
  (`TidyR5GaussianAR1.gaussian_ar1_unbounded`, `TidyR5GaussianAR1.gaussian_ar1_not_sustainable`,
  `TidyR5GaussianAR1.arSurplus_not_ae_bdd_above`). The earlier Gaussian theorem
  `DebtLimitStochastic.gaussian_iid_unbounded` is vacuous: it also assumes surpluses bounded
  above, which no non-degenerate Gaussian is
  (`DebtLimitStochasticMeasure.gaussian_iid_unbounded_vacuous`). The book's claim that bounded
  support still breaks any bound is false (`DebtLimitStochastic.bounded_support_counterexample`).
* **The present-value Laffer curve.** The present value of revenue `τy/(r − g)` and its elasticity
  are exact, for the improper integral itself (`Laffer.pv_tax_eq`,
  `Laffer.pv_integral_elasticity`), and the book's example is exactly at the top of the curve
  (`Laffer.book_top_of_curve`).
* **Discount rates and growth.** The first-order condition `r = δ + γg` (6.1)/(6.6), as an exact
  log form and as an exact derivative (`DiscountGrowth.euler_discrete_iff`,
  `DiscountGrowth.euler_exponential_iff`, `GrowthTheoryTVC.hasDerivAt_log_marginalUtility`). The
  value of debt does not depend on growth for `γ = 1` and falls with growth for `γ > 1`
  (`DiscountGrowth.value_indep_of_g`, `DiscountGrowth.value_strictAntiOn`). The growth-theory
  transversality condition holds iff `r > g`, and with `δ = 0` iff `γ > 1`
  (`GrowthTheoryTVC.tvc_iff`, `GrowthTheoryTVC.tvc_delta_zero_iff`). Population growth allows
  `r < g` with the per-capita condition satisfied (`GrowthTheoryTVC.population_allows_r_lt_g`).
* **Crashes and breakouts.** In Miller's two-period model with a surplus cap the price level is
  `P₀ = max(P*/(β(1 + i₀)), B₋₁/(s₀ + βs^max))` in every equilibrium with outstanding debt
  (`Crash.eq_price0`), an equilibrium exists iff `s₀ + βs^max > 0`
  (`Crash.exists_equilibrium_iff`), and the regimes switch endogenously, with the comparative
  statics of each regime as exact derivatives (`Crash.boundary_iff`,
  `Crash.hasDerivAt_price0_s0_constrained`, `Crash.hasDerivAt_price1_i0_constrained`).
* **Money, liquidity and return discounting.** (6.8)–(6.13) as exact derivatives and
  finite-horizon identities; in the steady state the two terms of (6.12) diverge to `−∞` and `+∞`
  while those of (6.13) converge (`MoneyLiquidity.steady_6_12_explodes`,
  `MoneyLiquidity.steady_6_13_converges`), and (6.9) is the improper present-value integral
  (`MoneyLiquidity.eq_6_9`). A money-and-debt path with value (6.9) and the transversality
  condition exists, uniquely, iff the improper present value converges, with no sign of
  `r^f − g` and no bound on flows assumed (`TidyR5MoneyExistence.money_debt_exists`,
  `TidyR5MoneyExistence.money_debt_exists_iff`, `TidyR5MoneyExistence.money_debt_unique`).
  The return-discounted identity (6.14) holds state by state
  (`ReturnDiscounting.eq_6_14_pathwise`).
* **Aggregate uncertainty and Bohn's example.** The true present value (6.15) can converge while
  the mistaken one (6.16) explodes (`AggregateUncertainty.correct_finite_incorrect_explodes`).
  With corrected lognormal formulas this region is non-empty for every `γ > 0`
  (`AggregateUncertainty.region_nonempty_iff`, `AggregateUncertainty.bohn_region`). (6.17) holds
  for any debt rolled over at the risk-free rate (`AggregateUncertainty.eq_6_17`), and a two-state
  coin tree with `r_f ≈ 0.83% < E g = 5%` satisfies (6.17) and (6.18) under genuine uncertainty
  (`AggregateUncertainty.bohn_numbers`, `AggregateUncertainty.bohn_witness_6_17`,
  `AggregateUncertainty.bohn_witness_6_18`).
* **Genuine probability models.** §6.4.7 holds on a genuine i.i.d. growth process on `ℕ → ℝ`
  under `ν^ℕ`, with consumption `c_t = ∏_{i<t} g(ε_{i+1})` and Mathlib's `condExp`: the process has
  i.i.d. growth at every date (`AggregateUncertaintyMeasure.meas_iidGrowth`), (6.15) and (6.16)
  converge or explode almost surely under the same conditions
  (`AggregateUncertaintyMeasure.correct_finite_incorrect_explodes`), and the present values are
  expectations of genuine infinite sums, `E_t Σ_{j≥1} = qκ/(1 − q)` for (6.15) and
  `c_t = E_t Σ_{j≥1} β^j (c_{t+j}/c_t)^{−γ} s_{t+j}` for (6.17) when `βE[G^{1−γ}] < 1`
  (`AggregateUncertaintyMeasure.E_tsum_correct_pv`, `AggregateUncertaintyMeasure.E_tsum_bohn_pv`).
  Bohn's example runs on an infinite i.i.d. coin process in which every history has probability
  zero (`AggregateUncertaintyMeasure.bohn_infinite_witness`), and agrees with the coin tree
  (`AggregateUncertaintyMeasure.bohnTree_measIIDGrowth`, `AggregateUncertaintyMeasure.link_pv_term_c`).
  Growth `G = exp ε` with `ε` i.i.d. `N(μ, v)` is a constructed lognormal process
  (`LognormalGrowthMeasure.map_growth`, `LognormalGrowthMeasure.iIndepFun_growth`) on which the
  region "true present value finite, mistaken one explodes" is non-empty iff `γ > 0`
  (`LognormalGrowthMeasure.lognormal_region_iff`). For §6.4.1, Theorem S holds for i.i.d.
  coordinate surpluses (`DebtLimitStochasticMeasure.iid_frequently_exceeds`), and i.i.d. Gaussian
  surpluses make debt almost surely unbounded (`DebtLimitStochasticMeasure.gaussian_process_unbounded`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections are the confirmed errors of the chapter survey:
* the backward solution (6.5), p. 196, has the wrong sign on the integral and the homogeneous
  term lacks `t` in its exponent (E6.1);
* the 20-year forward formula, p. 196, discounts past surpluses `σ_{t−τ}` instead of future
  surpluses `σ_{t+τ}` (E6.2);
* the "incorrect" lognormal term, p. 206, drops a `σ²/2`: it is `(γ² + 1)σ²/2`, not `γ²σ²/2`, so
  the region "true present value finite, mistaken one explodes" exists for every `γ > 0` (E6.5);
* Bohn's risk-free rate, p. 206, `r = δ + γg − ½γ(γ − 1)σ²`, matches neither lognormal convention
  (E6.7);
* "the last term converges to zero, via the transversality condition", p. 207, is a parameter
  restriction, `βE[G^{1−γ}] < 1` (E6.8);
* "even if we limit the support … the integral of the surplus eventually exceeds any bound",
  p. 197, is false: bounded deficits keep debt below `max x₀ (c/(1 − γ))`.

In addition, the typos E6.4 (`B₁` for `B₋₁`, p. 194) and E6.6 (a missing `+`, p. 206) are
corrected, the rounding in E6.3 (a 20% rise is a log change of 18.2%) and in "e^{−0.2} = 80%"
(81.9%) is made exact, the §6.3 regime claims are shown to need outstanding debt `B₀ ≠ 0`, and the
slogan "indeterminacy, not infinity" is shown to use two different criteria for its two halves.
The main correction to this formalisation rather than the book is that the earlier Gaussian debt
theorem `DebtLimitStochastic.gaussian_iid_unbounded` (and `Links.gaussian_not_bddD`, which uses
its hypotheses) is vacuous, and is replaced by
`DebtLimitStochasticMeasure.iid_unbounded_of_integrable` and
`DebtLimitStochasticMeasure.gaussian_process_unbounded`.

Not formalised:
* Miller's learning model (p. 195), a verbal summary of another paper;
* the claim that a managed surplus restores global determinacy (p. 197; survey E6.9): no surplus
  rule is specified. Only the boundary-avoiding management itself is formalised
  (`DebtLimitStochastic.managedPath_le`), as an adapted policy on the i.i.d. process
  (`DebtLimitStochasticMeasure.managed_adapted`, `DebtLimitStochasticMeasure.managedPath_le_process`),
  and Theorem S shows that without management no debt is sustainable;
* the continuous-time (Ornstein–Uhlenbeck) AR(1) surplus of p. 197, which needs Itô calculus. It
  is replaced by its discrete analogue, a Gaussian AR(1) surplus process on `ν^ℕ`
  (`TidyR5GaussianAR1.ar1_hasLaw_gaussian`, `TidyR5GaussianAR1.gaussian_ar1_unbounded`), with the
  book's decay `ρ = e^{−η}` per period (`TidyR5GaussianAR1.gaussian_ar1_exp_unbounded`);
* the discursive passages: dynamic inefficiency, overlapping generations and demographics
  (p. 200), the discussion paragraphs of §6.4.6 and §6.4.8, and contingent liabilities (§6.5,
  pp. 209–211).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](FiscalConstraints/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (shared core, restated from the earlier projects) |
| [Expectations](FiscalConstraints/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; bounded adapted processes; forward series; the pull-out property (shared core) |
| [ExpectationsFiniteTree](FiscalConstraints/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; coin-flip examples (shared core) |
| [ForwardSolution](FiscalConstraints/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [ExpIntegrals](FiscalConstraints/ExpIntegrals.lean) | 17 | Infrastructure for §§6.1–6.4.5: `∫₀^∞ e^{−au} = 1/a`, genuine non-integrability for `a ≤ 0`, growing streams `c/(r − g)`, bounds, translation, exponential limits and the transversality condition of a bounded path |
| [Laffer](FiscalConstraints/Laffer.lean) | 14 | §6.1: the present value of revenue, static and present-value elasticities as exact derivatives, the top of the curve, sensitivity in `r − g`, the 18.2% remark (E6.3) |
| [DiscountGrowth](FiscalConstraints/DiscountGrowth.lean) | 14 | §6.2, (6.1)–(6.2): `r = δ + γg` exactly, the value of debt and its dependence on growth; population growth (§6.4.4) |
| [Crash](FiscalConstraints/Crash.lean) | 28 | §6.3: Miller's two-period model with a surplus cap; both regimes, the endogenous boundary, the global price formula, existence and uniqueness, monotonicity, continuity and exact comparative statics; the `B₀ = 0` equilibrium |
| [LinearODE](FiscalConstraints/LinearODE.lean) | 12 | (6.4)–(6.5): the debt-to-GDP equation as an exact derivative, variation of constants and uniqueness, (6.5) corrected (E6.1), the finite-horizon identity and the forward present value |
| [RvsG](FiscalConstraints/RvsG.lean) | 69 | §§6.4.1–6.4.3, (6.3): the r-versus-g dichotomy in continuous and discrete time, the TVC, nominal determinacy and indeterminacy, temporary `r < g` with the 20-year formula corrected (E6.2), steady states and the book's numbers |
| [DebtLimitStochastic](FiscalConstraints/DebtLimitStochastic.lean) | 20 | §6.4.1, p. 197: Theorem S by the second Borel–Cantelli lemma, Gaussian surpluses (vacuous, see `DebtLimitStochasticMeasure`), the bounded-support counterexample, the managed surplus |
| [GrowthTheoryTVC](FiscalConstraints/GrowthTheoryTVC.lean) | 18 | §6.4.4: (6.6) as an exact derivative, when `r > g`, the transversality condition iff `r > g` (iff `γ > 1` at `δ = 0`), population growth |
| [MoneyLiquidity](FiscalConstraints/MoneyLiquidity.lean) | 17 | §6.4.5, (6.7)–(6.13): steady-state seigniorage, the money/GDP law of motion, both finite-horizon representations, (6.9) as an improper integral, explosion of (6.12) and convergence of (6.13), the TVC with the marginal rate of substitution |
| [ReturnDiscounting](FiscalConstraints/ReturnDiscounting.lean) | 8 | §6.4.6, (6.14): the return-discounted identity state by state and under `E_t`, the SDF version, when the return-discounted present value is correct, the linear discount factor |
| [AggregateUncertainty](FiscalConstraints/AggregateUncertainty.lean) | 52 | §6.4.7, (6.15)–(6.18): correct and mistaken present values under i.i.d. growth, lognormal moments with E6.5–E6.7 corrected, (6.17) and (6.18), the two-state coin-tree witness |
| [Links](FiscalConstraints/Links.lean) | 16 | Agreement between the two formalisation chains: (6.9) is the §6.4.1 present value, (6.1) = (6.6), the growth TVC is the levels TVC, Theorem S paths are discrete solutions of (6.4), and `r_f < g` with a finite present value needs risk |
| [ExpectationsMeasure](FiscalConstraints/ExpectationsMeasure.lean) | 71 | Measure-theoretic expectations (shared core, copied from `ObservationalEquivalence`): `MeasExpectationSystem` with Mathlib's `condExp`, the axioms a.e., news, the forward equation and sunspots, AR(1) conditional variance, bridges to and from the core `ExpectationSystem` |
| [ExpectationsMeasureIID](FiscalConstraints/ExpectationsMeasureIID.lean) | 37 | The genuine i.i.d. economy on `ℕ → ℝ` under `ν^ℕ` (shared core): independence, moments, every history null, determinacy iff `\|a\| < 1`, AR(1), the `±1` coin |
| [AggregateUncertaintyMeasure](FiscalConstraints/AggregateUncertaintyMeasure.lean) | 49 | §6.4.7, (6.15)–(6.18) on a genuine i.i.d. growth process: independence of past and future, i.i.d. growth a.e., `E_t` through infinite sums, (6.15) and (6.17) as expectations of infinite sums, (6.18) diverging a.s., Bohn's example as an infinite coin process, links to `IIDGrowth` and the coin tree |
| [LognormalGrowthMeasure](FiscalConstraints/LognormalGrowthMeasure.lean) | 19 | §6.4.7: a constructed lognormal growth process (`exp` of i.i.d. `N(μ, v)`), its law, independence and moments; (6.15)–(6.18) on it, the printed exponent wrong (E6.5), the region non-empty iff `γ > 0`, the corrected risk-free rate (E6.7) |
| [DebtLimitStochasticMeasure](FiscalConstraints/DebtLimitStochasticMeasure.lean) | 24 | §6.4.1, p. 197, on i.i.d. surplus processes: Theorem S, the bounded-support dichotomy for coin surpluses, `DebtLimitStochastic.gaussian_iid_unbounded` shown vacuous, debt a.s. unbounded for integrable surpluses with deficits of every size (Kolmogorov's 0-1 law), Gaussian surplus processes, the managed surplus as an adapted policy |
| [TidyR5MoneyExistence](FiscalConstraints/TidyR5MoneyExistence.lean) | 22 | §6.4.5, (6.9): existence of the money-and-debt solution with the forward value and the TVC, iff the improper present value converges; uniqueness; the TVC iff the value (6.9); the Bochner form |
| [TidyR5PiecewiseRvsG](FiscalConstraints/TidyR5PiecewiseRvsG.lean) | 39 | §6.4.1, p. 196: temporary `r < g` with a general eventually-constant `r − g` and with finitely many regimes; existence, uniqueness, explosion, the TVC, the general 20-year formula, `r > g` at the end necessary, the link to `RvsG` |
| [TidyR5GaussianAR1](FiscalConstraints/TidyR5GaussianAR1.lean) | 22 | §6.4.1, p. 197: a Gaussian AR(1) surplus process on `ν^ℕ`, its law and forecast, not bounded above; debt a.s. unbounded and no debt limit sustainable (Kolmogorov's 0-1 law), also for `ρ = e^{−η}` |

## Modelling conventions

* **Continuous time.** Paths are functions `ℝ → ℝ`. Laws of motion hold as exact derivatives
  (`HasDerivAt`) at every date, present values are Bochner integrals on `(0, ∞)` or `(t, ∞)`, and
  "the present value is infinite" means that the integrand is not integrable
  (`ExpIntegrals.not_integrableOn_exp_growth`). Elasticities are exact derivatives with respect to
  `log τ`.
* **The debt-to-GDP equation.** With `x = b/y`, `σ = s/y` and `a = r − g`, (6.4) is
  `x' = ax − σ`. A solution on `[0, ∞)` is continuous on `[0, ∞)` and satisfies the equation at
  every `t > 0` (`RvsG.SolvesOn`); surplus ratios are continuous and bounded by `M`. The
  determinacy criterion is boundedness of the debt-to-GDP ratio (`RvsG.BddOn`); the transversality
  condition `e^{−rt}b_t → 0` is proved separately (`RvsG.tvc_iff`, `RvsG.tvc_levels_iff`). With
  nominal debt `B₀`, the initial ratio is `x₀ = B₀/(P₀y₀)`. The discrete analogue is
  `x_{t+1} = γx_t − w_t` with `γ = (1 + r)/(1 + g)` (`RvsG.SolvesD`).
* **Miller's model.** §6.3 restates the two-period model of Chapter 1 under perfect foresight with
  an interest-rate target: `Crash.IsEquilibrium` holds for positive price levels satisfying the
  budget, the bond price and `B₀/P₁ = s₁` under the capped rule `Crash.surplus1`.
* **Probability for Theorem S.** `DebtLimitStochastic` works on a measure space with a probability
  measure; surpluses are measurable and independent (`iIndepFun`), and the debt path is, state by
  state, the discrete backward solution of `RvsG` (`DebtLimitStochastic.debtPath`). Its theorems
  assume surpluses bounded above almost surely, so its Gaussian case
  (`DebtLimitStochastic.gaussian_iid_unbounded`) has inconsistent hypotheses and proves nothing
  about Gaussian surpluses. `DebtLimitStochasticMeasure` takes the surpluses to be the coordinates
  of `ℕ → ℝ` under `ν^ℕ`, with the natural filtration, so the debt ratio is an adapted process
  (`DebtLimitStochasticMeasure.debtPath_adapted`); there unboundedness needs only integrable
  surpluses with deficits of every size
  (`DebtLimitStochasticMeasure.iid_unbounded_of_integrable`), which covers i.i.d. Gaussian
  surpluses (`DebtLimitStochasticMeasure.gaussian_process_unbounded`).
* **Expectations for §§6.4.6–6.4.7.** Random variables are `Ω → ℝ` under an arbitrary
  `ExpectationSystem` with the pull-out property (`ExpectationSystem.PullOut`). I.i.d. growth is the
  hypothesis `E_t[G_{t+1}^a] = mom a` for every real `a` (`AggregateUncertainty.IIDGrowth`), and
  "powers of consumption are known" is the hypothesis `AggregateUncertainty.KnownPowers`, because
  the expectation axioms do not imply that functions of known variables are known. Both are proved
  for the coin tree (`AggregateUncertainty.bohnSystem_iid`,
  `AggregateUncertainty.bohnSystem_knownPowers`).
* **Measure-theoretic expectations.** The core `ExpectationSystem` (an operator `E_t` on all
  functions `Ω → ℝ`, with exact equalities) is kept unchanged, and every result above that is
  stated for it still holds. On a countable `Ω` it forces finitely supported forecasts, so it
  cannot carry an infinite-horizon model with nondegenerate shocks. `ExpectationsMeasure` adds,
  alongside it, a probability space with a filtration (`ExpectationsMeasure.MeasExpectationSystem`):
  `E_t` is Mathlib's conditional expectation `condExp`, and equations hold almost everywhere. The
  bridge is additive and runs both ways: a finite event tree is a measure system with the same
  `E_t` at every state (`ExpectationsMeasure.TreeBridge.treeSystem_E`), and a measure system on a
  finite discrete state space with full support is a core system with the pull-out property
  (`ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem`,
  `ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_pullOut`). The genuine instance
  is the i.i.d. economy on `ℕ → ℝ` under `ν^ℕ`, in which every history has probability zero
  (`ExpectationsMeasureIID.iidSystem`, `ExpectationsMeasureIID.iid_not_finitely_supported`). For
  §6.4.7, consumption is `c_t = ∏_{i<t} g(ε_{i+1})` for a growth law `g` with every moment finite
  (`AggregateUncertaintyMeasure.GrowthLaw`, `AggregateUncertaintyMeasure.cons`), present values
  are genuine infinite sums with `E_t` taken through them
  (`AggregateUncertaintyMeasure.E_tsum_of_summable_integral`, from Mathlib's `condExp_tsum`), and
  the a.e. form of i.i.d. growth (`AggregateUncertaintyMeasure.MeasIIDGrowth`) gives the core
  `AggregateUncertainty.IIDGrowth` on finite full-support systems
  (`AggregateUncertaintyMeasure.MeasIIDGrowth.toCore`).
* **Explicit hypotheses.** Hypotheses the book leaves implicit are stated in each theorem: `r > g`
  for every closed-form present value; `B₀ ≠ 0`, `1 + i₀ > 0` and `s₀ + βs^max > 0` in §6.3;
  `0 ≤ γ < 1` and surpluses bounded above for Theorem S (integrable surpluses for the
  unbounded-debt theorem); `βE[G^{1−γ}] < 1` for the infinite-horizon
  present value of §6.4.7; `p_{s+1} + d_{s+1} ≠ 0` for (6.14).

## Relation to the Woodford and Galí projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects (the first three from `Woodford/ReturnOfMonetaryRules`,
`ForwardSolution` from the Woodford Chapter 2 and 3 projects), so the project builds on its own.
Nothing is imported from those projects. The chapter modules use only part of the core:
`ExpectationSystem` and `ExpectationSystem.PullOut` in `ReturnDiscounting` and
`AggregateUncertainty`, the finite event tree (`ExpectationsFiniteTree.FiniteTree`,
`ExpectationsFiniteTree.finiteTree_pullOut`) for the Bohn witness, and `ForwardSolution.E_of_known`
in `AggregateUncertainty`. `Determinacy` and the forward-series theory are carried for the later
Cochrane projects. The measure-theoretic core (`ExpectationsMeasure`, `ExpectationsMeasureIID`)
is copied, with only the namespace renamed, from the Cochrane `ObservationalEquivalence` project;
the three measure modules use its i.i.d. economy (`ExpectationsMeasureIID.iidSystem`) and its
bridge from finite event trees (`ExpectationsMeasure.TreeBridge.treeSystem`), and
`TidyR5GaussianAR1` builds its AR(1) surplus from `ExpectationsMeasureIID.ar1` on the same
economy.

Unlike the Chapter 1 project, no Woodford or Galí result is restated in a chapter module, and
`Links` links the chapter's own two formalisation chains rather than other books. Two
correspondences are recorded here without a link theorem:
* the r-versus-g dichotomy of `RvsG` is the deterministic, debt-to-GDP analogue of Woodford's
  intertemporal budget constraint and transversality condition (Chapter 2, `PriceLevelDetermination`),
  and its discrete case (D5) is the bounded-input-bounded-state recursion of Woodford's fiscal
  analysis (Chapter 4, `NeoWicksellianFramework`);
* Miller's model in `Crash` uses the equilibrium of Cochrane's own Chapter 1 (the `TwoPeriodModel`
  project), restated in `Crash.IsEquilibrium` and `Crash.isEquilibrium_iff` rather than imported.

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
