# A two-period model in Lean

This is the `Cochrane/TwoPeriodModel/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Chapter 1, "A two-period model" (pp. 4–19). Model equations hold for an
arbitrary expectation operator, so every result covers perfect foresight and genuine uncertainty:
random variables are functions `Ω → ℝ` and every equation holds state by state. The central object
is the fiscal-theory equilibrium: given fiscal policy and the debt sale, a triple of prices
`(P₀, P₁, Q₀)` satisfying the flow condition, the bond-pricing equation and the date-1 valuation
equation. "The price level is determined" means that there is exactly one such triple. This is
not uniqueness of bounded solutions, the notion of the Woodford projects: with a last day there is
no boundedness to impose, and the valuation equations alone pin down the price level. The library
contains **344 theorems**, including the shared core; 236 of them are in the fourteen chapter
modules.

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises.

Headline results, in the namespace `Cochrane.TwoPeriodModel`:
* **The fiscal theory determines the price level.** On the last day `B₀/P₁ = s₁` has exactly
  one positive solution `P₁ = B₀/s₁` (`TwoPeriod.lastDay_existsUnique`). In two periods, the
  flow condition (1.2), the bond price (1.3) and (1.4) imply the valuation equation
  `B₋₁/P₀ = s₀ + βE₀s₁` (1.5), and conversely (`TwoPeriod.valuation0_of_flow`,
  `TwoPeriod.flow_iff_valuation0`). There is exactly one equilibrium, with
  `P₁ = B₀/s₁` and `P₀ = B₋₁/(s₀ + βE₀s₁)` (`TwoPeriod.equilibrium_existsUnique`,
  `TwoPeriod.equilibrium_iff`), provided the surplus and its present value are positive; without
  that there is none (`TwoPeriod.no_equilibrium_of_s1_nonpos`,
  `TwoPeriod.no_equilibrium_of_pv_nonpos`). In a coin-flip economy, `P₁` is random and `P₀ = 4/3`
  (`TwoPeriod.coin_equilibrium`).
* **The household problem.** The bond price (1.3) and `M₁ = 0` are derived from optimisation.
  An optimal plan holds no money at the end of the last day when `E₀` has no null states
  (`TidyR6Household.money_zero_of_optimal`; the hypothesis is needed,
  `TidyR6Household.money_zero_needs_faithful`). The Euler equation is necessary for every `C¹`
  utility and sufficient for concave utility (`TidyR6Household.euler_of_optimal`,
  `TidyR6Household.optimal_of_euler`, `TidyR6Household.optimal_iff`). At constant consumption it
  is exactly (1.3), and with a random endowment it is the stochastic-discount-factor form
  (`TidyR6Household.euler_const_iff_bondPrice`, `TidyR6Household.euler_iff_sdf`). A competitive
  equilibrium is exactly a fiscal-theory equilibrium (`TidyR6Household.compEqm_iff_equilibrium`),
  and on every finite tree there is exactly one (`TidyR6Household.finiteTree_compEqm_existsUnique`).
  The same holds almost surely on a genuine probability space
  (`TidyR6HouseholdMeasure.m_optimal_iff`, `TidyR6HouseholdMeasure.m_compEqm_iff_equilibrium`).
* **Monetary policy and inflation.** Bond sales raise no extra revenue
  (`MonetaryFiscal.revenue_invariant`). A share split leaves `P₀` unchanged and scales `P₁`
  (`MonetaryFiscal.shareSplit_equilibrium`, `MonetaryFiscal.shareSplit_unique`). An
  interest-rate target, even a peg, has exactly one equilibrium (`MonetaryFiscal.target_existsUnique`,
  `MonetaryFiscal.determinate_under_peg`), and a higher rate raises `P₁` without moving `P₀`
  (`MonetaryFiscal.fisherian_two_period`). (1.9)–(1.10) determine expected and unexpected
  inflation (`MonetaryFiscal.inflation_decomposition`).
* **Debt sales and Table 1.1.** The equity issue, and the rows "Borrow", "Inflate" and "AR(1)" of
  Table 1.1 (`DebtSales.equityIssue_funds_deficit`, `DebtSales.borrow_price0`,
  `DebtSales.inflate_real_debt_falls_by_deficit`, `DebtSales.ar1_price0_rises_more`). The
  borrowing condition of p. 12 is corrected (`DebtSales.borrow_debt_corrected`,
  `DebtSales.borrow_printed_fails`), and the strategy is made implementable under genuine
  uncertainty (`DebtSales.borrow_implementable`). The s-shaped surplus is proved in two periods
  (`DebtSales.sShape_two_period`).
* **A price-level target.** Under the rule (1.13), `P₁ = P₁*` and the equilibrium is unique
  (`PriceLevelTarget.rule_price1`, `PriceLevelTarget.rule_existsUnique`). More debt or a higher
  interest rate lowers `P₀` immediately (`PriceLevelTarget.rule_price0_strictAnti_B0`,
  `PriceLevelTarget.rule_higher_rate_lowers_price0`), and the debt demand curve becomes flat
  (`PriceLevelTarget.rule_flat_demand`).
* **Active versus passive policy.** The budget constraint holds at every price level
  (`ActivePassive.budget_any_price`). Under the passive rule (1.16) the set of equilibrium price
  levels is uncountable (`ActivePassive.passive_indeterminate`). A continuous surplus rule that
  is weakly increasing in `P₁` gives exactly one equilibrium (`ActivePassive.active_existsUnique`).
  More generally, a continuous single-crossing rule, increasing or not, has exactly one
  equilibrium iff `B₀/P − s(P)` changes sign
  (`TidyR5SingleCrossing.singleCrossing_existsUnique_iff`); without continuity or without the
  sign change there can be none (`TidyR5SingleCrossing.discont_singleCrossing_no_eqm`,
  `TidyR5SingleCrossing.continuous_singleCrossing_no_eqm`).
  The `γ`-rule of §1.9 is determinate iff `γ ≠ 1`, correcting "less than one-for-one"
  (`ActivePassive.gamma_rule_determinate_iff`,
  `ActivePassive.less_than_one_for_one_not_necessary`). For general `α` and a random target
  (and random `α`, `γ`), it is determinate iff `γ ≠ 1` and `(α − γ)/(1 − γ) > 0` in every state,
  with `P₁ = P₁*(1 − γ)/(α − γ)` (`TidyR5GammaRandom.gamma_random_existsUnique_iff`,
  `TidyR5GammaRandom.gamma_random_valuation_iff`). Non-identification of `γ` and
  observational equivalence are proved (`ActivePassive.gamma_not_identified`,
  `ActivePassive.obs_equiv_two_period`).
* **The regression of p. 18 as an estimate.** Equilibrium data make the least-squares fit of
  `s₁` on a constant and `B₀/P₁` exactly `(0, 1)`, in every sample and in the population
  (`TidyR6Regression.ols_iff`, `TidyR6Regression.popOLS_equilibrium`). The estimate is consistent
  for the structural `γ` iff `γ = 1` (`TidyR6Regression.ols_consistent_iff`), and in the second
  regression every coefficient is least squares (`TidyR6Regression.gamma_not_identified_sample`,
  `TidyR6Regression.gamma_not_identified_pop`).
* **An infinite horizon.** With the transversality condition in place of the last day, the
  valuation equation `B_{t−1}/P_t = ∑_j β^j E_t s_{t+j}` holds iff the transversality condition
  does (`TidyR6InfiniteHorizon.tvc_iff_valuation`). There is exactly one equilibrium when the
  present value is positive, and none when it is not
  (`TidyR6InfiniteHorizon.equilibrium_existsUnique`,
  `TidyR6InfiniteHorizon.no_equilibrium_of_pv_nonpos`). Under the rule
  `s_t = γB_{t−1}/P_t + ŝ_t`, `P₀` is determined iff `γ ≤ 0` or `γ ≥ 2`
  (`TidyR6InfiniteActivePassive.determinate0_iff`). For `0 < γ < 2` every price path is an
  equilibrium with a suitable debt policy (`TidyR6InfiniteActivePassive.passive_every_price`),
  while `γ = 3` is active (`TidyR6InfiniteActivePassive.gamma_three_active`). The two-period model is the `T = 1`
  truncation (`TidyR6Truncation.finEqm_one_iff`), and as the last day recedes the `T`-period
  prices converge to the infinite-horizon price (`TidyR6Truncation.finEqm_price_tendsto`).
  Under the `γ`-rule, truncation selects the forward solution when `|1 − γ| > β`
  (`TidyR6Truncation.finRule_tendsto`) and can diverge when `1 − β < γ < 1`
  (`TidyR6Truncation.truncation_diverges`).
* **Links to Woodford.** Cochrane's passive response is locally Ricardian in Woodford's sense,
  and every rule that is not locally Ricardian gives a determinate two-period price level
  (`Links.passive_locallyRicardian`, `Links.not_locallyRicardian_two_period_determinate`). The
  passive rule is Woodford's Ricardian rule with `α = 1` (`Links.passive_is_alpha_one`,
  `Links.alpha_one_debt_retired`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections are the three confirmed errors of the chapter
survey:
* the sign in the borrowing condition of p. 12, `(B₀ + ΔB₀)/P₁ = s₁ − RΔs₀`, not `+` (E1);
* the condition for active policy on p. 18: responding "less than one-for-one" is sufficient but
  not necessary, since the rule is determinate iff `γ ≠ 1` (E2);
* the missing positivity hypotheses `s₁ > 0` and `s₀ + βE₀s₁ > 0` behind the price formulas of
  §§1.1–1.4 (E3).

In addition, under genuine uncertainty the borrowing strategy of Table 1.1 cannot keep `P₁`
unchanged by an additive rise in `s₁` unless `s₁` is known at date 0; it is implemented by
scaling debt and surplus together (addendum to E1). The parenthetical of p. 19, "`γ > 0` in the
later intertemporal model" indicates passive policy, is imprecise: with an infinite horizon and
the transversality condition the rule is passive iff `0 < γ < 2`, and `γ = 3` is active
(`TidyR6InfiniteActivePassive.determinate0_iff`, `TidyR6InfiniteActivePassive.gamma_three_active`).

Not formalised: the discursive parts of the chapter: the backing theory, Adam Smith and the
irrelevance of transactions (§1.2, pp. 5–7), the Ricardian/non-Ricardian terminology
(pp. 12–13), and the remark that the active-versus-passive debate is a dead end (p. 19).

The household problem, the infinite horizon and the regression of p. 18 are covered, within
these stated limits:
* Euler necessity for an abstract `ExpectationSystem` assumes `c₁` and `1/P₁` bounded
  (`TidyR6Household.euler_of_optimal`), since an abstract positive linear `E₀` has no
  continuity; the bound is automatic on finite trees.
* On a probability space, Euler necessity assumes `c₀`, `c₁` and `1/P₁` essentially bounded
  (`TidyR6HouseholdMeasure.m_euler_of_optimal`), and the choice set requires `u(c₀)`, `u(c₁)`
  and `B₀` integrable. In `TidyR6HouseholdMeasure.m_compEqm_iff_equilibrium` this reduces to
  `s₁/B₀` essentially bounded and `B₀` integrable.
* The infinite-horizon results use the core `ExpectationSystem` with
  `ExpectationSystem.PullOut` (perfect foresight and finite trees). They are not redone for
  measure-theoretic filtrations with infinitely many shocks.
* The passive construction lets the debt policy adjust:
  `TidyR6InfiniteActivePassive.passive_every_price` has the government choose nominal debt, of
  either sign, to support a given price path. Indeterminacy with an exogenous positive debt
  path is not claimed.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](TwoPeriodModel/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (shared core, restated from the earlier projects) |
| [Expectations](TwoPeriodModel/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; bounded adapted processes; forward series; the pull-out property (shared core) |
| [ExpectationsFiniteTree](TwoPeriodModel/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; coin-flip examples (shared core) |
| [ForwardSolution](TwoPeriodModel/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [TwoPeriod](TwoPeriodModel/TwoPeriod.lean) | 34 | §§1.1–1.3: the last day (1.1), known variables, (1.2)–(1.5), the equilibrium notion, existence and uniqueness of the price level, fiscal news and the discount rate |
| [MonetaryFiscal](TwoPeriodModel/MonetaryFiscal.lean) | 16 | §1.4: (1.8), the share split, interest-rate targets and pegs, (1.9)–(1.10), the Fisherian response |
| [DebtSales](TwoPeriodModel/DebtSales.lean) | 19 | §1.5: the equity issue, Table 1.1 (borrow, inflate, AR(1)) with the borrowing condition corrected, the s-shaped surplus |
| [PriceLevelTarget](TwoPeriodModel/PriceLevelTarget.lean) | 17 | §§1.6–1.7: the rule (1.13), financing a deficit, the rule with an interest-rate target, flat and unit-elastic debt demand |
| [ActivePassive](TwoPeriodModel/ActivePassive.lean) | 25 | §§1.8–1.9: (1.14)–(1.16), active and passive rules, the value-of-debt decomposition, the `γ`-rule corrected, non-identification and observational equivalence |
| [Links](TwoPeriodModel/Links.lean) | 19 | Woodford's locally Ricardian rules (Ch. 4) and Ricardian transversality (Ch. 2), restated and linked to Cochrane's passive policy |
| [TidyR5SingleCrossing](TwoPeriodModel/TidyR5SingleCrossing.lean) | 9 | §1.8: existence for single-crossing rules; a unique equilibrium iff the rule changes sign against `B₀/P`; a decreasing active rule; counterexamples without continuity or the sign change |
| [TidyR5GammaRandom](TwoPeriodModel/TidyR5GammaRandom.lean) | 11 | §1.9: the `γ`-rule for every `γ`; general `α` with a random target and random coefficients, state by state; the condition must hold in every state |
| [TidyR6Household](TwoPeriodModel/TidyR6Household.lean) | 15 | §§1.1–1.3: the household problem for an `ExpectationSystem`; `M₁ = 0` (needs no null states); the Euler equation, necessary and sufficient; (1.3) at constant consumption, the SDF form in general; competitive equilibrium is the fiscal-theory equilibrium, unique on finite trees |
| [TidyR6HouseholdMeasure](TwoPeriodModel/TidyR6HouseholdMeasure.lean) | 13 | The household problem on a probability space with a filtration, almost surely: `M₁ = 0`, the Euler equation in both directions, (1.3), competitive equilibrium |
| [TidyR6InfiniteHorizon](TwoPeriodModel/TidyR6InfiniteHorizon.lean) | 17 | §§1.3–1.4 with an infinite horizon: the real-debt recursion, the valuation equation iff the transversality condition, existence and uniqueness of the price level, `P₀` and debt sales |
| [TidyR6InfiniteActivePassive](TwoPeriodModel/TidyR6InfiniteActivePassive.lean) | 11 | §§1.8–1.9 with an infinite horizon: the rule `s_t = γv_t + ŝ_t` is passive for `0 < γ < 2` and active for `γ ≤ 0` or `γ ≥ 2`; `γ = 3` is active |
| [TidyR6Regression](TwoPeriodModel/TidyR6Regression.lean) | 9 | pp. 18–19: the regressions as least-squares estimates, in the sample and the population; consistency iff `γ = 1`; non-identification of `γ` |
| [TidyR6Truncation](TwoPeriodModel/TidyR6Truncation.lean) | 21 | The `T`-period model: `T = 1` is the two-period model; existence and uniqueness; convergence to the infinite horizon as `T → ∞`; the `γ`-rule with a last day, its limit and divergence |

## Modelling conventions

* **Expectations.** Random variables are `Ω → ℝ`, and every model equation holds as an equality
  of functions, for an arbitrary `ExpectationSystem` (linear, constant-preserving, monotone, with
  the law of iterated expectations). The model uses dates 0 and 1 of the system. Perfect
  foresight (`perfectForesight`) and every finite event tree
  (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) are instances. The coin-flip tree
  (`ExpectationsFiniteTree.coinSystem`) gives an equilibrium with a random price level
  (`TwoPeriod.coin_equilibrium`).
* **Pull-out as a hypothesis.** Results that take date-0 quantities out of `E₀` assume the
  pull-out property (`ExpectationSystem.PullOut`). It holds for perfect foresight
  (`perfectForesight_pullOut`) and every finite tree (`ExpectationsFiniteTree.finiteTree_pullOut`),
  but the `ExpectationSystem` axioms do not imply it.
* **Known variables.** A variable is known at date `t` when `E_t x = x` (`TwoPeriod.Known`).
  Date-0 variables (`B₋₁`, `B₀`, `s₀`, `P₀`) are hypotheses or conclusions of this form. Under
  pull-out, known variables are closed under products, reciprocals and quotients
  (`TwoPeriod.known_mul`, `TwoPeriod.known_inv`, `TwoPeriod.known_div`). The date-1 surplus `s₁`
  and price level `P₁` are random.
* **Equilibrium.** `TwoPeriod.Equilibrium 𝔼 β B₋₁ B₀ s₀ s₁ P₀ P₁ Q₀` holds when:
  * `P₀` and `P₁` are positive in every state;
  * `P₀` is known at date 0;
  * the flow condition (1.2) `B₋₁ = P₀s₀ + Q₀B₀` holds (`TwoPeriod.Flow0`);
  * the bond price (1.3) `Q₀ = βE₀(P₀/P₁)` holds (`TwoPeriod.BondPrice0`);
  * the date-1 valuation equation (1.1)/(1.4) `B₀/P₁ = s₁` holds (`TwoPeriod.Valuation1`).
  "The price level is determined" means that exactly one triple `(P₀, P₁, Q₀)` satisfies this
  (`TwoPeriod.equilibrium_existsUnique`). Under an interest-rate target, `B₀` becomes endogenous
  and the triple is `(P₀, B₀, P₁)` (`MonetaryFiscal.TargetEquilibrium`,
  `PriceLevelTarget.RuleTargetEquilibrium`).
* **Fiscal rules.** For active and passive policy, a date-1 surplus rule is a function
  `s : ℝ → ℝ` of the price level, and its equilibrium set is
  `{P₁ > 0 | B₀/P₁ = s(P₁)}` (`ActivePassive.eqmSet`). Policy is active when this set has exactly
  one element and passive when it is the whole half-line. The `γ`-rule is stated for a
  deterministic target and lifted state by state to a random one
  (`ActivePassive.gamma_rule_random` for `α = 1`; `TidyR5GammaRandom.gammaRuleRandom` for random
  `α`, `γ`, `B₀` and `P₁*`).
* **Explicit hypotheses.** Positivity the book leaves implicit is stated as a hypothesis in each
  theorem: `B₋₁, B₀ > 0`, `s₁ > 0`, `s₀ + βE₀s₁ > 0`, `E₀s₁ > 0` under a target, and
  `E₀(1/P₁*) > 0` under the rule (1.13).

## Relation to the Woodford projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects, so the project builds on its own. `Links` restates two
groups of Woodford results:
* from the Chapter 4 project (`NeoWicksellianFramework`): the debt law of motion under the tax
  rule (4.4) and locally Ricardian tax rules (`Links.Debt45`, `Links.dRec`, `Links.eq_dRec`,
  `Links.rec_bounded`, `Links.rec_unbounded`, `Links.abs_rec_le`, `Links.LocallyRicardian`,
  `Links.locallyRicardian_iff`);
* from the Chapter 2 project (`PriceLevelDetermination`): the Ricardian rule (4.2) and the
  transversality condition (`Links.discount`, `Links.ricardian_step`,
  `Links.ricardian_discounted`, `Links.ricardian_tvc`,
  `Links.ricardian_tvc_fails_of_alpha_zero`).

Nothing is imported from those projects. Identifying Cochrane's `γ` with Woodford's `τ_b`, the
link theorems prove the following:
* the passive response `γ = 1` is locally Ricardian, and a fixed surplus is not
  (`Links.passive_locallyRicardian`, `Links.fixed_surplus_not_locallyRicardian`);
* a response is locally Ricardian iff `1 − β < τ_b < 1 + β` (`Links.locallyRicardian_iff_interval`);
* a `γ`-rule that is indeterminate in two periods is locally Ricardian, but not conversely
  (`Links.two_period_indeterminate_imp_locallyRicardian`,
  `Links.locallyRicardian_two_period_determinate`). So "passive" is a single point with a last
  day, while Woodford's locally Ricardian interval `(1 − β, 1 + β)` is about bounded debt. Under
  Cochrane's transversality notion the infinite-horizon passive interval is `(0, 2)`
  (`TidyR6InfiniteActivePassive.determinate0_iff`);
* every response that is not locally Ricardian gives a determinate two-period price level
  (`Links.not_locallyRicardian_two_period_determinate`);
* Cochrane's passive rule (1.16) is Woodford's Ricardian rule with `α = 1` and no money
  (`Links.passive_is_alpha_one`). It retires all liabilities each period, so the transversality
  condition holds for every price path, just as (1.14) holds for every `P₁`
  (`Links.alpha_one_debt_retired`, `Links.passive_valuation_any_price`);
* with `α = 0` the transversality condition restricts prices (`Links.zero_surplus_restricts_prices`).

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
