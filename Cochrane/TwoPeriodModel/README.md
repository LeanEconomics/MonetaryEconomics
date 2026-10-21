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
contains **238 theorems**, including the shared core; 130 of them are in the six chapter modules.

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
  The `γ`-rule of §1.9 is determinate iff `γ ≠ 1`, correcting "less than one-for-one"
  (`ActivePassive.gamma_rule_determinate_iff`,
  `ActivePassive.less_than_one_for_one_not_necessary`). Non-identification of `γ` and
  observational equivalence are proved (`ActivePassive.gamma_not_identified`,
  `ActivePassive.obs_equiv_two_period`).
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
scaling debt and surplus together (addendum to E1).

Not formalised:
* the discursive parts of the chapter: the backing theory, Adam Smith and the irrelevance of
  transactions (§1.2, pp. 5–7), the Ricardian/non-Ricardian terminology (pp. 12–13), and the
  remark that the active-versus-passive debate is a dead end (p. 19);
* the household problem behind the bond-pricing equation (1.3) and behind zero demand for money
  at the end of the last day: (1.3) and `M₁ = 0` are imposed as equilibrium conditions, not
  derived from optimisation;
* existence of equilibrium for active rules that are single-crossing but not weakly increasing:
  `ActivePassive.active_unique_of_strictAnti` gives at most one equilibrium, and existence is
  proved only for continuous, weakly increasing rules;
* the general-`α` `γ`-rule with a random target (`ActivePassive.gamma_rule_random` takes
  `α = 1`; the general-`α` condition is proved for a deterministic target);
* the regression of p. 18 as a statistical estimate: `ActivePassive.rule_regression_gamma_one`
  proves only that equilibrium data satisfy `s₁ = 1 · B₀/P₁` exactly;
* any infinite-horizon statement. The comparison with an infinite horizon is made only through
  the restated Woodford results in `Links`.

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
  (`ActivePassive.gamma_rule_random`).
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
  day and an interval with an infinite horizon;
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
