# Assets, rules and balance sheets in Lean

This is the `Cochrane/AssetsRulesBalanceSheets/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Part II, Chapters 8–10: "Assets and choices" (pp. 238–258), "Better
rules" (pp. 259–286) and "Balance sheets and pots of assets" (pp. 287–311). Two claims from later
chapters that the surveys assign here are included: the real-bills doctrine of §11.5 (p. 322) and
the exchange-rate claims of §24.3 (p. 527). The setting is the book's: flexible prices, a constant
real rate `1/β`, and nominal, indexed, foreign-currency or defaultable one-period debt. Random
variables are `Ω → ℝ` under an arbitrary `ExpectationSystem`, so the structural results hold under
perfect foresight and under genuine uncertainty; comparative statics, numbers and some witnesses
are deterministic. The library contains **449 theorems**, including the shared core; 341 of them
are in the nineteen chapter modules (seventeen for the book's sections, plus the shared
`PresentValue` and the cross-chapter `Links`).

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises. "Theorem IT", "Theorem FR",
"Theorem ST" and "Theorem IP" are the labels of the chapter survey for the main claims of §9.2,
§9.3.2, §9.4.1 and §9.5.

Headline results, in the namespace `Cochrane.AssetsRulesBalanceSheets`:
* **Valuation equations, once.** Every valuation equation in Part II is the forward iterate of a
  flow `x_t = s_t + βE_tx_{t+1}` under a transversality condition, proved once in expected form
  and in pathwise form (`PresentValue.flow_tvc_iff_pv`, `PresentValue.real_flow_tvc_iff`,
  `PresentValue.tendsto_partialSums_of_tvc`, `PresentValue.eq_zero_of_tvc`).
* **Indexed, foreign and mixed debt (§§8.1–8.3).** With only indexed debt the price level drops
  out of the flow (`RealDebt.indexedFlow_price_free`) and (8.1) is a restriction on surpluses
  (`RealDebt.indexed_pv_news_zero`); nominal debt outstanding with real debt issued determines
  `P_t` (`RealDebt.nominalOutstanding_price_unique`); foreign-currency debt must be defaulted on
  when surpluses fall short (`RealDebt.foreign_default_required`). With both kinds of debt the
  price level is `P = B/(V − b)` and exists iff `V > b` (`CapitalStructure.mixed_price_unique`,
  `CapitalStructure.mixed_no_price`); its elasticity to fiscal news is exactly `−V/(V − b)` and
  rises with real debt (`CapitalStructure.log_price_elasticity`,
  `CapitalStructure.elasticity_strictMono`); the cashless limit is determinate along the sequence
  and indeterminate at the limit (`CapitalStructure.cashless_limit_indeterminate`).
* **Maturity and default (§§8.4–8.6).** (8.4) is derived from (3.20)–(3.21)
  (`MaturityBuffer.identity_84`); matching maturities to surpluses insulates the price level
  from real rates under perfect foresight, and only matching does (`MaturityBuffer.price_insulated`,
  `MaturityBuffer.price_insulated_only_if_matching`), but not under uncertainty
  (`MaturityBuffer.matching_fails_under_uncertainty`). An expected haircut does not move `P_t`
  (`Default.expected_default_no_effect`); "2 bonds at 50% = 1 bond" (`Default.scaled_flow_iff`);
  an independent central bank turns a fiscal shortfall into default instead of inflation
  (`CentralBankIndependence.independence_default_vs_inflation`).
* **An inflation target (§9.2, Theorem IT).** Under the surplus rule (9.4) and the rate target
  (9.5), `P = P*` is the unique equilibrium (`InflationTarget.price_eq_target`,
  `InflationTarget.exists_equilibrium`), provided `0 < α < 2`, which the book omits
  (`InflationTarget.tendsto_state_forecast_iff`); either policy alone is insufficient
  (`InflationTarget.target_alone_insufficient`, `InflationTarget.rule_alone_insufficient`).
* **Fiscal rules and the rate target (§9.3.2, Theorem FR).** The claim that only `P = P*`
  satisfies (9.9) and (9.12) is true under perfect foresight, false under uncertainty in general,
  and true under uncertainty for price levels bounded above or bounded away from zero. See the
  next section.
* **Other rules (§§9.3.3–9.6).** The regular budget repays itself for every `α_r > 0`
  (`FiscalRules.regular_tvc`); the fiscal Taylor rule (9.16) determines inflation iff
  `θ_{sπ} ≠ 0` (`FiscalTaylor.pi_determined`,
  `FiscalTaylor.pi_not_determined_without_surplus_response`); with nominal debt a nondecreasing
  surplus suffices (`MixedDebtRules.price_unique`). Theorem ST: under a spread target,
  unexpected inflation is `−D/(D + ρ)` times the fiscal shock, with existence and uniqueness for
  every `θ ∈ [0, 1]` (`SpreadTarget.unexpected_inflation_iff`, `SpreadTarget.exists_solution`,
  `SpreadTarget.unique_solution`). Free swaps at `P*` do not reach the target
  (`SpreadSwap.swap_reaches_target_iff`). Theorem IP: an indexed-debt peg gives `P = P*`
  (`IndexedDebtPeg.price_eq_target`, `IndexedDebtPeg.one_period_deviation`).
* **Pots of assets and balance sheets (Chapter 10).** The value of nominal liabilities equals the
  value of the bank's assets iff the flow and transversality conditions hold
  (`PotOfAssets.pot_valuation_iff`), purchases at market prices do not move `P`
  (`PotOfAssets.purchases_irrelevant`), and a conversion right is arbitrage-free iff (10.3) holds
  (`PotOfAssets.no_arbitrage_iff`). The perpetuity and one-period numeraires of p. 296 are
  corrected (`SharesAsMoney.perpetuity_price_level`, `SharesAsMoney.oneperiod_price_level`). A
  central bank holding only nominal government debt cannot determine the price level; one with
  real assets can (`BalanceSheets.nominal_cb_cannot_determine`,
  `BalanceSheets.real_cb_determines`).
* **Real bills and exchange rates (§11.5, §24.3).** Money issued against a real asset at market
  value leaves `P` unchanged (`PotOfAssets.real_bills_real_asset`). Separate surplus pools give a
  determinate exchange rate, the ratio of debt to surplus present values
  (`ExchangeRates.separate_pools_exchange_rate`); a common pool leaves every rate `e > 0`
  consistent with equilibrium (`ExchangeRates.common_pool_indeterminate`).

## The §9.3.2 uniqueness question (E9.9), settled

On p. 267 the book pairs the dynamic fiscal rule `s_t = s_{0,t} + θ(P_t − P*_t)` with indexed
debt, so that the valuation equation (9.9) holds, and an interest-rate target
`1/(1 + i_t) = βE_t(P*_t/P*_{t+1})` (9.12), and states that "only the sequence `P_t = P*_t`
satisfies both (9.9) and (9.12)". The chapter survey found this false under uncertainty and left
open whether bounded price levels restore it. Formalisation settles it in four parts, with
`P* ≡ 1` in (b) and (d).

* **(a) True under perfect foresight.** If (9.12) holds and (9.9) holds at date 0 with initial
  debt equal to the present value of `s₀` (the book's `a(β) = 0` case), then `P_t = P*_t` at every
  date (`FiscalRules.fr_perfectForesight`), and `P = P*` is an equilibrium
  (`FiscalRules.fr_exists`).
* **(b) False under uncertainty in general.** An explicit infinite "settle-or-continue" event
  tree is an equilibrium for every `0 < β < 1`, every initial price level `0 < P_0 < 1 = P*_0`,
  every rule coefficient `θ` and every initial debt `b̄`
  (`FiscalRules.Sunspot.sunspot_counterexample`). At each date the unsettled path either settles
  at a constant price level forever or continues at a lower price level, with settle probabilities
  strictly between 0 and 1 (`FiscalRules.Sunspot.settleProb_bounds`) chosen so that `1/P` is a
  martingale, which is (9.12) (`FiscalRules.Sunspot.martingale_inv`). Real debt is predetermined
  and satisfies (9.8) on every edge (`FiscalRules.Sunspot.flow_cont`); (9.9) holds at every node
  as a genuine convergent series of explicit conditional expectations
  (`FiscalRules.Sunspot.valuation_cont`, `FiscalRules.Sunspot.valuation_settled`) and ex post
  along every settling path (`FiscalRules.Sunspot.valuation_expost`); the transversality
  condition holds at every node (`FiscalRules.Sunspot.tvc_cont`). The path never settles with
  probability zero (`FiscalRules.Sunspot.contProb_tendsto_zero`).
* **(c) What survives in general.** Since `P*_t/P_t` is a martingale, Jensen's inequality gives
  `P_0 ≤ P*_0` in every equilibrium (`FiscalRules.fr_jensen`). The counterexample shows that this
  one-sided bound is all that survives without further restrictions.
* **(d) True for bounded price levels.** Under any `ExpectationSystem` with the pull-out property
  (so every finite event tree), with the flow (9.8) under the rule, predetermined real debt,
  `b_{−1}` equal to the present value of `s₀`, the transversality condition and (9.12): if the
  price level is **bounded above, or bounded away from zero**, then `P_t = P*_t = 1` at every date
  and state (`FiscalRules.fr_unique_bounded`). The proof shows that `Z_t = S_t/P_t`, with
  `S_t = ∑ βʲE_tP_{t+j}`, obeys `E_tZ_{t+1} = (Z_t − 1)/β`, so `Z_t − 1/(1 − β)` is forced to zero
  once `βᵏE_tZ_{t+k} → 0` (`FiscalRules.unique_of_ratio_tvc`); either bound delivers that limit
  through the transversality condition (`FiscalRules.value_bounds`).

The counterexample's prices are unbounded on both sides: the settled levels are unbounded above
(`FiscalRules.Sunspot.settlePrice_unbounded`) and the unsettled path tends to zero
(`FiscalRules.Sunspot.contPrice_tendsto_zero`). So it violates both conditions of (d), and (b)
and (d) are consistent. The corrected statement is the book's, with "among price paths bounded
above, or bounded away from zero" added. Part (d) takes a constant target and `a(β) = 0`; a
stochastic target is not treated.

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections are the confirmed errors of the chapter survey:
* the fiscal-rule uniqueness claim of p. 267 (E9.9), settled as above;
* free exchange of real for nominal debt at `P*`, pp. 279–280, does not drive `E_t(1/P_{t+1})` to
  `1/P*`: the gap follows the hyperbola `C/B` and never closes at finite `B` (E9.8);
* the limit `βᵀE_tV*_{t+T} → 0` of p. 264 needs `0 < α < 2` (E9.1), and Theorem IT's base step
  is `P_1 = P*_1`, with an induction step that needs `V*_t ≠ s_t` under uncertainty (E9.2);
* the real-rate formula (9.26), p. 277, has the wrong sign on `ΔE_tπ_t` and omits `1/κ` on the
  `u_π` terms (E9.4);
* the perpetuity numeraire of p. 296 gives `P_t = (1 + y)r/((1 + r)y)`, the reciprocal of the
  printed formula (E10.1), and the one-period numeraire gives `P_t = 1/β`, not `β` (E10.2);
* the "10%" price-level rises of p. 255 and p. 248, and the "1%" of p. 271, are first-order: the
  exact rises are `(s_t + V)/(s_t + 0.9V)`, `10/9` and `1/110` or `1/90` (E8.1, E8.4);
* matching maturities to surpluses cancels real rates under perfect foresight but not under
  uncertainty (E8.3).

In addition, (8.4) prints `r_{t+j}` where (3.22) has `r_{t+1+j}` (E8.5, found during
formalisation), the `θ_{iπ} = 0` display of p. 270 has `b_t` for `b_{t−1}` (E9.3), the footnote
formula for `r_t` on p. 276 divides by zero at `θ = 1` (E9.5), and the Dupor–Daniel exchange-rate
material is in §24.3, not §24.2 as the survey cites it.

Not formalised:
* the institutional and historical passages: §8.2's interpretation of pegs and the gold standard
  beyond the theorems listed, the corporate-finance and moral-hazard discussion of §§8.3–8.4,
  most of §8.6, §9.1, the verbal parts of §9.6, and §§10.2–10.7 beyond the balance-sheet
  identities in `BalanceSheets` (the ECB, crypto-currencies and "how much money");
* the out-of-equilibrium dynamics of §10.1.2: the conversion right is formalised by the
  arbitrage inequalities and the transversality asymmetry, not as a tâtonnement;
* the remark of §8.4 that longer maturity means more total inflation, which (8.4) alone does not
  determine;
* (3.20)–(3.21) and (9.22) are taken as model equations (the linearisations of Chapter 3),
  not derived from the nonlinear valuation equation;
* the continuous-time converse of the matching claim of §8.4: matching is proved sufficient in
  continuous time, but its necessity only in discrete time, with real rates bounded below by some
  `r̲ > 0` (`MaturityBuffer.matching_necessary`); the continuous version needs uniqueness of
  Laplace-type transforms;
* Theorem FR (d) with a stochastic target `P*` or with initial debt different from the present
  value of `s₀`;
* the sunspot tree of Theorem FR (b) as an `ExpectationSystem`: on its state space a positive
  linear `E_t` defined on all functions must have finite support, so the tree carries explicit
  node-based conditional expectations (`FiscalRules.Sunspot.condE`), with the law of iterated
  expectations, unit total probability and positivity proved
  (`FiscalRules.Sunspot.condE_succ`, `FiscalRules.Sunspot.condE_const`,
  `FiscalRules.Sunspot.condE_nonneg`);
* §9.4.1's claim that the IS shock does not appear in equilibrium output is proved given
  inflation (`SpreadTarget.x_formula`); that `u_x` still enters through unexpected inflation
  (E9.7) is not separately formalised;
* Daniel's (2001a) collapse of a peg with long-term debt, which the survey lists as optional for
  Chapter 7.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](AssetsRulesBalanceSheets/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (shared core, restated from the earlier projects) |
| [Expectations](AssetsRulesBalanceSheets/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; bounded adapted processes; forward series; the pull-out property (shared core) |
| [ExpectationsFiniteTree](AssetsRulesBalanceSheets/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; coin-flip examples (shared core) |
| [ForwardSolution](AssetsRulesBalanceSheets/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [PresentValue](AssetsRulesBalanceSheets/PresentValue.lean) | 13 | (8.1)–(8.2) and §§9.3.1–9.3.2: present values, the transversality condition, flow plus transversality iff present value (expected and pathwise), `B/P = V` and `b = s(P)` determine `P` |
| [RealDebt](AssetsRulesBalanceSheets/RealDebt.lean) | 20 | §§8.1–8.2, (8.1)–(8.2): indexed debt, the timing cases of p. 240, foreign-currency debt and default, reserves, the gold standard |
| [CapitalStructure](AssetsRulesBalanceSheets/CapitalStructure.lean) | 18 | §8.3, (8.3): mixed real and nominal debt, the leverage elasticity, the cashless limit, the pennies example |
| [MaturityBuffer](AssetsRulesBalanceSheets/MaturityBuffer.lean) | 12 | §8.4, (8.4): the weighted-inflation identity from (3.20)–(3.21), short and matched maturity, continuous-time matching and its discrete-time converse, failure under uncertainty |
| [Default](AssetsRulesBalanceSheets/Default.lean) | 18 | §8.5, (8.5)–(8.7): haircuts, expected default, the scaling invariance, a fixed bond price, the 10% example corrected |
| [CentralBankIndependence](AssetsRulesBalanceSheets/CentralBankIndependence.lean) | 5 | §8.6: central-bank purchases, "too much cash", default under independence versus inflation under unification |
| [PotOfAssets](AssetsRulesBalanceSheets/PotOfAssets.lean) | 24 | §§10.1.1–10.1.2, (10.1)–(10.6), and §11.5: real backing, (10.3) from flow plus transversality, purchases at market prices, the conversion right, the transversality asymmetry, real bills |
| [SharesAsMoney](AssetsRulesBalanceSheets/SharesAsMoney.lean) | 22 | §10.1.3, (10.7): potato-farm shares, the perpetuity and one-period numeraires corrected, the equity and no-default bounds |
| [BalanceSheets](AssetsRulesBalanceSheets/BalanceSheets.lean) | 8 | §§10.2–10.4: consolidated and separate balance sheets, Bassetto–Sargent, a walled-off central bank, asset volatility |
| [ExchangeRates](AssetsRulesBalanceSheets/ExchangeRates.lean) | 5 | §24.3: separate surplus pools (Daniel) versus a common pool (Dupor) |
| [InflationTarget](AssetsRulesBalanceSheets/InflationTarget.lean) | 28 | §9.2, (9.1)–(9.6): the target state, Theorem IT with `0 < α < 2`, existence, the two insufficiency claims, the zero-debt sunspot |
| [FiscalRules](AssetsRulesBalanceSheets/FiscalRules.lean) | 62 | §§9.3.1–9.3.3, (9.7)–(9.14): one-period and dynamic fiscal rules, Theorem FR (a)–(d) with the sunspot tree, regular and emergency budgets, the lagged rule |
| [FiscalTaylor](AssetsRulesBalanceSheets/FiscalTaylor.lean) | 13 | §9.3.4, (9.15)–(9.16): the fiscal Taylor rule, the double geometric sum, determinacy iff `θ_{sπ} ≠ 0` |
| [MixedDebtRules](AssetsRulesBalanceSheets/MixedDebtRules.lean) | 12 | §9.3.5: uniqueness with nominal debt, multiplicity needs a falling surplus, the debt-value elasticity, the shock decomposition |
| [SpreadTarget](AssetsRulesBalanceSheets/SpreadTarget.lean) | 30 | §§9.4–9.4.1, (9.17)–(9.26): Taylor rules as spread targets, the simple model, Theorem ST, the `θ = 1` case, (9.26) corrected, Holden's rule |
| [SpreadSwap](AssetsRulesBalanceSheets/SpreadSwap.lean) | 14 | §9.4.2, (9.27): market-price swaps, swaps at `P*`, the hyperbola and the corrected statement |
| [IndexedDebtPeg](AssetsRulesBalanceSheets/IndexedDebtPeg.lean) | 13 | §9.5, (9.28)–(9.29): Theorem IP, log-utility demand, nominal debt crowding out real debt, the five-minute example |
| [CPIStandard](AssetsRulesBalanceSheets/CPIStandard.lean) | 7 | §9.6: commodity standards, perpetuities versus one-year bonds, the indexed-claim peg, the CPI bet |
| [Links](AssetsRulesBalanceSheets/Links.lean) | 17 | Links between Chapters 8, 9 and 10: the same valuation equations, transversality conditions, indexed-debt prices, elasticities and bond prices |

## Modelling conventions

* **Expectations.** Random variables are `Ω → ℝ` under an arbitrary `ExpectationSystem` (linear,
  constant-preserving, monotone, with the law of iterated expectations), and every model equation
  holds state by state. A variable is known at `t` when `E_t x = x`, and a process is adapted when
  it is known at every date (`ExpectationSystem.Adapted`). Results that move known quantities
  through `E_t` assume `ExpectationSystem.PullOut`, which holds for perfect foresight
  (`perfectForesight_pullOut`) and for every finite event tree
  (`ExpectationsFiniteTree.finiteTree_pullOut`). Under pull-out, products, reciprocals and
  quotients of known variables are known (`InflationTarget.known_mul`, `InflationTarget.known_inv`,
  `InflationTarget.known_div`).
* **Dates and debt.** Debt is indexed by the date at which it comes due: `b t` is the book's
  `b_{t−1}` (issued at `t − 1`, paid at `t`), so `b (t + 1)` is chosen at `t` and the indexed flow
  reads `b t = s t + β b (t + 1)`. The same holds for nominal debt `B`, central-bank holdings and
  the debt of the fiscal-rule modules. In `InflationTarget` Lean date `t` is book date `t + 1`, and
  (9.1) is `V 0 = B 0/P* 0`. Debt chosen at `t` is a hypothesis of each theorem that needs it
  ("predetermined").
* **Bond prices.** Nominal bonds are priced risk-neutrally, `Q_t = βE_t(P_t/P_{t+1})`, with an
  expected haircut `D_{t+1}` inside the expectation in §8.5 (`Default.bondPrice`); a one-period
  indexed bond costs `βP_t` (`RealDebt.indexedPrice_eq`).
* **Transversality and present values.** The transversality condition is the explicit limit
  `βᵀE_tx_{t+T} → 0` (`PresentValue.TVC`), a hypothesis wherever the book "iterates forward".
  Present values are `E_t ∑ βʲs_{t+j}` (`PresentValue.pv`) or, in the Chapter 9 modules, sums of
  conditional expectations `∑ βʲE_ts_{t+j}`; they agree for bounded surpluses
  (`PresentValue.pv_eq_forwardSeries`). Pathwise (ex post) versions use the realised sum
  (`PresentValue.epv`). Every infinite sum is a genuine `HasSum` or `tsum` with an explicit
  summability or boundedness hypothesis.
* **Equilibrium and uniqueness.** There is no single equilibrium structure. A price path is
  checked against the flow condition at every date, bond pricing and the transversality condition
  (`InflationTarget.Economy`, `FiscalRules.RuleEquilibrium`, `RealDebt.NominalFlow`,
  `Default.DefaultFlow`, `PotOfAssets.PotFlow`). "The price level is determined" means that two
  positive adapted paths satisfying these conditions coincide; in §9.3.2 it is also asked among
  bounded paths (Theorem FR (d)) and in §9.4.1 given initial inflation (Theorem ST).
* **Witnesses.** Perfect foresight (`perfectForesight`) gives the numerical examples and most
  counterexamples. Uncertainty witnesses use the coin-flip tree of the shared core
  (`ExpectationsFiniteTree.coinSystem`: `InflationTarget.zero_debt_sunspot`,
  `MaturityBuffer.matching_fails_under_uncertainty`, `SpreadTarget.printed_9_26_fails_coin`),
  and the Theorem FR (b) counterexample uses its own infinite tree with explicit conditional
  expectations (`FiscalRules.Sunspot.condE`).
* **Explicit hypotheses.** Hypotheses the book leaves implicit are stated in each theorem: positive
  price levels, positive debts and present values wherever a formula divides by them, `0 ≤ β < 1`,
  bounded surpluses, `0 < α < 2` (§9.2), `V*_t ≠ s_t` under uncertainty (§9.2), `θ ≠ 0` for
  the fiscal rules, `|βθ_{iπ}| < 1` and `|βη| < 1` (§9.3.4), `θ ∈ [0, 1]`, `σκ > 0`, `0 ≤ ρ < 1`
  (§9.4.1), and strictly decreasing marginal utility (§9.5).

## Relation to the Woodford and Galí projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects (the first three from `Woodford/ReturnOfMonetaryRules`,
`ForwardSolution` from the Woodford Chapter 2 and 3 projects), so the project builds on its own.
Nothing is imported from those projects. The chapter modules use only part of the core:
`ExpectationSystem`, `ExpectationSystem.PullOut`, `ExpectationSystem.Adapted`, `BoundedProc`,
`ExpectationSystem.forwardSeries` and `ForwardSolution.E_of_known` throughout, `perfectForesight`
for the deterministic results and witnesses, and the coin-flip tree
(`ExpectationsFiniteTree.coinSystem`, `ExpectationsFiniteTree.coinShock`) for the uncertainty
witnesses. `Determinacy` is carried for the other Cochrane projects.

No Woodford or Galí result is restated in a chapter module. `Links` links the chapters of this
project to one another, not to other projects. Three correspondences are recorded here without a
link theorem:
* `PresentValue.flow_tvc_iff_pv` and `PresentValue.real_flow_tvc_iff` are this project's versions
  of Woodford's equivalence of the intertemporal budget constraint with the flow constraints plus
  transversality (Chapter 2, `PriceLevelDetermination`, `ibc_eq_iff_flow_eq_and_tvc`), proved
  directly;
* the condition `0 < α < 2` of §9.2 (`InflationTarget.tendsto_state_forecast_iff`) is the
  stability condition of Woodford's debt recursion under a tax rule (Chapter 4,
  `NeoWicksellianFramework`, `Fiscal.rec_bounded`), with the surplus responding to the target
  state `V*` instead of to debt;
* Holden's rule (`SpreadTarget.holden_unique`) is the one-dimensional Taylor principle: with
  `|φ| > 1` the only bounded inflation path is the target, as in the Galí Chapter 3 project
  (`BasicNewKeynesianModel`) and `ForwardSolution.existsUnique_bounded`.

Within the Cochrane projects, `MaturityBuffer` takes the linearised identities (3.20)–(3.21) of
Chapter 3 (`Generality`) as model equations, and `Links.valuation_of_short_debt` shows that the
linearised valuation equation (9.22) is their one-period-debt case. The present-value machinery
of `PresentValue` restates, for one-period debt, what `IntertemporalModel` (Chapter 2) and
`LongTermDebtDynamics` (Chapter 7) prove for their settings.

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
