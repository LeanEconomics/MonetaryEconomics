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
are deterministic. Theorem FR is also proved on genuine probability spaces, with Mathlib's
conditional expectation. The library contains **773 theorems**, including the shared core; 557 of
them are in the twenty-five chapter modules (seventeen for the book's sections, plus the shared
`PresentValue`, the cross-chapter `Links` and the six measure-theoretic Theorem FR modules).

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
* **Genuine probability models.** Theorem FR is restated on measure-theoretic expectation systems
  (`FiscalRulesMeasure.RuleEqm`). The settle-or-continue tree of part (b) becomes a genuine
  probability space, the settlement date `ω ∈ ℕ` with infinitely many atoms, on which Mathlib's
  `condExp` agrees at every state with the tree's explicit conditional expectations
  (`FiscalRulesMeasure.SunspotMeasure.sunSystem`, `FiscalRulesMeasure.SunspotMeasure.sun_E_node`,
  `FiscalRulesMeasure.SunspotMeasure.sun_not_finitely_supported`); the sunspot path and
  `P = P*` are both equilibria with the same initial debt
  (`FiscalRulesMeasure.SunspotMeasure.fr_b_measure`). Part (d) extends to stochastic targets and
  any initial debt: if the target's present value is predetermined, every equilibrium with prices
  bounded above is `P_t = (1 + (b₀ − b̄)/(θa₀))P*_t`, and this path is an equilibrium
  (`FiscalRulesTargetMeasure.fr_unique_stochastic`, `FiscalRulesTargetMeasure.exists_proportional`);
  with `b₀ ≠ b̄` no equilibrium has `P = P*`, for any target
  (`FiscalRulesTargetMeasure.initial_debt_of_target`); without that condition the proportional form
  fails (`FiscalRulesTargetMeasure.BoolExample.bool_counterexample`). Uniqueness needs no condition
  on the target: two bounded-above equilibria with the same `s₀`, target and initial debt coincide
  (`FiscalRulesTargetOpen.fr_compare`), so with `b₀ = b̄` the target `P = P*` is the unique
  bounded-above equilibrium even when its present value has news
  (`FiscalRulesTargetOpen.fr_d_news`). Prices bounded only away from zero need the bounded
  cumulative real-rate factor: an explicit counterexample on i.i.d. biased coins, for every
  `β ∈ (0, 1)`, has `b₀ = b̄`, a predetermined target value and `P ≥ m_P > 0`, yet `P ≠ P*`
  (`FiscalRulesBelowCounter.fr_below_counterexample`, `FiscalRulesBelowCounter.fr_d_dividing_line`);
  with that factor, `P = P*` again, news or not (`FiscalRulesTargetClose.fr_d_news_below`). A general
  surplus `s₀` with `a(β) = 0` (a predetermined present value `B`, as every moving average with
  `a(β) = 0` has) replaces `b̄` by `B₀` (`FiscalRulesTargetOpen.fr_unique_s0`,
  `FiscalRulesTargetOpen.MAinf.fr_unique_ma`, `FiscalRulesTargetClose.fr_unique_s0_random_full`).
  With news and `b₀ ≠ b̄`, existence can fail although the realised present value of the target
  plus the debt gap is positive on every path (`FiscalRulesTargetClose.NoExist.oneShot_no_eqm`);
  for news at one date the exact existence condition is proved
  (`FiscalRulesTargetClose.oneShot_eqm_form`, `FiscalRulesTargetClose.oneShot_eqm_exists`,
  `FiscalRulesTargetClose.oneShot_exists_iff_atom`). With news at every date, a bounded-above
  equilibrium exists iff some price path meets (9.12) and its realised discounted deviations from
  the target sum to `d₀` on almost every path, equivalently iff the forward valuation is
  predictable and starts at `d₀` (`FiscalRulesTargetFinal.exists_iff_pathwise`,
  `FiscalRulesTargetFinal.exists_iff_forward`); positivity of `d₀` plus the realised present value
  of the target is necessary, and sufficient when that value is predetermined
  (`FiscalRulesTargetFinal.exists_imp_pos`, `FiscalRulesTargetFinal.predetermined_exists_iff`),
  and the date-0 price level is nondecreasing in initial debt
  (`FiscalRulesTargetFinal.price_monotone`). A comparison identity, a submartingale whose drift
  is `βᵗN_t⁻¹(P'_t − P_t)²/(P_tP'_t) ≥ 0`, shows that two equilibria bounded away from zero, both
  possibly unbounded above, with the same initial debt (`b̄` or not) coincide under the date-0
  deflator bound alone (`FiscalRulesTargetFinal.compare_identity_below`,
  `FiscalRulesTargetFinal.fr_unique_below_pair`, `FiscalRulesTargetFinal.fr_unique_below_rule`).
  If no news arrives after some date `T` the deflator is bounded by `(M*/m)^{2T+1}`, so every
  finite system, and every bridged core finite tree, satisfies the bounded-away-from-zero theorem
  without further hypotheses, and the counterexample needs news at infinitely many dates
  (`FiscalRulesTargetFinal.resolved_hL`, `FiscalRulesTargetFinal.fr_d_resolved`,
  `FiscalRulesTargetFinal.finite_resolved`, `FiscalRulesTargetFinal.iid_not_resolved`,
  `FiscalRulesTargetFinal.tree_fr_d`).

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
  probability zero (`FiscalRules.Sunspot.contProb_tendsto_zero`). *Measure version:* the same
  tree is a genuine probability space on the settlement date, not finitely supported, whose
  `condExp` is the tree's `FiscalRules.Sunspot.condE` at every state; there the sunspot path is an
  equilibrium in the measure sense, with the same initial debt as `P = P*`
  (`FiscalRulesMeasure.SunspotMeasure.sun_E_node`, `FiscalRulesMeasure.SunspotMeasure.fr_b_measure`,
  `FiscalRulesMeasure.SunspotMeasure.fr_b_not_pinned`).
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
  through the transversality condition (`FiscalRules.value_bounds`). *Measure version:* on any
  measure-theoretic system, for an adapted bounded target `P* ≥ m > 0` whose present value `a_t`
  is predetermined (the target analogue of `a(β) = 0`) and any initial debt `b₀`, prices bounded
  above give `P_t = (1 + (b₀ − b̄)/(θa₀))P*_t` a.e., hence `P = P*` when `b₀ = b̄`
  (`FiscalRulesTargetMeasure.fr_unique_stochastic`,
  `FiscalRulesTargetMeasure.fr_unique_stochastic_target`); prices bounded away from zero give the
  same under a bounded cumulative target real-rate factor
  (`FiscalRulesTargetMeasure.fr_unique_stochastic_below`). This covers every deterministic target
  and a genuinely stochastic one (`FiscalRulesTargetMeasure.fr_unique_deterministic`,
  `FiscalRulesTargetMeasure.fr_unique_sShaped`), and on finite systems it gives the core theorem
  (`FiscalRulesTargetMeasure.fr_unique_bounded_link`).

The counterexample's prices are unbounded on both sides: the settled levels are unbounded above
(`FiscalRules.Sunspot.settlePrice_unbounded`) and the unsettled path tends to zero
(`FiscalRules.Sunspot.contPrice_tendsto_zero`), also in the measure version
(`FiscalRulesMeasure.SunspotMeasure.sun_price_unbounded`). So it violates both conditions of (d),
and (b) and (d) are consistent. The corrected statement is the book's, with "among price paths
bounded above, or bounded away from zero" added. With a stochastic target, the predetermined
target value is needed for the proportional form: a coin target whose present value has news, with
`b₀ ≠ b̄`, has the bounded equilibrium `P = P* + 1`
(`FiscalRulesTargetMeasure.BoolExample.bool_counterexample`), which is nevertheless the unique
bounded-above equilibrium for that debt (`FiscalRulesTargetOpen.BoolNews.bool_news_unique`). With
`b₀ = b̄`, bounded-above equilibria are unique for every bounded adapted target, news or not, and
equal `P*` (`FiscalRulesTargetOpen.fr_compare`, `FiscalRulesTargetOpen.fr_d_news`). Prices bounded
away from zero give the same only under the bounded cumulative target real-rate factor
(`FiscalRulesTargetClose.fr_d_news_below`), and that hypothesis cannot be dropped
(`FiscalRulesBelowCounter.fr_below_counterexample`). The factor is needed only from date 0, for
any initial debt (`FiscalRulesTargetFinal.fr_unique_below_pair`), and it holds automatically when
no news arrives after some date (`FiscalRulesTargetFinal.fr_d_resolved`), so the counterexample
needs news at infinitely many dates (`FiscalRulesTargetFinal.iid_not_resolved`).

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
* in Theorem FR (d) with a stochastic target and `b₀ ≠ b̄`: a closed-form existence condition in
  terms of primitives when the target's present value has news at infinitely many dates (the exact
  condition is the implicit one of `FiscalRulesTargetFinal.exists_iff_pathwise` and
  `FiscalRulesTargetFinal.exists_iff_forward`; explicit iffs are proved only for a predetermined
  target value and for one-shot news, and sufficiency of `d₀ ≥ 0` in general is conjectured, not
  proved); strict comparative statics (`d₀ < d₀'` ⇒ `P₀ < P'₀`; the weak version is
  `FiscalRulesTargetFinal.price_monotone`); and a link theorem from
  `FiscalRulesTargetClose.fr_d_news_below` to the hypotheses of the core `ExpectationSystem` (the
  bridged core hypotheses do not give the valuation `HasSum` when prices are unbounded above;
  `FiscalRulesTargetFinal.tree_fr_d` states the result on the bridged measure system of a core
  finite tree, and the constant-target case is `FiscalRulesBelowCounter.fr_below_link`);
* a general surplus process `s₀` with `a(β) = 0` in the core `FiscalRules`, which takes
  `s₀ = (1 − β)b̄` constant; the measure modules allow it (`FiscalRulesTargetOpen.RuleEqmGen`);
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
| [ExpectationsMeasure](AssetsRulesBalanceSheets/ExpectationsMeasure.lean) | 71 | Measure-theoretic expectations (shared core, copied from `ObservationalEquivalence`): `MeasExpectationSystem` with Mathlib's `condExp`, the axioms a.e., news, the forward equation and sunspots, AR(1) conditional variance, bridges to and from the core `ExpectationSystem` |
| [ExpectationsMeasureIID](AssetsRulesBalanceSheets/ExpectationsMeasureIID.lean) | 37 | The genuine i.i.d. economy on `ℕ → ℝ` under `ν^ℕ` (shared core): independence, moments, every history null, determinacy iff `\|a\| < 1`, AR(1), the `±1` coin |
| [FiscalRulesMeasure](AssetsRulesBalanceSheets/FiscalRulesMeasure.lean) | 39 | §9.3.2, (9.8)–(9.12): the rule equilibrium on a measure system; Theorem FR (b) on the genuine settlement-date probability space, its `condExp` equal to the tree's conditional expectations, unbounded prices |
| [FiscalRulesTargetMeasure](AssetsRulesBalanceSheets/FiscalRulesTargetMeasure.lean) | 35 | §9.3.2: Theorem FR (d) with a stochastic target and any initial debt, existence, deterministic and s-shaped targets, the coin counterexample, the link to the core theorem |
| [FiscalRulesTargetOpen](AssetsRulesBalanceSheets/FiscalRulesTargetOpen.lean) | 32 | §9.3.2: Theorem FR (d) with a general surplus `s₀`; the comparison theorem; uniqueness with a news-bearing target; finite and infinite moving averages with `a(β) = 0`; the link to the core theorem |
| [FiscalRulesBelowCounter](AssetsRulesBalanceSheets/FiscalRulesBelowCounter.lean) | 48 | §9.3.2: the counterexample on i.i.d. biased coins showing the bounded real-rate factor is needed when prices are only bounded away from zero; the dividing line; the link for a constant target |
| [FiscalRulesTargetClose](AssetsRulesBalanceSheets/FiscalRulesTargetClose.lean) | 24 | §9.3.2: the bounded-away-from-zero case with news, random date-0 data without a band, existence with one-shot news and a nonexistence example |
| [FiscalRulesTargetFinal](AssetsRulesBalanceSheets/FiscalRulesTargetFinal.lean) | 38 | §9.3.2: the comparison identity; uniqueness for two equilibria bounded away from zero and unbounded above, any initial debt; the exact existence condition with news at every date; comparative statics in initial debt; finite-horizon information bounds the deflator; the link to core finite trees |

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
* **Measure-theoretic expectations.** The core `ExpectationSystem` is kept unchanged, and every
  result above stated for it still holds; on a countable `Ω` it forces finitely supported
  forecasts, which is why the sunspot tree of Theorem FR (b) carries its own conditional
  expectations. `ExpectationsMeasure` adds, alongside it, a probability space with a filtration
  (`ExpectationsMeasure.MeasExpectationSystem`): `E_t` is Mathlib's `condExp`, processes are
  adapted in Mathlib's sense (`StronglyAdapted`), and equations hold almost everywhere. The bridge
  is additive and runs both ways: a finite event tree is a measure system with the same `E_t`
  (`ExpectationsMeasure.TreeBridge.treeSystem_E`), and a measure system on a finite discrete state
  space with full support is a core system with the pull-out property
  (`ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem`,
  `ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_pullOut`). The genuine instances
  are the i.i.d. economy on `ℕ → ℝ`, in which every history has probability zero
  (`ExpectationsMeasureIID.iidSystem`, `ExpectationsMeasureIID.iid_not_finitely_supported`), and
  the settlement-date space of Theorem FR (b) (`FiscalRulesMeasure.SunspotMeasure.sunSystem`). In
  the measure modules the rule equilibrium is `FiscalRulesMeasure.RuleEqm`, with (9.9) and the
  transversality condition a.e. and (9.8) on every path.
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
  expectations (`FiscalRules.Sunspot.condE`), realised as a genuine probability space in
  `FiscalRulesMeasure.SunspotMeasure.sunSystem`. The stochastic-target counterexample is a coin
  revealed at date 1 (`FiscalRulesTargetMeasure.BoolExample.boolSystem`). The news-bearing and
  general-`s₀` results use `FiscalRulesTargetOpen.RuleEqmGen`, the rule equilibrium with a general
  underlying surplus; their counterexamples live on i.i.d. biased coins
  (`FiscalRulesBelowCounter.Sys`), on a one-shot news system (`FiscalRulesTargetClose.oneShot`) and
  on `ℕ` with geometric weights (`FiscalRulesTargetClose.NoExist.wProb`). The exact existence
  condition builds candidate equilibria from the debt generated forward, path by path
  (`FiscalRulesTargetFinal.fwdDebt`).
* **Explicit hypotheses.** Hypotheses the book leaves implicit are stated in each theorem: positive
  price levels, positive debts and present values wherever a formula divides by them, `0 ≤ β < 1`,
  bounded surpluses, `0 < α < 2` (§9.2), `V*_t ≠ s_t` under uncertainty (§9.2), `θ ≠ 0` for
  the fiscal rules, a bounded cumulative target real-rate factor for prices bounded away from zero
  with a stochastic target (§9.3.2; from date 0 only, and automatic when news stops at a finite
  date, `FiscalRulesTargetFinal.EventuallyResolved`), `|βθ_{iπ}| < 1` and `|βη| < 1` (§9.3.4), `θ ∈ [0, 1]`, `σκ > 0`, `0 ≤ ρ < 1`
  (§9.4.1), and strictly decreasing marginal utility (§9.5).

## Relation to the Woodford and Galí projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects (the first three from `Woodford/ReturnOfMonetaryRules`,
`ForwardSolution` from the Woodford Chapter 2 and 3 projects), so the project builds on its own.
The measure-theoretic core (`ExpectationsMeasure`, `ExpectationsMeasureIID`) is copied from
`Cochrane/ObservationalEquivalence` with the namespace renamed.
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
