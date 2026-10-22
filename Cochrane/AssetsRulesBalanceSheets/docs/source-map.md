# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Part II: Chapter 8, "Assets and choices"
(pp. 238–258), Chapter 9, "Better rules" (pp. 259–286), and Chapter 10, "Balance sheets and pots
of assets" (pp. 287–311), with the real-bills claim of §11.5 (p. 322) and the exchange-rate claims
of §24.3 (p. 527). Each formal claim is listed with its Lean name, relative to the namespace
`Cochrane.AssetsRulesBalanceSheets`. Page numbers are book pages. The book has no labelled
propositions, so rows are keyed by equation number, section or page. Rows follow the book section
by section, and each heading names the modules that formalise the section: Chapters 8, 9 and 10,
then §11.5 and §24.3, then the links between the chapters and the shared tools. "Theorem IT",
"Theorem FR", "Theorem ST" and "Theorem IP" are the labels of the chapter survey; "E8.x", "E9.x"
and "E10.x" are its error codes (see [corrections](corrections.md)).

Debt is indexed by the date at which it comes due: `b t` is the book's `b_{t−1}`, and `b (t + 1)`
is chosen at `t`; in `InflationTarget` Lean date `t` is book date `t + 1`. Structural results hold
for an arbitrary `ExpectationSystem`, with `ExpectationSystem.PullOut` where known quantities move
through `E_t`; the transversality condition is the explicit limit `PresentValue.TVC`. The shared
core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is cited where a
row uses it. Theorem FR is also proved on measure-theoretic expectation systems
(`ExpectationsMeasure.MeasExpectationSystem`, with Mathlib's `condExp` and equations a.e.) in
`FiscalRulesMeasure`, `FiscalRulesTargetMeasure`, `FiscalRulesTargetOpen`,
`FiscalRulesBelowCounter`, `FiscalRulesTargetClose` and `FiscalRulesTargetFinal`, listed after the §9.3.1–§9.3.2 section;
the copied measure core is listed before the shared tools.

## §8.1 Indexed debt and the shared valuation machinery, (8.1), pp. 239–240 (PresentValue, RealDebt)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (8.1)–(8.2), pp. 239–240 | the ex post and the expected present value; for bounded surpluses and `0 ≤ β < 1` the expectation commutes with the sum, and the present value is bounded | `PresentValue.epv`, `PresentValue.pv`, `PresentValue.pv_eq_forwardSeries`, `PresentValue.pv_bounded` |
| Cochrane p. 239 (E8.2) | the transversality condition `βᵀE_tx_{t+T} → 0`, stated explicitly; a bounded value process satisfies it | `PresentValue.TVC`, `PresentValue.tvc_of_bounded` |
| Cochrane (8.1), p. 239; §9.2, p. 264 | "iterating forward": the flow `x_t = s_t + βE_tx_{t+1}` and the transversality condition at `(t, ω)` give partial sums converging to `x_t`, with no bound on `s`; the solution is the forward sum; for bounded surpluses, flow plus transversality iff `x_t = E_t ∑ βʲs_{t+j}` | `PresentValue.tendsto_partialSums_of_tvc`, `PresentValue.eq_forwardSeries_of_tvc`, `PresentValue.flow_tvc_iff_pv` |
| Cochrane p. 291; §9.2, p. 264 | "to avoid an explosion … both sides must be zero": `X_t = βE_tX_{t+1}` plus transversality forces `X = 0` | `PresentValue.eq_zero_of_tvc` |
| Cochrane (8.1), p. 239; (9.8), p. 266 | pathwise: `b_t = ∑_{j<T} βʲs_{t+j} + βᵀb_{t+T}`; the real flow plus `βᵀb_{t+T−1} → 0` iff the partial sums converge to `b_{t−1}`, with no summability and no sign of `β` (E8.2); a genuine sum when summable, as for bounded surpluses | `PresentValue.real_iterate`, `PresentValue.real_flow_tvc_iff`, `PresentValue.hasSum_of_tvc`, `PresentValue.summable_of_bounded` |
| Cochrane p. 289; p. 295 | `B/P = V` with `B, V > 0` has exactly one positive solution `P = B/V` | `PresentValue.valuation_price_unique` |
| Cochrane §9.3.1, p. 265; §10.1.1, p. 289 | `b = s(P)` with `s` strictly increasing on positive prices has at most one positive solution | `PresentValue.price_unique_of_strictMonoOn` |
| Cochrane p. 239 | the nominal price of a one-period indexed bond is `βP_t`; the real value at `t − 1` of `b_{t−1}` is `βb_{t−1}` | `RealDebt.indexedPrice`, `RealDebt.indexedPrice_eq`, `RealDebt.indexed_real_value` |
| Cochrane p. 239 | the indexed-debt flow is the real flow `b_{t−1} = s_t + βb_t`, state by state | `RealDebt.IndexedFlow`, `RealDebt.indexedFlow_iff` |
| Cochrane p. 239 | with only real debt and surpluses independent of `P`, the price level drops out: the flow holds for one price path iff for any other; the cash version of the flow holds iff the real flow does | `RealDebt.indexedFlow_price_free`, `RealDebt.cashFlow_iff` |
| Cochrane (8.1), p. 239 (E8.2) | flow plus pathwise transversality iff `b_{t−1} = ∑ βʲs_{t+j}` in every state, as a convergent series, and as a `tsum` when summable | `RealDebt.indexed_valuation_iff`, `RealDebt.indexed_valuation_tsum` |
| Cochrane p. 239 | "a restriction on surpluses" (`a(ρ) = 0`): the present value of surpluses from `t + 1` on has no news at `t + 1` | `RealDebt.indexed_pv_news_zero` |
| Cochrane p. 239 | surpluses `s_t = σ(P_t)` with `σ` injective determine the price level even with only real debt | `RealDebt.surplus_rule_determines` |
| Cochrane p. 240 | real debt outstanding and nominal debt issued: the flow does not involve `P_t`, which is undetermined | `RealDebt.nominalIssue_flow_iff`, `RealDebt.realOutstanding_price_free` |
| Cochrane p. 240 | nominal debt outstanding and real debt issued: `P_t = B_{t−1}/(s_t + βb_t)`, unique | `RealDebt.nominalOutstanding_price_unique` |

## §8.2 Foreign debt, reserves and the gold standard, (8.2), pp. 240–245 (RealDebt)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (8.2), p. 240 | the nominal flow `B_{t−1} = P_ts_t + Q_tB_t` is the real recursion `B_{t−1}/P_t = s_t + βE_t(B_t/P_{t+1})`; with the transversality condition it is the valuation `B_{t−1}/P_t = E_t ∑ βʲs_{t+j}`, a constraint on surpluses when `P*` is given from abroad | `RealDebt.NominalFlow`, `RealDebt.nominalFlow_iff_solves`, `RealDebt.nominal_valuation_iff` |
| Cochrane p. 240; §8.6, p. 257 | with the price level fixed at `P̄`, `BD/P̄ = V` forces the haircut `D = P̄V/B`; Greece in the euro: a shortfall needs an explicit haircut `D < 1` | `RealDebt.haircut_of_fixed_price`, `RealDebt.foreign_default_required` |
| Cochrane p. 242 | with reserves `G`, `B/P = G + V` gives `P = B/(G + V)`; reserves enter in parallel with the present value of surpluses | `RealDebt.reserves_price_unique`, `RealDebt.reserves_through_sum` |
| Cochrane pp. 242–243 | the gold standard is passive in the relative price `q`: a deflation raises the present value needed; the devaluation from $20 to $32 an ounce raises `P` by `8/5` and cuts the required present value by `5/8` | `RealDebt.gold_deflation_raises_pv`, `RealDebt.gold_devaluation` |

## §8.3 The corporate finance of government debt, (8.3), pp. 245–249 (CapitalStructure)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (8.3), p. 246 | the flow with real and nominal debt is the real recursion for `b_{t−1} + B_{t−1}/P_t`; with the transversality condition it is (8.3) | `CapitalStructure.MixedFlow`, `CapitalStructure.mixedFlow_iff_solves`, `CapitalStructure.mixed_valuation_iff` |
| Cochrane (8.3), p. 246 | "determined by the ability to devalue the nominal debt only": `P = B/(V − b)` when `V > b`; no price level when `V ≤ b` (default); with no nominal debt `P` is free if `V = b` and impossible otherwise | `CapitalStructure.mixed_price_unique`, `CapitalStructure.mixed_no_price`, `CapitalStructure.mixed_zero_nominal` |
| Cochrane §8.3, p. 246 | leverage: `d log P/dV = −1/(V − b)`, the exact elasticity `−V/(V − b)`, above one in size iff `b > 0` and strictly increasing in `b`; `P(V′)/P(V) = (V − b)/(V′ − b)`; the log price spread rises with `b` | `CapitalStructure.log_price_hasDerivAt`, `CapitalStructure.log_price_elasticity`, `CapitalStructure.elasticity_gt_one_iff`, `CapitalStructure.elasticity_strictMono`, `CapitalStructure.price_ratio`, `CapitalStructure.log_price_spread_strictMono` |
| Cochrane §8.3, p. 246 | more real debt "raises the chance of explicit default" | `CapitalStructure.default_prob_mono` |
| Cochrane §8.3, p. 248 | the cashless limit: determinate with the same `P` all along the sequence, nominal debt vanishing and the elasticity exploding; at the limit every `P` solves (8.3) | `CapitalStructure.cashless_sequence_determinate`, `CapitalStructure.cashless_sequence_price`, `CapitalStructure.cashless_nominal_vanishes`, `CapitalStructure.cashless_elasticity_explodes`, `CapitalStructure.cashless_limit_indeterminate` |
| Cochrane §8.3, p. 248 | $10 of pennies: the price level rises by exactly `10/9`, not 10% (E8.4) | `CapitalStructure.pennies_inflation` |

## §8.4 Long versus short debt, (8.4), pp. 249–254 (MaturityBuffer)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (3.20)–(3.21), p. 65, as used on p. 250 | the linearised identities, taken as model equations | `MaturityBuffer.Identity320`, `MaturityBuffer.Identity321` |
| Cochrane (8.4), p. 250 | `∑ ωʲΔEπ_{t+1+j} = −∑ ρʲΔEs_{t+1+j} + ∑_{j≥1}(ρʲ − ωʲ)ΔEr_{t+1+j}`, derived from (3.20)–(3.21), with the index `r_{t+1+j}` corrected (E8.5) | `MaturityBuffer.identity_84` |
| Cochrane §8.4, p. 250 | `ω = 0`: the whole revision of the present value is met by immediate inflation, exactly so with no real-rate news; `ω = ρ`: real-rate news drops out; the weights `ρʲ − ωʲ` shrink as `ω` rises | `MaturityBuffer.short_debt_identity`, `MaturityBuffer.short_debt_constant_rates`, `MaturityBuffer.matched_maturity_identity`, `MaturityBuffer.rate_weights_antitone` |
| Cochrane §8.4, p. 250 | continuous time, perfect foresight: if maturing debt matches surpluses, the present-value relation holds for every real-rate path, and the price level is insulated from real rates | `MaturityBuffer.cdisc`, `MaturityBuffer.matching_cancels`, `MaturityBuffer.price_insulated` |
| Cochrane §8.4, pp. 250–251 | the converse in discrete time: a price level independent of every real-rate path with rates at least `r̲ > 0` forces exact matching | `MaturityBuffer.ddisc`, `MaturityBuffer.ddisc_const`, `MaturityBuffer.ddisc_bump`, `MaturityBuffer.matching_necessary`, `MaturityBuffer.price_insulated_only_if_matching` |
| Cochrane §8.4, p. 250 (E8.3) | under uncertainty, matching `B^{(t+τ)}E_t(1/P_{t+τ}) = s_{t+τ}` does not cancel the rates: `E₀[D/P_τ] = 1 ≠ 3/4 = E₀[Ds_τ]` in the coin-flip tree | `MaturityBuffer.matching_fails_under_uncertainty` |

## §8.5 Default, (8.5)–(8.7), pp. 254–255 (Default)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (8.5), p. 254 | with a haircut `D_t` the price level is `P_t = BD/V`; an unexpected haircut `D = V′/V` absorbs a fall in the present value with no inflation | `Default.haircut_price_unique`, `Default.haircut_offsets_shock` |
| Cochrane (8.6)–(8.7), p. 254 | the bond price `Q_t = βE_t(P_tD_{t+1}/P_{t+1})` and the flow with haircuts; revenue `Q_tB_t/P_t = βE_t(B_tD_{t+1}/P_{t+1})`; the flow is the real recursion for `B_{t−1}D_t/P_t`; flow plus transversality iff (8.5) at every date | `Default.bondPrice`, `Default.DefaultFlow`, `Default.revenue_eq`, `Default.defaultFlow_iff_solves`, `Default.default_valuation_iff` |
| Cochrane (8.6), p. 254 | in present-value form, revenue is the present value from `t + 1`, whatever the expected haircut; an expected default with unchanged surpluses has no effect on `P_t`; a known haircut lowers the bond price proportionally | `Default.default_flow_pv`, `Default.expected_default_no_effect`, `Default.bondPrice_known_haircut` |
| Cochrane §8.5, p. 255 | "selling 2 bonds at a 50% haircut is exactly the same as selling 1 bond at none": the flow is invariant under `(B_t, D_t) ↦ (kB_t, D_t/k)` | `Default.bondPrice_scale`, `Default.scaled_flow_iff`, `Default.two_bonds_half_haircut` |
| Cochrane §8.5, p. 255 | with `Q_t` fixed, `P_{t+1} = βP_tD_{t+1}/Q_t`, the same as selling `D_{t+1}B_t` bonds with no haircut; an expected haircut lowers `P_{t+1}` | `Default.fixedQ_perfectForesight`, `Default.fixedQ_next_price_mono` |
| Cochrane §8.5, p. 255 (E8.1) | a 10% haircut with 10% lower surpluses raises `P_t` by `(s_t + V)/(s_t + 0.9V)`: `10/9` iff `s_t = 0`, below `10/9` if `s_t > 0`; `1/P` falls by exactly 10% iff `s_t = 0` | `Default.haircut_ten_percent`, `Default.haircut_factor_eq_iff`, `Default.haircut_factor_lt`, `Default.money_value_ten_percent_iff` |
| Cochrane §8.5, p. 255 | if the interest rate follows the default premium, `P_{t+1}` rises by the same factor as `P_t` | `Default.rate_follows_premium` |

## §8.6 Central bank independence, pp. 256–258 (CentralBankIndependence, RealDebt)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §8.6, p. 256 | a central-bank purchase of treasury debt paid with reserves leaves the consolidated valuation unchanged | `CentralBankIndependence.cb_purchase_neutral` |
| Cochrane §8.6, p. 257 | "inflation in the end comes from too much cash": cash is left over iff `P < B/(s + q)`, and none iff the flow holds | `CentralBankIndependence.cashLeft`, `CentralBankIndependence.cash_left_pos_iff`, `CentralBankIndependence.cash_left_zero_iff` |
| Cochrane §8.6, p. 257 | the same shortfall `V < B/P̄` gives explicit default under an independent central bank and inflation `P > P̄` under a unified one | `RealDebt.haircut_of_fixed_price`, `CentralBankIndependence.unified_inflates`, `CentralBankIndependence.independence_default_vs_inflation` |

## §9.2 A simple model of an inflation target, (9.1)–(9.6), pp. 263–264 (InflationTarget)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (9.1)–(9.5), pp. 263–264 | the target state (9.1)–(9.2), the surplus rule (9.4), the rate target (9.5), and the private-sector equilibrium with flow, bond pricing and transversality | `InflationTarget.StateInit`, `InflationTarget.StateRec`, `InflationTarget.SurplusRule`, `InflationTarget.RateTarget`, `InflationTarget.Economy` |
| Cochrane (9.3), (9.6), p. 264 | the flow rearranged; `V*` is adapted; `βE_tV*_{t+1} = V*_t − s_t`, and with (9.4) `= (1 − α)V*_t − s_{0,t}`; the forecasts obey `x_{T+1} = (1 − α)x_T − βᵀE_ts_{0,t+T}` | `InflationTarget.eq_9_3`, `InflationTarget.state_adapted`, `InflationTarget.eq_9_6`, `InflationTarget.eq_9_6_rule`, `InflationTarget.state_forecast_succ` |
| Cochrane §9.2, p. 264 | contraction lemmas behind the limit | `InflationTarget.abs_le_of_contraction`, `InflationTarget.tendsto_zero_of_contraction`, `InflationTarget.summable_of_contraction` |
| Cochrane §9.2, p. 264 (E9.1) | `βᵀE_tV*_{t+T} → 0` for bounded `s₀` when `0 < α < 2`; with `s₀ = 0` the forecasts are `(1 − α)ᵀV*_t`, so the limit is zero iff `0 < α < 2`; at `α = 0` it is `V*_t − ∑ βʲE_ts_{0,t+j}` | `InflationTarget.tendsto_state_forecast`, `InflationTarget.state_forecast_of_s0_zero`, `InflationTarget.tendsto_state_forecast_iff`, `InflationTarget.tendsto_state_forecast_alpha_zero` |
| Cochrane §9.2, p. 264 | under pull-out, products, reciprocals and quotients of known variables are known | `InflationTarget.known_mul`, `InflationTarget.known_inv`, `InflationTarget.known_div` |
| Cochrane §9.2, p. 264 | `V*_t = E_t ∑ βʲs_{t+j}`; real debt obeys `b_t = s_t + βE_tb_{t+1}`; `B_t/P_t = V*_t` at every date and state, the present value of surpluses | `InflationTarget.hasSum_state`, `InflationTarget.realDebt_rec`, `InflationTarget.realDebt_eq_state`, `InflationTarget.realDebt_hasSum` |
| Cochrane §9.2, p. 264 (Theorem IT; E9.1, E9.2) | with `0 < α < 2`, bounded `s₀`, nonzero initial debt and `V*_t ≠ s_t`, the unique equilibrium price level is `P = P*` (base step `P_1 = P*_1`); `P = P*` is an equilibrium | `InflationTarget.price_eq_target`, `InflationTarget.exists_equilibrium` |
| Cochrane §9.2, p. 264 | under perfect foresight `V*_t ≠ s_t` is not needed; under uncertainty it is: a coin-flip sunspot with fully repaid debt | `InflationTarget.price_eq_target_perfectForesight`, `InflationTarget.coinPrice`, `InflationTarget.coin_first_known`, `InflationTarget.coinPrice_known`, `InflationTarget.coinPrice_E0_inv`, `InflationTarget.zero_debt_sunspot` |
| Cochrane §9.2, p. 264 | "the interest-rate target alone is insufficient"; "the surplus rule is also insufficient": doubling the debt doubles the future price level | `InflationTarget.witnessState`, `InflationTarget.target_alone_insufficient`, `InflationTarget.ruleState`, `InflationTarget.rule_alone_insufficient` |

## §9.3.1–§9.3.2 Fiscal rules with indexed debt, (9.7)–(9.12), pp. 265–267 (FiscalRules)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §9.3.1, p. 265 | `b_{T−1} = s(P_T)` with `s` strictly increasing determines `P_T` "although the debt is fully indexed" | `PresentValue.price_unique_of_strictMonoOn`, `FiscalRules.existsUnique_price` |
| Cochrane (9.7), p. 265 | under `s_T(P_T) = b_{T−1} + θ(P_T − P*_T)`, `θ ≠ 0`, the valuation holds iff `P_T = P*_T` | `FiscalRules.eq_9_7_iff` |
| Cochrane (9.8)–(9.9), p. 266 | (9.8) iterated forward with the transversality condition gives (9.9) ex post; the ex post equilibrium of the dynamic rule; discounted-sum lemmas | `PresentValue.real_iterate`, `PresentValue.hasSum_of_tvc`, `FiscalRules.eq_9_9`, `FiscalRules.RuleEquilibrium`, `FiscalRules.tsum_shift`, `FiscalRules.abs_tsum_le` |
| Cochrane §9.3.2, p. 266 | (9.9) and the rule determine `∑ βʲP_{t+j}` "but not the shape of that path": adding any bounded `z` with `∑ βʲzⱼ = 0` gives another equilibrium; an explicit example | `FiscalRules.hyperplane_equilibrium`, `FiscalRules.hyperplaneShift`, `FiscalRules.hasSum_hyperplaneShift`, `FiscalRules.not_determined_by_valuation` |
| Cochrane §9.3.2, p. 266 | with `a(β) = 0` only the weighted sum of price deviations has no innovation | `FiscalRules.no_innovation_weighted_sum` |
| Cochrane (9.10)–(9.11), p. 267 | the debt rule and `M_t = 0` force `P = P*`; `P < P*` means money is printed, `P > P*` that it is soaked up | `FiscalRules.price_eq_target_of_debtRule`, `FiscalRules.money_pos_of_below`, `FiscalRules.money_neg_of_above` |
| Cochrane (9.12), p. 267 (Theorem FR (a)) | under perfect foresight only `P = P*` satisfies (9.9) and (9.12), and it is an equilibrium | `FiscalRules.fr_perfectForesight`, `FiscalRules.fr_exists` |
| Cochrane p. 267 (Theorem FR (b), E9.9) | false under uncertainty: the settle-or-continue tree is an equilibrium for every `0 < β < 1`, `0 < P_0 < 1 = P*_0`, `θ` and `b̄`, with genuine probabilities, (9.12) at every node, (9.8) on every edge with predetermined debt, (9.9) at every node and ex post, and transversality | `FiscalRules.Sunspot.sunspot_counterexample` |
| Cochrane p. 267 (E9.9, construction) | the coefficients, prices, values, probabilities, explicit conditional expectations, nodes, debt and surplus of the tree | `FiscalRules.Sunspot.coefL`, `FiscalRules.Sunspot.coefK`, `FiscalRules.Sunspot.contPrice`, `FiscalRules.Sunspot.value`, `FiscalRules.Sunspot.settlePrice`, `FiscalRules.Sunspot.settleProb`, `FiscalRules.Sunspot.contProb`, `FiscalRules.Sunspot.condE`, `FiscalRules.Sunspot.price`, `FiscalRules.Sunspot.nodeValue`, `FiscalRules.Sunspot.debt`, `FiscalRules.Sunspot.surplus`, `FiscalRules.Sunspot.pathNode` |
| Cochrane p. 267 (E9.9, bounds) | `S_n = P_n + βS_{n+1}`, `S_0 = 1/(1 − β)`; positivity and bounds of the coefficients and values; the settle price exceeds the continue price; settle probabilities in `(1 − β, 1)`; `1/P` is a martingale; continuation probabilities | `FiscalRules.Sunspot.value_rec`, `FiscalRules.Sunspot.value_zero`, `FiscalRules.Sunspot.coefK_pos`, `FiscalRules.Sunspot.coefL_pos`, `FiscalRules.Sunspot.value_pos`, `FiscalRules.Sunspot.value_le`, `FiscalRules.Sunspot.contPrice_lt_settlePrice`, `FiscalRules.Sunspot.settleProb_bounds`, `FiscalRules.Sunspot.martingale_inv`, `FiscalRules.Sunspot.contProb_succ'`, `FiscalRules.Sunspot.contProb_bounds` |
| Cochrane p. 267 (E9.9, expectations) | the law of iterated expectations on the tree; conditional expectations are affine, sum to one and are positive | `FiscalRules.Sunspot.condE_succ`, `FiscalRules.Sunspot.condE_affine`, `FiscalRules.Sunspot.condE_const`, `FiscalRules.Sunspot.condE_nonneg` |
| Cochrane p. 267 (E9.9, series) | the finite-horizon identity, the remainder tends to zero, and `∑ βʲE_nP_{n+j} = S_n` as a genuine series | `FiscalRules.Sunspot.geom_identity`, `FiscalRules.Sunspot.value_finite`, `FiscalRules.Sunspot.remainder_tendsto`, `FiscalRules.Sunspot.hasSum_value` |
| Cochrane (9.8), (9.9), (9.12), pp. 266–267 (E9.9, equilibrium conditions) | (9.9) at continue and settled nodes and ex post along every settling path; (9.8) on every edge; (9.12) at every node; transversality at every node | `FiscalRules.Sunspot.valuation_cont`, `FiscalRules.Sunspot.valuation_settled`, `FiscalRules.Sunspot.valuation_expost`, `FiscalRules.Sunspot.flow_cont`, `FiscalRules.Sunspot.flow_settled`, `FiscalRules.Sunspot.rate_target_cont`, `FiscalRules.Sunspot.rate_target_settled`, `FiscalRules.Sunspot.tvc_cont`, `FiscalRules.Sunspot.tvc_settled` |
| Cochrane p. 267 (E9.9) | the settled prices are unbounded above, the unsettled path tends to zero, and it has probability zero | `FiscalRules.Sunspot.settlePrice_unbounded`, `FiscalRules.Sunspot.contPrice_tendsto_zero`, `FiscalRules.Sunspot.contProb_tendsto_zero` |
| Cochrane (9.12), p. 267 (Theorem FR (c)) | `P*_t/P_t` is a martingale; Jensen's inequality; only `P_0 ≤ P*_0` survives under uncertainty | `FiscalRules.inv_ge_tangent`, `FiscalRules.jensen_inv`, `FiscalRules.fr_martingale`, `FiscalRules.fr_jensen` |
| Cochrane pp. 266–267 (Theorem FR (d), E9.9 settled) | with `P* ≡ 1`, pull-out, predetermined debt, `a(β) = 0` and transversality, a price level bounded above or bounded away from zero must be `P ≡ P*`; the core step via `Z_t = S_t/P_t`; the value bounds | `FiscalRules.fr_unique_bounded`, `FiscalRules.unique_of_ratio_tvc`, `FiscalRules.value_bounds` |

## §9.3.2 Theorem FR (b) on a genuine probability space, (9.8)–(9.12), pp. 266–267 (FiscalRulesMeasure)

Statements hold almost everywhere on a measure-theoretic expectation system; on the settlement-date
space every state has positive probability, so they hold at every state.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (9.8), (9.9), (9.12), pp. 266–267 | the rule equilibrium on a measure system: positive adapted integrable prices, (9.12) a.e., (9.8) under the rule on every path, predetermined real debt, (9.9) as a genuine `HasSum` a.e. and transversality a.e.; `P = P* ≡ 1` with `b ≡ b̄` is an equilibrium on every system | `FiscalRulesMeasure.RuleEqm`, `FiscalRulesMeasure.target_ruleEqm` |
| Cochrane p. 267 (E9.9, probabilities) | continuation probabilities multiply and are positive; the settlement-date probabilities `π_k = contProb 0 k · p_k` are positive, telescope and sum to one | `FiscalRulesMeasure.SunspotMeasure.contProb_succ`, `FiscalRulesMeasure.SunspotMeasure.contProb_add`, `FiscalRulesMeasure.SunspotMeasure.contProb_pos`, `FiscalRulesMeasure.SunspotMeasure.weight`, `FiscalRulesMeasure.SunspotMeasure.weight_eq`, `FiscalRulesMeasure.SunspotMeasure.weight_pos`, `FiscalRulesMeasure.SunspotMeasure.sum_weight`, `FiscalRulesMeasure.SunspotMeasure.hasSum_weight` |
| Cochrane p. 267 (E9.9, the space) | the law `∑ π_kδ_k` of the settlement date on `Ω = ℕ`, a probability measure; singletons and unsettled sets `{ω ≥ n}` | `FiscalRulesMeasure.SunspotMeasure.sunMeasure`, `FiscalRulesMeasure.SunspotMeasure.sunMeasure_apply`, `FiscalRulesMeasure.SunspotMeasure.sunMeasure_singleton`, `FiscalRulesMeasure.SunspotMeasure.sunMeasure_univ`, `FiscalRulesMeasure.SunspotMeasure.sunProb`, `FiscalRulesMeasure.SunspotMeasure.measureReal_singleton`, `FiscalRulesMeasure.SunspotMeasure.measureReal_Ici` |
| Cochrane p. 267 (E9.9, information) | the node visited at each date, information is never forgotten, and the tree filtration `𝓕_t = σ(node_t)`; node variables are known at their date | `FiscalRulesMeasure.SunspotMeasure.node`, `FiscalRulesMeasure.SunspotMeasure.node_of_le`, `FiscalRulesMeasure.SunspotMeasure.node_of_lt`, `FiscalRulesMeasure.SunspotMeasure.nodeBack`, `FiscalRulesMeasure.SunspotMeasure.nodeBack_node`, `FiscalRulesMeasure.SunspotMeasure.sunFiltration`, `FiscalRulesMeasure.SunspotMeasure.stronglyMeasurable_node` |
| Cochrane p. 267 (Theorem FR (b), E9.9) | the sunspot tree as a genuine measure-theoretic expectation system with full support and infinitely many atoms: no finite set of states has probability one | `FiscalRulesMeasure.SunspotMeasure.sunSystem`, `FiscalRulesMeasure.SunspotMeasure.sunSystem_μ`, `FiscalRulesMeasure.SunspotMeasure.sunSystem_fullSupport`, `FiscalRulesMeasure.SunspotMeasure.sun_not_finitely_supported` |
| Cochrane p. 267 (E9.9, conditional expectations) | Mathlib's `condExp` at every state is the value on a settled state and the cell average on the unsettled cell; integrability of node variables and of variables eventually constant on the unsettled states | `FiscalRulesMeasure.SunspotMeasure.cellAvg`, `FiscalRulesMeasure.SunspotMeasure.sun_E`, `FiscalRulesMeasure.SunspotMeasure.integrable_of_eventually_const`, `FiscalRulesMeasure.SunspotMeasure.integrable_node`, `FiscalRulesMeasure.SunspotMeasure.setIntegral_Ici_node`, `FiscalRulesMeasure.SunspotMeasure.cellAvg_node` |
| Cochrane p. 267 (E9.9, link) | `condExp` equals the node-based `FiscalRules.Sunspot.condE` at every state; `FiscalRules.Sunspot.condE` depends only on reachable nodes | `FiscalRulesMeasure.SunspotMeasure.sun_E_node`, `FiscalRulesMeasure.SunspotMeasure.condE_congr` |
| Cochrane (9.8), (9.9), (9.12), pp. 266–267 (E9.9, equilibrium conditions) | the price and debt processes; positive prices; predetermined debt; (9.8) on every path; (9.12), (9.9) as a genuine series, and transversality at every state | `FiscalRulesMeasure.SunspotMeasure.sunPrice`, `FiscalRulesMeasure.SunspotMeasure.sunDebt`, `FiscalRulesMeasure.SunspotMeasure.price_pos`, `FiscalRulesMeasure.SunspotMeasure.sunDebt_succ`, `FiscalRulesMeasure.SunspotMeasure.sun_flow`, `FiscalRulesMeasure.SunspotMeasure.sun_rate`, `FiscalRulesMeasure.SunspotMeasure.sun_valuation`, `FiscalRulesMeasure.SunspotMeasure.sun_tvc` |
| Cochrane p. 267 (Theorem FR (b), E9.9) | the sunspot path is a `RuleEqm` with `P_0 = c₀` and initial debt `b̄`; for every `0 < β < 1`, `0 < c₀ < 1`, `θ`, `b̄` it and `P = P*` are both equilibria with the same initial debt, so the rule and (9.12) do not pin `P = P*` | `FiscalRulesMeasure.SunspotMeasure.sunspot_ruleEqm`, `FiscalRulesMeasure.SunspotMeasure.sunPrice_zero`, `FiscalRulesMeasure.SunspotMeasure.sunDebt_zero`, `FiscalRulesMeasure.SunspotMeasure.fr_b_measure`, `FiscalRulesMeasure.SunspotMeasure.fr_b_not_pinned` |
| Cochrane p. 267 (consistency with Theorem FR (d)) | the sunspot prices are neither essentially bounded above nor bounded away from zero | `FiscalRulesMeasure.SunspotMeasure.sun_price_unbounded` |

## §9.3.2 Theorem FR (d) with a stochastic target, pp. 266–267 (FiscalRulesTargetMeasure)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (9.9), p. 266 (supporting lemmas) | iterating `Y_t = βE_tY_{t+1}`; a bounded or dominated iterate is zero; deflating by the target real-rate factor gives a martingale; the finite-horizon value identity; bounds and nonnegativity of the value under transversality | `FiscalRulesTargetMeasure.iterate_beta`, `FiscalRulesTargetMeasure.zero_of_iterate`, `FiscalRulesTargetMeasure.zero_of_iterate'`, `FiscalRulesTargetMeasure.deflated_martingale`, `FiscalRulesTargetMeasure.value_partial`, `FiscalRulesTargetMeasure.value_bounds`, `FiscalRulesTargetMeasure.value_nonneg` |
| Cochrane p. 267 (target value) | a bounded predetermined solution of `a_t = P*_t + βa_{t+1}` is adapted, at least `m/(1 − β)`, and is the expected present value `∑ βʲE_tP*_{t+j}` | `FiscalRulesTargetMeasure.targetValue_ge`, `FiscalRulesTargetMeasure.targetValue_adapted`, `FiscalRulesTargetMeasure.hasSum_E_target` |
| Cochrane pp. 266–267 (Theorem FR (d), stochastic `P*`) | for an adapted bounded target with predetermined present value, any equilibrium with prices bounded above has `P_t = (1 + (b₀ − b̄)/(θa₀))P*_t` a.e.; also for `RuleEqm` | `FiscalRulesTargetMeasure.fr_unique_stochastic`, `FiscalRulesTargetMeasure.fr_unique_ruleEqm` |
| Cochrane pp. 266–267 (Theorem FR (d), bounded away from zero) | the same conclusion for prices bounded below, given a bounded cumulative target real-rate factor | `FiscalRulesTargetMeasure.fr_unique_stochastic_below` |
| Cochrane pp. 266–267 (Theorem FR (d), `b₀ = b̄`) | `P = P*` | `FiscalRulesTargetMeasure.fr_unique_stochastic_target` |
| Cochrane p. 267 (Theorem FR (d), existence) | `P = cP*` with `b_t = b̄ + θ(c − 1)a_t` is an equilibrium for `c = 1 + (b₀ − b̄)/(θa₀) > 0` | `FiscalRulesTargetMeasure.exists_proportional` |
| Cochrane p. 267 (initial debt ≠ PV of `s₀`) | `P = P*` at every date forces `b₀ = b̄`, for any target and without bounds; with `b₀ ≠ b̄` the price level is pinned at a multiple of `P*`, never at `P*` | `FiscalRulesTargetMeasure.initial_debt_of_target`, `FiscalRulesTargetMeasure.fr_initial_debt` |
| Cochrane p. 266 (`a(β) = 0` analogue), deterministic targets | a deterministic bounded target has a predetermined present value and a telescoping, bounded real-rate factor; Theorem FR (d) for every deterministic target and initial debt, bounded above or away from zero | `FiscalRulesTargetMeasure.deterministic_target`, `FiscalRulesTargetMeasure.deterministic_deflator`, `FiscalRulesTargetMeasure.fr_unique_deterministic` |
| Cochrane p. 266 (`a(β) = 0` analogue), an s-shaped target | `P*_t = p̄ + η_t − η_{t−1}/β` has the predetermined present value `p̄/(1 − β) − η_{t−1}/β`, genuine news, and with `b₀ = b̄` the only bounded-above equilibrium is `P = P*` | `FiscalRulesTargetMeasure.lag`, `FiscalRulesTargetMeasure.sTarget`, `FiscalRulesTargetMeasure.sValue`, `FiscalRulesTargetMeasure.sTarget_props`, `FiscalRulesTargetMeasure.sTarget_news`, `FiscalRulesTargetMeasure.fr_unique_sShaped` |
| Cochrane p. 267 (counterexample, the space) | a fair coin revealed at date 1 as a measure system: `E_0` is the average, everything is known from date 1 | `FiscalRulesTargetMeasure.BoolExample.boolInfo`, `FiscalRulesTargetMeasure.BoolExample.boolTree`, `FiscalRulesTargetMeasure.BoolExample.boolSystem`, `FiscalRulesTargetMeasure.BoolExample.boolSystem_fullSupport`, `FiscalRulesTargetMeasure.BoolExample.boolE_zero`, `FiscalRulesTargetMeasure.BoolExample.boolE_succ`, `FiscalRulesTargetMeasure.BoolExample.bool_stronglyMeasurable_succ`, `FiscalRulesTargetMeasure.BoolExample.bool_adapted` |
| Cochrane p. 267 (what fails without a predetermined target value) | the target `P*_0 = 9/7`, then `3` or `1`, with `1 ≤ P* ≤ 3`; `P = P* + 1` with `b ≡ b̄ + θ/(1 − β)` is a bounded equilibrium, not proportional to `P*`, and no predetermined target value exists | `FiscalRulesTargetMeasure.BoolExample.Ps`, `FiscalRulesTargetMeasure.BoolExample.Pc`, `FiscalRulesTargetMeasure.BoolExample.bc`, `FiscalRulesTargetMeasure.BoolExample.Ps_bounds`, `FiscalRulesTargetMeasure.BoolExample.bool_ruleEqm`, `FiscalRulesTargetMeasure.BoolExample.Pc_not_proportional`, `FiscalRulesTargetMeasure.BoolExample.no_targetValue`, `FiscalRulesTargetMeasure.BoolExample.bool_counterexample` |
| Cochrane pp. 266–267 (Theorem FR (d), link to `FiscalRules`) | on finite full-support systems the measure theorem gives `FiscalRules.fr_unique_bounded` (bounded-above case), and the two agree | `FiscalRulesTargetMeasure.fr_unique_bounded_link`, `FiscalRulesTargetMeasure.fr_unique_bounded_link_core` |

## §9.3.2 Theorem FR (d) with a news-bearing target and a general `s₀`, pp. 266–267 (FiscalRulesTargetOpen)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §9.3.2, (9.8), (9.9), (9.12), pp. 266–267 | the rule equilibrium with a general underlying surplus `s₀` (the book's `s_{0,t} = a(L)ε_{s,t}`); `RuleEqm` is the case `s₀ = (1 − β)b̄` | `FiscalRulesTargetOpen.RuleEqmGen`, `FiscalRulesTargetOpen.ruleEqm_iff_gen` |
| Cochrane (9.8), (9.9), p. 266 (supporting lemmas) | a bounded surplus with the transversality condition gives `\|b_t\| ≤ C/(1 − β)`; a bounded predetermined `B` with `B_t = s_t + βB_{t+1}` is the expected present value of `s` (a `HasSum`); the transversality condition survives subtracting a bounded process | `FiscalRulesTargetOpen.debt_bdd`, `FiscalRulesTargetOpen.hasSum_E_value`, `FiscalRulesTargetOpen.tvc_sub_bdd` |
| Cochrane p. 266 (existence, `P = P*`) | with a bounded predetermined present value `B` of `s₀`, `P = P*` and `b = B` is an equilibrium for any positive adapted integrable target | `FiscalRulesTargetOpen.target_ruleEqmGen` |
| Cochrane (9.12), pp. 266–267 (the growth argument) | a price below the comparison path today forces one below it tomorrow on a positive-probability event; along such events the scaled debt difference grows, `Δ_{t+k+1} > δ/βᵏ` | `FiscalRulesTargetOpen.child_lt`, `FiscalRulesTargetOpen.compare_step` |
| Cochrane pp. 266–267, Thm FR (d) (comparison form) | two bounded-above equilibria with the same `s₀`, target and initial debt coincide; no condition on `s₀` or the target | `FiscalRulesTargetOpen.fr_compare` |
| Cochrane p. 267, Thm FR (d), stochastic `P*`, `b₀ = b̄` | `P = P*` is an equilibrium and the unique bounded-above one, even if the target's present value has news; with a general `s₀` and `b₀ = B₀`, `P = P*` and `b = B` | `FiscalRulesTargetOpen.fr_d_news`, `FiscalRulesTargetOpen.fr_unique_news` |
| Cochrane p. 267 (news example) | on the coin tree of `FiscalRulesTargetMeasure.BoolExample`, the bounded-above equilibrium is unique for every initial debt: `P*` for `b₀ = b̄`, `P* + 1` for `b₀ = b̄ + θ/(1 − β)` | `FiscalRulesTargetOpen.BoolNews.bool_news_unique` |
| link to core FR (d) | the news-robust theorem specialises to `FiscalRules.fr_unique_bounded` (bounded-above case) | `FiscalRulesTargetOpen.fr_d_news_link` |
| Cochrane p. 266, (9.9) with a general `s₀`, `a(β) = 0` | `P = (1 + (b₀ − B₀)/(θa₀))P*`, prices bounded above or bounded away from zero (the latter with the bounded real-rate factor); the same with random date-0 data in a band `c ∈ [c_min, c_max]`, `c_min > 0` | `FiscalRulesTargetOpen.fr_unique_s0`, `FiscalRulesTargetOpen.fr_unique_s0_below`, `FiscalRulesTargetOpen.fr_unique_s0_random`, `FiscalRulesTargetOpen.fr_unique_s0_random_below` |
| Cochrane p. 266, `s₀ = a(L)ε`, finite order | lagged shocks with a zero pre-sample, the surplus, the coefficients `c_m = ∑_{k≥m}α_kβ^{k−m}` (`c_0 = a(β)`, `c_{n+1} = 0`, `c_m = α_m + βc_{m+1}`) and the present value `B_t = ∑c_mε_{t−m}`; measurability and bounds | `FiscalRulesTargetOpen.MA.lagε`, `FiscalRulesTargetOpen.MA.surplus`, `FiscalRulesTargetOpen.MA.coef`, `FiscalRulesTargetOpen.MA.value`, `FiscalRulesTargetOpen.MA.lagε_succ`, `FiscalRulesTargetOpen.MA.coef_succ`, `FiscalRulesTargetOpen.MA.coef_zero`, `FiscalRulesTargetOpen.MA.coef_top`, `FiscalRulesTargetOpen.MA.lagε_measurable`, `FiscalRulesTargetOpen.MA.abs_lagε_le` |
| Cochrane p. 266, `a(β) = 0` | no news in the present value: `B_t = s_{0,t} + βB_{t+1}` with `B_{t+1}` known at `t`; the surplus and its present value are adapted and bounded, `B_0 = 0` | `FiscalRulesTargetOpen.MA.value_rec`, `FiscalRulesTargetOpen.MA.ma_props`, `FiscalRulesTargetOpen.MA.value_zero` |
| Cochrane p. 266, `s₀ = a(L)ε`, infinite order | for absolutely summable `α`: the surplus, coefficients and present value, convergence, `c_m = α_m + βc_{m+1}`, a uniform bound, `B_t = s_{0,t} + βB_{t+1}` when `a(β) = 0`, adapted and bounded | `FiscalRulesTargetOpen.MAinf.surplus`, `FiscalRulesTargetOpen.MAinf.coef`, `FiscalRulesTargetOpen.MAinf.value`, `FiscalRulesTargetOpen.MAinf.summable_abs_shift`, `FiscalRulesTargetOpen.MAinf.coef_succ`, `FiscalRulesTargetOpen.MAinf.value_rec`, `FiscalRulesTargetOpen.MAinf.sum_coef_le`, `FiscalRulesTargetOpen.MAinf.ma_props` |
| Cochrane p. 266 with p. 267 | FR (d) for a moving-average `s₀` with `a(β) = 0` and any adapted target: with zero initial debt the only bounded-above equilibrium is `P = P*` | `FiscalRulesTargetOpen.MA.fr_unique_ma`, `FiscalRulesTargetOpen.MAinf.fr_unique_ma` |

## §9.3.2 Theorem FR (d), prices bounded away from zero: a counterexample, pp. 266–267 (FiscalRulesBelowCounter)

All rows cite p. 267 unless marked. The space is `Ω = ℕ → ℝ` with i.i.d. biased coins,
`P(up) = p = (4 − 2β)/(8 − 3β)`.

| Book | Claim | Lean |
| --- | --- | --- |
| p. 267 (the shocks) | the biased coin `pδ₁ + (1 − p)δ₋₁`, its total mass and integrals; branch forecasts `E_t = pf + (1 − p)g`; atoms of mass at most `max(p, 1 − p)` | `FiscalRulesBelowCounter.biasMeasure`, `FiscalRulesBelowCounter.biasMeasure_univ`, `FiscalRulesBelowCounter.biasCoin`, `FiscalRulesBelowCounter.integral_biasCoin`, `FiscalRulesBelowCounter.E_branch`, `FiscalRulesBelowCounter.biasCoin_singleton_le` |
| p. 267 (the space) | the i.i.d. biased-coin system with its natural filtration; every history is null | `FiscalRulesBelowCounter.Sys`, `FiscalRulesBelowCounter.sys_singleton` |
| p. 267 (parameters) | `κ = 1 − β/2`, `κ' = 1 − β/4`, `p = κ/(κ + κ')`, the scale `c`, the Lyapunov base `x`, the contraction `λ < 1`, the price floor `m_P > 0` | `FiscalRulesBelowCounter.kap`, `FiscalRulesBelowCounter.kq`, `FiscalRulesBelowCounter.pr`, `FiscalRulesBelowCounter.cc`, `FiscalRulesBelowCounter.xL`, `FiscalRulesBelowCounter.lam`, `FiscalRulesBelowCounter.params`, `FiscalRulesBelowCounter.mP`, `FiscalRulesBelowCounter.mP_pos` |
| p. 267 (processes) | the target's present value `a_t` and the target `P*_t = a_t − βa_{t+1}`; the absorbed random walk `S_t`; the sunspot `M_t = c(1 − κ'^{S_t})` and its two successors; `Ã_t`, `B_t`, the value `V_t`, the price level `P_t = V_tP*_t/Ã_t`, real debt `b_t = b̄ + θ(V_t − a_t)`; the Lyapunov function `Ψ` | `FiscalRulesBelowCounter.av`, `FiscalRulesBelowCounter.tgt`, `FiscalRulesBelowCounter.Sw`, `FiscalRulesBelowCounter.Mv`, `FiscalRulesBelowCounter.Mup`, `FiscalRulesBelowCounter.Mdn`, `FiscalRulesBelowCounter.At`, `FiscalRulesBelowCounter.Bv`, `FiscalRulesBelowCounter.Vv`, `FiscalRulesBelowCounter.Pv`, `FiscalRulesBelowCounter.bv`, `FiscalRulesBelowCounter.Phi`, `FiscalRulesBelowCounter.Psi` |
| p. 267 (measurability) | coins, `a_t`, the target, `S_t` and its functions, `M`, `Ã`, `B`, `V`, `P`, `Φ`, `Ψ` are known at `t`; `a_{t+1}` and `V_{t+1}` are known at `t` | `FiscalRulesBelowCounter.meas_up`, `FiscalRulesBelowCounter.av_meas`, `FiscalRulesBelowCounter.av_pred`, `FiscalRulesBelowCounter.tgt_meas`, `FiscalRulesBelowCounter.Sw_meas`, `FiscalRulesBelowCounter.Sw_fun_meas`, `FiscalRulesBelowCounter.MAB_meas`, `FiscalRulesBelowCounter.Vv_meas`, `FiscalRulesBelowCounter.Vv_pred`, `FiscalRulesBelowCounter.Pv_meas`, `FiscalRulesBelowCounter.Phi_meas`, `FiscalRulesBelowCounter.Psi_meas` |
| p. 267 (pathwise facts) | `1 ≤ a_t ≤ 2 − β`; the target's two values stand in the ratio `κ`, are bounded and positive; `S_t` is absorbed at 0 and `≤ t + 1`; bounds on `M` and `Ã`; `βB_t = Ã_t − P*_t`; the discounted value recursion and ratio bound; the pathwise invariants; `m_P ≤ P_t ≤ V_t`; bounds on `Ψ`; the successor of `M` | `FiscalRulesBelowCounter.av_bounds`, `FiscalRulesBelowCounter.tgt_eq`, `FiscalRulesBelowCounter.tgt_bounds`, `FiscalRulesBelowCounter.tgt_pos`, `FiscalRulesBelowCounter.Sw_succ_zero`, `FiscalRulesBelowCounter.Sw_le`, `FiscalRulesBelowCounter.Mv_bounds`, `FiscalRulesBelowCounter.At_bounds`, `FiscalRulesBelowCounter.Bv_eq`, `FiscalRulesBelowCounter.Vv_fac`, `FiscalRulesBelowCounter.ratio_le`, `FiscalRulesBelowCounter.path_invariants`, `FiscalRulesBelowCounter.Pv_bounds`, `FiscalRulesBelowCounter.Psi_bounds`, `FiscalRulesBelowCounter.Mv_succ` |
| (9.8), (9.9), p. 266; (9.12), p. 267 | `V_t = P_t + βV_{t+1}`; the flow (9.8) on every path; `M` is a martingale under the target's risk-adjusted measure; the interest-rate target (9.12) | `FiscalRulesBelowCounter.Vv_rec`, `FiscalRulesBelowCounter.bv_flow`, `FiscalRulesBelowCounter.qmart`, `FiscalRulesBelowCounter.rate` |
| (9.9), p. 266 (transversality and valuation) | every process is integrable; `Ψ` contracts, `E_tΨ_{t+k} ≤ λᵏΨ_t`; the forecast value decays; the transversality condition; (9.9) as a `HasSum` | `FiscalRulesBelowCounter.integrable_all`, `FiscalRulesBelowCounter.psi_step`, `FiscalRulesBelowCounter.psi_iter`, `FiscalRulesBelowCounter.EV_bound`, `FiscalRulesBelowCounter.tvc`, `FiscalRulesBelowCounter.valuation` |
| pp. 266–267 | the construction is a `RuleEqm` | `FiscalRulesBelowCounter.counter_ruleEqm` |
| pp. 266–267, Thm FR (d), bounded away from zero (correction) | the bounded real-rate hypothesis is indispensable: for every `β ∈ (0, 1)`, `θ ≠ 0` and `b̄`, an equilibrium with `b₀ = b̄`, a predetermined target value and `P ≥ m_P > 0` has `P ≠ P*` (indeed `P₀ < P*₀` on every path) | `FiscalRulesBelowCounter.fr_below_counterexample` |
| pp. 266–267 | the dividing line for `b₀ = b̄`: bounded above means unique for every target; bounded away from zero alone does not | `FiscalRulesBelowCounter.fr_d_dividing_line` |
| link to core FR (d), bounded-below case | with constant `P*` the hypothesis holds (`L = 1`), giving the core result | `FiscalRulesBelowCounter.fr_below_link` |

## §9.3.2 Theorem FR (d): the bounded-below case with news, random date-0 data and existence, pp. 266–267 (FiscalRulesTargetClose)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (9.8), (9.12), pp. 266–267 (the growth argument) | propagation of `P_t < P'_t` with `Δ_{t+k+1} > δ/βᵏ`; a positive `Δ` exceeds some `1/(n + 1)`; the base event; one-sided versions with `Δ` bounded above, or bounded only where `P < P'` and the comparison path bounded | `FiscalRulesTargetClose.propagate`, `FiscalRulesTargetClose.exists_delta`, `FiscalRulesTargetClose.base_event`, `FiscalRulesTargetClose.compare_step_le`, `FiscalRulesTargetClose.compare_step_ratio` |
| Cochrane (9.9), p. 266 (supporting) | for positive prices, `D_t ≥ −M*/(1 − β)` | `FiscalRulesTargetClose.value_lower` |
| Cochrane p. 267 (supporting) | under the bounded real-rate factor, the debt deviation is at most a fixed multiple of the price level, `\|D_t\| ≤ L(M*/m_P + 1)/(1 − β)·P_t` | `FiscalRulesTargetClose.ratio_bdd` |
| Cochrane p. 267, Thm FR (d), bounded away from zero, stochastic `P*` | with the bounded real-rate factor, an equilibrium with `P ≥ m_P` equals any bounded-above one with the same initial debt; `P = P*` (and `b = B`) when `b₀` is the present value of `s₀`; `P = P*` for `RuleEqm` with `b₀ = b̄`; the target's present value may have news | `FiscalRulesTargetClose.fr_compare_below`, `FiscalRulesTargetClose.fr_unique_below_news`, `FiscalRulesTargetClose.fr_d_news_below` |
| Cochrane p. 266, general `s₀`, random date-0 data | `P = (1 + (b₀ − B₀)/(θa₀))P*` with no assumed band (`c > 0` a.e. is derived), prices bounded above or bounded away from zero | `FiscalRulesTargetClose.fr_unique_s0_random_full`, `FiscalRulesTargetClose.fr_unique_s0_random_below_full` |
| Cochrane p. 267 (one-shot news) | the system with no information at date 0 and everything known from date 1; `E_0` is the mean, `E_{t+1}f = f`, date-0 variables are constants; the target `P*_0 = p₀`, `P*_t = x` | `FiscalRulesTargetClose.oneShotFiltration`, `FiscalRulesTargetClose.oneShot`, `FiscalRulesTargetClose.oneShot_E_zero`, `FiscalRulesTargetClose.oneShot_E_succ`, `FiscalRulesTargetClose.oneShot_const`, `FiscalRulesTargetClose.osTarget` |
| Cochrane p. 267, existence with news, `b₀ ≠ b̄` | every bounded-above equilibrium is described by one number `d` solving `(p₀ + d₀ − βd)E[1/(x + (1 − β)d)] = p₀E[1/x]` with positive prices, and every such `d` gives one: the exact existence condition for one-shot news | `FiscalRulesTargetClose.oneShot_eqm_form`, `FiscalRulesTargetClose.osPrice`, `FiscalRulesTargetClose.osDebt`, `FiscalRulesTargetClose.oneShot_eqm_exists` |
| same, infimum attained (finite trees) | an equilibrium exists iff `d₀ + p₀ + βx_min/(1 − β) > 0`, i.e. iff the realised present value of the target plus `d₀` is positive on every path | `FiscalRulesTargetClose.oneShot_exists_iff_atom` |
| same (counterexample) | on `(ℕ, ∑π_kδ_k)`, `π_k = 3·4^{−(k+1)}`, with `x_k = 1 + 2^{−(k+1)}` (infimum not attained) and `d₀ = 1/10 − 1 − β/(1 − β)`: the realised present value plus `d₀` is at least `1/10` on every path, yet no bounded-above equilibrium exists | `FiscalRulesTargetClose.NoExist.wts`, `FiscalRulesTargetClose.NoExist.wts_pos`, `FiscalRulesTargetClose.NoExist.hasSum_wts`, `FiscalRulesTargetClose.NoExist.wMeasure`, `FiscalRulesTargetClose.NoExist.wMeasure_singleton`, `FiscalRulesTargetClose.NoExist.wMeasure_univ`, `FiscalRulesTargetClose.NoExist.wProb`, `FiscalRulesTargetClose.NoExist.xC`, `FiscalRulesTargetClose.NoExist.integral_pow2`, `FiscalRulesTargetClose.NoExist.oneShot_no_eqm` |

## §9.3.2 Theorem FR (d): exact existence, uniqueness without bounds above, and finite news, pp. 266–267 (FiscalRulesTargetFinal)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (9.12), p. 267 (supporting) | the target's real-rate factor `γ_t = E_t(P*_t/P*_{t+1})` and the deflator `N_t⁻¹ = ∏_{i<t} γ_i⁻¹`: `γ_t` is known at `t` and lies in `[m/M*, M*/m]`; `N⁻¹` is predictable, `0 < N_t⁻¹ ≤ (M*/m)ᵗ` and `N_{t+1}⁻¹γ_t = N_t⁻¹`; (9.12) as `E_t(1/P_{t+1}) = γ_t/P_t` | `FiscalRulesTargetFinal.gam`, `FiscalRulesTargetFinal.defl`, `FiscalRulesTargetFinal.gam_meas`, `FiscalRulesTargetFinal.gam_bounds`, `FiscalRulesTargetFinal.defl_meas`, `FiscalRulesTargetFinal.defl_bounds`, `FiscalRulesTargetFinal.defl_succ`, `FiscalRulesTargetFinal.rate_q` |
| Cochrane (9.8), (9.12), pp. 266–267 (the comparison identity) | `K_t = βᵗN_t⁻¹(1/P_t − 1/P'_t)Δ_t`, `Δ = (b − b')/θ`, is a submartingale with drift `βᵗN_t⁻¹(P'_t − P_t)²/(P_tP'_t) ≥ 0`; if `E_0K_T → 0` the drifts sum to `−K_0`, and `Δ_0 = 0` forces `P = P'` and `Δ ≡ 0` | `FiscalRulesTargetFinal.drift_hasSum`, `FiscalRulesTargetFinal.drift_unique` |
| Cochrane pp. 266–267, Thm FR (d), bounded away from zero, any `b₀` (correction) | with prices bounded away from zero (possibly unbounded above) and the deflator bounded from date 0, `E_0K_T → 0`; the identity `∑E_0[βᵗN_t⁻¹(P'_t − P_t)²/(P_tP'_t)] = ((b_0 − b'_0)/θ)(1/P'_0 − 1/P_0)`; two such equilibria with the same initial debt (`b̄` or not) coincide, for a general `s₀` and for the book's rule; the date-0 bound follows from the bound of `FiscalRulesTargetClose` | `FiscalRulesTargetFinal.below_limit`, `FiscalRulesTargetFinal.compare_identity_below`, `FiscalRulesTargetFinal.fr_unique_below_pair`, `FiscalRulesTargetFinal.fr_unique_below_rule`, `FiscalRulesTargetFinal.hL0_of_hL` |
| link to `FiscalRulesTargetClose` | with `b₀ = b̄` the pair theorem against `P = P*` re-derives `FiscalRulesTargetClose.fr_d_news_below` from the date-0 deflator bound alone | `FiscalRulesTargetFinal.fr_d_news_below_of_pair` |
| Cochrane (9.8)–(9.9), p. 266 (supporting) | the debt deviation generated forward from `d₀`, path by path: its flow, the telescoped `βᵀD_T = d₀ − ∑_{s<T}βˢ(P_s − P*_s)`, predetermination; bounded on a path iff the realised discounted deviations sum to `d₀` there; `hasSum_E_value` with the present value bounded only a.e. | `FiscalRulesTargetFinal.fwdDebt`, `FiscalRulesTargetFinal.fwdDebt_flow`, `FiscalRulesTargetFinal.fwdDebt_tele`, `FiscalRulesTargetFinal.fwdDebt_meas`, `FiscalRulesTargetFinal.fwdDebt_bdd_of_hasSum`, `FiscalRulesTargetFinal.hasSum_of_fwdDebt_bdd`, `FiscalRulesTargetFinal.hasSum_E_value_ae` |
| Cochrane pp. 266–267, existence, `b₀ ≠ b̄`, news at any dates | a bounded-above `P` meeting (9.12) with bounded forward debt is an equilibrium with `b₀ = b̄ + θd₀` (valuation and transversality follow); an equilibrium exists iff some `P` meets (9.12) with `∑βˢ(P_s − P*_s) = d₀` a.e. | `FiscalRulesTargetFinal.eqm_of_bdd`, `FiscalRulesTargetFinal.exists_iff_pathwise` |
| Cochrane (9.9), p. 266, as a forward recursion | the pathwise condition holds iff the forward valuation `forwardSol β (P − P*)`, the unique bounded solution of the contraction, is predictable and starts at `d₀`; existence iff such a `P` meets (9.12) | `FiscalRulesTargetFinal.forward_iff_pathwise`, `FiscalRulesTargetFinal.exists_iff_forward` |
| Cochrane pp. 266–267, existence | necessary: `d₀ + ∑βˢP*_s > 0` a.e.; with a predetermined target value `a`, existence iff `d₀ + a₀ > 0`; on the one-shot system the scalar condition of `FiscalRulesTargetClose` is recovered, with positivity needed only a.e. | `FiscalRulesTargetFinal.exists_imp_pos`, `FiscalRulesTargetFinal.predetermined_exists_iff`, `FiscalRulesTargetFinal.oneShot_exists_iff` |
| Cochrane pp. 266–267, comparative statics | for bounded-above equilibria `E_0K_T → 0` and the identity hold with no deflator bound; `d₀ ≤ d₀'` gives `P₀ ≤ P'₀` | `FiscalRulesTargetFinal.above_limit`, `FiscalRulesTargetFinal.compare_identity_above`, `FiscalRulesTargetFinal.price_monotone` |
| Cochrane p. 267, finite news | a system is resolved at `T` if no news arrives after `T`; then `γ_i = P*_i/P*_{i+1}` for `i ≥ T` and `∏γ⁻¹ ≤ (M*/m)^{2T+1}`, so FR (d) with prices bounded away from zero holds (`b₀ = b̄` gives `P = P*`; any `b₀`, uniqueness) with no deflator hypothesis | `FiscalRulesTargetFinal.EventuallyResolved`, `FiscalRulesTargetFinal.resolved_gam`, `FiscalRulesTargetFinal.resolved_hL`, `FiscalRulesTargetFinal.fr_d_resolved`, `FiscalRulesTargetFinal.fr_unique_resolved` |
| same (counterexample and finite systems) | the i.i.d. system of `FiscalRulesBelowCounter.fr_below_counterexample` is never resolved; every finite system is, so its deflator is bounded; on the bridged measure system of every core finite tree FR (d) for prices bounded away from zero holds without further hypotheses | `FiscalRulesTargetFinal.iid_not_resolved`, `FiscalRulesTargetFinal.finite_resolved`, `FiscalRulesTargetFinal.finite_hL`, `FiscalRulesTargetFinal.tree_fr_d` |

## §9.3.3 Fiscal rules in practice, (9.13)–(9.14), pp. 267–269 (FiscalRules)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §9.3.3, p. 269 (E9.6) | with the same-date rule, `b_{r,t} = R/(1 + Rα_r)(b_{r,t−1} − s_{0,t})`, the transversality condition holds for every `α_r > 0`, and the regular budget repays itself | `FiscalRules.regular_solve`, `FiscalRules.regular_tvc`, `FiscalRules.regular_hasSum` |
| Cochrane (9.14), p. 269 | the emergency budget `b_{p,t−1} = θ ∑ βʲ(P_{t+j} − P*_{t+j})`; with the debt target `b_{p,t} = 0`, `P_t = P*_t` | `FiscalRules.emergency_hasSum`, `FiscalRules.emergency_debt_target` |
| Cochrane pp. 268–269 | the total surplus and debt obey the usual valuation | `FiscalRules.total_hasSum` |
| Cochrane p. 269 (variant, E9.6) | with a lagged rule `s_{r,t} = s_{0,t} + α_rb_{r,t−1}`, transversality and repayment need `0 < α_r < 2`, and with `s₀ = 0` hold iff `0 < α_r < 2` | `FiscalRules.lagged_tvc`, `FiscalRules.lagged_tvc_iff`, `FiscalRules.lagged_hasSum` |

## §9.3.4 A fiscal rule with inflation and interest rates, (9.15)–(9.16), pp. 269–270 (FiscalTaylor)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (9.15), p. 270 | `E_tπ_{t+1} = θ_{iπ}π_t + u_t`; iterated, `E_tπ_{t+j} = θʲπ_t + fⱼu_t` | `FiscalTaylor.eq_9_15`, `FiscalTaylor.E_pi_iterate` |
| Cochrane (9.16), p. 270 | the coefficients `fⱼ`, `(θ − η)fⱼ = θʲ − ηʲ`, the bound and summability, `∑ βʲfⱼ = β/((1 − βθ)(1 − βη))`, `∑ (βθ)ʲ = 1/(1 − βθ)` | `FiscalTaylor.coefSeq`, `FiscalTaylor.coefSeq_closed`, `FiscalTaylor.abs_coefSeq_le`, `FiscalTaylor.summable_coefSeq`, `FiscalTaylor.tsum_coefSeq`, `FiscalTaylor.tsum_theta` |
| Cochrane (9.16), p. 270 (E9.3) | the valuation equation in terms of `π_t`, `u_t` and the present value of `s₀`, for `\|βθ_{iπ}\| < 1`, `\|βη\| < 1` | `FiscalTaylor.eq_9_16` |
| Cochrane §9.3.4, p. 270 | with `θ_{sπ} ≠ 0` inflation is determined at each date, explicitly; with `θ_{sπ} = 0` it is not; without the rate rule the valuation equation alone does not pin it down | `FiscalTaylor.pi_eq`, `FiscalTaylor.pi_determined`, `FiscalTaylor.pi_not_determined_without_surplus_response`, `FiscalTaylor.rate_rule_essential` |
| Cochrane §9.3.4, p. 270 (E9.3) | the `θ_{iπ} = 0` case, with `b_t` corrected to `b_{t−1}` | `FiscalTaylor.eq_theta_i_zero` |

## §9.3.5 Fiscal rules with nominal debt, p. 271 (MixedDebtRules)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §9.3.5, p. 271 | with `B > 0` the debt value `b + B/P` falls with `P`; a surplus that does not fall with `P`, in particular a constant one, gives at most one price level | `MixedDebtRules.value_strictAntiOn`, `MixedDebtRules.price_unique`, `MixedDebtRules.price_unique_const` |
| Cochrane §9.3.5, p. 271 | multiplicity requires `s′ < 0`, and occurs for `s(P) = b + B/P` | `MixedDebtRules.multiplicity_needs_decreasing`, `MixedDebtRules.multiplicity_example` |
| Cochrane §9.3.5, p. 271 | the derivative and elasticity of the debt value; with a nominal share of 10%, a 10% rise or fall in `P` changes the debt value by exactly `1/110` or `1/90`, not 1% | `MixedDebtRules.hasDerivAt_value`, `MixedDebtRules.elasticity_value`, `MixedDebtRules.ten_percent_rise`, `MixedDebtRules.ten_percent_fall` |
| Cochrane §9.3.5, p. 271 | a shock is split into debt devaluation and fiscal tightening; the devaluation share `k/(γ + k)` falls as `γ = s′(P)` rises | `MixedDebtRules.shock_decomposition`, `MixedDebtRules.devaluationShare`, `MixedDebtRules.devaluationShare_strictAnti`, `MixedDebtRules.devaluation_part` |

## §9.4–§9.4.1 Targeting the spread, (9.17)–(9.26), pp. 271–278 (SpreadTarget)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §9.4, p. 273 | a Taylor rule with a real rate tracking it is a spread target; the zero-cost swap rate is `β/Q_t`, expected inflation under the nominal risk-neutral weights | `SpreadTarget.taylor_spread_equiv`, `SpreadTarget.swap_rate` |
| Cochrane (9.17)–(9.21), p. 275 | the simple model; `σκr_t = E_tπ_{t+1} − π_t`; (9.21) for every `θ`, including `θ = 1`; `0 ≤ λ < 1`; `λ − 1`; iterated expectations | `SpreadTarget.SimpleModel`, `SpreadTarget.r_eq`, `SpreadTarget.eq_9_21_mul`, `SpreadTarget.lam`, `SpreadTarget.eq_9_21`, `SpreadTarget.lam_bounds`, `SpreadTarget.lam_sub_one`, `SpreadTarget.E_pi_iter` |
| Cochrane §9.4.1, p. 275 | without (9.22) inflation is stable but indeterminate | `SpreadTarget.indeterminate_without_valuation` |
| Cochrane (9.22), pp. 275–276 | the innovation operator, the valuation equation, innovations in future inflation and in the real return, the discount-rate term | `SpreadTarget.innov`, `SpreadTarget.Valuation`, `SpreadTarget.innov_pi_iter`, `SpreadTarget.innov_return`, `SpreadTarget.coefD`, `SpreadTarget.valuation_sum` |
| Cochrane (9.23), p. 276 (Theorem ST) | (9.22) holds iff `ΔE_{t+1}π_{t+1} = −D/(D + ρ)ε^{Σs}_{t+1}`; the solution path; uniqueness given `π_0`; existence and boundedness | `SpreadTarget.unexpected_inflation_iff`, `SpreadTarget.eq_9_23`, `SpreadTarget.pi_succ`, `SpreadTarget.unique_solution`, `SpreadTarget.solPi`, `SpreadTarget.exists_solution`, `SpreadTarget.solution_bounded` |
| Cochrane p. 276 and footnote 1 (E9.5) | the cases `θ = 0` and `θ = 1` (proved directly), the footnote formula undefined at `θ = 1`, the limit `θ → 1` | `SpreadTarget.theta_zero`, `SpreadTarget.theta_one`, `SpreadTarget.footnote_r`, `SpreadTarget.tendsto_coef_theta_one` |
| Cochrane p. 277 | at `θ = 1`, `x`, `r` and `i` follow inflation | `SpreadTarget.theta_one_paths` |
| Cochrane (9.24)–(9.26), p. 277 (E9.4, E9.7) | the full new-Keynesian model with a spread target; the first line of (9.26) (given inflation); the inflation innovation; (9.26) corrected; the difference from the printed formula; counterexamples to the printed `1/κ` (perfect foresight) and sign (coin-flip tree) | `SpreadTarget.FullNK`, `SpreadTarget.x_formula`, `SpreadTarget.innov_eq`, `SpreadTarget.r_formula`, `SpreadTarget.printed_minus_corrected`, `SpreadTarget.printed_9_26_fails_perfectForesight`, `SpreadTarget.coinPi`, `SpreadTarget.printed_9_26_fails_coin` |
| Cochrane p. 278 (Holden 2020) | `i_t = r_t + π* + φ(π_t − π*)` with `\|φ\| > 1` has the unique bounded solution `π ≡ π*` | `SpreadTarget.holden_unique` |

## §9.4.2 Debt sales with a spread target, (9.27), pp. 278–280 (SpreadSwap)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (9.27), p. 279 | `Q_tB_t/P_t = βB_tE_t(1/P_{t+1})`; the end-of-period valuation `βb_t + Q_tB_t/P_t = W` | `SpreadSwap.eq_9_27`, `SpreadSwap.end_of_period_valuation` |
| Cochrane §9.4.2, p. 279 | swaps at market prices leave `E_t(1/P_{t+1})` unchanged | `SpreadSwap.market_price_irrelevant` |
| Cochrane pp. 279–280 | after swaps at `P*`, `E_t(1/P_{t+1}) = e(B)`, and `de/dB = −(e − 1/P*)/B` | `SpreadSwap.eSwap`, `SpreadSwap.swap_valuation_iff`, `SpreadSwap.hasDerivAt_eSwap` |
| Cochrane bullet p. 280 (E9.8) | the hyperbola `e(B) − 1/P* = C/B`, `C = B₀(e₀ − 1/P*)`; the target is reached at finite `B` iff the gap was zero; the gap when real debt is exhausted; the numerical example `7/30 → 35/222` | `SpreadSwap.eSwap_sub_target`, `SpreadSwap.gap_const`, `SpreadSwap.swap_reaches_target_iff`, `SpreadSwap.real_debt_exhausted`, `SpreadSwap.numeric_example` |
| Cochrane p. 280 | the book's direction is right: `e` falls as `B` rises but stays above `1/P*` | `SpreadSwap.eSwap_strictAntiOn`, `SpreadSwap.eSwap_gt_target` |
| Cochrane pp. 279–280 (E9.8, corrected statement) | swaps at `P*` leave `b + B/P*` unchanged; the target holds iff `β(b + B/P*) = W`, reached by a passive supply at `B = P*(W/β − b)` | `SpreadSwap.swap_invariant`, `SpreadSwap.passive_supply` |

## §9.5 A price-level target via indexed debt, (9.28)–(9.29), pp. 281–284 (IndexedDebtPeg)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §9.5, pp. 281–282 | the real return on the pegged bond is too low iff `P_t < P*_t`; concave utility gives decreasing marginal utility | `IndexedDebtPeg.real_rate_low_iff`, `IndexedDebtPeg.marginal_utility_strictAntiOn` |
| Cochrane (9.28)–(9.29), pp. 281–282 (Theorem IP) | in a one-period deviation `P_t < P*_t` gives `c_t > c_{t+1}`; with market clearing the first-order condition holds at every date iff `P = P*`; with `c = y` the budget constraint is the government flow (9.28) | `IndexedDebtPeg.one_period_deviation`, `IndexedDebtPeg.price_eq_target`, `IndexedDebtPeg.eq_9_28_of_clearing` |
| Cochrane p. 282 | with log utility consumption demand is finite at every price level and falls as `P_t` rises | `IndexedDebtPeg.log_demand`, `IndexedDebtPeg.log_demand_strictAntiOn` |
| Cochrane p. 282 | more nominal debt "simply ends up selling less real debt"; a devaluation lowers the real value of nominal debt | `IndexedDebtPeg.nominal_debt_crowds_out_real`, `IndexedDebtPeg.devaluation_lowers_value` |
| Cochrane p. 283 | with a nominal bond-price target `Q*`, `P_t = Q*(1 + r_t)` | `IndexedDebtPeg.price_eq_peg_times_rate` |
| Cochrane pp. 283–284 | the five-minute example: `250 · 1.25 = 312.5`, unbounded money, `≈ 2.36 × 10³⁷` % a year | `IndexedDebtPeg.five_minute_example`, `IndexedDebtPeg.five_minute_unbounded`, `IndexedDebtPeg.annualised_rate` |

## §9.6 A CPI standard?, pp. 284–286 (CPIStandard)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §9.6, p. 285 | a commodity standard gives `P_t = G/g_t`, so relative-price variation is price-level variation | `CPIStandard.commodity_standard_price` |
| Cochrane §9.6, p. 285 | a perpetuity costs `1/r` and rises more than a one-year bond when the real rate falls | `CPIStandard.hasSum_perpetuity`, `CPIStandard.perpetuity_rises_more` |
| Cochrane §§9.5–9.6, pp. 281, 286 | a claim to next period's basket costs `βP_t`; pegging it at `βP*_t` gives `P_t = P*_t` | `CPIStandard.indexed_claim_price`, `CPIStandard.indexed_peg_pins_price` |
| Cochrane §9.6, p. 286 | the CPI bet at `$250` against `260` is an arbitrage with unbounded proceeds | `CPIStandard.cpi_bet_unbounded`, `CPIStandard.cpi_bet_example` |

## §10.1.1–§10.1.2 Pots of assets, (10.1)–(10.6), pp. 288–294 (PotOfAssets)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §10.1.1, p. 289 | `B_{t−1}/P_t = b_t` determines `P_t`; assets whose nominal value `Pb(P)` is strictly increasing determine it, and a solution exists by continuity | `PresentValue.valuation_price_unique`, `PotOfAssets.pot_unique_of_strictMono`, `PotOfAssets.pot_exists_of_continuous` |
| Cochrane §10.1, p. 288 | nominal assets cannot determine the price level | `PotOfAssets.pot_nominal_assets` |
| Cochrane §10.1.1, p. 289 | share splits: scaling `B` scales `P` | `PotOfAssets.share_split` |
| Cochrane p. 290 | the nominal flow is the §8.2 recursion | `RealDebt.nominalFlow_iff_solves` |
| Cochrane (10.1)–(10.3), pp. 290–291 | the share price `q̂_t` and its recursion; the cum-dividend value `ŝ_t + q̂_t` | `PotOfAssets.qhat`, `PotOfAssets.qhat_recursion`, `PotOfAssets.pv_eq_sh_add_qhat` |
| Cochrane (10.2), (10.4), (10.6), pp. 290–293 | the flow with purchases; `X_t`; its two forms; `βE_tX_{t+1}`; (10.2) at every date iff `X_t = βE_tX_{t+1}` | `PotOfAssets.PotFlow`, `PotOfAssets.potX`, `PotOfAssets.potX_eq_pv_form`, `PotOfAssets.beta_E_potX`, `PotOfAssets.potFlow_iff_X` |
| Cochrane (10.3), p. 291 | "both sides must be zero"; flow plus transversality iff `B_{t−1}/P_t = b̂_{t−1}(ŝ_t + q̂_t)`, the same as its middle expression | `PresentValue.eq_zero_of_tvc`, `PotOfAssets.pot_valuation_iff`, `PotOfAssets.pot_valuation_pv` |
| Cochrane (10.4)–(10.5), pp. 291, 293 (E10.3) | dropping `E_{t+1}` in (10.5) is harmless | `PotOfAssets.eq_10_5_eq_10_4` |
| Cochrane p. 291 | purchases at market prices do not affect `P_t`, and are matched by nominal liabilities | `PotOfAssets.purchases_irrelevant`, `PotOfAssets.purchases_matched` |
| Cochrane §10.1.2, pp. 293–294 | the conversion right: selling is profitable iff `P` is too low, buying iff too high, no arbitrage iff (10.3) | `PotOfAssets.sell_profit_pos_iff`, `PotOfAssets.buy_profit_pos_iff`, `PotOfAssets.no_arbitrage_iff` |
| Cochrane pp. 293–294 | the asymmetry of the transversality condition: discounted wealth is constant; transversality iff `X_t = 0`; no-Ponzi iff `X_t ≥ 0`; positive wealth explodes upward, negative downward | `PotOfAssets.discounted_wealth_const`, `PotOfAssets.wealth_tvc_iff`, `PotOfAssets.wealth_noPonzi_iff`, `PotOfAssets.wealth_explodes_pos`, `PotOfAssets.wealth_explodes_neg` |

## §10.1.3 Shares as money, (10.7), pp. 295–297 (SharesAsMoney)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §10.1.3, p. 295 | the share flow; "as if dividends delivered potatoes"; linearity of the present value; share value `(1/N)E_t ∑ βʲs_{t+j}`; `N/P_t = E_t ∑ βʲs_{t+j}` | `SharesAsMoney.ShareFlow`, `SharesAsMoney.shareFlow_iff_solves`, `SharesAsMoney.pv_smul`, `SharesAsMoney.share_valuation_iff`, `SharesAsMoney.potato_price_level`, `PresentValue.valuation_price_unique` |
| Cochrane (10.7), p. 296 | `∑ βʲ = 1/(1 − β) = (1 + r)/r`; the perpetuity's real value | `SharesAsMoney.pv_one`, `SharesAsMoney.perpetuity_real_value`, `SharesAsMoney.one_sub_beta_inv` |
| Cochrane (10.7), p. 296 (E10.1) | `P_t = (1 + y)r/((1 + r)y)`, constant; the printed formula is its reciprocal, equal iff `y = r`, `21/26` against `26/21` at `r = .04`, `y = .05`; `P_t = 1` iff `y = r`; the unit price level | `SharesAsMoney.perpetuity_price_level`, `SharesAsMoney.perpetuity_price_level_process`, `SharesAsMoney.printed_reciprocal`, `SharesAsMoney.printed_eq_iff`, `SharesAsMoney.printed_counterexample`, `SharesAsMoney.price_level_one_iff`, `SharesAsMoney.potato_perpetuity_unit` |
| Cochrane p. 296 | positive equity bounds the perpetuities by the present value of potato sales | `SharesAsMoney.pv_sub_const`, `SharesAsMoney.perpetuity_backing_bound` |
| Cochrane pp. 296–297 (E10.2) | a one-period indexed bond is worth `β`; as numeraire `P_t = 1/β`, not `β`; `1 + y` bonds give `P_t = (1 + r)/(1 + y)` | `SharesAsMoney.oneperiod_real_value`, `SharesAsMoney.oneperiod_price_level`, `SharesAsMoney.printed_beta_wrong`, `SharesAsMoney.numeraire_one_plus_y` |
| Cochrane p. 296 (E10.4) | the bonds are worth at most `βM_t`, exactly so when `M_t ≤ s_{t+1}` | `SharesAsMoney.bond_value_le`, `SharesAsMoney.bond_value_no_default` |

## §10.2–§10.7 Balance sheets, pp. 297–311 (BalanceSheets, CentralBankIndependence)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §10.3, pp. 299–300 | the separate valuations imply the consolidated one; given the central bank's, the treasury's holds iff the consolidated one does; contingent transfers unite the balance sheets | `BalanceSheets.consolidated_of_separate`, `BalanceSheets.treasury_iff_consolidated`, `BalanceSheets.contingent_transfers_unite` |
| Cochrane §10.3, p. 301 (Bassetto–Sargent) | a central bank holding only nominal government debt cannot determine `P`; one with real assets can, `P = (M − B_c)/A` | `BalanceSheets.nominal_cb_cannot_determine`, `BalanceSheets.real_cb_determines` |
| Cochrane §10.2, p. 298 | a walled-off central bank pins `P` and the treasury defaults without inflation; topping up its assets lowers `P` | `BalanceSheets.walled_off_insulated`, `BalanceSheets.topping_up_lowers_price` |
| Cochrane §10.4, p. 301 | the log price level moves one-for-one with the log asset value | `BalanceSheets.asset_volatility_passes_through` |
| Cochrane §10.7, p. 310 | converting debt into floating-rate money leaves `P` unchanged | `CentralBankIndependence.cb_purchase_neutral` |

## §11.5 Real bills, p. 322 (PotOfAssets)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §11.5, p. 322 | money issued against a real asset worth `ΔM/P` leaves `P` unchanged; against a nominal bill, the valuation equation has the same solutions as before | `PotOfAssets.real_bills_real_asset`, `PotOfAssets.real_bills_nominal_asset` |

## §24.3 Exchange rates, p. 527 (ExchangeRates)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §24.3, p. 527 (Daniel 2001b) | separate surplus pools: unique price levels and `e = (B₁/V₁)/(B₂/V₂)`, at every date and state | `ExchangeRates.separate_pools_determinate`, `ExchangeRates.separate_pools_exchange_rate`, `ExchangeRates.exchange_rate_eq_ratio_pv` |
| Cochrane §24.3, p. 527 (Dupor 2000) | a common pool: every `e > 0` is consistent with unique price levels, so the set of equilibrium exchange rates is the positive half-line | `ExchangeRates.common_pool_exchange_rate_free`, `ExchangeRates.common_pool_indeterminate` |

## Links between Chapters 8, 9 and 10 (Links)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §9.2, pp. 263–264; (8.2), p. 240 | the §9.2 economy satisfies the §8.2 nominal flow, and Theorem IT's real debt is the present value (8.2) | `Links.economy_nominalFlow`, `Links.economy_valuation` |
| Cochrane p. 239; §9.2, p. 263; §9.3.2, p. 266 | the transversality field of the §9.2 economy is `PresentValue.TVC`; under perfect foresight `PresentValue.TVC` is the ex post condition | `Links.economy_tvc_iff`, `Links.tvc_perfectForesight_iff` |
| Cochrane §8.1, p. 239; §9.3.2, pp. 266–267 | the rule equilibrium is the perfect-foresight indexed-debt equilibrium; under uncertainty the indexed flow with the rule gives (9.9) state by state | `Links.ruleEquilibrium_iff_indexed`, `Links.indexedFlow_eq_9_9` |
| Cochrane (9.7), p. 265; p. 239 | (9.7) is an injective `s(P)` rule, so `P = P*` | `Links.rule_97_determines` |
| Cochrane p. 239; §§9.5–9.6, pp. 281–286 | the indexed-bond price is the claim price; the peg clears iff `P_t = P*_t`; the first-order condition at the peg holds at every date iff the market price equals the peg | `Links.indexedPrice_eq_claimPrice`, `Links.indexed_peg_iff`, `Links.indexed_peg_foc_iff_market` |
| Cochrane (8.3), p. 246; §9.3.5, p. 271 | `b + B/P = V` has a unique positive `P` iff `b < V`; the two elasticities are reciprocal | `Links.mixed_existsUnique_iff`, `Links.elasticities_reciprocal` |
| Cochrane (8.4), p. 250; (9.22), p. 275 | (9.22) is the one-period-debt case of the §8.4 identities | `Links.valuation_922_of_short_debt`, `Links.valuation_of_short_debt` |
| Cochrane (8.6)–(8.7), p. 254; (9.27), p. 279 | without a haircut the §8.5 bond price and revenue are those of (9.27) | `Links.bondPrice_no_haircut`, `Links.revenue_eq_9_27` |
| Cochrane (10.7), p. 296; §9.6, p. 285 | `1/(1 − β)` is the coupon plus the ex-coupon value `1/r` | `Links.pv_one_eq_one_add_perpetuity` |

## Measure-theoretic expectations: the copied core (ExpectationsMeasure, ExpectationsMeasureIID)

Copied verbatim (namespace renamed) from the `ObservationalEquivalence` project, where it was
built; its docstrings cite Cochrane (2023), Ch. 2. Statements hold almost everywhere unless marked
exact.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2023) Ch. 2, pp. 29–30 (shared core) | a probability space with a filtration; `E_t x = μ[x \| 𝓕_t]` is Mathlib's `condExp`; bounded random variables and processes | `ExpectationsMeasure.MeasExpectationSystem`, `ExpectationsMeasure.MeasExpectationSystem.μ`, `ExpectationsMeasure.MeasExpectationSystem.E`, `ExpectationsMeasure.MeasExpectationSystem.BddRV`, `ExpectationsMeasure.MeasExpectationSystem.BddProc` |
| Ch. 2, pp. 29–30 (shared core) | the expectation axioms a.e.: linearity, constants (exact), monotonicity, the tower property, earlier forecasts known later (exact), adapted variables are their own forecast (exact), measurability and integrability of forecasts, the law of total expectation, pull-out of bounded known factors, bounds pass through `E_t` | `ExpectationsMeasure.MeasExpectationSystem.E_add`, `ExpectationsMeasure.MeasExpectationSystem.E_sub`, `ExpectationsMeasure.MeasExpectationSystem.E_smul`, `ExpectationsMeasure.MeasExpectationSystem.E_const`, `ExpectationsMeasure.MeasExpectationSystem.E_zero`, `ExpectationsMeasure.MeasExpectationSystem.E_mono`, `ExpectationsMeasure.MeasExpectationSystem.E_tower`, `ExpectationsMeasure.MeasExpectationSystem.stronglyMeasurable_E`, `ExpectationsMeasure.MeasExpectationSystem.integrable_E`, `ExpectationsMeasure.MeasExpectationSystem.E_of_stronglyMeasurable`, `ExpectationsMeasure.MeasExpectationSystem.E_of_aestronglyMeasurable`, `ExpectationsMeasure.MeasExpectationSystem.E_known`, `ExpectationsMeasure.MeasExpectationSystem.E_E_self`, `ExpectationsMeasure.MeasExpectationSystem.E_congr`, `ExpectationsMeasure.MeasExpectationSystem.integral_E`, `ExpectationsMeasure.MeasExpectationSystem.E_pullOut`, `ExpectationsMeasure.MeasExpectationSystem.abs_E_le` |
| Ch. 2, p. 29 (shared core) | bounded random variables are integrable and closed under constants, sums, multiples, differences, products, squares and forecasts | `ExpectationsMeasure.MeasExpectationSystem.BddRV.integrable`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.of_stronglyMeasurable`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.const`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.add`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.smul`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.sub`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.mul`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.sq`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.E` |
| (2.13), p. 30; (2.17), p. 35 (shared core) | the news `ΔE_{t+1}x = E_{t+1}x − E_tx` is a martingale difference, orthogonal to bounded date-`t` variables; revisions telescope into news and `x = E_tx + ΔE_{t+1}x` (exact) | `ExpectationsMeasure.MeasExpectationSystem.innov`, `ExpectationsMeasure.MeasExpectationSystem.stronglyMeasurable_innov`, `ExpectationsMeasure.MeasExpectationSystem.E_innov`, `ExpectationsMeasure.MeasExpectationSystem.E_mul_innov`, `ExpectationsMeasure.MeasExpectationSystem.E_sub_E_eq_sum_innov`, `ExpectationsMeasure.MeasExpectationSystem.eq_E_add_innov` |
| Ch. 2, p. 29 (present values; shared core) | `E_t` passes through a dominated series as a genuine `HasSum`; the realised discounted sum and its recursion, bound and measurability | `ExpectationsMeasure.MeasExpectationSystem.E_hasSum`, `ExpectationsMeasure.MeasExpectationSystem.discSum`, `ExpectationsMeasure.MeasExpectationSystem.summable_geom_mul`, `ExpectationsMeasure.MeasExpectationSystem.abs_tsum_geom_mul_le`, `ExpectationsMeasure.MeasExpectationSystem.discSum_succ`, `ExpectationsMeasure.MeasExpectationSystem.discSum_bdd`, `ExpectationsMeasure.MeasExpectationSystem.discSum_rec`, `ExpectationsMeasure.MeasExpectationSystem.aestronglyMeasurable_discSum` |
| Ch. 2, p. 29 (shared core) | `z_t = aE_tz_{t+1} + u_t` for `\|a\| < 1`: the forward solution `E_t∑aᵏu_{t+k} = ∑aᵏE_tu_{t+k}` is adapted, bounded and solves; uniqueness needs no adaptedness | `ExpectationsMeasure.MeasExpectationSystem.Solves`, `ExpectationsMeasure.MeasExpectationSystem.forwardSol`, `ExpectationsMeasure.MeasExpectationSystem.forwardSol_adapted`, `ExpectationsMeasure.MeasExpectationSystem.forwardSol_bdd`, `ExpectationsMeasure.MeasExpectationSystem.forwardSol_solves`, `ExpectationsMeasure.MeasExpectationSystem.forwardSol_hasSum`, `ExpectationsMeasure.MeasExpectationSystem.iterate_homog`, `ExpectationsMeasure.MeasExpectationSystem.forward_unique`, `ExpectationsMeasure.MeasExpectationSystem.existsUnique_forward` |
| Ch. 2, p. 29 (shared core) | for `\|a\| ≥ 1` a genuinely random bounded sunspot sits next to every bounded adapted solution; given genuinely random news, existence and uniqueness for all bounded adapted `u` iff `\|a\| < 1` | `ExpectationsMeasure.MeasExpectationSystem.sunspot`, `ExpectationsMeasure.MeasExpectationSystem.sunspot_succ`, `ExpectationsMeasure.MeasExpectationSystem.sunspot_adapted`, `ExpectationsMeasure.MeasExpectationSystem.sunspot_bdd`, `ExpectationsMeasure.MeasExpectationSystem.sunspot_solves`, `ExpectationsMeasure.MeasExpectationSystem.solves_add`, `ExpectationsMeasure.MeasExpectationSystem.solves_zero`, `ExpectationsMeasure.MeasExpectationSystem.sunspot_not_predictable`, `ExpectationsMeasure.MeasExpectationSystem.not_unique_of_one_le`, `ExpectationsMeasure.MeasExpectationSystem.unique_iff`, `ExpectationsMeasure.MeasExpectationSystem.existsUnique_iff` |
| §2.7, p. 42 (shared core) | AR(1) with martingale-difference, conditionally homoskedastic shocks: `E_tu_{t+j} = ρʲu_t`, `Var_tu_{t+j} = σ²∑_{i<j}ρ^{2i} = σ²(1 − ρ^{2j})/(1 − ρ²)` (Mathlib `condVar`) | `ExpectationsMeasure.MeasExpectationSystem.ar1_E`, `ExpectationsMeasure.MeasExpectationSystem.ar1_E_sq_dev`, `ExpectationsMeasure.MeasExpectationSystem.ar1_condVar`, `ExpectationsMeasure.MeasExpectationSystem.ar1_condVar_closed` |
| Ch. 2, p. 29 (shared core) | bridge to the core: on a finite discrete `Ω` with full support a measure system is an `ExpectationSystem` with the same `E_t` and the pull-out property | `ExpectationsMeasure.MeasExpectationSystem.eq_of_ae_eq`, `ExpectationsMeasure.MeasExpectationSystem.le_of_ae_le`, `ExpectationsMeasure.MeasExpectationSystem.ELin`, `ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem`, `ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_E`, `ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_pullOut` |
| Ch. 2, p. 29 (shared core) | bridge from the core: a finite event tree is a measure system whose `condExp` is the tree's cell average at every state; the round trip returns the tree's own `E` | `ExpectationsMeasure.TreeBridge.trivialFirst`, `ExpectationsMeasure.TreeBridge.sum_prob_condE`, `ExpectationsMeasure.TreeBridge.treeMeasure`, `ExpectationsMeasure.TreeBridge.treeMeasure_singleton`, `ExpectationsMeasure.TreeBridge.treeMeasure_univ`, `ExpectationsMeasure.TreeBridge.treeProb`, `ExpectationsMeasure.TreeBridge.integral_treeProb`, `ExpectationsMeasure.TreeBridge.treeFiltration`, `ExpectationsMeasure.TreeBridge.stronglyMeasurable_condE`, `ExpectationsMeasure.TreeBridge.treeSystem`, `ExpectationsMeasure.TreeBridge.treeSystem_fullSupport`, `ExpectationsMeasure.TreeBridge.treeSystem_E`, `ExpectationsMeasure.TreeBridge.treeSystem_toExpectationSystem_E` |
| Ch. 2, p. 29 (shared core) | the i.i.d. economy on `ℕ → ℝ` under `ν^ℕ` (Mathlib `Measure.infinitePi`), shocks `ε_t(ω) = ω_t`, natural filtration; future shocks independent of date-`t` information, so `E_tf(ε_{t+1}) = ∫f dν` | `ExpectationsMeasureIID.iidProb`, `ExpectationsMeasureIID.iidSystem`, `ExpectationsMeasureIID.shock`, `ExpectationsMeasureIID.measurable_shock`, `ExpectationsMeasureIID.coordSigma`, `ExpectationsMeasureIID.futureSigma`, `ExpectationsMeasureIID.coordSigma_le`, `ExpectationsMeasureIID.futureSigma_le`, `ExpectationsMeasureIID.iIndep_coord`, `ExpectationsMeasureIID.filtration_le_past`, `ExpectationsMeasureIID.indep_future`, `ExpectationsMeasureIID.E_future`, `ExpectationsMeasureIID.measurable_future_fun`, `ExpectationsMeasureIID.integral_shock_fun`, `ExpectationsMeasureIID.E_shock_fun`, `ExpectationsMeasureIID.E_shock`, `ExpectationsMeasureIID.E_shock_sq`, `ExpectationsMeasureIID.shock_ae_bdd` |
| Ch. 2, p. 29 (shared core) | mean-zero shocks with constant conditional variance `σ² > 0`, nondegenerate at every date; every history is null, so the system is not finitely (or countably) supported | `ExpectationsMeasureIID.E_shock_zero`, `ExpectationsMeasureIID.E_shock_sq_eq`, `ExpectationsMeasureIID.condVar_shock`, `ExpectationsMeasureIID.shock_not_ae_E`, `ExpectationsMeasureIID.singleton_lt_one`, `ExpectationsMeasureIID.exists_singleton_le`, `ExpectationsMeasureIID.iid_singleton`, `ExpectationsMeasureIID.iid_countable_null`, `ExpectationsMeasureIID.iid_not_finitely_supported` |
| Ch. 2, p. 29; §2.7, p. 42 (shared core) | determinacy in the i.i.d. economy iff `\|a\| < 1`, with a random sunspot otherwise; the bounded AR(1), its forecasts and conditional variance | `ExpectationsMeasureIID.iid_news`, `ExpectationsMeasureIID.iid_existsUnique_iff`, `ExpectationsMeasureIID.iid_sunspot`, `ExpectationsMeasureIID.ar1`, `ExpectationsMeasureIID.ar1_succ`, `ExpectationsMeasureIID.ar1_adapted`, `ExpectationsMeasureIID.ar1_bdd`, `ExpectationsMeasureIID.iid_ar1_E`, `ExpectationsMeasureIID.iid_ar1_condVar`, `ExpectationsMeasureIID.iid_ar1_condVar_closed` |
| Ch. 2, p. 29; §2.7, p. 42 (shared core) | the fair `±1` coin economy: mean zero, variance one, bounded, and every property above at once | `ExpectationsMeasureIID.coinMeasure`, `ExpectationsMeasureIID.coinMeasure_univ`, `ExpectationsMeasureIID.coin`, `ExpectationsMeasureIID.integral_coin`, `ExpectationsMeasureIID.coin_mean`, `ExpectationsMeasureIID.coin_var`, `ExpectationsMeasureIID.coin_bdd`, `ExpectationsMeasureIID.coin_economy` |

## Shared tools

| Book | Claim | Lean |
| --- | --- | --- |
| Chapters 8–10 throughout | the expectation axioms, pull-out, perfect foresight, adapted and bounded processes, forward series; known variables pass through `E_t` | `ExpectationSystem`, `ExpectationSystem.PullOut`, `ExpectationSystem.Adapted`, `BoundedProc`, `ExpectationSystem.forwardSeries`, `perfectForesight`, `perfectForesight_pullOut`, `ForwardSolution.E_of_known` |
| §8.4, §9.2, §9.4.1 | the coin-flip tree used by `MaturityBuffer.matching_fails_under_uncertainty`, `InflationTarget.zero_debt_sunspot` and `SpreadTarget.printed_9_26_fails_coin` | `ExpectationsFiniteTree.FiniteTree.toExpectationSystem`, `ExpectationsFiniteTree.coinSystem`, `ExpectationsFiniteTree.firstHeads`, `ExpectationsFiniteTree.coinShock`, `ExpectationsFiniteTree.finiteTree_pullOut` |
| shared core, not used by Chapters 8–10 | the forward solution and Schur–Cohn determinacy, carried for the other Cochrane projects | `ForwardSolution.existsUnique_bounded`, `SchurStable`, `schurStable_iff_roots` |
