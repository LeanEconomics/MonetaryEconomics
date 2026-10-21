# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, "An intertemporal model"
(pp. 20–51), and Online Appendix A1.1, "The transversality condition" (pp. 554–556). Each formal
claim is listed with its Lean name, relative to the namespace `Cochrane.IntertemporalModel`. Page
numbers are book pages. The book has no labelled propositions, so rows are keyed by equation
number, figure, section or page; Online Appendix equations are written A1 (1.1)–(1.3). Rows follow
the book section by section, and each heading names the modules that formalise the section:
§2.1 with A1.1, then §§2.2–2.10, then the links among the three formalisation chains, the links
to the Woodford projects, and the shared tools. Every statement holds for an arbitrary
`ExpectationSystem`, so under perfect foresight and under uncertainty, unless the row says
otherwise. Debt is `Bm t = B_{t−1}` in `Environment`, `Valuation` and `EquilibriumFormation`
and `B t = B_t` (with `Bm1 = B_{−1}`) in `FiscalMonetary`, `FlatSupply` and `GeneralLinks`.
Codes E4–E30 are the survey items recorded in [corrections](corrections.md). The shared core
(`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is cited where a row
uses it.

## §2.1 The intertemporal model: environment, (2.1)–(2.5), pp. 21–23 (Environment)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.1), p. 21 | the government flow constraint `M_{t−1} + B_{t−1} = P_ts_t + M_t + Q_tB_t` | `Environment.GovFlow` |
| Cochrane (2.2), p. 21 | the household flow constraint; with `c = y` it is the "mirror image" of (2.1); in general the two differ by the excess demand for goods | `Environment.HhFlow`, `Environment.hhFlow_iff_govFlow`, `Environment.hhFlow_sub_govFlow` |
| Cochrane p. 21 | the household maximises `∑ βᵗu(c_t)` (perfect foresight): feasible and optimal plans; the first-order condition derived variationally | `Environment.HhFeasible`, `Environment.HhOptimal`, `Environment.euler_of_optimal` |
| Cochrane p. 21 | the nominal and real Euler equations; `c_t = y` implies `R = 1/β` | `Environment.EulerNominal`, `Environment.EulerReal`, `Environment.realBondPrice_of_euler`, `Environment.realRate_eq_inv_beta` |
| Cochrane (2.3), p. 22 | `Q_t = 1/(1 + i_t) = βE_t(P_t/P_{t+1})`, from the Euler equation (both directions) and from an optimal plan | `Environment.bondPrice_of_euler`, `Environment.bondPrice_iff_euler`, `Environment.bondPrice_of_optimal` |
| Cochrane p. 21; (2.3), p. 22 | the rate `i_t = 1/Q_t − 1`; `Q_t = 1/(1 + i_t) = (1/R)E_t(P_t/P_{t+1})`; `i > 0` iff `Q < 1`, `i < 0` iff `Q > 1` | `Environment.rate`, `Environment.bondPrice_eq_inv_one_add_rate`, `Environment.inv_one_add_rate_eq`, `Environment.rate_pos_iff`, `Environment.rate_neg_iff` |
| Cochrane p. 22 | with `i_t > 0` money held overnight is strictly dominated; the rate cannot be negative; with `i_t = 0` money and bonds are perfect substitutes | `Environment.money_dominated`, `Environment.bonds_dominated_of_neg_rate`, `Environment.perfect_substitutes` |
| Cochrane (2.4), p. 22 | eliminating money: `B_{t−1} = P_ts_t + Q_tB_t`, with no money held or with `B` standing for `M + B` at a zero rate | `Environment.flow_of_govFlow`, `Environment.govFlow_merge` |
| Cochrane (2.5), p. 22 | `B_{t−1}/P_t = s_t + βB_tE_t(1/P_{t+1})`, i.e. `x_t = s_t + βE_tx_{t+1}` for `x_t = B_{t−1}/P_t`; (2.4) iff (2.5) | `Environment.flow_real_25`, `Environment.flow_real_x`, `Environment.flow_iff_real_x` |
| Cochrane p. 23 | with proportional taxes the real surplus `s_t = τ_ty − x_t` does not depend on the price level | `Environment.propTax_real_surplus`, `Environment.propTax_surplus_indep_price` |

## §2.1 The valuation equation, (2.5)–(2.8), pp. 22–23 (Valuation)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.5), p. 22 | the real flow condition at every date; real debt satisfying it is adapted | `Valuation.FlowX`, `Valuation.adapted_of_flow` |
| Cochrane (2.6), p. 22 | the transversality condition, as printed and as `lim_N β^N E_tx_{t+N} = 0`; the two are equivalent | `Valuation.TVC`, `Valuation.TVCBook`, `Valuation.tvc_iff_tvcBook` |
| Cochrane (2.7), p. 22 | the present value `∑_j β^j E_ts_{t+j}`, the core forward series; absolute summability for signed surpluses | `Valuation.pv`, `Valuation.pv_apply`, `Valuation.AbsSummable`, `Valuation.summable_terms`, `ExpectationSystem.forwardSeries` |
| Cochrane p. 22, "iterate (2.5)" | `x_t = ∑_{j<N} β^j E_ts_{t+j} + β^N E_tx_{t+N}`; flow plus TVC give the series; the forecast of a later present value is the tail | `Valuation.telescope`, `Valuation.hasSum_of_flow_tvc`, `Valuation.hasSum_E_pv` |
| Cochrane (2.5)–(2.7), p. 22 | the present value is known when computed and satisfies the flow and transversality conditions | `Valuation.E_pv_self`, `Valuation.pv_flow`, `Valuation.pv_tvc` |
| Cochrane (2.5)–(2.7), p. 22 | flow (2.5) and TVC (2.6) at every date iff (2.7) at every date, signed surpluses | `Valuation.valuation_iff` |
| Cochrane §2.1, pp. 21–22 | the equilibrium: positive adapted `P`, (2.3), (2.4), (2.6) | `Valuation.IsEqm` |
| Cochrane (2.7), p. 22 | in equilibrium real debt is the present value, `P_t = B_{t−1}/pv_t`, and the present value is positive | `Valuation.eqm_realDebt_eq_pv`, `Valuation.eqm_price_eq`, `Valuation.eqm_pv_pos` |
| Cochrane p. 22, "the price level must adjust so that (2.7) holds" | the candidate `P_t = B_{t−1}/pv_t` and its bond price form an equilibrium, the only one; with a nonpositive present value anywhere there is none | `Valuation.eqmPrice`, `Valuation.eqmBondPrice`, `Valuation.eqm_of_pv_pos`, `Valuation.existsUnique_eqm`, `Valuation.no_eqm_of_pv_nonpos` |
| Cochrane (2.2), (2.8), pp. 21–23 | the household flow in real terms; flow plus TVC iff `B_{t−1}/P_t = ∑β^j E_t(c_{t+j} − y + s_{t+j})` | `Valuation.hh_flow_iff_real`, `Valuation.hh_pv_iff` |
| Cochrane p. 23 | debt worth more than the present value of surpluses makes the household demand `c > y` somewhere | `Valuation.excess_demand_of_gap` |
| Cochrane p. 22, "non-negative debt rules out a negative value" | with `B ≥ 0` the no-Ponzi half holds automatically | `Valuation.noPonzi_of_nonneg_debt` |
| Cochrane p. 22, "household maximization ... imply the transversality condition" (perfect foresight) | an optimal plan with strictly increasing `u` satisfies the TVC; at `c = y` this gives (2.7) | `Valuation.tvc_of_optimal`, `Valuation.valuation_of_optimal` |
| Cochrane p. 22, "the consumer can raise consumption ... lower this terminal value" | for any `ExpectationSystem`, a pathwise bubble can be consumed: the deviation is feasible and lowers the terminal term by exactly `δ` | `Valuation.bubble_deviation` |

## §2.1 Household optimisation under uncertainty, pp. 21–22 (Valuation)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 21, "maximizes `E∑βᵗu(c_t)`" | state-contingent feasible plans, expected utility `∑_t βᵗE_0u(c_t)`, optimal plans | `Valuation.SFeasible`, `Valuation.expUtil`, `Valuation.SOptimal` |
| Cochrane p. 21 | every state has positive probability (`Faithful`); information stops growing (`InfoStable`); both hold for perfect foresight and every finite tree | `Valuation.Faithful`, `Valuation.perfectForesight_faithful`, `Valuation.finiteTree_faithful`, `Valuation.InfoStable`, `Valuation.perfectForesight_infoStable`, `Valuation.finiteTree_infoStable` |
| Cochrane pp. 21–22 (finite state space) | `E_t` is a finite weighted sum; limits and derivatives pass through `E_t`; modifying a plan at finitely many dates | `Valuation.E_eq_sum`, `Valuation.E_tendsto`, `Valuation.hasDerivAt_E`, `Valuation.hasSum_of_eq_off_finset` |
| Cochrane p. 21, "the consumer's first-order conditions" | an optimal plan with `B_t > 0` satisfies `Q_tu'(c_t)/P_t = βE_t[u'(c_{t+1})/P_{t+1}]` | `Valuation.euler_of_optimal_stoch` |
| Cochrane (2.6), p. 22 | optimisation implies the TVC at every date and state (finite state space, `InfoStable`) | `Valuation.tvc_of_optimal_stoch` |
| Cochrane (2.7), p. 22 | at `c = y`, optimisation implies (2.7) at every date | `Valuation.valuation_of_optimal_stoch` |

## Online Appendix A1.1 The transversality condition, pp. 554–556 (Valuation)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane A1.1 box, p. 554 | no-Ponzi (`≥ 0`, E27) and optimality (`≤ 0`); the TVC holds iff both do | `Valuation.NoPonzi`, `Valuation.NoOverAccumulation`, `Valuation.tendsto_zero_iff_noPonzi_and_optimal`, `Valuation.tvc_iff_noPonzi_and_optimal` |
| Cochrane A1 (1.1)–(1.2), p. 554 | iterating the household flow, with terminal weight `β^{T+1}`; the printed `R^{−T}` fails (E4) | `Valuation.hh_iterate`, `Valuation.printed_A1_2_false` |
| Cochrane A1 p. 555 | with constant surpluses a too-low price level explodes, `E_tx_{t+n} − s/(1−β) = β^{−n}(x_t − s/(1−β))`; the terminal term tends to `x_t − s/(1−β)`; the TVC holds iff `x_t = s/(1−β)`; the limit of the valuation | `Valuation.const_explodes`, `Valuation.const_terminal_limit`, `Valuation.const_tvc_iff`, `Valuation.const_valuation_limit` |
| Cochrane A1 (1.3), p. 556 | the deviation path in closed form; feasible under (1.3); it improves utility | `Valuation.deviation_closed_form`, `Valuation.deviation_feasible`, `Valuation.deviation_improves` |
| Cochrane A1 p. 556, "the increase `Δc` by which (1.3) holds with equality is the optimal choice" | optimal given a supergradient; optimal for concave increasing `u` | `Valuation.deviation_optimal`, `Valuation.concave_le_tangent`, `Valuation.deriv_nonneg_of_monotone`, `Valuation.deviation_optimal_concave` |
| Cochrane A1 p. 556 | the optimal plan keeps real debt constant (so satisfies the TVC) and is not an equilibrium unless the price level is the equilibrium one | `Valuation.optimal_plan_tvc`, `Valuation.tooLow_not_equilibrium` |

## §2.2–§2.3 Dynamic intuition; equilibrium formation, pp. 23–29 (EquilibriumFormation)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.7), p. 24 | `pv_t = s_t + ∑_{j≥1} β^j E_ts_{t+j}` | `EquilibriumFormation.pv_eq_s_add_fwd` |
| Cochrane (2.9), (2.11), pp. 24, 27 | debt sales raise real revenue `Q_tB_t/P_t = ∑_{j≥1} β^j E_ts_{t+j}`, in every equilibrium | `EquilibriumFormation.realRevenue_hasSum`, `EquilibriumFormation.eqm_realRevenue` |
| Cochrane (2.9), p. 24 | a deficit is financed by debt sales exceeding the maturing debt | `EquilibriumFormation.deficit_financed_by_debt` |
| Cochrane p. 24 | `Q_tB_t = βE_ts_{t+1}` holds in real terms when the debt is retired at `t + 1` (correction) | `EquilibriumFormation.soak_up_retired` |
| Cochrane pp. 24–25 | if the roll-over fails, `B_{t−1}/P_t = s_t`; (2.4) in real form | `EquilibriumFormation.no_rollover`, `EquilibriumFormation.flow_div_iff` |
| Cochrane p. 24 | under a passive surplus rule every positive adapted price level with bounded real debt is an equilibrium | `EquilibriumFormation.passiveSurplus`, `EquilibriumFormation.passive_every_price_eqm` |
| Cochrane pp. 25–26 | with `B_{−1} = 0`, (2.7) at date 0 reads `0 = pv_0`; `P_0` can be replaced by any positive date-0 variable; the price level is not unique | `EquilibriumFormation.no_initial_debt_pv_zero`, `EquilibriumFormation.no_initial_debt_P0_free`, `EquilibriumFormation.no_initial_debt_not_unique` |
| Cochrane (2.10)–(2.11), p. 27 | money is left overnight iff `P_t < B_{t−1}/pv_t`, none iff equality, negative iff `P_t` is above | `EquilibriumFormation.money_overhang_iff`, `EquilibriumFormation.money_zero_iff`, `EquilibriumFormation.money_negative_iff` |
| Cochrane p. 28, display | `B_{t−1}/P_t = s_t + ∑_{j=1}^{T} β^j E_ts_{t+j} + β^{T+1}E_tB_{t+T}/P_{t+T+1}`, and its limit; the printed `β^T` fails (E4) | `EquilibriumFormation.iterate_with_terminal`, `EquilibriumFormation.iterate_with_terminal_limit`, `EquilibriumFormation.printed_p28_false` |
| Cochrane p. 28 | a too-high price level pushes expected debt to `−∞`, ruled out by `B ≥ 0` | `EquilibriumFormation.tooHigh_explodes_down`, `EquilibriumFormation.tooHigh_violates_nonneg_debt` |

## §2.4 Fiscal and monetary policy, (2.12)–(2.15), pp. 29–34 (FiscalMonetary)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.7), p. 22; (2.15), p. 31 | the ex-post sum, the present value `E_t∑β^js_{t+j}`, the ex-dividend value; summability | `FiscalMonetary.epv`, `FiscalMonetary.pv`, `FiscalMonetary.pvEx`, `FiscalMonetary.SurplusSummable`, `FiscalMonetary.surplusSummable_of_zero`, `FiscalMonetary.surplusSummable_of_bounded` |
| Cochrane (2.15), p. 31; (2.26), p. 42 | `∑_{j≥1} = β∑_{j≥0}` shifted; `pvEx_t = βE_tpv_{t+1}`; both are adapted; `pv_t = s_t + pvEx_t`; a positive lower bound passes to `pvEx` | `FiscalMonetary.exsum_eq`, `FiscalMonetary.epv_succ`, `FiscalMonetary.pvEx_eq`, `FiscalMonetary.pv_adapted`, `FiscalMonetary.pvEx_adapted`, `FiscalMonetary.pv_eq_add_pvEx`, `FiscalMonetary.pvEx_ge` |
| Cochrane (2.7), p. 22 | for bounded surpluses, `E_r∑β^js_{t+j} = ∑β^jE_rs_{t+j}` | `FiscalMonetary.E_epv_tsum` |
| Cochrane (2.12)–(2.13), p. 30 | `E_tpv_{t+1}` and the news in `pv_{t+1}` | `FiscalMonetary.E_pv_succ`, `FiscalMonetary.news_pv_succ` |
| Cochrane (2.7), (2.12), (2.3), (2.14), pp. 22–31 | the valuation equation, bond pricing, equilibrium | `FiscalMonetary.Valuation`, `FiscalMonetary.BondPricing`, `FiscalMonetary.Equilibrium` |
| Cochrane p. 22; (2.12), p. 30 | `P_0 = B_{−1}/pv_0`, `P_{t+1} = B_t/pv_{t+1}`; real debt is known at `t` | `FiscalMonetary.price_zero`, `FiscalMonetary.price_succ`, `FiscalMonetary.realDebt_known` |
| Cochrane (2.13), p. 30 | `(B_t/P_t)ΔE_{t+1}(P_t/P_{t+1}) = ΔE_{t+1}∑β^js_{t+1+j}` | `FiscalMonetary.unexpected_inflation`, `FiscalMonetary.unexpected_inflation_eq` |
| Cochrane p. 30, bullet; p. 42 | unexpected inflation is zero iff present-value news is zero; disinflation iff positive news | `FiscalMonetary.no_surprise_iff`, `FiscalMonetary.disinflation_iff` |
| Cochrane p. 30, "you can't expect future unexpected shocks" | the forecast of every later unexpected inflation is zero | `FiscalMonetary.E_unexpected_inflation_zero` |
| Cochrane p. 30, display | `(B_t/P_t)E_t(P_t/P_{t+1}) = E_t∑β^js_{t+1+j}` | `FiscalMonetary.expected_inflation` |
| Cochrane (2.14)–(2.15), p. 31 | `(B_t/P_t)/(1 + i_t) = E_t∑_{j≥1}β^js_{t+j}`; `B_t = (1 + i_t)P_tE_t∑_{j≥1}β^js_{t+j}` | `FiscalMonetary.expected_valuation`, `FiscalMonetary.debt_eq` |
| Cochrane p. 31, unit-elastic demand | real revenue from bond sales depends only on surpluses | `FiscalMonetary.revenue_invariant` |
| Cochrane p. 31 | expected future bond sales do not matter | `FiscalMonetary.future_sales_irrelevant` |
| Cochrane p. 31, bullet | the share split: scaling `B_t` by `λ` leaves `P` up to `t`, scales `P_{t+1}` and `1 + i_t` by `λ`, leaves real revenue | `FiscalMonetary.shareSplit` |
| Cochrane §2.4.3, p. 31 | the target equilibrium path and the debt sold on the flat supply curve | `FiscalMonetary.pegP`, `FiscalMonetary.pegB`, `FiscalMonetary.pegP_succ`, `FiscalMonetary.pegP_pos` |
| Cochrane pp. 31–33, bullets | an interest-rate target, any adapted `i > −1`, has exactly one equilibrium | `FiscalMonetary.peg_equilibrium`, `FiscalMonetary.peg_unique`, `FiscalMonetary.peg_existsUnique` |
| Cochrane pp. 30, 32–33, bullets | the target sets expected inflation `E_t(P_t/P_{t+1}) = 1/(β(1 + i_t))`, whatever the surpluses; fiscal news sets unexpected inflation | `FiscalMonetary.peg_expected_inflation`, `FiscalMonetary.expected_inflation_indep_surplus`, `FiscalMonetary.inflation_decomposition` |
| Cochrane p. 32 | a higher target sells debt in proportion to `1 + i`; `ΔB/B = Δi/(1 + i)`, equal to `Δi` only at `i = 0`; 5% to 6% is `1/105` (E7) | `FiscalMonetary.debt_ratio_of_rate`, `FiscalMonetary.debt_growth_of_rate`, `FiscalMonetary.rate_change_eq_debt_growth_iff`, `FiscalMonetary.printed_one_percent_fails` |
| Cochrane p. 32, "fix the real rate ... infinite demands" | the real bond price is forced to `β`; a real-rate peg has no equilibrium; with linear utility the gain is unbounded | `FiscalMonetary.real_rate_forced`, `FiscalMonetary.no_eqm_real_rate_peg`, `FiscalMonetary.real_rate_peg_unbounded` |
| Cochrane p. 33, the classic doctrine | scaling a solution preserves every condition except the initial valuation equation, which pins the scale | `FiscalMonetary.scaled_all_but_initial`, `FiscalMonetary.scaled_not_initial` |
| Cochrane p. 33, perfect foresight | monetary policy gives a family `P_{t+1} = β(1 + i_t)P_t`; fiscal policy picks `P_0 = B_{−1}/pv_0` | `FiscalMonetary.pf_pricing_iff`, `FiscalMonetary.pf_price_formula`, `FiscalMonetary.pf_family` |
| Cochrane p. 33 | the Treasury/central-bank split is irrelevant when reserves fund the central bank's bonds | `FiscalMonetary.consolidation_irrelevant` |

## §2.5 The fiscal theory of monetary policy, (2.16)–(2.19), pp. 34–39 (LinearFTMP)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.16), p. 35 | the exact Fisher equation `1/(1 + i_t) = βE_t(P_t/P_{t+1})`, in logs; exact under perfect foresight | `LinearFTMP.FisherExact`, `LinearFTMP.fisher_log_form`, `LinearFTMP.fisher_pf_exact` |
| Cochrane (2.16), p. 35 | `i_t ≈ r + E_tπ_{t+1}` as the derivative at the steady state `r = −log β` | `LinearFTMP.hasDerivAt_E_exp`, `LinearFTMP.fisher_deriv`, `LinearFTMP.fisher_deriv_value` |
| Cochrane (2.17), p. 35 | the exact `V_tΔE_{t+1}(P_t/P_{t+1}) = ΔE_{t+1}PV_{t+1}`, `V_t = B_t/P_t` (E10) | `LinearFTMP.unexpected_inflation_exact` |
| Cochrane (2.17), p. 35 | the fiscal shock `ε_{Σs,t+1} = ∑β^jΔE_{t+1}s̃_{t+1+j}`, a genuine series and a shock | `LinearFTMP.pvNews`, `LinearFTMP.E_forwardSeries_succ`, `LinearFTMP.innov_forwardSeries`, `LinearFTMP.IsShock`, `LinearFTMP.pvNews_isShock` |
| Cochrane (2.17), p. 35 | the linear (2.17) is the first derivative of the exact one | `LinearFTMP.linear_217` |
| Cochrane (2.18), p. 35 | `(B_t/P_t)/(1 + i_t) = E_t∑_{j≥1}β^js_{t+j}`, exactly | `LinearFTMP.debt_218` |
| Cochrane (2.16)–(2.19), pp. 35–36 | the model holds iff `π_{t+1} = i_t − ε_{Σs,t+1}`; the solution is adapted and, given `π_0`, unique for every rate path | `LinearFTMP.PegModel`, `LinearFTMP.pegModel_iff`, `LinearFTMP.pegSol`, `LinearFTMP.pegSol_adapted`, `LinearFTMP.peg_existsUnique` |
| Cochrane pp. 33, 37 | stable under a peg: bounded inputs give bounded inflation | `LinearFTMP.pegSol_bounded` |
| Cochrane Fig. 2.1, p. 36 | impact `ΔE_{t+1}π_{t+1} = −ε_{Σs,t+1}`; later inflation follows the rate one period later; the rate and fiscal panels | `LinearFTMP.innov_shock_later`, `LinearFTMP.irf_peg_impact`, `LinearFTMP.irf_peg_later`, `LinearFTMP.fig21_rate`, `LinearFTMP.fig21_fiscal` |
| Cochrane p. 36 | `E_sπ_{t+1} = E_si_t`; the response is the same if announced; no effect on the announcement date | `LinearFTMP.expected_inflation_ahead`, `LinearFTMP.announcement_invariant`, `LinearFTMP.no_announcement_effect` |
| Cochrane p. 37 | the long-run Fisher relation | `LinearFTMP.long_run_fisher` |
| Cochrane Fig. 2.1, pp. 36–37, "expected" fiscal shock | inflation happens when the news arrives, whatever the timing of the surpluses | `LinearFTMP.innov_of_news`, `LinearFTMP.pvNews_of_news`, `LinearFTMP.fig21_expected_fiscal` |
| Cochrane §2.5.1, p. 38 | price-level targets: `p_t = E_tp*_{t+1} − i_t`; a higher rate lowers the price level; the fiscal contraction; "at a loggerhead" | `LinearFTMP.pTarget_price`, `LinearFTMP.pTarget_rate_lowers_price`, `LinearFTMP.pTarget_fiscal_contraction`, `LinearFTMP.loggerhead` |
| Cochrane p. 38 | `ΔE_tπ_t = ΔE_tp_t`; the printed `− p_{t−1}` fails (E6) | `LinearFTMP.innov_pi_eq_innov_p`, `LinearFTMP.printed_E6_false` |
| Cochrane p. 39 | passive fiscal policy accommodates every inflation innovation | `LinearFTMP.passiveShock`, `LinearFTMP.passive_valuation_holds`, `LinearFTMP.passive_any_innovation` |

## §2.6 Interest-rate rules, (2.20)–(2.25), Fig. 2.2, pp. 39–42 (LinearFTMP)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 40 | a shock's innovation on arrival is the shock | `LinearFTMP.innov_shock` |
| Cochrane (2.20)–(2.24), p. 40 | the rule model; the disturbance (2.23); eliminating the rate gives (2.24) | `LinearFTMP.RuleModel`, `LinearFTMP.Disturbance`, `LinearFTMP.Eq224`, `LinearFTMP.ruleModel_iff` |
| Cochrane (2.25), p. 40 | (2.24) iff `π_{t+1} = θπ_t + u_t − ε_{Σs,t+1}`; the solution is adapted | `LinearFTMP.eq224_iff`, `LinearFTMP.ruleSol`, `LinearFTMP.ruleSol_adapted` |
| Cochrane p. 40 | exactly one equilibrium for every `θ`: no Taylor principle | `LinearFTMP.rule_existsUnique` |
| Cochrane p. 40 | feeding the equilibrium rate into (2.19) gives the same result | `LinearFTMP.rule_eq_peg` |
| Cochrane §2.6 (E30) | bounded for `\|θ\| < 1`; unbounded for `\|θ\| > 1` | `LinearFTMP.ruleSol_bounded`, `LinearFTMP.ruleSol_unbounded` |
| Cochrane Fig. 2.2, pp. 40–41 | `c_j = (θ^j − η^j)/(θ − η)`; responses of `u`, `π` and `i` | `LinearFTMP.conv`, `LinearFTMP.conv_eq`, `LinearFTMP.irf_disturbance`, `LinearFTMP.irf_rule`, `LinearFTMP.irf_rule_rate` |
| Cochrane Fig. 2.2, p. 41 | monetary panel `c_j`; fiscal panel `π_t = θ^{t−1}`, `i_t = θ^t` | `LinearFTMP.fig22_monetary`, `LinearFTMP.fig22_fiscal` |
| Cochrane p. 41 | fiscal policy alone sets impact inflation; a one-time price jump; the price level can return | `LinearFTMP.fiscal_sets_impact`, `LinearFTMP.one_time_price_jump`, `LinearFTMP.price_level_returns` |
| Cochrane Fig. 2.2, p. 40, "hump-shaped" | for `0 < η < θ < 1` the response is unimodal; at `θ = 0.8`, `η = 0.7` the peak is `π_5 = 1.695` | `LinearFTMP.hump_step`, `LinearFTMP.hump_up`, `LinearFTMP.hump_down`, `LinearFTMP.hump_exists`, `LinearFTMP.fig22_peak` |

## §2.7 Fiscal policy and debt, (2.26)–(2.27), pp. 42–44 (FiscalMonetary)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.4), (2.26), pp. 22, 42 | `B_t/P_{t+1} = s_{t+1} + (B_{t+1}/P_{t+1})/(1 + i_{t+1}) = s_{t+1} + E_{t+1}∑_{j≥1}`, at later dates and at date 0; the nominal flow | `FiscalMonetary.eq_2_26`, `FiscalMonetary.eq_2_26_zero`, `FiscalMonetary.flow_nominal` |
| Cochrane (2.27), p. 42 | the innovation form of the flow condition | `FiscalMonetary.eq_2_27` |
| Cochrane p. 42 | the equity issue: same rate, more revenue; it finances a deficit with no unexpected inflation | `FiscalMonetary.equityIssue`, `FiscalMonetary.equityIssue_finances_deficit` |
| Cochrane p. 42 | a credible reform with deficits can disinflate | `FiscalMonetary.reform_with_deficits` |
| Cochrane p. 43 | present-value news is the discounted sum of surplus news; the s-shaped moving average | `FiscalMonetary.news_epv_tsum`, `FiscalMonetary.sShape_seq`, `FiscalMonetary.sShape` |
| Cochrane p. 43, AR(1) | news `η^jε`; present-value news `ε/(1 − βη)`; value-of-debt news `βη/(1 − βη)ε`, which falls with a deficit; the news exceeds the deficit | `FiscalMonetary.ar1_news`, `FiscalMonetary.ar1_pv_news`, `FiscalMonetary.ar1_value_news`, `FiscalMonetary.ar1_value_falls`, `FiscalMonetary.ar1_news_exceeds_deficit` |
| Cochrane p. 43 | `(B_t/P_t)ΔE_{t+1}(P_t/P_{t+1}) = ε/(1 − βη)`; the printed formula without `B_t/P_t` fails (E5) | `FiscalMonetary.ar1_unexpected_inflation`, `FiscalMonetary.ar1_printed_fails` |

## §2.8 The central bank and the Treasury, pp. 44–47 (FiscalMonetary)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §2.8, p. 44 | consolidation: only debt held by the public matters | `FiscalMonetary.consolidation_irrelevant` |
| Cochrane §2.8 | a split versus a secondary offering | `FiscalMonetary.shareSplit`, `FiscalMonetary.equityIssue` |

## §2.9 The flat supply curve, (2.28), pp. 47–49 (FlatSupply)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.28), p. 48 | the flow condition holds in equilibrium (cited as "(2.15)", E9) | `FlatSupply.eq_2_28`, `FlatSupply.eq_2_28_zero` |
| Cochrane (2.28), p. 48 | the Treasury rule `B_t = (B_{t−1} − P_ts_t)/Q_t`, in equilibrium | `FlatSupply.treasury_rule_iff`, `FlatSupply.treasury_rule_of_equilibrium`, `FlatSupply.treasury_rule_of_equilibrium_zero` |
| Cochrane p. 31; p. 48 | the revenue does not depend on the bond price; one quantity meets the unit-elastic demand | `FlatSupply.flat_supply_revenue`, `FlatSupply.flat_supply_meets_demand` |
| Cochrane p. 48 | the face value rises with `1 + i`; a 1% lower bond price needs `1/99` more face value, not 1% (E7) | `FlatSupply.treasury_debt_ratio`, `FlatSupply.one_percent_price_fall`, `FlatSupply.one_percent_printed_fails` |
| Cochrane p. 48 | the two-step process reproduces the target equilibrium | `FlatSupply.twoStep`, `FlatSupply.twoStep_eq_pegP`, `FlatSupply.twoStep_debt_eq_pegB`, `FlatSupply.twoStep_equilibrium` |

## §2.10 Fiscal stimulus, pp. 49–51 (FiscalMonetary)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 50 | (2.13) and the expected-valuation equation restated | `FiscalMonetary.unexpected_inflation`, `FiscalMonetary.expected_valuation` |
| Cochrane p. 50, "borrow ... spend ... repay ... no effect at all" | no jump in `P_{t+1}` when the present value is unchanged; neutral under perfect foresight | `FiscalMonetary.stimulus_no_jump`, `FiscalMonetary.pf_stimulus_neutral` |
| Cochrane p. 50, corrected | under uncertainty `P_{t+1}` is unchanged iff the rearrangement or the other fiscal news is zero; unexpected inflation is rescaled by real debt; a known addition leaves the news | `FiscalMonetary.stimulus_price_iff`, `FiscalMonetary.stimulus_unexpected_inflation`, `FiscalMonetary.news_pv_add_known` |
| Cochrane p. 50, example economy | the coin-flip economy: the first-coin indicator, baseline and stimulus surpluses, their values, news and equilibria | `FiscalMonetary.CoinExample.fh`, `FiscalMonetary.CoinExample.fh_nonneg`, `FiscalMonetary.CoinExample.coin_E_first`, `FiscalMonetary.CoinExample.coin_E_zero`, `FiscalMonetary.CoinExample.sB`, `FiscalMonetary.CoinExample.sS`, `FiscalMonetary.CoinExample.epv_tail`, `FiscalMonetary.CoinExample.sB_bounded`, `FiscalMonetary.CoinExample.sS_bounded`, `FiscalMonetary.CoinExample.epv_sB_succ`, `FiscalMonetary.CoinExample.epv_sS_add_two`, `FiscalMonetary.CoinExample.epv_sS_one`, `FiscalMonetary.CoinExample.pv_zero_eq`, `FiscalMonetary.CoinExample.pv_sB_succ`, `FiscalMonetary.CoinExample.pv_sB_one`, `FiscalMonetary.CoinExample.pv_sS_add_two`, `FiscalMonetary.CoinExample.pv_sS_one`, `FiscalMonetary.CoinExample.pv_sB_pos`, `FiscalMonetary.CoinExample.pv_sS_pos`, `FiscalMonetary.CoinExample.pvEx_sB_pos`, `FiscalMonetary.CoinExample.pvEx_sS_pos`, `FiscalMonetary.CoinExample.news_sB`, `FiscalMonetary.CoinExample.news_sB_ne`, `FiscalMonetary.CoinExample.coin_pullOut`, `FiscalMonetary.CoinExample.eqm_sB`, `FiscalMonetary.CoinExample.eqm_sS`, `ExpectationsFiniteTree.coinSystem` |
| Cochrane p. 50, counterexample | the stimulus leaves `pv_0`, `P_0` and expected inflation but changes `P_1` in every state; (2.13) gives nonzero unexpected inflation | `FiscalMonetary.CoinExample.stimulus_not_neutral`, `FiscalMonetary.CoinExample.coin_unexpected_inflation_ne` |

## Links among the three formalisation chains (GeneralLinks)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.7), p. 22 | `E_t∑β^js_{t+j} = ∑β^jE_ts_{t+j}` under monotone convergence and ex-post absolute summability, or for bounded surpluses | `GeneralLinks.fm_pv_eq_pv`, `GeneralLinks.fm_pv_eq_pv_of_bounded` |
| Cochrane §2.1, p. 21, timing | maturing debt from `B_{−1}` and the debt sold | `GeneralLinks.debtPath` |
| Cochrane §§2.1–2.4, pp. 21–33 | the valuation-equation equilibrium is the flow-plus-TVC equilibrium with `Q = 1/(1 + i)`; its price level is `B_{t−1}/pv_t` | `GeneralLinks.equilibrium_iff_isEqm`, `GeneralLinks.equilibrium_price_eq_eqmPrice` |
| Cochrane pp. 31–33 | a target selects exactly one derived equilibrium | `GeneralLinks.peg_existsUnique_isEqm` |
| Cochrane (2.11), (2.14)–(2.15), pp. 27, 31 | real revenue is the series of (2.11) | `GeneralLinks.equilibrium_realRevenue` |
| Cochrane §2.9, p. 48 | the two-step debt path is the maturing-debt path | `GeneralLinks.twoStep_eq_debtPath` |
| Cochrane (2.3), (2.16), pp. 22, 35 | bond pricing is the exact Fisher equation; every derived equilibrium satisfies it, also in logs | `GeneralLinks.bondPricing_iff_fisherExact`, `GeneralLinks.isEqm_fisherExact`, `GeneralLinks.isEqm_fisher_log` |
| Cochrane pp. 22, 33 | `Links.PegEqm` with `FiscalMonetary.pv` is `FiscalMonetary.Equilibrium`; the two peg constructions coincide | `GeneralLinks.equilibrium_iff_pegEqm`, `GeneralLinks.ftplPrice_eq_pegP`, `GeneralLinks.ftplDebt_eq_pegB` |
| Cochrane pp. 35, 43; (2.13), (2.17), (2.18) | the ex-post fiscal news is `ε_{Σs}`; every equilibrium satisfies the exact (2.17) and (2.18) | `GeneralLinks.innov_epv_eq_pvNews`, `GeneralLinks.equilibrium_pvNews`, `GeneralLinks.equilibrium_debt_218` |

## Links to the Woodford projects (Links)

| Book | Claim | Lean |
| --- | --- | --- |
| Woodford (2003) (1.21), p. 71 (restated from the Woodford Chapter 2 project) vs Cochrane (2.3), p. 22 | the exact Fisher equation; Cochrane's (2.3) is (1.21) with `u_c ≡ 1` | `Links.FisherExactW`, `Links.fisher_iff_W` |
| Woodford (2003) Prop. 2.5, p. 87; §A.6, p. 639 (restated from the Woodford Chapter 2 project) | sunspot price paths solve the Fisher equation under a peg; distinct sunspots give distinct paths; uncountably many in the coin-flip economy | `Links.Kexp`, `Links.grossInfl`, `Links.sunspotPrice`, `Links.Kexp_ge`, `Links.grossInfl_pos`, `Links.sunspotPrice_pos`, `Links.sunspot_fisher`, `Links.sunspotPrice_injective`, `Links.prop_2_5_uncountable` |
| Cochrane pp. 22, 31–33 | the peg equilibrium; debt follows from the target; the candidate path | `Links.PegEqm`, `Links.pegEqm_debt`, `Links.ftplPrice`, `Links.ftplDebt` |
| Cochrane p. 33 vs Woodford Prop. 2.5 | exactly one equilibrium for every adapted peg; in the coin-flip economy one path inside Woodford's uncountable set | `Links.peg_ftpl_existsUnique`, `Links.pv_const`, `Links.peg_contrast` |
| Woodford (2003) (2.6) and Prop. 2.6, p. 91; App. A, pp. 636–637 (restated from the Woodford Chapter 2 project) | (2.6) is a forward equation; bounded solutions are unique iff `\|φ_π\| > 1`; the sunspot family | `Links.Eq26`, `Links.eq26_iff_solves`, `Links.prop_2_6_iff`, `Links.sunspotInfl`, `Links.sunspotInfl_solves`, `Links.sunspotInfl_bounded`, `ForwardSolution.existsUnique_bounded` |
| Cochrane (2.24), p. 40 vs Woodford (2.6), Prop. 2.6 | (2.24) is (2.6) with `φ_π = θ`; every equilibrium solves it; for `\|θ\| ≤ 1` Woodford's criterion fails but the equilibrium is unique; in the coin-flip economy uncountably many bounded solutions against one | `Links.eq26_iff_224`, `Links.rule_solves_eq26`, `Links.taylor_contrast`, `Links.taylor_contrast_coin` |
| Woodford (2003) p. 66; (4.2), p. 124 (restated from the Woodford Chapter 2 project) | the discount factor; under a Ricardian rule `Q_{t,t+n}W_{t+n} = (1 − α)ⁿW_t` and the TVC holds along every path | `Links.discount`, `Links.ricardian_step`, `Links.ricardian_discounted`, `Links.ricardian_tvc` |
| Cochrane (2.5), p. 22; A1 (1.1), p. 554 | the perfect-foresight telescope | `Links.pv_telescope` |
| Cochrane p. 39 vs Woodford (4.2) | under a passive rule the valuation equation holds at every price level | `Links.passive_any_price` |
| Cochrane (2.5)–(2.7), p. 22; A1 p. 555 | with given surpluses, flow plus TVC pin real debt; any other value violates the TVC | `Links.active_unique_value`, `Links.active_tvc_fails` |
| Woodford (2003) (4.1), p. 311 (restated from the Woodford Chapter 4 project) vs Cochrane (2.4), p. 22 | Woodford's budget is Cochrane's flow with `B_t = (1 + i_t)D_t`; `b_t = V_t = B_t/P_t` | `Links.Budget`, `Links.timing_link`, `Links.timing_real` |

## Shared tools

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 30 (`ΔE_{t+1} = E_{t+1} − E_t`) | innovations and their algebra; "you can't expect future unexpected shocks"; a known factor comes out; forecast plus innovation | `ExpectationTools.innov`, `ExpectationTools.innov_add`, `ExpectationTools.innov_sub`, `ExpectationTools.innov_smul`, `ExpectationTools.innov_neg`, `ExpectationTools.innov_const`, `ExpectationTools.innov_of_known`, `ExpectationTools.E_innov_zero`, `ExpectationTools.E_innov_zero_of_le`, `ExpectationTools.innov_known_next`, `ExpectationTools.innov_E_succ`, `ExpectationTools.innov_mul_known`, `ExpectationTools.eq_E_add_innov` |
| Cochrane pp. 22, 30 | under pull-out, products, reciprocals and quotients of date-`t` variables are known; so is `1 + i` | `ExpectationTools.E_mul_known`, `ExpectationTools.E_inv_known`, `ExpectationTools.E_div_known`, `ExpectationTools.E_one_add_known` |
| Cochrane p. 22 | functions of known variables are known: the hypothesis, its two instances, quotients | `ExpectationTools.FunctionsKnown`, `ExpectationTools.perfectForesight_functionsKnown`, `ExpectationTools.finiteTree_functionsKnown`, `ExpectationTools.known_div` |
| Woodford (2003) §A.6, p. 639 (restated), used for Cochrane pp. 22, 33 | the closure property, its instances; it implies `FunctionsKnown` | `ExpectationTools.Closed`, `ExpectationTools.perfectForesight_closed`, `ExpectationTools.finiteTree_closed`, `ExpectationTools.functionsKnown_of_closed` |
| Cochrane p. 22 (restated from the Woodford Chapter 2 project) | conditional monotone convergence and its instances | `ExpectationTools.MonotoneConvergence`, `ExpectationTools.perfectForesight_monotoneConvergence`, `ExpectationTools.finiteTree_monotoneConvergence` |
| Cochrane pp. 22, 31, 35 | constant lower bounds pass through `E_t`; `E_t` of a nonnegative variable; `\|E_tx\| ≤ E_t\|x\|`; discounted forecasts of bounded surpluses are summable | `ExpectationTools.const_le_E`, `ExpectationTools.E_nonneg`, `ExpectationTools.abs_E_le_E_abs`, `ExpectationTools.summable_E_shift` |
| Chapter 2 throughout | the expectation axioms, pull-out, perfect foresight, bounded processes; finite event trees and the coin-flip tree; known variables; the forward series and `E_t` of a series | `ExpectationSystem`, `ExpectationSystem.PullOut`, `perfectForesight`, `perfectForesight_pullOut`, `BoundedProc`, `ExpectationsFiniteTree.FiniteTree.toExpectationSystem`, `ExpectationsFiniteTree.finiteTree_pullOut`, `ExpectationsFiniteTree.coinSystem`, `ExpectationsFiniteTree.coinShock`, `ForwardSolution.E_of_known`, `ExpectationSystem.forwardSeries`, `ExpectationSystem.E_tsum`, `ExpectationSystem.ar1_iterate` |
| shared core, not used by Chapter 2 | Schur–Cohn determinacy, carried for the later Cochrane projects | `SchurStable`, `schurStable_iff_roots` |
