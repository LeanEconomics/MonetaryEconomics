# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, "An intertemporal model"
(pp. 20–51), and Online Appendix A1.1, "The transversality condition" (pp. 554–556). Each formal
claim is listed with its Lean name, relative to the namespace `Cochrane.IntertemporalModel`. Page
numbers are book pages. The book has no labelled propositions, so rows are keyed by equation
number, figure, section or page; Online Appendix equations are written A1 (1.1)–(1.3). Rows follow
the book section by section, and each heading names the modules that formalise the section:
§2.1 with A1.1 (first for an `ExpectationSystem`, then on a genuine probability space), then
§§2.2–2.6, then the family of exact equilibria whose derivative is the linear model and the
equilibrium results on a genuine probability space (with and without their explicit hypotheses,
and the fiscal corollaries, targets and impulse responses), then §§2.7–2.10, then the links among the
three formalisation chains, the positivity of the bond price, the links to the Woodford
projects (for an `ExpectationSystem` and on a probability space), the measure-theoretic core
and the shared tools. Every statement holds for an arbitrary
`ExpectationSystem`, so under perfect foresight and under uncertainty, unless the row says
otherwise. The exceptions are the modules `HouseholdMeasure` and `HouseholdMeasureTVC`, which
solve the household problem on a probability space with Mathlib's conditional expectation and
information that may grow forever (statements hold almost surely), the modules `TidyR5Meas`,
`TidyR5MeasLinear`, `TidyR5MeasFamily` and `TidyR5MeasFamilyRule`, which restate the
equilibrium, targets, the linear model and the family of exact equilibria there, the modules
`TidyR6MeasHyp`, `TidyR6MeasFamilyVersion`, `TidyR6MeasFiscal`, `TidyR6MeasLinearIRF`,
`TidyR6MeasLinks`, `TidyR6MeasL1`, `TidyR6MeasSigned`, `TidyR6MeasFamilySharp`,
`TidyR6MeasRestate` and `TidyR6MeasZero`, which remove those results' explicit hypotheses and
restate the rest of the chapter and the Woodford contrasts there, and the
measure-theoretic core
`ExpectationsMeasure`, `ExpectationsMeasureIID` they build on. Debt is `Bm t = B_{t−1}` in `Environment`, `Valuation` and `EquilibriumFormation`
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

## §2.1 The household problem on a genuine probability space, pp. 21–22 (HouseholdMeasure)

Statements hold almost surely on a probability space with a filtration; information may grow
forever.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.2), p. 21, "maximizes `E∑βᵗu(c_t)`" | feasible plans (adapted consumption, bonds known when bought, the flow constraint almost surely, `B ≥ 0`); absolutely convergent expected utility; the genuine integral `E∑βⁿu(c_n)`; optimal plans | `HouseholdMeasure.Feasible`, `HouseholdMeasure.Admissible`, `HouseholdMeasure.expUtil`, `HouseholdMeasure.Optimal` |
| Cochrane p. 21 | admissible plans: the utility series converges almost surely, each term and the sum are integrable; a change at finitely many dates changes expected utility by the integrals of the changes | `HouseholdMeasure.Admissible.summable`, `HouseholdMeasure.Admissible.integrable`, `HouseholdMeasure.Admissible.integrable_sum`, `HouseholdMeasure.admissible_modify`, `HouseholdMeasure.aestronglyMeasurable_tsum` |
| Cochrane p. 21 | essentially bounded variables and their algebra; continuous functions of them; `∫zX = ∫zE_tX` for bounded known `z` | `HouseholdMeasure.BddAt`, `HouseholdMeasure.BddAt.mul`, `HouseholdMeasure.BddAt.add`, `HouseholdMeasure.BddAt.neg`, `HouseholdMeasure.BddAt.const`, `HouseholdMeasure.BddAt.comp`, `HouseholdMeasure.BddAt.E`, `HouseholdMeasure.BddAt.integrable`, `HouseholdMeasure.BddAt.exists_pos`, `HouseholdMeasure.integrable_comp_of_bdd`, `HouseholdMeasure.exists_abs_le_of_continuous`, `HouseholdMeasure.integral_mul_E` |
| Cochrane p. 21, "the consumer's first-order conditions" | differentiation of expected utility under the integral sign; a one-sided derivative of a function that does not rise is nonpositive | `HouseholdMeasure.hasDerivAt_integral_comp`, `HouseholdMeasure.deriv_nonpos_of_le` |
| Cochrane (2.2), p. 21 | the bond deviation (sell `εz` bonds at `t`, consume the proceeds, repay at `t + 1`) is feasible | `HouseholdMeasure.devC`, `HouseholdMeasure.devB`, `HouseholdMeasure.dev_feasible` |
| Cochrane p. 21 | the per-date regularity; the Euler gap `Q_tu'(c_t)/P_t − βE_t[u'(c_{t+1})/P_{t+1}]` is known at `t` and bounded; the marginal utility of a dollar at `t + 1` is bounded and integrable | `HouseholdMeasure.EulerRegular`, `HouseholdMeasure.eulerGap`, `HouseholdMeasure.eulerGap_stronglyMeasurable`, `HouseholdMeasure.eulerGap_bdd`, `HouseholdMeasure.margUtil_bdd`, `HouseholdMeasure.margUtil_integrable` |
| Cochrane p. 21, "the consumer's first-order conditions" | the variational inequality along every bounded `𝓕_t`-measurable deviation; the Euler inequality `βE_t[u'(c_{t+1})/P_{t+1}] ≤ Q_tu'(c_t)/P_t` almost surely at every date; equality almost surely on `{B_t > 0}`, and everywhere when `B_t > 0` almost surely | `HouseholdMeasure.foc_le`, `HouseholdMeasure.euler_kkt`, `HouseholdMeasure.euler_interior`, `HouseholdMeasure.euler_of_pos` |
| Cochrane (2.3), p. 22 | `E_t` of a positive payoff is positive; a bond price of asset-pricing form is positive; optimisation forces `Q_t > 0` at every date; on `{B_t > 0}` `Q_t = βE_t[u'(c_{t+1})/u'(c_t)·P_t/P_{t+1}]`; `Q_t = βE_t(P_t/P_{t+1})` gives `i_t > −1` | `HouseholdMeasure.E_pos`, `HouseholdMeasure.bondPrice_pos_of_formula`, `HouseholdMeasure.bondPrice_pos`, `HouseholdMeasure.bondPrice_formula`, `HouseholdMeasure.rate_gt_neg_one_of_formula` |

## §2.1 and A1.1 Transversality and the valuation equation on a genuine probability space, pp. 21–22, 554–556 (HouseholdMeasureTVC)

No `Valuation.InfoStable` hypothesis is used: information may grow forever.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane A1 p. 556 (concave utility) | the derivative of a concave function is antitone; `u(c + h) − u(c) ≥ hu'(c + h)`; bounds on utility at convex combinations and shifts | `HouseholdMeasureTVC.deriv_antitone`, `HouseholdMeasureTVC.sub_ge_mul_deriv`, `HouseholdMeasureTVC.abs_comb_le`, `HouseholdMeasureTVC.abs_shift_le` |
| Cochrane p. 22, "the consumer can raise consumption ... lower this terminal value" | the scaling deviation (keep the fraction `1 − θ` of the bonds from `T` on, consume the proceeds) satisfies every flow constraint exactly; the tail of the utility gain | `HouseholdMeasureTVC.kamC`, `HouseholdMeasureTVC.kamB`, `HouseholdMeasureTVC.kam_feasible`, `HouseholdMeasureTVC.tail`, `HouseholdMeasureTVC.hasSum_ite_lt` |
| Cochrane (2.6), p. 22, "Household maximization ... also imply the household transversality condition" | for concave increasing `u`: `β^TE[u'(c_T)Q_TB_T/P_T] → 0`; with the Euler inequality, `β^NE[u'(c_N)B_{N−1}/P_N] → 0`; `E[ZX] = E[ZE_tX]` for nonnegative `Z` known at `t`, by truncation | `HouseholdMeasureTVC.tvc_end_of_optimal`, `HouseholdMeasureTVC.integrable_mul_of_E`, `HouseholdMeasureTVC.tvc_of_kkt`, `HouseholdMeasureTVC.tvc_of_optimal` |
| Cochrane p. 21; A1 p. 556 | sufficiency: for concave `u`, a feasible admissible plan satisfying the Euler equation at every date and the TVC is optimal against every feasible admissible plan | `HouseholdMeasureTVC.tendsto_partial_utilDiff`, `HouseholdMeasureTVC.optimal_of_euler_tvc` |
| Cochrane p. 21 | uniformly bounded consumption gives admissible utility | `HouseholdMeasureTVC.admissible_of_bdd` |
| Cochrane (2.3)–(2.5), p. 22 | at `c = y` with (2.3): `Q_nB_n/P_n = βE_nx_{n+1}` and (2.5) almost surely; iterating (2.5) | `HouseholdMeasureTVC.endDebt_ae`, `HouseholdMeasureTVC.flowX_of_feasible`, `HouseholdMeasureTVC.telescope_ae` |
| Cochrane (2.6)–(2.7), p. 22 | the unconditional TVC gives (2.6) and (2.7) almost surely at every date; at `c = y` optimisation gives both, and `x_t = E_t∑_jβ^js_{t+j}` | `HouseholdMeasureTVC.tvc_valuation_of_unconditional`, `HouseholdMeasureTVC.valuation_of_optimal_eqm` |
| Cochrane pp. 21–22; §2.7, p. 42 | a genuine infinite-state equilibrium: in the i.i.d. economy with `s_t = s̄ + σε_t`, `P_t = B̄/(s̄/(1 − β) + σε_t)` and `Q_t = βE_t(P_t/P_{t+1})`, the endowment plan is optimal, (2.7) holds almost surely, `Q_t > 0`, `i_t > −1`, real debt carries news and every history is null | `HouseholdMeasureTVC.IID.surplus`, `HouseholdMeasureTVC.IID.price`, `HouseholdMeasureTVC.IID.bondPrice`, `HouseholdMeasureTVC.IID.E_affine`, `HouseholdMeasureTVC.IID.iid_equilibrium` |
| Cochrane p. 21 (finite event tree) | on a finite tree almost sure means every state, the measure `E_t` is the core `E_t`, measurability is "known", every variable is bounded and every plan regular, and expected utilities agree | `HouseholdMeasureTVC.Link.forall_of_ae`, `HouseholdMeasureTVC.Link.treeE`, `HouseholdMeasureTVC.Link.sm_iff_known`, `HouseholdMeasureTVC.Link.bddAt_tree`, `HouseholdMeasureTVC.Link.eulerRegular_tree`, `HouseholdMeasureTVC.Link.integral_tsum_tree`, `HouseholdMeasureTVC.Link.core_summable`, `HouseholdMeasureTVC.Link.integral_core_expUtil` |
| Cochrane pp. 21–22 (finite event tree) | core feasibility is measure feasibility; core optimality (pathwise absolutely convergent utility) implies measure optimality; the core Euler inequality, and the equation wherever `B_t > 0` (`Valuation.euler_of_optimal_stoch` needs `B_t > 0` in every state); the core TVC and `x_t = Valuation.pv` in every state without `Valuation.InfoStable` (cf. `Valuation.tvc_of_optimal_stoch`, `Valuation.valuation_of_optimal_stoch`) | `HouseholdMeasureTVC.Link.feasible_iff`, `HouseholdMeasureTVC.Link.optimal_of_core`, `HouseholdMeasureTVC.Link.link_euler`, `HouseholdMeasureTVC.Link.link_tvc_valuation` |

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

## §§2.4–2.6 A smooth family of exact equilibria and its derivative, pp. 29–42 (TidyR5Family, TidyR5FamilyRule)

Surpluses `s_t(ε) = s̄ + εŝ_t` with `ŝ` bounded and adapted, a rate family `i(ε)` with
`i(0) = 1/β − 1`, and shock sizes in the open interval `famDom` (`|ε|M < s̄`). Statements hold for
every `ExpectationSystem` with pull-out (and `FunctionsKnown` for the canonical and rule rates),
state by state.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §2.5, p. 35 | the surplus family, the steady-state value of debt `V = s̄/(1 − β)`, the open domain of shock sizes containing `0` | `TidyR5Family.surpFam`, `TidyR5Family.ssV`, `TidyR5Family.famDom`, `TidyR5Family.famDom_isOpen`, `TidyR5Family.zero_mem_famDom`, `TidyR5Family.famDom_mem_nhds` |
| Cochrane (2.7), p. 22; (2.15), p. 31 | present values of the family are affine in `ε`, bounded, and positive on `famDom` | `TidyR5Family.epv_surpFam`, `TidyR5Family.pv_surpFam`, `TidyR5Family.pvEx_surpFam`, `TidyR5Family.abs_pv_le`, `TidyR5Family.pv_surpFam_ge`, `TidyR5Family.pv_surpFam_pos`, `TidyR5Family.pvEx_surpFam_pos` |
| Cochrane §2.4.3, p. 31; (2.15) | the price level, debt and inflation of the family in closed form, the price recursion, positivity | `TidyR5Family.priceFam`, `TidyR5Family.debtFam`, `TidyR5Family.inflFam`, `TidyR5Family.priceFam_succ`, `TidyR5Family.priceFam_zero`, `TidyR5Family.priceFam_pos` |
| Cochrane pp. 31–35 | for every `ε` in `famDom` the family member is an exact equilibrium and the only one, so any family of equilibria is this one; at `ε = 0` it is the steady state | `TidyR5Family.fam_equilibrium`, `TidyR5Family.fam_unique`, `TidyR5Family.family_unique`, `TidyR5Family.fam_steady` |
| Cochrane pp. 31–35 | price level, debt and inflation are `C^n` in `ε` for every `n` (analytic included) when the rate family is | `TidyR5Family.pv_contDiff`, `TidyR5Family.pvEx_contDiff`, `TidyR5Family.price_contDiffOn`, `TidyR5Family.debt_contDiffOn`, `TidyR5Family.infl_contDiffOn` |
| Cochrane (2.17), p. 35 | the fiscal shock of (2.17) is the news about the present value of `ŝ` scaled by `V`; `π̂_0 = −PV_0(ŝ)/V` | `TidyR5Family.fiscShock`, `TidyR5Family.infl0`, `TidyR5Family.scaled_innov_pv`, `TidyR5Family.fiscShock_isShock`, `TidyR5Family.infl0_known` |
| Cochrane (2.16)–(2.19), pp. 35–36 | the derivative at `ε = 0` of inflation along the family is the solution (2.19) of the linear peg model, its unique adapted solution | `TidyR5Family.infl_hasDerivAt`, `TidyR5Family.fam_linearization` |
| Cochrane (2.16), p. 35 | the canonical rate family `1 + i_t(ε) = β⁻¹exp(εî_t)`: above `−1`, the steady state at `0`, adapted, exact in logs, smooth | `TidyR5Family.rateExp`, `TidyR5Family.rateExp_gt`, `TidyR5Family.rateExp_zero`, `TidyR5Family.rateExp_adapted`, `TidyR5Family.rateExp_log_hasDerivAt`, `TidyR5Family.rateExp_contDiff` |
| Cochrane pp. 31–36 | everything at once for the canonical target, and on every finite event tree | `TidyR5Family.exp_family_linearization`, `TidyR5Family.tree_family_linearization` |
| Cochrane (2.20)–(2.22), p. 40 | the exact rule `log(1 + i_t) = −log β + θπ_t + εu_t`; inflation and the rate of the rule family in closed form, above `−1`, adapted | `TidyR5FamilyRule.logInfl`, `TidyR5FamilyRule.RuleExact`, `TidyR5FamilyRule.ruleInfl`, `TidyR5FamilyRule.ruleRate`, `TidyR5FamilyRule.logInfl_priceFam`, `TidyR5FamilyRule.ruleRate_gt`, `TidyR5FamilyRule.log_one_add_ruleRate`, `TidyR5FamilyRule.ruleInfl_adapted`, `TidyR5FamilyRule.ruleRate_adapted`, `TidyR5FamilyRule.inflFam_eq_ruleInfl` |
| Cochrane §2.6, p. 40 | for every `θ` the rule family is an exact equilibrium satisfying the exact rule, and the only one | `TidyR5FamilyRule.rule_equilibrium`, `TidyR5FamilyRule.rule_exact`, `TidyR5FamilyRule.rule_unique` |
| Cochrane §2.6, p. 40 | inflation, rate, price level and debt of the rule family are `C^n` in `ε` for every `n` | `TidyR5FamilyRule.ruleInfl_contDiffOn`, `TidyR5FamilyRule.ruleRate_contDiffOn`, `TidyR5FamilyRule.rule_price_contDiffOn` |
| Cochrane (2.22), (2.25), p. 40 | the derivatives at `ε = 0` of inflation and the log gross rate are the solution (2.25) and its rate `θπ̂_t + u_t`, for every `θ` | `TidyR5FamilyRule.ruleInfl_hasDerivAt`, `TidyR5FamilyRule.rule_infl_hasDerivAt`, `TidyR5FamilyRule.rule_rate_hasDerivAt` |
| Cochrane §2.6, pp. 39–42 | everything at once for the rule, and on every finite event tree | `TidyR5FamilyRule.rule_family_linearization`, `TidyR5FamilyRule.tree_rule_linearization` |

## §2.1 and §§2.4–2.6 Equilibrium, targets, the linear model and the family on a genuine probability space (TidyR5Meas, TidyR5MeasLinear, TidyR5MeasFamily, TidyR5MeasFamilyRule)

On a `MeasExpectationSystem`: `E_t` is Mathlib's `condExp`, information may grow forever and
statements hold almost surely unless marked otherwise.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.7), p. 22; (2.15), p. 31; (2.26), p. 42 | the ex-dividend present value, known at `t`; bounds; `PV_t = s_t + PVex_t` | `TidyR5Meas.pvExM`, `TidyR5Meas.pvExM_sm`, `TidyR5Meas.pv_bdd`, `TidyR5Meas.pvExM_ge`, `TidyR5Meas.pv_eq_add_pvEx` |
| Cochrane §§2.1–2.4, pp. 21–33 | the valuation-equation equilibrium (no `i > −1` condition) and the derived equilibrium (2.3), (2.4), (2.6), almost surely | `TidyR5Meas.MValuation`, `TidyR5Meas.MBondPricing`, `TidyR5Meas.MEquilibrium`, `TidyR5Meas.MIsEqm` |
| Cochrane (2.3), p. 22 | in every equilibrium with `β > 0` the bond price is positive and `i > −1` almost surely | `TidyR5Meas.mEqm_rate_gt` |
| Cochrane (2.7), (2.12), (2.15), pp. 22, 30, 31 | `P_0 = B_{−1}/PV_0`, `P_{t+1} = B_t/PV_{t+1}`, `B_t = (1 + i_t)P_tPVex_t` | `TidyR5Meas.mPrice_zero`, `TidyR5Meas.mPrice_succ`, `TidyR5Meas.mDebt_eq` |
| Cochrane (2.13), pp. 30–33 | the target sets expected inflation; fiscal news sets unexpected inflation; the decomposition; no surprise iff no news | `TidyR5Meas.mExpected_inflation`, `TidyR5Meas.mUnexpected_inflation`, `TidyR5Meas.mInflation_decomposition`, `TidyR5Meas.mNo_surprise_iff` |
| Cochrane (2.4), (2.26), pp. 22, 42 | the flow condition holds in every equilibrium | `TidyR5Meas.mFlow` |
| Cochrane pp. 31–33 | the target path is adapted and positive, an equilibrium, and every equilibrium with the target equals it almost surely at every date | `TidyR5Meas.mPegP`, `TidyR5Meas.mPegB`, `TidyR5Meas.mPegP_sm`, `TidyR5Meas.mPegB_sm`, `TidyR5Meas.mPegP_pos`, `TidyR5Meas.mPeg_equilibrium`, `TidyR5Meas.mPeg_unique`, `TidyR5Meas.mPeg_existsUnique` |
| Cochrane (2.3)–(2.7), p. 22 | the real value of debt carried out; nominal vs real flow; (2.4) and (2.6) a.s. iff (2.7) a.s., both directions | `TidyR5Meas.endDebt`, `TidyR5Meas.nominal_iff_real`, `TidyR5Meas.mFlowTvc_iff_valuation` |
| Cochrane §§2.1–2.4, pp. 21–33 | the two notions agree with no `i > −1` hypothesis; the derived equilibrium's price level; a target selects exactly one derived equilibrium up to null sets | `TidyR5Meas.mEquilibrium_iff_mIsEqm`, `TidyR5Meas.mIsEqm_price_eq`, `TidyR5Meas.mPeg_existsUnique_mIsEqm` |
| Cochrane (2.16)–(2.19), pp. 35–36 | shocks; the linear peg model almost surely; existence and a.s. uniqueness given `π_0`, for every adapted integrable rate path | `TidyR5MeasLinear.MIsShock`, `TidyR5MeasLinear.MPegModel`, `TidyR5MeasLinear.E_innov_known_sub_shock`, `TidyR5MeasLinear.mPegModel_iff`, `TidyR5MeasLinear.mPeg_linear_existsUnique` |
| Cochrane (2.20)–(2.25), p. 40 | the linear rule model almost surely; existence and a.s. uniqueness for every `θ` | `TidyR5MeasLinear.MRuleModel`, `TidyR5MeasLinear.mRule_iff`, `TidyR5MeasLinear.mRule_linear_existsUnique` |
| Cochrane (2.13), (2.17), pp. 30, 35 | the fiscal shock `ΔE_{t+1}PV_{t+1}` is a shock and is the shock of the exact (2.17) | `TidyR5MeasLinear.mFiscShock`, `TidyR5MeasLinear.mFiscShock_isShock`, `TidyR5MeasLinear.mEquilibrium_fiscShock` |
| Chapter 2 (finite trees) | on a finite tree a.s. equality is equality, and present values, news, adaptedness and the ex-dividend value are the core ones | `TidyR5MeasLinear.Link.eq_of_ae`, `TidyR5MeasLinear.Link.tree_forwardSol`, `TidyR5MeasLinear.Link.tree_innov`, `TidyR5MeasLinear.Link.tree_adapted_iff`, `TidyR5MeasLinear.Link.tree_pvExM` |
| Chapter 2 (finite trees) | on a finite tree the target path, both equilibrium notions (for `β > 0`), shocks, the linear models and the fiscal shock are the core ones | `TidyR5MeasLinear.Link.tree_mPegP`, `TidyR5MeasLinear.Link.tree_mEquilibrium_iff`, `TidyR5MeasLinear.Link.tree_mIsEqm_iff`, `TidyR5MeasLinear.Link.tree_mIsShock_iff`, `TidyR5MeasLinear.Link.tree_mPegModel_iff`, `TidyR5MeasLinear.Link.tree_mRuleModel_iff`, `TidyR5MeasLinear.Link.tree_mFiscShock` |
| Cochrane pp. 31–35 | the family with fixed versions of present values: price level, debt, inflation, the scaled fiscal shock, `π̂_0`; equilibria are invariant under a.s. changes of prices and debt | `TidyR5MeasFamily.mEquilibrium_congr`, `TidyR5MeasFamily.pvAff`, `TidyR5MeasFamily.pvExAff`, `TidyR5MeasFamily.mFamP`, `TidyR5MeasFamily.mFamB`, `TidyR5MeasFamily.mFamInfl`, `TidyR5MeasFamily.mShock`, `TidyR5MeasFamily.mInfl0` |
| Cochrane (2.7), (2.15), pp. 22, 31 | present values of `s(ε)` are affine in `ε` a.s.; bounds and positivity on `famDom` | `TidyR5MeasFamily.discSum_surpFam`, `TidyR5MeasFamily.discSum_integrable`, `TidyR5MeasFamily.forwardSol_surpFam`, `TidyR5MeasFamily.pvExM_surpFam`, `TidyR5MeasFamily.good_ae`, `TidyR5MeasFamily.aff_pos`, `TidyR5MeasFamily.affEx_pos`, `TidyR5MeasFamily.mFamP_pos`, `TidyR5MeasFamily.forwardSol_surpFam_ge` |
| Cochrane (2.3), (2.16), pp. 22, 35 | the canonical rate is adapted (no `FunctionsKnown`) with integrable bond price | `TidyR5MeasFamily.rateExp_sm`, `TidyR5MeasFamily.rateExp_bondPrice_integrable` |
| Cochrane pp. 31–35 | the family is adapted, a.s. the target path, an equilibrium for each `ε`, unique a.s., the steady state at `0` | `TidyR5MeasFamily.mFamP_sm`, `TidyR5MeasFamily.mFamB_sm`, `TidyR5MeasFamily.mFam_ae_mPeg`, `TidyR5MeasFamily.mFam_equilibrium`, `TidyR5MeasFamily.mFam_unique`, `TidyR5MeasFamily.mFam_steady` |
| Cochrane (2.16)–(2.19), pp. 35–36 | a.s. smoothness in `ε`; a.s. the derivative of inflation is the solution (2.19), for any rate family and for the canonical target; the shock and `π̂_0` | `TidyR5MeasFamily.mFam_contDiffOn`, `TidyR5MeasFamily.mFamInfl_hasDerivAt_gen`, `TidyR5MeasFamily.mFamInfl_hasDerivAt`, `TidyR5MeasFamily.mShock_isShock`, `TidyR5MeasFamily.mInfl0_sm_integrable` |
| Cochrane pp. 31–36 | everything at once on a genuine probability space; on a finite tree the family is `TidyR5Family.priceFam` with inflation `TidyR5Family.inflFam` | `TidyR5MeasFamily.meas_family_linearization`, `TidyR5MeasFamily.Link.tree_mFamP`, `TidyR5MeasFamily.Link.tree_mFamInfl` |
| Cochrane (2.20)–(2.22), p. 40 | the rule family on a probability space: inflation and the rate in closed form, the exact rule a.s., above `−1`, adapted | `TidyR5MeasFamilyRule.mRuleInfl`, `TidyR5MeasFamilyRule.mRuleRate`, `TidyR5MeasFamilyRule.MRuleExact`, `TidyR5MeasFamilyRule.mRuleRate_gt`, `TidyR5MeasFamilyRule.log_one_add_mRuleRate`, `TidyR5MeasFamilyRule.mRuleInfl_sm`, `TidyR5MeasFamilyRule.mRuleRate_sm` |
| Cochrane (2.3), p. 22; p. 40 | inflation of the rule family is bounded on `famDom`, so its bond price is integrable | `TidyR5MeasFamilyRule.abs_log_le`, `TidyR5MeasFamilyRule.ruleBound`, `TidyR5MeasFamilyRule.aff_le`, `TidyR5MeasFamilyRule.le_aff`, `TidyR5MeasFamilyRule.mRuleInfl_bound`, `TidyR5MeasFamilyRule.mRuleRate_bondPrice_integrable` |
| Cochrane §2.6, p. 40 | for every `θ` the rule family is an equilibrium satisfying the exact rule a.s., and every such equilibrium equals it a.s.; invariance under a.s. changes of the rate | `TidyR5MeasFamilyRule.mRule_equilibrium`, `TidyR5MeasFamilyRule.mFamInfl_eq`, `TidyR5MeasFamilyRule.mRule_exact`, `TidyR5MeasFamilyRule.mEquilibrium_congr_rate`, `TidyR5MeasFamilyRule.mRule_unique` |
| Cochrane (2.22), (2.25), pp. 39–42 | smoothness; the derivatives at `0` are the solution (2.25) and its rate; everything at once; on a finite tree the rule family is `TidyR5FamilyRule.ruleRate` | `TidyR5MeasFamilyRule.mRule_contDiffOn`, `TidyR5MeasFamilyRule.mRuleInfl_hasDerivAt`, `TidyR5MeasFamilyRule.mRule_rate_hasDerivAt`, `TidyR5MeasFamilyRule.mRule_family_linearization`, `TidyR5MeasFamilyRule.Link.tree_mRuleRate` |

## §2.1 and §2.4 Equilibrium and targets on a genuine probability space without the explicit hypotheses (TidyR6MeasHyp, TidyR6MeasL1, TidyR6MeasSigned, TidyR6MeasZero)

Each hypothesis of `TidyR5Meas` is removed, weakened to its natural form or shown to be needed.
On a `MeasExpectationSystem`, statements hold almost surely unless marked otherwise.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.3), (2.7), (2.12), pp. 22, 30 | in every equilibrium the bond price `1/(1 + i_t)` and real debt are integrable; with positive initial debt `PV_0 > 0`; `PV_{t+1} > 0` iff the debt sold at `t` is positive | `TidyR6MeasHyp.mEqm_bondPrice_integrable`, `TidyR6MeasHyp.mEqm_realDebt_integrable`, `TidyR6MeasHyp.mEqm_pv_zero_pos`, `TidyR6MeasHyp.mEqm_pv_succ_pos_iff` |
| Cochrane (2.3), (2.15), pp. 22, 31 | `P_t/P_{t+1}` is integrable along the target path when the bond price is (conditional monotone convergence); positive present values give positive ex-dividend values; the target path is positive | `TidyR6MeasHyp.integrable_ratio`, `TidyR6MeasHyp.pvExM_pos`, `TidyR6MeasFiscal.pvExM_pos_at`, `TidyR6MeasHyp.mPegP_pos_ae`, `TidyR6MeasHyp.mPegB_pos_ae` |
| Cochrane pp. 31–33 | the target path is an equilibrium with no bound on surpluses and no `β < 1`; every equilibrium with the target equals it; existence and a.s. uniqueness; **an equilibrium with positive debt exists iff the bond price is integrable, `i > −1` a.s. and `PV_t > 0` a.s.** | `TidyR6MeasHyp.mPeg_equilibrium_pos`, `TidyR6MeasHyp.mPeg_unique_pos`, `TidyR6MeasHyp.mPeg_existsUnique_pos`, `TidyR6MeasHyp.mPeg_existsUnique_iff` |
| Cochrane (2.7), p. 22 | the present value is the genuine sum `∑ βᵏ E_t s_{t+k}` for surpluses dominated by summable bounds (growing surpluses allowed) | `TidyR6MeasHyp.forwardSol_hasSum_dom` |
| Cochrane §§2.1–2.4, pp. 21–33 | `MEquilibrium` iff `MIsEqm` plus adapted debt and rate, integrable `P_t/P_{t+1}` and integrable real debt; the adapted version of the rate, equal to it a.s.; a derived equilibrium becomes an `MEquilibrium` with that version | `TidyR6MeasHyp.mEquilibrium_iff_mIsEqm_reg`, `TidyR6MeasHyp.rateVersion`, `TidyR6MeasHyp.rateVersion_adapted`, `TidyR6MeasHyp.rateVersion_pricing`, `TidyR6MeasHyp.rate_ae_eq_version`, `TidyR6MeasHyp.mIsEqm_version` |
| Cochrane §2.1, p. 21; (2.3), p. 22 | on a complete filtration a function a.s. equal to a known one is known, a.s. bond pricing makes the rate adapted, and the two notions agree with no hypothesis on the rate | `TidyR6MeasHyp.CompleteFiltration`, `TidyR6MeasHyp.stronglyMeasurable_of_ae_eq`, `TidyR6MeasHyp.rate_adapted_of_complete`, `TidyR6MeasHyp.mEquilibrium_iff_mIsEqm_complete` |
| Cochrane (2.3), p. 22, counterexample | the point mass with the trivial filtration: `MIsEqm` and every other hypothesis hold, the rate is not adapted, `MEquilibrium` fails | `TidyR6MeasHyp.PointMass.ptProb`, `TidyR6MeasHyp.PointMass.botFiltration`, `TidyR6MeasHyp.PointMass.ptSystem`, `TidyR6MeasHyp.PointMass.ptRate`, `TidyR6MeasHyp.PointMass.ae_pt`, `TidyR6MeasHyp.PointMass.ptE`, `TidyR6MeasHyp.PointMass.rate_adapted_needed` |
| Cochrane §2.1, p. 21; (2.7), p. 22 | the uniform economy on `(0, 1]` with full information: `1/ω` is not integrable; a positive version of `ω`; constant surpluses `1/2` have present value `1` at `β = 1/2` | `TidyR6MeasHyp.Uniform.unifProb`, `TidyR6MeasHyp.Uniform.fullFiltration`, `TidyR6MeasHyp.Uniform.unifSystem`, `TidyR6MeasHyp.Uniform.inv_not_integrable`, `TidyR6MeasHyp.Uniform.mul_inv_not_integrable`, `TidyR6MeasHyp.Uniform.ae_pos`, `TidyR6MeasHyp.Uniform.unifE`, `TidyR6MeasHyp.Uniform.posVer`, `TidyR6MeasHyp.Uniform.posVer_pos`, `TidyR6MeasHyp.Uniform.measurable_posVer`, `TidyR6MeasHyp.Uniform.posVer_inv_not_integrable`, `TidyR6MeasHyp.Uniform.pv_half` |
| Cochrane pp. 31–33, counterexample | a target satisfying every other hypothesis of `TidyR5Meas.mPeg_equilibrium` but with non-integrable bond price has no equilibrium | `TidyR6MeasHyp.Uniform.nonintRate`, `TidyR6MeasHyp.Uniform.nonintRate_no_equilibrium` |
| Cochrane (2.3)–(2.6), p. 22, counterexamples | integrable real debt and integrable `P_t/P_{t+1}` are needed in the equivalence: `MIsEqm` holds only because `condExp` is `0` on non-integrable functions | `TidyR6MeasHyp.Uniform.cB`, `TidyR6MeasHyp.Uniform.realDebt_integrable_needed`, `TidyR6MeasHyp.Uniform.ppP`, `TidyR6MeasHyp.Uniform.ppRate`, `TidyR6MeasHyp.Uniform.ratio_integrable_needed` |
| Cochrane (2.7), p. 22 (tools restated from the DebtDeficitsInflation project) | conditional expectations commute with `L¹`-summable series | `TidyR6MeasL1.lintegral_enorm_eq`, `TidyR6MeasL1.tsum_lintegral_ne_top`, `TidyR6MeasL1.ae_summable_abs`, `TidyR6MeasL1.E_hasSum_L1` |
| Cochrane (2.7), p. 22 | integrable surpluses with summable discounted `L¹` norms from every date (`SurplusL1`); bounded and `L¹`-bounded surpluses are instances | `TidyR6MeasL1.SurplusL1`, `TidyR6MeasL1.SurplusL1.of_integral_bdd`, `TidyR6MeasL1.SurplusL1.of_bdd`, `TidyR6MeasL1.SurplusL1.summable_integral` |
| Cochrane (2.6)–(2.7), (2.26), pp. 22, 42 | for `SurplusL1` surpluses the present value is a genuine sum, solves its recursion and splits as `s_t + PVex_t`; the discounted forecast of a distant present value vanishes | `TidyR6MeasL1.E_shift_hasSum`, `TidyR6MeasL1.forwardSol_hasSum_L1`, `TidyR6MeasL1.forwardSol_solves_L1`, `TidyR6MeasL1.pv_eq_add_pvEx_L1`, `TidyR6MeasL1.tail_tendsto_L1` |
| Cochrane (2.3)–(2.7), §§2.1–2.4, pp. 21–33 | (2.4) and (2.6) iff (2.7), and `MEquilibrium` iff `MIsEqm` with regularity, for `SurplusL1` surpluses, with no bound and no `β < 1` | `TidyR6MeasL1.mFlowTvc_iff_valuation_L1`, `TidyR6MeasL1.mEquilibrium_iff_mIsEqm_L1` |
| Cochrane (2.7), p. 22, counterexample | summability is needed: at `β = 1/2`, `s_t = 2ᵗ` is integrable at every date, its junk present value satisfies the valuation equation and the flow condition fails | `TidyR6MeasL1.Junk.sGrow`, `TidyR6MeasL1.Junk.l1_needed` |
| Cochrane (2.26), (2.28), §2.9, pp. 42, 48 | the flow condition, the Treasury rule and the two-step process for `SurplusL1` surpluses | `TidyR6MeasL1.mFlow_L1`, `TidyR6MeasL1.mTreasury_rule_L1`, `TidyR6MeasL1.mTwoStep_eq_pegP_L1`, `TidyR6MeasL1.mTwoStep_debt_L1`, `TidyR6MeasL1.mTwoStep_equilibrium_L1` |
| Cochrane p. 43 (E5) | AR(1) surpluses with integrable shocks: forecasts, `PV_t = s_t/(1 − βη)`, present-value news, the corrected unexpected inflation, the printed formula fails, value news and its fall; the s-shape | `TidyR6MeasL1.ar1_E_L1`, `TidyR6MeasL1.mAr1_pv_L1`, `TidyR6MeasL1.mAr1_pv_news_L1`, `TidyR6MeasL1.mAr1_unexpected_inflation_L1`, `TidyR6MeasL1.mAr1_printed_fails_L1`, `TidyR6MeasL1.mAr1_value_news_L1`, `TidyR6MeasL1.mAr1_value_falls_L1`, `TidyR6MeasL1.mNews_pv_tsum_L1`, `TidyR6MeasL1.mSShape_L1` |
| Cochrane (2.12), (2.15), pp. 30–31 | in every equilibrium `B_t = 0` iff `PV_{t+1} = 0` and `B_tPV_{t+1} ≥ 0`; `B_t = (1 + i_t)P_tPVex_t` where debt is nonzero; the sign of `PV_{t+1}` must be known a period ahead | `TidyR6MeasSigned.div_pos_of_mul_pos`, `TidyR6MeasSigned.mEqm_sign`, `TidyR6MeasSigned.mDebt_eq_signed`, `TidyR6MeasSigned.mEqm_sign_condition` |
| Cochrane pp. 22, 30–33 | debt of either sign, present values nonzero a.s.: the target path is positive and an equilibrium, unique a.s.; an equilibrium exists iff the bond price is integrable, `i > −1`, `B_{−1}PV_0 > 0` and `PV_{t+1}E_tPV_{t+1} > 0` a.s. | `TidyR6MeasSigned.mPegP_pos_signed`, `TidyR6MeasSigned.mPeg_equilibrium_signed`, `TidyR6MeasSigned.mPeg_unique_signed`, `TidyR6MeasSigned.mPeg_existsUnique_iff_signed` |
| Cochrane pp. 22, 33 | with `PV ≡ 0` every constant price level is an equilibrium | `TidyR6MeasSigned.zero_pv_not_unique` |
| Cochrane (2.4), p. 22 | on a complete filtration debt is adapted (from `B_{−1}` known at `0`), so `MEquilibrium` iff `MIsEqm` with no adaptedness hypothesis; without completeness this fails (point mass) | `TidyR6MeasSigned.debt_adapted_of_complete`, `TidyR6MeasSigned.mEquilibrium_iff_mIsEqm_complete_L1`, `TidyR6MeasSigned.PointMass.ptDebt`, `TidyR6MeasSigned.PointMass.debt_adapted_needed` |
| Cochrane (2.15), p. 31; pp. 22, 30–33 | `B_t = (1 + i_t)P_tPVex_t` with no condition on debt; every equilibrium has `B_{−1} = 0 ⇔ PV_0 = 0`, `PV_{t+1} = 0 ⇔ E_tPV_{t+1} = 0` and the sign conditions | `TidyR6MeasZero.mDebt_eq_general`, `TidyR6MeasZero.mEqm_zero_conditions` |
| Cochrane (2.26), (2.28), §2.9, pp. 42, 48 | the flow condition and the Treasury rule with no positivity; the two-step process for debt of either sign, present values nonzero a.s. | `TidyR6MeasZero.mFlow_signed`, `TidyR6MeasZero.mTreasury_rule_signed`, `TidyR6MeasZero.mTwoStep_eq_pegP_signed`, `TidyR6MeasZero.mTwoStep_debt_signed`, `TidyR6MeasZero.mTwoStep_equilibrium_signed` |
| Cochrane §§2.4.3–2.4.4, pp. 31–33 | present values possibly zero: the target path, growing at `β(1 + i_t)` on the zero event, is adapted and an equilibrium; an equilibrium exists iff the bond price is integrable, `i > −1` a.s. and the conditions above hold | `TidyR6MeasZero.gFac`, `TidyR6MeasZero.zP`, `TidyR6MeasZero.zB`, `TidyR6MeasZero.gFac_sm`, `TidyR6MeasZero.zP_sm`, `TidyR6MeasZero.mPeg_equilibrium_zero`, `TidyR6MeasZero.mPeg_exists_iff_general` |
| Cochrane pp. 22, 33 | the price level is free on `{PV_0 = 0}` if it has positive probability, and on `{PV_{t+1} = 0}` if that event receives date-`(t + 1)` news | `TidyR6MeasZero.lam0`, `TidyR6MeasZero.nonunique_date0`, `TidyR6MeasZero.pertR`, `TidyR6MeasZero.pertY`, `TidyR6MeasZero.pertP`, `TidyR6MeasZero.pert_equilibrium`, `TidyR6MeasZero.nonunique_news` |
| Cochrane (2.3), p. 22; pp. 22, 33 | with `P_t/P_{t+1}` known at `t` the bond price pins `P_{t+1} = β(1 + i_t)P_t`; a two-state economy in which `{PV_1 = 0}` has probability `1/2` and the equilibrium is unique | `TidyR6MeasZero.pinned_of_known`, `TidyR6MeasZero.TwoState.twoMeasure`, `TidyR6MeasZero.TwoState.twoMeasure_univ`, `TidyR6MeasZero.TwoState.twoSystem`, `TidyR6MeasZero.TwoState.ae_two`, `TidyR6MeasZero.TwoState.measurable_bool`, `TidyR6MeasZero.TwoState.integrable_bool`, `TidyR6MeasZero.TwoState.twoE`, `TidyR6MeasZero.TwoState.sZ`, `TidyR6MeasZero.TwoState.pvZ`, `TidyR6MeasZero.TwoState.unique_with_zero_pv` |

## §§2.4–2.6 The family of exact equilibria with chosen versions (TidyR6MeasFamilyVersion, TidyR6MeasFamilySharp)

Versions of the present values are chosen bounded in every state, so smoothness and derivatives
hold in every state, and `ŝ` and `u` need only be bounded almost surely.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §§2.4–2.6, pp. 22, 31–40 | for given versions: the family's price level, debt, inflation, fiscal shock and `π̂_0`; the rule family's inflation and rate; the bounds on the versions | `TidyR6MeasFamilyVersion.vFamP`, `TidyR6MeasFamilyVersion.vFamB`, `TidyR6MeasFamilyVersion.vFamInfl`, `TidyR6MeasFamilyVersion.vShock`, `TidyR6MeasFamilyVersion.vInfl0`, `TidyR6MeasFamilyVersion.vRuleInfl`, `TidyR6MeasFamilyVersion.vRuleRate`, `TidyR6MeasFamilyVersion.Bounds` |
| Cochrane §2.4.3, §2.5, pp. 31, 35 | where `B_{−1} = 0` the family's price level and inflation are `0` (so the derivative is not the linear solution); nonzero price level otherwise | `TidyR6MeasFamilyVersion.vFamP_zero_of`, `TidyR6MeasFamilyVersion.vFamInfl_zero_of`, `TidyR6MeasFamilyVersion.vFamP_ne` |
| Cochrane (2.16)–(2.25), pp. 31–40, in every state | `C^n` in `ε`; the derivatives (2.19) and (2.25); the rule's rate above `−1` and the exact log rule; the family under the rule is the closed form | `TidyR6MeasFamilyVersion.vFam_contDiffOn`, `TidyR6MeasFamilyVersion.vFamInfl_hasDerivAt`, `TidyR6MeasFamilyVersion.vRuleRate_gt`, `TidyR6MeasFamilyVersion.log_one_add_vRuleRate`, `TidyR6MeasFamilyVersion.vRule_contDiffOn`, `TidyR6MeasFamilyVersion.vRuleInfl_hasDerivAt`, `TidyR6MeasFamilyVersion.vFamInfl_eq_vRuleInfl` |
| Cochrane pp. 31–40 | the families depend on the state only through the values of the versions, the rate and `u` | `TidyR6MeasFamilyVersion.vFamP_congr`, `TidyR6MeasFamilyVersion.vFamB_congr`, `TidyR6MeasFamilyVersion.vFamInfl_congr`, `TidyR6MeasFamilyVersion.vRuleInfl_congr`, `TidyR6MeasFamilyVersion.vRuleRate_congr` |
| Cochrane (2.3), (2.7), (2.26), pp. 22, 42 | necessity: positive present values on a neighbourhood of `0` bound `PV(ŝ)`, bounded `PV(ŝ)` bounds `ŝ`, and the canonical bond price is integrable iff `exp(−εî_t)` is | `TidyR6MeasFamilyVersion.pv_bound_necessary`, `TidyR6MeasFamilyVersion.shat_bound_of_pv_bound`, `TidyR6MeasFamilyVersion.rateExp_bondPrice_iff` |
| Cochrane (2.7), (2.15), pp. 22, 31; §2.5, p. 35 | the chosen versions by clamping: adapted, bounded in every state, a.s. equal to the present values and processes | `TidyR6MeasFamilyVersion.clamp`, `TidyR6MeasFamilyVersion.abs_clamp_le`, `TidyR6MeasFamilyVersion.clamp_eq`, `TidyR6MeasFamilyVersion.measurable_clamp`, `TidyR6MeasFamilyVersion.pvVer`, `TidyR6MeasFamilyVersion.pvExVer`, `TidyR6MeasFamilyVersion.procVer`, `TidyR6MeasFamilyVersion.ver_adapted`, `TidyR6MeasFamilyVersion.procVer_adapted`, `TidyR6MeasFamilyVersion.ver_bounds`, `TidyR6MeasFamilyVersion.ver_ae`, `TidyR6MeasFamilyVersion.procVer_ae`, `TidyR6MeasFamilyVersion.nonneg_of_bound` |
| Cochrane pp. 22–40 | present values, equilibria, surplus families and linear solutions are invariant under a.s. changes | `TidyR6MeasFamilyVersion.forwardSol_congr`, `TidyR6MeasFamilyVersion.pvExM_congr`, `TidyR6MeasFamilyVersion.mEquilibrium_congr_surplus`, `TidyR6MeasFamilyVersion.surpFam_ae`, `TidyR6MeasFamilyVersion.pegSol_congr`, `TidyR6MeasFamilyVersion.ruleSol_congr` |
| Cochrane pp. 31–40 | the families of `TidyR5MeasFamily` and `TidyR5MeasFamilyRule` are the version families with fixed versions; the version families are adapted | `TidyR6MeasFamilyVersion.mFamP_eq_vFamP`, `TidyR6MeasFamilyVersion.mFamB_eq_vFamB`, `TidyR6MeasFamilyVersion.mRuleInfl_eq_vRuleInfl`, `TidyR6MeasFamilyVersion.mRuleRate_eq_vRuleRate`, `TidyR6MeasFamilyVersion.vFamP_sm`, `TidyR6MeasFamilyVersion.vFamB_sm`, `TidyR6MeasFamilyVersion.vRuleInfl_sm`, `TidyR6MeasFamilyVersion.vRuleRate_sm` |
| Cochrane pp. 31–35 | with `ŝ` bounded a.s.: the version family equals the `TidyR5MeasFamily` family a.s. for all `ε` at once, is an equilibrium and is unique a.s.; the version shock is a shock and a.s. `TidyR5MeasFamily.mShock` | `TidyR6MeasFamilyVersion.vFam_ae_mFam`, `TidyR6MeasFamilyVersion.vFam_equilibrium`, `TidyR6MeasFamilyVersion.vFam_unique`, `TidyR6MeasFamilyVersion.vShock_ae`, `TidyR6MeasFamilyVersion.vShock_isShock` |
| Cochrane §§2.4–2.6, pp. 31–42 | everything at once: the peg family and, for every `θ`, the rule family with chosen versions | `TidyR6MeasFamilyVersion.version_family_linearization`, `TidyR6MeasFamilyVersion.version_rule_linearization` |
| Cochrane (2.16), p. 35 | integrability of `î` follows from integrability of `exp(−εî)` on `famDom`; the peg headline without it | `TidyR6MeasFamilySharp.ihat_integrable_of_exp`, `TidyR6MeasFamilySharp.version_family_linearization_exp` |
| Cochrane (2.3), (2.23), (2.25), pp. 22, 40 | the exact condition on `u`: `π_t(ε) = π⁰_t(ε) + εw_t` with `π⁰` bounded; the bond price is integrable iff `exp(−ε(θw_t + u_t))` is; the rule family is an equilibrium for every `ε ∈ famDom` iff that holds | `TidyR6MeasFamilySharp.wSum`, `TidyR6MeasFamilySharp.vRuleInfl_split`, `TidyR6MeasFamilySharp.vRuleInfl_bound`, `TidyR6MeasFamilySharp.vRule_bondPrice_iff`, `TidyR6MeasFamilySharp.vRule_equilibrium_iff` |
| Cochrane §2.6, pp. 39–42, example | the unbounded disturbance `u_t = −log ω` on the uniform distribution, with an equilibrium for every `ε ∈ famDom` | `TidyR6MeasFamilySharp.Unif.uLog`, `TidyR6MeasFamilySharp.Unif.unbounded_u_rule` |

## §§2.4–2.10 The fiscal corollaries, price-level targets and impulse responses on a genuine probability space (TidyR6MeasFiscal, TidyR6MeasLinearIRF, TidyR6MeasRestate)

Each row restates its `FiscalMonetary`, `FlatSupply` or `LinearFTMP` counterpart for
`TidyR5Meas.MEquilibrium` or the a.s. linear models; statements hold almost surely.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 31 | real revenue from bond sales is `PVex_t`; invariant across equilibria; future bond sales irrelevant; the share split | `TidyR6MeasFiscal.mRevenue`, `TidyR6MeasFiscal.mRevenue_invariant`, `TidyR6MeasFiscal.mFuture_sales_irrelevant`, `TidyR6MeasFiscal.mShareSplit` |
| Cochrane p. 42 | the equity issue; it finances a deficit with no unexpected inflation | `TidyR6MeasFiscal.mEquityIssue`, `TidyR6MeasFiscal.mEquityIssue_finances_deficit` |
| Cochrane (2.13), p. 30; p. 43 (E5) | news of a.s.-equal variables; bounded AR(1) surpluses: `PV_t = s_t/(1 − βη)`, present-value news, the corrected unexpected inflation, the printed formula fails, value news, the value falls with a deficit | `TidyR6MeasFiscal.innov_congr`, `TidyR6MeasFiscal.mAr1_pv`, `TidyR6MeasFiscal.mAr1_pv_news`, `TidyR6MeasFiscal.mAr1_unexpected_inflation`, `TidyR6MeasFiscal.mAr1_printed_fails`, `TidyR6MeasFiscal.mAr1_value_news`, `TidyR6MeasFiscal.mAr1_value_falls` |
| Cochrane p. 43 | present-value news is the discounted sum of surplus news; the s-shape | `TidyR6MeasFiscal.mNews_pv_tsum`, `TidyR6MeasFiscal.mSShape` |
| Cochrane p. 50 | adding a known amount leaves the news; no jump; `P_{t+1}` unchanged iff `D = 0` or no other news; unexpected inflation rescaled | `TidyR6MeasFiscal.mNews_pv_add_known`, `TidyR6MeasFiscal.mStimulus_no_jump`, `TidyR6MeasFiscal.mStimulus_price_iff`, `TidyR6MeasFiscal.mStimulus_unexpected_inflation` |
| Cochrane (2.28), §2.9, p. 48 | the Treasury rule; debt sold in the ratio of gross rates; the two-step process gives the target price level and debt, is adapted and is an equilibrium | `TidyR6MeasFiscal.mTreasury_rule`, `TidyR6MeasFiscal.mDebt_ratio_of_rate`, `TidyR6MeasFiscal.mTwoStep`, `TidyR6MeasFiscal.mTwoStep_eq_pegP`, `TidyR6MeasFiscal.mTwoStep_debt`, `TidyR6MeasFiscal.mTwoStep_sm`, `TidyR6MeasFiscal.mTwoStep_equilibrium` |
| Cochrane pp. 31, 48 (finite trees) | the revenue result and the Treasury rule give the core statements in every state | `TidyR6MeasFiscal.Link.tree_mRevenue`, `TidyR6MeasFiscal.Link.tree_mTreasury_rule` |
| Cochrane p. 43, on the `±1` coin | AR(1) present-value news is `ε_{t+1}/(1 − βη)`, nonzero a.s. | `TidyR6MeasFiscal.Coin.coin_ne_zero`, `TidyR6MeasFiscal.Coin.shock_ne_zero`, `TidyR6MeasFiscal.Coin.coin_ar1_news` |
| Cochrane p. 50, on the `±1` coin (every history null) | the stimulus counterexample: the heads indicator and its forecasts, the two surplus paths, their discounted sums and present values (equal at date `0` state by state), the zero target; `P_0` and `E_0(P_0/P_1)` agree but `P_1` differs a.s. | `TidyR6MeasFiscal.Coin.hd`, `TidyR6MeasFiscal.Coin.measurable_hd`, `TidyR6MeasFiscal.Coin.hd_cases`, `TidyR6MeasFiscal.Coin.hd_nonneg`, `TidyR6MeasFiscal.Coin.abs_aff_hd_le`, `TidyR6MeasFiscal.Coin.E_late`, `TidyR6MeasFiscal.Coin.E_zero_fun`, `TidyR6MeasFiscal.Coin.sB`, `TidyR6MeasFiscal.Coin.sS`, `TidyR6MeasFiscal.Coin.discSum_tail`, `TidyR6MeasFiscal.Coin.sB_sS_bdd`, `TidyR6MeasFiscal.Coin.discSum_sB`, `TidyR6MeasFiscal.Coin.discSum_sS`, `TidyR6MeasFiscal.Coin.discSum_rec'`, `TidyR6MeasFiscal.Coin.discSum_sS_one`, `TidyR6MeasFiscal.Coin.discSum_zero`, `TidyR6MeasFiscal.Coin.pv_values`, `TidyR6MeasFiscal.Coin.pv_pos`, `TidyR6MeasFiscal.Coin.zeroRate_ok`, `TidyR6MeasFiscal.Coin.coin_stimulus_not_neutral` |
| Cochrane (2.13), pp. 30, 35, 40 | the algebra of news; known variables have no news; a shock's news on arrival and before | `TidyR6MeasLinearIRF.innov_add'`, `TidyR6MeasLinearIRF.innov_sub'`, `TidyR6MeasLinearIRF.innov_smul'`, `TidyR6MeasLinearIRF.innov_lin3`, `TidyR6MeasLinearIRF.innov_known`, `TidyR6MeasLinearIRF.innov_shock`, `TidyR6MeasLinearIRF.innov_shock_later`, `TidyR6MeasLinearIRF.mInnov_of_news` |
| Cochrane Fig. 2.1, pp. 36–37 | peg responses on impact and later; the rate and fiscal panels; expected inflation; announcements; the long-run Fisher relation; the present-value news of announced surpluses; the expected fiscal shock | `TidyR6MeasLinearIRF.mIrf_peg_impact`, `TidyR6MeasLinearIRF.mIrf_peg_later`, `TidyR6MeasLinearIRF.mFig21_rate`, `TidyR6MeasLinearIRF.mFig21_fiscal`, `TidyR6MeasLinearIRF.mExpected_inflation_ahead`, `TidyR6MeasLinearIRF.mAnnouncement_invariant`, `TidyR6MeasLinearIRF.mNo_announcement_effect`, `TidyR6MeasLinearIRF.mLong_run_fisher`, `TidyR6MeasLinearIRF.mPvNews_of_news`, `TidyR6MeasLinearIRF.mFig21_expected_fiscal` |
| Cochrane §2.5.1, p. 38 (E6) | the price-level target; a higher rate lowers the price level; the fiscal contraction; the loggerhead; `ΔE_{t+1}π_{t+1} = ΔE_{t+1}p_{t+1}` | `TidyR6MeasLinearIRF.mPTarget_price`, `TidyR6MeasLinearIRF.mPTarget_rate_lowers_price`, `TidyR6MeasLinearIRF.mPTarget_fiscal_contraction`, `TidyR6MeasLinearIRF.mLoggerhead`, `TidyR6MeasLinearIRF.mInnov_pi_eq_innov_p` |
| Cochrane (2.23), (2.25), Fig. 2.2, pp. 40–41 | the disturbance's response; inflation and rate responses; the monetary and fiscal panels; fiscal policy sets impact; the one-time price jump; the price level returns | `TidyR6MeasLinearIRF.mIrf_disturbance`, `TidyR6MeasLinearIRF.mIrf_rule`, `TidyR6MeasLinearIRF.mIrf_rule_rate`, `TidyR6MeasLinearIRF.mFig22_monetary`, `TidyR6MeasLinearIRF.mFig22_fiscal`, `TidyR6MeasLinearIRF.mFiscal_sets_impact`, `TidyR6MeasLinearIRF.mOne_time_price_jump`, `TidyR6MeasLinearIRF.mPrice_level_returns` |
| Chapter 2 (finite trees) | the impact response, the rule responses and the price-level target give the core statements in every state | `TidyR6MeasLinearIRF.Link.tree_irf_peg_impact`, `TidyR6MeasLinearIRF.Link.tree_irf_rule`, `TidyR6MeasLinearIRF.Link.tree_pTarget_price` |
| Cochrane p. 39 | passive fiscal policy: the valuation equation holds and every shock is an equilibrium inflation innovation | `TidyR6MeasRestate.mPassiveShock`, `TidyR6MeasRestate.mPassive_valuation_holds`, `TidyR6MeasRestate.mPassive_any_innovation` |
| Cochrane p. 50 | with no present-value news `P_{t+1} = β(1 + i_t)P_t`; the stimulus is neutral when there is no fiscal news; the perfect-foresight case | `TidyR6MeasRestate.mPrice_succ_no_news`, `TidyR6MeasRestate.mStimulus_neutral_no_news`, `TidyR6MeasRestate.mPf_stimulus_neutral` |
| Cochrane p. 42, on the `±1` coin | a credible reform with deficits gives unexpected disinflation in every equilibrium; such a revision exists | `TidyR6MeasRestate.coin_pm_one`, `TidyR6MeasRestate.heads_pos`, `TidyR6MeasRestate.dShift`, `TidyR6MeasRestate.sReform`, `TidyR6MeasRestate.mReform_with_deficits`, `TidyR6MeasRestate.mReform_exists` |

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

## (2.3) The bond price is positive: the rate conditions are redundant for `β > 0` (TidyR5BondPrice)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.3), p. 22 | a positive payoff has a positive forecast in every state, from the core axioms alone, on any `Ω` | `TidyR5BondPrice.E_pos_of_pos` |
| Cochrane (2.3), p. 22 | in every derived equilibrium with `β > 0` the bond price is positive and `i > −1`; with `Q = 1/(1 + i)` the rate exceeds `−1` and (with pull-out) is adapted | `TidyR5BondPrice.bondPrice_pos`, `TidyR5BondPrice.isEqm_bondPrice_pos`, `TidyR5BondPrice.isEqm_rate_gt`, `TidyR5BondPrice.isEqm_inv_rate_gt`, `TidyR5BondPrice.isEqm_inv_rate_adapted` |
| Cochrane (2.3), (2.14), pp. 22, 31 | the bond-pricing condition alone forces `i > −1` and, with pull-out, an adapted rate | `TidyR5BondPrice.rate_gt_of_pricing`, `TidyR5BondPrice.rate_adapted_of_pricing`, `TidyR5BondPrice.bondPricing_rate_gt`, `TidyR5BondPrice.bondPricing_rate_adapted` |
| Cochrane §§2.1–2.4, pp. 21–33 | the rate conditions of `FiscalMonetary.Equilibrium` and the rate hypotheses of `GeneralLinks.equilibrium_iff_isEqm` are redundant for `β > 0`; so is `Q > 0` in `GeneralLinks.isEqm_fisher_log` | `TidyR5BondPrice.equilibrium_iff_reduced`, `TidyR5BondPrice.equilibrium_iff_isEqm_pos`, `TidyR5BondPrice.isEqm_fisher_log_pos` |
| Cochrane pp. 31–33 | a target with `i_t ≤ −1` in some state has no equilibrium of either kind | `TidyR5BondPrice.no_eqm_of_rate_le` |
| Cochrane §§2.1–2.4, pp. 21–33 | the hypothesis is needed at `β = 0`: with `i ≡ −1` every other hypothesis holds and `Valuation.IsEqm` holds, but `FiscalMonetary.Equilibrium` fails | `TidyR5BondPrice.rateNegOne`, `TidyR5BondPrice.beta_zero_counterexample` |

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

## Links to the Woodford projects on a genuine probability space (TidyR6MeasLinks, TidyR6MeasRestate)

The contrasts of `Links` on the i.i.d. `±1` coin economy, in which every history is null; sets
of solutions are counted up to null sets.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane Ch. 2, p. 29 | the clamped coin: bounded and measurable in every state, a.s. the coin, mean zero, not a.s. zero | `TidyR6MeasLinks.cc`, `TidyR6MeasLinks.abs_cc_le`, `TidyR6MeasLinks.measurable_cc`, `TidyR6MeasLinks.cc_one_neg`, `TidyR6MeasLinks.E_cc`, `TidyR6MeasLinks.cc_not_ae_zero`, `TidyR6MeasLinks.cc_mul_ne`, `TidyR6MeasLinks.measurable_cc_shock` |
| Woodford (2003) Proposition 2.5, §A.6, pp. 87, 639 (restated), used for Cochrane p. 33 | sunspot price paths (`u_c ≡ 1`) are positive, adapted and solve the Fisher equation under a peg a.s.; distinct `σ` differ with positive probability; uncountably many solutions up to null sets | `TidyR6MeasLinks.sunP`, `TidyR6MeasLinks.WFisher`, `TidyR6MeasLinks.sunP_pos`, `TidyR6MeasLinks.sunP_ratio`, `TidyR6MeasLinks.sunP_adapted`, `TidyR6MeasLinks.sunP_mem`, `TidyR6MeasLinks.sunP_distinct`, `TidyR6MeasLinks.prop_2_5_meas` |
| Cochrane p. 33 against Woodford Proposition 2.5 | with the valuation equation `P ≡ 1` a.s. is the unique equilibrium, and it is one of Woodford's solutions | `TidyR6MeasLinks.pv_one`, `TidyR6MeasLinks.peg_contrast_meas` |
| Woodford (2003) eq. (2.6), Proposition 2.6, App. A, pp. 91, 636 (restated), used for Cochrane §2.6 | (2.6) a.s.; its forward form; the determinacy criterion holds iff `\|φ_π\| > 1` on the coin | `TidyR6MeasLinks.Eq26M`, `TidyR6MeasLinks.eq26M_iff_solves`, `TidyR6MeasLinks.DetCrit`, `TidyR6MeasLinks.prop_2_6_meas` |
| Cochrane §2.6, pp. 39–40, against Woodford Proposition 2.6 | for `\|θ\| ≤ 1` the criterion fails but the rule model has an a.s.-unique solution; for `\|θ\| < 1` uncountably many bounded sunspot solutions against the unique `π = 0` | `TidyR6MeasLinks.taylor_contrast_meas`, `TidyR6MeasLinks.sunπ`, `TidyR6MeasLinks.WTaylor`, `TidyR6MeasLinks.sunπ_adapted`, `TidyR6MeasLinks.sunπ_bdd`, `TidyR6MeasLinks.sunπ_mem`, `TidyR6MeasLinks.taylor_contrast_coin_meas` |
| Woodford (2003) (4.2), p. 124 (restated), used for Cochrane p. 39 | the discount factor state by state; Ricardian transversality pathwise and in conditional expectation; under the passive rule the valuation equation holds for every initial real debt; with exogenous surpluses flow plus TVC give `x = PV` | `TidyR6MeasLinks.mDiscount`, `TidyR6MeasLinks.mDiscount_eq_discount`, `TidyR6MeasLinks.mRicardian_tvc`, `TidyR6MeasLinks.passivePath`, `TidyR6MeasLinks.mPassive_any_price`, `TidyR6MeasLinks.mActive_unique_value` |
| Cochrane §2.6 against Woodford (2.6) (finite trees) | the a.s. (2.6) is the core `Links.Eq26` | `TidyR6MeasLinks.Link.tree_eq26M_iff` |
| Woodford (2003) eq. (1.21), §A.6, pp. 71, 639 (restated), used for Cochrane p. 33 | the general `(u_c, ν)` sunspot family: positive, solves (1.21) a.s. for every adapted `ν < 1` with `u_c(1 − ν) ≥ m > 0`, distinct sunspots differ with positive probability; with `u_c ≡ 1`, (1.21) is (2.3) | `TidyR6MeasRestate.mKexp`, `TidyR6MeasRestate.mGrossInfl`, `TidyR6MeasRestate.mSunspotPrice`, `TidyR6MeasRestate.MFisherW`, `TidyR6MeasRestate.mKexp_ge`, `TidyR6MeasRestate.mSunspotPrice_pos`, `TidyR6MeasRestate.mSunspot_fisher`, `TidyR6MeasRestate.mSunspot_injective`, `TidyR6MeasRestate.mFisherW_one_iff` |

## Measure-theoretic expectations: the copied core (ExpectationsMeasure, ExpectationsMeasureIID)

Copied verbatim (namespace renamed) from the `ObservationalEquivalence` project, where it was
built; its docstrings cite Cochrane (2023), Chapter 2. Statements hold almost everywhere unless
marked exact.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane pp. 29–30 (shared core) | a probability space with a filtration; `E_t x = μ[x \| 𝓕_t]` is Mathlib's `condExp`; bounded random variables and processes | `ExpectationsMeasure.MeasExpectationSystem`, `ExpectationsMeasure.MeasExpectationSystem.μ`, `ExpectationsMeasure.MeasExpectationSystem.E`, `ExpectationsMeasure.MeasExpectationSystem.BddRV`, `ExpectationsMeasure.MeasExpectationSystem.BddProc` |
| Cochrane pp. 29–30 (shared core) | the expectation axioms a.e.: linearity, constants (exact), monotonicity, the tower property, earlier forecasts known later (exact), adapted variables are their own forecast (exact), measurability and integrability of forecasts, the law of total expectation, pull-out of bounded known factors, bounds pass through `E_t` | `ExpectationsMeasure.MeasExpectationSystem.E_add`, `ExpectationsMeasure.MeasExpectationSystem.E_sub`, `ExpectationsMeasure.MeasExpectationSystem.E_smul`, `ExpectationsMeasure.MeasExpectationSystem.E_const`, `ExpectationsMeasure.MeasExpectationSystem.E_zero`, `ExpectationsMeasure.MeasExpectationSystem.E_mono`, `ExpectationsMeasure.MeasExpectationSystem.E_tower`, `ExpectationsMeasure.MeasExpectationSystem.stronglyMeasurable_E`, `ExpectationsMeasure.MeasExpectationSystem.integrable_E`, `ExpectationsMeasure.MeasExpectationSystem.E_of_stronglyMeasurable`, `ExpectationsMeasure.MeasExpectationSystem.E_of_aestronglyMeasurable`, `ExpectationsMeasure.MeasExpectationSystem.E_known`, `ExpectationsMeasure.MeasExpectationSystem.E_E_self`, `ExpectationsMeasure.MeasExpectationSystem.E_congr`, `ExpectationsMeasure.MeasExpectationSystem.integral_E`, `ExpectationsMeasure.MeasExpectationSystem.E_pullOut`, `ExpectationsMeasure.MeasExpectationSystem.abs_E_le` |
| Cochrane p. 29 (shared core) | bounded random variables are integrable and closed under constants, sums, multiples, differences, products, squares and forecasts | `ExpectationsMeasure.MeasExpectationSystem.BddRV.integrable`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.of_stronglyMeasurable`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.const`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.add`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.smul`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.sub`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.mul`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.sq`, `ExpectationsMeasure.MeasExpectationSystem.BddRV.E` |
| Cochrane (2.13), p. 30; (2.17), p. 35 (shared core) | the news `ΔE_{t+1}x = E_{t+1}x − E_tx` is a martingale difference, orthogonal to bounded date-`t` variables; revisions telescope into news and `x = E_tx + ΔE_{t+1}x` (exact) | `ExpectationsMeasure.MeasExpectationSystem.innov`, `ExpectationsMeasure.MeasExpectationSystem.stronglyMeasurable_innov`, `ExpectationsMeasure.MeasExpectationSystem.E_innov`, `ExpectationsMeasure.MeasExpectationSystem.E_mul_innov`, `ExpectationsMeasure.MeasExpectationSystem.E_sub_E_eq_sum_innov`, `ExpectationsMeasure.MeasExpectationSystem.eq_E_add_innov` |
| Cochrane p. 29 (present values; shared core) | `E_t` passes through a dominated series as a genuine `HasSum`; the realised discounted sum and its recursion, bound and measurability | `ExpectationsMeasure.MeasExpectationSystem.E_hasSum`, `ExpectationsMeasure.MeasExpectationSystem.discSum`, `ExpectationsMeasure.MeasExpectationSystem.summable_geom_mul`, `ExpectationsMeasure.MeasExpectationSystem.abs_tsum_geom_mul_le`, `ExpectationsMeasure.MeasExpectationSystem.discSum_succ`, `ExpectationsMeasure.MeasExpectationSystem.discSum_bdd`, `ExpectationsMeasure.MeasExpectationSystem.discSum_rec`, `ExpectationsMeasure.MeasExpectationSystem.aestronglyMeasurable_discSum` |
| Cochrane p. 29 (shared core) | `z_t = aE_tz_{t+1} + u_t` for `\|a\| < 1`: the forward solution `E_t∑aᵏu_{t+k} = ∑aᵏE_tu_{t+k}` is adapted, bounded and solves; uniqueness needs no adaptedness | `ExpectationsMeasure.MeasExpectationSystem.Solves`, `ExpectationsMeasure.MeasExpectationSystem.forwardSol`, `ExpectationsMeasure.MeasExpectationSystem.forwardSol_adapted`, `ExpectationsMeasure.MeasExpectationSystem.forwardSol_bdd`, `ExpectationsMeasure.MeasExpectationSystem.forwardSol_solves`, `ExpectationsMeasure.MeasExpectationSystem.forwardSol_hasSum`, `ExpectationsMeasure.MeasExpectationSystem.iterate_homog`, `ExpectationsMeasure.MeasExpectationSystem.forward_unique`, `ExpectationsMeasure.MeasExpectationSystem.existsUnique_forward` |
| Cochrane p. 29 (shared core) | for `\|a\| ≥ 1` a genuinely random bounded sunspot sits next to every bounded adapted solution; given genuinely random news, existence and uniqueness for all bounded adapted `u` iff `\|a\| < 1` | `ExpectationsMeasure.MeasExpectationSystem.sunspot`, `ExpectationsMeasure.MeasExpectationSystem.sunspot_succ`, `ExpectationsMeasure.MeasExpectationSystem.sunspot_adapted`, `ExpectationsMeasure.MeasExpectationSystem.sunspot_bdd`, `ExpectationsMeasure.MeasExpectationSystem.sunspot_solves`, `ExpectationsMeasure.MeasExpectationSystem.solves_add`, `ExpectationsMeasure.MeasExpectationSystem.solves_zero`, `ExpectationsMeasure.MeasExpectationSystem.sunspot_not_predictable`, `ExpectationsMeasure.MeasExpectationSystem.not_unique_of_one_le`, `ExpectationsMeasure.MeasExpectationSystem.unique_iff`, `ExpectationsMeasure.MeasExpectationSystem.existsUnique_iff` |
| Cochrane §2.7, p. 42 (shared core) | AR(1) with martingale-difference, conditionally homoskedastic shocks: `E_tu_{t+j} = ρʲu_t`, `Var_tu_{t+j} = σ²∑_{i<j}ρ^{2i} = σ²(1 − ρ^{2j})/(1 − ρ²)` (Mathlib `condVar`) | `ExpectationsMeasure.MeasExpectationSystem.ar1_E`, `ExpectationsMeasure.MeasExpectationSystem.ar1_E_sq_dev`, `ExpectationsMeasure.MeasExpectationSystem.ar1_condVar`, `ExpectationsMeasure.MeasExpectationSystem.ar1_condVar_closed` |
| Cochrane p. 29 (shared core) | bridge to the core: on a finite discrete `Ω` with full support a measure system is an `ExpectationSystem` with the same `E_t` and the pull-out property | `ExpectationsMeasure.MeasExpectationSystem.eq_of_ae_eq`, `ExpectationsMeasure.MeasExpectationSystem.le_of_ae_le`, `ExpectationsMeasure.MeasExpectationSystem.ELin`, `ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem`, `ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_E`, `ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_pullOut` |
| Cochrane p. 29 (shared core) | bridge from the core: a finite event tree is a measure system whose `condExp` is the tree's cell average at every state; the round trip returns the tree's own `E` | `ExpectationsMeasure.TreeBridge.trivialFirst`, `ExpectationsMeasure.TreeBridge.sum_prob_condE`, `ExpectationsMeasure.TreeBridge.treeMeasure`, `ExpectationsMeasure.TreeBridge.treeMeasure_singleton`, `ExpectationsMeasure.TreeBridge.treeMeasure_univ`, `ExpectationsMeasure.TreeBridge.treeProb`, `ExpectationsMeasure.TreeBridge.integral_treeProb`, `ExpectationsMeasure.TreeBridge.treeFiltration`, `ExpectationsMeasure.TreeBridge.stronglyMeasurable_condE`, `ExpectationsMeasure.TreeBridge.treeSystem`, `ExpectationsMeasure.TreeBridge.treeSystem_fullSupport`, `ExpectationsMeasure.TreeBridge.treeSystem_E`, `ExpectationsMeasure.TreeBridge.treeSystem_toExpectationSystem_E` |
| Cochrane p. 29 (shared core) | the i.i.d. economy on `ℕ → ℝ` under `ν^ℕ` (Mathlib `Measure.infinitePi`), shocks `ε_t(ω) = ω_t`, natural filtration; future shocks independent of date-`t` information, so `E_tf(ε_{t+1}) = ∫f dν` | `ExpectationsMeasureIID.iidProb`, `ExpectationsMeasureIID.iidSystem`, `ExpectationsMeasureIID.shock`, `ExpectationsMeasureIID.measurable_shock`, `ExpectationsMeasureIID.coordSigma`, `ExpectationsMeasureIID.futureSigma`, `ExpectationsMeasureIID.coordSigma_le`, `ExpectationsMeasureIID.futureSigma_le`, `ExpectationsMeasureIID.iIndep_coord`, `ExpectationsMeasureIID.filtration_le_past`, `ExpectationsMeasureIID.indep_future`, `ExpectationsMeasureIID.E_future`, `ExpectationsMeasureIID.measurable_future_fun`, `ExpectationsMeasureIID.integral_shock_fun`, `ExpectationsMeasureIID.E_shock_fun`, `ExpectationsMeasureIID.E_shock`, `ExpectationsMeasureIID.E_shock_sq`, `ExpectationsMeasureIID.shock_ae_bdd` |
| Cochrane p. 29 (shared core) | mean-zero shocks with constant conditional variance `σ² > 0`, nondegenerate at every date; every history is null, so the system is not finitely (or countably) supported | `ExpectationsMeasureIID.E_shock_zero`, `ExpectationsMeasureIID.E_shock_sq_eq`, `ExpectationsMeasureIID.condVar_shock`, `ExpectationsMeasureIID.shock_not_ae_E`, `ExpectationsMeasureIID.singleton_lt_one`, `ExpectationsMeasureIID.exists_singleton_le`, `ExpectationsMeasureIID.iid_singleton`, `ExpectationsMeasureIID.iid_countable_null`, `ExpectationsMeasureIID.iid_not_finitely_supported` |
| Cochrane p. 29; §2.7, p. 42 (shared core) | determinacy in the i.i.d. economy iff `\|a\| < 1`, with a random sunspot otherwise; the bounded AR(1), its forecasts and conditional variance | `ExpectationsMeasureIID.iid_news`, `ExpectationsMeasureIID.iid_existsUnique_iff`, `ExpectationsMeasureIID.iid_sunspot`, `ExpectationsMeasureIID.ar1`, `ExpectationsMeasureIID.ar1_succ`, `ExpectationsMeasureIID.ar1_adapted`, `ExpectationsMeasureIID.ar1_bdd`, `ExpectationsMeasureIID.iid_ar1_E`, `ExpectationsMeasureIID.iid_ar1_condVar`, `ExpectationsMeasureIID.iid_ar1_condVar_closed` |
| Cochrane p. 29; §2.7, p. 42 (shared core) | the fair `±1` coin economy: mean zero, variance one, bounded, and every property above at once | `ExpectationsMeasureIID.coinMeasure`, `ExpectationsMeasureIID.coinMeasure_univ`, `ExpectationsMeasureIID.coin`, `ExpectationsMeasureIID.integral_coin`, `ExpectationsMeasureIID.coin_mean`, `ExpectationsMeasureIID.coin_var`, `ExpectationsMeasureIID.coin_bdd`, `ExpectationsMeasureIID.coin_economy` |

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
