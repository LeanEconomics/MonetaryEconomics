# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, "Monetarism" (pp. 433–464),
with the precise claims of Chapter 11 (pp. 315–318) and §14.1 (p. 342), and of Online Appendix
§1.6 "Money in continuous time" (pp. 567–569), Chapter 3 "Pruning multiple monetary equilibria"
(§§3.1–3.2.4, pp. 612–632) and Chapter 4 "Money in continuous time" (pp. 635–641). Each formal
claim is listed with its Lean name, relative to the namespace `Cochrane.Monetarism`. Page numbers
are book pages; "A1", "A3" and "A4" are Online Appendix Chapters 1, 3 and 4. The book has no
labelled propositions, so rows are keyed by equation number, figure, footnote, the survey's names
for the precise claims of the verbal chapters (V1–V5, V11, NI-7) or page. Rows follow Chapter 19
section by section. The Chapter 11 and §14.1 claims follow §19.1, whose module proves them, and
the Online Appendix Chapter 3 material follows §19.4, which defers to it. Then come Online
Appendix §1.6 and Chapter 4, the links between modules and the shared tools.

The linear and present-value results hold for an arbitrary `ExpectationSystem`, so under perfect
foresight and under uncertainty; date-`t` quantities are known at `t`, and results that take them
out of `E_t` assume `ExpectationSystem.PullOut`. The nonlinear phase dynamics of money in utility,
the Online Appendix Chapter 3 equilibria and the cash-in-advance equilibria are perfect-foresight,
as in the book; the first-order conditions are also derived on a finite event tree. Continuous
time is deterministic. Survey error codes E13–E23 are those of the survey of Chapters 11–19
(`notes/survey_cochrane_ch11-19.md`); see [corrections](corrections.md). Rows marked "restated"
reproduce results of the Woodford Chapter 2 project or of other Cochrane projects in this
namespace.

## §19.1 Equilibria and regimes, pp. 434–435 (Regimes)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (19.1), p. 434; (11.2), p. 315 | money demand `M_tV_t = P_ty_t` at every date and in every state | `Regimes.QuantityEq` |
| Cochrane §3.4; (19.3), p. 434 | the nominal bond is priced by the discount factor, `E_t(Λ_{t+1}/P_{t+1}) = (Λ_t/P_t)/(1 + i_t)` | `Regimes.BondPricing` |
| Cochrane (19.2)–(19.3), p. 434 | the partial sums of the two forms of the valuation equation, multiplied through by the known `Λ_t` | `Regimes.partial192`, `Regimes.partial193` |
| Cochrane (19.3), p. 434 | the one-period step of the summation by parts, `E_t[Λ_{k+1}M_k/P_{k+1}] = E_t[M_k(Λ_k/P_k)/(1 + i_k)]` | `Regimes.E_next_value`, `Regimes.step_identity` |
| Cochrane (19.2)–(19.3), p. 434 | the summation by parts at every horizon; given bond pricing and the money transversality condition, (19.2) holds iff (19.3) does | `Regimes.sum_by_parts`, `Regimes.eq192_iff_eq193` |
| Cochrane p. 434 | the book's money transversality condition `E_tΛ_{t+T}M_{t+T}/P_{t+T} → 0` implies the form used, for `i ≥ 0` and `M ≥ 0` | `Regimes.tail_tendsto_zero_of_book_tvc` |
| Cochrane p. 439; §3.4 | the government flow constraint `B_{t−1} + M_{t−1} = P_ts_t + Q_tB_t + M_t`, and its one-period valuation step | `Regimes.Flow`, `Regimes.flow_value_recursion` |
| Cochrane (19.2)–(19.3), p. 434 | given the flow constraint and bond pricing, (19.2) holds iff the bond transversality condition does; with the money transversality condition too, (19.3) holds | `Regimes.flow_pv_iff_tvc`, `Regimes.flow_eq193_of_tvc` |
| Cochrane (19.1), (19.3), p. 434 | under `MV = Py` the seigniorage flow `(i/(1 + i))M/P = (i/(1 + i))y/V` does not involve the price level | `Regimes.seigniorage_indep_price` |
| Cochrane p. 435 | the valuation equation `B_{t−1} + M_{t−1} = P_tW_t`; positive processes; the active-money/passive-fiscal and active-fiscal/passive-money regimes | `Regimes.Valuation`, `Regimes.Pos`, `Regimes.MonetaryEqm`, `Regimes.FiscalEqm` |
| Cochrane p. 435 (NI-7) | "the fiscal and monetary regimes are observationally equivalent": every equilibrium is the unique equilibrium of an active-money regime and of an active-fiscal regime, with identical observables | `Regimes.ni7` |
| Cochrane p. 435 | both passive: every positive price level is an equilibrium; both active: an equilibrium exists iff `M_tV_tW_t = D_ty_t` | `Regimes.double_passive`, `Regimes.double_active_iff` |
| Cochrane p. 435 | the passive surplus `s_t = W_t − βE_tW_{t+1}` exists for every bounded adapted target `W`, and its present value is `W_t` | `Regimes.passiveSurplus`, `Regimes.passive_surplus_realises` |

## Chapter 11: open-market operations and elastic currency, pp. 315–318 (Regimes, Seigniorage)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (11.1), p. 315 | the partial sum of the valuation equation with interest-paying money | `Regimes.partial111` |
| Cochrane (11.1), p. 315; V1, pp. 316–317 | the seigniorage term vanishes iff `i = i^m`, and then the right side of (11.1) is `∑βʲE_ts_{t+j}` | `Regimes.spread_term_eq_zero_iff`, `Regimes.partial111_of_no_spread` |
| Cochrane §11.2, pp. 316–317 (V1) | with `i = i^m` an open-market swap leaves the price level unchanged: (11.1) depends on bonds and money only through `B + M` | `Regimes.omo_irrelevant` |
| Cochrane §11.2, p. 317 (V2) | `P_0 = D/(S + Σ)` falls as the present value `Σ` of seigniorage rises; in the Cagan example raising money growth lowers `P_0` below the Laffer peak `1/a` and raises it beyond | `Seigniorage.v2_price_level`, `Seigniorage.v2_cagan` |
| Cochrane §11.2, p. 317 (V3) | "the price of money can be passive": exactly one spread `i − i^m` clears `MV(i − i^m) = Py` | `Regimes.spread_existsUnique` |
| Cochrane §11.2, p. 318 (V4) | with the same `B + M` and rigid `MV = Py`, money falls iff the price level falls iff the real value of surpluses rises, iff bonds rise | `Regimes.omo_equivalence` |
| Cochrane §11.3, p. 318 (V5) | elastic currency: with `M_t = P_ty_t/V_t` "any `P` is consistent with this policy" | `Regimes.elastic_currency` |

## §14.1 The helicopter drop, p. 342 (Regimes)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 342 | the fiscal-theory answer `P′/P = D′/D` and the monetarist answer `P′/P = M′/M` | `Regimes.ftpl_price_ratio`, `Regimes.quantity_price_ratio` |
| Cochrane p. 342 (V11) | "diluted 1%": nominal liabilities, hence the price level, rise by the factor `1 + 1/101`, within one hundredth of a percentage point of 1% | `Regimes.helicopter_fiscal`, `Regimes.helicopter_fiscal_approx` |
| Cochrane p. 342 (V11) | the monetarist answer is 100%; $2,000 of cash is 1% of $200,000; the doubling wipes out $50,000 of the real value of bonds | `Regimes.helicopter_monetarist`, `Regimes.helicopter_cash_share`, `Regimes.helicopter_bond_loss` |

## §19.2 Interest-elastic money demand and multiple equilibria, pp. 436–438 (CaganRE)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (19.4), p. 436 | money demand in levels iff in logs, `m_t − p_t − y = −ai_t` (`a = αv`) | `CaganRE.eq194_iff_log`, `CaganRE.MoneyDemand` |
| Cochrane (19.5), p. 436 | the Fisher equation; the Cagan equation; money demand and Fisher iff Cagan and Fisher; the second line of (19.5) | `CaganRE.Fisher`, `CaganRE.Cagan`, `CaganRE.md_fisher_iff_cagan`, `CaganRE.cagan_iff_expect` |
| Cochrane p. 437 | `θ = (1 + a)/a > 1`, `θ⁻¹ = a/(1 + a)`, `\|θ⁻¹\| < 1` | `CaganRE.theta`, `CaganRE.theta_gt_one`, `CaganRE.theta_inv`, `CaganRE.abs_theta_inv_lt_one` |
| Cochrane (19.8), p. 437 | the forcing `x_t = m_t − y + ar`; (19.5) is `p_t = θ⁻¹E_tp_{t+1} + (1 − θ⁻¹)x_t`; the forcing is adapted when money is | `CaganRE.forcing`, `CaganRE.cagan_iff_solves`, `CaganRE.forcing_adapted` |
| Cochrane (19.6), p. 436 | the steady state `p̄ = m − y + αvr`, rising in `r` | `CaganRE.pbar`, `CaganRE.steady_state_iff`, `CaganRE.steady_state_strictMono_r` |
| Cochrane (19.7), p. 436 | with constant money the equilibria are the processes with `E_tp_{t+1} − p̄ = θ(p_t − p̄)` | `CaganRE.eq197_iff` |
| Cochrane p. 437 | "the full set of solutions": the family `p_t − p̄ = θᵗ(p_0 − p̄) + ∑θ^{t−j}δ_j`; every member with `E_tδ_{t+1} = 0` solves, and every solution is a member | `CaganRE.caganFamily`, `CaganRE.caganFamily_closed`, `CaganRE.caganFamily_adapted`, `CaganRE.caganFamily_E_succ`, `CaganRE.caganFamily_solves`, `CaganRE.eq_caganFamily` |
| Cochrane p. 437 | "the alternative solutions are explosive", under perfect foresight and in expectation; a solution is bounded iff it is the steady state | `CaganRE.pf_path`, `CaganRE.pf_explodes`, `CaganRE.expected_path`, `CaganRE.expected_explodes`, `CaganRE.bounded_iff_steady` |
| Cochrane p. 437 | multiplicity: an uncountable set of perfect-foresight paths, and a sunspot path under genuine uncertainty that starts at `p̄` but is not the steady state | `CaganRE.pf_solutions_uncountable`, `CaganRE.coinShock_adapted`, `CaganRE.coin_sunspot_solves`, `CaganRE.coin_sunspot_ne_steady` |
| Cochrane (19.8), p. 437 | the forward iteration at finite horizon; the limit term exists iff the series converges; for bounded money it exists; it vanishes iff the solution is bounded; exactly one bounded solution | `CaganRE.eq198_finite`, `CaganRE.eq198`, `CaganRE.eq198_bounded_money`, `CaganRE.limit_zero_iff_bounded`, `CaganRE.bounded_existsUnique` |
| Cochrane pp. 437–438 | the valuation equation picks `P_0`; exactly one price path; it is bounded iff `B_{−1} = e^{p̄}∑βʲs_j`, so generically explosive | `CaganRE.fiscal_selects_P0`, `CaganRE.fiscal_path_existsUnique`, `CaganRE.fiscal_path_bounded_iff` |
| Cochrane p. 438 | `ΔE_{t+1}`; the stochastic valuation equation picks unexpected inflation, and with expected inflation determines `B_t` | `CaganRE.innov`, `CaganRE.valuation_split`, `CaganRE.stochastic_selection` |

## §19.3.1 Money in utility: budget constraints and first-order conditions, pp. 438–441 (MoneyInUtility)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (19.10), p. 439 | the household flow budget is the government's flow constraint with `s` replaced by `s + c − y` | `MoneyInUtility.HHFlow`, `MoneyInUtility.hhFlow_iff_flow` |
| Cochrane (19.11)–(19.12), p. 439 | (19.11) holds iff the transversality condition does; with both transversality conditions (19.12) holds | `MoneyInUtility.eq1911_iff_tvc`, `MoneyInUtility.eq1912_of_tvc` |
| Cochrane p. 440 | with `c = y` the household's (19.12) is the government's (19.3) | `MoneyInUtility.equilibrium_valuation` |
| Cochrane (19.9), p. 439; footnote 1, p. 440 | the time-0 problem under perfect foresight: feasible and optimal plans | `MoneyInUtility.Feasible`, `MoneyInUtility.Optimal` |
| Cochrane footnote 1, p. 440 | perturbation tools: a two-date change of a summable sequence; a cost-neutral two-date change cannot raise utility | `MoneyInUtility.tsum_modify_two`, `MoneyInUtility.perturb_le` |
| Cochrane (19.13)–(19.14), p. 440 | necessity: cross-date conditions, then `βᵗu_c = λΛ_t/Λ_0` and `βᵗu_m = λ(Λ_t/Λ_0)i_t/(1 + i_t)` with `λ = u_c(c_0, m_0)` | `MoneyInUtility.foc_cc`, `MoneyInUtility.foc_mc`, `MoneyInUtility.foc_1913_1914` |
| Cochrane (19.13)–(19.14), p. 440 | sufficiency under joint concavity (tangent line restated from the `IntertemporalModel` project) | `MoneyInUtility.concave_le_tangent`, `MoneyInUtility.supergradient_of_concave`, `MoneyInUtility.optimal_of_foc` |
| Cochrane footnote 1, p. 440 (under uncertainty) | the problem on a finite event tree: node-contingent plans, date-`t` cost and utility, feasibility and optimality; node indicators and node perturbations | `MoneyInUtility.FootnoteTree.TAdapted`, `MoneyInUtility.FootnoteTree.dateCost`, `MoneyInUtility.FootnoteTree.dateUtil`, `MoneyInUtility.FootnoteTree.TFeasible`, `MoneyInUtility.FootnoteTree.TOptimal`, `MoneyInUtility.FootnoteTree.cell`, `MoneyInUtility.FootnoteTree.cell_adapted`, `MoneyInUtility.FootnoteTree.sum_perturb_cell`, `MoneyInUtility.FootnoteTree.perturb_adapted`, `MoneyInUtility.FootnoteTree.tperturb_le` |
| Cochrane (19.13)–(19.14), p. 440 (under uncertainty) | necessity at every node of the tree; with one root node `λ` is the same in every state; sufficiency under concavity | `MoneyInUtility.FootnoteTree.tree_foc_cc`, `MoneyInUtility.FootnoteTree.tree_foc_mc`, `MoneyInUtility.FootnoteTree.tree_foc_1913_1914`, `MoneyInUtility.FootnoteTree.lambda_const`, `MoneyInUtility.FootnoteTree.tree_optimal_of_foc` |
| Cochrane p. 441; p. 449 | with pull-out, known variables are closed under products, reciprocals and quotients on any state space, and under every function on a finite one | `MoneyInUtility.known_mul`, `MoneyInUtility.known_inv`, `MoneyInUtility.known_div`, `MoneyInUtility.known_prod`, `MoneyInUtility.functionsKnown_of_fintype`, `MoneyInUtility.known_div_of_fintype` |
| Cochrane (19.11)–(19.12), p. 439; (19.15)–(19.16), p. 441 | the budget and value-of-money theorems with the knownness of `Λ_t/P_t` and `P_t/u_c(t)` derived from adaptedness | `MoneyInUtility.eq1911_iff_tvc_adapted`, `MoneyInUtility.eq1912_of_tvc_adapted`, `MoneyInUtility.value_of_money_iterated_adapted`, `MoneyInUtility.value_of_money_limit_adapted` |
| Cochrane (19.15)–(19.16), p. 441 | `1 = u_m/u_c + E_tβu_c′P/(u_cP′)`; the value of a dollar `v_t = u_m(t)/P_t + βE_tv_{t+1}` | `MoneyInUtility.convenience_identity`, `MoneyInUtility.value_recursion` |
| Cochrane p. 441 | "an asset-pricing view of the value of money": the iterated formula, and the value of a dollar as the present value of its liquidity dividends | `MoneyInUtility.value_of_money_iterated`, `MoneyInUtility.value_of_money_limit` |
| Cochrane (19.16), p. 441 (restated from the Woodford Chapter 2 project) | money demand `M = PL(y, i)` has at most one positive solution, and one under boundary conditions | `MoneyInUtility.lm_unique`, `MoneyInUtility.lm_exists` |

## §19.3.2 Equilibrium and multiple equilibria, pp. 441–445 (MoneyInUtility, MoneyTargetingDynamics)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (19.17)–(19.18), p. 442 | `P_t/P_{t+1} = (m_{t+1}/m_t)(M_t/M_{t+1})`; with separable utility and `c = y`, (19.17) is (19.18); the paths of (19.18) | `MoneyInUtility.price_ratio_eq`, `MoneyInUtility.eq1918_iff`, `MoneyInUtility.IsMIUPath` |
| Cochrane (19.18), p. 442 | with money growth `1 + µ`, (19.18) is Woodford's separable map | `MoneyTargetingDynamics.miuPath_iff_sepPath` |
| Cochrane (19.19), p. 442 | constant real balances iff `u_m/u_c = 1 − β/(1 + µ)`; inflation equals money growth; existence and uniqueness of the steady state | `MoneyInUtility.steady_state_path_iff`, `MoneyInUtility.steady_state_inflation`, `MoneyInUtility.steady_state_existsUnique` |
| Cochrane p. 443 | at `i = 0`, `u_m = 0` and `P_{t+1}/P_t = β ≈ 1 − δ`; satiation is absorbing; `i → 0` as `m → ∞`; the money demand correspondence | `MoneyInUtility.zero_rate_iff`, `MoneyInUtility.deflation_approx`, `MoneyInUtility.satiation_absorbing`, `MoneyInUtility.limit_rate_zero`, `MoneyInUtility.money_demand_correspondence` |
| Cochrane (19.20), p. 443 | power utility: `u_c = c^{−γ}`, `u_m = θm^{−γ}`, `u_m/u_c = θ(Py/M)^γ`; the inverse power demand; `M = Py(i/(θ(1 + i)))^{−1/γ}` | `MoneyInUtility.hasDerivAt_power`, `MoneyInUtility.power_um_ratio`, `MoneyInUtility.power_demand_iff`, `MoneyInUtility.power_money_demand` |
| Cochrane (19.21)–(19.22), p. 444 | the paths of (19.21) in `x = Py/M`; the steady state `θx̄^γ = 1 − 1/((1 + δ)(1 + µ)) ≈ δ + µ`, exactly and with error at most `(δ + µ)²` | `MoneyInUtility.IsPowerPath`, `MoneyInUtility.eq1922`, `MoneyInUtility.eq1922_exact`, `MoneyInUtility.eq1922_partial_delta`, `MoneyInUtility.eq1922_partial_mu`, `MoneyInUtility.eq1922_approx` |
| Cochrane p. 444 | calibration: `θ ≈ δ + µ` at `Py/M = 1`; at `Py/M = 10`, `θ = 0.01` for `γ = 1` but `0.001` for the figure's `γ = 2`; the interest cost of one tenth of a year's income | `MoneyInUtility.calib_unit`, `MoneyInUtility.calib_ten`, `MoneyInUtility.calib_ten_gamma_one`, `MoneyInUtility.calib_ten_gamma_two`, `MoneyInUtility.calib_interest_cost` |
| Cochrane (19.23), p. 444 | the map `x ↦ x(1 − θx̄^γ)/(1 − θx^γ)`; (19.21) iff the map; the inflation display; fixed point, positivity and single crossing | `MoneyInUtility.nextX`, `MoneyInUtility.eq1923_iff`, `MoneyInUtility.inflation_eq1923`, `MoneyTargetingDynamics.nextX_fixed`, `MoneyTargetingDynamics.nextX_pos`, `MoneyTargetingDynamics.nextX_lt_iff` |
| Cochrane Figure 19.1, p. 444 | `δ = µ = 0.2`, `γ = 2`, `θ = 0.01`: `x̄ = √(275/9)`, `θx̄^γ = 11/36`, `5.52 < x̄ < 5.53` | `MoneyInUtility.xbar191`, `MoneyInUtility.fig191_steady`, `MoneyInUtility.fig191_xbar_bounds` |
| Cochrane p. 444; Figure 19.1 | the slope at `x̄` is `1 + γθx̄^γ/(1 − θx̄^γ) > 1`, exactly `47/25` in the figure; the pole at `x = 10`; `P_{t+1}/P_t → 1/(1 + δ)` as `x → 0` | `MoneyInUtility.nextX_hasDerivAt`, `MoneyInUtility.slope_gt_one`, `MoneyInUtility.fig191_slope`, `MoneyInUtility.fig191_pole`, `MoneyInUtility.deflation_limit` |
| Cochrane p. 444 | "an unstable unique locally bounded equilibrium": the steady state repels, in general and in the figure | `MoneyTargetingDynamics.power_steady_repelling`, `MoneyTargetingDynamics.fig191_repelling` |
| Cochrane p. 444 | paths below `x̄` decrease to the deflationary steady state, with `x_{t+1}/x_t → β/(1 + µ)` and `P_{t+1}/P_t → β`; paths above `x̄` reach `θx^γ ≥ 1` in finite time | `MoneyTargetingDynamics.power_deflation_orbit`, `MoneyTargetingDynamics.power_deflation_inflation`, `MoneyTargetingDynamics.power_inflation_exits` |
| Cochrane pp. 444–445 (E13) | the zero-rate steady state attracts iff `1 + µ > β`, not `1 + µ > 1/β`; `β = 5/6`, `µ = 0` separates the two | `MoneyInUtility.e13_corrected`, `MoneyInUtility.e13_printed_fails`, `MoneyTargetingDynamics.e13_no_deflation_attractor` |
| Cochrane p. 445 | adding the valuation equation pins `P_0`, hence the whole path | `MoneyInUtility.fiscal_determines_path` |

## Restated from the Woodford Chapter 2 project: global dynamics of monetary targeting, pp. 442–445 (MoneyTargetingDynamics)

| Book | Claim | Lean |
| --- | --- | --- |
| Woodford (2003) §4.1, pp. 125–127 (survey lemma L5) | monotone orbits, limits of orbits are fixed points, slope above one repels, slope below one attracts | `MoneyTargetingDynamics.orbit_monotone_of_le`, `MoneyTargetingDynamics.orbit_antitone_of_ge`, `MoneyTargetingDynamics.fixed_of_tendsto`, `MoneyTargetingDynamics.monotone_orbit_atTop_or_fixed`, `MoneyTargetingDynamics.antitone_orbit_atBot_or_fixed`, `MoneyTargetingDynamics.sign_near_of_deriv_pos`, `MoneyTargetingDynamics.repelling_of_one_lt_abs_deriv`, `MoneyTargetingDynamics.attracting_of_abs_deriv_lt_one` |
| Woodford (2003) (4.7)–(4.8), p. 129; Cochrane (19.17), p. 442 | `F`, `G` and the general map; the Fisher equation iff `G(m_{t+1}) = (μ̄/β)F(m_t)`; its paths | `MoneyTargetingDynamics.Ffun`, `MoneyTargetingDynamics.Gfun`, `MoneyTargetingDynamics.eq48_iff_fisher`, `MoneyTargetingDynamics.IsPath48` |
| Woodford (2003) p. 130, Figure 2.5; Cochrane (19.18)–(19.19), p. 442 | the separable map, its shape, the second steady state at zero, the steady state `m*` and single crossing | `MoneyTargetingDynamics.sepF`, `MoneyTargetingDynamics.sepMap`, `MoneyTargetingDynamics.eq48_sep_iff`, `MoneyTargetingDynamics.sepF_pos`, `MoneyTargetingDynamics.sepF_strictMonoOn`, `MoneyTargetingDynamics.sepF_tendsto_zero`, `MoneyTargetingDynamics.sepMap_tendsto_zero`, `MoneyTargetingDynamics.sepMap_fixed_iff`, `MoneyTargetingDynamics.sep_exists_steady_state`, `MoneyTargetingDynamics.sep_single_crossing` |
| Woodford (2003) pp. 130–131; Cochrane p. 444 | one path per initial value; self-fulfilling inflations and deflations | `MoneyTargetingDynamics.IsSepPath`, `MoneyTargetingDynamics.sep_path_exists_unique`, `MoneyTargetingDynamics.sep_inflation_path`, `MoneyTargetingDynamics.sep_deflation_path` |
| Woodford (2003) pp. 131–133; Cochrane p. 443 | satiation: the path grows at `μ̄/β`, violates the transversality condition when `μ̄ ≥ 1`, and gives a continuum of equilibria when `β < μ̄ < 1` | `MoneyTargetingDynamics.Satiation`, `MoneyTargetingDynamics.satiated_path`, `MoneyTargetingDynamics.money_tvc_violated`, `MoneyTargetingDynamics.sep_deflation_violates_tvc`, `MoneyTargetingDynamics.money_contraction_continuum` |

## §19.4 Pruning equilibria, pp. 445–447, and Online Appendix §3.1, pruning deflationary equilibria, pp. 612–618 (PruningDeflation)

§19.4 is verbal and defers to Online Appendix Chapter 3; its claims are the rows of this and the
next three sections.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (19.18)–(19.21), pp. 442–444 | power marginal utilities; `u_m/u_c = θ(M/(Py))^{−γ}`; (19.18) in the power case | `PruningDeflation.umPow`, `PruningDeflation.ucPow`, `PruningDeflation.um_div_uc_pow`, `PruningDeflation.foc_power_iff` |
| A3 p. 612 | `m_{t+1}/m_t = (1 + δ)(1 + µ)(1 − θx_t^γ)`, increasing towards `(1 + δ)(1 + µ)` as `x ↘ 0` | `PruningDeflation.ratioMap`, `PruningDeflation.ratio_of_foc`, `PruningDeflation.growth_factor_eq`, `PruningDeflation.ratio_strictAntiOn`, `PruningDeflation.ratio_tendsto` |
| Cochrane (19.22)–(19.23), p. 444; A3 (3.3), p. 619 | in `x = 1/m` the map is (19.23); the fixed point; exactly one steady state when `β < 1 + µ` | `PruningDeflation.eq1923_iff`, `PruningDeflation.fixed_iff`, `PruningDeflation.steady_exists_unique` |
| A3 p. 612; Cochrane p. 444 | deflationary paths from `m_0 > m̄` exist, grow geometrically and without bound | `PruningDeflation.IsMPath`, `PruningDeflation.deflation_growth`, `PruningDeflation.deflation_tendsto_atTop`, `PruningDeflation.deflation_path_exists` |
| A3 p. 613 | the transversality term `β^{T+1}M_T/(P_{T+1}y)` and its recursion; a lower bound `C(1 + µ)^T` along deflations | `PruningDeflation.tvcTerm`, `PruningDeflation.tvcTerm_eq`, `PruningDeflation.scaled_succ`, `PruningDeflation.scaled_lower_bound` |
| A3 pp. 612–613 (E17) | the transversality condition fails along a deflation iff `µ ≥ 0`: it holds for `µ < 0`, tends to a positive constant at `µ = 0` and diverges for `µ > 0` | `PruningDeflation.tvc_tendsto_zero_of_neg`, `PruningDeflation.tvc_not_tendsto_zero`, `PruningDeflation.tvc_tendsto_zero_iff`, `PruningDeflation.tvc_mu_zero`, `PruningDeflation.tvc_mu_pos` |
| A3 pp. 613, 617 (E17) | for `β < 1 + µ < 1` the deflations are a continuum of equilibria; for `1 + µ ≤ β` there are none; the threshold is `µ > −δ/(1 + δ)`, not `µ > −δ` (`δ = 1`, `µ = −0.6`) | `PruningDeflation.deflation_continuum`, `PruningDeflation.no_deflation_of_le_beta`, `PruningDeflation.survival_threshold`, `PruningDeflation.survival_counterexample` |
| A3 p. 613 | a general bound used for the lower bound, `exp(−a/(1 − a₀)) ≤ 1 − a` | `PruningDeflation.exp_le_one_sub` |
| A3 p. 613; p. 443 | at satiation `P_{t+1} = βP_t` and `i = 0` | `PruningDeflation.deflation_at_satiation` |
| A3 (3.1), p. 614 | `(M_t − M_{t−1})/P_t = −s_t`; `P_t = βᵗP_0`; discounted surpluses | `PruningDeflation.flow_nodebt_iff`, `PruningDeflation.price_geometric`, `PruningDeflation.discounted_surplus` |
| A3 p. 614 | the finite present-value identity, telescoped: "final money equals initial money plus added money" | `PruningDeflation.pv_finite`, `PruningDeflation.pv_finite_telescoped`, `PruningDeflation.final_money_eq` |
| A3 p. 614 | the final term grows at `(1 + µ)^T`; the present value of surpluses tends to `−∞`; no equilibrium with positive money growth, active or passive; a passive policy needs falling money and a positive surplus | `PruningDeflation.tvc_term_growth`, `PruningDeflation.pv_surplus_tendsto_bot`, `PruningDeflation.no_eqm_positive_growth`, `PruningDeflation.passive_requires_negative_growth` |
| A3 p. 615 | "eventually constant or declining", made precise: the transversality condition holds iff nominal money tends to zero | `PruningDeflation.tvc_iff_money_vanishes` |
| A3 (19.12), pp. 614–615 | the infinite-horizon form; a determinate price level `P_0 = M_{−1}/S` with no money demand, and none when `S ≤ 0` | `PruningDeflation.tvc_limit`, `PruningDeflation.tvc_iff_pv`, `PruningDeflation.price_level_determined`, `PruningDeflation.no_price_level_of_nonpos_pv` |
| A3 §3.1.2, pp. 615–616 | open-market operations: `B_t + M_t = βᵗ(B_0 + M_0)`, constant real debt, closed-form bonds, negative bonds, money and bonds exploding in opposite directions, the transversality condition and the present value hold | `PruningDeflation.omo_total_debt`, `PruningDeflation.omo_real_debt_const`, `PruningDeflation.omo_bonds`, `PruningDeflation.omo_bonds_eventually_neg`, `PruningDeflation.omo_explode`, `PruningDeflation.omo_tvc`, `PruningDeflation.omo_pv` |
| A3 (3.2), p. 616 | the last-period condition `u_c = u_m`, its sufficiency under concavity, and the power case `m = θ^{1/γ}c` | `PruningDeflation.last_period_foc`, `PruningDeflation.last_period_foc_sufficient`, `PruningDeflation.last_period_power_demand` |
| A3 pp. 616–617 | the iterated budget with interest; with separable utility higher consumption raises desired money | `PruningDeflation.iterated_budget`, `PruningDeflation.separable_money_demand_rises` |

## Online Appendix §§3.2–3.2.1, pruning inflationary equilibria, pp. 618–621 (PruningInflation)

| Book | Claim | Lean |
| --- | --- | --- |
| A3 p. 619 | the demonetisation level `m_p = θ^{1/γ}`: the map is zero there, negative below; `θm^{−γ} ≤ 1` iff `m ≥ m_p` | `PruningInflation.wp_spec`, `PruningInflation.ratioMap_wp`, `PruningInflation.le_one_iff`, `PruningInflation.ratioMap_neg` |
| Cochrane Figure 19.1, p. 444 | the map is continuous, increasing above `m_p`, below the diagonal on `[m_p, m̄)` and above it on `[m̄, ∞)`; `m_p < m̄`; `m̄` is the only fixed point | `PruningInflation.ratioMap_strictMonoOn`, `PruningInflation.ratioMap_continuousOn`, `PruningInflation.wp_lt_ms`, `PruningInflation.ratioMap_lt_self`, `PruningInflation.self_le_ratioMap`, `PruningInflation.fixed_unique` |
| A3 (3.3), p. 619 (E22) | "the price level eventually explodes to infinity in finite time": every orbit from below `m̄` reaches `m_p`; no path with valued money starts below `m̄` | `PruningInflation.finite_time_explosion`, `PruningInflation.explosion_x_form`, `PruningInflation.no_positive_path_below` |
| A3 §3.2.1, p. 619 | equilibrium in real balances with the value of money `q = 1/P ≥ 0`; terminal balances `M_T = P_Tyθ^{1/γ}` and price `P_T = (M_T/y)θ^{−1/γ}` | `PruningInflation.IsEqm`, `PruningInflation.eqm_of_value`, `PruningInflation.terminal_balance`, `PruningInflation.terminal_price` |
| A3 p. 619; Figure 3.1 | "we work back from this terminal condition": the backward sequence exists, is unique, increases and accumulates at `m̄` | `PruningInflation.IsBackward`, `PruningInflation.backward_exists`, `PruningInflation.backward_unique`, `PruningInflation.backward_strictMono`, `PruningInflation.backward_tendsto` |
| A3 p. 619 | "not a continuum of inflationary equilibria, but a countable number": every equilibrium below `m̄` demonetises at a backward value, each backward value starts one, `m_0 ≥ m̄` never demonetises; the complete classification | `PruningInflation.eqm_demonetises`, `PruningInflation.eqm_of_backward`, `PruningInflation.eqm_of_ge`, `PruningInflation.eqm_initial_iff`, `PruningInflation.inflationary_initial_countable`, `PruningInflation.not_eqm_of_lt_wp`, `PruningInflation.not_eqm_between` |
| A3 (3.4)–(3.5), p. 620 | discrete and continuous money demand; their limits as `i → ∞`; their ratio `(1 + i)^{1/γ}` tends to one as `i → 0` | `PruningInflation.mdDisc`, `PruningInflation.mdCont`, `PruningInflation.md_discrete_iff`, `PruningInflation.md_discrete_tendsto`, `PruningInflation.md_cont_tendsto`, `PruningInflation.md_ratio`, `PruningInflation.md_ratio_tendsto` |
| A3 p. 620 | the modified utility, its exact partial derivatives, and (3.5) as its first-order condition | `PruningInflation.modU`, `PruningInflation.modU_hasDerivAt_c`, `PruningInflation.modU_hasDerivAt_m`, `PruningInflation.modified_foc_iff` |
| A3 p. 621 | the new difference equation, its steady state and `x`-form; it never reaches infinity in finite time; a continuum of inflationary equilibria with inflation rising without bound | `PruningInflation.newMap`, `PruningInflation.new_map_of_foc`, `PruningInflation.new_fixed_iff`, `PruningInflation.new_x_form`, `PruningInflation.new_map_pos`, `PruningInflation.new_inflation_tendsto_zero`, `PruningInflation.new_inflation_rate_tendsto`, `PruningInflation.new_inflationary_continuum` |

## Online Appendix §§3.2.2–3.2.3, the Obstfeld–Rogoff fix, pp. 621–629 (ObstfeldRogoff)

| Book | Claim | Lean |
| --- | --- | --- |
| A3 (3.6), p. 623 | the Euler equation in levels, in the value of money and in real balances; the steady state `v′(m̿) = (1 − β)u′(y)`; the terminal level `v′(M/P̄) = u′(y)` | `ObstfeldRogoff.eq36_iff_value`, `ObstfeldRogoff.eq36_real`, `ObstfeldRogoff.steady_iff`, `ObstfeldRogoff.terminal_iff` |
| A3 p. 626 | the redemption first-order condition at `T`; "a small decrease in the price level `P_T < P̄`" | `ObstfeldRogoff.redemption_foc_zero`, `ObstfeldRogoff.redemption_raises_balance` |
| A3 Figure 3.2, p. 624 | `v′(m) = 1/√m`; steady state `m = 4`; terminal level `M/P̄ = 1`; the backward step; `1 + √3/2 ≈ 1.866` and `(3 + 2√2)/4 ≈ 1.457` | `ObstfeldRogoff.figVp`, `ObstfeldRogoff.fig32_vp_eq_rpow`, `ObstfeldRogoff.fig32_vp_strictAnti`, `ObstfeldRogoff.fig32_steady`, `ObstfeldRogoff.fig32_terminal`, `ObstfeldRogoff.fig32_back`, `ObstfeldRogoff.fig32_back_spec`, `ObstfeldRogoff.fig32_eps0`, `ObstfeldRogoff.fig32_eps_half`, `ObstfeldRogoff.fig32_numbers` |
| A3 Figure 3.2 caption, p. 624 (E18) | the caption's `v(m) = m^{−1/2}` is decreasing and admits neither the steady state nor the terminal level; `v = 2√m` has `v′ = m^{−1/2}` | `ObstfeldRogoff.e18_caption_decreasing`, `ObstfeldRogoff.e18_no_steady_state`, `ObstfeldRogoff.e18_correct_v` |
| A3 p. 624 (Obstfeld–Rogoff (1983)) | with one-way redemption and the arbitrage bound `q_t ≥ ε`, real balances never fall below `m̿`: no hyperinflation path | `ObstfeldRogoff.IsORPath`, `ObstfeldRogoff.or_balance_step`, `ObstfeldRogoff.or_no_hyperinflation` |
| A3 pp. 624–625 | two-way conversion stops the inflation, but needs the government to sell money | `ObstfeldRogoff.two_way_steady`, `ObstfeldRogoff.two_way_needs_sale` |
| A3 pp. 625–627 | with a one-time redemption of the money carried out of `T`, the demonetised path is optimal for the price-taking household (a Walrasian equilibrium), and violates Obstfeld and Rogoff's bound | `ObstfeldRogoff.cochrane_sum_identity`, `ObstfeldRogoff.cochrane_household_optimal`, `ObstfeldRogoff.cochrane_violates_or_bound` |
| A3 pp. 626–627 | if the redemption offer also stands for dollars acquired at `q_{T+1} = 0`, the household has no optimum | `ObstfeldRogoff.standing_redemption_no_optimum` |
| A3 Figure 3.2, pp. 624–627 | the "ε = 0.5" path solves (3.6) and the redemption condition and is household-optimal for every `T` | `ObstfeldRogoff.fig32_v_supergradient`, `ObstfeldRogoff.fig32_cochrane_path`, `ObstfeldRogoff.fig32_cochrane_optimal` |

## Online Appendix §3.2.4, nonseparable utility, pp. 629–632; p. 445 (Nonseparable)

| Book | Claim | Lean |
| --- | --- | --- |
| A3 (3.8), p. 630 | `u_m/u_c = i/(1 + i) = 1 − Q` | `Nonseparable.foc38_iff` |
| A3 (3.7), p. 630 | the log discount factor has derivative `−γa − ηb` with `η = −mu_cm/u_c`; `log(1 + r^f)` has derivative `γa + ηb`; the printed `η = −u_cm/u_c` is the coefficient of a level change | `Nonseparable.sdf_log_hasFDerivAt`, `Nonseparable.rf_log_hasFDerivAt`, `Nonseparable.sdf_level_hasDerivAt` |
| A3 p. 630, footnote 1 | `d log(e^{−δt}u_c)/dt = −δ + (cu_cc/u_c)(ċ/c) + (mu_cm/u_c)(ṁ/m)` | `Nonseparable.ct_footnote` |
| A3 p. 631 | Obstfeld (1984) utility `−c^{−a}m^{−b}`: exact partials (the printed ones have sign typos), the marginal rate of substitution, the ratio of marginal utilities, the first-order condition | `Nonseparable.obs_uc`, `Nonseparable.obs_um`, `Nonseparable.obs_printed_typo`, `Nonseparable.obs_mrs`, `Nonseparable.obs_uc_ratio`, `Nonseparable.obs_foc` |
| A3 p. 631 | the equilibrium map (needs `m_t > b/a`), its steady state `m̄ = (b/a)A/(A − 1)` and relative form | `Nonseparable.obsRatio`, `Nonseparable.obsMap`, `Nonseparable.obs_map_iff`, `Nonseparable.obs_steady_iff`, `Nonseparable.obs_relative` |
| A3 pp. 631–632 (E19) | the derivative of `m_{t+1}/m_t` at `m̄` is `(b/a)(1 + i)/((1 − b)m̄²)`; the printed coefficient misses `1 + i`; the map has slope `1 − i/(b − 1)` | `Nonseparable.obs_ratio_hasDerivAt`, `Nonseparable.e19_printed_coefficient`, `Nonseparable.obs_map_hasDerivAt` |
| A3 p. 631; Cochrane p. 445 (E19) | the phase diagram cuts from above iff `b > 1`, but the steady state is stable iff `b > 1 + i/2`; `b = 1.04`, `i = 0.1025` has slope `−1.5625` | `Nonseparable.obs_cuts_from_above_iff`, `Nonseparable.obs_stable_iff`, `Nonseparable.e19_counterexample` |
| A3 pp. 631–632 | local attraction and repulsion (corollaries of the orbit lemmas); a continuum of convergent equilibria satisfying the transversality condition for `b > 1 + i/2`; local uniqueness for `1 < b < 1 + i/2` | `Nonseparable.local_contraction`, `Nonseparable.local_repulsion`, `Nonseparable.obs_multiple_stable`, `Nonseparable.obs_locally_unique` |
| A3 p. 632 | CES utility: `u_c`, `u_m`, the discount factor (power utility with constant `M/(Py)`), the marginal rate of substitution, money demand, unit income elasticity and interest elasticity `1/(ρ − 1)` | `Nonseparable.cesU`, `Nonseparable.ces_uc`, `Nonseparable.ces_um`, `Nonseparable.ces_uc_form`, `Nonseparable.ces_sdf`, `Nonseparable.ces_sdf_const`, `Nonseparable.ces_mrs`, `Nonseparable.ces_money_demand_iff`, `Nonseparable.ces_income_elasticity`, `Nonseparable.ces_interest_elasticity` |

## §19.5 The cash-in-advance model, pp. 447–455 (CashInAdvance)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (19.27)–(19.30), p. 449 | forward iteration with expectations (the case `a = 1` of `ForwardSolution.iterate_A15`); valuation iff transversality; normalising by `Λ_t` | `CashInAdvance.Stochastic.E_ratio`, `CashInAdvance.Stochastic.telescope`, `CashInAdvance.Stochastic.pv_iff_tvc`, `CashInAdvance.Stochastic.normalise_iff` |
| Cochrane (19.27), (19.29)–(19.30), p. 449 | the money-creation and interest-cost flows; `1 − Q = i/(1 + i)`; the flow budget in each form; adaptedness | `CashInAdvance.Stochastic.gB`, `CashInAdvance.Stochastic.gBM`, `CashInAdvance.Stochastic.interest_cost_eq`, `CashInAdvance.Stochastic.flow_step_B`, `CashInAdvance.Stochastic.flow_step_BM`, `CashInAdvance.Stochastic.gB_adapted`, `CashInAdvance.Stochastic.gBM_adapted` |
| Cochrane (19.28)–(19.30), p. 449 | the bond transversality condition iff (19.29); (19.28) iff (19.30) | `CashInAdvance.Stochastic.pv_19_29`, `CashInAdvance.Stochastic.pv_19_30` |
| Cochrane (19.28)–(19.30), p. 449 | given (19.28), (19.29) needs the money transversality condition; a path satisfying (19.27), (19.28) and (19.30) but not (19.29) | `CashInAdvance.Stochastic.tvc_B_iff_money_tvc`, `CashInAdvance.Stochastic.pv_19_29_needs_money_tvc` |
| Cochrane (19.34)–(19.35), p. 450 | the flows at `c = y` | `CashInAdvance.Stochastic.gB_market_clearing`, `CashInAdvance.Stochastic.gBM_market_clearing` |
| Cochrane (19.32), p. 450 | `Q_t = βE_t[(u′(y_{t+1})/u′(y_t))(P_t/P_{t+1})]` given `Λ_t = βᵗu′(y_t)` | `CashInAdvance.Stochastic.bond_price_19_32` |
| Cochrane (19.27), (19.30), p. 449 | the cost `QW + (1 − Q)M` of carrying wealth; optimal overnight money | `CashInAdvance.MoneyDemand.portfolioCost`, `CashInAdvance.MoneyDemand.IsOptimalMoney`, `CashInAdvance.MoneyDemand.portfolioCost_eq` |
| Cochrane (19.33), (19.37), pp. 450–454 | the money-demand correspondence: the minimum at `Q < 1`, every `M ≥ M_min` at `Q = 1`, no optimum at `Q > 1` | `CashInAdvance.MoneyDemand.optimal_iff`, `CashInAdvance.MoneyDemand.optimal_iff_of_lt_one`, `CashInAdvance.MoneyDemand.optimal_iff_of_eq_one`, `CashInAdvance.MoneyDemand.unbounded_of_one_lt`, `CashInAdvance.MoneyDemand.no_optimum_of_one_lt` |
| Cochrane (19.24)–(19.25), pp. 448–449 | the minimum overnight money `Pc/V + P(y − c)`, `Py/V` at `c = y` | `CashInAdvance.MoneyDemand.overnight_feasible_iff`, `CashInAdvance.MoneyDemand.overnight_min_clear` |
| Cochrane (19.33), p. 450; (19.37), p. 452; p. 454 | Fact 2: `MV = Py` at `i > 0`; the frictionless `M = 0`; the L-shaped demand | `CashInAdvance.MoneyDemand.fact2_19_33`, `CashInAdvance.MoneyDemand.fact_19_37`, `CashInAdvance.MoneyDemand.L_shaped_demand` |
| Cochrane pp. 450–453 (E14) | `i > 0` iff `Q < 1`; `i ≥ 0` iff `Q ≤ 1`; the printed `Q_t ≥ 1` means `i ≤ 0` | `CashInAdvance.MoneyDemand.Q_lt_one_iff`, `CashInAdvance.MoneyDemand.Q_le_one_iff`, `CashInAdvance.MoneyDemand.E14_one_le_Q_iff` |
| Cochrane p. 450 | the `V ≠ 1` wedge: the effective price of consumption is `1 + (1 − Q)(1/V − 1)`, equal to one iff `Q = 1` or `V = 1` | `CashInAdvance.MoneyDemand.binding_cost_wedge`, `CashInAdvance.MoneyDemand.wedge_eq_one_iff` |
| Cochrane §19.5.1, p. 448; footnote 1, p. 440 | the perfect-foresight consumption problem; it is the money-in-utility problem with no money | `CashInAdvance.Euler.lifetimeU`, `CashInAdvance.Euler.Admissible`, `CashInAdvance.Euler.IsOptimalPlan`, `CashInAdvance.Euler.isOptimalPlan_iff_optimal` |
| Cochrane (19.31), p. 450; p. 453 | Fact 1 from optimality: necessity by a two-date perturbation, sufficiency under concavity | `CashInAdvance.Euler.euler_necessary`, `CashInAdvance.Euler.euler_sufficient` |
| Cochrane (19.31), p. 450; (19.36), p. 452 | `βʲu′(y_{t+j})/u′(y_t) = Λ_{t+j}/Λ_t`; `β^j` with a constant endowment; with `V ≠ 1`, `Λ_{t+1}/Λ_t = βw_t/w_{t+1}` | `CashInAdvance.Euler.sdf_19_31`, `CashInAdvance.Euler.sdf_const_endowment`, `CashInAdvance.Euler.sdf_wedge` |
| Cochrane §19.5.1, pp. 448–449 (under uncertainty) | the problem on a finite event tree with `V = 1`: measurable plans, expected utility, present-value cost, admissible and optimal plans; the binding overnight money is `Py` | `CashInAdvance.TreeEuler.Meas`, `CashInAdvance.TreeEuler.expU`, `CashInAdvance.TreeEuler.pvCost`, `CashInAdvance.TreeEuler.Admissible`, `CashInAdvance.TreeEuler.IsOptimal`, `CashInAdvance.TreeEuler.cia_min_V1` |
| Cochrane (19.31), p. 450; p. 453 (under uncertainty) | node-level necessity and sufficiency; (19.31) state by state; `Λ_t = βᵗu′(y_t)` derived | `CashInAdvance.TreeEuler.euler_necessary`, `CashInAdvance.TreeEuler.euler_sufficient`, `CashInAdvance.TreeEuler.sdf_19_31`, `CashInAdvance.TreeEuler.sdf_eq` |
| Cochrane (19.32), p. 450 (under uncertainty) | the bond price from household optimality on the tree | `CashInAdvance.TreeEuler.bond_price_from_optimality` |
| Cochrane (19.32), p. 450 (E15); p. 454 | `Q_t = βP_t/P_{t+1}` equals `β` iff the price level is constant; `Q = 1` along `P_t = βᵗP_0`; `Q = β/(1 + µ)` along money growth | `CashInAdvance.PF.bondPrice`, `CashInAdvance.PF.bondPrice_eq_beta_iff`, `CashInAdvance.PF.bondPrice_const`, `CashInAdvance.PF.bondPrice_deflation`, `CashInAdvance.PF.bondPrice_growth` |
| Cochrane (19.27)–(19.30), (19.35), pp. 449–450 | perfect-foresight valuation iff transversality | `CashInAdvance.PF.pv_of_rec`, `CashInAdvance.PF.rec_of_flow`, `CashInAdvance.PF.valuation_iff` |
| Cochrane §§19.5.2, 19.5.4, pp. 449–452 | the frictionless and monetary equilibria; their overnight money is optimal; Fact 2 in equilibrium | `CashInAdvance.PF.FrictionlessEq`, `CashInAdvance.PF.MonetaryEq`, `CashInAdvance.PF.frictionless_money_optimal_iff`, `CashInAdvance.PF.frictionless_money_optimal`, `CashInAdvance.PF.monetary_money_optimal`, `CashInAdvance.PF.monetary_fact2` |
| Cochrane (19.35), p. 450; (19.38), p. 452 | the seigniorage terms; the valuation equations, (19.38) corrected to `(B_{t−1} + M_{t−1})/P_t`; the printed form holds iff `M_{t−1} = 0`, and fails in a zero-rate equilibrium | `CashInAdvance.PF.frictionless_seigniorage_zero`, `CashInAdvance.PF.monetary_seigniorage`, `CashInAdvance.PF.frictionless_valuation`, `CashInAdvance.PF.monetary_valuation`, `CashInAdvance.PF.printed_19_38_iff`, `CashInAdvance.PF.printed_19_38_counterexample` |
| Cochrane p. 453 | the frictionless price level is unique, `P_t = (B_{t−1} + M_{t−1})/∑βʲs_{t+j}`; "0/0" with no debt | `CashInAdvance.PF.frictionless_price_unique`, `CashInAdvance.PF.frictionless_price_formula`, `CashInAdvance.PF.zero_debt_indeterminate` |
| Cochrane pp. 452–453 (E14) | `P = (1 − β)B/s` is the unique frictionless equilibrium of the example, with `Q = β < 1` | `CashInAdvance.PF.example_equilibrium`, `CashInAdvance.PF.example_unique`, `CashInAdvance.PF.E14_example` |
| Cochrane p. 453 | passive fiscal policy leaves the frictionless price level undetermined | `CashInAdvance.PF.passiveSurplus`, `CashInAdvance.PF.passive_fiscal_indeterminate` |
| Cochrane §19.5.5, p. 454 (E15) | the standard equilibrium `P_t = M_tV/y`; `i > 0` iff `1 + µ > β`, `1 + i = (1 + δ)(1 + µ)`; it fails for `1 + µ < β`; `Q ≠ β` for `µ ≠ 0` | `CashInAdvance.PF.usual_equilibrium`, `CashInAdvance.PF.usual_rate`, `CashInAdvance.PF.usual_fails_low_growth`, `CashInAdvance.PF.E15_counterexample` |
| Cochrane p. 454 | deflationary equilibria for every `1 + µ ≥ β`; discounted real money grows iff `µ > 0`, and the money transversality condition holds iff `µ < 0` | `CashInAdvance.PF.deflation_equilibrium`, `CashInAdvance.PF.deflation_real_money`, `CashInAdvance.PF.deflation_real_money_grows_iff`, `CashInAdvance.PF.deflation_money_tvc_iff` |
| Cochrane p. 454 | an active fiscal policy prunes the deflationary equilibria | `CashInAdvance.PF.active_fiscal_prunes` |
| Cochrane §19.5.3, p. 451 | the same equilibrium supports either coordination story | `CashInAdvance.PF.coordination` |

## §19.6 Unpleasant arithmetic and fiscal theory, pp. 456–457 (UnpleasantArithmetic)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (19.39), p. 456 | seigniorage `σ = (y/V)(1 − M_{t−1}/M_t)`; inflation equals money growth | `UnpleasantArithmetic.seig`, `UnpleasantArithmetic.seigniorage_eq`, `UnpleasantArithmetic.inflation_eq_growth` |
| Cochrane p. 456 | seigniorage rises with money growth, is bounded by `y/V`, and every level below `y/V` has exactly one money growth | `UnpleasantArithmetic.seig_strictMono`, `UnpleasantArithmetic.seig_lt_bound`, `UnpleasantArithmetic.any_timing` |
| Cochrane (19.40), p. 456 | with fixed surpluses the present value of seigniorage is fixed; less now is exactly that much more later; lower money growth now forces higher money growth, and inflation, later | `UnpleasantArithmetic.seigniorage_pv`, `UnpleasantArithmetic.unpleasant_shift`, `UnpleasantArithmetic.unpleasant_tradeoff`, `UnpleasantArithmetic.unpleasant_money_growth` |
| Cochrane pp. 456–457 | nominal debt: `P_0 = B_{−1}/S`, rising as `S` falls, and a disinflation is a windfall to bondholders; real debt places no restriction on the price level | `UnpleasantArithmetic.nominal_debt_price`, `UnpleasantArithmetic.nominal_debt_price_anti`, `UnpleasantArithmetic.disinflation_windfall`, `UnpleasantArithmetic.real_debt_no_price` |

## §§19.7–19.8 Seigniorage and hyperinflation; monetary history, pp. 457–464 (Seigniorage)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (19.41), p. 458 | steady-state seigniorage `(1/(Py))dM/dt = (π + g)/V` | `Seigniorage.steady_seigniorage` |
| Cochrane p. 458 | revenue and its derivative; `d log(−s)/d log π = π/(π + g) − d log V/d log π`; money demand and velocity elasticities | `Seigniorage.revenue`, `Seigniorage.revenue_hasDerivAt`, `Seigniorage.revenue_elasticity`, `Seigniorage.money_demand_elasticity` |
| Cochrane p. 458 (E16) | the revenue maximum is where the velocity elasticity equals `π/(π + g)`, which is one iff `g = 0`; revenue rises iff the elasticity is below it | `Seigniorage.revenue_foc_iff`, `Seigniorage.e16_unit_iff`, `Seigniorage.revenue_deriv_pos_iff` |
| Cochrane pp. 457–458 | the Laffer limit: past that point revenue falls | `Seigniorage.laffer_decreasing` |
| Cochrane p. 458 | the Cagan example `V = e^{a(r+π)}`: elasticity `aπ`; strict maximum at `π = 1/a` (`0.5` for `a = 2`); revenue rises before and falls after the peak and vanishes at infinity | `Seigniorage.cagRev`, `Seigniorage.cagRev_eq`, `Seigniorage.cagan_velocity_elasticity`, `Seigniorage.cagan_revenue_le`, `Seigniorage.cagan_revenue_lt`, `Seigniorage.cagan_example_two`, `Seigniorage.cagan_revenue_tendsto_zero`, `Seigniorage.cagRev_hasDerivAt`, `Seigniorage.cagRev_strictMonoOn`, `Seigniorage.cagRev_strictAntiOn` |
| Cochrane pp. 457–458 | above the maximum there is no steady state; below it there is one on each side of the peak | `Seigniorage.no_steady_state_above_max`, `Seigniorage.two_steady_states` |
| Cochrane §19.8, p. 460 | Baumol–Tobin: the square-root rule minimises `iM + A/M`; interest elasticity `−1/2` and income elasticity `1/2`; unit LM slope; cash in advance has unit income and zero interest elasticity | `Seigniorage.btCost`, `Seigniorage.bt_min`, `Seigniorage.bt_interest_elasticity`, `Seigniorage.bt_income_elasticity`, `Seigniorage.bt_lm_slope`, `Seigniorage.cia_income_elasticity` |
| Cochrane §19.8, p. 462 (E23) | a 40% price rise devalues nominal debt by `2/7 ≈ 28.6%` | `Seigniorage.e23_real_loss` |

## Online Appendix §1.6, money in continuous time, pp. 567–569, with (1.28), p. 566 (ContinuousTime; restated from the Cochrane `Generality` project)

| Book | Claim | Lean |
| --- | --- | --- |
| A1 (1.28), p. 566; (1.33)–(1.34), p. 567 | forward integration, and its iff form `G_T → 0` iff `G_t = ∫_t^∞ h`; the real form of a present value | `ContinuousTime.tendsto_of_hasDerivAt`, `ContinuousTime.forward_iff`, `ContinuousTime.integral_ratio_eq`, `ContinuousTime.real_form_iff` |
| A1 (1.31), p. 567 | the flow in real terms | `ContinuousTime.flow_real` |
| A1 (1.32)–(1.33), p. 567 | seigniorage as money creation: the bond transversality condition iff the valuation equation | `ContinuousTime.printing_hasDerivAt`, `ContinuousTime.money_printing_iff` |
| A1 (1.34), p. 567 | seigniorage as interest saving; given (1.33), (1.34) iff the money transversality condition | `ContinuousTime.interest_hasDerivAt`, `ContinuousTime.money_interest_iff`, `ContinuousTime.printing_interest_iff_money_tvc` |
| A1 (1.35)–(1.36), p. 568 | ex-post discounting with `W`: `(1/X)′ = −i/X`, `Λ_τ/Λ_t = W_t/W_τ`, and both valuation forms | `ContinuousTime.inv_nominal_value`, `ContinuousTime.lambda_ratio_eq_W`, `ContinuousTime.printing_W_hasDerivAt`, `ContinuousTime.money_printing_W_iff`, `ContinuousTime.interest_W_hasDerivAt`, `ContinuousTime.money_interest_W_iff` |
| A1 p. 568 | the printed integrand `(i_t − i^m_t)` is misdated | `ContinuousTime.printed_index_counterexample` |
| A1 (1.37), p. 569 | valuation with the mixed portfolio return, which lies below `i` | `ContinuousTime.mixed_hasDerivAt`, `ContinuousTime.money_mixed_iff`, `ContinuousTime.mixed_rate_lt` |

## Online Appendix Chapter 4, money in continuous time, pp. 635–641 (ContinuousTime)

| Book | Claim | Lean |
| --- | --- | --- |
| A4 p. 635 | `Λ_t = e^{−∫_0^t r}` has `Λ′ = −rΛ`; the nominal discount factor has `(Λ/P)′ = −iΛ/P` | `ContinuousTime.hasDerivAt_discount`, `ContinuousTime.hasDerivAt_nominal_discount` |
| A4 p. 635; (4.5), p. 636 | the present-value budget is the present-value form of the flow constraint, iff the transversality condition; the equilibrium valuation equation | `ContinuousTime.budget_hasDerivAt`, `ContinuousTime.pv_budget_iff`, `ContinuousTime.valuation_4_5` |
| A4 (4.1)–(4.4), pp. 635–636 | `d/dt e^{−δt}`; the chain rule for `u_c(c_t, m_t)`; the intertemporal condition; `u_m/u_c = i − i^m`; the equilibrium form | `ContinuousTime.hasDerivAt_expDisc`, `ContinuousTime.hasDerivAt_marginal_utility`, `ContinuousTime.foc_4_1`, `ContinuousTime.foc_4_2`, `ContinuousTime.foc_4_3` |
| A4 p. 636 | the CES aggregator and utility; perfect substitutes `θ = 0`; separable `θ = γ` | `ContinuousTime.cesX`, `ContinuousTime.cesU`, `ContinuousTime.cesX_pos`, `ContinuousTime.ces_perfect_substitutes`, `ContinuousTime.ces_separable` |
| A4 (4.7), p. 637 | exact `u_c`, `u_m`, `u_cc`, `u_cm`; `u_m/u_c = α(m/c)^{−θ}` | `ContinuousTime.rpow_one_sub`, `ContinuousTime.hasDerivAt_cesU_c`, `ContinuousTime.hasDerivAt_cesU_m`, `ContinuousTime.ces_mrs_4_7`, `ContinuousTime.hasDerivAt_ucc`, `ContinuousTime.hasDerivAt_ucm` |
| A4 p. 637 | the elasticities `−cu_cc/u_c` and `mu_cm/u_c`, also in ratio form and with money demand | `ContinuousTime.ces_ucc_ratio`, `ContinuousTime.ces_ucc_elasticity`, `ContinuousTime.ces_ucc_elasticity_ratio`, `ContinuousTime.ces_ucm_elasticity`, `ContinuousTime.ces_ucm_elasticity_ratio`, `ContinuousTime.ces_A_eq` |
| A4 (4.6), p. 636 (E20) | `θ → 1` gives Cobb–Douglas for the aggregator normalised by `1 + α`; the printed one is `(1 + α)^{1/(1−θ)}` times it, diverges and has no limit | `ContinuousTime.cesNorm`, `ContinuousTime.log_mean_hasDerivAt`, `ContinuousTime.ces_norm_limit`, `ContinuousTime.ces_norm_utility_limit`, `ContinuousTime.ces_unnorm_eq`, `ContinuousTime.ces_unnorm_diverges`, `ContinuousTime.ces_unnorm_no_limit` |
| A4 p. 636 (E20) | `θ → ∞` with fixed `α` gives `min(c, m)` and `m/c → 1`; `min(c, αm)` and `M/P = c/α` need the coefficient `α^{−θ}` | `ContinuousTime.ces_limit_min`, `ContinuousTime.ces_coeff_rewrite`, `ContinuousTime.ces_limit_min_corrected`, `ContinuousTime.demand_limit_fixed`, `ContinuousTime.demand_corrected`, `ContinuousTime.demand_corrected_limit` |
| A4 p. 636 (E20) | `M/P = c/α` means `V = α`, so `α = 1/V` only for `α = 1` | `ContinuousTime.velocity_of_demand`, `ContinuousTime.alpha_eq_inv_V_iff` |
| A4 (4.8)–(4.10), pp. 637–638 | money demand `m/c = (1/α)^{−ξ}(i − i^m)^{−ξ}`; the form without `α`; the interest cost `α^ξ(i − i^m)^{1−ξ}`, tending to zero iff `ξ < 1` | `ContinuousTime.demand_4_8`, `ContinuousTime.demand_4_10`, `ContinuousTime.interest_cost_formula`, `ContinuousTime.interest_cost_tendsto_iff` |
| A4 (4.11)–(4.12), pp. 638–639 | the "prettier" form and (4.12); the derivative of money demand along a path | `ContinuousTime.is_prettier`, `ContinuousTime.is_4_12`, `ContinuousTime.demand_log_deriv`, `ContinuousTime.log_consumption_deriv` |
| A4 (4.13), p. 639 (E21) | the exact IS curve with money `ẋ + (σ − ξ)(m/c)/(1 + A)·d(i − i^m)/dt = σ(i − π − δ)`; its first-order form at the steady state | `ContinuousTime.is_exact`, `ContinuousTime.is_curve_exact`, `ContinuousTime.first_order_term`, `ContinuousTime.coefficient_differentiable`, `ContinuousTime.coefficient_gap` |
| A4 (4.13), p. 639 (E21) | the printed (4.13) fails at any steady state with `σδ ≠ 0`, and is right for deviations | `ContinuousTime.E21_steady_state`, `ContinuousTime.E21_deviations` |
| A4 (4.14)–(4.15), p. 640 (E21) | (4.14) exactly; `A/(1 + A)` versus `A` is second order; (4.15) is inconsistent with the discrete (4.13) unless `E_tπ_{t+1} = π_t` | `ContinuousTime.is_4_14_exact`, `ContinuousTime.A_ratio_gap`, `ContinuousTime.E21_discrete_inconsistent` |
| A4 (4.16)–(4.17), pp. 640–641 | the constraint `ṁ = (y − c − s) − mṖ/P`; money demand `v′/u′ = i` from the Hamiltonian conditions; constant consumption gives `r = δ`; the transversality condition | `ContinuousTime.constraint_4_16`, `ContinuousTime.hamiltonian_money_demand`, `ContinuousTime.hamiltonian_eq_i`, `ContinuousTime.constant_consumption_rate`, `ContinuousTime.tvc_4_17_iff` |

## Links between the modules (Links)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (19.23), p. 444; A3 p. 612 | the change of coordinates `x = 1/m`; the real-balance map is `nextX` conjugated by it | `Links.one_div_rpow_eq`, `Links.ratioMap_eq_one_div_nextX` |
| Cochrane (19.18), (19.21), pp. 442–444; A3 p. 612 | paths of (19.21) in `x` and in `m` coincide, and are paths of (19.18) | `Links.isMPath_iff_isPowerPath`, `Links.isMIUPath_iff_isMPath` |
| Cochrane p. 445 (E13); A3 p. 613 (E17) | the inflationary steady state exists iff deflationary paths exist iff `m̄` exists uniquely iff `β < 1 + µ`: E13 and E17 are one condition | `Links.e13_iff_e17` |
| Cochrane p. 444; A3 p. 612 | deflations in `m` are the `nextX` orbit to `x = 0`, at rate `β/(1 + µ)` | `Links.deflation_rate` |
| A3 (3.3), p. 619; Figure 19.1, p. 444 | the finite-time explosion is the exit of the `nextX` orbit, on the same path | `Links.explosion_same_path` |
| A3 pp. 612–613 (E17); p. 454 | the money-in-utility and cash-in-advance transversality conditions along deflations both hold iff `µ < 0` | `Links.deflation_tvc_miu_iff_cia` |
| Cochrane p. 454 versus p. 445 and A3 p. 613 | at `1 + µ = β` the cash-in-advance deflations exist and the money-in-utility ones do not | `Links.cia_boundary_deflation` |
| Cochrane (19.2), p. 434; (19.28)–(19.30), p. 449 | the `Regimes` valuation equation in `tsum` form | `Links.flow_pv_tsum_iff_tvc` |
| Cochrane p. 453; footnote 1, p. 440 | cash-in-advance sufficiency for every concave `u`, under perfect foresight and on the tree; the two tree notions of a node-contingent plan coincide | `Links.cia_euler_sufficient_of_concave`, `Links.tree_euler_sufficient_of_concave`, `Links.meas_iff_tAdapted` |
| Cochrane (19.13)–(19.16), pp. 440–441; A4 (4.1)–(4.2), pp. 635–636 | (19.16) from the first-order conditions through the algebra of (4.2); (19.13) is the discrete (4.1); the per-period interest cost tends to `i` | `Links.miu_foc_money_demand`, `Links.miu_foc_log_growth`, `Links.interest_cost_continuous_limit` |
| A3 p. 632; A4 pp. 636–637 | the two CES utilities differ by a constant, so their marginal utilities agree | `Links.ces_nonsep_eq_ct`, `Links.ces_uc_nonsep_eq_ct`, `Links.ces_um_nonsep_eq_ct` |
| A4 (4.8), p. 638; p. 443 | the A4 money demand is the inverse power demand | `Links.demand_4_8_eq_power_demand` |
| Cochrane (19.4)–(19.5), p. 436; p. 458 | Cagan velocity and revenue are the Seigniorage Cagan example | `Links.cagan_steady_revenue` |
| Cochrane p. 435 (NI-7); pp. 437–438 | the fiscally selected Cagan path is the bounded one iff money and fiscal policy are coordinated as in `Regimes.double_active_iff` | `Links.cagan_ni7` |
| Cochrane (19.39)–(19.40), p. 456; p. 458 | discrete seigniorage is steady-state revenue | `Links.seig_eq_revenue` |
| Cochrane p. 435; p. 453 | the `Regimes` and cash-in-advance passive surplus rules agree | `Links.passiveSurplus_regimes_eq_cia` |

## Shared tools

| Book | Claim | Lean |
| --- | --- | --- |
| Chapter 19 throughout | the expectation axioms, adapted processes, pull-out and perfect foresight; bounded processes | `ExpectationSystem`, `ExpectationSystem.Adapted`, `ExpectationSystem.PullOut`, `perfectForesight`, `perfectForesight_pullOut`, `BoundedProc` |
| (19.2), (19.11), (19.28)–(19.30) | forward iteration and the partial sums of the forward series (shared core, restated from the Woodford Chapter 2 and 3 projects) | `ForwardSolution.iterate_A15`, `ForwardSolution.tendsto_partial_A16`, `ExpectationSystem.forwardSeries`, `ForwardSolution.existsUnique_bounded` |
| p. 437; footnote 1, p. 440; §19.5.1 | finite event trees, their pull-out property and the coin-flip tree with its shock | `ExpectationsFiniteTree.FiniteTree`, `ExpectationsFiniteTree.FiniteTree.toExpectationSystem`, `ExpectationsFiniteTree.finiteTree_pullOut`, `ExpectationsFiniteTree.coinSystem`, `ExpectationsFiniteTree.coinShock` |
| shared core, not used by Chapter 19 | Schur–Cohn determinacy and the sunspot family, carried for the other Cochrane projects | `SchurStable`, `schurStable_iff_roots`, `ForwardSolution.sunspotFamily` |
