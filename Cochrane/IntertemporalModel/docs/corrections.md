# Corrections to the source

This file lists places where a claim in Chapter 2 of Cochrane (2023), *The Fiscal Theory of the
Price Level*, or in Online Appendix A1.1, is false, imprecise, or relies on an unstated
hypothesis, and where the Lean statement departs from the printed one. In each case the Lean
statement proves the stated version and cites the original.

Codes E4–E10, E27 and E30 are the Chapter 2 and A1.1 items of the survey of Chapters 1–3
(`notes/survey_cochrane_ch1-3.md`). Each was confirmed or refuted by formalisation before being
recorded here, and an entry is revised if formalisation shows the finding itself to be wrong (the
survey's planned "rearrangement neutrality" theorem for p. 50 is one such revision, below). Two
findings are new: the debt-sale formula of p. 24 and the stimulus claim of p. 50. Several claims
that the book asserts without proof turned out to be correct; they are listed in the last
section.

Out of scope are the discursive passages: the Apple-share analogy and the run interpretation
(§2.2), the equilibrium-formation philosophy and the debates of pp. 28–29, the Ricardian debate
and the data (pp. 43–44), and the institutional and historical material of §§2.8–2.10. Lean names
are relative to the namespace `Cochrane.IntertemporalModel`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| p. 28; A1 (1.2), p. 554 (E4) | Iterating the flow condition gives the terminal term `lim E_tβ^TB_{t+T}/P_{t+T+1}` (A1: `R^{−T}`). | The weight is `β^{T+1}`: `B_{t−1}/P_t = s_t + ∑_{j=1}^{T}β^jE_ts_{t+j} + β^{T+1}E_tB_{t+T}/P_{t+T+1}` (`EquilibriumFormation.iterate_with_terminal`, `Valuation.hh_iterate`). The printed weight fails under perfect foresight with `β = 1/2`, zero surpluses and `x_t = 2^t` (`EquilibriumFormation.printed_p28_false`, `Valuation.printed_A1_2_false`). A1 p. 555 has the exponent right. The slip does not affect whether the limit is zero. |
| p. 43 (E5) | For an AR(1) surplus, `ΔE_t(P_{t−1}/P_t) = ΔE_t∑β^js_{t+j} = ε_{s,t}/(1 − βη)`. | The factor `B_{t−1}/P_{t−1}` is missing, as (2.27) shows. The correct statement is `(B_t/P_t)ΔE_{t+1}(P_t/P_{t+1}) = ε_{s,t+1}/(1 − βη)` (`FiscalMonetary.ar1_unexpected_inflation`). The printed formula fails whenever the shock is nonzero and the real value of the debt differs from one (`FiscalMonetary.ar1_printed_fails`). |
| p. 38 (E6) | `ΔE_tπ_t = ΔE_tp_t − p_{t−1} = −ε_{Σs,t}`. | `p_{t−1}` is known at `t − 1`, so it has no innovation: `ΔE_tπ_t = ΔE_tp_t` (`LinearFTMP.innov_pi_eq_innov_p`). Under perfect foresight with `p ≡ 1` the printed left side is `0` and the right side `−1` (`LinearFTMP.printed_E6_false`). |
| p. 50 (new) | "Borrow money, don't drive up interest rates, spend the money, repay the debt" has "no effect at all on current, unexpected, or expected future inflation". | True under perfect foresight: a rearrangement with the same initial present value and the same target leaves the whole price path (`FiscalMonetary.pf_stimulus_neutral`). Under uncertainty only part survives. The current price level and expected inflation are unchanged (`FiscalMonetary.stimulus_no_jump`, `FiscalMonetary.expected_inflation_indep_surplus`). But a stimulus that adds a date-`t`-known amount `D` to the present value at `t + 1` leaves `P_{t+1}` unchanged iff `D = 0` or there is no other fiscal news (`FiscalMonetary.stimulus_price_iff`), and unexpected inflation is rescaled by the real value of the debt (`FiscalMonetary.stimulus_unexpected_inflation`). In a coin-flip economy with `β = 1/2`, the stimulus `s'_0 = s_0 − 1/2`, `s'_1 = s_1 + 1` leaves the date-0 present value, `P_0` and expected inflation, but changes `P_1` in every state (`FiscalMonetary.CoinExample.stimulus_not_neutral`). The survey's planned theorem "any change of surpluses with zero present-value innovation at every date leaves the price level unchanged" is therefore false under uncertainty and was not proved. |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 24 (new) | "The government can soak up those dollars by debt sales `Q_tB_t = βE_ts_{t+1}`." | The formula equates a nominal quantity with a real one, and it holds only when the debt is retired at `t + 1`. The correct statement is real: `Q_tB_t/P_t = βE_ts_{t+1}` when `B_{t+1} = 0` (`EquilibriumFormation.soak_up_retired`). In general the revenue is the whole present value of the following surpluses, (2.11) (`EquilibriumFormation.realRevenue_hasSum`, `EquilibriumFormation.eqm_realRevenue`). |
| p. 22 | "The price level must adjust so that (2.7) holds." | A hypothesis is missing, as in Chapter 1 (E3): the price level `P_t = B_{t−1}/pv_t` is positive only if the present value is positive in every state. With positive debt and a nonpositive present value at some date and state there is no equilibrium (`Valuation.no_eqm_of_pv_nonpos`); with positive present values there is exactly one (`Valuation.existsUnique_eqm`). Surpluses are signed, so the present value needs absolute summability, `∑β^jE_t\|s_{t+j}\| < ∞` (`Valuation.AbsSummable`), and the step "iterate (2.5) to (2.7)" needs conditional monotone convergence applied to the positive and negative parts (`Valuation.hasSum_E_pv`, `Valuation.valuation_iff`). |
| p. 22 | "Household maximization, budget constraint, and equilibrium `c_t = y` also imply the household transversality condition (2.6)." | Proved with explicit hypotheses: strictly increasing `u`, positive prices, the bond price (2.3) and summable discounted net demands. Under perfect foresight this is `Valuation.tvc_of_optimal`. Under uncertainty it is proved for state-contingent plans on a finite state space with faithful expectations and information that stops growing (`Valuation.tvc_of_optimal_stoch`); both hold on every finite event tree (`Valuation.finiteTree_faithful`, `Valuation.finiteTree_infoStable`). The general deviation argument holds for any `ExpectationSystem` (`Valuation.bubble_deviation`). |
| p. 21 | "The consumer's first-order conditions." | Derived variationally, in the interior case where the household holds bonds, `B_t > 0` in every state: under perfect foresight (`Environment.euler_of_optimal`) and on a finite state space (`Valuation.euler_of_optimal_stoch`). |
| (2.16), p. 35 | `1/(1 + i_t) = E_t(P_t/P_{t+1})/R` implies `i_t ≈ r + E_tπ_{t+1}`. | The approximation is an exact first derivative when the rate is measured as `log(1 + i_t)` and `r = −log β`: along a bounded direction of inflation, the exact map has derivative `E_tπ_{t+1}` at the steady state (`LinearFTMP.fisher_log_form`, `LinearFTMP.fisher_deriv`, `LinearFTMP.fisher_deriv_value`). Under perfect foresight it is exact in logs (`LinearFTMP.fisher_pf_exact`). |
| (2.17), p. 35 (E10) | `ΔE_{t+1}π_{t+1} = −ΔE_{t+1}∑β^js̃_{t+1+j}`, linearised around a steady-state value of debt. | Stated both ways. The exact form uses `V_t = B_t/P_t` and the gross rate `P_t/P_{t+1}`, with no approximation (`LinearFTMP.unexpected_inflation_exact`); every equilibrium satisfies it (`GeneralLinks.equilibrium_pvNews`). The linear form is its first derivative along a family of economies with `s̃ = s/V` (`LinearFTMP.linear_217`). |
| §2.6 (E30) | (2.25) is the equilibrium for any `θ`. | Correct for the linear model: for every `θ` the equilibrium exists and is unique given `π_0` (`LinearFTMP.rule_existsUnique`). It is bounded for `\|θ\| < 1` (`LinearFTMP.ruleSol_bounded`) and unbounded for `\|θ\| > 1` as soon as inflation starts away from zero (`LinearFTMP.ruleSol_unbounded`), so along those paths the linearisation of §2.5 is not justified. No claim of the book is false. |
| (2.19), p. 36; (2.25), p. 40 | "The full solution of the model." | Uniqueness is given `π_0`. Date-0 inflation is set by date-0 fiscal news, which lies outside the date-0 information of the `ExpectationSystem`, so `π_0` is data (`LinearFTMP.peg_existsUnique`, `LinearFTMP.rule_existsUnique`). |
| A1 p. 556 | The increase `Δc` at which (1.3) holds with equality is the optimal choice. | Proved for concave increasing `u` differentiable at the optimum (`Valuation.deviation_optimal_concave`), and more generally given a supergradient `g ≥ 0` (`Valuation.deviation_optimal`). Strict concavity is not needed. |
| (2.6), p. 22 | The TVC `lim_T E_tβ^TB_{T−1}/P_T = 0`. | Stated as `lim_N β^NE_tx_{t+N} = 0`, which is equivalent for `β > 0` (`Valuation.tvc_iff_tvcBook`). |

## Typos, cross-references and rounding

| Where | Book says | Finding |
| --- | --- | --- |
| p. 32 (E7) | A one percentage point higher target means "one percent more nominal debt". | Exactly, `ΔB/B = Δi/(1 + i)` (`FiscalMonetary.debt_growth_of_rate`), which equals `Δi` iff `i = 0` or `Δi = 0` (`FiscalMonetary.rate_change_eq_debt_growth_iff`). From 5% to 6% the rise is `1/105` (`FiscalMonetary.printed_one_percent_fails`). |
| p. 48 (E7) | A 1% lower bond price raises the face value sold "by one percent". | Exactly `1/99` (`FlatSupply.one_percent_price_fall`, `FlatSupply.one_percent_printed_fails`). |
| p. 48 (E9) | (2.28) is "the flow condition (2.15)". | It is (2.4)/(2.9) (`FlatSupply.eq_2_28`). |
| A1 p. 554 (E27) | "Later `lim E_t(Λ_TB_{T−1}/P_T) > 0`." | The no-Ponzi condition is `≥ 0`; it is stated as a `liminf ≥ 0`, without presupposing that the limit exists (`Valuation.NoPonzi`, `Valuation.tendsto_zero_iff_noPonzi_and_optimal`). |
| Box p. 39 (E8) | `u_t = η_su_{t−1} + ε_{i,t}`; the fiscal shock indexed `s̃_{t+j}`. | Notation only. The disturbance uses `η` as in (2.23) (`LinearFTMP.Disturbance`), and the fiscal shock uses `s̃_{t+1+j}` as in (2.17) (`LinearFTMP.pvNews`). |
| Fig. 2.2, p. 41 | The hump peaks at date 5. | Confirmed, narrowly: at `θ = 0.8`, `η = 0.7` the peak is `π_5 = 1.695` against `π_4 = 1.69` (`LinearFTMP.fig22_peak`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| Throughout | Conditional expectations pull out quantities known at `t` | `ExpectationSystem.PullOut` as a hypothesis; true for perfect foresight and every finite tree (`perfectForesight_pullOut`, `ExpectationsFiniteTree.finiteTree_pullOut`) |
| p. 22 | Functions of date-`t` variables are known at `t`, so that `P_t = B_{t−1}/pv_t` is adapted | `ExpectationTools.FunctionsKnown`; true for perfect foresight and finite trees (`ExpectationTools.perfectForesight_functionsKnown`, `ExpectationTools.finiteTree_functionsKnown`). The peg equilibrium of `Links` uses the stronger `ExpectationTools.Closed` |
| p. 22 | `E_t` commutes with infinite sums | `ExpectationTools.MonotoneConvergence`, applied to positive and negative parts; for bounded surpluses the interchange needs no hypothesis (`FiscalMonetary.E_epv_tsum`, `GeneralLinks.fm_pv_eq_pv_of_bounded`) |
| p. 22 | Signed surpluses have a well-defined present value | `Valuation.AbsSummable`, `FiscalMonetary.SurplusSummable` |
| p. 22; pp. 31–33 | Positive initial debt and positive present values in every state; under a target also a positive ex-dividend value | Hypotheses of `Valuation.existsUnique_eqm` and `FiscalMonetary.peg_existsUnique`; `Links.peg_ftpl_existsUnique` takes present values bounded below by `c > 0` |
| pp. 31–33 | The target is adapted with `i > −1`; debt and rate are adapted | Part of `FiscalMonetary.Equilibrium`; hypotheses of `GeneralLinks.equilibrium_iff_isEqm`. The positivity of the bond price is not derived from the expectation axioms |
| (2.13), p. 30 | Debt outstanding is nonzero when dividing by `B_t/P_t` | Hypothesis of `FiscalMonetary.unexpected_inflation_eq` and `FiscalMonetary.no_surprise_iff` |
| p. 43 | The AR(1) surplus is bounded and `\|βη\| < 1` | Hypotheses of `FiscalMonetary.ar1_pv_news` and its successors |
| p. 21 | Every state has positive probability; in a finite economy information stops growing | `Valuation.Faithful`, `Valuation.InfoStable`, used only for optimisation under uncertainty; true on finite trees |
| p. 22 | `B ≥ 0` rules out a negative terminal value | `Valuation.noPonzi_of_nonneg_debt` |

## Claims confirmed correct

| Where | Claim | Lean |
| --- | --- | --- |
| (2.2), p. 21 | The household constraint is the mirror image of the government's at `c = y` | `Environment.hhFlow_iff_govFlow` |
| (2.3), p. 22 | `R = 1/β` and `Q_t = βE_t(P_t/P_{t+1})` | `Environment.realRate_eq_inv_beta`, `Environment.bondPrice_iff_euler`, `Environment.bondPrice_of_optimal` |
| p. 22 | Money is dominated at `i > 0`; the rate cannot be negative; perfect substitutes at `i = 0` | `Environment.money_dominated`, `Environment.bonds_dominated_of_neg_rate`, `Environment.perfect_substitutes` |
| (2.4)–(2.5), p. 22 | Eliminating money; the real flow | `Environment.govFlow_merge`, `Environment.flow_iff_real_x` |
| p. 23 | Proportional taxes keep the price level out of (2.7) | `Environment.propTax_surplus_indep_price` |
| (2.5)–(2.7), p. 22 | Flow plus TVC iff the valuation equation | `Valuation.valuation_iff` |
| (2.8), p. 23 | The household present-value constraint; excess wealth means excess demand | `Valuation.hh_pv_iff`, `Valuation.excess_demand_of_gap` |
| A1.1, pp. 554–556 | TVC = no-Ponzi plus optimality; the too-low price level explodes; the deviation is feasible, improves utility and is not an equilibrium | `Valuation.tvc_iff_noPonzi_and_optimal`, `Valuation.const_explodes`, `Valuation.const_tvc_iff`, `Valuation.deviation_feasible`, `Valuation.deviation_improves`, `Valuation.tooLow_not_equilibrium` |
| pp. 24–27 | Roll-over; passive policy; `B_{−1} = 0` leaves `P_0` free; the money overhang | `EquilibriumFormation.no_rollover`, `EquilibriumFormation.passive_every_price_eqm`, `EquilibriumFormation.no_initial_debt_not_unique`, `EquilibriumFormation.money_overhang_iff` |
| p. 28 | A too-high price level pushes debt negative | `EquilibriumFormation.tooHigh_violates_nonneg_debt` |
| (2.12)–(2.15), pp. 30–31 | Unexpected and expected inflation; the value of the debt sold | `FiscalMonetary.unexpected_inflation`, `FiscalMonetary.expected_inflation`, `FiscalMonetary.expected_valuation` |
| pp. 31–33 | Unit-elastic demand, the share split, irrelevant future sales; determinacy under a target; the decomposition into expected and unexpected inflation | `FiscalMonetary.revenue_invariant`, `FiscalMonetary.shareSplit`, `FiscalMonetary.future_sales_irrelevant`, `FiscalMonetary.peg_existsUnique`, `FiscalMonetary.inflation_decomposition` |
| p. 32 | A real-rate peg has no equilibrium | `FiscalMonetary.no_eqm_real_rate_peg` |
| p. 33 | Under perfect foresight monetary policy gives a family and fiscal policy picks `P_0` | `FiscalMonetary.pf_family`, `FiscalMonetary.pf_price_formula` |
| pp. 36–38 | Fig. 2.1, announcement invariance, the long-run Fisher relation, the price-level target | `LinearFTMP.fig21_rate`, `LinearFTMP.fig21_fiscal`, `LinearFTMP.fig21_expected_fiscal`, `LinearFTMP.announcement_invariant`, `LinearFTMP.long_run_fisher`, `LinearFTMP.pTarget_rate_lowers_price` |
| p. 40 | Unique for every `θ`; the rule solution equals the peg solution with the equilibrium rate | `LinearFTMP.rule_existsUnique`, `LinearFTMP.rule_eq_peg` |
| Fig. 2.2, pp. 40–41 | The closed-form responses and the hump; fiscal policy sets impact inflation | `LinearFTMP.irf_rule`, `LinearFTMP.fig22_monetary`, `LinearFTMP.fig22_fiscal`, `LinearFTMP.hump_exists`, `LinearFTMP.fiscal_sets_impact` |
| (2.26)–(2.27), pp. 42–43 | The flow condition and its innovation form; the equity issue; the s-shape; the AR(1) value of debt falls with a deficit | `FiscalMonetary.eq_2_26`, `FiscalMonetary.eq_2_27`, `FiscalMonetary.equityIssue_finances_deficit`, `FiscalMonetary.sShape`, `FiscalMonetary.ar1_value_falls` |
| §2.8, p. 44 | The Treasury/central-bank split is irrelevant | `FiscalMonetary.consolidation_irrelevant` |
| (2.28), p. 48 | The Treasury rule and the flat supply curve | `FlatSupply.treasury_rule_iff`, `FlatSupply.flat_supply_revenue`, `FlatSupply.twoStep_equilibrium` |
