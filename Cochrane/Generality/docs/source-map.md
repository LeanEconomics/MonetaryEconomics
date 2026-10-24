# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, "A bit of generality"
(pp. 52–80), with Online Appendix A1.2–A1.6 (pp. 556–568) and A1.9.1 (pp. 576–577). Each formal
claim is listed with its Lean name, relative to the namespace `Cochrane.Generality`. Page numbers
are book pages. The book has no labelled propositions, so rows are keyed by equation number,
figure, section or page; Online Appendix equations are written A1 (1.4)–(1.50). Rows follow the
book section by section, and each heading names the modules that formalise the section: §§3.1–3.5
in discrete time with the matching appendix sections, §3.6 in continuous time, A1.9.1, then the
links among the four formalisation chains and the shared tools. Discrete-time statements hold for
an arbitrary `ExpectationSystem`, so under perfect foresight and under uncertainty, unless the row
says otherwise; continuous-time statements are deterministic (perfect foresight). Codes E11–E31
are the survey items recorded in [corrections](corrections.md). The shared core (`Determinacy`,
`Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is cited where a row uses it.

## §3.1 and §3.3 Discounting and the valuation theorem, pp. 53, 55 (LongTermDebt)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 55; §3.1, p. 53 (restated from the Woodford Chapter 2 project) | the multi-period discount factor `Λ_{t+n}/Λ_t = ∏_{k<n} m_{t+k}` from one-period factors; its algebra, sign and measurability; with `m ≡ β` it is `βⁿ` | `LongTermDebt.sdf`, `LongTermDebt.sdf_zero`, `LongTermDebt.sdf_succ`, `LongTermDebt.sdf_succ'`, `LongTermDebt.sdf_one`, `LongTermDebt.sdf_add`, `LongTermDebt.sdf_nonneg`, `LongTermDebt.sdf_pos`, `LongTermDebt.sdf_known`, `LongTermDebt.sdf_const` |
| Cochrane p. 55 | information accumulates; products of known variables are known (pull-out); `E_t` is monotone; `\|E_tx\| ≤ E_t\|x\|`; the law of iterated expectations with a discount factor | `LongTermDebt.known_of_le`, `LongTermDebt.known_mul`, `LongTermDebt.E_nonneg`, `LongTermDebt.abs_E_le_E_abs`, `LongTermDebt.E_sdf_mul_E` |
| Cochrane pp. 53, 55 (E29) | conditional monotone convergence, the interchange of `E_t` and infinite sums; it holds for perfect foresight and every finite tree; `E_t` commutes with an absolutely convergent series | `LongTermDebt.MonotoneConvergence`, `LongTermDebt.perfectForesight_monotoneConvergence`, `LongTermDebt.finiteTree_monotoneConvergence`, `LongTermDebt.E_tsum_abs` |
| Cochrane (3.3), (3.5), pp. 53, 55 (E29) | the present value as a genuine infinite sum; absolutely summable signed surpluses; summability; `E_t` taken outside the sum | `LongTermDebt.pv`, `LongTermDebt.SurplusSummable`, `LongTermDebt.abs_E_sdf_mul_le`, `LongTermDebt.summable_pv`, `LongTermDebt.pv_eq_E_tsum` |
| Cochrane p. 55 | signed surpluses: positive and negative parts, their summability, the split of the present-value terms; the tail of the present value; the present value is known at its date | `LongTermDebt.posPart`, `LongTermDebt.negPart`, `LongTermDebt.posPart_sub_negPart`, `LongTermDebt.summable_posPart`, `LongTermDebt.summable_negPart`, `LongTermDebt.E_sdf_mul_split`, `LongTermDebt.hasSum_E_sdf_mul_pv`, `LongTermDebt.hasSum_E_sdf_mul_pv_signed`, `LongTermDebt.E_pv_self` |
| Cochrane p. 53 ("iterating forward"), p. 55 | the real flow `x_t = s_t + E_t[m_tx_{t+1}]`, the transversality condition, the slack in the flow; the exact telescoping identity | `LongTermDebt.FlowRec`, `LongTermDebt.TVC`, `LongTermDebt.slack`, `LongTermDebt.telescope` |
| Cochrane p. 53 (from (3.2) to (3.3) and back), p. 55, (3.5) | flow and TVC give the present value; the present value at every date gives the flow and the TVC; **flow + TVC at every date iff `x_t = ∑_n E_t[(Λ_{t+n}/Λ_t)s_{t+n}]` at every date**, signed surpluses | `LongTermDebt.hasSum_of_flow_tvc`, `LongTermDebt.flow_of_pv`, `LongTermDebt.tvc_of_pv`, `LongTermDebt.flow_tvc_iff_pv` |

## §3.1 Long-term debt, (3.1)–(3.3), pp. 52–53 (LongTermDebt)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (3.1), p. 53 | `Q_t^{(t+j)} = E_t[βʲP_t/P_{t+j}]`, with a general discount factor; real bond prices; `Q_t^{(t)} = 1`; nonnegativity; the recursive form via the tower property | `LongTermDebt.ZeroPrice`, `LongTermDebt.zeroPrice_const_iff`, `LongTermDebt.realPrice`, `LongTermDebt.zeroPrice_eq_mul`, `LongTermDebt.zeroPrice_real`, `LongTermDebt.zeroPrice_zero`, `LongTermDebt.realPrice_nonneg`, `LongTermDebt.realPrice_succ`, `LongTermDebt.zeroPrice_recursive` |
| Cochrane (3.1), p. 53; p. 56 | under perfect foresight the term structure is the product of one-period prices, `∏_{k<j} 1/(1 + i_{t+k})` | `LongTermDebt.zeroPrice_pf_prod`, `LongTermDebt.zeroPrice_pf_rates` |
| Cochrane p. 53 ("this event means future inflation rather than current inflation") | under perfect foresight a bond price below `βʲ` is a price level that rises between `t` and `t + j` | `LongTermDebt.zeroPrice_lt_iff_inflation` |
| Cochrane (3.2), p. 53 (E29) | the base case of a finite maximum maturity; the flow with long-term debt; market value, value carried forward, real value; the flow as exact algebra and, given (3.1), as the real recursion | `LongTermDebt.MaxMaturity`, `LongTermDebt.FlowLT`, `LongTermDebt.mktValue`, `LongTermDebt.purchaseValue`, `LongTermDebt.realValue`, `LongTermDebt.flowLT_iff_value`, `LongTermDebt.purchaseValue_real`, `LongTermDebt.flowLT_iff_recursion`, `LongTermDebt.realValue_adapted` |
| Cochrane (3.1)–(3.3), p. 53 | given (3.1), flow (3.2) + TVC at every date iff the valuation equation (3.3) at every date; with `m ≡ β` exactly as printed | `LongTermDebt.valuationLT_iff`, `LongTermDebt.pv_const`, `LongTermDebt.valuationLT_iff_const` |
| Cochrane p. 53 (E28) | "we can derive (3.2) from (3.3) by considering its value at two adjacent dates" needs (3.1): counterexample | `LongTermDebt.valuationLT_not_imp_flow` |
| Cochrane (3.2)–(3.3), p. 53, with the geometric structure of A1 p. 559 | `B_{t−1}^{(t+j)} = ωʲb_t` with genuine infinite sums over maturities: flow, annuity and market value; the real recursion; flow + TVC iff the valuation equation | `LongTermDebt.geomDebt`, `LongTermDebt.GeomFlow`, `LongTermDebt.annuity`, `LongTermDebt.geomValue`, `LongTermDebt.geomValue_eq_tsum`, `LongTermDebt.realAnnuity`, `LongTermDebt.annuity_div`, `LongTermDebt.hasSum_shift`, `LongTermDebt.geomFlow_iff_recursion`, `LongTermDebt.geomValue_adapted`, `LongTermDebt.valuationGeom_iff` |

## Online Appendix A1.2.1 Geometric maturity, discrete time, pp. 559–561 (LongTermDebt)

| Book | Claim | Lean |
| --- | --- | --- |
| A1 p. 559 | with a constant rate the term structure is flat, `Q_t^{(t+j)} = 1/(1+i)ʲ` | `LongTermDebt.zeroPrice_pf_const_rate` |
| A1 (1.14), p. 559 | `∑ωʲ/(1+i)ʲ = (1+i)/(1+i−ω)`; the present value `(1+r)s/r`; the valuation equation | `LongTermDebt.geom_value`, `LongTermDebt.pv_const_value`, `LongTermDebt.valuation_1_14` |
| A1 (1.15), p. 559 | the steady state `B/P = (1+r−ω)s/r` | `LongTermDebt.steady_state_1_15` |
| A1 (1.16), p. 559 | `P_0/P = (1+i)(1+r−ω)/((1+r)(1+i−ω))`, from (1.14)–(1.15) and in general form; `P_0/P − 1` | `LongTermDebt.jumpRatio`, `LongTermDebt.price_jump_perm`, `LongTermDebt.price_jump_of_valuation`, `LongTermDebt.jumpRatio_sub_one` |
| A1 (1.16), p. 559; §3.1, p. 53 ("a rise in nominal interest rates … can result in a lower price level") | `P_0 < P` iff `i > r` and `ω > 0`; a rate cut raises `P_0`; the jump grows with `ω`; no jump with one-period debt (A1 p. 560) | `LongTermDebt.price_jump_lt_one_iff`, `LongTermDebt.price_jump_gt_one`, `LongTermDebt.jumpRatio_strictAntiOn_omega`, `LongTermDebt.price_jump_omega_zero` |
| A1 (1.19), p. 560 | the perpetuity `P_0 = (1+i)r/((1+r)i)·P`; "3% to 4% occasions a 25% drop" is 24.27% in discrete time, 25% only in continuous time | `LongTermDebt.price_jump_perpetuity`, `LongTermDebt.perpetuity_example` |
| A1 p. 560 (E15) | "with `ω = 0.8` … a 3.5% price level drop": the exact (1.16) at `r = 2%`, `i = 3%` gives `40/1173 ≈ 3.41%` | `LongTermDebt.omega_08_example` |
| A1 pp. 560–561, forward-guidance display | prices when the rate rises at `T`; the portfolio value; `P_0/P − 1 = (ω/(1+r))^T[(1.16) − 1]`; the drop | `LongTermDebt.fgPrice`, `LongTermDebt.fgPrice_eq_prod`, `LongTermDebt.fg_value`, `LongTermDebt.price_jump_fg`, `LongTermDebt.fgDrop`, `LongTermDebt.fg_eq_neg_drop` |
| A1 p. 561 | "forward guidance works"; the jump goes to zero as `T → ∞`; smaller for longer `T` and for lower `ω` | `LongTermDebt.fg_drop_pos`, `LongTermDebt.fg_tendsto_zero`, `LongTermDebt.fg_drop_antitone_T`, `LongTermDebt.fg_drop_strictAnti_T`, `LongTermDebt.fg_drop_strictMonoOn_omega` |
| A1 p. 560 | transitory and mean-reverting rises have a smaller effect | `LongTermDebt.annuity_mono_rates`, `LongTermDebt.price_le_of_annuity_le`, `LongTermDebt.meanReverting_le_perm` |
| A1 p. 561 | roll-over: bond sales under the geometric structure; `ω^{j−1}(1−ω)B` in the steady state; the steady flow iff (1.15) | `LongTermDebt.geom_rollover`, `LongTermDebt.geom_rollover_steady`, `LongTermDebt.steady_flow_iff_1_15` |
| A1 p. 561 ("needs tending, except in a knife edge case") | net issuance `ωʲ(b_{t+1} − ωb_t)`; no trading iff `b_{t+1} = ωb_t` iff `b_t = ωᵗb_0`; the flow in issuance form; **no trading iff `P_ts_t = ωᵗb_0`**, then nominal surpluses are known at date 0; otherwise some issuance is nonzero | `LongTermDebt.geom_issuance`, `LongTermDebt.NoTrade`, `LongTermDebt.geom_noTrade_iff`, `LongTermDebt.geom_noTrade_iff_path`, `LongTermDebt.geomFlow_iff_issuance`, `LongTermDebt.geom_knife_edge`, `LongTermDebt.knife_edge_surplus_known`, `LongTermDebt.geom_needs_tending` |

## §3.2 Ratios to GDP and a focus on inflation, (3.4), pp. 54–55 (Ratios)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 54 ("multiplying and dividing by real GDP") | `E_t[W/z] = E_t[W]/z` for `z` known at `t`; the growth-adjusted term and its expectation | `Ratios.E_div_known`, `Ratios.gdpTerm`, `Ratios.E_gdpTerm` |
| Cochrane p. 54, first display | the valuation equation holds iff its debt-to-GDP form holds | `Ratios.valuation_gdp_iff` |
| Cochrane (3.4), p. 54 | the value of one dollar, `1/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}/B_{t−1}]`; with `m ≡ β` as printed | `Ratios.valuation_per_dollar_iff`, `Ratios.valuation_per_dollar_const` |
| Cochrane p. 55, last display | the per-dollar form in ratios to GDP | `Ratios.valuation_per_dollar_gdp_iff` |
| Cochrane p. 54 ("there can be no expected shocks to the present value") | `E_t(E_{t+1} − E_t)X = 0`, in particular for `∑βʲs_{t+j}` | `Ratios.E_innov_zero`, `Ratios.E_innov_pv_zero` |
| Cochrane p. 54 | the flow condition in ratios to GDP; more growth with given surplus ratios raises the debt-to-GDP valuation | `Ratios.flow_gdp_iff`, `Ratios.gdp_growth_mono` |

## §3.3 Risk and discounting, (3.5)–(3.8), pp. 55–57 (StochasticDiscount)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 55 | `∏ m = Λ_{t+n}/Λ_t`; with `Λ_t = βᵗu'(c_t)` the factor `βⁿu'(c_{t+n})/u'(c_t)` | `StochasticDiscount.sdf_eq_ratio`, `StochasticDiscount.sdf_marginal_utility` |
| Cochrane p. 55 | the bond price `Q_t = E_t[(Λ_{t+1}/Λ_t)P_t/P_{t+1}]`; the flow with `Q`; real debt; the flow as the real recursion; the TVC in the book's form | `StochasticDiscount.bondPrice`, `StochasticDiscount.FlowOne`, `StochasticDiscount.realDebt`, `StochasticDiscount.flowOne_iff_rec`, `StochasticDiscount.tvc_lambda_iff` |
| Cochrane (3.5), p. 55 | flow + TVC at every date iff `B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}]` at every date (signed surpluses); the printed form; the price level is determined | `StochasticDiscount.valuation_sdf_iff`, `StochasticDiscount.pv_lambda`, `StochasticDiscount.price_eq_of_valuation`, `StochasticDiscount.price_unique` |
| Cochrane p. 56 | `1 = R⁻¹_{t+1}R_{t+1} = E_t(R⁻¹_{t+1}R_{t+1})` under any probabilities; `R_{t+1} = (1/Q_t)P_t/P_{t+1} = (1+i_t)P_t/P_{t+1}`; the ex-post flow | `StochasticDiscount.inv_return_expost`, `StochasticDiscount.inv_return_sdf`, `StochasticDiscount.expostReturn`, `StochasticDiscount.expostReturn_rate`, `StochasticDiscount.flow_expost` |
| Cochrane (3.6), p. 56 (E12) | the finite-horizon iteration, terminal product to `T`; convergence iff the terminal term vanishes; the ex-post present value, also after `E_t` ("holds ex-post, so it also holds ex-ante"); under perfect foresight `R⁻¹ = m` | `StochasticDiscount.ExPostFlow`, `StochasticDiscount.expost_iterate`, `StochasticDiscount.expost_tendsto_iff`, `StochasticDiscount.expost_pv`, `StochasticDiscount.expost_E_tendsto_iff`, `StochasticDiscount.expost_pv_E`, `StochasticDiscount.expost_flow_E`, `StochasticDiscount.pf_expost_inv_eq_sdf` |
| Cochrane p. 56 ("(3.5) well defined … but (3.6) explode"), the peso example | on `Option ℕ` (a fiscal switch at date `n`, or never), beliefs that the switch comes next period; the expectation system, pull-out, monotone convergence; surpluses, debt, price level; flow, bounds, adaptedness; `R_{t+1} = 1/2` on the never-switch path | `StochasticDiscount.pesoPt`, `StochasticDiscount.pesoPt_some_le`, `StochasticDiscount.pesoPt_some_gt`, `StochasticDiscount.pesoPt_none`, `StochasticDiscount.pesoPt_pt`, `StochasticDiscount.pesoPt_pt'`, `StochasticDiscount.pesoSystem`, `StochasticDiscount.pesoSystem_E`, `StochasticDiscount.pesoSystem_pullOut`, `StochasticDiscount.pesoSystem_monotoneConvergence`, `StochasticDiscount.pesoS`, `StochasticDiscount.pesoX`, `StochasticDiscount.peso_values`, `StochasticDiscount.pesoX_adapted`, `StochasticDiscount.pesoS_adapted`, `StochasticDiscount.pesoX_flow`, `StochasticDiscount.pesoX_bounds`, `StochasticDiscount.pesoS_abs_le`, `StochasticDiscount.pesoP`, `StochasticDiscount.pesoReturn_none` |
| Cochrane p. 56 | (3.5), the flow and the TVC hold everywhere, while on the never-switch path the partial sums of (3.6) tend to `−∞` and the terminal term to `+∞` | `StochasticDiscount.expost_may_diverge` |
| Cochrane p. 56, on finite trees | **on every finite event tree, (3.5) with its flow and TVC forces (3.6) to converge absolutely in every state**, with the terminal term tending to zero; known iff constant on information cells; information stops refining; the ex-post flow from the flow, also where `Q_t = 0` | `StochasticDiscount.finiteTree_expost_pv`, `StochasticDiscount.finiteTree_known_iff`, `StochasticDiscount.finiteTree_info_stable`, `StochasticDiscount.finiteTree_eventually_known`, `StochasticDiscount.expostFlow_of_flowOne` |
| Cochrane (3.7)–(3.8), pp. 56–57 | the portfolio return; (3.2) iff (3.8); "we iterate again": the ex-post present value with long-term debt | `StochasticDiscount.portfolioReturn`, `StochasticDiscount.flowLT_iff_3_8`, `StochasticDiscount.expostLT_pv` |

## §3.4 Money, (3.9)–(3.16), pp. 57–62 (Money)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 55; footnote 1, p. 58 | iterating `Y_t = c_t + E_tY_{t+1}`; the present value iff the terminal term vanishes | `Money.telescope`, `Money.pv_iff_tvc` |
| Cochrane pp. 55–59 | bond pricing by the discount factor; the standing assumptions | `Money.BondEuler`, `Money.Standing` |
| Cochrane (3.9), p. 57; p. 58 | the flow with money; with interest `i^m` on money; (3.9) is `i^m = 0` | `Money.Flow39`, `Money.FlowIm`, `Money.flow39_iff_flowIm` |
| Cochrane (3.10)–(3.12), pp. 58–59 | the present-value relation, the TVC, summability; the integrands of (3.10), (3.11), (3.12) and its second form; footnote 2's weight | `Money.PVRel`, `Money.TVC`, `Money.PVSummable`, `Money.term10`, `Money.term11`, `Money.term12`, `Money.term12b`, `Money.weight_identity` |
| Cochrane p. 55; footnote 1, p. 58 | the nominal Euler equation; pull-out of `Λ_t⁻¹`; the real value is known; the general flow-to-valuation theorem, both directions | `Money.E_next`, `Money.E_ratio`, `Money.adapted_val`, `Money.pv_book_iff` |
| Cochrane (3.12), p. 59, footnotes | the recursions behind (3.12) and its second form; each iff its TVC; with `i^m = 0` they reduce to (3.10) and (3.11) | `Money.rec_3_12`, `Money.rec_3_12b`, `Money.pv_3_12`, `Money.pv_3_12b`, `Money.term12_zero`, `Money.term12b_zero` |
| Cochrane (3.10)–(3.11), p. 58 | (3.10) iff the TVC on `B + M`; (3.11) iff the TVC on `B` alone | `Money.pv_3_10`, `Money.pv_3_11` |
| Cochrane p. 57 (E13) | "these equivalent expressions": the terminal terms differ by the money term; equivalent under the money TVC; given (3.11), (3.10) iff the money TVC; the money-bubble counterexample | `Money.tvc_split`, `Money.pv_3_10_iff_3_11`, `Money.pv_3_10_iff_money_tvc`, `Money.money_bubble` |
| Cochrane (3.13)–(3.15), p. 59 | the ex-post portfolio return; the flow (3.14); pathwise iteration; the finite and infinite ex-post present value | `Money.exPostReturn`, `Money.flow_3_14`, `Money.iterate_discount`, `Money.pv_discount_iff`, `Money.pv_3_15_finite`, `Money.pv_3_15_iff` |
| Cochrane §3.4.1, (3.16), pp. 59–60 (E14) | at `i = 0` only `B + M` matters; (3.16) from (3.10); full interest `i^m = i`; `β^j` needs `Λ_t = βᵗ`; `E_t` outside the sum; (3.16) does not follow from (3.11) | `Money.zero_bound_flow_total`, `Money.zero_bound_valuation`, `Money.full_interest_valuation`, `Money.zero_bound_beta`, `Money.zero_bound_E_outside`, `Money.zero_bound_not_from_3_11` |
| Cochrane p. 60 ("any seigniorage effect of monetary policy vanishes") | the surplus net of seigniorage; the integrand, valuation and flow with offsetting surpluses | `Money.offsetSurplus`, `Money.seigniorage_offset_term`, `Money.seigniorage_offset_valuation`, `Money.seigniorage_offset_flow` |
| Cochrane pp. 60–62 | with full interest only total debt matters; a passive money supply with `MV = Py` | `Money.full_interest_split_irrelevant`, `Money.passive_split` |
| Cochrane pp. 60–61 | the 2019 and early-1980s seigniorage arithmetic; "$200 billion or 5% of GDP" is 6.7% of the stated GDP | `Money.seigniorage_2019`, `Money.seigniorage_1980s` |

## Online Appendix A1.2 Nonlinear identities and their exact linearisation, pp. 556–558 (LogLinearIdentities)

| Book | Claim | Lean |
| --- | --- | --- |
| A1 (1.4)–(1.6), pp. 556–557 | market value, overnight value, nominal portfolio return; `V_tR^n_{t+1} = P_{t+1}sp_{t+1} + V_{t+1}` | `LogLinearIdentities.marketValue`, `LogLinearIdentities.overnightValue`, `LogLinearIdentities.nominalReturn`, `LogLinearIdentities.flow_value_identity` |
| A1 (1.7)–(1.8), p. 557 | the flow in ratios to GDP; the finite and infinite present-value identity, iff the terminal term vanishes | `LogLinearIdentities.flow_gdp`, `LogLinearIdentities.pv_gdp_finite`, `LogLinearIdentities.pv_gdp_iff` |
| A1 (1.9)–(1.11), p. 558 | the log flow identity; the exact derivative of `log(sy + e^{v'})`; the constant `r − g + (1 − ρ)(v − 1)`, zero at `r = g`; (1.11) is the tangent | `LogLinearIdentities.log_flow_identity`, `LogLinearIdentities.logFlow`, `LogLinearIdentities.logFlow_hasFDerivAt`, `LogLinearIdentities.logFlow_hasFDerivAt_rho`, `LogLinearIdentities.constant_1_11`, `LogLinearIdentities.constant_zero_of_rg`, `LogLinearIdentities.tangent_1_11` |
| A1 (1.12), p. 558; Cochrane p. 63 (E11) | `ρ = e^{−(r−g)}`, below one iff `r > g`; the printed `e^{r−g}` agrees only at `r = g` and is below one only if `r < g` | `LogLinearIdentities.rho_eq`, `LogLinearIdentities.rho_lt_one_iff`, `LogLinearIdentities.printed_rho_eq_iff`, `LogLinearIdentities.printed_rho_lt_one_iff` |
| Cochrane p. 63; A1 p. 558 | the scaled surplus `s̃ = ρ/(V/(Py))·s/y` | `LogLinearIdentities.stilde_eq` |

## §3.5.1 The linearised flow and present-value identities, (3.17)–(3.20), pp. 62–65 (LogLinearIdentities)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (3.17)–(3.18), p. 63 | the linearised flow; the discounted flow `s̃ + g − r`; the finite-horizon identity, pathwise and after `E_t` | `LogLinearIdentities.Flow317`, `LogLinearIdentities.zp`, `LogLinearIdentities.pv_318`, `LogLinearIdentities.pv_318_E` |
| Cochrane (3.19), p. 64 | the infinite identity iff the terminal term vanishes; a stationary `v` suffices; the `ρ = 1` version in deviations from the mean | `LogLinearIdentities.pv_319_iff`, `LogLinearIdentities.terminal_of_bounded`, `LogLinearIdentities.pv_rho_one` |
| Cochrane pp. 63–65 | the bounded ("stationary") linear economy with `0 < ρ < 1`; (3.19) as a genuine sum, with `E_t` outside as printed | `LogLinearIdentities.LinearEconomy`, `LogLinearIdentities.zp_bdd`, `LogLinearIdentities.zp_adapted`, `LogLinearIdentities.pv_319`, `LogLinearIdentities.pv_319_E_outside` |
| Cochrane p. 64 | `p_t = E_t(d_{t+1} + p_{t+1})/E_tR_{t+1}` | `LogLinearIdentities.price_expected_return` |
| Cochrane p. 64; Notation p. xxv | the innovation operator `ΔE_{t+1}`; a known variable has no innovation; bounds and summability | `LogLinearIdentities.innov`, `LogLinearIdentities.innov_apply`, `LogLinearIdentities.innov_known`, `LogLinearIdentities.abs_innov_le`, `LogLinearIdentities.summable_innov`, `LogLinearIdentities.summable_pow_succ` |
| Cochrane (3.20), pp. 64–65 | innovations of (3.19) sum to zero; the unexpected-inflation identity | `LogLinearIdentities.innov_pv`, `LogLinearIdentities.innov_identity_3_20` |

## Online Appendix A1.3 and (3.21)–(3.22) Bond returns, pp. 65, 561–564 (LogLinearIdentities)

| Book | Claim | Lean |
| --- | --- | --- |
| A1 (1.21)–(1.23), pp. 562–563 | at steady-state prices every portfolio earns `1 + i`; `Q = 1/(1+i−ω)`, `1/(1+i)` at `ω = 0`, `1/i` for perpetuities; the numerator `1 + ωQ_{t+1}` | `LogLinearIdentities.return_indep_weights`, `LogLinearIdentities.geomQ`, `LogLinearIdentities.geomQ_short`, `LogLinearIdentities.geomQ_perpetuity`, `LogLinearIdentities.geom_portfolio_return` |
| A1 (1.22)–(1.24), p. 563 (E15) | the log bond return; its exact derivative, coefficient `ω/(1+i)` and constant `log(1+i)`; `ω/(1+i) = ω` only if `ω = 0` or `i = 0` | `LogLinearIdentities.bondReturn`, `LogLinearIdentities.bondReturn_hasFDerivAt`, `LogLinearIdentities.bondReturn_steady`, `LogLinearIdentities.omega_hat_eq_iff` |
| A1 (1.24), p. 563 | the linear bond-return identity with a free weight `ω̂`; bounded bond prices; bounded returns | `LogLinearIdentities.BondRet`, `LogLinearIdentities.BondPriceOK`, `LogLinearIdentities.rn_bound` |
| A1 box, pp. 561, 564 (E16) | `q_t = −∑_{j≥1} ω̂^{j−1}r^n_{t+j}`; the printed `ω̂ʲ` holds only where `q_t = 0`; counterexample | `LogLinearIdentities.bondPrice_forward`, `LogLinearIdentities.printed_bondPrice_iff`, `LogLinearIdentities.printed_bondPrice_counterexample` |
| A1 p. 564 | the expectations hypothesis `ω̂E_tq_{t+1} − q_t = i_t` | `LogLinearIdentities.EH_bond` |
| Cochrane (3.21), p. 65; A1 (1.25), p. 564 | the bond-return innovation identity, in nominal and real form | `LogLinearIdentities.bondReturn_innov`, `LogLinearIdentities.bondReturn_innov_real` |
| Cochrane (3.22), p. 65 | the weighted-inflation identity | `LogLinearIdentities.weighted_inflation_identity` |

## §§3.5.2–3.5.4 Special cases, (3.23)–(3.28), Figure 3.1, pp. 65–71 (LogLinearIdentities)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane pp. 65–66 | with one-period debt `r^n_{t+1} = i_t` is known; with the expectations hypothesis; constant expected returns have no innovations | `LogLinearIdentities.short_debt_return_known`, `LogLinearIdentities.short_debt_EH`, `LogLinearIdentities.innov_r_zero` |
| Cochrane §3.5.2, p. 66; (3.27), p. 69; p. 67 | one-period debt with constant and with time-varying expected returns | `LogLinearIdentities.special_constant_short`, `LogLinearIdentities.special_varying_short` |
| Cochrane (3.23)–(3.25), pp. 67–68 | long-term debt with constant expected returns; the short and bond-return identities | `LogLinearIdentities.special_constant_long`, `LogLinearIdentities.identity_3_24`, `LogLinearIdentities.identity_3_25` |
| Cochrane (3.28), p. 69 | monetary policy without surplus change: `ΔE_{t+1}π_{t+1} = −∑_{j≥1} ω̂ʲΔE_{t+1}π_{t+1+j}`; on sequences | `LogLinearIdentities.monetary_disinflation`, `LogLinearIdentities.disinflation_seq` |
| Cochrane p. 66 | at 100% debt/GDP it takes four times the surplus of 25% | `LogLinearIdentities.scaling_ratio` |
| Cochrane p. 67 | `ω = 0.7`: a permanent 1% inflation equals a `1/(1 − 0.7) = 3.3%` jump; zero current inflation is possible | `LogLinearIdentities.perm_inflation_equiv`, `LogLinearIdentities.zero_current_inflation_possible` |
| Cochrane p. 69, Figure 3.1, p. 70 | a permanent rise forces the jump `−ω/(1−ω)`, `−4` at `ω = 0.8`; the log price path | `LogLinearIdentities.fig31_jump`, `LogLinearIdentities.fig31_value`, `LogLinearIdentities.fig31_path` |
| Cochrane pp. 69–70 | an expected rise gives no jump; announced `k` periods ahead the jump is `−ωᵏ/(1−ω)`; larger with longer debt and more persistent rises | `LogLinearIdentities.expected_rise_no_jump`, `LogLinearIdentities.announcement_jump`, `LogLinearIdentities.disinflation_monotone_omega`, `LogLinearIdentities.disinflation_monotone_length` |
| A1 p. 560; §3.5.3 (E15) | the exact log drop `−log(1133/1173) ∈ (3.46%, 3.48%)`, the text's "3.5%"; the linear jump is 4% with weight `ω` and `80/23 ≈ 3.48%` with `ω̂ = ω/(1+i)` | `LogLinearIdentities.fig31_log`, `LogLinearIdentities.fig31_linear_exact_coeff`, `Links.e15_reconciled` |
| Cochrane §3.5.4, pp. 70–71 | with perpetuities `ρ = ω̂` the discount-rate terms drop out; the weights differ by `ωʲ ≤ 0.8ʲ` | `LogLinearIdentities.perpetuity_no_discount_terms`, `LogLinearIdentities.weights_close` |
| Cochrane (3.26), p. 68 (new) | the nonlinear mark-to-market valuation is (3.3), with `s`, not `s̃` | `LongTermDebt.valuationLT_iff_const`, `Links.eq_3_26_printed_iff` |

## §3.6.1 Continuous time with short-term debt, (3.29)–(3.33), pp. 71–74; A1.4, pp. 564–565 (ContinuousShort)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §3.6.1, p. 74 | the cumulated rate and the discount function `D(t,τ) = exp(−∫_t^τ r)`: derivative, continuity, additivity, positivity, multiplicativity, the constant-rate case; a zero derivative means constant | `ContinuousShort.cumRate`, `ContinuousShort.disc`, `ContinuousShort.intervalIntegrable_of_ici`, `ContinuousShort.hasDerivAt_cumRate`, `ContinuousShort.continuousOn_cumRate`, `ContinuousShort.cumRate_self`, `ContinuousShort.cumRate_add`, `ContinuousShort.cumRate_const`, `ContinuousShort.disc_pos`, `ContinuousShort.disc_self`, `ContinuousShort.disc_mul`, `ContinuousShort.disc_eq_div`, `ContinuousShort.disc_const`, `ContinuousShort.hasDerivAt_disc`, `ContinuousShort.continuousOn_disc`, `ContinuousShort.eq_of_hasDerivAt_zero` |
| Cochrane §§3.6.1–3.6.3, pp. 74–78 | translating dates or maturities, `∫_0^∞ f(x+j)dj = ∫_x^∞ f` | `ContinuousShort.integral_Ioi_shift` |
| Cochrane (3.30)–(3.31), p. 73 | the flow identity on `[t, ∞)` (the price level may jump at `t`), the TVC, the present value as an improper integral with absolute integrability | `ContinuousShort.FlowOn`, `ContinuousShort.TVC`, `ContinuousShort.pv`, `ContinuousShort.PVIntegrable` |
| A1.4, p. 564; (3.31) | `d(DV) = −Ds`; the finite-horizon identity; `DV` converges; **valuation iff TVC** | `ContinuousShort.hasDerivAt_disc_mul`, `ContinuousShort.pv_finite`, `ContinuousShort.tendsto_disc_mul`, `ContinuousShort.valuation_iff_tvc` |
| Cochrane (3.31), §3.6.1 | the present value at later dates; its closed form; existence; restriction to later dates | `ContinuousShort.pvIntegrable_of_le`, `ContinuousShort.pv_eq_of_le`, `ContinuousShort.pv_eqOn_closed`, `ContinuousShort.flowOn_pv`, `ContinuousShort.tvc_pv`, `ContinuousShort.FlowOn.mono`, `ContinuousShort.TVC.mono` |
| Cochrane (3.30)–(3.31); A1.4, pp. 564–565 ("work either up or down") | uniqueness; every solution is the present value plus a bubble `c/D`, and the bubble satisfies the TVC iff `c = 0`; the present value at every date iff flow + TVC | `ContinuousShort.eqOn_pv_of_tvc`, `ContinuousShort.exists_unique_flow_tvc`, `ContinuousShort.flow_general_solution`, `ContinuousShort.flowOn_bubble`, `ContinuousShort.tvc_bubble_iff`, `ContinuousShort.tvc_iff_eqOn_pv`, `ContinuousShort.flowOn_tvc_of_eqOn_pv`, `ContinuousShort.eqOn_pv_iff_flowOn_tvc` |
| Cochrane (3.31), p. 73 | the price level is determined, `P(t) = B(t)/∫Ds`; positive; none when the present value is not positive; news moves `P(t)` by the ratio of present values | `ContinuousShort.price_level_determined`, `ContinuousShort.price_level_pos`, `ContinuousShort.no_positive_price_level`, `ContinuousShort.price_jump_ratio` |
| Cochrane (3.29)–(3.30), p. 73 | nominal flow iff real flow; `dR = i dt + d(1/P)/(1/P) = (i − π)dt`; from nominal paths to the real flow and the price level; the nominal valuation iff (3.29) + TVC | `ContinuousShort.hasDerivAt_real_of_nominal`, `ContinuousShort.hasDerivAt_nominal_of_real`, `ContinuousShort.hasDerivAt_inv_price`, `ContinuousShort.flowOn_of_nominal`, `ContinuousShort.price_level_of_nominal`, `ContinuousShort.nominal_pv_iff_flow` |
| Cochrane p. 74; A1 (1.26), p. 564 | `Λ(τ) = Λ(t)D(t,τ)`; `r = −Λ'/Λ`; `(Λ/P)' = −i(Λ/P)`; `(1/(PW))' = −i/(PW)` | `ContinuousShort.discountFactor_eq`, `ContinuousShort.rate_eq_neg_logDeriv`, `ContinuousShort.hasDerivAt_nominal_discount`, `ContinuousShort.hasDerivAt_inv_PW` |
| A1.4, pp. 564–565 | the discount-factor and ex-post-return chains, real and nominal | `ContinuousShort.flow_iff_Lambda`, `ContinuousShort.nominal_flow_iff_Lambda`, `ContinuousShort.flow_iff_W`, `ContinuousShort.nominal_flow_iff_W` |
| Cochrane (3.32)–(3.33), p. 74; box p. 71 | `W(τ)/W(t₀) = exp(∫i)P(t₀)/P(τ)`; `W(t)/W(τ) = D(t,τ)`; valuation with `W` iff `V/W → 0`; with a generic `Λ` iff `ΛV → 0` | `ContinuousShort.W_closed_form`, `ContinuousShort.disc_eq_W_ratio`, `ContinuousShort.valuation_W_iff`, `ContinuousShort.valuation_Lambda_iff` |
| Cochrane p. 74; A1 (1.17) | constant rate: the present value `∫e^{−c(τ−t)}s`; a constant surplus is worth `s₀/c`; `V = s₀/c` is the unique solution | `ContinuousShort.pv_const_rate`, `ContinuousShort.pvIntegrable_const`, `ContinuousShort.pv_const_const`, `ContinuousShort.value_const_const` |

## §3.6.2 Continuous time with long-term debt, (3.34)–(3.39), pp. 74–75; A1.2.1 and A1.5, pp. 559–566 (ContinuousLong)

| Book | Claim | Lean |
| --- | --- | --- |
| A1.2.1, pp. 559–560; (3.47) | the bundle paying `e^{−ω(u−t)}`: its price as zero-coupon prices times the geometric coupon; integrability; `Q' = (i + ω)Q − 1`; its TVC; uniqueness; `1/(i₀ + ω)` at a constant rate; positivity | `ContinuousLong.bondPrice`, `ContinuousLong.BondIntegrable`, `ContinuousLong.cumRate_add_const`, `ContinuousLong.disc_add_const`, `ContinuousLong.bondPrice_eq`, `ContinuousLong.bondIntegrable_of_ge`, `ContinuousLong.bondPrice_flow`, `ContinuousLong.bondPrice_tvc`, `ContinuousLong.bondPrice_unique`, `ContinuousLong.bondPrice_const`, `ContinuousLong.bondIntegrable_const`, `ContinuousLong.bondPrice_pos` |
| A1 p. 560 ("`ϖ = ∞` is instantaneous debt") (E20) | in the book's normalisation `ωQ → 1` as `ω → ∞` | `ContinuousLong.tendsto_book_bondValue` |
| Cochrane (3.34), p. 74; Notation p. xxvi (E31) | the debt density `B(t)e^{−ω(m−t)}`; the bond due now; net sales `(B' + ωB)e^{−ω(m−t)}`; the flow is `Q(B' + ωB) = B − Ps` | `ContinuousLong.debtDensity`, `ContinuousLong.debtDensity_self`, `ContinuousLong.hasDerivAt_debtDensity`, `ContinuousLong.flow_LT_geometric` |
| Cochrane (3.37)–(3.39), p. 75; (3.47) | for any bond-price path `V' = (R − π)V − s` with `R = (1 + Q' − ωQ)/Q`; under pricing `R = i`, `(QB)' = iQB − Ps`, and `V` solves the short-debt flow | `ContinuousLong.hasDerivAt_nominal_value`, `ContinuousLong.hasDerivAt_value_LT`, `ContinuousLong.nominalReturn_eq`, `ContinuousLong.hasDerivAt_nominal_value_priced`, `ContinuousLong.flowOn_value_LT` |
| Cochrane (3.35)–(3.36), p. 75 | valuation iff TVC; `P(t) = Q(t)B(t)/∫Ds`; with `W` iff `V/W → 0` | `ContinuousLong.valuation_LT_iff`, `ContinuousLong.price_level_LT`, `ContinuousLong.valuation_LT_W_iff` |
| Cochrane (3.37)–(3.39), p. 75, finite portfolio | an arbitrary finite portfolio: value growth, value-weighted returns, return `i` under pricing | `ContinuousLong.hasDerivAt_value_portfolio`, `ContinuousLong.portfolio_return_weights`, `ContinuousLong.hasDerivAt_value_portfolio_priced` |
| Cochrane §3.6.2, pp. 74–75, general maturity structure | the partial-derivative map; the diagonal and maturity derivatives; market value, issuance, capital gain, value-weighted return; **the regularity the book leaves implicit** | `ContinuousLong.partialsCLM`, `ContinuousLong.partialsCLM_apply`, `ContinuousLong.hasDerivAt_diag`, `ContinuousLong.hasDerivAt_maturity`, `ContinuousLong.mktValue`, `ContinuousLong.issuanceValue`, `ContinuousLong.capitalGain`, `ContinuousLong.valueWeightedReturn`, `ContinuousLong.MaturityRegularAt` |
| Cochrane (3.34), (3.37)–(3.39), p. 75, general maturity structure | the differential of `∫QB dj` (capital gains + net sales − maturing debt); with par and the flow (3.34); (3.37) as a value-weighted average; (3.39) `dV = −s dt + V dR` | `ContinuousLong.hasDerivAt_mktValue`, `ContinuousLong.hasDerivAt_mktValue_flow`, `ContinuousLong.valueWeightedReturn_eq`, `ContinuousLong.hasDerivAt_value_general` |
| Cochrane (3.35), (3.39), p. 75, general maturity structure with pricing | zero-coupon prices meet the pricing and par conditions; the value-weighted return is `i`; the short-debt flow; `V` solves the flow; valuation iff TVC and the price level | `ContinuousLong.zeroPrice_partials`, `ContinuousLong.capitalGain_priced`, `ContinuousLong.hasDerivAt_mktValue_priced`, `ContinuousLong.flowOn_value_general`, `ContinuousLong.valuation_general_iff` |
| Cochrane (3.34)–(3.35), special cases | the general value and flow reduce to the geometric bundle and to a finite portfolio | `ContinuousLong.mktValue_geometric`, `ContinuousLong.flow_general_geometric_iff`, `ContinuousLong.mktValue_finite`, `ContinuousLong.flow_general_finite_iff` |
| A1.5 (1.27)–(1.28), p. 566 (E23) | the integrated form with its limit term; (1.28) iff `V/W → 0`; "so the limit is zero" fails; every bubble violates (1.28); with `s ≥ 0`, `V/W` is nonincreasing | `ContinuousLong.A15_integrated`, `ContinuousLong.A15_valuation_iff`, `ContinuousLong.A15_counterexample`, `ContinuousLong.bubble_not_valuation`, `ContinuousLong.V_over_W_antitone` |
| A1.5 (1.29)–(1.30), p. 566 | the stock return; the stock price as a present value at its ex-post return | `ContinuousLong.stock_return_iff`, `ContinuousLong.stock_price_valuation` |
| A1.5, p. 566 | `E_t[d(ΛW)] = 0` (deterministic: `ΛW` constant); `ΛV = ∫Λs` | `ContinuousLong.Lambda_W_const`, `ContinuousLong.Lambda_valuation` |
| A1.5, p. 566 (new) | at jump points `V/W` does not jump and `W⁺/W⁻ = V⁺/V⁻`; the printed `dW/W = dP/P` has the wrong sign for short debt | `ContinuousLong.jump_V_over_W`, `ContinuousLong.jump_short_return_sign` |
| A1.2.1, (1.17)–(1.18), pp. 559–561 | the steady state with roll-over `ωB̄`; the jump from the valuation equation; `P(0)/P(0⁻) = (r + ω)/(i + ω)` with an explicit post-jump equilibrium | `ContinuousLong.steady_state_LT`, `ContinuousLong.price_jump_of_valuation`, `ContinuousLong.price_jump_permanent`, `ContinuousLong.post_jump_equilibrium` |
| A1 (1.20), p. 560 | the perpetuity `r/i`; 3% to 4% gives exactly 25% | `ContinuousLong.price_jump_perpetuity`, `ContinuousLong.price_jump_perpetuity_numeric` |
| A1 p. 560 (E20) | instantaneous debt, `ω → ∞`, gives no jump; the jump lies in `(0, 1)`; shorter maturity, smaller jump | `ContinuousLong.price_jump_tendsto_one`, `ContinuousLong.price_jump_lt_one`, `ContinuousLong.price_jump_mono` |
| A1 p. 561, continuous forward guidance | the rate path; cumulated rates before and after `T`; the bundle price; `P(0)/P(0⁻) − 1 = e^{−(r+ω)T}((r+ω)/(i+ω) − 1)`; `T = 0` is (1.18); the jump goes to zero, is negative, shrinks with `T` and with `ω` | `ContinuousLong.fgRate`, `ContinuousLong.cumRate_fg_le`, `ContinuousLong.cumRate_fg_ge`, `ContinuousLong.bondPrice_fg`, `ContinuousLong.price_jump_fg`, `ContinuousLong.fg_jump_at_zero`, `ContinuousLong.fg_jump_tendsto_zero`, `ContinuousLong.fg_jump_neg`, `ContinuousLong.fg_jump_antitone_T`, `ContinuousLong.fg_jump_antitone_ω` |

## §3.6.3 Linearised identities in continuous time, (3.39)–(3.51), pp. 76–79 (ContinuousLinear)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (3.29)–(3.31), pp. 73–74 | the valuation engine for a general discount factor `Λ' = −rΛ`: integrating a flow forward; tails vanish; `(ΛV)' = −Λf`; the discounted value converges; **TVC iff valuation**; at every date; uniqueness; existence | `ContinuousLinear.tendsto_of_hasDerivAt`, `ContinuousLinear.tendsto_integral_Ioi_zero`, `ContinuousLinear.discounted_hasDerivAt`, `ContinuousLinear.discounted_tendsto`, `ContinuousLinear.integral_ratio_eq`, `ContinuousLinear.tvc_iff_valuation`, `ContinuousLinear.valuation_every_date`, `ContinuousLinear.valuation_unique`, `ContinuousLinear.valuation_exists` |
| Cochrane p. 74 | the constant-rate discount factor; valuation iff TVC at a constant rate | `ContinuousLinear.hasDerivAt_expDisc`, `ContinuousLinear.expDisc_ratio`, `ContinuousLinear.const_rate_tvc_iff` |
| Cochrane (3.41)–(3.43), p. 76 | the shifted form `∫_0^∞ e^{−rτ}x_{t+τ}dτ`: integrability and the weighted integral | `ContinuousLinear.integrableOn_shift`, `ContinuousLinear.integrableOn_shift_weighted`, `ContinuousLinear.shift_weighted`, `ContinuousLinear.integral_weighted_sub` |
| Cochrane (3.39)–(3.40), p. 76 | the steady state `s̄ = rV̄`; the exact derivative of the flow map; the second-order remainder; the deviation form | `ContinuousLinear.steady_state_iff`, `ContinuousLinear.flow_hasFDerivAt`, `ContinuousLinear.flow_remainder`, `ContinuousLinear.flow_deviation_form` |
| Cochrane (3.41)–(3.43), p. 76 (E21) | the normalised flow (3.42); the value identity iff the TVC; the two-integral form; (3.41) in levels with the integrand dated `t + τ` | `ContinuousLinear.normalised_flow`, `ContinuousLinear.linear_value_iff`, `ContinuousLinear.linear_value_split`, `ContinuousLinear.value_identity_341` |
| Cochrane p. 76 | `dR = dR^n − π dt`; `d(1/P)/(1/P) = −dP/P` | `ContinuousLinear.real_return_of_nominal`, `ContinuousLinear.inv_price_growth` |
| Cochrane p. 77 (E18) | `ds = −ηs dt` is solved by `e^{−ητ}s_0` only; the printed `+ s̄` path is not a solution; the present value `s_t/(r + η)`; news `σ/(r + η)` | `ContinuousLinear.ar1_hasDerivAt`, `ContinuousLinear.ar1_unique`, `ContinuousLinear.ar1_printed_not_solution`, `ContinuousLinear.ar1_integrable`, `ContinuousLinear.ar1_pv`, `ContinuousLinear.ar1_news` |
| Cochrane p. 77; (3.47), pp. 77–78 (E22) | `Q = 1/(ω + y)`; the holding return converges to `(1 + Q')/Q − ω = y + Q'/Q`; the identity `Q dR^n = dt + dQ − ωQ dt` | `ContinuousLinear.bond_price_yield`, `ContinuousLinear.holding_return_tendsto`, `ContinuousLinear.return_eq_yield`, `ContinuousLinear.return_identity_iff` |
| Cochrane p. 78; (3.48) (E19) | the steady state `Q̄ = 1/(r + ω)`; the exact derivative; (3.48); the corrected intermediate line; the printed line forces `q = 1`; counterexample | `ContinuousLinear.bond_steady_state`, `ContinuousLinear.bond_hasFDerivAt`, `ContinuousLinear.bond_linear_iff`, `ContinuousLinear.bond_linear_corrected_line`, `ContinuousLinear.printed_line_forces_steady`, `ContinuousLinear.printed_line_counterexample` |
| Cochrane (3.49), p. 78 | the forward solution iff the TVC; bounded paths satisfy the TVC; uniqueness among bounded solutions; existence with `\|q^F − 1\| ≤ K/(r + ω)` | `ContinuousLinear.bond_price_forward_iff`, `ContinuousLinear.tvc_of_bounded`, `ContinuousLinear.bond_price_forward_bounded`, `ContinuousLinear.bondForward`, `ContinuousLinear.bondForward_spec` |
| Cochrane (3.35), (3.46), pp. 75–78 | `V = Qb` linearised, `v − 1 = (q − 1) + (β − 1)`, with its exact remainder; the unexpected bond return is the price jump | `ContinuousLinear.value_hasFDerivAt`, `ContinuousLinear.value_remainder`, `ContinuousLinear.news_return_tendsto` |
| Cochrane (3.42)–(3.49), pp. 76–78 | innovations as the difference between two perfect-foresight equilibria of the linearised model; the steady state is one; value, bond price and integrability in an equilibrium | `ContinuousLinear.Eqm.LinearEqm`, `ContinuousLinear.steady_state_eqm`, `ContinuousLinear.eqm_value`, `ContinuousLinear.eqm_bond`, `ContinuousLinear.eqm_int_real_bond`, `ContinuousLinear.eqm_int_infl` |
| Cochrane p. 77; (3.46), (3.50)–(3.51), pp. 77–78 | `Δ_tdv_t = Δ_tdR^n_t`; the value news identity; the bond-return news identity, nominal and real; the weighted-inflation identity | `ContinuousLinear.news_value_eq_bond`, `ContinuousLinear.news_value`, `ContinuousLinear.news_bond`, `ContinuousLinear.news_bond_real`, `ContinuousLinear.news_weighted_inflation` |
| Cochrane pp. 78–79 (E20) | with no bond-price jump, fiscal news equals discount-rate news; the left side of (3.51) tends to `0` as `ω → ∞`; the limit identity; at `ω = 0` (perpetuity, price `1/y`) it is `1/r` for `Δπ ≡ 1`; `ω → ∞` is instantaneous debt | `ContinuousLinear.short_debt_news`, `ContinuousLinear.short_limit_integrable`, `ContinuousLinear.short_limit`, `ContinuousLinear.short_limit_single`, `ContinuousLinear.short_debt_limit_identity`, `ContinuousLinear.perpetuity_lhs_ne_zero`, `ContinuousLinear.perpetuity_price`, `ContinuousLinear.instantaneous_limit` |
| Cochrane p. 78 | inflation news at the single instant `t` contributes nothing to (3.51) | `ContinuousLinear.lhs_ignores_one_date` |

## §3.6.4 Money in continuous time, (3.52)–(3.55), pp. 79–80; A1.6, pp. 567–568 (ContinuousMoney)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (3.52), p. 79; A1 (1.31) | the flow with money in real terms | `ContinuousMoney.flow_real` |
| A1 (1.26), p. 564; (1.35), p. 568 | `i = r + π`; `1/(PW)` is a nominal discount factor; `Λ_τ/Λ_t = W_t/W_τ` | `ContinuousMoney.nominal_discount_of_real`, `ContinuousMoney.inv_nominal_value`, `ContinuousMoney.lambda_ratio_eq_W` |
| Cochrane (3.31), (3.53); A1.6 | the forward-integration step in iff form; the conversion to the real form | `ContinuousMoney.forward_iff`, `ContinuousMoney.real_form_iff` |
| Cochrane (3.53), p. 79; A1 (1.32)–(1.33), p. 567 | money creation: `d(NB) = −NP(s + dM/P)`; the valuation iff the TVC on `B` | `ContinuousMoney.printing_hasDerivAt`, `ContinuousMoney.money_printing_iff` |
| Cochrane (3.54), p. 79; A1 (1.34), p. 567 | interest saving: the valuation iff the TVC on `M + B` | `ContinuousMoney.interest_hasDerivAt`, `ContinuousMoney.money_interest_iff` |
| §3.6.4; A1.6 (E13, continuous) | given (3.53), (3.54) iff the money TVC; a path where (3.53) holds and (3.54) fails | `ContinuousMoney.printing_interest_iff_money_tvc`, `ContinuousMoney.printing_without_interest_example` |
| Cochrane p. 79; A1 (1.36), p. 568 (E21) | ex-post discounting with `W`, money creation and interest saving, integrand dated `τ`; the printed `(i_t − i^m_t)` gives `1/2` where the truth is `1` | `ContinuousMoney.printing_W_hasDerivAt`, `ContinuousMoney.money_printing_W_iff`, `ContinuousMoney.interest_W_hasDerivAt`, `ContinuousMoney.money_interest_W_iff`, `ContinuousMoney.printed_index_counterexample` |
| Cochrane (3.55), p. 80; A1 (1.37) | the mixed portfolio return folds seigniorage into the discount rate; it lies below `i` | `ContinuousMoney.mixed_hasDerivAt`, `ContinuousMoney.money_mixed_iff`, `ContinuousMoney.mixed_rate_lt` |

## Online Appendix A1.9.1 State variables, (1.47)–(1.50), pp. 576–577 (MSV)

| Book | Claim | Lean |
| --- | --- | --- |
| A1 (1.47)–(1.50), p. 576 | the equilibrium of the simplest model; the forward equation `v_t = ρE_tv_{t+1} + E_ts_{t+1}`; inflation from (1.48) | `MSV.Eqm`, `MSV.eqm_solves`, `MSV.eqm_infl` |
| A1 pp. 576–577 | the forward solution `v*` and its inflation; existence; uniqueness of debt and inflation with bounded debt; bounded debt iff `v = v*` | `MSV.vstar`, `MSV.vstar_apply`, `MSV.forcing_ok`, `MSV.inflStar`, `MSV.msv_exists`, `MSV.msv_v_unique`, `MSV.msv_unique`, `MSV.msv_determinacy` |
| A1 p. 576 (E24) | `π_{t+1} = i_t − ΔE_{t+1}∑ρʲs_{t+1+j}`; with AR(1) surpluses `v_t = η_su_{s,t}/(1 − ρη_s)`, `π_{t+1} = u_{i,t} − ε_{s,t+1}/(1 − ρη_s)`, an equilibrium | `MSV.msv_infl_innov`, `MSV.vstar_ar1`, `MSV.msv_solution`, `MSV.msv_solution_is_eqm` |
| A1 p. 576 (E24) | the printed `+` is no bounded-debt equilibrium once a surplus shock is nonzero; on the coin-flip tree | `MSV.msv_printed_not_eqm`, `MSV.coin_bdd`, `MSV.msv_printed_fails_coin` |
| A1 p. 577 (E24) | undetermined coefficients: the guess works iff `A`, `B` take the corrected values, under `ρ ≠ 0`, `ρη_i ≠ 1`, `ρη_s ≠ 1`; the printed `B_{πs}` fails | `MSV.GuessOK`, `MSV.msv_coeffs_iff`, `MSV.msv_coeffs_printed_fails` |
| A1 p. 577 (restated from the Woodford Chapter 4 project) | the scalar recursion `d_{t+1} = γd_t + u_t`: determined by `d_0`; bounded-input-bounded-state iff `\|γ\| < 1` | `MSV.dRec`, `MSV.eq_dRec`, `MSV.abs_rec_le`, `MSV.rec_bounded`, `MSV.rec_unbounded` |
| A1 p. 577 ("determinacy comes … from the assumption that `v_t` is a time-invariant function of the state variables") | debt follows the explosive root `ρ⁻¹`, so bounded debt is a genuine restriction; deviations from `v*` explode in expectation | `MSV.msv_debt_rec`, `MSV.msv_debt_not_bibo`, `MSV.msv_deviation_iterate`, `MSV.msv_deviation_explodes` |

## Links among the four formalisation chains (Links)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (3.5), (3.10)–(3.12), pp. 55–59 | the money chain's present value and TVC (levels of `Λ`) are the long-term-debt chain's with `m_s = Λ_{s+1}/Λ_s` | `Links.pvRel_iff_pv`, `Links.tvc_money_iff_tvc` |
| Cochrane p. 55; footnote 1, p. 58 | the money chain's recursion and TVC are `LongTermDebt.FlowRec` and `LongTermDebt.TVC` with `m ≡ 1` | `Links.flowRec_one_iff`, `Links.tvc_one_iff` |
| Cochrane (3.5), p. 55, with `Λ_t = βᵗ`; (3.3), p. 53 | `m ≡ β`; the present value `∑βⁿE_ts_{t+n}`; the printed form; flow + TVC iff the constant-`β` valuation of (3.3) and Chapter 2 | `Links.sdf_ratio_pow`, `Links.pv_beta_pow`, `Links.pv_lambda_beta`, `Links.valuation_sdf_beta_iff` |
| Cochrane (3.1)–(3.3), (3.5); A1 p. 559 | short-term debt is `ω = 0`: the annuity, the value and the flow are one-period; the bond maturing next period is the one-period bond; `LongTermDebt.valuationGeom_iff` at `ω = 0` is `StochasticDiscount.valuation_sdf_iff` | `Links.annuity_zero`, `Links.geomValue_zero`, `Links.geomFlow_zero_iff`, `Links.zeroPrice_one_eq_bondPrice`, `Links.geomFlow_zero_iff_flowOne`, `Links.valuationGeom_zero_iff` |
| A1 p. 560; pp. 78–79 (E20) | discrete `ω = e^{−ϖ} → 0` gives `LongTermDebt.jumpRatio` → 1; continuous `ϖ → ∞` gives `ϖQ → 1` and `(r+ϖ)/(i+ϖ) → 1` | `Links.jumpRatio_tendsto_short`, `Links.short_debt_limits` |
| Cochrane (3.22), p. 65, and (3.51), p. 78; A1 (1.22) | with `ω = e^{−ϖ}`, `1 + i = e^r`, `ρ = e^{−r}`: `ω̂ = e^{−(r+ϖ)}`, and the discrete weights equal the continuous ones on the integer grid; the endpoints `ϖ = 0 ↔ ω = 1`, `ϖ → ∞ ↔ ω → 0` | `Links.bond_coeff_exp`, `Links.weights_322_351`, `Links.omega_disc_endpoints` |
| A1 (1.14), p. 559, and (3.47)/A1 (1.17) | with period length `h`, the discrete annuity tends to the continuous bond price `1/(i + ϖ)` | `Links.tendsto_slope_exp_sub`, `Links.annuity_tendsto_bondPrice` |
| A1 (1.16), p. 559, and (1.18), p. 560 | the discrete jump ratio tends to `(r + ϖ)/(i + ϖ)` | `Links.jumpRatio_tendsto_continuous` |
| A1 p. 560 and Figure 3.1, p. 69 (E15) | **one statement set:** exact proportional drop `40/1173 ∈ (3.41%, 3.42%)`; exact log drop in `(3.46%, 3.48%)`; linear 4% with `ω`; `80/23 ∈ (3.47, 3.48)` with `ω/(1+i)` | `Links.e15_reconciled` |
| Cochrane pp. 54, 64; A1 (1.14), (1.23) | `Ratios.E_innov_zero` for `LogLinearIdentities.innov`; `LogLinearIdentities.geomQ` is `LongTermDebt.geom_value/(1+i)` | `Links.E_innov_eq_zero`, `Links.geomQ_eq_geom_value_div` |
| Cochrane (3.31), p. 73; A1.4; p. 74 | the general engine of `ContinuousLinear` at `Λ = ContinuousShort.disc` gives `ContinuousShort`'s valuation iff TVC; the constant-rate factors agree | `Links.hasDerivAt_disc_of_continuous`, `Links.tvc_iff_pv_of_engine`, `Links.expDisc_ratio_eq_disc` |
| Cochrane p. 57; §3.6.4, A1.6 (E13) | the discrete and continuous counterexamples side by side: the `ΔM/P` valuation holds, the `iM/P` valuation fails | `Links.e13_discrete_and_continuous` |
| Cochrane (3.26), p. 68 (new) | with `s̃ = κs` the printed (3.26) is compatible with (3.3) only if `κ = 1` or the value of debt is zero | `Links.eq_3_26_printed_iff` |

## Shared tools

| Book | Claim | Lean |
| --- | --- | --- |
| Chapter 3 throughout (discrete time) | the expectation axioms, adaptedness, pull-out, perfect foresight; finite event trees and their pull-out property; bounded processes; `E_t` of a geometric series | `ExpectationSystem`, `ExpectationSystem.Adapted`, `ExpectationSystem.PullOut`, `perfectForesight`, `perfectForesight_pullOut`, `ExpectationsFiniteTree.FiniteTree`, `ExpectationsFiniteTree.FiniteTree.toExpectationSystem`, `ExpectationsFiniteTree.finiteTree_pullOut`, `BoundedProc`, `ExpectationSystem.E_tsum`, `ForwardSolution.E_tsum_dom` |
| A1 pp. 576–577 (`MSV`) | the forward series and its solution, boundedness and adaptedness; known variables; AR(1) iteration; the coin-flip tree with i.i.d. and AR(1) shocks | `ExpectationSystem.forwardSeries`, `ForwardSolution.Solves`, `ForwardSolution.forwardSeries_solves_abs`, `ForwardSolution.forwardSeries_bounded_abs`, `ForwardSolution.forwardSeries_adapted_abs`, `ForwardSolution.eq_forwardSeries_abs`, `ForwardSolution.E_of_known`, `ExpectationSystem.IsAR1`, `ExpectationSystem.ar1_iterate`, `ExpectationsFiniteTree.coinSystem`, `ExpectationsFiniteTree.coinShock`, `ExpectationsFiniteTree.coinAR1`, `ExpectationsFiniteTree.coinAR1_isAR1`, `ExpectationsFiniteTree.coinAR1_nondegenerate` |
| shared core, not used by Chapter 3 | the bounded forward solution and Schur–Cohn determinacy, carried for the later Cochrane projects | `ForwardSolution.existsUnique_bounded`, `SchurStable`, `schurStable_iff_roots` |
