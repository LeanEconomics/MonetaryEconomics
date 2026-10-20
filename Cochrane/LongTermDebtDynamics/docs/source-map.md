# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 7, "Long-term debt dynamics"
(pp. 212–236), with Online Appendix §A1.2.1 (pp. 559–561) and §A1.14 (pp. 588–592). Each formal
claim is listed with its Lean name, relative to the namespace `Cochrane.LongTermDebtDynamics`.
Page numbers are book pages; "App." marks the Online Appendix, whose equations are numbered
(1.14)–(1.20) and (1.63)–(1.68). The book has no labelled propositions, so rows are keyed by
equation number, section or page. Rows follow the book section by section, and each heading names
the modules that formalise the section: the opening pages, §§7.1–7.6 with the two appendix
sections next to the sections that use them, then the shared tools. "Theorem W" and "Theorem P"
are the labels of the chapter survey.

`D t m` is the book's `B_{t−1}^{(m)}`, the primitive price variable is `x_t = 1/P_t`, and in §7.4
`y_t = B_{t−1}^{(t)}/P_t` and `A_t^{(m)} = (B_t^{(m)} − B_{t−1}^{(m)})/B_{m−1}^{(m)}`. The
structural results hold for an arbitrary `ExpectationSystem` with `ExpectationSystem.PullOut`;
forward guidance, §7.6.1 and the counterexample are deterministic. The shared core
(`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is cited where a row
uses it.

## Opening: flow and present value with long-term debt, pp. 212–213 and 216 (MaturityStructure)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 212 | sales at `t` of maturity-`m` debt, `B_t^{(m)} − B_{t−1}^{(m)}`; debt is predetermined, so debt outstanding at the start of `t`, and debt chosen at `t`, is known at every later date | `MaturityStructure.sales`, `MaturityStructure.Predetermined`, `MaturityStructure.Predetermined.known`, `MaturityStructure.Predetermined.known_succ` |
| Cochrane p. 212 | `Q_t^{(t+j)} = β^jE_t(P_t/P_{t+j}) = β^jP_tE_t(1/P_{t+j})` | `MaturityStructure.bondPrice`, `MaturityStructure.bondPrice_eq` |
| Cochrane (3.2) recalled, p. 212; (7.1), p. 213; (7.4), p. 216 | the nominal flow condition, as a convergent series in every state, is the real flow condition (7.1) when `P_t > 0` | `MaturityStructure.NominalFlow`, `MaturityStructure.RealFlow`, `MaturityStructure.nominalFlow_iff_realFlow` |
| Cochrane (3.3) recalled, p. 212 | the nominal market value of debt is `P_t` times the real value `V_t` of (7.2) | `MaturityStructure.nominalValue_eq` |
| Cochrane (7.2), p. 213; (7.5), p. 216 | the real value of debt `V_t = ∑_j β^jB_{t−1}^{(t+j)}E_t(1/P_{t+j})`, the present value of surpluses, the present-value relation with both sides convergent series, and the domination hypothesis that lets `E_t` pass through the series | `MaturityStructure.debtTerm`, `MaturityStructure.debtValue`, `MaturityStructure.surplusTerm`, `MaturityStructure.pvSurplus`, `MaturityStructure.PresentValue`, `MaturityStructure.DebtDominated`, `MaturityStructure.hasSum_E_debtValue_succ` |
| Cochrane (7.1)–(7.2), p. 213 | the flow condition at `t` is the recursion `V_t = s_t + βE_tV_{t+1}`; `V_t` is then known at `t`; iterating, `V_t = ∑_{k<N} β^kE_ts_{t+k} + β^NE_tV_{t+N}` | `MaturityStructure.realFlow_iff_recursion`, `MaturityStructure.debtValue_adapted`, `MaturityStructure.debtValue_iterate` |
| Cochrane (7.2), p. 213 | bounded surpluses have an absolutely convergent present value, which satisfies the same recursion | `MaturityStructure.summable_surplusTerm`, `MaturityStructure.pvSurplus_recursion` |
| Cochrane (7.2), p. 213 | the transversality condition `β^NE_tV_{t+N} → 0`; given the flow conditions, the present-value relation at `t` holds iff it does | `MaturityStructure.Transversality`, `MaturityStructure.presentValue_iff_tvc` |
| Cochrane (7.1)–(7.2), p. 213; (7.4)–(7.5), p. 216 | the flow conditions at every date plus transversality are equivalent to the present-value relations at every date | `MaturityStructure.flow_tvc_iff_presentValue` |
| Cochrane (7.1)–(7.2), p. 213 | a bounded real value of debt satisfies transversality, so the flow conditions imply the present-value relations | `MaturityStructure.transversality_of_bounded`, `MaturityStructure.presentValue_of_bounded` |

## §7.1 Forward guidance and bond-price targets, (7.3), pp. 213–215 (ForwardGuidance)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 214 | bond prices after the announcement that the rate rises from `r` to `i` at `T`: `Q_0^{(j)} = (1+r)^{−j}` for `j ≤ T`, `Q_0^{(T+j)} = ((1+r)^T(1+i)^j)^{−1}`; unchanged prices without a rate change | `ForwardGuidance.fgPrice`, `ForwardGuidance.fgPrice_of_le`, `ForwardGuidance.fgPrice_add`, `ForwardGuidance.fgPrice_same` |
| Cochrane p. 214 | `Q_0^{(T+j)} > (1+i)^{−(T+j)}`, and bonds maturing after `T` fall in price | `ForwardGuidance.inv_pow_lt_fgPrice`, `ForwardGuidance.fgPrice_lt` |
| Cochrane p. 213 | bond prices rise with the horizon `T` | `ForwardGuidance.fgPrice_mono` |
| Cochrane pp. 214–215 | the rate path and the perfect-foresight price path, which satisfies the Fisher relation and is the only path that does | `ForwardGuidance.fgRate`, `ForwardGuidance.fgPath`, `ForwardGuidance.fgPath_succ`, `ForwardGuidance.fgPath_unique` |
| Cochrane bullet p. 215 | no second jump: the price level stays at `P_0` through `T`, and inflation starts when the rate rises | `ForwardGuidance.fgPath_eq_of_le`, `ForwardGuidance.fgPath_jump` |
| Cochrane p. 214 | the forward-guidance prices are `β^jP_0/P_j` along the path | `ForwardGuidance.fgPrice_eq_path` |
| Cochrane (7.3), pp. 214–215 | the valuation equation pins down `P_0` from bond prices or bond-price targets | `ForwardGuidance.priceLevel`, `ForwardGuidance.valuation_iff` |
| Cochrane p. 214 | guidance beyond the longest maturity `k` leaves `P_0` unchanged for `T ≥ k` (book: `T > k`), and `T ≥ k` is sharp (E7.6) | `ForwardGuidance.priceLevel_fg_of_le`, `ForwardGuidance.priceLevel_fg_lt` |
| Cochrane bullets p. 213 | the effect of guidance falls with the horizon and is smaller than that of the same immediate rise | `ForwardGuidance.priceLevel_mono`, `ForwardGuidance.priceLevel_immediate_le` |

## Online Appendix §A1.2.1, forward guidance with geometric maturity, pp. 559–561 (ForwardGuidance)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane App. p. 560 | the valuation sum `∑_j Q_0^{(j)}ω^j` in closed form, as a convergent series | `ForwardGuidance.fgSum`, `ForwardGuidance.hasSum_fg_geometric` |
| Cochrane App. (1.15), p. 559 | without a rate change the sum is `(1+r)/(1+r−ω)` | `ForwardGuidance.fgSum_same` |
| Cochrane App. p. 560 | the discrete forward-guidance formula `P_0/P − 1 = (ω/(1+r))^T[(1+i)(1+r−ω)/((1+r)(1+i−ω)) − 1]`, from the steady state | `ForwardGuidance.fgJump`, `ForwardGuidance.fg_jump_geometric`, `ForwardGuidance.fgJump_eq` |
| Cochrane App. (1.16), p. 559 | an immediate permanent rise gives `P_0/P = (1+i)(1+r−ω)/((1+r)(1+i−ω))` | `ForwardGuidance.fg_jump_immediate` |
| Cochrane App. p. 561 | the jump is negative, shrinks strictly with `T` (by the factor `ω/(1+r)`), tends to zero, and grows with `ω` | `ForwardGuidance.fgJump_neg`, `ForwardGuidance.fgJump_succ`, `ForwardGuidance.fgJump_abs_lt`, `ForwardGuidance.fgJump_tendsto`, `ForwardGuidance.fgJump_abs_mono_omega` |
| Cochrane App. p. 560; Figure 7.1 | with `ω = 0.8`, `r = 2%`, `i = 3%`: the immediate drop is between 3.4% and 3.5%, the `T = 3` drop between 1.6% and 1.7% (book: 3.5% and 1.6%) | `ForwardGuidance.fgJump_calibration` |
| Cochrane App. (1.19), p. 560 | a discrete perpetuity, 3% to 4%: `P_0/P = (1+i)r/((1+r)i) ∈ (0.757, 0.758)`, not the "25%" drop (E7.11) | `ForwardGuidance.perpetuity_ratio_bounds` |
| Cochrane App. p. 561 | the continuous-time integrand and the valuation integral in closed form, as an improper integral | `ForwardGuidance.cfgIntegrand`, `ForwardGuidance.cfgValue`, `ForwardGuidance.integral_cfg` |
| Cochrane App. (1.17), p. 560 | with no rate change the integral is `ϖ/(r+ϖ)` | `ForwardGuidance.cfgValue_same` |
| Cochrane App. p. 561 | the continuous forward-guidance formula `P_0/P − 1 = e^{−(r+ϖ)T}((r+ϖ)/(i+ϖ) − 1)` | `ForwardGuidance.cfgJump`, `ForwardGuidance.cfg_jump` |
| Cochrane App. (1.18), (1.20), p. 560 | `T = 0` gives `(r+ϖ)/(i+ϖ)`, and `r/i` for the perpetuity | `ForwardGuidance.cfgJump_zero` |
| Cochrane App. p. 561 | the continuous jump is negative, shrinks with `T`, vanishes as `T → ∞`, and shrinks with `ϖ` | `ForwardGuidance.cfgJump_neg`, `ForwardGuidance.cfgJump_abs_anti`, `ForwardGuidance.cfgJump_tendsto`, `ForwardGuidance.cfgJump_abs_anti_varpi` |
| Cochrane App. p. 561 | the sales that maintain the geometric structure, `ω^j(1−ω)B = ((1−ω)/ω)B_{t−1}^{(t+j+1)}` | `ForwardGuidance.steady_sales` |

## §7.2.1 Maturing debt and a buffer, (7.4)–(7.6), pp. 216–218 (MaturingDebt)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 216 | no sales or repurchases after the inherited structure; the debt due at `t + k` is then `B_{−1}^{(t+k)}` | `MaturingDebt.NoSales`, `MaturingDebt.debt_eq_initial` |
| Cochrane (7.6), p. 217 | `B_{−1}^{(t)}/P_t = B_{t−1}^{(t)}/P_t = s_t`; conversely `x_t = s_t/B_{−1}^{(t)}` solves every flow condition | `MaturingDebt.price_eq_maturing`, `MaturingDebt.noSales_solution` |
| Cochrane p. 217 | the present-value relation still holds, term by term | `MaturingDebt.noSales_presentValue` |
| Cochrane p. 217 | `B^{(t+j)}E_t(1/P_{t+j}) = E_ts_{t+j}` and `Q_t^{(t+j)}B^{(t+j)} = β^jP_tE_ts_{t+j}` | `MaturingDebt.noSales_E_price`, `MaturingDebt.noSales_bondPrice` |
| Cochrane pp. 216–217 | the buffer: unexpected inflation reflects only news about the current surplus, news about later surpluses moves bond prices, and `P_t` does not depend on later surpluses | `MaturingDebt.noSales_price_news`, `MaturingDebt.noSales_bond_news`, `MaturingDebt.noSales_price_indep` |

## §7.2.2 Intertemporal linkages, runs and defaults, (7.7), pp. 218–220 (MaturingDebt)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (7.7), p. 219 | with one-period debt only, `B_{t−1}^{(t)}/P_t = s_t + βB_t^{(t+1)}E_t(1/P_{t+1}) = s_t + E_t(βB_t^{(t+1)}/P_{t+1})` | `MaturingDebt.OnePeriod`, `MaturingDebt.oneperiod_flow_iff`, `MaturingDebt.oneperiod_flow_E` |
| Cochrane p. 219 | backward induction: with the debt retired at `T`, `B_{t−1}^{(t)}/P_t = ∑_{k ≤ T−t} β^kE_ts_{t+k}`; the last two steps are the display of p. 219 | `MaturingDebt.oneperiod_backward`, `MaturingDebt.oneperiod_two_period` |
| Cochrane pp. 219–220 | fear of low far-future surpluses raises today's price level | `MaturingDebt.oneperiod_fear` |

## §7.3–§7.3.2 Bond sales and bond-price targets, (7.8)–(7.13), pp. 220–224 (BondSales)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 221 | debt is traded at date 0 only; afterwards the debt outstanding is `B_0^{(m)}` | `BondSales.SalesAtZeroOnly`, `BondSales.debt_eq_one` |
| Cochrane (7.9), p. 221 | `B_0^{(t)}/P_t = s_t` for `t ≥ 1`, and `B_0^{(j)}E_0(1/P_j) = E_0s_j` | `BondSales.maturing_eq`, `BondSales.E_price_eq` |
| Cochrane (7.10)–(7.11), p. 221 | `Q_0^{(j)}B_0^{(j)} = β^jP_0E_0s_j`, so real revenue `β^jE_0s_j` does not depend on the amount sold | `BondSales.bondPrice_mul_debt`, `BondSales.real_revenue` |
| Cochrane (7.8), (7.12), pp. 221–222 | the dilution formula `B_{−1}^{(0)}/P_0 = s_0 + ∑_{j≥1} β^j((B_0^{(j)} − B_{−1}^{(j)})/B_0^{(j)})E_0s_j`, as a convergent series | `BondSales.dilution_formula` |
| Cochrane (7.13), p. 222 | with no long-term debt outstanding, `B_{−1}^{(0)}/P_0 = s_0 + ∑_{j≥1} β^jE_0s_j`, and `P_0` does not depend on the sales | `BondSales.no_outstanding`, `BondSales.no_outstanding_price_indep` |
| Cochrane bullets p. 222 | additional sales lower bond prices and raise future price levels | `BondSales.sales_lower_bondPrice`, `BondSales.sales_raise_future_price` |
| Cochrane bullet p. 223 | a bond-price target is supported by a unique, finite quantity; unit elasticity `d log B/d log Q = −1` | `BondSales.bondPrice_target_iff`, `BondSales.unit_elasticity` |
| Cochrane bullet p. 223 | with long-term debt outstanding, additional sales lower `P_0`; the marginal effect on `1/P_0` | `BondSales.outstanding_sales_lower_price`, `BondSales.hasDerivAt_dilution` |
| Cochrane bullet p. 224 | a state-contingent sale offsets a date-0 surplus shock, at the cost of a higher future price level (the content of the innovation form of (7.12), stated at date 0, E7.9) | `BondSales.offset_shock` |

## §7.3.3 Future bond sales, p. 224, and Online Appendix §A1.14, (1.63)–(1.68), pp. 588–592 (FutureSales)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane App. pp. 589–590 | in the three-period economy the flow conditions (7.1) are the three displayed equations | `FutureSales.flows_of_realFlow` |
| Cochrane App. (1.63), p. 589 | `B_1^{(2)}/P_2 = s_2` | `FutureSales.price_two` |
| Cochrane App. (1.64), p. 590 | `B_0^{(1)}/P_1 = s_1 + β((B_1^{(2)} − B_0^{(2)})/B_1^{(2)})E_1s_2`, and its date-0 expectation | `FutureSales.price_one`, `FutureSales.E_price_one` |
| Cochrane App. (1.65)–(1.66), pp. 590–591 | the date-0 price level with the dilution fractions `A₁` and `A₂` | `FutureSales.price_zero` |
| Cochrane App. §A1.14.1, p. 590 | with no long-term debt outstanding the expected sale has no effect on `P_0` | `FutureSales.no_outstanding_price_zero` |
| Cochrane App. bullets pp. 589–590 | expected future sales enter symmetrically with date-0 sales in `P_2` and, with `P_0` fixed, in `Q_0^{(2)}` | `FutureSales.price_two_symm`, `FutureSales.bondPrice_two_symm` |
| Cochrane App. (1.64), p. 590; bullet p. 591 | with deterministic debt, `B_0^{(1)}E_0(1/P_1) = E_0s_1 + β(F/(B_0^{(2)} + F))E_0s_2`; expected sales raise `Q_0^{(1)}` when time-2 debt was sold | `FutureSales.x1_formula`, `FutureSales.future_sales_raise_Q1` |
| Cochrane App. §A1.14.2, p. 591 | with no date-0 sales the expected sale has no effect on `P_0` (interaction only) | `FutureSales.no_time0_sales` |
| Cochrane App. (1.67)–(1.68), p. 592 | no date-0 sale of time-2 debt, and no date-0 sale of time-1 debt, where dilution is relative to all claims | `FutureSales.price_zero_no_sale_two`, `FutureSales.price_zero_no_sale_one` |
| Cochrane App. (1.66), p. 591 | `1/P_0` as a function of the expected sale `F`, agreeing with (1.65) term by term | `FutureSales.x0Fun`, `FutureSales.x0_closed` |
| Cochrane App. bullet p. 592 | `d(1/P_0)/dF` has the sign of `A₁ − A₂`: expected sales lower `P_0` if `A₁ > A₂`, raise it if `A₁ < A₂`, and have no effect if `A₁ = A₂` (E7.10) | `FutureSales.hasDerivAt_x0`, `FutureSales.x0_strictMono`, `FutureSales.x0_strictAnti`, `FutureSales.x0_const` |

## §7.4 A general formula, (7.14)–(7.17), pp. 224–226 (GeneralFormula)

### The system, the weights and Theorem W

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 225 | the fraction sold, `A_t^{(m)} = (B_t^{(m)} − B_{t−1}^{(m)})/B_{m−1}^{(m)}` | `GeneralFormula.fracSold` |
| Cochrane (7.1), (7.14), p. 225 | the flow conditions are the maturing-debt system `y_t = s_t + ∑_j β^{j+1}E_t(A_t^{(t+j+1)}y_{t+j+1})` when the debt coming due is nonzero (E7.1: (7.14) is the flow relation) | `GeneralFormula.MaturingSystem`, `GeneralFormula.realFlow_iff_maturingSystem` |
| Cochrane pp. 225–226 | the weights `W_t^{(0)} = 1`, `W_t^{(k+1)} = ∑_{n≤k} A_{t+n}^{(t+k+1)}W_t^{(n)}` (the book's `W_{t,k}` is `W_t^{(k)}`, E7.5) | `GeneralFormula.weight`, `GeneralFormula.weight_zero`, `GeneralFormula.weight_succ` |
| Cochrane p. 226 | Cochrane's last-step recursion equals the first-step recursion produced by substitution; a triangular reindexing | `GeneralFormula.weight_first_step`, `GeneralFormula.sum_triangle` |
| Cochrane p. 226 | Theorem W (ii): `W_t^{(m)}` is the sum over chains `t = k₀ < … < k_n = t + m` of `∏ A_{k_i}^{(k_{i+1})}`; the chains are the compositions of `m` | `GeneralFormula.comps`, `GeneralFormula.mem_comps`, `GeneralFormula.chainProd`, `GeneralFormula.chainProd_eq`, `GeneralFormula.chainSum`, `GeneralFormula.weight_eq_chainSum` |
| Cochrane p. 226 | if each `A_t^{(t+j+1)}` is known at `t + j`, `W_t^{(m+1)}` is known at `t + m` | `GeneralFormula.weight_known` |
| Cochrane (7.17), p. 225 | Theorem W, finite horizon: with no debt due after `T`, `y_t = ∑_{m ≤ T−t} β^mE_t(W_t^{(m)}s_{t+m})` exactly, under uncertainty | `GeneralFormula.theoremW_finite` |
| Cochrane (7.17), pp. 225–226 | the row condition `\|A_t^{(t+j+1)}\| ≤ a_j`, `∑ β^{j+1}a_j ≤ ρ`; the dominating weights, which bound the weights and have `∑ β^mw_m ≤ 1/(1−ρ)` for `ρ < 1` | `GeneralFormula.RowBound`, `GeneralFormula.domA`, `GeneralFormula.domWeight`, `GeneralFormula.weight_domA`, `GeneralFormula.domWeight_nonneg`, `GeneralFormula.domWeight_succ`, `GeneralFormula.abs_weight_le`, `GeneralFormula.sum_domWeight_le`, `GeneralFormula.summable_domWeight` |
| Cochrane (7.17), p. 225 | the weighted present value `E_t∑ β^mW_t^{(m)}s_{t+m}` converges absolutely under the row condition and solves the system | `GeneralFormula.formulaTerm`, `GeneralFormula.formulaW`, `GeneralFormula.abs_formulaTerm_le`, `GeneralFormula.formulaW_summable`, `GeneralFormula.formulaW_solves` |
| Cochrane (7.17), p. 225 | Theorem W, infinite horizon: under the row condition every bounded solution is (7.17); for the price level, `B_{t−1}^{(t)}/P_t = E_t∑ β^mW_t^{(m)}s_{t+m}` | `GeneralFormula.theoremW`, `GeneralFormula.price_formula` |
| Cochrane p. 225 | special cases: no sales after date 0 gives `W_t^{(k)} = 0` for `k ≥ 1`, so (7.6); pure one-period roll-over gives `W ≡ 1`, so the standard present value | `GeneralFormula.special_noSales`, `GeneralFormula.special_onePeriod`, `GeneralFormula.fracSold_onePeriod` |

### When the present-value system determines the price level (E7.4, settled)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (7.16), p. 225 | the difference of two solutions solves the homogeneous system; given one bounded solution, bounded solutions are unique iff the homogeneous system has no nonzero bounded solution | `GeneralFormula.homogeneous_of_two`, `GeneralFormula.unique_iff_homogeneous` |
| Cochrane (7.16), p. 225 | sufficient condition (b): under the row condition with `ρ < 1` the homogeneous system has only the zero bounded solution, so price paths with bounded real maturing debt satisfying every flow condition coincide | `GeneralFormula.unique_of_row`, `GeneralFormula.price_unique_row` |
| Cochrane (7.16), p. 225 | sufficient condition (a): no buy-backs, nonnegative inherited debt and positive debt coming due; then the sale fractions are nonnegative and each column sums to at most one | `GeneralFormula.NoBuyback`, `GeneralFormula.NoBuyback.nonneg`, `GeneralFormula.NoBuyback.frac_nonneg`, `GeneralFormula.NoBuyback.col_le_one` |
| Cochrane (7.16), p. 225 | with nonnegative sale fractions, column sums at most one and `0 < β < 1`, the homogeneous system has only the zero bounded solution, by a column-sum lemma and `\|E_tf\| ≤ E_t\|f\|` | `GeneralFormula.col_lemma`, `GeneralFormula.abs_E_le_E_abs`, `GeneralFormula.unique_of_noBuyback` |
| Cochrane (7.5), p. 216 | with nonnegative debt and price levels, the present-value relation bounds `0 ≤ B_{t−1}^{(t)}/P_t ≤ M/(1−β)` | `GeneralFormula.bounded_of_presentValue` |
| Cochrane (7.15)–(7.16), pp. 225–226 | without buy-backs, two positive price paths satisfying every flow and every present-value relation coincide, under uncertainty | `GeneralFormula.price_unique_noBuyback` |
| Cochrane (7.16)–(7.17), p. 225 | the counterexample: `B_{t−1}^{(t)} = 1`, `B_{t−1}^{(t+1)} = 2/β`, nothing later; constant surplus; `x* = s/(3(1−β))`; the family `1/P_t = x* + ε(−1/2)^t` | `GeneralFormula.cxD`, `GeneralFormula.cxS`, `GeneralFormula.cxStar`, `GeneralFormula.cxX`, `GeneralFormula.cxD_self`, `GeneralFormula.cxD_succ`, `GeneralFormula.cxD_far` |
| Cochrane (7.16), p. 225 (E7.4) | every member satisfies every flow condition and every present-value relation, is positive for `\|ε\| < x*` and bounded; different `ε` give different paths | `GeneralFormula.cx_flow`, `GeneralFormula.cx_presentValue`, `GeneralFormula.cx_pos`, `GeneralFormula.cx_bounded`, `GeneralFormula.cx_ne` |
| Cochrane (7.17), p. 225 (E7.4) | the sale fractions are `1 − 2/β` and `2/β`; the weights obey `W^{(k+2)} = (1 − 2/β)W^{(k+1)} + (2/β)W^{(k)}`, so `W^{(k)} = (β + 2(−2/β)^k)/(β + 2)`, and (7.17) diverges | `GeneralFormula.cx_frac`, `GeneralFormula.cx_weight_rec`, `GeneralFormula.cx_weight`, `GeneralFormula.cx_formula_diverges` |
| Cochrane p. 225 (E7.4) | the counterexample buys back debt and violates the row condition (row sum at least `2 + β`) | `GeneralFormula.cx_buyback`, `GeneralFormula.cx_not_row` |

### The printed displays (7.15)–(7.16)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (7.15), p. 225 (E7.2) | in an illustration with one unit of debt due at each of dates 0 and 1 and surpluses `s_0 = s_1 = 1`, every flow condition and the present-value relation with `β^j` hold, but the printed (7.15) without `β^j` would require `2 = 1 + β` | `GeneralFormula.exD`, `GeneralFormula.exS`, `GeneralFormula.printed_715_fails` |
| Cochrane (7.16), p. 225 (E7.3) | the corrected matrix, with row `t` entry `β^{m−t}B_{t−1}^{(m)}` in column `m ≥ t`; applied to `(1/P_m)` it gives the real value of debt | `GeneralFormula.pvMatrix`, `GeneralFormula.pvMatrix_row` |

## §7.5 Constraints on policy, (7.18)–(7.21), pp. 226–229 (PolicyConstraints)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 227 | quotients of known variables are known, true for perfect foresight and every finite tree; `E_t(f/b) = E_t(f)/b` for known `b` (E7.7) | `PolicyConstraints.DivClosed`, `PolicyConstraints.perfectForesight_divClosed`, `PolicyConstraints.finiteTree_divClosed`, `PolicyConstraints.E_div_known` |
| Cochrane box and (7.18), pp. 226–227 | the standing hypotheses of Theorem P: positive surpluses, positive targets `e_j = E_0(1/P_j)` known at date 0, consistent with (7.18) (E7.7) | `PolicyConstraints.Targets` |
| Cochrane (7.19), p. 227 | the policy `B_0^{(j)} = E_0s_j/E_0(1/P_j)`, sold at date 0 and never traded again, and its price levels; the sales are positive and known; the policy is predetermined | `PolicyConstraints.bOne`, `PolicyConstraints.polOneD`, `PolicyConstraints.polOneX`, `PolicyConstraints.bOne_known`, `PolicyConstraints.bOne_pos`, `PolicyConstraints.polOne_predetermined` |
| Cochrane (7.9), (7.19), p. 227 | `E_t(1/P_{j+1}) = E_ts_{j+1}/B_0^{(j+1)}`; `B_0^{(j)}E_0(1/P_j) = E_0s_j` | `PolicyConstraints.polOne_E`, `PolicyConstraints.polOne_719` |
| Cochrane box p. 226; pp. 227–228 | Theorem P: the policy achieves every target with positive price levels and satisfies every flow and present-value relation | `PolicyConstraints.polOne_achieves`, `PolicyConstraints.polOne_pos`, `PolicyConstraints.polOne_flow`, `PolicyConstraints.polOne_presentValue` |
| Cochrane (7.20), p. 227 | the roll-over policy: buy back long-term debt and roll over `B_{j−1}^{(j)} = E_0PV_j/e_j`; the present value of bounded surpluses is known at its date and has positive date-0 expectation | `PolicyConstraints.cTwo`, `PolicyConstraints.polTwoD`, `PolicyConstraints.polTwoX`, `PolicyConstraints.pvSurplus_adapted`, `PolicyConstraints.E_pvSurplus_pos`, `PolicyConstraints.cTwo_pos_known`, `PolicyConstraints.polTwo_E` |
| Cochrane (7.20), p. 227 | the second policy achieves the same targets and satisfies every flow and present-value relation | `PolicyConstraints.polTwo_achieves`, `PolicyConstraints.polTwo_flow`, `PolicyConstraints.polTwo_presentValue` |
| Cochrane bullet p. 226; p. 227 | many debt policies support the same price-level path | `PolicyConstraints.policies_differ` |
| Cochrane (7.18), p. 227 | every equilibrium satisfies (7.18), in nominal form | `PolicyConstraints.presentValue_zero_nominal` |
| Cochrane p. 228 | with only one-period debt outstanding, `P_0` does not depend on future price levels | `PolicyConstraints.onePeriod_price_zero` |
| Cochrane p. 228 | with nonnegative positions, debt policy cannot raise some price levels without lowering others ("stepping on a rake"); with a negative position it can (E7.8) | `PolicyConstraints.qe_tradeoff`, `PolicyConstraints.qe_tradeoff_strict`, `PolicyConstraints.qe_negative_position` |
| Cochrane p. 228 | debt policy can offset a fiscal shock at date 0, but only by raising some future price level | `PolicyConstraints.offset_shock`, `PolicyConstraints.offset_shock_cost` |
| Cochrane (7.21), p. 228 | the end-of-period real value of debt is `E_0∑_{j≥1} β^js_j`, whatever the quantities sold, also in nominal form | `PolicyConstraints.end_of_period_value`, `PolicyConstraints.end_of_period_value_nominal` |

## §7.6 Quantitative easing and friends, (7.22)–(7.24), pp. 229–234 (QuantitativeEasing)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (7.22), p. 230 | the geometric steady state `∑ β^jω^jB/P = B/(P(1−βω)) = s/(1−β)` and its price level | `QuantitativeEasing.steady_state`, `QuantitativeEasing.steady_price` |
| Cochrane (7.23), p. 230 | with (7.22), the present-value relation with Treasury debt, QE bonds and reserves is equivalent to (7.23) | `QuantitativeEasing.QEPresentValue`, `QuantitativeEasing.Eq723`, `QuantitativeEasing.pv_iff_723` |
| Cochrane p. 230; Figure 7.5 | given the price path and the QE purchases, (7.23) holds for exactly one reserve path, in closed form; "All M" with no QE | `QuantitativeEasing.reserves_formula`, `QuantitativeEasing.reserves_unique`, `QuantitativeEasing.all_M` |
| Cochrane p. 230 | given the price path and the reserves, the QE purchases are unique | `QuantitativeEasing.qe_unique` |
| Cochrane p. 230 | solving `∑_k β^kc_{t+k} = R_t`: `c_t = R_t − βR_{t+1}` when the tail series converge; any solution has this form and needs `β^NR_{t+N} → 0`; no solution for `R_t = β^{−t}` | `QuantitativeEasing.solve_tail`, `QuantitativeEasing.solve_tail_necessary`, `QuantitativeEasing.solve_tail_counterexample` |
| Cochrane p. 230 | the residual the purchases must finance; the purchases `B̃_0^{(j)} = B(R_j − βR_{j+1})P_j/P` exist when its tails converge, as for a bounded residual; existence requires `β^NR_{t+N} → 0` and fails for some reserve path, for any price path | `QuantitativeEasing.qeResidual`, `QuantitativeEasing.qe_exists`, `QuantitativeEasing.qe_residual_summable`, `QuantitativeEasing.qe_exists_necessary`, `QuantitativeEasing.qe_counterexample` |
| Cochrane (7.24), p. 232 | the same relation with bond prices `Q_t^{(j)} = β^{j−t}P_t/P_j` | `QuantitativeEasing.pv_iff_724` |
| Cochrane §7.6.2, p. 232 | only the total nominal market value of debt matters: two policies with the same market value satisfy the present-value relation for the same price levels, under uncertainty | `QuantitativeEasing.Irrelevance.maturity_irrelevance` |
| Cochrane p. 233 | strong QE, `B_0^{(j)} = P_js_j`: scaling supply by `λ` scales `P_j` by `λ` and `Q_0^{(j)}` by `1/λ`, so a 1% cut raises the bond price by 1.01–1.02% | `QuantitativeEasing.strong_qe` |

## Shared tools

| Book | Claim | Lean |
| --- | --- | --- |
| Chapter 7 throughout | the expectation axioms, pull-out, perfect foresight and adapted processes; `E_t(E_tx) = E_tx`; a variable known at `s` is known at every later date; `E_t` commutes with a dominated series | `ExpectationSystem`, `ExpectationSystem.PullOut`, `ExpectationSystem.Adapted`, `ExpectationSystem.E_E_self`, `perfectForesight`, `perfectForesight_pullOut`, `ForwardSolution.E_of_known`, `ForwardSolution.E_tsum_dom` |
| §7.5 | finite event trees (used for `PolicyConstraints.finiteTree_divClosed`) | `ExpectationsFiniteTree.FiniteTree`, `ExpectationsFiniteTree.FiniteTree.toExpectationSystem`, `ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E`, `ExpectationsFiniteTree.finiteTree_pullOut` |
| shared core, not used by Chapter 7 | forward series, the forward solution and Schur–Cohn determinacy, carried for the later Cochrane projects | `ExpectationSystem.forwardSeries`, `ForwardSolution.existsUnique_bounded`, `SchurStable`, `schurStable_iff_roots` |
