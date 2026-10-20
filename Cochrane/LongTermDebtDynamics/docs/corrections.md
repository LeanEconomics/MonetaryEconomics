# Corrections to the source

This file lists places where a claim in Chapter 7 of Cochrane (2023), *The Fiscal Theory of the
Price Level*, or in the Online Appendix sections it uses (§A1.2.1 and §A1.14), is false,
imprecise, or relies on an unstated hypothesis, and where the Lean statement departs from the
printed one. In each case the Lean statement proves the stated version and cites the original.

Codes E7.1–E7.11 are the Chapter 7 items of the survey of Chapters 6–10
(`notes/survey_cochrane_ch6-10.md`). Each was confirmed or refuted by formalisation before being
recorded here, and an entry is revised if formalisation shows the finding itself to be wrong.
E7.4 was the survey's open question; it is now settled (first section). Two findings, on strong
QE (p. 233) and on the reverse engineering of QE purchases (p. 230), are not in the survey and
were found during formalisation. Several claims that the book asserts without proof turned out to
be correct; they are listed in the last section.

Out of scope are §7.7 (the U.S. maturity structure, pp. 234–236), the narrative of runs and
defaults in §7.2.2 (pp. 219–220), and the discussion of precommitment and of the empirical record
of QE in §§7.6.2–7.6.3 (pp. 232–234). Lean names are relative to the namespace
`Cochrane.LongTermDebtDynamics`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| (7.16)–(7.17), p. 225 (E7.4) | The present-value relations are linear equations `Bp = Rs`, "and hence" their solution is `p = B⁻¹Rs`; (7.17) is a formula for it. | The system need not determine the price level, and (7.17) can diverge. With `B_{t−1}^{(t)} = 1`, `B_{t−1}^{(t+1)} = 2/β`, a constant surplus `s > 0` and `0 < β < 1`, every path `1/P_t = x* + ε(−1/2)^t`, `x* = s/(3(1 − β))`, `\|ε\| < x*`, is positive and bounded and satisfies every flow and every present-value relation (`GeneralFormula.cx_flow`, `GeneralFormula.cx_presentValue`, `GeneralFormula.cx_pos`, `GeneralFormula.cx_bounded`, `GeneralFormula.cx_ne`). Its weights are `W^{(k)} = (β + 2(−2/β)^k)/(β + 2)` and (7.17) diverges (`GeneralFormula.cx_weight`, `GeneralFormula.cx_formula_diverges`). **Settled:** the price level is determined (a) when the government never buys back debt, with nonnegative inherited debt and positive debt coming due: two positive paths satisfying every flow and present-value relation coincide, under uncertainty (`GeneralFormula.price_unique_noBuyback`); or (b) under the row condition `\|A_t^{(t+j+1)}\| ≤ a_j`, `∑ β^{j+1}a_j ≤ ρ < 1`, among paths with bounded real maturing debt, and then (7.17) converges absolutely and is the price level (`GeneralFormula.price_unique_row`, `GeneralFormula.theoremW`, `GeneralFormula.price_formula`). In general, given one bounded solution, uniqueness holds iff the homogeneous system has no nonzero bounded solution (`GeneralFormula.unique_iff_homogeneous`). The counterexample buys back debt and violates the row condition (`GeneralFormula.cx_buyback`, `GeneralFormula.cx_not_row`). |
| (7.15), p. 225 (E7.2) | `∑_j E_t(1/P_{t+j})B_{t−1}^{(t+j)} = E_t∑_j β^js_{t+j}`. | The left side omits `β^j`; the relation is (7.5), `MaturityStructure.PresentValue`. With one unit of debt due at each of dates 0 and 1, surpluses `s_0 = s_1 = 1` and `1/P_t = 1`, every flow condition and the corrected relation hold, but the printed one would require `2 = 1 + β` (`GeneralFormula.printed_715_fails`). |
| (7.16), p. 225 (E7.3) | The matrix display lists row `t` as `B_t^{(t+1)}, B_t^{(t+2)}, …`, without discount factors, and row 1 as `B_1^{(2)}, B_1^{(3)}, B_1^{(3)}, …`. | Row `t` must start with `B_{t−1}^{(t)}` in column `t` (the printed row is one index too late), its entries carry `β^{m−t}`, and the repeated `B_1^{(3)}` should be `B_1^{(4)}`. The corrected matrix is `GeneralFormula.pvMatrix`; applied to `(1/P_m)` its row `t` is the real value of debt (`GeneralFormula.pvMatrix_row`). |
| p. 233 (found during formalisation) | Under strong QE, `B_0^{(j)} = P_js_j`, a 1% cut in bond supply gives a 1% lower future price level and "a one percentage point decrease in bond price". | The sign of the bond-price effect is wrong. With `P_0` fixed and `Q_0^{(j)} = β^jP_0/P_j`, scaling supply by `λ` scales `P_j` by `λ` and `Q_0^{(j)}` by `1/λ`, so a 1% cut (`λ = 0.99`) raises the bond price by between 1.01% and 1.02% (`QuantitativeEasing.strong_qe`). The price-level half of the sentence is correct. |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| §7.1, p. 214 (E7.6) | "If `T > k`, and forward guidance exceeds the longest outstanding maturity", `P_0` "does not decline at all". | `T ≥ k` suffices (`ForwardGuidance.priceLevel_fg_of_le`), and it is sharp: if a maturity `j` with `T < j ≤ k` is outstanding and all positions are nonnegative, guidance lowers `P_0` (`ForwardGuidance.priceLevel_fg_lt`). |
| §7.5, pp. 226–228 (E7.7) | "There is a debt policy … that achieves any price level path consistent with" (7.18), namely (7.19), `B_0^{(j)}E_0(1/P_j) = E_0s_j`. | Theorem P is proved with the hypotheses the policy needs: positive surpluses with positive date-0 expectations, positive targets `E_0(1/P_j)` known at date 0, consistency with (7.18) (`PolicyConstraints.Targets`), and quotients of known variables being known (`PolicyConstraints.DivClosed`, true for perfect foresight and every finite tree). Then (7.19) achieves the targets with positive price levels and satisfies every flow and present-value relation (`PolicyConstraints.polOne_achieves`, `PolicyConstraints.polOne_pos`, `PolicyConstraints.polOne_flow`, `PolicyConstraints.polOne_presentValue`); (7.20) does too (`PolicyConstraints.polTwo_achieves`). The converse, that every equilibrium satisfies (7.18), needs none of them (`PolicyConstraints.presentValue_zero_nominal`). |
| §7.5, p. 228 (E7.8) | "A QE policy that raises near-term price levels with no decline in future price levels is not possible." | True with nonnegative positions `B_{−1}^{(j)} ≥ 0` (`PolicyConstraints.qe_tradeoff`, `PolicyConstraints.qe_tradeoff_strict`), false without: with `B_{−1}^{(0)} = 1` and `B_{−1}^{(1)} = −1`, raising both `P_0` and `P_1` preserves (7.18) (`PolicyConstraints.qe_negative_position`). |
| §7.6.1, p. 230 (found during formalisation) | For a desired price-level path and a choice of one of `M` or `B̃`, (7.23) "gives us the other one". | True in the direction "given `B̃`, find `M`": the reserves exist, are unique and are explicit (`QuantitativeEasing.reserves_formula`, `QuantitativeEasing.reserves_unique`). In the direction "given `M`, find `B̃`" the purchases are unique when they exist (`QuantitativeEasing.qe_unique`), and they exist when the tail series of the residual `R_t` converge, for example when it is bounded (`QuantitativeEasing.qe_exists`, `QuantitativeEasing.qe_residual_summable`). Existence requires `β^NR_{t+N} → 0` (`QuantitativeEasing.qe_exists_necessary`) and fails, for any positive price path, for reserves that make `R_t = β^{−t}` (`QuantitativeEasing.qe_counterexample`). |
| (7.17), p. 225 | (7.17) holds for any debt policy. | It is an exact identity when all debt matures by a finite date (`GeneralFormula.theoremW_finite`). With an infinite horizon it is proved under the row condition (`GeneralFormula.theoremW`); without a condition it is false (E7.4, above). Each sale fraction `A_t^{(t+j+1)}` is assumed known at `t + j`, the date of the last sale before maturity (`GeneralFormula.weight_known`). |
| §7.3.2, p. 224 | A state-contingent sale can offset a surplus shock. | Proved at date 0 with the revenue headroom stated: if the revenue from a maturity with outstanding debt can still rise by the size of the shock, a larger sale raises exactly that revenue and leaves `P_0` unchanged, raising the future price level (`BondSales.offset_shock`). |

## Typos, labels and rounding

| Where | Book says | Finding |
| --- | --- | --- |
| p. 225 (E7.1) | "the sequence of present-value relations (7.14) or flow relations (7.15)" | The labels are swapped: (7.14) is the flow relation (`GeneralFormula.MaturingSystem`, `GeneralFormula.realFlow_iff_maturingSystem`) and (7.15) the present-value relation. |
| p. 226 (E7.5) | `W_{t,k}` in the recursion for the weights. | `W_{t,k}` means `W_t^{(k)}`. The recursion itself is correct (`GeneralFormula.weight`, `GeneralFormula.weight_first_step`). |
| p. 224 (E7.9) | The innovation form of (7.12). | It mixes the generic date `t` with date 0. Its content is stated at date 0 (`BondSales.offset_shock`); no theorem depends on the notation. |
| App. p. 592 (E7.10) | "The last two terms of (1.67) partially offset." | (1.67) is the case `B_0^{(2)} = B_{−1}^{(2)}` (`FutureSales.price_zero_no_sale_two`) and has no such pair; the offsetting terms are in (1.66) (`FutureSales.x0Fun`, `FutureSales.x0_closed`). The substantive claim is correct (last section). |
| App. p. 560 (E7.11) | A rise from 3% to 4% "occasions a 25% price level drop". | Exact only in continuous time, `r/i = 0.75` (`ForwardGuidance.cfgJump_zero`). For the discrete perpetuity (1.19), `P_0/P = (1+i)r/((1+r)i)` is between 0.757 and 0.758, a drop of about 24.3% (`ForwardGuidance.perpetuity_ratio_bounds`). |
| App. p. 560; Figure 7.1 | Drops of 3.5% (immediate rise) and 1.6% (forward guidance) with `ω = 0.8`. | The book does not state `r` and `i`. With `r = 2%` and `i = 3%` the drops are about 3.41% and 1.65%, proved to lie between 3.4% and 3.5% and between 1.6% and 1.7% (`ForwardGuidance.fgJump_calibration`). Recorded as a check, not an error. |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| Throughout | Conditional expectations pull out quantities known at the date | `ExpectationSystem.PullOut` as a hypothesis; true for perfect foresight (`perfectForesight_pullOut`) and every finite tree (`ExpectationsFiniteTree.finiteTree_pullOut`) |
| Throughout | Debt is predetermined: inherited debt known at date 0, debt chosen at `t` known at `t` | `MaturityStructure.Predetermined` |
| Throughout | Infinite sums converge, and `E_t` passes through them | `HasSum` hypotheses and `MaturityStructure.DebtDominated`; bounded surpluses and `0 ≤ β < 1` for the present value (`MaturityStructure.summable_surplusTerm`) |
| (7.1)–(7.2), p. 213 | The present-value relation follows from the flow conditions only with transversality | `MaturityStructure.flow_tvc_iff_presentValue`; transversality is automatic for a bounded real value of debt (`MaturityStructure.presentValue_of_bounded`) |
| (7.1), p. 213 | `P_t > 0` and `x_t = 1/P_t` | `P_t x_t = 1` and adaptedness of `P` in `MaturityStructure.nominalFlow_iff_realFlow` |
| (7.12), p. 222; (7.17), p. 225 | The book divides by `B_0^{(j)}` and by the debt coming due `B_{m−1}^{(m)}` | `B_0^{(j)} ≠ 0` in `BondSales.dilution_formula`; nonzero debt coming due in `GeneralFormula.realFlow_iff_maturingSystem` and `GeneralFormula.price_formula` |
| §7.1; App. pp. 559–561 | `−1 < r < i` (or `≤`), `0 ≤ ω < 1 + r`, `r + ϖ > 0`, `i + ϖ > 0` | Hypotheses of the `ForwardGuidance` theorems |
| §7.3.2, p. 223 | Nonnegative inherited positions and positive expected surpluses for "sales lower `P_0`" | Hypotheses of `BondSales.outstanding_sales_lower_price` |
| §7.4, p. 225 (E7.4) | A condition on the debt policy for uniqueness | No buy-backs (`GeneralFormula.NoBuyback`) with `0 < β < 1`, or the row condition (`GeneralFormula.RowBound`) with `ρ < 1` |
| §7.5, p. 227 (E7.7) | Positive surpluses and targets; quotients of known variables are known | `PolicyConstraints.Targets`, `PolicyConstraints.DivClosed` |
| §7.5, p. 228 (E7.8) | Nonnegative positions `B_{−1}^{(j)} ≥ 0` | Hypothesis of `PolicyConstraints.qe_tradeoff`, `PolicyConstraints.qe_tradeoff_strict`, `PolicyConstraints.offset_shock_cost` |
| §7.6.1, p. 230 | `0 ≤ βω < 1`, positive `B` and steady-state price level | Hypotheses of `QuantitativeEasing.steady_state` and `QuantitativeEasing.pv_iff_723` |

## Claims confirmed correct

| Where | Claim | Lean |
| --- | --- | --- |
| (3.2)–(3.3), p. 212; (7.1)–(7.2), p. 213 | The real flow condition and the present-value relation with long-term debt | `MaturityStructure.nominalFlow_iff_realFlow`, `MaturityStructure.nominalValue_eq`, `MaturityStructure.flow_tvc_iff_presentValue` |
| §7.1, pp. 213–215 | The bond-price display; guidance has less effect than an immediate rise and less with a longer horizon; no second jump; bond-price targets work through (7.3) | `ForwardGuidance.inv_pow_lt_fgPrice`, `ForwardGuidance.priceLevel_immediate_le`, `ForwardGuidance.priceLevel_mono`, `ForwardGuidance.fgPath_eq_of_le`, `ForwardGuidance.valuation_iff` |
| App. (1.15)–(1.20), pp. 559–561 | The geometric and continuous formulas, the discrete and continuous forward-guidance formulas and their comparative statics, the steady-state sales | `ForwardGuidance.fgSum_same`, `ForwardGuidance.fg_jump_immediate`, `ForwardGuidance.fg_jump_geometric`, `ForwardGuidance.cfgValue_same`, `ForwardGuidance.cfg_jump`, `ForwardGuidance.fgJump_abs_lt`, `ForwardGuidance.cfgJump_tendsto`, `ForwardGuidance.steady_sales` |
| (7.6), p. 217 | The buffer: with no sales, `B_{−1}^{(t)}/P_t = s_t`, and later fiscal news moves bond prices only | `MaturingDebt.price_eq_maturing`, `MaturingDebt.noSales_price_news`, `MaturingDebt.noSales_bond_news` |
| (7.7), p. 219 | The one-period flow condition, the backward induction, and fear of future surpluses raising today's price level | `MaturingDebt.oneperiod_flow_E`, `MaturingDebt.oneperiod_two_period`, `MaturingDebt.oneperiod_fear` |
| (7.9)–(7.13), pp. 221–222 | Real revenue independent of quantity, the dilution formula, independence of `P_0` from sales with no outstanding debt | `BondSales.real_revenue`, `BondSales.dilution_formula`, `BondSales.no_outstanding_price_indep` |
| Bullets pp. 222–223 | Sales lower bond prices and raise future price levels; finite sales under a bond-price target; unit elasticity; with outstanding debt, sales lower `P_0` | `BondSales.sales_lower_bondPrice`, `BondSales.sales_raise_future_price`, `BondSales.bondPrice_target_iff`, `BondSales.unit_elasticity`, `BondSales.outstanding_sales_lower_price` |
| App. (1.63)–(1.68), pp. 589–592 | The three-period formulas, symmetry for `P_2` and `Q_0^{(2)}`, the interaction-only effect, and the sign of the effect of expected sales on `P_0` | `FutureSales.price_zero`, `FutureSales.price_two_symm`, `FutureSales.no_time0_sales`, `FutureSales.x0_strictMono`, `FutureSales.x0_strictAnti`, `FutureSales.x0_const` |
| p. 226 | Cochrane's recursion for the weights equals the chain-sum form | `GeneralFormula.weight_first_step`, `GeneralFormula.weight_eq_chainSum` |
| p. 225 | The special cases: no sales gives (7.6), one-period roll-over gives the standard present value | `GeneralFormula.special_noSales`, `GeneralFormula.special_onePeriod` |
| Bullet p. 226; p. 227 | Many debt policies support the same price-level path | `PolicyConstraints.policies_differ` |
| (7.18), p. 227; p. 228 | Every equilibrium satisfies (7.18); with only one-period debt future price levels do not affect `P_0`; debt policy can offset a fiscal shock at the cost of future inflation | `PolicyConstraints.presentValue_zero_nominal`, `PolicyConstraints.onePeriod_price_zero`, `PolicyConstraints.offset_shock`, `PolicyConstraints.offset_shock_cost` |
| (7.21), p. 228 | The end-of-period value of debt does not depend on the quantities sold | `PolicyConstraints.end_of_period_value` |
| (7.22)–(7.24), pp. 230–232 | The steady state, (7.23), "All M", (7.24) | `QuantitativeEasing.steady_state`, `QuantitativeEasing.pv_iff_723`, `QuantitativeEasing.all_M`, `QuantitativeEasing.pv_iff_724` |
| §7.6.2, p. 232 | Only the total market value of debt matters | `QuantitativeEasing.Irrelevance.maturity_irrelevance` |
