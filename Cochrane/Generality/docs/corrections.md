# Corrections to the source

This file lists places where a claim in Chapter 3 of Cochrane (2023), *The Fiscal Theory of the
Price Level*, or in Online Appendix A1.2–A1.6 and A1.9.1, is false, imprecise, or relies on an
unstated hypothesis, and where the Lean statement departs from the printed one. In each case the
Lean statement proves the stated version and cites the original.

Codes E11–E24, E28, E29 and E31 are the Chapter 3 and appendix items of the survey of Chapters 1–3
(`notes/survey_cochrane_ch1-3.md`). Each was confirmed or refuted by formalisation before being
recorded here, and an entry is revised if formalisation shows the finding itself to be wrong: E15
was refined (the text's "3.5%" turns out to be the more accurate number), and the survey's planned
"(3.6) may explode on a finite tree" example was replaced by a theorem that it cannot. Five findings
are new: the misprint in (3.26), the jump relation of A1 p. 566, the knife edge of A1 p. 561, the
finite-tree result for (3.6) and the 1980s seigniorage arithmetic.
Several claims that the book asserts without proof turned out to be correct; they are listed in
the last section.

Out of scope are the discursive passages: the remark that price stickiness makes the effect of a
rate rise smaller (A1 p. 560), the qualitative discussion of a passive money supply (pp. 61–62),
and the historical interpretation around the seigniorage numbers (pp. 60–61). Lean names are
relative to the namespace `Cochrane.Generality`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| (3.26), p. 68 (new) | The nonlinear mark-to-market valuation equation has `E_t∑βʲs̃_{t+j}` on the right. | `s̃` is the scaled surplus-to-GDP ratio of p. 63, `ρ/(V/(Py))·s/y` (`LogLinearIdentities.stilde_eq`). The nonlinear equation is (3.3), with the real surplus `s_{t+j}` (`LongTermDebt.valuationLT_iff_const`). If (3.3) holds and `s̃ = κs` with a constant scale `κ`, the printed (3.26) holds iff `κ = 1` or the value of debt is zero (`Links.eq_3_26_printed_iff`). Confirmed against the printed page. |
| p. 63 (E11) | `ρ = e^{r−g}`, and "everyone is so used to `ρ < 1`". | The exact derivative of the log flow identity gives `ρ = e^{−(r−g)}`, as A1 (1.12) has it (`LogLinearIdentities.rho_eq`). Then `ρ < 1` iff `r > g`, iff the steady-state surplus is positive (`LogLinearIdentities.rho_lt_one_iff`). The printed value agrees only when `r = g` (`LogLinearIdentities.printed_rho_eq_iff`) and is below one only when `r < g` (`LogLinearIdentities.printed_rho_lt_one_iff`). |
| p. 53 (E28) | "We can derive (3.2) from (3.3) by considering its value at two adjacent dates." | False without the bond-pricing equation (3.1). Under perfect foresight with `β = 1/2`, `P ≡ 1`, `s ≡ 1`, `B_{t−1}^{(t)} = 0`, `B_{t−1}^{(t+1)} = 1` and the price `Q_t^{(t+1)} = 2`, (3.3) and the TVC hold at every date while (3.2) fails at every date (`LongTermDebt.valuationLT_not_imp_flow`). With (3.1) the equivalence holds (`LongTermDebt.valuationLT_iff`). |
| p. 57 (E13) | (3.10) and (3.11) are "equivalent expressions". | The terminal term of (3.10) is that of (3.11) plus the money term `E_t[Λ_{t+T}M_{t+T}/P_{t+T}]` (`Money.tvc_split`). The two are equivalent under the money transversality condition (`Money.pv_3_10_iff_3_11`), and given (3.11), (3.10) holds iff it does (`Money.pv_3_10_iff_money_tvc`). In a money bubble, perfect foresight with `Λ_t = βᵗ`, `P ≡ 1`, `1 + i = β⁻¹`, `B ≡ 0`, `M_{t−1} = β⁻ᵗ`, (3.11) holds at every date and (3.10) at none (`Money.money_bubble`). The same holds in continuous time for (3.53) and (3.54) (`ContinuousMoney.printing_interest_iff_money_tvc`, `ContinuousMoney.printing_without_interest_example`); `Links.e13_discrete_and_continuous` states both. |
| p. 59 (E14) | (3.16) holds "following (3.11)", with weights `βʲ`. | (3.16) follows from (3.10) at `i = 0` (`Money.zero_bound_valuation`) or from (3.12) with `i^m = i` (`Money.full_interest_valuation`). It does not follow from (3.11): with Friedman-rule deflation `P_t = Λ_t = βᵗ`, constant money `m ≠ 0`, no bonds and no surpluses, (3.11) holds and (3.16) fails at every date (`Money.zero_bound_not_from_3_11`). The weights `βʲ` need `Λ_t = βᵗ` (`Money.zero_bound_beta`). |
| pp. 78–79 (E20) | "In the case of short-term debt `ω = 0`, the left-hand side is zero." | With coupons `e^{−ωτ}`, `ω = 0` is the perpetuity, price `1/y` (`ContinuousLinear.perpetuity_price`), and there the left side of (3.51) is not zero: it equals `1/r` for `Δπ ≡ 1` (`ContinuousLinear.perpetuity_lhs_ne_zero`). Short-term debt is the limit `ω → ∞` (`ContinuousLinear.instantaneous_limit`, `ContinuousLong.tendsto_book_bondValue`), where the left side tends to `0` (`ContinuousLinear.short_limit`, `ContinuousLinear.short_limit_single`) and fiscal news equals discount-rate news (`ContinuousLinear.short_debt_limit_identity`). A1 p. 560 has it right ("`ϖ = ∞` is instantaneous debt"). In discrete time short-term debt is `ω = 0`; the two conventions meet through `ω = e^{−ϖ}` (`Links.omega_disc_endpoints`, `Links.short_debt_limits`, `Links.jumpRatio_tendsto_short`). |
| A1 p. 566 (E23) | "From (1.27), `V` grows more slowly than `W`, so the limit is zero." | (1.28) holds iff the transversality condition `V(T)/W(T) → 0` holds (`ContinuousLong.A15_valuation_iff`); the limit is an assumption, not a consequence of (1.27). With `r = 1`, `s ≡ 0`, `V = W = e^τ`, (1.27) holds and `V/W → 1` (`ContinuousLong.A15_counterexample`); every bubble path violates (1.28) (`ContinuousLong.bubble_not_valuation`). What is true is that `V/W` is nonincreasing when surpluses are nonnegative (`ContinuousLong.V_over_W_antitone`). |
| A1 p. 566 (new) | At jump points `dW/W = dP/P`. | With nominal debt predetermined, `V/W` does not jump and `W⁺/W⁻ = V⁺/V⁻`: it is `dW/W = dV/V` (`ContinuousLong.jump_V_over_W`). With short-term debt `W⁺/W⁻ = P⁻/P⁺`, so the jumps of `W` and `P` have opposite signs whenever `P` jumps (`ContinuousLong.jump_short_return_sign`). |
| A1 pp. 576–577 (E24) | `π_{t+1} = i_t + ΔE_{t+1}∑ρʲs_{t+1+j} = u_{i,t} + ε_{s,t+1}/(1 − ρη_s)`, and `B_{πs} = +1/(1 − ρη_s)`. | Minus in both: in every equilibrium with bounded debt `π_{t+1} = i_t − ΔE_{t+1}∑ρʲs_{t+1+j}` (`MSV.msv_infl_innov`), and with AR(1) surpluses `π_{t+1} = u_{i,t} − ε_{s,t+1}/(1 − ρη_s)` (`MSV.msv_solution`, `MSV.msv_solution_is_eqm`). The printed inflation is not that of any bounded-debt equilibrium once some surplus shock is nonzero (`MSV.msv_printed_not_eqm`), also on the coin-flip tree (`MSV.msv_printed_fails_coin`). The undetermined-coefficients guess works iff `B_{πs} = −1/(1 − ρη_s)` (`MSV.msv_coeffs_iff`, `MSV.msv_coeffs_printed_fails`). |

## Figure 3.1 and the 3.5% drop (E15), reconciled

A1 p. 560 says that with `ω = 0.8` the permanent rate rise of Figure 3.1 "leads to a 3.5% price
level drop", and that the linear formulas of §3.5 are used in the figure, which plots a drop of
4%. The survey recorded this as a disagreement between text and figure, with an exact value of
3.41%. Formalisation shows that all four numbers are correct statements about different
quantities, at the figure's rates `r = 2%`, `i = 3%`. `Links.e15_reconciled` proves the whole set
in one statement.

| Quantity | Value | Lean |
| --- | --- | --- |
| Exact proportional drop `1 − P_0/P`, from (1.16) | `40/1173 ∈ (3.41%, 3.42%)` | `LongTermDebt.omega_08_example` |
| Exact log drop `−log(P_0/P)` | in `(3.46%, 3.48%)`: the text's "3.5%" | `LogLinearIdentities.fig31_log` |
| Linear drop with the printed weight `ω`, `ω/(1 − ω)` | 4%: Figure 3.1 | `LogLinearIdentities.fig31_jump`, `LogLinearIdentities.fig31_value` |
| Linear drop with the exact first-order weight `ω̂ = ω/(1+i)`, `ω̂/(1 − ω̂)` | `80/23 ≈ 3.48%` | `LogLinearIdentities.fig31_linear_exact_coeff` |

The text's 3.5% is right as a log change, and Figure 3.1 plots log prices. The figure's 4% comes
not from linearising but from the weight. The exact first-order coefficient of the bond return is
`ω/(1+i)` (A1 (1.22); `LogLinearIdentities.bondReturn_hasFDerivAt`,
`LogLinearIdentities.bondReturn_steady`), and the weight `ω` of (1.24) and (3.21)–(3.28) is a
second approximation. The two agree only if `ω = 0` or `i = 0`
(`LogLinearIdentities.omega_hat_eq_iff`). With the exact weight the linear drop (3.48%) matches the
exact log drop (3.46–3.48%). So text and figure still disagree, and the text is the more accurate.
The linear identities are therefore stated with a free weight `ω̂` (`LogLinearIdentities.BondRet`),
which is `ω/(1+i)` for the exact derivative and `ω` for the book's (1.24).

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 56 (new) | "It is possible that the present value is well defined using marginal utility or the discount factor as in (3.5), but the present value and terminal condition using ex-post returns (3.6) explode." | The claim depends on the probability model. On every finite event tree, with every state of positive probability, the flow and the TVC at every date (hence (3.5)) force (3.6) to converge absolutely in every state, with the terminal term tending to zero and `B_{t−1}/P_t` equal to the ex-post present value (`StochasticDiscount.finiteTree_expost_pv`). The proof uses that information on a finite tree stops being refined after some date, after which `R⁻¹_{t+1} = m_t` exactly (`StochasticDiscount.finiteTree_info_stable`, `StochasticDiscount.finiteTree_eventually_known`). The explosion does happen on the infinite state space `Option ℕ` (a fiscal switch at date `n`, or never): (3.5), the flow and the TVC hold everywhere, but along the never-switch path the partial sums of (3.6) tend to `−∞` and its terminal term to `+∞` (`StochasticDiscount.expost_may_diverge`). Agents assign that path probability zero at every date. |
| A1 p. 561 (new) | "A geometric maturity structure needs tending, except in a knife edge case that surpluses are also nonstochastic and geometric." | The exact condition is on nominal surpluses. If the geometric flow holds at every date and the value carried forward per unit, `∑ωʲQ_t^{(t+j+1)}`, is never zero, the government never trades iff `P_ts_t = ωᵗb_0` at every date (`LongTermDebt.geom_knife_edge`). Nominal surpluses are then known at date 0 (`LongTermDebt.knife_edge_surplus_known`). Otherwise some issuance `ω^{j−1}(b_{t+1} − ωb_t)` is nonzero (`LongTermDebt.geom_needs_tending`, `LongTermDebt.geom_issuance`). |
| (3.44)–(3.45), p. 77 | Innovations of diffusions and jumps, `Δ_t`. | Formalised without stochastic calculus: an innovation is the difference between two perfect-foresight equilibria of the linearised model from the news date on (`ContinuousLinear.Eqm.LinearEqm`). Two linking steps are proved: with real face value predetermined, the jump in the value of debt equals the jump in the bond price (`ContinuousLinear.news_value_eq_bond`), and that jump is the limit of the holding return across the news date (`ContinuousLinear.news_return_tendsto`). (3.46), (3.50) and (3.51) then hold as identities between the two paths (`ContinuousLinear.news_value`, `ContinuousLinear.news_bond`, `ContinuousLinear.news_weighted_inflation`). |
| A1 p. 577 | "Determinacy comes here from the assumption that `v_t` is a time-invariant function of the state variables." | Made precise: an equilibrium has bounded debt iff its debt is the forward solution `v*` (`MSV.msv_determinacy`). Debt follows the recursion with the explosive root `ρ⁻¹` (`MSV.msv_debt_rec`), which is not bounded-input-bounded-state (`MSV.msv_debt_not_bibo`), and a deviation from `v*` explodes in expectation like `\|ρ\|⁻ᵏ` (`MSV.msv_deviation_explodes`). |
| p. 64 | "If we use `ρ = 1`, then `E_tv_{t+T} → E(v)`, and equation (3.19) continues to hold describing deviations from this mean." | Proved with the convergence as a hypothesis: if `E_tv_{t+T} → v̄` and the series converges, `v_t − v̄ = ∑E_t(s̃ + g − r)_{t+1+j}` (`LogLinearIdentities.pv_rho_one`). |
| p. 77; (3.49), p. 78 | The bond-price forward solution. | Proved iff the transversality condition (`ContinuousLinear.bond_price_forward_iff`), and as the unique bounded solution (`ContinuousLinear.bond_price_forward_bounded`, `ContinuousLinear.bondForward_spec`). |
| (3.31), p. 73; A1.4 | The valuation equation, and "work either up or down" between it and the flow. | Each direction holds given the transversality condition: valuation iff TVC along the flow (`ContinuousShort.valuation_iff_tvc`), every solution of the flow is the present value plus a bubble `c/D(t,·)` that violates the TVC unless `c = 0` (`ContinuousShort.flow_general_solution`, `ContinuousShort.tvc_bubble_iff`), and the present value at every date iff flow + TVC (`ContinuousShort.eqOn_pv_iff_flowOn_tvc`). |

## Typos, cross-references and rounding

| Where | Book says | Finding |
| --- | --- | --- |
| (3.6), p. 56 (E12) | The terminal term has the product `∏_{k=1}^{j}R⁻¹_{t+k}`. | The upper index is `T` (`StochasticDiscount.expost_iterate`). |
| A1 box, pp. 561, 564 (E16) | `q̃_t = −∑_{j≥1}ωʲr̃^n_{t+j}`. | The exponent is `j − 1`: `q_t = −∑_{j≥1}ω̂^{j−1}r^n_{t+j}` (`LogLinearIdentities.bondPrice_forward`). The printed formula holds for a bounded solution only where `q_t = 0` (`LogLinearIdentities.printed_bondPrice_iff`); with `ω̂ = 1/2`, `q ≡ 1` it fails (`LogLinearIdentities.printed_bondPrice_counterexample`). The final (1.25)/(3.21) is correct (`LogLinearIdentities.bondReturn_innov`). |
| p. 70 (E17) | "Equation (3.5.3) opens quite a door." | A section number used as an equation number; the equation meant is (3.28) (`LogLinearIdentities.monetary_disinflation`). Not a formal claim. |
| p. 77 (E18) | `ds_t = −ηs_t + σdε_t`; `E_ts_{t+τ} = e^{−ητ}s_t + s̄`. | `ds = −ηs dt + σdε` and `E_ts_{t+τ} = e^{−ητ}s_t`: every solution of `s' = −ηs` is `e^{−ητ}s_0` (`ContinuousLinear.ar1_hasDerivAt`, `ContinuousLinear.ar1_unique`). For `η ≠ 0`, `s̄ ≠ 0` the printed path never satisfies the law of motion (`ContinuousLinear.ar1_printed_not_solution`). |
| p. 78 (E19) | `(dR^n_t − r dt) = dq_t − (r + ω)(1 − q_t)dt`. | The sign is `+`: (3.48) is equivalent to `R^n − r = q' + (r + ω)(1 − q)` (`ContinuousLinear.bond_linear_corrected_line`). The printed line with (3.48) forces `q = 1` (`ContinuousLinear.printed_line_forces_steady`); `q = 2`, `R^n = r`, `q' = r + ω` satisfies (3.48) but not the printed line (`ContinuousLinear.printed_line_counterexample`). (3.48) itself is correct. |
| (3.41), p. 76 (E21) | `∫e^{−rτ}(dR_t − r dt)`. | The integrand is dated `t + τ` (`ContinuousLinear.value_identity_341`, `ContinuousLinear.linear_value_split`). |
| p. 79; A1 p. 568 (E21) | `∫(W_t/W_τ)(s_τ + (i_t − i^m_t)M_τ/P_τ)dτ`. | The rate is dated `τ` (`ContinuousMoney.money_interest_W_iff`). With `P ≡ 1`, `i ≡ 1`, `W_τ = e^τ`, `B ≡ 0`, `M ≡ 1`, `i^m_τ = e^{−τ}` and `s = i^m`, the true value is `1` and the printed integral is `1/2` (`ContinuousMoney.printed_index_counterexample`). |
| pp. 77–78 (E22) | "Its coupons at time `t + Δ + τ` are now `e^{−ω(t+Δ+τ)}`." | The relative schedule `e^{−ω(Δ+τ)}` is meant; the conclusion is unaffected (`ContinuousLinear.holding_return_tendsto`). |
| Notation p. xxvi (E31) | Continuous maturity `B_t^{(t+j)} = e^{−ωt}B_t`. | `e^{−ωj}B_t` (`ContinuousLong.debtDensity`). The book's density `ϖe^{−ϖj}B_t` differs from the bundle convention used here by the constant `ϖ`, which leaves price ratios unchanged (`ContinuousLong.tendsto_book_bondValue`). |
| A1 p. 560 | "A rise in interest rates from `r = 3%` to `i = 4%` occasions a 25% price level drop." | Exact in continuous time, `r/i = 3/4` (`ContinuousLong.price_jump_perpetuity_numeric`). The discrete perpetuity formula (1.19) gives `P_0/P = 78/103`, a drop of 24.27% (`LongTermDebt.perpetuity_example`). |
| p. 60 (new) | Early-1980s deficits of "$200 billion or 5% of GDP", with GDP "about $3 trillion". | `200/3000 = 6.7%`. The other numbers are consistent (`Money.seigniorage_1980s`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| §3.1, §3.3, A1 (E29) | Summing over maturities and dates inside `E_t` | A finite maximum maturity (`LongTermDebt.MaxMaturity`) or the geometric structure with genuine infinite sums (`LongTermDebt.geomDebt`); conditional monotone convergence (`LongTermDebt.MonotoneConvergence`), true for perfect foresight and every finite tree (`LongTermDebt.perfectForesight_monotoneConvergence`, `LongTermDebt.finiteTree_monotoneConvergence`) |
| §§3.1–3.4 (E29) | Signed surpluses have a well-defined present value | Absolute summability `LongTermDebt.SurplusSummable`, used through the positive and negative parts (`LongTermDebt.E_sdf_mul_split`) |
| Throughout (discrete time) | Conditional expectations pull out quantities known at `t` | `ExpectationSystem.PullOut` as a hypothesis; true for perfect foresight and every finite tree (`perfectForesight_pullOut`, `ExpectationsFiniteTree.finiteTree_pullOut`) |
| §§3.1, 3.3 | The real value of debt `B_{t−1}/P_t` is known at `t` | A hypothesis of `LongTermDebt.flow_tvc_iff_pv` and `StochasticDiscount.valuation_sdf_iff`. The abstract axioms do not derive it from `B` and `P` being known separately |
| §§3.3–3.4 | `Λ > 0`, `P > 0`, `Λ/P` and `Λ⁻¹` known at `t`, debt and money predetermined, `1 + i > 0` | `Money.Standing` |
| p. 59 (E14) | `βʲ` in (3.16) | `Λ_t = βᵗ` (`Money.zero_bound_beta`) |
| §3.5 | Stationarity of the linear economy | Bounded processes and `0 < ρ < 1` (`LogLinearIdentities.LinearEconomy`); bounded bond prices and `\|ω̂\| < 1` (`LogLinearIdentities.BondPriceOK`). The general unbounded case is `LogLinearIdentities.pv_319_iff` |
| §3.6 | Regularity of continuous-time paths | Rates and surpluses continuous on `[t, ∞)`; values continuous on `[t, ∞)` and differentiable on `(t, ∞)`, so the price level may jump at `t` (`ContinuousShort.FlowOn`); absolute integrability of discounted surpluses (`ContinuousShort.PVIntegrable`); the TVC as an explicit limit (`ContinuousShort.TVC`) |
| §3.6.2, (3.34)–(3.39), pp. 74–75; A1.5 | Differentiating `∫_0^∞Q_t^{(t+j)}B_t^{(t+j)}dj` under the integral sign and producing the `−B_t^{(t)}dt` term | `ContinuousLong.MaturityRegularAt`: joint differentiability of `Q` and `B` in date and maturity; integrability of the value, of new issues and of the maturity derivative; measurability of the capital gain; decay of `Q·B` at long maturities; an integrable bound on the date derivative, uniform near the date. Plus the par condition `Q_t^{(t)} = 1`. Under these the book's (3.38)–(3.39) and valuation iff TVC hold as stated (`ContinuousLong.hasDerivAt_value_general`, `ContinuousLong.valuation_general_iff`) |
| A1 p. 561 | The knife edge | A nonzero value carried forward per unit, `∑ωʲQ_t^{(t+j+1)} ≠ 0` (`LongTermDebt.geom_knife_edge`) |
| p. 77; (3.47)–(3.49) | Convergence of the AR(1) and bond-price integrals | `r + η > 0` (`ContinuousLinear.ar1_pv`); `r + ω > 0` (`ContinuousLinear.bond_price_forward_bounded`) |
| A1 pp. 576–577 (E24) | The coefficient solution | `ρ ≠ 0`, `ρη_i ≠ 1`, `ρη_s ≠ 1` (`MSV.msv_coeffs_iff`); bounded disturbances and `\|ρ\| < 1` for existence (`MSV.msv_exists`) |

## Claims confirmed correct

| Where | Claim | Lean |
| --- | --- | --- |
| (3.1)–(3.3), p. 53 | Given (3.1), flow + TVC iff (3.3), for finite and geometric maturities | `LongTermDebt.valuationLT_iff`, `LongTermDebt.valuationLT_iff_const`, `LongTermDebt.valuationGeom_iff` |
| A1 (1.14)–(1.16), (1.19), pp. 559–560 | The valuation, steady state, jump and perpetuity formulas | `LongTermDebt.valuation_1_14`, `LongTermDebt.steady_state_1_15`, `LongTermDebt.price_jump_perm`, `LongTermDebt.price_jump_perpetuity` |
| A1 pp. 560–561 | Forward guidance: the closed form, "forward guidance works", the limit `T → ∞`, smaller jumps for longer `T` and shorter maturity; transitory rises matter less | `LongTermDebt.price_jump_fg`, `LongTermDebt.fg_drop_pos`, `LongTermDebt.fg_tendsto_zero`, `LongTermDebt.fg_drop_strictAnti_T`, `LongTermDebt.fg_drop_strictMonoOn_omega`, `LongTermDebt.meanReverting_le_perm`, `ContinuousLong.price_jump_fg` |
| A1 (1.17)–(1.18), (1.20), p. 560 | The continuous jump `(r + ω)/(i + ω)` and the perpetuity `r/i` | `ContinuousLong.price_jump_permanent`, `ContinuousLong.post_jump_equilibrium`, `ContinuousLong.price_jump_perpetuity` |
| (3.4), pp. 54–55 | The ratio forms of the valuation equation | `Ratios.valuation_gdp_iff`, `Ratios.valuation_per_dollar_iff`, `Ratios.valuation_per_dollar_gdp_iff` |
| (3.5), (3.7)–(3.8), pp. 55–57 | Valuation with a stochastic discount factor; the portfolio-return flow | `StochasticDiscount.valuation_sdf_iff`, `StochasticDiscount.flowLT_iff_3_8` |
| (3.12), footnote 2; (3.13)–(3.15), p. 59 | The interest-on-money weight; the ex-post forms | `Money.weight_identity`, `Money.pv_3_12`, `Money.flow_3_14`, `Money.pv_3_15_iff` |
| pp. 60–61 | 2019 seigniorage arithmetic; the offset argument | `Money.seigniorage_2019`, `Money.seigniorage_offset_valuation` |
| A1 (1.11), (1.23), p. 558, 563 | The constant of the linearisation; the geometric bond price and its limits | `LogLinearIdentities.constant_1_11`, `LogLinearIdentities.geomQ`, `LogLinearIdentities.geomQ_short`, `LogLinearIdentities.geomQ_perpetuity` |
| (3.20)–(3.25), (3.27)–(3.28), pp. 65–69 | The innovation identities and special cases | `LogLinearIdentities.innov_identity_3_20`, `LogLinearIdentities.bondReturn_innov`, `LogLinearIdentities.weighted_inflation_identity`, `LogLinearIdentities.special_constant_long`, `LogLinearIdentities.monetary_disinflation` |
| pp. 66–71 | Four times the surplus at 100% debt; `1/(1 − 0.7) = 3.3`; zero current inflation possible; the jump `−4` at `ω = 0.8`; announcement and expected rises; the weights differ only in the first terms | `LogLinearIdentities.scaling_ratio`, `LogLinearIdentities.perm_inflation_equiv`, `LogLinearIdentities.zero_current_inflation_possible`, `LogLinearIdentities.fig31_value`, `LogLinearIdentities.announcement_jump`, `LogLinearIdentities.expected_rise_no_jump`, `LogLinearIdentities.weights_close` |
| (3.29)–(3.33), A1.4, pp. 73–74, 564–565 | The continuous short-debt valuation, the price level and the `Λ` and `W` chains | `ContinuousShort.valuation_iff_tvc`, `ContinuousShort.price_level_determined`, `ContinuousShort.nominal_pv_iff_flow`, `ContinuousShort.W_closed_form` |
| (3.34)–(3.39), p. 75 | Long-term debt in continuous time, geometric and general (under the stated regularity) | `ContinuousLong.flow_LT_geometric`, `ContinuousLong.valuation_LT_iff`, `ContinuousLong.hasDerivAt_value_general` |
| (3.47)–(3.51), pp. 77–78 | The bond return, (3.48) as printed, the forward solution (3.49) and its sign, the news identities | `ContinuousLinear.return_eq_yield`, `ContinuousLinear.bond_linear_iff`, `ContinuousLinear.bond_price_forward_iff`, `ContinuousLinear.news_bond`, `ContinuousLinear.news_weighted_inflation` |
| (3.52)–(3.55), A1.5–A1.6, pp. 79–80, 565–568 | The money valuations in continuous time (up to E13 and E21), the stock analogue, `ΛV = ∫Λs` | `ContinuousMoney.money_printing_iff`, `ContinuousMoney.money_interest_iff`, `ContinuousMoney.money_mixed_iff`, `ContinuousLong.stock_price_valuation`, `ContinuousLong.Lambda_valuation` |
| A1 p. 576 | Existence and uniqueness of the bounded-debt equilibrium; `v_t = η_su_{s,t}/(1 − ρη_s)` | `MSV.msv_exists`, `MSV.msv_unique`, `MSV.msv_solution` |
