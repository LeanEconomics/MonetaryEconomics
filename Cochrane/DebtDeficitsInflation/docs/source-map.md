# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, "Debt, deficits, discount
rates and inflation" (pp. 81–116), with Online Appendix A2, "How not to test fiscal theory"
(pp. 593–611), and the derivations of the linearised identities in Online Appendix A1 §§1.2–1.3
(pp. 556–564). Each formal claim is listed with its Lean name, relative to the namespace
`Cochrane.DebtDeficitsInflation`. Page numbers are book pages; "A1" and "A2" mark Online Appendix
equation numbers and pages. The book has no labelled propositions, so rows are keyed by equation
number and page.

Rows follow the book: first the linearised identities of §3.5 that the chapter builds on and
their derivation in A1, then §§4.1–4.4, then A2 §§2.1–2.4, then the link theorems and the shared
tools. Each heading names the modules that formalise the section. Every statement holds for an
arbitrary `ExpectationSystem`, so under perfect foresight and under genuine uncertainty, except
the Hilbert-space Wold statements, which live in a real inner-product space of second moments,
and the finite measure-theoretic instance of conditioning down. The measure-theoretic modules
state their results on a genuine probability space with Mathlib conditional expectations, almost
everywhere: conditioning down on general nested filtrations (`ConditioningDownMeasure`), the
invertibility, Wold and Granger statements in an arbitrary Hilbert space (`InvertibilityMeasure`)
and in `L²` of an i.i.d. economy that is not finitely supported (`InvertibilityMeasureL2`), and
the Wold decomposition theorem itself in an arbitrary real Hilbert space and in that `L²` (`Wold`),
conditioning down with integrable processes and at `|ρ| = 1` (`TidyR6ConditioningDownL1`), and
Wold and Granger causality with conditional expectations given the σ-algebra of the past
(`TidyR6CondExpForecast`, `TidyR6GaussianForecast`, `TidyR6GaussianMA`), on
the copied measure core (`ExpectationsMeasure`, `ExpectationsMeasureIID`). `Δ_{t+1}` is the innovation operator
`E_{t+1} − E_t` (`Innovations.innov`), the book's `ΔE_{t+1}`. The data, the estimates, Tables 4.1
and 4.2, Figures 4.1–4.7 and the A2 Figures 2.1–2.2 are out of scope and have no rows; see the
README. The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`,
`ForwardSolution`) is cited where a row uses it.

## §3.5 The linearised identities, (3.17)–(3.25), pp. 63–68, as used in Chapter 4 (LinearizedIdentities)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (3.19), p. 64 | "assuming that the sums converge": ordinary convergence of a series (partial sums tend to a limit, no absolute summability needed), and its calculus | `LinearizedIdentities.SeriesTo`, `LinearizedIdentities.seriesTo_of_hasSum`, `LinearizedIdentities.seriesTo_iff_hasSum`, `LinearizedIdentities.SeriesTo.unique`, `LinearizedIdentities.SeriesTo.congr`, `LinearizedIdentities.SeriesTo.add`, `LinearizedIdentities.SeriesTo.sub`, `LinearizedIdentities.SeriesTo.const_mul`, `LinearizedIdentities.seriesTo_zero` |
| Cochrane (3.20), p. 65 | sums from `j = 1`: dropping the first term | `LinearizedIdentities.seriesTo_succ_iff` |
| Cochrane (3.17), p. 63 | the valuation recursion `x_t = ρx_{t+1} + f_{t+1}` (flow, Campbell–Shiller and bond-price identities all have this form) | `LinearizedIdentities.Recursion` |
| Cochrane (3.18), p. 63 | forward iteration ex post, and "holds ex post, so it holds ex ante": any linear map (`E_m`, `Δ_{t+1}`) of the iteration | `LinearizedIdentities.rec_finite`, `LinearizedIdentities.rec_map_finite` |
| Cochrane (3.19), p. 64 | under the terminal condition the linear image of the iteration converges | `LinearizedIdentities.rec_seriesTo_map` |
| Cochrane (3.19), p. 64 | "debt-to-GDP grows no faster than `ρ⁻ᵗ`": bounded processes satisfy the terminal conditions for `\|ρ\| < 1`, in levels, expectations and innovations | `LinearizedIdentities.tvc_of_bound`, `LinearizedIdentities.tvc_E_of_bounded`, `LinearizedIdentities.tvc_innov_of_bounded` |
| Cochrane A2 §2.3, p. 606 | "imposing convergence of the last term": an absolutely summable moving average satisfies the innovation terminal condition for every `\|ρ\| ≤ 1`, including `ρ = 1` | `LinearizedIdentities.tvc_innov_of_MAVec` |
| Cochrane (3.17), p. 63 | the linearised flow identity `ρv_{t+1} = v_t + r_{t+1} − g_{t+1} − s̃_{t+1}` is the recursion with payoff `s̃ + g − r` | `LinearizedIdentities.Flow`, `LinearizedIdentities.flow_iff_recursion` |
| Cochrane p. 66; §4.1, p. 86 | "I infer the surplus from the linearized flow identity (3.17), so that linearized identities hold exactly"; the inferred surplus is the only one consistent with the identity | `LinearizedIdentities.sOfFlow`, `LinearizedIdentities.flow_sOfFlow`, `LinearizedIdentities.eq_sOfFlow` |
| Cochrane (3.18), p. 63 | the ex-post present-value identity with terminal term | `LinearizedIdentities.pv_finite` |
| Cochrane (3.19), p. 64 | `v_t = E_t∑ρʲ(s̃ + g − r)_{t+1+j}` under the terminal condition: combined form, split form (the discount-rate sum converges when the other two do), `tsum` form, and the literal expectation of the infinite sum for bounded processes | `LinearizedIdentities.pv_expected_combined`, `LinearizedIdentities.pv_expected`, `LinearizedIdentities.pv_expected_tsum`, `LinearizedIdentities.pv_expected_bounded` |
| Cochrane (3.20), p. 65 | the unexpected-inflation identity `Δπ_{t+1} − Δrⁿ_{t+1} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}ρʲΔr_{t+1+j}` | `LinearizedIdentities.unexpected_inflation_identity`, `LinearizedIdentities.unexpected_inflation_identity_tsum` |
| Cochrane (3.21), p. 65; A1 §1.3 | the geometric-maturity return `rⁿ_{t+1} = ωq_{t+1} − q_t` and the bond-return identity `Δrⁿ_{t+1} = −∑_{j≥1}ωʲΔrⁿ_{t+1+j} = −∑_{j≥1}ωʲΔ(r + π)_{t+1+j}` | `LinearizedIdentities.BondReturn`, `LinearizedIdentities.bond_return_identity`, `LinearizedIdentities.bond_return_identity_real` |
| Cochrane p. 65 | with one-period debt (`ω = 0`) the nominal return has no innovation | `LinearizedIdentities.one_period_innov_rn` |
| Cochrane (3.22), p. 65 | the weighted unexpected-inflation identity | `LinearizedIdentities.weighted_inflation_identity` |
| Cochrane p. 66 | constant expected returns, and then no news about future returns | `LinearizedIdentities.ConstExpReturn`, `LinearizedIdentities.innov_future_return_zero` |
| Cochrane (3.23)–(3.25), pp. 67–68 | the identities under constant expected returns and no growth | `LinearizedIdentities.weighted_inflation_identity_const`, `LinearizedIdentities.inflation_identity_const`, `LinearizedIdentities.bond_return_identity_const` |
| Cochrane pp. 66–67 | one-period debt: `Δπ_{t+1} = −∑ρʲΔs̃_{t+1+j}` with constant returns, and with time-varying returns | `LinearizedIdentities.inflation_identity_one_period_const`, `LinearizedIdentities.inflation_identity_one_period` |

## Online Appendix A1 §§1.2–1.3, the linearisations as exact derivatives, pp. 556–564 (LinearizationDerivation)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane A1 (1.6)–(1.7), p. 557 | the exact flow identity in ratios to GDP | `LinearizationDerivation.flow_ratio` |
| Cochrane A1 (1.9), p. 558 | the log flow identity `v_t + rⁿ_{t+1} − π_{t+1} − g_{t+1} = log(sy_{t+1} + e^{v_{t+1}})` and its right-hand side as a function | `LinearizationDerivation.log_flow`, `LinearizationDerivation.flowLog` |
| Cochrane A1 (1.12), p. 558 | the steady state: `ρ = e^v/(e^v + sy)`, `r − g = log((e^v + sy)/e^v)`, the log identity at the steady state, `ρ = e^{−(r−g)}`; `ρ > 0`, and `ρ < 1` iff the steady-state surplus is positive | `LinearizationDerivation.rhoLin`, `LinearizationDerivation.ssRate`, `LinearizationDerivation.steady_state_flow`, `LinearizationDerivation.rhoLin_eq_exp`, `LinearizationDerivation.rhoLin_pos_lt_one_iff` |
| Cochrane A1 (1.9)–(1.11), p. 558 | the linearisation is the exact Fréchet derivative `ρ dv + (ρ/e^v) dsy`; the constant `r − g + (1 − ρ)(v − 1)` | `LinearizationDerivation.flowDeriv`, `LinearizationDerivation.flowDeriv_apply`, `LinearizationDerivation.flowLog_hasFDerivAt`, `LinearizationDerivation.flow_constant` |
| Cochrane A1 (1.13), p. 558 = (3.17), p. 63 | the first-order identity in deviations is exactly `LinearizedIdentities.Flow`, with `s̃ = ρ sy/e^v` | `LinearizationDerivation.flow_iff_first_order` |
| Cochrane A1 (1.23), p. 563 | the steady-state price `Q = ∑_{j≥1}ω^{j−1}/(1+i)^j = 1/(1 + i − ω)` | `LinearizationDerivation.bondQ`, `LinearizationDerivation.bondQ_hasSum` |
| Cochrane A1 (1.21)–(1.22), p. 563 | the steady-state return `(1 + ωQ)/Q = 1 + i`; the log return `log(1 + ωe^{q'}) − q`, equal to `log(1 + i)` at the steady state | `LinearizationDerivation.bond_steady_return`, `LinearizationDerivation.bondLog`, `LinearizationDerivation.bond_steady_log` |
| Cochrane A1 (1.22), p. 563 | the exact derivative `(ω/(1+i)) dq' − dq` | `LinearizationDerivation.bondDeriv`, `LinearizationDerivation.bondDeriv_apply`, `LinearizationDerivation.bondLog_hasFDerivAt` |
| Cochrane A1 (1.22), (1.24), p. 563 = (3.21), p. 65 | the first-order bond-return identity is exactly `LinearizedIdentities.BondReturn` with weight `ω/(1+i)` | `LinearizationDerivation.bondReturn_iff_first_order` |
| Cochrane A1 (1.24), p. 563 (E23) | the printed weight `ω` differs from the exact `ω/(1+i)` whenever `ω ≠ 0` and `i ≠ 0` | `LinearizationDerivation.approx_1_24_differs` |
| Cochrane A1 p. 564 (E22) | `q_t = −∑_{j≥1}ω^{j−1}rⁿ_{t+j}`, not the printed `−∑_{j≥1}ωʲrⁿ_{t+j}`; counterexample | `LinearizationDerivation.bond_price_series`, `LinearizationDerivation.printed_bond_price_counterexample` |

## §4.2 opening: innovations and moving averages, (4.1)–(4.4), pp. 86–88 (Innovations)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (4.2), p. 87 | the innovation operator `Δ_{t+1} = E_{t+1} − E_t` is linear; `E_tΔ_{t+1}x = 0`; `Δ_{t+1}x` is known at `t + 1`, equals `x − E_tx` when `x` is, and vanishes on constants | `Innovations.innov`, `Innovations.innov_apply`, `Innovations.innov_mean_zero`, `Innovations.innov_known`, `Innovations.innov_of_known_succ`, `Innovations.innov_const` |
| Cochrane p. 65 | "since `v_t` is known at time `t`, it disappears from this innovation accounting" | `Innovations.innov_of_known` |
| Cochrane (3.20), p. 65 | `Δ_{t+1}(E_mx) = Δ_{t+1}x` for `m ≥ t + 1` | `Innovations.innov_E_of_le` |
| Cochrane (4.1), p. 87 | martingale-difference shocks indexed by `ℤ` (scalar and vector); `E_tε_k` is `ε_k` or `0`; `Δ_{t+1}ε_k` is `ε_{t+1}` or `0` | `Innovations.IsMDS`, `Innovations.IsMDSVec`, `Innovations.E_shock_eq_zero`, `Innovations.E_shock`, `Innovations.innov_shock`, `Innovations.innov_shock_vec`, `Innovations.isMDSVec_of_isMDS` |
| Cochrane (4.1), p. 87 | `ℕ`-indexed martingale differences (zero forecast at every horizon, past shocks known), and their zero extension to the past | `Innovations.IsMDSNat`, `Innovations.IsMDSNat.E_future`, `Innovations.IsMDSNat.E_past`, `Innovations.extendShock`, `Innovations.isMDS_extendShock`, `Innovations.extendShock_bounded` |
| Cochrane (4.2), p. 87 | `E_t` and `Δ_{t+1}` commute with `∑c_jx_j` for absolutely summable weights and bounded `x_j` (generalising the core `ExpectationSystem.E_tsum`) | `Innovations.E_tsum_abs`, `Innovations.summable_E_terms`, `Innovations.innov_tsum_abs` |
| Cochrane (4.1)–(4.2), p. 87; §4.2.7, pp. 97–98 | the moving average `s_t = a(L)ε_t` (scalar and vector, absolutely summable coefficients), the generating function `a(z)`, its vector form and `c'ε_k`; `a(0) = a_0`; summability of `∑a_jzʲ` for `\|z\| ≤ 1`; the scalar case is the one-shock vector case | `Innovations.IsMA`, `Innovations.IsMAVec`, `Innovations.gen`, `Innovations.genVec`, `Innovations.dotShock`, `Innovations.gen_zero`, `Innovations.summable_coeff_mul_pow`, `Innovations.isMA_iff_vec` |
| Cochrane (4.1), p. 87 | a moving average in a bounded MDS is bounded, adapted, and `E_m` passes through its sum | `Innovations.abs_ma_term_le`, `Innovations.summable_ma_bound`, `Innovations.E_MAVec`, `Innovations.summable_E_MAVec`, `Innovations.abs_MAVec_le`, `Innovations.adapted_MAVec` |
| Cochrane (4.2), p. 87 (Hansen, Roberds and Sargent) | `Δ_{t+1}s_{t+1+j} = a_j'ε_{t+1}`; with `a_0 = 1`, `Δ_{t+1}s_{t+1} = ε_{t+1}` (4.4) | `Innovations.innov_MAVec`, `Innovations.innov_MA`, `Innovations.innov_MA_zero` |
| Cochrane (4.2), p. 87 | `Δ_{t+1}∑ρʲs_{t+1+j} = a(ρ)'ε_{t+1}` for `\|ρ\| < 1`, and termwise `∑ρʲΔ_{t+1}s_{t+1+j} = a(ρ)'ε_{t+1}` for every `\|ρ\| ≤ 1`, including `ρ = 1` | `Innovations.hasSum_dot_gen`, `Innovations.innov_PV_vec`, `Innovations.innov_PV`, `Innovations.innov_PV_termwise_vec`, `Innovations.innov_PV_termwise` |
| Cochrane (4.2), p. 87 | the innovations of a moving average satisfy the terminal condition `ρᵀΔ_{t+1}s_{t+1+T} → 0`, `\|ρ\| ≤ 1` | `Innovations.tendsto_pow_mul_innov_MAVec` |
| Cochrane (4.3), p. 87 | the AR(1) and its moving average `a_j = ηʲ`, both directions, and as a core `ExpectationSystem.IsAR1` | `Innovations.ar1_of_MA`, `Innovations.MA_of_ar1`, `Innovations.isAR1_of_MA` |
| Cochrane p. 88 | the i.i.d. process: `a_0 = 1`, `a_j = 0`, `a(z) = 1` | `Innovations.iidCoeff`, `Innovations.isMA_iid`, `Innovations.gen_iid` |
| Cochrane (4.1), p. 87 | a genuinely random bounded MDS on the coin-flip tree, used in the counterexamples | `Innovations.coinShockZ`, `Innovations.coinShockZ_isMDS`, `Innovations.coinShockZ_bounded`, `Innovations.coinShockZ_one` |

## §4.2–§4.2.1 Unexpected inflation, the AR(1) and the MA(1), (4.2)–(4.4), pp. 87–89 (SurplusMA)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §4.2, p. 87 | the simple model: (3.17) with no growth, one-period debt (`rⁿ_{t+1} = i_t` known at `t`), constant expected real return; the innovation terminal condition, automatic for bounded debt and `\|ρ\| < 1` | `SurplusMA.SimpleModel`, `SurplusMA.InnovTVC`, `SurplusMA.innovTVC_of_bounded` |
| Cochrane (4.2), p. 87 | `Δ_{t+1}π_{t+1} = −∑ρʲΔ_{t+1}s̃_{t+1+j} = −a(ρ)ε_{t+1}`, for every `\|ρ\| ≤ 1` | `SurplusMA.innov_infl_eq_tsum`, `SurplusMA.innov_infl_eq` |
| Cochrane (4.4), p. 88 | `Δπ_{t+1} = −a(ρ)Δs̃_{t+1}` | `SurplusMA.innov_infl_eq_surplus` |
| Cochrane §4.2.1, pp. 88–89 | the volatility of unexpected inflation is `a(ρ)²` times that of the shock; its covariance with the shock is `−a(ρ)` times the shock variance; with `a(ρ) = 0` there is no correlation | `SurplusMA.condVar_innov_infl`, `SurplusMA.condCov_innov_infl`, `SurplusMA.no_correlation_of_gen_zero` |
| Cochrane p. 88 | the example "5/(1 − 0.55) = 11%" (it is `100/9`) | `SurplusMA.ar1_volatility_example` |
| Cochrane (4.3), p. 88 | AR(1): `a(ρ) = 1/(1 − ρη)`; "a number greater than one" iff `η > 0` (E2); `η = −0.3`, `ρ = 0.9` gives `a(ρ) < 1` | `SurplusMA.gen_ar1`, `SurplusMA.one_lt_gen_ar1_iff`, `SurplusMA.gen_ar1_lt_one_example` |
| Cochrane p. 88 | `a_0 = 1` and `a(ρ) < 1` force some `a_j < 0` (`ρ > 0`) | `SurplusMA.exists_neg_coeff_of_gen_lt_one` |
| Cochrane p. 88 | the MA(1) `(1 − θL)ε_t`: `a(ρ) = 1 − θρ`; `θ = ρ⁻¹` gives `a(ρ) = 0`; `θ = 0` gives `1`; `θ < 0` gives `a(ρ) > 1`; `0 < θ < ρ⁻¹` gives `0 < a(ρ) < 1` | `SurplusMA.ma1Coeff`, `SurplusMA.isMA_ma1`, `SurplusMA.gen_ma1`, `SurplusMA.gen_ma1_inv`, `SurplusMA.gen_ma1_zero`, `SurplusMA.one_lt_gen_ma1`, `SurplusMA.gen_ma1_mem_Ioo` |
| Cochrane p. 88 (E3) | the MA(1) shock: `Δ_{t+1}s_{t+1} = ε_{t+1}`, `Δ_{t+1}s_{t+2} = −θε_{t+1}`; the printed signs hold only where there is no shock | `SurplusMA.innov_ma1_now`, `SurplusMA.innov_ma1_next`, `SurplusMA.ma1_printed_signs_false` |

## §4.2.2 Surpluses and debt, (4.5)–(4.7), pp. 89–90 (SurplusMA)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (4.6), p. 89 | `v_t = E_t(s̃_{t+1} + ρv_{t+1})` (with the constant expected return `c` normalised to 0) | `SurplusMA.value_recursion` |
| Cochrane (4.5), p. 89 | AR(1) surplus: `v_t = ηs_t/(1 − ρη)` | `SurplusMA.value_ar1` |
| Cochrane (4.7), p. 89 | `ρΔv_{t+1} = −Δπ_{t+1} − Δs̃_{t+1} = [a(ρ) − 1]ε_{t+1}` | `SurplusMA.rho_innov_value`, `SurplusMA.rho_innov_value_eq` |
| Cochrane pp. 89–90 | a surprise surplus raises the value of debt iff `a(ρ) > 1`; with `a(ρ) = 0` it lowers it one for one; with `a(ρ) = 1` debt is unchanged | `SurplusMA.innov_value_pos_iff`, `SurplusMA.innov_value_full_repayment` |
| Cochrane p. 91 | the linear rearrangement `ρΔv_{t+1} = ρΔ∑ρʲs̃_{t+2+j} = [a(ρ) − 1]ε_{t+1}` | `SurplusMA.innov_value_eq_series` |

## §4.2.3 The exact model, (4.8)–(4.10), pp. 87, 90–91 (SurplusMA)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §2.7; p. 91 | `B_t/P_{t+1}`, `B_t/P_t`, `P_t/P_{t+1}`, `Q_t = βE_t(P_t/P_{t+1})`, `∑βʲs_{t+j}`, the exact valuation equation `B_t/P_{t+1} = E_{t+1}∑βʲs_{t+1+j}` | `SurplusMA.realDebt`, `SurplusMA.realDebtEnd`, `SurplusMA.deflation`, `SurplusMA.bondPrice`, `SurplusMA.pv`, `SurplusMA.ExactValuation` |
| Cochrane pp. 87, 91 | `B_t/P_{t+1} = (B_t/P_t)(P_t/P_{t+1})`; `∑βʲs_{t+j} = s_t + β∑βʲs_{t+1+j}`; revenue `Q_tB_t/P_t = βE_t(B_t/P_{t+1})` (under pull-out); valuation implies the exact flow identity | `SurplusMA.realDebt_eq_mul`, `SurplusMA.pv_succ`, `SurplusMA.revenue_eq`, `SurplusMA.exact_flow_of_valuation` |
| Cochrane p. 87 (E1) | `(B_t/P_t)Δ_{t+1}(P_t/P_{t+1}) = Δ_{t+1}∑βʲs_{t+1+j} = a(β)ε_{t+1}` | `SurplusMA.exact_innov_line` |
| Cochrane p. 87 (E1) | the printed sum over `s_{t+j}` gives `βa(β)ε_{t+1}`; it equals `a(β)ε_{t+1}` iff `(1 − β)a(β)ε_{t+1} = 0`; coin-flip counterexample (`1/2` against `1`) | `SurplusMA.printed_exact_line`, `SurplusMA.printed_exact_line_iff`, `SurplusMA.printed_exact_line_counterexample` |
| Cochrane (4.8)–(4.10), p. 91 | `(B_t/P_t)Δ(P_t/P_{t+1}) = Δs_{t+1} + βΔ(B_{t+1}/P_{t+2}) = Δs_{t+1} + βΔ∑βʲs_{t+2+j} = ε_{t+1} + [a(β) − 1]ε_{t+1}` | `SurplusMA.exact_innov_flow`, `SurplusMA.exact_innov_flow_pv`, `SurplusMA.exact_innov_flow_ma` |
| Cochrane p. 91 | the revenue innovation is `[a(β) − 1]ε_{t+1}`; `a(β) = 0`: the deficit is debt-financed; `a(β) = 1`: inflation-financed; `a(β) > 1`: less revenue, devaluation exceeds the deficit | `SurplusMA.revenue_innov`, `SurplusMA.financing_by_debt`, `SurplusMA.financing_by_inflation`, `SurplusMA.financing_superinflation` |

## §4.2.4 The return on government debt, pp. 92–93 (SurplusMA)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 92 | `Δr_{t+1} = −Δπ_{t+1} = a(ρ)ε_{t+1}`; split into price change and dividend, `[a(ρ) − 1]ε + ε` | `SurplusMA.innov_return`, `SurplusMA.innov_return_split` |
| Cochrane p. 92 | with `a(ρ) = 0` debt is risk free in real terms; with `a(ρ) ≥ 1` the return is more volatile than surpluses | `SurplusMA.innov_return_riskfree`, `SurplusMA.abs_innov_return_ge` |
| Cochrane p. 93 | the one-step stochastic-discount-factor valuation (pull-out as a hypothesis) | `SurplusMA.sdf_one_step` |

## §4.2.5–§4.2.6 Stylised facts and an s-shaped surplus, pp. 94–97 (SurplusProcessFacts)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 94 | "these phenomena are tied together": `Δπ = −a(ρ)ε`, `ρΔv = (a(ρ) − 1)ε`, `Δr = a(ρ)ε` | `SurplusProcessFacts.tied_together` |
| Cochrane p. 94 | the indirect estimates: `a(ρ) = −E_t[Δπε]/E_t[ε²]`, `a(ρ)² = E_t[(Δπ)²]/E_t[ε²]`, and from the debt–surplus covariance `ρE_t[Δvε] = (a(ρ) − 1)E_t[ε²]` | `SurplusProcessFacts.gen_identified`, `SurplusProcessFacts.gen_identified_debt` |
| Cochrane p. 95 | a government that must not inflate or default needs `a(ρ) = 0` (iff, given a state with a non-zero shock) | `SurplusProcessFacts.no_inflation_iff_gen_zero` |
| Cochrane p. 95 | in the exact model, after a deficit shock, bond-sale revenue rises iff `a(β) < 1`, i.e. iff the value of subsequent surpluses rises | `SurplusProcessFacts.revenue_rises_iff` |
| Cochrane p. 96 | the debt-feedback model `s̃_{t+1} = αv_t + u_{s,t+1}`, `ρv_{t+1} = v_t − s̃_{t+1}`: flow identity, bounded debt for `\|1 − α\| < ρ`, adaptedness, `Δs̃_{t+1} = Δu_{s,t+1}` | `SurplusProcessFacts.fbValue`, `SurplusProcessFacts.fbSurplus`, `SurplusProcessFacts.fb_flow`, `SurplusProcessFacts.fbValue_bounded`, `SurplusProcessFacts.fbValue_adapted`, `SurplusProcessFacts.fb_innov_surplus` |
| Cochrane p. 96 | surpluses are fully repaid, `a_s(ρ) = 0`, for any bounded adapted disturbance | `SurplusProcessFacts.feedback_full_repayment` |
| Cochrane p. 96 | AR(1) news formula `∑ρʲΔu_{t+1+j} = Δu_{t+1}/(1 − ρη)`; `a_s(ρ) = 0` "even if `a_u(ρ) > 1`" | `SurplusProcessFacts.ar1_innov_sum`, `SurplusProcessFacts.feedback_repaid_despite_persistent_u` |

## §4.2.6 The debt-feedback surplus as a closed-form moving average, p. 96 (TidyR6FeedbackMA)

The disturbance is a moving average `u = a_u(L)ε` in a bounded martingale-difference shock with
an infinite past, and `λ = (1 − α)/ρ`. `SurplusProcessFacts` proves `a_s(ρ) = 0` termwise; here
the surplus is a moving average with an explicit coefficient sequence `a_s`.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 96 | the root `λ = (1 − α)/ρ`; the debt coefficients `c_m = ∑_{k ≤ m}a_{u,k}λ^{m−k}`; the surplus coefficients `a_{s,0} = a_{u,0}`, `a_{s,m+1} = a_{u,m+1} − (α/ρ)c_m`; the coefficients of `(1 − ρ⁻¹L)/(1 − λL)` | `TidyR6FeedbackMA.lam`, `TidyR6FeedbackMA.debtCoeff`, `TidyR6FeedbackMA.fbCoeff`, `TidyR6FeedbackMA.fbFactor` |
| Cochrane p. 96 | `c_0 = a_{u,0}` and `c_{m+1} = λc_m + a_{u,m+1}` (the debt dynamics); `a_s(L) = a_u(L)(1 − ρ⁻¹L)/(1 − λL)` as a convolution of coefficients (`ρ ≠ 0`); both sequences absolutely summable for `\|λ\| < 1` | `TidyR6FeedbackMA.debtCoeff_zero`, `TidyR6FeedbackMA.debtCoeff_succ`, `TidyR6FeedbackMA.fbCoeff_eq_conv`, `TidyR6FeedbackMA.summable_abs_debtCoeff`, `TidyR6FeedbackMA.summable_abs_fbCoeff` |
| Cochrane p. 96 | generating functions `c(z) = a_u(z)/(1 − λz)` and `a_s(z) = a_u(z)(1 − z/ρ)/(1 − λz)`; `a_s(ρ) = 0` for every disturbance ("surpluses themselves `s_t` may be fully repaid with `a_s(ρ) = 0`") | `TidyR6FeedbackMA.hasSum_gen_debtCoeff`, `TidyR6FeedbackMA.hasSum_gen_fbCoeff`, `TidyR6FeedbackMA.gen_fbCoeff_rho` |
| Cochrane (4.1), p. 87 (tools) | the moving average `∑_jb_jε_{t−j}` with an infinite past converges at every date and state and is a moving average in the sense of `Innovations.IsMA`; peeling off the current shock | `TidyR6FeedbackMA.maSeries`, `TidyR6FeedbackMA.summable_ma_term`, `TidyR6FeedbackMA.isMA_maSeries`, `TidyR6FeedbackMA.tsum_ma_succ` |
| Cochrane p. 96 | the stationary value of debt `v_t = −ρ⁻¹∑_mc_mε_{t−m}`, a moving average, solves `v_{t+1} = ρ⁻¹((1 − α)v_t − u_{t+1})`; started there, `SurplusProcessFacts.fbValue` is the stationary value at every date | `TidyR6FeedbackMA.statValue`, `TidyR6FeedbackMA.statValue_apply`, `TidyR6FeedbackMA.isMA_statValue`, `TidyR6FeedbackMA.statValue_succ`, `TidyR6FeedbackMA.fbValue_eq_statValue` |
| Cochrane p. 96 (E10, the Chapter 4 half, closed form) | the debt-feedback surplus is the moving average `a_s(L)ε` with impact `a_{s,0} = a_{u,0}`; for `ρ ≠ 0`, `\|ρ\| ≤ 1`, `\|1 − α\| < \|ρ\|`: `a_s(ρ) = 0`, `∑ρʲΔs̃_{t+1+j} = a_s(ρ)ε_{t+1} = 0`, while `∑ρʲΔu_{t+1+j} = a_u(ρ)ε_{t+1}` | `TidyR6FeedbackMA.fbSurplus_eq_maSeries`, `TidyR6FeedbackMA.feedback_ma_repaid` |
| Cochrane p. 96 (link) | for `0 < ρ < 1`, `\|1 − α\| < ρ`, the series of `SurplusProcessFacts.feedback_full_repayment` is the same series, converging to `0` and to `a_s(ρ)ε_{t+1}` | `TidyR6FeedbackMA.feedback_ma_link` |
| Cochrane p. 96 ("the `u_{s,t}` term may have `a_u(ρ) > 1`") | AR(1) disturbance `a_{u,j} = ηʲ`: `c_m = (η^{m+1} − λ^{m+1})/(η − λ)` (`η ≠ λ`) and `c_m = (m + 1)λᵐ` (`η = λ`); explicit `a_{s,m}`; `a_s(z) = (1 − z/ρ)/((1 − ηz)(1 − λz))`, `a_s(ρ) = 0 < 1 < a_u(ρ) = 1/(1 − ρη)` | `TidyR6FeedbackMA.debtCoeff_ar1`, `TidyR6FeedbackMA.debtCoeff_ar1_eq`, `TidyR6FeedbackMA.fbCoeff_ar1`, `TidyR6FeedbackMA.feedback_ar1_closed_form` |

## §4.2.7 Generalisations, (4.11)–(4.13), pp. 97–98, and A2 §2.3, p. 606 (GeneralizedHRS)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 98 | algebra of `c'ε`; non-degenerate shocks (no non-zero `c'ε_k` vanishes), so coefficient vectors are identified; `a(0) = a_0` for vectors | `GeneralizedHRS.dotShock_add`, `GeneralizedHRS.dotShock_sub`, `GeneralizedHRS.dotShock_neg`, `GeneralizedHRS.Nondeg`, `GeneralizedHRS.genVec_zero` |
| Cochrane p. 98 | for `\|ρ\| ≤ 1`, `∑_{j≥0}ρʲΔx_{t+1+j} = a_x(ρ)'ε_{t+1}` and `∑_{j≥1}ρʲΔx_{t+1+j} = [a_x(ρ) − a_x(0)]'ε_{t+1}` | `GeneralizedHRS.seriesTo_innov_MAVec`, `GeneralizedHRS.seriesTo_innov_MAVec_succ` |
| Cochrane p. 98 (E4) | corrected line before (4.11): `Δπ_{t+1} − Δrⁿ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ) − a_r(0)]'ε_{t+1}` | `GeneralizedHRS.innov_pi_vector` |
| Cochrane p. 98 (E4) | the printed right-hand side `[−a_s(ρ) − a_g(ρ) + a_r(ρ)]'ε` is identically zero; the printed line holds iff there is no unexpected inflation | `GeneralizedHRS.printed_rhs_eq_zero`, `GeneralizedHRS.printed_line_iff` |
| Cochrane p. 98 (E4) | a coin-flip model (i.i.d. surplus equal to the ex-post return, `π = −ε`) in which the printed line fails: `Δ_1π_1 = −1`, right-hand side `0` | `GeneralizedHRS.cxShock`, `GeneralizedHRS.cxCoeff`, `GeneralizedHRS.cxSurplus`, `GeneralizedHRS.cx_isMAVec`, `GeneralizedHRS.cx_innov_shock`, `GeneralizedHRS.printed_line_counterexample` |
| Cochrane (4.11), p. 98; A2 p. 606 (E4) | (4.11) `a_s(ρ) + a_g(ρ) = a_r(ρ)` is an identity in every model satisfying the flow identity and the terminal condition: shock form, and coefficient form under non-degenerate shocks; A2's `0 = a_s(ρ) − a_r(ρ)` | `GeneralizedHRS.identity_4_11`, `GeneralizedHRS.identity_4_11_vec`, `GeneralizedHRS.identity_A2` |
| Cochrane (4.11), p. 98 (E4) | the repayment condition with one-period debt: no unexpected inflation iff `a_s(ρ) + a_g(ρ) = a_r(ρ) − a_r(0)` | `GeneralizedHRS.repayment_iff`, `GeneralizedHRS.repayment_iff_vec` |
| Cochrane p. 98; A2 p. 606 | constant expected returns: `a_{r,j} = 0` for `j ≥ 1`, so `a_r(ρ) = a_r(0)`; with no growth the repayment condition is `a_s(ρ) = 0` | `GeneralizedHRS.const_expected_return_coeffs`, `GeneralizedHRS.const_discount_gen`, `GeneralizedHRS.repayment_reduces` |
| Cochrane (4.12), p. 98 | `a_π(ω)'ε = [−a_s(ρ) − a_g(ρ) + a_r(ρ) − a_r(ω)]'ε` (correct as printed) | `GeneralizedHRS.identity_4_12` |
| Cochrane p. 98 (Campbell–Shiller) | `r_{t+1} = ρ(p − d)_{t+1} − (p − d)_t + Δd_{t+1}` is a valuation recursion; `p_t − d_t = ∑_{j≥1}ρ^{j−1}(Δd_{t+j} − r_{t+j})`, finite horizon, ex post and in expectation | `GeneralizedHRS.CSReturn`, `GeneralizedHRS.csReturn_iff_recursion`, `GeneralizedHRS.campbellShiller_finite`, `GeneralizedHRS.campbellShiller`, `GeneralizedHRS.campbellShiller_expected` |
| Cochrane p. 98 (Campbell–Ammer, E5) | corrected display `Δr_{t+1} = Δ∑_{j≥1}ρ^{j−1}Δd_{t+j} − Δ∑_{j≥2}ρ^{j−1}r_{t+j} = {a_d(ρ) − [a_r(ρ) − a_r(0)]}'ε`; the printed display, and a counterexample (`5/2` against `1`) | `GeneralizedHRS.campbellAmmer`, `GeneralizedHRS.campbellAmmer_MA`, `GeneralizedHRS.printedCampbellAmmer`, `GeneralizedHRS.printed_campbellAmmer_counterexample` |
| Cochrane (4.13), p. 98 | `0 = [a_d(ρ) − a_r(ρ)]'ε`, an identity; coefficient form | `GeneralizedHRS.identity_4_13`, `GeneralizedHRS.identity_4_13_vec` |
| Cochrane A2 §2.3, p. 606 | "the present value relation in a model with a constant discount rate is not an identity": it holds iff the discounted expected returns sum to zero | `GeneralizedHRS.pv_constant_discount_iff` |

## §4.3 Surplus process estimates: conditioning down, pp. 101–102 and 108, and A2 §2.1.7, (2.22)–(2.23), pp. 602–603 (ConditioningDown)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 101 (`I_t ⊂ Ω_t`) | one system conditions on less information than another (tower property across information sets); reflexive, transitive; every system is coarser than full information (`E_t = id`) | `ConditioningDown.Coarser`, `ConditioningDown.coarser_refl`, `ConditioningDown.coarser_trans`, `ConditioningDown.fullInfo`, `ConditioningDown.coarser_fullInfo` |
| Cochrane p. 101 | always `E(X\|I_t) = E(v_t\|I_t)`; conditioning down is valid when `v_t ∈ I_t`, and only then | `ConditioningDown.condDown_general`, `ConditioningDown.condDown`, `ConditioningDown.condDown_iff` |
| Cochrane p. 101 | the same for the present value of a bounded surplus, as a sum of forecasts and pathwise | `ConditioningDown.condDown_series`, `ConditioningDown.condDown_pathwise` |
| Cochrane p. 102 | with `I = Ω`, `v_t` is an exact function of the VAR information (100% R²); a `v_t` not known given the VAR information refutes `I = Ω` | `ConditioningDown.r_squared_one`, `ConditioningDown.info_larger_of_not_known` |
| Cochrane p. 101; A2 p. 602 | an explicit failure on the coin-flip tree: `E(X\|I_0) = 1/2 ≠ v_0` | `ConditioningDown.condDown_fails_example` |
| Cochrane p. 101; A2 (2.22)–(2.23), p. 602 | the Mathlib conditional expectation on a finite space with full support is an `ExpectationSystem`; nested filtrations give coarser systems; known iff measurable; conditioning down holds iff `v_t` is `ℱI_t`-measurable | `ConditioningDown.CondExp.eq_of_ae_eq`, `ConditioningDown.CondExp.le_of_ae_le`, `ConditioningDown.CondExp.condExpSystem`, `ConditioningDown.CondExp.condExpSystem_E`, `ConditioningDown.CondExp.condExpSystem_coarser`, `ConditioningDown.CondExp.condExpSystem_known_iff`, `ConditioningDown.CondExp.condDown_condExp_iff` |

## §4.3 Conditioning down on a general probability space, pp. 101–102, and A2 (2.22)–(2.23), p. 602 (ConditioningDownMeasure)

People condition on a filtration `𝓕_t` (the book's `Ω_t`), the econometrician on a coarser
`𝓖_t ≤ 𝓕_t` (`I_t`) on the same probability space; both forecasts are Mathlib conditional
expectations, so nothing is finite or finitely supported. Statements hold almost everywhere, for
bounded measurable processes and `|ρ| < 1`.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 101 (`I_t ⊂ Ω_t`); A2 p. 602 ("two nested expectation systems") | the econometrician's system: same probability, coarser filtration; nested pairs, and every nested pair is a system with its coarsening; `v_t ∈ I_t` as a.e. `𝓖_t`-measurability; the econometrician's forecast is `condExp` given `𝓖_t` | `ConditioningDownMeasure.coarsen`, `ConditioningDownMeasure.Nested`, `ConditioningDownMeasure.MeasCoarser`, `ConditioningDownMeasure.eq_coarsen`, `ConditioningDownMeasure.KnownAE`, `ConditioningDownMeasure.coarsen_μ`, `ConditioningDownMeasure.coarsen_E` |
| Cochrane p. 101; A2 (2.22)–(2.23), p. 602 | the tower property across information sets; always `E(X\|I_t) = E(v_t\|I_t)`; `v_t = E(X\|I_t)` iff `v_t ∈ I_t`, with no integrability of `X`; known iff equal to its own forecast | `ConditioningDownMeasure.E_coarsen_tower`, `ConditioningDownMeasure.condDown_general`, `ConditioningDownMeasure.condDown_iff`, `ConditioningDownMeasure.known_iff_E_eq` |
| Cochrane p. 102 ("assume … `I_t = Ω_t`") | with no coarsening `v_t` is always known | `ConditioningDownMeasure.known_of_same` |
| Cochrane (2.13), p. 30, across information sets | the agents' news is unforecastable with the coarser information | `ConditioningDownMeasure.E_coarsen_innov` |
| Cochrane A2 (2.22)⇒(2.23), p. 602; p. 101 | under the agents' valuation equation, `∑ρʲE(s_{t+1+j}\|I_t) = E(v_t\|I_t)` (a genuine `HasSum`), and `= v_t` iff `v_t ∈ I_t` | `ConditioningDownMeasure.condDown_valuation`, `ConditioningDownMeasure.condDown_valuation_iff` |
| Cochrane (3.18)–(3.19), pp. 63–64 | the recursion iterated ex post; under any information the discounted forecasts sum to the forecast of `v_t`; under the agents' information to `v_t` | `ConditioningDownMeasure.pv_ex_post`, `ConditioningDownMeasure.pv_E`, `ConditioningDownMeasure.pv_agents` |
| Cochrane p. 101; A2 p. 602; `Links.condDown_flow` | with the flow identity ex post, the present value under any coarser information is `E(v_t\|I_t)`, hence `v_t` iff `v_t ∈ I_t` | `ConditioningDownMeasure.condDown_flow_iff` |
| Cochrane (3.20), p. 65 | news about a bounded variable is bounded; discounted news is summable; `∑ρʲΔf_{t+1+j} = Δ_{t+1}x_t` under any information | `ConditioningDownMeasure.abs_innov_le`, `ConditioningDownMeasure.summable_innov`, `ConditioningDownMeasure.innov_pv` |
| Cochrane (3.20), p. 65 | for ANY information set, `Δπ − Δrⁿ = −∑ρʲΔs̃ − ∑ρʲΔg + ∑_{j≥1}ρʲΔr + Δ_{t+1}v_t`; for the agents the last term vanishes (the book's form); it also vanishes for the econometrician when `v_t ∈ I_t` | `ConditioningDownMeasure.unexpected_inflation_any`, `ConditioningDownMeasure.unexpected_inflation_agents`, `ConditioningDownMeasure.innov_coarsen_of_known` |
| Cochrane §4.2, p. 87 | constant expected returns condition down; the econometrician's return news vanishes | `ConditioningDownMeasure.constExp_condDown`, `ConditioningDownMeasure.innov_return_condDown` |
| Cochrane (4.2), p. 87; p. 101; A2 p. 602 | the simple model under any nested information: `Δπ − Δrⁿ = −∑ρʲΔs̃ + Δ_{t+1}v_t`; for the agents `Δπ = −∑ρʲΔs̃`; for the econometrician the book's form holds iff `Δ^I_{t+1}v_t = 0` | `ConditioningDownMeasure.simple_model_any`, `ConditioningDownMeasure.simple_model_agents`, `ConditioningDownMeasure.simple_model_econ_iff` |
| Cochrane p. 102; A2 p. 602 ("people have more information than we do") | the econometrician sees the agents' information with a one-period lag; it is nested | `ConditioningDownMeasure.lagFiltration`, `ConditioningDownMeasure.nested_lag` |
| Cochrane p. 88, p. 102, (3.17), (4.2) (correction) | i.i.d. shocks, the MA(1) surplus `s̃_t = ε_t + θε_{t−1}`, debt `v_t = θε_t`, return `a(ρ)ε_t`, inflation `−a(ρ)ε_t`: the flow identity and `r = rⁿ − π` hold; the agents' decomposition holds, the lagged econometrician's fails at `t = 1` | `ConditioningDownMeasure.Example.exS`, `ConditioningDownMeasure.Example.exV`, `ConditioningDownMeasure.Example.exR`, `ConditioningDownMeasure.Example.exInfl`, `ConditioningDownMeasure.Example.exRn`, `ConditioningDownMeasure.Example.ex_flow`, `ConditioningDownMeasure.Example.ex_fisher`, `ConditioningDownMeasure.Example.econ_decomp_counterexample` |
| Cochrane p. 101; A2 (2.22)–(2.23) (links) | on a finite state space with full support: the econometrician's system is `ConditioningDown.CondExp.condExpSystem`; a nested pair is `ConditioningDown.Coarser`; the general `condDown_iff` is the abstract `ConditioningDown.condDown_iff`; a.e. means every state; the core innovation is the measure news; the core (3.20) follows | `ConditioningDownMeasure.coarsen_toExpectationSystem_E`, `ConditioningDownMeasure.coarser_core`, `ConditioningDownMeasure.condDown_iff_core`, `ConditioningDownMeasure.forall_of_ae`, `ConditioningDownMeasure.core_innov_eq`, `ConditioningDownMeasure.unexpected_inflation_core` |

## §4.3 Conditioning down with integrable processes and at `|ρ| = 1`, pp. 101–102, and A2 (2.22)–(2.23), p. 602 (TidyR6ConditioningDownL1)

The setting of `ConditioningDownMeasure`, with boundedness replaced by integrability and
discounted summability of the `L¹` norms, `∑_j|ρ|ʲE|x_{k+j}| < ∞` (`DiscL1`). This holds for
`|ρ| < 1` and processes bounded in `L¹` or `L²`, and for every `|ρ| ≤ 1`, including `ρ = ±1`,
when `∑_jE|x_j| < ∞`. Statements hold almost everywhere.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (3.19), p. 64; A2 (2.23), p. 602 (tools) | `∫⁻‖g‖ₑ = E\|g\|`; `∑_jE\|g_j\| < ∞` in extended form; then `∑_j\|g_j\|` converges a.s.; conditional expectations commute with `L¹`-summable series, `∑_jE_mg_j = E_m∑_jg_j` (a genuine `HasSum`, any information, no boundedness) | `TidyR6ConditioningDownL1.lintegral_enorm_eq`, `TidyR6ConditioningDownL1.tsum_lintegral_ne_top`, `TidyR6ConditioningDownL1.ae_summable_abs`, `TidyR6ConditioningDownL1.E_hasSum_L1` |
| Cochrane (3.19), p. 64 ("assuming that the sums converge") | the integrable replacement for bounded processes; it holds for `\|ρ\| < 1` and processes bounded in `L¹`, in `L²`, or essentially bounded, and for `\|ρ\| ≤ 1` when `∑_jE\|x_j\| < ∞` | `TidyR6ConditioningDownL1.DiscL1`, `TidyR6ConditioningDownL1.DiscL1.of_integral_bdd`, `TidyR6ConditioningDownL1.DiscL1.of_sq_bdd`, `TidyR6ConditioningDownL1.DiscL1.of_bdd`, `TidyR6ConditioningDownL1.DiscL1.of_summable` |
| Cochrane (3.17), (3.19), pp. 63–64 (tools) | `DiscL1` is closed under sums and differences and contains zero; the discounted terms have summable `L¹` norms and are a.e. absolutely summable | `TidyR6ConditioningDownL1.DiscL1.add`, `TidyR6ConditioningDownL1.DiscL1.sub`, `TidyR6ConditioningDownL1.DiscL1.zero`, `TidyR6ConditioningDownL1.DiscL1.summable_integral`, `TidyR6ConditioningDownL1.DiscL1.ae_summable` |
| Cochrane (3.18)–(3.19), pp. 63–64, any `ρ` | `L¹` versions of `ConditioningDownMeasure.pv_ex_post`, `ConditioningDownMeasure.pv_E`, `ConditioningDownMeasure.pv_agents`: the ex-post present value, the discounted forecasts under any information, and for the agents `v_t` itself | `TidyR6ConditioningDownL1.pv_ex_post_L1`, `TidyR6ConditioningDownL1.pv_E_L1`, `TidyR6ConditioningDownL1.pv_agents_L1` |
| Cochrane A2 (2.22)–(2.23), p. 602; p. 101, any `ρ` | the econometrician's discounted forecasts sum to `E(v_t\|I_t)`, and to `v_t` iff `v_t ∈ I_t`; the bounded `ConditioningDownMeasure.condDown_valuation_iff` is the special case `TidyR6ConditioningDownL1.DiscL1.of_bdd` | `TidyR6ConditioningDownL1.condDown_valuation_L1`, `TidyR6ConditioningDownL1.condDown_valuation_L1_iff`, `TidyR6ConditioningDownL1.condDown_valuation_iff_of_bdd` |
| Cochrane p. 101; A2 p. 602, any `ρ` | with the flow identity (3.17) ex post, the econometrician's discounted forecasts of `s̃ + g − r` sum to `E(v_t\|I_t)`, hence to `v_t` iff `v_t ∈ I_t` | `TidyR6ConditioningDownL1.condDown_flow_iff_L1` |
| Cochrane (3.20), p. 65, any `ρ` | discounted news about a `DiscL1` process is summable; `∑ρʲΔ_{t+1}f_{t+1+j} = Δ_{t+1}x_t` under any information | `TidyR6ConditioningDownL1.summable_innov_L1`, `TidyR6ConditioningDownL1.innov_pv_L1` |
| Cochrane (3.20), p. 65; (4.2), p. 87; p. 101; A2 p. 602, any `ρ` | `L¹` versions of the unexpected-inflation decompositions of `ConditioningDownMeasure`: under any information with the extra term `Δ^I_{t+1}v_t`; the book's form for the agents; the simple model under any nested information, for the agents, and for the econometrician iff `Δ^I_{t+1}v_t = 0` | `TidyR6ConditioningDownL1.unexpected_inflation_any_L1`, `TidyR6ConditioningDownL1.unexpected_inflation_agents_L1`, `TidyR6ConditioningDownL1.simple_model_any_L1`, `TidyR6ConditioningDownL1.simple_model_agents_L1`, `TidyR6ConditioningDownL1.simple_model_econ_iff_L1` |
| Cochrane (3.18)–(3.19), pp. 63–64 (tools) | if `a = S_n + b_n` for every `n`, then `S_n → a` iff `b_n → 0`; forward iteration of the forecasts, `E_mx_t = ∑_{j<T}ρʲE_mf_{t+1+j} + ρᵀE_mx_{t+T}` for all `T` at once | `TidyR6ConditioningDownL1.tendsto_iff_of_eq`, `TidyR6ConditioningDownL1.E_rec_finite` |
| Cochrane (3.18)–(3.20), pp. 63–65, every `ρ`, including `\|ρ\| = 1` | each present value converges iff its terminal condition holds: ex post, state by state (`ρᵀx_{t+T} → 0`); the forecasts under any information (`ρᵀE_mx_{t+T} → 0`); the news (`ρᵀΔ_{t+1}x_{t+T} → 0`) | `TidyR6ConditioningDownL1.pv_ex_post_iff_tvc`, `TidyR6ConditioningDownL1.pv_E_iff_tvc`, `TidyR6ConditioningDownL1.innov_pv_iff_tvc` |
| Cochrane p. 101; A2 p. 602, every `ρ` | the econometrician's discounted forecasts converge to `E(v_t\|I_t)` iff his terminal condition `ρᵀE(v_{t+T}\|I_t) → 0` holds; given it, to `v_t` iff `v_t ∈ I_t` | `TidyR6ConditioningDownL1.condDown_flow_iff_tvc` |
| Cochrane (3.19); A2 (2.22)–(2.23), p. 602; p. 101, every `ρ`, in `L¹` | with the terminal condition in `L¹` the discounted forecasts converge in `L¹` to `E_mx_t`; with conditionally convergent present values (e.g. `ρ = 1`, partial sums converging in `L¹`) the econometrician's forecasts converge in `L¹` to `E(v_t\|I_t)`, and to `v_t` iff `v_t ∈ I_t` | `TidyR6ConditioningDownL1.pv_E_tendsto_L1`, `TidyR6ConditioningDownL1.condDown_valuation_tendsto_L1`, `TidyR6ConditioningDownL1.condDown_valuation_tendsto_L1_iff` |
| Cochrane (3.18), p. 63, `\|ρ\| = 1` (correction to `ConditioningDownMeasure`) | the bounded-process statements need `\|ρ\| < 1`: with `ρ = ±1`, `x_t = ρᵗ` and no payoff, the recursion holds and `x` is bounded, but neither the ex-post nor the forecast present value equals `x_0 = 1`, and `x` is not `DiscL1` | `TidyR6ConditioningDownL1.pv_unit_root_fails` |
| Cochrane p. 101; A2 p. 602, `\|ρ\| = 1` (corrected statement) | with the flow identity ex post and `∑_tE\|v_t\| < ∞`, `∑_tE\|s̃_t + g_t − r_t\| < ∞`, the econometrician's discounted forecasts sum to `E(v_t\|I_t)`, and to `v_t` iff `v_t ∈ I_t` | `TidyR6ConditioningDownL1.condDown_flow_unit_root` |

## §4.3 The non-invertible MA(1), p. 102 (Invertibility)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 102 | MA(1): `a(ρ) = 1 − θρ`; `a(ρ) = 0` iff `θ = ρ⁻¹`; `0 ≤ θ < 1` gives `a(ρ) > 1 − ρ` | `Invertibility.ma1_aRho`, `Invertibility.ma1_aRho_eq_zero_iff`, `Invertibility.ma1_aRho_gt` |
| Cochrane p. 102 | the MA(1) autocovariances, and the flip: root `θ`, variance `σ²` and root `θ⁻¹`, variance `θ²σ²` have the same autocovariances | `Invertibility.ma1_autocov`, `Invertibility.ma1_autocov_flip` |
| Cochrane p. 102 | "you will falsely estimate `a(ρ) = 1 − ρ² ≠ 0`" | `Invertibility.ma1_fitted_aRho` |
| Cochrane p. 102 | forecasts of the MA(1); `v_t = −θε_t`; with `θ = ρ⁻¹`, "the value of debt reveals the true shock", `ε_t = −ρv_t` | `Invertibility.ma1_forecasts`, `Invertibility.ma1_pv_forward`, `Invertibility.ma1_value_reveals_shock` |
| Cochrane p. 102; A2 (2.13) | the autoregression estimates `u_t − ρu_{t−1}`: the Wold innovation is the prediction error, has variance `θ²σ²`, and the structural shock is not in the closed span of the surplus history | `Invertibility.Hilbert.ma1_wold` |
| Cochrane p. 102 | the PV relation is untestable with returns as discount rates | see A2 §2.2 below (`VARIdentities.var_pv_identity`) |

## §4.4 The roots of inflation, (4.14)–(4.18), pp. 103–116 (VARIdentities)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (4.17), p. 104 | the VAR `z_{t+1} = Az_t + ε_{t+1}` with random-variable coordinates; unforecastable shocks | `VARIdentities.IsVAR`, `VARIdentities.ShockMDS` |
| Cochrane p. 112 | observables `c'z`, realisations, linearity, innovations and expectations of observables, adaptedness | `VARIdentities.obs`, `VARIdentities.vecAt`, `VARIdentities.obs_apply`, `VARIdentities.obs_add`, `VARIdentities.obs_sub`, `VARIdentities.innov_obs`, `VARIdentities.E_obs`, `VARIdentities.obs_adapted` |
| Cochrane p. 103 ("impulse-responses die out"); A2 p. 605 | geometrically decaying powers; implied by all complex eigenvalues in the open unit disc (Gelfand); kept under scaling by `\|ω\| ≤ 1`; entries summable and tending to zero | `VARIdentities.PowDecay`, `VARIdentities.eigs`, `VARIdentities.map_ofReal_pow`, `VARIdentities.powDecay_of_eigs`, `VARIdentities.powDecay_smul`, `VARIdentities.summable_pow_entry`, `VARIdentities.tendsto_pow_entry` |
| Cochrane pp. 111–112 | the Neumann series `∑Aᵏ = (I − A)⁻¹`, `I − A` invertible | `VARIdentities.neumannSum`, `VARIdentities.neumannSum_mul`, `VARIdentities.inv_one_sub_eq`, `VARIdentities.isUnit_det_one_sub`, `VARIdentities.inv_one_sub_hasSum` |
| Cochrane p. 112 | `∑c'Aᵏe = c'(I − A)⁻¹e`; `∑_{j≥1}(1 − ωʲ)Aʲ = A(I − A)⁻¹ − ωA(I − ωA)⁻¹` | `VARIdentities.hasSum_bilin`, `VARIdentities.neumann_bilin_hasSum`, `VARIdentities.disc_rate_hasSum`, `VARIdentities.weight_bilin` |
| Cochrane (4.17), p. 104 | forecasts `E_tz_{t+k} = Aᵏz_t` and impulse responses `Δ_{t+1}z_{t+1+k} = Aᵏε_{t+1}`, for the state and for observables | `VARIdentities.var_forecast`, `VARIdentities.var_innov`, `VARIdentities.var_innov_obs`, `VARIdentities.var_forecast_obs` |
| Cochrane pp. 111–112 | `∑ρʲΔc'z_{t+1+j} = c'(I − ρA)⁻¹ε_{t+1}`; the surplus-and-growth sum `(a_s + a_g)'(I − A)⁻¹ε_1`; the discount-rate term `(a_{rⁿ} − a_π)'[A(I − A)⁻¹ − ωA(I − ωA)⁻¹]ε_1` | `VARIdentities.var_weighted_sum`, `VARIdentities.var_sum_responses`, `VARIdentities.var_disc_rate_sum` |
| Cochrane (4.15), p. 103 (E6) | (3.20) for general `ρ`, indices corrected to `g_{1+j}`, `r_{1+j}`; derived from `LinearizedIdentities.unexpected_inflation_identity` | `VARIdentities.identity_4_15` |
| Cochrane (4.16), p. 104 | (3.21): `Δrⁿ_{t+1} = −∑_{j≥1}ωʲΔrⁿ_{t+1+j}`; derived from `LinearizedIdentities.bond_return_identity` | `VARIdentities.identity_4_16` |
| Cochrane (4.14), p. 103 | (3.22) for general `ρ`, `∑ωʲΔπ = −∑ρʲΔs̃ − ∑ρʲΔg + ∑_{j≥1}(ρʲ − ωʲ)Δr` | `VARIdentities.identity_4_14` |
| Cochrane pp. 103–104 | in a stable VAR satisfying the identities every hypothesis holds automatically: (4.15), (4.14) with (4.16), and (4.14) at the book's `ρ = 1` | `VARIdentities.var_shifted_summable`, `VARIdentities.identity_4_15_of_var`, `VARIdentities.identity_4_14_of_var`, `VARIdentities.identity_4_14_rho_one_of_var` |
| Cochrane (4.17), p. 104 | filling in shocks by regression on the inflation shock is the Cholesky orthogonalisation with inflation first; the single-shock coefficient `Σ_{zπ}/Σ_{ππ} = L_{zπ}/L_{ππ}` | `VARIdentities.Regression.cholesky_blocks`, `VARIdentities.Regression.regression_eq_cholesky`, `VARIdentities.Regression.filled_shock_eq_orthogonalized`, `VARIdentities.Regression.regression_coeff_single` |
| Cochrane (4.18), p. 112 | regression on a functional `f'ε`: `b = Σf/(f'Σf)`, normalised `f'b = 1`, well defined since `f'Σf > 0`; the surplus-shock start makes the sum of surpluses respond by exactly `−1` | `VARIdentities.Regression.functional_regression`, `VARIdentities.Regression.functional_regression_normalised`, `VARIdentities.Regression.quadForm_pos`, `VARIdentities.Regression.surplus_shock_sum` |

## Online Appendix A2 §§2.1.1–2.1.6 How not to test: invertibility, (2.1)–(2.21), pp. 594–602 (Invertibility)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane A2 (2.3), p. 595 | the coefficients of `(1 − θL)/(1 − φL)`, `a(z) = (1 − θz)/(1 − φz)`, absolutely summable for `\|φ\| < 1` | `Invertibility.armaCoeff`, `Invertibility.armaCoeff_hasSum`, `Invertibility.genFn_armaCoeff`, `Invertibility.summable_abs_armaCoeff` |
| Cochrane (4.1), p. 87; A2 (2.4)–(2.5), p. 597 (E12) | MA(∞) autocovariances; the ARMA(1,1) autocovariances; root `θ`, variance `σ²` and root `θ⁻¹`, variance `θ²σ²` are indistinguishable | `Invertibility.autocov`, `Invertibility.arma11_autocov`, `Invertibility.arma11_autocov_flip` |
| Cochrane A2 p. 597 (E12) | the Blaschke identity `\|1 − ρ⁻¹z\| = \|ρ\|⁻¹\|1 − ρz\|` on the unit circle; spectral densities agree after rescaling the variance by `1/ρ²` | `Invertibility.blaschke_norm`, `Invertibility.spectral_density_flip` |
| Cochrane p. 102; A2 pp. 597, 600 | recoverability from current and past surpluses by a summable filter; the complex `a(z)`; recoverable ⇒ no zero in the closed unit disc; a zero there, in particular `a(ρ) = 0` with `\|ρ\| ≤ 1`, makes the shock unrecoverable | `Invertibility.Recoverable`, `Invertibility.genFnC`, `Invertibility.genFnC_ofReal`, `Invertibility.genFnC_ne_zero_of_recoverable`, `Invertibility.not_recoverable_of_root`, `Invertibility.not_recoverable_of_aRho_eq_zero` |
| Cochrane A2 (2.12), p. 598 | the only formal inverse of `1 − RL` is `∑RᵏLᵏ`, not summable for `\|R\| ≥ 1` | `Invertibility.ma1_formal_inverse`, `Invertibility.ma1_inverse_not_summable` |
| Cochrane A2 (2.3), p. 595 | `a(ρ) = β_s`; `β_s = 1` gives i.i.d. | `Invertibility.arma11_aRho_params`, `Invertibility.arma11_iid_of_one` |
| Cochrane A2 pp. 596–598 | the MA root `ρ/(1 − αβ_s)` lies inside the unit circle iff `β_s < (1 − ρ)/α` or `β_s > (1 + ρ)/α`; `\|φ\| < 1 < \|θ\|` is not recoverable | `Invertibility.arma11_root`, `Invertibility.arma11_noninvertible_iff`, `Invertibility.arma11_not_recoverable` |
| Cochrane A2 (2.5), p. 597 | the fitted ARMA(1,1) has `a(ρ) = (1 − ρ²)/α` | `Invertibility.arma11_wold_aRho` |
| Cochrane A2 (2.1)–(2.3), (2.7), p. 595–597 | the debt AR(1) and the surplus ARMA(1,1) in time-domain and revision form | `Invertibility.debt_ar1`, `Invertibility.arma11_time_domain`, `Invertibility.arma11_revision` |
| Cochrane A2 (2.8), pp. 597–598 | the debt–surplus VAR, eigenvalues `0` and `(1 − α)/ρ` (trace and determinant), stable for `\|(1 − α)/ρ\| < 1` (core `SchurStable`), the VAR innovation is the structural shock | `Invertibility.debt_var_eq`, `Invertibility.debt_var_tr_det`, `Invertibility.debt_var_stable`, `Invertibility.shock_from_debt` |
| Cochrane A2 (2.9)–(2.11), p. 598 (E13, E14) | `B_{t−1}/P_t = (1 + βθ)ε_t + θε_{t−1}`; no inflation iff `θ = −R`; then `B_{t−1}/P_t = −Rε_{t−1}`; the printed middle expression of (2.11) is wrong unless `ε_t = 0` | `Invertibility.ma1_debt_value`, `Invertibility.ma1_no_inflation_iff`, `Invertibility.ma1_repaying_debt_value`, `Invertibility.printed_2_11_wrong` |
| Cochrane A2 (2.13), p. 599 | the present-value news is `(1 + βc)w`; for the fitted `c = −β` it is `(1 − β²)w ≠ 0` | `Invertibility.ma1_pv_innov`, `Invertibility.ma1_fitted_pv_innov` |
| Cochrane A2 (2.14)–(2.16), p. 599 | the joint debt–surplus VAR with nilpotent matrix; the shock is recovered as `s_t − B_{t−1}/P`; debt forecasts surpluses | `Invertibility.ma1_debt_var` |
| Cochrane A2 p. 600; (4.1) | the moving average started from a zero pre-sample | `Invertibility.maSeries` |
| Cochrane A2 (2.19), p. 601 | the Hansen–Sargent coefficients `c_k = ∑ρʲa_{k+1+j}` and their properties; the split and forecast of a moving average; `E_t∑ρⁱs_{t+1+i} = ∑c_kε_{t−k}`, also for the pathwise sum; `∑c_kzᵏ = (a(z) − a(ρ))/(z − ρ)` | `Invertibility.hsCoeff`, `Invertibility.summable_hs`, `Invertibility.hsCoeff_rec`, `Invertibility.rho_hsCoeff_zero`, `Invertibility.abs_hsCoeff_le`, `Invertibility.ma_split`, `Invertibility.ma_forecast`, `Invertibility.hansenSargent`, `Invertibility.hansenSargent_E_tsum`, `Invertibility.hansenSargent_genFn` |
| Cochrane A2 (2.18), p. 600 | with `a(ρ) = 0` the ex-post present value equals the forecast, path by path | `Invertibility.value_expost_of_aRho_zero` |
| Cochrane A2 (2.17), (2.20)–(2.21), pp. 600–601 | `a(ρ) = 0` iff `a(L)` has the factor `1 − ρ⁻¹L`; then debt is the invertible moving average `−ρ⁻¹g(L)ε` | `Invertibility.factor_of_aRho_zero`, `Invertibility.factor_value` |
| Cochrane p. 102; A2 p. 597 (Hilbert space) | white noise, the MA(∞) process, the closed past span, the MA(1) `e_t − θe_{t−1}`, the candidate Wold innovation, and their tools | `Invertibility.Hilbert.WhiteNoise`, `Invertibility.Hilbert.maProc`, `Invertibility.Hilbert.pastSpan`, `Invertibility.Hilbert.maOne`, `Invertibility.Hilbert.woldInnov`, `Invertibility.Hilbert.WhiteNoise.norm_eq`, `Invertibility.Hilbert.maProc_hasSum`, `Invertibility.Hilbert.inner_hasSum_right`, `Invertibility.Hilbert.inner_e_maProc`, `Invertibility.Hilbert.mem_pastSpan_self`, `Invertibility.Hilbert.pastSpan_mono`, `Invertibility.Hilbert.mem_orthogonal_pastSpan`, `Invertibility.Hilbert.hasSum_mem_pastSpan` |
| Cochrane p. 102; A2 pp. 597, 600 | for any MA(∞) with `a(ρ) = 0`, `\|ρ\| < 1`, the structural shock is not in the closed span of current and past surpluses | `Invertibility.Hilbert.not_mem_pastSpan_of_aRho_eq_zero` |
| Cochrane A2 (2.5), pp. 597–601 | `w_t = ∑θ⁻ᵏm_{t−k}` converges, satisfies `w_t − θ⁻¹w_{t−1} = m_t`, and is the Wold innovation (orthogonal to the past, variance `θ²σ²`, fitted root `θ⁻¹ = ρ`) | `Invertibility.Hilbert.woldInnov_hasSum`, `Invertibility.Hilbert.wold_recursion`, `Invertibility.Hilbert.inner_e_wold`, `Invertibility.Hilbert.inner_wold_maProc`, `Invertibility.Hilbert.wold_innovation` |
| Cochrane A2 pp. 595–609 | the lag operator on coefficients, and the AR(2)/MA(1) filter identity | `Invertibility.Hilbert.shiftSeq`, `Invertibility.Hilbert.summable_abs_shiftSeq`, `Invertibility.Hilbert.maProc_shift_hasSum`, `Invertibility.Hilbert.maProc_shiftSeq`, `Invertibility.Hilbert.ar2_filter_eq_maOne` |
| Cochrane A2 (2.4)–(2.5), p. 597 (E12) | the ARMA(1,1) Wold statement: the fitted representation has numerator root `ρ`, innovation variance `σ²/ρ²` | `Invertibility.Hilbert.arma11_wold` |

## Online Appendix A2 §§2.1.4–2.1.6 Invertibility, Wold and Granger causality in a Hilbert space, (2.17)–(2.21), pp. 597–601 (InvertibilityMeasure)

Stated for white noise `e` in an arbitrary real Hilbert space, extending the Hilbert-space layer
of `Invertibility`; `InvertibilityMeasureL2` instantiates it in `L²` of a genuine probability space.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 102; (4.1), p. 87 (tools) | the closed span of all shocks; covariances of shocks with the moving average (`σ²a_{t−u}`, zero for future shocks); series, shocks and moving averages lie in the shock span; two members of it with equal shock covariances are equal; `‖s_t‖ ≤ (∑\|a_k\|)‖e_0‖`; the MA(1) coefficients; the norm of a finite combination of shocks; the unit filter `δ` | `InvertibilityMeasure.eSpan`, `InvertibilityMeasure.inner_e_maProc_future`, `InvertibilityMeasure.inner_e_maProc_int`, `InvertibilityMeasure.hasSum_mem_eSpan`, `InvertibilityMeasure.e_mem_eSpan`, `InvertibilityMeasure.maProc_mem_eSpan`, `InvertibilityMeasure.eq_of_inner_e`, `InvertibilityMeasure.norm_maProc_le`, `InvertibilityMeasure.maProc_armaCoeff_zero`, `InvertibilityMeasure.inner_sum_e`, `InvertibilityMeasure.maProc_delta` |
| Cochrane A2 (2.17), pp. 597–601 (tools) | products of lag polynomials (Cauchy product), absolutely summable and equal to the product of power series; a filter of a moving average is the moving average of the product, `b(L)[c(L)e_t] = (b·c)(L)e_t` | `InvertibilityMeasure.cconv`, `InvertibilityMeasure.summable_cconv`, `InvertibilityMeasure.mk_cconv`, `InvertibilityMeasure.hasSum_filter_maProc` |
| Cochrane p. 102; A2 p. 600 | `a(ρ) = 0` with `\|ρ\| ≤ 1`, including `ρ = 1`: no absolutely summable filter of current and past surpluses converges in `H` to the shock | `InvertibilityMeasure.not_filter_of_aRho_eq_zero` |
| Cochrane p. 102; A2 p. 597 ("`ρ ≤ 1`") (correction) | for `s_t = e_t − ρe_{t−1}`, `ρ = ±1`, `a(ρ) = 0` but the shock IS in the closed span of current and past surpluses: Cesàro means of the filter partial sums converge to it, error variance `σ²/(n+1)`; so the closed-span statement needs `\|ρ\| < 1` | `InvertibilityMeasure.mem_pastSpan_unit_root` |
| Cochrane A2 (2.17), p. 600 | the factorisation `a(L) = (1 − θL)g(L)`: coefficients, absolute summability, `a(z) = (1 − θz)g(z)`; an absolutely summable inverse of `g(L)` as a power-series identity; `∑θ⁻ᵏLᵏ(1 − θ⁻¹L) = 1`; coefficients determine the sequence | `InvertibilityMeasure.factorCoeff`, `InvertibilityMeasure.mk_factorCoeff`, `InvertibilityMeasure.summable_factorCoeff`, `InvertibilityMeasure.gen_factorCoeff`, `InvertibilityMeasure.mk_mul_eq_one`, `InvertibilityMeasure.mk_geom_factor`, `InvertibilityMeasure.eq_of_mk_eq` |
| Cochrane A2 pp. 597, 600 (Wold, the factorised (2.17)) | for `a = (1 − θL)g`, `\|θ\| > 1`, `g₀ = 1`, `g` invertible: the autoregression error `w` is white noise with variance `θ²σ²`, `s = ã(L)w` with `ã = (1 − θ⁻¹L)g` (root flipped), `a(θ⁻¹) = 0` but `ã(θ⁻¹) = (1 − θ⁻²)g(θ⁻¹) ≠ 0`, the shock is not in the surplus past and `w_t ≠ e_t` | `InvertibilityMeasure.wold_factor` |
| Cochrane A2 (2.18)–(2.19), pp. 600–601 | for `\|ρ\| < 1` the Hansen–Sargent coefficients are absolutely summable, so debt is a moving average; with `a(ρ) = 0` debt is the ex-post present value, in `H` | `InvertibilityMeasure.summable_abs_hsCoeff`, `InvertibilityMeasure.debt_hasSum_expost` |
| Cochrane A2 (2.20), p. 601 | with the factorisation, `c_k = −θg_k` ("the non-invertible root cancels"), and with `g` invertible the shock is in the closed span of the debt history | `InvertibilityMeasure.hsCoeff_factor`, `InvertibilityMeasure.shock_mem_debtSpan` |
| Cochrane A2 p. 601 (correction) | "the debt is an invertible moving average" needs the other roots outside the unit circle: `a = (1 − θL)(1 − 2L)` has `a(θ⁻¹) = 0` but the shock is not in the closed span of the debt history | `InvertibilityMeasure.debt_not_invertible_example` |
| Cochrane A2 p. 601 ("a VAR including surplus and value of debt") (tools) | white noise has a unitary time shift; the joint surplus–debt span contains the surplus and debt histories; maps of past spans; orthogonality to the joint span | `InvertibilityMeasure.exists_shift`, `InvertibilityMeasure.jointSpan`, `InvertibilityMeasure.pastSpan_le_jointSpan`, `InvertibilityMeasure.debt_mem_jointSpan`, `InvertibilityMeasure.pastSpan_debt_le_jointSpan`, `InvertibilityMeasure.map_pastSpan`, `InvertibilityMeasure.mem_orthogonal_jointSpan` |
| Cochrane A2 (2.21), p. 601 | debt Granger-causes surpluses for an ARBITRARY absolutely summable MA with `a₀ ≠ 0`, `a(ρ) = 0`, `\|ρ\| < 1`: the joint projection of `s_{t+1}` differs from the surplus-only one and its error is strictly smaller | `InvertibilityMeasure.granger_general` |
| Cochrane A2 (2.20)–(2.21), p. 601; p. 102 | factorised case: the joint forecast error is `e_{t+1}` (variance `σ²`), the surplus-only error variance `θ²σ² = σ²/ρ²`, and `σ² < θ²σ²` | `InvertibilityMeasure.granger_factor` |
| Cochrane p. 102; A2 (2.13), p. 599 (links) | `g = 1` is the MA(1) `1 − θL` of `Invertibility` and is invertible; `wold_factor` at `g = 1` gives `Invertibility.Hilbert.ma1_wold`, `Invertibility.ma1_fitted_aRho` and `v_t = −θe_t` | `InvertibilityMeasure.factorCoeff_delta`, `InvertibilityMeasure.recoverable_delta`, `InvertibilityMeasure.wold_factor_ma1` |

## Online Appendix A2 §§2.1.4–2.1.6 in `L²` of an i.i.d. probability space, pp. 597–601 (InvertibilityMeasureL2)

`H = L²(ν^ℕ)` of the i.i.d. economy of `ExpectationsMeasureIID` (not finitely supported), with
shocks `e_t = ε_{φ(t)}` for a bijection `φ : ℤ ≃ ℕ`. Inner products are covariances, closed spans
are mean-square limits and projections are best linear forecasts.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 102; A2 p. 597 | bounded i.i.d. shocks are square integrable; the shocks as elements of `L²`; distinct coordinates are uncorrelated; the shocks are white noise | `InvertibilityMeasureL2.memLp_coord`, `InvertibilityMeasureL2.shockL2`, `InvertibilityMeasureL2.integral_coord_mul`, `InvertibilityMeasureL2.iid_whiteNoise` |
| Cochrane p. 102; A2 p. 600 | `a(ρ) = 0`, `\|ρ\| ≤ 1` including `ρ = 1`: no absolutely summable filter converges in mean square to the shock; for `\|ρ\| < 1` the shock is not in the closed span of the surplus history | `InvertibilityMeasureL2.iid_not_filter`, `InvertibilityMeasureL2.iid_not_mem_pastSpan` |
| Cochrane p. 102; A2 p. 597 ("`ρ ≤ 1`") (correction) | at `ρ = ±1` the shock of `e_t − ρe_{t−1}` is a mean-square limit of linear combinations of current and past surpluses; so the closed-span statement is false for `\|ρ\| ≤ 1` (fair-coin counterexample with `1 − L`) | `InvertibilityMeasureL2.iid_unit_root`, `InvertibilityMeasureL2.closedSpan_fails_at_unit_root` |
| Cochrane A2 pp. 597, 600–601, (2.20)–(2.21) | the factorised Wold statement, and debt Granger-causes surpluses (general MA, and the factorised error variances `σ²` versus `θ²σ²`) in `L²` | `InvertibilityMeasureL2.iid_wold_factor`, `InvertibilityMeasureL2.iid_granger_general`, `InvertibilityMeasureL2.iid_granger_factor` |
| Cochrane p. 102; A2 pp. 597–601 | the fair `±1` coin: `1 − L` has `a(1) = 0`, its shock is in the closed span but no summable filter recovers it; for `\|ρ\| < 1`, `1 − ρ⁻¹L` and debt strictly improves the surplus forecast (error variances `1` versus `ρ⁻²`) | `InvertibilityMeasureL2.coin_L2` |

## Online Appendix A2 §§2.1.4 and 2.1.6 The Wold decomposition theorem, pp. 597 and 600 (Wold)

The book invokes the Wold decomposition theorem ("by the Wold decomposition theorem", p. 600)
without stating it. It is proved here for a sequence `x : ℤ → H` in a real Hilbert space that is
weakly stationary; in `L²` inner products are covariances and orthogonal projections are best
linear forecasts. `H_t` is the closed span of `x_t, x_{t−1}, …`, `H_{−∞}` the remote past.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane A2 p. 597 (`E(s_t\|s_{t−1}, …)`), p. 600 | the past `H_t` (the same subspace as `Invertibility.Hilbert.pastSpan`), the remote past `H_{−∞} = ⋂_tH_t`, the innovation `e_t = x_t − P_{H_{t−1}}x_t`, the Wold coefficients `c_j = ⟪x_0, e_{−j}⟫/‖e_0‖²`, the deterministic part `d_t = P_{H_{−∞}}x_t`; deterministic (`x_t ∈ H_{t−1}` for all `t`) and regular (`H_{−∞} = 0`) | `Wold.past`, `Wold.past_eq_pastSpan`, `Wold.remote`, `Wold.innov`, `Wold.woldCoeff`, `Wold.detPart`, `Wold.Deterministic`, `Wold.Regular` |
| Cochrane A2 pp. 597, 600 (tools) | `x_{t−k} ∈ H_t`, `H_t` grows with `t`; the remote past is closed, equals `⋂_tH_t`, lies in every `H_t`; `x_t = e_t + P_{H_{t−1}}x_t`; `e_t = 0` iff `x_t ∈ H_{t−1}`; the key step `H_t = H_{t−1} ⊕ ℝe_t`; a closed subspace containing `y_t, y_{t−1}, …` contains their closed span | `Wold.mem_past`, `Wold.self_mem_past`, `Wold.past_mono`, `Wold.mem_past_of_le`, `Wold.remote_eq`, `Wold.remote_le`, `Wold.mem_remote_iff`, `Wold.x_eq_innov_add`, `Wold.innov_eq_zero_iff`, `Wold.mem_past_pred`, `Wold.past_le_of_mem` |
| Cochrane A2 p. 597 (stationarity; tools) | the shift `U` maps `H_t` into `H_{t+1}` and commutes with the forecast; `e_{t+1} = Ue_t`; inner products of two processes shifted by the same isometry are shift invariant; `e = 0` at one date means at all | `Wold.map_past`, `Wold.starProjection_shift`, `Wold.innov_shift`, `Wold.inner_shift`, `Wold.innov_eq_zero_of` |
| Cochrane A2 p. 597, (2.5) (Wold (a)) | `e_t ∈ H_t`, `e_t ⟂ H_{t−1}`; the innovations are orthogonal with constant norm, so white noise with variance `‖e_0‖²` | `Wold.innov_mem`, `Wold.innov_mem_orthogonal`, `Wold.inner_innov_of_mem`, `Wold.inner_innov_lt`, `Wold.norm_innov`, `Wold.innov_whiteNoise` |
| Cochrane A2 p. 600 (Wold (b); tools) | `c_j` does not depend on the date; `⟪e_{t−j}, x_t⟫ = c_j‖e‖²`; the normalised innovations are orthonormal; coefficients of any convergent series in the innovations; the regular part lies in `H_t` and is orthogonal to `H_{−∞}`, `e_s ⟂ H_{−∞}`; `x_t − ∑c_je_{t−j} ∈ H_{−∞}`; `x_t = u_t + d_t`, `d_t ∈ H_{−∞}` | `Wold.inner_x_innov`, `Wold.inner_innov_x`, `Wold.orthonormal_innov`, `Wold.woldCoeff_smul`, `Wold.norm_inner_sq`, `Wold.inner_innov_hasSum`, `Wold.regPart_mem`, `Wold.innov_mem_orthogonal_remote`, `Wold.regPart_mem_orthogonal_remote`, `Wold.sub_regPart_mem_remote`, `Wold.x_eq_regPart_add_detPart`, `Wold.detPart_mem_remote` |
| Cochrane A2 pp. 597, 600 ("by the Wold decomposition theorem") (Wold (b)) | `x_t = ∑c_je_{t−j} + d_t`, the series converging in `H`; `∑c_j² < ∞` with Bessel's bound `‖e‖²∑c_j² ≤ ‖x_0‖²`; `c_0 = 1` when `e ≠ 0`; `c_j = ⟪x_t, e_{t−j}⟫/‖e_t‖²` at every date; `d_t = x_t − ∑c_je_{t−j} ∈ H_{−∞}`, `d ⟂ e` | `Wold.hasSum_wold`, `Wold.summable_sq_woldCoeff`, `Wold.tsum_sq_woldCoeff_le`, `Wold.woldCoeff_zero`, `Wold.woldCoeff_eq`, `Wold.detPart_eq`, `Wold.wold_decomposition` |
| Cochrane A2 p. 597 ("an autoregression … recovers the Wold representation") (Wold (c)) | uniqueness: if `x_t = ∑b_jw_{t−j} + z_t` with `w_t ∈ H_t`, `w_t ⟂ H_{t−1}`, `b_0 = 1`, `z_t ∈ H_{−∞}`, then `w = e`, `z = d`, and `b = c` when `e ≠ 0`; no white-noise assumption on `w` is needed | `Wold.wold_unique` |
| Cochrane A2 p. 600 (Wold (d)) | deterministic iff `e = 0` iff `d = x`; regular iff `d = 0` iff `x_t = ∑c_je_{t−j}`; `H_{−∞}` is the closed span of `d_t, d_{t−1}, …` at every `t`; the regular part is regular, the deterministic part deterministic, the two uncorrelated and both shifted by `U`; regular and deterministic means zero | `Wold.deterministic_iff`, `Wold.deterministic_iff_detPart`, `Wold.regular_iff`, `Wold.regular_iff_hasSum`, `Wold.remote_eq_past_detPart`, `Wold.wold_dichotomy`, `Wold.eq_zero_of_regular_deterministic` |
| Cochrane A2 p. 600 (Wold (d)) | a mixed example: `x_t = ε_t + v`, `v ⟂ ε`, `v ≠ 0`, has innovation `ε`, `c = (1, 0, …)`, `d = v`, and is neither regular nor deterministic | `Wold.mixed_example` |
| Cochrane A2 p. 597 (stationarity) | the orbit of a linear isometry is covariance stationary; a covariance-stationary sequence is the orbit of a linear isometry (`LinearMap.extendOfIsometry` on the closed span, the identity on its complement); the two are equivalent; the theorem under covariance stationarity alone | `Wold.stationary_of_shift`, `Wold.exists_shift_of_stationary`, `Wold.stationary_iff_exists_shift`, `Wold.wold_of_stationary` |
| Cochrane A2 p. 597; p. 102 | an absolutely summable moving average in white noise is shifted by the shock shift and is regular, so it has no deterministic part | `Wold.maProc_shift`, `Wold.maProc_regular` |
| Cochrane A2 pp. 597, 600, (2.17) (link) | the factorised claim is the Wold representation: for `a = (1 − θL)g` (`InvertibilityMeasure.wold_factor`) the autoregression error is the Wold innovation, the fitted `ã = (1 − θ⁻¹L)g` are the Wold coefficients, `‖w‖² = θ²σ²`, `d = 0` | `Wold.wold_factor_is_wold` |
| Cochrane A2 p. 597 (correction) | "the Wold representation, which has an invertible moving average": for `s_t = e_t − ρe_{t−1}`, `ρ = ±1`, the Wold innovation is `e_t`, `c = (1, −ρ, 0, …)`, `c(ρ) = 0`, and no absolutely summable autoregression recovers the Wold innovation | `Wold.wold_unit_root` |
| Cochrane A2 p. 600 (`L²` tools) | the constant random variable `1` in `L²(ν^ℕ)`, `E[1·1] = 1`, `1 ≠ 0`, `E[ε_t·1] = 0` | `Wold.IIDEconomy.oneL2`, `Wold.IIDEconomy.inner_oneL2`, `Wold.IIDEconomy.oneL2_ne_zero`, `Wold.IIDEconomy.inner_shockL2_one` |
| Cochrane p. 102; A2 pp. 597, 600 (`L²`) | every absolutely summable MA of the i.i.d. shocks is regular and the MA of its own Wold innovations; for the factorised `a` the Wold innovation is the autoregression error, not the structural shock, with variance `θ²σ²` | `Wold.IIDEconomy.iid_wold`, `Wold.IIDEconomy.iid_wold_factor_is_wold` |
| Cochrane A2 p. 600 (`L²`) | `x_t = ε_t + 1`: innovation `ε_t`, deterministic part the mean `1`, neither regular nor deterministic | `Wold.IIDEconomy.iid_mixed` |
| Cochrane A2 pp. 597, 600 (fair coin) | for `\|ρ\| < 1`, `s_t = e_t − ρ⁻¹e_{t−1}` has Wold coefficients `(1, −ρ, 0, …)` (root flipped), innovation variance `ρ⁻²`, and is regular; `ε_t + 1` has `d = 1`; correction: `ε_t − ε_{t−1}` has Wold polynomial `1 − z`, a root on the unit circle, and no summable autoregression recovers its innovation | `Wold.IIDEconomy.coin_wold`, `Wold.IIDEconomy.coin_wold_unit_root` |

## §4.3, p. 102, and Online Appendix A2 §§2.1.4–2.1.6, pp. 597–601: conditional-expectation forecasts versus linear forecasts (TidyR6CondExpForecast)

`Wold` and `InvertibilityMeasure` state Wold, non-invertibility and Granger causality for best
linear forecasts. Here the forecast is Mathlib's conditional expectation given the σ-algebra of
the past, `E(x|𝓖)`, which in `L²` is the orthogonal projection on the closed subspace `L²(𝓖)`
(Mathlib's `lpMeas`).

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane A2 p. 597 (tools) | for closed subspaces `K ≤ M`, `‖x − P_Kx‖² = ‖x − P_Mx‖² + ‖P_Mx − P_Kx‖²`; the larger projection is the better forecast, and the two coincide iff `P_Mx ∈ K` iff the errors have equal norms | `TidyR6CondExpForecast.Hilbert.nested_pythagoras`, `TidyR6CondExpForecast.Hilbert.nested_projection_eq_iff` |
| Cochrane A2 p. 597 (`E(s_t\|s_{t−1}, …)` as a conditional expectation) | `L²(𝓖)` has an orthogonal projection, and it is a.e. Mathlib's conditional expectation; a closed linear span of `𝓖`-measurable square-integrable variables lies in `L²(𝓖)` | `TidyR6CondExpForecast.hasOrthogonalProjection_lpMeas`, `TidyR6CondExpForecast.starProjection_lpMeas_ae_eq_condExp`, `TidyR6CondExpForecast.closure_span_le_lpMeas` |
| Cochrane p. 102; A2 pp. 597–601 (the general statement) | for every closed `K ≤ L²(𝓖)` (e.g. the closed span of the observed past), with `c = E(F\|𝓖)` and `p = P_KF`: `‖F − p‖² = ‖F − c‖² + ‖c − p‖²`, so the conditional expectation is never worse, and `c = p` iff `c ∈ K` iff the mean-square errors are equal | `TidyR6CondExpForecast.condExp_beats_linear` |
| Cochrane A2 p. 597 (`u_t = s_t − E(s_t\|s_{t−1}, …)` with conditional expectations) | the conditional-expectation forecast errors form a martingale-difference sequence for any filtration, and are orthogonal to every square-integrable function of the past | `TidyR6CondExpForecast.ceInnov_mds`, `TidyR6CondExpForecast.ceInnov_orthogonal` |
| Cochrane A2 p. 597 (`σ(s_t, s_{t−1}, …)`; tools) | the σ-algebra generated by a family and by the current and past values of a process; it is a sub-σ-algebra and the past values are measurable for it; the process in `L²`; `H_t ≤ L²(σ(x_t, x_{t−1}, …))`; the conditional-expectation innovation in `L²`, a.e. `x_t − E(x_t\|σ(x_{t−1}, …))` | `TidyR6CondExpForecast.genSigma`, `TidyR6CondExpForecast.pastSigma`, `TidyR6CondExpForecast.pastSigma_le`, `TidyR6CondExpForecast.measurable_pastSigma`, `TidyR6CondExpForecast.toL2`, `TidyR6CondExpForecast.past_le_lpMeas`, `TidyR6CondExpForecast.ceInnov`, `TidyR6CondExpForecast.ceInnov_ae_eq` |
| Cochrane A2 pp. 597, 600 (Wold with conditional expectations) | the conditional-expectation innovation never has a larger norm than the Wold innovation, and equals it iff the conditional forecast lies in `H_{t−1}` iff the error variances are equal; when that holds at every date of a covariance-stationary `x`, the conditional-expectation innovations are the Wold innovations, white noise, a martingale-difference sequence, and `x_t = ∑c_je_{t−j} + d_t` with them | `TidyR6CondExpForecast.ceInnov_eq_wold_iff`, `TidyR6CondExpForecast.wold_decomposition_condExp` |
| Cochrane p. 102; A2 (2.4), p. 597 (the i.i.d. economy) | the `ℤ`-indexed shock `e_t = ε_{φ(t)}` on `ℕ → ℝ`; the MA(1) surplus `s_t = e_t − θe_{t−1}`, `θ = ρ⁻¹`, and `s_{t+1} = e_{t+1} − θe_t`; measurability and integrability | `TidyR6CondExpForecast.IID.eps`, `TidyR6CondExpForecast.IID.surp`, `TidyR6CondExpForecast.IID.surp_succ`, `TidyR6CondExpForecast.IID.measurable_eps`, `TidyR6CondExpForecast.IID.measurable_surp`, `TidyR6CondExpForecast.IID.integrable_eps` |
| Cochrane p. 102; A2 (2.20)–(2.21), p. 601 (tools) | the σ-algebra of all shocks but `ε_j`, independent of `ε_j`; the current and past surpluses do not involve `e_{t+1}`; given such information `E(e_{t+1}\|𝓖) = 0`, and if it also reveals `e_t`, `E(s_{t+1}\|𝓖) = −θe_t` with error `e_{t+1}` | `TidyR6CondExpForecast.IID.avoidSigma`, `TidyR6CondExpForecast.IID.indep_avoid`, `TidyR6CondExpForecast.IID.measurable_avoid`, `TidyR6CondExpForecast.IID.measurable_surp_avoid`, `TidyR6CondExpForecast.IID.condExp_eps_next`, `TidyR6CondExpForecast.IID.condExp_surp_of_known` |
| Cochrane p. 102 (fair coin; tools) | the decoding map `g`, measurable; the coin shocks are `±1` a.s.; `g(a − θb) = a` for `a, b ∈ {±1}`, `θ ≠ ±1`; the shocks and the surplus are square integrable, the surplus is the `L²` moving average `(1 − θL)·1` of `InvertibilityMeasureL2`; `‖F‖² = EF²` | `TidyR6CondExpForecast.Coin.decode`, `TidyR6CondExpForecast.Coin.measurable_decode`, `TidyR6CondExpForecast.Coin.coin_ae`, `TidyR6CondExpForecast.Coin.eps_pm`, `TidyR6CondExpForecast.Coin.decode_sub`, `TidyR6CondExpForecast.Coin.memLp_eps`, `TidyR6CondExpForecast.Coin.memLp_surp`, `TidyR6CondExpForecast.Coin.toL2_surp`, `TidyR6CondExpForecast.Coin.norm_sq_eq_integral` |
| Cochrane p. 102; A2 p. 597 (correction) | with fair-coin shocks and `θ ≠ ±1` the shock is a measurable function of the current surplus alone, `e_t = g(s_t)` a.e. | `TidyR6CondExpForecast.Coin.coin_shock_eq` |
| Cochrane p. 102; A2 pp. 597–601 (counterexample) | fair coin, `s_t = e_t − θe_{t−1}`, `θ = ρ⁻¹`, `\|θ\| > 1`: `a(ρ) = 0`; `E(s_{t+1}\|σ(s_t, s_{t−1}, …)) = −θe_t` with mean-square error `1`; the best linear forecast has error variance `θ² > 1` and the shock is not in the closed span; so the conditional-expectation innovation is not the Wold innovation | `TidyR6CondExpForecast.Coin.coin_condExp_beats_linear` |

## §4.3, p. 102, and Online Appendix A2 §§2.1.4–2.1.6, pp. 597–601: Gaussian processes (TidyR6GaussianForecast)

For jointly Gaussian processes the conditional expectation given the σ-algebra of the past is the
best linear forecast, so the Wold and Granger statements hold with conditional expectations.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane A2 p. 597 (tools) | `E\|F\| ≤ ‖F‖_{L²}`; `‖F‖² = EF²`; `\|e^{ia} − e^{ib}\| ≤ \|a − b\|`; the characteristic function of a law, `φ(t) = Ee^{itY}`; a family as elements of `L²`; `⟪1, F⟫ = EF`; the closed span of a centred process is centred | `TidyR6GaussianForecast.integral_abs_le_norm`, `TidyR6GaussianForecast.norm_sq_eq_integral`, `TidyR6GaussianForecast.norm_cexp_sub_le`, `TidyR6GaussianForecast.charFun_map_eq`, `TidyR6GaussianForecast.toLpFam`, `TidyR6GaussianForecast.inner_one_eq_integral`, `TidyR6GaussianForecast.integral_eq_zero_of_mem_closure` |
| Cochrane A2 p. 597 (the Gaussian Hilbert space) | Gaussian laws are closed under `L²` limits; every finite combination and every element of the closed linear span of a Gaussian process is Gaussian; the closed span is itself a Gaussian process | `TidyR6GaussianForecast.hasGaussianLaw_of_tendsto`, `TidyR6GaussianForecast.hasGaussianLaw_of_mem_span`, `TidyR6GaussianForecast.hasGaussianLaw_of_mem_closure`, `TidyR6GaussianForecast.isGaussianProcess_closure` |
| Cochrane p. 102; A2 pp. 597–601 | for a centred Gaussian process, `E(X_τ\|σ(X_{past(i)} : i))` is a.e. the projection of `X_τ` on the closed span of the observed values (the best linear forecast) | `TidyR6GaussianForecast.condExp_eq_linear_of_gaussian`, `TidyR6GaussianForecast.linForecast` |
| Cochrane A2 (2.21), p. 601 | the conditional-expectation and linear forecast error variances coincide; so a strict linear Granger improvement (as in `InvertibilityMeasure.granger_general`) is a strict improvement of the conditional-expectation forecast | `TidyR6GaussianForecast.gaussian_condExp_mse`, `TidyR6GaussianForecast.gaussian_granger` |
| Cochrane A2 pp. 597, 600 | for a centred Gaussian process indexed by `ℤ` the conditional-expectation innovation is the Wold innovation at every date; for a covariance-stationary one the Wold decomposition holds with conditional-expectation innovations, which are white noise and a martingale-difference sequence | `TidyR6GaussianForecast.gaussian_ceInnov_eq_wold`, `TidyR6GaussianForecast.gaussian_wold_condExp` |
| Cochrane p. 102; A2 p. 597 (Gaussian shocks; tools) | the law `N(0, σ²)`: mean zero, variance `σ²`, integrable and square integrable; the shocks, coordinates and MA(1) surplus of the i.i.d. Gaussian economy are square integrable; the coordinates and the surplus are Gaussian processes; the shocks are white noise in `L²`; the surplus is the `L²` moving average `(1 − θL)·1` | `TidyR6GaussianForecast.GaussEconomy.gaussLaw`, `TidyR6GaussianForecast.GaussEconomy.gauss_mean`, `TidyR6GaussianForecast.GaussEconomy.gauss_var`, `TidyR6GaussianForecast.GaussEconomy.gauss_integrable`, `TidyR6GaussianForecast.GaussEconomy.gauss_memLp`, `TidyR6GaussianForecast.GaussEconomy.memLp_eps`, `TidyR6GaussianForecast.GaussEconomy.memLp_coord`, `TidyR6GaussianForecast.GaussEconomy.memLp_surp`, `TidyR6GaussianForecast.GaussEconomy.isGaussianProcess_coord`, `TidyR6GaussianForecast.GaussEconomy.isGaussianProcess_surp`, `TidyR6GaussianForecast.GaussEconomy.gauss_whiteNoise`, `TidyR6GaussianForecast.GaussEconomy.toL2_surp` |
| Cochrane p. 102 ("`v_t = −ρ⁻¹ε_t`") | the value of debt `v_t = −θe_t` (the Hansen–Sargent value, `InvertibilityMeasure.hsCoeff_factor`) | `TidyR6GaussianForecast.GaussEconomy.debt` |
| Cochrane p. 102; A2 pp. 597–601 | i.i.d. `N(0, σ²)` shocks, `s_t = e_t − θe_{t−1}`, `θ = ρ⁻¹`, `\|θ\| > 1`: `a(ρ) = 0`; `E(s_{t+1}\|σ(s_t, s_{t−1}, …))` is the linear forecast, error variance `θ²σ²`; `e_t` is not a.e. a measurable function of the surplus history; given surpluses and debt the forecast is `−θe_t` with error variance `σ² < θ²σ²`; the conditional-expectation innovation is the Wold innovation | `TidyR6GaussianForecast.GaussEconomy.gaussian_noninvertible_condExp` |

## §4.3, p. 102, and Online Appendix A2 (2.18)–(2.21), pp. 597–601: Gaussian moving averages for every `a(L)` (TidyR6GaussianMA)

The i.i.d. `N(0, σ²)` shocks are unbounded, so they are realised in `L²` directly
(`TidyR6GaussianMA.shockG`), not through `InvertibilityMeasureL2.shockL2`.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 102; (4.1), p. 87; A2 p. 597 | the Gaussian shocks `e_t = ε_{φ(t)}` in `L²(ν^ℕ)`, white noise with variance `σ²`; the moving average `s_t = ∑_ka_ke_{t−k}` in `L²` and a measurable representative, square integrable, of mean zero, with that `L²` class, in the closed span of the coordinates | `TidyR6GaussianMA.shockG`, `TidyR6GaussianMA.shockG_whiteNoise`, `TidyR6GaussianMA.maL2`, `TidyR6GaussianMA.maRep`, `TidyR6GaussianMA.measurable_maRep`, `TidyR6GaussianMA.memLp_maRep`, `TidyR6GaussianMA.toL2_maRep`, `TidyR6GaussianMA.maL2_mem`, `TidyR6GaussianMA.integral_maRep` |
| Cochrane p. 102; A2 p. 601 | surpluses `a(L)e` and debt `b(L)e`, indexed by `ℤ ⊕ ℤ`, are jointly a Gaussian process; so is a single moving average | `TidyR6GaussianMA.isGaussianProcess_pair`, `TidyR6GaussianMA.isGaussianProcess_maRep` |
| Cochrane A2 (2.18), p. 600 | Gaussian shocks, `a(ρ) = 0`, `\|ρ\| < 1`: debt `v_t = c(L)e_t`, `c = hsCoeff a ρ`, is the mean-square ex-post present value `∑_jρʲs_{t+1+j}` | `TidyR6GaussianMA.debt_expost` |
| Cochrane A2 pp. 597, 601 | projections on equal subspaces agree (tool); the conditional-expectation forecast errors of `s_{t+1}` given `σ(s_t, s_{t−1}, …)` and given `σ(s_t, v_t, s_{t−1}, v_{t−1}, …)` have the linear-forecast variances, for every absolutely summable `a(L)`, `b(L)` | `TidyR6GaussianMA.starProjection_congr`, `TidyR6GaussianMA.condExp_mse_ma` |
| Cochrane A2 (2.21), p. 601; p. 102 | debt Granger-causes surpluses with conditional expectations for every absolutely summable `a(L)` with `a₀ ≠ 0`, `a(ρ) = 0`, `\|ρ\| < 1`: the error of `E(s_{t+1}\|σ(s, v history))` is strictly smaller than that of `E(s_{t+1}\|σ(s history))` | `TidyR6GaussianMA.gaussian_granger_ma` |
| Cochrane A2 pp. 597, 600 | for every absolutely summable `a(L)` (including `a(ρ) = 0`) the conditional-expectation innovations are the Wold innovations, white noise, a martingale-difference sequence, and `s_t = ∑_jc_je^{CE}_{t−j}` with no deterministic part | `TidyR6GaussianMA.gaussian_wold_ma` |
| Cochrane p. 102; A2 pp. 597–601 (link) | the MA(1) of `TidyR6GaussianForecast.GaussEconomy.gaussian_noninvertible_condExp` is the case `a = (1 − θL)·1`, `ρ = θ⁻¹`: the same `L²` process, the hypotheses hold, and the conditional mean-square errors are `θ²σ²` (surpluses) and `σ²` (surpluses and debt) | `TidyR6GaussianMA.ma1_special_case` |

## Online Appendix A2 §2.1 Present-value examples, pp. 603–604 (PresentValueExamples)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane A2 p. 603 | AR(1) dividends: `E_t∑_{j≥1}βʲd_{t+j} = βρ_dd_t/(1 − βρ_d)`, as a series of forecasts and as the expectation of the sum | `PresentValueExamples.dividend_pv`, `PresentValueExamples.dividend_pv_E` |
| Cochrane A2 p. 603 | permanent income: `c_{t+1} − c_t = rβ(y_{t+1} − ρ_yy_t)/(1 − βρ_y)` | `PresentValueExamples.pih_consumption` |
| Cochrane A2 p. 604; (4.5), p. 89 | AR(1) surplus: `v_t = ηs_t/(1 − ρη)` | `PresentValueExamples.surplus_pv_ar1` |
| Cochrane A2 p. 604 (E15) | `Δπ_{t+1} = −(s_{t+1} − ηs_t)/(1 − ρη)`; the printed `1 − βη` is right iff `β = ρ` | `PresentValueExamples.innov_infl_ar1`, `PresentValueExamples.printed_p604_iff` |

## Online Appendix A2 §2.2 The present value as a VAR tautology, (2.24)–(2.26), pp. 604–605 (VARIdentities)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane A2 (2.25), p. 605 | the flow identity holding in the VAR forces `a_v'(I − ρA) = (a_s + a_g − a_{rⁿ} + a_π)'A` | `VARIdentities.flow_restriction_of_identity` |
| Cochrane A2 (2.25)–(2.26), p. 605 (E18) | the flow restriction and the PV restriction are the same when `I − ρA` is invertible | `VARIdentities.one_sub_smul_mul_comm`, `VARIdentities.inv_one_sub_mul_comm`, `VARIdentities.flow_restriction_iff_pv` |
| Cochrane A2 p. 605 | iterating the flow identity forward gives the present value | `VARIdentities.pv_of_flow` |
| Cochrane A2 (2.24)–(2.26), p. 605; p. 102 | in a stable VAR satisfying the flow identity, the VAR present value converges and equals `v_t`: (2.26) "reduces to `v_t = v_t`" | `VARIdentities.var_pv_identity` |

## Online Appendix A2 §2.4 The permanent–transitory surplus, (2.27)–(2.34), pp. 607–611 (PermanentTransitory)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane A2 (2.27)–(2.30), pp. 607–608 | forecasts `E_ts_{t+k} = η_zᵏz_t + η_xᵏx_t`; each component is an AR(1); revisions; PV news `ε_z/(1 − ρη_z) + ε_x/(1 − ρη_x)` | `PermanentTransitory.pt_forecast`, `PermanentTransitory.isAR1_of_shocks`, `PermanentTransitory.pt_revision`, `PermanentTransitory.pt_pv_revision` |
| Cochrane A2 (2.31), p. 608 | the policy response `ε_z = −kε_x`; `ε_s = ρ(η_z − η_x)ε_x/D`; PV news `β_sε_s`; `β_s = 1/(1 − ρη_x)` gives `ε_z = 0`; `β_s = 0` gives no inflation | `PermanentTransitory.kcoef`, `PermanentTransitory.pt_eps_s`, `PermanentTransitory.pt_inflation_eq`, `PermanentTransitory.pt_eps_z_zero`, `PermanentTransitory.pt_no_inflation` |
| Cochrane A2 p. 608 | the MA coefficients on `ε_s`, `a_0 = 1`, revisions, "you can quickly verify `a(ρ) = β_s`" | `PermanentTransitory.ptCoeff`, `PermanentTransitory.pt_coeff_zero`, `PermanentTransitory.pt_revision_eps_s`, `PermanentTransitory.pt_aRho` |
| Cochrane A2 (2.32), p. 609 | the ARMA(2,1) form, coefficientwise and in the time domain; `β_s = 0` gives the numerator `1 − ρ⁻¹L`; the coefficients are those of `(1 − θL)/((1 − η_xL)(1 − η_zL))` | `PermanentTransitory.ptTheta`, `PermanentTransitory.pt_arma21_coeffs`, `PermanentTransitory.pt_arma21_time`, `PermanentTransitory.pt_theta_zero`, `PermanentTransitory.pt_coeff_eq_ar2ma1` |
| Cochrane A2 (2.33), pp. 609–610 | AR(2) impulse response and ARMA(2,1) coefficients; `a(ρ) = (1 − θρ)/((1 − η_xρ)(1 − η_zρ))`; fitted `(1 − ρ²)/((1 − η_xρ)(1 − η_zρ))`; with `ρ = η_z`, "exactly the wrong AR(1)" | `PermanentTransitory.ar2Impulse`, `PermanentTransitory.ar2ma1Coeff`, `PermanentTransitory.ar2ma1_genFn`, `PermanentTransitory.pt_fitted_aRho`, `PermanentTransitory.pt_fit_ar1` |
| Cochrane A2 (2.32)–(2.33), pp. 609–610 (Hilbert space) | with `β_s = 0` the Wold innovation gives `(1 − η_xL)(1 − η_zL)s = (1 − ρL)w`, variance `σ²/ρ²`, structural shock unrecoverable; with `ρ = η_z`, `s_t − η_xs_{t−1} = w_t` | `PermanentTransitory.HilbertPT.summable_abs_ptCoeff`, `PermanentTransitory.HilbertPT.pt_wold`, `PermanentTransitory.HilbertPT.pt_wold_ar1` |
| Cochrane A2 p. 611 (E16) | `v_t = E_t∑_{j≥0}ρʲs_{t+j} = z_t/(1 − ρη_z) + x_t/(1 − ρη_x)`; the printed sum `∑_{j≥1}ρ^{j−1}s_{t+j}` is `(v_t − s_t)/ρ`, a different number | `PermanentTransitory.pt_value`, `PermanentTransitory.pt_value_printed`, `PermanentTransitory.pt_value_printed_eq`, `PermanentTransitory.printed_value_ne` |
| Cochrane A2 (2.34), p. 611 (E16) | the VAR in surplus and debt, for the formula and for the processes; eigenvalues `η_x`, `η_z`; the printed `v` violates (2.34) | `PermanentTransitory.pt_var`, `PermanentTransitory.pt_var_process`, `PermanentTransitory.pt_var_tr_det`, `PermanentTransitory.printed_value_var_fails` |
| Cochrane A2 p. 611 | the surplus-on-debt coefficient is positive although surpluses are exogenous; debt-on-debt `ρ⁻¹ > 1` with stable eigenvalues; the structural shocks are recoverable from the VAR residuals | `PermanentTransitory.pt_coeff_pos`, `PermanentTransitory.pt_debt_coeff_gt_one`, `PermanentTransitory.pt_shocks_recoverable` |

## Links between the modules (Links)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 88, (4.3); A2 (2.3), p. 595 | the ARMA family at `φ = 0` is the §4.2 MA(1), at `θ = 0` the AR(1); the two closed forms of `a(z)` agree | `Links.armaCoeff_zero_eq_ma1Coeff`, `Links.armaCoeff_ar1`, `Links.gen_armaCoeff_ar1`, `Links.gen_armaCoeff_zero` |
| Cochrane (4.17), p. 104; (4.1), p. 87 | VAR shock condition plus adaptedness = componentwise MDS | `Links.isMDSNat_iff_shockMDS` |
| Cochrane (4.1), p. 87; A2 p. 600 | the zero-presample moving average is a (4.1) moving average in an MDS on `ℤ` | `Links.presample`, `Links.presample_succ`, `Links.isMDS_presample`, `Links.abs_presample_le`, `Links.maSeries_isMA` |
| Cochrane (4.2), p. 87; A2 (2.19), p. 601 | `∑ρʲΔs_{t+1+j} = a(ρ)e_{t+1}` for the A2 moving average; the Hansen–Sargent forecasts revise by `a(ρ)e_{t+1}` | `Links.innov_PV_maSeries`, `Links.hansenSargent_innov` |
| Cochrane (4.2), p. 87 | the HRS identity for any surplus in revision form | `Links.innov_infl_of_revision` |
| Cochrane A2 (2.3), p. 595 | ARMA(1,1) surplus ⇒ `Δπ = −β_sε` | `Links.arma11_innov_infl` |
| Cochrane p. 102; A2 (2.9)–(2.13) | MA(1) revision form; `Δπ = −(1 + cρ)ε`; `θ = ρ⁻¹` ⇒ no inflation | `Links.ma1_revision`, `Links.ma1_innov_infl`, `Links.ma1_innov_infl_repay` |
| Cochrane A2 (2.30)–(2.31), p. 608; p. 96 | the permanent–transitory PV news via the AR(1) news formula; `Δπ = −β_sε_s` | `Links.pt_pv_revision_via_ar1`, `Links.pt_innov_infl` |
| Cochrane p. 101; A2 (2.22)–(2.23); (3.19) | with the flow identity ex post, the present value under any information set converges to `E^I_tv_t`, hence to `v_t` iff `v_t ∈ I_t` | `Links.condDown_flow` |

## Measure-theoretic expectations: the copied core (ExpectationsMeasure, ExpectationsMeasureIID)

Copied verbatim (namespace renamed) from the `ObservationalEquivalence` project, where it was
built; its docstrings cite Cochrane (2023), Ch. 2. Statements hold almost everywhere unless marked
exact.

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane Ch. 2, pp. 29–30 (shared core) | a probability space with a filtration; `E_t x = μ[x \| 𝓕_t]` is Mathlib's `condExp`; bounded random variables and processes | `ExpectationsMeasure.MeasExpectationSystem`, `ExpectationsMeasure.MeasExpectationSystem.μ`, `ExpectationsMeasure.MeasExpectationSystem.E`, `ExpectationsMeasure.MeasExpectationSystem.BddRV`, `ExpectationsMeasure.MeasExpectationSystem.BddProc` |
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
| Chapter 4 throughout | the expectation axioms, adapted and AR(1) processes, `E_t(E_tx) = E_tx`, `E_t` preserves bounds, AR(1) forecasts `E_tu_{t+k} = ηᵏu_t`, `E_t` of a geometrically dominated series, bounded processes, pull-out (a hypothesis in the exact model and the SDF valuation) | `ExpectationSystem`, `ExpectationSystem.Adapted`, `ExpectationSystem.IsAR1`, `ExpectationSystem.E_E_self`, `ExpectationSystem.abs_E_le`, `ExpectationSystem.ar1_iterate`, `ExpectationSystem.E_tsum`, `ExpectationSystem.PullOut`, `BoundedProc` |
| Chapter 4 throughout | a variable known at `s` is known at every later date; `E_t` commutes with a series dominated by a summable sequence | `ForwardSolution.E_of_known`, `ForwardSolution.E_tsum_dom` |
| counterexamples | the coin-flip tree and its shock | `ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E`, `ExpectationsFiniteTree.coinSystem`, `ExpectationsFiniteTree.coinShock`, `ExpectationsFiniteTree.firstHeads`, `ExpectationsFiniteTree.coinSystem_E0_firstHeads` |
| A2 p. 598, p. 611 | trace, determinant and the Schur–Cohn condition for `2 × 2` VAR matrices | `SchurStable`, `tr2`, `det2` |
| shared core, not used by Chapter 4 | the forward solution and its determinacy theory, carried for the later Cochrane projects | `ExpectationSystem.forwardSeries`, `ForwardSolution.existsUnique_bounded`, `schurStable_iff_roots` |
