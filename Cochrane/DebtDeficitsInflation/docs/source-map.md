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
and the measure-theoretic instance of conditioning down. `Δ_{t+1}` is the innovation operator
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

## Shared tools

| Book | Claim | Lean |
| --- | --- | --- |
| Chapter 4 throughout | the expectation axioms, adapted and AR(1) processes, `E_t(E_tx) = E_tx`, `E_t` preserves bounds, AR(1) forecasts `E_tu_{t+k} = ηᵏu_t`, `E_t` of a geometrically dominated series, bounded processes, pull-out (a hypothesis in the exact model and the SDF valuation) | `ExpectationSystem`, `ExpectationSystem.Adapted`, `ExpectationSystem.IsAR1`, `ExpectationSystem.E_E_self`, `ExpectationSystem.abs_E_le`, `ExpectationSystem.ar1_iterate`, `ExpectationSystem.E_tsum`, `ExpectationSystem.PullOut`, `BoundedProc` |
| Chapter 4 throughout | a variable known at `s` is known at every later date; `E_t` commutes with a series dominated by a summable sequence | `ForwardSolution.E_of_known`, `ForwardSolution.E_tsum_dom` |
| counterexamples | the coin-flip tree and its shock | `ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E`, `ExpectationsFiniteTree.coinSystem`, `ExpectationsFiniteTree.coinShock`, `ExpectationsFiniteTree.firstHeads`, `ExpectationsFiniteTree.coinSystem_E0_firstHeads` |
| A2 p. 598, p. 611 | trace, determinant and the Schur–Cohn condition for `2 × 2` VAR matrices | `SchurStable`, `tr2`, `det2` |
| shared core, not used by Chapter 4 | the forward solution and its determinacy theory, carried for the later Cochrane projects | `ExpectationSystem.forwardSeries`, `ForwardSolution.existsUnique_bounded`, `schurStable_iff_roots` |
