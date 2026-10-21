# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, "Observational equivalence"
(pp. 495–510), with the precise claims of Chapters 23–24 (pp. 512–523) and of Online Appendix
Chapter 2, "How not to test fiscal theory" (pp. 593–611). Each formal claim is listed with its
Lean name, relative to the namespace `Cochrane.ObservationalEquivalence`. Page numbers are book
pages. The book has no labelled propositions, so rows are keyed by equation number, section, the
survey's theorem names (OE-1, OE-2, NI-1 to NI-3, LR, RG) or page. Rows follow the book: the
valuation equation and the starred model of §22.1, observational equivalence, money regimes,
non-identification, the asset-pricing analogy of §22.2.4, the regressions and Granger causality of
§22.3, the Leeper regions of §22.7 and Chapter 23, Markov switching in Chapter 24, the
present-value identities of the Online Appendix, then the links between modules and the shared
tools.

The linear results hold for an arbitrary `ExpectationSystem`, so under perfect foresight and
under uncertainty. An *admissible* equilibrium has adapted, bounded inflation and debt satisfying
the transversality condition (`StarredModel.Admissible`); *unique* means the target is the only
admissible equilibrium (`Equivalence.UniqueEqm`). Survey error codes E12–E19 are those of the
survey of Chapters 20–25 (`notes/survey_cochrane_ch20-25.md`), and E6 that of the survey of
Chapters 11–19; see [corrections](corrections.md). Rows marked "restated" reproduce results
proved in an earlier project, with the namespace adapted.

## §22.1 The valuation equation, pp. 495–497; (22.2) (Valuation)

| Book | Claim | Lean |
| --- | --- | --- |
| (22.2), p. 495; (16.20), p. 373 | the Fisher equation `i_t = E_tπ_{t+1}` and the flow condition `ρv_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` | `Valuation.Fisher`, `Valuation.Flow` |
| (22.1), p. 495 | surprises `x_{t+1} − E_tx_{t+1}` are unforecastable at every horizon and equal the innovation `ΔE_{t+1}x_{t+1}` of an adapted process | `Valuation.surprise`, `Valuation.E_surprise`, `Valuation.E_surprise_later`, `Valuation.surprise_eq_innov` |
| (22.2), p. 495; (16.22), p. 373; (22.11), p. 501 | with the Fisher equation the flow condition is `ρv_{t+1} = v_t − ΔE_{t+1}π_{t+1} − s̃_{t+1}`, or `ρv_{t+1} = v_t + r_{t+1} − s̃_{t+1}` with the ex-post real return, whose expectation is zero at every horizon | `Valuation.flow_iff_surprise`, `Valuation.realReturn`, `Valuation.flow_iff_realReturn`, `Valuation.E_realReturn` |
| p. 495 | iterating (22.2) forward, ex post and under `E_t` | `Valuation.telescope`, `Valuation.telescope_E` |
| p. 495 ("iterating (22.2) forward and imposing the transversality condition") | the transversality condition `ρᵀE_tv_{t+T} → 0` holds iff the valuation equation holds at every date | `Valuation.TVC`, `Valuation.valuation_of_tvc`, `Valuation.tvc_of_valuation`, `Valuation.tvc_iff_valuation` |
| p. 495 | the present value of bounded surpluses: summable, bounded by `M/(1 − \|ρ\|)`, `v_t = ∑ρʲE_ts̃_{t+1+j} = E_t∑ρʲs̃_{t+1+j}`, first-term split | `Valuation.pvE`, `Valuation.pvE_summable`, `Valuation.abs_pvE_le`, `Valuation.valuation_tsum`, `Valuation.E_pvExPost`, `Valuation.valuation_E_exPost`, `Valuation.pvE_succ_split` |
| p. 495; (16.24), p. 373 | `ΔE_{t+1}π_{t+1} = −ΔE_{t+1}∑ρʲs̃_{t+1+j}` | `Valuation.unexpected_inflation`, `Valuation.unexpected_inflation_news` |
| p. 495 | bounded debt satisfies the transversality condition; the condition is preserved by sums and differences | `Valuation.tvc_of_bounded`, `Valuation.tvc_sub`, `Valuation.tvc_add` |

## The starred model: (16.20)–(16.24), p. 373; (22.1), p. 495; (22.7)–(22.11), p. 501 (StarredModel)

| Book | Claim | Lean |
| --- | --- | --- |
| (22.1)–(22.2), p. 495 | a path of observables `(π, i, v, s̃)` | `StarredModel.Outcome`, `StarredModel.outcome_ext` |
| (16.21), p. 373; (22.10), p. 501 | the target is consistent: it obeys the Fisher equation and the flow condition; equivalently (22.10) | `StarredModel.Consistent`, `StarredModel.consistent_iff_eq22_10` |
| p. 495; p. 508 ("the rule against nominal explosions") | admissibility: adapted, bounded inflation, transversality condition for debt | `StarredModel.Admissible` |
| (16.20)–(16.22), p. 373; (22.1), p. 495 | the `(φ, γ)` starred system with the date-0 condition `ρv_0 + π_0 = ρv*_0 + π*_0` | `StarredModel.Eqm` |
| (22.8)–(22.9), p. 501; (24.2), p. 520 | `s̃*_{t+1} = αv*_t + u_{s,t+1}` and `i*_t = θπ*_t + u_{i,t}`; the rules then read (22.8) and (22.9) | `StarredModel.StarredSurplus`, `StarredModel.ThetaRule`, `StarredModel.eq22_8`, `StarredModel.eq22_9` |
| (22.10), p. 501, with (23.4), p. 512 | target debt `ρv*_{t+1} = (1 − α)v*_t − ΔE_{t+1}π*_{t+1} − u_{s,t+1}` | `StarredModel.eq23_4_starred` |
| §16.6, p. 373; p. 495 ("in equilibrium, starred variables equal their unstarred counterparts") | the target is an equilibrium for every `(φ, γ)` | `StarredModel.starred_eqm` |
| (16.23)–(16.24), p. 373 | on the target the observables obey equations with neither `φ` nor `γ` | `StarredModel.observables_eq16_23_24` |
| (22.1), p. 495 | the deviation equations `E_te_{t+1} = φe_t`, `ρd_{t+1} = (1 − γ)d_t − ΔE_{t+1}e_{t+1}`, `ρd_0 + e_0 = 0`; every solution gives an equilibrium and every equilibrium arises this way | `StarredModel.deviation_dynamics`, `StarredModel.lag`, `StarredModel.ofDev`, `StarredModel.ofDev_eqm`, `StarredModel.eq_ofDev`, `StarredModel.ofDev_zero` |
| p. 495 | admissibility passes between paths and their deviations | `StarredModel.dev_admissible`, `StarredModel.ofDev_admissible` |
| p. 497 ("an equilibrium condition for all of these models") | every admissible equilibrium of every `(φ, γ)` system satisfies the valuation equation and the unexpected-inflation formula | `StarredModel.valuation_all_regimes` |
| (22.3)–(22.6), p. 500; (23.1)–(23.4), p. 512 | the unstarred Leeper model, with the `ρ` that (22.6) omits (E13), and inherited debt `ρv_0 + π_0 = K` | `StarredModel.LeeperEqm` |
| p. 512, after (23.4) | `ρv_{t+1} = (1 − γ)v_t − ΔE_{t+1}π_{t+1} − u_{s,t+1}`; `E_tπ_{t+1} = φπ_t + u_{i,t}` | `StarredModel.eq23_4`, `StarredModel.leeper_expected_inflation` |
| §22.3, p. 500 | the Leeper model is the starred system around itself, for every `(φ′, γ′)` | `StarredModel.leeper_is_starred` |
| (24.1), p. 520 (E14) | the printed rule is the starred rule with target rate `θπ*_t + u_{i,t}` and off-target coefficient `θ + φ` | `StarredModel.rule24_1_printed` |

## OE-1: observational equivalence of interest-rate regimes, §§22.1–22.2, pp. 495–497; §22.7, pp. 508–509 (Equivalence)

| Book | Claim | Lean |
| --- | --- | --- |
| box p. 495; §16.6, p. 373 | the target is an admissible equilibrium for every `(φ, γ)`; uniqueness and the determinate set | `Equivalence.starred_admissible_eqm`, `Equivalence.UniqueEqm`, `Equivalence.Determinate` |
| (22.1), p. 495 | inflation on target forces debt on target, and conversely | `Equivalence.d_zero_of_e_zero`, `Equivalence.e_zero_of_d_zero` |
| (23.4), p. 512; p. 513 | the debt deviation is an AR(1) with `ρᵀE_td_{t+T} = (1 − γ)ᵀd_t`; it satisfies the transversality condition when `\|1 − γ\| < 1`, and only if it is zero when `\|1 − γ\| ≥ 1` | `Equivalence.isAR1_of_dyn`, `Equivalence.pow_mul_E_ar1`, `Equivalence.tvc_of_ar1`, `Equivalence.zero_of_ar1_tvc` |
| p. 495; §§16.5–16.6, pp. 371–373 (E12) | `\|φ\| > 1` gives uniqueness for every `γ`; `γ ≤ 0` or `γ ≥ 2` gives uniqueness for every `φ`; so does the book's `γ = 0` | `Equivalence.unique_of_active_money`, `Equivalence.unique_of_active_fiscal`, `Equivalence.unique_of_determinate`, `Equivalence.unique_of_gamma_zero` |
| p. 508 (E19) | double-active policy `φ > 1`, `γ = 0` is uniquely determinate in the starred form | `Equivalence.unique_double_active` |
| pp. 508–509 (double passive, E12) | for `\|φ\| ≤ 1`, `0 < γ < 2` the date-0 jump family is an uncountable set of admissible equilibria; the target is not unique | `Equivalence.famE`, `Equivalence.famD`, `Equivalence.famPath`, `Equivalence.famPath_eqm`, `Equivalence.famPath_admissible`, `Equivalence.famPath_injective`, `Equivalence.continuum_double_passive`, `Equivalence.not_unique_of_passive` |
| pp. 495, 501, 508–509 (E12) | the target is unique iff `\|φ\| > 1 ∨ γ ≤ 0 ∨ γ ≥ 2` | `Equivalence.unique_iff`, `Equivalence.determinate_iff` |
| p. 495 (E12) | counterexamples to the printed labels: `φ = −2`, `γ = 1` and `φ = 1/2`, `γ = 3` are determinate | `Equivalence.printed_phi_lt_one_determinate`, `Equivalence.printed_gamma_pos_determinate` |
| pp. 508–509 ("even if the ingredient is sunspots") | every bounded martingale-difference sunspot gives an equilibrium; on the coin-flip tree such equilibria are genuinely random; under perfect foresight every equilibrium is a date-0 jump path | `Equivalence.sunspot_eqm`, `Equivalence.coinShock_adapted`, `Equivalence.coinShock_bounded`, `Equivalence.coin_sunspot_eqm`, `Equivalence.perfectForesight_eq_famPath` |
| p. 497 (the recipe) | any path obeying the common equilibrium conditions is the unique equilibrium of every determinate starred system around itself | `Equivalence.recipe` |
| p. 496 ("any time series produced by an active-money/passive fiscal regime can be produced by an active-fiscal/passive-money regime and vice versa") | an equilibrium of any `(φ₁, γ₁)` system is the unique equilibrium of every determinate `(φ₂, γ₂)` system; Leeper-model equilibria are active-fiscal starred equilibria | `Equivalence.oe_both_ways`, `Equivalence.leeper_recipe` |
| (16.10), p. 370; (16.15)–(16.18), p. 371 | the new-Keynesian AR(1) solution `π_t = −u_t/(φ − η)`, unique for `\|φ\| > 1`, and its observables | `Equivalence.nk_solution`, `Equivalence.nk_unique`, `Equivalence.nk_observables` |
| §16.6, p. 372 | the fiscal-theory equilibrium with `θ = η` and fiscal shock `ε/(φ − η)` is the same process; in the new-Keynesian equilibrium the valuation equation forces this "passive" fiscal news | `Equivalence.ftpl_eq_nk`, `Equivalence.nk_passive_fiscal_news` |

## OE-2: money-supply regimes, §22.1, pp. 495–496; §22.7, p. 508 (MoneyRegimes)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 496 | the present value `∑βʲs_{t+j}` of bounded surpluses: summable, `PV_t = s_t + βPV_{t+1}` | `MoneyRegimes.pv`, `MoneyRegimes.pv_summable`, `MoneyRegimes.pv_succ` |
| pp. 495–496 | the money model: `P > 0`, `M_tV_t = P_ty_t`, `W_t/P_t = ∑βʲs_{t+j}` | `MoneyRegimes.Eqm` |
| p. 496 | the valuation equation implies the flow constraint `W_t = P_ts_t + Q_tW_{t+1}`, `Q_t = βP_t/P_{t+1}` | `MoneyRegimes.flow_of_valuation` |
| p. 496 (active money) | `M` determines `P = MV/y`; passive surpluses complete an equilibrium for every money supply | `MoneyRegimes.activeMoney_price`, `MoneyRegimes.activeMoney_exists` |
| p. 496 (active fiscal) | surpluses and nominal debt determine `P_t = W_t/PV_t`, and money follows | `MoneyRegimes.activeFiscal_unique`, `MoneyRegimes.activeFiscal_exists` |
| p. 496 (OE-2) | an equilibrium path is the unique equilibrium of both regimes | `MoneyRegimes.oe2` |
| p. 508 ("fixes `M` and … surpluses at an inconsistent value") | with `M`, `s`, `W` fixed an equilibrium exists iff `W_ty_t/(M_tV_t) = PV_t`; halving `M` leaves none | `MoneyRegimes.inconsistent_iff`, `MoneyRegimes.halve_money_no_eqm` |

## Non-identification, §22.1, p. 496; §22.3, pp. 500–502; §16.5, p. 371 (NonIdentification)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 496 (NI-1) | the equilibrium set; on the determinate set it is the same singleton for every `(φ, γ)` | `NonIdentification.EqmSet`, `NonIdentification.eqmSet_eq_singleton`, `NonIdentification.eqmSet_const_on_determinate` |
| p. 496; p. 371 ("the likelihood function does not involve `φ`") | every statistic of the observed path is constant on the determinate set; the observed path is an equilibrium for every `(φ, γ)`; no estimator recovers `(φ, γ)` | `NonIdentification.statistic_independent`, `NonIdentification.target_mem_eqmSet`, `NonIdentification.not_identified` |
| (22.7)–(22.8), p. 501 (NI-2) | in equilibrium `i_t = θπ_t + u_{i,t}` and `E_tπ_{t+1} = θπ_t + u_{i,t}`, whatever `φ` | `NonIdentification.eqm_rate_theta`, `NonIdentification.eqm_inflation_theta` |
| p. 501 ("`θ` can, in principle, be measured") | a population moment condition recovers `θ`; the specification `i_t = φπ_t + u_{i,t}` imposes `φ = θ` | `NonIdentification.coef_from_moment`, `NonIdentification.regression_identifies_theta`, `NonIdentification.spec_forces_phi_eq_theta` |
| p. 501 ("`θ < 1` if we wish stationary solutions", E12) | inflation stays bounded for all bounded inputs iff `\|θ\| < 1` | `NonIdentification.stationary_iff` |
| (22.8), p. 501 | the `θ`-target; any `\|θ\| < 1` combines with any `\|φ\| > 1` | `NonIdentification.thetaTarget`, `NonIdentification.thetaTarget_ok`, `NonIdentification.theta_target_unique` |
| (22.9), p. 501 (NI-3) | in equilibrium `s̃_{t+1} = αv_t + u_{s,t+1}`; regressions recover `α`; (22.5) imposes `γ = α` | `NonIdentification.eqm_surplus_alpha`, `NonIdentification.regression_identifies_alpha`, `NonIdentification.spec_forces_gamma_eq_alpha` |
| §16.5, p. 371; §22.3, pp. 500–502 | reverse engineering: any path obeying the Fisher equation and the flow condition is a Leeper equilibrium for every `(φ, γ)`; the disturbances differ by `(φ₂ − φ₁)π_t` | `NonIdentification.reverse_engineer_rule`, `NonIdentification.revUi`, `NonIdentification.revUs`, `NonIdentification.reverse_engineer_leeper`, `NonIdentification.rev_disturbances_differ` |
| p. 502 | the s-shaped surplus from `α > 0` or from an s-shaped disturbance with `α = 0` | `NonIdentification.sshape_two_ways`, `NonIdentification.leeper_sshape_two_ways` |
| p. 502 | an explicit s-shaped response: it obeys the flow condition and (22.9), is positive on impact and negative afterwards for `0 < α < 1`, and has zero present value for `0 < α < 2` | `NonIdentification.irfV`, `NonIdentification.irfS`, `NonIdentification.impulse`, `NonIdentification.irf_flow`, `NonIdentification.irf_surplus`, `NonIdentification.irf_sshape`, `NonIdentification.irf_pv_zero` |

## §22.2.4 The same situation elsewhere, pp. 498–499 (AssetPricingOE, PresentValueIdentity)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 498 | `p = ∑π_su′(c_s)x_s`; "rational" and "behavioural" pricing are observationally equivalent; only the product `πm` is identified | `AssetPricingOE.price`, `AssetPricingOE.rational_behavioral_equiv`, `AssetPricingOE.behavioral_pos`, `AssetPricingOE.same_prices_iff` |
| pp. 498–499 | the Harrison–Kreps risk-neutral measure | `AssetPricingOE.riskNeutral` |
| p. 499 | portfolios, arbitrage and strictly positive discount factors; a discount factor rules out arbitrage | `AssetPricingOE.cost`, `AssetPricingOE.payoff`, `AssetPricingOE.IsArbitrage`, `AssetPricingOE.NoArbitrage`, `AssetPricingOE.IsSDF`, `AssetPricingOE.cost_eq_of_sdf`, `AssetPricingOE.noArbitrage_of_sdf` |
| p. 499 ("absent arbitrage, there is a discount factor") | the finite-state discount-factor theorem, by Hahn–Banach separation; the price in expectation form under any full-support beliefs | `AssetPricingOE.gains`, `AssetPricingOE.simplexSet`, `AssetPricingOE.convex_simplexSet`, `AssetPricingOE.functional_eq_sum`, `AssetPricingOE.exists_sdf_of_noArbitrage`, `AssetPricingOE.ftap`, `AssetPricingOE.sdf_expectation_form` |
| p. 499 | the flow constraint with one-period nominal debt; the ex-post discount factor `Λ_{t+1}/Λ_t = Q_tP_{t+1}/P_t` is positive and prices the bond exactly | `PresentValueIdentity.DebtFlow`, `PresentValueIdentity.sdfStep`, `PresentValueIdentity.sdf`, `PresentValueIdentity.sdf_pos`, `PresentValueIdentity.sdf_prices_bond`, `PresentValueIdentity.sdf_flow` |
| p. 499, displayed equation | `B_{t−1}/P_t = ∑(Λ_{t+j}/Λ_t)s_{t+j}` under the transversality condition, and conversely; the `E_t` form for any `ExpectationSystem` | `PresentValueIdentity.sdf_valuation_finite`, `PresentValueIdentity.sdf_valuation_tendsto`, `PresentValueIdentity.sdf_valuation_hasSum`, `PresentValueIdentity.tvc_of_sdf_valuation`, `PresentValueIdentity.sdf_valuation_E` |

## Theorem RG: surpluses on debt, §22.3, p. 501; §24.1, p. 519; Online Appendix p. 593 (MACovariance, SurplusRegression)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 501; A2 p. 593 | white-noise shocks for a covariance form; finite moving averages and their autocovariances | `MACovariance.WhiteNoise`, `MACovariance.maProc`, `MACovariance.autocov` |
| p. 501 | covariance is the inner product of shifted coefficient vectors; variance; stationarity; zero variance iff all coefficients vanish | `MACovariance.cov_maProc`, `MACovariance.var_maProc`, `MACovariance.cov_maProc_stationary`, `MACovariance.var_maProc_eq_zero_iff` |
| p. 501 (consistency of the hypotheses) | the coordinate inner product on `ℤ →₀ ℝ` and its unit vectors are white noise | `MACovariance.finsuppCov`, `MACovariance.finsuppNoise`, `MACovariance.finsuppNoise_whiteNoise` |
| p. 501 (the Kac–Murdock–Szegő kernel) | the kernel `ρ^{\|k−l\|}`, its quadratic form, tail sums and LDL form, with their recursions | `MACovariance.kmsKernel`, `MACovariance.kmsForm`, `MACovariance.kmsTail`, `MACovariance.kmsLDL`, `MACovariance.kmsKernel_symm`, `MACovariance.kmsKernel_succ`, `MACovariance.kmsTail_zero_succ`, `MACovariance.kmsTail_shift`, `MACovariance.kmsTail_succ`, `MACovariance.kmsTail_of_le`, `MACovariance.kmsForm_succ`, `MACovariance.kmsLDL_succ` |
| p. 501 (RG) | `∑ρ^{\|k−l\|}x_kx_l = y_0² + (1 − ρ²)∑y_m²`; positive semidefinite for `ρ² ≤ 1`, definite for `ρ² < 1`; as a Mathlib `Matrix.PosDef` | `MACovariance.kmsForm_eq_ldl`, `MACovariance.kmsForm_nonneg`, `MACovariance.kmsForm_eq_zero_iff`, `MACovariance.kmsForm_pos`, `MACovariance.kmsMatrix`, `MACovariance.kmsMatrix_quad`, `MACovariance.kmsMatrix_posDef` |
| p. 501; A2 pp. 593, 602 | agents' information, the exogenous surplus `s_t = a(L)ε_t`, the value of debt `v_t = E_t∑ρʲs_{t+1+j}`, its coefficients, the regression coefficient, white noise, `a(ρ)` | `SurplusRegression.ShockInfo`, `SurplusRegression.surplus`, `SurplusRegression.valueOfDebt`, `SurplusRegression.vCoeff`, `SurplusRegression.regCoeff`, `SurplusRegression.IsIID`, `SurplusRegression.aRho` |
| p. 501; A2 (2.22), p. 602 | `v_t = b(L)ε_t` with `b_m = ∑ρʲa_{m+1+j}`, the Kac–Murdock–Szegő tail sums | `SurplusRegression.E_maProc`, `SurplusRegression.abs_maProc_le`, `SurplusRegression.shifted_sum`, `SurplusRegression.value_eq_maProc`, `SurplusRegression.vCoeff_of_le`, `SurplusRegression.vCoeff_eq_kmsTail` |
| p. 501 | `Cov(s_{t+1}, v_t) = ∑a_{k+1}b_k`, `Var(v_t) = ∑b_k²` | `SurplusRegression.cov_surplus_value`, `SurplusRegression.var_value` |
| p. 501, §24.1 p. 519, A2 p. 593 (RG) | `2Cov(s_{t+1}, v_t) = ∑_{k≥1}a_k² + ∑_{k,l≥1}ρ^{\|k−l\|}a_ka_l`; covariance and regression coefficient are positive iff the surplus is not white noise | `SurplusRegression.two_sum_eq_ldl`, `SurplusRegression.two_cov_eq_kms`, `SurplusRegression.sum_sq_pos_iff`, `SurplusRegression.cov_pos_iff`, `SurplusRegression.regCoeff_pos_iff` |
| A2 p. 593 | a white-noise surplus gives `v ≡ 0` and zero covariance | `SurplusRegression.iid_value_zero`, `SurplusRegression.iid_cov_zero` |
| §24.1, p. 519 (E16) | the book's claim with `a(ρ) < 1` is true; the MA(1) `(1, 1)` has `a(ρ) > 1` and a positive coefficient | `SurplusRegression.book_claim_aRho_lt_one`, `SurplusRegression.ma1Coeff`, `SurplusRegression.ma1_aRho_gt_one`, `SurplusRegression.ma1_regCoeff_pos` |
| A2 p. 604; p. 501; p. 519 (E16) | AR(1): `v_t = ηs_t/(1 − ρη)`, `Cov = η²σ²/(1 − ρη)`, `γ̂ = 1 − ρη`, though `a(ρ) = 1/(1 − ρη) > 1` | `SurplusRegression.ar1_value`, `SurplusRegression.ar1_cov`, `SurplusRegression.ar1_regCoeff`, `SurplusRegression.ar1_aRho_gt_one` |
| p. 501 (infinite moving averages) | truncation, the infinite coefficients `b_m`, covariance and Kac–Murdock–Szegő form, with bounds and summability | `SurplusRegression.truncSeq`, `SurplusRegression.bInf`, `SurplusRegression.covInf`, `SurplusRegression.kmsInf`, `SurplusRegression.abs_kmsKernel_le`, `SurplusRegression.abs_tsum_le_of_le`, `SurplusRegression.tail_abs`, `SurplusRegression.abs_le_tsum_abs`, `SurplusRegression.abs_truncSeq_le`, `SurplusRegression.tendsto_truncSeq`, `SurplusRegression.bInf_bound`, `SurplusRegression.covInf_summable`, `SurplusRegression.kmsInf_summable`, `SurplusRegression.sq_summable`, `SurplusRegression.truncSeq_support` |
| p. 501 | the finite identity for truncations and its limit by dominated convergence | `SurplusRegression.bInf_trunc`, `SurplusRegression.covInf_trunc`, `SurplusRegression.sq_trunc`, `SurplusRegression.kmsInf_trunc`, `SurplusRegression.two_finite_eq`, `SurplusRegression.tendsto_covInf_trunc`, `SurplusRegression.tendsto_sq_trunc`, `SurplusRegression.tendsto_kmsInf_trunc` |
| p. 501, §24.1 p. 519 (RG, infinite MA) | `2∑x_mb_m = ∑x_k² + ∑∑ρ^{\|k−l\|}x_kx_l`; the infinite form is semidefinite, bounded below by `(1 − ρ²)/(1 + \|ρ\|)²∑x_k²`, and definite for `\|ρ\| < 1`; covariance and regression coefficient positive iff not white noise | `SurplusRegression.two_covInf_eq`, `SurplusRegression.kmsForm_lower`, `SurplusRegression.kmsInf_nonneg`, `SurplusRegression.kmsInf_lower`, `SurplusRegression.kmsInf_pos`, `SurplusRegression.covInf_pos_iff`, `SurplusRegression.bInf_abs_summable`, `SurplusRegression.bInf_sq_summable`, `SurplusRegression.regInf_pos_iff` |
| p. 501, §24.1 p. 519 | the genuine covariances of the lag-`N` truncations converge to the infinite-MA covariance | `SurplusRegression.cov_trunc_tendsto` |
| A2 p. 604 | AR(1) as a corollary: `b_m = η^{m+1}/(1 − ρη)`, covariance `η²σ²/(1 − ρη)` | `SurplusRegression.ar1_bInf`, `SurplusRegression.ar1_covInf` |
| p. 501 (RG is not vacuous) | a certainty-equivalent model with bounded white-noise shocks satisfying every hypothesis, where the MA(1) gives a positive coefficient | `SurplusRegression.truncPath`, `SurplusRegression.truncPath_trunc_le`, `SurplusRegression.truncPath_le_trunc`, `SurplusRegression.truncSystem`, `SurplusRegression.clampShock`, `SurplusRegression.clampShock_bounded`, `SurplusRegression.clampShock_info`, `SurplusRegression.clampShock_linearIndependent`, `SurplusRegression.shockCoord`, `SurplusRegression.shockCoord_shock`, `SurplusRegression.truncCov`, `SurplusRegression.clampShock_whiteNoise`, `SurplusRegression.truncModel_regCoeff_pos` |

## Granger causality and information, §22.3, pp. 501–502; Online Appendix (2.22)–(2.23), p. 602 (Granger)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 501, footnote 1 (restated from the `DebtDeficitsInflation` project) | the VAR `z_{t+1} = Az_t + ε_{t+1}` with unforecastable shocks; `E_tz_{t+k} = Aᵏz_t`; `ΔE_{t+1}z_{t+1+k} = Aᵏε_{t+1}` | `Granger.IsVAR`, `Granger.ShockMDS`, `Granger.var_forecast`, `Granger.var_innov` |
| p. 501, footnote 1 ("surprises to `x` forecast … surprises to `y`") | with orthonormal shocks the covariance of the revision of `y` with the `x`-shock is `(Aᵏ)_{yx}` | `Granger.cov_innov_shock` |
| p. 501, footnote 1 | one-step and impulse-response non-causality; the latter is "no `h`-step forecast loads on `x`" and implies the former | `Granger.OneStepNonCausal`, `Granger.IRFNonCausal`, `Granger.irf_nonCausal_iff_forecast`, `Granger.irf_imp_oneStep` |
| p. 501, footnote 1 ("Equivalently …", E17) | the two coincide in a bivariate VAR; in the chain `x → w → y`, `A_{yx} = 0` but `(A²)_{yx} = 1` | `Granger.bivariate_oneStep_iff_irf`, `Granger.chainA`, `Granger.trivariate_counterexample` |
| pp. 501–502; A2 p. 593 | the news model `s_t = ε_{t−1}`: `v_t = ε_t`, `s_{t+1} = v_t`, regression coefficient one, past surpluses uncorrelated with the next | `Granger.newsCoeff`, `Granger.news_surplus`, `Granger.newsCoeff_support`, `Granger.news_value`, `Granger.news_surplus_eq_value`, `Granger.news_regCoeff`, `Granger.news_past_surplus_uncorrelated`, `Granger.truncModel_news` |
| pp. 501–502 ("debt [should] Granger-cause surpluses") | as a VAR, debt Granger-causes surpluses and surpluses do not Granger-cause debt | `Granger.newsA`, `Granger.newsZ`, `Granger.newsShock`, `Granger.news_isVAR`, `Granger.news_debt_causes_surplus`, `Granger.news_surplus_not_cause_debt` |
| A2 (2.22)–(2.23), p. 602 | coarser information; (2.22) gives `E(v_t\|I_t) = E(PV\|I_t)`; (2.23) holds iff `v_t` is in our information set; it holds when `I = Ω` | `Granger.Coarser`, `Granger.pv_ours_of_agents`, `Granger.pv_ours_iff`, `Granger.pv_ours_of_same` |
| A2 p. 602 (example) | when agents know the coin and we do not, (2.22) holds and (2.23) fails | `Granger.coinMean`, `Granger.oursInfo`, `Granger.ours_coarser`, `Granger.coinSurplus`, `Granger.coinSurplus_pv`, `Granger.pv_ours_fails` |

## The Leeper regions, §22.3, p. 500; §22.7, pp. 508–509; (23.1)–(23.4), pp. 512–513 (LeeperRegions, FiscalRec)

| Book | Claim | Lean |
| --- | --- | --- |
| (23.1)–(23.4), p. 512 | a path is a Leeper equilibrium iff expected inflation obeys the monetary equation, debt obeys (23.4) and `ρv_0 + π_0 = K`; debt is generated by (23.4) from `K` | `LeeperRegions.mkPath`, `LeeperRegions.mkPath_eqm`, `LeeperRegions.eq_mkPath`, `LeeperRegions.vPath`, `LeeperRegions.vPath_spec`, `LeeperRegions.vPath_adapted` |
| (23.4), p. 512 | the recursion `d_{t+1} = γd_t + u_t` is adapted when `u_t` is known at `t + 1` | `FiscalRec.dRec_adapted_of_succ` |
| pp. 495, 501, 512–513 (E12) | `\|1 − γ\| ≥ 1 ↔ γ ≤ 0 ∨ γ ≥ 2`; `\|1 − γ\| < 1 ↔ 0 < γ < 2` | `FiscalRec.one_le_abs_one_sub_iff`, `FiscalRec.abs_one_sub_lt_one_iff` |
| p. 513 | `qᵀx → 0` iff `\|q\| < 1` or `x = 0`; a stable recursion with vanishing inputs tends to zero | `FiscalRec.tendsto_pow_mul_iff`, `FiscalRec.eq_zero_of_tendsto_pow_mul`, `FiscalRec.tendsto_zero_of_stable_rec` |
| p. 513 ("if `γ > 0` … any unexpected inflation is consistent with the transversality condition", E12) | for `0 < γ < 2` any debt path obeying (23.4) satisfies the transversality condition | `LeeperRegions.tvc_passive` |
| (23.1)–(23.2), p. 512; (16.19), p. 371 | active money: the forward solution `π^m` is the only bounded solution; a bounded process with `E_te_{t+1} = φe_t`, `\|φ\| > 1`, is zero | `LeeperRegions.piM`, `LeeperRegions.piM_spec`, `FiscalRec.zero_of_E_succ_eq_smul` |
| (23.3)–(23.4), pp. 512–513 ("only one value of unexpected inflation keeps debt from exploding") | for `\|1 − γ\| ≥ 1` debt is the fiscal forward solution `v^f` and unexpected inflation is `ν^f`, for every `φ` | `LeeperRegions.vF`, `LeeperRegions.vF_spec`, `LeeperRegions.leeper_debt_E`, `LeeperRegions.eq_vF`, `LeeperRegions.nuF`, `LeeperRegions.active_fiscal_forced` |
| p. 508; (23.1)–(23.4) | for `\|φ\| > 1` inflation is `π^m` in every equilibrium | `LeeperRegions.active_money_forced` |
| §22.3, p. 500; §22.7, p. 508, region (a) | `\|φ\| > 1`, `0 < γ < 2`: exactly one equilibrium | `LeeperRegions.region_a` |
| p. 508, region (b) (E12) | `\|φ\| < 1`, `γ ≤ 0 ∨ γ ≥ 2`: exactly one equilibrium for bounded `K`; existence iff `K` bounded; a counterexample with unbounded `K` | `LeeperRegions.piB`, `LeeperRegions.region_b`, `LeeperRegions.region_b_iff`, `LeeperRegions.region_b_unbounded_K` |
| p. 508, region (c) ("inflation is overdetermined") | both active: existence iff the date-0 restriction and the cross-restriction hold; at most one `K` works; none with martingale-difference fiscal shocks, e.g. on the coin-flip tree | `LeeperRegions.region_c_iff`, `LeeperRegions.region_c_unique_K`, `LeeperRegions.piM_zero`, `LeeperRegions.vF_zero_of_md`, `LeeperRegions.region_c_md_nonexistence`, `LeeperRegions.region_c_coin` |
| p. 508 (E19) | double-active is unique in the starred form and has no equilibrium in the unstarred form with zero disturbances and nonzero debt | `LeeperRegions.e19_starred_vs_unstarred` |
| pp. 508–509, region (d) ("back to indeterminacy") | `\|φ\| < 1`, `0 < γ < 2`: uncountably many equilibria; every bounded martingale-difference sunspot gives one; random ones on the coin-flip tree | `LeeperRegions.region_d`, `LeeperRegions.region_d_sunspot`, `LeeperRegions.region_d_coin` |
| p. 508, boundary `\|φ\| = 1` | a continuum whenever the monetary equation has a bounded solution (any `\|φ\| ≤ 1`); no equilibrium for `u_{i,t} = −φ^{t+1}` | `LeeperRegions.region_d_of_solution`, `LeeperRegions.region_d_unit_nonexistence` |
| p. 513 (E12) | `γ = 3 > 0` is active: debt and unexpected inflation are pinned down | `LeeperRegions.gamma_three_active` |
| p. 508 (the Woodford–Leeper criterion) | bounded debt; uniqueness under it; bounded debt satisfies the transversality condition | `LeeperRegions.AdmissibleB`, `LeeperRegions.UniqueEqmB`, `LeeperRegions.admissible_of_B` |
| p. 508; pp. 512–513 | under bounded debt the target is unique iff `\|φ\| > 1` or `\|1 − γ\| > ρ`; `γ = (1 − ρ)/2` is passive under one criterion and active under the other | `LeeperRegions.uniqueB_iff`, `LeeperRegions.criterion_matters` |
| p. 508 vs Woodford (2003) p. 313 | a rule with feedback `γ` is locally Ricardian iff `\|1 − γ\| < ρ` | `LeeperRegions.locallyRicardian_iff_gamma` |
| (16.21)–(16.22), p. 373, as printed; (22.1), p. 495 (E6) | with the actual surplus driving target debt, `γ` drops out of the gap; `ρᵀE_tv_{t+T} → ((α − γ)/α)(v_t − v*_t)`; the transversality condition holds iff `γ = α` or debt is on target | `LeeperRegions.literal_gap`, `LeeperRegions.literal_vS`, `LeeperRegions.literal_limit`, `LeeperRegions.literal_tvc_iff` |

## Restated Woodford block: debt recursions and locally Ricardian rules (FiscalRec)

| Book | Claim | Lean |
| --- | --- | --- |
| Woodford (2003) (4.2), (4.4), (4.5), pp. 312–313 (restated from the Woodford Chapter 4 project) | the debt law, the tax rule and the implied law of motion of real debt | `FiscalRec.Debt42`, `FiscalRec.Tax44`, `FiscalRec.Debt45`, `FiscalRec.debt42_iff_45` |
| Woodford (2003) pp. 277, 313–314, Prop. C.2, App. C.8 (restated); Cochrane (23.4), p. 512 | the recursion `d_{t+1} = γd_t + u_t`: determined by `d_0`, bounded-input-bounded-state iff `\|γ\| < 1`, adapted | `FiscalRec.dRec`, `FiscalRec.eq_dRec`, `FiscalRec.abs_rec_le`, `FiscalRec.rec_bounded`, `FiscalRec.rec_unbounded`, `FiscalRec.pow_bounded_eq_zero`, `FiscalRec.dRec_adapted` |
| Woodford (2003) pp. 312–314 (restated); Cochrane p. 508 | locally Ricardian tax rules: iff `\|β⁻¹(1 − τ_b)\| < 1`, iff `τ_b > 1 − β` for `τ_b ≤ 1` | `FiscalRec.LocallyRicardian`, `FiscalRec.locallyRicardian_iff`, `FiscalRec.ricardian_iff_taub` |

## Markov switching, §24.2, pp. 522–523; §22.3, p. 500 (MarkovRegimes)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 522 | a two-state transition matrix; regime-history nodes; the model `E_tπ_{t+1} = φ_{S_t}π_t + u_t`; bounded processes | `MarkovRegimes.Transition`, `MarkovRegimes.P01`, `MarkovRegimes.P10`, `MarkovRegimes.Node`, `MarkovRegimes.Solves`, `MarkovRegimes.BoundedFn` |
| p. 523 | `M = Φ⁻¹P`, nonnegative for `φ > 0`; its characteristic polynomial at 1; Schur stability of nonnegative `2 × 2` matrices | `MarkovRegimes.regM`, `MarkovRegimes.regM_nonneg`, `MarkovRegimes.charpoly_one_eq`, `MarkovRegimes.schur_iff_of_nonneg` |
| pp. 522–523 (the long-run Taylor principle) | the Davig–Leeper condition holds iff both eigenvalues of `Φ⁻¹P` lie in the open unit disc | `MarkovRegimes.DLCondition`, `MarkovRegimes.dl_iff_schur` |
| p. 523 | under the condition the only bounded homogeneous solution is zero; otherwise a Perron vector gives a nonzero bounded one | `MarkovRegimes.pow_succ_apply`, `MarkovRegimes.abs_le_pow_bound`, `MarkovRegimes.homog_eq_zero`, `MarkovRegimes.mulVec_fin_two`, `MarkovRegimes.exists_perron`, `MarkovRegimes.homog_nonzero_of_not_dl` |
| p. 523 | the forward solution exists and is bounded under the condition | `MarkovRegimes.summable_pow_entry_of_schur`, `MarkovRegimes.fwdTerm`, `MarkovRegimes.fwdSol`, `MarkovRegimes.fwdTerm_bound`, `MarkovRegimes.summable_bound`, `MarkovRegimes.fwdTerm_summable`, `MarkovRegimes.fwdSol_solves`, `MarkovRegimes.fwdSol_bounded`, `MarkovRegimes.solves_sub` |
| pp. 522–523 | exactly one bounded equilibrium for every bounded disturbance iff the Davig–Leeper condition holds | `MarkovRegimes.determinate_iff` |
| p. 523 | both active is determinate; both passive is not | `MarkovRegimes.both_active_determinate`, `MarkovRegimes.both_passive_indeterminate` |
| p. 523 ("temporarily passive") | with `φ = (2, ½)`, a short-lived passive regime is determinate and a persistent one is not | `MarkovRegimes.egShortPassive`, `MarkovRegimes.egLongPassive`, `MarkovRegimes.temporarily_passive_determinate`, `MarkovRegimes.locally_active_indeterminate` |
| pp. 522–523 | the same dichotomy in any `ExpectationSystem` with a Markov regime process, extraneous sunspots included | `MarkovRegimes.MarkovRegime`, `MarkovRegimes.abstract_bound`, `MarkovRegimes.abstract_homog_eq_zero`, `MarkovRegimes.abstract_homog_nonzero` |

## Online Appendix §2.2, (2.24)–(2.26), pp. 604–605; §2.3, p. 606 (PresentValueIdentity)

| Book | Claim | Lean |
| --- | --- | --- |
| pp. 103, 111–112; A2 p. 605 (restated from the `DebtDeficitsInflation` project) | observables `c′z` of a VAR and their linearity, forecasts and responses | `PresentValueIdentity.obs`, `PresentValueIdentity.vecAt`, `PresentValueIdentity.obs_apply`, `PresentValueIdentity.obs_add`, `PresentValueIdentity.obs_sub`, `PresentValueIdentity.innov_obs`, `PresentValueIdentity.E_obs`, `PresentValueIdentity.var_innov_obs`, `PresentValueIdentity.var_forecast_obs`, `PresentValueIdentity.obs_adapted` |
| A2 p. 605 ("the eigenvalues of `A` are less than one"; restated, from Woodford's Chapter 4 project by way of `DebtDeficitsInflation`) | eigenvalues in the open unit disc give geometric decay of the powers of `A` | `PresentValueIdentity.PowDecay`, `PresentValueIdentity.eigs`, `PresentValueIdentity.map_ofReal_pow`, `PresentValueIdentity.powDecay_of_eigs`, `PresentValueIdentity.powDecay_smul` |
| pp. 111–112 (restated) | Neumann series `∑Aᵏ = (I − A)⁻¹` for a decaying matrix, entrywise and in bilinear form; the `ρ`-weighted sum of responses `c′(I − ρA)⁻¹ε_{t+1}` | `PresentValueIdentity.summable_pow_entry`, `PresentValueIdentity.tendsto_pow_entry_of_powDecay`, `PresentValueIdentity.neumannSum`, `PresentValueIdentity.neumannSum_mul`, `PresentValueIdentity.inv_one_sub_eq`, `PresentValueIdentity.isUnit_det_one_sub`, `PresentValueIdentity.inv_one_sub_hasSum`, `PresentValueIdentity.hasSum_bilin`, `PresentValueIdentity.neumann_bilin_hasSum`, `PresentValueIdentity.weight_bilin`, `PresentValueIdentity.var_weighted_sum` |
| A2 (2.25), p. 605 (restated) | the flow identity forces `a_v′(I − ρA) = (a_s + a_g − a_{rⁿ} + a_π)′A` | `PresentValueIdentity.flow_restriction_of_identity` |
| A2 (2.25)–(2.26), p. 605 (restated) | the coefficient restriction and the present-value restriction are the same when `I − ρA` is invertible | `PresentValueIdentity.one_sub_smul_mul_comm`, `PresentValueIdentity.inv_one_sub_mul_comm`, `PresentValueIdentity.flow_restriction_iff_pv` |
| A2 (2.24)–(2.26), p. 605 ("(2.26) reduces to `v_t = v_t`"; restated) | in a stable VAR obeying the flow identity the VAR present value converges and equals `v_t` | `PresentValueIdentity.var_pv_identity` |
| A2 (2.24)–(2.25), p. 605 (implicit) | an exact flow identity forces singular shocks `c′ε_{t+1} = 0`; with nondegenerate shocks `v ≡ 0` | `PresentValueIdentity.obs_smul`, `PresentValueIdentity.obs_var_succ`, `PresentValueIdentity.flow_forces_singular`, `PresentValueIdentity.ShockNondeg`, `PresentValueIdentity.nondeg_forces_trivial` |
| A2 §2.3, p. 606 | the linearised identity ex post, finite and infinite, split into surpluses and returns; "it always holds ex-post, so it always holds ex-ante" | `PresentValueIdentity.expost_pv_finite`, `PresentValueIdentity.expost_pv`, `PresentValueIdentity.expost_pv_split`, `PresentValueIdentity.pv_identity_exante` |
| A2 §2.3, p. 606 ("`0 = a_s(ρ) − a_r(ρ)` … is an identity") | the revisions of the present values of surpluses and returns are equal; with a constant return the surplus revision is zero, the testable `a(ρ) = 0` | `PresentValueIdentity.as_eq_ar_innov`, `PresentValueIdentity.const_return_as_zero` |
| A2 §2.3, p. 606 | `a(ρ)` for an observable of a VAR; `ΔE_{t+1}∑ρʲ(a′z)_{t+1+j} = a(ρ)′ε_{t+1}`; `a_s(ρ) = a_r(ρ)` for nondegenerate shocks | `PresentValueIdentity.genVAR`, `PresentValueIdentity.genVAR_hasSum`, `PresentValueIdentity.innov_pv_var`, `PresentValueIdentity.as_eq_ar_var` |

## Links between the modules and to Woodford (Links)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 508 | perfect foresight is full information on the one-point state space | `Links.perfectForesight_eq_fullInfo` |
| pp. 495–496 | the ex-post present value is the money model's present value one period later | `Links.pvExPost_eq_pv` |
| p. 501; A2 (2.22), p. 602 | the regression module's value of debt is the valuation equation of the frictionless model | `Links.valueOfDebt_eq_valuation` |
| p. 495 from A2 §2.3, p. 606 | the unexpected-inflation formula follows from the ex-post identity with `r_{t+1} = i_t − π_{t+1}`, needing only bounded debt | `Links.unexpected_inflation_of_identity` |
| p. 499 with p. 496 | in the money model the discount-factor step is `β`, `Λ_t = βᵗ`, and the discount-factor valuation reproduces `W_t/P_t = ∑βʲs_{t+j}` | `Links.sdf_of_const_step`, `Links.moneyEqm_debtFlow`, `Links.moneyEqm_sdfStep`, `Links.moneyEqm_sdf_valuation` |
| p. 502 with p. 501, §24.1 p. 519 | the s-shaped surplus has zero present value yet a positive regression coefficient on debt (for `\|1 − α\| < ρ`) | `Links.sshape_summable`, `Links.sshape_regression_pos` |
| p. 508 vs Woodford (2003) Prop. 4.11, pp. 311–314 | with passive money, bounded-debt uniqueness iff not locally Ricardian and `\|1 − γ\| ≠ ρ`; locally Ricardian with passive money is non-unique under both criteria | `Links.uniqueB_iff_not_ricardian`, `Links.ricardian_passive_not_unique` |
| pp. 522–523 with p. 495 | with one regime the Davig–Leeper condition is the Taylor principle, the starred system's determinacy, and the core's `\|φ⁻¹\| < 1` | `Links.dl_const_iff`, `Links.markov_const_determinate_iff`, `Links.markov_const_iff_starred_determinate`, `Links.markov_const_iff_forward` |
| pp. 495–497 (OE-2 with OE-1) | the money model's observable path is consistent, admissible for bounded inflation, and the unique equilibrium of every determinate interest-rate regime | `Links.moneyOutcome`, `Links.moneyOutcome_consistent`, `Links.moneyOutcome_admissible`, `Links.oe2_oe1` |
| p. 523; A2 p. 605 | a Schur-stable `2 × 2` matrix has geometrically decaying powers | `Links.powDecay_of_schur` |

## Shared tools

| Book | Claim | Lean |
| --- | --- | --- |
| (22.1), p. 495; p. 501, footnote 1 | the innovation operator `ΔE_{t+1}`, a linear map; zero on variables known at `t` | `ExpectationTools.innov`, `ExpectationTools.innov_apply`, `ExpectationTools.innov_of_known` |
| p. 508; A2 p. 602 | full information `E_t = id` on any state space | `ExpectationTools.fullInfo`, `ExpectationTools.fullInfo_E` |
| p. 495; A2 §2.3, p. 606 | the ex-post present value; geometric weights on bounded sequences | `ExpectationTools.pvExPost`, `ExpectationTools.summable_pow_mul_of_bounded`, `ExpectationTools.tendsto_pow_mul_of_bounded` |
| p. 495; A2 pp. 605–606 | iterating a flow identity forward; under `E_t` and the transversality condition it gives the present-value relation | `ExpectationTools.flow_telescope`, `ExpectationTools.pv_of_flow` |
| Chapter 22 throughout (shared core) | the expectation axioms, adapted processes, perfect foresight, bounded processes, finite event trees and the coin-flip tree and shock | `ExpectationSystem`, `ExpectationSystem.Adapted`, `perfectForesight`, `BoundedProc`, `ExpectationsFiniteTree.FiniteTree.toExpectationSystem`, `ExpectationsFiniteTree.coinSystem`, `ExpectationsFiniteTree.coinShock` |
| shared core | forward solutions, the unit-root non-existence lemma behind `LeeperRegions.region_d_unit_nonexistence`, and Schur–Cohn determinacy used by `MarkovRegimes` | `ForwardSolution.existsUnique_iff`, `ForwardSolution.no_bounded_solution_unit`, `SchurStable`, `schurStable_iff_roots` |
