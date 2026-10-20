# Corrections to the source

This file lists places where a claim in Chapter 22 (with the precise claims of Chapters 23–24 and
Online Appendix Chapter 2) of Cochrane (2023), *The Fiscal Theory of the Price Level*, is false,
imprecise, or relies on an unstated hypothesis, and where the Lean statement departs from the
printed one. In each case the Lean statement proves the stated version and cites the original.

Codes E12–E19 are the Chapter 22–24 items of the survey of Chapters 20–25
(`notes/survey_cochrane_ch20-25.md`); E6 is the Chapter 16 item of the survey of Chapters 11–19
(`notes/survey_cochrane_ch11-19.md`), which recurs here because (22.1) and (22.10) repeat (16.21).
Each was confirmed or refuted by formalisation before being recorded here, and an entry is revised
if formalisation shows the finding itself to be wrong: the survey's bounded-debt range, its
continuum claim and its discount-factor formula are corrected below. Several claims that the book
asserts without proof turned out to be correct; they are listed in the last section.

Out of scope are the verbal and empirical passages: §22.4 "Plausibility and other evidence", the
laugh tests of §22.5, §22.6 "Chicken and regimes", §22.8, the literature review of Chapters 23–24,
and the Beck-Friis–Willems label swap on p. 525 (E15). The typo on p. 512 ("can leave have", E18)
is cosmetic. Lean names are relative to the namespace `Cochrane.ObservationalEquivalence`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| p. 495 (box), p. 501, pp. 512–513 (E12) | Active money is "`φ > 1`, `γ > 0`", active fiscal "`φ < 1`, `γ = 0`"; "we should have `θ < 1` if we wish stationary solutions"; "if `γ > 0` … any unexpected inflation is consistent with the transversality condition". | The conditions need absolute values and an upper bound on `γ`. Under the book's criterion the target is the unique admissible equilibrium iff `\|φ\| > 1` or `γ ≤ 0` or `γ ≥ 2` (`Equivalence.unique_iff`, `Equivalence.determinate_iff`). `φ = −2 < 1` with `γ = 1` is determinate (`Equivalence.printed_phi_lt_one_determinate`), and `γ = 3 > 0` is active (`Equivalence.printed_gamma_pos_determinate`, `LeeperRegions.gamma_three_active`). Every `γ` with `\|1 − γ\| ≥ 1` pins down debt and unexpected inflation, not only `γ = 0` (`Equivalence.unique_of_active_fiscal`, `LeeperRegions.active_fiscal_forced`). Debt from (23.4) satisfies the transversality condition for every inflation path iff `0 < γ < 2` (`LeeperRegions.tvc_passive`, `Equivalence.tvc_of_ar1`, `Equivalence.zero_of_ar1_tvc`). Inflation `π_{t+1} = θπ_t + w_t` stays bounded for all bounded inputs iff `\|θ\| < 1` (`NonIdentification.stationary_iff`). |
| p. 508 (boundary of E12) | Passive money is "`φ < 1`". | At `\|φ\| = 1` (which includes `φ = −1 < 1`) the Leeper model with `0 < γ < 2` is neither determinate nor always indeterminate. If the monetary equation has a bounded solution there is a continuum (`LeeperRegions.region_d_of_solution`); for the bounded disturbance `u_{i,t} = −φ^{t+1}` there is no equilibrium at all (`LeeperRegions.region_d_unit_nonexistence`). Indeterminacy is guaranteed only for `\|φ\| < 1` (`LeeperRegions.region_d`). |
| (22.6), p. 500 (E13) | `v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`. | `ρ` is missing, inconsistent with (22.2), (22.11) and (23.4); with `ρ = 1` the transversality argument of pp. 512–513 degenerates. The Leeper model is stated with `ρv_{t+1}` (`StarredModel.LeeperEqm`), and the substitution of p. 512 is verified (`StarredModel.eq23_4`). |
| (24.1), p. 520 (E14) | `i_t = θπ_t + φ(π_t − π*_t) + u_{i,t}`. | It should be `θπ*_t`, as in (22.8). As printed, the rule is the starred rule with target rate `θπ*_t + u_{i,t}` and off-target coefficient `θ + φ`, so determinacy would turn on `\|θ + φ\|` (`StarredModel.rule24_1_printed`). |
| p. 501, footnote 1 (E17) | "Equivalently, `x_t` does not Granger-cause `y_t` if the impulse-response function of `y` to `x` shocks is zero." | True in a bivariate VAR (`Granger.bivariate_oneStep_iff_irf`) and for the multi-horizon definition (`Granger.irf_nonCausal_iff_forecast`). False for the standard one-step definition with three or more variables: in the chain `x → w → y`, `A_{yx} = 0` but `(A²)_{yx} = 1` (`Granger.trivariate_counterexample`). The impulse-response definition implies the one-step one (`Granger.irf_imp_oneStep`). |
| p. 508 (E19) | "If `φ > 1` and `γ = 0` both policies are active … inflation is overdetermined … no equilibrium can form." | False in the starred parametrisation (22.1): there the coordinated target is the unique admissible equilibrium (`Equivalence.unique_double_active`). In the unstarred model (22.3)–(22.6) non-existence is generic, not certain: an equilibrium exists iff a date-0 restriction and a cross-restriction on the disturbances hold (`LeeperRegions.region_c_iff`). At most one inherited debt works (`LeeperRegions.region_c_unique_K`), and with martingale-difference fiscal shocks none does (`LeeperRegions.region_c_md_nonexistence`, `LeeperRegions.region_c_coin`). The two forms are contrasted in `LeeperRegions.e19_starred_vs_unstarred`. |
| (16.21), p. 373, repeated in (22.1), p. 495, and (22.10), p. 501 (E6) | Fiscal policy is passive for "`γ > 0`". | As printed, target debt `v*` is driven by the actual surplus. Then `γ` drops out of the gap dynamics (`LeeperRegions.literal_gap`, `LeeperRegions.literal_vS`), `ρᵀE_tv_{t+T} → ((α − γ)/α)(v_t − v*_t)` (`LeeperRegions.literal_limit`), and the transversality condition holds iff `γ = α` or debt is on target (`LeeperRegions.literal_tvc_iff`). Passivity is `γ = α`, neither `γ > 0` nor `0 < γ < 2`, in agreement with the Chapter 16 project. The main formalisation reads the target as an exogenous consistent path driven by the target surplus (`StarredModel.Consistent`, `StarredModel.StarredSurplus`). On the target both readings coincide, and under this one the passive range is `0 < γ < 2` (`Equivalence.unique_iff`). The unstarred rule `s̃_{t+1} = γv_t + u_{s,t+1}` is unaffected. |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| §24.1, p. 519; p. 501 (E16) | "A surplus moving average with `a(ρ) < 1` generates a regression coefficient `γ > 0`." | True (`SurplusRegression.book_claim_aRho_lt_one`), but the hypothesis is superfluous. With an exogenous moving-average surplus, `2Cov(s_{t+1}, v_t) = ∑_{k≥1}a_k² + ∑_{k,l≥1}ρ^{\|k−l\|}a_ka_l` (`SurplusRegression.two_cov_eq_kms`), and the coefficient is positive iff the surplus is not white noise (`SurplusRegression.regCoeff_pos_iff`). The same holds for absolutely summable infinite moving averages (`SurplusRegression.covInf_pos_iff`, `SurplusRegression.regInf_pos_iff`). The MA(1) `(1, 1)` has `a(ρ) = 1 + ρ > 1` and a positive coefficient (`SurplusRegression.ma1_aRho_gt_one`, `SurplusRegression.ma1_regCoeff_pos`); the AR(1) has `γ̂ = 1 − ρη > 0` for every `η ≠ 0`, including `a(ρ) = 1/(1 − ρη) > 1` (`SurplusRegression.ar1_regCoeff`, `SurplusRegression.ar1_aRho_gt_one`). |
| p. 508; pp. 512–513 (the equilibrium criterion) | The regime boundaries are stated without saying which equilibrium criterion they assume. | They depend on it. Under the transversality condition the passive range is `0 < γ < 2` (`Equivalence.unique_iff`). Under bounded debt the target is unique iff `\|φ\| > 1` or `\|1 − γ\| > ρ`, so the passive range is `1 − ρ ≤ γ ≤ 1 + ρ`, boundary included (`LeeperRegions.uniqueB_iff`). The survey's open interval `1 − ρ < γ < 1 + ρ` is wrong at the boundary, where bounded sunspot paths still exist; Woodford's locally Ricardian condition is the strict `\|1 − γ\| < ρ` (`LeeperRegions.locallyRicardian_iff_gamma`). `γ = (1 − ρ)/2` is passive under the first criterion and active under the second (`LeeperRegions.criterion_matters`). |
| p. 508, region (b) | With passive money and active fiscal policy the equilibrium is unique. | Only for bounded inherited debt. An admissible equilibrium exists iff `K` is bounded, since `π_0 = K − ρv^f_0` is forced (`LeeperRegions.region_b_iff`, `LeeperRegions.region_b`). On the state space `ℕ` with full information and `K(ω) = ω` there is none (`LeeperRegions.region_b_unbounded_K`). On a finite tree the hypothesis holds automatically. |
| pp. 508–509 (double passive) | "We are back to indeterminacy … even if the ingredient is sunspots." | Proved for `\|φ\| ≤ 1`, `0 < γ < 2` in the starred form (`Equivalence.continuum_double_passive`) and for `\|φ\| < 1` in the Leeper form (`LeeperRegions.region_d`). The survey said the continuum needs a non-degenerate expectation system; it does not. The date-0 inflation jump indexes a continuum even under perfect foresight, where every equilibrium is such a jump path (`Equivalence.perfectForesight_eq_famPath`). Genuinely random sunspot equilibria are shown separately on the coin-flip tree (`Equivalence.coin_sunspot_eqm`, `LeeperRegions.region_d_coin`). |
| p. 499 | "Absent arbitrage, there is a discount factor that reconciles the value of debt to …" surpluses. | Formalised twice. The finite-state, one-period fundamental theorem of asset pricing is proved by Hahn–Banach separation (`AssetPricingOE.ftap`). For government debt, the ex-post discount factor `Λ_{t+1}/Λ_t = Q_tP_{t+1}/P_t` prices the one-period bond exactly (`PresentValueIdentity.sdf_prices_bond`) and, under the transversality condition, gives `B_{t−1}/P_t = E_t∑(Λ_{t+j}/Λ_t)s_{t+j}` (`PresentValueIdentity.sdf_valuation_E`). The survey's formula `Q_tP_t/P_{t+1}` is inverted. |
| A2 p. 605 | "So long as the eigenvalues of `A` are less than one, this restriction is identical to the restriction coming from the flow identity." | Only invertibility of `I − ρA` is needed for the equivalence of (2.25) and (2.26) (`PresentValueIdentity.flow_restriction_iff_pv`); convergence of the present value is a separate matter, which needs stability (`PresentValueIdentity.var_pv_identity`). This is E18 of the survey of Chapters 4–5, carried over with the restated block. |
| A2 p. 605 (implicit) | The flow identity (2.24) holds among the VAR variables. | An exact identity among VAR variables forces a singular shock covariance: `c′ε_{t+1} = 0` with `c = ρa_v − (a_{rⁿ} − a_π − a_g − a_s)` (`PresentValueIdentity.flow_forces_singular`). With nondegenerate shocks it forces `v ≡ 0` (`PresentValueIdentity.nondeg_forces_trivial`). |
| A2 §2.3, p. 606 | `0 = a_s(ρ) − a_r(ρ)` "derives from an identity, so it too is an identity". | Proved as a statement about innovations in every model in which bounded processes obey the flow identity (`PresentValueIdentity.as_eq_ar_innov`), and as `a_s(ρ) = a_r(ρ)` for VAR observables with nondegenerate shocks (`PresentValueIdentity.as_eq_ar_var`). |
| pp. 522–523 (Davig–Leeper) | Markov switching: a future active regime can select equilibria; "temporarily passive" policy. | Stated for two regimes and `φ_i > 0`, the Davig–Leeper setting. The model has exactly one bounded equilibrium for every bounded disturbance iff the long-run Taylor principle holds (`MarkovRegimes.determinate_iff`), equivalently both eigenvalues of `Φ⁻¹P` lie in the open unit disc (`MarkovRegimes.dl_iff_schur`). "Bounded" is the sup norm over regime histories. Uniqueness here excludes sunspots too (`MarkovRegimes.abstract_homog_eq_zero`). Farmer, Waggoner and Zha's finding that the condition is not sufficient concerns mean-square-stable solutions, a different criterion, so it is no counterexample. |
| p. 508 ("if monetary policy fixes `M` and fiscal policy fixes surpluses at an inconsistent value, no equilibrium can form") | No equilibrium when `M` and `s` are inconsistent. | Made precise: with `M`, `s` and `W` all fixed an equilibrium exists iff `W_ty_t/(M_tV_t) = ∑βʲs_{t+j}` at every date (`MoneyRegimes.inconsistent_iff`); halving the money supply with surpluses unchanged leaves none (`MoneyRegimes.halve_money_no_eqm`). |
| p. 496 (NI-1) | "Without additional identifying assumptions, the parameters that separate regimes such as `γ` and `φ` are not identified." | Stated pathwise: the equilibrium set is the same singleton for all determinate `(φ, γ)` (`NonIdentification.eqmSet_const_on_determinate`), so every statistic agrees (`NonIdentification.statistic_independent`) and no function of the observed path returns `(φ, γ)` (`NonIdentification.not_identified`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| Throughout | Disturbances and surpluses are bounded and adapted; `0 < ρ < 1` | Hypotheses of each theorem; some proofs need only `ρ ≠ 0` (`Equivalence.unique_iff`) or `\|ρ\| < 1` (`Valuation.valuation_E_exPost`) |
| (22.1), p. 495 | A common date-0 condition for all candidate paths | `ρv_0 + π_0 = ρv*_0 + π*_0` is part of `StarredModel.Eqm`; `π_0 = π*_0` is derived in the determinate regions (`Equivalence.unique_of_determinate`), not imposed |
| (22.3)–(22.6), p. 500 | Inherited debt known at date 0, and bounded in region (b) | `ρv_0 + π_0 = K` with `E_0K = K` in `StarredModel.LeeperEqm`; boundedness of `K` in `LeeperRegions.region_b`, shown necessary by `LeeperRegions.region_b_unbounded_K` |
| p. 501; A2 p. 593 | Shocks are serially uncorrelated with unit variance and a martingale difference sequence for the agents | `MACovariance.WhiteNoise` for an abstract covariance form and `SurplusRegression.ShockInfo`; satisfiable with nonzero bounded shocks (`SurplusRegression.truncModel_regCoeff_pos`) |
| p. 501; §24.1, p. 519 | Infinite moving averages converge | `∑\|a_k\| < ∞`, hypothesis of `SurplusRegression.two_covInf_eq` and its successors; square summability alone is not covered |
| p. 502 with p. 501 | The s-shaped surplus is a convergent moving average | `\|1 − α\| < ρ` in `Links.sshape_summable`, `Links.sshape_regression_pos` (a scope condition, not a book error) |
| pp. 495–496 | Money model under perfect foresight with positive velocity and output, `0 ≤ β < 1`, bounded surpluses, nonzero nominal liabilities | Part of `MoneyRegimes.Eqm` and hypotheses of `MoneyRegimes.oe2`; bounded inflation for `Links.moneyOutcome_admissible` and `Links.oe2_oe1` |
| pp. 522–523 | Positive policy coefficients `φ_i > 0` and two regimes | Hypotheses of `MarkovRegimes.dl_iff_schur`, `MarkovRegimes.determinate_iff`; both regimes possible at date 0 for `MarkovRegimes.abstract_homog_nonzero` |
| A2 p. 605 | `I − ρA` invertible, and a stable VAR for convergence | Hypotheses of `PresentValueIdentity.flow_restriction_iff_pv` and `PresentValueIdentity.var_pv_identity` (`PresentValueIdentity.PowDecay`) |
| p. 499 | Positive bond prices and price levels; the transversality condition and summable discounted surpluses | Hypotheses of `PresentValueIdentity.sdf_valuation_hasSum` and `PresentValueIdentity.sdf_valuation_E` |
| pp. 498–499 | Finitely many states and assets, full-support beliefs | Hypotheses of `AssetPricingOE.ftap`, `AssetPricingOE.rational_behavioral_equiv` |

## A comparison with Woodford (not a book error)

Cochrane's transversality criterion is weaker than Woodford's bounded-debt criterion, and
Woodford's local Ricardianness (Proposition 4.11) is stricter than bounded-debt passivity. In
Cochrane's notation a rule is locally Ricardian iff `\|1 − γ\| < ρ`
(`LeeperRegions.locallyRicardian_iff_gamma`). With passive money the target is the unique bounded
equilibrium iff the rule is not locally Ricardian and `\|1 − γ\| ≠ ρ`
(`Links.uniqueB_iff_not_ricardian`), so on the boundary `\|1 − γ\| = ρ` a rule that is not locally
Ricardian still leaves the equilibrium indeterminate. A locally Ricardian rule with passive money
is indeterminate under both criteria (`Links.ricardian_passive_not_unique`).

## Claims confirmed correct

| Where | Claim | Lean |
| --- | --- | --- |
| p. 495 | The valuation equation follows from iterating (22.2) and imposing the transversality condition, and conversely; unexpected inflation is minus the news about the present value of surpluses | `Valuation.tvc_iff_valuation`, `Valuation.valuation_E_exPost`, `Valuation.unexpected_inflation_news` |
| p. 497 | The valuation equation is an equilibrium condition of every regime | `StarredModel.valuation_all_regimes` |
| p. 495 (box); p. 496 | The target is an equilibrium for every `(φ, γ)`; any time series from one regime can be produced by the other | `StarredModel.starred_eqm`, `Equivalence.oe_both_ways` |
| p. 497 | The recipe turning any new-Keynesian or monetarist equilibrium into a fiscal-theory one | `Equivalence.recipe`, `Equivalence.leeper_recipe` |
| (16.23)–(16.24), p. 373 | On the target the observables involve neither `φ` nor `γ` | `StarredModel.observables_eq16_23_24` |
| §16.6, p. 372 | The new-Keynesian AR(1) equilibrium is a fiscal-theory equilibrium with `θ = η` and passive fiscal news `ε/(φ − η)` | `Equivalence.ftpl_eq_nk`, `Equivalence.nk_passive_fiscal_news` |
| p. 501 | `θ` can be measured; `i = φπ + u` imposes `φ = θ`; (22.5) imposes `α = γ`; `θ` and `φ` have distinct functions | `NonIdentification.regression_identifies_theta`, `NonIdentification.spec_forces_phi_eq_theta`, `NonIdentification.spec_forces_gamma_eq_alpha`, `NonIdentification.theta_target_unique` |
| §16.5, p. 371 | Reverse engineering of the disturbances | `NonIdentification.reverse_engineer_rule`, `NonIdentification.reverse_engineer_leeper`, `NonIdentification.rev_disturbances_differ` |
| p. 502 | The s-shaped surplus from `α > 0` or from an s-shaped disturbance | `NonIdentification.sshape_two_ways`, `NonIdentification.irf_sshape`, `NonIdentification.irf_pv_zero` |
| pp. 495–496 | OE-2 for money-supply regimes | `MoneyRegimes.oe2`, `MoneyRegimes.activeMoney_exists`, `MoneyRegimes.activeFiscal_exists` |
| p. 498 | Probabilities and marginal utility enter only as a product | `AssetPricingOE.rational_behavioral_equiv`, `AssetPricingOE.same_prices_iff` |
| pp. 501–502; A2 p. 593 | With news, debt Granger-causes exogenous surpluses and forecasts them; "even with completely exogenous surpluses, we expect a positive regression coefficient" | `Granger.news_debt_causes_surplus`, `Granger.news_regCoeff`, `SurplusRegression.regCoeff_pos_iff` |
| A2 (2.22)–(2.23), p. 602 | The present-value relation with our information holds only if the value of debt is in our information set | `Granger.pv_ours_iff`, `Granger.pv_ours_fails` |
| A2 (2.24)–(2.26), p. 605 | (2.25) holds automatically; (2.26) "reduces to `v_t = v_t`" | `PresentValueIdentity.flow_restriction_of_identity`, `PresentValueIdentity.var_pv_identity` |
| A2 §2.3, p. 606 | The identity holds ex post, so ex ante; the constant-discount model is `a(ρ) = 0` | `PresentValueIdentity.pv_identity_exante`, `PresentValueIdentity.const_return_as_zero` |
| A2 p. 604 | AR(1) present value `v_t = ηs_t/(1 − ρη)` | `SurplusRegression.ar1_value` |
| p. 508, regions (a) and (d) | One equilibrium for active money with passive fiscal policy; indeterminacy, sunspots included, when both are passive | `LeeperRegions.region_a`, `LeeperRegions.region_d`, `LeeperRegions.region_d_sunspot` |
| p. 512 | The substitution after (23.4) | `StarredModel.eq23_4` |
| p. 523 | A temporarily passive regime can be determinate; a passive regime expected to persist undoes an active one | `MarkovRegimes.temporarily_passive_determinate`, `MarkovRegimes.locally_active_indeterminate` |
