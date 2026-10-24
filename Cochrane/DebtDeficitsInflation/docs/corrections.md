# Corrections to the source

This file lists places where a claim in Chapter 4 of Cochrane (2023), *The Fiscal Theory of the
Price Level*, in Online Appendix A2, or in the A1 §§1.2–1.3 linearisation derivations the chapter
relies on, is false, imprecise, or relies on an unstated hypothesis, and where the Lean statement
departs from the printed one. In each case the Lean statement proves the stated version and cites
the original.

Codes E1–E18 are the Chapter 4 and A2 items of the survey of Chapters 4–5
(`notes/survey_cochrane_ch4-5.md`; E11 is unused). E22 and E23 are that survey's codes for the two
A1 items used here. Each was confirmed or refuted by formalisation before being recorded here, and
an entry is revised if formalisation shows the finding itself to be wrong. One finding, on the
ARMA(1,1) invertibility threshold of A2 p. 598, is not in the survey's list of errors (the survey
had stated the threshold as an "iff", which is false) and was found during formalisation. Several
claims that the book asserts without proof turned out to be correct; they are listed in the last
section.

Out of scope are the data, the estimates, the tables and the figures of Chapter 4 (§4.1,
Figures 4.1–4.7, Tables 4.1–4.2, and the numerical decompositions of §§4.3–4.4) and the
simulations of A2 (Figures 2.1–2.2): this project formalises identities and model claims only.
Survey items that concern only those numbers (E7, E8, E9) are listed in the section on typos and
rounding without a Lean statement. Also out of scope are the discursive passages, for example the
risk-premium narrative of p. 93 and the remarks on liquidity premia, tax smoothing and the
historical record on pp. 94–97. Lean names are relative to the namespace
`Cochrane.DebtDeficitsInflation`.

## The (4.11) correction: an identity, not a repayment condition (E4)

On p. 98 the book generalises the Hansen–Roberds–Sargent result `Δπ_{t+1} = −a(ρ)ε_{t+1}` to
time-varying discount rates and growth. It writes `Δπ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ)]'ε_{t+1}`
and then offers (4.11), `a_s(ρ) + a_g(ρ) = a_r(ρ)`, as "the equivalent of `a(ρ) = 0`" that
characterises a government which repays its debt. Here `a_r` is the moving average of the
ex-post real return including its `j = 0` term, as in (4.12), (4.13) and A2 §2.3. Formalisation
shows:

1. **The printed line is false.** Its right-hand side is identically zero in every model that
   satisfies the flow identity (3.17) and the terminal condition
   (`GeneralizedHRS.printed_rhs_eq_zero`), so the line holds iff there is no unexpected inflation at
   all (`GeneralizedHRS.printed_line_iff`). In a coin-flip model with an i.i.d. surplus equal to the
   ex-post return and `π = −ε`, the flow identity holds, the right-hand side is `0`, and
   `Δ_1π_1 = −1` (`GeneralizedHRS.printed_line_counterexample`).
2. **The correct line** subtracts the `j = 0` return term and adds the nominal return:
   `Δπ_{t+1} − Δrⁿ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ) − a_r(0)]'ε_{t+1}`
   (`GeneralizedHRS.innov_pi_vector`). This is consistent with (4.12) at `ω = 0`, which is correct
   as printed (`GeneralizedHRS.identity_4_12`).
3. **(4.11) as printed is an identity.** `[a_s(ρ) + a_g(ρ) − a_r(ρ)]'ε_{t+1} = 0` in every model
   (`GeneralizedHRS.identity_4_11`), and with non-degenerate shocks `a_s(ρ) + a_g(ρ) = a_r(ρ)` as
   vectors, whatever the inflation process (`GeneralizedHRS.identity_4_11_vec`). This is what A2
   §2.3, p. 606, itself says ("`0 = a_s(ρ) − a_r(ρ)` … is an identity",
   `GeneralizedHRS.identity_A2`), and it is the same kind of statement as (4.13)
   (`GeneralizedHRS.identity_4_13`).
4. **The repayment condition** (no unexpected inflation with one-period debt) is
   `a_s(ρ) + a_g(ρ) = a_r(ρ) − a_r(0)` (`GeneralizedHRS.repayment_iff`,
   `GeneralizedHRS.repayment_iff_vec`). Under constant expected returns the return has no
   moving-average coefficients beyond `j = 0`, so `a_r(ρ) = a_r(0)`
   (`GeneralizedHRS.const_expected_return_coeffs`, `GeneralizedHRS.const_discount_gen`), and with no
   growth the condition reduces to the book's `a_s(ρ) = 0` (`GeneralizedHRS.repayment_reduces`).

All four statements hold for every `|ρ| ≤ 1`, including the book's `ρ = 1`, for bounded
martingale-difference shocks and absolutely summable moving-average coefficients; the innovation
terminal condition is then automatic for every moving average
(`LinearizedIdentities.tvc_innov_of_MAVec`). The book's conclusion that (4.11)–(4.13) "no longer
test" anything stands, and is strengthened: (4.11) itself is one of the identities.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| p. 87 (E1) | In the exact model, `(B_t/P_t)Δ_{t+1}(P_t/P_{t+1}) = Δ_{t+1}∑_{j≥0}βʲs_{t+j} = a(β)ε_{t+1}`. | The sum must run over `s_{t+1+j}`, as the valuation `B_t/P_{t+1} = E_{t+1}∑βʲs_{t+1+j}` requires; then the line holds (`SurplusMA.exact_innov_line`). The printed sum over `s_{t+j}` gives `βa(β)ε_{t+1}` (`SurplusMA.printed_exact_line`), equal to `a(β)ε_{t+1}` in a state iff `(1 − β)a(β)ε_{t+1} = 0` (`SurplusMA.printed_exact_line_iff`). For a coin-flip i.i.d. surplus with `β = 1/2` the printed formula gives `1`, the truth is `1/2` (`SurplusMA.printed_exact_line_counterexample`). |
| p. 88 (E3) | For the MA(1) with `θ = ρ⁻¹`, "a shock `s₁ = −ε₁` sets off an expectation `s₂ = ρ⁻¹ε₁`". | Both signs are flipped: `Δ_1s_1 = ε_1` and `Δ_1s_2 = −ρ⁻¹ε_1` (`SurplusMA.innov_ma1_now`, `SurplusMA.innov_ma1_next`). The printed pair holds in a state only if `ε_1 = 0` there (`SurplusMA.ma1_printed_signs_false`). |
| p. 98 (E4) | `Δπ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ)]'ε_{t+1}`, and (4.11) is the repayment condition. | See the first section: the line is false (its right-hand side is identically zero), (4.11) is an identity, and the repayment condition is `a_s(ρ) + a_g(ρ) = a_r(ρ) − a_r(0)` (`GeneralizedHRS.printed_rhs_eq_zero`, `GeneralizedHRS.printed_line_counterexample`, `GeneralizedHRS.innov_pi_vector`, `GeneralizedHRS.identity_4_11`, `GeneralizedHRS.repayment_iff_vec`). |
| p. 98, Campbell–Ammer display (E5) | `Δr_{t+1} = Δ∑_{j≥1}ρ^{j−1}Δd_{t+1} − Δ∑_{j≥2}ρ^{j−1}Δr_{t+j}`. | `Δd_{t+1}` should be `Δd_{t+j}`, and `Δr_{t+j}` should be `r_{t+j}` (returns are not differenced). The corrected display and its moving-average form `{a_d(ρ) − [a_r(ρ) − a_r(0)]}'ε` are proved (`GeneralizedHRS.campbellAmmer`, `GeneralizedHRS.campbellAmmer_MA`); the following MA formula in the book is right. With i.i.d. coin-flip `Δd = r = ε` and `ρ = 1/2`, `Δ_1r_1 = 1` but the printed display (`GeneralizedHRS.printedCampbellAmmer`) gives `5/2` (`GeneralizedHRS.printed_campbellAmmer_counterexample`). |
| A2 (2.11), p. 598 (E13) | `B_{t−1}/P_t = ε_t − Rε_{t−1} + βRε_t = −Rε_{t−1}`. | The sign of `βRε_t` must be minus (`βθ = −βR`); as printed the coefficient on `ε_t` is `2`, and the middle expression equals `−Rε_{t−1}` only when `ε_t = 0` (`Invertibility.printed_2_11_wrong`). The correct value is `−Rε_{t−1}` (`Invertibility.ma1_repaying_debt_value`). |
| A2 p. 604 (E15) | `Δπ = −a(ρ)ε = −(s_{t+1} − η_ss_t)/(1 − βη_s)`. | The denominator is `1 − ρη` (`PresentValueExamples.innov_infl_ar1`). Given `η ≠ 0` and a non-zero shock, the printed formula is right iff `β = ρ` (`PresentValueExamples.printed_p604_iff`). |
| A2 p. 611 (E16) | `v_t = E_t∑_{j≥1}ρ^{j−1}s_{t+j} = z_t/(1 − ρη_z) + x_t/(1 − ρη_x)`, and the VAR (2.34). | The closed form and (2.34) are correct for `v_t = E_t∑_{j≥0}ρʲs_{t+j}`, the current surplus included (`PermanentTransitory.pt_value`, `PermanentTransitory.pt_var`, `PermanentTransitory.pt_var_process`). The printed sum equals `η_zz_t/(1 − ρη_z) + η_xx_t/(1 − ρη_x) = (v_t − s_t)/ρ` (`PermanentTransitory.pt_value_printed`, `PermanentTransitory.pt_value_printed_eq`), a different number unless `η_z = 1` (`PermanentTransitory.printed_value_ne`), and it violates (2.34) (`PermanentTransitory.printed_value_var_fails`). |
| A1 p. 564 (E22) | `q̃_t = −∑_{j≥1}ωʲr̃ⁿ_{t+j}`. | Iterating `rⁿ_{t+1} = ωq_{t+1} − q_t` gives `q_t = −∑_{j≥1}ω^{j−1}rⁿ_{t+j}` (`LinearizationDerivation.bond_price_series`). With `ω = 1/2`, `rⁿ ≡ 1`, `q ≡ −2` the identity holds, the correct sum is `−2` and the printed sum `−1` (`LinearizationDerivation.printed_bond_price_counterexample`). (1.25) and (3.21) are unaffected (`LinearizedIdentities.bond_return_identity`). |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| (4.3), p. 88 (E2) | For the AR(1), "`a(ρ) = 1/(1 − ρη)` is a number greater than one". | Only for `η > 0`: for `0 < ρ`, `\|ρη\| < 1`, `a(ρ) > 1` iff `η > 0` (`SurplusMA.gen_ar1`, `SurplusMA.one_lt_gen_ar1_iff`). With `η = −0.3`, `ρ = 0.9`, `a(ρ) = 1/1.27 < 1` (`SurplusMA.gen_ar1_lt_one_example`). |
| A1 (1.24), p. 563 (E23) | The bond return is linearised as `rⁿ_{t+1} ≈ ωq̃_{t+1} − q̃_t`; replacing `ω/(1+i)` by `ω` "makes no practical difference". | The exact first-order coefficient is `ω/(1+i)` and the steady-state log return is `log(1 + i)`, not `i` (`LinearizationDerivation.bondLog_hasFDerivAt`, `LinearizationDerivation.bond_steady_log`); the first-order identity is exactly `LinearizedIdentities.BondReturn` with weight `ω/(1+i)` (`LinearizationDerivation.bondReturn_iff_first_order`). The two weights differ whenever `ω ≠ 0` and `i ≠ 0` (`LinearizationDerivation.approx_1_24_differs`). The linear modules take an abstract weight `ω`, so they hold verbatim for `ω̃ = ω/(1+i)`. |
| A2 p. 598, and the survey (found during formalisation) | "The non-invertibility problem occurs for any `β_s < (1 − ρ)/α`." | True but incomplete. With `α, ρ > 0`, the MA root `ρ/(1 − αβ_s)` of (2.3) lies strictly inside the unit circle iff `β_s < (1 − ρ)/α` **or** `β_s > (1 + ρ)/α` (the region `θ < −1`, not mentioned in the book) (`Invertibility.arma11_root`, `Invertibility.arma11_noninvertible_iff`). The survey's "iff `β_s < (1 − ρ)/α`" is false. |
| A2 p. 605 (E18) | "So long as the eigenvalues of `A` are less than one", the flow restriction (2.25) and the present-value restriction (2.26) are identical. | Two separate conditions. The restrictions are algebraically equivalent whenever `I − ρA` is invertible (`VARIdentities.flow_restriction_iff_pv`). Convergence of the VAR present value, and its equality with `v_t`, needs decaying powers of `A` and `\|ρ\| ≤ 1` (`VARIdentities.var_pv_identity`), which all eigenvalues in the open unit disc imply (`VARIdentities.powDecay_of_eigs`). |
| A2 (2.4)–(2.5), p. 597 (E12, second half) | (2.5) is the Wold representation of the true process. | The two processes have the same second moments only after rescaling the innovation variance: root `θ` with variance `σ²` matches root `θ⁻¹` with variance `θ²σ²` (`Invertibility.arma11_autocov_flip`, `Invertibility.spectral_density_flip`), and the Wold innovation of (2.4) has variance `σ²/ρ²` (`Invertibility.Hilbert.arma11_wold`). |
| A2 p. 606 (clarification, not counted as an error) | "The constant discount factor model is just `a_r(ρ) = 0`." | Under constant expected returns `a_{r,j} = 0` for `j ≥ 1`, so `a_r(ρ) = a_r(0)` (`GeneralizedHRS.const_expected_return_coeffs`, `GeneralizedHRS.const_discount_gen`); `a_r(ρ) = 0` additionally imposes no surprise in the ex-post return, `a_r(0) = 0`. The constant-discount present value holds iff the discounted expected returns sum to zero (`GeneralizedHRS.pv_constant_discount_iff`). |
| A2 pp. 597, 600 ("`a(ρ) = 0`, `ρ ≤ 1`") | A surplus with `a(ρ) = 0`, `ρ ≤ 1`, is not invertible. | Proved for `\|ρ\| ≤ 1` in filter form: no absolutely summable filter of current and past surpluses recovers the shock (`Invertibility.not_recoverable_of_aRho_eq_zero`). The Hilbert-space statement (the shock is not in the closed span of the surplus history) needs `\|ρ\| < 1`, since `∑ρᵐe_{t−m}` does not converge at `ρ = 1` (`Invertibility.Hilbert.not_mem_pastSpan_of_aRho_eq_zero`). |
| p. 96 (the Chapter 4 half of E10) | With `s̃_{t+1} = αv_t + u_{s,t+1}`, "surpluses themselves may be fully repaid with `a_s(ρ) = 0`, even if `a_u(ρ) > 1`". | Proved in termwise form: `∑ρʲΔs̃_{t+1+j} = 0` for any bounded adapted disturbance, `0 < ρ < 1`, `\|1 − α\| < ρ` (`SurplusProcessFacts.feedback_full_repayment`), while an AR(1) disturbance has `a_u(ρ) = 1/(1 − ρη) > 1` (`SurplusProcessFacts.feedback_repaid_despite_persistent_u`). The further claim that this specification is "compatible with active fiscal policy" is a Chapter 5 statement and is not treated here (E10). |

## Typos, labels and rounding

| Where | Book says | Finding |
| --- | --- | --- |
| (4.15), p. 103 (E6) | `Δ_1` combined with `g_{t+1+j}`, `r_{t+1+j}`. | Index typo: `g_{1+j}`, `r_{1+j}`. Stated with the corrected indices, for general `ρ` and every date (`VARIdentities.identity_4_15`). |
| A2 p. 597 (E12, first half) | "(2.5) is the Wold moving-average representation of the true process (2.5)." | Should read "of (2.4)" (`Invertibility.Hilbert.arma11_wold`). |
| A2 p. 598 (E14) | The government "issues debt `B_{t−1}/P_t = ε_{t−1}`". | Loose: by (2.11) the debt is `−Rε_{t−1}` (`Invertibility.ma1_repaying_debt_value`). |
| A2 p. 594 (E17) | "Section 5.5". | Should be §5.4 ((5.22)–(5.23)), and (2.1) writes `v_t` for `v*_t`. Not formalised (a cross-reference). |
| p. 101 (E7, suspected) | The AR(1) with `0.55` gives `a(1) = 2.21` and "predicts 2.28% inflation". | `1/(1 − 0.55) = 2.22`; 2.28 cannot be `a(ρ)` for `ρ < 1`. An estimate; out of scope, not formalised. |
| pp. 112–114 (E8) | Figure 4.7 caption and text indices; "rise" versus "decline". | Caption typos; out of scope, not formalised. |
| Table 4.2 (E9) | The decomposition. | Not an error: the survey found every row adds up within ±0.01. Out of scope, not formalised. |
| p. 88 | "5/(1 − 0.55) = 11%". | Exactly `100/9 ≈ 11.1` (`SurplusMA.ar1_volatility_example`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| (4.1)–(4.2), throughout | The shock is a bounded martingale difference and the moving-average coefficients are absolutely summable | `Innovations.IsMDS`, `Innovations.IsMDSVec` with an explicit bound; `Innovations.IsMA`, `Innovations.IsMAVec` include absolute summability |
| (3.19), (4.2), (4.11)–(4.13) | "Assuming that the sums converge" and the terminal condition | Present values use ordinary convergence (`LinearizedIdentities.SeriesTo`), so conditionally convergent sums are covered; the innovation terminal condition is a hypothesis (`SurplusMA.InnovTVC`), automatic for bounded debt and `\|ρ\| < 1` (`SurplusMA.innovTVC_of_bounded`) and, for moving averages, for every `\|ρ\| ≤ 1` (`LinearizedIdentities.tvc_innov_of_MAVec`) |
| (4.2), (4.11), (4.13); Ch. 4 uses `ρ = 1` | The identities at `ρ = 1` | Proved for every `\|ρ\| ≤ 1`, including `ρ = 1` (`SurplusMA.innov_infl_eq`, `GeneralizedHRS.identity_4_11`, `GeneralizedHRS.identity_4_13`); (4.14) at `ρ = 1` in a stable VAR (`VARIdentities.identity_4_14_rho_one_of_var`) |
| (4.11)–(4.13), coefficient forms | The shocks are non-degenerate, so equal shock combinations have equal coefficients | `GeneralizedHRS.Nondeg` as a hypothesis of the coefficient-form theorems (`GeneralizedHRS.identity_4_11_vec`, `GeneralizedHRS.repayment_iff_vec`, `GeneralizedHRS.identity_4_13_vec`) |
| §4.2.3, p. 93 | Quantities known at `t` pull out of `E_t` | `ExpectationSystem.PullOut` as a hypothesis of the exact-model theorems and `SurplusMA.sdf_one_step`; `\|β\| < 1` and bounded surpluses for the exact model |
| p. 103 ("all the variables are stationary, impulse-responses die out") | The VAR is stable | `VARIdentities.PowDecay`, implied by all eigenvalues in the open unit disc (`VARIdentities.powDecay_of_eigs`) |
| (4.17)–(4.18) | The shock covariance has a Cholesky factor with an invertible leading block, it is positive definite for (4.18), and regressions are population projections | `Σ = LLᵀ` with `L` block lower triangular and `L₁₁` invertible in `VARIdentities.Regression.regression_eq_cholesky`; positive definiteness in `VARIdentities.Regression.quadForm_pos`; the regressions are stated as covariance algebra, not as estimators |
| p. 101; A2 (2.22)–(2.23) | The VAR's information is contained in people's information | `ConditioningDown.Coarser` (tower property across information sets); the measure-theoretic instance is proved on a finite probability space with full support (`ConditioningDown.CondExp.condExpSystem`) |
| pp. 89–92, 94–95 | Sign statements need `ρ > 0` and a state with a non-zero shock | Hypotheses of `SurplusMA.innov_value_pos_iff`, `SurplusProcessFacts.no_inflation_iff_gen_zero`, `SurplusProcessFacts.gen_identified` (non-zero conditional variance) |
| A2 (2.3), p. 595 | `\|φρ\| < 1` for the debt AR(1), `φ = (1 − α)/ρ` | `0 < α < 2` in `Invertibility.arma11_aRho_params` and `Links.arma11_innov_infl` |
| p. 96 | Debt is stabilised by the feedback | `\|1 − α\| < ρ` in `SurplusProcessFacts.fbValue_bounded` and `SurplusProcessFacts.feedback_full_repayment` |
| A2 §2.4 | The two AR(1) components have distinct persistence | `η_z ≠ η_x` in `PermanentTransitory.pt_aRho`, `PermanentTransitory.pt_arma21_coeffs`, `PermanentTransitory.HilbertPT.pt_wold`, `PermanentTransitory.pt_shocks_recoverable` |

## Claims confirmed correct

| Where | Claim | Lean |
| --- | --- | --- |
| (4.2), p. 87 | Hansen–Roberds–Sargent: `Δπ_{t+1} = −∑ρʲΔs̃_{t+1+j} = −a(ρ)ε_{t+1}`; (4.4) | `SurplusMA.innov_infl_eq_tsum`, `SurplusMA.innov_infl_eq`, `SurplusMA.innov_infl_eq_surplus` |
| pp. 88–89 | Volatility `a(ρ)²`, covariance `−a(ρ)`, no correlation when `a(ρ) = 0` | `SurplusMA.condVar_innov_infl`, `SurplusMA.condCov_innov_infl`, `SurplusMA.no_correlation_of_gen_zero` |
| p. 88 | `a(ρ) < 1` forces a negative `a_j`; the MA(1) cases `θ = ρ⁻¹, 0, < 0` and `0 < θ < ρ⁻¹` | `SurplusMA.exists_neg_coeff_of_gen_lt_one`, `SurplusMA.gen_ma1_inv`, `SurplusMA.gen_ma1_zero`, `SurplusMA.one_lt_gen_ma1`, `SurplusMA.gen_ma1_mem_Ioo` |
| (4.5)–(4.7), pp. 89–90 | The value of debt and its innovation `[a(ρ) − 1]ε`, and the debt-response cases | `SurplusMA.value_ar1`, `SurplusMA.value_recursion`, `SurplusMA.rho_innov_value_eq`, `SurplusMA.innov_value_pos_iff`, `SurplusMA.innov_value_full_repayment` |
| (4.8)–(4.10), p. 91 | The exact-model decomposition and the three financing cases | `SurplusMA.exact_innov_flow`, `SurplusMA.exact_innov_flow_pv`, `SurplusMA.exact_innov_flow_ma`, `SurplusMA.financing_by_debt`, `SurplusMA.financing_by_inflation`, `SurplusMA.financing_superinflation` |
| §4.2.4, pp. 92–93 | Return innovations, risk-free debt with `a(ρ) = 0`, the SDF valuation | `SurplusMA.innov_return`, `SurplusMA.innov_return_riskfree`, `SurplusMA.abs_innov_return_ge`, `SurplusMA.sdf_one_step` |
| §§4.2.5–4.2.6, pp. 94–96 | The facts tied together by `a(ρ)`, its indirect estimates, no default iff `a(ρ) = 0`, revenue needs higher later surpluses | `SurplusProcessFacts.tied_together`, `SurplusProcessFacts.gen_identified`, `SurplusProcessFacts.no_inflation_iff_gen_zero`, `SurplusProcessFacts.revenue_rises_iff` |
| (4.12), (4.13), Campbell–Shiller, p. 98 | Correct as printed | `GeneralizedHRS.identity_4_12`, `GeneralizedHRS.identity_4_13`, `GeneralizedHRS.campbellShiller` |
| (4.14), (4.16), pp. 103–104 | The decompositions, in a stable VAR with no extra hypotheses | `VARIdentities.identity_4_14_of_var`, `VARIdentities.identity_4_16` |
| (4.17), p. 104 | Filling in shocks by regression "is equivalent to the usual orthogonalization" | `VARIdentities.Regression.regression_eq_cholesky`, `VARIdentities.Regression.filled_shock_eq_orthogonalized` |
| (4.18), p. 112 | The surplus-shock normalisation | `VARIdentities.Regression.functional_regression_normalised`, `VARIdentities.Regression.surplus_shock_sum` |
| pp. 101–102 | Conditioning down is valid iff `v_t ∈ I_t`; `I = Ω` means 100% R² | `ConditioningDown.condDown_iff`, `ConditioningDown.CondExp.condDown_condExp_iff`, `ConditioningDown.r_squared_one` |
| p. 102 | The MA(1) with `θ = ρ⁻¹` is not invertible, an autoregression gives `a(ρ) = 1 − ρ²`, the value of debt reveals the shock | `Invertibility.Hilbert.ma1_wold`, `Invertibility.ma1_fitted_aRho`, `Invertibility.ma1_value_reveals_shock` |
| A2 (2.3), (2.5), (2.6)–(2.8), pp. 595–598 | `a(ρ) = β_s`; fitted `(1 − ρ²)/α`; the debt VAR recovers the shock | `Invertibility.arma11_aRho_params`, `Invertibility.arma11_wold_aRho`, `Invertibility.shock_from_debt`, `Invertibility.debt_var_stable` |
| A2 (2.9)–(2.16), pp. 598–599 | The MA(1) debt examples, apart from E13–E14 | `Invertibility.ma1_debt_value`, `Invertibility.ma1_no_inflation_iff`, `Invertibility.ma1_inverse_not_summable`, `Invertibility.ma1_fitted_pv_innov`, `Invertibility.ma1_debt_var` |
| A2 (2.17)–(2.21), pp. 600–601 | `a(ρ) = 0` iff the factor `1 − ρ⁻¹L`; debt equals the ex-post present value; the Hansen–Sargent formula | `Invertibility.factor_of_aRho_zero`, `Invertibility.factor_value`, `Invertibility.value_expost_of_aRho_zero`, `Invertibility.hansenSargent`, `Invertibility.hansenSargent_genFn` |
| A2 p. 603 | The dividend and permanent-income examples | `PresentValueExamples.dividend_pv`, `PresentValueExamples.pih_consumption` |
| A2 (2.24)–(2.26), p. 605 | With `v_t` in the VAR the present value is a tautology | `VARIdentities.var_pv_identity` |
| A2 §2.3, p. 606 | `0 = a_s(ρ) − a_r(ρ)` is an identity; the constant-discount PV is not | `GeneralizedHRS.identity_A2`, `GeneralizedHRS.pv_constant_discount_iff` |
| A2 (2.27)–(2.33), pp. 607–610 | The permanent–transitory process: `a(ρ) = β_s`, the ARMA(2,1), the fitted `a(ρ)`, the "wrong AR(1)" | `PermanentTransitory.pt_aRho`, `PermanentTransitory.pt_arma21_coeffs`, `PermanentTransitory.pt_fitted_aRho`, `PermanentTransitory.HilbertPT.pt_wold`, `PermanentTransitory.HilbertPT.pt_wold_ar1` |
| A2 p. 611 | The positive surplus-on-debt coefficient and `ρ⁻¹ > 1` with stable eigenvalues | `PermanentTransitory.pt_coeff_pos`, `PermanentTransitory.pt_debt_coeff_gt_one`, `PermanentTransitory.pt_var_tr_det` |
| A1 (1.12), (1.13), (1.23), pp. 558–563 | `ρ = e^{−(r−g)}`; the first-order flow identity is (3.17); `Q = 1/(1 + i − ω)` | `LinearizationDerivation.rhoLin_eq_exp`, `LinearizationDerivation.flow_iff_first_order`, `LinearizationDerivation.bondQ_hasSum` |
