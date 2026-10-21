# Debt, deficits, discount rates and inflation in Lean

This is the `Cochrane/DebtDeficitsInflation/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Chapter 4, "Debt, deficits, discount rates and inflation" (pp. 81–116),
together with Online Appendix A2, "How not to test fiscal theory" (pp. 593–611), and the
derivations of the linearised identities in Online Appendix A1 §§1.2–1.3 (pp. 556–564). The
chapter is almost entirely about identities: the linearised flow identity of the government debt,
moving-average representations of surpluses, and what they imply for unexpected inflation, the
value of debt and the return on debt. Every identity and model claim is proved for an arbitrary
`ExpectationSystem`, so under perfect foresight and under genuine uncertainty, with an explicit
innovation operator `Δ_{t+1} = E_{t+1} − E_t` and moving averages in a martingale-difference
shock. The invertibility and Wold statements of §4.3 and A2 are proved in a real Hilbert space of
second moments. Conditioning down, invertibility, Wold and Granger causality are also proved on a
genuine probability space, with Mathlib conditional expectations and in `L²` of an i.i.d. economy,
and the Wold decomposition theorem that A2 invokes is proved in full for any weakly stationary
sequence in a real Hilbert space.
The library contains **753 theorems**, including the shared core; 385 of them are in the twelve
chapter modules and 152 in the four measure-theoretic and Hilbert-space chapter modules.

**Scope.** The data, the estimates, the tables and the figures of Chapter 4 are out of scope:
§4.1's U.S. surplus and debt series (Figures 4.1–4.2), the surplus-process estimates of §4.3
(Table 4.1, Figure 4.3), the inflation decompositions of §4.4 (Table 4.2, Figures 4.4–4.7), and
the simulations of A2 (Figures 2.1–2.2). The project formalises identities and model claims only:
the formulas behind those numbers, not the numbers.

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises.

Headline results, in the namespace `Cochrane.DebtDeficitsInflation`:
* **Unexpected inflation is `−a(ρ)` times the surplus shock.** If the surplus is a moving average
  `s_t = a(L)ε_t` (4.1) in a bounded martingale-difference shock, then in the simple model
  (one-period debt, constant expected return, no growth) `Δπ_{t+1} = −∑ρʲΔs̃_{t+1+j} = −a(ρ)ε_{t+1}`
  (4.2), for every `|ρ| ≤ 1`, including the book's `ρ = 1` (`SurplusMA.innov_infl_eq_tsum`,
  `SurplusMA.innov_infl_eq`). The underlying news formula `Δ_{t+1}∑ρʲs_{t+1+j} = a(ρ)ε_{t+1}` holds
  for scalar and vector shocks (`Innovations.innov_PV`, `Innovations.innov_PV_termwise_vec`).
* **The value of debt, the return and the financing of deficits.** (4.5)–(4.10):
  `ρΔv_{t+1} = [a(ρ) − 1]ε_{t+1}` (`SurplusMA.rho_innov_value_eq`), `Δr_{t+1} = a(ρ)ε_{t+1}`
  (`SurplusMA.innov_return`), and in the exact nonlinear model the revenue from bond sales moves by
  `[a(β) − 1]ε_{t+1}`, so a deficit is debt-financed when `a(β) = 0` and inflation-financed when
  `a(β) = 1` (`SurplusMA.exact_innov_flow_ma`, `SurplusMA.revenue_innov`,
  `SurplusMA.financing_by_debt`, `SurplusMA.financing_by_inflation`).
* **(4.11) is an identity, not a repayment condition.** See the next section.
* **The VAR decompositions.** The Neumann sums behind Table 4.2 (`VARIdentities.inv_one_sub_hasSum`,
  `VARIdentities.disc_rate_hasSum`), and (4.14)–(4.16) in a stable VAR with every convergence
  hypothesis discharged (`VARIdentities.identity_4_14_of_var`,
  `VARIdentities.identity_4_14_rho_one_of_var`). Filling in shocks by regression is the Cholesky
  orthogonalisation (`VARIdentities.Regression.regression_eq_cholesky`). With the value of debt in
  the VAR the present-value relation is a tautology, and (2.25) ⇔ (2.26) needs only `I − ρA`
  invertible (`VARIdentities.var_pv_identity`, `VARIdentities.flow_restriction_iff_pv`).
* **Conditioning down.** The present value computed with the VAR's information equals the value of
  debt iff `v_t` is in that information set, for any pair of nested expectation systems and for
  Mathlib conditional expectations (`ConditioningDown.condDown_iff`,
  `ConditioningDown.CondExp.condDown_condExp_iff`, `Links.condDown_flow`); it genuinely fails
  otherwise (`ConditioningDown.condDown_fails_example`).
* **The linearisations are exact derivatives.** (3.17) is exactly the first-order expansion of the
  log flow identity at the steady state, with `ρ = e^{−(r−g)}`
  (`LinearizationDerivation.flowLog_hasFDerivAt`, `LinearizationDerivation.flow_iff_first_order`),
  and the bond-return identity is the exact expansion with weight `ω/(1+i)`
  (`LinearizationDerivation.bondReturn_iff_first_order`).
* **Genuine probability models.** On a probability space with nested filtrations and Mathlib
  conditional expectations, the present value conditions down to `E(v_t|I_t)`, and to `v_t` iff
  `v_t ∈ I_t` (`ConditioningDownMeasure.condDown_iff`, `ConditioningDownMeasure.condDown_valuation_iff`,
  `ConditioningDownMeasure.condDown_flow_iff`); the unexpected-inflation decomposition with the
  econometrician's news carries an extra term `Δ^I_{t+1}v_t` and holds in the book's form iff it
  vanishes (`ConditioningDownMeasure.unexpected_inflation_any`,
  `ConditioningDownMeasure.simple_model_econ_iff`, with the counterexample
  `ConditioningDownMeasure.Example.econ_decomp_counterexample`). In a Hilbert space, and in `L²` of
  the i.i.d. economy: `a(ρ) = 0` with `|ρ| ≤ 1` rules out recovery of the shock by any summable
  filter (`InvertibilityMeasure.not_filter_of_aRho_eq_zero`, `InvertibilityMeasureL2.iid_not_filter`);
  the factorised Wold statement `a = (1 − ρ⁻¹L)g` with the root flipped, for every invertible `g`
  (`InvertibilityMeasure.wold_factor`, `InvertibilityMeasureL2.iid_wold_factor`); debt is the ex-post
  present value and reveals the shock (`InvertibilityMeasure.debt_hasSum_expost`,
  `InvertibilityMeasure.shock_mem_debtSpan`); and debt Granger-causes surpluses for an arbitrary
  absolutely summable moving average (`InvertibilityMeasure.granger_general`,
  `InvertibilityMeasureL2.iid_granger_general`), with error variances `σ²` versus `θ²σ²` in the
  factorised case (`InvertibilityMeasure.granger_factor`).
* **The Wold decomposition theorem.** A2 pp. 597 and 600 invoke it without stating it; it is
  proved in full for a weakly stationary sequence in a real Hilbert space (in `L²`: inner products
  are covariances, projections best linear forecasts). The innovations `e_t = x_t − P_{H_{t−1}}x_t`
  are white noise, and `x_t = ∑c_je_{t−j} + d_t` with `∑c_j² < ∞`, `c_0 = 1` and `d_t` in the
  remote past orthogonal to `e` (`Wold.wold_decomposition`); any one-sided representation in
  forecast errors is the Wold one, which is why an autoregression recovers it (`Wold.wold_unique`);
  the regular part is regular and the deterministic part deterministic, and neither can be dropped
  (`Wold.wold_dichotomy`, `Wold.mixed_example`); covariance stationarity is the same as being the
  orbit of a linear isometry (`Wold.stationary_iff_exists_shift`, `Wold.wold_of_stationary`). Every
  absolutely summable moving average in white noise is regular (`Wold.maProc_regular`), and the
  factorised statement (2.17) is an instance: its autoregression error is the Wold innovation and
  its fitted coefficients the Wold coefficients (`Wold.wold_factor_is_wold`,
  `Wold.IIDEconomy.iid_wold_factor_is_wold`, `Wold.IIDEconomy.coin_wold`).

## (4.11) is an identity, not a repayment condition

The book's generalisation of `a(ρ) = 0` to time-varying discount rates (p. 98) is the main
correction of the chapter (survey E4). With `a_r` the moving average of the ex-post real return
including its `j = 0` term, as in (4.12), (4.13) and A2 §2.3:
* the printed line `Δπ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ)]'ε_{t+1}` is false: its right-hand side is
  identically zero (`GeneralizedHRS.printed_rhs_eq_zero`), so it holds iff there is no unexpected
  inflation (`GeneralizedHRS.printed_line_iff`), and a coin-flip model satisfying the flow identity
  violates it (`GeneralizedHRS.printed_line_counterexample`). The correct line is
  `Δπ_{t+1} − Δrⁿ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ) − a_r(0)]'ε_{t+1}`
  (`GeneralizedHRS.innov_pi_vector`);
* (4.11), `a_s(ρ) + a_g(ρ) = a_r(ρ)`, holds in every model that satisfies the flow identity and the
  terminal condition, whatever the inflation process (`GeneralizedHRS.identity_4_11`,
  `GeneralizedHRS.identity_4_11_vec`), as A2 §2.3 itself says of `0 = a_s(ρ) − a_r(ρ)`
  (`GeneralizedHRS.identity_A2`);
* the repayment condition (no unexpected inflation with one-period debt) is
  `a_s(ρ) + a_g(ρ) = a_r(ρ) − a_r(0)` (`GeneralizedHRS.repayment_iff`,
  `GeneralizedHRS.repayment_iff_vec`). Under constant expected returns `a_r(ρ) = a_r(0)`, and with
  no growth it reduces to `a_s(ρ) = 0` (`GeneralizedHRS.const_expected_return_coeffs`,
  `GeneralizedHRS.repayment_reduces`).

(4.12) and (4.13) are correct as printed (`GeneralizedHRS.identity_4_12`,
`GeneralizedHRS.identity_4_13`), and the Campbell–Ammer display before (4.13) is corrected (E5).

## What `a(ρ)` determines

`a(ρ) = ∑a_jρʲ` (`Innovations.gen`) is the single number the chapter is about. The library proves:
* **Examples.** AR(1): `a(ρ) = 1/(1 − ρη)`, greater than one iff `η > 0` (`SurplusMA.gen_ar1`,
  `SurplusMA.one_lt_gen_ar1_iff`, E2). MA(1): `a(ρ) = 1 − θρ`, zero iff `θ = ρ⁻¹`
  (`SurplusMA.gen_ma1`, `Invertibility.ma1_aRho_eq_zero_iff`). `a(ρ) < 1` forces a negative
  coefficient: the s-shaped surplus (`SurplusMA.exists_neg_coeff_of_gen_lt_one`). The A2 ARMA(1,1)
  and the permanent–transitory process both have `a(ρ) = β_s` (`Invertibility.arma11_aRho_params`,
  `PermanentTransitory.pt_aRho`), so `Δπ = −β_sε` (`Links.arma11_innov_infl`,
  `Links.pt_innov_infl`).
* **Everything is tied together by it.** Unexpected inflation, the debt response and the return
  innovation are `Δπ = −a(ρ)ε`, `ρΔv = (a(ρ) − 1)ε` and `Δr = a(ρ)ε`
  (`SurplusProcessFacts.tied_together`), and `a(ρ)` is identified from second moments
  (`SurplusProcessFacts.gen_identified`, `SurplusProcessFacts.gen_identified_debt`). No inflation or
  default iff `a(ρ) = 0` (`SurplusProcessFacts.no_inflation_iff_gen_zero`); then government debt is
  risk free (`SurplusMA.innov_return_riskfree`). With debt feedback `a_s(ρ) = 0` even when the
  disturbance has `a_u(ρ) > 1` (`SurplusProcessFacts.feedback_repaid_despite_persistent_u`).
* **`a(ρ) = 0` makes the surplus non-invertible.** `a(ρ) = 0` iff `a(L)` has the factor `1 − ρ⁻¹L`
  (`Invertibility.factor_of_aRho_zero`, `Invertibility.factor_value`), and then no summable filter
  of current and past surpluses recovers the shock (`Invertibility.not_recoverable_of_aRho_eq_zero`,
  `|ρ| ≤ 1`), nor does any element of their closed span
  (`Invertibility.Hilbert.not_mem_pastSpan_of_aRho_eq_zero`, `|ρ| < 1`). The closed-span statement
  is false at `|ρ| = 1`: for `s_t = e_t − ρe_{t−1}`, `ρ = ±1`, the shock is a mean-square limit of
  linear combinations of current and past surpluses, though of no summable filter
  (`InvertibilityMeasure.mem_pastSpan_unit_root`, `InvertibilityMeasureL2.closedSpan_fails_at_unit_root`).
  An autoregression recovers
  the Wold representation with the root flipped from `ρ⁻¹` to `ρ`
  (`Invertibility.Hilbert.wold_innovation`), and so estimates a non-zero `a(ρ)`: `1 − ρ²` for the
  MA(1), `(1 − ρ²)/α` for the ARMA(1,1), `(1 − ρ²)/((1 − η_xρ)(1 − η_zρ))` for the
  permanent–transitory process (`Invertibility.ma1_fitted_aRho`, `Invertibility.arma11_wold_aRho`,
  `PermanentTransitory.pt_fitted_aRho`, with the Wold statements `Invertibility.Hilbert.ma1_wold`,
  `Invertibility.Hilbert.arma11_wold`, `PermanentTransitory.HilbertPT.pt_wold`). A VAR that includes
  the value of debt recovers the shock (`Invertibility.shock_from_debt`,
  `PermanentTransitory.pt_shocks_recoverable`). With `a(ρ) = 0` debt equals the ex-post present
  value of surpluses (`Invertibility.value_expost_of_aRho_zero`), and the Hansen–Sargent formula is
  proved in generating-function form, `∑c_kzᵏ = (a(z) − a(ρ))/(z − ρ)`
  (`Invertibility.hansenSargent_genFn`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. Besides E4, the confirmed errors of the chapter survey are:
* the exact-model line of p. 87 sums over `s_{t+j}` instead of `s_{t+1+j}` and so is off by a
  factor `β` (E1);
* "`a(ρ) = 1/(1 − ρη)` is a number greater than one", p. 88, needs `η > 0` (E2);
* both signs in the MA(1) example of p. 88 are flipped (E3);
* the Campbell–Ammer display of p. 98 has two index errors (E5), and (4.15) one index typo (E6);
* in A2: the reference and the variance rescaling of the Wold representation, p. 597 (E12), the
  sign in (2.11) (E13), the debt `−Rε_{t−1}` of p. 598 (E14), `1 − βη` for `1 − ρη` on p. 604
  (E15), the summation index of the value of debt on p. 611, without which (2.34) fails (E16), and
  "eigenvalues less than one" where only `I − ρA` invertible is needed, p. 605 (E18);
* in A1: `q_t = −∑ω^{j−1}rⁿ_{t+j}`, not `−∑ωʲrⁿ_{t+j}`, p. 564 (E22), and the bond-return weight
  `ω/(1+i)`, which (1.24) replaces by `ω` (E23).

In addition, found during formalisation: A2's ARMA(1,1) is non-invertible not only for
`β_s < (1 − ρ)/α` but also for `β_s > (1 + ρ)/α` (`Invertibility.arma11_noninvertible_iff`); the
recovery of the shock from an autoregression of debt, A2 p. 601, needs the other roots of `a(L)`
outside the unit circle (`InvertibilityMeasure.debt_not_invertible_example`); and the
unexpected-inflation decomposition conditions down only up to the term `Δ^I_{t+1}v_t`
(`ConditioningDownMeasure.Example.econ_decomp_counterexample`). The Wold theorem makes two A2
p. 597 statements precise: the Wold moving average is fundamental but can have a root on the unit
circle, so "invertible" is too strong (`Wold.wold_unit_root`,
`Wold.IIDEconomy.coin_wold_unit_root`), and an autoregression recovers the moving average only
for a regular process, without a deterministic part (`Wold.IIDEconomy.iid_mixed`). An earlier version of this README
listed the closed-span non-invertibility statement at `ρ = 1` as unproved; it is false (see
[corrections](docs/corrections.md)).

Not formalised:
* the data, estimates, tables and figures (see Scope), and with them the survey items that concern
  only numbers: the `a(1) = 2.21` versus "2.28%" discrepancy of p. 101 (E7, suspected), the
  Figure 4.7 caption (E8) and the row sums of Table 4.2 (E9, not an error). The one number checked
  is the p. 88 example `5/(1 − 0.55) ≈ 11%` (`SurplusMA.ar1_volatility_example`);
* the discursive passages: the risk-premium narrative of p. 93, the remarks on Jiang et al.,
  liquidity premia and the unit root in GDP (p. 94), Barro tax smoothing, the monetarist and
  new-Keynesian passive-policy remark, the Canzoneri–Cumby–Diba narrative and observational
  equivalence (pp. 96–97), "there always exists a discount rate" (p. 102), and the interpretation
  remarks of pp. 108 and 115–116;
* the claim of p. 96 that the debt-feedback surplus is "compatible with active fiscal policy"
  (E10): it is a Chapter 5 statement. The Chapter 4 half, `a_s(ρ) = 0` with `a_u(ρ) > 1`, is
  proved, in termwise form `∑ρʲΔs̃_{t+1+j} = 0` rather than as a closed-form coefficient sequence;
* the cross-reference "Section 5.5" of A2 p. 594 (E17);
* statistical claims: "OLS is consistent" for (2.16), and the regressions of (4.17)–(4.18) as
  estimators (they are proved as population covariance algebra);
* Wold and Granger causality as statements about conditional expectations given the σ-algebra of
  past surpluses: they are proved for best linear forecasts (closed linear spans and orthogonal
  projections in `L²`), which is what Wold and a VAR mean; for non-Gaussian shocks the two differ.
  This includes the general Wold decomposition theorem (`Wold.wold_decomposition`): its innovation
  is the linear forecast error, not `x_t − E(x_t|σ(x_{t−1}, x_{t−2}, …))`;
* conditioning down without bounded processes or with `|ρ| = 1`: the measure-theoretic results
  assume bounded measurable processes and `|ρ| < 1`, which the ex-post present value needs.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](DebtDeficitsInflation/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (shared core, restated from the earlier projects) |
| [Expectations](DebtDeficitsInflation/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; bounded adapted processes; forward series; the pull-out property (shared core) |
| [ExpectationsFiniteTree](DebtDeficitsInflation/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; coin-flip examples (shared core) |
| [ForwardSolution](DebtDeficitsInflation/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [Innovations](DebtDeficitsInflation/Innovations.lean) | 45 | §4.2, (4.1)–(4.4), §4.2.7: the innovation operator, martingale-difference shocks on `ℤ` and `ℕ`, `E_t` of absolutely summable series, scalar and vector moving averages, `a(z)`, the news formula `Δ∑ρʲs = a(ρ)ε` for `\|ρ\| ≤ 1`, the AR(1), a coin-flip shock |
| [LinearizedIdentities](DebtDeficitsInflation/LinearizedIdentities.lean) | 36 | §3.5, (3.17)–(3.25), as used in Ch. 4: ordinary convergence of series, forward iteration and terminal conditions, the flow identity and the inferred surplus (p. 86), the present-value, unexpected-inflation, bond-return and weighted-inflation identities |
| [LinearizationDerivation](DebtDeficitsInflation/LinearizationDerivation.lean) | 18 | A1 §§1.2–1.3: (3.17) and the bond-return identity as exact Fréchet derivatives at the steady state, `ρ = e^{−(r−g)}`, `Q = 1/(1 + i − ω)`, weight `ω/(1+i)`; E22, E23 |
| [SurplusMA](DebtDeficitsInflation/SurplusMA.lean) | 48 | §§4.2–4.2.4, (4.2)–(4.10): the simple model, Hansen–Roberds–Sargent, volatility and correlation, the AR(1) and MA(1), the value of debt, the exact model and the financing cases, the return on debt; E1–E3 |
| [SurplusProcessFacts](DebtDeficitsInflation/SurplusProcessFacts.lean) | 12 | §§4.2.5–4.2.6: the facts tied together by `a(ρ)`, its indirect estimates, no default iff `a(ρ) = 0`, bond-sale revenue, the debt-feedback model with `a_s(ρ) = 0` |
| [GeneralizedHRS](DebtDeficitsInflation/GeneralizedHRS.lean) | 31 | §4.2.7, (4.11)–(4.13), A2 §2.3: the corrected inflation line, (4.11) as an identity and the repayment condition, (4.12), Campbell–Shiller, Campbell–Ammer, (4.13), the constant-discount present value; E4, E5 |
| [PresentValueExamples](DebtDeficitsInflation/PresentValueExamples.lean) | 6 | A2 pp. 603–604: AR(1) dividends, permanent income, the AR(1) surplus lines; E15 |
| [VARIdentities](DebtDeficitsInflation/VARIdentities.lean) | 47 | §§4.3–4.4, (4.14)–(4.18), A2 §2.2: VARs, decaying powers, Neumann sums, (4.14)–(4.16) with stable-VAR versions, regression = Cholesky, the PV tautology (2.24)–(2.26); E6, E18 |
| [ConditioningDown](DebtDeficitsInflation/ConditioningDown.lean) | 17 | §4.3 pp. 101–102, A2 (2.22)–(2.23): coarser information, conditioning down iff `v_t ∈ I_t`, 100% R², a failure example, the Mathlib conditional-expectation instance |
| [Invertibility](DebtDeficitsInflation/Invertibility.lean) | 74 | §4.3 p. 102, A2 §§2.1.1–2.1.6, (2.1)–(2.21): autocovariance and spectral flips, non-recoverability when `a(ρ) = 0`, the ARMA(1,1) and its threshold, the debt VARs, the MA(1) debt examples, Hansen–Sargent, the factorisation, Hilbert-space Wold statements; E12–E14 |
| [PermanentTransitory](DebtDeficitsInflation/PermanentTransitory.lean) | 32 | A2 §2.4, (2.27)–(2.34): the permanent–transitory surplus, `a(ρ) = β_s`, the ARMA(2,1), the fitted representation and its Wold statement, the corrected value of debt and the VAR (2.34); E16 |
| [Links](DebtDeficitsInflation/Links.lean) | 19 | Links between the innovation and the VAR/invertibility modules: the ARMA family and the §4.2 examples, `ℕ`- and `ℤ`-indexed shocks, Hansen–Sargent news, `Δπ = −β_sε` for the A2 processes, conditioning down with the flow identity |
| [ExpectationsMeasure](DebtDeficitsInflation/ExpectationsMeasure.lean) | 71 | Measure-theoretic expectations (shared core, copied from `ObservationalEquivalence`): `MeasExpectationSystem` with Mathlib's `condExp`, the axioms a.e., news, the forward equation and sunspots, AR(1) conditional variance, bridges to and from the core `ExpectationSystem` |
| [ExpectationsMeasureIID](DebtDeficitsInflation/ExpectationsMeasureIID.lean) | 37 | The genuine i.i.d. economy on `ℕ → ℝ` under `ν^ℕ` (shared core): independence, moments, every history null, determinacy iff `\|a\| < 1`, AR(1), the `±1` coin |
| [ConditioningDownMeasure](DebtDeficitsInflation/ConditioningDownMeasure.lean) | 36 | §4.3 pp. 101–102, A2 (2.22)–(2.23) on a general probability space: nested filtrations, conditioning down iff `v_t ∈ I_t`, the valuation and flow identities, (3.20) and (4.2) under any information with the extra term `Δ^I_{t+1}v_t`, the lagged-econometrician counterexample, links to `ConditioningDown` |
| [InvertibilityMeasure](DebtDeficitsInflation/InvertibilityMeasure.lean) | 38 | §4.3 p. 102, A2 (2.17)–(2.21) in a Hilbert space: no summable filter at `\|ρ\| ≤ 1`, the closed-span correction at `\|ρ\| = 1`, the factorised Wold statement, debt as ex-post PV and its invertibility (with a counterexample), Granger causality for an arbitrary moving average |
| [InvertibilityMeasureL2](DebtDeficitsInflation/InvertibilityMeasureL2.lean) | 11 | The invertibility, Wold and Granger statements in `L²` of the i.i.d. economy (`e_t = ε_{φ(t)}`, `φ : ℤ ≃ ℕ`), the unit-root counterexample, the fair-coin instance |
| [Wold](DebtDeficitsInflation/Wold.lean) | 67 | A2 pp. 597, 600: the Wold decomposition theorem in a real Hilbert space (innovations, decomposition, uniqueness, the regular/deterministic dichotomy, covariance stationarity ⇔ isometry orbit), a mixed example, MAs are regular, the factorised (2.17) as an instance, the unit-root correction, the `L²` i.i.d. and fair-coin instances |

## Modelling conventions

* **Expectations and innovations.** Random variables are `Ω → ℝ` under an arbitrary
  `ExpectationSystem`. The innovation operator `Innovations.innov 𝔼 t` is the linear map
  `Δ_{t+1} = E_{t+1} − E_t`. A variable known at `t` (`E_tx = x`) has no innovation at `t + 1`.
  Results that move known quantities through `E_t` (the exact model, the SDF valuation) assume
  `ExpectationSystem.PullOut`.
* **Shocks and moving averages.** Shocks are indexed by `ℤ`, so that the moving average (4.1) has
  an infinite past; processes and information are indexed by `ℕ`. A shock is a bounded
  martingale difference (`Innovations.IsMDS`, `Innovations.IsMDSVec`), and moving averages have
  absolutely summable coefficients (`Innovations.IsMA`, `Innovations.IsMAVec`). The Online
  Appendix processes are written with `ℕ`-indexed shocks and a zero pre-sample
  (`Invertibility.maSeries`) or in revision form `Δ_{t+1}s_{t+1+j} = a_jε_{t+1}`; `Links` connects
  both to (4.1).
* **The simple model and the linear identities.** The primitives are the linearised flow identity
  (3.17) (`LinearizedIdentities.Flow`) and the geometric-maturity return
  `rⁿ_{t+1} = ωq_{t+1} − q_t` (`LinearizedIdentities.BondReturn`), as exact equalities at every date
  and state; `LinearizationDerivation` proves they are the exact first-order expansions of the
  nonlinear identities. The simple model of §4.2 adds one-period debt, a constant expected return
  and no growth (`SurplusMA.SimpleModel`). The exact model of §4.2.3 is the nonlinear valuation
  `B_t/P_{t+1} = E_{t+1}∑βʲs_{t+1+j}` with a constant real rate (`SurplusMA.ExactValuation`).
* **Infinite sums and terminal conditions.** "Assuming that the sums converge" is made explicit:
  present values use ordinary convergence of partial sums (`LinearizedIdentities.SeriesTo`), so
  conditionally convergent sums are covered, with `HasSum`/`tsum` corollaries under summability.
  The terminal condition is stated in innovations (`SurplusMA.InnovTVC`); it is automatic for
  bounded debt with `|ρ| < 1` and for every moving average with `|ρ| ≤ 1`
  (`LinearizedIdentities.tvc_innov_of_MAVec`), so the book's `ρ = 1` is covered.
* **VARs.** A VAR is `z_{t+1} = Az_t + ε_{t+1}` with random-variable coordinates
  (`VARIdentities.IsVAR`); stability is decay of the powers of `A` (`VARIdentities.PowDecay`),
  implied by all complex eigenvalues in the open unit disc.
* **Two information sets.** Conditioning down uses two expectation systems, the second coarser
  than the first (`ConditioningDown.Coarser`), with the Mathlib conditional expectation on nested
  filtrations of a finite space as an instance. On a general probability space the econometrician's
  system is the agents' system with a coarser filtration (`ConditioningDownMeasure.coarsen`,
  `ConditioningDownMeasure.Nested`), and `v_t ∈ I_t` means a.e. measurability
  (`ConditioningDownMeasure.KnownAE`).
* **Second moments.** Autocovariances and spectral densities are stated as identities of coefficient
  sequences. Wold and invertibility statements live in a real Hilbert space: white noise is an
  orthogonal family with equal norms (`Invertibility.Hilbert.WhiteNoise`), and "computable from the
  surplus history" means membership of the closed linear span of current and past surpluses
  (`Invertibility.Hilbert.pastSpan`). The genuine instance is `L²` of the i.i.d. economy
  (`InvertibilityMeasureL2.shockL2`, `InvertibilityMeasureL2.iid_whiteNoise`), where inner products
  are covariances and projections are best linear forecasts. The Wold theorem takes a sequence
  `x : ℤ → H` that is weakly stationary in either of two equivalent forms: the orbit of a linear
  isometry `U x_t = x_{t+1}`, or `⟪x_s, x_u⟫` depending only on `s − u`
  (`Wold.stationary_iff_exists_shift`); `Wold.past` is `Invertibility.Hilbert.pastSpan`.
* **Measure-theoretic expectations.** The core `ExpectationSystem` (an operator `E_t` on all
  functions `Ω → ℝ`, with exact equalities) is kept unchanged, and every result above stated for it
  still holds. On a countable `Ω` it forces finitely supported forecasts, so it cannot carry an
  infinite-horizon model with nondegenerate shocks. `ExpectationsMeasure` adds, alongside it, a
  probability space with a filtration (`ExpectationsMeasure.MeasExpectationSystem`): `E_t` is
  Mathlib's `condExp`, variables are bounded measurable functions and processes (`BddRV`, `BddProc`),
  and equations hold almost everywhere. The bridge is additive and runs both ways: a finite event
  tree is a measure system with the same `E_t` (`ExpectationsMeasure.TreeBridge.treeSystem_E`), and
  a measure system on a finite space with full support is a core system with pull-out
  (`ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem`,
  `ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_pullOut`);
  `ConditioningDownMeasure` links its results to `ConditioningDown` this way
  (`ConditioningDownMeasure.condDown_iff_core`). The genuine instance is the i.i.d. economy on
  `ℕ → ℝ` under `ν^ℕ`, in which every history has probability zero
  (`ExpectationsMeasureIID.iidSystem`, `ExpectationsMeasureIID.iid_not_finitely_supported`).
* **Explicit hypotheses.** Hypotheses the book leaves implicit are stated in each theorem:
  `|ρ| ≤ 1` (or `< 1`), `|β| < 1` in the exact model, bounded shocks, non-degenerate shocks for
  the coefficient forms of (4.11)–(4.13) (`GeneralizedHRS.Nondeg`), a state with a non-zero shock
  for the "iff" results, `0 < α < 2` for the A2 ARMA(1,1), `|1 − α| < ρ` for debt feedback, and
  `η_z ≠ η_x` for the permanent–transitory process.

## Relation to the Woodford and Galí projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects (the first three from `Woodford/ReturnOfMonetaryRules`,
`ForwardSolution` from the Woodford Chapter 2 and 3 projects), so the project builds on its own.
Nothing is imported from those projects. The measure core (`ExpectationsMeasure`,
`ExpectationsMeasureIID`) is copied, with the namespace renamed, from the Cochrane Chapter 22
project `ObservationalEquivalence`. The chapter modules use `ExpectationSystem`,
`ExpectationSystem.Adapted`, `ExpectationSystem.IsAR1`, `ExpectationSystem.PullOut`,
`ExpectationSystem.E_tsum`, `ForwardSolution.E_tsum_dom`, the coin-flip tree
(`ExpectationsFiniteTree.coinSystem`) for the counterexamples, and the Schur–Cohn condition
`SchurStable` (Woodford Prop. C.1, Galí Chapter 3) for the stability of the A2 debt VAR
(`Invertibility.debt_var_stable`). The forward-solution theory is carried for the later Cochrane
projects.

Three results are restated from the Woodford Chapter 4 project (`NeoWicksellianFramework`,
module `InvariantSplit`): the complex eigenvalues of a real matrix and the Gelfand bound that
decaying powers follow from eigenvalues in the open unit disc (`VARIdentities.eigs`,
`VARIdentities.map_ofReal_pow`, `VARIdentities.powDecay_of_eigs`). They give the book's "the
eigenvalues of `A` are less than one" its exact content.

Within the Cochrane projects, `LinearizedIdentities` and `LinearizationDerivation` prove again,
locally, the §3.5 identities and their A1 derivations that the Chapter 3 project (`Generality`,
module `LogLinearIdentities`) also proves; nothing is imported. The versions here are adapted to
Chapter 4: the identities are stated with ordinary convergence and for moving averages with
`|ρ| ≤ 1`, including `ρ = 1`, where the Chapter 3 project works with bounded processes and
`0 < ρ < 1`. E22 and E23 of this project are the same two A1 corrections that the Chapter 3
project records under the codes of the Chapters 1–3 survey. No Woodford or Galí result is linked by
a link theorem: the `Links` module links this project's own modules, and the survey's proposed
links to Woodford's fiscal theory and to the Chapter 5 surplus process ((2.1) = (5.22)) are not
made.

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
