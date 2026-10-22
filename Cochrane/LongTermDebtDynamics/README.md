# Long-term debt dynamics in Lean

This is the `Cochrane/LongTermDebtDynamics/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Chapter 7, "Long-term debt dynamics" (pp. 212–236), together with the
two parts of the Online Appendix that the chapter relies on: §A1.2.1, the geometric-maturity and
forward-guidance formulas (pp. 559–561), and §A1.14, the three-period economy with expected
future bond sales (pp. 588–592). The setting is the book's: flexible prices, a constant real rate
`1/β`, risk-neutral bond prices `Q_t^{(t+j)} = β^j E_t(P_t/P_{t+j})` and zero-coupon nominal debt
of every maturity. The structural results (the flow and present-value relations, the buffer,
bond sales, the general formula, Theorem P and maturity-structure irrelevance) hold for an
arbitrary `ExpectationSystem` with the pull-out property, so under perfect foresight and under
genuine uncertainty. Eleven further modules take the book's deterministic passages (forward
guidance, §7.6.1, §A1.14) to uncertainty and settle existence in §7.4. The library contains
**438 theorems**, including the shared core; 197 of them are in the eight chapter modules and 133
in the eleven further modules.

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises. "Theorem W" (the general formula
(7.17)) and "Theorem P" (the policy constraint of §7.5) are the labels of the chapter survey.

Headline results, in the namespace `Cochrane.LongTermDebtDynamics`:
* **Flow and present value.** The nominal flow condition (3.2) is the real flow condition (7.1)
  (`MaturityStructure.nominalFlow_iff_realFlow`). With bounded surpluses, the flow conditions at
  every date plus the transversality conditions are equivalent to the present-value relations
  (7.2) at every date (`MaturityStructure.flow_tvc_iff_presentValue`), and a bounded real value of
  debt makes the transversality condition automatic (`MaturityStructure.presentValue_of_bounded`).
* **Forward guidance.** Guidance has a smaller effect than the same immediate rise, and the
  effect falls with the horizon (`ForwardGuidance.priceLevel_immediate_le`,
  `ForwardGuidance.priceLevel_mono`). Guidance that reaches the longest maturity `k` has no effect
  already for `T ≥ k`, not only for the printed `T > k`, and `T ≥ k` is sharp
  (`ForwardGuidance.priceLevel_fg_of_le`, `ForwardGuidance.priceLevel_fg_lt`). The price level
  does not jump a second time when the rate rises (`ForwardGuidance.fgPath_eq_of_le`,
  `ForwardGuidance.fgPath_jump`). The Online Appendix formulas behind Figure 7.1 are proved in
  discrete time, as genuine convergent series (`ForwardGuidance.fg_jump_geometric`), and in
  continuous time, as genuine improper integrals (`ForwardGuidance.integral_cfg`,
  `ForwardGuidance.cfg_jump`), with their comparative statics.
* **Forward guidance under uncertainty.** With random surpluses and a rate path known at date 0,
  the bond-price display, the valuation equation (7.3), the three comparative statics of §7.1 and
  the discrete jump of p. 560 all hold state by state
  (`TidyR5GuidanceUncertainty.stoch_fgPrice`, `TidyR5GuidanceUncertainty.stoch_fg_no_effect`,
  `TidyR5GuidanceUncertainty.stoch_fg_lowers`, `TidyR5GuidanceUncertainty.stoch_fg_mono`,
  `TidyR5GuidanceUncertainty.stoch_fg_jump`). The book's price path is then the path of
  `E_0(1/P_j)`, and "no second jump" becomes `E_t(P_t/P_{t+1}) = 1` before `T`
  (`TidyR5GuidanceUncertainty.stoch_E0_path`, `TidyR5GuidanceUncertainty.stoch_no_expected_jump`).
  With a state-contingent rate path, bond prices carry a covariance term
  (`TidyR5RandomGuidance.bondPrice_cov_rate`). Guidance with `T ≥ k` still has no effect
  (`TidyR5RandomGuidance.random_fg_no_effect`), but all three comparative statics fail, with
  counterexamples: a higher expected rate path can raise `P_0`
  (`TidyR5RandomGuidance.cg_counterexample`), and the earlier of two announcements can give the
  higher price level, against both monotonicity in the horizon and the immediate-rise comparison
  (`TidyR5RandomHorizon.cg_horizon_counterexample`).
* **The buffer and runs.** With no sales after date 0, `B_{−1}^{(t)}/P_t = s_t` (7.6), so
  unexpected inflation reflects only news about the current surplus while news about later
  surpluses moves bond prices (`MaturingDebt.price_eq_maturing`, `MaturingDebt.noSales_price_news`,
  `MaturingDebt.noSales_bond_news`). With one-period debt, the backward induction of p. 219 is a
  theorem, and fear of low far-future surpluses raises today's price level
  (`MaturingDebt.oneperiod_backward`, `MaturingDebt.oneperiod_fear`).
* **Bond sales.** The dilution formula (7.12) as a convergent series (`BondSales.dilution_formula`).
  With no long-term debt outstanding, `P_0` does not depend on sales
  (`BondSales.no_outstanding_price_indep`); with long-term debt outstanding, more sales lower
  `P_0` (`BondSales.outstanding_sales_lower_price`). A bond-price target is supported by a finite,
  unique quantity with unit elasticity (`BondSales.bondPrice_target_iff`,
  `BondSales.unit_elasticity`). In the three-period economy of §A1.14 the effect of expected
  future sales on `P_0` has the sign of `A₁ − A₂` (`FutureSales.x0_strictMono`,
  `FutureSales.x0_strictAnti`, `FutureSales.x0_const`). The derivative and the sign rule also
  hold with random debt, random surpluses and state-contingent future sales
  (`TidyR5FutureSalesRandom.hasDerivAt_x0R`, `TidyR5FutureSalesRandom.x0R_mono`,
  `TidyR5FutureSalesRandom.x0R_anti`, `TidyR5FutureSalesRandom.x0R_const`). The innovation form
  of (7.12) holds at every date, corrected (E7.9): there is no unexpected inflation exactly when
  surplus news is offset by news in the dilution terms (`TidyR5InnovationForm.innovation_at`,
  `TidyR5InnovationForm.no_surprise_iff`, `TidyR5InnovationForm.innovation_rowR`).
* **The general formula (Theorem W).** Cochrane's recursively defined weights are sums over
  strictly increasing chains of sale fractions (`GeneralFormula.weight_eq_chainSum`). (7.17) is
  an exact identity in every economy whose debt matures by a finite date
  (`GeneralFormula.theoremW_finite`), and with an infinite horizon under a row condition on the
  sale fractions (`GeneralFormula.theoremW`), also with random bounds
  (`TidyR5SeriesExchange.theoremW_rowR'`). `E_t` passes through every absolutely convergent
  series for every `ExpectationSystem`: this is a theorem of the axioms, not a hypothesis
  (`TidyR5SeriesExchange.seriesExchange`). It reduces to (7.6) and to the standard present
  value in the two special cases of §7.4 (`GeneralFormula.special_noSales`,
  `GeneralFormula.special_onePeriod`).
* **When the present-value system determines the price level (settled).** See the next section.
* **Constraints on policy (Theorem P).** For any positive targets `E_0(1/P_j)` consistent with
  the date-0 present-value relation (7.18), the policy (7.19) satisfies every flow and
  present-value relation and achieves the targets (`PolicyConstraints.polOne_achieves`,
  `PolicyConstraints.polOne_flow`, `PolicyConstraints.polOne_presentValue`). The roll-over policy
  (7.20) achieves the same targets with a different debt path
  (`PolicyConstraints.policies_differ`), and every equilibrium satisfies (7.18)
  (`PolicyConstraints.presentValue_zero_nominal`). With nonnegative positions, debt policy cannot
  raise some price levels without lowering others (`PolicyConstraints.qe_tradeoff_strict`); with
  a negative position it can (`PolicyConstraints.qe_negative_position`).
* **Quantitative easing.** (7.22)–(7.24) (`QuantitativeEasing.steady_state`,
  `QuantitativeEasing.pv_iff_723`, `QuantitativeEasing.pv_iff_724`). Given the price path, the
  reserves supporting given QE purchases are unique and explicit
  (`QuantitativeEasing.reserves_formula`); the QE purchases supporting given reserves are unique
  (`QuantitativeEasing.qe_unique`) and exist if and only if a tail condition holds, which bounded
  paths satisfy and which can fail (`QuantitativeEasing.qe_exists`,
  `QuantitativeEasing.qe_exists_necessary`, `QuantitativeEasing.qe_counterexample`). Only the
  total market value of debt matters (`QuantitativeEasing.Irrelevance.maturity_irrelevance`).
  Under uncertainty both directions of the reverse engineering of p. 230 have exact conditions:
  predetermined reserves exist iff the implied reserves are known one period ahead
  (`TidyR5QEUncertainty.reserves_exist_iff`), and date-0 QE purchases exist iff every implied
  purchase is known at date 0 (`TidyR5QEReverse.qe_exists_iff`). Surplus news defeats both: a
  coin-flip surplus shock admits neither for a deterministic path
  (`TidyR5QEUncertainty.coin_no_reserves`, `TidyR5QEReverse.coin_no_qe`).

## The §7.4 uniqueness question, settled

On p. 225 the book writes the present-value relations as an infinite upper-triangular linear
system `Bp = Rs` (7.16) and its solution as `p = B⁻¹Rs`, and then gives the weighted present value
(7.17) as "a pretty formula" for it. The chapter survey flagged this as its one open question
(E7.4): an infinite triangular system can have a nonzero bounded kernel, so it was not clear when
the flow and present-value relations determine the price level at all. Formalisation settles it.
Write `y_t = B_{t−1}^{(t)}/P_t` and `A_t^{(m)} = (B_t^{(m)} − B_{t−1}^{(m)})/B_{m−1}^{(m)}` for
the fraction of the debt due at `m` that is sold at `t` (`GeneralFormula.fracSold`).

1. **A counterexample: the price level is not determined in general.** Let one unit of debt
   mature at every date and `2/β` units be due the next date, `B_{t−1}^{(t)} = 1`,
   `B_{t−1}^{(t+1)} = 2/β` (`GeneralFormula.cxD`), with a constant surplus `s > 0` and
   `0 < β < 1`. Every path `1/P_t = x* + ε(−1/2)^t` with `x* = s/(3(1 − β))` satisfies every flow
   condition and every present-value relation (`GeneralFormula.cx_flow`,
   `GeneralFormula.cx_presentValue`). For `|ε| < x*` the price levels are positive and bounded
   (`GeneralFormula.cx_pos`, `GeneralFormula.cx_bounded`), and different `ε` give different paths
   (`GeneralFormula.cx_ne`). Debt is nonnegative and the transversality condition holds, so
   positivity, boundedness and the present-value relations together do not pin down `P`. The
   weights are `W^{(k)} = (β + 2(−2/β)^k)/(β + 2)`, so `β^kW^{(k)}` does not tend to zero and
   (7.17) diverges (`GeneralFormula.cx_weight`, `GeneralFormula.cx_formula_diverges`).
2. **Sufficient condition (a): no buy-backs.** Suppose the government never buys back debt
   (`B_t^{(m)} ≥ B_{t−1}^{(m)}` for `t < m`), inherited positions are nonnegative and the debt
   coming due is positive (`GeneralFormula.NoBuyback`), surpluses are bounded and `0 < β < 1`.
   Then two positive price-level paths that both satisfy every flow condition and every
   present-value relation coincide, under uncertainty (`GeneralFormula.price_unique_noBuyback`).
   No summability hypothesis on the debt policy is needed: the present-value relations bound the
   real value of maturing debt (`GeneralFormula.bounded_of_presentValue`), and the homogeneous
   system has no nonzero bounded solution because each column of sale fractions sums to at most
   one (`GeneralFormula.NoBuyback.col_le_one`, `GeneralFormula.col_lemma`,
   `GeneralFormula.unique_of_noBuyback`).
   Existence has an exact condition, given predetermined debt and that quotients of known
   variables are known (`PolicyConstraints.DivClosed`). Without buy-backs (7.17) converges and solves the flow system
   with no row condition, because every weight lies in `[0, 1]`
   (`TidyR5NoBuybackExistence.weight_mem_unit`, `TidyR5NoBuybackExistence.formulaW_solves_noBuyback`).
   A positive equilibrium exists if and only if (7.17) is strictly positive at every date and
   state, and it is then `1/P_t = E_t∑_m β^mW_t^{(m)}s_{t+m}/B_{t−1}^{(t)}`
   (`TidyR5NoBuybackExistence.exists_equilibrium_iff`,
   `TidyR5NoBuybackExistence.maturing_eq_formulaW`). Positive bounded surpluses suffice
   (`TidyR5NoBuybackExistence.existsUnique_of_pos_surplus`). No buy-backs alone do not: with one
   unit due at every date, no trading, `s_0 = −1` and `s_t = 1` afterwards, no positive `P_0`
   exists although the date-0 present value of surpluses is positive for `β > 1/2`
   (`TidyR5NoBuybackExistence.cb_no_positive_price`, `TidyR5NoBuybackExistence.cb_pv_pos`).
3. **Sufficient condition (b): the row condition.** Suppose the sale fractions are bounded by a
   deterministic sequence, `|A_t^{(t+j+1)}| ≤ a_j`, with `∑_j β^{j+1}a_j ≤ ρ < 1`
   (`GeneralFormula.RowBound`). Then bounded solutions are unique
   (`GeneralFormula.unique_of_row`, `GeneralFormula.price_unique_row`), (7.17) converges
   absolutely, and it is the price level (`GeneralFormula.theoremW`,
   `GeneralFormula.price_formula`). The bounds may be random and date-dependent, and need not be
   adapted: it suffices that `∑_j β^{j+1}|A_t^{(t+j+1)}(ω)| ≤ ρ < 1` at every date and state
   (`TidyR5RandomRow.RowBoundR`), which is strictly weaker even under perfect foresight
   (`TidyR5RandomRow.sx_not_rowBound`). Then (7.14) has exactly one bounded solution for every
   `ExpectationSystem` (`TidyR5RandomRow.existsUnique_bounded_solution`), and it is (7.17), with
   no interchange hypothesis (`TidyR5SeriesExchange.theoremW_rowR'`,
   `TidyR5SeriesExchange.price_formula_rowR'`).
4. **The criterion.** Given one bounded solution, bounded solutions are unique if and only if the
   homogeneous system `d_t = ∑_j β^{j+1}E_t(A_t^{(t+j+1)}d_{t+j+1})` has no nonzero bounded
   solution (`GeneralFormula.unique_iff_homogeneous`, `GeneralFormula.homogeneous_of_two`).

The counterexample violates both sufficient conditions: it buys back debt every period
(`GeneralFormula.cx_buyback`), and no bound satisfies the row condition, since the row sum is at
least `2 + β` (`GeneralFormula.cx_not_row`). The difference `ε(−1/2)^t` of two of its price paths
is exactly the nonzero bounded homogeneous solution that the criterion rules out. The survey's
candidate condition, nonnegative sale fractions plus absolute summability, is replaced by two
proved conditions that each ask for less: no buy-backs without any summability hypothesis, or
the row condition without any sign restriction on sales. Neither condition is shown to be
necessary.

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections are the confirmed errors of the chapter survey and
those found during formalisation:
* "`p = B⁻¹Rs`" (7.16), p. 225, does not determine the price level in general, and (7.17) can
  diverge; the counterexample and the two sufficient conditions above (E7.4);
* the present-value relation (7.15), p. 225, omits the discount factors `β^j` (E7.2), and the
  matrix display (7.16) starts each row one index too late and also omits `β^{m−t}` (E7.3);
* forward guidance beyond the longest maturity has no effect already for `T ≥ k`, not only for
  `T > k`, p. 214 (E7.6);
* Theorem P, pp. 227–228, needs positive targets known at date 0, positive surpluses and the fact
  that quotients of known variables are known (E7.7); "QE … not possible", p. 228, needs
  nonnegative positions in every maturity (E7.8);
* "a one percent decrease in bond supply gives … a one percentage point decrease in bond price",
  p. 233, has the wrong sign: the bond price rises by about 1% (found during formalisation);
* the reverse engineering of p. 230, "given `M`, solve for `B̃`", can fail: the QE purchases are
  unique when they exist, but exist only under a tail condition (found during formalisation).
  Both directions of p. 230 rely on perfect foresight, the book's own assumption ("I drop `E_0`"):
  under uncertainty reserves exist iff the implied reserves are known one period ahead, and QE
  purchases fixed at date 0 exist iff every implied purchase is known at date 0, so surplus news
  defeats both (a precision, not an error);
* the comparative statics of §7.1, pp. 213–214, hold for a rate path known at date 0 but fail for
  a state-contingent one: a higher expected rate path can raise `P_0`, and an earlier
  announcement can give the higher price level (a precision: the book's §7.1 is deterministic).

In addition, the labels (7.14) and (7.15) are swapped in the text (E7.1), the innovation display
of p. 224 mixes the dates `0` and `t` and is corrected at a general date (E7.9), the "25%" drop of
p. 560 is about 24.3% in discrete time (E7.11), and the reference to (1.67) on p. 592 should be to
(1.66) (E7.10). An earlier version of this README listed existence of an equilibrium under no
buy-backs alone as open; it is false, and the exact condition replaces it (see the §7.4 section
above and the last section of the corrections).

Not formalised:
* §7.7, the U.S. maturity structure (pp. 234–236), and Figures 7.6–7.7, which are data. The other
  figures are illustrations; the formulas behind them are formalised, and the Figure 7.1
  calibration numbers are checked (`ForwardGuidance.fgJump_calibration`);
* the discursive passages: the run, rollover-crisis and default narrative of §7.2.2 (pp. 219–220,
  only the backward recursion and its monotonicity are theorems), the remarks after Theorem W on
  focusing on interest-rate targets (p. 226), the precommitment and empirical-QE discussion of
  §7.6.2 (pp. 232–234) and the summary §7.6.3;
* Theorem W with an infinite horizon under neither the row condition nor no buy-backs: it is false
  in general (the counterexample above);
* the continuous-time forward-guidance formula of §A1.2.1 (p. 561) under uncertainty: by the
  project's conventions continuous time is deterministic (no stochastic calculus). The discrete
  formula of p. 560 is proved state by state (`TidyR5GuidanceUncertainty.stoch_fg_jump`);
* for state-contingent guidance, "equilibrium" means, as in the book's §7.1, the Fisher relation
  at every date plus the date-0 valuation equation (7.3); flow conditions at later dates under a
  specified debt policy are not imposed in the counterexamples;
* with random debt in §A1.14, the strict sign rule is proved only under uniform positive lower
  bounds (`TidyR5FutureSalesRandom.x0R_strictMono`), because an abstract `ExpectationSystem` need
  not be strictly positive; under the book's sign conditions alone the weak versions are proved
  (`TidyR5FutureSalesRandom.x0R_mono`, `TidyR5FutureSalesRandom.x0R_anti`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](LongTermDebtDynamics/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (shared core, restated from the earlier projects) |
| [Expectations](LongTermDebtDynamics/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; bounded adapted processes; forward series; the pull-out property (shared core) |
| [ExpectationsFiniteTree](LongTermDebtDynamics/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; coin-flip examples (shared core) |
| [ForwardSolution](LongTermDebtDynamics/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [MaturityStructure](LongTermDebtDynamics/MaturityStructure.lean) | 15 | Pp. 212–213, 216: debt arrays, predetermined debt, bond prices, (3.2)/(3.3) recalled, the flow condition (7.1)/(7.4), the present-value relation (7.2)/(7.5), and flow plus transversality iff present value |
| [ForwardGuidance](LongTermDebtDynamics/ForwardGuidance.lean) | 37 | §7.1, (7.3), and §A1.2.1: forward-guidance bond prices and the price path, `T ≥ k` sharp, monotonicity in the horizon, the discrete and continuous closed forms with comparative statics, the Figure 7.1 calibration, the perpetuity ratio, steady-state sales |
| [MaturingDebt](LongTermDebtDynamics/MaturingDebt.lean) | 14 | §§7.2.1–7.2.2, (7.6)–(7.7): no sales and the buffer, one-period debt, the backward-induction recursion and fear of future surpluses |
| [BondSales](LongTermDebtDynamics/BondSales.lean) | 15 | §§7.3–7.3.2, (7.8)–(7.13): sales at date 0 only, the dilution formula, no outstanding debt, bond-price targets and unit elasticity, sales with outstanding debt, offsetting a surplus shock |
| [FutureSales](LongTermDebtDynamics/FutureSales.lean) | 18 | §7.3.3 and §A1.14, (1.63)–(1.68): the three-period economy, symmetry and interaction effects, the sign of the effect of expected sales on `P_0` |
| [GeneralFormula](LongTermDebtDynamics/GeneralFormula.lean) | 52 | §7.4, (7.14)–(7.17): the weights and their chain-sum form, Theorem W (finite and infinite horizon), uniqueness without buy-backs and under the row condition, the homogeneous-system criterion, the special cases, (7.15) and (7.16) corrected, the non-uniqueness counterexample |
| [PolicyConstraints](LongTermDebtDynamics/PolicyConstraints.lean) | 29 | §7.5, (7.18)–(7.21): Theorem P with the policies (7.19) and (7.20), one-period debt, the QE trade-off and its sign hypothesis, offsetting a fiscal shock, the end-of-period value of debt |
| [QuantitativeEasing](LongTermDebtDynamics/QuantitativeEasing.lean) | 17 | §7.6, (7.22)–(7.24): the geometric steady state, reverse engineering of reserves and of QE purchases (uniqueness, existence and its failure), maturity-structure irrelevance, strong QE |
| [TidyR5Pathwise](LongTermDebtDynamics/TidyR5Pathwise.lean) | 7 | §7.4, (7.14)/(7.17): the pathwise weighted present value solves the flow system state by state; (7.17) solves it given the interchanges |
| [TidyR5NoBuybackExistence](LongTermDebtDynamics/TidyR5NoBuybackExistence.lean) | 17 | §7.4: without buy-backs the weights lie in `[0, 1]` and (7.17) solves the flow system; a positive equilibrium exists iff (7.17) > 0 everywhere; positive surpluses suffice; no buy-backs alone do not (counterexample) |
| [TidyR5RandomRow](LongTermDebtDynamics/TidyR5RandomRow.lean) | 23 | §7.4: the row condition with random bounds; existence and uniqueness of the bounded solution for every expectation system; Theorem W given `SeriesExchange`; strictly weaker than deterministic bounds |
| [TidyR5FutureSalesRandom](LongTermDebtDynamics/TidyR5FutureSalesRandom.lean) | 17 | §A1.14, (1.63)–(1.68): random debt and state-contingent future sales; the derivative of `1/P_0`, the sign rule, (1.64) |
| [TidyR5GuidanceUncertainty](LongTermDebtDynamics/TidyR5GuidanceUncertainty.lean) | 14 | §7.1, (7.3), and §A1.2.1 (discrete) under uncertainty with a rate path known at date 0: bond prices, the expected path, the comparative statics and the jump, state by state |
| [TidyR5QEUncertainty](LongTermDebtDynamics/TidyR5QEUncertainty.lean) | 8 | §7.6.1 under uncertainty, "given `B̃`, find `M`": reserves exist iff known one period ahead; the innovation form; surplus news defeats a deterministic path |
| [TidyR5SeriesExchange](LongTermDebtDynamics/TidyR5SeriesExchange.lean) | 10 | §7.4: `E_t` passes through absolutely convergent series for every expectation system; Theorem W with random bounds and no interchange hypothesis |
| [TidyR5InnovationForm](LongTermDebtDynamics/TidyR5InnovationForm.lean) | 7 | §7.3.2, (7.12), p. 224: the dilution formula and its innovation form at every date (E7.9 corrected); the general-policy innovation form |
| [TidyR5QEReverse](LongTermDebtDynamics/TidyR5QEReverse.lean) | 7 | §7.6.1 under uncertainty, "given `M`, find `B̃`": uniqueness, the exact existence condition, the coin-flip counterexample |
| [TidyR5RandomGuidance](LongTermDebtDynamics/TidyR5RandomGuidance.lean) | 18 | §7.1 with a state-contingent rate path: the covariance decomposition of bond prices, what survives, and the counterexample to "a rate rise lowers `P_0`" |
| [TidyR5RandomHorizon](LongTermDebtDynamics/TidyR5RandomHorizon.lean) | 5 | §7.1, p. 213: the counterexample to monotonicity in the horizon and to the immediate-rise comparison for state-contingent guidance |

## Modelling conventions

* **Debt arrays and dates.** Dates are natural numbers. `D t m` is the face value of debt due at
  date `m` that is outstanding at the start of date `t`, the book's `B_{t−1}^{(m)}`. So the
  inherited structure `B_{−1}^{(m)}` is `D 0 m`, the end-of-period stock `B_t^{(m)}` is
  `D (t + 1) m`, and sales are `D (t + 1) m − D t m` (`MaturityStructure.sales`). Debt is
  predetermined: `D 0 m` is known at date 0 and `D (t + 1) m` at date `t`
  (`MaturityStructure.Predetermined`).
* **The price variable.** As Cochrane recommends, the primitive variable is `x_t = 1/P_t`, so
  every system is linear. Where `P` itself appears, `P_t x_t = 1` is a hypothesis. Bond prices
  are risk-neutral, `Q_t^{(t+j)} = β^j E_t(P_t/P_{t+j})` (`MaturityStructure.bondPrice`).
* **Expectations.** Random variables are `Ω → ℝ` under an arbitrary `ExpectationSystem`; results
  that move known quantities through `E_t` assume `ExpectationSystem.PullOut`. A variable is known
  at `t` when `E_t x = x`, and a process is adapted when it is known at every date
  (`ExpectationSystem.Adapted`). The policy (7.19) divides known variables, so Theorem P also
  assumes `PolicyConstraints.DivClosed`, proved for perfect foresight and for every finite event
  tree (`PolicyConstraints.perfectForesight_divClosed`, `PolicyConstraints.finiteTree_divClosed`).
  In the chapter modules forward guidance (§7.1, §A1.2.1), §7.6.1 and strong QE are
  deterministic, as in the book; the counterexample and the printed (7.15) are under perfect
  foresight (`perfectForesight`). The further modules redo forward guidance (except the
  continuous-time formula), §7.6.1 and §A1.14 with random surpluses, price levels and debt, and
  their counterexamples live on a finite coin-flip tree.
  `E_t` passes through every absolutely convergent series, for every `ExpectationSystem`
  (`TidyR5SeriesExchange.seriesExchange`), because `E_t` is linear and monotone on unbounded
  random variables too; no countable-additivity hypothesis is needed.
* **Infinite sums.** Every infinite sum is a genuine `HasSum` or `tsum` with an explicit
  summability or domination hypothesis (`MaturityStructure.DebtDominated`), never a junk value.
  The continuous-time formula of §A1.2.1 is an improper integral on `(0, ∞)`.
* **Equilibrium and uniqueness.** There is no single equilibrium structure. A price path is
  checked against the flow condition at every date (`MaturityStructure.RealFlow`) and, where
  stated, the present-value relation at every date (`MaturityStructure.PresentValue`). In §7.4
  the flow conditions are the maturing-debt system for `y_t = B_{t−1}^{(t)}/P_t`
  (`GeneralFormula.MaturingSystem`, `GeneralFormula.realFlow_iff_maturingSystem`). "The price
  level is determined" means that two adapted paths satisfying these conditions coincide, among
  positive paths (no buy-backs) or among paths with bounded real maturing debt (row condition).
* **Explicit hypotheses.** Hypotheses the book leaves implicit are stated in each theorem:
  `0 ≤ β < 1` (`0 < β < 1` for uniqueness without buy-backs), bounded surpluses, nonzero debt
  coming due wherever the book divides by it, `B_0^{(j)} ≠ 0` in (7.12), each sale fraction
  `A_t^{(t+j+1)}` known at `t + j` in Theorem W, `−1 < r < i` and `0 ≤ ω < 1 + r` for forward
  guidance, and the positivity conditions of Theorem P (`PolicyConstraints.Targets`).

## Relation to the Woodford and Galí projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects (the first three from `Woodford/ReturnOfMonetaryRules`,
`ForwardSolution` from the Woodford Chapter 2 and 3 projects), so the project builds on its own.
Nothing is imported from those projects. The chapter modules use only part of the core:
`ExpectationSystem`, `ExpectationSystem.PullOut`, `ExpectationSystem.Adapted`,
`ExpectationSystem.E_E_self`, `ForwardSolution.E_of_known` and `ForwardSolution.E_tsum_dom`
throughout, `perfectForesight` for the counterexample, and the finite event tree
(`ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E`) for
`PolicyConstraints.finiteTree_divClosed`; the further modules also use the finite event tree for
their coin-flip counterexamples. `Determinacy` and the forward-series theory are carried
for the later Cochrane projects.

No Woodford or Galí result is restated in a chapter module, and there is no link module. Three
correspondences are recorded here without a link theorem:
* `MaturityStructure.flow_tvc_iff_presentValue` is the long-debt analogue of Woodford's
  equivalence of the intertemporal budget constraint with the flow constraints plus
  transversality (Chapter 2, `PriceLevelDetermination`, `ibc_eq_iff_flow_eq_and_tvc`). It is
  proved directly for the maturity structure, not restated;
* the uniqueness argument under the row condition (`GeneralFormula.unique_of_row`) is the
  infinite-system version of the contraction argument behind `ForwardSolution.existsUnique_bounded`
  (`|a| < 1`), and the counterexample's kernel `(−1/2)^t` is a bounded homogeneous solution of the
  same kind as `ForwardSolution.sunspotFamily` for `|a| > 1`;
* within the Cochrane projects, one-period debt connects the chapter to the earlier valuation
  equations: the last two steps of the backward induction (`MaturingDebt.oneperiod_two_period`)
  are the two-period valuation of Chapter 1 (`TwoPeriodModel`), and pure roll-over
  (`GeneralFormula.special_onePeriod`) gives the standard present value of Chapter 2
  (`IntertemporalModel`). Both are proved here for the maturity structure, not imported.

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
