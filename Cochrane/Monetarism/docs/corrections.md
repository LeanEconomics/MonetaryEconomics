# Corrections to the source

This file lists places where a claim in Chapter 19 (with the precise claims of Chapter 11, §14.1
and Online Appendix §1.6 and Chapters 3–4) of Cochrane (2023), *The Fiscal Theory of the Price
Level*, is false, imprecise, or relies on an unstated hypothesis, and where the Lean statement
departs from the printed one. In each case the Lean statement proves the stated version and
cites the original.

Codes E13–E23 are the Chapter 19 and Online Appendix Chapters 3–4 items of the survey of Chapters
11–19 (`notes/survey_cochrane_ch11-19.md`). Each was confirmed or refuted by formalisation before
being recorded here, and an entry is revised if formalisation shows the finding itself to be
wrong. The survey marked E21's (4.15) item and E23 as suspected; formalisation confirms both.
E13 and E17 turn out to be one misprinted condition (`Links.e13_iff_e17`). The formalisation also
found the errors in (19.29), (19.38) and the partial derivatives of p. 631, which the survey did
not list. Several claims that the book asserts without proof turned out to be correct; they are
listed in the last section.

Out of scope are the verbal passages: the discussion of §19.4 (pp. 445–447) beyond the claims
formalised from Online Appendix Chapter 3, the history of §19.8 beyond Baumol–Tobin, the LM slope
and E23, the literature survey of A3 §3.1.4 (where the `µ` quoted from Buiter and Siebert is
gross money growth, a notation clash recorded under E17), the interpretation of A3 §3.2.3 and
§3.3. The survey's suspicion that the time axis of Figure 3.2 is shifted by one period (E18) was
not checked. Lean names are relative to the namespace `Cochrane.Monetarism`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| pp. 444–445 (E13) | The deflationary steady state is stable when money growth is "positive, or mildly negative `1 + µ > 1/β`, i.e. approximately `µ > −δ`". | The condition is `1 + µ > β`, i.e. `µ > −δ/(1 + δ) ≈ −δ`. Under it the inflationary steady state `x̄` exists and `x_{t+1}/x_t → β/(1 + µ) < 1` near `x = 0` (`MoneyInUtility.e13_corrected`); every path started below `x̄` converges to `x = 0` (`MoneyTargetingDynamics.power_deflation_orbit`). If `1 + µ ≤ β` no path converges to `x = 0` (`MoneyTargetingDynamics.e13_no_deflation_attractor`). The printed condition is not necessary: `β = 5/6`, `µ = 0` satisfies `1 + µ > β` but not `1 + µ > 1/β` (`MoneyInUtility.e13_printed_fails`). |
| p. 453 (E14) | "The nominal interest rate is nonnegative, `Q_t ≥ 1`." | It is `Q_t ≤ 1` (`CashInAdvance.MoneyDemand.Q_le_one_iff`); the printed condition says the rate is non-positive (`CashInAdvance.MoneyDemand.E14_one_le_Q_iff`). The book's own example has `Q = β < 1` (`CashInAdvance.PF.E14_example`). At `Q > 1` the household has no optimal money holding (`CashInAdvance.MoneyDemand.no_optimum_of_one_lt`). |
| p. 450 (E15) | "If the endowment is constant … `Λ_{t+j}/Λ_t = βʲ`; `Q = β`." | `Q_t = βP_t/P_{t+1}`, which is `β` iff the price level is constant (`CashInAdvance.PF.bondPrice_eq_beta_iff`). In the standard money-growth equilibrium `Q = β/(1 + µ) ≠ β` for `µ ≠ 0` (`CashInAdvance.PF.E15_counterexample`, `CashInAdvance.PF.bondPrice_growth`). |
| A3 pp. 612–613, 617 (E17) | The transversality objection "only applies to … `µ > 0`"; "if money growth is negative `µ ≤ 0`, deflationary equilibria survive"; survival for "`−δ < µ < 0`" or "`−δ ≤ µ < 0`". | Along a deflation the transversality condition fails iff `µ ≥ 0` (`PruningDeflation.tvc_tendsto_zero_iff`): at `µ = 0` the term tends to a positive constant (`PruningDeflation.tvc_mu_zero`). Deflationary equilibria form a continuum iff `β < 1 + µ < 1` (`PruningDeflation.deflation_continuum`), and for `1 + µ ≤ β` there is no deflationary path at all (`PruningDeflation.no_deflation_of_le_beta`). So the range is `−δ/(1 + δ) < µ < 0`, not `−δ < µ < 0`: `δ = 1`, `µ = −0.6` satisfies the printed range but `1 + µ < β` (`PruningDeflation.survival_threshold`, `PruningDeflation.survival_counterexample`). This is E13's condition (`Links.e13_iff_e17`). |
| A3 p. 624, Figure 3.2 caption (E18) | "`v(m) = m^{−1/2}`" | It must be `v′(m) = m^{−1/2}`, i.e. `v = 2√m` (`ObstfeldRogoff.e18_correct_v`). The caption's `v` is decreasing (`ObstfeldRogoff.e18_caption_decreasing`) and admits neither the steady state `m = 4` nor the terminal level `M/P̄ = 1` (`ObstfeldRogoff.e18_no_steady_state`). With `v′ = m^{−1/2}` every plotted number is verified (`ObstfeldRogoff.fig32_numbers`). |
| A3 pp. 631–632 (E19) | `m_{t+1}/m_t ≈ 1 + (b/a)(1/(1 − b))(m_t − m̄)/m̄²`; "negative for `b > 1`. In that case, dynamics are stable." | The coefficient misses the factor `1 + i = (1 + δ)(1 + µ)` (`Nonseparable.obs_ratio_hasDerivAt`, `Nonseparable.e19_printed_coefficient`). The map has slope `1 − i/(b − 1)` (`Nonseparable.obs_map_hasDerivAt`). It cuts from above iff `b > 1` (`Nonseparable.obs_cuts_from_above_iff`), but it is stable iff `b > 1 + i/2` (`Nonseparable.obs_stable_iff`). With `b = 1.04` and `i = 0.1025` the slope is `−1.5625` (`Nonseparable.e19_counterexample`), and for `1 < b < 1 + i/2` the steady state is locally unique (`Nonseparable.obs_locally_unique`). For `b > 1 + i/2` the continuum of stable equilibria satisfying the transversality condition exists (`Nonseparable.obs_multiple_stable`). |
| A4 p. 636 (E20) | (4.6): as `θ → 1` the CES utility tends to `[c^{1/(1+α)}m^{α/(1+α)}]^{1−γ}/(1 − γ)`; as `θ → ∞` it tends to `min(c, αm)`, with `M/P = c/α`, "i.e. `α = 1/V`". | (4.6) holds for the aggregator normalised by `1 + α` (`ContinuousTime.ces_norm_limit`, `ContinuousTime.ces_norm_utility_limit`); the printed aggregator is `(1 + α)^{1/(1−θ)}` times it, diverges and has no limit (`ContinuousTime.ces_unnorm_eq`, `ContinuousTime.ces_unnorm_diverges`, `ContinuousTime.ces_unnorm_no_limit`). With fixed `α` the `θ → ∞` limit is `min(c, m)` and money demand tends to `m/c = 1` (`ContinuousTime.ces_limit_min`, `ContinuousTime.demand_limit_fixed`); `min(c, αm)` and `M/P = c/α` need the coefficient `α^{−θ}` (`ContinuousTime.ces_limit_min_corrected`, `ContinuousTime.demand_corrected_limit`). Finally `M/P = c/α` means `V = α` (`ContinuousTime.velocity_of_demand`), so `α = 1/V` holds only for `α = 1` (`ContinuousTime.alpha_eq_inv_V_iff`). |
| A4 pp. 639–640 (E21) | (4.13) `ẋ + (σ − ξ)(m/c)·d(i − i^m)/dt = σ(i − π)`; (4.14); (4.15) `E_tx_{t+1} − x_t = σ(i_t − π_t)`. | The exact equation is `ẋ + (σ − ξ)(m/c)/(1 + A)·d(i − i^m)/dt = σ(i − π − δ)` (`ContinuousTime.is_exact`, `ContinuousTime.is_curve_exact`). (4.13) and (4.14) drop `−δσ`, so the printed (4.13) is false at any steady state with `σδ ≠ 0` (`ContinuousTime.E21_steady_state`) and right only for deviations (`ContinuousTime.E21_deviations`, `ContinuousTime.is_4_14_exact`). (4.15) contradicts the book's discrete (4.13) unless `E_tπ_{t+1} = π_t`, so it should use `E_tπ_{t+1}` (`ContinuousTime.E21_discrete_inconsistent`). |
| A3 p. 619 (E22) | "For `P_0y/M_0 > PM/M`, the price level eventually explodes." | Read `P_0y/M_0 > P̄y/M`; so stated, every orbit from below the steady state reaches the demonetisation level in finite time (`PruningInflation.finite_time_explosion`). |
| p. 462 (E23) | "The resulting 40% cumulative price-level rise … devalued WWII debt by 40%." | A 40% rise lowers the real value of nominal debt by `1 − 1/1.4 = 2/7 ≈ 28.6%` (`Seigniorage.e23_real_loss`). |
| (19.27)–(19.30), p. 449 | The flow budget (19.27) and the transversality condition (19.28) imply the present-value budget in both forms, (19.29) and (19.30). | (19.28) gives (19.30) (`CashInAdvance.Stochastic.pv_19_30`), but (19.29) also needs the money transversality condition (`CashInAdvance.Stochastic.tvc_B_iff_money_tvc`, `CashInAdvance.Stochastic.pv_19_29`). With `Λ_t = 2^{−t}`, `P ≡ 1`, `M_{t−1} = 2^t`, `B_{t−1} = −2^t` and `s_t = −2^t`, (19.27), (19.28) and (19.30) hold and (19.29) fails (`CashInAdvance.Stochastic.pv_19_29_needs_money_tvc`). |
| (19.38), p. 452 | In the frictionless model `B_{t−1}/P_t = ∑βʲs_{t+j}`. | It should read `(B_{t−1} + M_{t−1})/P_t` (`CashInAdvance.PF.frictionless_valuation`), as the book's own condition on p. 453 uses. The printed form holds iff `M_{t−1} = 0` (`CashInAdvance.PF.printed_19_38_iff`). The zero-rate equilibrium `P_t = βᵗP_0`, `B_{t−1} = M_{t−1} = Wβᵗ/2`, `s = W(1 − β)/P_0` has `B_{−1}/P_0 = W/(2P_0)` but `∑βʲs_j = W/P_0` (`CashInAdvance.PF.printed_19_38_counterexample`). |
| A3 p. 631 | `u_c = ac^{−a−1}m^{b}` and `u_m = bc^{a}m^{−b−1}` for `u = −c^{−a}m^{−b}`. | Sign typos in the exponents: `u_c = ac^{−a−1}m^{−b}` and `u_m = bc^{−a}m^{−b−1}` (`Nonseparable.obs_uc`, `Nonseparable.obs_um`); at `a = b = 1`, `c = m = 2` the printed values are `1/2` against `1/8` (`Nonseparable.obs_printed_typo`). The book's next line uses the correct ones. |
| A1 p. 568 | The integrand `(i_t − i^m_t)M_τ/P_τ` in the valuation equation with ex-post discounting. | The rate must be dated `τ` (`ContinuousTime.money_interest_W_iff`). A path with `i^m_τ = e^{−τ}` gives `1` for the correct integral and `1/2` for the printed one (`ContinuousTime.printed_index_counterexample`). The `Generality` project found this first. |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 458 (E16) | "start with an inelastic money demand, `MV(i) = Py`"; "maximum revenue occurs where the elasticity of velocity is roughly one". | The demand is interest-elastic. Revenue is maximal where the velocity elasticity equals `π/(π + g)` (`Seigniorage.revenue_foc_iff`), which is one iff output does not grow (`Seigniorage.e16_unit_iff`). In the Cagan example the unique maximum is at `π = 1/a` (`Seigniorage.cagan_revenue_lt`). |
| p. 444 | "For a more realistic `Py/M ≈ 10`, we need `θ` on the order of 0.01." | `θ = (δ + µ)·10^{−γ}` at `Py/M = 10` (`MoneyInUtility.calib_ten`): `0.01` for `γ = 1` (`MoneyInUtility.calib_ten_gamma_one`), but `0.001` for the figure's `γ = 2` (`MoneyInUtility.calib_ten_gamma_two`). |
| p. 434 | The money transversality condition `E_tΛ_{t+T}M_{t+T}/P_{t+T} → 0` turns (19.2) into (19.3). | The summation by parts needs `E_tΛ_{t+T}M_{t+T−1}/P_{t+T} → 0` (`Regimes.eq192_iff_eq193`). The book's form implies it when `i ≥ 0` and `M ≥ 0` (`Regimes.tail_tendsto_zero_of_book_tvc`). A clarification, not an error. |
| p. 342 | The fiscal-theory answer to the helicopter drop is 1%. | The exact rise is `1/101`, within `10⁻⁴` of 1% (`Regimes.helicopter_fiscal`, `Regimes.helicopter_fiscal_approx`). Wording only. |
| p. 450 (Fact 1) | Overnight cash is unaffected by consumption, so the cash-in-advance constraint does not distort asset pricing. | Exact only for `V = 1` or `i = 0`. With binding money `P(c/V + y − c)` the effective price of consumption is `1 + (1 − Q)(1/V − 1)` (`CashInAdvance.MoneyDemand.binding_cost_wedge`, `CashInAdvance.MoneyDemand.wedge_eq_one_iff`), and `Λ_{t+1}/Λ_t = βw_t/w_{t+1}` (`CashInAdvance.Euler.sdf_wedge`). Suspected imprecision: the book calls the story "cleanest when `V = 1`", so it may be intended. |
| p. 454 | The standard path; deflationary equilibria for `P_0 < M_0V/y`. | The standard path is `P_t = M_tV/y` (the book drops `V`; `CashInAdvance.PF.usual_equilibrium`), and the deflationary equilibria exist also at `P_0 = M_0V/y` (`CashInAdvance.PF.deflation_equilibrium`). |
| p. 454 versus p. 445 and A3 p. 613 | Cash-in-advance and money-in-utility deflations re-emerge under the same money growth. | The transversality condition `µ < 0` is the same in both models (`Links.deflation_tvc_miu_iff_cia`), but existence is not: the cash-in-advance deflations exist for `1 + µ ≥ β`, the money-in-utility ones only for `1 + µ > β`, so at `1 + µ = β` only the first exist (`Links.cia_boundary_deflation`). |
| A3 p. 615 | "The nominal money supply is eventually constant or declining." | With `P_{t+1} = βP_t` the transversality condition holds iff nominal money tends to zero (`PruningDeflation.tvc_iff_money_vanishes`); money constant at a positive level violates it. |
| A3 p. 630 | `r^f ≈ δ + γE_tΔc_{t+1} + ηE_tΔm_{t+1}` with `η = −u_cm/u_c`. | With log money growth the coefficient is `η = −mu_cm/u_c` (`Nonseparable.sdf_log_hasFDerivAt`, `Nonseparable.rf_log_hasFDerivAt`); `−u_cm/u_c` is the coefficient of a level change (`Nonseparable.sdf_level_hasDerivAt`). |
| A3 p. 631 | The map `m_{t+1}/m_t = [(1 + µ)/β·(1 − b/(am_t))]^{1/(1−b)}`. | Needs `m_t > b/a` so that the bracket is positive; it is a hypothesis of `Nonseparable.obs_map_iff`. |
| A3 pp. 624–627 | Obstfeld and Rogoff: one-way redemption rules out hyperinflations; Cochrane: the demonetised path is an equilibrium; Obstfeld and Rogoff's rejoinder that a deviator can redeem a dollar carried into `T + 1`. | The dispute is about the redemption offer. In Obstfeld and Rogoff's finite-price notion, real balances never fall below the steady state (`ObstfeldRogoff.or_no_hyperinflation`); the only role of `ε > 0` is to keep prices finite, and their extra hypothesis `v′(Mε) ≥ u′(y)` is not needed. With a one-time redemption of the money carried out of `T`, Cochrane's path is optimal for the price-taking household, a Walrasian equilibrium (`ObstfeldRogoff.cochrane_household_optimal`, for every `T` in Figure 3.2 `ObstfeldRogoff.fig32_cochrane_optimal`), and it violates Obstfeld and Rogoff's bound (`ObstfeldRogoff.cochrane_violates_or_bound`). If the offer also stands for dollars acquired at `q_{T+1} = 0`, the household has no optimum, so the path is not an equilibrium (`ObstfeldRogoff.standing_redemption_no_optimum`). |
| A3 p. 619 | "There is not a continuum of inflationary equilibria, but a countable number." | Proved as a complete classification: positive initial real balances start an equilibrium iff `m_0 ≥ m̄` or `m_0` is one of the backward values `z_T` (`PruningInflation.eqm_initial_iff`), so the inflationary ones are countable (`PruningInflation.inflationary_initial_countable`). |
| p. 437 | "The solution picked in this way will generically be one of the explosive solutions." | The fiscally selected path is bounded iff `B_{−1} = e^{p̄}∑βʲs_j` (`CaganRE.fiscal_path_bounded_iff`), and that happens iff money and fiscal policy are coordinated as in NI-7 (`Links.cagan_ni7`). |
| A4 p. 638 | The interest cost of money tends to zero as `i − i^m → 0` when `ξ < 1`. | Proved as an iff (`ContinuousTime.interest_cost_tendsto_iff`). |
| p. 454 | An active fiscal policy prunes the deflationary equilibria. | Proved for the zero-rate family the book discusses: with the standard path's money, initial wealth and surplus held fixed, no equilibrium has a permanently zero rate (`CashInAdvance.PF.active_fiscal_prunes`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| Throughout | Conditional expectations pull out date-`t` quantities | `ExpectationSystem.PullOut` as a hypothesis; true for perfect foresight (`perfectForesight_pullOut`) and every finite tree (`ExpectationsFiniteTree.finiteTree_pullOut`) |
| pp. 439–441, 449 | `Λ_t/P_t` and `P_t/u_c(t)` are known at `t` | Derived from adapted `Λ`, `P`, `u_c` on any state space (`MoneyInUtility.known_div`, `MoneyInUtility.eq1911_iff_tvc_adapted`, `MoneyInUtility.value_of_money_limit_adapted`) |
| (19.2)–(19.3), (19.11)–(19.12), p. 434, 439 | The infinite sums `E_t∑` exist | Stated as limits of `E_t` of the partial sums, multiplied by the known `Λ_t` (`Regimes.flow_pv_iff_tvc`); in `tsum` form with summable flows (`Links.flow_pv_tsum_iff_tvc`, `CashInAdvance.Stochastic.pv_19_30`) |
| Footnote 1, p. 440; p. 453 | The first-order conditions are sufficient | Concavity in supergradient form (`MoneyInUtility.optimal_of_foc`, `CashInAdvance.Euler.euler_sufficient`), supplied by joint concavity (`MoneyInUtility.supergradient_of_concave`) or concavity of `u` (`Links.cia_euler_sufficient_of_concave`) |
| (19.31)–(19.32), p. 450 | The Euler equation under uncertainty | Derived on a finite event tree with `V = 1` (`CashInAdvance.TreeEuler.sdf_eq`, `CashInAdvance.TreeEuler.bond_price_from_optimality`); for a general `ExpectationSystem` `Λ_t = βᵗu′(y_t)` is a hypothesis (`CashInAdvance.Stochastic.bond_price_19_32`) |
| §19.3.2, A3 | Positive real balances and `θx^γ < 1` along equilibrium paths | Domain hypotheses of `MoneyInUtility.eq1923_iff` and `MoneyTargetingDynamics.nextX_pos`; demonetisation is `q = 1/P = 0` (`PruningInflation.IsEqm`) |
| p. 437 | `B_{−1} > 0` and a positive present value of surpluses | Hypotheses of `CaganRE.fiscal_selects_P0` and `CaganRE.fiscal_path_existsUnique` |
| p. 453 | `0 < B_{t−1} + M_{t−1}` and an absolutely summable surplus | Hypotheses of `CashInAdvance.PF.frictionless_price_unique` and `CashInAdvance.PF.frictionless_price_formula` |
| A4 | Continuous paths and integrable present values | `HasDerivAt` and `IntegrableOn` hypotheses; continuity of `r` for the discount factor (`ContinuousTime.hasDerivAt_discount`) |

## A correction to the formalisation record (not a book error)

An earlier stage of the work recorded that on an infinite state space the knownness of `Λ_t/P_t`
and `P_t/u_c(t)` "cannot be derived" from the expectation axioms, because the known variables form
only a unital subalgebra. That was wrong. The pull-out property gives `a·E_t(a⁻¹) = E_t(1) = 1`,
so the reciprocal of a nowhere-zero known variable is known on any state space
(`MoneyInUtility.known_inv`, `MoneyInUtility.known_div`). The theorems that derive knownness from
adaptedness (`MoneyInUtility.eq1911_iff_tvc_adapted`, `MoneyInUtility.eq1912_of_tvc_adapted`,
`MoneyInUtility.value_of_money_iterated_adapted`, `MoneyInUtility.value_of_money_limit_adapted`)
therefore hold on any state space. On a finite state space every function of a known variable is
known (`MoneyInUtility.functionsKnown_of_fintype`).

## Claims confirmed correct

| Where | Claim | Lean |
| --- | --- | --- |
| (19.2)–(19.3), p. 434 | The two forms of the valuation equation are equivalent under the money transversality condition | `Regimes.eq192_iff_eq193` |
| p. 435 | NI-7, double-passive indeterminacy, coordination under double-active policy | `Regimes.ni7`, `Regimes.double_passive`, `Regimes.double_active_iff` |
| pp. 315–318 | V1–V5: open-market irrelevance, seigniorage and the price level, the passive spread, observational equivalence of open-market operations, elastic currency | `Regimes.omo_irrelevant`, `Seigniorage.v2_cagan`, `Regimes.spread_existsUnique`, `Regimes.omo_equivalence`, `Regimes.elastic_currency` |
| (19.5)–(19.8), pp. 436–437 | The Cagan equation, the steady state, the full solution family, explosions and the forward solution | `CaganRE.cagan_iff_solves`, `CaganRE.steady_state_iff`, `CaganRE.eq_caganFamily`, `CaganRE.pf_explodes`, `CaganRE.eq198` |
| (19.13)–(19.16), pp. 440–441 | The first-order conditions, derived by optimisation, and the value of money | `MoneyInUtility.foc_1913_1914`, `MoneyInUtility.FootnoteTree.tree_foc_1913_1914`, `MoneyInUtility.value_of_money_iterated` |
| (19.19), (19.21)–(19.23), pp. 442–444 | The steady state, power money demand, (19.22) `≈ δ + µ`, the map (19.23) | `MoneyInUtility.steady_state_path_iff`, `MoneyInUtility.power_money_demand`, `MoneyInUtility.eq1922_approx`, `MoneyInUtility.eq1923_iff` |
| Figure 19.1, p. 444 | `x̄ ≈ 5.53`, slope `1.88` (exactly `47/25`), pole at `10`, unstable steady state, deflation limit `1/(1 + δ)` | `MoneyInUtility.fig191_xbar_bounds`, `MoneyInUtility.fig191_slope`, `MoneyInUtility.fig191_pole`, `MoneyTargetingDynamics.fig191_repelling`, `MoneyInUtility.deflation_limit` |
| p. 443 | Satiation is absorbing; zero rates as a limit; the correspondence | `MoneyInUtility.satiation_absorbing`, `MoneyInUtility.limit_rate_zero`, `MoneyInUtility.money_demand_correspondence` |
| A3 (3.1)–(3.6), pp. 614–623 | The no-debt telescoping, open-market operations, the last-period condition, the finite-time explosion, the modified utility and its continuum | `PruningDeflation.pv_finite_telescoped`, `PruningDeflation.omo_tvc`, `PruningDeflation.last_period_foc`, `PruningInflation.finite_time_explosion`, `PruningInflation.new_inflationary_continuum` |
| A3 Figure 3.2, p. 624 | `m = 4`, `M/P̄ = 1`, `1.866`, `1.457` | `ObstfeldRogoff.fig32_numbers` |
| A3 p. 632 | CES money in utility: discount factor, money demand, unit income elasticity | `Nonseparable.ces_sdf_const`, `Nonseparable.ces_money_demand_iff`, `Nonseparable.ces_income_elasticity` |
| (19.33), (19.37), pp. 450–454 | Fact 2, frictionless Fact 2 and the L-shaped demand | `CashInAdvance.MoneyDemand.fact2_19_33`, `CashInAdvance.MoneyDemand.fact_19_37`, `CashInAdvance.MoneyDemand.L_shaped_demand` |
| pp. 451–454 | The example `P = (1 − β)B/s`, passive-fiscal indeterminacy, the deflationary equilibria, coordination | `CashInAdvance.PF.example_unique`, `CashInAdvance.PF.passive_fiscal_indeterminate`, `CashInAdvance.PF.deflation_equilibrium`, `CashInAdvance.PF.coordination` |
| (19.39)–(19.40), pp. 456–457 | Unpleasant arithmetic; nominal versus real debt | `UnpleasantArithmetic.unpleasant_money_growth`, `UnpleasantArithmetic.nominal_debt_price_anti`, `UnpleasantArithmetic.real_debt_no_price` |
| (19.41), p. 458; p. 460 | Steady-state seigniorage; the Cagan peak; Baumol–Tobin elasticities of one half | `Seigniorage.steady_seigniorage`, `Seigniorage.cagan_revenue_lt`, `Seigniorage.bt_interest_elasticity`, `Seigniorage.bt_income_elasticity` |
| A1 (1.31)–(1.37), pp. 567–569 | Valuation with money in continuous time, each form iff its transversality condition | `ContinuousTime.money_printing_iff`, `ContinuousTime.money_interest_iff`, `ContinuousTime.money_mixed_iff` |
| A4 (4.1)–(4.5), (4.7)–(4.12), (4.16)–(4.17), pp. 635–641 | The present-value budget, first-order conditions, CES derivatives and elasticities, money demand, (4.11)–(4.12), the Hamiltonian consequences | `ContinuousTime.pv_budget_iff`, `ContinuousTime.foc_4_2`, `ContinuousTime.ces_mrs_4_7`, `ContinuousTime.demand_4_8`, `ContinuousTime.is_4_12`, `ContinuousTime.hamiltonian_eq_i` |
