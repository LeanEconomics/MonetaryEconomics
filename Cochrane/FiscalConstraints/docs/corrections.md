# Corrections to the source

This file lists places where a claim in Chapter 6 of Cochrane (2023), *The Fiscal Theory of the
Price Level*, is false, imprecise, or relies on an unstated hypothesis, and where the Lean
statement departs from the printed one. In each case the Lean statement proves the stated
version and cites the original.

Codes E6.1–E6.10 are the Chapter 6 items of the survey of Chapters 6–10
(`notes/survey_cochrane_ch6-10.md`). Each was confirmed or refuted by formalisation before being
recorded here, and an entry is revised if formalisation shows the finding itself to be wrong (the
survey's Theorem S hypothesis is one such revision, below). Several claims that the book asserts
without proof turned out to be correct; they are listed in the last section.

Out of scope are Miller's learning model (p. 195), the discursive remarks on dynamic
inefficiency, overlapping generations and demographics (p. 200), the discussion paragraphs of
§6.4.6 and §6.4.8, and contingent liabilities (§6.5, pp. 209–211). Lean names are relative to the
namespace `Cochrane.FiscalConstraints`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| (6.5), p. 196 (E6.1) | The backward solution of (6.4) is `x_t = ∫₀^t e^{(r−g)τ}σ_{t−τ}dτ + e^{(r−g)}x₀`. | Two errors: the integral has the wrong sign and the homogeneous term lacks `t` in its exponent. The solution is `x_t = e^{(r−g)t}x₀ − ∫₀^t e^{(r−g)τ}σ_{t−τ}dτ` (`LinearODE.corrected_6_5`), unique among solutions continuous on `[0, t]` (`LinearODE.eq_vocFrom`). Each error has its own counterexample: with `r − g = 1`, no surpluses and `x₀ = 1` the solution at `t = 2` is `e²` but the printed formula gives `e` (`LinearODE.printed_6_5_wrong_exponent`); with `r = g`, `σ = 1` and `x₀ = 0` the solution at `t = 1` is `−1` but the printed formula gives `+1` (`LinearODE.printed_6_5_wrong_sign`). |
| §6.4.1, p. 196 (E6.2) | The 20-year forward formula, with `r − g = −1%` for 20 years and `+1%` after, discounts `s_{t−τ}/y_{t−τ}`. | A forward solution discounts future surpluses `σ_{t+τ}`; the printed formula copies the past surpluses of the backward formula. With future surpluses it is the unique bounded solution (`RvsG.book_twenty_year_formula`, `RvsG.step_existsUnique`). For a surplus path that is zero from date 0 on, the unique bounded solution starts at 0 but the printed formula is strictly positive (`RvsG.printed20_wrong`). The discount factors themselves are right. In the same passage "`e^{−0.2}` = 80%" is between 81.87% and 81.88% (`RvsG.exp_neg_two_tenths_bounds`). |
| p. 197 | "Even if we limit the support of the surplus distribution … the integral of the surplus eventually exceeds any bound." | False. If deficits are bounded, `σ_t ≥ −c`, debt never exceeds `max x₀ (c/(1 − γ))` on any path (`DebtLimitStochastic.debtPath_le_of_bounded_deficits`); constant deficits `σ_t = −c` are a counterexample (`DebtLimitStochastic.bounded_support_counterexample`). The correct version is Theorem S: with independent surpluses bounded above and a probability of a deficit of at least `c` bounded away from zero, debt exceeds every level `M < c/(1 − γ)` infinitely often, almost surely (`DebtLimitStochastic.frequently_exceeds`). Debt is almost surely unbounded only when deficits are unbounded in distribution, for example Gaussian (`DebtLimitStochastic.iid_unbounded`, `DebtLimitStochastic.gaussian_iid_unbounded`). |
| §6.4.7, p. 206 (E6.5) | The "incorrect" terms are `exp[((1−γ)g + γ²σ²/2)j]`. | The factor `E[c′/c] = e^{g+σ²/2}` contributes a `σ²/2` that is dropped: the terms are `exp[((1−γ)g + (γ² + 1)σ²/2)j]` (`AggregateUncertainty.lognormal_incorrect`), and for `σ² ≠ 0` this differs from the printed value (`AggregateUncertainty.printed_incorrect_wrong`). Consequently the region "true present value finite, mistaken one explosive" is non-empty iff `γ > 0` (`AggregateUncertainty.region_nonempty_iff`); with the printed exponent it would be non-empty iff `γ > 1/2` (`AggregateUncertainty.printed_region_iff`). The book's comparison for `γ > 1` is sufficient but not needed. |
| §6.4.7, p. 206 (E6.7) | Bohn's risk-free rate `r = δ + γg − ½γ(γ − 1)σ²`. | Under i.i.d. lognormal growth it matches neither convention when `γσ² ≠ 0` (`AggregateUncertainty.printed_bohn_rate_wrong`). With `g` the mean log growth, `log(1 + r_f) = δ + γg − γ²σ²/2` (`AggregateUncertainty.log_riskFree_lognormal`); with `g` the log of mean gross growth, `log(1 + r_f) = δ + γg − γ(γ + 1)σ²/2` (`AggregateUncertainty.log_riskFree_mean_growth`). The qualitative claim survives: precautionary saving can push `r_f` below growth with a finite present value (`AggregateUncertainty.bohn_region`). |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| §6.3, p. 194 | "So long as `s₁ < s^max` we have `P₁ = P*`", and the two regime formulas. | True for equilibria with outstanding debt `B₀ ≠ 0` (`Crash.unconstrained_regime`, `Crash.eq_price0`). When `s₀ > 0` there is also an equilibrium with `B₀ = 0`: the government retires all debt at date 0, `P₀ = B₋₁/s₀` and `s₁ = 0 < s^max`, yet `P₁ ≠ P*` unless `s₀ = β(1 + i₀)B₋₁/P*` exactly (`Crash.degenerate_equilibrium`, `Crash.degenerate_price0_ne`). An equilibrium exists iff `s₀ + βs^max > 0` (`Crash.exists_equilibrium_iff`). |
| §6.4.1, pp. 195–196 | "`r < g` implies price-level indeterminacy, not infinity." | The two halves use different criteria. Under the criterion that the debt-to-GDP ratio stay bounded, every `P₀ > 0` is consistent with `r < g` (`RvsG.nominal_indeterminacy`): indeterminacy. Under the transversality criterion `e^{−rt}b_t → 0`, no `P₀` satisfies it when the surplus ratio is a nonzero constant (`RvsG.tvc_fails_of_neg`): infinity, in the present-value sense. For `r > g` the two criteria agree (`RvsG.bddOn_iff`, `RvsG.tvc_levels_iff`). |
| (6.17), p. 207 (E6.8) | "The last term converges to zero, via the transversality condition." | A parameter restriction: for debt equal to consumption the terminal term is `c_t(βE[G^{1−γ}])^T` (`AggregateUncertainty.terminal_c`), which tends to zero iff `βE[G^{1−γ}] < 1` (`AggregateUncertainty.terminal_tendsto_iff`). The infinite SDF present value equals `c_t` iff the same holds (`AggregateUncertainty.bohn_pv_hasSum_iff`). It is a hypothesis, not a consequence. |
| Summary box p. 195; p. 197 (E6.9) | With permanent `r < g` and stochastic surpluses, "an upper bound on debt-to-GDP restores the present value"; p. 197 imagines a managed surplus process that avoids the bound. | Asserted, not derived, and no surplus rule is specified. The formal content is the two halves the text does establish: without management no initial debt is sustainable (`DebtLimitStochastic.not_sustainable`), and a surplus raised just enough to avoid the boundary keeps debt below it (`DebtLimitStochastic.managedPath_le`, `DebtLimitStochastic.managedPath_eq_of_le`). That this restores a unique price level is not formalised. |
| p. 197 | The AR(1) surplus "ranges over the entire real line", so debt eventually exceeds any bound. | Proved in discrete time for i.i.d. surpluses: deficits of every size with probability bounded away from zero make debt almost surely unbounded (`DebtLimitStochastic.unbounded_of_unbounded_deficits`), in particular for i.i.d. Gaussian surpluses (`DebtLimitStochastic.gaussian_iid_unbounded`). The continuous-time AR(1) version is not formalised. |
| §6.4.1, p. 196 | The 20-year example of temporary `r < g`. | Proved for the book's two-regime case, `r − g = a₁` (of any sign) before `T₀` and `a₂ > 0` after (`RvsG.step_existsUnique`), not for a general piecewise-constant `r − g`. |
| (6.14), p. 204 | The return-discounted identity, for positive prices. | Positivity is not needed: (6.14) holds state by state whenever `p_{s+1} + d_{s+1} ≠ 0` (`ReturnDiscounting.eq_6_14_pathwise`). |
| (6.9), p. 201 | The value of money and debt is the present value of surpluses plus seigniorage. | Proved as a representation and uniqueness theorem: given a solution of the flow equation with bounded continuous flows, `r^f > g` and the transversality condition, it equals the improper integral (`MoneyLiquidity.eq_6_9`), and two such solutions coincide (`MoneyLiquidity.present_value_unique`). Existence of the solution is not proved; the book does not claim it. |
| §6.4.7, pp. 205–207 | Consumption growth is i.i.d., lognormal or two-state, over an infinite horizon. | The infinite-horizon theorems hold for any expectation system with i.i.d. growth at every date (`AggregateUncertainty.IIDGrowth`, `AggregateUncertainty.correct_pv_summable_iff`, `AggregateUncertainty.bohn_pv_hasSum_iff`). An expectation system must be linear on all functions `Ω → ℝ`, so no infinite-horizon i.i.d. system is constructed: the witness is a coin tree of every finite horizon (`AggregateUncertainty.bohnTree`, `AggregateUncertainty.bohnSystem_iid`), and limits are taken over its closed forms. Lognormality enters through its moments (`AggregateUncertainty.lognormalMoment_eq_integral`). |

## Typos and rounding

| Where | Book says | Finding |
| --- | --- | --- |
| §6.1, p. 190 (E6.3) | "`τ` from 50% to 60%, a 20% rise", in an elasticity formula, implies a 0.2 percentage point growth reduction. | The formula needs a log change, `log 1.2 ∈ (0.18, 0.19)` (`Laffer.log_tax_ratio_bounds`), so the implied reduction is between 0.18 and 0.19 percentage points (`Laffer.book_growth_reduction_bounds`). |
| §6.3, p. 194 (E6.4) | "A lot of outstanding debt `B₁`". | Should be `B₋₁`; the regime boundary is stated in terms of `B₋₁` (`Crash.boundary_iff_debt`). |
| §6.4.7, p. 206 (E6.6) | `e^{−δ(1−γ)g+…}`. | Should be `e^{−δ+(1−γ)g+…}`, the `β^j = e^{−δj}` factor; the preceding "correct" term also omits `β^j`. Built into the exponents `AggregateUncertainty.correctExponent` and `AggregateUncertainty.incorrectExponent`. |
| §6.4.5, p. 203 (E6.10) | The marginal rate of substitution is written with `β`, the transversality condition with `e^{−ρ}`. | The same object; stated once, with `ρ`, in `MoneyLiquidity.mrs_eq_riskfree` and `MoneyLiquidity.tvc_mrs_iff`. Cosmetic. |
| §6.4.2, p. 198 | "11,000 years"; 150% grows to "450%". | `log 3/0.0001` lies between 10,986 and 10,987 (`RvsG.book_years_bounds`), and `150e^{1.1}` between 450.6 and 450.7 (`RvsG.book_450_bounds`). At the exact horizon the factors are exactly `1/3` and `3` (`RvsG.book_growth_out_of_debt`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| §§6.1–6.4 | `r > g` for every closed-form present value | Hypothesis of `ExpIntegrals.integral_exp_growth`, `Laffer.pv_tax_eq`, `DiscountGrowth.value_of_debt_eq`, `RvsG.pv_const`; shown necessary by `ExpIntegrals.not_integrableOn_exp_growth` and its uses |
| §6.4.1 | Surplus ratios are continuous and bounded | Hypotheses of the `RvsG` continuous-time theorems; continuity is needed for classical solutions (`LinearODE.vocFrom_hasDerivAt`) |
| §6.3 | Outstanding debt `B₀ ≠ 0` | Hypothesis of `Crash.unconstrained_regime`, `Crash.boundary_iff`, `Crash.eq_price0`; shown necessary by `Crash.degenerate_equilibrium` |
| §6.3 | `s₀ + βs^max > 0` and `1 + i₀ > 0` | `Crash.exists_equilibrium_iff`; `Crash.one_add_pos` derives `1 + i₀ > 0` in equilibrium |
| p. 197 (S) | Surpluses independent and bounded above, `0 ≤ γ < 1` | Hypotheses of `DebtLimitStochastic.frequently_exceeds`. The survey's version required surpluses bounded below by `−K`; formalisation showed the bound must be from above (it floors the debt path, `DebtLimitStochastic.debtPath_lower`) |
| §§6.4.4–6.4.5 | `g > 0` for the `γ > 1` criterion; `π + g > 0` for the money return below growth | Hypotheses of `GrowthTheoryTVC.tvc_delta_zero_iff`, `MoneyLiquidity.steady_6_12_explodes`, `MoneyLiquidity.return_discounted_terminal_explodes` |
| §§6.4.6–6.4.7 | Conditional expectations pull out known quantities; powers of consumption are known | `ExpectationSystem.PullOut` and `AggregateUncertainty.KnownPowers` as hypotheses, proved for the coin tree (`AggregateUncertainty.bohnSystem_pullOut`, `AggregateUncertainty.bohnSystem_knownPowers`) |
| p. 204 | `Λ_t` positive and known; the needed reciprocals known | Hypotheses of `ReturnDiscounting.sdf_finite_horizon_div` and `ReturnDiscounting.linear_discount_factor_prices` |
| (6.17), p. 207 | `βE[G^{1−γ}] < 1` | Hypothesis of the infinite-horizon present value, `AggregateUncertainty.bohn_pv_hasSum_iff` (E6.8) |

## Claims confirmed correct

| Where | Claim | Lean |
| --- | --- | --- |
| §6.1, pp. 189–190 | The present value of revenue, the static and present-value elasticities, the top of the curve, "r closer to g makes the present value more sensitive" | `Laffer.pv_tax_eq`, `Laffer.static_elasticity`, `Laffer.pv_integral_elasticity`, `Laffer.book_top_of_curve`, `Laffer.semi_elasticity_strictAntiOn` |
| (6.1)–(6.2), p. 191 | `r = δ + γg`; the value of debt is independent of growth for `γ = 1` and falls with it for `γ > 1` | `DiscountGrowth.euler_discrete_iff`, `DiscountGrowth.euler_exponential_iff`, `DiscountGrowth.value_of_debt_eq`, `DiscountGrowth.value_indep_of_g`, `DiscountGrowth.value_strictAntiOn` |
| §6.3, p. 194 | The two regimes, the boundary, deficits passing into `P₀` only when constrained, the interest rate raising `P₁` only when constrained | `Crash.unconstrained_regime`, `Crash.constrained_regime`, `Crash.boundary_iff`, `Crash.hasDerivAt_price0_s0_constrained`, `Crash.hasDerivAt_price1_i0_constrained` |
| (6.3)–(6.4), pp. 195–196 | The present value at a constant ratio and the debt-to-GDP equation | `RvsG.pv_const`, `LinearODE.debt_gdp_ode` |
| §6.4.1, p. 196 | `r > g`: the present value is the unique non-explosive value; `r < g`: every value is non-explosive and paths converge | `RvsG.existsUnique_bdd`, `RvsG.bddOn_of_neg`, `RvsG.tendsto_sub_of_neg`, `RvsG.eq_pvD_of_bddD`, `RvsG.tendsto_sub_D` |
| §§6.4.2–6.4.3, pp. 198–199 | The flow surplus is continuous across `r = g`; `r − g = −1%` at 100% debt funds a 1% deficit | `RvsG.steady_surplus_continuous`, `RvsG.book_one_percent_deficit` |
| (6.6), pp. 199–200 | `r > g` under standard preferences; the TVC holds iff `γ > 1` with `δ = 0`; population growth allows `r < g` | `GrowthTheoryTVC.rate_gt_growth_of_standard`, `GrowthTheoryTVC.tvc_delta_zero_iff`, `GrowthTheoryTVC.population_allows_r_lt_g` |
| (6.8)–(6.13), pp. 201–203 | The steady state, the middle term, the laws of motion, both finite-horizon representations, explosion of (6.12) and convergence of (6.13), the TVC with the MRS | `MoneyLiquidity.steady_state_deficit`, `MoneyLiquidity.middle_term`, `MoneyLiquidity.hasDerivAt_moneyRatio`, `MoneyLiquidity.eq_6_12`, `MoneyLiquidity.eq_6_13`, `MoneyLiquidity.steady_6_12_explodes`, `MoneyLiquidity.steady_6_13_converges`, `MoneyLiquidity.tvc_mrs_iff` |
| (6.14), p. 204 | The return-discounted identity, the SDF version, the linear discount factor | `ReturnDiscounting.eq_6_14`, `ReturnDiscounting.sdf_finite_horizon`, `ReturnDiscounting.linear_discount_factor_prices` |
| (6.15)–(6.18), pp. 205–207 | The true present value can converge while the mistaken one explodes; `r_f < g` is the same inequality as the mistaken one exploding; (6.17) and (6.18) with their limits | `AggregateUncertainty.correct_finite_incorrect_explodes`, `AggregateUncertainty.riskFree_lt_growth_iff`, `AggregateUncertainty.eq_6_17`, `AggregateUncertainty.eq_6_18`, `AggregateUncertainty.eq_6_18_diverges`, `AggregateUncertainty.bohn_numbers` |
