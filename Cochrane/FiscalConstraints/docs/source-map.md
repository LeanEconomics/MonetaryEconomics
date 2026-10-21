# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, "Fiscal constraints"
(pp. 187–211). Each formal claim is listed with its Lean name, relative to the namespace
`Cochrane.FiscalConstraints`. Page numbers are book pages. The book has no labelled propositions,
so rows are keyed by equation number, section or page. Rows follow the book section by section,
and each heading names the modules that formalise the section: §§6.1–6.4.7, then the links
between the two formalisation chains, then the shared tools. Continuous-time statements are exact
derivatives and genuine improper integrals on `(0, ∞)`; "infinite" present values are
non-integrable integrands. Writing `x = b/y`, `σ = s/y` and `a = r − g`, the debt-to-GDP equation
(6.4) is `x' = ax − σ`, and its discrete analogue is `x_{t+1} = γx_t − w_t` with
`γ = (1 + r)/(1 + g)`. The labels D1–D6 (the r-versus-g dichotomy), S (the debt limit) and B
(Bohn's example) are those of the chapter survey. The stochastic results of §§6.4.6–6.4.7 hold
for an arbitrary `ExpectationSystem` with `ExpectationSystem.PullOut`. The shared core
(`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is cited where a row
uses it.

## §6.1 The present-value Laffer curve, pp. 187–190 (Laffer, ExpIntegrals)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 189 | the discount factor `e^{−au}` is integrable on `(c, ∞)` for `a > 0`, with `∫_c^∞ e^{−au}du = e^{−ac}/a` and `∫₀^∞ e^{−au}du = 1/a`; for `a ≤ 0` and `c ≠ 0`, `c e^{−au}` is not integrable | `ExpIntegrals.integrableOn_exp_neg_mul`, `ExpIntegrals.integral_exp_neg_mul_Ioi`, `ExpIntegrals.integral_exp_neg_mul_Ioi_zero`, `ExpIntegrals.not_integrableOn_exp_neg_mul` |
| Cochrane p. 189; (6.2), p. 191; (6.3), p. 195 | a stream `c e^{gu}` discounted at `r` has integrand `c e^{−(r−g)u}`; for `r > g` it is integrable with present value `c/(r − g)`, and for `r ≤ g`, `c ≠ 0` it is not integrable | `ExpIntegrals.exp_growth_eq`, `ExpIntegrals.integrableOn_exp_growth`, `ExpIntegrals.integral_exp_growth`, `ExpIntegrals.not_integrableOn_exp_growth` |
| Cochrane p. 189 | `PV_t = ∫₀^∞ e^{−ru}τy_te^{gu}du = τy_t/(r − g)` for `r > g`; for `r ≤ g` the present value of positive revenue is infinite | `Laffer.pv_tax_eq`, `Laffer.pv_tax_not_integrable` |
| Cochrane p. 189 | the output elasticity `∂log y/∂log τ = τy′(τ)/y(τ)`, and the static Laffer elasticity `∂log(τy)/∂log τ = 1 + ∂log y/∂log τ`, as exact derivatives in `log τ` | `Laffer.output_elasticity`, `Laffer.static_elasticity` |
| Cochrane p. 190 | `∂log PV/∂log τ = 1 + ∂log y/∂log τ + (1/(r − g))∂g/∂log τ`, for the closed form and for the improper integral itself | `Laffer.pv_elasticity`, `Laffer.pv_integral_elasticity` |
| Cochrane p. 190 | with no static effect and `∂g/∂log τ = −(r − g)` the elasticity is zero; in general it is nonpositive iff `∂g/∂log τ ≤ −(r − g)(1 + ε_y)`; the book's `r − g = 0.01`, `dg/dlog τ = −0.01` is the top of the curve | `Laffer.pv_elasticity_zero_of`, `Laffer.pv_elasticity_nonpos_iff`, `Laffer.book_top_of_curve` |
| Cochrane p. 190 | "r closer to g makes the present value more sensitive": the semi-elasticities in `g` and `r` are `±1/(r − g)`, and `1/(r − g)` is strictly decreasing in `r − g > 0` | `Laffer.log_pv_hasDerivAt_g`, `Laffer.log_pv_hasDerivAt_r`, `Laffer.semi_elasticity_strictAntiOn` |
| Cochrane p. 190 (E6.3) | a rise from 50% to 60% is a log change `log 1.2 ∈ (0.18, 0.19)`, so the implied growth cut is 0.18–0.19 pp, not 0.2 | `Laffer.log_tax_ratio_bounds`, `Laffer.book_growth_reduction_bounds` |

## §6.2 Discount rates, (6.1)–(6.2), pp. 191–193 (DiscountGrowth)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (6.1), p. 191 | discrete time: `e^{−δ}(1 + g)^{−γ}(1 + r) = 1` iff `log(1 + r) = δ + γlog(1 + g)` | `DiscountGrowth.euler_discrete_iff` |
| Cochrane (6.1), p. 191; (6.6), p. 199 | continuous time: the marginal value `λ(t) = e^{−δt}c(t)^{−γ}e^{rt}` has `λ′ = λ(r − δ − γċ/c)`, is stationary iff `r = δ + γċ/c`, and along `c₀e^{gt}` is constant iff `r = δ + γg` | `DiscountGrowth.marginalValue`, `DiscountGrowth.marginalValue_hasDerivAt`, `DiscountGrowth.euler_continuous_iff`, `DiscountGrowth.euler_exponential_iff` |
| Cochrane (6.2), p. 191 | `B/(Py) = ∫₀^∞ e^{−ru}σ(y_{t+u}/y_t)du = σ/(r − g)` for `r > g`; the integral diverges for `r ≤ g`, `σ ≠ 0` | `DiscountGrowth.value_of_debt_eq`, `DiscountGrowth.value_of_debt_not_integrable` |
| Cochrane p. 191 | with (6.1) the value is `σ/(δ + (γ − 1)g)`: independent of `g` for `γ = 1`; its derivative in `g` is `−σ(γ − 1)/(δ + (γ − 1)g)²`; it falls with `g` for `γ > 1` and rises for `γ < 1` | `DiscountGrowth.valueOfDebt`, `DiscountGrowth.value_indep_of_g`, `DiscountGrowth.value_hasDerivAt`, `DiscountGrowth.value_strictAntiOn`, `DiscountGrowth.value_strictMonoOn` |
| Cochrane p. 191 | "the discount rate effect is larger than the cashflow effect": the semi-elasticity in `g` is `1/(r − g) − γ/(r − g)` | `DiscountGrowth.log_value_hasDerivAt` |

## §6.3 Crashes and breakouts, pp. 193–195 (Crash)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 194 | the capped rule `s₁ = min(B₀/P*, s₁^max)`; the equilibrium `(P₀, P₁, B₀)`: positive prices, the budget, the bond price `1/(1 + i₀) = βP₀/P₁`, and `B₀/P₁ = s₁` | `Crash.surplus1`, `Crash.IsEquilibrium` |
| Cochrane p. 194 | in equilibrium `1 + i₀ > 0`, `P₁ = β(1 + i₀)P₀` and `B₋₁/P₀ = s₀ + βs₁`; "equilibrium still consists of `B₀/P₁ = s₁`, `B₋₁/P₀ = s₀ + βs₁`" as an iff | `Crash.one_add_pos`, `Crash.fisher`, `Crash.valuation`, `Crash.isEquilibrium_iff` |
| Cochrane p. 194 | unconstrained regime `s₁ < s^max` (with `B₀ ≠ 0`): `P₁ = P*`, `P₀ = P*/(β(1 + i₀))`, unaffected by `s₀` | `Crash.unconstrained_regime` |
| Cochrane p. 194 | constrained regime `s₁ = s^max`: `B₋₁/P₀ = s₀ + βs^max`, `B₀/P₁ = s^max` | `Crash.constrained_regime` |
| Cochrane p. 194 (E6.4) | the boundary: `s₁ < s^max` iff `β(1 + i₀)B₋₁/P* − s₀ < βs^max`; equivalently "a lot of outstanding debt `B₋₁`" (printed `B₁`) is debt above `P*(s₀ + βs^max)/(β(1 + i₀))` | `Crash.boundary_iff`, `Crash.boundary_iff_debt` |
| Cochrane p. 194 | the global formula `P₀ = max(P*/(β(1 + i₀)), B₋₁/(s₀ + βs^max))` and `P₁ = β(1 + i₀)P₀`, with its two branches | `Crash.price0`, `Crash.price1`, `Crash.price0_eq_left`, `Crash.price0_eq_right` |
| Cochrane p. 194 | the regimes emerge endogenously: every equilibrium with `B₀ ≠ 0` has `P₀` given by the formula; the formula is an equilibrium; an equilibrium exists iff `s₀ + βs^max > 0`; uniqueness | `Crash.eq_price0`, `Crash.isEquilibrium_price0`, `Crash.exists_equilibrium_iff`, `Crash.price0_unique` |
| Cochrane p. 194 (imprecision) | with `s₀ > 0` there is also an equilibrium with `B₀ = 0`, `s₁ = 0 < s^max`, whose `P₀` differs from the formula, so `P₁ ≠ P*` | `Crash.degenerate_equilibrium`, `Crash.degenerate_price0_ne` |
| Cochrane p. 194 | `P₀` weakly falls with `s₀` and `i₀` and rises with debt; `P₁` weakly rises with `i₀`; `P₀` is continuous in `s₀` and `i₀` (no jump at the regime switch) | `Crash.price0_antitoneOn_s0`, `Crash.price0_antitoneOn_i0`, `Crash.price0_monotone_debt`, `Crash.price1_monotoneOn_i0`, `Crash.continuousOn_price0_s0`, `Crash.continuousOn_price0_i0` |
| Cochrane p. 194 | unconstrained interior: `∂P₀/∂s₀ = 0`, `∂P₀/∂i₀ < 0`, `∂P₁/∂i₀ = 0` | `Crash.hasDerivAt_price0_s0_unconstrained`, `Crash.hasDerivAt_price0_i0_unconstrained`, `Crash.hasDerivAt_price1_i0_unconstrained` |
| Cochrane p. 194 | constrained interior: deficits flow into `P₀` (`∂P₀/∂s₀ < 0`), `∂P₀/∂i₀ = 0`, and a higher rate "just increases inflation" (`∂P₁/∂i₀ > 0`) | `Crash.hasDerivAt_price0_s0_constrained`, `Crash.hasDerivAt_price0_i0_constrained`, `Crash.hasDerivAt_price1_i0_constrained` |

## §6.4 What if r < g?, (6.3), p. 195 (RvsG)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (6.3), p. 195 | `b/y = ∫e^{−(r−g)τ}(s/y)dτ = (s/y)/(r − g)` for a constant ratio and `r > g`; for `r ≤ g` the integral diverges ("apparently infinite") | `RvsG.pv_const`, `RvsG.pv_const_not_integrable` |

## §6.4.1 The debt-to-GDP equation, (6.4)–(6.5), p. 196 (LinearODE)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (6.4), p. 196 | from `ḃ = rb − s` and `ẏ = gy`, `d(b/y)/dt = (r − g)(b/y) − s/y` (time-varying `r`, `g`, `s`); the discrete analogue `b_{t+1}/y_{t+1} = ((1 + r)/(1 + g))(b_t/y_t) − s_{t+1}/y_{t+1}` | `LinearODE.debt_gdp_ode`, `LinearODE.debt_gdp_discrete` |
| Cochrane (6.5), p. 196 | the variation-of-constants solution from `(t₀, x₀)` starts at `x₀` and solves `x' = ax − σ`; any solution on `[t₀, T]` equals it, and two solutions agreeing at `t₀` agree at `T` | `LinearODE.vocFrom`, `LinearODE.vocFrom_self`, `LinearODE.vocFrom_hasDerivAt`, `LinearODE.eq_vocFrom`, `LinearODE.solution_unique` |
| Cochrane (6.5), p. 196 (E6.1) | corrected: `x_t = e^{at}x₀ − ∫₀^t e^{aτ}σ_{t−τ}dτ`; the printed `∫₀^t e^{aτ}σ_{t−τ}dτ + e^{a}x₀` gives `e` instead of `e²` and `+1` instead of `−1` in two counterexamples | `LinearODE.corrected_6_5`, `LinearODE.printed65`, `LinearODE.printed_6_5_wrong_exponent`, `LinearODE.printed_6_5_wrong_sign` |

## §6.4.1 r versus g: the dichotomy, pp. 195–197 (RvsG)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (6.4), p. 196 | solutions on `[0, ∞)`, bounded paths, and the forward present value `x̂_t = ∫₀^∞ e^{−au}σ_{t+u}du` | `RvsG.SolvesOn`, `RvsG.BddOn`, `RvsG.pv` |
| Cochrane (6.5), p. 196 | every solution is the backward solution from its initial value; every initial value gives a solution; two backward solutions differ by `e^{at}(x₀ − z₀)` | `RvsG.solvesOn_eq`, `RvsG.vocFrom_solvesOn`, `RvsG.vocFrom_sub` |
| Cochrane p. 196 (D1) | for `a > 0` the present value is the backward solution from `x̂₀`, is bounded by `M/a`, and solves (6.4) | `RvsG.pv_eq_voc`, `RvsG.abs_pv_le`, `RvsG.pv_hasDerivAt`, `RvsG.pv_solvesOn`, `RvsG.pv_bddOn` |
| Cochrane p. 196 (D1) | `x_t − x̂_t = e^{at}(x₀ − x̂₀)`; other solutions explode; a solution is bounded iff `x₀ = x̂₀`, and then it is the present value at every date; exactly one bounded solution | `RvsG.sub_pv`, `RvsG.tendsto_abs_of_ne`, `RvsG.bddOn_iff`, `RvsG.eq_pv_of_bddOn`, `RvsG.existsUnique_bdd` |
| Cochrane p. 196 (D1) | the transversality condition, in ratios `e^{−at}x_t → 0` and in levels `e^{−rt}b_t → 0`, holds iff `x₀ = x̂₀` | `RvsG.tvc_iff`, `RvsG.tvc_levels_iff` |
| Cochrane p. 196 (D1) | with nominal debt `B₀ > 0`, `P₀` gives a bounded path iff `P₀ = B₀/(y₀x̂₀)` | `RvsG.nominal_determinacy` |
| Cochrane pp. 195–196 (D2) | for `r < g` every solution is bounded, `\|x_t\| ≤ \|x₀\| + M/(g − r)`, and any two converge ("the larger debt-to-GDP ratio melts away") | `RvsG.abs_le_of_neg`, `RvsG.bddOn_of_neg`, `RvsG.tendsto_sub_of_neg` |
| Cochrane pp. 195–196 (D2) | "indeterminacy, not infinity": every `P₀ > 0` gives a bounded path; yet with a constant nonzero surplus ratio no solution satisfies the transversality condition | `RvsG.nominal_indeterminacy`, `RvsG.tvc_fails_of_neg` |
| Cochrane p. 196 (D3) | for `r = g`, `x_t = x₀ − ∫₀^t σ`, bounded iff the cumulated surpluses are; with a constant nonzero ratio no solution is bounded | `RvsG.eq_of_zero`, `RvsG.bddOn_iff_zero`, `RvsG.not_bddOn_zero_const` |
| Cochrane p. 196 (D4) | two regimes, `a₁` before `T₀` and `a₂` after; the forward present value with time-varying discounting at date 0 and at every date; the glued solution | `RvsG.SolvesStep`, `RvsG.stepPV0`, `RvsG.pvStep`, `RvsG.stepSol` |
| Cochrane (6.5), p. 196 (D4) | backward solutions from `t₀` differ by `e^{a(t−t₀)}(x₀ − z₀)`; from `x̂₀` the path reaches the post-`T₀` present value; a two-regime solution is the backward solution before and after `T₀` | `RvsG.vocFrom_sub_from`, `RvsG.vocFrom_stepPV0`, `RvsG.step_after`, `RvsG.step_before` |
| Cochrane p. 196 (D4) | after `T₀` every solution differs from the present value by `e^{a₂(t−T₀)}e^{a₁T₀}(x₀ − x̂₀)`; "values of debt different from this forward-looking integral lead to explosions"; bounded iff `x₀ = x̂₀` | `RvsG.step_sub_pv`, `RvsG.step_tendsto_abs_of_ne`, `RvsG.step_bddOn_iff` |
| Cochrane p. 196 (D4) | the bounded solution is the forward present value at every date; the glued path equals it and solves the equation; exactly one bounded solution | `RvsG.vocFrom_stepPV0_eq`, `RvsG.stepSol_eq_pvStep`, `RvsG.stepSol_solvesStep`, `RvsG.step_existsUnique` |
| Cochrane p. 196 (E6.2) | the 20-year formula with future surpluses `σ_{t+τ}` is the unique non-explosive ratio; the printed version, with past surpluses, is positive for a path that is zero from date 0, where the true value is 0 | `RvsG.book_twenty_year_formula`, `RvsG.printed20`, `RvsG.pastOnly`, `RvsG.printed20_wrong` |
| Cochrane p. 196 (E6.2, rounding) | with `r − g = −1%` and zero surpluses the ratio falls to `e^{−0.2}` of its value in 20 years, and `e^{−0.2} ∈ (0.8187, 0.8188)`, not 80% | `RvsG.twenty_years_zero_surplus`, `RvsG.exp_neg_two_tenths_bounds` |
| Cochrane p. 196 (D5) | the discrete equation, bounded sequences, the present value `x̂_t = ∑_j w_{t+j}/γ^{j+1}`, the backward solution; `γ > 1` iff `r > g` | `RvsG.SolvesD`, `RvsG.BddD`, `RvsG.pvD`, `RvsG.iterD`, `RvsG.gamma_gt_one_iff` |
| Cochrane p. 196 (D5) | the backward solution solves the equation; two solutions differ by `γᵗ(x₀ − z₀)`; for `γ > 1` the present value is absolutely convergent, bounded by `M/(γ − 1)`, satisfies `x̂_t = (w_t + x̂_{t+1})/γ` and solves the equation | `RvsG.iterD_solves`, `RvsG.solvesD_sub`, `RvsG.abs_pvD_term_le`, `RvsG.summable_pvD`, `RvsG.abs_pvD_le`, `RvsG.pvD_succ`, `RvsG.pvD_solves` |
| Cochrane p. 196 (D5) | for `γ > 1` other solutions explode; bounded iff `x₀ = x̂₀`, and then it is the present value; transversality `x_t/γᵗ → 0` iff `x₀ = x̂₀`; nominal determinacy | `RvsG.tendsto_abs_of_ne_D`, `RvsG.bddD_iff`, `RvsG.eq_pvD_of_bddD`, `RvsG.tvcD_iff`, `RvsG.nominal_determinacy_D` |
| Cochrane p. 196 (D5) | for `0 ≤ γ < 1` every solution is bounded and any two converge, so every price level gives a bounded path; for `γ = 1`, `x_t = x₀ − ∑_{j<t}w_j`, bounded iff the partial sums are | `RvsG.abs_le_of_lt_one`, `RvsG.tendsto_sub_D`, `RvsG.nominal_indeterminacy_D`, `RvsG.eq_of_one`, `RvsG.bddD_iff_one` |

## §6.4.1 A debt limit with stochastic surpluses, pp. 196–197 (DebtLimitStochastic)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (6.4), p. 196, discrete | the stochastic debt path `x_{t+1} = γx_t − σ_t`, path by path the backward solution of `RvsG` | `DebtLimitStochastic.debtPath`, `DebtLimitStochastic.debtPath_succ` |
| Cochrane p. 197 | with surpluses bounded above by `K`, debt is bounded below; after `k` consecutive deficits of size at least `c`, `x_{t+k} ≥ γᵏx_t + c(1 + γ + ⋯ + γ^{k−1})`; for `M < c/(1 − γ)` a run length lifts every debt above the floor to above `M` ("flip 100 heads in a row") | `DebtLimitStochastic.debtPath_lower`, `DebtLimitStochastic.debtPath_run`, `DebtLimitStochastic.exists_run_length` |
| Cochrane p. 197 | blocks of `k` bad draws: measurable, on disjoint dates, with product probabilities, mutually independent, and with infinite total probability | `DebtLimitStochastic.badBlock`, `DebtLimitStochastic.measurableSet_badBlock`, `DebtLimitStochastic.block_index_injOn`, `DebtLimitStochastic.biInter_badBlock`, `DebtLimitStochastic.measure_biInter_badBlock`, `DebtLimitStochastic.iIndepSet_badBlock`, `DebtLimitStochastic.tsum_badBlock_eq_top` |
| Cochrane p. 197 (S) | Theorem S: independent surpluses bounded above with probability at least `p > 0` of a deficit `≥ c` push debt above every `M < c/(1 − γ)` infinitely often, almost surely; "no value of debt `b₀/y₀` is sustainable" | `DebtLimitStochastic.frequently_exceeds`, `DebtLimitStochastic.not_sustainable` |
| Cochrane p. 197 | an AR(1) "ranges over the entire real line": deficits of every size with probability bounded away from zero make debt almost surely unbounded; so do i.i.d. surpluses unbounded below and i.i.d. Gaussian surpluses | `DebtLimitStochastic.unbounded_of_unbounded_deficits`, `DebtLimitStochastic.iid_unbounded`, `DebtLimitStochastic.gaussian_deficit_pos`, `DebtLimitStochastic.gaussian_iid_unbounded` |
| Cochrane p. 197 (false as printed) | "even if we limit the support … the integral of the surplus eventually exceeds any bound": with `σ_t ≥ −c` debt never exceeds `max x₀ (c/(1 − γ))`; constant deficits are a counterexample | `DebtLimitStochastic.debtPath_le_of_bounded_deficits`, `DebtLimitStochastic.bounded_support_counterexample` |
| Cochrane p. 197 | the managed surplus, raised just enough to avoid the boundary, keeps debt at or below the limit from date 1, and differs from the unmanaged surplus only at the boundary | `DebtLimitStochastic.managedPath`, `DebtLimitStochastic.managedPath_le`, `DebtLimitStochastic.managedPath_eq_of_le` |

## §6.4.2–§6.4.3 The flow surplus and r < g as a free lunch, pp. 198–199 (RvsG)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 198 (D6) | a constant ratio `x*` solves (6.4) with constant `σ*` iff `σ* = (r − g)x*`, continuous across `r = g`; discretely `w* = (γ − 1)x*` | `RvsG.steady_state_iff`, `RvsG.steady_surplus_continuous`, `RvsG.steady_state_iff_D` |
| Cochrane p. 198 | at 100% debt, `r − g = ±0.01%` needs a steady surplus of `±0.01%` of GDP | `RvsG.book_flow_basis_point` |
| Cochrane p. 198 | with zero surpluses `x_t = e^{(r−g)t}x₀`; 150% falls to exactly 50% after `log 3/0.0001` years at `r − g = −0.01%` and rises to exactly 450% at `+0.01%` | `RvsG.zero_surplus_path`, `RvsG.book_growth_out_of_debt` |
| Cochrane p. 198 (rounding) | `log 3 ∈ (1.0986, 1.0987)`; "11,000 years" is between 10,986 and 10,987; `150e^{1.1} ∈ (450.6, 450.7)` | `RvsG.log_three_bounds`, `RvsG.book_years_bounds`, `RvsG.book_450_bounds` |
| Cochrane p. 199 | at 100% debt, `r − g = −1%` funds a steady deficit of 1% of GDP, and no more | `RvsG.book_one_percent_deficit` |

## §6.4.4 Growth theory and the transversality condition, (6.6), pp. 199–200 (GrowthTheoryTVC, DiscountGrowth)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 199 | balanced-growth consumption, discounted marginal utility `Λ_t = e^{−δt}c_t^{−γ}`, the rate `r = δ + γg`; `c_t^a = c₀^ae^{agt}` | `GrowthTheoryTVC.consumption`, `GrowthTheoryTVC.marginalUtility`, `GrowthTheoryTVC.rate`, `GrowthTheoryTVC.consumption_rpow` |
| Cochrane (6.6), p. 199 | `log Λ_t = −γlog c₀ − (δ + γg)t`, so `−(d/dt)log Λ_t = δ + γg`; `Λ_t = c₀^{−γ}e^{−(δ+γg)t}` | `GrowthTheoryTVC.log_marginalUtility`, `GrowthTheoryTVC.hasDerivAt_log_marginalUtility`, `GrowthTheoryTVC.marginalUtility_eq` |
| Cochrane p. 203 (used in §6.4.5) | the marginal rate of substitution is the risk-free discount factor, `Λ_τ/Λ_t = e^{−r(τ−t)}` | `GrowthTheoryTVC.marginalUtility_ratio` |
| Cochrane p. 199 | `r > g` iff `δ + (γ − 1)g > 0`; `r < g` iff `δ < (1 − γ)g`; `δ > 0`, `γ ≥ 1` give `r > g`; small `δ`, `γ < 1` and `g > 0` can give `r < g` | `GrowthTheoryTVC.rate_gt_growth_iff`, `GrowthTheoryTVC.rate_lt_growth_iff`, `GrowthTheoryTVC.rate_gt_growth_of_standard`, `GrowthTheoryTVC.rate_lt_growth_possible` |
| Cochrane p. 200 | `u′(c_T)b_T = c_T^{1−γ}(b_T/c_T)`; for `b_T = κc_T`, `e^{−δT}u′(c_T)b_T = κc₀^{1−γ}e^{(−δ+(1−γ)g)T}` | `GrowthTheoryTVC.tvc_term_identity`, `GrowthTheoryTVC.tvc_term_eq` |
| Cochrane p. 200 | the transversality condition for a steady debt/consumption ratio holds iff `r > g`; with `δ = 0` iff `γ > 1`; for `γ < 1` the term grows without bound | `GrowthTheoryTVC.tvc_iff`, `GrowthTheoryTVC.tvc_delta_zero_iff`, `GrowthTheoryTVC.tvc_diverges_of_lt_one` |
| Cochrane p. 200 | population growth: per-capita consumption grows at `g − n` and the per-capita first-order condition is `r = δ + γ(g − n)`, as a constant marginal value and as the rate of decline of marginal utility; for `n = 0` it is (6.6) | `DiscountGrowth.percapita_growth`, `DiscountGrowth.euler_population_iff`, `GrowthTheoryTVC.rate_population`, `GrowthTheoryTVC.rate_population_zero` |
| Cochrane p. 200 | "population growth allows `r < g` more easily": `r < g` iff `δ + (γ − 1)g < γn`; the per-capita TVC holds iff `r > g − n`; `δ = 1%`, `g = 3%`, `n = 2%` give `r = 2% ∈ (g − n, g)` | `DiscountGrowth.r_lt_g_population_iff`, `GrowthTheoryTVC.tvc_population_iff`, `GrowthTheoryTVC.population_allows_r_lt_g` |

## §6.4.5 Liquidity, seigniorage and r < g, (6.7)–(6.13), pp. 200–203 (MoneyLiquidity, LinearODE, ExpIntegrals)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 201 | with constant velocity money grows at `π + g` | `MoneyLiquidity.money_growth` |
| Cochrane (6.7)–(6.8), p. 201 | if `dM/dt = −Ps`, then `(π + g)M/(Py) = −s/y`; with a deficit the return on money `−π` is below `g` | `MoneyLiquidity.steady_state_deficit`, `MoneyLiquidity.money_return_lt_growth` |
| Cochrane p. 202 | with `i = r^f + π` the middle term of (6.9) is `(r^f − g)M/(Py)`; seigniorage exceeds the deficit | `MoneyLiquidity.middle_term`, `MoneyLiquidity.seigniorage_exceeds_deficit` |
| Cochrane (6.10)–(6.11), p. 202 and fn. 1 | `dm/dt + m(π + g) = −s/y` and `dm/dt + m(i − r^f + g) = −s/y` for `m = M/(Py)`; with debt, `dw/dt = (i − π − g)w − iM/(Py) − s/y` for `w = (M + B)/(Py)` | `MoneyLiquidity.hasDerivAt_moneyRatio`, `MoneyLiquidity.hasDerivAt_moneyRatio_rf`, `MoneyLiquidity.hasDerivAt_liabilityRatio` |
| Cochrane (6.12)–(6.13), pp. 202–203 | for a solution of `w' = aw − f` on `ℝ`, `w_t = ∫_t^T e^{−a(τ−t)}f_τdτ + e^{−a(T−t)}w_T` for all `t, T` | `LinearODE.finite_horizon_identity` |
| Cochrane (6.12), p. 202 | the money ratio is the value of surpluses discounted at the money return `−(π + g)` plus a terminal term; in the steady state the terms go to `−∞` and `+∞` | `MoneyLiquidity.eq_6_12`, `MoneyLiquidity.steady_6_12_explodes` |
| Cochrane (6.13), p. 203 | discounting at `r^f`, the money ratio is the value of surpluses plus seigniorage plus a terminal term; in the steady state both converge | `MoneyLiquidity.eq_6_13`, `MoneyLiquidity.steady_6_13_converges` |
| Cochrane (6.9), p. 201 | for `a > 0` a bounded solution satisfies the TVC; with bounded continuous flows and the TVC, `w_t = ∫_t^∞ e^{−a(τ−t)}f_τdτ`; `(M + B)/(Py)` is the present value of surpluses plus seigniorage at `r^f − g`, and it is unique | `ExpIntegrals.tvc_of_bounded`, `LinearODE.forward_present_value`, `MoneyLiquidity.eq_6_9`, `MoneyLiquidity.present_value_unique` |
| Cochrane p. 203 | with power utility the marginal rate of substitution is `e^{−r^f(τ−t)}`, `r^f = ρ + γg`; the TVC `e^{−r^f(T−t)}M_T/P_T → 0` holds iff `r^f > g`; the terminal value discounted at the ex-post money return explodes | `MoneyLiquidity.mrs_eq_riskfree`, `MoneyLiquidity.tvc_mrs_iff`, `MoneyLiquidity.return_discounted_terminal_explodes` |

## §6.4.6 Discount rates versus rates of return, (6.14), pp. 204–205 (ReturnDiscounting)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 204 | the gross return, the return discount factor `∏_{k≤j}R_{t+k}⁻¹`, the return-discounted value of dividends; `1 = E_t[R⁻¹R]` | `ReturnDiscounting.grossReturn`, `ReturnDiscounting.returnDiscount`, `ReturnDiscounting.returnPV`, `ReturnDiscounting.one_eq_E_inv_mul` |
| Cochrane (6.14), p. 204 | one more period of discounting; (6.14) state by state when `p_{s+1} + d_{s+1} ≠ 0`; and under `E_t` for an adapted price | `ReturnDiscounting.returnDiscount_succ_mul`, `ReturnDiscounting.eq_6_14_pathwise`, `ReturnDiscounting.eq_6_14` |
| Cochrane p. 204, display above (6.14) | the SDF finite-horizon value `Λ_tp_t = E_t[∑Λ_{t+j}d_{t+j} + Λ_{t+T}p_{t+T}]`, and divided by `Λ_t` | `ReturnDiscounting.sdf_finite_horizon`, `ReturnDiscounting.sdf_finite_horizon_div` |
| Cochrane p. 204 | "correct, if the sum and terminal value converge": with a summable return-discounted sum `S`, `p_t = S` iff the terminal term tends to zero | `ReturnDiscounting.return_pv_iff_terminal` |
| Cochrane p. 204 | the linear discount factor `R_{t+1}/E_t(R²_{t+1})` prices the return | `ReturnDiscounting.linear_discount_factor_prices` |

## §6.4.7 Aggregate uncertainty, (6.15)–(6.18), pp. 205–207 (AggregateUncertainty)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 205 | powers of consumption known at `t`; growth `G_{t+1} = c_{t+1}/c_t`; i.i.d. growth `E_t[G^a_{t+1}] = mom a`; the ratio `c_{t+j}/c_t`, the SDF `β^j(c_{t+j}/c_t)^{−γ}` and the gross risk-free rate `1/(βE[G^{−γ}])` | `AggregateUncertainty.KnownPowers`, `AggregateUncertainty.growth`, `AggregateUncertainty.IIDGrowth`, `AggregateUncertainty.ratio`, `AggregateUncertainty.pvDisc`, `AggregateUncertainty.riskFreeGross` |
| Cochrane (6.15), p. 205 | products of known variables are known; `c_t/c_t = 1`, `c_{t+j+1}/c_t = (c_{t+j}/c_t)G_{t+j+1}`, ratios and growth positive, powers known at `t + j` | `AggregateUncertainty.known_mul`, `AggregateUncertainty.ratio_zero`, `AggregateUncertainty.ratio_succ`, `AggregateUncertainty.ratio_pos`, `AggregateUncertainty.growth_pos`, `AggregateUncertainty.ratio_rpow_known` |
| Cochrane (6.15), p. 205; p. 206 | i.i.d. growth over one and over `j` periods, `E_t[(c_{t+j}/c_t)^aX] = (mom a)^jX`; the risk-free rate prices the riskless bond | `AggregateUncertainty.E_growth_mul`, `AggregateUncertainty.E_ratio_pow_mul`, `AggregateUncertainty.riskFree_prices` |
| Cochrane (6.15)–(6.16), p. 205 | the summand; correct terms `(β mom(1−γ))^jκ`; terms with the expectation inside `(β mom(−γ) mom 1)^jκ = ((1 + g)/(1 + r))^jκ` | `AggregateUncertainty.pvTerm`, `AggregateUncertainty.correct_term`, `AggregateUncertainty.incorrect_term`, `AggregateUncertainty.incorrect_ratio_eq` |
| Cochrane pp. 205–206 | a geometric series converges iff `\|q\| < 1`; the correct and the mistaken present values converge iff their ratios are below one in absolute value; "the true present value can converge while this mistaken one explodes" | `AggregateUncertainty.summable_geom_succ_iff`, `AggregateUncertainty.correct_pv_summable_iff`, `AggregateUncertainty.incorrect_pv_summable_iff`, `AggregateUncertainty.correct_finite_incorrect_explodes` |
| Cochrane p. 205 | the lognormal moment `E[G^a] = e^{aμ + va²/2}`, from the Gaussian moment generating function; the correct ratio `e^{−δ+(1−γ)μ+(1−γ)²v/2}` | `AggregateUncertainty.lognormalMoment`, `AggregateUncertainty.lognormalMoment_eq_integral`, `AggregateUncertainty.lognormal_correct` |
| Cochrane p. 206 (E6.5, E6.6) | the incorrect ratio is `e^{−δ+(1−γ)μ+(γ²+1)v/2}`, not the printed `γ²v/2`; the three exponents (with the typo `−δ(1−γ)g` read as `−δ + (1−γ)g`) | `AggregateUncertainty.lognormal_incorrect`, `AggregateUncertainty.printed_incorrect_wrong`, `AggregateUncertainty.correctExponent`, `AggregateUncertainty.incorrectExponent`, `AggregateUncertainty.printedExponent` |
| Cochrane p. 206 (E6.5) | "it is entirely possible": the region with a finite correct and an explosive mistaken present value is non-empty iff `γ > 0` (iff `γ > 1/2` with the printed exponent), with `δ > 0` available | `AggregateUncertainty.region_nonempty_iff`, `AggregateUncertainty.printed_region_iff`, `AggregateUncertainty.region_pos_delta` |
| Cochrane p. 206 (E6.7) | Bohn's rate: `log(1 + r_f) = δ + γμ − γ²v/2 = δ + γg_m − γ(γ + 1)v/2`; the printed `δ + γg − γ(γ − 1)σ²/2` matches neither | `AggregateUncertainty.log_riskFree_lognormal`, `AggregateUncertainty.log_riskFree_mean_growth`, `AggregateUncertainty.printed_bohn_rate_wrong` |
| Cochrane p. 206 (B) | `1 + r_f < E[G]` iff the mistaken present value explodes; for every `γ > 0`, `σ² > 0` there are `μ`, `δ > 0` with a finite present value and `r_f` below mean growth | `AggregateUncertainty.riskFree_lt_growth_iff`, `AggregateUncertainty.bohn_region` |
| Cochrane (6.17), p. 207 | rolling over at the risk-free rate has zero present value; (6.17) for any adapted debt rolled over at `R`; for `b = c`, the terminal term is `(β mom(1−γ))^Tc_t` and the surplus terms `q^j(1 − q)c_t` | `AggregateUncertainty.rollover_step`, `AggregateUncertainty.eq_6_17`, `AggregateUncertainty.terminal_c`, `AggregateUncertainty.pv_term_c` |
| Cochrane (6.17), p. 207 (E6.8) | "the last term converges to zero, via the transversality condition" iff `βE[G^{1−γ}] < 1`; the infinite SDF present value equals `c_t` iff the same | `AggregateUncertainty.terminal_tendsto_iff`, `AggregateUncertainty.bohn_pv_hasSum_iff` |
| Cochrane (6.18), p. 207 | the ex-post return on the rolled-over debt is `R`; (6.18) state by state and in expectation, `c_t(1 − (E[G]/R)^T)` and `c_t(E[G]/R)^T`; with `r < g` they go to `−∞` and `+∞` | `AggregateUncertainty.bohn_grossReturn`, `AggregateUncertainty.eq_6_18_pathwise`, `AggregateUncertainty.eq_6_18`, `AggregateUncertainty.eq_6_18_diverges` |
| Cochrane p. 206, two-state example (B) | the coin tree of horizon `H`: observations, the tree and its expectation system with pull-out; a flip not yet revealed leaves the information cell and has expectation `(f true + f false)/2` | `AggregateUncertainty.coinObsH`, `AggregateUncertainty.coinObsH_eq_iff`, `AggregateUncertainty.bohnTree`, `AggregateUncertainty.bohnSystem`, `AggregateUncertainty.bohnSystem_pullOut`, `AggregateUncertainty.info_flip`, `AggregateUncertainty.bohnTree_condE_coin` |
| Cochrane p. 206 (B) | growth `5/4` or `17/20`, consumption as their product, positive, with `c_{t+1}/c_t = G(ω_t)`; powers known; i.i.d. with moments `((5/4)^a + (17/20)^a)/2`; `E[G] = 21/20`, `E[G⁻¹] = 84/85`, `E[G⁻²] = 7312/7225` | `AggregateUncertainty.bohnGrowth`, `AggregateUncertainty.bohnGrowth_pos`, `AggregateUncertainty.bohnC`, `AggregateUncertainty.bohnC_pos`, `AggregateUncertainty.bohnC_growth`, `AggregateUncertainty.bohnSystem_knownPowers`, `AggregateUncertainty.bohnMom`, `AggregateUncertainty.bohnSystem_iid`, `AggregateUncertainty.bohnMom_values` |
| Cochrane pp. 205–207 (B) | with `β = 49/50`, `γ = 2`: `1 + r_f ≈ 1.0083 < E[G] = 1.05`, `βE[G^{−1}] ≈ 0.968 < 1`; (6.17) holds with terminal term `(4116/4250)^T → 0`; (6.18) has terms going to `−∞` and `+∞`; correct summands shrink, mistaken ones grow | `AggregateUncertainty.bohn_numbers`, `AggregateUncertainty.bohn_witness_6_17`, `AggregateUncertainty.bohn_witness_6_18`, `AggregateUncertainty.bohn_witness_terms` |

## Links between the two formalisation chains (Links, LinearODE)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (6.9), p. 201, and p. 196 | the forward integral of (6.9) is the §6.4.1 present value `RvsG.pv`; a solution satisfying the TVC equals it | `Links.forward_integral_eq_pv`, `Links.forward_present_value_eq_pv` |
| Cochrane (6.5), p. 196, and (6.12)–(6.13), pp. 202–203 | the finite-horizon identity and the variation-of-constants formula agree: `w_T = vocFrom a f t w_t T` for all `t, T` | `LinearODE.vocFrom_eq_of_global` |
| Cochrane (6.2), p. 191, and (6.3), p. 195 | the value of debt `σ/(δ + (γ − 1)g)` is `RvsG.pv` of the constant ratio `σ` at `r − g` | `Links.valueOfDebt_eq_pv` |
| Cochrane (6.1), p. 191, and (6.6), p. 199 | the marginal value of §6.2 is discounted marginal utility times `e^{rt}`; the first-order condition of §6.2 holds iff `r` is the rate of §6.4.4 | `Links.marginalValue_consumption`, `Links.euler_iff_rate` |
| Cochrane p. 200 | `r < g` iff `δ + (γ − 1)g < γn`, for the population rate of `GrowthTheoryTVC` | `Links.rate_population_lt_growth_iff` |
| Cochrane pp. 196, 200 | the growth-theory TVC term is `c₀^{−γ}` times the levels term `e^{−rT}b_T`; for a steady ratio the levels TVC holds iff `r > g` | `Links.growth_tvc_term_eq_levels`, `Links.growth_tvc_iff_levels_tvc` |
| Cochrane pp. 196, 198, 200 | steady debt solves (6.4) with surplus ratio `(r − g)κ` and is the present value for `r > g`; the growth TVC then follows from §6.4.1 alone | `Links.steady_debt_is_pv`, `Links.growth_tvc_from_rvsg` |
| Cochrane (6.4), pp. 196–197 | the discrete debt/GDP recursion and every path of Theorem S solve `RvsG.SolvesD`; bounded surpluses give bounded paths (D5); with Gaussian surpluses almost every path is unbounded (S) | `Links.debt_gdp_solvesD`, `Links.debtPath_solvesD`, `Links.debtPath_abs_le`, `Links.gaussian_not_bddD` |
| Cochrane pp. 195–196, 205–206 | without risk, `r_f < g` iff the present value diverges; with lognormal risk `r_f < E[G]` and a finite present value coexist | `Links.deterministic_rf_lt_g_iff`, `Links.rf_lt_g_pv_finite_needs_risk` |

## Shared tools

| Book | Claim | Lean |
| --- | --- | --- |
| §§6.4.1–6.4.5 (infrastructure) | bounded continuous streams discounted at `a > 0` are integrable with `\|∫_c^∞ e^{−au}σ\| ≤ Me^{−ac}/a`; translation of `(0, ∞)` to `(t, ∞)`; `∫_{(0,∞)} − ∫_0^t = ∫_{(t,∞)}`; `∫₀^T e^{−au}du = (1 − e^{−aT})/a`; `Ke^{aT} → 0` iff `a < 0`, `→ ∞` for `a > 0` | `ExpIntegrals.integrableOn_exp_mul_bdd`, `ExpIntegrals.abs_integral_exp_mul_le`, `ExpIntegrals.integral_Ioi_comp_add`, `ExpIntegrals.integral_exp_shift`, `ExpIntegrals.integral_Ioi_sub_interval`, `ExpIntegrals.intervalIntegral_exp_neg_mul`, `ExpIntegrals.tendsto_const_mul_exp_zero_iff`, `ExpIntegrals.tendsto_const_mul_exp_atTop` |
| §§6.4.6–6.4.7 | the expectation axioms, pull-out, perfect foresight; finite event trees and their pull-out property (used for `AggregateUncertainty.bohnTree`); a variable known at date `s` is known at every later date | `ExpectationSystem`, `ExpectationSystem.PullOut`, `perfectForesight`, `perfectForesight_pullOut`, `ExpectationsFiniteTree.FiniteTree`, `ExpectationsFiniteTree.FiniteTree.toExpectationSystem`, `ExpectationsFiniteTree.finiteTree_pullOut`, `ForwardSolution.E_of_known` |
| shared core, not used by Chapter 6 | forward series, the forward solution and Schur–Cohn determinacy, carried for the later Cochrane projects | `ExpectationSystem.forwardSeries`, `ForwardSolution.existsUnique_bounded`, `SchurStable`, `schurStable_iff_roots` |
