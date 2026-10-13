# Corrections to the source

Places where a claim in Chapter 2 of Galí (2015) is false, imprecise, or relies
on an unstated hypothesis, and where the Lean statement departs from the
printed one. In each case the Lean statement proves the stated version and
cites the original. Entries are recorded when found and revised if
formalisation shows the finding itself to be wrong. Lean names are relative to
the namespace `Gali.ClassicalMonetaryModel`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| p. 28 | "If φ_π < 1, the forward solution (25) does not converge." | False: for an AR(1) driver with `|ρ| < φ_π` the series converges to `(r̂_t − v_t)/(φ_π − ρ)` and solves (24) for every `φ_π > 0`. What fails for `φ_π ≤ 1` is uniqueness, not convergence (`InterestRules.fwd25_ar1_hasSum`, `InterestRules.c2_3_forward_converges_not_unique`, `InterestRules.printed_divergence_false`). |
| pp. 40–41 | The planner sets `U_m = 0`, (50), and the decentralised economy is efficient iff `i_t = 0` (the Friedman rule). | With the chapter's own utilities `U_m > 0` everywhere (p. 32), so the planner's problem has no maximiser (`FriedmanRule.no_planner_optimum_isoelastic`) and money demand does not exist at `i = 0` (`MIUSeparable.no_money_demand_of_nonpos`). Proved: the book's literal equivalence (`FriedmanRule.decentralised_efficient_iff`) and global optimality of the Friedman rule under a satiable concave utility of real balances (`FriedmanRule.decentralised_optimal_iff_friedman`). |
| pp. 39–40 | After a monetary shock the real wage is countercyclical. | Needs `α > 0`. At `α = 0` labour demand is flat and the real wage does not move (`MIUNonseparable.real_wage_acyclical_of_alpha_zero`); for `0 < α < 1` it is strictly countercyclical (`MIUNonseparable.real_wage_strictly_countercyclical`). |
| Exercise 2.3(a), p. 47 | `φ_i ∈ [0, 1]`; determinacy iff `φ_π > 1`. | At `φ_i = 1` the rule is `i_t = i_{t−1}` and the equilibrium is never unique (`Ex2_3.pa_phi_i_one_not_determinate`); the range must be `0 ≤ φ_i < 1`. The general criterion is `|φ_i + (1 − φ_i)φ_π| > 1` (`Ex2_3.pa_determinate_iff`), which reduces to `φ_π > 1` only for `φ_π ≥ 0` (`Ex2_3.pa_determinate_iff_of_nonneg`). At `φ_π = 1` there are both multiple equilibria and, for a constant nonzero `r̂`, none (`Ex2_3.pa_two_solutions`, `Ex2_3.pa_boundary_nonexistence`). The same holds for part (b) with `δ`. |
| Exercise 2.6, p. 49 | The equilibrium is unique iff `φ_π > 1`. | Needs `φ_π ≥ 0`: with `ϖ = 0` and `φ_π = −2`, `|c| = 2 > 1` and the equilibrium is unique although `φ_π < 1` (`Ex2_6.counterexample_negative_phi`, `Ex2_6.unique_negative_phi`). Proved for `φ_π ≥ 0` (`Ex2_6.determinate_iff`). |
| Exercise 2.4(d), p. 48 | Derive the welfare losses from interest-rate fluctuations. | For every `σ ≤ 2`, including log utility, the second derivative of welfare in the interest rate is positive, so mean-preserving fluctuations raise expected utility to second order (`Ex2_4.W2_pos_of_le_two`, `Ex2_4.fluctuations_raise_welfare`). The exact sign condition is `Ex2_4.W2_pos_iff`; losses arise only for large `σ`. |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 20 | `σ ≥ 0`. | With `σ = φ = α = 0`, `D = σ(1 − α) + φ + α = 0` (`FirmsEquilibrium.bigD_zero_counterexample`), and the real block then has no solution when `a ≠ 0` and infinitely many when `a = 0` (`FirmsEquilibrium.staticBlock_degenerate_no_solution`, `FirmsEquilibrium.staticBlock_degenerate_many`). Stated with `σ > 0`, which gives `D > 0` (`FirmsEquilibrium.bigD_pos`). |
| p. 24 | The real rate falls after a technology shock and rises after an increase in `z`. | Only for `ρ_a < 1` and `ρ_z < 1` (`FirmsEquilibrium.rateCoeffA_neg_iff`, `FirmsEquilibrium.rateCoeffZ_pos_iff`); at `ρ = 1` the response is zero (`FirmsEquilibrium.rateCoeffA_rho_one`, `FirmsEquilibrium.realRate_no_z_response`). The book allows `ρ ∈ [0, 1]` on pp. 21–22. |
| p. 23 | Labour demand solves (14). | Unique only for `0 < α < 1`; at `α = 0` with `W = PA` every `N ≥ 0` is optimal (`FirmsEquilibrium.labour_demand_unique`, `FirmsEquilibrium.labour_demand_not_unique_alpha_zero`). |
| p. 28 | Determinacy iff `φ_π > 1` (the case `φ_π = 1` is not treated). | At `φ_π = 1` the equilibrium is never unique (adding a constant gives another) and a bounded one may not exist (`InterestRules.not_unique_of_le_one`, `InterestRules.phi_one_no_bounded_solution`); the Taylor principle holds on all of `φ_π ≥ 0` (`InterestRules.taylor_principle`). |
| p. 26 | An exogenous interest rate leaves the price level indeterminate. | Under perfect foresight the only free variable is the initial price level (`InterestRules.perfectForesight_exo_pinned`); sunspot fluctuations after date 0 need genuine uncertainty (`InterestRules.coin_exo_sunspot`). |
| p. 27 | Liquidity effect iff `ηρ_v > 1`. | Needs `φ_π > ρ_v` and `η ≥ 0` (`InterestRules.liquidity_effect_iff`). |
| (28), p. 29 | The forward solution for the price level. | Needs a bounded money supply. With growing money, the uniqueness class is `p − m` bounded (fn. 8; `MoneySupply.eq29_unique`). |
| p. 35 | With `ν = σ`, (37) and (38) coincide with the separable case. | Exact for (38) (`MIUNonseparable.miuEuler_nu_eq_sigma`); (37) holds up to the constant factor `(1 − ϑ)⁻¹`, i.e. a rescaled labour disutility (`MIUNonseparable.labour_supply_nu_eq_sigma`). |
| p. 38 | `ψ_yi ≃ −k_m/8`, so −0.04 for `k_m = 0.3` and −0.4 for `k_m = 3`. | The exact `ν → ∞` limit is `−k_mβ/(8(1 + k_m(1 − β)))`, which tends to `−k_m/8` as `β → 1` (`MIUNonseparable.tendsto_psiYi_nu`, `MIUNonseparable.tendsto_calib_beta_one`). At `β = 0.99`: −0.0370 and −0.360; the book's −0.4 is −0.375 rounded (`MIUNonseparable.psiYi_limit_km_base`, `MIUNonseparable.psiYi_limit_km_m2`). |
| p. 42 | `i_t = φ(r_{t−1} + π_t)` has the unique stationary solution `i = 0`, so `π_t = −r_{t−1}`. | Holds in the log-linear model with the Fisher equation (22) (`FriedmanRule.lagged_rule_unique`, `FriedmanRule.lagged_rule_exists`). |
| Exercise 2.2 b(i), p. 47 | Hint: `p̂_t ≡ p_t − p*`. | With a time-varying target `p*_t` the hint's deviation is unbounded when `π* ≠ 0` (`Ex2_2.hint_constant_target_unbounded`); the deviation must be `p_t − p*_t`. |
| Exercise 2.2 a(i), p. 46 | A rule delivering `π_t = π*`. | `i_t = r_t + π*` is indeterminate (`Ex2_2.strictIT_not_unique`, `Ex2_2.strictIT_sunspot`); full stabilisation needs `i_t = r_t + π* + φ_π(π_t − π*)` with `|φ_π| > 1` (`Ex2_2.strictIT_unique`). |
| Exercises 2.4(b), 2.5(c), p. 48–49 | The Friedman rule is optimal. | A supremum that is not attained: at `i = 0` the money first-order condition has no solution and no constant-velocity equilibrium exists, while welfare rises without bound as `i → 0⁺` (`Ex2_4.no_money_foc_at_zero_rate`, `Ex2_4.friedman_rule`, `Ex2_5.not_equilibrium_at_friedman`, `Ex2_5.tendsto_welfare_rate`, `Ex2_5.not_optimal_of_equilibrium`). In Ex 2.5 welfare also rises with `σ_m²` (`Ex2_5.welfare_strictMono_var`). |
| Exercise 2.4(c), p. 48 | The welfare cost as a permanent percentage increase in consumption. | Ambiguous; both readings are formalised. Holding real balances fixed, compensation may not exist (`Ex2_4.welfareCost_levels_none`); holding velocity fixed it always does (`Ex2_4.welfareCost_ratio`). |
| Exercise 2.8(b), p. 50 | Output falls with money growth. | Requires the cash-in-advance constraint to bind. With transversality it binds in every equilibrium for `γ ≥ 0`, `0 < β ≤ 1` (`Ex2_8.cia_binds_of_tvc`, `Ex2_8.output_eq_of_tvc`), but for `β < 1 + γ < 1` there is an equilibrium with the constraint slack forever and output 1 (`Ex2_8.slack_equilibrium_counterexample`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| (6), pp. 19–20 | Transversality is necessary | Proved as `liminf ≤ 0` and as `lim = 0` when the limit exists (`Household.tvc_liminf_of_optimal`, `Household.tvc_of_optimal_of_tendsto`); `lim = 0` without assuming the limit exists is not claimed. Under uncertainty only fn. 3's equilibrium fact is used (`Household.tvc_of_zero_bonds_stoch`). |
| (6) vs (3) | `Λ_{t,T}B_T/P_T` versus the market-price form `(∏ Q)B_T` | Equivalent along the Euler equation when `Q` is bounded away from 0 and above (`Household.bookTVC_iff`) |
| fn. 5, p. 22 | `ρ = −log β ≃ β⁻¹ − 1` | `0 ≤ (β⁻¹ − 1) − (−log β) ≤ (1 − β)²/β` (`Household.discount_rate_gap`) |
| (5), p. 19 | Euler necessity under uncertainty | Needs finitely many states or a uniform bound (`Household.euler_necessary_finite`, `Household.euler_general_necessary`) |
| p. 34 | Money demand (34) | Exists only for `i > 0` |
| p. 27, p. 30 | Closed forms | `ρ ≤ 1 < φ_π`; `|ρ_m| ≤ 1`, `η ≥ 0`; overshooting iff `ηρ_m > 0` (`MoneySupply.price_overshoots_iff`) |
| Exercise 2.5 | Gaussian i.i.d. shocks | Constructed on `Measure.infinitePi` (`Ex2_5.techInnovations`, `Ex2_5.moneyInnovations`); welfare is the expectation of lifetime utility (`Ex2_5.integral_tsum_welfare`) |
| Exercise 2.8(a) | Sufficiency of the first-order conditions | Against competitors with nonnegative money holdings, with transversality as a limit (`Ex2_8.overtakes_of_foc`) |
