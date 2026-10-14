# Source map

Woodford (2003), *Interest and Prices*, Chapter 2, "Price-Level Determination under Interest-Rate
Rules" (pp. 61–138), with the proofs in Appendix A (pp. 627–655). Each formal claim is listed with
its Lean name, relative to the namespace `Woodford.PriceLevelDetermination`. Page numbers are book
pages. Rows follow the book: Chapter 2 §1–§4, then Appendix A.1–A.17. A claim proved in the
appendix is listed at the place where the chapter states it.

| Book | Claim | Lean |
| --- | --- | --- |
| Woodford (1.4)–(1.5), p. 66 | riskless bond price `B = A/(1 + i)` | `AssetPricing.E_q_riskless`, `AssetPricing.riskless_gross_return` |
| Woodford (1.6), p. 66 | riskless-debt dynamics | `AssetPricing.riskless_debt_dynamics` |
| Woodford (1.7)–(1.8), pp. 66–67 | `1 − E_t[Q(1 + i^m)] = Δ`; the flow constraint (1.2) ⇔ (1.7) | `AssetPricing.one_sub_E_q_gross_im`, `AssetPricing.flow_1_2_iff_flow_1_7` |
| Woodford p. 67 | `Q_{t,T} = ∏Q_{s−1,s}`, `Q_{t,t} = 1` | `AssetPricing.sdf`, `AssetPricing.sdf_add`, `AssetPricing.sdf_zero` |
| Woodford (1.10), p. 68 | income present value finite (absolute form) | `IntertemporalBudget.IncomeSummable`, `IntertemporalBudget.summable_income` |
| Woodford (1.11), p. 68 | an arbitrage when `i < i^m` | `AssetPricing.arbitrage_position`, `AssetPricing.arbitrage_unbounded_consumption` |
| Prop 2.1, pp. 68–69; A.1, pp. 627–628 | (1.7) + (1.9) ⇔ (1.12), both directions | `IntertemporalBudget.prop_2_1_iff`, `IntertemporalBudget.prop_2_1`, `IntertemporalBudget.telescope` |
| Woodford (1.13), p. 69 | the intertemporal constraint at every date | `IntertemporalBudget.ibc_of_flow` |
| Woodford (1.14)–(1.15), p. 69 | `M = 0` or `i = i^m` | `Equilibrium.reallocate_spending`, `Equilibrium.cashless_optimality` |
| Woodford (1.16)–(1.17), p. 70 | Euler condition with (1.5) gives the Fisher equation, and conversely | `Equilibrium.fisher_of_euler`, `Equilibrium.E_q_of_euler_fisher` |
| Woodford (1.18)–(1.19), p. 70 | (1.13) with equality ⇔ flow constraint with equality + transversality | `IntertemporalBudget.ibc_eq_iff_flow_eq_and_tvc`, `IntertemporalBudget.ibc_eq_of_flow_eq_and_tvc`, `IntertemporalBudget.flow_eq_and_tvc_of_ibc_eq` |
| Woodford p. 71 | `M^s > 0` forces (1.15) | `Equilibrium.zeroSpread_of_money_supply` |
| Woodford (1.20)–(1.23), pp. 71–72 | substituting the SDF; (1.18) ⇔ (1.22); (1.19) ⇔ (1.23) | `Equilibrium.sdf_of_euler`, `Equilibrium.E_sdf_mul_of_euler`, `Equilibrium.tvc_iff_1_22`, `Equilibrium.spendingSummable_iff_1_23` |
| Woodford (1.21), p. 71 | the exact Fisher equation in logs | `LogLinear.FisherExact`, `LogLinear.fisher_log_form` |
| Woodford p. 72 | rational-expectations equilibrium | `Equilibrium.REE` |
| Prop 2.2, p. 72; A.2, pp. 628–629 | (1.22) ⇔ (1.24) | `Transversality.prop_2_2`, `Transversality.tvc_identity` |
| Woodford (1.24), p. 72 | transversality on total liabilities, perfect-foresight form | `LocalIFT.TVC`, `Nonlinear.tvc_iff_tvcDebt` |
| Woodford (1.25), p. 73 | government flow constraint ⇒ household flow with equality | `AssetPricing.household_flow_eq_of_gov_flow` |
| Woodford (1.26)–(1.27), p. 73 | indirect utility with government purchases | `Equilibrium.indirectU`, `Equilibrium.hasDerivAt_indirectU`, `Equilibrium.fisher_1_26_of_euler`, `Equilibrium.budget_total_demand` |
| Woodford (1.29), p. 76 | implied taxes (exact) | `Wicksell.taxes_1_29` |
| Woodford p. 79 | steady state; `ī > 0`; (1.24) at the steady state | `Wicksell.steadyState_fisher`, `Wicksell.steadyState_rate_pos`, `Wicksell.steadyState_tvc` |
| Woodford p. 79 | (1.24) holds near the steady state under the fiscal rule `γ_D < π̄/β` | `LocalIFT.wicksell_tvc`, `LocalIFT.tvc_of_bounds`, `LocalIFT.abs_D_le`, `LocalIFT.target_ge` |
| Woodford p. 79 | the fiscal hypothesis is needed | `LocalIFT.wicksell_tvc_fails`, `LocalIFT.taylor_tvc_fails` |
| Woodford (1.32), p. 79 | log-linear Fisher equation as an exact derivative | `LogLinear.hasDerivAt_E_exp`, `LogLinear.hasDerivAt_log_E_exp`, `LogLinear.fisher_deriv`, `LogLinear.hasDerivAt_E` |
| Woodford (1.33), p. 80 | `r̂ = σ⁻¹E_t[Δ(Ŷ − g)]`; government-purchases variant | `LogLinear.hasFDerivAt_lambda`, `LogLinear.hasFDerivAt_lambdaG`, `LogLinear.fisher_composite_deriv`, `LogLinear.fisher_composite_deriv_1_33` |
| Woodford (1.34), fn. 15, p. 81 | `î = φ_p P̂ + ν` as an exact derivative | `LogLinear.hasFDerivAt_wicksell`, `LocalIFT.slopes_logRule`, `LocalIFT.slopes_gW` |
| Woodford (1.35)–(1.36), p. 81 | reduction to one equation in `P̂` | `Wicksell.identity_1_35`, `Wicksell.system_iff_reduced`, `Wicksell.reduced_iff_solves` |
| Woodford (1.38), p. 81 | the nominal rate in equilibrium | `Wicksell.interest_1_38` |
| Woodford (1.37), Prop 2.3, p. 82 | the unique bounded solution when `φ_p > 0`; determinate ⇔ `φ_p > 0` for `φ_p ≥ 0` | `Wicksell.existsUnique_priceGap`, `Wicksell.priceGap_eq_forwardSeries`, `Wicksell.prop_2_3_linear`, `Wicksell.determinate_iff` |
| Prop 2.3, p. 82; A.3–A.4, pp. 633–635 | local determinacy of the exact Wicksellian equilibrium; `C¹` dependence | `LocalIFT.wicksell_local_determinacy`, `LocalIFT.wicksell_smooth_dependence` |
| Prop 2.3, p. 82 | (1.37) is accurate to `O(ξ²)` (under `C²`) | `LocalIFT.wicksell_second_order` |
| Prop 2.4, p. 82; A.5, pp. 637–638 | no equilibrium when `i^m = 0` | `NoBubble.prop_2_4`, `NoBubble.no_REE`, `NoBubble.not_tvcWealth`, `NoBubble.tvcDebt_lower_bound` |
| Prop 2.4, p. 82 | the hypotheses are not vacuous | `NoBubble.fisher_deflation_path` |
| Woodford (1.39), p. 83 | weighted-average form; weights positive and summing to 1 | `Wicksell.logPrice_1_39`, `Wicksell.weights_pos`, `Wicksell.weights_hasSum_one`, `ForwardSolution.tsum_weights_by_parts` |
| Woodford fn. 17, p. 84 | only `log P* − φ_p⁻¹ν` matters (corrected) | `Wicksell.fn17_corrected`, `Wicksell.fn17_printed_false` |
| Woodford p. 85 | `P̂ ≡ 0` ⇔ `ν ≡ r̂` | `Wicksell.zero_gap_iff` |
| Woodford p. 85 | the effect of the gap varies as `1/φ_p` and vanishes as `φ_p → ∞`; the bound is attained | `Wicksell.abs_priceGap_le`, `Wicksell.gap_bound_antitone`, `Wicksell.gap_bound_tendsto_zero`, `Wicksell.constant_gap` |
| Woodford fn. 20, p. 85 | the Gibson paradox | `Wicksell.gibson` |
| Woodford (2.1), p. 86 | constant-prices interest rate | `ExogenousRate.constant_prices_2_1` |
| Prop 2.5, p. 87; A.6, p. 639 | exact sunspot equilibria; distinct; uncountably many | `ExogenousRate.sunspot_fisher`, `ExogenousRate.sunspotPrice_injective`, `ExogenousRate.prop_2_5_uncountable` |
| Prop 2.5, p. 87 | under tight bounds `π_t ∈ P`, and (A.2) holds | `ExogenousRate.infl_small`, `ExogenousRate.grossInfl_bounds`, `ExogenousRate.tvc_tight` |
| Woodford (2.2)–(2.3), p. 87 | every solution has the form (2.3); uncountably many | `ExogenousRate.sol23_solves`, `ExogenousRate.eq_sol23`, `ExogenousRate.bounded_solutions_not_countable` |
| Woodford p. 88 | price paths wander arbitrarily far apart | `ExogenousRate.prices_diverge`, `ExogenousRate.flipSystem` |
| Woodford p. 89 | the worst-case argument | `ExogenousRate.worst_case` |
| Woodford (2.4)–(2.5), pp. 90–91 | `î = ī + φ_π π` as an exact derivative | `LogLinear.hasFDerivAt_taylor`, `LocalIFT.slopes_logRule` |
| Woodford (2.6)–(2.7), p. 91 | reduction; the forward solution | `TaylorPrinciple.fisher_iff_26`, `TaylorPrinciple.inflation27_eq_forwardSeries`, `TaylorPrinciple.existsUnique_27` |
| Prop 2.6, p. 91 | determinate ⇔ `φ_π > 1` (for `φ_π ≥ 0`); ⇔ `\|φ_π\| > 1` in general; indeterminate for `0 ≤ φ_π < 1` | `TaylorPrinciple.prop_2_6`, `TaylorPrinciple.prop_2_6_iff`, `TaylorPrinciple.indeterminate_lt_one` |
| Prop 2.6, p. 91 | the boundary `φ_π = 1` | `TaylorPrinciple.one_no_bounded`, `TaylorPrinciple.one_not_unique` |
| Prop 2.6, p. 91 | exact model: local determinacy for `\|φ_π\| > 1`, indeterminacy for `\|φ_π\| < 1`; (2.7) accurate to `O(ξ²)` | `LocalIFT.taylor_local_determinacy`, `LocalIFT.taylor_smooth_dependence`, `LocalIFT.taylor_local_indeterminacy`, `LocalIFT.taylor_second_order` |
| Prop 2.6, p. 91 (with p. 79) | (1.24) near the steady state under a Taylor rule | `LocalIFT.taylor_tvc`, `LocalIFT.exists_eps_tvc` |
| Woodford fn. 25, p. 91 | the price level is determined, not only inflation | `TaylorPrinciple.price_level_determined`, `TaylorPrinciple.logLevel_eq`, `LocalIFT.taylor_price_level`, `LocalIFT.price_eq_of_infl_eq` |
| Woodford p. 92 | variability bound; unit root versus the Wicksellian rule | `TaylorPrinciple.abs_infl_le`, `TaylorPrinciple.infl_bound_antitone`, `TaylorPrinciple.oneOff_taylor`, `TaylorPrinciple.oneOff_wicksell` |
| Woodford p. 93 | regression coefficient `φ_p/2` | `TaylorPrinciple.regression_coefficient`, `TaylorPrinciple.var_diff_pos` |
| Woodford (2.8), p. 94; p. 95 | moving average; partial-adjustment form | `InertialRules.smoothed`, `InertialRules.smoothed_eq`, `InertialRules.smoothed_finite`, `InertialRules.eq_2_8_recursion`, `InertialRules.partialAdjust_iff_series` |
| Woodford (2.9), p. 95 | rule on smoothed inflation | `InertialRules.SmoothedRule` |
| Prop 2.7, p. 95; A.7, pp. 639–640 | determinate ⇔ `Φ_π > 1` (for `Φ_π ≥ 0`); ⇔ `\|δ + (1 − δ)Φ_π\| > 1` in general | `InertialRules.prop_2_7`, `InertialRules.determinate7_iff` |
| Prop 2.7, p. 95 | exact model: local determinacy / indeterminacy; (2.10) accurate to `O(ξ²)` | `Nonlinear.smooth_local_determinacy`, `Nonlinear.smooth_local_indeterminacy`, `Nonlinear.prop_2_7_cond`, `Nonlinear.smooth_second_order` |
| Woodford (2.10)/(A.18), p. 95 | solution for smoothed inflation | `InertialRules.eq_2_10` |
| Woodford (2.11)/(A.19), p. 95 | inflation from smoothed inflation | `InertialRules.eq_2_11` |
| Woodford (2.12), p. 96 | the inertial rule | `InertialRules.InertialRule` |
| Woodford p. 96 | (2.12) ⇔ (2.9) with `Φ_π = φ_π/(1 − ρ)`, `δ = ρ` | `InertialRules.smoothedRule_iff_inertialRule`, `InertialRules.inertialRule_iff_smoothedRule`, `InertialRules.eqm7_iff_eqm8`, `InertialRules.rule_iff_smoothed_series` |
| Woodford p. 96 | `Φ_π > 1` ⇔ `φ_π + ρ > 1` (for `ρ < 1`) | `InertialRules.taylor_principle_equiv` |
| Prop 2.8, (2.13), p. 96; A.8, pp. 640–641 | determinate ⇔ `φ_π > 0` and `φ_π + ρ > 1`; in general ⇔ `φ_π ≠ 0` and `\|φ_π + ρ\| > 1` | `InertialRules.prop_2_8`, `InertialRules.determinate8_iff`, `InertialRules.determinate8_of`, `InertialRules.exists_other_eqm8`, `InertialRules.continuum_eqm8` |
| Prop 2.8, p. 96 | exact model: local determinacy / indeterminacy; (2.15) accurate to `O(ξ²)` | `Nonlinear.inertial_local_determinacy`, `Nonlinear.inertial_local_indeterminacy`, `Nonlinear.prop_2_8_cond`, `Nonlinear.inertial_slope_iff`, `Nonlinear.inertial_second_order` |
| Woodford (2.14)–(2.15), p. 96 | the inflation and interest-rate solutions | `InertialRules.eq_2_14`, `InertialRules.eq_2_15` |
| Woodford p. 97; A.8, p. 641 | negative `φ_π` can be determinate | `InertialRules.determinate8_superinertial_neg`, `InertialRules.determinate8_exists_neg`, `InertialRules.determinate8_large_neg` |
| Woodford p. 97 | `φ_π = 0` is never determinate | `InertialRules.not_determinate8_zero` |
| Woodford p. 97 | AR(1) natural rate: `î ∝ r̂` | `InertialRules.ar1_interest`, `InertialRules.ma_rep_i`, `InertialRules.stationary_ma_i`, `InertialRules.irfI_pos` |
| Woodford p. 97 | the effect on `E_tπ_{t+1}` is `(ρ_r − ρ)` times the effect on `π_t` | `InertialRules.ar1_innovation_loadings`, `InertialRules.ar1_expected_inflation`, `InertialRules.irfPi_one` |
| Woodford p. 97 | transitory if `ρ = ρ_r`; antipersistent if `ρ > ρ_r` | `InertialRules.irfPi_transitory`, `InertialRules.irfPi_antipersistent`, `InertialRules.irfPi_less_persistent` |
| Prop 2.9, pp. 97–98; A.9, pp. 642–643 | corrected statement | `InertialRules.prop_2_9_corrected`, `InertialRules.prop_2_9_exists`, `InertialRules.prop_2_9_unique`, `InertialRules.prop_2_9_monotone` |
| Prop 2.9, pp. 97–98 | false as printed | `InertialRules.prop_2_9_false`, `InertialRules.prop_2_9_printed_false`, `InertialRules.e2_counterexample` |
| Fig. 2.1, p. 98 | impulse responses (closed form) | `InertialRules.irfR`, `InertialRules.irfI`, `InertialRules.irfPi`, `InertialRules.ma_rep_pi`, `InertialRules.stationary_ma_pi` |
| Woodford (2.16), p. 99 | Beveridge–Nelson innovation `(1 − ρ)(1 − ρ_r)⁻¹(φ_π + ρ − ρ_r)⁻¹ε` | `InertialRules.bn_innovation`, `InertialRules.bn_limit` |
| Woodford p. 99 | the innovation is zero iff `ρ = 1` | `InertialRules.bn_coeff_eq_zero_iff` |
| Woodford fn. 32, p. 99 | the `ρ = 1` rule is the first difference of (1.34) | `InertialRules.fn32_first_difference` |
| Prop 2.10, (2.17), pp. 100–101; A.10, p. 643 | (2.12) ⇔ (2.17) | `InertialRules.prop_2_10`, `InertialRules.shiftE` |
| Woodford (3.2), p. 103 | `M > 0` ⇒ `u_m/u_c = Δ` | `MoneyGrowth.foc_money_eq` |
| Woodford (3.3) ⇔ (3.5), p. 104 | money demand from `u_m/u_c` | `Nonlinear.mg_money_demand_iff` |
| Woodford (3.5), fn. 38, p. 104 | `L(Y, Δ)` well defined, increasing in `Y`, decreasing in `Δ` | `MoneyGrowth.lm_unique`, `MoneyGrowth.lm_exists`, `MoneyGrowth.lm_mono_income`, `MoneyGrowth.lm_anti_spread` |
| Woodford p. 106 | the money supply implementing a rate path is unique | `MoneyGrowth.exists_unique_money` |
| Woodford (3.6), p. 107 | log-linear money demand as an exact derivative; `η_y, η_i > 0` | `MoneyGrowth.hasFDerivAt_moneyDemand`, `MoneyGrowth.lm_partials`, `MoneyGrowth.eta_pos`, `Nonlinear.mg_coeffs_eq` |
| Prop 2.11, p. 107; A.11, pp. 644–645 | the unique bounded equilibrium under money-growth targeting | `MoneyGrowth.prop_2_11`, `MoneyGrowth.cagan_iff_scalar` |
| Prop 2.11, p. 107 | exact model: locally unique equilibrium with `P_t/M_t ∈ 𝒫`; `C¹` dependence | `Nonlinear.mg_local_determinacy`, `Nonlinear.mg_smooth_dependence` |
| Woodford (3.7), p. 108 | the price level as a weighted sum; weights positive, summing to 1 | `MoneyGrowth.prop_2_11_priceLevel`, `MoneyGrowth.phi_pos`, `MoneyGrowth.hasSum_phi` |
| Woodford (3.7), p. 108 | accurate to `O(ξ²)` | `Nonlinear.mg_priceLevel_second_order`, `Nonlinear.phi_sum_by_parts` |
| Woodford (3.8), p. 109 | `ι` increasing; money targeting is a Wicksellian rule with `φ_p = 1/η_i`; (3.7) is (1.39) | `MoneyGrowth.liquidity_preference_mono`, `MoneyGrowth.lm_iff_wicksell`, `MoneyGrowth.priceLevel_eq_wicksell`, `MoneyGrowth.phi_eq_wicksell_weight` |
| Woodford (3.9), p. 110 | Wicksellian rule ⇔ money-feedback rule | `MoneyGrowth.wicksell_iff_moneyFeedback` |
| Woodford p. 110 | only `log M − η_i log(1 + i^m)` matters | `MoneyGrowth.mgEquilibrium_composite` |
| Woodford (3.10), p. 113 | `χ = s_m υ`; same sign | `NonSeparable.chi_eq_sm_mul_upsilon`, `NonSeparable.chi_pos_iff`, `NonSeparable.chi_neg_iff` |
| Woodford (3.11), p. 114 | Euler equation with a real-balance effect, as an exact derivative | `NonSeparable.hasFDerivAt_logMU`, `NonSeparable.fisher311_of_lambda`, `Nonlinear.hasFDerivAt_euler311`, `Nonlinear.euler_iff_euler311` |
| Woodford (3.12), p. 114 | substitution of (3.6); `∂λ/∂ĵ = −χη_i` etc. | `NonSeparable.fisher311_iff_312`, `Nonlinear.hasFDerivAt_lamI`, `Nonlinear.lamI_coeffs`, `Nonlinear.lamI_j` |
| Woodford (3.13)–(3.15), pp. 114–115 | constant spread: `î = r̃ + E π′`; determinacy | `NonSeparable.spread_const_iff`, `NonSeparable.fisher312_constSpread`, `NonSeparable.constSpread_existsUnique` |
| Prop 2.12, p. 115; A.12, p. 645 | determinate for every `φ_p > 0` under (3.16); exact condition | `NonSeparable.prop_2_12`, `NonSeparable.prop_2_12_iff`, `NonSeparable.abs_B_lt_A` |
| Prop 2.12, p. 115 | exact model: local determinacy / indeterminacy | `Nonlinear.nsw_local_determinacy`, `Nonlinear.prop_2_12_exact`, `Nonlinear.nsw_local_indeterminacy`, `Nonlinear.nsw_smooth_dependence` |
| Woodford (3.17)–(3.19), p. 116 | solution and weights; positivity; sums | `NonSeparable.prop_2_12_priceLevel`, `NonSeparable.phi212_pos`, `NonSeparable.phiT212_pos`, `NonSeparable.hasSum_phi212`, `NonSeparable.hasSum_phiT212` |
| Woodford (3.17), p. 116 | accurate to `O(ξ²)` | `Nonlinear.nsw_second_order` |
| Woodford p. 116 | continuity in `χ`; reduction to (1.39) at `χ = 0` | `NonSeparable.sol212_continuousOn`, `NonSeparable.weights212_at_zero` |
| Prop 2.13, p. 116; A.13, p. 646 | determinate ⇔ `φ_π > 0` and `φ_π + ρ > 1`; `φ_π = 0` never determinate | `NonSeparable.prop_2_13`, `NonSeparable.det213_iff`, `NonSeparable.not_det213_zero` |
| Prop 2.13, p. 116 | exact model: local determinacy / indeterminacy | `Nonlinear.nsi_local_determinacy`, `Nonlinear.prop_2_13_cond`, `Nonlinear.nsi_local_indeterminacy`, `Nonlinear.nsi_smooth_dependence` |
| Woodford (3.20)–(3.22), p. 117 | solution and weights; positivity; reduction to (2.14) | `NonSeparable.gap213_formula`, `NonSeparable.weights213_pos`, `NonSeparable.weights213_at_zero` |
| Woodford (3.20), p. 117 | accurate to `O(ξ²)` | `Nonlinear.nsi_second_order` |
| Woodford p. 117 | `m̂ ∝ (σ⁻¹ + υ)Ŷ − β log(i/ī)` | `Calibration.hasFDerivAt_logMRS`, `Calibration.hasDerivAt_logSpread`, `Calibration.elasticity_ratio` |
| Woodford (3.23), p. 118 | `χ = s_m(2β − σ⁻¹)` | `Calibration.chi_calibrated` |
| Woodford p. 118 | `χ > 0` ⇔ `σ > 1/(2β)` (corrected) | `Calibration.chi_pos_iff_sigma`, `Calibration.sigma_threshold_bounds`, `Calibration.book_sigma_claim_false` |
| Woodford p. 118 | `χ < 2s_m`, `s_m = .0025`, `χ ≤ .005`; semilog bound `χ ≤ .01` | `Calibration.chi_lt_two_sm`, `Calibration.sm_value`, `Calibration.chi_le_005`, `Calibration.semilog_ratio_bounds`, `Calibration.chi_semilog_lt` |
| Fig. 2.2, p. 119 | `Φ_π = 1.5`; larger `φ̃_0` at `χ = .02` | `Calibration.fig22_parameters`, `Calibration.fig22_phiT0` |
| Fig. 2.3, pp. 119–120 | `∑φ_jρ_rʲ = 1/(A − Bρ_r)`; the value 2.5 | `Calibration.hasSum_weights_geom`, `Calibration.impact_AR1`, `Calibration.fig23_check` |
| Woodford (3.24), p. 121 | `χ(Δ) → χ̄` | `ShortPeriod.chi_limit` |
| Prop 2.14, p. 121; A.14, p. 647 | short-period determinacy | `ShortPeriod.prop_2_14`, `ShortPeriod.prop_2_14_eventually`, `ShortPeriod.prop_2_14_eventually_not`, `ShortPeriod.tendsto_delta_gamma` |
| Woodford fn. 55, p. 121 | (3.16) fails for `χ̄ < 0` | `ShortPeriod.fn55` |
| Prop 2.15, p. 122; A.15, pp. 647–648 | determinate ⇔ `Φ_π > 1`; (3.25) ⇔ `G > 0` | `ShortPeriod.prop_2_15`, `ShortPeriod.cond325_iff` |
| Woodford (3.26)/(A.36), pp. 122, 647 | the coefficient form of `î` | `ShortPeriod.rate_A36` |
| Woodford (4.2), p. 124 | a Ricardian fiscal rule implies the transversality condition (1.18); `α > 0` is needed | `GlobalDynamics.ricardian_tvc`, `GlobalDynamics.ricardian_discounted`, `GlobalDynamics.ricardian_tvc_fails_of_alpha_zero` |
| Woodford (4.3)–(4.6), pp. 124–125 | derivation of (4.5) and (4.6) | `GlobalDynamics.eq45_iff_fisher`, `GlobalDynamics.fisher_path_iff_eq45`, `GlobalDynamics.isPath45_iff_isPath46_of_const` |
| Woodford p. 125, fn. 58 | a continuum of perfect-foresight equilibria; (4.4) holds | `GlobalDynamics.continuum_pf_equilibria`, `GlobalDynamics.bound44_summable`, `GlobalDynamics.orbit46_isPath` |
| Woodford p. 125 | the Taylor principle ⇔ the curve cuts the diagonal from below | `GlobalDynamics.taylorCoeff_eq_slope`, `GlobalDynamics.target_isFixed` |
| Woodford p. 125 | a second steady state `Π** < Π*`, where the Taylor principle fails | `GlobalDynamics.second_steady_state` |
| Fig. 2.4, p. 126 | self-fulfilling deflation to `β` | `GlobalDynamics.self_fulfilling_deflation46`, `GlobalDynamics.deflation46_strictAnti`, `GlobalDynamics.deflation46_eventually_deflation` |
| Woodford p. 127 | inflation above target explodes (corrected) | `GlobalDynamics.inflation_unbounded46`, `GlobalDynamics.inflation_unbounded_iff`, `GlobalDynamics.e6_counterexample` |
| Woodford p. 127 | other paths leave a neighbourhood of `Π*` | `GlobalDynamics.target_locally_repelling`, `GlobalDynamics.target_locally_unique` |
| Woodford p. 127 | local indeterminacy at `Π**` | `GlobalDynamics.deflationary_steady_state_indeterminate` |
| Woodford p. 127 | `u_cm > 0` ⇒ `Π/λ(φ(Π))` increasing; deflations under (4.5) | `GlobalDynamics.ratio_strictMonoOn`, `GlobalDynamics.self_fulfilling_deflation45`, `GlobalDynamics.deflation45_exists`, `GlobalDynamics.isPath45_unique` |
| Woodford p. 127, fn. 61 | `λ` "not too strongly increasing" suffices | `GlobalDynamics.self_fulfilling_deflation45_gen`, `GlobalDynamics.deflation45_exists_gen`, `GlobalDynamics.step45_down_gen`, `GlobalDynamics.antitone_lam_gives_gen` |
| Woodford p. 127, fn. 61 | some restriction on `λ` is needed | `GlobalDynamics.deflation45_counterexample` |
| Woodford pp. 127–128 | deflations of (4.5) satisfy (4.4) | `GlobalDynamics.deflation45_bound44_gen`, `GlobalDynamics.bound44_summable_path`, `GlobalDynamics.deflation45_bound44` |
| Woodford (4.7)–(4.8), p. 129 | derivation of `G(m′) = (μ̄/β)F(m)` | `MoneyTargetingDynamics.eq48_iff_fisher` |
| Fig. 2.5, p. 130 | `F` positive and increasing, `F(0⁺) = 0`, single crossing | `MoneyTargetingDynamics.sepF_pos`, `MoneyTargetingDynamics.sepF_strictMonoOn`, `MoneyTargetingDynamics.sepF_tendsto_zero`, `MoneyTargetingDynamics.sep_single_crossing` |
| Woodford p. 130 | "`F` convex" (false) | `MoneyTargetingDynamics.e7_counterexample` |
| Woodford pp. 130–131 | `m₀ < m*` → 0; `m₀ > m*` → ∞ | `MoneyTargetingDynamics.sep_path_exists_unique`, `MoneyTargetingDynamics.sep_inflation_path`, `MoneyTargetingDynamics.sep_deflation_path` |
| Woodford (4.9), p. 132 | deflations violate the transversality condition (`μ̄ ≥ 1`) | `MoneyTargetingDynamics.money_tvc_violated`, `MoneyTargetingDynamics.sep_deflation_violates_tvc`, `MoneyTargetingDynamics.satiated_path` |
| Woodford p. 132 | Taylor rule with growing `D` and `φ = 0` below `Π̲` | `MoneyTargetingDynamics.zero_bound_inflation_eq_beta`, `MoneyTargetingDynamics.zero_bound_tvc_violated` |
| Woodford p. 133 | eventually `1 + φ(Π_T) ≤ μ̄` ⇒ the transversality condition fails (corrected) | `MoneyTargetingDynamics.tvcValue_succ`, `MoneyTargetingDynamics.e4_corrected_inequality`, `MoneyTargetingDynamics.e4_printed_inequality_false`, `MoneyTargetingDynamics.deflation_tvc_violated`, `MoneyTargetingDynamics.fig24_deflations_violate_tvc` |
| Woodford pp. 132–133 | the target path satisfies the transversality condition iff `βμ̄ < Π*` | `MoneyTargetingDynamics.target_tvc_iff` |
| Woodford p. 133 | `μ̄ < 1`: a continuum of paths satisfying the transversality condition | `MoneyTargetingDynamics.money_contraction_continuum` |
| Woodford (4.10), p. 136 | Obstfeld–Rogoff: no path with `m_t < m*` | `MoneyTargetingDynamics.or_no_path_below`, `MoneyTargetingDynamics.or_bounds_exist`, `MoneyTargetingDynamics.or_iteration_bound`, `MoneyTargetingDynamics.or_paths_above_mstar` |
| Woodford p. 137 | uniqueness of the stochastic equilibrium in the Schmitt-Grohé–Uribe example | Only asserted in the book; not formalised (the perfect-foresight result is `SchmittGroheUribe.sgu_unique_pf_equilibrium`) |
| A.1, p. 627 | `E_t[Q_{t,T}X] = E_t[Q_{t,s}E_s[Q_{s,T}X]]` | `AssetPricing.E_sdf_tower`, `AssetPricing.E_sdf_mul_E` |
| A.1, p. 628 | the sufficiency construction of wealth | `IntertemporalBudget.exists_wealth_of_ibc` |
| A.2, Prop 2.2′, p. 629 | (1.22) ⇔ (A.3) | `Transversality.prop_2_2'` |
| A.3, (A.7)–(A.8), p. 632 | the equilibrium map on `ℓ∞` is `C¹` and strictly differentiable at every point; the lead operator is bounded | `LocalIFT.hasStrictFDerivAt_eqMap`, `LocalIFT.contDiff_eqMap`, `LocalIFT.shift`, `LocalIFT.norm_shift_le` |
| A.3, (A.9), p. 632 | `a + bS` invertible iff `\|b\| < \|a\|`; `b − S` invertible iff `\|b\| > 1` | `LocalIFT.isUnit_TOp_iff`, `LocalIFT.isUnit_linOp_iff` |
| A.3, p. 633 | locally unique equilibrium for small shocks, `C¹` in the shocks (vector shocks, local hypotheses) | `LocalIFT.local_determinacy3`, `LocalIFT.local_determinacy_loc`, `LocalIFT.local_determinacy` |
| A.3, (A.5)/(A.10), p. 633 | the first-order term is the log-linear solution | `LocalIFT.hasFDerivAt_implicitSol3`, `LocalIFT.linSol3_apply`, `LocalIFT.hasFDerivAt_implicitSol`, `LocalIFT.linSolOp_apply` |
| A.3, p. 633 | `O(‖u‖²)` accuracy (needs `C²` or `C^{1,1}`) | `LocalIFT.second_order3`, `LocalIFT.second_order_loc`, `LocalIFT.second_order_accuracy`, `LocalIFT.second_order_accuracy_of_contDiff_two` |
| A.3, p. 633 | `O(‖u‖²)` fails under `C¹` alone | `LocalIFT.not_second_order_of_C1` |
| A.3, p. 633 | indeterminacy of the exact model when the root is inside the unit circle | `LocalIFT.local_indeterminacy_loc`, `LocalIFT.local_indeterminacy` |
| A.4, (A.14)–(A.15), p. 636 | iterating the forward equation | `ForwardSolution.Solves`, `ForwardSolution.iterate_A15` |
| A.4, (A.16), p. 636 | the unique bounded solution when `\|a\| < 1` (including `a < 0`) | `ForwardSolution.existsUnique_bounded`, `ForwardSolution.eq_forwardSeries_abs`, `ForwardSolution.tendsto_partial_A16`, `ForwardSolution.forwardSeries_solves_abs` |
| A.4, (A.16), p. 636 | `1 − aS` invertible on `ℓ∞` with the forward sum as inverse | `LocalIFT.isUnit_fwdOp`, `LocalIFT.fwdOp_inverse_apply`, `LocalIFT.eq_fwdSol` |
| A.4, (A.14)–(A.16), pp. 636–637 | the form `A z_t = B E_t z_{t+1} + f_t`: unique bounded solution iff `\|B\| < \|A\|` | `ForwardSolution.ScalarEq`, `ForwardSolution.scalar_existsUnique`, `ForwardSolution.scalar_determinate_iff`, `ForwardSolution.scalar_homog` |
| A.4, (A.17), pp. 636–637 | a continuum of bounded solutions when `\|a\| > 1`; every solution is in the family | `ForwardSolution.sunspotFamily_solves`, `ForwardSolution.sunspotFamily_bounded`, `ForwardSolution.eq_sunspotFamily`, `ForwardSolution.exists_bounded_of_one_lt` |
| A.4, p. 637 | `\|a\| = 1`: if one bounded solution exists there are uncountably many; one may not exist | `ForwardSolution.bounded_solutions_not_countable`, `ForwardSolution.unit_sunspot_solves`, `ForwardSolution.no_bounded_solution_unit` |
| A.4, p. 637 | the recursion printed for `\|a\| = 1` (corrected) | `ForwardSolution.printed_A17_one_solves`, `ForwardSolution.printed_A17_fails_neg_one`, `ForwardSolution.forwardSeries_solves_of_decay` |
| A.4, p. 637 | `\|a\| < 1` is necessary and sufficient | `ForwardSolution.existsUnique_iff` |
| App. A (survey L2) | `∑cBʲ/A^{j+1} = c/(A − B)`; summation by parts | `ForwardSolution.hasSum_geometric_ratio`, `ForwardSolution.tsum_geometric_ratio`, `ForwardSolution.abel_tsum`, `ForwardSolution.summable_geom_mul` |
| A.6, p. 639 | the inflation surprise (corrected) | `ExogenousRate.surprise_A6`, `ExogenousRate.printed_surprise_false`, `ExogenousRate.coin_info_zero` |
| A.6, p. 639 | the sunspot construction | `ExogenousRate.Kexp`, `ExogenousRate.grossInfl`, `ExogenousRate.sunspotPrice`, `ExogenousRate.sunspotPrice_pos` |
| A.7, (A.20), p. 640 | the difference equation for smoothed inflation | `InertialRules.eq_A_20` |
| A.8, pp. 640–641 | the equation for `î` and for the gap | `InertialRules.interest_equation`, `InertialRules.gap_equation`, `InertialRules.gap_forward` |
| A.8, p. 641 | inverting (2.12) for `π` (exact model) | `Nonlinear.solveRule`, `Nonlinear.solveRule_local`, `Nonlinear.hasFDerivAt_solveRule` |
| A.9, (A.23), p. 642 | `var(î)`, `cov(î_t, î_{t−1})` | `InertialRules.msq_irfI`, `InertialRules.acov1_irfI` |
| A.9, (A.24), p. 642 | `var(π)` | `InertialRules.msq_irfPi`, `InertialRules.irfPi_from_irfI`, `InertialRules.var_pi_book_route` |
| A.9, p. 642 | the `φ_π` that achieves the target | `InertialRules.achieve_iff` |
| A.9, (A.25), p. 643 | `σ(î)` (corrected) | `InertialRules.msq_irfI_eq_sq`, `InertialRules.sigma_i_formula` |
| A.9, p. 643 | `h(ρ)` increasing | `InertialRules.hfun_strictMono` |
| A.10, p. 643 | predetermined variable: (A.14) ⇔ (A.16) | `ForwardSolution.solves_iff_forwardSeries`, `ForwardSolution.predetermined_restriction` |
| A.11, (A.28)–(A.29), pp. 644–645 | the Cagan form | `MoneyGrowth.lm_iff_cagan`, `MoneyGrowth.cagan_iff_scalar` |
| A.11, (A.30), p. 645 | the solution for real balances; accurate to `O(ξ²)` | `MoneyGrowth.mgPrice`, `MoneyGrowth.mgRate`, `Nonlinear.mg_second_order`, `Nonlinear.linSol3_FMG_apply` |
| A.12, (A.32), p. 645 | the `P̂` equation; slopes of the exact model | `NonSeparable.eq212_iff_scalar`, `Nonlinear.slopes_FW`, `Nonlinear.hasFDerivAt_FW` |
| A.12–A.13, pp. 645–646 | sign lemma (survey L4) | `ForwardSolution.abs_lt_abs_of_sub_pos_add_pos`, `ForwardSolution.abs_lt_abs_iff_of_add_pos` |
| A.13, (A.33), p. 646 | the `î` equation; slopes of the exact model | `NonSeparable.eq213_iff`, `Nonlinear.slopes_F13`, `Nonlinear.gamma_slope_iff` |
| A.14, (A.34), p. 647 | `Δγ₀, Δγ₁ → η̃χ̄φ_π` | `ShortPeriod.tendsto_delta_gamma` |
| A.15, p. 648 | `Λ = 1/γ₁` and the limits of `Λ, Γ, Γ̃, ξ`; continuous and positive | `ShortPeriod.LambdaC_eq`, `ShortPeriod.LambdaC_sub`, `ShortPeriod.prop_2_15_limits`, `ShortPeriod.limits_continuousOn`, `ShortPeriod.limits_pos` |
| A.15, p. 648 | the printed identity and limit (false) | `ShortPeriod.book_identity_false`, `ShortPeriod.book_Lambda_limit_wrong` |
| A.16, (A.37)–(A.39), p. 649 | flow budget under the alternative timing | `Timing.budget_A39` |
| A.16, (A.40), pp. 649–650 | the intertemporal budget constraint | `Timing.ibc_A40` |
| A.16, (A.41), p. 650 | first-order condition | `Timing.foc_A41` |
| A.16, (A.42)–(A.46), pp. 650–651 | `λ = u_c + u_m`; Euler and Fisher equations; the money-demand relation | `Timing.lambda_A44`, `Timing.euler_A42_iff_A43`, `Timing.fisher_A46_iff_A43`, `Timing.oddsRatio_strictMonoOn` |
| A.16, (A.47), p. 651 | `χ` as an exact elasticity; separable ⇒ `χ < 0` iff `u_mm < 0` | `Timing.chiLS_is_elasticity`, `Timing.chiLS_neg_iff_of_separable` |
| A.16, (A.48)–(A.49), p. 652 | `λ = v_C` | `Timing.A48_lambda_credit`, `Timing.A48_lambda_cash` |
| A.16, p. 653 | cash/credit goods: `λ = v_c(m)`, `χ < 0` | `Timing.cashcredit_lambda`, `Timing.cashcredit_chi_neg`, `Timing.uCC`, `Timing.cashcredit_indirect_nhds`, `Timing.cashcredit_indirect_lambda` |
| A.17, p. 654 | `c₁ = min(m, C/(1 + θ))` | `SchmittGroheUribe.c1opt_optimal` |
| A.17, (A.54), p. 654 | `λ = 1/min(m, C/(1 + θ))` | `SchmittGroheUribe.lambda_A54_binding`, `SchmittGroheUribe.lambda_A54_satiated` |
| A.17, (A.55), p. 654 | money demand `L(Y, i)` | `SchmittGroheUribe.money_demand_A55` |
| A.17, p. 654 | `λ(i) = (1 + θ(1 + i))/Ȳ`; elasticity below 1 at each `i`, tending to 1 | `SchmittGroheUribe.lambda_of_i`, `SchmittGroheUribe.elasticity_lt_one`, `SchmittGroheUribe.elasticity_tendsto_one` |
| A.17, (A.56), pp. 654–655 | the rule; the Taylor principle ⇔ `φ_π > 1` | `SchmittGroheUribe.phiSGU`, `SchmittGroheUribe.taylorCoeff_phiSGU` |
| A.17, p. 655 | `A` decreasing to `θ/Ȳ`; `B` monotone to `φ_πθ/Ȳ`; the bound `Π̄` | `SchmittGroheUribe.sguA_antitone`, `SchmittGroheUribe.sguA_tendsto`, `SchmittGroheUribe.sguB_strictAntiOn`, `SchmittGroheUribe.sguB_tendsto`, `SchmittGroheUribe.sguPibar_spec`, `SchmittGroheUribe.sgu_no_successor` |
| A.17, p. 655 | no hyperinflation; the unique perfect-foresight equilibrium | `SchmittGroheUribe.sgu_no_hyperinflation`, `SchmittGroheUribe.sgu_deflation_tendsto`, `SchmittGroheUribe.sgu_unique_pf_equilibrium` |
| A.17, p. 655 | both fail when `β + θΠ*(1 − φ_π) < 0` | `SchmittGroheUribe.e5_counterexample` |
