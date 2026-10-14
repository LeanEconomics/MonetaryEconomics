# Source map

Galí (2015), *Monetary Policy, Inflation, and the Business Cycle*, 2nd ed.,
Chapter 8, "Monetary Policy in the Open Economy" (pp. 223–260), with Appendix 8.1 and
Exercises 8.1–8.2. Each formalised claim, equation or exercise is listed with its Lean name,
relative to the namespace `Gali.OpenEconomy`. Page numbers are book pages.

| Book | Claim | Lean |
| --- | --- | --- |
| Galí (2), p. 225 | CES consumption index | `Preferences.cesIndex` |
| Galí (4), p. 226 | variety demand; ∫P_H(i)C_H(i) = P_H C_H | `Preferences.Variety.spend_eq_iff`, `Preferences.Variety.spend_demand` |
| Galí (5), p. 226 | demands are the unique expenditure minimiser | `Preferences.expenditure_eq_iff`, `Preferences.expenditure_ge` |
| Galí (5), p. 226 | demands deliver C | `Preferences.cesIndex_demand` |
| Galí p. 226 | CPI = least cost of a unit of C | `Preferences.cpi_isLeast` |
| Galí p. 226 | υ is the import share when η = 1 or P_H = P_F | `Preferences.importShare`, `Preferences.importShare_of_eq` |
| Galí p. 227 | P_H C_H + P_F C_F = P C | `Preferences.expenditure_demand`, `Preferences.Variety.two_stage_expenditure` |
| Galí fn. 1, p. 225 | η → 1 limit of the index | `Preferences.cesIndex_tendsto_cd` |
| Galí fn. 2, p. 226 | CPI = P_H^{1−υ}P_F^υ at η = 1 | `Preferences.cpi_tendsto_cd`, `Preferences.expenditureCD_eq_iff` |
| Galí (12), p. 229 | p = (1−υ)p_H + υp_F = p_H + υs | `Identities.log_cpi_eq`, `Identities.hasFDerivAt_logCPI`, `Identities.hasDerivAt_cpiGap` |
| Galí fn. 4, p. 229 | (12) exact at η = 1 | `Identities.log_cpiCD_eq` |
| Galí (13), p. 229 | π = π_H + υΔs | `Identities.cpi_inflation`, `Identities.hasFDerivAt_inflationGap`, `Identities.cpi_inflation_cd` |
| Galí (14), p. 230 | s = e + p* − p_H | `Identities.tot_lop` |
| Galí p. 230 | q = (1−υ)s | `Identities.rer_eq`, `Identities.hasDerivAt_rerGap`, `Identities.rer_cd` |
| Galí (8), p. 227 | Arrow optimality condition | `RiskSharing.arrow_foc_of_optimal`, `RiskSharing.optimal_of_arrow_foc`, `RiskSharing.arrow_optimal_iff` |
| Galí (9), p. 228 | stochastic discount factor | `RiskSharing.arrow_sdf_iff` |
| Galí fn. 3, p. 228 | portfolio price = E[QD] | `RiskSharing.portfolio_price` |
| Galí (10), p. 228 | Q_t = E_t Q_{t,t+1} | `RiskSharing.bond_price`, `RiskSharing.bond_price_expectation` |
| Galí (15), p. 230 | foreign Arrow condition | `RiskSharing.foreign_sdf_iff`, `RiskSharing.foreign_optimal_iff` |
| Galí (16), p. 231 | C = ϑC*Z^{1/σ}𝒬^{1/σ} | `RiskSharing.riskSharing_ratio_const`, `RiskSharing.riskSharing`, `RiskSharing.vartheta_eq_one` |
| Galí (17), p. 231 | c = y* + (z+q)/σ | `RiskSharing.riskSharing_log`, `RiskSharing.riskSharing_log_tot`, `RiskSharing.riskSharing_log_cd` |
| Galí p. 231 | exact UIP condition | `UIP.uip_exact`, `UIP.uip_node_iff` |
| Galí (18), p. 232 | i = i* + E_tΔe | `UIP.hasFDerivAt_uipGap`, `UIP.uipGap_zero`, `UIP.uipGap_const` |
| Galí (19), p. 232 | terms-of-trade difference equation | `UIP.tot_difference` |
| Galí (20), fn. 5, p. 232 | forward solution | `UIP.tot_forward`, `UIP.forward_iff`, `UIP.forward_counterexample` |
| Galí p. 232 | (19) implied by the Euler equations, (17), (13) | `UIP.tot_difference_of_eulers` |
| Galí (12), p. 229 | p − p_H = υs; first order, exact if η = 1 | `Identities.log_cpi_eq`, `Identities.hasDerivAt_cpiGap`, `Identities.log_cpiCD_eq`, `AggregateDemand.eq25_ces`, `AggregateDemand.eq25_cd` |
| Galí p. 234 | X = υS^ηY*; trade balanced at the symmetric steady state | `AggregateDemand.exports_eq`, `AggregateDemand.trade_balanced_ss`, `AggregateDemand.netExports_ss` |
| Galí (24), p. 235 | goods-market clearing, exact | `AggregateDemand.eq24`, `AggregateDemand.log_eq24` |
| Galí (25), p. 235 | y = (1−υ)c + υ(2−υ)ηs + υy* as a derivative | `AggregateDemand.eq25` |
| Galí (26), p. 235 | Euler equation in π_H | `AggregateDemand.eq26` |
| Galí (27), p. 235 | s = σ_υ(y − y*) − (1−υ)Φz | `AggregateDemand.eq27`, `AggregateDemand.eq27_proc` |
| Galí p. 235 | 1 + υ(ϖ−1) = (1−υ)² + υ(2−υ)ση > 0; Φ, σ_υ > 0 | `AggregateDemand.one_add_mul_varpi`, `AggregateDemand.one_add_mul_varpi_pos`, `AggregateDemand.Phi_pos`, `AggregateDemand.sigmaU_pos` |
| Galí (28), p. 235 | open-economy DIS | `AggregateDemand.eq26_iff_eq28` |
| Galí p. 235 | ση > 1 ⇒ σ_υ decreasing in υ | `AggregateDemand.sigmaU_strictAntiOn` |
| Galí (29)–(30), p. 235 | gap form and rⁿ | `AggregateDemand.eq28_iff_eq29`, `AggregateDemand.natRate` |
| Galí p. 236 | nx = y − c − υs to first order | `AggregateDemand.hasFDerivAt_netExports`, `AggregateDemand.netExports_eq` |
| Galí (31), p. 236 | nx = υ(ϖ/σ − 1)s − (υ/σ)z; σ = η = 1 ⇒ invariant to s | `AggregateDemand.eq31`, `AggregateDemand.nxCoef_eq_zero`, `AggregateDemand.eq31_unit` |
| Galí p. 236 | "υ large ⇒ depreciation improves nx" is false | `AggregateDemand.not_large_openness_improves`, `AggregateDemand.nxCoef_counterexample`, `AggregateDemand.nxCoef_one_nonpos` |
| Galí p. 236 | corrected sign statements | `AggregateDemand.nxCoef_eventually_pos`, `AggregateDemand.nxCoef_pos_iff` |
| Galí (32), p. 237 | y = a + (1−α)n to first order | `Supply.eq32_exact`, `Supply.eq32`, `Supply.dispersion_family_first_order` |
| Galí (33)–(34), p. 237 | markup equation; NKPC in y, s, a, z | `Supply.eq33`, `Supply.eq34` |
| Galí (35), p. 238 | natural output; Γ_a > 0 | `Supply.eq35_iff`, `Supply.GammaA_pos` |
| Galí p. 238 | σ − υ(ϖ−1)σ_υ = σ_υ | `Supply.sigma_sub_eq_sigmaU` |
| Galí p. 238 | σ = η = 1 ⇒ Γ_* = 0, Γ_z < 0 (υ > 0) | `Supply.GammaStar_unit`, `Supply.GammaZ_unit_neg` |
| Galí fn. 8, p. 238 | υ = 0 ⇒ Γ_z = 0 | `Supply.GammaZ_zero` |
| Galí (36)–(37), p. 238 | markup gap; open-economy NKPC | `Supply.eq36`, `Supply.sgap_eq`, `Supply.eq37` |
| Galí p. 238 | υ = 0 or σ = η = 1 ⇒ κ_υ = κ | `Supply.kappaU_zero`, `Supply.kappaU_unit` |
| Galí p. 239 | ση > 1 ⇒ κ_υ decreasing in υ | `AggregateDemand.one_lt_varpi`, `Supply.kappaU_strictAntiOn` |
| Galí (38), p. 239 | rⁿ with Ψ_*, Ψ_z; limits as υ → 0 | `Supply.eq38`, `Supply.tendsto_PsiStar`, `Supply.tendsto_PsiZ` |
| Galí (37), p. 238 / (29), p. 236 | open-economy NKPC and DIS with σ_υ, κ_υ | `TaylorRule.NKPC`, `TaylorRule.DISGap`, `AggregateDemand.sigmaU`, `Supply.kappaU` |
| Galí p. 235 | 1 + υ(ϖ−1) > 0; ση > 1 ⇒ σ_υ decreasing in υ | `AggregateDemand.one_add_mul_varpi_pos`, `AggregateDemand.sigmaU_strictAntiOn` |
| Galí (39), p. 239 | Taylor rule; gap form | `TaylorRule.InterestRule`, `TaylorRule.taylorRule_iff_gap` |
| Galí (40), p. 240 | system ⇔ x_t = A_υE_t x_{t+1} + B_υu_t | `TaylorRule.equilibrium_iff_solves` |
| Galí (41), p. 240 | determinacy ⇔ κ_υ(φ_π−1) + (1−β)φ_y > 0 | `TaylorRule.schurStable_AU_iff`, `TaylorRule.determinate_iff_41`, `TaylorRule.determinate_iff_41_primitives` |
| Galí p. 240 | unique bounded equilibrium under (41); otherwise not | `TaylorRule.equilibrium_unique`, `TaylorRule.equilibrium_not_unique` |
| Galí p. 241 | monetary shock responses, unique MSV equilibrium | `TaylorRule.monetary_shock`, `TaylorRule.equilibrium_iff_msv`, `TaylorRule.msv_structural`, `TaylorRule.msv_unique` |
| Galí p. 241 | Λ_v > 0 under (41) | `TaylorRule.msvLambda_pos` |
| Galí p. 241 | nominal and real rate responses; real-rate bracket positive | `TaylorRule.monNomCoef_eq_book`, `TaylorRule.monRealCoef_eq_book`, `TaylorRule.monRealCoef_pos` |
| Galí p. 241 | s = σ_υỹ | `TaylorRule.monetary_tot` |
| Galí p. 242 | Δe | `TaylorRule.monetary_exchangeRate` |
| Galí p. 242 | permanent price-level fall κ_υΛ_v/(1−ρ_v) | `TaylorRule.expected_inflation_tsum`, `TaylorRule.expected_inflation_hasSum`, `TaylorRule.priceLevel_longRun` |
| Galí p. 242 | overshooting ⇔ σ_υ(1−βρ_v)(1−ρ_v) > κ_υρ_v ⇔ nominal rate rises | `TaylorRule.overshoot_iff`, `TaylorRule.overshoot_iff_nominal_rises`, `TaylorRule.exchangeRate_longRun_change` |
| Galí p. 241 | Λ_v increasing in openness (corrected hypotheses) | `TaylorRule.lambdaV_lt_of_slope_pos`, `TaylorRule.lambdaV_strictMonoOn` |
| Galí p. 241 | the printed claim is false | `TaylorRule.printed_monotonicity_false`, `TaylorRule.counterexample_strictAntiOn`, `TaylorRule.counterexample_values` |
| Galí p. 243 | ση = 1 ⇒ closed-economy responses | `TaylorRule.closed_economy_equivalence`, `TaylorRule.closed_economy_responses`, `TaylorRule.sigma_eta_one` |
| Galí p. 246 | exact C = Y^{1−υ}(Y*)^υ, Y = SY* | `OptimalPolicy.consumption_possibilities` |
| Galí fn. 2, p. 230 | P_F/P = S^{1−υ}, P_H/P = S^{−υ} (η = 1) | `OptimalPolicy.relPrices_cpi` |
| Galí p. 246 | MRS = MRT | `OptimalPolicy.hasDerivAt_frontier`, `OptimalPolicy.foc_iff` |
| Galí p. 246 | N = [(1−υ)(1−α)]^{1/(1+φ)} optimal, unique | `OptimalPolicy.planner_optimal_iff`, `OptimalPolicy.planner_existsUnique`, `OptimalPolicy.plannerWelfare_le` |
| Galí p. 246 | the flexible-price markup | `OptimalPolicy.markup_eq` |
| Galí p. 246 | first line omits (1−τ) | `OptimalPolicy.printedFirstLine_eq_markup_iff` |
| Galí p. 247 | (1−τ)(1−υ)M = 1 ⇔ flex allocation efficient | `OptimalPolicy.flexEmployment_eq_opt_iff`, `OptimalPolicy.flex_optimal` |
| Galí p. 247 | subsidy smaller than closed-economy one; negative (a tax) at the calibration | `OptimalPolicy.optSubsidy_lt_closed`, `OptimalPolicy.optSubsidy_neg_iff`, `OptimalPolicy.optSubsidy_calibration` |
| Galí p. 247 | SDIT optimal | `OptimalPolicy.divine_coincidence`, `OptimalPolicy.optimal_policy` |
| Galí (42), pp. 247–248 | φ_π > 1 implements SDIT uniquely; i = rⁿ indeterminate | `OptimalPolicy.rule42_unique`, `OptimalPolicy.equilibrium_iff_zero`, `OptimalPolicy.exogRule_not_determinate`, `OptimalPolicy.exogRule_not_unique` |
| Galí p. 248 | Γ_a > 0; technology ⇒ real depreciation; sⁿ decomposition | `OptimalPolicy.GammaA_pos_of_lt_one`, `OptimalPolicy.tot_tech_coeff_pos`, `OptimalPolicy.natural_tot_eq` |
| Galí p. 248 | preference shock ⇒ appreciation, all parameters | `OptimalPolicy.tot_pref_coeff_neg` |
| Galí p. 248 | e^{DIT} = sⁿ − p*, p^{DIT} = υsⁿ | `OptimalPolicy.dit_exchange_rate_cpi` |
| App. 8.1, p. 255 | second-order expansion (exact + O(s³)) | `Welfare.utility_exact`, `Welfare.secondOrder_eq`, `Welfare.period_utility_second_order`, `Welfare.efficiency_iff` |
| App. 8.1, pp. 255–256 | sign of 𝕎 | `Welfare.welfare_sign`, `Welfare.appendix_sign_error` |
| Lemma 2, p. 256 | exact for the Calvo recursion; only up to t.i.p. | `Welfare.lemma2_calvo`, `Welfare.lemma2_printed_fails` |
| Galí (43)–(44), p. 249 | 𝕎 and 𝕍 | `Welfare.welfare_eq_loss43`, `Welfare.loss43_eq_pathLoss`, `Welfare.welfare_stationary44` |
| Galí p. 249 | (1−υ) × closed-economy weights | `Welfare.closed_economy_weights` |
| Galí p. 256 | ỹ = (1−α)ñ | `Welfare.gap_eq_employment` |
| Galí p. 250 | PEG ⇒ i = i* | `SimpleRules.peg_rate` |
| Table 8.1 | loss row from the s.d.s; λ includes Θ | `SimpleRules.tableLoss_values`, `SimpleRules.tableLoss_consistent`, `SimpleRules.tableLoss_noTheta_inconsistent`, `SimpleRules.tot_eq_output` |
| Galí p. 251 | PEG most volatile only among strict regimes | `SimpleRules.peg_not_most_volatile_inflation`, `SimpleRules.peg_most_volatile_strict`, `SimpleRules.peg_most_volatile_gap` |
| Galí fn. 14 | world output affects sⁿ, c, CPI, e | `SimpleRules.world_output_effects` |
| Galí fn. 15 | unit root in e only under FDIT/FCIT | `SimpleRules.sdit_meanReverting`, `SimpleRules.scit_meanReverting`, `SimpleRules.peg_meanReverting`, `SimpleRules.fdit_permanent_shift`, `SimpleRules.fdit_unit_root`, `SimpleRules.fcit_cumulative` |
| Ex 8.1, p. 259 | competitive firm ⇔ w − p_H = a | `Ex8_1.firm_optimum_iff`, `Ex8_1.firm_log_iff` |
| Ex 8.1, p. 259 | labour supply ⇔ household optimum | `Ex8_1.household_optimum_iff`, `Ex8_1.labour_supply_log_iff` |
| Ex 8.1, p. 258 | no assets ⇒ p + c = p_H + y | `Ex8_1.budget_tradeBalance`, `Ex8_1.tradeBalance_log` |
| Ex 8.1, p. 259 | unit elasticity ⇒ s = y − y* | `Ex8_1.tot_of_marketClearing`, `Ex8_1.tot_log_iff` |
| Ex 8.1(a), p. 259 | c = (1−υ)y + υy* | `Ex8_1.consumption_eq` |
| Ex 8.1(a), p. 259 | y, s, e = m − y*, p_H (unique) | `Ex8_1.staticEq_iff`, `Ex8_1.staticEq_existsUnique`, `Ex8_1.equilibrium_iff` |
| Ex 8.1(a), p. 259 | σ = 1 ⇒ y independent of y* | `Ex8_1.outputSol_sigma_one`, `Ex8_1.outputSol_indep_iff` |
| Ex 8.1(b), p. 259 | peg ⇒ money endogenous, m = ē + y* uniquely | `Ex8_1.peg_iff`, `Ex8_1.peg_existsUnique`, `Ex8_1.pegEquilibrium_iff` |
| Ex 8.2(a), p. 260 | determinacy ⇔ φ_π > 1 | `Ex8_2.taylor_determinate_iff` |
| Ex 8.2(a), p. 260 | closed forms; existence and uniqueness | `Ex8_2.taylor_iff`, `Ex8_2.taylor_exists`, `Ex8_2.taylor_unique`, `Ex8_2.taylor_closed_forms_38` |
| Ex 8.2(a), p. 260 | response signs and exchange-rate path | `Ex8_2.taylor_signs_38`, `Ex8_2.taylor_irf_38`, `Ex8_2.taylor_irf_tendsto` |
| Ex 8.2(b), p. 260 | stable root λ ∈ (0,1), other root > 1 | `Ex8_2.exists_root`, `Ex8_2.root_unique`, `Ex8_2.other_root` |
| Ex 8.2(b), p. 260 | factorisation | `Ex8_2.peg_nkpc_iff` |
| Ex 8.2(b), p. 260 | unique bounded peg equilibrium, closed forms | `Ex8_2.peg_iff`, `Ex8_2.peg_exists`, `Ex8_2.peg_unique`, `Ex8_2.pegP_closed` |
| Ex 8.2(b), p. 260 | i = i* under the peg; response signs | `Ex8_2.peg_rate_38`, `Ex8_2.peg_irf_signs` |
| Fig. 8.1, Table 8.1 (simulations) | Impulse responses and simulated moments | Computational; Table 8.1 losses recomputed in `SimpleRules.tableLoss_values` |
