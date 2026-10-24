# Source map

Galí (2015), *Monetary Policy, Inflation, and the Business Cycle*, 2nd ed.,
Chapter 2, "A Classical Monetary Model" (pp. 17–51), with Appendix 2.1 and
Exercises 2.1–2.9. Each formalised claim, equation or exercise is listed with its Lean
name, relative to the namespace `Gali.ClassicalMonetaryModel`. Page numbers are book pages.

| Book | Claim | Lean |
| --- | --- | --- |
| (25) p. 27, (28) p. 29 | `0 ≤ a < 1`, bounded adapted forcing: the forward series is the unique bounded solution of `z_t = a E_t z_{t+1} + u_t` | `ExpectationSystem.forwardSeries_solves`, `ExpectationSystem.eq_forwardSeries` |
| p. 26 and passim | The expectation axioms hold under genuine uncertainty | `ExpectationsFiniteTree.FiniteTree.toExpectationSystem` |
| Galí p. 18 | U_c>0, U_cc≤0, U_n≤0, U_nn≤0, U_cz>0 | `Household.margUtilC_pos`, `Household.hasDerivAt_margUtilC`, `Household.margUtilN_nonpos`, `Household.hasDerivAt_margUtilN`, `Household.hasDerivAt_margUtilC_Z` |
| Galí p. 21 | separability; Z does not affect the MRS | `Household.hasDerivAt_margUtilC_N`, `Household.mrs_eq` |
| Galí (4), p. 19 | −U_n/U_c = W/P necessary and sufficient (general U) | `Household.static_foc_general_necessary`, `Household.static_foc_general_iff`, `Household.static_foc_general_sufficient` |
| Galí (7), p. 21 | W/P = C^σN^φ, iff | `Household.static_optimum_iff` |
| Galí (9), p. 21 | w − p = σc + φn (exact) | `Household.labour_supply_log_iff` |
| Galí (5), p. 19 | Euler necessary (perturbation) and sufficient (general U) | `Household.euler_general_necessary`, `Household.euler_general_sufficient`, `Household.euler_general_ratio` |
| Galí (8), p. 21 | functional-form Euler under uncertainty | `Household.euler_necessary`, `Household.euler_necessary_finite`, `Household.euler_sufficient`, `Household.eulerEq_ratio_form` |
| Galí (1)–(8), pp. 18–21 | infinite-horizon optimality ⟺ FOCs + transversality | `Household.optimal_of_foc`, `Household.budgetBinds_of_optimal`, `Household.staticFOC_of_optimal`, `Household.eulerDet_of_optimal`, `Household.optimal_iff`, `Household.tsum_le_of_optimal` |
| Galí (6), pp. 19–20 | transversality is necessary | `Household.tvc_liminf_of_optimal`, `Household.tvc_of_optimal_of_tendsto`, `Household.bookTVC_iff` |
| Galí fn. 3, p. 20 | B_t = 0 ⇒ (6) | `Household.tvc_of_zero_bonds`, `Household.tvc_of_zero_bonds_stoch` |
| Galí (51), App. 2.1, p. 44 | Taylor step: value 1, gradient (1,−σ,−1,1) | `Household.eulerKernel_steady`, `Household.hasFDerivAt_eulerKernel`, `Household.eulerKernel_linearisation` |
| Galí (10), p. 21 / p. 44 | log-linear Euler as an exact derivative | `Household.hasDerivAt_log_eulerMoment_family`, `Household.linearisedEuler_eq_zero_iff` |
| Galí (10), p. 21 | exact under perfect foresight | `Household.pf_eulerEq_iff`, `Household.pf_eulerEq_imp_eulerLogLinear` |
| Galí fn. 5, p. 22 | ρ = −log β ≃ β⁻¹ − 1 | `Household.neg_log_le_inv_sub_one`, `Household.discount_rate_gap`, `Household.discount_rate_gap_isBigO` |
| Galí (11), p. 22 | money demand | `Household.MoneyDemand`, `Household.moneyDemand_iff_price` |
| Galí (14), p. 23 | profit-max FOC necessary and sufficient; unique for 0<α<1 | `FirmsEquilibrium.labour_demand_iff`, `FirmsEquilibrium.labour_demand_unique` |
| Galí (15), p. 23 | log labour demand | `FirmsEquilibrium.labour_demand_log_iff` |
| Galí (18),(19),(21), pp. 23–24 | unique solution with explicit ψ's | `FirmsEquilibrium.staticBlock_iff`, `FirmsEquilibrium.staticBlock_exists`, `FirmsEquilibrium.staticBlock_unique` |
| Galí pp. 21–23 | static block exactly log-linear in levels | `FirmsEquilibrium.levelsBlock_iff_log`, `FirmsEquilibrium.levelsBlock_iff_explicit` |
| Galí (20), p. 23 | real rate | `FirmsEquilibrium.realRate_eq`, `FirmsEquilibrium.realRate_eq_pf`, `FirmsEquilibrium.equilibrium_realRate` |
| Galí p. 24 | ψ_ya>0; real wage rises; sign ψ_na = sign(1−σ) | `FirmsEquilibrium.psiYa_pos`, `FirmsEquilibrium.psiWa_pos`, `FirmsEquilibrium.sign_psiNa` |
| Galí p. 24 | r falls with a, rises with z | `FirmsEquilibrium.rateCoeffA_neg_iff`, `FirmsEquilibrium.rateCoeffZ_pos_iff` |
| Galí p. 24 | neutrality | `FirmsEquilibrium.neutrality`, `FirmsEquilibrium.neutrality_across_policies`, `FirmsEquilibrium.levels_neutrality`, `FirmsEquilibrium.realBondPrice_neutral` |
| Galí §2.4.4, p. 30 | all policies welfare-equivalent | `FirmsEquilibrium.welfare_policy_invariant`, `FirmsEquilibrium.welfare_limit_policy_invariant` |
| Galí (22), p. 24 | Fisher equation i_t = E_tπ_{t+1} + r_t | `InterestRules.Fisher` |
| Galí p. 25 | steady state i = ρ + π | `InterestRules.fisher_steadyState_iff` |
| Galí §2.4.1, p. 26 | exogenous rate: π_t = π + v_{t−1} − r̂_{t−1} + ξ_t equilibrium for every MDS ξ, and only these | `InterestRules.exo_equilibrium_iff`, `InterestRules.exoPath_fisher` |
| Galí p. 26 | price-level form | `InterestRules.price_exoPath` |
| Galí p. 26 | indeterminacy: two distinct bounded equilibria | `InterestRules.exo_two_equilibria`, `InterestRules.perfectForesight_exo_pinned` |
| Galí p. 26 | a genuine sunspot under uncertainty (coin tree) | `InterestRules.coin_exo_sunspot` |
| Galí (24), p. 27 | rule + Fisher ⟺ φ_π π̂_t = E_tπ̂_{t+1} + r̂_t − v_t | `InterestRules.rule_fisher_iff_eq24` |
| Galí (25), p. 27 | φ_π > 1 ⇒ forward series is the unique bounded solution | `InterestRules.eq25_unique_bounded` |
| Galí p. 27 | AR(1) closed form for π_t | `InterestRules.inflation_ar1_closed_form`, `InterestRules.inflation_closed_form_book` |
| Galí p. 27 | monetary-shock impact derivatives | `InterestRules.impact_representation`, `InterestRules.hasDerivAt_inflImpact`, `InterestRules.hasDerivAt_rateImpact`, `InterestRules.hasDerivAt_moneyImpact` |
| Galí p. 27 | prices fall; rate falls iff ρ_v > 0 | `InterestRules.inflation_falls`, `InterestRules.rate_falls_iff` |
| Galí p. 27 | liquidity effect iff ηρ_v > 1 | `InterestRules.liquidity_effect_iff` |
| Galí (26), p. 28 | φ_π < 1: every MDS gives a bounded solution; all solutions of form (26) | `InterestRules.eq26_multiplicity`, `InterestRules.path26_bounded`, `InterestRules.eq24_iff_path26`, `InterestRules.eq26_levels` |
| Galí fn. 7, p. 28 | τ-combinations are MDS; arbitrary inflation response | `InterestRules.isMDS_fn7`, `InterestRules.fn7_surprise` |
| Galí p. 28 | Taylor principle: determinate ⟺ φ_π > 1 (φ_π ≥ 0, incl. φ_π = 1) | `InterestRules.taylor_principle` |
| Galí p. 28 (φ_π = 1, omitted) | never unique; existence can fail | `InterestRules.not_unique_of_le_one`, `InterestRules.phi_one_no_bounded_solution` |
| Galí (27), p. 29 | (11)+(16)+(22) ⇒ (27); converse for η > 0 | `MoneySupply.eq27_of_model`, `MoneySupply.fisher_of_eq27` |
| Galí (28), p. 29 | forward solution unique bounded for η ≥ 0 | `MoneySupply.eq28_unique` |
| Galí fn. 8, p. 29 | (27) ⟺ the p − m equation | `MoneySupply.eq27_iff_tilde` |
| Galí (29), p. 29 | money-growth representation, unique with p − m bounded | `MoneySupply.eq29_unique`, `MoneySupply.fwd29_eq` |
| Galí p. 29 | interest-rate expression | `MoneySupply.interest_rate_29` |
| Galí p. 30 | AR(1) money growth: p and i closed forms | `MoneySupply.ar1_money_equilibrium`, `MoneySupply.ar1_series29` |
| Galí p. 30 | impact responses | `MoneySupply.impact_representationM`, `MoneySupply.hasDerivAt_priceImpactM`, `MoneySupply.hasDerivAt_moneyImpactM`, `MoneySupply.hasDerivAt_rateImpactM` |
| Galí p. 30 | price overshooting; no liquidity effect | `MoneySupply.price_overshoots_iff`, `MoneySupply.price_overshoots`, `MoneySupply.no_liquidity_effect_iff` |
| Galí (32), p. 32 | budget constraint with A = B + M | `MIUSeparable.budget_rewrite` |
| Galí p. 32 | 1 − e^{−i} ≃ i | `MIUSeparable.one_sub_exp_neg_le`, `MIUSeparable.mul_exp_neg_le_one_sub_exp_neg` |
| Galí (33), pp. 32–33 | U_m/U_c = 1 − Q necessary (general U) | `MIUSeparable.miu_foc_necessary` |
| Galí (33), pp. 32–33 | necessary and sufficient (separable U) | `MIUSeparable.miu_static_optimum_iff`, `MIUSeparable.miu_static_optimum_iff_exp` |
| Galí p. 33 | U_c, U_n independent of M/P | `MIUSeparable.hasDerivAt_sepUtil_C`, `MIUSeparable.hasDerivAt_sepUtil_N` |
| Galí (34), p. 34 | money demand | `MIUSeparable.money_demand_iff` |
| Galí (35), p. 34 | log-linear money demand, η = 1/(ν(e^i − 1)) | `MIUSeparable.hasFDerivAt_logMoneyDemand` |
| Galí p. 34 | η ≃ 1/(νi) | `MIUSeparable.eta_le`, `MIUSeparable.exp_neg_div_le_eta` |
| Galí (36), p. 34 | ν = σ case | `MIUSeparable.hasFDerivAt_logMoneyDemand_unit`, `MIUSeparable.money_demand_unit_elastic` |
| Galí p. 35 | U_c, U_m of the CES composite | `MIUNonseparable.hasDerivAt_nsUtil_C`, `MIUNonseparable.hasDerivAt_nsUtil_m` |
| Galí (37), p. 35 | labour supply | `MIUNonseparable.labour_foc_necessary` |
| Galí (38), p. 35 | Euler equation | `MIUNonseparable.euler5_iff_miuEuler` |
| Galí (39), p. 35 | money demand | `MIUNonseparable.money_foc_necessary`, `MIUNonseparable.money_demand_39_iff` |
| Galí p. 35 | ν = σ reduces to separable case | `MIUNonseparable.miuEuler_nu_eq_sigma`, `MIUNonseparable.labour_supply_nu_eq_sigma` |
| Galí fn. 10, p. 36 | unit consumption elasticity | `MIUNonseparable.moneyDemand39_homogeneous` |
| Galí (40), p. 36 | log money demand | `MIUNonseparable.log_moneyDemand39`, `MIUNonseparable.hasFDerivAt_log_money_demand_40` |
| Galí p. 36 | w − p = σc + φn + (ν − σ)(c − x) | `MIUNonseparable.labour_supply_log` |
| Galí p. 36 | c − x = χ(c − (m − p)) | `MIUNonseparable.hasFDerivAt_gap` |
| Galí pp. 36–37 | χ: partial derivative, both forms, χ ∈ [0,1) | `MIUNonseparable.hasDerivAt_logX_steady_state`, `MIUNonseparable.chi1_eq_chi`, `MIUNonseparable.share_at_km`, `MIUNonseparable.chi_mem` |
| Galí p. 36 | k_m | `MIUNonseparable.km_money_demand` |
| Galí (41), p. 37 | ϖ | `MIUNonseparable.varpi_eq`, `MIUNonseparable.eq41`, `MIUNonseparable.varpi_pos_iff` |
| Galí (42)–(43), p. 37 | y = ψ_ya a + ψ_yi i | `MIUNonseparable.eq43`, `MIUNonseparable.psiYi_neg_iff` |
| Galí p. 38 | ν → ∞ limit, −k_m/8; numbers | `MIUNonseparable.tendsto_psiYi_nu`, `MIUNonseparable.psiYi_limit_calib`, `MIUNonseparable.tendsto_calib_beta_one`, `MIUNonseparable.psiYi_limit_km_base`, `MIUNonseparable.psiYi_limit_km_m2` |
| Galí (44)–(45), p. 38 | y = Θ(m − p), Θ ∈ [0,1) | `MIUNonseparable.eq44_45`, `MIUNonseparable.Theta_mem` |
| Galí (46), p. 39 | MIU Euler equation | `MIUNonseparable.pf_miuEuler_iff`, `MIUNonseparable.hasDerivAt_log_miuMoment_family`, `MIUNonseparable.linearisedMIUEuler_eq_zero_iff`, `MIUNonseparable.eulerGap_iff_eulerLinear` |
| Galí (47), p. 39 | Euler in output | `MIUNonseparable.eq47_of_clearing` |
| Galí (48), p. 39 | price-level forward solution | `MIUNonseparable.price_level_48`, `MIUNonseparable.price_level_48_exists` |
| Galí pp. 39–40 | countercyclical real wage | `MIUNonseparable.real_wage_countercyclical`, `MIUNonseparable.real_wage_strictly_countercyclical` |
| Galí (49)–(50), p. 40 | planner FOCs | `FriedmanRule.planner_foc_necessary`, `FriedmanRule.planner_optimum_iff` |
| Galí p. 41 | (49) holds whatever the policy | `FriedmanRule.decentralised_49` |
| Galí p. 41 | efficient ⟺ i_t = 0 ∀t | `FriedmanRule.decentralised_efficient_iff`, `FriedmanRule.decentralised_optimal_iff_friedman` |
| Galí p. 41 | π = −ρ | `FriedmanRule.friedman_steady_state_inflation` |
| Galí p. 41 | i = 0 ⇒ indeterminacy | `FriedmanRule.friedman_equilibrium_iff`, `FriedmanRule.friedman_indeterminate`, `FriedmanRule.friedman_sunspot_coin` |
| Galí fn. 13, p. 41 | determinacy ⟺ φ_π > 1 | `FriedmanRule.fn13_unique`, `FriedmanRule.fn13_exists`, `FriedmanRule.fn13_not_unique` |
| Galí p. 42 | i_t = φ(r_{t−1} + π_t) ⇒ i ≡ 0, π_t = −r_{t−1} | `FriedmanRule.lagged_rule_unique`, `FriedmanRule.lagged_rule_exists`, `FriedmanRule.inflation_rule_implies_zero_rate` |
| Ex 2.1, p. 46 / (4) p. 19 | U_C, U_N; −U_N/U_C = νC/(1−N) | `Ex2_1.hasDerivAt_periodUtility_C`, `Ex2_1.hasDerivAt_periodUtility_N`, `Ex2_1.mrs_eq` |
| Ex 2.1 / (4) | labour FOC, necessary and sufficient | `Ex2_1.static_optimum_iff` |
| Ex 2.1 | log labour supply; log-linear form | `Ex2_1.labour_supply_log_iff`, `Ex2_1.hasDerivAt_labourSupply_family` |
| Ex 2.1 / (5) | Euler equation, necessary and sufficient | `Ex2_1.euler_necessary`, `Ex2_1.euler_necessary_finite`, `Ex2_1.euler_sufficient` |
| Ex 2.1 / App 2.1 | moment form; perfect-foresight log form | `Ex2_1.eulerEq_iff_moment`, `Ex2_1.pf_eulerEq_iff` |
| Ex 2.1 / App 2.1 | log-linear Euler with the employment term | `Ex2_1.hasDerivAt_moment_family`, `Ex2_1.linearisedEuler_zero_iff` |
| Ex 2.2 a(ii) | money growth supporting it | `Ex2_2.strictIT_money_growth` |
| Ex 2.2 a(iii) | constant money growth does not stabilise | `Ex2_2.constMoneyGrowth_inflation`, `Ex2_2.constMoneyGrowth_not_stabilising` |
| Ex 2.2 b(i), p. 47 | price-level rule: forward solution unique and exists; AR(1) form | `Ex2_2.plEquilibrium_iff`, `Ex2_2.plEquilibrium_unique_iff`, `Ex2_2.plEquilibrium_exists`, `Ex2_2.pl_ar1` |
| Ex 2.2 b(ii) | money rule: forward solution unique and exists | `Ex2_2.moneyEquilibrium_iff`, `Ex2_2.moneyEquilibrium_unique_iff`, `Ex2_2.moneyEquilibrium_exists` |
| Ex 2.2 b(iii) | money rule as an interest-rate rule with ψ = 1/η | `Ex2_2.moneyRule_as_interestRule`, `Ex2_2.moneyEquilibrium_iff_interestRule` |
| Ex 2.3 | Blanchard–Kahn with one predetermined variable | `Ex2_3.saddle_unique`, `Ex2_3.saddle_exists`, `Ex2_3.stable_not_unique`, `Ex2_3.outside_nonexistence`, `Ex2_3.bothOutside_roots` |
| Ex 2.3(a) | equilibrium i and π | `Ex2_3.pa_interest_forward`, `Ex2_3.pa_inflation_eq` |
| Ex 2.3(b), p. 48 | moving-average rule: determinate ⟺ φπ > 1 | `Ex2_3.maBar_succ`, `Ex2_3.ma_determinate_iff`, `Ex2_3.ma_determinate_iff_of_nonneg` |
| Ex 2.3(c) | MA rule = PA rule with φi = δ | `Ex2_3.ma_iff_pa`, `Ex2_3.ma_equilibrium_iff_pa`, `Ex2_3.pa_as_ma` |
| Ex 2.4(a), p. 48 | money FOC iff; money demand; semi-elasticity | `Ex2_4.money_optimum_iff`, `Ex2_4.money_demand_iff`, `Ex2_4.hasDerivAt_money_demand_log` |
| Ex 2.4(a) | bond Euler equation, iff | `Ex2_4.euler_necessary`, `Ex2_4.euler_necessary_finite`, `Ex2_4.euler_sufficient` |
| Ex 2.4(b) | Friedman rule: welfare strictly decreasing in i, supremum as i → 0⁺ | `Ex2_4.friedman_rule`, `Ex2_4.friedman_rule_inflation` |
| Ex 2.4(c) | welfare cost λ(π): closed form, existence, uniqueness | `Ex2_4.welfareCost_levels`, `Ex2_4.welfareCost_levels_unique`, `Ex2_4.welfareCost_levels_none`, `Ex2_4.welfareCost_ratio`, `Ex2_4.welfareCost_ratio_unique` |
| Ex 2.4(d) | second-order welfare W̄ + W′h + ½W″h² + O(h³) | `Ex2_4.welfare_taylor`, `Ex2_4.welfare_fluctuations` |
| Ex 2.5(a), p. 49 | marginal utilities of (52) | `Ex2_5.hasDerivAt_utility_C`, `Ex2_5.hasDerivAt_utility_m`, `Ex2_5.hasDerivAt_utility_N` |
| Ex 2.5(a), p. 49 | labour FOC W/P = CN^φ (iff) | `Ex2_5.labour_optimum_iff` |
| Ex 2.5(a), (33) p. 32 | money FOC C = (1−Q)M/P (iff) | `Ex2_5.money_optimum_iff` |
| Ex 2.5(a), p. 49 | firm W = PA | `Ex2_5.firm_optimum_iff` |
| Ex 2.5(b), p. 49 | N_t = 1, Y_t = A_t | `Ex2_5.employment_eq_one`, `Ex2_5.output_eq_technology` |
| Ex 2.5(b), p. 49 | E_t[M_t/M_{t+1}] = e^{σ²/2}/(1+γ_m) | `Ex2_5.condExp_money_ratio` |
| Ex 2.5(b), p. 49 | constant V = 1 − βe^{σ²/2}/(1+γ_m) | `Ex2_5.velocity_of_constant` |
| Ex 2.5(b), p. 49 | exact equilibrium exists | `Ex2_5.candidate_isEquilibrium` |
| Ex 2.5(b), p. 49 | inflation | `Ex2_5.inflation_eq`, `Ex2_5.log_inflation_eq` |
| Ex 2.5(c), p. 49 | welfare closed form | `Ex2_5.hasSum_expected_welfare` |
| Ex 2.5(c), p. 49 | dependence on γ_m, σ_m² | `Ex2_5.welfare_strictAnti_gamma`, `Ex2_5.welfare_strictMono_var` |
| Ex 2.5(c), p. 49 | Friedman rule optimal (as supremum) | `Ex2_5.not_optimal_of_equilibrium`, `Ex2_5.tendsto_welfare_rate`, `Ex2_5.friedman_iff` |
| Ex 2.6, p. 49 | E_tπ_{t+1} = cπ_t | `Ex2_6.expected_infl_eq_c`, `Ex2_6.isEquilibrium_iff` |
| Ex 2.6, p. 49 | ϖ + σψ_yi = ϖ(φ+α)/D ≥ 0 | `Ex2_6.kappa_eq`, `Ex2_6.kappa_nonneg` |
| Ex 2.6, p. 49 | unique iff φ_π > 1 | `Ex2_6.determinate_iff`, `Ex2_6.unique_of_one_lt_abs_c`, `Ex2_6.exists_equilibrium`, `Ex2_6.not_unique_of_le_one` |
| Ex 2.7(a), p. 50 | U_c, U_m, U_n and signs | `Ex2_7.hasDerivAt_U_c`, `Ex2_7.hasDerivAt_U_m`, `Ex2_7.hasDerivAt_U_n`, `Ex2_7.U_m_nonneg`, `Ex2_7.U_n_neg` |
| Ex 2.7(a), p. 50 | second derivatives | `Ex2_7.hasDerivAt_U_mm`, `Ex2_7.U_mm_nonpos`, `Ex2_7.hasDerivAt_U_nn`, `Ex2_7.hasDerivAt_U_nm` |
| Ex 2.7(b), p. 50 | (W/P)(−S_m) ≃ i | `Ex2_7.shopping_rate_eq`, `Ex2_7.shopping_rate_approx` |
| Ex 2.7(c), p. 50 | money demand | `Ex2_7.money_demand`, `Ex2_7.money_demand_of_hasFDerivAt` |
| Ex 2.8(a), p. 50 | FOCs via KKT | `Ex2_8.kkt`, `Ex2_8.foc_cia_ineq`, `Ex2_8.nonneg_of_left_max` |
| Ex 2.8(b), p. 50 | output falls with money growth | `Ex2_8.output_of_binding`, `Ex2_8.output_strictAnti`, `Ex2_8.stationary_isEquilibrium` |
| Ex 2.8(c), p. 50 | optimal π = β − 1 | `Ex2_8.optimal_inflation` |
| Ex 2.9(a), p. 51 | KKT FOCs | `Ex2_9.kkt` |
| Ex 2.9(b), p. 51 | U_m = V₁ − V₂ = Pμ ≥ 0 | `Ex2_9.hasDerivAt_U_m`, `Ex2_9.U_m_eq_mul_mu`, `Ex2_9.U_m_nonneg` |
| Ex 2.5(b), p. 49 | i.i.d. Gaussian shocks exist; exact equilibrium exists | `Ex2_5.techInnovations`, `Ex2_5.moneyInnovations`, `Ex2_5.coord_indep`, `Ex2_5.exists_exact_equilibrium` |
| Ex 2.5(c), p. 49 | welfare = E₀ Σ βᵗ U_t (interchange) | `Ex2_5.integral_tsum_welfare` |
| Galí (3) p. 19 / Ex 2.8 | no-Ponzi; overtaking optimality | `Ex2_8.NoPonzi`, `Ex2_8.OptimalNP`, `Ex2_8.optimal_of_optimalNP` |
| Galí (6) p. 19 / Ex 2.8 | transversality is necessary | `Ex2_8.tvc_liminf_of_optimalNP`, `Ex2_8.eqTVC_of_optimalNP` |
| Ex 2.8(b), p. 50 | CIA binds in every equilibrium (γ ≥ 0) | `Ex2_8.cia_binds_of_tvc` |
| Ex 2.8(b), p. 50 | output (β/(1+γ))^{1/(1+φ)} in every equilibrium | `Ex2_8.output_eq_of_tvc` |
| Ex 2.8(b), p. 50 | slack-CIA equilibrium for β < 1+γ < 1 | `Ex2_8.slack_equilibrium_counterexample` |
| Ex 2.8(a), p. 50 | FOCs sufficient (vs competitors with M ≥ 0, TVC limit form) | `Ex2_8.overtakes_of_foc`, `Ex2_8.budget_binds_of_optimal`, `Ex2_8.u_le_tangent` |
