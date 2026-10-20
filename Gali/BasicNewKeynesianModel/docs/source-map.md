# Source map

Galí (2015), *Monetary Policy, Inflation, and the Business Cycle*, 2nd ed.,
Chapter 3, "The Basic New Keynesian Model" (pp. 52–97), with Appendices 3.1–3.4 and
Exercises 3.1–3.9. Each formalised claim, equation or exercise is listed with its Lean
name, relative to the namespace `Gali.BasicNewKeynesianModel`. Page numbers are book pages.

| Book | Claim | Lean |
| --- | --- | --- |
| §3.2, p. 55 | A price lasts `k + 1` periods with probability `(1 − θ)θᵏ`; these sum to one; survival `θᵏ` | `durationProb`, `survival_sum`, `tail_sum`, `CalvoParam` |
| §3.2, p. 55 | The average duration of a price is `1/(1 − θ)` | `mean_duration`, `CalvoParam.mean_duration` |
| p. 65; Woodford Prop. C.1 | Both roots inside the unit circle iff `|D| < 1 ∧ |T| < 1 + D` | `schurStable_iff_roots` |
| p. 65 | Under Schur–Cohn the only bounded solution of `x_t = A x_{t+1}` is zero; otherwise a nonzero bounded one exists | `homogeneous_eq_zero`, `exists_bounded_homogeneous` |
| p. 61 and passim | `z_t = a E_t z_{t+1} + u_t`, `|a| < 1`: at most one bounded solution; AR(1) forcing | `ExpectationSystem.forward_unique`, `ExpectationSystem.forward_ar1_solves` |
| p. 65 | Determinacy of `x_t = A E_t x_{t+1} + B u_t` iff Schur–Cohn | `ExpectationSystem.determinate_iff`, `ExpectationSystem.system_unique`, `ExpectationSystem.system_not_unique` |
| Galí (1), p. 53 / App 3.1 p. 83 | expenditure ≥ P·C; = iff C(i)=(P(i)/P)^{−ε}C a.e. | `CES.spend_ge`, `CES.spend_eq_iff` |
| Galí p. 53 | demand schedule delivers C; ∫P(i)C(i)=PC | `CES.cesAgg_demand`, `CES.spend_demand` |
| Galí App 3.1, p. 83 | max C for given X: C ≤ X/P, equality iff demand schedule | `CES.cesAgg_le_of_spend`, `CES.cesAgg_eq_iff_of_spend` |
| Galí p. 53, continuum [0,1] | all of the above with Lebesgue measure | `CES.unitInterval_expenditure_minimisation` |
| Galí p. 53, finite goods | all of the above with weights | `CES.Finite.finite_expenditure_minimisation` |
| Galí (12), p. 58 | Y = C | `CES.market_clearing` |
| Galí (7) p. 55 / (36) p. 84 | Π^{1−ε} = θ + (1−θ)(P*/P_{t−1})^{1−ε} | `CalvoIndex.calvo_recursion`, `CalvoIndex.calvo_recursion_lottery`, `CalvoIndex.calvo_recursion_of_dist` |
| Galí App 3.2, p. 84 | non-resetters = past distribution scaled by θ | `CalvoIndex.dist_law_of_motion`, `CalvoIndex.lottery_model` |
| Galí p. 55 | zero-inflation steady state ⇒ P* = P_{t−1} = P_t | `CalvoIndex.zero_inflation_iff`, `CalvoIndex.zero_inflation_levels` |
| Galí (8), p. 55 | π = (1−θ)(p*−p_{t−1}) to first order | `CalvoIndex.hasDerivAt_inflFn`, `CalvoIndex.log_infl_eq_inflFn`, `CalvoIndex.inflFn_isLittleO` |
| Galí App 3.3, p. 84 | θ^k + (1−θ)Σθ^{k−h} = 1; decomposition by date of last reset | `CalvoIndex.prob_identity`, `CalvoIndex.dist_k_step`, `CalvoIndex.dist_k_step_mass` |
| Galí p. 59, (14) | (1−α)n = y − a + d, exact | `PriceDispersion.employment_identity`, `PriceDispersion.employment_level` |
| Galí App 3.4, p. 85 | d ≥ 0; d = 0 iff all prices equal | `PriceDispersion.dispersion_nonneg`, `PriceDispersion.dispersion_eq_zero_iff`, `PriceDispersion.dispersion_eq_zero_iff_const` |
| Galí App 3.4, p. 85 | E p̂ = ((ε−1)/2)E p̂² to 2nd order | `PriceDispersion.relLogPrice_mean_second_order` |
| Galí App 3.4, p. 86 | ∫(p(i)−p)² ≃ var_i p | `PriceDispersion.relLogPrice_sq_second_order` |
| Galí App 3.4, p. 86 | d ≃ (ε/(2Θ)) var_i p(i) | `PriceDispersion.dispersion_second_order` |
| Galí p. 59 | d = 0 to first order | `PriceDispersion.dispersion_family_first_order` |
| Galí p. 63 (E_t) | ExpectationSystem axioms hold on a finite tree with genuine uncertainty | `ExpectationsFiniteTree.FiniteTree.toExpectationSystem` |
| Galí p. 63 | the tree instance is not perfect foresight | `ExpectationsFiniteTree.coinSystem_not_perfectForesight` |
| Galí (6), p. 55 | AR(1) with mean-zero innovations on the tree | `ExpectationsFiniteTree.coinAR1_isAR1` |
| Galí (31), p. 74 | l = ỹ − ηi + yⁿ | `MoneyRule.eq31_of_money_demand` |
| Galí (32), p. 74 | (32) ⇔ DIS given (31) | `MoneyRule.dis_iff_eq32` |
| Galí (33), p. 74 | l̂_{t−1} = l̂_t + π_t − Δm_t | `MoneyRule.eq33_of_levels` |
| Galí (34), p. 75 | model ⇔ A_{M,0}x_t = A_{M,1}E_t x_{t+1} + B_M s_t | `MoneyRule.model_iff_system34`, `MoneyRule.system34_iff` |
| Galí p. 75 | det(A_{M,1} − λA_{M,0}) = the cubic | `MoneyRule.det_AM1_sub_smul_AM0` |
| Galí p. 75 | eigenvalues of A_M = roots of the cubic | `MoneyRule.isRoot_charpoly_AM_iff` |
| Galí p. 75 | f(0) = σηβ > 0, f(1) = κ > 0, leading coeff −(1+ση) | `MoneyRule.charCubic_signs`, `MoneyRule.charCubic_expand` |
| Galí p. 75 | one eigenvalue > 1 | `MoneyRule.AM_has_eigenvalue_gt_one` |
| Galí p. 75 | product of eigenvalues ∈ (0,1) | `MoneyRule.det_AM_pos_lt_one` |
| Galí p. 75, fn. 14 | determinacy always holds (the book's claim, stated) | `MoneyRule.BookDeterminacyClaim` |
| Galí p. 75, fn. 14 | f = det(A_{M,1} − zA_{M,0}) has a root r > 1 and factors with a Schur-stable quadratic (the book's claim, proved for σ ≥ 0, η ≥ 0, κ > 0, 0 ≤ β ≤ 1) | `MoneyRuleRoots.bookDeterminacyClaim_holds`, `MoneyRuleRoots.bookDeterminacyClaim_gali` |
| Galí p. 75 | A_M: one eigenvalue outside the closed disc, two inside, none on the circle (with multiplicity) | `MoneyRuleRoots.AM_root_location`, `MoneyRuleRoots.AM_root_location_gali`, `MoneyRuleRoots.real_eigenvalue_unique` |
| Galí p. 75 | backward form; A_b = A_M⁻¹; BK conditions; determinate for every forcing | `MoneyRuleDeterminacy.Ab3_eq_inv_AM`, `MoneyRuleDeterminacy.Ab3_root_location`, `MoneyRuleDeterminacy.Abk_bk_conditions`, `MoneyRuleDeterminacy.Abk_determinate` |
| Galí p. 75 (η = 0) | exact reduction to two variables; determinate | `MoneyRuleDeterminacy.system34_zero_iff`, `MoneyRuleDeterminacy.B2_bk_conditions`, `MoneyRuleDeterminacy.B2_determinate` |
| Galí p. 75, "always determined" | (34) has a unique bounded adapted equilibrium for all bounded adapted shocks and any l̂₋₁ | `MoneyRuleDeterminacy.system34_existsUnique` |
| Galí §3.4.2, pp. 74–75 | unique equilibrium of the model equations, i included (η > 0) | `MoneyRuleDeterminacy.model_existsUnique` |
| Galí p. 75; Woodford App. C.1 | general Blanchard–Kahn theorem: determinate iff no unit root, counting rule and genericity; a unit root gives non-existence | `GeneralBK.determinate_iff`, `GeneralBK.nonexist_of_unit`, `GeneralBK.not_determinate_of_unit` |
| Galí (35), p. 75 | money-growth AR(1) | `MoneyRule.moneyGrowth_isAR1` |
| Galí p. 77 | interest-rate difference equation | `MoneyRule.interest_rate_equation` |
| Galí p. 77 | forward solution unique bounded | `MoneyRule.interest_rate_forward_unique`, `MoneyRule.interest_rate_forward_exists` |
| Galí p. 77 | σ = 1 ⇒ i comoves positively with Δm | `MoneyRule.interest_rate_log_utility`, `MoneyRule.interest_rate_comoves` |
| Galí p. 77 | liquidity effect possible for σ > 1 | `MoneyRule.liquidity_effect_of_sigma_gt_one` |
| Galí p. 79 | money rule = price-level rule | `MoneyRule.price_level_rule` |
| Galí (9)–(10), p. 56 | demand; objective as an infinite sum; its derivative | `ResetPrice.demand`, `ResetPrice.objective`, `ResetPrice.hasDerivAt_objective` |
| Galí (10), p. 56 | (10) necessary at an optimum | `ResetPrice.foc_of_isLocalMax` |
| Galí (10), p. 56 | (10) ⟺ optimum (convex costs); maximiser unique | `ResetPrice.isMaxOn_iff_foc` |
| Galí p. 57 | zero-inflation steady state: P = MΨ | `ResetPrice.steadyState_foc_iff` |
| Galí (11), p. 57 | (11) as the exact linearisation of (10) | `ResetPrice.hasDerivAt_focLHS_path`, `ResetPrice.eq11_iff`, `ResetPrice.eq11_real_marginal_cost` |
| Galí pp. 57–60 | recursive form of the pricing rule | `ResetPrice.resetPrice_recursive`, `ResetPrice.normForward_rec` |
| Galí App. 3.3 (37), pp. 84–85 | reset probabilities sum to 1; V = objective + Υ | `ResetPrice.reset_prob_sum`, `ResetPrice.firmValue_eq`, `ResetPrice.isMaxOn_firmValue_iff` |
| Galí (14), p. 59 | (1−α)n = y − a + d | `MarginalCost.eq14_exact`, `MarginalCost.eq14` |
| Galí p. 59, fn. 3 | ψ = w − (a − αn + log(1−α)) | `MarginalCost.log_marginal_cost` |
| Galí p. 60 | average marginal cost; n = ∫n(i) to first order | `MarginalCost.average_marginal_cost`, `MarginalCost.log_aggregate_first_order` |
| Galí p. 60 | Θ ∈ (0,1]; Θ = 1 ⟺ α = 0 | `MarginalCost.Theta_pos`, `MarginalCost.Theta_le_one`, `MarginalCost.Theta_eq_one_iff` |
| Galí p. 60 | p* formula | `MarginalCost.pstar_formula` |
| Galí (16), p. 60 | recursive form, unique bounded solution | `MarginalCost.eq16`, `MarginalCost.eq16_unique`, `MarginalCost.eq16_of_eq11` |
| Galí (17), pp. 60–61 | π = βEπ′ − λμ̂ | `NKPC.eq17` |
| Galí p. 61 | λ decreasing in θ, α, ε (ε needs α > 0) | `NKPC.lam_strictAntiOn_theta`, `NKPC.lam_strictAntiOn_alpha`, `NKPC.lam_strictAntiOn_eps` |
| Galí p. 61 | forward solution of (17) | `NKPC.nkpc_forward`, `NKPC.nkpc_forward_unique` |
| Galí fn. 4, p. 61 | π = βEπ′ + λ m̂c | `NKPC.fn4` |
| Galí (18), p. 62 | markup–output relation | `NKPC.eq18` |
| Galí (19)–(20), p. 62 | natural output | `NKPC.eq19_iff_eq20` |
| Galí p. 62 | μ = 0 gives classical output; market power lowers level | `NKPC.psi_y_perfect_competition`, `NKPC.natural_output_lower` |
| Galí (21), p. 62 | μ̂ = −(σ + (φ+α)/(1−α))ỹ | `NKPC.eq21` |
| Galí (22), p. 63 | NKPC with κ | `NKPC.eq22`, `NKPC.eq22_of_primitives`, `NKPC.kappa_pos` |
| Galí (10), p. 56 | objective differentiable with derivative = LHS of (10), primitives only | `ResetPrice.hasDerivAt_objective_of_primitives` |
| Galí (10), p. 56 | (10) necessary at an optimum (primitives only) | `ResetPrice.foc_of_isLocalMax_of_primitives` |
| Galí (10), p. 56 | convex costs: (10) ⟺ optimum, unique (primitives only) | `ResetPrice.isMaxOn_iff_foc_of_primitives` |
| Galí (9)–(10), p. 56 | domination, Lipschitz, convergence from primitives | `ResetPrice.dominated_of_primitives`, `ResetPrice.lipschitz_of_primitives`, `ResetPrice.summable_profit_of_primitives` |
| Galí (9), p. 56 | demand in compact positive range | `ResetPrice.demand_bounds`, `ResetPrice.weight_bounds` |
| Galí p. 54 | period utility U(C,N;Z) | `Household.periodUtility` |
| Galí ch. 2 (4),(7), pp. 19–21 | static FOC W/P = N^φC^σ, necessary and sufficient | `Household.static_foc_necessary`, `Household.static_foc_sufficient`, `Household.static_optimum_iff` |
| Galí (2), p. 54 | w − p = σc + φn | `Household.labour_supply_log_iff` |
| Galí p. 54; ch. 2 (5),(8) | Euler equation: necessary (perturbation), sufficient | `Household.euler_necessary`, `Household.euler_necessary_finite`, `Household.euler_sufficient`, `Household.eulerEq_ratio_form` |
| Galí p. 54; ch. 2 App. 2.1 | Euler equation ⇔ log moment = 1 | `Household.eulerEq_iff_moment` |
| Galí p. 54 | perfect foresight: i − π' − ρ = σΔc (exact) | `Household.pf_eulerEq_iff`, `Household.pf_eulerEq_iff_noshock` |
| Galí (3), p. 54 | first-order approximation as an exact derivative | `Household.hasDerivAt_log_eulerMoment_family`, `Household.linearisedEuler_eq`, `Household.linearisedEuler_eq_zero_iff` |
| Galí (3), p. 54 | exact under perfect foresight | `Household.pf_eulerEq_imp_eulerLogLinear` |
| Galí (12)–(13), p. 58 | Y = C plus (3) ⇒ (13) | `Household.eulerOutput_iff_of_clearing`, `Household.eulerOutput_of_eulerLogLinear`, `Household.pf_eulerEq_imp_eulerOutput` |
| Galí p. 59 | (1−α)n = y − a + d, exact | `Household.employment_log_identity` |
| Galí (13), p. 58 | Euler equation in output | `DIS.EulerOutput` |
| Galí p. 58 | forward iteration, exact finite T | `DIS.euler_forward_finite`, `DIS.euler_forward_ar1` |
| Galí p. 58 | forward solution with lim E_t y_{t+T} | `DIS.euler_forward_tendsto`, `DIS.euler_forward_tsum`, `DIS.euler_forward_limit_zero` |
| Galí p. 63 | r^n = real rate at natural output | `DIS.natRate_iff` |
| Galí (24), p. 63 | natural rate with AR(1) a, z | `DIS.natRate_ar1` |
| Galí (23), p. 63 | DIS in gaps ⇔ (13) | `DIS.euler_iff_disGap` |
| Galí (25), p. 63 | ỹ = −σ⁻¹ Σ E(r − r^n) | `DIS.gap_forward_tendsto`, `DIS.gap_forward_tsum` |
| Galí (26), p. 65 | rule in gap form | `TaylorRuleSystem.taylorRule_iff_gap` |
| Galí (27), p. 65 | NK + rule ⇔ x = A_T E x' + B_T u | `TaylorRuleSystem.equilibrium_iff_solves`, `tr2_AT`, `det2_AT` |
| Galí (28), p. 65 | Schur–Cohn for A_T ⇔ κ(φ_π−1)+(1−β)φ_y > 0 | `TaylorRuleSystem.schurStable_AT_iff` |
| Galí p. 65 | determinate iff (28) | `TaylorRuleSystem.determinate_iff_BM`, `equilibrium_unique`, `equilibrium_not_unique` |
| Galí (29)–(30), p. 66 | MSV, Λ_u > 0, unique bounded equilibrium | `TaylorRuleSystem.msv_structural`, `msvLambda_pos`, `msv_unique`, `equilibrium_iff_msv` |
| Galí pp. 66–67 | monetary shock | `ShockResponses.monetary_shock`, `monetary_signs`, `monNomCoef_neg_iff` |
| Galí p. 67 | money supply; liquidity effect | `ShockResponses.monetary_money_supply`, `liquidity_effect_iff`, `money_contracts_of_nominal_rises`, `liquidity_effect_of_nominal_rises` |
| Galí pp. 70–71 | discount shock ≡ monetary shock | `ShockResponses.discount_shock`, `discount_eq_monetary`, `discount_rates_fall` |
| Galí p. 71 | natural rate falls (C3-5) | `ShockResponses.discount_natRate_falls`, `discount_natRate_book_numbers` |
| Galí pp. 71–72 | technology: ỹ, π, y | `ShockResponses.technology_shock`, `technology_output`, `techOutput_eq` |
| Galí p. 72 | employment, corrected (C3-3) | `ShockResponses.technology_employment`, `techNCoef_eq`, `techNCoef_sub_printed`, `techNCoef_ne_printed` |
| Galí p. 72 | κ(φ_π−ρ_a)Λ_a ∈ (0,1) needs φ_π > ρ_a (C3-4) | `ShockResponses.techOutputCoef_mem`, `techOutputCoef_counterexample`, `techOutputCoef_unit_root` |
| Galí p. 72 | σ ≥ 1 or large φ_y ⇒ n falls | `ShockResponses.techNCoef_neg_of_one_le_sigma`, `techNCoef_neg_of_phiy_large`, `techNCoef_neg_iff` |
| Galí pp. 67–68, fn. 12 | baseline numbers | `Calibration.*` |
| Ex 3.1(a), p. 88 | hazard f/(1−F) = φ | `Ex3_1.hazard_eq` |
| Ex 3.1(a), p. 88 | instantaneous change probability = φ at every t | `Ex3_1.hazard_tendsto`, `Ex3_1.cond_change_prob` |
| Ex 3.1(b), p. 89 | mean 1/φ | `Ex3_1.mean_duration` |
| Ex 3.1(b), p. 89 | median log 2/φ (unique), ratio log 2 | `Ex3_1.median_duration`, `Ex3_1.cdf_eq_half_iff`, `Ex3_1.median_div_mean` |
| Ex 3.1(c), p. 89 | monthly λ = 1−e^{−φ}; φ = −log(1−λ) | `Ex3_1.monthly_change_prob`, `Ex3_1.lambda_eq_iff` |
| Ex 3.1(d), p. 89 | θ = e^{−3φ} = (1−λ)³ | `Ex3_1.quarterly_survival`, `Ex3_1.quarterlyCalvo_theta` |
| Ex 3.2(a), p. 89 | Y(i) = (P(i)/P)^{−ε}(C+G) | `Ex3_2.total_demand`, `Ex3_2.govt_total_demand` |
| Ex 3.2(b), p. 89 | ŷ = (1−S_G)ĉ + S_Gĝ | `Ex3_2.hasFDerivAt_log_output` |
| Ex 3.2(c), p. 89 | m̂c coefficients; purchases lower mc | `Ex3_2.hasFDerivAt_logMC`, `Ex3_2.mc_coeff_g_neg` |
| Ex 3.2(d), p. 89 | DIS with (1−S_G)/σ slope and S_G(g−Eg') | `Ex3_2.dis_iff` |
| Ex 3.3(a), p. 90 | y = c + g exactly | `Ex3_3.Goods.goods_market_exact` |
| Ex 3.3(b), p. 90 | y^n = (σg−μ)/(σ+φ) | `Ex3_3.natural_output_iff`, `Ex3_3.natOutput_multiplier_mem`, `Ex3_3.natCons_multiplier_neg` |
| Ex 3.3(c), p. 90 | gap DIS; r^n = ρ + σφ(1−ρ_g)g/(σ+φ) | `Ex3_3.euler_iff_dis_gap`, `Ex3_3.natRate_ar1`, `Ex3_3.natRate_eq_euler` |
| Ex 3.3(d), p. 91 | determinacy ⟺ φ_π > 1 | `Ex3_3.schurStable_iff`, `Ex3_3.determinate_iff` |
| Ex 3.3(d), p. 91 | MSV equilibrium, existence and uniqueness | `Ex3_3.msv_equilibrium`, `Ex3_3.equilibrium_iff_msv` |
| Ex 3.3(d), p. 91 | responses | `Ex3_3.msv_responses_pos`, `Ex3_3.output_multiplier_bounds` |
| Ex 3.4(a), p. 91 | exact Π recursion with indexation | `Ex3_4.PriceIndex.indexed_recursion`, `Ex3_4.PriceIndex.dist_law_of_motion` |
| Ex 3.4(a), p. 91 | π̂ = θωπ̂_{−1} + (1−θ)(p̂*−p̂_{−1}) | `Ex3_4.PriceIndex.hasFDerivAt_inflFn` |
| Ex 3.4(b), p. 92 | FOC; optimum ⟺ FOC | `Ex3_4.hasDerivAt_objective`, `Ex3_4.foc_iff`, `Ex3_4.isMaxOn_iff_foc` |
| Ex 3.4(c), p. 92 | log-linear reset-price rule | `Ex3_4.hasDerivAt_logResetPrice`, `Ex3_4.logResetPrice_zero`, `Ex3_4.resetPrice_isMaxOn_iff` |
| Ex 3.4(d), p. 92 | hybrid NKPC γ_b, γ_f, λ̃ and converse | `Ex3_4.hybrid_nkpc`, `Ex3_4.rule_of_hybrid_nkpc` |
| Ex 3.5(a), p. 92 | FOC of the Taylor price setter (necessary) | `Ex3_5.hasDerivAt_objective`, `Ex3_5.foc_of_isLocalMax` |
| Ex 3.5(a), p. 92 | FOC also sufficient, unique root | `Ex3_5.isMaxOn_iff_foc` |
| Ex 3.5(a), p. 92 | printed FOC (without 1/P_{t+k}) fails at the optimum | `Ex3_5.printed_foc_counterexample` |
| Ex 3.5(b), p. 93 | p* = μ + Σ ω_k E_t ψ_{t+k} | `Ex3_5.hasDerivAt_focLHS_path`, `Ex3_5.pricing_rule_iff` |
| Ex 3.5(b), p. 93 | ω_k = β^k(1−β)/(1−β^N), sum to 1 | `Ex3_5.taylorWeight_eq`, `Ex3_5.sum_taylorWeight` |
| Ex 3.5(b), p. 93 | β → 1 gives 1/N | `Ex3_5.tendsto_taylorWeight`, `Ex3_5.pricing_rule_iff_undiscounted` |
| Ex 3.5(c), p. 93 | p_t = N⁻¹ Σ p*_{t−k} | `Ex3_5.hasDerivAt_log_priceIndex` |
| Ex 3.5(d), p. 93 | two-period rule, δ = σ + φ | `Ex3_5.taylor_two_period_rule`, `Ex3_5.natural_output` |
| Ex 3.5(e), p. 93 | unique bounded solution, λ = (1−√δ)/(1+√δ); closed forms | `Ex3_5.gap_equation`, `Ex3_5.taylor_equilibrium`, `Ex3_5.taylor_gap_closed`, `Ex3_5.taylor_model_closed_form` |
| Ex 3.5(f), p. 93 | persistence decreasing in δ | `Ex3_5.taylorRoot_strictAntiOn`, `Ex3_5.gapIRF_lt`, `Ex3_5.tendsto_taylorRoot_zero`, `Ex3_5.taylorRoot_neg` |
| Ex 3.6(a), (38), p. 94 | p = (1−θ)Σθ^j p_{t−j,t} | `Ex3_6.hasDerivAt_log_priceIndex` |
| Ex 3.6(b), (39), p. 94 | plan FOC; p_{t,t+k} = μ + E_tψ_{t+k} | `Ex3_6.planObjective_update`, `Ex3_6.plan_foc_of_isLocalMax`, `Ex3_6.plan_hasDerivAt_path`, `Ex3_6.plan_rule_iff` |
| Ex 3.6(c), p. 94 | yⁿ = a − μ; m̂c = ỹ | `Ex3_6.natural_output`, `Ex3_6.mc_eq_gap` |
| Ex 3.6(d), (40), p. 95 | sticky-information Phillips curve | `Ex3_6.eq40` |
| Ex 3.6(e)–(f), p. 95 | impulse responses; comparison with NKPC | `Ex3_6.sticky_info_closed_form`, `Ex3_6.output_employment`, `Ex3_6.nkpc_comparison` |
| Ex 3.7(a), p. 96 | yⁿ = a − μ/(1+φ) | `Ex3_7.natural_output` |
| Ex 3.7, (41), p. 95 | DIS in gaps with rⁿ | `Ex3_7.gap_dis`, `Ex3_7.naturalRate_randomWalk`, `Ex3_7.naturalRate_ar1` |
| Ex 3.7(b), p. 96 | determinacy iff φ_π > 1; ỹ = π = 0 unique | `Ex3_7.determinate_iff_taylor`, `Ex3_7.randomWalk_equilibrium` |
| Ex 3.7(c), p. 96 | MSV unique; negative gap | `Ex3_7.ar1_equilibrium`, `Ex3_7.ar1_signs` |
| Ex 3.8(a), p. 96 | nⁿ, yⁿ | `Ex3_8.natural_levels`, `Ex3_8.natural_logs` |
| Ex 3.8(c), p. 96 | r = ρ | `Ex3_8.euler_real_rate`, `Ex3_8.hasDerivAt_euler_path` |
| Ex 3.8(d), p. 96 | rule replicates natural allocation (unique) | `Ex3_8.natural_allocation_replicated` |
| Ex 3.9(a), p. 97 | hybrid NKPC γ_b, γ_f, κ, φ̃ | `Ex3_9.hybrid_nkpc`, `Ex3_9.hybrid_nkpc_of_series`, `Ex3_9.hybrid_standard`, `Ex3_9.gammas_sum` |
| p. 75, §3.4.2 | Unique equilibrium of the model equations including i at η = 0 | Not formalised: at η = 0 money demand does not involve i, which is then set by the DIS; determinacy of (34) itself covers η = 0 (`MoneyRuleDeterminacy.system34_existsUnique`) |
