# Source map

Galí (2015), *Monetary Policy, Inflation, and the Business Cycle*, 2nd ed.,
Chapter 4, "Monetary Policy Design in the Basic New Keynesian Model" (pp. 98–125), with
Appendix 4.1 and Exercises 4.1–4.6. Each formalised claim, equation or exercise is listed with
its Lean name, relative to the namespace `Gali.MonetaryPolicyDesign`. Page numbers are book pages.

| Book | Claim | Lean |
| --- | --- | --- |
| Galí (1), (2), p. 99 | the optimum is symmetric, necessary and sufficient with (3) | `Efficient.Goods.planner_optimal_iff` |
| Galí (1)–(3), p. 99 | optimal iff N(i)=N* a.e.; existence and uniqueness | `Efficient.Goods.planner_optimal_iff_effEmployment`, `Efficient.Goods.planner_existsUnique` |
| Galí p. 99, continuum [0,1] | Lebesgue version | `Efficient.Goods.planner_optimal_iff_unitInterval` |
| Galí p. 99, finite goods | weighted version, every good | `Efficient.Finite.planner_optimal_iff_finite` |
| Galí p. 99 | C ≤ A N^{1−α}, equality iff symmetric | `Efficient.Goods.aggConsumption_le`, `Efficient.Goods.aggConsumption_eq_iff` |
| Galí (3), p. 99 | MRS and MPN as derivatives | `Efficient.marginal_utilities`, `Efficient.hasDerivAt_output` |
| Galí (3), p. 99 | MRS=MPN necessary and sufficient | `Efficient.symWelfare_isMax_iff_foc` |
| Galí (3), p. 99 | unique efficient employment N* | `Efficient.mrs_sym_eq_mpn_iff`, `Efficient.existsUnique_efficient` |
| Galí p. 102 | non-symmetric allocations strictly worse | `Efficient.Goods.welfare_lt_of_not_symmetric` |
| Galí p. 100 | firm optimum P(i)=M(1−τ)W/MPN(i), unique, identical across firms | `Distortions.firm_optimal_iff`, `Distortions.firm_existsUnique`, `Distortions.optimal_identical`, `Distortions.flex_price_rule` |
| Galí p. 100 | MRS = MPN/M < MPN | `Distortions.flex_mrs`, `Distortions.flex_mrs_lt_mpn` |
| Galí p. 100 | employment strictly below efficient | `Distortions.markup_inefficiently_low`, `Distortions.existsUnique_flex`, `Distortions.lt_of_wedge` |
| Galí p. 100 | strict welfare loss from the markup | `Distortions.flex_welfare_lt` |
| Galí p. 101 | τ=1/ε restores efficiency; unique | `Distortions.wedge_eq_one_iff_subsidy`, `Distortions.flex_efficient_iff_subsidy`, `Distortions.flex_equilibrium` |
| Galí p. 101 | average markup | `Distortions.avgMarkup_subsidy`, `Distortions.mrs_eq_avgMarkup`, `Distortions.foc_iff_avgMarkup`, `Distortions.employment_avgMarkup` |
| Galí pp. 101–102 | price dispersion violates (1),(2); strict loss | `Distortions.Dispersion.dispersion_violates_symmetry`, `Distortions.Dispersion.dispersion_welfare_loss`, `Distortions.Dispersion.prices_equal_of_optimal` |
| Galí (4),(5), p. 103 | (ỹ,π)≡0 equilibrium iff i=rⁿ | `OptimalPolicy.zero_equilibrium_iff` |
| Galí p. 103 | divine coincidence (bounded equilibria) | `OptimalPolicy.divine_coincidence`, `OptimalPolicy.optimal_policy_characterisation` |
| Galí p. 103 | optimal policy attains zero loss; unique minimiser | `OptimalPolicy.optimal_policy` |
| Galí p. 102 | ỹ=0 ⟺ efficient output (with subsidy) | `OptimalPolicy.gap_zero_iff_efficient` |
| Galí p. 102 | price stability ⇒ no relative-price distortions | `OptimalPolicy.no_dispersion_of_price_stability` |
| Galí (6)–(7), p. 104 | DIS and NKPC | `RuleExogenous.DIS`, `RuleExogenous.NKPC` |
| Galí (8)–(10), pp. 104–105 | under i = rⁿ, equilibrium ⟺ x_t = A_O E_t x_{t+1} | `RuleExogenous.equilibrium_iff_solves` |
| Galí p. 105 | ỹ = π = 0 solves (9) | `RuleExogenous.zero_equilibrium` |
| Galí p. 105 | A_O: real eigenvalues, one in (0,1), one > 1 | `RuleExogenous.eigenvalues_AO` |
| Galí p. 105 | indeterminacy | `RuleExogenous.not_determinate_AO`, `RuleExogenous.exists_second_equilibrium`, `RuleExogenous.equilibrium_not_unique` |
| Galí (11)–(13), p. 105 | system under the Taylor rule | `RuleTaylorPrinciple.equilibrium_iff_solves` |
| Galí (14), p. 106 | determinacy ⟺ κ(φπ−1)+(1−β)φy > 0 | `RuleTaylorPrinciple.determinate_iff_14`, `RuleTaylorPrinciple.schurStable_AT_iff` |
| Galí p. 106 | under (14), ỹ = π = 0, i = rⁿ is the unique equilibrium | `RuleTaylorPrinciple.equilibrium_iff_zero` |
| Galí p. 106 | indeterminacy without (14) | `RuleTaylorPrinciple.exists_nonzero_equilibrium` |
| Galí (15), p. 106 | long-run di/dπ = φπ + φy(1−β)/κ | `RuleTaylorPrinciple.tendsto_rate_of_tendsto_infl` |
| Galí p. 107 | (14) ⟺ (15) > 1 | `RuleTaylorPrinciple.taylorPrinciple_iff` |
| Galí p. 107 | the real rate eventually rises | `RuleTaylorPrinciple.realRate_eventually_pos` |
| Galí (16), p. 108 | system under the forward rule (corrected A_F) | `RuleForward.equilibrium_iff_solves`, `RuleForward.AF_one_one` |
| Galí (17)–(18), p. 108 | determinacy ⟺ (17) ∧ (18) | `RuleForward.determinate_iff_17_18` |
| Galí pp. 108–109 | unique equilibrium under (17)–(18) | `RuleForward.equilibrium_iff_zero` |
| Galí fn. 7, p. 108 | φy < σ(1+β⁻¹) implied | `RuleForward.fn7_implied`, `RuleForward.abs_det2_AF_lt_one_iff` |
| Galí p. 110 | φy = 0, contemporaneous: ⟺ φπ > 1 | `RuleForward.determinate_contemporaneous_phiy_zero` |
| Galí p. 110 | φy = 0, forward: ⟺ 1 < φπ < 1 + 2σ(1+β)/κ | `RuleForward.determinate_forward_phiy_zero` |
| Galí App 4.1, p. 117 | 2nd-order Taylor of U in log deviations | `Welfare.logdev_taylor`, `Welfare.taylor_two` |
| Galí App 4.1, p. 118 | Lemma 1, d = (ε/2Θ)var | `Welfare.dispersion_second_order` |
| Galí App 4.1, p. 119 | log P = E p + ((1−ε)/2)var + O(s³) | `Welfare.logPriceIndex_second_order` |
| Galí App 4.1, pp. 118–119 | completing the square (exact) | `Welfare.secondOrderUtility_eq` |
| Galí App 4.1, pp. 118–119 | Uₜ − U = −½U_cC[Γ(y−ŷⁿ)² + (ε/Θ)var] + tip + O(s³) | `Welfare.period_utility_second_order`, `Welfare.period_utility_second_order_dispersion`, `Welfare.period_utility_normalised` |
| Galí p. 118 | efficiency −Uₙ/U_c = MPN | `Welfare.efficiency_iff` |
| Galí p. 119 | ŷⁿ coefficient identity | `Welfare.gapCoeff_mul_psiYA` |
| Galí p. 119 | exact dispersion recursion | `Welfare.calvoMix_var_meanChange`, `Welfare.calvo_var_recursion` |
| Lemma 2, p. 119 | Σβᵗvar = θ/((1−βθ)(1−θ))Σβᵗ(Δm)² (exact) | `Welfare.lemma2`, `Welfare.lemma2_calvo` |
| Galí p. 116 | inherited dispersion | `Welfare.lemma2_hasSum`, `Welfare.lemma2_calvo_inherited` |
| Galí p. 119 | Δm = π to first order | `Welfare.inflation_sub_meanChange`, `Welfare.inflation_sq_sub_meanChange_sq` |
| Galí pp. 111, 119 | W | `Welfare.welfareLoss`, `Welfare.welfare_eq_loss`, `Welfare.welfare_eq_loss_calvo` |
| Galí p. 111 | L | `Welfare.avgLoss`, `Welfare.welfare_stationary` |
| Galí p. 111 | gap coefficient ↑ in σ, φ, α | `Welfare.gapCoeff_strictMono_sigma`, `Welfare.gapCoeff_strictMono_phi`, `Welfare.gapCoeff_strictMonoOn_alpha` |
| Galí p. 111 | ε/λ ↑ in ε, θ | `Welfare.inflWeight_strictMonoOn_eps`, `Welfare.inflWeight_strictMonoOn_theta` |
| Galí p. 111 | relative weight κ/ε in α | `Welfare.relWeight_strictAntiOn_alpha`, `Welfare.relWeight_strictMonoOn_alpha`, `Welfare.relWeight_not_increasing_alpha`, `Welfare.relWeight_baseline` |
| Galí (19)–(20), p. 112 | v = φ_yŷⁿ | `SimpleRules.rule19_iff_rule20` |
| Galí p. 112 | system A_T, B_T; determinacy (14) | `SimpleRules.equilibrium_iff_solves`, `SimpleRules.determinate_iff` |
| Galí p. 112 | rⁿ − v | `SimpleRules.drivingForce_eq` |
| Galí pp. 112–113 | MSV, unique bounded equilibrium | `SimpleRules.equilibrium_iff_msv`, `SimpleRules.equilibrium_iff_msv_single` |
| Galí p. 113 | L as quadratic form × var | `SimpleRules.msvLoss_eq`, `SimpleRules.equilibrium_loss`, `SimpleRules.variance_isSecondMoment`, `SimpleRules.ar1Var_hasSum` |
| Galí fn. 10, p. 114 | variances → 0 as φπ → ∞ | `SimpleRules.msvLoss_tendsto_zero` |
| Galí §4.4.2, p. 115 | constant money = (34) | `SimpleRules.constantMoney_iff_system34` |
| Galí Table 4.1, p. 113 | 32 entries | `SimpleRules.table41_tech_1`, `SimpleRules.table41_tech_2`, `SimpleRules.table41_tech_3`, `SimpleRules.table41_tech_4`, `SimpleRules.table41_demand_1`, `SimpleRules.table41_demand_2`, `SimpleRules.table41_demand_3`, `SimpleRules.table41_demand_4` |
| Ex 4.1(a), p. 121; (10) p. 105 | A_O has real eigenvalues 0 < λ₁ < 1 < λ₂ | `Ex4_1.AO_eigenvalues` |
| Ex 4.1(a); (8)–(10) | i = rⁿ ⇔ x = A_O E x′; indeterminate | `Ex4_1.equilibrium_AO_iff`, `Ex4_1.AO_not_unique` |
| Ex 4.1(b), p. 121 | A_T eigenvalues inside ⇔ (14) | `Ex4_1.AT_eigenvalues_inside_iff`, `Ex4_1.eigenvalues_inside_iff` |
| Ex 4.1(b), p. 121 | printed "outside" is false | `Ex4_1.printed_ex4_1b_false`, `Ex4_1.AT_not_both_outside`, `Ex4_1.printed_iff_iff_not14` |
| Ex 4.1(b); p. 106 | rule (11) unique iff (14) | `Ex4_1.rule11_unique`, `Ex4_1.rule11_not_unique` |
| Ex 4.2(a), p. 121 | MSV solution, existence and uniqueness | `Ex4_2.ex4_2a_equilibrium_iff`, `Ex4_2.ex4_2a_exists`, `Ex4_2.ex4_2a_rate` |
| Ex 4.2(a) | multiplicity for φ_π ≤ 1 | `Ex4_2.ex4_2a_not_unique` |
| Ex 4.2(b) | limits as φ_π → ∞ | `Ex4_2.ex4_2b_limits`, `Ex4_2.ex4_2b_coefficients` |
| Ex 4.2(c) | var π via MSV and stationary variance | `Ex4_2.ex4_2c_variance`, `Ex4_2.stationary_var_ar1` |
| Ex 4.2(c) | argmin of var π | `Ex4_2.ex4_2c_interior`, `Ex4_2.ex4_2c_corner`, `Ex4_2.ex4_2c_no_noise`, `Ex4_2.ex4_2c_iid` |
| Ex 4.3(a), p. 122 | MSV responses, existence and uniqueness | `Ex4_3.ex4_3a_equilibrium_iff`, `Ex4_3.ex4_3a_exists` |
| Ex 4.3(b) | dependence on φ_π, κ; limits | `Ex4_3.ex4_3b_mono_phi`, `Ex4_3.ex4_3b_mono_kappa`, `Ex4_3.ex4_3b_phi_infty`, `Ex4_3.ex4_3b_kappa_infty`, `Ex4_3.ex4_3b_kappa_zero` |
| Ex 4.3(c) | sign of the employment response | `Ex4_3.ex4_3c_sign`, `Ex4_3.ex4_3c_both_signs`, `Ex4_3.ex4_3c_covariance` |
| Ex 4.4(a), p. 122 | ỹ = π = 0 minimises ϑ var ỹ + var π; equilibrium iff i = rⁿ | `Ex4_4.zero_minimises_loss`, `Ex4_4.zero_equilibrium_iff` |
| Ex 4.4(a), p. 122 | the rule implements ỹ = π = 0 uniquely iff (14) | `Ex4_4.rule_implements`, `Ex4_4.implements_uniquely_iff`, `Ex4_4.schurStable_AT_iff` |
| Ex 4.4(b), p. 122 | money under the optimal policy; constant money suboptimal | `Ex4_4.money_path_optimal`, `Ex4_4.constant_money_not_optimal`, `Ex4_4.constant_money_optimal_of_const` |
| Ex 4.4(c), p. 123 | money rule implements the optimum (existence); equals a price-level interest rule | `Ex4_4.moneyRule_equilibrium`, `Ex4_4.moneyRule_iff_interestRule` |
| Ex 4.4(c), p. 123 | uniqueness under the money rule (the claim, stated) | `Ex4_4.MoneyRuleUniqueness` |
| Ex 4.4(c), p. 123 | the money rule reduces to (34) with zero shocks | `Ex4_4Determinacy.system34_of_moneyRule` |
| Ex 4.4(c), p. 123 | the optimum is the unique bounded equilibrium under the money rule | `Ex4_4Determinacy.moneyRuleUniqueness_holds`, `Ex4_4Determinacy.moneyRule_implements_uniquely` |
| Ch. 3 (34), p. 75 (used in Ex 4.4(c)) | the money-rule system (34) and its characteristic cubic | `MoneyRuleSystem.System34`, `MoneyRuleSystem.charCubic`, `MoneyRuleSystem.isRoot_charpoly_AM_iff` |
| Ch. 3 p. 75, fn. 14 | f has a root r > 1 and factors with a Schur-stable quadratic (the book's claim) | `MoneyRuleRoots.bookDeterminacyClaim_holds`, `MoneyRuleRoots.bookDeterminacyClaim_gali` |
| Ch. 3 p. 75 | A_M: one eigenvalue outside the closed disc, two inside, none on the circle | `MoneyRuleRoots.AM_root_location`, `MoneyRuleRoots.AM_root_location_gali` |
| Ch. 3 p. 75 | backward form; BK conditions; determinate for every forcing (η > 0; exact reduction at η = 0) | `MoneyRuleDeterminacy.Abk_bk_conditions`, `MoneyRuleDeterminacy.Abk_determinate`, `MoneyRuleDeterminacy.system34_zero_iff`, `MoneyRuleDeterminacy.B2_determinate` |
| Ch. 3 p. 75, "always determined" | (34) has a unique bounded adapted equilibrium for all bounded adapted shocks and any l̂₋₁ | `MoneyRuleDeterminacy.system34_existsUnique` |
| Woodford App. C.1 | general Blanchard–Kahn theorem | `GeneralBK.determinate_iff`, `GeneralBK.nonexist_of_unit`, `GeneralBK.not_determinate_of_unit` |
| Ex 4.5(a), p. 124 | household FOCs | `Ex4_5.labour_optimum_iff`, `Ex4_5.money_optimum_iff`, `Ex4_5.eulerRHS` |
| Ex 4.5(b), p. 124 | P(i) = 𝓜W/A | `Ex4_5.price_optimum_iff` |
| Ex 4.5(c), p. 124 | N constant; Y; V; inflation; existence | `Ex4_5.flex_employment`, `Ex4_5.flex_output`, `Ex4_5.flex_velocity`, `Ex4_5.flex_inflation`, `Ex4_5.flex_candidate` |
| Ex 4.5(d), p. 124 | utility vs γ_m, σ_m²; Friedman rule | `Ex4_5.hasSum_flex_welfare`, `Ex4_5.welfare_strictAnti_gamma`, `Ex4_5.welfare_strictMono_var`, `Ex4_5.not_optimal_of_equilibrium`, `Ex4_5.friedman_iff` |
| Ex 4.5(e), p. 124 | preset-price FOC with E_{t−1}; exact N, Y, M/P | `Ex4_5.sticky_price_optimal`, `Ex4_5.sticky_price_unique`, `Ex4_5.pricing_iff`, `Ex4_5.sticky_employment`, `Ex4_5.sticky_output_balances`, `Ex4_5.sticky_candidate` |
| Ex 4.5(f), p. 124 | expected utility with lognormal shocks | `Ex4_5.hasSum_sticky_welfare`, `Ex4_5.integral_tsum_sticky_welfare` |
| Ex 4.5(g), pp. 124–125 | φ_a = 1, φ_v = 0 replicates flexible prices; Friedman level | `Ex4_5.stabilization_improves`, `Ex4_5.stabilization_optimal`, `Ex4_5.tendsto_policyWelfare_friedman`, `Ex4_5.policy_not_optimal`, `Ex4_5.sticky_replicates_flex`, `Ex4_5.sticky_employment_replicates`, `Ex4_5.policyWelfare_replicates` |
| Ex 4.5 | concrete Gaussian probability space | `Ex4_5.concreteShocks`, `Ex4_5.exists_flex_equilibrium`, `Ex4_5.exists_sticky_equilibrium` |
| Ex 4.6, p. 125 | determinacy iff φ_p > 0 ∨ φ_p < φ* (corrected) | `Ex4_6.determinate_of_pos`, `Ex4_6.not_determinate_of_le`, `Ex4_6.determinate_iff`, `Ex4_6.determinate_iff_pos_of_ge`, `Ex4_6.book_claim_false` |
| Table 4.2, p. 119 | Money-growth rule statistics | Computational (requires numerically solving the `3 × 3` money-rule system, whose determinacy is proved in `MoneyRuleDeterminacy.system34_existsUnique`); not formalised |
