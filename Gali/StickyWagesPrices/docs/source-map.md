# Source map

Galí (2015), *Monetary Policy, Inflation, and the Business Cycle*, 2nd ed.,
Chapter 6, "A Model with Sticky Wages and Prices" (pp. 163–198), with Appendices 6.1–6.2 and
Exercises 6.1–6.4. Each formalised claim, equation or exercise is listed with its Lean name,
relative to the namespace `Gali.StickyWagesPrices`. Page numbers are book pages.

| Book | Claim | Lean |
| --- | --- | --- |
| Galí (2),(4), pp. 164–165 | CES labour index and wage index | `LaborAggregation.laborIndex`, `LaborAggregation.cesIndex` |
| Galí (3), p. 164 | labour demand is the unique cost minimiser | `LaborAggregation.cost_min_iff`, `LaborAggregation.wageBill_ge`, `LaborAggregation.wageBill_eq_iff` |
| Galí (3), p. 164 | continuum and finite weights | `LaborAggregation.unitInterval_cost_minimisation`, `LaborAggregation.Finite.finite_cost_minimisation` |
| Galí p. 165 | wage bill ∫W(j)N(i,j)dj = W N(i) | `LaborAggregation.wageBill_demand` |
| Galí pp. 170–171 | N = Δ_w Δ_p (Y/A)^{1/(1−α)}, exact | `LaborAggregation.aggregate_employment` |
| Galí p. 171 | (1−α)n = y − a + d_w + d_p, exact | `LaborAggregation.employment_identity` |
| Galí p. 171 | d_w, d_p ≥ 0, = 0 iff no dispersion | `LaborAggregation.dW_nonneg`, `LaborAggregation.dW_eq_zero_iff`, `LaborAggregation.dP_nonneg`, `LaborAggregation.dP_eq_zero_iff` |
| Galí p. 171 | (1−α)n = y − a to first order | `LaborAggregation.dW_family_first_order`, `LaborAggregation.dP_family_first_order`, `LaborAggregation.employment_first_order` |
| Galí p. 171, App 6.1 p. 190 | d_w ≃ ((1−α)ε_w/2) var_j w | `WageDispersion.dW_second_order` |
| Galí p. 171 | d_p ≃ (ε_p/2Θ) var_i p | `WageDispersion.dP_second_order` |
| App 6.1, p. 189 | n + n²/2 ≃ ∫n(j) + ½∫n(j)² | `WageDispersion.log_integral_exp_second_order` |
| App 6.1, p. 189 | ∫ŵ = ((ε_w−1)/2)var + O(s³); ∫ŵ² = var + O(s⁴) | `WageDispersion.relLogWage_mean_second_order`, `WageDispersion.relLogWage_sq_second_order` |
| App 6.1, p. 189 | ∫n(j)² = n² + ε_w² var_j w | `WageDispersion.integral_sq_employment`, `WageDispersion.integral_sq_employment_second_order` |
| App 6.1, p. 192 | wage Lemma 2, exact in Δm^w | `WageDispersion.wageMix_var_meanChange`, `WageDispersion.wage_lemma2_calvo`, `WageDispersion.wage_lemma2_calvo_inherited` |
| App 6.1, p. 192 | Δm^w = π^w to first order | `WageDispersion.wageInflation_sub_meanChange`, `WageDispersion.wageInflation_sq_sub_meanChange_sq` |
| Galí (10), p. 167 | union objective as a genuine sum | `WageSetting.unionObjective`, `WageSetting.E_tsum_unionObjective`, `WageSetting.unionObjective_eq` |
| Galí (11), p. 168 | FOC necessary | `WageSetting.union_hasDerivAt`, `WageSetting.union_foc_of_isLocalMax` |
| Galí (11), p. 168 | FOC sufficient, optimum unique | `WageSetting.union_isMaxOn_iff_foc` |
| Galí pp. 167–168 | regularity from primitives | `WageSetting.primitives_of_union` |
| Galí p. 168 | θ_w = 0 ⇒ W*/P = M_w MRS | `WageSetting.union_flexible`, `WageSetting.flexible_wage_index` |
| Galí p. 168 | zero-inflation steady state | `WageSetting.union_steadyState_foc_iff` |
| Galí (12), p. 168 | exact linearisation of (11) | `WageSetting.foc11_eq_focLHS`, `WageSetting.hasDerivAt_focLHS_path`, `WageSetting.eq12_iff` |
| Galí (13), p. 169 | recursive form, unique bounded solution | `WageSetting.eq13` |
| Galí p. 169 | Calvo wage cross-section and index recursion | `WageInflation.wage_dist_law_of_motion`, `WageInflation.wage_recursion`, `WageInflation.wage_index_recursion`, `WageInflation.wage_recursion_lottery` |
| Galí (14), p. 169 | exact derivative | `WageInflation.hasDerivAt_inflFn`, `WageInflation.log_wageIndex_eq`, `WageInflation.eq14_tangent` |
| Galí (15), p. 170 | (13) + (14) ⟺ (15) | `WageInflation.eq15_iff` |
| Galí p. 170 | λ_w > 0, decreasing in θ_w, ε_w, φ | `WageInflation.lambdaW_pos`, `WageInflation.lambdaW_strictAntiOn_theta`, `WageInflation.lambdaW_strictAntiOn_eps`, `WageInflation.lambdaW_strictAntiOn_phi` |
| Galí (16), p. 171 | ψ_wa = (1−αψ_ya)/(1−α) = (σ+φ)/(σ(1−α)+φ+α) > 0 | `GapForm.psiWA_eq`, `GapForm.psiWA_pos` |
| Galí (16), p. 171 | natural allocation with flexible prices and wages, unique | `GapForm.natural_allocation_iff` |
| Galí (17), p. 172 | μ̂^p = −α/(1−α)ỹ − ω̃ | `GapForm.priceMarkup_gap` |
| Galí (18), p. 172 | price NKPC in gaps, κ_p = αλ_p/(1−α) | `GapForm.priceNKPC_iff_gap`, `GapForm.priceNKPC_iff_gap_of_levels` |
| Galí (19), p. 172 | μ̂^w = ω̃ − (σ+φ/(1−α))ỹ | `GapForm.wageMarkup_gap` |
| Galí (20), p. 172 | wage NKPC in gaps | `GapForm.wageNKPC_iff_gap`, `GapForm.wageNKPC_iff_gap_of_levels` |
| Galí (21), p. 172 | ω̃_t = ω̃_{t−1} + π^w − π^p − Δωⁿ | `GapForm.wageGap_identity` |
| Galí (22), p. 173 | DIS in gaps with rⁿ | `GapForm.euler_iff_disGap_ar1`, `GapForm.natRate_ar1` |
| Galí (36), p. 184 | composite NKPC for all parameters | `GapForm.composite_nkpc`, `GapForm.composite_nkpc_explicit` |
| Galí (36), p. 184 | κ̄ = λ_pλ_wΘ_y/(λ_p+λ_w) | `GapForm.kappaBar_eq`, `GapForm.kappaBar_pos` |
| Galí fn. 6, p. 183 | κ_p = κ_w ⇒ κ = λ_pλ_w/(λ_p+λ_w)·Θ_y | `GapForm.kappa_common` |
| Galí (23)–(24), p. 173 | model ⇔ A₀x = A₁Ex' + B₀u | `System.equilibrium_iff_matrixEq`, `System.matrixEq_iff_rows` |
| Galí pp. 173–174 | zero path solves (24) ⇔ u₁ ≡ 0, Δωⁿ ≡ 0 | `System.zeroPath_exists_iff`, `System.zeroPath_iff` |
| Galí p. 174 | zero path ⇔ ω̂ⁿ ≡ 0 and v = r̂ⁿ, any φ_y | `System.zeroPath_iff_primitives`, `System.zeroPath_solves_any_phiY` |
| Galí p. 174 | det(A₀ − A₁) = −λ_pλ_wΘ_y(LHS − 1) | `System.det_A0_sub_A1_eq`, `System.det_A0_sub_A1` |
| Galí p. 174 | 1 is an eigenvalue ⇔ LHS = 1 | `System.one_eigenvalue_iff`, `System.det_neg_iff` |
| Galí p. 174 | φ_y = 0 ⇒ condition φ_p + φ_w > 1 | `System.detCondition_phiY_zero` |
| Galí p. 175, Fig. 6.1 | threshold strictly decreasing in φ_y | `System.threshold_strictAnti`, `System.detCondition_iff_threshold` |
| Galí (24), p. 173 | (24) is (22)+(23), (18), (20), (21) row by row | `Determinacy4.Dyn.eq24_iff` |
| Galí p. 174 | det(A₀ʷ − A₁ʷ) = −λ_pλ_wΘ_y(LHS − 1) | `Determinacy4.Par.det_A0_sub_A1_real`, `Determinacy4.Par.qr_one_eq_mul`, `Determinacy4.bookPar_Ψ`, `Determinacy4.bookPar_Lhs` |
| Galí p. 174 | unique bounded equilibrium ⇔ LHS > 1 (φ's ≥ 0) | `Determinacy4.determinacy_iff` |
| Galí p. 174 | 3 eigenvalues inside, 1 outside ⇔ LHS > 1 | `Determinacy4.eigenvalues_iff`, `Determinacy4.Par.eigen_count_iff` |
| Galí p. 174 | φ_y = 0 ⇒ φ_p + φ_w > 1 | `Determinacy4.determinacy_iff_phiY_zero` |
| Galí p. 174, fn. 1 | existence and uniqueness with one predetermined variable | `Determinacy4.Dyn.determinate_of_pos` |
| Galí p. 174 | condition fails ⇒ not determinate | `Determinacy4.Dyn.not_determinate_of_le`, `Determinacy4.Dyn.not_determinate_of_eq`, `Determinacy4.Dyn.not_determinate_of_no_root`, `Determinacy4.Dyn.not_determinate_of_neg` |
| Galí p. 174 (tools) | argument principle; root count constant along paths; no root on the circle | `Determinacy4.argument_principle`, `Determinacy4.inCount_path`, `Determinacy4.circle_cert` |
| Fig. 6.1, p. 175 | "Indeterminacy" region contains non-existence points (all 4 eigenvalues inside; no bounded solution with ω̃₋₁ = 1, u = 0) | `Determinacy4.exNE_lhs`, `Determinacy4.exNE_no_root`, `Determinacy4.exNE_no_bounded_solution` |
| Fig. 6.1, p. 175 | at the baseline calibration the failure is multiplicity | `Determinacy4.exBase_two_roots`, `Determinacy4.exBase_multiplicity` |
| Galí (25)–(27), p. 178 | planner optimum ⇔ symmetric, MRS = MPN | `Efficiency.Planner.planner_optimal_iff` |
| Galí (25)–(27), p. 178 | optimum N(i,j) = N* a.e.; exists, unique | `Efficiency.Planner.planner_optimal_iff_effEmployment`, `Efficiency.Planner.planner_existsUnique` |
| Galí (25)–(27), p. 178 | on the continua [0,1]×[0,1] | `Efficiency.Planner.planner_optimal_iff_unitInterval` |
| Galí (25)–(26), p. 178 | C ≤ A L^{1−α}, equality iff symmetric | `Efficiency.Planner.aggConsumption_le`, `Efficiency.Planner.aggConsumption_eq_iff` |
| Galí (27), p. 178 | MRS = MPN necessary and sufficient; unique N* | `Efficiency.symWelfare_isMax_iff_foc`, `Efficiency.mrs_sym_eq_mpn_iff`, `Efficiency.existsUnique_efficient` |
| Galí p. 178 | flexible rules give MRS = MPN/((1−τ)M_pM_w) | `Efficiency.flex_mrs_eq`, `Efficiency.flex_equilibrium` |
| Galí p. 179 | efficient iff τ = 1 − 1/(M_pM_w); unique, in (0,1) | `Efficiency.flex_equilibrium_efficient_iff`, `Efficiency.existsUnique_subsidy`, `Efficiency.optimalSubsidy_mem` |
| Galí pp. 188–191 | completing the square (exact) | `Welfare.secondOrderUtility_eq`, `Welfare.gapCoeff_eq`, `Welfare.upsilon_split` |
| Galí pp. 190–191 | distorted steady state | `Welfare.secondOrderUtility_distorted` |
| Galí (28), pp. 188–191 | period utility = quadratic + t.i.p. + O(s³) | `Welfare.period_utility_second_order`, `Welfare.period_utility_second_order_families` |
| Galí p. 192 | Lemma 2 with inherited dispersion | `Welfare.lemma2_inherited`, `Welfare.lemma2_printed_fails_with_inherited` |
| Galí (28), pp. 179, 192 | 𝕎 = ½Σβᵗ[Γỹ² + (ε_p/λ_p)(π^p)² + (ε_w(1−α)/λ_w)(π^w)²] | `Welfare.welfare_eq_loss`, `Welfare.welfare_eq_loss_inherited`, `Welfare.welfare_eq_loss_calvo` |
| Galí (29), p. 179 | L/(1−β) | `Welfare.welfare_stationary` |
| Galí p. 179 | wage weight increasing in ε_w, 1−α, θ_w | `Welfare.wageWeight_strictMonoOn_eps`, `Welfare.wageWeight_strictAnti_alpha`, `Welfare.wageWeight_strictMonoOn_theta` |
| Galí p. 180 | flexible wages: ω̃ and NKPC with κ_p = λ_pΘ_y; optimum unique | `LimitingCases.flexWage_realWageGap`, `LimitingCases.flexWage_nkpc`, `LimitingCases.flexWage_optimal`, `LimitingCases.nk_zero_unique_pf` |
| Galí p. 180 | λ_w → ∞ as θ_w → 0⁺; wage weight → 0 | `LimitingCases.lambdaW_tendsto_atTop`, `LimitingCases.wageWeight_tendsto_zero` |
| Galí p. 180 | flexible prices | `LimitingCases.flexPrice_realWageGap`, `LimitingCases.flexPrice_nkpc`, `LimitingCases.flexPrice_optimal` |
| Galí p. 180 | strict price targeting suboptimal unless wages flexible | `LimitingCases.strict_price_targeting_suboptimal`, `LimitingCases.strict_price_targeting_suboptimal_model`, `LimitingCases.flexWage_strictPrice_forces_zero_gap` |
| Galí p. 180 | strict wage targeting suboptimal unless prices flexible | `LimitingCases.strict_wage_targeting_suboptimal`, `LimitingCases.strict_wage_targeting_suboptimal_model` |
| Galí pp. 166, 170 | baseline λ_p, λ_w | `Calibration.lambdaP_baseline`, `Calibration.lambdaW_baseline` |
| Galí p. 186 | 0.85 composite weight = 47/55 | `Calibration.compositeWeight_baseline` |
| Galí (28)/(29) | loss weights 8, ≈419.4, ≈924.0 | `Calibration.gapCoeff_baseline`, `Calibration.priceWeight_baseline`, `Calibration.wageWeight_baseline` |
| Table 6.1 | losses recomputed from printed s.d.s | `Calibration.table61_losses`, `Calibration.table61_ranking`, `Calibration.table61_flexible_swap` |
| Galí (30)–(33), p. 181 | Lagrangian sufficiency, deterministic | `OptimalPolicy.Det.isOptimal_of_foc`, `OptimalPolicy.Det.loss_sub_hasSum` |
| Galí (30)–(33), p. 181 | uniqueness; FOCs necessary when a FOC solution exists | `OptimalPolicy.Det.eq_of_loss_eq`, `OptimalPolicy.Det.isOptimal_iff_foc`, `OptimalPolicy.Det.existsUnique_optimal` |
| Galí (30)–(33), p. 181 | optimality under uncertainty (PullOut) | `OptimalPolicy.Stoch.commitment_optimal` |
| Galí p. 181, App. 6.2, p. 192 | matrix form A₀*x = A₁*Ex' + B₀*Δa | `OptimalPolicy.Stoch.matrix_form_iff` |
| Galí §6.4.1, p. 181 | demand shocks only ⇒ zero path optimal and unique | `OptimalPolicy.Det.demand_zero_optimal`, `OptimalPolicy.Stoch.demand_zero_optimal` |
| Galí p. 182 | i = rⁿ + φ_pπ^p implements the optimum | `OptimalPolicy.Stoch.rule_implements` |
| Galí p. 182 (κ_p = κ_w) | the rule is determinate iff φ_p > 1 | `OptimalPolicy.Stoch.ruleDeterminate_iff` |
| Galí fn. 6, p. 183 | κ = λ_pλ_w/(λ_p+λ_w)·Θ_y | `OptimalPolicy.book_fn6` |
| Galí (34)–(35), pp. 183–184 | π̄_t = −(1/ε)Δỹ_t; π̄_0 = −(1/ε)ỹ_0 | `OptimalPolicy.Stoch.composite_foc`, `OptimalPolicy.Det.composite_foc` |
| Galí (36), p. 184 | composite NKPC | `OptimalPolicy.Stoch.composite_nkpc`, `OptimalPolicy.book_composite_slope` |
| Galí p. 184 | π̄ = ỹ = 0 optimal (pathwise and under E₀), unique | `OptimalPolicy.Stoch.composite_targeting_optimal`, `OptimalPolicy.Stoch.composite_targeting_solves`, `OptimalPolicy.Det.composite_targeting_existsUnique` |
| Galí p. 184 | the book's check is only the necessary conditions | `OptimalPolicy.composite_path_satisfies_34_35` |
| Galí p. 184 | composite weights increase with own stickiness | `OptimalPolicy.wage_weight_strictMonoOn`, `OptimalPolicy.price_weight_strictMonoOn` |
| Galí pp. 184–185 | strict composite targeting ⇔ ỹ ≡ 0 | `OptimalPolicy.Stoch.composite_zero_iff` |
| Galí p. 182 (p. 174 with φ_w = φ_y = 0) | the rule with φ_p > 1 is determinate | `OptimalPolicy.Stoch.ruleDeterminate_of_phiP`, `OptimalPolicy.Stoch.ruleDeterminate_book` |
| Galí p. 182 | the rule implements the optimal (zero) allocation, uniquely | `OptimalPolicy.Stoch.rule_implements_book` |
| Galí p. 173 | the rule system is (24) with zero forcing | `OptimalPolicy.Stoch.rule_isSol` |
| Ex 6.1(a), p. 194 | firm FOC w − p = a | `Ex6_1.firm_optimal_iff`, `Ex6_1.labor_demand_log` |
| Ex 6.1(a), p. 194 | n = a/φ, y = (1+φ)a/φ | `Ex6_1.flexEq_iff` |
| Ex 6.1(b), p. 195 | π = Eπ' + φň + u (exact, iff) | `Ex6_1.inflation_eq_iff` |
| Ex 6.1(c), p. 195 | optimal policy: unique and exists | `Ex6_1.optimal_unique`, `Ex6_1.optimal_exists` |
| Ex 6.2(a), p. 195 | flexible equilibrium closed forms | `Ex6_2.flex_iff` |
| Ex 6.2(a), p. 196 | nominal indeterminacy | `Ex6_2.flex_any_price`, `Ex6_2.flex_two_equilibria` |
| Ex 6.2(b), p. 196 | wage rule (set-up only) | `Ex6_2.WageInAdvance` |
| Ex 6.2(c), p. 196 | E_{t−1}n_t = ρa a_{t−1}/φ, p − E_{t−1}p = −ε^a, w − p = a | `Ex6_2.wage_facts` |
| Ex 6.2(c), p. 196 | equilibrium under i = ρ + φ_ππ | `Ex6_2.taylor_unique`, `Ex6_2.taylor_exists` |
| Ex 6.2(d), p. 196 | optimal policy and implementing rule | `Ex6_2.optimal_real_rate`, `Ex6_2.optimal_unique`, `Ex6_2.optimal_exists` |
| Ex 6.3, p. 196 | firm FOC and exact logs | `Ex6_3.labor_demand_iff`, `Ex6_3.profit_le`, `Ex6_3.labor_demand_log`, `Ex6_3.production_log`, `Ex6_3.goods_log` |
| Ex 6.3(a), p. 196 | n = 0, y = 0, p = m, ω = log(1−α) | `Ex6_3.flexible_iff` |
| Ex 6.3(b), p. 196 | n = ε, y = (1−α)ε | `Ex6_3.advance_iff`, `Ex6_3.advance_solution`, `Ex6_3.advance_exists` |
| Ex 6.3(c), p. 197 | n_t = n_{t−1} + ε_t (hysteresis) | `Ex6_3.union_iff`, `Ex6_3.union_solution`, `Ex6_3.union_hysteresis`, `Ex6_3.union_exists` |
| Ex 6.4(a), p. 197 | yᵉ = 2a | `Ex6_4.efficient_hours_iff`, `Ex6_4.efficient_output_log` |
| Ex 6.4(b), p. 197 | w − p = n/(1+δ) vs n; real rigidity | `Ex6_4.competitive_supply_log`, `Ex6_4.real_wage_schedule`, `Ex6_4.real_rigidity` |
| Ex 6.4(c), p. 197 | yⁿ = (2+δ)a − (1+δ)μ | `Ex6_4.natural_iff`, `Ex6_4.markup_eq` |
| Ex 6.4(d), p. 197 | μ̂ = −ỹ/(1+δ) | `Ex6_4.markup_gap` |
| Ex 6.4(e), p. 197 | gap NKPC, cost push | `Ex6_4.nkpc_iff`, `Ex6_4.cost_push` |
| Ex 6.4(e), p. 198 | tradeoff iff δ > 0 | `Ex6_4.divine_iff`, `Ex6_4.divine_iff_mu0`, `Ex6_4.tradeoff_iff_delta`, `Ex6_4.strict_inflation_gap` |
| Ex 6.4(f), p. 198 | discretion with i.i.d. a | `Ex6_4.discretionEq_iff`, `Ex6_4.discretion_iid_iff`, `Ex6_4.discretion_output`, `Ex6_4.perfect_competition` |
| Figs. 6.2–6.3, Table 6.1 (simulations) | Impulse responses and simulated moments | Computational; Table 6.1 losses recomputed in `Calibration.table61_losses` |
