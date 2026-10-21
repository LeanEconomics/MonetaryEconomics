# Source map

Galí (2015), *Monetary Policy, Inflation, and the Business Cycle*, 2nd ed.,
Chapter 7, "Unemployment in the New Keynesian Model" (pp. 199–222), with Exercises 7.1–7.3.
Each formalised claim, equation or exercise is listed with its Lean name, relative to the
namespace `Gali.Unemployment`. Page numbers are book pages.

| Book | Claim | Lean |
| --- | --- | --- |
| Galí p. 202 | ∫₀^N χ s^φ ds = χN^{1+φ}/(1+φ) | `IndivisibleLabor.integral_disutility` |
| Galí p. 202 | household utility = Ch6 utility | `IndivisibleLabor.householdUtility_eq_ch6` |
| Galí p. 204 | participate iff W/P ≥ χC^σ s^φ | `IndivisibleLabor.marginal_value`, `IndivisibleLabor.participates_iff` |
| Galí (5), p. 204 | marginal participant L(j) | `IndivisibleLabor.eq5_iff`, `IndivisibleLabor.marginal_indifferent` |
| Galí p. 204 | participating set = [0, L(j)] (∩ [0,1]) | `IndivisibleLabor.participation_set_eq`, `IndivisibleLabor.participation_set_unit` |
| Galí (6), p. 204 | exact by type and integrated | `UnemploymentDef.eq6_type`, `UnemploymentDef.eq6_integrated`, `UnemploymentDef.eq6_residual_eq` |
| Galí (6), p. 204 | approximation is first order | `UnemploymentDef.eq6_first_order`, `UnemploymentDef.wageIndex_first_order`, `UnemploymentDef.laborForce_first_order` |
| Galí (7), fn. 6, p. 205 | 1 − N/L = 1 − e^{−u}; error ≤ u²/2 for u ≥ 0 | `UnemploymentDef.unemploymentRate_eq`, `UnemploymentDef.abs_rate_sub_u_le`, `UnemploymentDef.abs_rate_sub_u_bound_fails_neg` |
| Galí (8), p. 205 | μ^w = φu | `UnemploymentDef.eq8_iff` |
| Galí (10), p. 206 | uⁿ = μ^w/φ > 0 | `UnemploymentDef.natRate_eq`, `UnemploymentDef.natRate_pos` |
| Galí (11), p. 207 | NK wage Phillips curve | `UnemploymentDef.wageNKPC_iff_eq11` |
| Galí p. 206 | flexible wages ⇒ u ≡ uⁿ; fluctuations need rigidity | `UnemploymentDef.flexible_unemployment_constant`, `UnemploymentDef.fluctuations_require_rigidity`, `UnemploymentDef.sticky_unemployment_gap_consistent` |
| Galí (16), p. 208 | φû = μ̂^w = ω̃ − (σ + φ/(1−α))ỹ | `Equilibrium.eq16_levels` |
| Galí fn. 8, p. 208 | (14) + (16) ⇔ Ch6 (20) | `Equilibrium.eq14_iff_eq20` |
| Galí §7.2, pp. 207–208 | Ch7 system = Ch6 system + (16) | `Equilibrium.ch7_iff_ch6`, `Equilibrium.isSol7_iff` |
| Galí §7.2 / p. 174 | determinacy transfers | `Equilibrium.determinate_iff_ch6` |
| Galí §7.2 / p. 174 | Ch7 determinacy ⇔ the p. 174 inequality | `Equilibrium.determinacy_ch7_iff`, `Equilibrium.determinacy_ch7_iff_phiY_zero` |
| Galí (17), p. 210 | Taylor rule (17) determinate | `Equilibrium.rule17_determinate` |
| Galí p. 174 (restated) | 4×4 determinacy theorem, copied from Ch6 | `Determinacy4.determinacy_iff`, `Determinacy4.eigenvalues_iff` |
| Galí (10), pp. 206, 209 | M_w = exp(φuⁿ) | `Policy.markup_eq_exp` |
| Galí p. 209 | ε_w = M_w/(M_w−1) | `Policy.epsW_markup_iff` |
| Galí p. 209 | ε_w ≈ 4.5; markup ≈ 28% | `Policy.calibration_epsW`, `Policy.calibration_markup`, `Policy.calibration_book_epsW` |
| Galí (6), p. 204 | labour supply solved for l | `Policy.laborForce_iff` |
| Galí p. 210, Fig. 7.2 | wealth effect ∂l/∂c = −σ/φ < 0 | `Policy.hasDerivAt_laborForce`, `Policy.laborForce_strictAnti` |
| Galí (5), p. 204 | marginal participant; elasticity −σ/φ | `Policy.marginalParticipant_eq5`, `Policy.hasDerivAt_log_marginalParticipant` |
| Galí fn. 12, p. 211 | θ_w → 0 ⇒ unemployment fluctuations vanish (uniformly bounded π^w) | `Policy.unemployment_vanishes`, `Policy.unemployment_volatility_vanishes`, `Policy.tendsto_lamWOf_atTop`, `Policy.abs_unemp_le` |
| Galí fn. 12, p. 211 | the bound cannot be dropped | `Policy.unemployment_need_not_vanish` |
| Galí p. 206, (16) | flexible wages ⇒ û ≡ 0 | `Policy.flexible_wages_no_unemployment_gap` |
| Galí fn. 8, p. 208 | (14)+(16) ⇒ Ch6 (20) | `Policy.fn8_wage_pc` |
| Galí §7.2 | Ch7 constraints = Ch6 constraints + (16) | `Policy.feasible7_iff` |
| Galí p. 212 | Ch7 optimal policy = Ch6 problem with û from (16) | `Policy.isOptimal7_iff`, `Policy.isOptimal7_iff_eq`, `Policy.existsUnique_optimal7`, `Policy.isOptimal7_iff_foc` |
| Galí (18)–(21), p. 212 | identical to Ch6 (30)–(33) | `Policy.foc7_iff_ch6` |
| Galí pp. 208, 213 | ψ_ya = ψ_wa = 1 at σ = 1 | `Policy.psiYA_sigma_one`, `Policy.psiWA_sigma_one` |
| Galí p. 213 | efficient response: n = l = 0, y = a | `Policy.efficient_technology_sigma_one`, `Policy.efficient_employment_zero_iff` |
| Galí (6),(7),(9),(16) | participation consistency | `Policy.participation_consistent` |
| Galí p. 214 | demand shocks: labour market insulated | `Policy.demand_shock_optimal_iff`, `Policy.demand_shock_labour_market` |
| Galí (22), p. 214 | level vs gap intercept | `Policy.rule22_level_iff_gap`, `Policy.rule22_level_not_steady`, `Policy.rule22_deviation` |
| Ex 7.1(a), p. 220 | flexible price = M_p × marginal cost | `Ex7_1.profit_isMaxOn_iff` |
| Ex 7.1(a), p. 220 | subsidy ⇒ P = W; π^p = π^w | `Ex7_1.flexPrice_eq_wage`, `Ex7_1.infl_eq_of_realWage_const` |
| Ex 7.1(a), p. 220 | π^p = βEπ^p' − φλ_w(u − uⁿ) | `Ex7_1.ex7_1a_from_primitives` |
| Ex 7.1(b), p. 220 | φu = −(σ+φ)(y − yᵉ) | `Ex7_1.phi_u_eq_gap` |
| Ex 7.1(b), p. 220 | flexible prices remove the price-inflation term | `Ex7_1.ch6PeriodLoss_tendsto_flex` |
| Ex 7.1(b), p. 220 | loss ∝ α_u u² + π² | `Ex7_1.flexLoss_eq`, `Ex7_1.expected_welfare_eq` |
| Ex 7.1(b), p. 220 | printed β^k sum diverges; β^t converges | `Ex7_1.printed_sum_not_summable`, `Ex7_1.correct_sum_hasSum` |
| Ex 7.1(b), p. 220 | the steady-state distortion is not small | `Ex7_1.distortion_eq`, `Ex7_1.distortion_calibration` |
| Ex 7.1(c), p. 220 | discretionary equilibrium exists, unique | `Ex7_1.discretionEq_iff_const` |
| Ex 7.1(c), p. 220 | average inflation positive (inflation bias) | `Ex7_1.expected_inflation_eq`, `Ex7_1.piStar_primitives`, `Ex7_1.inflationBias_pos` |
| Ex 7.1(c), p. 220 | ways to eliminate the bias | `Ex7_1.inflationBias_zero_iff`, `Ex7_1.wageSubsidy_markup_zero`, `Ex7_1.inflationBias_strictMonoOn` |
| Ex 7.1(d), p. 220 | implementing rule | `Ex7_1.rule_implements`, `Ex7_1.rule_indeterminate` |
| Ex 7.1(e), p. 220 | commitment optimum, unique | `Ex7_1.Commit.isOptimal_iff`, `Ex7_1.Commit.isOptimal_iff_targeting` |
| Ex 7.1(e), p. 220 | vs discretion: no long-run bias, lower loss | `Ex7_1.Commit.commitment_beats_discretion`, `Ex7_1.Commit.commitment_tendsto`, `Ex7_1.Commit.commInfl_lt_piStar` |
| Ex 7.2(a), p. 221 | wage equation error λ_w(ξ̂ + μ̂^w) | `Ex7_2.ex7_2a`, `Ex7_2.errorForm_hat` |
| Ex 7.2(a), p. 221 | the two shocks are not separately identified | `Ex7_2.errorForm_shift_iff`, `Ex7_2.not_identified` |
| Ex 7.2(b), p. 221 | in u-form only μ^w appears; both identified with participation | `Ex7_2.ex7_2b`, `Ex7_2.identified` |
| Ex 7.3(a), p. 222 | household utility = log C − χΘ∫N^{1+φ}/(1+φ) | `Ex7_3.household_utility`, `Ex7_3.integral_disutility` |
| Ex 7.3(b), p. 222 | participation w − p = ξ + z + φl | `Ex7_3.participation_log`, `Ex7_3.participants_iff` |
| Ex 7.3, p. 221 | z_t = (1−υ)z_{t−1} + υc_t; υ = 1, υ = 0 cases | `Ex7_3.z_log`, `Ex7_3.zPath_one`, `Ex7_3.zPath_zero` |
| Ex 7.3(b), p. 222 | υ dampens the labour-force response | `Ex7_3.labourForce_dampening`, `Ex7_3.dampening_strictMonoOn`, `Ex7_3.lagged_pulse_not_monotone` |
| Table 7.1, Figs. 7.2–7.6 | Simulated moments and impulse responses | Computational; not formalised |
