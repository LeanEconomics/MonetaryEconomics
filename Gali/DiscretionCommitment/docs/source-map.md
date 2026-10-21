# Source map

Galí (2015), *Monetary Policy, Inflation, and the Business Cycle*, 2nd ed.,
Chapter 5, "Monetary Policy Tradeoffs: Discretion versus Commitment" (pp. 126–162), with
Appendices 5.1–5.2 and Exercises 5.1–5.5. Each formalised claim, equation or exercise is listed
with its Lean name, relative to the namespace `Gali.DiscretionCommitment`. Page numbers are book pages.

| Book | Claim | Lean |
| --- | --- | --- |
| Galí (1), p. 128 | loss ∝ Σβᵗ(π²+ϑx²), ϑ = κ/ε | `LossAndCostPush.vartheta_eq_weight_ratio`, `LossAndCostPush.hasSum_welfare_of_loss`, `LossAndCostPush.expected_welfare_eq_scaled_loss`, `LossAndCostPush.welfareW_efficient` |
| Galí (2), p. 128 | π = βEπ' + κx + u, u = κ(yᵉ−yⁿ) | `LossAndCostPush.nkpc_iff_costPush` |
| Galí p. 128 | u ≢ 0 ⇒ tradeoff | `LossAndCostPush.zero_outcome_iff`, `LossAndCostPush.costPush_eq_zero_iff` |
| App 5.1, p. 155 | −U_n/U_c = MPN(1−Φ) | `LossAndCostPush.distortion_iff` |
| App 5.1, pp. 154–155 | completing the square with Φ | `LossAndCostPush.secondOrderUtility_eq_distorted`, `LossAndCostPush.small_distortion_polynomial`, `LossAndCostPush.period_utility_small_distortion` |
| App 5.1, p. 156 | W = −Σβᵗ[Φx̂ − ½((ε/λ)π² + Γx̂²)] | `LossAndCostPush.welfare_small_distortion` |
| App 5.2, p. 156 | reset-price sums, recursion | `CostPushSources.resetPrice_solves` |
| App 5.2, p. 157 | π = βEπ' − λ(μ−μⁿ); u = λμ̂ⁿ | `CostPushSources.inflation_eq_markupGap`, `CostPushSources.nkpc_priceMarkup` |
| App 5.2, p. 156 | sums from k = 1 break the NKPC | `CostPushSources.weights_sum_k1`, `CostPushSources.printedResetPrice_const`, `CostPushSources.printed_priceSetting_breaks_nkpc` |
| App 5.2, p. 157 | μ_t = −μ_w − (σ+φ)y + (1+φ)a | `CostPushSources.priceMarkup_eq`, `CostPushSources.printed_markup_line_iff` |
| App 5.2, p. 157 | u = +λ(μ_w − μ̄_w) | `CostPushSources.nkpc_wageMarkup`, `CostPushSources.printed_wage_costPush_contradiction`, `CostPushSources.wageMarkup_costPush_pos` |
| Galí pp. 129–130 | period problem; (4) | `Discretion.period_problem_iff`, `Discretion.periodObj_isMinOn_iff`, `Discretion.discretionEq_iff` |
| Galí p. 130 | forward inflation equation | `Discretion.inflation_forward_iff`, `Discretion.aDisc_mem` |
| Galí (5),(6), p. 130 | MSV, unique bounded | `Discretion.discretionEq_iff_msv`, `Discretion.discretion_msv_isEq`, `Discretion.discretion_iff_forwardSeries` |
| Galí p. 131 | dampening at all horizons | `Discretion.zeroGap_iff`, `Discretion.psiPi_lt`, `Discretion.dampening` |
| Galí p. 132 | permanent price-level change | `Discretion.expected_priceLevel_hasSum`, `Discretion.priceLevel_response_strictMonoOn` |
| Galí (7), p. 132 | DIS in x with rᵉ | `Discretion.dis_welfareGap_iff`, `Discretion.efficientRate_eq` |
| Galí (8), p. 133 | i = rᵉ + Ψ_i u, Ψ_i > 0 | `Discretion.interestRate_iff`, `Discretion.psiI_pos` |
| Galí (9), p. 133 | rule (8) indeterminate | `Discretion.rule8_iff_solves`, `Discretion.AO_eigenvalues`, `Discretion.AO_not_schurStable`, `Discretion.rule8_indeterminate` |
| Galí (10), p. 133 | φ_π > 1 implements uniquely (iff for φ_π ≥ 0) | `Discretion.rule10_iff_solves`, `Discretion.AT_schurStable_iff`, `Discretion.rule10_implements`, `Discretion.rule10_indeterminate` |
| Galí p. 134 | commitment problem, Lagrangian sufficiency | `Commitment.loss_sub_hasSum`, `Commitment.expLoss_sub_hasSum` |
| Galí pp. 134–135 | FOCs ϑx−κξ=0, π+ξ_t−ξ_{t−1}=0, ξ₋₁=0 | `Commitment.FOC`, `Commitment.Det.isOptimal_iff_foc` |
| Galí (11)–(13), p. 135 | targeting rule in levels | `Commitment.foc_iff_targeting`, `Commitment.targeting_iff_eleven_twelve` |
| Galí (14), p. 135 | p̂ = γp̂₋₁ + γβEp̂′ + γu | `Commitment.nkpc_iff_priceEq` |
| Galí (15), p. 136 | δ ∈ (0,1) iff κ > 0; δ root | `Commitment.del_mem_Ioo_iff`, `Commitment.del_quad`, `Commitment.four_beta_gam_sq_lt_one` |
| Galí (15), fn. 4, p. 136 | 1−γβδ = γ/δ; b = δ/(1−δβρ) | `Commitment.one_sub_gam_beta_del`, `Commitment.fwd_ar1` |
| Galí (15), p. 136 | stationary solution, unique bounded | `Commitment.pHat_ar1`, `Commitment.priceEq_unique`, `Commitment.Det.pHatD_eq` |
| Galí (16), p. 136 | x dynamics and x₀ | `Commitment.gapC_ar1`, `Commitment.gapC_zero` |
| Galí §5.2.2 | optimal policy, deterministic: exists, unique, FOCs iff | `Commitment.Det.candD_isOptimal`, `Commitment.Det.isOptimal_iff`, `Commitment.Det.existsUnique_optimal` |
| Galí §5.2.2 | optimal policy under uncertainty (with pull-out) | `Commitment.commitment_optimal`, `Commitment.finiteTree_pullOut` |
| Galí p. 143 | κ²δ/ϑ = (1−δ)(1−βδ) | `Commitment.kappa_sq_del` |
| Galí p. 137 | iterated NKPC | `Commitment.iterated_nkpc` |
| Galí p. 138 | ρ_u = 0 rate path | `Commitment.dis_iff_rate_rho0`, `Commitment.pHat_rho0_sum` |
| Galí p. 138, fn. 6 | rule with φ_p > 0 implements uniquely | `Commitment.rule_implements` |
| Galí (4)–(6), p. 130 | discretionary MSV path | `CommitmentVsDiscretion.disc_nkpc`, `CommitmentVsDiscretion.disc_unique` |
| Galí p. 137 | commitment ≥ discretion, strict if u ≠ 0 | `CommitmentVsDiscretion.commitment_le_discretion`, `CommitmentVsDiscretion.commitment_lt_discretion` |
| Galí p. 136 | persistence after a transitory shock | `CommitmentVsDiscretion.impulse_rho0` |
| Galí (17), p. 139 | loss with linear term, Λ = Φλ/ε; link to App. 5.1 | `DistortedSS.periodLoss`, `DistortedSS.distLambda`, `DistortedSS.loss_rescale`, `DistortedSS.distLambda_pos`, `DistortedSS.markup_distortion_pos` |
| Galí (18), p. 139 | NKPC in x̂ | `DistortedSS.nkpc_in_xhat` |
| Galí (19), p. 140 | discretion FOC necessary and sufficient | `DistortedSS.discretion_period_optimal_iff`, `DistortedSS.discretion_period_strict` |
| Galí (20), p. 140 | discretionary π (MSV), existence and uniqueness | `DistortedSS.discretion_exists`, `DistortedSS.discretion_unique`, `DistortedSS.discretion_forward` |
| Galí p. 141 | inflation bias π̄ > 0, x̄ > 0, increasing in Λ and Φ | `DistortedSS.inflationBias_pos`, `DistortedSS.gapBias_pos`, `DistortedSS.strictMono_inflationBias`, `DistortedSS.strictMono_inflationBias_Phi` |
| Galí p. 141 | shock response independent of Λ; bias permanent | `DistortedSS.discretion_shock_response_indep`, `DistortedSS.discretion_zeroShock` |
| Galí p. 142 | FOCs; ξ = −p̂ | `DistortedSS.CommitmentFOC`, `DistortedSS.mult_eq_neg_priceLevel` |
| Galí (21), p. 142 | ϑx̂ = −κp̂ + Λ | `DistortedSS.commitment_eq21` |
| Galí (22), p. 142 | price-level equation; γ ∈ (0,1) | `DistortedSS.commitment_eq22`, `Commitment.gam_pos`, `DistortedSS.gam_lt_one` |
| Galí (23), fn. 8, p. 142 | δ ∈ (0,1), root of the quadratic | `Commitment.del_pos`, `Commitment.del_lt_one_iff`, `Commitment.del_quad` |
| Galí (23), p. 142 | solution, existence and uniqueness | `DistortedSS.commitment_exists`, `DistortedSS.commitment_unique`, `DistortedSS.commitment_eq23` |
| Galí (24), p. 142 | backward sum | `DistortedSS.commitment_eq24` |
| Galí (25), p. 143 | x̂ dynamics | `DistortedSS.commGap_eq25`, `DistortedSS.commitment_eq25_eq27` |
| Galí (26), p. 143 | corrected x̂₀ = δΛ/ϑ − … | `DistortedSS.commGap_eq26_corrected` |
| Galí (27), p. 143 | corrected x̂_t = δ^{t+1}Λ/ϑ − … | `DistortedSS.commGap_eq27_corrected` |
| Galí (26)–(27), p. 143 | printed versions false | `DistortedSS.printed_eq26_iff`, `DistortedSS.printed_eq26_false`, `DistortedSS.printed_eq27_iff`, `DistortedSS.printed_eq27_sum_tendsto` |
| Galí p. 143 | κ²δ/ϑ = (1−δ)(1−βδ) | `Commitment.kappa_sq_del` |
| Galí p. 143 | lim p̂; κ lim p̂ = Λ | `DistortedSS.tendsto_priceLevel_zeroShock`, `DistortedSS.kappa_limit_priceLevel` |
| Galí p. 143 | lim x̂ = 0, lim π = 0; positive along the way | `DistortedSS.tendsto_gap_zeroShock`, `DistortedSS.tendsto_infl_zeroShock`, `DistortedSS.commitment_zeroShock_pos` |
| Galí pp. 143–144 | commitment avoids the permanent bias | `DistortedSS.commitment_vs_discretion_longrun` |
| Galí pp. 141–143 | deterministic optimality: FOCs necessary and sufficient; existence, uniqueness for bounded u | `DistortedSS.lagrangian_identity`, `DistortedSS.lagrangian_sufficiency`, `DistortedSS.det_optimal_iff`, `DistortedSS.det_commitment_exists`, `DistortedSS.det_commitment_optimal` |
| Galí p. 143 | linear term makes the optimum non-zero | `DistortedSS.zero_path_not_optimal`, `DistortedSS.det_zeroShock_optimal` |
| Galí (28)–(30), pp. 144–145 | ZLB, NKPC, IS, natural-rate path | `ZLBDiscretion.natRate`, `ZLBDiscretion.NKPC`, `ZLBDiscretion.DIS`, `ZLBDiscretion.dis_iff` |
| Galí p. 145 | ZLB rules out first best when rⁿ < 0 | `ZLBDiscretion.firstBest_rate`, `ZLBDiscretion.firstBest_violates_zlb`, `ZLBDiscretion.firstBest_eqm_of_nonneg` |
| Galí (31)–(32), p. 146 | per-period problem; (32) = (28)+(30) | `ZLBDiscretion.PeriodOptimal`, `ZLBDiscretion.nkpc_iff_eq31`, `ZLBDiscretion.zlb_iff_le_ups1` |
| Galí p. 146 | KKT necessary and sufficient | `ZLBDiscretion.periodKKT_sufficient`, `ZLBDiscretion.periodKKT_necessary`, `ZLBDiscretion.periodOptimal_iff_kkt`, `ZLBDiscretion.periodKKT_iff_book` |
| Galí (33), p. 146 | ϑx = −κπ − ξ₂ | `ZLBDiscretion.eq33` |
| Galí (34), p. 147 | backward system with A, B | `ZLBDiscretion.eq34_matrix`, `ZLBDiscretion.eq34_iff` |
| Galí p. 147 | x, π < 0 on [0, t_Z], ξ₂ > 0 | `ZLBDiscretion.Amat_pos`, `ZLBDiscretion.Bvec_pos`, `ZLBDiscretion.backState_neg`, `ZLBDiscretion.disc_exists` |
| Galí pp. 146–147 | discretionary equilibrium exists; unique among paths converging to 0 | `ZLBDiscretion.disc_exists`, `ZLBDiscretion.disc_unique` |
| Galí p. 146 | a second bounded (deflationary) equilibrium | `ZLBDiscretion.deflation_discEq`, `ZLBDiscretion.deflation_bounded`, `ZLBDiscretion.deflation_ne_disc` |
| Galí pp. 148–149 | commitment problem | `ZLBCommitment.Feasible`, `ZLBCommitment.loss`, `ZLBCommitment.Optimal`, `ZLBCommitment.feasible_iff` |
| Galí (35)–(36), p. 149 | FOCs + slackness | `ZLBCommitment.FOC35`, `ZLBCommitment.FOC36`, `ZLBCommitment.KKT` |
| Galí p. 149 | KKT ⇒ optimal | `ZLBCommitment.lagrangian_identity`, `ZLBCommitment.kkt_sufficient`, `ZLBCommitment.kkt_optimal` |
| Galí p. 149 | uniqueness | `ZLBCommitment.kkt_unique`, `ZLBCommitment.optimal_unique` |
| Galí (37)–(39), p. 149 | post-liftoff equations | `ZLBCommitment.post_eq37`, `ZLBCommitment.post_eq38`, `ZLBCommitment.post_eq39` |
| Galí (40)–(41), p. 150 | x = −(κ/ϑ)(p−p*), p̂ = δp̂₋₁, unique stationary | `ZLBCommitment.post_priceLevel`, `ZLBCommitment.post_eq40`, `ZLBCommitment.post_eq41`, `ZLBCommitment.post_unique_bounded` |
| Galí (42)–(43), p. 150 | x > 0, π > 0 after liftoff, → 0 | `ZLBCommitment.post_eq42_pos`, `ZLBCommitment.post_eq43_pos`, `ZLBCommitment.post_tendsto_zero` |
| Galí (44)–(47), pp. 150–151 | liftoff conditions, M | `ZLBCommitment.Mmat`, `ZLBCommitment.Nmat_det`, `ZLBCommitment.liftoff_iff`, `ZLBCommitment.eq47_iff`, `ZLBCommitment.eq47` |
| Galí (48)–(50), p. 151 | ZLB phase, H, J | `ZLBCommitment.eq48_iff`, `ZLBCommitment.eq49_iff`, `ZLBCommitment.eq49_matrix`, `ZLBCommitment.eq50_iff` |
| Galí p. 152 | algorithm: verification theorem | `ZLBCommitment.post_rate`, `ZLBCommitment.post_rate_nonneg`, `ZLBCommitment.algorithm_eq47`, `ZLBCommitment.algorithm_verification` |
| Galí p. 152 | the equation count | `ZLBCommitment.equation_count` |
| Ex 5.1(a), p. 159 | equilibrium exists | `Ex5_1.msv_equilibrium` |
| Ex 5.1(a), p. 159 | unique for φπ > 1; indeterminate for 0 ≤ φπ ≤ 1 | `Ex5_1.ex5_1a_unique`, `Ex5_1.ex5_1a_unique_bounded`, `Ex5_1.schurStable_A_iff`, `Ex5_1.ex5_1a_not_unique` |
| Ex 5.1(b), p. 159 | ϑ var x + var π = L(φπ) | `Ex5_1.ex5_1b_loss_eq` |
| Ex 5.1(b), p. 159 | φπ* = (κσ/ϑ)[1+(ϑ+κ²)σz²/σu²] unique global minimiser | `Ex5_1.lossFn_eq`, `Ex5_1.lossFn_ge`, `Ex5_1.lossFn_phiStar` |
| Ex 5.1(b), p. 159 | on φπ > 1: minimiser if φπ* > 1, corner otherwise | `Ex5_1.ex5_1b_optimal`, `Ex5_1.ex5_1b_equilibrium_optimal`, `Ex5_1.ex5_1b_corner` |
| Ex 5.1(c), p. 159 | comparative statics and limits | `Ex5_1.phiR_strictAntiOn_weight`, `Ex5_1.phiR_strictMono_ratio`, `Ex5_1.phiR_strictMono_sigma`, `Ex5_1.phiR_strictMonoOn_kappa`, `Ex5_1.tendsto_phiR_weight_zero`, `Ex5_1.tendsto_phiR_ratio_atTop` |
| Ex 5.2(a), p. 160 | Markov feasibility ⇔ ψπ(1−βρ) = κψx + 1 | `Ex5_2.markov_feasible_iff` |
| Ex 5.2(a), p. 160 | optimal Markov coefficients, unique minimiser | `Ex5_2.objective_eq`, `Ex5_2.ex5_2a` |
| Ex 5.2(b), p. 160 | Markov ≤ discretion, strict iff ρu ≠ 0 | `Ex5_2.discretion_unique`, `Ex5_2.ex5_2b_objective`, `Ex5_2.ex5_2b` |
| Ex 5.2(c), p. 160 | commitment strictly beats the Markov optimum | `Ex5_2.improve_date0`, `Ex5_2.improve_date1`, `Ex5_2.ex5_2c`, `Ex5_2.ex5_2c_commitment` |
| Ex 5.3(a), p. 161 | FOCs necessary and sufficient; optimum unique | `Ex5_3.ex5_3a_sufficient`, `Ex5_3.ex5_3a_necessary`, `Ex5_3.ex5_3a_optimal_iff` |
| Ex 5.3(b), p. 161 | FOCs ⇔ the interest-rate rule | `Ex5_3.ex5_3b_rule_iff`, `Ex5_3.ex5_3b` |
| Ex 5.4(a), p. 161 | period problem; x = −(κ/ϑ)π̃ | `Ex5_4.period_opt_iff`, `Ex5_4.period_targeting_iff`, `Ex5_4.ex5_4a_period_optimal`, `Ex5_4.period_foc_alt` |
| Ex 5.4(a), p. 161 | discretionary equilibrium exists, unique | `Ex5_4.ex5_4a_exists`, `Ex5_4.ex5_4a_unique`, `Ex5_4.ex5_4a_inflation` |
| Ex 5.4(b), p. 161 | commitment optimal ⇔ FOCs; level rule | `Ex5_4.ex5_4b_sufficient`, `Ex5_4.ex5_4b_necessary`, `Ex5_4.ex5_4b_optimal_iff`, `Ex5_4.foc_iff_level_rule`, `Ex5_4.ex5_4b` |
| Ex 5.5(a), p. 162 | discretionary equilibrium given π̄ | `Ex5_5.ex5_5a_exists`, `Ex5_5.ex5_5a_unique`, `Ex5_5.ex5_5a_period_optimal` |
| Ex 5.5(a), p. 162 | i ~ N(ρ+π̄, s²); P(i<0) = Φ(−(ρ+π̄)/s) | `Ex5_5.hasLaw_rate`, `Ex5_5.ex5_5a_prob` |
| Ex 5.5(a), p. 162 | the 5% quantile exists and is unique | `Ex5_5.exists_quantile`, `Ex5_5.phi_z05`, `Ex5_5.eq_z05_iff` |
| Ex 5.5(a), p. 162 | optimal π̄* = −ρ − s z_{0.05} | `Ex5_5.constraint_iff`, `Ex5_5.ex5_5a_loss_diff`, `Ex5_5.ex5_5a` |
| Ex 5.5(b), p. 162 | implementing rule, unique iff φ > 1 | `Ex5_5.ex5_5b_exists`, `Ex5_5.ex5_5b_unique`, `Ex5_5.ex5_5b_not_unique` |
| Ex 5.5, p. 162 | non-vacuity on a Gaussian product space | `Ex5_5.ex5_5_nonvacuous` |
| Figure 5.3, p. 152 | ZLB simulation | Computational; not formalised |
