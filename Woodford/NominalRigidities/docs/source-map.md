# Source map

Woodford (2003), *Interest and Prices*, Chapter 3, "Optimizing Models with Nominal Rigidities"
(pp. 139–236), with the proofs in Appendix B (pp. 656–669). Each formal claim is listed with its
Lean name, relative to the namespace `Woodford.NominalRigidities`. Page numbers are book pages.
Rows follow the book: Chapter 3 §1.1–§4, then Appendix B.1–B.7. A claim proved in the appendix is
listed at the place where the chapter states it.

| Book | Claim | Lean |
| --- | --- | --- |
| Woodford (1.2)–(1.3), p. 146 | the price index is the least cost of a unit of the aggregate; the minimiser exists and is unique | `DixitStiglitz.priceIndex_isLeast_unitCost`, `DixitStiglitz.cost_isLeast`, `DixitStiglitz.cost_minimiser_unique`, `DixitStiglitz.costSet` |
| Woodford (1.3), p. 146 | the index is positive; the integral identities behind it | `DixitStiglitz.priceIndex_pos`, `DixitStiglitz.priceIndex_rpow`, `DixitStiglitz.priceIndex_rpow_of_ne`, `DixitStiglitz.integral_relPrice_rpow`, `DixitStiglitz.integrated_young` |
| Woodford (1.5), p. 147 | demand; it is the unique cost-minimising bundle and expenditure is `PC` (both directions) | `DixitStiglitz.demand`, `DixitStiglitz.spend_ge`, `DixitStiglitz.spend_eq_iff`, `DixitStiglitz.spend_demand`, `DixitStiglitz.cesAgg_demand`, `DixitStiglitz.price_mul_demand` |
| Woodford (1.5), p. 147 | the dual form: the largest aggregate for given spending | `DixitStiglitz.cesAgg_le_of_spend`, `DixitStiglitz.cesAgg_eq_iff_of_spend` |
| Woodford (1.5), p. 147 | on the unit interval and with finitely many goods | `DixitStiglitz.unitInterval_expenditure_minimisation`, `DixitStiglitz.Finite.finite_expenditure_minimisation` |
| Woodford n. 5, (1.12), p. 147 | market clearing in each good | `DixitStiglitz.market_clearing` |
| Woodford (1.7), p. 148 | the production technology | `MarginalCost.Technology`, `MarginalCost.Technology.f_strictMonoOn`, `MarginalCost.Technology.finv_strictMonoOn`, `MarginalCost.Technology.hasDerivAt_finv` |
| Woodford (1.8)–(1.9), p. 148 | `MC = (w/A)Ψ(y/A)`; `Ψ` positive, continuous and increasing | `MarginalCost.Technology.hasDerivAt_variableCost`, `MarginalCost.Technology.Psi`, `MarginalCost.Technology.Psi_pos`, `MarginalCost.Technology.Psi_strictMonoOn`, `MarginalCost.Technology.Psi_continuousOn`, `MarginalCost.Technology.hasDerivAt_Psi` |
| Woodford p. 148 | with linear technology `Ψ` is constant | `MarginalCost.linearTech`, `MarginalCost.linearTech_Psi`, `MarginalCost.linearTech_not_strictMono` |
| Woodford (1.10), p. 149 | real marginal cost `s(y, Y; ξ̃)` | `MarginalCost.rmc`, `MarginalCost.rmc_eq_real_wage_cost` |
| Woodford (1.11), p. 150 | the yeoman-farmer equivalence | `MarginalCost.yeoman_hasDerivAt`, `MarginalCost.yeoman_rmc` |
| Woodford p. 151 | `s` increasing in both arguments (strictly only under strict concavity) | `MarginalCost.rmc_strictMonoOn_y`, `MarginalCost.rmc_strictMonoOn_Y`, `MarginalCost.rmc_linear_const` |
| Woodford (1.12), p. 151 | demand for good `i` | `FlexiblePrices.dem`, `FlexiblePrices.dem_pos`, `FlexiblePrices.hasDerivAt_dem`, `FlexiblePrices.dem_strictAntiOn` |
| Woodford p. 151 | the Lerner markup `μ = θ/(θ − 1)` | `FlexiblePrices.hasDerivAt_profit`, `FlexiblePrices.lerner_foc_iff`, `FlexiblePrices.lerner_singlePeaked` |
| Woodford (1.13), p. 151 | a unique `y(i)` given `Y`; `p/P = μs` | `FlexiblePrices.relative_supply_existsUnique`, `FlexiblePrices.baseline_markup` |
| Woodford (1.14), p. 151 | the symmetric equilibrium `μs(Y, Y) = 1` | `FlexiblePrices.symmetric_flexible_eqm`, `FlexiblePrices.symmetric_flexible_eqm_of`, `FlexiblePrices.baseline_flexEqm_iff`, `FlexiblePrices.diag_strictMonoOn` |
| Woodford (1.14), p. 151 | existence of the natural rate (corrected) | `FlexiblePrices.naturalRate_existsUnique_iff`, `FlexiblePrices.isoelastic_naturalRate` |
| Woodford (1.14), p. 151 | existence fails under the stated hypotheses | `FlexiblePrices.bounded_primitives`, `FlexiblePrices.bounded_rmc_strictMono`, `FlexiblePrices.noNaturalRate_baseline`, `FlexiblePrices.baseline_noFlexEqm` |
| Woodford (1.15)–(1.16), p. 152 | `ω = ω_w + ω_p`, `σ⁻¹`, technology elasticity `−(1 + ω)` | `MarginalCost.omegaW`, `MarginalCost.omegaP`, `MarginalCost.sigmaInv`, `MarginalCost.elasticity_rmc_y`, `MarginalCost.elasticity_rmc_Y`, `MarginalCost.elasticity_rmc_A` |
| Woodford (1.16), p. 152 | the component elasticities | `MarginalCost.elasticity_vh`, `MarginalCost.elasticity_Psi`, `MarginalCost.elasticity_uc`, `MarginalCost.log_rmc` |
| Woodford p. 152 | `ω_p, ω_w, σ⁻¹ > 0` (exact conditions) | `MarginalCost.omegaP_pos_iff`, `MarginalCost.omegaW_pos_iff`, `MarginalCost.sigmaInv_pos_iff`, `MarginalCost.linearTech_omegaP` |
| Woodford (1.15), p. 152 | `ŝ = ωŷ + σ⁻¹Ŷ − (ω + σ⁻¹)Ŷⁿ` as an exact derivative | `MarginalCost.logRmcGap`, `MarginalCost.fderiv_logRmcGap`, `MarginalCost.eq_1_15`, `MarginalCost.naturalRate_deriv`, `FlexiblePrices.eq_1_15_unconditional` |
| Woodford p. 152 | the natural rate is continuous and differentiable in the shocks | `FlexiblePrices.root_continuousAt`, `FlexiblePrices.implicit_hasFDerivAt`, `FlexiblePrices.logRmcGap_diag_strictMono` |
| Woodford (1.18), p. 153 | the baseline profit function is homogeneous of degree one and single-peaked | `FlexiblePrices.baselineProfit`, `FlexiblePrices.baselineProfit_homogeneous`, `FlexiblePrices.baseline_singlePeaked` |
| Assumption 3.1, pp. 153–154 | homogeneity and single-peakedness; `Π₁` homogeneous of degree 0; Euler | `FlexiblePrices.HomogeneousOne`, `FlexiblePrices.SinglePeakedAt`, `FlexiblePrices.Assumption31`, `FlexiblePrices.deriv_homogeneous_zero`, `FlexiblePrices.euler`, `Predetermined.deriv_homogeneous_degree_zero`, `Calvo.hom_deg_zero_of_hom_deg_one` |
| Woodford p. 154 | the peak is the optimum; FOC at the peak | `FlexiblePrices.singlePeaked_lt`, `FlexiblePrices.singlePeaked_isOptimal_iff`, `FlexiblePrices.isOptimal_deriv_zero`, `FlexiblePrices.foc_iff_optimal` |
| Prop 3.1, p. 154 | output is independent of monetary policy | `FlexiblePrices.flexEqm_iff_one`, `FlexiblePrices.FlexEqm` |
| Prop 3.1, (1.19)–(1.21), p. 154 | (1.21) necessary; existence and uniqueness of `Yⁿ` (corrected) | `FlexiblePrices.flexEqm_foc`, `FlexiblePrices.prop_3_1_characterisation`, `FlexiblePrices.prop_3_1` |
| Prop 3.1, p. 154 | Assumption 3.1 gives neither existence nor uniqueness | `FlexiblePrices.twoRoots_counterexample`, `FlexiblePrices.noNaturalRate_counterexample`, `FlexiblePrices.continuumNaturalRate_counterexample` |
| Woodford (1.21), p. 154 | the natural rate exists locally (implicit-function theorem) | `Predetermined.natural_rate_exists`, `Predetermined.implicit_function_scalar`, `Predetermined.implicit_function_real` |
| Woodford (1.21), p. 154; (1.15) | Calvo's `ŷⁿ = −(ψ_z/ψ_y)z` equals the natural-rate derivative of §1.1 | `Calvo.natRate_deriv`, `Links.baseD_natRate` |
| Woodford (1.22)–(1.23), p. 155 | the ex-ante FOC is necessary (finite trees, perfect foresight) | `Predetermined.hasDerivAt_expected_profit`, `Predetermined.foc_1_23_necessary`, `Predetermined.foc_1_23_tree`, `Predetermined.foc_1_23_perfectForesight` |
| Woodford (1.22)–(1.23), p. 155 | the FOC is sufficient under concave profits | `Predetermined.concave_tangent_le`, `Predetermined.foc_1_23_sufficient` |
| Woodford (1.24), p. 156 | the FOC involves no nominal variables | `Predetermined.expected_foc_symmetric_eq` |
| Woodford (1.25), p. 156; p. 164 | the baseline `Π₁` and form of the FOC | `Predetermined.baselineProfit`, `Predetermined.hasDerivAt_baselineProfit`, `Predetermined.baselineProfit_foc_symmetric`, `Predetermined.expected_foc_baseline_iff` |
| Woodford (1.26), pp. 156–157 | `P` exists and is unique ("implicitly defined") | `Predetermined.asResidualAt`, `Predetermined.asRoot_existsUnique`, `Predetermined.priceLevel_existsUnique_tree`, `Predetermined.tree_condE_congr_on_cell`, `Predetermined.tree_known_const_on_cell` |
| Woodford (1.26), pp. 156–157 | without monotonicity several solutions, without a sign change none | `Predetermined.priceLevel_not_unique_counterexample`, `Predetermined.priceLevel_not_exists_counterexample` |
| Woodford p. 157 | `P` is homogeneous of degree 1 in nominal spending; output is scale-invariant | `Predetermined.priceLevel_homogeneous`, `Predetermined.priceLevel_homogeneous_tree`, `Predetermined.asResidual_scale`, `Predetermined.output_scale_invariant` |
| Woodford (1.27), p. 157 | `Π₁ ≈ ψ_y(Ŷ − Ŷⁿ)` | `Predetermined.linearisation_gap_form` |
| Woodford p. 157 | the discount factor drops out to first order | `Predetermined.hasDerivAt_E_foc_product` |
| Woodford p. 157 | `log P = E log 𝒴 − E log Yⁿ`; `log Y = E log Yⁿ +` spending surprise; `E log Y = E log Yⁿ` | `Predetermined.AS.expected_gap_zero_of_foc`, `Predetermined.AS.predetermined_price_level`, `Predetermined.AS.predetermined_output`, `Predetermined.AS.forecastable_output` |
| Woodford p. 158 | the output surprise equals the spending surprise | `Predetermined.AS.output_surprise` |
| Woodford (1.30), p. 158 | `Π₁ ≈ ψ_p(log p/P − ζ(Ŷ − Ŷⁿ))` | `Predetermined.foc_relative_price_form`, `Predetermined.linearised_foc_form`, `Calvo.marginal_profit_gap_form` |
| Woodford p. 158 | `ψ_p < 0` does not follow from Assumption 3.1 | `Predetermined.cePi`, `Predetermined.cePi1`, `Predetermined.psi_p_not_negative_counterexample` |
| Woodford p. 159 | `log P = ι log p₁ + (1 − ι) log p₂` as an exact derivative | `Predetermined.logCES2`, `Predetermined.logCES2_eq`, `Predetermined.hasFDerivAt_log_ces_two` |
| Woodford (1.31), p. 159 | `log p₂ = E_{t−1} log p₁`; the price surprise | `Predetermined.NC.sticky_price_eq`, `Predetermined.NC.sticky_eq_expected_flex`, `Predetermined.NC.surprise_price` |
| Prop 3.2, (1.32), p. 159 | the New Classical Phillips curve | `Predetermined.NC.prop_3_2`, `Predetermined.NC.kappa_pos` |
| Woodford p. 160 | `E_{t−1}` of the gap is zero; `E log Y = E log Yⁿ` | `Predetermined.PC.expected_gap_zero`, `Predetermined.PC.expected_output` |
| Woodford (1.33), p. 160 | output and the price level (corrected) | `Predetermined.PC.output_corrected`, `Predetermined.PC.price_level_corrected` |
| Woodford (1.33), p. 160 | the printed forms hold iff `Yⁿ` is predictable; counterexample | `Predetermined.PC.printed_1_33_iff`, `Predetermined.PC.printed_price_level_iff`, `Predetermined.printed_1_33_counterexample` |
| Woodford (1.32)–(1.33), pp. 159–160 | output moves only on impact in the New Classical model | `Persistence.NCPC`, `Persistence.ncpc_iff`, `Persistence.ncpc_shock_gap`, `Persistence.nc_vs_calvo` |
| Fig. 3.1, p. 160 | the curve: closed form, endpoints, derivatives | `Predetermined.kappaNC`, `Predetermined.outputElasticity`, `Predetermined.fig31`, `Predetermined.fig31_closed_form`, `Predetermined.fig31_endpoints`, `Predetermined.fig31_hasDerivAt`, `Predetermined.fig31_deriv2` |
| Fig. 3.1, p. 160 | decreasing; convex iff `ζ > 1`, concave iff `ζ < 1`, linear at `ζ = 1`; farther from the chord the larger `ζ` | `Predetermined.fig31_strictAntiOn`, `Predetermined.fig31_strictConvexOn`, `Predetermined.fig31_strictConcaveOn`, `Predetermined.fig31_linear`, `Predetermined.fig31_antitone_zeta`, `Predetermined.fig31_vs_chord` |
| Woodford p. 160 | `κ → ∞` and `1/(1 + κ) → 0` as `ι → 1` | `Predetermined.kappaNC_strictMonoOn`, `Predetermined.kappaNC_tendsto_atTop`, `Predetermined.outputElasticity_tendsto_zero` |
| Woodford (1.34), p. 162 | the notional SRAS `log(p^I/P) = ζ(Ŷ − Ŷⁿ)` | `StrategicComplementarity.notional_sras_general`, `StrategicComplementarity.sras_gap_form` |
| Woodford p. 162 | best-response slope `1 − ζ`; complements iff `ζ < 1` | `StrategicComplementarity.best_response_hasDerivAt`, `StrategicComplementarity.strategic_complements_iff`, `StrategicComplementarity.strategic_substitutes_iff` |
| Woodford p. 164, (1.16) | for the baseline model `ψ_p = −(θ − 1)Ȳ(1 + ωθ)`, `ψ_y = (θ − 1)Ȳ(ω + σ⁻¹)` | `Links.baseD_coeffs` |
| Woodford (1.35), p. 164 | `ζ = (ω + σ⁻¹)/(1 + ωθ)`; `ζ < 1` if `σ⁻¹ = 0`; equal to `−ψ_y/ψ_p` | `StrategicComplementarity.zeta_1_35`, `StrategicComplementarity.zeta_1_35_pos`, `StrategicComplementarity.zeta_lt_one_linear_utility`, `Links.baseD_zeta` |
| Woodford pp. 152–167 | marginal-cost elasticities by factor-market structure | `StrategicComplementarity.specific_factor_elasticities`, `StrategicComplementarity.common_labour_elasticities`, `StrategicComplementarity.homogeneous_factor_elasticities` |
| Woodford p. 165 | `ζ = ω + σ⁻¹` in homogeneous factor markets; `> 1` if `σ = 1` | `StrategicComplementarity.zeta_homogeneous`, `StrategicComplementarity.zeta_homogeneous_gt_one` |
| Woodford p. 166 | 2.25, 1.25, 0.17 | `StrategicComplementarity.chari_numbers` |
| Woodford (1.37), p. 167 | the common-labour-market `ζ`; between the other two; 0.38 | `StrategicComplementarity.zeta_1_37`, `StrategicComplementarity.zeta_1_37_between`, `StrategicComplementarity.chari_common_labour` |
| Woodford p. 168 | CES gives a constant elasticity | `Kimball.ces_theta_const` |
| Woodford (1.39)–(1.41), pp. 168–169 | the notional SRAS slope `ζ = (s_y + s_Y)/(1 + θ(ε_μ + s_y))`; the curve exists | `StrategicComplementarity.zetaGen`, `StrategicComplementarity.sras`, `StrategicComplementarity.notional_sras_slope`, `StrategicComplementarity.notional_sras_exists` |
| Woodford (1.39), p. 168 | `p/P = μ(y/Y)s` | `Kimball.kimball_foc_iff`, `Kimball.muK` |
| Woodford p. 169 | `ε_μ = −θ′/(θ(θ − 1))`; `ε_μ > 0` iff `θ` decreasing | `Kimball.markupLog`, `Kimball.markup_elasticity`, `Kimball.markup_elasticity_pos_iff` |
| Woodford p. 169 | `ε_μ` lowers `ζ`; `ζ → 0` as `ε_μ → ∞` | `StrategicComplementarity.zetaGen_strictAntiOn_markup`, `StrategicComplementarity.zetaGen_tendsto_zero_markup` |
| Woodford p. 169 | the Bergin–Feenstra pricing equation; pass-through one half | `StrategicComplementarity.bergin_feenstra`, `StrategicComplementarity.bergin_feenstra_passthrough_half` |
| Woodford pp. 169–170 | Kimball special cases; 0.17 → 0.16 | `StrategicComplementarity.zeta_kimball_homogeneous`, `StrategicComplementarity.zeta_kimball_specific` |
| Woodford (1.42), p. 170 | Leontief technology with intermediate inputs | `Kimball.leontief_feasible_iff`, `Kimball.leontief_cost_min` |
| Prop 3.3, (1.43), p. 171 | `ζ` with intermediate inputs | `StrategicComplementarity.zeta33`, `StrategicComplementarity.prop_3_3_formula`, `StrategicComplementarity.prop_3_3` |
| Prop 3.3, p. 171; B.2, (B.6), pp. 657–659 | Proposition 3.3 from the primitives `ψ`, `θ(·)`, value-added marginal cost and `s_m`; from `ψ ∈ C³` | `Kimball.prop_3_3_complete`, `Kimball.prop_3_3_from_psi` |
| Woodford p. 171 | `ζ → 0` as `s_m → μ⁻¹`; the factor 0.4 | `StrategicComplementarity.zeta33_tendsto_zero`, `StrategicComplementarity.zeta33_homogeneous_factor` |
| Woodford fn. 23, p. 171 | 54% materials share; `s_m = 0.9` gives `ζ = 0` | `StrategicComplementarity.footnote_23` |
| Table 3.1, p. 172 | all 16 entries, exactly, and their rounding | `StrategicComplementarity.table31_row1`, `StrategicComplementarity.table31_row2`, `StrategicComplementarity.table31_row3`, `StrategicComplementarity.table31_row4`, `StrategicComplementarity.table31_rounding`, `StrategicComplementarity.table31_one_fifth` |
| Woodford p. 177 | the lottery model of Calvo pricing | `Calvo.lottery_model`, `Calvo.integral_calvo_mix`, `Calvo.dist_law_of_motion` |
| Woodford (2.1), p. 178 | the Calvo index recursion, exact for a continuum of goods | `Calvo.calvo_integral`, `Calvo.calvo_index_rpow`, `Calvo.calvo_index`, `Calvo.calvo_index_lottery` |
| Woodford p. 178 | cohort decomposition; weights sum to one | `Calvo.cohort_decomposition`, `Calvo.cohort_weights_sum` |
| Woodford (2.2)–(2.3), pp. 178–179 | the infinite-horizon objective (genuine `tsum`) and its FOC | `Calvo.resetObjective`, `Calvo.resetFOC`, `Calvo.hasDerivAt_resetObjective`, `Calvo.foc_of_isLocalMax`, `Calvo.hasDerivAt_tsum_E`, `Calvo.hasDerivAt_E` |
| Woodford (2.2)–(2.4), p. 179 | the FOC characterises the optimum under concave profits | `Calvo.concaveOn_resetObjective`, `Calvo.isMaxOn_of_concaveOn_of_deriv_zero`, `Calvo.isMaxOn_iff_foc` |
| Woodford fn. 31, p. 179 | reduces to (1.22) | `Calvo.objective_fn31` |
| Woodford p. 179 | the zero-inflation steady state solves (2.1) and (2.4) | `Calvo.steady_state_solves`, `Calvo.focPath`, `Calvo.focPath_zero`, `Calvo.foc_relative_price` |
| Woodford (2.5), p. 180 | the log of (2.1) as an exact Fréchet derivative | `Calvo.logIndexFn`, `Calvo.log_calvo_index`, `Calvo.logIndexFn_diag`, `Calvo.hasFDerivAt_logIndexFn`, `Calvo.hasDerivAt_logIndexFn_path`, `Calvo.Eq25` |
| Woodford (2.6), p. 180 | the exact derivative of (2.4); the discount-factor term drops out | `Calvo.mp_uniform_expansion`, `Calvo.hasDerivAt_tsum_E_of_expansion`, `Calvo.hasDerivAt_focPath`, `Calvo.focPath_deriv_eq`, `Calvo.eq26_iff_deriv_zero`, `Calvo.Eq26` |
| Woodford (1.18), (2.4), pp. 153, 179 | the baseline marginal profit `mp(x, y, z)` is the own-price derivative of (1.18) | `Links.baseMP`, `Links.baselineProfit_hasDerivAt`, `Links.baseMP_eq`, `Links.dem_exp`, `Links.rmc_pos`, `Links.shockLin` |
| Woodford (2.6), p. 180 | the baseline `mp` is Fréchet-differentiable at the steady state | `Links.baseD`, `Links.baseMP_hasFDerivAt`, `Links.baseD_apply` |
| Woodford (1.15), (1.30), (2.14) | `ζ(ŷ − ŷⁿ) = (1 + ωθ)⁻¹ŝ`, derived not assumed | `Links.baseD_gap_rmc` |
| Woodford (2.6)–(2.8), p. 181 | (2.6) ⇔ (2.8); from primitives | `Calvo.costTerm`, `Calvo.Eq28`, `Calvo.eq26_iff_eq28`, `Links.eq26_iff_eq28_baseline` |
| Woodford (2.10)–(2.11), p. 182 | the quadratic and its roots `0 < λ₁ < 1 < β⁻¹ < λ₂`; `ξ` | `QuadraticRoots.charPoly`, `QuadraticRoots.lam1`, `QuadraticRoots.lam2`, `QuadraticRoots.root_location`, `QuadraticRoots.lam1_lt_one_lt_lam2`, `QuadraticRoots.calvoXi`, `QuadraticRoots.calvoXi_pos` |
| Prop 3.4, p. 182; B.3, pp. 659–661 | existence and uniqueness in the difference-stationary class | `Calvo.DiffStationary`, `Calvo.prop34`, `Calvo.prop34_unique`, `Calvo.prop34_exists_iff`, `Calvo.prop34_init_necessary`, `Calvo.psol_eq25`, `Calvo.psol_eq28` |
| Woodford (2.9), p. 182 | the explicit form of the solution | `Calvo.Psol`, `Calvo.psol_eq29`, `Calvo.psol_known`, `Calvo.psol_boundedIncr` |
| Prop 3.4, p. 182 | outside the class: a continuum when `ω̃θ > 0`; unique when `ω̃θ = 0`; perfect-foresight uniqueness when `ω̃θ < 0` | `Calvo.prop34_continuum`, `Calvo.prop34_continuum_injective`, `Calvo.perturbation_not_diffStationary`, `Calvo.perturbation_not_summable`, `Calvo.prop34_unique_of_w_zero`, `Calvo.prop34_pf_unique_of_w_neg` |
| Prop 3.4, p. 182 | `α` versus `λ₁`; `αβλ₂ < 1` iff `ω̃θ > 0` | `QuadraticRoots.alpha_lt_lam1_iff`, `QuadraticRoots.lam1_eq_alpha_iff`, `QuadraticRoots.alpha_lt_lam1_calvo_iff`, `QuadraticRoots.alpha_beta_lam2` |
| Woodford §2.1, p. 183 | dependence of the roots on the slope; flexible-price limit | `QuadraticRoots.lam1_strictAntiOn`, `QuadraticRoots.lam2_strictMonoOn`, `QuadraticRoots.tendsto_lam1_zero`, `QuadraticRoots.tendsto_lam2_zero`, `QuadraticRoots.tendsto_lam1_atTop`, `QuadraticRoots.tendsto_inv_lam2_atTop`, `Calvo.flexible_limit` |
| Woodford fn. 41, p. 186 | `λ₁λ₂ = β⁻¹` | `QuadraticRoots.lam1_mul_lam2` |
| Woodford (2.12)–(2.13), p. 187 | the NKPC and its slope `κ` | `NKPC.infl`, `NKPC.NKPCurve`, `QuadraticRoots.kappa`, `QuadraticRoots.kappa_pos` |
| Prop 3.5, p. 187; B.4, pp. 661–662 | (2.6) ⇔ NKPC given (2.5) | `NKPC.prop35`, `NKPC.B17_iff_nkpc`, `NKPC.inflation_eq_resetGap`, `NKPC.eq26_iff_resetGap` |
| Prop 3.5, p. 187; (2.13)–(2.14) | from primitives: (2.6) ⇔ NKPC with `κ(ζ)` ⇔ `π = ξŝ + βEπ`, `κ = (ω + σ⁻¹)ξ` | `Links.prop35_baseline` |
| Woodford p. 187 | `κ = (ω + σ⁻¹)ξ`; comparative statics in `ω` and `θ` | `NKPC.kappa_baseline`, `NKPC.kappaBase`, `NKPC.kappaBase_omega_diff`, `NKPC.kappaBase_strictMonoOn_omega`, `NKPC.kappaBase_strictAntiOn_omega`, `NKPC.kappaBase_const_omega`, `NKPC.hasDerivAt_kappaBase_omega`, `NKPC.hasDerivAt_kappaBase_theta`, `NKPC.kappaBase_strictAntiOn_theta` |
| Woodford (2.14), p. 188 | `π = ξŝ + βE_tπ_{t+1}` | `NKPC.kappa_gap_eq_xi_s`, `NKPC.nkpc_iff_eq214` |
| Woodford p. 188 | forecastable gaps | `NKPC.forecastable_gap_iff` |
| Woodford p. 188 | `κ` increasing in `ζ`, decreasing in `α`; the limits `α → 0, 1` | `NKPC.kappa_strictMono_zeta`, `NKPC.kappa_strictAntiOn_alpha`, `NKPC.tendsto_kappa_alpha_one`, `NKPC.tendsto_kappa_alpha_zero` |
| Woodford (2.12), pp. 187, 189 | the price-level form used in §2.3 is the NKPC | `Persistence.NKPC`, `Persistence.nkpc_iff_second_order`, `Links.persistence_nkpc_iff`, `Links.prop35_persistence` |
| Woodford p. 189; B.5 | unique equilibrium (linear growth, stationary gap), any expectation system | `Persistence.LinGrowth`, `Persistence.eqmP`, `Persistence.eqmP_nkpc`, `Persistence.nkpc_unique`, `Persistence.nkpc_existsUnique`, `Persistence.nkpc_existsUnique_gap`, `Links.calvo_eq_eqmP` |
| Woodford p. 189; B.3, p. 661 | non-uniqueness outside the class | `Persistence.nkpc_add_hom`, `Persistence.nkpc_not_unique`, `Persistence.nkpc_solutions_not_countable` |
| Woodford (2.16)–(2.18), pp. 189–190 | the impulse-response difference equation and its general solution | `Persistence.IRFEq`, `Persistence.irfEq_iff_lag`, `Persistence.irfEq_iff_exists`, `Persistence.hom_unbounded`, `Persistence.irfEq_bounded_unique`, `Persistence.irfEq_unbounded_family` |
| Woodford (2.19), p. 190 | `0 < λ₁ < 1 < β⁻¹ < λ₂`, `λ₁λ₂ = β⁻¹` | `Persistence.root_location`, `Persistence.lam1_mul_lam2` |
| Prop 3.6, p. 190; B.5, pp. 662–664 | `p̃_k = 1 − λ^{k+1}` is the unique solution with `p̃_k → 1`; a continuum otherwise | `Persistence.p36`, `Persistence.prop_3_6`, `Persistence.prop_3_6_unique`, `Persistence.prop_3_6_bounded`, `Persistence.prop_3_6_all_solutions` |
| Prop 3.6, p. 190 | the stochastic statement: `p̃_k = ∂E_t log P_{t+k}/∂ε_t` | `Persistence.shock_response`, `Persistence.shock_response_expect`, `Persistence.shock_hasDerivAt`, `Persistence.prop_3_6_stochastic` |
| Prop 3.6, p. 190 | for Calvo-derived equilibria | `Links.prop_3_6_calvo` |
| Woodford p. 191 | `ỹ₀ = λ < 1`, monotone decay; `p̃` rises to 1 | `Persistence.y36`, `Persistence.y36_eq`, `Persistence.y36_zero`, `Persistence.y36_decay`, `Persistence.p36_rise`, `Persistence.p36_tendsto` |
| Fig. 3.7, p. 191 | `λ ≈ 0.8605` | `Persistence.lam1_fig37` |
| Woodford p. 192 | `λ` decreasing in `κ`; `→ 0` as `κ → ∞`, `→ 1` as `κ → 0`; any `κ` through `ζ` | `Persistence.lam1_strictAnti`, `Persistence.lam1_lt_two_div`, `Persistence.lam1_tendsto_zero_atTop`, `Persistence.lam1_tendsto_one`, `Persistence.kappaCalvo_surj`, `Persistence.kappaCalvo_strictAnti_alpha`, `Persistence.lam1_strictMono_alpha`, `Persistence.lam1_strictAnti_zeta` |
| Woodford p. 193 | `P(α) = (1 − α)(1 − αβ)(1 − ζ)`; `λ > α` iff `ζ < 1` (and the `=`, `<` cases) | `Persistence.charPoly_alpha`, `QuadraticRoots.charPoly_alpha`, `QuadraticRoots.charPoly_alpha_calvo`, `Persistence.alpha_lt_lam_iff`, `Persistence.alpha_eq_lam_iff`, `Persistence.lam_lt_alpha_iff` |
| Woodford p. 194 | half-lives; the contract multiplier `log α⁻¹/log λ⁻¹ > 1` iff `ζ < 1` | `Persistence.halfLife`, `Persistence.rpow_halfLife`, `Persistence.halfLife_strictMonoOn`, `Persistence.contractMult`, `Persistence.contractMult_eq`, `Persistence.contractMult_gt_one_iff` |
| Woodford (2.20), fn. 50, p. 194 | `log λ⁻¹/Δ → n`; the multiplier tends to `2a*/(√(4a*(a* + 1)ζ + 1) − 1)` | `Persistence.tendsto_rate`, `Persistence.ct_limit`, `Persistence.contractMult_tendsto`, `Persistence.div_ctRoot_eq_cmLimit`, `Persistence.cmLimit` |
| Woodford p. 194 | the limit multiplier: `> 1` iff `ζ < 1`, decreasing, `≈ ζ^{−1/2}` for `a* ≫ 1` | `Persistence.cmLimit_gt_one_iff`, `Persistence.cmLimit_strictAnti`, `Persistence.cmLimit_eq_iff`, `Persistence.cmLimit_tendsto_atTop` |
| Woodford p. 195, fn. 51 | a multiplier of 20 needs `ζ ≈ 0.004`; Chari et al. | `Persistence.zeta_for_twenty`, `Persistence.cmLimit_0004`, `Persistence.chari_required_multiplier` |
| Woodford p. 196 | 1.44 ⇒ `ζ = 0.49`; `ζ ∈ [.10, .15]` ⇒ 2.6–3.3, half-lives 5.5–6.8 | `Persistence.required_multiplier_144`, `Persistence.zeta_for_144`, `Persistence.cmLimit_010`, `Persistence.cmLimit_015`, `Persistence.half_lives_55_68` |
| Woodford p. 196, fn. 55 | the 2.08-quarter half-life; `1 − e^{−0.33} = 0.28` | `Persistence.sync_half_life`, `Persistence.frac_changed_028` |
| Woodford (2.21), p. 197 | an innovation raises `E log 𝒴_{t+k}` by `(1 − ρ)⁻¹(1 − ρ^{k+1})` | `SpendingGrowth.ARGrowth`, `SpendingGrowth.arGrowth_shock`, `SpendingGrowth.unit_response` |
| Prop 3.7, p. 198; B.6, pp. 664–666 | `ỹ_k`, `p̃_k = 1 − ρ^{k+1} − ỹ_k`; uniqueness, a continuum outside | `SpendingGrowth.y37`, `SpendingGrowth.p37`, `SpendingGrowth.prop_3_7`, `SpendingGrowth.prop_3_7_classes`, `SpendingGrowth.p37_irfEq`, `SpendingGrowth.y37_tendsto`, `SpendingGrowth.p37_tendsto` |
| Prop 3.7, p. 198 | for every `0 ≤ ρ < 1`, including `ρ = λ` | `SpendingGrowth.hsum`, `SpendingGrowth.hsum_closed`, `SpendingGrowth.hsum_diag`, `SpendingGrowth.rho_eq_lam` |
| Prop 3.7, p. 198 | the full stochastic statement | `SpendingGrowth.prop_3_7_stochastic` |
| Woodford p. 198 | `ρ = 0` reduces to Proposition 3.6 | `SpendingGrowth.rho_zero` |
| Woodford p. 198 | `ỹ_k > 0`; unimodal; a hump iff `λ + ρ > 1` | `SpendingGrowth.y37_pos`, `SpendingGrowth.y37_unimodal`, `SpendingGrowth.hump_iff`, `SpendingGrowth.hsum_decr_after` |
| Woodford p. 198 | `ỹ₁ = (λ + ρ)ỹ₀` (printed with the wrong index) | `SpendingGrowth.E3_index` |
| Fig. 3.9, p. 199 | a hump at `β = .99`, `κ = .024`, `ρ = .4` | `SpendingGrowth.fig39_hump` |
| Woodford p. 200 | peak output arbitrarily close to 1 as `κ → 0`, yet below spending | `SpendingGrowth.peak_near_one`, `SpendingGrowth.p37_pos`, `SpendingGrowth.hsum_one`, `SpendingGrowth.y37_tendsto_kappa` |
| Woodford p. 200 | the New Classical peak is at most `1 − ρ` | `SpendingGrowth.nc_peak_bound` |
| Woodford (2.22)–(2.23), pp. 200–201 | sector indices are minimal costs; the two-level demand system; normalisation | `DixitStiglitz.Nested.sector_cost`, `DixitStiglitz.Nested.nested_cost_ge_and_eq_iff`, `DixitStiglitz.Nested.nested_demand_attains`, `DixitStiglitz.Nested.nested_isLeast`, `DixitStiglitz.Nested.common_price_demands`, `DixitStiglitz.Nested.upperIndex` |
| Woodford (2.22)–(2.23), pp. 200–201 | the demands give back `C`; expenditure `PC`; common prices | `TwoSector.finPriceIndex_two`, `TwoSector.upperIndex_two`, `TwoSector.ces_aggregate_of_demands`, `TwoSector.ces_expenditure`, `TwoSector.ces_common_price`, `TwoSector.lowerNest_const`, `DixitStiglitz.priceIndex_const`, `DixitStiglitz.cesAgg_const` |
| Woodford p. 201 | the sectors `[0, n₁] ∪ (n₁, 1]` | `DixitStiglitz.twoSector_split` |
| Woodford n. 61, p. 201 | `η < 1` allowed; Cobb–Douglas as the limit `η → 1` | `DixitStiglitz.finPriceIndex`, `DixitStiglitz.fin_cost_ge_and_eq_iff`, `DixitStiglitz.cobbDouglas_cost_ge_and_eq_iff`, `DixitStiglitz.tendsto_cobbDouglas`, `TwoSector.nestedIndex_tendsto_cobbDouglas`, `TwoSector.nestedAgg_tendsto_cobbDouglas` |
| Woodford p. 201 | `n₁p̂₁ + n₂p̂₂ = 0` (needs `η ≠ 1`) | `TwoSector.relPrice_sum`, `TwoSector.relPrice_index_linear` |
| Woodford (2.25), p. 202 | the level form ⇔ the relative reset price | `TwoSector.Eq225`, `TwoSector.E_level`, `TwoSector.level_iff_relative`, `TwoSector.printed_2_25_fails` |
| Woodford (2.26), p. 202 | the sectoral Calvo index linearised | `TwoSector.hasDerivAt_logCES2` |
| Prop 3.8, (2.27), p. 203; B.7, pp. 666–669 | the sectoral Phillips curves; derived from (B.32) and the Calvo law | `TwoSector.prop_3_8`, `TwoSector.prop_3_8_full`, `TwoSector.kappaJ`, `TwoSector.gamma1`, `TwoSector.gamma2` |
| Prop 3.8, p. 203 | `κ_j > 0`, `γ₁ > 0`, `γ₂ < 0` | `TwoSector.kappa_pos`, `TwoSector.gamma1_pos`, `TwoSector.gamma2_neg` |
| Woodford (2.28), p. 204 | the relative-price identity; the aggregate price | `TwoSector.relPrice_identity`, `TwoSector.aggregate_price`, `TwoSector.relPrices_of_index` |
| Woodford p. 204; p. 669 | the natural relative price | `TwoSector.natural_relPrice`, `TwoSector.natural_relPrice_eq_div` |
| Woodford p. 204 | `n₁γ₁ + n₂γ₂ = 0` iff `α₁ = α₂`; then (2.12) | `TwoSector.gamma_weighted_sum`, `TwoSector.calvoSlope_strictAnti`, `TwoSector.gamma_weighted_sum_eq_zero_iff`, `TwoSector.printed_E8_false`, `TwoSector.aggregate_nkpc`, `TwoSector.aggregate_compatible` |
| Woodford p. 204 | `α₁ ≠ α₂` gives a trade-off | `TwoSector.incompatible_of_unequal` |
| Woodford (3.1), p. 205 | the forward solution; unique bounded solution | `Delays.nkpc_forward`, `Delays.nkpc_existsUnique` |
| Woodford fn. 63, p. 205 | quasi-acceleration plus a forecast error | `Delays.footnote_63`, `Delays.footnote_63_orthogonal` |
| Woodford p. 206 | inflation increasing in expected gaps; precedes output and peaks no later | `Delays.fwdSum`, `Delays.fwdSum_pos`, `Delays.det_forward`, `Delays.nkpc_mono`, `Delays.infl_precedes_output`, `Delays.infl_peaks_no_later` |
| Woodford (3.2), p. 208 | the delayed AS relation, derived from the delayed FOC; the NKPC is `d = 0` | `Delays.DelayedNKPC`, `Delays.delayed_from_foc`, `Links.nkpc_iff_delayed_zero` |
| Woodford p. 209 | `π` predetermined; only `E_{t−d}` matters | `Delays.delayed_predetermined`, `Delays.prices_predetermined`, `Delays.delayed_forward`, `Delays.delayed_existsUnique`, `Delays.delayed_depends_on_forecasts` |
| Woodford p. 209 | no inflation effect before `t + d`; revisions solve the IRF system | `Delays.revision_zero_before_delay`, `Delays.revision_recursion`, `Delays.revision_irf` |
| Woodford (3.3), p. 209 | the nominal-GDP response | `Delays.nomIRF`, `Delays.nomIRF_growth`, `Delays.nomIRF_shift`, `Delays.nomIRF_bounds` |
| Woodford (3.2), p. 208; Figs. 3.11–3.13 | the delayed IRF: unique; exists for every `d` and any bounded input | `Delays.DelayIRF`, `Delays.irf_unique`, `Delays.irfP`, `Delays.irf_exists`, `Delays.delayIRF_congr`, `Delays.irf_exists_delay` |
| Woodford (3.3), p. 209; Figs. 3.11–3.16 | IRFs to (3.3) exist and are unique for every `d`, `s`, with and without indexation | `Delays.irf_existsUnique_nom` |
| Fig. 3.11, p. 210 | output contracts on impact | `Delays.irfP_one_pos`, `Delays.fig_3_11_general`, `Delays.fig_3_11_contraction` |
| Fig. 3.12, p. 211 | Figure 3.9 shifted by `d`; also for expectation revisions | `Delays.shiftSeq`, `Delays.shift_solves`, `Delays.fig_3_12`, `Delays.fig_3_12_stochastic` |
| Figs. 3.12–3.13 | no output response before `d` | `Delays.delayed_output_eq_nominal` |
| Woodford (3.3), p. 209; Fig. 3.12 | `q` independent of `ε` on an event tree; Figure 3.12 without a revision hypothesis | `Delays.shockTree`, `Delays.shockSystem`, `Delays.shockTree_independent`, `Delays.treeNom`, `Delays.treeNom_diff`, `Delays.fig_3_12_tree` |
| Woodford (3.2)–(3.3), pp. 208–209 | the tree economy: an equilibrium exists and is unique | `Delays.TreeEq`, `Delays.treeEq_exists`, `Delays.treeEq_unique` |
| Fig. 3.12, p. 211 | the unique tree equilibrium has the Figure 3.12 shift property | `Delays.fig_3_12_tree_equilibrium` |
| Woodford (3.3), p. 209 | with `q ≡ 0` nominal GDP is `e · nomIRF` and bounded | `Delays.treeNom_noq`, `Delays.treeNom_noq_bounded` |
| Woodford p. 213 | Yun indexation; a vertical long-run Phillips curve | `Delays.yun_iff`, `Delays.yun_vertical` |
| Woodford (3.4)–(3.5), pp. 214–215 | the indexation rule; the price index | `Delays.indexed_law`, `Delays.indexed_relPrice`, `Delays.hasDerivAt_eq_3_5` |
| Woodford (3.6), p. 215 | the indexed AS relation; its forward form | `Delays.IndexedNKPC`, `Delays.eq_3_6_from_foc`, `Delays.eq_3_6_forward`, `Delays.eq_3_6_unique` |
| Woodford pp. 216–217, fn. 67 | the hybrid and Fuhrer–Moore forms | `Delays.eq_3_6_iff_hybrid`, `Delays.fuhrer_moore`, `Delays.hybrid_weights_sum_one_iff` |
| Woodford (3.7), p. 217 | delay plus indexation | `Delays.eq_3_7_forward`, `Delays.quasiDiff_predetermined`, `Delays.revision_index_irf` |
| Woodford (3.6), p. 215; Figs. 3.14–3.16 | one root `μ > 1/β` outside the unit circle, two inside | `Delays.cubicC`, `Delays.cubic_root_exists`, `Delays.index_factor`, `Delays.cubic_roots_location` |
| Figs. 3.14–3.16 | the indexed IRF: unique bounded solution (any `d`); existence for every `d`, `0 ≤ γ ≤ 1` | `Delays.IndexIRF`, `Delays.indexIRF_unique`, `Delays.indexIRF_exists`, `Delays.indexIRF_congr`, `Delays.indexIRF_exists_delay` |
| Fig. 3.15, pp. 217–218 | the `s = d` response is Figure 3.14 shifted by `d` | `Delays.indexIRF_shift`, `Delays.fig_3_15` |
| Woodford p. 217 | indexation and lagged nominal GDP: output contracts on impact | `Delays.p217_contraction`, `Delays.p217_contraction_general` |
| Woodford (4.1)–(4.2), pp. 221–222 | labour demand is the unique cost-minimising bundle; it delivers `H` and costs `WH` | `DixitStiglitz.labour_cost_minimisation`, `WageSetting.Labor.cost_min_iff`, `WageSetting.Labor.unitInterval_cost_minimisation`, `WageSetting.Labor.laborIndex_demand`, `WageSetting.Labor.wageBill_demand` |
| Woodford p. 222 | Calvo resetting gives the wage-index recursion; survival probability `α^k` | `WageSetting.Index.wage_index_recursion`, `WageSetting.Index.wage_recursion_lottery`, `WageSetting.Index.dist_k_step` |
| Woodford (4.3), p. 222 | the wage-setting objective is an instance of Calvo's (2.2) | `WageSetting.wageObjective`, `WageSetting.wageObjective_eq`, `WageSetting.objective_eq_resetObjective` |
| Woodford (4.4), p. 222 | the FOC; necessary and sufficient, unique maximiser when `v` is convex | `WageSetting.eq44LHS`, `WageSetting.eq44_iff_focSum`, `WageSetting.wage_isMaxOn_iff_foc`, `WageSetting.foc_of_isLocalMax` |
| Woodford (4.3)–(4.4), pp. 222–223 | (4.4) characterises the optimal wage, from primitive bounds | `WageSetting.wage_primitives`, `WageSetting.wage_isMaxOn_iff_foc_of_primitives`, `WageSetting.isMaxOn_iff_foc_of_primitives` |
| Woodford (4.5), fn. 73 | `v_h/Λ = VP` | `WageSetting.mrs_nominal_eq` |
| Woodford p. 223 | flexible wages: `w = μ_w VP`; steady state | `WageSetting.wage_flexible_iff`, `WageSetting.wage_steadyState_iff` |
| Woodford (4.6), p. 223 | the exact first-order approximation of the index recursion | `WageSetting.Index.index_tangent`, `WageSetting.Index.hasDerivAt_inflFn`, `WageSetting.Index.index_law_iff` |
| Woodford p. 223 | the type MRS; `log(h(j)/H) = −θ_w(log w(j) − log W)` | `WageSetting.hasDerivAt_log_vh`, `WageSetting.log_demand_sub` |
| Woodford (4.7), p. 223 | the exact linearisation of (4.4) | `WageSetting.hasDerivAt_focLHS_path`, `WageSetting.linear_reset_rule_iff`, `WageSetting.reset_rule_iff`, `WageSetting.eq47_of_linearisation` |
| Woodford (4.8)–(4.9), p. 224 | (4.6) + (4.7) ⇔ (4.6) + (4.8) under geometric growth; the price analogue | `StickyWages.calvo_pc_iff`, `StickyWages.reset_sum_iff_pc`, `StickyWages.eq48_eq49_iff`, `StickyWages.forwardSeries_solves_growth`, `StickyWages.eq_forwardSeries_growth` |
| Woodford (4.9), p. 224 | the price-setting objective is an instance of the generic reset problem; the FOC is necessary and sufficient | `WageSetting.priceObjective`, `WageSetting.priceObjective_eq`, `WageSetting.hasDerivAt_priceCost`, `WageSetting.priceMC_monotoneOn`, `WageSetting.price_isMaxOn_iff_foc` |
| Woodford (4.9), p. 224 | the linearised price reset rule with `ω_pθ_p` | `WageSetting.hasDerivAt_log_mc`, `WageSetting.price_reset_rule_of_linearisation` |
| Woodford p. 224 | the wage and price brackets (corrected) | `StickyWages.wage_gap_eq`, `StickyWages.price_gap_eq`, `StickyWages.printed_s_hat_iff`, `StickyWages.printed_s_hat_counterexample` |
| Woodford (4.10), pp. 224–225 | exact derivatives of `v̂` and `ψ̂`; `v̂ + ψ̂ = (ω + σ⁻¹)(Ŷ − Ŷⁿ)` | `StickyWages.hasDerivAt_logMRS`, `StickyWages.hasDerivAt_psihat`, `StickyWages.vhat_alt`, `StickyWages.vhat_add_psihat`, `StickyWages.natural_output_iff` |
| Prop 3.9, (4.11)–(4.12), p. 225 | wage and price Phillips curves; `wⁿ` is the flexible real wage; `κ_w, κ_p > 0` | `StickyWages.prop_3_9`, `StickyWages.natural_real_wage_iff`, `StickyWages.kappaW_pos`, `StickyWages.kappaP_pos` |
| Woodford (4.13)–(4.15), p. 226 | `π̄` obeys an NKPC with `κ > 0`; `κ` falls as either rigidity rises | `StickyWages.eq414`, `StickyWages.kappaBar_pos`, `StickyWages.kappaBar_strictMonoOn_xiW`, `StickyWages.xi_strictAntiOn`, `StickyWages.kappaBar_strictAntiOn_alphaW` |
| Woodford p. 226 | `α_w → 0` gives (2.12)–(2.13) with `ζ` from (1.37); `α_p → 0` gives a wage Phillips curve | `StickyWages.tendsto_kappaBar_alphaW`, `StickyWages.tendsto_weight_alphaW`, `StickyWages.kappaBar_flexible_wages_eq`, `StickyWages.tendsto_kappaBar_alphaP`, `StickyWages.tendsto_weight_alphaP`, `Links.flexible_wages_slope_eq_kappa` |
| Woodford (4.16), p. 227 | the flexible-price real-wage relation and the `log Y` equation | `StickyWages.eq412_bracket`, `StickyWages.price_bracket_eq`, `StickyWages.eq416` |
| Woodford p. 227 | the nominal-wage equation with `κ̂ = κ/(1 + ω_p)` | `StickyWages.nominal_wage_eq` |
| Woodford pp. 227, 230 | a nominal anchor: nominal spending a random walk; the wage equation as a second-order equation | `StickyWages.AnchorEq`, `StickyWages.anchorSol`, `StickyWages.anchorSol_eq`, `StickyWages.randomWalk_E`, `StickyWages.anchor_iff_secondOrder` |
| Woodford p. 227 | `w̃_k = 1 − λ^{k+1}`, unique bounded; the `E_t` response; output `(1 + ω_p)⁻¹λ^{k+1}` (corrected) | `StickyWages.WtildeEq`, `StickyWages.wtilde_unique`, `StickyWages.anchor_existsUnique`, `StickyWages.anchor_E_response`, `StickyWages.pc_iff_anchor`, `StickyWages.output_response`, `StickyWages.printed_output_response_ne` |
| Woodford (4.17), p. 228 | `κ̂ = (1 − α)(1 − αβ)/α · ζ̃`; `λ > α_w` iff `ζ̃ < 1` | `StickyWages.kappaHat_eq`, `StickyWages.lam_gt_alpha_iff` |
| Woodford p. 228 | Andersen: `ζ̃ = ω_p/(1 + ω_p) < 1`; with `ν = 0`, `ζ̃ > 1` iff `σ < 1`; `ζ = ν` | `StickyWages.andersen_wage`, `StickyWages.andersen_contract_multiplier_iff`, `StickyWages.andersen_price`, `StickyWages.linear_production` |
| Woodford pp. 229–230 | Huang–Liu: `ζ̃ = (1 + ν)/(1 + νθ_w) < 1`, `ζ = 1 + ν`; specific markets `ζ ≤ ζ̃` iff `θ_p ≥ θ_w`; (1.35) < (1.37) | `StickyWages.zetaTilde`, `StickyWages.huang_liu_tilde`, `StickyWages.huang_liu_common`, `StickyWages.huang_liu_specific_le_iff`, `StickyWages.specific_lt_common` |
| Woodford p. 229 | `ν ≥ ω_p` and `θ_w ≥ θ_p` imply `ζ̃ < ζ` (corrected condition) | `StickyWages.zetaTilde_lt_zetaCommon`, `StickyWages.printed_E15_counterexample` |
| Woodford (4.18), p. 230 | the real-wage equation; a second-order equation | `StickyWages.eq418`, `StickyWages.eq418_iff_secondOrder` |
| Woodford p. 230 | `κ_w = κ_p`: a unique bounded real wage, independent of output and policy | `StickyWages.realWage_indep_of_output`, `StickyWages.eq422` |
| Woodford (4.19)–(4.20), p. 230 | the price Phillips curve with `u_t` (with `β`) | `StickyWages.eq419`, `StickyWages.printed_eq419_iff`, `StickyWages.printed_eq419_counterexample` |
| Woodford pp. 230–231 | output as in Prop 3.6 with `κ = ξ_pω_p < ξ_p(ω + σ⁻¹)`; larger and more persistent | `StickyWages.kappa_sticky_lt_flexible`, `StickyWages.output_response_larger`, `StickyWages.lam1_strictAntiOn` |
| Woodford (4.21), p. 231 | the flexible-wage real wage; `ω > ν` (with `φ_h > 1`) | `StickyWages.eq411_bracket`, `StickyWages.eq421`, `StickyWages.omega_gt_nu`, `StickyWages.phiH_gt_one` |
| Woodford p. 231 | `α_w` can be chosen so `κ_w = κ_p`, uniquely iff `ω_p > 0` | `StickyWages.alphaW_existsUnique`, `StickyWages.alphaW_none_of_linear` |
| Woodford (4.22), pp. 231–232 | roots `0 < λ₁ < 1 < β⁻¹ < λ₂`; the unique bounded solution in the printed form | `StickyWages.lam1_pos`, `StickyWages.lam1_lt_one`, `StickyWages.inv_beta_lt_lam2`, `StickyWages.inv_beta_lam2`, `StickyWages.quad_factor`, `StickyWages.SecondOrder`, `StickyWages.secondOrder_unique`, `StickyWages.secondOrder_existsUnique`, `StickyWages.secondOrderSol_eq` |
| Woodford p. 232 | the flexible limits `λ₁ → 0`, `λ₂⁻¹ → 0` | `StickyWages.tendsto_lam1_atTop`, `StickyWages.tendsto_inv_lam2_atTop` |
| Woodford p. 232 | `log w_t − λ₁z_t → 0` uniformly; `λ₁c → 1` | `StickyWages.secondOrder_flexible_bound`, `StickyWages.tendsto_lam1_mul`, `StickyWages.tendsto_flexBound`, `StickyWages.secondOrder_flexible_limit` |
| Woodford p. 232 | the real-wage limits are (4.21) and the flexible-price relation | `StickyWages.forcing_factor`, `StickyWages.tendsto_ratio_flexible_wages`, `StickyWages.tendsto_ratio_flexible_prices`, `StickyWages.realWage_flexible_limit` |
| Woodford p. 233, fn. 77 | the real-wage response has the sign of `κ_w − κ_p` | `StickyWages.realWage_response_sign`, `StickyWages.secondOrderSol_nonneg`, `StickyWages.secondOrderSol_smul` |
| Woodford p. 233 | `w = wⁿ` solves (4.18) iff `Δlog wⁿ = βE Δlog wⁿ′`; a bounded such `wⁿ` is constant | `StickyWages.natural_real_wage_solves_iff`, `StickyWages.bounded_natural_wage_const` |
| Fig. 3.18, p. 233 | the calibration of `ξ_w` that makes `κ_w = κ_p` | `StickyWages.fig318_equal_stickiness` |
| Woodford (4.23)–(4.24), p. 234 | indexed wage and price Phillips curves | `WageSetting.indexed_profit_eq`, `StickyWages.eq423_424` |
| Woodford (4.25), p. 235 | flexible prices with `ω_p = 0`; equal indexation with `u` from (4.20) | `StickyWages.eq416_linear`, `StickyWages.eq425_flexible_prices`, `StickyWages.eq425_equal_indexation` |
| B.1, (B.1)–(B.3), p. 656 | Kimball demand minimises cost; unique | `Kimball.kimball_demand_cost_min`, `Kimball.kimball_demand_unique` |
| B.1, (B.1)–(B.3), p. 656 | with a continuum of goods | `Kimball.kimball_demand_cost_min_continuum` |
| B.1, (B.4), p. 656 | the demand exists; its elasticity is `θ(x)` | `Kimball.thetaK`, `Kimball.kimball_demand_exists`, `Kimball.kimball_demand_elasticity`, `Kimball.kimball_log_demand` |
| B.1, (B.4)–(B.5), p. 656 | `θ′(1)`, hence `ε_μ`, computed from `ψ` | `Kimball.thetaKDeriv`, `Kimball.thetaK_hasStrictDerivAt`, `Kimball.strictDerivs_of_contDiff` |
| B.1, p. 657 | the materials aggregate costs `P` per unit at symmetric prices and when a null set deviates; not in general | `Kimball.kimball_unit_cost_symmetric`, `Kimball.kimball_unit_cost_ae`, `Kimball.psiQ`, `Kimball.kimball_unit_cost_counterexample` |
| B.2, (B.7), p. 658 | value added and final demand | `Kimball.value_added_log_deviation`, `Kimball.aggregate_value_added_hasDerivAt`, `Kimball.final_demand_value_added` |
| B.2, (B.8), p. 658 | Leontief marginal cost; linearised `ŝ = (1 − μs_m)(s_yŷ + s_YŶ)` | `Kimball.leontief_marginal_cost`, `StrategicComplementarity.intermediate_input_elasticities` |
| B.2, (B.9), p. 658 | the steady state; needs `s_m < μ⁻¹` | `Kimball.steady_state_B9`, `Kimball.steady_state_needs_sm_lt`, `Kimball.steady_state_exists`, `Kimball.den_pos` |
| B.3, (B.11), pp. 659–660 | the characteristic polynomial; `A(L) = β(1 − λ₁L)(1 − λ₂L)`; Vieta | `QuadraticRoots.lagPoly`, `QuadraticRoots.lagPoly_factor`, `QuadraticRoots.lagPoly_eq_reciprocal`, `QuadraticRoots.charPoly_factor`, `QuadraticRoots.lam1_add_lam2`, `QuadraticRoots.beta_mul_sum`, `QuadraticRoots.beta_mul_prod` |
| B.3, p. 660 | the sign argument: `P(0)`, `P(1)`, `P(β⁻¹)` | `QuadraticRoots.charPoly_zero`, `QuadraticRoots.charPoly_one`, `QuadraticRoots.charPoly_inv`, `QuadraticRoots.between_roots_of_neg`, `QuadraticRoots.charPoly_pos_iff`, `QuadraticRoots.charPoly_pos_iff_outside`, `QuadraticRoots.charPoly_neg_iff` |
| B.3, p. 660 | `(1 − λ₁)(1 − λ₂⁻¹) = ξλ₁` (corrected) | `QuadraticRoots.one_sub_mul_one_sub_inv`, `QuadraticRoots.c_mul_lam1`, `QuadraticRoots.coeff_pos_lt_one`, `QuadraticRoots.calvo_coeff_identity` |
| B.3, p. 660 | the printed product is negative and the printed step false | `QuadraticRoots.printed_E5_neg`, `QuadraticRoots.printed_E5_ne`, `QuadraticRoots.printed_E5_step_ne`, `QuadraticRoots.printed_E5_counterexample` |
| B.3, p. 659 | the recursive reset-price equation (corrected sign) | `Calvo.recursive_reset_price`, `Calvo.recursive_iff_B13`, `Calvo.printed_E4_fails` |
| B.3, (B.13)–(B.14), pp. 659–660 | derived from (2.8) for any solution in the class | `Calvo.B13_iff_B14`, `Calvo.solution_B13`, `Calvo.solution_B14`, `Calvo.zbar`, `Calvo.zbar_rec` |
| B.3, (B.15), p. 660 | `z̄` is difference-stationary | `Calvo.zbar_props`, `Calvo.fwd_diffStationary`, `Calvo.mcost_diffStationary`, `Calvo.costTerm_diffStationary` |
| B.3, p. 660 | the bound on `log S` | `Calvo.BoundedIncr`, `Calvo.diffStationary_of_boundedIncr`, `Calvo.fwd_boundedIncr` |
| B.3, pp. 660–661 | forward sums of difference-stationary processes; `E_t` and dominated series | `Calvo.fwd_decomp`, `Calvo.summable_fwd`, `Calvo.fwd_rec`, `Calvo.E_fwd_succ`, `Calvo.fwd_adapted`, `ForwardSolution.E_tsum_dom` |
| B.3, p. 661 | the growth argument for uniqueness | `Calvo.forward_unique_growth` |
| B.3, p. 661 | the explosive solutions | `Calvo.hpath`, `Calvo.root_calvo_identity`, `Calvo.root_reset_identity`, `Calvo.hasSum_root_path`, `Calvo.exists_lin_lt_pow` |
| B.4, p. 662 | the interchange of sums, with absolute convergence | `NKPC.summable_double`, `NKPC.interchange_sums` |
| B.4, (B.17), p. 662 | the recursive form via the tower property | `NKPC.resetForcing`, `NKPC.resetGap_rec`, `NKPC.resetForcing_adapted`, `NKPC.resetForcing_bounded`, `NKPC.E_price_change` |
| B.5, (B.20), p. 663 | `κ = β(1 − λ₁)(λ₂ − 1)`; `A(L) = β(1 − λ₁L)(1 − λ₂L)` | `Persistence.kappa_eq`, `Persistence.kappa_div_eq`, `Persistence.lagPoly_factor` |
| B.5, (B.21), p. 663 | the lag form and its homogeneous solutions | `Persistence.prev`, `Persistence.irfEq_ext`, `Persistence.hom`, `Persistence.hom_irfEq`, `Persistence.hom_zero_ne` |
| B.5, pp. 663–664 | `z_k = β⁻¹λ₂⁻¹κ∑λ₂^{−j} = 1 − λ₁` | `Persistence.seq_forward_hasSum`, `Persistence.irf_forward_hasSum`, `Persistence.forward_sum_one`, `Persistence.forward_value_eq`, `Persistence.z_eq_of_bounded` |
| B.5, (B.18), p. 664 | `p̃_k = λ₁p̃_{k−1} + 1 − λ₁` | `Persistence.first_order_solution`, `Persistence.backward_sum` |
| B.6, (B.23), p. 665 | `Ỹ_k = 1 − ρ^{k+1}` (corrected) | `SpendingGrowth.Ytil`, `SpendingGrowth.prevZ_Ytil`, `SpendingGrowth.Ytil_eq_sum`, `SpendingGrowth.printed_B23_false` |
| B.6, (B.24)–(B.25), p. 665 | the price equation ⇔ the output equation; the `A(L)Ỹ` display | `SpendingGrowth.OutEq`, `SpendingGrowth.irfEq_Ytil_iff`, `SpendingGrowth.lag_Ytil` |
| B.6, p. 665 | the forward sum is `Cρ^k`, `C > 0` | `SpendingGrowth.B6_forward_hasSum`, `SpendingGrowth.B6_value`, `SpendingGrowth.Cc`, `SpendingGrowth.Cc_pos` |
| B.6, (B.26), p. 665 | `(1 − ρL)(1 − λ₁L)ỹ_{k+1} = 0`, `ỹ₀ = C` | `SpendingGrowth.B26` |
| B.6, (B.22), p. 666 | the general solution; `A₁ = λC/(λ − ρ)`, `A₂ = ρC/(ρ − λ)` | `SpendingGrowth.general_solution`, `SpendingGrowth.y37_closed`, `SpendingGrowth.general_solution_eq_B22` |
| B.6, p. 666 | the sign pattern; the positive term dominates | `SpendingGrowth.coeff_signs`, `SpendingGrowth.hsum_step` |
| B.7, (B.28), p. 667 | the profit gradient (corrected) | `TwoSector.profit_gradient`, `TwoSector.printed_B28_not_derivative` |
| B.7, (B.29), p. 667 | log-linear sector demand; per-good normalisation | `TwoSector.log_sectorDemand`, `TwoSector.sectorDemand_linear`, `TwoSector.revenue_per_good`, `TwoSector.logdev_normalisation` |
| B.7, (B.30), p. 667 | real marginal cost as an exact derivative (corrected) | `TwoSector.mcDeriv`, `TwoSector.hasDerivAt_mc_path`, `TwoSector.realMC_B30`, `TwoSector.printed_B30_fails`, `TwoSector.printed_display_iff` |
| B.7, (B.31)–(B.32), p. 668 | the linearised FOC, perfect foresight | `TwoSector.bracket_hasDerivAt`, `TwoSector.summand_hasDerivAt`, `TwoSector.linearised_FOC`, `TwoSector.linearised_FOC_B32`, `TwoSector.firm_mc`, `TwoSector.foc_summand_rewrite` |
| B.7, (B.31)–(B.32), p. 668 | under uncertainty; `E_t` outside the sum | `TwoSector.E_tsum_of_dominated`, `TwoSector.E_tsum_polyGeom`, `TwoSector.linFOC_iff_E_outside`, `TwoSector.linearised_FOC_uncertain`, `TwoSector.linearised_FOC_B32_uncertain` |
| B.7, (B.32), p. 668 | the relative reset-price form | `TwoSector.tailSeries`, `TwoSector.tailSeries_eq`, `TwoSector.LinFOC`, `TwoSector.hasSum_cumulated`, `TwoSector.linFOC_iff` |
| B.7, (B.33), p. 668 | the sectoral inflation equation | `TwoSector.relative_law_iff_nkpc`, `TwoSector.sector_inflation` |
| B.7, p. 669 | the `ŝ_j − p̂_j` display | `TwoSector.realMC_gap` |
