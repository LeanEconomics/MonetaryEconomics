# Monetarism in Lean

This is the `Cochrane/Monetarism/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Chapter 19, "Monetarism" (pp. 433–464), together with the precise claims
of Chapter 11 on open-market operations and elastic currency (pp. 315–318), the helicopter
arithmetic of §14.1 (p. 342), and Online Appendix §1.6 (pp. 567–569), Chapter 3, "Pruning
multiple monetary equilibria" (§§3.1–3.2.4, pp. 612–632), and Chapter 4, "Money in continuous
time" (pp. 635–641). The present-value and Cagan results hold for an arbitrary expectation
operator, so they cover perfect foresight and genuine uncertainty. The nonlinear phase dynamics
are perfect-foresight, as in the book. The household first-order conditions are derived by
optimisation, under perfect foresight, on a finite event tree and on a genuine probability space
whose information grows forever, there without bounds on prices or plans. Continuous time is
deterministic, except the `E_td(·)` forms, the product step and the chain (1.31)–(1.34) of Online
Appendix §1.6 (`TidyR6StochasticDrift`, `TidyR7ProductStep`, `TidyR7MonetarismModel`,
`TidyR7MonetarismValuation`). The library contains **2062 theorems**, including the shared core; 578 of them are in the fourteen
chapter modules, 175 in the six measure-theoretic household modules, 195 in the four `TidyR5…`
modules, 108 of these in a verbatim copy of the general Blanchard–Kahn theorem (`TidyR5BK`), 136
in the eleven `TidyR6Household…` modules, 142 in the twelve further `TidyR6…` modules: 27 on
Woodford's convexity, Taylor-rule and Obstfeld–Rogoff sections, 54 on active fiscal policy under
uncertainty, 49 on the Hamiltonian conditions and 12 on the `E_td(·)` forms, 110 in the four
`TidyR7Stieltjes…` modules, deterministic Riemann–Stieltjes tools for the product step of (1.32),
28 in `TidyR7JumpSums`, the same tools for jumping integrators, 154 in the six
`TidyR7CondDominated`/`TidyR7ProductStep…` modules that prove that product step, for continuous
and for jumping bonds, 220 in the nine `TidyR7Monetarism…` modules that prove the chain
(1.31) → (1.32) → (1.33)–(1.34) under uncertainty, with continuous and with jumping money, and
108 in the four `TidyR7Brownian…` modules, a Brownian motion on `[0, ∞)` and its martingale
tools, 66 of them copied from the Meyn–Tweedie project.

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises. Survey codes E13–E23 refer to the
survey of Chapters 11–19 (`notes/survey_cochrane_ch11-19.md`), as do V1–V5 and V11 (the precise
claims of the verbal chapters) and NI-7.

Headline results, in the namespace `Cochrane.Monetarism`:
* **Regimes, NI-7 and double passive policy.** Given bond pricing and the money transversality
  condition, the two forms (19.2) and (19.3) of the valuation equation are equivalent
  (`Regimes.eq192_iff_eq193`), and (19.2) holds iff the bond transversality condition does
  (`Regimes.flow_pv_iff_tvc`). Every equilibrium of `MV = Py` and the valuation equation is the
  unique equilibrium of an active-money/passive-fiscal regime and of an active-fiscal/passive-money
  regime with the same observables (NI-7, `Regimes.ni7`). With both policies passive every positive
  price level is an equilibrium (`Regimes.double_passive`). With both active an equilibrium exists
  iff they are coordinated (`Regimes.double_active_iff`).
* **Chapter 11 and the helicopter.** With `i = i^m` an open-market swap leaves the price level
  unchanged (V1, `Regimes.omo_irrelevant`). Below the Laffer peak, raising money growth lowers the
  initial price level; beyond it, raising money growth raises it (V2, `Seigniorage.v2_cagan`). A
  unique interest spread clears money demand (V3, `Regimes.spread_existsUnique`). Both readings of
  an open-market operation describe the same event (V4, `Regimes.omo_equivalence`). Under elastic
  currency any price level clears the money market (V5, `Regimes.elastic_currency`). The
  helicopter drop of p. 342 raises the price level by exactly `1/101` in fiscal theory and doubles
  it in monetarism (`Regimes.helicopter_fiscal`, `Regimes.helicopter_monetarist`).
* **Cagan with rational expectations.** The equilibria of (19.5) with constant money are exactly
  the family `p_t − p̄ = θᵗ(p_0 − p̄) + ∑θ^{t−j}δ_j` with `E_tδ_{t+1} = 0`
  (`CaganRE.caganFamily_solves`, `CaganRE.eq_caganFamily`). All but the steady state explode
  (`CaganRE.pf_explodes`, `CaganRE.bounded_iff_steady`). There are uncountably many
  perfect-foresight paths and sunspots under genuine uncertainty
  (`CaganRE.pf_solutions_uncountable`, `CaganRE.coin_sunspot_ne_steady`). The valuation equation
  selects exactly one path (`CaganRE.fiscal_path_existsUnique`), and the selected path is
  explosive unless `B_{−1} = e^{p̄}∑βʲs_j` (`CaganRE.fiscal_path_bounded_iff`).
* **Money in utility.** The first-order conditions (19.13)–(19.14) are derived from the time-0
  problem of footnote 1 by cost-neutral perturbations, under perfect foresight and on a finite
  event tree, with sufficiency under concavity (`MoneyInUtility.foc_1913_1914`,
  `MoneyInUtility.FootnoteTree.tree_foc_1913_1914`,
  `MoneyInUtility.FootnoteTree.tree_optimal_of_foc`).
  The knownness of `Λ_t/P_t` and `P_t/u_c(t)` follows from adaptedness on any state space
  (`MoneyInUtility.known_div`, `MoneyInUtility.value_of_money_limit_adapted`). The value of a
  dollar is the present value of its liquidity dividends (`MoneyInUtility.value_of_money_limit`).
  Figure 19.1 is certified: `5.52 < x̄ < 5.53`, the slope at `x̄` is exactly `47/25`, and the pole
  is at `x = 10` (`MoneyInUtility.fig191_xbar_bounds`, `MoneyInUtility.fig191_slope`,
  `MoneyInUtility.fig191_pole`). The zero-rate steady state attracts iff `1 + µ > β`, not
  `1 + µ > 1/β` (E13, `MoneyInUtility.e13_corrected`). The calibration of p. 444, `θ` of order
  `0.01`, holds only for `γ = 1` (`MoneyInUtility.calib_ten_gamma_two`).
* **Money-targeting dynamics.** Woodford's global analysis of monetary targeting is restated from
  the Woodford Chapter 2 project, and (19.18) is its separable map
  (`MoneyTargetingDynamics.miuPath_iff_sepPath`). In the power example the inflationary steady
  state repels (`MoneyTargetingDynamics.power_steady_repelling`). Every path below it converges to
  the deflationary steady state with `P_{t+1}/P_t → β`
  (`MoneyTargetingDynamics.power_deflation_orbit`,
  `MoneyTargetingDynamics.power_deflation_inflation`). Every path above it leaves the domain in
  finite time (`MoneyTargetingDynamics.power_inflation_exits`). Woodford's remaining sections are
  restated too: his convexity claim fails for (19.18) itself (E7,
  `TidyR6WoodfordSections.e7_convexity_fails`, `TidyR6WoodfordSections.e7_miuPath_iff`), his
  Taylor-rule transversality argument holds with the corrected inequality (E4,
  `TidyR6WoodfordSections.e4_corrected_inequality`,
  `TidyR6WoodfordSections.fig24_deflations_violate_tvc`), and under Obstfeld and Rogoff's
  condition (4.10) no path of (19.18) has real balances below the steady state
  (`TidyR6WoodfordSections.or_miu_no_path_below`).
* **Unpleasant arithmetic.** With fixed surpluses the present value of seigniorage is fixed, so
  lower money growth now forces higher money growth and inflation later
  (`UnpleasantArithmetic.unpleasant_money_growth`). With nominal debt a fall in the present value
  of surpluses raises the price level with no money at all
  (`UnpleasantArithmetic.nominal_debt_price_anti`).
* **Seigniorage.** Revenue is maximal where the velocity elasticity equals `π/(π + g)`, which is
  one only when `g = 0` (E16, `Seigniorage.revenue_foc_iff`, `Seigniorage.e16_unit_iff`). In the
  Cagan example the unique peak is at `π = 1/a`; above it there is no steady state, below it there
  are two (`Seigniorage.cagan_revenue_lt`, `Seigniorage.no_steady_state_above_max`,
  `Seigniorage.two_steady_states`). Baumol–Tobin gives elasticities of one half
  (`Seigniorage.bt_interest_elasticity`, `Seigniorage.bt_income_elasticity`). A 40% price rise
  devalues nominal debt by 28.6% (E23, `Seigniorage.e23_real_loss`).
* **Pruning deflations.** Along a deflation the transversality condition fails iff `µ ≥ 0`,
  including `µ = 0` (E17, `PruningDeflation.tvc_tendsto_zero_iff`, `PruningDeflation.tvc_mu_zero`).
  For `β < 1 + µ < 1` the deflations are a continuum of equilibria, and for `1 + µ ≤ β` there are
  none (`PruningDeflation.deflation_continuum`, `PruningDeflation.no_deflation_of_le_beta`). E13
  and E17 are one condition (`Links.e13_iff_e17`). With no money demand the price level is
  determinate (`PruningDeflation.price_level_determined`).
* **Pruning inflations.** Paths below the steady state explode in finite time
  (`PruningInflation.finite_time_explosion`). The inflationary equilibria, which demonetise at a
  finite date, are countable and are completely classified
  (`PruningInflation.eqm_initial_iff`, `PruningInflation.inflationary_initial_countable`). With the
  modified utility of p. 620 there is instead a continuum that never explodes
  (`PruningInflation.new_inflationary_continuum`).
* **Obstfeld–Rogoff.** The Figure 3.2 caption should read `v′(m) = m^{−1/2}` (E18,
  `ObstfeldRogoff.e18_no_steady_state`, `ObstfeldRogoff.e18_correct_v`). The redemption dispute is
  resolved precisely. Obstfeld and Rogoff's finite-price theorem holds
  (`ObstfeldRogoff.or_no_hyperinflation`). With a one-time tender of the money carried out of `T`,
  Cochrane's demonetised path is a Walrasian equilibrium
  (`ObstfeldRogoff.cochrane_household_optimal`, `ObstfeldRogoff.fig32_cochrane_optimal`). With a
  standing offer that also redeems dollars bought at a zero value, no household optimum exists
  (`ObstfeldRogoff.standing_redemption_no_optimum`).
* **Nonseparable utility.** The Obstfeld (1984) phase diagram cuts from above iff `b > 1`, but it
  is stable iff `b > 1 + i/2` (E19, `Nonseparable.obs_cuts_from_above_iff`,
  `Nonseparable.obs_stable_iff`, `Nonseparable.e19_counterexample`). The printed partial
  derivatives have sign typos (`Nonseparable.obs_printed_typo`).
* **Cash in advance.** The stochastic Euler equation (19.31) and the bond price (19.32) are derived
  from household optimality on a finite event tree (`CashInAdvance.TreeEuler.sdf_eq`,
  `CashInAdvance.TreeEuler.bond_price_from_optimality`). (19.29) needs the money transversality
  condition (`CashInAdvance.Stochastic.pv_19_29_needs_money_tvc`). (19.38) is corrected to
  `(B_{t−1} + M_{t−1})/P_t` (`CashInAdvance.PF.frictionless_valuation`,
  `CashInAdvance.PF.printed_19_38_counterexample`). The nominal rate is non-negative iff `Q ≤ 1`
  (E14, `CashInAdvance.MoneyDemand.Q_le_one_iff`), and `Q = β` only with a constant price level
  (E15, `CashInAdvance.PF.bondPrice_eq_beta_iff`). For `V ≠ 1` the constraint drives a wedge into
  asset pricing (`CashInAdvance.MoneyDemand.binding_cost_wedge`,
  `CashInAdvance.Euler.sdf_wedge`), and on a probability space the printed (19.32) fails for every
  `V ≠ 1` (`CashInAdvanceMeasure.printed_1932_counterexample`). The boundary between the
  cash-in-advance and money-in-utility deflations is `1 + µ = β`
  (`Links.cia_boundary_deflation`). Active fiscal policy determines the price level across all
  paths, late switches to the zero bound and partial deflations included, iff initial nominal
  liabilities are nonnegative, `B_{−1} + M_{−1} ≥ 0`; otherwise a zero-rate deflation survives
  (`TidyR5ActiveFiscal.active_fiscal_unique_iff`, `TidyR5ActiveFiscal.active_fiscal_price_unique`,
  `TidyR5ActiveFiscal.active_fiscal_two_equilibria`).
* **Active fiscal policy under uncertainty.** With random, time-varying money and an arbitrary
  surplus process, for every `ExpectationSystem` with the pull-out property and full support (every
  finite event tree) and on a genuine probability space, every equilibrium has the standard price
  level `P = MV/y` once `B_{−1} + M_{−1} ≥ 0`, the standard valuation holds, and
  `B_{−1} + M_{−1} > 0` or `q_0 < 1` (`TidyR6ActiveFiscalTree.stoch_price_unique`,
  `TidyR6ActiveFiscalMeasure.meas_price_unique`). If the standard equilibrium exists it is the
  only one, prices and bonds (`TidyR6ActiveFiscalTree.unique_of_standard`,
  `TidyR6ActiveFiscalMeasure.meas_unique_of_standard`,
  `TidyR6ActiveFiscalMeasureExist.meas_bonds_unique`). It exists iff the surplus is coordinated
  with money (`TidyR6ActiveFiscalExist.std_exists_iff`), so coordination holds iff the unique
  equilibrium is the standard one (`TidyR6ActiveFiscalExist.std_existsUnique_iff`); on a
  probability space this is proved for equilibria with bounded real debt
  (`TidyR6ActiveFiscalMeasureExist.meas_std_exists_iff`), and an uncoordinated surplus supports a
  mean-zero debt bubble under the unconditional transversality condition
  (`TidyR6ActiveFiscalBubble.bubble_not_coordinated`). Each hypothesis is needed: the proviso
  (`TidyR6ActiveFiscalTree.pf_two_equilibria`), the pinning condition
  (`TidyR6ActiveFiscalTree.pin_needed`) and coordination, without which a coin-flip surplus shock
  leaves no standard equilibrium (`TidyR6ActiveFiscalTree.coin_no_standard_equilibrium`).
* **Continuous time.** The present-value budget of Online Appendix Chapter 4 is the present-value
  form of the flow constraint (`ContinuousTime.pv_budget_iff`), and the first-order conditions
  follow by the chain rule (`ContinuousTime.foc_4_1`, `ContinuousTime.foc_4_2`). The CES limits
  are corrected (E20). (4.6) holds only for the normalised aggregator, and with fixed `α` the
  `θ → ∞` limit is `min(c, m)` (`ContinuousTime.ces_norm_limit`, `ContinuousTime.ces_limit_min`).
  The printed `α = 1/V` holds only for `α = 1` (`ContinuousTime.alpha_eq_inv_V_iff`). The IS curve
  with money is stated exactly, restoring the dropped `−δσ` (E21, `ContinuousTime.is_curve_exact`,
  `ContinuousTime.E21_steady_state`). The valuation equations of Online Appendix §1.6 are restated
  (`ContinuousTime.money_interest_iff`). The Hamiltonian conditions (4.16)–(4.17) are necessary
  and sufficient for the book's problem with concave utilities: the costate equation by du
  Bois-Reymond, without assuming consumption differentiable (`TidyR6Pontryagin.costate_necessary`),
  the transversality condition under Kamihigashi's scaling condition
  (`TidyR6Pontryagin.tvc_necessary`), and sufficiency (`TidyR6Pontryagin.optimal_of_costate`,
  `TidyR6Pontryagin.optimal_iff`); with piecewise-continuous consumption the costate is continuous
  and equals `u′(c)` off the jumps (`TidyR6PontryaginPC.pontryagin_pc`,
  `TidyR6PontryaginPCSuff.optimal_iff_pc`). Some condition is needed for the transversality
  condition: at the optimum of Halkin's (1974) problem it fails for every costate
  (`TidyR6Halkin.halkin_no_tvc`). The `E_td(·)` forms (1.32)–(1.34) of Online Appendix §1.6 hold
  exactly on a `Δ`-grid (`TidyR6StochasticDrift.incr_1_32`, `TidyR6StochasticDrift.incr_1_34`); in
  continuous time, with `E_tdX = a dt` defined as the martingale property of `X − ∫a`, valuation
  holds iff the transversality condition does (`TidyR6StochasticDrift.valuation_iff_tvc`), and
  (1.32) holds for finite-variation discount factors (`TidyR6StochasticDrift.drift_1_32_fv`).
  The whole chain (1.31) → (1.32) → (1.33)–(1.34) is also proved under uncertainty with `Λ/P` a
  finite-variation part plus a càdlàg martingale (news, jumps allowed), adapted bonds and money
  with continuous bounded-variation paths and a general `i^m`, and with money and bonds that jump
  together with `Λ/P` (see the bullets on the §1.6 product step and chain below).
* **Pathwise Riemann–Stieltjes tools for the §1.6 product step.** The integral `∫_a^b f dg` is
  the integral against Mathlib's Lebesgue–Stieltjes measure of `g` frozen outside `[a, b]`
  (`TidyR7StieltjesIntegral.rsInt`), with total mass `g(b) − g(a)` and the jumps of `g` as atoms
  (`TidyR7StieltjesIntegral.stMeasure_Icc`, `TidyR7StieltjesIntegral.stMeasure_singleton_interior`).
  Left-point sums converge to it along any partitions with mesh → 0, for continuous `f` and `g`
  of bounded variation (`TidyR7StieltjesSums.tendsto_rsSum_of_continuousOn`) and for càdlàg `f`
  and continuous `g` of bounded variation (`TidyR7StieltjesSums.tendsto_rsSum_of_isCadlag`); in
  the second case the cross sum `Σ ΔfΔg` tends to zero (`TidyR7StieltjesSums.tendsto_crossSum_zero`),
  which fails without continuity of `g` (`TidyR7StieltjesSums.not_tendsto_crossSum_heaviside`).
  With the exact partition identity for products (`TidyR7StieltjesCalculus.prod_partition_identity`)
  this gives integration by parts (`TidyR7StieltjesCalculus.integration_by_parts_of_isCadlag`).
  For random paths the integral and the variation are measurable in `ω`
  (`TidyR7StieltjesCalculus.measurable_rsInt`, `TidyR7StieltjesVariation.measurable_eVariationOn`).
* **The §1.6 product step (1.32), in expectation form, without a stochastic integral.** For `B`
  adapted with continuous bounded-variation paths and `Λ/P = A + M` (`A` càdlàg of bounded
  variation, `M` a càdlàg martingale, under domination conditions),
  `E_s[B_tX_t − B_sX_s] = E_s[∫_s^t X dB] + E_s[∫_s^t B dA]` almost surely
  (`TidyR7ProductStep.ProductStepData.product_step`). The proof takes conditional expectations of
  the exact partition identity (`TidyR7ProductStep.pathwise_identity`), in which the martingale sum
  has `E_s[Σ B_iΔM_i] = 0` at every partition (`TidyR7ProductStep.ProductStepData.condExp_sumBM_zero`),
  and passes the pathwise limits under `E_s` by an almost-sure conditional dominated convergence
  (`TidyR7CondDominated.ae_tendsto_condExp_of_dominated`). The expected-increment integral
  `B·E_s d(Λ/P) := lim E_s[Σ B_iΔ(Λ/P)_i]` exists, is unique and equals `E_s[∫B dA]`
  (`TidyR7ProductStep.product_step_expIncr`), giving (1.32) in the book's notation
  (`TidyR7ProductStep.product_step_1_32`); with `C¹` paths it is `E_t d(Λ/P) = −i(Λ/P)dt` and agrees
  with `TidyR6StochasticDrift.drift_1_32_fv` (`TidyR7ProductStepCases.product_step_1_32_C1`,
  `TidyR7ProductStepCases.drift_1_32_link`). On a fair coin revealed at time 1 with random bonds
  and a nonzero martingale part both sides are computed, `1 = 1 + 0`
  (`TidyR7ProductStepCoin.coin_headline`), and adaptedness of `B` cannot be dropped
  (`TidyR7ProductStepCoin.coin_anticipating_fails`). Bonds that jump together with `Λ/P` need a
  third term, the jump covariation, still without a stochastic integral: for `B` adapted, càdlàg
  and of bounded variation, `E_s[B_tX_t − B_sX_s] = E_s[∫ X_− dB] + E_s[∫ B_− dA] +
  E_s[Σ_{s<u≤t} ΔX_uΔB_u]` (`TidyR7ProductStepJump.JumpStepData.jump_step`), or in two terms with
  the Lebesgue–Stieltjes integral of the current `X`, `E_s[∫ X dB] + E_s[∫ B_− dA]`
  (`TidyR7ProductStepJump.JumpStepData.jump_step_ls`). The book's two-term step, read as limits of
  left-point sums, holds iff the expected jump covariation vanishes
  (`TidyR7ProductStepJump.JumpStepData.book_step_iff`), and for continuous `B` the corrected step
  is the one above (`TidyR7ProductStepJump.JumpStepData.jump_step_recovers_product_step`). The
  tools are the limits `Σ f(t_i)Δg_i → ∫ f_− dg` and `Σ ΔfΔg → Σ_u Δf_uΔg_u` for càdlàg
  bounded-variation `g` (`TidyR7JumpSums.tendsto_rsSum_leftLim`,
  `TidyR7JumpSums.tendsto_crossSum_jumpSum`). On the coin, bonds jumping with the news break the
  left-point reading, `1 ≠ 0` (`TidyR7ProductStepJumpCoin.jump_book_fails`), and bonds jumping with
  the drift part break the Lebesgue–Stieltjes reading, `1 ≠ 1 + 1`
  (`TidyR7ProductStepJumpCoin.jumpA_ls_fails`).
* **The §1.6 chain (1.31) → (1.32) → (1.33)–(1.34) under uncertainty.** In
  `TidyR7MonetarismModel.MonetaryModel`, `Λ, P > 0` are adapted, `Λ/P = A + N` with `N` a càdlàg
  martingale and `dA = −i(Λ/P) dt`, bonds and money are adapted, money has continuous
  bounded-variation paths, and the flow (1.31) holds path by path. Then (1.32) holds integrated,
  `E_s[n_tB_t − n_sB_s] = −E_s[∫_s^t Λs dr + ∫_s^t n dM]` with `n = Λ/P`
  (`TidyR7MonetarismModel.MonetaryModel.incr_1_32`), with interest on money
  (`TidyR7MonetarismModel.MonetaryModel.incr_1_32_general`), and so does the line before (1.34),
  `E_t d(Λ(M + B)/P) = −Λ(s + (i − i^m)M/P) dt` (`TidyR7MonetarismModel.MonetaryModel.incr_1_34`).
  Integrating to infinity, valuation holds iff the transversality condition does: in the limit
  form `lim_k E_s∫_s^{T_k} = n_sB_s`, with no convergence hypothesis
  (`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_seq`), and in the printed forms
  `B_s/P_s = E_s∫_s^∞ (Λ_τ/Λ_s)(s_τ dτ + dM_τ/P_τ)` and
  `(M_s + B_s)/P_s = E_s∫_s^∞ (Λ_τ/Λ_s)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ` when the flows converge
  dominatedly (`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_book`,
  `TidyR7MonetarismValuation.MonetaryModel.valuation_1_34_book`). On a fair coin with news in
  `Λ/P` and random bonds, money and surplus both sides of (1.32) are `1/2`
  (`TidyR7MonetarismCoin.coin_1_32`); on `[0, ∞)` with news and a positive rate (1.33) and (1.34)
  hold as printed (`TidyR7MonetarismCoinInf.inf_1_33_book`). The printed `E_t∫_t^∞` can be
  undefined while the limit form holds (`TidyR7MonetarismCoin.imp_headline`), and even when the
  pathwise limit exists the literal equation can fail without domination or `L¹` convergence
  (`TidyR7MonetarismUI.ui_headline`). The `C¹`, deterministic and `Δ`-grid forms are recovered
  (`TidyR7MonetarismLinks.incr_1_32_C1`, `TidyR7MonetarismLinks.money_printing_recovered`,
  `TidyR7MonetarismLinks.grid_1_32_rate`). When money jumps at news dates and bonds jump
  opposite to it, `ΔB = −ΔM`, with `B + M` continuous (`TidyR7MonetarismJump.JumpMonetaryModel`),
  line 3 of (1.32) and (1.33) hold verbatim with `∫ n dM` the Lebesgue–Stieltjes integral of the
  post-jump `n` (`TidyR7MonetarismJump.JumpMonetaryModel.incr_1_32_jump`,
  `TidyR7MonetarismJump.JumpMonetaryModel.valuation_1_33_jump`); with the pre-jump reading
  `∫ n_− dM` the extra term `−E_s[Σ ΔnΔM]` appears
  (`TidyR7MonetarismJump.JumpMonetaryModel.incr_1_32_jump_left`), the printed middle line holds iff
  `E_s[Σ Δ(Λ/P)ΔM] = 0` (`TidyR7MonetarismJump.JumpMonetaryModel.middle_1_32_book_iff`), and
  (1.34) is unchanged (`TidyR7MonetarismJump.JumpMonetaryModel.valuation_1_34_jump`). In an
  open-market operation at the news date the pre-jump line 3 gives `0 ≠ −1/2`
  (`TidyR7MonetarismJumpCoin.jcoin_1_32_left_fails`).
* **Brownian infrastructure for (1.32) with diffusive bonds.** Mathlib defines Brownian motion
  (`ProbabilityTheory.IsBrownianReal`) but proves no existence theorem; a Brownian motion on
  `[0, ∞)` exists (`TidyR7BrownianExist.exists_isBrownianReal`). It is the time change
  `W(t) = (1+t)B(t/(1+t)) − tB(1)` (`TidyR7BrownianExist.bmPath`) of the Lévy–Ciesielski motion `B`
  on `[0,1]`, whose construction (`TidyR7BrownianSchauder`, `TidyR7BrownianUnit`) is copied from the
  Meyn–Tweedie `LimitTheorems` project of LeanDynamicProgramming; every path is continuous
  (`TidyR7BrownianExist.isBrownianReal_bmPath`). For any pre-Brownian motion with measurable values,
  the increment `W t − W s` is independent of the natural filtration at `s`
  (`TidyR7BrownianTools.indep_increment_bmFiltration`), `W` and `W t² − t` are martingales
  (`TidyR7BrownianTools.martingale_bm`, `TidyR7BrownianTools.martingale_bm_sq_sub`), and
  `E[(W t − W s)⁴] = 3(t − s)²` (`TidyR7BrownianTools.integral_increment_pow_four`); `W` carries over
  to the index `ℝ` of the product step (`TidyR7BrownianTools.bmReal`). The stochastic integral is
  not yet built.
* **Links: explosions, the tree problem and Galí's money rule.** The finite-time exit of
  Figure 19.1 and the finite-time explosion of A3 (3.3) are each derived from the other
  (`LinksTidy.exits_iff_explosion`). The cash-in-advance tree problem with `V = 1` is the
  footnote-1 tree problem with `ι = 0` (`LinksTidy.TreeBridge.isOptimal_iff_tOptimal`), so the
  Euler results pass both ways: the tree Euler equation needs no positivity of the state prices
  (`LinksTidy.TreeBridge.tree_euler_necessary_general`), and the full cash-in-advance sufficiency
  theorem follows from the footnote-tree one by averaging over information cells
  (`LinksTidy.TreeBridge.euler_sufficient_of_tree_optimal_of_foc`). Galí's (2015) money-rule
  system (34) with a zero output gap is the flexible-price Cagan model plus `π_t = βE_tπ_{t+1}`
  (`LinksTidy.GaliMoneyRule.system34_zero_gap_iff`), whose money block is (19.5) with `a = η`
  (`LinksTidy.GaliMoneyRule.flexBlock_iff_cagan`). The flexible-price model is determinate in
  Galí's sense with bounded money growth (`LinksTidy.GaliMoneyRule.flex_existsUnique`), and
  Galí's boundedness requirement is exactly Cochrane's selection of the steady state
  (`LinksTidy.GaliMoneyRule.cagan_realBalances_bounded_iff`). With sticky prices the
  flexible-price path is not a zero-gap equilibrium
  (`LinksTidy.GaliMoneyRule.flex_not_zero_gap_eq34`). Galí's sticky-price determinacy theorem
  holds for the same equilibrium notion: for `σ > 0`, `η ≥ 0`, `κ > 0`, `0 < β ≤ 1`, (34) has
  exactly one bounded adapted equilibrium in every `ExpectationSystem`
  (`TidyR5MoneyRule.system34_existsUnique`, `TidyR5MoneyRule.system34_and_flex_existsUnique`),
  proved from Galí's root count (`TidyR5MoneyRule.AM_root_location`) and the general
  Blanchard–Kahn theorem (`TidyR5BK.GeneralBK.determinate_of`). As `κ → ∞` the sticky-price
  equilibria converge to the flexible-price one uniformly over dates and states, at rate
  `O(1/κ)` (`TidyR5KappaLimit.kappa_limit`, `TidyR5KappaLimit.sticky_flex_bound`); the limit is
  attained at a finite `κ` iff `π^f_t = βE_tπ^f_{t+1}` (`TidyR5KappaLimit.sticky_eq_flex_iff`),
  never in the `β ≠ 1` example (`TidyR5KappaLimit.gap_never_zero`).
* **Genuine probability models.** On a probability space with a filtration, where `E_t` is
  Mathlib's conditional expectation and every budget constraint holds almost surely
  (`ExpectationsMeasure.MeasExpectationSystem`), the Chapter 19 household problem with complete
  contingent-claim markets is posed and solved (`HouseholdMeasure.Optimal`). Bounded budget-neutral
  deviations give the first-order condition (`HouseholdMeasure.pair_foc`), and concavity with the
  transversality condition gives sufficiency (`HouseholdMeasure.optimal_of_supergradient`). In
  money in utility, (19.13)–(19.16) and the value-of-money recursion are derived from optimality
  (`MoneyInUtilityMeasure.foc_1913`, `MoneyInUtilityMeasure.foc_1914`,
  `MoneyInUtilityMeasure.money_demand_1916`, `MoneyInUtilityMeasure.value_recursion`). The
  transversality condition is necessary, so the first-order conditions and the transversality
  condition characterise the optimum (`MoneyInUtilityMeasureTVC.tvc_necessary`,
  `MoneyInUtilityMeasureTVC.optimal_iff_foc_tvc`), and the value of a dollar is the present value
  of its liquidity dividends iff `βᴶE_t[u_c(t+J)/P_{t+J}] → 0`
  (`MoneyInUtilityMeasureTVC.value_of_money_limit_iff`). The date-`t` present-value budgets
  (19.11)–(19.12) hold almost surely iff the conditional transversality conditions do
  (`HouseholdMeasureTVC.pv_1911_iff`, `HouseholdMeasureTVC.pv_1912_iff`). In cash in advance, for
  every velocity `V`, `Λ_tw_t = βᵗu′(y_t)` and the bond price with the wedge
  `w = 1 + (1/V − 1)ι` are derived (`CashInAdvanceMeasure.lambda_derived`,
  `CashInAdvanceMeasure.bond_1932`); the printed (19.32) holds for `V = 1` and fails for every
  `V ≠ 1` (`CashInAdvanceMeasure.bond_1932_V1`, `CashInAdvanceMeasure.printed_1932_counterexample`).
  The transversality condition is necessary there too, and Fact 2 (19.33) holds almost surely
  wherever `i > 0` (`CashInAdvanceMeasureTVC.tvc_necessary`, `CashInAdvanceMeasureTVC.money_binds`,
  `CashInAdvanceMeasureTVC.money_binds_1933`). The i.i.d. economies of `ExpectationsMeasureIID`, in
  which every history has probability zero, carry optimal plans of both models
  (`MoneyInUtilityMeasure.IID.coin_economy`, `CashInAdvanceMeasure.IID.iid_sdf`); with coin shocks
  and `V ≠ 1` the bond price and the wedge are genuinely random and the printed (19.32) fails
  almost surely at every date (`CashInAdvanceMeasureTVC.IIDWedge.coin_wedge`). On a finite event
  tree the measure-theoretic optima are the tree optima of `MoneyInUtility.FootnoteTree` and
  `CashInAdvance.TreeEuler`, in both directions
  (`MoneyInUtilityMeasure.Link.link_tOptimal_of_optimal`,
  `MoneyInUtilityMeasure.Link.link_optimal_of_tOptimal`, `CashInAdvanceMeasure.Link.link_isOptimal`,
  `CashInAdvanceMeasure.Link.link_optimal_of_isOptimal`).
* **The household problem without regularity hypotheses.** With prices only adapted, positive and
  with `Λ_t/P_t` integrable (`TidyR6HouseholdRoll.PriceWeak`), no bound on consumption, real
  balances, claims, endowment or taxes, and utility `C¹` only on an open domain (so `log` and
  power utilities are covered), (19.13)–(19.14) hold with one **constant** multiplier, derived from
  perpetual-rollover deviations (`TidyR6HouseholdFOC.miu_multiplier`). The exact characterisation
  of the money-in-utility optimum is these first-order conditions with `λ > 0` plus the liminf
  transversality condition (`TidyR6HouseholdSuff.miu_optimal_iff`); the liminf form needs no
  concavity or reference plan (`TidyR6HouseholdFOC.miu_liminf_tvc`). In cash in advance `Q_t ≤ 1`
  is derived from optimality (`TidyR6HouseholdCIA.cia_iota_nonneg`), the Karush–Kuhn–Tucker
  conditions are necessary everywhere, including where money is zero
  (`TidyR6HouseholdCIAKKT.cia_kkt_necessary`), and the optimum is exactly KKT plus the liminf
  transversality condition (`TidyR6HouseholdCIAKKT.cia_optimal_iff`); the wedge Euler equation
  (19.31) can fail at an optimum with zero money
  (`TidyR6HouseholdCIA.WedgeCx.wedge_euler_needs_money`). The limit transversality condition is
  necessary without bounds (`TidyR6HouseholdTVC.tvc_general`), with concavity only on two
  segments per date (`TidyR6HouseholdTVCDom.tvc_seg`), for utilities on open convex domains such
  as `log` (`TidyR6HouseholdTVCDom.miu_tvc_dom`, `TidyR6HouseholdTVCDom.cia_tvc_dom`,
  `TidyR6HouseholdTVCDom.log_hypotheses`); it fails at an optimum without an admissible
  reference plan or without nonsatiation (`TidyR6HouseholdTVCCx.tvc_needs_reference`,
  `TidyR6HouseholdTVCCx.tvc_needs_nonsatiation`, `TidyR6HouseholdTVCCx.cia_needs_nonsatiation`). For a general `ExpectationSystem` the pointwise
  first-order conditions cannot be derived because of states the date-0 expectation ignores
  (`TidyR6HouseholdNull.bond_price_needs_foc`, `TidyR6HouseholdNull.value_recursion_needs_foc`),
  and on a countable state space every `ExpectationSystem` is given by finitely supported
  conditional probabilities (`TidyR6HouseholdRep.expectation_rep`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections are:
* `1 + µ > β`, not `1 + µ > 1/β`, on p. 445 (E13), and the same condition `µ > −δ/(1 + δ)` for
  the deflations of the Online Appendix, whose transversality condition fails at `µ = 0` too (E17);
* `Q_t ≤ 1`, not `Q_t ≥ 1`, on p. 453 (E14); `Q = β` only with a constant price level, p. 450
  (E15);
* "inelastic" and "roughly one" on p. 458: the peak elasticity is `π/(π + g)` (E16);
* the Figure 3.2 caption, `v′(m)` for `v(m)` (E18), and `P̄y/M` for `PM/M` on p. 619 (E22);
* stability of the Obstfeld (1984) map needs `b > 1 + i/2`, and the printed coefficient misses
  `1 + i` (E19);
* the CES limits of Online Appendix Chapter 4 (E20) and the dropped `−δσ` in (4.13)–(4.14), with
  `E_tπ_{t+1}` in (4.15) (E21);
* 28.6%, not 40%, on p. 462 (E23);
* active fiscal policy rules out the multiple equilibria of p. 454 only when `B_{−1} + M_{−1} ≥ 0`,
  the proviso of p. 453 (`TidyR5ActiveFiscal.active_fiscal_unique_iff`); under uncertainty it also
  needs `B_{−1} + M_{−1} > 0` or `q_0 < 1` (`TidyR6ActiveFiscalTree.pin_needed`), and the standard
  equilibrium exists only if surpluses are coordinated with money
  (`TidyR6ActiveFiscalTree.coin_no_standard_equilibrium`, `TidyR6ActiveFiscalExist.std_exists_iff`);
* "first order conditions and transversality conditions are necessary and sufficient", p. 453:
  the limit transversality condition is not necessary in general; the optimum is exactly the
  first-order (KKT) conditions plus the liminf transversality condition
  (`TidyR6HouseholdTVCCx.tvc_needs_reference`, `TidyR6HouseholdSuff.miu_optimal_iff`,
  `TidyR6HouseholdCIAKKT.cia_optimal_iff`).

In addition, the formalisation shows that (19.29) needs the money transversality condition, that
(19.32) fails for `V ≠ 1`, that the wedge Euler equation (19.31) needs positive overnight money,
that (19.38) must include money, that the partial derivatives on p. 631 have sign typos, and that
the calibration of p. 444 holds only for `γ = 1`.

Not formalised:
* the verbal and historical parts of the chapter: §19.4 beyond the Online Appendix claims, §19.8
  beyond Baumol–Tobin, the LM slope, cash-in-advance elasticities and E23, the literature survey
  of Online Appendix §3.1.4 (including the Buiter–Siebert notation clash of E17), the
  interpretation of §3.2.3, and §3.3 on uniqueness in cash-in-advance models;
* the remaining hypotheses of the household problem on a probability space. The necessity of the
  limit transversality condition still assumes utility concave and increasing along the bundle on
  the plan–reference and plan–step segments, the Kamihigashi step in the domain, and in cash in
  advance nonnegative reference and step money (`TidyR6HouseholdTVCDom.tvc_seg`); whether these
  are needed is open, and only primitive sufficient conditions for the money ones are given
  (`TidyR6HouseholdTVCDom.mRef_nonneg`, `TidyR6HouseholdTVCDom.step_money_nonneg`). A
  counterexample would need an optimum at which wealth oscillates while utility stays summable,
  and certifying its optimality needs a global supergradient at the plan, which forces utility to
  grow linearly. CRRA utility with `σ > 1` meets the hypotheses of
  `TidyR6HouseholdTVCDom.cia_tvc_dom` but is not certified in Lean (only `log` is,
  `TidyR6HouseholdTVCDom.log_hypotheses`). Utility that is only locally Lipschitz, without
  continuous partial derivatives, is not covered. The integrability of `Λ_t/P_t` in
  `TidyR6HouseholdRoll.PriceWeak` is kept as part of the definition: without it `Q_t` is not a
  conditional expectation;
* for a general `ExpectationSystem` the first-order conditions and `Λ_t = βᵗu′(y_t)` remain
  hypotheses (`CashInAdvance.Stochastic.bond_price_19_32`, `MoneyInUtility.value_recursion`): the
  obstruction is states the date-0 expectation ignores, not the absence of a measure
  (`TidyR6HouseholdNull.nullSystem`). On a countable state space every `ExpectationSystem` is
  given by finitely supported probabilities (`TidyR6HouseholdRep.expectation_rep`); on an
  uncountable one the representation is neither proved nor refuted, since a counterexample would
  yield a real-valued measurable cardinal, whose existence ZFC (and Lean) cannot prove;
* the Hamiltonian conditions (4.16)–(4.17) beyond the book's concave problem. Necessity and
  sufficiency are proved for concave `u, v` with continuous derivatives on `(0, ∞)` and optimal
  consumption `LocBounded` and continuous off a countable set
  (`TidyR6PontryaginPCSuff.optimal_iff_pc`). The necessity of the transversality condition needs
  Kamihigashi's scaling condition (`TidyR6Pontryagin.tvc_necessary`); Halkin's minimal problem
  shows that some condition is needed (`TidyR6Halkin.halkin_no_tvc`), but no counterexample inside
  the book's model is formalised and no homogeneity condition replacing it is proved. A general
  Pontryagin principle without concavity is not formalised;
* the product step `E_td(BΛ/P)` of Online Appendix §1.6 (1.32) for bonds with a martingale or
  diffusive (non-bounded-variation) part: that needs a stochastic integral and the bracket
  `[X, B]`, which Mathlib does not have. A Brownian motion itself now exists
  (`TidyR7BrownianExist.exists_isBrownianReal`), with its martingale tools, but no stochastic
  integral is built on it; no measurable modification of an arbitrary `IsBrownianReal` and no
  usual augmentation of its filtration are proved. Adapted bonds of bounded variation are covered, with
  continuous paths (`TidyR7ProductStep.ProductStepData.product_step`) and with càdlàg paths that
  jump together with `Λ/P` (`TidyR7ProductStepJump.JumpStepData.jump_step`). The domination and
  integrability conditions of `TidyR7ProductStep.ProductStepData` and
  `TidyR7ProductStepJump.JumpStepData` are sufficient; their necessity is not proved (only adaptedness of `B` is shown necessary,
  `TidyR7ProductStepCoin.coin_anticipating_fails`). The chain (1.31)–(1.34) built on it
  (`TidyR7MonetarismModel`, `TidyR7MonetarismValuation`, `TidyR7MonetarismJump`) inherits these
  limits; with jumping money it assumes `B + M` continuous (no atom in the surplus), and the
  failure of the pre-jump reading of (1.33) has no infinite-horizon instance (only the
  finite-horizon `TidyR7MonetarismJumpCoin.jcoin_1_33_finite`);
* (1.34) on `[0, ∞)` with nonzero money. The infinite-horizon instance of the printed (1.33) and
  (1.34) has zero money (`TidyR7MonetarismCoinInf.inf_1_34_book`): in that model with constant
  nonzero money the money transversality condition fails, because `i → 0`;
* under active fiscal policy, the literal "there is exactly one equilibrium iff the surplus is
  coordinated with money": coordination is proved equivalent to the unique equilibrium being the
  standard one (`TidyR6ActiveFiscalExist.std_existsUnique_iff`), but a unique non-standard
  equilibrium is not excluded. On a probability space existence is characterised only for
  equilibria with bounded real debt (`TidyR6ActiveFiscalMeasureExist.meas_std_exists_iff`): the
  unconditional transversality condition of `TidyR6ActiveFiscalMeasure.MeasMonetaryEq` admits
  mean-zero debt bubbles (`TidyR6ActiveFiscalBubble.bubble_not_coordinated`);
* the suspected one-period shift of the time axis of Figure 3.2 (E18).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](Monetarism/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (shared core, restated from the earlier projects) |
| [Expectations](Monetarism/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; adapted and bounded processes; forward series; the pull-out property (shared core) |
| [ExpectationsFiniteTree](Monetarism/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; the coin-flip tree and its shock (shared core) |
| [ForwardSolution](Monetarism/ForwardSolution.lean) | 44 | The forward solution of `z_t = aE_tz_{t+1} + u_t` (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [Regimes](Monetarism/Regimes.lean) | 26 | §19.1, (19.1)–(19.3): summation by parts, valuation iff transversality, NI-7, double passive and double active policy; Chapter 11 V1, V3–V5; the helicopter arithmetic of p. 342 |
| [CaganRE](Monetarism/CaganRE.lean) | 35 | §19.2, (19.4)–(19.8): the full solution family, explosions, sunspots, the forward solution, fiscal selection of the price level |
| [MoneyInUtility](Monetarism/MoneyInUtility.lean) | 73 | §19.3, (19.9)–(19.23): budget constraints, first-order conditions by optimisation (perfect foresight and finite tree), knownness, the value of money, power utility, Figure 19.1, E13 |
| [MoneyTargetingDynamics](Monetarism/MoneyTargetingDynamics.lean) | 34 | §19.3.2: global dynamics of monetary targeting (restated from the Woodford Chapter 2 project); the power example globally; E13 |
| [UnpleasantArithmetic](Monetarism/UnpleasantArithmetic.lean) | 13 | §19.6, (19.39)–(19.40): seigniorage, unpleasant arithmetic, nominal versus real debt |
| [Seigniorage](Monetarism/Seigniorage.lean) | 27 | §§19.7–19.8, (19.41): the Laffer limit and E16, the Cagan example, Chapter 11 V2, Baumol–Tobin, E23 |
| [PruningDeflation](Monetarism/PruningDeflation.lean) | 53 | Online Appendix §3.1: deflationary paths, the transversality condition and E17, fiscal theory with no money demand, open-market operations, the last-period condition |
| [PruningInflation](Monetarism/PruningInflation.lean) | 42 | Online Appendix §§3.2–3.2.1, (3.3)–(3.5): finite-time explosion, the countable classification, the modified utility and its continuum |
| [ObstfeldRogoff](Monetarism/ObstfeldRogoff.lean) | 28 | Online Appendix §§3.2.2–3.2.3, (3.6), Figure 3.2: E18, Obstfeld and Rogoff's theorem, Cochrane's demonetised equilibrium and the redemption dispute |
| [Nonseparable](Monetarism/Nonseparable.lean) | 33 | Online Appendix §3.2.4, (3.7)–(3.8): the discount factor, Obstfeld (1984) utility and E19, CES money in utility |
| [CashInAdvance](Monetarism/CashInAdvance.lean) | 78 | §19.5, (19.24)–(19.38): stochastic present-value budgets, money demand by optimisation, the Euler equation (perfect foresight and finite tree), frictionless and monetary equilibria, E14, E15 |
| [ContinuousTime](Monetarism/ContinuousTime.lean) | 82 | Online Appendix §1.6 (restated from the `Generality` project) and Chapter 4, (4.1)–(4.17): the present-value budget, first-order conditions, CES and E20, the IS curve with money and E21, the Hamiltonian |
| [Links](Monetarism/Links.lean) | 24 | The same objects across modules: coordinates `x` and `m`, E13 = E17, MIU and CIA deflations, discrete and continuous first-order conditions, CES, Cagan and seigniorage |
| [LinksTidy](Monetarism/LinksTidy.lean) | 30 | Further links: the finite-time exit and explosion derived from each other; the cash-in-advance tree problem as the footnote-1 tree problem, with the Euler results both ways; Galí's (2015) money rule (34) restated and related to the flexible-price Cagan model |
| [ExpectationsMeasure](Monetarism/ExpectationsMeasure.lean) | 71 | Measure-theoretic expectations (shared core, copied from `ObservationalEquivalence`): `MeasExpectationSystem` with Mathlib's `condExp`, the axioms a.e., news, the forward equation and sunspots, AR(1) conditional variance, bridges to and from the core `ExpectationSystem` |
| [ExpectationsMeasureIID](Monetarism/ExpectationsMeasureIID.lean) | 37 | The genuine i.i.d. economy on `ℕ → ℝ` under `ν^ℕ` (shared core): independence, moments, every history null, determinacy iff `\|a\| < 1`, AR(1), the `±1` coin |
| [HouseholdMeasure](Monetarism/HouseholdMeasure.lean) | 61 | §§19.3.1, 19.5.1 on a probability space: complete contingent-claim markets, the flow budget almost surely, no-Ponzi, expected utility as a genuine integral; budget-neutral deviations and the first-order condition; the date-0 present-value budget; sufficiency; the bundle Euler equation; finite trees as probability spaces |
| [MoneyInUtilityMeasure](Monetarism/MoneyInUtilityMeasure.lean) | 32 | §19.3.1, (19.13)–(19.16) on a probability space: the first-order conditions necessary and sufficient, the bond price, money demand and value recursion derived; links to `MoneyInUtility.FootnoteTree`; the i.i.d. and coin economies |
| [CashInAdvanceMeasure](Monetarism/CashInAdvanceMeasure.lean) | 36 | §19.5, (19.24)–(19.32) on a probability space for every `V`: the velocity wedge, `Λ` and (19.31)–(19.32) derived, the counterexample to the printed (19.32) for `V ≠ 1`, sufficiency; links to `CashInAdvance.TreeEuler`; the i.i.d. economy with `V = 1` |
| [HouseholdMeasureTVC](Monetarism/HouseholdMeasureTVC.lean) | 23 | (19.11)–(19.12), (19.28): the date-`t` present-value budgets iff the conditional transversality conditions; the transversality condition is necessary (Kamihigashi deviation) |
| [MoneyInUtilityMeasureTVC](Monetarism/MoneyInUtilityMeasureTVC.lean) | 6 | §19.3.1, p. 441: transversality necessary; first-order conditions and transversality iff optimal; the iterated value of money and its limit |
| [CashInAdvanceMeasureTVC](Monetarism/CashInAdvanceMeasureTVC.lean) | 17 | §19.5, (19.28), (19.33): transversality necessary for every `V`; Fact 2 under uncertainty; the i.i.d. economy with `V ≠ 1`, a random wedge and the printed (19.32) failing |
| [TidyR5BK](Monetarism/TidyR5BK.lean) | 108 | The general Blanchard–Kahn theorem, a verbatim copy of the `StickyPriceFiscal` project's `BKCopy` (itself the Woodford Chapter 4 project's `InvariantSplit`, `GeneralBKForward` and `GeneralBK`) |
| [TidyR5MoneyRule](Monetarism/TidyR5MoneyRule.lean) | 67 | §19.1, p. 435, with Galí (2015), p. 75: Galí's determinacy theorem for the money rule (34), restated from the Galí Chapter 4 project for the equilibrium notion of `LinksTidy.GaliMoneyRule`; the root count, both `η > 0` and `η = 0` |
| [TidyR5KappaLimit](Monetarism/TidyR5KappaLimit.lean) | 14 | §§19.1–19.2: the `O(1/κ)` bound and the uniform `κ → ∞` limit of the sticky-price equilibria; when it is attained |
| [TidyR5ActiveFiscal](Monetarism/TidyR5ActiveFiscal.lean) | 6 | §19.5.5, pp. 453–454: active fiscal policy determines the cash-in-advance price level across all paths iff `B_{−1} + M_{−1} ≥ 0`; the counterexample otherwise |
| [TidyR6HouseholdRoll](Monetarism/TidyR6HouseholdRoll.lean) | 16 | §19.3, footnote 1, p. 440: weak price regularity `PriceWeak`; homogeneous deviations; the perpetual rollover of debt as a budget-neutral deviation |
| [TidyR6HouseholdLocal](Monetarism/TidyR6HouseholdLocal.lean) | 14 | (19.9), (19.13)–(19.14): utility `C¹` on an open domain; differentiation of expected utility for localized deviations with no bound on the plan |
| [TidyR6HouseholdFOC](Monetarism/TidyR6HouseholdFOC.lean) | 17 | (19.13)–(19.14): the money-in-utility first-order conditions with one constant multiplier, without regularity hypotheses; the liminf transversality condition |
| [TidyR6HouseholdSuff](Monetarism/TidyR6HouseholdSuff.lean) | 5 | p. 453: sufficiency with `PriceWeak` prices and the liminf transversality condition; the money-in-utility optimum iff first-order conditions plus liminf transversality |
| [TidyR6HouseholdCIA](Monetarism/TidyR6HouseholdCIA.lean) | 10 | (19.31), (19.33), p. 453: the wedge Euler equation where money is positive; `Q_t ≤ 1` derived; KKT sufficiency; the wedge Euler equation fails with zero money |
| [TidyR6HouseholdTVCCx](Monetarism/TidyR6HouseholdTVCCx.lean) | 16 | p. 439, (19.28): the admissible reference plan and nonsatiation cannot be dropped from the transversality theorem |
| [TidyR6HouseholdTVC](Monetarism/TidyR6HouseholdTVC.lean) | 18 | p. 439, (19.28): the transversality condition necessary without bounds, for money in utility and cash in advance |
| [TidyR6HouseholdNull](Monetarism/TidyR6HouseholdNull.lean) | 6 | (19.15)–(19.16), (19.31)–(19.32): null states; for a general `ExpectationSystem` the pointwise first-order conditions cannot be derived |
| [TidyR6HouseholdCIAKKT](Monetarism/TidyR6HouseholdCIAKKT.lean) | 12 | (19.24)–(19.33), p. 453: the KKT conditions necessary everywhere; the cash-in-advance optimum iff KKT plus liminf transversality |
| [TidyR6HouseholdTVCDom](Monetarism/TidyR6HouseholdTVCDom.lean) | 15 | p. 439, (19.28): the transversality condition with concavity on two segments only, for utilities on open convex domains (`log` certified) |
| [TidyR6HouseholdRep](Monetarism/TidyR6HouseholdRep.lean) | 7 | Ch. 2, pp. 29–30: every `ExpectationSystem` on a countable state space is given by finitely supported conditional probabilities |
| [TidyR6WoodfordSections](Monetarism/TidyR6WoodfordSections.lean) | 27 | §19.3.2, pp. 441–445, and A3 §3.2.2: Woodford's convexity counterexample (E7), Taylor-rule transversality section (E4) and Obstfeld–Rogoff section (4.10), restated from the Woodford Chapter 2 project and linked to `MoneyTargetingDynamics` |
| [TidyR6ActiveFiscalTree](Monetarism/TidyR6ActiveFiscalTree.lean) | 23 | §19.5.5, pp. 448–454, under uncertainty for every `ExpectationSystem` with full support: the stochastic wealth recursion, `Q_t ≥ q_t`, uniqueness of the standard equilibrium; the proviso, the pinning condition and the coin-flip counterexample to existence |
| [TidyR6ActiveFiscalExist](Monetarism/TidyR6ActiveFiscalExist.lean) | 6 | pp. 448–454: the standard equilibrium exists iff the surplus is coordinated with money; coordination iff the unique equilibrium is the standard one |
| [TidyR6ActiveFiscalMeasure](Monetarism/TidyR6ActiveFiscalMeasure.lean) | 13 | §19.5.5 on a probability space: the recursion and valuation in expectation, `Q_t ≥ q_t` a.s., uniqueness of the standard price level almost surely |
| [TidyR6ActiveFiscalMeasureExist](Monetarism/TidyR6ActiveFiscalMeasureExist.lean) | 6 | pp. 448–454 on a probability space: unique bonds, `q_t > 0`, existence iff coordination for bounded real debt |
| [TidyR6ActiveFiscalBubble](Monetarism/TidyR6ActiveFiscalBubble.lean) | 6 | (19.28), pp. 449–454: a mean-zero debt bubble on the coin tree, a standard-price equilibrium under the unconditional transversality condition without coordination |
| [TidyR6PontryaginTools](Monetarism/TidyR6PontryaginTools.lean) | 16 | A4 §4.1.3, p. 640: the concave first-order condition under an integral by monotone convergence, the tangent inequality, smooth bumps, the du Bois-Reymond lemma |
| [TidyR6Pontryagin](Monetarism/TidyR6Pontryagin.lean) | 16 | A4 (4.16)–(4.17), pp. 640–641: the book's problem; necessity of the costate equation and of the transversality condition (Kamihigashi), sufficiency, the characterisation; the `log` steady state |
| [TidyR6PontryaginPC](Monetarism/TidyR6PontryaginPC.lean) | 11 | A4 (4.16)–(4.17): necessity with piecewise-continuous consumption; a continuous costate equal to `u′(c)` off the jumps |
| [TidyR6PontryaginPCSuff](Monetarism/TidyR6PontryaginPCSuff.lean) | 2 | A4 (4.16)–(4.17): sufficiency with a continuous costate; the characterisation with piecewise-continuous consumption |
| [TidyR6Halkin](Monetarism/TidyR6Halkin.lean) | 4 | A4 (4.17): Halkin's (1974) counterexample, an optimum at which the transversality condition fails for every costate |
| [TidyR6StochasticDrift](Monetarism/TidyR6StochasticDrift.lean) | 12 | A1 §1.6, (1.32)–(1.34), p. 567: `E_td(·)` exactly on a `Δ`-grid; the drift notion, valuation iff transversality under uncertainty, finite-variation discount factors |
| [TidyR7StieltjesIntegral](Monetarism/TidyR7StieltjesIntegral.lean) | 44 | A1 §1.6, p. 567 (tool for (1.32)): the Riemann–Stieltjes integral `∫_a^b f dg` from Mathlib's Lebesgue–Stieltjes vector measure; its atoms, linearity in `f` and `g`, the bound `sup\|f\|·Var(g)`, additivity over intervals; càdlàg functions have countably many jumps |
| [TidyR7StieltjesSums](Monetarism/TidyR7StieltjesSums.lean) | 34 | A1 §1.6, p. 567 (tool for (1.32)): partitions; convergence of left-point Riemann–Stieltjes sums for continuous `f` or for càdlàg `f` with continuous `g`; the cross sum vanishes, and needs continuous `g`; dyadic partitions |
| [TidyR7StieltjesCalculus](Monetarism/TidyR7StieltjesCalculus.lean) | 11 | A1 §1.6, (1.32), p. 567 (tool): the exact partition identity for products; integration by parts; domination of the sums; measurability of `ω ↦ ∫_a^b f(ω) dg(ω)` |
| [TidyR7StieltjesVariation](Monetarism/TidyR7StieltjesVariation.lean) | 21 | A1 §1.6, p. 567 (tool for (1.32)): the variation of a right-continuous path over a countable set; `ω ↦ Var_{[a,b]}(g(ω, ·))` measurable; the degenerate interval `[a, a]` |
| [TidyR7CondDominated](Monetarism/TidyR7CondDominated.lean) | 14 | A1 §1.6, p. 567 (tool for (1.32)): conditional dominated convergence almost surely; the measurable path supremum `sup_{[s,t]}\|X\|`; partition sequences with mesh → 0 |
| [TidyR7ProductStep](Monetarism/TidyR7ProductStep.lean) | 35 | A1 §1.6, (1.32), p. 567: the product step in expectation form for adapted continuous bounded-variation `B` and `Λ/P` = bounded-variation part + martingale; the pathwise and discrete identities, limits along any partitions, the expected-increment integral `B·E_s d(Λ/P)`, the book's notation |
| [TidyR7ProductStepCases](Monetarism/TidyR7ProductStepCases.lean) | 11 | A1 §1.6, (1.32), pp. 567–568: deterministic bonds; `Λ/P` of bounded variation and integration by parts; `C¹` integrators; the `C¹` case `E_t d(Λ/P) = −i(Λ/P)dt` and the link with `TidyR6StochasticDrift.drift_1_32_fv` |
| [TidyR7ProductStepCoin](Monetarism/TidyR7ProductStepCoin.lean) | 24 | A1 §1.6, (1.32), p. 567: non-vacuity on a fair coin revealed at time 1 (random bonds, nonzero martingale part, `1 = 1 + 0`); adaptedness of `B` cannot be dropped |
| [TidyR7MonetarismAC](Monetarism/TidyR7MonetarismAC.lean) | 8 | A1 §1.6, p. 567 (tool for (1.31)–(1.32)): primitives of locally integrable densities are continuous of bounded variation; `∫_a^b f dg = ∫_a^b f h` for càdlàg `f` and `g` with density `h` |
| [TidyR7MonetarismModel](Monetarism/TidyR7MonetarismModel.lean) | 31 | A1 §1.6, (1.31)–(1.34), pp. 567–568: the model under uncertainty (`Λ/P` = finite-variation part + càdlàg martingale, the flow (1.31) path by path); (1.32) integrated, with general `i^m`, its middle line and the line before (1.34); the `HasDrift` instances; the domination conditions |
| [TidyR7MonetarismValuation](Monetarism/TidyR7MonetarismValuation.lean) | 19 | A1 §1.6, (1.33)–(1.34), p. 567: the finite-horizon budget; valuation iff transversality in limit form (no convergence hypothesis), `L¹` form and dominated form; (1.33) and (1.34) as printed |
| [TidyR7MonetarismCoin](Monetarism/TidyR7MonetarismCoin.lean) | 30 | A1 §1.6, (1.31)–(1.33), p. 567: non-vacuity on a fair coin with news in `Λ/P` (both sides of (1.32) are `1/2`; the expectation is needed; the finite-horizon (1.33)); the printed `E_t∫_t^∞` can be undefined while the limit form holds |
| [TidyR7MonetarismLinks](Monetarism/TidyR7MonetarismLinks.lean) | 14 | A1 §1.6, (1.32)–(1.34), p. 567: the `C¹` case, the deterministic `ContinuousTime` forms and the `Δ`-grid recovered from the stochastic chain |
| [TidyR7MonetarismCoinInf](Monetarism/TidyR7MonetarismCoinInf.lean) | 27 | A1 §1.6, (1.33)–(1.34), p. 567: non-vacuity on `[0, ∞)` with news in `Λ/P` and a positive nominal rate (zero money): the `L¹` form and the printed (1.33) and (1.34) |
| [TidyR7MonetarismUI](Monetarism/TidyR7MonetarismUI.lean) | 36 | A1 §1.6, (1.33), p. 567: the domination (or `L¹`) hypothesis of the printed `E_t∫_t^∞` cannot be dropped: transversality and the limit form hold, the pathwise limit exists, the literal equation fails |
| [TidyR7JumpSums](Monetarism/TidyR7JumpSums.lean) | 28 | A1 §1.6, p. 567 (tool for (1.32)): Riemann–Stieltjes sums against a càdlàg bounded-variation integrator: left-point sums tend to `∫ f_− dg`, right-point sums to `∫ f dg`, cross sums to the absolutely convergent jump covariation `Σ_u Δf_uΔg_u = ∫ f dg − ∫ f_− dg` |
| [TidyR7ProductStepJump](Monetarism/TidyR7ProductStepJump.lean) | 43 | A1 §1.6, (1.32), p. 567: the corrected product step for adapted càdlàg bounded-variation bonds, with the jump covariation as a third term; its two-term Lebesgue–Stieltjes form; the book's left-point step holds iff the expected jump covariation vanishes; continuous bonds recover `TidyR7ProductStep` |
| [TidyR7ProductStepJumpCoin](Monetarism/TidyR7ProductStepJumpCoin.lean) | 27 | A1 §1.6, (1.32), p. 567: on the coin, bonds jumping with the news break the left-point step (`1 ≠ 0`), bonds jumping with the drift part break the two-term Lebesgue–Stieltjes step (`1 ≠ 1 + 1`); the corrected step holds in both and with a non-shared jump |
| [TidyR7MonetarismJump](Monetarism/TidyR7MonetarismJump.lean) | 43 | A1 §1.6, (1.31)–(1.34), pp. 567–568: the model with jumping money (`ΔB = −ΔM`, `B + M` continuous); (1.32) line 3 and (1.33) verbatim with the post-jump `∫ n dM`, the extra term `−E_s[Σ ΔnΔM]` with the pre-jump reading, the printed middle line iff it vanishes; (1.34) verbatim |
| [TidyR7MonetarismJumpCoin](Monetarism/TidyR7MonetarismJumpCoin.lean) | 12 | A1 §1.6, (1.31)–(1.34), pp. 567–568: an open-market operation at a news date: the pre-jump line 3 of (1.32) and the printed middle line fail (`0 ≠ −1/2`), the finite-horizon (1.33) fails with the pre-jump flow; the post-jump forms and (1.34) hold |
| [TidyR7BrownianSchauder](Monetarism/TidyR7BrownianSchauder.lean) | 53 | A1 §1.6, pp. 567–568 (tool for (1.32) with diffusive bonds; copied from the Meyn–Tweedie project): the Lévy–Ciesielski construction on `[0,1]`: Schauder functions, the covariance identity `Σ_m S_m(s)S_m(t) = min s t`, Gaussian sums and their limits, uniform convergence almost surely to a path continuous for every `ω` |
| [TidyR7BrownianUnit](Monetarism/TidyR7BrownianUnit.lean) | 13 | A1 §1.6, pp. 567–568 (tool; copied from the Meyn–Tweedie project): Brownian motion on `[0,1]`: continuous paths from `0`, finite-dimensional laws, Mathlib's `IsGaussianProcess`, `B(t) ~ N(0, t)`, `Cov(B s, B t) = min s t` |
| [TidyR7BrownianExist](Monetarism/TidyR7BrownianExist.lean) | 17 | A1 §1.6, pp. 567–568 (tool for (1.32) with diffusive bonds): a Brownian motion on `[0, ∞)` exists (Mathlib's `IsBrownianReal`), the time change `(1+t)B(t/(1+t)) − tB(1)`, every path continuous; `W 2 − W(1/2) ~ N(0, 3/2)` |
| [TidyR7BrownianTools](Monetarism/TidyR7BrownianTools.lean) | 25 | A1 §1.6, pp. 567–568 (tool): for any pre-Brownian motion, the second and fourth moments of increments, the natural filtration, increments independent of the past, `W` and `W t² − t` martingales; the bridge to the index `ℝ` |

## Modelling conventions

* **Expectations.** Random variables are `Ω → ℝ`, processes `ℕ → Ω → ℝ`, and the present-value
  and Cagan results hold state by state for an arbitrary `ExpectationSystem`. A process is adapted
  when `E_tx_t = x_t` (`ExpectationSystem.Adapted`). Results that take date-`t` quantities out of
  `E_t` assume `ExpectationSystem.PullOut`. Perfect foresight (`perfectForesight`) and every
  finite event tree (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) are instances, and
  the coin-flip tree gives a genuine Cagan sunspot (`CaganRE.coin_sunspot_solves`).
* **Timing.** In `Regimes` and `MoneyInUtility` money and bonds carried into date `t` are indexed
  by `t`, so the book's `M_{t−1}` and `B_{t−1}` are dated `t`. In `CashInAdvance` they are
  `Min t` and `Bin t`, and the bonds and overnight money chosen at `t` are dated `t + 1`.
* **Infinite sums.** The sums `E_t∑` of (19.2), (19.3), (19.11) and (19.12) are limits of `E_t`
  of the partial sums, multiplied through by the known `Λ_t` (`Regimes.partial192`). The
  cash-in-advance budgets use `tsum` with summable flows
  (`CashInAdvance.Stochastic.pv_iff_tvc`), and `Links.flow_pv_tsum_iff_tvc` restates the
  `Regimes` form that way. Unpleasant arithmetic uses genuine `HasSum`.
* **Optimisation.** The household problems are stated as optimisation problems and their
  first-order conditions are derived, not imposed: `MoneyInUtility.Optimal`,
  `MoneyInUtility.FootnoteTree.TOptimal`, `CashInAdvance.Euler.IsOptimalPlan` and
  `CashInAdvance.TreeEuler.IsOptimal`. The cash-in-advance consumption problem is the
  money-in-utility problem without money, under perfect foresight
  (`CashInAdvance.Euler.isOptimalPlan_iff_optimal`) and on a finite tree
  (`LinksTidy.TreeBridge.isOptimal_iff_tOptimal`), and
  overnight money is a linear programme (`CashInAdvance.MoneyDemand.IsOptimalMoney`).
* **Coordinates.** Chapter 19 writes (19.23) in `x = Py/M` (`MoneyInUtility.nextX`); the Online
  Appendix writes it in real balances `m = M/(Py) = 1/x` (`PruningDeflation.ratioMap`). Both are
  kept, and `Links` proves them conjugate (`Links.ratioMap_eq_one_div_nextX`,
  `Links.isMPath_iff_isPowerPath`).
* **Demonetisation.** In the Online Appendix the value of money `q_t = 1/P_t ≥ 0` is the state, so
  an infinite price level is `q_t = 0` (`PruningInflation.IsEqm`, `ObstfeldRogoff.IsORPath`).
* **Continuous time.** Paths are `ℝ → ℝ` with `HasDerivAt`; present values are integrals over
  `(t, ∞)` with `IntegrableOn`; transversality conditions are explicit limits. In `TidyR6Pontryagin`
  the budget (4.16) may fail on a countable set, so consumption may jump, and a plan is optimal
  when no feasible plan has a utility gain with a larger positive than negative part.
  `TidyR6StochasticDrift` uses processes `ℝ → Ω → ℝ` on a probability space with a filtration
  indexed by `ℝ`, and `E_tdX = a dt` means that `X − ∫a` has the martingale property
  (`TidyR6StochasticDrift.HasDrift`). In the `TidyR7Stieltjes…` modules partitions are strictly
  increasing (`TidyR7StieltjesSums.Partition`), càdlàg is Mathlib's `IsCadlag` on `ℝ`, and
  linearity and additivity of the integral assume `TidyR7StieltjesIntegral.RSIntegrable`, which
  continuous, càdlàg and bounded measurable integrands satisfy.
* **Measure-theoretic expectations.** The core `ExpectationSystem` (an operator `E_t` on all
  functions `Ω → ℝ`, with exact equalities) is kept unchanged, and every result above that is
  stated for it still holds. On a countable `Ω` it forces finitely supported forecasts
  (`TidyR6HouseholdRep.expectation_rep`), so it cannot carry an infinite-horizon household
  problem with nondegenerate shocks.
  `ExpectationsMeasure` adds, alongside it, a probability space with a filtration
  (`ExpectationsMeasure.MeasExpectationSystem`): `E_t` is Mathlib's conditional expectation
  `condExp`, variables are bounded measurable functions and processes, and equations hold almost
  everywhere. The bridge is additive and runs both ways: a finite event tree is a measure system
  with the same `E_t` at every state (`ExpectationsMeasure.TreeBridge.treeSystem_E`), and a
  measure system on a finite discrete state space with full support is a core system with the
  pull-out property (`ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem`,
  `ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_pullOut`). The genuine instance
  is the i.i.d. economy on `ℕ → ℝ` under `ν^ℕ`, in which every history has probability zero
  (`ExpectationsMeasureIID.iidSystem`, `ExpectationsMeasureIID.iid_not_finitely_supported`). The
  household modules add complete markets with the nominal state-price density `pk = Λ/P`
  (`HouseholdMeasure.pk`, `HouseholdMeasure.bondPrice`, `HouseholdMeasure.iota`), contingent
  claims `a_t` in place of `B_{t−1}`, the flow constraint almost surely
  (`HouseholdMeasure.Flow`), a no-Ponzi condition (`HouseholdMeasure.Feasible`), essentially
  bounded variables (`HouseholdMeasure.BddAt`) and regular prices
  (`HouseholdMeasure.PriceRegular`); the `TidyR6Household…` modules replace the last two by weakly
  regular prices (`TidyR6HouseholdRoll.PriceWeak`) and unbounded plans. Optimality is
  `HouseholdMeasure.Optimal` with an extra constraint, none for money in utility and the
  cash-in-advance constraints in real overnight balances for cash in advance
  (`CashInAdvanceMeasure.CIACon`).
* **Explicit hypotheses.** Positivity of prices, money, output and velocity, `0 < β < 1`,
  summability of discounted flows, concavity for sufficiency, and the domain `θx^γ < 1` of the
  power map are stated in each theorem.

## Relation to the Woodford projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects, so the project builds on its own. Nothing is imported from
those projects. Four further blocks come from the Woodford Chapter 2 project
(`PriceLevelDetermination`), and their docstrings say so:
* `MoneyTargetingDynamics` restates that project's survey lemma L5 on one-dimensional maps (from
  its `GlobalDynamics` module) and its analysis of monetary targeting (from its module of the same
  name): the maps `F` and `G`, the separable map of Woodford's Figure 2.5, self-fulfilling
  inflations and deflations, satiation and the transversality condition
  (`MoneyTargetingDynamics.sepMap`, `MoneyTargetingDynamics.sep_deflation_violates_tvc`,
  `MoneyTargetingDynamics.money_contraction_continuum`). Cochrane's (19.18) is that separable map
  with `μ̄ = 1 + µ` (`MoneyTargetingDynamics.miuPath_iff_sepPath`). The module then adds
  Cochrane's power example globally;
* `CaganRE` is adapted from that project's Cagan equation (A.28)–(A.29) (`MoneyGrowth`);
* `MoneyInUtility.lm_unique` and `MoneyInUtility.lm_exists` restate its money-demand lemmas;
* `TidyR6WoodfordSections` restates the three sections `MoneyTargetingDynamics` left out (the
  convexity counterexample E7, the Taylor-rule transversality section with E4 and the
  Obstfeld–Rogoff section) and links them to `MoneyTargetingDynamics`.

The two books use different Obstfeld–Rogoff devices. Woodford's is the boundary condition (4.10)
`lim m v′(m) > 0`, under which no inflationary path is an equilibrium; his `or_*` theorems are
restated in `TidyR6WoodfordSections` and applied to (19.18)
(`TidyR6WoodfordSections.or_miu_no_path_below`). Cochrane's Online Appendix uses the redemption of money at a floor value `ε`, and
`ObstfeldRogoff` proves that argument directly (`ObstfeldRogoff.or_no_hyperinflation`) together
with Cochrane's demonetised counter-equilibrium. Under the redemption device the outcome depends on
whether the offer is a one-time tender or a standing offer
(`ObstfeldRogoff.cochrane_household_optimal`, `ObstfeldRogoff.standing_redemption_no_optimum`).

## Relation to other Cochrane projects

* **Chapter 3 and Online Appendix §1.6 (`Generality`).** That project owns the valuation equation
  with money in continuous time (its `ContinuousMoney` module). `ContinuousTime` restates (1.28)
  and (1.31)–(1.37) from it (`ContinuousTime.money_printing_iff`,
  `ContinuousTime.money_interest_iff`, `ContinuousTime.money_mixed_iff`), together with the
  misdated integrand of p. 568, which that project found first
  (`ContinuousTime.printed_index_counterexample`).
* **Chapter 2 (`IntertemporalModel`).** The tangent-line inequality for concave functions is
  restated from it (`MoneyInUtility.concave_le_tangent`).
* **Chapters 5 and 17 (`StickyPriceFiscal`).** `TidyR5BK` is a verbatim copy of that project's
  `BKCopy`, the general Blanchard–Kahn theorem of the Woodford Chapter 4 project nested as
  sub-namespaces: the same 129 declarations, only the namespace changed, with the Woodford
  (2003) App. C.1 citations kept. The two projects' core `Expectations` modules are identical, so
  no adaptation was needed. Here it serves Galí's money-rule theorem (`TidyR5MoneyRule`), which is
  restated from the Galí Chapter 4 project with its system and equilibrium notion taken from
  `LinksTidy.GaliMoneyRule` rather than copied.
* **Chapter 22 (`ObservationalEquivalence`).** That project owns the general equivalence of money
  regimes, OE-2 (its `MoneyRegimes.oe2`). This project proves the §19.1 statement NI-7
  (`Regimes.ni7`) for the valuation equation `B_{t−1} + M_{t−1} = P_tW_t` with an arbitrary
  expectation operator, and V4 as its open-market special case (`Regimes.omo_equivalence`).

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
