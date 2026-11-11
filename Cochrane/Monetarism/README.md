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
`TidyR7MonetarismValuation`, `TidyR7MonetarismIto`). The library contains **2990 theorems**, including the shared core; 578 of them are in the fourteen
chapter modules, 175 in the six measure-theoretic household modules, 195 in the four `TidyR5…`
modules, 108 of these in a verbatim copy of the general Blanchard–Kahn theorem (`TidyR5BK`), 136
in the eleven `TidyR6Household…` modules, 142 in the twelve further `TidyR6…` modules: 27 on
Woodford's convexity, Taylor-rule and Obstfeld–Rogoff sections, 54 on active fiscal policy under
uncertainty, 49 on the Hamiltonian conditions and 12 on the `E_td(·)` forms, 110 in the four
`TidyR7Stieltjes…` modules, deterministic Riemann–Stieltjes tools for the product step of (1.32),
28 in `TidyR7JumpSums`, the same tools for jumping integrators, 154 in the six
`TidyR7CondDominated`/`TidyR7ProductStep…` modules that prove that product step, for continuous
and for jumping bonds, 283 in the thirteen `TidyR7Monetarism…` modules that prove the chain
(1.31) → (1.32) → (1.33)–(1.34) under uncertainty, with continuous, with jumping and with
diffusive money and bonds,
173 in the six `TidyR7Brownian…` modules, a Brownian motion on `[0, ∞)`, its martingale tools,
its quadratic variation and the infinite variation of its paths, 66 of them copied from the
Meyn–Tweedie project, 239 in the eleven `TidyR7Ito…` modules, the Itô integral `∫ H dW`,
Itô processes, Itô's product rule with covariation and the general product step of (1.32)
with diffusive bonds, 100 in the five `TidyR8Monetarism…` modules, the sharp condition
for the printed (1.33)–(1.34), the dominated (1.33) with the bracket and infinite-horizon
instances with nonzero and with jumping money, 80 in the eight `TidyR9…` modules, Itô's
formula for `f(t, X)`, `1/X` and `exp X` and the counterexamples to (1.32) and (1.33) with a
positive diffusive `Λ/P`, 79 in the eight `TidyR10Doob…` modules, Doob's `L²` inequality,
adapted continuous versions of `∫ G dW`, the product step with `M = W` and `M = ∫ K dW` and the
Fubini isometry, 94 in the five `TidyR10TwoBM…` modules, two independent Brownian motions,
their cross variation and the (1.32) product step with bonds and `Λ/P` on different shocks,
71 in the four `TidyR11JumpDiff…` modules, the (1.32) product step with jumps and diffusion
together, in terms of money and on a Brownian motion with an independent coin, and 137 in the
eleven `TidyR12SDE…` modules, existence and uniqueness for stochastic differential equations,
Itô processes with unbounded coefficients, geometric Brownian motion and a positive diffusive
`Λ/P` with a known constant rate.

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
  (`TidyR7ProductStepJumpCoin.jumpA_ls_fails`). Bonds that jump and diffuse at once are covered
  by the unified step below (`TidyR11JumpDiffStep.JumpDiffData.jump_diff_step`), which without
  diffusion is the jump step above (`TidyR11JumpDiffStep.JumpDiffData.jd_recovers_jump_step`).
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
  (`TidyR7MonetarismUI.ui_headline`). The sharp condition is `L¹` convergence of the flows: if
  the flows `F_{T_k}` converge almost surely to `G` and are bounded below by an integrable `−h`,
  then under the `L¹` transversality condition the printed form holds iff `∫|F_{T_k} − G| → 0`
  (`TidyR8MonetarismUISharp.valuation_iff_L1_char`), iff the flows are uniformly integrable
  (`TidyR8MonetarismUISharp.tendsto_integral_abs_iff_unifIntegrable`), and under the almost-sure
  one iff `E_s|F_{T_k} − G| → 0` a.s. (`TidyR8MonetarismUISharp.valuation_iff_condL1_char`), in
  the economy for (1.33) with `i^m = 0` and for (1.34)
  (`TidyR8MonetarismUISharp.MonetaryModel.valuation_1_33_char_L1`,
  `TidyR8MonetarismUISharp.MonetaryModel.valuation_1_34_char_L1`); domination is one sufficient
  case, and without the lower bound the printed form can hold while `E|F_{T_k} − G| = 2`
  (`TidyR8MonetarismUISharp.sgn_headline`). On `[0, ∞)` with money `M = 2`, interest on money
  `i^m = 1/2`, a decaying discount factor and news in `Λ/P`, (1.34) holds as printed, both sides
  `4` (`TidyR8MonetarismMoneyInf.moneyInf_1_34_book`). The `C¹`, deterministic and `Δ`-grid
  forms are recovered
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
  (`TidyR7MonetarismJumpCoin.jcoin_1_32_left_fails`); on `[0, ∞)`, with the transversality
  condition holding, the post-jump (1.33) holds in the dominated form while the pre-jump one
  gives `2 ≠ 2 − e^{−1}/2`, the gap being the jump covariation `e^{−1}/2`
  (`TidyR8MonetarismJumpInf.jumpInf_headline`), and (1.34) holds verbatim with jumping money
  (`TidyR8MonetarismJumpInf.jumpInf_1_34`).
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
  to the index `ℝ` of the product step (`TidyR7BrownianTools.bmReal`). Its quadratic variation is
  `t − s`: exactly `E[(Σ(ΔW_i)² − (t − s))²] = 2Σ(Δt_i)²`
  (`TidyR7BrownianQV.integral_qvSum_sub_sq`), also conditionally on `𝓕_s`
  (`TidyR7BrownianQV.condExp_qvSum_sub_sq`) for any admissible filtration
  (`TidyR7BrownianQV.BMFiltration`), so `Σ(ΔW_i)² → t − s` in `L²` and in probability as the mesh
  tends to `0` and almost surely along the dyadic partitions
  (`TidyR7BrownianQV.ae_tendsto_qvSum_dyadic`); weighted by a bounded adapted `H`,
  `Σ H(ΔW_i)² − Σ HΔt_i → 0` in `L²`, the rule `(dW)² = dt`
  (`TidyR7BrownianQV.tendsto_eLpNorm_wqvSum`). Hence almost surely every Brownian path has
  infinite variation on every interval (`TidyR7BrownianVariation.ae_forall_not_bv`), and the
  bounded-variation product step provably cannot take a Brownian bond
  (`TidyR7BrownianVariation.not_productStepData_bm`); against a bond with continuous
  bounded-variation paths the cross sum vanishes, `dW·dB = 0`
  (`TidyR7BrownianVariation.ae_tendsto_sumCross_bm_bv`).
* **The Itô integral `∫ H dW`.** For a pre-Brownian `W`, any admissible filtration and an
  integrand that is adapted, bounded and almost surely continuous on `[s, t]`
  (`TidyR7ItoIntegral.ItoIntegrand`), the left-point sums `Σ H_{t_i}ΔW_i` converge in mean square
  along any partitions with mesh `→ 0` (`TidyR7ItoIntegral.L2Tendsto_itoSum`) to an adapted
  limit `TidyR7ItoIntegral.itoInt`, built without completing the filtration
  (`TidyR7ItoL2.exists_L2Tendsto`). It satisfies the Itô isometry
  `E[(∫_s^t H dW)²] = E[∫_s^t H_u² du]` (`TidyR7ItoIntegral.integral_itoInt_sq`), is linear
  (`TidyR7ItoIntegral.itoInt_add`, `TidyR7ItoIntegral.itoInt_const_mul`), is a martingale in `t`
  (`TidyR7ItoIntegral.martingale_itoInt`) with the conditional isometry
  (`TidyR7ItoIntegral.condExp_itoInt_sq`), and has a modification with almost surely continuous
  paths on `[s, T]` (`TidyR7ItoContinuity.exists_continuous_modification`, via Kolmogorov's
  maximal inequality `TidyR7ItoContinuity.kolmogorov_maximal`). For integrands of bounded
  variation it is Track 1's pathwise integral by parts, `∫ H dW = H_tW_t − H_sW_s − ∫ W dH`
  (`TidyR7ItoBridge.itoInt_eq_byParts`), and the Itô correction holds:
  `∫_s^t W dW = (W_t² − W_s² − (t − s))/2` (`TidyR7ItoBridge.itoInt_bm`); on the constructed
  motion `∫_0^1 W dW = (W_1² − 1)/2` (`TidyR7ItoBridge.itoInt_bmPath`), not the Stratonovich value
  `W_1²/2` (`TidyR7ItoBridge.not_itoInt_bmPath_eq_stratonovich`).
* **Itô's product rule `d(XY) = X dY + Y dX + d[X, Y]`.** The Itô integral extends to
  unbounded integrands that are square integrable and uniformly continuous in mean square
  (`TidyR7ItoUnbounded.MSIntegrand`, `TidyR7ItoUnbounded.L2Tendsto_itoSum_ms`), with
  `∫ ZK dW = Z∫ K dW` for square-integrable `𝓕_r`-measurable `Z`
  (`TidyR7ItoProducts.itoInt_mul_left`). For Itô processes
  `X_u = X_s + ∫_s^u a dr + ∫_s^u H dW` and `Y_u = Y_s + ∫_s^u b dr + ∫_s^u K dW` with bounded
  adapted almost surely continuous coefficients (`TidyR7ItoProcess.ItoProcess`), the bracket is
  `Σ ΔX_iΔY_i → ∫_s^t H_uK_u du` in `L¹`, `d[X, Y] = HK dt`
  (`TidyR7ItoCovariation.tendsto_integral_abs_sumCross`), and almost surely
  `X_tY_t − X_sY_s = ∫ X dY + ∫ Y dX + ∫_s^t H_uK_u du` (`TidyR7ItoProductRule.product_rule`),
  with Itô's formula `X_t² − X_s² = 2∫ X dX + ∫_s^t H_u² du`
  (`TidyR7ItoProductRule.ito_formula_sq`). Conditionally,
  `E_s[X_tY_t − X_sY_s] = E_s[∫_s^t (Xb + Ya + HK) du]`
  (`TidyR7ItoProductRule.condExp_product_rule`), and in the expected-increment form
  `E_s d(XY) = X E_s dY + Y E_s dX + E_s d[X, Y]`
  (`TidyR7ItoProductRule.expected_increment_product_rule`). The book's bracket-free form holds
  iff `E_s[∫_s^t HK du] = 0` (`TidyR7ItoProductRule.condExp_product_rule_bookForm_iff`); for
  `H = 0` it is Track 1's product step term by term
  (`TidyR7ItoProductRule.condExp_product_rule_bv`), and for `X = Y = W` on the constructed motion
  it fails (`TidyR7ItoProductRule.not_bookForm_bmPath`).
* **Itô's formula `df(t, X) = f_t dt + f_x dX + ½f_xx d[X]`.** For an Itô process `X` with almost
  surely continuous paths on `[s, t]` and `f(u, x)` with jointly continuous partials, `f_t` and
  `f_xx` bounded and `f_x(u, X_u)` mean-square continuous, almost surely
  `f(t, X_t) − f(s, X_s) = ∫ f_t du + ∫ f_x a du + ∫ f_x H dW + ½∫ f_xx H² du`
  (`TidyR9ItoFormula.ito_formula_time`); the Taylor remainder is controlled by uniform continuity
  on the compact range of each path, so no global uniform continuity of `f''` is needed. For
  `f ∈ C²` with `f''` bounded (`f'` may be unbounded)
  `f(X_t) − f(X_s) = ∫ f'(X)a du + ∫ f'(X)H dW + ½∫ f''(X)H² du` (`TidyR9ItoFormula.ito_formula`);
  `f(x) = x²` gives back `TidyR7ItoProductRule.ito_formula_sq`
  (`TidyR9ItoFormula.ito_formula_sq_recovers`), and on the constructed motion
  `sin W_1 = ∫_0^1 cos W dW − ½∫_0^1 sin W du` (`TidyR9ItoFormula.ito_formula_sin_bmPath`). With
  `f'` bounded as well, `f(X)` is again an Itô process, with drift `f'(X)a + ½f''(X)H²` and
  diffusion `f'(X)H` (`TidyR9ItoFormula.itoProcess_comp`), and
  `E_s[f(X_t) − f(X_s)] = E_s[∫_s^t (f'(X)a + ½f''(X)H²) du]` a.s.
  (`TidyR9ItoFormula.condExp_ito_formula`). So are `f(u, X_u)`
  (`TidyR9ItoFormulaVariants.itoProcess_comp_time`), the discounted `e^{−ru}g(X_u)`
  (`TidyR9ItoFormulaVariants.itoProcess_discount`), `1/X` for `X ≥ c > 0` on `[s, t]`, with drift
  `−a/X² + H²/X³` and diffusion `−H/X²` (`TidyR9ItoFormulaVariants.itoProcess_inv`), and `exp X`
  for `|X| ≤ M` on `[s, t]`, with drift `e^X(a + ½H²)` and diffusion `e^X H`
  (`TidyR9ItoFormulaVariants.itoProcess_exp`). The lognormal discount factor
  `Λ_u = exp(σW_u − σ²u/2)`, whose diffusion coefficient is unbounded, is not an Itô process
  with bounded coefficients; its martingale property `E_s[Λ_t/Λ_s] = 1` is proved from the
  Gaussian law of the increment (`TidyR9ExpMartingale.condExp_exp_increment`), and it solves
  `dΛ = σΛ dW` as an Itô process with mean-square continuous coefficients
  (`TidyR12SDEGBM.expMart_eq`, see the item on stochastic differential equations below).
* **Doob's inequality and continuous versions.** Mathlib v4.34 has only the weak-type maximal
  inequality. Doob's `L²` inequality is proved in discrete time,
  `E[(max_{l ≤ N}|Y_l|)²] ≤ 4E[Y_N²]` (`TidyR10DoobDiscrete.doob_sq_discrete`), and in continuous
  time for any modification with almost surely right-continuous paths of a square-integrable
  martingale, `E[(sup_{[s,T]}|M|)²] ≤ 4E[M_T²]` (`TidyR10DoobContinuous.doob_sq_pathSup`); hence
  for Brownian motion (`TidyR10DoobIto.doob_sq_bm`) and for the Itô integral,
  `E[(sup_{[s,T]}|∫ H dW|)²] ≤ 4E[∫_s^T H_u² du]` (`TidyR10DoobIto.doob_sq_itoInt`). The Itô
  integral has a version on `[s, ∞)` adapted to `𝓕` itself, with almost every path continuous, a
  martingale satisfying Doob's bound (`TidyR10DoobVersion.exists_adapted_continuous_itoInt`), also
  for unbounded mean-square continuous integrands
  (`TidyR10DoobMSVersion.exists_adapted_continuous_itoInt_ms`); for the `P`-completed filtration
  (`TidyR10DoobAugment.augment`), which leaves conditional expectations and the Itô integral
  unchanged, EVERY path is continuous (`TidyR10DoobAugment.exists_continuous_itoInt_augment`).
  So Track 1's product step takes a Brownian martingale part, `M = W`
  (`TidyR10DoobProductStep.productStepData_bm`), and `M = ∫ K dW`
  (`TidyR10DoobProductStep.exists_productStepData_itoInt`), with the conclusion
  `E[B_tX_t − B_sX_s | 𝓕_s] = E[∫_s^t X dB | 𝓕_s]` for `𝓕` itself
  (`TidyR10DoobProductStep.product_step_itoInt`). The isometry holds in Fubini form,
  `E[(∫_s^t G dW)²] = ∫_s^t E[G_u²] du` for mean-square continuous `G`
  (`TidyR10DoobFubini.integral_itoInt_sq_ms`).
* **Two Brownian motions.** Two independent Brownian motions with every path continuous and a
  filtration admissible for both exist (`TidyR10TwoBMExist.exists_two_independent_bm`,
  `TidyR10TwoBMExist.TwoBMFiltration`). Their cross variation vanishes:
  `E[(Σ ΔW¹_iΔW²_i)²] = Σ(Δt_i)²` (`TidyR10TwoBMCross.integral_cvSum_sq`), so `dW¹dW² = 0` in
  `L²` along any partitions with mesh `→ 0` (`TidyR10TwoBMCross.L2Tendsto_cvSum`) and almost
  surely along dyadic ones. For Itô processes with two drivers
  (`TidyR10TwoBMIto.ItoProcess2`), Itô's product rule is
  `d(XY) = X dY + Y dX + (H¹K¹ + H²K²) dt` (`TidyR10TwoBMIto.product_rule_two`). The correlated
  motion `W³ = ρW¹ + √(1 − ρ²)W²` (`TidyR10TwoBMIto.corrBM`) is a Brownian motion for `|ρ| ≤ 1`
  (`TidyR10TwoBMCorr.isBrownianReal_corrBM`) with `d[W¹, W³] = ρ dt`. In the (1.32) product
  step the bracket is `σ_B¹σ_X¹ + σ_B²σ_X²` (`TidyR10TwoBMBondStep.twoBM_bond_step`); it vanishes
  when bonds and `Λ/P` load on separate drivers
  (`TidyR10TwoBMBondStep.twoBM_bond_step_separate_drivers`), so the book's step holds with
  `Λ/P = 2 + sin W¹` and bonds `b + c sin W²` (`TidyR10TwoBMBondStep.indepDrv_book_holds`), and
  with correlated shocks it holds iff `ρc = 0` (`TidyR10TwoBMBondStep.corrDrv_book_iff`).
* **Stochastic differential equations and Itô processes with unbounded coefficients.** Itô
  processes with mean-square continuous, possibly unbounded drift and diffusion
  (`TidyR12SDEProcess.ItoProcessMS`) contain those with bounded coefficients
  (`TidyR12SDEProcess.ItoProcess.toItoProcessMS`). For `dX = b(t, X) dt + σ(t, X) dW` on
  `[s, T]`, `X_s = ξ` square integrable and `𝓕_s`-measurable, with `b` and `σ` Lipschitz in `x`
  uniformly on `[s, T]`, `|b(t, 0)| ≤ K` and continuous in `t` against the weight `1 + |x|`
  (`TidyR12SDEPicard.SDECoeff`; linear coefficients `α(t) + β(t)x` with `α, β` continuous
  qualify, `TidyR12SDEPicard.sdeCoeff_linear`), Picard iteration gives a mean-square continuous
  solution, unique among mean-square continuous solutions (`TidyR12SDEExist.sde_existsUnique`,
  from the contraction `TidyR12SDEPicard.picard_sub_sq_le` and `TidyR12SDEPicard.sde_unique`).
  It is an `ItoProcessMS` with drift `b(u, X_u)` and diffusion `σ(u, X_u)`
  (`TidyR12SDEExist.sdeSol_itoProcessMS`) and has an adapted version with almost surely
  continuous paths (`TidyR12SDEVersion.exists_adapted_continuous_sdeSol`). Geometric Brownian
  motion `G_u = ξ·exp(κ(u − s) + σ(W_u − W_s))` solves `dG = (κ + σ²/2)G dt + σG dW`, proved
  from the left-point sums with remainder moments `o(h)` and no Itô formula for `exp`
  (`TidyR12SDEGBM.gbm_eq`, `TidyR12SDEGauss.gbmMean_littleO`, `TidyR12SDEGauss.gbmSq_littleO`); it is
  the solution of that equation (`TidyR12SDEGBM.gbm_eq_sdeSol`), positive for `ξ > 0`, with
  `E_s[G_t] = e^{(κ + σ²/2)(t − s)}G_s` (`TidyR12SDEGBM.gbm_pos`, `TidyR12SDEGBM.condExp_gbm`).
  The exponential martingale solves `dG = σG dW` (`TidyR12SDEGBM.expMart_eq`,
  `TidyR12SDEGBM.condExp_expMart`), and `uW_u` is an `ItoProcessMS` with the unbounded drift `W`
  (`TidyR12SDEGBM.itoProcessMS_mul_bm`). For `X` an `ItoProcessMS` and `Y` an Itô process with
  bounded coefficients and bounded values, `Σ ΔX_iΔY_i → ∫_s^t H_uK_u du` in `L¹`
  (`TidyR12SDEBracket.tendsto_integral_abs_sumCross_ms`) and
  `E_s[X_tY_t − X_sY_s] = E_s[∫_s^t (Xb + Ya + HK) du]` a.s.
  (`TidyR12SDEProductRule.condExp_product_rule_ms`). In the money–bond model with such a `Λ/P`
  (`TidyR12SDEMonetary.ItoMonetaryModelMS`) the corrected (1.32) holds, and its printed line 3
  holds iff `E_s[∫_s^t σ_Xσ_B du] = 0`
  (`TidyR12SDEMonetary.ItoMonetaryModelMS.incr_1_32_ms_general`,
  `TidyR12SDEMonetary.ItoMonetaryModelMS.incr_1_32_ms_book_iff`).
* **(1.32)–(1.34) with diffusive bonds.** For bonds `B` and `X = Λ/P` Itô processes on the same
  Brownian motion, with diffusions `σ_B` and `σ_X`, the step from the middle line of (1.32) to its
  last line is `E_t d(BX) = X dB + B E_t dX + E_t d[B, X]` with `d[B, X] = σ_Bσ_X dt`: almost
  surely `E_s[B_tX_t − B_sX_s] = E_s[∫ Bν du + ∫ Xβ du + ∫ σ_Bσ_X du]`
  (`TidyR7ItoBondStep.bond_step`), also as limits of conditional partition sums
  (`TidyR7ItoBondStep.bond_step_expIncr`). The book's bracket-free step holds iff
  `E_s[∫_s^t σ_Bσ_X du] = 0` (`TidyR7ItoBondStep.bond_step_book_iff`), and for every Itô `Λ/P` iff
  bonds have no diffusion (`TidyR7ItoBondStep.bookForm_forall_iff`). In the money–bond model with
  Itô `Λ/P`, bonds and money and the flow (1.31) imposed on the coefficients
  (`TidyR7MonetarismIto.ItoMonetaryModel`; diffusive bonds force `σ_M = −σ_B`), line 1 of (1.32)
  holds as a rate identity (`TidyR7MonetarismIto.ItoMonetaryModel.line1_1_32_rate`), line 2
  verbatim (`TidyR7MonetarismIto.ItoMonetaryModel.middle_1_32_ito`), line 3 gains the bracket, `E_s[n_tB_t − n_sB_s] = E_s[−(∫ (Λs − i^m nM) du + ∫ n dM) + ∫ σ_Xσ_B du]`
  (`TidyR7MonetarismIto.ItoMonetaryModel.incr_1_32_ito_general`), and holds as printed iff
  `E_s[∫_s^t σ_Xσ_B du] = 0` (`TidyR7MonetarismIto.ItoMonetaryModel.incr_1_32_ito_book_iff`).
  Valuation (1.33) holds iff transversality with `−∫ σ_Xσ_B du` in the flow
  (`TidyR7MonetarismItoValuation.valuation_1_33_ito`), and as printed, under transversality, iff
  `E_s[∫_s^{T_k} σ_Xσ_B du] → 0` (`TidyR7MonetarismItoValuation.valuation_1_33_ito_book_iff`);
  (1.34) holds verbatim (`TidyR7MonetarismItoValuation.valuation_1_34_ito`). With `Λ/P = 1 + W`
  and bonds `b + cW` the printed line 3 fails, `1 ≠ 0` for `c = 1`
  (`TidyR7MonetarismItoCex.cex_headline`); with bonds and `Λ/P` diffusing on disjoint time
  intervals it holds (`TidyR7MonetarismItoCex.disj_1_32`); on `[0, ∞)` transversality holds while
  the printed (1.33) gives `0 ≠ 1/3` (`TidyR7MonetarismItoCexInf.inf_headline`). The dominated
  (1.33) with the bracket holds iff transversality: if the corrected flows converge almost surely
  under an integrable dominator, `n_sB_s = E_s[G]` a.s. iff `E_s[n_{T_k}B_{T_k}] → 0` a.s.
  (`TidyR8MonetarismItoDom.valuation_1_33_ito_dom`). Under pathwise hypotheses (a.s. continuous
  drift integrands, drift flow and bracket density integrable to infinity, an a.s. convergent
  dominated Itô part) the flows converge and are dominated, and the book's bracket-free
  dominated (1.33) holds iff `E_s[∫_s^∞ σ_Xσ_B du] = 0`
  (`TidyR8MonetarismItoDom.valuation_1_33_ito_dom_pathwise`); on the `[0, ∞)` economy these
  hypotheses hold, `n_0B_0 = 1/3 = E_0[G]`, and the book's form fails, `0 ≠ 1/3`
  (`TidyR8MonetarismItoDomInf.itoDomInf_headline`).
  The counterexamples persist with a positive diffusive `Λ/P`. With `P = 1` and
  `Λ/P = Λ = 2 + sin W ∈ [1, 3]` the bond-pricing drift forces the random adapted rate
  `i = sin W/(2(2 + sin W))`, `|i| ≤ 1/2`; with bonds `b + c sin W` and money `M₀ − c sin W` this
  is a `TidyR7MonetarismIto.ItoMonetaryModel` (`TidyR9MonetarismItoPositive.posModel`), and for
  every `c ≠ 0` and `t > 0` the printed line 3 of (1.32) fails on `[0, t]`, the bracket having
  mean `cE∫_0^t cos²W du ≠ 0`, while the corrected line holds
  (`TidyR9MonetarismItoPositive.pos_headline`). With unbounded coefficients the random rate is
  not needed: with `P = 1`, `Λ/P = n₀e^{−iu}exp(σW_u − σ²u/2) > 0` for a constant known rate
  `i`, so that `E_s[n_t] = e^{−i(t − s)}n_s`, bonds `b₀ + c·arctan W` and money `M₀ − c·arctan W`
  (`TidyR12SDEMonetaryGBM.gbmModel`, a `TidyR12SDEMonetary.ItoMonetaryModelMS`), the printed
  line 3 of (1.32) fails on every `[s, t]`, `0 ≤ s < t`, for every `σ ≠ 0` and `c ≠ 0`, while
  the corrected line holds (`TidyR12SDEMonetaryGBM.gbm_book_fails`,
  `TidyR12SDEMonetaryGBM.gbm_headline`); with `c = 0` the printed line holds although `Λ/P`
  diffuses (`TidyR12SDEMonetaryGBM.gbm_book_holds_bv`). With time-varying loadings,
  `Λ/P = 2 + φ(u) sin W ∈ [1, 3]`, bonds and `Λ/P` diffusing on disjoint time sets satisfy the
  printed (1.32) (`TidyR9MonetarismItoPositiveInf.disjP_1_32`), and on `[0, ∞)` the
  transversality condition holds exactly while the bracket stays below `−κ < 0` and the printed
  (1.33) fails (`TidyR9MonetarismItoPositiveInf.infP_headline`). With bonds and `Λ/P` on two
  independent shocks the bracket is `σ_B¹σ_X¹ + σ_B²σ_X²`
  (`TidyR10TwoBMBondStep.twoBM_bond_step`), and the book's step holds when bonds load only on one
  shock and `Λ/P` only on the other, however diffusive both are
  (`TidyR10TwoBMBondStep.twoBM_bond_step_separate_drivers`): with `Λ/P = 2 + sin W¹ ∈ [1, 3]` and
  bonds `b + c sin W²` it holds on every `[s, t]`
  (`TidyR10TwoBMBondStep.indepDrv_book_holds`), while with correlated shocks,
  `Λ/P = 2 + arctan W¹ > 0` and bonds `b + cW³`, it holds on `[s, t]` iff `ρc = 0`
  (`TidyR10TwoBMBondStep.corrDrv_book_iff`). Diffusive bonds that also jump with `Λ/P` are
  covered by the unified step of the next item
  (`TidyR11JumpDiffStep.JumpDiffData.jump_diff_step`), which without jumps and with `C¹` drifts
  is the form of `TidyR7ItoBondStep.bond_step`
  (`TidyR11JumpDiffStep.JumpDiffData.jd_recovers_bond_step`).
* **The (1.32) step with jumps and diffusion together.** For `Λ/P = X = A + M_d + M_c` and bonds
  `B = B_bv + B_c`, with `A` and `B_bv` adapted, càdlàg and of bounded variation, `M_d` a càdlàg
  bounded-variation martingale and `M_c = ∫K dW`, `B_c = ∫σ_B dW` driftless Itô processes with
  every path continuous (`TidyR11JumpDiffStep.JumpDiffData`), almost surely
  `E_s[B_tX_t − B_sX_s] = E_s[∫ X_− dB_bv] + E_s[∫ B_− dA] + E_s[∫_s^t σ_BK du] +
  E_s[Σ_{s<u≤t} ΔB_uΔX_u]` (`TidyR11JumpDiffStep.JumpDiffData.jump_diff_step`). The last two
  terms are the full covariation `[B, X]_t − [B, X]_s` (`TidyR11JumpDiffStep.fullCov`,
  `TidyR11JumpDiffStep.JumpDiffData.jump_diff_step_fullCov`), and the book's two-term step holds
  iff its conditional expectation vanishes (`TidyR11JumpDiffStep.JumpDiffData.jd_book_iff`). The
  proof splits `BX` into four products and applies
  `TidyR7ProductStepJump.JumpStepData.jump_step` to three of them and
  `TidyR7ItoProductRule.condExp_product_rule` to the fourth. Without diffusion the step is the
  jump step (`TidyR11JumpDiffStep.JumpDiffData.jd_recovers_jump_step`), without jumps and with
  `C¹` drifts the form of `TidyR7ItoBondStep.bond_step`
  (`TidyR11JumpDiffStep.JumpDiffData.jd_recovers_bond_step`), with neither
  `TidyR7ProductStep.ProductStepData.product_step`
  (`TidyR11JumpDiffStep.JumpDiffData.jd_recovers_product_step`). Under the flow (1.31), with
  `B_bv + M_bv` continuous and `σ_B = −σ_M`, the covariation of bonds with `Λ/P` is minus that of
  money path by path (`TidyR11JumpDiffMoney.fullCov_bonds_eq_neg_money`), so the omitted term is
  `−E_s([M, Λ/P]_t − [M, Λ/P]_s)` (`TidyR11JumpDiffMoney.jump_diff_step_money`,
  `TidyR11JumpDiffMoney.jump_diff_book_iff_money`). On a Brownian motion with an independent fair
  coin revealed at time 1 (`TidyR11JumpDiffCoinBM.cbF_isBM`, `TidyR11JumpDiffCoinBM.martingale_cbJ`),
  with `Λ/P = eξ1{u≥1} + dW` and bonds `eξ1{u≥1} + cW` on `[0, 2]`, the continuous covariation is
  `2cd` and the jump covariation `e²` (`TidyR11JumpDiffCoinBMStep.jdcb_fullCov`); the book's step
  holds iff `2cd + e² = 0` (`TidyR11JumpDiffCoinBMStep.jdcb_book_iff`), fails for `c = d = e = 1`,
  `2 + 1 ≠ 0` (`TidyR11JumpDiffCoinBMStep.jdcb_book_fails`), and holds for `c = −1/2`, `d = e = 1`,
  where both parts are nonzero and cancel, `−1 + 1 = 0` (`TidyR11JumpDiffCoinBMStep.jdcb_cancel`).
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
* the product step `E_td(BΛ/P)` of Online Appendix §1.6 (1.32) for bonds with a martingale part
  that is not an Itô process, and parts of the diffusive case. They need a stochastic integral
  and the bracket `[X, B]`, which Mathlib does not have; both are built here. A Brownian motion
  exists
  (`TidyR7BrownianExist.exists_isBrownianReal`), with its martingale tools, and its bracket
  `[W]_t = t` is proved (in `L²`, in probability, almost surely along dyadic partitions and
  conditionally, `TidyR7BrownianQV`); its paths have infinite variation almost surely, so the
  bounded-variation product step provably excludes diffusive bonds
  (`TidyR7BrownianVariation.not_productStepData_bm`), and its bracket with bonds of continuous
  bounded-variation paths is `0` (`TidyR7BrownianVariation.ae_tendsto_sumCross_bm_bv`). The Itô
  integral exists for mean-square continuous integrands (`TidyR7ItoUnbounded.MSIntegrand`,
  `TidyR7ItoUnbounded.L2Tendsto_itoSum_ms`), which include the bounded adapted almost surely
  continuous ones, Itô processes and their products with bounded ones, with the isometry,
  linearity, the martingale property, the conditional isometry, the Fubini isometry
  (`TidyR10DoobFubini.integral_itoInt_sq_ms`), Doob's bound (`TidyR10DoobIto.doob_sq_itoInt_ms`)
  and an adapted version on `[s, ∞)` with almost every path continuous
  (`TidyR10DoobMSVersion.exists_adapted_continuous_itoInt_ms`); it agrees with Track 1 for bounded-variation integrands
  (`TidyR7ItoBridge.itoInt_eq_byParts`), `∫ W dW = (W_t² − W_s² − (t − s))/2`
  (`TidyR7ItoBridge.itoInt_bm`), and `∫ cH dW = c∫ H dW` for square-integrable
  `𝓕_s`-measurable `c` (`TidyR7ItoProducts.itoInt_mul_left`). Itô's product rule with
  covariation `d[X, Y] = HK dt` is proved for Itô processes, almost surely
  (`TidyR7ItoProductRule.product_rule`), conditionally on `𝓕_s`
  (`TidyR7ItoProductRule.condExp_product_rule`) and in the expected-increment form
  (`TidyR7ItoProductRule.expected_increment_product_rule`); the book's bracket-free form holds
  iff `E_s[∫_s^t HK du] = 0` (`TidyR7ItoProductRule.condExp_product_rule_bookForm_iff`) and
  fails for `X = Y = W` (`TidyR7ItoProductRule.not_bookForm_bmPath`). The general step in the
  book's economy is done: for Itô bonds and Itô `Λ/P` the step has the bracket
  `E_t d[B, Λ/P] = σ_Bσ_X dt`
  (`TidyR7ItoBondStep.bond_step`), and (1.32)–(1.34) hold in `TidyR7MonetarismIto.ItoMonetaryModel`
  with the bracket in line 3 of (1.32) and in the flow of (1.33)
  (`TidyR7MonetarismIto.ItoMonetaryModel.incr_1_32_ito_general`,
  `TidyR7MonetarismItoValuation.valuation_1_33_ito`, `TidyR7MonetarismItoValuation.valuation_1_34_ito`).
  A positive diffusive `Λ/P` is done. With bounded coefficients, Itô's formula with time
  dependence, for `1/X` and for `exp X` (`TidyR9ItoFormula.ito_formula_time`,
  `TidyR9ItoFormulaVariants.itoProcess_inv`, `TidyR9ItoFormulaVariants.itoProcess_exp`) gives
  `Λ/P = 2 + sin W ∈ [1, 3]` with a random nominal rate `i`, and the counterexamples
  for (1.32), for disjoint diffusions and for the infinite-horizon (1.33) hold with `Λ/P > 0`
  throughout (`TidyR9MonetarismItoPositive.pos_headline`,
  `TidyR9MonetarismItoPositiveInf.disjP_1_32`, `TidyR9MonetarismItoPositiveInf.infP_headline`).
  With unbounded coefficients (`TidyR12SDEProcess.ItoProcessMS`), the geometric Brownian motion
  `Λ/P = n₀e^{−iu}exp(σW_u − σ²u/2)` has a constant known rate `i`, and the printed line 3 of
  (1.32) fails inside the money–bond model `TidyR12SDEMonetary.ItoMonetaryModelMS` on every
  `[s, t]`, `0 ≤ s < t` (`TidyR12SDEMonetaryGBM.gbm_book_fails`,
  `TidyR12SDEMonetaryGBM.gbm_headline`; inside the bounded-coefficient
  `TidyR7MonetarismIto.ItoMonetaryModel` it is shown only on `[0, t]`,
  `TidyR9MonetarismItoPositive.pos_book_fails`). Stochastic differential equations with Lipschitz
  coefficients have unique solutions (`TidyR12SDEExist.sde_existsUnique`) with adapted almost
  surely continuous versions (`TidyR12SDEVersion.exists_adapted_continuous_sdeSol`), geometric
  Brownian motion is one (`TidyR12SDEGBM.gbm_eq_sdeSol`), and `exp(σW − σ²t/2)` is an Itô process
  with mean-square continuous coefficients (`TidyR12SDEGBM.expMart_eq`).
  What remains: for these equations, uniqueness among solutions that are not mean-square
  continuous, coefficients without the time continuity of `TidyR12SDEPicard.SDECoeff`, systems
  and several Brownian motions (one dimension and one driver only), and continuous versions for
  `W` without almost surely continuous paths or for `s = T`; Itô's formula for
  `TidyR12SDEProcess.ItoProcessMS`; the almost sure product rule for an `ItoProcessMS` against
  an Itô process with bounded coefficients (only the conditional form,
  `TidyR12SDEProductRule.condExp_product_rule_ms`; it needs `Σ Y_iI_i → ∫ YH dW`), and any
  product rule with both factors unbounded (it needs `L⁴` bounds); (1.33)–(1.34), the infinite
  horizon and the dominated forms in `TidyR12SDEMonetary.ItoMonetaryModelMS` (only the (1.32)
  step is restated there); Itô's formula
  without path continuity of `X` as a hypothesis (`TidyR7ItoProcess.ItoProcess` is specified at
  fixed times; adapted continuous versions of `∫ H dW` are proved,
  `TidyR10DoobVersion.exists_adapted_continuous_itoInt`, but none of `X_s + ∫ a dr + ∫ φ dW` is
  packaged or used in Itô's formula); Itô's formula
  with `f''` unbounded, or localised by stopping times (`f''` is bounded globally and
  localisation is only by deterministic bounds on the range, so `1/W` is not covered and
  `exp(σW)` only directly, from the left-point sums, `TidyR12SDEGBM.gbm_eq`); Itô's formula for `f(X, Y)`,
  with one or with two drivers (only one-dimensional `f(t, X)`); Itô
  processes whose drift or diffusion is merely measurable, or unbounded without mean-square
  continuity (`TidyR7ItoProcess.ItoProcess` has bounded coefficients with almost surely
  continuous paths; `TidyR12SDEProcess.ItoProcessMS` admits unbounded mean-square continuous
  ones, among them geometric Brownian motion and `uW_u`, `TidyR12SDEGBM.gbm_itoProcessMS`,
  `TidyR12SDEGBM.itoProcessMS_mul_bm`, but of the results built on `TidyR7ItoProcess.ItoProcess`
  only the bracket, the conditional product rule and the (1.32) step are redone for it); pathwise time integrals in the model statements (they use the
  mean-square `TidyR7ItoProducts.dtInt`, which equals the pathwise integral a.s. for a.s.
  continuous paths, `TidyR7ItoProducts.dtInt_ae_eq_integral`; only the corrected flow of
  (1.33) and Itô's formula are restated path by path,
  `TidyR8MonetarismItoDom.flowItoC_pathwise`, `TidyR9ItoFormula.ito_formula_pathwise`,
  `TidyR9ItoFormulaVariants.ito_formula_time_pathwise`); the dominated
  form of (1.33) with the bracket without assuming that the Itô part
  `J_k = ∫_s^{T_k} nσ_M dW` converges almost surely under an integrable dominator
  (`TidyR8MonetarismItoDom.valuation_1_33_ito_dom_pathwise` takes it as a hypothesis, verified
  when money's diffusion vanishes after a date, `TidyR8MonetarismItoDom.itoInt_eventually_const`;
  the Doob bound and the Fubini isometry are now proved, `TidyR10DoobIto.doob_sq_itoInt_ms`,
  `TidyR10DoobFubini.integral_itoInt_sq_ms`, but the general case is not derived from them), or
  with drift integrands that are not almost surely continuous;
  more than two Brownian motions (two independent ones with a common filtration and
  `dW¹dW² = 0` are proved, `TidyR10TwoBMExist.exists_two_independent_bm`,
  `TidyR10TwoBMCross.L2Tendsto_cvSum`; `n > 2` drivers are not packaged, and correlated motions
  are built only from an independent pair, `TidyR10TwoBMIto.corrBM`); the money–bond model
  (1.31)–(1.34) with two drivers (only its (1.32) product step is restated,
  `TidyR10TwoBMBondStep.twoBM_bond_step`); a full jump-diffusion money–bond model with the
  valuation equations (1.33)–(1.34) (the unified (1.32) step is done,
  `TidyR11JumpDiffStep.JumpDiffData.jump_diff_step`, in terms of money,
  `TidyR11JumpDiffMoney.jump_diff_step_money`, with an instance in which the continuous and jump
  parts cancel, `TidyR11JumpDiffCoinBMStep.jdcb_cancel`; the models (1.31)–(1.34) with jumps and
  with diffusion remain separate, `TidyR7MonetarismJump.JumpMonetaryModel` and
  `TidyR7MonetarismIto.ItoMonetaryModel`); a positive `Λ/P` in a jump-diffusion instance (the
  instance has `Λ/P = eξ1{u≥1} + dW`; a positive one needs an adapted version of `∫ cos W dW` with
  every path continuous, adaptedness of `∫ sin W dr` and measurability of its path variation);
  Itô parts with drift inside `TidyR11JumpDiffStep.JumpDiffData` (`B_c` and `M_c` are driftless;
  the drifts sit in the bounded-variation parts); a constructor of
  `TidyR11JumpDiffStep.JumpDiffData` from the data of `TidyR7ProductStepJump.JumpStepData` alone
  (it also needs `A` adapted and `M_d` of bounded variation); the no-jump reduction with the
  mean-square time integrals of `TidyR7ItoBondStep.bond_step`
  (`TidyR11JumpDiffStep.JumpDiffData.jd_recovers_bond_step` uses pathwise ones, and
  `TidyR7ItoProducts.dtInt_ae_eq_integral` is not applied to restate it); an expected-increment
  form of the unified step; the value of the instance's first term `E_0[∫ X_− dB_bv]`; the
  unified step, like `TidyR7ItoBondStep.bond_step`, assumes bounded almost surely continuous Itô
  coefficients, and it assumes every path of `B_c` and `M_c` continuous; the bracket of Itô processes in `L²`, with one or two drivers (only in
  `L¹`; for the raw motions `(dW)² = dt` and `dW¹dW² = 0` hold in `L²`; it needs `E[(∫ H dW)⁴] ≤ cC⁴(b − a)²`, a Burkholder–Davis–Gundy inequality with `p = 4`
  or Itô's formula for `x⁴`, whose `f''` is unbounded). `M = W` and `M = ∫ K dW` in
  `TidyR7ProductStep.ProductStepData` are covered (`TidyR10DoobProductStep.productStepData_bm`,
  `TidyR10DoobProductStep.exists_productStepData_itoInt`, the latter for the completed filtration
  with the conclusion stated for `𝓕_s`, `TidyR10DoobProductStep.product_step_itoInt`), but the
  bonds' variation `Var_{[s,t]}(B)` is assumed measurable and bounded and the instances use the
  deterministic `B_u = u`; and the data with a mean-square continuous, unbounded `K` are not
  derived. Doob's inequality is proved for `p = 2` only, and for `s < T` (the degenerate `s = T`
  is not stated). Infrastructure that the results above do not use is also
  not proved: a version of `∫ G dW` with every path continuous for an unbounded mean-square
  continuous `G` (only almost every path,
  `TidyR10DoobMSVersion.exists_adapted_continuous_itoInt_ms`; every path for bounded integrands
  and the completed filtration, `TidyR10DoobAugment.exists_continuous_itoInt_augment`); a
  counterexample showing that an `𝓕`-adapted version with every path continuous needs the
  completion; the conditional form of the cross-variation `L²` identity of two motions (only
  with a bounded `𝓕_s`-measurable weight, `TidyR10TwoBMCross.integral_mul_wcvSum_sq`); integrands
  `X·Y` with both factors
  unbounded (only `X·K` with `K` bounded); `Σ ΔXΔB → 0` for a general continuous
  bounded-variation `B` (only for `B` an Itô process with zero diffusion); a measurable
  modification of an arbitrary `IsBrownianReal` and the usual augmentation of its filtration
  (only the `P`-completion, `TidyR10DoobAugment.augment`, without right continuity; the joint
  filtration of two motions is their natural one).
  Adapted bonds of bounded variation are covered, with
  continuous paths (`TidyR7ProductStep.ProductStepData.product_step`) and with càdlàg paths that
  jump together with `Λ/P` (`TidyR7ProductStepJump.JumpStepData.jump_step`). The domination and
  integrability conditions of `TidyR7ProductStep.ProductStepData` and
  `TidyR7ProductStepJump.JumpStepData` are sufficient; their necessity is not proved (only adaptedness of `B` is shown necessary,
  `TidyR7ProductStepCoin.coin_anticipating_fails`). The chain (1.31)–(1.34) built on it
  (`TidyR7MonetarismModel`, `TidyR7MonetarismValuation`, `TidyR7MonetarismJump`) inherits these
  limits; with jumping money it assumes `B + M` continuous (no atom in the surplus). The
  infinite-horizon failure of the pre-jump reading of (1.33)
  (`TidyR8MonetarismJumpInf.jumpInf_headline`) is stated as `n_0B_0 ≠ E_0[G⁻]`, not restated
  in the real form `B_0/P_0`;
* a `TidyR7MonetarismModel.MonetaryModel` economy in which the printed (1.33) holds while the
  flows do not converge in `L¹`: the integrable lower bound of
  `TidyR8MonetarismUISharp.valuation_iff_L1_char` is shown necessary for "printed ⇒ `L¹`" only
  in a generic budget system on `ℕ` (`TidyR8MonetarismUISharp.sgn_headline`,
  `TidyR8MonetarismUISharp.sgn_no_lower_bound`);
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
| [TidyR7BrownianQV](Monetarism/TidyR7BrownianQV.lean) | 48 | A1 §1.6, pp. 567–568 (tool for (1.32) with diffusive bonds): the quadratic variation of a pre-Brownian motion along partitions: `E(ΔW)² = Δt`, `Var((ΔW)²) = 2Δt²`, admissible filtrations, `(ΔW)² − Δt` orthogonal to the past, the exact identity `E[(Σ(ΔW_i)² − (t − s))²] = 2Σ(Δt_i)²` and its weighted and conditional forms, `Σ(ΔW_i)² → t − s` in `L²`, in probability and almost surely along dyadic partitions, the weighted rule `(dW)² = dt` in `L²` |
| [TidyR7BrownianVariation](Monetarism/TidyR7BrownianVariation.lean) | 17 | A1 §1.6, (1.32), pp. 567–568: almost surely Brownian paths have infinite variation on every interval; no bounded-variation product-step data has a Brownian bond; `dW·dB = 0` for continuous bounded-variation `B` and `dW·dt = 0`; non-vacuity on the constructed motion |
| [TidyR7ItoL2](Monetarism/TidyR7ItoL2.lean) | 20 | A1 §1.6, pp. 567–568 (tool for the Itô integral): mean-square convergence, completeness of `L²` with an adapted limit, uniqueness and linearity of limits, an `L²` and an a.s. limit agree, Cauchy–Schwarz, `E[GX_k] → E[GY]` and `E[GX_k²] → E[GY²]`, Riemann sums, mean-square uniform continuity of a.s. continuous bounded processes |
| [TidyR7ItoSums](Monetarism/TidyR7ItoSums.lean) | 44 | A1 §1.6, pp. 567–568 (tool for the Itô integral): increments orthogonal to the past, elementary integrals and their weighted `L²` identity, left-point sums, the discrete Itô isometry and its conditional form, `E[I_p(H) \| 𝓕_s] = 0`, the common refinement and the Cauchy estimate, concatenation |
| [TidyR7ItoIntegral](Monetarism/TidyR7ItoIntegral.lean) | 32 | A1 §1.6, pp. 567–568 (the stochastic integral for (1.32) with diffusive bonds): admissible integrands, the Itô integral as an adapted mean-square limit along any partitions, the Itô isometry, linearity, additivity over intervals, the martingale property and the conditional isometry |
| [TidyR7ItoBridge](Monetarism/TidyR7ItoBridge.lean) | 16 | A1 §1.6, (1.32), pp. 567–568: for bounded-variation integrands the Itô integral is Track 1's integral by parts, `dH·dW = 0`, Wiener integrals and their isometry; `∫_s^t W dW = (W_t² − W_s² − (t − s))/2`, not the Stratonovich value, and its isometry on the constructed motion |
| [TidyR7ItoContinuity](Monetarism/TidyR7ItoContinuity.lean) | 16 | A1 §1.6, pp. 567–568: Kolmogorov's maximal inequality, stopped left-point sums and restricted partitions, a modification of `t ↦ ∫_s^t H dW` with a.s. continuous paths on `[s, T]` |
| [TidyR7ItoUnbounded](Monetarism/TidyR7ItoUnbounded.lean) | 23 | A1 §1.6, pp. 567–568 (the integrands `X·K` of (1.32) with diffusive bonds): mean-square continuous integrands without bound or path regularity, the `L²` cell identity with unbounded coefficients, existence of `∫ G dW` along any partitions, the isometry as a limit of Riemann sums, `E_r ∫_r^t G dW = 0` |
| [TidyR7ItoProducts](Monetarism/TidyR7ItoProducts.lean) | 19 | A1 §1.6, pp. 567–568: products `X·K` with bounded admissible `K` are mean-square continuous, `∫ ZK dW = Z∫ K dW` for square-integrable `𝓕_r`-measurable `Z`, the time integral `∫ G du` in mean square and its agreement with the pathwise one |
| [TidyR7ItoProcess](Monetarism/TidyR7ItoProcess.lean) | 18 | A1 §1.6, pp. 567–568 (bonds and `Λ/P` in (1.32) with diffusive bonds): Itô processes `X_s + ∫ a dr + ∫ H dW`, their increments and mean-square modulus, Itô processes as mean-square continuous integrands, the drift error, `L²`/`L¹` tools |
| [TidyR7ItoCovariation](Monetarism/TidyR7ItoCovariation.lean) | 14 | A1 §1.6, (1.32), pp. 567–568: `Σ X_iΔY_i → ∫ X b du + ∫ X K dW` in `L²`, the bracket `Σ ΔX_iΔY_i → ∫ HK du` in `L¹`, and no bracket when one factor has no diffusion |
| [TidyR7ItoProductRule](Monetarism/TidyR7ItoProductRule.lean) | 22 | A1 §1.6, (1.32), pp. 567–568: Itô's product rule with covariation (a.s., conditional on `𝓕_s`, expected-increment form), Itô's formula for `x²`, the book's bracket-free form iff `E_s∫HK du = 0`, the link to Track 1's product step, `W` and the clock as Itô processes, and the failure of the book form for `X = Y = W` |
| [TidyR7ItoBondStep](Monetarism/TidyR7ItoBondStep.lean) | 15 | A1 §1.6, (1.32), p. 567: the general product step for Itô bonds and Itô `Λ/P` with the bracket `σ_Bσ_X dt` (conditional and expected-increment forms), the book's step iff `E_s∫σ_Bσ_X du = 0`, and for every Itô `Λ/P` iff bonds have no diffusion; linearity of the mean-square time integral |
| [TidyR7MonetarismIto](Monetarism/TidyR7MonetarismIto.lean) | 16 | A1 §1.6, (1.31)–(1.34), pp. 567–568: the money–bond model with Itô `Λ/P`, bonds and money (`σ_M = −σ_B`, `B + M` locally riskless); lines 1–2 of (1.32) verbatim, line 3 corrected with the bracket and as printed iff its conditional mean vanishes; the line before (1.34) verbatim |
| [TidyR7MonetarismItoValuation](Monetarism/TidyR7MonetarismItoValuation.lean) | 15 | A1 §1.6, (1.33)–(1.34), p. 567: the finite-horizon budget with the bracket; the corrected (1.33) iff transversality (limit and `L¹` forms); the printed (1.33) under transversality iff the bracket vanishes in the limit; (1.34) verbatim |
| [TidyR7MonetarismItoCex](Monetarism/TidyR7MonetarismItoCex.lean) | 19 | A1 §1.6, (1.31)–(1.34), pp. 567–568: on the constructed motion, `Λ/P = 1 + W` with bonds `b + cW` breaks the printed line 3 of (1.32) (`1 ≠ 0` at `c = 1`) while the corrected line and (1.34) hold; bonds and `Λ/P` diffusing on disjoint intervals satisfy the printed (1.32) and (1.33) |
| [TidyR7MonetarismItoCexInf](Monetarism/TidyR7MonetarismItoCexInf.lean) | 13 | A1 §1.6, (1.32)–(1.33), p. 567: on `[0, ∞)` with bonds diffusing against `Λ/P`, transversality and the corrected (1.33) hold while the printed (1.33) fails (`0 ≠ 1/3`) |
| [TidyR8MonetarismUISharp](Monetarism/TidyR8MonetarismUISharp.lean) | 26 | A1 §1.6, (1.33)–(1.34), p. 567: the sharp condition for the printed `E_s∫_s^∞` forms: with flows converging a.s. and bounded below by an integrable function, printed iff `L¹` convergence (iff uniform integrability, Vitali) and iff conditional `L¹` convergence; in the economy for (1.33) and (1.34); the earlier counterexample and coin economy as instances; the lower bound cannot be dropped; conditional dominated convergence with a.s. hypotheses and (conditional) Scheffé |
| [TidyR8MonetarismItoDom](Monetarism/TidyR8MonetarismItoDom.lean) | 9 | A1 §1.6, (1.33), p. 567: the dominated (1.33) with the bracket for diffusive bonds iff transversality; under pathwise hypotheses, with the book's bracket-free dominated form iff `E_s∫_s^∞σ_Xσ_B du = 0`; the corrected flow path by path; additivity and eventual constancy of the Itô integral |
| [TidyR8MonetarismItoDomInf](Monetarism/TidyR8MonetarismItoDomInf.lean) | 11 | A1 §1.6, (1.33), p. 567: on economy 3 on `[0, ∞)` the hypotheses of the dominated (1.33) hold; with the bracket `n_0B_0 = 1/3 = E_0[G]`, the book's dominated form fails (`0 ≠ 1/3`) |
| [TidyR8MonetarismMoneyInf](Monetarism/TidyR8MonetarismMoneyInf.lean) | 31 | A1 §1.6, (1.31)–(1.34), pp. 567–568: an infinite-horizon economy with nonzero money and interest on money and a decaying discount factor with news (`M = B = 2`, `i = 1`, `i^m = 1/2`); transversality holds and the printed and `L¹` forms of (1.34) hold, both sides `4` |
| [TidyR8MonetarismJumpInf](Monetarism/TidyR8MonetarismJumpInf.lean) | 23 | A1 §1.6, (1.31)–(1.34), pp. 567–568: an open-market operation at the news date on `[0, ∞)`: transversality and the post-jump dominated (1.33) hold, the pre-jump (1.33) fails (`2 ≠ 2 − e^{−1}/2`, the jump covariation `e^{−1}/2`); (1.34) verbatim with jumping money |
| [TidyR9ExpMartingale](Monetarism/TidyR9ExpMartingale.lean) | 3 | A1 §1.6, pp. 567–568: the lognormal discount factor `exp(σW − σ²t/2)` has mean one and is a martingale, `E_s[Λ_t/Λ_s] = 1`, from the Gaussian law of the increment; on the constructed motion |
| [TidyR9ItoTaylor](Monetarism/TidyR9ItoTaylor.lean) | 4 | A1 §1.6, pp. 567–568 (tool for Itô's formula): Taylor bounds with second-order remainder in space and first-order in time, Lipschitz from a bounded derivative, and the uniform estimate along a continuous path |
| [TidyR9ItoPathSums](Monetarism/TidyR9ItoPathSums.lean) | 6 | A1 §1.6, pp. 567–568 (tool for Itô's formula): the exact partition identity for `f(t, x_t)`, the time sum and its limit `∫ f_t du`, and the Taylor remainder `o(Σ(Δx)²)` |
| [TidyR9ItoWeightedBracket](Monetarism/TidyR9ItoWeightedBracket.lean) | 5 | A1 §1.6, pp. 567–568 (tool for Itô's formula): the weighted bracket `Σ G_iΔX_iΔY_i → ∫ GHK du` in `L¹` for a bounded adapted weight with a.s. continuous paths; the weight `1` gives back the bracket |
| [TidyR9ItoFormula](Monetarism/TidyR9ItoFormula.lean) | 16 | A1 §1.6, pp. 567–568: Itô's formula with time dependence and for `f ∈ C²` with `f''` bounded, with pathwise time integrals, `f(X)` as an Itô process, the conditional form, `x²` recovered, and `sin W` on the constructed motion |
| [TidyR9ItoFormulaVariants](Monetarism/TidyR9ItoFormulaVariants.lean) | 17 | A1 §1.6, pp. 567–568: localisation to `[s, t]`, `f(X)` with `f'` bounded on the range, `f(u, X_u)` and discounting `e^{−ru}g(X)` as Itô processes, `1/X` for `X ≥ c > 0` and `exp X` for `\|X\| ≤ M` |
| [TidyR9MonetarismItoPositive](Monetarism/TidyR9MonetarismItoPositive.lean) | 11 | A1 §1.6, (1.31)–(1.34), pp. 567–568: the economy `Λ/P = 2 + sin W ∈ [1, 3]` with the forced random rate, bonds `b + c sin W`; the printed line 3 of (1.32) fails on `[0, t]` for `c ≠ 0` with `Λ > 0` throughout, the corrected line and (1.34) hold |
| [TidyR9MonetarismItoPositiveInf](Monetarism/TidyR9MonetarismItoPositiveInf.lean) | 18 | A1 §1.6, (1.32)–(1.33), p. 567: time-varying loadings, `Λ/P = 2 + φ(u) sin W ∈ [1, 3]`; disjoint diffusions satisfy the printed (1.32) and (1.33) iff transversality; on `[0, ∞)` transversality holds exactly while the printed (1.33) fails |
| [TidyR10DoobDiscrete](Monetarism/TidyR10DoobDiscrete.lean) | 18 | A1 §1.6, pp. 567–568 (tool for (1.32) with diffusive bonds): the running maximum and its increments, the pathwise bound `S_N² ≤ 2Σ\|Y_l\|D_l`, and Doob's `L²` inequality `E[(max_{l ≤ N}\|Y_l\|)²] ≤ 4E[Y_N²]` in discrete time from orthogonal increments |
| [TidyR10DoobContinuous](Monetarism/TidyR10DoobContinuous.lean) | 11 | A1 §1.6, pp. 567–568 (tool): dyadic grids and their maxima, Doob's `L²` inequality on a grid and in continuous time for a modification with a.s. right-continuous paths, and for a Mathlib martingale |
| [TidyR10DoobIto](Monetarism/TidyR10DoobIto.lean) | 9 | A1 §1.6, pp. 567–568: Doob's inequality for Brownian motion and for `∫ G dW` (mean-square continuous and bounded integrands), orthogonal increments of the Itô integral, on the constructed motion |
| [TidyR10DoobVersion](Monetarism/TidyR10DoobVersion.lean) | 7 | A1 §1.6, pp. 567–568: left dyadic limits, and a version of `∫ H dW` on `[s, ∞)` adapted to `𝓕` itself, a.s. continuous, a martingale with Doob's bound |
| [TidyR10DoobAugment](Monetarism/TidyR10DoobAugment.lean) | 9 | A1 §1.6, pp. 567–568: the `P`-completed filtration, admissible, with the same conditional expectations and Itô integral, and a version of `∫ H dW` with every path continuous adapted to it |
| [TidyR10DoobProductStep](Monetarism/TidyR10DoobProductStep.lean) | 12 | A1 §1.6, (1.32), p. 567: the product step of Track 1 with a martingale part `M = W` or `M = ∫ K dW` (the latter for the completed filtration, its conclusion for `𝓕_s`), with bounded-variation bonds; on the constructed motion |
| [TidyR10DoobFubini](Monetarism/TidyR10DoobFubini.lean) | 6 | A1 §1.6, pp. 567–568: continuity of `u ↦ E[G_u²]`, the Itô isometry in Fubini form `E[(∫ G dW)²] = ∫ E[G_u²] du`, `E∫H² = ∫E[H²]` for bounded integrands, Doob in Fubini form; on the constructed motion |
| [TidyR10DoobMSVersion](Monetarism/TidyR10DoobMSVersion.lean) | 7 | A1 §1.6, pp. 567–568: stopped sums with orthogonal increments, a continuous modification and an adapted a.s. continuous version of `∫ G dW` for mean-square continuous `G` without a bound, its martingale property |
| [TidyR10TwoBMExist](Monetarism/TidyR10TwoBMExist.lean) | 15 | A1 §1.6, pp. 567–568 (tool for (1.32) with two shocks): a filtration admissible for two Brownian motions, independence of joins, the joint natural filtration, and two independent Brownian motions on `gaussSeq ⊗ gaussSeq` |
| [TidyR10TwoBMCross](Monetarism/TidyR10TwoBMCross.lean) | 27 | A1 §1.6, pp. 567–568 (tool): moments of `ΔW¹ΔW²`, `E[ΔW¹ΔW² \| 𝓕_u] = 0`, the exact identity `E[(ΣΔW¹_iΔW²_i)²] = Σ(Δt_i)²` and its weighted forms, `dW¹dW² = 0` in `L²` and a.s. along dyadic partitions |
| [TidyR10TwoBMIto](Monetarism/TidyR10TwoBMIto.lean) | 26 | A1 §1.6, pp. 567–568: Itô integrals per driver, two-driver Itô processes and their split, brackets `(H¹K¹ + H²K²) dt` in `L¹`, the two-driver product rule and its conditional form, the correlated motion `W³` with `d[W¹, W³] = ρ dt` |
| [TidyR10TwoBMBondStep](Monetarism/TidyR10TwoBMBondStep.lean) | 19 | A1 §1.6, (1.32), p. 567: the product step with bonds and `Λ/P` on two shocks, bracket `σ_B¹σ_X¹ + σ_B²σ_X²`; the book's step holds with separate drivers (`2 + sin W¹`, `b + c sin W²`) and with correlated shocks iff `ρc = 0` |
| [TidyR10TwoBMCorr](Monetarism/TidyR10TwoBMCorr.lean) | 7 | A1 §1.6, pp. 567–568: independent Gaussian processes are jointly Gaussian, `W³ = ρW¹ + √(1 − ρ²)W²` is a Brownian motion for `\|ρ\| ≤ 1`, a common filtration is admissible for it |
| [TidyR11JumpDiffStep](Monetarism/TidyR11JumpDiffStep.lean) | 24 | A1 §1.6, (1.32), p. 567: the product step with bonds and `Λ/P` that jump and diffuse together, `X = A + M_d + M_c`, `B = B_bv + B_c`; the full covariation `∫σ_BK du + ΣΔBΔX`; the book's step iff its conditional expectation vanishes; reductions to the jump step, the Itô bond step and the bounded-variation product step |
| [TidyR11JumpDiffCoinBM](Monetarism/TidyR11JumpDiffCoinBM.lean) | 20 | A1 §1.6, pp. 567–568 (tool): a Brownian motion and an independent fair coin revealed at time 1 on `gaussSeq ⊗ coinMeasure`, an admissible filtration with the coin, the jump martingale `e·ξ·1{u ≥ 1}`, `c·W` as an Itô process, domination for processes bounded by `a + b\|W\|` |
| [TidyR11JumpDiffCoinBMStep](Monetarism/TidyR11JumpDiffCoinBMStep.lean) | 21 | A1 §1.6, (1.32), p. 567: the unified step on `Λ/P = eξ1{u≥1} + dW`, bonds `eξ1{u≥1} + cW` on `[0, 2]`: continuous covariation `2cd`, jump covariation `e²`; the book's step iff `2cd + e² = 0`, failing for `c = d = e = 1`, holding for `c = −1/2`, `d = e = 1` as the parts cancel; the reductions are not vacuous |
| [TidyR11JumpDiffMoney](Monetarism/TidyR11JumpDiffMoney.lean) | 6 | A1 §1.6, (1.31)–(1.32), p. 567: under (1.31) the covariation of bonds with `Λ/P` is minus that of money; the unified step and the book's condition in terms of money; money on the coin instance |
| [TidyR12SDETools](Monetarism/TidyR12SDETools.lean) | 13 | A1 §1.6, pp. 567–568 (tool for SDEs): additivity and linearity of the mean-square time integral and of `∫ G dW` for mean-square continuous integrands, Cauchy–Schwarz for Riemann sums, `E[(∫_s^t G du)²] ≤ (t − s)∫_s^t E[G_u²] du`, bounded second moments on `[s, t]` |
| [TidyR12SDEProcess](Monetarism/TidyR12SDEProcess.lean) | 6 | A1 §1.6, (1.32)–(1.34), pp. 567–568: Itô processes with mean-square continuous, possibly unbounded coefficients (`ItoProcessMS`), containing those with bounded coefficients; increments, the mean-square increment bound, restriction to subintervals |
| [TidyR12SDEPicard](Monetarism/TidyR12SDEPicard.lean) | 16 | A1 §1.6, pp. 567–568: admissible SDE coefficients (Lipschitz, linear growth, continuous in `t` against `1 + \|x\|`), linear coefficients, the Picard map and its contraction estimate, the Gronwall iteration, uniqueness among mean-square continuous solutions |
| [TidyR12SDEExist](Monetarism/TidyR12SDEExist.lean) | 13 | A1 §1.6, pp. 567–568: the Picard iterates converge uniformly in mean square; existence and uniqueness for `dX = b(t, X)dt + σ(t, X)dW`, `X_s = ξ`; the solution is an `ItoProcessMS` |
| [TidyR12SDEGauss](Monetarism/TidyR12SDEGauss.lean) | 19 | A1 §1.6, pp. 567–568 (tool for GBM): Gaussian moments of a Brownian increment, `E[e^{cZ}]` and `E[Ze^{cZ}]` from Mathlib `hasDerivAt_mgf`, independence through the increment, the left-point remainder of GBM with `E[R], E[R²] = o(h)` |
| [TidyR12SDEGBM](Monetarism/TidyR12SDEGBM.lean) | 24 | A1 §1.6, pp. 567–568: geometric Brownian motion solves `dG = (κ + σ²/2)G dt + σG dW` (from the left-point sums), is an `ItoProcessMS`, is the SDE solution, is positive, `E_s[G_t] = e^{m(t − s)}G_s`; the exponential martingale `dG = σG dW`; `uW_u` with unbounded drift; instances on the constructed motion |
| [TidyR12SDEBracket](Monetarism/TidyR12SDEBracket.lean) | 8 | A1 §1.6, pp. 567–568: the bracket `Σ ΔXΔY → ∫ HK du` in `L¹` for `X` an `ItoProcessMS` and `Y` with bounded coefficients; the cell decomposition and the four sums with mean-square bounds |
| [TidyR12SDEProductRule](Monetarism/TidyR12SDEProductRule.lean) | 6 | A1 §1.6, (1.32), p. 567: the conditional product rule `E_s[X_tY_t − X_sY_s] = E_s[∫ (Xb + Ya + HK) du]` for `X` an `ItoProcessMS` and bounded `Y`, and its bracket-free form iff `E_s[∫ HK du] = 0` |
| [TidyR12SDEMonetary](Monetarism/TidyR12SDEMonetary.lean) | 6 | A1 §1.6, (1.31)–(1.32), pp. 567–568: the money–bond model with `Λ/P` an `ItoProcessMS` (`ItoMonetaryModelMS`); the corrected (1.32), the printed line 3 iff the expected bracket vanishes, holding when `σ_Xσ_B = 0`, failing when `E∫σ_Xσ_B ≠ 0` |
| [TidyR12SDEMonetaryGBM](Monetarism/TidyR12SDEMonetaryGBM.lean) | 15 | A1 §1.6, (1.31)–(1.32), pp. 567–568: the GBM economy `Λ/P = n₀e^{−iu}exp(σW_u − σ²u/2) > 0` with a constant known rate, bonds `b₀ + c·arctan W`; the printed line 3 of (1.32) fails on every `[s, t]` for `σc ≠ 0`, the corrected line holds, the printed line holds for `c = 0` |
| [TidyR12SDEVersion](Monetarism/TidyR12SDEVersion.lean) | 11 | A1 §1.6, pp. 567–568: a continuous modification of `t ↦ ∫_s^t G du` (stopped Riemann sums against `W_u = u`, a uniform cell bound, Borel–Cantelli), a continuous modification and an adapted a.s. continuous version of the SDE solution |

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
