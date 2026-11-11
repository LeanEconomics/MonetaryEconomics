# The zero bound and the Covid inflation in Lean

This is the `Cochrane/ZeroBound/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Chapter 20, "The zero bound" (pp. 465–485), the model claims and
arithmetic of Chapter 21, "The Covid inflation" (pp. 486–494), and the future-selection claims of
Chapter 24 (pp. 522–524). The chapter works in two settings, and so does the library. The
discrete-time models (the peg of §20.1, the rule with a bound of §20.2.1, Gabaix's model of
§20.2.6, the regime switches of Chapter 24) are stated for an arbitrary expectation operator, so
every result covers perfect foresight and genuine uncertainty: processes are `ℕ → Ω → ℝ` and
every equation holds state by state. The continuous-time Werning model of §§20.2.2–20.2.5 uses
deterministic paths `ℝ → ℝ`, exact derivatives off a countable set of dates, and genuine
improper integrals; its stochastic version uses processes on a filtered probability space, with
the expectational equations in integrated form and Mathlib's conditional expectation. In both, an equilibrium is a solution of the model
equations, "determinate" means exactly one bounded solution, and the fiscal theory selects instead through the valuation
equation. The library contains **2236 theorems**, including the shared core and its
measure-theoretic copy (`TidyR6ExpectationsMeasure`, `TidyR6ExpectationsMeasureIID`, 108) and the
Brownian-motion, Itô, Ornstein–Uhlenbeck and martingale-representation tools copied from the
Monetarism and FiscalConstraints projects (fifty modules, 905); 1115 of them are in the forty
chapter modules, 124 of
these in verbatim copies of Woodford results
(`GlobalDynamics`, 49, from Chapter 2; `TidyR6WoodfordSequences` and `TidyR6WoodfordZLB`, 75,
from Chapter 6), 305 in the seven modules on Galí's and Woodford's treatments of the bound
(`LinksGaliWoodford`, `LinksGaliWoodfordLimit`, `LiftoffTiming`, `LiftoffStructure`,
`LiftoffRhoZero`, `TidyR6CommonModel`, `TidyR6CommonModelExist`), and 199 in the fourteen modules on
the Werning model under uncertainty (`TidyR7StochWerning`, its five companions, the six
TidyR8StochWerning modules and the two TidyR9StochWerning modules).

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises. Survey codes E1–E11 and E20 refer to
the survey of Chapters 20–25.

Headline results, in the namespace `Cochrane.ZeroBound`:
* **The new-Keynesian model at a peg.** The roots (5.6) straddle the unit circle, `λ₂ < 1 < λ₁`,
  so the peg is not determinate (`ZLBPeg.pegMatrix_roots`, `ZLBPeg.peg_not_determinate`). The
  bounded equilibria are exactly the sunspot recursions `p_t = λ₁E_tp_{t+1}` for `p = π − ī`
  (`ZLBPeg.peg_equilibrium_char`): an uncountable family (`ZLBPeg.peg_continuum`), with a
  genuinely random member on the coin-flip tree (`ZLBPeg.coin_sunspot_equilibrium`), all stable
  in expectation (`ZLBPeg.peg_expected_converges`). Adding the fiscal valuation equation (5.13)
  gives exactly one bounded equilibrium, which is stable and quiet, with unexpected inflation
  `−(1 − ρ/λ₁)` times the fiscal news (`ZLBPeg.fiscal_selects`, `ZLBPeg.fiscal_stable`,
  `ZLBPeg.fiscal_quiet`, `ZLBPeg.fiscal_unexpected_inflation`). A date-0 deflation happens iff
  the fiscal news is a contraction (`ZLBPeg.deflation_iff_fiscal_contraction`).
* **The discrete rule with a zero bound.** E1: the kink of (20.3)–(20.4) is at `π*(φ − 1)/φ`, not
  `π* + (φ − 1)` (`ZLBRule.kink_iff`, `ZLBRule.e1_printed_threshold_false`). E2: with a negative
  natural rate a steady state exists iff `−u ≤ π*(φ − 1)/φ`, and at the Figure 20.3 values there
  is none, `f_u(π) − π ≥ 1/3` (`ZLBRule.steady_exists_iff`, `ZLBRule.fig203_no_steady_state`).
  E3: the future rule selects `π₉ = 3/2`, `π₈ = 9/8`, `π₇ = 11/16`, `π₆ = 1/32`, and the rate lifts
  off early, `i₉ = 1`, `i₈ = 1/4` (`ZLBRule.fig203_selection`, `ZLBRule.fig203_early_liftoff`).
  Global versus local: the bounded orbits are exactly `π₀ ≤ π*`, a continuum returning to zero
  inflation and zero rates, while `π*` is the only locally bounded one
  (`ZLBRule.bounded_orbits_eq`, `ZLBRule.orbit_below_rate_zero`,
  `ZLBRule.locally_bounded_unique_E`). Under uncertainty orbits above `π*` still explode in
  expectation, bounded solutions stay below `π*`, and a bounded solution from `π₀` exists iff
  `π₀ ≤ π*`, for every expectation system and almost surely on a probability space
  (`TidyR6OrbitStochastic.stoch_explodes`, `TidyR6OrbitStochastic.bounded_le_target`,
  `TidyR6OrbitStochastic.bounded_init_iff`); the return to zero holds on every finite tree
  (`TidyR6OrbitStochastic.finiteTree_dichotomy`) but not with genuine uncertainty: a bounded
  solution with i.i.d. shocks has `E[π_t] → 1/2` and the rate positive with probability tending to
  `1/2` (`TidyR6OrbitStochastic.cex_not_ae_tendsto_zero`,
  `TidyR6OrbitStochastic.cex_not_ae_rate_zero`). The early lift-off survives the continuous-time
  limit: in the period-`h` family of Figure 20.3 the lift-off date converges to
  `t_L = T − Λ/(σκ(φ − 1)) < T` (`TidyR6LiftoffLimit.liftoff_time_tendsto`,
  `TidyR6LiftoffLimit.path_tendsto`, `TidyR6LiftoffLimit.ct_liftoff`), so it differs from delayed
  lift-off (`TidyR6LiftoffLimit.early_vs_delayed`).
* **Future selection.** An active rule from date `T` on selects a unique bounded equilibrium
  whatever the policy before `T`, provided the rule coefficient `φ_t` is nonzero
  (`FutureSelection.future_selection`); the hypothesis `φ_t ≠ 0`, implicit in the book, cannot be
  dropped (`FutureSelection.zero_coefficient_not_unique`). The Davig–Leeper fiscal switch: an
  expected switch to active fiscal policy selects, and fiscal shocks move inflation even while
  money is active (`FutureSelection.fiscal_switch_selects`,
  `FutureSelection.fiscal_switch_unexpected_inflation`, `FutureSelection.fiscal_switch_example`).
  Leaving the active-money regime is a discrete shift (p. 523): every continuous path of Leeper
  parameters from active money to active fiscal moves both eigenvalues across the unit circle and
  passes a point with no unique equilibrium, and the response of `π₀` jumps from 0 to 1
  (`TidyR6RegimeEigen.path_crosses`, `TidyR6RegimeEigen.no_determinate_path`,
  `TidyR6RegimeEigen.pi0_response_jump`), while a shift of `θ` in `i = θπ + w` is harmless
  (`TidyR6RegimeEigen.ftpl_existsUnique`, `TidyR6RegimeEigen.ftpl_continuous_theta`).
* **Gabaix's model.** The peg is determinate iff `(1 − M)(1 − βM^f) > σκ`, exactly
  (`Gabaix.gabaix_determinate_iff`); it never is at `M = 1` or for `κ ≥ 1/σ`
  (`Gabaix.rational_IS_indeterminate`, `Gabaix.frictionless_limit_indeterminate`). E8: "`M` less
  than a half" is neither necessary nor sufficient (`Gabaix.e8_half_not_necessary`,
  `Gabaix.e8_not_sufficient`).
* **The Covid inflation.** A helicopter drop raises prices in proportion
  (`Covid.helicopter_exact`). E10: two-thirds backing of 30% new debt gives 8.33%, not 10%
  (`Covid.partial_backing_example`); 10% is the first-order term, with exact remainder
  `−f(1 − f)Δ²/(1 + fΔ)` (`Covid.hasDerivAt_priceRatio`, `Covid.priceRatio_remainder`). E11: the
  1981 windfall is a real return of about 11.5%, not 12% (`Covid.windfall_real_return`).
  Disinflation with falling expected inflation costs `(1 − β)/κ` per point of inflation, less
  than without (`Covid.joint_less_painful`). The nonlinear valuation equation `P = B/S` gives
  unexpected log inflation exactly minus the news in `log S`, and its linearisation holds with an
  explicit second-order remainder (`TidyR6CovidValuation.unexpected_log_inflation`,
  `TidyR6CovidValuation.linearisation_remainder`, `TidyR6CovidValuation.remainder_bounds`); for the
  helicopter of p. 488 the linear prediction is `1/13` against an exact `1/12` in levels and
  `log(13/12)` in logs (`TidyR6CovidValuation.helicopter_book_numbers`).
* **The continuous-time Werning model.** The bounded paths of the experiment are exactly a
  one-parameter family indexed by `π_T` (`WerningModel.bdd_path_iff`). For continuous forcing,
  (20.8)–(20.10) are exactly the forward-stable solutions, in bijection with the constant `C`
  (`WerningModel.eq20_8_iff`, `WerningModel.family_equiv`). E6: for the experiment, (20.8) holds
  with `dg/dt` read as the Stieltjes measure `g(δ_0 − δ_T)` (`WerningModel.experiment_eq20_8`),
  and the derivatives jump at `T` (`WerningModel.jump_pi`, `WerningModel.jump_x`).
* **Selection at the zero bound.** The `π_T = 0` equilibrium has deflation that steadily improves
  and a large output gap (`ZLBSelection.nk_pi_neg`, `ZLBSelection.nk_pi_strictMonoOn`,
  `ZLBSelection.nk_x_neg`); `π_0 → −∞` as `κ → ∞` and as `T → ∞`
  (`ZLBSelection.pi0NK_tendsto_kappa`, `ZLBSelection.pi0NK_tendsto_T`). The output gap is strictly
  decreasing in `κ`, a claim the book marks "not shown" (`ZLBSelection.nk_x_strictAnti_kappa`).
  The limit is not the frictionless solution (`ZLBSelection.nk_discontinuity`). The `π_0 = 0`
  equilibrium has `0 < π_t < −u` and converges to the frictionless square wave
  (`ZLBSelection.nj_pos`, `ZLBSelection.nj_uniform_trap`). The inflation jump equals
  `−(r + λ^b)` times the fiscal innovation (`ZLBSelection.jump_eq_fiscal`).
* **Forward guidance.** `π_0 − π_0' = e^{λ^b T}(π_T − π_T')` (`ForwardGuidance.dpi0_dpiT`),
  increasing in `T` and `κ`. Delaying lift-off has the same power only with a positive post-trap
  natural rate; then `π_0` is strictly increasing and unbounded in the delay
  (`ForwardGuidance.delay_pi0_strictMono`, `ForwardGuidance.delay_pi0_tendsto`).
* **Multipliers.** E20: the standard multiplier is below one for short traps
  (`Multipliers.multNK0_lt_one_short`); at `T = 1` it is about 0.53
  (`Multipliers.e20_counterexample`). It exceeds one for long traps and tends to infinity in `T`
  and `κ` (`Multipliers.multNK0_gt_one_eventually`, `Multipliers.multNK_tendsto_kappa`). No-jump
  multipliers lie in `(−1, 0)` and tend to `−1` (`Multipliers.multNJ_bounds`,
  `Multipliers.multNJ_tendsto_kappa`). Future spending is exponentially more effective
  (`Multipliers.windowMult_strictMono`).
* **The Werning model under uncertainty.** The expectational IS and Phillips curves are read as
  `E_s[Z_t − Z_s − ∫_s^t D] = 0` (`TidyR7StochWerning.ExpDrift`, `TidyR7StochWerning.IsStochEqm`)
  and "do not explode" as bounded first moments (`TidyR7StochWerning.BddL1`), implied by bounded
  second moments (`TidyR7StochWerning.BddL2`). Certainty equivalence holds: conditional means
  solve the deterministic model, with no Itô correction (`TidyR7StochWerning.condMean_integral_eq`).
  Every bounded equilibrium of the experiment is the family of Figure 20.4 with `π_T` replaced by
  `E_sπ_T`, `E_sπ_t = wPi(E_sπ_T)_t` (`TidyR7StochWerningTrap.condExp_pi_eq_wPi`); the unstable
  root is ruled out state by state (`TidyR7StochWerningTrap.x_eq_of_pi`), and news propagates as
  the deterministic response `e^{−λ^b(t−s)}` (`TidyR7StochWerningTrap.revision_pi_eq`). On a
  Brownian motion every `π_T` and loading `b` of an Ornstein–Uhlenbeck inflation innovation give a
  distinct equilibrium bounded in `L²` (`TidyR7StochWerningExist.isStochEqm_eq`,
  `TidyR7StochWerningExist.bddL2_eqPi`), with Itô form
  `π_t = wPi(π_T)_t + b e^{−λ^b t}∫_0^t e^{λ^b u}dW_u` (`TidyR7StochWerningExist.eqPi_ae_eq_itoInt`),
  which for `b ≠ 0` is not bounded in `L^∞` (`TidyR7StochWerningExist.not_bdd_ae_eqPi`). The active
  rule (20.7) and the new-Keynesian choice of `π_T` remove all randomness
  (`TidyR7StochWerningSelect.active_rule_selects`, `TidyR7StochWerningSelect.nk_selection`); the
  fiscal `π_0 = 0` pins only the mean path (`TidyR7StochWerningSelect.pi0_not_selects`). Under a
  mean-reverting natural-rate shock the unstable combination `λ^fπ − κx` responds by
  `−κσ/(λ^f + η)` (`TidyR7StochWerningNatural.unstable_natural`), non-vacuously
  (`TidyR7StochWerningNaturalExist.natural_nonvacuous`). For `b ≠ 0` almost every path of the
  Ornstein–Uhlenbeck equilibria is unbounded, `sup_{t≥0} π_t = +∞` and `inf_{t≥0} π_t = −∞`
  (`TidyR8StochWerningRecurrence.eqPi_sup_inf`). With the zero rate during the trap and the active
  rule after it in one model, every bounded equilibrium is the chosen path almost surely, and that
  path is an equilibrium (`TidyR8StochWerningActiveTrap.active_trap_selects`,
  `TidyR8StochWerningActiveTrap.active_trap_exists`). The equilibria of the experiment are exactly
  the continuous martingales `M_t = e^{λ^b t}(π_t − wPi(0)_t)` with `e^{−λ^b t}M_t` bounded in
  `L¹` (`TidyR8StochWerningMartingale.martingale_of_isStochEqm`,
  `TidyR8StochWerningMartingale.isStochEqm_of_martingale`), and every `C¹` time-varying loading
  gives a mean-square-bounded equilibrium (`TidyR8StochWerningMartingale.isStochEqm_loading`). The
  standard multiplier and the deflation without limit hold state by state
  (`TidyR8StochWerningLimits.nk_multiplier_stoch`, `TidyR8StochWerningLimits.nk_frictionless_stoch`);
  under `π_0 = 0` the no-jump multiplier and the smooth frictionless limit hold in mean
  (`TidyR8StochWerningLimits.nj_mean_multiplier`, `TidyR8StochWerningLimits.nj_frictionless_stoch`). Under natural-rate shocks
  `E_sπ_t = wPi(0)_t + e^{−λ^b(t−s)}(π_s − wPi(0)_s) + d k(t − s)ν_s`
  (`TidyR8StochWerningNaturalMean.condExp_pi_nat`) and the equilibria are bounded in mean square
  (`TidyR8StochWerningNaturalMean.bddL2_natPi`); when the rate tracks the natural rate after the
  trap, as on p. 474, the news acts only through the remaining trap
  (`TidyR8StochWerningNaturalTrack.unstable_track`, `TidyR8StochWerningNaturalTrack.condExp_pi_track`),
  and such equilibria exist (`TidyR8StochWerningNaturalTrack.isStochEqmTrack_trackPi`). The
  Brownian-motion and Itô modules are copied from the Monetarism project (via the
  FiscalConstraints copies) and the Ornstein–Uhlenbeck modules from the FiscalConstraints project.
* **Which innovations occur.** On the Brownian filtration the martingales that index the
  equilibria are stochastic integrals. The extended Itô integral `t ↦ ∫_s^t H dW` has a
  modification with almost surely continuous paths (`TidyR9StochWerningMRepVersion.swmrep_exists_continuous_modification`),
  a version adapted to `𝓕` with almost every path continuous
  (`TidyR9StochWerningMRepVersion.swmrep_exists_adapted_continuous`), and a version with every path continuous that is
  adapted to, and a martingale for, the completed filtration `augment P 𝓕`
  (`TidyR9StochWerningMRepVersion.swmrep_exists_continuous_augment`). Every martingale on `[0, ∞)` with `M_t ∈ L²` is
  `M_t = E[M_0] + ∫_0^t H dW` with one `H` for all horizons, unique `dt × dP`-a.e.
  (`TidyR9StochWerningMRepVersion.swmrep_martingale_rep`, `TidyR9StochWerningMRepVersion.swmrep_martingale_rep_unique`). Hence every regular
  `L¹`-bounded equilibrium of the experiment with `π_t ∈ L²` is
  `π_t = wPi(0)_t + e^{−λ^b t}(c + ∫_0^t H dW)`, and `x` likewise with the factor `λ^f/κ`, where
  `c = E[π_0] − wPi(0)_0` and `(c, H)` is unique: the free constant `C` of p. 475 becomes the
  pair `(c, H)` (`TidyR9StochWerningInnovations.swinnov_eqm_rep`, `TidyR9StochWerningInnovations.swinnov_eqm_rep_unique`,
  `TidyR9StochWerningInnovations.swinnov_eqm_rep_natural`). Conversely every `c` and every `H` with
  `E∫_0^t H² ≤ K e^{2λ^b t}`, in particular every bounded `H`, give a regular mean-square-bounded
  equilibrium (`TidyR9StochWerningInnovations.swinnov_eqm_of_integrand`, `TidyR9StochWerningInnovations.swinnov_growth_of_bdd`); for
  mean-square-bounded equilibria the growth condition is also necessary, so they correspond
  exactly to the pairs `(c, H)` that satisfy it (`TidyR9StochWerningInnovations.swinnov_growth_of_rep`,
  `TidyR9StochWerningInnovations.swinnov_eqm_rep_bddL2`). Every continuous bounded deterministic loading `b`, not only a
  `C¹` one, gives an equilibrium with innovations `dπ_t = b(t)dW_t`
  (`TidyR9StochWerningInnovations.swinnov_loading_continuous`). The filtration matters: the converse and the continuous
  loadings give equilibria for the completed filtration `augment P 𝓕`, not for `𝓕` itself,
  because a version of `∫ H dW` with every path continuous is adapted only to the completion; the
  direct direction holds on both, `swinnov_eqm_rep` for `augment P 𝓕` and
  `swinnov_eqm_rep_natural` for `𝓕`, every equilibrium for `𝓕` being one for `augment P 𝓕`
  (`TidyR9StochWerningInnovations.swinnov_isStochEqm_augment`). On `TidyR7BrownianExist.bmPath` at the book's calibration:
  the representation of the constant-loading equilibrium, news only between dates `1` and `2`
  (`H = 1_{(1,2]}`), and the continuous loading `|sin t|`, not differentiable at `0`
  (`TidyR9StochWerningInnovations.bmPath_swinnov_rep`, `TidyR9StochWerningInnovations.bmPath_swinnov_window`, `TidyR9StochWerningInnovations.bmPath_swinnov_abs_sin`). Doob's
  inequality, continuous versions of the Itô integral, the completed filtration, Itô processes
  and the product rule, Itô's formula and the martingale representation theorem on `[0, T]`
  with the extended integral (`TidyR13MRepTheorem.mrep_martingale`) are thirty-two modules
  copied from the Monetarism project, two of them (`TidyR8MonetarismItoDom`,
  `TidyR13MRepMonetarism`) in part.
* **Welfare at the zero bound.** E9: with exact Calvo dispersion, the zero-bound steady state
  `Π_L = β` is better than `Π*` iff `βΠ* > 1` (`ZLBWelfare.zlb_better_iff`,
  `ZLBWelfare.e9_counterexample`); the book's calibration satisfies the condition
  (`ZLBWelfare.book_calibration`).
* **Links.** The discrete peg roots, scaled by the period length, converge to the continuous-time
  roots, and the discrete peg paths to the continuous ones (`Links.tendsto_lam1_scaled`,
  `Links.peg_paths_converge`). Gabaix's model at `M = M^f = 1` is the peg
  (`Links.gabaix_rational_eq_peg`, `Links.gabaix_rational_straddle`). A steady state of the
  Chapter 16 map at the bound is `Π_L = β` (`Links.zlb_fixed_point_eq_beta`).
* **Galí's commitment and Woodford's moment constraint.** Galí's optimal commitment at the bound
  is delayed lift-off plus a positive promise: given Galí's sign condition, it lies strictly above
  delayed lift-off at its own lift-off date, which lies above discretion, and discretion has
  strictly larger loss (`LinksGaliWoodford.comm_gt_delay`, `LinksGaliWoodford.comm_gt_disc`,
  `LiftoffTiming.comm_gt_disc_opt`, `LiftoffTiming.comm_loss_lt_opt`). The sign condition fails at
  an exact optimum (`LinksGaliWoodford.cex_xi_neg`). Discrete trap paths converge to Werning's
  continuous ones (`LinksGaliWoodfordLimit.trap_tendsto`). Neither Woodford's moment constraint
  nor the pathwise bound implies the other (`LinksGaliWoodford.Moments.neither_implies`). A common
  model contains both: Galí's and Cochrane's discrete model with Galí's loss, in which the
  pathwise optimum is exactly Galí's commitment optimum (`TidyR6CommonModel.pathOpt_iff`) and
  Proposition 6.9 holds (`TidyR6CommonModel.prop_6_9_common`), its optimum existing iff the moment
  constraints can be met and then unique (`TidyR6CommonModelExist.momOpt_exists_iff`,
  `TidyR6CommonModel.momOpt_unique`). See the relation to the Woodford and Galí projects below.
* **The commitment optimum.** At the optimum the bound binds on the whole shock, so the lift-off
  date satisfies `t_C ≥ t_Z` and Galí's guess is without loss of generality
  (`LiftoffTiming.optimal_trap_binds`, `LiftoffTiming.liftoff_ge`,
  `LiftoffTiming.algorithm_verification_gen`); commitment inflation never exceeds the depth of the
  shock (`LiftoffTiming.optimal_pi_le`). For `ρ > 0` the optimum exists, is unique, and keeps the
  rate at zero exactly on `[0, t_C]` and positive after
  (`LiftoffStructure.commitment_characterisation`); it is always the path of Galí's algorithm
  (`LiftoffStructure.optimal_algorithm_form`). With a zero post-shock natural rate, `ρ = 0`, the
  case is fully classified for every `β ∈ (0, 1)`, `κ, σ, ϑ, η > 0` and `t_Z`: the optimum exists
  and is unique, its rate is zero forever iff `ϑ ≤ σκ`, and it lifts off at a finite
  `t_C ≥ t_Z` with `i > 0` afterwards iff `σκ < ϑ`; `η`, `β` and `t_Z` play no role
  (`LiftoffRhoZero.rho_zero_zero_iff`, `LiftoffRhoZero.rho_zero_liftoff_iff`,
  `LiftoffRhoZero.rho_zero_classification`). Exact rational optima certify both sides
  (`LiftoffRhoZero.cert_liftoff_now`, `LiftoffRhoZero.cert_liftoff_late`,
  `LiftoffRhoZero.cert_zero_forever`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections are the confirmed errors of the chapter survey:
* the kink of (20.3)–(20.4), p. 472: at `π*(φ − 1)/φ`, not `π* + (φ − 1)` (E1);
* the steady states with a negative natural rate, p. 472: they exist only if
  `−u ≤ π*(φ − 1)/φ`, and not at the Figure 20.3 values (E2);
* "the nominal rate remains stuck at zero", p. 472: it lifts off two periods early (E3);
* Gabaix's determinacy condition, p. 483: exactly `(1 − M)(1 − βM^f) > σκ` (E8);
* the welfare of `Π_L`, pp. 484–485: better iff `βΠ* > 1` (E9);
* partial backing, p. 488: 8.33%, not 10% (E10); the 1981 windfall, p. 493: 11.5%, not 12% (E11);
* multipliers "substantially greater than one", p. 481: false for short traps (E20).

In addition, the formalisation reads (20.9) with `r_t` the natural rate and `dg/dt` a measure
(E6), corrects the cross-reference "(17.2)" to (20.6) (E4), makes explicit the hypothesis
`φ_t ≠ 0` of future selection and the timing of the natural rate in Figure 20.3, and gives
delayed lift-off the positive post-trap natural rate it needs. The links with Galí (2015) correct
two features of his commitment solution: the positivity of (42)–(43), p. 150, needs
`ξ₁,t_C+1 > 0`, which fails at an exact optimum (`LinksGaliWoodford.cex_xi_neg`), and strictly
later lift-off is not a property of every optimum (`LinksGaliWoodford.cex_liftoff_at_shock_end`).
The weak inequality `t_C ≥ t_Z`, Galí's guess, holds at every optimum (`LiftoffTiming.liftoff_ge`),
and with a zero post-shock natural rate the rate lifts off iff `σκ < ϑ`
(`LiftoffStructure.rho_zero_no_liftoff`, `LiftoffRhoZero.rho_zero_liftoff_iff`).

Five statements are made precise. The claim of p. 473 that undershooting equilibria "return
back to zero inflation and zero interest rates" holds under perfect foresight and on finite trees
but fails under genuine uncertainty (`TidyR6OrbitStochastic.cex_not_ae_tendsto_zero`). The
linearised valuation equation predicts `1/13` for the helicopter of p. 488, against the exact
`1/12` in levels and `log(13/12)` in logs, complementing E10. The remark of p. 523 on moving
eigenvalues is confirmed (`TidyR6RegimeEigen.path_crosses`). Under uncertainty the fiscal
selection `π_0 = 0` of p. 476 pins only the mean path, so it must specify the inflation innovation
at every date, while the choice of `π_T` and the active rule (20.7) remove all randomness
(`TidyR7StochWerningSelect.pi0_not_selects`, `TidyR7StochWerningSelect.nk_selection`,
`TidyR7StochWerningSelect.active_rule_selects`); so the fiscal selection carries the frictionless
limit and the multipliers only for means, the `π_T` selection state by state
(`TidyR8StochWerningLimits.nj_mean_multiplier`, `TidyR8StochWerningLimits.nk_multiplier_stoch`).
When the rate tracks the random natural rate after the trap, natural-rate news affects inflation
and output only through the remaining trap (`TidyR8StochWerningNaturalTrack.unstable_track`).

Not formalised:
* the empirical and narrative parts of Chapters 20–21: the U.S. and Japanese experience, QE, the
  Occam discussion and the list of patches, the 2020 FOMC strategy, secular stagnation, the
  Lucas–Stokey reading of Covid inflation, and the speculation of Chapter 21;
* claims owned by other Cochrane projects: the old-Keynesian deflation spiral (p. 466,
  `KeynesianStickyPrices`), the monetarist reading of QE and the Friedman rule (pp. 468–469,
  p. 485, `Monetarism`), the AR(1) and Figure 5.6 readings of the Covid debt (pp. 488–489,
  `DebtDeficitsInflation` and `StickyPriceFiscal`), the higher-rates simulations of §17.4.2
  (p. 493, `KeynesianStickyPrices`), and the
  observational-equivalence remark of p. 476 and the Markov-switching determinacy of Chapter 24
  (`ObservationalEquivalence`). The fiscal side of the p. 476 remark is
  `ZLBSelection.jump_eq_fiscal`;
* the literature reviews of §§20.2.6 and 24;
* the verbal claim that it is "impossible to produce a deep recession without deep but improving
  deflation" (p. 477), which has no precise statement;
* the illustrative numbers of Figures 20.4–20.6 (`π_0 = −132.46%`, `π_T ≈ 1.01%`, multipliers of
  66 and 528); only the E20 point `T = 1` is formalised;
* parts of the stochastic versions of §§20.2.2–20.2.5, which the `TidyR7StochWerning`,
  TidyR8StochWerning and TidyR9StochWerning modules otherwise give on the natural filtration of a
  Brownian motion with the `TidyR7StochWerning.BddL1` and `TidyR7StochWerning.BddL2` selections
  (proved: the almost-sure unboundedness of the Ornstein–Uhlenbeck equilibria, the active rule
  and the trap in one model, the frictionless limit and the multipliers, `E_sπ_t` and `L²` bounds
  under natural-rate shocks, the tracking rate after `T`, every equilibrium as a martingale and,
  when `π_t ∈ L²`, as `c + ∫ H dW`, and existence for continuous loadings): the representation
  of equilibria with `π_t` only in `L¹`, since an `L¹` martingale of the Brownian filtration is
  `M_0 + ∫ H dW` only with `∫_0^t H² < ∞` almost surely, which needs a local-martingale integral;
  the converse (every admissible `(c, H)`) and existence for continuous non-`C¹` loadings on the
  natural filtration `𝓕` itself, which are proved for the completed filtration `augment P 𝓕`
  only, so that on `𝓕` the only existence result for time-varying loadings is the `C¹` one
  (`TidyR8StochWerningMartingale.isStochEqm_loading`); existence for general deterministic
  loadings that are only locally square integrable (proved: continuous bounded loadings and the
  window `1_{(1,2]}`); almost-sure unboundedness beyond constant loadings; conditional (not only
  mean) multipliers under the fiscal `π_0 = 0` selection; and, in the tracking model, an added
  stable-direction innovation (only `b = 0`), the martingale description (proved for the trap
  with `ν = 0` only) and a separate statement of `E_sx_t`;
* a nonlinear sticky-price valuation equation: the linearisation with remainder is of the
  frictionless `P = B/S` of Chapter 21, and the sticky-price (5.13) is linked to it only through
  the frictionless limit of the impact coefficient (`Links.fiscal_impact_frictionless`);
* convergence of Figure 20.3 to Werning's model: the period-`h` family converges to the
  continuous-time model with the static IS curve of §20.2.1, not to Werning's dynamic-IS model of
  §§20.2.2–20.2.4; that the two lift-offs differ is proved instead (`TidyR6LiftoffLimit.early_vs_delayed`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](ZeroBound/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (shared core, restated from the earlier projects) |
| [Expectations](ZeroBound/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; adapted and AR(1) processes; the backward system and determinacy (shared core) |
| [ExpectationsFiniteTree](ZeroBound/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; the coin-flip tree and its shock (shared core) |
| [ForwardSolution](ZeroBound/ForwardSolution.lean) | 44 | The forward solution of `z_t = aE_tz_{t+1} + u_t` and the sunspot family (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [GlobalDynamics](ZeroBound/GlobalDynamics.lean) | 49 | One-dimensional dynamics, (4.5)–(4.6), self-fulfilling deflations (verbatim from the Woodford Chapter 2 project) |
| [ZLBPeg](ZeroBound/ZLBPeg.lean) | 36 | §20.1: the new-Keynesian model at a peg, root straddle, the sunspot characterisation and continuum; fiscal valuation (5.13) selects a stable, quiet equilibrium |
| [ZLBRule](ZeroBound/ZLBRule.lean) | 39 | §20.2.1: (20.1)–(20.4) with the kink corrected (E1), steady states (E2), global versus local boundedness, Figure 20.3 and early lift-off (E3) |
| [FutureSelection](ZeroBound/FutureSelection.lean) | 11 | §20.2.1 and Chapter 24: selection by a deterministic switch to an active monetary rule or to active fiscal policy |
| [Gabaix](ZeroBound/Gabaix.lean) | 16 | §20.2.6: (20.11)–(20.12) at a peg, determinacy iff `(1 − M)(1 − βM^f) > σκ`, E8 counterexamples |
| [Covid](ZeroBound/Covid.lean) | 24 | Chapter 21: the helicopter drop and partial backing (E10), fiscal news, Phillips-curve disinflation, interest costs and the windfall (E11), data arithmetic |
| [ContinuousTimeNK](ZeroBound/ContinuousTimeNK.lean) | 53 | §20.2.2: the roots `λ^f`, `λ^b`; forward and backward integrals; linear ODEs off a countable set; the Green's-function family (20.8) (calculus partly restated from the Chapter 5 project) |
| [WerningModel](ZeroBound/WerningModel.lean) | 41 | §20.2.2: (20.5)–(20.10), the bounded paths as a one-parameter family, jump conditions, (20.8) both ways, its Stieltjes reading (E6), (20.7) |
| [ZLBSelection](ZeroBound/ZLBSelection.lean) | 51 | §§20.2.2–20.2.3: the `π_T = 0` and `π_0 = 0` equilibria, limits in `κ` and `T`, the frictionless model and the discontinuity, the square-wave limit, the jump as a fiscal innovation |
| [ForwardGuidance](ZeroBound/ForwardGuidance.lean) | 19 | §20.2.4: the sensitivity `e^{λ^b T}`, the glide path, delayed lift-off |
| [Multipliers](ZeroBound/Multipliers.lean) | 32 | §20.2.5: the IS curve solved forward, standard and no-jump multipliers, E20, future spending |
| [ZLBWelfare](ZeroBound/ZLBWelfare.lean) | 21 | §20.3: exact Calvo dispersion, `Π_L = β`, better than `Π*` iff `βΠ* > 1` (E9) |
| [Links](ZeroBound/Links.lean) | 20 | Discrete-to-continuous convergence of roots, paths and impact coefficients; Gabaix at `M = M^f = 1`; `Π_L = β` in the Chapter 16 map and in the rule of §20.2.1 |
| [LinksGaliWoodford](ZeroBound/LinksGaliWoodford.lean) | 123 | Galí's commitment as delayed lift-off plus a promise, the discrete Werning family, the sign of `ξ₁,t_C+1` and an exact optimum; Woodford's moment constraint against the pathwise bound; Woodford's dispersion and `Π_L = β` (Galí and Woodford definitions restated) |
| [LinksGaliWoodfordLimit](ZeroBound/LinksGaliWoodfordLimit.lean) | 19 | Exact two-mode closed form of the discrete trap path; convergence of whole trap paths to the continuous-time Werning paths |
| [LiftoffTiming](ZeroBound/LiftoffTiming.lean) | 69 | Galí's commitment optimum: necessity of the KKT conditions with transversality, `π_t ≤ η`, the bound binds on the whole shock, `t_C ≥ t_Z`; the commitment theorems without that hypothesis |
| [LiftoffStructure](ZeroBound/LiftoffStructure.lean) | 30 | Existence (Hilbert projection in a weighted `ℓ²`) and uniqueness of the optimum; no re-binding, finite lift-off, the post-lift-off closed form; the full characterisation; the `ρ = 0` dichotomy and `ρ > 0` necessary |
| [LiftoffRhoZero](ZeroBound/LiftoffRhoZero.lean) | 20 | The `ρ = 0` case classified: rate zero forever iff `ϑ ≤ σκ`, finite lift-off iff `σκ < ϑ`; the shapes of both branches; the verification theorem for `ρ = 0`; exact certificates on each side |
| [TidyR6WoodfordSequences](ZeroBound/TidyR6WoodfordSequences.lean) | 40 | Bounded sequences and processes, discounted sums, the dispersion recursion (verbatim from the Woodford Chapter 6 project's `Sequences`) |
| [TidyR6WoodfordZLB](ZeroBound/TidyR6WoodfordZLB.lean) | 35 | Woodford's moment constraint, Kuhn–Tucker multipliers and Proposition 6.9 (verbatim from the Woodford Chapter 6 project's `ZLB`) |
| [TidyR6CommonModel](ZeroBound/TidyR6CommonModel.lean) | 25 | A common model for the bound and Proposition 6.9: the linear rate, convexity, Proposition 6.9 in the model, the bound as Galí's commitment optimum, uniqueness, comparisons of the two constraints |
| [TidyR6CommonModelExist](ZeroBound/TidyR6CommonModelExist.lean) | 19 | Existence of the moment-constrained optimum in `ℓ²(ℕ ⊕ ℕ)`: iff the constraints can be met; existence and uniqueness in the trap at Woodford's calibration |
| [TidyR6CovidValuation](ZeroBound/TidyR6CovidValuation.lean) | 18 | Chapter 21: the nonlinear valuation equation `P = B/S`, exact unexpected log inflation, the linearisation with explicit remainder, the helicopter numbers `1/13`, `1/12`, `log(13/12)` |
| [TidyR6ExpectationsMeasure](ZeroBound/TidyR6ExpectationsMeasure.lean) | 71 | Measure-theoretic expectations with Mathlib's `condExp` (copied from `ObservationalEquivalence`): the axioms a.e., news, the forward equation and sunspots, AR(1), bridges to and from the core |
| [TidyR6ExpectationsMeasureIID](ZeroBound/TidyR6ExpectationsMeasureIID.lean) | 37 | The i.i.d. economy on `ℕ → ℝ` under `ν^ℕ` (copied from `ObservationalEquivalence`): independence, moments, every history null, determinacy iff `\|a\| < 1`, AR(1), the `±1` coin |
| [TidyR6LiftoffLimit](ZeroBound/TidyR6LiftoffLimit.lean) | 56 | §20.2.1: the period-`h` family of Figure 20.3, its continuous-time limit with lift-off at `t_L < T`, convergence of the lift-off date and path, early versus delayed lift-off |
| [TidyR6OrbitStochastic](ZeroBound/TidyR6OrbitStochastic.lean) | 33 | §20.2.1: the global orbit results under uncertainty, for every expectation system, on finite trees and a.e.; the i.i.d. counterexample to the return to zero |
| [TidyR6RegimeEigen](ZeroBound/TidyR6RegimeEigen.lean) | 17 | Chapter 24, p. 523: the Leeper eigenvalues, the determinacy map, every path between the regimes crosses the unit circle, the jump in `∂π₀/∂c₀`; `θ` shifts are harmless |
| [ExpIntegrals](ZeroBound/ExpIntegrals.lean) | 17 | Exponential integrals on `[0, ∞)`: discount factors, growing streams, translation, transversality (copied from the FiscalConstraints project) |
| [LinearODE](ZeroBound/LinearODE.lean) | 12 | The debt-to-GDP equation (6.4), variation of constants, the corrected (6.5), the forward present value (copied from the FiscalConstraints project) |
| [TidyR7BrownianSchauder](ZeroBound/TidyR7BrownianSchauder.lean), [TidyR7BrownianUnit](ZeroBound/TidyR7BrownianUnit.lean), [TidyR7BrownianExist](ZeroBound/TidyR7BrownianExist.lean), [TidyR7BrownianTools](ZeroBound/TidyR7BrownianTools.lean), [TidyR7StieltjesIntegral](ZeroBound/TidyR7StieltjesIntegral.lean), [TidyR7StieltjesSums](ZeroBound/TidyR7StieltjesSums.lean), [TidyR7BrownianQV](ZeroBound/TidyR7BrownianQV.lean), [TidyR7ItoL2](ZeroBound/TidyR7ItoL2.lean), [TidyR7ItoSums](ZeroBound/TidyR7ItoSums.lean), [TidyR7ItoIntegral](ZeroBound/TidyR7ItoIntegral.lean), [TidyR7StieltjesCalculus](ZeroBound/TidyR7StieltjesCalculus.lean), [TidyR7ItoBridge](ZeroBound/TidyR7ItoBridge.lean) | 357 | Brownian motion (Lévy–Ciesielski construction, existence on `[0, ∞)`, the natural filtration, martingales, quadratic variation), the Riemann–Stieltjes integral, the Itô integral and its isometry, and the bridge to pathwise and Wiener integrals (TidyR7BrownianSchauder 53, TidyR7BrownianUnit 13, TidyR7BrownianExist 17, TidyR7BrownianTools 25, TidyR7StieltjesIntegral 44, TidyR7StieltjesSums 34, TidyR7BrownianQV 48, TidyR7ItoL2 20, TidyR7ItoSums 44, TidyR7ItoIntegral 32, TidyR7StieltjesCalculus 11, TidyR7ItoBridge 16; copied from the Monetarism project via the FiscalConstraints copies) |
| [TidyR7OUPath](ZeroBound/TidyR7OUPath.lean) | 23 | The Ornstein–Uhlenbeck equation solved path by path for any continuous driving path, uniqueness, the exact AR(1) step (copied from the FiscalConstraints project) |
| [TidyR7WienerGaussian](ZeroBound/TidyR7WienerGaussian.lean) | 13 | Wiener integrals of deterministic `C¹` integrands: by-parts form, isometry, Gaussian law (copied from the FiscalConstraints project) |
| [TidyR7OrnsteinUhlenbeck](ZeroBound/TidyR7OrnsteinUhlenbeck.lean) | 33 | The Ornstein–Uhlenbeck process `ouProc` driven by a pre-Brownian motion: pathwise solution, Itô form, Gaussian law, stationary limit (copied from the FiscalConstraints project) |
| [TidyR7StochWerning](ZeroBound/TidyR7StochWerning.lean) | 10 | §§20.2.2–20.2.5 under uncertainty: `E_t dZ = D dt` in integrated form, regular processes, `L¹` and `L²` bounds, stochastic equilibrium, certainty equivalence |
| [TidyR7StochWerningTrap](ZeroBound/TidyR7StochWerningTrap.lean) | 21 | §§20.2.2, 20.2.4 under uncertainty: every bounded equilibrium of the experiment, `E_sπ_t = wPi(E_sπ_T)_t`, the unstable root ruled out state by state, output and news responses, the deterministic case |
| [TidyR7StochWerningExist](ZeroBound/TidyR7StochWerningExist.lean) | 20 | §20.2.2 under uncertainty: explicit equilibria on a Brownian motion for every `π_T` and innovation loading, `L²` bounds, distinctness, no `L^∞` bound, the Itô form, non-vacuity |
| [TidyR7StochWerningSelect](ZeroBound/TidyR7StochWerningSelect.lean) | 6 | (20.7) and p. 476 under uncertainty: the active rule and the choice of `π_T` select state by state; `π_0 = 0` pins only the mean path |
| [TidyR7StochWerningNatural](ZeroBound/TidyR7StochWerningNatural.lean) | 3 | (20.8)–(20.10) with a mean-reverting natural-rate shock: the unstable combination pinned state by state, response `−κσ/(λ^f + η)` |
| [TidyR7StochWerningNaturalExist](ZeroBound/TidyR7StochWerningNaturalExist.lean) | 20 | Natural-rate shocks: explicit `L¹`-bounded equilibria on a Brownian motion with an Ornstein–Uhlenbeck shock, the pathwise smoothing `chiProc`, non-vacuity |
| [TidyR7OUSampled](ZeroBound/TidyR7OUSampled.lean) | 9 | The Ornstein–Uhlenbeck process sampled at integer dates: an AR(1) with i.i.d. Gaussian innovations (the innovation part, copied from the FiscalConstraints project) |
| [TidyR8StochWerningActiveTrap](ZeroBound/TidyR8StochWerningActiveTrap.lean) | 7 | (20.7) and pp. 475–476 under uncertainty: the trap and the active rule in one model, unique equilibrium almost surely and pathwise, existence, non-vacuity |
| [TidyR8StochWerningLimits](ZeroBound/TidyR8StochWerningLimits.lean) | 7 | §§20.2.3, 20.2.5 under uncertainty: the standard multiplier and deflation without limit state by state; the no-jump multiplier and the square-wave limit in mean; the deterministic case |
| [TidyR8StochWerningNaturalMean](ZeroBound/TidyR8StochWerningNaturalMean.lean) | 21 | Natural-rate shocks: `E_sν_t`, `E_sπ_t` and `E_sx_t` in every bounded equilibrium; `L²` bounds for the smoothing and the explicit equilibria, non-vacuity |
| [TidyR8StochWerningMartingale](ZeroBound/TidyR8StochWerningMartingale.lean) | 16 | §20.2.2 under uncertainty: the equilibria are exactly the martingales `e^{λ^b t}(π_t − wPi(0)_t)`; Wiener-integral martingales and equilibria with `C¹` time-varying loadings, non-vacuity |
| [TidyR8StochWerningNaturalTrack](ZeroBound/TidyR8StochWerningNaturalTrack.lean) | 19 | Natural-rate shocks with the rate tracking the natural rate after the trap: the unstable combination state by state, `E_sπ_t`, existence and `L²` bounds, non-vacuity |
| [TidyR8StochWerningRecurrence](ZeroBound/TidyR8StochWerningRecurrence.lean) | 21 | §20.2.2 under uncertainty: recurrence of the sampled Ornstein–Uhlenbeck process (0-1 law), almost every equilibrium path with `b ≠ 0` has `sup π = +∞`, `inf π = −∞`, non-vacuity |
| [TidyR10DoobDiscrete](ZeroBound/TidyR10DoobDiscrete.lean), [TidyR7StieltjesVariation](ZeroBound/TidyR7StieltjesVariation.lean), [TidyR7CondDominated](ZeroBound/TidyR7CondDominated.lean), [TidyR10DoobContinuous](ZeroBound/TidyR10DoobContinuous.lean), [TidyR7ItoContinuity](ZeroBound/TidyR7ItoContinuity.lean), [TidyR7ItoUnbounded](ZeroBound/TidyR7ItoUnbounded.lean), [TidyR7ItoProducts](ZeroBound/TidyR7ItoProducts.lean), [TidyR7ItoProcess](ZeroBound/TidyR7ItoProcess.lean), [TidyR7ProductStep](ZeroBound/TidyR7ProductStep.lean), [TidyR7ItoCovariation](ZeroBound/TidyR7ItoCovariation.lean), [TidyR7ItoProductRule](ZeroBound/TidyR7ItoProductRule.lean), [TidyR7ItoBondStep](ZeroBound/TidyR7ItoBondStep.lean), [TidyR8MonetarismItoDom](ZeroBound/TidyR8MonetarismItoDom.lean), [TidyR10DoobIto](ZeroBound/TidyR10DoobIto.lean), [TidyR10DoobVersion](ZeroBound/TidyR10DoobVersion.lean), [TidyR10DoobAugment](ZeroBound/TidyR10DoobAugment.lean), [TidyR7BrownianVariation](ZeroBound/TidyR7BrownianVariation.lean) | 272 | Doob's `L²` inequality in discrete and continuous time, the variation of paths, conditional dominated convergence, continuous modifications of the Itô integral, unbounded mean-square integrands, Itô processes, the product step and Itô's product rule, the product step for two Itô processes, additivity of the Itô integral over intervals, Doob for `W` and `∫ G dW`, adapted continuous versions, the completed filtration `augment` with an every-path-continuous Itô integral, infinite variation of Brownian paths (TidyR10DoobDiscrete 18, TidyR7StieltjesVariation 21, TidyR7CondDominated 14, TidyR10DoobContinuous 11, TidyR7ItoContinuity 16, TidyR7ItoUnbounded 23, TidyR7ItoProducts 19, TidyR7ItoProcess 18, TidyR7ProductStep 35, TidyR7ItoCovariation 14, TidyR7ItoProductRule 22, TidyR7ItoBondStep 15, TidyR8MonetarismItoDom 4, TidyR10DoobIto 9, TidyR10DoobVersion 7, TidyR10DoobAugment 9, TidyR7BrownianVariation 17; copied from the Monetarism project, `TidyR8MonetarismItoDom` in part) |
| [TidyR9ItoTaylor](ZeroBound/TidyR9ItoTaylor.lean), [TidyR9ItoPathSums](ZeroBound/TidyR9ItoPathSums.lean), [TidyR9ItoWeightedBracket](ZeroBound/TidyR9ItoWeightedBracket.lean), [TidyR9ItoFormula](ZeroBound/TidyR9ItoFormula.lean), [TidyR10DoobProductStep](ZeroBound/TidyR10DoobProductStep.lean), [TidyR10DoobFubini](ZeroBound/TidyR10DoobFubini.lean), [TidyR10DoobMSVersion](ZeroBound/TidyR10DoobMSVersion.lean), [TidyR9ItoFormulaVariants](ZeroBound/TidyR9ItoFormulaVariants.lean), [TidyR12SDETools](ZeroBound/TidyR12SDETools.lean) | 86 | Itô's formula (Taylor tools, path sums, the weighted bracket, the formula and its variants), the product step with a Brownian or Itô-integral martingale part, the Itô isometry in Fubini form, continuous versions for mean-square integrands, mean-square time integrals and `L²` bounds (TidyR9ItoTaylor 4, TidyR9ItoPathSums 6, TidyR9ItoWeightedBracket 5, TidyR9ItoFormula 16, TidyR10DoobProductStep 12, TidyR10DoobFubini 6, TidyR10DoobMSVersion 7, TidyR9ItoFormulaVariants 17, TidyR12SDETools 13; copied from the Monetarism project) |
| [TidyR13MRepIntegral](ZeroBound/TidyR13MRepIntegral.lean), [TidyR13MRepCutoff](ZeroBound/TidyR13MRepCutoff.lean), [TidyR13MRepOneStep](ZeroBound/TidyR13MRepOneStep.lean), [TidyR13MRepDensity](ZeroBound/TidyR13MRepDensity.lean), [TidyR13MRepTheorem](ZeroBound/TidyR13MRepTheorem.lean), [TidyR13MRepMonetarism](ZeroBound/TidyR13MRepMonetarism.lean) | 83 | The martingale representation theorem on the Brownian filtration on `[0, T]`: the extended integrand class and integral `mrepInt`, integrands switched on over a sub-interval, the density argument, the theorem with uniqueness, instances on `bmPath` (TidyR13MRepIntegral 35, TidyR13MRepCutoff 15, TidyR13MRepOneStep 8, TidyR13MRepDensity 8, TidyR13MRepTheorem 11, TidyR13MRepMonetarism 6; copied from the Monetarism project, `TidyR13MRepMonetarism` in part) |
| [TidyR9StochWerningMRepVersion](ZeroBound/TidyR9StochWerningMRepVersion.lean) | 10 | §20.2.2 under uncertainty (tools): continuous and every-path-continuous versions of the extended Itô integral, martingale representation on `[0, ∞)` with one integrand, uniqueness |
| [TidyR9StochWerningInnovations](ZeroBound/TidyR9StochWerningInnovations.lean) | 18 | §20.2.2 under uncertainty: which innovations occur, `π = wPi(0) + e^{−λ^b t}(c + ∫H dW)` with `(c, H)` unique; the converse for the completed filtration, the exact correspondence for mean-square-bounded equilibria, continuous non-`C¹` loadings, non-vacuity |

## Modelling conventions

* **Expectations.** In the discrete-time modules random variables are `Ω → ℝ`, processes
  `ℕ → Ω → ℝ`, and every equation holds as an equality of functions for an arbitrary
  `ExpectationSystem`. A process is adapted when `E_tx_t = x_t` (`ExpectationSystem.Adapted`).
  Perfect foresight (`perfectForesight`) and every finite event tree are instances; the coin-flip
  tree (`ExpectationsFiniteTree.coinSystem`) gives a genuinely random sunspot at the peg
  (`ZLBPeg.coin_sunspot_equilibrium`). The worked examples
  `FutureSelection.zero_coefficient_not_unique` and `FutureSelection.fiscal_switch_example`, the
  orbit results of `ZLBRule` and `Links.peg_pf_path` are under perfect foresight; the orbit results
  under uncertainty are in `TidyR6OrbitStochastic`, which also uses the measure-theoretic
  expectations of `TidyR6ExpectationsMeasure` (Mathlib's `condExp`, equations almost
  everywhere).
* **Equilibrium and determinacy.** An equilibrium is an adapted process satisfying the model at
  every date and state, and the new-Keynesian selection is the bounded one (`BoundedProc`). A
  linear system is determinate when it has at most one bounded adapted solution for every
  forcing (`ExpectationSystem.Determinate`), characterised by Schur–Cohn (`SchurStable`). Future
  selection uses a deterministic switch date; the fiscal switch uses boundedness as its
  equilibrium criterion, which implies the transversality condition when `|ρ| < 1`.
* **Fiscal valuation.** In discrete time it is the linearised (5.13) at a constant interest rate
  with one-period debt, as a genuine infinite sum, starting from the steady state at date `−1`
  (`ZLBPeg.Valuation`). In continuous time it is the debt flow with an explicit transversality
  condition (`ZLBSelection.IsValuation`). Chapter 21 uses the frictionless level form
  `P = B/S` (`Covid.priceLevel`).
* **Continuous time.** Paths are deterministic functions `ℝ → ℝ`, continuous on `[0, ∞)`, that
  satisfy (20.5)–(20.6) by `HasDerivAt` off a countable set of dates, where the forcing jumps
  (`WerningModel.IsPath`). The equilibrium criterion is boundedness on `[0, ∞)`
  (`WerningModel.BddOnIci`); (20.8) uses forward stability, `e^{−λ^f t}π_t → 0`. Infinite-horizon
  integrals are Bochner integrals with proved integrability. In the experiment the natural rate
  is `u < 0` on `[0, T)` and `0` after, the interest rate is `0`, and the Phillips-curve
  disturbance is `g` on `[0, T)` and `0` after (`WerningModel.trapStep`). Selections are named by
  their pinned value: `π_T = 0` (new-Keynesian, `ZLBSelection.pi0NK`) and `π_0 = 0` (no jump,
  `ZLBSelection.piTnj`). Under uncertainty (`TidyR7StochWerning`) processes are `ℝ → Ω → ℝ` with
  continuous adapted paths (`TidyR7StochWerning.Regular`), `E_t dZ_t = D_t dt` means
  `E_s[Z_t − Z_s − ∫_s^t D] = 0` for `0 ≤ s ≤ t` (`TidyR7StochWerning.ExpDrift`), and the
  criterion is bounded first moments (`TidyR7StochWerning.BddL1`); the explicit equilibria live on
  the natural filtration of a pre-Brownian motion, such as `TidyR7BrownianExist.bmPath`.
* **Notation.** `λ₁`, `λ₂` are the discrete roots (5.6) (`ZLBPeg.lam1`, `ZLBPeg.lam2`); `λ^f`,
  `λ^b` the continuous-time roots (`ContinuousTimeNK.lamf`, `ContinuousTimeNK.lamb`). The
  functions `h` and `k` of the closed forms are `WerningModel.hh` and `WerningModel.kk`.
* **Welfare.** Welfare is compared through the exact steady-state relative-price dispersion of
  the Calvo model with constant inflation, and through the steady-state quadratic loss; the
  zero-bound steady state is `Π_L = β`, from (16.28) with `i = 0`.
* **Explicit hypotheses.** Hypotheses the book leaves implicit are stated in each theorem:
  `φ_t ≠ 0` before a monetary switch, `|ρ| < 1` and `γ_t ≠ 1` for the fiscal switch,
  `σκ > 0` and `φ > 1` for the rule, `u < 0`, `T > 0` and `ρ ≥ 0` for the limits and
  monotonicity in `κ`, and `0 < β ≤ 1`, `Π* ≥ 1` for the welfare comparison. The commitment
  theorems of `LinksGaliWoodford` take the form of the path from Galí's algorithm, with
  `t_C ≥ t_Z` and, where positivity after lift-off is used, `ξ₁,t_C+1 > 0` as hypotheses.
  `t_C ≥ t_Z` is proved for every optimum (`LiftoffTiming.liftoff_ge`), and versions for the
  optimum drop it (`LiftoffTiming.comm_gt_disc_opt`); `ξ₁,t_C+1 > 0` remains a hypothesis of
  (42)–(43), because it fails at some optima. The shape of the zero-rate spell assumes `ρ > 0`; with `ρ = 0`
  it holds iff `σκ < ϑ` (`LiftoffStructure.rho_zero_no_liftoff`,
  `LiftoffRhoZero.rho_zero_liftoff_iff`).

## Relation to the Woodford and Galí projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects, so the project builds on its own. Nothing is imported from
those projects. `GlobalDynamics` is a verbatim copy of the module of the same name in the
Woodford Chapter 2 project (`PriceLevelDetermination`), taken from its copy in the Chapter 16
project, with only the namespace changed: one-dimensional dynamics, the second steady state and
self-fulfilling deflations of (4.5)–(4.6). Here `ZLBRule` uses its attraction and repulsion
lemmas (`ZLBRule.lower_attracting`, `ZLBRule.upper_repelling`), and `Links` uses its map
`GlobalDynamics.map46`, which is Cochrane's (16.28), to identify the steady state at the bound
with `Π_L = β` (`Links.map46_fixed_beta_iff`, `Links.zlb_fixed_point_eq_beta`).

`LinksGaliWoodford` and `LinksGaliWoodfordLimit` link Chapter 20 to two other treatments of the
bound, and `LiftoffTiming`, `LiftoffStructure` and `LiftoffRhoZero` solve Galí's commitment
problem in that setting.
The definitions they need are restated, with docstrings "restated from the Galí Chapter 5
project" or "restated from the Woodford Chapter 6 project", and every result is proved here.

**Galí (2015), §5.4.2, in the `DiscretionCommitment` project (`ZLBCommitment`).** Galí solves
for the optimal commitment policy of a central bank facing the bound, with Kuhn–Tucker conditions
and a lift-off date `t_C + 1`, in the discrete model `π_t = βπ_{t+1} + κx_t`,
`x_t = x_{t+1} − σ⁻¹(i_t − π_{t+1} − rⁿ_t)` with natural rate `−η` on `[0, t_Z]` and `ρ` after.
* *Commitment is delayed lift-off with a positive promise.* At a zero rate the model is a
  monotone backward map (`LinksGaliWoodford.zr_strict`, `LinksGaliWoodford.zr_lower`). In the
  discrete delayed-lift-off family, lift-off at `t_Z + 1` is Galí's discretion, and `x_t`, `π_t`
  are strictly increasing and unbounded in the lift-off date (`LinksGaliWoodford.delay_eq_disc`,
  `LinksGaliWoodford.delay_lt_of_lt`, `LinksGaliWoodford.delay_pi0_tendsto`). Commitment obeys the
  same recursion on `[0, t_C]` and differs only by a strictly positive promised state at lift-off
  (`LinksGaliWoodford.comm_liftoff_pos`), so commitment > delay(`t_C + 1`) ≥ delay(`t_Z + 1`) =
  discretion (`LinksGaliWoodford.comm_gt_delay`, `LinksGaliWoodford.comm_gt_disc`), with
  `i = 0 < rⁿ` on `(t_Z, t_C]` (`LinksGaliWoodford.comm_rates`). Discretion has strictly larger
  loss (`LinksGaliWoodford.comm_loss_lt`, and from the conditions of Galí's algorithm alone,
  `LinksGaliWoodford.comm_loss_lt_alg`, via the restated
  `LinksGaliWoodford.algorithm_verification`).
* *The Werning family.* The bounded paths with `i = 0` in the trap and `i = rⁿ` after are exactly
  a one-parameter family indexed by `c = π_{t_Z+1}`, the discrete counterpart of
  `WerningModel.bdd_path_iff` (`LinksGaliWoodford.w_family_iff`); `c = 0` is discretion
  (`LinksGaliWoodford.w_zero`), and `π₀` moves by `λ₁^{t_Z+1}` per unit of `c`, a sensitivity that
  tends to `e^{λ^b t}` (`LinksGaliWoodford.w_pi0_sub`, `LinksGaliWoodford.sensitivity_tendsto_exp`).
  The commitment path's `π₀` equals that of exactly one member, whose promise `c` is strictly
  positive (`LinksGaliWoodford.comm_promise`); but if `t_C > t_Z` the commitment path is not
  itself a member (`LinksGaliWoodford.comm_not_member`). Cutting the time to the end of the trap
  into `n + 1` periods, every member's trap path converges to the continuous Werning path with
  `π_T = c` (`LinksGaliWoodfordLimit.trap_tendsto`).
* *Galí's sign condition, p. 150.* The positivity of (42)–(43) after lift-off needs
  `ξ₁,t_C+1 > 0`. This holds iff the price level at lift-off is below its long-run level
  (`LinksGaliWoodford.xi_pos_iff`, `LinksGaliWoodford.longrun_price`), and fails at an exact,
  verified optimum (`β = 9/10`, `κ = 1/10`, `ϑ = 1/819`, `σ = 1`, `ρ = 1/10`, `η = 1/100`,
  `t_Z = 0`), where output and inflation are negative from date 2 on and lift-off is at the end of
  the shock, `t_C = t_Z` (`LinksGaliWoodford.cex_optimal`, `LinksGaliWoodford.cex_xi_neg`,
  `LinksGaliWoodford.cex_liftoff_at_shock_end`). Commitment still lies above discretion on the
  zero-rate spell (`LinksGaliWoodford.comm_gt_disc_of_state`).
* *Lift-off timing, proved (`LiftoffTiming`).* At the commitment optimum the bound binds on all
  of `[0, t_Z]`, so `t_C ≥ t_Z`, for all `β ∈ (0,1)`, `κ, σ, ϑ, η > 0` and `ρ ≥ 0`
  (`LiftoffTiming.optimal_trap_binds`, `LiftoffTiming.optimal_h48`, `LiftoffTiming.liftoff_ge`,
  `LiftoffTiming.liftoff_ge_mult`, `LiftoffTiming.liftoff_after_shock`). The proof has two steps.
  First, the KKT conditions are necessary (`LiftoffTiming.kkt_necessary`): raising the rate at a
  single date is a finite-support direction whose loss derivative is `β^s ξ₂,s/σ`, which gives
  `ξ₂ ≥ 0` and complementary slackness, and transversality `β^t ξ₂,t → 0` follows from Tannery's
  theorem after subtracting the bounded peg mode (`LiftoffTiming.cross_hdir`,
  `LiftoffTiming.tendsto_mxi2`). Second, the rate gap and the multiplier combination are both
  second-difference operators of inflation, so discrete maximum principles apply: commitment
  inflation never exceeds `η` (`LiftoffTiming.optimal_pi_le`), and a slack date in the shock gives
  a negative rate when `σκ ≤ ϑ` and explosive peg dynamics when `ϑ < σκ`
  (`LiftoffTiming.slack_contra_le`, `LiftoffTiming.slack_contra_gt`,
  `LiftoffTiming.trap_mult_pos`). The commitment theorems hold for the optimum without the
  hypotheses `t_C ≥ t_Z` and (48) (`LiftoffTiming.comm_gt_disc_opt`,
  `LiftoffTiming.comm_loss_lt_opt`, `LiftoffTiming.comm_promise_opt`,
  `LiftoffTiming.comm_gt_disc_of_state_opt`), and the verification theorem holds for an arbitrary
  guess, proving `t_Z ≤ t_C`: Galí's guess is without loss of generality
  (`LiftoffTiming.algorithm_verification_gen`, `LiftoffTiming.comm_loss_lt_alg_gen`). Earlier
  numerical "counterexamples" were round-off at weights `β^t` near `10⁻¹⁷`.
* *The optimum characterised (`LiftoffStructure`).* Coding paths in a weighted `ℓ²(ℕ ⊕ ℕ)` makes
  the loss a squared norm and the feasible set closed and convex, so the Hilbert projection
  theorem gives existence, and strict convexity uniqueness, for every `ρ ≥ 0` and `t_Z`
  (`LiftoffStructure.exists_optimal`, `LiftoffStructure.optimal_exists_unique`). After the shock
  the bound never re-binds once it is slack (`LiftoffStructure.no_return`), lift-off is finite
  for `ρ > 0` (`LiftoffStructure.exists_slack_after`), and Galí's closed form (37)–(43) after
  lift-off is necessary (`LiftoffStructure.post_form`). Hence, for `κ, σ, ϑ, ρ, η > 0`, the
  binding set is an initial interval `[0, t_C]` with `t_C ≥ t_Z` and `i > 0` after
  (`LiftoffStructure.optimal_binding`, `LiftoffStructure.optimal_liftoff`), the optimum satisfies
  every hypothesis of Galí's algorithm (`LiftoffStructure.optimal_algorithm_form`), and the
  whole statement is `LiftoffStructure.commitment_characterisation`.
* *A zero post-shock natural rate.* With `ρ = 0` the optimum either keeps the rate at zero forever
  or has `σκ ≠ ϑ` and the shape above (`LiftoffStructure.rho_zero_structure`, with the
  post-lift-off rates of `LiftoffStructure.liftoff_rates`). At `σκ = ϑ` it never lifts off
  (`LiftoffStructure.rho_zero_unit_ratio`, `LiftoffStructure.rho_zero_no_liftoff`, exact instance
  `LiftoffStructure.rho_zero_instance`), so `ρ > 0` in the characterisation is necessary.
  `LiftoffRhoZero` classifies the case completely: the rate is zero forever iff `ϑ ≤ σκ`
  (`LiftoffRhoZero.rho_zero_zero_iff`), not only at `σκ = ϑ`, and lifts off iff `σκ < ϑ`
  (`LiftoffRhoZero.rho_zero_liftoff_iff`). If `σκ < ϑ`, a zero-rate optimum would have post-shock
  inflation `μʲπ_{t_Z+1}` with `π_{t_Z+1} > 0`, decaying at the stable peg root `μ`
  (`LiftoffRhoZero.peg_geometric`, `LiftoffRhoZero.zero_rate_pi_pos`). This forces the bound's
  multipliers resonantly, so they explode or turn negative (`LiftoffRhoZero.forced_mult_contra`,
  `LiftoffRhoZero.rho_zero_lt_not_zero`). If `ϑ < σκ`, a lift-off would bring deflation and a
  recession, and nonnegative rate gaps would carry the fall back to date 0. The whole path would
  then be nonpositive, which no optimum is (`LiftoffRhoZero.back_rise`,
  `LiftoffRhoZero.nonpos_contra`, `LiftoffRhoZero.rho_zero_gt_no_slack`). On the lift-off
  branch Galí's sign condition `ξ₁,t_B+1 > 0` holds automatically
  (`LiftoffRhoZero.rho_zero_branch_b`), and a verification theorem for `ρ = 0`
  (`LiftoffRhoZero.verification_zero`) certifies exact optima on both sides.
* *What remains open.* Galí's sign condition `ξ₁,t_C+1 > 0` remains a genuine hypothesis of the
  positivity of (42)–(43) and of the results that use it, because it fails at some optima with
  `ρ > 0` (`LinksGaliWoodford.cex_xi_neg`).

**Woodford (2003), Chapter 6, §4.2, in the `StabilizationWelfare` project (`ZLB.lean`).**
Proposition 6.9 replaces the bound by a constraint on the discounted mean and second moment of
the interest rate, `Ê[i] ≥ 0` and `Ê[i²] ≤ K(Ê[i])²`. In `ZLB.lean` it is stated over an abstract
convex policy set. That module and `Sequences` are copied here verbatim, with only the namespace
changed (`TidyR6WoodfordZLB`, `TidyR6WoodfordSequences`), and `TidyR6CommonModel` instantiates the
policy set with the discrete model of Chapter 20 and Galí's loss, so that both problems live in
one model.
* The common model. The interest rate implied by the IS curve is linear in the policy, the
  structural hypotheses of Proposition 6.9 are proved (`TidyR6CommonModel.cset_convex`,
  `TidyR6CommonModel.loss_convexOn`, `TidyR6CommonModel.mom1_affine`,
  `TidyR6CommonModel.mom2_convexOn`), and the proposition holds there
  (`TidyR6CommonModel.prop_6_9_common`). The zero bound is the other special case: the pathwise
  optimum is exactly `LinksGaliWoodford.Optimal` (`TidyR6CommonModel.pathOpt_iff`). The
  moment-constrained optimum exists iff the constraints can be met, and is unique
  (`TidyR6CommonModelExist.momOpt_exists_iff`, `TidyR6CommonModel.momOpt_unique`); in the trap it
  exists whenever `Kβ ≥ 1`, which holds at Woodford's calibration
  (`TidyR6CommonModelExist.momOpt_existsUnique_trap`). Model-feasible witnesses show that neither
  constraint implies the other (`TidyR6CommonModel.neither_in_model`), and the optimal losses
  compare as the constraint sets do (`TidyR6CommonModel.values_compare`).
* Neither constraint implies the other (`LinksGaliWoodford.Moments.neither_implies`). The
  pathwise bound gives `Ê[i] ≥ 0` (`LinksGaliWoodford.Moments.pathwise_mean_nonneg`), and gives
  Woodford's constraint under a band condition (`LinksGaliWoodford.Moments.band_moment_feasible`).
  Conversely, Woodford's constraint bounds the discounted frequency of `i < 0` by
  `1/(1 + k²)`, a Cantelli bound, where the pathwise bound requires `0`
  (`LinksGaliWoodford.Moments.violation_freq_le`,
  `LinksGaliWoodford.Moments.pathwise_violation_freq`).
* Welfare. At constant inflation Woodford's dispersion recursion (2.20) converges to Cochrane's
  stationary dispersion (`LinksGaliWoodford.disp_const_tendsto`), and under Woodford's discounted
  criterion `Π_L = β` is better than `Π*` iff `1 < βΠ*`, as in E9
  (`LinksGaliWoodford.woodford_zlb_better_iff`). Galí's deflationary steady state `π = −ρ`, `i = 0`
  is `Π_L = β`, and it is strictly worse than his zero-inflation target in all three measures
  (`LinksGaliWoodford.gali_deflation_steady`, `LinksGaliWoodford.gali_deflation_worse`).

## Relation to other Cochrane projects

* **Chapter 5 (`StickyPriceFiscal`).** Much of the calculus of `ContinuousTimeNK` (exponential
  limits, improper integrals, the forward integral, the forward value iff the transversality
  condition) is restated from that project's `CTSimple`, and the scaled-root block,
  `Links.tendsto_peg_decay` and `Links.tendsto_peg_impact` from its `Links`; the docstrings say
  "restated from the Cochrane Chapter 5 project". The model (5.1)–(5.2), the roots (5.6) and the
  valuation equation (5.13), which `ZLBPeg` uses at a peg, are formalised there in general. New
  here are the backward integral, variation of constants off a countable set, and (20.8).
* **Chapter 16 (`NewKeynesianSelection`).** `GlobalDynamics` is that project's copy. That project
  proves the lower bound of §16.8: `Π_L` is the largest fixed point of the map in `[β, Π*)`, with
  its error E2 corrected. Here `Π_L = β` exactly, the case in which the rule is at the bound at
  `Π_L` (`ZLBWelfare.zlb_steady_state`, `Links.zlb_fixed_point_eq_beta`); `Π_L` above `β`, as in
  the 1% example of p. 380, is covered by `ZLBWelfare.zlb_better_of_one_le`. The indeterminacy of
  the frictionless model under a passive rule, proved there, appears here as
  `FutureSelection.passive_forever_not_unique`.
* **Chapter 6 (FiscalConstraints) and Chapter 19 (Monetarism).** The twelve Brownian-motion and
  Itô modules (`TidyR7BrownianSchauder` to `TidyR7ItoBridge`) are copies of the Monetarism
  project's, taken from the FiscalConstraints project's copies, and `ExpIntegrals`, `LinearODE`,
  `TidyR7OUPath`, `TidyR7WienerGaussian` and `TidyR7OrnsteinUhlenbeck` are copies of
  FiscalConstraints' own modules, all with only the namespace renamed and proofs unchanged; the
  docstrings say "Restated from the Cochrane Monetarism project" or "Restated from the Cochrane
  FiscalConstraints project" and name the original. `TidyR7OUSampled` copies only the innovation
  part of FiscalConstraints' module of that name, and the four tail-event tools at the start of
  `TidyR8StochWerningRecurrence` are restated from its DebtLimitStochasticMeasure module, where
  they give the almost-sure unboundedness of debt. There the Ornstein–Uhlenbeck process is the
  AR(1) surplus of p. 197; here it is the stable-direction inflation innovation and the
  natural-rate shock of the stochastic Werning model. A further thirty-two Monetarism modules
  (`TidyR10DoobDiscrete` to `TidyR13MRepMonetarism` in the library map: Doob's inequality,
  continuous versions of the Itô integral, Itô's formula and the martingale representation
  theorem) are copied directly from the Monetarism project, with only the namespace renamed and
  proofs unchanged, as the import closure that `TidyR9StochWerningMRepVersion` needs; there they
  serve the (1.32) product step of Online Appendix §1.6, here the description of the
  innovations of the stochastic Werning model. `TidyR8MonetarismItoDom` keeps only its four Itô
  tools and `TidyR13MRepMonetarism` only its six results without the stochastic discount factor;
  no Monetarism economics module is copied.
* **Chapter 22 (`ObservationalEquivalence`).** That project owns the observational-equivalence
  remark of p. 476 and the Leeper model (23.1)–(23.4) with constant coefficients and its four
  regions (`LeeperRegions`), and the Markov-switching determinacy condition of Davig and Leeper
  (`MarkovRegimes`). `FutureSelection` treats the same model with time-varying coefficients and a
  deterministic switch, and `TidyR6RegimeEigen` with constant coefficients along a continuous path
  of parameters. The measure-theoretic expectations (`TidyR6ExpectationsMeasure`,
  `TidyR6ExpectationsMeasureIID`) are copied from that project with the namespace renamed.

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
