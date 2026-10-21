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
improper integrals. In both, an equilibrium is a solution of the model equations, "determinate"
means exactly one bounded solution, and the fiscal theory selects instead through the valuation
equation. The library contains **761 theorems**, including the shared core; 653 of them are in
the seventeen chapter modules, 49 of these in a verbatim copy of Woodford Chapter 2 results
(`GlobalDynamics`), and 241 in the four modules on Galí's and Woodford's treatments of the bound
(`LinksGaliWoodford`, `LinksGaliWoodfordLimit`, `LiftoffTiming`, `LiftoffStructure`).

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
  `ZLBRule.locally_bounded_unique_E`).
* **Future selection.** An active rule from date `T` on selects a unique bounded equilibrium
  whatever the policy before `T`, provided the rule coefficient `φ_t` is nonzero
  (`FutureSelection.future_selection`); the hypothesis `φ_t ≠ 0`, implicit in the book, cannot be
  dropped (`FutureSelection.zero_coefficient_not_unique`). The Davig–Leeper fiscal switch: an
  expected switch to active fiscal policy selects, and fiscal shocks move inflation even while
  money is active (`FutureSelection.fiscal_switch_selects`,
  `FutureSelection.fiscal_switch_unexpected_inflation`, `FutureSelection.fiscal_switch_example`).
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
  than without (`Covid.joint_less_painful`).
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
  nor the pathwise bound implies the other (`LinksGaliWoodford.Moments.neither_implies`). See
  the relation to the Woodford and Galí projects below.
* **The commitment optimum.** At the optimum the bound binds on the whole shock, so the lift-off
  date satisfies `t_C ≥ t_Z` and Galí's guess is without loss of generality
  (`LiftoffTiming.optimal_trap_binds`, `LiftoffTiming.liftoff_ge`,
  `LiftoffTiming.algorithm_verification_gen`); commitment inflation never exceeds the depth of the
  shock (`LiftoffTiming.optimal_pi_le`). For `ρ > 0` the optimum exists, is unique, and keeps the
  rate at zero exactly on `[0, t_C]` and positive after
  (`LiftoffStructure.commitment_characterisation`); it is always the path of Galí's algorithm
  (`LiftoffStructure.optimal_algorithm_form`). With `ρ = 0` and `σκ = ϑ` the rate never lifts off
  (`LiftoffStructure.rho_zero_no_liftoff`).

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
and lift-off needs a positive post-shock natural rate (`LiftoffStructure.rho_zero_no_liftoff`).

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
* the Chapter 24 remark that leaving the active-money regime "requires a discrete shift … to move
  eigenvalues" (p. 523), and the literature reviews of §§20.2.6 and 24;
* the verbal claim that it is "impossible to produce a deep recession without deep but improving
  deflation" (p. 477), which has no precise statement;
* the illustrative numbers of Figures 20.4–20.6 (`π_0 = −132.46%`, `π_T ≈ 1.01%`, multipliers of
  66 and 528); only the E20 point `T = 1` is formalised;
* an exact relation between the discrete early lift-off of Figure 20.3 and the continuous-time
  delayed lift-off, whose models and parameters do not match, and between the nonlinear Covid
  helicopter `P = B/S` and the linearised valuation equations, beyond the frictionless limit of
  the impact coefficient (`Links.fiscal_impact_frictionless`);
* which calibrations with `ρ = 0` and `σκ ≠ ϑ` never lift off: the exact dichotomy is proved
  (`LiftoffStructure.rho_zero_structure`), and `σκ = ϑ` always lands in the never-lift-off branch,
  but the converse is not (see the relation to the Woodford and Galí projects below);
* a structural link with Woodford's Proposition 6.9, which shares no model equations with
  Chapter 20; the link is at the level of the constraint;
* stochastic versions of the continuous-time results, and of the global orbit results of
  §20.2.1, which are under perfect foresight as in the book; local uniqueness and the Figure
  20.3 selection hold for any expectation operator.

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

## Modelling conventions

* **Expectations.** In the discrete-time modules random variables are `Ω → ℝ`, processes
  `ℕ → Ω → ℝ`, and every equation holds as an equality of functions for an arbitrary
  `ExpectationSystem`. A process is adapted when `E_tx_t = x_t` (`ExpectationSystem.Adapted`).
  Perfect foresight (`perfectForesight`) and every finite event tree are instances; the coin-flip
  tree (`ExpectationsFiniteTree.coinSystem`) gives a genuinely random sunspot at the peg
  (`ZLBPeg.coin_sunspot_equilibrium`). The worked examples
  `FutureSelection.zero_coefficient_not_unique` and `FutureSelection.fiscal_switch_example`, the
  orbit results of `ZLBRule` and `Links.peg_pf_path` are under perfect foresight.
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
  `ZLBSelection.piTnj`).
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
  (42)–(43), because it fails at some optima. The shape of the zero-rate spell assumes `ρ > 0`, which is
  necessary (`LiftoffStructure.rho_zero_no_liftoff`).

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
bound, and `LiftoffTiming` and `LiftoffStructure` solve Galí's commitment problem in that setting.
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
* *What remains open.* Which calibrations with `ρ = 0` and `σκ ≠ ϑ` never lift off is not
  settled; the dichotomy is exact, but "never lifts off iff `σκ = ϑ`" is not claimed. Galí's sign
  condition `ξ₁,t_C+1 > 0` remains a genuine hypothesis of the positivity of (42)–(43) and of the
  results that use it, because it fails at some optima (`LinksGaliWoodford.cex_xi_neg`).

**Woodford (2003), Chapter 6, §4.2, in the `StabilizationWelfare` project (`ZLB.lean`).**
Proposition 6.9 replaces the bound by a constraint on the discounted mean and second moment of
the interest rate, `Ê[i] ≥ 0` and `Ê[i²] ≤ K(Ê[i])²`. In `ZLB.lean` it is stated over an abstract
convex policy set, so it shares no IS or Phillips-curve equations with Chapter 20, and the link
is at the level of the constraint.
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
* **Chapter 22 (`ObservationalEquivalence`).** That project owns the observational-equivalence
  remark of p. 476 and the Leeper model (23.1)–(23.4) with constant coefficients and its four
  regions (`LeeperRegions`), and the Markov-switching determinacy condition of Davig and Leeper
  (`MarkovRegimes`). `FutureSelection` treats the same model with time-varying coefficients and a
  deterministic switch.

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
