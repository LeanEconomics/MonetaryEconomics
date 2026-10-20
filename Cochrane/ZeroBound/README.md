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
equation. The library contains **520 theorems**, including the shared core; 412 of them are in
the thirteen chapter modules, 49 of these in a verbatim copy of Woodford Chapter 2 results
(`GlobalDynamics`).

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
delayed lift-off the positive post-trap natural rate it needs.

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
  monotonicity in `κ`, and `0 < β ≤ 1`, `Π* ≥ 1` for the welfare comparison.

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

Two other projects treat the zero bound differently, and no theorem links them to this one:
* Galí (2015), §5.4.2, in the `DiscretionCommitment` project (`ZLBCommitment`): the optimal
  commitment policy of a central bank facing the bound, with the bound as an inequality
  constraint, Kuhn–Tucker conditions and an announced lift-off date, after which inflation and
  the output gap are positive. Commitment to a later lift-off and to inflation after the trap is
  the content of the delayed lift-off and the glide path of §20.2.4
  (`ForwardGuidance.delay_pi0`, `ForwardGuidance.glide_path`), here studied as equilibrium
  selection rather than as an optimum.
* Woodford (2003), Chapter 6, §4.2, in the `StabilizationWelfare` project (`ZLB.lean`):
  Proposition 6.9, optimal stabilisation when the bound is replaced by a constraint on the mean
  and variance of the interest rate. It is a stochastic, second-moment treatment, while
  Chapter 20 is about the equilibria of a deterministic trap.

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
