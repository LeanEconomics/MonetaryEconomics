# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, "The zero bound"
(pp. 465–485), the model claims and arithmetic of Chapter 21, "The Covid inflation"
(pp. 486–494), and the future-selection claims of Chapter 24 (pp. 522–524). Each formal claim is
listed with its Lean name, relative to the namespace `Cochrane.ZeroBound`. Page numbers are book
pages. The book has no labelled propositions, so rows are keyed by equation number, figure,
table or page. Rows follow the book section by section, and each heading names the modules that
formalise the section: §20.1, §20.2.1 with the Chapter 24 claims, §§20.2.2–20.2.6, §20.3,
Chapter 21, then the links between the modules, the restated Woodford block and the shared
tools.

The discrete-time results (§20.1, §20.2.1, §20.2.6, Chapter 24) hold for an arbitrary
`ExpectationSystem`, so under perfect foresight and under uncertainty, except where a row says
"perfect foresight". An *equilibrium* is an adapted process satisfying the model equations at
every date and state; *determinate* means at most one bounded adapted equilibrium for every
forcing (`ExpectationSystem.Determinate`). The continuous-time results (§§20.2.2–20.2.5) are
about deterministic paths `ℝ → ℝ` that satisfy the ODEs by `HasDerivAt` off a countable set;
the equilibrium criterion is boundedness on `[0, ∞)`. Survey error codes E1–E11 and E20 are
those of the survey of Chapters 20–25 (`notes/survey_cochrane_ch20-25.md`); see
[corrections](corrections.md). Rows marked "restated" reproduce results proved in an earlier
project, with the namespace adapted.

## §20.1 The experiment: the new-Keynesian model at a peg, pp. 465–469 (ZLBPeg)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (5.6), p. 119; used p. 467 | the roots `λ₁, λ₂` of `λ² − (1 + β + σκ)λ + β`, with the discriminant written as the core `discQ`; their sum, product and ordering | `ZLBPeg.lam1`, `ZLBPeg.lam2`, `ZLBPeg.disc_pos`, `ZLBPeg.lam_add`, `ZLBPeg.lam_mul`, `ZLBPeg.lam_root`, `ZLBPeg.lam2_le_lam1`, `ZLBPeg.lam2_pos` |
| Cochrane p. 119; p. 467 | the roots straddle the unit circle, `0 < λ₂ < 1 < λ₁` | `ZLBPeg.one_lt_lam1`, `ZLBPeg.lam2_lt_one` |
| Cochrane (5.1)–(5.2), p. 118, at a peg `i_t = ī` | the model `PegEq`; its backward form `z_t = AE_tz_{t+1} + w` with `A = [[1, σ], [κ, β + σκ]]`; `E_t` of an affine combination | `ZLBPeg.PegEq`, `ZLBPeg.pegMatrix`, `ZLBPeg.pegForcing`, `ZLBPeg.E_affine2`, `ZLBPeg.pegEq_iff_solves` |
| Cochrane (5.6), p. 119; p. 467 | trace `1 + β + σκ` and determinant `β`; the eigenvalues are `λ₁, λ₂` and straddle the unit circle; Schur–Cohn fails | `ZLBPeg.pegMatrix_tr_det`, `ZLBPeg.pegMatrix_roots`, `ZLBPeg.peg_not_schurStable` |
| Cochrane p. 467 | "inflation is indeterminate at the zero bound": the peg system is not determinate; its steady state is `π = ī`, `x = (1 − β)ī/κ` | `ZLBPeg.peg_not_determinate`, `ZLBPeg.peg_steady` |
| Cochrane p. 467 | exact characterisation of the bounded equilibria: the combination `q = κx + (λ − 1)π + (β − λ)ī` obeys `q_t = λE_tq_{t+1}`; the unstable one is pinned; `π − ī` follows the stable recursion; conversely these imply the model | `ZLBPeg.pegQ`, `ZLBPeg.peg_q_step`, `ZLBPeg.peg_slaving`, `ZLBPeg.peg_pi_rec`, `ZLBPeg.pegEq_of_slaving`, `ZLBPeg.peg_equilibrium_iff` |
| Cochrane p. 467 | every bounded equilibrium is `π = ī + p`, `x = pegX p` with `p_t = λ₁E_tp_{t+1}`, and every such `p` gives one | `ZLBPeg.pegPi`, `ZLBPeg.pegX`, `ZLBPeg.E_pegPi`, `ZLBPeg.pegEq_of_sunspot`, `ZLBPeg.peg_equilibrium_char` |
| Cochrane p. 467 ("there are many equilibria … sunspots") | any bounded martingale-difference sunspot `δ` gives an equilibrium with inflation surprise `δ`; the set of equilibria is uncountable; on the coin-flip tree there is a genuinely random sunspot equilibrium | `ZLBPeg.sunspot_equilibrium`, `ZLBPeg.sunspot_innovation`, `ZLBPeg.peg_continuum`, `ZLBPeg.coin_sunspot_equilibrium` |
| Cochrane p. 467 ("inflation is stable at the zero bound") | in every bounded equilibrium `E_sπ_{s+k} → ī` | `ZLBPeg.peg_expected_converges` |
| Cochrane (5.13), p. 121, at a constant rate | the linearised valuation equation `ΔE_{t+1}∑ρʲπ_{t+1+j} = −ε_{t+1}` as a genuine `HasSum`, from the steady state at date `−1`; the discounted sums for `E_tp_{t+1} = rp_t` | `ZLBPeg.Valuation`, `ZLBPeg.valuation_sum0`, `ZLBPeg.valuation_sum` |
| Cochrane p. 469 ("add active fiscal policy … stable, determinate, and quiet") | the fiscal equilibrium `fiscalP`; the valuation equation pins it; exactly one bounded adapted equilibrium for every bounded fiscal-news process and `0 ≤ ρ ≤ 1`; unexpected inflation `−(1 − ρ/λ₁)ε`; stable; quiet without fiscal news | `ZLBPeg.fiscalP`, `ZLBPeg.valuation_pins`, `ZLBPeg.fiscal_selects`, `ZLBPeg.fiscal_unexpected_inflation`, `ZLBPeg.fiscal_stable`, `ZLBPeg.fiscal_quiet` |
| Cochrane p. 469 | a date-0 deflation happens iff the date-0 fiscal news is a contraction | `ZLBPeg.deflation_iff_fiscal_contraction` |

## §20.2.1 Removing sunspots? The rule with a zero bound, pp. 471–474, Figure 20.3 (ZLBRule)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (20.1), p. 472 | the rule `i = max[π* + φ(π − π*), 0]`; the static-IS model with the rule | `ZLBRule.rule`, `ZLBRule.ZLBEq` |
| Cochrane (20.2), p. 472 | eliminating `x`; the map form `E_tπ_{t+1} = f_u(π_t)` | `ZLBRule.fmap`, `ZLBRule.eq20_2_iff`, `ZLBRule.eq20_2_iff_map` |
| Cochrane (20.3)–(20.4), p. 472 (E1) | the kink is at `π*(φ − 1)/φ`; the two branches; the printed threshold `π* + (φ − 1)` is false (at the Figure 20.3 values the kink is 1, not 3) | `ZLBRule.kink`, `ZLBRule.slopeR`, `ZLBRule.kink_iff`, `ZLBRule.eq20_3`, `ZLBRule.eq20_4`, `ZLBRule.active_of_kink_le`, `ZLBRule.kink_fig203`, `ZLBRule.e1_printed_threshold_false` |
| Cochrane p. 472 (phase diagram) | the map is continuous, strictly increasing and onto, with slopes `1/(1 + σκ) < 1` and `(1 + φσκ)/(1 + σκ)`, greater than one iff `φ > 1` | `ZLBRule.fmap_continuous`, `ZLBRule.fmap_strictMono`, `ZLBRule.fmap_surjective`, `ZLBRule.hasDerivAt_fmap_left`, `ZLBRule.hasDerivAt_fmap_right`, `ZLBRule.slope_left_lt_one`, `ZLBRule.slope_right_gt_one_iff` |
| Cochrane pp. 472–473 | contraction on the zero-bound branch ("converging as time goes forward"), expansion on the active branch ("alternative equilibria diverge") | `ZLBRule.zlb_branch_contraction`, `ZLBRule.active_branch_expansion` |
| Cochrane p. 472 | the steady states with `u_r = 0` are exactly `0` and `π*`; the lower one attracts and the upper one repels | `ZLBRule.fixed_u_zero`, `ZLBRule.lower_attracting`, `ZLBRule.upper_repelling` |
| Cochrane p. 472 (E2) | with `u < 0` the candidates `−u` and `π* + u/(φ − 1)`; both are steady states iff `−u ≤ π*(φ − 1)/φ`, otherwise there is none; they are pushed in | `ZLBRule.fixed_iff`, `ZLBRule.upper_on_branch_iff`, `ZLBRule.steady_exists_iff`, `ZLBRule.both_steady`, `ZLBRule.steady_states_pushed_in` |
| Cochrane p. 472, Figure 20.3 values (E2) | no steady state during the shock: `f_u(π) − π ≥ 1/3` for all `π`; the printed steady states `2` and `0` are not fixed points | `ZLBRule.fig203_no_steady_state`, `ZLBRule.fig203_printed_steady_states_false` |
| Cochrane pp. 473–474, perfect foresight, `u = 0` | the kink lies in `(0, π*)`; orbits above `π*` explode; orbits below converge to zero inflation and eventually zero rates; the bounded orbits are exactly those with `π₀ ≤ π*`; `π*` is the only locally bounded one | `ZLBRule.active_affine`, `ZLBRule.kink_mem`, `ZLBRule.orbit_above`, `ZLBRule.orbit_below_tendsto_zero`, `ZLBRule.orbit_below_rate_zero`, `ZLBRule.bounded_orbits_eq`, `ZLBRule.locally_bounded_unique` |
| Cochrane p. 473, any `ExpectationSystem` | `π*` is the only locally bounded equilibrium from date `T` on (via the shifted expectation system) | `ZLBRule.shiftE`, `ZLBRule.locally_bounded_unique_E` |
| Cochrane p. 472 | once `π_T` is fixed, the path before `T` is unique and deterministic; with the active rule from `T` on, the selected path exists | `ZLBRule.backward_unique`, `ZLBRule.backward_exists` |
| Cochrane Figure 20.3, pp. 472–473 | the natural rate `−2` before `T = 10` and `0` from `T` on; the future rule selects `π_t = 2` for `t ≥ 10` and `π₉ = 3/2`, `π₈ = 9/8`, `π₇ = 11/16`, `π₆ = 1/32` | `ZLBRule.uFig`, `ZLBRule.fig203_selection` |
| Cochrane p. 472 (E3) | "while the nominal rate remains stuck at zero" is false: `i₉ = 1`, `i₈ = 1/4`, `i₇ = i₆ = 0` | `ZLBRule.fig203_early_liftoff` |

## §20.2.1 and Chapter 24: selection by expected future policy, p. 472 and pp. 522–524 (FutureSelection)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 472; Ch. 24, p. 523 | the engine: `c_ty_t = dE_ty_{t+1} + f_t` with `c_t ≠ 0` before `T` and `c_t = c_A`, `\|d\| < \|c_A\|` from `T` on has exactly one bounded adapted solution; a recursion contracting after `T` is bounded | `FutureSelection.switch_scalar`, `FutureSelection.bounded_of_rec` |
| Cochrane p. 472 (frictionless version) | the model `E_tπ_{t+1} = φ_tπ_t + u_t` and its scalar form | `FutureSelection.RuleEq`, `FutureSelection.ruleEq_iff` |
| Cochrane p. 472 ("expectation of future equilibrium-selection policy can select equilibria even when policy is currently … passive") | any nonzero `φ_t` before `T` and `\|φ_A\| > 1` from `T` on: exactly one bounded adapted equilibrium, under any `ExpectationSystem` | `FutureSelection.future_selection` |
| Cochrane p. 467 and p. 472 (contrast) | passive policy forever leaves uncountably many bounded equilibria; with a pure peg `φ₀ = 0` future policy does not pin `π₀` (perfect foresight) | `FutureSelection.passive_forever_not_unique`, `FutureSelection.zero_coefficient_not_unique` |
| Cochrane (23.1)–(23.4), p. 512, with time-varying `φ_t`, `γ_t` (Ch. 24, p. 522) | the Leeper model with a date-0 flow; `ρE_tv_{t+1} = (1 − γ_t)v_t − E_tu_{s,t+1}` | `FutureSelection.LeeperEq`, `FutureSelection.leeper_debt_eq` |
| Cochrane Ch. 24, p. 523 (Davig and Leeper 2007) | passive fiscal policy (`γ_t ≠ 1`) and any monetary rule before `T`, active fiscal and passive money from `T` on: exactly one bounded adapted equilibrium for `\|ρ\| < 1` | `FutureSelection.fiscal_switch_selects` |
| Cochrane Ch. 24, pp. 523–524 ("fiscal shocks affect inflation immediately even in the locally-active money/passive fiscal … regime") | unexpected inflation `−ρΔE_{t+1}v_{t+1} − ΔE_{t+1}u_{s,t+1}` in every equilibrium; an explicit example with `φ₀ = 2` and `π₀ = −2δ` for a post-switch surplus `δ` (perfect foresight) | `FutureSelection.fiscal_switch_unexpected_inflation`, `FutureSelection.fiscal_switch_example` |
| Cochrane Ch. 24, p. 523 (contrast) | without the switch, an active monetary rule forever makes inflation independent of fiscal policy | `FutureSelection.no_switch_fiscal_irrelevant` |

## §20.2.2 The continuous-time model: roots, integrals and linear ODEs, pp. 474–475 (ContinuousTimeNK)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 475 | the roots `λ^f = (√(ρ² + 4κσ) + ρ)/2`, `λ^b = (√(ρ² + 4κσ) − ρ)/2`; positivity, `λ^fλ^b = κσ`, `λ^f − λ^b = ρ`, `λ^f + λ^b = √(ρ² + 4κσ)`; the roots of `λ² − ρλ − κσ` and its factorisation | `ContinuousTimeNK.lamf`, `ContinuousTimeNK.lamb`, `ContinuousTimeNK.abs_lt_sqrt_disc`, `ContinuousTimeNK.sq_sqrt_disc`, `ContinuousTimeNK.lamf_pos`, `ContinuousTimeNK.lamb_pos`, `ContinuousTimeNK.lamf_mul_lamb`, `ContinuousTimeNK.lamf_sub_lamb`, `ContinuousTimeNK.lamf_add_lamb`, `ContinuousTimeNK.lamf_add_lamb_pos`, `ContinuousTimeNK.lamf_root`, `ContinuousTimeNK.lamb_root`, `ContinuousTimeNK.charpoly_factor` |
| Cochrane p. 475 | `κσ/λ^f = λ^b`; `λ^b ≤ λ^f` for `ρ ≥ 0`; the bounds `λ^b ≥ √(κσ) − ρ/2`, `λ^f ≥ √(κσ) + ρ/2` | `ContinuousTimeNK.kappa_sigma_div_lamf`, `ContinuousTimeNK.lamb_le_lamf`, `ContinuousTimeNK.sqrt_sub_le_lamb`, `ContinuousTimeNK.sqrt_add_le_lamf` |
| Cochrane pp. 477–479 | both roots are strictly increasing in `κ` and tend to infinity as `κ → ∞` | `ContinuousTimeNK.lamb_strictMono`, `ContinuousTimeNK.lamf_strictMono`, `ContinuousTimeNK.sqrt_kappa_tendsto`, `ContinuousTimeNK.lamb_tendsto_atTop`, `ContinuousTimeNK.lamf_tendsto_atTop` |
| Cochrane §5.7, pp. 163–167 (restated from the Chapter 5 project); p. 475 | derivatives and limits of exponentials; improper integrals and shifts; bounded paths satisfy the transversality condition; integrability and bounds of discounted paths; the forward value iff the transversality condition (5.95) | `ContinuousTimeNK.hasDerivAt_expNeg`, `ContinuousTimeNK.hasDerivAt_expPos`, `ContinuousTimeNK.tendsto_expNeg`, `ContinuousTimeNK.tendsto_expPos`, `ContinuousTimeNK.tendsto_of_deriv_Ioi`, `ContinuousTimeNK.integral_Ioi_shift`, `ContinuousTimeNK.integral_exp_shift`, `ContinuousTimeNK.tvc_of_bounded`, `ContinuousTimeNK.integrableOn_exp_mul_of_bdd`, `ContinuousTimeNK.abs_integral_exp_le`, `ContinuousTimeNK.integral_exp_Ioi`, `ContinuousTimeNK.integrableOn_exp_Ioi`, `ContinuousTimeNK.intervalIntegral_exp`, `ContinuousTimeNK.tvc_iff_forward` |
| Cochrane (20.8), p. 474; Online Appendix A1 §1.12, p. 580 | the forward integral `∫_t^∞ e^{−a(s−t)}z_s ds`, its closed form, ODE, bound and continuity (partly restated from the Chapter 5 project) | `ContinuousTimeNK.fwdInt`, `ContinuousTimeNK.fwdInt_eq`, `ContinuousTimeNK.fwdInt_hasDerivAt`, `ContinuousTimeNK.fwdInt_abs_le`, `ContinuousTimeNK.fwdInt_continuous` |
| Cochrane (20.8), p. 474 | the two-sided backward integral `∫_{−∞}^t e^{−b(t−s)}z_s ds`, as a time-reversed forward integral; its ODE, bound and continuity | `ContinuousTimeNK.bwdInfInt`, `ContinuousTimeNK.bwdInfInt_eq_fwdInt`, `ContinuousTimeNK.bwdInfInt_hasDerivAt`, `ContinuousTimeNK.bwdInfInt_abs_le`, `ContinuousTimeNK.bwdInfInt_continuous` |
| Cochrane p. 475 (solving piecewise; A1 §1.12) | variation of constants off a countable set of dates: constancy, `f' = af` and `f' = af + b` on intervals, half-lines and the whole line; a bounded solution of an unstable ODE is zero ("forward-explosive solutions are ruled out") | `ContinuousTimeNK.const_of_hasDerivAt_zero_off`, `ContinuousTimeNK.linear_ode_Icc`, `ContinuousTimeNK.affine_ode_Icc`, `ContinuousTimeNK.linear_ode_Ici`, `ContinuousTimeNK.unstable_bdd_zero`, `ContinuousTimeNK.linear_ode_univ` |
| Cochrane (20.8), p. 474 | the Green's-function family `greenPi C`: its ODE, a bound on the particular part, injectivity in `C`, forward stability; a solution of `(D − λ^f)(D + λ^b)π = −z` is forward-stable iff it is `greenPi C` for some `C` | `ContinuousTimeNK.greenPi`, `ContinuousTimeNK.greenPi_hasDerivAt`, `ContinuousTimeNK.greenPi_sub_abs_le`, `ContinuousTimeNK.greenPi_injective`, `ContinuousTimeNK.greenPi_forward_stable`, `ContinuousTimeNK.forward_stable_iff` |

## §20.2.2 Deflation jump: the Werning model, pp. 474–476, Figure 20.4 (WerningModel)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (20.5)–(20.6), p. 474 | a path: `dx/dt = σ(i − π − u_r)`, `dπ/dt = ρπ − κ(x + g)`, continuous on `[0, ∞)`, the ODEs off a countable set; "do not explode"; linearity and congruence | `WerningModel.IsPath`, `WerningModel.BddOnIci`, `WerningModel.IsPath.add`, `WerningModel.IsPath.sub`, `WerningModel.IsPath.congr` |
| Cochrane p. 475 ("we set to zero … `C_f e^{λ^f t}`") | the bounded unforced paths are `π_t = e^{−λ^b t}π_0`, `κx_t = λ^fπ_t` | `WerningModel.homog_bdd` |
| Cochrane pp. 474–475 | the experiment's step forcing; the functions `h` and `k`; the trap formulas for `π` and `y = λ^fπ − κ(x + g)` and their derivatives and end values | `WerningModel.trapStep`, `WerningModel.hh`, `WerningModel.kk`, `WerningModel.trapPi`, `WerningModel.trapY`, `WerningModel.hh_zero`, `WerningModel.kk_zero`, `WerningModel.hh_hasDerivAt`, `WerningModel.kk_hasDerivAt`, `WerningModel.trapPi_hasDerivAt`, `WerningModel.trapY_hasDerivAt`, `WerningModel.trapPi_zero`, `WerningModel.trapY_zero`, `WerningModel.trapPi_shift` |
| Cochrane pp. 475–476, Figure 20.4 | the family `(wX π_T, wPi π_T)` indexed by `π_T`; members differ by `(π_T − π_T')e^{λ^b(T−t)}`; continuity; each member is a bounded path of the experiment | `WerningModel.wPi`, `WerningModel.wX`, `WerningModel.wPi_T`, `WerningModel.wPi_shift`, `WerningModel.wX_shift`, `WerningModel.wPi_continuous`, `WerningModel.wX_continuous`, `WerningModel.wPath_isPath`, `WerningModel.bdd_of_cont_exp`, `WerningModel.wPath_bdd` |
| Cochrane pp. 474–475 | the bounded paths of the experiment are exactly the one-parameter family, with a unique constant `π_T` | `WerningModel.bdd_path_iff`, `WerningModel.bdd_path_existsUnique` |
| Cochrane p. 475 (E6: the jump conditions) | `x` and `π` are continuous at `T`; `π̇(T⁺) − π̇(T⁻) = κg`, `ẋ(T⁺) − ẋ(T⁻) = σu` | `WerningModel.trapBranch_hasDerivAt`, `WerningModel.trapBranchX_hasDerivAt`, `WerningModel.postBranch_hasDerivAt`, `WerningModel.jump_pi`, `WerningModel.jump_x` |
| Cochrane (20.8)–(20.10), pp. 474–475, whole time line, continuous forcing (E4, E6) | the model on `ℝ`; the forcing (20.9) with `r_t` the natural rate; the output gap (20.10); every member of (20.8)–(20.10) solves the model, and the forward-stable solutions are exactly these; the constant `C` gives a bijection with `ℝ` | `WerningModel.IsGlobalSol`, `WerningModel.zForce`, `WerningModel.bookX`, `WerningModel.eq20_8_solves`, `WerningModel.eq20_8_iff`, `WerningModel.family_equiv` |
| Cochrane (20.8)–(20.10), pp. 474–475, for the experiment (E6) | the Green's kernel; the absolutely continuous forcing; the step integrals; `dg/dt` read as the measure `g(δ_0 − δ_T)` with atoms; the constant `C` of the member indexed by `π_T`; the book's formulas hold for every member, the bounded paths are exactly the book's formulas, and `C` is pinned by `π_0` | `WerningModel.kern`, `WerningModel.zTrap`, `WerningModel.integral_exp_bwd`, `WerningModel.integral_exp_fwd`, `WerningModel.bwd_step_le`, `WerningModel.bwd_step_ge`, `WerningModel.fwd_step_le`, `WerningModel.fwd_step_ge`, `WerningModel.bookC`, `WerningModel.atomsB`, `WerningModel.atomsF`, `WerningModel.bookPi`, `WerningModel.bookKX`, `WerningModel.book_form`, `WerningModel.experiment_eq20_8`, `WerningModel.bookPi_C_unique` |
| Cochrane (20.7), p. 474 | under an active rule after `T` deviations explode, so the rule selects the chosen path as the unique bounded one | `WerningModel.active_rule_dev_zero`, `WerningModel.eq20_7_selects` |

## §§20.2.2–20.2.3 The deflation jump and the puzzling frictionless limit, pp. 475–478, Figure 20.5 (ZLBSelection)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 475; p. 481 | `h` is strictly increasing, `h(s) > 1`, with an exponential lower bound; `k` is positive and strictly increasing | `ZLBSelection.hh_strictMonoOn`, `ZLBSelection.one_lt_hh`, `ZLBSelection.hh_ge`, `ZLBSelection.kk_pos`, `ZLBSelection.kk_strictMono` |
| Cochrane p. 477 | the hyperbolic form of `h`; `sinh v/v` increasing; `h(s)` strictly increasing in `κ` for `ρ ≥ 0` | `ZLBSelection.sinhc_strictMonoOn`, `ZLBSelection.hh_eq_cosh`, `ZLBSelection.hh_strictMono_kappa` |
| Cochrane pp. 475–476 | the `π_T = 0` equilibrium: `π_t = −u(1 − h(T − t))`, `π_0 = −u(1 − h(T))`, and the survey's closed form | `ZLBSelection.pi0NK`, `ZLBSelection.nk_pi_eq`, `ZLBSelection.pi0NK_eq`, `ZLBSelection.pi0NK_book` |
| Cochrane p. 476 ("deflation steadily improves … no deflation spiral") | deflation throughout the trap, strictly improving; zero inflation and output from `T` on | `ZLBSelection.nk_pi_neg`, `ZLBSelection.nk_pi_strictMonoOn`, `ZLBSelection.nk_after` |
| Cochrane (20.10), p. 475; p. 476 ("a large output gap … expected output growth is strong") | the output gap during the trap is negative and strictly rising | `ZLBSelection.nk_x_eq`, `ZLBSelection.nk_x_neg`, `ZLBSelection.nk_x_strictMonoOn` |
| Cochrane p. 476 | with `g = 0`, `x_t < 0` iff `dπ/dt > ρπ_t` | `ZLBSelection.gap_neg_iff` |
| Cochrane p. 477 ("as we move … `T` to the right, the new-Keynesian deflation blows up") | a lower bound on the jump; `π_0 → −∞` as `T → ∞` | `ZLBSelection.pi0NK_le`, `ZLBSelection.pi0NK_tendsto_T` |
| Cochrane p. 477 ("deflation … gets worse without limit as prices become less sticky") | at every date of the trap `π_t → −∞` as `κ → ∞`, and `π_t` is strictly decreasing in `κ`; the same for `π_0`; `x_0 → −∞` | `ZLBSelection.half_le_weight`, `ZLBSelection.expLamb_tendsto_kappa`, `ZLBSelection.nk_tendsto_kappa`, `ZLBSelection.pi0NK_tendsto_kappa`, `ZLBSelection.nk_strictAnti_kappa`, `ZLBSelection.pi0NK_strictAnti_kappa`, `ZLBSelection.x0NK_tendsto_kappa` |
| Cochrane p. 477 ("(not shown) output gaps become larger as price stickiness is reduced") | `H = ∫_0^s h`; `x_t = σuH(T − t)`; `H` strictly increasing in `κ`; the output gap is strictly decreasing in `κ` at every date of the trap, in particular at date 0 | `ZLBSelection.HH`, `ZLBSelection.HH_zero`, `ZLBSelection.HH_hasDerivAt`, `ZLBSelection.nk_x_eq_HH`, `ZLBSelection.HH_strictMono_kappa`, `ZLBSelection.nk_x_strictAnti_kappa`, `ZLBSelection.x0NK_strictAnti_kappa` |
| Cochrane p. 477 | the frictionless model has the unique solution `x = −g`, `π = i − u_r` | `ZLBSelection.IsFrictionless`, `ZLBSelection.frictionless_iff` |
| Cochrane p. 478 (the limit is not the limit point) | at every `t ∈ (0, T)` the `π_T = 0` inflation does not converge to the frictionless value as `κ → ∞` | `ZLBSelection.nk_discontinuity` |
| Cochrane p. 476 ("the declining natural rate is met by a slight inflation rise") | the no-jump equilibrium: `π_0 = 0`, its closed form, `0 < π_t < −u` for `t > 0`, `0 < π_T < −u`, decay after `T` | `ZLBSelection.piTnj`, `ZLBSelection.nj_pi0`, `ZLBSelection.nj_formula`, `ZLBSelection.nj_key`, `ZLBSelection.nj_pos`, `ZLBSelection.nj_lt`, `ZLBSelection.piTnj_bounds`, `ZLBSelection.nj_tendsto_time` |
| Cochrane p. 478 ("smoothly rises to fill out a square function"; "ε price stickiness implies δ deviation") | the no-jump path converges to the frictionless square wave pointwise, and uniformly on compacts away from `0` and `T` | `ZLBSelection.expNeg_lam_tendsto`, `ZLBSelection.nj_dist_trap`, `ZLBSelection.nj_limit_trap`, `ZLBSelection.nj_uniform_trap`, `ZLBSelection.nj_uniform_after`, `ZLBSelection.nj_limit_after` |
| Cochrane p. 476 ("a fiscal theorist picks the equilibrium by the fiscal innovation at time 0"); §5.7 | debt valuation with the transversality condition; `π_0 − π_0' = −(r + λ^b)` times the difference in present values of surpluses; the `π_T = 0` equilibrium needs a fiscal contraction, unbounded as `κ → ∞` | `ZLBSelection.IsValuation`, `ZLBSelection.jump_eq_fiscal`, `ZLBSelection.fiscalContraction`, `ZLBSelection.nk_fiscal_contraction`, `ZLBSelection.fiscalContraction_tendsto` |

## §20.2.4 Forward guidance, pp. 478–480 (ForwardGuidance)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 479 ("inflation at time 0 is sensitive to its expectation at time T") | `π_t − π_t' = e^{λ^b(T−t)}(π_T − π_T')`; at date 0 the factor is `e^{λ^b T}`, an exact derivative | `ForwardGuidance.dpi_dpiT`, `ForwardGuidance.dpi0_dpiT`, `ForwardGuidance.hasDerivAt_pi0_piT` |
| Cochrane p. 479 (the glide path) | the no-jump equilibrium has `π_T = −π_0^{NK}e^{−λ^b T}`, and `0 < π_T < −u` although the deflation it removes is unbounded | `ForwardGuidance.piTnj_eq`, `ForwardGuidance.glide_path` |
| Cochrane p. 479 ("promises … further in the future have greater effects"; "as prices become less sticky … greater effect") | the sensitivity `e^{λ^b T}` is strictly increasing and unbounded in `T` and in `κ` | `ForwardGuidance.sensitivity_strictMono_T`, `ForwardGuidance.sensitivity_tendsto_T`, `ForwardGuidance.sensitivity_strictMono_kappa`, `ForwardGuidance.sensitivity_tendsto_kappa` |
| Cochrane p. 479 ("at the flexible-price limit point, forward guidance has no effect at all") | the frictionless model has no free constant | `ForwardGuidance.frictionless_unique` |
| Cochrane p. 479 (Woodford 2012, Werning 2012: delaying the rate rise) | the model depends on `i − u_r` only; with a positive post-trap natural rate `u₂` and lift-off at `L = T + τ`, the `π_L = 0` path solves the model, is bounded, vanishes after `L` and is unique; `π_0 = −u(1 − h(T)) + u₂(h(L) − h(T))`, equal to the standard value at `τ = 0`, strictly increasing and unbounded in `τ` | `ForwardGuidance.isPath_congr_forcing`, `ForwardGuidance.delayI`, `ForwardGuidance.delayU`, `ForwardGuidance.delayPi`, `ForwardGuidance.delayX`, `ForwardGuidance.delay_isPath`, `ForwardGuidance.delay_bdd`, `ForwardGuidance.delay_after`, `ForwardGuidance.delay_unique`, `ForwardGuidance.delay_pi0`, `ForwardGuidance.delay_zero`, `ForwardGuidance.delay_pi0_strictMono`, `ForwardGuidance.delay_pi0_tendsto` |

## §20.2.5 Magical multipliers and Bastiat banished, pp. 480–482, Figure 20.6 (Multipliers)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 480 | the IS curve (20.5) solved forward, `x_t = −∫_0^∞ σ(i − u_r − π) ds`, for any path with `x_T → 0` and along every bounded path of the experiment | `Multipliers.is_forward`, `Multipliers.trapStep_integrableOn`, `Multipliers.experiment_is_forward` |
| Cochrane pp. 480–481 | output in the standard (`π_T = 0`) and no-jump (`π_0 = 0`) equilibria with disturbance `g`; it is affine in `g`, and the multipliers are exact derivatives `∂x_t/∂g` | `Multipliers.xNK`, `Multipliers.piTnjg`, `Multipliers.xNJ`, `Multipliers.multNK`, `Multipliers.multNJ`, `Multipliers.nj_g_pi0`, `Multipliers.xNK_affine`, `Multipliers.xNJ_affine`, `Multipliers.hasDerivAt_xNK`, `Multipliers.hasDerivAt_xNJ` |
| Cochrane p. 481 ("multipliers increase as price stickiness is reduced … go to infinity") | the standard multiplier is positive, strictly increasing in `κ`, and tends to infinity as `κ → ∞` | `Multipliers.multNK_pos`, `Multipliers.multNK_strictMono_kappa`, `Multipliers.multNK_tendsto_kappa` |
| Cochrane p. 481 ("increase exponentially … as the length of the liquidity trap increases") | `m_0 = h(T) − 1`, strictly increasing in `T`, with an exponential lower bound, unbounded, and greater than one for long traps | `Multipliers.multNK0_eq`, `Multipliers.multNK0_strictMonoOn_T`, `Multipliers.multNK0_ge`, `Multipliers.multNK0_tendsto_T`, `Multipliers.multNK0_gt_one_eventually` |
| Cochrane p. 481 (E20) | "substantially greater than one" fails for short traps: `0 < m_0 < 1` for all small `T`; at `κ = σ = 1`, `ρ = 0.05`, `T = 1`, `0 < m_0 < 1` (about 0.53) | `Multipliers.multNK0_lt_one_short`, `Multipliers.e20_counterexample` |
| Cochrane p. 481 ("the multiplier is −1 at the limit point") | in the frictionless model `∂x_t/∂g = −1` during the trap | `Multipliers.frictionless_multiplier` |
| Cochrane p. 481 ("small, and clustered around the frictionless value −1") | the no-jump multiplier in closed form; `−1 < m_t < 0`; a distance bound; `m_t → −1` as `κ → ∞` or `T → ∞` | `Multipliers.multNJ_formula`, `Multipliers.multNJ_bounds`, `Multipliers.multNJ_dist`, `Multipliers.multNJ_tendsto_kappa`, `Multipliers.multNJ_tendsto_T` |
| Cochrane p. 481 ("spending … in the future is exponentially more effective") | spending on a window `[a, a + Δ)`: the unique `π_T = 0` path, its time-0 multiplier `h(a + Δ) − h(a)` in closed form, strictly increasing and unbounded in `a` | `Multipliers.gWindow`, `Multipliers.windowX`, `Multipliers.windowPi`, `Multipliers.window_isPath`, `Multipliers.window_after`, `Multipliers.window_bdd`, `Multipliers.window_unique`, `Multipliers.windowMult`, `Multipliers.window_x0`, `Multipliers.windowMult_eq`, `Multipliers.windowMult_strictMono`, `Multipliers.windowMult_tendsto` |

## §20.2.6 Literature and patches: Gabaix's model, pp. 482–483 (Gabaix)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (20.11)–(20.12), p. 482, at a peg | the model; its backward matrix `[[M, σ], [κM, M^fβ + σκ]]` and forcing; trace and determinant; the system form | `Gabaix.GabaixEq`, `Gabaix.gabaixMatrix`, `Gabaix.gabaixForcing`, `Gabaix.gabaix_tr_det`, `Gabaix.gabaixEq_iff_solves` |
| Cochrane pp. 482–483 (E8, exact boundary) | `1 − tr A + det A = (1 − M)(1 − βM^f) − σκ`; for `0 ≤ M, M^f ≤ 1`, `0 < β < 1`, `σκ ≥ 0`: Schur–Cohn, both roots inside the unit circle, and determinacy each hold iff `(1 − M)(1 − βM^f) > σκ` | `Gabaix.gabaix_charpoly_one`, `Gabaix.gabaix_schur_iff`, `Gabaix.gabaix_roots_iff`, `Gabaix.gabaix_determinate_iff` |
| Cochrane pp. 482–483 | the steady state; under the condition it is the unique bounded equilibrium; otherwise there are others | `Gabaix.gabaix_steady`, `Gabaix.gabaix_unique`, `Gabaix.gabaix_not_unique` |
| Cochrane p. 483 ("bounded away from rationality … from the frictionless price limit") | never determinate at `M = 1`; indeterminate for `κ ≥ 1/σ`; determinacy requires `M < 1 − σκ`, `σκ < 1 − βM^f` | `Gabaix.rational_IS_indeterminate`, `Gabaix.frictionless_limit_indeterminate`, `Gabaix.determinate_bounded_away` |
| Cochrane p. 482 ("eigenvalues must switch from greater to less than one") | on the boundary one is a root | `Gabaix.boundary_root_one` |
| Cochrane p. 483 (E8) | "`M` less than a half" is not necessary (`M = M^f = 3/5`, `σκ = 1/10`; `M = 0.9`, `M^f = 1/2`, `σκ = 0.05`), and "with `σκ` less than about a half" is not sufficient (`M = M^f = σκ = 2/5`) | `Gabaix.e8_half_not_necessary`, `Gabaix.e8_half_not_necessary'`, `Gabaix.e8_not_sufficient` |

## §20.3 Zero bound summary and implications: welfare, pp. 484–485 (ZLBWelfare)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 485 (Calvo pricing) | the stationary age weights `(1 − α)αʲ`, log relative prices, dispersion and the average squared distance from the reset price; the weights sum to one; first and second moments of the age | `ZLBWelfare.calvoW`, `ZLBWelfare.relPrice`, `ZLBWelfare.dispersion`, `ZLBWelfare.resetGap`, `ZLBWelfare.hasSum_calvoW`, `ZLBWelfare.hasSum_calvoW_mul`, `ZLBWelfare.hasSum_sq_mul_geometric`, `ZLBWelfare.hasSum_calvoW_sq` |
| Cochrane p. 485 ("relative prices are less distorted"; "firms are closer to their optimal prices") | the mean relative price is zero; exact dispersion `απ²/(1 − α)²`, the fixed point of Woodford's recursion; reset gap `α(1 + α)π²/(1 − α)²`; zero iff `π = 0`; both strictly increasing in `\|π\|` | `ZLBWelfare.relPrice_mean`, `ZLBWelfare.dispersion_eq`, `ZLBWelfare.resetGap_eq`, `ZLBWelfare.dispersion_fixed_point`, `ZLBWelfare.dispersion_eq_zero_iff`, `ZLBWelfare.relPrice_zero`, `ZLBWelfare.dispersion_lt_iff`, `ZLBWelfare.resetGap_lt_iff` |
| Cochrane p. 485 | the steady-state Phillips curve `x̄ = (1 − β)π/κ`; the steady-state loss `π² + λx̄²` is strictly increasing in `\|π\|` | `ZLBWelfare.ss_phillips_iff`, `ZLBWelfare.ssLoss`, `ZLBWelfare.ssLoss_lt_iff` |
| Cochrane (16.28), p. 379; p. 484 | at the bound the steady state is `Π_L = β` | `ZLBWelfare.zlb_steady_state` |
| Cochrane pp. 484–485 (E9) | "`Π_L` has greater welfare than `Π*`" holds iff `1 < βΠ*`, for dispersion and for the quadratic loss; it is worse iff `βΠ* < 1`; counterexample `β = 0.95`, `Π* = 1.02` | `ZLBWelfare.zlb_better_iff`, `ZLBWelfare.zlb_worse_iff`, `ZLBWelfare.zlb_welfare_better_iff`, `ZLBWelfare.e9_counterexample` |
| Cochrane p. 380 (the book's numbers); p. 485 | with `r = 1%` and a 2% target the zero-bound steady state is better; so is any `Π_L ∈ [1, Π*)` | `ZLBWelfare.book_calibration`, `ZLBWelfare.zlb_better_of_one_le` |

## Chapter 21 The Covid inflation, pp. 486–494 (Covid)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane pp. 486, 488 | the CPI rose 5.15%, a 7.8% annual rate; the arithmetic of Table 21.1; $5 trillion is nearly 30% of $17 trillion | `Covid.cpi_rise`, `Covid.table_21_1`, `Covid.debt_increase_nearly_30` |
| Cochrane pp. 487, 490 (frictionless valuation, one-period debt) | `P = B/S`; a helicopter drop with unchanged surpluses raises `P` in proportion; 30% more debt gives 30% higher prices | `Covid.priceLevel`, `Covid.helicopter_exact`, `Covid.helicopter_thirty` |
| Cochrane p. 488 (E10) | with a fraction `f` of the new debt backed, `P′/P = (1 + Δ)/(1 + fΔ)` and real debt rises by `1 + fΔ`; two-thirds backing of 30% gives `13/12` (8.33%) and exactly +20%; the printed pair is inconsistent | `Covid.priceRatio`, `Covid.partial_backing`, `Covid.partial_backing_example`, `Covid.e10_printed_pair_inconsistent` |
| Cochrane p. 488 (E10) | 10% is the first-order term `(1 − f)Δ`, with exact remainder `−f(1 − f)Δ²/(1 + fΔ)` | `Covid.hasDerivAt_priceRatio`, `Covid.priceRatio_remainder`, `Covid.first_order_example` |
| Cochrane p. 490 | more backing, less inflation; with only the new reserves unbacked the rise is `65/56` | `Covid.priceRatio_strictAnti`, `Covid.reserves_only_unbacked` |
| Cochrane p. 491 ("bad fiscal news can only affect unexpected inflation"), frictionless (5.10)–(5.12) | fiscal news leaves expected inflation unchanged and `π_{t+1} = i_t − ε_{t+1}` | `Covid.fiscal_news_only_unexpected` |
| Cochrane p. 492 ("if the Fed left the interest rate alone, inflation would eventually return") | at a peg with fiscal valuation, expected inflation returns to the peg | `Covid.peg_inflation_returns` |
| Cochrane p. 493 (Phillips-curve disinflation) | `x = (π − βE_tπ_{t+1})/κ`; a joint fall costs `(1 − β)d/κ`, a fall in `π` alone `d/κ`; the joint fall is less painful, painless as `β → 1`; the nominal rate falls at once | `Covid.pc_output`, `Covid.disinflation_joint`, `Covid.disinflation_alone`, `Covid.joint_less_painful`, `Covid.painless_limit`, `Covid.fisherian_rate_fall` |
| Cochrane p. 493 | at `r = 5%` the interest cost is 5% of GDP at 100% debt, four times that at 25% | `Covid.interest_cost_four_times`, `Covid.interest_cost_ratio` |
| Cochrane p. 493 (E11) | the 1981 bond windfall: `1.1584/1.039 − 1` lies in `(11.49%, 11.5%)`, not 12% | `Covid.windfall_real_return` |

## Links between the modules (Links)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (5.6), p. 119; §5.7.1, p. 165; p. 475 (restated from the Chapter 5 project) | with period length `h` (`β = 1 − ρh`, slopes `σh`, `κh`): `λ₁ = 1 + h·scaledRoot` exactly and the formula for `λ₂`; the scaled root is continuous, positive and equals `λ^b` at `h = 0` | `Links.scaledRoot`, `Links.lam1_scaled_eq`, `Links.lam2_scaled_eq`, `Links.scaledRoot_zero`, `Links.continuous_scaledRoot`, `Links.scaledRoot_pos` |
| Cochrane p. 467 → p. 475 | `(λ₁ − 1)/h → λ^b` and `(λ₂ − 1)/h → −λ^f`; the decay `λ₁^{−n}` over `n` periods of length `t/n` tends to `e^{−λ^b t}` | `Links.tendsto_lam1_scaled`, `Links.tendsto_lam2_scaled`, `Links.tendsto_peg_decay` |
| Cochrane p. 467 → pp. 474–475 | under perfect foresight every bounded peg equilibrium is `π_t − ī = λ₁^{−t}(π₀ − ī)`; with the same initial inflation the discrete equilibria converge to the continuous-time path `e^{−λ^b t}c`; the continuous-time family is uncountable | `Links.peg_pf_path`, `Links.peg_paths_converge`, `Links.werning_continuum` |
| Cochrane p. 469 → p. 476; p. 491 | the discrete impact coefficient per unit time tends to `r + λ^b`; as `κ → ∞` the coefficient `1 − ρ/λ₁` tends to `1` | `Links.tendsto_peg_impact`, `Links.fiscal_impact_frictionless` |
| Cochrane (20.7), p. 474, with p. 475, vs p. 472 | a peg at zero during the trap and `i = φπ`, `φ > 1`, afterwards: every bounded path is the `π_T = 0` member of the Werning family | `Links.werning_future_selection` |
| Cochrane (20.11)–(20.12), p. 482, vs (5.1)–(5.2) and p. 467 | at `M = M^f = 1` the Gabaix matrix and model are the peg ones; the condition fails and the roots straddle the unit circle | `Links.gabaix_rational_eq_peg`, `Links.gabaixEq_rational_iff`, `Links.gabaix_rational_straddle` |
| Cochrane (16.28), p. 379; p. 484 | `β` is a fixed point of the Chapter 16 map iff `φ(β) = 0`; a fixed point at the bound is `Π_L = β` | `Links.map46_fixed_beta_iff`, `Links.zlb_fixed_point_eq_beta` |
| Cochrane p. 472 and p. 484 | with natural rate `u = −log β` the zero-bound steady state of the (20.2) map is `π = log β`, the rule is at the bound there, and `e^{log β} = β = Π_L` | `Links.zlb_steady_log` |

## Restated Woodford block (GlobalDynamics)

These declarations are a verbatim copy of the module `GlobalDynamics` of the Woodford Chapter 2
project (`PriceLevelDetermination`), by way of its copy in the Chapter 16 project
(`NewKeynesianSelection`), namespace adapted. Their docstrings cite Woodford (2003), *Interest
and Prices*. `ZLBRule` uses the attraction and repulsion lemmas for the steady states of p. 472,
and `Links` uses the map `GlobalDynamics.map46`, which is Cochrane's (16.28).

| Book | Claim | Lean |
| --- | --- | --- |
| Woodford (2003) §4.1, pp. 123–127 (survey lemma L5); for Cochrane p. 472 | one-dimensional maps: monotone orbits, limits are fixed points, slope above one repels, below one attracts | `GlobalDynamics.orbit_monotone_of_le`, `GlobalDynamics.orbit_antitone_of_ge`, `GlobalDynamics.fixed_of_tendsto`, `GlobalDynamics.monotone_orbit_atTop_or_fixed`, `GlobalDynamics.antitone_orbit_atBot_or_fixed`, `GlobalDynamics.sign_near_of_deriv_pos`, `GlobalDynamics.repelling_of_one_lt_abs_deriv`, `GlobalDynamics.attracting_of_abs_deriv_lt_one` |
| Woodford (2003) (1.8), p. 67; (4.2), p. 124 | the opportunity cost of money; the discount factor; the Ricardian rule `T = αW − ΔM` and its transversality condition | `GlobalDynamics.oppCost`, `GlobalDynamics.oppCost_zero`, `GlobalDynamics.discount`, `GlobalDynamics.ricardian_step`, `GlobalDynamics.ricardian_discounted`, `GlobalDynamics.ricardian_tvc`, `GlobalDynamics.ricardian_tvc_fails_of_alpha_zero` |
| Woodford (2003) (4.3)–(4.6), pp. 124–125; for Cochrane (16.28), p. 379 | (4.5) from the Fisher equation; (4.6) in the separable case; its map and orbits; (4.4) and a continuum of perfect-foresight equilibria | `GlobalDynamics.eq45_iff_fisher`, `GlobalDynamics.IsPath45`, `GlobalDynamics.IsPath46`, `GlobalDynamics.fisher_path_iff_eq45`, `GlobalDynamics.isPath45_iff_isPath46_of_const`, `GlobalDynamics.map46`, `GlobalDynamics.orbit46`, `GlobalDynamics.orbit46_succ`, `GlobalDynamics.orbit46_isPath`, `GlobalDynamics.isPath46_eq_orbit`, `GlobalDynamics.bound44Term`, `GlobalDynamics.bound44_summable`, `GlobalDynamics.continuum_pf_equilibria` |
| Woodford (2003) pp. 124–127 | the target is a steady state; the Taylor coefficient is the slope of the map; the second steady state; self-fulfilling deflations; local indeterminacy at the deflationary steady state; local repulsion and uniqueness at the target | `GlobalDynamics.target_isFixed`, `GlobalDynamics.hasDerivAt_map46`, `GlobalDynamics.taylorCoeff_eq_slope`, `GlobalDynamics.second_steady_state`, `GlobalDynamics.map46_step_down`, `GlobalDynamics.self_fulfilling_deflation46`, `GlobalDynamics.deflation46_strictAnti`, `GlobalDynamics.deflation46_eventually_deflation`, `GlobalDynamics.deflationary_steady_state_indeterminate`, `GlobalDynamics.target_locally_repelling`, `GlobalDynamics.target_locally_unique` |
| Woodford (2003) p. 127, Woodford survey error E6 | "inflation above target rises without bound" needs no steady state above the target; counterexample | `GlobalDynamics.inflation_unbounded46`, `GlobalDynamics.inflation_unbounded_iff`, `GlobalDynamics.phiCE`, `GlobalDynamics.e6_counterexample` |
| Woodford (2003) pp. 127–128, fn. 61 | real-balance effects: self-fulfilling deflations of (4.5) under monotone or "not too strongly increasing" `λ`, with (4.4); a restriction is needed | `GlobalDynamics.ratio_strictMonoOn`, `GlobalDynamics.steady_state45_iff`, `GlobalDynamics.isPath45_unique`, `GlobalDynamics.step45_down`, `GlobalDynamics.self_fulfilling_deflation45`, `GlobalDynamics.deflation45_exists`, `GlobalDynamics.deflation45_bound44`, `GlobalDynamics.step45_down_gen`, `GlobalDynamics.self_fulfilling_deflation45_gen`, `GlobalDynamics.deflation45_exists_gen`, `GlobalDynamics.antitone_lam_gives_gen`, `GlobalDynamics.phiCE45`, `GlobalDynamics.deflation45_counterexample`, `GlobalDynamics.bound44_summable_path`, `GlobalDynamics.deflation45_bound44_gen` |

## Shared tools

| Book | Claim | Lean |
| --- | --- | --- |
| Chapter 20 throughout (discrete time) | the expectation axioms, adaptedness, AR(1) processes, perfect foresight; bounded processes and vectors | `ExpectationSystem`, `ExpectationSystem.Adapted`, `ExpectationSystem.AdaptedVec`, `ExpectationSystem.IsAR1`, `perfectForesight`, `BoundedProc`, `BoundedVec` |
| p. 467 (`ZLBPeg`), pp. 482–483 (`Gabaix`) | the backward system `z_t = AE_tz_{t+1} + w`, determinacy and its Schur–Cohn characterisation; the discriminant `discQ`, trace and determinant | `ExpectationSystem.Solves`, `ExpectationSystem.Determinate`, `ExpectationSystem.determinate_iff`, `ExpectationSystem.system_not_unique`, `SchurStable`, `schurStable_iff_roots`, `discQ`, `tr2`, `det2` |
| p. 467 (`ZLBPeg`); p. 472 (`FutureSelection`) | the sunspot family; the scalar equation and its forward solution | `ForwardSolution.sunspotFamily`, `ForwardSolution.sunspotFamily_succ`, `ForwardSolution.sunspotFamily_solves`, `ForwardSolution.sunspotFamily_adapted`, `ForwardSolution.sunspotFamily_bounded`, `ForwardSolution.Solves`, `ForwardSolution.E_of_known`, `ForwardSolution.scalarSol`, `ForwardSolution.scalar_existsUnique`, `ForwardSolution.exists_bounded_of_one_lt` |
| p. 467 (`ZLBPeg.coin_sunspot_equilibrium`) | finite event trees and the coin-flip tree with its shock and AR(1) | `ExpectationsFiniteTree.FiniteTree.toExpectationSystem`, `ExpectationsFiniteTree.coinSystem`, `ExpectationsFiniteTree.coinShock`, `ExpectationsFiniteTree.coinAR1`, `ExpectationsFiniteTree.coinAR1_isAR1`, `ExpectationsFiniteTree.coinAR1_nondegenerate` |
| shared core, not used by Chapters 20–21 | pull-out, forward series and the vector forward solution, carried for the other Cochrane projects | `ExpectationSystem.PullOut`, `ExpectationSystem.forwardSeries`, `ForwardSolution.existsUnique_bounded` |
