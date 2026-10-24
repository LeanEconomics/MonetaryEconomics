# New-Keynesian models and equilibrium selection in Lean

This is the `Cochrane/NewKeynesianSelection/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Chapter 16, "The new-Keynesian models, equilibrium selection"
(pp. 363–396), together with the precise claims of Chapter 12, "Interest-rate targets"
(pp. 324–328), and Online Appendix A3, §§3.1.1–3.1.2 (pp. 613–616). The linear models are stated
for an arbitrary expectation operator, so every result covers perfect foresight and genuine
uncertainty: processes are `ℕ → Ω → ℝ` and every equation holds state by state. The nonlinear
model of §16.8 and the selection patches of §16.10 are perfect-foresight paths, as in the book's
Figure 16.2. The central objects are the new-Keynesian equilibrium (an adapted inflation process
solving `E_tπ_{t+1} = φπ_t + u_t`, (16.4)) and its selection: "determinate" means exactly one
bounded equilibrium for every bounded adapted disturbance. Against it stands the fiscal-theory
equilibrium of the same equations, in which unexpected inflation is set by the fiscal shock and
no boundedness is imposed. The library contains **619 theorems**, including the shared core; 511
of them are in the thirteen chapter modules, 95 of these in verbatim copies of Woodford Chapter 2
results (`GlobalDynamics` and the `WoodfordMuBar` and `SGU` blocks of `SelectionPatches`).

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises. Survey codes E1–E6 refer to the
survey of Chapters 11–19; NI-1 to NI-6 are its non-identification theorems.

Headline results, in the namespace `Cochrane.NewKeynesianSelection`:
* **The simplest model and determinacy.** Eliminating `i` from (16.1)–(16.2) gives (16.4), and
  under passive fiscal policy (16.3) is inert; with an exogenous fiscal shock the equations are
  exactly the fiscal-theory rule model of §2.6 (`SimplestModel.nk_iff`,
  `SimplestModel.nk_passive_iff`, `SimplestModel.nk_with_163_iff_ruleModel`). The equilibria are
  in bijection with the pairs `(π_0, δ)` of initial inflation and sunspot (16.5)
  (`SimplestModel.equilibria_bijOn`). For `|φ| < 1` they are bounded and uncountable, with
  genuinely random sunspots on the coin-flip tree; for `|φ| > 1` all but the forward solution
  (16.6) explode; (16.4) is determinate iff `|φ| > 1` (`SimplestModel.indeterminate_of_abs_lt_one`,
  `SimplestModel.coin_sunspot`, `SimplestModel.explodes_of_ne_fwdSol`,
  `SimplestModel.fwdSol_existsUnique`, `SimplestModel.determinate_iff`). The AR(1) results
  (16.7)–(16.11) and Figure 16.1 are exact (`SimplestModel.ar1_solution`,
  `SimplestModel.fig161_values`). The Wicksellian rule (16.8) is corrected: the coefficient is
  `φ_p`, not `φ`, and the price level is determinate iff `φ_p > 0` or `φ_p < −2`
  (`SimplestModel.wicksell_apply`, `SimplestModel.wicksell_determinate_iff`,
  `SimplestModel.printed_wicksell_false`; E4). The Chapter 12 claims are proved in the
  fiscal-theory model: a peg is stable, determinate and quiet; a peg at zero gives `π = −r`; and
  with `i = φπ`, `φ > 1` is determinate but unstable (`FTPLSimple.peg_stable_determinate`,
  `FTPLSimple.zero_peg_deflation`, `FTPLSimple.rule_determinate_unstable`).
* **King's form.** The translation (16.13) between targets and disturbances is a bijection of
  bounded adapted processes for `|φ| > 1` (`KingForm.translation_bijOn`). Under (16.14) the only
  bounded equilibrium is `π = π*`, for any disturbance process, so the bank can attain any bounded
  inflation path; the rate sets expected inflation and selection sets unexpected inflation
  (`KingForm.eq_target_of_bounded`, `KingForm.any_target_attainable`,
  `KingForm.expected_set_by_rate`, `KingForm.unexpected_set_by_selection`). The fiscal theory
  gives the same inflation with no `φ` (`KingForm.ftpl_same_inflation`).
* **Hyperinflations and the transversality condition.** Under the passive surplus rule real debt
  is constant, and every positive price path, however explosive, is a full perfect-foresight
  equilibrium with the transversality condition and (16.26) (`Hyperinflation.any_price_path_eqm`).
  The path `π_t = φᵗπ_0` obeys the exact rule `1 + i_t = (1 + r)Π_t^φ`, explodes, and is still an
  equilibrium (`Hyperinflation.hyperinflation_satisfies_tvc`); under uncertainty real debt is a
  martingale and the transversality condition holds for every price process
  (`Hyperinflation.stoch_tvc`). The fiscal theory rules out real explosions instead:
  `P_0 = B_{−1}/PV` (`Hyperinflation.ftpl_tvc_iff`, `Hyperinflation.ftpl_price_level_iff`).
* **Non-identification and learnability.** NI-1: every bounded adapted inflation process is the
  selected equilibrium for every `|φ| > 1`, so the set of `φ` consistent with any data is all of
  `1 < |φ|`; neither `φ` nor `u` is identified, and the law of the observables does not involve
  `φ` (`Identification.reverse_selected`, `Identification.nk_fiber_eq`,
  `Identification.phi_not_identified`, `Identification.law_obs_eq`). NI-2 and NI-3: `φ` enters
  only through `u/(φ − η)`, and OLS of `i` on `π` gives exactly `η` on every sample, with any
  instrument (`Identification.ni2_same_iff`, `Identification.ni3_ols`, `Identification.ni3_iv`).
  NI-4: in King's form the bounded equilibrium set does not depend on `φ`
  (`Identification.king_eq_set_indep`). Identified is the same as learnable, so `φ` is not
  learnable while the fiscal-theory `θ` is, for every `θ`
  (`Identification.identified_iff_learnable`, `Identification.phi_not_learnable`,
  `Identification.ftpl_theta_learnable`).
* **Observational equivalence and E6.** NI-5: the selected AR(1) equilibrium is the fiscal-theory
  equilibrium with `θ = η` and fiscal shock `ε_i/(φ − η)`, with identical impulse responses, and
  the observable sets of the two models coincide in both directions
  (`ObservationalEquivalence.nk_is_ftpl`, `ObservationalEquivalence.nk_irf_eq_ftpl_irf`,
  `ObservationalEquivalence.nkObsSet_eq_ftplObsSet`,
  `ObservationalEquivalence.selectedObsSet_eq_boundedFtplObsSet`). NI-6: in the unified model
  (16.20)–(16.22) every regime has the observable system (16.23)–(16.24), so `γ` is as
  unidentified as `φ` (`ObservationalEquivalence.eqObs_eq`,
  `ObservationalEquivalence.regimes_observationally_equivalent`). With (16.21)–(16.22) as printed
  `γ` drops out of the debt gap, and **fiscal policy is passive iff `γ = α`**, not for every
  `γ > 0`; the survey's `0 < γ < 2` is also wrong (`ObservationalEquivalence.passive_iff`,
  `ObservationalEquivalence.e6_printed_fails`; E6). In `Links`, this passivity is shown to be
  strictly weaker than Woodford's local Ricardianness (`Links.passive_of_ricardian`,
  `Links.passive_not_ricardian`).
* **Responses.** The model is Fisherian: the real rate is zero, and on a monetary shock inflation
  and the rate fall on impact although `u_1 > 0` (`Responses.real_rate_zero`,
  `Responses.impact_signs`). The super-Fisherian response gives `π = i = 1` from date 1, and the
  open-mouth operation moves inflation with `i ≡ 0` (`Responses.super_fisherian`,
  `Responses.open_mouth`; E5 is a typo only). The rule `i = φE_tπ_{t+1}` does have solutions:
  for `φ ≠ 1` every equilibrium has `E_tπ_{t+1} = i = 0` (`Responses.ruleExp_has_solution`,
  `Responses.ruleExp_trivial`). Without the passive fiscal contraction a monetary shock has no
  non-explosive equilibrium (`Responses.no_eq_without_fiscal`).
* **The lower bound.** (16.25) linearises to (16.1) exactly, as a Gateaux derivative at any
  steady state in every bounded direction, for any expectation system
  (`LowerBound.gateaux_log_bondPricing`). With `Φ′(Π*) > 1`, `Π*` is the unique locally bounded
  equilibrium, yet every path of Figure 16.2 is an equilibrium
  (`LowerBound.target_unique_locally_bounded`, `LowerBound.continuum_of_equilibria`). The second
  steady state is corrected (E2): the bound is `Π_{t+1} ≥ β`; `Π_L` exists for continuous
  `Φ ≥ β`, with only `Φ′(Π_L) ≤ 1` (`LowerBound.lower_steady_state`); a tangency
  counterexample has `Φ′(Π_L) = 1` and a discontinuous one has no `Π_L`
  (`LowerBound.e2_tangency_counterexample`,
  `LowerBound.e2_discontinuous_counterexample`). Deflations trundle down to `Π_L`, and the
  2%/1% example reaches `i = 0` in finite time (`LowerBound.deflation_tendsto_lower`,
  `LowerBound.example_two_one`).
* **Selection patches.** MSV selects `−u/(φ − η)` among linear solutions, even for `|φ| < 1`,
  but not among nonlinear ones (`SelectionPatches.msv_iff`,
  `SelectionPatches.msv_nonlinear_counterexample`). Stopping an inflation does not rule it out,
  while the Atkeson–Chari–Kehoe overlap prunes inflations but not deflations
  (`SelectionPatches.stop_not_rule_out`, `SelectionPatches.ack_prunes_inflation`,
  `SelectionPatches.ack_keeps_deflation`). The Benhabib–Schmitt-Grohé–Uribe surplus rule and
  Woodford's `μ̄` rule remove the deflation trap and keep the target
  (`SelectionPatches.bsgu_no_equilibrium_to_lower`, `SelectionPatches.mubar_deflation_violates`,
  `SelectionPatches.mubar_target_tvc_iff`), and so does Bassetto's rule
  (`SelectionPatches.bassetto_no_equilibrium`). V-shaped and discontinuous rules select `Π*`; a
  rule tangent to the 45° line does not (`SelectionPatches.v_rule_unique_bounded`,
  `SelectionPatches.tangent_rule_converges`). (16.32) is Woodford's (4.5), so the restated
  Schmitt-Grohé–Uribe results apply (`SelectionPatches.eq1632_iff_path45`,
  `SelectionPatches.SGU.sgu_unique_pf_equilibrium`). Under a bounded continuous rule a
  finite-time explosion needs `u_c ∘ L` to be singular on the range of rates, and an explicit
  singular model produces one (`SelectionPatches.successor_exists_of_bounded_rule`,
  `SelectionPatches.bounded_rule_explosion`). Sims' 1994 penny breaks the transversality condition
  only for a fast enough approach to the zero bound; a slow convergence is a counterexample
  (`SelectionPatches.sims_tvc_violated`, `SelectionPatches.sims_slow_counterexample`).
* **Sims' tiny fiscal theory (E1).** Debt explodes as printed, but the transversality condition
  fails for every `π₀ ≠ 0` **iff `φ ≥ R`**; for `1 < φ < R` policy stays passive
  (`SimsTinyFiscal.debt_explodes`, `SimsTinyFiscal.e1_tvc_violated_iff`,
  `SimsTinyFiscal.e1_counterexample`). Stationary debt needs `R − 1 < γ < R + 1`
  (`SimsTinyFiscal.stationary_iff`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections are the confirmed errors of the chapter survey:
* Sims' patch, p. 396: the transversality condition fails for every `π₀ ≠ 0` iff `φ ≥ R`, not
  for every `φ > 1`; and "`γ > R − 1`" does not make debt stationary (E1);
* the lower bound, p. 379: the bound is weak, `Π_L` needs continuity, and only `Φ′(Π_L) ≤ 1`
  follows (E2);
* the Wicksellian price level, p. 365: `φ_p` for the printed `φ`, and determinacy also for
  `φ_p < −2` (E4);
* the open-mouth example, p. 375: typographical only (E5);
* the passive-fiscal regime, p. 373: passive iff `γ = α`, neither "`γ > 0`" nor the survey's
  "`0 < γ < 2`" (E6).

In addition, the formalisation makes precise the convergence claim for `|φ| < 1` (p. 364), the
"no solution" of the rule `i = φE_tπ_{t+1}` (p. 376), the MSV claim (p. 385), the bounded-rule
explosion of (16.32) (p. 393), Sims' 1994 argument (p. 394), the `θ = φ` identification
(p. 382), the `θ < 1` restriction (p. 394) and the hidden initial condition of the active-fiscal
regime (p. 373).

Not formalised:
* the verbal and empirical parts of the chapter: why to rule out inflation that runs up and
  stays, central-bank communication and history, the Smets–Wouters and Clarida–Galí–Gertler
  estimates (p. 381), Giannoni–Woodford's "some other state variable must jump" (p. 382), and the
  claim that removing the bound would allow global instability (p. 380), covered only through
  the Bassetto results;
* the claim that in richer models `φ > 1` is neither necessary nor sufficient for the explosive
  eigenvalue (p. 369, Chapter 12 claim P8), and Friedman's adaptive-expectations spiral (P1):
  both need a sticky-price model and belong to the `KeynesianStickyPrices` project;
* the e-stability (Evans–Honkapohja) link of §16.10.7; the chapter's claims there about
  identification and learnability are covered;
* the household problems behind (16.25) and (16.31): both are imposed as equilibrium conditions.
  The linearisation of (16.25) is a Gateaux derivative only, since `E_t` is an abstract linear
  map with no topology;
* a money market in the Atkeson–Chari–Kehoe regime: the money-growth rule enters through
  constant velocity as `Π_{t+1} = μ` (`SelectionPatches.quantity_theory_growth`);
* stochastic versions of the nonlinear results of §16.8 and §16.10, apart from the bond-pricing
  equation, its linearisation and the passive-fiscal results of §16.3.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](NewKeynesianSelection/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (shared core, restated from the earlier projects) |
| [Expectations](NewKeynesianSelection/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; adapted and AR(1) processes; forward series; the pull-out property (shared core) |
| [ExpectationsFiniteTree](NewKeynesianSelection/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; the coin-flip tree and its shock (shared core) |
| [ForwardSolution](NewKeynesianSelection/ForwardSolution.lean) | 44 | The forward solution of `z_t = aE_tz_{t+1} + u_t` and the sunspot family (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [Innovation](NewKeynesianSelection/Innovation.lean) | 33 | The innovation `ΔE_{t+1}` (algebra restated from the Chapter 2 project); the unique expected/unexpected split; shocks; AR(1) innovations |
| [FTPLSimple](NewKeynesianSelection/FTPLSimple.lean) | 35 | The simple fiscal-theory model (2.16)–(2.25), restated from the Chapter 2 project; the Chapter 12 claims P2–P6 |
| [SimplestModel](NewKeynesianSelection/SimplestModel.lean) | 42 | §16.1: (16.1)–(16.11), the sunspot family, determinacy iff `\|φ\| > 1`, Figure 16.1, the Wicksellian rule (16.8) corrected |
| [KingForm](NewKeynesianSelection/KingForm.lean) | 18 | §16.2: King's form (16.12)–(16.14) and its translation bijection; any target attainable; the fiscal-theory comparison |
| [Hyperinflation](NewKeynesianSelection/Hyperinflation.lean) | 29 | §§16.3–16.4: the fiscal block of §16.8, nominal explosions satisfy the transversality condition, the fiscal theory rules out real ones; stability and `φ < −1` |
| [Identification](NewKeynesianSelection/Identification.lean) | 55 | §16.5, §16.9, §16.10.7: NI-1 to NI-4, finite-sample OLS and IV identities, identification patches, identified iff learnable |
| [ObservationalEquivalence](NewKeynesianSelection/ObservationalEquivalence.lean) | 43 | §16.6: NI-5 and the two-way NK/FTPL translation; the unified model (16.20)–(16.24), E6 corrected, NI-6 |
| [Responses](NewKeynesianSelection/Responses.lean) | 25 | §16.7: alternative paths, Fisherian, super-Fisherian and open-mouth responses, the rule `i = φE_tπ_{t+1}`, the fiscal requirement |
| [GlobalDynamics](NewKeynesianSelection/GlobalDynamics.lean) | 49 | One-dimensional dynamics, (4.5)–(4.6), self-fulfilling deflations (verbatim from the Woodford Chapter 2 project) |
| [LowerBound](NewKeynesianSelection/LowerBound.lean) | 42 | §16.8: (16.25)–(16.30), exact linearisation, `Π_L` with E2 corrected, the full equilibrium and its continuum, the 2%/1% example |
| [SelectionPatches](NewKeynesianSelection/SelectionPatches.lean) | 99 | §§16.10.1–16.10.6 and A3: MSV, ACK, BSGU, `μ̄`, Bassetto, V-shaped and tangent rules, (16.31)–(16.32), Sims 1994, helicopter money and OMOs; 46 theorems in the restated Woodford blocks `WoodfordMuBar` and `SGU` |
| [SimsTinyFiscal](NewKeynesianSelection/SimsTinyFiscal.lean) | 16 | §16.10.8: (16.33)–(16.34), the closed form, E1 corrected, stationarity |
| [Links](NewKeynesianSelection/Links.lean) | 25 | Equivalences between the definitions of different modules; links to Woodford's (1.36), Prop. 2.3, (4.5) and Prop. 4.11 |

## Modelling conventions

* **Expectations.** Random variables are `Ω → ℝ`, processes `ℕ → Ω → ℝ`, and every linear model
  equation holds as an equality of functions, for an arbitrary `ExpectationSystem`. A process is
  adapted when `E_tx_t = x_t` (`ExpectationSystem.Adapted`). Perfect foresight
  (`perfectForesight`) and every finite event tree
  (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) are instances; the coin-flip tree
  (`ExpectationsFiniteTree.coinSystem`) makes the sunspot, response and E6 examples genuinely
  random. Pull-out (`ExpectationSystem.PullOut`) is a hypothesis only where a known factor is
  taken out of an expectation: `Innovation.innov_mul_known` and the stochastic §16.3 results
  (`Hyperinflation.stoch_tvc`, `Links.stoch_tvc_obs`).
* **Innovations and shocks.** `ΔE_{t+1}x = E_{t+1}x − E_tx` (`Innovation.innov`). A shock is known
  at `t + 1` with `E_tε_{t+1} = 0` (`Innovation.IsShock`); its date-0 value is irrelevant, and an
  adapted process with unforecastable increments is a shock (`Innovation.adapted_isShock_iff`).
* **New-Keynesian equilibrium and selection.** An equilibrium of (16.4) is an adapted inflation
  process satisfying (16.4) at every date (`SimplestModel.Eq164`). The new-Keynesian selection is
  the locally bounded equilibrium, a bounded process (`BoundedProc`), and the model is
  determinate when there is exactly one for every bounded adapted disturbance
  (`SimplestModel.determinate_iff`, `Identification.Selected`).
* **Fiscal-theory equilibrium.** An adapted inflation process satisfying the Fisher equation and
  `ΔE_{t+1}π_{t+1} = −ε_{Σs,t+1}` at every date, given `π_0` (`FTPLSimple.PegModel`,
  `FTPLSimple.RuleModel`). No boundedness is imposed: the price level is set by the valuation
  equation, not by ruling out explosive paths.
* **Observational equivalence is pathwise.** Observables are equal as functions `ℕ → Ω → ℝ`,
  which implies equality of their laws under every probability model
  (`Identification.law_obs_eq`). Regression results are finite-sample algebraic identities.
* **The nonlinear model.** §16.8 and §16.10 work with gross inflation `Π_t = P_t/P_{t−1}`,
  `β = 1/(1 + r)` and the rule `1 + i_t = (1 + r)Φ(Π_t)`, under perfect foresight. Nominal debt is
  indexed by its redemption date, `D_t = B_{t−1}`; the transversality condition is an explicit
  limit, and the valuation equation (16.26) a genuine `HasSum`. The zero bound `i_t ≥ 0` is part
  of the equilibrium (`LowerBound.IsEquilibrium`).
* **Several definitions of one object.** The chapter was formalised in three concurrent chains.
  Where book objects have two definitions differing by adaptedness or argument order
  (`Identification.NKEq` and `SimplestModel.NKModel`, `Identification.Selected` and
  `SimplestModel.fwdSol`, `Identification.FTPLEq` and `FTPLSimple.RuleModel`,
  `Identification.KingEq` and `KingForm.KingRule`, the two transversality conditions
  `Hyperinflation.TVC` and `ObservationalEquivalence.TVC`), both are kept and proved equivalent in
  `Links`.
* **Explicit hypotheses.** Hypotheses the book leaves implicit are stated in each theorem:
  `φ ≠ η` for the AR(1) results, `r > 0` for the passive rule, continuity of `Φ` for `Π_L`, and
  `0 < ρ < 1`, `0 < α < 2` with `v_0 = v*_0` for the unified model.

## Relation to the Woodford projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects, so the project builds on its own. Nothing is imported from
those projects. Three blocks are verbatim copies of the Woodford Chapter 2 project
(`PriceLevelDetermination`), with only the namespace changed and docstrings prefixed "Restated
from the Woodford Chapter 2 project":
* `GlobalDynamics`, from its module of the same name: one-dimensional dynamics, the second steady
  state, self-fulfilling deflations of (4.5)–(4.6) (`GlobalDynamics.second_steady_state`,
  `GlobalDynamics.self_fulfilling_deflation45`);
* `SelectionPatches.WoodfordMuBar`, from `MoneyTargetingDynamics`: liabilities growing at `μ̄`
  violate the transversality condition along deflations
  (`SelectionPatches.WoodfordMuBar.fig24_deflations_violate_tvc`);
* `SelectionPatches.SGU`, the whole of `SchmittGroheUribe`, including the unique-equilibrium
  result under Woodford's error-E5 hypothesis and its counterexample
  (`SelectionPatches.SGU.sgu_unique_pf_equilibrium`, `SelectionPatches.SGU.e5_counterexample`).

Cochrane's (16.32) is Woodford's (4.5) (`SelectionPatches.eq1632_iff_path45`), so these results
apply to Cochrane's model directly. `Links` restates two further Woodford statements and derives
them from Cochrane's results:
* Woodford's reduced equation (1.36) and Proposition 2.3, from the Chapter 2 project: (1.36) is
  (16.4) for the price gap, the Wicksellian model (16.8) is its case `r̂ = π* = 0`, and
  Proposition 2.3 and Woodford's "determinate iff `φ_p > 0`" follow from the forward solution and
  the corrected (16.8) (`Links.woodfordReduced_iff_eq164`, `Links.wicksellModel_iff_woodford`,
  `Links.woodford_prop_2_3_linear`, `Links.woodford_determinate_iff`);
* the tax-rule debt dynamics (4.5) and the Ricardian condition of Proposition 4.11, from the
  Chapter 4 project (`NeoWicksellianFramework`): with `γ = α` the unified model's debt is (4.5)
  with `τ_b = α`, passivity holds iff `γ = α`, and the locally Ricardian condition is
  `τ_b > 1 − β` (`Links.fiscalBlock_debt45`, `Links.e6_passive_iff_woodford45`,
  `Links.woodford_ricardian_iff`). A locally Ricardian rule is passive, but not conversely: with
  `ρ = 1/2` and `γ = α = 1/4` policy is passive while `|ρ⁻¹(1 − α)| = 3/2`
  (`Links.passive_of_ricardian`, `Links.passive_not_ricardian`).

## Relation to other Cochrane projects

* **Chapter 2 (`IntertemporalModel`).** The §§2.5–2.6 part of `FTPLSimple` (the fiscal shock
  (2.17), the peg (2.19) and the rule model (2.20)–(2.25)) is a copy of that project's
  `LinearFTMP`, and the algebra of `Innovation.innov` is restated from its `ExpectationTools`;
  the docstrings say "Restated from the Chapter 2 project". The Chapter 12 claims and the
  `passiveShock_isShock` lemma are new here.
* **Chapter 22 (`ObservationalEquivalence`).** That project owns the general observational
  equivalence and non-identification theorems for the starred form of the policy rules,
  (16.20)–(16.24) with Chapter 22's (22.1)–(22.11) (its modules `StarredModel`, `Equivalence`,
  `NonIdentification`). This project proves the Chapter 16 instances (NI-1 to NI-6) in the
  simplest model. The two agree on E6: under the printed reading of (16.21), in which the actual
  surplus drives target debt, passivity holds iff `γ = α` (here
  `ObservationalEquivalence.passive_iff`; there `LeeperRegions.literal_tvc_iff`). That project
  takes the target-surplus reading as its main one, under which the range is `0 < γ < 2`
  (`Equivalence.unique_iff`).
* **Chapter 5 (`StickyPriceFiscal`).** The rule on actual debt `s_{t+1} = γv_t + u_{s,t+1}` of
  (5.36)–(5.37), whose passivity range `0 < γ < 2` the survey transferred to (16.20), is
  formalised there.

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
