# Observational equivalence in Lean

This is the `Cochrane/ObservationalEquivalence/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Chapter 22, "Observational equivalence" (pp. 495–510), together with the
precise claims of Chapters 23–24 (pp. 512–523) and of Online Appendix Chapter 2, "How not to test
fiscal theory" (pp. 593–611). The linear models are stated for an arbitrary expectation operator,
so every result covers perfect foresight and genuine uncertainty: processes are `ℕ → Ω → ℝ` and
every equation holds state by state. The central object is the frictionless model
`i_t = E_tπ_{t+1}`, `ρv_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` (22.2), closed by monetary and
fiscal rules written around a target path, the "starred" form (16.20)–(16.24), (22.1),
(22.7)–(22.11). Its equilibria are judged by the book's criterion: adapted, bounded inflation and
the transversality condition for debt. "Unique" means that the target is the only such
equilibrium. The library contains **484 theorems**, including the shared core; 376 of them are in
the fifteen chapter modules.

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises. Survey codes E12–E19 refer to the
survey of Chapters 20–25 (`notes/survey_cochrane_ch20-25.md`), and E6 to the survey of Chapters
11–19. OE-1, OE-2, NI-1 to NI-3, LR and RG are that survey's names for the chapter's theorems.

Headline results, in the namespace `Cochrane.ObservationalEquivalence`:
* **Valuation in all regimes.** Given the Fisher equation and the flow condition, the
  transversality condition holds iff the valuation equation `v_t = E_t∑ρʲs̃_{t+1+j}` does
  (`Valuation.tvc_iff_valuation`, `Valuation.valuation_E_exPost`), and unexpected inflation is
  minus the news about the present value of surpluses (`Valuation.unexpected_inflation_news`). No
  policy rule is used, so every admissible equilibrium of every regime, active money included,
  satisfies the valuation equation (`StarredModel.valuation_all_regimes`, p. 497).
* **The starred model and OE-1.** The target is an equilibrium for every `(φ, γ)`
  (`StarredModel.starred_eqm`). Under the transversality criterion it is the unique admissible
  equilibrium **iff `|φ| > 1` or `γ ≤ 0` or `γ ≥ 2`** (`Equivalence.unique_iff`,
  `Equivalence.determinate_iff`); otherwise there is a continuum, indexed by the date-0 jump even
  under perfect foresight, plus genuinely random sunspot equilibria
  (`Equivalence.continuum_double_passive`, `Equivalence.sunspot_eqm`,
  `Equivalence.coin_sunspot_eqm`). This corrects the printed labels "`φ > 1`, `γ > 0`" and
  "`φ < 1`, `γ = 0`" (E12): `φ = −2` is determinate and `γ = 3` is active
  (`Equivalence.printed_phi_lt_one_determinate`, `Equivalence.printed_gamma_pos_determinate`).
  Under the bounded-debt criterion the target is unique iff `|φ| > 1` or `|1 − γ| > ρ`, so the
  passive range is `1 − ρ ≤ γ ≤ 1 + ρ`, boundary included (`LeeperRegions.uniqueB_iff`,
  `LeeperRegions.criterion_matters`). Equation (16.21) has two readings. Read literally, with the
  actual surplus driving target debt, fiscal policy is passive iff `γ = α`, as in the Chapter 16
  project (`LeeperRegions.literal_tvc_iff`). Read with an exogenous target, the reading used
  throughout, the passive range is `0 < γ < 2`. Any equilibrium path of one regime is the unique
  equilibrium of every determinate regime around itself, which is the book's "recipe"
  (`Equivalence.oe_both_ways`, `Equivalence.recipe`, `Equivalence.leeper_recipe`).
* **Non-identification and reverse engineering.** On the determinate set the equilibrium set is
  the same singleton for every `(φ, γ)`, so no statistic of the data depends on them and no
  estimator recovers them (NI-1; `NonIdentification.statistic_independent`,
  `NonIdentification.not_identified`). Regressions recover `θ` and `α`, never `φ` and `γ`, and the
  specifications (22.4)–(22.5) impose `φ = θ` and `γ = α` (NI-2, NI-3;
  `NonIdentification.regression_identifies_theta`, `NonIdentification.spec_forces_phi_eq_theta`,
  `NonIdentification.regression_identifies_alpha`, `NonIdentification.spec_forces_gamma_eq_alpha`).
  Any path obeying the Fisher equation and the flow condition is a Leeper-model equilibrium for
  every `(φ, γ)` with reverse-engineered disturbances (`NonIdentification.reverse_engineer_leeper`).
  An s-shaped surplus can come from `α > 0` or from an s-shaped disturbance with `α = 0`
  (`NonIdentification.sshape_two_ways`, `NonIdentification.irf_pv_zero`).
* **The four Leeper regions.** In the unstarred model (22.3)–(22.6) = (23.1)–(23.4): (a)
  `|φ| > 1`, `0 < γ < 2` and (b) `|φ| < 1`, `γ ≤ 0 ∨ γ ≥ 2` each have exactly one equilibrium
  (`LeeperRegions.region_a`, `LeeperRegions.region_b`), but (b) only for bounded inherited debt
  (`LeeperRegions.region_b_iff`, `LeeperRegions.region_b_unbounded_K`). In (c), both active, an
  equilibrium exists iff a cross-restriction on the disturbances holds; at most one inherited debt
  works, and with martingale-difference fiscal shocks none does (`LeeperRegions.region_c_iff`,
  `LeeperRegions.region_c_unique_K`, `LeeperRegions.region_c_coin`). In (d), `|φ| < 1`,
  `0 < γ < 2`, there is a continuum, with random sunspots (`LeeperRegions.region_d`,
  `LeeperRegions.region_d_sunspot`). At the boundary `|φ| = 1` the model is neither determinate
  nor always indeterminate: there is a continuum when the monetary equation has a bounded
  solution and no equilibrium for `u_{i,t} = −φ^{t+1}` (`LeeperRegions.region_d_of_solution`,
  `LeeperRegions.region_d_unit_nonexistence`). Double-active policy is uniquely determinate in the
  starred form and generically has no equilibrium in the unstarred form (E19;
  `LeeperRegions.e19_starred_vs_unstarred`).
* **OE-2: money regimes.** In the money model `MV = Py`, `W_t/P_t = ∑βʲs_{t+j}`, an equilibrium
  path is the unique equilibrium of the active-money regime given `M` and of the active-fiscal
  regime given `(W, s)` (`MoneyRegimes.oe2`). With `M`, `s` and `W` all fixed an equilibrium exists
  iff they are consistent, and halving `M` leaves none (`MoneyRegimes.inconsistent_iff`,
  `MoneyRegimes.halve_money_no_eqm`). The money model's observable path is also the unique
  equilibrium of every determinate interest-rate regime (`Links.oe2_oe1`).
* **Theorem RG: a positive surplus-on-debt coefficient.** With an exogenous moving-average surplus
  and the valuation equation, `2Cov(s_{t+1}, v_t) = ∑_{k≥1}a_k² + ∑_{k,l≥1}ρ^{|k−l|}a_ka_l`, and
  the regression coefficient is positive iff the surplus is not white noise
  (`SurplusRegression.two_cov_eq_kms`, `SurplusRegression.regCoeff_pos_iff`). The proof is the
  positive-definiteness of the Kac–Murdock–Szegő kernel `ρ^{|k−l|}`
  (`MACovariance.kmsForm_eq_ldl`, `MACovariance.kmsMatrix_posDef`). The theorem holds for every
  absolutely summable infinite moving average too (`SurplusRegression.two_covInf_eq`,
  `SurplusRegression.kmsInf_pos`, `SurplusRegression.regInf_pos_iff`). The book's hypothesis
  `a(ρ) < 1` is superfluous: the MA(1) `(1, 1)` and every AR(1) violate it and give a positive
  coefficient, `1 − ρη` for the AR(1) (E16; `SurplusRegression.ma1_regCoeff_pos`,
  `SurplusRegression.ar1_regCoeff`).
* **Granger causality and information.** The footnote's two definitions of Granger causality
  coincide in a bivariate VAR and differ with three variables: in the chain `x → w → y`, `x` does
  not cause `y` at one step but moves it at horizon 2 (E17; `Granger.bivariate_oneStep_iff_irf`,
  `Granger.trivariate_counterexample`). In the news model `s_{t+1} = ε_t` debt Granger-causes
  exogenous surpluses and not conversely (`Granger.news_debt_causes_surplus`,
  `Granger.news_surplus_not_cause_debt`). The present-value relation with our forecasts holds iff
  the value of debt is in our information set (`Granger.pv_ours_iff`, `Granger.pv_ours_fails`).
* **Present-value identities (Online Appendix Chapter 2).** In a VAR containing `v`, the flow
  identity forces the coefficient restriction (2.25), which is the present-value restriction
  (2.26), so (2.26) "reduces to `v_t = v_t`" (`PresentValueIdentity.flow_restriction_iff_pv`,
  `PresentValueIdentity.var_pv_identity`). An exact identity among VAR variables forces a singular
  shock covariance (`PresentValueIdentity.flow_forces_singular`,
  `PresentValueIdentity.nondeg_forces_trivial`). The linearised identity holds ex post, so ex ante,
  and `a_s(ρ) = a_r(ρ)` is an identity (`PresentValueIdentity.pv_identity_exante`,
  `PresentValueIdentity.as_eq_ar_innov`). The ex-post discount factor `Q_tP_{t+1}/P_t` prices the
  bond exactly and turns the flow constraint into the valuation equation
  (`PresentValueIdentity.sdf_prices_bond`, `PresentValueIdentity.sdf_valuation_E`). The
  finite-state fundamental theorem of asset pricing is proved by Hahn–Banach separation
  (`AssetPricingOE.ftap`); probabilities and marginal utility are identified only as a product
  (`AssetPricingOE.same_prices_iff`).
* **Davig–Leeper Markov switching.** With two Markov regimes and `φ_i > 0`, the model has exactly
  one bounded equilibrium for every bounded disturbance iff the Davig–Leeper long-run Taylor
  principle holds, equivalently both eigenvalues of `Φ⁻¹P` lie in the open unit disc
  (`MarkovRegimes.determinate_iff`, `MarkovRegimes.dl_iff_schur`). A temporarily passive regime
  can be determinate and a locally active one indeterminate
  (`MarkovRegimes.temporarily_passive_determinate`, `MarkovRegimes.locally_active_indeterminate`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections are the confirmed errors of the chapter survey:
* the regime labels on pp. 495, 501 and 512–513: `|φ| > 1` and `|θ| < 1`, not `φ > 1` and
  `θ < 1`, and passive fiscal policy is `0 < γ < 2` under the transversality condition, not
  `γ > 0` (E12);
* the missing `ρ` in (22.6), p. 500 (E13);
* `θπ_t` for `θπ*_t` in (24.1), p. 520, which makes the off-target coefficient `θ + φ` (E14);
* the superfluous `a(ρ) < 1` hypothesis on p. 519 (E16);
* the footnote "equivalently" on p. 501, false with three or more variables (E17);
* "both active: no equilibrium can form" on p. 508, false in the starred form and only generic in
  the unstarred one (E19);
* the printed (16.21), under which passivity is `γ = α` (E6, carried over from Chapter 16).

In addition, the formalisation shows that the regime boundary depends on the equilibrium
criterion, that the boundary `|φ| = 1` is neither determinate nor indeterminate, that region (b)
needs bounded inherited debt, and that an exact present-value identity in a VAR needs singular
shocks.

Not formalised:
* the verbal and empirical parts of Chapter 22: §§22.2.1–22.2.3 beyond the recipe, narrative
  identification (p. 498), §22.4 "Plausibility and other evidence", the laugh tests of §22.5
  (apart from the discount-factor point, `PresentValueIdentity.sdf_valuation_E`), Japan's debt,
  §22.6 "Chicken and regimes", and §22.8;
* the literature review of Chapter 23 beyond (23.1)–(23.4) and the remarks of pp. 512–513, and of
  Chapter 24 beyond §24.1, (24.1)–(24.2) and the Davig–Leeper model of pp. 522–523; in particular
  the label swap in Beck-Friis–Willems (p. 525, E15) and the two-currency results (p. 527);
* Online Appendix §§2.1.1–2.1.6 and the permanent-transitory model of §2.4 (pp. 607–611), which
  belong to the `DebtDeficitsInflation` project;
* Theorem RG for square-summable but not absolutely summable moving averages: the covariance is an
  abstract bilinear form with no `L²` structure to control the Toeplitz operator;
* covariances as genuine probability covariances: they are a symmetric bilinear form for which the
  shocks are orthonormal, and the model that shows the hypotheses consistent
  (`SurplusRegression.truncSystem`) is certainty-equivalent;
* Markov switching with more than two regimes, with `φ_i ≤ 0`, or with a non-degenerate chain in
  an abstract `ExpectationSystem` (no pointwise-linear expectation carries one; the abstract
  results are stated for any system that does);
* region (d) sunspot families in the unstarred model at `|φ| = 1` (they exist exactly when the
  monetary equation has a bounded solution, `LeeperRegions.region_d_of_solution`);
* the money model under uncertainty: OE-2 is proved under perfect foresight, as in the book;
* the household problems behind the Fisher equation, the flow condition and `MV = Py`: all are
  imposed as equilibrium conditions.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](ObservationalEquivalence/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (shared core, restated from the earlier projects) |
| [Expectations](ObservationalEquivalence/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; adapted and AR(1) processes; forward series; the pull-out property (shared core) |
| [ExpectationsFiniteTree](ObservationalEquivalence/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; the coin-flip tree and its shock (shared core) |
| [ForwardSolution](ObservationalEquivalence/ForwardSolution.lean) | 44 | The forward solution of `z_t = aE_tz_{t+1} + u_t` and the sunspot family (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [ExpectationTools](ObservationalEquivalence/ExpectationTools.lean) | 7 | Shared by both halves: the innovation `ΔE_{t+1}`, full information, the ex-post present value, geometric weights, iterating a flow identity |
| [FiscalRec](ObservationalEquivalence/FiscalRec.lean) | 16 | Scalar debt recursions; Woodford's (4.2), (4.4)–(4.5) and locally Ricardian rules (restated from the Woodford Chapter 4 project); the corrected boundaries `0 < γ < 2` |
| [Valuation](ObservationalEquivalence/Valuation.lean) | 22 | §22.1, (22.2): the flow condition, the transversality condition iff the valuation equation, unexpected inflation |
| [StarredModel](ObservationalEquivalence/StarredModel.lean) | 18 | (16.20)–(16.24), (22.1), (22.7)–(22.11), (23.4), (24.1): the starred system, deviations, valuation in all regimes, the Leeper model, E13–E14 |
| [Equivalence](ObservationalEquivalence/Equivalence.lean) | 34 | §§22.1–22.2: OE-1 with E12 corrected, the double-passive continuum and sunspots, the recipe, the §16.6 AR(1) example |
| [NonIdentification](ObservationalEquivalence/NonIdentification.lean) | 25 | §22.1, §22.3, §16.5: NI-1 to NI-3, reverse engineering, the s-shaped surplus both ways |
| [LeeperRegions](ObservationalEquivalence/LeeperRegions.lean) | 36 | §22.7, (22.3)–(22.6), (23.1)–(23.4): regions (a)–(d), the boundary `\|φ\| = 1`, E19, the bounded-debt criterion, the printed (16.21) |
| [MoneyRegimes](ObservationalEquivalence/MoneyRegimes.lean) | 10 | §22.1, §22.7: OE-2 for money-supply regimes; inconsistent money and surpluses |
| [MACovariance](ObservationalEquivalence/MACovariance.lean) | 19 | Finite moving averages, covariances, the Kac–Murdock–Szegő kernel and its LDL factorisation |
| [SurplusRegression](ObservationalEquivalence/SurplusRegression.lean) | 61 | p. 501, §24.1, A2 p. 593: Theorem RG for finite and infinite moving averages, E16, AR(1), a non-vacuity model |
| [Granger](ObservationalEquivalence/Granger.lean) | 23 | p. 501 footnote 1, pp. 501–502, A2 (2.22)–(2.23): Granger definitions and E17, the news model, information sets |
| [PresentValueIdentity](ObservationalEquivalence/PresentValueIdentity.lean) | 47 | A2 (2.24)–(2.26) and §2.3 (VAR block restated from the `DebtDeficitsInflation` project), singular shocks, the ex-post discount factor of p. 499 |
| [AssetPricingOE](ObservationalEquivalence/AssetPricingOE.lean) | 11 | §22.2.4: rational and behavioural pricing, the risk-neutral measure, the finite-state FTAP |
| [MarkovRegimes](ObservationalEquivalence/MarkovRegimes.lean) | 27 | §24.2: Davig–Leeper Markov switching, determinacy iff the long-run Taylor principle, examples |
| [Links](ObservationalEquivalence/Links.lean) | 20 | Agreement between the two halves of the project; OE-2 with OE-1; links to Woodford Prop. 4.11 |

## Modelling conventions

* **Expectations.** Random variables are `Ω → ℝ`, processes `ℕ → Ω → ℝ`, and every linear model
  equation holds as an equality of functions, for an arbitrary `ExpectationSystem`. A process is
  adapted when `E_tx_t = x_t` (`ExpectationSystem.Adapted`). Perfect foresight
  (`perfectForesight`), full information on any state space (`ExpectationTools.fullInfo`) and
  every finite event tree (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) are
  instances; the coin-flip tree (`ExpectationsFiniteTree.coinSystem`) makes the sunspot and
  non-existence examples genuinely random. The innovation `ΔE_{t+1} = E_{t+1} − E_t` is the
  linear map `ExpectationTools.innov`.
* **The starred model.** A path is `StarredModel.Outcome` `(π, i, v, s̃)`. The target obeys the
  Fisher equation and the flow condition (`StarredModel.Consistent`), and its debt is driven by
  the target surplus `s̃*_{t+1} = αv*_t + u_{s,t+1}` (`StarredModel.StarredSurplus`). The printed
  (16.21) drives target debt with the actual surplus; on the target both readings coincide, and
  off it the printed one is treated separately (`LeeperRegions.literal_tvc_iff`). An equilibrium
  of the `(φ, γ)` system is `StarredModel.Eqm`.
* **The initial condition.** Inherited nominal debt and the date-0 surplus are common to every
  candidate path, so the date-0 flow condition becomes `ρv_0 + π_0 = ρv*_0 + π*_0`. The condition
  `π_0 = π*_0` is not imposed: it is derived in the determinate regions
  (`Equivalence.unique_of_determinate`), and in the double-passive region the date-0 jump indexes
  a continuum under perfect foresight (`Equivalence.perfectForesight_eq_famPath`). In the Leeper
  model the inherited debt is `ρv_0 + π_0 = K` with `K` known at date 0
  (`StarredModel.LeeperEqm`).
* **Equilibrium criteria.** An equilibrium is admissible when inflation and debt are adapted,
  inflation is bounded and debt satisfies the transversality condition `ρᵀE_tv_{t+T} → 0`
  (`StarredModel.Admissible`, `Valuation.TVC`). The Woodford–Leeper alternative requires bounded
  debt (`LeeperRegions.AdmissibleB`). Uniqueness means the target is the only admissible
  equilibrium (`Equivalence.UniqueEqm`, `LeeperRegions.UniqueEqmB`).
* **Observational equivalence is pathwise.** Two regimes are equivalent when they have the same
  equilibrium set as a set of paths (`NonIdentification.EqmSet`), so every statistic, any
  likelihood included, agrees (`NonIdentification.statistic_independent`).
* **Covariances.** Second moments are taken with a symmetric bilinear form `B` on random
  variables for which the shocks are orthonormal (`MACovariance.WhiteNoise`); the shocks are a
  martingale difference sequence for the agents (`SurplusRegression.ShockInfo`). Every `L²` model
  is an instance, and `SurplusRegression.truncSystem` with `SurplusRegression.truncCov` satisfies
  all the hypotheses with nonzero bounded shocks.
* **VARs.** `z_{t+1} = Az_t + ε_{t+1}` with `E_tε_{t+1} = 0` (`Granger.IsVAR`,
  `Granger.ShockMDS`); stability is geometric decay of the powers of `A`
  (`PresentValueIdentity.PowDecay`), implied by eigenvalues in the open unit disc
  (`PresentValueIdentity.powDecay_of_eigs`).
* **The money model.** Deterministic sequences under perfect foresight, as in the book, with
  `W_t = B_{t−1} + M_{t−1}`, positive velocity and output, bounded surpluses and `0 ≤ β < 1`
  (`MoneyRegimes.Eqm`).
* **Markov switching.** All uncertainty comes from the regimes, so a process is a function of the
  regime history (`MarkovRegimes.Node`) and bounded means bounded over all histories
  (`MarkovRegimes.BoundedFn`). The same uniqueness dichotomy is proved for any `ExpectationSystem`
  carrying a Markov regime process (`MarkovRegimes.MarkovRegime`).
* **Explicit hypotheses.** Bounded adapted disturbances, `0 < ρ < 1` (or `|ρ| < 1`, or `ρ ≠ 0`,
  as each proof needs), bounded inherited debt in region (b), absolute summability of
  infinite moving averages and `φ_i > 0` for Markov switching are stated in each theorem.

## Relation to the Woodford projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects, so the project builds on its own. Nothing is imported from
those projects. Two further blocks are restated from the Woodford Chapter 4 project
(`NeoWicksellianFramework`), and their docstrings say so:
* `FiscalRec`, from its `Fiscal` and `BlanchardKahn` modules: Woodford's (4.2), (4.4) and (4.5)
  (`FiscalRec.Debt42`, `FiscalRec.Tax44`, `FiscalRec.Debt45`, `FiscalRec.debt42_iff_45`), the
  scalar recursion and its bounded-input-bounded-state property (`FiscalRec.dRec`,
  `FiscalRec.eq_dRec`, `FiscalRec.abs_rec_le`, `FiscalRec.rec_bounded`, `FiscalRec.rec_unbounded`,
  `FiscalRec.pow_bounded_eq_zero`, `FiscalRec.dRec_adapted`), and locally Ricardian tax rules
  (`FiscalRec.LocallyRicardian`, `FiscalRec.locallyRicardian_iff`,
  `FiscalRec.ricardian_iff_taub`);
* the eigenvalue bound behind geometric decay in `PresentValueIdentity`, from its
  `InvariantSplit` module by way of the `DebtDeficitsInflation` project
  (`PresentValueIdentity.eigs`, `PresentValueIdentity.map_ofReal_pow`,
  `PresentValueIdentity.powDecay_of_eigs`).

`Links` relates the bounded-debt criterion to Woodford's Proposition 4.11. In Cochrane's notation
a fiscal rule is locally Ricardian iff `|1 − γ| < ρ` (`LeeperRegions.locallyRicardian_iff_gamma`).
With passive money `|φ| ≤ 1`, the target is the unique bounded equilibrium iff the rule is not
locally Ricardian and `|1 − γ| ≠ ρ` (`Links.uniqueB_iff_not_ricardian`). On the boundary
`|1 − γ| = ρ` the rule is not locally Ricardian, yet bounded sunspot paths still exist. A locally
Ricardian rule with passive money is indeterminate under both criteria
(`Links.ricardian_passive_not_unique`). Cochrane's transversality criterion is weaker than
Woodford's: `γ = (1 − ρ)/2` is passive under the first and active under the second
(`LeeperRegions.criterion_matters`).

## Relation to other Cochrane projects

* **Chapter 16 (`NewKeynesianSelection`).** That project proves the Chapter 16 special cases of
  observational equivalence and non-identification (NI-1 to NI-6) in the simplest model, and the
  two-way translation of the §16.6 AR(1) example. This project owns the general theorems for the
  starred form (`StarredModel`, `Equivalence`, `NonIdentification`) and proves the AR(1) example
  again in its own setting (`Equivalence.nk_solution`, `Equivalence.ftpl_eq_nk`,
  `Equivalence.nk_passive_fiscal_news`). The two agree on E6: under the printed reading of
  (16.21), passivity holds iff `γ = α` (there `ObservationalEquivalence.passive_iff`; here
  `LeeperRegions.literal_tvc_iff`). This project takes the exogenous-target reading as its main
  one, under which the range is `0 < γ < 2` (`Equivalence.unique_iff`).
* **Chapter 4 and Online Appendix Chapter 2 (`DebtDeficitsInflation`).** The VAR block of
  `PresentValueIdentity` (`PresentValueIdentity.obs` to `PresentValueIdentity.var_pv_identity`)
  and the VAR forecast and impulse-response lemmas of `Granger` (`Granger.IsVAR`,
  `Granger.var_forecast`, `Granger.var_innov`) are restated from its `VARIdentities` module, as
  the module and section docstrings say. That project owns the `a(ρ)` results of Chapter 4 and
  Online Appendix §§2.1.1–2.1.6 and 2.4; this one adds the singular-shock theorems, the §2.3
  identity, the ex-post discount factor and the information-set results of (2.22)–(2.23).

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
