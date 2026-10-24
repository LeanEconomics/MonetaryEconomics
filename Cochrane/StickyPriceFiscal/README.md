# Fiscal theory in sticky-price models in Lean

This is the `Cochrane/StickyPriceFiscal/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Chapter 5, "Fiscal theory in sticky-price models" (pp. 117–186), together
with the parts of the Online Appendix that the chapter relies on: §§A1.7–A1.13 (pp. 569–585),
§A1.3 on the geometric maturity structure (pp. 561–564) and §A2, (2.1)–(2.3) (p. 595). The
discrete-time models (§§5.1–5.6) are stated for an arbitrary `ExpectationSystem`, so every result
holds under perfect foresight and under genuine uncertainty. The continuous-time models (§5.7)
are about deterministic paths after a date-0 shock, which is how the book computes its responses.
"Determinate" means that exactly one bounded equilibrium exists for every admissible forcing and
initial condition. The library contains **933 theorems**, including the shared core; 825 of them
are in the nineteen chapter modules, 108 of these in a verbatim copy of the Woodford Chapter 4
Blanchard–Kahn theorem (`BKCopy`).

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises. Survey codes E19–E54 refer to the
survey of Chapters 4–5.

## Headline results

All names are in the namespace `Cochrane.StickyPriceFiscal`.

### The new-Keynesian model (§5.1, §5.1.1)

* **The Euler equation, exactly.** Under pull-out the consumer's first-order condition is exactly
  `log(1 + I_t) − δ = −log E_t[exp(X_{t+1})]`, and its derivative along bounded directions is the
  IS curve (5.1) with `σ = 1/γ` (`NKModel.euler_log_form`, `NKModel.euler_deriv`,
  `NKModel.is_iff_linear_euler`). Integrating (5.1) forward, (5.3), holds iff `E_tx_{t+k} → 0`
  (`NKModel.eq_5_3`).
* **The roots and the long run.** `0 < λ₂ < 1 < λ₁`, `λ₁λ₂ = β`, and the coefficients of (5.5)
  sum to one (`NKModel.one_lt_lam1`, `NKModel.lam2_lt_one`, `NKModel.coeff_sum_one`). Constant
  equilibria are Fisherian, and indexation removes the long-run tradeoff (`NKModel.nk_const_iff`,
  `NKModel.ipc_no_tradeoff`).
* **Inflation is a two-sided moving average.** Bounded `(x, π)` solve the model iff inflation has
  the form (5.5) for some date-0 constant and bounded martingale-difference shock
  (`TwoSidedMA.eq_5_5`). The forward-looking half means that with sticky prices inflation moves
  before an announced rate rise (`TwoSidedMA.anticipated_moves_before`).

### Fiscal theory in the new-Keynesian model: determinacy and `ρ = 1` (§5.1.2)

* **Determinacy.** With the predetermined real value of debt `b_{t+1} = v_t + i_t` as the state,
  the model (5.15)–(5.16) has exactly one bounded equilibrium for every bounded rate and surplus
  path and initial debt, for `0 < ρ < 1` (`FiscalNK.fiscalNK_determinate`,
  `FiscalNK.eqm_determinate`). Existence is by explicit construction (`FiscalNK.eqm_exists`).
* **`ρ = 1`.** Boundedness no longer selects: every bounded equilibrium has a one-parameter family
  of bounded companions (`FiscalNK.rho_one_not_determinate`). The transversality condition rules
  them out and selects at most one, for every `0 < ρ ≤ 1` (`FiscalNK.rho_one_tvc_unique`,
  `FiscalNK.eqm_unique_tvc`). "`ρ ≤ 1` provides the forward-looking root" holds only with the
  transversality condition (E20, E32).

### Closed forms under a peg (§§5.1.2, 5.2, 5.3)

* **Any deterministic path.** Under a peg with deterministic surpluses inflation is
  `a + (1 − ρ/λ₁)(b₀ − a − S)λ₁^{−t}`, depending on surpluses only through their present value
  (`FiscalNK.det_unique`, `FiscalNK.pv_only`).
* **Permanent rise (Fig. 5.1).** `π_{1+j} = 1 − (1 − ρ/λ₁)λ₁^{−j}`, with `π₁ = ρ/λ₁ > 0`, larger
  for stickier prices (`FiscalNK.perm_rise`, `FiscalNK.perm_rise_pi0_strictAnti`). As `κ → 0` it
  tends to `ρ`, not to the rise (E27, `FiscalNK.perm_rise_kappa_zero`). Output falls on impact
  only under a condition, which fails for sticky enough prices
  (`FiscalNK.perm_rise_x0_neg_iff`, `FiscalNK.perm_rise_x0_pos_small_kappa`).
* **Anticipated rise (Fig. 5.2), new closed form.** A rise announced for date `S` gives
  `π_t = Bλ₂^{S−t} + Cλ₁^{−t}` before it and `1 + (B − 1)λ₁^{−(t−S)} + Cλ₁^{−t}` after; this is
  the unique bounded equilibrium (`FiscalNK.anticipated_rise`).
* **Fiscal shock (Fig. 5.3).** `π_{1+j} = (1 − ρ/λ₁)λ₁^{−j}`; the impact is in `(0.394, 0.395)`
  at the figure's calibration; the `ρ`-weighted cumulative inflation is exactly one, the raw sum
  is in `(1.015, 1.016)` (`FiscalNK.fiscal_shock`, `FiscalNK.fig53_impact`,
  `FiscalNK.fiscal_shock_pv_one`, `FiscalNK.fig53_cumulative`; E28).
* **AR(1) rise with long-term debt, and the p. 131 persistence correction.** For `i_t = η^t`,
  `π_t = Aη^t + Cλ₁^{−t}` in closed form (`LongTermDebt.ltd_ar1`, `LongTermDebt.ar1_impact`).
  With `ρ = β`, as in the book's calibrations, a rise of **any** persistence `0 ≤ η < 1` is
  disinflationary on impact iff `ω̃ > ρ/λ₁`, the permanent-rise condition
  (`LongTermDebt.ar1_disinflation_iff_rho_eq_beta`). So "the interest-rate rise must be
  persistent" (p. 131) is not a precondition: persistence only enlarges the disinflation
  (`LongTermDebt.ar1_magnitude_rho_eq_beta`). Long-term debt and surprise are necessary
  (`LongTermDebt.ar1_short_debt_no_disinflation`, `HigherOrLower.anticipated_rise_no_disinflation`).

### Long-term debt (§5.2, App. §1.3)

* **The exact weight.** The portfolio return is linearised as an exact derivative, with
  coefficient `ω̃ = ω/(1 + i)` (`LongTermDebt.bondReturn_hasFDerivAt`, `LongTermDebt.bondReturn_ss`);
  the `ω` of App. (1.24) is strictly larger (E23, `LongTermDebt.e23_coef_lt`). The model is written
  with `ω̃`, and it is determinate (`LongTermDebt.ltd_determinate`).
* **Fig. 5.4.** After a permanent rise `π_{1+j} = 1 − [(1 − ρ/λ₁)/(1 − ω̃)]λ₁^{−j}`, so **inflation
  falls on impact iff `ω̃ > ρ/λ₁`** (`LongTermDebt.ltd_perm_rise`,
  `LongTermDebt.ltd_disinflation_iff`), more with longer maturity and less sticky prices, and
  then rises to the new rate (`LongTermDebt.ltd_strictAnti_om`,
  `LongTermDebt.ltd_pi0_strictAnti_kappa`, `LongTermDebt.ltd_tendsto_one`). The plotted values
  are those of the caption's `ω = 0.85` with the exact weight, not the text's `ω = 0.8` (E29,
  `LongTermDebt.fig54_impact`).
* **Irrelevance.** Maturity does not matter without bond-price news: for anticipated rate paths
  and for fiscal shocks at a fixed rate (`LongTermDebt.ltd_anticipated_no_news`,
  `LongTermDebt.ltd_fiscal_shock`).

### The surplus process and active versus passive policy (§5.4, (5.38) corrected)

* **The s-shaped surplus.** The moving-average representations (5.25)–(5.26), `a(ρ) = β_s` for
  `0 < α < 2` (the upper bound is missing in the book, E31), and exactly one sign change
  (`SurplusProcess.s_ma_525`, `SurplusProcess.aCoef_526`, `SurplusProcess.hasSum_aCoef`,
  `SurplusProcess.s_shape`). In the frictionless model `ΔEπ = −β_sε` and debt equals the latent
  `v*` (`SurplusProcess.equilibrium_528`).
* **Selection.** Boundedness selects `v = v*` for `|ρ| < 1`; at `ρ = 1` a bounded counterexample
  exists, and the transversality condition selects at every `ρ` (`ActivePassive.select_bounded`,
  `ActivePassive.rho_one_counterexample`, `ActivePassive.select_tvc`).
* **(5.38) corrected.** Under `s̃ = αv* + γ(v − v*) + u`, policy is **active iff `γ ≠ α`**, not
  "iff `γ = 0`" (E33, `ActivePassive.tvc_v_iff_538`, `ActivePassive.active_iff_538`,
  `ActivePassive.printed_538_false`). A rule on actual debt is passive exactly for `0 < γ < 2`,
  with bounded debt for `1 − ρ < γ < 1 + ρ` (`ActivePassive.gamma_passive_iff`,
  `ActivePassive.gamma_bounded`; E54 and the `γ` condition E6 of the survey of Chapters 11–19).
  The debt equation of (5.41) has a sign error (`ActivePassive.printed_541_sign`).
* **Observational equivalence.** The active-fiscal model and the active-money model (5.42) have
  the same equilibrium observables (`ActivePassive.observationally_equivalent`).
* **Nonlinear continuous time (§5.4.2).** The transversality condition is equivalent to the
  valuation equation; `γ > 0` gives it, `γ > r` keeps debt bounded and `γ = r` does not (E34); the
  passive nominal rule is consistent with every price level; `P_0 = P*_0` needs `B_0 ≠ 0` (E37)
  (`NonlinearCT.tvc_iff_pv`, `NonlinearCT.gamma_pos_tvc`, `NonlinearCT.gamma_eq_r_counterexample`,
  `NonlinearCT.nominal_passive`, `NonlinearCT.price_level_unique`).

### Policy rules: the exact model-level determinacy condition (§5.5, App. §§1.9–1.11)

* **The `(x, π)` block.** Through the copied general Blanchard–Kahn theorem, the block is
  determinate iff the passive-money condition `κ(θ_iπ − 1) + (1 − β)θ_ix < 0` holds; `θ_iπ < 1`
  alone is not enough (E43); genericity holds iff `κ ≠ 0` (`PolicyRules.block_determinate_iff`,
  `PolicyRules.thetaIpi_lt_one_insufficient`, `PolicyRules.genericX_iff_kappa_ne_zero`).
* **Determinacy of the model.** Under passive money, `|ω| < 1`, `ρ > 0` and `|1 − α| < ρ`
  there is exactly one bounded equilibrium for every initial inflation and debt
  (`PolicyRules.policyRules_determinate`, `PolicyRules.policyRules_full_determinate`). Active
  money, or `|1 − α| > ρ`, leaves some initial condition without one
  (`PolicyRules.nonexist_of_active`, `PolicyRules.nonexist_of_alpha`).
* **The `α` boundary, exactly.** There is always at most one equilibrium
  (`PolicyRules.policyRules_unique`). Writing debt as a bounded state part plus a shock-driven
  part `W_{t+1} = φW_t + κ_sε_{s,t+1} + κ_iε_{i,t+1}`, `φ = (1 − α)/ρ`, an equilibrium exists iff
  `W` is bounded (`PolicyRules.alpha_exists_iff`). Hence the model is determinate iff
  `|1 − α| ≤ ρ` under perfect foresight (`PolicyRules.alpha_iff_pf`), and iff `|1 − α| < ρ`, or
  `|1 − α| = ρ` with `κ_s = κ_i = 0`, with recurring news (`PolicyRules.alpha_iff_trunc`).
* **The unit root, exactly.** On `κ(θ_iπ − 1) + (1 − β)θ_ix = 0` (E20) the model has at most one
  equilibrium, and one exists iff the inflation martingale `π + ku_i` is bounded
  (`PolicyRules.unitroot_unique`, `PolicyRules.unitroot_exists_iff`). It is determinate under
  perfect foresight (`PolicyRules.unitroot_pf`), and with recurring news iff `β_s = 0` and
  `β_i = k` (`PolicyRules.unitroot_iff_trunc`).
* **The `truncSystem` caveat.** "Recurring news" is the truncation expectation system
  `PolicyRules.truncSystem` on coin sequences: `E_t` evaluates at the path that keeps the first `t`
  coins and sets the later ones to tails. It satisfies every `ExpectationSystem` axiom and makes
  coin-driven shocks unpredictable, but it is a point-mass belief. The non-existence happens on the
  all-heads path (`PolicyRules.bump_unbounded`), to which this belief gives probability zero. The
  core has no infinite-horizon full-support coin system, so whether a full-support i.i.d. system
  gives the same verdict is not proved.
* **Responses and Table 5.1.** The closed form `x_t = gπ_t − σ/(λ_u − η_i)u_{i,t}`,
  `E_tπ_{t+1} = λ_sπ_t + …` (`PolicyRules.closed_form`); the identities (3.20)–(3.22) for every
  bounded solution (`PolicyRules.identity_320`, `PolicyRules.identity_321`,
  `PolicyRules.identity_322`); the corrected Table 5.1 entries (E40, E41,
  `PolicyRules.table51_monetary_noRule_corrected`, `PolicyRules.betaS_bookRules_etaS`).
* **The appendix.** The corrected `λ±` (E19, `PolicyRules.appA1_lambda_pm`) and the corrected
  minimum-state-variable solution, unique from boundedness alone (E21, `PolicyRules.msv_unique`).

### Continuous time, with certified Figure 5.11 and Table 5.2 numbers (§§5.7–5.7.5, App. §1.12)

* **All bounded solutions.** For any bounded continuous rate path, `(x, π)` is a bounded solution
  iff `π` belongs to the family (5.94), indexed by `π₀` (`CTSimple.ct_family`,
  `CTSimple.ct_family_pinned_by_pi0`). With predetermined debt the valuation equation selects
  exactly one member, with no price-level jump (`CTSimple.ct_equilibrium_exists_unique`,
  `CTSimple.ct_no_price_jump`); the step example (5.96) and its frictionless limit follow
  (`CTSimple.ct_step_solution`, `CTSimple.ct_price_limit`).
* **Long-term debt (Fig. 5.10).** `π₀ = 1 − (r + λ₂)/(r + ω)`, negative iff `ω < λ₂`, with a
  smooth frictionless limit and longer disinflation for stickier prices
  (`CTSimple.fig510`, `CTSimple.fig510_initial_disinflation`, `CTSimple.fig510_price_limit`,
  `CTSimple.fig510_disinflation_longer`).
* **S-shaped surpluses (§5.7.2).** The impulse response in closed form, with a single sign
  change, and `L(r) = +β_s`, not `−β_s` (E47) (`CTSurplus.ct_surplus_irf`, `CTSurplus.ct_s_shape`,
  `CTSurplus.surplus_L_r`).
* **Rules (§§5.7.3–5.7.5).** Eliminating `v*` needs `v*₀ = v₀` (E49, `CTRules.ct_elim`). For every
  `α` an equilibrium is determined by `π₀`; for `α > 0` every `π₀` is an equilibrium and (5.111)
  selects one; for `α ≤ 0` the valuation equation pins it (`CTRulesEquilibrium.rules_unique_of_pi0`,
  `CTRulesEquilibrium.rules_exists_unique_beta`, `CTRulesEquilibrium.rules_unique_nonpos`). A
  surplus rule reacting to inflation can make inflation fall after a rate rise even with
  short-term debt (`CTRules.ct_fiscal_rule_negative_iff`).
* **Certified numbers.** In the Fig. 5.11 model an equilibrium exists, is unique and has
  `−0.8028 < π₀ < −0.8027` (`CTRulesEquilibrium.fig511_pi0`). For Table 5.2 row 4 an `α = 0.4`
  equilibrium with zero weighted sum of surpluses exists and every one has
  `−0.5086 < β_i < −0.5085`, not the printed `−0.91` (E52, `CTRulesEquilibrium.table52_betai`).
  Both are proved by rational enclosures, not floating point.

### The matrix method (App. §1.13)

* **Real diagonalisable systems.** A response is bounded iff the explosive modes start at zero;
  the expectational errors follow from the explosive rows (`CTRules.matrix_bounded_iff`,
  `CTRules.matrix_errors`, `CTRules.matrix_errors_unique`). A zero eigenvalue is not stable (E25,
  `CTRules.mode_zero_unbounded`).
* **Complex and defective eigenvalues, given a Jordan decomposition.** Given `A = QJQ⁻¹` with `J`
  in Jordan form, a solution of `z' = Az` is bounded iff the modes with `Re d > 0` and the
  non-leading modes of blocks with `Re d = 0` start at zero (`CTMatrixMethod.jordan_modes_bounded_iff`,
  `CTMatrixMethod.matrix_jordan_bounded_iff`), with the cases diagonalisable over `ℂ` and real
  systems (`CTMatrixMethod.matrix_cdiag_bounded_iff`, `CTMatrixMethod.real_system_bounded_iff`).
  The decomposition is a hypothesis, as in the book's `A = QΛQ⁻¹`: Mathlib has no Jordan normal
  form for matrices.

### Sims' model (§5.7.6)

* The system (5.118)–(5.125) with exact linearisations of the perpetuity price, the value of
  long-term debt and marginal utility (`Sims.SimsSys`, `Sims.perpetuity_linearization`,
  `Sims.debt_linearization`, `Sims.marginal_utility_log`); the bond price, inflation and debt as
  present values (`Sims.bond_price_pv`, `Sims.inflation_pv`, `Sims.debt_pv`); "Fisherian in the
  long run" (`Sims.fisherian_inflation`, `Sims.steady_state_peg`); the habit roots
  (`Sims.habit_roots`).

### Links between the sections

`Links` proves that the separately formalised sections agree: the §5.5 model without rules is the
§5.2 model, and with one-period debt the §5.1.2 model, with the same unique equilibrium
(`Links.redEquil_noRule_eq_ltd`, `Links.redEquil_noRule_eq_fiscalNK`); the discrete roots,
impact coefficient and decay converge to the continuous-time ones as the period length goes to
zero (`Links.tendsto_lam1_scaled`, `Links.tendsto_peg_impact`, `Links.tendsto_peg_decay`); and the
§5.5 determinacy condition in `α` is `|g| ≤ 1` for the §5.4 root, a region in which the rule is
passive in the §5.4 sense (`Links.alpha_iff_pf_gRoot`, `Links.determinate_region_passive`).
`FiscalNK` determinacy is not derived from `PolicyRules.policyRules_determinate`, which assumes
`|1 − α| < ρ` and so excludes the `α = 0` of §5.1.2.

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections are:
* (5.38), p. 139: active iff `γ ≠ α`, not iff `γ = 0` (E33);
* (5.41), p. 139: the sign of `β_sε` in the debt equation (found during formalisation);
* p. 131: persistence is not needed for a disinflationary rate rise (found during formalisation);
* p. 121, pp. 136–137, 148 and App. pp. 574–576: `ρ = 1` and unit eigenvalues are not
  forward-looking roots; the exact model-level answers above (E20, E32);
* the missing upper bounds `α < 2`, `α < 1 + ρ`, `γ < 2`, `γ < 1 + ρ`, and the exact condition in
  `α` (E31, E54, E6 of Chapters 11–19);
* Table 5.1 (`2.58` should be `0.26`, E41; `η_s = 0.5`, not `0.4`, E40) and Table 5.2
  (`β_i = −0.5085`, not `−0.91`, E52);
* the passive-money condition is not `θ_iπ < 1` (E43);
* sign errors in App. §1.9 and §1.9.1 (E19, E21), §5.4.4 (E38), §5.4.2 (E36), §5.7.2 (E45, E47),
  (5.63) (E39) and (5.115) (E51), and the index errors of App. p. 564 (E22) and p. 161 (E44);
* the κ → 0 limit is `ρ`, not `1` (E27); inflation moves before an anticipated rise (E30);
  Fig. 5.4 uses `ω = 0.85` with the exact weight `ω/(1 + i)` (E23, E29).

Not formalised:
* the verbal parts: most of §5.1.3 (pp. 125–127), §5.3 beyond its precise clauses (including the
  foreign-currency-debt clause and the historical discussion), §5.4.3 (pp. 143–145), the shock
  definitions of §5.5.6, and the review §5.8 (pp. 181–186);
* the interest-cost surplus rule of pp. 161–162, a bilinear specification with only verbal claims;
* numbers that need a full numerical solution: most Table 5.1 entries, Figs. 5.6–5.9, Table 5.2
  rows 2–3 (`1.28`, `0.50`), and the hump shape and timing of Figs. 5.14–5.15. Fig. 5.5 itself is
  not formalised, only the facts it plots;
* for `ρ ≠ β`, the dependence of the AR(1) impact response on persistence beyond the closed form
  `LongTermDebt.ar1_impact`; the resonant case `λ₁η = 1` is excluded;
* determinacy with recurring news under a full-support system: the boundary results use the
  point-mass `PolicyRules.truncSystem` (see the caveat above);
* the survey's "strict stationarity" at `ρ = 1`: there is no stationarity notion for an abstract
  `ExpectationSystem`; boundedness and the transversality condition are treated instead;
* the matrix method for every matrix without the Jordan-decomposition hypothesis. A
  hypothesis-free version needs the generalised-eigenspace projections and the asymptotics of
  `exp(tA)`, which Mathlib does not provide in that form. The P/M selector notation of App. §1.13 is
  replaced by row-by-row statements;
* the operator calculus `L(D)` of §5.7.2 in general: it is covered for exponential-sum responses
  (`CTSurplus.hs_pv`, `CTSurplus.hs_innovation`);
* stochastic continuous time: `dε` and `dδ` are date-0 jumps followed by perfect foresight, as in
  the book's responses, not diffusions;
* the full discrete-to-continuous limit of the peg path: only the roots, the impact coefficient
  and the decay factor are shown to converge (`Links`);
* a formal link between `LongTermDebt`'s exact weight `ω̃` and the `omega` of `PolicyRules.Params`
  (the same parameter by docstring only), and between `NonlinearCT.tvc_iff_integral` and
  `CTSimple.tvc_iff_forward`, which use different time conventions.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](StickyPriceFiscal/Determinacy.lean) | 23 | The Schur–Cohn condition and the roots of a real quadratic for `2 × 2` matrices (shared core, restated from the earlier projects) |
| [Expectations](StickyPriceFiscal/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; bounded adapted processes; AR(1) processes; forward series; the pull-out property (shared core) |
| [ExpectationsFiniteTree](StickyPriceFiscal/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; coin-flip examples (shared core) |
| [ForwardSolution](StickyPriceFiscal/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [SharedTools](StickyPriceFiscal/SharedTools.lean) | 13 | The innovation operator `ΔE_{t+1}` (5.58), AR(1) disturbances, the transversality condition, stable scalar recursions |
| [NKModel](StickyPriceFiscal/NKModel.lean) | 39 | §5.1, (5.1)–(5.4), (5.6), (5.8), App. §1.7: the model, the Euler equation as an exact derivative, the forward integrations, the roots, the long-run tradeoff and indexation |
| [TwoSidedMA](StickyPriceFiscal/TwoSidedMA.lean) | 27 | §5.1.1, (5.5), (5.7), (5.9)–(5.10), (5.14), App. §1.7: the two-sided moving average as a characterisation of all bounded equilibria; E26; anticipated rises (E30) |
| [FiscalNK](StickyPriceFiscal/FiscalNK.lean) | 47 | §5.1.2, (5.11)–(5.16): determinacy for `ρ < 1`, `ρ = 1`, peg closed forms for Figs. 5.1–5.3 including the anticipated rise, the calibration |
| [LongTermDebt](StickyPriceFiscal/LongTermDebt.lean) | 38 | §5.2, (5.17)–(5.21), App. §§1.3, 1.10: the exact weight `ω̃`, determinacy, Fig. 5.4, irrelevance without return news, the AR(1) rise of §5.3; E22, E23, E29 |
| [HigherOrLower](StickyPriceFiscal/HigherOrLower.lean) | 14 | §5.3: the Fisher identity, interest costs, the Fisherian long run, the preconditions for a disinflationary rise, the joint contraction |
| [SurplusProcess](StickyPriceFiscal/SurplusProcess.lean) | 60 | §5.4, (5.22)–(5.28), App. A2: the surplus process, its moving averages, `a(ρ) = β_s`, the s-shape, Fig. 5.5, the frictionless equilibrium; E31 |
| [ActivePassive](StickyPriceFiscal/ActivePassive.lean) | 54 | §§5.4.1, 5.4.4, (5.29)–(5.42): selection of `v = v*`, the `γ` rules, (5.38) corrected, (5.41)'s sign, observational equivalence, AR(1) surpluses; E10, E31–E33, E38, E54 |
| [NonlinearCT](StickyPriceFiscal/NonlinearCT.lean) | 41 | §5.4.2, (5.43)–(5.50): the nonlinear continuous-time flow, transversality and valuation, the `γ` rules, nominal debt, the latent `V*`; E34–E37 |
| [AltSurplus](StickyPriceFiscal/AltSurplus.lean) | 15 | §5.6, (5.82)–(5.84): backed and unbacked surplus components; E44 |
| [BKCopy](StickyPriceFiscal/BKCopy.lean) | 108 | The general Blanchard–Kahn theorem, a verbatim copy of the Woodford Chapter 4 project's `InvariantSplit`, `GeneralBKForward` and `GeneralBK` |
| [PolicyRules](StickyPriceFiscal/PolicyRules.lean) | 137 | §5.5, (5.51)–(5.81), App. §§1.9, 1.9.1, 1.11: the model with rules, the `(x, π)` block, determinacy and its exact model-level boundaries, the closed form, Table 5.1; E19–E21, E39–E41, E43 |
| [CTSimple](StickyPriceFiscal/CTSimple.lean) | 90 | §§5.7–5.7.1, (5.85)–(5.96), App. §1.12, and Fig. 5.10: scalar ODEs, the family (5.94), the valuation equation, the step example, the frictionless limit |
| [Sims](StickyPriceFiscal/Sims.lean) | 20 | §5.7.6, (5.118)–(5.125): Sims' model, exact linearisations, forward solutions, the Fisherian long run, the habit roots |
| [CTSurplus](StickyPriceFiscal/CTSurplus.lean) | 20 | §5.7.2, (5.97)–(5.104): the surplus impulse response, continuous-time Hansen–Sargent, `L(r) = β_s`, the s-shape; E45–E48 |
| [CTRules](StickyPriceFiscal/CTRules.lean) | 39 | §§5.7.3–5.7.5, (5.105)–(5.117), App. §1.13: bond prices, partial adjustment, (5.115), the `v*` elimination, the weighted identity, Laplace closed forms, the real diagonalisable matrix method; E25, E49, E51–E53 |
| [CTRulesEquilibrium](StickyPriceFiscal/CTRulesEquilibrium.lean) | 21 | §§5.7.3–5.7.5: existence and uniqueness of the rules equilibrium for every `α`, and the certified Fig. 5.11 and Table 5.2 numbers |
| [CTMatrixMethod](StickyPriceFiscal/CTMatrixMethod.lean) | 17 | App. §1.13 with complex and defective eigenvalues, given a Jordan decomposition |
| [Links](StickyPriceFiscal/Links.lean) | 25 | Links between the sections: innovations, discrete and continuous roots, the §5.5 model without rules as the §§5.1.2 and 5.2 models, fiscal-rule roots, ODE solutions |

## Modelling conventions

* **Expectations.** In §§5.1–5.6 random variables are `Ω → ℝ`, processes are indexed by `ℕ`, and
  every model equation holds state by state for an arbitrary `ExpectationSystem`. Results that
  move known factors through `E_t` assume `ExpectationSystem.PullOut`. Counterexamples under
  genuine uncertainty use the coin-flip tree (`ExpectationsFiniteTree.coinSystem`) or, for
  shocks that recur at every date, `PolicyRules.truncSystem`. The innovation `ΔE_{t+1}` is
  `SharedTools.innov`; statements in §§5.1–5.4 write `E_{t+1} − E_t` explicitly, which is the same
  by `SharedTools.innov_apply`.
* **Equilibrium and determinacy.** An equilibrium is a bounded adapted solution from given
  predetermined values: the real value of nominal debt `b_0 = v_{−1} + i_{−1}` in §5.1.2
  (`FiscalNK.Eqm`), pre-sample debt and bond price in §5.2 (`LongTermDebt.LTD`), initial inflation
  and debt in §5.5 (`PolicyRules.RedEquil`). "Determinate" means exactly one equilibrium for every
  bounded adapted forcing and initial condition; in §5.5 at model level it means for every shock
  process with the model's own AR(1) parameters (`PolicyRules.ModelDeterminate`). Where the book
  appeals to "debt cannot explode", the Lean statements separate boundedness from the
  transversality condition (`SharedTools.TVC`), since they differ at `ρ = 1`.
* **Two-sided moving averages.** Time starts at 0, so the infinite past of (5.5) is replaced by
  one pre-sample term `λ₁^{−t}K` with `K` known at date 0, and moving averages of shocks start
  from zero pre-sample states (`TwoSidedMA.piMA`, `SurplusProcess.ma`).
* **Long-term debt.** The model uses the exact first-order weight `ω̃ = ω/(1 + i)` of App. (1.22),
  not the `ω` of (1.24) (E23). In §5.5 the parameter `omega` of `PolicyRules.Params` is documented
  as this weight, and the book's parameters set it to `0.9` (`PolicyRules.bookRules`).
* **Continuous time.** Paths are functions `ℝ → ℝ` after a date-0 shock: the model holds as exact
  `HasDerivAt` equations on `(0, ∞)`, paths are continuous on `[0, ∞)` with the right limits as
  initial values, and the `dε`, `dδ` terms are the jumps at date 0. Infinite-horizon integrals are
  Bochner integrals over `(0, ∞)` with proved integrability. Instantaneous debt is predetermined,
  so the price level does not jump (`CTSimple.IsCTEquilibrium`).
* **Numbers.** Printed figure and table values are proved as rational enclosures by exact
  arithmetic (`norm_num`, `nlinarith`), never by floating-point evaluation.
* **Explicit hypotheses.** Hypotheses the book leaves implicit are stated in each theorem:
  `σ, κ > 0`, `0 < β < 1`, `0 < ρ < 1` for determinacy, `r > 0`, bounded forcing, `0 ≤ ω̃ < 1`,
  `0 < α < 2` and `|ρη| < 1` for the surplus process, `|η_i|, |η_s| < 1`, and the conditions
  listed in [corrections](docs/corrections.md).

## Relation to the Woodford projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects (the first three from `Woodford/ReturnOfMonetaryRules`,
`ForwardSolution` from the Woodford Chapter 2 and 3 projects), so the project builds on its own.
Nothing is imported from those projects. The chapter modules use `ExpectationSystem`,
`ExpectationSystem.PullOut`, `ExpectationSystem.Adapted`, `ExpectationSystem.IsAR1`,
`ExpectationSystem.forward_unique`, `ExpectationSystem.forwardSeries`, `ForwardSolution.Solves`,
`ForwardSolution.existsUnique_bounded`, the coin-flip tree, and the quadratic roots `root₁` and
`root₂` of `Determinacy`; the Schur–Cohn theorem itself (`schurStable_iff_roots`) is carried for
the later projects.

**`BKCopy` is a verbatim copy of the Woodford Chapter 4 general Blanchard–Kahn theorem.** It
consists of the three modules `InvariantSplit`, `GeneralBKForward` and `GeneralBK` of the
`Woodford/NeoWicksellianFramework` project, nested as sub-namespaces of
`Cochrane.StickyPriceFiscal.BKCopy`: the same 129 declarations in the same order, with the same
statements and proofs, only the namespace and `open` lines changed. The docstrings keep the
Woodford (2003) App. C.1 citations; the module docstring cites Cochrane App. §1.9, pp. 573–576.
`BKCopy.GeneralBKForward.fsolves_exists` uses the core `ExpectationSystem.E_tsum`, whose statement is the
same as in the Woodford core. The same three modules are also carried by the Galí Chapter 3
project (`Gali/BasicNewKeynesianModel`). `PolicyRules` uses the theorem in its counting form
(`BKCopy.GeneralBK.determinate_iff_count`), with `BKCopy.GeneralBK.determinate_of` for
sufficiency and `BKCopy.GeneralBK.not_determinate_of_unit` for the unit root; this replaces the
book's appeal to Blanchard and Kahn (1980) without proof.

Two further results are restated or related without a link theorem:
* `NKModel.hasDerivAt_E_exp`, the derivative of `ε ↦ E_t[exp(εX)]` used to linearise the Euler
  equation, is restated from the Woodford Chapter 2 project (`PriceLevelDetermination`, module
  `LogLinear`);
* the Woodford Chapter 4 project proves determinacy of its fiscal block (`Fiscal`, a `3 × 3`
  system with debt as the predetermined variable). `FiscalNK` does not restate it: it proves the
  determinacy of (5.15)–(5.16) directly, with the predetermined real value of debt
  `b_{t+1} = v_t + i_t`, by solving the debt root `ρ⁻¹` forward and the stable root `λ₁⁻¹`
  backward (`FiscalNK.eqm_determinate`).

Within the Cochrane projects, `CTSimple.integral_Ioi_shift` and `CTSimple.tvc_of_bounded` are
restated from the Chapter 3 project (`Generality`). App. §1.3 is also formalised in that project;
`LongTermDebt` proves its own versions of the portfolio return and its exact derivative, without
a link theorem.

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
