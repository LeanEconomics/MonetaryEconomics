# Corrections to the source

Places where a claim in Chapter 6 of Galí (2015) is false, imprecise, or relies
on an unstated hypothesis, and where the Lean statement departs from the
printed one. In each case the Lean statement proves the stated version and
cites the original. Entries are recorded when found and revised if
formalisation shows the finding itself to be wrong. Lean names are relative to
the namespace `Gali.StickyWagesPrices`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| p. 174 | `ỹ = π^p = π^w = 0` is a solution only when `ωⁿ` is constant and `φ_y = 0`, and `v = rⁿ`. | With `ω̃_{−1} = 0`, the zero path solves (24) iff `ω̂ⁿ ≡ 0` and `v = r̂ⁿ = rⁿ − ρ`, for every `φ_y`: a constant `ωⁿ` forces `a ≡ 0`, so the `φ_y = 0` hypothesis is redundant (`System.zeroPath_iff_primitives`, `System.zeroPath_solves_any_phiY`); with `v = rⁿ` and `ρ ≠ 0` the zero path is not a solution (`System.zeroPath_fails_v_eq_rn`). |
| pp. 188–190 | The second-order expansion of period utility written with `−U_nN(…)`. | The first display on p. 188 has `+U_nN`, which is correct; the next three displays flip the sign, inconsistently with it and with `−U_n/U_c = MPN(1 − Φ)`. The normalised display on p. 190 is correct (`Welfare.secondOrderUtility_eq`). |
| (16), p. 171 | `ωⁿ = log(1 − α) + ψ_wa a − μ^p`. | The constant `−αψ_y/(1 − α)` is missing; it is nonzero in general (`GapForm.natural_allocation_iff`, `GapForm.natWage_constant_ne_zero`). Harmless for the dynamics, which use only `Δωⁿ` and gaps. |
| Lemma 2, p. 192 | `∑βᵗ var_j w_t(j) = θ_w/((1 − θ_w)(1 − βθ_w)) ∑βᵗ(π^w_t)²` (and the price version). | Exact only without inherited dispersion; with initial dispersion `V₀` a term `θV₀/(1 − βθ)` is added (`Welfare.lemma2_inherited`, `Welfare.lemma2_printed_fails_with_inherited`). The exact versions are in the change of the cross-sectional mean (`WageDispersion.wage_lemma2_calvo`, `WageDispersion.wage_lemma2_calvo_inherited`). |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 174 | Determinacy iff `φ_p + φ_w + φ_y(1 − β)/Θ_y · (1/λ_p + 1/λ_w) > 1` (stated without proof; fn. 2 cites the literature). | Proved in full, in both the determinacy and the eigenvalue form (`Determinacy4.determinacy_iff`, `Determinacy4.eigenvalues_iff`). The proof needs only `κ_p, κ_w ≥ 0` (`Determinacy4.Dyn.determinate_iff`), slightly weaker than `φ ≥ 0`. |
| Fig. 6.1, p. 175 | The region below the frontier is labelled "Indeterminacy". | It also contains points where no bounded equilibrium exists: at `β = 9/10`, `σ = 3/4`, `α = 3/4`, `φ = 3`, `λ_p = 1/40`, `λ_w = 6/5`, `φ_p = 2/25`, `φ_w = 31/50`, `φ_y = 7/100` all four eigenvalues lie inside the unit circle and there is no bounded solution with `ω̃_{−1} = 1` (`Determinacy4.exNE_lhs`, `Determinacy4.exNE_no_root`, `Determinacy4.exNE_no_bounded_solution`). At the baseline calibration the failure is indeed multiplicity (`Determinacy4.exBase_two_roots`, `Determinacy4.exBase_multiplicity`). |
| p. 184 | `π̄ = ỹ = 0` is optimal "since it satisfies the optimality conditions (34) and (35)". | (34)–(35) are necessary conditions only (`OptimalPolicy.composite_path_satisfies_34_35`). The claim is true and proved by a separation argument: the loss splits into a `(ỹ, π̄)` block and a policy-invariant block in `π^w − π^p` (`OptimalPolicy.Stoch.composite_targeting_optimal`, `OptimalPolicy.Det.composite_targeting_existsUnique`). |
| (36), p. 184 | `π̄ = βE_tπ̄_{t+1} + κỹ` "independently of parameter values". | `κ` is defined only when `κ_p = κ_w`. In general the slope is `κ̄ = λ_pλ_wΘ_y/(λ_p + λ_w)`, strictly between `κ_p` and `κ_w` when they differ (`GapForm.kappaBar_eq`, `GapForm.kappaBar_strictly_between`). |
| p. 169 | `mrs_{t+k|t} = mrs_{t+k} − ε_wφ(w*_t − w_{t+k})`. | Exactly there is an extra `−φ log Δ_w`, of second order with zero derivative, which justifies the book's first-order claim (`WageSetting.log_mrsReset`, `WageSetting.mrs_correction_first_order`). |
| App. 6.1, p. 189 | `n̂(j) − n̂ = −ε_w ŵ(j)`, hence `∫n̂(j)² = n̂² + ε_w² var_j w`. | The step drops `−log Δ_w`; the identity holds to third order only when `n̂` is itself first order, an explicit hypothesis (`WageDispersion.integral_sq_employment`, `WageDispersion.integral_sq_employment_second_order`). |
| (11), p. 168 | The union's first-order condition. | Necessary and sufficient with a unique optimum, without concavity of the objective (it is unimodal), from primitive bounds (`WageSetting.union_isMaxOn_iff_foc`, `WageSetting.primitives_of_union`). |
| p. 180 | Flexible wages as the limit `λ_w → ∞`. | Stated as the limiting model with a constant wage markup (`LimitingCases.flexWage_nkpc`, `LimitingCases.flexWage_optimal`); the limit itself is proved separately (`LimitingCases.lambdaW_tendsto_atTop`, `LimitingCases.wageWeight_tendsto_zero`). The book also redefines `κ_w` here, clashing with (20). |
| p. 180 | Strict price (wage) inflation targeting is suboptimal unless wages (prices) are flexible. | Proved as: for every sticky-wage (sticky-price) calibration there is a technology-shock path for which the strict-targeting path is strictly worse than another feasible path (`LimitingCases.strict_price_targeting_suboptimal_model`, `LimitingCases.strict_wage_targeting_suboptimal_model`); not for every shock path. |
| Table 6.1, p. 186 | Losses. | Recomputed from the printed standard deviations they are lower in every technology column, and the order of flexible composite and flexible wage targeting is reversed (`Calibration.table61_losses`, `Calibration.table61_flexible_swap`); consistent with truncated standard deviations. |
| p. 191; p. 190 | Displays with a stray `dj` / `∫…dj`. | Typos. |
| p. 189 | `var_i{w_t(i)}`. | `var_j`. |
| Exercise 6.2(b), p. 196 | — | Part (b) asks no question; it introduces the wage rule used in (c)–(d) (`Ex6_2.WageInAdvance`). |
| Exercise 6.4(f), p. 198 | `y*_t`; "`μ` infinitesimally small". | `y*_t` is read as `yᵉ_t` and `μ = 0` is set exactly (`Ex6_4.discretion_iid_iff`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| (15), p. 170 | `λ_w > 0` | Needs `θ_w > 0`, `βθ_w < 1`, `1 + ε_wφ > 0` (`WageInflation.lambdaW_pos`) |
| pp. 181–184 | Optimality under uncertainty | The pull-out property `E_t(ay) = aE_t y` for date-`t` `a`, true for perfect foresight and every finite event tree (`ExpectationSystem.PullOut`, `ExpectationsFiniteTree.finiteTree_pullOut`); the composite-targeting result does not need it |
| p. 182 | The implementing rule is determinate | Proved from the p. 174 theorem for `φ_p > 1` (`OptimalPolicy.Stoch.ruleDeterminate_book`, `OptimalPolicy.Stoch.rule_implements_book`); the converse for `φ_p ≤ 1` is proved when `κ_p = κ_w` (`OptimalPolicy.Stoch.ruleDeterminate_iff`) |
| §6.4 | Existence of the optimal path for general technology shocks | Not claimed; first-order conditions are shown sufficient, and necessary when a solution exists (`OptimalPolicy.Det.isOptimal_iff_foc`) |
