# Corrections to the source

Places where a claim in Chapter 4 of Galí (2015) is false, imprecise, or relies
on an unstated hypothesis, and where the Lean statement departs from the
printed one. In each case the Lean statement proves the stated version and
cites the original. Entries are recorded when found and revised if
formalisation shows the finding itself to be wrong. Lean names are relative to
the namespace `Gali.MonetaryPolicyDesign`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| p. 108 | The forward-looking rule gives `A_F` with (2,2) entry `β − κφ_π/σ`. | The correct entry is `β + κ(1 − φ_π)/σ` (`RuleForward.AF_one_one`, `RuleForward.AF_ne_AFprinted`). Conditions (17)–(18) characterise determinacy for the corrected matrix (`RuleForward.determinate_iff_17_18`). At `σ = κ = 1`, `β = 1/2`, `φ_π = 3`, `φ_y = 0` the true system is determinate but the printed matrix fails Schur–Cohn (`RuleForward.printed_verdict_differs`, `RuleForward.printed_determinacy_differs`), and the printed system has a bounded nonzero solution that is no equilibrium (`RuleForward.printed_solution_not_equilibrium`). |
| p. 111 | The relative weight of output-gap fluctuations is increasing in `α`. | The absolute coefficient `σ + (φ+α)/(1−α)` is increasing (`Welfare.gapCoeff_strictMonoOn_alpha`), but the weight relative to inflation, `κ/ε`, has the sign of `(1 − σ) − (σ + φ)(ε − 1)` for every `α`: it is strictly decreasing iff `(σ + φ)(ε − 1) > 1 − σ`, which covers the baseline and every `σ ≥ 1` (`Welfare.relWeight_strictAntiOn_alpha`, `Welfare.relWeight_strictMonoOn_alpha`). Baseline: `103/1800` at `α = 0` falling to `103/7560` at `α = 0.4` (`Welfare.relWeight_baseline`, `Welfare.relWeight_not_increasing_alpha`). |
| Exercise 4.1(b), p. 121 | `A_T` has both eigenvalues outside the unit circle iff (14). | Inside: both eigenvalues lie inside the unit circle iff (14) (`Ex4_1.AT_eigenvalues_inside_iff`). Since `0 < det A_T < 1` they are never both outside, and the printed equivalence holds exactly when (14) fails (`Ex4_1.AT_not_both_outside`, `Ex4_1.printed_iff_iff_not14`, `Ex4_1.printed_ex4_1b_false`). |
| Exercise 4.6, p. 125 | Under `i = rⁿ + φ_p p̂` there is a unique stationary equilibrium iff `φ_p > 0`. | Over all real `φ_p` the equilibrium is determinate iff `φ_p > 0` or `φ_p < φ* = −2 − 4σ(1+β)/κ` (`Ex4_6.determinate_iff`, `Ex4_6.book_claim_false`). For `φ_p < φ*` there is one stable root in `(−1, 0)` and the unique equilibrium oscillates (`Ex4_6.determinate_of_lt_phiStar`); at the baseline `φ_p = −100` is determinate. The book's claim holds for `φ_p ≥ φ*`, in particular for all `φ_p ≥ 0` (`Ex4_6.determinate_iff_pos_of_ge`). |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 103 | `ỹ_t = 0` for all `t` implies `π_t = 0` for all `t`. | Only along bounded equilibria (`OptimalPolicy.infl_zero_of_gap_zero`). Under perfect foresight `ỹ ≡ 0`, `π_t = β^{−t}`, `i_t = rⁿ_t + β^{−(t+1)}` solves both equations (`OptimalPolicy.unbounded_counterexample`). |
| p. 110 | Determinacy for `φ_π` "no greater than" `1 + 2σ(1+β)/κ`. | The bound is strict: at equality `−1` is an eigenvalue and the system is indeterminate (`RuleForward.boundary_eigenvalue_neg_one`, `RuleForward.not_determinate_at_boundary`, `RuleForward.determinate_forward_phiy_zero`). |
| p. 99 | (1)–(2) hold "for all `i`". | On the continuum the optimum is unique up to null sets (`Efficient.Goods.planner_optimal_iff`); for finitely many goods with positive weights, for every `i` (`Efficient.Finite.planner_optimal_iff_finite`). |
| Lemma 2, p. 119 | `∑βᵗ var_i p_t(i) = θ/((1−βθ)(1−θ)) ∑βᵗπ_t²`. | Exact when inflation is measured by the change in the cross-sectional mean of log prices, `Δm_t`, with no inherited dispersion (`Welfare.lemma2_calvo`); with inherited dispersion `V₀` a term `θV₀/(1−βθ)` is added (`Welfare.lemma2_calvo_inherited`). The relation to `π` is second order: `π − Δm = O(s²)`, `π² − Δm² = O(s³)` (`Welfare.inflation_sub_meanChange`, `Welfare.inflation_sq_sub_meanChange_sq`). |
| Table 4.1, p. 113 | Standard deviations and losses. | All 32 entries follow from the closed forms when truncated to the printed digits; eight would differ under rounding (e.g. technology, `φ_π = 1.5`, `φ_y = 0`: `sd(π) = 0.3458`, printed `.34`) (`SimpleRules.table41_truncated`). |
| Exercise 4.2(c), p. 121 | Find the `φ_π` that minimises the variance of inflation. | A unique interior minimiser exists iff `σ var ξ · h(1) < κ var r̂`; otherwise there is no minimiser on the determinacy region `φ_π > 1` (`Ex4_2.ex4_2c_interior`, `Ex4_2.ex4_2c_corner`). The first-order condition is a quartic; a closed form exists only for `ρ_r = 0`, `φ* = κ var r̂/(σ var ξ)` (`Ex4_2.ex4_2c_iid`). |
| Exercise 4.5(e), p. 124 | The firm's objective deflates by `P_{t+1}`. | Real profit at date `t` is deflated by `P_t` (`Ex4_5.sticky_objective_eq`). |
| Exercise 4.5(d), (g), pp. 124–125 | The optimal policy satisfies the Friedman rule. | With `log(M/P)` utility there is no equilibrium at the Friedman rule and welfare is unbounded as `i → 0⁺`, so no optimal policy exists (`Ex4_5.not_equilibrium_at_friedman`, `Ex4_5.policy_not_optimal`). For every nominal rate, `φ_a = 1`, `φ_v = 0` is the unique best choice (`Ex4_5.stabilization_optimal`) and replicates the flexible-price allocation (`Ex4_5.sticky_replicates_flex`). |
| Exercise 4.4(c), p. 123 | The money rule implements the optimal allocation. | Existence is proved (`Ex4_4.moneyRule_equilibrium`). Uniqueness under the money rule is the same open `3 × 3` determinacy question as Chapter 3, fn. 14; it is not yet claimed (`Ex4_4.MoneyRuleUniqueness`). |
| Table 4.2, p. 119 | Statistics under a money-growth rule. | Not formalised: it needs the solution of the `3 × 3` money-rule system. |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| p. 100 | The firm's pricing rule | Derived as the unique global optimum of the firm's problem (`Distortions.firm_optimal_iff`) |
| App. 4.1 | "`≃`" in the welfare approximation | An exact completing-the-square identity plus `O(s³)` along one-parameter families (`Welfare.secondOrderUtility_eq`, `Welfare.period_utility_second_order`) |
| App. 4.1 | Separable utility, efficient steady state | `U = (u(C) + w(N))e^z`; `−U_n/U_c = MPN` at the steady state (`Welfare.efficiency_iff`) |
| (15), p. 106 | A "permanent change in inflation" | `π_t → π̄` and `E_tπ_{t+1} → π̄`; then `i_t − rⁿ_t` converges (`RuleTaylorPrinciple.tendsto_rate_of_tendsto_infl`) |
| p. 113 | Stationary variances of AR(1) shocks | An abstract second-moment functional, satisfied by Mathlib's `variance` (`SimpleRules.variance_isSecondMoment`) |
| Exercise 4.2 | `ξ` i.i.d. and uncorrelated with `r̂` | `IsAR1 0` for expectations, zero covariance for variances |
