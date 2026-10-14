# Corrections to the source

Places where a claim in Chapter 5 of Galí (2015) is false, imprecise, or relies
on an unstated hypothesis, and where the Lean statement departs from the
printed one. In each case the Lean statement proves the stated version and
cites the original. Entries are recorded when found and revised if
formalisation shows the finding itself to be wrong. Lean names are relative to
the namespace `Gali.DiscretionCommitment`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| (26)–(27), p. 143 | With a distorted steady state, `x̂_0 = (1 − δ)Λ/ϑ − …` and the deterministic part of `x̂_t` is `Λ(1 − δ)δᵏ/ϑ`. | The deterministic term is `δ^{t+1}Λ/ϑ`, so `x̂_0 = δΛ/ϑ − κδu_0/(ϑ(1 − δβρ_u))` (`DistortedSS.commGap_eq26_corrected`, `DistortedSS.commGap_eq27_corrected`). The printed (26) holds only when `δ = 1/2` (`DistortedSS.printed_eq26_iff`); at `β = 1/2`, `κ = 1`, `ϑ = 8/21`, `Λ = 1`, `u ≡ 0` it gives `63/32` against the true `21/32` (`DistortedSS.printed_eq26_false`). Reading (27) with the deterministic term inside the sum gives a limit `Λ/ϑ ≠ 0`, contradicting the book's `lim x̂ = 0` (`DistortedSS.printed_eq27_sum_tendsto`). |
| App. 5.2, p. 156 | The price-setting sums start at `k = 1`. | They must start at `k = 0`: from `k = 1` the weights sum to `βθ ≠ 1` (`CostPushSources.weights_sum_k1`) and a path satisfying the printed rule and the Calvo index violates the NKPC (`CostPushSources.printed_priceSetting_breaks_nkpc`). With `k = 0` the NKPC follows (`CostPushSources.inflation_eq_markupGap`). |
| App. 5.2, p. 157 | `μ_t = +μ_{w,t} − (σ + φ)y_t + (1 + φ)a_t`, hence `u_t = −λ(μ_{w,t} − μ_w)`. | The sign of `μ_{w,t}` is negative; the printed line holds only if `μ_{w,t} = 0` (`CostPushSources.printed_markup_line_iff`). The cost-push shock is `u_t = +λ(μ_{w,t} − μ_w)` (`CostPushSources.nkpc_wageMarkup`, `CostPushSources.wageMarkup_costPush_pos`); the printed sign contradicts the derivation (`CostPushSources.printed_wage_costPush_contradiction`). |
| pp. 146–147 | Under discretion at the zero lower bound, `i_t = ρ` and `x = π = 0` from `t_Z + 1` on; the path (34) is the equilibrium. | Not the only bounded equilibrium: the deflationary steady state `π = −ρ`, `x = −(1 − β)ρ/κ`, `i = 0` forever (glued to (34) on `[0, t_Z]`) is a second bounded discretionary equilibrium with consistent multipliers (`ZLBDiscretion.deflation_discEq`, `ZLBDiscretion.deflation_bounded`, `ZLBDiscretion.deflation_ne_disc`). The book's path is the unique equilibrium in which `(x_t, π_t) → (0, 0)` (`ZLBDiscretion.disc_unique`). |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 136 | `δ ∈ (0, 1)`. | `δ > 0` always, but `δ < 1` iff `κ ≠ 0`; at `κ = 0`, `δ = 1` (`Commitment.del_lt_one_iff`, `Commitment.del_mem_Ioo_iff`, `Commitment.del_kappa_zero`). |
| pp. 133–135 | The commitment Lagrangian (stochastic). | The argument uses `E_t(ξ_t y) = ξ_t E_t y` for `ξ_t` known at `t`, which is not implied by linearity, monotonicity and iterated expectations alone. It is stated as a hypothesis (`Commitment.PullOut`), proved for perfect foresight and for every finite event tree (`Commitment.perfectForesight_pullOut`, `Commitment.finiteTree_pullOut`). Uniqueness of the stochastic optimum is in conditional mean square. |
| (10), p. 133 | The rule with `φ_π > 1` implements the discretionary equilibrium. | An iff for `φ_π ≥ 0`: for `0 ≤ φ_π ≤ 1` there is another bounded equilibrium (`Discretion.rule10_indeterminate`). |
| p. 138 | The implementing rule has the factor `(1 − σκ/α_x)`. | `(1 − σκ/ϑ)` (1st-edition notation) (`Commitment.dis_iff_rate_rho0`). |
| p. 138, fn. 6 | "See exercise 4.5." | Exercise 4.6 in the 2nd edition (`Commitment.rule_implements`). |
| p. 134 | "Differentiating the Lagrangian with respect to `y_t`". | With respect to `x_t` (`Commitment.FOC`). |
| p. 145 onward | `ε` for the drop in the natural rate. | Clashes with the demand elasticity `ε` in `ϑ = κ/ε`; renamed `η` (`ZLBDiscretion.natRate`). |
| p. 152 | Check `i_t ≥ 0` for every `t ≥ t_C + 1`; "4(t_C + 2) equations". | The infinitely many checks reduce to dates `t_C + 1` and `t_C + 2` (`ZLBCommitment.post_rate_nonneg`). The equation count holds only if (46) and `ξ_{2,t_C+1} = 0` are counted with (47) (`ZLBCommitment.equation_count`, `ZLBCommitment.algorithm_eq47`). |
| Exercise 5.1(b), p. 159 | `φ_π*` minimises the loss. | It is the unique global minimiser (`Ex5_1.lossFn_ge`); on the determinacy region `φ_π > 1` it is the minimiser only if `φ_π* > 1`, and otherwise there is none (`Ex5_1.ex5_1b_optimal`, `Ex5_1.ex5_1b_corner`). |
| Exercise 5.2(b)–(c), p. 160 | The optimal Markov policy beats discretion; commitment does better still. | Markov equals discretion exactly when `ρ_u = 0` (`Ex5_2.ex5_2b_objective`); commitment is strictly better than the optimal Markov policy for every `|ρ_u| < 1`, including `ρ_u = 0` (`Ex5_2.ex5_2c`). |
| Exercise 5.4(a), p. 161 | Period-by-period optimisation gives `x = −(κ/ϑ)π̃`. | Only when `E_t π̃_{t+1}` is taken as given; if `E_t π_{t+1}` is taken as given the condition is `ϑ(1 + βγ)x = −κπ̃` (`Ex5_4.period_foc_alt`). |
| Exercise 5.5, p. 162 | A unique bounded equilibrium with normal shocks. | With Gaussian shocks no equilibrium is bounded; uniqueness is among bounded deviations from the solution (`Ex5_5.ex5_5b_unique`). The optimal steady-state inflation `π̄* = −ρ − s z_{0.05}` can be negative (`Ex5_5.ex5_5a`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| App. 5.1 | "Small distortion" | Exact at the level of the second-order polynomial with `Φ = O(s)` (`LossAndCostPush.small_distortion_polynomial`); for actual utility at a fixed distorted steady state the neglected term is `Φ × O(s²)` (`LossAndCostPush.period_utility_small_distortion`) |
| §5.2 | `ρ_u ∈ [0, 1)` | Most results hold for every `ρ_u < 1` (`Discretion.discretionEq_iff_msv`) |
| §5.2.2, §5.3 | Optimality of the commitment path | Deterministic: optimal iff first-order conditions, existence and uniqueness for every bounded shock path (`Commitment.Det.existsUnique_optimal`, `DistortedSS.det_commitment_optimal`) |
| §5.4.2 | Commitment at the zero lower bound | KKT sufficiency and uniqueness (`ZLBCommitment.kkt_optimal`, `ZLBCommitment.optimal_unique`); necessity and existence for arbitrary shocks are not claimed |
| Exercises 5.3, 5.4(b) | Commitment problems | Deterministic, over bounded paths; first-order conditions necessary and sufficient |
