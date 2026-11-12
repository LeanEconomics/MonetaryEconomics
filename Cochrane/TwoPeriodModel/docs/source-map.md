# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, "A two-period model"
(pp. 4–19). Each formal claim is listed with its Lean name, relative to the namespace
`Cochrane.TwoPeriodModel`. Page numbers are book pages. The book has no labelled propositions,
so rows are keyed by equation number, table, box or page. Rows follow the book section by
section, and each heading names the modules that formalise the section: §§1.1–1.9, then the
household problem, the infinite horizon, the truncation and the regressions, then the links to
the Woodford projects, then the shared tools. Every statement holds for an arbitrary
`ExpectationSystem`, so under perfect foresight and under uncertainty, except those of
`TidyR6HouseholdMeasure` and the population rows of `TidyR6Regression`, which hold almost
surely on a probability space. Date-0 quantities are
`Known` at date 0, and results that take them out of `E₀` assume `ExpectationSystem.PullOut`.
"The price level is determined" means that there is exactly one equilibrium triple
(`TwoPeriod.Equilibrium`). The shared core (`Determinacy`, `Expectations`,
`ExpectationsFiniteTree`, `ForwardSolution`) is cited where a row uses it.

## §1.1–§1.2 The last day; intuition, pp. 4–7 (TwoPeriod)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (1.1), p. 4 | "cash printed in the morning must be soaked up by taxes": `B₀ = P₁s₁` is (1.1) `B₀/P₁ = s₁` when `P₁ ≠ 0` | `TwoPeriod.lastDay_iff` |
| Cochrane (1.1), p. 4 | with `B₀ > 0` and `s₁ > 0` there is exactly one positive price level, `P₁ = B₀/s₁` | `TwoPeriod.lastDay_existsUnique`, `TwoPeriod.lastDay_eq` |
| Cochrane (1.1), p. 4 | with `s₁ ≤ 0` no positive price level solves (1.1) (E3) | `TwoPeriod.lastDay_none` |
| Cochrane p. 5 | money left over after taxes, `M₁ = B₀ − P₁s₁`, is positive ("too much money chasing too few goods") iff `P₁ < B₀/s₁`, and negative iff `P₁ > B₀/s₁` | `TwoPeriod.excess_money_iff`, `TwoPeriod.money_shortage_iff` |
| Cochrane p. 4; pp. 17–18 | with a proportional tax, `P₁s₁ = τP₁y₁`, the real surplus `s₁ = τy₁` does not depend on `P₁` | `TwoPeriod.propTax_real` |

## §1.3 The two-period model and present value, pp. 7–8 (TwoPeriod)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 8 | a variable is known at date `t` when `E_t x = x`; constants and expectations `E_t x` are known at `t`; known at `s` implies known later; known variables are closed under sums, differences and multiples, and under pull-out under products, reciprocals and quotients | `TwoPeriod.Known`, `TwoPeriod.known_const`, `TwoPeriod.known_E`, `TwoPeriod.known_mono`, `TwoPeriod.known_add`, `TwoPeriod.known_sub`, `TwoPeriod.known_smul`, `TwoPeriod.known_mul`, `TwoPeriod.known_inv`, `TwoPeriod.known_div` |
| Cochrane (1.1)/(1.4), pp. 4, 8 | the date-1 valuation equation `B₀/P₁ = s₁`, state by state | `TwoPeriod.Valuation1` |
| Cochrane (1.2), p. 8 | the date-0 flow condition `B₋₁ = P₀s₀ + Q₀B₀` | `TwoPeriod.Flow0` |
| Cochrane (1.3), p. 8 | `Q₀ = 1/(1 + i₀) = βE₀(P₀/P₁) = (1/R)E₀(P₀/P₁)` | `TwoPeriod.BondPrice0`, `TwoPeriod.rate`, `TwoPeriod.bondPrice_eq_inv_one_add_rate`, `TwoPeriod.bondPrice_R` |
| Cochrane p. 8, unnumbered display after (1.3) | `B₋₁/P₀ = s₀ + βE₀(1/P₁)B₀` | `TwoPeriod.flow_real` |
| Cochrane (1.5), p. 8 | the valuation equation `B₋₁/P₀ = s₀ + βE₀s₁` and the present value `s₀ + βE₀s₁`, known at date 0 when `s₀` is | `TwoPeriod.Valuation0`, `TwoPeriod.pv`, `TwoPeriod.known_pv` |
| Cochrane (1.2)–(1.5), p. 8 | bond sales raise nominal revenue `Q₀B₀ = P₀βE₀s₁`; (1.2), (1.3) and (1.4) imply (1.5); given (1.3)–(1.4), (1.2) and (1.5) are equivalent | `TwoPeriod.revenue_eq`, `TwoPeriod.valuation0_of_flow`, `TwoPeriod.flow_iff_valuation0` |
| Cochrane pp. 7–8 | the equilibrium of the two-period model: positive `P₀, P₁`, `P₀` known at 0, (1.2), (1.3), (1.4) | `TwoPeriod.Equilibrium` |
| Cochrane (1.4)–(1.5), p. 8 | `P₁ = B₀/s₁` and `P₀ = B₋₁/(s₀ + βE₀s₁)` | `TwoPeriod.price1_eq`, `TwoPeriod.price0_eq` |
| Cochrane pp. 7–8 | the price level is determined: `(P₀, P₁, Q₀)` is an equilibrium iff it is given by the formulas, and there is exactly one, when `B₋₁, B₀ > 0`, `s₁ > 0` and `s₀ + βE₀s₁ > 0` | `TwoPeriod.equilibrium_iff`, `TwoPeriod.equilibrium_existsUnique` |
| Cochrane (1.1), p. 4; (1.5), p. 8 | with `s₁ ≤ 0` in some state, or a nonpositive present value, there is no equilibrium (E3) | `TwoPeriod.no_equilibrium_of_s1_nonpos`, `TwoPeriod.no_equilibrium_of_pv_nonpos` |
| Cochrane box p. 7; p. 8 | "a higher discount rate, lower `β`, can lead to inflation with no change in surpluses": `P₀` is strictly decreasing in `β` | `TwoPeriod.price0_strictAnti_beta` |
| Cochrane p. 8 | bad news about future surpluses raises `P₀`; `P₀` depends on `(s₀, s₁)` only through `s₀ + βE₀s₁`; any deficit `s₀` is compatible with any price level | `TwoPeriod.price0_strictAnti_Es1`, `TwoPeriod.price0_eq_of_pv_eq`, `TwoPeriod.price0_any_level` |
| Cochrane p. 8 | under genuine uncertainty: in a coin-flip economy an equilibrium exists, `P₁` is `1/2` after heads and `1` after tails, and `P₀ = 4/3` | `TwoPeriod.coin_equilibrium`, `ExpectationsFiniteTree.coinSystem` |

## §1.4 Monetary policy, fiscal policy and inflation, pp. 9–10 (MonetaryFiscal)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (1.8), p. 9 | `B₋₁/P₀ = s₀ + Q₀B₀/P₀ = s₀ + βE₀(P₀/P₁)B₀/P₀ = s₀ + βE₀s₁` | `MonetaryFiscal.eq_1_8` |
| Cochrane p. 9 | bond sales raise real revenue `Q₀B₀/P₀ = βE₀s₁`, whatever `B₀` | `MonetaryFiscal.revenue_invariant` |
| Cochrane p. 9 | share split: selling `κB₀` with unchanged surpluses gives the unique equilibrium `(P₀, κP₁, Q₀/κ)`; doubling `B₀` doubles `P₁` and halves `Q₀` | `MonetaryFiscal.shareSplit_equilibrium`, `MonetaryFiscal.shareSplit_unique`, `MonetaryFiscal.doubling` |
| Cochrane (1.3), p. 8; p. 9 | `i₀` is strictly decreasing in `Q₀`, so the share split raises the nominal rate | `MonetaryFiscal.rate_strictAnti`, `MonetaryFiscal.shareSplit_rate_rises` |
| Cochrane p. 10 | an interest-rate target: `B₀` endogenous, `Q₀ = 1/(1 + i₀)`; the flat supply curve `B₀ = (1 + i₀)P₀βE₀s₁` | `MonetaryFiscal.TargetEquilibrium`, `MonetaryFiscal.target_bond_demand` |
| Cochrane p. 10 | inflation is stable and determinate under a target, even a peg: for every `i₀ > −1` exactly one `(P₀, B₀, P₁)` | `MonetaryFiscal.target_existsUnique`, `MonetaryFiscal.determinate_under_peg` |
| Cochrane (1.9), p. 10 | `E₀(P₀/P₁) = 1/(β(1 + i₀))`, "really, by lowering `E(1/P₁)`" | `MonetaryFiscal.expected_inflation`, `MonetaryFiscal.E0_invP1` |
| Cochrane p. 10 | the Fisherian response: a higher `i₀` leaves `P₀` and raises `P₁` in every state | `MonetaryFiscal.fisherian_two_period` |
| Cochrane (1.10), p. 10 | `(B₀/P₀)(E₁ − E₀)(P₀/P₁) = (E₁ − E₀)s₁` | `MonetaryFiscal.innov`, `MonetaryFiscal.unexpected_inflation` |
| Cochrane p. 10 | (1.9)–(1.10) completely determine expected and unexpected inflation; without fiscal news inflation equals expected inflation | `MonetaryFiscal.inflation_decomposition`, `MonetaryFiscal.no_fiscal_news` |

## §1.5 Fiscal policy debt sales, pp. 10–13, Table 1.1 (DebtSales)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (1.5), p. 8 | in every equilibrium `P₀ = B₋₁/(s₀ + βE₀s₁)` | `DebtSales.price0_formula` |
| Cochrane (1.11), p. 11 | raising `B₀` and `s₁` in proportion leaves `P₁` | `DebtSales.equityIssue_price1` |
| Cochrane (1.12), p. 11 | the equity issue multiplies the real revenue from debt sales by `κ` | `DebtSales.equityIssue_revenue` |
| Cochrane p. 11 | the extra revenue can lower `P₀`, or fund a deficit `s₀ − (κ − 1)βE₀s₁` with `P₀` unchanged | `DebtSales.equityIssue_lowers_price0`, `DebtSales.equityIssue_funds_deficit` |
| Cochrane Table 1.1, "Borrow", pp. 11–12 | lowering `s₀` by `Δ` and raising `E₀s₁` by `−Δ/β` leaves `P₀`; the value of debt rises by `−Δ` | `DebtSales.borrow_price0`, `DebtSales.borrow_value_rises` |
| Cochrane Table 1.1, "Borrow", p. 12 | `P₁` is unchanged in every state iff `B₀′s₁ = B₀s₁′`; scaling `B₀` and `s₁` by `c = 1 − Δ/(βE₀s₁)` implements the strategy with `P₀, P₁, Q₀` unchanged (E1 addendum) | `DebtSales.borrow_keeps_price1_iff`, `DebtSales.borrow_implementable` |
| Cochrane p. 12 | `(B₀ + ΔB₀)/P₁ = s₁ − RΔs₀`, not the printed `s₁ + RΔs₀` (E1) | `DebtSales.borrow_debt_corrected`, `DebtSales.borrow_printed_fails` |
| Cochrane Table 1.1, "Inflate", pp. 11–12 | `P₀` rises; the value of debt is unchanged; `B₋₁/P₀` falls by exactly the fall in `s₀` | `DebtSales.inflate_price0_rises`, `DebtSales.inflate_value_unchanged`, `DebtSales.inflate_real_debt_falls_by_deficit` |
| Cochrane Table 1.1, "AR(1)", pp. 11–12 | `P₀` rises more than under "Inflate"; the value of debt falls | `DebtSales.ar1_price0_rises_more`, `DebtSales.ar1_value_falls` |
| Cochrane Table 1.1, column `B₀/P₁`, p. 11 | the expected value of maturing debt changes with expected `s₁` | `DebtSales.maturing_value_change` |
| Cochrane p. 12 | the s-shaped surplus: a deficit with a rising value of debt needs higher expected surpluses | `DebtSales.sShape_two_period` |
| Cochrane pp. 11–12 | a completely steady `P₀` despite a deficit iff `Δs₀ + βΔE₀s₁ = 0` | `DebtSales.steady_price0_iff` |

## §1.6–§1.7 Debt reactions and a price-level target; fiscal policy changes monetary policy, pp. 13–15 (PriceLevelTarget)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (1.13), p. 13 | under `s₁ = B₀/P₁*`, a positive `P₁` solves (1.4) iff `P₁ = P₁*`; every equilibrium has `P₁ = P₁*` | `PriceLevelTarget.rule_price1_iff`, `PriceLevelTarget.rule_price1` |
| Cochrane p. 14 | `B₋₁/P₀ = s₀ + βE₀(B₀/P₁*) = s₀ + βB₀E₀(1/P₁*)` | `PriceLevelTarget.rule_pv`, `PriceLevelTarget.rule_valuation` |
| Cochrane pp. 13–14 | under the rule there is exactly one equilibrium, with `P₀ = B₋₁/(s₀ + βB₀E₀(1/P₁*))` | `PriceLevelTarget.rule_existsUnique`, `PriceLevelTarget.rule_price0` |
| Cochrane p. 14 | finance a deficit by borrowing (`P₀`, `P₁` unchanged), by inflating (sell no more debt: `P₀` rises) or by super-inflating (sell less: `s₁` falls, `P₀` rises more) | `PriceLevelTarget.rule_borrow`, `PriceLevelTarget.rule_inflate`, `PriceLevelTarget.rule_superinflate` |
| Cochrane box p. 14; p. 15 | larger debt `B₀` leaves `P₁ = P₁*` and lowers `P₀` immediately | `PriceLevelTarget.rule_price0_strictAnti_B0` |
| Cochrane p. 15 | under the rule and a target `i₀`: `P₀ = 1/((1 + i₀)βE₀(1/P₁*))`, and the equilibrium `(P₀, B₀, P₁)` is unique | `PriceLevelTarget.RuleTargetEquilibrium`, `PriceLevelTarget.rule_target_price0`, `PriceLevelTarget.rule_target_existsUnique` |
| Cochrane box p. 14; p. 15 | "higher interest rates lower inflation, immediately", with an expected future fiscal tightening | `PriceLevelTarget.rule_higher_rate_lowers_price0`, `PriceLevelTarget.rule_higher_rate_fiscal_tightening` |
| Cochrane p. 15 | under the rule the debt demand curve is flat and revenue rises with `B₀`; with fixed surpluses demand is unit-elastic | `PriceLevelTarget.rule_flat_demand`, `PriceLevelTarget.rule_revenue`, `PriceLevelTarget.unit_elastic` |

## §1.8–§1.9 Budget constraints, active and passive policy, and a debt rule, pp. 15–19 (ActivePassive)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (1.15), p. 16 | the budget constraint `B₀ = P₁s₁ + M₁` holds at every price level | `ActivePassive.budget_any_price` |
| Cochrane (1.14)–(1.15), p. 16 | (1.14) is the budget constraint plus `M₁ = 0`; off equilibrium the constraint holds with `M₁ ≠ 0` | `ActivePassive.valuation_of_zero_money`, `ActivePassive.money_zero_of_valuation`, `ActivePassive.money_nonzero_off_equilibrium` |
| Cochrane p. 17 | the equilibrium set of a surplus rule `s(P₁)` | `ActivePassive.eqmSet` |
| Cochrane (1.16), p. 17 | under the passive rule `s₁ = B₀/P₁` every `P₁ > 0` is an equilibrium; the set is uncountable | `ActivePassive.passive_eqmSet`, `ActivePassive.passive_indeterminate` |
| Cochrane (1.16), p. 18 | the passive tax rate `τ₁ = B₀/(P₁y₁)` falls as `P₁` rises | `ActivePassive.passive_taxRate`, `ActivePassive.passive_taxRate_strictAnti` |
| Cochrane p. 17 | a single crossing gives at most one equilibrium; a continuous, weakly increasing rule positive somewhere gives exactly one; a fixed surplus is active | `ActivePassive.active_unique_of_strictAnti`, `ActivePassive.active_existsUnique`, `ActivePassive.fixed_surplus_active` |
| Cochrane pp. 17–18 | a proportional tax `s₁ = τy₁ − g₁ > 0` is active | `ActivePassive.propTax_active` |
| Cochrane p. 17 | "or multiple crossings": `s(P) = B₀(3 − P)/2` has the two equilibria `1` and `2` | `ActivePassive.multiple_crossings` |
| Cochrane p. 18 | three sources of variation in the value of debt, and the split of its innovation | `ActivePassive.value_decomp`, `ActivePassive.value_decomp_innov` |
| Cochrane pp. 18–19 | the rule `s₁ = αB₀/P₁* + γ(B₀/P₁ − B₀/P₁*)`; its equilibria solve `(1 − γ)B₀/P₁ = (α − γ)B₀/P₁*`; `α = γ = 1` is passive; `γ = 1`, `α ≠ 1` has no equilibrium | `ActivePassive.gammaRule`, `ActivePassive.gamma_eqmSet`, `ActivePassive.gamma_eqmSet_passive`, `ActivePassive.gamma_eqmSet_empty` |
| Cochrane p. 18 | with `α = 1` the rule is determinate iff `γ ≠ 1`; `γ = 2` is determinate, so "less than one-for-one" is not necessary (E2) | `ActivePassive.gamma_rule_determinate_iff`, `ActivePassive.less_than_one_for_one_not_necessary` |
| Cochrane pp. 18–19 | for `γ ≠ 1`, unique iff `(α − γ)/(1 − γ) > 0`; the same state by state with a random target | `ActivePassive.gamma_rule_general_iff`, `ActivePassive.gamma_rule_random` |
| Cochrane p. 19 | `γ` is not identified; passive and active regimes are observationally equivalent | `ActivePassive.gamma_not_identified`, `ActivePassive.obs_equiv_two_period` |
| Cochrane p. 18 | the regression `s₁ = a + γB₀/P₁ + u₁` would estimate `γ = 1`: equilibrium data satisfy `s₁ = 1 · B₀/P₁` exactly | `ActivePassive.rule_regression_gamma_one` |

## §1.8 Active rules with a single crossing, p. 17 (TidyR5SingleCrossing)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 17 | the excess valuation `B₀/P − s(P)`, whose zeros on `P > 0` are the equilibria; the sign change: some `a > 0` has `s(a) ≤ B₀/a` and some `b > 0` has `B₀/b ≤ s(b)` | `TidyR5SingleCrossing.excess`, `TidyR5SingleCrossing.SignChange` |
| Cochrane p. 17 | a rule continuous on `P > 0` with a sign change has an equilibrium (intermediate value theorem, `a` and `b` in either order, no monotonicity); the sign change is necessary; so for a continuous rule an equilibrium exists iff the sign change holds | `TidyR5SingleCrossing.exists_of_signChange`, `TidyR5SingleCrossing.signChange_of_mem`, `TidyR5SingleCrossing.eqmSet_nonempty_iff` |
| Cochrane p. 17 | "we just have to exclude the one-for-one case … (or multiple crossings)": a continuous rule with `B₀/P − s(P)` strictly decreasing on `P > 0` has exactly one equilibrium iff the sign change holds | `TidyR5SingleCrossing.singleCrossing_existsUnique_iff` |
| Cochrane p. 17 | a checkable sufficient condition: `s ≤ M` on `(0, 1]` and `s ≥ ε > 0` for `P ≥ P₀`, with `B₀ > 0`, give exactly one equilibrium | `TidyR5SingleCrossing.singleCrossing_existsUnique_of_bounds` |
| Cochrane p. 17 | the strictly decreasing rule `s(P) = B₀/(2P) + c` is not weakly increasing, so `ActivePassive.active_existsUnique` does not apply, yet it is active, with `P₁ = B₀/(2c)` | `TidyR5SingleCrossing.decreasing_rule_active` |
| Cochrane p. 17 | continuity and a single crossing are not enough: `s(P) = B₀/P + P` has no equilibrium | `TidyR5SingleCrossing.continuous_singleCrossing_no_eqm` |
| Cochrane p. 17 | continuity cannot be dropped: a single-crossing rule with a sign change, and a positive surplus at every price level when `B₀ ≥ 1`, has no equilibrium; it is indeed not continuous | `TidyR5SingleCrossing.jumpExcess`, `TidyR5SingleCrossing.jumpRule`, `TidyR5SingleCrossing.discont_singleCrossing_no_eqm`, `TidyR5SingleCrossing.discont_rule_not_continuousOn` |

## §1.9 The `γ`-rule with general `α` and a random target, pp. 18–19 (TidyR5GammaRandom)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane pp. 18–19 | the coefficient `(α − γ)/(1 − γ)`; `γ ≠ 1` and `(α − γ)/(1 − γ) > 0` iff `(α − γ)(1 − γ) > 0` | `TidyR5GammaRandom.gammaCoef`, `TidyR5GammaRandom.gamma_cond_iff_mul_pos` |
| Cochrane pp. 18–19 | deterministic target, every `γ` including `γ = 1`: unique iff `γ ≠ 1` and `(α − γ)/(1 − γ) > 0`, and then `P₁ = P₁*(1 − γ)/(α − γ)` | `TidyR5GammaRandom.gamma_rule_full_iff`, `TidyR5GammaRandom.gamma_rule_eq_iff`, `TidyR5GammaRandom.div_gammaCoef` |
| Cochrane p. 19 | a random variable is the unique state-by-state solution iff every state has a unique solution | `TidyR5GammaRandom.existsUnique_pi_iff` |
| Cochrane pp. 18–19 | the rule state by state with random `α`, `γ`, `B₀` and `P₁*`: exactly one positive random `P₁` solves (1.14) iff `γ ≠ 1` and `(α − γ)/(1 − γ) > 0` in every state, and then `P₁ = P₁*(1 − γ)/(α − γ)` state by state | `TidyR5GammaRandom.gammaRuleRandom`, `TidyR5GammaRandom.gamma_random_existsUnique_iff`, `TidyR5GammaRandom.gamma_random_valuation_iff` |
| Cochrane pp. 18–19 | deterministic `α`, `γ` with a random target: unique iff `(α − γ)(1 − γ) > 0`, whatever the distribution of `P₁*`; `α = 1` recovers `ActivePassive.gamma_rule_random` | `TidyR5GammaRandom.gamma_random_const_iff`, `TidyR5GammaRandom.gamma_random_alpha_one` |
| Cochrane p. 8; p. 19 | with deterministic `α`, `γ` the equilibrium `P₁` is known at date 1 whenever `P₁*` is | `TidyR5GammaRandom.gamma_random_known` |
| Cochrane pp. 18–19 | the condition must hold in every state: a random `γ` equal to `1` in one state and `0` in the other gives no unique equilibrium | `TidyR5GammaRandom.gamma_random_one_state_fails` |

## §§1.1–1.3 The household problem behind (1.3) and `M₁ = 0`, pp. 4–8 (TidyR6Household)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §1.3, pp. 7–8; (1.2), p. 8; (1.1), (1.15), pp. 4, 16 | the household's environment and plan; the date-0 budget `B₋₁ + P₀y₀ = P₀c₀ + P₀s₀ + Q₀B₀` and the last-day budget `B₀ + P₁y₁ = P₁c₁ + P₁s₁ + M₁`; feasibility (date-0 choices known at 0, `M₁ ≥ 0`) | `TidyR6Household.Env`, `TidyR6Household.Plan`, `TidyR6Household.Budget0`, `TidyR6Household.Budget1`, `TidyR6Household.Feasible` |
| Cochrane §1.2, p. 7 (representative agent) | expected utility `u(c₀) + βE₀u(c₁)`; an optimal plan; the Euler equation `Q₀u'(c₀)/P₀ = βE₀[u'(c₁)/P₁]` | `TidyR6Household.value`, `TidyR6Household.Optimal`, `TidyR6Household.Euler` |
| Cochrane p. 7; (1.3), p. 8 (tools) | a differentiable concave function lies below its tangents; `ε ↦ E_t[u(f + εg)]` has derivative `E_t[u'(f)g]` for bounded `f`, `g`, in every `ExpectationSystem` | `TidyR6Household.le_tangent`, `TidyR6Household.hasDerivAt_E_comp` |
| Cochrane §1.1, p. 4 ("nobody wants to hold cash … after the end of day 1") | with strictly increasing utility and a faithful `E₀` (no null states), an optimal plan has `M₁ = 0`; every finite tree with positive probabilities is faithful | `TidyR6Household.Faithful0`, `TidyR6Household.money_zero_of_optimal`, `TidyR6Household.finiteTree_faithful0` |
| Cochrane §1.1, p. 4 (faithfulness is needed) | under the two-state system `pointSystem`, which has a null state, an optimal plan holds money in the null state | `TidyR6Household.pointSystem`, `TidyR6Household.money_zero_needs_faithful` |
| Cochrane (1.3), p. 8 (necessity) | the bond deviation of a feasible plan is feasible; an optimal plan satisfies the Euler equation for every `C¹` utility, with `c₁` and `1/P₁` bounded | `TidyR6Household.dev`, `TidyR6Household.dev_feasible`, `TidyR6Household.euler_of_optimal` |
| Cochrane (1.3), p. 8 (sufficiency) | for concave, weakly increasing utility, a feasible plan with `M₁ = 0` and the Euler equation is optimal; both directions together | `TidyR6Household.optimal_of_euler`, `TidyR6Household.optimal_iff` |
| Cochrane (1.3), p. 8; §1.2, p. 7 (constant endowment) | at constant consumption the Euler equation is exactly `Q₀ = βE₀(P₀/P₁)`; with a random endowment it is `Q₀ = βE₀[(u'(y₁)/u'(y₀))(P₀/P₁)]` | `TidyR6Household.euler_const_iff_bondPrice`, `TidyR6Household.euler_iff_sdf` |
| Cochrane (1.1)–(1.4), pp. 4–8 | a competitive equilibrium is exactly a fiscal-theory equilibrium: (1.2), (1.3) and (1.4) are derived, not imposed | `TidyR6Household.CompEqm`, `TidyR6Household.compEqm_iff_equilibrium` |
| Cochrane §1.3, pp. 7–8, on finite trees | the same without boundedness hypotheses; exactly one competitive equilibrium; the coin-flip economy with linear utility has `P₀ = 4/3` | `TidyR6Household.finiteTree_compEqm_iff`, `TidyR6Household.finiteTree_compEqm_existsUnique`, `TidyR6Household.coin_compEqm` |

## §§1.1–1.3 The household problem on a probability space, pp. 4–8 (TidyR6HouseholdMeasure)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §1.3, p. 8 (genuine uncertainty) | a probability space with a filtration, `E_t x = μ[x \| 𝓕 t]` (restated from the IntertemporalModel project) | `TidyR6HouseholdMeasure.MeasSystem`, `TidyR6HouseholdMeasure.MeasSystem.μ`, `TidyR6HouseholdMeasure.MeasSystem.E` |
| Cochrane p. 7; (1.3), p. 8 (tools, restated from the IntertemporalModel project) | continuous functions are bounded on compacts and integrable along essentially bounded variables; differentiation of expected utility under the integral; `E[dX] = E[d E_t X]`; the bounded weight | `TidyR6HouseholdMeasure.exists_abs_le_of_continuous`, `TidyR6HouseholdMeasure.integrable_comp_of_bdd`, `TidyR6HouseholdMeasure.hasDerivAt_integral_comp`, `TidyR6HouseholdMeasure.integral_mul_E`, `TidyR6HouseholdMeasure.abs_weight_le` |
| Cochrane §§1.2–1.3, pp. 7–8 | feasibility almost surely, with `u(c₀)`, `u(c₁)` and `B₀` integrable; expected utility as an integral, and its split; optimality; the Euler equation a.s.; essential boundedness | `TidyR6HouseholdMeasure.MFeasible`, `TidyR6HouseholdMeasure.expU`, `TidyR6HouseholdMeasure.expU_eq`, `TidyR6HouseholdMeasure.MOptimal`, `TidyR6HouseholdMeasure.MEuler`, `TidyR6HouseholdMeasure.BddAt` |
| Cochrane §1.1, p. 4 | an optimal plan with essentially bounded `c₁` has `M₁ = 0` almost surely | `TidyR6HouseholdMeasure.m_money_zero_of_optimal` |
| Cochrane (1.3), p. 8 | Euler necessity with `c₀`, `c₁`, `1/P₁` essentially bounded (no bound on `Q₀/P₀`); sufficiency for concave utility; both directions | `TidyR6HouseholdMeasure.m_euler_of_optimal`, `TidyR6HouseholdMeasure.m_optimal_of_euler`, `TidyR6HouseholdMeasure.m_optimal_iff` |
| Cochrane (1.3), p. 8 | the bond price `Q₀ = βP₀E₀(1/P₁)` is the printed `Q₀ = βE₀(P₀/P₁)` under integrability; at constant consumption the Euler equation is (1.3) a.s. | `TidyR6HouseholdMeasure.MBondPrice`, `TidyR6HouseholdMeasure.m_bondPrice_iff`, `TidyR6HouseholdMeasure.m_euler_const_iff` |
| Cochrane (1.1)–(1.4), pp. 4–8 | a competitive equilibrium is exactly an almost-sure fiscal-theory equilibrium (`B₀` integrable, `s₁/B₀` essentially bounded) | `TidyR6HouseholdMeasure.MEquilibrium`, `TidyR6HouseholdMeasure.MCompEqm`, `TidyR6HouseholdMeasure.m_compEqm_iff_equilibrium` |

## §§1.3–1.4 The model with an infinite horizon, pp. 7–9 (TidyR6InfiniteHorizon)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (1.2)–(1.3), p. 8, at every date | the flow condition `B_{t−1} = P_t s_t + Q_t B_t`; the bond price `Q_t = βE_t(P_t/P_{t+1})`; the real debt `v_t = B_{t−1}/P_t` | `TidyR6InfiniteHorizon.Flow`, `TidyR6InfiniteHorizon.BondPrice`, `TidyR6InfiniteHorizon.realDebt` |
| Cochrane §1.1, p. 4 (the last day replaced by a limit); pp. 7–8 | the transversality condition `β^T E_t[B_{t+T−1}/P_{t+T}] → 0`; the equilibrium; the present value `∑_j β^j E_t s_{t+j}`; debt known when issued | `TidyR6InfiniteHorizon.TVC`, `TidyR6InfiniteHorizon.Equilibrium`, `TidyR6InfiniteHorizon.pvInf`, `TidyR6InfiniteHorizon.DebtKnown`, `TidyR6InfiniteHorizon.debtKnown_at` |
| Cochrane (1.2)–(1.5), p. 8 | the revenue from bond sales is `P_t · βE_t v_{t+1}`; given (1.3) the flow condition is the recursion `v_t = s_t + βE_t v_{t+1}`, and conversely; the real debt is adapted | `TidyR6InfiniteHorizon.revenue_eq`, `TidyR6InfiniteHorizon.realDebt_rec`, `TidyR6InfiniteHorizon.flow_of_rec`, `TidyR6InfiniteHorizon.realDebt_adapted` |
| Cochrane (1.5), p. 8, iterated forward | `β^T E_t v_{t+T} → v_t − ∑_j β^j E_t s_{t+j}`; so the valuation equation holds at every date iff the transversality condition does; the present value satisfies the recursion and is adapted | `TidyR6InfiniteHorizon.tendsto_tvc_term`, `TidyR6InfiniteHorizon.tvc_iff_valuation`, `TidyR6InfiniteHorizon.pvInf_rec`, `TidyR6InfiniteHorizon.pvInf_adapted` |
| Cochrane pp. 7–8 | every equilibrium satisfies the valuation equation; equilibrium iff `P_t = B_{t−1}/∑_j β^j E_t s_{t+j}` with a positive present value; exactly one equilibrium; none if the present value is not positive somewhere (E3) | `TidyR6InfiniteHorizon.valuation_of_equilibrium`, `TidyR6InfiniteHorizon.equilibrium_iff`, `TidyR6InfiniteHorizon.equilibrium_existsUnique`, `TidyR6InfiniteHorizon.no_equilibrium_of_pv_nonpos` |
| Cochrane p. 8; §1.4, p. 9 | `P₀ = B_{−1}/∑_j β^j E_0 s_j`; `P₀` depends on surpluses only through their present value and not on later debt sales; scaling the debt coming due scales the price level (the share split) | `TidyR6InfiniteHorizon.price0_eq`, `TidyR6InfiniteHorizon.price0_eq_of_pv_eq`, `TidyR6InfiniteHorizon.price0_indep_debt`, `TidyR6InfiniteHorizon.price1_scales_with_debt` |

## §§1.8–1.9 Active and passive rules with an infinite horizon, pp. 15–19 (TidyR6InfiniteActivePassive)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (1.3), p. 8 (restated from the IntertemporalModel project) | `E_t` of a positive variable is positive | `TidyR6InfiniteActivePassive.E_pos_of_pos` |
| Cochrane §1.9, pp. 18–19 | the rule `s_t = γB_{t−1}/P_t + ŝ_t`; its equilibria; the forward value `∑_j (β/(1 − γ))^j E_t[ŝ_{t+j}/(1 − γ)]`; in equilibrium `(1 − γ)v_t = ŝ_t + βE_t v_{t+1}` | `TidyR6InfiniteActivePassive.ruleSurplus`, `TidyR6InfiniteActivePassive.RuleEqm`, `TidyR6InfiniteActivePassive.ruleF`, `TidyR6InfiniteActivePassive.rule_rec` |
| Cochrane p. 19 (passive, `0 < γ < 2`) | every solution of the rule recursion satisfies the transversality condition; with the debt policy `passiveDebt` every positive adapted price path is an equilibrium; every `P₀ > 0` is an equilibrium price level | `TidyR6InfiniteActivePassive.stable_tendsto_zero`, `TidyR6InfiniteActivePassive.passive_tvc`, `TidyR6InfiniteActivePassive.passiveDebt`, `TidyR6InfiniteActivePassive.passive_every_price`, `TidyR6InfiniteActivePassive.passive_indeterminate` |
| Cochrane p. 19 (active, `γ ≤ 0` or `γ ≥ 2`) | the transversality condition holds iff `v = ruleF`; every equilibrium has `B_{t−1}/P_t = ruleF_t`; exactly one equilibrium | `TidyR6InfiniteActivePassive.active_tvc_iff`, `TidyR6InfiniteActivePassive.active_valuation`, `TidyR6InfiniteActivePassive.active_existsUnique` |
| Cochrane p. 19 ("`γ > 0` in the later intertemporal model" indicates passive policy) | `P₀` is determined iff `γ ≤ 0` or `γ ≥ 2`; `γ = 3 > 0` is active, with the unique equilibrium `P_t = 2 + β` | `TidyR6InfiniteActivePassive.determinate0_iff`, `TidyR6InfiniteActivePassive.gamma_three_active` |

## §1.1 The two-period model as a truncation of the infinite horizon (TidyR6Truncation)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §1.1, p. 4; (1.5), p. 8 | the backward solution of `z_T = u_T`, `z_t = u_t + aE_t z_{t+1}`: last day, recursion, uniqueness, closed form `∑_{j ≤ T−t} a^j E_t u_{t+j}`, measurability | `TidyR6Truncation.finSteps`, `TidyR6Truncation.finSol`, `TidyR6Truncation.finSol_last`, `TidyR6Truncation.finSol_rec`, `TidyR6Truncation.finSol_unique`, `TidyR6Truncation.finSol_closed`, `TidyR6Truncation.finSol_known` |
| Cochrane §1.1, p. 4; (1.5), p. 8 | as `T → ∞` the backward solution converges to the forward solution `∑_j a^j E_t u_{t+j}` (`\|a\| < 1`) | `TidyR6Truncation.finSol_tendsto` |
| Cochrane §§1.1–1.3, pp. 4–8 | the `T`-period equilibrium; with `T = 1` it is exactly `TwoPeriod.Equilibrium`, with present value `TwoPeriod.pv` | `TidyR6Truncation.FinEqm`, `TidyR6Truncation.finEqm_one_iff`, `TidyR6Truncation.finSol_one_zero` |
| Cochrane §§1.1–1.3, pp. 4–8 | the flow condition as the real-debt recursion at one date; every `T`-period model has exactly one equilibrium, `P_t = B_{t−1}/∑_{j ≤ T−t} β^j E_t s_{t+j}` | `TidyR6Truncation.flow_iff_rec`, `TidyR6Truncation.finEqm_iff`, `TidyR6Truncation.finEqm_exists`, `TidyR6Truncation.finEqm_unique` |
| Cochrane §1.3, pp. 7–8 (the limit of last days) | the `T`-period price levels converge to the infinite-horizon equilibrium price level, which every infinite-horizon equilibrium has | `TidyR6Truncation.finEqm_price_tendsto`, `TidyR6Truncation.finEqm_limit_is_equilibrium` |
| Cochrane §1.1, p. 4 | an infinite-horizon equilibrium with `B₁ = 0` restricts to a two-period equilibrium; a two-period equilibrium, continued with no debt and no surpluses, is an infinite-horizon equilibrium | `TidyR6Truncation.restrict_twoPeriod`, `TidyR6Truncation.extend_twoPeriod` |
| Cochrane §1.9, pp. 18–19, with a last day | the rule recursion with `(1 − γ)v_T = ŝ_T`; every `γ ≠ 1` determines the real debt; with `γ = 1` the last-day price is free | `TidyR6Truncation.finRule_rec`, `TidyR6Truncation.finRule_realDebt`, `TidyR6Truncation.finRule_gamma_one` |
| Cochrane §1.9, pp. 18–19 (truncation as a selection) | for `\|1 − γ\| > β` the truncated equilibria converge to `ruleF`; for `1 − β < γ < 1` the truncated real debt diverges | `TidyR6Truncation.finRule_tendsto`, `TidyR6Truncation.truncation_diverges` |

## pp. 18–19 The regressions as statistical estimates (TidyR6Regression)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 18 | the sum of squared residuals, least-squares estimates, the sample mean and the textbook OLS slope | `TidyR6Regression.ssr`, `TidyR6Regression.ssr_nonneg`, `TidyR6Regression.IsOLS`, `TidyR6Regression.mean`, `TidyR6Regression.olsSlope` |
| Cochrane p. 18 ("the regression would estimate `γ = 1`") | every equilibrium lies on `s₁ = 0 + 1 · B₀/P₁`; with such data and a varying regressor the OLS estimates are exactly `(0, 1)` | `TidyR6Regression.equilibrium_data`, `TidyR6Regression.ols_iff`, `TidyR6Regression.olsSlope_eq_one` |
| Cochrane p. 18, in the population | the population mean squared residual and least-squares coefficients; with `B₀/P₁` square integrable and not a.s. constant the coefficients are exactly `(0, 1)`, whatever the surplus rule | `TidyR6Regression.popSSR`, `TidyR6Regression.IsPopOLS`, `TidyR6Regression.popOLS_iff`, `TidyR6Regression.popOLS_equilibrium` |
| Cochrane pp. 18–19 | the estimate is consistent for the structural `γ` of the `γ`-rule iff `γ = 1` | `TidyR6Regression.ols_consistent_iff` |
| Cochrane p. 19 ("`γ` … is not identified") | in the second regression every coefficient `g` is least squares, in the sample and in the population | `TidyR6Regression.gamma_not_identified_sample`, `TidyR6Regression.gamma_not_identified_pop` |

## Links to the Woodford projects (Links)

| Book | Claim | Lean |
| --- | --- | --- |
| Woodford (2003) (4.5), pp. 313–314; p. 277, Prop. C.2, p. 672 (restated from the Woodford Chapter 4 project) | the debt law of motion under the tax rule (4.4); the scalar recursion `d_{t+1} = γd_t + u_t` is bounded-input-bounded-state iff `\|γ\| < 1` | `Links.Debt45`, `Links.dRec`, `Links.eq_dRec`, `Links.rec_bounded`, `Links.rec_unbounded`, `Links.abs_rec_le` |
| Woodford (2003) pp. 312–313 (restated from the Woodford Chapter 4 project) | locally Ricardian tax rules; (4.4) is locally Ricardian iff `\|β⁻¹(1 − τ_b)\| < 1` | `Links.LocallyRicardian`, `Links.locallyRicardian_iff` |
| Cochrane (1.16), p. 17, §§1.8–1.9, pp. 17–18, vs Woodford (2003) p. 313 | the passive response `γ = τ_b = 1` is locally Ricardian; a fixed surplus `γ = 0` is not; locally Ricardian iff `1 − β < τ_b < 1 + β` | `Links.passive_locallyRicardian`, `Links.fixed_surplus_not_locallyRicardian`, `Links.locallyRicardian_iff_interval` |
| Cochrane pp. 18–19 vs Woodford (2003) p. 313 | a `γ`-rule indeterminate in two periods is locally Ricardian; `γ = 1 − β/2` is locally Ricardian yet determinate; every non-Ricardian `γ` is determinate | `Links.two_period_indeterminate_imp_locallyRicardian`, `Links.locallyRicardian_two_period_determinate`, `Links.not_locallyRicardian_two_period_determinate` |
| Woodford (2003) p. 66; (4.2), p. 124 (restated from the Woodford Chapter 2 project) | the discount factor; under `T = αW − ΔM`, `Q_{t,t+n}W_{t+n} = (1 − α)ⁿW_t`, so the transversality condition holds for `0 < α ≤ 1` and fails for `α = 0` with `W_t ≠ 0` | `Links.discount`, `Links.ricardian_step`, `Links.ricardian_discounted`, `Links.ricardian_tvc`, `Links.ricardian_tvc_fails_of_alpha_zero` |
| Cochrane (1.16), p. 17, vs Woodford (2003) (4.2), p. 124 | the passive rule is Woodford's rule with `α = 1` and no money; it retires all liabilities, so the transversality condition holds for any price path, as (1.14) holds for any `P₁` | `Links.passive_is_alpha_one`, `Links.alpha_one_debt_retired`, `Links.passive_valuation_any_price` |
| Cochrane p. 17 vs Woodford (2003) p. 124 | with `α = 0` the transversality condition restricts prices | `Links.zero_surplus_restricts_prices` |

## Shared tools

| Book | Claim | Lean |
| --- | --- | --- |
| Chapter 1 throughout | the expectation axioms, pull-out, perfect foresight; bounded processes (used by `Links.LocallyRicardian`); finite event trees and the coin-flip tree | `ExpectationSystem`, `ExpectationSystem.PullOut`, `perfectForesight`, `perfectForesight_pullOut`, `BoundedProc`, `ExpectationsFiniteTree.FiniteTree.toExpectationSystem`, `ExpectationsFiniteTree.finiteTree_pullOut`, `ExpectationsFiniteTree.coinSystem`, `ExpectationsFiniteTree.firstHeads`, `ExpectationsFiniteTree.coinSystem_E0_firstHeads` |
| shared core, not used by Chapter 1 | forward series, the forward solution and Schur–Cohn determinacy, carried for the later Cochrane projects | `ExpectationSystem.forwardSeries`, `ForwardSolution.existsUnique_bounded`, `SchurStable`, `schurStable_iff_roots` |
