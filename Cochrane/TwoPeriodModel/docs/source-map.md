# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, "A two-period model"
(pp. 4–19). Each formal claim is listed with its Lean name, relative to the namespace
`Cochrane.TwoPeriodModel`. Page numbers are book pages. The book has no labelled propositions,
so rows are keyed by equation number, table, box or page. Rows follow the book section by
section, and each heading names the modules that formalise the section: §§1.1–1.9, then the
links to the Woodford projects, then the shared tools. Every statement holds for an arbitrary
`ExpectationSystem`, so under perfect foresight and under uncertainty. Date-0 quantities are
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
