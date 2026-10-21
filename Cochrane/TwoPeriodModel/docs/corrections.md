# Corrections to the source

This file lists places where a claim in Chapter 1 of Cochrane (2023), *The Fiscal Theory of the
Price Level*, is false, imprecise, or relies on an unstated hypothesis, and where the Lean
statement departs from the printed one. In each case the Lean statement proves the stated
version and cites the original.

Codes E1–E3 are the Chapter 1 items of the survey of Chapters 1–3
(`notes/survey_cochrane_ch1-3.md`). Each was confirmed or refuted by formalisation before being
recorded here, and an entry is revised if formalisation shows the finding itself to be wrong.
Several claims that the book asserts without proof turned out to be correct; they are listed in
the last section.

Out of scope are the discursive passages: the backing theory and the irrelevance of transactions
(§1.2), the Ricardian terminology (pp. 12–13) and the remark that the active-versus-passive
debate is a dead end (p. 19). Lean names are relative to the namespace `Cochrane.TwoPeriodModel`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| p. 12 (E1) | To borrow without changing `P₁`, the government sells `ΔB₀` with `(B₀ + ΔB₀)/P₁ = s₁ + RΔs₀`, the surplus `s₁` being raised by `−RΔs₀`. | The sign is wrong: the condition is `(B₀ + ΔB₀)/P₁ = s₁ − RΔs₀`, and `P₁` is the equilibrium price for `(B₀ + ΔB₀, s₁ − RΔs₀)` iff `ΔB₀ = −RΔs₀P₁` (`DebtSales.borrow_debt_corrected`). With the debt implied by the printed condition, the date-1 price level differs from `P₁` whenever `Δs₀ ≠ 0` (`DebtSales.borrow_printed_fails`). The rest of the "Borrow" row is correct (last section). |
| p. 18 (E2) | "Active fiscal policy only requires that the government respond less than one-for-one to the last component." | Responding less than one-for-one is sufficient but not necessary. With `α = 1` the rule `s₁ = αB₀/P₁* + γ(B₀/P₁ − B₀/P₁*)` has a unique equilibrium iff `γ ≠ 1`, and then `P₁ = P₁*` (`ActivePassive.gamma_rule_determinate_iff`). The over-responding rule `γ = 2` is determinate (`ActivePassive.less_than_one_for_one_not_necessary`). For general `α` and `γ ≠ 1` the rule is determinate iff `(α − γ)/(1 − γ) > 0`, with `P₁ = P₁*(1 − γ)/(α − γ)` (`ActivePassive.gamma_rule_general_iff`). For `γ = 1`, `α ≠ 1` there is no equilibrium at all (`ActivePassive.gamma_eqmSet_empty`). |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| (1.1), p. 4; (1.4)–(1.5), p. 8; §1.4 (E3) | `P₁ = B₀/s₁` and `P₀ = B₋₁/(s₀ + βE₀s₁)`: the valuation equations determine the price level. | A hypothesis is missing: the formulas give a positive price level only if `s₁ > 0` in every state and `s₀ + βE₀s₁ > 0`. With `B₀ > 0` and `s₁ ≤ 0` no positive `P₁` solves (1.1) (`TwoPeriod.lastDay_none`), and if either condition fails in some state there is no equilibrium (`TwoPeriod.no_equilibrium_of_s1_nonpos`, `TwoPeriod.no_equilibrium_of_pv_nonpos`). With both, there is exactly one (`TwoPeriod.equilibrium_existsUnique`). The hypotheses are carried by every later theorem that uses the formulas. |
| Table 1.1, "Borrow", p. 12 (addendum to E1) | Raising the date-1 surplus by `−RΔs₀` and selling `ΔB₀` keeps `P₁` unchanged. | Under genuine uncertainty this is imprecise. An additive rise `−RΔs₀` in `s₁` in every state, with a debt `B₀` known at date 0, keeps `P₁` unchanged in every state only if `s₁` is itself known at date 0: `P₁` is kept iff `B₀′s₁ = B₀s₁′` (`DebtSales.borrow_keeps_price1_iff`). The strategy is implemented by scaling debt and the date-1 surplus by the date-0 factor `c = 1 − Δs₀/(βE₀s₁)`. Then `P₀`, `P₁` and `Q₀` are all unchanged and `E₀(cs₁) = E₀s₁ − Δs₀/β`, as the row requires (`DebtSales.borrow_implementable`). |
| (1.16), p. 17 | Under the passive rule, (1.14) "no longer determines the price level". | Stated as: every `P₁ > 0` is an equilibrium (`ActivePassive.passive_eqmSet`), so the set of equilibrium price levels is uncountable (`ActivePassive.passive_indeterminate`). |
| p. 17 | Active policy: "we just have to exclude the one-for-one case … (or multiple crossings)". | A single crossing gives at most one equilibrium (`ActivePassive.active_unique_of_strictAnti`). Existence needs more. It is proved, by the intermediate value theorem, for a continuous surplus rule that is weakly increasing in `P₁` and positive at some price level (`ActivePassive.active_existsUnique`). This covers a fixed surplus and a proportional tax (`ActivePassive.fixed_surplus_active`, `ActivePassive.propTax_active`). A rule with two crossings is exhibited (`ActivePassive.multiple_crossings`). |
| pp. 18–19 | The `γ`-rule with a random target `P₁*`. | The equilibrium set is computed for a deterministic target. With a random target the rule is applied state by state: for `α = 1` and `γ ≠ 1` the only solution is `P₁ = P₁*`, and for `γ = 1` every `P₁ > 0` solves it (`ActivePassive.gamma_rule_random`). |
| p. 18 | "The regression would estimate `γ = 1`." | Formalised as an exact property of equilibrium data, not as a statistical estimate: under (1.13) every equilibrium satisfies `s₁ = 0 + 1 · B₀/P₁` (`ActivePassive.rule_regression_gamma_one`). |
| pp. 11–12 | "Fiscal theory can produce a completely steady price level despite wide variation in deficits and debt." | Proved as an iff: a deficit `Δs₀` leaves `P₀` unchanged iff `Δs₀ + β(E₀s₁′ − E₀s₁) = 0` (`DebtSales.steady_price0_iff`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| Throughout | Conditional expectations pull out quantities known at date 0 | `ExpectationSystem.PullOut` as a hypothesis; true for perfect foresight (`perfectForesight_pullOut`) and every finite tree (`ExpectationsFiniteTree.finiteTree_pullOut`) |
| Throughout | `B₋₁`, `B₀`, `s₀` and `P₀` are known at date 0 | `TwoPeriod.Known` hypotheses; `P₀` known at date 0 is part of `TwoPeriod.Equilibrium` |
| Throughout | Price levels are positive; `B₋₁, B₀ > 0` | Part of `TwoPeriod.Equilibrium`, and hypotheses of `TwoPeriod.equilibrium_existsUnique` and its successors |
| §§1.1–1.5 (E3) | `s₁ > 0` in every state and `s₀ + βE₀s₁ > 0` | Hypotheses of `TwoPeriod.equilibrium_existsUnique`, `TwoPeriod.equilibrium_iff`, `DebtSales.price0_formula`; shown necessary by `TwoPeriod.no_equilibrium_of_s1_nonpos`, `TwoPeriod.no_equilibrium_of_pv_nonpos` |
| p. 10 | Under an interest-rate target or peg, `E₀s₁ > 0` strictly, so that the debt sold is positive | Hypothesis of `MonetaryFiscal.target_existsUnique`, `MonetaryFiscal.determinate_under_peg`, `MonetaryFiscal.fisherian_two_period`. It does not follow from `s₁ > 0` in an abstract `ExpectationSystem`, so it is stated separately |
| p. 10 | `i₀ > −1` | Hypothesis of `MonetaryFiscal.target_existsUnique` and `PriceLevelTarget.rule_target_existsUnique` |
| §§1.6–1.7 | `P₁* > 0` and `E₀(1/P₁*) > 0` | Hypotheses of the `PriceLevelTarget` theorems |
| §1.7, p. 15 | Under the rule and a target, `s₀ < B₋₁(1 + i₀)βE₀(1/P₁*)`, so that a positive debt is sold | Hypothesis of `PriceLevelTarget.rule_target_existsUnique` |
| (1.14), p. 16 | No demand for money at the end of the last day | `M₁ = 0` imposed (`ActivePassive.valuation_of_zero_money`), not derived from a household problem |

## Claims confirmed correct

| Where | Claim | Lean |
| --- | --- | --- |
| (1.2)–(1.5), p. 8 | (1.2), (1.3) and (1.4) imply (1.5), and the unnumbered display after (1.3) | `TwoPeriod.valuation0_of_flow`, `TwoPeriod.flow_iff_valuation0`, `TwoPeriod.flow_real` |
| Box p. 7; p. 8 | A lower `β` or bad fiscal news raises `P₀`; `P₀` depends on surpluses only through their present value | `TwoPeriod.price0_strictAnti_beta`, `TwoPeriod.price0_strictAnti_Es1`, `TwoPeriod.price0_eq_of_pv_eq`, `TwoPeriod.price0_any_level` |
| (1.8), p. 9 | The chain of equalities, and "bond sales raise no extra revenue" | `MonetaryFiscal.eq_1_8`, `MonetaryFiscal.revenue_invariant` |
| p. 9 | The share split: `P₀` unchanged, `P₁` scaled, `Q₀` divided, the rate rises | `MonetaryFiscal.shareSplit_unique`, `MonetaryFiscal.doubling`, `MonetaryFiscal.shareSplit_rate_rises` |
| p. 10 | Determinacy under a peg and the Fisherian response | `MonetaryFiscal.target_existsUnique`, `MonetaryFiscal.fisherian_two_period` |
| (1.9)–(1.10), p. 10 | Expected and unexpected inflation | `MonetaryFiscal.E0_invP1`, `MonetaryFiscal.unexpected_inflation`, `MonetaryFiscal.inflation_decomposition` |
| (1.11)–(1.12), p. 11 | The equity issue | `DebtSales.equityIssue_price1`, `DebtSales.equityIssue_revenue`, `DebtSales.equityIssue_lowers_price0`, `DebtSales.equityIssue_funds_deficit` |
| Table 1.1, pp. 11–12 | "Borrow" (apart from E1), "Inflate" and "AR(1)", and the column `B₀/P₁` | `DebtSales.borrow_price0`, `DebtSales.borrow_value_rises`, `DebtSales.inflate_real_debt_falls_by_deficit`, `DebtSales.ar1_price0_rises_more`, `DebtSales.ar1_value_falls`, `DebtSales.maturing_value_change` |
| p. 12 | The s-shaped surplus in two periods | `DebtSales.sShape_two_period` |
| (1.13), pp. 13–15 | `P₁ = P₁*`; borrow, inflate, super-inflate; higher rates lower `P₀` immediately with a future fiscal tightening; flat and unit-elastic debt demand | `PriceLevelTarget.rule_price1`, `PriceLevelTarget.rule_superinflate`, `PriceLevelTarget.rule_higher_rate_lowers_price0`, `PriceLevelTarget.rule_higher_rate_fiscal_tightening`, `PriceLevelTarget.rule_flat_demand`, `PriceLevelTarget.unit_elastic` |
| (1.14)–(1.15), p. 16 | Budget constraints hold at off-equilibrium prices; equilibrium conditions need not | `ActivePassive.budget_any_price`, `ActivePassive.money_nonzero_off_equilibrium` |
| p. 18 | The passive tax rate falls as `P₁` rises; three sources of variation in the value of debt | `ActivePassive.passive_taxRate_strictAnti`, `ActivePassive.value_decomp_innov` |
| p. 19 | `γ` is not identified; observational equivalence of passive and active regimes | `ActivePassive.gamma_not_identified`, `ActivePassive.obs_equiv_two_period` |
