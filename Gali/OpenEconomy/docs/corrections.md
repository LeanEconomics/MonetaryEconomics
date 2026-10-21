# Corrections to the source

Places where a claim in Chapter 8 of Galí (2015) is false, imprecise, or relies
on an unstated hypothesis, and where the Lean statement departs from the
printed one. In each case the Lean statement proves the stated version and
cites the original. Entries are recorded when found and revised if
formalisation shows the finding itself to be wrong. Lean names are relative to
the namespace `Gali.OpenEconomy`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| p. 236, after (31) | "If `υ` and/or `η` are sufficiently large, a terms of trade depreciation will improve the trade balance." | False for `υ` large alone: the coefficient `υ(ϖ/σ − 1)` equals `η − 1` at `υ = 1`, and with `σ = 1`, `η = 0.9` it is negative for every `υ ∈ (0, 1]` (`AggregateDemand.nxCoef_one_nonpos`, `AggregateDemand.nxCoef_counterexample`, `AggregateDemand.not_large_openness_improves`). Correct: for `η > 1` it is positive for `υ` near 1; for fixed `υ`, positive iff `η > (σ + 1 − υ)/((2 − υ)σ)` (`AggregateDemand.nxCoef_eventually_pos`, `AggregateDemand.nxCoef_pos_iff`). |
| p. 241 | "If `ση > 1` then `Λ_v` can be shown to be increasing in the degree of openness." | False: at `σ = 1`, `η = 2`, `β = 0.99`, `λ = 17/300`, `φ = 1`, `α = 1/4`, `φ_π = 0`, `φ_y = 30`, `ρ_v = 0.99`, condition (41) holds for every `υ ∈ [0, 1]` but `Λ_v` is strictly decreasing (`TaylorRule.printed_monotonicity_false`, `TaylorRule.counterexample_strictAntiOn`). `1/Λ_v` is affine in `σ_υ` with slope `(1 − βρ_v)(1 − ρ_v) + λ(φ_π − ρ_v)`; when that slope is positive, `Λ_v` is increasing (`TaylorRule.lambdaV_strictMonoOn`). |
| App. 8.1, pp. 255–256 | `𝕎 = −((1 − υ)/2) E_0 ∑ βᵗ(…)`. | The sign is `+`, since `𝕎 = −E_0 ∑βᵗ(U_t − U)/(U_cC)` and `(U_t − U)/(U_cC) = −((1 − υ)/2)(…) + t.i.p.` (`Welfare.welfare_sign`, `Welfare.appendix_sign_error`). The final display and (43) are correct. |
| p. 251 | The PEG regime amplifies output-gap and domestic-inflation volatility the most, "with the CITR regime lying somewhere in between". | Contradicts Table 8.1: `sd(π_H)` is 0.35 under PEG but 0.69 under FDIT and 0.58 under FCIT. True only among the strict regimes, and for the output gap across all five (`SimpleRules.peg_not_most_volatile_inflation`, `SimpleRules.peg_most_volatile_strict`, `SimpleRules.peg_most_volatile_gap`). "CITR" is not defined (presumably SCIT). |
| fn. 14, p. 251 | Under the calibration, changes in world output have no effect on the domestic economy. | They leave `yⁿ`, `ỹ`, `π_H` unchanged but move the natural terms of trade (coefficient `−1`), consumption, the CPI and the exchange rate (`SimpleRules.world_output_effects`). |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 247 | "The required subsidy is smaller than the one needed to offset firms' market power." | True (`OptimalPolicy.optSubsidy_lt_closed`), but `τ = 1 − 1/((1 − υ)M)` is negative iff `υ > 1/ε` (`OptimalPolicy.optSubsidy_neg_iff`): at the book's `ε = 9`, `υ = 0.4` it is `−13/27`, a 48% employment tax (`OptimalPolicy.optSubsidy_calibration`). |
| p. 246 | `ℳ = P_H/(W/MPN)`. | Marginal cost is `(1 − τ)W/MPN`; as printed the first line agrees with the others only if `τ = 0` (`OptimalPolicy.printedFirstLine_eq_markup_iff`). |
| fn. 15, p. 251 | "Given the unit root in the nominal exchange rate". | Regime-dependent: under SDIT, SCIT and PEG the exchange rate is a function of stationary variables and mean-reverts; under FDIT a one-time technology shock shifts it permanently (`SimpleRules.sdit_meanReverting`, `SimpleRules.scit_meanReverting`, `SimpleRules.peg_meanReverting`, `SimpleRules.fdit_permanent_shift`, `SimpleRules.fdit_unit_root`). For FCIT only the cumulative accounting identity is proved (`SimpleRules.fcit_cumulative`). |
| (20) and fn. 5, p. 232 | The forward solution for the terms of trade, justified by stationarity of the driving forces. | It needs `lim_T E_t s_T = 0`, which is a hypothesis, not a consequence: given (19) the representation holds iff the limit condition holds (`UIP.forward_iff`), and it fails without it (`UIP.forward_counterexample`). |
| (18), p. 231 | `i_t = i*_t + E_tΔe_{t+1}`. | The log-linearisation drops second-moment (risk-premium) terms; it is the exact derivative at the deterministic steady state, and exact when there is no exchange-rate risk (`UIP.hasFDerivAt_uipGap`, `UIP.uipGap_const`). |
| p. 248 | Preference shocks appreciate the natural terms of trade, since `σ_υΓ_z − (1 − υ)Φ < 0`. | Asserted without proof; proved for all parameters (`OptimalPolicy.tot_pref_coeff_neg`). |
| p. 238 | `σ = η = 1` implies `Γ_z < 0`. | Needs `υ > 0`; `Γ_z = 0` at `υ = 0` (`Supply.GammaZ_unit_neg`, `Supply.GammaZ_zero`). |
| p. 243 | `σ = η = 1` gives the closed-economy responses. | Needs only `ση = 1` (`TaylorRule.closed_economy_equivalence`). |
| Lemma 2, p. 256 | Stated as an equality. | Exact only without inherited dispersion and with inflation measured by the change in the mean log price; otherwise up to `θV₀/(1 − βθ)` (`Welfare.lemma2_calvo`, `Welfare.lemma2_printed_fails`). |
| Table 8.1, p. 251 | Losses. | Reproduced from the printed standard deviations via (44) only if `λ` includes `Θ` (`SimpleRules.tableLoss_consistent`, `SimpleRules.tableLoss_noTheta_inconsistent`). |
| Exercise 8.2, p. 260 | The natural rate's technology coefficient. | The exercise never ties `ψ_ra` to `ψ_ya`; (38) requires `ψ_ra = σ_υ(1 − ρ_a)ψ_ya`, without which the peg's nominal rate is not `i*` (`Ex8_2.peg_iff`, `Ex8_2.peg_rate_38`). |
| p. 240 | The guess `π_t = ψ_{πv} v_t`. | `π_{H,t}`. |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| §8.1.1 | Openness `υ ∈ [0, 1]` | `0 < υ < 1` for the CES demand system (at the endpoints one good drops out) |
| pp. 235, 239 | Positivity of `Φ`, `σ_υ`; monotonicity of `κ_υ` | `σ > 0`, `η > 0`, `υ ∈ [0, 1]`; `λ > 0` (`AggregateDemand.Phi_pos`, `AggregateDemand.sigmaU_pos`, `Supply.kappaU_strictAntiOn`) |
| (16), p. 231 | `ϑ = 1` | Holds under symmetric initial conditions (`RiskSharing.vartheta_eq_one`) |
| Exercise 8.1, p. 259 | `s = y − y*` | Derived from goods-market clearing and balanced trade; needs `υ > 0` (`Ex8_1.tot_of_marketClearing`) |
