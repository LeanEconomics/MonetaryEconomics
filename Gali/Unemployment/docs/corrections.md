# Corrections to the source

Places where a claim in Chapter 7 of Galí (2015) is false, imprecise, or relies
on an unstated hypothesis, and where the Lean statement departs from the
printed one. In each case the Lean statement proves the stated version and
cites the original. Entries are recorded when found and revised if
formalisation shows the finding itself to be wrong. Lean names are relative to
the namespace `Gali.Unemployment`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| Exercise 7.1(b), p. 220 | The loss `∑_t β^k[α_u u_t² + π_t²]`. | The discount factor is `β^t`; with `β^k` the sum diverges along any path with a constant nonzero period loss, such as the discretionary equilibrium of part (c) (`Ex7_1.printed_sum_not_summable`, `Ex7_1.correct_sum_hasSum`). |
| Exercise 7.3(b), p. 222 | Intermediate `υ` dampens the response of the labour force. | True for the impact response and for responses to persistent changes in consumption, which rise strictly in `υ` (`Ex7_3.labourForce_dampening`, `Ex7_3.dampening_strictMonoOn`); not for lagged responses to a one-period change, `υ(1 − υ)ᵏ`, which are not monotone in `υ` (`Ex7_3.lagged_pulse_not_monotone`). |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 212 | The optimality conditions "are identical to those derived in chapter 3". | Chapter 6; the printed (18)–(21) are exactly Chapter 6's (30)–(33) (`Policy.foc7_iff_ch6`). The text also attaches the multipliers to "(13), (14), and (15) and (16) combined"; the pairing is `ζ₂ ↔ (14) + (16)` combined. |
| p. 209 | `ε_w ≈ 4.5`, a markup of about 28 percent. | Exactly `ε_w = e^{1/4}/(e^{1/4} − 1) ∈ (4.5, 4.55)` and markup `e^{1/4} − 1 ∈ (0.28, 0.29)`; `ε_w = 4.5` itself gives `2/7` (`Policy.calibration_epsW`, `Policy.calibration_markup`, `Policy.calibration_book_epsW`). |
| (22), p. 214 | The simple rule written in the level of unemployment. | Read in levels it equals the gap rule with an intercept shifted by `0.025` and is inconsistent with the zero-inflation steady state; in gaps it is consistent; the intercept does not affect the responses (`Policy.rule22_level_iff_gap`, `Policy.rule22_level_not_steady`, `Policy.rule22_deviation`). |
| fn. 12, p. 211 | As `θ_w → 0` unemployment fluctuations vanish. | Requires wage inflation to be bounded uniformly in `θ_w`; then `û → 0` uniformly (`Policy.unemployment_vanishes`, `Policy.unemployment_volatility_vanishes`). Without the bound it fails: `û ≡ 1` solves the wage curve for every `λ_w` (`Policy.unemployment_need_not_vanish`). |
| fn. 6, p. 205 | `1 − N/L = 1 − e^{−u} ≃ u`. | Within `u²/2` for `u ≥ 0` (`UnemploymentDef.abs_rate_sub_u_le`); the bound fails for `u < 0` (`UnemploymentDef.abs_rate_sub_u_bound_fails_neg`). |
| p. 204 | The participating members are `[0, L(j)]`. | Within the unit interval of members, `[0, min(L(j), 1)]` (`IndivisibleLabor.participation_set_unit`, `IndivisibleLabor.laborForce_le_one_iff`). |
| (6), p. 204 | "An approximate relation." | Exact type by type and exact after integrating logs; the only approximation is replacing `∫w(j)`, `∫l(j)` by the log wage index and log labour force, which is first order (`UnemploymentDef.eq6_type`, `UnemploymentDef.eq6_integrated`, `UnemploymentDef.eq6_first_order`). |
| Exercise 7.1(b), p. 220 | Take the Chapter 6 loss as a starting point. | That loss presumes an efficient or nearly efficient steady state; here the remaining distortion `Φ = 1 − e^{−φuⁿ}` lies in `(0.22, 0.23)` at the calibration (`Ex7_1.distortion_eq`, `Ex7_1.distortion_calibration`). The weight `α_u` is proved exactly under the stated approximation (`Ex7_1.flexLoss_eq`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| §7.2 | Determinacy of the system with unemployment | Equivalent to Chapter 6's (`Equilibrium.determinate_iff_ch6`), hence iff the p. 174 condition (`Equilibrium.determinacy_ch7_iff`) |
| §7.3 | Optimal policy | Deterministic Lagrangian sufficiency and uniqueness (`Policy.isOptimal7_iff_foc`, `Policy.existsUnique_optimal7`) |
| Exercise 7.3(a) | Full risk sharing within the household; integrability of `N(j)^{1+φ}` | Taken as assumptions (`Ex7_3.household_utility`) |
