# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, "Keynesian models with
sticky prices" (pp. 397–421), Chapter 18, "History and implications" (pp. 422–432), and Online
Appendix A1, §1.8, "Three-equation model solution" (pp. 571–572), and §1.13.1, "Calculating
responses of the standard new-Keynesian model" (pp. 586–588). Each formal claim is listed with its
Lean name, relative to the namespace `Cochrane.KeynesianStickyPrices`. Page numbers are book
pages. The book has no labelled propositions, so rows are keyed by equation number, figure,
footnote or page. Rows follow the book section by section, and each heading names the modules
that formalise the section: §§17.1–17.5, the Online Appendix material where the chapter uses it,
Chapter 18, then the links between the two chains of modules and the shared tools.

The linear models are stated for an arbitrary `ExpectationSystem`, so every such row holds under
perfect foresight and under genuine uncertainty. The full-model paths of §17.4 (Figures 17.5–17.7,
the reverse-engineered disturbances) are perfect-foresight sequences after the announcement or
shock, as in the book's figures; statements with an infinite past are ℤ-indexed and pathwise.
*Determinate* means that there is exactly one bounded equilibrium for every bounded adapted
disturbance (`RulesAdaptiveRE.REDeterminate`), or, for a deviation system, that its only bounded
adapted solution is zero (`TaylorDeterminacy.Determinate`); `Links` proves the two agree where
both apply. Survey error codes E7–E11 and E24 are those of the survey of Chapters 11–19
(`notes/survey_cochrane_ch11-19.md`); see [corrections](corrections.md). Rows marked "restated"
reproduce results proved in an earlier project, with the namespace adapted.

## §17.1 New vs. old Keynesian models, pp. 397–399 (StaticIS)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (17.1)–(17.2), pp. 397–398 | the IS and Phillips curves with an expected-inflation process `πᵉ`; eliminating output, `π_t = (1 + σκ)πᵉ_t − σκi_t + κE_tx_{t+1}` | `StaticIS.ISPhillips`, `StaticIS.isPhillips_infl` |
| Cochrane (17.3)–(17.4), p. 398 | the static IS model is (17.1)–(17.2) with `E_tx_{t+1}` deleted | `StaticIS.StaticModel`, `StaticIS.isPhillips_iff_static_of_E_zero` |
| Cochrane (17.5), p. 398 | the single equilibrium condition `π_t = −σκi_t + (1 + σκ)πᵉ_t` | `StaticIS.staticModel_iff`, `StaticIS.exists_static_iff_17_5` |
| Cochrane (17.6), p. 398 | adaptive expectations `πᵉ_t = π_{t−1}` (`π_{−1}` given) give (17.6) `π_t = (1 + σκ)π_{t−1} − σκi_t`; rearranged, `π_t − π_{t−1} = −σκ(i_t − π_{t−1})` | `StaticIS.lagged`, `StaticIS.AdaptiveEq`, `StaticIS.exists_static_adaptive_iff`, `StaticIS.adaptive_change_iff` |
| Cochrane p. 398, "determinate" | given `π_{−1}`, (17.6) has exactly one solution, whatever the rate path | `StaticIS.adaptivePath`, `StaticIS.adaptivePath_solves`, `StaticIS.adaptive_unique`, `StaticIS.adaptive_existsUnique` |
| Cochrane p. 398, "unstable" | under a peg `i = ī`, `π_t − ī = (1 + σκ)^{t+1}(π_{−1} − ī)`, which is unbounded unless `π_{−1} = ī` | `StaticIS.adaptive_peg`, `StaticIS.adaptive_peg_unbounded`, `StaticIS.adaptive_peg_bounded_iff` |
| Cochrane p. 398 | `i = π` is a steady state of both models | `StaticIS.adaptive_steady_state`, `StaticIS.re_steady_state` |
| Cochrane p. 399 | the old-Keynesian mechanism: a high real rate lowers output, and low output lowers inflation | `StaticIS.adaptive_mechanism` |
| Cochrane (17.5), (17.7), p. 398 | rational expectations `πᵉ_t = E_tπ_{t+1}`: (17.7) `E_tπ_{t+1} = π_t/(1 + σκ) + σκi_t/(1 + σκ)`; rearranged, `E_tπ_{t+1} − π_t = σκ(i_t − E_tπ_{t+1})`; a high real rate raises expected inflation | `StaticIS.REModel`, `StaticIS.reModel_iff_static`, `StaticIS.reModel_iff_17_7`, `StaticIS.re_change`, `StaticIS.re_mechanism` |
| Cochrane p. 398, "the coefficient `1/(1 + σκ) < 1`" | the coefficient lies in `(0, 1)` and the two coefficients sum to one | `StaticIS.coeff_17_7` |
| Cochrane pp. 398–400, "stable but indeterminate" | the family driven by expectational errors `δ`: for every `π_0` known at date 0 and every adapted martingale-difference `δ` it is an equilibrium with errors `δ`, and every equilibrium is a member; bounded inputs give a bounded member; for every initial inflation there is a bounded equilibrium, so (17.7) never has a unique one | `StaticIS.reFamily`, `StaticIS.reFamily_succ`, `StaticIS.reFamily_adapted`, `StaticIS.reFamily_solves`, `StaticIS.reErr`, `StaticIS.reErr_mds`, `StaticIS.eq_reFamily`, `StaticIS.reFamily_bounded`, `StaticIS.re_indeterminate`, `StaticIS.re_not_unique` |

## §17.2 Responses to interest-rate changes, pp. 399–401 (StaticIS, RulesAdaptiveRE)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (17.8), p. 400, finite start | `π_{t+1} = aᵗ⁺¹π_0 + b∑_{j≤t} aʲi_{t−j} + ∑_{j≤t} aʲδ_{t+1−j}`, `a = 1/(1 + σκ)`, `b = σκ/(1 + σκ)` | `StaticIS.reFamily_closed` |
| Cochrane (17.8), p. 400, infinite past | on ℤ, every bounded path solving the recursion with bounded `i`, `δ` is the backward moving average (17.8), and conversely (pathwise) | `StaticIS.eq_17_8`, `SharedTools.backward_series_solves` |
| Cochrane Fig. 17.1, p. 399 | adaptive model, permanent rise of the rate from 0 to 1: `π_t = 1 − (1 + σκ)^{t+1}`, inflation spirals down, faster when prices are less sticky | `StaticIS.fig17_1_path`, `StaticIS.fig17_1_tendsto`, `StaticIS.fig17_1_less_sticky` |
| Cochrane Fig. 17.2, p. 400 | rational expectations, `δ = 0`: `π_t = 1 − (1 + σκ)^{−t}` is an equilibrium, rises strictly to 1, higher at every date when prices are less sticky, and tends to the frictionless `π_1 = 1` as `κ → ∞` | `StaticIS.fig17_2_solves`, `StaticIS.fig17_2_strictMono`, `StaticIS.fig17_2_tendsto`, `StaticIS.fig17_2_less_sticky`, `StaticIS.fig17_2_frictionless_limit` |
| Cochrane Fig. 17.2, p. 400, dashed lines | every date-1 value `π_1 = c` starts a path `π_{t+1} = 1 + (c − 1)(1 + σκ)^{−t}` that obeys (17.7) and converges to 1 | `StaticIS.fig17_2_dashed` |
| Cochrane p. 402 | the frictionless limit of (17.7): as `κ → ∞` the coefficients tend to 0 and 1, the Fisher relation | `StaticIS.tendsto_coeff_17_7` |
| Cochrane p. 401 | a fully expected rate path brings no expectational errors after the announcement, so the path is pinned down by announcement-date inflation | `StaticIS.no_surprise_of_known`, `StaticIS.eq_reFamily_of_known` |
| Cochrane p. 401 | "active fiscal policy likewise selects one equilibrium": fixing unexpected inflation by a fiscal shock makes the equilibrium unique | `StaticIS.fiscal_selects` |
| Cochrane p. 401 | with `i_t = i*_t + φ(π_t − π*_t)` deviations obey `E_td_{t+1} = (1 + σκφ)/(1 + σκ)·d_t`; for `φ > 1` the bank selects any bounded equilibrium `π*` of the peg model, so any value of unexpected inflation | `RulesAdaptiveRE.deviation_eq`, `RulesAdaptiveRE.rule_selects`, `RulesAdaptiveRE.rule_selects_any_delta` |

## §17.3 Rational expectations responses with policy rules, pp. 401–403 (RulesAdaptiveRE)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (17.9), p. 402 | with `i_t = φπ_t + u_t`, `π_t = (1 + σκ)/(1 + σκφ)·πᵉ_t − σκ/(1 + σκφ)·u_t` | `RulesAdaptiveRE.eq_17_9` |
| Cochrane (17.10), p. 402 | the adaptive model with the rule; its solution from `π_{−1}`, unique for every rule with `1 + σκφ ≠ 0`; undisturbed, `π_t = cᵗ⁺¹π_{−1}` | `RulesAdaptiveRE.AdaptiveRule`, `RulesAdaptiveRE.adaptiveRule_iff_17_10`, `RulesAdaptiveRE.adaptiveRulePath`, `RulesAdaptiveRE.adaptiveRule_existsUnique`, `RulesAdaptiveRE.adaptiveRule_homog` |
| Cochrane p. 402 (E7) | `\|1 + σκ\| < \|1 + σκφ\|` iff `φ > 1` or `φ < −1 − 2/(σκ)`; so the coefficient of (17.10) has modulus below one exactly there | `RulesAdaptiveRE.abs_lt_abs_iff`, `RulesAdaptiveRE.abs_coeff_lt_one_iff` |
| Cochrane p. 402 (E7) | the adaptive model with a rule is stable iff `φ > 1` or `φ < −1 − 2/(σκ)`; "`\|φ\| > 1` stabilizes" fails at `σ = 1`, `κ = 1/2`, `φ = −3/2` (coefficient 6); at `φ = −1 − 2/(σκ)` the coefficient is `−1` | `RulesAdaptiveRE.AdaptiveStable`, `RulesAdaptiveRE.adaptiveStable_iff`, `RulesAdaptiveRE.printed_abs_phi_gt_one_stabilizes_false`, `RulesAdaptiveRE.boundary_coeff` |
| Cochrane p. 402 | "passive `\|φ\| < 1` produces unstable inflation" (true): undisturbed paths diverge; in the stable case bounded disturbances give bounded inflation | `RulesAdaptiveRE.passive_unstable`, `RulesAdaptiveRE.unstable_diverges`, `RulesAdaptiveRE.adaptiveRule_bounded` |
| Cochrane (17.11), p. 402 | the rational-expectations model with the rule: `E_tπ_{t+1} = (1 + σκφ)/(1 + σκ)·π_t + σκ/(1 + σκ)·u_t`, and its undivided form | `RulesAdaptiveRE.RERule`, `RulesAdaptiveRE.reRule_iff_17_11`, `RulesAdaptiveRE.reRule_iff_scalar` |
| Cochrane p. 402 (E7) | (17.11) is determinate iff `φ > 1` or `φ < −1 − 2/(σκ)`; the coefficient has modulus below one iff `−1 − 2/(σκ) < φ < 1`; "`φ < 1` is indeterminate" fails at `σ = 1`, `κ = 1/2`, `φ = −6`; it holds on `[−1 − 2/(σκ), 1]` | `RulesAdaptiveRE.REDeterminate`, `RulesAdaptiveRE.reDeterminate_iff`, `RulesAdaptiveRE.re_coeff_abs_lt_one_iff`, `RulesAdaptiveRE.printed_passive_indeterminate_false`, `RulesAdaptiveRE.passive_indeterminate` |
| Cochrane p. 402 | the frictionless case (16.4) is the `κ → ∞` limit of (17.11) | `RulesAdaptiveRE.tendsto_coeff_17_11` |
| Cochrane p. 403 | the forward solution `π_t = −σκ/(1 + σκφ)∑((1 + σκ)/(1 + σκφ))ʲE_tu_{t+j}` is the unique bounded equilibrium when (17.11) is determinate | `RulesAdaptiveRE.forward_solution` |

## §17.3.1 Responses with policy rules, pp. 403–406 (AR1Responses, PersistenceFreedom)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (17.12), p. 403 | the denominator `φ − η + (1 − η)/(σκ)`, nonzero for a determinate rule and `\|η\| ≤ 1`, positive for `φ > 1`, `η ≤ 1` | `AR1Responses.den`, `AR1Responses.den_mul`, `AR1Responses.den_ne_zero`, `AR1Responses.den_pos` |
| Cochrane (17.12), p. 403 | with an AR(1) disturbance the unique bounded equilibrium of (17.11) is `π_t = −u_t/(φ − η + (1 − η)/(σκ))`; the two printed forms agree, and so does the forward series | `AR1Responses.ar1_solves`, `AR1Responses.eq_17_12`, `AR1Responses.coeff_17_12_forms`, `AR1Responses.eq_17_12_series` |
| Cochrane (17.13), p. 404 | `i_t = −(η − (1 − η)/(σκ))/den·u_t`, both printed forms | `AR1Responses.coeff_17_13_forms`, `AR1Responses.eq_17_13` |
| Cochrane p. 404 | the frictionless limits `κ → ∞` of (17.12)–(17.13) are (16.9) and (16.11) | `AR1Responses.tendsto_17_12`, `AR1Responses.tendsto_17_13` |
| Cochrane p. 404 | `η = 1` is super-Fisherian: `π_t = i_t = −u_t/(φ − 1)` | `AR1Responses.superFisher_simple` |
| Cochrane p. 405 | open mouth at `η = 1/(1 + σκ)`: `π_t = −u_t/φ`, `i_t = 0`; for `φ > 1` the rate moves with the disturbance iff `η < 1/(1 + σκ)` | `AR1Responses.openMouth_simple`, `AR1Responses.num_pos_iff`, `AR1Responses.i_coeff_pos_iff` |
| Cochrane Fig. 17.3, p. 404 | `σ = 1`, `κ = 1/2`: the threshold is `2/3`; at `η = 0.3` the rate moves with the disturbance, at `η = 0.9` against it, at `η = 2/3` not at all | `AR1Responses.fig17_3` |
| Cochrane (17.14), p. 405 | `(i*, π*)` is an equilibrium pair iff `i*_t = (1 + 1/(σκ))E_tπ*_{t+1} − π*_t/(σκ)` | `PersistenceFreedom.eq_17_14` |
| Cochrane (17.14), p. 405 (E8) | the inverse needs past expectational errors: on ℤ, `E_tπ*_{t+1} = σκ/(1 + σκ)∑(1 + σκ)^{−j}i*_{t−j} + ∑_{j≥1}(1 + σκ)^{−j}δ_{t+1−j}`; the printed form holds with no past surprises and fails for a single `δ_1 = 1` | `PersistenceFreedom.corrected_inverse`, `PersistenceFreedom.printed_inverse_of_no_surprise`, `PersistenceFreedom.printed_inverse_false` |
| Cochrane p. 405 | "any value of unexpected inflation is consistent with any persistence of the interest-rate target": for news `ε` revealed at date 1, every bounded rate path and every `c` there is a bounded equilibrium with `ΔE_1π*_1 = cε`, also on the coin-flip tree; a permanent rise with a negative response and a one-period rise with a positive one | `PersistenceFreedom.targetPath`, `PersistenceFreedom.shockRate`, `PersistenceFreedom.shockInfl`, `PersistenceFreedom.targetPath_bounded`, `PersistenceFreedom.any_sign`, `PersistenceFreedom.any_sign_coin`, `PersistenceFreedom.permanent_negative`, `PersistenceFreedom.transitory_positive` |
| Cochrane p. 406 | the long-run response is +1 in every equilibrium: if the rate converges and expectational errors die out, inflation converges to the rate; in particular after an announcement | `PersistenceFreedom.long_run_one`, `PersistenceFreedom.any_sign_long_run` |

## §17.3.2 Adaptive expectations responses with policy rules, pp. 406–407, Figure 17.4 (AdaptiveTaylor)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 406 | the AR(2) `(1 − cL)(1 − ηL)π_t = −σκ/(1 + φσκ)·ε_t`, `c = (1 + σκ)/(1 + φσκ)`; its first factor is (17.10) | `AdaptiveTaylor.ar2`, `AdaptiveTaylor.ar1_form` |
| Cochrane p. 406 | for `φ > 1`, `c ∈ (0, 1)` | `AdaptiveTaylor.fig17_4_coeff` |
| Cochrane Fig. 17.4, p. 407 | a permanent disturbance from date 0: `π_t = −(1 − cᵗ⁺¹)/(φ − 1)` and `i_t = 1 − φ(1 − cᵗ⁺¹)/(φ − 1)` | `AdaptiveTaylor.fig17_4_path`, `AdaptiveTaylor.fig17_4_rate` |
| Cochrane p. 406, Fig. 17.4 | the rate first rises (`i_0 > 0`), inflation declines, the rate then falls and reverses course, and both converge to `−1/(φ − 1)` | `AdaptiveTaylor.fig17_4_i_zero`, `AdaptiveTaylor.fig17_4_infl_strictAnti`, `AdaptiveTaylor.fig17_4_i_strictAnti`, `AdaptiveTaylor.fig17_4_i_reverses`, `AdaptiveTaylor.fig17_4_tendsto` |
| Cochrane p. 406 | for `φ > 1` bounded disturbances give bounded inflation and transitory ones die out | `AdaptiveTaylor.taylor_bounded`, `AdaptiveTaylor.taylor_transitory` |
| Cochrane p. 406 | if the rate cannot move: a deflation spiral at the zero bound, an inflation spiral under a too-low peg (Friedman) | `AdaptiveTaylor.peg_spiral` |

## §17.4–§17.4.1 Full-model responses; interest rates and inflation, pp. 407–410, Figures 17.5–17.6 (FullModel, PersistenceFreedom, FiscalUnderpinnings)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (17.15)–(17.17), p. 407 | the IS curve, the Fisher equation (defining `r_t = i_t − E_tπ_{t+1}`), the Phillips curve, with disturbances | `FullModel.IS`, `FullModel.Fisher`, `FullModel.PC`, `FullModel.Model`, `FullModel.fisher_iff` |
| Cochrane (17.18), p. 408 | eliminating `x` and `r`: `σκi_t = −βE_tπ_{t+2} + (1 + β + σκ)E_tπ_{t+1} − π_t` (no disturbances), and the iff form with disturbances for `κ ≠ 0` | `FullModel.eq_17_18`, `FullModel.eq_17_18_shocks` |
| Cochrane (17.15)–(17.18), pp. 407–408 | the perfect-foresight model as sequences; it is the model under `perfectForesight`; equilibria are output from the Phillips curve and inflation solving (17.18) | `FullModel.PFEqm`, `FullModel.pf_model_iff`, `FullModel.BoundedS`, `FullModel.Second`, `FullModel.pfEqm_iff_second` |
| Cochrane (5.6), p. 119; A1 p. 570; p. 408 (restated from the Chapter 5 project) | the roots `λ₁ > 1 > λ₂ > 0` of `λ² − (1 + β + σκ)λ + β`, their sum and product, `σκ = (λ₁ − 1)(1 − λ₂)` | `FullModel.lam1`, `FullModel.lam2`, `FullModel.disc_pos`, `FullModel.lam_sum`, `FullModel.lam_prod`, `FullModel.sigma_kappa_eq`, `FullModel.lam2_lt_lam1`, `FullModel.one_lt_lam1`, `FullModel.lam2_lt_one`, `FullModel.lam2_pos` |
| Cochrane (5.5), p. 119 | the forward sum `F_t = ∑ qᵏi_{t+k}`: summable, recursive, bounded, the unique bounded solution of `G_t = i_t + qG_{t+1}` | `FullModel.F`, `FullModel.F_summable`, `FullModel.F_rec`, `FullModel.F_bound`, `FullModel.homog_zero`, `FullModel.F_unique` |
| Cochrane (5.5), p. 119; A1 §1.7, p. 570 | factoring the lag polynomial: bounded `π` solves (17.18) iff `λ₁π_{t+1} = π_t + σκF_t` | `FullModel.factor_identity`, `FullModel.second_iff_factor` |
| Cochrane p. 408 | for bounded `i` and every initial inflation `p` there is exactly one bounded solution with `π_0 = p`; bounded equilibria are indexed by `π_0` | `FullModel.path`, `FullModel.path_factor`, `FullModel.path_bounded`, `FullModel.pf_existsUnique`, `FullModel.pf_eqm_iff` |
| Cochrane pp. 137–138 (restated from the Chapter 5 project) | `\|x_{t+1}\| ≤ c\|x_t\| + F`, `0 ≤ c < 1`, gives a uniform bound | `FullModel.bounded_of_rec` |
| Cochrane p. 408; A1 p. 570 | long-run response 1: if `i_t → ī`, every bounded equilibrium has `π_t → ī` and `x_t → (1 − β)ī/κ` | `FullModel.tendsto_of_rec`, `FullModel.tendsto_F`, `FullModel.tendsto_pi`, `FullModel.tendsto_x` |
| Cochrane (5.5), p. 119; p. 408 | the two-sided moving average `π_t = c[∑_{j<t} λ₁^{−j}i_{t−1−j} + λ₂F_t]`, `c = σκ/(λ₁ − λ₂) > 0`, is the path with no initial expectational error | `FullModel.coef`, `FullModel.coef_mul`, `FullModel.coef_pos`, `FullModel.twoSided`, `FullModel.twoSided_factor`, `FullModel.twoSided_eq` |
| Cochrane Fig. 17.5, p. 408 | the permanent rise `i_t = 1{t ≥ T}` announced at date 0, and its forward sum `F_t = q^{T−t}/(1 − q)` | `FullModel.stepI`, `FullModel.stepI_bound`, `FullModel.stepI_tendsto`, `FullModel.F_step` |
| Cochrane Fig. 17.5, pp. 408–409 | the no-surprise response is the two-sided moving average; up to the rise `π_t = cλ₂^{T−t+1}/(1 − λ₂)`, so inflation rises before the rate; it is positive, strictly increasing, below one and converges to one | `FullModel.antPath`, `FullModel.antPath_twoSided`, `FullModel.antPath_second`, `FullModel.antPath_le_T`, `FullModel.antPath_pos`, `FullModel.antPath_strictMono`, `FullModel.antPath_lt_one`, `FullModel.antPath_tendsto_one` |
| Cochrane p. 409, "output declines" | output is negative iff `π_t < βπ_{t+1}`; along the response it is negative up to and including the date of the rise, and converges to `(1 − β)/κ` | `FullModel.x_neg_iff`, `FullModel.antPath_x_neg`, `FullModel.antPath_x_tendsto` |
| Cochrane p. 409 | "expected future interest-rate rises increase inflation today": for every initial inflation, at every date `t ≥ 1` | `FullModel.rise_raises_inflation` |
| Cochrane Fig. 17.5, p. 409 | the dashed (unexpected) response joins the solid (anticipated) one at the date of the rise | `FullModel.dashed_joins_solid` |
| Cochrane p. 410 | "the original `δ₁ = 0` equilibrium already had a little jump" | `FullModel.antPath_zero_pos` |
| Cochrane Fig. 17.5, p. 409, anticipated from the infinite past | on ℤ: the step, its forward sum, the closed form `zPath`; it solves (17.18), is bounded, and is the only bounded path (uniqueness for every bounded rate path); it depends only on `t − T` | `FullModel.SecondZ`, `FullModel.BoundedZ`, `FullModel.stepZ`, `FullModel.GZ`, `FullModel.GZ_rec`, `FullModel.zPath`, `FullModel.zPath_factor`, `FullModel.zPath_bounded`, `FullModel.zPath_second`, `FullModel.secondZ_unique`, `FullModel.zPath_existsUnique`, `FullModel.zPath_shift` |
| Cochrane Fig. 17.5, pp. 409–410 | the response announced at date 0 (or `−N`) coincides with `zPath` from the announcement on; two responses differ by `(p − q)λ₁^{−n}`; as the announcement recedes every response converges to `zPath` | `FullModel.zPath_eq_antPath`, `FullModel.antPath_eq_zPath_shift`, `FullModel.path_sub_path`, `FullModel.tendsto_zPath` |
| Cochrane Fig. 17.6, pp. 409–410 | equilibria A–E: every initial inflation (super-neutral, none, negative) gives a bounded equilibrium converging to one | `FullModel.fig17_6_any_jump` |
| Cochrane pp. 410, 416 | full model: for every bounded rate path and every announcement-date inflation exactly one bounded equilibrium, converging to the rate; `η* = 1/λ₁`, and the roots of `βλ² − (1 + β + σκ)λ + 1` are `η*` and `1/λ₂ > 1` | `PersistenceFreedom.full_any_sign`, `PersistenceFreedom.full_long_run`, `PersistenceFreedom.etaStar_eq_inv_lam1`, `PersistenceFreedom.etaStar_mul_inv_lam2`, `PersistenceFreedom.one_lt_inv_lam2` |
| Cochrane Fig. 17.6, p. 410 (E24) | after an unexpected permanent rise `π_j = 1 + (p − 1)λ₁^{−j}`; the surplus change `Δs(p)` from (17.19) with `ρ < 1`, a percentage of steady-state surpluses; `Δs(p) = (1 − p)/(λ₁ − ρ) − p` | `FiscalUnderpinnings.path_step0`, `FiscalUnderpinnings.deltaS`, `FiscalUnderpinnings.permanent_surplus_pct`, `FiscalUnderpinnings.deltaS_closed` |
| Cochrane Fig. 17.6, p. 410 | B has `Δs = −1` for every parameter value (printed −1.00); D has `Δs = 1/(λ₁ − ρ) > 0`; C (`Δs = 0`) is `p = 1/(1 + λ₁ − ρ)`, not the `ΔE₁π₁ = 0` equilibrium | `FiscalUnderpinnings.deltaS_B`, `FiscalUnderpinnings.deltaS_D`, `FiscalUnderpinnings.deltaS_zero_iff` |
| Cochrane Fig. 17.6, p. 410 (new correction) | for any parameters, the printed D (1.66) and `δ = 0` (0.67) values force `Δs < −1.9` at `δ₁ = +1` and `Δs > 3.2` at `δ₁ = −1`, against the printed A = −1.53 and E = 2.99; the printed A and E fit jumps in `(0.82, 0.84)` and `(−0.88, −0.86)` | `FiscalUnderpinnings.fig17_6_inconsistent`, `FiscalUnderpinnings.fig17_6_implied_jumps` |

## §17.4.2 The fiscal underpinnings of new-Keynesian models, pp. 411–415, Figure 17.7 (FiscalUnderpinnings)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (17.19), p. 411 | the innovation `ΔE_{t+1}`, its linearity, zero on known variables; the flow condition `ρv_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`; the ex-ante real rate (17.16) and its news | `FiscalUnderpinnings.innov`, `FiscalUnderpinnings.innov_sub`, `FiscalUnderpinnings.innov_known`, `FiscalUnderpinnings.Flow`, `FiscalUnderpinnings.rea`, `FiscalUnderpinnings.innov_rea_self`, `FiscalUnderpinnings.innov_expost_eq` |
| Cochrane (17.19), p. 411 | the exact finite-horizon identity | `FiscalUnderpinnings.innov_finite` |
| Cochrane (17.19), p. 411 | as printed, with `r_{t+1+j}` the ex-ante rate earned between `t + j` and `t + 1 + j`; with (17.16)'s dating the real-rate sum carries a factor `ρ`, and the printed form then holds iff `ρ = 1` or there is no real-rate news; the ex-post reading makes the `j = 0` term `−ΔE_{t+1}π_{t+1}` | `FiscalUnderpinnings.eq_17_19`, `FiscalUnderpinnings.eq_17_19_own_dating`, `FiscalUnderpinnings.printed_own_dating_iff`, `FiscalUnderpinnings.expost_first_term` |
| Cochrane (17.19), p. 411 | for bounded processes and `0 ≤ ρ < 1` the innovation passes through the sums, the printed `ΔE∑` form | `FiscalUnderpinnings.innov_tsum`, `FiscalUnderpinnings.eq_17_19_bounded` |
| Cochrane p. 411 | "for higher interest rates to lower inflation, there must be a fiscal contraction" | `FiscalUnderpinnings.fiscal_contraction` |
| Cochrane pp. 411–412 | at 100% debt to GDP, a point of unexpected disinflation needs a point of GDP of surplus news | `FiscalUnderpinnings.surplus_gdp` |
| Cochrane p. 414 | reverse engineering: for every bounded rate path and initial inflation a disturbance `u = i − φπ` produces them; different initial inflations give different disturbances | `FiscalUnderpinnings.reverse_engineer`, `FiscalUnderpinnings.reverse_engineer_distinct` |
| Cochrane Fig. 17.7, p. 413; p. 414 | for `i_n = ηⁿ`, `π_n = cηⁿ + (π₁ − c)μⁿ` with `μ = 1/λ₁` solves (17.18) and is the unique bounded path with that initial inflation | `FiscalUnderpinnings.cAR`, `FiscalUnderpinnings.piAR`, `FiscalUnderpinnings.piAR_second`, `FiscalUnderpinnings.piAR_eq_path` |
| Cochrane p. 412, Fig. 17.7 | the required surplus `Σs = −π₁ + ∑(i_n − π_{n+1})` and its closed form | `FiscalUnderpinnings.sigmaS`, `FiscalUnderpinnings.sigmaS_closed` |
| Cochrane Fig. 17.7, p. 413 | at `σ = 1`, `κ = 0.25`, `β = 0.95`, `η = 0.6`: `c = −125/11`, `λ₁ = (2.2 + √1.04)/2`, interval bounds | `FiscalUnderpinnings.fig17_7_params`, `FiscalUnderpinnings.fig17_7_c`, `FiscalUnderpinnings.fig17_7_lam1`, `FiscalUnderpinnings.fig17_7_lam1_bounds`, `FiscalUnderpinnings.fig17_7_L_bounds`, `FiscalUnderpinnings.fig17_7_sigmaS` |
| Cochrane Fig. 17.7, p. 413 | `π₁ = −1, −0.5, 0, 0.5` require `Σs = 3.55, 2.23, 0.91, −0.41`; 2.55 of the first from real rates | `FiscalUnderpinnings.fig17_7_values`, `FiscalUnderpinnings.fig17_7_real_rates` |
| Cochrane Fig. 17.7, p. 414 | with `π₁ = 0` inflation then slightly rises, `π₂ ∈ (0, 0.25)` | `FiscalUnderpinnings.fig17_7_zero_panel` |
| Cochrane p. 414 | the reverse-engineered disturbances are not AR(1) (at `φ = 1.2`, for every `π₁ ≠ c`) | `FiscalUnderpinnings.not_geometric`, `FiscalUnderpinnings.fig17_7_u_not_ar1` |
| Cochrane p. 413 | `5 × 3.55 = 17.75 ≈ 18` percent of GDP | `FiscalUnderpinnings.fig17_7_times_five` |
| Cochrane p. 414 (E10) | `5 × 2.23 = 11.15`, not 11.5; $2.23 trillion matches the printed $2.2 trillion | `FiscalUnderpinnings.e10` |
| Cochrane p. 414 | fed the reverse-engineered disturbance, the standard rule with `φ > 1` has the given paths as its unique bounded equilibrium | `TaylorDeterminacy.reverse_engineered_unique` |

## §17.4.3 Responses to AR(1) monetary policy disturbances, pp. 415–416, Figure 17.8; Online Appendix A1 §1.13.1, pp. 586–588, and §1.8, pp. 571–572 (AR1Responses)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (17.15)–(17.17), (17.20), p. 415; A1 p. 586 | the three-equation model with the rule `i_t = φπ_t + u_t` substituted | `AR1Responses.ThreeEq` |
| Cochrane A1 (1.59)–(1.62), p. 588 | undetermined coefficients: the guess solves the model iff (1.59); (1.59) iff `απ = −1/denF` (1.60) and `αx = (1 − βη)/κ·απ` (1.61); then `i_t = (η − (1 − βη)(1 − η)/(σκ))π_t` (1.62) | `AR1Responses.denF`, `AR1Responses.denF_mul`, `AR1Responses.denF_pos`, `AR1Responses.msv_solves`, `AR1Responses.coeffs_of_msv`, `AR1Responses.eq_1_59_iff`, `AR1Responses.msv_i_eq` |
| Cochrane A1 (1.55), p. 586; p. 420 | the transition matrix `A = P⁻¹Q` of the forward-looking form, its entries, and the vector system it solves | `AR1Responses.transA`, `AR1Responses.transA_explicit`, `AR1Responses.threeEq_solves` |
| Cochrane A1 pp. 587–588; p. 415 | for `φ > 1`, `A` is Schur-stable and the MSV solution is the unique bounded equilibrium | `AR1Responses.schurStable_of_one_lt`, `AR1Responses.msv_unique` |
| Cochrane A1 p. 588 | (1.60) generalises (17.12) (`β = 0`) and (16.9) (`κ → ∞`) | `AR1Responses.msv_beta_zero`, `AR1Responses.tendsto_1_60` |
| Cochrane A1 §1.8, p. 572 | the lag-operator solution `−σκ/((1 + σκφ)(1 − λ₁η)(1 − λ₂η))u` equals (1.60): the factorisation with possibly complex roots, partial fractions, geometric sums | `AR1Responses.lag_form`, `AR1Responses.lag_factor`, `AR1Responses.partial_fractions`, `AR1Responses.lag_sum_ar1` |
| Cochrane A1 §1.8, p. 572 (E11) | for `φ > 1` both lag roots have modulus below one; at `φ = 1.5`, `β = 0.99`, `σ = 1`, `κ = 0.5` they are complex | `AR1Responses.lag_roots_norm_lt_one`, `AR1Responses.lag_roots_complex_example` |
| Cochrane p. 415 | `η = 1`, super-Fisherian: `π = i = −u/(φ − 1)`, `x = (1 − β)/κ·π`; a negative disturbance raises the rate and output | `AR1Responses.superFisher_full`, `AR1Responses.superFisher_full_signs` |
| Cochrane p. 416 | the open-mouth persistence `η*` is the unique root with `η ≤ 1` of `βη² − (1 + β + σκ)η + 1 = 0`, in `(0, 1)`; there `i = 0` and `π = −u/φ` | `AR1Responses.openMouth_iff_quadratic`, `AR1Responses.etaStar`, `AR1Responses.etaStar_root`, `AR1Responses.etaStar_mem`, `AR1Responses.quad_sub`, `AR1Responses.eq_etaStar`, `AR1Responses.openMouth_full` |
| Cochrane p. 416, Fig. 17.8 | at `β = 0.95`, `κ = 1/2`, `σ = 1`, `0.508 < η* < 0.509` (printed 0.51) | `AR1Responses.etaStar_fig17_8` |
| Cochrane pp. 415–416, Fig. 17.8 | a negative disturbance lowers the rate and raises inflation iff `η < η*`; the `η = 0.3`, `φ = 1.5` panel | `AR1Responses.full_i_coeff_pos_of_lt`, `AR1Responses.full_i_coeff_neg_of_gt`, `AR1Responses.fig17_8_transitory` |

## §17.5.1 Optimal policy, pp. 417–420 (OptimalPolicy, TaylorDeterminacy)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (17.22), pp. 417–418 | King's rule `i_t = i*_t + φ(π_t − π*_t)` is `i_t = φπ_t + u_{i,t}` with `u_{i,t} = i*_t − φπ*_t`; the starred paths satisfy it for every `φ` | `OptimalPolicy.KingRule`, `OptimalPolicy.king_iff_standard`, `OptimalPolicy.king_equilibrium` |
| Cochrane (17.23)–(17.24), p. 417 | the starred model is (17.15)–(17.17) | `OptimalPolicy.Starred`, `OptimalPolicy.starred_iff_model` |
| Cochrane (17.27), p. 418 | `(i*, x*, π*)` solves the starred model iff `x*` comes from the Phillips curve and `i*` is (17.27) | `OptimalPolicy.eq_17_27` |
| Cochrane (17.25), p. 417 | zero inflation: `x* = −u_π/κ`, `i* = (−E_tu_{π,t+1} + u_{π,t})/(σκ) + u_x/σ` | `OptimalPolicy.eq_17_25` |
| Cochrane (17.26), p. 417 | zero output gap: `π* = E_t∑βʲu_{π,t+j}` is the unique bounded inflation, `i* = E_t∑βʲu_{π,t+1+j} + u_x/σ` | `OptimalPolicy.E_forwardSeries_succ`, `OptimalPolicy.eq_17_26` |
| Cochrane p. 418 (E9) | with `x* = 0` the intercept is `(1 − φβ)E_t∑βʲu_{π,t+1+j} − φu_{π,t} + u_x/σ`, not `(1 − φ)E_t∑βʲu_{π,t+1+j} + u_x/σ`; the difference `φ[(1 − β)S − u_π]`; `−160/67` against the printed `−70/67` at `ρ = 0.7`, `β = 0.95`, `φ = 1.5` | `OptimalPolicy.e9_intercept`, `OptimalPolicy.e9_difference`, `OptimalPolicy.e9_counterexample` |
| Cochrane p. 418 | any inflation path, and any output path, is attainable exactly, with bounded rates when the target is bounded | `OptimalPolicy.boundedProc_E`, `OptimalPolicy.boundedProc_add_smul`, `OptimalPolicy.any_pi_attainable`, `OptimalPolicy.any_x_attainable` |
| Cochrane p. 418 | Woodford's loss `λV(x) + (1 − λ)V(π)`; `x* = 0` and `π* = 0` are its corners | `OptimalPolicy.woodfordLoss`, `OptimalPolicy.loss_corner_x`, `OptimalPolicy.loss_corner_pi` |
| Cochrane (17.28), p. 419 | the rule with long-run target and systematic responses has total inflation coefficient `θ_π + φ_π` | `OptimalPolicy.Rule1728`, `OptimalPolicy.rule_17_28_eq` |
| Cochrane p. 419 | without a time-varying intercept `φ` cannot stabilise inflation: zero inflation under `i = φπ + c` pins the IS disturbance, so with a geometric cost-push shock no `(φ, c)` works; zero output forces `φ = ρ`, `c = 0` | `OptimalPolicy.pi_zero_constant_intercept`, `OptimalPolicy.no_rule_stabilises_inflation`, `OptimalPolicy.x_zero_constant_intercept` |
| Cochrane pp. 419–420, φ irrelevance | an equilibrium under King's rule in deviations; for every `φ` in the determinacy region the bounded equilibria are exactly the starred paths, so the equilibrium set does not depend on `φ`; the standard rule with `u = i* − φπ*` has them as unique equilibrium | `TaylorDeterminacy.KingEqm`, `TaylorDeterminacy.deviation_of_eqm`, `TaylorDeterminacy.phi_irrelevance`, `TaylorDeterminacy.phi_irrelevance_sets`, `TaylorDeterminacy.standard_rule_unique`, `TaylorDeterminacy.pf_starred` |

## §17.5.2 Determinacy, pp. 420–421; Online Appendix A1 (1.55)–(1.58), pp. 586–587 (TaylorDeterminacy)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 420; A1 p. 587 | a system `Px_t = QE_tx_{t+1}` is determinate iff `det P ≠ 0` and `P⁻¹Q` is Schur-stable; with `det P = 0` a one-period blip solves it | `TaylorDeterminacy.StructSolves`, `TaylorDeterminacy.StructDeterminate`, `TaylorDeterminacy.solve2`, `TaylorDeterminacy.struct_iff_solves`, `TaylorDeterminacy.not_determinate_of_det_zero`, `TaylorDeterminacy.structDeterminate_iff` |
| Cochrane (17.29)–(17.32), p. 420, with an output response | the deviation system with `ĩ = φπ̃ + φ_xx̃`, its structural form, and determinacy | `TaylorDeterminacy.Deviation`, `TaylorDeterminacy.stack`, `TaylorDeterminacy.deviation_iff_struct`, `TaylorDeterminacy.Determinate`, `TaylorDeterminacy.determinate_iff_struct` |
| Cochrane p. 420; A1 p. 587 | determinate iff `D = 1 + σφ_x + σκφ ≠ 0` and `SchurStable (T/D) (β/D)`, `T = 1 + β + σκ + βσφ_x`; explicit inequalities | `TaylorDeterminacy.determinate_iff`, `TaylorDeterminacy.schur_div_pos`, `TaylorDeterminacy.schur_div_neg`, `TaylorDeterminacy.determinate_iff_explicit` |
| Cochrane A1 (1.58), p. 587; p. 420 | with `φ_x = 0`: determinate iff `φ > 1` or `φ < −(1 + 2(1 + β)/(σκ))` | `TaylorDeterminacy.determinate_iff_phi` |
| Cochrane Ch. 16 p. 369; A1 p. 587 (restated from Galí's Bullard–Mitra condition) | for `φ, φ_x ≥ 0`: determinate iff `κ(φ − 1) + (1 − β)φ_x > 0` | `TaylorDeterminacy.determinate_iff_BM` |
| Cochrane p. 420; A1 p. 587; Ch. 16 p. 369; Ch. 12 p. 328 | "`φ > 1` is neither necessary nor sufficient": `i = 0.5π + 2x` is determinate; every `φ ∈ [0, 1)` is made determinate by a large output response; `φ = −5` is determinate with `φ_x = 0` | `TaylorDeterminacy.not_necessary_witness`, `TaylorDeterminacy.not_necessary_phix`, `TaylorDeterminacy.not_necessary_negative` |
| Cochrane p. 420; Ch. 16 p. 369; Ch. 12 p. 328 | non-sufficiency needs `φ_x < 0`: `i = 2π − 2x` is not determinate, every `φ` is undone by `φ_x = −(1 + σκφ)/σ`; with `φ_x ≥ 0`, `φ > 1` is sufficient, and output responses widen the region | `TaylorDeterminacy.not_sufficient_witness`, `TaylorDeterminacy.not_sufficient`, `TaylorDeterminacy.sufficient_of_phix_nonneg`, `TaylorDeterminacy.widens_with_phix` |
| Cochrane (17.33), p. 420 | `E_t(x̃, π̃)' = β⁻¹[[β + σκ + βσφ_x, −σ(1 − βφ)], [−κ, 1]](x̃, π̃)`; (17.33) is `φ_x = 0` | `TaylorDeterminacy.deviation_iff_17_33`, `TaylorDeterminacy.Mmat` |
| Cochrane A1 (1.55), p. 586 | the model with the rule and disturbances in forward form, with the `u_x` entry `−β` inside the `1/β`; the printed `−1` is right only if `β = 1` or `u_x = 0` | `TaylorDeterminacy.eq_1_55`, `TaylorDeterminacy.printed_1_55_iff` |
| Cochrane A1 (1.57), p. 587 | `tr M = (1 + β + σκ)/β`, `det M = (1 + σκφ)/β`, the discriminant, and the printed eigenvalues are the roots of `λ² − tr M·λ + det M` | `TaylorDeterminacy.trM`, `TaylorDeterminacy.detM`, `TaylorDeterminacy.tr_det_Mmat`, `TaylorDeterminacy.discE`, `TaylorDeterminacy.discQ_eq`, `TaylorDeterminacy.eq_1_57` |
| Cochrane A1 p. 587; p. 420 | the + eigenvalue exceeds one; for `φ < 1` the − eigenvalue is below one, and above `−1` iff `φ > −(1 + 2(1 + β)/(σκ))`; for `\|φ\| < 1` exactly one stable eigenvalue | `TaylorDeterminacy.plus_root_gt_one`, `TaylorDeterminacy.roots_phi_lt_one`, `TaylorDeterminacy.abs_phi_lt_one_one_stable` |
| Cochrane p. 420; A1 p. 587 (E11) | for `φ > 1` both eigenvalues are explosive: real and above one, or complex with modulus above one | `TaylorDeterminacy.roots_phi_gt_one` |
| Cochrane p. 421 | real explosions: for `φ < 1/β` (in particular `1 < φ < 1/β`) a non-selected path has `βᵗx̃_t → −∞` | `TaylorDeterminacy.real_explosion` |

## Chapter 18, History and implications, pp. 422–432 (History)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane Ch. 18 footnote 1, p. 424 | in the permanent-income model with AR(1) income, `c_t = rk_t + r/(1 + r − η)·y_t`; the MPC is strictly increasing in `η`, hence not structural | `History.mpc`, `History.mpc_eq`, `History.pih_consumption`, `History.mpc_strictMonoOn`, `History.mpc_injective` |
| Cochrane (18.1), p. 427 | the Taylor rule with an output response; for `φ_π, φ_x ≥ 0` determinate iff `κ(φ_π − 1) + (1 − β)φ_x > 0`, so `φ_π > 1` "gives the eigenvalue you need" | `History.Rule181`, `History.rule181_determinate_iff`, `History.rule181_phi_gt_one` |
| Cochrane (18.2), p. 427 | the inertial, forward-looking rule; without inertia and forward responses it is (18.1); without inertia its deviations form a structural system, determinate iff `det P ≠ 0` and `P⁻¹Q` is Schur-stable | `History.Rule182`, `History.rule182_reduces`, `History.Q182`, `History.rule182_deviation_iff`, `History.rule182_determinate_iff` |
| Cochrane (18.3), p. 427 | "write it King's way, and the likelihood function will be flat": every statistic of the equilibrium paths is the same for all `φ` in the determinacy region | `History.likelihood_flat` |
| Cochrane p. 428 | Clarida–Galí–Gertler: `φ_π > 1` means determinacy, but for `φ_π ∈ [0, 1)` indeterminacy holds iff `(1 − β)φ_x ≤ κ(1 − φ_π)` | `History.cgg_reading` |

## Links between the two chains (Links)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 400; (17.19), p. 411 | the simple model's expectational error of an adapted process is the innovation; the any-sign announcement surprise is an innovation | `Links.reErr_eq_innov`, `Links.any_sign_innov` |
| Cochrane (17.18), p. 408; (17.7), p. 398 | under perfect foresight (17.18) at `β = 0` is (17.7) with no expectational errors | `Links.second_beta_zero_iff` |
| Cochrane (17.8), p. 400; Fig. 17.5, p. 409 | on ℤ the bounded solutions of (17.18) at `β = 0` are the backward moving average (17.8) | `Links.secondZ_beta_zero` |
| Cochrane (17.29)–(17.32), p. 420; (17.11), p. 402 | at `β = 0` the deviation system is (17.11) with the rule, and its determinacy is the corrected E7 condition, i.e. `REDeterminate` | `Links.deviation_beta_zero`, `Links.determinate_beta_zero_iff`, `Links.determinate_beta_zero_iff_reDeterminate` |
| Cochrane A1 (1.58), p. 587; p. 402 | the (1.58) bound equals the E7 bound at `β = 0`, lies strictly below it for `β > 0`, and tends to it as `β → 0` | `Links.bound_1_58_beta_zero`, `Links.bound_1_58_lt`, `Links.tendsto_bound_1_58` |
| Cochrane A1 (1.55), p. 586; (17.33), p. 420 | `transA` is `solvedA (Pmat σ κ φ 0) (Qmat σ β)` and the inverse of `M`; determinacy is Schur stability of `transA` | `Links.transA_eq_solvedA`, `Links.Mmat_mul_transA`, `Links.determinate_iff_transA` |
| Cochrane A1 pp. 587–588 | MSV uniqueness on the whole determinacy region (1.58), including the negative branch | `Links.msv_unique_of_determinate` |
| Cochrane A1 §1.8, p. 572; (1.57), p. 587 (E11) | the lag roots and the eigenvalues are reciprocal, with discriminants of the same sign, so for `φ > 1` both eigenvalues have modulus above one; the complex example falls in the complex branch | `Links.inv_mem_roots`, `Links.discQ_div`, `Links.trM_detM_eq`, `Links.eigen_norm_gt_one`, `Links.complex_example_discE` |
| Cochrane A1 §1.13.1, p. 588; (17.15)–(17.17), p. 407 | the three-equation model is the full model with the rule substituted | `Links.threeEq_iff_model` |
| Cochrane p. 416; (5.6), p. 119 | `λ₂ = βη*`; with `i ≡ 0` every perfect-foresight equilibrium is `π_0η*ᵗ` | `Links.lam2_eq_beta_mul_etaStar`, `Links.openMouth_path` |
| Cochrane p. 415; p. 408 | a constant rate gives the constant inflation path | `Links.superFisher_path` |
| Cochrane Fig. 17.5, p. 409; pp. 405, 410 | `zPath` from the announcement on is the member of the `full_any_sign` family with `c = zPath T 0`; every other member differs by `(c − zPath T 0)λ₁^{−n}` | `Links.zPath_eq_path`, `Links.path_sub_zPath` |
| Cochrane (18.1)–(18.2), p. 427 | the deviation system is the model with (18.1); (18.2) without forward responses has `Q = Qmat` and the same determinacy condition | `Links.deviation_iff_rule181`, `Links.Q182_no_forward`, `Links.rule182_determinate_iff_determinate` |

## Shared tools

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane pp. 406, 408 | stable scalar recursions: `x_{n+1} = ax_n + f_n`, `\|a\| < 1`, `f_n → 0` gives `x_n → 0`, and the averaging form | `SharedTools.tendsto_zero_of_stable`, `SharedTools.tendsto_of_stable_avg` |
| Cochrane (5.5), p. 119, as used on p. 408 | forward sums of a bounded path: recursion, bound, limit | `SharedTools.fwd_sum_props`, `SharedTools.fwd_sum_tendsto` |
| Cochrane (17.8), p. 400; Fig. 17.5, p. 409 | ℤ-indexed stable backward recursions: iteration, the backward moving average, its converse, and the homogeneous case | `SharedTools.backward_iterate`, `SharedTools.eq_backward_series`, `SharedTools.backward_series_solves`, `SharedTools.int_homog_zero` |
| Cochrane p. 420; A1 (1.55), p. 586 | the structural matrices `P`, `Q` and `A = P⁻¹Q` with its trace and determinant | `SharedTools.Pmat`, `SharedTools.Qmat`, `SharedTools.det2_Pmat`, `SharedTools.solvedA`, `SharedTools.tr2_solvedA`, `SharedTools.det2_solvedA` |
| Chapters 17–18 throughout | the expectation axioms, adaptedness, AR(1) processes, perfect foresight; bounded processes; the coin-flip tree and its shock (used by `PersistenceFreedom.any_sign_coin`) | `ExpectationSystem`, `ExpectationSystem.Adapted`, `ExpectationSystem.IsAR1`, `perfectForesight`, `BoundedProc`, `ExpectationsFiniteTree.FiniteTree.toExpectationSystem`, `ExpectationsFiniteTree.coinSystem`, `ExpectationsFiniteTree.coinShock` |
| Cochrane p. 403; (17.26), p. 417; p. 420 | the scalar forward solution (used by `RulesAdaptiveRE` and `AR1Responses`); the forward series (used by `OptimalPolicy`); the vector uniqueness results and Schur–Cohn (used by `AR1Responses` and `TaylorDeterminacy`) | `ForwardSolution.scalar_existsUnique`, `ExpectationSystem.forwardSeries`, `ExpectationSystem.system_unique`, `ExpectationSystem.system_not_unique`, `SchurStable`, `schurStable_iff_roots` |
| shared core, not used by Chapters 17–18 | pull-out, the sunspot family and the vector forward solution, carried for the other Cochrane projects | `ExpectationSystem.PullOut`, `ForwardSolution.sunspotFamily`, `ForwardSolution.existsUnique_bounded` |
