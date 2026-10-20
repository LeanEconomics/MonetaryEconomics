# Source map

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, "The new-Keynesian models,
equilibrium selection" (pp. 363–396), with the precise claims of Chapter 12, "Interest-rate
targets", and Online Appendix A3, §§3.1.1–3.1.2 (pp. 613–616). Each formal claim is listed with
its Lean name, relative to the namespace `Cochrane.NewKeynesianSelection`. Page numbers are book
pages. The book has no labelled propositions, so rows are keyed by equation number, figure, the
survey's claim codes (Chapter 12 claims P2–P6, non-identification theorems NI-1 to NI-6) or page.
Rows follow the book section by section, and each heading names the modules that formalise the
section: the innovation operator and the Chapter 2 model the chapter rereads, Chapter 12,
§§16.1–16.10, Online Appendix A3, then the links between modules and to Woodford (2003), the
restated Woodford blocks, and the shared tools.

The linear results hold for an arbitrary `ExpectationSystem`, so under perfect foresight and
under uncertainty; an *equilibrium* of (16.4) is an adapted inflation process satisfying (16.4) at
every date, and *determinate* means exactly one bounded equilibrium for every bounded adapted
disturbance. The nonlinear results of §16.8 and §16.10 are under perfect foresight unless the row
says otherwise. Survey error codes E1–E6 are those of the survey of Chapters 11–19
(`notes/survey_cochrane_ch11-19.md`); see [corrections](corrections.md). Rows marked "restated"
reproduce results proved in an earlier project, with the namespace adapted.

## Innovations and shocks, §2.4, p. 30; (16.3)–(16.5), p. 364 (Innovation)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §2.4, p. 30 | the innovation `ΔE_{t+1}x = E_{t+1}x − E_tx` and its algebra (restated from the Chapter 2 project) | `Innovation.innov`, `Innovation.innov_add`, `Innovation.innov_sub`, `Innovation.innov_smul`, `Innovation.innov_neg`, `Innovation.innov_const`, `Innovation.innov_of_known`, `Innovation.innov_known_next`, `Innovation.innov_E_succ`, `Innovation.innov_mul_known` |
| Cochrane p. 30; (16.5), p. 364 | "you can't expect future unexpected shocks": `E_s ΔE_{t+1}x = 0` for `s ≤ t` | `Innovation.E_innov_zero`, `Innovation.E_innov_zero_of_le` |
| Cochrane (16.3), p. 364; p. 35 | for `x` known at `t + 1`, `ΔE_{t+1}x = x − E_tx`, and `x = E_tx + ΔE_{t+1}x`; the split into a known part and an unforecastable part is unique | `Innovation.innov_eq_sub_E`, `Innovation.eq_E_add_innov`, `Innovation.decomposition_unique` |
| Cochrane p. 30 | iterating: `x = E_tx + ∑_{j<n} ΔE_{t+j+1}x` for `x` known at `t + n` | `Innovation.telescope_innov` |
| Cochrane p. 40; (16.5), p. 364 | a shock: known at `t + 1` with `E_tε_{t+1} = 0`; its innovation on arrival is itself, later shocks have none, its earlier forecasts are zero | `Innovation.IsShock`, `Innovation.innov_shock`, `Innovation.innov_shock_later`, `Innovation.E_shock_of_le`, `Innovation.isShock_iff_innov` |
| Cochrane (16.5), p. 364 | the innovation process of any process is a shock, and an adapted process is its forecast plus its innovation process; shocks are closed under linear combinations | `Innovation.innovProc`, `Innovation.innovProc_isShock`, `Innovation.eq_E_add_innovProc`, `Innovation.isShock_lin`, `Innovation.isShock_smul`, `Innovation.isShock_neg`, `Innovation.isShock_zero` |
| Cochrane p. 365 | an adapted process with unforecastable increments is a shock; the two notions differ only at date 0 | `Innovation.adapted_isShock_iff` |
| Cochrane pp. 364–365 | the AR(1) law `u_{t+1} = ηu_t + ε_{t+1}`: shock-driven AR(1)s are `IsAR1 η`, and conversely; `ΔE_{t+1}u_{t+1+j} = ηʲε_{t+1}`; `E_su_{s+k} = ηᵏu_s` | `Innovation.AR1Law`, `Innovation.ar1_of_shock`, `Innovation.shock_of_ar1`, `Innovation.innov_ar1`, `Innovation.E_ar1_shift` |
| Cochrane (2.17), p. 35; (16.3), p. 364 | the innovation of a dominated infinite sum is the sum of the innovations | `Innovation.innov_tsum` |
| Cochrane (16.5), p. 364 | on the coin-flip tree a genuinely random shock exists | `Innovation.coinShock_adapted`, `Innovation.coin_shock_ne_zero` |

## The simple fiscal-theory model, §§2.5–2.6, pp. 34–42 (FTPLSimple, restated from the Chapter 2 project)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.7), (2.17)–(2.18), pp. 22, 35 | discounted surplus forecasts are summable; the fiscal shock `ε_{Σs,t+1}` is the innovation in the present value of surpluses, and it is a shock | `FTPLSimple.summable_E_shift`, `FTPLSimple.pvNews`, `FTPLSimple.E_forwardSeries_succ`, `FTPLSimple.innov_forwardSeries`, `FTPLSimple.pvNews_isShock` |
| Cochrane (2.16)–(2.19), pp. 35–36 | the peg model; it holds iff `π_{t+1} = i_t − ε_{Σs,t+1}`; for every adapted rate path, fiscal shock and `π_0` it has exactly one adapted solution, bounded when the inputs are | `FTPLSimple.PegModel`, `FTPLSimple.pegModel_iff`, `FTPLSimple.pegSol`, `FTPLSimple.pegSol_adapted`, `FTPLSimple.peg_existsUnique`, `FTPLSimple.pegSol_bounded` |
| Cochrane Figure 2.1, p. 36 | no unexpected inflation without a fiscal shock; inflation follows the rate one period later; `E_sπ_{t+1} = E_si_t` | `FTPLSimple.irf_peg_impact`, `FTPLSimple.irf_peg_later`, `FTPLSimple.expected_inflation_ahead` |
| Cochrane p. 39; (16.3), p. 364 | passive fiscal policy `ε_{Σs,t+1} = −ΔE_{t+1}π_{t+1}`: it is a shock, the valuation equation holds on every path, and every shock is an equilibrium inflation innovation | `FTPLSimple.passiveShock`, `FTPLSimple.passiveShock_isShock`, `FTPLSimple.passive_valuation_holds`, `FTPLSimple.passive_any_innovation` |
| Cochrane (2.20)–(2.25), p. 40 | the rule model `i_t = θπ_t + u_t`; eliminating `i`; the solution (2.25); for every `θ` exactly one equilibrium given `π_0`; it equals the peg solution for the equilibrium rate; bounded for `\|θ\| < 1`, unbounded for `\|θ\| > 1` | `FTPLSimple.RuleModel`, `FTPLSimple.Disturbance`, `FTPLSimple.Eq224`, `FTPLSimple.ruleModel_iff`, `FTPLSimple.eq224_iff`, `FTPLSimple.ruleSol`, `FTPLSimple.ruleSol_adapted`, `FTPLSimple.rule_existsUnique`, `FTPLSimple.rule_eq_peg`, `FTPLSimple.ruleSol_bounded`, `FTPLSimple.ruleSol_unbounded` |

## Chapter 12, "Interest-rate targets", §§12.1–12.2, pp. 325–327 (FTPLSimple)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane §12.1, p. 325 (P2, Sargent–Wallace) | the Fisher equation alone leaves unexpected inflation arbitrary; its adapted solutions are uncountable | `FTPLSimple.fisher_alone_any_innovation`, `FTPLSimple.fisher_alone_not_countable` |
| Cochrane §12.1, p. 326 (P3) | a peg is stable, determinate and quiet; with no fiscal news there is no unexpected inflation; the conditional variance of unexpected inflation is that of the fiscal shock | `FTPLSimple.peg_stable_determinate`, `FTPLSimple.peg_quiet`, `FTPLSimple.peg_unexpected_sq` |
| Cochrane §12.1, pp. 324–326 (P4–P5) | with a real rate `r_t`: the model holds iff `π_{t+1} = i_t − r_t − ε_{Σs,t+1}`; exactly one equilibrium; `E_tπ_{t+1} = i_t − r_t`, so real-rate variation passes one for one into expected inflation | `FTPLSimple.PegModelR`, `FTPLSimple.pegR_iff`, `FTPLSimple.pegR_existsUnique`, `FTPLSimple.pegR_expected`, `FTPLSimple.real_rate_passthrough` |
| Cochrane §12.1, p. 326 (P4) | a peg at zero gives the deflation `π = −r̄`; the steady states of a peg `ī` are `π̄ = ī − r̄` | `FTPLSimple.zero_peg_deflation`, `FTPLSimple.peg_steady_state_iff` |
| Cochrane §12.2, p. 327 (P6) | with `i_t = φπ_t`, `E_tπ_{t+j} = φʲπ_t`; for `\|φ\| > 1` the equilibrium is unique given the fiscal shock (determinate) yet expected inflation explodes (unstable); for `\|φ\| < 1` it converges | `FTPLSimple.rule_expected_path`, `FTPLSimple.rule_determinate_unstable`, `FTPLSimple.rule_stable` |

## §16.1 The simplest model, pp. 363–366, Figure 16.1 (SimplestModel)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (16.1)–(16.4), p. 364 | the model; eliminating `i_t` gives (16.4) `E_tπ_{t+1} = φπ_t + u_t` | `SimplestModel.NKModel`, `SimplestModel.Eq164`, `SimplestModel.nk_iff` |
| Cochrane (16.3), p. 364 | under passive fiscal policy (16.3) only determines surpluses: it holds for every inflation process, and (16.1)–(16.3) hold iff (16.1)–(16.2) do | `SimplestModel.passive_163`, `SimplestModel.nk_passive_iff` |
| Cochrane p. 364 | "the same set of equations as the simplest fiscal theory model": with an exogenous fiscal shock (16.1)–(16.3) is the rule model (2.20)–(2.22) | `SimplestModel.nk_with_163_iff_ruleModel` |
| Cochrane (16.5), p. 364 | the equilibria `π_{t+1} = φπ_t + u_t + δ_{t+1}`: every member is an adapted equilibrium; every equilibrium is the member with its own `π_0` and innovations; the index is unique; bijection with the pairs `(π_0, δ)`; the family is (2.25) with `ε_{Σs} = −δ` | `SimplestModel.nkSol`, `SimplestModel.nkSol_adapted`, `SimplestModel.nkSol_solves`, `SimplestModel.eq164_iff_165`, `SimplestModel.eq_nkSol`, `SimplestModel.nkSol_inj`, `SimplestModel.equilibria_bijOn`, `SimplestModel.nkSol_eq_ruleSol` |
| Cochrane p. 364, `\|φ\| < 1` | "this economy is stable": expected inflation obeys `E_tπ_{t+j+1} = φE_tπ_{t+j} + E_tu_{t+j}`, stays bounded, converges for a constant disturbance; the sunspot component fades; members of (16.5) are bounded | `SimplestModel.expected_succ`, `SimplestModel.expected_bounded`, `SimplestModel.expected_const_converges`, `SimplestModel.sunspot_expected`, `SimplestModel.sunspot_fades`, `SimplestModel.nkSol_bounded` |
| Cochrane p. 364 | "converges going forward for any initial value" needs a convergent forecast of the disturbance (counterexample `φ = 0`, `u_t = (−1)ᵗ`) | `SimplestModel.converges_needs_convergent_u` |
| Cochrane p. 364 | "but it remains indeterminate": for `\|φ\| < 1` the bounded equilibria are uncountable; a genuinely random sunspot equilibrium on the coin-flip tree | `SimplestModel.indeterminate_of_abs_lt_one`, `SimplestModel.coin_sunspot` |
| Cochrane p. 364, `\|φ\| > 1` | (16.4) has at most one bounded solution; every equilibrium other than (16.6) has `\|E_tπ_{t+j}\| → ∞` somewhere | `SimplestModel.eq164_unique`, `SimplestModel.explodes_of_ne_fwdSol` |
| Cochrane (16.6), p. 364 | the unique locally bounded equilibrium `π_t = −∑ φ^{−(j+1)}E_tu_{t+j}`, adapted | `SimplestModel.eq164_iff_scalar`, `SimplestModel.fwdSol`, `SimplestModel.fwdSol_apply`, `SimplestModel.eq164_adapted`, `SimplestModel.fwdSol_existsUnique` |
| Cochrane pp. 364, 370 | (16.4) is determinate iff `\|φ\| > 1`: "`φ < −1` is as good as `φ > 1`" | `SimplestModel.determinate_iff` |
| Cochrane (16.9), p. 365 | with an AR(1) disturbance `π_t = −u_t/(φ − η)` solves (16.4) for every `φ ≠ η`, is adapted and bounded, and is the locally bounded equilibrium for `\|φ\| > 1` | `SimplestModel.ar1Pi`, `SimplestModel.ar1Pi_eq164`, `SimplestModel.ar1Pi_adapted`, `SimplestModel.ar1Pi_bounded`, `SimplestModel.ar1_solution` |
| Cochrane (16.7), (16.10)–(16.11), p. 365 | the selected `π_0` and `δ_{t+1} = −ε_{t+1}/(φ − η)`; `π_{t+1} = ηπ_t − ε_{i,t+1}/(φ − η)`; `i_t = −ηu_t/(φ − η)` | `SimplestModel.ar1_selection`, `SimplestModel.ar1_law_1610`, `SimplestModel.ar1_rate` |
| Cochrane Figure 16.1, pp. 365–366 | impulse responses as innovations; at `φ = 1.25`, `η = 0.8` inflation falls by `20/9` and the rate by `16/9` on impact, then both revert monotonically to zero | `SimplestModel.irf_ar1`, `SimplestModel.fig161_values`, `SimplestModel.fig161_reverts` |
| Cochrane (16.8), p. 365 | the Wicksellian rule: the price gap obeys `E_tx_{t+1} = (1 + φ_p)x_t + u_t`; unique bounded price level `p_t = p* − ∑ (1 + φ_p)^{−(j+1)}E_tu_{t+j}` | `SimplestModel.WicksellModel`, `SimplestModel.wicksell_iff`, `SimplestModel.wicksell_existsUnique`, `SimplestModel.wicksell_apply` |
| Cochrane (16.8), p. 365 (E4) | determinate iff `φ_p > 0` or `φ_p < −2`; the printed formula with `1 + φ` is not a solution | `SimplestModel.wicksell_determinate_iff`, `SimplestModel.printed_wicksell_false` |

## §16.2 Inflation targets and equilibrium selection, pp. 366–368; §16.4, p. 369 (KingForm)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (16.12)–(16.13), p. 366 | King's form `i_t = i*_t + φ(π_t − π*_t)` is (16.2) with `u_t = E_tπ*_{t+1} − φπ*_t`; with (16.1) it is the simplest model; bounded adapted targets give bounded adapted disturbances | `KingForm.KingRule`, `KingForm.toU`, `KingForm.kingRule_iff`, `KingForm.kingModel_iff_nk`, `KingForm.toU_bounded`, `KingForm.toU_adapted` |
| Cochrane p. 367 | the inverse `π*_t = −∑ φ^{−(j+1)}E_tu_{t+j}`; for `\|φ\| > 1` the translation is a bijection between bounded adapted targets and disturbances | `KingForm.fwdSol_toU`, `KingForm.toU_fwdSol`, `KingForm.translation_bijOn` |
| Cochrane (16.14), p. 367 | `E_t(π_{t+1} − π*_{t+1}) = φ(π_t − π*_t)`; the target is an equilibrium; for `\|φ\| > 1` it is the only bounded one, for any disturbance process | `KingForm.eq1614_iff`, `KingForm.target_solves`, `KingForm.eq_target_of_bounded` |
| Cochrane p. 369 (`*` notation); p. 367 | `E_t(π_{t+j} − π*_{t+j}) = φʲ(π_t − π*_t)`; off target the expected deviation explodes | `KingForm.deviation_expected`, `KingForm.deviation_explodes` |
| Cochrane p. 367 | the central bank can achieve any bounded inflation path; `i_t = i*_t`; the rate sets expected inflation, selection sets unexpected inflation | `KingForm.any_target_attainable`, `KingForm.eqm_rate_eq_target`, `KingForm.expected_set_by_rate`, `KingForm.unexpected_set_by_selection` |
| Cochrane p. 367 | `i*_t = θπ*_t + u_t` is a standard rule with disturbance `(θ − φ)π*_t + u_t` | `KingForm.thetaRule_iff` |
| Cochrane p. 367 | the fiscal theory with the same rate path and `ε_{Σs} = −ΔEπ*` gives the same inflation, with no boundedness and no `φ` | `KingForm.ftpl_same_inflation` |

## §16.3–§16.4 Hyperinflations; central-bank destabilisation, pp. 368–370 (Hyperinflation)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (16.25), (16.28), p. 379 | the perfect-foresight Fisher equation, the flow condition `B_t/(1 + i_t) + P_ts_t = B_{t−1}`, the passive rule `s_t = (r/(1+r))B_{t−1}/P_t`, the transversality condition `(1 + r)^{−T}B_{T−1}/P_T → 0` and the valuation equation (16.26) as a genuine sum | `Hyperinflation.FisherPF`, `Hyperinflation.Flow`, `Hyperinflation.PassiveRule`, `Hyperinflation.TVC`, `Hyperinflation.Valuation` |
| Cochrane (16.30), p. 379 | real debt evolves as `B_t/P_{t+1} = (1 + r)(B_{t−1}/P_t − s_t)`, one date at a time and along paths | `Hyperinflation.real_debt_flow_scalar`, `Hyperinflation.real_debt_flow` |
| Cochrane p. 379 | under the passive rule real debt is constant, the transversality condition holds and (16.30) implies (16.26), for every price path | `Hyperinflation.passive_real_debt_const_real`, `Hyperinflation.passive_real_debt_const`, `Hyperinflation.passive_tvc`, `Hyperinflation.passive_valuation` |
| Cochrane §16.3, p. 368; p. 379 | "economics does not rule out nominal explosions": every positive price path is a full perfect-foresight equilibrium | `Hyperinflation.any_price_path_eqm` |
| Cochrane p. 379 (E2) | the zero bound `i_t ≥ 0` iff `Π_{t+1} ≥ β` (weak inequality) | `Hyperinflation.zero_bound_iff_scalar`, `Hyperinflation.zero_bound_iff` |
| Cochrane §16.3, p. 368; (16.27)–(16.29), p. 378 | the path `π_t = φᵗπ_0` as an exact nonlinear path: it solves (16.4) with `u = 0`, obeys `1 + i_t = (1 + r)Π_t^φ`, explodes, and is still an equilibrium with the transversality condition and constant real debt | `Hyperinflation.hyperP`, `Hyperinflation.hyperP_pos`, `Hyperinflation.hyper_log_inflation`, `Hyperinflation.hyper_linear_eqm`, `Hyperinflation.hyper_rule`, `Hyperinflation.hyper_explodes`, `Hyperinflation.hyperinflation_satisfies_tvc` |
| Cochrane (16.25)–(16.26), pp. 368, 377–379, under uncertainty | with passive fiscal policy real debt is a martingale, expected real debt is constant, and every equilibrium price process satisfies `β^TE_tb_{t+T} → 0` and (16.26) | `Hyperinflation.FisherE`, `Hyperinflation.FlowE`, `Hyperinflation.realDebt`, `Hyperinflation.stoch_real_debt_martingale`, `Hyperinflation.stoch_expected_real_debt`, `Hyperinflation.stoch_tvc`, `Hyperinflation.stoch_valuation` |
| Cochrane (16.30) ⇒ (16.26), p. 379 | iterating the real flow with exogenous surpluses: `b_t = ∑_{j<T} βʲs_{t+j} + βᵀb_{t+T}` | `Hyperinflation.RealDebtFlow`, `Hyperinflation.pv_partial`, `Hyperinflation.ftpl_discounted_debt` |
| Cochrane §16.3, p. 369 | the fiscal theory rules out real explosions: the transversality condition holds iff `b_0` is the present value of surpluses; a too-low price level makes real debt explode; `P_0 = B_{−1}/PV` | `Hyperinflation.ftpl_tvc_iff`, `Hyperinflation.ftpl_real_explosion`, `Hyperinflation.ftpl_price_level_iff` |
| Cochrane §16.4, p. 369 | `E_tπ_{t+j} = φʲπ_t`; `\|φ\| < 1` stable, `\|φ\| > 1` the bank destabilises | `Hyperinflation.expected_path`, `Hyperinflation.stable_of_abs_lt_one`, `Hyperinflation.unstable_of_one_lt_abs` |
| Cochrane §16.4, p. 370 | `φ < −1` gives oscillating explosions and local determinacy | `Hyperinflation.oscillating_of_lt_neg_one`, `Hyperinflation.determinate_of_lt_neg_one` |

## §16.5 Identification, pp. 370–372 (Identification)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (16.1)–(16.2), (16.4), p. 364 | the equilibrium notion of the identification results: adapted `π`, the Fisher rate, the rule; eliminating `i` | `Identification.fisherRate`, `Identification.NKEq`, `Identification.nkEq_iff` |
| Cochrane (16.6), p. 364 | the new-Keynesian selection: the unique bounded adapted solution of (16.4); for `\|φ\| > 1` every bounded adapted solution is the selected one, and the selected equilibrium is unique | `Identification.Selected`, `Identification.selected_of`, `Identification.selected_unique` |
| Cochrane p. 371 (NI-1) | reverse engineering: for every adapted `π` and every `φ`, `u = i − φπ` makes `π` an equilibrium, and for bounded `π` and `\|φ\| > 1` the selected one; every bounded equilibrium is selected for every such `φ` | `Identification.reverseU`, `Identification.reverse_nkEq`, `Identification.reverse_selected`, `Identification.every_eq_selected` |
| Cochrane p. 371 | knowing `φ` gives `u`; knowing `u` gives `φ`; the reverse-engineered disturbances differ by `(φ₂ − φ₁)π` | `Identification.u_eq_of_nkEq`, `Identification.phi_eq_of_same_u`, `Identification.reverseU_sub` |
| Cochrane §16.5, p. 370; §16.10.7, p. 394 | identification of a parameter on a class of specifications from observables | `Identification.IdentifiedOn`, `Identification.nkClass`, `Identification.nkObs` |
| Cochrane pp. 370–371 (NI-1) | the set of `φ` consistent with any data is all of `1 < \|φ\|`; zero inflation is selected for every `φ`; neither `φ` nor `u` is identified | `Identification.nk_fiber_eq`, `Identification.zero_selected`, `Identification.phi_not_identified`, `Identification.u_not_identified` |
| Cochrane p. 371 | "the likelihood function does not involve `φ`": the law of the observables is the same under any probability model | `Identification.law_obs_eq` |
| Cochrane p. 365 | the AR(1) disturbance as an adapted process driven by a shock; it is `IsAR1 η` | `Identification.AR1`, `Identification.AR1.E_succ`, `Identification.AR1.isAR1` |
| Cochrane (16.9)–(16.11), (16.15), pp. 365, 371 | `π = −u/(φ − η)` is the selected equilibrium; (16.10); `i_t = −ηu_t/(φ − η) = ηπ_t` with no error | `Identification.ar1_selected`, `Identification.eq_16_10`, `Identification.eq_16_15` |
| Cochrane (16.3), (16.16)–(16.18), p. 371 | `ε_π = −ε_i/(φ − η)`; with the passive fiscal response `ε_π = −ε_{Σs}`, `ε_{Σs} = ε_i/(φ − η)`; the observable system | `Identification.eq_16_16_innov`, `Identification.eq_16_18`, `Identification.ObsAR1`, `Identification.ar1_obs` |
| Cochrane p. 371 | conversely any bounded solution of the observable system is the selected AR(1) equilibrium for every `\|φ\| > 1`, `φ ≠ η` | `Identification.obs_selected_every_phi` |
| Cochrane pp. 370–371 (NI-2) | `φ` and the disturbance enter only through `u/(φ − η)`; rescaling leaves the equilibrium unchanged | `Identification.ni2_same_iff`, `Identification.ni2_rescaled` |
| Cochrane (16.15), p. 371 | finite-sample OLS (with and without intercept), sample mean and IV estimates, as exact identities when `y = ηx` on the sample | `Identification.olsNoInt`, `Identification.sampleMean`, `Identification.olsSlope`, `Identification.olsIntercept`, `Identification.ivEst`, `Identification.olsNoInt_eq`, `Identification.sampleMean_eq`, `Identification.olsSlope_eq`, `Identification.olsIntercept_eq_zero`, `Identification.ivEst_eq` |
| Cochrane (16.15), p. 371 (NI-3) | "a regression of `i_t` on `π_t` produces `η` not `φ`", on every history and sample; "no instrument can help" | `Identification.ni3_ols`, `Identification.ni3_ols_slope`, `Identification.ni3_ols_ne_phi`, `Identification.ni3_iv` |
| Cochrane (16.16), p. 371 | the autoregression of observed inflation is `η + ∑π_tε_{π,t+1}/∑π_t²`, which involves only observables | `Identification.ols_ar_eq` |
| Cochrane (16.12), (16.19), pp. 366, 371 (NI-4) | the King-form equilibrium with consistent targets; the targets are an equilibrium for every `φ`; for `\|φ\| > 1` the only bounded one; the selection term vanishes; the bounded equilibrium set `{(π*, i*)}` is the same for every `\|φ\| > 1` | `Identification.KingEq`, `Identification.TargetsConsistent`, `Identification.king_target_eq`, `Identification.king_bounded_eq`, `Identification.king_selection_zero`, `Identification.king_eq_set`, `Identification.king_eq_set_indep` |

## §16.6 Observational equivalence, pp. 372–374 (ObservationalEquivalence)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (2.20)–(2.25), p. 40 | the fiscal-theory equilibrium satisfies (2.25), is unique given `π_0` for every `θ`, and exists (the path `FTPLSimple.ruleSol`) | `ObservationalEquivalence.ftpl_eq_225`, `ObservationalEquivalence.ftpl_unique`, `ObservationalEquivalence.ftpl_exists` |
| Cochrane p. 372 (NI-5) | the selected AR(1) equilibrium is the fiscal-theory equilibrium with `θ = η`, `u = 0`, `ε_{Σs} = ε_i/(φ − η)`, and is its path; the passive surplus equals the active fiscal shock | `ObservationalEquivalence.nk_is_ftpl`, `ObservationalEquivalence.nk_eq_ftpl_path`, `ObservationalEquivalence.passive_surplus_eq_active` |
| Cochrane (16.10), (16.16), p. 372; Figure 16.1, Figure 2.2 | impulse responses of the observable system, of the new-Keynesian monetary shock and of the fiscal-theory fiscal shock; the two coincide | `ObservationalEquivalence.obs_irf`, `ObservationalEquivalence.nk_irf`, `ObservationalEquivalence.ftpl_irf`, `ObservationalEquivalence.nk_irf_eq_ftpl_irf` |
| Cochrane p. 373 | "any new-Keynesian model can be written as a fiscal theory model", for every `θ`, a time-varying peg included; "observational equivalence goes both ways" | `ObservationalEquivalence.nk_to_ftpl`, `ObservationalEquivalence.nk_to_peg`, `ObservationalEquivalence.ftpl_to_nk` |
| Cochrane pp. 372–373 | the observable sets of new-Keynesian and fiscal-theory equilibria are equal, and so are those of selected and of bounded fiscal-theory equilibria | `ObservationalEquivalence.nkObsSet`, `ObservationalEquivalence.ftplObsSet`, `ObservationalEquivalence.nkObsSet_eq_ftplObsSet`, `ObservationalEquivalence.selectedObsSet`, `ObservationalEquivalence.boundedFtplObsSet`, `ObservationalEquivalence.selectedObsSet_eq_boundedFtplObsSet` |
| Cochrane (16.20)–(16.22), p. 373 | the unified model: monetary block, fiscal block (as printed, the actual surplus in both debt equations), the transversality condition `ρ^TE_tv_{t+T} → 0`, equilibrium | `ObservationalEquivalence.MonetaryBlock`, `ObservationalEquivalence.FiscalBlock`, `ObservationalEquivalence.TVC`, `ObservationalEquivalence.UnifiedEq` |
| Cochrane (5.35), pp. 137–138, for (16.21)–(16.22) | the debt gap obeys `ρe_{t+1} = e_t − (ΔEπ − ΔEπ*)`, free of `γ`; the target and actual debt dynamics; `ρᵏE_te_{t+k} = e_t`; the gap vanishes iff unexpected inflation is on target | `ObservationalEquivalence.e_dyn`, `ObservationalEquivalence.vs_dyn`, `ObservationalEquivalence.v_dyn`, `ObservationalEquivalence.E_gap`, `ObservationalEquivalence.gap_zero_iff` |
| Cochrane p. 138; (16.21)–(16.22), p. 373 | a linear recursion with converging forcing converges; `ρ^TE_tv_{t+T} → ((α − γ)/α)(v_t − v*_t)`; the transversality condition holds iff `(α − γ)(v_t − v*_t) = 0` | `ObservationalEquivalence.rec_limit`, `ObservationalEquivalence.tendsto_tvc`, `ObservationalEquivalence.tvc_iff` |
| Cochrane p. 373 (E6) | passive fiscal policy; `γ = α` is passive; the fiscal block has a solution for every inflation path; with `γ ≠ α` an off-target path violates the transversality condition; passive iff `γ = α` | `ObservationalEquivalence.FiscalPassive`, `ObservationalEquivalence.passive_of_eq`, `ObservationalEquivalence.fiscalPath`, `ObservationalEquivalence.fiscalSurplus`, `ObservationalEquivalence.fiscalPath_block`, `ObservationalEquivalence.not_passive_of_ne`, `ObservationalEquivalence.passive_iff` |
| Cochrane p. 373 (E6, coin-flip tree) | the tree has a nonzero innovation; passive iff `γ = α`; `ρ = α = 1/2`, `γ = 1` is not passive; an off-target sunspot path solves the monetary block and violates the transversality condition for every `γ ≠ α` | `ObservationalEquivalence.coin_innov_ne_zero`, `ObservationalEquivalence.coin_passive_iff`, `ObservationalEquivalence.e6_printed_fails`, `ObservationalEquivalence.coinSunspot`, `ObservationalEquivalence.coinSunspot_monetary`, `ObservationalEquivalence.e6_counterexample` |
| Cochrane p. 373 | the regimes: the inflation gap obeys `x_{t+1} = φx_t + (ΔEπ − ΔEπ*)`; active fiscal (`γ ≠ α`, any `φ`) gives `ΔEπ = ΔEπ*` and `π_t − π*_t = φᵗ(π_0 − π*_0)`, and with `φ = 0` `π = π*` from date 1; active money gives `π = π*` for every `γ` | `ObservationalEquivalence.gap_succ`, `ObservationalEquivalence.af_regime`, `ObservationalEquivalence.af_regime_phi_zero`, `ObservationalEquivalence.am_regime` |
| Cochrane (16.23)–(16.24), p. 373 (NI-6) | the observable system; every equilibrium of every regime satisfies it, every solution is an equilibrium of every regime; the observable sets are equal and nonempty; the regimes are observationally equivalent and `γ`, like `φ`, is not identified | `ObservationalEquivalence.ObsFiscal`, `ObservationalEquivalence.unifiedEq_obs`, `ObservationalEquivalence.obs_unifiedEq`, `ObservationalEquivalence.eqObs`, `ObservationalEquivalence.eqObs_eq`, `ObservationalEquivalence.eqObs_nonempty`, `ObservationalEquivalence.regimes_observationally_equivalent`, `ObservationalEquivalence.gamma_phi_not_identified` |

## §16.7 Responses, pp. 374–377 (Responses)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (16.12)–(16.13), p. 374 | the two forms of the rule; "the `u_1 = 1` shock is the same thing as a `π*_1 = −1/φ` shock" | `Responses.king_iff_nk`, `Responses.u_shock_eq_target` |
| Cochrane p. 374 | the alternative paths `E_sπ_{s+k} = −ηᵏu_s/(φ − η) + φᵏ(π_s + u_s/(φ − η))` explode unless `π_s = −u_s/(φ − η)`; the non-explosive solution is exactly (16.9), with no uniform bound on `u` (so `η = 1` is covered) | `Responses.alt_paths`, `Responses.NonExplosive`, `Responses.alt_paths_explode`, `Responses.nonExplosive_iff` |
| Cochrane pp. 374–376 | the model is Fisherian: the real rate is zero, `E_tπ_{t+j+1} = E_ti_{t+j}`, and in the selected equilibrium `i_tπ_t ≥ 0` | `Responses.real_rate_zero`, `Responses.expected_follows_rate`, `Responses.fisherian_sign` |
| Cochrane Figure 16.1, pp. 374–375 | the impulse path; on a positive shock inflation and the rate fall on impact although `u_1 > 0`, and the fall is entirely unexpected | `Responses.impulse_path`, `Responses.impact_signs` |
| Cochrane p. 375 | super-Fisherian: `η = 1`, `ε_1 = 1 − φ` gives `π_t = i_t = 1` for `t ≥ 1`, on the coin-flip tree as well | `Responses.super_fisherian`, `Responses.dateOneShock`, `Responses.dateOneShock_isShock`, `Responses.superU`, `Responses.superU_ar1`, `Responses.super_fisherian_coin` |
| Cochrane p. 375 (E5) | open mouth: `η = 0`, `ε_1 = −φ` gives `π_1 = 1`, `π_2 = π_3 = … = 0`, `i ≡ 0`, and a permanent price-level jump; on the coin-flip tree as well | `Responses.open_mouth`, `Responses.open_mouth_price_jump`, `Responses.open_mouth_coin` |
| Cochrane p. 376 | the rule `i_t = φE_tπ_{t+1}`: for `φ ≠ 1` every equilibrium has `E_tπ_{t+1} = i_t = 0`; every shock process is equilibrium inflation; `π = 0` is a solution; with a disturbance `E_tπ_{t+1} = u_t/(1 − φ)` and the real rate is still zero | `Responses.RuleExpEq`, `Responses.ruleExp_trivial`, `Responses.ruleExp_solutions`, `Responses.ruleExp_has_solution`, `Responses.ruleExp_disturbance` |
| Cochrane pp. 372, 376–377 | the full model (16.1)–(16.3): no fiscal shock, no unexpected inflation; the selected AR(1) equilibrium needs exactly `ε_{Σs} = ε_i/(φ − η)`; without the fiscal response no non-explosive equilibrium exists; unexpected inflation is negative iff the fiscal shock is positive | `Responses.NK3Eq`, `Responses.no_fiscal_no_surprise`, `Responses.nk3_ar1_fiscal_iff`, `Responses.no_eq_without_fiscal`, `Responses.disinflation_iff_contraction` |

## §16.8 A full nonlinear model and the lower bound, pp. 377–380, Figure 16.2 (LowerBound)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (16.25), (16.28), pp. 377–378 | the bond-pricing equation for any expectation system; under perfect foresight `Π_{t+1} = β(1 + i_t)`; with price levels | `LowerBound.BondPricing`, `LowerBound.bondPricing_perfectForesight_iff`, `LowerBound.fisher_pf_iff` |
| Cochrane (16.25) ⇒ (16.1), pp. 377–378 | exact log Fisher equation; the exact linearisation: the derivative of `log(1 + i_t)` along a bounded direction of log inflation is `E_tπ_{t+1}`, at the zero-inflation steady state and, as a Gateaux derivative, at any steady state | `LowerBound.log_fisher_pf`, `LowerBound.abs_exp_sub_le`, `LowerBound.hasDerivAt_E_exp`, `LowerBound.hasDerivAt_log_bondPricing`, `LowerBound.E_exp_pos`, `LowerBound.gateaux_log_bondPricing` |
| Cochrane (16.27), p. 378 | the slope of the rule in logs at `Π*` is `Φ′(Π*)`, so the linearised Taylor coefficient is `φ = Φ′(Π*)` | `LowerBound.hasDerivAt_log_rule` |
| Cochrane (16.27)–(16.29), p. 378 | the rule and perfect foresight hold iff `Π_{t+1} = Φ(Π_t)`; "initial inflation is the only indeterminacy" | `LowerBound.dynamics_iff`, `LowerBound.eq_orbit`, `LowerBound.orbit_succ` |
| Cochrane p. 378 | with `Φ′(Π*) > 1` paths near `Π*` lead away, and `Π*` is the unique locally bounded equilibrium | `LowerBound.target_repelling`, `LowerBound.target_unique_locally_bounded` |
| Cochrane pp. 378–379 (E2) | `Π_{t+1} = β` exactly when `i_t = 0`, which the bound allows; the rule respects the bound at `Π` iff `Φ(Π) ≥ β` | `LowerBound.zero_bound_eq_iff`, `LowerBound.rule_respects_bound_iff` |
| Cochrane p. 379 (E2) | the second steady state, corrected: for `Φ` continuous on `[β, Π*]` with `Φ ≥ β` there is a largest fixed point `Π_L ∈ [β, Π*)`, with `Φ′(Π_L) ≤ 1` | `LowerBound.lower_steady_state` |
| Cochrane p. 379 (E2) | the tangency counterexample `Φ′(Π_L) = 1`, `Π_L` not stable from the left, but paths from `(Π_L, Π*)` still converge | `LowerBound.phiTan`, `LowerBound.phiTan_poly_ge`, `LowerBound.phiTan_eq`, `LowerBound.hasDerivAt_tanPoly`, `LowerBound.hasDerivAt_phiTan`, `LowerBound.e2_tangency_counterexample`, `LowerBound.phiTan_left_unstable`, `LowerBound.phiTan_deflation_tendsto` |
| Cochrane p. 379 (E2) | without continuity there need be no second steady state | `LowerBound.phiJump`, `LowerBound.e2_discontinuous_counterexample` |
| Cochrane pp. 379–380 | deflations "trundle down gently" to `Π_L`, strictly; local indeterminacy near `Π_L` when `\|Φ′(Π_L)\| < 1` | `LowerBound.deflation_tendsto_lower`, `LowerBound.deflation_strictAnti`, `LowerBound.lower_locally_indeterminate` |
| Cochrane (16.26), (16.30), p. 379 | given the flow, the valuation equation holds iff the transversality condition does | `LowerBound.valuation_of_tvc`, `LowerBound.tvc_of_valuation`, `LowerBound.valuation_iff_tvc` |
| Cochrane p. 379 | the rule `s_t = γB_{t−1}/P_t` satisfies the transversality condition for all debt iff `0 < γ < 2`, and `r/(1 + r)` lies in that range | `LowerBound.passive_gamma_tvc_iff`, `LowerBound.passive_coefficient_mem` |
| Cochrane §16.8, pp. 377–379 | the full equilibrium (positive prices, zero bound, (16.25), (16.27), flow, (16.26)); its dynamics and transversality condition | `LowerBound.prevP`, `LowerBound.infl`, `LowerBound.IsEquilibrium`, `LowerBound.equilibrium_dynamics` |
| Cochrane p. 379 | "all of the paths graphed in Figure 16.2 are perfect-foresight equilibria": one for every initial inflation, including the deflations to `Π_L` | `LowerBound.equilibrium_exists`, `LowerBound.continuum_of_equilibria`, `LowerBound.deflationary_equilibria` |
| Cochrane p. 379 | the truncated linear rule; the gap below target is `min(Π* − β, φᵗ(Π* − Π₀))`; paths below `Π*` reach `i = 0` in finite time and stay | `LowerBound.truncRule`, `LowerBound.truncRule_props`, `LowerBound.truncRule_orbit_gap`, `LowerBound.truncRule_hits_bound` |
| Cochrane pp. 379–380 | the 2%/1% example (from `1.0199` to net inflation `β − 1 = −1/101`); with `r = −1%`, `Π_L` near 1% | `LowerBound.example_two_one`, `LowerBound.negative_real_rate_example` |

## §16.9 Identification patches, pp. 380–383 (Identification)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane pp. 367, 382 | the rule `i_t = θπ*_t + φ(π_t − π*_t) + u_t` is a King rule; the target is an equilibrium; for `\|φ\| > 1` the data obey `i_t = θπ_t + u_t`, free of `φ` | `Identification.ThetaEq`, `Identification.ThetaConsistent`, `Identification.thetaEq_iff_king`, `Identification.thetaEq_target`, `Identification.thetaRule_eq_obs` |
| Cochrane p. 382 | "the identifying assumptions that let us measure `φ` start with `θ = φ`": an instrument orthogonal to `u` measures `θ`, and `φ` iff `θ = φ`; IV algebra | `Identification.iv_identifies_iff`, `Identification.ivEst_eq_add` |
| Cochrane p. 382 | with `θ = φ` and no disturbance the simplest model gives only `π = 0`: identification needs shocks from other equations | `Identification.theta_eq_phi_no_shock_zero` |
| Cochrane p. 382 (Giannoni–Woodford) | the real-rate-shock model; the IV estimate is `φ + ∑zu/∑zπ`, equal to `φ` iff the instrument is orthogonal to `u`; unique bounded equilibrium; an identified example (`φ = 2`) | `Identification.RREq`, `Identification.rr_iv_eq_phi_add`, `Identification.rr_iv_eq_phi_iff`, `Identification.rr_unique`, `Identification.rr_example` |

## §16.10.1–§16.10.6 Equilibrium-selection patches, pp. 383–394 (SelectionPatches)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (16.4), p. 364 | under perfect foresight (16.4) is `π_{t+1} = φπ_t + u_t` | `SelectionPatches.simpleModel_pf_iff` |
| Cochrane §16.10.1, p. 385 | MSV: among `π_t = cu_t`, the only solution is `c = −1/(φ − η)`, for every `φ ≠ η`, passive `\|φ\| < 1` included; none if `φ = η` | `SelectionPatches.msv_unique`, `SelectionPatches.msv_iff`, `SelectionPatches.msv_none_of_eq` |
| Cochrane §16.10.1, p. 385 | the explosive and sunspot solutions are not of MSV form, bounded ones included when `\|φ\| ≤ 1` | `SelectionPatches.pf_explosive_not_msv`, `SelectionPatches.pf_passive_bounded_not_msv` |
| Cochrane §16.10.1, p. 385 | with nonlinear `f`, `π_t = f(u_t)` admits solutions that explode when `φ > 1` | `SelectionPatches.rpow_orbit`, `SelectionPatches.msv_nonlinear_counterexample` |
| Cochrane §16.10.2, p. 389 | constant velocity: money growth is inflation | `SelectionPatches.quantity_theory_growth` |
| Cochrane §16.10.2, pp. 388–389 (Atkeson–Chari–Kehoe) | the overlap regime; no equilibrium forms at `T` unless `Φ(Π_T) = μ`; the equilibria are the Taylor paths that never exceed `Π_U`; inflations are pruned, deflations are not; Woodford's commodity backstop | `SelectionPatches.ACKEq`, `SelectionPatches.ack_inconsistent`, `SelectionPatches.ack_bounded`, `SelectionPatches.ack_iff`, `SelectionPatches.ack_prunes_inflation`, `SelectionPatches.ack_keeps_deflation`, `SelectionPatches.woodford_backstop_prunes` |
| Cochrane §16.10.2, pp. 386–387 | the separated regime; the stabilised path exists and is unique for every `Π₀`: "stopping an inflation does not rule it out" | `SelectionPatches.StabEq`, `SelectionPatches.stabPath`, `SelectionPatches.stabPath_taylor`, `SelectionPatches.stabPath_money`, `SelectionPatches.stab_exists`, `SelectionPatches.stab_unique`, `SelectionPatches.stop_not_rule_out` |
| Cochrane §16.10.3, pp. 390–391 (Benhabib, Schmitt-Grohé and Uribe) | `b_{t+1} = (1 + r)(1 − θ(Π_t))b_t`; with `θ ≤ θ̄ < 0` eventually discounted debt diverges; no equilibrium converges to `Π_L` when `θ(Π_L) < 0`; the target survives | `SelectionPatches.bsgu_real_debt`, `SelectionPatches.bsgu_tvc_violated`, `SelectionPatches.bsgu_no_equilibrium_to_lower`, `SelectionPatches.bsgu_target_survives` |
| Cochrane §16.10.3, p. 390 (Woodford's `μ̄` rule) | the transversality term is multiplied by `βμ̄/Π_{T+1}`; it fails when eventually `Π_{T+1} ≤ βμ̄`; every path to `Π_L < βμ̄` violates it; the target satisfies it iff `βμ̄ < Π*` | `SelectionPatches.mubar_tvc_step`, `SelectionPatches.mubar_tvc_violated`, `SelectionPatches.mubar_deflation_violates`, `SelectionPatches.mubar_target_tvc_iff` |
| Cochrane §16.10.4, pp. 391–392 (Bassetto) | a rule ignoring the bound with `Π*` its only steady state on `[β, Π*]` sends every path below `Π*` to `i < 0` in finite time, so no equilibrium starts there; the linear rule, whose inflationary paths are not removed | `SelectionPatches.bassetto_exit`, `SelectionPatches.bassetto_no_equilibrium`, `SelectionPatches.linRule`, `SelectionPatches.linear_rule_exit` |
| Cochrane §16.10.5, p. 392 (Woodford p. 136) | a rule vertical at `Π_U` gives an explosion in finite time | `SelectionPatches.vertical_rule_exit` |
| Cochrane §16.10.5, p. 392 (Alstadheim–Henderson) | a rule sending every `Π ≠ Π*` above `Π*` makes every other path explode, so `Π*` is the unique bounded path; the V-shaped and the discontinuous rule satisfy this | `SelectionPatches.v_rule_unbounded`, `SelectionPatches.v_rule_unique_bounded`, `SelectionPatches.vRule`, `SelectionPatches.vRule_props`, `SelectionPatches.ahJump`, `SelectionPatches.ahJump_props` |
| Cochrane §16.10.5, p. 392 | touching the 45° line only at `Π*` is not enough: the tangent rule has a continuum of bounded paths converging to `Π*` | `SelectionPatches.tangentRule`, `SelectionPatches.tangent_rule_converges` |
| Cochrane (16.31)–(16.32), p. 393 | (16.31) is (16.32) with the argument of `L` the interest rate; (16.32) is Woodford's (4.5), so the restated Schmitt-Grohé–Uribe results apply | `SelectionPatches.eq1632_iff`, `SelectionPatches.eq1632_iff_path45` |
| Cochrane (16.32), p. 393 | with a bounded continuous rule and `u_c ∘ L` continuous and positive on the range of rates, every `Π_t` has a finite successor and every path exists | `SelectionPatches.successor_exists_of_bounded_rule`, `SelectionPatches.path_exists_of_bounded_rule` |
| Cochrane (16.31)–(16.32), p. 393 | a bounded rule with money demand vanishing at a finite rate: no finite successor for `Π_t ∈ (1, 3/2)` | `SelectionPatches.boundedRule`, `SelectionPatches.boundedRate`, `SelectionPatches.moneyDemand`, `SelectionPatches.ucMoney`, `SelectionPatches.boundedRate_ge`, `SelectionPatches.bounded_rule_explosion` |
| Cochrane §16.10.6, pp. 393–394 (Sims 1994) | with nominal money above `M̲ > 0` and `∑(Π_{t+1} − β) < ∞` the transversality condition fails; in particular when the bound is reached in finite time | `SelectionPatches.sims_tvc_violated`, `SelectionPatches.sims_tvc_violated_of_eventually_beta` |
| Cochrane §16.10.6, p. 394 | the penny does not bite when `Π_L > β`, nor for a slow convergence `Π_{t+1} = β(t + 2)/(t + 1)` | `SelectionPatches.sims_no_bite_above_beta`, `SelectionPatches.sims_slow_counterexample` |

## Online Appendix A3, §§3.1.1–3.1.2, pp. 613–616 (SelectionPatches)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane A3 (3.1), p. 614 | helicopter money with no debt: the present-value relation "final money equals initial money plus added money" | `SelectionPatches.a3_helicopter_pv` |
| Cochrane A3, p. 614 | with perpetual money growth the discounted real money diverges: the transversality condition is violated | `SelectionPatches.a3_helicopter_tvc_violated` |
| Cochrane A3 §3.1.2, pp. 615–616 | open-market operations: constant real total debt; `B_t + M_t = βᵗ(B_0 + M_0)` and `B_t` eventually negative; the transversality condition holds | `SelectionPatches.a3_omo_real_const`, `SelectionPatches.a3_omo_nominal`, `SelectionPatches.a3_omo_debt_negative`, `SelectionPatches.a3_omo_tvc` |

## §16.10.7 Learning and other selection devices, pp. 394–395 (Identification, ObservationalEquivalence)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 394 | "people in the economy cannot learn it any more than econometricians can": identified iff some function of the observables recovers the parameter; `φ` is not learnable | `Identification.identified_iff_learnable`, `Identification.phi_not_learnable` |
| Cochrane p. 394 | in the active-fiscal equilibrium `θ = i_t/π_t`, identified and learnable for every `θ` (not only `θ < 1`) | `Identification.FTPLEq`, `Identification.ftplClass`, `Identification.ftpl_theta_eq`, `Identification.ftpl_theta_identified`, `Identification.ftpl_theta_learnable` |
| Cochrane p. 373; p. 394 ("the argument admittedly cuts both ways") | neither `γ` nor `φ` is identified, hence neither is learnable | `ObservationalEquivalence.unifiedClass`, `ObservationalEquivalence.gamma_phi_not_learnable` |

## §16.10.8 A tiny bit of fiscal theory (Sims 2013), pp. 395–396 (SimsTinyFiscal)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane p. 395; (16.33)–(16.34) | `π_t = φᵗπ₀`; `b_{t+1} = (R − γ)b_t − θφᵗπ₀` | `SimsTinyFiscal.infl_path`, `SimsTinyFiscal.eq1634` |
| Cochrane p. 396 | the closed form, the printed form, and the borderline case `φ = R − γ` | `SimsTinyFiscal.closed_form`, `SimsTinyFiscal.closed_form_book`, `SimsTinyFiscal.closed_form_eq` |
| Cochrane p. 396 | "for any `π₀ ≠ 0`, debt explodes": true for `\|R − γ\| < 1 < φ`, `θπ₀ ≠ 0` | `SimsTinyFiscal.debt_explodes` |
| Cochrane p. 396 (E1) | `R^{−t}b_t → 0` iff `θπ₀ = 0` or `φ < R`; the transversality condition fails for every `π₀ ≠ 0` iff `φ ≥ R`; counterexample `R = 1.05`, `γ = 0.5`, `φ = 1.02`; the transversality condition selects `π₀ = 0` iff `φ ≥ R` | `SimsTinyFiscal.tvc_iff`, `SimsTinyFiscal.e1_tvc_violated_iff`, `SimsTinyFiscal.e1_counterexample`, `SimsTinyFiscal.active_iff` |
| Cochrane p. 395 | the valuation equation holds iff the transversality condition does; when it fails the valuation equation cannot hold | `SimsTinyFiscal.valuation_iff_tvc`, `SimsTinyFiscal.valuation_fails` |
| Cochrane p. 395 (E1, second part) | "`γ > R − 1` so debt is stationary" needs `R − 1 < γ < R + 1`; `γ = 3.05` is a counterexample | `SimsTinyFiscal.stationary_iff`, `SimsTinyFiscal.stationary_counterexample` |
| Cochrane p. 396 | with a bounded external surplus component, debt is bounded and policy passive | `SimsTinyFiscal.passive_of_bounded` |
| Cochrane p. 396, quoting Sims | on the selected path the surplus and debt do not depend on `θ` | `SimsTinyFiscal.selected_path_indep_theta` |

## Links between the modules and to Woodford (Links)

| Book | Claim | Lean |
| --- | --- | --- |
| Cochrane (16.1)–(16.2), (16.6), (16.9), pp. 364–365 | `Identification.NKEq` is `SimplestModel.NKModel` plus adaptedness; the selection `Identification.Selected` is the forward solution; the two forms of (16.9) agree | `Links.nkEq_iff_nkModel`, `Links.selected_iff_eq_fwdSol`, `Links.ar1_selected_eq_fwdSol` |
| Cochrane (2.20)–(2.25), p. 40; (16.1)–(16.3), p. 364 | `Identification.FTPLEq` is `FTPLSimple.RuleModel` plus adaptedness and equals `FTPLSimple.ruleSol`; `Responses.NK3Eq` is the rule model with `θ = φ` | `Links.ftplEq_iff_ruleModel`, `Links.ftplEq_eq_ruleSol`, `Links.nk3Eq_iff_ruleModel` |
| Cochrane p. 372 (NI-5) and §2.6, p. 40 | the selected AR(1) equilibrium is the `FTPLSimple` rule equilibrium and its path | `Links.nk_is_ruleModel` |
| Cochrane p. 327 (P6), §16.4, p. 369 | every rule-model solution satisfies (16.4) with `φ = θ`, so the §16.4 expected path re-derives P6 | `Links.ruleModel_eq164`, `Links.rule_expected_path_of_eq164` |
| Cochrane (16.12)–(16.14), (16.19), pp. 366–367, 371 | the `Responses` disturbance is `KingForm.toU`; `Identification.KingEq` is `KingForm.KingRule` with the Fisher equation; NI-4's bounded-equilibrium result follows from `KingForm.eq_target_of_bounded` | `Links.king_disturbance_eq_toU`, `Links.kingEq_iff_kingRule`, `Links.king_bounded_eq_of_kingForm` |
| Cochrane (16.8), p. 365, vs Woodford (2003) (1.36), Prop. 2.3, pp. 81–82 (restated from the Woodford Chapter 2 project) | Woodford's (1.36) is (16.4) for the price gap; the Wicksellian model is (1.36) with `r̂ = π* = 0`; Prop. 2.3 and Woodford's "determinate iff `φ_p > 0`" (within `φ_p ≥ 0`) derived from Cochrane's results | `Links.WoodfordReduced`, `Links.woodfordReduced_iff_eq164`, `Links.wicksellModel_iff_woodford`, `Links.woodford_prop_2_3_linear`, `Links.woodford_determinate_iff` |
| Cochrane p. 373 (E6) vs Woodford (2003) (4.5), Prop. 4.11, pp. 313–314 (restated from the Woodford Chapter 4 project) | with `γ = α` the unified model's debt is Woodford's (4.5) with `τ_b = α`; passive iff `γ = α`; the locally Ricardian condition is `τ_b > 1 − β`; locally Ricardian implies passive, not conversely (`ρ = 1/2`, `α = 1/4`) | `Links.WoodfordDebt45`, `Links.fiscalBlock_debt45`, `Links.e6_passive_iff_woodford45`, `Links.woodford_ricardian_iff`, `Links.passive_of_ricardian`, `Links.passive_not_ricardian` |
| Cochrane pp. 368, 377–379, (16.26), (16.30) | an equilibrium of §16.8 satisfies the §16.3 fiscal block; the passive transversality condition via the `γ` criterion | `Links.isEquilibrium_hyper`, `Links.passive_tvc_of_gamma` |
| Cochrane pp. 137, 368, 373 | the unified model's transversality condition is §16.3's under perfect foresight; the stochastic passive result is the unified model's condition | `Links.tvc_pf_iff`, `Links.stoch_tvc_obs` |

## Restated Woodford blocks (GlobalDynamics, SelectionPatches.WoodfordMuBar, SelectionPatches.SGU)

These declarations are verbatim copies of the Woodford Chapter 2 project (`PriceLevelDetermination`
modules `GlobalDynamics`, `MoneyTargetingDynamics` and `SchmittGroheUribe`), namespace adapted.
Their docstrings cite Woodford (2003), *Interest and Prices*; they serve Cochrane's §16.8 and
§16.10, where Figure 16.2 is Woodford's Figure 2.4 in Cochrane's notation.

| Book | Claim | Lean |
| --- | --- | --- |
| Woodford (2003) §4.1, pp. 123–127 (survey lemma L5); for Cochrane pp. 378–380 | one-dimensional maps: monotone orbits, limits are fixed points, slope above one repels, below one attracts | `GlobalDynamics.orbit_monotone_of_le`, `GlobalDynamics.orbit_antitone_of_ge`, `GlobalDynamics.fixed_of_tendsto`, `GlobalDynamics.monotone_orbit_atTop_or_fixed`, `GlobalDynamics.antitone_orbit_atBot_or_fixed`, `GlobalDynamics.sign_near_of_deriv_pos`, `GlobalDynamics.repelling_of_one_lt_abs_deriv`, `GlobalDynamics.attracting_of_abs_deriv_lt_one` |
| Woodford (2003) (1.8), p. 67; (4.2), p. 124; for Cochrane p. 379 | the opportunity cost of money; the discount factor; the Ricardian rule `T = αW − ΔM` and its transversality condition | `GlobalDynamics.oppCost`, `GlobalDynamics.oppCost_zero`, `GlobalDynamics.discount`, `GlobalDynamics.ricardian_step`, `GlobalDynamics.ricardian_discounted`, `GlobalDynamics.ricardian_tvc`, `GlobalDynamics.ricardian_tvc_fails_of_alpha_zero` |
| Woodford (2003) (4.3)–(4.6), pp. 124–125; for Cochrane (16.29), (16.32) | (4.5) from the Fisher equation; (4.6) in the separable case; its map and orbits; (4.4) and a continuum of perfect-foresight equilibria | `GlobalDynamics.eq45_iff_fisher`, `GlobalDynamics.IsPath45`, `GlobalDynamics.IsPath46`, `GlobalDynamics.fisher_path_iff_eq45`, `GlobalDynamics.isPath45_iff_isPath46_of_const`, `GlobalDynamics.map46`, `GlobalDynamics.orbit46`, `GlobalDynamics.orbit46_succ`, `GlobalDynamics.orbit46_isPath`, `GlobalDynamics.isPath46_eq_orbit`, `GlobalDynamics.bound44Term`, `GlobalDynamics.bound44_summable`, `GlobalDynamics.continuum_pf_equilibria` |
| Woodford (2003) pp. 124–127; for Cochrane pp. 378–380 | the target is a steady state; the Taylor coefficient is the slope of the map; the second steady state; self-fulfilling deflations; local indeterminacy at the deflationary steady state; local repulsion and uniqueness at the target | `GlobalDynamics.target_isFixed`, `GlobalDynamics.hasDerivAt_map46`, `GlobalDynamics.taylorCoeff_eq_slope`, `GlobalDynamics.second_steady_state`, `GlobalDynamics.map46_step_down`, `GlobalDynamics.self_fulfilling_deflation46`, `GlobalDynamics.deflation46_strictAnti`, `GlobalDynamics.deflation46_eventually_deflation`, `GlobalDynamics.deflationary_steady_state_indeterminate`, `GlobalDynamics.target_locally_repelling`, `GlobalDynamics.target_locally_unique` |
| Woodford (2003) p. 127, Woodford survey error E6 | "inflation above target rises without bound" needs no steady state above the target; counterexample | `GlobalDynamics.inflation_unbounded46`, `GlobalDynamics.inflation_unbounded_iff`, `GlobalDynamics.phiCE`, `GlobalDynamics.e6_counterexample` |
| Woodford (2003) pp. 127–128, fn. 61 | real-balance effects: self-fulfilling deflations of (4.5) under monotone or "not too strongly increasing" `λ`, with (4.4); a restriction is needed | `GlobalDynamics.ratio_strictMonoOn`, `GlobalDynamics.steady_state45_iff`, `GlobalDynamics.isPath45_unique`, `GlobalDynamics.step45_down`, `GlobalDynamics.self_fulfilling_deflation45`, `GlobalDynamics.deflation45_exists`, `GlobalDynamics.deflation45_bound44`, `GlobalDynamics.step45_down_gen`, `GlobalDynamics.self_fulfilling_deflation45_gen`, `GlobalDynamics.deflation45_exists_gen`, `GlobalDynamics.antitone_lam_gives_gen`, `GlobalDynamics.phiCE45`, `GlobalDynamics.deflation45_counterexample`, `GlobalDynamics.bound44_summable_path`, `GlobalDynamics.deflation45_bound44_gen` |
| Woodford (2003) pp. 132–133 (Woodford survey error E4); for Cochrane §16.10.3, p. 390 | liabilities growing at `μ̄` rule out self-fulfilling deflations through the transversality condition, and keep the target iff `βμ̄ < Π*` | `SelectionPatches.WoodfordMuBar.tvcValue`, `SelectionPatches.WoodfordMuBar.tvcValue_succ`, `SelectionPatches.WoodfordMuBar.taylor_tvc_violated_of_eventually_le`, `SelectionPatches.WoodfordMuBar.e4_printed_inequality_false`, `SelectionPatches.WoodfordMuBar.e4_corrected_inequality`, `SelectionPatches.WoodfordMuBar.deflation_tvc_violated`, `SelectionPatches.WoodfordMuBar.zero_bound_inflation_eq_beta`, `SelectionPatches.WoodfordMuBar.zero_bound_tvc_violated`, `SelectionPatches.WoodfordMuBar.fig24_deflations_violate_tvc`, `SelectionPatches.WoodfordMuBar.target_tvc_iff` |
| Woodford (2003) (A.53)–(A.55), p. 654; for Cochrane (16.31)–(16.32), p. 393 | the Schmitt-Grohé–Uribe cash-goods economy: optimal cash purchases, `λ`, money demand, `λ(i)` and its elasticity | `SelectionPatches.SGU.c1opt`, `SelectionPatches.SGU.uSGU`, `SelectionPatches.SGU.c1opt_optimal`, `SelectionPatches.SGU.lambda_A54_binding`, `SelectionPatches.SGU.lambda_A54_satiated`, `SelectionPatches.SGU.LSGU`, `SelectionPatches.SGU.money_demand_A55`, `SelectionPatches.SGU.lamSGU`, `SelectionPatches.SGU.lambda_of_i`, `SelectionPatches.SGU.lamSGU_tendsto_atTop`, `SelectionPatches.SGU.elasticity`, `SelectionPatches.SGU.hasDerivAt_lamSGU`, `SelectionPatches.SGU.elasticity_lt_one`, `SelectionPatches.SGU.elasticity_tendsto_one`, `SelectionPatches.SGU.elasticity_i_lt_one` |
| Woodford (2003) (A.56), pp. 654–655 | the truncated Taylor rule and the functions `A`, `B` of (4.5) | `SelectionPatches.SGU.ellSGU`, `SelectionPatches.SGU.phiSGU`, `SelectionPatches.SGU.one_add_phiSGU`, `SelectionPatches.SGU.phiSGU_nonneg`, `SelectionPatches.SGU.phiSGU_continuous`, `SelectionPatches.SGU.phiSGU_target`, `SelectionPatches.SGU.taylorCoeff_phiSGU`, `SelectionPatches.SGU.sguA`, `SelectionPatches.SGU.sguB`, `SelectionPatches.SGU.sguC`, `SelectionPatches.SGU.lamSGU_phi_pos`, `SelectionPatches.SGU.eq45_iff_AB`, `SelectionPatches.SGU.sguAB_formula`, `SelectionPatches.SGU.sguB_formula`, `SelectionPatches.SGU.sguA_antitone`, `SelectionPatches.SGU.sguA_tendsto`, `SelectionPatches.SGU.sguB_strictAntiOn`, `SelectionPatches.SGU.sguB_gt`, `SelectionPatches.SGU.sguB_tendsto`, `SelectionPatches.SGU.sguA_lt_B_above`, `SelectionPatches.SGU.sguB_lt_A_below`, `SelectionPatches.SGU.sgu_at_beta`, `SelectionPatches.SGU.sguAB_continuousAt` |
| Woodford (2003) p. 655 (Woodford survey error E5); for Cochrane p. 393 | under the added hypothesis `β + θΠ*(1 − φ_π) > 0`: no successor above `Π̄`, no hyperinflation, deflations converge to `β`, the target is the unique perfect-foresight equilibrium; without it, a counterexample | `SelectionPatches.SGU.sguPibar`, `SelectionPatches.SGU.sguPibar_spec`, `SelectionPatches.SGU.sgu_no_successor`, `SelectionPatches.SGU.sgu_no_hyperinflation`, `SelectionPatches.SGU.sgu_deflation_tendsto`, `SelectionPatches.SGU.sgu_unique_pf_equilibrium`, `SelectionPatches.SGU.gE5`, `SelectionPatches.SGU.priceFrom`, `SelectionPatches.SGU.phiE5`, `SelectionPatches.SGU.gE5_mem`, `SelectionPatches.SGU.gE5_eq45`, `SelectionPatches.SGU.e5_counterexample` |

## Shared tools

| Book | Claim | Lean |
| --- | --- | --- |
| Chapter 16 throughout | the expectation axioms, adaptedness, AR(1) processes, pull-out, perfect foresight; bounded processes; finite event trees and the coin-flip tree with its shock | `ExpectationSystem`, `ExpectationSystem.Adapted`, `ExpectationSystem.IsAR1`, `ExpectationSystem.PullOut`, `perfectForesight`, `perfectForesight_pullOut`, `BoundedProc`, `ExpectationsFiniteTree.FiniteTree.toExpectationSystem`, `ExpectationsFiniteTree.finiteTree_pullOut`, `ExpectationsFiniteTree.coinSystem`, `ExpectationsFiniteTree.coinShock` |
| (2.17), p. 35; (16.5)–(16.6), p. 364 | the forward series (used by `FTPLSimple`); the scalar forward solution of `φπ_t = E_tπ_{t+1} − u_t` (used by `SimplestModel` for (16.6)); the sunspot family (used by `ObservationalEquivalence`); the dominated-sum lemma (used by `Innovation`) | `ExpectationSystem.forwardSeries`, `ForwardSolution.ScalarEq`, `ForwardSolution.scalarSol`, `ForwardSolution.scalar_existsUnique`, `ForwardSolution.sunspotFamily`, `ForwardSolution.sunspotFamily_solves`, `ForwardSolution.E_tsum_dom` |
| shared core, not used by Chapter 16 | Schur–Cohn determinacy for `2 × 2` systems and the vector forward solution, carried for the later Cochrane projects | `SchurStable`, `schurStable_iff_roots`, `ForwardSolution.existsUnique_bounded` |
