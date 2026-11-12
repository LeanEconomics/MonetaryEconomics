# Keynesian models with sticky prices in Lean

This is the `Cochrane/KeynesianStickyPrices/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Chapter 17, "Keynesian models with sticky prices" (pp. 397–421), and
Chapter 18, "History and implications" (pp. 422–432), together with Online Appendix A1, §1.8,
"Three-equation model solution" (pp. 571–572), and §1.13.1, "Calculating responses of the
standard new-Keynesian model" (pp. 586–588). The linear models are stated for an arbitrary
expectation operator, so every result about them covers perfect foresight and genuine
uncertainty: processes are `ℕ → Ω → ℝ` and every equation holds state by state. The full-model
paths of §17.4 are perfect-foresight sequences after the announcement or shock, as in the book's
figures; their expected-path and news forms are also proved for every expectation system and,
almost surely, on genuine probability spaces with Mathlib's conditional expectation. Statements
about an infinite past are ℤ-indexed: pathwise under perfect foresight, and almost surely on a
probability space with a ℤ-indexed filtration. The central objects
are the simple sticky-price model (17.1)–(17.14), under adaptive and under rational expectations,
and the three-equation model (17.15)–(17.33), whose equations are also derived from household and
price-setting problems; "determinate" means exactly one bounded equilibrium for every bounded
adapted disturbance. The library contains **1638 theorems**, including the shared core and the
infrastructure restated from the Woodford Chapter 4 and Cochrane Chapter 2 and 22 projects; 1034
of them are in the forty-eight chapter modules.

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises. Survey codes E7–E11 and E24 refer to
the survey of Chapters 11–19.

Headline results, in the namespace `Cochrane.KeynesianStickyPrices`:
* **The static IS model: adaptive versus rational expectations.** Deleting `E_tx_{t+1}` from the
  IS and Phillips curves leaves the single condition (17.5) (`StaticIS.exists_static_iff_17_5`).
  With adaptive expectations (17.6) the solution is unique given `π_{−1}` but spirals away from a
  peg, `π_t − ī = (1 + σκ)^{t+1}(π_{−1} − ī)` (`StaticIS.adaptive_existsUnique`,
  `StaticIS.adaptive_peg_unbounded`). With rational expectations (17.7) the coefficient lies in
  `(0, 1)`, every expectational error gives an equilibrium and there is never a unique bounded
  one (`StaticIS.coeff_17_7`, `StaticIS.reFamily_solves`, `StaticIS.re_not_unique`). On an
  infinite past every bounded solution is the backward moving average (17.8), and conversely
  (`StaticIS.eq_17_8`, `SharedTools.backward_series_solves`). Figures 17.1–17.2 are exact
  (`StaticIS.fig17_1_path`, `StaticIS.fig17_2_solves`, `StaticIS.fig17_2_frictionless_limit`).
* **Policy rules in both models (E7).** With `i = φπ + u` the adaptive model is stable, and the
  rational-expectations model determinate, iff **`φ > 1` or `φ < −1 − 2/(σκ)`**
  (`RulesAdaptiveRE.adaptiveStable_iff`, `RulesAdaptiveRE.reDeterminate_iff`). So "`|φ| > 1`
  stabilizes" fails at `σκ = 1/2`, `φ = −3/2`, and "`φ < 1` is indeterminate" fails at `φ = −6`
  (`RulesAdaptiveRE.printed_abs_phi_gt_one_stabilizes_false`,
  `RulesAdaptiveRE.printed_passive_indeterminate_false`). With `φ > 1` a rule
  `i = i* + φ(π − π*)` selects any equilibrium of the peg model
  (`RulesAdaptiveRE.rule_selects_any_delta`).
* **AR(1) responses.** (17.12)–(17.13) give the unique bounded equilibrium, with both printed
  forms and the frictionless limits (16.9) and (16.11) (`AR1Responses.eq_17_12`,
  `AR1Responses.eq_17_13`, `AR1Responses.tendsto_17_12`). `η = 1` is super-Fisherian and
  `η = 1/(1 + σκ)` is the open-mouth case (`AR1Responses.superFisher_simple`,
  `AR1Responses.openMouth_simple`). In the full model (1.59)–(1.62) hold, and for `φ > 1` the
  minimal-state-variable solution is the unique bounded equilibrium (`AR1Responses.eq_1_59_iff`,
  `AR1Responses.msv_unique`). The open-mouth persistence `η*` is the unique root in `(0, 1)` of
  `βη² − (1 + β + σκ)η + 1`; it equals `1/λ₁`, and `0.508 < η* < 0.509` at the Figure 17.8
  parameters (`AR1Responses.eq_etaStar`, `PersistenceFreedom.etaStar_eq_inv_lam1`,
  `AR1Responses.etaStar_fig17_8`).
* **Any persistence with any sign (E8).** For news revealed at date 1, every bounded rate path is
  compatible with every value of unexpected inflation, also on the coin-flip tree and in the full
  model (`PersistenceFreedom.any_sign`, `PersistenceFreedom.any_sign_coin`,
  `PersistenceFreedom.full_any_sign`), while the long-run response is always one
  (`PersistenceFreedom.long_run_one`, `FullModel.tendsto_pi`). The printed inverse of (17.14)
  omits past expectational errors; the corrected inverse adds them
  (`PersistenceFreedom.corrected_inverse`, `PersistenceFreedom.printed_inverse_false`).
* **The adaptive Taylor rule.** With adaptive expectations inflation is an AR(2); in Figure 17.4
  the rate rises, reverses course, and converges with inflation to `−1/(φ − 1)`; a pegged rate
  spirals (`AdaptiveTaylor.ar2`, `AdaptiveTaylor.fig17_4_i_reverses`,
  `AdaptiveTaylor.fig17_4_tendsto`, `AdaptiveTaylor.peg_spiral`).
* **The full model.** Under perfect foresight the bounded equilibria of (17.18) are indexed by
  initial inflation `π_0`, the no-surprise one being the two-sided moving average (5.5)
  (`FullModel.pf_existsUnique`, `FullModel.twoSided_eq`). In Figure 17.5 inflation rises before
  an announced rate rise and output is negative up to the rise (`FullModel.antPath_le_T`,
  `FullModel.antPath_x_neg`, `FullModel.rise_raises_inflation`); the rise anticipated from the
  infinite past has exactly one bounded path on ℤ, `FullModel.zPath`, to which every response
  converges as the announcement recedes (`FullModel.zPath_existsUnique`,
  `FullModel.tendsto_zPath`). For Figure 17.6, the surplus news implied by the flow condition is
  `ρ(1 − p)/(λ₁ − ρ) − p` (`TidyR5StochasticFiscal.surplus_news_rise`;
  `FiscalUnderpinnings.deltaS`, `(1 − p)/(λ₁ − ρ) − p`, omits the factor `ρ` and agrees only for
  `ρ = 1` or `p = 1`), and B has `Δs = −1` exactly (`FiscalUnderpinnings.deltaS_closed`,
  `FiscalUnderpinnings.deltaS_B`); the
  labels `δ₁ = ±1%` of A and E are inconsistent with the printed `Δs` values for any parameters
  (`FiscalUnderpinnings.fig17_6_inconsistent`).
* **Fiscal underpinnings.** (17.19) is exact with `r_{t+1+j}` the real rate earned between
  `t + j` and `t + 1 + j`; with (17.16)'s dating the real-rate sum needs a factor `ρ`
  (`FiscalUnderpinnings.eq_17_19`, `FiscalUnderpinnings.printed_own_dating_iff`). Lower
  inflation needs a fiscal contraction (`FiscalUnderpinnings.fiscal_contraction`). The Figure
  17.7 numbers 3.55, 2.23, 0.91, −0.41 and 2.55 are certified by interval bounds, and the
  reverse-engineered disturbances are not AR(1) (`FiscalUnderpinnings.fig17_7_values`,
  `FiscalUnderpinnings.fig17_7_real_rates`, `FiscalUnderpinnings.fig17_7_u_not_ar1`). E10:
  `5 × 2.23 = 11.15` (`FiscalUnderpinnings.e10`).
* **Optimal policy (E9).** Any inflation or output path is attainable, and `φ` drops out of the
  equilibrium (`OptimalPolicy.any_pi_attainable`, `OptimalPolicy.any_x_attainable`,
  `TaylorDeterminacy.phi_irrelevance_sets`). The `x* = 0` intercept is
  `(1 − φβ)E_t∑βʲu_{π,t+1+j} − φu_{π,t} + u_x/σ` (`OptimalPolicy.e9_intercept`,
  `OptimalPolicy.e9_counterexample`).
* **Taylor determinacy with an output response.** The deviation system is determinate iff
  `D ≠ 0` and `(T/D, β/D)` is Schur-stable; with `φ_x = 0` iff `φ > 1` or
  `φ < −(1 + 2(1 + β)/(σκ))` (1.58) (`TaylorDeterminacy.determinate_iff`,
  `TaylorDeterminacy.determinate_iff_phi`). "`φ > 1` is neither necessary nor sufficient":
  non-necessity holds even with `φ_x = 0`, but **non-sufficiency needs `φ_x < 0`**, since with
  `φ_x ≥ 0`, `φ > 1` is sufficient (`TaylorDeterminacy.not_necessary_negative`,
  `TaylorDeterminacy.not_sufficient`, `TaylorDeterminacy.sufficient_of_phix_nonneg`). For
  `φ > 1` the eigenvalues can be complex, with modulus above one (E11;
  `TaylorDeterminacy.roots_phi_gt_one`, `AR1Responses.lag_roots_complex_example`). The shock
  matrix of (1.55) has `−β`, not `−1`, as its `u_x` entry (`TaylorDeterminacy.printed_1_55_iff`).
* **Chapter 18.** The permanent-income MPC `r/(1 + r − η)` depends on persistence
  (`History.pih_consumption`, `History.mpc_injective`); with (18.1) and `φ_x ≥ 0`, `φ_π > 1`
  gives determinacy (`History.rule181_determinate_iff`); (18.2) without inertia is a structural
  system with its determinacy condition (`History.rule182_determinate_iff`); every statistic of
  the equilibrium paths is the same for all `φ` in the determinacy region, (18.3)
  (`History.likelihood_flat`); and the Clarida–Galí–Gertler reading holds only for small output
  responses (`History.cgg_reading`).
* **Links.** The simple model is exactly the `β = 0` case of the full model: for the
  perfect-foresight equation, the infinite-past solution, the deviation system and determinacy
  (`Links.second_beta_zero_iff`, `Links.secondZ_beta_zero`, `Links.deviation_beta_zero`,
  `Links.determinate_beta_zero_iff_reDeterminate`). MSV uniqueness holds on the whole
  determinacy region, including the oscillating branch of (1.58)
  (`Links.msv_unique_of_determinate`).
* **The full model on ℤ for any rate path.** Under perfect foresight, for every bounded rate path
  `i : ℤ → ℝ` and `β > 0`, (17.18) has exactly one bounded solution, the two-sided moving
  average (5.5) with the stable root solved backward over the infinite past and the unstable one
  forward, also as a genuine two-sided sum over ℤ (`FullModelTidy.secondZ_existsUnique`,
  `FullModelTidy.eq_piZ`, `FullModelTidy.piZ_eq_tsum_int`). The Figure 17.5 path is the special
  case of the step (`FullModelTidy.zPath_eq_piZ`), and the bounded `(x, π)` equilibrium on ℤ
  exists and is unique (`FullModelTidy.eqmZ_existsUnique`).
* **Real explosions for every `φ` (p. 421).** Under perfect foresight, some deviation has
  `βᵗx̃_t → +∞` iff `φ < 1/β`, or `β + σκ > 1` with real roots, `4β(1 + σκφ) ≤ (1 + β + σκ)²`
  (`FullModelTidy.explodes_atTop_iff`); `βᵗx̃_t` is unbounded for some deviation iff `φ < 1/β` or
  `β(1 + σκφ) > 1`, and the real transversality condition fails for some deviation iff `φ < 1/β`
  or `β(1 + σκφ) ≥ 1` (`FullModelTidy.unbounded_iff`, `FullModelTidy.tvc_fails_iff`). At the
  book's own calibrations the roots are complex: real explosions exist but oscillate, and none
  tends to `±∞` (`FullModelTidy.book_calibration_oscillates`,
  `FullModelTidy.fig17_7_calibration_oscillates`). At `β = 0.95`, `σ = 1`, `κ = 1/25`, `φ = 1.2`
  the system is determinate, yet every deviation satisfies the real transversality condition
  (`FullModelTidy.tvc_cannot_rule_out`).
* **Real explosions with an output response and under uncertainty (p. 421).** With
  `ĩ = φπ̃ + φ_xx̃`, `T = 1 + β + σκ + βσφ_x` and `B = β(1 + σφ_x + σκφ)`, for every `φ` and `φ_x`:
  some deviation has `βᵗx̃_t → +∞` iff `φ < 1/β` or (`T > 2` and `4B ≤ T²`); `βᵗx̃_t` is unbounded
  for some deviation iff `φ < 1/β`, `|B| > 1`, `1 + B + T < 0` or `B = 1 ∧ T = −2`; the real
  transversality condition fails iff `φ < 1/β`, `|B| ≥ 1` or `1 + B + T ≤ 0`
  (`TidyR5RealExplosions.explodesX_iff`, `TidyR5RealExplosions.unboundedX_iff`,
  `TidyR5RealExplosions.tvcX_fails_iff`), from the characterisation of
  `y_{t+2} = Ay_{t+1} − By_t` for all real `A`, `B` (`TidyR5Recurrence.exists_atTop_iff`,
  `TidyR5Recurrence.exists_unbounded_iff`, `TidyR5Recurrence.exists_not_tendsto_zero_iff`). At the
  Figure 17.8 calibration the output response `φ_x = 1/2` keeps the system determinate and
  produces a monotone real explosion (`TidyR5RealExplosions.book_calibration_output_response`).
  The same conditions characterise `E_tβʲx̃_{t+j}` under every expectation system and, with
  positive probability or for the mean, on every probability space
  (`TidyR5RealExplosions.explodes_uncertainty_iff`,
  `TidyR5ExplosionsMeasure.explodes_measure_iff`, `TidyR5ExplosionsMeasure.explodes_mean_iff`).
  Read pathwise the claim fails: on the i.i.d. coin space every deviation satisfies the expected
  real transversality condition, yet a deviation's realised `βᵗx̃_t` is unbounded almost surely
  (`TidyR5PathwiseExplosion.pathwise_explosion`).
* **The full-model paths under uncertainty (§17.4).** For every expectation system, and almost
  surely on a probability space, expected paths and the news `ΔE_{s+1}` about the whole future are
  perfect-foresight equilibria, so Figures 17.5–17.6 are impulse responses
  (`TidyR5StochasticPaths.expected_path`, `TidyR5StochasticPaths.news_path`,
  `TidyR5StochasticPaths.news_rise`, `TidyR5StochasticPathsMeasure.news_path_ae`). The equilibria
  of Figure 17.6 are indexed by initial inflation and an arbitrary bounded innovation process,
  with existence and uniqueness (`TidyR5StochasticPaths.innov_eqm_existsUnique`,
  `TidyR5InnovEqmMeasure.piM_equilibrium`, `TidyR5InnovEqmMeasure.eq_piM`); each is the unique
  equilibrium under its reverse-engineered disturbance
  (`TidyR5StochasticPaths.reverse_engineer_innov`, `TidyR5ReverseMeasure.reverse_engineer_piM`).
  The surplus news of Figures 17.6–17.7, including `Σs` per unit rate shock, follows from (17.19)
  (`TidyR5StochasticFiscal.surplus_news_rise`,
  `TidyR5StochasticFiscal.surplus_news_ar1_eq_sigmaS`,
  `TidyR5StochasticFiscalMeasure.surplus_news_rise_ae`).
* **An infinite past under uncertainty.** On a probability space with a ℤ-indexed filtration
  (`TidyR6ZExpectations.ZMeasExpectationSystem`), every bounded equilibrium of (17.7) is almost
  surely the backward moving average (17.8) of the rates and its own expectational errors, and
  for every bounded martingale-difference sequence of errors there is exactly one
  (`TidyR6ZStaticIS.eq_17_8_ae`, `TidyR6ZStaticIS.piB_equilibrium`, `TidyR6ZStaticIS.eq_piB`);
  uniqueness given the errors needs the bound as `t → −∞` (`TidyR6ZStaticIS.remote_family_bdd_iff`,
  `TidyR6ZStaticIS.remote_one_solves`). The printed inverse of (17.14) holds almost surely at
  every date iff every expectational error is zero (`TidyR6ZStaticIS.printed_inverse_iff`). In the
  full model the bounded equilibria on ℤ are indexed by their innovations alone, with existence
  and almost-sure uniqueness (`TidyR6ZFullModel.piZM_equilibrium`, `TidyR6ZFullModel.eq_piZM`,
  `TidyR6ZFullModel.eqm_unique_given_innov`). For the rise of Figure 17.5 every bounded
  equilibrium is `zPath` plus the backward sum of its innovations, and `zPath` is the only one iff
  the filtration carries no news (`TidyR6ZFullModel.zPath_representation`,
  `TidyR6ZFullModel.zPath_unique_iff_noNews`); on a coin revealed at date 1 there is a second
  (`TidyR6ZFullModel.zPath_not_unique_coin`).
* **The household and price-setting problems behind (17.15)–(17.17).** On a genuine probability
  space and on finite trees, the household's Euler equation gives the IS curve exactly, with the
  explicit second-order precautionary disturbance `u_x = −σE_t[e^z − 1 − z] ≤ 0`
  (`TidyR6EulerIS.euler_iff_IS`, `TidyR6EulerIS.isRem_bounds`, `TidyR6EulerIS.optimal_iff_IS`).
  Both price setters named on p. 118 give (17.17) exactly with explicit second-order
  remainders: costs of changing prices (Rotemberg), with `κ = (ε − 1)Ȳ^{1−γ}(γ + ϕ)/φ`
  (`TidyR6RotembergPC.nonlinPC_iff_PCM`, `TidyR6RotembergPC.optimal_iff_PC`), and Calvo, with
  `κ = (1 − α)(1 − αβ)(γ + ϕ)/(α(1 + εϕ))`, an almost-sure version and the single bound
  `|u_π| ≤ calvoC·L²` (`TidyR6CalvoPC.calvo_iff_PC`, `TidyR6CalvoAE.calvo_iff_PC_ae`,
  `TidyR6CalvoBound.calvoRem_abs_le`). Equilibria of the derived economies are exactly
  `FullModel.Model` with the remainders as disturbances (`TidyR6DerivedModel.eqm_iff_model`,
  `TidyR6DerivedModel.Tree.eqm_iff_model`, `TidyR6CalvoDerived.eqm_iff_model_calvo`), and the
  steady state is an equilibrium (`TidyR6DerivedModel.steady_state_eqm`). The Rotemberg
  first-order condition is necessary over all plans but not globally sufficient: a deep deflation
  satisfies it without being optimal (`TidyR6RotembergGlobal.cex_not_optimal`); it is sufficient
  among all plans near the steady state (`TidyR6RotembergLocal.optimal_near_ss`,
  `TidyR6RotembergLocal.optimal_near_ss_yeo`). The joint yeoman-farmer problem agrees with the
  decentralised household and price-setter problems (`TidyR6JointYeoman.joint_iff_decentral`,
  `TidyR6JointGlobal.joint_of_decentral_u`, `TidyR6JointGlobal.joint_iff_decentral_near_ss`).
  Preference and markup shocks give `u_x = −σ(E_tζ_{t+1} − ζ_t) + rem` and
  `u_π = κ̃(μ − ζ) + rem` (`TidyR6ShockModel.eqm_iff_modelZ`).
* **(18.2) with inertia, a completion.** The book makes no determinacy claim. For all parameters
  with `σ, κ, β > 0`, under any expectation system: with `1 − σφ_{x,1} ≠ 0`, determinate iff
  exactly one root of `det(λM − N)` is inside the unit circle and two outside, and the rule
  responds along the peg's stable direction, `κ(φ_π + φ_{π,1}μ) + (φ_x + φ_{x,1}μ)(1 − βμ) ≠ 0`
  at `μ = 1/λ₁` (`TidyR5Inertia.determinate182_iff`), with a closed form in the eight
  parameters (`TidyR5InertiaForward.determinate182_closed_iff`); with `σφ_{x,1} = 1` the system
  drops an order and is determinate iff `D₁D₋₁ < 0` and the same response condition holds
  (`TidyR5InertiaSingular.determinate182_singular_iff`, through the singular-pencil
  Blanchard–Kahn theorem). With backward-looking responses it is determinate iff
  `κ(φ_π + φ_i − 1) + (1 − β)φ_x > 0` and `φ_π > 0 ∨ φ_x > 0`
  (`TidyR5Inertia.determinate182_noForward_iff`): the long-run Taylor principle with inertia is
  not sufficient on its own (`TidyR5Inertia.not_determinate182_no_response`). The response
  condition is polynomial: with `A = κφ_π + φ_x + φ_{x,1}`, `B = κφ_{π,1} − βφ_x − φ_{x,1}(β + σκ)`
  and the resultant `R = βA² + (1 + β + σκ)AB + B²`, genericity holds iff `R ≠ 0` or
  `B(A + B) < 0`, so determinacy is a set of polynomial (in)equalities in the eight parameters
  (`TidyR6Genericity182.generic182_iff_poly`, `TidyR6Genericity182.determinate182_poly_iff`,
  `TidyR6Genericity182.determinate182_singular_poly_iff`). `R ≠ 0` alone is not necessary
  (`TidyR6Genericity182.res182_zero_but_generic`), and the parameters at which genericity fails
  form a nonempty Lebesgue-null set (`TidyR6Genericity182.nongeneric_with_response`,
  `TidyR6Genericity182.volume_nonGeneric`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections are the confirmed errors of the chapter survey:
* the stability and determinacy sets of (17.10)–(17.11), p. 402: `φ > 1` or
  `φ < −1 − 2/(σκ)`, not "`|φ| > 1`" and "`φ < 1` indeterminate" (E7);
* the inverse of (17.14), p. 405, which omits past expectational errors (E8);
* the `x* = 0` intercept, p. 418 (E9);
* `5 × 2.23 = 11.15`, p. 414 (E10);
* complex roots and eigenvalues, A1 pp. 572 and 587: "unstable" and "explosive" are statements
  about moduli (E11).

Three further errors were found: the `u_x` entry of the shock matrix in A1 (1.55), p. 586; the
dating of the real rate in (17.19), p. 411; and the labels of equilibria A and E in Figure 17.6,
p. 410, which cannot match the printed `Δs` values (the survey's E24 left these values unchecked).
In addition, the formalisation makes precise "`φ > 1` is neither necessary nor sufficient"
(p. 420, A1 p. 587), the real explosions "`E_tβʲx_{t+j} → ∞`" for `φ ≥ 1/β` (p. 421), "with
`φ < 1` we have multiple equilibria" (A1 p. 587), the Clarida–Galí–Gertler reading (p. 428), the
output response of Figure 17.5 (p. 409), the infinite past of (17.8) (p. 400), the
cross-reference to (1.62) for (1.60) (A1 p. 588) and the rounding `η* ≈ 0.51` (p. 416). With
an output response the real-explosion claim of p. 421 is no longer decided by the determinant
condition, and at the Figure 17.8 calibration with `φ_x = 1/2` the explosions are monotone; under
genuine uncertainty the claim holds only in its expectational form, not pathwise. For (18.2),
where the book makes no claim, the long-run Taylor principle with inertia is not sufficient. The
micro-foundations of p. 118 are made precise: "linearize ... suppressing constants" drops a
nonpositive second-order precautionary term from the IS curve; the price setter's first-order
condition is not globally sufficient, only near the steady state; a preference shock on the
utility of consumption enters the Phillips curve as well as the IS curve; and the slope `κ`,
which the book leaves unspecified, is given for both price setters.
Corrections to the earlier formalisation, not the book: `FiscalUnderpinnings.deltaS`
omits the factor `ρ` on real-rate news, so the corrected D is `ρ/(λ₁ − ρ)` and C is at
`δ = ρ/λ₁` (`TidyR5StochasticFiscal.surplus_news_D`,
`TidyR5StochasticFiscal.surplus_news_zero_iff`); decentralised ⇒ joint optimality, first stated
only for prices in the concavity region, holds over all uniformly bounded plans
(`TidyR6JointGlobal.joint_of_decentral_u`); `TidyR6CalvoPC.calvo_iff_PC` needs neither its
separate reset-price bound nor everywhere bounds (`TidyR6CalvoBound.calvo_iff_PC_small`,
`TidyR6CalvoAE.calvo_iff_PC_ae`); the uniqueness on ℤ of `FullModel.zPath_existsUnique`,
`FullModelTidy.secondZ_existsUnique` and `FullModelTidy.eqmZ_existsUnique` holds under perfect
foresight only, and fails read under uncertainty (`TidyR6ZFullModel.zPath_not_unique_coin`); and
the genericity condition of (18.2) is not the resultant condition `R ≠ 0` but `R ≠ 0` or
`B(A + B) < 0` (`TidyR6Genericity182.res182_zero_but_generic`,
`TidyR6Genericity182.generic182_iff_poly`).

Not formalised:
* the verbal and historical parts of Chapter 18 (§§18.1–18.3, beyond footnote 1 and
  (18.1)–(18.3)), Sims' (2016) backward-looking fiscal model (p. 431), the determinacy plots of
  Cochrane (2011b) (p. 420, A1 p. 587), and the remarks on why real explosions are not observed
  (p. 421);
* for the household and price-setting problems behind (17.15)–(17.17): whether joint
  yeoman-farmer optimality implies the price setter's global optimality far from the steady
  state (it does near it, `TidyR6JointGlobal.joint_iff_decentral_near_ss`; decentralised ⇒ joint
  over merely date-wise bounded competitors needs their admissibility, a hypothesis of
  `TidyR6JointGlobal.joint_of_decentral_class`); an explicit radius: the `ρ` of
  `TidyR6RotembergLocal.near_ss` is existential (the conditions `TidyR6RotembergLocal.PotCond`
  themselves are explicit); the existence of `L₀ > 0` with `TidyR6CalvoBound.Small` on
  `[0, L₀]`, stated in the docstring but not as a Lean theorem; the insufficiency of
  integrability-only Calvo hypotheses, of which only the uniqueness failure
  `TidyR6CalvoAE.unbounded_solves` is in Lean (divergence of the discounted weights under
  integrable inflation is argued in the docstring); and the law of large numbers over a continuum
  of firms: the Calvo index is assumed (almost surely in `TidyR6CalvoAE`), derived only from
  deterministic cohort masses (`TidyR6CalvoReset.index_eq_of_cohort`);
* the Figure 17.6 numbers 0.67, 1.66, −1.53 and 2.99: the book gives no `σ, κ, β, ρ` for the
  figure. Only the `Δs` formula (with the factor `ρ`, `TidyR5StochasticFiscal.surplus_news_rise`),
  B, C and D, and the inconsistency of A and E (`FiscalUnderpinnings.fig17_6_inconsistent`,
  `TidyR5StochasticFiscal.fig17_6_inconsistent_corrected`) are proved;
* for the infinite past under uncertainty: the household and price-setting problems behind
  (17.15)–(17.17) are posed from date 0 only; existence of bounded equilibria on ℤ is proved on
  the probability space (`TidyR6ZStaticIS.piB_equilibrium`, `TidyR6ZFullModel.piZM_equilibrium`),
  not for the abstract `TidyR6ZExpectations.ZExpectationSystem`, for which only the restriction
  to the dates `t ≥ s` and the state-by-state (17.8) are proved
  (`TidyR6ZStaticIS.eq_17_8_abstract`, `TidyR6ZFullModel.modelZA_restrict`); and downward
  martingale convergence (`E_t` as `t → −∞`) is not used: the remote past enters only as
  information known at every date (`TidyR6ZExpectations.ZMeasExpectationSystem.remote`);
* for (18.2), whether the set of parameters at which genericity fails is Zariski-closed. It is
  semialgebraic (`TidyR6Genericity182.resp_zero_iff`), inside the proper hypersurface `R = 0`
  (`TidyR6Genericity182.nongeneric_subset_res`, `TidyR6Genericity182.res182_ne_zero_somewhere`),
  nonempty (`TidyR6Genericity182.nongeneric_no_response`), a strict subset of that hypersurface
  (`TidyR6Genericity182.res182_zero_but_generic`) and Lebesgue-null
  (`TidyR6Genericity182.volume_nonGeneric`);
* the likelihood of (18.3) as a statistical object: `History.likelihood_flat` is a statement about
  every function of the equilibrium paths;
* A1 §1.9 (matrix and state-variable methods, pp. 573–578) as an exposition, and the
  continuous-time parts of §1.13 (pp. 580–585), which the chapter only points to; the survey's E11
  items on pp. 574–575 belong there. The Blanchard–Kahn theorems that §1.9 describes are restated
  from the Woodford Chapter 4 project and used for (18.2), with the degree-two root count
  `TidyR5QuadRoots.count_one_iff`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](KeynesianStickyPrices/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (shared core, restated from the earlier projects) |
| [Expectations](KeynesianStickyPrices/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; adapted and AR(1) processes; forward series; vector uniqueness; the pull-out property (shared core) |
| [ExpectationsFiniteTree](KeynesianStickyPrices/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; the coin-flip tree and its shock (shared core) |
| [ForwardSolution](KeynesianStickyPrices/ForwardSolution.lean) | 44 | The forward solution of `z_t = aE_tz_{t+1} + u_t` and the sunspot family (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [SharedTools](KeynesianStickyPrices/SharedTools.lean) | 11 | Lemmas proved in both chains and collected once: stable recursions, forward sums, ℤ-indexed backward recursions (17.8), the structural matrices `P`, `Q`, `P⁻¹Q` |
| [StaticIS](KeynesianStickyPrices/StaticIS.lean) | 43 | §§17.1–17.2: (17.1)–(17.8), adaptive versus rational expectations, the solution family, (17.8) on the infinite past, Figures 17.1–17.2, selection by fiscal policy |
| [RulesAdaptiveRE](KeynesianStickyPrices/RulesAdaptiveRE.lean) | 23 | §§17.2–17.3: (17.9)–(17.11), stability and determinacy sets with E7 corrected, the forward solution, selection by a rule |
| [AR1Responses](KeynesianStickyPrices/AR1Responses.lean) | 46 | §17.3.1, §17.4.3, A1 §1.8 and §1.13.1: (17.12)–(17.13), (1.59)–(1.62), MSV uniqueness, lag roots with E11, super-Fisherian and open-mouth cases, `η*`, Figures 17.3 and 17.8 |
| [FullModel](KeynesianStickyPrices/FullModel.lean) | 61 | §§17.4–17.4.1: (17.15)–(17.18), the roots (restated from the Chapter 5 project), the two-sided moving average, equilibria indexed by `π_0`, Figure 17.5 including the path anticipated from the infinite past, Figure 17.6 |
| [PersistenceFreedom](KeynesianStickyPrices/PersistenceFreedom.lean) | 16 | §17.3.1, §17.4.1, §17.4.3: (17.14) and its corrected inverse (E8), any persistence with any sign, long-run response one, `η* = 1/λ₁` |
| [AdaptiveTaylor](KeynesianStickyPrices/AdaptiveTaylor.lean) | 12 | §17.3.2: the AR(2), Figure 17.4, stability, the peg spiral |
| [FiscalUnderpinnings](KeynesianStickyPrices/FiscalUnderpinnings.lean) | 39 | §17.4.2: (17.19) with the dating correction, the fiscal contraction, reverse engineering, Figure 17.7 numbers, E10, the `Δs` of Figure 17.6 (without the factor `ρ` on real-rate news; corrected in `TidyR5StochasticFiscal`) and its label inconsistency |
| [OptimalPolicy](KeynesianStickyPrices/OptimalPolicy.lean) | 20 | §17.5.1: (17.22)–(17.28), any path attainable, E9 corrected, Woodford's loss, constant intercepts |
| [TaylorDeterminacy](KeynesianStickyPrices/TaylorDeterminacy.lean) | 36 | §17.5.2 and A1 (1.55)–(1.58): structural systems, determinacy with `φ_x`, (1.58), Bullard–Mitra, "neither necessary nor sufficient", (1.55) corrected, (1.57) and E11, `φ` irrelevance, real explosions |
| [History](KeynesianStickyPrices/History.lean) | 11 | Chapter 18: the PIH footnote, (18.1)–(18.3), the Clarida–Galí–Gertler reading |
| [Links](KeynesianStickyPrices/Links.lean) | 28 | Links between the two chains: the simple model as the `β = 0` case of the full model, (1.55) and (17.33), MSV uniqueness on the whole determinacy region, lag roots and eigenvalues, `zPath` and the `full_any_sign` family, (18.1)–(18.2) |
| [FullModelTidy](KeynesianStickyPrices/FullModelTidy.lean) | 54 | §17.4.1 and §17.5.2: (17.18) and the equilibrium on ℤ for every bounded rate path, the two-sided ℤ-sum (5.5); real explosions (17.29)–(17.33) for every `φ`, as `→ ±∞`, unboundedness and failure of the transversality condition, with the book's calibrations as counterexamples (p. 421) |
| [TidyR5SchurCohn](KeynesianStickyPrices/TidyR5SchurCohn.lean) | 45 | Woodford App. C.1, Props. C.1–C.2: root location for real quadratics and cubics, Cases I, II, III′ (restated from the Woodford Chapter 4 project) |
| [TidyR5BlanchardKahn](KeynesianStickyPrices/TidyR5BlanchardKahn.lean) | 90 | Woodford App. C.1: `2 × 2` forward systems and the `3 × 3` Blanchard–Kahn theorem with one predetermined variable, `determinate3_iff` (restated from the Woodford Chapter 4 project) |
| [TidyR5ExpectationsMeasure](KeynesianStickyPrices/TidyR5ExpectationsMeasure.lean) | 71 | Conditional expectations on a probability space with a filtration (Mathlib `condExp`), a.e. axioms, news, forward solutions, bridges to the core (restated from the Chapter 22 project) |
| [TidyR5ExpectationsMeasureIID](KeynesianStickyPrices/TidyR5ExpectationsMeasureIID.lean) | 37 | The i.i.d. economy on `ℕ → ℝ` and the fair-coin economy (restated from the Chapter 22 project) |
| [TidyR5Recurrence](KeynesianStickyPrices/TidyR5Recurrence.lean) | 20 | p. 421, A1 (1.57): `y_{t+2} = Ay_{t+1} − By_t` for all real `A`, `B`: explosions to `±∞`, unboundedness, failure to tend to zero |
| [TidyR5RealExplosions](KeynesianStickyPrices/TidyR5RealExplosions.lean) | 33 | p. 421 with the output response of (18.1): real explosions, unboundedness and the real transversality condition for every `φ`, `φ_x`, under perfect foresight and every expectation system; the Fig. 17.8 calibration with `φ_x = 1/2`; the determinant condition no longer decides |
| [TidyR5ExplosionsMeasure](KeynesianStickyPrices/TidyR5ExplosionsMeasure.lean) | 12 | p. 421 on a probability space: the same characterisations with positive probability and for the mean |
| [TidyR5InvariantSplit](KeynesianStickyPrices/TidyR5InvariantSplit.lean) | 52 | Woodford App. C.1: eigenvalue counts and the stable invariant subspace (restated from the Woodford Chapter 4 project) |
| [TidyR5GeneralBKForward](KeynesianStickyPrices/TidyR5GeneralBKForward.lean) | 17 | Woodford App. C.1, fn. 1: forward systems over a finite index type (restated from the Woodford Chapter 4 project) |
| [TidyR5GeneralBK](KeynesianStickyPrices/TidyR5GeneralBK.lean) | 39 | Woodford App. C.1: the general Blanchard–Kahn theorem (restated from the Woodford Chapter 4 project) |
| [TidyR5GeneralBKPencil](KeynesianStickyPrices/TidyR5GeneralBKPencil.lean) | 7 | Woodford App. C.1: Blanchard–Kahn for systems in pencil form with `A₀` invertible (restated from the Woodford Chapter 4 project) |
| [TidyR5GeneralBKSingular](KeynesianStickyPrices/TidyR5GeneralBKSingular.lean) | 49 | Woodford App. C.1, fn. 2; King–Watson, Klein: Blanchard–Kahn for singular pencils (restated from the Woodford Chapter 4 project) |
| [TidyR5ThreeByThree](KeynesianStickyPrices/TidyR5ThreeByThree.lean) | 28 | Woodford Prop. 4.4 and App. C.3: the inertial rule `A44`, corrected (restated from the Woodford Chapter 4 project) |
| [TidyR5Inertia](KeynesianStickyPrices/TidyR5Inertia.lean) | 16 | (18.2), p. 427, with inertia: the `3 × 3` system, the characteristic polynomial, genericity, determinacy through Prop. C.2; backward-looking responses; inertia alone not determinate |
| [TidyR5InertiaForward](KeynesianStickyPrices/TidyR5InertiaForward.lean) | 11 | (18.2) with forward responses: `P(±1)`, (C.15), `\|A₂\|` in closed form and the closed-form determinacy condition |
| [TidyR5QuadRoots](KeynesianStickyPrices/TidyR5QuadRoots.lean) | 4 | A1 §1.9: one root inside the unit circle for a real polynomial of degree at most two iff `p(1)p(−1) < 0` |
| [TidyR5InertiaSingular](KeynesianStickyPrices/TidyR5InertiaSingular.lean) | 17 | (18.2) with `σφ_{x,1} = 1`: the pencil form for all parameters, `det(λM − N)`, determinacy iff `D₁D₋₁ < 0` and the response condition |
| [TidyR5StochasticPaths](KeynesianStickyPrices/TidyR5StochasticPaths.lean) | 17 | §17.4, Figs. 17.5–17.6 and p. 414 under any expectation system: expected paths and news as perfect-foresight equilibria, equilibria indexed by innovations, reverse-engineered disturbances |
| [TidyR5StochasticPathsMeasure](KeynesianStickyPrices/TidyR5StochasticPathsMeasure.lean) | 8 | §17.4, Figs. 17.5–17.6 on a probability space: expected paths and news a.s. |
| [TidyR5InnovEqmMeasure](KeynesianStickyPrices/TidyR5InnovEqmMeasure.lean) | 8 | Fig. 17.6 on a probability space: (17.18) and its factored form a.e.; existence and a.s. uniqueness of the equilibrium for every innovation process |
| [TidyR5PathwiseExplosion](KeynesianStickyPrices/TidyR5PathwiseExplosion.lean) | 17 | p. 421: on the i.i.d. coin space the expected real transversality condition holds for every deviation, yet realised `βᵗx̃_t` is unbounded a.s. for some deviation |
| [TidyR5ReverseMeasure](KeynesianStickyPrices/TidyR5ReverseMeasure.lean) | 6 | pp. 414, 420 on a probability space: uniqueness under a rule a.s., reverse-engineered disturbances |
| [TidyR5StochasticFiscal](KeynesianStickyPrices/TidyR5StochasticFiscal.lean) | 16 | Figs. 17.6–17.7, (17.19) under any expectation system: surplus news `ρ(1 − δ)/(λ₁ − ρ) − δ` correcting `FiscalUnderpinnings.deltaS`, AR(1) news, `Σs`, `u` news not geometric |
| [TidyR5StochasticFiscalMeasure](KeynesianStickyPrices/TidyR5StochasticFiscalMeasure.lean) | 15 | Figs. 17.6–17.7, (17.19) on a probability space: (17.19) a.s., surplus news, AR(1) news, `Σs` |
| [TidyR6HouseholdMeasure](KeynesianStickyPrices/TidyR6HouseholdMeasure.lean) | 35 | Ch. 2, (2.2)–(2.3), pp. 21–22: the household problem on a probability space, the Euler equation and the bond price (restated from the Chapter 2 project) |
| [TidyR6CalvoReset](KeynesianStickyPrices/TidyR6CalvoReset.lean) | 10 | p. 118, p. 421: the Calvo reset-price problem, its unique optimum, and the cohort price index |
| [TidyR6HouseholdMeasureTVC](KeynesianStickyPrices/TidyR6HouseholdMeasureTVC.lean) | 26 | Ch. 2, (2.6)–(2.7), p. 22; A1 p. 556: transversality, sufficiency and the valuation equation on a probability space (restated from the Chapter 2 project) |
| [TidyR6EulerIS](KeynesianStickyPrices/TidyR6EulerIS.lean) | 36 | (17.15)–(17.16), p. 118: the household Euler equation is the IS curve exactly, with the second-order disturbance `u_x = −σE_t[e^z − 1 − z]`; optimality iff IS; finite trees |
| [TidyR6PriceSetting](KeynesianStickyPrices/TidyR6PriceSetting.lean) | 29 | p. 118: the general price-setting problem; necessity of the first-order condition, sufficiency with concavity and transversality |
| [TidyR6Rotemberg](KeynesianStickyPrices/TidyR6Rotemberg.lean) | 15 | p. 118: the Rotemberg payoff, its failure of concavity, the concavity region, optimality in the region iff the first-order condition |
| [TidyR6RotembergPC](KeynesianStickyPrices/TidyR6RotembergPC.lean) | 23 | (17.17): the symmetric Rotemberg first-order condition is the nonlinear Phillips curve, exactly (17.17) with an explicit second-order remainder; finite trees |
| [TidyR6CalvoPC](KeynesianStickyPrices/TidyR6CalvoPC.lean) | 57 | (17.17) from Calvo price setting: weights, forecasts, log-linearised recursions, the exact identity, optimal resetting iff (17.17) with `κ = (1 − α)(1 − αβ)(γ + ϕ)/(α(1 + εϕ))` |
| [TidyR6CalvoBound](KeynesianStickyPrices/TidyR6CalvoBound.lean) | 18 | (17.17): the single bound `\|u_π\| ≤ calvoC·L²`; the index bounds the reset price |
| [TidyR6CalvoAE](KeynesianStickyPrices/TidyR6CalvoAE.lean) | 17 | (17.17): the Calvo Phillips curve under almost-sure bounds and index; an unbounded solution of the reset-gap equation |
| [TidyR6DerivedModel](KeynesianStickyPrices/TidyR6DerivedModel.lean) | 12 | (17.15)–(17.18) derived: equilibria are exactly the model with the remainders as disturbances; linearisation as the exact derivative; the steady state; finite trees |
| [TidyR6CalvoDerived](KeynesianStickyPrices/TidyR6CalvoDerived.lean) | 6 | (17.15)–(17.17) derived with Calvo price setting; the steady state |
| [TidyR6HouseholdPref](KeynesianStickyPrices/TidyR6HouseholdPref.lean) | 8 | p. 119: the household with preference weights; the Euler equation, the budget comparison against different taxes, sufficiency |
| [TidyR6JointYeoman](KeynesianStickyPrices/TidyR6JointYeoman.lean) | 15 | p. 118: the joint yeoman-farmer problem coincides with the decentralised problems (prices in the concavity region) |
| [TidyR6RotembergGlobal](KeynesianStickyPrices/TidyR6RotembergGlobal.lean) | 12 | p. 118: the Rotemberg first-order condition is not globally sufficient (a deep deflation) |
| [TidyR6RotembergLocal](KeynesianStickyPrices/TidyR6RotembergLocal.lean) | 26 | p. 118: near the steady state the Rotemberg first-order condition is sufficient among all plans |
| [TidyR6JointGlobal](KeynesianStickyPrices/TidyR6JointGlobal.lean) | 3 | p. 118: decentralised ⇒ joint over all uniformly bounded plans; joint ⇔ decentralised near the steady state |
| [TidyR6ShockPC](KeynesianStickyPrices/TidyR6ShockPC.lean) | 12 | (17.17), p. 119: the Rotemberg Phillips curve with a cost-push shift |
| [TidyR6ShockModel](KeynesianStickyPrices/TidyR6ShockModel.lean) | 15 | (17.15)–(17.17), pp. 119, 407: preference and markup shocks, `u_x = −σu_r + rem`, `u_π = κ̃(μ − ζ) + rem` |
| [TidyR6Genericity182](KeynesianStickyPrices/TidyR6Genericity182.lean) | 19 | (18.2), p. 427, with (5.6): genericity iff `R ≠ 0 ∨ B(A + B) < 0`, determinacy as polynomial (in)equalities in the eight parameters; the failure set nonempty, a strict subset of `R = 0`, Lebesgue-null |
| [TidyR6ZExpectations](KeynesianStickyPrices/TidyR6ZExpectations.lean) | 45 | Ch. 2, pp. 29–30, §17.2, p. 400: ℤ-indexed expectations, abstract and on a probability space with a ℤ-indexed filtration; restriction to the ℕ systems, news, the remote past, forward sums on ℤ |
| [TidyR6ZStaticIS](KeynesianStickyPrices/TidyR6ZStaticIS.lean) | 25 | (17.7)–(17.8), (17.14), pp. 399–405, on ℤ under uncertainty: equilibria indexed by their expectational errors, the role of `t → −∞`, the corrected and printed inverses of (17.14) |
| [TidyR6ZFullModel](KeynesianStickyPrices/TidyR6ZFullModel.lean) | 31 | (17.15)–(17.18), Figs. 17.5–17.6, pp. 407–410, on ℤ under uncertainty: equilibria indexed by their innovations; `zPath` unique iff no news, a second equilibrium on the coin space |

## Modelling conventions

* **Expectations.** Random variables are `Ω → ℝ`, processes `ℕ → Ω → ℝ`, and every linear model
  equation holds as an equality of functions, for an arbitrary `ExpectationSystem`. A process is
  adapted when `E_tx_t = x_t` (`ExpectationSystem.Adapted`). Perfect foresight
  (`perfectForesight`) and every finite event tree
  (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) are instances; the coin-flip tree
  makes the any-sign result genuinely random (`PersistenceFreedom.any_sign_coin`). No chapter
  result needs the pull-out property.
* **Probability spaces.** The `…Measure` modules and `TidyR5PathwiseExplosion` pose the models
  on a probability space with a filtration and Mathlib's conditional expectation
  (`TidyR5ExpectationsMeasure.MeasExpectationSystem`): equations hold almost everywhere, variables
  are integrable, and boundedness is essential boundedness. The i.i.d. coin economy
  (`TidyR5ExpectationsMeasureIID`) has no finitely supported description. The household and
  price-setting problems behind (17.15)–(17.17) (the `TidyR6…` modules) are posed there too, with
  information that may grow forever, and transferred to finite event trees, where they give
  `FullModel.Model` in every state.
* **Timing.** Dates are natural numbers. In the adaptive model `π_{−1}` is an initial value
  (`StaticIS.lagged`); in Figure 17.7 the book's dates `1, 2, …` are `n = 0, 1, …`. The
  perfect-foresight full model works with sequences `ℕ → ℝ` (`FullModel.PFEqm`,
  `FullModel.Second`), linked to the general model by `FullModel.pf_model_iff`; an infinite past
  is a ℤ-indexed sequence (`FullModel.SecondZ`, `StaticIS.eq_17_8`,
  `PersistenceFreedom.corrected_inverse`) or, under uncertainty, a ℤ-indexed filtration
  (`TidyR6ZExpectations.ZMeasExpectationSystem`), whose restriction to the dates `t ≥ s` is the
  ℕ-indexed system (`TidyR6ZExpectations.ZMeasExpectationSystem.restrict`).
* **Expectational errors and innovations.** The simple model's error `δ_{t+1} = π_{t+1} −
  E_tπ_{t+1}` (`StaticIS.reErr`) is a process; the innovation `ΔE_{t+1}` of (17.19)
  (`FiscalUnderpinnings.innov`) is an operator. They agree on adapted processes
  (`Links.reErr_eq_innov`).
* **Stability and determinacy.** Adaptive stability is convergence to zero after any initial
  condition without further disturbances (`RulesAdaptiveRE.AdaptiveStable`). Determinacy of the
  simple model is existence and uniqueness of a bounded equilibrium for every bounded adapted
  disturbance (`RulesAdaptiveRE.REDeterminate`); determinacy of a deviation or structural system
  is that its only bounded adapted solution is zero (`TaylorDeterminacy.Determinate`,
  `TaylorDeterminacy.StructDeterminate`). The two agree at `β = 0`
  (`Links.determinate_beta_zero_iff_reDeterminate`).
* **Two chains and their links.** The simple model (`StaticIS` to `AdaptiveTaylor`) and the
  full model (`FullModel` to `History`) were formalised separately. Lemmas both needed are
  collected in `SharedTools`; objects kept twice on purpose are linked in `Links`: the
  three-equation model `AR1Responses.ThreeEq` and `FullModel.Model`
  (`Links.threeEq_iff_model`), the transition matrix `AR1Responses.transA` and
  `TaylorDeterminacy.Mmat` (`Links.Mmat_mul_transA`), and `AR1Responses.etaStar` and
  `FullModel.lam1` (`PersistenceFreedom.etaStar_eq_inv_lam1`).
* **Explicit hypotheses.** Hypotheses the book leaves implicit are stated in each theorem:
  `σκ > 0`; `1 + σκφ ≠ 0` for (17.9)–(17.10); `|η| ≤ 1` and a bounded disturbance for the AR(1)
  results; `0 < β < 1` for (1.58) and the Bullard–Mitra condition; `[Nonempty Ω]` for
  determinacy; the transversality condition and summability, or boundedness with `0 ≤ ρ < 1`,
  for (17.19).

## Relation to the Galí and Woodford projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects, so the project builds on its own. Nothing is imported from
the Galí or Woodford projects. For (18.2) with inertia, the Woodford Chapter 4 project's
Schur–Cohn, Blanchard–Kahn and singular-pencil modules, and the Proposition 4.4 part of its
`ThreeByThree`, are restated as `TidyR5SchurCohn`, `TidyR5BlanchardKahn`, `TidyR5InvariantSplit`,
`TidyR5GeneralBKForward`, `TidyR5GeneralBK`, `TidyR5GeneralBKPencil`, `TidyR5GeneralBKSingular`
and `TidyR5ThreeByThree`. With backward-looking responses the matrix of (18.2) is Woodford's
`A44` with the output response in his annualised units (`TidyR5Inertia.A182_noForward`), and the
condition is his Proposition 4.4 as corrected there (`TidyR5ThreeByThree.prop44`). The
measure-theoretic expectations are restated from the Chapter 22 project
(`ObservationalEquivalence`) as `TidyR5ExpectationsMeasure` and `TidyR5ExpectationsMeasureIID`.

The Taylor-rule determinacy pieces are adapted from the Galí Chapter 3 project
(`BasicNewKeynesianModel`). There, `TaylorRuleSystem.determinate_iff_BM` proves that the system
(27) is determinate iff the Bullard–Mitra condition `κ(φ_π − 1) + (1 − β)φ_y > 0` holds, for
`σ, κ > 0`, `0 < β < 1` and `φ_π, φ_y ≥ 0`. `TaylorDeterminacy.determinate_iff_BM` restates the
same condition for Cochrane's deviation system (17.29)–(17.32) with an output response `φ_x`,
under the same hypotheses; Cochrane's `σ` is the reciprocal of Galí's. It is proved here from the
general criterion `TaylorDeterminacy.determinate_iff_explicit`, not copied. The structural-system
criterion `TaylorDeterminacy.structDeterminate_iff` follows the same pattern as Galí's
`TaylorRuleSystem`, through the core results `ExpectationSystem.system_unique` and
`ExpectationSystem.system_not_unique`. `History.rule181_determinate_iff` is the same condition
for the rule (18.1).

The comparison shows what the nonnegativity hypotheses hide. Galí's statement, like the one
here, covers only `φ, φ_x ≥ 0`, where `φ > 1` is sufficient. Outside that quadrant this project
proves the oscillating branch (1.58) (`TaylorDeterminacy.determinate_iff_phi`), non-necessity with
`φ_x = 0` (`TaylorDeterminacy.not_necessary_negative`) and non-sufficiency with `φ_x < 0`
(`TaylorDeterminacy.not_sufficient`). Galí's MSV result (`TaylorRuleSystem.equilibrium_iff_msv`)
corresponds to `AR1Responses.msv_unique` for `φ > 1`, which `Links.msv_unique_of_determinate`
extends to the whole determinacy region.

Woodford's version of the condition is Proposition 4.3, restated in the Woodford Chapter 7
project (`GainsFromCommitment`) as `OptimalTaylor.taylor_determinate_iff`,
`φ_π + (1 − β)φ_x/(4κ) > 1`; the factor 4 comes from Woodford's annualised interest rate. It is
not linked formally here. Woodford's loss on p. 418 is Cochrane's statement of it
(`OptimalPolicy.woodfordLoss`), not a restated result.

## Relation to other Cochrane projects

* **Chapter 2 (`IntertemporalModel`).** The household problem on a probability space, with the
  Euler equation, the transversality condition and sufficiency, is restated from that project's
  `HouseholdMeasure` and `HouseholdMeasureTVC` (by way of the Chapter 16 project's copies) as
  `TidyR6HouseholdMeasure` and `TidyR6HouseholdMeasureTVC`, and used for the IS curve
  (`TidyR6EulerIS`) and the household with preference shocks (`TidyR6HouseholdPref`).
* **Chapter 5 (`StickyPriceFiscal`).** The roots `λ₁ > 1 > λ₂ > 0` of (5.6) and the bound
  `FullModel.bounded_of_rec` are restated from that project (`NKModel.lam1`, `NKModel.lam2`), with
  docstrings saying "restated from the Chapter 5 project". The two-sided moving average (5.5)
  is restated in perfect-foresight form (`FullModel.twoSided_eq`); the Chapter 5 project proves
  the stochastic version with a pre-sample term (`TwoSidedMA.eq_5_5`). Its result that sticky
  prices move inflation before an announced rise (`TwoSidedMA.anticipated_moves_before`) is
  sharpened here by the Figure 17.5 results (`FullModel.antPath_le_T`,
  `FullModel.rise_raises_inflation`).
* **Chapter 16 (`NewKeynesianSelection`).** The simplest new-Keynesian model of Chapter 16 is the
  `κ → ∞` limit of the simple sticky-price model: the coefficients of (17.11) tend to those of
  (16.4) (`RulesAdaptiveRE.tendsto_coeff_17_11`), and the AR(1) responses (17.12)–(17.13) and
  (1.60) tend to (16.9) and (16.11) (`AR1Responses.tendsto_17_12`, `AR1Responses.tendsto_17_13`,
  `AR1Responses.tendsto_1_60`), which that project proves as `SimplestModel.ar1_solution` and
  `SimplestModel.ar1_rate`. Its determinacy condition `|φ| > 1` (`SimplestModel.determinate_iff`)
  is the limit of the E7 region, since `−1 − 2/(σκ) → −1`; this limit is not stated as a separate
  theorem. That project leaves to this one the claim that in richer models `φ > 1` is neither
  necessary nor sufficient (Chapter 12 claim P8) and Friedman's adaptive-expectations spiral
  (P1): they are `TaylorDeterminacy.not_sufficient`, `TaylorDeterminacy.not_necessary_phix` and
  `AdaptiveTaylor.peg_spiral`.

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
