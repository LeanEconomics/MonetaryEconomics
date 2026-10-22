# Optimal policy rules in Lean

This is the `Woodford/OptimalPolicyRules/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Woodford (2003), *Interest and Prices*, Chapter 8, "Optimal Monetary
Policy Rules" (pp. 534–623), together with the proofs
in Appendix G (pp. 716–745). Model equations hold for an arbitrary expectation operator, so every
result covers perfect foresight and genuine uncertainty. Losses are genuine infinite discounted
sums over bounded plans. Every optimality claim is proved as optimality: a feasible plan satisfying
the first-order conditions minimises the expected loss over all bounded feasible plans (Lagrangian
sufficiency), with uniqueness from strict convexity. "Optimal from a timeless perspective" and
"robustly optimal" are given precise definitions and proved. "Unique equilibrium" means unique
among bounded adapted processes. The library contains **3003 theorems**, including the shared
core.

The general Giannoni–Woodford theory of §§1.4–1.5 (Propositions 8.1–8.4), which the book states
without proof, is proved in general, in corrected form where the printed statement fails (see
[Propositions 8.1–8.4 in general](#propositions-8184-in-general)). All the concrete results
(§§2–4, Propositions 8.5–8.11, Appendix G.2–G.10) are proved in full, and the general theory is
specialised to the basic and inflation-inertia models.

Headline results, in the namespace `Woodford.OptimalPolicyRules`:
* **The general framework.** Lagrangian sufficiency for the general LQ problem (1.1)–(1.4) under
  any expectation system with pull-out, as an exact identity (`GeneralFOC.lagrangian_gap`,
  `GeneralFOC.lagrangian_sufficiency`); the timeless and robust optimality definitions
  (`GeneralSetup.LQProblem.TimelesslyOptimalPlan`, `GeneralSetup.RobustlyOptimal`); the root
  pairing of fn 8 and a counterexample to its "exactly half" (`GeneralFOC.Pencil.pencil_det_pairing`,
  `GeneralFOC.Pencil.fn8_counterexample`), with the corrected count `2L + C = 2n`, so exactly half
  iff no root lies on `|ν| = β^{−1/2}` (`TidyR5aExactlyHalf.two_lower_add_circle`,
  `TidyR5aExactlyHalf.lower_eq_half_iff`); necessity of the first-order conditions, which the book
  asserts without proof, state by state with faithful expectations and in conditional mean square
  without them, faithfulness being needed for the pointwise form (`TidyR5bFOCNecessity.foc_necessary`,
  `TidyR5bFOCMeanSq.foc_necessary_meanSq`, `TidyR5bFaithNeeded.faithful_needed`), hence (1.10)–(1.12)
  exactly (`TidyR5bFOCNecessity.restated_iff_affine`); the exogenous-instrument determinacy claim of
  p. 546 for every `Ẽ`, with genericity and no unit-circle root, counting finite roots only
  (`TidyR5aExoSingular.Sys.exoDeterminate_iff_count`,
  `TidyR5aExoSingular.Sys.not_exoDeterminate_of_pencil_zero`); the target criterion (1.23)
  through the adjugate, with the corrected degree of `α(L)` (`TargetCriterion.Crit.eq123_adjugate`,
  `Adjugate.natDegree_alpha_le_rank`, `Adjugate.nilpotent_counterexample`); Proposition 8.2
  conditional on Proposition 8.1 (`TargetCriterion.Prop82.prop82_optimal`,
  `TargetCriterion.Prop82.prop82_unique`); the lemma behind (1.30) ⇔ (1.31) for polynomials of any
  degree with complex roots (`TargetCriterion.eq130_iff_eq131`).
* **Optimal inflation targeting rules.** The criterion (2.5) is robustly optimal, and so is (2.9)
  for every `0 ≤ γ ≤ 1` and every (2.10) (`InflTargetInertia.baseline_robustlyOptimal`,
  `InflTargetInertia.indexation_robustlyOptimal`, `InflTargetInertia.rule210_robustlyOptimal`);
  the flexible-wage limit (2.14) as a genuine limit of equilibria
  (`InflTargetStickyWages.flexible_wage_family`); the corrected (2.20) derived and sufficient, and
  determinate exactly when every root of a cubic lies outside an ellipse, which fails for some
  admissible parameters (`InflTargetStickyWages.foc_imp_criterion`,
  `InflTargetStickyWages.criterion_determinacy_iff_stableRoots`,
  `InflTargetStickyWages.P1_criterion_not_determinate`), the exact region holding under every
  expectation system and on every filtered probability space
  (`TidyR5bStickyBoundary.determinacy_iff_stableRoots_any`, `TidyR5bStickyExists.exists_meas_iff_stableRoots`); the criterion (2.5) necessary for timeless
  optimality under uncertainty (`TidyR5bInertiaNecessity.timeless_iff_criterion`,
  `TidyR5bInertiaNecessity.timeless_criterion_meanSq`); (2.22) robustly optimal for `κ_w = κ_p`
  (`InflTargetStickyWages.sym_robustlyOptimal`); (2.27) robustly optimal for every `0 ≤ δ < 1`
  (`InflTargetHabit.habit_robustlyOptimal`); (2.32) and (2.34) with predetermined decisions
  (`InflTargetPredetermined.eq232_optimal_rule`, `InflTargetPredetermined.eq234_of_optimal`); the
  Giannoni–Woodford weights and `δ` (`GWModel.deltaGW_unique`, `GWModel.deltaGW_table`).
* **Optimal interest-rate rules.** Proposition 8.5 holds for every admissible parameter vector:
  the model's characteristic polynomial never has a root in `1 ≤ |μ| ≤ β⁻¹`, so the rule is always
  determinate and the book's hypothesis is redundant (`IRuleBasic.rule_determinate`,
  `IRuleBasic.pG_ne_zero_of_annulus`, `IRuleBasic.bounded_optimum_exists`, `IRuleBasic.prop_8_5`);
  the rule equilibrium is the unique optimum (`IRuleBasic.rule_eqm_unique_optimum`);
  Proposition 8.6 and the target criterion (3.13) (`IRuleForwardIntegrated.prop_8_6`,
  `IRuleForwardIntegrated.rule_iff_crit313`); Proposition 8.7 (`CubicRoots.prop_8_7`); the
  rule system of p. 593 has at most one bounded solution for every admissible parameter vector,
  by strict convexity rather than a root count (`InflationInertiaRules.rule_system_unique`,
  `InflationInertiaRules.rule_system_determinate`), and for every `0 ≤ γ ≤ 1` exactly one for
  every bounded disturbance and history, built from the bounded optimal plan
  (`TidyRuleSystem.rule_system_existsUnique`, `TidyRuleSystem.rule_system_exists_iff`), also at
  `λₓ = 0` (`TidyR5aLambdaXZero.rule_system_existsUnique_nonneg`); the equilibrium paths converge to
  the Chapter 7 paths as `λ_i → 0`, uniformly over dates and states (p. 591;
  `TidyR5aLambdaILimit.paths_converge`, `TidyR5aLambdaILimitMeasure.paths_convergeM`); Rule III is
  robustly optimal at the full stochastic level (`TidyR5aRuleIIIStochastic.Inertia.ruleIII_prop82_B`,
  `TidyR5aRuleIIIMeasure.AllCases.m_prop82_III_all`);
  Propositions 8.8–8.11, unconditional
  (`InflationInertiaRules.prop_8_8_ruleIII`, `Links.prop_8_9_ruleIII_standing`,
  `Links.prop_8_10_standing`, `Links.prop_8_11_standing`), with their limits as `γ → 0` and
  `γ → 1` along the actual roots (`Links.prop_8_9_ruleI_limit_standing`,
  `Links.prop_8_11_limit_one_standing`); the delayed-information versions (3.29)–(3.31)
  (`Links.eq316_delay_iff_target331`); the reaction function (4.1) implements the optimal policy
  (`Reflections.rule41_timelesslyOptimal`).
* **The generalised Taylor principle (p. 585; Ch. 4, (2.9) and fn 27).** For a general rule with
  any number of lags the principle `φπ(1) + (1 − β)φₓ(1)/(4κ) > 1 − ρ(1)` holds iff the symbol of
  the system at `μ = 1` has positive determinant, `det = κσ · gap`, and its boundary is exactly
  where the system has the eigenvalue 1 (`Tidy.TaylorPrinciple.det_symOne`,
  `Tidy.TaylorPrinciple.unit_root_iff`, `Tidy.TaylorPrinciple.shift_solves_iff`). For rules of the
  form (3.7) it reduces to `φπ + ρ₁ > 1` (`Tidy.TaylorPrinciple.gtp37_iff`); the optimal rule
  satisfies it at every admissible calibration, with slack `κσ/λᵢ + κσ/β`, and its cumulative
  response to a permanent rise in inflation tends to `+∞` (`Tidy.TaylorPrinciple.rule37_gtp`,
  `Tidy.TaylorPrinciple.rule37_gtp_determinate`, `Tidy.TaylorPrinciple.rule37_step_tendsto`).
* **The parity remark of p. 727, exact.** `Δ(γ) = −β⁴` times the discriminant of the cubic, and
  `Δ` has exactly one root in `(0, 1)`, a simple one, with `Δ < 0` below it and `Δ > 0` above it
  up to 1: the book's "one or three roots" never has three (`Tidy.Parity.deltaQuartic_eq_disc`,
  `Tidy.Parity.delta_unique_root`, `Tidy.Parity.deltaPoly_roots_Ioo`).
* **Numbers.** `γ̄ ∈ (.3533, .3534)` (`CubicRoots.calib_gamma_bar`); the Fig. 8.4 mean horizon in
  `(2.2, 2.25)` and the relative weight `∑|α_j|/α₀ ∈ (.386, .389)`, by interval arithmetic
  (`Links.fig_8_4_mean_horizon_standing`, `Links.fig_8_4_abs_weight_ratio_standing`); the
  p. 586 and pp. 590–591 coefficients (`IRuleBasic.p586_numbers`,
  `IRuleForwardIntegrated.p590_numbers`).
* **Genuine probability models.** The general problem (1.1)–(1.4) is restated on a probability
  space with a filtration, `E_t` Mathlib's conditional expectation and every equation holding
  almost surely. Lagrangian sufficiency holds as an exact identity and the optimal target path is
  a.s. unique (`OptimalRulesMeasure.m_lagrangian_gap`, `OptimalRulesMeasure.m_lagrangian_sufficiency`,
  `OptimalRulesMeasure.m_targets_eq_of_J_eq`). Proposition 8.2's linear form (1.5) is proved for a
  VAR(1) exogenous state, `E_t s_{t+1} = A s_t`: under the perfect-foresight Assumption 8.1, every
  bounded solution of (1.1) + (1.9) on every probability space has `z_t = f⁰ + f_Z Z̄_t + f_s s_t`
  a.s. with `Z̄_t = (Z_t, M_{t−1})`, the coefficients fixed before the probability space
  (`OptimalRulesMeasureMarkov.prop82_linear_form`), and also with the `Z̄_t` of (1.24)
  (`OptimalRulesMeasureMarkov.prop82_linear_form_124`); the target criterion (1.23) holds a.s.
  (`OptimalRulesMeasureMarkov.criterion_var`); and when the endogenous state transition `H_n` is
  stable the solution exists, is a.s. unique and is optimal from a timeless perspective
  (`OptimalRulesMeasureMarkov.m_existsUnique_var`, `OptimalRulesMeasureIID.iid_prop82`). The
  book's Assumption 8.1 holds iff the corrected bounded form holds and date-`t₀` information is
  a.s. bounded and a.s. predictable (`OptimalRulesMeasure.assumption81_iff`; for robust
  optimality `OptimalRulesMeasure.robustlyOptimal_iff`). So it fails on the infinite fair-coin
  economy at every `t₀ ≥ 1` and on Gaussian i.i.d. economies
  (`OptimalRulesMeasureIID.coin_not_assumption81`, `OptimalRulesMeasureIID.gauss_not_assumption81`),
  and holds as stated for a static problem on the coin economy at `t₀ = 0`
  (`OptimalRulesMeasureStatic.static_coin_assumption81`). On a finite, fully supported space every
  notion agrees with the core one, and the one-point space is perfect foresight
  (`OptimalRulesMeasure.Bridge.mAssumption81_iff`, `OptimalRulesMeasure.Bridge.unitSystem_pf`).
  For an arbitrary bounded adapted disturbance (no VAR): the conditional forecast path of any
  solution is a perfect-foresight solution (`OptimalRulesMeasureForecast.fc_focSystem`), so the
  uniqueness half of Assumption 8.1 follows from its perfect-foresight form
  (`OptimalRulesMeasureForecast.m_focUnique_of_pf`) and (1.23) holds a.s.
  (`OptimalRulesMeasureForecast.m_criterion`). Conversely, a bounded feasible plan satisfying (1.23)
  a.s. is the FOC solution, so commitment to (1.23) is determinate with no stability of `Λ`
  (`OptimalRulesMeasureConverse.m_criterion_iff`, `OptimalRulesMeasureConverse.m_prop82_unique_pf`).
  The perfect-foresight solution map has an absolutely summable kernel, by the closed graph theorem
  (`OptimalRulesMeasureKernel.kernel_summable`, `OptimalRulesMeasureKernel.kernel_hasSum`), and
  existence holds iff the forecast-driven state `X_{t+1} = h + HX_t + E_t∑_kK^N_kc_{t+k}` is
  essentially bounded (`OptimalRulesMeasureGeneral.m_exists_iff`), which geometric stability of `H`
  guarantees (`OptimalRulesMeasureGeneral.m_assumption81MB_of_powDecay`,
  `OptimalRulesMeasureGeneral.m_prop82_general`). The perfect-foresight Assumption 8.1 makes `H_n`
  power-bounded but not geometrically stable (`OptimalRulesMeasureStability.powBdd_Hn`,
  `OptimalRulesMeasureStability.ur_eigenvalue_one`), and it does not give existence for every
  disturbance: Example B fails on the fair-coin economy
  (`OptimalRulesMeasureCounterexample.pf_assumption81_not_sufficient`). The exact spectral relation
  is with the pencil of (1.1) + (1.9), not (1.15): `ν` is an eigenvalue of `H` iff `|ν| ≤ 1` and `ν`
  is a root of that pencil (`OptimalRulesMeasureSpectrum.eig_Hgen_iff`), so the root condition on
  the pencil gives the measure Assumption 8.1 for every disturbance
  (`OptimalRulesMeasureSpectrum.m_assumption81MB_of_noEulerRoot`). In the basic model and the
  inflation-inertia model `H_n` is geometrically stable
  (`OptimalRulesMeasureStabilityModels.NK.nk_powDecay`,
  `OptimalRulesMeasureStabilityModels.Inertia.in_powDecay`), and Proposition 8.2 holds on every
  filtered probability space for every bounded adapted disturbance with no hypothesis left
  (`OptimalRulesMeasureModelsProp82.NK.nk_m_prop82_general`; inertia model in the real case,
  `OptimalRulesMeasureModelsProp82.Inertia.in_m_prop82_general`). The whole theory is redone for
  a quasi-split (`Prop81CaseII.QuasiSplit`, case (ii) of Assumption 8.2, where no real deflating
  split exists): Proposition 8.2 holds for every bounded adapted disturbance and on every VAR
  economy (`OptimalRulesMeasureQuasiSplit.m_prop82_generalQ`,
  `OptimalRulesMeasureQuasiSplit.m_prop82_varQ`), the forward step through the a.s. vanishing of a
  bounded residual with `D_t = βH E_tD_{t+1}` (`OptimalRulesMeasureQuasiSplit.m_fwd_zero`), and the
  real-split theorems are recovered as a special case
  (`OptimalRulesMeasureQuasiSplit.m_prop82_general_of_quasi`). So the inflation-inertia model
  satisfies Proposition 8.2 on every filtered probability space in the complex case `discQ < 0`
  (`OptimalRulesMeasureInertiaComplex.in_m_prop82_complex_general`,
  `OptimalRulesMeasureInertiaComplex.in_m_prop82_complex_var`) and at every admissible calibration
  `0 < γ ≤ 1`, with no hypothesis left (`OptimalRulesMeasureInertiaComplex.in_m_prop82_all_general`,
  `OptimalRulesMeasureInertiaComplex.in_m_prop82_all_var`); Assumption 8.5 holds for the `Λ` of
  every quasi-split of the model (`OptimalRulesMeasureInertiaComplex.in_h85_quasi`). The
  spectral relation holds with multiplicities: the Euler pencil `det(νF − G)` factors as
  `det(νI − H) · R(ν)`, and the eigenvalues of `H`, with algebraic multiplicity, are exactly the
  roots of the pencil in the closed unit disc, the unit circle included
  (`OptimalRulesMeasureMultiplicity.eulerPoly_factor`,
  `OptimalRulesMeasureMultiplicity.roots_charpoly_eq`,
  `OptimalRulesMeasureMultiplicity.rootMultiplicity_charpoly`). The pencil pairs `ν` with
  `1/(βν)` with equal multiplicities (`OptimalRulesMeasureEulerPencil.rootMultiplicity_pairMap`,
  `OptimalRulesMeasureEulerPencil.card_lower_eq_upper`); the perfect-foresight Assumption 8.1
  makes it regular, puts exactly `n` roots in the closed disc (the Blanchard–Kahn count) and none
  in `1 < |ν| < β⁻¹` (`OptimalRulesMeasureMultiplicity.eulerPoly_ne_zero`,
  `OptimalRulesMeasureMultiplicity.card_closedDisk_eq`,
  `OptimalRulesMeasureMultiplicity.eulerRoot_gap`). The same involution maps the unselected roots
  of (1.15) to the eigenvalues of `Λ`, so the remark after Proposition 8.1 becomes an iff
  (`OptimalRulesMeasureMultiplicity.prop81_eig_pairMap`,
  `OptimalRulesMeasureMultiplicity.powDecay_Λ_iff_outside`). In Example B every horizon of news
  feeds the unit-root direction, `e'K^N_k ≠ 0`, while the total forcing sums to zero
  (`OptimalRulesMeasureKernelB.eB_KN`, `OptimalRulesMeasureKernelB.eB_eKN_ne_zero`,
  `OptimalRulesMeasureKernelB.eB_eKN_hasSum`).
* **Cross-links.** The formalisations of the same objects in different modules are proved to
  agree: the canonical roots of Proposition 8.7 satisfy the hypotheses of Propositions 8.9–8.11
  (`Links.inertiaRoots_of_standing`); the two Euler equations, `A(z)` and discriminants coincide
  (`Links.euler_iff_euler`, `Links.modelDisc_eq_deltaG`); at `γ = 0` Proposition 8.5's
  equilibrium is the unique solution of the p. 593 rule system (`Links.inertia_system_gamma_zero`);
  the model equations of the sections agree (`Links.asInd_iff`).

## Propositions 8.1–8.4 in general

Thirty-one modules (647 theorems, from `PencilSplit` to `InertiaProp82Complex` in the library
map) prove the general theory of §§1.4–1.5 and Appendix G.1–G.2, which the book takes from Giannoni and
Woodford (2002a) without proof.

* **Proposition 8.1 from Assumptions 8.2–8.4**, through a real deflating pair `A J = Î J Ψ` of the
  pencil (1.15) (App. G.1), for any expectation system. Three corrections:
  * *Multipliers known at their date.* The statement needs `M_t` known at `t` (as p. 540 says) and
    adapted plans (`Prop81General.Prop81ConclusionM`, `Prop81General.prop81`,
    `PencilAssumptions.prop81_of_assumptions`). Without this it is false under uncertainty
    (`Prop81General.not_prop81Equiv_coin`); under perfect foresight the original holds
    (`Prop81General.prop81_perfectForesight`).
  * *Repeated roots.* The distinct-root clause of Assumption 8.3 is replaced by selecting whole
    root classes, through generalised eigenspaces (`PencilRepeated.SelWhole`,
    `PencilRepeated.prop81_of_assumptions_general`). A selection may also take only part of a
    repeated root (`TidyR5bPartialSel.prop81_of_assumptions_partial`,
    `TidyR5bPartialSel.prop82_of_assumptions_partial`); `Υ` is then determined by the selection iff
    each partially selected root has a single Jordan chain (`TidyR5bCyclicSel.selSpace_conj_unique_iff`,
    `TidyR5bSelLink.Υ_unique_iff`; counterexample `TidyR5bPartialSel.partial_nonunique`).
  * *Case (ii) of Assumption 8.2* (one unpaired complex root). The book's Assumption 8.4(ii)
    depends on how the eigenvector is scaled (`Prop81Unique.re_det_rescale_zero`,
    `CaseIIInstance.book_condition_depends_on_scaling`). It is replaced by a normalisation-free
    condition (`CaseIIBasis.Assumption84II`, basis-invariant by `CaseIIBasis.basis_invariance`),
    under which Proposition 8.1 holds (`CaseIIBasis.prop81_caseII`). An explicit system shows the
    condition is not vacuous (`CaseIIInstance.ex82`, `CaseIIInstance.ex84`,
    `CaseIIInstance.ex_prop81`). Its existential form implies the every-basis form only when the
    zero root is semisimple (`TidyR5bCaseIIZeroChain.zc_semisimple_needed`). That example system
    satisfies Assumption 8.5 but not Assumption 8.1, and the conclusion of Proposition 8.2 fails
    for it, so Assumption 8.1 cannot be dropped (`TidyR5aCaseIIExample.ex_prop82_summary`).

  The uniqueness remark of p. 553 holds when no root lies on `|μ| = β⁻¹`
  (`Prop81Unique.remark_p553`); in general `Λ` and `Υ` are unique iff `Λ` is power-bounded, under
  every expectation system (`TidyR5bReRepUncertain.unique_iff_powBdd_any`), which fails for a
  Jordan block on the circle (`TidyR5bReRep.jordan_nonunique`); and `deg α = rank Λ = rank Ẽ` (E18) under the assumptions
  (`PencilAssumptions.natDegree_alpha_eq_rank`).
* **Proposition 8.2 without the stability hypothesis**, and with Assumption 8.1 corrected.
  * `TargetCriterion.Recursion.MultStable` fails whenever Assumption 8.7 holds
    (`PencilAssumptions.not_multStable_of_unselected`). Assumption 8.5 is what keeps the
    multipliers bounded (`Prop82General.KrylovBound.boundedV_of_krylov`).
  * The earlier formalisation of Assumption 8.1 cannot hold under uncertainty
    (`NKAssumption81.not_assumption81_coin`). The corrected one takes a bounded initial
    multiplier known at `t₀ − 1` (`Prop82General.Assumption81M`).
  * Proved: existence, uniqueness, optimality subject to (1.27), and the time-invariant multiplier
    rule (1.17) (`Prop82General.Prop82M.prop82M_determinate`,
    `Prop82General.Prop82M.prop82M_optimal`, `Prop82General.Prop82M.prop82M_multiplier_rule`);
    the `d = min(k, n_z − 1)` lags of (1.24) suffice (`MultiplierLags.rule_lags_lt`,
    `MultiplierLags.rule_lags_full`).
  * Robust optimality: `Prop82General.Prop82M.prop82M_robustlyOptimal`, and from the assumptions
    `PencilAssumptions.prop82_of_assumptions`, `PencilRepeated.prop82_of_assumptions_general`,
    `CaseIIBasis.prop82_caseII`.
* **Proposition 8.3 with the no-circle hypothesis.** For every representation of Proposition 8.1,
  `α(L)` has exactly `m` zeros inside the unit circle when no root of (1.15) has `|λ| = β⁻¹`
  (`Prop83.prop83`, `Prop83Links.prop83M`, `Prop83Links.prop83M_const`). Without that hypothesis
  only the bounds hold (`Prop83.prop83_bounds`), and the exact count fails
  (`Prop83.circle_counterexample`). Assumption 8.1 does not exclude roots on the circle
  (`Circle81.assumption81_not_exclude_circle`), and the exact count fails even for a problem
  satisfying the full Assumption 8.1 (`TidyR5bProp83Circle.prop83_fails_on_circle`).
* **Proposition 8.4, unconditional.**
  * The bounded forward inverse exists and is unique exactly when every root is outside the unit
    circle (`Prop84General.forward_inverse_existsUnique`, `Prop84General.forward_inverse_iff`).
  * The factorisation `α = α₁α₂` (`Prop84General.alpha_factorization`).
  * (1.28) ⇔ (1.32) (`Prop84General.prop84`, `Prop84General.prop84_criterion`,
    `Prop83Links.prop84M`). Every hypothesis of the earlier conditional theorem is discharged
    (`GeneralTheoryLinks.Old.prop84_conditional_discharged`).
* **Worked instance: the basic model (§3.1).**
  * Assumptions 8.1–8.5 hold (`NKAssumption81.NK.nk_assumption81M`,
    `GeneralTheoryLinks.NK.nk_assumption82`, `GeneralLinks.nk_assumption83`,
    `GeneralTheoryLinks.NK.nk_assumption84`, `GeneralTheoryLinks.NK.nk_assumption85`).
  * Propositions 8.1 and 8.3 are fully unconditional (`GeneralTheoryLinks.NK.nk_prop81_prop83`).
  * Proposition 8.2 needs only pull-out (`GeneralTheoryLinks.NK.nk_prop82`).
  * The general criterion is the rule (3.7) (`GeneralLinks.nk_crit_iff_rule`), and Propositions
    8.5 (superinertia) and 8.6 follow from the general theory (`GeneralLinks.nk_zerosInside`,
    `GeneralLinks.prop_8_6_from_general`).
* **Worked instance: the inflation-inertia model (§3.2).**
  * Propositions 8.1 and 8.3 hold at every admissible calibration
    (`GeneralTheoryLinks.Inertia.in_props_81_83_all`). This covers the complex case, through the
    corrected Assumption 8.4(ii) (`InertiaProp8182.in_assumption84II`,
    `InertiaProp8182.in_prop81_complex`), and the double root, where Assumption 8.3 fails
    (`GeneralTheoryLinks.Inertia.in_double_props_81_83`).
  * Rules I and II are exactly the general criterion (1.23) for the two deflating splits
    (`InertiaCriterion.crit_iff_ruleI`, `InertiaCriterion.crit_iff_ruleII`).
  * Rule III is not of the form (1.28) for any deflating split (`InertiaSplit.split_classify`,
    `InertiaSplit.split_not_ruleIII`), but it is the criterion of a full representation of the
    corrected Proposition 8.1 at every `0 < γ ≤ 1`, and robustly optimal
    (`TidyR5aRuleIIIStochastic.Inertia.ruleIII_prop81M`,
    `TidyR5aRuleIIIStochastic.Inertia.ruleIII_prop82_B`).
  * Assumption 8.1 holds at every admissible calibration, for any expectation system, in its
    bounded-initial-condition form (`InertiaAssumption81.Assumption81MB`,
    `InertiaAssumption81.in_assumption81MB`); `Prop82General.Assumption81M` holds on a finite
    sample space (`InertiaAssumption81.in_assumption81M_of_finite`), and the original Assumption
    8.1 under perfect foresight (`InertiaAssumption81.in_assumption81_perfectForesight`). With a
    predetermined variable the initial condition `Z_{t₀}` must be bounded: on an infinite sample
    space with unbounded `Z_{t₀}` the unbounded-condition forms fail
    (`InertiaAssumption81.not_in_assumption81M`). The proof goes through a copy of the general
    Blanchard–Kahn theorem with a random bounded predetermined initial vector
    (`GeneralBKCopy.determinate_of`) applied to the FOC system (`InertiaFOCSystem.solves_bk_iff`).
  * Proposition 8.2 holds at every admissible calibration, real and complex roots alike
    (`InertiaProp82Complex.in_prop82_all_B`, `InertiaProp82Complex.in_prop82_all_finite`). The
    real case is `InertiaAssumption81.in_prop82_real_B`; the complex case is
    `InertiaProp82Complex.in_prop82_complex_B`, through Assumption 8.5 for the `Λ` of the
    case-(ii) construction (`InertiaProp82Complex.in_assumption85_complex`). Robust optimality is
    in the bounded-initial-condition sense `InertiaAssumption81.RobustlyOptimalB`.
  * The bounded optimal plan that p. 593 assumes exists, at every calibration
    (`InertiaAssumption81.in_focSolvableMB`): the degree-6 characteristic polynomial of the FOC
    system has no root in `1 ≤ |μ| ≤ β⁻¹` (`InertiaFOCRoots.charD_ne_zero_of_annulus`) and exactly
    three inside the unit circle (`InertiaFOCRoots.charD_inside_three`).
  * At `γ = 0` the leading matrix of the FOC system is singular, so the results above take
    `0 < γ ≤ 1`; there the system reduces to the basic model's, and Assumption 8.1 and
    Proposition 8.2 hold at every `0 ≤ γ ≤ 1` (`TidyR5aInertiaGammaZero.focSystem0_iff`,
    `TidyR5aInertiaGammaZero.in_assumption81MB_all`, `TidyR5aInertiaGammaZero.in_prop82_all_B'`),
    also on every filtered probability space (`TidyR5aInertiaGammaZeroMeasure.in0_m_prop82_general`).
  * Proposition 8.9's `ρ₁ > 1` and Proposition 8.10 follow from the general theory
    (`InertiaSplit.prop_8_9_rho1_from_general`, `InertiaProp810.prop_8_10_via_prop84`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections and results:
* the (2.6) misprint `βE_t[π_{t+1} − π_t]` for `βE_t[π_{t+1} − γπ_t]`, found independently in §2.1
  and §3.2; the wrong target criterion (2.20) (E14) and the cross-reference of p. 563 (E15); the
  typo in (2.32) (E16); (2.26) holding only for bounded processes (E17); the degree of `α(L)`
  (E18); the "exactly half" of fn 8 (E19), which is `2L + C = 2n` in general;
* the exogenous-instrument count of p. 546 needs genericity and no unit-circle root, and counts
  finite roots only (for singular `Ẽ` the roots at infinity are unstable, and a singular pencil is
  never determinate); the necessity of the first-order conditions (p. 541) needs faithful
  expectations state by state and holds in conditional mean square, so almost surely, without them;
* with `κ_w ≠ κ_p` the corrected (2.20) is determinate exactly when every root of
  `P(Z) = λ_xZ(Z + ξ)² + λ_w(κ_wZ + Δ)² + λ_p(κ_pZ + Δ)²` lies outside an explicit ellipse (exact
  region on every probability space); the admissible parameters P1 violate it, and then neither the
  optimal plan nor commitment to the criterion is determinate;
* Proposition 8.5 holds for all admissible parameters (E21), and the p. 593 determinacy claim
  holds for all parameters, uniqueness by strict convexity and existence from the bounded optimal
  plan;
* Δ(γ) has exactly one root in `(0, 1)`, a simple one, not "one or three" (p. 727); the
  eigenvector of Ch. 4 fn 27 has output-gap entry `(1 − β)/κ`; for (3.7) the generalised Taylor
  principle is exactly `φπ + ρ₁ > 1`, so "`φπ > 0` and `ρ₁ > 1`" is sufficient, not necessary
  (p. 585);
* the gaps in Appendix G.6 and Lemma G.2 (E20, E22) and the `γ → 1` limits of Propositions 8.9
  and 8.11, closed;
* the printed `φ_x = .15` of pp. 590–591 is `.164` (S2), and `φ_x = .33` of p. 586 is `.3226`;
  `λ_x = .0026` of p. 574 is `.0027`;
* the Fig. 8.4 ratio `.39` confirmed by the enclosure `(.386, .389)`;
* in the general theory: Proposition 8.3 needs no root of (1.15) on `|λ| = β⁻¹`, even under the
  full Assumption 8.1; the remark of p. 553 holds iff `Λ` is power-bounded; Assumption 8.4(ii) is
  normalisation-dependent in case (ii) and is replaced, and the semisimplicity hypothesis of its
  ∃ ⇒ ∀ cannot be dropped; with a partial selection `Υ` is determined iff each partially selected
  root has one Jordan chain;
  Assumption 8.3 is sufficient but not necessary; the `MultStable` hypothesis is unnecessary.
  Assumption 8.1 with a predetermined variable needs a bounded initial condition `Z_{t₀}`
  (counterexample on an infinite sample space). On a genuine probability space the book's
  Assumption 8.1 holds exactly when the corrected form does and date-`t₀` information is a.s.
  bounded and a.s. predictable at `t₀ − 1`; the bounded optimal plan that p. 593 assumes
  exists at every calibration, by a root count for the degree-6 FOC polynomial, not the
  Proposition 8.7 cubic. The perfect-foresight Assumption 8.1 does not make `H_n` geometrically
  stable and does not give the measure Assumption 8.1 for every disturbance, and the eigenvalues
  of `H` are not the roots of (1.15) selected by the split; an earlier version of this README
  listed the first as unproved and the second as open (see [corrections](docs/corrections.md)).
  Separately, two hypothesis structures of the earlier formalisation (the original Proposition
  8.1 conclusion and Assumption 8.1) were found unsatisfiable under uncertainty and corrected;
  these are formalisation errors, not the book's.

Not formalised:
* in the general theory:
  * a formal instantiation of `GeneralBKCopy.determinate_of` for the stacked system (1.1) + (1.9):
    its leading matrix `F` is singular, so the system is not in Blanchard–Kahn form, and the link
    is through the root count `OptimalRulesMeasureMultiplicity.card_closedDisk_eq` only;
  * for partial selections, the per-root count data `TidyR5bSelLink.CountData` is a hypothesis of
    `TidyR5bSelLink.Υ_unique_iff`, not derived from a bare `PencilSplit.DeflatingSplit`; the "only
    if" direction needs `Ẽ` invertible and Assumption 8.4, and a deflating split that does not come
    from a `PencilEigen.RealSelection` is outside the theorem;
  * the exact criterion for the remark of p. 553 (`TidyR5bReRepUncertain.unique_iff_powBdd_any`)
    needs a nonempty sample space and one bounded solution of (1.18) (e.g. from Assumption 8.1),
    and is stated for the exact expectation systems only: no representation of Proposition 8.1 is
    formalised on the conditional-expectation model;
  * the counterexample to Proposition 8.3 under the full Assumption 8.1 is under perfect foresight
    (which suffices to refute the claim);
  * Rule III on a probability space (`TidyR5aRuleIIIMeasure.AllCases.m_prop82_III_all`) is proved
    for general disturbances; the VAR / timeless-optimality packaging is not;
* necessity of the first-order conditions on a probability space: the almost-sure form
  (`TidyR5bFaithNeeded.foc_ae_of_version`) assumes that the exact operators are versions of
  Mathlib's conditional expectation and that the squared residuals are integrable; the general LQ
  problem is not restated on the `OptimalRulesMeasure` framework;
* for the p. 593 rule system on a probability space, existence for `λₓ > 0` (uniqueness is proved
  for every `λₓ ≥ 0`, existence at `λₓ = 0`);
* for `λ_i → 0` on a probability space, the existence of the rule equilibria and of the (2.5)
  solution, which `TidyR5aLambdaILimitMeasure.paths_convergeM` takes as given;
* for the (2.20) region on a probability space (`TidyR5bStickyExists.exists_meas_iff_stableRoots`),
  general bounded `𝓕₀`-measurable initial values (the theorems take `w_{t₀−1} = 0` and constant
  initial multipliers), and a.s. uniqueness of the solution (only existence is ported);
* the derivation of the Giannoni–Woodford criteria (2.41)–(2.45) and their coefficients
  (`φ_w = .565`, `θ* = .580`, …), which need the unprinted structural model; (2.40) is proved under
  the explicit hypothesis that the constraints involve `i` only through forecasts a quarter
  earlier, verified for the IS block;
* necessity of the generalised Taylor principle for determinacy within the (3.7) family, which
  the book does not claim (fn 27): what is proved is that its boundary is exactly where an
  eigenvalue equals 1; pre-sample values in §3.1 are numbers, not random variables;
* Kalman filtering and Svensson–Woodford certainty equivalence beyond (3.32)–(3.35);
* the plotted curves of Figures 8.1–8.6, beyond the specific numbers listed above; and §4 apart
  from (4.1).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](OptimalPolicyRules/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated from the earlier projects) |
| [Expectations](OptimalPolicyRules/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; bounded adapted processes; forward series; the pull-out property |
| [ExpectationsFiniteTree](OptimalPolicyRules/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; coin-flip examples |
| [ForwardSolution](OptimalPolicyRules/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` (restated from the Chapter 2 and 3 projects); sunspot families; summation by parts |
| [QuadraticRoots](OptimalPolicyRules/QuadraticRoots.lean) | 15 | The roots of `βλ² − (1 + β + c)λ + 1` (restated from the Chapter 3 project) |
| [ExpectationTools](OptimalPolicyRules/ExpectationTools.lean) | 32 | Faithful expectations; complexified expectations; the complex forward inverse |
| [GeneralSetup](OptimalPolicyRules/GeneralSetup.lean) | 14 | §§1.1–1.3: the LQ problem (1.1)–(1.4), timeless and robust optimality, rules (1.13)–(1.14), the Sargent–Wallace property |
| [GeneralFOC](OptimalPolicyRules/GeneralFOC.lean) | 48 | §§1.1, 1.4: the Lagrangian (1.7)–(1.9), Lagrangian sufficiency, Assumption 8.1, (1.10)–(1.12), fn 8, the p. 552 selection, (1.18)–(1.19) |
| [Adjugate](OptimalPolicyRules/Adjugate.lean) | 23 | §1.4: (1.22), fn 16, the corrected degrees of `α(L)` and `B(L)` |
| [TargetCriterion](OptimalPolicyRules/TargetCriterion.lean) | 53 | §§1.4–1.5, App. G.2: (1.23), Props 8.1–8.4 conditional, Assumptions 8.5–8.6, (1.28)–(1.31), p. 558 |
| [InflTargetInertia](OptimalPolicyRules/InflTargetInertia.lean) | 67 | §2.1: (2.1)–(2.10), the workhorse, robust optimality of (2.5), (2.9), (2.10) |
| [InflTargetStickyWages](OptimalPolicyRules/InflTargetStickyWages.lean) | 117 | §2.2: (2.11)–(2.22), the flexible-wage limit, the corrected (2.20) and its exact determinacy region |
| [InflTargetHabit](OptimalPolicyRules/InflTargetHabit.lean) | 20 | §2.3: (2.23)–(2.27) |
| [InflTargetPredetermined](OptimalPolicyRules/InflTargetPredetermined.lean) | 54 | §2.4: (2.28)–(2.34) |
| [GWModel](OptimalPolicyRules/GWModel.lean) | 35 | §2.5: (2.35)–(2.45) and the p. 574 numbers |
| [Reflections](OptimalPolicyRules/Reflections.lean) | 6 | §4.1: the reaction function (4.1) |
| [CubicRoots](OptimalPolicyRules/CubicRoots.lean) | 111 | §3.2, App. G.3, G.6: `A(z)`, Proposition 8.7, Lemmas G.1–G.2, the discriminant, `γ̄` |
| [InflationInertiaRules](OptimalPolicyRules/InflationInertiaRules.lean) | 98 | §3.2, App. G.7: (3.14)–(3.24), Proposition 8.8, the determinacy of p. 593 |
| [IRuleBasic](OptimalPolicyRules/IRuleBasic.lean) | 122 | §3.1, App. G.4: (3.1)–(3.9), Proposition 8.5, fn 35, the p. 586 numbers |
| [IRuleForwardIntegrated](OptimalPolicyRules/IRuleForwardIntegrated.lean) | 38 | §3.1, App. G.5: (3.10)–(3.13), Proposition 8.6, the pp. 590–591 numbers |
| [IRulePredetermined](OptimalPolicyRules/IRulePredetermined.lean) | 11 | §3.3: (3.28)–(3.31) |
| [ImperfectInfo](OptimalPolicyRules/ImperfectInfo.lean) | 9 | §3.4: (3.32)–(3.35) |
| [InflationInertiaRepresentations](OptimalPolicyRules/InflationInertiaRepresentations.lean) | 140 | §3.2, App. G.8–G.10: Propositions 8.9–8.11, Lemma G.2, Figures 8.3–8.5 |
| [Links](OptimalPolicyRules/Links.lean) | 59 | Proofs that the different formalisations of the same book objects agree |
| [PencilSplit](OptimalPolicyRules/PencilSplit.lean) | 27 | App. G.1: vector forward solutions (Gelfand decay), the deflating pair `A J = Î J Ψ` (`DeflatingSplit`), the matrices `Λ`, `Υ`, `K` of (1.20)–(1.21) |
| [Prop81General](OptimalPolicyRules/Prop81General.lean) | 17 | Prop 8.1 from any deflating split, corrected so multipliers are known at their date (`Prop81ConclusionM`); the original fails under uncertainty (coin-flip counterexample); rank `Λ` = rank `Ẽ` |
| [Prop82General](OptimalPolicyRules/Prop82General.lean) | 18 | Prop 8.2 without `MultStable`: Assumption 8.5 bounds the multipliers; the multiplier rule (1.17); robust optimality; the corrected Assumption 8.1 (`Assumption81M`) |
| [PencilEigen](OptimalPolicyRules/PencilEigen.lean) | 31 | Assumptions 8.2 and 8.3 as stated; a real deflating pair from eigenvectors, (G.1)–(G.4); the kernel clauses of Assumption 8.3 always hold |
| [PencilAssumptions](OptimalPolicyRules/PencilAssumptions.lean) | 24 | Assumptions 8.4–8.5, (G.6)–(G.7); Props 8.1 and 8.2 from Assumptions 8.1–8.5; `deg α = rank Λ = rank Ẽ` (E18); `MultStable` fails under Assumption 8.7 |
| [Prop81Unique](OptimalPolicyRules/Prop81Unique.lean) | 17 | The remark of p. 553 (unique `Λ`, `Υ`, `Q`, `R` and multipliers) with no root on the circle, and its counterexample; no real split carries an unpaired complex root |
| [PencilRepeated](OptimalPolicyRules/PencilRepeated.lean) | 33 | Prop 8.1 and 8.2 with repeated roots: generalised eigenspaces of the shifted pencil and real descent, for selections of whole root classes |
| [Prop81CaseII](OptimalPolicyRules/Prop81CaseII.lean) | 14 | Props 8.1 and 8.2 in case (ii) of Assumption 8.2 (`QuasiSplit`, residual root `h`), under the basis-universal Assumption 8.4(ii) |
| [MultiplierLags](OptimalPolicyRules/MultiplierLags.lean) | 6 | (1.24): `d = min(k, n_z − 1)` lags of `q` suffice for the multiplier rule; the role of the first part of Assumption 8.5 |
| [CaseIIBasis](OptimalPolicyRules/CaseIIBasis.lean) | 19 | The corrected Assumption 8.4(ii) is basis-invariant; the existential form, ∃ ⇔ ∀ when the zero root is semisimple; Props 8.1 and 8.2 in case (ii) |
| [CaseIIInstance](OptimalPolicyRules/CaseIIInstance.lean) | 20 | Case (ii) with `n_Z = 1`: the residual root as a function of the eigenvector's scaling, the book's normalisation, and a system satisfying Assumptions 8.2(ii) and 8.4(ii) |
| [Prop83](OptimalPolicyRules/Prop83.lean) | 56 | Prop 8.3 for every representation, with no root on `\|λ\| = β⁻¹`; the bounds without it; the Jordan-block counterexample; nonempty sample space needed |
| [Prop84General](OptimalPolicyRules/Prop84General.lean) | 21 | Prop 8.4 unconditional: the bounded forward inverse (exact root condition), the factorisation `α = α₁α₂`, (1.28) ⇔ (1.32) from any date |
| [GeneralLinks](OptimalPolicyRules/GeneralLinks.lean) | 31 | The basic model (§3.1) as a general problem: (1.1), (1.9), `Λ`, `α`, the criterion is the rule (3.7); Props 8.5 and 8.6 from the general theory |
| [GeneralLinksInertia](OptimalPolicyRules/GeneralLinksInertia.lean) | 11 | The inflation-inertia model (§3.2) as a general problem: (1.1), (1.9); Prop 8.10 from the (1.30) ⇔ (1.31) lemma |
| [Prop83Links](OptimalPolicyRules/Prop83Links.lean) | 7 | Props 8.3 and 8.4 for the corrected representation of Prop 8.1; Prop 8.3 without Assumption 8.1 |
| [Circle81](OptimalPolicyRules/Circle81.lean) | 5 | Assumption 8.1 does not exclude roots of (1.15) on `\|μ\| = β⁻¹` |
| [InertiaSplit](OptimalPolicyRules/InertiaSplit.lean) | 54 | The inflation-inertia model: its pencil, every deflating split classified, Prop 8.3 for every representation, Rule III not a split's rule, Prop 8.9's `ρ₁ > 1` |
| [InertiaProp810](OptimalPolicyRules/InertiaProp810.lean) | 5 | Prop 8.10 from the general Prop 8.4 (real case) |
| [InertiaCriterion](OptimalPolicyRules/InertiaCriterion.lean) | 13 | The general criterion (1.23) of the inflation-inertia model is Rule I or Rule II |
| [InertiaRuleIII](OptimalPolicyRules/InertiaRuleIII.lean) | 5 | `Λ` is not pinned down by the homogeneous content of Prop 8.1; Rule III is compatible with it |
| [NKAssumption81](OptimalPolicyRules/NKAssumption81.lean) | 23 | Assumption 8.1 for the basic model (corrected form, any expectation system); the original formalisation fails under uncertainty |
| [InertiaProp8182](OptimalPolicyRules/InertiaProp8182.lean) | 13 | The inflation-inertia model: Assumption 8.5, Prop 8.2 in the real case, Assumptions 8.2(ii) and 8.4(ii) and Prop 8.1 in the complex case |
| [GeneralTheoryLinks](OptimalPolicyRules/GeneralTheoryLinks.lean) | 29 | Links: the bounded-orbit subspace; Props 8.1–8.3 at the double root and at every calibration of the inflation-inertia model; Assumptions 8.2–8.5 and Props 8.1–8.3 for the basic model; old vs corrected structures |
| [BKInvariantSplit](OptimalPolicyRules/BKInvariantSplit.lean) | 52 | The bounded-orbit invariant subspace and its graph form (restated from the Chapter 4 project) |
| [BKForward](OptimalPolicyRules/BKForward.lean) | 17 | The vector forward solution under an expectation system (restated from the Chapter 4 project) |
| [GeneralBKCopy](OptimalPolicyRules/GeneralBKCopy.lean) | 21 | Blanchard–Kahn sufficiency (App. C.1) for any expectation system, with a random bounded predetermined initial vector known at date 0 |
| [InertiaFOCRoots](OptimalPolicyRules/InertiaFOCRoots.lean) | 10 | The degree-6 FOC polynomial of the inflation-inertia model: no root in `1 ≤ \|μ\| ≤ β⁻¹`, exactly three inside the unit circle |
| [InertiaFOCSystem](OptimalPolicyRules/InertiaFOCSystem.lean) | 19 | The inflation-inertia FOC system (1.1) + (1.9) as a Blanchard–Kahn system: regular pencil, roots, and the equivalence of solutions |
| [InertiaAssumption81](OptimalPolicyRules/InertiaAssumption81.lean) | 22 | Assumption 8.1 for the inflation-inertia model at every calibration (bounded initial conditions; finite `Ω`; perfect foresight), the unbounded counterexample, Prop 8.2 in the real case |
| [InertiaProp82Complex](OptimalPolicyRules/InertiaProp82Complex.lean) | 7 | Assumption 8.5 for the case-(ii) `Λ`; Prop 8.2 for the inflation-inertia model in the complex case and at every calibration |
| [TidyRuleSystem](OptimalPolicyRules/TidyRuleSystem.lean) | 14 | p. 593: existence for the rule system (2.6), (3.1), (3.16) for every `0 ≤ γ ≤ 1` and every bounded history, from the bounded optimal plan; existence iff the history is bounded and known; exactly one solution |
| [Tidy](OptimalPolicyRules/Tidy.lean) | 36 | p. 585 with Ch. 4 (2.9) and fn 27: the generalised Taylor principle for general rules, its boundary as the unit eigenvalue, (3.7) satisfies it; App. G.6 p. 727: `Δ(γ)` has exactly one root in `(0, 1)`, simple |
| [ExpectationsMeasure](OptimalPolicyRules/ExpectationsMeasure.lean) | 71 | Measure-theoretic expectations (shared core, copied from `ObservationalEquivalence`): `MeasExpectationSystem` with Mathlib's `condExp`, the axioms a.e., news, the forward equation and sunspots, AR(1) conditional variance, bridges to and from the core `ExpectationSystem` |
| [ExpectationsMeasureIID](OptimalPolicyRules/ExpectationsMeasureIID.lean) | 37 | The genuine i.i.d. economy on `ℕ → ℝ` under `ν^ℕ` (shared core): independence, moments, every history null, determinacy iff `\|a\| < 1`, AR(1), the `±1` coin |
| [OptimalRulesMeasure](OptimalPolicyRules/OptimalRulesMeasure.lean) | 47 | §§1.1–1.4 on a probability space: (1.1), (1.2), (1.9), Lagrangian sufficiency a.s., Assumption 8.1 in the book's and the corrected forms, robust optimality; the book's form ⇔ the bounded form + `BddInfo` + `PredInfo`; bridges to the core on a finite space and to perfect foresight on one point |
| [OptimalRulesMeasureMarkov](OptimalPolicyRules/OptimalRulesMeasureMarkov.lean) | 55 | Prop 8.2 on VAR economies: the perfect-foresight solution map and its time-invariant coefficient matrices; conditional forecasts of any solution; the linear form (1.5) and with (1.24); (1.19)–(1.20) and (1.23) a.s.; Assumption 8.1 (uniqueness; existence under stable `H_n`); timeless optimality |
| [OptimalRulesMeasureIID](OptimalPolicyRules/OptimalRulesMeasureIID.lean) | 19 | The i.i.d.-driven VAR and Prop 8.2 on it; the fair-coin economy (`BddInfo` holds, `PredInfo` fails) and the Gaussian economy (`BddInfo` fails): the book's Assumption 8.1 and robust optimality there |
| [OptimalRulesMeasureStatic](OptimalPolicyRules/OptimalRulesMeasureStatic.lean) | 14 | A static problem: the corrected Assumption 8.1 on every probability space; the book's form holds on the coin economy at `t₀ = 0` and fails at `t₀ ≥ 1`; `H_n = 0`, so the existence theorem applies |
| [OptimalRulesMeasureForecast](OptimalPolicyRules/OptimalRulesMeasureForecast.lean) | 11 | For any bounded adapted disturbance: forecast paths of solutions are perfect-foresight solutions; Assumption 8.1 (uniqueness) from perfect foresight; (1.19)–(1.20) and (1.23) a.s. |
| [OptimalRulesMeasureConverse](OptimalPolicyRules/OptimalRulesMeasureConverse.lean) | 29 | The converse of Prop 8.1 with conditional expectations: the forward recursion by the tower property, (1.23) a.s. ⟺ the FOC solution, determinacy under (1.23), Prop 8.2 on VAR economies; links to the core criterion |
| [OptimalRulesMeasureKernel](OptimalPolicyRules/OptimalRulesMeasureKernel.lean) | 29 | The perfect-foresight solution map: affine, time invariant, closed under limits; continuity by the closed graph theorem; the absolutely summable kernel |
| [OptimalRulesMeasureGeneral](OptimalPolicyRules/OptimalRulesMeasureGeneral.lean) | 25 | Assumption 8.1 for any bounded adapted disturbance: the forecast-driven state, the exact existence condition, stable `H` or the root condition; `H` power-bounded; Prop 8.2 for every disturbance |
| [OptimalRulesMeasureStability](OptimalPolicyRules/OptimalRulesMeasureStability.lean) | 20 | `H_n` = `H`, power-bounded; stable iff no unit-circle eigenvalue; the counterexample `urP` with eigenvalue 1 where measure Assumption 8.1 still holds |
| [OptimalRulesMeasureStabilityModels](OptimalPolicyRules/OptimalRulesMeasureStabilityModels.lean) | 11 | `H_n` geometrically stable in the basic and inflation-inertia models; Assumption 8.1 on every probability space for both |
| [OptimalRulesMeasureModelsProp82](OptimalPolicyRules/OptimalRulesMeasureModelsProp82.lean) | 9 | The empty deflating split; Assumption 8.5 and the split discharged; measure Prop 8.2 with no hypothesis left for the basic model and the inflation-inertia model (real case) |
| [OptimalRulesMeasureCounterexample](OptimalPolicyRules/OptimalRulesMeasureCounterexample.lean) | 36 | Example B: perfect-foresight Assumption 8.1 holds, `H` has eigenvalue 1 with a forced left eigen-direction, and on the fair-coin economy no bounded solution exists |
| [OptimalRulesMeasureSpectrum](OptimalPolicyRules/OptimalRulesMeasureSpectrum.lean) | 23 | The spectrum of `H` = roots of the Euler pencil of (1.1) + (1.9) in the closed unit disc; the root condition on the pencil; not the selected roots of (1.15) |
| [OptimalRulesMeasureQuasiSplit](OptimalPolicyRules/OptimalRulesMeasureQuasiSplit.lean) | 32 | Prop 8.2 from a quasi-split (case (ii)) with conditional expectations: (1.19)–(1.20) and (1.23) a.s., the converse by a.s. forward uniqueness, every disturbance and VAR economies; the real split as a special case; link to the core criterion |
| [OptimalRulesMeasureInertiaComplex](OptimalPolicyRules/OptimalRulesMeasureInertiaComplex.lean) | 12 | Assumption 8.5 for every quasi-split of the inflation-inertia model; measure Prop 8.2 in the complex case and at every calibration, with no hypothesis left; links to the core |
| [OptimalRulesMeasureEulerPencil](OptimalPolicyRules/OptimalRulesMeasureEulerPencil.lean) | 27 | The Euler pencil `det(νF − G)` of (1.1) + (1.9) as a polynomial; the symplectic pairing `ν ↔ 1/(βν)` with multiplicities; coefficient symmetry; equal halves at `β^{−1/2}`; at most `n` roots in the closed unit disc |
| [OptimalRulesMeasureMultiplicity](OptimalPolicyRules/OptimalRulesMeasureMultiplicity.lean) | 22 | The factorisation `det(νF − G) = det(νI − H) · R(ν)`; the eigenvalues of `H` with multiplicity are the closed-disc roots; regularity, the Blanchard–Kahn count and the spectral gap under Assumption 8.1; `Λ` stable iff every unselected root has `\|μ\| > β⁻¹` |
| [OptimalRulesMeasureKernelB](OptimalPolicyRules/OptimalRulesMeasureKernelB.lean) | 11 | Example B: the next-state kernel `K^N_k` at every lag; the forcing of the unit-root direction, nonzero at every lag with zero sum; the partner root `2 = β⁻¹` |
| [TidyR5aCaseIIExample](OptimalPolicyRules/TidyR5aCaseIIExample.lean) | 22 | `CaseIIInstance.exProblem`: Assumption 8.5 holds, both halves of Assumption 8.1 fail, and no direct rule is robustly optimal, so the conclusion of Prop 8.2 fails |
| [TidyR5aExactlyHalf](OptimalPolicyRules/TidyR5aExactlyHalf.lean) | 17 | fn 8 corrected: `2L + C = 2n` for a regular Euler pencil, exactly half iff no root on `\|ν\| = β^{−1/2}`; the counterexample as an `LQProblem`; regularity needed |
| [TidyR5aExogenousInstrument](OptimalPolicyRules/TidyR5aExogenousInstrument.lean) | 32 | p. 546 with `Ẽ` invertible: Blanchard–Kahn in both directions; determinacy iff exactly `n_Z` roots of (1.15) inside and genericity; Sargent–Wallace; the basic model |
| [TidyR5aExoSingular](OptimalPolicyRules/TidyR5aExoSingular.lean) | 69 | p. 546 for every `Ẽ`: a pencil decomposition into nilpotent and regular parts; finite roots counted, roots at infinity unstable; a singular pencil is never determinate |
| [TidyR5aInertiaGammaZero](OptimalPolicyRules/TidyR5aInertiaGammaZero.lean) | 20 | The inflation-inertia model at `γ = 0`: reduction to the basic model, Assumption 8.1 and Prop 8.2; both at every `0 ≤ γ ≤ 1` |
| [TidyR5aInertiaGammaZeroMeasure](OptimalPolicyRules/TidyR5aInertiaGammaZeroMeasure.lean) | 8 | `γ = 0` on a probability space: no Euler root on the unit circle, Assumption 8.1 and Prop 8.2 for every bounded adapted disturbance and on VAR economies |
| [TidyR5aLambdaILimit](OptimalPolicyRules/TidyR5aLambdaILimit.lean) | 13 | p. 591: the equilibrium paths under (3.7) converge to the (2.5) paths as `λ_i → 0`, uniformly over dates and states |
| [TidyR5aLambdaXZero](OptimalPolicyRules/TidyR5aLambdaXZero.lean) | 23 | p. 593 at `λₓ = 0`: the rule system in Blanchard–Kahn form, its root counts and genericity; existence, so determinacy for every `λₓ ≥ 0` |
| [TidyR5aMeasBK](OptimalPolicyRules/TidyR5aMeasBK.lean) | 10 | Blanchard–Kahn (App. C.1) with Mathlib's conditional expectation: existence and a.s. uniqueness |
| [TidyR5aLambdaXZeroMeasure](OptimalPolicyRules/TidyR5aLambdaXZeroMeasure.lean) | 15 | p. 593 on a probability space: a.s. uniqueness for every `λₓ ≥ 0` by forecast transfer; existence at `λₓ = 0` |
| [TidyR5aLambdaILimitMeasure](OptimalPolicyRules/TidyR5aLambdaILimitMeasure.lean) | 11 | p. 591 on a probability space: the paths converge a.s. at every date as `λ_i → 0` (equilibria given) |
| [TidyR5aRuleIIIStochastic](OptimalPolicyRules/TidyR5aRuleIIIStochastic.lean) | 15 | Rule III (3.24) at the full stochastic level: moving the unstable eigenvalue of `Λ`; a representation of Prop 8.1 with Rule III's `α(L)`; Prop 8.2 for it |
| [TidyR5aRuleIIIMeasure](OptimalPolicyRules/TidyR5aRuleIIIMeasure.lean) | 29 | Rule III on a probability space: the modification a.s.; the real case, any quasi-split, and every `0 < γ ≤ 1` |
| [TidyR5bCaseIIZeroChain](OptimalPolicyRules/TidyR5bCaseIIZeroChain.lean) | 35 | A case-(ii) system whose zero root is not semisimple: the existential Assumption 8.4(ii) holds and the universal one fails |
| [TidyR5bCondExpC](OptimalPolicyRules/TidyR5bCondExpC.lean) | 29 | Complex conditional expectations; the forward solution, one stage of `P(𝒵)` and the cubic of (2.20) on a probability space |
| [TidyR5bPartialSel](OptimalPolicyRules/TidyR5bPartialSel.lean) | 43 | Partial selections of a repeated root: the selected subspace, a real deflating pair, Props 8.1 and 8.2 without `SelWhole`; `Υ` not determined (example) |
| [TidyR5bCyclicSel](OptimalPolicyRules/TidyR5bCyclicSel.lean) | 24 | Partial selections: the invariant subspace is unique iff one Jordan chain; the selected subspace unique iff `CyclicPartial`; `Υ` ↔ column space |
| [TidyR5bFOCNecessity](OptimalPolicyRules/TidyR5bFOCNecessity.lean) | 34 | Necessity of (1.9) for the general LQ problem (faithful expectations); (1.10)–(1.12) without attainability, the affine form (1.11) exactly |
| [TidyR5bFOCMeanSq](OptimalPolicyRules/TidyR5bFOCMeanSq.lean) | 5 | Necessity of (1.9) in conditional mean square, without faithfulness |
| [TidyR5bFaithNeeded](OptimalPolicyRules/TidyR5bFaithNeeded.lean) | 15 | Faithfulness is needed for the pointwise (1.9) (two-state counterexample); (1.9) almost surely, including on the conditional-expectation model |
| [TidyR5bInertiaNecessity](OptimalPolicyRules/TidyR5bInertiaNecessity.lean) | 9 | (2.5) necessary for timeless optimality under any expectation system: in conditional mean square, state by state with faithful expectations; the equivalence |
| [TidyR5bReRep](OptimalPolicyRules/TidyR5bReRep.lean) | 17 | The remark of p. 553 on the circle: agreement on bounded orbits, uniqueness for power-bounded `Λ`, re-representation; Jordan and simple-root examples |
| [TidyR5bProp83Circle](OptimalPolicyRules/TidyR5bProp83Circle.lean) | 13 | A counterexample to Prop 8.3 satisfying the full Assumption 8.1, Assumptions 8.3 and 8.7 (`m = 1`), with a root on `\|μ\| = β⁻¹` |
| [TidyR5bReRepConverse](OptimalPolicyRules/TidyR5bReRepConverse.lean) | 12 | The p. 553 remark under perfect foresight: `Λ`, `Υ` unique iff `Λ` power-bounded |
| [TidyR5bReRepUncertain](OptimalPolicyRules/TidyR5bReRepUncertain.lean) | 10 | The p. 553 remark under every expectation system: re-representation under uncertainty; unique iff `Λ` power-bounded |
| [TidyR5bSelLink](OptimalPolicyRules/TidyR5bSelLink.lean) | 24 | Partial selections on the book's objects: the column space of a real deflating pair is a selected subspace (count data); `Υ` unique iff `CyclicPartial` |
| [TidyR5bStickyBoundary](OptimalPolicyRules/TidyR5bStickyBoundary.lean) | 11 | The (2.20) region for `κ_w ≠ κ_p` under every expectation system, via date-`t₀` forecast paths: the boundary, the exact region, the criterion |
| [TidyR5bStickyMeasure](OptimalPolicyRules/TidyR5bStickyMeasure.lean) | 11 | The (2.20) region on a probability space, the "only if" half and the boundary, via unconditional means |
| [TidyR5bStickyExists](OptimalPolicyRules/TidyR5bStickyExists.lean) | 10 | The (2.20) region on a probability space, the "if" half: existence a.s. iff `StableRoots` |

## Modelling conventions

* **Expectations.** Random variables are `Ω → ℝ` and processes `ℕ → Ω → ℝ`. Every model equation
  holds at every date as an equality of functions, for an arbitrary `ExpectationSystem` (linear,
  constant-preserving, monotone, with the law of iterated expectations). Perfect foresight
  (`perfectForesight`) and every finite event tree
  (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) are instances; the robust-optimality
  theorems of §2 have finite-tree corollaries (`InflTargetInertia.baseline_robustlyOptimal_finiteTree`,
  `InflTargetStickyWages.sym_robustlyOptimal_finiteTree`). Complex roots are handled by the complexified
  expectation `ExpectationTools.EC`. Shifted and delayed information sets are themselves
  expectation systems (`InflTargetPredetermined.shift`, `IRulePredetermined.delay`). The
  measure-theoretic restatement is described in the next bullet.
* **Measure-theoretic expectations.** The core `ExpectationSystem` (an operator `E_t` on all
  functions `Ω → ℝ`, with exact equalities) is kept unchanged, and every result above that is
  stated for it still holds. On a countable `Ω` it forces finitely supported forecasts, so it
  cannot carry an infinite-horizon model with nondegenerate shocks. `ExpectationsMeasure` adds,
  alongside it, a probability space with a filtration (`ExpectationsMeasure.MeasExpectationSystem`):
  `E_t` is Mathlib's conditional expectation `condExp`, variables are bounded measurable functions
  and processes (`BddRV`, `BddProc`, Mathlib's `StronglyAdapted`), and equations hold almost
  everywhere. The bridge is additive and runs both ways: a finite event tree is a measure system
  with the same `E_t` at every state (`ExpectationsMeasure.TreeBridge.treeSystem_E`), and a
  measure system on a finite discrete state space with full support is a core system with the
  pull-out property (`ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem`,
  `ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_pullOut`). The genuine instance
  is the i.i.d. economy on `ℕ → ℝ` under `ν^ℕ`, in which every history has probability zero
  (`ExpectationsMeasureIID.iidSystem`, `ExpectationsMeasureIID.iid_not_finitely_supported`). The
  Chapter 8 objects are restated on it with `E_t` applied componentwise
  (`OptimalRulesMeasure.EVm`) and essentially bounded vector processes
  (`OptimalRulesMeasure.MBoundedV`); the exogenous state is a VAR(1) in the conditional-expectation
  sense (`OptimalRulesMeasureMarkov.IsVAR`), or, from `OptimalRulesMeasureForecast` on, any bounded
  adapted disturbance, which enters through its conditional forecast path
  (`OptimalRulesMeasureForecast.cfc`) and the perfect-foresight kernel
  (`OptimalRulesMeasureKernel.KY`); the endogenous state transition of the general case is
  `OptimalRulesMeasureGeneral.Hgen`, equal to `H_n` (`OptimalRulesMeasureStability.Hn_eq_Hgen`).
  On a finite, fully supported space each notion is the
  core one (`OptimalRulesMeasure.Bridge.mFOCSystem_iff`, `OptimalRulesMeasure.Bridge.mAssumption81_iff`),
  and the one-point space is perfect foresight (`OptimalRulesMeasure.Bridge.unitSystem_pf`).
* **Bounded adapted processes.** Plans, multipliers and disturbances are bounded and adapted;
  pre-sample values (`x_{t₀−1}`, `π_{t₀−1}`, `i_{t₀−1}`, the multiplier history) are bounded and
  known at `t₀`. Uniqueness is uniqueness among bounded adapted processes.
* **Explicit hypotheses.** The optimality theorems take the pull-out property
  (`ExpectationSystem.PullOut`, true for perfect foresight and every finite tree) as a hypothesis.
  Exact uniqueness of an optimum takes faithfulness of the conditional expectation
  (`ExpectationTools.Faithful`, true for perfect foresight); without it the optimum is unique in
  conditional mean square (`InflTargetPredetermined.welfare_eq_imp`). Parameter restrictions the
  book leaves implicit (`0 < β < 1`, `κ, σ, λ > 0`, `0 ≤ γ ≤ 1`, `0 ≤ δ < 1`) are hypotheses.
* **Supplied results as hypotheses.** The chapter's derivations from Proposition 8.1 take its
  conclusion as the structure `TargetCriterion.Prop81.Prop81Conclusion`. The general theory proves
  the corrected structure `Prop81General.Prop81ConclusionM`, and the original implies it
  (`GeneralTheoryLinks.Old.conclusionM_of_conclusion`). Proposition 8.7's conclusions enter
  Propositions 8.9–8.11 as the structure `InflationInertiaRepresentations.InertiaRoots`, which
  `Links.inertiaRoots_of_standing` discharges, so the Links versions are unconditional.
* **Timeless and robust optimality** are given a precise definition in each setting
  (`GeneralSetup.LQProblem.TimelesslyOptimalPlan`, `GeneralSetup.RobustlyOptimal`,
  `InflTargetInertia.TimelessOptimal`, `InflTargetInertia.RobustlyOptimal`,
  `InflTargetStickyWages.TimelessOptimalSW`, `InflTargetHabit.TimelessOptimalH`,
  `InflTargetPredetermined.TimelesslyOptimal`, `IRuleBasic.OptimalGiven`,
  `InflationInertiaRules.TimelesslyOptimal`) and proved.

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check. Each compiler run (the build and the
fresh audit) has a timeout of 3600 s.
