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
figures, and statements about an infinite past are ℤ-indexed and pathwise. The central objects
are the simple sticky-price model (17.1)–(17.14), under adaptive and under rational expectations,
and the three-equation model (17.15)–(17.33); "determinate" means exactly one bounded equilibrium
for every bounded adapted disturbance. The library contains **454 theorems**, including the
shared core; 346 of them are in the twelve chapter modules.

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
  `FullModel.tendsto_zPath`). For Figure 17.6, `Δs(p) = (1 − p)/(λ₁ − ρ) − p` and B has
  `Δs = −1` exactly (`FiscalUnderpinnings.deltaS_closed`, `FiscalUnderpinnings.deltaS_B`); the
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
(p. 420, A1 p. 587), "with `φ < 1` we have multiple equilibria" (A1 p. 587), the
Clarida–Galí–Gertler reading (p. 428), the output response of Figure 17.5 (p. 409), the infinite
past of (17.8) (p. 400), the cross-reference to (1.62) for (1.60) (A1 p. 588) and the rounding
`η* ≈ 0.51` (p. 416).

Not formalised:
* the verbal and historical parts of Chapter 18 (§§18.1–18.3, beyond footnote 1 and
  (18.1)–(18.3)), Sims' (2016) backward-looking fiscal model (p. 431), the determinacy plots of
  Cochrane (2011b) (p. 420, A1 p. 587), and the remarks on why real explosions are not observed
  (p. 421);
* the household problems behind (17.15)–(17.17): the IS and Phillips curves are imposed as
  equilibrium conditions;
* the Figure 17.6 numbers 0.67, 1.66, −1.53 and 2.99: the book gives no `σ, κ, β, ρ` for the
  figure. Only the `Δs` formula, B, C and D, and the inconsistency of A and E are proved;
* existence of a bounded path on ℤ for (17.18) with `β > 0` and an arbitrary bounded rate path:
  uniqueness is proved in general (`FullModel.secondZ_unique`), existence only for the step of
  Figure 17.5 (`FullModel.zPath_existsUnique`);
* stochastic versions of the full-model paths of §17.4: Figures 17.5–17.7, the reverse-engineered
  disturbances and `Δs` are under perfect foresight after the announcement or shock, with
  pre-shock expectations at the steady state. The infinite-past statements ((17.8), the corrected
  inverse of (17.14), `zPath`) are pathwise, because the core `ExpectationSystem` has no infinite
  past;
* (18.2) with inertia `φ_i ≠ 0`, a three-dimensional system with a predetermined variable; the
  book makes no determinacy claim about it;
* real explosions for `φ ≥ 1/β`: `TaylorDeterminacy.real_explosion` covers `φ < 1/β`;
* the likelihood of (18.3) as a statistical object: `History.likelihood_flat` is a statement about
  every function of the equilibrium paths;
* A1 §1.9 (matrix and state-variable methods, pp. 573–578) and the continuous-time parts of
  §1.13 (pp. 580–585), which the chapter only points to; the survey's E11 items on pp. 574–575
  belong there.

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
| [FiscalUnderpinnings](KeynesianStickyPrices/FiscalUnderpinnings.lean) | 39 | §17.4.2: (17.19) with the dating correction, the fiscal contraction, reverse engineering, Figure 17.7 numbers, E10, the `Δs` of Figure 17.6 and its label inconsistency |
| [OptimalPolicy](KeynesianStickyPrices/OptimalPolicy.lean) | 20 | §17.5.1: (17.22)–(17.28), any path attainable, E9 corrected, Woodford's loss, constant intercepts |
| [TaylorDeterminacy](KeynesianStickyPrices/TaylorDeterminacy.lean) | 36 | §17.5.2 and A1 (1.55)–(1.58): structural systems, determinacy with `φ_x`, (1.58), Bullard–Mitra, "neither necessary nor sufficient", (1.55) corrected, (1.57) and E11, `φ` irrelevance, real explosions |
| [History](KeynesianStickyPrices/History.lean) | 11 | Chapter 18: the PIH footnote, (18.1)–(18.3), the Clarida–Galí–Gertler reading |
| [Links](KeynesianStickyPrices/Links.lean) | 28 | Links between the two chains: the simple model as the `β = 0` case of the full model, (1.55) and (17.33), MSV uniqueness on the whole determinacy region, lag roots and eigenvalues, `zPath` and the `full_any_sign` family, (18.1)–(18.2) |

## Modelling conventions

* **Expectations.** Random variables are `Ω → ℝ`, processes `ℕ → Ω → ℝ`, and every linear model
  equation holds as an equality of functions, for an arbitrary `ExpectationSystem`. A process is
  adapted when `E_tx_t = x_t` (`ExpectationSystem.Adapted`). Perfect foresight
  (`perfectForesight`) and every finite event tree
  (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) are instances; the coin-flip tree
  makes the any-sign result genuinely random (`PersistenceFreedom.any_sign_coin`). No chapter
  result needs the pull-out property.
* **Timing.** Dates are natural numbers. In the adaptive model `π_{−1}` is an initial value
  (`StaticIS.lagged`); in Figure 17.7 the book's dates `1, 2, …` are `n = 0, 1, …`. The
  perfect-foresight full model works with sequences `ℕ → ℝ` (`FullModel.PFEqm`,
  `FullModel.Second`), linked to the general model by `FullModel.pf_model_iff`; an infinite past
  is a ℤ-indexed sequence (`FullModel.SecondZ`, `StaticIS.eq_17_8`,
  `PersistenceFreedom.corrected_inverse`).
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
the Galí or Woodford projects.

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
