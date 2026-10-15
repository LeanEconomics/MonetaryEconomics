# Dynamics of the response to monetary policy in Lean

This is the `Woodford/PolicyResponseDynamics/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Woodford (2003), *Interest and Prices*, Chapter 5, "Dynamics of the
Response to Monetary Policy" (pp. 320–380), together with the proofs in Appendix D
(pp. 687–691). Model equations hold for an arbitrary expectation operator, so results cover
perfect foresight and genuine uncertainty; log-linear equations are exact derivatives of the
nonlinear model, infinite sums are genuine limits, and determinacy means existence and
uniqueness of a bounded adapted equilibrium for every bounded forcing, proved rather than
assumed from a root count. The library contains **757 theorems**, including the shared core.

Headline results, in the namespace `Woodford.PolicyResponseDynamics`:
* **Predetermined expenditure.** The IS relation (1.6)–(1.8) as exact derivatives, with the
  forward solution for `λ̂` holding exactly when the limit exists
  (`Predetermined.eq16_deriv`, `Predetermined.lam_forward_iff`,
  `Predetermined.lam_forward_needs_limit`); the delayed model reduces to the Chapter 4 system, so
  it is determinate iff (1.14) holds, with (1.13) corrected (`Predetermined.delayed_determinate_iff`,
  `Predetermined.printed_rule_counterexample`); its solution is the forecast of the Chapter 4
  solution, and intercept tracking with `+ π̄` minimises the gap variance
  (`Predetermined.delayed_eq_forecast_ch4`, `Predetermined.intercept_tracking_iff`,
  `Predetermined.variance_gap_tracking`).
* **Habit persistence.** `λ_t` as the marginal value of income, in both interpretations
  (`Habit.habit_marginal_value`, `Habit.invest_marginal_value`), the forward solution and the
  AR(2) output gap (`Habit.forward_solution`, `Habit.ar2_output_gap`), (1.26) iff (1.27) for every
  `η ≥ 0` with the root location of (1.28) (`Habit.AS126_iff_AS127_habit`,
  `Habit.habDelta_lt_iff`), and existence and uniqueness under an exact Blanchard–Kahn condition
  for `n` non-predetermined variables, shown to hold at a calibration
  (`Habit.habit_existsUnique`, `Habit.bkCondition_calibration`).
* **Small quantitative models.** (2.1), (2.4)–(2.7) derived, the Table 5.1–5.3 arithmetic with
  `ζ` corrected (`SmallModels.eq21`, `SmallModels.eq25`, `SmallModels.table51_zeta_from_theta`),
  and the Figure 5.8 rule identified as (2.8), which is determinate, rather than (1.12), which is
  not (`SmallModels.fig58_rule112_indeterminate`, `SmallModels.Prop44.fig58_rule28_determinate`).
* **Investment and pricing.** (3.3)–(3.11) as exact derivatives, with `q` and (3.7) corrected
  (`InvestmentModel.FOC.eq_3_3_bounded`, `InvestmentModel.Linearise.eq_3_6`,
  `InvestmentModel.Linear.eq_3_7_printed_false`); Proposition 5.1 in full, with `a, b > 0`
  false as printed and true iff `αβμ₂ < 1` (`Prop51.prop51`, `Links.prop51_investmentModel`,
  `Prop51.book_calibration_a_neg`, `Prop51.a_pos_b_pos`); (3.17), the forward solution (3.19)
  under an exact root condition, and the limits as `ε_ψ → ∞` (`InvestmentLimits.eq314_iff_eq317`,
  `InvestmentLimits.determinate317_iff`, `InvestmentLimits.limit_relation_iff`).
* **The IS block and the natural rate.** Root location and the solutions (3.20)–(3.23) with the
  constant coefficient corrected to `σ + kh` (`ISBlock.Par.roots_iff`, `ISBlock.eq323`,
  `ISBlock.chi_const`); Proposition 5.2 with its missing terms restored
  (`InvestmentNaturalRate.prop52`, `InvestmentNaturalRate.printed328_false`), and determinacy of
  (3.36) iff every eigenvalue of `Â` lies outside the unit circle, from a proved criterion for
  `n`-dimensional forward systems (`InvestmentNaturalRate.econ_determinate_iff`,
  `ForwardSystems.expSysDeterminate_iff`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise.

Not covered: necessity of the Blanchard–Kahn condition for the habit model (1.30)–(1.33), which
is deferred to a later project on the general theory (sufficiency is proved); the empirical
content of the chapter (the VAR identification, Figures 5.1–5.5, Table 5.4 and its Wald tests,
and the estimated reaction functions) is out of scope; the simulated impulse responses and
coefficient plots of Figures 5.6–5.10 are not formalised, only the claims the text makes about
them.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](PolicyResponseDynamics/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated from the Galí projects) |
| [Expectations](PolicyResponseDynamics/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; forward series; the pull-out property |
| [ExpectationsFiniteTree](PolicyResponseDynamics/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out |
| [ForwardSolution](PolicyResponseDynamics/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` for `\|a\| < 1`, the continuum for `\|a\| ≥ 1` (restated from the Chapter 2 and 3 projects); `E_t` and dominated series |
| [ForwardSystems](PolicyResponseDynamics/ForwardSystems.lean) | 38 | Vector forward systems (restated from the Chapter 4 and Galí Chapter 6 projects); second-order equations with one stable root (p. 365, D.2); determinacy of `n`-dimensional systems `E_t x_{t+1} = A x_t + w_t` (p. 376) |
| [ExpectationCalculus](PolicyResponseDynamics/ExpectationCalculus.lean) | 3 | Differentiating under `E_t`, shared by the exact derivatives of §1 and §3 |
| [Predetermined](PolicyResponseDynamics/Predetermined.lean) | 83 | §1.1: (1.3)–(1.11) as exact derivatives, the delayed model (1.12)–(1.17) and its determinacy, intercept tracking and the variance decomposition, (1.18)–(1.22); Proposition 4.3 restated |
| [SmallModels](PolicyResponseDynamics/SmallModels.lean) | 109 | §2: (2.1)–(2.7), Tables 5.1–5.3, rule (1.12) and Figure 5.8; Propositions C.1, C.2 and sufficiency in Proposition 4.4 restated |
| [Habit](PolicyResponseDynamics/Habit.lean) | 93 | §1.2, D.1: (1.23)–(1.29) as exact derivatives, the forward solution, the root of (1.28), the one-predetermined-variable theory for (1.30)–(1.33) and a calibration |
| [InvestmentModel](PolicyResponseDynamics/InvestmentModel.lean) | 94 | §3.1–3.2: (3.1)–(3.13) and (3.18) as exact derivatives, with (3.6) and (3.7) corrected, the steady state, the long run of p. 365, the natural rate of p. 373 |
| [Prop51](PolicyResponseDynamics/Prop51.lean) | 75 | §3.2, D.2: Proposition 5.1 with (D.2)–(D.6), the equality case, the signs of `a` and `b` corrected |
| [InvestmentLimits](PolicyResponseDynamics/InvestmentLimits.lean) | 44 | §3.2–3.3: (3.16)–(3.19), n. 31, the limits as `ε_ψ → ∞` |
| [ISBlock](PolicyResponseDynamics/ISBlock.lean) | 53 | §3.3: (3.20)–(3.26), root location, the constant IS coefficient of p. 367 corrected, n. 34 |
| [InvestmentNaturalRate](PolicyResponseDynamics/InvestmentNaturalRate.lean) | 37 | §3.4, D.3: the natural rate, Proposition 5.2 corrected, (3.27)–(3.39), determinacy of (3.36), n. 38, p. 378 |
| [Links](PolicyResponseDynamics/Links.lean) | 20 | §1–§3: the investment model linked to Propositions 5.1 and 5.2 and to the IS block, the habit model to (2.4), (1.26) and (D.2) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
