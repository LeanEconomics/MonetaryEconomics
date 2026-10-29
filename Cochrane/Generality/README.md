# A bit of generality in Lean

This is the `Cochrane/Generality/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of John H. Cochrane, *The Fiscal Theory of the Price Level* (Princeton
University Press, 2023), Chapter 3, "A bit of generality" (pp. 52–80), with Online Appendix
A1.2–A1.6 (pp. 556–568) and A1.9.1 (pp. 576–577). The chapter generalises the valuation equation
of Chapters 1–2 in five directions: long-term debt, ratios to GDP, stochastic discount factors and
ex-post returns, money, and linearisation; it then repeats the development in continuous time.
Discrete-time results hold for an arbitrary expectation operator, so they cover perfect foresight
and genuine uncertainty: random variables are functions `Ω → ℝ`, processes are `ℕ → Ω → ℝ`, every
equation holds state by state, present values are genuine infinite sums and surpluses are signed.
Continuous-time results are deterministic, with paths `ℝ → ℝ`, present values as improper
integrals, and a price level free to jump at the initial date. The common thread is one theorem in
many settings: **the flow condition plus the transversality condition at every date hold iff the
real value of the debt equals the present value of surpluses at every date**, and then the
valuation equation determines the price level. The library contains **782 theorems**, including
the shared core; 674 of them are in the seventeen chapter modules.

The book has no labelled propositions. The source map is organised by equation number, section
and page, and every Lean name cites the page it formalises.

Headline results, in the namespace `Cochrane.Generality`:
* **Long-term debt (§3.1).** Given the bond-pricing equation (3.1), the flow (3.2) and the
  transversality condition hold at every date iff the valuation equation (3.3) does, for a finite
  maximum maturity (`LongTermDebt.valuationLT_iff`, `LongTermDebt.valuationLT_iff_const`) and for
  a geometric maturity structure with genuine infinite sums (`LongTermDebt.valuationGeom_iff`).
  Without (3.1) the book's step "derive (3.2) from (3.3)" fails
  (`LongTermDebt.valuationLT_not_imp_flow`, E28). The appendix's price jump (1.16) after a
  permanent rate rise, `P_0 < P` iff `i > r` and `ω > 0`, its forward-guidance version and the
  roll-over of geometric debt are proved
  (`LongTermDebt.price_jump_perm`, `LongTermDebt.price_jump_lt_one_iff`,
  `LongTermDebt.price_jump_fg`, `LongTermDebt.steady_flow_iff_1_15`). The knife edge in which a
  geometric structure needs no tending is exactly `P_ts_t = ωᵗb_0` (`LongTermDebt.geom_knife_edge`).
* **Stochastic discounting and ex-post returns (§3.3).** Flow plus TVC iff (3.5),
  `B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}]` (`StochasticDiscount.valuation_sdf_iff`). The
  inverse return is a discount factor under any probabilities (`StochasticDiscount.inv_return_sdf`),
  and (3.6) is iterated with the terminal index corrected (`StochasticDiscount.expost_iterate`,
  E12). The book's warning that (3.6) may explode while (3.5) is fine is realised on an infinite
  state space along a zero-probability path (`StochasticDiscount.expost_may_diverge`), and proved
  impossible on every finite event tree (`StochasticDiscount.finiteTree_expost_pv`).
* **Money (§3.4).** Each of (3.10), (3.11) and (3.12) is equivalent to its own transversality
  condition (`Money.pv_3_10`, `Money.pv_3_11`, `Money.pv_3_12`). (3.10) and (3.11) are equivalent
  only under the money transversality condition, and a money bubble separates them
  (`Money.pv_3_10_iff_money_tvc`, `Money.money_bubble`, E13). The zero-bound formula (3.16)
  follows from (3.10), not (3.11) (`Money.zero_bound_valuation`, `Money.zero_bound_not_from_3_11`,
  E14).
* **Linearisation (§3.5, A1.2–A1.3).** The log-linear identities are exact first derivatives:
  `ρ = e^{−(r−g)}`, not the printed `e^{r−g}` (`LogLinearIdentities.rho_eq`, E11), and the
  bond-return weight is `ω/(1+i)` (`LogLinearIdentities.bondReturn_steady`). The
  unexpected-inflation identity (3.20), the bond-return identity (3.21) and the
  weighted-inflation identity (3.22) hold on any expectation system
  (`LogLinearIdentities.innov_identity_3_20`, `LogLinearIdentities.bondReturn_innov`,
  `LogLinearIdentities.weighted_inflation_identity`), with the special cases (3.23)–(3.28) and
  Figure 3.1.
* **The innovation identities beyond bounded processes (§3.5).** With summable present values,
  the printed (3.20) holds iff the terminal limits satisfy `L_t = ρL_{t+1}`
  (`TidyR6InnovGrowth.identity_3_20_iff`), in particular under the transversality condition
  (`TidyR6InnovGrowth.identity_3_20_of_tvc`). (3.19)–(3.28) hold for any `ρ > 0` and processes
  growing at a rate `γ < 1/ρ` (`TidyR6InnovGrowth.g_identity_3_20`,
  `TidyR6InnovGrowth.g_weighted_inflation`), and fail at the boundary `γ = 1/ρ`
  (`TidyR6InnovGrowth.Boundary.boundary_3_20`). On a measure space with a filtration they hold
  almost everywhere for integrable processes with `L¹` (or `L²`) growth `γ < 1/ρ`
  (`TidyR6InnovMeasure.m_identity_3_20`, `TidyR6InnovMeasure.m_weighted_inflation`,
  `TidyR6InnovMeasure.L2Growth.toL1`).
* **Figure 3.1 as an equilibrium (§3.5.3).** The linear model with an interest-rate target,
  the expectations hypothesis, the Fisher equation and the flow (3.17) has exactly one
  equilibrium (`TidyR6Fig31Equilibrium.exists_eqm`, `TidyR6Fig31Equilibrium.unique_eqm`). In it
  a permanent rate rise gives the Figure 3.1 response, a rise announced `k` periods ahead gives
  the impact `−ω̂ᵏ/(1 − ω̂)`, and an expected rise gives no jump
  (`TidyR6Fig31Equilibrium.fig31_equilibrium`, `TidyR6Fig31Equilibrium.announcement_equilibrium`,
  `TidyR6Fig31Equilibrium.expected_rise_equilibrium`), as in a coin-flip economy
  (`TidyR6Fig31Equilibrium.CoinEconomy.fig31_coin_economy`).
* **Figure 3.1 reconciled (E15).** At the figure's `r = 2%`, `i = 3%`, `ω = 0.8`, one theorem
  proves the exact proportional drop 3.41%, the exact log drop 3.46–3.48% (the text's "3.5%"), the
  linear drop 4% with the printed weight `ω` (the figure), and 3.48% with the exact weight
  `ω/(1+i)` (`Links.e15_reconciled`). The figure's 4% comes from the weight, not from
  linearising.
* **Continuous time (§3.6, A1.4–A1.6).** Valuation iff transversality, existence and uniqueness,
  and the price level `P(t) = B(t)/∫Ds` with short-term debt (`ContinuousShort.valuation_iff_tvc`,
  `ContinuousShort.exists_unique_flow_tvc`, `ContinuousShort.price_level_determined`); the same
  with geometric long-term debt and with an arbitrary maturity density under explicit regularity
  (`ContinuousLong.valuation_LT_iff`, `ContinuousLong.valuation_general_iff`); the linearised
  news identities (3.46)–(3.51) between two perfect-foresight paths
  (`ContinuousLinear.news_weighted_inflation`); short-term debt as the limit `ω → ∞`, not `ω = 0`
  (`ContinuousLinear.short_limit`, E20); and the money valuations (3.53)–(3.55)
  (`ContinuousMoney.money_printing_iff`, `ContinuousMoney.money_interest_iff`,
  `ContinuousMoney.money_mixed_iff`).
* **The simplest model by undetermined coefficients (A1.9.1).** The bounded-debt equilibrium
  exists and is unique, and bounded debt holds iff debt is the forward solution
  (`MSV.msv_exists`, `MSV.msv_unique`, `MSV.msv_determinacy`). Inflation is
  `π_{t+1} = u_{i,t} − ε_{s,t+1}/(1 − ρη_s)`, with a minus sign (`MSV.msv_solution`, E24).
* **Links among the chains.** The discrete and continuous objects agree where the book talks about
  the same thing: short-term debt is `ω = 0` in discrete time (`Links.valuationGeom_zero_iff`)
  and `ϖ → ∞` in continuous time (`Links.short_debt_limits`); the (3.22) and (3.51) weights agree
  on the integer grid (`Links.weights_322_351`); the discrete annuity and jump ratio converge to
  their continuous counterparts (`Links.annuity_tendsto_bondPrice`,
  `Links.jumpRatio_tendsto_continuous`).
* **Discrete to continuous with time-varying rates.** The discrete bond-price recursion
  converges to the transversality solution of `Q' = (i + ϖ)Q − 1` uniformly on compacts, and on
  `[t₀, ∞)` for a bounded, uniformly continuous rate
  (`TidyR6DiscreteBondLimit.tendstoUniformlyOn_Icc`,
  `TidyR6DiscreteBondLimit.tendstoUniformlyOn_Ici`,
  `TidyR6DiscreteBondLimit.tendsto_unique_ode_solution`). Uniform convergence on `[0, ∞)` needs
  uniformly consistent per-period rates (`TidyR6DiscreteBondLimit.not_uniform_Ici`). The discrete
  valuation recursion converges in the same way to the solution of `V' = rV − s`
  (`TidyR6DiscreteValuationLimit.val_tendstoUniformlyOn_Icc`,
  `TidyR6DiscreteValuationLimit.val_tendstoUniformlyOn_Ici`). E13 is one continuous economy
  and its discretisations, with the same gap and converging flows
  (`TidyR6E13Limit.e13_one_economy`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for the claims found false and where the Lean statements make
the printed text precise. The main corrections are:
* E11, p. 63: `ρ = e^{−(r−g)}`, not `e^{r−g}`;
* E13, p. 57: (3.10) and (3.11) are equivalent only under the money transversality condition, in
  discrete and in continuous time (`Links.e13_discrete_and_continuous`), and in one economy and its
  discretisations (`TidyR6E13Limit.e13_one_economy`);
* E14, p. 59: (3.16) follows from (3.10), not (3.11);
* E15, A1 p. 560 and Figure 3.1: the 3.5% of the text and the 4% of the figure reconciled (above);
* E20, pp. 78–79: short-term debt is `ω → ∞`, not `ω = 0`, which is the perpetuity;
* E23, A1 p. 566: "so the limit is zero" does not follow from (1.27); the limit is the
  transversality condition (`ContinuousLong.A15_counterexample`);
* E24, A1 pp. 576–577: the sign of the fiscal shock in inflation is minus;
* E28, p. 53: deriving (3.2) from (3.3) needs (3.1);
* **p. 64 (new):** "debt/GDP is expected to grow no faster than `ρ^{−t}`" is insufficient. Growth
  exactly `ρ^{−t}` breaks (3.19) and (3.20) (`TidyR6InnovGrowth.Boundary.boundary_3_20`); the
  condition is `ρ^T E_t v_{t+T} → 0`, implied by strictly slower growth
  (`TidyR6InnovGrowth.identity_3_20_of_tvc`, `TidyR6InnovGrowth.g_identity_3_20`);
* **(3.26), p. 68 (new):** the nonlinear valuation equation is printed with the scaled surplus
  `s̃`; it is (3.3), with `s` (`Links.eq_3_26_printed_iff`);
* A1 p. 566 (new): at jump points `dW/W = dV/V`, not `dP/P`, which has the wrong sign for short
  debt (`ContinuousLong.jump_short_return_sign`);
* the typos E12, E16, E18, E19, E21, E22 and E31, each with a counterexample to the printed form
  where one exists, and the 1980s figure of p. 60 (`200/3000 = 6.7%`, not 5%).

Four further results make the text precise rather than correct it:
* **The p. 56 finite-tree result.** On every finite event tree in which all states have positive
  probability, (3.5) with its flow and transversality condition forces the ex-post present value
  (3.6) to converge absolutely in every state, with a vanishing terminal term
  (`StochasticDiscount.finiteTree_expost_pv`). Information on a finite tree stops being refined,
  after which the inverse return equals the discount factor. The explosion the book describes needs
  an infinite state space and a path to which agents give probability zero
  (`StochasticDiscount.expost_may_diverge`).
* **The §3.6.2 regularity.** The book differentiates `∫_0^∞Q_t^{(t+j)}B_t^{(t+j)}dj` under the
  integral sign without stating any hypothesis. The derivation needs joint differentiability of
  `Q` and `B` in date and maturity, integrability of the value, of new issues and of the maturity
  derivative, decay at long maturities, an integrable bound on the date derivative, and the par
  condition `Q_t^{(t)} = 1`, which produces the `−B_t^{(t)}dt` term
  (`ContinuousLong.MaturityRegularAt`). Under them (3.38)–(3.39) and valuation iff transversality
  hold as printed (`ContinuousLong.hasDerivAt_value_general`,
  `ContinuousLong.valuation_general_iff`).
* **The A1 p. 561 knife edge.** "Nonstochastic and geometric" surpluses means nominal surpluses
  `P_ts_t = ωᵗb_0`, known at date 0 (`LongTermDebt.geom_knife_edge`,
  `LongTermDebt.knife_edge_surplus_known`).
* **`ρ = 1` on p. 64.** For (3.20) to hold "describing deviations from this mean", `E_t v_{t+T}`
  and `E_{t+1}v_{t+1+T}` must converge to the same constant
  (`TidyR6InnovGrowth.identity_3_20_rho_one_mean`). Boundedness alone is not enough
  (`TidyR6InnovGrowth.Boundary.rho_one_bounded`).

Not formalised:
* the discursive passages: that price stickiness makes the effect of a rate rise smaller (A1
  p. 560), the qualitative discussion of a passive money supply (pp. 61–62; only the split
  `M = Py/V` and the irrelevance of the split under full interest are proved,
  `Money.passive_split`, `Money.full_interest_split_irrelevant`), and the historical reading of
  the seigniorage numbers beyond their arithmetic;
* the remark of p. 66 that §3.5.2 "agrees with (2.13)": projects do not import each other, and
  `LogLinearIdentities.special_constant_short` is the statement on this side;
* diffusions and jumps, (3.44)–(3.45): Mathlib has no stochastic integral. Continuous time is
  deterministic, an innovation is the difference between two perfect-foresight paths
  (`ContinuousLinear.Eqm.LinearEqm`), and `E_t[d(ΛW)] = 0` is stated as `(ΛW)' = 0`
  (`ContinuousLong.Lambda_W_const`);
* a Gaussian instance of `TidyR6InnovMeasure.MGrowthEconomy`. The almost-everywhere theorems
  are universally quantified, and `TidyR6InnovMeasure.L2Growth.toL1` covers stationary `L²`
  processes, but no Gaussian economy is constructed.

Stated limits of the results that are formalised:
* the convergence theorems on `[t₀, ∞)` assume a bounded, uniformly continuous rate
  (`TidyR6DiscreteBondLimit.tendstoUniformlyOn_Ici`), and the valuation version also a bounded,
  uniformly continuous surplus (`TidyR6DiscreteValuationLimit.val_tendstoUniformlyOn_Ici`).
  Without uniformly consistent per-period rates uniform convergence on `[0, ∞)` can fail
  (`TidyR6DiscreteBondLimit.not_uniform_Ici`); that uniform continuity of the rate itself is
  necessary is not proved;
* the valuation theorem on compacts assumes surpluses bounded on `[t₀, ∞)`
  (`TidyR6DiscreteValuationLimit.val_tendstoUniformlyOn_Icc`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](Generality/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (shared core, restated from the earlier projects) |
| [Expectations](Generality/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; bounded adapted processes; forward series; the pull-out property (shared core) |
| [ExpectationsFiniteTree](Generality/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out; coin-flip examples (shared core) |
| [ForwardSolution](Generality/ForwardSolution.lean) | 44 | The forward solution of `z_t = a E_t z_{t+1} + u_t` (shared core, restated from the Woodford Chapter 2 and 3 projects) |
| [LongTermDebt](Generality/LongTermDebt.lean) | 93 | §3.1, (3.1)–(3.3), and A1.2.1 in discrete time: stochastic discounting and flow + TVC iff present value for signed surpluses; zero-coupon pricing; finite and geometric maturity; E28; the price jump (1.14)–(1.16), (1.19), the 3.41% of E15, forward guidance, transitory rises, roll-over and the knife edge |
| [Ratios](Generality/Ratios.lean) | 10 | §3.2, (3.4): the valuation equation per unit of GDP and per dollar; no expected innovations; growth raises the valuation |
| [StochasticDiscount](Generality/StochasticDiscount.lean) | 42 | §3.3, (3.5)–(3.8): the SDF valuation and the price level; inverse returns; (3.6) with E12; the peso example in which (3.6) explodes, and its impossibility on finite trees; the portfolio return |
| [Money](Generality/Money.lean) | 38 | §3.4, (3.9)–(3.16): the three present-value forms each iff its TVC; E13 with the money bubble; (3.13)–(3.15); the zero bound and E14; seigniorage offsets and arithmetic |
| [LogLinearIdentities](Generality/LogLinearIdentities.lean) | 72 | §3.5 and A1.2–A1.3: the nonlinear identities and their exact derivatives (E11, the weight `ω/(1+i)`); (3.17)–(3.25), (3.27)–(3.28); E16; Figure 3.1 and the log drop of E15 |
| [MSV](Generality/MSV.lean) | 25 | A1.9.1, (1.47)–(1.50): existence, uniqueness and determinacy of the bounded-debt equilibrium; undetermined coefficients; E24; the explosive root |
| [ContinuousShort](Generality/ContinuousShort.lean) | 60 | §3.6.1, (3.29)–(3.33), A1.4: discounting, valuation iff TVC, existence, uniqueness and bubbles, the price level and its jumps, the `Λ` and `W` chains, constant rates |
| [ContinuousLong](Generality/ContinuousLong.lean) | 70 | §3.6.2, (3.34)–(3.39), A1.2.1 and A1.5 in continuous time: the geometric bundle, finite portfolios and a general maturity density under explicit regularity; E20, E23 and the jump relation of A1 p. 566; the price jump, perpetuity and forward guidance |
| [ContinuousLinear](Generality/ContinuousLinear.lean) | 68 | §3.6.3, (3.39)–(3.51): a valuation engine for any discount factor; exact derivatives of the flow and bond identities; E18, E19, E21; the bond-price forward solution; news identities between two paths; the short-debt limit (E20) |
| [ContinuousMoney](Generality/ContinuousMoney.lean) | 20 | §3.6.4, (3.52)–(3.55), A1.6: money creation, interest saving and the mixed return, each iff its TVC; the continuous E13; E21 |
| [Links](Generality/Links.lean) | 30 | Agreement among the four chains: discrete valuation machinery, short-term debt as `ω = 0` and `ϖ → ∞`, discrete and continuous weights and limits, E15 in one statement, E13 in both settings, the (3.26) misprint |
| [TidyR6DiscreteBondLimit](Generality/TidyR6DiscreteBondLimit.lean) | 35 | §3.6.2 and A1 (1.14)→(1.17): the discrete bond-price recursion with time-varying rates, its transversality solution, error bounds, convergence to `Q' = (i + ϖ)Q − 1` on compacts and on `[t₀, ∞)`; a counterexample to uniform convergence on `[0, ∞)` |
| [TidyR6DiscreteValuationLimit](Generality/TidyR6DiscreteValuationLimit.lean) | 16 | (3.5), (3.30)–(3.31), A1.4: the discrete valuation recursion with time-varying `r` and `s` converges to `V' = rV − s`, on compacts and on `[t₀, ∞)` |
| [TidyR6E13Limit](Generality/TidyR6E13Limit.lean) | 12 | §3.4, §3.6.4, A1.6: E13 as one continuous economy and its discretisations, with the same gap and converging flows |
| [TidyR6InnovGrowth](Generality/TidyR6InnovGrowth.lean) | 38 | §3.5, A1.3: (3.20) iff `L_t = ρL_{t+1}`; `ρ = 1` with a common mean; (3.19)–(3.28) for growth `γ < 1/ρ`; counterexamples at `γ = 1/ρ` and `γ = 1/\|ω̂\|` |
| [TidyR6Fig31Equilibrium](Generality/TidyR6Fig31Equilibrium.lean) | 15 | §3.5.3, A1.3: the full linear model, existence and uniqueness of equilibrium; Figure 3.1, announcements and the expected rise as equilibrium responses; a coin-flip instance |
| [TidyR6InnovMeasure](Generality/TidyR6InnovMeasure.lean) | 30 | §3.5, A1.3 on a measure space with a filtration: (3.18)–(3.28) almost everywhere for integrable processes with `L¹` (or `L²`) growth `γ < 1/ρ` |

## Modelling conventions

* **Expectations.** Discrete-time modules (`LongTermDebt`, `Ratios`, `StochasticDiscount`,
  `Money`, `LogLinearIdentities`, `MSV`) work with an arbitrary `ExpectationSystem`: linear,
  constant-preserving and monotone, with the law of iterated expectations. Perfect foresight
  (`perfectForesight`) and every finite event tree
  (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) are instances.
* **Pull-out and monotone convergence as hypotheses.** Results that take date-`t` quantities out
  of `E_t` assume `ExpectationSystem.PullOut`. Results that exchange `E_t` with an infinite sum
  assume conditional monotone convergence (`LongTermDebt.MonotoneConvergence`, survey E29). Both
  hold for perfect foresight and every finite tree, but the `ExpectationSystem` axioms imply
  neither.
* **Discount factors.** Discrete discounting uses one-period factors `m_t = Λ_{t+1}/Λ_t`, known
  at `t + 1`, and `LongTermDebt.sdf` for `Λ_{t+n}/Λ_t`. The book's frictionless case is `m ≡ β`
  (`LongTermDebt.sdf_const`). `Money` works with the levels `Λ_t` (`Money.Standing`); the two
  forms are linked (`Links.pvRel_iff_pv`).
* **Signed surpluses.** Present values are genuine infinite sums of signed surpluses with
  absolutely summable present values (`LongTermDebt.SurplusSummable`), handled through positive
  and negative parts.
* **Timing and debt.** In `LongTermDebt`, `B t j` is `B_{t−1}^{(t+j)}` and `Q t j` is
  `Q_t^{(t+j)}`; the geometric decay `ω` is written `w` there, because `ω` names states. In
  `Ratios` and `StochasticDiscount`, `D t` is `B_{t−1}`. In `Money`, `B t` and `M t` are `B_{t−1}`
  and `M_{t−1}`. Maturity structures are either finite (`LongTermDebt.MaxMaturity`) or geometric
  (`LongTermDebt.geomDebt`).
* **Linear identities.** The linear model of `LogLinearIdentities` is bounded ("stationary",
  p. 64) with `0 < ρ < 1` (`LogLinearIdentities.LinearEconomy`). `TidyR6InnovGrowth` allows any
  `ρ > 0` and processes growing at a rate `γ < 1/ρ` (`TidyR6InnovGrowth.GrowthEconomy`), and
  `TidyR6InnovMeasure` integrable processes with `L¹` growth on a finite measure space with a
  filtration, every identity holding almost everywhere (`TidyR6InnovMeasure.MGrowthEconomy`).
  The bond-return weight is a free parameter `ω̂` (`LogLinearIdentities.BondRet`): `ω/(1+i)` for
  the exact derivative, `ω` for the book's (1.24).
  Innovations are `LogLinearIdentities.innov`, `ΔE_{t+1} = E_{t+1} − E_t`.
* **Continuous time.** Paths are deterministic functions `ℝ → ℝ`. Rates and surpluses are
  continuous on `[t, ∞)`; values are continuous on `[t, ∞)` and differentiable on `(t, ∞)`, so
  the price level may jump at `t` (`ContinuousShort.FlowOn`). The discount function is
  `D(t,τ) = exp(−∫_t^τ r)` (`ContinuousShort.disc`), present values are improper integrals under
  absolute integrability (`ContinuousShort.PVIntegrable`), and the transversality condition is an
  explicit limit. `ContinuousLinear` carries a second valuation engine for any discount factor
  `Λ' = −rΛ`; the two engines are linked (`Links.tvc_iff_pv_of_engine`).
* **Bond normalisation.** A geometric bundle pays the coupon flow `e^{−ω(u−t)}`
  (`ContinuousLong.bondPrice`). The book's density `ϖe^{−ϖj}B` differs by the constant `ϖ`, which
  leaves price ratios unchanged. `ω = 0` is the perpetuity; `ω → ∞` is instantaneous debt.
* **Innovations in continuous time** are differences between an old and a new perfect-foresight
  equilibrium of the linearised model from the news date on (`ContinuousLinear.Eqm.LinearEqm`).
* **Money in continuous time** is discounted with the nominal factor `N = Λ/P`, `N' = −iN`, so the
  price level itself need not be differentiable (`ContinuousMoney`).

## Relation to the Woodford projects

The shared core (`Determinacy`, `Expectations`, `ExpectationsFiniteTree`, `ForwardSolution`) is
restated from the Woodford projects, so the project builds on its own; `Determinacy` (Galí 2015,
Chapter 3, and Woodford's Appendix C) is carried for the later Cochrane projects and is not used
here. Nothing is imported from those projects. Two groups of Woodford results are restated as
tools:
* from the Chapter 2 project (`PriceLevelDetermination`, `AssetPricing` and
  `IntertemporalBudget`): the multi-period discount factor, conditional monotone convergence and
  the present-value tail identities (`LongTermDebt.sdf`, `LongTermDebt.MonotoneConvergence`,
  `LongTermDebt.perfectForesight_monotoneConvergence`,
  `LongTermDebt.finiteTree_monotoneConvergence`,
  `LongTermDebt.hasSum_E_sdf_mul_pv`, `LongTermDebt.hasSum_E_sdf_mul_pv_signed`), adapted to
  signed surpluses in `LongTermDebt.flow_tvc_iff_pv`;
* from the Chapter 4 project (`NeoWicksellianFramework`): the scalar debt recursion and its
  bounded-input-bounded-state dichotomy (`MSV.dRec`, `MSV.eq_dRec`, `MSV.abs_rec_le`,
  `MSV.rec_bounded`, `MSV.rec_unbounded`). In A1.9.1 debt follows this recursion with the
  explosive root `ρ⁻¹` (`MSV.msv_debt_rec`, `MSV.msv_debt_not_bibo`), which is how the bounded-debt
  requirement selects the forward solution.

`Links` here links the chapter's own four formalisation chains, not other projects. The
constant-`β` specialisation of (3.5) is the valuation equation of the Chapter 2 project
(`IntertemporalModel`) for one-period debt (`Links.valuation_sdf_beta_iff`), stated on this side
only.

## Build and verify

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
