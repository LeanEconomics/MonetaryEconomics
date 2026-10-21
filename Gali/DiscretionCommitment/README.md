# Discretion versus commitment in Lean

This is the `Gali/DiscretionCommitment/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Galí (2015), *Monetary Policy, Inflation, and the
Business Cycle*, 2nd ed., Chapter 5, "Monetary Policy Tradeoffs: Discretion
versus Commitment" (pp. 126–162), with its appendices and exercises. The
library contains **555 theorems** and audits **820 declarations**.

Headline results, in the namespace `Gali.DiscretionCommitment`:
* **Optimal commitment.** The path from the Lagrangian first-order conditions
  is the unique optimum of the infinite-horizon problem
  (`Commitment.Det.existsUnique_optimal`, `Commitment.Det.isOptimal_iff_foc`),
  and under uncertainty it minimises the expected loss among bounded adapted
  plans (`Commitment.commitment_optimal`), given the pull-out property of
  conditional expectations, which every finite event tree satisfies
  (`Commitment.finiteTree_pullOut`).
* **Discretion.** The unique discretionary equilibrium and its implementation
  (`Discretion.discretionEq_iff_msv`, `Discretion.rule10_implements`);
  commitment strictly beats it whenever there is a shock
  (`CommitmentVsDiscretion.commitment_lt_discretion`).
* **Inflation bias.** Discretion has a permanent positive bias; commitment has
  none in the long run (`DistortedSS.inflationBias_pos`,
  `DistortedSS.tendsto_infl_zeroShock`), with (26)–(27) corrected.
* **Zero lower bound.** KKT characterisations under discretion and commitment,
  and a verification theorem for the book's algorithm
  (`ZLBDiscretion.periodOptimal_iff_kkt`, `ZLBCommitment.algorithm_verification`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](DiscretionCommitment/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated from the Chapter 4 project) |
| [Expectations](DiscretionCommitment/Expectations.lean) | 18 | Rational expectations as an `ExpectationSystem`; forward series; determinacy iff Schur–Cohn |
| [ExpectationsFiniteTree](DiscretionCommitment/ExpectationsFiniteTree.lean) | 20 | A finite event tree satisfies the expectation axioms |
| [LossAndCostPush](DiscretionCommitment/LossAndCostPush.lean) | 33 | §5.2, App. 5.1: the loss (1) with `ϑ = κ/ε`, the cost-push NKPC (2), the small-distortion welfare criterion |
| [CostPushSources](DiscretionCommitment/CostPushSources.lean) | 17 | App. 5.2: cost-push shocks from price and wage markups (both printed slips corrected) |
| [Discretion](DiscretionCommitment/Discretion.lean) | 40 | §5.2.1: the period problem, the discretionary equilibrium (5)–(6), dampening, (7)–(10) and implementation |
| [Commitment](DiscretionCommitment/Commitment.lean) | 98 | §5.2.2: the optimal commitment policy, deterministic and under uncertainty; `γ`, `δ`; (11)–(16); the implementing price-level rule |
| [CommitmentVsDiscretion](DiscretionCommitment/CommitmentVsDiscretion.lean) | 14 | §5.2: commitment beats discretion; impact responses; persistence after a transitory shock |
| [DistortedSS](DiscretionCommitment/DistortedSS.lean) | 68 | §5.3: the inflation bias under discretion; commitment with a distorted steady state, (21)–(27) with (26)–(27) corrected; no long-run bias |
| [ZLBDiscretion](DiscretionCommitment/ZLBDiscretion.lean) | 38 | §5.4.1: discretion at the zero lower bound, KKT, the sign lemma, existence; a second (deflationary) equilibrium |
| [ZLBCommitment](DiscretionCommitment/ZLBCommitment.lean) | 42 | §5.4.2: commitment at the zero lower bound, KKT sufficiency, post-liftoff dynamics, the verification theorem for the algorithm |
| [Ex5_1](DiscretionCommitment/Ex5_1.lean) | 38 | Exercise 5.1: the optimised Taylor rule |
| [Ex5_2](DiscretionCommitment/Ex5_2.lean) | 32 | Exercise 5.2: the optimal Markov policy |
| [Ex5_3](DiscretionCommitment/Ex5_3.lean) | 22 | Exercise 5.3: transaction frictions and the implementing rule |
| [Ex5_4](DiscretionCommitment/Ex5_4.lean) | 22 | Exercise 5.4: indexation |
| [Ex5_5](DiscretionCommitment/Ex5_5.lean) | 30 | Exercise 5.5: optimal steady-state inflation with a zero-lower-bound chance constraint |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
