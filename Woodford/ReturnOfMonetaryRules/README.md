# The return of monetary rules in Lean

This is the `Woodford/ReturnOfMonetaryRules/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of the formal content of Woodford (2003), *Interest and
Prices*, Chapter 1, "The Return of Monetary Rules" (pp. 1–60). The chapter is
largely discursive; its formal claims are all here. The library contains
**127 theorems**, including the shared core.

Headline results, in the namespace `Woodford.ReturnOfMonetaryRules`:
* **The channel system.** The overnight rate lies in the channel, falls with
  reserve supply, and a unique supply hits the target independently of the
  target itself (`ChannelSystem.rate_mem_channel`,
  `ChannelSystem.existsUnique_target_supply`, `ChannelSystem.target_supply_set_indep`).
* **Interest-rate rules.** The difference rule is the Wicksell rule
  (`InterestRateRules.difference_iff_wicksell`); the Taylor principle as the real
  rate rising with inflation (`InterestRateRules.taylorPrinciple_iff`).
* **The neo-Wicksellian model.** For bounded shocks the price level (4.12) is the
  unique bounded equilibrium (`NeoWicksellian.existsUnique_priceLevel`), and
  determinacy holds for every shock exactly when `φ > 0` or `φ < −2`
  (`NeoWicksellian.existsUnique_iff`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the Lean statements make the
printed text precise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Determinacy](ReturnOfMonetaryRules/Determinacy.lean) | 23 | The Schur–Cohn condition for `2 × 2` matrices (restated from the Galí projects) |
| [Expectations](ReturnOfMonetaryRules/Expectations.lean) | 20 | Rational expectations as an `ExpectationSystem`; forward series; the pull-out property |
| [ExpectationsFiniteTree](ReturnOfMonetaryRules/ExpectationsFiniteTree.lean) | 21 | A finite event tree satisfies the expectation axioms and pull-out |
| [ChannelSystem](ReturnOfMonetaryRules/ChannelSystem.lean) | 20 | §3.1–3.2: the channel-system overnight rate (3.1) with a genuine CDF, the target supply (3.2), no clearing demand |
| [InterestRateRules](ReturnOfMonetaryRules/InterestRateRules.lean) | 18 | §4, §4.1: the Wicksell rule and its difference form, the Taylor rule and the Taylor principle, partial adjustment, target criteria |
| [NeoWicksellian](ReturnOfMonetaryRules/NeoWicksellian.lean) | 25 | §4.3: (4.9)–(4.12), the unique bounded price level, its long-run level, and the exact determinacy region |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
