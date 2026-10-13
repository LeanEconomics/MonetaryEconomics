# The basic New Keynesian model in Lean

This is the `Gali/BasicNewKeynesianModel/` proof project in
[LeanEconomics/MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics).
Run the commands below from this directory. [Return to the library index](../../README.md).

A checked formalisation of Galí (2015), *Monetary Policy, Inflation, and the
Business Cycle*, 2nd ed., Chapter 3, "The Basic New Keynesian Model"
(pp. 52–97), with the exercises. The library contains **5 theorems**.

Headline results, in the namespace `Gali.BasicNewKeynesianModel`:
* **Calvo price durations.** The duration distribution sums to one and the
  average duration of a price is `1/(1 − θ)` (`survival_sum`, `mean_duration`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [PriceDuration](BasicNewKeynesianModel/PriceDuration.lean) | 5 | §3.2: Calvo price durations, mean duration `1/(1 − θ)`, the bundled parameter `CalvoParam` |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
