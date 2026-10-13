# Corrections to the source

Places where a claim in Chapter 3 of Galí (2015) is false, imprecise, or relies
on an unstated hypothesis, and where the Lean statement departs from the
printed one. In each case the Lean statement proves the stated version and
cites the original. Entries are recorded when found and revised if
formalisation shows the finding itself to be wrong.

## Claims that need a changed statement

None yet.

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| p. 55 | `θ ∈ [0, 1)` for the mean duration `1/(1 − θ)` to be finite | `0 ≤ θ`, `θ < 1` (`mean_duration`) |
