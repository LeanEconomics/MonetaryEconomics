# Monetary Economics in Lean

Checked monetary economics, following two textbooks: Jordi Galí, *Monetary
Policy, Inflation, and the Business Cycle: An Introduction to the New Keynesian
Framework and Its Applications* (2nd ed., 2015), and Michael Woodford,
*Interest and Prices: Foundations of a Theory of Monetary Policy* (2003). Each
folder is an independent Lean/Mathlib project for one chapter, with precise
statements, a source map to the book's equations, propositions and pages, a
record of where the printed text had to be corrected, and reproducible proof
checks. Galí projects live under `Gali/`, Woodford projects under `Woodford/`.

| Project | Chapter | Checked results | Start here |
| --- | --- | --- | --- |
| [Gali/BasicNewKeynesianModel](Gali/BasicNewKeynesianModel/README.md) | Galí 3 The Basic New Keynesian Model | 5 theorems: Calvo price durations, mean duration `1/(1 − θ)` | [Chapter overview](Gali/BasicNewKeynesianModel/README.md) |

Every project builds and audits with `python scripts/verify.py` from its own
directory; GitHub Actions runs all of them.
