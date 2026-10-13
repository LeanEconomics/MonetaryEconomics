# Source map

Galí (2015), *Monetary Policy, Inflation, and the Business Cycle*, 2nd ed.,
Chapter 3, "The Basic New Keynesian Model" (pp. 52–97). Each formalised claim,
equation or exercise is listed with its Lean name. Page numbers are book pages.

| Book | Page | Claim | Lean |
| --- | --- | --- | --- |
| §3.2 | 55 | A price lasts `k + 1` periods with probability `(1 − θ)θᵏ`; these sum to one | `durationProb`, `durationProb_nonneg`, `survival_sum`, `CalvoParam` |
| §3.2 | 55 | A price is still in force after `k` periods with probability `θᵏ` | `tail_sum` |
| §3.2 | 55 | The average duration of a price is `1/(1 − θ)` | `mean_duration`, `CalvoParam.mean_duration` |
