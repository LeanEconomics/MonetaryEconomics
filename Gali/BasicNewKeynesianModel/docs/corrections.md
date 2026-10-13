# Corrections to the source

Places where a claim in Chapter 3 of Galí (2015) is false, imprecise, or relies
on an unstated hypothesis, and where the Lean statement departs from the
printed one. In each case the Lean statement proves the stated version and
cites the original. Entries are recorded when found and revised if
formalisation shows the finding itself to be wrong. Lean names are relative to
the namespace `Gali.BasicNewKeynesianModel`.

## Claims that are false as printed

| Where | Book says | Finding |
| --- | --- | --- |
| (20), p. 62 | `ψ_y > 0`. | False: `ψ_y < 0` whenever `μ > 0` and `α ∈ [0, 1)`, in particular at `μ = log(ε/(ε − 1))`. This matches the next sentence (market power lowers output) (`NKPC.psi_y_neg`, `NKPC.psi_y_neg_at_markup`; the printed sign is refuted by `NKPC.not_psi_y_pos`). |
| p. 61 | `λ` is strictly decreasing in the demand elasticity `ε`. | True only when `α > 0` (`NKPC.lam_strictAntiOn_eps`). At `α = 0`, `Θ = 1` and `λ` does not depend on `ε` (`NKPC.lam_const_eps`, `NKPC.not_lam_strictAntiOn_eps`). |
| p. 72 | The employment response to technology is `[(1−σ)κ(φ_π−ρ_a)/D − (φ_y+σ(1−ρ_a))(1−βρ_a)]Λ_a`. | The second term is missing the factor `1/(1 − α)`. The corrected coefficient differs from the printed one by `−α/(1−α)·(φ_y+σ(1−ρ_a))(1−βρ_a)Λ_a`, nonzero whenever `α ≠ 0`. At the baseline the corrected value is −0.2564 and the printed one is −0.1923 (`ShockResponses.techNCoef_eq`, `ShockResponses.techNCoef_ne_printed`, `Calibration.employment_baseline`). Sign conclusions are unaffected. |
| p. 72 | "It is easy to check that `κ(φ_π − ρ_a)Λ_a ∈ (0, 1)`." | Needs `φ_π > ρ_a` (and `ρ_a < 1`); proved under that hypothesis (`ShockResponses.techOutputCoef_mem`). Counterexample satisfying (28): `φ_π = 0`, `φ_y = 20`, `ρ_a = 0.9`, `β = 0.99`, `σ = 1`, `κ = 0.1717`. The coefficient is negative, so output falls after a positive technology shock (`ShockResponses.techOutputCoef_counterexample`). It equals 1 at `ρ_a = 1`, `φ_y = 0` (`ShockResponses.techOutputCoef_unit_root`). The claim "`σ ≥ 1` implies employment falls" also needs `φ_π ≥ ρ_a` (`ShockResponses.techNCoef_neg_of_one_le_sigma`). |
| p. 71 | The discount-rate shock implies "an increase on impact of one percentage point in the (annualized) natural rate". | A fall: with `ρ_z = 0.5` and `ε^z = −0.5` the natural rate changes by `−0.25` per quarter, −1 point annualised (`ShockResponses.discount_natRate_falls`, `ShockResponses.discount_natRate_book_numbers`). The text's `∂r^n/∂ε^z = (1 − ρ_z)ε^z` is the change, not the derivative. |
| Exercise 3.5(a), p. 92 | The first-order condition is `∑ E_t[Λ_{t,t+k} Y_{t+k|t}(P* − M Ψ_{t+k})] = 0`. | The objective carries `1/P_{t+k}`, which the printed condition drops. The correct condition is `∑ E_t[Λ_{t,t+k}(1/P_{t+k}) Y_{t+k|t}(P* − M Ψ_{t+k})] = 0` (`Ex3_5.foc_of_isLocalMax`, `Ex3_5.isMaxOn_iff_foc`). Counterexample under perfect foresight: `N = 2`, `ε = 2`, `Λ = C = 1`, `P = (1, 2)`, `Ψ = (1, 2)`. The optimum is `P* = 10/3`, but the printed condition gives `18/5` (`Ex3_5.printed_foc_counterexample`). The two coincide to first order around the zero-inflation steady state, so part (b) is unaffected. |
| Exercise 3.7, (41), p. 95 | The DIS in gaps with the constant `ρ`. | Valid only in part (b), random-walk technology. In part (c) the natural rate moves, `r^n_t = ρ − (1 − ρ_a)a_t` (`Ex3_7.naturalRate_ar1`, `Ex3_7.ar1_equilibrium`). |

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 58 | Iterating (13) forward gives `y_t = σ⁻¹z_t − σ⁻¹∑E_t(r_{t+k} − ρ) + lim E_t y_{t+T}`. | At a finite horizon the shock term is `σ⁻¹(1 − ρ_zᵀ)z_t`. The book's `σ⁻¹z_t` appears only in the limit, which needs `|ρ_z| < 1` (`DIS.euler_forward_ar1`, `DIS.euler_forward_tendsto`). |
| p. 75, fn. 14 | Under the money-supply rule the equilibrium is always determinate. | The book offers only numerical evidence. Proved: the model is equivalent to the `3 × 3` system (34), the eigenvalues of `A_M` are the roots of the characteristic cubic, one eigenvalue exceeds 1, and their product lies in `(0, 1)` (`MoneyRule.isRoot_charpoly_AM_iff`, `MoneyRule.AM_has_eigenvalue_gt_one`, `MoneyRule.det_AM_pos_lt_one`). The full claim, two eigenvalues inside the unit circle, is not yet claimed: it is recorded as `MoneyRule.BookDeterminacyClaim` and scheduled for after both books are finished. |
| App. 3.1, p. 83 | The demand schedule follows from the Lagrangian first-order conditions. | These give necessity at an interior optimum only. Proved instead: spending is at least `P·C` for every allocation, with equality iff the demand schedule holds almost everywhere (`CES.spend_ge`, `CES.spend_eq_iff`). |
| (10), p. 56 | The reset price satisfies (10). | Proved necessary at a local optimum, and with convex costs also sufficient with a unique maximiser, from primitive bounds on discount factors, prices, consumption and costs (`ResetPrice.foc_of_isLocalMax_of_primitives`, `ResetPrice.isMaxOn_iff_foc_of_primitives`). |
| fn. 12, p. 72 | "`ϕ_ya = 1`". | Should read `ψ_ya = 1`; holds at `σ = 1` for every `φ` (`Calibration.psiYA_one_of_sigma_one`). |
| p. 79 | "A comparison with the responses shown in figure 3.2 (... under an interest rate rule)". | The technology shock under the interest-rate rule is figure 3.3. Not formalised (figures). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| p. 55 | `θ ∈ [0, 1)` for the mean duration `1/(1 − θ)` to be finite | `0 ≤ θ`, `θ < 1` (`mean_duration`) |
| p. 65 | "Unique equilibrium" means unique among bounded processes | `BoundedVec`, `ExpectationSystem.Determinate` |
| p. 63 and passim | `E_t` is linear, preserves constants and order, and obeys iterated expectations | `ExpectationSystem`; satisfiable under genuine uncertainty (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`) |
| App. 3.2, p. 84 | Non-resetting firms' prices are distributed like last period's, with mass `θ` (the reset lottery is independent of current prices) | A hypothesis on the firm measure (`CalvoIndex.calvo_recursion`), satisfied by an explicit lottery economy (`CalvoIndex.lottery_model`) |
| App. 3.1, App. 3.4 | Integrability of `P(i)^{1−ε}` and of spending; bounded price deviations | Explicit hypotheses (`CES.spend_ge`, `PriceDispersion.dispersion_second_order`) |
| App. 3.4, p. 86 | "`≃`" in `d_t ≃ (ε/2Θ) var_i p_t(i)` | `O(s³)` along one-parameter families with bounded deviations (`PriceDispersion.dispersion_second_order`) |
| (3), p. 54 | The log-linear Euler equation | Exact under perfect foresight (`Household.pf_eulerEq_imp_eulerLogLinear`); under uncertainty the exact derivative of the nonlinear condition (`Household.hasDerivAt_log_eulerMoment_family`) |
| (29)–(30), p. 66 | `ρ_u ∈ [0, 1)` | `ρ_u < 1` suffices: `Λ_u > 0` under (28) for every `ρ_u < 1` (`TaylorRuleSystem.msvLambda_pos`) |
| (33), p. 74; p. 79; Ex. 3.4(d) | Equations involving `t − 1` | Stated for dates `t ≥ 1` |
