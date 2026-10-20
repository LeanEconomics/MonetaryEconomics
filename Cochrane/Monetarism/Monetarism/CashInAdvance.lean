/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.Expectations
import Monetarism.ExpectationsFiniteTree
import Monetarism.MoneyInUtility
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The cash-in-advance model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.5, pp. 447–455.

Timing convention. `Bin t` and `Min t` are the nominal bonds and money the household brings
*into* date `t` (the book's `B_{t−1}`, `M_{t−1}`); the bonds and the overnight money chosen at
`t` are `Bin (t + 1)` and `Min (t + 1)` (the book's `B_t`, `M_t`). The flow budget (19.27) is
`Bin t + Min t + P_t(y_t − c_t) = Q_t Bin (t+1) + Min (t+1) + P_t s_t`.

## Contents

* **Stochastic present-value budget** (19.27)–(19.30), (19.34)–(19.35) for an arbitrary
  `ExpectationSystem`: from the flow budget and the nominal bond price
  `Λ_t Q_t/P_t = E_t(Λ_{t+1}/P_{t+1})`, the TVC on bonds holds **iff** (19.29) holds, and the TVC
  (19.28) on bonds plus money holds **iff** (19.30) holds. Given (19.28), (19.29) holds iff the
  separate money TVC holds; an explicit path satisfies (19.27), (19.28), (19.30) but violates
  (19.29) (the book's "these conditions imply … two ways" needs the money TVC). The knownness
  lemmas `known_mul`, `known_inv`, `known_div` are `MoneyInUtility`'s, and `telescope` is the
  case `a = 1` of the core `ForwardSolution.iterate_A15`.
* **Money demand by optimisation** (19.33), (19.37), the L-shaped demand of p. 454, and the
  interest-rate sign (E14): the overnight-money choice is a linear programme with an L-shaped
  solution correspondence; `Q > 1` has no optimum.
* **Consumption Euler equation** (19.31)/(19.36) derived from optimality (perfect foresight;
  the problem is `MoneyInUtility.Optimal` without money, `isOptimalPlan_iff_optimal`):
  necessity by a two-date perturbation, sufficiency under concavity; (19.32) with genuine
  uncertainty; E15 (`Q = β` only with a constant price level); the `V ≠ 1` wedge.
* **The household problem on a finite event tree** (`TreeEuler`, genuine uncertainty, infinite
  horizon): node-level Euler necessity, sufficiency under concavity, (19.31) state by state, and
  (19.32) with `Λ_t = β^tu'(y_t)` derived from optimality.
* **Perfect-foresight equilibria** (constant endowment): the frictionless model, the valuation
  (19.38) (corrected to `(B_{t−1} + M_{t−1})/P_t`), uniqueness of the price level (p. 453), the
  worked case `P = (1 − β)B/s`, passive-fiscal indeterminacy; the monetary model, the standard
  equilibrium `P_t = M_tV/y`, the continuum of deflationary equilibria, real-money growth and the
  money TVC, and pruning by an active fiscal policy (pp. 453–454).
-/

namespace Cochrane.Monetarism.CashInAdvance

open Filter Topology

/-! ## Stochastic present-value budget constraint -/

namespace Stochastic

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

open Cochrane.Monetarism.MoneyInUtility (known_mul known_inv known_div)

/-- Cochrane (2023), (19.29)–(19.30), p. 449: the book's discounting `E_t[(Λ_{t+j}/Λ_t) f]`
equals `E_t[Λ_{t+j} f]/Λ_t` when `Λ_t` is known at `t` and positive (pull-out property). -/
theorem E_ratio (hPO : 𝔼.PullOut) {t : ℕ} {Λt Λj f : Ω → ℝ} (hΛ : 𝔼.E t Λt = Λt)
    (hΛ0 : ∀ ω, 0 < Λt ω) :
    𝔼.E t (Λj * f / Λt) = 𝔼.E t (Λj * f) / Λt := by
  have h : Λj * f / Λt = Λt⁻¹ * (Λj * f) := by
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    ring
  rw [h, hPO t _ _ (known_inv 𝔼 hPO hΛ fun ω => (hΛ0 ω).ne')]
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
  ring

/-- Cochrane (2023), (19.27)–(19.30), p. 449: **forward iteration with expectations.** If
`x_t = E_t x_{t+1} + g_t` at every date with `g` adapted, then for every horizon
`x_t = Σ_{j ≤ T} E_t g_{t+j} + E_t x_{t+T+1}` (law of iterated expectations; the case `a = 1`
of the core `ForwardSolution.iterate_A15`). -/
theorem telescope {x g : ℕ → Ω → ℝ} (hrec : ∀ t, x t = 𝔼.E t (x (t + 1)) + g t)
    (hg : ∀ t, 𝔼.E t (g t) = g t) (t : ℕ) :
    ∀ T, x t = ∑ j ∈ Finset.range (T + 1), 𝔼.E t (g (t + j)) + 𝔼.E t (x (t + T + 1)) := by
  intro T
  have hsol : ForwardSolution.Solves 𝔼 1 g x := fun k => by rw [one_smul]; exact hrec k
  have h := ForwardSolution.iterate_A15 𝔼 hg hsol t (T + 1)
  simp only [one_pow, one_smul] at h
  exact h.trans (add_comm _ _)

/-- Cochrane (2023), (19.28)–(19.30), p. 449: **valuation iff transversality** (pointwise in the
state). Under `x_t = E_t x_{t+1} + g_t` with `g` adapted and `j ↦ E_t g_{t+j}(ω)` summable, the
transversality condition `E_t x_{t+T}(ω) → 0` holds iff `x_t(ω) = Σ_j E_t g_{t+j}(ω)`. -/
theorem pv_iff_tvc {x g : ℕ → Ω → ℝ} (hrec : ∀ t, x t = 𝔼.E t (x (t + 1)) + g t)
    (hg : ∀ t, 𝔼.E t (g t) = g t) (t : ℕ) (ω : Ω)
    (hs : Summable fun j => 𝔼.E t (g (t + j)) ω) :
    Tendsto (fun T => 𝔼.E t (x (t + T)) ω) atTop (𝓝 0) ↔
      x t ω = ∑' j, 𝔼.E t (g (t + j)) ω := by
  have hpart : ∀ T, 𝔼.E t (x (t + (T + 1))) ω =
      x t ω - ∑ j ∈ Finset.range (T + 1), 𝔼.E t (g (t + j)) ω := by
    intro T
    have h := congrFun (telescope 𝔼 hrec hg t T) ω
    rw [Pi.add_apply, Finset.sum_apply] at h
    rw [← add_assoc]
    linarith
  have hlim : Tendsto (fun T => ∑ j ∈ Finset.range (T + 1), 𝔼.E t (g (t + j)) ω) atTop
      (𝓝 (∑' j, 𝔼.E t (g (t + j)) ω)) :=
    (tendsto_add_atTop_iff_nat 1).2 hs.hasSum.tendsto_sum_nat
  rw [← tendsto_add_atTop_iff_nat 1]
  simp_rw [hpart]
  constructor
  · intro h
    have h2 := hlim.const_sub (x t ω)
    have := tendsto_nhds_unique h h2
    linarith
  · intro h
    have h2 := hlim.const_sub (x t ω)
    rwa [← h, sub_self] at h2

variable (Λ P Q Bin Min s c y : ℕ → Ω → ℝ)

/-- Cochrane (2023), (19.29), p. 449: the date-`τ` flow in the money-creation form,
`Λ_τ((M_τ − M_{τ−1})/P_τ + s_τ + c_τ − y_τ)` (`M_τ = Min (τ+1)`, `M_{τ−1} = Min τ`). -/
noncomputable def gB : ℕ → Ω → ℝ := fun τ => Λ τ * ((Min (τ + 1) - Min τ) / P τ + s τ + c τ - y τ)

/-- Cochrane (2023), (19.30), p. 449: the date-`τ` flow in the interest-cost form,
`Λ_τ((1 − Q_τ) M_τ/P_τ + s_τ + c_τ − y_τ)`; `1 − Q_τ = i_τ/(1 + i_τ)` (`interest_cost_eq`). -/
noncomputable def gBM : ℕ → Ω → ℝ :=
  fun τ => Λ τ * ((1 - Q τ) * Min (τ + 1) / P τ + s τ + c τ - y τ)

/-- Cochrane (2023), (19.30), p. 449: with `Q = 1/(1 + i)`, `1 − Q = i/(1 + i)`. -/
theorem interest_cost_eq {Qv i : ℝ} (hi : 1 + i ≠ 0) (hQ : Qv = 1 / (1 + i)) :
    1 - Qv = i / (1 + i) := by
  rw [hQ]
  field_simp
  ring

variable {Λ P Q Bin Min s c y}

/-- Cochrane (2023), (19.27), (19.32), p. 449: the flow budget (19.27), multiplied by `Λ_t/P_t`,
with the nominal bond price `Λ_t Q_t/P_t = E_t(Λ_{t+1}/P_{t+1})` and bonds chosen at `t` known
at `t`, gives `Λ_t B_{t−1}/P_t = E_t(Λ_{t+1}B_t/P_{t+1}) + gB_t`. -/
theorem flow_step_B (hPO : 𝔼.PullOut) (hQ : ∀ t, Λ t * Q t / P t = 𝔼.E t (Λ (t + 1) / P (t + 1)))
    (hB : ∀ t, 𝔼.E t (Bin (t + 1)) = Bin (t + 1)) (hP : ∀ t ω, P t ω ≠ 0)
    (hflow : ∀ t, Bin t + Min t + P t * (y t - c t) = Q t * Bin (t + 1) + Min (t + 1) + P t * s t)
    (t : ℕ) :
    Λ t * Bin t / P t = 𝔼.E t (Λ (t + 1) * Bin (t + 1) / P (t + 1)) + gB Λ P Min s c y t := by
  have h1 : Λ (t + 1) * Bin (t + 1) / P (t + 1) = Bin (t + 1) * (Λ (t + 1) / P (t + 1)) := by
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    ring
  rw [h1, hPO t _ _ (hB t), ← hQ t]
  funext ω
  have hf := congrFun (hflow t) ω
  have hPω := hP t ω
  simp only [gB, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply] at hf ⊢
  field_simp
  linear_combination (Λ t ω) * hf

/-- Cochrane (2023), (19.27), (19.30), p. 449: in terms of bonds plus money,
`Λ_t(B_{t−1} + M_{t−1})/P_t = E_t(Λ_{t+1}(B_t + M_t)/P_{t+1}) + gBM_t`: holding money overnight
costs `(1 − Q_t)M_t`. -/
theorem flow_step_BM (hPO : 𝔼.PullOut)
    (hQ : ∀ t, Λ t * Q t / P t = 𝔼.E t (Λ (t + 1) / P (t + 1)))
    (hB : ∀ t, 𝔼.E t (Bin (t + 1)) = Bin (t + 1)) (hM : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1))
    (hP : ∀ t ω, P t ω ≠ 0)
    (hflow : ∀ t, Bin t + Min t + P t * (y t - c t) = Q t * Bin (t + 1) + Min (t + 1) + P t * s t)
    (t : ℕ) :
    Λ t * (Bin t + Min t) / P t =
      𝔼.E t (Λ (t + 1) * (Bin (t + 1) + Min (t + 1)) / P (t + 1)) + gBM Λ P Q Min s c y t := by
  have hBM : 𝔼.E t (Bin (t + 1) + Min (t + 1)) = Bin (t + 1) + Min (t + 1) := by
    rw [map_add, hB t, hM t]
  have h1 : Λ (t + 1) * (Bin (t + 1) + Min (t + 1)) / P (t + 1) =
      (Bin (t + 1) + Min (t + 1)) * (Λ (t + 1) / P (t + 1)) := by
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply]
    ring
  rw [h1, hPO t _ _ hBM, ← hQ t]
  funext ω
  have hf := congrFun (hflow t) ω
  have hPω := hP t ω
  simp only [gBM, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.one_apply] at hf ⊢
  field_simp
  linear_combination (Λ t ω) * hf

/-- Cochrane (2023), §19.5.1, p. 449 (measurability bookkeeping): if the discount factor, the
price level, money, surpluses, consumption and endowment are adapted (money chosen at `t` known at
`t`), the money-creation flow `gB` is adapted. -/
theorem gB_adapted (hPO : 𝔼.PullOut) (hΛ : 𝔼.Adapted Λ) (hPa : 𝔼.Adapted P)
    (hMa : 𝔼.Adapted Min) (hM : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1)) (hs : 𝔼.Adapted s)
    (hc : 𝔼.Adapted c) (hy : 𝔼.Adapted y) (hP : ∀ t ω, P t ω ≠ 0) (t : ℕ) :
    𝔼.E t (gB Λ P Min s c y t) = gB Λ P Min s c y t := by
  have hdiv : 𝔼.E t ((Min (t + 1) - Min t) / P t) = (Min (t + 1) - Min t) / P t :=
    known_div 𝔼 hPO (by rw [map_sub, hM t, hMa t]) (hPa t) (hP t)
  have hin : 𝔼.E t ((Min (t + 1) - Min t) / P t + s t + c t - y t) =
      (Min (t + 1) - Min t) / P t + s t + c t - y t := by
    rw [map_sub, map_add, map_add, hdiv, hs t, hc t, hy t]
  exact known_mul 𝔼 hPO (hΛ t) hin

/-- Cochrane (2023), §19.5.1, p. 449 (measurability bookkeeping): under the same adaptedness
hypotheses (and an adapted bond price), the interest-cost flow `gBM` is adapted. -/
theorem gBM_adapted (hPO : 𝔼.PullOut) (hΛ : 𝔼.Adapted Λ) (hPa : 𝔼.Adapted P)
    (hQa : 𝔼.Adapted Q) (hM : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1)) (hs : 𝔼.Adapted s)
    (hc : 𝔼.Adapted c) (hy : 𝔼.Adapted y) (hP : ∀ t ω, P t ω ≠ 0) (t : ℕ) :
    𝔼.E t (gBM Λ P Q Min s c y t) = gBM Λ P Q Min s c y t := by
  have h1Q : 𝔼.E t (1 - Q t) = 1 - Q t := by
    rw [map_sub, hQa t]
    congr 1
    exact 𝔼.const t 1
  have hdiv : 𝔼.E t ((1 - Q t) * Min (t + 1) / P t) = (1 - Q t) * Min (t + 1) / P t :=
    known_div 𝔼 hPO (known_mul 𝔼 hPO h1Q (hM t)) (hPa t) (hP t)
  have hin : 𝔼.E t ((1 - Q t) * Min (t + 1) / P t + s t + c t - y t) =
      (1 - Q t) * Min (t + 1) / P t + s t + c t - y t := by
    rw [map_sub, map_add, map_add, hdiv, hs t, hc t, hy t]
  exact known_mul 𝔼 hPO (hΛ t) hin

/-- Cochrane (2023), (19.28)–(19.29), p. 449: **present-value budget, seigniorage as money
creation.** Under the flow budget (19.27), the nominal bond price, adaptedness and the pull-out
property, with the flows summable, the bond transversality condition
`E_t[Λ_{t+T} B_{t+T−1}/P_{t+T}] → 0` holds iff
`Λ_t B_{t−1}/P_t = Σ_j E_t[Λ_{t+j}((M_{t+j} − M_{t+j−1})/P_{t+j} + s_{t+j} + c_{t+j} −
y_{t+j})]`. -/
theorem pv_19_29 (hPO : 𝔼.PullOut)
    (hQ : ∀ t, Λ t * Q t / P t = 𝔼.E t (Λ (t + 1) / P (t + 1)))
    (hB : ∀ t, 𝔼.E t (Bin (t + 1)) = Bin (t + 1)) (hP : ∀ t ω, P t ω ≠ 0)
    (hflow : ∀ t, Bin t + Min t + P t * (y t - c t) = Q t * Bin (t + 1) + Min (t + 1) + P t * s t)
    (hΛ : 𝔼.Adapted Λ) (hPa : 𝔼.Adapted P) (hMa : 𝔼.Adapted Min)
    (hM : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1)) (hs : 𝔼.Adapted s) (hc : 𝔼.Adapted c)
    (hy : 𝔼.Adapted y) (t : ℕ) (ω : Ω)
    (hsum : Summable fun j => 𝔼.E t (gB Λ P Min s c y (t + j)) ω) :
    Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bin (t + T) / P (t + T)) ω) atTop (𝓝 0) ↔
      Λ t ω * Bin t ω / P t ω = ∑' j, 𝔼.E t (gB Λ P Min s c y (t + j)) ω :=
  pv_iff_tvc 𝔼 (x := fun τ => Λ τ * Bin τ / P τ) (flow_step_B 𝔼 hPO hQ hB hP hflow)
    (gB_adapted 𝔼 hPO hΛ hPa hMa hM hs hc hy hP) t ω hsum

/-- Cochrane (2023), (19.28), (19.30), p. 449: **present-value budget, seigniorage as interest
saving.** Under the same hypotheses (bond price adapted), the transversality condition (19.28)
`E_t[Λ_{t+T}(B_{t+T−1} + M_{t+T−1})/P_{t+T}] → 0` holds iff
`Λ_t(B_{t−1} + M_{t−1})/P_t = Σ_j E_t[Λ_{t+j}((1 − Q_{t+j})M_{t+j}/P_{t+j} + s + c − y)]`. -/
theorem pv_19_30 (hPO : 𝔼.PullOut)
    (hQ : ∀ t, Λ t * Q t / P t = 𝔼.E t (Λ (t + 1) / P (t + 1)))
    (hB : ∀ t, 𝔼.E t (Bin (t + 1)) = Bin (t + 1)) (hP : ∀ t ω, P t ω ≠ 0)
    (hflow : ∀ t, Bin t + Min t + P t * (y t - c t) = Q t * Bin (t + 1) + Min (t + 1) + P t * s t)
    (hΛ : 𝔼.Adapted Λ) (hPa : 𝔼.Adapted P) (hQa : 𝔼.Adapted Q)
    (hM : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1)) (hs : 𝔼.Adapted s) (hc : 𝔼.Adapted c)
    (hy : 𝔼.Adapted y) (t : ℕ) (ω : Ω)
    (hsum : Summable fun j => 𝔼.E t (gBM Λ P Q Min s c y (t + j)) ω) :
    Tendsto (fun T => 𝔼.E t (Λ (t + T) * (Bin (t + T) + Min (t + T)) / P (t + T)) ω) atTop
        (𝓝 0) ↔
      Λ t ω * (Bin t ω + Min t ω) / P t ω = ∑' j, 𝔼.E t (gBM Λ P Q Min s c y (t + j)) ω :=
  pv_iff_tvc 𝔼 (x := fun τ => Λ τ * (Bin τ + Min τ) / P τ)
    (flow_step_BM 𝔼 hPO hQ hB hM hP hflow) (gBM_adapted 𝔼 hPO hΛ hPa hQa hM hs hc hy hP) t ω hsum

/-- Cochrane (2023), (19.29)–(19.30), p. 449: the book's normalised form. With `Λ_t > 0`,
`x · B/P = S` is the same as `B/P = S/Λ_t`, i.e. `B_{t−1}/P_t = Σ_j E_t[(Λ_{t+j}/Λ_t)(…)]`
(see `E_ratio` for moving `1/Λ_t` inside `E_t`). -/
theorem normalise_iff {Λt X S : ℝ} (hΛt : 0 < Λt) : Λt * X = S ↔ X = S / Λt := by
  constructor
  · intro h
    rw [← h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- Cochrane (2023), (19.28)–(19.30), p. 449: given the transversality condition (19.28) on bonds
plus money, the bond transversality condition behind (19.29) holds **iff** the money
transversality condition `E_t[Λ_{t+T}M_{t+T−1}/P_{t+T}] → 0` holds. -/
theorem tvc_B_iff_money_tvc (t : ℕ) (ω : Ω)
    (hBM : Tendsto (fun T => 𝔼.E t (Λ (t + T) * (Bin (t + T) + Min (t + T)) / P (t + T)) ω)
      atTop (𝓝 0)) :
    Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bin (t + T) / P (t + T)) ω) atTop (𝓝 0) ↔
      Tendsto (fun T => 𝔼.E t (Λ (t + T) * Min (t + T) / P (t + T)) ω) atTop (𝓝 0) := by
  have hsplit : ∀ T, 𝔼.E t (Λ (t + T) * (Bin (t + T) + Min (t + T)) / P (t + T)) ω =
      𝔼.E t (Λ (t + T) * Bin (t + T) / P (t + T)) ω +
        𝔼.E t (Λ (t + T) * Min (t + T) / P (t + T)) ω := by
    intro T
    have h : Λ (t + T) * (Bin (t + T) + Min (t + T)) / P (t + T) =
        Λ (t + T) * Bin (t + T) / P (t + T) + Λ (t + T) * Min (t + T) / P (t + T) := by
      funext ω'
      simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply]
      ring
    rw [h, map_add, Pi.add_apply]
  simp_rw [hsplit] at hBM
  constructor
  · intro h
    have := hBM.sub h
    simp only [add_sub_cancel_left, sub_zero] at this
    exact this
  · intro h
    have := hBM.sub h
    simp only [add_sub_cancel_right, sub_zero] at this
    exact this

/-- Cochrane (2023), (19.27)–(19.30), p. 449: **the two present-value forms are not equivalent
without the money transversality condition.** Perfect foresight, `P ≡ 1`, `Λ_t = 2^{−t}`,
`Q ≡ 1/2` (so `Λ_tQ_t/P_t = Λ_{t+1}/P_{t+1}`), `c = y`, money `M_{t−1} = 2^t`, bonds
`B_{t−1} = −2^t`, surpluses `s_t = −2^t`. The flow (19.27) and the TVC (19.28) hold, every flow
term of (19.29) and (19.30) is zero, so (19.30) holds (`0 = 0`) but (19.29) fails
(`Λ_0B_{−1}/P_0 = −1 ≠ 0`); the money TVC fails (`Λ_tM_{t−1}/P_t = 1`). -/
theorem pv_19_29_needs_money_tvc :
    let Λ : ℕ → ℝ := fun t => (1 / 2) ^ t
    let Min : ℕ → ℝ := fun t => 2 ^ t
    let Bin : ℕ → ℝ := fun t => -2 ^ t
    let s : ℕ → ℝ := fun t => -2 ^ t
    (∀ t, Λ t * (1 / 2) / 1 = Λ (t + 1) / 1) ∧
      (∀ t, Bin t + Min t + 1 * 0 = 1 / 2 * Bin (t + 1) + Min (t + 1) + 1 * s t) ∧
      Tendsto (fun T => Λ T * (Bin T + Min T) / 1) atTop (𝓝 0) ∧
      (∀ τ, Λ τ * ((1 - 1 / 2) * Min (τ + 1) / 1 + s τ + 0) = 0) ∧
      (∀ τ, Λ τ * ((Min (τ + 1) - Min τ) / 1 + s τ + 0) = 0) ∧
      Λ 0 * Bin 0 / 1 ≠ 0 ∧
      ¬ Tendsto (fun T => Λ T * Min T / 1) atTop (𝓝 0) := by
  intro Λ Min Bin s
  have hone : ∀ t : ℕ, (1 / 2 : ℝ) ^ t * 2 ^ t = 1 := by
    intro t
    rw [← mul_pow]
    norm_num
  refine ⟨fun t => ?_, fun t => ?_, ?_, fun τ => ?_, fun τ => ?_, ?_, ?_⟩
  · simp only [Λ, pow_succ]
  · simp only [Bin, Min, s, pow_succ]
    ring
  · have : (fun T => Λ T * (Bin T + Min T) / 1) = fun _ => (0 : ℝ) := by
      funext T
      simp only [Bin, Min]
      ring
    rw [this]
    exact tendsto_const_nhds
  · simp only [Min, s, pow_succ]
    ring
  · simp only [Min, s, pow_succ]
    ring
  · simp only [Λ, Bin]
    norm_num
  · have : (fun T => Λ T * Min T / 1) = fun _ => (1 : ℝ) := by
      funext T
      simp only [Λ, Min, div_one]
      exact hone T
    rw [this]
    intro h
    have := tendsto_nhds_unique tendsto_const_nhds h
    norm_num at this

/-- Cochrane (2023), (19.34), p. 450: with goods-market clearing `c = y` the money-creation flow
is `Λ_τ((M_τ − M_{τ−1})/P_τ + s_τ)`. -/
theorem gB_market_clearing (τ : ℕ) :
    gB Λ P Min s y y τ = Λ τ * ((Min (τ + 1) - Min τ) / P τ + s τ) := by
  funext ω
  simp only [gB, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply]
  ring

/-- Cochrane (2023), (19.35), p. 450: with `c = y` the interest-cost flow is
`Λ_τ((1 − Q_τ)M_τ/P_τ + s_τ) = Λ_τ(i_τ M_τ/((1 + i_τ)P_τ) + s_τ)` (`interest_cost_eq`). -/
theorem gBM_market_clearing (τ : ℕ) :
    gBM Λ P Q Min s y y τ = Λ τ * ((1 - Q τ) * Min (τ + 1) / P τ + s τ) := by
  funext ω
  simp only [gBM, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply]
  ring

/-- Cochrane (2023), (19.32), p. 450: **nominal bond price with genuine uncertainty.** If the
state-price density is `Λ_t = β^t u'(y_t)` (Fact 1, (19.31)) with `u'(y_t) > 0` adapted, the
price level is adapted and positive and `Λ_tQ_t/P_t = E_t(Λ_{t+1}/P_{t+1})`, then
`Q_t = β E_t[(u'(y_{t+1})/u'(y_t))(P_t/P_{t+1})]`. -/
theorem bond_price_19_32 (hPO : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β) {uc : ℕ → Ω → ℝ}
    (huc : ∀ t ω, 0 < uc t ω) (hucA : 𝔼.Adapted uc) (hΛdef : ∀ t, Λ t = β ^ t • uc t)
    (hPa : 𝔼.Adapted P) (hP : ∀ t ω, 0 < P t ω)
    (hQ : ∀ t, Λ t * Q t / P t = 𝔼.E t (Λ (t + 1) / P (t + 1))) (t : ℕ) :
    Q t = β • 𝔼.E t (uc (t + 1) / uc t * (P t / P (t + 1))) := by
  have hΛpos : ∀ ω, Λ t ω ≠ 0 := by
    intro ω
    rw [hΛdef t]
    exact (mul_pos (pow_pos hβ t) (huc t ω)).ne'
  have hΛA : 𝔼.E t (Λ t) = Λ t := by
    rw [hΛdef t, map_smul, hucA t]
  have hk : 𝔼.E t (P t / Λ t) = P t / Λ t :=
    known_div 𝔼 hPO (hPa t) hΛA hΛpos
  have hinner : β • (uc (t + 1) / uc t * (P t / P (t + 1))) =
      P t / Λ t * (Λ (t + 1) / P (t + 1)) := by
    funext ω
    have h1 := (huc t ω).ne'
    have h2 := (hP (t + 1) ω).ne'
    have h3 := (hP t ω).ne'
    have hb := (pow_pos hβ t).ne'
    simp only [hΛdef, Pi.smul_apply, Pi.mul_apply, Pi.div_apply, smul_eq_mul, pow_succ]
    field_simp
  rw [← map_smul, hinner, hPO t _ _ hk, ← hQ t]
  funext ω
  have h3 := (hP t ω).ne'
  have := hΛpos ω
  simp only [Pi.mul_apply, Pi.div_apply]
  field_simp

end Stochastic

/-! ## Money demand: the overnight-money choice -/

namespace MoneyDemand

/-- Cochrane (2023), (19.27), p. 449: the period-`t` nominal cost `Q(W − M) + M` of carrying
nominal wealth `W = B_t + M_t` into the next period as bonds `W − M` (price `Q`) and overnight
money `M`. Given consumption and next-period wealth, this is the only part of the budget (19.27)
that depends on the split between money and bonds. -/
def portfolioCost (Q W M : ℝ) : ℝ := Q * (W - M) + M

/-- Cochrane (2023), (19.24)–(19.26), pp. 448–449: overnight money `M` is optimal when it is
feasible (`M ≥ M_min`, the least money the constraints allow) and minimises the cost of carrying
wealth `W` among feasible choices. -/
def IsOptimalMoney (Q Mmin W M : ℝ) : Prop :=
  Mmin ≤ M ∧ ∀ M', Mmin ≤ M' → portfolioCost Q W M ≤ portfolioCost Q W M'

/-- Cochrane (2023), (19.30), p. 449: the cost is `QW + (1 − Q)M`; `1 − Q = i/(1 + i)` is the
interest cost of money. -/
theorem portfolioCost_eq (Q W M : ℝ) : portfolioCost Q W M = Q * W + (1 - Q) * M := by
  unfold portfolioCost
  ring

/-- Cochrane (2023), (19.33), (19.37), p. 454: **the money-demand correspondence.** `M` is an
optimal overnight money holding iff `Q ≤ 1` (non-negative nominal rate), `M ≥ M_min`, and
`M = M_min` whenever `Q < 1` (positive nominal rate). -/
theorem optimal_iff {Q Mmin W M : ℝ} :
    IsOptimalMoney Q Mmin W M ↔ Q ≤ 1 ∧ Mmin ≤ M ∧ (Q < 1 → M = Mmin) := by
  simp only [IsOptimalMoney, portfolioCost_eq]
  constructor
  · rintro ⟨hM, h⟩
    refine ⟨?_, hM, fun hQ => ?_⟩
    · by_contra hQ
      push Not at hQ
      have := h (M + 1) (by linarith)
      nlinarith
    · have := h Mmin le_rfl
      have : (1 - Q) * (M - Mmin) ≤ 0 := by linarith
      have h2 : M - Mmin ≤ 0 := by
        by_contra h3
        push Not at h3
        have := mul_pos (by linarith : (0 : ℝ) < 1 - Q) h3
        linarith
      linarith
  · rintro ⟨hQ, hM, hb⟩
    refine ⟨hM, fun M' hM' => ?_⟩
    rcases lt_or_eq_of_le hQ with hQ | hQ
    · rw [hb hQ]
      have := mul_le_mul_of_nonneg_left hM' (by linarith : (0 : ℝ) ≤ 1 - Q)
      linarith
    · rw [hQ]
      simp

/-- Cochrane (2023), (19.33), (19.37), pp. 450–452: at a positive nominal rate (`Q < 1`) the
optimal overnight money holding is the minimum the constraints allow. -/
theorem optimal_iff_of_lt_one {Q Mmin W M : ℝ} (hQ : Q < 1) :
    IsOptimalMoney Q Mmin W M ↔ M = Mmin := by
  rw [optimal_iff]
  constructor
  · rintro ⟨-, -, h⟩
    exact h hQ
  · rintro rfl
    exact ⟨hQ.le, le_rfl, fun _ => rfl⟩

/-- Cochrane (2023), p. 454: **the L.** At a zero nominal rate (`Q = 1`) money demand is a
correspondence: every `M ≥ M_min` is optimal. -/
theorem optimal_iff_of_eq_one {Mmin W M : ℝ} : IsOptimalMoney 1 Mmin W M ↔ Mmin ≤ M := by
  rw [optimal_iff]
  constructor
  · rintro ⟨-, h, -⟩
    exact h
  · intro h
    exact ⟨le_rfl, h, fun h1 => absurd h1 (lt_irrefl 1)⟩

/-- Cochrane (2023), pp. 452, 454: at a negative nominal rate (`Q > 1`) the household can lower
its cost without bound by holding more money (and shorting bonds). -/
theorem unbounded_of_one_lt {Q Mmin W : ℝ} (hQ : 1 < Q) (K : ℝ) :
    ∃ M, Mmin ≤ M ∧ portfolioCost Q W M < K := by
  refine ⟨max Mmin ((K - Q * W) / (1 - Q)) + 1, by
    have := le_max_left Mmin ((K - Q * W) / (1 - Q)); linarith, ?_⟩
  have h1 : (K - Q * W) / (1 - Q) < max Mmin ((K - Q * W) / (1 - Q)) + 1 := by
    have := le_max_right Mmin ((K - Q * W) / (1 - Q)); linarith
  rw [div_lt_iff_of_neg (by linarith)] at h1
  rw [portfolioCost_eq]
  linarith

/-- Cochrane (2023), pp. 452–454: **no equilibrium with a negative nominal rate**: for `Q > 1`
there is no optimal money holding. -/
theorem no_optimum_of_one_lt {Q Mmin W M : ℝ} (hQ : 1 < Q) : ¬ IsOptimalMoney Q Mmin W M := by
  rw [optimal_iff]
  rintro ⟨h, -, -⟩
  linarith

/-- Cochrane (2023), (19.24)–(19.25), pp. 448–449: overnight money `M = M^d + P(y − c)` is
feasible for some `M^d` obeying the cash-in-advance constraint `Pc ≤ M^dV` iff
`M ≥ Pc/V + P(y − c)`: the monetary model's minimum overnight money. -/
theorem overnight_feasible_iff {P c y V M : ℝ} (hV : 0 < V) :
    (∃ Md, P * c ≤ Md * V ∧ M = Md + P * (y - c)) ↔ P * c / V + P * (y - c) ≤ M := by
  constructor
  · rintro ⟨Md, h1, rfl⟩
    have : P * c / V ≤ Md := by rw [div_le_iff₀ hV]; exact h1
    linarith
  · intro h
    refine ⟨M - P * (y - c), ?_, by ring⟩
    rw [← div_le_iff₀ hV]
    linarith

/-- Cochrane (2023), (19.24)–(19.25): at the market-clearing allocation `c = y` the monetary
model's minimum overnight money is `Py/V`. -/
theorem overnight_min_clear (P y V : ℝ) : P * y / V + P * (y - y) = P * y / V := by
  ring

/-- Cochrane (2023), (19.33), p. 450, **Fact 2**: in the monetary model with a positive nominal
rate (`Q < 1`) and `c = y`, optimal overnight money satisfies the quantity equation
`M_tV = P_ty_t`. -/
theorem fact2_19_33 {Q P y V W M : ℝ} (hV : 0 < V) (hQ : Q < 1)
    (hopt : IsOptimalMoney Q (P * y / V) W M) : M * V = P * y := by
  rw [(optimal_iff_of_lt_one hQ).1 hopt]
  field_simp

/-- Cochrane (2023), (19.37), p. 452, **frictionless Fact 2**: when money can be returned at
the end of the day the minimum overnight money is `0` (constraint (19.26)), so a positive nominal
rate (`Q < 1`) implies `M_t = 0`. -/
theorem fact_19_37 {Q W M : ℝ} (hQ : Q < 1) (hopt : IsOptimalMoney Q 0 W M) : M = 0 :=
  (optimal_iff_of_lt_one hQ).1 hopt

/-- Cochrane (2023), p. 454: **the L-shaped cash-in-advance money demand.** At `i = 0`
(`Q = 1`) any `M` with `MV ≥ Py` is optimal. -/
theorem L_shaped_demand {P y V W M : ℝ} (hV : 0 < V) :
    IsOptimalMoney 1 (P * y / V) W M ↔ P * y ≤ M * V := by
  rw [optimal_iff_of_eq_one, div_le_iff₀ hV]

/-- Cochrane (2023), pp. 450, 452: with `Q = 1/(1 + i)` and `1 + i > 0`, a positive nominal rate
is `Q < 1`. -/
theorem Q_lt_one_iff {i : ℝ} (hi : 0 < 1 + i) : 1 / (1 + i) < 1 ↔ 0 < i := by
  rw [div_lt_one hi]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 453 (**E14**): the nominal rate is non-negative iff `Q_t ≤ 1` (the book
prints `Q_t ≥ 1`). -/
theorem Q_le_one_iff {i : ℝ} (hi : 0 < 1 + i) : 1 / (1 + i) ≤ 1 ↔ 0 ≤ i := by
  rw [div_le_one hi]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 453 (**E14**): the printed condition `Q_t ≥ 1` says the nominal rate is
non-positive, the opposite of the intended non-negativity. -/
theorem E14_one_le_Q_iff {i : ℝ} (hi : 0 < 1 + i) : 1 ≤ 1 / (1 + i) ↔ i ≤ 0 := by
  rw [le_div_iff₀ hi]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), (19.30), p. 450 (the `V ≠ 1` wedge): at the binding minimum overnight money
`Pc/V + P(y − c)`, the date-`t` terms of the present-value budget (19.30) that involve
consumption are `(1 − Q)(Pc/V + P(y − c)) + P(c − y) = P(1 + (1 − Q)(1/V − 1))c − QPy`: the
effective price of consumption is `1 + (1 − Q)(1/V − 1)` per unit. -/
theorem binding_cost_wedge {P c y V Q : ℝ} (hV : V ≠ 0) :
    (1 - Q) * (P * c / V + P * (y - c)) + P * (c - y) =
      P * (1 + (1 - Q) * (1 / V - 1)) * c - Q * P * y := by
  field_simp
  ring

/-- Cochrane (2023), p. 450 ("cash overnight `M_t` will be unaffected"): the consumption wedge
`1 + (1 − Q)(1/V − 1)` equals `1` iff `Q = 1` (zero rate) or `V = 1`. So the no-distortion
argument for Fact 1 is exact only for `V = 1` (or `i = 0`). -/
theorem wedge_eq_one_iff {Q V : ℝ} (hV : V ≠ 0) :
    1 + (1 - Q) * (1 / V - 1) = 1 ↔ Q = 1 ∨ V = 1 := by
  constructor
  · intro h
    have h' : (1 - Q) * (1 / V - 1) = 0 := by linarith
    rcases mul_eq_zero.1 h' with h1 | h1
    · left; linarith
    · right
      field_simp at h1
      linarith
  · rintro (h | h)
    · rw [h]; ring
    · rw [h]; ring

end MoneyDemand

/-! ## The consumption Euler equation (perfect foresight) -/

namespace Euler

/-- Cochrane (2023), §19.5.1, p. 448: lifetime utility `Σ_t β^t u(c_t)`. -/
noncomputable def lifetimeU (β : ℝ) (u : ℝ → ℝ) (c : ℕ → ℝ) : ℝ := ∑' t, β ^ t * u (c t)

/-- Cochrane (2023), (19.29)–(19.30), p. 449: a consumption plan is admissible when lifetime
utility and the present value `Σ_t p_tc_t` at prices `p` converge absolutely and
`Σ_t p_tc_t ≤ W` (the present-value budget with all non-consumption terms in `W`). -/
def Admissible (β : ℝ) (u : ℝ → ℝ) (p : ℕ → ℝ) (W : ℝ) (c : ℕ → ℝ) : Prop :=
  Summable (fun t => β ^ t * u (c t)) ∧ Summable (fun t => p t * c t) ∧ ∑' t, p t * c t ≤ W

/-- Cochrane (2023), §19.5.1, p. 449: `c` maximises lifetime utility among admissible plans. -/
def IsOptimalPlan (β : ℝ) (u : ℝ → ℝ) (p : ℕ → ℝ) (W : ℝ) (c : ℕ → ℝ) : Prop :=
  Admissible β u p W c ∧ ∀ c', Admissible β u p W c' → lifetimeU β u c' ≤ lifetimeU β u c

/-- Cochrane (2023), §19.5.1, p. 449, and footnote 1, p. 440: the consumption-only problem is the
money-in-utility time-0 problem `MoneyInUtility.Optimal` with utility independent of money and
a zero cost of money (`ι = 0`, `m = 0`), so the two-date perturbation machinery of
`MoneyInUtility` applies. -/
theorem isOptimalPlan_iff_optimal {β : ℝ} {u : ℝ → ℝ} {p : ℕ → ℝ} {W : ℝ} {c : ℕ → ℝ} :
    IsOptimalPlan β u p W c ↔
      MoneyInUtility.Optimal β (fun x _ => u x) p (fun _ => 0) W c (fun _ => 0) := by
  simp only [IsOptimalPlan, Admissible, lifetimeU, MoneyInUtility.Optimal,
    MoneyInUtility.Feasible, zero_mul, add_zero]
  constructor
  · rintro ⟨⟨hu, hs, hW⟩, hmax⟩
    exact ⟨⟨hs, hW⟩, hu, fun c' _ hf hu' => hmax c' ⟨hu', hf.1, hf.2⟩⟩
  · rintro ⟨⟨hs, hW⟩, hu, hmax⟩
    exact ⟨⟨hu, hs, hW⟩, fun c' hc' => hmax c' (fun _ => 0) ⟨hc'.2.1, hc'.2.2⟩ hc'.1⟩

/-- Cochrane (2023), (19.31), p. 450, **Fact 1, necessity**: at an optimal plan the marginal
rate of substitution between any two dates equals the price ratio:
`β^t u'(c_t) p_s = β^s u'(c_s) p_t` (perturb `c_t` by `εp_s` and `c_s` by `−εp_t`, at constant
cost, with `MoneyInUtility.perturb_le`). -/
theorem euler_necessary {β : ℝ} {u : ℝ → ℝ} {p c : ℕ → ℝ} {W : ℝ}
    (hopt : IsOptimalPlan β u p W c) {t s : ℕ} (hts : t ≠ s) {d1 d2 : ℝ}
    (h1 : HasDerivAt u d1 (c t)) (h2 : HasDerivAt u d2 (c s)) :
    β ^ t * d1 * p s = β ^ s * d2 * p t := by
  have hopt' := isOptimalPlan_iff_optimal.mp hopt
  set D : ℝ → ℝ := fun ε => β ^ t * u (c t + ε * p s) + β ^ s * u (c s - ε * p t) with hD
  have hle : ∀ ε, D ε ≤ D 0 := by
    intro ε
    have := MoneyInUtility.perturb_le (c' := Function.update (Function.update c t
      (c t + ε * p s)) s (c s - ε * p t)) (m' := fun _ => 0) hopt' hts (fun k hkt hks => by
        simp [Function.update_of_ne hks, Function.update_of_ne hkt]) (fun _ _ _ => rfl)
      (by simp [Function.update_of_ne hts]; ring)
    simpa [hD, Function.update_of_ne hts, Function.update_of_ne hts.symm] using this
  have hd1 : HasDerivAt (fun ε => c t + ε * p s) (p s) 0 := by
    simpa using (hasDerivAt_mul_const (p s)).const_add (c t)
  have hd2 : HasDerivAt (fun ε => c s - ε * p t) (-p t) 0 := by
    simpa using (hasDerivAt_mul_const (p t)).const_sub (c s)
  have hu1 : HasDerivAt (fun ε => u (c t + ε * p s)) (d1 * p s) 0 :=
    HasDerivAt.comp_of_eq 0 h1 hd1 (by simp)
  have hu2 : HasDerivAt (fun ε => u (c s - ε * p t)) (d2 * -p t) 0 :=
    HasDerivAt.comp_of_eq 0 h2 hd2 (by simp)
  have hDd : HasDerivAt D (β ^ t * (d1 * p s) + β ^ s * (d2 * -p t)) 0 :=
    (hu1.const_mul _).add (hu2.const_mul _)
  have hmax : IsLocalMax D 0 := Filter.Eventually.of_forall hle
  have := hmax.hasDerivAt_eq_zero hDd
  linarith

/-- Cochrane (2023), §19.5.4, p. 453 ("first order conditions and transversality conditions are
necessary and sufficient"), **sufficiency**: if `u` lies below its tangent lines at the plan
(`u x ≤ u(c_τ) + u'_τ(x − c_τ)`, concavity), the first-order conditions
`β^τ u'_τ = λp_τ` hold with `λ ≥ 0`, `β ≥ 0`, and the budget binds, then the plan is optimal. -/
theorem euler_sufficient {β : ℝ} {u : ℝ → ℝ} {p c du : ℕ → ℝ} {W lam : ℝ} (hβ : 0 ≤ β)
    (hlam : 0 ≤ lam) (hconc : ∀ τ x, u x ≤ u (c τ) + du τ * (x - c τ))
    (hfoc : ∀ τ, β ^ τ * du τ = lam * p τ) (hadm : Admissible β u p W c)
    (hbind : ∑' τ, p τ * c τ = W) : IsOptimalPlan β u p W c := by
  refine ⟨hadm, fun c' hc' => ?_⟩
  have hle : ∀ τ, β ^ τ * u (c' τ) - β ^ τ * u (c τ) ≤ lam * (p τ * c' τ - p τ * c τ) := by
    intro τ
    have h := mul_le_mul_of_nonneg_left (hconc τ (c' τ)) (pow_nonneg hβ τ)
    have : lam * (p τ * c' τ - p τ * c τ) = β ^ τ * du τ * (c' τ - c τ) := by
      rw [hfoc τ]
      ring
    rw [this]
    nlinarith
  have hs1 : Summable (fun τ => β ^ τ * u (c' τ) - β ^ τ * u (c τ)) := hc'.1.sub hadm.1
  have hs2 : Summable (fun τ => lam * (p τ * c' τ - p τ * c τ)) :=
    (hc'.2.1.sub hadm.2.1).mul_left lam
  have htot := hs1.tsum_le_tsum hle hs2
  rw [hc'.1.tsum_sub hadm.1, tsum_mul_left, hc'.2.1.tsum_sub hadm.2.1] at htot
  unfold lifetimeU
  have : lam * (∑' τ, p τ * c' τ - ∑' τ, p τ * c τ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam (by rw [hbind]; linarith [hc'.2.2])
  linarith

/-- Cochrane (2023), (19.31), p. 450 and (19.36), p. 452, **Fact 1**: if consuming the endowment
`y` is optimal at the state prices `Λ > 0` and `u'(y_t) ≠ 0` (and `β > 0`), then
`β^j u'(y_{t+j})/u'(y_t) = Λ_{t+j}/Λ_t`. -/
theorem sdf_19_31 {β : ℝ} {u : ℝ → ℝ} {Λ y du : ℕ → ℝ} {W : ℝ} (hβ : 0 < β)
    (hopt : IsOptimalPlan β u Λ W y) (hΛ : ∀ t, 0 < Λ t)
    (hdu : ∀ t, HasDerivAt u (du t) (y t)) (hdu0 : ∀ t, du t ≠ 0) (t j : ℕ) :
    β ^ j * du (t + j) / du t = Λ (t + j) / Λ t := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have := hdu0 t
    have := (hΛ t).ne'
    simp only [pow_zero, one_mul, add_zero]
    field_simp
  · have h := euler_necessary hopt (s := t + j) (by omega) (hdu t) (hdu (t + j))
    have := hdu0 t
    have := (hΛ t).ne'
    rw [pow_add] at h
    have hb : β ^ t ≠ 0 := (pow_pos hβ t).ne'
    rw [div_eq_div_iff (hdu0 t) (hΛ t).ne']
    have := mul_left_cancel₀ hb (by linear_combination h :
      β ^ t * (du t * Λ (t + j)) = β ^ t * (β ^ j * du (t + j) * Λ t))
    linarith

/-- Cochrane (2023), p. 450 and (19.36), p. 452: with a constant endowment, `Λ_{t+j}/Λ_t = β^j`. -/
theorem sdf_const_endowment {β : ℝ} {u : ℝ → ℝ} {Λ : ℕ → ℝ} {W ybar d : ℝ} (hβ : 0 < β)
    (hopt : IsOptimalPlan β u Λ W (fun _ => ybar)) (hΛ : ∀ t, 0 < Λ t)
    (hdu : HasDerivAt u d ybar) (hd0 : d ≠ 0) (t j : ℕ) :
    Λ (t + j) / Λ t = β ^ j := by
  have := sdf_19_31 (du := fun _ => d) hβ hopt hΛ (fun _ => hdu) (fun _ => hd0) t j
  rw [← this]
  field_simp

/-- Cochrane (2023), p. 450 (the `V ≠ 1` wedge): if consuming a constant endowment is optimal at
the effective consumption prices `Λ_tw_t` (`w_t = 1 + (1 − Q_t)(1/V − 1)`,
`MoneyDemand.binding_cost_wedge`), then `Λ_{t+1}/Λ_t = βw_t/w_{t+1}`; this equals `β` iff
`w_t = w_{t+1}`, which holds for `V = 1` (`MoneyDemand.wedge_eq_one_iff`) but not in general. -/
theorem sdf_wedge {β : ℝ} {u : ℝ → ℝ} {Λ w : ℕ → ℝ} {W ybar d : ℝ} (hβ : 0 < β)
    (hopt : IsOptimalPlan β u (fun t => Λ t * w t) W (fun _ => ybar)) (hΛ : ∀ t, 0 < Λ t)
    (hw : ∀ t, 0 < w t) (hdu : HasDerivAt u d ybar) (hd0 : d ≠ 0) (t : ℕ) :
    Λ (t + 1) / Λ t = β * w t / w (t + 1) := by
  have h := sdf_const_endowment hβ hopt (fun t => mul_pos (hΛ t) (hw t)) hdu hd0 t 1
  have := (hΛ t).ne'
  have := (hw t).ne'
  have := (hw (t + 1)).ne'
  simp only [pow_one] at h
  field_simp at h ⊢
  linear_combination h

end Euler

/-! ## The household problem on a finite event tree (genuine uncertainty) -/

namespace TreeEuler

open ExpectationsFiniteTree

variable {Ω : Type*} [Fintype Ω] (T : FiniteTree Ω)

/-- Cochrane (2023), §19.5.1, p. 448: a plan is measurable (date-`t` choices depend only on the
date-`t` information cell of the event tree). -/
def Meas (x : ℕ → Ω → ℝ) : Prop := ∀ t ω ω', T.info t ω ω' → x t ω = x t ω'

/-- Cochrane (2023), §19.5.1, p. 448: expected lifetime utility `E Σ_t β^t u(c_t)`. -/
noncomputable def expU (β : ℝ) (u : ℝ → ℝ) (c : ℕ → Ω → ℝ) : ℝ :=
  ∑' t, β ^ t * ∑ ω, T.prob ω * u (c t ω)

/-- Cochrane (2023), (19.30), p. 449: the date-`t` present-value cost `E[Λ_tc_t]` of a
consumption plan at the state-price density `Λ`. -/
noncomputable def pvCost (Λ c : ℕ → Ω → ℝ) (t : ℕ) : ℝ := ∑ ω, T.prob ω * (Λ t ω * c t ω)

/-- Cochrane (2023), (19.24)–(19.30), pp. 448–449: **the cash-in-advance household's problem
on an event tree, present-value form.** With `V = 1` the binding overnight money
`Pc + P(y − c) = Py` does not depend on consumption (`cia_min_V1`), so, money and bonds chosen
optimally, the budget (19.30) — equivalent to the flow budget (19.27) plus the TVC (19.28) by
`Stochastic.pv_19_30` — reads `Σ_t E[Λ_tc_t] ≤ W` with every other term in `W`. A plan is
admissible when it is measurable, expected utility and present value converge absolutely, and
the budget holds. -/
def Admissible (β : ℝ) (u : ℝ → ℝ) (Λ : ℕ → Ω → ℝ) (W : ℝ) (c : ℕ → Ω → ℝ) : Prop :=
  Meas T c ∧ Summable (fun t => β ^ t * ∑ ω, T.prob ω * u (c t ω)) ∧
    Summable (pvCost T Λ c) ∧ ∑' t, pvCost T Λ c t ≤ W

/-- Cochrane (2023), §19.5.1, p. 449: `c` maximises expected utility among admissible plans. -/
def IsOptimal (β : ℝ) (u : ℝ → ℝ) (Λ : ℕ → Ω → ℝ) (W : ℝ) (c : ℕ → Ω → ℝ) : Prop :=
  Admissible T β u Λ W c ∧ ∀ c', Admissible T β u Λ W c' → expU T β u c' ≤ expU T β u c

/-- Cochrane (2023), (19.24)–(19.25), p. 448: with `V = 1` the minimum overnight money
`Pc/V + P(y − c)` is `Py`, independent of consumption (no monetary wedge, cf.
`MoneyDemand.wedge_eq_one_iff`). -/
theorem cia_min_V1 (P c y : ℝ) : P * c / 1 + P * (y - c) = P * y := by ring

/-- Cochrane (2023), (19.31), p. 450, **Fact 1 under uncertainty, necessity**: at an optimal
plan, for any two nodes `(t, ω₀)` and `(s, ω₁)` with `t ≠ s`,
`β^t u'(c_t(ω₀)) Λ_s(ω₁) = β^s u'(c_s(ω₁)) Λ_t(ω₀)` (state prices measurable and positive). The
proof raises consumption by `ε` on the date-`t` information cell of `ω₀` and lowers it on the
date-`s` cell of `ω₁` by the amount that leaves the present value unchanged. -/
theorem euler_necessary {β : ℝ} {u : ℝ → ℝ} {Λ c : ℕ → Ω → ℝ} {W : ℝ}
    (hopt : IsOptimal T β u Λ W c) (hΛm : Meas T Λ) (hΛ : ∀ t ω, 0 < Λ t ω)
    {t s : ℕ} (hts : t ≠ s) (ω₀ ω₁ : Ω) {d1 d2 : ℝ}
    (h1 : HasDerivAt u d1 (c t ω₀)) (h2 : HasDerivAt u d2 (c s ω₁)) :
    β ^ t * d1 * Λ s ω₁ = β ^ s * d2 * Λ t ω₀ := by
  classical
  have hcm := hopt.1.1
  have hmA := T.mass_pos t ω₀
  have hmB := T.mass_pos s ω₁
  have hΛA := hΛ t ω₀
  have hΛB := hΛ s ω₁
  set k := T.mass t ω₀ * Λ t ω₀ / (T.mass s ω₁ * Λ s ω₁) with hk
  -- the cell-perturbation identity (`MoneyInUtility.FootnoteTree.sum_perturb_cell`)
  have key : ∀ (r : ℕ) (ω₂ : Ω) (a : ℝ) (F : Ω → ℝ → ℝ),
      (∀ ω, T.info r ω ω₂ → F ω = F ω₂) →
      ∑ ω, T.prob ω * F ω (if T.info r ω ω₂ then a else 0) - ∑ ω, T.prob ω * F ω 0 =
        T.mass r ω₂ * (F ω₂ a - F ω₂ 0) := by
    intro r ω₂ a F hF
    have h := MoneyInUtility.FootnoteTree.sum_perturb_cell T (t := r) (ω0 := ω₂) F
      (fun _ => 0) (fun _ _ => rfl) hF a
    have e : ∀ ω, (if T.info r ω ω₂ then a else 0) =
        0 + a * MoneyInUtility.FootnoteTree.cell T r ω₂ ω := by
      intro ω
      unfold MoneyInUtility.FootnoteTree.cell
      split_ifs <;> simp
    simp only [e]
    simp only [zero_add] at h ⊢
    linarith
  let pert : ℝ → ℕ → Ω → ℝ := fun ε τ ω =>
    c τ ω + (if τ = t ∧ T.info t ω ω₀ then ε else 0) +
      (if τ = s ∧ T.info s ω ω₁ then -(ε * k) else 0)
  have hpt : ∀ ε ω, pert ε t ω = c t ω + (if T.info t ω ω₀ then ε else 0) := by
    intro ε ω
    simp [pert, hts]
  have hps : ∀ ε ω, pert ε s ω = c s ω + (if T.info s ω ω₁ then -(ε * k) else 0) := by
    intro ε ω
    simp [pert, Ne.symm hts]
  have hpo : ∀ ε τ ω, τ ≠ t → τ ≠ s → pert ε τ ω = c τ ω := by
    intro ε τ ω h1 h2
    simp [pert, h1, h2]
  -- the perturbed plan is measurable
  have hmeas : ∀ ε, Meas T (pert ε) := by
    intro ε τ ω ω' h
    have e1 : (τ = t ∧ T.info t ω ω₀) ↔ (τ = t ∧ T.info t ω' ω₀) := by
      constructor <;> rintro ⟨rfl, h'⟩ <;> refine ⟨rfl, ?_⟩
      · exact (T.info τ).trans ((T.info τ).symm h) h'
      · exact (T.info τ).trans h h'
    have e2 : (τ = s ∧ T.info s ω ω₁) ↔ (τ = s ∧ T.info s ω' ω₁) := by
      constructor <;> rintro ⟨rfl, h'⟩ <;> refine ⟨rfl, ?_⟩
      · exact (T.info τ).trans ((T.info τ).symm h) h'
      · exact (T.info τ).trans h h'
    simp only [pert]
    rw [hcm τ ω ω' h, if_congr e1 rfl rfl, if_congr e2 rfl rfl]
  -- cost differences, date by date
  have hcostt : ∀ ε, pvCost T Λ (pert ε) t - pvCost T Λ c t = T.mass t ω₀ * (Λ t ω₀ * ε) := by
    intro ε
    unfold pvCost
    simp only [hpt]
    have := key t ω₀ ε (fun ω x => Λ t ω * (c t ω + x)) (fun ω h => by
      funext x; simp only [hΛm t ω ω₀ h, hcm t ω ω₀ h])
    simp only [add_zero] at this
    rw [this]
    ring
  have hcosts : ∀ ε, pvCost T Λ (pert ε) s - pvCost T Λ c s =
      T.mass s ω₁ * (Λ s ω₁ * -(ε * k)) := by
    intro ε
    unfold pvCost
    simp only [hps]
    have := key s ω₁ (-(ε * k)) (fun ω x => Λ s ω * (c s ω + x)) (fun ω h => by
      funext x; simp only [hΛm s ω ω₁ h, hcm s ω ω₁ h])
    simp only [add_zero] at this
    rw [this]
    ring
  have hcosto : ∀ ε τ, τ ∉ ({t, s} : Finset ℕ) → pvCost T Λ (pert ε) τ - pvCost T Λ c τ = 0 := by
    intro ε τ hτ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hτ
    unfold pvCost
    simp only [hpo ε τ _ hτ.1 hτ.2, sub_self]
  -- utility differences, date by date
  let φ : ℝ → ℝ := fun ε => β ^ t * (T.mass t ω₀ * u (c t ω₀ + ε)) +
    β ^ s * (T.mass s ω₁ * u (c s ω₁ + -(ε * k)))
  have hut : ∀ ε, β ^ t * ∑ ω, T.prob ω * u (pert ε t ω) - β ^ t * ∑ ω, T.prob ω * u (c t ω) =
      β ^ t * (T.mass t ω₀ * (u (c t ω₀ + ε) - u (c t ω₀))) := by
    intro ε
    simp only [hpt]
    have := key t ω₀ ε (fun ω x => u (c t ω + x)) (fun ω h => by
      funext x; simp only [hcm t ω ω₀ h])
    simp only [add_zero] at this
    rw [← mul_sub, this]
  have hus : ∀ ε, β ^ s * ∑ ω, T.prob ω * u (pert ε s ω) - β ^ s * ∑ ω, T.prob ω * u (c s ω) =
      β ^ s * (T.mass s ω₁ * (u (c s ω₁ + -(ε * k)) - u (c s ω₁))) := by
    intro ε
    simp only [hps]
    have := key s ω₁ (-(ε * k)) (fun ω x => u (c s ω + x)) (fun ω h => by
      funext x; simp only [hcm s ω ω₁ h])
    simp only [add_zero] at this
    rw [← mul_sub, this]
  have huo : ∀ ε τ, τ ∉ ({t, s} : Finset ℕ) →
      β ^ τ * ∑ ω, T.prob ω * u (pert ε τ ω) - β ^ τ * ∑ ω, T.prob ω * u (c τ ω) = 0 := by
    intro ε τ hτ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hτ
    simp only [hpo ε τ _ hτ.1 hτ.2, sub_self]
  -- admissibility and value of the perturbed plan
  have hadm : ∀ ε, Admissible T β u Λ W (pert ε) := by
    intro ε
    have hsd : Summable (fun τ => pvCost T Λ (pert ε) τ - pvCost T Λ c τ) :=
      summable_of_ne_finset_zero (hcosto ε)
    have hsum0 : ∑' τ, (pvCost T Λ (pert ε) τ - pvCost T Λ c τ) = 0 := by
      rw [tsum_eq_sum (hcosto ε), Finset.sum_pair hts, hcostt, hcosts, hk]
      field_simp
      ring
    have hud : Summable (fun τ => β ^ τ * ∑ ω, T.prob ω * u (pert ε τ ω) -
        β ^ τ * ∑ ω, T.prob ω * u (c τ ω)) := summable_of_ne_finset_zero (huo ε)
    refine ⟨hmeas ε, (hud.add hopt.1.2.1).congr fun τ => by ring,
      (hsd.add hopt.1.2.2.1).congr fun τ => by ring, ?_⟩
    have h := hsd.tsum_add hopt.1.2.2.1
    rw [show (fun τ => pvCost T Λ (pert ε) τ) =
        fun τ => (pvCost T Λ (pert ε) τ - pvCost T Λ c τ) + pvCost T Λ c τ from
          funext fun τ => by ring, h, hsum0, zero_add]
    exact hopt.1.2.2.2
  have hval : ∀ ε, expU T β u (pert ε) = expU T β u c + (φ ε - φ 0) := by
    intro ε
    have hud : Summable (fun τ => β ^ τ * ∑ ω, T.prob ω * u (pert ε τ ω) -
        β ^ τ * ∑ ω, T.prob ω * u (c τ ω)) := summable_of_ne_finset_zero (huo ε)
    have hsum : ∑' τ, (β ^ τ * ∑ ω, T.prob ω * u (pert ε τ ω) -
        β ^ τ * ∑ ω, T.prob ω * u (c τ ω)) = φ ε - φ 0 := by
      rw [tsum_eq_sum (huo ε), Finset.sum_pair hts, hut, hus]
      simp only [φ, add_zero, zero_mul, neg_zero]
      ring
    unfold expU
    rw [show (fun τ => β ^ τ * ∑ ω, T.prob ω * u (pert ε τ ω)) =
        fun τ => (β ^ τ * ∑ ω, T.prob ω * u (pert ε τ ω) -
          β ^ τ * ∑ ω, T.prob ω * u (c τ ω)) + β ^ τ * ∑ ω, T.prob ω * u (c τ ω) from
          funext fun τ => by ring, hud.tsum_add hopt.1.2.1, hsum]
    ring
  have hmax : IsLocalMax φ 0 := Filter.Eventually.of_forall fun ε => by
    have := hopt.2 (pert ε) (hadm ε)
    rw [hval ε] at this
    linarith
  have hd1 : HasDerivAt (fun ε => β ^ t * (T.mass t ω₀ * u (c t ω₀ + ε)))
      (β ^ t * (T.mass t ω₀ * d1)) 0 :=
    ((HasDerivAt.comp_const_add (c t ω₀) 0 (by simpa using h1)).const_mul _).const_mul _
  have hin : HasDerivAt (fun ε : ℝ => c s ω₁ + -(ε * k)) (-(1 * k)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const k).neg).const_add (c s ω₁)
  have h2' : HasDerivAt u d2 (c s ω₁ + -(0 * k)) := by simpa using h2
  have hd2 : HasDerivAt (fun ε => β ^ s * (T.mass s ω₁ * u (c s ω₁ + -(ε * k))))
      (β ^ s * (T.mass s ω₁ * (d2 * -(1 * k)))) 0 :=
    ((h2'.comp 0 hin).const_mul _).const_mul _
  have hder := hmax.hasDerivAt_eq_zero (HasDerivAt.add hd1 hd2)
  rw [hk] at hder
  field_simp at hder
  have hmA' := hmA.ne'
  have := mul_left_cancel₀ hmA' (by linear_combination hder :
    T.mass t ω₀ * (β ^ t * d1 * Λ s ω₁) = T.mass t ω₀ * (β ^ s * d2 * Λ t ω₀))
  exact this

/-- Cochrane (2023), p. 453 ("first order conditions and transversality conditions are
necessary and sufficient"), **sufficiency under uncertainty**: if `u` lies below its tangent
lines at the plan, the node-by-node first-order conditions `β^τ u'(c_τ(ω)) = λΛ_τ(ω)` hold with
`λ ≥ 0`, `β ≥ 0`, and the present-value budget (which embodies the TVC, `Stochastic.pv_19_30`)
binds, then the plan is optimal. -/
theorem euler_sufficient {β : ℝ} {u : ℝ → ℝ} {Λ c du : ℕ → Ω → ℝ} {W lam : ℝ} (hβ : 0 ≤ β)
    (hlam : 0 ≤ lam) (hconc : ∀ τ ω x, u x ≤ u (c τ ω) + du τ ω * (x - c τ ω))
    (hfoc : ∀ τ ω, β ^ τ * du τ ω = lam * Λ τ ω) (hadm : Admissible T β u Λ W c)
    (hbind : ∑' τ, pvCost T Λ c τ = W) : IsOptimal T β u Λ W c := by
  refine ⟨hadm, fun c' hc' => ?_⟩
  have hle : ∀ τ, β ^ τ * ∑ ω, T.prob ω * u (c' τ ω) - β ^ τ * ∑ ω, T.prob ω * u (c τ ω) ≤
      lam * (pvCost T Λ c' τ - pvCost T Λ c τ) := by
    intro τ
    unfold pvCost
    rw [← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    have hp := (T.prob_pos ω).le
    have h := hconc τ ω (c' τ ω)
    have hb := pow_nonneg hβ τ
    have e : lam * (T.prob ω * (Λ τ ω * c' τ ω) - T.prob ω * (Λ τ ω * c τ ω)) =
        T.prob ω * (β ^ τ * du τ ω * (c' τ ω - c τ ω)) := by
      rw [hfoc τ ω]
      ring
    rw [e]
    have h2 : β ^ τ * (u (c' τ ω) - u (c τ ω)) ≤ β ^ τ * du τ ω * (c' τ ω - c τ ω) := by
      have := mul_le_mul_of_nonneg_left h hb
      nlinarith
    have := mul_le_mul_of_nonneg_left h2 hp
    nlinarith
  have hs1 := hc'.2.1.sub hadm.2.1
  have hs2 := (hc'.2.2.1.sub hadm.2.2.1).mul_left lam
  have htot := hs1.tsum_le_tsum hle hs2
  rw [hc'.2.1.tsum_sub hadm.2.1, tsum_mul_left, hc'.2.2.1.tsum_sub hadm.2.2.1] at htot
  unfold expU
  have : lam * (∑' τ, pvCost T Λ c' τ - ∑' τ, pvCost T Λ c τ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam (by rw [hbind]; linarith [hc'.2.2.2])
  linarith

/-- Cochrane (2023), (19.31), p. 450, **Fact 1 under uncertainty**: if consuming the endowment
`y` is optimal at the state-price density `Λ > 0` (measurable), `β > 0` and `u'(y_t(ω)) ≠ 0`, then
state by state `Λ_{t+j}(ω)/Λ_t(ω) = β^j u'(y_{t+j}(ω))/u'(y_t(ω))`. -/
theorem sdf_19_31 {β : ℝ} {u : ℝ → ℝ} {Λ y uc : ℕ → Ω → ℝ} {W : ℝ} (hβ : 0 < β)
    (hopt : IsOptimal T β u Λ W y) (hΛm : Meas T Λ) (hΛ : ∀ t ω, 0 < Λ t ω)
    (hdu : ∀ t ω, HasDerivAt u (uc t ω) (y t ω)) (huc : ∀ t ω, uc t ω ≠ 0) (t j : ℕ) (ω : Ω) :
    Λ (t + j) ω / Λ t ω = β ^ j * uc (t + j) ω / uc t ω := by
  have h0 := (hΛ t ω).ne'
  have h1 := huc t ω
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [add_zero, pow_zero, one_mul]
    rw [div_self h0, div_self h1]
  · have h := euler_necessary T hopt hΛm hΛ (t := t) (s := t + j) (by omega) ω ω
      (hdu t ω) (hdu (t + j) ω)
    rw [pow_add] at h
    have hb : β ^ t ≠ 0 := (pow_pos hβ t).ne'
    rw [div_eq_div_iff h0 h1]
    have := mul_left_cancel₀ hb (by linear_combination h :
      β ^ t * (uc t ω * Λ (t + j) ω) = β ^ t * (β ^ j * uc (t + j) ω * Λ t ω))
    linarith

/-- Cochrane (2023), (19.31), p. 450: with the normalisation `Λ_0 = u'(y_0)` (state prices are
defined up to scale), optimality of `y` gives `Λ_t = β^t u'(y_t)` at every node. -/
theorem sdf_eq {β : ℝ} {u : ℝ → ℝ} {Λ y uc : ℕ → Ω → ℝ} {W : ℝ} (hβ : 0 < β)
    (hopt : IsOptimal T β u Λ W y) (hΛm : Meas T Λ) (hΛ : ∀ t ω, 0 < Λ t ω)
    (hdu : ∀ t ω, HasDerivAt u (uc t ω) (y t ω)) (huc : ∀ t ω, uc t ω ≠ 0)
    (hnorm : Λ 0 = uc 0) (t : ℕ) : Λ t = β ^ t • uc t := by
  funext ω
  have h := sdf_19_31 T hβ hopt hΛm hΛ hdu huc 0 t ω
  rw [zero_add, hnorm] at h
  have := huc 0 ω
  rw [div_eq_div_iff this this] at h
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_right_cancel₀ this (by linarith)

/-- Cochrane (2023), (19.32), p. 450, **bond price from household optimality under
uncertainty**: on a finite event tree, if consuming the endowment is optimal at state prices
`Λ` (normalised `Λ_0 = u'(y_0)`), `u'(y) > 0`, the price level is adapted and positive and the
nominal bond price is `Λ_tQ_t/P_t = E_t(Λ_{t+1}/P_{t+1})`, then
`Q_t = βE_t[(u'(y_{t+1})/u'(y_t))(P_t/P_{t+1})]`; `Λ_t = β^tu'(y_t)` is derived (`sdf_eq`),
not assumed. -/
theorem bond_price_from_optimality {β : ℝ} {u : ℝ → ℝ} {Λ y uc P Q : ℕ → Ω → ℝ} {W : ℝ}
    (hβ : 0 < β) (hopt : IsOptimal T β u Λ W y) (hΛm : Meas T Λ) (hΛ : ∀ t ω, 0 < Λ t ω)
    (hdu : ∀ t ω, HasDerivAt u (uc t ω) (y t ω)) (huc : ∀ t ω, 0 < uc t ω)
    (hnorm : Λ 0 = uc 0) (hPa : T.toExpectationSystem.Adapted P) (hP : ∀ t ω, 0 < P t ω)
    (hQ : ∀ t, Λ t * Q t / P t = T.toExpectationSystem.E t (Λ (t + 1) / P (t + 1))) (t : ℕ) :
    Q t = β • T.toExpectationSystem.E t (uc (t + 1) / uc t * (P t / P (t + 1))) := by
  have hucA : T.toExpectationSystem.Adapted uc := by
    intro τ
    rw [FiniteTree.toExpectationSystem_E]
    funext ω
    refine T.condE_of_const_on_cell fun ω' h => ?_
    have hy : y τ ω' = y τ ω := hopt.1.1 τ ω' ω h
    have h1 := hdu τ ω'
    rw [hy] at h1
    exact h1.unique (hdu τ ω)
  exact Stochastic.bond_price_19_32 T.toExpectationSystem (finiteTree_pullOut T) hβ huc hucA
    (sdf_eq T hβ hopt hΛm hΛ hdu (fun t ω => (huc t ω).ne') hnorm) hPa hP hQ t

end TreeEuler


/-! ## Perfect-foresight equilibria with a constant endowment -/

namespace PF

/-- Cochrane (2023), (19.32), p. 450: with a constant endowment (`Λ_{t+1}/Λ_t = β`, Fact 1) the
nominal bond price is `Q_t = βP_t/P_{t+1}`. -/
noncomputable def bondPrice (β : ℝ) (P : ℕ → ℝ) (t : ℕ) : ℝ := β * P t / P (t + 1)

/-- Cochrane (2023), p. 450 (**E15**): with a constant endowment `Q_t = βP_t/P_{t+1}`, which
equals `β` iff the price level is constant between `t` and `t + 1` (the book's "`Q = β`"). -/
theorem bondPrice_eq_beta_iff {β : ℝ} {P : ℕ → ℝ} (hβ : 0 < β) (hP : ∀ t, 0 < P t) (t : ℕ) :
    bondPrice β P t = β ↔ P (t + 1) = P t := by
  have h1 := (hP t).ne'
  have h2 := (hP (t + 1)).ne'
  unfold bondPrice
  rw [div_eq_iff h2]
  constructor
  · intro h
    have := mul_left_cancel₀ hβ.ne' (by linarith : β * P t = β * P (t + 1))
    linarith
  · intro h
    rw [h]

/-- Cochrane (2023), (19.32), p. 450: for a constant price level `Q_t = β`. -/
theorem bondPrice_const {β p : ℝ} (hp : p ≠ 0) (t : ℕ) : bondPrice β (fun _ => p) t = β := by
  unfold bondPrice
  field_simp

/-- Cochrane (2023), p. 454: along `P_t = β^tP_0` (deflation at the real rate) `Q_t = 1`, i.e.
`i_t = 0`. -/
theorem bondPrice_deflation {β P0 : ℝ} (hβ : 0 < β) (hP0 : 0 < P0) (t : ℕ) :
    bondPrice β (fun t => β ^ t * P0) t = 1 := by
  unfold bondPrice
  have := (pow_pos hβ t).ne'
  have := hP0.ne'
  change β * (β ^ t * P0) / (β ^ (t + 1) * P0) = 1
  rw [pow_succ]
  field_simp

/-- Cochrane (2023), p. 454: along `P_t = P_{−1}(1+μ)^{t+1}` (the quantity-theory path)
`Q_t = β/(1 + μ)`, i.e. `1 + i = (1 + δ)(1 + μ)` with `1 + δ = 1/β`. -/
theorem bondPrice_growth {β c g : ℝ} (hc : c ≠ 0) (hg : g ≠ 0) (t : ℕ) :
    bondPrice β (fun t => c * g ^ (t + 1)) t = β / g := by
  unfold bondPrice
  have := pow_ne_zero (t + 1) hg
  change β * (c * g ^ (t + 1)) / (c * g ^ (t + 1 + 1)) = β / g
  rw [pow_succ g (t + 1)]
  field_simp

/-- Cochrane (2023), (19.28)–(19.30), p. 449 (deterministic version): if `z_t = z_{t+1} + f_t` and
`j ↦ f_{t+j}` is summable, then `z_T → 0` iff `z_t = Σ_j f_{t+j}`. -/
theorem pv_of_rec {z f : ℕ → ℝ} (hrec : ∀ t, z t = z (t + 1) + f t) (t : ℕ)
    (hs : Summable fun j => f (t + j)) :
    Tendsto z atTop (𝓝 0) ↔ z t = ∑' j, f (t + j) := by
  have hpart : ∀ n, z (t + n) = z t - ∑ j ∈ Finset.range n, f (t + j) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, show t + (n + 1) = t + n + 1 by omega]
      have := hrec (t + n)
      linarith
  rw [← tendsto_add_atTop_iff_nat t]
  have hfun : (fun n => z (n + t)) = fun n => z t - ∑ j ∈ Finset.range n, f (t + j) :=
    funext fun n => by rw [add_comm, hpart]
  rw [hfun]
  have hlim := hs.hasSum.tendsto_sum_nat
  constructor
  · intro h
    have := tendsto_nhds_unique h (hlim.const_sub (z t))
    linarith
  · intro h
    have := hlim.const_sub (z t)
    rwa [← h, sub_self] at this

/-- Cochrane (2023), (19.27), p. 449 (perfect foresight, `c = y`, `Λ_t = β^t`): the flow budget
gives `β^t(B_{t−1} + M_{t−1})/P_t = β^{t+1}(B_t + M_t)/P_{t+1} + β^t(s_t + (1 − Q_t)M_t/P_t)`. -/
theorem rec_of_flow {β : ℝ} {P Bin Min s : ℕ → ℝ} (hpos : ∀ t, 0 < P t)
    (hflow : ∀ t, Bin t + Min t = bondPrice β P t * Bin (t + 1) + Min (t + 1) + P t * s t)
    (t : ℕ) :
    β ^ t * (Bin t + Min t) / P t = β ^ (t + 1) * (Bin (t + 1) + Min (t + 1)) / P (t + 1) +
      β ^ t * (s t + (1 - bondPrice β P t) * Min (t + 1) / P t) := by
  have h1 := (hpos t).ne'
  have h2 := (hpos (t + 1)).ne'
  rw [hflow t]
  unfold bondPrice
  rw [pow_succ]
  field_simp
  ring

/-- Cochrane (2023), (19.35), p. 450 (perfect foresight): **valuation iff transversality.** Under
the flow budget, with `β > 0` and the flows summable, the TVC (19.28)
`β^T(B_{T−1} + M_{T−1})/P_T → 0` holds iff
`(B_{t−1} + M_{t−1})/P_t = Σ_j β^j(s_{t+j} + (1 − Q_{t+j})M_{t+j}/P_{t+j})`. -/
theorem valuation_iff {β : ℝ} {P Bin Min s : ℕ → ℝ} (hβ : 0 < β) (hpos : ∀ t, 0 < P t)
    (hflow : ∀ t, Bin t + Min t = bondPrice β P t * Bin (t + 1) + Min (t + 1) + P t * s t)
    (t : ℕ) (hs : Summable fun j =>
      β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j))) :
    Tendsto (fun T => β ^ T * (Bin T + Min T) / P T) atTop (𝓝 0) ↔
      (Bin t + Min t) / P t = ∑' j,
        β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j)) := by
  have hs' : Summable fun j => β ^ (t + j) *
      (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j)) :=
    (hs.mul_left (β ^ t)).congr fun j => by rw [pow_add]; ring
  rw [pv_of_rec (f := fun τ => β ^ τ * (s τ + (1 - bondPrice β P τ) * Min (τ + 1) / P τ))
    (z := fun τ => β ^ τ * (Bin τ + Min τ) / P τ) (rec_of_flow hpos hflow) t hs']
  have hsum : ∑' j, β ^ (t + j) *
      (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j)) =
      β ^ t * ∑' j, β ^ j *
        (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j)) := by
    rw [← tsum_mul_left]
    congr 1
    funext j
    rw [pow_add]
    ring
  rw [hsum]
  have hb := (pow_pos hβ t).ne'
  have hp := (hpos t).ne'
  constructor
  · intro h
    have h' : β ^ t * ((Bin t + Min t) / P t) = β ^ t * ∑' j, β ^ j *
        (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j)) := by
      rw [← h]
      ring
    exact mul_left_cancel₀ hb h'
  · intro h
    rw [← h]
    ring

variable (β y V : ℝ) (P Bin Min s : ℕ → ℝ)

/-- Cochrane (2023), §19.5.4, pp. 449, 452: a perfect-foresight equilibrium of the
**frictionless** model with a constant endowment (`c = y`, `Λ_t = β^t` by (19.36),
`Q_t = βP_t/P_{t+1}`): positive prices; optimal overnight money, i.e. `M_t ≥ 0`, `Q_t ≤ 1` and
`Q_t < 1 ⇒ M_t = 0` (`frictionless_money_optimal`); the flow budget (19.27); and the
transversality condition (19.28). -/
structure FrictionlessEq where
  pos : ∀ t, 0 < P t
  money_nonneg : ∀ t, 0 ≤ Min (t + 1)
  rate_nonneg : ∀ t, bondPrice β P t ≤ 1
  no_money : ∀ t, bondPrice β P t < 1 → Min (t + 1) = 0
  flow : ∀ t, Bin t + Min t = bondPrice β P t * Bin (t + 1) + Min (t + 1) + P t * s t
  tvc : Tendsto (fun T => β ^ T * (Bin T + Min T) / P T) atTop (𝓝 0)

/-- Cochrane (2023), §19.5.2, pp. 449–450: a perfect-foresight equilibrium of the **monetary**
(cash-in-advance) model with a constant endowment `y` and velocity `V > 0`: positive prices;
optimal overnight money, i.e. `M_t ≥ P_ty/V` ((19.24)–(19.25) at `c = y`), `Q_t ≤ 1` and
`Q_t < 1 ⇒ M_t = P_ty/V` (`monetary_money_optimal`); the flow budget (19.27); and the
transversality condition (19.28). -/
structure MonetaryEq where
  pos : ∀ t, 0 < P t
  cia : ∀ t, P t * y / V ≤ Min (t + 1)
  rate_nonneg : ∀ t, bondPrice β P t ≤ 1
  binds : ∀ t, bondPrice β P t < 1 → Min (t + 1) = P t * y / V
  flow : ∀ t, Bin t + Min t = bondPrice β P t * Bin (t + 1) + Min (t + 1) + P t * s t
  tvc : Tendsto (fun T => β ^ T * (Bin T + Min T) / P T) atTop (𝓝 0)

variable {β y V P Bin Min s}

/-- Cochrane (2023), (19.37), p. 452: the money conditions of `FrictionlessEq` at date `t` are
exactly optimality of the overnight money holding with minimum `0` (any wealth `W`). -/
theorem frictionless_money_optimal_iff {W : ℝ} (t : ℕ) :
    MoneyDemand.IsOptimalMoney (bondPrice β P t) 0 W (Min (t + 1)) ↔
      bondPrice β P t ≤ 1 ∧ 0 ≤ Min (t + 1) ∧ (bondPrice β P t < 1 → Min (t + 1) = 0) :=
  MoneyDemand.optimal_iff

/-- Cochrane (2023), (19.37), p. 452: in a frictionless equilibrium overnight money is optimal. -/
theorem frictionless_money_optimal (h : FrictionlessEq β P Bin Min s) (W : ℝ) (t : ℕ) :
    MoneyDemand.IsOptimalMoney (bondPrice β P t) 0 W (Min (t + 1)) :=
  MoneyDemand.optimal_iff.2 ⟨h.rate_nonneg t, h.money_nonneg t, h.no_money t⟩

/-- Cochrane (2023), (19.33), p. 450: in a monetary equilibrium overnight money is optimal, with
minimum `P_ty/V`. -/
theorem monetary_money_optimal (h : MonetaryEq β y V P Bin Min s) (W : ℝ) (t : ℕ) :
    MoneyDemand.IsOptimalMoney (bondPrice β P t) (P t * y / V) W (Min (t + 1)) :=
  MoneyDemand.optimal_iff.2 ⟨h.rate_nonneg t, h.cia t, h.binds t⟩

/-- Cochrane (2023), (19.33), p. 450, **Fact 2** in equilibrium: positive nominal rate ⇒
`M_tV = P_ty`. -/
theorem monetary_fact2 (h : MonetaryEq β y V P Bin Min s) (hV : 0 < V) {t : ℕ}
    (hQ : bondPrice β P t < 1) : Min (t + 1) * V = P t * y := by
  rw [h.binds t hQ]
  field_simp

/-- Cochrane (2023), (19.38), p. 452, **corrected**: in a frictionless equilibrium the seigniorage
term vanishes, `(1 − Q_t)M_t = 0` (either `M_t = 0` or `Q_t = 1`). -/
theorem frictionless_seigniorage_zero (h : FrictionlessEq β P Bin Min s) (t : ℕ) :
    (1 - bondPrice β P t) * Min (t + 1) = 0 := by
  rcases lt_or_eq_of_le (h.rate_nonneg t) with hQ | hQ
  · rw [h.no_money t hQ, mul_zero]
  · rw [hQ, sub_self, zero_mul]

/-- Cochrane (2023), (19.35), p. 450: in a monetary equilibrium the seigniorage term is
`(1 − Q_t)M_t/P_t = (1 − Q_t)y/V` (binding constraint, or `Q_t = 1`). -/
theorem monetary_seigniorage (h : MonetaryEq β y V P Bin Min s) (hV : 0 < V) (t : ℕ) :
    (1 - bondPrice β P t) * Min (t + 1) / P t = (1 - bondPrice β P t) * y / V := by
  have hp := (h.pos t).ne'
  have := hV.ne'
  rcases lt_or_eq_of_le (h.rate_nonneg t) with hQ | hQ
  · rw [h.binds t hQ]
    field_simp
  · rw [hQ]
    ring

/-- Cochrane (2023), (19.38), p. 452, **corrected**: in a frictionless equilibrium
`(B_{t−1} + M_{t−1})/P_t = Σ_j β^j s_{t+j}` (surpluses absolutely summable; individual surpluses
may be negative). The book prints `B_{t−1}/P_t` (see `printed_19_38_counterexample`). -/
theorem frictionless_valuation (hβ : 0 < β) (h : FrictionlessEq β P Bin Min s) (t : ℕ)
    (hs : Summable fun j => β ^ j * s (t + j)) :
    (Bin t + Min t) / P t = ∑' j, β ^ j * s (t + j) := by
  have hfun : (fun j => β ^ j *
      (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j))) =
      fun j => β ^ j * s (t + j) := by
    funext j
    rw [mul_div_assoc, show (1 - bondPrice β P (t + j)) * (Min (t + j + 1) / P (t + j)) =
      (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j) by ring,
      frictionless_seigniorage_zero h (t + j), zero_div, add_zero]
  have := (valuation_iff hβ h.pos h.flow t (by rw [hfun]; exact hs)).1 h.tvc
  rwa [hfun] at this

/-- Cochrane (2023), (19.35), p. 450 in a monetary equilibrium:
`(B_{t−1} + M_{t−1})/P_t = Σ_j β^j(s_{t+j} + (1 − Q_{t+j})y/V)`. -/
theorem monetary_valuation (hβ : 0 < β) (hV : 0 < V) (h : MonetaryEq β y V P Bin Min s)
    (t : ℕ) (hs : Summable fun j => β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * y / V)) :
    (Bin t + Min t) / P t = ∑' j, β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * y / V) := by
  have hfun : (fun j => β ^ j *
      (s (t + j) + (1 - bondPrice β P (t + j)) * Min (t + j + 1) / P (t + j))) =
      fun j => β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * y / V) := by
    funext j
    rw [monetary_seigniorage h hV (t + j)]
  have := (valuation_iff hβ h.pos h.flow t (by rw [hfun]; exact hs)).1 h.tvc
  rwa [hfun] at this

/-- Cochrane (2023), (19.38), p. 452: given the corrected valuation, the printed form
`B_{t−1}/P_t = Σ_j β^j s_{t+j}` holds iff `M_{t−1} = 0`. -/
theorem printed_19_38_iff (hβ : 0 < β) (h : FrictionlessEq β P Bin Min s) (t : ℕ)
    (hs : Summable fun j => β ^ j * s (t + j)) :
    Bin t / P t = ∑' j, β ^ j * s (t + j) ↔ Min t = 0 := by
  rw [← frictionless_valuation hβ h t hs]
  have hp := (h.pos t).ne'
  constructor
  · intro e
    field_simp at e
    linarith
  · intro e
    rw [e, add_zero]

/-- Cochrane (2023), (19.38), p. 452 (**printed form false when money is held at a zero rate**):
for `0 < β < 1`, `P_0, W > 0`, the zero-rate path `P_t = β^tP_0`, `B_{t−1} = M_{t−1} = Wβ^t/2`,
`s_t = W(1 − β)/P_0` is a frictionless equilibrium, but `B_{−1}/P_0 = W/(2P_0)` while
`Σ_j β^j s_j = W/P_0`. -/
theorem printed_19_38_counterexample (hβ0 : 0 < β) (hβ1 : β < 1) {P0 W : ℝ} (hP0 : 0 < P0)
    (hW : 0 < W) :
    FrictionlessEq β (fun t => β ^ t * P0) (fun t => W * β ^ t / 2) (fun t => W * β ^ t / 2)
        (fun _ => W * (1 - β) / P0) ∧
      W * β ^ 0 / 2 / (β ^ 0 * P0) ≠ ∑' j, β ^ j * (W * (1 - β) / P0) := by
  have hbp := bondPrice_deflation hβ0 hP0
  refine ⟨⟨fun t => mul_pos (pow_pos hβ0 t) hP0, fun t => by positivity,
    fun t => (hbp t).le, fun t ht => absurd ((hbp t) ▸ ht) (lt_irrefl 1), fun t => ?_, ?_⟩, ?_⟩
  · rw [hbp t, pow_succ]
    field_simp
    ring
  · have hfun : (fun T => β ^ T * (W * β ^ T / 2 + W * β ^ T / 2) / (β ^ T * P0)) =
        fun T => W / P0 * β ^ T := by
      funext T
      have := (pow_pos hβ0 T).ne'
      field_simp
      ring
    rw [hfun]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (W / P0)
  · rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1]
    have h1 : (1 - β) ≠ 0 := by linarith
    have hr : (1 - β)⁻¹ * (W * (1 - β) / P0) = W / P0 := by field_simp
    rw [hr]
    simp only [pow_zero, one_mul, mul_one]
    intro h
    have := hP0.ne'
    field_simp at h
    linarith

/-- Cochrane (2023), p. 453: **the frictionless price level is unique** given the government's
choices: two frictionless equilibria with the same `{B, M, s}` and `B_{t−1} + M_{t−1} ≠ 0` at
every date (surpluses absolutely summable) have the same price level. -/
theorem frictionless_price_unique (hβ : 0 < β) {P' : ℕ → ℝ} (h : FrictionlessEq β P Bin Min s)
    (h' : FrictionlessEq β P' Bin Min s) (hBM : ∀ t, Bin t + Min t ≠ 0)
    (hs : ∀ t, Summable fun j => β ^ j * s (t + j)) : P = P' := by
  funext t
  have e1 := frictionless_valuation hβ h t (hs t)
  have e2 := frictionless_valuation hβ h' t (hs t)
  rw [← e2] at e1
  have hp := (h.pos t).ne'
  have hp' := (h'.pos t).ne'
  field_simp at e1
  have := mul_left_cancel₀ (hBM t) (by linarith : (Bin t + Min t) * P' t = (Bin t + Min t) * P t)
  linarith

/-- Cochrane (2023), p. 453: in a frictionless equilibrium with `B_{t−1} + M_{t−1} > 0` the
present value of surpluses is positive and `P_t = (B_{t−1} + M_{t−1})/Σ_j β^j s_{t+j}`. -/
theorem frictionless_price_formula (hβ : 0 < β) (h : FrictionlessEq β P Bin Min s) (t : ℕ)
    (hBM : 0 < Bin t + Min t) (hs : Summable fun j => β ^ j * s (t + j)) :
    0 < ∑' j, β ^ j * s (t + j) ∧ P t = (Bin t + Min t) / ∑' j, β ^ j * s (t + j) := by
  have e := frictionless_valuation hβ h t hs
  have hpos : 0 < ∑' j, β ^ j * s (t + j) := by rw [← e]; exact div_pos hBM (h.pos t)
  refine ⟨hpos, ?_⟩
  rw [← e]
  have := (h.pos t).ne'
  field_simp

/-- Cochrane (2023), p. 453 ("rule out 0/0 problems"): with no debt, no money and no surpluses,
every constant positive price level is a frictionless equilibrium. -/
theorem zero_debt_indeterminate (hβ1 : β < 1) {P0 : ℝ} (hP0 : 0 < P0) :
    FrictionlessEq β (fun _ => P0) (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  have hbp := bondPrice_const (β := β) hP0.ne'
  refine ⟨fun _ => hP0, fun _ => le_rfl, fun t => by rw [hbp t]; linarith, fun _ _ => rfl,
    fun t => by ring, ?_⟩
  simp

/-- Cochrane (2023), pp. 452–453: **the frictionless example.** With `0 < β < 1`, constant
nominal debt `B > 0`, no money and a constant surplus `s > 0`, the constant price level
`P = (1 − β)B/s` is a frictionless equilibrium (with `Q_t = β < 1`, so `M = 0` is optimal, and the
TVC `β^TB/P → 0`). -/
theorem example_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1) {B sb : ℝ} (hB : 0 < B) (hs : 0 < sb) :
    FrictionlessEq β (fun _ => (1 - β) * B / sb) (fun _ => B) (fun _ => 0) (fun _ => sb) := by
  have hP : 0 < (1 - β) * B / sb := div_pos (mul_pos (by linarith) hB) hs
  have hbp := bondPrice_const (β := β) hP.ne'
  refine ⟨fun _ => hP, fun _ => le_rfl, fun t => by rw [hbp t]; linarith, fun _ _ => rfl,
    fun t => ?_, ?_⟩
  · rw [hbp t]
    field_simp
    ring
  · have hfun : (fun T => β ^ T * (B + 0) / ((1 - β) * B / sb)) =
        fun T => sb / (1 - β) * β ^ T := by
      funext T
      rw [add_zero]
      have : (1 - β) ≠ 0 := by linarith
      have := hB.ne'
      field_simp
    rw [hfun]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (sb / (1 - β))

/-- Cochrane (2023), pp. 452–453: **uniqueness in the example**: every frictionless equilibrium
with constant debt `B > 0`, no money and constant surplus `s` has `P_t = (1 − β)B/s`. -/
theorem example_unique (hβ0 : 0 < β) (hβ1 : β < 1) {B sb : ℝ} (hB : 0 < B)
    (h : FrictionlessEq β P (fun _ => B) (fun _ => 0) (fun _ => sb)) (t : ℕ) :
    P t = (1 - β) * B / sb := by
  have hsum : Summable fun j => β ^ j * (fun _ => sb) (t + j) :=
    (summable_geometric_of_lt_one hβ0.le hβ1).mul_right sb |>.congr fun j => by ring
  have e := frictionless_valuation hβ0 h t hsum
  simp only [add_zero] at e
  rw [show (∑' j, β ^ j * sb) = sb / (1 - β) by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1]; ring] at e
  have hp := (h.pos t).ne'
  have h1 : (1 - β) ≠ 0 := by linarith
  have hsb : sb ≠ 0 := by
    intro h0
    rw [h0, zero_div] at e
    exact (div_pos hB (h.pos t)).ne' e
  field_simp at e
  field_simp
  linarith

/-- Cochrane (2023), p. 453 (**E14**): in the example equilibrium `Q_t = β < 1`, so the printed
requirement "`Q_t ≥ 1`" fails in an equilibrium; the correct requirement is `Q_t ≤ 1`. -/
theorem E14_example (hβ1 : β < 1) {B sb : ℝ} (hP : (1 - β) * B / sb ≠ 0) (t : ℕ) :
    bondPrice β (fun _ => (1 - β) * B / sb) t < 1 ∧
      ¬ 1 ≤ bondPrice β (fun _ => (1 - β) * B / sb) t := by
  rw [bondPrice_const hP]
  exact ⟨hβ1, not_le.2 hβ1⟩

/-- Cochrane (2023), p. 453: a **passive** surplus rule `s_t = (1 − β)B/P_t` (surpluses respond to
the price level so as to validate it). -/
noncomputable def passiveSurplus (β B : ℝ) (P : ℕ → ℝ) : ℕ → ℝ := fun t => (1 - β) * B / P t

/-- Cochrane (2023), p. 453: **passive fiscal policy leaves the frictionless price level
undetermined**: under the passive rule every constant price level `P_0 > 0` is an equilibrium
(constant debt `B`, no money). -/
theorem passive_fiscal_indeterminate (hβ0 : 0 < β) (hβ1 : β < 1) {B : ℝ}
    {P0 : ℝ} (hP0 : 0 < P0) :
    FrictionlessEq β (fun _ => P0) (fun _ => B) (fun _ => 0)
      (passiveSurplus β B (fun _ => P0)) := by
  have hbp := bondPrice_const (β := β) hP0.ne'
  refine ⟨fun _ => hP0, fun _ => le_rfl, fun t => by rw [hbp t]; linarith, fun _ _ => rfl,
    fun t => ?_, ?_⟩
  · rw [hbp t]
    simp only [passiveSurplus]
    field_simp
    ring
  · have hfun : (fun T => β ^ T * (B + 0) / P0) = fun T => B / P0 * β ^ T := by
      funext T
      ring
    rw [hfun]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (B / P0)

/-- Cochrane (2023), §19.5.5, p. 454: **the standard monetary equilibrium.** With money
`M_{t−1} = M_{−1}(1+μ)^t`, `β ≤ 1 + μ`, real debt `b`, the price level `P_t = M_tV/y` and the
(passive) surplus `s = (b(1 − β) − μy/V)/(1 + μ)` form a monetary equilibrium. -/
theorem usual_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hV : 0 < V) {μ Mm1 b : ℝ}
    (hμ : β ≤ 1 + μ) (hM : 0 < Mm1) :
    MonetaryEq β y V (fun t => Mm1 * V / y * (1 + μ) ^ (t + 1))
      (fun t => b * (Mm1 * (1 + μ) ^ t * V / y)) (fun t => Mm1 * (1 + μ) ^ t)
      (fun _ => (b * (1 - β) - μ * y / V) / (1 + μ)) := by
  have hg : 0 < 1 + μ := lt_of_lt_of_le hβ0 hμ
  have hc : 0 < Mm1 * V / y := by positivity
  have hbp := bondPrice_growth (β := β) hc.ne' hg.ne'
  refine ⟨fun t => by positivity, fun t => le_of_eq ?_, fun t => ?_, fun t _ => ?_,
    fun t => ?_, ?_⟩
  · field_simp
  · rw [hbp t, div_le_one hg]
    exact hμ
  · field_simp
  · rw [hbp t]
    have := hg.ne'
    have := hV.ne'
    have := hy.ne'
    rw [pow_succ]
    field_simp
    ring
  · have hfun : (fun T => β ^ T * (b * (Mm1 * (1 + μ) ^ T * V / y) + Mm1 * (1 + μ) ^ T) /
        (Mm1 * V / y * (1 + μ) ^ (T + 1))) = fun T => (b + y / V) / (1 + μ) * β ^ T := by
      funext T
      have := (pow_pos hg T).ne'
      have := hg.ne'
      have := hV.ne'
      have := hy.ne'
      have := hM.ne'
      rw [pow_succ]
      field_simp
    rw [hfun]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul _

/-- Cochrane (2023), p. 454: along the standard path the nominal rate is positive (`Q < 1`, the
cash constraint binds) iff `1 + μ > β`; and `1/Q = (1/β)(1 + μ)`, i.e. `1 + i = (1 + δ)(1 + μ)`. -/
theorem usual_rate {μ c : ℝ} (hβ0 : 0 < β) (hc : c ≠ 0) (hg : 0 < 1 + μ) (t : ℕ) :
    (bondPrice β (fun t => c * (1 + μ) ^ (t + 1)) t < 1 ↔ β < 1 + μ) ∧
      1 / bondPrice β (fun t => c * (1 + μ) ^ (t + 1)) t = 1 / β * (1 + μ) := by
  rw [bondPrice_growth hc hg.ne']
  refine ⟨div_lt_one hg, ?_⟩
  have := hβ0.ne'
  have := hg.ne'
  field_simp

/-- Cochrane (2023), p. 454 ("Even the `MV = Py` equilibrium becomes indeterminate when money
growth is too low"): if `1 + μ < β` the quantity-theory path requires a negative nominal rate
(`Q > 1`), so it is not an equilibrium. -/
theorem usual_fails_low_growth {μ Mm1 : ℝ} (hg : 0 < 1 + μ) (hμ : 1 + μ < β)
    (hc : Mm1 * V / y ≠ 0) {Bin' s' : ℕ → ℝ} :
    ¬ MonetaryEq β y V (fun t => Mm1 * V / y * (1 + μ) ^ (t + 1)) Bin'
      (fun t => Mm1 * (1 + μ) ^ t) s' := by
  intro h
  have := h.rate_nonneg 0
  rw [bondPrice_growth hc hg.ne', div_le_one hg] at this
  linarith

/-- Cochrane (2023), p. 450 (**E15**, explicit): along the standard monetary equilibrium
`Q_t = β/(1 + μ)`, which differs from the printed "`Q = β`" whenever `μ ≠ 0`. -/
theorem E15_counterexample {μ c : ℝ} (hβ0 : 0 < β) (hc : c ≠ 0) (hg : 0 < 1 + μ) (hμ : μ ≠ 0)
    (t : ℕ) : bondPrice β (fun t => c * (1 + μ) ^ (t + 1)) t ≠ β := by
  rw [bondPrice_growth hc hg.ne']
  intro h
  rw [div_eq_iff hg.ne'] at h
  have : β * μ = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hβ0.ne' h1
  · exact hμ h1

/-- Cochrane (2023), p. 454: **deflationary equilibria for any money growth with `1 + μ ≥ β`.**
For every `P_0 > 0` with `P_0 ≤ M_0V/y` (`M_0 = M_{−1}(1 + μ)`) and any initial nominal wealth
`A_0`, the path `P_t = β^tP_0` (zero nominal rate) with money `M_{t−1} = M_{−1}(1+μ)^t`, debt
`B_{t−1} = A_0β^t − M_{t−1}` and the passive surplus `s = A_0(1 − β)/P_0` is a monetary
equilibrium: people happily hold ever larger real balances at a zero rate. -/
theorem deflation_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1)
    {μ Mm1 P0 A0 : ℝ} (hμ : β ≤ 1 + μ) (hM : 0 ≤ Mm1) (hP0 : 0 < P0)
    (hcap : P0 * y / V ≤ Mm1 * (1 + μ)) :
    MonetaryEq β y V (fun t => β ^ t * P0) (fun t => A0 * β ^ t - Mm1 * (1 + μ) ^ t)
      (fun t => Mm1 * (1 + μ) ^ t) (fun _ => A0 * (1 - β) / P0) := by
  have hg : 0 < 1 + μ := lt_of_lt_of_le hβ0 hμ
  have hbp := bondPrice_deflation hβ0 hP0
  refine ⟨fun t => mul_pos (pow_pos hβ0 t) hP0, fun t => ?_, fun t => (hbp t).le,
    fun t ht => absurd ((hbp t) ▸ ht) (lt_irrefl 1), fun t => ?_, ?_⟩
  · have hpow : β ^ t ≤ (1 + μ) ^ t := pow_le_pow_left₀ hβ0.le hμ t
    calc β ^ t * P0 * y / V = β ^ t * (P0 * y / V) := by ring
      _ ≤ β ^ t * (Mm1 * (1 + μ)) := mul_le_mul_of_nonneg_left hcap (pow_nonneg hβ0.le t)
      _ ≤ (1 + μ) ^ t * (Mm1 * (1 + μ)) :=
          mul_le_mul_of_nonneg_right hpow (mul_nonneg hM hg.le)
      _ = Mm1 * (1 + μ) ^ (t + 1) := by rw [pow_succ]; ring
  · rw [hbp t, pow_succ, pow_succ]
    field_simp
    ring
  · have hfun : (fun T => β ^ T * (A0 * β ^ T - Mm1 * (1 + μ) ^ T + Mm1 * (1 + μ) ^ T) /
        (β ^ T * P0)) = fun T => A0 / P0 * β ^ T := by
      funext T
      have := (pow_pos hβ0 T).ne'
      field_simp
      ring
    rw [hfun]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (A0 / P0)

/-- Cochrane (2023), p. 454: along the deflation `P_t = β^tP_0` with `M_t = M_{−1}(1+μ)^{t+1}`,
discounted real money is `β^tM_t/P_t = (1 + μ)^t M_0/P_0`. -/
theorem deflation_real_money {μ Mm1 P0 : ℝ} (hβ0 : 0 < β) (hP0 : 0 < P0) (t : ℕ) :
    β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0) = Mm1 * (1 + μ) / P0 * (1 + μ) ^ t := by
  have := (pow_pos hβ0 t).ne'
  have := hP0.ne'
  rw [pow_succ]
  field_simp

/-- Cochrane (2023), p. 454: in the deflationary equilibria discounted real money
`β^tM_t/P_t` grows strictly ("real money holdings grow faster than the interest rate") iff
`μ > 0` (`M_{−1}, P_0 > 0`, `1 + μ > 0`). -/
theorem deflation_real_money_grows_iff {μ Mm1 P0 : ℝ} (hβ0 : 0 < β) (hP0 : 0 < P0)
    (hM : 0 < Mm1) (hg : 0 < 1 + μ) :
    StrictMono (fun t : ℕ => β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0)) ↔ 0 < μ := by
  have hfun : (fun t : ℕ => β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0)) =
      fun t => Mm1 * (1 + μ) / P0 * (1 + μ) ^ t :=
    funext fun t => deflation_real_money hβ0 hP0 t
  have hC : 0 < Mm1 * (1 + μ) / P0 := by positivity
  rw [hfun]
  constructor
  · intro h
    have := h (show (0 : ℕ) < 1 by norm_num)
    simp only [pow_zero, mul_one, pow_one] at this
    have := lt_of_mul_lt_mul_left (by simpa using this :
      Mm1 * (1 + μ) / P0 * 1 < Mm1 * (1 + μ) / P0 * (1 + μ)) hC.le
    linarith
  · intro hμ
    exact strictMono_nat_of_lt_succ fun n => mul_lt_mul_of_pos_left
      (pow_lt_pow_right₀ (by linarith) (Nat.lt_succ_self n)) hC

/-- Cochrane (2023), p. 454 and Online Appendix A3 (cf. E17): in the deflationary equilibria the
money transversality condition `β^tM_t/P_t → 0` holds iff `μ < 0`; it fails for every `μ ≥ 0`. -/
theorem deflation_money_tvc_iff {μ Mm1 P0 : ℝ} (hβ0 : 0 < β) (hP0 : 0 < P0) (hM : 0 < Mm1)
    (hg : 0 < 1 + μ) :
    Tendsto (fun t : ℕ => β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0)) atTop (𝓝 0) ↔
      μ < 0 := by
  have hfun : (fun t : ℕ => β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0)) =
      fun t => Mm1 * (1 + μ) / P0 * (1 + μ) ^ t :=
    funext fun t => deflation_real_money hβ0 hP0 t
  have hC : 0 < Mm1 * (1 + μ) / P0 := by positivity
  rw [hfun]
  constructor
  · intro h
    have h2 := h.const_mul (Mm1 * (1 + μ) / P0)⁻¹
    simp only [mul_zero, ← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] at h2
    rw [tendsto_pow_atTop_nhds_zero_iff, abs_lt] at h2
    linarith [h2.2]
  · intro hμ
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hg.le (by linarith)).const_mul
      (Mm1 * (1 + μ) / P0)
    simpa using this

/-- Cochrane (2023), p. 454: **an active fiscal policy prunes the deflationary equilibria.** Fix
the money path of the standard equilibrium (`M_{t−1} = M_{−1}(1+μ)^t`, `1 + μ > β`), its initial
nominal wealth `A_0 = B_{−1} + M_{−1} = M_{−1}(bV/y + 1)` (`b ≥ 0`) and its surplus
`s = (b(1 − β) − μy/V)/(1 + μ)` as an exogenous (active) sequence that does not respond to the
price level. Then there is no monetary equilibrium with a permanently zero nominal rate
(`Q_t = 1` for all `t`). -/
theorem active_fiscal_prunes (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hV : 0 < V)
    {μ Mm1 b : ℝ} (hμ : β < 1 + μ) (hM : 0 < Mm1) (hb : 0 ≤ b) {P' Bin' : ℕ → ℝ}
    (h : MonetaryEq β y V P' Bin' (fun t => Mm1 * (1 + μ) ^ t)
      (fun _ => (b * (1 - β) - μ * y / V) / (1 + μ)))
    (hA : Bin' 0 + Mm1 * (1 + μ) ^ 0 = Mm1 * (b * V / y + 1))
    (hzero : ∀ t, bondPrice β P' t = 1) : False := by
  have hg : 0 < 1 + μ := lt_trans hβ0 hμ
  set sv := (b * (1 - β) - μ * y / V) / (1 + μ) with hsv
  have hsum : Summable fun j => β ^ j * ((fun _ => sv) (0 + j) +
      (1 - bondPrice β P' (0 + j)) * y / V) := by
    refine ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right sv).congr fun j => ?_
    simp only [hzero, sub_self, zero_mul, zero_div, add_zero]
  have e := monetary_valuation hβ0 hV h 0 hsum
  simp only [hzero, sub_self, zero_mul, zero_div, add_zero, zero_add] at e
  rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1, hA] at e
  have hcia := h.cia 0
  simp only [zero_add, pow_one] at hcia
  have hP := h.pos 0
  have h1 : (1 - β) ≠ 0 := by linarith
  -- e : M(bV/y + 1)/P' 0 = (1 - β)⁻¹ * sv
  have key : Mm1 * V * (b * V + y) * (1 - β) * (1 + μ) =
      y * P' 0 * (b * V * (1 - β) - y * μ) := by
    rw [hsv] at e
    have := hV.ne'
    have := hy.ne'
    have := hg.ne'
    field_simp at e
    linear_combination e
  have hcia' : P' 0 * y ≤ Mm1 * (1 + μ) * V := by
    rw [div_le_iff₀ hV] at hcia
    linarith
  have hlhs : 0 < Mm1 * V * (b * V + y) * (1 - β) * (1 + μ) := by
    have : 0 < b * V + y := by nlinarith
    have : 0 < 1 - β := by linarith
    positivity
  rcases le_or_gt (b * V * (1 - β) - y * μ) 0 with hneg | hposv
  · have h3 : y * P' 0 * (b * V * (1 - β) - y * μ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  · have h5 : P' 0 * y * (b * V * (1 - β) - y * μ) ≤
        Mm1 * (1 + μ) * V * (b * V * (1 - β) - y * μ) :=
      mul_le_mul_of_nonneg_right hcia' hposv.le
    have hid : y * P' 0 * (b * V * (1 - β) - y * μ) =
        Mm1 * (1 + μ) * V * (b * V * (1 - β) - y * μ) + Mm1 * (1 + μ) * V * y * (1 - β + μ) := by
      rw [← key]
      ring
    have h7 : 0 < Mm1 * (1 + μ) * V * y * (1 - β + μ) := by
      have : 0 < 1 - β + μ := by linarith
      positivity
    have h8 : P' 0 * y * (b * V * (1 - β) - y * μ) = y * P' 0 * (b * V * (1 - β) - y * μ) := by
      ring
    linarith

/-- Cochrane (2023), §19.5.3, p. 451: **the same equilibrium supports either coordination
story.** In a monetary equilibrium with positive nominal rates at every date, the price level is
pinned by money, `P_t = M_tV/y` ("active money"), and at the same time by the debt valuation
equation, `P_t = (B_{t−1} + M_{t−1})/Σ_j β^j(s_{t+j} + (1 − Q_{t+j})y/V)` ("active fiscal"),
whenever `B_{t−1} + M_{t−1} > 0`. -/
theorem coordination (hβ : 0 < β) (hy : 0 < y) (hV : 0 < V) (h : MonetaryEq β y V P Bin Min s)
    (hQ : ∀ t, bondPrice β P t < 1) (t : ℕ) (hBM : 0 < Bin t + Min t)
    (hs : Summable fun j => β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * y / V)) :
    P t = Min (t + 1) * V / y ∧
      P t = (Bin t + Min t) /
        ∑' j, β ^ j * (s (t + j) + (1 - bondPrice β P (t + j)) * y / V) := by
  refine ⟨?_, ?_⟩
  · have := monetary_fact2 h hV (hQ t)
    have := hy.ne'
    field_simp
    linarith
  · rw [← monetary_valuation hβ hV h t hs]
    have := (h.pos t).ne'
    have := hBM.ne'
    field_simp

end PF

end Cochrane.Monetarism.CashInAdvance
