/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.LeeperRegions
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Region (d) at the boundary `|φ| = 1`: when the monetary equation has a bounded solution

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.7, pp. 508–509
(regions (a)–(d) of the Leeper model (22.3)–(22.6)), and Chapter 23, eqs. (23.1)–(23.2), p. 512.

`LeeperRegions.region_d_of_solution` shows that at `|φ| ≤ 1` (with `0 < γ < 2`) the Leeper model
has uncountably many admissible equilibria as soon as the monetary equation
`E_t π_{t+1} = φπ_t + u_{i,t}` has one bounded adapted solution, and
`LeeperRegions.region_d_unit_nonexistence` exhibits a bounded `u_i` with no equilibrium at all.
This module characterises, in terms of the disturbance `u_i`, when a bounded solution exists at
`φ = 1` and at `φ = −1`, in any `ExpectationSystem`.

## The two sums

With `φ² = 1` write
* `condSum φ u t T = ∑_{j<T} φʲ E_t u_{t+j}` — the conditional sums (`φ = 1`: plain sums of
  forecasts; `φ = −1`: alternating sums);
* `pathSum φ u t = ∑_{s<t} φˢ u_s` — the realised sums.

## Main results

* `iterate_sol`: any solution satisfies `φᵀ E_t π_{t+T} = π_t + φ condSum_t(T)`;
  `condBdd_of_sol` (**necessity**, any expectation system): a bounded solution forces the
  conditional sums to be bounded, uniformly in `t`, `T` and the state.
* `finSol`: the solution pinned at `π_N = 0`, `π^{(N)}_t = D_t − φ^{t+N} E_t D_N` with
  `D_{t+1} = φD_t + u_t`; it solves the equation in every expectation system (`finSol_solves`)
  and `π^{(N)}_t = −φ condSum_t(N − t)` for `t ≤ N` (`finSol_eq_condSum`).
* `sol_of_pathBdd` (**sufficiency**, any expectation system): bounded realised sums give a bounded
  solution (`π = D`).
* `exists_iff_of_eventually` (**the characterisation**): when information stops arriving at some
  date `N` (`E_t = E_N` for `t ≥ N`: perfect foresight, full information, every finite tree such as
  the coin tree, `coinSystem_eventually`), a bounded solution exists **iff** the conditional sums
  are bounded; `exists_iff_phi_one` (`φ = 1`: `|E_t ∑_{j<T} u_{t+j}| ≤ C`) and
  `exists_iff_phi_neg_one` (`φ = −1`: `|E_t ∑_{j<T} (−1)ʲ u_{t+j}| ≤ C`).
* `exists_iff_known` (any expectation system): if the disturbance is known at date 0
  (deterministic disturbances in particular), a bounded solution exists iff the realised sums
  are bounded — `∑_{s<t} u_s` for `φ = 1`, `∑_{s<t} (−1)ˢ u_s` for `φ = −1`.
* `leeper_unit_dichotomy`: at `φ² = 1` and `0 < γ < 2` the set of admissible equilibria is empty
  or uncountable, and nonempty iff the monetary equation has a bounded solution;
  `leeper_unit_iff_eventually`, `leeper_unit_iff_known`: the same in terms of the sums.
* Counterexamples (any nonempty state space, deterministic disturbances): a constant `u_i = c ≠ 0`
  has no bounded solution at `φ = 1` but one at `φ = −1` (`const_phi_one_none`,
  `const_phi_neg_one_sol`); `u_{i,t} = c(−1)ᵗ` the reverse (`alt_phi_one_sol`,
  `alt_phi_neg_one_none`); the vanishing disturbance `u_{i,t} = 1/(t + 1)` has none at `φ = 1`
  (`harmonic_phi_one_none`) while `(−1)ᵗ/(t + 1)` has one at `φ = 1` and none at `φ = −1`
  (`altHarmonic_phi_one_sol`, `altHarmonic_phi_neg_one_none`). In the Leeper model
  (`leeper_const`, `leeper_harmonic`): no equilibrium at `φ = 1`, uncountably many at `φ = −1`.

The general case with genuinely infinite uncertainty, where the realised sums need not be
bounded, is `TidyR5UnitRootMeasure`.
-/

namespace Cochrane.ObservationalEquivalence.TidyR5UnitRoot

open Filter Topology
open Cochrane.ObservationalEquivalence.Valuation Cochrane.ObservationalEquivalence.StarredModel
open Cochrane.ObservationalEquivalence.LeeperRegions

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Definitions -/

/-- Cochrane (2023), (23.1)–(23.2), p. 512: `π` solves the monetary equation
`E_t π_{t+1} = φπ_t + u_{i,t}`. -/
def MonEq (φ : ℝ) (u π : ℕ → Ω → ℝ) : Prop := ∀ t, 𝔼.E t (π (t + 1)) = φ • π t + u t

/-- Cochrane (2023), §22.7, p. 508: the monetary equation has a bounded adapted solution. -/
def HasBddSol (φ : ℝ) (u : ℕ → Ω → ℝ) : Prop :=
  ∃ π, 𝔼.Adapted π ∧ BoundedProc π ∧ MonEq 𝔼 φ u π

/-- Cochrane (2023), §22.7, p. 508: the conditional sums `∑_{j<T} φʲ E_t u_{t+j}`. -/
noncomputable def condSum (φ : ℝ) (u : ℕ → Ω → ℝ) (t T : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range T, φ ^ j • 𝔼.E t (u (t + j))

/-- Cochrane (2023), §22.7, p. 508: the conditional sums are bounded uniformly in the date, the
horizon and the state. -/
def CondBdd (φ : ℝ) (u : ℕ → Ω → ℝ) : Prop := ∃ C, ∀ t T ω, |condSum 𝔼 φ u t T ω| ≤ C

/-- Cochrane (2023), §22.7, p. 508: the realised sums `∑_{s<t} φˢ u_s`. -/
noncomputable def pathSum (φ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  ∑ s ∈ Finset.range t, φ ^ s • u s

/-- Cochrane (2023), §22.7, p. 508: the accumulated disturbance `D_0 = 0`,
`D_{t+1} = φD_t + u_t` (the solution with `π_0 = 0` and no sunspot). -/
noncomputable def accum (φ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => φ • accum φ u t + u t

/-- Cochrane (2023), §22.7, p. 508: the solution pinned at `π_N = 0`,
`π^{(N)}_t = D_t − φ^{t+N} E_t D_N`. -/
noncomputable def finSol (φ : ℝ) (u : ℕ → Ω → ℝ) (N t : ℕ) : Ω → ℝ :=
  accum φ u t - φ ^ (t + N) • 𝔼.E t (accum φ u N)

/-! ### Powers of `φ` with `φ² = 1` -/

/-- Cochrane (2023), §22.7, p. 508 (tool): with `φ² = 1`, `|φ| = 1`. -/
theorem abs_eq_one {φ : ℝ} (hφ : φ ^ 2 = 1) : |φ| = 1 := by
  have : |φ| ^ 2 = 1 := by rw [sq_abs, hφ]
  nlinarith [abs_nonneg φ, sq_nonneg (|φ| - 1), sq_nonneg (|φ| + 1)]

/-- Cochrane (2023), §22.7, p. 508 (tool): with `φ² = 1`, `|φⁿ| = 1`. -/
theorem abs_pow_eq_one {φ : ℝ} (hφ : φ ^ 2 = 1) (n : ℕ) : |φ ^ n| = 1 := by
  rw [abs_pow, abs_eq_one hφ, one_pow]

/-- Cochrane (2023), §22.7, p. 508 (tool): with `φ² = 1`, `φ^{n+2} = φⁿ`. -/
theorem pow_add_two {φ : ℝ} (hφ : φ ^ 2 = 1) (n : ℕ) : φ ^ (n + 2) = φ ^ n := by
  rw [pow_add, hφ, mul_one]

/-- Cochrane (2023), §22.7, p. 508 (tool): with `φ² = 1`, `φ^{2n} = 1`. -/
theorem pow_two_mul {φ : ℝ} (hφ : φ ^ 2 = 1) (n : ℕ) : φ ^ (2 * n) = 1 := by
  rw [pow_mul, hφ, one_pow]

/-! ### Iterating the monetary equation -/

/-- Cochrane (2023), (23.2), p. 512, iterated: if `π_t` is known at `t` and
`E_s π_{s+1} = φπ_s + u_s` at every date, then with `φ² = 1`,
`φᵀ E_t π_{t+T} = π_t + φ ∑_{j<T} φʲ E_t u_{t+j}`. -/
theorem iterate_sol {φ : ℝ} (hφ : φ ^ 2 = 1) {u π : ℕ → Ω → ℝ} (hπ : MonEq 𝔼 φ u π) {t : ℕ}
    (hπt : 𝔼.E t (π t) = π t) (T : ℕ) :
    φ ^ T • 𝔼.E t (π (t + T)) = π t + φ • condSum 𝔼 φ u t T := by
  induction T with
  | zero => simp [condSum, hπt]
  | succ T ih =>
    have hE : 𝔼.E t (π (t + (T + 1))) = φ • 𝔼.E t (π (t + T)) + 𝔼.E t (u (t + T)) := by
      rw [show t + (T + 1) = t + T + 1 by omega, ← 𝔼.tower (Nat.le_add_right t T), hπ (t + T),
        map_add, map_smul]
    rw [hE, condSum, Finset.sum_range_succ, ← condSum, smul_add, smul_add, smul_smul,
      ← pow_succ, show T + 1 + 1 = T + 2 by omega, pow_add_two hφ, ih, smul_smul, ← pow_succ',
      add_assoc]

/-- Cochrane (2023), §22.7, p. 508 (**necessity**, in every expectation system): if the
monetary equation at `φ² = 1` has a bounded adapted solution, the conditional sums
`∑_{j<T} φʲ E_t u_{t+j}` are bounded (by twice the bound of the solution), uniformly in `t`,
`T` and the state. -/
theorem condBdd_of_sol {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ} (h : HasBddSol 𝔼 φ u) :
    CondBdd 𝔼 φ u := by
  obtain ⟨π, hπa, ⟨M, hM⟩, hπ⟩ := h
  refine ⟨M + M, fun t T ω => ?_⟩
  have e := congrFun (iterate_sol 𝔼 hφ hπ (hπa t) T) ω
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e
  have e2 : condSum 𝔼 φ u t T ω = φ * (φ ^ T * 𝔼.E t (π (t + T)) ω - π t ω) := by
    have hφ2 : φ * φ = 1 := by rw [← sq]; exact hφ
    rw [e]
    linear_combination (-(condSum 𝔼 φ u t T ω)) * hφ2
  rw [e2, abs_mul, abs_eq_one hφ, one_mul]
  refine (abs_sub _ _).trans (add_le_add ?_ (hM t ω))
  rw [abs_mul, abs_pow_eq_one hφ, one_mul]
  exact 𝔼.abs_E_le (hM (t + T)) t ω

/-! ### The accumulated disturbance and the pinned solutions -/

/-- Cochrane (2023), §22.7, p. 508: with an adapted disturbance, `D_t` is known at `t`. -/
theorem accum_adapted {φ : ℝ} {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u) : 𝔼.Adapted (accum φ u) := by
  intro t
  induction t with
  | zero => change 𝔼.E 0 0 = 0; exact map_zero _
  | succ t ih =>
    change 𝔼.E (t + 1) (φ • accum φ u t + u t) = φ • accum φ u t + u t
    rw [map_add, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hua t)]

/-- Cochrane (2023), §22.7, p. 508: `D` solves the monetary equation (it is the solution with
`π_0 = 0` and no news). -/
theorem accum_solves {φ : ℝ} {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u) :
    MonEq 𝔼 φ u (accum φ u) := fun t => by
  change 𝔼.E t (φ • accum φ u t + u t) = φ • accum φ u t + u t
  rw [map_add, map_smul, accum_adapted 𝔼 hua t, hua t]

omit 𝔼 in
/-- Cochrane (2023), §22.7, p. 508: with `φ² = 1`, `D_t = φ^{t+1} ∑_{s<t} φˢ u_s`, so
`|D_t|` is the absolute realised sum. -/
theorem accum_eq_pathSum {φ : ℝ} (hφ : φ ^ 2 = 1) (u : ℕ → Ω → ℝ) (t : ℕ) :
    accum φ u t = φ ^ (t + 1) • pathSum φ u t := by
  induction t with
  | zero => simp [accum, pathSum]
  | succ t ih =>
    change φ • accum φ u t + u t = _
    rw [ih]
    unfold pathSum
    rw [Finset.sum_range_succ, smul_add]
    simp only [smul_smul, ← pow_succ']
    rw [show φ ^ (t + 1 + 1) * φ ^ t = φ ^ (2 * (t + 1)) by ring, pow_two_mul hφ, one_smul]

/-- Cochrane (2023), §22.7, p. 508: the pinned path `π^{(N)}` solves the monetary equation in
every expectation system (adapted disturbance, `φ² = 1`). -/
theorem finSol_solves {φ : ℝ} {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u) (N : ℕ) :
    MonEq 𝔼 φ u (finSol 𝔼 φ u N) := fun t => by
  have h1 := accum_solves 𝔼 (φ := φ) hua t
  simp only [finSol]
  rw [map_sub, map_smul, h1, 𝔼.tower (Nat.le_succ t), smul_sub, smul_smul, ← pow_succ',
    show t + 1 + N = t + N + 1 by omega]
  abel

/-- Cochrane (2023), §22.7, p. 508: the pinned path is adapted. -/
theorem finSol_adapted {φ : ℝ} {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u) (N : ℕ) :
    𝔼.Adapted (finSol 𝔼 φ u N) := fun t => by
  simp only [finSol]
  rw [map_sub, map_smul, accum_adapted 𝔼 hua t, 𝔼.E_E_self]

/-- Cochrane (2023), §22.7, p. 508: before the pinning date, `π^{(N)}_t = −φ condSum_t(N − t)`. -/
theorem finSol_eq_condSum {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u)
    (t T : ℕ) : finSol 𝔼 φ u (t + T) t = -(φ • condSum 𝔼 φ u t T) := by
  have h := iterate_sol 𝔼 hφ (accum_solves 𝔼 (φ := φ) hua) (accum_adapted 𝔼 hua t) T
  simp only [finSol]
  rw [show t + (t + T) = 2 * t + T by ring, pow_add, pow_two_mul hφ, one_mul, h]
  abel

/-- Cochrane (2023), §22.7, p. 508 (**sufficiency**, in every expectation system): bounded
realised sums `∑_{s<t} φˢ u_s` give a bounded adapted solution, `π = D`. -/
theorem sol_of_pathBdd {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u)
    (hb : BoundedProc (pathSum φ u)) : HasBddSol 𝔼 φ u := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨accum φ u, accum_adapted 𝔼 hua, ⟨M, fun t ω => ?_⟩, accum_solves 𝔼 hua⟩
  rw [accum_eq_pathSum hφ, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow_eq_one hφ, one_mul]
  exact hM t ω

/-! ### The characterisation -/

/-- Cochrane (2023), §22.7, p. 508: information stops arriving at date `N`:
`E_t = E_N` for every `t ≥ N`. -/
def EventuallyConstant (N : ℕ) : Prop := ∀ t, N ≤ t → ∀ x, 𝔼.E t x = 𝔼.E N x

/-- Cochrane (2023), §22.7, p. 508: if information stops arriving at `N`, after `N` the pinned
path is a realised (= conditional) sum: `π^{(N)}_{N+k} = φ^{k+1} condSum_N(k)`. -/
theorem finSol_after {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u) {N : ℕ}
    (hN : EventuallyConstant 𝔼 N) (k : ℕ) :
    finSol 𝔼 φ u N (N + k) = φ ^ (k + 1) • condSum 𝔼 φ u N k := by
  have h := iterate_sol 𝔼 hφ (accum_solves 𝔼 (φ := φ) hua) (accum_adapted 𝔼 hua N) k
  have hk : 𝔼.E N (accum φ u (N + k)) = accum φ u (N + k) := by
    rw [← hN (N + k) (Nat.le_add_right N k), accum_adapted 𝔼 hua]
  rw [hk] at h
  have hD : accum φ u (N + k) = φ ^ k • accum φ u N + φ ^ (k + 1) • condSum 𝔼 φ u N k := by
    have h2 := congrArg (fun z => φ ^ k • z) h
    simp only [smul_smul, smul_add, ← pow_add, show k + k = 2 * k by ring, pow_two_mul hφ,
      one_smul] at h2
    rw [h2, pow_succ]
  simp only [finSol]
  rw [ForwardSolution.E_of_known 𝔼 (Nat.le_add_right N k) (accum_adapted 𝔼 hua N), hD,
    show N + k + N = 2 * N + k by ring, pow_add φ (2 * N) k, pow_two_mul hφ, one_mul]
  abel

/-- Cochrane (2023), §22.7, p. 508 (**the characterisation** when information stops arriving at
some date — perfect foresight, full information, finite event trees): at `φ² = 1` the monetary
equation has a bounded adapted solution **iff** the conditional sums
`∑_{j<T} φʲ E_t u_{t+j}` are bounded. -/
theorem exists_iff_of_eventually {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u)
    {N : ℕ} (hN : EventuallyConstant 𝔼 N) : HasBddSol 𝔼 φ u ↔ CondBdd 𝔼 φ u := by
  refine ⟨condBdd_of_sol 𝔼 hφ, fun ⟨C, hC⟩ => ?_⟩
  refine ⟨finSol 𝔼 φ u N, finSol_adapted 𝔼 hua N, ⟨C, fun t ω => ?_⟩, finSol_solves 𝔼 hua N⟩
  rcases le_or_gt t N with htN | htN
  · obtain ⟨T, rfl⟩ := Nat.exists_eq_add_of_le htN
    rw [finSol_eq_condSum 𝔼 hφ hua, Pi.neg_apply, abs_neg, Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_eq_one hφ, one_mul]
    exact hC t T ω
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htN.le
    rw [finSol_after 𝔼 hφ hua hN, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow_eq_one hφ,
      one_mul]
    exact hC N k ω

/-- Cochrane (2023), §22.7, p. 508, at `φ = 1`: when information stops arriving at some date,
`E_t π_{t+1} = π_t + u_{i,t}` has a bounded adapted solution iff the forecasts of the cumulated
disturbance are bounded, `|E_t ∑_{j<T} u_{t+j}| ≤ C`. -/
theorem exists_iff_phi_one {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u) {N : ℕ}
    (hN : EventuallyConstant 𝔼 N) :
    HasBddSol 𝔼 1 u ↔ ∃ C, ∀ t T ω, |𝔼.E t (∑ j ∈ Finset.range T, u (t + j)) ω| ≤ C := by
  rw [exists_iff_of_eventually 𝔼 (by norm_num) hua hN, CondBdd]
  simp only [condSum, one_pow, one_smul, map_sum]

/-- Cochrane (2023), §22.7, p. 508, at `φ = −1`: when information stops arriving at some date,
`E_t π_{t+1} = −π_t + u_{i,t}` has a bounded adapted solution iff the forecasts of the
alternating sums are bounded, `|E_t ∑_{j<T} (−1)ʲ u_{t+j}| ≤ C`. -/
theorem exists_iff_phi_neg_one {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u) {N : ℕ}
    (hN : EventuallyConstant 𝔼 N) :
    HasBddSol 𝔼 (-1) u ↔
      ∃ C, ∀ t T ω, |𝔼.E t (∑ j ∈ Finset.range T, (-1 : ℝ) ^ j • u (t + j)) ω| ≤ C := by
  rw [exists_iff_of_eventually 𝔼 (by norm_num) hua hN, CondBdd]
  simp only [condSum, map_sum, map_smul]

/-- Cochrane (2023), §22.7, p. 508 (disturbances known at date 0, e.g. deterministic ones, in
every expectation system): at `φ² = 1` a bounded adapted solution exists **iff** the realised
sums `∑_{s<t} φˢ u_s` are bounded **iff** the conditional sums are bounded. -/
theorem exists_iff_known {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u)
    (hu0 : ∀ s, 𝔼.E 0 (u s) = u s) :
    (HasBddSol 𝔼 φ u ↔ BoundedProc (pathSum φ u)) ∧ (HasBddSol 𝔼 φ u ↔ CondBdd 𝔼 φ u) := by
  have hp : ∀ T, condSum 𝔼 φ u 0 T = pathSum φ u T := fun T => by
    simp only [condSum, pathSum, zero_add, hu0]
  have h1 : CondBdd 𝔼 φ u → BoundedProc (pathSum φ u) := fun ⟨C, hC⟩ =>
    ⟨C, fun t ω => by rw [← hp]; exact hC 0 t ω⟩
  have h2 : BoundedProc (pathSum φ u) → HasBddSol 𝔼 φ u := sol_of_pathBdd 𝔼 hφ hua
  exact ⟨⟨fun h => h1 (condBdd_of_sol 𝔼 hφ h), h2⟩,
    ⟨condBdd_of_sol 𝔼 hφ, fun h => h2 (h1 h)⟩⟩

/-- Cochrane (2023), §22.7, p. 508, at `φ = 1` with a disturbance known at date 0: a bounded
solution exists iff the partial sums `∑_{s<t} u_s` are bounded. -/
theorem exists_iff_known_phi_one {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u)
    (hu0 : ∀ s, 𝔼.E 0 (u s) = u s) :
    HasBddSol 𝔼 1 u ↔ BoundedProc fun t => ∑ s ∈ Finset.range t, u s := by
  rw [(exists_iff_known 𝔼 (by norm_num) hua hu0).1]
  unfold pathSum
  simp only [one_pow, one_smul]

/-- Cochrane (2023), §22.7, p. 508, at `φ = −1` with a disturbance known at date 0: a bounded
solution exists iff the alternating partial sums `∑_{s<t} (−1)ˢ u_s` are bounded. -/
theorem exists_iff_known_phi_neg_one {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u)
    (hu0 : ∀ s, 𝔼.E 0 (u s) = u s) :
    HasBddSol 𝔼 (-1) u ↔ BoundedProc fun t => ∑ s ∈ Finset.range t, (-1 : ℝ) ^ s • u s :=
  (exists_iff_known 𝔼 (by norm_num) hua hu0).1

/-! ### Expectation systems in which information stops arriving -/

omit 𝔼 in
/-- Cochrane (2023), §22.7, p. 508: under perfect foresight information never arrives. -/
theorem perfectForesight_eventually : EventuallyConstant perfectForesight 0 :=
  fun _ _ _ => rfl

omit 𝔼 in
/-- Cochrane (2023), §22.7, p. 508: with full information on any state space information never
arrives. -/
theorem fullInfo_eventually : EventuallyConstant (ExpectationTools.fullInfo Ω) 0 :=
  fun _ _ _ => rfl

/-- Cochrane (2023), §22.7, p. 509 (the coin-flip tree): both flips are known from date 2 on, so
information stops arriving at date 2. -/
theorem coinSystem_eventually : EventuallyConstant ExpectationsFiniteTree.coinSystem 2 := by
  have hfull : ∀ t, 2 ≤ t → ∀ x, ExpectationsFiniteTree.coinSystem.E t x = x := by
    intro t ht x
    funext ω
    rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
    refine ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h => ?_
    change Setoid.ker (ExpectationsFiniteTree.coinObs t) ω' ω at h
    rw [Setoid.ker_def] at h
    have h1 : 1 ≤ t := by omega
    simp only [ExpectationsFiniteTree.coinObs, h1, ht, ↓reduceIte] at h
    rw [show ω' = ω from Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)]
  intro t ht x
  rw [hfull t ht, hfull 2 le_rfl]

/-! ### The Leeper model at `|φ| = 1` -/

/-- Cochrane (2023), §22.7, pp. 508–509, region (d) at the boundary `φ² = 1` (`0 < γ < 2`): the
set of admissible equilibria of the Leeper model is either empty or uncountable, and it is
nonempty exactly when the monetary equation has a bounded adapted solution. -/
theorem leeper_unit_dichotomy [Nonempty Ω] {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hφ : φ ^ 2 = 1) (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us) (hK : 𝔼.E 0 K = K) :
    ((∃ x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x) ↔ HasBddSol 𝔼 φ ui) ∧
      ((∃ x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x) →
        ¬ {x | LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x}.Countable) := by
  have hsol : HasBddSol 𝔼 φ ui → ¬ {x | LeeperEqm 𝔼 ρ φ γ ui us K x ∧
      Admissible 𝔼 ρ x}.Countable := fun ⟨π, hπa, hπb, hπ⟩ =>
    region_d_of_solution 𝔼 hρ0 hρ1 (abs_eq_one hφ).le hγ hus husa hK hπa hπb hπ
  have hne : (∃ x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x) → HasBddSol 𝔼 φ ui :=
    fun ⟨x, hx, hadm⟩ => ⟨x.pi, hadm.1, hadm.2.2.1, leeper_expected_inflation 𝔼 hx⟩
  refine ⟨⟨hne, fun h => ?_⟩, fun h => hsol (hne h)⟩
  by_contra hcon
  push Not at hcon
  apply hsol h
  have : {x | LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun x hx => hcon x hx.1 hx.2
  rw [this]
  exact Set.countable_empty

/-- Cochrane (2023), §22.7, pp. 508–509, region (d) at `φ² = 1` when information stops arriving
(perfect foresight, finite trees): the Leeper model has an admissible equilibrium (and then
uncountably many) iff the conditional sums `∑_{j<T} φʲ E_t u_{i,t+j}` are bounded. -/
theorem leeper_unit_iff_eventually [Nonempty Ω] {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hφ : φ ^ 2 = 1) (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us)
    (hK : 𝔼.E 0 K = K) {N : ℕ} (hN : EventuallyConstant 𝔼 N) :
    (∃ x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x) ↔ CondBdd 𝔼 φ ui :=
  (leeper_unit_dichotomy 𝔼 hρ0 hρ1 hφ hγ hus husa hK).1.trans
    (exists_iff_of_eventually 𝔼 hφ huia hN)

/-- Cochrane (2023), §22.7, pp. 508–509, region (d) at `φ² = 1` with a monetary disturbance known
at date 0 (deterministic in particular), in every expectation system: the Leeper model has an
admissible equilibrium (and then uncountably many) iff the realised sums `∑_{s<t} φˢ u_{i,s}` are
bounded. -/
theorem leeper_unit_iff_known [Nonempty Ω] {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hφ : φ ^ 2 = 1) (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (huia : 𝔼.Adapted ui) (hui0 : ∀ s, 𝔼.E 0 (ui s) = ui s) (hus : ∀ t ω, |us t ω| ≤ Ms)
    (husa : 𝔼.Adapted us) (hK : 𝔼.E 0 K = K) :
    (∃ x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x) ↔ BoundedProc (pathSum φ ui) :=
  (leeper_unit_dichotomy 𝔼 hρ0 hρ1 hφ hγ hus husa hK).1.trans
    (exists_iff_known 𝔼 hφ huia hui0).1

/-! ### Counterexamples: the two boundary cases differ -/

/-- Cochrane (2023), §22.7, p. 508 (tool): a deterministic disturbance is adapted and known at
date 0. -/
theorem det_known (c : ℕ → ℝ) :
    𝔼.Adapted (fun t (_ : Ω) => c t) ∧ ∀ s, 𝔼.E 0 (fun (_ : Ω) => c s) = fun _ => c s :=
  ⟨fun t => 𝔼.const t (c t), fun s => 𝔼.const 0 (c s)⟩

/-- Cochrane (2023), §22.7, p. 508 (tool): with a deterministic disturbance the realised sums are
deterministic. -/
theorem pathSum_det (φ : ℝ) (c : ℕ → ℝ) (t : ℕ) (ω : Ω) :
    pathSum φ (fun t (_ : Ω) => c t) t ω = ∑ s ∈ Finset.range t, φ ^ s * c s := by
  simp [pathSum, Finset.sum_apply]

/-- Cochrane (2023), §22.7, p. 508 (a deterministic disturbance at `φ² = 1`, every expectation
system on a nonempty state space): a bounded solution exists iff the real partial sums
`∑_{s<t} φˢ c_s` are bounded. -/
theorem det_iff [Nonempty Ω] {φ : ℝ} (hφ : φ ^ 2 = 1) (c : ℕ → ℝ) :
    HasBddSol 𝔼 φ (fun t _ => c t) ↔ ∃ C, ∀ t, |∑ s ∈ Finset.range t, φ ^ s * c s| ≤ C := by
  obtain ⟨ha, h0⟩ := det_known 𝔼 (Ω := Ω) c
  rw [(exists_iff_known 𝔼 hφ ha h0).1]
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun t => by rw [← pathSum_det φ c t ω]; exact hC t ω⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun t ω' => by rw [pathSum_det]; exact hC t⟩

/-- Cochrane (2023), §22.7, p. 508 (counterexample): a constant disturbance `u_{i,t} = c ≠ 0` has
no bounded solution at `φ = 1` (the partial sums `t c` diverge). -/
theorem const_phi_one_none [Nonempty Ω] {c : ℝ} (hc : c ≠ 0) :
    ¬ HasBddSol 𝔼 1 (fun _ _ => c) := by
  rw [det_iff 𝔼 (by norm_num) (fun _ => c)]
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |c|)
  have h := hC n
  simp only [one_pow, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, abs_mul,
    Nat.abs_cast] at h
  rw [div_lt_iff₀ (abs_pos.2 hc)] at hn
  linarith

/-- Cochrane (2023), §22.7, p. 508 (counterexample): at `φ = −1` the same constant disturbance
has the bounded solution `π_t = c/2`. -/
theorem const_phi_neg_one_sol (c : ℝ) : HasBddSol 𝔼 (-1) (fun _ _ => c) := by
  refine ⟨fun _ _ => c / 2, fun t => 𝔼.const t _, ⟨|c / 2|, fun _ _ => le_rfl⟩, fun t => ?_⟩
  rw [𝔼.const]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), §22.7, p. 508 (counterexample): the alternating disturbance
`u_{i,t} = c(−1)ᵗ` has the bounded solution `π_t = c(1 − (−1)ᵗ)/2` at `φ = 1`. -/
theorem alt_phi_one_sol (c : ℝ) : HasBddSol 𝔼 1 (fun t _ => c * (-1) ^ t) := by
  refine ⟨fun t _ => c * (1 - (-1) ^ t) / 2, fun t => 𝔼.const t _, ⟨|c|, fun t _ => ?_⟩,
    fun t => ?_⟩
  · rw [abs_div, abs_mul, abs_two]
    have h : |1 - (-1 : ℝ) ^ t| ≤ 2 := by
      rcases neg_one_pow_eq_or ℝ t with h | h <;> rw [h] <;> norm_num
    nlinarith [abs_nonneg c]
  · rw [𝔼.const]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
    ring

/-- Cochrane (2023), §22.7, p. 508 (counterexample): at `φ = −1` the alternating disturbance
`u_{i,t} = c(−1)ᵗ`, `c ≠ 0`, has no bounded solution. -/
theorem alt_phi_neg_one_none [Nonempty Ω] {c : ℝ} (hc : c ≠ 0) :
    ¬ HasBddSol 𝔼 (-1) (fun t _ => c * (-1) ^ t) := by
  rw [det_iff 𝔼 (by norm_num) (fun t => c * (-1) ^ t)]
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |c|)
  have e : ∑ s ∈ Finset.range n, (-1 : ℝ) ^ s * (c * (-1) ^ s) = n * c := by
    rw [Finset.sum_congr rfl fun s _ => show (-1 : ℝ) ^ s * (c * (-1) ^ s) = c by
      rw [mul_left_comm, ← mul_pow]; norm_num]
    simp
  have h := hC n
  rw [e, abs_mul, Nat.abs_cast] at h
  rw [div_lt_iff₀ (abs_pos.2 hc)] at hn
  linarith

/-- Cochrane (2023), §22.7, p. 508 (counterexample): a disturbance that dies out,
`u_{i,t} = 1/(t + 1)`, still has no bounded solution at `φ = 1` (the harmonic series diverges). -/
theorem harmonic_phi_one_none [Nonempty Ω] :
    ¬ HasBddSol 𝔼 1 (fun t _ => 1 / ((t : ℝ) + 1)) := by
  rw [det_iff 𝔼 (by norm_num) (fun t => 1 / ((t : ℝ) + 1))]
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop C).exists
  have h := (le_abs_self _).trans (hC n)
  simp only [one_pow, one_mul] at h
  linarith

/-- Cochrane (2023), §22.7, p. 508 (tool): the alternating harmonic partial sums are bounded. -/
theorem altHarmonic_bdd :
    ∃ C, ∀ t, |∑ s ∈ Finset.range t, (-1 : ℝ) ^ s * (1 / ((s : ℝ) + 1))| ≤ C := by
  have hanti : Antitone fun s : ℕ => 1 / ((s : ℝ) + 1) := fun a b hab => by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have h0 : Tendsto (fun s : ℕ => 1 / ((s : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨R, -, hR⟩ := cauchySeq_bdd (hanti.cauchySeq_alternating_series_of_tendsto_zero h0)
  refine ⟨R, fun t => ?_⟩
  have := hR t 0
  rw [Real.dist_eq] at this
  simpa using this.le

/-- Cochrane (2023), §22.7, p. 508 (counterexample): at `φ = 1` the alternating vanishing
disturbance `u_{i,t} = (−1)ᵗ/(t + 1)` has a bounded solution. -/
theorem altHarmonic_phi_one_sol [Nonempty Ω] :
    HasBddSol 𝔼 1 (fun t _ => (-1) ^ t * (1 / ((t : ℝ) + 1))) := by
  rw [det_iff 𝔼 (by norm_num) (fun t => (-1) ^ t * (1 / ((t : ℝ) + 1)))]
  simpa only [one_pow, one_mul] using altHarmonic_bdd

/-- Cochrane (2023), §22.7, p. 508 (counterexample): at `φ = −1` the alternating vanishing
disturbance `u_{i,t} = (−1)ᵗ/(t + 1)` has no bounded solution. -/
theorem altHarmonic_phi_neg_one_none [Nonempty Ω] :
    ¬ HasBddSol 𝔼 (-1) (fun t _ => (-1) ^ t * (1 / ((t : ℝ) + 1))) := by
  rw [det_iff 𝔼 (by norm_num) (fun t => (-1) ^ t * (1 / ((t : ℝ) + 1)))]
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop C).exists
  have e : ∑ s ∈ Finset.range n, (-1 : ℝ) ^ s * ((-1) ^ s * (1 / ((s : ℝ) + 1))) =
      ∑ s ∈ Finset.range n, 1 / ((s : ℝ) + 1) :=
    Finset.sum_congr rfl fun s _ => by rw [← mul_assoc, ← mul_pow]; norm_num
  have h := (le_abs_self _).trans (hC n)
  rw [e] at h
  linarith

/-- Cochrane (2023), §22.7, pp. 508–509 (the boundary cases differ in the Leeper model): with
`0 < γ < 2` and a constant monetary disturbance `u_i = c ≠ 0`, there is no admissible equilibrium
at `φ = 1` and there are uncountably many at `φ = −1`. -/
theorem leeper_const [Nonempty Ω] {ρ γ Ms c : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hγ : 0 < γ ∧ γ < 2) (hc : c ≠ 0) {us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us) (hK : 𝔼.E 0 K = K) :
    (¬ ∃ x, LeeperEqm 𝔼 ρ 1 γ (fun _ _ => c) us K x ∧ Admissible 𝔼 ρ x) ∧
      ¬ {x | LeeperEqm 𝔼 ρ (-1) γ (fun _ _ => c) us K x ∧ Admissible 𝔼 ρ x}.Countable :=
  ⟨fun h => const_phi_one_none 𝔼 hc
      ((leeper_unit_dichotomy 𝔼 hρ0 hρ1 (by norm_num) hγ hus husa hK).1.1 h),
    (leeper_unit_dichotomy 𝔼 hρ0 hρ1 (by norm_num) hγ hus husa hK).2
      ((leeper_unit_dichotomy 𝔼 hρ0 hρ1 (by norm_num) hγ hus husa hK).1.2
        (const_phi_neg_one_sol 𝔼 c))⟩

/-- Cochrane (2023), §22.7, pp. 508–509 (a vanishing disturbance is not enough): with
`0 < γ < 2` and `u_{i,t} = 1/(t + 1)` the Leeper model has no admissible equilibrium at `φ = 1`. -/
theorem leeper_harmonic [Nonempty Ω] {ρ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hγ : 0 < γ ∧ γ < 2) {us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us) (hK : 𝔼.E 0 K = K) :
    ¬ ∃ x, LeeperEqm 𝔼 ρ 1 γ (fun t _ => 1 / ((t : ℝ) + 1)) us K x ∧ Admissible 𝔼 ρ x :=
  fun h => harmonic_phi_one_none 𝔼
    ((leeper_unit_dichotomy 𝔼 hρ0 hρ1 (by norm_num) hγ hus husa hK).1.1 h)

end Cochrane.ObservationalEquivalence.TidyR5UnitRoot
