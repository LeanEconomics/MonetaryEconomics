/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.MarkovRegimesGeneral
import ObservationalEquivalence.MarkovRegimesGeneralMeasure

/-!
# `N`-regime Markov switching in an abstract expectation system

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 24, §24.2, pp. 522–523 (Davig and
Leeper (2006, 2007): rule coefficients switch according to a Markov process; "the Markov
assumption, with exactly two (or even N) states", p. 523), and Chapter 22, §22.3, p. 500.

`MarkovRegimes.abstract_homog_eq_zero` and `MarkovRegimes.abstract_homog_nonzero` prove the
two-regime, positive-coefficient dichotomy in any `ExpectationSystem` carrying a Markov regime
process (`MarkovRegimes.MarkovRegime`: `E_t f(S_{t+1}) = ∑_j P_{S_t j} f(j)`). This module gives
the `N`-regime, any-sign analogues and finds the right hypothesis for them.

## Main results

* `MarkovRegimeN`: the `N`-regime Markov property, `E_t f(S_{t+1}) = ∑_j P_{S_t j} f(j)`.
* `absN_homog_eq_zero` (**uniqueness**): if every `φ_i ≠ 0` and the spectral radius of `|Φ|⁻¹P`
  is `< 1` (`GenCondition`), every bounded solution of `E_t π_{t+1} = φ_{S_t} π_t` is zero; and
  `absN_unique`, two bounded solutions of the model with a disturbance coincide. Only the Markov
  property is used, with coefficients of any sign.
* `absN_homog_nonzero_of_not_naive`: if some `φ_i = 0`, or the spectral radius of `Φ⁻¹P`
  itself is not `< 1`, there is a nonzero bounded solution (all regimes possible at date `0`).
* `absN_pos_dichotomy`: for `φ_i > 0` and any `N`, a nonzero bounded solution exists iff the
  condition fails. The two-regime results are the case `N = 2` (`two_regime_eq_zero`,
  `two_regime_nonzero`).
* **The Markov property alone does not suffice for signs** (`markov_only_nonzero_fails`): in the
  two-state system `avgSystem` (`E_t x = (x(0) + x(1))/2`) with the Markov regime `avgRegime`
  (`p_ij = ½`) and `φ = (½, −½)`, the condition fails (`avg_not_genCondition`) but every solution
  of the homogeneous model is zero (`avg_homog_zero`). There the regime is not known at date `t`
  (`avgRegime_not_adapted`).
* `HistMarkovN` (**the right hypothesis**): the forecast of any function of the next node of the
  regime tree is the tree's forecast,
  `E_t G(S_{t+1}, (S_t, …, S_0)) = ∑_j P_{S_t j} G(j, (S_t, …, S_0))`. It implies the Markov
  property (`HistMarkovN.toMarkov`) and that the regime is known (`HistMarkovN.adapted`).
  Under it: `hist_twisted` (the sign-twisted sunspot `π_t = s_t x_t(S_t)`), `hist_dichotomy`
  (**a nonzero bounded homogeneous solution exists iff the condition fails**), `tree_transfer`
  (every solution on the regime tree of `MarkovRegimesGeneral` is a solution in the system), and
  `hist_determinate_iff` (**for every bounded disturbance driven by the regime history there is
  exactly one bounded equilibrium iff `GenCondition`**, the condition of
  `MarkovRegimesGeneral.determinate_iff`).
* **Scope.** With non-degenerate transitions neither `HistMarkovN` nor a known Markov regime has a
  constructible model (modules TidyR6MarkovNoGo and TidyR6MarkovInstances: forecasts are atomless,
  never finitely supported, and no countable state space works). The abstract theorems are
  instantiated on degenerate chains in TidyR6MarkovInstances; the substantive non-degenerate
  versions are `MarkovRegimesGeneral.determinate_iff` and
  `MarkovRegimesGeneralMeasure.meas_determinate_iff`. The Markov-property-only theorems are
  instantiable both with a known degenerate regime and, as with `avgRegime`, with a non-degenerate
  regime that is not known.
-/

namespace Cochrane.ObservationalEquivalence.TidyR6MarkovAbstractN

open Filter Topology
open Cochrane.ObservationalEquivalence.MarkovRegimesGeneral
open scoped Matrix ENNReal NNReal

variable {Ω : Type*} {N : ℕ}

/-- Cochrane (2023), p. 522: the past regimes before date `t`, most recent first:
`pastOf S t ω = [S_{t−1}, …, S_0]`, so the regime-tree node at date `t` is
`(S_t, pastOf S t)`. -/
def pastOf (S : ℕ → Ω → Fin N) : ℕ → Ω → List (Fin N)
  | 0, _ => []
  | t + 1, ω => S t ω :: pastOf S t ω

/-- Cochrane (2023), eqs. (22.3)–(22.4), p. 500, with Markov switching (p. 522): the homogeneous
model `E_t π_{t+1} = φ_{S_t} π_t` at every date. -/
def Homog (𝔼 : ExpectationSystem Ω) (S : ℕ → Ω → Fin N) (φ : Fin N → ℝ) (e : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t, 𝔼.E t (e (t + 1)) = fun ω => φ (S t ω) * e t ω

/-- Cochrane (2023), eqs. (22.3)–(22.4), p. 500, with Markov switching (p. 522): the model
`E_t π_{t+1} = φ_{S_t} π_t + u_t` at every date. -/
def Sol (𝔼 : ExpectationSystem Ω) (S : ℕ → Ω → Fin N) (φ : Fin N → ℝ) (u π : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t, 𝔼.E t (π (t + 1)) = fun ω => φ (S t ω) * π t ω + u t ω

variable (𝔼₀ : ExpectationSystem Ω) (T₀ : TransitionN N)

/-- Cochrane (2023), p. 523 ("exactly two (or even N) states"): an `N`-state Markov regime process
in an expectation system, `E_t f(S_{t+1}) = ∑_j P_{S_t j} f(j)`. -/
structure MarkovRegimeN where
  /-- the regime process -/
  S : ℕ → Ω → Fin N
  /-- the Markov property -/
  markov : ∀ t (f : Fin N → ℝ), 𝔼₀.E t (f ∘ S (t + 1)) = fun ω => ∑ j, T₀.P (S t ω) j * f j

/-- Cochrane (2023), pp. 522–523: an `N`-state regime process whose forecasts are those of the
regime tree — for every function `G` of the next node,
`E_t G(S_{t+1}, (S_t, …, S_0)) = ∑_j P_{S_t j} G(j, (S_t, …, S_0))`.
**Scope:** with non-degenerate transitions (two positive entries in every row of `P`) the tree
hypothesis has no constructible model: the module TidyR6MarkovInstances proves that every date-`0`
forecast then gives weight zero to every single state, and TidyR6MarkovNoGo that no forecast is
a finite combination of values and no countable state space works. The buildable models have
degenerate (deterministic) transitions, where the theorem is instantiated in
TidyR6MarkovInstances; the substantive non-degenerate versions are
`MarkovRegimesGeneral.determinate_iff` (regime tree) and
`MarkovRegimesGeneralMeasure.meas_determinate_iff` (probability space). -/
structure HistMarkovN where
  /-- the regime process -/
  S : ℕ → Ω → Fin N
  /-- the forecast of the next node is the regime tree's -/
  hist : ∀ t (G : NodeN N → ℝ), 𝔼₀.E t (fun ω => G (S (t + 1) ω, pastOf S (t + 1) ω)) =
    fun ω => ∑ j, T₀.P (S t ω) j * G (j, pastOf S (t + 1) ω)

variable {𝔼₀ T₀}

/-! ### Uniqueness from the Markov property alone -/

/-- Cochrane (2023), p. 523 (iterating the expectational recursion, any signs): a bounded solution
of the homogeneous model satisfies `|π_t| ≤ B ∑_j ((|Φ|⁻¹P)^k)_{S_t j}` for every `k`.
Generalises `MarkovRegimes.abstract_bound`; abstract form of
`MarkovRegimesGeneral.abs_le_pow_bound`. -/
theorem absN_bound {𝔼 : ExpectationSystem Ω} {T : TransitionN N} (R : MarkovRegimeN 𝔼 T)
    {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0) {e : ℕ → Ω → ℝ} (he : Homog 𝔼 R.S φ e) {B : ℝ}
    (hB : ∀ t ω, |e t ω| ≤ B) (k : ℕ) :
    ∀ t ω, |e t ω| ≤ B * ∑ j, (absM T φ ^ k) (R.S t ω) j := by
  induction k with
  | zero =>
    intro t ω
    simp only [pow_zero, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      mul_one]
    exact hB t ω
  | succ k ih =>
    intro t ω
    set f : Fin N → ℝ := fun l => B * ∑ j, (absM T φ ^ k) l j with hf
    have hpos : 0 < |φ (R.S t ω)| := abs_pos.2 (hφ _)
    have hup : e (t + 1) ≤ f ∘ R.S (t + 1) :=
      fun ω' => (le_abs_self _).trans (ih (t + 1) ω')
    have hlo : -(f ∘ R.S (t + 1)) ≤ e (t + 1) := fun ω' => by
      have h1 := ih (t + 1) ω'
      have h2 := neg_abs_le (e (t + 1) ω')
      simp only [Pi.neg_apply, Function.comp_apply, hf]
      linarith
    have h1 := 𝔼.mono t hup ω
    have h2 := 𝔼.mono t hlo ω
    rw [map_neg, R.markov t f] at h2
    rw [R.markov t f] at h1
    have hE : 𝔼.E t (e (t + 1)) ω = φ (R.S t ω) * e t ω := congrFun (he t) ω
    have hval : ∑ j, T.P (R.S t ω) j * f j =
        |φ (R.S t ω)| * (B * ∑ l, (absM T φ ^ (k + 1)) (R.S t ω) l) := by
      have hs := sum_pow_succ (absM T φ) k (R.S t ω) (fun _ => 1)
      simp only [mul_one] at hs
      rw [row_absM T (hφ _), hs]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [Pi.neg_apply] at h2
    beta_reduce at h1
    rw [hE, hval] at h1 h2
    have habs : |φ (R.S t ω)| * |e t ω| ≤
        |φ (R.S t ω)| * (B * ∑ l, (absM T φ ^ (k + 1)) (R.S t ω) l) := by
      rw [← abs_mul, abs_le]
      exact ⟨by linarith, h1⟩
    exact le_of_mul_le_mul_left habs hpos

/-- Cochrane (2023), pp. 522–523 (**uniqueness, `N` regimes, any signs, abstract system**): if
every `φ_i ≠ 0` and the spectral radius of `|Φ|⁻¹P` is `< 1`, in any expectation system with a
Markov regime process the only bounded solution of the homogeneous model is zero.
Generalises `MarkovRegimes.abstract_homog_eq_zero`; abstract form of
`MarkovRegimesGeneral.homog_eq_zero`. -/
theorem absN_homog_eq_zero {𝔼 : ExpectationSystem Ω} {T : TransitionN N}
    (R : MarkovRegimeN 𝔼 T) {φ : Fin N → ℝ} (hc : GenCondition T φ) {e : ℕ → Ω → ℝ}
    (he : Homog 𝔼 R.S φ e) (hb : BoundedProc e) : e = 0 := by
  obtain ⟨B, hB⟩ := hb
  funext t ω
  have hlim : Tendsto (fun k => B * ∑ j, (absM T φ ^ k) (R.S t ω) j) atTop (𝓝 0) := by
    have hj : ∀ j ∈ Finset.univ,
        Tendsto (fun k => (absM T φ ^ k) (R.S t ω) j) atTop (𝓝 0) :=
      fun j _ => (summable_abs_pow_entry hc.2 _ j).of_abs.tendsto_atTop_zero
    simpa using (tendsto_finsetSum Finset.univ hj).const_mul B
  have hle : |e t ω| ≤ 0 :=
    ge_of_tendsto' hlim fun k => absN_bound R hc.1 he hB k t ω
  simpa using abs_nonpos_iff.mp hle

/-- Cochrane (2023), pp. 522–523: the difference of two solutions of the model solves the
homogeneous model.
Restates `MarkovRegimesGeneral.solves_sub` in an abstract system. -/
theorem sol_sub {𝔼 : ExpectationSystem Ω} {S : ℕ → Ω → Fin N} {φ : Fin N → ℝ}
    {u π₁ π₂ : ℕ → Ω → ℝ} (h₁ : Sol 𝔼 S φ u π₁) (h₂ : Sol 𝔼 S φ u π₂) :
    Homog 𝔼 S φ (π₁ - π₂) := by
  intro t
  rw [show (π₁ - π₂) (t + 1) = π₁ (t + 1) - π₂ (t + 1) from rfl, map_sub, h₁ t, h₂ t]
  funext ω
  simp only [Pi.sub_apply]
  ring

/-- Cochrane (2023), pp. 522–523 (**at most one bounded equilibrium**): under the condition, in
any expectation system with a Markov regime process, two bounded solutions of
`E_t π_{t+1} = φ_{S_t} π_t + u_t` coincide, whatever the disturbance `u`. -/
theorem absN_unique {𝔼 : ExpectationSystem Ω} {T : TransitionN N} (R : MarkovRegimeN 𝔼 T)
    {φ : Fin N → ℝ} (hc : GenCondition T φ) {u π₁ π₂ : ℕ → Ω → ℝ} (h₁ : Sol 𝔼 R.S φ u π₁)
    (h₂ : Sol 𝔼 R.S φ u π₂) (hb₁ : BoundedProc π₁) (hb₂ : BoundedProc π₂) : π₁ = π₂ := by
  obtain ⟨B1, hB1⟩ := hb₁
  obtain ⟨B2, hB2⟩ := hb₂
  have h0 := absN_homog_eq_zero R hc (sol_sub h₁ h₂) ⟨B1 + B2, fun t ω => by
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hB1 t ω) (hB2 t ω))⟩
  exact sub_eq_zero.mp h0

/-! ### Non-uniqueness from the Markov property alone -/

/-- Cochrane (2023), p. 523 (**zero coefficients**): if `φ_i = 0` and regime `i` is possible at
date `0`, then `π_0 = 1{S_0 = i}`, `π_t = 0` for `t ≥ 1`, is a nonzero bounded solution of the
homogeneous model.
Abstract form of `MarkovRegimesGeneral.zero_coeff_homog` and
`MarkovRegimesGeneralMeasure.zero_coeff_homogM`. -/
theorem absN_zero_coeff_homog {𝔼 : ExpectationSystem Ω} {T : TransitionN N}
    (R : MarkovRegimeN 𝔼 T) {φ : Fin N → ℝ} {i : Fin N} (hφ : φ i = 0)
    (hi : ∃ ω, R.S 0 ω = i) : ∃ e, Homog 𝔼 R.S φ e ∧ BoundedProc e ∧ e ≠ 0 := by
  classical
  refine ⟨fun t ω => if t = 0 ∧ R.S 0 ω = i then 1 else 0, fun t => ?_, ⟨1, fun t ω => ?_⟩, ?_⟩
  · have h0 : (fun ω => if t + 1 = 0 ∧ R.S 0 ω = i then (1 : ℝ) else 0) = 0 := by
      funext ω
      simp
    change 𝔼.E t (fun ω => if t + 1 = 0 ∧ R.S 0 ω = i then (1 : ℝ) else 0) =
      fun ω => φ (R.S t ω) * (if t = 0 ∧ R.S 0 ω = i then 1 else 0)
    rw [h0, map_zero]
    funext ω
    split_ifs with ht
    · obtain ⟨rfl, hω⟩ := ht
      simp [hω, hφ]
    · simp
  · change |(if t = 0 ∧ R.S 0 ω = i then (1 : ℝ) else 0)| ≤ 1
    split_ifs <;> simp
  · intro h0
    obtain ⟨ω, hω⟩ := hi
    have := congrFun (congrFun h0 0) ω
    simp [hω] at this

/-- Cochrane (2023), p. 523 (**the naive condition fails**): if every `φ_i ≠ 0` and the spectral
radius of `Φ⁻¹P` is not `< 1`, then `π_t = x_t(S_t)` with `x_t = Φ⁻¹P x_{t+1}` is a nonzero
bounded solution of the homogeneous model, using the Markov property alone.
Abstract form of `MarkovRegimesGeneral.homog_nonzero_of_not_naive`. -/
theorem absN_homog_nonzero_naive {𝔼 : ExpectationSystem Ω} {T : TransitionN N}
    (R : MarkovRegimeN 𝔼 T) {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0)
    (h : ¬ specRad (sgnM T φ) < 1) (hS0 : ∀ i, ∃ ω, R.S 0 ω = i) :
    ∃ e, Homog 𝔼 R.S φ e ∧ BoundedProc e ∧ e ≠ 0 := by
  obtain ⟨x, hx, ⟨B, hB⟩, i₀, hi₀⟩ := exists_bdd_backward h
  refine ⟨fun t ω => x t (R.S t ω), fun t => ?_, ⟨B, fun t ω => hB _ _⟩, ?_⟩
  · change 𝔼.E t (x (t + 1) ∘ R.S (t + 1)) = _
    rw [R.markov t (x (t + 1))]
    funext ω
    change ∑ j, T.P (R.S t ω) j * x (t + 1) j = φ (R.S t ω) * x t (R.S t ω)
    rw [row_sgnM T (hφ _), hx t]
    rfl
  · intro h0
    obtain ⟨ω, hω⟩ := hS0 i₀
    have := congrFun (congrFun h0 0) ω
    simp only [Pi.zero_apply, hω] at this
    exact hi₀ this

/-- Cochrane (2023), p. 523: if all regimes are possible at date `0` and the naive condition
(`NaiveCondition`: every `φ_i ≠ 0` and spectral radius of `Φ⁻¹P` `< 1`) fails, the homogeneous
model has a nonzero bounded solution, using the Markov property alone. -/
theorem absN_homog_nonzero_of_not_naive {𝔼 : ExpectationSystem Ω} {T : TransitionN N}
    (R : MarkovRegimeN 𝔼 T) {φ : Fin N → ℝ} (h : ¬ NaiveCondition T φ)
    (hS0 : ∀ i, ∃ ω, R.S 0 ω = i) : ∃ e, Homog 𝔼 R.S φ e ∧ BoundedProc e ∧ e ≠ 0 := by
  by_cases h0 : ∀ i, φ i ≠ 0
  · exact absN_homog_nonzero_naive R h0 (fun hs => h ⟨h0, hs⟩) hS0
  · push Not at h0
    obtain ⟨i, hi⟩ := h0
    exact absN_zero_coeff_homog R hi (hS0 i)

/-- Cochrane (2023), p. 523: for positive coefficients `|Φ|⁻¹P = Φ⁻¹P`.
Generalises `MarkovRegimesGeneral.absM_ofTwo` to `N` regimes. -/
theorem sgnM_eq_absM (T : TransitionN N) {φ : Fin N → ℝ} (hφ : ∀ i, 0 < φ i) :
    sgnM T φ = absM T φ := by
  ext i j
  simp [sgnM, absM, abs_of_pos (hφ i)]

/-- Cochrane (2023), pp. 522–523 (**the dichotomy for `N` regimes and `φ_i > 0`, abstract
system**): if all regimes are possible at date `0`, in any expectation system with a Markov
regime process the homogeneous model has a nonzero bounded solution iff the spectral radius of
`|Φ|⁻¹P` is not `< 1`.
Generalises `MarkovRegimes.abstract_homog_nonzero` and `MarkovRegimes.abstract_homog_eq_zero`. -/
theorem absN_pos_dichotomy {𝔼 : ExpectationSystem Ω} {T : TransitionN N}
    (R : MarkovRegimeN 𝔼 T) {φ : Fin N → ℝ} (hφ : ∀ i, 0 < φ i)
    (hS0 : ∀ i, ∃ ω, R.S 0 ω = i) :
    (∃ e, Homog 𝔼 R.S φ e ∧ BoundedProc e ∧ e ≠ 0) ↔ ¬ GenCondition T φ := by
  constructor
  · rintro ⟨e, he, hb, hne⟩ hc
    exact hne (absN_homog_eq_zero R hc he hb)
  · intro hc
    have hs : ¬ specRad (sgnM T φ) < 1 := by
      rw [sgnM_eq_absM T hφ]
      exact fun h => hc ⟨fun i => (hφ i).ne', h⟩
    exact absN_homog_nonzero_naive R (fun i => (hφ i).ne') hs hS0

/-! ### Two regimes: the special case -/

/-- Cochrane (2023), p. 522: a two-state Markov regime of `MarkovRegimes` as an `N = 2` Markov
regime. -/
def ofRegime2 {𝔼 : ExpectationSystem Ω} {T : MarkovRegimes.Transition}
    (R : MarkovRegimes.MarkovRegime 𝔼 T) : MarkovRegimeN 𝔼 (ofTwo T) where
  S := R.S
  markov := R.markov

/-- Cochrane (2023), pp. 522–523 (**`MarkovRegimes.abstract_homog_eq_zero` recovered**): the
two-regime uniqueness result is the case `N = 2`, `φ > 0` of `absN_homog_eq_zero`. -/
theorem two_regime_eq_zero {𝔼 : ExpectationSystem Ω} {T : MarkovRegimes.Transition}
    (R : MarkovRegimes.MarkovRegime 𝔼 T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : MarkovRegimes.DLCondition T φ) {e : ℕ → Ω → ℝ}
    (he : ∀ t, 𝔼.E t (e (t + 1)) = fun ω => φ (R.S t ω) * e t ω) (hb : BoundedProc e) :
    e = 0 :=
  absN_homog_eq_zero (ofRegime2 R) ((dl_iff_genCondition T hφ).1 hdl) he hb

/-- Cochrane (2023), pp. 522–523 (**`MarkovRegimes.abstract_homog_nonzero` recovered**): the
two-regime non-uniqueness result is the case `N = 2`, `φ > 0` of `absN_pos_dichotomy`. -/
theorem two_regime_nonzero {𝔼 : ExpectationSystem Ω} {T : MarkovRegimes.Transition}
    (R : MarkovRegimes.MarkovRegime 𝔼 T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hndl : ¬ MarkovRegimes.DLCondition T φ) (hS0 : ∀ i, ∃ ω, R.S 0 ω = i) :
    ∃ e : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (e (t + 1)) = fun ω => φ (R.S t ω) * e t ω) ∧
      BoundedProc e ∧ e ≠ 0 :=
  (absN_pos_dichotomy (ofRegime2 R) hφ hS0).2 (mt (dl_iff_genCondition T hφ).2 hndl)

/-! ### The Markov property alone does not determine the any-sign case -/

/-- Cochrane (2023), p. 523: the averaging map `x ↦ (x(0) + x(1))/2` on two states. -/
noncomputable def avgMap : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := fun _ => (x 0 + x 1) / 2
  map_add' x y := by
    funext ω
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Cochrane (2023), p. 523: the two-state expectation system in which every forecast is the
average over both states, `E_t x = (x(0) + x(1))/2` at every date. -/
noncomputable def avgSystem : ExpectationSystem (Fin 2) where
  E := fun _ => avgMap
  const := fun _ c => by
    funext ω
    change (c + c) / 2 = c
    ring
  mono := fun _ x y h ω => by
    change (x 0 + x 1) / 2 ≤ (y 0 + y 1) / 2
    linarith [h 0, h 1]
  tower := fun _ x => by
    funext ω
    change ((x 0 + x 1) / 2 + (x 0 + x 1) / 2) / 2 = (x 0 + x 1) / 2
    ring
  known := fun _ x => by
    funext ω
    change ((x 0 + x 1) / 2 + (x 0 + x 1) / 2) / 2 = (x 0 + x 1) / 2
    ring

/-- Cochrane (2023), p. 523: in `avgSystem`, the regime `S_t(ω) = ω` is a Markov regime with
i.i.d. transitions `p_ij = ½` (`MarkovRegimesGeneral.egHalf`). -/
noncomputable def avgRegime : MarkovRegimeN avgSystem (ofTwo egHalf) where
  S := fun _ ω => ω
  markov := fun _ f => by
    funext ω
    change (f 0 + f 1) / 2 = ∑ j, (1 / 2 : ℝ) * f j
    rw [Fin.sum_univ_two]
    ring

/-- Cochrane (2023), p. 523: in `avgRegime` both regimes are possible at date `0`. -/
theorem avgRegime_initial (i : Fin 2) : ∃ ω, avgRegime.S 0 ω = i := ⟨i, rfl⟩

/-- Cochrane (2023), p. 523: in `avgSystem` the regime is not known at date `t`:
`E_t 1{S_t = 0} = ½ ≠ 1{S_t = 0}`. -/
theorem avgRegime_not_adapted (t : ℕ) :
    avgSystem.E t ((fun l : Fin 2 => if l = 0 then (1 : ℝ) else 0) ∘ avgRegime.S t) ≠
      (fun l : Fin 2 => if l = 0 then (1 : ℝ) else 0) ∘ avgRegime.S t := by
  intro h
  have h0 := congrFun h 0
  change ((if (0 : Fin 2) = 0 then (1 : ℝ) else 0) + (if (1 : Fin 2) = 0 then 1 else 0)) / 2 =
    (if (0 : Fin 2) = 0 then 1 else 0) at h0
  norm_num at h0

/-- Cochrane (2023), p. 523: with `p_ij = ½` and `φ = (½, −½)` the condition fails (the spectral
radius of `|Φ|⁻¹P = 2P` is `2`). -/
theorem avg_not_genCondition : ¬ GenCondition (ofTwo egHalf) ![1 / 2, -1 / 2] := fun h =>
  naive_not_sufficient.2 ((determinate_iff _ _).2 h)

/-- Cochrane (2023), p. 523: in `avgSystem` with `avgRegime` and `φ = (½, −½)`, every solution of
the homogeneous model — bounded or not — is zero. -/
theorem avg_homog_zero {e : ℕ → Fin 2 → ℝ}
    (he : Homog avgSystem avgRegime.S ![1 / 2, -1 / 2] e) : e = 0 := by
  have key : ∀ t, (e (t + 1) 0 + e (t + 1) 1) / 2 = 1 / 2 * e t 0 ∧
      (e (t + 1) 0 + e (t + 1) 1) / 2 = -1 / 2 * e t 1 := fun t =>
    ⟨congrFun (he t) 0, congrFun (he t) 1⟩
  have hsum : ∀ t, e t 0 + e t 1 = 0 := fun t => by
    obtain ⟨h1, h2⟩ := key t
    linarith
  funext t ω
  obtain ⟨h1, h2⟩ := key t
  have := hsum (t + 1)
  fin_cases ω
  · simp only [Fin.zero_eta, Fin.isValue, Pi.zero_apply]
    linarith
  · simp only [Fin.mk_one, Fin.isValue, Pi.zero_apply]
    linarith

/-- Cochrane (2023), pp. 522–523 (**the any-sign non-uniqueness result does not follow from the
Markov property**): it is false that in every expectation system with a Markov regime process
in which all regimes are possible at date `0`, failure of the condition gives a nonzero bounded
solution — `avgSystem` with `p_ij = ½`, `φ = (½, −½)` is a counterexample. -/
theorem markov_only_nonzero_fails :
    ¬ (∀ (Ω : Type) (𝔼 : ExpectationSystem Ω) (R : MarkovRegimeN 𝔼 (ofTwo egHalf)),
      (∀ i, ∃ ω, R.S 0 ω = i) → ¬ GenCondition (ofTwo egHalf) ![1 / 2, -1 / 2] →
        ∃ e, Homog 𝔼 R.S ![1 / 2, -1 / 2] e ∧ BoundedProc e ∧ e ≠ 0) := by
  intro h
  obtain ⟨e, he, -, hne⟩ := h (Fin 2) avgSystem avgRegime avgRegime_initial avg_not_genCondition
  exact hne (avg_homog_zero he)

/-! ### The tree hypothesis: the full any-sign dichotomy -/

namespace HistMarkovN

variable {𝔼 : ExpectationSystem Ω} {T : TransitionN N}

/-- Cochrane (2023), p. 522: the tree hypothesis implies the Markov property. -/
def toMarkov (R : HistMarkovN 𝔼 T) : MarkovRegimeN 𝔼 T where
  S := R.S
  markov := fun t f => R.hist t (fun n => f n.1)

/-- Cochrane (2023), p. 522: under the tree hypothesis the regime is known at each date,
`E_t f(S_t) = f(S_t)`. -/
theorem adapted (R : HistMarkovN 𝔼 T) (t : ℕ) (f : Fin N → ℝ) :
    𝔼.E t (f ∘ R.S t) = f ∘ R.S t := by
  have h := R.hist t (fun n => n.2.head?.elim 0 f)
  change 𝔼.E t (f ∘ R.S t) = fun ω => ∑ j, T.P (R.S t ω) j * f (R.S t ω) at h
  rw [h]
  funext ω
  rw [← Finset.sum_mul, T.rowSum, one_mul]
  rfl

end HistMarkovN

/-- Cochrane (2023), pp. 522–523 (**the sign-twisted sunspot in an abstract system**): under the
tree hypothesis, if every `φ_i ≠ 0` and the spectral radius of `|Φ|⁻¹P` is not `< 1`, then
`π_t = s_t x_t(S_t)`, with `s_t = ∏_{τ<t} sgn φ_{S_τ}` and `x_t = |Φ|⁻¹P x_{t+1}`, is a nonzero
bounded solution of the homogeneous model.
**Scope:** with non-degenerate transitions (two positive entries in every row of `P`) the tree
hypothesis has no constructible model: the module TidyR6MarkovInstances proves that every date-`0`
forecast then gives weight zero to every single state, and TidyR6MarkovNoGo that no forecast is
a finite combination of values and no countable state space works. The buildable models have
degenerate (deterministic) transitions, where the theorem is instantiated in
TidyR6MarkovInstances; the substantive non-degenerate versions are
`MarkovRegimesGeneral.determinate_iff` (regime tree) and
`MarkovRegimesGeneralMeasure.meas_determinate_iff` (probability space).
Abstract form of `MarkovRegimesGeneral.homog_nonzero_of_not` and
`MarkovRegimesGeneralMeasure.twisted_solves`. -/
theorem hist_twisted {𝔼 : ExpectationSystem Ω} {T : TransitionN N} (R : HistMarkovN 𝔼 T)
    {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0) (h : ¬ specRad (absM T φ) < 1)
    (hS0 : ∀ i, ∃ ω, R.S 0 ω = i) : ∃ e, Homog 𝔼 R.S φ e ∧ BoundedProc e ∧ e ≠ 0 := by
  obtain ⟨x, hx, ⟨B, hB⟩, i₀, hi₀⟩ := exists_bdd_backward h
  refine ⟨fun t ω => histSign φ (pastOf R.S t ω) * x t (R.S t ω), fun t => ?_,
    ⟨B, fun t ω => ?_⟩, ?_⟩
  · have hm : 𝔼.E t (fun ω => histSign φ (pastOf R.S (t + 1) ω) * x (t + 1) (R.S (t + 1) ω)) =
        fun ω => ∑ j, T.P (R.S t ω) j * (histSign φ (pastOf R.S (t + 1) ω) * x (t + 1) j) :=
      R.hist t (fun n => histSign φ n.2 * x (t + 1) n.1)
    change 𝔼.E t (fun ω => histSign φ (pastOf R.S (t + 1) ω) * x (t + 1) (R.S (t + 1) ω)) = _
    rw [hm]
    funext ω
    have hrow : ∑ j, T.P (R.S t ω) j * x (t + 1) j = |φ (R.S t ω)| * x t (R.S t ω) := by
      rw [row_absM T (hφ _), hx t]
      rfl
    change ∑ j, T.P (R.S t ω) j * (histSign φ (R.S t ω :: pastOf R.S t ω) * x (t + 1) j) =
      φ (R.S t ω) * (histSign φ (pastOf R.S t ω) * x t (R.S t ω))
    calc ∑ j, T.P (R.S t ω) j * (histSign φ (R.S t ω :: pastOf R.S t ω) * x (t + 1) j)
        = histSign φ (R.S t ω :: pastOf R.S t ω) * ∑ j, T.P (R.S t ω) j * x (t + 1) j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = φ (R.S t ω) * (histSign φ (pastOf R.S t ω) * x t (R.S t ω)) := by
          rw [hrow, histSign_cons]
          linear_combination (histSign φ (pastOf R.S t ω) * x t (R.S t ω)) *
            sgn_mul_abs (φ (R.S t ω))
  · change |histSign φ (pastOf R.S t ω) * x t (R.S t ω)| ≤ B
    rw [abs_mul, abs_histSign, one_mul]
    exact hB _ _
  · intro h0
    obtain ⟨ω, hω⟩ := hS0 i₀
    have := congrFun (congrFun h0 0) ω
    change histSign φ [] * x 0 (R.S 0 ω) = 0 at this
    simp only [histSign, List.map_nil, List.prod_nil, one_mul, hω] at this
    exact hi₀ this

/-- Cochrane (2023), pp. 522–523 (**the `N`-regime, any-sign dichotomy in an abstract system**):
under the tree hypothesis, with all regimes possible at date `0`, the homogeneous model has a
nonzero bounded solution iff the condition fails (some `φ_i = 0`, or the spectral radius of
`|Φ|⁻¹P` is not `< 1`).
**Scope:** with non-degenerate transitions (two positive entries in every row of `P`) the tree
hypothesis has no constructible model: the module TidyR6MarkovInstances proves that every date-`0`
forecast then gives weight zero to every single state, and TidyR6MarkovNoGo that no forecast is
a finite combination of values and no countable state space works. The buildable models have
degenerate (deterministic) transitions, where the theorem is instantiated in
TidyR6MarkovInstances; the substantive non-degenerate versions are
`MarkovRegimesGeneral.determinate_iff` (regime tree) and
`MarkovRegimesGeneralMeasure.meas_determinate_iff` (probability space).
Abstract form of `MarkovRegimesGeneral.homog_eq_zero` with
`MarkovRegimesGeneral.homog_nonzero_of_not`. -/
theorem hist_dichotomy {𝔼 : ExpectationSystem Ω} {T : TransitionN N} (R : HistMarkovN 𝔼 T)
    {φ : Fin N → ℝ} (hS0 : ∀ i, ∃ ω, R.S 0 ω = i) :
    (∃ e, Homog 𝔼 R.S φ e ∧ BoundedProc e ∧ e ≠ 0) ↔ ¬ GenCondition T φ := by
  constructor
  · rintro ⟨e, he, hb, hne⟩ hc
    exact hne (absN_homog_eq_zero R.toMarkov hc he hb)
  · intro hc
    by_cases h0 : ∀ i, φ i ≠ 0
    · exact hist_twisted R h0 (fun hs => hc ⟨h0, hs⟩) hS0
    · push Not at h0
      obtain ⟨i, hi⟩ := h0
      exact absN_zero_coeff_homog R.toMarkov hi (hS0 i)

/-- Cochrane (2023), pp. 522–523 (**the regime tree inside the system**): under the tree
hypothesis, every solution `π` on the regime tree of `MarkovRegimesGeneral` with disturbance `u`
gives the solution `π_t = π(S_t, pastOf S t)` in the system, with disturbance
`u_t = u(S_t, pastOf S t)`.
**Scope:** with non-degenerate transitions (two positive entries in every row of `P`) the tree
hypothesis has no constructible model: the module TidyR6MarkovInstances proves that every date-`0`
forecast then gives weight zero to every single state, and TidyR6MarkovNoGo that no forecast is
a finite combination of values and no countable state space works. The buildable models have
degenerate (deterministic) transitions, where the theorem is instantiated in
TidyR6MarkovInstances; the substantive non-degenerate versions are
`MarkovRegimesGeneral.determinate_iff` (regime tree) and
`MarkovRegimesGeneralMeasure.meas_determinate_iff` (probability space). -/
theorem tree_transfer {𝔼 : ExpectationSystem Ω} {T : TransitionN N} (R : HistMarkovN 𝔼 T)
    {φ : Fin N → ℝ} {u π : NodeN N → ℝ} (h : Solves T φ u π) :
    Sol 𝔼 R.S φ (fun t ω => u (R.S t ω, pastOf R.S t ω))
      (fun t ω => π (R.S t ω, pastOf R.S t ω)) := by
  intro t
  change 𝔼.E t (fun ω => π (R.S (t + 1) ω, pastOf R.S (t + 1) ω)) = _
  rw [R.hist t π]
  funext ω
  exact h (R.S t ω) (pastOf R.S t ω)

/-- Cochrane (2023), pp. 522–523: determinacy in an abstract system under the tree hypothesis —
for every bounded disturbance driven by the regime history, `u_t = u(S_t, pastOf S t)`, there is
exactly one bounded solution. -/
def HDeterminate {𝔼 : ExpectationSystem Ω} {T : TransitionN N} (R : HistMarkovN 𝔼 T)
    (φ : Fin N → ℝ) : Prop :=
  ∀ u : NodeN N → ℝ, BoundedFn u →
    ∃! π : ℕ → Ω → ℝ, Sol 𝔼 R.S φ (fun t ω => u (R.S t ω, pastOf R.S t ω)) π ∧ BoundedProc π

/-- Cochrane (2023), pp. 522–523 (**Davig–Leeper for `N` regimes and any signs, in an abstract
expectation system**): under the tree hypothesis, with all regimes possible at date `0`, the model
`E_t π_{t+1} = φ_{S_t} π_t + u_t` has exactly one bounded equilibrium for every bounded
history-driven disturbance iff every `φ_i ≠ 0` and the spectral radius of `|Φ|⁻¹P` is `< 1` —
the condition of `MarkovRegimesGeneral.determinate_iff` on the regime tree.
**Scope:** with non-degenerate transitions (two positive entries in every row of `P`) the tree
hypothesis has no constructible model: the module TidyR6MarkovInstances proves that every date-`0`
forecast then gives weight zero to every single state, and TidyR6MarkovNoGo that no forecast is
a finite combination of values and no countable state space works. The buildable models have
degenerate (deterministic) transitions, where the theorem is instantiated in
TidyR6MarkovInstances; the substantive non-degenerate versions are
`MarkovRegimesGeneral.determinate_iff` (regime tree) and
`MarkovRegimesGeneralMeasure.meas_determinate_iff` (probability space). -/
theorem hist_determinate_iff {𝔼 : ExpectationSystem Ω} {T : TransitionN N}
    (R : HistMarkovN 𝔼 T) (φ : Fin N → ℝ) (hS0 : ∀ i, ∃ ω, R.S 0 ω = i) :
    HDeterminate R φ ↔ GenCondition T φ := by
  constructor
  · intro hd
    by_contra hc
    obtain ⟨e, he, hb, hne⟩ := (hist_dichotomy R hS0).2 hc
    obtain ⟨π, _, huniq⟩ := hd 0 ⟨0, fun n => by simp⟩
    have hz : ∀ x : ℕ → Ω → ℝ, Homog 𝔼 R.S φ x →
        Sol 𝔼 R.S φ (fun t ω => (0 : NodeN N → ℝ) (R.S t ω, pastOf R.S t ω)) x := by
      intro x hx t
      rw [hx t]
      funext ω
      simp
    have h0 : (0 : ℕ → Ω → ℝ) = π := huniq 0 ⟨hz 0 (fun t => by
      funext ω
      simp), ⟨0, fun t ω => by simp⟩⟩
    exact hne ((huniq e ⟨hz e he, hb⟩).trans h0.symm)
  · intro hc u ⟨U, hU⟩
    refine ⟨fun t ω => fwdSol T φ u (R.S t ω, pastOf R.S t ω),
      ⟨tree_transfer R (fwdSol_solves T hc hU), ?_⟩, ?_⟩
    · obtain ⟨B, hB⟩ := fwdSol_bounded T hc hU
      exact ⟨B, fun t ω => hB _⟩
    · rintro π ⟨hπ, hπb⟩
      obtain ⟨B, hB⟩ := fwdSol_bounded T hc hU
      exact absN_unique R.toMarkov hc hπ (tree_transfer R (fwdSol_solves T hc hU)) hπb
        ⟨B, fun t ω => hB _⟩

end Cochrane.ObservationalEquivalence.TidyR6MarkovAbstractN
