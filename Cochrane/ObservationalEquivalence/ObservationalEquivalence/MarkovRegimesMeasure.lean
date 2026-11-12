/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.ExpectationsMeasureIID
import ObservationalEquivalence.MarkovRegimes
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Markov-switching monetary policy on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 24, §24.2, pp. 522–523 (Davig and
Leeper (2006, 2007): policy-rule coefficients switch between regimes according to a Markov
process; "a time with `φ < 1` should be something like 'locally passive' or 'temporarily
passive'").

The module `MarkovRegimes` proves the Davig–Leeper determinacy condition on the regime tree and,
for an abstract `ExpectationSystem` that carries a Markov regime process, states the dichotomy for
systems that have one — but no pointwise-linear expectation system carries a non-degenerate chain.
Here the chain lives on a genuine infinite-horizon probability space.

## Main results

* `MeasMarkovRegime S T`: a regime process `S_t ∈ {0, 1}` adapted to a `MeasExpectationSystem`
  with the Markov property `E_t f(S_{t+1}) = ∑_j P_{S_t j} f(j)` a.e.; `MSolves`: the model
  `E_t π_{t+1} = φ_{S_t} π_t + u_t` a.e.
* `meas_homog_eq_zero`: under the Davig–Leeper condition every bounded adapted solution of the
  homogeneous model is zero a.e.; `fwdSolM_solves`, `fwdSolM_bdd`: the forward solution
  `π_t = ∑_k Δ_k(t)` exists and is bounded; `perron_solves`: when the condition fails,
  `π_t = w_{S_t}/r^t` is a nonzero bounded solution.
* `meas_determinate_iff` (**Davig–Leeper, genuinely**): if both regimes have positive probability
  at date `0`, the model has exactly one bounded adapted equilibrium (a.e.) for every bounded
  adapted disturbance iff `DLCondition`; `meas_determinate_iff_tree`, `meas_determinate_iff_tree`:
  the same condition as the tree result `determinate_iff` and as `dl_iff_schur`.
* The construction: `unifProb` (uniform law on `[0, 1]`), `chain T q` (`S_0 = 0` iff `U_0 < q`,
  `S_{t+1} = 0` iff `U_{t+1} < P_{S_t 0}`, with i.i.d. uniforms `U_t` under `Measure.infinitePi`),
  `chain_markov` (the Markov property), `chainRegime` (a `MeasMarkovRegime` of `iidSystem`),
  `chain_initial_pos`, `chain_singleton_null` (every path has probability zero: not a finite
  tree), `chain_determinate_iff`; examples `chain_temporarily_passive`, `chain_locally_active`.
-/

namespace Cochrane.ObservationalEquivalence.MarkovRegimesMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationsMeasure
open Cochrane.ObservationalEquivalence.ExpectationsMeasureIID
open Cochrane.ObservationalEquivalence.MarkovRegimes
open scoped Matrix

variable {Ω : Type*} [MeasurableSpace Ω]

variable (S : MeasExpectationSystem Ω) (T : Transition)

/-- Cochrane (2023), p. 522 ("switches … according to a Markov process"), genuinely: a regime
process adapted to the filtration of a `MeasExpectationSystem`, with the Markov property
`E_t f(S_{t+1}) = ∑_j P_{S_t j} f(j)` a.e. -/
structure MeasMarkovRegime where
  /-- the regime process -/
  regime : ℕ → Ω → Fin 2
  /-- the regime is known at each date -/
  adapted : ∀ t, Measurable[S.𝓕 t] (regime t)
  /-- the Markov property -/
  markov : ∀ t (f : Fin 2 → ℝ), S.E t (fun ω => f (regime (t + 1) ω)) =ᵐ[S.μ]
    fun ω => ∑ j, T.P (regime t ω) j * f j

variable {S T}

/-- Cochrane (2023), eqs. (22.3)–(22.4), p. 500, with Markov-switching `φ` (p. 522), genuinely:
`E_t π_{t+1} = φ_{S_t} π_t + u_t` a.e. at every date. -/
def MSolves (R : MeasMarkovRegime S T) (φ : Fin 2 → ℝ) (u π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, S.E t (π (t + 1)) =ᵐ[S.μ] fun ω => φ (R.regime t ω) * π t ω + u t ω

/-! ### Functions of the regime -/

/-- Cochrane (2023), p. 522: a function of the current regime is known at that date. -/
theorem sm_comp (R : MeasMarkovRegime S T) (f : Fin 2 → ℝ) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (fun ω => f (R.regime t ω)) :=
  (Measurable.of_discrete.comp (R.adapted t)).stronglyMeasurable

/-- Cochrane (2023), p. 522: `|f(i)| ≤ |f(0)| + |f(1)|`. -/
theorem abs_fin_two_le (f : Fin 2 → ℝ) (i : Fin 2) : |f i| ≤ |f 0| + |f 1| := by
  fin_cases i <;> simp

/-- Cochrane (2023), p. 522: a function of the regime is a bounded random variable. -/
theorem bddRV_comp (R : MeasMarkovRegime S T) (f : Fin 2 → ℝ) (t : ℕ) :
    S.BddRV (fun ω => f (R.regime t ω)) :=
  MeasExpectationSystem.BddRV.of_stronglyMeasurable (sm_comp R f t)
    (Eventually.of_forall fun ω => abs_fin_two_le f (R.regime t ω))

/-- Cochrane (2023), p. 522: a bounded adapted process is integrable at every date. -/
theorem integrable_of_adapted {x : ℕ → Ω → ℝ} (hx : StronglyAdapted S.𝓕 x) (hb : S.BddProc x)
    (t : ℕ) : Integrable (x t) S.μ := by
  obtain ⟨M, hM⟩ := hb
  exact MeasExpectationSystem.BddRV.integrable
    (MeasExpectationSystem.BddRV.of_stronglyMeasurable (hx t) (hM t))

/-- Cochrane (2023), p. 523 (iterating the expectational recursion): if `|x| ≤ g(S_{t+1})` a.e.
then `|E_t x| ≤ ∑_j P_{S_t j} g(j)` a.e. -/
theorem abs_E_le_markov (R : MeasMarkovRegime S T) {x : Ω → ℝ} (hx : Integrable x S.μ)
    {g : Fin 2 → ℝ} {t : ℕ} (hb : ∀ᵐ ω ∂S.μ, |x ω| ≤ g (R.regime (t + 1) ω)) :
    ∀ᵐ ω ∂S.μ, |S.E t x ω| ≤ ∑ j, T.P (R.regime t ω) j * g j := by
  have hf := (bddRV_comp R g (t + 1)).integrable
  have hn := (bddRV_comp R (fun l => -g l) (t + 1)).integrable
  have hup : x ≤ᵐ[S.μ] fun ω => g (R.regime (t + 1) ω) :=
    hb.mono fun ω h => (le_abs_self _).trans h
  have hlo : (fun ω => -g (R.regime (t + 1) ω)) ≤ᵐ[S.μ] x :=
    hb.mono fun ω h => by have := neg_abs_le (x ω); linarith
  filter_upwards [S.E_mono hx hf hup t, S.E_mono hn hx hlo t, R.markov t g,
    R.markov t (fun l => -g l)] with ω h1 h2 h3 h4
  rw [h3] at h1
  rw [h4] at h2
  simp only [mul_neg, Finset.sum_neg_distrib] at h2
  exact abs_le.2 ⟨by linarith, h1⟩

/-- Cochrane (2023), p. 523: the powers of `M = Φ⁻¹P` have nonnegative entries. -/
theorem regM_pow_nonneg {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) (k : ℕ) (i j : Fin 2) :
    0 ≤ (regM T φ ^ k) i j := by
  induction k generalizing i with
  | zero => rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ_apply]
    exact add_nonneg (mul_nonneg (regM_nonneg T hφ i 0) (ih 0))
      (mul_nonneg (regM_nonneg T hφ i 1) (ih 1))

/-! ### Uniqueness under the Davig–Leeper condition -/

/-- Cochrane (2023), p. 523, genuinely: a bounded adapted solution of the homogeneous model
`E_t e_{t+1} = φ_{S_t} e_t` satisfies `|e_t| ≤ B ∑_j (M^k)_{S_t j}` a.e. for every `k`. -/
theorem meas_bound (R : MeasMarkovRegime S T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    {e : ℕ → Ω → ℝ} (he : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] fun ω => φ (R.regime t ω) * e t ω)
    (hea : StronglyAdapted S.𝓕 e) {B : ℝ} (hB : ∀ t, ∀ᵐ ω ∂S.μ, |e t ω| ≤ B) (k : ℕ) :
    ∀ t, ∀ᵐ ω ∂S.μ, |e t ω| ≤ B * ∑ j, (regM T φ ^ k) (R.regime t ω) j := by
  induction k with
  | zero =>
    intro t
    filter_upwards [hB t] with ω h
    simpa only [pow_zero, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      mul_one] using h
  | succ k ih =>
    intro t
    have hei : Integrable (e (t + 1)) S.μ := integrable_of_adapted hea ⟨B, hB⟩ (t + 1)
    filter_upwards [abs_E_le_markov R hei (g := fun l => B * ∑ j, (regM T φ ^ k) l j)
      (ih (t + 1)), he t] with ω h1 h2
    rw [h2] at h1
    set i := R.regime t ω
    have hφi := hφ i
    have hval : ∑ j, T.P i j * (B * ∑ l, (regM T φ ^ k) j l) =
        φ i * (B * ∑ j, (regM T φ ^ (k + 1)) i j) := by
      simp only [pow_succ_apply, Fin.sum_univ_two, regM, Matrix.of_apply]
      field_simp
      ring
    rw [hval, abs_mul, abs_of_pos hφi] at h1
    exact le_of_mul_le_mul_left h1 hφi

/-- Cochrane (2023), pp. 522–523, genuinely: under the Davig–Leeper condition the homogeneous
model has no bounded adapted solution other than zero (a.e.) — no regime-dependent or extraneous
sunspots. -/
theorem meas_homog_eq_zero (R : MeasMarkovRegime S T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) {e : ℕ → Ω → ℝ}
    (he : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] fun ω => φ (R.regime t ω) * e t ω)
    (hea : StronglyAdapted S.𝓕 e) (hb : S.BddProc e) : ∀ t, e t =ᵐ[S.μ] 0 := by
  obtain ⟨B, hB⟩ := hb
  have hS := (dl_iff_schur T hφ).mp hdl
  intro t
  filter_upwards [ae_all_iff.2 fun k => meas_bound R hφ he hea hB k t] with ω h
  have hlim : Tendsto (fun k => B * ∑ j, (regM T φ ^ k) (R.regime t ω) j) atTop (𝓝 0) := by
    have h0 := tendsto_pow_entry hS (R.regime t ω) 0
    have h1 := tendsto_pow_entry hS (R.regime t ω) 1
    simpa [Fin.sum_univ_two] using (h0.add h1).const_mul B
  have hle : |e t ω| ≤ 0 := ge_of_tendsto' hlim h
  simpa using abs_nonpos_iff.mp hle

/-! ### Existence: the forward solution -/

/-- Cochrane (2023), p. 523 (the forward solution, genuinely): `Δ_0(t) = −u_t/φ_{S_t}`,
`Δ_{k+1}(t) = E_t Δ_k(t+1)/φ_{S_t}`. -/
noncomputable def fwdM (R : MeasMarkovRegime S T) (φ : Fin 2 → ℝ) (u : ℕ → Ω → ℝ) :
    ℕ → ℕ → Ω → ℝ
  | 0, t => fun ω => -((φ (R.regime t ω))⁻¹ * u t ω)
  | k + 1, t => fun ω => (φ (R.regime t ω))⁻¹ * S.E t (fwdM R φ u k (t + 1)) ω

/-- Cochrane (2023), p. 523: `Δ_k(t)` is known at `t`. -/
theorem fwdM_sm (R : MeasMarkovRegime S T) (φ : Fin 2 → ℝ) {u : ℕ → Ω → ℝ}
    (hua : StronglyAdapted S.𝓕 u) (k t : ℕ) : StronglyMeasurable[S.𝓕 t] (fwdM R φ u k t) := by
  cases k with
  | zero => exact ((sm_comp R (fun i => (φ i)⁻¹) t).mul (hua t)).neg
  | succ k => exact (sm_comp R (fun i => (φ i)⁻¹) t).mul (S.stronglyMeasurable_E t _)

/-- Cochrane (2023), p. 523: `|Δ_k(t)| ≤ U ∑_l (M^k)_{S_t l}/φ_l` a.e. -/
theorem fwdM_bound (R : MeasMarkovRegime S T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) {U : ℝ} (hU : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ U)
    (k : ℕ) : ∀ t, ∀ᵐ ω ∂S.μ,
      |fwdM R φ u k t ω| ≤ U * ∑ l, (regM T φ ^ k) (R.regime t ω) l / φ l := by
  induction k with
  | zero =>
    intro t
    filter_upwards [hU t] with ω h
    simp only [fwdM, pow_zero, Matrix.one_apply, ite_div, zero_div, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    have hφi := hφ (R.regime t ω)
    rw [abs_neg, abs_mul, abs_inv, abs_of_pos hφi, mul_one_div, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right h hφi.le
  | succ k ih =>
    intro t
    have hint : Integrable (fwdM R φ u k (t + 1)) S.μ :=
      MeasExpectationSystem.BddRV.integrable
        (MeasExpectationSystem.BddRV.of_stronglyMeasurable (fwdM_sm R φ hua k (t + 1))
          (M := |U * ∑ l, (regM T φ ^ k) 0 l / φ l| + |U * ∑ l, (regM T φ ^ k) 1 l / φ l|)
          ((ih (t + 1)).mono fun ω h => h.trans ((le_abs_self _).trans
            (abs_fin_two_le (fun i => U * ∑ l, (regM T φ ^ k) i l / φ l) _))))
    filter_upwards [abs_E_le_markov R hint (g := fun i => U * ∑ l, (regM T φ ^ k) i l / φ l)
      (ih (t + 1))] with ω h1
    simp only [fwdM]
    have hφi := hφ (R.regime t ω)
    have hval : (φ (R.regime t ω))⁻¹ *
        ∑ j, T.P (R.regime t ω) j * (U * ∑ l, (regM T φ ^ k) j l / φ l) =
        U * ∑ l, (regM T φ ^ (k + 1)) (R.regime t ω) l / φ l := by
      have h0 := (hφ 0).ne'
      have h1 := (hφ 1).ne'
      simp only [pow_succ_apply, Fin.sum_univ_two, regM, Matrix.of_apply]
      field_simp
      ring
    rw [abs_mul, abs_inv, abs_of_pos hφi, ← hval]
    exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hφi.le)

/-- Cochrane (2023), p. 523: the dominating constants
`c_k = U ∑_l (M^k)_{0l}/φ_l + U ∑_l (M^k)_{1l}/φ_l` bound `|Δ_k(t)|` in every regime. -/
theorem fwdM_bound_const (R : MeasMarkovRegime S T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) {U : ℝ} (hU0 : 0 ≤ U)
    (hU : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ U) (k t : ℕ) :
    ∀ᵐ ω ∂S.μ, |fwdM R φ u k t ω| ≤
      U * ∑ l, (regM T φ ^ k) 0 l / φ l + U * ∑ l, (regM T φ ^ k) 1 l / φ l := by
  have hnn : ∀ i, 0 ≤ U * ∑ l, (regM T φ ^ k) i l / φ l := fun i =>
    mul_nonneg hU0 (Finset.sum_nonneg fun l _ => div_nonneg (regM_pow_nonneg hφ k i l) (hφ l).le)
  filter_upwards [fwdM_bound R hφ hua hU k t] with ω h
  refine h.trans ?_
  rcases Fin.exists_fin_two.1 ⟨R.regime t ω, rfl⟩ with h0 | h1
  · rw [h0]; linarith [hnn 1]
  · rw [h1]; linarith [hnn 0]

/-- Cochrane (2023), p. 523: the forward solution `π_t = E_t ∑_k Δ_k(t)` (adapted by
construction; `fwdSolM_hasSum`: it is `∑_k Δ_k(t)` a.e.). -/
noncomputable def fwdSolM (R : MeasMarkovRegime S T) (φ : Fin 2 → ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  S.E t (fun ω => ∑' k, fwdM R φ u k t ω)

/-- Cochrane (2023), p. 523: under the Davig–Leeper condition the dominating constants are
summable. -/
theorem summable_const (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) (U : ℝ) :
    Summable (fun k => U * ∑ l, (regM T φ ^ k) 0 l / φ l + U * ∑ l, (regM T φ ^ k) 1 l / φ l) :=
  (summable_bound T hφ hdl U 0).add (summable_bound T hφ hdl U 1)

/-- Cochrane (2023), p. 523: under the Davig–Leeper condition the forward solution is the
convergent series `∑_k Δ_k(t)` a.e. -/
theorem fwdSolM_hasSum (R : MeasMarkovRegime S T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) {U : ℝ} (hU0 : 0 ≤ U)
    (hU : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ U) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => fwdM R φ u k t ω) (fwdSolM R φ u t ω) := by
  have hE := S.E_hasSum (f := fun k => fwdM R φ u k t) (summable_const T hφ hdl U)
    (fun k => ((fwdM_sm R φ hua k t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun k => fwdM_bound_const R hφ hua hU0 hU k t) t
  have hEk : ∀ k, S.E t (fwdM R φ u k t) = fwdM R φ u k t := fun k =>
    S.E_of_stronglyMeasurable (fwdM_sm R φ hua k t)
      (MeasExpectationSystem.BddRV.integrable
        (MeasExpectationSystem.BddRV.of_stronglyMeasurable (fwdM_sm R φ hua k t)
          (fwdM_bound_const R hφ hua hU0 hU k t)))
  filter_upwards [hE] with ω h
  simp only [hEk] at h
  exact h

/-- Cochrane (2023), pp. 522–523, genuinely: under the Davig–Leeper condition the forward
solution solves `E_t π_{t+1} = φ_{S_t} π_t + u_t` a.e. -/
theorem fwdSolM_solves (R : MeasMarkovRegime S T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) {U : ℝ} (hU0 : 0 ≤ U)
    (hU : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ U) : MSolves R φ u (fwdSolM R φ u) := by
  intro t
  have hcongr : S.E t (fwdSolM R φ u (t + 1)) =ᵐ[S.μ]
      S.E t (fun ω => ∑' k, fwdM R φ u k (t + 1) ω) :=
    S.E_congr ((fwdSolM_hasSum R hφ hdl hua hU0 hU (t + 1)).mono fun ω h => h.tsum_eq.symm) t
  have hE := S.E_hasSum (f := fun k => fwdM R φ u k (t + 1)) (summable_const T hφ hdl U)
    (fun k => ((fwdM_sm R φ hua k (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable)
    (fun k => fwdM_bound_const R hφ hua hU0 hU k (t + 1)) t
  filter_upwards [hcongr, hE, fwdSolM_hasSum R hφ hdl hua hU0 hU t] with ω e1 e2 e3
  rw [e1]
  have hφi := (hφ (R.regime t ω)).ne'
  have key : ∀ k, S.E t (fwdM R φ u k (t + 1)) ω =
      φ (R.regime t ω) * fwdM R φ u (k + 1) t ω := by
    intro k
    simp only [fwdM]
    rw [← mul_assoc, mul_inv_cancel₀ hφi, one_mul]
  simp only [key] at e2
  have e3' := (hasSum_nat_add_iff' 1).mpr e3
  simp only [Finset.sum_range_one] at e3'
  rw [e2.unique (e3'.mul_left (φ (R.regime t ω)))]
  simp only [fwdM]
  field_simp
  ring

/-- Cochrane (2023), pp. 522–523: the forward solution is bounded. -/
theorem fwdSolM_bdd (R : MeasMarkovRegime S T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) {U : ℝ} (hU0 : 0 ≤ U)
    (hU : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ U) : S.BddProc (fwdSolM R φ u) := by
  refine ⟨∑' k, (U * ∑ l, (regM T φ ^ k) 0 l / φ l + U * ∑ l, (regM T φ ^ k) 1 l / φ l),
    fun t => ?_⟩
  filter_upwards [fwdSolM_hasSum R hφ hdl hua hU0 hU t,
    ae_all_iff.2 fun k => fwdM_bound_const R hφ hua hU0 hU k t] with ω h hb
  have hs : Summable fun k => |fwdM R φ u k t ω| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hb (summable_const T hφ hdl U)
  rw [← h.tsum_eq]
  have hn := norm_tsum_le_tsum_norm (f := fun k => fwdM R φ u k t ω)
    (by simpa only [Real.norm_eq_abs] using hs)
  simp only [Real.norm_eq_abs] at hn
  exact hn.trans (Summable.tsum_le_tsum hb hs (summable_const T hφ hdl U))

/-- Cochrane (2023), p. 523: the forward solution is adapted. -/
theorem fwdSolM_adapted (R : MeasMarkovRegime S T) (φ : Fin 2 → ℝ) (u : ℕ → Ω → ℝ) :
    StronglyAdapted S.𝓕 (fwdSolM R φ u) := fun t => S.stronglyMeasurable_E t _

/-! ### Non-uniqueness when the condition fails -/

/-- Cochrane (2023), pp. 522–523, genuinely: for an eigenvector `M w = r w`, the process
`π_t = w_{S_t}/r^t` solves the homogeneous model `E_t π_{t+1} = φ_{S_t} π_t` a.e. -/
theorem perron_solves (R : MeasMarkovRegime S T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    {r : ℝ} (hr0 : 0 < r) {w : Fin 2 → ℝ} (hMw : regM T φ *ᵥ w = r • w) :
    MSolves R φ 0 (fun t ω => w (R.regime t ω) / r ^ t) := by
  intro t
  filter_upwards [R.markov t (fun l => w l / r ^ (t + 1))] with ω hm
  rw [hm]
  set i := R.regime t ω
  have hrow := congrFun hMw i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, regM, Matrix.of_apply,
    Pi.smul_apply, smul_eq_mul] at hrow
  have hφi := (hφ i).ne'
  have hrow' : T.P i 0 * w 0 + T.P i 1 * w 1 = φ i * (r * w i) := by
    field_simp at hrow; linarith
  have hrl := (pow_pos hr0 t).ne'
  have hr0' := hr0.ne'
  have key : T.P i 0 * (w 0 / r ^ (t + 1)) + T.P i 1 * (w 1 / r ^ (t + 1)) =
      φ i * (w i / r ^ t) := by
    rw [pow_succ, show T.P i 0 * (w 0 / (r ^ t * r)) + T.P i 1 * (w 1 / (r ^ t * r))
      = (T.P i 0 * w 0 + T.P i 1 * w 1) / (r ^ t * r) by ring, hrow']
    field_simp
  simp only [Fin.sum_univ_two, Pi.zero_apply, add_zero]
  exact key

/-- Cochrane (2023), pp. 522–523: the zero process solves the homogeneous model. -/
theorem msolves_zero (R : MeasMarkovRegime S T) (φ : Fin 2 → ℝ) : MSolves R φ 0 0 := fun t =>
  Eventually.of_forall fun ω => by simp [S.E_zero]

/-! ### The Davig–Leeper determinacy theorem -/

/-- Cochrane (2023), pp. 522–523 (**Davig and Leeper's determinacy condition, genuinely**): in
any `MeasExpectationSystem` carrying a Markov regime process with both regimes possible at date
`0`, and for `φ_0, φ_1 > 0`, the model `E_t π_{t+1} = φ_{S_t} π_t + u_t` has, for every bounded
adapted disturbance, a bounded adapted equilibrium that is unique up to a.e. equality iff
`(1 − φ_1)p_00 + (1 − φ_0)p_11 + φ_0φ_1 > 1` and `p_00/φ_0 + p_11/φ_1 < 2`. -/
theorem meas_determinate_iff (R : MeasMarkovRegime S T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hS0 : ∀ i, S.μ {ω | R.regime 0 ω = i} ≠ 0) :
    (∀ u : ℕ → Ω → ℝ, StronglyAdapted S.𝓕 u → S.BddProc u →
      (∃ π, MSolves R φ u π ∧ StronglyAdapted S.𝓕 π ∧ S.BddProc π) ∧
      ∀ π₁ π₂ : ℕ → Ω → ℝ, MSolves R φ u π₁ → MSolves R φ u π₂ → StronglyAdapted S.𝓕 π₁ →
        StronglyAdapted S.𝓕 π₂ → S.BddProc π₁ → S.BddProc π₂ → ∀ t, π₁ t =ᵐ[S.μ] π₂ t) ↔
      DLCondition T φ := by
  constructor
  · intro h
    by_contra hndl
    rw [dl_iff_schur T hφ] at hndl
    obtain ⟨r, w, hr1, -, hwne, hMw⟩ := exists_perron (regM_nonneg T hφ) hndl
    have hr0 : 0 < r := by linarith
    have huniq := (h 0 (fun _ => stronglyMeasurable_zero)
      ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩).2
    have hsol := perron_solves R hφ hr0 hMw
    have hea : StronglyAdapted S.𝓕 (fun t ω => w (R.regime t ω) / r ^ t) := fun t =>
      sm_comp R (fun l => w l / r ^ t) t
    have heb : S.BddProc (fun t ω => w (R.regime t ω) / r ^ t) := by
      refine ⟨|w 0| + |w 1|, fun t => Eventually.of_forall fun ω => ?_⟩
      have hge : 1 ≤ r ^ t := one_le_pow₀ hr1
      rw [abs_div, abs_of_pos (pow_pos hr0 _)]
      exact (div_le_self (abs_nonneg _) hge).trans (abs_fin_two_le w _)
    have h0 := huniq _ 0 hsol (msolves_zero R φ) hea (fun _ => stronglyMeasurable_zero) heb
      ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩ 0
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hwne (funext hcon)
    apply hS0 i
    refine measure_mono_null (fun ω (hω : R.regime 0 ω = i) => ?_) (ae_iff.1 h0)
    simp only [Set.mem_ofPred_eq, pow_zero, div_one, Pi.zero_apply, hω]
    exact hi
  · intro hdl u hua ⟨U, hU⟩
    have hU0 : 0 ≤ U := by
      obtain ⟨ω, hω⟩ := (hU 0).exists
      exact (abs_nonneg _).trans hω
    refine ⟨⟨fwdSolM R φ u, fwdSolM_solves R hφ hdl hua hU0 hU, fwdSolM_adapted R φ u,
      fwdSolM_bdd R hφ hdl hua hU0 hU⟩, ?_⟩
    intro π₁ π₂ h₁ h₂ ha₁ ha₂ hb₁ hb₂
    have hi₁ := integrable_of_adapted ha₁ hb₁
    have hi₂ := integrable_of_adapted ha₂ hb₂
    have he : ∀ t, S.E t (π₁ (t + 1) - π₂ (t + 1)) =ᵐ[S.μ]
        fun ω => φ (R.regime t ω) * (π₁ t ω - π₂ t ω) := by
      intro t
      filter_upwards [S.E_sub (hi₁ (t + 1)) (hi₂ (t + 1)) t, h₁ t, h₂ t] with ω e1 e2 e3
      rw [e1, Pi.sub_apply, e2, e3]
      ring
    obtain ⟨B₁, hB₁⟩ := hb₁
    obtain ⟨B₂, hB₂⟩ := hb₂
    have hz := meas_homog_eq_zero R hφ hdl (e := fun t => π₁ t - π₂ t) he
      (fun t => (ha₁ t).sub (ha₂ t)) ⟨B₁ + B₂, fun t => by
        filter_upwards [hB₁ t, hB₂ t] with ω e1 e2
        exact (abs_sub _ _).trans (add_le_add e1 e2)⟩
    intro t
    filter_upwards [hz t] with ω e
    exact sub_eq_zero.mp e

/-- Cochrane (2023), pp. 522–523 (**link** with the tree result `determinate_iff` and
`dl_iff_schur`): determinacy on the genuine probability space is equivalent to determinacy on the
regime tree, and to both eigenvalues of `M = Φ⁻¹P` lying in the open unit disc. -/
theorem meas_determinate_iff_tree (R : MeasMarkovRegime S T) {φ : Fin 2 → ℝ}
    (hφ : ∀ i, 0 < φ i) (hS0 : ∀ i, S.μ {ω | R.regime 0 ω = i} ≠ 0) :
    ((∀ u : ℕ → Ω → ℝ, StronglyAdapted S.𝓕 u → S.BddProc u →
      (∃ π, MSolves R φ u π ∧ StronglyAdapted S.𝓕 π ∧ S.BddProc π) ∧
      ∀ π₁ π₂ : ℕ → Ω → ℝ, MSolves R φ u π₁ → MSolves R φ u π₂ → StronglyAdapted S.𝓕 π₁ →
        StronglyAdapted S.𝓕 π₂ → S.BddProc π₁ → S.BddProc π₂ → ∀ t, π₁ t =ᵐ[S.μ] π₂ t) ↔
      (∀ u, BoundedFn u → ∃! π, Solves T φ u π ∧ BoundedFn π)) ∧
    (DLCondition T φ ↔ SchurStable (tr2 (regM T φ)) (det2 (regM T φ))) :=
  ⟨(meas_determinate_iff R hφ hS0).trans (determinate_iff T hφ).symm, dl_iff_schur T hφ⟩

/-! ### A genuine two-state Markov chain driven by i.i.d. uniforms -/

/-- Cochrane (2023), p. 522 (the construction of the regime process): the uniform law on
`[0, 1]`. -/
noncomputable def unifProb : ProbabilityMeasure ℝ :=
  ⟨volume.restrict (Set.Icc 0 1), ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩⟩

/-- Cochrane (2023), p. 522: `Pr(U < p) = p` for `p ≤ 1` (`ofReal` truncates negative `p`). -/
theorem unif_Iio {p : ℝ} (h1 : p ≤ 1) :
    (unifProb : Measure ℝ) (Set.Iio p) = ENNReal.ofReal p := by
  change volume.restrict (Set.Icc 0 1) (Set.Iio p) = _
  rw [Measure.restrict_apply measurableSet_Iio]
  have e : Set.Iio p ∩ Set.Icc 0 1 = Set.Ico 0 p := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨a, b, -⟩; exact ⟨b, a⟩
    · rintro ⟨a, b⟩; exact ⟨b, a, by linarith⟩
  rw [e, Real.volume_Ico, sub_zero]

/-- Cochrane (2023), p. 522: `Pr(U ≥ p) = 1 − p` for `0 ≤ p`. -/
theorem unif_Ici {p : ℝ} (h0 : 0 ≤ p) :
    (unifProb : Measure ℝ) (Set.Ici p) = ENNReal.ofReal (1 - p) := by
  change volume.restrict (Set.Icc 0 1) (Set.Ici p) = _
  rw [Measure.restrict_apply measurableSet_Ici]
  have e : Set.Ici p ∩ Set.Icc 0 1 = Set.Icc p 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨a, -, b⟩; exact ⟨a, b⟩
    · rintro ⟨a, b⟩; exact ⟨a, by linarith, b⟩
  rw [e, Real.volume_Icc]

/-- Cochrane (2023), p. 522: the uniform law has no atoms. -/
theorem unif_singleton (x : ℝ) : (unifProb : Measure ℝ) {x} = 0 :=
  le_antisymm ((Measure.restrict_le_self (s := Set.Icc (0 : ℝ) 1)) {x} |>.trans
    (by rw [Real.volume_singleton])) bot_le

/-- Cochrane (2023), p. 522: the step `x ↦ a` if `x < p`, `b` otherwise. -/
noncomputable def stepFn (p a b x : ℝ) : ℝ := if x < p then a else b

/-- Cochrane (2023), p. 522: the step function is measurable. -/
theorem measurable_stepFn (p a b : ℝ) : Measurable (stepFn p a b) :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

/-- Cochrane (2023), p. 522: `E[step(U)] = a p + b (1 − p)` for the uniform `U`. -/
theorem integral_stepFn {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (a b : ℝ) :
    ∫ x, stepFn p a b x ∂(unifProb : Measure ℝ) = a * p + b * (1 - p) := by
  have e : stepFn p a b = fun x => b + (a - b) * Set.indicator (Set.Iio p) 1 x := by
    funext x
    by_cases hx : x < p
    · simp [stepFn, hx]
    · simp [stepFn, hx]
  have hind : Integrable (Set.indicator (Set.Iio p) (1 : ℝ → ℝ)) (unifProb : Measure ℝ) :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Iio
  rw [e, integral_add (integrable_const _) (hind.const_mul _), integral_const_mul,
    integral_indicator_one measurableSet_Iio, measureReal_def, unif_Iio h1,
    ENNReal.toReal_ofReal h0]
  simp
  ring

/-- Cochrane (2023), p. 522 (the regime process): `S_0 = 0` iff `U_0 < q`, and
`S_{t+1} = 0` iff `U_{t+1} < p_{S_t 0}`, with i.i.d. uniforms `U_t(ω) = ω_t`. -/
noncomputable def chain (T : Transition) (q : ℝ) : ℕ → (ℕ → ℝ) → Fin 2
  | 0 => fun ω => if ω 0 < q then 0 else 1
  | t + 1 => fun ω => if ω (t + 1) < T.P (chain T q t ω) 0 then 0 else 1

/-- Cochrane (2023), p. 522: the regime is known at each date. -/
theorem chain_measurable (T : Transition) (q : ℝ) (t : ℕ) :
    Measurable[(iidSystem unifProb).𝓕 t] (chain T q t) := by
  induction t with
  | zero =>
    exact Measurable.ite (measurableSet_lt (f := fun ω : ℕ → ℝ => ω 0) (g := fun _ => q)
      (measurable_shock unifProb le_rfl) measurable_const) measurable_const measurable_const
  | succ t ih =>
    have hg : Measurable[(iidSystem unifProb).𝓕 (t + 1)]
        (fun ω => T.P (chain T q t ω) 0) :=
      (Measurable.of_discrete (f := fun i : Fin 2 => T.P i 0)).comp
        (ih.mono ((iidSystem unifProb).𝓕.mono (Nat.le_succ t)) le_rfl)
    exact Measurable.ite (measurableSet_lt (f := fun ω : ℕ → ℝ => ω (t + 1))
      (g := fun ω => T.P (chain T q t ω) 0) (measurable_shock unifProb le_rfl) hg)
      measurable_const measurable_const

/-- Cochrane (2023), p. 522: the transition probability `p_{i0}` lies in `[0, 1]`. -/
theorem P_le_one (T : Transition) (i : Fin 2) : T.P i 0 ≤ 1 := by
  have := T.rowSum i
  rw [Fin.sum_univ_two] at this
  linarith [T.nonneg i 1]

/-- Cochrane (2023), p. 522 (**the Markov property**): `E_t f(S_{t+1}) = ∑_j p_{S_t j} f(j)`
a.e. — the regime process is a Markov chain with transition matrix `P`. -/
theorem chain_markov (T : Transition) (q : ℝ) (t : ℕ) (f : Fin 2 → ℝ) :
    (iidSystem unifProb).E t (fun ω => f (chain T q (t + 1) ω)) =ᵐ[(iidSystem unifProb).μ]
      fun ω => ∑ j, T.P (chain T q t ω) j * f j := by
  set Sy := iidSystem unifProb
  have hdec : (fun ω => f (chain T q (t + 1) ω)) =
      (fun ω => (if chain T q t ω = 0 then (1 : ℝ) else 0)) *
          (fun ω => stepFn (T.P 0 0) (f 0) (f 1) (ω (t + 1))) +
        (fun ω => (if chain T q t ω = 1 then (1 : ℝ) else 0)) *
          (fun ω => stepFn (T.P 1 0) (f 0) (f 1) (ω (t + 1))) := by
    funext ω
    simp only [Pi.add_apply, Pi.mul_apply, stepFn]
    change f (if ω (t + 1) < T.P (chain T q t ω) 0 then 0 else 1) = _
    generalize chain T q t ω = c
    fin_cases c <;> simp <;> split_ifs <;> rfl
  have hgsm : ∀ i : Fin 2, StronglyMeasurable[Sy.𝓕 t]
      (fun ω => (if chain T q t ω = i then (1 : ℝ) else 0)) := fun i =>
    ((Measurable.of_discrete (f := fun c : Fin 2 => if c = i then (1 : ℝ) else 0)).comp
      (chain_measurable T q t)).stronglyMeasurable
  have hgb : ∀ i : Fin 2, ∀ᵐ ω ∂Sy.μ, |(if chain T q t ω = i then (1 : ℝ) else 0)| ≤ 1 :=
    fun i => Eventually.of_forall fun ω => by split_ifs <;> simp
  have hyB : ∀ i : Fin 2, Sy.BddRV (fun ω => stepFn (T.P i 0) (f 0) (f 1) (ω (t + 1))) := by
    intro i
    refine ⟨((measurable_stepFn _ _ _).comp (measurable_pi_apply (t + 1))).aestronglyMeasurable,
      |f 0| + |f 1|, Eventually.of_forall fun ω => ?_⟩
    simp only [stepFn]
    split_ifs
    · exact abs_fin_two_le f 0
    · exact abs_fin_two_le f 1
  have hgB : ∀ i : Fin 2, Sy.BddRV (fun ω => (if chain T q t ω = i then (1 : ℝ) else 0)) :=
    fun i => MeasExpectationSystem.BddRV.of_stronglyMeasurable (hgsm i) (hgb i)
  have hEy : ∀ i : Fin 2, Sy.E t (fun ω => stepFn (T.P i 0) (f 0) (f 1) (ω (t + 1)))
      =ᵐ[Sy.μ] fun _ => f 0 * T.P i 0 + f 1 * (1 - T.P i 0) := by
    intro i
    rw [← integral_stepFn (T.nonneg i 0) (P_le_one T i)]
    exact E_shock_fun unifProb t (f := stepFn (T.P i 0) (f 0) (f 1)) (measurable_stepFn _ _ _)
  rw [hdec]
  filter_upwards [Sy.E_add ((hgB 0).mul (hyB 0)).integrable ((hgB 1).mul (hyB 1)).integrable t,
    Sy.E_pullOut (hgsm 0) (hgb 0) (hyB 0).integrable,
    Sy.E_pullOut (hgsm 1) (hgb 1) (hyB 1).integrable, hEy 0, hEy 1] with ω h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, h3, Pi.mul_apply, Pi.mul_apply, h4, h5, Fin.sum_univ_two]
  generalize chain T q t ω = c
  fin_cases c <;> simp [P01, P10] <;> ring

/-- Cochrane (2023), p. 522: the regime process of `chain` as a Markov regime of the i.i.d.
expectation system with uniform shocks. -/
noncomputable def chainRegime (T : Transition) (q : ℝ) : MeasMarkovRegime (iidSystem unifProb) T :=
  ⟨chain T q, chain_measurable T q, chain_markov T q⟩

/-- Cochrane (2023), p. 522: the initial distribution, `Pr(S_0 = 0) = q`, `Pr(S_0 = 1) = 1 − q`;
both regimes are possible at date `0` when `0 < q < 1`. -/
theorem chain_initial (T : Transition) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (iidSystem unifProb).μ {ω | chain T q 0 ω = 0} = ENNReal.ofReal q ∧
      (iidSystem unifProb).μ {ω | chain T q 0 ω = 1} = ENNReal.ofReal (1 - q) := by
  have hmp := measurePreserving_eval_infinitePi (fun _ => (unifProb : Measure ℝ)) 0
  have e0 : {ω : ℕ → ℝ | chain T q 0 ω = 0} = (fun ω : ℕ → ℝ => ω 0) ⁻¹' Set.Iio q := by
    ext ω
    simp only [chain, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio]
    split_ifs with h <;> simp [h]
  have e1 : {ω : ℕ → ℝ | chain T q 0 ω = 1} = (fun ω : ℕ → ℝ => ω 0) ⁻¹' Set.Ici q := by
    ext ω
    simp only [chain, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici]
    split_ifs with h
    · simp only [Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, false_iff, not_le]; exact h
    · simp only [true_iff]; exact not_lt.1 h
  refine ⟨?_, ?_⟩
  · rw [e0]
    change Measure.infinitePi (fun _ => (unifProb : Measure ℝ)) _ = _
    rw [hmp.measure_preimage measurableSet_Iio.nullMeasurableSet, unif_Iio hq1]
  · rw [e1]
    change Measure.infinitePi (fun _ => (unifProb : Measure ℝ)) _ = _
    rw [hmp.measure_preimage measurableSet_Ici.nullMeasurableSet, unif_Ici hq0]

/-- Cochrane (2023), p. 522: with `0 < q < 1` both regimes have positive probability at
date `0`. -/
theorem chain_initial_pos (T : Transition) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (i : Fin 2) :
    (iidSystem unifProb).μ {ω | chain T q 0 ω = i} ≠ 0 := by
  obtain ⟨h0, h1⟩ := chain_initial T hq0.le hq1.le
  fin_cases i
  · simp only [Fin.zero_eta, h0, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq0
  · simp only [Fin.mk_one, h1, ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith

/-- Cochrane (2023), p. 522 (**not a finite tree**): every single path of regimes and shocks has
probability zero. -/
theorem chain_singleton_null (ω : ℕ → ℝ) : (iidSystem unifProb).μ {ω} = 0 := by
  have hmp := measurePreserving_eval_infinitePi (fun _ => (unifProb : Measure ℝ)) 0
  refine le_antisymm ?_ bot_le
  calc (iidSystem unifProb).μ {ω}
      ≤ (iidSystem unifProb).μ ((fun ω' : ℕ → ℝ => ω' 0) ⁻¹' {ω 0}) :=
        measure_mono fun ω' h => by rw [Set.mem_singleton_iff.mp h]; rfl
    _ = (unifProb : Measure ℝ) {ω 0} := by
        change Measure.infinitePi (fun _ => (unifProb : Measure ℝ)) _ = _
        rw [hmp.measure_preimage (measurableSet_singleton _).nullMeasurableSet]
    _ = 0 := unif_singleton _

/-- Cochrane (2023), p. 522 (the conditional transition probabilities):
`Pr(S_{t+1} = j | 𝓕_t) = p_{S_t j}` a.e. -/
theorem chain_transition (T : Transition) (q : ℝ) (t : ℕ) (j : Fin 2) :
    (iidSystem unifProb).E t (fun ω => if chain T q (t + 1) ω = j then (1 : ℝ) else 0)
      =ᵐ[(iidSystem unifProb).μ] fun ω => T.P (chain T q t ω) j := by
  filter_upwards [chain_markov T q t (fun c => if c = j then (1 : ℝ) else 0)] with ω h
  rw [h]
  simp

/-- Cochrane (2023), pp. 522–523 (**Davig–Leeper on a genuine Markov chain**): for the chain
driven by i.i.d. uniforms with `0 < q < 1` and `φ_0, φ_1 > 0`, bounded adapted equilibria exist
and are unique (a.e.) for every bounded adapted disturbance iff the Davig–Leeper condition holds,
iff the tree model is determinate. -/
theorem chain_determinate_iff (T : Transition) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) :
    ((∀ u : ℕ → (ℕ → ℝ) → ℝ, StronglyAdapted (iidSystem unifProb).𝓕 u →
      (iidSystem unifProb).BddProc u →
      (∃ π, MSolves (chainRegime T q) φ u π ∧ StronglyAdapted (iidSystem unifProb).𝓕 π ∧
        (iidSystem unifProb).BddProc π) ∧
      ∀ π₁ π₂ : ℕ → (ℕ → ℝ) → ℝ, MSolves (chainRegime T q) φ u π₁ →
        MSolves (chainRegime T q) φ u π₂ → StronglyAdapted (iidSystem unifProb).𝓕 π₁ →
        StronglyAdapted (iidSystem unifProb).𝓕 π₂ → (iidSystem unifProb).BddProc π₁ →
        (iidSystem unifProb).BddProc π₂ → ∀ t, π₁ t =ᵐ[(iidSystem unifProb).μ] π₂ t) ↔
      DLCondition T φ) ∧
    (DLCondition T φ ↔ ∀ u, BoundedFn u → ∃! π, Solves T φ u π ∧ BoundedFn π) :=
  ⟨meas_determinate_iff (chainRegime T q) hφ (chain_initial_pos T hq0 hq1),
    (determinate_iff T hφ).symm⟩

/-- Cochrane (2023), p. 523 ("temporarily passive", genuinely): with `φ = (2, ½)` and a
short-lived passive regime (`p_00 = 0.9`, `p_11 = 0.4`), the Markov-chain economy has a unique
bounded equilibrium for every bounded disturbance. -/
theorem chain_temporarily_passive {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (u : ℕ → (ℕ → ℝ) → ℝ) (hua : StronglyAdapted (iidSystem unifProb).𝓕 u)
    (hub : (iidSystem unifProb).BddProc u) :
    (∃ π, MSolves (chainRegime egShortPassive q) ![2, 1 / 2] u π ∧
      StronglyAdapted (iidSystem unifProb).𝓕 π ∧ (iidSystem unifProb).BddProc π) ∧
    ∀ π₁ π₂ : ℕ → (ℕ → ℝ) → ℝ, MSolves (chainRegime egShortPassive q) ![2, 1 / 2] u π₁ →
      MSolves (chainRegime egShortPassive q) ![2, 1 / 2] u π₂ →
      StronglyAdapted (iidSystem unifProb).𝓕 π₁ → StronglyAdapted (iidSystem unifProb).𝓕 π₂ →
      (iidSystem unifProb).BddProc π₁ → (iidSystem unifProb).BddProc π₂ →
      ∀ t, π₁ t =ᵐ[(iidSystem unifProb).μ] π₂ t := by
  have hφ : ∀ i, 0 < (![2, 1 / 2] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  exact ((chain_determinate_iff egShortPassive hq0 hq1 hφ).1.2
    temporarily_passive_determinate) u hua hub

/-- Cochrane (2023), pp. 522–523 ("locally active", genuinely): with `φ = (2, ½)` and a
persistent passive regime (`p_00 = p_11 = 0.9`), the Markov-chain economy does not have a unique
bounded equilibrium for every bounded disturbance, although regime `0` is active. -/
theorem chain_locally_active {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ¬ (∀ u : ℕ → (ℕ → ℝ) → ℝ, StronglyAdapted (iidSystem unifProb).𝓕 u →
      (iidSystem unifProb).BddProc u →
      (∃ π, MSolves (chainRegime egLongPassive q) ![2, 1 / 2] u π ∧
        StronglyAdapted (iidSystem unifProb).𝓕 π ∧ (iidSystem unifProb).BddProc π) ∧
      ∀ π₁ π₂ : ℕ → (ℕ → ℝ) → ℝ, MSolves (chainRegime egLongPassive q) ![2, 1 / 2] u π₁ →
        MSolves (chainRegime egLongPassive q) ![2, 1 / 2] u π₂ →
        StronglyAdapted (iidSystem unifProb).𝓕 π₁ →
        StronglyAdapted (iidSystem unifProb).𝓕 π₂ → (iidSystem unifProb).BddProc π₁ →
        (iidSystem unifProb).BddProc π₂ → ∀ t, π₁ t =ᵐ[(iidSystem unifProb).μ] π₂ t) := by
  have hφ : ∀ i, 0 < (![2, 1 / 2] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  rw [(chain_determinate_iff egLongPassive hq0 hq1 hφ).1]
  exact locally_active_indeterminate

end Cochrane.ObservationalEquivalence.MarkovRegimesMeasure
