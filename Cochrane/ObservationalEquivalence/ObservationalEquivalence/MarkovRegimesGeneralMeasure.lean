/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.MarkovRegimesGeneral
import ObservationalEquivalence.MarkovRegimesMeasure

/-!
# `N`-regime Markov switching with coefficients of any sign on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 24, §24.2, pp. 522–523 (Davig and
Leeper (2006, 2007): policy-rule coefficients switch according to a Markov process; "the Markov
assumption, with exactly two (or even N) states"; "a time with `φ < 1` should be something like
'locally passive' or 'temporarily passive'").

`MarkovRegimesGeneral` proves the determinacy theorem for `N` regimes and coefficients of any sign
on the regime tree. Here the same theorem is proved in any `MeasExpectationSystem` carrying an
`N`-state Markov regime process, and on a genuine `N`-state chain driven by i.i.d. uniforms.

## Main results

* `MeasMarkovRegimeN S T`: an adapted `Fin N`-valued regime process with the a.e. Markov property
  `E_t f(S_{t+1}) = ∑_j P_{S_t j} f(j)`; `MSolves`, `MDeterminate`.
* `meas_determinate_iff` (**Davig–Leeper for `N` regimes and any signs, genuinely**): if every
  regime has positive probability at date `0`, the model `E_t π_{t+1} = φ_{S_t} π_t + u_t` has a
  bounded adapted equilibrium, unique a.e., for every bounded adapted disturbance iff every
  `φ_i ≠ 0` and the spectral radius of `|Φ|⁻¹P` is `< 1` (`GenCondition`).
  Necessity: `zero_coeff_homogM` (`φ_i = 0`: `π_0 = 1{S_0 = i}`, `π_t = 0` for `t ≥ 1`) and
  `twisted_solves` (the sign-twisted sunspot `π_t = s_t x_t(S_t)`, `s_t = ∏_{τ<t} sgn φ_{S_τ}`).
  Sufficiency: `meas_homog_eq_zero`, `fwdSolM_solves`, `fwdSolM_bdd`.
* Links: `meas_determinate_iff_tree` (same condition as the tree), `ofTwoRegime`,
  `meas_two_regime_recovered` (the two-regime `φ > 0` result of `MarkovRegimesMeasure` as a special
  case), `meas_dl_corrected` (two regimes, any signs).
* The chain: `cumP`, `pick` (inverse-CDF sampling), `unif_pick` (`Pr(pick p U = j) = p_j`),
  `integral_pick`, `chainN` (`S_0 = pick q U_0`, `S_{t+1} = pick P_{S_t} U_{t+1}`), `chainN_markov`,
  `chainRegimeN`, `chainN_initial`, `chainN_determinate_iff`; examples
  `chainN_three_regime_determinate`, `chain_negative_regime_determinate`,
  `chain_dl_formula_fails_negative`, `chain_naive_not_sufficient`.
-/

namespace Cochrane.ObservationalEquivalence.MarkovRegimesGeneralMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationsMeasure
open Cochrane.ObservationalEquivalence.ExpectationsMeasureIID
open Cochrane.ObservationalEquivalence.MarkovRegimesGeneral
open scoped Matrix ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

variable (S : MeasExpectationSystem Ω) (T : TransitionN N)

/-- Cochrane (2023), p. 522 ("switches … according to a Markov process"), genuinely, with `N`
regimes: a regime process adapted to the filtration with the Markov property
`E_t f(S_{t+1}) = ∑_j P_{S_t j} f(j)` a.e. -/
structure MeasMarkovRegimeN where
  /-- the regime process -/
  regime : ℕ → Ω → Fin N
  /-- the regime is known at each date -/
  adapted : ∀ t, Measurable[S.𝓕 t] (regime t)
  /-- the Markov property -/
  markov : ∀ t (f : Fin N → ℝ), S.E t (fun ω => f (regime (t + 1) ω)) =ᵐ[S.μ]
    fun ω => ∑ j, T.P (regime t ω) j * f j

variable {S T}

/-- Cochrane (2023), eqs. (22.3)–(22.4), p. 500, with Markov-switching `φ` (p. 522), genuinely:
`E_t π_{t+1} = φ_{S_t} π_t + u_t` a.e. at every date. -/
def MSolves (R : MeasMarkovRegimeN S T) (φ : Fin N → ℝ) (u π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, S.E t (π (t + 1)) =ᵐ[S.μ] fun ω => φ (R.regime t ω) * π t ω + u t ω

/-- Cochrane (2023), pp. 522–523, genuinely: for every bounded adapted disturbance there is a
bounded adapted equilibrium, and any two are equal a.e. -/
def MDeterminate (R : MeasMarkovRegimeN S T) (φ : Fin N → ℝ) : Prop :=
  ∀ u : ℕ → Ω → ℝ, StronglyAdapted S.𝓕 u → S.BddProc u →
    (∃ π, MSolves R φ u π ∧ StronglyAdapted S.𝓕 π ∧ S.BddProc π) ∧
    ∀ π₁ π₂ : ℕ → Ω → ℝ, MSolves R φ u π₁ → MSolves R φ u π₂ → StronglyAdapted S.𝓕 π₁ →
      StronglyAdapted S.𝓕 π₂ → S.BddProc π₁ → S.BddProc π₂ → ∀ t, π₁ t =ᵐ[S.μ] π₂ t

/-! ### Functions of the regime -/

/-- Cochrane (2023), p. 522: a function of the current regime is known at that date. -/
theorem sm_comp (R : MeasMarkovRegimeN S T) (f : Fin N → ℝ) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (fun ω => f (R.regime t ω)) :=
  (Measurable.of_discrete.comp (R.adapted t)).stronglyMeasurable

/-- Cochrane (2023), p. 522: `|f(i)| ≤ ∑_l |f(l)|`. -/
theorem abs_le_sum_abs (f : Fin N → ℝ) (i : Fin N) : |f i| ≤ ∑ l, |f l| :=
  Finset.single_le_sum (f := fun l => |f l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- Cochrane (2023), p. 522: a function of the regime is a bounded random variable. -/
theorem bddRV_comp (R : MeasMarkovRegimeN S T) (f : Fin N → ℝ) (t : ℕ) :
    S.BddRV (fun ω => f (R.regime t ω)) :=
  MeasExpectationSystem.BddRV.of_stronglyMeasurable (sm_comp R f t)
    (Eventually.of_forall fun ω => abs_le_sum_abs f (R.regime t ω))

/-- Cochrane (2023), p. 522: a bounded adapted process is integrable at every date. -/
theorem integrable_of_adapted {x : ℕ → Ω → ℝ} (hx : StronglyAdapted S.𝓕 x) (hb : S.BddProc x)
    (t : ℕ) : Integrable (x t) S.μ := by
  obtain ⟨M, hM⟩ := hb
  exact MeasExpectationSystem.BddRV.integrable
    (MeasExpectationSystem.BddRV.of_stronglyMeasurable (hx t) (hM t))

/-- Cochrane (2023), p. 523 (iterating the expectational recursion): if `|x| ≤ g(S_{t+1})` a.e.
then `|E_t x| ≤ ∑_j P_{S_t j} g(j)` a.e. -/
theorem abs_E_le_markov (R : MeasMarkovRegimeN S T) {x : Ω → ℝ} (hx : Integrable x S.μ)
    {g : Fin N → ℝ} {t : ℕ} (hb : ∀ᵐ ω ∂S.μ, |x ω| ≤ g (R.regime (t + 1) ω)) :
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

/-! ### Uniqueness under the condition -/

/-- Cochrane (2023), p. 523, genuinely: a bounded adapted solution of the homogeneous model
satisfies `|e_t| ≤ B ∑_j ((|Φ|⁻¹P)^k)_{S_t j}` a.e. for every `k`. -/
theorem meas_bound (R : MeasMarkovRegimeN S T) {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0)
    {e : ℕ → Ω → ℝ} (he : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] fun ω => φ (R.regime t ω) * e t ω)
    (hea : StronglyAdapted S.𝓕 e) {B : ℝ} (hB : ∀ t, ∀ᵐ ω ∂S.μ, |e t ω| ≤ B) (k : ℕ) :
    ∀ t, ∀ᵐ ω ∂S.μ, |e t ω| ≤ B * ∑ j, (absM T φ ^ k) (R.regime t ω) j := by
  induction k with
  | zero =>
    intro t
    filter_upwards [hB t] with ω h
    simpa only [pow_zero, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      mul_one] using h
  | succ k ih =>
    intro t
    have hei : Integrable (e (t + 1)) S.μ := integrable_of_adapted hea ⟨B, hB⟩ (t + 1)
    filter_upwards [abs_E_le_markov R hei (g := fun l => B * ∑ j, (absM T φ ^ k) l j)
      (ih (t + 1)), he t] with ω h1 h2
    rw [h2] at h1
    set i := R.regime t ω
    have hpos : 0 < |φ i| := abs_pos.2 (hφ i)
    have hval : ∑ j, T.P i j * (B * ∑ l, (absM T φ ^ k) j l) =
        |φ i| * (B * ∑ j, (absM T φ ^ (k + 1)) i j) := by
      have hs := sum_pow_succ (absM T φ) k i (fun _ => 1)
      simp only [mul_one] at hs
      rw [row_absM T (hφ i), hs]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hval, abs_mul] at h1
    exact le_of_mul_le_mul_left h1 hpos

/-- Cochrane (2023), pp. 522–523, genuinely: under the condition the homogeneous model has no
bounded adapted solution other than zero (a.e.) — no regime-dependent or extraneous sunspots. -/
theorem meas_homog_eq_zero (R : MeasMarkovRegimeN S T) {φ : Fin N → ℝ} (hc : GenCondition T φ)
    {e : ℕ → Ω → ℝ} (he : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] fun ω => φ (R.regime t ω) * e t ω)
    (hea : StronglyAdapted S.𝓕 e) (hb : S.BddProc e) : ∀ t, e t =ᵐ[S.μ] 0 := by
  obtain ⟨B, hB⟩ := hb
  intro t
  filter_upwards [ae_all_iff.2 fun k => meas_bound R hc.1 he hea hB k t] with ω h
  have hlim : Tendsto (fun k => B * ∑ j, (absM T φ ^ k) (R.regime t ω) j) atTop (𝓝 0) := by
    have hj : ∀ j ∈ Finset.univ,
        Tendsto (fun k => (absM T φ ^ k) (R.regime t ω) j) atTop (𝓝 0) :=
      fun j _ => (summable_abs_pow_entry hc.2 _ j).of_abs.tendsto_atTop_zero
    simpa using (tendsto_finsetSum Finset.univ hj).const_mul B
  have hle : |e t ω| ≤ 0 := ge_of_tendsto' hlim h
  simpa using abs_nonpos_iff.mp hle

/-! ### Existence: the forward solution -/

/-- Cochrane (2023), p. 523 (the forward solution, genuinely): `Δ_0(t) = −u_t/φ_{S_t}`,
`Δ_{k+1}(t) = E_t Δ_k(t+1)/φ_{S_t}`. -/
noncomputable def fwdM (R : MeasMarkovRegimeN S T) (φ : Fin N → ℝ) (u : ℕ → Ω → ℝ) :
    ℕ → ℕ → Ω → ℝ
  | 0, t => fun ω => -((φ (R.regime t ω))⁻¹ * u t ω)
  | k + 1, t => fun ω => (φ (R.regime t ω))⁻¹ * S.E t (fwdM R φ u k (t + 1)) ω

/-- Cochrane (2023), p. 523: `Δ_k(t)` is known at `t`. -/
theorem fwdM_sm (R : MeasMarkovRegimeN S T) (φ : Fin N → ℝ) {u : ℕ → Ω → ℝ}
    (hua : StronglyAdapted S.𝓕 u) (k t : ℕ) : StronglyMeasurable[S.𝓕 t] (fwdM R φ u k t) := by
  cases k with
  | zero => exact ((sm_comp R (fun i => (φ i)⁻¹) t).mul (hua t)).neg
  | succ k => exact (sm_comp R (fun i => (φ i)⁻¹) t).mul (S.stronglyMeasurable_E t _)

/-- Cochrane (2023), p. 523: the regime-wise bound `U ∑_l ((|Φ|⁻¹P)^k)_{il}/|φ_l|`. -/
noncomputable def bnd (T : TransitionN N) (φ : Fin N → ℝ) (U : ℝ) (k : ℕ) (i : Fin N) : ℝ :=
  U * ∑ l, (absM T φ ^ k) i l * (1 / |φ l|)

/-- Cochrane (2023), p. 523: `|Δ_k(t)| ≤ U ∑_l ((|Φ|⁻¹P)^k)_{S_t l}/|φ_l|` a.e. -/
theorem fwdM_bound (R : MeasMarkovRegimeN S T) {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0)
    {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) {U : ℝ} (hU : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ U)
    (k : ℕ) : ∀ t, ∀ᵐ ω ∂S.μ, |fwdM R φ u k t ω| ≤ bnd T φ U k (R.regime t ω) := by
  induction k with
  | zero =>
    intro t
    filter_upwards [hU t] with ω h
    simp only [fwdM, bnd, pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [abs_neg, abs_mul, abs_inv, mul_one_div, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right h (abs_nonneg _)
  | succ k ih =>
    intro t
    have hint : Integrable (fwdM R φ u k (t + 1)) S.μ :=
      MeasExpectationSystem.BddRV.integrable
        (MeasExpectationSystem.BddRV.of_stronglyMeasurable (fwdM_sm R φ hua k (t + 1))
          (M := ∑ l, |bnd T φ U k l|)
          ((ih (t + 1)).mono fun ω h => h.trans ((le_abs_self _).trans
            (abs_le_sum_abs (bnd T φ U k) _))))
    filter_upwards [abs_E_le_markov R hint (g := bnd T φ U k) (ih (t + 1))] with ω h1
    simp only [fwdM]
    set i := R.regime t ω
    have hpos : 0 < |φ i| := abs_pos.2 (hφ i)
    have hval : (|φ i|)⁻¹ * ∑ j, T.P i j * bnd T φ U k j = bnd T φ U (k + 1) i := by
      have hs := sum_pow_succ (absM T φ) k i (fun l => 1 / |φ l|)
      simp only [bnd]
      rw [row_absM T (hφ i), hs, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [abs_mul, abs_inv, ← hval]
    exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (abs_nonneg _))

/-- Cochrane (2023), p. 523: the dominating constants `c_k = ∑_i |bnd_k(i)|` bound `|Δ_k(t)|`. -/
theorem fwdM_bound_const (R : MeasMarkovRegimeN S T) {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0)
    {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) {U : ℝ}
    (hU : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ U) (k t : ℕ) :
    ∀ᵐ ω ∂S.μ, |fwdM R φ u k t ω| ≤ ∑ l, |bnd T φ U k l| := by
  filter_upwards [fwdM_bound R hφ hua hU k t] with ω h
  exact h.trans ((le_abs_self _).trans (abs_le_sum_abs (bnd T φ U k) _))

/-- Cochrane (2023), p. 523: under the condition the dominating constants are summable. -/
theorem summable_const (T : TransitionN N) {φ : Fin N → ℝ} (hc : GenCondition T φ) (U : ℝ) :
    Summable (fun k => ∑ l, |bnd T φ U k l|) :=
  summable_sum fun l _ => (summable_bound T hc U l).abs

/-- Cochrane (2023), p. 523: the forward solution `π_t = E_t ∑_k Δ_k(t)` (adapted by
construction; `fwdSolM_hasSum`: it is `∑_k Δ_k(t)` a.e.). -/
noncomputable def fwdSolM (R : MeasMarkovRegimeN S T) (φ : Fin N → ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  S.E t (fun ω => ∑' k, fwdM R φ u k t ω)

/-- Cochrane (2023), p. 523: under the condition the forward solution is the convergent series
`∑_k Δ_k(t)` a.e. -/
theorem fwdSolM_hasSum (R : MeasMarkovRegimeN S T) {φ : Fin N → ℝ} (hc : GenCondition T φ)
    {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) {U : ℝ}
    (hU : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ U) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => fwdM R φ u k t ω) (fwdSolM R φ u t ω) := by
  have hE := S.E_hasSum (f := fun k => fwdM R φ u k t) (summable_const T hc U)
    (fun k => ((fwdM_sm R φ hua k t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun k => fwdM_bound_const R hc.1 hua hU k t) t
  have hEk : ∀ k, S.E t (fwdM R φ u k t) = fwdM R φ u k t := fun k =>
    S.E_of_stronglyMeasurable (fwdM_sm R φ hua k t)
      (MeasExpectationSystem.BddRV.integrable
        (MeasExpectationSystem.BddRV.of_stronglyMeasurable (fwdM_sm R φ hua k t)
          (fwdM_bound_const R hc.1 hua hU k t)))
  filter_upwards [hE] with ω h
  simp only [hEk] at h
  exact h

/-- Cochrane (2023), pp. 522–523, genuinely: under the condition the forward solution solves
`E_t π_{t+1} = φ_{S_t} π_t + u_t` a.e. -/
theorem fwdSolM_solves (R : MeasMarkovRegimeN S T) {φ : Fin N → ℝ} (hc : GenCondition T φ)
    {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) {U : ℝ}
    (hU : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ U) : MSolves R φ u (fwdSolM R φ u) := by
  intro t
  have hcongr : S.E t (fwdSolM R φ u (t + 1)) =ᵐ[S.μ]
      S.E t (fun ω => ∑' k, fwdM R φ u k (t + 1) ω) :=
    S.E_congr ((fwdSolM_hasSum R hc hua hU (t + 1)).mono fun ω h => h.tsum_eq.symm) t
  have hE := S.E_hasSum (f := fun k => fwdM R φ u k (t + 1)) (summable_const T hc U)
    (fun k => ((fwdM_sm R φ hua k (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable)
    (fun k => fwdM_bound_const R hc.1 hua hU k (t + 1)) t
  filter_upwards [hcongr, hE, fwdSolM_hasSum R hc hua hU t] with ω e1 e2 e3
  rw [e1]
  have hφi := hc.1 (R.regime t ω)
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
theorem fwdSolM_bdd (R : MeasMarkovRegimeN S T) {φ : Fin N → ℝ} (hc : GenCondition T φ)
    {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) {U : ℝ}
    (hU : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ U) : S.BddProc (fwdSolM R φ u) := by
  refine ⟨∑' k, ∑ l, |bnd T φ U k l|, fun t => ?_⟩
  filter_upwards [fwdSolM_hasSum R hc hua hU t,
    ae_all_iff.2 fun k => fwdM_bound_const R hc.1 hua hU k t] with ω h hb
  have hs : Summable fun k => |fwdM R φ u k t ω| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hb (summable_const T hc U)
  rw [← h.tsum_eq]
  have hn := norm_tsum_le_tsum_norm (f := fun k => fwdM R φ u k t ω)
    (by simpa only [Real.norm_eq_abs] using hs)
  simp only [Real.norm_eq_abs] at hn
  exact hn.trans (Summable.tsum_le_tsum hb hs (summable_const T hc U))

/-- Cochrane (2023), p. 523: the forward solution is adapted. -/
theorem fwdSolM_adapted (R : MeasMarkovRegimeN S T) (φ : Fin N → ℝ) (u : ℕ → Ω → ℝ) :
    StronglyAdapted S.𝓕 (fwdSolM R φ u) := fun t => S.stronglyMeasurable_E t _

/-! ### Non-uniqueness when the condition fails -/

/-- Cochrane (2023), pp. 522–523: a nonzero bounded adapted solution of the homogeneous model
rules out determinacy. -/
theorem not_mdet_of_homog (R : MeasMarkovRegimeN S T) {φ : Fin N → ℝ} {e : ℕ → Ω → ℝ}
    (he : MSolves R φ 0 e) (hea : StronglyAdapted S.𝓕 e) (heb : S.BddProc e)
    (hne : ¬ e 0 =ᵐ[S.μ] 0) : ¬ MDeterminate R φ := by
  intro hd
  have huniq := (hd 0 (fun _ => stronglyMeasurable_zero)
    ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩).2
  have hz : MSolves R φ 0 0 := fun t => Eventually.of_forall fun ω => by simp [S.E_zero]
  exact hne (huniq e 0 he hz hea (fun _ => stronglyMeasurable_zero) heb
    ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩ 0)

/-- Cochrane (2023), p. 523 (**zero coefficients**): the process `π_0 = 1{S_0 = i}`,
`π_t = 0` for `t ≥ 1`. -/
noncomputable def zeroSunspot (R : MeasMarkovRegimeN S T) (i : Fin N) : ℕ → Ω → ℝ :=
  fun t ω => (if t = 0 then 1 else 0) * (if R.regime t ω = i then 1 else 0)

/-- Cochrane (2023), p. 523 (**zero coefficients, genuinely**): if `φ_i = 0`, the process
`π_0 = 1{S_0 = i}`, `π_t = 0` for `t ≥ 1` is a bounded adapted solution of the homogeneous
model. -/
theorem zero_coeff_homogM (R : MeasMarkovRegimeN S T) {φ : Fin N → ℝ} {i : Fin N}
    (hφ : φ i = 0) :
    MSolves R φ 0 (zeroSunspot R i) ∧ StronglyAdapted S.𝓕 (zeroSunspot R i) ∧
      S.BddProc (zeroSunspot R i) := by
  refine ⟨fun t => ?_, fun t => ?_, ⟨1, fun t => Eventually.of_forall fun ω => ?_⟩⟩
  · have h0 : zeroSunspot R i (t + 1) = 0 := by
      funext ω; simp [zeroSunspot]
    refine Eventually.of_forall fun ω => ?_
    rw [h0, S.E_zero]
    by_cases hr : R.regime t ω = i
    · simp [zeroSunspot, hr, hφ]
    · simp [zeroSunspot, hr]
  · exact (stronglyMeasurable_const.mul (sm_comp R (fun l => if l = i then 1 else 0) t))
  · simp only [zeroSunspot]
    split_ifs <;> simp

/-- Cochrane (2023), p. 523: the sign of the regime history, `s_0 = 1`,
`s_{t+1} = sgn φ_{S_t} · s_t`. -/
noncomputable def sgnProc (R : MeasMarkovRegimeN S T) (φ : Fin N → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun ω => sgn (φ (R.regime t ω)) * sgnProc R φ t ω

/-- Cochrane (2023), p. 523: `s_{t+1}` is known at `t`. -/
theorem sgnProc_succ_sm (R : MeasMarkovRegimeN S T) (φ : Fin N → ℝ) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (sgnProc R φ (t + 1)) := by
  induction t with
  | zero => exact (sm_comp R (fun l => sgn (φ l)) 0).mul stronglyMeasurable_const
  | succ t ih =>
    exact (sm_comp R (fun l => sgn (φ l)) (t + 1)).mul (ih.mono (S.𝓕.mono (Nat.le_succ t)))

/-- Cochrane (2023), p. 523: `s_t` is known at `t`. -/
theorem sgnProc_sm (R : MeasMarkovRegimeN S T) (φ : Fin N → ℝ) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (sgnProc R φ t) := by
  cases t with
  | zero => exact stronglyMeasurable_const
  | succ t => exact (sgnProc_succ_sm R φ t).mono (S.𝓕.mono (Nat.le_succ t))

/-- Cochrane (2023), p. 523: `|s_t| = 1`. -/
theorem abs_sgnProc (R : MeasMarkovRegimeN S T) (φ : Fin N → ℝ) (t : ℕ) (ω : Ω) :
    |sgnProc R φ t ω| = 1 := by
  induction t with
  | zero => simp [sgnProc]
  | succ t ih => simp only [sgnProc]; rw [abs_mul, abs_sgn, ih, one_mul]

/-- Cochrane (2023), pp. 522–523 (**the sign-twisted sunspot, genuinely**): if
`x_t = |Φ|⁻¹P x_{t+1}` and every `φ_i ≠ 0`, then `π_t = s_t x_t(S_t)` solves the homogeneous
model `E_t π_{t+1} = φ_{S_t} π_t` a.e. -/
theorem twisted_solves (R : MeasMarkovRegimeN S T) {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0)
    {x : ℕ → Fin N → ℝ} (hx : ∀ t, x t = absM T φ *ᵥ x (t + 1)) :
    MSolves R φ 0 (fun t ω => sgnProc R φ t ω * x t (R.regime t ω)) := by
  intro t
  have hpull := S.E_pullOut (sgnProc_succ_sm R φ t) (C := 1)
    (Eventually.of_forall fun ω => (abs_sgnProc R φ (t + 1) ω).le)
    (bddRV_comp R (x (t + 1)) (t + 1)).integrable
  filter_upwards [hpull, R.markov t (x (t + 1))] with ω h1 h2
  change S.E t (sgnProc R φ (t + 1) * fun ω => x (t + 1) (R.regime (t + 1) ω)) ω = _
  rw [h1, Pi.mul_apply, h2]
  set i := R.regime t ω
  have hrow : ∑ j, T.P i j * x (t + 1) j = |φ i| * x t i := by
    rw [row_absM T (hφ i), hx t]
    rfl
  rw [hrow]
  simp only [sgnProc, Pi.zero_apply, add_zero]
  linear_combination (sgnProc R φ t ω * x t i) * sgn_mul_abs (φ i)

/-! ### The determinacy theorem -/

/-- Cochrane (2023), pp. 522–523 (**Davig–Leeper for `N` regimes and any signs, genuinely**): in
any `MeasExpectationSystem` carrying an `N`-state Markov regime process in which every regime has
positive probability at date `0`, the model `E_t π_{t+1} = φ_{S_t} π_t + u_t` has, for every
bounded adapted disturbance, a bounded adapted equilibrium that is unique up to a.e. equality iff
every `φ_i ≠ 0` and the spectral radius of `|Φ|⁻¹P` is `< 1`. -/
theorem meas_determinate_iff (R : MeasMarkovRegimeN S T) (φ : Fin N → ℝ)
    (hS0 : ∀ i, S.μ {ω | R.regime 0 ω = i} ≠ 0) : MDeterminate R φ ↔ GenCondition T φ := by
  constructor
  · intro hd
    by_cases h0 : ∀ i, φ i ≠ 0
    · refine ⟨h0, ?_⟩
      by_contra hns
      obtain ⟨x, hx, ⟨B, hB⟩, i₀, hi₀⟩ := exists_bdd_backward hns
      refine not_mdet_of_homog R (twisted_solves R h0 hx)
        (fun t => (sgnProc_sm R φ t).mul (sm_comp R (x t) t))
        ⟨B, fun t => Eventually.of_forall fun ω => ?_⟩ ?_ hd
      · rw [abs_mul, abs_sgnProc, one_mul]; exact hB _ _
      · intro hz
        apply hS0 i₀
        refine measure_mono_null (fun ω (hω : R.regime 0 ω = i₀) => ?_) (ae_iff.1 hz)
        simp only [Set.mem_ofPred_eq, sgnProc, one_mul, hω, Pi.zero_apply]
        exact hi₀
    · push Not at h0
      obtain ⟨i, hi⟩ := h0
      obtain ⟨hs, ha, hb⟩ := zero_coeff_homogM R (S := S) hi
      refine absurd hd (not_mdet_of_homog R hs ha hb fun hz => hS0 i ?_)
      refine measure_mono_null (fun ω (hω : R.regime 0 ω = i) => ?_) (ae_iff.1 hz)
      simp [zeroSunspot, hω]
  · intro hc u hua ⟨U, hU⟩
    refine ⟨⟨fwdSolM R φ u, fwdSolM_solves R hc hua hU, fwdSolM_adapted R φ u,
      fwdSolM_bdd R hc hua hU⟩, ?_⟩
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
    have hz := meas_homog_eq_zero R hc (e := fun t => π₁ t - π₂ t) he
      (fun t => (ha₁ t).sub (ha₂ t)) ⟨B₁ + B₂, fun t => by
        filter_upwards [hB₁ t, hB₂ t] with ω e1 e2
        exact (abs_sub _ _).trans (add_le_add e1 e2)⟩
    intro t
    filter_upwards [hz t] with ω e
    exact sub_eq_zero.mp e

/-- Cochrane (2023), pp. 522–523 (**link** with the tree theorem `determinate_iff`): determinacy
on the genuine probability space is equivalent to determinacy on the regime tree. -/
theorem meas_determinate_iff_tree (R : MeasMarkovRegimeN S T) (φ : Fin N → ℝ)
    (hS0 : ∀ i, S.μ {ω | R.regime 0 ω = i} ≠ 0) : MDeterminate R φ ↔ Determinate T φ :=
  (meas_determinate_iff R φ hS0).trans (determinate_iff T φ).symm

/-- Cochrane (2023), pp. 522–523, genuinely: determinacy depends only on `|φ_i|`. -/
theorem meas_determinate_iff_abs (R : MeasMarkovRegimeN S T) (φ : Fin N → ℝ)
    (hS0 : ∀ i, S.μ {ω | R.regime 0 ω = i} ≠ 0) :
    MDeterminate R φ ↔ MDeterminate R (fun i => |φ i|) := by
  rw [meas_determinate_iff_tree R φ hS0, meas_determinate_iff_tree R _ hS0]
  exact determinate_iff_abs T φ

/-! ### Two regimes: the special case of `MarkovRegimesMeasure` -/

/-- Cochrane (2023), p. 522: a two-state Markov regime of `MarkovRegimesMeasure` as an `N = 2`
Markov regime. -/
def ofTwoRegime {T₂ : MarkovRegimes.Transition}
    (R : MarkovRegimesMeasure.MeasMarkovRegime S T₂) : MeasMarkovRegimeN S (ofTwo T₂) :=
  ⟨R.regime, R.adapted, R.markov⟩

/-- Cochrane (2023), pp. 522–523 (**link**): for `N = 2` the genuine model is exactly that of
`MarkovRegimesMeasure`. -/
theorem msolves_ofTwo {T₂ : MarkovRegimes.Transition}
    (R : MarkovRegimesMeasure.MeasMarkovRegime S T₂) (φ : Fin 2 → ℝ) (u π : ℕ → Ω → ℝ) :
    MSolves (ofTwoRegime R) φ u π ↔ MarkovRegimesMeasure.MSolves R φ u π :=
  Iff.rfl

/-- Cochrane (2023), pp. 522–523 (**the two-regime, `φ > 0` result recovered**): for two regimes
with `φ_0, φ_1 > 0`, genuine determinacy holds iff Davig and Leeper's condition holds. -/
theorem meas_two_regime_recovered {T₂ : MarkovRegimes.Transition}
    (R : MarkovRegimesMeasure.MeasMarkovRegime S T₂) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hS0 : ∀ i, S.μ {ω | R.regime 0 ω = i} ≠ 0) :
    MDeterminate (ofTwoRegime R) φ ↔ MarkovRegimes.DLCondition T₂ φ :=
  (meas_determinate_iff (ofTwoRegime R) φ hS0).trans (dl_iff_genCondition T₂ hφ).symm

/-- Cochrane (2023), pp. 522–523 (**the corrected two-regime formula, genuinely**): for two regimes
and coefficients of any sign, genuine determinacy holds iff `φ_0, φ_1 ≠ 0` and the Davig–Leeper
formula holds for `|φ_0|, |φ_1|`. -/
theorem meas_dl_corrected {T₂ : MarkovRegimes.Transition}
    (R : MarkovRegimesMeasure.MeasMarkovRegime S T₂) (φ : Fin 2 → ℝ)
    (hS0 : ∀ i, S.μ {ω | R.regime 0 ω = i} ≠ 0) :
    MDeterminate (ofTwoRegime R) φ ↔
      (∀ i, φ i ≠ 0) ∧ MarkovRegimes.DLCondition T₂ (fun i => |φ i|) :=
  (meas_determinate_iff_tree (ofTwoRegime R) φ hS0).trans (dl_corrected T₂ φ)

/-! ### A genuine `N`-state Markov chain driven by i.i.d. uniforms -/

/-- Cochrane (2023), p. 522 (sampling a regime): the cumulative probabilities
`c_k = ∑_{l < k} p_l`. -/
noncomputable def cumP (p : Fin N → ℝ) (k : ℕ) : ℝ := ∑ l : Fin N, if (l : ℕ) < k then p l else 0

/-- Cochrane (2023), p. 522: `c_0 = 0`. -/
theorem cumP_zero (p : Fin N → ℝ) : cumP p 0 = 0 := by simp [cumP]

/-- Cochrane (2023), p. 522: the cumulative probabilities are monotone. -/
theorem cumP_mono {p : Fin N → ℝ} (hp : ∀ j, 0 ≤ p j) {k k' : ℕ} (h : k ≤ k') :
    cumP p k ≤ cumP p k' := by
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases h1 : (l : ℕ) < k
  · simp [h1, show (l : ℕ) < k' by omega]
  · simp only [h1, ↓reduceIte]
    split_ifs
    · exact hp l
    · exact le_rfl

/-- Cochrane (2023), p. 522: `c_N = ∑_l p_l = 1`. -/
theorem cumP_top {p : Fin N → ℝ} (hp1 : ∑ j, p j = 1) : cumP p N = 1 := by
  simp only [cumP, Fin.is_lt, ↓reduceIte]
  exact hp1

/-- Cochrane (2023), p. 522: `c_k ≤ 1`. -/
theorem cumP_le_one {p : Fin N → ℝ} (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (k : ℕ) :
    cumP p k ≤ 1 := by
  rw [← hp1]
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs
  · exact le_rfl
  · exact hp l

/-- Cochrane (2023), p. 522: `c_{j+1} = c_j + p_j`. -/
theorem cumP_succ (p : Fin N → ℝ) (j : Fin N) : cumP p (j + 1) = cumP p j + p j := by
  have key : ∀ l : Fin N, (if (l : ℕ) < j + 1 then p l else 0) =
      (if (l : ℕ) < j then p l else 0) + (if l = j then p l else 0) := by
    intro l
    by_cases h1 : (l : ℕ) < j
    · have hne : l ≠ j := fun h => by rw [h] at h1; omega
      simp [h1, hne, show (l : ℕ) < j + 1 by omega]
    · by_cases h2 : l = j
      · subst h2; simp
      · have hv : (l : ℕ) ≠ j := fun h => h2 (Fin.ext h)
        have : ¬ (l : ℕ) < j + 1 := by omega
        simp [h1, h2, this]
  simp only [cumP, key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Cochrane (2023), p. 522: the number of regimes whose cumulative probability `c_{l+1}` is at
most `x`. -/
noncomputable def cnt (p : Fin N → ℝ) (x : ℝ) : ℕ :=
  (Finset.univ.filter fun l : Fin N => cumP p (l + 1) ≤ x).card

/-- Cochrane (2023), p. 522: the count is monotone in `x`. -/
theorem cnt_mono (p : Fin N → ℝ) : Monotone (cnt p) := fun x y hxy =>
  Finset.card_le_card fun l hl => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    linarith

/-- Cochrane (2023), p. 522 (inverse-CDF sampling): `pick p x = j` iff `c_j ≤ x < c_{j+1}` (for
`x ∈ [0, 1)`, `pick_spec`). -/
noncomputable def pick [NeZero N] (p : Fin N → ℝ) (x : ℝ) : Fin N :=
  ⟨min (cnt p x) (N - 1), Nat.lt_of_le_of_lt (min_le_right _ _)
    (Nat.sub_lt (NeZero.pos N) Nat.one_pos)⟩

/-- Cochrane (2023), p. 522: sampling is measurable. -/
theorem measurable_pick [NeZero N] (p : Fin N → ℝ) : Measurable (pick p) :=
  (measurable_from_nat (f := fun n => (⟨min n (N - 1), Nat.lt_of_le_of_lt (min_le_right _ _)
    (Nat.sub_lt (NeZero.pos N) Nat.one_pos)⟩ : Fin N))).comp (cnt_mono p).measurable

/-- Cochrane (2023), p. 522: if `c_j ≤ x < c_{j+1}` then `pick p x = j`. -/
theorem pick_eq [NeZero N] {p : Fin N → ℝ} (hp : ∀ j, 0 ≤ p j) {x : ℝ} {j : Fin N}
    (h1 : cumP p j ≤ x) (h2 : x < cumP p (j + 1)) : pick p x = j := by
  have hset : (Finset.univ.filter fun l : Fin N => cumP p (l + 1) ≤ x) =
      Finset.univ.filter fun l : Fin N => (l : ℕ) < j := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hl
      by_contra hlj
      push Not at hlj
      have := cumP_mono hp (show (j : ℕ) + 1 ≤ l + 1 by omega)
      linarith
    · intro hl
      exact (cumP_mono hp (show (l : ℕ) + 1 ≤ j by omega)).trans h1
  have hc : cnt p x = j := by
    rw [cnt, hset, Fin.card_filter_val_lt]
    exact min_eq_right j.isLt.le
  ext
  simp only [pick, hc]
  have := j.isLt
  omega

/-- Cochrane (2023), p. 522: every `x ∈ [0, 1)` lies in some `[c_j, c_{j+1})`. -/
theorem exists_interval [NeZero N] {p : Fin N → ℝ} (hp1 : ∑ j, p j = 1) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < 1) : ∃ j : Fin N, cumP p j ≤ x ∧ x < cumP p (j + 1) := by
  classical
  have hN := NeZero.pos N
  have htop : x < cumP p (N - 1 + 1) := by
    rw [Nat.sub_add_cancel hN, cumP_top hp1]; exact hx1
  have hex : ∃ k, x < cumP p (k + 1) := ⟨N - 1, htop⟩
  have hk : x < cumP p (Nat.find hex + 1) := Nat.find_spec hex
  have hkN : Nat.find hex < N := by
    have := Nat.find_min' hex htop
    omega
  refine ⟨⟨Nat.find hex, hkN⟩, ?_, hk⟩
  change cumP p (Nat.find hex) ≤ x
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, cumP_zero]; exact hx0
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at this
    rwa [Nat.sub_add_cancel hpos] at this

/-- Cochrane (2023), p. 522: for `x ∈ [0, 1)`, `pick p x = j` iff `c_j ≤ x < c_{j+1}`. -/
theorem pick_spec [NeZero N] {p : Fin N → ℝ} (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) (j : Fin N) :
    pick p x = j ↔ cumP p j ≤ x ∧ x < cumP p (j + 1) := by
  constructor
  · intro h
    obtain ⟨j', h1, h2⟩ := exists_interval hp1 hx0 hx1
    have := pick_eq hp h1 h2
    rw [h] at this
    subst this
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact pick_eq hp h1 h2

/-- Cochrane (2023), p. 522: `Pr(pick p U = j) = p_j` for a uniform `U`. -/
theorem unif_pick [NeZero N] {p : Fin N → ℝ} (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (j : Fin N) :
    (MarkovRegimesMeasure.unifProb : Measure ℝ) {x | pick p x = j} = ENNReal.ofReal (p j) := by
  change volume.restrict (Set.Icc 0 1) {x | pick p x = j} = _
  have hms : MeasurableSet {x | pick p x = j} := measurable_pick p (measurableSet_singleton j)
  rw [Measure.restrict_apply hms]
  have hI : volume (Set.Ico (cumP p j) (cumP p (j + 1))) = ENNReal.ofReal (p j) := by
    rw [Real.volume_Ico, cumP_succ, add_sub_cancel_left]
  have hsub1 : Set.Ico (cumP p j) (cumP p (j + 1)) ⊆ {x | pick p x = j} ∩ Set.Icc 0 1 := by
    intro x ⟨h1, h2⟩
    have h0 : 0 ≤ cumP p j := (cumP_zero p).symm.le.trans (cumP_mono hp (Nat.zero_le _))
    have hle := cumP_le_one hp hp1 (j + 1)
    exact ⟨pick_eq hp h1 h2, by linarith, by linarith⟩
  have hsub2 : {x | pick p x = j} ∩ Set.Icc 0 1 ⊆
      Set.Ico (cumP p j) (cumP p (j + 1)) ∪ {1} := by
    intro x ⟨hx, h0, h1⟩
    rcases h1.lt_or_eq with hlt | heq
    · exact Or.inl ((pick_spec hp hp1 h0 hlt j).1 hx)
    · exact Or.inr heq
  refine le_antisymm ?_ (hI ▸ measure_mono hsub1)
  calc volume ({x | pick p x = j} ∩ Set.Icc 0 1)
      ≤ volume (Set.Ico (cumP p j) (cumP p (j + 1)) ∪ {1}) := measure_mono hsub2
    _ ≤ volume (Set.Ico (cumP p j) (cumP p (j + 1))) + volume ({1} : Set ℝ) :=
        measure_union_le _ _
    _ = ENNReal.ofReal (p j) := by rw [hI, Real.volume_singleton, add_zero]

/-- Cochrane (2023), p. 522: `E f(pick p U) = ∑_j p_j f(j)` for a uniform `U`. -/
theorem integral_pick [NeZero N] {p : Fin N → ℝ} (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (f : Fin N → ℝ) :
    ∫ x, f (pick p x) ∂(MarkovRegimesMeasure.unifProb : Measure ℝ) = ∑ j, p j * f j := by
  have hm := measurable_pick p
  rw [← integral_map hm.aemeasurable
    (Measurable.of_discrete (f := f)).stronglyMeasurable.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, measureReal_def, Measure.map_apply hm (measurableSet_singleton j)]
  change ((MarkovRegimesMeasure.unifProb : Measure ℝ) {x | pick p x = j}).toReal * f j = _
  rw [unif_pick hp hp1, ENNReal.toReal_ofReal (hp j)]

/-- Cochrane (2023), p. 522 (**the `N`-state regime process**): `S_0 = pick q U_0` and
`S_{t+1} = pick P_{S_t} U_{t+1}`, with i.i.d. uniforms `U_t(ω) = ω_t`. -/
noncomputable def chainN [NeZero N] (T : TransitionN N) (q : Fin N → ℝ) :
    ℕ → (ℕ → ℝ) → Fin N
  | 0 => fun ω => pick q (ω 0)
  | t + 1 => fun ω => pick (T.P (chainN T q t ω)) (ω (t + 1))

/-- Cochrane (2023), p. 522: the regime is known at each date. -/
theorem chainN_measurable [NeZero N] (T : TransitionN N) (q : Fin N → ℝ) (t : ℕ) :
    Measurable[(iidSystem MarkovRegimesMeasure.unifProb).𝓕 t] (chainN T q t) := by
  induction t with
  | zero =>
    exact (measurable_pick q).comp (measurable_shock MarkovRegimesMeasure.unifProb le_rfl)
  | succ t ih =>
    have hF : Measurable (fun z : Fin N × ℝ => pick (T.P z.1) z.2) :=
      measurable_from_prod_countable_right fun i => measurable_pick (T.P i)
    have heq : chainN T q (t + 1) = (fun z : Fin N × ℝ => pick (T.P z.1) z.2) ∘
        (fun ω => (chainN T q t ω, shock (t + 1) ω)) := by
      funext ω
      simp only [chainN, Function.comp_apply, shock]
    rw [heq]
    exact hF.comp ((ih.mono ((iidSystem MarkovRegimesMeasure.unifProb).𝓕.mono
      (Nat.le_succ t)) le_rfl).prodMk
      (measurable_shock MarkovRegimesMeasure.unifProb le_rfl))

/-- Cochrane (2023), p. 522 (**the Markov property**): `E_t f(S_{t+1}) = ∑_j P_{S_t j} f(j)`
a.e. — the regime process is an `N`-state Markov chain with transition matrix `P`. -/
theorem chainN_markov [NeZero N] (T : TransitionN N) (q : Fin N → ℝ) (t : ℕ)
    (f : Fin N → ℝ) :
    (iidSystem MarkovRegimesMeasure.unifProb).E t (fun ω => f (chainN T q (t + 1) ω))
      =ᵐ[(iidSystem MarkovRegimesMeasure.unifProb).μ]
      fun ω => ∑ j, T.P (chainN T q t ω) j * f j := by
  set Sy := iidSystem MarkovRegimesMeasure.unifProb
  set ind : Fin N → (ℕ → ℝ) → ℝ := fun i ω => if chainN T q t ω = i then 1 else 0 with hind
  set y : Fin N → (ℕ → ℝ) → ℝ := fun i ω => f (pick (T.P i) (ω (t + 1))) with hy
  have hdec : (fun ω => f (chainN T q (t + 1) ω)) = ∑ i, ind i * y i := by
    funext ω
    simp only [Finset.sum_apply, Pi.mul_apply, hind, hy]
    rw [Finset.sum_eq_single (chainN T q t ω)]
    · simp [chainN]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have hgm : ∀ i : Fin N, Measurable (fun x => f (pick (T.P i) x)) := fun i =>
    (Measurable.of_discrete (f := f)).comp (measurable_pick (T.P i))
  have hindsm : ∀ i, StronglyMeasurable[Sy.𝓕 t] (ind i) := fun i =>
    ((Measurable.of_discrete (f := fun c : Fin N => if c = i then (1 : ℝ) else 0)).comp
      (chainN_measurable T q t)).stronglyMeasurable
  have hindb : ∀ i, ∀ᵐ ω ∂Sy.μ, |ind i ω| ≤ 1 := fun i =>
    Eventually.of_forall fun ω => by simp only [hind]; split_ifs <;> simp
  have hyB : ∀ i, Sy.BddRV (y i) := fun i =>
    ⟨((hgm i).comp (measurable_pi_apply (t + 1))).aestronglyMeasurable, ∑ l, |f l|,
      Eventually.of_forall fun ω => abs_le_sum_abs f _⟩
  have hindB : ∀ i, Sy.BddRV (ind i) := fun i =>
    MeasExpectationSystem.BddRV.of_stronglyMeasurable (hindsm i) (hindb i)
  have hterm : ∀ i, Sy.E t (ind i * y i) =ᵐ[Sy.μ] fun ω => ind i ω * ∑ j, T.P i j * f j := by
    intro i
    have hEy : Sy.E t (y i) =ᵐ[Sy.μ] fun _ => ∑ j, T.P i j * f j := by
      rw [← integral_pick (T.nonneg i) (T.rowSum i) f]
      exact E_shock_fun MarkovRegimesMeasure.unifProb t (hgm i)
    filter_upwards [Sy.E_pullOut (hindsm i) (hindb i) (hyB i).integrable, hEy] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
  rw [hdec]
  filter_upwards [condExp_finsetSum (s := Finset.univ) (f := fun i => ind i * y i)
    (fun i _ => ((hindB i).mul (hyB i)).integrable) (Sy.𝓕 t), ae_all_iff.2 hterm]
    with ω h1 h2
  refine h1.trans ?_
  rw [Finset.sum_apply]
  refine (Finset.sum_congr rfl fun i _ => h2 i).trans ?_
  simp only [hind]
  rw [Finset.sum_eq_single (chainN T q t ω)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

/-- Cochrane (2023), p. 522: the regime process of `chainN` as an `N`-state Markov regime of the
i.i.d. expectation system with uniform shocks. -/
noncomputable def chainRegimeN [NeZero N] (T : TransitionN N) (q : Fin N → ℝ) :
    MeasMarkovRegimeN (iidSystem MarkovRegimesMeasure.unifProb) T :=
  ⟨chainN T q, chainN_measurable T q, chainN_markov T q⟩

/-- Cochrane (2023), p. 522: the initial distribution, `Pr(S_0 = i) = q_i`. -/
theorem chainN_initial [NeZero N] (T : TransitionN N) {q : Fin N → ℝ} (hq0 : ∀ j, 0 ≤ q j)
    (hq1 : ∑ j, q j = 1) (i : Fin N) :
    (iidSystem MarkovRegimesMeasure.unifProb).μ {ω | chainN T q 0 ω = i} =
      ENNReal.ofReal (q i) := by
  have hmp := measurePreserving_eval_infinitePi
    (fun _ => (MarkovRegimesMeasure.unifProb : Measure ℝ)) 0
  have e0 : {ω : ℕ → ℝ | chainN T q 0 ω = i} = Function.eval 0 ⁻¹' (pick q ⁻¹' {i}) :=
    rfl
  rw [e0]
  change Measure.infinitePi (fun _ => (MarkovRegimesMeasure.unifProb : Measure ℝ)) _ = _
  rw [hmp.measure_preimage (measurable_pick q (measurableSet_singleton i)).nullMeasurableSet]
  exact unif_pick hq0 hq1 i

/-- Cochrane (2023), p. 522: with `q_i > 0` every regime has positive probability at date `0`. -/
theorem chainN_initial_pos [NeZero N] (T : TransitionN N) {q : Fin N → ℝ}
    (hq0 : ∀ j, 0 < q j) (hq1 : ∑ j, q j = 1) (i : Fin N) :
    (iidSystem MarkovRegimesMeasure.unifProb).μ {ω | (chainRegimeN T q).regime 0 ω = i} ≠ 0 := by
  change (iidSystem MarkovRegimesMeasure.unifProb).μ {ω | chainN T q 0 ω = i} ≠ 0
  rw [chainN_initial T (fun j => (hq0 j).le) hq1 i, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact hq0 i

/-- Cochrane (2023), pp. 522–523 (**Davig–Leeper for `N` regimes and any signs, on a genuine
Markov chain**): for the `N`-state chain driven by i.i.d. uniforms with every `q_i > 0`, bounded
adapted equilibria exist and are unique (a.e.) for every bounded adapted disturbance iff every
`φ_i ≠ 0` and the spectral radius of `|Φ|⁻¹P` is `< 1`, iff the tree model is determinate. -/
theorem chainN_determinate_iff [NeZero N] (T : TransitionN N) {q : Fin N → ℝ}
    (hq0 : ∀ j, 0 < q j) (hq1 : ∑ j, q j = 1) (φ : Fin N → ℝ) :
    (MDeterminate (chainRegimeN T q) φ ↔ GenCondition T φ) ∧
      (MDeterminate (chainRegimeN T q) φ ↔ Determinate T φ) :=
  ⟨meas_determinate_iff _ φ (chainN_initial_pos T hq0 hq1),
    meas_determinate_iff_tree _ φ (chainN_initial_pos T hq0 hq1)⟩

/-- Cochrane (2023), p. 523 (**three regimes on a genuine chain**): three equally likely i.i.d.
regimes with `φ = (4, −4, ½)` — one negative, one passive — give a determinate economy. -/
theorem chainN_three_regime_determinate :
    MDeterminate (chainRegimeN (iidT (fun _ : Fin 3 => 1 / 3) (fun _ => by norm_num)
      (by simp)) (fun _ => 1 / 3)) ![4, -4, 1 / 2] :=
  ((chainN_determinate_iff _ (fun _ => by norm_num) (by simp) _).2).2 three_regime_determinate

/-- Cochrane (2023), p. 523 (**a negative regime that is still determinate, genuinely**): on the
two-state chain of `MarkovRegimesMeasure` with `p_00 = 0.9`, `p_11 = 0.4`, `0 < q < 1` and
`φ = (2, −½)`, the economy is determinate. -/
theorem chain_negative_regime_determinate {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    MDeterminate (ofTwoRegime (MarkovRegimesMeasure.chainRegime MarkovRegimes.egShortPassive q))
      ![2, -1 / 2] :=
  (meas_determinate_iff_tree _ _
    (MarkovRegimesMeasure.chain_initial_pos MarkovRegimes.egShortPassive hq0 hq1)).2
    negative_regime_determinate

/-- Cochrane (2023), pp. 522–523 (**the Davig–Leeper formula fails with a negative coefficient,
genuinely**): on the two-state chain with `p_00 = 0.9`, `p_11 = 0.5`, `0 < q < 1` and
`φ = (½, −½)`, the formula holds but the economy is indeterminate. -/
theorem chain_dl_formula_fails_negative {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    MarkovRegimes.DLCondition egDL ![1 / 2, -1 / 2] ∧
      ¬ MDeterminate (ofTwoRegime (MarkovRegimesMeasure.chainRegime egDL q)) ![1 / 2, -1 / 2] :=
  ⟨dl_formula_fails_negative.1, fun h => dl_formula_fails_negative.2
    ((meas_determinate_iff_tree _ _
      (MarkovRegimesMeasure.chain_initial_pos egDL hq0 hq1)).1 h)⟩

/-- Cochrane (2023), p. 523 (**the naive condition is not sufficient, genuinely**): on the
two-state chain with `p_ij = ½`, `0 < q < 1` and `φ = (½, −½)`, `Φ⁻¹P` is nilpotent but the
economy is indeterminate. -/
theorem chain_naive_not_sufficient {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    NaiveCondition (ofTwo egHalf) ![1 / 2, -1 / 2] ∧
      ¬ MDeterminate (ofTwoRegime (MarkovRegimesMeasure.chainRegime egHalf q)) ![1 / 2, -1 / 2] :=
  ⟨naive_not_sufficient.1, fun h => naive_not_sufficient.2
    ((meas_determinate_iff_tree _ _
      (MarkovRegimesMeasure.chain_initial_pos egHalf hq0 hq1)).1 h)⟩

end Cochrane.ObservationalEquivalence.MarkovRegimesGeneralMeasure
