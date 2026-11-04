/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.TidyR6MarkovNoGo
import ObservationalEquivalence.ForwardSolution

/-!
# `N`-regime Markov switching in an abstract expectation system with the pull-out property

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 24, §24.2, pp. 522–523 (Davig and
Leeper (2006, 2007); "the Markov assumption, with exactly two (or even N) states", p. 523), and
Chapter 22, §22.3, p. 500.

In an `ExpectationSystem` with the pull-out property (`ExpectationSystem.PullOut`), a Markov regime
process (`TidyR6MarkovAbstractN.MarkovRegimeN`) that is known at each date
(`TidyR6MarkovNoGo.RegimeAdapted`) gives the full Davig–Leeper theorem for **arbitrary** bounded
adapted disturbances, not only for disturbances driven by the regime history.

## Main results

* `wt`: the weights `w_{t,k} = ∏_{s=0}^{k} 1/φ_{S_{t+s}}`; `E_abs_wt`:
  `E_t |w_{t,k}| = ∑_j ((|Φ|⁻¹P)^k)_{S_t j}/|φ_j|`.
* `fwdP`: the forward solution `π_t = −∑_k E_t(w_{t,k} u_{t+k})`; `fwdP_solves`, `fwdP_bounded`,
  `fwdP_adapted` (under `GenCondition`); the infinite sum is exchanged with `E_t` by
  `ForwardSolution.E_tsum_dom`, which needs no further hypothesis.
* `pullOut_twisted`: if the spectral radius of `|Φ|⁻¹P` is not `< 1`, the sign-twisted sunspot
  `π_t = s_t x_t(S_t)` is a nonzero bounded solution of the homogeneous model.
* `pullOut_determinate_iff` (**Davig–Leeper for `N` regimes and any signs**): with all regimes
  possible at date `0`, for every bounded adapted disturbance there is exactly one bounded
  equilibrium iff `GenCondition`.

These hypotheses include a known regime, so with non-degenerate transitions they have no model on a
countable state space and no model with a pointwise-linear forecast
(`TidyR6MarkovNoGo.countable_no_regime`, `TidyR6MarkovNoGo.not_pointwiseLinear`). Their buildable
models have degenerate transitions (`TidyR6MarkovInstances`); the substantive non-degenerate
versions are `MarkovRegimesGeneral.determinate_iff` (regime tree) and
`MarkovRegimesGeneralMeasure.meas_determinate_iff` (probability space).
-/

namespace Cochrane.ObservationalEquivalence.TidyR6MarkovPullOut

open Filter Topology
open Cochrane.ObservationalEquivalence.MarkovRegimesGeneral
open Cochrane.ObservationalEquivalence.TidyR6MarkovAbstractN
open Cochrane.ObservationalEquivalence.TidyR6MarkovNoGo

variable {Ω : Type*} {N : ℕ}

/-- Cochrane (2023), p. 523: the forward weights `w_{t,k} = ∏_{s=0}^{k} 1/φ_{S_{t+s}}`, with
`w_{t,0} = 1/φ_{S_t}` and `w_{t,k+1} = (1/φ_{S_t}) w_{t+1,k}`. -/
noncomputable def wt (S : ℕ → Ω → Fin N) (φ : Fin N → ℝ) : ℕ → ℕ → Ω → ℝ
  | t, 0, ω => 1 / φ (S t ω)
  | t, k + 1, ω => 1 / φ (S t ω) * wt S φ (t + 1) k ω

/-- Cochrane (2023), p. 523: the `k`-th term of the forward solution, `E_t(w_{t,k} u_{t+k})`.
Abstract form of `MarkovRegimesGeneral.fwdTerm`. -/
noncomputable def fterm (𝔼 : ExpectationSystem Ω) (S : ℕ → Ω → Fin N) (φ : Fin N → ℝ)
    (u : ℕ → Ω → ℝ) (t k : ℕ) : Ω → ℝ :=
  𝔼.E t (wt S φ t k * u (t + k))

/-- Cochrane (2023), pp. 522–523: the forward solution `π_t = −∑_k E_t(w_{t,k} u_{t+k})`.
Abstract form of `MarkovRegimesGeneral.fwdSol` and `MarkovRegimesGeneralMeasure.fwdSolM`. -/
noncomputable def fwdP (𝔼 : ExpectationSystem Ω) (S : ℕ → Ω → Fin N) (φ : Fin N → ℝ)
    (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => -∑' k, fterm 𝔼 S φ u t k ω

/-- Cochrane (2023), p. 523: the summable bound `∑_i ∑_j |((|Φ|⁻¹P)^k)_{ij}|/|φ_j|`.
As `MarkovRegimesGeneralMeasure.bnd`. -/
noncomputable def bnd (T : TransitionN N) (φ : Fin N → ℝ) (k : ℕ) : ℝ :=
  ∑ i, ∑ j, |(absM T φ ^ k) i j| * (1 / |φ j|)

variable {𝔼 : ExpectationSystem Ω} {T : TransitionN N}

/-- Cochrane (2023), p. 523: the weight `w_{t,k}` is known at date `t + k`. -/
theorem wt_adapted (hP : 𝔼.PullOut) {S : ℕ → Ω → Fin N} (hA : RegimeAdapted 𝔼 S)
    (φ : Fin N → ℝ) : ∀ k t, 𝔼.E (t + k) (wt S φ t k) = wt S φ t k := by
  intro k
  induction k with
  | zero => intro t; exact hA t (fun l => 1 / φ l)
  | succ k ih =>
    intro t
    have hfun : wt S φ t (k + 1) = (fun ω => 1 / φ (S t ω)) * wt S φ (t + 1) k := rfl
    have ha : 𝔼.E (t + (k + 1)) (fun ω => 1 / φ (S t ω)) = fun ω => 1 / φ (S t ω) :=
      adapted_later hA (by omega) (fun l => 1 / φ l)
    rw [hfun, hP _ _ _ ha, show t + (k + 1) = t + 1 + k by omega, ih (t + 1)]

/-- Cochrane (2023), p. 523: `|w_{t,k+1}| = (1/|φ_{S_t}|) |w_{t+1,k}|`. -/
theorem abs_wt_succ (S : ℕ → Ω → Fin N) (φ : Fin N → ℝ) (t k : ℕ) :
    (fun ω => |wt S φ t (k + 1) ω|) =
      (fun ω => 1 / |φ (S t ω)|) * fun ω => |wt S φ (t + 1) k ω| := by
  funext ω
  simp only [wt, Pi.mul_apply, abs_mul, abs_div, abs_one]

/-- Cochrane (2023), p. 523: `E_t |w_{t,k}| = ∑_j ((|Φ|⁻¹P)^k)_{S_t j}/|φ_j|`. -/
theorem E_abs_wt (R : MarkovRegimeN 𝔼 T) (hA : RegimeAdapted 𝔼 R.S) (hP : 𝔼.PullOut)
    {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0) : ∀ k t, 𝔼.E t (fun ω => |wt R.S φ t k ω|) =
      fun ω => ∑ j, (absM T φ ^ k) (R.S t ω) j * (1 / |φ j|) := by
  intro k
  induction k with
  | zero =>
    intro t
    have h := hA t (fun l => |1 / φ l|)
    change 𝔼.E t (fun ω => |1 / φ (R.S t ω)|) = fun ω => |1 / φ (R.S t ω)| at h
    change 𝔼.E t (fun ω => |1 / φ (R.S t ω)|) = _
    rw [h]
    funext ω
    simp [Matrix.one_apply]
  | succ k ih =>
    intro t
    set g : Fin N → ℝ := fun l => ∑ j, (absM T φ ^ k) l j * (1 / |φ j|) with hg
    have ha : 𝔼.E t (fun ω => 1 / |φ (R.S t ω)|) = fun ω => 1 / |φ (R.S t ω)| :=
      hA t (fun l => 1 / |φ l|)
    rw [abs_wt_succ, hP _ _ _ ha, ← 𝔼.tower (Nat.le_succ t), ih (t + 1)]
    have hm : 𝔼.E t (fun ω => ∑ j, (absM T φ ^ k) (R.S (t + 1) ω) j * (1 / |φ j|)) =
        fun ω => ∑ l, T.P (R.S t ω) l * g l := R.markov t g
    rw [hm]
    funext ω
    simp only [Pi.mul_apply]
    have hs := sum_pow_succ (absM T φ) k (R.S t ω) (fun j => 1 / |φ j|)
    have h0 : |φ (R.S t ω)| ≠ 0 := abs_ne_zero.2 (hφ _)
    rw [hs, row_absM T (hφ _) g, ← mul_assoc, one_div_mul_cancel h0, one_mul]

/-- Cochrane (2023), p. 523: `|E_t(w_{t,k} u_{t+k})| ≤ U ∑_j ((|Φ|⁻¹P)^k)_{S_t j}/|φ_j|` when
`|u| ≤ U`.
Abstract form of `MarkovRegimesGeneral.fwdTerm_bound`. -/
theorem fterm_bound (R : MarkovRegimeN 𝔼 T) (hA : RegimeAdapted 𝔼 R.S) (hP : 𝔼.PullOut)
    {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0) {u : ℕ → Ω → ℝ} {U : ℝ} (hU : ∀ t ω, |u t ω| ≤ U)
    (t k : ℕ) (ω : Ω) :
    |fterm 𝔼 R.S φ u t k ω| ≤ U * ∑ j, (absM T φ ^ k) (R.S t ω) j * (1 / |φ j|) := by
  set a : Ω → ℝ := fun ω => |wt R.S φ t k ω| with ha
  have hup : wt R.S φ t k * u (t + k) ≤ U • a := fun ω' => by
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, ha]
    calc wt R.S φ t k ω' * u (t + k) ω' ≤ |wt R.S φ t k ω' * u (t + k) ω'| := le_abs_self _
      _ = |wt R.S φ t k ω'| * |u (t + k) ω'| := abs_mul _ _
      _ ≤ |wt R.S φ t k ω'| * U := mul_le_mul_of_nonneg_left (hU _ _) (abs_nonneg _)
      _ = U * |wt R.S φ t k ω'| := mul_comm _ _
  have hlo : -(U • a) ≤ wt R.S φ t k * u (t + k) := fun ω' => by
    simp only [Pi.mul_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, ha]
    have h1 : |wt R.S φ t k ω' * u (t + k) ω'| ≤ U * |wt R.S φ t k ω'| := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hU _ _) (abs_nonneg _)
    linarith [neg_abs_le (wt R.S φ t k ω' * u (t + k) ω')]
  have h1 := 𝔼.mono t hup ω
  have h2 := 𝔼.mono t hlo ω
  rw [map_neg, map_smul, ha, E_abs_wt R hA hP hφ k t] at h2
  rw [map_smul, ha, E_abs_wt R hA hP hφ k t] at h1
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  exact abs_le.2 ⟨h2, h1⟩

/-- Cochrane (2023), p. 523: `∑_j ((|Φ|⁻¹P)^k)_{ij}/|φ_j| ≤ bnd k`. -/
theorem row_le_bnd (T : TransitionN N) (φ : Fin N → ℝ) (k : ℕ) (i : Fin N) :
    ∑ j, (absM T φ ^ k) i j * (1 / |φ j|) ≤ bnd T φ k := by
  have hnn : ∀ j, 0 ≤ 1 / |φ j| := fun j => one_div_nonneg.2 (abs_nonneg _)
  calc ∑ j, (absM T φ ^ k) i j * (1 / |φ j|) ≤ ∑ j, |(absM T φ ^ k) i j| * (1 / |φ j|) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (le_abs_self _) (hnn j)
    _ ≤ bnd T φ k := by
        unfold bnd
        exact Finset.single_le_sum (f := fun i => ∑ j, |(absM T φ ^ k) i j| * (1 / |φ j|))
          (fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hnn j))
          (Finset.mem_univ i)

/-- Cochrane (2023), p. 523: under the condition the bound is summable.
As `MarkovRegimesGeneralMeasure.summable_const` and `MarkovRegimesGeneral.summable_bound`. -/
theorem bnd_summable {φ : Fin N → ℝ} (hc : GenCondition T φ) : Summable (bnd T φ) := by
  unfold bnd
  exact summable_sum fun i _ => summable_sum fun j _ =>
    (summable_abs_pow_entry hc.2 i j).mul_right _

/-- Cochrane (2023), p. 523: the terms of the forward solution are dominated by `U · bnd k`. -/
theorem fterm_le (R : MarkovRegimeN 𝔼 T) (hA : RegimeAdapted 𝔼 R.S) (hP : 𝔼.PullOut)
    {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0) {u : ℕ → Ω → ℝ} {U : ℝ} (hU : ∀ t ω, |u t ω| ≤ U)
    (t k : ℕ) (ω : Ω) : |fterm 𝔼 R.S φ u t k ω| ≤ U * bnd T φ k := by
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU t ω)
  exact (fterm_bound R hA hP hφ hU t k ω).trans
    (mul_le_mul_of_nonneg_left (row_le_bnd T φ k _) hU0)

/-- Cochrane (2023), p. 523: the first term, `E_t(u_t/φ_{S_t}) = u_t/φ_{S_t}` for adapted `u`. -/
theorem fterm_zero (hP : 𝔼.PullOut) {S : ℕ → Ω → Fin N} (hA : RegimeAdapted 𝔼 S)
    (φ : Fin N → ℝ) {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) (t : ℕ) :
    fterm 𝔼 S φ u t 0 = fun ω => 1 / φ (S t ω) * u t ω := by
  have ha : 𝔼.E t (fun ω => 1 / φ (S t ω)) = fun ω => 1 / φ (S t ω) := hA t (fun l => 1 / φ l)
  unfold fterm
  change 𝔼.E t ((fun ω => 1 / φ (S t ω)) * u t) = _
  rw [hP _ _ _ ha, hu t]
  rfl

/-- Cochrane (2023), p. 523: the recursion of the terms,
`E_t(w_{t,k+1} u_{t+k+1}) = (1/φ_{S_t}) E_t E_{t+1}(w_{t+1,k} u_{t+1+k})`. -/
theorem fterm_succ (hP : 𝔼.PullOut) {S : ℕ → Ω → Fin N} (hA : RegimeAdapted 𝔼 S)
    (φ : Fin N → ℝ) (u : ℕ → Ω → ℝ) (t k : ℕ) :
    fterm 𝔼 S φ u t (k + 1) = (fun ω => 1 / φ (S t ω)) * 𝔼.E t (fterm 𝔼 S φ u (t + 1) k) := by
  have ha : 𝔼.E t (fun ω => 1 / φ (S t ω)) = fun ω => 1 / φ (S t ω) := hA t (fun l => 1 / φ l)
  have hfun : wt S φ t (k + 1) * u (t + (k + 1)) =
      (fun ω => 1 / φ (S t ω)) * (wt S φ (t + 1) k * u (t + 1 + k)) := by
    funext ω
    simp only [wt, Pi.mul_apply, show t + (k + 1) = t + 1 + k by omega]
    ring
  unfold fterm
  rw [hfun, hP _ _ _ ha, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), p. 523: the forward-solution terms are summable at every state. -/
theorem fterm_summable (R : MarkovRegimeN 𝔼 T) (hA : RegimeAdapted 𝔼 R.S) (hP : 𝔼.PullOut)
    {φ : Fin N → ℝ} (hc : GenCondition T φ) {u : ℕ → Ω → ℝ} {U : ℝ}
    (hU : ∀ t ω, |u t ω| ≤ U) (t : ℕ) (ω : Ω) : Summable (fun k => fterm 𝔼 R.S φ u t k ω) :=
  Summable.of_norm_bounded ((bnd_summable hc).mul_left U) fun k => by
    rw [Real.norm_eq_abs]
    exact fterm_le R hA hP hc.1 hU t k ω

/-- Cochrane (2023), pp. 522–523 (**existence for any bounded adapted disturbance**): under the
condition, `π_t = −∑_k E_t(w_{t,k} u_{t+k})` solves `E_t π_{t+1} = φ_{S_t} π_t + u_t`.
Abstract form of `MarkovRegimesGeneral.fwdSol_solves`. -/
theorem fwdP_solves (R : MarkovRegimeN 𝔼 T) (hA : RegimeAdapted 𝔼 R.S) (hP : 𝔼.PullOut)
    {φ : Fin N → ℝ} (hc : GenCondition T φ) {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) {U : ℝ}
    (hU : ∀ t ω, |u t ω| ≤ U) : Sol 𝔼 R.S φ u (fwdP 𝔼 R.S φ u) := by
  intro t
  funext ω
  have hneg : fwdP 𝔼 R.S φ u (t + 1) = -fun ω' => ∑' k, fterm 𝔼 R.S φ u (t + 1) k ω' := rfl
  rw [hneg, map_neg, Pi.neg_apply,
    ForwardSolution.E_tsum_dom 𝔼 ((bnd_summable hc).mul_left U)
      (fun k ω' => fterm_le R hA hP hc.1 hU (t + 1) k ω') t ω]
  have hφ := hc.1 (R.S t ω)
  have hk : ∀ k, 𝔼.E t (fterm 𝔼 R.S φ u (t + 1) k) ω =
      φ (R.S t ω) * fterm 𝔼 R.S φ u t (k + 1) ω := fun k => by
    rw [fterm_succ hP hA φ u t k, Pi.mul_apply]
    field_simp
  simp only [hk]
  rw [tsum_mul_left]
  have hs := fterm_summable R hA hP hc hU t ω
  change -(φ (R.S t ω) * ∑' k, fterm 𝔼 R.S φ u t (k + 1) ω) =
    φ (R.S t ω) * -∑' k, fterm 𝔼 R.S φ u t k ω + u t ω
  rw [hs.tsum_eq_zero_add, fterm_zero hP hA φ hu t]
  field_simp
  ring

/-- Cochrane (2023), pp. 522–523: under the condition the forward solution is bounded by
`U ∑_k bnd k`.
Abstract form of `MarkovRegimesGeneral.fwdSol_bounded`. -/
theorem fwdP_bounded (R : MarkovRegimeN 𝔼 T) (hA : RegimeAdapted 𝔼 R.S) (hP : 𝔼.PullOut)
    {φ : Fin N → ℝ} (hc : GenCondition T φ) {u : ℕ → Ω → ℝ} {U : ℝ}
    (hU : ∀ t ω, |u t ω| ≤ U) : BoundedProc (fwdP 𝔼 R.S φ u) := by
  refine ⟨∑' k, U * bnd T φ k, fun t ω => ?_⟩
  change |-∑' k, fterm 𝔼 R.S φ u t k ω| ≤ _
  rw [abs_neg, ← Real.norm_eq_abs]
  exact tsum_of_norm_bounded ((bnd_summable hc).mul_left U).hasSum fun k => by
    rw [Real.norm_eq_abs]
    exact fterm_le R hA hP hc.1 hU t k ω

/-- Cochrane (2023), pp. 522–523: the forward solution is adapted.
Abstract form of `MarkovRegimesGeneralMeasure.fwdSolM_adapted`. -/
theorem fwdP_adapted (R : MarkovRegimeN 𝔼 T) (hA : RegimeAdapted 𝔼 R.S) (hP : 𝔼.PullOut)
    {φ : Fin N → ℝ} (hc : GenCondition T φ) {u : ℕ → Ω → ℝ} {U : ℝ}
    (hU : ∀ t ω, |u t ω| ≤ U) : 𝔼.Adapted (fwdP 𝔼 R.S φ u) := by
  intro t
  funext ω
  have hneg : fwdP 𝔼 R.S φ u t = -fun ω' => ∑' k, fterm 𝔼 R.S φ u t k ω' := rfl
  rw [hneg, map_neg, Pi.neg_apply, Pi.neg_apply,
    ForwardSolution.E_tsum_dom 𝔼 ((bnd_summable hc).mul_left U)
      (fun k ω' => fterm_le R hA hP hc.1 hU t k ω') t ω]
  simp only [fterm, 𝔼.E_E_self]

/-! ### Non-uniqueness: the sign-twisted sunspot -/

/-- Cochrane (2023), p. 523: the sign of the regime history, `s_t = ∏_{τ<t} sgn φ_{S_τ}`.
Abstract form of `MarkovRegimesGeneralMeasure.sgnProc` and `MarkovRegimesGeneral.histSign`. -/
noncomputable def sgnP (S : ℕ → Ω → Fin N) (φ : Fin N → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => histSign φ (pastOf S t ω)

/-- Cochrane (2023), p. 523: `s_{t+1} = sgn φ_{S_t} · s_t`.
Abstract form of `MarkovRegimesGeneralMeasure.sgnProc_succ_sm`. -/
theorem sgnP_succ (S : ℕ → Ω → Fin N) (φ : Fin N → ℝ) (t : ℕ) :
    sgnP S φ (t + 1) = (fun ω => sgn (φ (S t ω))) * sgnP S φ t := by
  funext ω
  simp only [sgnP, pastOf, histSign_cons, Pi.mul_apply]

/-- Cochrane (2023), p. 523: with pull-out and a known regime, `s_t` is known at date `t`.
Abstract form of `MarkovRegimesGeneralMeasure.sgnProc_sm`. -/
theorem sgnP_adapted (hP : 𝔼.PullOut) {S : ℕ → Ω → Fin N} (hA : RegimeAdapted 𝔼 S)
    (φ : Fin N → ℝ) : ∀ t, 𝔼.E t (sgnP S φ t) = sgnP S φ t := by
  intro t
  induction t with
  | zero =>
    have h0 : sgnP S φ 0 = fun _ => 1 := by
      funext ω
      simp [sgnP, pastOf, histSign]
    rw [h0, 𝔼.const]
  | succ t ih =>
    have ha : 𝔼.E (t + 1) (fun ω => sgn (φ (S t ω))) = fun ω => sgn (φ (S t ω)) :=
      adapted_later hA (Nat.le_succ t) (fun l => sgn (φ l))
    rw [sgnP_succ, hP _ _ _ ha, ← ih, 𝔼.known (Nat.le_succ t)]

/-- Cochrane (2023), p. 523: with pull-out and a known regime, `s_{t+1}` is known at date `t`. -/
theorem sgnP_succ_adapted (hP : 𝔼.PullOut) {S : ℕ → Ω → Fin N} (hA : RegimeAdapted 𝔼 S)
    (φ : Fin N → ℝ) (t : ℕ) : 𝔼.E t (sgnP S φ (t + 1)) = sgnP S φ (t + 1) := by
  have ha : 𝔼.E t (fun ω => sgn (φ (S t ω))) = fun ω => sgn (φ (S t ω)) :=
    hA t (fun l => sgn (φ l))
  rw [sgnP_succ, hP _ _ _ ha, sgnP_adapted hP hA φ t]

/-- Cochrane (2023), pp. 522–523 (**the sign-twisted sunspot with pull-out**): if every
`φ_i ≠ 0` and the spectral radius of `|Φ|⁻¹P` is not `< 1`, then `π_t = s_t x_t(S_t)` with
`x_t = |Φ|⁻¹P x_{t+1}` is a nonzero bounded solution of the homogeneous model.
Pull-out form of `MarkovRegimesGeneralMeasure.twisted_solves` and
`TidyR6MarkovAbstractN.hist_twisted`. -/
theorem pullOut_twisted (R : MarkovRegimeN 𝔼 T) (hA : RegimeAdapted 𝔼 R.S) (hP : 𝔼.PullOut)
    {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0) (h : ¬ specRad (absM T φ) < 1)
    (hS0 : ∀ i, ∃ ω, R.S 0 ω = i) : ∃ e, Homog 𝔼 R.S φ e ∧ BoundedProc e ∧ e ≠ 0 := by
  obtain ⟨x, hx, ⟨B, hB⟩, i₀, hi₀⟩ := exists_bdd_backward h
  refine ⟨fun t => sgnP R.S φ t * (x t ∘ R.S t), fun t => ?_, ⟨B, fun t ω => ?_⟩, ?_⟩
  · change 𝔼.E t (sgnP R.S φ (t + 1) * (x (t + 1) ∘ R.S (t + 1))) = _
    rw [hP _ _ _ (sgnP_succ_adapted hP hA φ t), R.markov t (x (t + 1)), sgnP_succ]
    funext ω
    have hrow : ∑ j, T.P (R.S t ω) j * x (t + 1) j = |φ (R.S t ω)| * x t (R.S t ω) := by
      rw [row_absM T (hφ _), hx t]
      rfl
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [hrow]
    linear_combination (sgnP R.S φ t ω * x t (R.S t ω)) * sgn_mul_abs (φ (R.S t ω))
  · change |sgnP R.S φ t ω * x t (R.S t ω)| ≤ B
    rw [abs_mul, sgnP, abs_histSign, one_mul]
    exact hB _ _
  · intro h0
    obtain ⟨ω, hω⟩ := hS0 i₀
    have := congrFun (congrFun h0 0) ω
    change histSign φ [] * x 0 (R.S 0 ω) = 0 at this
    simp only [histSign, List.map_nil, List.prod_nil, one_mul, hω] at this
    exact hi₀ this

/-- Cochrane (2023), pp. 522–523: determinacy with pull-out — for every bounded adapted
disturbance there is exactly one bounded solution of `E_t π_{t+1} = φ_{S_t} π_t + u_t`. -/
def PDeterminate (𝔼 : ExpectationSystem Ω) (S : ℕ → Ω → Fin N) (φ : Fin N → ℝ) : Prop :=
  ∀ u : ℕ → Ω → ℝ, 𝔼.Adapted u → BoundedProc u → ∃! π, Sol 𝔼 S φ u π ∧ BoundedProc π

/-- Cochrane (2023), pp. 522–523 (**Davig–Leeper for `N` regimes and any signs, for arbitrary
bounded adapted disturbances**): in an expectation system with the pull-out property and a known
Markov regime, all regimes possible at date `0`, the model has exactly one bounded equilibrium for
every bounded adapted disturbance iff every `φ_i ≠ 0` and the spectral radius of `|Φ|⁻¹P` is
`< 1`. The equilibrium is the adapted forward solution `fwdP`. With non-degenerate transitions
these hypotheses have no countable or pointwise-linear model
(`TidyR6MarkovNoGo.countable_no_regime`): the theorem is substantive only for degenerate chains
(`TidyR6MarkovInstances`), and the non-degenerate versions are
`MarkovRegimesGeneral.determinate_iff` and `MarkovRegimesGeneralMeasure.meas_determinate_iff`. -/
theorem pullOut_determinate_iff (R : MarkovRegimeN 𝔼 T) (hA : RegimeAdapted 𝔼 R.S)
    (hP : 𝔼.PullOut) (φ : Fin N → ℝ) (hS0 : ∀ i, ∃ ω, R.S 0 ω = i) :
    PDeterminate 𝔼 R.S φ ↔ GenCondition T φ := by
  constructor
  · intro hd
    by_contra hc
    obtain ⟨e, he, hb, hne⟩ : ∃ e, Homog 𝔼 R.S φ e ∧ BoundedProc e ∧ e ≠ 0 := by
      by_cases h0 : ∀ i, φ i ≠ 0
      · exact pullOut_twisted R hA hP h0 (fun hs => hc ⟨h0, hs⟩) hS0
      · push Not at h0
        obtain ⟨i, hi⟩ := h0
        exact absN_zero_coeff_homog R hi (hS0 i)
    have hz : ∀ x : ℕ → Ω → ℝ, Homog 𝔼 R.S φ x → Sol 𝔼 R.S φ 0 x := by
      intro x hx t
      rw [hx t]
      funext ω
      simp
    obtain ⟨π, _, huniq⟩ := hd 0 (fun t => by simp) ⟨0, fun t ω => by simp⟩
    have h0 : (0 : ℕ → Ω → ℝ) = π := huniq 0 ⟨hz 0 (fun t => by
      funext ω
      simp), ⟨0, fun t ω => by simp⟩⟩
    exact hne ((huniq e ⟨hz e he, hb⟩).trans h0.symm)
  · intro hc u hu ⟨U, hU⟩
    refine ⟨fwdP 𝔼 R.S φ u, ⟨fwdP_solves R hA hP hc hu hU, fwdP_bounded R hA hP hc hU⟩, ?_⟩
    rintro π ⟨hπ, hπb⟩
    exact absN_unique R hc hπ (fwdP_solves R hA hP hc hu hU) hπb (fwdP_bounded R hA hP hc hU)

end Cochrane.ObservationalEquivalence.TidyR6MarkovPullOut
