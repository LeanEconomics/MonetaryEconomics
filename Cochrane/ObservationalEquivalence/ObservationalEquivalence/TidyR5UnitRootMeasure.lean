/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.TidyR5UnitRoot
import ObservationalEquivalence.SurplusRegressionL2
import ObservationalEquivalence.ExpectationsMeasureIIDZ
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# The monetary equation at `|φ| = 1` under genuine uncertainty

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.7, pp. 508–509
(region (d) and the boundary `|φ| = 1`), and Chapter 23, eqs. (23.1)–(23.2), p. 512.

`TidyR5UnitRoot` characterises when `E_t π_{t+1} = φπ_t + u_{i,t}` (`φ² = 1`) has a bounded
adapted solution in expectation systems in which information eventually stops arriving. Here the
characterisation is proved on any probability space with any filtration (`MeasExpectationSystem`,
Mathlib's `condExp`, equations a.e., bounded meaning essentially bounded), where infinitely many
genuine shocks can arrive.

## Main results

* `exists_mem_iInter_of_antitone`: in a real Hilbert space a decreasing sequence of nonempty
  closed convex sets with bounded minimal norms has a common point (minimal-norm points form a
  Cauchy sequence). This replaces a weak-compactness argument.
* `iterate_solM`, `condBddM_of_sol` (**necessity**): a bounded solution forces the conditional sums
  `∑_{j<T} φʲ E_t u_{t+j}` to be essentially bounded, uniformly in `t` and `T`.
* `finSolM`: the solution pinned at `π_N = 0`, `finSolM_solves`, `finSolM_bound`.
* `sol_of_condBddM` (**sufficiency**): if the conditional sums are bounded, the pinned solutions
  for `N = 0, 1, 2, …` are embedded in the Hilbert space `ℓ²(ℕ; L²(P))` with weights `2^{−t}`, and a
  common point of the closed convex sets they generate is a bounded adapted solution.
* `exists_iff_condBddM` (**the characterisation**): at `φ² = 1` a bounded adapted solution exists
  iff the conditional sums are essentially bounded; `exists_iff_phi_one_M`
  (`|E_t ∑_{j<T} u_{t+j}| ≤ C`) and `exists_iff_phi_neg_one_M`
  (`|E_t ∑_{j<T} (−1)ʲ u_{t+j}| ≤ C`).
* `coin_realised_not_necessary`: with genuinely infinite uncertainty the realised sums need not be
  bounded — in the i.i.d. coin economy `u_{i,t} = φᵗ ε_t` has the bounded solution
  `π_t = −φ^{t+1} ε_t`, while the realised sums `∑_{s<t} φˢ u_s = ∑_{s<t} ε_s` (a random walk) are
  not essentially bounded. So the realised-sum criterion of `TidyR5UnitRoot.exists_iff_known` is
  sufficient but not necessary in general.
-/

namespace Cochrane.ObservationalEquivalence.TidyR5UnitRootMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationsMeasure

/-! ### Nested closed convex sets in a Hilbert space -/

/-- Cochrane (2023), §22.7, p. 508 (tool for the existence proof): in a real Hilbert space, a
decreasing sequence of nonempty closed convex sets each containing a point of norm at most `R`
has a common point. The minimal-norm points `x_n` satisfy
`‖x_n‖² + ‖x_m − x_n‖² ≤ ‖x_m‖²` for `m ≥ n`, so they form a Cauchy sequence. -/
theorem exists_mem_iInter_of_antitone {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {K : ℕ → Set F} (hanti : Antitone K) (hne : ∀ n, (K n).Nonempty)
    (hcl : ∀ n, IsClosed (K n)) (hcv : ∀ n, Convex ℝ (K n)) {R : ℝ}
    (hR : ∀ n, ∃ y ∈ K n, ‖y‖ ≤ R) : ∃ z, ∀ n, z ∈ K n := by
  have hmin : ∀ n, ∃ v ∈ K n, ∀ w ∈ K n, ‖v‖ ^ 2 + ‖w - v‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    intro n
    obtain ⟨v, hv, hvmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex (hne n) (hcl n).isComplete (hcv n) 0
    have hvar := (norm_eq_iInf_iff_real_inner_le_zero (hcv n) hv).1 hvmin
    refine ⟨v, hv, fun w hw => ?_⟩
    have h := hvar w hw
    have e : ‖w‖ ^ 2 = ‖v‖ ^ 2 + 2 * inner ℝ v (w - v) + ‖w - v‖ ^ 2 := by
      have hw' : w = v + (w - v) := by abel
      conv_lhs => rw [hw']
      rw [norm_add_sq_real]
    rw [zero_sub, inner_neg_left] at h
    linarith
  choose x hxK hxmin using hmin
  have hmono : ∀ n m, n ≤ m → ‖x n‖ ^ 2 + ‖x m - x n‖ ^ 2 ≤ ‖x m‖ ^ 2 :=
    fun n m hnm => hxmin n (x m) (hanti hnm (hxK m))
  have hbdd : ∀ n, ‖x n‖ ^ 2 ≤ R ^ 2 := fun n => by
    obtain ⟨y, hy, hyR⟩ := hR n
    have h1 := hxmin n y hy
    have h2 : ‖y‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyR 2
    nlinarith [sq_nonneg ‖y - x n‖]
  set a : ℕ → ℝ := fun n => ‖x n‖ ^ 2 with ha
  have ha_mono : Monotone a := monotone_nat_of_le_succ fun n => by
    have := hmono n (n + 1) (Nat.le_succ n)
    simp only [ha]
    nlinarith [sq_nonneg ‖x (n + 1) - x n‖]
  have ha_bdd : BddAbove (Set.range a) := ⟨R ^ 2, by rintro _ ⟨n, rfl⟩; exact hbdd n⟩
  have hlim := tendsto_atTop_ciSup ha_mono ha_bdd
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff']
    intro e he
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (hlim.eventually (Ioi_mem_nhds (by nlinarith : (⨆ n, a n) - e ^ 2 < ⨆ n, a n)))
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hmono N n hn
    have h2 : a n ≤ ⨆ n, a n := le_ciSup ha_bdd n
    have h3 := hN N le_rfl
    rw [dist_eq_norm]
    refine lt_of_pow_lt_pow_left₀ 2 he.le ?_
    simp only [ha] at h1 h2 h3
    linarith
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨z, fun n => (hcl n).mem_of_tendsto hz
    (eventually_atTop.2 ⟨n, fun m hm => hanti hm (hxK m)⟩)⟩

/-! ### The monetary equation on a probability space -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), (23.1)–(23.2), p. 512, on a probability space: `π` solves
`E_t π_{t+1} = φπ_t + u_{i,t}` almost surely at every date. -/
def MonEqM (φ : ℝ) (u π : ℕ → Ω → ℝ) : Prop := ∀ t, S.E t (π (t + 1)) =ᵐ[S.μ] φ • π t + u t

/-- Cochrane (2023), §22.7, p. 508, on a probability space: the monetary equation has an adapted,
essentially bounded solution. -/
def HasBddSolM (φ : ℝ) (u : ℕ → Ω → ℝ) : Prop :=
  ∃ π, StronglyAdapted S.𝓕 π ∧ S.BddProc π ∧ MonEqM S φ u π

/-- Cochrane (2023), §22.7, p. 508: the conditional sums `∑_{j<T} φʲ E_t u_{t+j}`. -/
noncomputable def condSumM (φ : ℝ) (u : ℕ → Ω → ℝ) (t T : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range T, φ ^ j • S.E t (u (t + j))

/-- Cochrane (2023), §22.7, p. 508: the conditional sums are essentially bounded, uniformly in
the date and the horizon. -/
def CondBddM (φ : ℝ) (u : ℕ → Ω → ℝ) : Prop :=
  ∃ C, ∀ t T, ∀ᵐ ω ∂S.μ, |condSumM S φ u t T ω| ≤ C

variable {S}

/-- Cochrane (2023), (23.2), p. 512, iterated on a probability space: if `π_t` is integrable at
every date, `E_t π_t = π_t` a.e. and `π` solves the monetary equation, then with `φ² = 1`,
`φᵀ E_t π_{t+T} = π_t + φ ∑_{j<T} φʲ E_t u_{t+j}` a.e. -/
theorem iterate_solM {φ : ℝ} (hφ : φ ^ 2 = 1) {u π : ℕ → Ω → ℝ}
    (hui : ∀ t, Integrable (u t) S.μ) (hπi : ∀ t, Integrable (π t) S.μ) (hπ : MonEqM S φ u π)
    {t : ℕ} (hπt : S.E t (π t) =ᵐ[S.μ] π t) (T : ℕ) :
    φ ^ T • S.E t (π (t + T)) =ᵐ[S.μ] π t + φ • condSumM S φ u t T := by
  induction T with
  | zero =>
    filter_upwards [hπt] with ω h
    simp [condSumM, h]
  | succ T ih =>
    have h1 : S.E t (π (t + (T + 1))) =ᵐ[S.μ] S.E t (S.E (t + T) (π (t + T + 1))) := by
      rw [show t + (T + 1) = t + T + 1 by omega]
      exact (S.E_tower (Nat.le_add_right t T) _).symm
    have h2 := S.E_congr (hπ (t + T)) t
    have h3 := S.E_add ((hπi (t + T)).smul φ) (hui (t + T)) t
    have h4 := S.E_smul φ (π (t + T)) t
    filter_upwards [ih, h1, h2, h3, h4] with ω e0 e1 e2 e3 e4
    simp only [condSumM, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      Finset.sum_range_succ] at e0 e1 e2 e3 e4 ⊢
    rw [e1, e2, e3, e4]
    have hφ2 : φ * φ = 1 := by rw [← sq]; exact hφ
    rw [pow_succ]
    linear_combination e0 + (φ ^ T * S.E t (π (t + T)) ω) * hφ2

/-- Cochrane (2023), §22.7, p. 508 (**necessity** on a probability space): a bounded adapted
solution at `φ² = 1` forces the conditional sums to be essentially bounded (by twice the bound
of the solution). -/
theorem condBddM_of_sol {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ}
    (hui : ∀ t, Integrable (u t) S.μ) (h : HasBddSolM S φ u) : CondBddM S φ u := by
  obtain ⟨π, hπa, ⟨M, hM⟩, hπ⟩ := h
  have hπi : ∀ t, Integrable (π t) S.μ := fun t =>
    MeasExpectationSystem.BddRV.integrable ⟨((hπa t).mono (S.𝓕.le t)).aestronglyMeasurable,
      M, hM t⟩
  refine ⟨M + M, fun t T => ?_⟩
  have hπt : S.E t (π t) =ᵐ[S.μ] π t :=
    EventuallyEq.of_eq (S.E_of_stronglyMeasurable (hπa t) (hπi t))
  filter_upwards [iterate_solM hφ hui hπi hπ hπt T, S.abs_E_le (hM (t + T)) t, hM t]
    with ω e hE hπω
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e
  have hφ2 : φ * φ = 1 := by rw [← sq]; exact hφ
  have e2 : condSumM S φ u t T ω = φ * (φ ^ T * S.E t (π (t + T)) ω - π t ω) := by
    rw [e]
    linear_combination (-(condSumM S φ u t T ω)) * hφ2
  rw [e2, abs_mul, TidyR5UnitRoot.abs_eq_one hφ, one_mul]
  refine (abs_sub _ _).trans (add_le_add ?_ hπω)
  rw [abs_mul, TidyR5UnitRoot.abs_pow_eq_one hφ, one_mul]
  exact hE

/-! ### The accumulated disturbance and the pinned solutions -/

/-- Cochrane (2023), §22.7, p. 508: the accumulated disturbance `D_0 = 0`,
`D_{t+1} = φD_t + u_t`. -/
noncomputable def accumM (φ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => φ • accumM φ u t + u t

/-- Cochrane (2023), §22.7, p. 508: `D_t` and `D_{t+1}` are known at `t` (adapted disturbance). -/
theorem accumM_meas {φ : ℝ} {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (accumM φ u t) ∧
      StronglyMeasurable[S.𝓕 t] (accumM φ u (t + 1)) := by
  induction t with
  | zero =>
    refine ⟨stronglyMeasurable_const, ?_⟩
    change StronglyMeasurable[S.𝓕 0] (φ • (0 : Ω → ℝ) + u 0)
    rw [smul_zero, zero_add]
    exact hua 0
  | succ t ih =>
    have h1 : StronglyMeasurable[S.𝓕 (t + 1)] (accumM φ u (t + 1)) :=
      ih.2.mono (S.𝓕.mono (Nat.le_succ t))
    refine ⟨h1, ?_⟩
    change StronglyMeasurable[S.𝓕 (t + 1)] (φ • accumM φ u (t + 1) + u (t + 1))
    exact (h1.const_smul φ).add (hua (t + 1))

/-- Cochrane (2023), §22.7, p. 508: `D_t` is integrable. -/
theorem accumM_integrable {φ : ℝ} {u : ℕ → Ω → ℝ} (hui : ∀ t, Integrable (u t) S.μ) (t : ℕ) :
    Integrable (accumM φ u t) S.μ := by
  induction t with
  | zero => exact integrable_zero _ _ _
  | succ t ih => exact (ih.smul φ).add (hui t)

/-- Cochrane (2023), §22.7, p. 508: `D` solves the monetary equation (exactly, hence a.e.). -/
theorem accumM_solves {φ : ℝ} {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u)
    (hui : ∀ t, Integrable (u t) S.μ) : MonEqM S φ u (accumM φ u) := fun t =>
  EventuallyEq.of_eq (S.E_of_stronglyMeasurable (accumM_meas hua t).2
    (accumM_integrable hui (t + 1)))

/-- Cochrane (2023), §22.7, p. 508: the solution pinned at `π_N = 0`,
`π^{(N)}_t = D_t − φ^{t+N} E_t D_N`. -/
noncomputable def finSolM (S : MeasExpectationSystem Ω) (φ : ℝ) (u : ℕ → Ω → ℝ) (N t : ℕ) :
    Ω → ℝ :=
  accumM φ u t - φ ^ (t + N) • S.E t (accumM φ u N)

/-- Cochrane (2023), §22.7, p. 508: the pinned path is known at `t`. -/
theorem finSolM_meas {φ : ℝ} {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) (N t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (finSolM S φ u N t) :=
  (accumM_meas hua t).1.sub ((S.stronglyMeasurable_E t _).const_smul _)

/-- Cochrane (2023), §22.7, p. 508: the pinned path is integrable. -/
theorem finSolM_integrable {φ : ℝ} {u : ℕ → Ω → ℝ} (hui : ∀ t, Integrable (u t) S.μ)
    (N t : ℕ) : Integrable (finSolM S φ u N t) S.μ :=
  (accumM_integrable hui t).sub ((S.integrable_E t _).smul _)

/-- Cochrane (2023), §22.7, p. 508: the pinned path solves the monetary equation at every date. -/
theorem finSolM_solves {φ : ℝ} {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u)
    (hui : ∀ t, Integrable (u t) S.μ) (N : ℕ) : MonEqM S φ u (finSolM S φ u N) := fun t => by
  have h1 := S.E_sub (accumM_integrable (φ := φ) hui (t + 1))
    ((S.integrable_E (t + 1) (accumM φ u N)).smul (φ ^ (t + 1 + N))) t
  have h2 := S.E_smul (φ ^ (t + 1 + N)) (S.E (t + 1) (accumM φ u N)) t
  have h3 := S.E_tower (Nat.le_succ t) (accumM φ u N)
  have h4 := accumM_solves (φ := φ) hua hui t
  filter_upwards [h1, h2, h3, h4] with ω e1 e2 e3 e4
  simp only [finSolM, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e1 e2 e3 e4 ⊢
  rw [e1, e4, e2, e3, show t + 1 + N = t + N + 1 by omega, pow_succ]
  ring

/-- Cochrane (2023), §22.7, p. 508: before the pinning date the pinned path is a conditional sum,
`π^{(t+T)}_t = −φ ∑_{j<T} φʲ E_t u_{t+j}` a.e. -/
theorem finSolM_eq {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u)
    (hui : ∀ t, Integrable (u t) S.μ) (t T : ℕ) :
    finSolM S φ u (t + T) t =ᵐ[S.μ] -(φ • condSumM S φ u t T) := by
  have hD := iterate_solM hφ hui (accumM_integrable hui) (accumM_solves (φ := φ) hua hui)
    (EventuallyEq.of_eq (S.E_of_stronglyMeasurable (accumM_meas hua t).1
      (accumM_integrable hui t))) T
  filter_upwards [hD] with ω e
  simp only [finSolM, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
    at e ⊢
  rw [show t + (t + T) = 2 * t + T by ring, pow_add, TidyR5UnitRoot.pow_two_mul hφ, one_mul, e]
  ring

/-- Cochrane (2023), §22.7, p. 508: with conditional sums bounded by `C`, the pinned path is
bounded by `C` up to its pinning date. -/
theorem finSolM_bound {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u)
    (hui : ∀ t, Integrable (u t) S.μ) {C : ℝ} (hC : ∀ t T, ∀ᵐ ω ∂S.μ, |condSumM S φ u t T ω| ≤ C)
    {N t : ℕ} (htN : t ≤ N) : ∀ᵐ ω ∂S.μ, |finSolM S φ u N t ω| ≤ C := by
  obtain ⟨T, rfl⟩ := Nat.exists_eq_add_of_le htN
  filter_upwards [finSolM_eq hφ hua hui t T, hC t T] with ω e hc
  rw [e, Pi.neg_apply, abs_neg, Pi.smul_apply, smul_eq_mul, abs_mul,
    TidyR5UnitRoot.abs_eq_one hφ, one_mul]
  exact hc

/-- Cochrane (2023), §22.7, p. 508: the pinned path vanishes at its pinning date. -/
theorem finSolM_self {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u)
    (hui : ∀ t, Integrable (u t) S.μ) (N : ℕ) : finSolM S φ u N N = 0 := by
  simp only [finSolM]
  rw [S.E_of_stronglyMeasurable (accumM_meas hua N).1 (accumM_integrable hui N),
    show N + N = 2 * N by ring, TidyR5UnitRoot.pow_two_mul hφ, one_smul, sub_self]

/-! ### The Hilbert space of weighted processes -/

open Cochrane.ObservationalEquivalence.SurplusRegressionL2 (proj proj_ae)

/-- Cochrane (2023), §22.7, p. 508 (tool): the Hilbert space `ℓ²(ℕ; L²(P))`; a process `π` is
stored as `x_t = 2^{−t} π_t`. -/
noncomputable abbrev Hil (S : MeasExpectationSystem Ω) := lp (fun _ : ℕ => Lp ℝ 2 S.μ) 2

/-- Cochrane (2023), §22.7, p. 508 (tool): the weights `w_t = 2^{−t}`. -/
noncomputable def wt (t : ℕ) : ℝ := (1 / 2) ^ t

/-- Cochrane (2023), §22.7, p. 508 (tool): the weights are positive. -/
theorem wt_pos (t : ℕ) : 0 < wt t := by unfold wt; positivity

/-- Cochrane (2023), §22.7, p. 508 (tool): `w_{t+1} = w_t / 2`. -/
theorem wt_succ (t : ℕ) : wt (t + 1) = wt t / 2 := by unfold wt; rw [pow_succ]; ring

/-- Cochrane (2023), §22.7, p. 508 (tool): each coordinate of `ℓ²(ℕ; L²(P))` is a continuous
function of the whole sequence. -/
theorem continuous_coord (t : ℕ) : Continuous fun x : Hil S => x t :=
  (LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have := lp.norm_apply_le_norm two_ne_zero (x - y) t
    rwa [lp.coeFn_sub, Pi.sub_apply] at this).continuous

/-- Cochrane (2023), §22.7, p. 508 (tool): the `L²` variables essentially bounded by `c`. -/
def BndSet (c : ℝ) : Set (Lp ℝ 2 S.μ) := {f | ∀ᵐ ω ∂S.μ, |f ω| ≤ c}

/-- Cochrane (2023), §22.7, p. 508 (tool): an `L²` variable is essentially bounded by `c` iff
`|∫_A f| ≤ c P(A)` for every event `A`. -/
theorem mem_bndSet_iff (c : ℝ) (f : Lp ℝ 2 S.μ) :
    f ∈ BndSet c ↔ ∀ A, MeasurableSet A → |∫ ω in A, f ω ∂S.μ| ≤ c * S.μ.real A := by
  have hfi : Integrable f S.μ := (Lp.memLp f).integrable one_le_two
  constructor
  · intro hf A hA
    calc |∫ ω in A, f ω ∂S.μ| ≤ ∫ ω in A, |f ω| ∂S.μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω in A, c ∂S.μ :=
          integral_mono_ae hfi.abs.integrableOn (integrable_const c) (ae_restrict_of_ae hf)
      _ = c * S.μ.real A := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  · intro hf
    have hc : Integrable (fun _ : Ω => c) S.μ := integrable_const c
    have h1 : (fun ω => f ω) ≤ᵐ[S.μ] fun _ => c :=
      ae_le_of_forall_setIntegral_le hfi hc fun A hA _ => by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
        exact (le_abs_self _).trans (hf A hA)
    have h2 : (fun ω => -f ω) ≤ᵐ[S.μ] fun _ => c :=
      ae_le_of_forall_setIntegral_le hfi.neg hc fun A hA _ => by
        rw [setIntegral_const, smul_eq_mul, mul_comm, integral_neg]
        exact (neg_le_abs _).trans (hf A hA)
    filter_upwards [h1, h2] with ω e1 e2
    exact abs_le.2 ⟨by linarith, e1⟩

/-- Cochrane (2023), §22.7, p. 508 (tool): the essentially bounded `L²` variables form a closed
set (an intersection of closed half-spaces `|⟨1_A, f⟩| ≤ c P(A)`). -/
theorem isClosed_bndSet (c : ℝ) : IsClosed (BndSet (S := S) c) := by
  have e : BndSet (S := S) c = ⋂ A : {A : Set Ω // MeasurableSet A},
      {f | |inner ℝ (indicatorConstLp 2 A.2 (measure_ne_top S.μ A.1) (1 : ℝ)) f| ≤
        c * S.μ.real A.1} := by
    ext f
    rw [mem_bndSet_iff, Set.mem_iInter, Subtype.forall]
    refine forall_congr' fun A => forall_congr' fun hA => ?_
    rw [Set.mem_ofPred_eq, L2.inner_indicatorConstLp_one]
  rw [e]
  exact isClosed_iInter fun A =>
    isClosed_le (continuous_abs.comp (continuous_const.inner continuous_id)) continuous_const

/-- Cochrane (2023), §22.7, p. 508 (tool): the essentially bounded `L²` variables form a convex
set. -/
theorem convex_bndSet (c : ℝ) : Convex ℝ (BndSet (S := S) c) := by
  intro f hf g hg a b ha hb hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f, Lp.coeFn_smul b g]
    with ω e1 e2 e3 e4 e5
  rw [e3, Pi.add_apply, e4, e5, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  calc |a * f ω + b * g ω| ≤ a * |f ω| + b * |g ω| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * c + b * c := add_le_add (mul_le_mul_of_nonneg_left e1 ha)
        (mul_le_mul_of_nonneg_left e2 hb)
    _ = c := by rw [← add_mul, hab, one_mul]

/-- Cochrane (2023), §22.7, p. 508 (tool): the processes `x_t = 2^{−t}π_t` with
`|π_t| ≤ C`, `π_t` known at `t`, and the monetary equation at the dates `t < n`
(`E_t x_{t+1} = (φ/2) x_t + 2^{−(t+1)} u_t`). -/
def Kset (u : ℕ → Ω → ℝ) (hu : ∀ t, MemLp (u t) 2 S.μ) (φ C : ℝ) (n : ℕ) : Set (Hil S) :=
  {x | (∀ t, x t ∈ BndSet (wt t * C)) ∧ (∀ t, proj S t (x t) = x t) ∧
    ∀ t, t < n → proj S t (x (t + 1)) = (φ / 2) • x t + wt (t + 1) • (hu t).toLp (u t)}

/-- Cochrane (2023), §22.7, p. 508 (tool): the sets `Kset` decrease with `n`. -/
theorem kset_antitone {u : ℕ → Ω → ℝ} (hu : ∀ t, MemLp (u t) 2 S.μ) (φ C : ℝ) :
    Antitone (Kset (S := S) u hu φ C) := fun _ _ hmn _ hx =>
  ⟨hx.1, hx.2.1, fun t ht => hx.2.2 t (lt_of_lt_of_le ht hmn)⟩

/-- Cochrane (2023), §22.7, p. 508 (tool): `Kset` is closed. -/
theorem isClosed_kset {u : ℕ → Ω → ℝ} (hu : ∀ t, MemLp (u t) 2 S.μ) (φ C : ℝ) (n : ℕ) :
    IsClosed (Kset (S := S) u hu φ C n) := by
  have e : Kset (S := S) u hu φ C n =
      (⋂ t, (fun x : Hil S => x t) ⁻¹' BndSet (wt t * C)) ∩
      ((⋂ t, {x : Hil S | proj S t (x t) = x t}) ∩
      ⋂ t, ⋂ (_ : t < n), {x : Hil S | proj S t (x (t + 1)) =
        (φ / 2) • x t + wt (t + 1) • (hu t).toLp (u t)}) := by
    ext x
    simp only [Kset, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  rw [e]
  refine (isClosed_iInter fun t => (isClosed_bndSet _).preimage (continuous_coord t)).inter
    ((isClosed_iInter fun t => isClosed_eq ((proj S t).continuous.comp (continuous_coord t))
      (continuous_coord t)).inter (isClosed_iInter fun t => isClosed_iInter fun _ =>
        isClosed_eq ((proj S t).continuous.comp (continuous_coord (t + 1)))
          ((((continuous_coord t).const_smul (φ / 2)).add
            (continuous_const (y := wt (t + 1) • (hu t).toLp (u t)))).congr fun _ => rfl)))

/-- Cochrane (2023), §22.7, p. 508 (tool): `Kset` is convex. -/
theorem convex_kset {u : ℕ → Ω → ℝ} (hu : ∀ t, MemLp (u t) 2 S.μ) (φ C : ℝ) (n : ℕ) :
    Convex ℝ (Kset (S := S) u hu φ C n) := by
  intro x hx y hy a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  have hc : ∀ t, (a • x + (1 - a) • y) t = a • x t + (1 - a) • y t := fun t => by
    rw [lp.coeFn_add, lp.coeFn_smul, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
  refine ⟨fun t => ?_, fun t => ?_, fun t ht => ?_⟩
  · rw [hc]; exact convex_bndSet _ (hx.1 t) (hy.1 t) ha hb hab
  · rw [hc, map_add, map_smul, map_smul, hx.2.1 t, hy.2.1 t]
  · rw [hc, hc, map_add, map_smul, map_smul, hx.2.2 t ht, hy.2.2 t ht]
    module

/-- Cochrane (2023), §22.7, p. 508 (tool): an `L²` element known at `t` is fixed by `E_t`. -/
theorem proj_toLp_of_meas {t : ℕ} {f : Ω → ℝ} (hf : StronglyMeasurable[S.𝓕 t] f)
    (hm : MemLp f 2 S.μ) : proj S t (hm.toLp f) = hm.toLp f := by
  apply Lp.ext
  filter_upwards [proj_ae t (hm.toLp f), S.E_congr hm.coeFn_toLp t, hm.coeFn_toLp] with ω e1 e2 e3
  rw [e1, e2, S.E_of_stronglyMeasurable hf (hm.integrable one_le_two), e3]

/-- Cochrane (2023), §22.7, p. 508 (tool): an essentially bounded `L²` element has norm at most
its bound (probability measure). -/
theorem norm_le_of_bnd {f : Lp ℝ 2 S.μ} {c : ℝ} (hc : 0 ≤ c) (hf : f ∈ BndSet c) : ‖f‖ ≤ c := by
  have hf' : ∀ᵐ ω ∂S.μ, |f ω| ≤ c := hf
  have := Lp.norm_le_of_ae_bound hc (hf'.mono fun ω h => by rwa [Real.norm_eq_abs])
  simpa [measureUnivNNReal] using this

/-- Cochrane (2023), §22.7, p. 508 (tool): with conditional sums bounded by `C ≥ 0`, the pinned
solution `π^{(n)}`, frozen after `n`, gives a point of `Kset n` of norm at most `2C`. -/
theorem kset_point {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u)
    (hu : ∀ t, MemLp (u t) 2 S.μ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t T, ∀ᵐ ω ∂S.μ, |condSumM S φ u t T ω| ≤ C) (n : ℕ) :
    ∃ y ∈ Kset (S := S) u hu φ C n, ‖y‖ ≤ 2 * C := by
  have hui : ∀ t, Integrable (u t) S.μ := fun t => (hu t).integrable one_le_two
  set p : ℕ → Ω → ℝ := fun t => finSolM S φ u n (min t n) with hp
  have hpb : ∀ t, ∀ᵐ ω ∂S.μ, |p t ω| ≤ C := fun t =>
    finSolM_bound hφ hua hui hC (min_le_right t n)
  have hpmeas : ∀ t, StronglyMeasurable[S.𝓕 t] (p t) := fun t =>
    (finSolM_meas hua n (min t n)).mono (S.𝓕.mono (min_le_left t n))
  have hpm : ∀ t, MemLp (p t) 2 S.μ := fun t =>
    MemLp.of_bound ((hpmeas t).mono (S.𝓕.le t)).aestronglyMeasurable C
      ((hpb t).mono fun ω h => by rwa [Real.norm_eq_abs])
  set yv : ℕ → Lp ℝ 2 S.μ := fun t => wt t • (hpm t).toLp (p t) with hyv
  have hyb : ∀ t, yv t ∈ BndSet (wt t * C) := fun t => by
    filter_upwards [Lp.coeFn_smul (wt t) ((hpm t).toLp (p t)), (hpm t).coeFn_toLp, hpb t]
      with ω e1 e2 e3
    rw [e1, Pi.smul_apply, e2, smul_eq_mul, abs_mul, abs_of_pos (wt_pos t)]
    exact mul_le_mul_of_nonneg_left e3 (wt_pos t).le
  have hyn : ∀ t, ‖yv t‖ ≤ wt t * C := fun t =>
    norm_le_of_bnd (mul_nonneg (wt_pos t).le hC0) (hyb t)
  have hgeo : Summable fun t : ℕ => (wt t * C) ^ (2 : ℝ) := by
    have : (fun t : ℕ => (wt t * C) ^ (2 : ℝ)) = fun t => C ^ 2 * (1 / 4 : ℝ) ^ t := by
      funext t
      rw [Real.rpow_two, wt, mul_pow, mul_comm]
      congr 1
      rw [← pow_mul, mul_comm t 2, pow_mul]
      norm_num
    rw [this]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : ∀ t, ‖yv t‖ ^ (2 : ℝ) ≤ (wt t * C) ^ (2 : ℝ) := fun t =>
    Real.rpow_le_rpow (norm_nonneg _) (hyn t) (by norm_num)
  have hmem : Memℓp yv 2 := memℓp_gen (by
    rw [show (2 : ENNReal).toReal = 2 by norm_num]
    exact Summable.of_nonneg_of_le (fun t => by positivity) hle hgeo)
  refine ⟨⟨yv, hmem⟩, ⟨hyb, fun t => ?_, fun t ht => ?_⟩, ?_⟩
  · change proj S t (wt t • (hpm t).toLp (p t)) = wt t • (hpm t).toLp (p t)
    rw [map_smul, proj_toLp_of_meas (hpmeas t)]
  · change proj S t (wt (t + 1) • (hpm (t + 1)).toLp (p (t + 1))) =
      (φ / 2) • (wt t • (hpm t).toLp (p t)) + wt (t + 1) • (hu t).toLp (u t)
    have hp1 : p (t + 1) = finSolM S φ u n (t + 1) := by
      simp only [hp, min_eq_left (Nat.succ_le_of_lt ht)]
    have hp0 : p t = finSolM S φ u n t := by simp only [hp, min_eq_left ht.le]
    rw [map_smul]
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (wt (t + 1)) (proj S t ((hpm (t + 1)).toLp (p (t + 1)))),
      proj_ae t ((hpm (t + 1)).toLp (p (t + 1))), S.E_congr (hpm (t + 1)).coeFn_toLp t,
      finSolM_solves (φ := φ) hua hui n t,
      Lp.coeFn_add ((φ / 2) • (wt t • (hpm t).toLp (p t))) (wt (t + 1) • (hu t).toLp (u t)),
      Lp.coeFn_smul (φ / 2) (wt t • (hpm t).toLp (p t)),
      Lp.coeFn_smul (wt t) ((hpm t).toLp (p t)), (hpm t).coeFn_toLp,
      Lp.coeFn_smul (wt (t + 1)) ((hu t).toLp (u t)), (hu t).coeFn_toLp]
      with ω e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e4 e5 e6 e7 e9 ⊢
    rw [e1, e2, e3, hp1, e4, e5, e6, e7, e8, e9, e10, hp0, wt_succ]
    ring
  · refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
    rw [show (2 : ENNReal).toReal = 2 by norm_num]
    calc ∑' t, ‖yv t‖ ^ (2 : ℝ) ≤ ∑' t, (wt t * C) ^ (2 : ℝ) :=
          Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun t => by positivity) hle hgeo)
            hgeo
      _ = C ^ 2 * (4 / 3) := by
          have : (fun t : ℕ => (wt t * C) ^ (2 : ℝ)) = fun t => C ^ 2 * (1 / 4 : ℝ) ^ t := by
            funext t
            rw [Real.rpow_two, wt, mul_pow, mul_comm]
            congr 1
            rw [← pow_mul, mul_comm t 2, pow_mul]
            norm_num
          rw [this, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
      _ ≤ (2 * C) ^ (2 : ℝ) := by
          rw [Real.rpow_two]
          nlinarith [sq_nonneg C]

/-- Cochrane (2023), §22.7, p. 508 (**sufficiency** on a probability space): at `φ² = 1`, an
adapted, essentially bounded disturbance whose conditional sums are essentially bounded admits an
adapted, essentially bounded solution of the monetary equation. -/
theorem sol_of_condBddM {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u)
    (hub : S.BddProc u) (hCB : CondBddM S φ u) : HasBddSolM S φ u := by
  obtain ⟨Mu, hMu⟩ := hub
  have hu : ∀ t, MemLp (u t) 2 S.μ := fun t =>
    MemLp.of_bound ((hua t).mono (S.𝓕.le t)).aestronglyMeasurable Mu
      ((hMu t).mono fun ω h => by rwa [Real.norm_eq_abs])
  obtain ⟨C₀, hC₀⟩ := hCB
  set C := |C₀| with hCdef
  have hC : ∀ t T, ∀ᵐ ω ∂S.μ, |condSumM S φ u t T ω| ≤ C := fun t T =>
    (hC₀ t T).mono fun ω h => h.trans (le_abs_self _)
  have hC0 : 0 ≤ C := abs_nonneg _
  obtain ⟨z, hz⟩ := exists_mem_iInter_of_antitone (kset_antitone (S := S) hu φ C)
    (fun n => let ⟨y, hy, _⟩ := kset_point hφ hua hu hC0 hC n; ⟨y, hy⟩)
    (isClosed_kset hu φ C) (convex_kset hu φ C) (fun n => kset_point hφ hua hu hC0 hC n)
  have hz1 : ∀ t, z t ∈ BndSet (wt t * C) := (hz 0).1
  have hz2 : ∀ t, proj S t (z t) = z t := (hz 0).2.1
  have hz3 : ∀ t, proj S t (z (t + 1)) = (φ / 2) • z t + wt (t + 1) • (hu t).toLp (u t) :=
    fun t => (hz (t + 1)).2.2 t (Nat.lt_succ_self t)
  set π : ℕ → Ω → ℝ := fun t => S.E t ((wt t)⁻¹ • ⇑(z t)) with hπ
  have hπae : ∀ t, π t =ᵐ[S.μ] (wt t)⁻¹ • ⇑(z t) := fun t => by
    filter_upwards [S.E_smul (wt t)⁻¹ (⇑(z t)) t, proj_ae t (z t)] with ω e1 e2
    simp only [hπ]
    rw [e1, Pi.smul_apply, Pi.smul_apply, ← e2, hz2 t]
  refine ⟨π, fun t => S.stronglyMeasurable_E t _, ⟨C, fun t => ?_⟩, fun t => ?_⟩
  · filter_upwards [hπae t, hz1 t] with ω e1 e2
    rw [e1, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos (wt_pos t)]
    rw [inv_mul_le_iff₀ (wt_pos t)]
    exact e2
  · filter_upwards [S.E_congr (hπae (t + 1)) t, S.E_smul (wt (t + 1))⁻¹ (⇑(z (t + 1))) t,
      proj_ae t (z (t + 1)), hπae t,
      Lp.coeFn_add ((φ / 2) • z t) (wt (t + 1) • (hu t).toLp (u t)),
      Lp.coeFn_smul (φ / 2) (z t), Lp.coeFn_smul (wt (t + 1)) ((hu t).toLp (u t)),
      (hu t).coeFn_toLp] with ω e1 e2 e3 e4 e5 e6 e7 e8
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e4 e5 e6 e7 ⊢
    rw [e1, e2, ← e3, hz3 t, e5, e6, e7, e8, e4, wt_succ]
    have hw := (wt_pos t).ne'
    field_simp

/-- Cochrane (2023), §22.7, p. 508 (**the characterisation** on any probability space with any
filtration): at `φ² = 1`, for an adapted, essentially bounded disturbance, the monetary equation
`E_t π_{t+1} = φπ_t + u_{i,t}` has an adapted, essentially bounded solution **iff** the
conditional sums `∑_{j<T} φʲ E_t u_{t+j}` are essentially bounded, uniformly in `t` and `T`. -/
theorem exists_iff_condBddM {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ}
    (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u) : HasBddSolM S φ u ↔ CondBddM S φ u := by
  have hui : ∀ t, Integrable (u t) S.μ := fun t => by
    obtain ⟨M, hM⟩ := hub
    exact MeasExpectationSystem.BddRV.integrable
      ⟨((hua t).mono (S.𝓕.le t)).aestronglyMeasurable, M, hM t⟩
  exact ⟨condBddM_of_sol hφ hui, sol_of_condBddM hφ hua hub⟩

/-- Cochrane (2023), §22.7, p. 508 (tool): `E_t` of a finite sum of the disturbance is the sum of
the forecasts, a.e. -/
theorem E_sum_ae {u : ℕ → Ω → ℝ} (hui : ∀ t, Integrable (u t) S.μ) (c : ℕ → ℝ) (t T : ℕ) :
    S.E t (∑ j ∈ Finset.range T, c j • u (t + j)) =ᵐ[S.μ]
      ∑ j ∈ Finset.range T, c j • S.E t (u (t + j)) := by
  refine (condExp_finsetSum (fun j _ => (hui (t + j)).smul (c j)) _).trans ?_
  have h := fun j => S.E_smul (c j) (u (t + j)) t
  filter_upwards [ae_all_iff.2 h] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => hω j

/-- Cochrane (2023), §22.7, p. 508, at `φ = 1` on any probability space: a bounded solution of
`E_t π_{t+1} = π_t + u_{i,t}` exists iff `|E_t ∑_{j<T} u_{t+j}| ≤ C` a.e. for all `t`, `T`. -/
theorem exists_iff_phi_one_M {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u)
    (hub : S.BddProc u) :
    HasBddSolM S 1 u ↔
      ∃ C, ∀ t T, ∀ᵐ ω ∂S.μ, |S.E t (∑ j ∈ Finset.range T, u (t + j)) ω| ≤ C := by
  have hui : ∀ t, Integrable (u t) S.μ := fun t => by
    obtain ⟨M, hM⟩ := hub
    exact MeasExpectationSystem.BddRV.integrable
      ⟨((hua t).mono (S.𝓕.le t)).aestronglyMeasurable, M, hM t⟩
  rw [exists_iff_condBddM (by norm_num) hua hub]
  refine exists_congr fun C => forall_congr' fun t => forall_congr' fun T => ?_
  have h := E_sum_ae hui (fun _ => (1 : ℝ)) t T
  simp only [one_smul] at h
  have e : condSumM S 1 u t T = ∑ j ∈ Finset.range T, S.E t (u (t + j)) := by
    simp [condSumM]
  rw [e]
  constructor <;> intro hb <;> filter_upwards [hb, h] with ω e1 e2 <;> simp_all

/-- Cochrane (2023), §22.7, p. 508, at `φ = −1` on any probability space: a bounded solution of
`E_t π_{t+1} = −π_t + u_{i,t}` exists iff `|E_t ∑_{j<T} (−1)ʲ u_{t+j}| ≤ C` a.e. for all `t`,
`T`. -/
theorem exists_iff_phi_neg_one_M {u : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u)
    (hub : S.BddProc u) :
    HasBddSolM S (-1) u ↔
      ∃ C, ∀ t T, ∀ᵐ ω ∂S.μ,
        |S.E t (∑ j ∈ Finset.range T, (-1 : ℝ) ^ j • u (t + j)) ω| ≤ C := by
  have hui : ∀ t, Integrable (u t) S.μ := fun t => by
    obtain ⟨M, hM⟩ := hub
    exact MeasExpectationSystem.BddRV.integrable
      ⟨((hua t).mono (S.𝓕.le t)).aestronglyMeasurable, M, hM t⟩
  rw [exists_iff_condBddM (by norm_num) hua hub]
  refine exists_congr fun C => forall_congr' fun t => forall_congr' fun T => ?_
  have h := E_sum_ae hui (fun j => (-1 : ℝ) ^ j) t T
  unfold condSumM
  constructor <;> intro hb <;> filter_upwards [hb, h] with ω e1 e2
  · rw [e2]; exact e1
  · rw [← e2]; exact e1

/-! ### The realised sums are not necessary under genuine uncertainty -/

open Cochrane.ObservationalEquivalence.ExpectationsMeasureIIDZ
open ExpectationsMeasureIID (coin coin_mean coin_var coin_bdd)

/-- Cochrane (2023), §22.7, p. 508 (tool): in the coin economy the random walk
`∑_{s<t} ε_s` has second moment `t`. -/
theorem integral_randomWalk_sq (t : ℕ) :
    ∫ ω, (∑ s ∈ Finset.range t, shockZ (s : ℤ) ω) ^ 2 ∂(iidZSystem coin).μ = t := by
  have hint : ∀ s r : ℕ, Integrable (fun ω => shockZ (s : ℤ) ω * shockZ (r : ℤ) ω)
      (iidZSystem coin).μ := fun s r =>
    Integrable.of_bound ((measurable_shockZ_pi _).mul (measurable_shockZ_pi _)).aestronglyMeasurable
      1 (by
        filter_upwards [shockZ_ae_bdd coin coin_bdd (s : ℤ), shockZ_ae_bdd coin coin_bdd (r : ℤ)]
          with ω h1 h2
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one).trans (by norm_num))
  have e : (fun ω => (∑ s ∈ Finset.range t, shockZ (s : ℤ) ω) ^ 2) =
      fun ω => ∑ s ∈ Finset.range t, ∑ r ∈ Finset.range t, shockZ (s : ℤ) ω * shockZ (r : ℤ) ω := by
    funext ω
    rw [sq, Finset.sum_mul_sum]
  rw [e, integral_finsetSum _ fun s _ => integrable_finsetSum _ fun r _ => hint s r]
  simp_rw [integral_finsetSum _ fun r _ => hint _ r,
    integral_shockZ_mul coin_mean coin_var coin_bdd, Nat.cast_inj]
  simp only [Finset.sum_ite_eq, Finset.mem_range]
  simp only [Finset.sum_boole, Nat.cast_inj]
  rw [Finset.filter_true_of_mem fun x hx => Finset.mem_range.1 hx, Finset.card_range]

/-- Cochrane (2023), §22.7, pp. 508–509 (**the realised-sum criterion is not necessary under
genuine uncertainty**): in the i.i.d. coin economy, at `φ² = 1`, the adapted bounded disturbance
`u_{i,t} = φᵗ ε_t` has the bounded adapted solution `π_t = −φ^{t+1} ε_t` (so its conditional sums
are bounded), while its realised sums `∑_{s<t} φˢ u_{i,s} = ∑_{s<t} ε_s` — a random walk — are not
essentially bounded. -/
theorem coin_realised_not_necessary {φ : ℝ} (hφ : φ ^ 2 = 1) :
    StronglyAdapted (iidZSystem coin).𝓕 (fun t ω => φ ^ t * shockZ (t : ℤ) ω) ∧
    (iidZSystem coin).BddProc (fun t ω => φ ^ t * shockZ (t : ℤ) ω) ∧
    HasBddSolM (iidZSystem coin) φ (fun t ω => φ ^ t * shockZ (t : ℤ) ω) ∧
    CondBddM (iidZSystem coin) φ (fun t ω => φ ^ t * shockZ (t : ℤ) ω) ∧
    ¬ (iidZSystem coin).BddProc
      (TidyR5UnitRoot.pathSum φ (fun t ω => φ ^ t * shockZ (t : ℤ) ω)) := by
  set S := iidZSystem coin with hS
  set u : ℕ → (ℤ → ℝ) → ℝ := fun t ω => φ ^ t * shockZ (t : ℤ) ω with hu
  have hpow : ∀ n : ℕ, |φ ^ n| = 1 := TidyR5UnitRoot.abs_pow_eq_one hφ
  have hua : StronglyAdapted S.𝓕 u := fun t =>
    ((measurable_shockZ coin (le_refl (t : ℤ))).const_mul _).stronglyMeasurable
  have hub : S.BddProc u := ⟨1, fun t => by
    filter_upwards [shockZ_ae_bdd coin coin_bdd (t : ℤ)] with ω h
    simp only [hu, abs_mul, hpow, one_mul]
    exact h⟩
  have hsol : HasBddSolM S φ u := by
    refine ⟨fun t ω => -(φ ^ (t + 1) * shockZ (t : ℤ) ω), fun t =>
      (((measurable_shockZ coin (le_refl (t : ℤ))).const_mul _).neg).stronglyMeasurable,
      ⟨1, fun t => ?_⟩, fun t => ?_⟩
    · filter_upwards [shockZ_ae_bdd coin coin_bdd (t : ℤ)] with ω h
      simp only [abs_neg, abs_mul, hpow, one_mul]
      exact h
    · have e : (fun ω => -(φ ^ (t + 1 + 1) * shockZ ((t + 1 : ℕ) : ℤ) ω)) =
          (-φ ^ (t + 2)) • shockZ ((t : ℤ) + 1) := by
        funext ω
        simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring
      change S.E t (fun ω => -(φ ^ (t + 1 + 1) * shockZ ((t + 1 : ℕ) : ℤ) ω)) =ᵐ[S.μ] _
      rw [e]
      filter_upwards [S.E_smul (-φ ^ (t + 2)) (shockZ ((t : ℤ) + 1)) t,
        E_shockZ_zero (ν := coin) coin_mean (t := t) (k := (t : ℤ) + 1) (by omega)] with ω e1 e2
      rw [e1, Pi.smul_apply, e2]
      simp only [Pi.zero_apply, smul_eq_mul, mul_zero, Pi.add_apply, Pi.smul_apply, hu]
      have h2 : φ * φ ^ (t + 1) = φ ^ t := by
        rw [← pow_succ', show t + 1 + 1 = t + 2 by omega, TidyR5UnitRoot.pow_add_two hφ]
      linear_combination (shockZ (t : ℤ) ω) * h2
  refine ⟨hua, hub, hsol, (exists_iff_condBddM hφ hua hub).1 hsol, ?_⟩
  rintro ⟨M, hM⟩
  have hpath : ∀ t, TidyR5UnitRoot.pathSum φ u t =
      fun ω => ∑ s ∈ Finset.range t, shockZ (s : ℤ) ω := fun t => by
    funext ω
    simp only [TidyR5UnitRoot.pathSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hu]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← mul_assoc, ← pow_add, ← two_mul, TidyR5UnitRoot.pow_two_mul hφ, one_mul]
  obtain ⟨n, hn⟩ := exists_nat_gt (M ^ 2)
  have hb : ∀ᵐ ω ∂S.μ, (∑ s ∈ Finset.range n, shockZ (s : ℤ) ω) ^ 2 ≤ M ^ 2 := by
    filter_upwards [hM n] with ω h
    rw [hpath] at h
    have h0 : 0 ≤ M := (abs_nonneg _).trans h
    nlinarith [abs_nonneg (∑ s ∈ Finset.range n, shockZ (s : ℤ) ω),
      sq_abs (∑ s ∈ Finset.range n, shockZ (s : ℤ) ω)]
  have hint : Integrable (fun ω => (∑ s ∈ Finset.range n, shockZ (s : ℤ) ω) ^ 2) S.μ := by
    refine Integrable.of_bound ?_ (M ^ 2) ?_
    · exact ((Finset.measurable_sum _ fun s _ => measurable_shockZ_pi _).pow_const
        2).aestronglyMeasurable
    · filter_upwards [hb] with ω h
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h
  have hle := integral_mono_ae hint (integrable_const (M ^ 2)) hb
  rw [integral_randomWalk_sq, integral_const] at hle
  simp only [probReal_univ, smul_eq_mul, one_mul] at hle
  linarith

end Cochrane.ObservationalEquivalence.TidyR5UnitRootMeasure
