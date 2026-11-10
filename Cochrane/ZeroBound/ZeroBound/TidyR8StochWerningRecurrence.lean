/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7StochWerningExist
import ZeroBound.TidyR7OUSampled
import Mathlib.Probability.Independence.ZeroOne

/-!
# The Ornstein–Uhlenbeck equilibria are almost surely unbounded on `[0, ∞)`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, p. 474 ("do not
explode as time increases") and p. 475 (Figure 20.4), under uncertainty.

TidyR7StochWerningExist builds, for every `(π_T, b)`, the equilibria
`π_t = wPi(π_T)_t + ζ^b_t`, `x_t = wX(π_T)_t + (λ^f/κ)ζ^b_t` of the trap experiment, with the
Ornstein–Uhlenbeck innovation `ζ^b = ouProc (λ^b) 0 0 b W`; they are bounded in mean square
but not in `L^∞` (`TidyR7StochWerningExist.not_bdd_ae_eqPi`). Here we prove the pathwise
statement: **for `b ≠ 0`, almost every path of `π` (and of `x`) has `sup_{t ≥ 0} π_t = +∞` and
`inf_{t ≥ 0} π_t = −∞`**; indeed `π` exceeds every level, and falls below every level, at
arbitrarily late integer dates.

The argument is the recurrence of a stationary Gaussian AR(1): sampled at integer dates the OU
process is `ζ_{n+1} = e^{−η}ζ_n + ε_n` with i.i.d. Gaussian innovations `ε_n`
(TidyR7OUSampled). The events "`ζ_n` comes within `1/(m+1)` of `a` from above infinitely often"
are tail events of the innovations (`ouProc_shift`, the effect of `ζ_N` decays like `e^{−ηk}`),
they have positive probability (`prob_ouProc_gt`: Chebyshev for `ζ_n` and the independence of
`ε_n` from `ε_0, …, ε_{n−1}`), hence probability one by Kolmogorov's 0-1 law.

## Main results

* `ouProc_frequently_gt`, `ouProc_frequently_lt`: for `η > 0`, `σ ≠ 0`, almost surely
  `ζ_n > M` and `ζ_n < M` for infinitely many `n`, for every `M`.
* `det_add_ou_unbounded`: a deterministic path bounded on `[0, ∞)` plus `c ζ` (`c ≠ 0`) is
  almost surely unbounded above and below at arbitrarily late dates.
* **`eqPi_unbounded`, `eqX_unbounded`, `eqPi_sup_inf`**: the equilibria with a non-zero
  innovation loading have almost surely unbounded paths on `[0, ∞)`, above and below.
* Non-vacuity on bmPath at the book's calibration: `bmPath_eqPi_sup_inf`.
-/

namespace Cochrane.ZeroBound.TidyR8StochWerningRecurrence

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.TidyR7StochWerning Cochrane.ZeroBound.TidyR7StochWerningExist
open Cochrane.ZeroBound.TidyR7OUPath Cochrane.ZeroBound.TidyR7OrnsteinUhlenbeck
open Cochrane.ZeroBound.TidyR7OUSampled Cochrane.ZeroBound.TidyR7BrownianTools
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-! ## Tail-event tools (restated from the FiscalConstraints project) -/

/-- Cochrane (2023), p. 197 (tool): a frequently-true property is shift invariant.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.frequently_shift_iff). -/
theorem frequently_shift_iff {p : ℕ → Prop} (N : ℕ) :
    (∃ᶠ t in atTop, p t) ↔ ∃ᶠ k in atTop, p (N + k) := by
  rw [frequently_atTop, frequently_atTop]
  constructor
  · intro h a
    obtain ⟨t, ht, hp⟩ := h (N + a)
    exact ⟨t - N, by omega, by rwa [show N + (t - N) = t by omega]⟩
  · intro h a
    obtain ⟨k, hk, hp⟩ := h a
    exact ⟨N + k, by omega, hp⟩

/-- Cochrane (2023), p. 197 (tool): "`z_t` gets within `1/(m+1)` of `a` from above infinitely
often, for every `m`" is unchanged by a perturbation that vanishes at infinity.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.frequently_near_of_tendsto). -/
theorem frequently_near_of_tendsto {z z' : ℕ → ℝ} (hzz : Tendsto (fun t => z t - z' t) atTop (𝓝 0))
    {a : ℝ} (h : ∀ m : ℕ, ∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < z t) (m : ℕ) :
    ∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < z' t := by
  have hpos : (0 : ℝ) < 1 / (2 * (m : ℝ) + 2) := by positivity
  have hev : ∀ᶠ t in atTop, |z t - z' t| < 1 / (2 * (m : ℝ) + 2) := by
    refine (hzz.eventually (Metric.ball_mem_nhds 0 hpos)).mono fun t ht => ?_
    rw [Real.dist_0_eq_abs] at ht
    exact ht
  have hf := h (2 * m + 1)
  refine (hf.and_eventually hev).mono fun t ht => ?_
  obtain ⟨h1, h2⟩ := ht
  rw [abs_lt] at h2
  have e1 : (1 : ℝ) / ((((2 * m + 1 : ℕ)) : ℝ) + 1) = 1 / (2 * (m : ℝ) + 2) := by
    push_cast; ring_nf
  rw [e1] at h1
  have e2 : 1 / (2 * (m : ℝ) + 2) + 1 / (2 * (m : ℝ) + 2) = 1 / ((m : ℝ) + 1) := by
    field_simp; ring
  linarith

/-- Cochrane (2023), p. 197 (tool): the event "frequently near or above `a`" for a sequence of
`m'`-measurable variables is `m'`-measurable.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.measurableSet_frequently_near). -/
theorem measurableSet_frequently_near {m' : MeasurableSpace Ω} {y : ℕ → Ω → ℝ}
    (hy : ∀ k, Measurable[m'] (y k)) (a : ℝ) :
    MeasurableSet[m'] {ω | ∀ m : ℕ, ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < y k ω} := by
  have h : {ω | ∀ m : ℕ, ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < y k ω} =
      ⋂ m : ℕ, ⋂ n : ℕ, ⋃ k : ℕ, ⋃ (_ : n ≤ k), {ω | a - 1 / ((m : ℝ) + 1) < y k ω} := by
    ext ω
    simp [frequently_atTop]
  rw [h]
  exact MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => MeasurableSet.iUnion
    fun k => MeasurableSet.iUnion fun _ => measurableSet_lt measurable_const (hy k)

/-- Cochrane (2023), p. 197 (tool): if the events `A_{t+2}` all have probability at least `q`,
then "`A_t` infinitely often" has probability at least `q` (continuity from above).
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.DebtLimitStochasticMeasure.le_measure_frequently). -/
theorem le_measure_frequently {μ : Measure Ω} [IsFiniteMeasure μ] {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet (A t)) {q : ENNReal}
    (hq : ∀ t, q ≤ μ (A (t + 2))) : q ≤ μ {ω | ∃ᶠ t in atTop, ω ∈ A t} := by
  set B : ℕ → Set Ω := fun N => ⋃ t, ⋃ (_ : N ≤ t), A t with hBdef
  have hset : {ω | ∃ᶠ t in atTop, ω ∈ A t} = ⋂ N, B N := by
    ext ω
    simp [hBdef, frequently_atTop]
  have hanti : Antitone B := fun N N' h ω hω => by
    simp only [hBdef, Set.mem_iUnion] at hω ⊢
    obtain ⟨t, ht, h'⟩ := hω
    exact ⟨t, h.trans ht, h'⟩
  have hBm : ∀ N, NullMeasurableSet (B N) μ := fun N =>
    (MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun _ => hA t).nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hBm hanti ⟨0, measure_ne_top μ _⟩
  rw [hset]
  refine ge_of_tendsto' hlim fun N => ?_
  calc q ≤ μ (A (N + 2)) := hq N
    _ ≤ μ (B N) := measure_mono (Set.subset_biUnion_of_mem (u := A) (by omega : N ≤ N + 2))

/-! ## The sampled OU process and its innovations -/

/-- Cochrane (2023), §20.2.2, p. 474: the OU innovation at integer dates,
`ζ_{n+1} = e^{−η}ζ_n + ε_n` (`ζ = ouProc η 0 0 σ W`), path by path.
`TidyR7OUSampled.ouProc_succ` with `s̄ = s_0 = 0`. -/
theorem ouProc_succ_zero (hcont : ∀ ω, Continuous fun t => W t ω) (η σ : ℝ) (n : ℕ) (ω : Ω) :
    ouProc η 0 0 σ W ((n + 1 : ℕ) : ℝ) ω =
      Real.exp (-η) * ouProc η 0 0 σ W n ω + ouInnov η σ W n ω := by
  have h := ouProc_succ hcont η 0 0 σ n ω
  push_cast
  linarith

/-- Cochrane (2023), §20.2.2, p. 474 (tool): the OU process is measurable at every date.
A corollary of `TidyR7StochWerningExist.stronglyMeasurable_ouProc`. -/
theorem measurable_ouProc_at (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (η σ t : ℝ) :
    Measurable (ouProc η 0 0 σ W t) :=
  ((stronglyMeasurable_ouProc hW hcont η 0 0 σ t).mono ((bmFiltrationReal W hW).le t)).measurable

/-- Cochrane (2023), §20.2.2, p. 474 (tool): the innovations are measurable.
Strengthens `TidyR7OUSampled.aemeasurable_ouInnov`; here `ouInnov n` is the innovation that module
writes `ε_{n+1}`. -/
theorem measurable_ouInnov (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (η σ : ℝ) (n : ℕ) : Measurable (ouInnov η σ W n) := by
  have e : ouInnov η σ W n = fun ω => ouProc η 0 0 σ W ((n + 1 : ℕ) : ℝ) ω -
      Real.exp (-η) * ouProc η 0 0 σ W n ω := by
    funext ω
    rw [ouProc_succ_zero hcont]
    ring
  rw [e]
  exact (measurable_ouProc_at hW hcont η σ _).sub
    ((measurable_ouProc_at hW hcont η σ _).const_mul _)

/-- Cochrane (2023), §20.2.2, p. 474: the σ-algebra generated by the innovation `ε_n`. -/
noncomputable abbrev innovSigma (η σ : ℝ) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (ouInnov η σ W n) inferInstance

/-- Cochrane (2023), §20.2.2, p. 474 (tool): `σ(ε_n)` is a sub-σ-algebra. -/
theorem innovSigma_le (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (η σ : ℝ) (n : ℕ) : innovSigma η σ W n ≤ mΩ :=
  (measurable_ouInnov hW hcont η σ n).comap_le

/-- Cochrane (2023), §20.2.2, p. 474 (tool): `ε_n` is `σ(ε_n)`-measurable. -/
theorem measurable_ouInnov_sigma (η σ : ℝ) (n : ℕ) :
    Measurable[innovSigma η σ W n] (ouInnov η σ W n) :=
  comap_measurable _

/-- Cochrane (2023), §20.2.2, p. 474: **the innovation σ-algebras are independent**
(`TidyR7OUSampled.iIndepFun_ouInnov`). -/
theorem iIndep_innovSigma (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {η : ℝ} (hη : 0 < η) (σ : ℝ) :
    iIndep (innovSigma η σ W) P :=
  (iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_ouInnov hB hW hcont hη σ)

/-- Cochrane (2023), §20.2.2, p. 474: the OU process restarted at `N` from `0`, driven by
`ε_N, ε_{N+1}, …`: `w_0 = 0`, `w_{k+1} = e^{−η}w_k + ε_{N+k}`. -/
noncomputable def ouFrom (η σ : ℝ) (W : ℝ≥0 → Ω → ℝ) (N : ℕ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun ω => Real.exp (-η) * ouFrom η σ W N k ω + ouInnov η σ W (N + k) ω

/-- Cochrane (2023), §20.2.2, p. 474: restarting at `N`, `ζ_{N+k} = e^{−ηk}ζ_N + w_k`. -/
theorem ouProc_shift (hcont : ∀ ω, Continuous fun t => W t ω) (η σ : ℝ) (N : ℕ) (ω : Ω) :
    ∀ k : ℕ, ouProc η 0 0 σ W ((N + k : ℕ) : ℝ) ω =
      Real.exp (-η) ^ k * ouProc η 0 0 σ W N ω + ouFrom η σ W N k ω := by
  intro k
  induction k with
  | zero => simp [ouFrom]
  | succ k ih =>
    rw [← add_assoc, ouProc_succ_zero hcont, ih]
    change _ = _ + (Real.exp (-η) * ouFrom η σ W N k ω + ouInnov η σ W (N + k) ω)
    ring

/-- Cochrane (2023), §20.2.2, p. 474: the restarted process depends only on the innovations
from date `N` on. -/
theorem measurable_ouFrom (η σ : ℝ) (N : ℕ) :
    ∀ k, Measurable[⨆ i ≥ N, innovSigma η σ W i] (ouFrom η σ W N k) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact (ih.const_mul _).add ((measurable_ouInnov_sigma η σ (N + k)).mono
      (le_iSup₂ (f := fun i (_ : i ≥ N) => innovSigma η σ W i) (N + k) (by omega)) le_rfl)

/-- Cochrane (2023), §20.2.2, p. 474: `ζ_n` depends only on the innovations before `n`. -/
theorem measurable_ouProc_past (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (η σ : ℝ) :
    ∀ n : ℕ, Measurable[⨆ i ∈ Set.Iio n, innovSigma η σ W i] (ouProc η 0 0 σ W n) := by
  intro n
  induction n with
  | zero =>
    have e : ouProc η 0 0 σ W ((0 : ℕ) : ℝ) = fun _ => 0 := by
      funext ω
      simpa using ouProc_zero hW0 η 0 0 σ ω
    rw [e]
    exact measurable_const
  | succ n ih =>
    have e : ouProc η 0 0 σ W ((n + 1 : ℕ) : ℝ) =
        fun ω => Real.exp (-η) * ouProc η 0 0 σ W n ω + ouInnov η σ W n ω :=
      funext (ouProc_succ_zero hcont η σ n)
    rw [e]
    refine ((ih.mono (biSup_mono fun i (hi : i ∈ Set.Iio n) =>
      (show i ∈ Set.Iio (n + 1) from Nat.lt_succ_of_lt hi)) le_rfl).const_mul _).add
        ((measurable_ouInnov_sigma η σ n).mono ?_ le_rfl)
    exact le_iSup₂ (f := fun i (_ : i ∈ Set.Iio (n + 1)) => innovSigma η σ W i) n
      (Nat.lt_succ_self n)

/-- Cochrane (2023), §20.2.2, p. 474: **`ζ_{n+1}` exceeds any level with probability bounded
away from zero, uniformly in `n`.** Chebyshev: `P(ζ_n² ≥ D) ≤ σ²/(2ηD) ≤ 1/2`; and
`ε_n > a + 1 + D` is independent of `ζ_n` and has a fixed positive probability. -/
theorem prob_ouProc_gt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ : ℝ} (hη : 0 < η)
    (hσ : σ ≠ 0) (a : ℝ) :
    ∃ q : ℝ≥0∞, q ≠ 0 ∧ ∀ n : ℕ, q ≤ P {ω | a < ouProc η 0 0 σ W ((n + 1 : ℕ) : ℝ) ω} := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set D := σ ^ 2 / η + 1 with hD
  have hσ2 : 0 ≤ σ ^ 2 / η := div_nonneg (sq_nonneg σ) hη.le
  have hD0 : 0 < D := by linarith
  set c := a + (1 + D) with hc
  set p := gaussianReal 0 (ouVar η σ 1) (Set.Ioi c) with hp
  have hp0 : p ≠ 0 :=
    (gaussianReal_open_pos 0 (ouVar_ne_zero hη hσ one_pos) isOpen_Ioi Set.nonempty_Ioi).ne'
  refine ⟨p * ENNReal.ofReal (1 / 2), mul_ne_zero hp0 (by norm_num), fun n => ?_⟩
  set ζ := ouProc η 0 0 σ W (n : ℝ) with hζ
  set A := {ω | c < ouInnov η σ W n ω} with hA
  set B := {ω | ζ ω ^ 2 < D} with hBset
  have hAm : MeasurableSet[⨆ i ∈ ({n} : Set ℕ), innovSigma η σ W i] A :=
    measurableSet_lt measurable_const ((measurable_ouInnov_sigma η σ n).mono
      (le_iSup₂ (f := fun i (_ : i ∈ ({n} : Set ℕ)) => innovSigma η σ W i) n rfl) le_rfl)
  have hBm : MeasurableSet[⨆ i ∈ Set.Iio n, innovSigma η σ W i] B :=
    measurableSet_lt ((measurable_ouProc_past hcont hW0 η σ n).pow_const 2) measurable_const
  have hind := (Indep_iff _ _ _).1 (indep_iSup_of_disjoint (innovSigma_le hW hcont η σ)
    (iIndep_innovSigma hB hW hcont hη σ) (S := {n}) (T := Set.Iio n)
    (Set.disjoint_singleton_left.2 (lt_irrefl n))) A B hAm hBm
  have hAval : P A = p := by
    rw [hp, ← ouInnov_hasLaw hB hW hcont hη σ n,
      Measure.map_apply (measurable_ouInnov hW hcont η σ n) measurableSet_Ioi]
    rfl
  have hBval : ENNReal.ofReal (1 / 2) ≤ P B := by
    obtain ⟨hmem, hsq⟩ := ouProc_sq_le hB hW hcont hW0 hη σ (Nat.cast_nonneg (α := ℝ) n)
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Eventually.of_forall fun ω => sq_nonneg (ζ ω)) hmem.integrable_sq D
    have hreal : P.real {ω | D ≤ ζ ω ^ 2} ≤ 1 / 2 := by
      have h1 : D * P.real {ω | D ≤ ζ ω ^ 2} ≤ σ ^ 2 / (2 * η) := hmk.trans hsq
      have h2 : σ ^ 2 / (2 * η) = (σ ^ 2 / η) / 2 := by field_simp
      have hpr := measureReal_nonneg (μ := P) (s := {ω | D ≤ ζ ω ^ 2})
      have hpr1 : P.real {ω | D ≤ ζ ω ^ 2} ≤ 1 := measureReal_le_one
      nlinarith
    have hcompl : Bᶜ = {ω | D ≤ ζ ω ^ 2} := by
      ext ω
      simp [hBset]
    have hBmeas : MeasurableSet B :=
      measurableSet_lt ((measurable_ouProc_at hW hcont η σ _).pow_const 2) measurable_const
    have hBc : P.real Bᶜ ≤ 1 / 2 := by rw [hcompl]; exact hreal
    rw [measureReal_compl hBmeas, probReal_univ] at hBc
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hsub : A ∩ B ⊆ {ω | a < ouProc η 0 0 σ W ((n + 1 : ℕ) : ℝ) ω} := by
    rintro ω ⟨ha, hb⟩
    simp only [hA, hBset, Set.mem_ofPred_eq] at ha hb ⊢
    rw [ouProc_succ_zero hcont]
    have hρ0 : 0 < Real.exp (-η) := Real.exp_pos _
    have hρ1 : Real.exp (-η) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hz : -(1 + D) < ζ ω := by nlinarith [sq_nonneg (ζ ω + 1)]
    have hz2 : -(1 + D) < Real.exp (-η) * ζ ω := by
      rcases le_total 0 (ζ ω) with h | h
      · nlinarith [mul_nonneg hρ0.le h]
      · nlinarith [mul_le_mul_of_nonpos_right hρ1 h]
    simp only [hc] at ha
    linarith
  calc p * ENNReal.ofReal (1 / 2) ≤ P A * P B := by rw [hAval]; gcongr
    _ = P (A ∩ B) := hind.symm
    _ ≤ _ := measure_mono hsub

/-! ## Recurrence -/

/-- **Cochrane (2023), §20.2.2, p. 474: the sampled OU process is almost surely unbounded
above.** For `η > 0`, `σ ≠ 0`, almost surely `ζ_n > M` for infinitely many integers `n`, for
every `M` (`ζ = ouProc η 0 0 σ W`). Tail events (`ouProc_shift`) of positive probability
(`prob_ouProc_gt`) have probability one (Kolmogorov's 0-1 law,
`ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop`). -/
theorem ouProc_frequently_gt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ : ℝ} (hη : 0 < η)
    (hσ : σ ≠ 0) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ᶠ n : ℕ in atTop, M < ouProc η 0 0 σ W n ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set x : ℕ → Ω → ℝ := fun n ω => ouProc η 0 0 σ W n ω with hx
  set E : ℝ → Set Ω := fun a =>
    {ω | ∀ m : ℕ, ∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < x t ω} with hE
  have hρ0 : 0 ≤ Real.exp (-η) := (Real.exp_pos _).le
  have hρ1 : Real.exp (-η) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have htail : ∀ a, MeasurableSet[limsup (innovSigma η σ W) atTop] (E a) := by
    intro a
    rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
    intro N
    set y : ℕ → Ω → ℝ := fun k => ouFrom η σ W N k with hy
    have heq : E a = {ω | ∀ m : ℕ, ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < y k ω} := by
      ext ω
      simp only [hE, Set.mem_ofPred_eq]
      have hshift : ∀ m : ℕ, (∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < x t ω) ↔
          ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < x (N + k) ω :=
        fun m => frequently_shift_iff N
      simp only [hshift]
      have hdiff : Tendsto (fun k => x (N + k) ω - y k ω) atTop (𝓝 0) := by
        have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (x N ω)
        rw [zero_mul] at h1
        refine h1.congr fun k => ?_
        simp only [hx, hy]
        rw [ouProc_shift hcont η σ N ω k]
        ring
      have hdiff' : Tendsto (fun k => y k ω - x (N + k) ω) atTop (𝓝 0) := by
        have := hdiff.neg
        rw [neg_zero] at this
        refine this.congr fun k => ?_
        ring
      exact ⟨fun h m => frequently_near_of_tendsto hdiff h m,
        fun h m => frequently_near_of_tendsto hdiff' h m⟩
    rw [heq]
    exact measurableSet_frequently_near (measurable_ouFrom η σ N) a
  have hpos : ∀ a, P (E a) ≠ 0 := by
    intro a
    obtain ⟨q, hq0, hq⟩ := prob_ouProc_gt hB hW hcont hW0 hη hσ a
    have hfreq := le_measure_frequently (μ := P) (A := fun t => {ω | a < x t ω})
      (fun t => measurableSet_lt measurable_const (measurable_ouProc_at hW hcont η σ _))
      (fun t => hq (t + 1))
    have hsub : {ω | ∃ᶠ t in atTop, ω ∈ {ω' | a < x t ω'}} ⊆ E a := by
      intro ω hω m
      refine hω.mono fun t ht => ?_
      have : 0 < 1 / ((m : ℝ) + 1) := by positivity
      simp only [Set.mem_ofPred_eq] at ht
      linarith
    intro h0
    exact hq0 (nonpos_iff_eq_zero.1 ((hfreq.trans (measure_mono hsub)).trans_eq h0))
  have hone : ∀ n : ℕ, ∀ᵐ ω ∂P, ω ∈ E n := by
    intro n
    rcases measure_zero_or_one_of_measurableSet_limsup_atTop (innovSigma_le hW hcont η σ)
      (iIndep_innovSigma hB hW hcont hη σ) (htail n) with h | h
    · exact absurd h (hpos n)
    · have hm : MeasurableSet (E n) :=
        (limsup_le_iSup.trans (iSup_le (innovSigma_le hW hcont η σ))) _ (htail n)
      rw [ae_iff]
      have := (prob_compl_eq_zero_iff hm).2 h
      simpa [Set.compl_def] using this
  filter_upwards [ae_all_iff.2 hone] with ω hω M
  obtain ⟨n, hn⟩ := exists_nat_gt (M + 1)
  refine (hω n 0).mono fun t ht => ?_
  simp only [CharP.cast_eq_zero, zero_add, div_one] at ht
  linarith

/-- Cochrane (2023), §20.2.2, p. 474: **the sampled OU process is almost surely unbounded
below**: almost surely `ζ_n < M` for infinitely many `n`, for every `M` (apply
`ouProc_frequently_gt` to the loading `−σ`, `ζ^{−σ} = −ζ^σ`). -/
theorem ouProc_frequently_lt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ : ℝ} (hη : 0 < η)
    (hσ : σ ≠ 0) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ᶠ n : ℕ in atTop, ouProc η 0 0 σ W n ω < M := by
  filter_upwards [ouProc_frequently_gt hB hW hcont hW0 hη (neg_ne_zero.2 hσ)] with ω hω M
  refine (hω (-M)).mono fun n hn => ?_
  rw [ouProc_loading η (-σ), neg_mul, ← ouProc_loading η σ] at hn
  linarith

/-- Cochrane (2023), §20.2.2, p. 474: **a bounded deterministic path plus a non-zero multiple of
the OU process is almost surely unbounded above and below** at arbitrarily late dates
`t → ∞` (real `t`, through the integer dates). -/
theorem det_add_ou_unbounded (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η b c : ℝ} (hη : 0 < η)
    (hb : b ≠ 0) (hc : c ≠ 0) {f : ℝ → ℝ} (hf : BddOnIci f) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, (∃ᶠ t in atTop, M < f t + c * ouProc η 0 0 b W t ω) ∧
      ∃ᶠ t in atTop, f t + c * ouProc η 0 0 b W t ω < M := by
  obtain ⟨K, hK⟩ := hf
  have hcb : c * b ≠ 0 := mul_ne_zero hc hb
  filter_upwards [ouProc_frequently_gt hB hW hcont hW0 hη hcb,
    ouProc_frequently_lt hB hW hcont hW0 hη hcb] with ω hgt hlt M
  have he : ∀ t : ℝ, c * ouProc η 0 0 b W t ω = ouProc η 0 0 (c * b) W t ω := fun t => by
    rw [ouProc_loading η b, ouProc_loading η (c * b)]
    ring
  refine ⟨tendsto_natCast_atTop_atTop.frequently ((hgt (M + K)).mono fun n hn => ?_),
    tendsto_natCast_atTop_atTop.frequently ((hlt (M - K)).mono fun n hn => ?_)⟩
  · have := (abs_le.1 (hK n (Nat.cast_nonneg n))).1
    rw [he]
    linarith
  · have := (abs_le.1 (hK n (Nat.cast_nonneg n))).2
    rw [he]
    linarith

/-! ## The equilibria -/

/-- **Cochrane (2023), §20.2.2, pp. 474–475, under uncertainty: the inflation path of an
equilibrium with a non-zero innovation loading is almost surely unbounded on `[0, ∞)`**, above
and below: almost surely, for every `M`, `π_t > M` and `π_t < M` at arbitrarily late dates.
Strengthens `TidyR7StochWerningExist.not_bdd_ae_eqPi`. -/
theorem eqPi_unbounded (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {σ ρ κ : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (T u g πT : ℝ) {b : ℝ} (hb : b ≠ 0) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, (∃ᶠ t in atTop, M < eqPi σ κ ρ T u g πT b W t ω) ∧
      ∃ᶠ t in atTop, eqPi σ κ ρ T u g πT b W t ω < M := by
  filter_upwards [det_add_ou_unbounded hB hW hcont hW0 (lamb_pos (ρ := ρ) hκ hσ) hb one_ne_zero
    (wPath_bdd (ρ := ρ) hκ hσ T u g πT).2] with ω hω M
  simpa only [eqPi, one_mul] using hω M

/-- Cochrane (2023), (20.10), p. 475, under uncertainty: **the output path of an equilibrium
with a non-zero innovation loading is almost surely unbounded on `[0, ∞)`**, above and
below. -/
theorem eqX_unbounded (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {σ ρ κ : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (T u g πT : ℝ) {b : ℝ} (hb : b ≠ 0) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, (∃ᶠ t in atTop, M < eqX σ κ ρ T u g πT b W t ω) ∧
      ∃ᶠ t in atTop, eqX σ κ ρ T u g πT b W t ω < M := by
  have hc : lamf ρ κ σ / κ ≠ 0 := div_ne_zero (lamf_pos hκ hσ).ne' hκ.ne'
  filter_upwards [det_add_ou_unbounded hB hW hcont hW0 (lamb_pos (ρ := ρ) hκ hσ) hb hc
    (wPath_bdd (ρ := ρ) hκ hσ T u g πT).1] with ω hω M
  simpa only [eqX] using hω M

/-- **Cochrane (2023), §20.2.2, p. 474 ("do not explode"), under uncertainty: almost surely
`sup_{t ≥ 0} π_t = +∞` and `inf_{t ≥ 0} π_t = −∞`** for the equilibria with `b ≠ 0`, which
are nevertheless bounded in mean square (`TidyR7StochWerningExist.bddL2_eqPi`). -/
theorem eqPi_sup_inf (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {σ ρ κ : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (T u g πT : ℝ) {b : ℝ} (hb : b ≠ 0) :
    ∀ᵐ ω ∂P, ¬ BddAbove ((fun t => eqPi σ κ ρ T u g πT b W t ω) '' Set.Ici 0) ∧
      ¬ BddBelow ((fun t => eqPi σ κ ρ T u g πT b W t ω) '' Set.Ici 0) := by
  filter_upwards [eqPi_unbounded hB hW hcont hW0 hσ hκ T u g πT hb] with ω hω
  refine ⟨fun ⟨M, hM⟩ => ?_, fun ⟨M, hM⟩ => ?_⟩
  · obtain ⟨t, ht, ht0⟩ := ((hω M).1.and_eventually (eventually_ge_atTop 0)).exists
    exact absurd (hM ⟨t, ht0, rfl⟩) (not_le.2 ht)
  · obtain ⟨t, ht, ht0⟩ := ((hω M).2.and_eventually (eventually_ge_atTop 0)).exists
    exact absurd (hM ⟨t, ht0, rfl⟩) (not_le.2 ht)

/-! ## Non-vacuity on the constructed Brownian motion -/

open Cochrane.ZeroBound.TidyR7BrownianExist Cochrane.ZeroBound.TidyR7BrownianSchauder

/-- Cochrane (2023), §20.2.2, p. 474 (non-vacuity): on bmPath at the book's calibration
(`ρ = 0.05`, `σ = κ = 1`, `T = 5`, `u_r = −2%`, `g = 0`, `π_T = 0`, unit loading), almost every
inflation path is unbounded above and below on `[0, ∞)`, although the process is bounded in
mean square. -/
theorem bmPath_eqPi_sup_inf :
    (∀ᵐ ω ∂gaussSeq,
      ¬ BddAbove ((fun t => eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath t ω) '' Set.Ici 0) ∧
      ¬ BddBelow ((fun t => eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath t ω) '' Set.Ici 0)) ∧
    BddL2 gaussSeq (eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath) := by
  have := isProbabilityMeasure_gaussSeq
  exact ⟨eqPi_sup_inf isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath bmPath_zero
      one_pos one_pos _ _ _ _ one_ne_zero,
    bddL2_eqPi isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath bmPath_zero one_pos
      one_pos _ _ _ _ _⟩

end Cochrane.ZeroBound.TidyR8StochWerningRecurrence
