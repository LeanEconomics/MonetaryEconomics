/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.TidyR8OUDebtUnbounded

/-!
# The boundary case `r = g`: debt (6.5) with an OU surplus

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197, with the
debt equation (6.4)–(6.5), p. 196, at `a = r − g = 0`: `b_t = b_0 − ∫_0^t s_u du`.

At `a = 0` the restarted debt does not forget its date-`N` state (`γ = e^0 = 1`), so the tail
argument of TidyR8OUDebtUnbounded needs a different route: the perturbation stays bounded
(`abs_dseq_one_le`), so "exceeds every level infinitely often" is still a tail event, and its
probability is positive because the variance of debt grows without bound (`integral_debtG_sq_ge`,
the integrated AR(1)) while the mean is bounded on the relevant side.

## Main results (`a = 0`, `η > 0`, `σ ≠ 0`)

* `chain_frequently_of_eventually`: the 0-1 law for the chain with `γ = 1`;
* **`rgEqual_frequently_gt`**: if `s̄ ≤ 0`, almost surely debt exceeds every level at arbitrarily
  late dates (so `sup_{t ≥ 0} b_t = ∞`);
* **`rgEqual_frequently_lt`**: if `s̄ ≥ 0`, almost surely debt falls below every level at
  arbitrarily late dates (`inf_{t ≥ 0} b_t = −∞`);
* **`rgEqual_sup_inf`**: with `s̄ = 0` both; non-vacuity `bmPath_rgEqual_sup_inf`.
-/

namespace Cochrane.FiscalConstraints.TidyR8OUDebtRgEqual

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.FiscalConstraints.TidyR7OUPath Cochrane.FiscalConstraints.TidyR7WienerGaussian
open Cochrane.FiscalConstraints.TidyR7OrnsteinUhlenbeck
open Cochrane.FiscalConstraints.TidyR7BrownianTools Cochrane.FiscalConstraints.LinearODE
open Cochrane.FiscalConstraints.DebtLimitStochasticMeasure
open Cochrane.FiscalConstraints.TidyR5GaussianAR1
open Cochrane.FiscalConstraints.TidyR8OURestart Cochrane.FiscalConstraints.TidyR8DebtChain
open Cochrane.FiscalConstraints.TidyR8OUDebtUnbounded
open scoped ENNReal NNReal

/-! ### The chain with `γ = 1` -/

/-- Cochrane (2023), p. 197: with `γ = 1` the response to the date-`N` surplus gap stays
bounded, `|d_k| ≤ 1/(1 − |ρ|)` for `|ρ| < 1`.
A companion to `TidyR5GaussianAR1.abs_dseq_le`. -/
theorem abs_dseq_one_le {ρ : ℝ} (hρ : |ρ| < 1) (k : ℕ) : |dseq 1 ρ k| ≤ 1 / (1 - |ρ|) := by
  have h1 : 0 < 1 - |ρ| := by linarith
  have hk : ∀ k, |dseq 1 ρ k| ≤ (1 - |ρ| ^ k) / (1 - |ρ|) := by
    intro k
    induction k with
    | zero => simp [dseq]
    | succ k ih =>
      change |1 * dseq 1 ρ k - ρ ^ k| ≤ _
      rw [one_mul]
      calc |dseq 1 ρ k - ρ ^ k| ≤ |dseq 1 ρ k| + |ρ ^ k| := abs_sub _ _
        _ ≤ (1 - |ρ| ^ k) / (1 - |ρ|) + |ρ| ^ k := by rw [abs_pow]; linarith
        _ = (1 - |ρ| ^ (k + 1)) / (1 - |ρ|) := by field_simp; ring
  refine (hk k).trans (div_le_div_of_nonneg_right ?_ h1.le)
  linarith [pow_nonneg (abs_nonneg ρ) k]

/-- Cochrane (2023), p. 197 (tool): the event "`y_k` exceeds every natural level infinitely
often" is measurable when every `y_k` is.
The construction of `DebtLimitStochasticMeasure.measurableSet_frequently_near`. -/
theorem measurableSet_frequently_nat {Ξ : Type*} {m' : MeasurableSpace Ξ} {y : ℕ → Ξ → ℝ}
    (hy : ∀ k, Measurable[m'] (y k)) :
    MeasurableSet[m'] {ξ | ∀ M : ℕ, ∃ᶠ k in atTop, (M : ℝ) < y k ξ} := by
  have h : {ξ | ∀ M : ℕ, ∃ᶠ k in atTop, (M : ℝ) < y k ξ} =
      ⋂ M : ℕ, ⋂ n : ℕ, ⋃ k : ℕ, ⋃ (_ : n ≤ k), {ξ | (M : ℝ) < y k ξ} := by
    ext ξ
    simp [frequently_atTop]
  rw [h]
  exact MeasurableSet.iInter fun M => MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun _ => measurableSet_lt measurable_const (hy k)

/-- **Cochrane (2023), p. 197: the 0-1 law for the chain with `γ = 1`.** Under any probability
measure making the innovations independent, `|ρ| < 1`, any `θ`: if some `q > 0` bounds
`P(θx_n > M)` from below for all large `n`, for every level `M`, then almost surely `θx_n`
exceeds every level infinitely often.
The `γ = 1` analogue of `TidyR8DebtChain.chain_frequently`. -/
theorem chain_frequently_of_eventually {Q : Measure (ℕ → Fin 2 → ℝ)} [IsProbabilityMeasure Q]
    (hind : iIndepFun (fun n (ξ : ℕ → Fin 2 → ℝ) => ξ n) Q) {ρ : ℝ} (hρ : |ρ| < 1)
    (c0 c1 u0 x0 θ : ℝ) {q : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq : ∀ M : ℝ, ∃ N0 : ℕ, ∀ n, N0 ≤ n → q ≤ Q {ξ | M < θ * chainX ρ 1 c0 c1 u0 x0 n ξ}) :
    ∀ᵐ ξ ∂Q, ∀ M : ℝ, ∃ᶠ n in atTop, M < θ * chainX ρ 1 c0 c1 u0 x0 n ξ := by
  set x := chainX ρ 1 c0 c1 u0 x0 with hx
  have hindep : iIndep blockSigma Q := hind.iIndep
  set U : ℕ → Set (ℕ → Fin 2 → ℝ) := fun M => {ξ | ∃ᶠ n in atTop, (M : ℝ) < θ * x n ξ} with hU
  set E := {ξ : ℕ → Fin 2 → ℝ | ∀ M : ℕ, ∃ᶠ n in atTop, (M : ℝ) < θ * x n ξ} with hE
  have hxm : ∀ n, Measurable fun ξ => θ * x n ξ := fun n =>
    (measurable_chainX ρ 1 c0 c1 u0 x0 n).const_mul θ
  have htail : MeasurableSet[limsup blockSigma atTop] E := by
    rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
    intro N
    set y : ℕ → (ℕ → Fin 2 → ℝ) → ℝ := fun k ξ => θ * chainX ρ 1 c0 c1 0 0 k (shiftSeq N ξ)
      with hy
    have hym : ∀ k, Measurable[⨆ i ≥ N, blockSigma i] (y k) := fun k =>
      (measurable_chainX_shift ρ 1 c0 c1 N k).const_mul θ
    have heq : E = {ξ | ∀ M : ℕ, ∃ᶠ k in atTop, (M : ℝ) < y k ξ} := by
      ext ξ
      simp only [hE, Set.mem_ofPred_eq]
      set B := |θ| * (|x N ξ| + |chainU ρ u0 N ξ| * |c1| * (1 / (1 - |ρ|))) with hB
      have hdiff : ∀ k, |θ * x (N + k) ξ - y k ξ| ≤ B := by
        intro k
        have e : θ * x (N + k) ξ - y k ξ
            = θ * (x N ξ + chainU ρ u0 N ξ * (c1 * dseq 1 ρ k)) := by
          rw [hx, chainX_shift]
          simp only [hy, one_pow, one_mul]
          ring
        rw [e, abs_mul, hB]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg θ)
        refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
        rw [abs_mul, abs_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (abs_dseq_one_le hρ k)
          (abs_nonneg c1)) (abs_nonneg _)
      constructor
      · intro h M
        have h1 := (frequently_shift_iff N).1 (h (M + ⌈B⌉₊))
        refine h1.mono fun k hk => ?_
        have := (abs_le.1 (hdiff k)).2
        have hc := Nat.le_ceil B
        push_cast at hk
        linarith
      · intro h M
        refine (frequently_shift_iff N).2 ((h (M + ⌈B⌉₊)).mono fun k hk => ?_)
        have := (abs_le.1 (hdiff k)).1
        have hc := Nat.le_ceil B
        push_cast at hk
        linarith
    rw [heq]
    exact measurableSet_frequently_nat hym
  have hUm : ∀ M, MeasurableSet (U M) := by
    intro M
    have h : U M = ⋂ n : ℕ, ⋃ k : ℕ, ⋃ (_ : n ≤ k), {ξ | (M : ℝ) < θ * x k ξ} := by
      ext ξ
      simp [hU, frequently_atTop]
    rw [h]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k =>
      MeasurableSet.iUnion fun _ => measurableSet_lt measurable_const (hxm k)
  have hUq : ∀ M, q ≤ Q (U M) := by
    intro M
    obtain ⟨N0, hN0⟩ := hq M
    have h := le_measure_frequently (μ := Q) (A := fun t => {ξ | (M : ℝ) < θ * x (N0 + t) ξ})
      (fun t => measurableSet_lt measurable_const (hxm _))
      (fun t => hN0 (N0 + (t + 2)) (by omega))
    refine h.trans (measure_mono fun ξ hξ => ?_)
    exact (frequently_shift_iff N0).2 hξ
  have hEU : E = ⋂ M, U M := by
    ext ξ
    simp [hE, hU]
  have hEpos : Q E ≠ 0 := by
    have hanti : Antitone U := by
      intro M M' hMM' ξ hξ
      refine hξ.mono fun n hn => ?_
      have : (M : ℝ) ≤ M' := by exact_mod_cast hMM'
      linarith
    have hval := hanti.measure_iInter (fun M => (hUm M).nullMeasurableSet) ⟨0, measure_ne_top Q _⟩
    rw [hEU, hval]
    exact fun h0 => hq0 (nonpos_iff_eq_zero.1 ((le_iInf hUq).trans h0.le))
  have hEm : MeasurableSet E := (limsup_le_iSup.trans (iSup_le blockSigma_le)) _ htail
  have hone : Q E = 1 := by
    rcases measure_zero_or_one_of_measurableSet_limsup_atTop blockSigma_le hindep htail with
      h | h
    · exact absurd h hEpos
    · exact h
  have hae : ∀ᵐ ξ ∂Q, ξ ∈ E := by
    rw [ae_iff]
    have := (prob_compl_eq_zero_iff hEm).2 hone
    simpa [Set.compl_def] using this
  filter_upwards [hae] with ξ hξ M
  refine (hξ ⌈M⌉₊).mono fun n hn => ?_
  have := Nat.le_ceil M
  linarith

/-! ### Moments of debt at `r = g` -/

/-- Cochrane (2023), (6.5), p. 197 (tool): `F_c(x) = ∫_0^x e^{−cv}dv = (1 − e^{−cx})/c`.
Restates `ExpIntegrals.intervalIntegral_exp_neg_mul`. -/
theorem debtF_eq {c : ℝ} (hc : c ≠ 0) (x : ℝ) : debtF c x = (1 - exp (-c * x)) / c := by
  have hd : ∀ y ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt (fun u => -exp (-c * u) / c) (exp (-c * y)) y := fun y _ => by
    have h := (((hasDerivAt_id' y).const_mul (-c)).exp.neg).div_const c
    refine h.congr_deriv ?_
    field_simp
  rw [debtF, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun u => exp (-c * u)).intervalIntegrable 0 x)]
  simp only [mul_zero, exp_zero]
  ring

/-- Cochrane (2023), (6.5), p. 197: at `r = g` the debt kernel is `k_t(u) = e^{−η(t−u)}`. -/
theorem debtKernel_zero {η : ℝ} (hη : η ≠ 0) (t u : ℝ) :
    debtKernel 0 η t u = exp (-η * (t - u)) := by
  have e1 : exp (-(η * t)) * exp (η * u) = exp (-(η * (t - u))) := by
    rw [← exp_add]; ring_nf
  have e2 : exp (-(η * u)) * exp (η * u) = 1 := by rw [← exp_add]; simp
  simp only [debtKernel, zero_mul, exp_zero, one_mul, neg_zero, zero_add, debtF_eq hη]
  field_simp
  linear_combination e1 - e2

/-- Cochrane (2023), (6.5), p. 197: at `r = g`, `G_1(0) = ∫_0^1 e^{−η(1−u)}du > 0`. -/
theorem debtG_zero_pos {η : ℝ} (hη : η ≠ 0) : 0 < debtG 0 η 1 0 := by
  rw [debtG, intervalIntegral.integral_symm, neg_neg]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_debtKernel 0 η 1).intervalIntegrable 0 1) (fun u _ => ?_) one_pos
  rw [debtKernel_zero hη]
  exact exp_pos _

/-- Cochrane (2023), (6.5), p. 197: at `r = g`, `G_t(r) ≥ G_1(0)` for `r ≤ t − 1`. -/
theorem debtG_zero_ge {η : ℝ} (hη : η ≠ 0) {t r : ℝ} (hr : r ≤ t - 1) :
    debtG 0 η 1 0 ≤ debtG 0 η t r := by
  have hc : ∀ x y : ℝ, IntervalIntegrable (debtKernel 0 η t) volume x y :=
    fun x y => (continuous_debtKernel 0 η t).intervalIntegrable x y
  have hs := debtG_shift 0 η 1 0 (t - 1)
  rw [show (1 : ℝ) + (t - 1) = t by ring, zero_add] at hs
  have hdiff : debtG 0 η t r - debtG 0 η t (t - 1)
      = ∫ u in r..(t - 1), debtKernel 0 η t u := by
    simp only [debtG]
    rw [← intervalIntegral.integral_interval_sub_left (hc t (t - 1)) (hc t r)]
    ring
  have hpos : 0 ≤ ∫ u in r..(t - 1), debtKernel 0 η t u :=
    intervalIntegral.integral_nonneg hr fun u _ => by rw [debtKernel_zero hη]; exact (exp_pos _).le
  linarith

/-- **Cochrane (2023), (6.5), p. 197: at `r = g` the debt variance grows without bound**,
`∫_0^t G_t² ≥ (t − 1)G_1(0)²` for `t ≥ 1` (the integral of an AR(1)). -/
theorem integral_debtG_sq_ge {η : ℝ} (hη : η ≠ 0) {t : ℝ} (ht : 1 ≤ t) :
    (t - 1) * debtG 0 η 1 0 ^ 2 ≤ ∫ r in (0 : ℝ)..t, debtG 0 η t r ^ 2 := by
  have hc : ∀ x y : ℝ, IntervalIntegrable (fun r => debtG 0 η t r ^ 2) volume x y :=
    fun x y => ((continuous_debtG 0 η t).pow 2).intervalIntegrable x y
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc 0 (t - 1)) (hc (t - 1) t)]
  have h1 : 0 ≤ ∫ r in (t - 1)..t, debtG 0 η t r ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun r _ => sq_nonneg _
  have h0 : ∫ r in (0 : ℝ)..(t - 1), debtG 0 η 1 0 ^ 2
      ≤ ∫ r in (0 : ℝ)..(t - 1), debtG 0 η t r ^ 2 := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hc 0 (t - 1)) fun r hr => ?_
    have hg := debtG_zero_pos hη
    exact pow_le_pow_left₀ hg.le (debtG_zero_ge hη hr.2) 2
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h0
  linarith

/-- Cochrane (2023), (6.5), p. 197: at `r = g` the mean debt is
`b_0 − s̄t − (s_0 − s̄)∫_0^t e^{−ηu}du`.
`TidyR7OUPath.debtMean` at `a = 0`. -/
theorem debtMean_zero_eq (η sbar s0 b0 t : ℝ) :
    debtMean 0 η sbar s0 b0 t
      = b0 - sbar * t - (s0 - sbar) * ∫ u in (0 : ℝ)..t, exp (-η * u) := by
  have i1 := (intervalIntegrable_const (μ := volume) (a := 0) (b := t) (c := sbar))
  have i2 := (by fun_prop : Continuous fun u => exp (-η * u) * (s0 - sbar)).intervalIntegrable
    (μ := volume) 0 t
  have e : (fun u => exp (-0 * u) * ouMean η sbar s0 u)
      = fun u => sbar + exp (-η * u) * (s0 - sbar) := by
    funext u
    simp [ouMean]
  simp only [debtMean, vocFrom, e]
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const]
  simp only [zero_mul, mul_zero, neg_zero, exp_zero, one_mul, smul_eq_mul, sub_zero]
  ring

/-- Cochrane (2023), (6.5), p. 197: at `r = g` with `s̄ ≤ 0` the mean debt is bounded below,
`debtMean_t ≥ −(|b_0| + |s_0 − s̄|/η)` for `t ≥ 0`. -/
theorem debtMean_zero_ge {η sbar : ℝ} (hη : 0 < η) (hs : sbar ≤ 0) (s0 b0 : ℝ) {t : ℝ}
    (ht : 0 ≤ t) : -(|b0| + |s0 - sbar| / η) ≤ debtMean 0 η sbar s0 b0 t := by
  rw [debtMean_zero_eq]
  obtain ⟨h0, h1⟩ := integral_exp_neg_le hη ht
  have hst : 0 ≤ -(sbar * t) := by nlinarith
  have hd : (s0 - sbar) * ∫ u in (0 : ℝ)..t, exp (-η * u) ≤ |s0 - sbar| / η := by
    calc (s0 - sbar) * ∫ u in (0 : ℝ)..t, exp (-η * u)
        ≤ |s0 - sbar| * ∫ u in (0 : ℝ)..t, exp (-η * u) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |s0 - sbar| * (1 / η) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |s0 - sbar| / η := by ring
  linarith [neg_abs_le b0]

/-- Cochrane (2023), (6.5), p. 197: at `r = g` with `s̄ ≥ 0` the mean debt is bounded above,
`debtMean_t ≤ |b_0| + |s_0 − s̄|/η` for `t ≥ 0`. -/
theorem debtMean_zero_le {η sbar : ℝ} (hη : 0 < η) (hs : 0 ≤ sbar) (s0 b0 : ℝ) {t : ℝ}
    (ht : 0 ≤ t) : debtMean 0 η sbar s0 b0 t ≤ |b0| + |s0 - sbar| / η := by
  rw [debtMean_zero_eq]
  obtain ⟨h0, h1⟩ := integral_exp_neg_le hη ht
  have hst : 0 ≤ sbar * t := mul_nonneg hs ht
  have hd : -(|s0 - sbar| / η) ≤ (s0 - sbar) * ∫ u in (0 : ℝ)..t, exp (-η * u) := by
    have h2 : -(|s0 - sbar| * ∫ u in (0 : ℝ)..t, exp (-η * u))
        ≤ (s0 - sbar) * ∫ u in (0 : ℝ)..t, exp (-η * u) := by
      rw [← neg_mul]
      exact mul_le_mul_of_nonneg_right (neg_abs_le _) h0
    have h3 : |s0 - sbar| * ∫ u in (0 : ℝ)..t, exp (-η * u) ≤ |s0 - sbar| / η := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    linarith
  linarith [le_abs_self b0]

/-! ### Probabilities -/

/-- Cochrane (2023), p. 197 (tool): if `C ≥ 0`, `m ≥ −C` and `√v ≥ |M| + C + 1`, then
`N(m, v)(M, ∞) ≥ N(0, 1)(1, ∞)`.
A variant of `TidyR8OUDebtUnbounded.gaussianReal_Ioi_ge`. -/
theorem gaussianReal_Ioi_ge_one {m C : ℝ} (hC : 0 ≤ C) (hm : -C ≤ m) {v : ℝ≥0} {M : ℝ}
    (hv : |M| + C + 1 ≤ √(v : ℝ)) :
    gaussianReal 0 1 (Set.Ioi 1) ≤ gaussianReal m v (Set.Ioi M) := by
  rw [gaussianReal_eq_map m v, Measure.map_apply (by fun_prop) measurableSet_Ioi]
  refine measure_mono fun x hx => ?_
  simp only [Set.mem_Ioi, Set.mem_preimage] at hx ⊢
  have hs : 0 < √(v : ℝ) := by linarith [abs_nonneg M]
  have h1 : √(v : ℝ) < √(v : ℝ) * x := by nlinarith
  linarith [le_abs_self M]

/-- Cochrane (2023), p. 197 (tool): if `C ≥ 0`, `m ≤ C` and `√v ≥ |M| + C + 1`, then
`N(m, v)(−∞, −M) ≥ N(0, 1)(−∞, −1)`.
A variant of `TidyR8OUDebtUnbounded.gaussianReal_Iio_ge`. -/
theorem gaussianReal_Iio_ge_one {m C : ℝ} (hC : 0 ≤ C) (hm : m ≤ C) {v : ℝ≥0} {M : ℝ}
    (hv : |M| + C + 1 ≤ √(v : ℝ)) :
    gaussianReal 0 1 (Set.Iio (-1)) ≤ gaussianReal m v (Set.Iio (-M)) := by
  rw [gaussianReal_eq_map m v, Measure.map_apply (by fun_prop) measurableSet_Iio]
  refine measure_mono fun x hx => ?_
  simp only [Set.mem_Iio, Set.mem_preimage] at hx ⊢
  have hs : 0 < √(v : ℝ) := by linarith [abs_nonneg M]
  have h1 : √(v : ℝ) * x < -√(v : ℝ) := by nlinarith
  linarith [le_abs_self M]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- Cochrane (2023), (6.5), p. 197: at `r = g` the debt variance exceeds any level at late
dates: `√(debtVar_t) ≥ L` for `t ≥ 1 + L²/(σ²G_1(0)²)`. -/
theorem sqrt_debtVar_zero_ge {η σ : ℝ} (hη : 0 < η) (hσ : σ ≠ 0) (L : ℝ) {t : ℝ}
    (ht : 1 + L ^ 2 / (σ ^ 2 * debtG 0 η 1 0 ^ 2) ≤ t) : L ≤ √(debtVar 0 η σ t : ℝ) := by
  have hg := debtG_zero_pos hη.ne'
  have hd : 0 < σ ^ 2 * debtG 0 η 1 0 ^ 2 := by positivity
  have ht1 : 1 ≤ t := le_trans (by have := div_nonneg (sq_nonneg L) hd.le; linarith) ht
  have hI := integral_debtG_sq_ge hη.ne' ht1
  have hpos : 0 ≤ ∫ r in (0 : ℝ)..t, debtG 0 η t r ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun r _ => sq_nonneg _
  rw [debtVar, Real.coe_toNNReal _ (mul_nonneg (sq_nonneg σ) hpos)]
  refine Real.le_sqrt_of_sq_le ?_
  have h1 : L ^ 2 ≤ (t - 1) * (σ ^ 2 * debtG 0 η 1 0 ^ 2) := by
    rw [← div_le_iff₀ hd]; linarith
  calc L ^ 2 ≤ (t - 1) * (σ ^ 2 * debtG 0 η 1 0 ^ 2) := h1
    _ = σ ^ 2 * ((t - 1) * debtG 0 η 1 0 ^ 2) := by ring
    _ ≤ σ ^ 2 * ∫ r in (0 : ℝ)..t, debtG 0 η t r ^ 2 :=
        mul_le_mul_of_nonneg_left hI (sq_nonneg σ)

/-- **Cochrane (2023), p. 197, at `r = g` with `s̄ ≤ 0`: debt exceeds any level with
probability at least `q = N(0,1)(1, ∞) > 0` at all late dates.** -/
theorem rgEqual_prob_gt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ sbar : ℝ}
    (hη : 0 < η) (hσ : σ ≠ 0) (hs : sbar ≤ 0) (s0 b0 M : ℝ) :
    ∃ T : ℝ, ∀ t, T ≤ t →
      gaussianReal 0 1 (Set.Ioi 1) ≤ P {ω | M < ouDebtProc 0 η sbar s0 σ b0 W t ω} := by
  set C := |b0| + |s0 - sbar| / η
  refine ⟨1 + (|M| + C + 1) ^ 2 / (σ ^ 2 * debtG 0 η 1 0 ^ 2), fun t ht => ?_⟩
  have hg := debtG_zero_pos hη.ne'
  have ht0 : 0 < t := by
    have := div_nonneg (sq_nonneg (|M| + C + 1)) (by positivity : (0 : ℝ) ≤ σ ^ 2
      * debtG 0 η 1 0 ^ 2)
    linarith
  have hm := aemeasurable_ouDebtProc (P := P) hB hW hcont hW0 0 η sbar s0 σ b0 ht0
  have h := Measure.map_apply_of_aemeasurable hm (measurableSet_Ioi (a := M))
  rw [ouDebtProc_hasLaw hB hW hcont hW0 0 η sbar s0 σ b0 ht0] at h
  rw [show {ω | M < ouDebtProc 0 η sbar s0 σ b0 W t ω}
    = ouDebtProc 0 η sbar s0 σ b0 W t ⁻¹' Set.Ioi M from rfl, ← h]
  exact gaussianReal_Ioi_ge_one (by positivity) (debtMean_zero_ge hη hs s0 b0 ht0.le)
    (sqrt_debtVar_zero_ge hη hσ _ ht)

/-- **Cochrane (2023), p. 197, at `r = g` with `s̄ ≥ 0`: debt falls below any level with
probability at least `N(0,1)(−∞, −1) > 0` at all late dates.** -/
theorem rgEqual_prob_lt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ sbar : ℝ}
    (hη : 0 < η) (hσ : σ ≠ 0) (hs : 0 ≤ sbar) (s0 b0 M : ℝ) :
    ∃ T : ℝ, ∀ t, T ≤ t →
      gaussianReal 0 1 (Set.Iio (-1)) ≤ P {ω | ouDebtProc 0 η sbar s0 σ b0 W t ω < -M} := by
  set C := |b0| + |s0 - sbar| / η
  refine ⟨1 + (|M| + C + 1) ^ 2 / (σ ^ 2 * debtG 0 η 1 0 ^ 2), fun t ht => ?_⟩
  have hg := debtG_zero_pos hη.ne'
  have ht0 : 0 < t := by
    have := div_nonneg (sq_nonneg (|M| + C + 1)) (by positivity : (0 : ℝ) ≤ σ ^ 2
      * debtG 0 η 1 0 ^ 2)
    linarith
  have hm := aemeasurable_ouDebtProc (P := P) hB hW hcont hW0 0 η sbar s0 σ b0 ht0
  have h := Measure.map_apply_of_aemeasurable hm (measurableSet_Iio (a := -M))
  rw [ouDebtProc_hasLaw hB hW hcont hW0 0 η sbar s0 σ b0 ht0] at h
  rw [show {ω | ouDebtProc 0 η sbar s0 σ b0 W t ω < -M}
    = ouDebtProc 0 η sbar s0 σ b0 W t ⁻¹' Set.Iio (-M) from rfl, ← h]
  exact gaussianReal_Iio_ge_one (by positivity) (debtMean_zero_le hη hs s0 b0 ht0.le)
    (sqrt_debtVar_zero_ge hη hσ _ ht)

/-- Cochrane (2023), p. 197, at `r = g` (sampled): for `θ = ±1`, if the probability that
`θb_t > M` is at least `q > 0` at all late dates for every `M`, then a.s. `θb_n` exceeds every
level at infinitely many integer dates. -/
theorem rgEqual_sampled_frequently (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ : ℝ} (hη : 0 < η)
    (sbar s0 b0 θ : ℝ) {q : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq : ∀ M : ℝ, ∃ T : ℝ, ∀ t, T ≤ t →
      q ≤ P {ω | M < θ * ouDebtProc 0 η sbar s0 σ b0 W t ω}) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ᶠ n : ℕ in atTop, M < θ * ouDebtProc 0 η sbar s0 σ b0 W n ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set B : Ω → ℕ → Fin 2 → ℝ := fun ω n => ouBlock 0 η σ W n ω with hBdef
  have hBn : ∀ n, AEMeasurable (fun ω => ouBlock 0 η σ W n ω) P := fun n =>
    AEMeasurable.of_eval fun i => aemeasurable_ouBlock hB hW hcont 0 η σ n i
  have hBm : AEMeasurable B P := AEMeasurable.of_eval hBn
  have hind := iIndepFun_ouBlock hB hW hcont 0 η σ
  have hQ : iIndepFun (fun n (ξ : ℕ → Fin 2 → ℝ) => ξ n) (P.map B) := by
    rw [hBdef, hind.map_fun_eq_infinitePi_map₀ hBm]
    exact iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hρ : |exp (-η)| < 1 := by
    rw [abs_of_pos (exp_pos _)]
    exact exp_lt_one_iff.2 (by linarith)
  set x := chainX (exp (-η)) 1 (sbar * debtA 0) (debtD 0 η) (s0 - sbar) b0 with hx
  have hpath : ∀ ω n, x n (B ω) = ouDebtProc 0 η sbar s0 σ b0 W n ω := fun ω n => by
    have := ouDebtProc_sampled_eq_chainX hcont hW0 0 η sbar s0 σ b0 ω n
    rw [exp_zero] at this
    exact this
  have hmain := chain_frequently_of_eventually hQ hρ (sbar * debtA 0) (debtD 0 η) (s0 - sbar) b0
    θ hq0 fun M => by
      obtain ⟨T, hT⟩ := hq M
      refine ⟨⌈T⌉₊, fun n hn => ?_⟩
      rw [Measure.map_apply_of_aemeasurable hBm (measurableSet_lt measurable_const
        ((measurable_chainX _ _ _ _ _ _ n).const_mul θ))]
      refine (hT n ((Nat.le_ceil T).trans (by exact_mod_cast hn))).trans_eq ?_
      congr 1
      ext ω
      change _ ↔ M < θ * x n (B ω)
      rw [hpath]
      exact Iff.rfl
  filter_upwards [ae_of_ae_map hBm hmain] with ω h M
  refine (h M).mono fun n hn => ?_
  change M < θ * x n (B ω) at hn
  rwa [hpath] at hn

/-- **Cochrane (2023), p. 197, at `r = g` with `s̄ ≤ 0`: almost surely debt exceeds every level
at arbitrarily late dates** (`η > 0`, `σ ≠ 0`, every `s_0`, `b_0`). -/
theorem rgEqual_frequently_gt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ sbar : ℝ}
    (hη : 0 < η) (hσ : σ ≠ 0) (hs : sbar ≤ 0) (s0 b0 : ℝ) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ᶠ t in atTop, M < ouDebtProc 0 η sbar s0 σ b0 W t ω := by
  have h := rgEqual_sampled_frequently (σ := σ) hB hW hcont hW0 hη sbar s0 b0 1
    (q := gaussianReal 0 1 (Set.Ioi 1))
    (gaussianReal_open_pos 0 one_ne_zero isOpen_Ioi Set.nonempty_Ioi).ne' fun M => by
      obtain ⟨T, hT⟩ := rgEqual_prob_gt hB hW hcont hW0 hη hσ hs s0 b0 M
      exact ⟨T, fun t ht => (hT t ht).trans_eq (by simp only [one_mul])⟩
  filter_upwards [h] with ω hω M
  exact frequently_real_of_nat (p := fun t => M < ouDebtProc 0 η sbar s0 σ b0 W t ω)
    ((hω M).mono fun n hn => by simpa only [one_mul] using hn)

/-- **Cochrane (2023), p. 197, at `r = g` with `s̄ ≥ 0`: almost surely debt falls below every
level at arbitrarily late dates** (`η > 0`, `σ ≠ 0`, every `s_0`, `b_0`). -/
theorem rgEqual_frequently_lt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ sbar : ℝ}
    (hη : 0 < η) (hσ : σ ≠ 0) (hs : 0 ≤ sbar) (s0 b0 : ℝ) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ᶠ t in atTop, ouDebtProc 0 η sbar s0 σ b0 W t ω < M := by
  have h := rgEqual_sampled_frequently (σ := σ) hB hW hcont hW0 hη sbar s0 b0 (-1)
    (q := gaussianReal 0 1 (Set.Iio (-1)))
    (gaussianReal_open_pos 0 one_ne_zero isOpen_Iio Set.nonempty_Iio).ne' fun M => by
      obtain ⟨T, hT⟩ := rgEqual_prob_lt hB hW hcont hW0 hη hσ hs s0 b0 M
      refine ⟨T, fun t ht => (hT t ht).trans (measure_mono fun ω hω => ?_)⟩
      simp only [Set.mem_ofPred_eq] at hω ⊢
      linarith
  filter_upwards [h] with ω hω M
  exact frequently_real_of_nat (p := fun t => ouDebtProc 0 η sbar s0 σ b0 W t ω < M)
    ((hω (-M)).mono fun n hn => by linarith)

/-- **Cochrane (2023), p. 197, at `r = g` with `s̄ = 0`: almost surely `sup_{t ≥ 0} b_t = +∞`
and `inf_{t ≥ 0} b_t = −∞`.** -/
theorem rgEqual_sup_inf (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ : ℝ}
    (hη : 0 < η) (hσ : σ ≠ 0) (s0 b0 : ℝ) :
    ∀ᵐ ω ∂P, ¬ BddAbove ((fun t => ouDebtProc 0 η 0 s0 σ b0 W t ω) '' Set.Ici 0) ∧
      ¬ BddBelow ((fun t => ouDebtProc 0 η 0 s0 σ b0 W t ω) '' Set.Ici 0) := by
  filter_upwards [rgEqual_frequently_gt hB hW hcont hW0 hη hσ le_rfl s0 b0,
    rgEqual_frequently_lt hB hW hcont hW0 hη hσ le_rfl s0 b0] with ω h1 h2
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨t, ht1, ht2⟩ := ((h1 M).and_eventually (eventually_ge_atTop 0)).exists
    exact absurd (hM ⟨t, ht2, rfl⟩) (not_le.2 ht1)
  · rintro ⟨M, hM⟩
    obtain ⟨t, ht1, ht2⟩ := ((h2 M).and_eventually (eventually_ge_atTop 0)).exists
    exact absurd (hM ⟨t, ht2, rfl⟩) (not_le.2 ht1)

open Cochrane.FiscalConstraints.TidyR7BrownianExist
open Cochrane.FiscalConstraints.TidyR7BrownianSchauder

/-- Cochrane (2023), p. 197 (non-vacuity): on bmPath, with `r = g`, `s̄ = 0` and `η = σ = 1`,
almost surely debt has `sup = +∞` and `inf = −∞`. -/
theorem bmPath_rgEqual_sup_inf (s0 b0 : ℝ) :
    ∀ᵐ ω ∂gaussSeq, ¬ BddAbove ((fun t => ouDebtProc 0 1 0 s0 1 b0 bmPath t ω) '' Set.Ici 0) ∧
      ¬ BddBelow ((fun t => ouDebtProc 0 1 0 s0 1 b0 bmPath t ω) '' Set.Ici 0) :=
  rgEqual_sup_inf isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath bmPath_zero
    one_pos one_ne_zero s0 b0

end Cochrane.FiscalConstraints.TidyR8OUDebtRgEqual
