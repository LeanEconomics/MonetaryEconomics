/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.TidyR7OrnsteinUhlenbeck
import FiscalConstraints.TidyR5GaussianAR1

/-!
# The OU surplus sampled at integer dates is the Gaussian AR(1)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197. The discrete
analogue TidyR5GaussianAR1 of the book's continuous-time AR(1) uses `ρ = e^{−η}`. This module
proves that this is exactly what the continuous-time process gives at integer dates: with
`ρ = e^{−η}` and `v₁ = σ²(1 − e^{−2η})/(2η)`,

* `ouProc_succ`: `s_{n+1} − s̄ = ρ(s_n − s̄) + ε_{n+1}` path by path, with the innovation
  `ε_{n+1} = σe^{−η(n+1)}∫_n^{n+1} e^{ηu}dW_u` (`ouInnov`, `ouInnov_eq`);
* `ouInnov_hasLaw`: `ε_{n+1} ~ N(0, v₁)`; `covariance_ouInnov`: distinct innovations are
  uncorrelated; `isGaussianProcess_ouInnov`: they are jointly Gaussian;
* **`iIndepFun_ouInnov`, `map_ouInnov`**: the innovations are i.i.d. `N(0, v₁)` — their joint
  law is the product measure `(iidSystem (gaussianProb 0 v₁)).μ` of TidyR5GaussianAR1;
* **`ouProc_succ_eq_ar1`, `map_ouProc_sampled`**: `s_{n+1} = s̄ + ρ^{n+1}(s_0 − s̄) + u_n(ε)`
  with `u = ExpectationsMeasureIID.ar1 ρ`, so the sampled path has the law of the discrete
  Gaussian AR(1) (plus the deterministic transient); `arVar_eq_ouVar` checks the variances;
* **`sampled_debt_unbounded`, `sampled_debt_not_sustainable`**: with these surpluses and
  `0 ≤ γ < 1` (permanent `r < g`), almost surely the discrete debt-to-GDP ratio exceeds every
  level infinitely often, from every initial debt and every `s_0`; no debt limit is sustainable.
* Non-vacuity on bmPath: `bmPath_map_ouInnov`, `bmPath_sampled_debt_unbounded`.
-/

namespace Cochrane.FiscalConstraints.TidyR7OUSampled

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.FiscalConstraints.TidyR7OUPath Cochrane.FiscalConstraints.TidyR7WienerGaussian
open Cochrane.FiscalConstraints.TidyR7OrnsteinUhlenbeck
open Cochrane.FiscalConstraints.TidyR7BrownianTools
open Cochrane.FiscalConstraints.ExpectationsMeasureIID
open Cochrane.FiscalConstraints.DebtLimitStochastic
open Cochrane.FiscalConstraints.LognormalGrowthMeasure Cochrane.FiscalConstraints.TidyR5GaussianAR1
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- Cochrane (2023), p. 197: the innovation `ε_{n+1}` of the OU surplus over `[n, n + 1]`. -/
noncomputable def ouInnov (η σ : ℝ) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  σ * ouStep η (fun u => bmReal W u ω) n 1

/-- **Cochrane (2023), p. 197: the sampled OU surplus is an AR(1) with `ρ = e^{−η}`**, path by
path: `s_{n+1} − s̄ = e^{−η}(s_n − s̄) + ε_{n+1}`.
`TidyR7OUPath.ouPath_step` at `h = 1`. -/
theorem ouProc_succ (hcont : ∀ ω, Continuous fun t => W t ω) (η sbar s0 σ : ℝ) (n : ℕ)
    (ω : Ω) :
    ouProc η sbar s0 σ W ((n : ℝ) + 1) ω - sbar
      = exp (-η) * (ouProc η sbar s0 σ W n ω - sbar) + ouInnov η σ W n ω := by
  have h := ouPath_step (η := η) (sbar := sbar) (s0 := s0) (σ := σ)
    (continuous_bmReal (hcont ω)) (n : ℝ) 1
  rw [mul_one] at h
  exact h

/-- Cochrane (2023), p. 197: the innovation is `σe^{−η(n+1)}` times the Wiener integral
`∫_n^{n+1} e^{ηu} dW_u` (by parts), path by path. -/
theorem ouInnov_eq (η σ : ℝ) (n : ℕ) :
    ouInnov η σ W n = fun ω => σ * exp (-η * ((n : ℝ) + 1))
      * wienerBP W (fun u => exp (η * u)) (fun u => exp (η * u) * η) n ((n : ℝ) + 1) ω := by
  funext ω
  have hint : (∫ u in (n : ℝ)..((n : ℝ) + 1), bmReal W u ω * (exp (η * u) * η))
      = η * ∫ u in (n : ℝ)..((n : ℝ) + 1), exp (η * u) * bmReal W u ω := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    ring
  have e1 : exp (-η * ((n : ℝ) + 1)) * exp (η * ((n : ℝ) + 1)) = 1 := by
    rw [← exp_add]; ring_nf; exact exp_zero
  have e2 : exp (-η * ((n : ℝ) + 1)) * exp (η * n) = exp (-η) := by
    rw [← exp_add]; ring_nf
  simp only [ouInnov, ouStep, wienerBP, hint, mul_one]
  linear_combination (-(σ * bmReal W ((n : ℝ) + 1) ω)) * e1 + (σ * bmReal W n ω) * e2

/-- Cochrane (2023), p. 197: the one-period innovation variance
`v₁ = σ²(1 − e^{−2η})/(2η)` is `ouVar η σ 1`.
Precisely: `P.map ouInnov = N(0, ouVar η σ 1)`. -/
theorem ouInnov_hasLaw (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {η : ℝ} (hη : 0 < η) (σ : ℝ) (n : ℕ) :
    P.map (ouInnov η σ W n) = gaussianReal 0 (ouVar η σ 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlt : (n : ℝ) < n + 1 := by linarith
  have hY := (memLp_wienerBP (P := P) hB hW hcont (hasDerivAt_expMul η)
    (by fun_prop : Continuous fun u => exp (η * u) * η) hn hlt).aestronglyMeasurable
    |>.aemeasurable
  have hlaw := map_wienerBP (P := P) hB hW hcont (hasDerivAt_expMul η)
    (by fun_prop : Continuous fun u => exp (η * u) * η) hn hlt
  have h := map_affine_gaussian hY hlaw 0 (σ * exp (-η * ((n : ℝ) + 1)))
  simp only [zero_add] at h
  rw [ouInnov_eq, h]
  congr 1
  have hI := integral_exp_sq hη.ne' (n : ℝ) ((n : ℝ) + 1)
  have hpos : 0 ≤ ∫ u in (n : ℝ)..((n : ℝ) + 1), exp (η * u) ^ 2 :=
    intervalIntegral.integral_nonneg hlt.le fun u _ => sq_nonneg _
  have hv : 0 ≤ σ ^ 2 * (1 - exp (-2 * η * 1)) / (2 * η) := by
    have : exp (-2 * η * 1) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
    exact div_nonneg (mul_nonneg (sq_nonneg σ) (by linarith)) (by positivity)
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hpos, ouVar, Real.coe_toNNReal _ hv, hI]
  have e1 : exp (-η * ((n : ℝ) + 1)) ^ 2 * exp (2 * η * ((n : ℝ) + 1)) = 1 := by
    rw [sq, ← exp_add, ← exp_add]; ring_nf; exact exp_zero
  have e2 : exp (-η * ((n : ℝ) + 1)) ^ 2 * exp (2 * η * n) = exp (-2 * η * 1) := by
    rw [sq, ← exp_add, ← exp_add]; ring_nf
  rw [mul_pow]
  have e3 : σ ^ 2 * exp (-η * ((n : ℝ) + 1)) ^ 2
      * ((exp (2 * η * ((n : ℝ) + 1)) - exp (2 * η * n)) / (2 * η))
      = σ ^ 2 * (exp (-η * ((n : ℝ) + 1)) ^ 2 * exp (2 * η * ((n : ℝ) + 1))
        - exp (-η * ((n : ℝ) + 1)) ^ 2 * exp (2 * η * n)) / (2 * η) := by ring
  rw [e3, e1, e2]

/-- Cochrane (2023), p. 197: the innovations are almost everywhere measurable. -/
theorem aemeasurable_ouInnov (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (η σ : ℝ) (n : ℕ) :
    AEMeasurable (ouInnov η σ W n) P := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlt : (n : ℝ) < n + 1 := by linarith
  have := (memLp_wienerBP (P := P) hB hW hcont (hasDerivAt_expMul η)
    (by fun_prop : Continuous fun u => exp (η * u) * η) hn hlt).aestronglyMeasurable
    |>.aemeasurable
  rw [ouInnov_eq]
  fun_prop

/-- Cochrane (2023), p. 197: the innovations are square integrable. -/
theorem memLp_ouInnov (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (η σ : ℝ) (n : ℕ) :
    MemLp (ouInnov η σ W n) 2 P := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlt : (n : ℝ) < n + 1 := by linarith
  rw [ouInnov_eq]
  exact (memLp_wienerBP (P := P) hB hW hcont (hasDerivAt_expMul η)
    (by fun_prop : Continuous fun u => exp (η * u) * η) hn hlt).const_mul _

/-- Cochrane (2023), p. 197: the innovations have mean zero. -/
theorem integral_ouInnov (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {η : ℝ} (hη : 0 < η) (σ : ℝ) (n : ℕ) :
    ∫ ω, ouInnov η σ W n ω ∂P = 0 := by
  calc ∫ ω, ouInnov η σ W n ω ∂P = ∫ x, x ∂(P.map (ouInnov η σ W n)) :=
        (integral_map (aemeasurable_ouInnov hB hW hcont η σ n) aestronglyMeasurable_id).symm
    _ = 0 := by rw [ouInnov_hasLaw hB hW hcont hη σ n, integral_id_gaussianReal]

/-- **Cochrane (2023), p. 197: distinct innovations are uncorrelated.** -/
theorem covariance_ouInnov (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {η : ℝ} (hη : 0 < η) (σ : ℝ) {m n : ℕ}
    (hmn : m ≠ n) : cov[ouInnov η σ W m, ouInnov η σ W n; P] = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have key : ∀ m n : ℕ, m < n → ∫ ω, ouInnov η σ W m ω * ouInnov η σ W n ω ∂P = 0 := by
    intro m n hlt
    have h0 := integral_mul_wienerBP_eq_zero (P := P) hB hW hcont (hasDerivAt_expMul η)
      (by fun_prop : Continuous fun u => exp (η * u) * η) (hasDerivAt_expMul η)
      (by fun_prop : Continuous fun u => exp (η * u) * η) (Nat.cast_nonneg m)
      (by linarith : (m : ℝ) < m + 1) (by exact_mod_cast hlt : (m : ℝ) + 1 ≤ n)
      (by linarith : (n : ℝ) < n + 1)
    rw [ouInnov_eq, ouInnov_eq]
    simp only
    have e : ∀ ω, σ * exp (-η * ((m : ℝ) + 1))
        * wienerBP W (fun u => exp (η * u)) (fun u => exp (η * u) * η) m ((m : ℝ) + 1) ω
        * (σ * exp (-η * ((n : ℝ) + 1))
          * wienerBP W (fun u => exp (η * u)) (fun u => exp (η * u) * η) n ((n : ℝ) + 1) ω)
        = (σ * exp (-η * ((m : ℝ) + 1)) * (σ * exp (-η * ((n : ℝ) + 1))))
          * (wienerBP W (fun u => exp (η * u)) (fun u => exp (η * u) * η) m ((m : ℝ) + 1) ω
          * wienerBP W (fun u => exp (η * u)) (fun u => exp (η * u) * η) n ((n : ℝ) + 1) ω) :=
      fun ω => by ring
    simp_rw [e]
    rw [integral_const_mul, h0, mul_zero]
  rw [covariance_eq_sub (memLp_ouInnov hB hW hcont η σ m) (memLp_ouInnov hB hW hcont η σ n),
    integral_ouInnov hB hW hcont hη σ m, integral_ouInnov hB hW hcont hη σ n, mul_zero, sub_zero]
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · exact key m n hlt
  · have := key n m hlt
    simp_rw [mul_comm (ouInnov η σ W n _)] at this
    exact this

/-- **Cochrane (2023), p. 197: the innovations are jointly Gaussian** (every finite linear
combination is a linear combination of Wiener integrals,
`TidyR7WienerGaussian.exists_map_sum_wienerBP`). -/
theorem isGaussianProcess_ouInnov (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (η σ : ℝ) :
    IsGaussianProcess (fun (p : (_ : ℕ) × Unit) ω => ouInnov η σ W p.1 ω) P where
  hasGaussianLaw I := by
    have hV : AEMeasurable (fun ω => I.restrict (fun p : (_ : ℕ) × Unit => ouInnov η σ W p.1 ω))
        P := AEMeasurable.of_eval fun i => aemeasurable_ouInnov hB hW hcont η σ i.1.1
    refine ⟨hV, isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hV]
    set d : I → ℝ := fun i => L (fun j => if i = j then 1 else 0)
      * (σ * exp (-η * (((i : (_ : ℕ) × Unit).1 : ℝ) + 1)))
    obtain ⟨v, hv⟩ := exists_map_sum_wienerBP (P := P) hB hW hcont Finset.univ d
      (h := fun _ => fun u => exp (η * u)) (h' := fun _ => fun u => exp (η * u) * η)
      (fun _ => hasDerivAt_expMul η) (fun _ => by fun_prop)
      (s := fun i => ((i : (_ : ℕ) × Unit).1 : ℝ)) (t := fun i => ((i : (_ : ℕ) × Unit).1 : ℝ) + 1)
      (fun _ => by linarith)
    refine ⟨0, v, ?_⟩
    rw [← hv]
    congr 1
    funext ω
    simp only [Function.comp_apply]
    rw [show L (I.restrict fun p : (_ : ℕ) × Unit => ouInnov η σ W p.1 ω)
      = L.toLinearMap (I.restrict fun p : (_ : ℕ) × Unit => ouInnov η σ W p.1 ω) from rfl,
      LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.restrict, smul_eq_mul, d, ouInnov_eq, ContinuousLinearMap.coe_coe]
    ring

/-- **Cochrane (2023), p. 197: the innovations are independent.** Jointly Gaussian and
uncorrelated (`ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_eq_zero`). -/
theorem iIndepFun_ouInnov (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {η : ℝ} (hη : 0 < η) (σ : ℝ) :
    iIndepFun (fun n => ouInnov η σ W n) P := by
  have h := IsGaussianProcess.iIndepFun_of_covariance_eq_zero
    (X := fun (n : ℕ) (_ : Unit) ω => ouInnov η σ W n ω)
    (isGaussianProcess_ouInnov hB hW hcont η σ)
    (fun n _ => aemeasurable_ouInnov hB hW hcont η σ n)
    (fun m n hmn _ _ => covariance_ouInnov hB hW hcont hη σ hmn)
  exact h.comp (fun _ f => f ()) (fun _ => measurable_pi_apply ())

/-- **Cochrane (2023), p. 197: the innovations are i.i.d. `N(0, σ²(1 − e^{−2η})/(2η))`**: their
joint law is the product measure of TidyR5GaussianAR1. -/
theorem map_ouInnov (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {η : ℝ} (hη : 0 < η) (σ : ℝ) :
    P.map (fun ω n => ouInnov η σ W n ω) = (iidSystem (gaussianProb 0 (ouVar η σ 1))).μ := by
  have hE : AEMeasurable (fun ω n => ouInnov η σ W n ω) P :=
    AEMeasurable.of_eval fun n => aemeasurable_ouInnov hB hW hcont η σ n
  rw [(iIndepFun_ouInnov hB hW hcont hη σ).map_fun_eq_infinitePi_map₀ hE]
  simp_rw [ouInnov_hasLaw hB hW hcont hη σ]
  rfl

/-- **Cochrane (2023), p. 197: the sampled OU surplus in AR(1) form**:
`s_{n+1} = s̄ + ρ^{n+1}(s_0 − s̄) + u_n(ε)` with `ρ = e^{−η}`, `u = ar1 ρ` and `ε_k = ouInnov k`. -/
theorem ouProc_succ_eq_ar1 (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    (η sbar s0 σ : ℝ) (n : ℕ) (ω : Ω) :
    ouProc η sbar s0 σ W ((n : ℝ) + 1) ω
      = sbar + exp (-η) ^ (n + 1) * (s0 - sbar)
        + ar1 (exp (-η)) n (fun k => ouInnov η σ W k ω) := by
  induction n with
  | zero =>
    have h := ouProc_succ hcont η sbar s0 σ 0 ω
    simp only [Nat.cast_zero, zero_add, ouProc_zero hW0] at h
    simp only [Nat.cast_zero, zero_add, pow_one]
    rw [show ar1 (exp (-η)) 0 (fun k => ouInnov η σ W k ω) = ouInnov η σ W 0 ω from rfl]
    linarith
  | succ n ih =>
    have h := ouProc_succ hcont η sbar s0 σ (n + 1) ω
    push_cast at h ⊢
    rw [ih] at h
    rw [ar1_succ_apply, pow_succ]
    linear_combination h

/-- **Cochrane (2023), p. 197: the law of the sampled OU surplus.** The process
`n ↦ s_{n+1}` has the law of `s̄ + ρ^{n+1}(s_0 − s̄) + u_n` under the i.i.d. Gaussian product
measure of TidyR5GaussianAR1 (`ρ = e^{−η}`, innovation variance `σ²(1 − e^{−2η})/(2η)`). -/
theorem map_ouProc_sampled (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η : ℝ} (hη : 0 < η)
    (sbar s0 σ : ℝ) :
    P.map (fun ω (n : ℕ) => ouProc η sbar s0 σ W ((n : ℝ) + 1) ω)
      = (iidSystem (gaussianProb 0 (ouVar η σ 1))).μ.map
          (fun e n => sbar + exp (-η) ^ (n + 1) * (s0 - sbar) + ar1 (exp (-η)) n e) := by
  have hE : AEMeasurable (fun ω n => ouInnov η σ W n ω) P :=
    AEMeasurable.of_eval fun n => aemeasurable_ouInnov hB hW hcont η σ n
  have hG : Measurable fun (e : ℕ → ℝ) (n : ℕ) =>
      sbar + exp (-η) ^ (n + 1) * (s0 - sbar) + ar1 (exp (-η)) n e :=
    Measurable.of_eval fun n => (measurable_ar1 (exp (-η)) n).const_add _
  rw [← map_ouInnov hB hW hcont hη σ, AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hE]
  congr 1
  funext ω n
  exact ouProc_succ_eq_ar1 hcont hW0 η sbar s0 σ n ω

/-- Cochrane (2023), p. 197 (consistency check): the discrete AR(1) variance
`v₁ ∑_{j ≤ n} ρ^{2j}` of `TidyR5GaussianAR1.arVar` equals the continuous-time variance
`σ²(1 − e^{−2η(n+1)})/(2η)` at date `n + 1`. -/
theorem arVar_eq_ouVar {η : ℝ} (hη : 0 < η) (σ : ℝ) (n : ℕ) :
    arVar (exp (-η)) (ouVar η σ 1) n = ouVar η σ ((n : ℝ) + 1) := by
  have hq : exp (-2 * η) ≠ 1 := (exp_lt_one_iff.2 (by linarith)).ne
  have hq1 : exp (-2 * η) < 1 := exp_lt_one_iff.2 (by linarith)
  have hv1 : 0 ≤ σ ^ 2 * (1 - exp (-2 * η * 1)) / (2 * η) := by
    rw [mul_one]
    exact div_nonneg (mul_nonneg (sq_nonneg σ) (by linarith)) (by positivity)
  have hvn : 0 ≤ σ ^ 2 * (1 - exp (-2 * η * ((n : ℝ) + 1))) / (2 * η) := by
    have : exp (-2 * η * ((n : ℝ) + 1)) ≤ 1 :=
      exp_le_one_iff.2 (by have := Nat.cast_nonneg (α := ℝ) n; nlinarith)
    exact div_nonneg (mul_nonneg (sq_nonneg σ) (by linarith)) (by positivity)
  apply NNReal.eq
  have hr : ((rho2 (exp (-η)) : ℝ≥0) : ℝ) = exp (-2 * η) := by
    change exp (-η) ^ 2 = exp (-2 * η)
    rw [sq, ← exp_add]
    ring_nf
  simp only [arVar, NNReal.coe_mul, NNReal.coe_sum, NNReal.coe_pow, hr, ouVar,
    Real.coe_toNNReal _ hv1, Real.coe_toNNReal _ hvn]
  rw [geom_sum_eq hq, ← exp_nat_mul]
  have e : ((n + 1 : ℕ) : ℝ) * (-2 * η) = -2 * η * ((n : ℝ) + 1) := by push_cast; ring
  rw [e, mul_one]
  have hd : exp (-2 * η) - 1 ≠ 0 := sub_ne_zero.2 hq
  have key : (1 - exp (-2 * η)) * ((exp (-2 * η * ((n : ℝ) + 1)) - 1) / (exp (-2 * η) - 1))
      = 1 - exp (-2 * η * ((n : ℝ) + 1)) := by
    rw [show 1 - exp (-2 * η) = -(exp (-2 * η) - 1) by ring, neg_mul, mul_div_assoc',
      mul_div_cancel_left₀ _ hd]
    ring
  rw [show σ ^ 2 * (1 - exp (-2 * η)) / (2 * η)
      * ((exp (-2 * η * ((n : ℝ) + 1)) - 1) / (exp (-2 * η) - 1))
      = σ ^ 2 * ((1 - exp (-2 * η)) * ((exp (-2 * η * ((n : ℝ) + 1)) - 1)
        / (exp (-2 * η) - 1))) / (2 * η) by ring, key]

/-! ### The discrete debt limit with sampled OU surpluses -/

/-- Cochrane (2023), (6.4) p. 196 (tool): debt paths whose surpluses differ by at most `K` at
every date differ by at most `K/(1 − γ)`, for `0 ≤ γ < 1`. -/
theorem abs_debtPath_sub_le {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (x₀ : ℝ) {σ σ' : ℕ → Ω → ℝ}
    {K : ℝ} (hK : ∀ n ω, |σ' n ω - σ n ω| ≤ K) (n : ℕ) (ω : Ω) :
    |debtPath γ x₀ σ' n ω - debtPath γ x₀ σ n ω| ≤ K / (1 - γ) := by
  have h1 : 0 < 1 - γ := by linarith
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ω)
  induction n with
  | zero =>
    have : debtPath γ x₀ σ' 0 ω - debtPath γ x₀ σ 0 ω = 0 := sub_self x₀
    rw [this, abs_zero]
    positivity
  | succ n ih =>
    rw [debtPath_succ, debtPath_succ]
    have e : γ * debtPath γ x₀ σ' n ω - σ' n ω - (γ * debtPath γ x₀ σ n ω - σ n ω)
        = γ * (debtPath γ x₀ σ' n ω - debtPath γ x₀ σ n ω) - (σ' n ω - σ n ω) := by ring
    rw [e]
    calc |γ * (debtPath γ x₀ σ' n ω - debtPath γ x₀ σ n ω) - (σ' n ω - σ n ω)|
        ≤ γ * |debtPath γ x₀ σ' n ω - debtPath γ x₀ σ n ω| + |σ' n ω - σ n ω| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hγ0]
      _ ≤ γ * (K / (1 - γ)) + K := add_le_add (mul_le_mul_of_nonneg_left ih hγ0) (hK n ω)
      _ = K / (1 - γ) := by field_simp; ring

/-- **Cochrane (2023), p. 197 ("the future debt-to-GDP ratio ... will eventually exceed any
bound"), sampled OU surpluses.** With the OU surplus (`η > 0`, `σ ≠ 0`) paid at integer dates,
`σ_n = s_{n+1}`, and debt `x_{n+1} = γx_n − σ_n`, `0 ≤ γ < 1` (permanent `r < g`), almost
surely debt exceeds every level infinitely often, for every initial debt and every `s_0`.
Transfers `TidyR5GaussianAR1.gaussian_ar1_exp_unbounded` through `map_ouInnov`. -/
theorem sampled_debt_unbounded (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ γ : ℝ} (hη : 0 < η)
    (hσ : σ ≠ 0) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (x₀ sbar s0 : ℝ) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ᶠ n in atTop,
      M < debtPath γ x₀ (fun n ω => ouProc η sbar s0 σ W ((n : ℝ) + 1) ω) n ω := by
  have hE : AEMeasurable (fun ω n => ouInnov η σ W n ω) P :=
    AEMeasurable.of_eval fun n => aemeasurable_ouInnov hB hW hcont η σ n
  have hv : ouVar η σ 1 ≠ 0 := ouVar_ne_zero hη hσ one_pos
  have hiid := gaussian_ar1_exp_unbounded hv hη hγ0 hγ1 x₀ sbar
  rw [← map_ouInnov hB hW hcont hη σ] at hiid
  have hP := ae_of_ae_map hE hiid
  set K := |s0 - sbar|
  have hρ : 0 ≤ exp (-η) ∧ exp (-η) ≤ 1 := ⟨(exp_pos _).le, exp_le_one_iff.2 (by linarith)⟩
  have hK : ∀ (n : ℕ) (ω : Ω), |ouProc η sbar s0 σ W ((n : ℝ) + 1) ω
      - arSurplus (exp (-η)) sbar n (fun k => ouInnov η σ W k ω)| ≤ K := by
    intro n ω
    rw [ouProc_succ_eq_ar1 hcont hW0, arSurplus]
    have e : sbar + exp (-η) ^ (n + 1) * (s0 - sbar)
        + ar1 (exp (-η)) n (fun k => ouInnov η σ W k ω)
        - (sbar + ar1 (exp (-η)) n fun k => ouInnov η σ W k ω)
        = exp (-η) ^ (n + 1) * (s0 - sbar) := by ring
    rw [e, abs_mul, abs_of_nonneg (pow_nonneg hρ.1 _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hρ.1 hρ.2)
  filter_upwards [hP] with ω hω M
  refine (hω (M + K / (1 - γ))).mono fun n hn => ?_
  have hb := abs_debtPath_sub_le hγ0 hγ1 x₀
    (σ := fun n ω => arSurplus (exp (-η)) sbar n (fun k => ouInnov η σ W k ω))
    (σ' := fun n ω => ouProc η sbar s0 σ W ((n : ℝ) + 1) ω) hK n ω
  have e : debtPath γ x₀ (fun n ω => arSurplus (exp (-η)) sbar n (fun k => ouInnov η σ W k ω)) n ω
      = debtPath γ x₀ (arSurplus (exp (-η)) sbar) n (fun k => ouInnov η σ W k ω) := rfl
  rw [e] at hb
  linarith [(abs_le.1 hb).1]

/-- **Cochrane (2023), p. 197 ("the initial value of debt ... is not sustainable"), sampled OU
surpluses**: for every debt limit `M`, the event that debt stays at or below `M` forever has
probability zero.
The sampled-OU analogue of `TidyR5GaussianAR1.gaussian_ar1_not_sustainable`. -/
theorem sampled_debt_not_sustainable (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ γ : ℝ} (hη : 0 < η)
    (hσ : σ ≠ 0) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (x₀ sbar s0 M : ℝ) :
    P {ω | ∀ n, debtPath γ x₀ (fun n ω => ouProc η sbar s0 σ W ((n : ℝ) + 1) ω) n ω ≤ M}
      = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [sampled_debt_unbounded hB hW hcont hW0 hη hσ hγ0 hγ1 x₀ sbar s0] with ω hω hall
  obtain ⟨n, hn⟩ := (hω M).exists
  exact absurd (hall n) (not_le.mpr hn)

/-! ### Non-vacuity on the constructed Brownian motion -/

open Cochrane.FiscalConstraints.TidyR7BrownianExist
open Cochrane.FiscalConstraints.TidyR7BrownianSchauder

/-- Cochrane (2023), p. 197 (non-vacuity): on bmPath, the OU innovations are i.i.d.
`N(0, σ²(1 − e^{−2η})/(2η))`. -/
theorem bmPath_map_ouInnov {η : ℝ} (hη : 0 < η) (σ : ℝ) :
    gaussSeq.map (fun ω n => ouInnov η σ bmPath n ω)
      = (iidSystem (gaussianProb 0 (ouVar η σ 1))).μ :=
  map_ouInnov isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath hη σ

/-- Cochrane (2023), p. 197 (non-vacuity): on bmPath, with `η = σ = 1` and `γ = 0.99`, the
discrete debt with sampled OU surpluses is almost surely unbounded above. -/
theorem bmPath_sampled_debt_unbounded (x₀ sbar s0 : ℝ) :
    ∀ᵐ ω ∂gaussSeq, ∀ M : ℝ, ∃ᶠ n in atTop,
      M < debtPath (99 / 100) x₀ (fun n ω => ouProc 1 sbar s0 1 bmPath ((n : ℝ) + 1) ω) n ω :=
  sampled_debt_unbounded isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath bmPath_zero
    one_pos one_ne_zero (by norm_num) (by norm_num) x₀ sbar s0

end Cochrane.FiscalConstraints.TidyR7OUSampled
