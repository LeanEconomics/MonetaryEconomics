/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7OrnsteinUhlenbeck
import Mathlib.Probability.Independence.Basic

/-!
# The OU process sampled at integer dates: i.i.d. Gaussian innovations

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197, used here
for Chapter 20, §20.2.2, p. 474 (the Ornstein–Uhlenbeck inflation of the stochastic zero-bound
equilibria). Restated (the innovation part only) from the Cochrane FiscalConstraints project
(module TidyR7OUSampled there; its AR(1) transfer to the product space and the debt results
are not copied). With `ρ = e^{−η}` and `v₁ = σ²(1 − e^{−2η})/(2η)`,

* `ouProc_succ`: `s_{n+1} − s̄ = ρ(s_n − s̄) + ε_{n+1}` path by path, with the innovation
  `ε_{n+1} = σe^{−η(n+1)}∫_n^{n+1} e^{ηu}dW_u` (`ouInnov`, `ouInnov_eq`);
* `ouInnov_hasLaw`: `ε_{n+1} ~ N(0, v₁)`; `covariance_ouInnov`: distinct innovations are
  uncorrelated; `isGaussianProcess_ouInnov`: they are jointly Gaussian;
* **`iIndepFun_ouInnov`**: the innovations are independent.
-/

namespace Cochrane.ZeroBound.TidyR7OUSampled

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7OUPath Cochrane.ZeroBound.TidyR7WienerGaussian
open Cochrane.ZeroBound.TidyR7OrnsteinUhlenbeck
open Cochrane.ZeroBound.TidyR7BrownianTools
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- Cochrane (2023), p. 197: the innovation `ε_{n+1}` of the OU surplus over `[n, n + 1]`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUSampled.ouInnov). -/
noncomputable def ouInnov (η σ : ℝ) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  σ * ouStep η (fun u => bmReal W u ω) n 1

/-- **Cochrane (2023), p. 197: the sampled OU surplus is an AR(1) with `ρ = e^{−η}`**, path by
path: `s_{n+1} − s̄ = e^{−η}(s_n − s̄) + ε_{n+1}`.
`TidyR7OUPath.ouPath_step` at `h = 1`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUSampled.ouProc_succ). -/
theorem ouProc_succ (hcont : ∀ ω, Continuous fun t => W t ω) (η sbar s0 σ : ℝ) (n : ℕ)
    (ω : Ω) :
    ouProc η sbar s0 σ W ((n : ℝ) + 1) ω - sbar
      = exp (-η) * (ouProc η sbar s0 σ W n ω - sbar) + ouInnov η σ W n ω := by
  have h := ouPath_step (η := η) (sbar := sbar) (s0 := s0) (σ := σ)
    (continuous_bmReal (hcont ω)) (n : ℝ) 1
  rw [mul_one] at h
  exact h

/-- Cochrane (2023), p. 197: the innovation is `σe^{−η(n+1)}` times the Wiener integral
`∫_n^{n+1} e^{ηu} dW_u` (by parts), path by path.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUSampled.ouInnov_eq). -/
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
Precisely: `P.map ouInnov = N(0, ouVar η σ 1)`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUSampled.ouInnov_hasLaw). -/
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

/-- Cochrane (2023), p. 197: the innovations are almost everywhere measurable.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUSampled.aemeasurable_ouInnov). -/
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

/-- Cochrane (2023), p. 197: the innovations are square integrable.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUSampled.memLp_ouInnov). -/
theorem memLp_ouInnov (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (η σ : ℝ) (n : ℕ) :
    MemLp (ouInnov η σ W n) 2 P := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlt : (n : ℝ) < n + 1 := by linarith
  rw [ouInnov_eq]
  exact (memLp_wienerBP (P := P) hB hW hcont (hasDerivAt_expMul η)
    (by fun_prop : Continuous fun u => exp (η * u) * η) hn hlt).const_mul _

/-- Cochrane (2023), p. 197: the innovations have mean zero.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUSampled.integral_ouInnov). -/
theorem integral_ouInnov (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {η : ℝ} (hη : 0 < η) (σ : ℝ) (n : ℕ) :
    ∫ ω, ouInnov η σ W n ω ∂P = 0 := by
  calc ∫ ω, ouInnov η σ W n ω ∂P = ∫ x, x ∂(P.map (ouInnov η σ W n)) :=
        (integral_map (aemeasurable_ouInnov hB hW hcont η σ n) aestronglyMeasurable_id).symm
    _ = 0 := by rw [ouInnov_hasLaw hB hW hcont hη σ n, integral_id_gaussianReal]

/-- **Cochrane (2023), p. 197: distinct innovations are uncorrelated.**
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUSampled.covariance_ouInnov). -/
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
`TidyR7WienerGaussian.exists_map_sum_wienerBP`).
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUSampled.isGaussianProcess_ouInnov). -/
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
uncorrelated (`ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_eq_zero`).
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUSampled.iIndepFun_ouInnov). -/
theorem iIndepFun_ouInnov (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {η : ℝ} (hη : 0 < η) (σ : ℝ) :
    iIndepFun (fun n => ouInnov η σ W n) P := by
  have h := IsGaussianProcess.iIndepFun_of_covariance_eq_zero
    (X := fun (n : ℕ) (_ : Unit) ω => ouInnov η σ W n ω)
    (isGaussianProcess_ouInnov hB hW hcont η σ)
    (fun n _ => aemeasurable_ouInnov hB hW hcont η σ n)
    (fun m n hmn _ _ => covariance_ouInnov hB hW hcont hη σ hmn)
  exact h.comp (fun _ f => f ()) (fun _ => measurable_pi_apply ())

end Cochrane.ZeroBound.TidyR7OUSampled
