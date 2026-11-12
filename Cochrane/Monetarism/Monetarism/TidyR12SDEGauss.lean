/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR12SDEExist
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Gaussian moments of Brownian increments for geometric Brownian motion

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.32)–(1.34) (Track 3, chunk B4). The positive stochastic
discount factor `Λ/P = n₀e^{−it}exp(σW_t − σ²t/2)` (constant `i` and `σ`) is a geometric
Brownian motion. To show that it
solves `dn = −i n dt + σ n dW` (`TidyR12SDEGBM`) one needs, for a Brownian increment
`Z = W_b − W_a` (`h = b − a`), the moments `E[e^{cZ}] = e^{c²h/2}` and `E[Ze^{cZ}] = ch e^{c²h/2}`,
and the small-`h` behaviour of the left-point remainder
`R = e^{κh + σZ} − 1 − mh − σZ`, `m = κ + σ²/2`: `E[R] = o(h)` and `E[R²] = o(h)`.

## Main results

* `mgf_incr`, `integral_exp_mul_incr`, `integrable_exp_mul_incr`, `integral_incr_mul_exp`
  (`E[Ze^{cZ}] = ch e^{c²h/2}`, from Mathlib `hasDerivAt_mgf` and `mgf_gaussianReal`).
* `integrable_mul_fun_incr`, `integral_mul_fun_incr`, `memLp_mul_fun_incr`: products of an
  `𝓕_a`-measurable variable with a function of the increment over `[a, b]` (independence).
* `gbmRem`, `integral_gbmRem`, `integral_gbmRem_sq`, `memLp_gbmRem`: the remainder and its first
  two moments in closed form; `gbmMean_littleO`, `gbmSq_littleO`: both are `o(h)`.
* `integral_exp_incr_sub_one_sq`: `E[(e^{κh+σZ} − 1)²] = e^{(2κ+2σ²)h} − 2e^{mh} + 1`.
-/

namespace Cochrane.Monetarism.TidyR12SDEGauss

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7BrownianTools Cochrane.Monetarism.TidyR7BrownianQV
  Cochrane.Monetarism.TidyR7ItoSums
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-! ## Moments of an increment -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the moment generating function of a Brownian
increment**, `E[e^{cZ}] = e^{(b − a)c²/2}` for `Z = W_b − W_a`, `0 ≤ a ≤ b`. -/
theorem mgf_incr (hB : IsPreBrownianReal W P) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (c : ℝ) :
    mgf (incr W a b) P c = Real.exp ((b - a) * c ^ 2 / 2) := by
  have h := mgf_gaussianReal (hB.hasLaw_sub b.toNNReal a.toNNReal) c
  have e : incr W a b = W b.toNNReal - W a.toNNReal := rfl
  rw [e, h]
  congr 1
  have h2 := abs_toNNReal_sub ha hab
  rw [coe_nndist, Real.dist_eq]
  change 0 * c + |((b.toNNReal : ℝ≥0) : ℝ) - ((a.toNNReal : ℝ≥0) : ℝ)| * c ^ 2 / 2 = _
  rw [h2]
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `E[e^{cZ}] = e^{(b − a)c²/2}` as an integral. -/
theorem integral_exp_mul_incr (hB : IsPreBrownianReal W P) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (c : ℝ) :
    ∫ ω, Real.exp (c * incr W a b ω) ∂P = Real.exp ((b - a) * c ^ 2 / 2) :=
  mgf_incr hB ha hab c

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `e^{cZ}` is integrable for every `c`. -/
theorem integrable_exp_mul_incr (hB : IsPreBrownianReal W P) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (c : ℝ) : Integrable (fun ω => Real.exp (c * incr W a b ω)) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [← mgf_pos_iff, mgf_incr hB ha hab c]
  exact Real.exp_pos _

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E[Ze^{cZ}] = c(b − a)e^{(b − a)c²/2}`** for a
Brownian increment `Z = W_b − W_a`, `0 ≤ a ≤ b` (the derivative of the moment generating
function, Mathlib `hasDerivAt_mgf`). -/
theorem integral_incr_mul_exp (hB : IsPreBrownianReal W P) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (c : ℝ) :
    ∫ ω, incr W a b ω * Real.exp (c * incr W a b ω) ∂P
      = c * (b - a) * Real.exp ((b - a) * c ^ 2 / 2) := by
  have hset : integrableExpSet (incr W a b) P = Set.univ :=
    Set.eq_univ_of_forall fun c => integrable_exp_mul_incr hB ha hab c
  have h1 := hasDerivAt_mgf (X := incr W a b) (μ := P) (t := c) (by simp [hset])
  have e : mgf (incr W a b) P = fun c => Real.exp ((b - a) * c ^ 2 / 2) :=
    funext fun c => mgf_incr hB ha hab c
  rw [e] at h1
  have h2 : HasDerivAt (fun c => Real.exp ((b - a) * c ^ 2 / 2))
      (Real.exp ((b - a) * c ^ 2 / 2) * ((b - a) * (2 * c) / 2)) c := by
    have h3 : HasDerivAt (fun c : ℝ => (b - a) * c ^ 2 / 2) ((b - a) * (2 * c) / 2) c := by
      have := ((hasDerivAt_pow 2 c).const_mul (b - a)).div_const 2
      simpa using this
    exact h3.exp
  have := h1.unique h2
  rw [this]
  ring

/-! ## Products with functions of the increment -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `a ≤ b`, an `𝓕_a`-strongly measurable `Q` and a
measurable `φ` are independent through the increment: `E[Q φ(Z)] = E[Q]E[φ(Z)]`. -/
theorem integral_mul_fun_incr (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    {a b : ℝ} (hab : a ≤ b) {Q : Ω → ℝ} (hQ : StronglyMeasurable[𝓕 a] Q) {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    ∫ ω, Q ω * φ (incr W a b ω) ∂P = (∫ ω, Q ω ∂P) * ∫ ω, φ (incr W a b ω) ∂P := by
  have hI : IndepFun Q (fun ω => φ (incr W a b ω)) P :=
    ((indepFun_incr h𝓕 hab hQ).comp (φ := φ) (ψ := id) hφ measurable_id).symm
  exact hI.integral_fun_mul_eq_mul_integral (hQ.mono (𝓕.le a)).aestronglyMeasurable
    (hφ.comp (measurable_incr hW a b)).aestronglyMeasurable

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `Q φ(Z)` is integrable for integrable
`𝓕_a`-measurable `Q` and integrable `φ(Z)`. -/
theorem integrable_mul_fun_incr (h𝓕 : BMFiltration P W 𝓕) {a b : ℝ} (hab : a ≤ b)
    {Q : Ω → ℝ} (hQ : StronglyMeasurable[𝓕 a] Q) (hQi : Integrable Q P) {φ : ℝ → ℝ}
    (hφ : Measurable φ) (hφi : Integrable (fun ω => φ (incr W a b ω)) P) :
    Integrable (fun ω => Q ω * φ (incr W a b ω)) P := by
  have hI : IndepFun Q (fun ω => φ (incr W a b ω)) P :=
    ((indepFun_incr h𝓕 hab hQ).comp (φ := φ) (ψ := id) hφ measurable_id).symm
  exact hI.integrable_mul hQi hφi

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `X φ(Z)` is square integrable for square-integrable
`𝓕_a`-measurable `X` and square-integrable `φ(Z)`.
Generalises `TidyR7ItoUnbounded.memLp_mul_incr_of_memLp` (`φ = id`). -/
theorem memLp_mul_fun_incr (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    {a b : ℝ} (hab : a ≤ b) {X : Ω → ℝ} (hX : StronglyMeasurable[𝓕 a] X) (hX2 : MemLp X 2 P)
    {φ : ℝ → ℝ} (hφ : Measurable φ) (hφ2 : MemLp (fun ω => φ (incr W a b ω)) 2 P) :
    MemLp (fun ω => X ω * φ (incr W a b ω)) 2 P := by
  refine (memLp_two_iff_integrable_sq (((hX.mono (𝓕.le a)).measurable.mul
    (hφ.comp (measurable_incr hW a b))).aestronglyMeasurable)).2 ?_
  have h := integrable_mul_fun_incr h𝓕 hab (hX.pow 2) hX2.integrable_sq
    (φ := fun z => φ z ^ 2) (hφ.pow_const 2) hφ2.integrable_sq
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.mul_apply, Pi.pow_apply, Function.comp_apply]
  ring

/-! ## The left-point remainder -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the left-point remainder of geometric Brownian
motion** over a step `h`, `R(z) = e^{κh + σz} − 1 − (κ + σ²/2)h − σz`. -/
noncomputable def gbmRem (κ σ h z : ℝ) : ℝ :=
  Real.exp (κ * h + σ * z) - 1 - (κ + σ ^ 2 / 2) * h - σ * z

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the mean of the remainder in closed form,
`e^{(κ + σ²/2)h} − 1 − (κ + σ²/2)h`. -/
noncomputable def gbmMean (κ σ h : ℝ) : ℝ :=
  Real.exp ((κ + σ ^ 2 / 2) * h) - 1 - (κ + σ ^ 2 / 2) * h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the second moment of the remainder in closed form. -/
noncomputable def gbmSq (κ σ h : ℝ) : ℝ :=
  Real.exp ((2 * κ + 2 * σ ^ 2) * h)
    - 2 * (1 + (κ + σ ^ 2 / 2) * h + σ ^ 2 * h) * Real.exp ((κ + σ ^ 2 / 2) * h)
    + (1 + (κ + σ ^ 2 / 2) * h) ^ 2 + σ ^ 2 * h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the remainder is continuous in `z`. -/
theorem continuous_gbmRem (κ σ h : ℝ) : Continuous (gbmRem κ σ h) := by
  unfold gbmRem
  fun_prop

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `e^{κh + σZ}` is square integrable. -/
theorem memLp_exp_incr (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (κ σ : ℝ) :
    MemLp (fun ω => Real.exp (κ * (b - a) + σ * incr W a b ω)) 2 P := by
  have hm : Measurable fun ω => Real.exp (κ * (b - a) + σ * incr W a b ω) :=
    Real.measurable_exp.comp (measurable_const.add (measurable_const.mul (measurable_incr hW a b)))
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 ?_
  have h := (integrable_exp_mul_incr hB ha hab (2 * σ)).const_mul (Real.exp (2 * κ * (b - a)))
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only
  rw [← Real.exp_add, sq, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the remainder `R(Z)` is square integrable. -/
theorem memLp_gbmRem (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (κ σ : ℝ) :
    MemLp (fun ω => gbmRem κ σ (b - a) (incr W a b ω)) 2 P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := (((memLp_exp_incr hB hW ha hab κ σ).sub (memLp_const 1)).sub
    (memLp_const ((κ + σ ^ 2 / 2) * (b - a)))).sub ((memLp_incr hB a b).const_mul σ)
  have e : (fun ω => gbmRem κ σ (b - a) (incr W a b ω)) = fun ω =>
      Real.exp (κ * (b - a) + σ * incr W a b ω) - 1 - (κ + σ ^ 2 / 2) * (b - a)
        - σ * incr W a b ω := rfl
  rw [e]
  exact h

/-! ## The moments in closed form -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `e^{κh + σz} = e^{κh}e^{σz}`. -/
lemma exp_affine (κ σ h z : ℝ) : Real.exp (κ * h + σ * z) = Real.exp (κ * h) * Real.exp (σ * z) :=
  Real.exp_add _ _

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`E[e^{κh + σZ}] = e^{(κ + σ²/2)h}`** for a Brownian
increment over `[a, b]`, `h = b − a`, `0 ≤ a`. -/
theorem integral_exp_incr (hB : IsPreBrownianReal W P) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (κ σ : ℝ) :
    ∫ ω, Real.exp (κ * (b - a) + σ * incr W a b ω) ∂P = Real.exp ((κ + σ ^ 2 / 2) * (b - a)) := by
  simp only [exp_affine]
  rw [integral_const_mul, integral_exp_mul_incr hB ha hab, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`E[(e^{κh + σZ})²] = e^{(2κ + 2σ²)h}`**. -/
theorem integral_exp_incr_sq (hB : IsPreBrownianReal W P) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (κ σ : ℝ) :
    ∫ ω, Real.exp (κ * (b - a) + σ * incr W a b ω) ^ 2 ∂P
      = Real.exp ((2 * κ + 2 * σ ^ 2) * (b - a)) := by
  have e : ∀ ω, Real.exp (κ * (b - a) + σ * incr W a b ω) ^ 2
      = Real.exp (2 * κ * (b - a)) * Real.exp ((2 * σ) * incr W a b ω) := fun ω => by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  simp only [e]
  rw [integral_const_mul, integral_exp_mul_incr hB ha hab, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the mean of the remainder**,
`E[R(Z)] = e^{(κ + σ²/2)h} − 1 − (κ + σ²/2)h`. -/
theorem integral_gbmRem (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (κ σ : ℝ) :
    ∫ ω, gbmRem κ σ (b - a) (incr W a b ω) ∂P = gbmMean κ σ (b - a) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have iE := (memLp_exp_incr hB hW ha hab κ σ).integrable one_le_two
  have iZ : Integrable (fun ω => σ * incr W a b ω) P :=
    ((memLp_incr hB a b).integrable one_le_two).const_mul σ
  have s1 : ∫ ω, (Real.exp (κ * (b - a) + σ * incr W a b ω) - 1) ∂P
      = ∫ ω, Real.exp (κ * (b - a) + σ * incr W a b ω) ∂P - ∫ _ω, (1 : ℝ) ∂P :=
    integral_sub iE (integrable_const _)
  have s2 : ∫ ω, (Real.exp (κ * (b - a) + σ * incr W a b ω) - 1 - (κ + σ ^ 2 / 2) * (b - a)) ∂P
      = ∫ ω, (Real.exp (κ * (b - a) + σ * incr W a b ω) - 1) ∂P
        - ∫ _ω, (κ + σ ^ 2 / 2) * (b - a) ∂P :=
    integral_sub (iE.sub (integrable_const _)) (integrable_const _)
  have s3 : ∫ ω, gbmRem κ σ (b - a) (incr W a b ω) ∂P
      = ∫ ω, (Real.exp (κ * (b - a) + σ * incr W a b ω) - 1 - (κ + σ ^ 2 / 2) * (b - a)) ∂P
        - ∫ ω, σ * incr W a b ω ∂P :=
    integral_sub ((iE.sub (integrable_const _)).sub (integrable_const _)) iZ
  rw [s3, s2, s1, integral_exp_incr hB ha hab]
  simp only [integral_const, integral_const_mul, integral_incr hB, probReal_univ, smul_eq_mul,
    one_mul, mul_zero, sub_zero, gbmMean]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the second moment of the remainder**,
`E[R(Z)²] = e^{(2κ + 2σ²)h} − 2(1 + mh + σ²h)e^{mh} + (1 + mh)² + σ²h`, `m = κ + σ²/2`
(expand; `E[Ze^{σZ}] = σh e^{σ²h/2}`, `TidyR12SDEGauss.integral_incr_mul_exp`). -/
theorem integral_gbmRem_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (κ σ : ℝ) :
    ∫ ω, gbmRem κ σ (b - a) (incr W a b ω) ^ 2 ∂P = gbmSq κ σ (b - a) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set h := b - a with hh
  set Z := incr W a b with hZ
  set c0 := 1 + (κ + σ ^ 2 / 2) * h with hc0
  set E1 := Real.exp (κ * h) with hE1
  have iA : Integrable (fun ω => Real.exp ((2 * σ) * Z ω)) P :=
    integrable_exp_mul_incr hB ha hab _
  have iB : Integrable (fun ω => Real.exp (σ * Z ω)) P := integrable_exp_mul_incr hB ha hab _
  have mB : MemLp (fun ω => Real.exp (σ * Z ω)) 2 P := by
    have h0 := memLp_exp_incr hB hW ha hab 0 σ
    simpa using h0
  have iC : Integrable (fun ω => Z ω * Real.exp (σ * Z ω)) P :=
    (memLp_incr hB a b).integrable_mul mB
  have iD : Integrable Z P := (memLp_incr hB a b).integrable one_le_two
  have iE : Integrable (fun ω => Z ω ^ 2) P := integrable_incr_sq hB a b
  have hpt : ∀ ω, gbmRem κ σ h (Z ω) ^ 2 =
      (E1 ^ 2 * Real.exp ((2 * σ) * Z ω) + (-(2 * c0 * E1)) * Real.exp (σ * Z ω)
        + (-(2 * σ * E1)) * (Z ω * Real.exp (σ * Z ω)))
      + (c0 ^ 2 + (2 * c0 * σ) * Z ω + σ ^ 2 * Z ω ^ 2) := by
    intro ω
    have e1 : Real.exp ((2 * σ) * Z ω) = Real.exp (σ * Z ω) ^ 2 := by
      rw [sq, ← Real.exp_add]
      ring_nf
    simp only [gbmRem, exp_affine, e1, hc0, hE1]
    ring
  have i1 : Integrable (fun ω => E1 ^ 2 * Real.exp ((2 * σ) * Z ω)
      + (-(2 * c0 * E1)) * Real.exp (σ * Z ω) + (-(2 * σ * E1)) * (Z ω * Real.exp (σ * Z ω))) P :=
    ((iA.const_mul _).add (iB.const_mul _)).add (iC.const_mul _)
  have i2 : Integrable (fun ω => c0 ^ 2 + (2 * c0 * σ) * Z ω + σ ^ 2 * Z ω ^ 2) P :=
    ((integrable_const _).add (iD.const_mul _)).add (iE.const_mul _)
  have iAB : Integrable (fun ω => E1 ^ 2 * Real.exp ((2 * σ) * Z ω)
      + (-(2 * c0 * E1)) * Real.exp (σ * Z ω)) P := (iA.const_mul _).add (iB.const_mul _)
  have iCD : Integrable (fun ω => c0 ^ 2 + (2 * c0 * σ) * Z ω) P :=
    (integrable_const _).add (iD.const_mul _)
  have t1 : ∫ ω, gbmRem κ σ h (Z ω) ^ 2 ∂P
      = ∫ ω, (E1 ^ 2 * Real.exp ((2 * σ) * Z ω) + (-(2 * c0 * E1)) * Real.exp (σ * Z ω)
        + (-(2 * σ * E1)) * (Z ω * Real.exp (σ * Z ω))) ∂P
        + ∫ ω, (c0 ^ 2 + (2 * c0 * σ) * Z ω + σ ^ 2 * Z ω ^ 2) ∂P :=
    (integral_congr_ae (ae_of_all _ hpt)).trans (integral_add i1 i2)
  have t2 : ∫ ω, (E1 ^ 2 * Real.exp ((2 * σ) * Z ω) + (-(2 * c0 * E1)) * Real.exp (σ * Z ω)
        + (-(2 * σ * E1)) * (Z ω * Real.exp (σ * Z ω))) ∂P
      = ∫ ω, E1 ^ 2 * Real.exp ((2 * σ) * Z ω) ∂P + ∫ ω, (-(2 * c0 * E1)) * Real.exp (σ * Z ω) ∂P
        + ∫ ω, (-(2 * σ * E1)) * (Z ω * Real.exp (σ * Z ω)) ∂P :=
    by rw [integral_add iAB (iC.const_mul _), integral_add (iA.const_mul _) (iB.const_mul _)]
  have t3 : ∫ ω, (c0 ^ 2 + (2 * c0 * σ) * Z ω + σ ^ 2 * Z ω ^ 2) ∂P
      = ∫ _ω, c0 ^ 2 ∂P + ∫ ω, (2 * c0 * σ) * Z ω ∂P + ∫ ω, σ ^ 2 * Z ω ^ 2 ∂P :=
    by rw [integral_add iCD (iE.const_mul _), integral_add (integrable_const _) (iD.const_mul _)]
  rw [t1, t2, t3]
  simp only [integral_const_mul, integral_const, smul_eq_mul, probReal_univ, one_mul]
  rw [integral_exp_mul_incr hB ha hab, integral_exp_mul_incr hB ha hab,
    integral_incr_mul_exp hB ha hab, hZ, integral_incr hB, integral_incr_sq hB ha hab]
  simp only [gbmSq, hc0, hE1, ← hh]
  have k1 : Real.exp (κ * h) ^ 2 * Real.exp (h * (2 * σ) ^ 2 / 2)
      = Real.exp ((2 * κ + 2 * σ ^ 2) * h) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  have k2 : Real.exp (κ * h) * Real.exp (h * σ ^ 2 / 2) = Real.exp ((κ + σ ^ 2 / 2) * h) := by
    rw [← Real.exp_add]
    ring_nf
  rw [k1]
  linear_combination (-(2 * (1 + (κ + σ ^ 2 / 2) * h)) - 2 * σ * σ * h) * k2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`E[(e^{κh + σZ} − 1)²] = e^{(2κ + 2σ²)h}
− 2e^{(κ + σ²/2)h} + 1`** (the mean-square increment factor of geometric Brownian motion). -/
theorem integral_exp_incr_sub_one_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (κ σ : ℝ) :
    ∫ ω, (Real.exp (κ * (b - a) + σ * incr W a b ω) - 1) ^ 2 ∂P
      = Real.exp ((2 * κ + 2 * σ ^ 2) * (b - a)) - 2 * Real.exp ((κ + σ ^ 2 / 2) * (b - a))
        + 1 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have mE := memLp_exp_incr hB hW ha hab κ σ
  have i2 := mE.integrable_sq
  have i1 := (mE.integrable one_le_two).const_mul 2
  have e : ∀ ω, (Real.exp (κ * (b - a) + σ * incr W a b ω) - 1) ^ 2
      = (Real.exp (κ * (b - a) + σ * incr W a b ω) ^ 2
        - 2 * Real.exp (κ * (b - a) + σ * incr W a b ω)) + 1 := fun ω => by ring
  have u1 : ∫ ω, (Real.exp (κ * (b - a) + σ * incr W a b ω) - 1) ^ 2 ∂P
      = ∫ ω, (Real.exp (κ * (b - a) + σ * incr W a b ω) ^ 2
        - 2 * Real.exp (κ * (b - a) + σ * incr W a b ω)) ∂P + ∫ _ω, (1 : ℝ) ∂P :=
    (integral_congr_ae (ae_of_all _ e)).trans (integral_add (i2.sub i1) (integrable_const _))
  have u2 : ∫ ω, (Real.exp (κ * (b - a) + σ * incr W a b ω) ^ 2
        - 2 * Real.exp (κ * (b - a) + σ * incr W a b ω)) ∂P
      = ∫ ω, Real.exp (κ * (b - a) + σ * incr W a b ω) ^ 2 ∂P
        - ∫ ω, 2 * Real.exp (κ * (b - a) + σ * incr W a b ω) ∂P := integral_sub i2 i1
  rw [u1, u2, integral_const_mul, integral_exp_incr_sq hB ha hab, integral_exp_incr hB ha hab]
  simp

/-! ## Small-step behaviour -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **a function with `f 0 = 0` and `f′(0) = 0` is
`o(h)` from the right**: for `ε > 0` there is `δ > 0` with `|f h| ≤ εh` on `[0, δ]`. -/
theorem exists_abs_le_of_hasDerivAt_zero {f : ℝ → ℝ} (hf0 : f 0 = 0) (hf : HasDerivAt f 0 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ h, 0 ≤ h → h ≤ δ → |f h| ≤ ε * h := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hf
  have h1 := hf.def hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.1 h1
  refine ⟨δ / 2, by positivity, fun h h0 hh => ?_⟩
  have hd : dist h 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
    linarith
  have := hδf hd
  simp only [zero_add, hf0, sub_zero, smul_zero, Real.norm_eq_abs, abs_of_nonneg h0] at this
  exact this

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`E[R] = o(h)`**: `gbmMean κ σ` vanishes to first
order at `0`. -/
theorem gbmMean_littleO (κ σ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, 0 ≤ h → h ≤ δ → |gbmMean κ σ h| ≤ ε * h := by
  refine exists_abs_le_of_hasDerivAt_zero (by simp [gbmMean]) ?_ hε
  set m := κ + σ ^ 2 / 2
  have h1 : HasDerivAt (fun h : ℝ => m * h) m 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul m
  have h2 := ((h1.exp.sub_const 1).sub h1)
  refine h2.congr_deriv ?_
  simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`E[R²] = o(h)`**: `gbmSq κ σ` vanishes to first
order at `0`. -/
theorem gbmSq_littleO (κ σ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, 0 ≤ h → h ≤ δ → |gbmSq κ σ h| ≤ ε * h := by
  refine exists_abs_le_of_hasDerivAt_zero (by simp [gbmSq]; ring) ?_ hε
  set m := κ + σ ^ 2 / 2 with hm
  have hl : ∀ c : ℝ, HasDerivAt (fun h : ℝ => c * h) c 0 := fun c => by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have d1 := (hl (2 * κ + 2 * σ ^ 2)).exp
  have d2 := ((((hl m).const_add 1).add (hl (σ ^ 2))).mul (hl m).exp).const_mul 2
  have d3 := ((hl m).const_add 1).pow 2
  have d4 := hl (σ ^ 2)
  have h := ((d1.sub d2).add d3).add d4
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · simp only [gbmSq, hm, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]
    ring
  · simp only [mul_zero, Real.exp_zero, add_zero, Pi.add_apply]
    push_cast
    ring

end Cochrane.Monetarism.TidyR12SDEGauss
