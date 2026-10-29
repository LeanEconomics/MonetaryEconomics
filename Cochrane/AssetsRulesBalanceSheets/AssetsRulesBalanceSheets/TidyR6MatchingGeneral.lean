/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.TidyR5MatchingMeas
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.PSeries

/-!
# Continuous-time matching: wider classes of payment streams

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.4, pp. 250–251 (the
continuous-time present-value relation; matching makes real rates cancel, and "otherwise, the
mismatch ... determines how the price level reacts to real interest rates").

`TidyR5MatchingMeas.matching_necessary_meas` proves the converse of
`MaturityBuffer.matching_cancels` for measurable mismatch streams `y` whose present value converges
absolutely at the lowest rate `r̲` (`e^{−r̲τ} y ∈ L¹(0, ∞)`). The converse is extended here in the
two directions in which a "present value of a payment stream" still makes sense, and the claim is
shown to fail beyond them.

## Main results

* `matching_necessary_measure` (**payment streams that are measures**): debt can mature in lumps
  at discrete dates (Dirac masses) as well as continuously. If two positive measures `μ, ν` on
  `[0, ∞)` (e.g. the positive and negative parts of a signed mismatch stream) have absolutely
  convergent present values at `r̲` and the same present value along every constant real-rate
  path `λ ≥ r̲`, then they coincide on `[0, ∞)`. The proof pushes `e^{−r̲τ}μ` forward by
  `τ ↦ e^{−τ}` to `[0, 1]`, uses Weierstrass and `ext_of_forall_integral_eq_of_IsFiniteMeasure`, and
  undoes the push-forward and the density (`pushM_injective`).
* `matching_necessary_improper` (**conditionally convergent present values**): for a locally
  integrable stream `y` whose present values `lim_{T→∞} ∫₀^T e^{−λτ} y(τ) dτ` exist and vanish for
  every `λ ≥ r̲` (convergence may be conditional), `y = 0` a.e. on `(0, ∞)`. Proof: with
  `Φ(T) = ∫₀^T e^{−r̲τ} y`, integration by parts for absolutely continuous functions
  (`AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`) gives
  `∫₀^T e^{−(r̲+c)τ} y = e^{−cT}Φ(T) + c ∫₀^T e^{−cτ}Φ`, so the bounded continuous `Φ` has vanishing
  Laplace transform, `Φ ≡ 0` (`TidyR5Matching.laplace_unique`), and by the Lebesgue
  differentiation theorem `y = 0` a.e.
* `improper_of_integrable`: this class contains the class of
  `TidyR5MatchingMeas.matching_necessary_meas` (absolutely convergent present values are limits
  of the truncated ones), and
  `improper_class_strictly_larger`: it is strictly larger.
* `junk_counterexample` (**outside the class the claim fails**): `y(τ) = e^{τ²}` has no present
  value at any rate (`no_present_value`: the truncated present values are unbounded), so with
  Lean's convention for non-integrable functions its "present value" is `0` along every constant
  rate path, yet `y ≠ 0` everywhere. A convergence hypothesis on the present value is therefore
  necessary; the improper class above is the natural class of function streams on which the claim
  has content (its maximality is not proved).
-/

namespace Cochrane.AssetsRulesBalanceSheets.TidyR6MatchingGeneral

open MeasureTheory Filter Topology Real

/-! ### Payment streams that are measures -/

/-- Cochrane (2023), §8.4, p. 250: the discount weight at the lowest rate, `e^{−r̲τ}`, as an
extended nonnegative density. -/
noncomputable def wgt (rl : ℝ) (τ : ℝ) : ENNReal := ENNReal.ofReal (exp (-(rl * τ)))

/-- Cochrane (2023), §8.4, p. 250: the stream `μ` on `[0, ∞)` discounted at `r̲`. -/
noncomputable def wMeas (rl : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (μ.restrict (Set.Ici 0)).withDensity (wgt rl)

/-- Cochrane (2023), §8.4, p. 250: the discounted stream transported to `[0, 1]` by
`τ ↦ e^{−τ}`. -/
noncomputable def pushM (rl : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (wMeas rl μ).map (fun τ => exp (-τ))

/-- Cochrane (2023), §8.4, p. 250: the discount weight is measurable. -/
theorem wgt_measurable (rl : ℝ) : Measurable (wgt rl) :=
  ENNReal.measurable_ofReal.comp ((continuous_exp.comp
    ((continuous_const.mul continuous_id).neg)).measurable)

/-- Cochrane (2023), §8.4, p. 250: `τ ↦ e^{−τ}` is a measurable embedding of `ℝ` into `ℝ`. -/
theorem expNeg_embedding : MeasurableEmbedding (fun τ : ℝ => exp (-τ)) := by
  refine MeasurableEmbedding.of_measurable_inverse (g := fun x => -log x)
    (continuous_exp.comp continuous_neg).measurable ?_ (measurable_log.neg) fun τ => by
      simp
  have : Set.range (fun τ : ℝ => exp (-τ)) = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_range, Set.mem_Ioi]
    constructor
    · rintro ⟨τ, rfl⟩
      exact exp_pos _
    · intro hx
      exact ⟨-log x, by simp [exp_log hx]⟩
  rw [this]
  exact measurableSet_Ioi

/-- Cochrane (2023), §8.4, p. 250: if the present value at `r̲` converges absolutely, the
discounted stream is a finite measure. -/
theorem wMeas_finite {rl : ℝ} {μ : Measure ℝ}
    (hμ : Integrable (fun τ => exp (-(rl * τ))) (μ.restrict (Set.Ici 0))) :
    IsFiniteMeasure (wMeas rl μ) := by
  refine ⟨?_⟩
  rw [wMeas, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hμ.lintegral_lt_top

/-- Cochrane (2023), §8.4, p. 250: the transported stream lives on `[0, 1]`. -/
theorem pushM_ae (rl : ℝ) (μ : Measure ℝ) : ∀ᵐ x ∂pushM rl μ, x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [pushM, expNeg_embedding.ae_map_iff]
  have h : ∀ᵐ τ ∂(μ.restrict (Set.Ici 0)), τ ∈ Set.Ici (0 : ℝ) := ae_restrict_mem measurableSet_Ici
  have h2 := (withDensity_absolutelyContinuous (μ.restrict (Set.Ici 0)) (wgt rl)).ae_le h
  filter_upwards [h2] with τ hτ
  exact ⟨(exp_pos _).le, exp_le_one_iff.2 (by linarith [Set.mem_Ici.1 hτ])⟩

/-- Cochrane (2023), §8.4, p. 250 (**the moments are present values**): the `n`-th moment of the
transported stream is the present value at the constant rate `r̲ + n`,
`∫ xⁿ d(pushM) = ∫_{[0,∞)} e^{−(r̲+n)τ} dμ`. -/
theorem pushM_moment (rl : ℝ) (μ : Measure ℝ) (n : ℕ) :
    ∫ x, x ^ n ∂pushM rl μ = ∫ τ in Set.Ici 0, exp (-((rl + n) * τ)) ∂μ := by
  rw [pushM, expNeg_embedding.integral_map, wMeas,
    integral_withDensity_eq_integral_toReal_smul (wgt_measurable rl)]
  · refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [wgt, ENNReal.toReal_ofReal (exp_pos _).le, smul_eq_mul]
    rw [← exp_nat_mul, ← exp_add]
    ring_nf
  · exact Eventually.of_forall fun τ => ENNReal.ofReal_lt_top

/-- Cochrane (2023), §8.4, p. 250 (supporting lemma, **moment determinacy on `[0, 1]`**): two
finite measures on `ℝ` living on `[0, 1]` with the same moments `∫ xⁿ` agree. -/
theorem eq_of_moments {p q : Measure ℝ} [IsFiniteMeasure p] [IsFiniteMeasure q]
    (hp : ∀ᵐ x ∂p, x ∈ Set.Icc (0 : ℝ) 1) (hq : ∀ᵐ x ∂q, x ∈ Set.Icc (0 : ℝ) 1)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂p = ∫ x, x ^ n ∂q) : p = q := by
  -- integrability of continuous functions bounded on `[0, 1]`
  have hint : ∀ (m : Measure ℝ) [IsFiniteMeasure m], (∀ᵐ x ∂m, x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ φ : ℝ → ℝ, Continuous φ → Integrable φ m := by
    intro m _ hm φ hφ
    obtain ⟨C, hC⟩ :=
      isCompact_Icc.exists_bound_of_continuousOn (hφ.continuousOn (s := Set.Icc 0 1))
    exact Integrable.of_bound hφ.aestronglyMeasurable C (hm.mono fun x hx => hC x hx)
  have hpoly : ∀ r : Polynomial ℝ, ∫ x, r.eval x ∂p = ∫ x, r.eval x ∂q := by
    intro r
    have e : ∀ (m : Measure ℝ) [IsFiniteMeasure m], (∀ᵐ x ∂m, x ∈ Set.Icc (0 : ℝ) 1) →
        ∫ x, r.eval x ∂m = ∑ i ∈ Finset.range (r.natDegree + 1), r.coeff i * ∫ x, x ^ i ∂m := by
      intro m _ hm
      have : (fun x => r.eval x) = fun x => ∑ i ∈ Finset.range (r.natDegree + 1),
          r.coeff i * x ^ i := by
        funext x
        rw [Polynomial.eval_eq_sum_range]
      rw [this, integral_finsetSum]
      · exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      · intro i _
        exact (hint m hm _ (continuous_pow i)).const_mul _
    rw [e p hp, e q hq]
    exact Finset.sum_congr rfl fun i _ => by rw [hmom i]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  set K := p.real Set.univ + q.real Set.univ with hK
  have hK0 : 0 ≤ K := by positivity
  have hle : ∀ ε, 0 < ε → |∫ x, f x ∂p - ∫ x, f x ∂q| ≤ ε * K := by
    intro ε hε
    obtain ⟨r, hr⟩ := exists_polynomial_near_of_continuousOn 0 1 f f.continuous.continuousOn ε hε
    have hfi : ∀ (m : Measure ℝ) [IsFiniteMeasure m], (∀ᵐ x ∂m, x ∈ Set.Icc (0 : ℝ) 1) →
        |∫ x, f x ∂m - ∫ x, r.eval x ∂m| ≤ ε * m.real Set.univ := by
      intro m _ hm
      rw [← integral_sub (hint m hm _ f.continuous) (hint m hm _ r.continuous)]
      have := norm_integral_le_of_norm_le_const (μ := m) (f := fun x => f x - r.eval x)
        (C := ε) (hm.mono fun x hx => by
          rw [Real.norm_eq_abs, abs_sub_comm]
          exact (hr x hx).le)
      rwa [Real.norm_eq_abs] at this
    have h1 := hfi p hp
    have h2 := hfi q hq
    rw [hpoly r] at h1
    have := abs_sub_le (∫ x, f x ∂p) (∫ x, r.eval x ∂q) (∫ x, f x ∂q)
    rw [abs_sub_comm (∫ x, r.eval x ∂q)] at this
    calc |∫ x, f x ∂p - ∫ x, f x ∂q| ≤ ε * p.real Set.univ + ε * q.real Set.univ := by
          linarith
      _ = ε * K := by ring
  by_contra hne
  have hpos : 0 < |∫ x, f x ∂p - ∫ x, f x ∂q| := abs_pos.2 (sub_ne_zero.2 hne)
  have := hle (|∫ x, f x ∂p - ∫ x, f x ∂q| / (2 * (K + 1))) (by positivity)
  have e2 : |∫ x, f x ∂p - ∫ x, f x ∂q| / (2 * (K + 1)) * K ≤
      |∫ x, f x ∂p - ∫ x, f x ∂q| / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- Cochrane (2023), §8.4, p. 250 (supporting lemma): the transport is injective on streams with
absolutely convergent present values: `pushM r̲ μ = pushM r̲ ν` forces `μ = ν` on `[0, ∞)`. -/
theorem pushM_injective {rl : ℝ} {μ ν : Measure ℝ} (h : pushM rl μ = pushM rl ν) :
    μ.restrict (Set.Ici 0) = ν.restrict (Set.Ici 0) := by
  have hw : wMeas rl μ = wMeas rl ν := by
    rw [← expNeg_embedding.comap_map (wMeas rl μ), ← expNeg_embedding.comap_map (wMeas rl ν)]
    exact congrArg (Measure.comap _) h
  have hne0 : ∀ τ, wgt rl τ ≠ 0 := fun τ => by
    simp [wgt, exp_pos]
  have hnetop : ∀ τ, wgt rl τ ≠ ⊤ := fun τ => ENNReal.ofReal_ne_top
  rw [← withDensity_inv_same (μ := μ.restrict (Set.Ici 0)) (wgt_measurable rl)
      (Eventually.of_forall hne0) (Eventually.of_forall hnetop),
    ← withDensity_inv_same (μ := ν.restrict (Set.Ici 0)) (wgt_measurable rl)
      (Eventually.of_forall hne0) (Eventually.of_forall hnetop)]
  exact congrArg (fun m => m.withDensity fun x => (wgt rl x)⁻¹) hw

/-- Cochrane (2023), §8.4, pp. 250–251 (**the converse for payment streams that are measures**):
let `μ, ν` be measures on `ℝ` (streams of real payments on `[0, ∞)`, continuous or lumpy — e.g.
debt maturing at discrete dates is a sum of Dirac masses; a signed mismatch stream is the
difference of its positive and negative parts) whose present values at the lowest rate `r̲`
converge absolutely. If the two streams have the same present value
`∫_{[0,∞)} e^{−λτ} dμ = ∫_{[0,∞)} e^{−λτ} dν` along every constant real-rate path `λ ≥ r̲`, then
`μ = ν` on `[0, ∞)`: the maturity structure must match the surpluses exactly. -/
theorem matching_necessary_measure {rl : ℝ} {μ ν : Measure ℝ}
    (hμ : Integrable (fun τ => exp (-(rl * τ))) (μ.restrict (Set.Ici 0)))
    (hν : Integrable (fun τ => exp (-(rl * τ))) (ν.restrict (Set.Ici 0)))
    (h : ∀ l, rl ≤ l → ∫ τ in Set.Ici 0, exp (-(l * τ)) ∂μ = ∫ τ in Set.Ici 0, exp (-(l * τ)) ∂ν) :
    μ.restrict (Set.Ici 0) = ν.restrict (Set.Ici 0) := by
  have := wMeas_finite hμ
  have := wMeas_finite hν
  have : IsFiniteMeasure (pushM rl μ) := Measure.isFiniteMeasure_map _ _
  have : IsFiniteMeasure (pushM rl ν) := Measure.isFiniteMeasure_map _ _
  refine pushM_injective (eq_of_moments (pushM_ae rl μ) (pushM_ae rl ν) fun n => ?_)
  rw [pushM_moment, pushM_moment]
  exact h _ (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)

/-! ### Conditionally convergent present values -/

/-- Cochrane (2023), §8.4, p. 250: the truncated present value of the mismatch stream at the
lowest rate, `Φ(x) = ∫₀ˣ e^{−r̲τ} y(τ) dτ`. -/
noncomputable def prim (rl : ℝ) (y : ℝ → ℝ) (x : ℝ) : ℝ := ∫ τ in (0 : ℝ)..x, exp (-(rl * τ)) * y τ

/-- Cochrane (2023), §8.4, p. 250: the discount factor `e^{−λτ}` is continuous. -/
theorem disc_continuous (l : ℝ) : Continuous (fun τ : ℝ => exp (-(l * τ))) :=
  continuous_exp.comp ((continuous_const.mul continuous_id).neg)

/-- Cochrane (2023), §8.4, p. 250: for a locally integrable stream the discounted stream is
interval integrable on every `[0, T]`. -/
theorem g_intervalIntegrable {rl : ℝ} {y : ℝ → ℝ}
    (hloc : ∀ T, 0 ≤ T → IntervalIntegrable y volume 0 T) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun τ => exp (-(rl * τ)) * y τ) volume 0 T :=
  (hloc T hT).continuousOn_mul (disc_continuous rl).continuousOn

/-- Cochrane (2023), §8.4, p. 250: the truncated present value is continuous on `[0, ∞)`. -/
theorem prim_continuousOn {rl : ℝ} {y : ℝ → ℝ}
    (hloc : ∀ T, 0 ≤ T → IntervalIntegrable y volume 0 T) :
    ContinuousOn (prim rl y) (Set.Ici 0) := by
  intro x hx
  have hx0 : 0 ≤ x := hx
  have hc := intervalIntegral.continuousOn_primitive_interval'
    (g_intervalIntegrable (rl := rl) hloc (by linarith : (0 : ℝ) ≤ x + 1))
    (Set.left_mem_uIcc (a := (0 : ℝ)) (b := x + 1))
  rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ x + 1)] at hc
  refine (hc x ⟨hx0, by linarith⟩).mono_of_mem_nhdsWithin ?_
  refine mem_nhdsWithin.2 ⟨Set.Iio (x + 1), isOpen_Iio, by simp, fun z hz => ?_⟩
  exact ⟨hz.2, le_of_lt hz.1⟩

/-- Cochrane (2023), §8.4, p. 250 (**integration by parts**): for `c > 0`, `T ≥ 0`,
`∫₀^T e^{−(r̲+c)τ} y = e^{−cT} Φ(T) + c ∫₀^T e^{−cτ} Φ(τ) dτ`, by
`AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul` and Lebesgue differentiation
(`IntervalIntegrable.ae_hasDerivAt_integral`). -/
theorem ibp {rl c : ℝ} {y : ℝ → ℝ} (hloc : ∀ T, 0 ≤ T → IntervalIntegrable y volume 0 T)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ τ in (0 : ℝ)..T, exp (-((rl + c) * τ)) * y τ =
      exp (-(c * T)) * prim rl y T + c * ∫ τ in (0 : ℝ)..T, exp (-(c * τ)) * prim rl y τ := by
  set g : ℝ → ℝ := fun τ => exp (-(rl * τ)) * y τ with hg
  set f : ℝ → ℝ := fun τ => exp (-(c * τ)) with hf
  have hgi := g_intervalIntegrable (rl := rl) hloc hT
  have hfd : ∀ x, HasDerivAt f (-c * exp (-(c * x))) x := fun x => by
    have h0 : HasDerivAt (fun x => c * x) c x := by simpa using (hasDerivAt_id x).const_mul c
    have h1 : HasDerivAt (fun x => -(c * x)) (-c) x := h0.neg
    exact HasDerivAt.congr_deriv h1.exp (by ring)
  have hcd : ContDiff ℝ 1 f := Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).neg)
  have hfac : AbsolutelyContinuousOnInterval f 0 T := hcd.contDiffOn.absolutelyContinuousOnInterval
  have hΦac : AbsolutelyContinuousOnInterval (prim rl y) 0 T :=
    hgi.absolutelyContinuousOnInterval_intervalIntegral (Set.left_mem_uIcc)
  have hibp := hfac.integral_mul_deriv_eq_deriv_mul hΦac
  have hderf : deriv f = fun x => -c * exp (-(c * x)) := funext fun x => (hfd x).deriv
  have hderΦ : ∀ᵐ x, x ∈ Set.uIoc 0 T → f x * deriv (prim rl y) x = f x * g x := by
    filter_upwards [hgi.ae_hasDerivAt_integral] with x hx hxm
    have h := hx (Set.uIoc_subset_uIcc hxm) 0 Set.left_mem_uIcc
    rw [show (fun x => ∫ t in (0 : ℝ)..x, g t) = prim rl y from rfl] at h
    rw [h.deriv]
  rw [intervalIntegral.integral_congr_ae hderΦ, hderf] at hibp
  have hΦ0 : prim rl y 0 = 0 := intervalIntegral.integral_same
  have e1 : (fun τ => exp (-((rl + c) * τ)) * y τ) = fun τ => f τ * g τ := by
    funext τ
    simp only [hf, hg, ← mul_assoc, ← exp_add]
    ring_nf
  rw [e1, hibp, hΦ0, mul_zero, sub_zero]
  have e2 : ∫ x in (0 : ℝ)..T, -c * exp (-(c * x)) * prim rl y x =
      -c * ∫ x in (0 : ℝ)..T, exp (-(c * x)) * prim rl y x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [e2]
  ring

/-- Cochrane (2023), §8.4, pp. 250–251 (**the converse for conditionally convergent present
values**): let the mismatch stream `y` be locally integrable on `[0, ∞)` and let its present value
along every constant real-rate path `λ ≥ r̲` exist as an improper integral and vanish,
`∫₀^T e^{−λτ} y(τ) dτ → 0` as `T → ∞` (the convergence may be conditional). Then `y = 0` a.e. on
`(0, ∞)`. -/
theorem matching_necessary_improper {rl : ℝ} {y : ℝ → ℝ}
    (hloc : ∀ T, 0 ≤ T → IntervalIntegrable y volume 0 T)
    (h : ∀ l, rl ≤ l → Tendsto (fun T => ∫ τ in (0 : ℝ)..T, exp (-(l * τ)) * y τ) atTop (𝓝 0)) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioi 0)), y τ = 0 := by
  have hΦc := prim_continuousOn (rl := rl) hloc
  have hΦlim : Tendsto (prim rl y) atTop (𝓝 0) := h rl le_rfl
  -- `Φ` is bounded on `[0, ∞)`
  obtain ⟨M, hM⟩ : ∃ M, ∀ τ, 0 ≤ τ → |prim rl y τ| ≤ M := by
    obtain ⟨T0, hT0⟩ := eventually_atTop.1 (hΦlim.eventually (Metric.closedBall_mem_nhds 0 one_pos))
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hΦc.mono (fun z hz => hz.1 : Set.Icc 0 (max T0 0) ⊆ Set.Ici 0))
    refine ⟨max C 1, fun τ hτ => ?_⟩
    rcases le_total τ (max T0 0) with h1 | h1
    · exact (hC τ ⟨hτ, h1⟩).trans (le_max_left _ _)
    · have := hT0 τ (le_trans (le_max_left _ _) h1)
      rw [Real.dist_eq, sub_zero] at this
      exact this.trans (le_max_right _ _)
  -- the Laplace transform of `Φ` vanishes
  have hLap : ∀ c, 0 < c → ∫ τ in Set.Ioi 0, exp (-(c * τ)) * prim rl y τ = 0 := by
    intro c hc
    have hint := TidyR5Matching.integrableOn_disc hc hΦc hM
    have h1 : Tendsto (fun T => exp (-(c * T)) * prim rl y T +
        c * ∫ τ in (0 : ℝ)..T, exp (-(c * τ)) * prim rl y τ) atTop
        (𝓝 (0 * 0 + c * ∫ τ in Set.Ioi 0, exp (-(c * τ)) * prim rl y τ)) := by
      refine Tendsto.add (Tendsto.mul ?_ hΦlim)
        ((intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id).const_mul c)
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
    have h2 : Tendsto (fun T => exp (-(c * T)) * prim rl y T +
        c * ∫ τ in (0 : ℝ)..T, exp (-(c * τ)) * prim rl y τ) atTop (𝓝 0) :=
      (h (rl + c) (by linarith)).congr' (eventually_atTop.2 ⟨0, fun T hT => ibp hloc hT⟩)
    have := tendsto_nhds_unique h1 h2
    simp only [mul_zero, zero_add, mul_eq_zero] at this
    rcases this with h3 | h3
    · linarith
    · exact h3
  have hΦ0 : ∀ τ, 0 ≤ τ → prim rl y τ = 0 :=
    TidyR5Matching.laplace_unique one_pos hΦc hM fun n => hLap _ (by positivity)
  -- Lebesgue differentiation: `e^{−r̲τ} y = Φ' = 0` a.e. on `(0, ∞)`
  have hder : ∀ N : ℕ, ∀ᵐ x, x ∈ Set.uIcc 0 (N : ℝ) → ∀ c ∈ Set.uIcc 0 (N : ℝ),
      HasDerivAt (fun x => ∫ t in c..x, exp (-(rl * t)) * y t) (exp (-(rl * x)) * y x) x :=
    fun N => (g_intervalIntegrable (rl := rl) hloc (Nat.cast_nonneg N)).ae_hasDerivAt_integral
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [ae_all_iff.2 hder] with x hx hx0
  have hx0' : 0 < x := hx0
  obtain ⟨N, hN⟩ := exists_nat_gt x
  have hmem : x ∈ Set.uIcc 0 (N : ℝ) := by
    rw [Set.uIcc_of_le (Nat.cast_nonneg N)]
    exact ⟨hx0'.le, hN.le⟩
  have h1 : HasDerivAt (prim rl y) (exp (-(rl * x)) * y x) x :=
    hx N hmem 0 Set.left_mem_uIcc
  have heq : prim rl y =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx0') fun z hz => hΦ0 z (le_of_lt hz)
  have h2 : HasDerivAt (prim rl y) 0 x := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  have h3 := h1.unique h2
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd h4 (exp_pos _).ne'
  · exact h4

/-- Cochrane (2023), §8.4, p. 250 (**the improper class contains the absolutely
convergent class**): if `e^{−r̲τ} y` is integrable on `(0, ∞)` (the class of
`TidyR5MatchingMeas.matching_necessary_meas`), then `y` is locally integrable on `[0, ∞)` and for
every `λ ≥ r̲` the truncated present values converge to the present value
`∫_{(0,∞)} e^{−λτ} y`; so `matching_necessary_improper` contains
`TidyR5MatchingMeas.matching_necessary_meas`. -/
theorem improper_of_integrable {rl : ℝ} {y : ℝ → ℝ}
    (hint : IntegrableOn (fun τ => exp (-(rl * τ)) * y τ) (Set.Ioi 0)) :
    (∀ T, 0 ≤ T → IntervalIntegrable y volume 0 T) ∧
      ∀ l, rl ≤ l → Tendsto (fun T => ∫ τ in (0 : ℝ)..T, exp (-(l * τ)) * y τ) atTop
        (𝓝 (∫ τ in Set.Ioi 0, exp (-(l * τ)) * y τ)) := by
  refine ⟨fun T hT => ?_, fun l hl =>
    intervalIntegral_tendsto_integral_Ioi 0 (TidyR5MatchingMeas.integrableOn_shift hl hint)
      tendsto_id⟩
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  have hsub : IntegrableOn (fun τ => exp (-(rl * τ)) * y τ) (Set.Ioc 0 T) :=
    hint.mono_set Set.Ioc_subset_Ioi_self
  have hm : AEStronglyMeasurable (fun τ => exp (rl * τ)) (volume.restrict (Set.Ioc 0 T)) :=
    (continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  refine IntegrableOn.congr_fun (hsub.bdd_mul hm (c := exp (|rl| * T)) ?_) (fun τ _ => ?_)
    measurableSet_Ioc
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with τ hτ
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_exp]
    have h1 : rl * τ ≤ |rl| * τ := mul_le_mul_of_nonneg_right (le_abs_self rl) hτ.1.le
    have h2 : |rl| * τ ≤ |rl| * T := mul_le_mul_of_nonneg_left hτ.2 (abs_nonneg rl)
    linarith
  · rw [← mul_assoc, ← exp_add]
    simp

/-! ### The improper class is strictly larger -/

/-- Cochrane (2023), §8.4, p. 250 (an example stream): the alternating harmonic step stream,
`y(τ) = (−1)ᵏ/(k + 1)` on `[k, k + 1)`. -/
noncomputable def alt (τ : ℝ) : ℝ := (-1) ^ (⌊τ⌋₊) / ((⌊τ⌋₊ : ℝ) + 1)

/-- Cochrane (2023), §8.4, p. 250: the example stream is measurable and bounded by `1`. -/
theorem alt_props : Measurable alt ∧ ∀ τ, |alt τ| ≤ 1 := by
  refine ⟨(Measurable.of_discrete (f := fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1))).comp
    Nat.measurable_floor, fun τ => ?_⟩
  unfold alt
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity)]
  exact (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌊τ⌋₊)])

/-- Cochrane (2023), §8.4, p. 250: the example stream is interval integrable on every interval. -/
theorem alt_ii (a b : ℝ) : IntervalIntegrable alt volume a b := by
  have : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) :=
    isFiniteMeasure_restrict.2 (by rw [Set.uIoc]; exact measure_Ioc_lt_top.ne)
  exact intervalIntegrable_iff.2 (Integrable.of_bound alt_props.1.aestronglyMeasurable 1
    (Eventually.of_forall fun τ => by rw [Real.norm_eq_abs]; exact alt_props.2 τ))

/-- Cochrane (2023), §8.4, p. 250: on `[k, T]`, `T ≤ k + 1`, the stream and its absolute value are
the constants `(−1)ᵏ/(k + 1)` and `1/(k + 1)`, so their integrals are `(T − k)` times those. -/
theorem alt_piece (k : ℕ) {T : ℝ} (hk : (k : ℝ) ≤ T) (hT : T ≤ k + 1) :
    ∫ τ in (k : ℝ)..T, alt τ = (T - k) * ((-1) ^ k / ((k : ℝ) + 1)) ∧
      ∫ τ in (k : ℝ)..T, |alt τ| = (T - k) * (1 / ((k : ℝ) + 1)) := by
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ T := by simp [ae_iff, measure_singleton]
  have hval : ∀ x, x ∈ Set.Ioc (k : ℝ) T → x ≠ T → alt x = (-1) ^ k / ((k : ℝ) + 1) := by
    intro x hx hxT
    have hfl : ⌊x⌋₊ = k := by
      rw [Nat.floor_eq_iff (by linarith [hx.1, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])]
      exact ⟨hx.1.le, lt_of_lt_of_le (lt_of_le_of_ne hx.2 hxT) hT⟩
    simp [alt, hfl]
  constructor
  · rw [intervalIntegral.integral_congr_ae (g := fun _ => (-1) ^ k / ((k : ℝ) + 1)) ?_,
      intervalIntegral.integral_const, smul_eq_mul]
    filter_upwards [hne] with x hxT hx
    rw [Set.uIoc_of_le hk] at hx
    exact hval x hx hxT
  · rw [intervalIntegral.integral_congr_ae (g := fun _ => 1 / ((k : ℝ) + 1)) ?_,
      intervalIntegral.integral_const, smul_eq_mul]
    filter_upwards [hne] with x hxT hx
    rw [Set.uIoc_of_le hk] at hx
    rw [hval x hx hxT, abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos (by positivity)]

/-- Cochrane (2023), §8.4, p. 250: over `[0, n]` the stream integrates to the alternating
harmonic partial sum and its absolute value to the harmonic partial sum. -/
theorem alt_blocks (n : ℕ) :
    ∫ τ in (0 : ℝ)..n, alt τ = ∑ k ∈ Finset.range n, (-1) ^ k * (1 / ((k : ℝ) + 1)) ∧
      ∫ τ in (0 : ℝ)..n, |alt τ| = ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by
  constructor
  · rw [← Nat.cast_zero, ← intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ)) fun k _ => alt_ii _ _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.cast_succ, (alt_piece k (T := (k : ℝ) + 1) (by linarith) le_rfl).1]
    ring
  · rw [← Nat.cast_zero, ← intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ)) fun k _ => (alt_ii _ _).abs]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.cast_succ, (alt_piece k (T := (k : ℝ) + 1) (by linarith) le_rfl).2]
    ring

/-- Cochrane (2023), §8.4, p. 250 (**the improper class is strictly larger**): the alternating
harmonic step stream `alt` is locally integrable, its truncated present values converge at every
rate `λ ≥ 0` (conditionally at `λ = 0`), but `e^{−0·τ} alt` is not integrable on `(0, ∞)`: with
`r̲ = 0` it belongs to the class of `matching_necessary_improper` and not to the class of
`TidyR5MatchingMeas.matching_necessary_meas`. -/
theorem improper_class_strictly_larger :
    (∀ T, 0 ≤ T → IntervalIntegrable alt volume 0 T) ∧
      (∀ l, 0 ≤ l → ∃ L, Tendsto (fun T => ∫ τ in (0 : ℝ)..T, exp (-(l * τ)) * alt τ) atTop
        (𝓝 L)) ∧
      ¬ IntegrableOn (fun τ => exp (-(0 * τ)) * alt τ) (Set.Ioi 0) := by
  have hfa : Antitone (fun k : ℕ => 1 / ((k : ℝ) + 1)) := fun i j hij => by
    have : (i : ℝ) ≤ j := Nat.cast_le.2 hij
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  obtain ⟨L0, hL0⟩ := hfa.tendsto_alternating_series_of_tendsto_zero
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun T _ => alt_ii 0 T, fun l hl => ?_, fun hint => ?_⟩
  · rcases hl.lt_or_eq with hl | rfl
    · have hexp : IntegrableOn (fun τ => exp (-l * τ)) (Set.Ioi 0) :=
        exp_neg_integrableOn_Ioi 0 hl
      have hint : IntegrableOn (fun τ => exp (-(l * τ)) * alt τ) (Set.Ioi 0) := by
        refine hexp.mono' (((disc_continuous l).measurable.mul alt_props.1).aestronglyMeasurable)
          (Eventually.of_forall fun τ => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), neg_mul]
        exact mul_le_of_le_one_right (exp_pos _).le (alt_props.2 τ)
      exact ⟨_, ((improper_of_integrable (rl := l) hint).2 l le_rfl)⟩
    · refine ⟨L0, ?_⟩
      have hsplit : ∀ T, 0 ≤ T → ∫ τ in (0 : ℝ)..T, exp (-(0 * τ)) * alt τ =
          (∑ k ∈ Finset.range ⌊T⌋₊, (-1) ^ k * (1 / ((k : ℝ) + 1))) +
            (T - ⌊T⌋₊) * ((-1) ^ ⌊T⌋₊ / ((⌊T⌋₊ : ℝ) + 1)) := fun T hT => by
        simp only [zero_mul, neg_zero, exp_zero, one_mul]
        rw [← intervalIntegral.integral_add_adjacent_intervals (alt_ii 0 (⌊T⌋₊ : ℝ))
          (alt_ii _ T), (alt_blocks ⌊T⌋₊).1,
          (alt_piece ⌊T⌋₊ (Nat.floor_le hT) (Nat.lt_floor_add_one T).le).1]
      have hflo : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := tendsto_nat_floor_atTop
      have hrem : Tendsto (fun T : ℝ => (T - ⌊T⌋₊) * ((-1) ^ ⌊T⌋₊ / ((⌊T⌋₊ : ℝ) + 1))) atTop
          (𝓝 0) := by
        have hb0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hb := hb0.comp hflo
        refine squeeze_zero_norm' (eventually_atTop.2 ⟨0, fun T hT => ?_⟩) hb
        rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
          abs_of_pos (by positivity : (0 : ℝ) < (⌊T⌋₊ : ℝ) + 1)]
        have h1 : |T - ⌊T⌋₊| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [Nat.floor_le hT, Nat.lt_floor_add_one T]
        simp only [Function.comp]
        calc |T - ⌊T⌋₊| * (1 / ((⌊T⌋₊ : ℝ) + 1)) ≤ 1 * (1 / ((⌊T⌋₊ : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = 1 / ((⌊T⌋₊ : ℝ) + 1) := one_mul _
      have := (hL0.comp hflo).add hrem
      rw [add_zero] at this
      exact this.congr' (eventually_atTop.2 ⟨0, fun T hT => (hsplit T hT).symm⟩)
  · have hint' : IntegrableOn alt (Set.Ioi 0) := hint.congr_fun (fun τ _ => by simp)
      measurableSet_Ioi
    have hb : ∀ n : ℕ, ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) ≤ ∫ τ in Set.Ioi 0, |alt τ| := by
      intro n
      rw [← (alt_blocks n).2, intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
      exact setIntegral_mono_set hint'.abs (Eventually.of_forall fun τ => abs_nonneg _)
        Set.Ioc_subset_Ioi_self.eventuallyLE
    obtain ⟨n, hn⟩ := ((Real.tendsto_sum_range_one_div_nat_succ_atTop).eventually_gt_atTop
      (∫ τ in Set.Ioi 0, |alt τ|)).exists
    exact absurd (hb n) (not_le.2 hn)

/-! ### Outside the class the claim fails -/

/-- Cochrane (2023), §8.4, p. 250 (supporting lemma): for every rate `λ`, the discounted stream
`e^{−λτ} e^{τ²}` is at least `1` beyond `max λ 0`. -/
theorem junk_ge_one (l : ℝ) {τ : ℝ} (hτ : max l 0 ≤ τ) : 1 ≤ exp (-(l * τ)) * exp (τ ^ 2) := by
  rw [← exp_add, one_le_exp_iff]
  have h1 : l ≤ τ := (le_max_left _ _).trans hτ
  have h2 : 0 ≤ τ := (le_max_right _ _).trans hτ
  nlinarith

/-- Cochrane (2023), §8.4, p. 250 (**no present value**): for the stream `y(τ) = e^{τ²}` the
truncated present values `∫₀^T e^{−λτ} y` diverge to `+∞` at every rate `λ`; in particular they
converge at no rate, and `e^{−λτ} y` is integrable on `(0, ∞)` at no rate. -/
theorem no_present_value (l : ℝ) :
    Tendsto (fun T => ∫ τ in (0 : ℝ)..T, exp (-(l * τ)) * exp (τ ^ 2)) atTop atTop ∧
      ¬ IntegrableOn (fun τ => exp (-(l * τ)) * exp (τ ^ 2)) (Set.Ioi 0) := by
  set a := max l 0 with ha
  have ha0 : 0 ≤ a := le_max_right _ _
  have hcont : Continuous (fun τ => exp (-(l * τ)) * exp (τ ^ 2)) :=
    (disc_continuous l).mul (continuous_exp.comp (continuous_pow 2))
  constructor
  · refine tendsto_atTop_mono' atTop (eventually_atTop.2 ⟨a, fun T hT => ?_⟩)
      (tendsto_atTop_add_const_right atTop (-a) tendsto_id)
    change T + -a ≤ ∫ τ in (0 : ℝ)..T, exp (-(l * τ)) * exp (τ ^ 2)
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := a)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    have h1 : 0 ≤ ∫ τ in (0 : ℝ)..a, exp (-(l * τ)) * exp (τ ^ 2) :=
      intervalIntegral.integral_nonneg ha0 fun τ _ => (mul_pos (exp_pos _) (exp_pos _)).le
    have h2 : ∫ τ in a..T, (1 : ℝ) ≤ ∫ τ in a..T, exp (-(l * τ)) * exp (τ ^ 2) :=
      intervalIntegral.integral_mono_on hT intervalIntegrable_const (hcont.intervalIntegrable _ _)
        fun τ hτ => junk_ge_one l hτ.1
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h2
    linarith
  · intro hint
    have h1 : IntegrableOn (fun _ => (1 : ℝ)) (Set.Ioi a) := by
      refine ((hint.mono_set (Set.Ioi_subset_Ioi ha0)).mono' ?_ ?_)
      · exact aestronglyMeasurable_const
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with τ hτ
        rw [Real.norm_eq_abs, abs_one]
        exact junk_ge_one l (le_of_lt hτ)
    rw [integrableOn_const_iff] at h1
    rcases h1 with h1 | h1
    · simp at h1
    · rw [Real.volume_Ioi] at h1
      exact lt_irrefl _ h1

/-- Cochrane (2023), §8.4, pp. 250–251 (**outside the class the claim fails**): there is a stream
`y` (namely `e^{τ²}`), nonzero everywhere and hence not `0` a.e. on `(0, ∞)`, whose present value
in Lean's sense, `∫_{(0,∞)} e^{−λτ} y` (`0` by convention when the integrand is not integrable), is
`0` along every constant real-rate path `λ`. Without a convergence hypothesis on the present value
the matching claim is false; and since the truncated present values of this stream diverge at
every rate (`no_present_value`), the conditionally convergent class of
`matching_necessary_improper` is the natural class on which the claim has content (maximality
is not proved). -/
theorem junk_counterexample :
    ∃ y : ℝ → ℝ, (∀ l, ∫ τ in Set.Ioi 0, MaturityBuffer.cdisc (fun _ => l) τ * y τ = 0) ∧
      (∀ τ, y τ ≠ 0) ∧ ¬ ∀ᵐ τ ∂(volume.restrict (Set.Ioi (0 : ℝ))), y τ = 0 := by
  refine ⟨fun τ => exp (τ ^ 2), fun l => ?_, fun τ => (exp_pos _).ne', fun hae => ?_⟩
  · simp only [TidyR5Matching.cdisc_const]
    exact integral_undef (no_present_value l).2
  · have hne : volume.restrict (Set.Ioi (0 : ℝ)) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioi]
      exact ENNReal.top_ne_zero
    have : (ae (volume.restrict (Set.Ioi (0 : ℝ)))).NeBot := ae_neBot.2 hne
    obtain ⟨τ, hτ⟩ := hae.exists
    exact (exp_pos _).ne' hτ

end Cochrane.AssetsRulesBalanceSheets.TidyR6MatchingGeneral
