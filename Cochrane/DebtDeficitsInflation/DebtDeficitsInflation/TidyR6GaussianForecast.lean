/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.TidyR6CondExpForecast
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Gaussian processes: conditional-expectation forecasts are linear

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, p. 102, and Online
Appendix Chapter 2, §§2.1.4–2.1.6, pp. 597–601.

For jointly Gaussian processes the conditional expectation given the σ-algebra of the past equals
the best linear forecast, so the Wold and Granger statements of `Wold` and `InvertibilityMeasure`
hold verbatim with Mathlib conditional expectations.

## Main results

* The Gaussian Hilbert space: real Gaussian laws are closed under `L²` limits
  (`hasGaussianLaw_of_tendsto`), so every element of the closed linear span of a Gaussian process
  is Gaussian (`hasGaussianLaw_of_mem_closure`) and the closed span is itself a Gaussian process
  (`isGaussianProcess_closure`).
* `condExp_eq_linear_of_gaussian`: for a centered Gaussian process, `E(X_τ|σ(X_i : i ∈ past))`
  is a.e. the orthogonal projection of `X_τ` on the closed linear span of the past (the linear
  forecast error is uncorrelated with, hence independent of, the past).
* `gaussian_condExp_mse`, `gaussian_granger`: conditional and linear (`linForecast`) forecast
  error variances coincide, so every linear Granger-causality statement (e.g.
  `InvertibilityMeasure.granger_general`) holds with conditional expectations.
* `gaussian_ceInnov_eq_wold`, `gaussian_wold_condExp`: for a centered Gaussian process indexed by
  `ℤ`, the conditional-expectation innovations are the Wold innovations, and the Wold
  decomposition holds with them.
* The i.i.d. Gaussian economy (`GaussEconomy.gaussLaw`): coordinates form a Gaussian process
  (`GaussEconomy.isGaussianProcess_coord`), and for the book's `a(ρ) = 0` surplus
  `s_t = e_t − θe_{t−1}`, `θ = ρ⁻¹` (`GaussEconomy.gaussian_noninvertible_condExp`): the
  conditional forecast `E(s_{t+1}|σ(s_t, s_{t−1}, …))` is the linear one, with error variance
  `θ²σ²`; the shock is not even a nonlinear function of the surplus history; and, with debt
  `v_t = −θe_t`, the conditional forecast given surpluses and debt has error variance
  `σ² < θ²σ²` (debt Granger-causes surpluses with conditional expectations).
-/

namespace Cochrane.DebtDeficitsInflation.TidyR6GaussianForecast

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped RealInnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### `L²` tools -/

/-- Cochrane (2023), Online Appendix p. 597 (tool): on a probability space `E|F| ≤ ‖F‖_{L²}`. -/
theorem integral_abs_le_norm (F : Lp ℝ 2 μ) : ∫ ω, |F ω| ∂μ ≤ ‖F‖ := by
  have h1 : ∫ ω, |F ω| ∂μ = (eLpNorm F 1 μ).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm
      (Lp.aestronglyMeasurable F)]
    · simp only [Real.norm_eq_abs]
    · exact Lp.aestronglyMeasurable F
  rw [h1, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top F)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))

omit [IsProbabilityMeasure μ] in
/-- Cochrane (2023), Online Appendix p. 597 (tool): in `L²`, `‖F‖² = E F²`.
Generalises `TidyR6CondExpForecast.Coin.norm_sq_eq_integral` to any measure space. -/
theorem norm_sq_eq_integral (F : Lp ℝ 2 μ) : ‖F‖ ^ 2 = ∫ ω, (F ω) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun ω => by
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs])

/-- Cochrane (2023), Online Appendix p. 597 (tool): `|e^{ia} − e^{ib}| ≤ |a − b|`. -/
theorem norm_cexp_sub_le (a b : ℝ) : ‖cexp (a * I) - cexp (b * I)‖ ≤ |a - b| := by
  have h : cexp (a * I) - cexp (b * I) = cexp (b * I) * (cexp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-! ### Gaussian laws are closed under `L²` limits -/

omit [IsProbabilityMeasure μ] in
/-- Cochrane (2023), Online Appendix p. 597 (tool): the characteristic function of the law of a
random variable, `φ(t) = E e^{itY}`. -/
theorem charFun_map_eq {Y : Ω → ℝ} (hY : AEMeasurable Y μ) (t : ℝ) :
    charFun (μ.map Y) t = ∫ ω, cexp (t * Y ω * I) ∂μ := by
  rw [charFun_apply_real, integral_map hY (by fun_prop)]

/-- Cochrane (2023), Online Appendix p. 597, **the Gaussian Hilbert space** (tool): if `W_n → W`
in `L²` and every `W_n` has a Gaussian law, so does `W` (characteristic functions converge, and
the means and variances converge). -/
theorem hasGaussianLaw_of_tendsto {W : ℕ → Lp ℝ 2 μ} {W' : Lp ℝ 2 μ}
    (hW : Tendsto W atTop (𝓝 W')) (hG : ∀ n, HasGaussianLaw (W n : Ω → ℝ) μ) :
    HasGaussianLaw (W' : Ω → ℝ) μ := by
  have hmeas : ∀ F : Lp ℝ 2 μ, AEMeasurable (F : Ω → ℝ) μ := fun F =>
    (Lp.aestronglyMeasurable F).aemeasurable
  have hnorm : Tendsto (fun n => ‖W n - W'‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hW
  have hint : ∀ F : Lp ℝ 2 μ, Integrable (F : Ω → ℝ) μ := fun F =>
    (Lp.memLp F).integrable one_le_two
  have habs : ∀ n, ∫ ω, |W n ω - W' ω| ∂μ ≤ ‖W n - W'‖ := fun n => by
    calc ∫ ω, |W n ω - W' ω| ∂μ = ∫ ω, |(W n - W') ω| ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_sub (W n) W'] with ω h
          rw [h, Pi.sub_apply]
      _ ≤ ‖W n - W'‖ := integral_abs_le_norm _
  -- the means converge
  have hm : Tendsto (fun n => ∫ ω, W n ω ∂μ) atTop (𝓝 (∫ ω, W' ω ∂μ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hnorm
    rw [← integral_sub (hint _) (hint _), Real.norm_eq_abs]
    exact (abs_integral_le_integral_abs).trans (habs n)
  -- the second moments converge
  have hsq : Tendsto (fun n => ∫ ω, (W n ω) ^ 2 ∂μ) atTop (𝓝 (∫ ω, (W' ω) ^ 2 ∂μ)) := by
    simp_rw [← norm_sq_eq_integral]
    exact (continuous_norm.tendsto W').comp hW |>.pow 2
  have hv : Tendsto (fun n => Var[(W n : Ω → ℝ); μ]) atTop (𝓝 (Var[(W' : Ω → ℝ); μ])) := by
    simp_rw [variance_eq_sub (Lp.memLp _)]
    exact hsq.sub (hm.pow 2)
  -- the characteristic functions converge
  have hcf : ∀ t : ℝ, Tendsto (fun n => charFun (μ.map (W n)) t) atTop
      (𝓝 (charFun (μ.map W') t)) := fun t => by
    simp_rw [charFun_map_eq (hmeas _)]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ F : Lp ℝ 2 μ, Integrable (fun ω => cexp (t * F ω * I)) μ := fun F =>
      Integrable.of_bound (by
        have : AEMeasurable (fun ω => cexp (t * F ω * I)) μ := by fun_prop
        exact this.aestronglyMeasurable) 1 (Eventually.of_forall fun ω => by
          rw [show (t : ℂ) * (F ω : ℂ) * I = ((t * F ω : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I])
    have hlim : Tendsto (fun n => |t| * ‖W n - W'‖) atTop (𝓝 0) := by
      simpa using hnorm.const_mul |t|
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
    rw [← integral_sub (hb _) (hb _)]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ ω, ‖cexp (t * W n ω * I) - cexp (t * W' ω * I)‖ ∂μ
        ≤ ∫ ω, |t| * |W n ω - W' ω| ∂μ := by
          refine integral_mono ((hb _).sub (hb _)).norm
            (((hint _).sub (hint _)).abs.const_mul _) fun ω => ?_
          have := norm_cexp_sub_le (t * W n ω) (t * W' ω)
          push_cast at this
          calc _ ≤ |t * W n ω - t * W' ω| := this
            _ = |t| * |W n ω - W' ω| := by rw [← mul_sub, abs_mul]
      _ ≤ |t| * ‖W n - W'‖ := by
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (habs n) (abs_nonneg t)
  -- identify the limit
  have hlaw : ∀ n, μ.map (W n) = gaussianReal (∫ ω, W n ω ∂μ) (Var[(W n : Ω → ℝ); μ]).toNNReal :=
    fun n => (hG n).map_eq_gaussianReal
  have hcf2 : ∀ t : ℝ, Tendsto (fun n => charFun (μ.map (W n)) t) atTop
      (𝓝 (cexp (t * (∫ ω, W' ω ∂μ) * I - (Var[(W' : Ω → ℝ); μ]) * t ^ 2 / 2))) := fun t => by
    simp_rw [hlaw, charFun_gaussianReal, Real.coe_toNNReal _ (variance_nonneg _ _)]
    refine (Complex.continuous_exp.tendsto _).comp ?_
    have h1 : Tendsto (fun n => ((∫ ω, W n ω ∂μ : ℝ) : ℂ)) atTop
        (𝓝 ((∫ ω, W' ω ∂μ : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto _).comp hm
    have h2 : Tendsto (fun n => ((Var[(W n : Ω → ℝ); μ] : ℝ) : ℂ)) atTop
        (𝓝 ((Var[(W' : Ω → ℝ); μ] : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto _).comp hv
    exact ((h1.const_mul (t : ℂ)).mul_const I).sub ((h2.mul_const ((t : ℂ) ^ 2)).div_const 2)
  have heq : μ.map W' = gaussianReal (∫ ω, W' ω ∂μ) (Var[(W' : Ω → ℝ); μ]).toNNReal := by
    have : IsFiniteMeasure (μ.map W') := Measure.isFiniteMeasure_map _ _
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [tendsto_nhds_unique (hcf t) (hcf2 t), charFun_gaussianReal,
      Real.coe_toNNReal _ (variance_nonneg _ _)]
  exact ⟨hmeas W', by rw [heq]; infer_instance⟩

/-! ### The closed linear span of a Gaussian process -/

variable {T : Type*}

/-- Cochrane (2023), Online Appendix p. 597: a family of square-integrable variables as elements
of `L²`.
Generalises `TidyR6CondExpForecast.toL2` to an arbitrary index type. -/
noncomputable def toLpFam {X : T → Ω → ℝ} (hm2 : ∀ t, MemLp (X t) 2 μ) (t : T) : Lp ℝ 2 μ :=
  (hm2 t).toLp (X t)

omit [IsProbabilityMeasure μ] in
/-- Cochrane (2023), Online Appendix p. 597 (tool): every finite linear combination of a Gaussian
process has a Gaussian law. -/
theorem hasGaussianLaw_of_mem_span {X : T → Ω → ℝ} (hX : IsGaussianProcess X μ)
    (hm2 : ∀ t, MemLp (X t) 2 μ) {W : Lp ℝ 2 μ}
    (hW : W ∈ Submodule.span ℝ (Set.range (toLpFam hm2))) :
    HasGaussianLaw (W : Ω → ℝ) μ := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hW
  set s := c.support
  have hae : ((c.sum fun i a => a • toLpFam hm2 i : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ]
      fun ω => ∑ i ∈ s, c i * X i ω := by
    rw [Finsupp.sum]
    have hs : ∀ᵐ ω ∂μ, ∀ i ∈ s, (c i • toLpFam hm2 i : Lp ℝ 2 μ) ω = c i * X i ω :=
      (eventually_all_finset s).2 fun i _ => by
        filter_upwards [Lp.coeFn_smul (c i) (toLpFam hm2 i), MemLp.coeFn_toLp (hm2 i)]
          with ω h1 h2
        rw [h1, Pi.smul_apply, smul_eq_mul, toLpFam, h2]
    filter_upwards [Lp.coeFn_fun_finsetSum s (fun i => c i • toLpFam hm2 i), hs] with ω h1 h2
    rw [h1]
    exact Finset.sum_congr rfl h2
  let L : (s → ℝ) →L[ℝ] ℝ := ∑ i : s, c i • ContinuousLinearMap.proj i
  have hL := (hX.hasGaussianLaw s).map L
  have hfun : (L ∘ fun ω => s.restrict (X · ω)) = fun ω => ∑ i ∈ s, c i * X i ω := by
    funext ω
    simp only [L, Function.comp_apply, Finset.univ_eq_attach, sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, Finset.restrict, smul_eq_mul]
    exact Finset.sum_attach s (fun i => c i * X i ω)
  rw [hfun] at hL
  exact hL.congr hae.symm

/-- Cochrane (2023), Online Appendix p. 597, **the Gaussian Hilbert space**: every element of the
closed linear span (in `L²`) of a Gaussian process has a Gaussian law. -/
theorem hasGaussianLaw_of_mem_closure {X : T → Ω → ℝ} (hX : IsGaussianProcess X μ)
    (hm2 : ∀ t, MemLp (X t) 2 μ) {W : Lp ℝ 2 μ}
    (hW : W ∈ (Submodule.span ℝ (Set.range (toLpFam hm2))).topologicalClosure) :
    HasGaussianLaw (W : Ω → ℝ) μ := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hW
  obtain ⟨seq, hseq, hlim⟩ := mem_closure_iff_seq_limit.1 hW
  exact hasGaussianLaw_of_tendsto hlim fun n => hasGaussianLaw_of_mem_span hX hm2 (hseq n)

/-- Cochrane (2023), Online Appendix p. 597, **the Gaussian Hilbert space**: the closed linear span
of a Gaussian process, indexed by its own elements, is a Gaussian process (all finite families are
jointly Gaussian). -/
theorem isGaussianProcess_closure {X : T → Ω → ℝ} (hX : IsGaussianProcess X μ)
    (hm2 : ∀ t, MemLp (X t) 2 μ) :
    IsGaussianProcess (fun W : (Submodule.span ℝ (Set.range (toLpFam hm2))).topologicalClosure =>
      ((W : Lp ℝ 2 μ) : Ω → ℝ)) μ := by
  classical
  set K := (Submodule.span ℝ (Set.range (toLpFam hm2))).topologicalClosure
  refine ⟨fun I => ?_⟩
  have hYm : Measurable fun ω => I.restrict (fun W : K => ((W : Lp ℝ 2 μ) : Ω → ℝ) ω) :=
    measurable_pi_iff.2 fun i => (Lp.stronglyMeasurable ((i : K) : Lp ℝ 2 μ)).measurable
  refine ⟨hYm.aemeasurable, isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
  set Y := fun ω => I.restrict (fun W : K => ((W : Lp ℝ 2 μ) : Ω → ℝ) ω)
  set Z : Lp ℝ 2 μ := ∑ i : I, L (fun j => if i = j then 1 else 0) • ((i : K) : Lp ℝ 2 μ)
  have hZ : Z ∈ K := K.sum_mem fun i _ => K.smul_mem _ (i : K).2
  have hae : (Z : Ω → ℝ) =ᵐ[μ] L ∘ Y := by
    have hs : ∀ᵐ ω ∂μ, ∀ i ∈ (Finset.univ : Finset I),
        (L (fun j => if i = j then 1 else 0) • ((i : K) : Lp ℝ 2 μ) : Lp ℝ 2 μ) ω =
          L (fun j => if i = j then 1 else 0) * ((i : K) : Lp ℝ 2 μ) ω :=
      (eventually_all_finset _).2 fun i _ => by
        filter_upwards [Lp.coeFn_smul (L (fun j => if i = j then 1 else 0))
          ((i : K) : Lp ℝ 2 μ)] with ω h1
        rw [h1, Pi.smul_apply, smul_eq_mul]
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i : I => L (fun j => if i = j then 1 else 0) • ((i : K) : Lp ℝ 2 μ)), hs]
      with ω h1 h2
    have hpi := LinearMap.pi_apply_eq_sum_univ (L : (I → ℝ) →ₗ[ℝ] ℝ) (Y ω)
    simp only [ContinuousLinearMap.coe_coe] at hpi
    rw [h1, Finset.sum_congr rfl h2, Function.comp_apply, hpi]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Y, Finset.restrict, smul_eq_mul]
    ring
  have hmap : (μ.map Y).map L = μ.map (Z : Ω → ℝ) := by
    rw [Measure.map_map L.continuous.measurable hYm]
    exact Measure.map_congr hae.symm
  rw [hmap, (hasGaussianLaw_of_mem_closure hX hm2 hZ).map_eq_gaussianReal]
  exact ⟨_, _, rfl⟩

/-- Cochrane (2023), Online Appendix p. 597 (tool): `⟪1, F⟫ = E F` in `L²`. -/
theorem inner_one_eq_integral (F : Lp ℝ 2 μ) :
    ⟪(memLp_const (1 : ℝ)).toLp (fun _ : Ω => (1 : ℝ)), F⟫ = ∫ ω, F ω ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_const (1 : ℝ) (μ := μ) (p := 2))] with ω h
  rw [h]
  simp

/-- Cochrane (2023), Online Appendix p. 597 (tool): every element of the closed linear span of a
centered process has mean zero. -/
theorem integral_eq_zero_of_mem_closure {X : T → Ω → ℝ} (hm2 : ∀ t, MemLp (X t) 2 μ)
    (h0 : ∀ t, ∫ ω, X t ω ∂μ = 0) {W : Lp ℝ 2 μ}
    (hW : W ∈ (Submodule.span ℝ (Set.range (toLpFam hm2))).topologicalClosure) :
    ∫ ω, W ω ∂μ = 0 := by
  set one : Lp ℝ 2 μ := (memLp_const (1 : ℝ)).toLp (fun _ : Ω => (1 : ℝ))
  have hle : (Submodule.span ℝ (Set.range (toLpFam hm2))).topologicalClosure ≤ (ℝ ∙ one)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right,
      inner_one_eq_integral, ← h0 t]
    exact integral_congr_ae (MemLp.coeFn_toLp (hm2 t))
  rw [← inner_one_eq_integral]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hW)

/-! ### Gaussian processes: the conditional forecast is the linear forecast -/

/-- Cochrane (2023), §4.3, p. 102, and Online Appendix pp. 597–601, **for jointly Gaussian
processes the conditional-expectation forecast is the best linear forecast**: if `X` is a
centered Gaussian process of measurable variables, then for any family of observed past values
`X_{past(i)}` and any target `X_τ`, a.e.
`E(X_τ|σ(X_{past(i)} : i)) = P_K X_τ`, `K` the closed linear span of the observed values. The
linear forecast error is uncorrelated with the past, hence (joint Gaussianity) independent of
it. -/
theorem condExp_eq_linear_of_gaussian {X : T → Ω → ℝ} (hX : IsGaussianProcess X μ)
    (hXm : ∀ t, Measurable (X t)) (h0 : ∀ t, ∫ ω, X t ω ∂μ = 0) (hm2 : ∀ t, MemLp (X t) 2 μ)
    {ι : Type*} (past : ι → T) (τ : T) :
    μ[X τ | TidyR6CondExpForecast.genSigma fun i => X (past i)] =ᵐ[μ]
      ((Submodule.span ℝ (Set.range fun i => toLpFam hm2 (past i))).topologicalClosure
        |>.starProjection (toLpFam hm2 τ) : Ω → ℝ) := by
  set KS := (Submodule.span ℝ (Set.range fun i => toLpFam hm2 (past i))).topologicalClosure
  set KA := (Submodule.span ℝ (Set.range (toLpFam hm2))).topologicalClosure
  have hG : TidyR6CondExpForecast.genSigma (fun i => X (past i)) ≤ mΩ :=
    iSup_le fun i => (hXm _).comap_le
  set p := KS.starProjection (toLpFam hm2 τ)
  set e := toLpFam hm2 τ - p
  have hKSA : KS ≤ KA := Submodule.topologicalClosure_mono (Submodule.span_mono
    (by rintro _ ⟨i, rfl⟩; exact ⟨past i, rfl⟩))
  have hxA : ∀ t, toLpFam hm2 t ∈ KA := fun t =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨t, rfl⟩)
  have heA : e ∈ KA := KA.sub_mem (hxA τ) (hKSA (KS.starProjection_apply_mem _))
  have hperp : e ∈ KSᗮ := KS.sub_starProjection_mem_orthogonal _
  have he0 : ∫ ω, e ω ∂μ = 0 := integral_eq_zero_of_mem_closure hm2 h0 heA
  -- the linear forecast error is uncorrelated with the past
  have hcov : ∀ (_ : Unit) (i : ι), cov[(e : Ω → ℝ), X (past i); μ] = 0 := fun _ i => by
    have hin : ⟪toLpFam hm2 (past i), e⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (Submodule.le_topologicalClosure _
        (Submodule.subset_span (Set.mem_range_self (f := fun i => toLpFam hm2 (past i)) i)))
        hperp
    rw [covariance, he0, h0]
    simp only [sub_zero]
    rw [← hin, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (hm2 (past i))] with ω h
    simp only [toLpFam] at h ⊢
    rw [h]
    simp only [RCLike.inner_apply, conj_trivial]
  -- joint Gaussianity of the error and the past
  have hK := isGaussianProcess_closure hX hm2
  let f : Unit ⊕ ι → KA := Sum.elim (γ := KA) (fun _ => ⟨e, heA⟩)
    fun i => ⟨toLpFam hm2 (past i), hxA _⟩
  have hZ : IsGaussianProcess (Sum.elim (fun _ : Unit => (e : Ω → ℝ)) fun i => X (past i)) μ := by
    refine (hK.comp_right f).congr fun j => ?_
    rcases j with _ | i
    · exact ae_eq_refl _
    · exact MemLp.coeFn_toLp (hm2 (past i))
  have hind := hZ.indepFun_of_covariance_eq_zero
    (fun _ => (Lp.stronglyMeasurable e).measurable.aemeasurable)
    (fun i => (hXm (past i)).aemeasurable) hcov
  rw [IndepFun_iff_Indep] at hind
  have hle1 : MeasurableSpace.comap (e : Ω → ℝ) inferInstance ≤
      MeasurableSpace.comap (fun ω (_ : Unit) => (e : Ω → ℝ) ω) MeasurableSpace.pi := by
    have hm : Measurable[MeasurableSpace.comap (fun ω (_ : Unit) => (e : Ω → ℝ) ω)
        MeasurableSpace.pi] (e : Ω → ℝ) := (measurable_pi_apply (X := fun _ : Unit => ℝ) ()).comp
      (comap_measurable (fun ω (_ : Unit) => (e : Ω → ℝ) ω))
    exact hm.comap_le
  have hle2 : TidyR6CondExpForecast.genSigma (fun i => X (past i)) ≤
      MeasurableSpace.comap (fun ω i => X (past i) ω) MeasurableSpace.pi := by
    refine iSup_le fun i => ?_
    have hm : Measurable[MeasurableSpace.comap (fun ω i => X (past i) ω) MeasurableSpace.pi]
        (X (past i)) := (measurable_pi_apply (X := fun _ : ι => ℝ) i).comp
      (comap_measurable (fun ω i => X (past i) ω))
    exact hm.comap_le
  have hind' := indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hle1) hle2
  have hce : μ[(e : Ω → ℝ) | TidyR6CondExpForecast.genSigma fun i => X (past i)] =ᵐ[μ] 0 := by
    have := condExp_indep_eq (Lp.stronglyMeasurable e).measurable.comap_le hG
      (comap_measurable (e : Ω → ℝ)).stronglyMeasurable hind'
    filter_upwards [this] with ω hω
    rw [hω, he0, Pi.zero_apply]
  -- the linear forecast is measurable for the past
  have hKS : KS ≤ lpMeas ℝ ℝ (TidyR6CondExpForecast.genSigma fun i => X (past i)) 2 μ :=
    TidyR6CondExpForecast.closure_span_le_lpMeas hG (fun i => toLpFam hm2 (past i)) fun i =>
      ((Measurable.of_comap_le (le_iSup (fun i => MeasurableSpace.comap (X (past i))
        inferInstance) i)).stronglyMeasurable.aestronglyMeasurable).congr
        (MemLp.coeFn_toLp (hm2 (past i))).symm
  have hpm : AEStronglyMeasurable[TidyR6CondExpForecast.genSigma fun i => X (past i)]
      (p : Ω → ℝ) μ :=
    mem_lpMeas_iff_aestronglyMeasurable.1 (hKS (KS.starProjection_apply_mem _))
  have hint : ∀ F : Lp ℝ 2 μ, Integrable (F : Ω → ℝ) μ := fun F =>
    (Lp.memLp F).integrable one_le_two
  have hsplit : X τ =ᵐ[μ] fun ω => p ω + e ω := by
    filter_upwards [MemLp.coeFn_toLp (hm2 τ), Lp.coeFn_sub (toLpFam hm2 τ) p] with ω h1 h2
    rw [show e ω = (toLpFam hm2 τ - p) ω from rfl, h2, Pi.sub_apply, toLpFam, h1]
    ring
  filter_upwards [condExp_congr_ae (m := TidyR6CondExpForecast.genSigma fun i => X (past i))
      hsplit, condExp_add (hint p) (hint e) (TidyR6CondExpForecast.genSigma fun i => X (past i)),
    condExp_of_aestronglyMeasurable' hG hpm (hint p), hce] with ω h1 h2 h3 h4
  rw [h1]
  have h2' : μ[fun ω => p ω + e ω | TidyR6CondExpForecast.genSigma fun i => X (past i)] ω =
      μ[(p : Ω → ℝ) | TidyR6CondExpForecast.genSigma fun i => X (past i)] ω +
        μ[(e : Ω → ℝ) | TidyR6CondExpForecast.genSigma fun i => X (past i)] ω := h2
  rw [h2', h3, h4, Pi.zero_apply, add_zero]

/-- Cochrane (2023), Online Appendix p. 597: the best linear forecast of `X_τ` from the closed
linear span of the observed values `X_{past(i)}`. -/
noncomputable def linForecast {X : T → Ω → ℝ} (hm2 : ∀ t, MemLp (X t) 2 μ) {ι : Type*}
    (past : ι → T) (τ : T) : Lp ℝ 2 μ :=
  (Submodule.span ℝ (Set.range fun i => toLpFam hm2 (past i))).topologicalClosure.starProjection
    (toLpFam hm2 τ)

/-- Cochrane (2023), Online Appendix p. 601 (tool for Granger causality): for a centered Gaussian
process, the mean-square error of the conditional-expectation forecast of `X_τ` given
`σ(X_{past(i)} : i)` equals the linear forecast error variance `‖X_τ − P_KX_τ‖²`. -/
theorem gaussian_condExp_mse {X : T → Ω → ℝ} (hX : IsGaussianProcess X μ)
    (hXm : ∀ t, Measurable (X t)) (h0 : ∀ t, ∫ ω, X t ω ∂μ = 0) (hm2 : ∀ t, MemLp (X t) 2 μ)
    {ι : Type*} (past : ι → T) (τ : T) :
    ∫ ω, (X τ ω - μ[X τ | TidyR6CondExpForecast.genSigma fun i => X (past i)] ω) ^ 2 ∂μ =
      ‖toLpFam hm2 τ - linForecast hm2 past τ‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [condExp_eq_linear_of_gaussian hX hXm h0 hm2 past τ, MemLp.coeFn_toLp (hm2 τ),
    Lp.coeFn_sub (toLpFam hm2 τ) (linForecast hm2 past τ)] with ω h1 h2 h3
  rw [h1, h3, Pi.sub_apply, toLpFam, h2]
  rfl

/-- Cochrane (2023), Online Appendix eq. (2.21), p. 601 ("debt Granger-causes surpluses"), **with
conditional expectations, for any centered Gaussian process**: if the best linear forecast of
`X_τ` from a family of observables (e.g. surpluses and debt) has strictly smaller error variance
than from another (surpluses alone) — as `InvertibilityMeasure.granger_general` proves for every
absolutely summable `a(L)` with `a(ρ) = 0` — then so does the conditional-expectation forecast
given the generated σ-algebras. -/
theorem gaussian_granger {X : T → Ω → ℝ} (hX : IsGaussianProcess X μ)
    (hXm : ∀ t, Measurable (X t)) (h0 : ∀ t, ∫ ω, X t ω ∂μ = 0) (hm2 : ∀ t, MemLp (X t) 2 μ)
    {ι₁ ι₂ : Type*} (past₁ : ι₁ → T) (past₂ : ι₂ → T) (τ : T)
    (hlt : ‖toLpFam hm2 τ - linForecast hm2 past₂ τ‖ < ‖toLpFam hm2 τ - linForecast hm2 past₁ τ‖) :
    ∫ ω, (X τ ω - μ[X τ | TidyR6CondExpForecast.genSigma fun i => X (past₂ i)] ω) ^ 2 ∂μ <
      ∫ ω, (X τ ω - μ[X τ | TidyR6CondExpForecast.genSigma fun i => X (past₁ i)] ω) ^ 2 ∂μ := by
  rw [gaussian_condExp_mse hX hXm h0 hm2, gaussian_condExp_mse hX hXm h0 hm2]
  exact pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero

/-! ### Wold and Granger with conditional expectations for Gaussian processes -/

/-- Cochrane (2023), Online Appendix pp. 597 and 600, **Wold with conditional expectations for
Gaussian processes**: for a centered Gaussian process `x` indexed by `ℤ`, the
conditional-expectation innovation `x_t − E(x_t|σ(x_{t−1}, x_{t−2}, …))` is the Wold innovation
`x_t − P_{H_{t−1}}x_t` at every date. -/
theorem gaussian_ceInnov_eq_wold {x : ℤ → Ω → ℝ} (hX : IsGaussianProcess x μ)
    (hx : ∀ t, Measurable (x t)) (h0 : ∀ t, ∫ ω, x t ω ∂μ = 0) (hx2 : ∀ t, MemLp (x t) 2 μ)
    (t : ℤ) :
    TidyR6CondExpForecast.ceInnov hx hx2 t = Wold.innov (TidyR6CondExpForecast.toL2 hx2) t := by
  have hG := TidyR6CondExpForecast.pastSigma_le hx (t - 1)
  have := TidyR6CondExpForecast.hasOrthogonalProjection_lpMeas (μ := μ) hG
  refine ((TidyR6CondExpForecast.ceInnov_eq_wold_iff hx hx2 t).2.1).2 ?_
  have heq : (lpMeas ℝ ℝ (TidyR6CondExpForecast.pastSigma x (t - 1)) 2 μ).starProjection
      (TidyR6CondExpForecast.toL2 hx2 t) =
      (Wold.past (TidyR6CondExpForecast.toL2 hx2) (t - 1)).starProjection
        (TidyR6CondExpForecast.toL2 hx2 t) := by
    refine Lp.ext ?_
    filter_upwards [TidyR6CondExpForecast.starProjection_lpMeas_ae_eq_condExp hG (hx2 t),
      condExp_eq_linear_of_gaussian hX hx h0 hx2 (fun k : ℕ => t - 1 - k) t] with ω h1 h2
    exact h1.trans h2
  rw [heq]
  exact Submodule.starProjection_apply_mem _ _

/-- Cochrane (2023), Online Appendix pp. 597 and 600, **the Wold decomposition with conditional
expectations for Gaussian processes**: for a centered, covariance-stationary Gaussian process
indexed by `ℤ`, the conditional-expectation innovations are white noise, `x_t = ∑c_je_{t−j} + d_t`
with them, and they form a martingale-difference sequence for the natural filtration. -/
theorem gaussian_wold_condExp {x : ℤ → Ω → ℝ} (hX : IsGaussianProcess x μ)
    (hx : ∀ t, Measurable (x t)) (h0 : ∀ t, ∫ ω, x t ω ∂μ = 0) (hx2 : ∀ t, MemLp (x t) 2 μ)
    {U : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 μ}
    (hU : ∀ t, U (TidyR6CondExpForecast.toL2 hx2 t) = TidyR6CondExpForecast.toL2 hx2 (t + 1)) :
    (∀ t, TidyR6CondExpForecast.ceInnov hx hx2 t =
      Wold.innov (TidyR6CondExpForecast.toL2 hx2) t) ∧
    Invertibility.Hilbert.WhiteNoise (TidyR6CondExpForecast.ceInnov hx hx2)
      (‖TidyR6CondExpForecast.ceInnov hx hx2 0‖ ^ 2) ∧
    (∀ t, HasSum (fun j : ℕ => Wold.woldCoeff (TidyR6CondExpForecast.toL2 hx2) j •
      TidyR6CondExpForecast.ceInnov hx hx2 (t - j))
      (TidyR6CondExpForecast.toL2 hx2 t - Wold.detPart (TidyR6CondExpForecast.toL2 hx2) t)) ∧
    (∀ t, μ[fun ω => x t ω - μ[x t | TidyR6CondExpForecast.pastSigma x (t - 1)] ω |
      TidyR6CondExpForecast.pastSigma x (t - 1)] =ᵐ[μ] 0) := by
  refine TidyR6CondExpForecast.wold_decomposition_condExp hx hx2 hU fun t => ?_
  have := TidyR6CondExpForecast.hasOrthogonalProjection_lpMeas (μ := μ)
    (TidyR6CondExpForecast.pastSigma_le hx (t - 1))
  have h := ((TidyR6CondExpForecast.ceInnov_eq_wold_iff hx hx2 t).2.1).1
    (gaussian_ceInnov_eq_wold hX hx h0 hx2 t)
  exact h

/-! ### The i.i.d. Gaussian economy and the non-invertible surplus -/

namespace GaussEconomy

open Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID
open Cochrane.DebtDeficitsInflation.TidyR6CondExpForecast
open Cochrane.DebtDeficitsInflation.TidyR6CondExpForecast.IID
open Cochrane.DebtDeficitsInflation.InvertibilityMeasure
open Cochrane.DebtDeficitsInflation.Invertibility
open Cochrane.DebtDeficitsInflation.Invertibility.Hilbert
open Cochrane.DebtDeficitsInflation.Innovations (gen)
open scoped NNReal

/-- Cochrane (2023), p. 102 and Online Appendix p. 597 (Gaussian shocks): the law `N(0, σ²)` as a
probability measure. -/
noncomputable def gaussLaw (v : ℝ≥0) : ProbabilityMeasure ℝ := ⟨gaussianReal 0 v, inferInstance⟩

/-- Cochrane (2023), p. 102 (tool): the Gaussian shock has mean zero. -/
theorem gauss_mean (v : ℝ≥0) : ∫ x, x ∂(gaussLaw v : Measure ℝ) = 0 :=
  integral_id_gaussianReal

/-- Cochrane (2023), p. 102 (tool): the Gaussian shock is square integrable. -/
theorem gauss_memLp (v : ℝ≥0) : MemLp (fun x : ℝ => x) 2 (gaussLaw v : Measure ℝ) :=
  memLp_id_gaussianReal' 2 (by norm_num)

/-- Cochrane (2023), p. 102 (tool): the Gaussian shock has variance `σ²`. -/
theorem gauss_var (v : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussLaw v : Measure ℝ) = v := by
  have h := variance_eq_sub (gauss_memLp v)
  have hv : Var[fun x : ℝ => x; (gaussLaw v : Measure ℝ)] = v := variance_fun_id_gaussianReal
  rw [hv, gauss_mean] at h
  rw [show (fun x : ℝ => x) ^ 2 = fun x => x ^ 2 from rfl] at h
  linarith

/-- Cochrane (2023), p. 102 (tool): the Gaussian shock is integrable. -/
theorem gauss_integrable (v : ℝ≥0) : Integrable (fun x : ℝ => x) (gaussLaw v : Measure ℝ) :=
  (gauss_memLp v).integrable one_le_two

/-- Cochrane (2023), p. 102 (tool): the shocks of the Gaussian economy are square integrable. -/
theorem memLp_eps (v : ℝ≥0) (t : ℤ) : MemLp (eps t) 2 (iidSystem (gaussLaw v)).μ :=
  (gauss_memLp v).comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ => (gaussLaw v : Measure ℝ)) (Equiv.intEquivNat t))

/-- Cochrane (2023), p. 102 (tool): the coordinates of the Gaussian economy are square
integrable. -/
theorem memLp_coord (v : ℝ≥0) (i : ℕ) :
    MemLp (fun ω : ℕ → ℝ => ω i) 2 (iidSystem (gaussLaw v)).μ :=
  (gauss_memLp v).comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ => (gaussLaw v : Measure ℝ)) i)

/-- Cochrane (2023), p. 102 (tool): the MA(1) surplus of the Gaussian economy is square
integrable. -/
theorem memLp_surp (v : ℝ≥0) (θ : ℝ) (t : ℤ) : MemLp (surp θ t) 2 (iidSystem (gaussLaw v)).μ :=
  (memLp_eps v t).sub ((memLp_eps v (t - 1)).const_mul θ)

/-- Cochrane (2023), p. 102: the i.i.d. Gaussian shocks form a Gaussian process. -/
theorem isGaussianProcess_coord (v : ℝ≥0) :
    IsGaussianProcess (fun (i : ℕ) (ω : ℕ → ℝ) => ω i) (iidSystem (gaussLaw v)).μ := by
  refine ⟨fun I => ?_⟩
  have hind : iIndepFun (fun (i : I) (ω : ℕ → ℝ) => ω i) (iidSystem (gaussLaw v)).μ :=
    (iIndepFun_infinitePi (P := fun _ => (gaussLaw v : Measure ℝ)) (X := fun _ => id)
      (fun _ => measurable_id)).precomp Subtype.val_injective
  have hg : ∀ i : I, HasGaussianLaw (fun ω : ℕ → ℝ => ω i) (iidSystem (gaussLaw v)).μ :=
    fun i => HasLaw.hasGaussianLaw (μ := gaussianReal 0 v)
      ⟨(measurable_pi_apply _).aemeasurable,
        (measurePreserving_eval_infinitePi (fun _ => (gaussLaw v : Measure ℝ)) (i : ℕ)).map_eq⟩
  exact iIndepFun.hasGaussianLaw hg hind

/-- Cochrane (2023), p. 102: the MA(1) surplus of the Gaussian economy is a centered Gaussian
process (every finite family of surpluses is jointly Gaussian). -/
theorem isGaussianProcess_surp (v : ℝ≥0) (θ : ℝ) :
    IsGaussianProcess (surp θ) (iidSystem (gaussLaw v)).μ ∧
      ∀ t, ∫ ω, surp θ t ω ∂(iidSystem (gaussLaw v)).μ = 0 := by
  have hK := isGaussianProcess_closure (isGaussianProcess_coord v) (memLp_coord v)
  set K := (Submodule.span ℝ (Set.range (toLpFam (memLp_coord v)))).topologicalClosure
  have hmem : ∀ i, toLpFam (memLp_coord v) i ∈ K := fun i =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  let sL : ℤ → K := fun k => ⟨toLpFam (memLp_coord v) (Equiv.intEquivNat k) -
    θ • toLpFam (memLp_coord v) (Equiv.intEquivNat (k - 1)),
    K.sub_mem (hmem _) (K.smul_mem _ (hmem _))⟩
  refine ⟨(hK.comp_right sL).congr fun k => ?_, fun t => ?_⟩
  · filter_upwards [Lp.coeFn_sub (toLpFam (memLp_coord v) (Equiv.intEquivNat k))
      (θ • toLpFam (memLp_coord v) (Equiv.intEquivNat (k - 1))),
      Lp.coeFn_smul θ (toLpFam (memLp_coord v) (Equiv.intEquivNat (k - 1))),
      MemLp.coeFn_toLp (memLp_coord v (Equiv.intEquivNat k)),
      MemLp.coeFn_toLp (memLp_coord v (Equiv.intEquivNat (k - 1)))] with ω h1 h2 h3 h4
    change (toLpFam (memLp_coord v) (Equiv.intEquivNat k) -
      θ • toLpFam (memLp_coord v) (Equiv.intEquivNat (k - 1)) : Lp ℝ 2 _) ω = surp θ k ω
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul, toLpFam, toLpFam, h3, h4]
    rfl
  · have h1 := integrable_eps (gauss_integrable v) t
    have h2 := (integrable_eps (gauss_integrable v) (t - 1)).const_mul θ
    have hz : ∀ s : ℤ, ∫ ω, eps s ω ∂(iidSystem (gaussLaw v)).μ = 0 := fun s => by
      have := integral_shock_fun (gaussLaw v) (Equiv.intEquivNat s) (f := id) measurable_id
      simpa [eps, gauss_mean] using this
    simp only [surp]
    rw [integral_sub h1 h2, integral_const_mul, hz, hz, mul_zero, sub_zero]

/-- Cochrane (2023), p. 102 and Online Appendix p. 597: the Gaussian shocks are white noise with
variance `σ²` in `L²`. -/
theorem gauss_whiteNoise (v : ℝ≥0) :
    WhiteNoise (fun t => (memLp_eps v t).toLp (eps t)) v := by
  intro t u
  rw [L2.inner_def]
  have hcongr : (fun ω => ⟪((memLp_eps v t).toLp (eps t) : (ℕ → ℝ) → ℝ) ω,
      ((memLp_eps v u).toLp (eps u) : (ℕ → ℝ) → ℝ) ω⟫) =ᵐ[(iidSystem (gaussLaw v)).μ]
      fun ω => ω (Equiv.intEquivNat t) * ω (Equiv.intEquivNat u) := by
    filter_upwards [MemLp.coeFn_toLp (memLp_eps v t), MemLp.coeFn_toLp (memLp_eps v u)]
      with ω h1 h2
    rw [h1, h2]
    simp only [eps, RCLike.inner_apply, conj_trivial]
    ring
  rw [integral_congr_ae hcongr]
  by_cases htu : t = u
  · subst htu
    simp only [↓reduceIte]
    have h := integral_shock_fun (gaussLaw v) (Equiv.intEquivNat t) (f := fun x => x ^ 2)
      (measurable_id.pow_const 2)
    rw [gauss_var] at h
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  · simp only [htu, ↓reduceIte]
    exact InvertibilityMeasureL2.integral_coord_mul ((Equiv.intEquivNat).injective.ne htu)
      (gauss_mean v)

/-- Cochrane (2023), p. 102 (tool): the `L²` class of the Gaussian MA(1) surplus is the `L²`
moving average `(1 − θL)·1` of the Gaussian shocks. -/
theorem toL2_surp (v : ℝ≥0) (θ : ℝ) :
    toL2 (memLp_surp v θ) = maProc (factorCoeff θ (fun k => if k = 0 then 1 else 0))
      (fun t => (memLp_eps v t).toLp (eps t)) := by
  funext t
  rw [factorCoeff_delta, maProc_armaCoeff_zero (gauss_whiteNoise v)]
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_surp v θ t),
    Lp.coeFn_sub ((memLp_eps v t).toLp (eps t)) (θ • (memLp_eps v (t - 1)).toLp (eps (t - 1))),
    Lp.coeFn_smul θ ((memLp_eps v (t - 1)).toLp (eps (t - 1))),
    MemLp.coeFn_toLp (memLp_eps v t), MemLp.coeFn_toLp (memLp_eps v (t - 1))]
    with ω h1 h2 h3 h4 h5
  rw [toL2, h1, maOne, h2, Pi.sub_apply, h3, Pi.smul_apply, smul_eq_mul, h4, h5]
  rfl

/-- Cochrane (2023), p. 102 ("`v_t = −ρ⁻¹ε_t`"): the value of debt for the MA(1) surplus
`s_t = e_t − θe_{t−1}`, `v_t = −θe_t` (the Hansen–Sargent value,
`InvertibilityMeasure.hsCoeff_factor`). -/
def debt (θ : ℝ) (t : ℤ) (ω : ℕ → ℝ) : ℝ := -θ * eps t ω

/-- Cochrane (2023), §4.3, p. 102, and Online Appendix pp. 597–601, **Wold, non-invertibility
and Granger causality with conditional expectations, for Gaussian shocks**. In the i.i.d.
`N(0, σ²)` economy (`σ² > 0`) with the book's `a(ρ) = 0` surplus `s_t = e_t − θe_{t−1}`,
`θ = ρ⁻¹`, `|θ| > 1`: (i) `a(ρ) = 0`; (ii) `E(s_{t+1}|σ(s_t, s_{t−1}, …))` is a.e. the best
linear forecast; (iii) its mean-square error is `θ²σ²`; (iv) the shock `e_t` is not a.e. a
measurable function of the surplus history (non-invertibility holds for σ-algebras, unlike for
coin shocks, `TidyR6CondExpForecast.Coin.coin_condExp_beats_linear`); (v) adding the value of
debt `v_t = −θe_t` to the information, `E(s_{t+1}|σ(s, v history)) = −θe_t` with mean-square
error `σ² < θ²σ²` (debt Granger-causes surpluses); (vi) at every date the
conditional-expectation innovation is the Wold innovation. -/
theorem gaussian_noninvertible_condExp {v : ℝ≥0} (hv : (v : ℝ) ≠ 0) {θ : ℝ} (hθ : 1 < |θ|)
    (t : ℤ) :
    gen (factorCoeff θ (fun k => if k = 0 then 1 else 0)) θ⁻¹ = 0 ∧
    ((iidSystem (gaussLaw v)).μ[surp θ (t + 1) | pastSigma (surp θ) t]
      =ᵐ[(iidSystem (gaussLaw v)).μ]
      (((Submodule.span ℝ (Set.range fun k : ℕ => toL2 (memLp_surp v θ) (t - k))).topologicalClosure
        |>.starProjection (toL2 (memLp_surp v θ) (t + 1)) : Lp ℝ 2 _) : (ℕ → ℝ) → ℝ)) ∧
    ∫ ω, (surp θ (t + 1) ω - (iidSystem (gaussLaw v)).μ[surp θ (t + 1) | pastSigma (surp θ) t] ω)
      ^ 2 ∂(iidSystem (gaussLaw v)).μ = θ ^ 2 * v ∧
    ¬ AEStronglyMeasurable[pastSigma (surp θ) t] (eps t) (iidSystem (gaussLaw v)).μ ∧
    ((iidSystem (gaussLaw v)).μ[surp θ (t + 1) | genSigma (Sum.elim
      (fun k : ℕ => surp θ (t - k)) (fun k : ℕ => debt θ (t - k)))] =ᵐ[(iidSystem (gaussLaw v)).μ]
      fun ω => -θ * eps t ω) ∧
    ∫ ω, (surp θ (t + 1) ω - (iidSystem (gaussLaw v)).μ[surp θ (t + 1) | genSigma (Sum.elim
      (fun k : ℕ => surp θ (t - k)) (fun k : ℕ => debt θ (t - k)))] ω) ^ 2
      ∂(iidSystem (gaussLaw v)).μ = v ∧
    (v : ℝ) < θ ^ 2 * v ∧
    ∀ τ, ceInnov (measurable_surp θ) (memLp_surp v θ) τ = Wold.innov (toL2 (memLp_surp v θ)) τ := by
  have hθ0 : θ ≠ 0 := by intro h; rw [h, abs_zero] at hθ; linarith
  have hδ : Summable (fun k : ℕ => |(if k = 0 then (1 : ℝ) else 0)|) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by simp_all
  have he := gauss_whiteNoise v
  obtain ⟨-, -, -, -, hgen, -, -, -, -⟩ := wold_factor he hv hθ hδ (by simp) recoverable_delta t
  obtain ⟨-, hPS, -, hlt⟩ := granger_factor he hv hθ hδ (by simp) recoverable_delta t
  rw [← toL2_surp v θ] at hPS
  obtain ⟨hG, h0⟩ := isGaussianProcess_surp v θ
  have hlin := condExp_eq_linear_of_gaussian hG (measurable_surp θ) h0 (memLp_surp v θ)
    (fun k : ℕ => t - k) (t + 1)
  have hwold : ∀ τ, ceInnov (measurable_surp θ) (memLp_surp v θ) τ =
      Wold.innov (toL2 (memLp_surp v θ)) τ :=
    gaussian_ceInnov_eq_wold hG (measurable_surp θ) h0 (memLp_surp v θ)
  have hmse : ∫ ω, (surp θ (t + 1) ω - (iidSystem (gaussLaw v)).μ[surp θ (t + 1) |
      pastSigma (surp θ) t] ω) ^ 2 ∂(iidSystem (gaussLaw v)).μ = θ ^ 2 * v := by
    have hn : ‖ceInnov (measurable_surp θ) (memLp_surp v θ) (t + 1)‖ ^ 2 = θ ^ 2 * v := by
      rw [hwold]
      simpa [Wold.innov, Wold.past_eq_pastSpan] using hPS
    rw [← hn, norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [ceInnov_ae_eq (measurable_surp θ) (memLp_surp v θ) (t + 1)] with ω hω
    rw [hω, add_sub_cancel_right]
  -- debt reveals the shock
  set Y : ℕ ⊕ ℕ → (ℕ → ℝ) → ℝ := Sum.elim (fun k : ℕ => surp θ (t - k))
    (fun k : ℕ => debt θ (t - k))
  have hYm : ∀ i, Measurable (Y i) := fun i => by
    rcases i with k | k
    · exact measurable_surp θ _
    · exact (measurable_eps _).const_mul _
  have hYa : ∀ i, Measurable[avoidSigma (Equiv.intEquivNat (t + 1))] (Y i) := fun i => by
    rcases i with k | k
    · exact measurable_surp_avoid θ t k
    · have h1 : Equiv.intEquivNat (t - k) ≠ Equiv.intEquivNat (t + 1) :=
        (Equiv.intEquivNat).injective.ne (by omega)
      exact (measurable_avoid h1).const_mul _
  have hkY : AEStronglyMeasurable[genSigma Y] (eps t) (iidSystem (gaussLaw v)).μ := by
    have hd : Measurable[genSigma Y] (Y (Sum.inr 0)) :=
      Measurable.of_comap_le (le_iSup (fun i => MeasurableSpace.comap (Y i) inferInstance)
        (Sum.inr 0))
    have : eps t = fun ω => -θ⁻¹ * Y (Sum.inr 0) ω := by
      funext ω
      simp only [Y, Sum.elim_inr, debt, Nat.cast_zero, sub_zero]
      field_simp
    rw [this]
    exact (hd.const_mul _).stronglyMeasurable.aestronglyMeasurable
  obtain ⟨hceY, hmseY⟩ := condExp_surp_of_known (gauss_integrable v) (gauss_mean v) θ hYm hYa
    hkY
  rw [gauss_var] at hmseY
  refine ⟨hgen, hlin, hmse, fun hk => ?_, hceY, hmseY, by simpa using hlt, hwold⟩
  obtain ⟨-, hm2⟩ := condExp_surp_of_known (gauss_integrable v) (gauss_mean v) θ
    (fun k : ℕ => measurable_surp θ (t - k)) (measurable_surp_avoid θ t) hk
  rw [gauss_var] at hm2
  have : (v : ℝ) = θ ^ 2 * v := hm2.symm.trans hmse
  linarith

end GaussEconomy

end Cochrane.DebtDeficitsInflation.TidyR6GaussianForecast
