/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.Wold
import Mathlib.Probability.ConditionalExpectation

/-!
# Conditional-expectation forecasts versus linear forecasts: Wold and Granger with `condExp`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, p. 102, and Online
Appendix Chapter 2, §§2.1.4–2.1.6, pp. 597–601 (the Wold representation, "the shock is not
recoverable from the surplus history", "debt Granger-causes surpluses").

`Wold` and `InvertibilityMeasure` prove these statements for best linear forecasts (orthogonal
projections on closed linear spans in `L²`). Here they are related to Mathlib conditional
expectations given the σ-algebra of the past.

* **The general statement.** The conditional expectation `E(x|𝓖)` of `x ∈ L²` is the orthogonal
  projection on the closed subspace `L²(𝓖)` (Mathlib's `lpMeas`, `condExpL2`). Any closed linear
  span `K` of `𝓖`-measurable variables lies in `L²(𝓖)`, so the conditional-expectation forecast
  error is never larger than the linear one, with the Pythagorean decomposition
  `‖x − P_Kx‖² = ‖x − E(x|𝓖)‖² + ‖E(x|𝓖) − P_Kx‖²`, and the two forecasts coincide iff their
  mean-square errors are equal iff `E(x|𝓖) ∈ K` (`condExp_beats_linear`).
* **Conditional-expectation innovations form a martingale-difference sequence**
  (`ceInnov_mds`, `ceInnov_orthogonal`), orthogonal to the whole past, and for a process indexed
  by `ℤ` with its natural filtration they are the Wold innovations iff the linear and
  conditional forecasts coincide (`ceInnov_eq_wold_iff`); then the Wold decomposition holds with
  conditional-expectation innovations (`wold_decomposition_condExp`).
* **Counterexample (non-Gaussian shocks).** For fair `±1` coin shocks and the book's `a(ρ) = 0`
  surplus `s_t = e_t − ρ⁻¹e_{t−1}` (`0 < |ρ| < 1`), the shock is a measurable function of the
  current surplus alone, `e_t = g(s_t)` (`Coin.coin_shock_eq`), so the conditional-expectation
  forecast `E(s_{t+1}|σ(s_t, s_{t−1}, …)) = −ρ⁻¹e_t` has error variance `1`, while the best
  linear forecast has error variance `ρ⁻² > 1` and the shock is not in the closed linear span
  (`Coin.coin_condExp_beats_linear`). The Wold innovation is therefore not
  `x_t − E(x_t|σ(x_{t−1}, …))` in general, and non-invertibility is a statement about linear
  forecasts only.
-/

namespace Cochrane.DebtDeficitsInflation.TidyR6CondExpForecast

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

/-! ### Nested projections -/

namespace Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Cochrane (2023), Online Appendix p. 597 (tool): for closed subspaces `K ≤ M` with orthogonal
projections, `‖x − P_Kx‖² = ‖x − P_Mx‖² + ‖P_Mx − P_Kx‖²`. -/
theorem nested_pythagoras {K M : Submodule ℝ H} [K.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] (hKM : K ≤ M) (x : H) :
    ‖x - K.starProjection x‖ ^ 2 =
      ‖x - M.starProjection x‖ ^ 2 + ‖M.starProjection x - K.starProjection x‖ ^ 2 := by
  have h1 : x - M.starProjection x ∈ Mᗮ := M.sub_starProjection_mem_orthogonal x
  have h2 : M.starProjection x - K.starProjection x ∈ M :=
    M.sub_mem (M.starProjection_apply_mem x) (hKM (K.starProjection_apply_mem x))
  have h0 : ⟪x - M.starProjection x, M.starProjection x - K.starProjection x⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal h2 h1
  rw [show x - K.starProjection x =
    (x - M.starProjection x) + (M.starProjection x - K.starProjection x) by abel]
  simpa only [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_real h0

/-- Cochrane (2023), Online Appendix p. 597 (tool): for `K ≤ M`, the projection on the larger
subspace is the better forecast, and the two coincide iff `P_Mx ∈ K` iff the errors have the same
norm. -/
theorem nested_projection_eq_iff {K M : Submodule ℝ H} [K.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] (hKM : K ≤ M) (x : H) :
    ‖x - M.starProjection x‖ ≤ ‖x - K.starProjection x‖ ∧
    (M.starProjection x = K.starProjection x ↔ M.starProjection x ∈ K) ∧
    (M.starProjection x = K.starProjection x ↔
      ‖x - M.starProjection x‖ = ‖x - K.starProjection x‖) := by
  have hp := nested_pythagoras hKM x
  refine ⟨?_, ⟨fun h => h ▸ K.starProjection_apply_mem x, fun h => ?_⟩, ⟨fun h => by rw [h],
    fun h => ?_⟩⟩
  · have : ‖x - M.starProjection x‖ ^ 2 ≤ ‖x - K.starProjection x‖ ^ 2 := by
      rw [hp]; nlinarith [sq_nonneg ‖M.starProjection x - K.starProjection x‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  · have hperp : x - M.starProjection x ∈ Kᗮ :=
      Submodule.orthogonal_le hKM (M.sub_starProjection_mem_orthogonal x)
    exact (Submodule.eq_starProjection_of_mem_orthogonal h hperp).symm
  · rw [h] at hp
    have h0 : ‖M.starProjection x - K.starProjection x‖ = 0 := by
      nlinarith [sq_nonneg ‖M.starProjection x - K.starProjection x‖,
        norm_nonneg (M.starProjection x - K.starProjection x)]
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)

end Hilbert

/-! ### Conditional expectations as projections in `L²` -/

variable {Ω : Type*} {G : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Cochrane (2023), Online Appendix p. 597 (`E(s_t|s_{t−1}, …)` as a conditional expectation):
the closed subspace `L²(𝓖)` of `𝓖`-measurable square-integrable variables (Mathlib's
`lpMeas`) has an orthogonal projection. -/
theorem hasOrthogonalProjection_lpMeas (hG : G ≤ mΩ) :
    (lpMeas ℝ ℝ G 2 μ).HasOrthogonalProjection := by
  have : Fact (G ≤ mΩ) := ⟨hG⟩
  infer_instance

/-- Cochrane (2023), Online Appendix p. 597: the projection on `L²(𝓖)` is Mathlib's conditional
expectation, `P_{L²(𝓖)}x = E(x|𝓖)` a.e. -/
theorem starProjection_lpMeas_ae_eq_condExp (hG : G ≤ mΩ) {f : Ω → ℝ}
    (hf : MemLp f 2 μ) :
    haveI := hasOrthogonalProjection_lpMeas (μ := μ) hG
    ((lpMeas ℝ ℝ G 2 μ).starProjection (hf.toLp f) : Ω → ℝ) =ᵐ[μ] μ[f | G] := by
  have : Fact (G ≤ mΩ) := ⟨hG⟩
  exact hf.condExpL2_ae_eq_condExp hG

omit [IsProbabilityMeasure μ] in
/-- Cochrane (2023), Online Appendix p. 597 (tool): a closed linear span of `𝓖`-measurable
square-integrable variables lies in `L²(𝓖)`. -/
theorem closure_span_le_lpMeas (hG : G ≤ mΩ) {ι : Type*}
    (y : ι → Lp ℝ 2 μ) (hy : ∀ i, AEStronglyMeasurable[G] (y i : Ω → ℝ) μ) :
    (Submodule.span ℝ (Set.range y)).topologicalClosure ≤ lpMeas ℝ ℝ G 2 μ := by
  have : Fact (G ≤ mΩ) := ⟨hG⟩
  refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_aestronglyMeasurable hG)
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact mem_lpMeas_iff_aestronglyMeasurable.2 (hy i)

omit [IsProbabilityMeasure μ] in
/-- Cochrane (2023), §4.3, p. 102, and Online Appendix pp. 597–601, **the general statement**:
let `K` be any closed subspace of `L²(𝓖)` (e.g. the closed linear span of the observed past).
For every `F ∈ L²`, with `c = E(F|𝓖)` (the projection on `L²(𝓖)`, a.e. Mathlib's `condExp`) and
`p = P_KF` (the best linear forecast):
`‖F − p‖² = ‖F − c‖² + ‖c − p‖²`; so `‖F − c‖ ≤ ‖F − p‖`, and `c = p` iff `c ∈ K` iff the two
mean-square errors are equal. -/
theorem condExp_beats_linear (hG : G ≤ mΩ) (K : Submodule ℝ (Lp ℝ 2 μ))
    [K.HasOrthogonalProjection] (hK : K ≤ lpMeas ℝ ℝ G 2 μ) (F : Lp ℝ 2 μ) :
    haveI := hasOrthogonalProjection_lpMeas (μ := μ) hG
    ‖F - K.starProjection F‖ ^ 2 = ‖F - (lpMeas ℝ ℝ G 2 μ).starProjection F‖ ^ 2 +
        ‖(lpMeas ℝ ℝ G 2 μ).starProjection F - K.starProjection F‖ ^ 2 ∧
      ‖F - (lpMeas ℝ ℝ G 2 μ).starProjection F‖ ≤ ‖F - K.starProjection F‖ ∧
      ((lpMeas ℝ ℝ G 2 μ).starProjection F = K.starProjection F ↔
        (lpMeas ℝ ℝ G 2 μ).starProjection F ∈ K) ∧
      ((lpMeas ℝ ℝ G 2 μ).starProjection F = K.starProjection F ↔
        ‖F - (lpMeas ℝ ℝ G 2 μ).starProjection F‖ = ‖F - K.starProjection F‖) := by
  have := hasOrthogonalProjection_lpMeas (μ := μ) hG
  obtain ⟨h1, h2, h3⟩ := Hilbert.nested_projection_eq_iff hK F
  exact ⟨Hilbert.nested_pythagoras hK F, h1, h2, h3⟩

/-! ### Conditional-expectation innovations: a martingale-difference sequence -/

/-- Cochrane (2023), Online Appendix p. 597 ("`u_t = s_t − E(s_t|s_{t−1}, …)`" read with
conditional expectations): for any filtration `𝓕` and integrable `x_{t+1}`, the forecast error
`x_{t+1} − E(x_{t+1}|𝓕_t)` is `𝓕_{t+1}`-measurable when `x` is adapted, and has conditional mean
zero given `𝓕_t`: the conditional-expectation innovations form a martingale-difference
sequence. -/
theorem ceInnov_mds (𝓕 : Filtration ℕ mΩ) {x : ℕ → Ω → ℝ} (hx : StronglyAdapted 𝓕 x)
    (hi : ∀ t, Integrable (x t) μ) (t : ℕ) :
    StronglyMeasurable[𝓕 (t + 1)] (x (t + 1) - μ[x (t + 1) | 𝓕 t]) ∧
    μ[x (t + 1) - μ[x (t + 1) | 𝓕 t] | 𝓕 t] =ᵐ[μ] 0 := by
  refine ⟨(hx (t + 1)).sub (stronglyMeasurable_condExp.mono (𝓕.mono (Nat.le_succ t))), ?_⟩
  filter_upwards [condExp_sub (hi (t + 1)) integrable_condExp (𝓕 t),
    (condExp_condExp_of_le (le_refl (𝓕 t)) (𝓕.le t) : μ[μ[x (t + 1) | 𝓕 t] | 𝓕 t] =ᵐ[μ] _)]
    with ω h1 h2
  rw [h1, Pi.sub_apply, h2, sub_self, Pi.zero_apply]

omit [IsProbabilityMeasure μ] in
/-- Cochrane (2023), Online Appendix p. 597: in `L²`, the conditional-expectation innovation is
orthogonal to every square-integrable function of the past, `x − E(x|𝓖) ⟂ L²(𝓖)`; in particular
it is uncorrelated with every earlier innovation and with the closed linear span of the past. -/
theorem ceInnov_orthogonal (hG : G ≤ mΩ) (F : Lp ℝ 2 μ) :
    haveI := hasOrthogonalProjection_lpMeas (μ := μ) hG
    F - (lpMeas ℝ ℝ G 2 μ).starProjection F ∈ (lpMeas ℝ ℝ G 2 μ)ᗮ := by
  have := hasOrthogonalProjection_lpMeas (μ := μ) hG
  exact (lpMeas ℝ ℝ G 2 μ).sub_starProjection_mem_orthogonal F

/-! ### Processes indexed by `ℤ`: the natural filtration and the Wold innovations -/

/-- Cochrane (2023), Online Appendix p. 597 (`σ(s_t, s_{t−1}, …)`, `σ(s, v)`): the σ-algebra
generated by a family of real random variables. -/
abbrev genSigma {ι : Type*} (Y : ι → Ω → ℝ) : MeasurableSpace Ω :=
  ⨆ i, MeasurableSpace.comap (Y i) inferInstance

/-- Cochrane (2023), Online Appendix p. 597 (`σ(s_t, s_{t−1}, …)`): the σ-algebra generated by the
current and past values of a process. -/
abbrev pastSigma (x : ℤ → Ω → ℝ) (t : ℤ) : MeasurableSpace Ω :=
  genSigma fun k : ℕ => x (t - k)

omit [IsProbabilityMeasure μ] in
/-- Cochrane (2023), Online Appendix p. 597 (tool): for measurable `x` the past σ-algebra is a
sub-σ-algebra. -/
theorem pastSigma_le {x : ℤ → Ω → ℝ} (hx : ∀ t, Measurable (x t)) (t : ℤ) :
    pastSigma x t ≤ mΩ :=
  iSup_le fun k => (hx (t - k)).comap_le

omit mΩ [IsProbabilityMeasure μ] in
/-- Cochrane (2023), Online Appendix p. 597 (tool): `x_{t−k}` is measurable for the past
σ-algebra at `t`. -/
theorem measurable_pastSigma (x : ℤ → Ω → ℝ) (t : ℤ) (k : ℕ) :
    Measurable[pastSigma x t] (x (t - k)) :=
  Measurable.of_comap_le (le_iSup (fun k : ℕ => MeasurableSpace.comap (x (t - k))
    inferInstance) k)

/-- Cochrane (2023), Online Appendix p. 597: the process as a sequence in `L²`. -/
noncomputable def toL2 {x : ℤ → Ω → ℝ} (hx2 : ∀ t, MemLp (x t) 2 μ) (t : ℤ) : Lp ℝ 2 μ :=
  (hx2 t).toLp (x t)

omit [IsProbabilityMeasure μ] in
/-- Cochrane (2023), Online Appendix p. 597: the closed linear span of the past, `H_t`, lies in
`L²(σ(x_t, x_{t−1}, …))`. -/
theorem past_le_lpMeas {x : ℤ → Ω → ℝ} (hx : ∀ t, Measurable (x t))
    (hx2 : ∀ t, MemLp (x t) 2 μ) (t : ℤ) :
    Wold.past (toL2 hx2) t ≤ lpMeas ℝ ℝ (pastSigma x t) 2 μ :=
  closure_span_le_lpMeas (pastSigma_le hx t) (fun k : ℕ => toL2 hx2 (t - k)) fun k =>
    ((measurable_pastSigma x t k).stronglyMeasurable.aestronglyMeasurable).congr
      (MemLp.coeFn_toLp _).symm

/-- Cochrane (2023), Online Appendix p. 597 ("`u_t = s_t − E(s_t|s_{t−1}, s_{t−2}, …)`" with
conditional expectations): the conditional-expectation innovation, as an element of `L²`. -/
noncomputable def ceInnov {x : ℤ → Ω → ℝ} (hx : ∀ t, Measurable (x t))
    (hx2 : ∀ t, MemLp (x t) 2 μ) (t : ℤ) : Lp ℝ 2 μ :=
  haveI := hasOrthogonalProjection_lpMeas (μ := μ) (pastSigma_le hx (t - 1))
  toL2 hx2 t - (lpMeas ℝ ℝ (pastSigma x (t - 1)) 2 μ).starProjection (toL2 hx2 t)

/-- Cochrane (2023), Online Appendix p. 597: `ceInnov` is a.e. `x_t − E(x_t|σ(x_{t−1}, …))` with
Mathlib's `condExp`. -/
theorem ceInnov_ae_eq {x : ℤ → Ω → ℝ} (hx : ∀ t, Measurable (x t))
    (hx2 : ∀ t, MemLp (x t) 2 μ) (t : ℤ) :
    (ceInnov hx hx2 t : Ω → ℝ) =ᵐ[μ] fun ω => x t ω - μ[x t | pastSigma x (t - 1)] ω := by
  have := hasOrthogonalProjection_lpMeas (μ := μ) (pastSigma_le hx (t - 1))
  filter_upwards [Lp.coeFn_sub (toL2 hx2 t)
      ((lpMeas ℝ ℝ (pastSigma x (t - 1)) 2 μ).starProjection (toL2 hx2 t)),
    MemLp.coeFn_toLp (hx2 t), starProjection_lpMeas_ae_eq_condExp (pastSigma_le hx (t - 1))
      (hx2 t)] with ω h1 h2 h3
  simp only [ceInnov]
  rw [h1, Pi.sub_apply, toL2, h2, h3]

omit [IsProbabilityMeasure μ] in
/-- Cochrane (2023), Online Appendix pp. 597 and 600, **Wold with conditional expectations**: the
conditional-expectation innovation never has a larger norm than the Wold (linear) innovation,
`‖x_t − E(x_t|σ(past))‖ ≤ ‖x_t − P_{H_{t−1}}x_t‖`, and the two innovations are equal iff the
conditional forecast lies in the closed linear span `H_{t−1}` iff the two forecast errors have
the same variance. -/
theorem ceInnov_eq_wold_iff {x : ℤ → Ω → ℝ} (hx : ∀ t, Measurable (x t))
    (hx2 : ∀ t, MemLp (x t) 2 μ) (t : ℤ) :
    haveI := hasOrthogonalProjection_lpMeas (μ := μ) (pastSigma_le hx (t - 1))
    ‖ceInnov hx hx2 t‖ ≤ ‖Wold.innov (toL2 hx2) t‖ ∧
    (ceInnov hx hx2 t = Wold.innov (toL2 hx2) t ↔
      (lpMeas ℝ ℝ (pastSigma x (t - 1)) 2 μ).starProjection (toL2 hx2 t) ∈
        Wold.past (toL2 hx2) (t - 1)) ∧
    (ceInnov hx hx2 t = Wold.innov (toL2 hx2) t ↔
      ‖ceInnov hx hx2 t‖ = ‖Wold.innov (toL2 hx2) t‖) := by
  have := hasOrthogonalProjection_lpMeas (μ := μ) (pastSigma_le hx (t - 1))
  obtain ⟨h1, h2, h3⟩ := Hilbert.nested_projection_eq_iff (past_le_lpMeas hx hx2 (t - 1))
    (toL2 hx2 t)
  have he : ceInnov hx hx2 t = Wold.innov (toL2 hx2) t ↔
      (lpMeas ℝ ℝ (pastSigma x (t - 1)) 2 μ).starProjection (toL2 hx2 t) =
        (Wold.past (toL2 hx2) (t - 1)).starProjection (toL2 hx2 t) := by
    simp only [ceInnov, Wold.innov]
    exact sub_right_inj
  refine ⟨h1, he.trans h2, he.trans h3⟩

/-- Cochrane (2023), Online Appendix pp. 597 and 600, **the Wold decomposition with
conditional-expectation innovations**: for a covariance-stationary `x` (`U x_t = x_{t+1}`, `U` a
linear isometry, as in `Wold.wold_decomposition`) whose conditional forecasts lie in the closed
linear span of the past at every date, the conditional-expectation innovations are the Wold
innovations; hence they are white noise, `x_t = ∑_j c_j e_{t−j} + d_t` with them, and they are a
martingale-difference sequence for the natural filtration. -/
theorem wold_decomposition_condExp {x : ℤ → Ω → ℝ} (hx : ∀ t, Measurable (x t))
    (hx2 : ∀ t, MemLp (x t) 2 μ) {U : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 μ}
    (hU : ∀ t, U (toL2 hx2 t) = toL2 hx2 (t + 1))
    (hco : ∀ t, haveI := hasOrthogonalProjection_lpMeas (μ := μ) (pastSigma_le hx (t - 1))
      (lpMeas ℝ ℝ (pastSigma x (t - 1)) 2 μ).starProjection (toL2 hx2 t) ∈
        Wold.past (toL2 hx2) (t - 1)) :
    (∀ t, ceInnov hx hx2 t = Wold.innov (toL2 hx2) t) ∧
    Invertibility.Hilbert.WhiteNoise (ceInnov hx hx2) (‖ceInnov hx hx2 0‖ ^ 2) ∧
    (∀ t, HasSum (fun j : ℕ => Wold.woldCoeff (toL2 hx2) j • ceInnov hx hx2 (t - j))
      (toL2 hx2 t - Wold.detPart (toL2 hx2) t)) ∧
    (∀ t, μ[fun ω => x t ω - μ[x t | pastSigma x (t - 1)] ω | pastSigma x (t - 1)] =ᵐ[μ] 0) := by
  have heq : ∀ t, ceInnov hx hx2 t = Wold.innov (toL2 hx2) t := fun t =>
    ((ceInnov_eq_wold_iff hx hx2 t).2.1).2 (hco t)
  have hfun : ceInnov hx hx2 = Wold.innov (toL2 hx2) := funext heq
  obtain ⟨-, -, hwn, -, -, -, -, hsum, -, -⟩ := Wold.wold_decomposition hU
  refine ⟨heq, by rw [hfun]; exact hwn, fun t => by rw [hfun]; exact hsum t, fun t => ?_⟩
  have hG := pastSigma_le hx (t - 1)
  have hi : Integrable (x t) μ := (hx2 t).integrable one_le_two
  filter_upwards [condExp_sub hi integrable_condExp (pastSigma x (t - 1)),
    (condExp_condExp_of_le (le_refl (pastSigma x (t - 1))) hG :
      μ[μ[x t | pastSigma x (t - 1)] | pastSigma x (t - 1)] =ᵐ[μ] _)] with ω h1 h2
  have h1' : μ[fun ω => x t ω - μ[x t | pastSigma x (t - 1)] ω | pastSigma x (t - 1)] ω =
      μ[x t | pastSigma x (t - 1)] ω - μ[μ[x t | pastSigma x (t - 1)] | pastSigma x (t - 1)] ω :=
    h1
  rw [h1', h2, sub_self, Pi.zero_apply]

/-! ### The i.i.d. economy: the MA(1) surplus and its σ-algebra of past surpluses -/

namespace IID

open Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID

variable {ν : ProbabilityMeasure ℝ}

/-- Cochrane (2023), p. 102 and Online Appendix p. 597: the `ℤ`-indexed i.i.d. shock
`e_t = ε_{φ(t)}` (`φ : ℤ ≃ ℕ`), as a function on `Ω = ℕ → ℝ`. -/
def eps (t : ℤ) (ω : ℕ → ℝ) : ℝ := ω (Equiv.intEquivNat t)

/-- Cochrane (2023), p. 102 ("`s_t = ε_t − ρ⁻¹ε_{t−1}`") and Online Appendix (2.4), p. 597: the
MA(1) surplus `s_t = e_t − θe_{t−1}` (`θ = ρ⁻¹`). -/
def surp (θ : ℝ) (t : ℤ) (ω : ℕ → ℝ) : ℝ := eps t ω - θ * eps (t - 1) ω

/-- Cochrane (2023), p. 102 (tool): `s_{t+1} = e_{t+1} − θe_t`. -/
theorem surp_succ (θ : ℝ) (t : ℤ) : surp θ (t + 1) = fun ω => eps (t + 1) ω - θ * eps t ω := by
  funext ω
  simp [surp]

/-- Cochrane (2023), p. 102 (tool): the shock is measurable. -/
theorem measurable_eps (t : ℤ) : Measurable (eps t) := measurable_pi_apply _

/-- Cochrane (2023), p. 102 (tool): the surplus is measurable. -/
theorem measurable_surp (θ : ℝ) (t : ℤ) : Measurable (surp θ t) :=
  (measurable_eps t).sub ((measurable_eps (t - 1)).const_mul θ)

/-- Cochrane (2023), p. 102 (tool): with an integrable law the shock is integrable. -/
theorem integrable_eps (hi : Integrable (fun x : ℝ => x) (ν : Measure ℝ)) (t : ℤ) :
    Integrable (eps t) (iidSystem ν).μ :=
  ((measurePreserving_eval_infinitePi (fun _ => (ν : Measure ℝ))
    (Equiv.intEquivNat t)).integrable_comp hi.aestronglyMeasurable).2 hi

/-- Cochrane (2023), p. 102 (tool): the σ-algebra of all shocks other than `ε_j`. -/
abbrev avoidSigma (j : ℕ) : MeasurableSpace (ℕ → ℝ) := ⨆ i ∈ {i : ℕ | i ≠ j}, coordSigma i

/-- Cochrane (2023), p. 102 (tool): `ε_j` is independent of all the other shocks. -/
theorem indep_avoid (j : ℕ) : Indep (coordSigma j) (avoidSigma j) (iidSystem ν).μ := by
  have h := indep_iSup_of_disjoint coordSigma_le (iIndep_coord ν) (S := {j})
    (T := {i : ℕ | i ≠ j}) (Set.disjoint_left.2 fun i hi hT => hT (Set.mem_singleton_iff.1 hi))
  simpa only [iSup_singleton] using h

/-- Cochrane (2023), p. 102 (tool): the other shocks are measurable for `avoidSigma j`. -/
theorem measurable_avoid {i j : ℕ} (h : i ≠ j) : Measurable[avoidSigma j] (fun ω : ℕ → ℝ => ω i) :=
  Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ {i : ℕ | i ≠ j}) => coordSigma i) i h)

/-- Cochrane (2023), p. 102: the σ-algebra of current and past MA(1) surpluses at `t` does not
involve the next shock `e_{t+1}`. -/
theorem measurable_surp_avoid (θ : ℝ) (t : ℤ) (k : ℕ) :
    Measurable[avoidSigma (Equiv.intEquivNat (t + 1))] (surp θ (t - k)) := by
  have h1 : Equiv.intEquivNat (t - k) ≠ Equiv.intEquivNat (t + 1) :=
    (Equiv.intEquivNat).injective.ne (by omega)
  have h2 : Equiv.intEquivNat (t - k - 1) ≠ Equiv.intEquivNat (t + 1) :=
    (Equiv.intEquivNat).injective.ne (by omega)
  exact (measurable_avoid h1).sub ((measurable_avoid h2).const_mul θ)

/-- Cochrane (2023), p. 102: given any information that does not involve `e_{t+1}`, the next
shock is unforecastable, `E(e_{t+1}|𝓖) = 0`. -/
theorem condExp_eps_next (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) {t : ℤ} {ι : Type*}
    {Y : ι → (ℕ → ℝ) → ℝ} (hY : ∀ i, Measurable (Y i))
    (hYa : ∀ i, Measurable[avoidSigma (Equiv.intEquivNat (t + 1))] (Y i)) :
    (iidSystem ν).μ[eps (t + 1) | genSigma Y] =ᵐ[(iidSystem ν).μ] 0 := by
  have hGle : genSigma Y ≤ MeasurableSpace.pi := iSup_le fun i => (hY i).comap_le
  have hG : genSigma Y ≤ avoidSigma (Equiv.intEquivNat (t + 1)) :=
    iSup_le fun i => (hYa i).comap_le
  have hind := indep_of_indep_of_le_right (indep_avoid (ν := ν) (Equiv.intEquivNat (t + 1))) hG
  have hsm : StronglyMeasurable[coordSigma (Equiv.intEquivNat (t + 1))] (eps (t + 1)) :=
    (Measurable.of_comap_le le_rfl).stronglyMeasurable
  have h := condExp_indep_eq (coordSigma_le _) hGle hsm hind
  have h0 : ∫ ω, eps (t + 1) ω ∂(iidSystem ν).μ = 0 := by
    have := integral_shock_fun ν (Equiv.intEquivNat (t + 1)) (f := id) measurable_id
    simpa [eps, hmean] using this
  filter_upwards [h] with ω hω
  rw [hω, h0, Pi.zero_apply]

/-- Cochrane (2023), p. 102, and Online Appendix (2.20)–(2.21), p. 601 (tool): if the information
`𝓖` reveals `e_t` and does not involve `e_{t+1}`, the conditional forecast of the MA(1) surplus is
`E(s_{t+1}|𝓖) = −θe_t`, and its error is `e_{t+1}`, with mean square `E ε²`. -/
theorem condExp_surp_of_known (hi : Integrable (fun x : ℝ => x) (ν : Measure ℝ))
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (θ : ℝ) {t : ℤ} {ι : Type*}
    {Y : ι → (ℕ → ℝ) → ℝ} (hY : ∀ i, Measurable (Y i))
    (hYa : ∀ i, Measurable[avoidSigma (Equiv.intEquivNat (t + 1))] (Y i))
    (hk : AEStronglyMeasurable[genSigma Y] (eps t) (iidSystem ν).μ) :
    (iidSystem ν).μ[surp θ (t + 1) | genSigma Y] =ᵐ[(iidSystem ν).μ]
      (fun ω => -θ * eps t ω) ∧
    ∫ ω, (surp θ (t + 1) ω - (iidSystem ν).μ[surp θ (t + 1) | genSigma Y] ω) ^ 2
      ∂(iidSystem ν).μ = ∫ x, x ^ 2 ∂(ν : Measure ℝ) := by
  have hGle : genSigma Y ≤ MeasurableSpace.pi := iSup_le fun i => (hY i).comap_le
  have hi1 := integrable_eps hi (t + 1)
  have hi0 := (integrable_eps hi t).const_mul θ
  have hk' : (iidSystem ν).μ[fun ω => θ * eps t ω | genSigma Y] =ᵐ[(iidSystem ν).μ]
      fun ω => θ * eps t ω := condExp_of_aestronglyMeasurable' hGle (hk.const_mul θ) hi0
  have hce : (iidSystem ν).μ[surp θ (t + 1) | genSigma Y] =ᵐ[(iidSystem ν).μ]
      (fun ω => -θ * eps t ω) := by
    rw [surp_succ]
    filter_upwards [condExp_sub hi1 hi0 (genSigma Y), condExp_eps_next hmean hY hYa, hk']
      with ω h1 h2 h3
    have h1' : (iidSystem ν).μ[fun ω => eps (t + 1) ω - θ * eps t ω | genSigma Y] ω =
        (iidSystem ν).μ[eps (t + 1) | genSigma Y] ω -
          (iidSystem ν).μ[fun ω => θ * eps t ω | genSigma Y] ω := h1
    rw [h1', h2, h3, Pi.zero_apply]
    ring
  refine ⟨hce, ?_⟩
  have herr : (fun ω => (surp θ (t + 1) ω - (iidSystem ν).μ[surp θ (t + 1) | genSigma Y] ω) ^ 2)
      =ᵐ[(iidSystem ν).μ] fun ω => (eps (t + 1) ω) ^ 2 := by
    filter_upwards [hce] with ω hω
    rw [hω, surp_succ]
    ring
  rw [integral_congr_ae herr]
  exact integral_shock_fun ν (Equiv.intEquivNat (t + 1)) (f := fun x => x ^ 2)
    (measurable_id.pow_const 2)

end IID

/-! ### The fair coin: the shock is a function of the current surplus -/

namespace Coin

open Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID
open Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2
open Cochrane.DebtDeficitsInflation.InvertibilityMeasure
open Cochrane.DebtDeficitsInflation.Invertibility
open Cochrane.DebtDeficitsInflation.Invertibility.Hilbert
open Cochrane.DebtDeficitsInflation.Innovations (gen)
open IID

/-- Cochrane (2023), p. 102 (counterexample): the decoding map `g(y) = 1` if `y ∈ {1 − θ, 1 + θ}`
and `−1` otherwise. -/
noncomputable def decode (θ : ℝ) (y : ℝ) : ℝ := if y = 1 - θ ∨ y = 1 + θ then 1 else -1

/-- Cochrane (2023), p. 102 (tool): the decoding map is measurable. -/
theorem measurable_decode (θ : ℝ) : Measurable (decode θ) :=
  Measurable.ite ((measurableSet_singleton _).union (measurableSet_singleton _))
    measurable_const measurable_const

/-- Cochrane (2023), p. 102 (tool): the fair coin takes the values `±1` almost surely. -/
theorem coin_ae : ∀ᵐ x ∂(coin : Measure ℝ), x = 1 ∨ x = -1 := by
  have hS : MeasurableSet {x : ℝ | ¬(x = 1 ∨ x = -1)} :=
    ((measurableSet_singleton (1 : ℝ)).union (measurableSet_singleton (-1 : ℝ))).compl
  rw [ae_iff]
  change coinMeasure {x : ℝ | ¬(x = 1 ∨ x = -1)} = 0
  simp only [coinMeasure, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hS,
    smul_eq_mul]
  simp

/-- Cochrane (2023), p. 102 (tool): every coin shock is `±1` almost surely. -/
theorem eps_pm (t : ℤ) : ∀ᵐ ω ∂(iidSystem coin).μ, eps t ω = 1 ∨ eps t ω = -1 :=
  (measurePreserving_eval_infinitePi (fun _ => (coin : Measure ℝ))
    (Equiv.intEquivNat t)).quasiMeasurePreserving.ae coin_ae

/-- Cochrane (2023), p. 102 (tool): for `θ ≠ ±1`, `g(a − θb) = a` for `a, b ∈ {±1}`. -/
theorem decode_sub {θ : ℝ} (h1 : θ ≠ 1) (h2 : θ ≠ -1) {a b : ℝ} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) : decode θ (a - θ * b) = a := by
  unfold decode
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp
  · have h : (1 : ℝ) - θ * -1 = 1 - θ ∨ (1 : ℝ) - θ * -1 = 1 + θ := Or.inr (by ring)
    simp only [h, ↓reduceIte]
  · have h : ¬((-1 : ℝ) - θ * 1 = 1 - θ ∨ (-1 : ℝ) - θ * 1 = 1 + θ) := by
      rintro (h | h)
      · linarith
      · exact h2 (by linarith)
    simp only [h, ↓reduceIte]
  · have h : ¬((-1 : ℝ) - θ * -1 = 1 - θ ∨ (-1 : ℝ) - θ * -1 = 1 + θ) := by
      rintro (h | h)
      · exact h1 (by linarith)
      · linarith
    simp only [h, ↓reduceIte]

/-- Cochrane (2023), p. 102 and Online Appendix p. 597, **correction**: with fair-coin shocks and
`θ ≠ ±1`, the structural shock is a measurable function of the current surplus alone,
`e_t = g(s_t)` a.e.; so it is measurable for the σ-algebra of current and past surpluses. -/
theorem coin_shock_eq {θ : ℝ} (h1 : θ ≠ 1) (h2 : θ ≠ -1) (t : ℤ) :
    (eps t =ᵐ[(iidSystem coin).μ] fun ω => decode θ (surp θ t ω)) ∧
    AEStronglyMeasurable[pastSigma (surp θ) t] (eps t) (iidSystem coin).μ := by
  have heq : eps t =ᵐ[(iidSystem coin).μ] fun ω => decode θ (surp θ t ω) := by
    filter_upwards [eps_pm t, eps_pm (t - 1)] with ω ha hb
    rw [surp, decode_sub h1 h2 ha hb]
  refine ⟨heq, ?_⟩
  have hm : Measurable[pastSigma (surp θ) t] (surp θ t) := by
    simpa using measurable_pastSigma (surp θ) t 0
  exact ((measurable_decode θ).comp hm).stronglyMeasurable.aestronglyMeasurable.congr heq.symm

/-- Cochrane (2023), p. 102 (tool): the coin shocks are square integrable. -/
theorem memLp_eps (t : ℤ) : MemLp (eps t) 2 (iidSystem coin).μ :=
  memLp_coord coin_bdd (Equiv.intEquivNat t)

/-- Cochrane (2023), p. 102 (tool): the coin MA(1) surplus is square integrable. -/
theorem memLp_surp (θ : ℝ) (t : ℤ) : MemLp (surp θ t) 2 (iidSystem coin).μ :=
  (memLp_eps t).sub ((memLp_eps (t - 1)).const_mul θ)

/-- Cochrane (2023), p. 102 (tool): the `L²` class of the surplus is the `L²` moving average of
`InvertibilityMeasureL2` with coefficients `(1 − θL)·1`. -/
theorem toL2_surp (θ : ℝ) :
    toL2 (memLp_surp θ) = maProc (factorCoeff θ (fun k => if k = 0 then 1 else 0))
      (shockL2 coin_bdd) := by
  funext t
  rw [factorCoeff_delta, maProc_armaCoeff_zero (iid_whiteNoise coin_mean coin_var coin_bdd)]
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_surp θ t),
    Lp.coeFn_sub (shockL2 coin_bdd t) (θ • shockL2 coin_bdd (t - 1)),
    Lp.coeFn_smul θ (shockL2 coin_bdd (t - 1)),
    MemLp.coeFn_toLp (memLp_coord coin_bdd (Equiv.intEquivNat t)),
    MemLp.coeFn_toLp (memLp_coord coin_bdd (Equiv.intEquivNat (t - 1)))] with ω h1 h2 h3 h4 h5
  rw [toL2, h1, maOne, h2, Pi.sub_apply, h3, Pi.smul_apply, smul_eq_mul]
  change surp θ t ω = shockL2 coin_bdd t ω - θ * shockL2 coin_bdd (t - 1) ω
  rw [shockL2, h4, shockL2, h5]
  rfl

/-- Cochrane (2023), p. 102 (tool): in `L²`, `‖F‖² = E F²`. -/
theorem norm_sq_eq_integral {μ : Measure (ℕ → ℝ)} (F : Lp ℝ 2 μ) :
    ‖F‖ ^ 2 = ∫ ω, (F ω) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun ω => by
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs])

/-- Cochrane (2023), §4.3, p. 102, and Online Appendix pp. 597–601, **counterexample: for
non-Gaussian shocks the conditional-expectation forecast beats the linear one**. Fair `±1` coin
shocks, the book's `a(ρ) = 0` MA(1) `s_t = e_t − θe_{t−1}` with `θ = ρ⁻¹`, `|θ| > 1`:
(i) `a(ρ) = 0`; (ii) the shock is a function of the current surplus, `e_t = g(s_t)` a.e.;
(iii) `E(s_{t+1}|σ(s_t, s_{t−1}, …)) = −θe_t` a.e., with mean-square error `1`;
(iv) the best linear forecast from the closed linear span of the surplus history has error
variance `θ² > 1`, and the shock is not in that span; (v) hence the conditional-expectation
innovation `s_{t+1} − E(s_{t+1}|σ(past))` is not the Wold innovation. -/
theorem coin_condExp_beats_linear {θ : ℝ} (hθ : 1 < |θ|) (t : ℤ) :
    gen (factorCoeff θ (fun k => if k = 0 then 1 else 0)) θ⁻¹ = 0 ∧
    (eps t =ᵐ[(iidSystem coin).μ] fun ω => decode θ (surp θ t ω)) ∧
    ((iidSystem coin).μ[surp θ (t + 1) | pastSigma (surp θ) t] =ᵐ[(iidSystem coin).μ]
      fun ω => -θ * eps t ω) ∧
    ∫ ω, (surp θ (t + 1) ω - (iidSystem coin).μ[surp θ (t + 1) | pastSigma (surp θ) t] ω) ^ 2
      ∂(iidSystem coin).μ = 1 ∧
    (haveI : (pastSpan (toL2 (memLp_surp θ)) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      ‖toL2 (memLp_surp θ) (t + 1) - (pastSpan (toL2 (memLp_surp θ)) t).starProjection
        (toL2 (memLp_surp θ) (t + 1))‖ ^ 2 = θ ^ 2) ∧
    (1 : ℝ) < θ ^ 2 ∧
    shockL2 coin_bdd t ∉ pastSpan (toL2 (memLp_surp θ)) t ∧
    ceInnov (measurable_surp θ) (memLp_surp θ) (t + 1) ≠
      Wold.innov (toL2 (memLp_surp θ)) (t + 1) := by
  have hθ1 : θ ≠ 1 := by intro h; rw [h, abs_one] at hθ; exact lt_irrefl _ hθ
  have hθ2 : θ ≠ -1 := by intro h; rw [h, abs_neg, abs_one] at hθ; exact lt_irrefl _ hθ
  have hδ : Summable (fun k : ℕ => |(if k = 0 then (1 : ℝ) else 0)|) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by simp_all
  obtain ⟨-, -, hgen, -, hnot, -⟩ :=
    iid_wold_factor coin_mean coin_var one_pos coin_bdd hθ hδ (by simp) recoverable_delta t
  obtain ⟨-, hPS, -, hlt⟩ :=
    iid_granger_factor coin_mean coin_var one_pos coin_bdd hθ hδ (by simp) recoverable_delta t
  rw [← toL2_surp θ] at hPS hnot
  have hmean := coin_mean
  have hint : Integrable (fun x : ℝ => x) (coin : Measure ℝ) :=
    Integrable.of_bound measurable_id.aestronglyMeasurable 1
      (coin_bdd.mono fun x h => by rwa [Real.norm_eq_abs])
  have hk := (coin_shock_eq hθ1 hθ2 t).2
  obtain ⟨hce, hmse⟩ := condExp_surp_of_known hint hmean θ (fun k : ℕ => measurable_surp θ (t - k))
    (measurable_surp_avoid θ t) hk
  rw [coin_var] at hmse
  refine ⟨hgen, (coin_shock_eq hθ1 hθ2 t).1, hce, hmse, by simpa using hPS, by simpa using hlt,
    hnot, fun heq => ?_⟩
  have hn1 : ‖ceInnov (measurable_surp θ) (memLp_surp θ) (t + 1)‖ ^ 2 = 1 := by
    rw [norm_sq_eq_integral, ← hmse]
    refine integral_congr_ae ?_
    filter_upwards [ceInnov_ae_eq (measurable_surp θ) (memLp_surp θ) (t + 1)] with ω hω
    rw [hω, add_sub_cancel_right]
  have hn2 : ‖Wold.innov (toL2 (memLp_surp θ)) (t + 1)‖ ^ 2 = θ ^ 2 := by
    have := hPS
    simp only [mul_one] at this
    simpa [Wold.innov, Wold.past_eq_pastSpan] using this
  rw [heq, hn2] at hn1
  rw [hn1] at hlt
  simp at hlt

end Coin

end Cochrane.DebtDeficitsInflation.TidyR6CondExpForecast
