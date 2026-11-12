/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.TidyR6GaussianForecast

/-!
# Gaussian moving averages: Wold and Granger with conditional expectations for every `a(L)`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, p. 102, and Online
Appendix Chapter 2, §§2.1.4–2.1.6, eqs. (2.18)–(2.21), pp. 597–601.

In the i.i.d. `N(0, σ²)` economy (unbounded shocks, so not `InvertibilityMeasureL2.shockL2`) the
structural shocks `e_t = ε_{φ(t)}` are white noise in `L²` (`GaussEconomy.gauss_whiteNoise`), and
every absolutely summable moving average `s = a(L)e` (`InvertibilityMeasure` / `maProc`) has a
measurable representative `maRep` which is a centered Gaussian process, jointly with the debt
`v = c(L)e` (Hansen–Sargent coefficients `c = hsCoeff a ρ`, the ex-post present value of
surpluses when `a(ρ) = 0`, `debt_expost`).

## Main results

* `isGaussianProcess_pair`, `integral_maRep`: the surplus and debt representatives are jointly a
  centered Gaussian process.
* `condExp_mse_ma`: the conditional-expectation forecast errors of `s_{t+1}` given
  `σ(s_t, s_{t−1}, …)` and given `σ(s_t, v_t, s_{t−1}, v_{t−1}, …)` have the linear-forecast
  variances.
* `gaussian_granger_ma`: **debt Granger-causes surpluses with Mathlib conditional expectations**
  for every absolutely summable `a(L)` with `a₀ ≠ 0`, `a(ρ) = 0`, `|ρ| < 1` (the non-invertible
  case), from `InvertibilityMeasure.granger_general`.
* `gaussian_wold_ma`: **the Wold statement with conditional expectations** for every absolutely
  summable `a(L)`: the conditional-expectation innovations are the Wold innovations, white noise,
  a martingale-difference sequence, and `s_t = ∑_j c_j e^{CE}_{t−j}` (no deterministic part).
* `ma1_special_case`: the factorised MA(1) `1 − θL` of
  `GaussEconomy.gaussian_noninvertible_condExp` is the special case `a = (1 − θL)·1`, `ρ = θ⁻¹`:
  the same `L²` process, mean-square errors `θ²σ²` (surpluses) and `σ²` (surpluses and debt).
-/

namespace Cochrane.DebtDeficitsInflation.TidyR6GaussianMA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace NNReal
open Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID
open Cochrane.DebtDeficitsInflation.TidyR6CondExpForecast
open Cochrane.DebtDeficitsInflation.TidyR6CondExpForecast.IID
open Cochrane.DebtDeficitsInflation.TidyR6GaussianForecast
open Cochrane.DebtDeficitsInflation.TidyR6GaussianForecast.GaussEconomy
open Cochrane.DebtDeficitsInflation.InvertibilityMeasure
open Cochrane.DebtDeficitsInflation.Invertibility
open Cochrane.DebtDeficitsInflation.Invertibility.Hilbert
open Cochrane.DebtDeficitsInflation.Innovations (gen)

/-! ### The Gaussian `L²` moving average and its representative -/

/-- Cochrane (2023), p. 102 and Online Appendix p. 597: the Gaussian structural shocks
`e_t = ε_{φ(t)}` in `L²(ν^ℕ)`, `ν = N(0, σ²)`. -/
noncomputable def shockG (v : ℝ≥0) (t : ℤ) : Lp ℝ 2 (iidSystem (gaussLaw v)).μ :=
  (memLp_eps v t).toLp (eps t)

/-- Cochrane (2023), eq. (4.1), p. 87: the moving average `s_t = ∑_k a_k e_{t−k}` of the Gaussian
shocks in `L²`. -/
noncomputable def maL2 (v : ℝ≥0) (a : ℕ → ℝ) (t : ℤ) : Lp ℝ 2 (iidSystem (gaussLaw v)).μ :=
  maProc a (shockG v) t

/-- Cochrane (2023), eq. (4.1), p. 87: a measurable representative of the Gaussian moving
average, a genuine random variable on `ℕ → ℝ`. -/
noncomputable def maRep (v : ℝ≥0) (a : ℕ → ℝ) (t : ℤ) : (ℕ → ℝ) → ℝ :=
  (maL2 v a t : (ℕ → ℝ) → ℝ)

/-- Cochrane (2023), p. 102 (tool): the Gaussian shocks are white noise with variance `σ²`.
Restates `TidyR6GaussianForecast.GaussEconomy.gauss_whiteNoise`. -/
theorem shockG_whiteNoise (v : ℝ≥0) : WhiteNoise (shockG v) v := gauss_whiteNoise v

/-- Cochrane (2023), p. 102 (tool): the representative is measurable. -/
theorem measurable_maRep (v : ℝ≥0) (a : ℕ → ℝ) (t : ℤ) : Measurable (maRep v a t) :=
  (Lp.stronglyMeasurable _).measurable

/-- Cochrane (2023), p. 102 (tool): the representative is square integrable. -/
theorem memLp_maRep (v : ℝ≥0) (a : ℕ → ℝ) (t : ℤ) :
    MemLp (maRep v a t) 2 (iidSystem (gaussLaw v)).μ :=
  Lp.memLp _

/-- Cochrane (2023), p. 102 (tool): the `L²` class of the representative is the moving average. -/
theorem toL2_maRep (v : ℝ≥0) (a : ℕ → ℝ) : toL2 (memLp_maRep v a) = maL2 v a :=
  funext fun _ => Lp.toLp_coeFn _ _

/-- Cochrane (2023), p. 102 (tool): every absolutely summable moving average of the shocks lies in
the closed linear span of the i.i.d. Gaussian coordinates. -/
theorem maL2_mem (v : ℝ≥0) {a : ℕ → ℝ} (ha : Summable fun k => |a k|) (t : ℤ) :
    maL2 v a t ∈ (Submodule.span ℝ (Set.range (toLpFam (memLp_coord v)))).topologicalClosure := by
  have h := maProc_mem_eSpan (shockG_whiteNoise v) ha t
  refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_) h
  rintro _ ⟨s, rfl⟩
  exact ⟨Equiv.intEquivNat s, rfl⟩

/-- Cochrane (2023), p. 102 (tool): the moving averages of the Gaussian shocks have mean zero. -/
theorem integral_maRep (v : ℝ≥0) {a : ℕ → ℝ} (ha : Summable fun k => |a k|) (t : ℤ) :
    ∫ ω, maRep v a t ω ∂(iidSystem (gaussLaw v)).μ = 0 := by
  refine integral_eq_zero_of_mem_closure (memLp_coord v) (fun i => ?_) (maL2_mem v ha t)
  have := integral_shock_fun (gaussLaw v) i (f := id) measurable_id
  simpa [gauss_mean] using this

/-- Cochrane (2023), p. 102 and Online Appendix p. 601: two moving averages of the Gaussian shocks
(surpluses `a(L)e` and debt `b(L)e`), indexed by `ℤ ⊕ ℤ`, are jointly a Gaussian process. -/
theorem isGaussianProcess_pair (v : ℝ≥0) {a b : ℕ → ℝ} (ha : Summable fun k => |a k|)
    (hb : Summable fun k => |b k|) :
    IsGaussianProcess (Sum.elim (maRep v a) (maRep v b)) (iidSystem (gaussLaw v)).μ := by
  have hK := isGaussianProcess_closure (isGaussianProcess_coord v) (memLp_coord v)
  refine (hK.comp_right (Sum.elim (fun t => ⟨maL2 v a t, maL2_mem v ha t⟩)
    fun t => ⟨maL2 v b t, maL2_mem v hb t⟩)).congr fun j => ?_
  rcases j with t | t <;> exact ae_eq_refl _

/-- Cochrane (2023), p. 102: a single moving average of the Gaussian shocks is a Gaussian
process. -/
theorem isGaussianProcess_maRep (v : ℝ≥0) {a : ℕ → ℝ} (ha : Summable fun k => |a k|) :
    IsGaussianProcess (maRep v a) (iidSystem (gaussLaw v)).μ :=
  (isGaussianProcess_pair v ha ha).comp_right Sum.inl

/-- Cochrane (2023), Online Appendix eq. (2.18), p. 600 ("debt equals the ex-post present value
of surpluses"), for Gaussian shocks: if `a(ρ) = 0`, `|ρ| < 1`, the debt `v_t = c(L)e_t`
(`c = hsCoeff a ρ`) is the mean-square limit `∑_j ρʲ s_{t+1+j}`.
An instance of `InvertibilityMeasure.debt_hasSum_expost`. -/
theorem debt_expost (v : ℝ≥0) {a : ℕ → ℝ} (ha : Summable fun k => |a k|) {ρ : ℝ} (hρ : |ρ| < 1)
    (h0 : gen a ρ = 0) (t : ℤ) :
    HasSum (fun j : ℕ => ρ ^ j • maL2 v a (t + 1 + j)) (maL2 v (hsCoeff a ρ) t) :=
  debt_hasSum_expost (shockG_whiteNoise v) ha hρ h0 t

/-! ### Conditional-expectation forecast errors -/

/-- Cochrane (2023), Online Appendix p. 597 (tool): projections on equal subspaces agree. -/
theorem starProjection_congr {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {K K' : Submodule ℝ H} [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection] (h : K = K')
    (x : H) : K.starProjection x = K'.starProjection x := by
  subst h
  rfl

/-- Cochrane (2023), Online Appendix pp. 597 and 601, for Gaussian shocks and every absolutely
summable `a(L)`, `b(L)`: the mean-square error of `E(s_{t+1}|σ(s_t, s_{t−1}, …))` is the linear
forecast error variance from `H_t = span(s_t, s_{t−1}, …)`, and that of
`E(s_{t+1}|σ(s_t, v_t, s_{t−1}, v_{t−1}, …))` is the linear error variance from the joint span. -/
theorem condExp_mse_ma (v : ℝ≥0) {a b : ℕ → ℝ} (ha : Summable fun k => |a k|)
    (hb : Summable fun k => |b k|) (t : ℤ) :
    (haveI : (pastSpan (maL2 v a) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      ∫ ω, (maRep v a (t + 1) ω - (iidSystem (gaussLaw v)).μ[maRep v a (t + 1) |
        genSigma fun k : ℕ => maRep v a (t - k)] ω) ^ 2 ∂(iidSystem (gaussLaw v)).μ =
      ‖maL2 v a (t + 1) - (pastSpan (maL2 v a) t).starProjection (maL2 v a (t + 1))‖ ^ 2) ∧
    (haveI : (jointSpan (maL2 v a) (maL2 v b) t).HasOrthogonalProjection := by
        unfold jointSpan; infer_instance
      ∫ ω, (maRep v a (t + 1) ω - (iidSystem (gaussLaw v)).μ[maRep v a (t + 1) |
        genSigma (Sum.elim (fun k : ℕ => maRep v a (t - k)) fun k : ℕ => maRep v b (t - k))] ω)
        ^ 2 ∂(iidSystem (gaussLaw v)).μ =
      ‖maL2 v a (t + 1) - (jointSpan (maL2 v a) (maL2 v b) t).starProjection
        (maL2 v a (t + 1))‖ ^ 2) := by
  set X := Sum.elim (maRep v a) (maRep v b)
  have hX := isGaussianProcess_pair v ha hb
  have hXm : ∀ i, Measurable (X i) := fun i => by
    rcases i with s | s <;> exact measurable_maRep _ _ _
  have h0 : ∀ i, ∫ ω, X i ω ∂(iidSystem (gaussLaw v)).μ = 0 := fun i => by
    rcases i with s | s
    · exact integral_maRep v ha s
    · exact integral_maRep v hb s
  have hm2 : ∀ i, MemLp (X i) 2 (iidSystem (gaussLaw v)).μ := fun i => by
    rcases i with s | s <;> exact memLp_maRep _ _ _
  have hT : toLpFam hm2 = Sum.elim (maL2 v a) (maL2 v b) := by
    funext i
    rcases i with s | s <;> exact Lp.toLp_coeFn _ _
  have hτ : toLpFam hm2 (Sum.inl (t + 1)) = maL2 v a (t + 1) := congrFun hT _
  have hP : (Submodule.span ℝ (Set.range fun k : ℕ => toLpFam hm2 (Sum.inl (t - k)))
      ).topologicalClosure = pastSpan (maL2 v a) t := by
    rw [hT]
    rfl
  have hJ : (Submodule.span ℝ (Set.range fun i : ℕ ⊕ ℕ => toLpFam hm2
      (Sum.elim (fun k : ℕ => (Sum.inl (t - k) : ℤ ⊕ ℤ)) (fun k : ℕ => Sum.inr (t - k)) i))
      ).topologicalClosure = jointSpan (maL2 v a) (maL2 v b) t := by
    rw [hT, jointSpan]
    congr 2
    ext y
    constructor
    · rintro ⟨i | i, rfl⟩
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr ⟨i, rfl⟩
    · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
      · exact ⟨Sum.inl k, rfl⟩
      · exact ⟨Sum.inr k, rfl⟩
  have m1 := gaussian_condExp_mse hX hXm h0 hm2 (fun k : ℕ => (Sum.inl (t - k) : ℤ ⊕ ℤ))
    (Sum.inl (t + 1))
  have m2 := gaussian_condExp_mse hX hXm h0 hm2
    (Sum.elim (fun k : ℕ => (Sum.inl (t - k) : ℤ ⊕ ℤ)) (fun k : ℕ => Sum.inr (t - k)))
    (Sum.inl (t + 1))
  have hfun : (fun i => X (Sum.elim (fun k : ℕ => (Sum.inl (t - k) : ℤ ⊕ ℤ))
      (fun k : ℕ => Sum.inr (t - k)) i)) =
      Sum.elim (fun k : ℕ => maRep v a (t - k)) fun k : ℕ => maRep v b (t - k) := by
    funext i
    rcases i with k | k <;> rfl
  rw [hfun] at m2
  have hS : (pastSpan (maL2 v a) t).HasOrthogonalProjection := by
    unfold pastSpan; infer_instance
  have hJS : (jointSpan (maL2 v a) (maL2 v b) t).HasOrthogonalProjection := by
    unfold jointSpan; infer_instance
  refine ⟨?_, ?_⟩
  · refine m1.trans ?_
    simp only [linForecast, hτ]
    rw [starProjection_congr hP]
  · refine m2.trans ?_
    simp only [linForecast, hτ]
    rw [starProjection_congr hJ]

/-! ### Granger causality and Wold with conditional expectations, every `a(L)` -/

/-- Cochrane (2023), Online Appendix eq. (2.21), p. 601 ("debt Granger-causes surpluses"), **with
Mathlib conditional expectations, Gaussian shocks and an arbitrary absolutely summable `a(L)`**
with `a₀ ≠ 0`, `a(ρ) = 0`, `|ρ| < 1` (the non-invertible case): the mean-square error of
`E(s_{t+1}|σ(s_t, v_t, s_{t−1}, v_{t−1}, …))` is strictly smaller than that of
`E(s_{t+1}|σ(s_t, s_{t−1}, …))`, where `v = c(L)e` is the debt (`c = hsCoeff a ρ`, the ex-post
present value `debt_expost`). -/
theorem gaussian_granger_ma {v : ℝ≥0} (hv : (v : ℝ) ≠ 0) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (ha0 : a 0 ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1) (h0 : gen a ρ = 0)
    (t : ℤ) :
    ∫ ω, (maRep v a (t + 1) ω - (iidSystem (gaussLaw v)).μ[maRep v a (t + 1) |
      genSigma (Sum.elim (fun k : ℕ => maRep v a (t - k))
        fun k : ℕ => maRep v (hsCoeff a ρ) (t - k))] ω) ^ 2 ∂(iidSystem (gaussLaw v)).μ <
    ∫ ω, (maRep v a (t + 1) ω - (iidSystem (gaussLaw v)).μ[maRep v a (t + 1) |
      genSigma fun k : ℕ => maRep v a (t - k)] ω) ^ 2 ∂(iidSystem (gaussLaw v)).μ := by
  obtain ⟨m1, m2⟩ := condExp_mse_ma v ha (summable_abs_hsCoeff ha hρ) t
  rw [m1, m2]
  exact pow_lt_pow_left₀ (granger_general (shockG_whiteNoise v) hv ha ha0 hρ h0 t).2
    (norm_nonneg _) two_ne_zero

/-- Cochrane (2023), Online Appendix pp. 597 and 600, **the Wold statement with Mathlib
conditional expectations for every absolutely summable moving average of Gaussian shocks**
(including `a(ρ) = 0`): the conditional-expectation innovations
`s_t − E(s_t|σ(s_{t−1}, s_{t−2}, …))` are the Wold innovations, white noise, a
martingale-difference sequence for the natural filtration, and `s_t = ∑_j c_j e^{CE}_{t−j}` in
mean square with the Wold coefficients (the deterministic part vanishes). -/
theorem gaussian_wold_ma {v : ℝ≥0} (hv : (v : ℝ) ≠ 0) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) :
    (∀ t, ceInnov (measurable_maRep v a) (memLp_maRep v a) t = Wold.innov (maL2 v a) t) ∧
    WhiteNoise (ceInnov (measurable_maRep v a) (memLp_maRep v a))
      (‖ceInnov (measurable_maRep v a) (memLp_maRep v a) 0‖ ^ 2) ∧
    (∀ t, HasSum (fun j : ℕ => Wold.woldCoeff (maL2 v a) j •
      ceInnov (measurable_maRep v a) (memLp_maRep v a) (t - j)) (maL2 v a t)) ∧
    (∀ t, (iidSystem (gaussLaw v)).μ[fun ω => maRep v a t ω -
      (iidSystem (gaussLaw v)).μ[maRep v a t | pastSigma (maRep v a) (t - 1)] ω |
        pastSigma (maRep v a) (t - 1)] =ᵐ[(iidSystem (gaussLaw v)).μ] 0) := by
  obtain ⟨U, hU⟩ := Wold.maProc_shift (shockG_whiteNoise v) hv ha
  have hU' : ∀ t, U (toL2 (memLp_maRep v a) t) = toL2 (memLp_maRep v a) (t + 1) := by
    rw [toL2_maRep]
    exact hU
  obtain ⟨h1, h2, h3, h4⟩ := gaussian_wold_condExp (isGaussianProcess_maRep v ha)
    (measurable_maRep v a) (integral_maRep v ha) (memLp_maRep v a) hU'
  have hreg := Wold.maProc_regular (shockG_whiteNoise v) ha
  have hdet : ∀ t, Wold.detPart (maL2 v a) t = 0 := fun t => by
    have h := Wold.detPart_mem_remote (maL2 v a) t
    rw [show Wold.remote (maL2 v a) = ⊥ from hreg] at h
    exact (Submodule.mem_bot ℝ).1 h
  rw [toL2_maRep] at h1 h3
  refine ⟨h1, h2, fun t => ?_, h4⟩
  have := h3 t
  rwa [hdet, sub_zero] at this

/-! ### The factorised MA(1) as a special case -/

/-- Cochrane (2023), p. 102 and Online Appendix pp. 597–601, **link**: the MA(1)
`s_t = e_t − θe_{t−1}` (`|θ| > 1`) of `GaussEconomy.gaussian_noninvertible_condExp` is the case
`a = (1 − θL)·1`, `ρ = θ⁻¹` of `gaussian_granger_ma`: the same `L²` process
(`GaussEconomy.toL2_surp`), the representatives agree a.e. with `surp θ`, the hypotheses
`a₀ ≠ 0`, `a(ρ) = 0`, `|ρ| < 1` hold, and the conditional mean-square errors are `θ²σ²` from
surpluses (as in `GaussEconomy.gaussian_noninvertible_condExp`) and `σ²` from surpluses and debt. -/
theorem ma1_special_case {v : ℝ≥0} (hv : (v : ℝ) ≠ 0) {θ : ℝ} (hθ : 1 < |θ|) (t : ℤ) :
    maL2 v (factorCoeff θ (fun k => if k = 0 then 1 else 0)) = toL2 (memLp_surp v θ) ∧
    (∀ s, maRep v (factorCoeff θ (fun k => if k = 0 then 1 else 0)) s
      =ᵐ[(iidSystem (gaussLaw v)).μ] surp θ s) ∧
    factorCoeff θ (fun k => if k = 0 then 1 else 0) 0 ≠ 0 ∧
    gen (factorCoeff θ (fun k => if k = 0 then 1 else 0)) θ⁻¹ = 0 ∧ |θ⁻¹| < 1 ∧
    ∫ ω, (maRep v (factorCoeff θ (fun k => if k = 0 then 1 else 0)) (t + 1) ω -
      (iidSystem (gaussLaw v)).μ[maRep v (factorCoeff θ (fun k => if k = 0 then 1 else 0))
        (t + 1) | genSigma fun k : ℕ =>
          maRep v (factorCoeff θ (fun k => if k = 0 then 1 else 0)) (t - k)] ω) ^ 2
      ∂(iidSystem (gaussLaw v)).μ = θ ^ 2 * v ∧
    ∫ ω, (surp θ (t + 1) ω - (iidSystem (gaussLaw v)).μ[surp θ (t + 1) |
      pastSigma (surp θ) t] ω) ^ 2 ∂(iidSystem (gaussLaw v)).μ = θ ^ 2 * v ∧
    ∫ ω, (maRep v (factorCoeff θ (fun k => if k = 0 then 1 else 0)) (t + 1) ω -
      (iidSystem (gaussLaw v)).μ[maRep v (factorCoeff θ (fun k => if k = 0 then 1 else 0))
        (t + 1) | genSigma (Sum.elim (fun k : ℕ =>
          maRep v (factorCoeff θ (fun k => if k = 0 then 1 else 0)) (t - k)) fun k : ℕ =>
          maRep v (hsCoeff (factorCoeff θ (fun k => if k = 0 then 1 else 0)) θ⁻¹) (t - k))] ω)
        ^ 2 ∂(iidSystem (gaussLaw v)).μ = v := by
  have hδ : Summable (fun k : ℕ => |(if k = 0 then (1 : ℝ) else 0)|) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by simp_all
  have hq : |θ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hθ
  have ha := summable_factorCoeff θ hδ
  have he := shockG_whiteNoise v
  have hL : maL2 v (factorCoeff θ (fun k => if k = 0 then 1 else 0)) = toL2 (memLp_surp v θ) :=
    (toL2_surp v θ).symm
  obtain ⟨-, -, -, -, hgen, -, -, -, -⟩ := wold_factor he hv hθ hδ (by simp) recoverable_delta t
  obtain ⟨hPJ, hPS, hσn, -⟩ := granger_factor he hv hθ hδ (by simp) recoverable_delta t
  obtain ⟨m1, m2⟩ := condExp_mse_ma v ha (summable_abs_hsCoeff ha hq) t
  have hmse := (gaussian_noninvertible_condExp hv hθ t).2.2.1
  refine ⟨hL, fun s => ?_, by simp [factorCoeff], hgen, hq, ?_, hmse, ?_⟩
  · rw [maRep, hL]
    exact MemLp.coeFn_toLp _
  · rw [m1]
    exact hPS
  · rw [m2]
    unfold maL2
    rw [hPJ, sub_sub_cancel, hσn]

end Cochrane.DebtDeficitsInflation.TidyR6GaussianMA
