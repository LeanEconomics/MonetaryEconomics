/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.ExpectationsMeasureIIDZ
import ObservationalEquivalence.SurplusRegression
import Mathlib.Probability.Moments.Variance

/-!
# Theorem RG with genuine probability covariances

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, p. 501 ("We may easily
see a coefficient `γ > 0` from a fiscal-theory equilibrium"), Chapter 24, §24.1, p. 519, and
Online Appendix Chapter 2, introduction, p. 593 ("Even with completely exogenous surpluses, we
expect a positive regression coefficient of surpluses on debt").

The module `SurplusRegression` proves Theorem RG with covariances given by an abstract bilinear
form for which the shocks are orthonormal, and shows the hypotheses consistent only in the
certainty-equivalent model `truncSystem`. Here everything is a genuine probability statement on a
`MeasExpectationSystem` (Mathlib's `condExp` and `covariance`):

## Setting

`ShockMDS S ε σ²`: shocks `ε_k`, `k ∈ ℤ`, adapted (`ε_k` known at `t ≥ k`), a martingale-difference
sequence (`E_t ε_{t+1} = 0`), essentially bounded, with `E ε_k² = σ²`; the pre-sample shocks
(`k ≤ 0`, all known at date `0`) have mean zero and are uncorrelated. The i.i.d. economy
`iidZSystem` (and the `±1` coin) satisfies all of this (`iidZ_shockMDS`).

The surplus is an absolutely summable moving average `s_t = ∑_k a_k ε_{t−k}` (`maInf`, a finite
moving average being the case `a_k = 0` for `k > N`, `surplus_eq_maInf`), and the value of debt is
the valuation equation `v_t = E_t ∑_{j ≥ 0} ρ^j s_{t+1+j}` (`valueM`, Mathlib `condExp`).

## Main results

* `ShockMDS.integral_mul`: `E[ε_j ε_k] = σ² 1{j = k}` from the martingale-difference property;
  `integral_maInf_mul_maInf`: `E[a(L)ε_{τ+h} · b(L)ε_τ] = σ² ∑_m a_{m+h} b_m`.
* `valueM_eq`: `v_t = ∑_m b_m ε_{t−m}` a.e., `b_m = ∑_j ρ^j a_{m+1+j}` (the conditional
  expectation of a doubly infinite sum, computed with dominated convergence and Fubini).
* `cov_surplus_valueM`: `Cov(s_{t+1}, v_t) = σ² ∑_m a_{m+1} b_m = σ² · covInf` (Mathlib
  `covariance`); `var_valueM`: `Var(v_t) = σ² ∑ b_m²`.
* `two_covM_eq_kms` (**Theorem RG, genuine**):
  `2 Cov(s_{t+1}, v_t) = σ² (∑ a_k² + ∑ ρ^{|k−l|} a_k a_l)` (sums over `k, l ≥ 1`);
  `covM_pos_iff`, `regM_pos_iff`: positive iff not white noise;
  `regM_eq`: the regression coefficient is `covInf / ∑ b²` (`σ²` cancels).
* Finite moving averages: `valueM_eq_finite`, `covM_finite`, `two_covM_finite`,
  `regM_finite_pos_iff`.
* Link with the abstract-bilinear-form version: `covM_finite_eq_abstract` (genuine covariance `=
  σ²` × the covariance in **any** abstract model, e.g. `truncSystem`), `covM_eq_lim_abstract`
  (infinite MA: `σ²` × the limit of the abstract covariances of the truncations).
* `iidZ_shockMDS`, `coinZ_regM_pos`, `coinZ_theoremRG`: the theorem holds in the genuine i.i.d.
  coin economy; `iidZ_not_certainty_equivalent`: that economy is not certainty-equivalent
  (`E_t ε_{t+1}² = σ² ≠ 0`, while `truncSystem` gives `0`), so the `truncSystem` caveat is no
  longer needed.
-/

namespace Cochrane.ObservationalEquivalence.SurplusRegressionMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationsMeasure
open Cochrane.ObservationalEquivalence.ExpectationsMeasureIIDZ
open Cochrane.ObservationalEquivalence.MACovariance
open Cochrane.ObservationalEquivalence.SurplusRegression
open Cochrane.ObservationalEquivalence.ExpectationTools (pvExPost)

variable {Ω : Type*} [MeasurableSpace Ω]

variable (S : MeasExpectationSystem Ω) (ε : ℤ → Ω → ℝ) (σ2 : ℝ)

/-- Cochrane (2023), p. 501 and Online Appendix p. 593 (`s_t = a(L)ε_t` with serially
uncorrelated shocks of variance `σ²`), as genuine probability statements: the shocks are adapted
(`ε_k` known at every date `t ≥ k`), a martingale-difference sequence, essentially bounded, with
`E ε_k² = σ²`; the pre-sample shocks `k ≤ 0` have mean zero and are uncorrelated. -/
structure ShockMDS where
  /-- `ε_k` is known at every date `t ≥ k` -/
  adapted : ∀ (k : ℤ) (t : ℕ), k ≤ t → StronglyMeasurable[S.𝓕 t] (ε k)
  /-- martingale difference: `E_t ε_{t+1} = 0` -/
  mds : ∀ t : ℕ, S.E t (ε ((t : ℤ) + 1)) =ᵐ[S.μ] 0
  /-- a uniform essential bound -/
  bdd : ∃ M, ∀ k, ∀ᵐ ω ∂S.μ, |ε k ω| ≤ M
  /-- the variance -/
  var : ∀ k, ∫ ω, ε k ω ^ 2 ∂S.μ = σ2
  /-- pre-sample shocks have mean zero -/
  presampleMean : ∀ k : ℤ, k ≤ 0 → ∫ ω, ε k ω ∂S.μ = 0
  /-- pre-sample shocks are uncorrelated -/
  presampleOrth : ∀ j k : ℤ, j ≤ 0 → k ≤ 0 → j ≠ k → ∫ ω, ε j ω * ε k ω ∂S.μ = 0

variable {S ε σ2}

namespace ShockMDS

/-- Cochrane (2023), p. 501: each shock is a.e. strongly measurable. -/
theorem aesm (h : ShockMDS S ε σ2) (k : ℤ) : AEStronglyMeasurable (ε k) S.μ :=
  ((h.adapted k k.toNat (Int.self_le_toNat k)).mono (S.𝓕.le _)).aestronglyMeasurable

/-- Cochrane (2023), p. 501: each shock is integrable. -/
theorem integrable (h : ShockMDS S ε σ2) (k : ℤ) : Integrable (ε k) S.μ := by
  obtain ⟨M, hM⟩ := h.bdd
  exact MeasExpectationSystem.BddRV.integrable ⟨h.aesm k, M, hM k⟩

/-- Cochrane (2023), p. 501: a.e., all shocks are bounded by a common `M ≥ 0`. -/
theorem ae_bdd (h : ShockMDS S ε σ2) : ∃ M, 0 ≤ M ∧ ∀ᵐ ω ∂S.μ, ∀ k, |ε k ω| ≤ M := by
  obtain ⟨M, hM⟩ := h.bdd
  obtain ⟨ω, hω⟩ := (hM 0).exists
  exact ⟨M, (abs_nonneg _).trans hω, ae_all_iff.2 hM⟩

/-- Cochrane (2023), Online Appendix p. 602: future shocks are unforecastable, `E_t ε_k = 0` for
`k > t` (the martingale-difference property and the law of iterated expectations). -/
theorem E_future (h : ShockMDS S ε σ2) {t : ℕ} {k : ℤ} (hk : (t : ℤ) < k) :
    S.E t (ε k) =ᵐ[S.μ] 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  have hn : t ≤ n := by omega
  filter_upwards [(S.E_tower hn (ε ((n : ℤ) + 1))).symm, S.E_congr (h.mds n) t] with ω h1 h2
  rw [h1, h2, S.E_zero]

/-- Cochrane (2023), Online Appendix p. 602 (the measure-theoretic `ShockInfo`): conditional
expectations keep the realised shocks and drop the future ones,
`E_t ε_k = ε_k 1{k ≤ t}` a.e. -/
theorem E_shock (h : ShockMDS S ε σ2) (t : ℕ) (k : ℤ) :
    S.E t (ε k) =ᵐ[S.μ] if k ≤ t then ε k else 0 := by
  by_cases hk : k ≤ t
  · simp only [hk, ↓reduceIte]
    rw [S.E_of_stronglyMeasurable (h.adapted k t hk) (h.integrable k)]
  · simp only [hk, ↓reduceIte]
    exact h.E_future (by omega)

/-- Cochrane (2023), p. 501: an earlier shock is uncorrelated with a later in-sample shock (the
martingale-difference property). -/
theorem integral_mul_of_lt (h : ShockMDS S ε σ2) {j k : ℤ} (hjk : j < k) (hk : 1 ≤ k) :
    ∫ ω, ε j ω * ε k ω ∂S.μ = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  obtain ⟨M, hM⟩ := h.bdd
  have hj : StronglyMeasurable[S.𝓕 n] (ε j) := h.adapted j n (by omega)
  have hz : S.E n (ε j * ε ((n : ℤ) + 1)) =ᵐ[S.μ] 0 := by
    filter_upwards [S.E_pullOut hj (hM j) (h.integrable _), h.mds n] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
    simp
  calc ∫ ω, ε j ω * ε ((n : ℤ) + 1) ω ∂S.μ
      = ∫ ω, S.E n (ε j * ε ((n : ℤ) + 1)) ω ∂S.μ := (S.integral_E n _).symm
    _ = 0 := by rw [integral_congr_ae hz]; simp

/-- Cochrane (2023), p. 501 (white noise, genuinely): `E[ε_j ε_k] = σ² 1{j = k}`. -/
theorem integral_mul (h : ShockMDS S ε σ2) (j k : ℤ) :
    ∫ ω, ε j ω * ε k ω ∂S.μ = if j = k then σ2 else 0 := by
  by_cases hjk : j = k
  · subst hjk
    simp only [↓reduceIte]
    rw [← h.var j]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp [sq])
  · simp only [hjk, ↓reduceIte]
    by_cases hpre : j ≤ 0 ∧ k ≤ 0
    · exact h.presampleOrth j k hpre.1 hpre.2 hjk
    · rcases lt_or_gt_of_ne hjk with hlt | hlt
      · exact h.integral_mul_of_lt hlt (by omega)
      · rw [← h.integral_mul_of_lt hlt (by omega)]
        exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)

/-- Cochrane (2023), p. 501: every shock has mean zero. -/
theorem integral_eq_zero (h : ShockMDS S ε σ2) (k : ℤ) : ∫ ω, ε k ω ∂S.μ = 0 := by
  by_cases hk : k ≤ 0
  · exact h.presampleMean k hk
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    calc ∫ ω, ε ((n : ℤ) + 1) ω ∂S.μ = ∫ ω, S.E n (ε ((n : ℤ) + 1)) ω ∂S.μ :=
          (S.integral_E n _).symm
      _ = 0 := by rw [integral_congr_ae (h.mds n)]; simp

end ShockMDS

/-! ### Infinite moving averages and their second moments -/

/-- Cochrane (2023), p. 501 and Online Appendix p. 593: the moving average
`a(L)ε_τ = ∑_{k ≥ 0} a_k ε_{τ−k}` (a genuine `tsum`, pointwise). -/
noncomputable def maInf (a : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (τ : ℤ) : Ω → ℝ :=
  fun ω => ∑' k, a k * ε (τ - k) ω

/-- Cochrane (2023), p. 501: the surplus `s_t = a(L)ε_t` at the model dates `t ∈ ℕ`. -/
noncomputable def surplusInf (a : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (t : ℕ) : Ω → ℝ := maInf a ε t

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602: the value of debt from the valuation
equation, `v_t = E_t ∑_{j ≥ 0} ρ^j s_{t+1+j}`, with Mathlib's conditional expectation. -/
noncomputable def valueM (S : MeasExpectationSystem Ω) (ρ : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  S.E t (pvExPost ρ s t)

/-- Cochrane (2023), p. 501: the moving-average coefficients of the value of debt,
`b_m = ∑_{j ≥ 0} ρ^j a_{m+1+j}` (`bInf` of the lagged coefficients). -/
noncomputable def bCoeff (ρ : ℝ) (a : ℕ → ℝ) (m : ℕ) : ℝ := bInf ρ (fun k => a (k + 1)) m

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 501: a moving average with absolutely summable coefficients of shocks
bounded by `M` converges and is bounded by `∑ |a_k| M`. -/
theorem abs_maInf_le {a : ℕ → ℝ} (ha : Summable fun k => |a k|) {e : ℤ → Ω → ℝ} {M : ℝ}
    {ω : Ω} (hω : ∀ k, |e k ω| ≤ M) (τ : ℤ) :
    Summable (fun k => a k * e (τ - k) ω) ∧ |maInf a e τ ω| ≤ (∑' k, |a k|) * M := by
  obtain ⟨h1, h2⟩ := abs_tsum_le_of_le (ha.mul_right M) (f := fun k => a k * e (τ - k) ω)
    fun k => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hω _) (abs_nonneg _)
  exact ⟨h1, by rwa [tsum_mul_right] at h2⟩

/-- Cochrane (2023), p. 501: the moving average is a.e. strongly measurable. -/
theorem aesm_maInf {μ : Measure Ω} {a : ℕ → ℝ} (ha : Summable fun k => |a k|)
    {e : ℤ → Ω → ℝ} (hm : ∀ k, AEStronglyMeasurable (e k) μ) {M : ℝ}
    (hb : ∀ᵐ ω ∂μ, ∀ k, |e k ω| ≤ M) (τ : ℤ) : AEStronglyMeasurable (maInf a e τ) μ := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun N ω => ∑ k ∈ Finset.range N, a k * e (τ - k) ω)
    (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hm _).const_mul _) ?_
  filter_upwards [hb] with ω hω
  exact (abs_maInf_le ha hω τ).1.hasSum.tendsto_sum_nat

/-- Cochrane (2023), p. 501 (tool): the expectation of an absolutely convergent series of bounded
variables times a bounded variable is the series of expectations,
`E[(∑ c_k f_k) g] = ∑ c_k E[f_k g]`. -/
theorem integral_tsum_mul {μ : Measure Ω} [IsProbabilityMeasure μ] {c : ℕ → ℝ}
    (hc : Summable fun k => |c k|) {f : ℕ → Ω → ℝ} {M : ℝ}
    (hfm : ∀ k, AEStronglyMeasurable (f k) μ) (hf : ∀ k, ∀ᵐ ω ∂μ, |f k ω| ≤ M) {g : Ω → ℝ}
    {G : ℝ} (hgm : AEStronglyMeasurable g μ) (hg : ∀ᵐ ω ∂μ, |g ω| ≤ G) :
    ∫ ω, (∑' k, c k * f k ω) * g ω ∂μ = ∑' k, c k * ∫ ω, f k ω * g ω ∂μ := by
  have hpt : ∀ k, ∀ᵐ ω ∂μ, ‖c k * f k ω * g ω‖ ≤ |c k| * (M * G) := fun k => by
    filter_upwards [hf k, hg] with ω h1 h2
    have := mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have hint : ∀ k, Integrable (fun ω => c k * f k ω * g ω) μ := fun k =>
    Integrable.of_bound (((hfm k).const_mul (c k)).mul hgm) _ (hpt k)
  have hle : ∀ k, ∫ ω, ‖c k * f k ω * g ω‖ ∂μ ≤ |c k| * (M * G) := fun k => by
    calc ∫ ω, ‖c k * f k ω * g ω‖ ∂μ ≤ ∫ _, |c k| * (M * G) ∂μ :=
          integral_mono_ae (hint k).norm (integrable_const _) (hpt k)
      _ = |c k| * (M * G) := by simp
  have hsum : Summable fun k => ∫ ω, ‖c k * f k ω * g ω‖ ∂μ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) hle
      (hc.mul_right _)
  calc ∫ ω, (∑' k, c k * f k ω) * g ω ∂μ = ∫ ω, ∑' k, c k * f k ω * g ω ∂μ := by
        congr 1; funext ω; rw [tsum_mul_right]
    _ = ∑' k, ∫ ω, c k * f k ω * g ω ∂μ :=
        (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = ∑' k, c k * ∫ ω, f k ω * g ω ∂μ := by
        congr 1; funext k; rw [← integral_const_mul]; congr 1; funext ω; ring

/-- Cochrane (2023), p. 501: `E[a(L)ε_{τ+h} ε_{τ−m}] = σ² a_{m+h}`. -/
theorem integral_maInf_shock (h : ShockMDS S ε σ2) {a : ℕ → ℝ} (ha : Summable fun k => |a k|)
    (τ : ℤ) (hh m : ℕ) :
    ∫ ω, maInf a ε (τ + hh) ω * ε (τ - m) ω ∂S.μ = σ2 * a (m + hh) := by
  obtain ⟨M, -, hb⟩ := h.ae_bdd
  have hM : ∀ k, ∀ᵐ ω ∂S.μ, |ε k ω| ≤ M := fun k => hb.mono fun ω hω => hω k
  rw [show (fun ω => maInf a ε (τ + hh) ω * ε (τ - m) ω) =
      fun ω => (∑' k, a k * ε (τ + hh - k) ω) * ε (τ - m) ω from rfl,
    integral_tsum_mul ha (fun k => h.aesm _) (fun k => hM _) (h.aesm _) (hM _)]
  simp only [h.integral_mul]
  rw [tsum_eq_single (m + hh) fun k hk => by
    have : ¬ (τ + hh - k = τ - m) := by
      intro he; apply hk; omega
    simp [this]]
  have : τ + hh - ((m + hh : ℕ) : ℤ) = τ - m := by push_cast; ring
  simp only [this, ↓reduceIte]
  ring

/-- Cochrane (2023), p. 501 (covariances of moving averages, genuinely):
`E[a(L)ε_{τ+h} · b(L)ε_τ] = σ² ∑_m a_{m+h} b_m`. -/
theorem integral_maInf_mul_maInf (h : ShockMDS S ε σ2) {a b : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (hb : Summable fun k => |b k|) (τ : ℤ) (hh : ℕ) :
    ∫ ω, maInf a ε (τ + hh) ω * maInf b ε τ ω ∂S.μ = σ2 * ∑' m, a (m + hh) * b m := by
  obtain ⟨M, -, hbd⟩ := h.ae_bdd
  have hM : ∀ k, ∀ᵐ ω ∂S.μ, |ε k ω| ≤ M := fun k => hbd.mono fun ω hω => hω k
  have hA : ∀ᵐ ω ∂S.μ, |maInf a ε (τ + hh) ω| ≤ (∑' k, |a k|) * M :=
    hbd.mono fun ω hω => (abs_maInf_le ha hω _).2
  calc ∫ ω, maInf a ε (τ + hh) ω * maInf b ε τ ω ∂S.μ
      = ∫ ω, (∑' m, b m * ε (τ - m) ω) * maInf a ε (τ + hh) ω ∂S.μ :=
        integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    _ = ∑' m, b m * ∫ ω, ε (τ - m) ω * maInf a ε (τ + hh) ω ∂S.μ :=
        integral_tsum_mul hb (fun k => h.aesm _) (fun k => hM _)
          (aesm_maInf ha h.aesm hbd _) hA
    _ = ∑' m, σ2 * (a (m + hh) * b m) := by
        congr 1; funext m
        rw [show (∫ ω, ε (τ - m) ω * maInf a ε (τ + hh) ω ∂S.μ) =
          ∫ ω, maInf a ε (τ + hh) ω * ε (τ - m) ω ∂S.μ from
            integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)]
        rw [integral_maInf_shock h ha τ hh m]
        ring
    _ = σ2 * ∑' m, a (m + hh) * b m := tsum_mul_left

/-- Cochrane (2023), p. 501: a moving average of the shocks has mean zero. -/
theorem integral_maInf (h : ShockMDS S ε σ2) {a : ℕ → ℝ} (ha : Summable fun k => |a k|)
    (τ : ℤ) : ∫ ω, maInf a ε τ ω ∂S.μ = 0 := by
  obtain ⟨M, -, hbd⟩ := h.ae_bdd
  have hM : ∀ k, ∀ᵐ ω ∂S.μ, |ε k ω| ≤ M := fun k => hbd.mono fun ω hω => hω k
  have := integral_tsum_mul (μ := S.μ) ha (f := fun k => ε (τ - k)) (fun k => h.aesm _)
    (fun k => hM _) (g := fun _ => (1 : ℝ)) (G := 1) aestronglyMeasurable_const
    (Eventually.of_forall fun _ => by simp)
  simp only [mul_one] at this
  rw [show (fun ω => maInf a ε τ ω) = fun ω => ∑' k, a k * ε (τ - k) ω from rfl, this]
  simp [h.integral_eq_zero]

/-! ### The value of debt -/

/-- Cochrane (2023), p. 501 (Fubini for the value of debt): for `|ρ| < 1`, absolutely summable
`a` and bounded `e`, `∑_j ρ^j ∑_m a_{m+j+1} e_m = ∑_m b_m e_m`. -/
theorem tsum_geom_tsum_comm {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} (ha : Summable fun k => |a k|)
    {e : ℕ → ℝ} {M : ℝ} (he : ∀ m, |e m| ≤ M) :
    ∑' j, ρ ^ j * ∑' m, a (m + j + 1) * e m = ∑' m, bCoeff ρ a m * e m := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (he 0)
  set A := ∑' k, |a k|
  have htail : ∀ j, Summable (fun m => |a (m + j + 1)|) ∧ ∑' m, |a (m + j + 1)| ≤ A := by
    intro j
    have hs := (summable_nat_add_iff (j + 1)).mpr ha
    refine ⟨hs, ?_⟩
    have := ha.sum_add_tsum_nat_add (j + 1)
    have h0 : 0 ≤ ∑ i ∈ Finset.range (j + 1), |a i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    change ∑' m, |a (m + (j + 1))| ≤ A
    linarith
  have hG0 : ∀ p : ℕ × ℕ, 0 ≤ |ρ| ^ p.1 * (|a (p.2 + p.1 + 1)| * M) := fun p => by positivity
  have hGs : Summable (fun p : ℕ × ℕ => |ρ| ^ p.1 * (|a (p.2 + p.1 + 1)| * M)) := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨fun j => ?_, ?_⟩
    · exact ((htail j).1.mul_right M).mul_left (|ρ| ^ j)
    refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun m => hG0 (j, m)) (fun j => ?_)
      ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right (A * M))
    change ∑' m, |ρ| ^ j * (|a (m + j + 1)| * M) ≤ |ρ| ^ j * (A * M)
    rw [tsum_mul_left, tsum_mul_right]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (htail j).2 hM)
      (pow_nonneg (abs_nonneg _) _)
  have hFs : Summable (Function.uncurry fun j m => ρ ^ j * (a (m + j + 1) * e m)) :=
    hGs.of_norm_bounded fun p => by
      change |ρ ^ p.1 * (a (p.2 + p.1 + 1) * e p.2)| ≤ |ρ| ^ p.1 * (|a (p.2 + p.1 + 1)| * M)
      rw [abs_mul, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (he _) (abs_nonneg _))
        (pow_nonneg (abs_nonneg _) _)
  calc ∑' j, ρ ^ j * ∑' m, a (m + j + 1) * e m
      = ∑' j, ∑' m, ρ ^ j * (a (m + j + 1) * e m) := by
        congr 1; funext j; rw [← tsum_mul_left]
    _ = ∑' m, ∑' j, ρ ^ j * (a (m + j + 1) * e m) := hFs.tsum_comm.symm
    _ = ∑' m, bCoeff ρ a m * e m := by
        congr 1; funext m
        simp only [bCoeff, bInf]
        rw [← tsum_mul_right]
        congr 1; funext j
        ring

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602 (**the value of debt, genuinely**): with an
exogenous absolutely summable moving-average surplus and martingale-difference shocks, the
valuation equation `v_t = E_t ∑_j ρ^j s_{t+1+j}` gives `v_t = b(L)ε_t` a.e.,
`b_m = ∑_j ρ^j a_{m+1+j}`. -/
theorem valueM_eq (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (t : ℕ) :
    valueM S ρ (surplusInf a ε) t =ᵐ[S.μ] maInf (bCoeff ρ a) ε t := by
  obtain ⟨M, hM0, hall⟩ := h.ae_bdd
  have hM : ∀ k, ∀ᵐ ω ∂S.μ, |ε k ω| ≤ M := fun k => hall.mono fun ω hω => hω k
  set A := ∑' k, |a k|
  have hB : ∀ j : ℕ, S.E t (fun ω => ρ ^ j * surplusInf a ε (t + 1 + j) ω) =ᵐ[S.μ]
      fun ω => ρ ^ j * ∑' m, a (m + j + 1) * ε ((t : ℤ) - m) ω := by
    intro j
    set τ : ℤ := ((t + 1 + j : ℕ) : ℤ) with hτ
    have hE := S.E_hasSum (f := fun k ω => a k * ε (τ - k) ω) (c := fun k => |a k| * M)
      (ha.mul_right M) (fun k => (h.aesm _).const_mul _) (fun k => by
        filter_upwards [hM (τ - k)] with ω h1
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) t
    have hk : ∀ k : ℕ, S.E t (fun ω => a k * ε (τ - k) ω) =ᵐ[S.μ]
        fun ω => a k * (if τ - k ≤ t then ε (τ - k) ω else 0) := by
      intro k
      filter_upwards [S.E_smul (a k) (ε (τ - k)) t, h.E_shock t (τ - k)] with ω h1 h2
      change S.E t (a k • ε (τ - k)) ω = _
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
      split_ifs <;> rfl
    filter_upwards [hE, ae_all_iff.2 hk, S.E_smul (ρ ^ j) (surplusInf a ε (t + 1 + j)) t]
      with ω h1 h2 h3
    change S.E t (ρ ^ j • surplusInf a ε (t + 1 + j)) ω = _
    rw [h3, Pi.smul_apply, smul_eq_mul]
    congr 1
    simp only [h2] at h1
    have h1' := (hasSum_nat_add_iff' (j + 1)).mpr h1
    have hz : ∑ i ∈ Finset.range (j + 1), a i * (if τ - i ≤ t then ε (τ - i) ω else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have : ¬ (τ - i ≤ t) := by simp only [Finset.mem_range] at hi; omega
        simp [this]
    rw [hz, sub_zero] at h1'
    have he : (fun m : ℕ => a (m + (j + 1)) *
        (if τ - ((m + (j + 1) : ℕ) : ℤ) ≤ t then ε (τ - ((m + (j + 1) : ℕ) : ℤ)) ω else 0)) =
        fun m => a (m + j + 1) * ε ((t : ℤ) - m) ω := by
      funext m
      have c1 : τ - ((m + (j + 1) : ℕ) : ℤ) ≤ t := by omega
      have c2 : τ - ((m + (j + 1) : ℕ) : ℤ) = (t : ℤ) - m := by omega
      simp only [c1, ↓reduceIte]
      rw [c2]
      rfl
    rw [he] at h1'
    exact h1'.tsum_eq.symm
  have hsb : ∀ τ : ℤ, ∀ᵐ ω ∂S.μ, |maInf a ε τ ω| ≤ A * M := fun τ =>
    hall.mono fun ω hω => (abs_maInf_le ha hω τ).2
  have hE := S.E_hasSum (f := fun j ω => ρ ^ j * surplusInf a ε (t + 1 + j) ω)
    (c := fun j => |ρ| ^ j * (A * M))
    ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right _)
    (fun j => (aesm_maInf ha h.aesm hall _).const_mul _) (fun j => by
      filter_upwards [hsb ((t + 1 + j : ℕ) : ℤ)] with ω h1
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left h1 (pow_nonneg (abs_nonneg _) _)) t
  filter_upwards [hE, ae_all_iff.2 hB, hall] with ω h1 h2 hω
  simp only [h2] at h1
  change S.E t (pvExPost ρ (surplusInf a ε) t) ω = ∑' m, bCoeff ρ a m * ε ((t : ℤ) - m) ω
  rw [← tsum_geom_tsum_comm hρ ha (e := fun m => ε ((t : ℤ) - m) ω) fun m => hω _]
  exact h1.tsum_eq.symm

/-! ### Theorem RG with genuine covariances -/

/-- Cochrane (2023), p. 501: for `|ρ| < 1` the value-of-debt coefficients are absolutely
summable. -/
theorem bCoeff_abs_summable {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} (ha : Summable fun k => |a k|) :
    Summable fun m => |bCoeff ρ a m| :=
  bInf_abs_summable hρ ((summable_nat_add_iff 1).mpr ha)

/-- Cochrane (2023), p. 501: the surplus has mean zero. -/
theorem integral_surplusInf (h : ShockMDS S ε σ2) {a : ℕ → ℝ} (ha : Summable fun k => |a k|)
    (t : ℕ) : ∫ ω, surplusInf a ε t ω ∂S.μ = 0 :=
  integral_maInf h ha t

/-- Cochrane (2023), p. 501: the value of debt has mean zero. -/
theorem integral_valueM (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (t : ℕ) :
    ∫ ω, valueM S ρ (surplusInf a ε) t ω ∂S.μ = 0 := by
  rw [integral_congr_ae (valueM_eq h hρ ha t)]
  exact integral_maInf h (bCoeff_abs_summable hρ ha) t

/-- Cochrane (2023), p. 501: `E[s_{t+1} v_t] = σ² ∑_m a_{m+1} b_m`. -/
theorem integral_surplus_valueM (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (t : ℕ) :
    ∫ ω, surplusInf a ε (t + 1) ω * valueM S ρ (surplusInf a ε) t ω ∂S.μ =
      σ2 * covInf ρ (fun k => a (k + 1)) := by
  calc ∫ ω, surplusInf a ε (t + 1) ω * valueM S ρ (surplusInf a ε) t ω ∂S.μ
      = ∫ ω, maInf a ε ((t : ℤ) + ((1 : ℕ) : ℤ)) ω * maInf (bCoeff ρ a) ε t ω ∂S.μ := by
        refine integral_congr_ae ?_
        filter_upwards [valueM_eq h hρ ha t] with ω hω
        rw [hω, surplusInf, Nat.cast_add]
    _ = σ2 * ∑' m, a (m + 1) * bCoeff ρ a m :=
        integral_maInf_mul_maInf h ha (bCoeff_abs_summable hρ ha) t 1
    _ = σ2 * covInf ρ (fun k => a (k + 1)) := rfl

/-- Cochrane (2023), p. 501 (**the covariance of surpluses with lagged debt, genuinely**): with
Mathlib's `covariance`, `Cov(s_{t+1}, v_t) = σ² ∑_m a_{m+1} b_m = σ² · covInf ρ (a_{·+1})` — the
abstract formula `covInf` of `SurplusRegression` times the shock variance. -/
theorem cov_surplus_valueM (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (t : ℕ) :
    cov[surplusInf a ε (t + 1), valueM S ρ (surplusInf a ε) t; S.μ] =
      σ2 * covInf ρ (fun k => a (k + 1)) := by
  rw [covariance, integral_surplusInf h ha, integral_valueM h hρ ha]
  simp only [sub_zero]
  exact integral_surplus_valueM h hρ ha t

/-- Cochrane (2023), p. 501: `Var(v_t) = σ² ∑_m b_m²` (Mathlib `variance`). -/
theorem var_valueM (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (t : ℕ) :
    Var[valueM S ρ (surplusInf a ε) t; S.μ] = σ2 * ∑' m, bCoeff ρ a m ^ 2 := by
  rw [← covariance_self (X := valueM S ρ (surplusInf a ε) t)
    (S.integrable_E t _).aestronglyMeasurable.aemeasurable, covariance,
    integral_valueM h hρ ha]
  simp only [sub_zero]
  calc ∫ ω, valueM S ρ (surplusInf a ε) t ω * valueM S ρ (surplusInf a ε) t ω ∂S.μ
      = ∫ ω, maInf (bCoeff ρ a) ε ((t : ℤ) + ((0 : ℕ) : ℤ)) ω * maInf (bCoeff ρ a) ε t ω ∂S.μ := by
        refine integral_congr_ae ?_
        filter_upwards [valueM_eq h hρ ha t] with ω hω
        rw [hω, Nat.cast_zero, add_zero]
    _ = σ2 * ∑' m, bCoeff ρ a (m + 0) * bCoeff ρ a m :=
        integral_maInf_mul_maInf h (bCoeff_abs_summable hρ ha) (bCoeff_abs_summable hρ ha) t 0
    _ = σ2 * ∑' m, bCoeff ρ a m ^ 2 := by simp only [add_zero, sq]

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (**Theorem RG with genuine
covariances**): for an absolutely summable exogenous surplus moving average and the valuation
equation, `2 Cov(s_{t+1}, v_t) = σ² (∑_{k≥1} a_k² + ∑_{k,l≥1} ρ^{|k−l|} a_k a_l)`. -/
theorem two_covM_eq_kms (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (t : ℕ) :
    2 * cov[surplusInf a ε (t + 1), valueM S ρ (surplusInf a ε) t; S.μ] =
      σ2 * (∑' k, a (k + 1) ^ 2 + kmsInf ρ (fun k => a (k + 1))) := by
  rw [cov_surplus_valueM h hρ ha t, ← two_covInf_eq hρ.le ((summable_nat_add_iff 1).mpr ha)]
  ring

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (Theorem RG, sign, genuinely):
with `σ² > 0`, the covariance of surpluses with lagged debt is strictly positive iff the surplus
is not white noise. -/
theorem covM_pos_iff (h : ShockMDS S ε σ2) (hσ : 0 < σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (t : ℕ) :
    0 < cov[surplusInf a ε (t + 1), valueM S ρ (surplusInf a ε) t; S.μ] ↔ ¬ IsIID a := by
  rw [cov_surplus_valueM h hρ ha t, mul_pos_iff_of_pos_left hσ]
  exact covInf_pos_iff hρ.le ha

/-- Cochrane (2023), p. 501: the population regression coefficient of `x` on `y`,
`Cov(x, y)/Var(y)`, with Mathlib's `covariance` and `variance`. -/
noncomputable def regM (μ : Measure Ω) (x y : Ω → ℝ) : ℝ := cov[x, y; μ] / Var[y; μ]

/-- Cochrane (2023), p. 501: the regression coefficient of `s_{t+1}` on `v_t` is
`∑_m a_{m+1} b_m / ∑_m b_m²` (the shock variance cancels). -/
theorem regM_eq (h : ShockMDS S ε σ2) (hσ : σ2 ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (t : ℕ) :
    regM S.μ (surplusInf a ε (t + 1)) (valueM S ρ (surplusInf a ε) t) =
      covInf ρ (fun k => a (k + 1)) / ∑' m, bCoeff ρ a m ^ 2 := by
  rw [regM, cov_surplus_valueM h hρ ha t, var_valueM h hρ ha t, mul_div_mul_left _ _ hσ]

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (Theorem RG, regression form,
genuinely): "even with completely exogenous surpluses, we expect a positive regression
coefficient of surpluses on debt" — the genuine regression coefficient is strictly positive iff
the surplus is not white noise. -/
theorem regM_pos_iff (h : ShockMDS S ε σ2) (hσ : 0 < σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (t : ℕ) :
    0 < regM S.μ (surplusInf a ε (t + 1)) (valueM S ρ (surplusInf a ε) t) ↔ ¬ IsIID a := by
  rw [regM_eq h hσ.ne' hρ ha t]
  exact regInf_pos_iff hρ ha

/-- Cochrane (2023), Online Appendix p. 604 (AR(1) surplus `a_k = η^k`, genuinely):
`Cov(s_{t+1}, v_t) = σ² η² ∑ η^{2k}/(1 − ρη)`, positive iff `η ≠ 0` (with `σ² > 0`). -/
theorem ar1_covM (h : ShockMDS S ε σ2) (hσ : 0 < σ2) {η ρ : ℝ} (hη : |η| < 1) (hρ : |ρ| < 1)
    (t : ℕ) :
    cov[surplusInf (fun k => η ^ k) ε (t + 1), valueM S ρ (surplusInf (fun k => η ^ k) ε) t;
        S.μ] = σ2 * (η ^ 2 * (∑' k : ℕ, (η ^ k) ^ 2) / (1 - ρ * η)) ∧
      (0 < cov[surplusInf (fun k => η ^ k) ε (t + 1),
        valueM S ρ (surplusInf (fun k => η ^ k) ε) t; S.μ] ↔ η ≠ 0) := by
  have ha : Summable fun k => |η ^ k| := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg η) hη
  obtain ⟨h1, -, h3⟩ := ar1_covInf hη hρ
  rw [cov_surplus_valueM h hρ ha t]
  simp only [pow_succ] at h1 h3 ⊢
  refine ⟨by rw [h1], ?_⟩
  rw [mul_pos_iff_of_pos_left hσ]
  exact h3

/-! ### Finite moving averages -/

/-- Cochrane (2023), p. 501: a finite moving average has absolutely summable coefficients. -/
theorem summable_of_finite {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) :
    Summable fun k => |a k| :=
  summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun k hk => by
    simp only [Finset.mem_range, not_lt] at hk
    rw [ha k (by omega), abs_zero]

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 501: the finite moving average `surplus a N ε` of `SurplusRegression` is
the infinite one with `a_k = 0` beyond `N`. -/
theorem surplus_eq_maInf {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (e : ℤ → Ω → ℝ)
    (t : ℕ) : surplus a N e t = surplusInf a e t := by
  funext ω
  simp only [surplus, maProc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, surplusInf, maInf]
  rw [tsum_eq_sum (s := Finset.range (N + 1)) fun k hk => by
    simp only [Finset.mem_range, not_lt] at hk
    rw [ha k (by omega), zero_mul]]

/-- Cochrane (2023), p. 501: for a finite moving average, `b_m` is the finite sum `vCoeff`. -/
theorem bCoeff_eq_vCoeff {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (ρ : ℝ) (m : ℕ) :
    bCoeff ρ a m = vCoeff ρ a N m := by
  simp only [bCoeff, bInf, vCoeff]
  rw [tsum_eq_sum (s := Finset.range (N + 1)) fun j hj => by
    simp only [Finset.mem_range, not_lt] at hj
    rw [ha _ (by omega), mul_zero]]
  exact Finset.sum_congr rfl fun j _ => by rw [show m + j + 1 = m + 1 + j by omega]

/-- Cochrane (2023), p. 501: for a finite moving average, `covInf` is the finite covariance
`∑_{k ≤ N} a_{k+1} b_k` of `SurplusRegression.cov_surplus_value`. -/
theorem covInf_eq_finite {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (ρ : ℝ) :
    covInf ρ (fun k => a (k + 1)) = ∑ k ∈ Finset.range (N + 1), a (k + 1) * vCoeff ρ a N k := by
  unfold covInf
  rw [tsum_eq_sum (s := Finset.range (N + 1)) fun m hm => by
    simp only [Finset.mem_range, not_lt] at hm
    change a (m + 1) * _ = 0
    rw [ha (m + 1) (by omega), zero_mul]]
  exact Finset.sum_congr rfl fun m _ => by rw [← bCoeff_eq_vCoeff ha]; rfl

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 501: for a finite moving average, `b(L)ε_t` is the finite moving average
`maProc (vCoeff ρ a N) N ε t`. -/
theorem maInf_bCoeff_eq {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (ρ : ℝ)
    (e : ℤ → Ω → ℝ) (t : ℕ) : maInf (bCoeff ρ a) e t = maProc (vCoeff ρ a N) N e t := by
  funext ω
  simp only [maInf, maProc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [tsum_eq_sum (s := Finset.range (N + 1)) fun m hm => by
    simp only [Finset.mem_range, not_lt] at hm
    rw [bCoeff_eq_vCoeff ha, vCoeff_of_le ρ ha (by omega), zero_mul]]
  exact Finset.sum_congr rfl fun m _ => by rw [bCoeff_eq_vCoeff ha]

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602 (the genuine counterpart of
`SurplusRegression.value_eq_maProc`): with a finite moving-average surplus,
`v_t = b(L)ε_t` a.e., `b_m = ∑_j ρ^j a_{m+1+j}`. -/
theorem valueM_eq_finite (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ}
    (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    valueM S ρ (surplus a N ε) t =ᵐ[S.μ] maProc (vCoeff ρ a N) N ε t := by
  rw [show surplus a N ε = surplusInf a ε from funext (surplus_eq_maInf ha ε),
    ← maInf_bCoeff_eq ha]
  exact valueM_eq h hρ (summable_of_finite ha) t

/-- Cochrane (2023), p. 501 (the genuine counterpart of `SurplusRegression.cov_surplus_value`):
`Cov(s_{t+1}, v_t) = σ² ∑_{k ≤ N} a_{k+1} b_k`. -/
theorem covM_finite (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ}
    (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    cov[surplus a N ε (t + 1), valueM S ρ (surplus a N ε) t; S.μ] =
      σ2 * ∑ k ∈ Finset.range (N + 1), a (k + 1) * vCoeff ρ a N k := by
  rw [show surplus a N ε = surplusInf a ε from funext (surplus_eq_maInf ha ε),
    cov_surplus_valueM h hρ (summable_of_finite ha) t, covInf_eq_finite ha]

/-- Cochrane (2023), p. 501, §24.1 p. 519 (survey **Theorem RG**, finite form, genuinely):
`2 Cov(s_{t+1}, v_t) = σ² (∑_{k<N} a_{k+1}² + ∑_{k,l<N} ρ^{|k−l|} a_{k+1} a_{l+1})`. -/
theorem two_covM_finite (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ}
    (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    2 * cov[surplus a N ε (t + 1), valueM S ρ (surplus a N ε) t; S.μ] =
      σ2 * (∑ k ∈ Finset.range N, a (k + 1) ^ 2 + kmsForm ρ N (fun k => a (k + 1))) := by
  rw [covM_finite h hρ ha t, kmsForm_eq_ldl, ← two_sum_eq_ldl ρ ha]
  ring

/-- Cochrane (2023), p. 501, §24.1 p. 519 (Theorem RG, regression form, finite moving averages,
genuinely): the regression coefficient is positive iff the surplus is not white noise. -/
theorem regM_finite_pos_iff (h : ShockMDS S ε σ2) (hσ : 0 < σ2) {ρ : ℝ} (hρ : |ρ| < 1)
    {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    0 < regM S.μ (surplus a N ε (t + 1)) (valueM S ρ (surplus a N ε) t) ↔ ¬ IsIID a := by
  rw [show surplus a N ε = surplusInf a ε from funext (surplus_eq_maInf ha ε)]
  exact regM_pos_iff h hσ hρ (summable_of_finite ha) t

/-! ### Link with the abstract bilinear-form version -/

/-- Cochrane (2023), p. 501 (**link**): the genuine covariance equals `σ²` times the covariance
computed in **any** abstract model of `SurplusRegression` (a core `ExpectationSystem` with
`ShockInfo`, any covariance form `B` for which the shocks are white noise). -/
theorem covM_finite_eq_abstract (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℕ) {Ω' : Type*} {𝔼 : ExpectationSystem Ω'}
    {B : LinearMap.BilinForm ℝ (Ω' → ℝ)} {e : ℤ → Ω' → ℝ} (hw : WhiteNoise B e)
    (he : ShockInfo 𝔼 e) {M : ℝ} (hM : ∀ k ω, |e k ω| ≤ M) (t' : ℕ) :
    cov[surplus a N ε (t + 1), valueM S ρ (surplus a N ε) t; S.μ] =
      σ2 * B (surplus a N e (t' + 1)) (valueOfDebt 𝔼 ρ (surplus a N e) t') := by
  rw [covM_finite h hρ ha t, SurplusRegression.cov_surplus_value hw he hM hρ ha t']

/-- Cochrane (2023), p. 501 (link with the certainty-equivalent model): the genuine covariance is
`σ²` times the covariance in `SurplusRegression.truncSystem`. -/
theorem covM_finite_eq_trunc (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ}
    (ha : ∀ k, N < k → a k = 0) (t t' : ℕ) :
    cov[surplus a N ε (t + 1), valueM S ρ (surplus a N ε) t; S.μ] =
      σ2 * truncCov (surplus a N clampShock (t' + 1))
        (valueOfDebt truncSystem ρ (surplus a N clampShock) t') :=
  covM_finite_eq_abstract h hρ ha t clampShock_whiteNoise clampShock_info clampShock_bounded t'

/-- Cochrane (2023), p. 501 (**link**, infinite moving averages): the genuine covariance is the
limit of `σ²` times the abstract covariances of the lag-`N` truncations
(`SurplusRegression.cov_trunc_tendsto`). -/
theorem covM_eq_lim_abstract (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (t : ℕ) {Ω' : Type*} {𝔼 : ExpectationSystem Ω'}
    {B : LinearMap.BilinForm ℝ (Ω' → ℝ)} {e : ℤ → Ω' → ℝ} (hw : WhiteNoise B e)
    (he : ShockInfo 𝔼 e) {M : ℝ} (hM : ∀ k ω, |e k ω| ≤ M) (t' : ℕ) :
    Tendsto (fun N => σ2 * B (surplus (truncSeq a (N + 1)) N e (t' + 1))
      (valueOfDebt 𝔼 ρ (surplus (truncSeq a (N + 1)) N e) t')) atTop
      (𝓝 (cov[surplusInf a ε (t + 1), valueM S ρ (surplusInf a ε) t; S.μ])) := by
  rw [cov_surplus_valueM h hρ ha t]
  exact (cov_trunc_tendsto hw he hM hρ ha t').const_mul σ2

/-! ### The genuine i.i.d. economy: the `truncSystem` caveat is no longer needed -/

variable {ν : ProbabilityMeasure ℝ}

/-- Cochrane (2023), p. 501: the i.i.d. shocks with an infinite past (mean zero, variance `σ²`,
bounded support) satisfy `ShockMDS`. -/
theorem iidZ_shockMDS {σ2' B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2') (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) :
    ShockMDS (iidZSystem ν) shockZ σ2' :=
  ⟨fun _ _ hkt => (measurable_shockZ ν hkt).stronglyMeasurable,
    fun _ => E_shockZ_zero hmean (by omega), ⟨B, shockZ_ae_bdd ν hbdd⟩,
    fun k => by
      rw [integral_shockZ_fun ν k (f := fun x => x ^ 2) (measurable_id.pow_const 2), hvar],
    fun k _ => by rw [integral_shockZ_fun ν k (f := fun x => x) measurable_id, hmean],
    fun j k _ _ hjk => by rw [integral_shockZ_mul hmean hvar hbdd j k]; simp [hjk]⟩

/-- Cochrane (2023), p. 501: the fair `±1` coin economy with an infinite past satisfies
`ShockMDS` with `σ² = 1`. -/
theorem coinZ_shockMDS : ShockMDS (iidZSystem ExpectationsMeasureIID.coin) shockZ 1 :=
  iidZ_shockMDS ExpectationsMeasureIID.coin_mean ExpectationsMeasureIID.coin_var
    ExpectationsMeasureIID.coin_bdd

/-- Cochrane (2023), p. 501, §24.1 p. 519 (Theorem RG is not vacuous, genuinely): in the i.i.d.
coin economy, for every absolutely summable surplus moving average, Theorem RG holds with genuine
covariances, and the genuine regression coefficient is positive iff the surplus is not white
noise. -/
theorem coinZ_theoremRG {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} (ha : Summable fun k => |a k|)
    (t : ℕ) :
    2 * cov[surplusInf a shockZ (t + 1), valueM (iidZSystem ExpectationsMeasureIID.coin) ρ
        (surplusInf a shockZ) t; (iidZSystem ExpectationsMeasureIID.coin).μ] =
      1 * (∑' k, a (k + 1) ^ 2 + kmsInf ρ (fun k => a (k + 1))) ∧
    (0 < regM (iidZSystem ExpectationsMeasureIID.coin).μ (surplusInf a shockZ (t + 1))
        (valueM (iidZSystem ExpectationsMeasureIID.coin) ρ (surplusInf a shockZ) t) ↔
      ¬ IsIID a) :=
  ⟨two_covM_eq_kms coinZ_shockMDS hρ ha t, regM_pos_iff coinZ_shockMDS one_pos hρ ha t⟩

/-- Cochrane (2023), §24.1, p. 519 (survey E16, genuinely): in the coin economy the MA(1)
surplus `s_t = ε_t + ε_{t−1}` has a strictly positive genuine regression coefficient on debt. -/
theorem coinZ_regM_pos {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    0 < regM (iidZSystem ExpectationsMeasureIID.coin).μ (surplus ma1Coeff 1 shockZ (t + 1))
      (valueM (iidZSystem ExpectationsMeasureIID.coin) ρ (surplus ma1Coeff 1 shockZ) t) := by
  refine (regM_finite_pos_iff coinZ_shockMDS one_pos hρ
    (fun k hk => by simp [ma1Coeff]; omega) t).2 fun hiid => ?_
  have := hiid 1 le_rfl
  simp [ma1Coeff] at this

/-- Cochrane (2023), p. 501 (**why the `truncSystem` caveat is no longer needed**): the i.i.d.
economy is not certainty-equivalent — the forecast of `ε_{t+1}²` is `σ² > 0` (genuinely
nonzero), whereas `truncSystem` (future shocks set to their mean) forecasts `0`. -/
theorem iidZ_not_certainty_equivalent {σ2' : ℝ} (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2')
    (hσ : 0 < σ2') (t : ℕ) :
    (iidZSystem ν).E t (fun ω => shockZ ((t : ℤ) + 1) ω ^ 2) =ᵐ[(iidZSystem ν).μ]
        (fun _ => σ2') ∧
      ¬ (iidZSystem ν).E t (fun ω => shockZ ((t : ℤ) + 1) ω ^ 2) =ᵐ[(iidZSystem ν).μ] 0 ∧
      truncSystem.E t (fun ω => clampShock ((t : ℤ) + 1) ω ^ 2) = 0 := by
  have h1 : (iidZSystem ν).E t (fun ω => shockZ ((t : ℤ) + 1) ω ^ 2) =ᵐ[(iidZSystem ν).μ]
      (fun _ => σ2') := by
    rw [← hvar]
    exact E_shockZ_fun ν (by omega) (f := fun x => x ^ 2) (measurable_id.pow_const 2)
  refine ⟨h1, fun h0 => ?_, ?_⟩
  · obtain ⟨ω, hω⟩ := (h1.symm.trans h0).exists
    simp only [Pi.zero_apply] at hω
    linarith
  · funext ω
    simp [truncSystem, LinearMap.funLeft_apply, clampShock, truncPath]

end Cochrane.ObservationalEquivalence.SurplusRegressionMeasure
