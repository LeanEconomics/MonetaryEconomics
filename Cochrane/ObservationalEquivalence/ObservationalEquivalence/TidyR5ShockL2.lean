/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.SurplusRegressionL2
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Theorem RG with square-integrable (possibly unbounded) martingale-difference shocks

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, p. 501, Chapter 24,
§24.1, p. 519, and Online Appendix Chapter 2, introduction, p. 593 (surpluses `s_t = a(L)ε_t`
with serially uncorrelated shocks of variance `σ²`).

`SurplusRegressionMeasure` and `SurplusRegressionL2` prove Theorem RG for shocks satisfying
`SurplusRegressionMeasure.ShockMDS`, which asks for a uniform essential bound. The book only needs
serially uncorrelated shocks of variance `σ²`. Here the bound is dropped: `ShockMDS2` asks for
square-integrable shocks, and everything is done in `L²(P)`:

* `ShockMDS2 S ε σ²`: `ε_k` (`k ∈ ℤ`) known at every `t ≥ k`, `E_t ε_{t+1} = 0`, `ε_k ∈ L²`,
  `E ε_k² = σ²`, pre-sample shocks mean zero and uncorrelated. `ShockMDS2.integral_mul`:
  `E[ε_j ε_k] = σ² 1{j = k}` (the conditional expectation pulls out an `L²` factor by Hölder).
* `maL2`, `inner_maL2_maL2`: `L²` moving averages and their covariances; `proj_shock`,
  `proj_maL2`, `proj_pvL2`; `valueL2_ae`: `v_t = E_t PV_t = b(L)ε_t` a.e.
* **Theorem RG**: `cov_surplus_valueL2`, `var_valueL2`, `two_covL2_eq_kms`, `covL2_pos_iff`,
  `regL2_eq`, `regL2_pos_iff`, for square-summable moving averages of square-integrable
  martingale-difference shocks.
* Links: `ShockMDS.toShockMDS2` (bounded shocks are square-integrable) and
  `valueL2_eq_bounded`, `regL2_eq_bounded` (for bounded shocks the objects are those of
  `SurplusRegressionL2`).
* The i.i.d. economy with any law of finite variance: `iidZ_shockMDS2`; with Gaussian shocks
  (`gaussZ_shockMDS2`), which are not essentially bounded (`gaussZ_not_shockMDS`), Theorem RG holds
  (`gaussZ_theoremRG`, `gaussZ_harmonic_regL2_pos`) — a case the bounded versions did not cover.
-/

namespace Cochrane.ObservationalEquivalence.TidyR5ShockL2

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationsMeasure
open Cochrane.ObservationalEquivalence.ExpectationsMeasureIIDZ
open Cochrane.ObservationalEquivalence.MACovariance
open Cochrane.ObservationalEquivalence.SurplusRegression
open Cochrane.ObservationalEquivalence.SurplusRegressionMeasure
open Cochrane.ObservationalEquivalence.SquareSummableRG
open Cochrane.ObservationalEquivalence.SurplusRegressionL2 (proj proj_ae integral_mul_eq_inner
  inner_tsum_left inner_tsum_right bCoeff_sq_summable harmonicCoeff)

variable {Ω : Type*} [MeasurableSpace Ω]

variable (S : MeasExpectationSystem Ω) (ε : ℤ → Ω → ℝ) (σ2 : ℝ)

/-- Cochrane (2023), p. 501 and Online Appendix p. 593 (`s_t = a(L)ε_t` with serially
uncorrelated shocks of variance `σ²`), without a bound: the shocks are adapted (`ε_k` known at
every date `t ≥ k`), a martingale-difference sequence, square-integrable, with `E ε_k² = σ²`; the
pre-sample shocks `k ≤ 0` have mean zero and are uncorrelated. -/
structure ShockMDS2 where
  /-- `ε_k` is known at every date `t ≥ k` -/
  adapted : ∀ (k : ℤ) (t : ℕ), k ≤ t → StronglyMeasurable[S.𝓕 t] (ε k)
  /-- martingale difference: `E_t ε_{t+1} = 0` -/
  mds : ∀ t : ℕ, S.E t (ε ((t : ℤ) + 1)) =ᵐ[S.μ] 0
  /-- square integrability -/
  memLp : ∀ k, MemLp (ε k) 2 S.μ
  /-- the variance -/
  var : ∀ k, ∫ ω, ε k ω ^ 2 ∂S.μ = σ2
  /-- pre-sample shocks have mean zero -/
  presampleMean : ∀ k : ℤ, k ≤ 0 → ∫ ω, ε k ω ∂S.μ = 0
  /-- pre-sample shocks are uncorrelated -/
  presampleOrth : ∀ j k : ℤ, j ≤ 0 → k ≤ 0 → j ≠ k → ∫ ω, ε j ω * ε k ω ∂S.μ = 0

variable {S ε σ2}

namespace ShockMDS2

/-- Cochrane (2023), p. 501: each shock is integrable. -/
theorem integrable (h : ShockMDS2 S ε σ2) (k : ℤ) : Integrable (ε k) S.μ :=
  (h.memLp k).integrable one_le_two

/-- Cochrane (2023), Online Appendix p. 602: future shocks are unforecastable, `E_t ε_k = 0` for
`k > t`. -/
theorem E_future (h : ShockMDS2 S ε σ2) {t : ℕ} {k : ℤ} (hk : (t : ℤ) < k) :
    S.E t (ε k) =ᵐ[S.μ] 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  have hn : t ≤ n := by omega
  filter_upwards [(S.E_tower hn (ε ((n : ℤ) + 1))).symm, S.E_congr (h.mds n) t] with ω h1 h2
  rw [h1, h2, S.E_zero]

/-- Cochrane (2023), p. 501: an earlier shock is uncorrelated with a later in-sample shock; the
earlier shock is pulled out of the conditional expectation (Hölder: the product of two `L²`
variables is integrable). -/
theorem integral_mul_of_lt (h : ShockMDS2 S ε σ2) {j k : ℤ} (hjk : j < k) (hk : 1 ≤ k) :
    ∫ ω, ε j ω * ε k ω ∂S.μ = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  have hj : StronglyMeasurable[S.𝓕 n] (ε j) := h.adapted j n (by omega)
  have hz : S.E n (ε j * ε ((n : ℤ) + 1)) =ᵐ[S.μ] 0 := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (g := ε ((n : ℤ) + 1)) hj
      ((h.memLp j).integrable_mul (h.memLp _)) (h.integrable _), h.mds n] with ω h1 h2
    have h1' : S.E n (ε j * ε ((n : ℤ) + 1)) ω = ε j ω * S.E n (ε ((n : ℤ) + 1)) ω := h1
    rw [h1', h2]
    simp
  calc ∫ ω, ε j ω * ε ((n : ℤ) + 1) ω ∂S.μ
      = ∫ ω, S.E n (ε j * ε ((n : ℤ) + 1)) ω ∂S.μ := (S.integral_E n _).symm
    _ = 0 := by rw [integral_congr_ae hz]; simp

/-- Cochrane (2023), p. 501 (white noise, square-integrable shocks): `E[ε_j ε_k] = σ² 1{j = k}`. -/
theorem integral_mul (h : ShockMDS2 S ε σ2) (j k : ℤ) :
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
theorem integral_eq_zero (h : ShockMDS2 S ε σ2) (k : ℤ) : ∫ ω, ε k ω ∂S.μ = 0 := by
  by_cases hk : k ≤ 0
  · exact h.presampleMean k hk
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    calc ∫ ω, ε ((n : ℤ) + 1) ω ∂S.μ = ∫ ω, S.E n (ε ((n : ℤ) + 1)) ω ∂S.μ :=
          (S.integral_E n _).symm
      _ = 0 := by rw [integral_congr_ae (h.mds n)]; simp

/-- Cochrane (2023), p. 501: the shock variance is nonnegative. -/
theorem var_nonneg (h : ShockMDS2 S ε σ2) : 0 ≤ σ2 := by
  rw [← h.var 0]
  exact integral_nonneg fun ω => sq_nonneg _

end ShockMDS2

/-- Cochrane (2023), p. 501: bounded martingale-difference shocks (`ShockMDS`) are
square-integrable ones. -/
theorem ShockMDS.toShockMDS2 (h : ShockMDS S ε σ2) : ShockMDS2 S ε σ2 :=
  ⟨h.adapted, h.mds, SurplusRegressionL2.memLp_shock h, h.var, h.presampleMean, h.presampleOrth⟩

/-! ### The shocks and moving averages in `L²` -/

/-- Cochrane (2023), p. 501: the shock `ε_k` as an element of `L²(P)`. -/
noncomputable def shockL2 (h : ShockMDS2 S ε σ2) (k : ℤ) : Lp ℝ 2 S.μ :=
  (h.memLp k).toLp (ε k)

/-- Cochrane (2023), p. 501: the shocks are orthogonal in `L²` with `‖ε_k‖² = σ²`. -/
theorem inner_shockL2 (h : ShockMDS2 S ε σ2) (j k : ℤ) :
    inner ℝ (shockL2 h j) (shockL2 h k) = if j = k then σ2 else 0 := by
  rw [L2.inner_def, ← h.integral_mul j k]
  refine integral_congr_ae ?_
  filter_upwards [(h.memLp j).coeFn_toLp, (h.memLp k).coeFn_toLp] with ω h1 h2
  rw [Real.inner_apply]
  simp only [shockL2]
  rw [h1, h2]

/-- Cochrane (2023), p. 501 (Pythagoras): `‖∑_{k ∈ s} c_k ε_{τ−k}‖² = σ² ∑_{k ∈ s} c_k²`. -/
theorem norm_sq_finset (h : ShockMDS2 S ε σ2) (c : ℕ → ℝ) (τ : ℤ) (s : Finset ℕ) :
    ‖∑ k ∈ s, c k • shockL2 h (τ - k)‖ ^ 2 = σ2 * ∑ k ∈ s, c k ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right, inner_shockL2,
    sub_right_inj, Nat.cast_inj, mul_ite, mul_zero, Finset.sum_ite_eq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [hk, ↓reduceIte]
  ring

/-- Cochrane (2023), p. 501: for square-summable `c` the moving average `∑_k c_k ε_{τ−k}`
converges in `L²`. -/
theorem summable_ma (h : ShockMDS2 S ε σ2) {c : ℕ → ℝ} (hc : Summable fun k => c k ^ 2)
    (τ : ℤ) : Summable fun k => c k • shockL2 h (τ - k) := by
  have hσ := h.var_nonneg
  rw [summable_iff_vanishing_norm]
  intro e he
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.1 hc (e ^ 2 / (σ2 + 1)) (by positivity)
  refine ⟨s, fun t ht => ?_⟩
  have h1 := hs t ht
  have h0 : 0 ≤ ∑ k ∈ t, c k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h0] at h1
  have h2 : ‖∑ k ∈ t, c k • shockL2 h (τ - k)‖ ^ 2 < e ^ 2 := by
    rw [norm_sq_finset]
    have h3 : σ2 * ∑ k ∈ t, c k ^ 2 ≤ σ2 * (e ^ 2 / (σ2 + 1)) :=
      mul_le_mul_of_nonneg_left h1.le hσ
    have h4 : σ2 * (e ^ 2 / (σ2 + 1)) < e ^ 2 := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith [sq_pos_of_pos he]
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 he.le h2

/-- Cochrane (2023), p. 501: the moving average `c(L)ε_τ = ∑_k c_k ε_{τ−k}` in `L²`. -/
noncomputable def maL2 (h : ShockMDS2 S ε σ2) (c : ℕ → ℝ) (τ : ℤ) : Lp ℝ 2 S.μ :=
  ∑' k, c k • shockL2 h (τ - k)

/-- Cochrane (2023), p. 501: `E[c(L)ε_{τ+h} ε_{τ−m}] = σ² c_{m+h}`. -/
theorem inner_maL2_shock (h : ShockMDS2 S ε σ2) {c : ℕ → ℝ} (hc : Summable fun k => c k ^ 2)
    (τ : ℤ) (hh m : ℕ) :
    inner ℝ (maL2 h c (τ + hh)) (shockL2 h (τ - m)) = σ2 * c (m + hh) := by
  rw [maL2, inner_tsum_left _ (summable_ma h hc _)]
  simp only [real_inner_smul_left, inner_shockL2]
  rw [tsum_eq_single (m + hh) fun k hk => by
    have : ¬ (τ + hh - k = τ - m) := by intro he; apply hk; omega
    simp [this]]
  have : τ + hh - ((m + hh : ℕ) : ℤ) = τ - m := by push_cast; ring
  simp only [this, ↓reduceIte]
  ring

/-- Cochrane (2023), p. 501 (covariances of square-summable moving averages of square-integrable
shocks): `E[a(L)ε_{τ+h} · b(L)ε_τ] = σ² ∑_m a_{m+h} b_m`. -/
theorem inner_maL2_maL2 (h : ShockMDS2 S ε σ2) {a b : ℕ → ℝ} (ha : Summable fun k => a k ^ 2)
    (hb : Summable fun k => b k ^ 2) (τ : ℤ) (hh : ℕ) :
    inner ℝ (maL2 h a (τ + hh)) (maL2 h b τ) = σ2 * ∑' m, a (m + hh) * b m := by
  rw [show maL2 h b τ = ∑' k, b k • shockL2 h (τ - k) from rfl,
    inner_tsum_right _ (summable_ma h hb τ)]
  simp only [real_inner_smul_right, inner_maL2_shock h ha]
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by ring

/-- Cochrane (2023), Online Appendix p. 602: `E_t ε_k = ε_k 1{k ≤ t}` in `L²`. -/
theorem proj_shock (h : ShockMDS2 S ε σ2) (t : ℕ) (k : ℤ) :
    proj S t (shockL2 h k) = if k ≤ t then shockL2 h k else 0 := by
  apply Lp.ext
  have hE := (proj_ae t (shockL2 h k)).trans (S.E_congr (h.memLp k).coeFn_toLp t)
  by_cases hk : k ≤ t
  · simp only [hk, ↓reduceIte]
    refine hE.trans ?_
    rw [S.E_of_stronglyMeasurable (h.adapted k t hk) (h.integrable k)]
    exact (h.memLp k).coeFn_toLp.symm
  · simp only [hk, ↓reduceIte]
    refine (hE.trans (h.E_future (by omega))).trans ?_
    exact (Lp.coeFn_zero ℝ 2 S.μ).symm

/-- Cochrane (2023), p. 501: `E_t a(L)ε_{t+1+j} = ∑_m a_{m+j+1} ε_{t−m}` in `L²`. -/
theorem proj_maL2 (h : ShockMDS2 S ε σ2) {c : ℕ → ℝ} (hc : Summable fun k => c k ^ 2)
    (t j : ℕ) :
    proj S t (maL2 h c ((t + 1 + j : ℕ) : ℤ)) = maL2 h (fun m => c (m + j + 1)) t := by
  set τ : ℤ := ((t + 1 + j : ℕ) : ℤ) with hτ
  have hs := summable_ma h hc τ
  have hP : HasSum (fun k => c k • (if τ - k ≤ t then shockL2 h (τ - k) else 0))
      (proj S t (maL2 h c τ)) := by
    have := (hs.mapL (proj S t)).hasSum
    rw [← (proj S t).map_tsum hs] at this
    refine this.congr_fun fun k => ?_
    rw [map_smul, proj_shock]
  have h1 := (hasSum_nat_add_iff' (j + 1)).mpr hP
  have hz : ∑ i ∈ Finset.range (j + 1), c i • (if τ - i ≤ t then shockL2 h (τ - i) else 0) =
      0 := Finset.sum_eq_zero fun i hi => by
    have : ¬ (τ - i ≤ t) := by simp only [Finset.mem_range] at hi; omega
    simp [this]
  rw [hz, sub_zero] at h1
  rw [← h1.tsum_eq]
  refine tsum_congr fun m => ?_
  have c2 : τ - ((m + (j + 1) : ℕ) : ℤ) = (t : ℤ) - m := by omega
  have c3 : (t : ℤ) - m ≤ t := by omega
  simp only [c2, c3, ↓reduceIte]
  rfl

/-! ### Surpluses and the value of debt -/

/-- Cochrane (2023), p. 501: the surplus `s_n = a(L)ε_n ∈ L²` at the model dates `n ∈ ℕ`. -/
noncomputable def surplusL2 (h : ShockMDS2 S ε σ2) (a : ℕ → ℝ) (n : ℕ) : Lp ℝ 2 S.μ :=
  maL2 h a n

/-- Cochrane (2023), p. 501: `‖a(L)ε_τ‖² = σ² ∑ a_k²`. -/
theorem norm_maL2_sq (h : ShockMDS2 S ε σ2) {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2)
    (τ : ℤ) : ‖maL2 h a τ‖ ^ 2 = σ2 * ∑' k, a k ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have := inner_maL2_maL2 h ha ha τ 0
  simp only [Nat.cast_zero, add_zero] at this
  rw [this]
  simp only [sq]

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602: the ex-post present value
`PV_t = ∑_{j ≥ 0} ρ^j s_{t+1+j}` as an `L²`-convergent series. -/
noncomputable def pvL2 (h : ShockMDS2 S ε σ2) (ρ : ℝ) (a : ℕ → ℝ) (t : ℕ) : Lp ℝ 2 S.μ :=
  ∑' j, ρ ^ j • surplusL2 h a (t + 1 + j)

/-- Cochrane (2023), p. 501: for `|ρ| < 1` the present-value series converges in `L²`. -/
theorem summable_pv (h : ShockMDS2 S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    Summable fun j => ρ ^ j • surplusL2 h a (t + 1 + j) := by
  have hn : ∀ n : ℕ, ‖surplusL2 h a n‖ = Real.sqrt (σ2 * ∑' k, a k ^ 2) := fun n => by
    rw [← norm_maL2_sq h ha n, Real.sqrt_sq (norm_nonneg _)]
    rfl
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right (Real.sqrt (σ2 * ∑' k, a k ^ 2)))
    fun j => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_pow, hn]

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602 (**the value of debt**): the valuation
equation `v_t = E_t PV_t` with Mathlib's conditional expectation of the `L²` present value. -/
noncomputable def valueL2 (h : ShockMDS2 S ε σ2) (ρ : ℝ) (a : ℕ → ℝ) (t : ℕ) : Ω → ℝ :=
  S.E t (pvL2 h ρ a t)

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602: `E_t PV_t = b(L)ε_t` in `L²`,
`b_m = ∑_j ρ^j a_{m+1+j}`. -/
theorem proj_pvL2 (h : ShockMDS2 S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    proj S t (pvL2 h ρ a t) = maL2 h (bCoeff ρ a) t := by
  have hpv := summable_pv h hρ ha t
  have htail : ∀ j, Summable fun m => a (m + j + 1) ^ 2 := fun j =>
    (summable_nat_add_iff (j + 1)).mpr ha
  have hb := bCoeff_sq_summable hρ ha
  set W : ℕ → Lp ℝ 2 S.μ := fun j => maL2 h (fun m => a (m + j + 1)) t with hW
  have hY : proj S t (pvL2 h ρ a t) = ∑' j, ρ ^ j • W j := by
    rw [pvL2, (proj S t).map_tsum hpv]
    exact tsum_congr fun j => by rw [map_smul, surplusL2, proj_maL2 h ha]
  have hYs : Summable fun j => ρ ^ j • W j := by
    have := hpv.mapL (proj S t)
    refine this.congr fun j => ?_
    rw [map_smul, surplusL2, proj_maL2 h ha]
  rw [hY]
  set Y := ∑' j, ρ ^ j • W j
  set Z := maL2 h (bCoeff ρ a) t
  set D := Y - Z with hD
  have hWe : ∀ j n : ℕ, inner ℝ (W j) (shockL2 h ((t : ℤ) - n)) = σ2 * a (n + j + 1) := by
    intro j n
    have := inner_maL2_shock h (htail j) t 0 n
    simp only [Nat.cast_zero, add_zero] at this
    exact this
  have hDe : ∀ n : ℕ, inner ℝ D (shockL2 h ((t : ℤ) - n)) = 0 := by
    intro n
    rw [hD, inner_sub_left, inner_tsum_left _ hYs]
    simp only [real_inner_smul_left, hWe]
    have hZ := inner_maL2_shock h hb t 0 n
    simp only [Nat.cast_zero, add_zero] at hZ
    rw [hZ]
    simp only [bCoeff, bInf]
    rw [← tsum_mul_left]
    rw [sub_eq_zero]
    exact tsum_congr fun j => by ring
  have hDW : ∀ j, inner ℝ D (W j) = 0 := by
    intro j
    rw [show W j = ∑' m, a (m + j + 1) • shockL2 h ((t : ℤ) - m) from rfl,
      inner_tsum_right _ (summable_ma h (htail j) _)]
    simp only [real_inner_smul_right, hDe, mul_zero, tsum_zero]
  have hDY : inner ℝ D Y = 0 := by
    rw [inner_tsum_right _ hYs]
    simp only [real_inner_smul_right, hDW, mul_zero, tsum_zero]
  have hDZ : inner ℝ D Z = 0 := by
    rw [show Z = ∑' m, bCoeff ρ a m • shockL2 h ((t : ℤ) - m) from rfl,
      inner_tsum_right _ (summable_ma h hb _)]
    simp only [real_inner_smul_right, hDe, mul_zero, tsum_zero]
  have hDD : inner ℝ D D = 0 := by
    conv_rhs => rw [← sub_self (0 : ℝ)]
    nth_rewrite 2 [hD]
    rw [inner_sub_right, hDY, hDZ]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hDD)

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602 (**the value of debt with square-integrable
shocks**): `v_t = E_t PV_t = b(L)ε_t` a.e. -/
theorem valueL2_ae (h : ShockMDS2 S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    valueL2 h ρ a t =ᵐ[S.μ] maL2 h (bCoeff ρ a) t := by
  have := (proj_ae t (pvL2 h ρ a t)).symm
  rw [proj_pvL2 h hρ ha t] at this
  exact this

/-! ### Theorem RG -/

/-- Cochrane (2023), p. 501: an `L²` moving average of the shocks has mean zero. -/
theorem integral_maL2 (h : ShockMDS2 S ε σ2) {c : ℕ → ℝ} (hc : Summable fun k => c k ^ 2)
    (τ : ℤ) : ∫ ω, maL2 h c τ ω ∂S.μ = 0 := by
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) 2 S.μ := memLp_const 1
  have hone : ∀ X : Lp ℝ 2 S.μ, inner ℝ (h1.toLp _) X = ∫ ω, X ω ∂S.μ := by
    intro X
    rw [← integral_mul_eq_inner]
    refine integral_congr_ae ?_
    filter_upwards [h1.coeFn_toLp] with ω hω
    rw [hω, one_mul]
  rw [← hone, maL2, inner_tsum_right _ (summable_ma h hc τ)]
  simp only [real_inner_smul_right]
  simp only [hone]
  refine (tsum_congr fun k => ?_).trans tsum_zero
  rw [shockL2, integral_congr_ae (h.memLp _).coeFn_toLp, h.integral_eq_zero, mul_zero]

/-- Cochrane (2023), p. 501: the value of debt has mean zero. -/
theorem integral_valueL2 (h : ShockMDS2 S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) : ∫ ω, valueL2 h ρ a t ω ∂S.μ = 0 := by
  rw [integral_congr_ae (valueL2_ae h hρ ha t)]
  exact integral_maL2 h (bCoeff_sq_summable hρ ha) t

/-- Cochrane (2023), p. 501 (**covariance of surpluses with lagged debt, square-integrable
shocks**): `Cov(s_{t+1}, v_t) = σ² ∑_m a_{m+1} b_m` (Mathlib `covariance`). -/
theorem cov_surplus_valueL2 (h : ShockMDS2 S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    cov[surplusL2 h a (t + 1), valueL2 h ρ a t; S.μ] = σ2 * covInf ρ (fun k => a (k + 1)) := by
  rw [covariance, integral_valueL2 h hρ ha t,
    show ∫ ω, surplusL2 h a (t + 1) ω ∂S.μ = 0 from integral_maL2 h ha _]
  simp only [sub_zero]
  calc ∫ ω, surplusL2 h a (t + 1) ω * valueL2 h ρ a t ω ∂S.μ
      = ∫ ω, maL2 h a ((t : ℤ) + ((1 : ℕ) : ℤ)) ω * maL2 h (bCoeff ρ a) t ω ∂S.μ := by
        refine integral_congr_ae ?_
        filter_upwards [valueL2_ae h hρ ha t] with ω hω
        rw [hω, surplusL2, Nat.cast_add]
    _ = inner ℝ (maL2 h a ((t : ℤ) + ((1 : ℕ) : ℤ))) (maL2 h (bCoeff ρ a) t) :=
        integral_mul_eq_inner _ _
    _ = σ2 * ∑' m, a (m + 1) * bCoeff ρ a m :=
        inner_maL2_maL2 h ha (bCoeff_sq_summable hρ ha) t 1
    _ = σ2 * covInf ρ (fun k => a (k + 1)) := rfl

/-- Cochrane (2023), p. 501: `Var(v_t) = σ² ∑_m b_m²` (square-integrable shocks). -/
theorem var_valueL2 (h : ShockMDS2 S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    Var[valueL2 h ρ a t; S.μ] = σ2 * ∑' m, bCoeff ρ a m ^ 2 := by
  have hb := bCoeff_sq_summable hρ ha
  rw [← covariance_self (X := valueL2 h ρ a t)
    (S.integrable_E t _).aestronglyMeasurable.aemeasurable, covariance,
    integral_valueL2 h hρ ha]
  simp only [sub_zero]
  calc ∫ ω, valueL2 h ρ a t ω * valueL2 h ρ a t ω ∂S.μ
      = ∫ ω, maL2 h (bCoeff ρ a) ((t : ℤ) + ((0 : ℕ) : ℤ)) ω *
          maL2 h (bCoeff ρ a) t ω ∂S.μ := by
        refine integral_congr_ae ?_
        filter_upwards [valueL2_ae h hρ ha t] with ω hω
        rw [hω, Nat.cast_zero, add_zero]
    _ = inner ℝ (maL2 h (bCoeff ρ a) ((t : ℤ) + ((0 : ℕ) : ℤ))) (maL2 h (bCoeff ρ a) t) :=
        integral_mul_eq_inner _ _
    _ = σ2 * ∑' m, bCoeff ρ a (m + 0) * bCoeff ρ a m := inner_maL2_maL2 h hb hb t 0
    _ = σ2 * ∑' m, bCoeff ρ a m ^ 2 := by simp only [add_zero, sq]

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (**Theorem RG with
square-integrable martingale-difference shocks**): `2 Cov(s_{t+1}, v_t) = σ² (∑_{k≥1} a_k² +
∑_{k,l≥1} ρ^{|k−l|} a_k a_l)`, for every square-summable moving average. -/
theorem two_covL2_eq_kms (h : ShockMDS2 S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    2 * cov[surplusL2 h a (t + 1), valueL2 h ρ a t; S.μ] =
      σ2 * (∑' k, a (k + 1) ^ 2 + kmsInf ρ (fun k => a (k + 1))) := by
  rw [cov_surplus_valueL2 h hρ ha t,
    ← two_covInf_eq_of_sq hρ ((summable_nat_add_iff 1).mpr ha)]
  ring

/-- Cochrane (2023), p. 501, §24.1 p. 519 (Theorem RG, sign, square-integrable shocks): with
`σ² > 0` the covariance of surpluses with lagged debt is positive iff the surplus is not white
noise. -/
theorem covL2_pos_iff (h : ShockMDS2 S ε σ2) (hσ : 0 < σ2) {ρ : ℝ} (hρ : |ρ| < 1)
    {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    0 < cov[surplusL2 h a (t + 1), valueL2 h ρ a t; S.μ] ↔ ¬ IsIID a := by
  rw [cov_surplus_valueL2 h hρ ha t, mul_pos_iff_of_pos_left hσ]
  exact covInf_pos_iff_of_sq hρ ha

/-- Cochrane (2023), p. 501: the regression coefficient of `s_{t+1}` on `v_t` is
`∑_m a_{m+1} b_m / ∑_m b_m²` (square-integrable shocks; `σ²` cancels). -/
theorem regL2_eq (h : ShockMDS2 S ε σ2) (hσ : σ2 ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    regM S.μ (surplusL2 h a (t + 1)) (valueL2 h ρ a t) =
      covInf ρ (fun k => a (k + 1)) / ∑' m, bCoeff ρ a m ^ 2 := by
  rw [regM, cov_surplus_valueL2 h hρ ha t, var_valueL2 h hρ ha t, mul_div_mul_left _ _ hσ]

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (**Theorem RG, regression
form, square-integrable martingale-difference shocks**): the regression coefficient of surpluses
on lagged debt is strictly positive iff the surplus is not white noise. -/
theorem regL2_pos_iff (h : ShockMDS2 S ε σ2) (hσ : 0 < σ2) {ρ : ℝ} (hρ : |ρ| < 1)
    {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    0 < regM S.μ (surplusL2 h a (t + 1)) (valueL2 h ρ a t) ↔ ¬ IsIID a := by
  rw [regL2_eq h hσ.ne' hρ ha t]
  exact regInf_pos_iff_of_sq hρ ha

/-! ### Link with the bounded case -/

/-- Cochrane (2023), p. 501 (**link**): for bounded shocks the value of debt is that of
`SurplusRegressionL2`. -/
theorem valueL2_eq_bounded (h : ShockMDS S ε σ2) (ρ : ℝ) (a : ℕ → ℝ) (t : ℕ) :
    valueL2 (ShockMDS.toShockMDS2 h) ρ a t = SurplusRegressionL2.valueL2 h ρ a t := rfl

/-- Cochrane (2023), p. 501 (**link**): for bounded shocks the surplus and the regression
coefficient are those of `SurplusRegressionL2`. -/
theorem regL2_eq_bounded (h : ShockMDS S ε σ2) (ρ : ℝ) (a : ℕ → ℝ) (t : ℕ) :
    surplusL2 (ShockMDS.toShockMDS2 h) a (t + 1) = SurplusRegressionL2.surplusL2 h a (t + 1) ∧
      regM S.μ (surplusL2 (ShockMDS.toShockMDS2 h) a (t + 1))
        (valueL2 (ShockMDS.toShockMDS2 h) ρ a t) =
      regM S.μ (SurplusRegressionL2.surplusL2 h a (t + 1))
        (SurplusRegressionL2.valueL2 h ρ a t) := ⟨rfl, rfl⟩

/-! ### The i.i.d. economy with unbounded shocks -/

variable {ν : ProbabilityMeasure ℝ}

/-- Cochrane (2023), p. 501: in the i.i.d. economy each shock is square-integrable when the law
`ν` has a finite second moment. -/
theorem memLp_shockZ (hν : MemLp id 2 (ν : Measure ℝ)) (k : ℤ) :
    MemLp (shockZ k) 2 (iidZSystem ν).μ :=
  hν.comp_measurePreserving (measurePreserving_eval_infinitePi (fun _ => (ν : Measure ℝ)) k)

/-- Cochrane (2023), p. 501: i.i.d. square-integrable shocks are uncorrelated,
`E[ε_j ε_k] = σ² 1{j = k}`. -/
theorem integral_shockZ_mul_L2 {σ2' : ℝ} (hν : MemLp id 2 (ν : Measure ℝ))
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2')
    (j k : ℤ) :
    ∫ ω, shockZ j ω * shockZ k ω ∂(iidZSystem ν).μ = if j = k then σ2' else 0 := by
  by_cases hjk : j = k
  · subst hjk
    simp only [↓reduceIte]
    rw [← hvar, ← integral_shockZ_fun ν j (f := fun x => x ^ 2) (measurable_id.pow_const 2)]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp [sq])
  · simp only [hjk, ↓reduceIte]
    have hind : IndepFun (shockZ j) (shockZ k) (iidZSystem ν).μ :=
      (iIndepFun_infinitePi (P := fun _ => (ν : Measure ℝ)) (X := fun _ => id)
        (fun _ => measurable_id)).indepFun hjk
    have h := hind.integral_mul_eq_mul_integral
      ((memLp_shockZ hν j).integrable one_le_two).aestronglyMeasurable
      ((memLp_shockZ hν k).integrable one_le_two).aestronglyMeasurable
    rw [Pi.mul_def] at h
    rw [h, integral_shockZ_fun ν j (f := fun x => x) measurable_id, hmean, zero_mul]

/-- Cochrane (2023), p. 501: the i.i.d. shocks with an infinite past, mean zero and variance
`σ²` — with no bound on their support — satisfy `ShockMDS2`. -/
theorem iidZ_shockMDS2 {σ2' : ℝ} (hν : MemLp id 2 (ν : Measure ℝ))
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2') :
    ShockMDS2 (iidZSystem ν) shockZ σ2' :=
  ⟨fun _ _ hkt => (measurable_shockZ ν hkt).stronglyMeasurable,
    fun _ => E_shockZ_zero hmean (by omega), memLp_shockZ hν,
    fun k => by
      rw [integral_shockZ_fun ν k (f := fun x => x ^ 2) (measurable_id.pow_const 2), hvar],
    fun k _ => by rw [integral_shockZ_fun ν k (f := fun x => x) measurable_id, hmean],
    fun j k _ _ hjk => by rw [integral_shockZ_mul_L2 hν hmean hvar j k]; simp [hjk]⟩

/-- Cochrane (2023), p. 501: if the law of the shocks gives positive probability to
`{|x| > M}` for every `M`, the shocks are not essentially bounded, so `ShockMDS` fails. -/
theorem iidZ_not_shockMDS {σ2' : ℝ} (hunb : ∀ M : ℝ, (ν : Measure ℝ) {x | M < |x|} ≠ 0) :
    ¬ Nonempty (ShockMDS (iidZSystem ν) shockZ σ2') := by
  rintro ⟨h⟩
  obtain ⟨M, hM⟩ := h.bdd
  apply hunb M
  have hmp : MeasurePreserving (fun ω : ℤ → ℝ => ω 0) (iidZSystem ν).μ (ν : Measure ℝ) :=
    measurePreserving_eval_infinitePi (fun _ => (ν : Measure ℝ)) 0
  have hmeas : MeasurableSet {x : ℝ | M < |x|} := measurableSet_lt measurable_const
    continuous_abs.measurable
  rw [← hmp.measure_preimage hmeas.nullMeasurableSet]
  have := ae_iff.1 (hM 0)
  simpa only [not_le, Set.preimage_ofPred_eq, shockZ] using this

/-- Cochrane (2023), p. 501: the centred normal law `N(0, v)` as a probability measure on `ℝ`. -/
noncomputable def gauss (v : NNReal) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 v, inferInstance⟩

/-- Cochrane (2023), p. 501: i.i.d. normal shocks `N(0, v)` with an infinite past satisfy
`ShockMDS2` with `σ² = v`. -/
theorem gaussZ_shockMDS2 (v : NNReal) : ShockMDS2 (iidZSystem (gauss v)) shockZ v := by
  have hmean : ∫ x, x ∂((gauss v : ProbabilityMeasure ℝ) : Measure ℝ) = 0 :=
    integral_id_gaussianReal
  have hvar : ∫ x, x ^ 2 ∂((gauss v : ProbabilityMeasure ℝ) : Measure ℝ) = v := by
    change ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v
    have h := variance_id_gaussianReal (μ := 0) (v := v)
    rw [variance_eq_integral measurable_id.aemeasurable] at h
    simpa [integral_id_gaussianReal] using h
  exact iidZ_shockMDS2 (memLp_id_gaussianReal 2) hmean hvar

/-- Cochrane (2023), p. 501: normal shocks with `v > 0` are not essentially bounded, so the
bounded versions of Theorem RG (`SurplusRegressionMeasure`, `SurplusRegressionL2`) do not apply
to them. -/
theorem gaussZ_not_shockMDS {v : NNReal} (hv : v ≠ 0) :
    ¬ Nonempty (ShockMDS (iidZSystem (gauss v)) shockZ v) := by
  refine iidZ_not_shockMDS fun M h0 => ?_
  have hvol : (MeasureTheory.volume : Measure ℝ) {x | M < |x|} = 0 :=
    gaussianReal_absolutelyContinuous' 0 hv h0
  have hsub : Set.Ioi (|M| + 1) ⊆ {x : ℝ | M < |x|} := fun x hx => by
    simp only [Set.mem_Ioi] at hx
    change M < |x|
    have := le_abs_self M
    have := le_abs_self x
    linarith
  have := measure_mono_null hsub hvol
  rw [Real.volume_Ioi] at this
  exact ENNReal.top_ne_zero this

/-- Cochrane (2023), p. 501, §24.1 p. 519 (**Theorem RG with unbounded shocks**): with i.i.d.
normal shocks `N(0, v)`, `v > 0`, for every square-summable surplus moving average,
`2 Cov(s_{t+1}, v_t) = v (∑ a_k² + ∑∑ ρ^{|k−l|} a_k a_l)` and the regression coefficient of
surpluses on debt is positive iff the surplus is not white noise. -/
theorem gaussZ_theoremRG {v : NNReal} (hv : v ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    2 * cov[surplusL2 (gaussZ_shockMDS2 v) a (t + 1), valueL2 (gaussZ_shockMDS2 v) ρ a t;
        (iidZSystem (gauss v)).μ] = v * (∑' k, a (k + 1) ^ 2 + kmsInf ρ (fun k => a (k + 1))) ∧
    (0 < regM (iidZSystem (gauss v)).μ (surplusL2 (gaussZ_shockMDS2 v) a (t + 1))
        (valueL2 (gaussZ_shockMDS2 v) ρ a t) ↔ ¬ IsIID a) :=
  ⟨two_covL2_eq_kms _ hρ ha t,
    regL2_pos_iff _ (lt_of_le_of_ne v.2 (fun h => hv (NNReal.coe_eq_zero.1 h.symm))) hρ ha t⟩

/-- Cochrane (2023), p. 501, §24.1 p. 519: with i.i.d. normal shocks the harmonic surplus
`s_t = ∑_{k ≥ 1} ε_{t−k}/k` (square-summable, not absolutely summable) has a strictly positive
regression coefficient on debt. -/
theorem gaussZ_harmonic_regL2_pos {v : NNReal} (hv : v ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    0 < regM (iidZSystem (gauss v)).μ (surplusL2 (gaussZ_shockMDS2 v) harmonicCoeff (t + 1))
      (valueL2 (gaussZ_shockMDS2 v) ρ harmonicCoeff t) := by
  obtain ⟨h2, -⟩ := harmonic_sq_not_abs
  refine ((gaussZ_theoremRG hv hρ h2 t).2).2 fun hiid => ?_
  have := hiid 1 le_rfl
  simp at this

end Cochrane.ObservationalEquivalence.TidyR5ShockL2
