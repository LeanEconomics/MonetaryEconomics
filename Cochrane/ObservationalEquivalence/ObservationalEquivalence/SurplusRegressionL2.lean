/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.SurplusRegressionMeasure
import ObservationalEquivalence.SquareSummableRG
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Theorem RG for square-summable moving averages in `L²`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, p. 501, Chapter 24,
§24.1, p. 519, and Online Appendix Chapter 2, introduction, p. 593.

A moving average `s_t = ∑_k a_k ε_{t−k}` with square-summable but not absolutely summable
coefficients need not converge pointwise; it converges in `L²`. This module works in the Hilbert
space `L²(P)` (Mathlib's `Lp ℝ 2`) of a `MeasExpectationSystem` with `ShockMDS` shocks:

* `shockL2 h k`: the shock `ε_k` as an element of `L²`; `inner_shockL2`: the shocks are
  orthogonal with `‖ε_k‖² = σ²` (`E[ε_j ε_k] = σ² 1{j = k}`).
* `maL2 h c τ = ∑_k c_k ε_{τ−k}`, an `L²`-convergent series for every square-summable `c`
  (`summable_ma`); `inner_maL2_maL2`: `E[a(L)ε_{τ+h} b(L)ε_τ] = σ² ∑_m a_{m+h} b_m`.
* `proj S t`: Mathlib's `condExpL2` (the orthogonal projection on date-`t` measurable functions);
  `proj_ae`: it is `E_t` a.e.; `proj_shock`: it keeps `ε_k` for `k ≤ t` and kills it for `k > t`.
* The value of debt from the valuation equation, `v_t = E_t PV_t`, where
  `PV_t = ∑_j ρ^j s_{t+1+j}` is the `L²` present value (`pvL2`) and `E_t` is Mathlib's `condExp`
  (`valueL2`); `valueL2_ae`: `v_t = b(L)ε_t` a.e., `b_m = ∑_j ρ^j a_{m+1+j}`.
* **Theorem RG for square-summable moving averages**: `cov_surplus_valueL2`
  (`Cov(s_{t+1}, v_t) = σ² ∑_m a_{m+1} b_m`), `var_valueL2`, `two_covL2_eq_kms`
  (`2 Cov = σ² (∑ a_k² + ∑∑ ρ^{|k−l|} a_k a_l)`), `covL2_pos_iff`, `regL2_pos_iff`.
* Link with the absolutely summable case: `maL2_ae_maInf` (the `L²` sum is the pointwise sum),
  `valueL2_ae_valueM` (the two values of debt agree a.e.).
* `coinZ_harmonic_regL2_pos`: in the i.i.d. coin economy the surplus `a_k = 1/k`, which is
  square-summable but not absolutely summable (`harmonic_sq_not_abs`), has a strictly positive
  regression coefficient of surpluses on debt.
-/

namespace Cochrane.ObservationalEquivalence.SurplusRegressionL2

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationsMeasure
open Cochrane.ObservationalEquivalence.ExpectationsMeasureIIDZ
open Cochrane.ObservationalEquivalence.MACovariance
open Cochrane.ObservationalEquivalence.SurplusRegression
open Cochrane.ObservationalEquivalence.SurplusRegressionMeasure
open Cochrane.ObservationalEquivalence.SquareSummableRG

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω} {ε : ℤ → Ω → ℝ}
  {σ2 : ℝ}

/-! ### The shocks in `L²` -/

/-- Cochrane (2023), p. 501: each shock is square-integrable. -/
theorem memLp_shock (h : ShockMDS S ε σ2) (k : ℤ) : MemLp (ε k) 2 S.μ := by
  obtain ⟨M, hM⟩ := h.bdd
  exact MemLp.of_bound (h.aesm k) M ((hM k).mono fun ω h1 => by rwa [Real.norm_eq_abs])

/-- Cochrane (2023), p. 501: the shock variance is nonnegative. -/
theorem var_nonneg (h : ShockMDS S ε σ2) : 0 ≤ σ2 := by
  rw [← h.var 0]
  exact integral_nonneg fun ω => sq_nonneg _

/-- Cochrane (2023), p. 501: the shock `ε_k` as an element of `L²(P)`. -/
noncomputable def shockL2 (h : ShockMDS S ε σ2) (k : ℤ) : Lp ℝ 2 S.μ :=
  (memLp_shock h k).toLp (ε k)

/-- Cochrane (2023), p. 501: the shocks are orthogonal in `L²` with `‖ε_k‖² = σ²`. -/
theorem inner_shockL2 (h : ShockMDS S ε σ2) (j k : ℤ) :
    inner ℝ (shockL2 h j) (shockL2 h k) = if j = k then σ2 else 0 := by
  rw [L2.inner_def, ← h.integral_mul j k]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_shock h j).coeFn_toLp, (memLp_shock h k).coeFn_toLp] with ω h1 h2
  rw [Real.inner_apply]
  simp only [shockL2]
  rw [h1, h2]

/-- Cochrane (2023), p. 501 (Pythagoras): `‖∑_{k ∈ s} c_k ε_{τ−k}‖² = σ² ∑_{k ∈ s} c_k²`. -/
theorem norm_sq_finset (h : ShockMDS S ε σ2) (c : ℕ → ℝ) (τ : ℤ) (s : Finset ℕ) :
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
theorem summable_ma (h : ShockMDS S ε σ2) {c : ℕ → ℝ} (hc : Summable fun k => c k ^ 2)
    (τ : ℤ) : Summable fun k => c k • shockL2 h (τ - k) := by
  have hσ := var_nonneg h
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
noncomputable def maL2 (h : ShockMDS S ε σ2) (c : ℕ → ℝ) (τ : ℤ) : Lp ℝ 2 S.μ :=
  ∑' k, c k • shockL2 h (τ - k)

/-- Cochrane (2023), p. 501 (tool): the inner product passes through a convergent series on the
right. -/
theorem inner_tsum_right (x : Lp ℝ 2 S.μ) {f : ℕ → Lp ℝ 2 S.μ} (hf : Summable f) :
    inner ℝ x (∑' k, f k) = ∑' k, inner ℝ x (f k) := by
  have := (innerSL ℝ x).map_tsum hf
  simpa only [innerSL_apply_apply] using this

/-- Cochrane (2023), p. 501 (tool): the inner product passes through a convergent series on the
left. -/
theorem inner_tsum_left (x : Lp ℝ 2 S.μ) {f : ℕ → Lp ℝ 2 S.μ} (hf : Summable f) :
    inner ℝ (∑' k, f k) x = ∑' k, inner ℝ (f k) x := by
  rw [real_inner_comm, inner_tsum_right x hf]
  exact tsum_congr fun k => real_inner_comm _ _

/-- Cochrane (2023), p. 501: `E[c(L)ε_{τ+h} ε_{τ−m}] = σ² c_{m+h}`. -/
theorem inner_maL2_shock (h : ShockMDS S ε σ2) {c : ℕ → ℝ} (hc : Summable fun k => c k ^ 2)
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

/-- Cochrane (2023), p. 501 (covariances of square-summable moving averages):
`E[a(L)ε_{τ+h} · b(L)ε_τ] = σ² ∑_m a_{m+h} b_m`. -/
theorem inner_maL2_maL2 (h : ShockMDS S ε σ2) {a b : ℕ → ℝ} (ha : Summable fun k => a k ^ 2)
    (hb : Summable fun k => b k ^ 2) (τ : ℤ) (hh : ℕ) :
    inner ℝ (maL2 h a (τ + hh)) (maL2 h b τ) = σ2 * ∑' m, a (m + hh) * b m := by
  rw [show maL2 h b τ = ∑' k, b k • shockL2 h (τ - k) from rfl,
    inner_tsum_right _ (summable_ma h hb τ)]
  simp only [real_inner_smul_right, inner_maL2_shock h ha]
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by ring

/-! ### Conditional expectations as orthogonal projections -/

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` on `L²`, Mathlib's `condExpL2` (the orthogonal
projection onto the date-`t` measurable functions), as a continuous linear map `L² → L²`. -/
noncomputable def proj (S : MeasExpectationSystem Ω) (t : ℕ) : Lp ℝ 2 S.μ →L[ℝ] Lp ℝ 2 S.μ :=
  (lpMeas ℝ ℝ (S.𝓕 t) 2 S.μ).subtypeL.comp (condExpL2 ℝ ℝ (S.𝓕.le t))

/-- Cochrane (2023), Ch. 2, pp. 29–30: the projection is the conditional expectation `E_t`
(a.e.). -/
theorem proj_ae (t : ℕ) (X : Lp ℝ 2 S.μ) : proj S t X =ᵐ[S.μ] S.E t X := by
  have := (Lp.memLp X).condExpL2_ae_eq_condExp (𝕜 := ℝ) (S.𝓕.le t)
  rw [Lp.toLp_coeFn] at this
  exact this

/-- Cochrane (2023), Online Appendix p. 602: `E_t` keeps the realised shocks and kills the
future ones, `E_t ε_k = ε_k 1{k ≤ t}` in `L²`. -/
theorem proj_shock (h : ShockMDS S ε σ2) (t : ℕ) (k : ℤ) :
    proj S t (shockL2 h k) = if k ≤ t then shockL2 h k else 0 := by
  apply Lp.ext
  have hE := (proj_ae t (shockL2 h k)).trans
    (S.E_congr (memLp_shock h k).coeFn_toLp t)
  by_cases hk : k ≤ t
  · simp only [hk, ↓reduceIte]
    refine hE.trans ?_
    rw [S.E_of_stronglyMeasurable (h.adapted k t hk) (h.integrable k)]
    exact (memLp_shock h k).coeFn_toLp.symm
  · simp only [hk, ↓reduceIte]
    refine (hE.trans (h.E_future (by omega))).trans ?_
    exact (Lp.coeFn_zero ℝ 2 S.μ).symm

/-- Cochrane (2023), p. 501: forecasting a future surplus, `E_t a(L)ε_{t+1+j} =
∑_m a_{m+j+1} ε_{t−m}` in `L²`. -/
theorem proj_maL2 (h : ShockMDS S ε σ2) {c : ℕ → ℝ} (hc : Summable fun k => c k ^ 2)
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
noncomputable def surplusL2 (h : ShockMDS S ε σ2) (a : ℕ → ℝ) (n : ℕ) : Lp ℝ 2 S.μ :=
  maL2 h a n

/-- Cochrane (2023), p. 501: `‖a(L)ε_τ‖² = σ² ∑ a_k²` (stationarity). -/
theorem norm_maL2_sq (h : ShockMDS S ε σ2) {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2)
    (τ : ℤ) : ‖maL2 h a τ‖ ^ 2 = σ2 * ∑' k, a k ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have := inner_maL2_maL2 h ha ha τ 0
  simp only [Nat.cast_zero, add_zero] at this
  rw [this]
  simp only [sq]

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602: the ex-post present value
`PV_t = ∑_{j ≥ 0} ρ^j s_{t+1+j}` as an `L²`-convergent series. -/
noncomputable def pvL2 (h : ShockMDS S ε σ2) (ρ : ℝ) (a : ℕ → ℝ) (t : ℕ) : Lp ℝ 2 S.μ :=
  ∑' j, ρ ^ j • surplusL2 h a (t + 1 + j)

/-- Cochrane (2023), p. 501: for `|ρ| < 1` the present-value series converges in `L²`. -/
theorem summable_pv (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    Summable fun j => ρ ^ j • surplusL2 h a (t + 1 + j) := by
  have hn : ∀ n : ℕ, ‖surplusL2 h a n‖ = Real.sqrt (σ2 * ∑' k, a k ^ 2) := fun n => by
    rw [← norm_maL2_sq h ha n, Real.sqrt_sq (norm_nonneg _)]
    rfl
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right (Real.sqrt (σ2 * ∑' k, a k ^ 2)))
    fun j => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_pow, hn]

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602 (**the value of debt, genuinely**): the
valuation equation `v_t = E_t PV_t` with Mathlib's conditional expectation of (a representative
of) the `L²` present value. -/
noncomputable def valueL2 (h : ShockMDS S ε σ2) (ρ : ℝ) (a : ℕ → ℝ) (t : ℕ) : Ω → ℝ :=
  S.E t (pvL2 h ρ a t)

/-- Cochrane (2023), p. 501: the value-of-debt coefficients of a square-summable moving average
are square-summable. -/
theorem bCoeff_sq_summable {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) :
    Summable fun m => bCoeff ρ a m ^ 2 :=
  bInf_sq_summable_of_sq hρ ((summable_nat_add_iff 1).mpr ha)

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602: `E_t PV_t = b(L)ε_t` in `L²`,
`b_m = ∑_j ρ^j a_{m+1+j}` (the conditional expectation of the present value is computed term by
term and the double series is identified through its inner products with the shocks). -/
theorem proj_pvL2 (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
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

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602 (**the value of debt, square-summable
surpluses**): `v_t = E_t PV_t = b(L)ε_t` a.e. -/
theorem valueL2_ae (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    valueL2 h ρ a t =ᵐ[S.μ] maL2 h (bCoeff ρ a) t := by
  have := (proj_ae t (pvL2 h ρ a t)).symm
  rw [proj_pvL2 h hρ ha t] at this
  exact this

/-! ### Theorem RG -/

/-- Cochrane (2023), p. 501 (tool): `E[X Y] = ⟨X, Y⟩` in `L²`. -/
theorem integral_mul_eq_inner (X Y : Lp ℝ 2 S.μ) :
    ∫ ω, X ω * Y ω ∂S.μ = inner ℝ X Y := by
  rw [L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun ω => (Real.inner_apply _ _).symm)

/-- Cochrane (2023), p. 501: an `L²` moving average of the shocks has mean zero. -/
theorem integral_maL2 (h : ShockMDS S ε σ2) {c : ℕ → ℝ} (hc : Summable fun k => c k ^ 2)
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
  rw [shockL2, integral_congr_ae (memLp_shock h _).coeFn_toLp, h.integral_eq_zero, mul_zero]

/-- Cochrane (2023), p. 501: the value of debt has mean zero. -/
theorem integral_valueL2 (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) : ∫ ω, valueL2 h ρ a t ω ∂S.μ = 0 := by
  rw [integral_congr_ae (valueL2_ae h hρ ha t)]
  exact integral_maL2 h (bCoeff_sq_summable hρ ha) t

/-- Cochrane (2023), p. 501 (**covariance of surpluses with lagged debt, square-summable
moving averages**): `Cov(s_{t+1}, v_t) = σ² ∑_m a_{m+1} b_m` (Mathlib `covariance`). -/
theorem cov_surplus_valueL2 (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
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

/-- Cochrane (2023), p. 501: `Var(v_t) = σ² ∑_m b_m²` (square-summable moving averages). -/
theorem var_valueL2 (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
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

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (**Theorem RG for
square-summable moving averages**): `2 Cov(s_{t+1}, v_t) = σ² (∑_{k≥1} a_k² +
∑_{k,l≥1} ρ^{|k−l|} a_k a_l)`, every sum absolutely convergent. -/
theorem two_covL2_eq_kms (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    2 * cov[surplusL2 h a (t + 1), valueL2 h ρ a t; S.μ] =
      σ2 * (∑' k, a (k + 1) ^ 2 + kmsInf ρ (fun k => a (k + 1))) := by
  rw [cov_surplus_valueL2 h hρ ha t,
    ← two_covInf_eq_of_sq hρ ((summable_nat_add_iff 1).mpr ha)]
  ring

/-- Cochrane (2023), p. 501, §24.1 p. 519 (Theorem RG, sign, square-summable): with `σ² > 0`
the covariance of surpluses with lagged debt is positive iff the surplus is not white noise. -/
theorem covL2_pos_iff (h : ShockMDS S ε σ2) (hσ : 0 < σ2) {ρ : ℝ} (hρ : |ρ| < 1)
    {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    0 < cov[surplusL2 h a (t + 1), valueL2 h ρ a t; S.μ] ↔ ¬ IsIID a := by
  rw [cov_surplus_valueL2 h hρ ha t, mul_pos_iff_of_pos_left hσ]
  exact covInf_pos_iff_of_sq hρ ha

/-- Cochrane (2023), p. 501: the regression coefficient of `s_{t+1}` on `v_t` is
`∑_m a_{m+1} b_m / ∑_m b_m²` (square-summable moving averages). -/
theorem regL2_eq (h : ShockMDS S ε σ2) (hσ : σ2 ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    regM S.μ (surplusL2 h a (t + 1)) (valueL2 h ρ a t) =
      covInf ρ (fun k => a (k + 1)) / ∑' m, bCoeff ρ a m ^ 2 := by
  rw [regM, cov_surplus_valueL2 h hρ ha t, var_valueL2 h hρ ha t, mul_div_mul_left _ _ hσ]

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (**Theorem RG, regression
form, square-summable moving averages**): the regression coefficient of surpluses on lagged debt
is strictly positive iff the surplus is not white noise. -/
theorem regL2_pos_iff (h : ShockMDS S ε σ2) (hσ : 0 < σ2) {ρ : ℝ} (hρ : |ρ| < 1)
    {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) (t : ℕ) :
    0 < regM S.μ (surplusL2 h a (t + 1)) (valueL2 h ρ a t) ↔ ¬ IsIID a := by
  rw [regL2_eq h hσ.ne' hρ ha t]
  exact regInf_pos_iff_of_sq hρ ha

/-! ### Link with the absolutely summable case -/

/-- Cochrane (2023), p. 501 (**link**): for absolutely summable coefficients the `L²` moving
average is the pointwise moving average `maInf` of `SurplusRegressionMeasure` (a.e.). -/
theorem maL2_ae_maInf (h : ShockMDS S ε σ2) {a : ℕ → ℝ} (ha : Summable fun k => |a k|)
    (τ : ℤ) : maL2 h a τ =ᵐ[S.μ] maInf a ε τ := by
  have ha2 : Summable fun k => a k ^ 2 := sq_summable ha
  obtain ⟨M, -, hbd⟩ := h.ae_bdd
  have hm : MemLp (maInf a ε τ) 2 S.μ :=
    MemLp.of_bound (aesm_maInf ha h.aesm hbd τ) ((∑' k, |a k|) * M)
      (hbd.mono fun ω hω => by rw [Real.norm_eq_abs]; exact (abs_maInf_le ha hω τ).2)
  set P := hm.toLp (maInf a ε τ)
  have hPP : inner ℝ P P = σ2 * ∑' k, a k ^ 2 := by
    rw [← integral_mul_eq_inner]
    have := integral_maInf_mul_maInf h ha ha τ 0
    simp only [Nat.cast_zero, add_zero] at this
    rw [← tsum_congr fun k => (sq (a k)).symm, ← this]
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with ω hω
    rw [hω]
  have hPe : ∀ m : ℕ, inner ℝ P (shockL2 h (τ - m)) = σ2 * a m := by
    intro m
    rw [← integral_mul_eq_inner]
    have := integral_maInf_shock h ha τ 0 m
    simp only [Nat.cast_zero, add_zero] at this
    rw [← this]
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp, (memLp_shock h (τ - m)).coeFn_toLp] with ω h1 h2
    simp only [shockL2] at h2 ⊢
    rw [h1, h2]
  have hPL : inner ℝ P (maL2 h a τ) = σ2 * ∑' k, a k ^ 2 := by
    rw [maL2, inner_tsum_right _ (summable_ma h ha2 τ)]
    simp only [real_inner_smul_right, hPe]
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by ring
  have hLL : inner ℝ (maL2 h a τ) (maL2 h a τ) = σ2 * ∑' k, a k ^ 2 := by
    have := inner_maL2_maL2 h ha2 ha2 τ 0
    simp only [Nat.cast_zero, add_zero] at this
    rw [this]
    exact congrArg _ (tsum_congr fun k => (sq (a k)).symm)
  have hD : inner ℝ (maL2 h a τ - P) (maL2 h a τ - P) = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hLL, hPP, hPL, real_inner_comm, hPL]
    ring
  have hEq : maL2 h a τ = P := sub_eq_zero.mp (inner_self_eq_zero.mp hD)
  rw [hEq]
  exact hm.coeFn_toLp

/-- Cochrane (2023), p. 501 (**link**): for absolutely summable coefficients the `L²` value of
debt agrees a.e. with the value of debt of `SurplusRegressionMeasure` (both are `b(L)ε_t`). -/
theorem valueL2_ae_valueM (h : ShockMDS S ε σ2) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (t : ℕ) :
    valueL2 h ρ a t =ᵐ[S.μ] valueM S ρ (surplusInf a ε) t :=
  ((valueL2_ae h hρ (sq_summable ha) t).trans
    (maL2_ae_maInf h (bCoeff_abs_summable hρ ha) t)).trans (valueM_eq h hρ ha t).symm

/-! ### A square-summable, not absolutely summable surplus in the coin economy -/

/-- Cochrane (2023), p. 501: the surplus coefficients `a_0 = 0`, `a_k = 1/k` (`k ≥ 1`). -/
noncomputable def harmonicCoeff (k : ℕ) : ℝ := if k = 0 then 0 else 1 / k

/-- Cochrane (2023), p. 501, §24.1 p. 519 (Theorem RG beyond absolute summability): in the i.i.d.
coin economy the surplus `s_t = ∑_{k ≥ 1} ε_{t−k}/k` — square-summable but not absolutely
summable — has a strictly positive regression coefficient of surpluses on debt. -/
theorem coinZ_harmonic_regL2_pos {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    ¬ Summable (fun k => |harmonicCoeff k|) ∧
    0 < regM (iidZSystem ExpectationsMeasureIID.coin).μ
      (surplusL2 coinZ_shockMDS harmonicCoeff (t + 1))
      (valueL2 coinZ_shockMDS ρ harmonicCoeff t) := by
  obtain ⟨h2, h1⟩ := harmonic_sq_not_abs
  refine ⟨h1, (regL2_pos_iff coinZ_shockMDS one_pos hρ h2 t).2 fun hiid => ?_⟩
  have := hiid 1 le_rfl
  simp at this

end Cochrane.ObservationalEquivalence.SurplusRegressionL2
