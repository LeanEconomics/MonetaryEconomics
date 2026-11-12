/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.Invertibility
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Invertibility, Wold and Granger causality in the Hilbert space of second moments

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, p. 102, and Online
Appendix Chapter 2, §§2.1.4–2.1.6, eqs. (2.4)–(2.5) and (2.17)–(2.21), pp. 597–601.

This module extends the Hilbert-space layer of `Invertibility` (white noise `e` in a real Hilbert
space `H`, moving averages `maProc a e`, closed past spans `pastSpan`). It is stated for an
arbitrary `H`; `InvertibilityMeasureL2` instantiates it on `L²(Ω, P)` of a genuine i.i.d.
probability space.

## Main definitions

* `eSpan e`: the closed span of all the shocks; `cconv b c`: the Cauchy product of coefficient
  sequences (the coefficients of `b(L)c(L)`).
* `factorCoeff θ g`: the coefficients of `(1 − θL)g(L)` (the book's factorisation (2.17));
  `jointSpan s v t`: the closed span of current and past `s` AND `v` (the debt–surplus VAR's
  information); the one-step-ahead forecast error `u_t = s_t − P(s_t|s_{t−1}, …)`
  (in `wold_factor`).

## Main results

* Tools: `inner_e_maProc_int`, `eq_of_inner_e`, `hasSum_filter_maProc`
  (`b(L)[c(L)e_t] = (b·c)(L)e_t` in `H`), `gen_factorCoeff` (`a(z) = (1 − θz)g(z)`).
* Non-invertibility at `|ρ| ≤ 1`, including `ρ = 1` (p. 102, A2 p. 600):
  `not_filter_of_aRho_eq_zero`
  — no absolutely summable filter of current and past surpluses converges in `H` to the shock.
* Correction at `|ρ| = 1`: `mem_pastSpan_unit_root` — for `s_t = e_t − ρe_{t−1}`, `ρ = ±1`
  (`a(ρ) = 0`), the shock IS in the closed span of current and past surpluses (Cesàro means of
  the filter partial sums converge to it, error variance `σ²/(n+1)`); so the closed-span
  statement `Invertibility.Hilbert.not_mem_pastSpan_of_aRho_eq_zero` genuinely needs `|ρ| < 1`.
* Wold (A2 pp. 597, 600, the factorised claim (2.17)): `wold_factor` — for
  `a(L) = (1 − θL)g(L)`, `|θ| > 1`, `g₀ = 1` and `g` invertible (absolutely summable inverse),
  the autoregression's innovation is `w_t = ∑θ⁻ᵏm_{t−k}` (`m_t = e_t − θe_{t−1}`), with
  variance `θ²σ²`, `s_t = ∑ã_n w_{t−n}` for `ã(L) = (1 − θ⁻¹L)g(L)` (root flipped), fitted
  `ã(θ⁻¹) = (1 − θ⁻²)g(θ⁻¹) ≠ 0` while `a(θ⁻¹) = 0`, and `w_t ≠ e_t`.
* Debt (2.18)–(2.20): `summable_abs_hsCoeff` (for `|ρ| < 1` debt is a moving average),
  `debt_hasSum_expost` (with `a(ρ) = 0` debt is the ex-post present value, in `H`),
  `hsCoeff_factor` (`c = −θg`, "the non-invertible root cancels"), `shock_mem_debtSpan` (with `g`
  invertible the shock is recovered from the debt history), `debt_not_invertible_example`
  (correction: when another root of `a(L)` is inside the disc the debt is NOT invertible).
* Links: `factorCoeff_delta`, `recoverable_delta`, `wold_factor_ma1` (`g = 1` gives the MA(1)
  statements `Invertibility.Hilbert.ma1_wold`, `Invertibility.ma1_fitted_aRho`, and `v = −θe`).
* Granger causality ((2.21), p. 601): `exists_shift` (white noise has a unitary time shift),
  `granger_general` — for an ARBITRARY absolutely summable MA with `a₀ ≠ 0`, `a(ρ) = 0`,
  `|ρ| < 1`, the projection of `s_{t+1}` on the joint surplus–debt past differs from that on the
  surplus past, and the forecast-error norm is strictly smaller with debt; `granger_factor` —
  in the factorised case the two error variances are exactly `σ²` and `θ²σ² = σ²/ρ²`.
-/

namespace Cochrane.DebtDeficitsInflation.InvertibilityMeasure

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations (gen)
open Cochrane.DebtDeficitsInflation.Invertibility
open Cochrane.DebtDeficitsInflation.Invertibility.Hilbert
open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Tools: the closed span of the shocks and filters of moving averages -/

/-- Cochrane (2023), p. 102 (tool): the closed linear span of all the structural shocks. -/
noncomputable def eSpan (e : ℤ → H) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range e)).topologicalClosure

/-- Cochrane (2023), p. 102 (tool): a shock from the future is uncorrelated with the moving
average, `⟪e_{t+1+n}, s_t⟫ = 0`. -/
theorem inner_e_maProc_future [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) (n : ℕ) :
    ⟪e (t + 1 + n), maProc a e t⟫ = 0 := by
  have h := inner_hasSum_right (maProc_hasSum he ha t) (e (t + 1 + n))
  refine h.unique ?_
  convert hasSum_zero with k
  rw [real_inner_smul_right, he]
  have : t + 1 + (n : ℤ) ≠ t - k := by omega
  simp [this]

/-- Cochrane (2023), p. 102 (tool): the covariance of any shock with the moving average,
`⟪e_u, s_t⟫ = σ² a_{t−u}` for `u ≤ t` and `0` for `u > t`. -/
theorem inner_e_maProc_int [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t u : ℤ) :
    ⟪e u, maProc a e t⟫ = if u ≤ t then σ2 * a (t - u).toNat else 0 := by
  by_cases hu : u ≤ t
  · simp only [hu, ↓reduceIte]
    have e1 : u = t - ((t - u).toNat : ℕ) := by omega
    conv_lhs => rw [e1]
    exact inner_e_maProc he ha t _
  · simp only [hu, ↓reduceIte]
    have e1 : u = t + 1 + ((u - t - 1).toNat : ℕ) := by omega
    rw [e1]
    exact inner_e_maProc_future he ha t _

/-- Cochrane (2023), p. 102 (tool): a convergent series of members of the shock span lies in it. -/
theorem hasSum_mem_eSpan {e : ℤ → H} {f : ℕ → H} {x : H} (h : HasSum f x)
    (hf : ∀ k, f k ∈ eSpan e) : x ∈ eSpan e :=
  (Submodule.isClosed_topologicalClosure _).mem_of_tendsto h.tendsto_sum_nat
    (Filter.Eventually.of_forall fun _ => Submodule.sum_mem _ fun k _ => hf k)

/-- Cochrane (2023), p. 102 (tool): each shock lies in the shock span. -/
theorem e_mem_eSpan (e : ℤ → H) (u : ℤ) : e u ∈ eSpan e :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨u, rfl⟩)

/-- Cochrane (2023), p. 102 (tool): a moving average lies in the shock span. -/
theorem maProc_mem_eSpan [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) : maProc a e t ∈ eSpan e :=
  hasSum_mem_eSpan (maProc_hasSum he ha t) fun _ => Submodule.smul_mem _ _ (e_mem_eSpan e _)

/-- Cochrane (2023), p. 102 (tool): two members of the shock span with the same covariances with
every shock are equal. -/
theorem eq_of_inner_e {e : ℤ → H} {x y : H} (hx : x ∈ eSpan e) (hy : y ∈ eSpan e)
    (h : ∀ u, ⟪e u, x⟫ = ⟪e u, y⟫) : x = y := by
  have hd : x - y ∈ eSpan e := Submodule.sub_mem _ hx hy
  have hle : eSpan e ≤ (ℝ ∙ (x - y))ᗮ := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
      (Submodule.isClosed_orthogonal _)
    rintro _ ⟨u, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_left,
      real_inner_comm, h u, real_inner_comm, sub_self]
  have h0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hd)
  rwa [inner_self_eq_zero, sub_eq_zero] at h0

/-- Cochrane (2023), p. 87 (tool): `‖s_t‖ ≤ (∑|a_k|)‖e_0‖`. -/
theorem norm_maProc_le [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) :
    ‖maProc a e t‖ ≤ (∑' k, |a k|) * ‖e 0‖ := by
  have hs : Summable fun k : ℕ => ‖a k • e (t - k)‖ :=
    (ha.mul_right ‖e 0‖).congr fun k => by rw [norm_smul, Real.norm_eq_abs, he.norm_eq (t - k)]
  calc ‖maProc a e t‖ ≤ ∑' k : ℕ, ‖a k • e (t - k)‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' k, |a k| * ‖e 0‖ := tsum_congr fun k => by
        rw [norm_smul, Real.norm_eq_abs, he.norm_eq (t - k)]
    _ = (∑' k, |a k|) * ‖e 0‖ := tsum_mul_right

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600 (tool): the coefficients of the product
`b(L)c(L)`, `(b·c)_n = ∑_{k ≤ n} b_k c_{n−k}`. -/
noncomputable def cconv (b c : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), b k * c (n - k)

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600 (tool): the product of absolutely summable
lag polynomials is absolutely summable. -/
theorem summable_cconv {b c : ℕ → ℝ} (hb : Summable (fun k => |b k|))
    (hc : Summable (fun k => |c k|)) : Summable (fun n => |cconv b c n|) := by
  have := summable_norm_sum_mul_range_of_summable_norm (f := b) (g := c)
    (by simpa [Real.norm_eq_abs] using hb) (by simpa [Real.norm_eq_abs] using hc)
  simpa [Real.norm_eq_abs, cconv] using this

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600 (tool): the product of lag polynomials is
the product of power series. -/
theorem mk_cconv (b c : ℕ → ℝ) :
    PowerSeries.mk (cconv b c) = PowerSeries.mk b * PowerSeries.mk c := by
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, cconv,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp

/-- Cochrane (2023), Online Appendix pp. 597–601 (tool): **filters of moving averages** — for
absolutely summable `b`, `c`, `∑_k b_k s_{t−k} = (b·c)(L)e_t` in `H`, where `s = c(L)e`. -/
theorem hasSum_filter_maProc [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {b c : ℕ → ℝ} (hb : Summable (fun k => |b k|)) (hc : Summable (fun k => |c k|)) (t : ℤ) :
    HasSum (fun k : ℕ => b k • maProc c e (t - k)) (maProc (cconv b c) e t) := by
  have hsum : Summable (fun k : ℕ => b k • maProc c e (t - k)) := by
    refine Summable.of_norm_bounded (hb.mul_right ((∑' k, |c k|) * ‖e 0‖)) fun k => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_maProc_le he hc _) (abs_nonneg _)
  have hX := hsum.hasSum
  convert hX using 1
  refine eq_of_inner_e (maProc_mem_eSpan he (summable_cconv hb hc) t)
    (hasSum_mem_eSpan hX fun k => Submodule.smul_mem _ _ (maProc_mem_eSpan he hc _))
    fun u => ?_
  have h := inner_hasSum_right hX (e u)
  refine (h.unique ?_).symm
  rw [inner_e_maProc_int he (summable_cconv hb hc)]
  by_cases hu : u ≤ t
  · simp only [hu, ↓reduceIte]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, u = t - n := ⟨(t - u).toNat, by omega⟩
    subst hn
    have hn' : (t - (t - (n : ℤ))).toNat = n := by omega
    rw [hn']
    have hF : ∀ k, ⟪e (t - n), b k • maProc c e (t - k)⟫ =
        if k ∈ Finset.range (n + 1) then σ2 * (b k * c (n - k)) else 0 := by
      intro k
      rw [real_inner_smul_right, inner_e_maProc_int he hc]
      by_cases hk : k ∈ Finset.range (n + 1)
      · have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have h1 : t - (n : ℤ) ≤ t - k := by omega
        have h2 : (t - (k : ℤ) - (t - n)).toNat = n - k := by omega
        simp only [h1, hk, ↓reduceIte]
        rw [h2]
        ring
      · have : ¬ t - (n : ℤ) ≤ t - k := by
          rw [Finset.mem_range] at hk; omega
        simp only [this, hk, ↓reduceIte, mul_zero]
    have hS : HasSum (fun k => if k ∈ Finset.range (n + 1) then σ2 * (b k * c (n - k)) else 0)
        (∑ k ∈ Finset.range (n + 1),
          if k ∈ Finset.range (n + 1) then σ2 * (b k * c (n - k)) else 0) :=
      hasSum_sum_of_ne_finset_zero fun k hk => by simp only [hk, ↓reduceIte]
    rw [Finset.sum_ite_of_true (fun _ hk => hk), ← Finset.mul_sum] at hS
    exact hS.congr_fun hF
  · simp only [hu, ↓reduceIte]
    convert hasSum_zero with k
    rw [real_inner_smul_right, inner_e_maProc_int he hc]
    have : ¬ u ≤ t - k := by omega
    simp only [this, ↓reduceIte, mul_zero]

/-! ### Non-invertibility at `|ρ| ≤ 1`, and what fails at `|ρ| = 1` -/

/-- Cochrane (2023), p. 102 ("the shock `ε_t` is a function of current and future surpluses, not
current and past surpluses") and Online Appendix p. 600, in the Hilbert space, for every
`|ρ| ≤ 1` including the book's `ρ = 1`: if `a(ρ) = 0`, no absolutely summable filter of current and
past surpluses converges (in mean square) to the structural shock `e_t`. -/
theorem not_filter_of_aRho_eq_zero [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ}
    (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) {ρ : ℝ}
    (hρ : |ρ| ≤ 1) (h0 : gen a ρ = 0) (t : ℤ) :
    ¬ ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
      HasSum (fun k : ℕ => b k • maProc a e (t - k)) (e t) := by
  rintro ⟨b, hb, hsum⟩
  refine not_recoverable_of_aRho_eq_zero ha hρ h0 ⟨b, hb, fun n => ?_⟩
  have h1 := (hasSum_filter_maProc he hb ha t).unique hsum
  have h2 : ⟪e (t - n), maProc (cconv b a) e t⟫ = ⟪e (t - n), e t⟫ := by rw [h1]
  rw [inner_e_maProc he (summable_cconv hb ha) t n, he] at h2
  change cconv b a n = _
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.cast_zero, sub_zero, ↓reduceIte] at h2 ⊢
    exact mul_left_cancel₀ hσ (h2.trans (mul_one σ2).symm)
  · have hne : t - (n : ℤ) ≠ t := by omega
    simp only [hne, hn, ↓reduceIte] at h2 ⊢
    exact (mul_eq_zero.mp h2).resolve_left hσ

/-- Cochrane (2023), p. 102 (tool): the MA(1) coefficients give `s_t = e_t − θe_{t−1}`. -/
theorem maProc_armaCoeff_zero [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (θ : ℝ) (t : ℤ) : maProc (armaCoeff 0 θ) e t = maOne θ e t := by
  have ha := summable_abs_armaCoeff (show |(0 : ℝ)| < 1 by simp) θ
  have := ar2_filter_eq_maOne he ha (φ1 := 0) (φ2 := 0) (θ := θ) rfl (by simp [armaCoeff])
    (fun k => by simp [armaCoeff]) t
  simpa using this

/-- Cochrane (2023), p. 102 (tool): the squared norm of a finite combination of distinct shocks,
`‖∑ c_m e_{f(m)}‖² = σ² ∑ c_m²`. -/
theorem inner_sum_e {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (c : ℕ → ℝ) (f : ℕ → ℤ)
    (hf : Function.Injective f) (N : ℕ) :
    ⟪∑ m ∈ Finset.range N, c m • e (f m), ∑ m ∈ Finset.range N, c m • e (f m)⟫ =
      σ2 * ∑ m ∈ Finset.range N, c m ^ 2 := by
  rw [sum_inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [inner_sum]
  have : ∀ m' ∈ Finset.range N, ⟪c m • e (f m), c m' • e (f m')⟫ =
      if m = m' then c m * c m' * σ2 else 0 := by
    intro m' _
    rw [real_inner_smul_left, real_inner_smul_right, he]
    simp only [hf.eq_iff]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  simp only [hm, ↓reduceIte]
  ring

/-- Cochrane (2023), p. 102, and Online Appendix p. 597 ("`ρ ≤ 1`"), **correction at `|ρ| = 1`**:
for the MA(1) `s_t = e_t − ρe_{t−1}` with `ρ = ±1` we have `a(ρ) = 1 − ρ² = 0`, yet the structural
shock `e_t` IS in the closed linear span of current and past surpluses: the Cesàro means of the
filter partial sums `∑_{k≤m} ρᵏs_{t−k} = e_t − ρ^{m+1}e_{t−m−1}` converge to it, with error
variance `σ²/(n+1)`. So in mean square the shock can be recovered from the surplus history at
`|ρ| = 1` (though by no absolutely summable filter, `not_filter_of_aRho_eq_zero`), and
`Invertibility.Hilbert.not_mem_pastSpan_of_aRho_eq_zero` cannot be extended to `|ρ| = 1`. -/
theorem mem_pastSpan_unit_root [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {ρ : ℝ} (hρ : ρ ^ 2 = 1) (t : ℤ) :
    gen (armaCoeff 0 ρ) ρ = 0 ∧ e t ∈ pastSpan (maProc (armaCoeff 0 ρ) e) t := by
  refine ⟨by rw [ma1_aRho]; nlinarith, ?_⟩
  set s := maProc (armaCoeff 0 ρ) e with hs
  have hsm : ∀ τ, s τ = e τ - ρ • e (τ - 1) := fun τ => maProc_armaCoeff_zero he ρ τ
  -- partial sums of the filter
  have hP : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), ρ ^ k • s (t - k) =
      e t - ρ ^ (m + 1) • e (t - 1 - m) := by
    intro m
    induction m with
    | zero => simp [hsm]
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, hsm, smul_sub, smul_smul, ← pow_succ,
        show t - ((m + 1 : ℕ) : ℤ) = t - 1 - m by push_cast; ring,
        show t - 1 - (m : ℤ) - 1 = t - 1 - ((m + 1 : ℕ) : ℤ) by push_cast; ring]
      abel
  set y : ℕ → H := fun n => ((n : ℝ) + 1)⁻¹ •
    ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (m + 1), ρ ^ k • s (t - k) with hy
  have hymem : ∀ n, y n ∈ pastSpan s t := fun n =>
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m _ => Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (mem_pastSpan_self s t k))
  have hdiff : ∀ n, e t - y n = ((n : ℝ) + 1)⁻¹ •
      ∑ m ∈ Finset.range (n + 1), ρ ^ (m + 1) • e (t - 1 - m) := by
    intro n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [hy, hP, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    rw [smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_add, Nat.cast_one,
      inv_mul_cancel₀ hn, one_smul]
    abel
  have hnorm : ∀ n, ‖e t - y n‖ ^ 2 = σ2 / ((n : ℝ) + 1) := by
    intro n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [hdiff, ← real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_smul_right,
      inner_sum_e he (fun m => ρ ^ (m + 1)) (fun m => t - 1 - m)
        (fun m m' h => by simpa using h) (n + 1)]
    have : ∀ m ∈ Finset.range (n + 1), (ρ ^ (m + 1)) ^ 2 = 1 := fun m _ => by
      rw [← pow_mul, mul_comm, pow_mul, hρ, one_pow]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp
  have hlim : Tendsto y atTop (𝓝 (e t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun n : ℕ => σ2 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat σ2 |>.comp (tendsto_add_atTop_nat 1) |>.congr
        fun n => by simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [← hnorm, norm_sub_rev, Real.sqrt_sq (norm_nonneg _)]
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
    (Eventually.of_forall hymem)

/-! ### The general (factorised) Wold statement -/

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600: the coefficients of `(1 − θL)g(L)`,
`a₀ = g₀`, `a_{k+1} = g_{k+1} − θg_k`. -/
def factorCoeff (θ : ℝ) (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => g 0
  | k + 1 => g (k + 1) - θ * g k

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600 (tool): `(1 − θL)g(L)` is the product of
the lag polynomials `g(L)` and `1 − θL` (as power series). -/
theorem mk_factorCoeff (θ : ℝ) (g : ℕ → ℝ) :
    PowerSeries.mk (factorCoeff θ g) = PowerSeries.mk g * PowerSeries.mk (armaCoeff 0 θ) := by
  rw [← mk_cconv]
  congr 1
  funext n
  rcases n with _ | m
  · simp [factorCoeff, cconv, armaCoeff]
  · rw [cconv, Finset.sum_range_succ, Finset.sum_range_succ, Nat.sub_self,
      show m + 1 - m = 0 + 1 by omega, factorCoeff]
    have h0 : ∑ k ∈ Finset.range m, g k * armaCoeff 0 θ (m + 1 - k) = 0 :=
      Finset.sum_eq_zero fun k hk => by
        have hk' : m + 1 - k = (m - k) + 1 := by rw [Finset.mem_range] at hk; omega
        have hk'' : m - k ≠ 0 := by rw [Finset.mem_range] at hk; omega
        rw [hk', armaCoeff, zero_pow hk'', mul_zero, mul_zero]
    rw [h0]
    simp [armaCoeff]
    ring

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600 (tool): `(1 − θL)g(L)` has absolutely
summable coefficients when `g` does. -/
theorem summable_factorCoeff (θ : ℝ) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|)) :
    Summable (fun k => |factorCoeff θ g k|) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_)
    (((summable_nat_add_iff 1).mpr hg).add (hg.mul_left |θ|))
  change |g (k + 1) - θ * g k| ≤ |g (k + 1)| + |θ| * |g k|
  calc |g (k + 1) - θ * g k| ≤ |g (k + 1)| + |θ * g k| := abs_sub _ _
    _ = |g (k + 1)| + |θ| * |g k| := by rw [abs_mul]

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600: `a(z) = (1 − θz)g(z)` for `|z| ≤ 1`. -/
theorem gen_factorCoeff (θ : ℝ) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|)) {z : ℝ}
    (hz : |z| ≤ 1) : gen (factorCoeff θ g) z = (1 - θ * z) * gen g z := by
  have hgz : Summable (fun j => g j * z ^ j) :=
    Summable.of_norm_bounded hg fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hz)
  have h1 : HasSum (fun j => g (j + 1) * z ^ (j + 1)) (gen g z - g 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hgz.hasSum
    simpa [gen] using this
  have h2 : HasSum (fun j => factorCoeff θ g (j + 1) * z ^ (j + 1))
      (gen g z - g 0 - θ * z * gen g z) := by
    refine (h1.sub (hgz.hasSum.mul_left (θ * z))).congr_fun fun j => ?_
    simp only [factorCoeff, pow_succ]
    ring
  have h3 : HasSum (fun j => factorCoeff θ g j * z ^ j)
      (factorCoeff θ g 0 + (gen g z - g 0 - θ * z * gen g z)) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa using h2
  rw [gen, h3.tsum_eq, factorCoeff]
  ring

/-- Cochrane (2023), p. 600 (tool): an absolutely summable inverse of `g(L)` turns into the power
series identity `h(L)g(L) = 1`. -/
theorem mk_mul_eq_one {h g : ℕ → ℝ}
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), h k * g (n - k) = if n = 0 then 1 else 0) :
    PowerSeries.mk h * PowerSeries.mk g = 1 := by
  rw [← mk_cconv]
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_one, cconv, hconv]

/-- Cochrane (2023), Online Appendix p. 597 (tool): `∑ θ⁻ᵏ Lᵏ (1 − θ⁻¹L) = 1`. -/
theorem mk_geom_factor (θ : ℝ) :
    PowerSeries.mk (fun k => (θ⁻¹) ^ k) * PowerSeries.mk (armaCoeff 0 θ⁻¹) = 1 := by
  rw [← mk_factorCoeff]
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases n with _ | m
  · simp [factorCoeff]
  · simp only [factorCoeff, pow_succ, Nat.add_one_ne_zero, ↓reduceIte]
    ring

/-- Cochrane (2023), Online Appendix p. 597 (tool): the coefficients of a power series determine
the sequence. -/
theorem eq_of_mk_eq {b c : ℕ → ℝ} (h : PowerSeries.mk b = PowerSeries.mk c) : b = c := by
  funext n
  have := congrArg (PowerSeries.coeff n) h
  simpa using this

/-- Cochrane (2023), Online Appendix pp. 597 and 600 (`(1 − ρ⁻¹L)` "blows up going backwards"; "if
you do run an autoregression you recover a representation that is invertible, by the Wold
decomposition theorem"), **the factorised claim made precise**: let `s_t = a(L)e_t` with
`a(L) = (1 − θL)g(L)` (the book's (2.17) with `θ = ρ⁻¹`), `|θ| > 1`, `g₀ = 1`, and `g`
absolutely summable with an absolutely summable inverse (all other roots outside the unit
circle, the book's "appropriately less than one"). Then, with `m_t = e_t − θe_{t−1}` and
`w_t = ∑θ⁻ᵏm_{t−k}`:
* `s_t − w_t` is the projection of `s_t` on its own past (`w` is the autoregression's error);
* `w` is white noise with variance `θ²σ²`;
* `s_t = ∑ ã_n w_{t−n}` with `ã(L) = (1 − θ⁻¹L)g(L)`: the root `θ` is flipped to `θ⁻¹ = ρ`;
* `a(θ⁻¹) = 0` but the fitted `ã(θ⁻¹) = (1 − θ⁻²)g(θ⁻¹) ≠ 0` ("the resulting estimate of
  `a(L)` does not have `a(ρ) = 0` even in infinite data");
* the structural shock is not in the closed span of the surplus history, and `w_t ≠ e_t`. -/
theorem wold_factor [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (hσ : σ2 ≠ 0) {θ : ℝ} (hθ : 1 < |θ|) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|))
    (hg0 : g 0 = 1) (hrec : Recoverable g) (t : ℤ) :
    (haveI : (pastSpan (maProc (factorCoeff θ g) e) (t - 1)).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      (pastSpan (maProc (factorCoeff θ g) e) (t - 1)).starProjection
        (maProc (factorCoeff θ g) e t)) =
      maProc (factorCoeff θ g) e t - woldInnov θ (maOne θ e) t ∧
    ⟪woldInnov θ (maOne θ e) t, woldInnov θ (maOne θ e) t⟫ = θ ^ 2 * σ2 ∧
    (∀ u, u < t → ⟪woldInnov θ (maOne θ e) t, woldInnov θ (maOne θ e) u⟫ = 0) ∧
    HasSum (fun n : ℕ => factorCoeff θ⁻¹ g n • woldInnov θ (maOne θ e) (t - n))
      (maProc (factorCoeff θ g) e t) ∧
    gen (factorCoeff θ g) θ⁻¹ = 0 ∧
    gen (factorCoeff θ⁻¹ g) θ⁻¹ = (1 - θ⁻¹ ^ 2) * gen g θ⁻¹ ∧
    gen (factorCoeff θ⁻¹ g) θ⁻¹ ≠ 0 ∧
    e t ∉ pastSpan (maProc (factorCoeff θ g) e) t ∧
    woldInnov θ (maOne θ e) t ≠ e t := by
  obtain ⟨h, hh, hconv⟩ := hrec
  have hθ0 : θ ≠ 0 := by intro h0; rw [h0, abs_zero] at hθ; linarith
  have hq : |θ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hθ
  set a := factorCoeff θ g with ha_def
  have ha := summable_factorCoeff θ hg
  have hd := summable_abs_armaCoeff (show |(0 : ℝ)| < 1 by simp) θ
  set s := maProc a e with hs
  have hroot : gen a θ⁻¹ = 0 := by
    rw [gen_factorCoeff θ hg hq.le, mul_inv_cancel₀ hθ0, sub_self, zero_mul]
  have ha0 : a 0 = 1 := hg0
  have hh0 : h 0 = 1 := by
    have := hconv 0
    simpa [hg0] using this
  -- `h(L)s_t = m_t`
  have hha : cconv h a = armaCoeff 0 θ := by
    refine eq_of_mk_eq ?_
    rw [mk_cconv, ha_def, mk_factorCoeff, ← mul_assoc, mk_mul_eq_one hconv, one_mul]
  have hm : ∀ τ, maOne θ e τ - s τ ∈ pastSpan s (τ - 1) := by
    intro τ
    have hf := hasSum_filter_maProc he hh ha τ
    rw [hha, maProc_armaCoeff_zero he] at hf
    rw [← hasSum_nat_add_iff' 1] at hf
    simp only [Finset.range_one, Finset.sum_singleton, hh0, one_smul, Nat.cast_zero,
      sub_zero] at hf
    refine hasSum_mem_pastSpan hf fun k => Submodule.smul_mem _ _ ?_
    rw [show τ - ((k + 1 : ℕ) : ℤ) = τ - 1 - k by push_cast; ring]
    exact mem_pastSpan_self s (τ - 1) k
  obtain ⟨-, hsub, hproj, hnorm, hwhite, -, hnot⟩ :=
    wold_innovation he hσ hθ ha ha0 hroot hm t
  -- `w = (θ⁻ᵏ)(L)(1 − θL)e`
  have hgeo : Summable (fun k => |(θ⁻¹) ^ k|) := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg _) hq
  have hw : ∀ τ, woldInnov θ (maOne θ e) τ =
      maProc (cconv (fun k => (θ⁻¹) ^ k) (armaCoeff 0 θ)) e τ := by
    intro τ
    refine (woldInnov_hasSum he hθ τ).unique ?_
    have := hasSum_filter_maProc he hgeo hd τ
    refine this.congr_fun fun k => ?_
    rw [maProc_armaCoeff_zero he]
  -- the fitted representation
  have hfit : HasSum (fun n : ℕ => factorCoeff θ⁻¹ g n • woldInnov θ (maOne θ e) (t - n))
      (s t) := by
    have hft := hasSum_filter_maProc he (summable_factorCoeff θ⁻¹ hg)
      (summable_cconv hgeo hd) t
    have hcoef : cconv (factorCoeff θ⁻¹ g) (cconv (fun k => (θ⁻¹) ^ k) (armaCoeff 0 θ)) = a := by
      refine eq_of_mk_eq ?_
      rw [mk_cconv, mk_cconv, mk_factorCoeff, ha_def, mk_factorCoeff,
        show PowerSeries.mk g * PowerSeries.mk (armaCoeff 0 θ⁻¹) *
          (PowerSeries.mk (fun k => (θ⁻¹) ^ k) * PowerSeries.mk (armaCoeff 0 θ)) =
          PowerSeries.mk g * (PowerSeries.mk (fun k => (θ⁻¹) ^ k) *
            PowerSeries.mk (armaCoeff 0 θ⁻¹)) * PowerSeries.mk (armaCoeff 0 θ) by ring,
        mk_geom_factor θ, mul_one]
    rw [hcoef] at hft
    exact hft.congr_fun fun n => by rw [hw]
  have hfitted : gen (factorCoeff θ⁻¹ g) θ⁻¹ = (1 - θ⁻¹ ^ 2) * gen g θ⁻¹ := by
    rw [gen_factorCoeff θ⁻¹ hg hq.le, sq]
  have hgne : gen g θ⁻¹ ≠ 0 := by
    intro h0
    refine genFnC_ne_zero_of_recoverable hg ⟨h, hh, hconv⟩ (z := ((θ⁻¹ : ℝ) : ℂ)) ?_ ?_
    · rw [Complex.norm_real, Real.norm_eq_abs]; exact hq.le
    · rw [genFnC_ofReal, h0, Complex.ofReal_zero]
  have hsq : (1 : ℝ) - θ⁻¹ ^ 2 ≠ 0 := by
    have : θ⁻¹ ^ 2 < 1 := by
      rw [← sq_abs]
      exact pow_lt_one₀ (abs_nonneg _) hq two_ne_zero
    linarith
  have hwne : woldInnov θ (maOne θ e) t ≠ e t := by
    intro hwe
    have hst : s t ∈ pastSpan s t := by simpa using mem_pastSpan_self s t 0
    have hsub' := pastSpan_mono s (show t - 1 ≤ t by omega) hsub
    have : e t ∈ pastSpan s t := by
      rw [← hwe]
      have := Submodule.sub_mem _ hst hsub'
      convert this using 1
      simp only [hs, ha_def]
      abel
    exact hnot this
  exact ⟨hproj, hnorm, hwhite, hfit, hroot, hfitted, by rw [hfitted]; exact mul_ne_zero hsq hgne,
    hnot, hwne⟩

/-! ### Debt: the ex-post present value, and recovering the shock from the debt history -/

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601 (tool): for `|ρ| < 1` the Hansen–Sargent
coefficients `c_k = ∑ⱼ ρʲ a_{k+1+j}` are absolutely summable, so debt `v_t = ∑ c_k e_{t−k}` is a
moving average. -/
theorem summable_abs_hsCoeff {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) {ρ : ℝ}
    (hρ : |ρ| < 1) : Summable (fun k => |hsCoeff a ρ k|) := by
  set F : ℕ × ℕ → ℝ := fun p => |ρ| ^ p.2 * |a (p.1 + 1 + p.2)| with hF
  have hF0 : 0 ≤ F := fun p => by positivity
  have hsw : Summable (F ∘ Prod.swap) := by
    have h0 : 0 ≤ F ∘ Prod.swap := fun p => hF0 p.swap
    rw [summable_prod_of_nonneg h0]
    have hj : ∀ j : ℕ, Summable fun k : ℕ => |ρ| ^ j * |a (k + 1 + j)| := fun j =>
      ((summable_nat_add_iff (f := fun i => |a i|) (1 + j)).mpr ha).mul_left (|ρ| ^ j) |>.congr
        fun k => by simp only [add_assoc]
    refine ⟨hj, ?_⟩
    refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun k => h0 _) (fun j => ?_)
      ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right (∑' i, |a i|))
    change ∑' k, |ρ| ^ j * |a (k + 1 + j)| ≤ |ρ| ^ j * ∑' i, |a i|
    rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑' k, |a (k + 1 + j)| = ∑' k, |a (k + (1 + j))| :=
          tsum_congr fun k => by rw [add_assoc]
      _ ≤ ∑' i, |a i| := by
          rw [← ha.sum_add_tsum_nat_add (1 + j)]
          exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hFs : Summable F := (Equiv.prodComm ℕ ℕ).summable_iff.mp hsw
  have hk := ((summable_prod_of_nonneg hF0).mp hFs).2
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_) hk
  have hsk : Summable fun j => ‖ρ ^ j * a (k + 1 + j)‖ :=
    ((summable_prod_of_nonneg hF0).mp hFs).1 k |>.congr fun j => by
      simp [hF]
  calc |hsCoeff a ρ k| = ‖∑' j, ρ ^ j * a (k + 1 + j)‖ := by rw [Real.norm_eq_abs]; rfl
    _ ≤ ∑' j, ‖ρ ^ j * a (k + 1 + j)‖ := norm_tsum_le_tsum_norm hsk
    _ = ∑' j, F (k, j) := tsum_congr fun j => by simp [hF]

/-- Cochrane (2023), Online Appendix eq. (2.18), p. 600 ("debt equals the ex-post as well as
expected present value of surpluses"), in the Hilbert space: if `a(ρ) = 0`, `|ρ| < 1`, then
`∑_{j≥0} ρʲ s_{t+1+j}` converges to the debt `v_t = ∑ c_k e_{t−k}` (Hansen–Sargent `c`). -/
theorem debt_hasSum_expost [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) {ρ : ℝ} (hρ : |ρ| < 1) (h0 : gen a ρ = 0)
    (t : ℤ) :
    HasSum (fun j : ℕ => ρ ^ j • maProc a e (t + 1 + j)) (maProc (hsCoeff a ρ) e t) := by
  have hc := summable_abs_hsCoeff ha hρ
  have hsum : Summable (fun j : ℕ => ρ ^ j • maProc a e (t + 1 + j)) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right ((∑' k, |a k|) * ‖e 0‖))
      fun j => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
    exact mul_le_mul_of_nonneg_left (norm_maProc_le he ha _) (by positivity)
  have hX := hsum.hasSum
  convert hX using 1
  refine eq_of_inner_e (maProc_mem_eSpan he hc t)
    (hasSum_mem_eSpan hX fun j => Submodule.smul_mem _ _ (maProc_mem_eSpan he ha _))
    fun u => ?_
  refine ((inner_hasSum_right hX (e u)).unique ?_).symm
  rw [inner_e_maProc_int he hc]
  by_cases hu : u ≤ t
  · simp only [hu, ↓reduceIte]
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, u = t - n := ⟨(t - u).toNat, by omega⟩
    have hn : (t - (t - (n : ℤ))).toNat = n := by omega
    rw [hn, hsCoeff]
    refine ((summable_hs ha hρ.le n).hasSum.mul_left σ2).congr_fun fun j => ?_
    rw [real_inner_smul_right, inner_e_maProc_int he ha]
    have h1 : t - (n : ℤ) ≤ t + 1 + j := by omega
    have h2 : (t + 1 + (j : ℤ) - (t - n)).toNat = n + 1 + j := by omega
    simp only [h1, ↓reduceIte, h2]
    ring
  · simp only [hu, ↓reduceIte]
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, u = t + 1 + n := ⟨(u - t - 1).toNat, by omega⟩
    rw [← hasSum_nat_add_iff' n]
    have hz : ∑ i ∈ Finset.range n, ⟪e (t + 1 + n), ρ ^ i • maProc a e (t + 1 + i)⟫ = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [real_inner_smul_right, inner_e_maProc_int he ha]
        have : ¬ t + 1 + (n : ℤ) ≤ t + 1 + i := by rw [Finset.mem_range] at hi; omega
        simp [this]
    rw [hz, sub_zero]
    have hsa : Summable (fun i => a i * ρ ^ i) :=
      Summable.of_norm_bounded ha fun i => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ.le)
    have := hsa.hasSum.mul_left (σ2 * ρ ^ n)
    rw [← gen, h0, mul_zero] at this
    refine this.congr_fun fun i => ?_
    rw [real_inner_smul_right, inner_e_maProc_int he ha]
    have h1 : t + 1 + (n : ℤ) ≤ t + 1 + ((i + n : ℕ) : ℤ) := by push_cast; omega
    have h2 : (t + 1 + ((i + n : ℕ) : ℤ) - (t + 1 + n)).toNat = i := by push_cast; omega
    simp only [h1, ↓reduceIte, h2]
    ring

/-- Cochrane (2023), p. 102 (tool): the moving average with coefficients `δ₀ = 1`, `δ_k = 0`
otherwise is the shock itself. -/
theorem maProc_delta [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (t : ℤ) :
    maProc (fun n => if n = 0 then 1 else 0) e t = e t := by
  have hs : Summable (fun n : ℕ => |(if n = 0 then (1 : ℝ) else 0)|) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by simp_all
  refine (maProc_hasSum he hs t).unique ?_
  convert hasSum_ite_eq (0 : ℕ) (e t) using 1
  funext n
  by_cases hn : n = 0 <;> simp [hn]

/-- Cochrane (2023), Online Appendix eq. (2.20), p. 601: with `a(L) = (1 − θL)g(L)`, `θ = ρ⁻¹`,
the Hansen–Sargent debt coefficients are `c_k = −θg_k`: "the non-invertible root cancels". -/
theorem hsCoeff_factor {θ : ℝ} (hθ : 1 < |θ|) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|)) :
    hsCoeff (factorCoeff θ g) θ⁻¹ = fun k => -θ * g k := by
  have hθ0 : θ ≠ 0 := by intro h0; rw [h0, abs_zero] at hθ; linarith
  have hq : |θ⁻¹| ≤ 1 := by rw [abs_inv]; exact inv_le_one_of_one_le₀ hθ.le
  have := (factor_value (a := factorCoeff θ g) hg (inv_ne_zero hθ0) hq rfl (fun k => by
    simp only [factorCoeff, inv_inv])).2
  funext k
  rw [this k, inv_inv]

/-- Cochrane (2023), Online Appendix eq. (2.20), p. 601 ("thus, one can recover the structural
shock to surpluses from an autoregression of debt on past debt"): if `a(L) = (1 − θL)g(L)`,
`|θ| > 1`, and `g` has an absolutely summable inverse `h`, then `e_t = −θ⁻¹∑_k h_k v_{t−k}`: the
shock lies in the closed span of current and past debt. -/
theorem shock_mem_debtSpan [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {θ : ℝ} (hθ : 1 < |θ|) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|)) (hrec : Recoverable g)
    (t : ℤ) : e t ∈ pastSpan (maProc (hsCoeff (factorCoeff θ g) θ⁻¹) e) t := by
  obtain ⟨h, hh, hconv⟩ := hrec
  have hθ0 : θ ≠ 0 := by intro h0; rw [h0, abs_zero] at hθ; linarith
  rw [hsCoeff_factor hθ hg]
  have hcg : Summable (fun k => |-θ * g k|) := (hg.mul_left |θ|).congr fun k => by
    rw [abs_mul, abs_neg]
  have hb : Summable (fun k => |-θ⁻¹ * h k|) := (hh.mul_left |θ⁻¹|).congr fun k => by
    rw [abs_mul, abs_neg]
  have hf := hasSum_filter_maProc he hb hcg t
  have hco : cconv (fun k => -θ⁻¹ * h k) (fun k => -θ * g k) =
      fun n => if n = 0 then 1 else 0 := by
    funext n
    rw [cconv, ← hconv n]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [hco, maProc_delta he] at hf
  refine hasSum_mem_pastSpan hf fun k => Submodule.smul_mem _ _ (mem_pastSpan_self _ t k)

/-- Cochrane (2023), Online Appendix p. 601 ("the debt is an invertible moving average of the
structural shock. Thus, one can recover the structural shock … from an autoregression of debt on
past debt"), **correction**: this needs the other roots of `a(L)` outside the unit circle. With
`a(L) = (1 − θL)(1 − 2L)`, `|θ| > 1`, the government repays (`a(θ⁻¹) = 0`) and debt is
`v_t = −θ(1 − 2L)e_t`, a function of current and past shocks, but the shock is NOT in the closed
span of current and past debt (the debt MA has the root `1/2` inside the disc). -/
theorem debt_not_invertible_example [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ}
    (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {θ : ℝ} (hθ : 1 < |θ|) (t : ℤ) :
    gen (factorCoeff θ (armaCoeff 0 2)) θ⁻¹ = 0 ∧
    hsCoeff (factorCoeff θ (armaCoeff 0 2)) θ⁻¹ = (fun k => -θ * armaCoeff 0 2 k) ∧
    e t ∉ pastSpan (maProc (hsCoeff (factorCoeff θ (armaCoeff 0 2)) θ⁻¹) e) t := by
  have hθ0 : θ ≠ 0 := by intro h0; rw [h0, abs_zero] at hθ; linarith
  have hq : |θ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hθ
  have hg := summable_abs_armaCoeff (show |(0 : ℝ)| < 1 by simp) 2
  have hhs := hsCoeff_factor hθ hg
  refine ⟨by rw [gen_factorCoeff θ hg hq.le, mul_inv_cancel₀ hθ0, sub_self, zero_mul], hhs, ?_⟩
  rw [hhs]
  have hcg : Summable (fun k => |-θ * armaCoeff 0 2 k|) := (hg.mul_left |θ|).congr fun k => by
    rw [abs_mul, abs_neg]
  have hroot : gen (fun k => -θ * armaCoeff 0 2 k) (1 / 2) = 0 := by
    have h1 : gen (fun k => -θ * armaCoeff 0 2 k) (1 / 2) =
        -θ * gen (armaCoeff 0 2) (1 / 2) := by
      rw [Cochrane.DebtDeficitsInflation.Innovations.gen,
        Cochrane.DebtDeficitsInflation.Innovations.gen, ← tsum_mul_left]
      exact tsum_congr fun j => by ring
    rw [h1, ma1_aRho]
    norm_num
  exact not_mem_pastSpan_of_aRho_eq_zero he hσ hcg (by norm_num) hroot t

/-! ### Granger causality: debt helps forecast surpluses -/

/-- Cochrane (2023), Online Appendix p. 597 (tool; stationarity of a moving average in white
noise): white noise with `σ² ≠ 0` has a unitary time shift `U e_t = e_{t+1}` of the whole
Hilbert space (extend the normalised shocks to a Hilbert basis and shift them, fixing the rest). -/
theorem exists_shift [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (hσ : σ2 ≠ 0) : ∃ U : H ≃ₗᵢ[ℝ] H, ∀ t, U (e t) = e (t + 1) := by
  classical
  have hσn : σ2 = ‖e 0‖ ^ 2 := by
    have := he 0 0
    simp only [↓reduceIte, real_inner_self_eq_norm_sq] at this
    exact this.symm
  have hn : ‖e 0‖ ≠ 0 := by
    intro h0; rw [h0] at hσn; exact hσ (by simpa using hσn)
  set ê : ℤ → H := fun t => ‖e 0‖⁻¹ • e t with hê
  have hon : Orthonormal ℝ ê := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [hê, real_inner_smul_left, real_inner_smul_right]
    rw [he i j]
    split_ifs
    · rw [hσn]; field_simp
    · ring
  have hinj : Function.Injective ê := hon.linearIndependent.injective
  have hsub : Orthonormal ℝ (Subtype.val : Set.range ê → H) :=
    (orthonormal_subtype_range hinj).2 hon
  obtain ⟨w, b, hsw, hb⟩ := hsub.exists_hilbertBasis_extension
  have hmem : ∀ t, ê t ∈ w := fun t => hsw ⟨t, rfl⟩
  have hch : ∀ t (h : ∃ s, ê s = ê t), h.choose = t := fun t h => hinj h.choose_spec
  let f : w → w := fun x => if h : ∃ t, ê t = x then ⟨ê (h.choose + 1), hmem _⟩ else x
  let g : w → w := fun x => if h : ∃ t, ê t = x then ⟨ê (h.choose - 1), hmem _⟩ else x
  have hf : ∀ t, f ⟨ê t, hmem t⟩ = ⟨ê (t + 1), hmem _⟩ := fun t => by
    have h : ∃ s, ê s = ê t := ⟨t, rfl⟩
    simp only [f, h, ↓reduceDIte, hch t h]
  have hg : ∀ t, g ⟨ê t, hmem t⟩ = ⟨ê (t - 1), hmem _⟩ := fun t => by
    have h : ∃ s, ê s = ê t := ⟨t, rfl⟩
    simp only [g, h, ↓reduceDIte, hch t h]
  have hgf : ∀ x, g (f x) = x := fun x => by
    by_cases h : ∃ t, ê t = x
    · obtain ⟨t, ht⟩ := h
      obtain rfl : x = ⟨ê t, hmem t⟩ := Subtype.ext ht.symm
      rw [hf, hg]
      simp
    · simp only [f, g, h, ↓reduceDIte]
  have hfg : ∀ x, f (g x) = x := fun x => by
    by_cases h : ∃ t, ê t = x
    · obtain ⟨t, ht⟩ := h
      obtain rfl : x = ⟨ê t, hmem t⟩ := Subtype.ext ht.symm
      rw [hg, hf]
      simp
    · simp only [f, g, h, ↓reduceDIte]
  let σ : w ≃ w := ⟨f, g, hgf, hfg⟩
  have hb' : Orthonormal ℝ (b ∘ σ) := b.orthonormal.comp σ σ.injective
  have hsp : ⊤ ≤ (Submodule.span ℝ (Set.range (b ∘ σ))).topologicalClosure := by
    rw [Set.range_comp, σ.range_eq_univ, Set.image_univ, b.dense_span]
  refine ⟨b.repr.trans (HilbertBasis.mk hb' hsp).repr.symm, fun t => ?_⟩
  have key : ∀ i, (b.repr.trans (HilbertBasis.mk hb' hsp).repr.symm) (b i) = b (σ i) := by
    intro i
    rw [LinearIsometryEquiv.trans_apply, b.repr_self, HilbertBasis.repr_symm_single,
      HilbertBasis.coe_mk]
    rfl
  have hbi : ∀ τ, b ⟨ê τ, hmem τ⟩ = ê τ := fun τ => by rw [hb]
  have het : ∀ τ, e τ = ‖e 0‖ • ê τ := fun τ => by
    rw [hê, smul_smul, mul_inv_cancel₀ hn, one_smul]
  rw [het, map_smul, ← hbi, key]
  change ‖e 0‖ • b (f ⟨ê t, hmem t⟩) = e (t + 1)
  rw [hf, hbi, het (t + 1)]

/-- Cochrane (2023), Online Appendix p. 601 ("a VAR including surplus and value of debt"): the
closed linear span of current and past surpluses AND current and past debt. -/
noncomputable def jointSpan (s v : ℤ → H) (t : ℤ) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range (fun k : ℕ => s (t - k)) ∪
    Set.range (fun k : ℕ => v (t - k)))).topologicalClosure

/-- Cochrane (2023), p. 601 (tool): the surplus history is part of the VAR's information. -/
theorem pastSpan_le_jointSpan (s v : ℤ → H) (t : ℤ) : pastSpan s t ≤ jointSpan s v t :=
  Submodule.topologicalClosure_mono (Submodule.span_mono Set.subset_union_left)

/-- Cochrane (2023), p. 601 (tool): the debt history is part of the VAR's information. -/
theorem debt_mem_jointSpan (s v : ℤ → H) (t : ℤ) (k : ℕ) : v (t - k) ∈ jointSpan s v t :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inr ⟨k, rfl⟩))

/-- Cochrane (2023), p. 601 (tool): the closed span of the debt history is part of the VAR's
information. -/
theorem pastSpan_debt_le_jointSpan (s v : ℤ → H) (t : ℤ) : pastSpan v t ≤ jointSpan s v t :=
  Submodule.topologicalClosure_mono (Submodule.span_mono Set.subset_union_right)

/-- Cochrane (2023), p. 597 (tool): a continuous linear map sending the generators of one past
span to those of another maps the closed spans into each other. -/
theorem map_pastSpan (L : H →L[ℝ] H) {s s' : ℤ → H} {t t' : ℤ}
    (h : ∀ k : ℕ, L (s (t - k)) = s' (t' - k)) {x : H} (hx : x ∈ pastSpan s t) :
    L x ∈ pastSpan s' t' := by
  have hle : pastSpan s t ≤ (pastSpan s' t').comap (L : H →ₗ[ℝ] H) := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨k, rfl⟩
      change L (s (t - k)) ∈ pastSpan s' t'
      rw [h k]
      exact mem_pastSpan_self s' t' k
    · exact (Submodule.isClosed_topologicalClosure _).preimage L.continuous
  exact hle hx

/-- Cochrane (2023), Online Appendix eq. (2.21), p. 601 ("VAR shocks to debt `ε_t` help to forecast
surpluses, so debt Granger-causes surpluses"), for an ARBITRARY absolutely summable moving
average: let `s_t = a(L)e_t` with `a₀ ≠ 0`, `a(ρ) = 0`, `|ρ| < 1`, and let `v_t = ∑c_ke_{t−k}` be
the debt (Hansen–Sargent coefficients; by `debt_hasSum_expost` the ex-post present value of
surpluses). Then the best linear forecast of `s_{t+1}` from current and past surpluses and debt
differs from the one from surpluses alone, and its error is strictly smaller. The proof uses
only stationarity (`exists_shift`): if debt did not help, the surplus innovations `u` would satisfy
`∑ρʲ⟪u_{t+1}, s_{t+1+j}⟫ = 0`, which makes `∑ρᵏu_{t−k}` a nonzero element of the surplus past
orthogonal to that past. -/
theorem granger_general [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (hσ : σ2 ≠ 0) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (ha0 : a 0 ≠ 0) {ρ : ℝ}
    (hρ : |ρ| < 1) (h0 : gen a ρ = 0) (t : ℤ) :
    (haveI : (pastSpan (maProc a e) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      (pastSpan (maProc a e) t).starProjection (maProc a e (t + 1))) ≠
    (haveI : (jointSpan (maProc a e) (maProc (hsCoeff a ρ) e) t).HasOrthogonalProjection := by
        unfold jointSpan; infer_instance
      (jointSpan (maProc a e) (maProc (hsCoeff a ρ) e) t).starProjection (maProc a e (t + 1))) ∧
    (haveI : (pastSpan (maProc a e) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
    haveI : (jointSpan (maProc a e) (maProc (hsCoeff a ρ) e) t).HasOrthogonalProjection := by
        unfold jointSpan; infer_instance
      ‖maProc a e (t + 1) - (jointSpan (maProc a e) (maProc (hsCoeff a ρ) e) t).starProjection
        (maProc a e (t + 1))‖ <
      ‖maProc a e (t + 1) - (pastSpan (maProc a e) t).starProjection (maProc a e (t + 1))‖) := by
  have hS : ∀ τ, (pastSpan (maProc a e) τ).HasOrthogonalProjection := fun τ => by
    unfold pastSpan; infer_instance
  have hJ : (jointSpan (maProc a e) (maProc (hsCoeff a ρ) e) t).HasOrthogonalProjection := by
    unfold jointSpan; infer_instance
  set s := maProc a e with hs
  set v := maProc (hsCoeff a ρ) e with hv
  obtain ⟨U, hU⟩ := exists_shift he hσ
  set UL : H →L[ℝ] H := U.toContinuousLinearEquiv.toContinuousLinearMap with hUL
  set UL' : H →L[ℝ] H := U.symm.toContinuousLinearEquiv.toContinuousLinearMap with hUL'
  have hUs : ∀ τ, U (s τ) = s (τ + 1) := by
    intro τ
    have h1 := (maProc_hasSum he ha τ).mapL UL
    refine h1.unique ((maProc_hasSum he ha (τ + 1)).congr_fun fun k => ?_)
    change U (a k • e (τ - k)) = a k • e (τ + 1 - k)
    rw [map_smul, hU, show τ - (k : ℤ) + 1 = τ + 1 - k by ring]
  have hUs' : ∀ τ, U.symm (s τ) = s (τ - 1) := fun τ => by
    rw [← U.symm_apply_apply (s (τ - 1)), hUs, sub_add_cancel]
  -- the spans move with the shift
  have hUS : ∀ τ x, x ∈ pastSpan s τ → U x ∈ pastSpan s (τ + 1) := fun τ x hx =>
    map_pastSpan UL (fun k => by
      change U (s (τ - k)) = s (τ + 1 - k)
      rw [hUs, show τ - (k : ℤ) + 1 = τ + 1 - k by ring]) hx
  have hUS' : ∀ τ x, x ∈ pastSpan s (τ + 1) → U.symm x ∈ pastSpan s τ := fun τ x hx =>
    map_pastSpan UL' (fun k => by
      change U.symm (s (τ + 1 - k)) = s (τ - k)
      rw [hUs', show τ + 1 - (k : ℤ) - 1 = τ - k by ring]) hx
  have hP : ∀ τ x, U ((pastSpan s τ).starProjection x) =
      (pastSpan s (τ + 1)).starProjection (U x) := by
    intro τ x
    refine (Submodule.eq_starProjection_of_mem_orthogonal
      (hUS τ _ (Submodule.starProjection_apply_mem _ x)) ?_).symm
    rw [← map_sub, Submodule.mem_orthogonal]
    intro y hy
    rw [← U.apply_symm_apply y, LinearIsometryEquiv.inner_map_map]
    exact Submodule.inner_right_of_mem_orthogonal (hUS' τ y hy)
      (Submodule.sub_starProjection_mem_orthogonal x)
  -- the surplus innovations and their stationarity
  set u : ℤ → H := fun τ => s τ - (pastSpan s (τ - 1)).starProjection (s τ) with hu
  have hUu : ∀ τ, U (u τ) = u (τ + 1) := by
    intro τ
    simp only [hu, map_sub, hP, hUs, sub_add_cancel, add_sub_cancel_right]
  have hu_orth : ∀ τ, u τ ∈ (pastSpan s (τ - 1))ᗮ := fun τ =>
    Submodule.sub_starProjection_mem_orthogonal (s τ)
  have hs_mem : ∀ τ, s τ ∈ pastSpan s τ := fun τ => by simpa using mem_pastSpan_self s τ 0
  have hu_mem : ∀ τ, u τ ∈ pastSpan s τ := fun τ =>
    Submodule.sub_mem _ (hs_mem τ)
      (pastSpan_mono s (by omega) (Submodule.starProjection_apply_mem _ _))
  have hstep : ∀ τ (j : ℕ), ⟪u (τ + 1), s (τ + 1 + j)⟫ = ⟪u τ, s (τ + j)⟫ := by
    intro τ j
    rw [← hUu, show τ + 1 + (j : ℤ) = τ + j + 1 by ring, ← hUs, LinearIsometryEquiv.inner_map_map]
  have hγ : ∀ τ (j : ℕ), ⟪u τ, s (τ + j)⟫ = ⟪u 0, s j⟫ := by
    intro τ j
    induction τ using Int.induction_on with
    | zero => simp
    | succ i ih => rw [hstep, ih]
    | pred i ih =>
      rw [← ih, ← hstep (-(i : ℤ) - 1) j, show -(i : ℤ) - 1 + 1 = -i by ring]
  have huu : ∀ τ, ⟪u τ, u τ⟫ = ⟪u 0, s 0⟫ := by
    intro τ
    have h1 : ⟪u τ, (pastSpan s (τ - 1)).starProjection (s τ)⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) (hu_orth τ)
    have h2 := hγ τ 0
    simp only [Nat.cast_zero, add_zero] at h2
    conv_lhs => rw [show u τ = s τ - (pastSpan s (τ - 1)).starProjection (s τ) from rfl]
    rw [inner_sub_right, h1, sub_zero, ← h2]
  -- the innovation is not zero
  have he_orth : ∀ τ, e τ ∈ (pastSpan s (τ - 1))ᗮ := fun τ =>
    mem_orthogonal_pastSpan fun k => by
      have := inner_e_maProc_future he ha (τ - 1 - k) k
      rwa [show τ - 1 - (k : ℤ) + 1 + k = τ by ring] at this
  have heu : ∀ τ, ⟪e τ, u τ⟫ = σ2 * a 0 := by
    intro τ
    have h1 : ⟪e τ, (pastSpan s (τ - 1)).starProjection (s τ)⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) (he_orth τ)
    change ⟪e τ, s τ - (pastSpan s (τ - 1)).starProjection (s τ)⟫ = _
    rw [inner_sub_right, h1, sub_zero]
    simpa using inner_e_maProc he ha τ 0
  have hu0 : ⟪u t, u t⟫ ≠ 0 := by
    intro h
    have : u t = 0 := inner_self_eq_zero.mp h
    have := heu t
    rw [‹u t = 0›, inner_zero_right] at this
    exact mul_ne_zero hσ ha0 this.symm
  have hnu : ∀ τ, ‖u τ‖ = ‖u 0‖ := by
    intro τ
    have h1 := huu τ
    have h2 := huu 0
    rw [real_inner_self_eq_norm_sq] at h1 h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (h1.trans h2.symm)
  -- the main argument
  have hne : (pastSpan s t).starProjection (s (t + 1)) ≠
      (jointSpan s v t).starProjection (s (t + 1)) := by
    intro hEq
    have hut : u (t + 1) = s (t + 1) - (jointSpan s v t).starProjection (s (t + 1)) := by
      change s (t + 1) - (pastSpan s (t + 1 - 1)).starProjection (s (t + 1)) = _
      rw [add_sub_cancel_right, hEq]
    have hJo : u (t + 1) ∈ (jointSpan s v t)ᗮ := by
      rw [hut]; exact Submodule.sub_starProjection_mem_orthogonal _
    have hv0 : ⟪u (t + 1), v t⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (by simpa using debt_mem_jointSpan s v t 0) hJo
    -- `∑ρʲγ_j = 0`
    have hΓ : HasSum (fun j : ℕ => ρ ^ j * ⟪u 0, s j⟫) 0 := by
      have h := inner_hasSum_right (debt_hasSum_expost he ha hρ h0 t) (u (t + 1))
      rw [← hv, hv0] at h
      refine h.congr_fun fun j => ?_
      rw [real_inner_smul_right, ← hγ (t + 1) j]
    -- `y = ∑ρᵏu_{t−k}`
    have hys : Summable (fun k : ℕ => ρ ^ k • u (t - k)) := by
      refine Summable.of_norm_bounded
        ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right ‖u 0‖) fun k => ?_
      rw [norm_smul, Real.norm_eq_abs, abs_pow, hnu]
    have hy := hys.hasSum
    set y := ∑' k : ℕ, ρ ^ k • u (t - k) with hy_def
    have hyS : y ∈ pastSpan s t :=
      hasSum_mem_pastSpan hy fun k => Submodule.smul_mem _ _
        (pastSpan_mono s (by omega) (hu_mem (t - k)))
    have hyO : y ∈ (pastSpan s t)ᗮ := by
      refine mem_orthogonal_pastSpan fun j => ?_
      rw [real_inner_comm]
      have h := inner_hasSum_right hy (s (t - j))
      refine h.unique ?_
      rw [← hasSum_nat_add_iff' j]
      have hz : ∑ k ∈ Finset.range j, ⟪s (t - j), ρ ^ k • u (t - k)⟫ = 0 :=
        Finset.sum_eq_zero fun k hk => by
          rw [real_inner_smul_right]
          have hkj : k < j := Finset.mem_range.mp hk
          have hmem : s (t - j) ∈ pastSpan s (t - k - 1) := by
            have := mem_pastSpan_self s (t - k - 1) (j - k - 1)
            rwa [show t - (k : ℤ) - 1 - ((j - k - 1 : ℕ) : ℤ) = t - j by omega]
              at this
          rw [Submodule.inner_right_of_mem_orthogonal hmem (hu_orth (t - k)), mul_zero]
      rw [hz, sub_zero]
      have := hΓ.mul_left (ρ ^ j)
      rw [mul_zero] at this
      refine this.congr_fun fun i => ?_
      rw [real_inner_smul_right, real_inner_comm,
        show t - ((i + j : ℕ) : ℤ) = t - j - i by push_cast; ring,
        show s (t - j) = s (t - j - i + i) by ring_nf, hγ, pow_add]
      ring
    have hy0 : y = 0 := inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hyS hyO)
    have hyu : ⟪u t, y⟫ = ⟪u t, u t⟫ := by
      have h := inner_hasSum_right hy (u t)
      refine h.unique ?_
      have h1 : HasSum (fun k : ℕ => ⟪u t, ρ ^ k • u (t - k)⟫)
          ⟪u t, ρ ^ 0 • u (t - ((0 : ℕ) : ℤ))⟫ := hasSum_single 0 fun k hk => by
        rw [real_inner_smul_right]
        have hmem : u (t - k) ∈ pastSpan s (t - 1) :=
          pastSpan_mono s (by omega) (hu_mem (t - k))
        rw [Submodule.inner_left_of_mem_orthogonal hmem (hu_orth t), mul_zero]
      have e0 : ⟪u t, ρ ^ 0 • u (t - ((0 : ℕ) : ℤ))⟫ = ⟪u t, u t⟫ := by simp
      rwa [e0] at h1
    rw [hy0, inner_zero_right] at hyu
    exact hu0 hyu.symm
  refine ⟨hne, ?_⟩
  -- Pythagoras
  set p := (pastSpan s t).starProjection (s (t + 1))
  set q := (jointSpan s v t).starProjection (s (t + 1))
  have hpJ : p ∈ jointSpan s v t :=
    pastSpan_le_jointSpan s v t (Submodule.starProjection_apply_mem _ _)
  have hqp : q - p ∈ jointSpan s v t :=
    Submodule.sub_mem _ (Submodule.starProjection_apply_mem _ _) hpJ
  have horth : ⟪s (t + 1) - q, q - p⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hqp (Submodule.sub_starProjection_mem_orthogonal _)
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  rw [show s (t + 1) - q + (q - p) = s (t + 1) - p by abel] at hpy
  have hpos : 0 < ‖q - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have : ‖s (t + 1) - q‖ ^ 2 < ‖s (t + 1) - p‖ ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this

/-- Cochrane (2023), p. 601 (tool): a vector orthogonal to every current and past surplus and debt
is orthogonal to the joint span. -/
theorem mem_orthogonal_jointSpan {s v : ℤ → H} {t : ℤ} {x : H}
    (hs : ∀ k : ℕ, ⟪x, s (t - k)⟫ = 0) (hv : ∀ k : ℕ, ⟪x, v (t - k)⟫ = 0) :
    x ∈ (jointSpan s v t)ᗮ := by
  have hle : jointSpan s v t ≤ (ℝ ∙ x)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
      (Submodule.isClosed_orthogonal _)
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hs k)
    · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hv k)
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [real_inner_comm]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hu)

/-- Cochrane (2023), Online Appendix eqs. (2.20)–(2.21), p. 601, and p. 102 ("the value of debt
reveals the true shock"), quantitatively: for `a(L) = (1 − θL)g(L)`, `|θ| > 1` (`ρ = θ⁻¹`), `g₀ = 1`
and `g` invertible, the joint surplus–debt forecast of `s_{t+1}` has error `e_{t+1}` (variance
`σ²`: the structural shock is recovered), the surplus-only forecast has error variance
`θ²σ² = σ²/ρ²`, and `σ² < θ²σ²`: debt Granger-causes surpluses. -/
theorem granger_factor [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (hσ : σ2 ≠ 0) {θ : ℝ} (hθ : 1 < |θ|) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|))
    (hg0 : g 0 = 1) (hrec : Recoverable g) (t : ℤ) :
    (haveI : (jointSpan (maProc (factorCoeff θ g) e)
        (maProc (hsCoeff (factorCoeff θ g) θ⁻¹) e) t).HasOrthogonalProjection := by
        unfold jointSpan; infer_instance
      Submodule.starProjection
        (jointSpan (maProc (factorCoeff θ g) e) (maProc (hsCoeff (factorCoeff θ g) θ⁻¹) e) t)
        (maProc (factorCoeff θ g) e (t + 1))) =
      maProc (factorCoeff θ g) e (t + 1) - e (t + 1) ∧
    (haveI : (pastSpan (maProc (factorCoeff θ g) e) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      ‖maProc (factorCoeff θ g) e (t + 1) - Submodule.starProjection
        (pastSpan (maProc (factorCoeff θ g) e) t) (maProc (factorCoeff θ g) e (t + 1))‖ ^ 2) =
      θ ^ 2 * σ2 ∧
    ‖e (t + 1)‖ ^ 2 = σ2 ∧ σ2 < θ ^ 2 * σ2 := by
  have hθ0 : θ ≠ 0 := by intro h0; rw [h0, abs_zero] at hθ; linarith
  have hq : |θ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hθ
  have ha := summable_factorCoeff θ hg
  have hc := summable_abs_hsCoeff ha hq
  have hJ : (jointSpan (maProc (factorCoeff θ g) e)
      (maProc (hsCoeff (factorCoeff θ g) θ⁻¹) e) t).HasOrthogonalProjection := by
    unfold jointSpan; infer_instance
  set s := maProc (factorCoeff θ g) e with hs
  set v := maProc (hsCoeff (factorCoeff θ g) θ⁻¹) e with hv
  have hσn : ‖e (t + 1)‖ ^ 2 = σ2 := by
    have := he (t + 1) (t + 1)
    simp only [↓reduceIte, real_inner_self_eq_norm_sq] at this
    exact this
  have hσp : 0 < σ2 := lt_of_le_of_ne (hσn ▸ sq_nonneg _) (Ne.symm hσ)
  -- the joint forecast
  have hJo : e (t + 1) ∈ (jointSpan s v t)ᗮ := mem_orthogonal_jointSpan
    (fun k => by
      have := inner_e_maProc_future he ha (t - k) k
      rwa [show t - (k : ℤ) + 1 + k = t + 1 by ring] at this)
    (fun k => by
      have := inner_e_maProc_future he hc (t - k) k
      rwa [show t - (k : ℤ) + 1 + k = t + 1 by ring] at this)
  have hqJ : s (t + 1) - e (t + 1) ∈ jointSpan s v t := by
    have h := maProc_hasSum he ha (t + 1)
    rw [← hasSum_nat_add_iff' 1] at h
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, sub_zero] at h
    rw [show factorCoeff θ g 0 = 1 from hg0, one_smul] at h
    refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto h.tendsto_sum_nat
      (Eventually.of_forall fun n => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_)
    rw [show t + 1 - ((k + 1 : ℕ) : ℤ) = t - k by push_cast; ring]
    exact pastSpan_debt_le_jointSpan s v t
      (pastSpan_mono v (by omega) (shock_mem_debtSpan he hθ hg hrec (t - k)))
  have hPJ : (jointSpan s v t).starProjection (s (t + 1)) = s (t + 1) - e (t + 1) :=
    Submodule.eq_starProjection_of_mem_orthogonal hqJ (by simpa using hJo)
  -- the surplus-only forecast
  obtain ⟨hproj, hnorm, -⟩ := wold_factor he hσ hθ hg hg0 hrec (t + 1)
  simp only [add_sub_cancel_right] at hproj
  have hS : (pastSpan s t).HasOrthogonalProjection := by unfold pastSpan; infer_instance
  have hPS : ‖s (t + 1) - (pastSpan s t).starProjection (s (t + 1))‖ ^ 2 = θ ^ 2 * σ2 := by
    rw [hproj, sub_sub_cancel, ← real_inner_self_eq_norm_sq, hnorm]
  have hθ2 : 1 < θ ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_nonneg θ]
  exact ⟨hPJ, hPS, hσn, by nlinarith⟩

/-! ### Links to the MA(1) statements of `Invertibility` -/

/-- Cochrane (2023), p. 102 (link): with `g = 1` the factorised moving average is the MA(1)
`1 − θL` of `Invertibility` (`armaCoeff 0 θ`). -/
theorem factorCoeff_delta (θ : ℝ) :
    factorCoeff θ (fun k => if k = 0 then 1 else 0) = armaCoeff 0 θ := by
  funext k
  rcases k with _ | _ | k <;> simp [factorCoeff, armaCoeff]

/-- Cochrane (2023), p. 102 (link): `g = 1` is trivially invertible. -/
theorem recoverable_delta : Recoverable (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) := by
  refine ⟨fun k => if k = 0 then 1 else 0,
    summable_of_ne_finset_zero (s := {0}) fun n hn => by simp_all, fun n => ?_⟩
  rcases n with _ | n
  · simp
  · rw [Finset.sum_eq_zero fun k _ => ?_]
    · simp
    · by_cases hk0 : k = 0
      · subst hk0; simp
      · simp [hk0]

/-- Cochrane (2023), p. 102 and Online Appendix (2.13), p. 599 (link): for `g = 1`, `wold_factor`
is `Invertibility.Hilbert.ma1_wold` — structural MA(1) `1 − θL`, fitted MA(1) `1 − θ⁻¹L` with
`ã(ρ) = 1 − ρ²` at `ρ = θ⁻¹` (`Invertibility.ma1_fitted_aRho`), and debt `v_t = −θe_t`
(p. 102, "`v_t = −ρ⁻¹ε_t`"). -/
theorem wold_factor_ma1 {θ : ℝ} (hθ : 1 < |θ|) :
    factorCoeff θ (fun k => if k = 0 then 1 else 0) = armaCoeff 0 θ ∧
    factorCoeff θ⁻¹ (fun k => if k = 0 then 1 else 0) = armaCoeff 0 θ⁻¹ ∧
    gen (factorCoeff θ⁻¹ (fun k => if k = 0 then 1 else 0)) θ⁻¹ = 1 - θ⁻¹ ^ 2 ∧
    hsCoeff (armaCoeff 0 θ) θ⁻¹ = fun k => -θ * (if k = 0 then 1 else 0) := by
  have hq : |θ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hθ
  refine ⟨factorCoeff_delta θ, factorCoeff_delta θ⁻¹, ?_, ?_⟩
  · rw [factorCoeff_delta]
    exact (ma1_fitted_aRho hq).1
  · rw [← factorCoeff_delta θ]
    exact hsCoeff_factor hθ (summable_of_ne_finset_zero (s := {0}) fun n hn => by simp_all)

end Cochrane.DebtDeficitsInflation.InvertibilityMeasure
