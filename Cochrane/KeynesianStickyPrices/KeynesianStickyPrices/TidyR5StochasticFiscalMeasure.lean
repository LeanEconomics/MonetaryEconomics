/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR5StochasticPathsMeasure
import KeynesianStickyPrices.TidyR5StochasticFiscal

/-!
# The fiscal requirements of Figures 17.6–17.7 on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4.1–17.4.2, eq. (17.19),
pp. 410–414, Figures 17.6 and 17.7.

The measure-theoretic version of TidyR5StochasticFiscal, on a probability space with a
filtration and Mathlib's conditional expectation:

* `FlowM`: the linearised flow condition `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` a.e.;
  `innov_finite_ae` (the finite-horizon unexpected-inflation identity, a.s. for all horizons) and
  `eq_17_19_own_dating_ae` (**(17.19)** a.s.: on the event where the transversality condition
  holds and the news series converge,
  `ΔE_{t+1} π_{t+1} = −∑ ρʲ ΔE_{t+1} s̃_{t+1+j} + ρ ∑ ρʲ ΔE_{t+1} r_{t+1+j}`).
* `surplus_news_rise_ae` (Fig. 17.6's `Δs` as surplus news): a.s. on the event of a permanent
  rise of expected rates, the surplus news is `ρ(1 − δ)/(λ₁ − ρ) − δ`.
* `ar1_iterate_ae`, `news_rate_ar1_ae`, `news_ar1_ae` (Fig. 17.7): with AR(1) rates the rate news
  is `ε ηᵏ` and the inflation news is `cεηʲ + (δ − cε)λ₁^{−j}` a.s.; `surplus_news_ar1_ae`
  (`ρ = 1`): a.s., where (17.19)'s hypotheses hold, the surplus news is `ε Σs(δ/ε)`'s closed form;
  `news_u_ar1_ae` and `fig17_7_news_u_not_geometric_ae`: the news about the reverse-engineered
  disturbance is not geometric at the book's parameters, a.s. on `{ε ≠ 0, δ ≠ cε}`.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5StochasticFiscalMeasure

open MeasureTheory Filter Topology FullModel FiscalUnderpinnings TidyR5ExpectationsMeasure
open TidyR5StochasticPaths TidyR5StochasticPathsMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### News on a probability space -/

/-- Cochrane (2023), eq. (17.19), p. 411: `ΔE_{t+1}` is additive (a.e.). -/
theorem innov_add_ae {a b : Ω → ℝ} (ha : Integrable a S.μ) (hb : Integrable b S.μ) (t : ℕ) :
    S.innov t (a + b) =ᵐ[S.μ] S.innov t a + S.innov t b := by
  filter_upwards [S.E_add ha hb (t + 1), S.E_add ha hb t] with ω e1 e2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, Pi.add_apply, e1, e2]
  ring

/-- Cochrane (2023), eq. (17.19): `ΔE_{t+1}` commutes with differences (a.e.). -/
theorem innov_sub_ae {a b : Ω → ℝ} (ha : Integrable a S.μ) (hb : Integrable b S.μ) (t : ℕ) :
    S.innov t (a - b) =ᵐ[S.μ] S.innov t a - S.innov t b := by
  filter_upwards [S.E_sub ha hb (t + 1), S.E_sub ha hb t] with ω e1 e2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, e1, e2]
  ring

/-- Cochrane (2023), eq. (17.19): `ΔE_{t+1}` is homogeneous (a.e.). -/
theorem innov_smul_ae (c : ℝ) (a : Ω → ℝ) (t : ℕ) :
    S.innov t (c • a) =ᵐ[S.μ] c • S.innov t a := by
  filter_upwards [S.E_smul c a (t + 1), S.E_smul c a t] with ω e1 e2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, Pi.smul_apply, e1, e2, smul_eq_mul]
  ring

/-- Cochrane (2023), eq. (17.19): `ΔE_{t+1}` respects a.e. equality. -/
theorem innov_congr_ae {a b : Ω → ℝ} (h : a =ᵐ[S.μ] b) (t : ℕ) :
    S.innov t a =ᵐ[S.μ] S.innov t b := by
  filter_upwards [S.E_congr h (t + 1), S.E_congr h t] with ω e1 e2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, e1, e2]

/-- Cochrane (2023), eq. (17.19): a variable known at `t` has no news. -/
theorem innov_known {t : ℕ} {y : Ω → ℝ} (hy : StronglyMeasurable[S.𝓕 t] y)
    (hyi : Integrable y S.μ) : S.innov t y = 0 := by
  unfold MeasExpectationSystem.innov
  rw [S.E_of_stronglyMeasurable (hy.mono (S.𝓕.mono (Nat.le_succ t))) hyi,
    S.E_of_stronglyMeasurable hy hyi, sub_self]

/-- Cochrane (2023), eq. (17.19): news about a later forecast is news about the variable,
`ΔE_{t+1} E_n y = ΔE_{t+1} y` a.e. for `n ≥ t + 1`. -/
theorem innov_E_ae {t n : ℕ} (hn : t + 1 ≤ n) (y : Ω → ℝ) :
    S.innov t (S.E n y) =ᵐ[S.μ] S.innov t y := by
  filter_upwards [S.E_tower hn y, S.E_tower (by omega : t ≤ n) y] with ω e1 e2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, e1, e2]

/-! ### The unexpected-inflation identity (17.19) -/

/-- Cochrane (2023), p. 411 (one-period debt), on a probability space: the flow condition
`ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` a.e., all variables integrable. -/
def FlowM (ρ : ℝ) (i s v π : ℕ → Ω → ℝ) : Prop :=
  (∀ t, Integrable (i t) S.μ ∧ Integrable (s t) S.μ ∧ Integrable (v t) S.μ ∧
    Integrable (π t) S.μ) ∧
  ∀ t, ρ • v (t + 1) =ᵐ[S.μ] v t + i t - π (t + 1) - s (t + 1)

/-- Cochrane (2023), eq. (17.16): the ex-ante real rate `r_n = i_n − E_n π_{n+1}`. -/
noncomputable def reaM (i π : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ := i n - S.E n (π (n + 1))

/-- Cochrane (2023), eq. (17.19), p. 411, finite horizon, on a probability space: for adapted
`v`, `i`, almost surely, for every horizon `N`,
`ΔE_{t+1} π_{t+1} = −∑_{j≤N} ρʲ ΔE s̃_{t+1+j} + ∑_{j<N} ρ^{j+1} ΔE r_{t+1+j}
  − ρ^{N+1} ΔE v_{t+N+1}`. -/
theorem innov_finite_ae {ρ : ℝ} {i s v π : ℕ → Ω → ℝ} (hv : StronglyAdapted S.𝓕 v)
    (hi : StronglyAdapted S.𝓕 i) (hf : FlowM S ρ i s v π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ N, S.innov t (π (t + 1)) ω =
      -∑ j ∈ Finset.range (N + 1), ρ ^ j * S.innov t (s (t + 1 + j)) ω +
        ∑ j ∈ Finset.range N, ρ ^ (j + 1) * S.innov t (reaM S i π (t + 1 + j)) ω -
        ρ ^ (N + 1) * S.innov t (v (t + N + 1)) ω := by
  obtain ⟨hint, hfl⟩ := hf
  -- the news of the flow condition at every date `n`
  have hflow : ∀ n, ∀ᵐ ω ∂S.μ, ρ * S.innov t (v (n + 1)) ω =
      S.innov t (v n) ω + S.innov t (i n - π (n + 1)) ω - S.innov t (s (n + 1)) ω := by
    intro n
    obtain ⟨ii, -, iv, -⟩ := hint n
    obtain ⟨-, is', iv', iπ'⟩ := hint (n + 1)
    filter_upwards [innov_congr_ae S (hfl n) t, innov_smul_ae S ρ (v (n + 1)) t,
      innov_sub_ae S ((iv.add ii).sub iπ') is' t, innov_sub_ae S (iv.add ii) iπ' t,
      innov_add_ae S iv ii t, innov_sub_ae S ii iπ' t] with ω a b c d e f
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c d e f
    linear_combination -b + a + c + d + e - f
  have hrea : ∀ j, ∀ᵐ ω ∂S.μ, S.innov t (i (t + 1 + j) - π (t + 1 + j + 1)) ω =
      S.innov t (reaM S i π (t + 1 + j)) ω := by
    intro j
    obtain ⟨ii, -, -, -⟩ := hint (t + 1 + j)
    obtain ⟨-, -, -, iπ⟩ := hint (t + 1 + j + 1)
    filter_upwards [innov_sub_ae S ii iπ t, innov_sub_ae S ii (S.integrable_E _ _) t,
      innov_E_ae S (by omega : t + 1 ≤ t + 1 + j) (π (t + 1 + j + 1))] with ω a b c
    simp only [reaM, Pi.sub_apply] at a b c ⊢
    rw [a, b, c]
  have hvi : ∀ n, Integrable (v n) S.μ := fun n => (hint n).2.2.1
  have hii : ∀ n, Integrable (i n) S.μ := fun n => (hint n).1
  have hv0 := innov_known S (hv t) (hvi t)
  have hit := innov_known S (hi t) (hii t)
  filter_upwards [ae_all_iff.mpr hflow, ae_all_iff.mpr hrea,
    innov_sub_ae S (hii t) (hint (t + 1)).2.2.2 t] with ω hF hR h0 N
  rw [hit] at h0
  induction N with
  | zero =>
    have h := hF t
    rw [hv0, h0] at h
    simp only [Pi.zero_apply, Pi.sub_apply, zero_add, Finset.sum_range_one, pow_zero, one_mul,
      Finset.range_zero, Finset.sum_empty, pow_one, add_zero] at h ⊢
    linear_combination h
  | succ N ih =>
    have h := hF (t + N + 1)
    rw [show t + N + 1 = t + 1 + N by omega, show t + 1 + N + 1 = t + 1 + N + 1 from rfl,
      hR N] at h
    rw [ih, Finset.sum_range_succ _ (N + 1),
      Finset.sum_range_succ (fun j => ρ ^ (j + 1) * S.innov t (reaM S i π (t + 1 + j)) ω) N,
      show t + 1 + (N + 1) = t + 1 + N + 1 by omega, show t + N + 1 = t + 1 + N by omega,
      show t + (N + 1) + 1 = t + 1 + N + 1 by omega]
    linear_combination ρ ^ (N + 1) * h

/-- Cochrane (2023), eq. (17.19), p. 411, with the dating of (17.16), on a probability space:
almost surely, wherever the transversality condition `ρᴺ ΔE_{t+1} v_{t+N} → 0` holds and the
news series converge,
`ΔE_{t+1} π_{t+1} = −∑ ρʲ ΔE_{t+1} s̃_{t+1+j} + ρ ∑ ρʲ ΔE_{t+1} r_{t+1+j}`. -/
theorem eq_17_19_own_dating_ae {ρ : ℝ} {i s v π : ℕ → Ω → ℝ} (hv : StronglyAdapted S.𝓕 v)
    (hi : StronglyAdapted S.𝓕 i) (hf : FlowM S ρ i s v π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, Tendsto (fun N => ρ ^ N * S.innov t (v (t + N)) ω) atTop (𝓝 0) →
      Summable (fun j => ρ ^ j * S.innov t (s (t + 1 + j)) ω) →
      Summable (fun j => ρ ^ j * S.innov t (reaM S i π (t + 1 + j)) ω) →
      S.innov t (π (t + 1)) ω = -∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω +
        ρ * ∑' j, ρ ^ j * S.innov t (reaM S i π (t + 1 + j)) ω := by
  filter_upwards [innov_finite_ae S hv hi hf t] with ω hfin htvc hs hr
  have h1 : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), ρ ^ j * S.innov t (s (t + 1 + j)) ω)
      atTop (𝓝 (∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω)) :=
    hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun N => ∑ j ∈ Finset.range N,
      ρ ^ (j + 1) * S.innov t (reaM S i π (t + 1 + j)) ω) atTop
      (𝓝 (ρ * ∑' j, ρ ^ j * S.innov t (reaM S i π (t + 1 + j)) ω)) := by
    refine (hr.hasSum.tendsto_sum_nat.const_mul ρ).congr fun N => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : Tendsto (fun N => ρ ^ (N + 1) * S.innov t (v (t + N + 1)) ω) atTop (𝓝 0) :=
    htvc.comp (tendsto_add_atTop_nat 1)
  have hlim := (h1.neg.add h2).sub h3
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun N => hfin N) hlim

/-! ### Figure 17.6: surplus news -/

/-- Cochrane (2023), Fig. 17.6, p. 410, and eq. (17.19), on a probability space: with essentially
bounded processes, `0 ≤ ρ < 1`, adapted `v`, `i` and the flow condition, almost surely on the
event that the date-`(t+1)` news is a permanent rise of expected rates, the surplus news is
`ρ(1 − δ)/(λ₁ − ρ) − δ`, `δ = ΔE_{t+1} π_{t+1}` (`TidyR5StochasticFiscal.surplus_news_rise`). -/
theorem surplus_news_rise_ae {σ β κ ρ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {i r x π s v : ℕ → Ω → ℝ} (h : ModelM S σ β κ i r x π)
    (hv : StronglyAdapted S.𝓕 v) (hia : StronglyAdapted S.𝓕 i) (hf : FlowM S ρ i s v π)
    (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) (hvb : ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ M)
    (hib : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M) (hπb : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (∀ k, S.innov t (i (t + 1 + k)) ω = 1) →
      ∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω =
        ρ * (1 - S.innov t (π (t + 1)) ω) / (lam1 σ β κ - ρ) - S.innov t (π (t + 1)) ω := by
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have hint := hf.1
  have hrea : ∀ j, ∀ᵐ ω ∂S.μ, S.innov t (reaM S i π (t + 1 + j)) ω =
      S.innov t (i (t + 1 + j)) ω - S.innov t (π (t + 1 + (j + 1))) ω := by
    intro j
    filter_upwards [innov_sub_ae S (hint (t + 1 + j)).1 (S.integrable_E _ _) t,
      innov_E_ae S (by omega : t + 1 ≤ t + 1 + j) (π (t + 1 + j + 1))] with ω a b
    simp only [reaM, Pi.sub_apply] at a b ⊢
    rw [a, b]
    rfl
  filter_upwards [eq_17_19_own_dating_ae S hv hia hf t, news_path_ae S ha hβ h hib hπb t,
    ae_all_iff.mpr hrea, ae_bound_innov S hsb t, ae_bound_innov S hvb t]
    with ω h19 hnp hR hsB hvB hnews
  set δ := S.innov t (π (t + 1)) ω
  have hp := hnp.1
  have hn : (fun j => S.innov t (i (t + 1 + j)) ω) = stepI 0 := funext fun k => by
    rw [hnews k]; simp [stepI]
  rw [hn] at hp
  have hnπ : ∀ j, S.innov t (π (t + 1 + j)) ω = 1 + (δ - 1) * (lam1 σ β κ)⁻¹ ^ j := fun j => by
    rw [congrFun hp j, path_step0 ha hβ]
  have hrr : ∀ j, ρ ^ j * S.innov t (reaM S i π (t + 1 + j)) ω =
      (1 - δ) * (lam1 σ β κ)⁻¹ * (ρ * (lam1 σ β κ)⁻¹) ^ j := fun j => by
    rw [hR j, hnews j, hnπ (j + 1)]
    ring
  have hq0 : 0 ≤ ρ * (lam1 σ β κ)⁻¹ := mul_nonneg hρ0 (inv_nonneg.mpr hl0.le)
  have hq1 : ρ * (lam1 σ β κ)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hl0]; linarith
  have hRs : HasSum (fun j => ρ ^ j * S.innov t (reaM S i π (t + 1 + j)) ω)
      ((1 - δ) * (lam1 σ β κ)⁻¹ * (1 - ρ * (lam1 σ β κ)⁻¹)⁻¹) :=
    ((hasSum_geometric_of_lt_one hq0 hq1).mul_left ((1 - δ) * (lam1 σ β κ)⁻¹)).congr_fun
      fun j => by rw [hrr j]
  have htvc : Tendsto (fun N => ρ ^ N * S.innov t (v (t + N)) ω) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N => ρ ^ N * (2 * M)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (2 * M)
    refine squeeze_zero_norm (fun N => ?_) hlim
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_left (hvB (t + N)) (pow_nonneg hρ0 N)
  have hs : Summable fun j => ρ ^ j * S.innov t (s (t + 1 + j)) ω := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right (2 * M))
      (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_left (hsB _) (pow_nonneg hρ0 j)
  have e := h19 htvc hs hRs.summable
  rw [hRs.tsum_eq] at e
  have hden : lam1 σ β κ - ρ ≠ 0 := by linarith
  have h1 : (1 - ρ * (lam1 σ β κ)⁻¹) = (lam1 σ β κ - ρ) / lam1 σ β κ := by field_simp
  rw [h1] at e
  simp only [δ] at e ⊢
  field_simp at e ⊢
  linear_combination e

/-! ### Figure 17.7: AR(1) rates -/

/-- Cochrane (2023), p. 412, on a probability space: AR(1) rates, `E_t i_{t+1} = η i_t` a.s. -/
def IsAR1M (η : ℝ) (i : ℕ → Ω → ℝ) : Prop :=
  StronglyAdapted S.𝓕 i ∧ (∀ t, Integrable (i t) S.μ) ∧
    ∀ t, S.E t (i (t + 1)) =ᵐ[S.μ] η • i t

/-- Cochrane (2023), p. 412, on a probability space: `E_t i_{t+k} = ηᵏ i_t` a.s. -/
theorem ar1_iterate_ae {η : ℝ} {i : ℕ → Ω → ℝ} (h : IsAR1M S η i) (t k : ℕ) :
    S.E t (i (t + k)) =ᵐ[S.μ] η ^ k • i t := by
  obtain ⟨ha, hi, hE⟩ := h
  induction k with
  | zero =>
    rw [add_zero, pow_zero, one_smul, S.E_of_stronglyMeasurable (ha t) (hi t)]
  | succ k ih =>
    have e : t + (k + 1) = t + k + 1 := rfl
    rw [e]
    filter_upwards [(S.E_tower (Nat.le_add_right t k) (i (t + k + 1))).symm,
      S.E_congr (hE (t + k)) t, S.E_smul η (i (t + k)) t, ih] with ω a b c d
    rw [a, b, c, Pi.smul_apply, d]
    simp only [Pi.smul_apply, smul_eq_mul, pow_succ]
    ring

/-- Cochrane (2023), Fig. 17.7, p. 413, on a probability space: with AR(1) rates, a.s. the
date-`(s+1)` rate news is `ε ηᵏ` at every horizon, `ε = ΔE_{s+1} i_{s+1}`. -/
theorem news_rate_ar1_ae {η : ℝ} {i : ℕ → Ω → ℝ} (h : IsAR1M S η i) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ k, S.innov s (i (s + 1 + k)) ω = S.innov s (i (s + 1)) ω * η ^ k := by
  refine ae_all_iff.mpr fun k => ?_
  have e2 : s + (k + 1) = s + 1 + k := by omega
  have h2 := ar1_iterate_ae S h s (k + 1)
  have h3 := ar1_iterate_ae S h s 1
  rw [e2] at h2
  filter_upwards [ar1_iterate_ae S h (s + 1) k, h2, h3] with ω a b c
  have hE1 : S.E (s + 1) (i (s + 1)) = i (s + 1) := S.E_of_stronglyMeasurable (h.1 _) (h.2.1 _)
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c ⊢
  rw [a, b, hE1, c, pow_succ, pow_one]
  ring

/-- Cochrane (2023), Fig. 17.7, p. 413, on a probability space: with AR(1) rates (`0 ≤ η < 1`)
and essentially bounded rates and inflation, a.s. the inflation news is
`c ε ηʲ + (δ − c ε) λ₁^{−j}`. -/
theorem news_ar1_ae {σ β κ η M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hη0 : 0 ≤ η)
    (hη1 : η < 1) (hD : -β * η ^ 2 + (1 + β + σ * κ) * η - 1 ≠ 0) {i r x π : ℕ → Ω → ℝ}
    (h : ModelM S σ β κ i r x π) (hiAR : IsAR1M S η i) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M)
    (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ j, S.innov s (π (s + 1 + j)) ω =
      cAR σ β κ η * S.innov s (i (s + 1)) ω * η ^ j +
        (S.innov s (π (s + 1)) ω - cAR σ β κ η * S.innov s (i (s + 1)) ω) *
          (lam1 σ β κ)⁻¹ ^ j := by
  filter_upwards [news_path_ae S ha hβ h hi hπ s, news_rate_ar1_ae S hiAR s] with ω hp hr j
  set ε := S.innov s (i (s + 1)) ω
  set δ := S.innov s (π (s + 1)) ω
  have hn : (fun k => S.innov s (i (s + 1 + k)) ω) = fun k => ε * η ^ k :=
    funext fun k => hr k
  have e := congrFun hp.1 j
  rw [hn] at e
  rw [e]
  have h1 := path_sub_path σ β κ (fun k => ε * η ^ k) δ (ε * cAR σ β κ η) j
  have h2 := path_smul σ β κ ε (fun k => η ^ k) (cAR σ β κ η) j
  rw [← piAR_eq_path ha hβ hη0 hη1 hD] at h2
  simp only [piAR, sub_self, zero_mul, add_zero] at h2
  linear_combination h1 + h2

/-- Cochrane (2023), Fig. 17.7 and p. 412, on a probability space: with AR(1) rates, `ρ = 1`
and the flow condition, a.s., wherever (17.19)'s transversality condition and surplus-news
summability hold, the surplus news is
`−δ + ε/(1 − η) − cεη/(1 − η) − (δ − cε)/(λ₁ − 1)` (`= ε Σs(δ/ε)` for `ε ≠ 0`,
`TidyR5StochasticFiscal.surplus_news_ar1_eq_sigmaS`). -/
theorem surplus_news_ar1_ae {σ β κ η M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hη0 : 0 ≤ η)
    (hη1 : η < 1) (hD : -β * η ^ 2 + (1 + β + σ * κ) * η - 1 ≠ 0)
    {i r x π s v : ℕ → Ω → ℝ} (h : ModelM S σ β κ i r x π) (hiAR : IsAR1M S η i)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ)
    (hv : StronglyAdapted S.𝓕 v) (hf : FlowM S 1 i s v π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, Tendsto (fun N => (1 : ℝ) ^ N * S.innov t (v (t + N)) ω) atTop (𝓝 0) →
      Summable (fun j => (1 : ℝ) ^ j * S.innov t (s (t + 1 + j)) ω) →
      ∑' j, (1 : ℝ) ^ j * S.innov t (s (t + 1 + j)) ω =
        -S.innov t (π (t + 1)) ω + S.innov t (i (t + 1)) ω / (1 - η) -
          cAR σ β κ η * S.innov t (i (t + 1)) ω * η / (1 - η) -
          (S.innov t (π (t + 1)) ω - cAR σ β κ η * S.innov t (i (t + 1)) ω) /
            (lam1 σ β κ - 1) := by
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have hμ0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr hl0.le
  have hμ1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hint := hf.1
  have hrea : ∀ j, ∀ᵐ ω ∂S.μ, S.innov t (reaM S i π (t + 1 + j)) ω =
      S.innov t (i (t + 1 + j)) ω - S.innov t (π (t + 1 + (j + 1))) ω := by
    intro j
    filter_upwards [innov_sub_ae S (hint (t + 1 + j)).1 (S.integrable_E _ _) t,
      innov_E_ae S (by omega : t + 1 ≤ t + 1 + j) (π (t + 1 + j + 1))] with ω a b
    simp only [reaM, Pi.sub_apply] at a b ⊢
    rw [a, b]
    rfl
  filter_upwards [eq_17_19_own_dating_ae S hv hiAR.1 hf t, ae_all_iff.mpr hrea,
    news_rate_ar1_ae S hiAR t, news_ar1_ae S ha hβ hη0 hη1 hD h hiAR hi hπ t]
    with ω h19 hR hrate hnπ htvc hs
  set ε := S.innov t (i (t + 1)) ω
  set δ := S.innov t (π (t + 1)) ω
  set c := cAR σ β κ η
  set μ := (lam1 σ β κ)⁻¹
  have hrr : ∀ j, (1 : ℝ) ^ j * S.innov t (reaM S i π (t + 1 + j)) ω =
      ε * η ^ j - (c * ε * η * η ^ j + (δ - c * ε) * μ * μ ^ j) := fun j => by
    rw [hR j, hrate j, hnπ (j + 1)]
    simp only [one_pow, one_mul, pow_succ]
    ring
  have g1 := hasSum_geometric_of_lt_one hη0 hη1
  have g2 := hasSum_geometric_of_lt_one hμ0 hμ1
  have hRs : HasSum (fun j => (1 : ℝ) ^ j * S.innov t (reaM S i π (t + 1 + j)) ω)
      (ε * (1 - η)⁻¹ - (c * ε * η * (1 - η)⁻¹ + (δ - c * ε) * μ * (1 - μ)⁻¹)) :=
    ((g1.mul_left ε).sub ((g1.mul_left (c * ε * η)).add
      (g2.mul_left ((δ - c * ε) * μ)))).congr_fun fun j => by rw [hrr j]
  have e := h19 htvc hs hRs.summable
  rw [hRs.tsum_eq] at e
  have h1 : 1 - η ≠ 0 := by linarith
  have h2 : lam1 σ β κ - 1 ≠ 0 := by linarith
  have h3 : 1 - μ = (lam1 σ β κ - 1) / lam1 σ β κ := by simp only [μ]; field_simp
  rw [h3] at e
  simp only [μ, c, ε, δ] at e ⊢
  field_simp at e ⊢
  linear_combination e

/-- Cochrane (2023), p. 414, on a probability space: a.s. the news about the reverse-engineered
disturbance `u = i − φπ` after an AR(1) rate shock is `εηʲ − φ(cεηʲ + (δ − cε)λ₁^{−j})`. -/
theorem news_u_ar1_ae {σ β κ η φ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hη0 : 0 ≤ η)
    (hη1 : η < 1) (hD : -β * η ^ 2 + (1 + β + σ * κ) * η - 1 ≠ 0) {i r x π : ℕ → Ω → ℝ}
    (h : ModelM S σ β κ i r x π) (hiAR : IsAR1M S η i) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M)
    (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ j, S.innov s (i (s + 1 + j) - φ • π (s + 1 + j)) ω =
      S.innov s (i (s + 1)) ω * η ^ j - φ * (cAR σ β κ η * S.innov s (i (s + 1)) ω * η ^ j +
        (S.innov s (π (s + 1)) ω - cAR σ β κ η * S.innov s (i (s + 1)) ω) *
          (lam1 σ β κ)⁻¹ ^ j) := by
  have hint := h.1
  have hsub : ∀ j, ∀ᵐ ω ∂S.μ, S.innov s (i (s + 1 + j) - φ • π (s + 1 + j)) ω =
      S.innov s (i (s + 1 + j)) ω - φ * S.innov s (π (s + 1 + j)) ω := by
    intro j
    filter_upwards [innov_sub_ae S (hint (s + 1 + j)).1 ((hint (s + 1 + j)).2.2.2.smul φ) s,
      innov_smul_ae S φ (π (s + 1 + j)) s] with ω a b
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b
    rw [a, b]
  filter_upwards [ae_all_iff.mpr hsub, news_rate_ar1_ae S hiAR s,
    news_ar1_ae S ha hβ hη0 hη1 hD h hiAR hi hπ s] with ω a b c j
  rw [a j, b j, c j]

/-- Cochrane (2023), Fig. 17.7 and p. 414 ("the reverse-engineered `u_t` … are not AR(1)"), on a
probability space, at the book's parameters (`σ = 1`, `β = 0.95`, `κ = 0.25`, `η = 0.6`,
`φ = 1.2`): almost surely, on the event `{ε ≠ 0, δ ≠ cε}` (`c = −125/11`), the news about the
reverse-engineered disturbance is not geometric in the horizon. -/
theorem fig17_7_news_u_not_geometric_ae {M Mπ : ℝ} {i r x π : ℕ → Ω → ℝ}
    (h : ModelM S 1 (19 / 20) (1 / 4) i r x π) (hiAR : IsAR1M S (3 / 5) i)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, S.innov s (i (s + 1)) ω ≠ 0 →
      S.innov s (π (s + 1)) ω ≠ -125 / 11 * S.innov s (i (s + 1)) ω →
      ¬ ∃ r : ℝ, ∀ j : ℕ,
        S.innov s (i (s + 1 + (j + 1)) - (6 / 5 : ℝ) • π (s + 1 + (j + 1))) ω =
          r * S.innov s (i (s + 1 + j) - (6 / 5 : ℝ) • π (s + 1 + j)) ω := by
  obtain ⟨-, -, hη0, hη1⟩ := fig17_7_params
  have hD : -(19 / 20 : ℝ) * (3 / 5) ^ 2 + (1 + 19 / 20 + 1 * (1 / 4)) * (3 / 5) - 1 ≠ 0 := by
    norm_num
  filter_upwards [news_u_ar1_ae S (φ := 6 / 5) (by norm_num) (by norm_num) hη0 hη1 hD h hiAR
    hi hπ s] with ω hu hε hδ
  have hp : S.innov s (π (s + 1)) ω / S.innov s (i (s + 1)) ω ≠ -125 / 11 :=
    fun e => hδ (by rw [← e]; field_simp)
  rintro ⟨r, hr⟩
  refine fig17_7_u_not_ar1 hp ⟨r, fun n => ?_⟩
  have e := hr n
  rw [hu (n + 1), hu n] at e
  simp only [piAR, fig17_7_c] at e ⊢
  apply mul_left_cancel₀ hε
  field_simp
  linear_combination 55 * e

end Cochrane.KeynesianStickyPrices.TidyR5StochasticFiscalMeasure
