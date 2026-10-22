/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR5StochasticPaths

/-!
# The fiscal requirements of Figures 17.6–17.7 under uncertainty

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4.1–17.4.2, eq. (17.19),
pp. 410–414, Figures 17.6 (`Δs`) and 17.7 (AR(1) rates, `Σs`, reverse-engineered disturbances).

FiscalUnderpinnings computed the surplus requirements under perfect foresight after the
shock, with pre-shock expectations at the steady state. Here they are the **news** about
surpluses required by the unexpected-inflation identity (17.19) in an equilibrium under an
arbitrary `ExpectationSystem`, combined with the news form of the equilibrium paths
(`TidyR5StochasticPaths.news_path`).

## Figure 17.6: `Δs` as surplus news

`surplus_news_rise`: if at date `t + 1` the news is a permanent rise of expected rates
(`ΔE_{t+1} i_{t+1+k} = 1`) and unexpected inflation is `δ = ΔE_{t+1} π_{t+1}`, then for bounded
processes and `0 ≤ ρ < 1` the surplus news is
`∑ ρʲ ΔE_{t+1} s̃_{t+1+j} = ρ(1 − δ)/(λ₁ − ρ) − δ`. The real-rate news enters with the factor
`ρ` of (17.19) in the dating of (17.16) (`FiscalUnderpinnings.eq_17_19_own_dating`).

**Correction to our earlier formalisation.** `FiscalUnderpinnings.deltaS` is
`−δ + ∑ ρʲ (1 − π_{j+1})`, i.e. (17.19) without that factor `ρ`; the two agree iff `ρ = 1` or
`δ = 1` (`surplus_news_eq_deltaS_iff`, `surplus_news_vs_deltaS`). Equilibrium B (`δ = 1`) still
needs `−1` (`surplus_news_B`), D (`δ = 0`) needs `ρ/(λ₁ − ρ)`, not `1/(λ₁ − ρ)`
(`surplus_news_D`), and C (`Δs = 0`) is `δ = ρ/λ₁`, not `1/(1 + λ₁ − ρ)`
(`surplus_news_zero_iff`). The corrected requirement is again affine in `δ` with slope
`−(1 + K)`, so the label inconsistency of Fig. 17.6 survives
(`fig17_6_inconsistent_corrected`).

## Figure 17.7: AR(1) rates

With AR(1) rates (`ExpectationSystem.IsAR1`), the rate news after a shock is
`ΔE_{s+1} i_{s+1+k} = ε ηᵏ` with `ε = i_{s+1} − η i_s` (`news_rate_ar1`), so the inflation news
is `c ε ηʲ + (δ − c ε) λ₁^{−j}` (`news_ar1`; Fig. 17.7 per unit shock, `FiscalUnderpinnings.piAR`).
With `ρ = 1` and the transversality condition and summability of surplus news that (17.19)
needs, the surplus news is the closed form of `FiscalUnderpinnings.sigmaS_closed` scaled by `ε`
(`surplus_news_ar1`), i.e. `ε Σs(δ/ε)` (`surplus_news_ar1_eq_sigmaS`); a unit shock gives exactly
the numbers of Fig. 17.7. The news about the reverse-engineered disturbance `u = i − φπ` is
`ε(ηʲ − φ piAR(δ/ε)_j)` (`news_u_ar1`), and at the book's parameters it is not geometric unless
`δ = c ε` (`fig17_7_news_u_not_geometric`): the stochastic disturbance process that delivers
AR(1) rates does not have AR(1) impulse responses.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5StochasticFiscal

open Filter Topology FullModel FiscalUnderpinnings TidyR5StochasticPaths

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Tools -/

/-- Cochrane (2023), p. 411: news about a later expectation is news about the variable,
`ΔE_{t+1} E_n y = ΔE_{t+1} y` for `n ≥ t + 1`. -/
theorem innov_E {t n : ℕ} (hn : t + 1 ≤ n) (y : Ω → ℝ) : innov 𝔼 t (𝔼.E n y) = innov 𝔼 t y := by
  unfold innov
  rw [𝔼.tower hn, 𝔼.tower (by omega : t ≤ n)]

/-- Cochrane (2023), eqs. (17.16) and (17.19): the news about the ex-ante real rate
`r_{t+1+j} = i_{t+1+j} − E_{t+1+j} π_{t+2+j}` is rate news minus inflation news. -/
theorem innov_rea {t : ℕ} (i π : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) :
    innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω =
      innov 𝔼 t (i (t + 1 + j)) ω - innov 𝔼 t (π (t + 1 + (j + 1))) ω := by
  unfold rea
  rw [innov_sub, innov_E 𝔼 (by omega)]
  rfl

/-- `ΔE_{t+1}` is homogeneous. -/
theorem innov_smul (t : ℕ) (c : ℝ) (y : Ω → ℝ) : innov 𝔼 t (c • y) = c • innov 𝔼 t y := by
  unfold innov
  rw [map_smul, map_smul, smul_sub]

/-! ### Figure 17.6: `Δs` as surplus news -/

/-- Cochrane (2023), Fig. 17.6, p. 410, and eq. (17.19), p. 411, under uncertainty: in an
equilibrium with bounded processes, the flow condition and `0 ≤ ρ < 1`, if the date-`(t+1)`
news is a permanent rise of expected rates, `ΔE_{t+1} i_{t+1+k} = 1`, the news about the
present value of surpluses is `ρ(1 − δ)/(λ₁ − ρ) − δ`, `δ = ΔE_{t+1} π_{t+1}`. -/
theorem surplus_news_rise {σ β κ ρ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {i r x π s v : ℕ → Ω → ℝ} (h : Model 𝔼 σ β κ 0 0 i r x π)
    (hv : 𝔼.Adapted v) (hia : 𝔼.Adapted i) (hf : Flow ρ i s v π) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hvb : ∀ t ω, |v t ω| ≤ M) (hib : ∀ t ω, |i t ω| ≤ M) (hπb : ∀ t ω, |π t ω| ≤ M)
    (t : ℕ) (ω : Ω) (hnews : ∀ k, innov 𝔼 t (i (t + 1 + k)) ω = 1) :
    ∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω =
      ρ * (1 - innov 𝔼 t (π (t + 1)) ω) / (lam1 σ β κ - ρ) - innov 𝔼 t (π (t + 1)) ω := by
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  set δ := innov 𝔼 t (π (t + 1)) ω
  have hp := (news_path 𝔼 ha hβ h hib hπb t ω).1
  have hn : (fun j => innov 𝔼 t (i (t + 1 + j)) ω) = stepI 0 := funext fun k => by
    rw [hnews k]; simp [stepI]
  rw [hn] at hp
  have hnπ : ∀ j, innov 𝔼 t (π (t + 1 + j)) ω = 1 + (δ - 1) * (lam1 σ β κ)⁻¹ ^ j := fun j => by
    have := congrFun hp j
    rw [this, path_step0 ha hβ]
  -- the real-rate news
  have hrr : ∀ j, ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω =
      (1 - δ) * (lam1 σ β κ)⁻¹ * (ρ * (lam1 σ β κ)⁻¹) ^ j := fun j => by
    rw [innov_rea, hnews j, hnπ (j + 1)]
    ring
  have hq0 : 0 ≤ ρ * (lam1 σ β κ)⁻¹ := mul_nonneg hρ0 (inv_nonneg.mpr hl0.le)
  have hq1 : ρ * (lam1 σ β κ)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hl0]; linarith
  have hR : HasSum (fun j => ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω)
      ((1 - δ) * (lam1 σ β κ)⁻¹ * (1 - ρ * (lam1 σ β κ)⁻¹)⁻¹) := by
    refine ((hasSum_geometric_of_lt_one hq0 hq1).mul_left ((1 - δ) * (lam1 σ β κ)⁻¹)).congr_fun
      fun j => ?_
    rw [hrr j]
  -- transversality and summability of surplus news from boundedness
  have hM : 0 ≤ M := (abs_nonneg _).trans (hsb 0 ω)
  have htvc : Tendsto (fun N => ρ ^ N * innov 𝔼 t (v (t + N)) ω) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N => ρ ^ N * (2 * M)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (2 * M)
    refine squeeze_zero_norm (fun N => ?_) hlim
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_left (abs_innov_le 𝔼 (hvb (t + N)) t ω) (pow_nonneg hρ0 N)
  have hs : Summable fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right (2 * M))
      (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_left (abs_innov_le 𝔼 (hsb _) t ω) (pow_nonneg hρ0 j)
  have e := eq_17_19_own_dating 𝔼 hv hia hf t ω htvc hs hR.summable
  rw [hR.tsum_eq] at e
  have hden : lam1 σ β κ - ρ ≠ 0 := by linarith
  have h1 : (1 - ρ * (lam1 σ β κ)⁻¹) = (lam1 σ β κ - ρ) / lam1 σ β κ := by field_simp
  rw [h1] at e
  simp only [δ] at e ⊢
  field_simp at e ⊢
  linear_combination e

/-- Cochrane (2023), Fig. 17.6: the surplus news of `surplus_news_rise` differs from
`FiscalUnderpinnings.deltaS` by `(1 − ρ)(1 − δ)/(λ₁ − ρ)` (the missing factor `ρ` on real-rate
news). -/
theorem surplus_news_vs_deltaS {σ β κ ρ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < lam1 σ β κ) (δ : ℝ) :
    ρ * (1 - δ) / (lam1 σ β κ - ρ) - δ =
      deltaS σ β κ ρ δ - (1 - ρ) * (1 - δ) / (lam1 σ β κ - ρ) := by
  rw [deltaS_closed ha hβ hρ0 hρ]
  have : lam1 σ β κ - ρ ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), Fig. 17.6 (correction to `FiscalUnderpinnings.deltaS`): the surplus news
required by (17.19) equals `deltaS δ` iff `ρ = 1` or `δ = 1`. -/
theorem surplus_news_eq_deltaS_iff {σ β κ ρ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < lam1 σ β κ) (δ : ℝ) :
    ρ * (1 - δ) / (lam1 σ β κ - ρ) - δ = deltaS σ β κ ρ δ ↔ ρ = 1 ∨ δ = 1 := by
  rw [surplus_news_vs_deltaS ha hβ hρ0 hρ]
  have hden : 0 < lam1 σ β κ - ρ := by linarith
  constructor
  · intro h
    have : (1 - ρ) * (1 - δ) / (lam1 σ β κ - ρ) = 0 := by linarith
    rcases mul_eq_zero.mp ((div_eq_zero_iff.mp this).resolve_right hden.ne') with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> simp [h]

/-- Cochrane (2023), Fig. 17.6, equilibrium B (`δ = 1`): surplus news `−1`, as in
`FiscalUnderpinnings.deltaS_B`. -/
theorem surplus_news_B (σ β κ ρ : ℝ) : ρ * (1 - 1) / (lam1 σ β κ - ρ) - 1 = -1 := by ring

/-- Cochrane (2023), Fig. 17.6, equilibrium D (`δ = 0`), corrected: surplus news
`ρ/(λ₁ − ρ) > 0` for `0 < ρ < λ₁`. -/
theorem surplus_news_D {σ β κ ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < lam1 σ β κ) :
    ρ * (1 - 0) / (lam1 σ β κ - ρ) - 0 = ρ / (lam1 σ β κ - ρ) ∧
      0 < ρ / (lam1 σ β κ - ρ) :=
  ⟨by ring, div_pos hρ0 (by linarith)⟩

/-- Cochrane (2023), Fig. 17.6, equilibrium C ("the `Δs = 0` equilibrium is not the equilibrium
with `δ₁ = 0` or with `ΔE₁ π₁ = 0`"), corrected: zero surplus news iff `δ = ρ/λ₁`. -/
theorem surplus_news_zero_iff {σ β κ ρ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β)
    (hρ : ρ < lam1 σ β κ) (δ : ℝ) :
    ρ * (1 - δ) / (lam1 σ β κ - ρ) - δ = 0 ↔ δ = ρ / lam1 σ β κ := by
  have hl0 : 0 < lam1 σ β κ := one_pos.trans (one_lt_lam1 ha hβ)
  have hden : lam1 σ β κ - ρ ≠ 0 := by linarith
  rw [sub_eq_zero, div_eq_iff hden, eq_div_iff hl0.ne']
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), Fig. 17.6, p. 410: the label inconsistency of
`FiscalUnderpinnings.fig17_6_inconsistent` holds for the corrected surplus news too (it is
affine, `K'(1 − δ) − δ` with `K' = ρ/(λ₁ − ρ)`): given the printed D and `δ = 0` values, the
jumps `±1` from the printed `δ = 0` point give `< −1.9` and `> 3.2`. -/
theorem fig17_6_inconsistent_corrected {σ β κ ρ p0 : ℝ}
    (hD : |(fun p => ρ * (1 - p) / (lam1 σ β κ - ρ) - p) 0 - 1.66| ≤ 0.005)
    (h0 : |(fun p => ρ * (1 - p) / (lam1 σ β κ - ρ) - p) p0 - 0.67| ≤ 0.005) :
    (fun p => ρ * (1 - p) / (lam1 σ β κ - ρ) - p) (p0 + 1) < -1.9 ∧
      3.2 < (fun p => ρ * (1 - p) / (lam1 σ β κ - ρ) - p) (p0 - 1) :=
  fig17_6_inconsistent (K := ρ / (lam1 σ β κ - ρ))
    (fun p => ρ * (1 - p) / (lam1 σ β κ - ρ) - p) (fun p => by ring) hD h0

/-! ### Figure 17.7: AR(1) rates -/

/-- Cochrane (2023), Fig. 17.7, p. 413, under uncertainty: with AR(1) rates
(`E_t i_{t+1} = η i_t`) the date-`(s+1)` rate news is `ε ηᵏ`, `ε = ΔE_{s+1} i_{s+1}`. -/
theorem news_rate_ar1 {η : ℝ} {i : ℕ → Ω → ℝ} (hiAR : 𝔼.IsAR1 η i) (s : ℕ) (ω : Ω) (k : ℕ) :
    innov 𝔼 s (i (s + 1 + k)) ω = innov 𝔼 s (i (s + 1)) ω * η ^ k := by
  unfold innov
  have e1 := 𝔼.ar1_iterate hiAR (s + 1) k
  have e2 := 𝔼.ar1_iterate hiAR s (k + 1)
  have e3 := 𝔼.ar1_iterate hiAR s 1
  rw [show s + (k + 1) = s + 1 + k by omega] at e2
  simp only [Pi.sub_apply]
  rw [e1, e2, e3, hiAR.1 (s + 1)]
  simp only [Pi.smul_apply, smul_eq_mul, pow_succ]
  ring

/-- Cochrane (2023), Fig. 17.7, p. 413, under uncertainty: with AR(1) rates (`0 ≤ η < 1`),
the inflation news after a rate shock `ε` with unexpected inflation `δ` is
`c ε ηʲ + (δ − c ε) λ₁^{−j}`, `c = σκ/(−βη² + (1 + β + σκ)η − 1)` — Fig. 17.7 per unit shock. -/
theorem news_ar1 {σ β κ η M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hD : -β * η ^ 2 + (1 + β + σ * κ) * η - 1 ≠ 0) {i r x π : ℕ → Ω → ℝ}
    (h : Model 𝔼 σ β κ 0 0 i r x π) (hiAR : 𝔼.IsAR1 η i) (hi : ∀ t ω, |i t ω| ≤ M)
    (hπ : ∀ t ω, |π t ω| ≤ Mπ) (s : ℕ) (ω : Ω) (j : ℕ) :
    innov 𝔼 s (π (s + 1 + j)) ω =
      cAR σ β κ η * innov 𝔼 s (i (s + 1)) ω * η ^ j +
        (innov 𝔼 s (π (s + 1)) ω - cAR σ β κ η * innov 𝔼 s (i (s + 1)) ω) *
          (lam1 σ β κ)⁻¹ ^ j := by
  set ε := innov 𝔼 s (i (s + 1)) ω
  set δ := innov 𝔼 s (π (s + 1)) ω
  have hp := (news_path 𝔼 ha hβ h hi hπ s ω).1
  have hn : (fun k => innov 𝔼 s (i (s + 1 + k)) ω) = fun k => ε * η ^ k :=
    funext fun k => news_rate_ar1 𝔼 hiAR s ω k
  rw [hn] at hp
  have e := congrFun hp j
  rw [e]
  have h1 := path_sub_path σ β κ (fun k => ε * η ^ k) δ (ε * cAR σ β κ η) j
  have h2 := path_smul σ β κ ε (fun k => η ^ k) (cAR σ β κ η) j
  rw [← piAR_eq_path ha hβ hη0 hη1 hD] at h2
  simp only [piAR, sub_self, zero_mul, add_zero] at h2
  linear_combination h1 + h2

/-- Cochrane (2023), Fig. 17.7 and p. 412, under uncertainty: with AR(1) rates, `ρ = 1`, the
flow condition, the transversality condition and summable surplus news (the hypotheses of
(17.19), `FiscalUnderpinnings.eq_17_19_own_dating`), the surplus news after a rate shock `ε`
with unexpected inflation `δ` is
`−δ + ε/(1 − η) − c ε η/(1 − η) − (δ − c ε)/(λ₁ − 1)`. -/
theorem surplus_news_ar1 {σ β κ η M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hη0 : 0 ≤ η)
    (hη1 : η < 1) (hD : -β * η ^ 2 + (1 + β + σ * κ) * η - 1 ≠ 0)
    {i r x π s v : ℕ → Ω → ℝ} (h : Model 𝔼 σ β κ 0 0 i r x π) (hiAR : 𝔼.IsAR1 η i)
    (hi : ∀ t ω, |i t ω| ≤ M) (hπ : ∀ t ω, |π t ω| ≤ Mπ) (hv : 𝔼.Adapted v)
    (hf : Flow 1 i s v π) (t : ℕ) (ω : Ω)
    (htvc : Tendsto (fun N => (1 : ℝ) ^ N * innov 𝔼 t (v (t + N)) ω) atTop (𝓝 0))
    (hs : Summable fun j => (1 : ℝ) ^ j * innov 𝔼 t (s (t + 1 + j)) ω) :
    ∑' j, (1 : ℝ) ^ j * innov 𝔼 t (s (t + 1 + j)) ω =
      -innov 𝔼 t (π (t + 1)) ω + innov 𝔼 t (i (t + 1)) ω / (1 - η) -
        cAR σ β κ η * innov 𝔼 t (i (t + 1)) ω * η / (1 - η) -
        (innov 𝔼 t (π (t + 1)) ω - cAR σ β κ η * innov 𝔼 t (i (t + 1)) ω) /
          (lam1 σ β κ - 1) := by
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have hμ0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr hl0.le
  have hμ1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  set ε := innov 𝔼 t (i (t + 1)) ω
  set δ := innov 𝔼 t (π (t + 1)) ω
  set c := cAR σ β κ η
  set μ := (lam1 σ β κ)⁻¹
  have hrr : ∀ j, (1 : ℝ) ^ j * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω =
      ε * η ^ j - (c * ε * η * η ^ j + (δ - c * ε) * μ * μ ^ j) := fun j => by
    rw [innov_rea, news_rate_ar1 𝔼 hiAR t ω j,
      news_ar1 𝔼 ha hβ hη0 hη1 hD h hiAR hi hπ t ω (j + 1)]
    simp only [one_pow, one_mul, pow_succ]
    ring
  have g1 := hasSum_geometric_of_lt_one hη0 hη1
  have g2 := hasSum_geometric_of_lt_one hμ0 hμ1
  have hR : HasSum (fun j => (1 : ℝ) ^ j * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω)
      (ε * (1 - η)⁻¹ - (c * ε * η * (1 - η)⁻¹ + (δ - c * ε) * μ * (1 - μ)⁻¹)) := by
    refine ((g1.mul_left ε).sub ((g1.mul_left (c * ε * η)).add
      (g2.mul_left ((δ - c * ε) * μ)))).congr_fun fun j => ?_
    rw [hrr j]
  have e := eq_17_19_own_dating 𝔼 hv hiAR.1 hf t ω htvc hs hR.summable
  rw [hR.tsum_eq] at e
  have h1 : 1 - η ≠ 0 := by linarith
  have h2 : lam1 σ β κ - 1 ≠ 0 := by linarith
  have h3 : 1 - μ = (lam1 σ β κ - 1) / lam1 σ β κ := by simp only [μ]; field_simp
  rw [h3] at e
  simp only [μ, c, ε, δ] at e ⊢
  field_simp at e ⊢
  linear_combination e

/-- Cochrane (2023), Fig. 17.7, p. 413: for a nonzero rate shock `ε` the surplus news of
`surplus_news_ar1` is `ε Σs(δ/ε)` (`FiscalUnderpinnings.sigmaS`); a unit shock (`ε = 1`)
requires exactly the `Σs` of Fig. 17.7 (`FiscalUnderpinnings.fig17_7_values`). -/
theorem surplus_news_ar1_eq_sigmaS {σ β κ η : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hη0 : 0 ≤ η)
    (hη1 : η < 1) {ε : ℝ} (hε : ε ≠ 0) (δ : ℝ) :
    -δ + ε / (1 - η) - cAR σ β κ η * ε * η / (1 - η) -
        (δ - cAR σ β κ η * ε) / (lam1 σ β κ - 1) = ε * sigmaS σ β κ η (δ / ε) := by
  rw [sigmaS_closed ha hβ hη0 hη1]
  have h1 : 1 - η ≠ 0 := by linarith
  have h2 : lam1 σ β κ - 1 ≠ 0 := by linarith [one_lt_lam1 ha hβ]
  field_simp

/-- Cochrane (2023), p. 414, under uncertainty: the news about the reverse-engineered
disturbance `u = i − φπ` after an AR(1) rate shock is `ε ηʲ − φ (c ε ηʲ + (δ − c ε) λ₁^{−j})`. -/
theorem news_u_ar1 {σ β κ η φ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hη0 : 0 ≤ η)
    (hη1 : η < 1) (hD : -β * η ^ 2 + (1 + β + σ * κ) * η - 1 ≠ 0) {i r x π : ℕ → Ω → ℝ}
    (h : Model 𝔼 σ β κ 0 0 i r x π) (hiAR : 𝔼.IsAR1 η i) (hi : ∀ t ω, |i t ω| ≤ M)
    (hπ : ∀ t ω, |π t ω| ≤ Mπ) (s : ℕ) (ω : Ω) (j : ℕ) :
    innov 𝔼 s (i (s + 1 + j) - φ • π (s + 1 + j)) ω =
      innov 𝔼 s (i (s + 1)) ω * η ^ j - φ * (cAR σ β κ η * innov 𝔼 s (i (s + 1)) ω * η ^ j +
        (innov 𝔼 s (π (s + 1)) ω - cAR σ β κ η * innov 𝔼 s (i (s + 1)) ω) *
          (lam1 σ β κ)⁻¹ ^ j) := by
  rw [innov_sub, innov_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    news_rate_ar1 𝔼 hiAR s ω j, news_ar1 𝔼 ha hβ hη0 hη1 hD h hiAR hi hπ s ω j]

/-- Cochrane (2023), Fig. 17.7 and p. 414 ("the reverse-engineered `u_t` … are not AR(1)"),
under uncertainty, at the book's parameters (`σ = 1`, `β = 0.95`, `κ = 0.25`, `η = 0.6`,
`φ = 1.2`): after a nonzero rate shock `ε` with unexpected inflation `δ ≠ c ε`
(`c = −125/11`), the news about the reverse-engineered disturbance is not geometric in the
horizon. -/
theorem fig17_7_news_u_not_geometric {M Mπ : ℝ} {i r x π : ℕ → Ω → ℝ}
    (h : Model 𝔼 1 (19 / 20) (1 / 4) 0 0 i r x π) (hiAR : 𝔼.IsAR1 (3 / 5) i)
    (hi : ∀ t ω, |i t ω| ≤ M) (hπ : ∀ t ω, |π t ω| ≤ Mπ) (s : ℕ) (ω : Ω)
    (hε : innov 𝔼 s (i (s + 1)) ω ≠ 0)
    (hδ : innov 𝔼 s (π (s + 1)) ω ≠ -125 / 11 * innov 𝔼 s (i (s + 1)) ω) :
    ¬ ∃ r : ℝ, ∀ j : ℕ, innov 𝔼 s (i (s + 1 + (j + 1)) - (6 / 5 : ℝ) • π (s + 1 + (j + 1))) ω =
      r * innov 𝔼 s (i (s + 1 + j) - (6 / 5 : ℝ) • π (s + 1 + j)) ω := by
  obtain ⟨-, -, hη0, hη1⟩ := fig17_7_params
  have hD : -(19 / 20 : ℝ) * (3 / 5) ^ 2 + (1 + 19 / 20 + 1 * (1 / 4)) * (3 / 5) - 1 ≠ 0 := by
    norm_num
  have hp : innov 𝔼 s (π (s + 1)) ω / innov 𝔼 s (i (s + 1)) ω ≠ -125 / 11 :=
    fun e => hδ (by rw [← e]; field_simp)
  rintro ⟨r, hr⟩
  refine fig17_7_u_not_ar1 hp ⟨r, fun n => ?_⟩
  have e := hr n
  rw [news_u_ar1 𝔼 (by norm_num) (by norm_num) hη0 hη1 hD h hiAR hi hπ s ω (n + 1),
    news_u_ar1 𝔼 (by norm_num) (by norm_num) hη0 hη1 hD h hiAR hi hπ s ω n] at e
  simp only [piAR, fig17_7_c] at e ⊢
  apply mul_left_cancel₀ hε
  field_simp
  linear_combination 55 * e

end Cochrane.KeynesianStickyPrices.TidyR5StochasticFiscal
