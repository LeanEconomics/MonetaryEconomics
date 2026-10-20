/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.VARIdentities
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Invertibility: why a VAR without the value of debt cannot recover the surplus process

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, p. 102, and Online
Appendix Chapter 2, §§2.1.1–2.1.6, eqs. (2.1)–(2.21), pp. 594–602.

A government that repays its debts runs a surplus process `s_t = a(L)ε_t` with `a(ρ) = 0`; the
moving average then has a root inside the unit circle and cannot be recovered from the history of
surpluses (an autoregression recovers the invertible "Wold" representation, with the root
flipped from `ρ⁻¹` to `ρ`), while a VAR that includes the value of debt recovers it.

## Main definitions

* `gen a z = ∑ aⱼ zʲ` (the book's `a(z)`, and `a(ρ)`; from `Innovations`); `genFnC` its complex
  version. Shocks are `Innovations.IsMDSNat` martingale differences.
* `armaCoeff φ θ`: the MA coefficients of `(1 − θL)/(1 − φL)` (MA(1) when `φ = 0`).
* `autocov a σ² k = σ² ∑ aⱼ a_{j+k}`: autocovariances of an MA(∞) process.
* `Recoverable a`: the structural shock is an absolutely summable filter of current and past
  surpluses (`ε_t = ∑ b_k s_{t−k}`, `b * a = δ`).
* `maSeries`, `hsCoeff`: an MA process started from a zero pre-sample, and the Hansen–Sargent
  coefficients `c_k = ∑ⱼ ρʲ a_{k+1+j}`.
* Hilbert-space layer: `WhiteNoise e σ²` (orthogonal, equal variances, `ℤ`-indexed), `maProc a e`
  (the MA(∞) process `∑ a_k e_{t−k}`), `pastSpan s t` (the closed span of `s_t, s_{t−1}, …`),
  `woldInnov θ m` (`w_t = ∑ θ⁻ᵏ m_{t−k}`).

## Main results

* Autocovariance flip (p. 102, (2.13), (2.4)–(2.5), survey E12): `arma11_autocov_flip` — the
  ARMA(1,1) with MA root `θ` and innovation variance `σ²` has exactly the same autocovariances as
  the one with root `θ⁻¹` and variance `θ²σ²`; `ma1_autocov_flip` (`φ = 0`); `blaschke_norm`,
  `spectral_density_flip`.
* Non-invertibility (pp. 597, 600): `genFnC_ne_zero_of_recoverable` (a recoverable MA has no zero
  in the closed unit disc), `not_recoverable_of_aRho_eq_zero` (`a(ρ) = 0`, `|ρ| ≤ 1` ⇒ not
  recoverable); `ma1_formal_inverse`, `ma1_inverse_not_summable` (2.12).
* ARMA(1,1) of (2.1)–(2.8): `debt_ar1` (2.7), `arma11_time_domain` and `arma11_revision` (2.3),
  `arma11_aRho_params` (`a(ρ) = β_s`), `arma11_iid_of_one`, `arma11_noninvertible_iff` (the root
  lies inside the disc iff `β_s < (1 − ρ)/α` or `β_s > (1 + ρ)/α`), `arma11_wold_aRho` (fitted
  `a(ρ) = (1 − ρ²)/α`), `debt_var_tr_det`, `debt_var_stable`, `shock_from_debt` (2.6)–(2.8).
* MA(1) examples: `ma1_pv_forward`, `ma1_value_reveals_shock` (p. 102), `ma1_debt_value` (2.9),
  `ma1_no_inflation_iff`, `ma1_repaying_debt_value` (2.10)–(2.11), `printed_2_11_wrong` (E13),
  `ma1_fitted_pv_innov` (2.13), `ma1_debt_var` (2.14)–(2.16).
* Hansen–Sargent: `ma_forecast`, `hansenSargent`, `hansenSargent_E_tsum` (2.19) and
  `hansenSargent_genFn` (`∑ c_k zᵏ = (a(z) − a(ρ))/(z − ρ)`); `value_expost_of_aRho_zero` (2.18:
  with `a(ρ) = 0` the ex-post present value equals the ex-ante one); `factor_value` (2.20)–(2.21)
  and `factor_of_aRho_zero` (2.17: `a(ρ) = 0` iff `a(L)` has the factor `1 − ρ⁻¹L`).
* Hilbert-space Wold statements: `not_mem_pastSpan_of_aRho_eq_zero` — for any MA(∞) with
  `a(ρ) = 0`, `|ρ| < 1`, the structural shock `e_t` is not in the closed linear span of current and
  past surpluses (no linear procedure on the surplus history recovers it); `wold_innovation` — for
  a process whose MA polynomial has the root `θ⁻¹` (`|θ| > 1`) and which is an AR filter of
  `m_t = e_t − θe_{t−1}`, `w_t = ∑ θ⁻ᵏ m_{t−k}` is its Wold innovation: `w_t ⟂` the past,
  `s_t − w_t` in the past (so it is the orthogonal projection of `s_t` on the past), `w` is white
  noise with variance `θ²σ²`, and `m_t = w_t − θ⁻¹w_{t−1}` — the fitted MA root is `θ⁻¹ = ρ`;
  instances `ma1_wold` (p. 102, (2.13)) and `arma11_wold` ((2.4)–(2.5)).
-/

namespace Cochrane.DebtDeficitsInflation.Invertibility

open Filter Topology VARIdentities
open Cochrane.DebtDeficitsInflation.Innovations (gen IsMDSNat innov innov_apply)
open scoped Matrix

variable {Ω : Type*}

/-! ### Generating functions and ARMA(1,1) coefficients -/

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595: the moving-average coefficients of
`(1 − θL)/(1 − φL)`: `a₀ = 1`, `a_{k+1} = (φ − θ)φᵏ` (an MA(1) `1 − θL` when `φ = 0`). -/
def armaCoeff (φ θ : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (φ - θ) * φ ^ k

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595: `a(z) = (1 − θz)/(1 − φz)` for
`|φz| < 1`. -/
theorem armaCoeff_hasSum {φ θ z : ℝ} (h : |φ * z| < 1) :
    HasSum (fun j => armaCoeff φ θ j * z ^ j) ((1 - θ * z) / (1 - φ * z)) := by
  have hne : 1 - φ * z ≠ 0 := by
    intro h0
    have : φ * z = 1 := by linarith
    rw [this, abs_one] at h
    exact lt_irrefl _ h
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, armaCoeff, pow_zero, mul_one]
  have hg := (hasSum_geometric_of_abs_lt_one h).mul_left ((φ - θ) * z)
  convert hg using 1
  · funext k
    simp only [pow_succ, mul_pow]
    ring
  · rw [div_sub_one hne, div_eq_mul_inv]
    ring

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595: `a(z) = (1 − θz)/(1 − φz)`. -/
theorem genFn_armaCoeff {φ θ z : ℝ} (h : |φ * z| < 1) :
    gen (armaCoeff φ θ) z = (1 - θ * z) / (1 - φ * z) :=
  (armaCoeff_hasSum h).tsum_eq

/-- Cochrane (2023), Online Appendix p. 595: the ARMA(1,1) coefficients are absolutely summable
when `|φ| < 1`. -/
theorem summable_abs_armaCoeff {φ : ℝ} (hφ : |φ| < 1) (θ : ℝ) :
    Summable (fun k => |armaCoeff φ θ k|) := by
  rw [← summable_nat_add_iff 1]
  have := (summable_geometric_of_lt_one (abs_nonneg φ) hφ).mul_left |φ - θ|
  refine this.congr fun k => ?_
  simp [armaCoeff, abs_mul, abs_pow]

/-- Cochrane (2023), eq. (4.1), p. 87: the autocovariances `γ_k = σ² ∑ⱼ aⱼ a_{j+k}` of an MA(∞)
process with innovation variance `σ²`. -/
noncomputable def autocov (a : ℕ → ℝ) (σ2 : ℝ) (k : ℕ) : ℝ := σ2 * ∑' j, a j * a (j + k)

/-- Cochrane (2023), Online Appendix eqs. (2.4)–(2.5), p. 597: the autocovariances of the
ARMA(1,1) `(1 − θL)/(1 − φL)`, `|φ| < 1`: `γ_k = σ²[a_k + (φ − θ)²φᵏ/(1 − φ²)]`. -/
theorem arma11_autocov {φ : ℝ} (hφ : |φ| < 1) (θ σ2 : ℝ) (k : ℕ) :
    autocov (armaCoeff φ θ) σ2 k =
      σ2 * (armaCoeff φ θ k + (φ - θ) ^ 2 * φ ^ k / (1 - φ ^ 2)) := by
  have hφ2 : |φ ^ 2| < 1 := by
    rw [abs_pow]; nlinarith [abs_nonneg φ]
  have h : HasSum (fun j => armaCoeff φ θ j * armaCoeff φ θ (j + k))
      (armaCoeff φ θ k + (φ - θ) ^ 2 * φ ^ k / (1 - φ ^ 2)) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, armaCoeff, one_mul, zero_add,
      add_sub_cancel_left]
    have hg := (hasSum_geometric_of_abs_lt_one hφ2).mul_left ((φ - θ) ^ 2 * φ ^ k)
    rw [show (φ - θ) ^ 2 * φ ^ k / (1 - φ ^ 2) = (φ - θ) ^ 2 * φ ^ k * (1 - φ ^ 2)⁻¹ by
      rw [div_eq_mul_inv]]
    refine hg.congr_fun fun j => ?_
    rw [show j + 1 + k = (j + k) + 1 by omega]
    simp only
    ring
  rw [autocov, h.tsum_eq]

/-- Cochrane (2023), Online Appendix eqs. (2.4)–(2.5), p. 597, and survey E12 (the spectral
densities agree only after rescaling the innovation variance): the ARMA(1,1) with MA root `θ` and
innovation variance `σ²` has the same autocovariances at every lag as the one with root `θ⁻¹`
and variance `θ²σ²`. Second moments cannot tell them apart. -/
theorem arma11_autocov_flip {φ θ : ℝ} (hφ : |φ| < 1) (hθ : θ ≠ 0) (σ2 : ℝ) (k : ℕ) :
    autocov (armaCoeff φ θ) σ2 k = autocov (armaCoeff φ θ⁻¹) (θ ^ 2 * σ2) k := by
  have hφ2 : 1 - φ ^ 2 ≠ 0 := by
    have : φ ^ 2 < 1 := by nlinarith [abs_nonneg φ, sq_abs φ]
    linarith
  rw [arma11_autocov hφ, arma11_autocov hφ]
  cases k with
  | zero =>
    simp only [armaCoeff, pow_zero, mul_one]
    field_simp
    ring
  | succ k =>
    simp only [armaCoeff]
    field_simp
    ring

/-- Cochrane (2023), p. 102, and Online Appendix (2.13), p. 599: the MA(1) `s_t = ε_t − θε_{t−1}`
has autocovariances `(1 + θ²)σ²`, `−θσ²` and zero beyond lag one. -/
theorem ma1_autocov (θ σ2 : ℝ) :
    autocov (armaCoeff 0 θ) σ2 0 = (1 + θ ^ 2) * σ2 ∧
    autocov (armaCoeff 0 θ) σ2 1 = -θ * σ2 ∧
    ∀ k, autocov (armaCoeff 0 θ) σ2 (k + 2) = 0 := by
  have h0 : |(0 : ℝ)| < 1 := by simp
  refine ⟨?_, ?_, fun k => ?_⟩
  · rw [arma11_autocov h0]; simp [armaCoeff]; ring
  · rw [arma11_autocov h0]; simp [armaCoeff]; ring
  · rw [arma11_autocov h0]; simp [armaCoeff]

/-- Cochrane (2023), p. 102 ("an autoregression will estimate `s̃_t = u_t − θu_{t−1}` with
`θ = ρ`"), and Online Appendix (2.13), p. 599: the MA(1) with root `θ` and variance `σ²` and the
MA(1) with root `θ⁻¹` and variance `θ²σ²` have identical autocovariances. -/
theorem ma1_autocov_flip {θ : ℝ} (hθ : θ ≠ 0) (σ2 : ℝ) (k : ℕ) :
    autocov (armaCoeff 0 θ) σ2 k = autocov (armaCoeff 0 θ⁻¹) (θ ^ 2 * σ2) k :=
  arma11_autocov_flip (by simp) hθ σ2 k

/-- Cochrane (2023), Online Appendix p. 597 (the spectral density `S(ω) = a(e^{iω})a(e^{−iω})`):
the Blaschke identity — on the unit circle `|1 − ρ⁻¹z| = |ρ|⁻¹ |1 − ρz|`. -/
theorem blaschke_norm {ρ : ℝ} (hρ : ρ ≠ 0) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖1 - (ρ : ℂ)⁻¹ * z‖ = |ρ|⁻¹ * ‖1 - (ρ : ℂ) * z‖ := by
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  have h1 : 1 - (ρ : ℂ)⁻¹ * z = (ρ : ℂ)⁻¹ * ((ρ : ℂ) - z) := by
    field_simp
  have hzc : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  have h2 : 1 - (ρ : ℂ) * z = -(z * ((starRingEnd ℂ) ((ρ : ℂ) - z))) := by
    rw [map_sub, Complex.conj_ofReal, mul_sub, hzc]
    ring
  rw [h1, h2, norm_neg, norm_mul, norm_mul, hz, one_mul, Complex.norm_conj, norm_inv,
    Complex.norm_real, Real.norm_eq_abs]

/-- Cochrane (2023), Online Appendix p. 597 and survey E12: the spectral density of the
non-invertible numerator `1 − ρ⁻¹L` with innovation variance `σ²` equals that of the invertible
numerator `1 − ρL` with variance `σ²/ρ²`, at every frequency (`|z| = 1`). -/
theorem spectral_density_flip {ρ : ℝ} (hρ : ρ ≠ 0) {z : ℂ} (hz : ‖z‖ = 1) (σ2 : ℝ) :
    ‖1 - (ρ : ℂ)⁻¹ * z‖ ^ 2 * σ2 = ‖1 - (ρ : ℂ) * z‖ ^ 2 * (σ2 / ρ ^ 2) := by
  rw [blaschke_norm hρ hz, mul_pow, inv_pow, sq_abs]
  field_simp

/-! ### Recoverability and the zeros of `a(z)` -/

/-- Cochrane (2023), p. 102 ("the shock `ε_t` is a function of current and future surpluses, not
current and past surpluses") and Online Appendix p. 600: the structural shock is recoverable
from current and past surpluses by an absolutely summable filter `ε_t = ∑ b_k s_{t−k}`, i.e.
`b * a = δ` (Cauchy product). -/
def Recoverable (a : ℕ → ℝ) : Prop :=
  ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
    ∀ n, ∑ k ∈ Finset.range (n + 1), b k * a (n - k) = if n = 0 then 1 else 0

/-- Cochrane (2023), Online Appendix p. 597 ("all zeros of the moving-average representation are
outside the unit circle"): the complex generating function `a(z) = ∑ aⱼ zʲ`. -/
noncomputable def genFnC (a : ℕ → ℝ) (z : ℂ) : ℂ := ∑' j, (a j : ℂ) * z ^ j

/-- Cochrane (2023), Online Appendix p. 597: at a real point the complex generating function is
the real one. -/
theorem genFnC_ofReal (a : ℕ → ℝ) (ρ : ℝ) : genFnC a (ρ : ℂ) = (gen a ρ : ℂ) := by
  rw [genFnC, gen, Complex.ofReal_tsum]
  push_cast
  rfl

/-- Cochrane (2023), Online Appendix pp. 597, 600 ("the condition for a moving-average
representation to correspond to an autoregression is that all the zeros of `a(z)` lie outside
the unit circle"): if the shock is recoverable from current and past surpluses, `a(z) ≠ 0` on
the closed unit disc. -/
theorem genFnC_ne_zero_of_recoverable {a : ℕ → ℝ} (ha : Summable (fun j => |a j|))
    (hrec : Recoverable a) {z : ℂ} (hz : ‖z‖ ≤ 1) : genFnC a z ≠ 0 := by
  obtain ⟨b, hb, hconv⟩ := hrec
  have hzn : ∀ n : ℕ, ‖z ^ n‖ ≤ 1 := fun n => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
  have hf : Summable (fun n => ‖(b n : ℂ) * z ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (hzn n)) hb
  have hg : Summable (fun n => ‖(a n : ℂ) * z ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (hzn n)) ha
  have hprod := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg
  have hinner : ∀ n, ∑ k ∈ Finset.range (n + 1), (b k : ℂ) * z ^ k * ((a (n - k) : ℂ) *
      z ^ (n - k)) = if n = 0 then 1 else 0 := by
    intro n
    have : ∑ k ∈ Finset.range (n + 1), (b k : ℂ) * z ^ k * ((a (n - k) : ℂ) * z ^ (n - k)) =
        z ^ n * ((∑ k ∈ Finset.range (n + 1), b k * a (n - k) : ℝ) : ℂ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have : z ^ n = z ^ k * z ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
      rw [this]
      ring
    rw [this, hconv n]
    split_ifs with h
    · subst h; simp
    · simp
  simp only [hinner] at hprod
  rw [tsum_ite_eq] at hprod
  intro h0
  rw [genFnC] at h0
  rw [h0, mul_zero] at hprod
  exact zero_ne_one hprod

/-- Cochrane (2023), Online Appendix p. 600: a zero of `a(z)` in the closed unit disc makes the
structural shock unrecoverable from current and past surpluses. -/
theorem not_recoverable_of_root {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (h0 : genFnC a z = 0) : ¬ Recoverable a :=
  fun hrec => genFnC_ne_zero_of_recoverable ha hrec hz h0

/-- Cochrane (2023), p. 102, and Online Appendix p. 597 ("a government that pays back its debts
runs a surplus process with `a(ρ) = 0`, `ρ ≤ 1` … so the moving-average representation … must
be non-invertible") and p. 600: if `a(ρ) = 0` with `|ρ| ≤ 1`, the structural shock cannot be
recovered from current and past surpluses by any absolutely summable filter. -/
theorem not_recoverable_of_aRho_eq_zero {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ}
    (hρ : |ρ| ≤ 1) (h0 : gen a ρ = 0) : ¬ Recoverable a := by
  refine not_recoverable_of_root ha (z := (ρ : ℂ)) ?_ ?_
  · rw [Complex.norm_real, Real.norm_eq_abs]; exact hρ
  · rw [genFnC_ofReal, h0, Complex.ofReal_zero]

/-! ### The MA(1) and ARMA(1,1) examples -/

/-- Cochrane (2023), p. 88 and p. 102: for the MA(1) `s_t = ε_t − θε_{t−1}`, `a(ρ) = 1 − θρ`. -/
theorem ma1_aRho (θ ρ : ℝ) : gen (armaCoeff 0 θ) ρ = 1 - θ * ρ := by
  rw [genFn_armaCoeff (by simp)]
  simp

/-- Cochrane (2023), p. 102: the MA(1) repays its debt, `a(ρ) = 0`, exactly when `θ = ρ⁻¹`. -/
theorem ma1_aRho_eq_zero_iff {θ ρ : ℝ} (hρ : ρ ≠ 0) : gen (armaCoeff 0 θ) ρ = 0 ↔ θ = ρ⁻¹ := by
  rw [ma1_aRho]
  constructor
  · intro h
    field_simp
    linarith
  · rintro rfl
    field_simp
    ring

/-- Cochrane (2023), p. 102 ("with only `θ < 1`, and thus `a(ρ) > 1 − ρ`, the moving average is
technically invertible"): for `0 ≤ θ < 1` and `ρ > 0`, `a(ρ) = 1 − θρ > 1 − ρ`. -/
theorem ma1_aRho_gt {θ ρ : ℝ} (hθ1 : θ < 1) (hρ : 0 < ρ) :
    1 - ρ < gen (armaCoeff 0 θ) ρ := by
  rw [ma1_aRho]
  nlinarith

/-- Cochrane (2023), p. 102 ("you will falsely estimate `a(ρ) = 1 − ρ² ≠ 0`"): the fitted
(flipped-root) MA(1) has `a(ρ) = 1 − ρ²`, nonzero for `|ρ| < 1`. -/
theorem ma1_fitted_aRho {ρ : ℝ} (hρ : |ρ| < 1) :
    gen (armaCoeff 0 ρ) ρ = 1 - ρ ^ 2 ∧ gen (armaCoeff 0 ρ) ρ ≠ 0 := by
  rw [ma1_aRho]
  refine ⟨by ring, ?_⟩
  have : ρ ^ 2 < 1 := by nlinarith [abs_nonneg ρ, sq_abs ρ]
  nlinarith

/-- Cochrane (2023), Online Appendix eq. (2.12), p. 598: the only formal inverse of `1 − RL` is
`∑ Rᵏ Lᵏ` — if `b * (1 − RL) = δ` then `b_k = Rᵏ`. -/
theorem ma1_formal_inverse {R : ℝ} {b : ℕ → ℝ}
    (hb : ∀ n, ∑ k ∈ Finset.range (n + 1), b k * armaCoeff 0 R (n - k) =
      if n = 0 then 1 else 0) : ∀ k, b k = R ^ k := by
  have h0 : b 0 = 1 := by simpa [armaCoeff] using hb 0
  have hstep : ∀ k, b (k + 1) = R * b k := by
    intro k
    have h := hb (k + 1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
    have hz : ∑ x ∈ Finset.range k, b x * armaCoeff 0 R (k + 1 - x) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hxk : x < k := Finset.mem_range.mp hx
      rw [show k + 1 - x = (k - 1 - x + 1) + 1 by omega]
      simp [armaCoeff]
    rw [hz, show k + 1 - k = 0 + 1 by omega, Nat.sub_self] at h
    simp only [armaCoeff, pow_zero, mul_one, zero_add, zero_sub, Nat.add_one_ne_zero,
      ↓reduceIte] at h
    linarith
  intro k
  induction k with
  | zero => simp [h0]
  | succ k ih => rw [hstep k, ih, pow_succ, mul_comm]

/-- Cochrane (2023), Online Appendix eq. (2.12), p. 598 ("we see exploding coefficients"): for
`|R| ≥ 1` the inverse coefficients `Rᵏ` are not summable, and `1 − RL` is not recoverable. -/
theorem ma1_inverse_not_summable {R : ℝ} (hR : 1 ≤ |R|) :
    ¬ Summable (fun k => |R ^ k|) ∧ ¬ Recoverable (armaCoeff 0 R) := by
  constructor
  · intro h
    have := h.tendsto_atTop_zero
    have hge : ∀ k : ℕ, 1 ≤ |R ^ k| := fun k => by rw [abs_pow]; exact one_le_pow₀ hR
    have hev := this.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    obtain ⟨k, hk⟩ := hev.exists
    linarith [hge k]
  · have hR0 : R ≠ 0 := by
      intro h; rw [h, abs_zero] at hR; linarith
    refine not_recoverable_of_aRho_eq_zero (ρ := R⁻¹) (summable_abs_armaCoeff (by simp) R) ?_ ?_
    · rw [abs_inv]; exact inv_le_one_of_one_le₀ hR
    · rw [ma1_aRho, mul_inv_cancel₀ hR0, sub_self]

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595: with `φ = (1 − α)/ρ`,
`θ = (1 − αβ_s)/ρ` (`ρ ≠ 0`, `0 < α < 2` so that `|φρ| < 1`), `a(ρ) = β_s` — "β_s controls how
much of a shock is repaid, and how much results in inflation". -/
theorem arma11_aRho_params {ρ α βs : ℝ} (hρ : ρ ≠ 0) (hα0 : 0 < α) (hα2 : α < 2) :
    gen (armaCoeff ((1 - α) / ρ) ((1 - α * βs) / ρ)) ρ = βs := by
  have h : |(1 - α) / ρ * ρ| < 1 := by
    rw [div_mul_cancel₀ _ hρ, abs_lt]; constructor <;> linarith
  have hα : α ≠ 0 := hα0.ne'
  rw [genFn_armaCoeff h, div_mul_cancel₀ _ hρ, div_mul_cancel₀ _ hρ,
    show (1 : ℝ) - (1 - α * βs) = α * βs by ring, show (1 : ℝ) - (1 - α) = α by ring]
  field_simp

/-- Cochrane (2023), Online Appendix p. 595 ("in the case `β_s = 1`, the roots cancel and we
recover the i.i.d. shock"): `θ = φ` makes every coefficient after the first vanish. -/
theorem arma11_iid_of_one (φ : ℝ) (k : ℕ) : armaCoeff φ φ (k + 1) = 0 := by
  simp [armaCoeff]

/-- Cochrane (2023), Online Appendix p. 598 ("the non-invertibility problem occurs for any
`β_s < (1 − ρ)/α`"): with `α, ρ > 0`, the MA root `ρ/(1 − αβ_s)` of (2.3) lies strictly inside
the unit circle (`|θ| > 1`) iff `β_s < (1 − ρ)/α` or `β_s > (1 + ρ)/α`. (The second region,
`θ < −1`, is not mentioned in the book.) -/
theorem arma11_noninvertible_iff {ρ α βs : ℝ} (hρ : 0 < ρ) (hα : 0 < α) :
    1 < |(1 - α * βs) / ρ| ↔ βs < (1 - ρ) / α ∨ (1 + ρ) / α < βs := by
  rw [abs_div, abs_of_pos hρ, one_lt_div hρ, lt_abs, lt_div_iff₀ hα, div_lt_iff₀ hα]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- Cochrane (2023), Online Appendix p. 596: the MA root of (2.3) is `z* = ρ/(1 − αβ_s)`. -/
theorem arma11_root {ρ α βs : ℝ} (hρ : ρ ≠ 0) (h : 1 - α * βs ≠ 0) :
    1 - (1 - α * βs) / ρ * (ρ / (1 - α * βs)) = 0 := by
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 597 ("this ARMA(1,1) is not invertible, and hence it
cannot be recovered by any autoregression"): for `|φ| < 1 < |θ|` the ARMA(1,1) with MA root
`θ⁻¹` is not recoverable. -/
theorem arma11_not_recoverable {φ θ : ℝ} (hφ : |φ| < 1) (hθ : 1 < |θ|) :
    ¬ Recoverable (armaCoeff φ θ) := by
  have hθ0 : θ ≠ 0 := by intro h; rw [h, abs_zero] at hθ; linarith
  have hinv : |θ⁻¹| ≤ 1 := by rw [abs_inv]; exact inv_le_one_of_one_le₀ hθ.le
  have hφθ : |φ * θ⁻¹| < 1 := by
    rw [abs_mul]
    calc |φ| * |θ⁻¹| ≤ |φ| * 1 := mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
      _ < 1 := by linarith
  refine not_recoverable_of_aRho_eq_zero (summable_abs_armaCoeff hφ θ) hinv ?_
  rw [genFn_armaCoeff hφθ, mul_inv_cancel₀ hθ0, sub_self, zero_div]

/-- Cochrane (2023), Online Appendix eq. (2.5), p. 597: the fitted (Wold) ARMA(1,1)
`(1 − ρL)/(1 − φL)`, `φ = (1 − α)/ρ`, has `a(ρ) = (1 − ρ²)/α`, "not the correct answer
`a(ρ) = 0`". -/
theorem arma11_wold_aRho {ρ α : ℝ} (hρ : ρ ≠ 0) (hα0 : 0 < α) (hα2 : α < 2) :
    gen (armaCoeff ((1 - α) / ρ) ρ) ρ = (1 - ρ ^ 2) / α := by
  have h : |(1 - α) / ρ * ρ| < 1 := by
    rw [div_mul_cancel₀ _ hρ, abs_lt]; constructor <;> linarith
  rw [genFn_armaCoeff h, div_mul_cancel₀ _ hρ]
  congr 1
  · ring
  · ring


/-! ### The debt VAR (2.1)–(2.8) under any expectation system -/

/-- Cochrane (2023), Online Appendix eq. (2.7), p. 597: in the model (2.1)–(2.2) with
`a_u(L) = 1`, `s_{t+1} = αv_t + ε_{t+1}`, `ρv_{t+1} = v_t + β_sε_{t+1} − s_{t+1}`, the value of debt
is an AR(1), `v_{t+1} = ((1 − α)/ρ)v_t − ((1 − β_s)/ρ)ε_{t+1}`. -/
theorem debt_ar1 {ρ α βs : ℝ} (hρ : ρ ≠ 0) {s v ε : ℕ → Ω → ℝ}
    (hs : ∀ t, s (t + 1) = α • v t + ε (t + 1))
    (hv : ∀ t, ρ • v (t + 1) = v t + βs • ε (t + 1) - s (t + 1)) (t : ℕ) :
    v (t + 1) = ((1 - α) / ρ) • v t - ((1 - βs) / ρ) • ε (t + 1) := by
  funext w
  have h1 := congrFun (hv t) w
  have h2 := congrFun (hs t) w
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  field_simp
  linarith

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595 (first form): the surplus is an
ARMA(1,1), `s_{t+2} − ((1 − α)/ρ)s_{t+1} = ε_{t+2} − ((1 − αβ_s)/ρ)ε_{t+1}`. -/
theorem arma11_time_domain {ρ α βs : ℝ} (hρ : ρ ≠ 0) {s v ε : ℕ → Ω → ℝ}
    (hs : ∀ t, s (t + 1) = α • v t + ε (t + 1))
    (hv : ∀ t, ρ • v (t + 1) = v t + βs • ε (t + 1) - s (t + 1)) (t : ℕ) :
    s (t + 2) - ((1 - α) / ρ) • s (t + 1) = ε (t + 2) - ((1 - α * βs) / ρ) • ε (t + 1) := by
  funext w
  have h1 := congrFun (hs (t + 1)) w
  have h2 := congrFun (hs t) w
  have h3 := congrFun (debt_ar1 hρ hs hv t) w
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 ⊢
  rw [h1, h2, h3]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595 (second form): the surplus response to the
shock, `Δ_{t+1} s_{t+1+j} = a_j ε_{t+1}` with `a₀ = 1`, `a_{k+1} = −α(1 − β_s)ρ⁻¹((1 − α)/ρ)ᵏ`
("1 in one direction followed by a small and geometrically decaying set of responses in the
other direction"), i.e. `a = armaCoeff ((1 − α)/ρ) ((1 − αβ_s)/ρ)`. -/
theorem arma11_revision (𝔼 : ExpectationSystem Ω) {ρ α βs : ℝ} (hρ : ρ ≠ 0)
    {s v ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε) (hvad : 𝔼.Adapted v)
    (hs : ∀ t, s (t + 1) = α • v t + ε (t + 1))
    (hv : ∀ t, ρ • v (t + 1) = v t + βs • ε (t + 1) - s (t + 1)) (t j : ℕ) :
    innov 𝔼 t (s (t + 1 + j)) =
      armaCoeff ((1 - α) / ρ) ((1 - α * βs) / ρ) j • ε (t + 1) := by
  set φ := (1 - α) / ρ with hφ
  have hv1 := debt_ar1 hρ hs hv
  have har : 𝔼.IsAR1 φ v := by
    refine ⟨hvad, fun τ => ?_⟩
    rw [hv1 τ, map_sub, map_smul, map_smul, hvad τ, hmds.2 τ, smul_zero, sub_zero]
  have hfc : ∀ τ k, 𝔼.E τ (s (τ + 1 + k)) = (α * φ ^ k) • v τ := by
    intro τ k
    rw [show τ + 1 + k = τ + k + 1 by omega, hs (τ + k), map_add, map_smul,
      𝔼.ar1_iterate har τ k, show τ + k + 1 = τ + 1 + k by omega, hmds.E_future τ k, add_zero,
      smul_smul]
  cases j with
  | zero =>
    have hk : 𝔼.E (t + 1) (s (t + 1)) = s (t + 1) := by
      rw [hs t, map_add, map_smul, ← hvad t, 𝔼.known (Nat.le_succ t), hvad t, hmds.1 (t + 1)]
    have h0 := hfc t 0
    rw [add_zero] at h0
    rw [add_zero, innov_apply, hk, h0, hs t]
    simp [armaCoeff]
  | succ k =>
    have h1 := hfc (t + 1) k
    have h2 := hfc t (k + 1)
    rw [show t + 1 + 1 + k = t + 1 + (k + 1) by omega] at h1
    rw [← hφ] at hv1
    have hcoef : φ - (1 - α * βs) / ρ = -(α * ((1 - βs) / ρ)) := by
      rw [hφ]; field_simp; ring
    rw [innov_apply, h1, h2, hv1 t]
    funext w
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, armaCoeff]
    linear_combination (-(φ ^ k * ε (t + 1) w)) * hcoef

/-- Cochrane (2023), Online Appendix eq. (2.8), p. 597: the debt–surplus VAR in matrix form,
`(s_{t+1}, v_{t+1}) = [[0, α], [0, (1 − α)/ρ]](s_t, v_t) + (1, −(1 − β_s)/ρ)ε_{t+1}`. -/
theorem debt_var_eq {ρ α βs : ℝ} (hρ : ρ ≠ 0) {s v ε : ℕ → Ω → ℝ}
    (hs : ∀ t, s (t + 1) = α • v t + ε (t + 1))
    (hv : ∀ t, ρ • v (t + 1) = v t + βs • ε (t + 1) - s (t + 1)) (t : ℕ) (w : Ω) :
    ![s (t + 1) w, v (t + 1) w] = !![0, α; 0, (1 - α) / ρ] *ᵥ ![s t w, v t w] +
      ε (t + 1) w • ![1, -((1 - βs) / ρ)] := by
  have h1 := congrFun (hs t) w
  have h2 := congrFun (debt_ar1 hρ hs hv t) w
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  ext i
  fin_cases i
  · simp [h1]
    ring
  · simp [h2]
    ring

/-- Cochrane (2023), Online Appendix p. 598 ("the eigenvalues of the transition matrix are
`(1 − α)/ρ` and 0"): trace `(1 − α)/ρ` and determinant `0`. -/
theorem debt_var_tr_det (ρ α : ℝ) :
    tr2 !![0, α; 0, (1 - α) / ρ] = (1 - α) / ρ ∧ det2 !![0, α; 0, (1 - α) / ρ] = 0 := by
  simp [tr2, det2]

/-- Cochrane (2023), Online Appendix p. 598 ("both less than one, so this is the joint Wold
moving-average representation"): for `|(1 − α)/ρ| < 1` the debt VAR is stable (Schur–Cohn). -/
theorem debt_var_stable {ρ α : ℝ} (h : |(1 - α) / ρ| < 1) :
    SchurStable (tr2 !![0, α; 0, (1 - α) / ρ]) (det2 !![0, α; 0, (1 - α) / ρ]) := by
  rw [(debt_var_tr_det ρ α).1, (debt_var_tr_det ρ α).2]
  exact ⟨by simp, by simpa using h⟩

/-- Cochrane (2023), Online Appendix p. 598 ("the true surplus shock can be recovered from the
history of debt"): the VAR innovation of the surplus is the structural shock,
`ε_{t+1} = s_{t+1} − E_t s_{t+1}` with `E_t s_{t+1} = αv_t`. -/
theorem shock_from_debt (𝔼 : ExpectationSystem Ω) {α : ℝ} {s v ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hvad : 𝔼.Adapted v) (hs : ∀ t, s (t + 1) = α • v t + ε (t + 1))
    (t : ℕ) : 𝔼.E t (s (t + 1)) = α • v t ∧ ε (t + 1) = s (t + 1) - 𝔼.E t (s (t + 1)) := by
  have h : 𝔼.E t (s (t + 1)) = α • v t := by
    rw [hs t, map_add, map_smul, hvad t, hmds.2 t, add_zero]
  refine ⟨h, ?_⟩
  rw [h, hs t]
  abel

/-! ### MA(1) examples (p. 102 and Online Appendix §2.1.5) -/

/-- Cochrane (2023), p. 102, and Online Appendix eq. (2.9), p. 598 (tool): for
`s_{t+1} = ε_{t+1} + cε_t` the forecasts are `E_t s_{t+1} = cε_t` and `E_t s_{t+2+k} = 0`. -/
theorem ma1_forecasts (𝔼 : ExpectationSystem Ω) {c : ℝ} {s ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + c • ε t) (t : ℕ) :
    𝔼.E t (s (t + 1)) = c • ε t ∧ ∀ k, 𝔼.E t (s (t + 2 + k)) = 0 := by
  constructor
  · rw [hs t, map_add, map_smul, hmds.2 t, hmds.1 t, zero_add]
  · intro k
    rw [show t + 2 + k = (t + 1 + k) + 1 by omega, hs, map_add, map_smul,
      show t + 1 + k + 1 = t + 1 + (k + 1) by omega, hmds.E_future, hmds.E_future, smul_zero,
      add_zero]

/-- Cochrane (2023), p. 102 (the MA(1) `s̃_t = ε_t − θε_{t−1}`): the value of debt
`v_t = E_t ∑ ρʲ s̃_{t+1+j}` equals `−θε_t`. -/
theorem ma1_pv_forward (𝔼 : ExpectationSystem Ω) {θ ρ : ℝ} {s ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) - θ • ε t) (t : ℕ) (w : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) w) (-θ * ε t w) := by
  have hs' : ∀ t, s (t + 1) = ε (t + 1) + (-θ) • ε t := fun t => by
    rw [hs t, neg_smul, sub_eq_add_neg]
  obtain ⟨h1, h2⟩ := ma1_forecasts 𝔼 hmds hs' t
  have h0 : ρ ^ 0 * 𝔼.E t (s (t + 1 + 0)) w = -θ * ε t w := by
    rw [add_zero, h1]; simp
  rw [← h0]
  refine hasSum_single 0 fun j hj => ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  rw [show t + 1 + k.succ = t + 2 + k by omega, h2 k]
  simp

/-- Cochrane (2023), p. 102 ("in this example, we have `v_t = −θε_t = −ρ⁻¹ε_t`. The value of
debt reveals the true shock"): with `θ = ρ⁻¹`, `ε_t = −ρ v_t`. -/
theorem ma1_value_reveals_shock (𝔼 : ExpectationSystem Ω) {ρ : ℝ} (hρ : ρ ≠ 0)
    {s ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) - ρ⁻¹ • ε t)
    (t : ℕ) (w : Ω) :
    (∑' j, ρ ^ j * 𝔼.E t (s (t + 1 + j)) w) = -ρ⁻¹ * ε t w ∧
    ε t w = -ρ * ∑' j, ρ ^ j * 𝔼.E t (s (t + 1 + j)) w := by
  rw [(ma1_pv_forward 𝔼 hmds hs t w).tsum_eq]
  refine ⟨rfl, ?_⟩
  field_simp

/-- Cochrane (2023), Online Appendix eq. (2.9), p. 598: for `s_t = ε_t + θε_{t−1}`, the value of
debt is `B_{t−1}/P_t = E_t ∑ βʲ s_{t+j} = (1 + βθ)ε_t + θε_{t−1}` (dates shifted by one). -/
theorem ma1_debt_value (𝔼 : ExpectationSystem Ω) {θ β : ℝ} {s ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + θ • ε t) (t : ℕ) (w : Ω) :
    HasSum (fun j => β ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) w)
      ((1 + β * θ) * ε (t + 1) w + θ * ε t w) := by
  obtain ⟨h1, h2⟩ := ma1_forecasts 𝔼 hmds hs (t + 1)
  have hk : 𝔼.E (t + 1) (s (t + 1)) = s (t + 1) := by
    rw [hs t, map_add, map_smul, hmds.1 (t + 1), hmds.E_past (Nat.le_succ t)]
  have hval : (∑ j ∈ Finset.range 2, β ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) w) =
      (1 + β * θ) * ε (t + 1) w + θ * ε t w := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero, pow_zero, one_mul,
      pow_one, zero_add]
    rw [hk, show t + 1 + 1 = t + 1 + 1 by rfl, h1, hs t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [← hval]
  refine hasSum_sum_of_ne_finset_zero fun j hj => ?_
  have hj2 : 2 ≤ j := by simp at hj; omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj2
  rw [show t + 1 + (2 + k) = t + 1 + 2 + k by omega, h2 k]
  simp

/-- Cochrane (2023), Online Appendix p. 598 ("if a government wishes no unexpected inflation,
the surplus process must follow `a(β) = 1 + βθ = 0`. Therefore … `θ = −R`"), `R = β⁻¹`. -/
theorem ma1_no_inflation_iff {β θ : ℝ} (hβ : β ≠ 0) : 1 + β * θ = 0 ↔ θ = -β⁻¹ := by
  constructor
  · intro h
    field_simp
    linarith
  · rintro rfl
    field_simp
    ring

/-- Cochrane (2023), Online Appendix eqs. (2.10)–(2.11), p. 598: with `θ = −R`, `βR = 1`, the
value of debt is `B_{t−1}/P_t = −Rε_{t−1}`: the government borrows to fund the deficit and repays
it with interest one period later. -/
theorem ma1_repaying_debt_value (𝔼 : ExpectationSystem Ω) {β R : ℝ} (hβR : β * R = 1)
    {s ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + (-R) • ε t)
    (t : ℕ) (w : Ω) :
    HasSum (fun j => β ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) w) (-R * ε t w) := by
  have h := ma1_debt_value 𝔼 (β := β) hmds hs t w
  rwa [show 1 + β * -R = 0 by linarith, zero_mul, zero_add] at h

/-- Cochrane (2023), Online Appendix eq. (2.11), p. 598, survey E13: the printed middle expression
`ε_t − Rε_{t−1} + βRε_t` (with `βR = 1`) equals the correct value `−Rε_{t−1}` only when
`ε_t = 0`; the sign of `βRε_t` must be minus (`βθ = −βR`). -/
theorem printed_2_11_wrong {β R : ℝ} (hβR : β * R = 1) (e1 e0 : ℝ) :
    e1 - R * e0 + β * R * e1 = -R * e0 ↔ e1 = 0 := by
  rw [hβR]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), Online Appendix p. 599 ((2.13): "`(E_t − E_{t−1}) ∑ βʲ s_{t+j} = (1 − β²)w_t`,
not zero"): for `s_{t+1} = w_{t+1} + cw_t` the news in the present value is `(1 + βc)w_{t+1}`
`= a(β)w_{t+1}`; for the autoregression's fitted `c = −β` it is `(1 − β²)w_{t+1}`. -/
theorem ma1_pv_innov (𝔼 : ExpectationSystem Ω) {c β : ℝ} {s ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + c • ε t) (t : ℕ) (w : Ω) :
    (∑' j, β ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) w) - (∑' j, β ^ j * 𝔼.E t (s (t + 1 + j)) w) =
      (1 + β * c) * ε (t + 1) w := by
  have hs' : ∀ t, s (t + 1) = ε (t + 1) - (-c) • ε t := fun t => by
    rw [hs t, neg_smul, sub_neg_eq_add]
  rw [(ma1_debt_value 𝔼 hmds hs t w).tsum_eq, (ma1_pv_forward 𝔼 (ρ := β) hmds hs' t w).tsum_eq]
  ring

/-- Cochrane (2023), Online Appendix eq. (2.13), p. 599: the fitted MA(1) `s_t = w_t − βw_{t−1}`
has `a(β) = 1 − β²` ("you predict volatile inflation"), nonzero for `|β| < 1`. -/
theorem ma1_fitted_pv_innov (𝔼 : ExpectationSystem Ω) {β : ℝ} {s w : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 w) (hs : ∀ t, s (t + 1) = w (t + 1) + (-β) • w t) (t : ℕ) (x : Ω) :
    (∑' j, β ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) x) - (∑' j, β ^ j * 𝔼.E t (s (t + 1 + j)) x) =
      (1 - β ^ 2) * w (t + 1) x := by
  rw [ma1_pv_innov 𝔼 hmds hs t x]
  ring

/-- Cochrane (2023), Online Appendix eqs. (2.14)–(2.16), p. 599: for `s_t = ε_t − Rε_{t−1}` and
`B_t/P = −Rε_t`, the joint process is the VAR `(s_t, B_t/P) = [[0, 1], [0, 0]](s_{t−1}, B_{t−1}/P)
+ (ε_t, −Rε_t)`, its matrix is nilpotent (the terms converge, unlike (2.12)), the structural shock
is recovered as `ε_t = s_t − B_{t−1}/P`, and debt forecasts surpluses, `E_{t−1}s_t = B_{t−1}/P`
(debt Granger-causes surpluses although surpluses are exogenous). -/
theorem ma1_debt_var (𝔼 : ExpectationSystem Ω) {R : ℝ} {s ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + (-R) • ε t) (t : ℕ) (w : Ω) :
    ![s (t + 1) w, -R * ε (t + 1) w] = !![0, 1; 0, 0] *ᵥ ![s t w, -R * ε t w] +
      ![ε (t + 1) w, -R * ε (t + 1) w] ∧
    (!![(0 : ℝ), 1; 0, 0]) ^ 2 = 0 ∧
    ε (t + 1) = s (t + 1) - (-R) • ε t ∧
    𝔼.E t (s (t + 1)) = (-R) • ε t := by
  refine ⟨?_, ?_, ?_, (ma1_forecasts 𝔼 hmds hs t).1⟩
  · have h1 := congrFun (hs t) w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    ext i
    fin_cases i
    · simp [h1]
      ring
    · simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hs t]
    abel

/-! ### The Hansen–Sargent formula (2.19) and the value of debt (2.18), (2.20)–(2.21) -/

/-- Cochrane (2023), eq. (4.1), p. 87, and Online Appendix p. 600: the moving average
`s_t = ∑_{j ≤ t} aⱼ ε_{t−j}` started from a zero pre-sample (shocks dated `0, 1, 2, …`). -/
def maSeries (a : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range (t + 1), a j • ε (t - j)

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601: the Hansen–Sargent coefficients
`c_k = ∑ⱼ ρʲ a_{k+1+j}` of `[(a(L) − a(ρ))L⁻¹/(1 − ρL⁻¹)]`. -/
noncomputable def hsCoeff (a : ℕ → ℝ) (ρ : ℝ) (k : ℕ) : ℝ := ∑' j, ρ ^ j * a (k + 1 + j)

/-- Cochrane (2023), Online Appendix p. 601 (tool): the series defining `c_k` converges. -/
theorem summable_hs {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (k : ℕ) : Summable (fun j => ρ ^ j * a (k + 1 + j)) := by
  have h : Summable (fun j => |a (j + (k + 1))|) :=
    (summable_nat_add_iff (f := fun j => |a j|) (k + 1)).mpr ha
  refine Summable.of_norm_bounded h fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, show k + 1 + j = j + (k + 1) by omega]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ)

/-- Cochrane (2023), Online Appendix p. 601 (tool): `c_k = a_{k+1} + ρ c_{k+1}`. -/
theorem hsCoeff_rec {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (k : ℕ) : hsCoeff a ρ k = a (k + 1) + ρ * hsCoeff a ρ (k + 1) := by
  rw [hsCoeff, (summable_hs ha hρ k).tsum_eq_zero_add, hsCoeff, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show k + 1 + (j + 1) = k + 1 + 1 + j by omega, pow_succ]
  ring

/-- Cochrane (2023), Online Appendix p. 601 (tool): `ρc_0 = a(ρ) − a_0`. -/
theorem rho_hsCoeff_zero {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ρ * hsCoeff a ρ 0 = gen a ρ - a 0 := by
  have hs : Summable (fun j => a j * ρ ^ j) :=
    Summable.of_norm_bounded ha fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ)
  rw [gen, hs.tsum_eq_zero_add, hsCoeff, ← tsum_mul_left]
  simp only [pow_zero, mul_one, add_sub_cancel_left]
  refine tsum_congr fun j => ?_
  rw [show 0 + 1 + j = j + 1 by omega, pow_succ]
  ring

/-- Cochrane (2023), Online Appendix p. 601 (tool): `|c_k| ≤ ∑|aⱼ|` for `|ρ| ≤ 1`. -/
theorem abs_hsCoeff_le {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (k : ℕ) : |hsCoeff a ρ k| ≤ ∑' j, |a j| := by
  have h : Summable (fun j => |a (j + (k + 1))|) :=
    (summable_nat_add_iff (f := fun j => |a j|) (k + 1)).mpr ha
  have h1 : |hsCoeff a ρ k| ≤ ∑' j, |a (j + (k + 1))| := by
    have hb : ∀ j, ‖ρ ^ j * a (k + 1 + j)‖ ≤ |a (j + (k + 1))| := fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, show k + 1 + j = j + (k + 1) by omega]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ)
    have hn : Summable (fun j => ‖ρ ^ j * a (k + 1 + j)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb h
    rw [hsCoeff, ← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm hn).trans (Summable.tsum_le_tsum hb hn h)
  have h2 := ha.sum_add_tsum_nat_add (k + 1)
  have h3 : 0 ≤ ∑ i ∈ Finset.range (k + 1), |a i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601 (tool): the surplus `t + 1 + i` periods
ahead splits into future shocks and the shocks already known at `t`. -/
theorem ma_split (a : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (t i : ℕ) :
    maSeries a ε (t + 1 + i) = ∑ j ∈ Finset.range (i + 1), a j • ε (t + 1 + (i - j)) +
      ∑ k ∈ Finset.range (t + 1), a (k + 1 + i) • ε (t - k) := by
  rw [maSeries, show t + 1 + i + 1 = (i + 1) + (t + 1) by omega, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.mp hj
    rw [show t + 1 + i - j = t + 1 + (i - j) by omega]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.mp hk
    rw [show i + 1 + k = k + 1 + i by omega, show t + 1 + i - (k + 1 + i) = t - k by omega]

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601: the forecast of a moving average,
`E_t s_{t+1+i} = ∑_{k ≤ t} a_{k+1+i} ε_{t−k}` (future shocks are forecast to be zero). -/
theorem ma_forecast (𝔼 : ExpectationSystem Ω) {ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε)
    (a : ℕ → ℝ) (t i : ℕ) :
    𝔼.E t (maSeries a ε (t + 1 + i)) = ∑ k ∈ Finset.range (t + 1), a (k + 1 + i) • ε (t - k) := by
  rw [ma_split, map_add, map_sum, map_sum]
  simp only [map_smul, hmds.E_future, smul_zero, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hmds.E_past (Nat.sub_le t k)]

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601 (the Hansen–Sargent prediction formula):
`E_t ∑ ρⁱ s_{t+1+i} = ∑_k c_k ε_{t−k}`, `c_k = ∑ⱼ ρʲ a_{k+1+j}` — the operator
`[(a(L) − a(ρ))L⁻¹/(1 − ρL⁻¹)]ε_t` (here as the sum of forecasts, `|ρ| ≤ 1`). -/
theorem hansenSargent (𝔼 : ExpectationSystem Ω) {ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε)
    {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ : |ρ| ≤ 1) (t : ℕ) (w : Ω) :
    HasSum (fun i => ρ ^ i * 𝔼.E t (maSeries a ε (t + 1 + i)) w)
      (∑ k ∈ Finset.range (t + 1), hsCoeff a ρ k * ε (t - k) w) := by
  simp only [ma_forecast 𝔼 hmds, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine hasSum_sum fun k _ => ?_
  have := ((summable_hs ha hρ k).hasSum).mul_right (ε (t - k) w)
  refine this.congr_fun fun i => ?_
  ring

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601, for the genuine (pathwise) present value:
with bounded shocks and `|ρ| < 1`, `E_t(∑ ρⁱ s_{t+1+i}) = ∑_k c_k ε_{t−k}`. -/
theorem hansenSargent_E_tsum (𝔼 : ExpectationSystem Ω) {ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε)
    {M : ℝ} (hM : ∀ t w, |ε t w| ≤ M) {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ}
    (hρ : |ρ| < 1) (t : ℕ) (w : Ω) :
    𝔼.E t (fun x => ∑' i, ρ ^ i * maSeries a ε (t + 1 + i) x) w =
      ∑ k ∈ Finset.range (t + 1), hsCoeff a ρ k * ε (t - k) w := by
  set A := ∑' j, |a j| with hA
  have hbound : ∀ n x, |maSeries a ε n x| ≤ M * A := by
    intro n x
    rw [maSeries, Finset.sum_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 x)
    calc ∑ j ∈ Finset.range (n + 1), |(a j • ε (n - j)) x|
        ≤ ∑ j ∈ Finset.range (n + 1), |a j| * M := Finset.sum_le_sum fun j _ => by
          rw [Pi.smul_apply, smul_eq_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hM _ x) (abs_nonneg _)
      _ = M * ∑ j ∈ Finset.range (n + 1), |a j| := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ M * A := mul_le_mul_of_nonneg_left
          (ha.sum_le_tsum _ fun _ _ => abs_nonneg _) hM0
  have hu : Summable (fun i => |ρ| ^ i * (M * A)) :=
    (summable_geometric_of_lt_one (abs_nonneg _) hρ).mul_right _
  have hf : ∀ i x, |(ρ ^ i • maSeries a ε (t + 1 + i)) x| ≤ |ρ| ^ i * (M * A) := by
    intro i x
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hbound _ x) (pow_nonneg (abs_nonneg _) _)
  have h := ForwardSolution.E_tsum_dom 𝔼 hu hf t w
  change 𝔼.E t (fun x => ∑' i, (ρ ^ i • maSeries a ε (t + 1 + i)) x) w = _
  rw [h, ← (hansenSargent 𝔼 hmds ha hρ.le t w).tsum_eq]
  refine tsum_congr fun i => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601 (generating-function form): for
`|ρ| ≤ 1`, `|z| < 1`, `z ≠ ρ`, `∑_k c_k zᵏ = (a(z) − a(ρ))/(z − ρ)`. -/
theorem hansenSargent_genFn {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ z : ℝ}
    (hρ : |ρ| ≤ 1) (hz : |z| < 1) (hzρ : z ≠ ρ) :
    ∑' k, hsCoeff a ρ k * z ^ k = (gen a z - gen a ρ) / (z - ρ) := by
  set c := hsCoeff a ρ with hc
  have hCs : Summable (fun k => c k * z ^ k) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (abs_nonneg _) hz).mul_left (∑' j, |a j|)) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right (abs_hsCoeff_le ha hρ k) (pow_nonneg (abs_nonneg _) _)
  set C := ∑' k, c k * z ^ k with hCdef
  have hC := hCs.hasSum
  have hC1 : HasSum (fun k => c (k + 1) * z ^ (k + 1)) (C - c 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hC
    simpa using this
  have haz : Summable (fun j => a j * z ^ j) :=
    Summable.of_norm_bounded ha fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hz.le)
  have hA1 : HasSum (fun k => a (k + 1) * z ^ (k + 1)) (gen a z - a 0) := by
    have := (hasSum_nat_add_iff' 1).mpr haz.hasSum
    simpa [gen] using this
  have hzC : HasSum (fun k => c k * z ^ (k + 1)) (z * C) := by
    refine (hC.mul_left z).congr_fun fun k => ?_
    rw [pow_succ]; ring
  have hrec : HasSum (fun k => c k * z ^ (k + 1)) (gen a z - a 0 + ρ * (C - c 0)) := by
    refine (hA1.add (hC1.mul_left ρ)).congr_fun fun k => ?_
    rw [hc, hsCoeff_rec ha hρ k]
    ring
  have h1 := hzC.unique hrec
  have h2 := rho_hsCoeff_zero ha hρ
  rw [← hc] at h2
  have hne : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
  rw [eq_div_iff hne]
  linear_combination h1 - h2

/-- Cochrane (2023), Online Appendix eq. (2.18), p. 600 ("debt equals the ex-post as well as
expected present value of surpluses"): if `a(ρ) = 0` (`|ρ| < 1`, bounded shocks), the realised
present value `∑ ρⁱ s_{t+1+i}` equals the forecast `∑_k c_k ε_{t−k}` path by path — future shocks
drop out because the government offsets each one. -/
theorem value_expost_of_aRho_zero {ε : ℕ → Ω → ℝ} {M : ℝ} (hM : ∀ t w, |ε t w| ≤ M)
    {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ : |ρ| < 1) (h0 : gen a ρ = 0)
    (t : ℕ) (w : Ω) :
    HasSum (fun i => ρ ^ i * maSeries a ε (t + 1 + i) w)
      (∑ k ∈ Finset.range (t + 1), hsCoeff a ρ k * ε (t - k) w) := by
  have hf : Summable (fun j => ‖a j * ρ ^ j‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ.le)) ha
  have hg : Summable (fun m => ‖ρ ^ m * ε (t + 1 + m) w‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hM _ w) (pow_nonneg (abs_nonneg _) _))
      ((summable_geometric_of_lt_one (abs_nonneg _) hρ).mul_right M)
  have hcauchy := hasSum_sum_range_mul_of_summable_norm hf hg
  have hfz : ∑' n, a n * ρ ^ n = 0 := h0
  rw [hfz, zero_mul] at hcauchy
  have hknown : HasSum (fun i => ∑ k ∈ Finset.range (t + 1), ρ ^ i * a (k + 1 + i) * ε (t - k) w)
      (∑ k ∈ Finset.range (t + 1), hsCoeff a ρ k * ε (t - k) w) :=
    hasSum_sum fun k _ => ((summable_hs ha hρ.le k).hasSum).mul_right (ε (t - k) w)
  have hsum := hcauchy.add hknown
  rw [zero_add] at hsum
  refine hsum.congr_fun fun i => ?_
  rw [ma_split, Pi.add_apply, Finset.sum_apply, Finset.sum_apply, mul_add, Finset.mul_sum,
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Pi.smul_apply, smul_eq_mul]
    have : ρ ^ i = ρ ^ j * ρ ^ (i - j) := by rw [← pow_add, Nat.add_sub_cancel' hji]
    rw [this]
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), Online Appendix eqs. (2.20)–(2.21), pp. 600–601: if the moving average has
the factor `1 − ρ⁻¹L`, `a(L) = (1 − ρ⁻¹L)g(L)` (`a₀ = g₀`, `a_{k+1} = g_{k+1} − ρ⁻¹g_k`,
`∑|g_k| < ∞`, `0 < |ρ| ≤ 1`), then `a(ρ) = 0` and the Hansen–Sargent coefficients are
`c_k = −ρ⁻¹g_k`: the debt is the *invertible* moving average `v_t = −ρ⁻¹g(L)ε_t` — "the
non-invertible root cancels". -/
theorem factor_value {a g : ℕ → ℝ} (hg : Summable (fun j => |g j|)) {ρ : ℝ} (hρ0 : ρ ≠ 0)
    (hρ : |ρ| ≤ 1) (h0 : a 0 = g 0) (hk : ∀ k, a (k + 1) = g (k + 1) - ρ⁻¹ * g k) :
    gen a ρ = 0 ∧ ∀ k, hsCoeff a ρ k = -ρ⁻¹ * g k := by
  have hgs : ∀ m, Summable (fun j => ρ ^ j * g (m + j)) := fun m => by
    have h : Summable (fun j => |g (j + m)|) :=
      (summable_nat_add_iff (f := fun j => |g j|) m).mpr hg
    refine Summable.of_norm_bounded h fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, add_comm m j]
    exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ)
  constructor
  · have hG : Summable (fun j => g j * ρ ^ j) := (hgs 0).congr fun j => by rw [zero_add, mul_comm]
    have h1 : HasSum (fun j => g (j + 1) * ρ ^ (j + 1)) (∑' j, g j * ρ ^ j - g 0) := by
      have := (hasSum_nat_add_iff' 1).mpr hG.hasSum
      simpa using this
    have h2 : HasSum (fun j => a (j + 1) * ρ ^ (j + 1)) (∑' j, g j * ρ ^ j - g 0 -
        ∑' j, g j * ρ ^ j) := by
      refine (h1.sub hG.hasSum).congr_fun fun j => ?_
      rw [hk j, pow_succ]
      field_simp
    have h3 : HasSum (fun j => a j * ρ ^ j) (a 0 + (∑' j, g j * ρ ^ j - g 0 -
        ∑' j, g j * ρ ^ j)) := by
      rw [← hasSum_nat_add_iff' 1]
      simpa using h2
    rw [gen, h3.tsum_eq, h0]
    ring
  · intro k
    have hsplit : ∑' j, ρ ^ j * g (k + j) = g k + ρ * ∑' j, ρ ^ j * g (k + 1 + j) := by
      rw [(hgs k).tsum_eq_zero_add, ← tsum_mul_left]
      simp only [pow_zero, one_mul, add_zero]
      congr 1
      refine tsum_congr fun j => ?_
      rw [pow_succ, show k + (j + 1) = k + 1 + j by omega]
      ring
    have hA : hsCoeff a ρ k = ∑' j, ρ ^ j * g (k + 1 + j) - ρ⁻¹ * ∑' j, ρ ^ j * g (k + j) := by
      rw [hsCoeff, ← tsum_mul_left, ← Summable.tsum_sub (hgs (k + 1)) ((hgs k).mul_left _)]
      refine tsum_congr fun j => ?_
      rw [show k + 1 + j = j + k + 1 by omega, hk (j + k), show j + k + 1 = k + 1 + j by omega,
        show j + k = k + j by omega]
      ring
    rw [hA, hsplit]
    field_simp
    ring

/-- Cochrane (2023), Online Appendix eq. (2.17), p. 600 ("if we have `a(ρ) = 0`, one of the
numerator factors must be `(1 − ρ⁻¹L)`"): if `a(ρ) = 0` (`ρ ≠ 0`, `|ρ| ≤ 1`), then
`a(L) = (1 − ρ⁻¹L)g(L)` with `g_k = −ρc_k` (bounded). With `factor_value`, `a(ρ) = 0` iff `a(L)`
has the factor `1 − ρ⁻¹L`. -/
theorem factor_of_aRho_zero {a : ℕ → ℝ} (ha : Summable (fun j => |a j|)) {ρ : ℝ} (hρ0 : ρ ≠ 0)
    (hρ : |ρ| ≤ 1) (h0 : gen a ρ = 0) :
    a 0 = -ρ * hsCoeff a ρ 0 ∧
    (∀ k, a (k + 1) = -ρ * hsCoeff a ρ (k + 1) - ρ⁻¹ * (-ρ * hsCoeff a ρ k)) ∧
    ∀ k, |-ρ * hsCoeff a ρ k| ≤ ∑' j, |a j| := by
  refine ⟨?_, fun k => ?_, fun k => ?_⟩
  · have := rho_hsCoeff_zero ha hρ
    rw [h0] at this
    linarith
  · rw [hsCoeff_rec ha hρ k]
    field_simp
    ring
  · rw [abs_mul, abs_neg]
    calc |ρ| * |hsCoeff a ρ k| ≤ 1 * ∑' j, |a j| :=
          mul_le_mul hρ (abs_hsCoeff_le ha hρ k) (abs_nonneg _) zero_le_one
      _ = ∑' j, |a j| := one_mul _

/-! ### Second moments in a Hilbert space: non-recoverability and the Wold innovation -/

namespace Hilbert

open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Cochrane (2023), p. 102, and Online Appendix p. 597 (white noise, `ℤ`-indexed so that moving
averages have an infinite past): pairwise orthogonal with common variance `σ²`. -/
def WhiteNoise (e : ℤ → H) (σ2 : ℝ) : Prop := ∀ t u, ⟪e t, e u⟫ = if t = u then σ2 else 0

/-- Cochrane (2023), eq. (4.1), p. 87: the moving average `s_t = ∑_k a_k e_{t−k}` in the Hilbert
space of second moments. -/
noncomputable def maProc (a : ℕ → ℝ) (e : ℤ → H) (t : ℤ) : H := ∑' k : ℕ, a k • e (t - k)

/-- Cochrane (2023), p. 102 ("any statistical procedure based on the history of surpluses
alone"): the closed linear span of `s_t, s_{t−1}, s_{t−2}, …` — everything linear (including
limits) that can be computed from current and past surpluses. -/
noncomputable def pastSpan (s : ℤ → H) (t : ℤ) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range fun k : ℕ => s (t - k))).topologicalClosure

/-- Cochrane (2023), p. 102 and Online Appendix (2.4), p. 597: the MA(1) `m_t = e_t − θe_{t−1}`. -/
def maOne (θ : ℝ) (e : ℤ → H) (t : ℤ) : H := e t - θ • e (t - 1)

/-- Cochrane (2023), p. 102 ("`u_t = s_t − E(s_t|s_{t−1}, s_{t−2}, …)`") and Online Appendix
(2.5), p. 597: the candidate Wold innovation `w_t = ∑_k θ⁻ᵏ m_{t−k}`. -/
noncomputable def woldInnov (θ : ℝ) (m : ℤ → H) (t : ℤ) : H := ∑' k : ℕ, (θ⁻¹) ^ k • m (t - k)

/-- Cochrane (2023), Online Appendix p. 597 (tool): white noise has variance `σ²` and constant
norm. -/
theorem WhiteNoise.norm_eq {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (t : ℤ) :
    ‖e t‖ = ‖e 0‖ := by
  have h1 := he t t
  have h2 := he 0 0
  simp only [↓reduceIte, real_inner_self_eq_norm_sq] at h1 h2
  have : ‖e t‖ ^ 2 = ‖e 0‖ ^ 2 := by rw [h1, h2]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

/-- Cochrane (2023), Online Appendix p. 597 (tool): moving averages with absolutely summable
coefficients converge in the Hilbert space. -/
theorem maProc_hasSum [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) :
    HasSum (fun k : ℕ => a k • e (t - k)) (maProc a e t) := by
  refine (Summable.of_norm ?_).hasSum
  refine (ha.mul_right ‖e 0‖).congr fun k => ?_
  rw [norm_smul, Real.norm_eq_abs, he.norm_eq (t - k)]

/-- Cochrane (2023), p. 102 (tool): inner products pass through convergent series. -/
theorem inner_hasSum_right {f : ℕ → H} {x : H} (h : HasSum f x) (y : H) :
    HasSum (fun k => ⟪y, f k⟫) ⟪y, x⟫ := by
  simpa [innerSL_apply_apply] using h.mapL (innerSL ℝ y)

/-- Cochrane (2023), p. 102 (tool): the covariance of a past shock with the moving average,
`⟪e_{t−n}, s_t⟫ = σ² a_n`. -/
theorem inner_e_maProc [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) (n : ℕ) :
    ⟪e (t - n), maProc a e t⟫ = σ2 * a n := by
  have h := inner_hasSum_right (maProc_hasSum he ha t) (e (t - n))
  refine h.unique ?_
  have : σ2 * a n = (fun k : ℕ => ⟪e (t - n), a k • e (t - k)⟫) n := by
    change σ2 * a n = ⟪e (t - n), a n • e (t - n)⟫
    rw [real_inner_smul_right, he (t - n) (t - n)]
    simp only [↓reduceIte]
    ring
  rw [this]
  refine hasSum_single n fun k hk => ?_
  rw [real_inner_smul_right, he]
  have : t - (n : ℤ) ≠ t - k := by
    intro h; exact hk (by exact_mod_cast (sub_right_inj.mp h).symm)
  simp [this]

/-- Cochrane (2023), p. 102 (tool): the members `s_{t−k}` lie in the closed past span. -/
theorem mem_pastSpan_self (s : ℤ → H) (t : ℤ) (k : ℕ) : s (t - k) ∈ pastSpan s t :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨k, rfl⟩)

/-- Cochrane (2023), p. 102 (tool): the past span grows with the date. -/
theorem pastSpan_mono (s : ℤ → H) {t t' : ℤ} (h : t ≤ t') : pastSpan s t ≤ pastSpan s t' := by
  refine Submodule.topologicalClosure_mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h)
  have : s (t - k) = s (t' - ((k + d : ℕ) : ℤ)) := by
    congr 1; push_cast; omega
  change s (t - k) ∈ _
  rw [this]
  exact Submodule.subset_span ⟨k + d, rfl⟩

/-- Cochrane (2023), p. 102 (tool): a vector orthogonal to every `s_{t−k}` is orthogonal to the
whole closed past span. -/
theorem mem_orthogonal_pastSpan {s : ℤ → H} {t : ℤ} {x : H} (h : ∀ k : ℕ, ⟪x, s (t - k)⟫ = 0) :
    x ∈ (pastSpan s t)ᗮ := by
  have hle : pastSpan s t ≤ (ℝ ∙ x)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
      (Submodule.isClosed_orthogonal _)
    rintro _ ⟨k, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (h k)
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [real_inner_comm]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hu)

/-- Cochrane (2023), p. 102 (tool): a convergent series of members of the closed past span lies
in it. -/
theorem hasSum_mem_pastSpan {s : ℤ → H} {t : ℤ} {f : ℕ → H} {x : H} (h : HasSum f x)
    (hf : ∀ k, f k ∈ pastSpan s t) : x ∈ pastSpan s t :=
  (Submodule.isClosed_topologicalClosure _).mem_of_tendsto h.tendsto_sum_nat
    (Filter.Eventually.of_forall fun _ => Submodule.sum_mem _ fun k _ => hf k)

/-- Cochrane (2023), p. 102 ("you cannot recover them from any statistical procedure based on the
history of surpluses alone") and Online Appendix pp. 597, 600 (for any moving average with
`a(ρ) = 0`): if `s_t = ∑ a_k e_{t−k}` with `a(ρ) = 0`, `|ρ| < 1`, the structural shock `e_t` is not
in the closed linear span of `s_t, s_{t−1}, …`: the vector `∑ ρᵐ e_{t−m}` is orthogonal to every
`s_{t−j}` but not to `e_t`. -/
theorem not_mem_pastSpan_of_aRho_eq_zero [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ}
    (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) {ρ : ℝ}
    (hρ : |ρ| < 1) (h0 : gen a ρ = 0) (t : ℤ) : e t ∉ pastSpan (maProc a e) t := by
  have hg : Summable (fun m => |ρ ^ m|) := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg ρ) hρ
  set u := maProc (fun m => ρ ^ m) e t with hu
  have horth : ∀ j : ℕ, ⟪u, maProc a e (t - j)⟫ = 0 := by
    intro j
    have h := inner_hasSum_right (maProc_hasSum he ha (t - j)) u
    have hsa : Summable (fun i => a i * ρ ^ i) :=
      Summable.of_norm_bounded ha fun i => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ.le)
    have h2 : HasSum (fun i => ⟪u, a i • e (t - j - i)⟫) (σ2 * ρ ^ j * gen a ρ) := by
      refine (hsa.hasSum.mul_left (σ2 * ρ ^ j)).congr_fun fun i => ?_
      rw [real_inner_smul_right, real_inner_comm,
        show t - (j : ℤ) - (i : ℤ) = t - ((j + i : ℕ) : ℤ) by push_cast; ring,
        hu, inner_e_maProc he hg t (j + i), pow_add]
      ring
    rw [h.unique h2, h0, mul_zero]
  intro hmem
  have hx : u ∈ (pastSpan (maProc a e) t)ᗮ := mem_orthogonal_pastSpan horth
  have h1 := Submodule.inner_right_of_mem_orthogonal hmem hx
  have h2 : ⟪e t, u⟫ = σ2 := by
    have := inner_e_maProc he hg t 0
    simpa using this
  rw [h1] at h2
  exact hσ h2.symm

/-- Cochrane (2023), Online Appendix eq. (2.5), p. 597 (tool): `w_t = ∑ θ⁻ᵏ m_{t−k}` converges. -/
theorem woldInnov_hasSum [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {θ : ℝ} (hθ : 1 < |θ|) (t : ℤ) :
    HasSum (fun k : ℕ => (θ⁻¹) ^ k • maOne θ e (t - k)) (woldInnov θ (maOne θ e) t) := by
  have hq : |θ⁻¹| < 1 := by
    rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hθ
  refine (Summable.of_norm ?_).hasSum
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one (abs_nonneg _) hq).mul_right ((1 + |θ|) * ‖e 0‖))
  rw [norm_smul, Real.norm_eq_abs, abs_pow, maOne]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (abs_nonneg _) _)
  calc ‖e (t - k) - θ • e (t - k - 1)‖ ≤ ‖e (t - k)‖ + ‖θ • e (t - k - 1)‖ := norm_sub_le _ _
    _ = (1 + |θ|) * ‖e 0‖ := by
      rw [norm_smul, Real.norm_eq_abs, he.norm_eq (t - k), he.norm_eq (t - k - 1)]; ring

/-- Cochrane (2023), Online Appendix eq. (2.5), p. 597: `w_t − θ⁻¹w_{t−1} = m_t`, i.e. the
fitted moving average has root `θ⁻¹` (`= ρ` when `θ = ρ⁻¹`). -/
theorem wold_recursion [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) {θ : ℝ}
    (hθ : 1 < |θ|) (t : ℤ) :
    maOne θ e t = woldInnov θ (maOne θ e) t - θ⁻¹ • woldInnov θ (maOne θ e) (t - 1) := by
  have h := woldInnov_hasSum he hθ t
  rw [← hasSum_nat_add_iff' 1] at h
  have h1 := (woldInnov_hasSum he hθ (t - 1)).const_smul θ⁻¹
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_smul, Nat.cast_zero,
    sub_zero] at h
  have heq := h.unique (h1.congr_fun fun k => ?_)
  · rw [← heq]; abel
  · rw [smul_smul, ← pow_succ']
    congr 2
    push_cast
    ring

/-- Cochrane (2023), Online Appendix p. 597 (tool): the covariance of `w_t` with the structural
shocks, `⟪e_{t−n}, w_t⟫ = σ²` for `n = 0` and `σ²θ⁻ⁿ(1 − θ²)` for `n ≥ 1`. -/
theorem inner_e_wold [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) {θ : ℝ}
    (hθ : 1 < |θ|) (t : ℤ) (n : ℕ) :
    ⟪e (t - n), woldInnov θ (maOne θ e) t⟫ =
      σ2 * (θ⁻¹) ^ n - (if n = 0 then 0 else σ2 * θ * (θ⁻¹) ^ (n - 1)) := by
  have h := inner_hasSum_right (woldInnov_hasSum he hθ t) (e (t - n))
  refine h.unique ?_
  have hterm : ∀ k : ℕ, ⟪e (t - n), (θ⁻¹) ^ k • maOne θ e (t - k)⟫ =
      (if k = n then σ2 * (θ⁻¹) ^ n else 0) -
        (if k + 1 = n then σ2 * θ * (θ⁻¹) ^ k else 0) := by
    intro k
    rw [real_inner_smul_right, maOne, inner_sub_right, real_inner_smul_right, he, he]
    have e1 : (t - (n : ℤ) = t - k) ↔ k = n := by
      constructor
      · intro h; exact_mod_cast (sub_right_inj.mp h).symm
      · rintro rfl; rfl
    have e2 : (t - (n : ℤ) = t - k - 1) ↔ k + 1 = n := by
      constructor
      · intro h; omega
      · intro h; subst h; push_cast; ring
    by_cases h1 : k = n <;> by_cases h2 : k + 1 = n <;> simp_all <;> ring
  simp only [hterm]
  refine HasSum.sub (hasSum_ite_eq n _) ?_
  cases n with
  | zero =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    exact hasSum_zero
  | succ n =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte, add_tsub_cancel_right, Nat.add_right_cancel_iff]
    refine (hasSum_ite_eq n (σ2 * θ * (θ⁻¹) ^ n)).congr_fun fun k => ?_
    by_cases hk : k = n
    · simp [hk]
    · simp [hk]

/-- Cochrane (2023), Online Appendix p. 597 (tool): the covariance of `w_t` with the moving
average `s_{t−j}`, `j ≥ 1`, is `σ²(1 − θ²)θ⁻ʲ a(θ⁻¹)`. -/
theorem inner_wold_maProc [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {θ : ℝ} (hθ : 1 < |θ|) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) (j : ℕ) :
    ⟪woldInnov θ (maOne θ e) t, maProc a e (t - (j + 1 : ℕ))⟫ =
      σ2 * (1 - θ ^ 2) * (θ⁻¹) ^ (j + 1) * gen a θ⁻¹ := by
  have hθ0 : θ ≠ 0 := by intro h; rw [h, abs_zero] at hθ; linarith
  have hq : |θ⁻¹| ≤ 1 := by rw [abs_inv]; exact inv_le_one_of_one_le₀ hθ.le
  have h := inner_hasSum_right (maProc_hasSum he ha (t - (j + 1 : ℕ)))
    (woldInnov θ (maOne θ e) t)
  have hsa : Summable (fun i => a i * (θ⁻¹) ^ i) :=
    Summable.of_norm_bounded ha fun i => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hq)
  refine h.unique ((hsa.hasSum.mul_left (σ2 * (1 - θ ^ 2) * (θ⁻¹) ^ (j + 1))).congr_fun
    fun i => ?_)
  rw [real_inner_smul_right, real_inner_comm,
    show t - ((j + 1 : ℕ) : ℤ) - (i : ℤ) = t - ((j + 1 + i : ℕ) : ℤ) by push_cast; ring,
    inner_e_wold he hθ t]
  simp only [show j + 1 + i ≠ 0 by omega, ↓reduceIte, show j + 1 + i - 1 = j + i by omega]
  have hinv : θ * θ⁻¹ = 1 := mul_inv_cancel₀ hθ0
  rw [show j + 1 + i = (j + i) + 1 by omega, pow_succ, pow_add, pow_succ]
  linear_combination (a i * σ2 * (θ⁻¹) ^ j * (θ⁻¹) ^ i * θ) * hinv

/-- Cochrane (2023), p. 102, and Online Appendix pp. 597–601 (the Wold representation fitted by
an autoregression): let `s_t = ∑ a_k e_{t−k}` (white noise `e`, variance `σ²`) have `a₀ = 1` and
an MA root at `θ⁻¹`, `a(θ⁻¹) = 0`, `|θ| > 1` (with `θ = ρ⁻¹`: `a(ρ) = 0`), and let
`m_t = e_t − θe_{t−1}` differ from `s_t` by a member of the past span (an AR filter,
`m_t = s_t − φ₁s_{t−1} − …`). Then `w_t = ∑ θ⁻ᵏ m_{t−k}` is the Wold innovation of `s`:
`w_t ⟂` the past, `s_t − w_t` lies in the past span, hence `s_t − w_t` is the orthogonal
projection of `s_t` on its past ("`u_t = s_t − E(s_t|s_{t−1}, …)`"); `w` is white noise with
variance `θ²σ²` (= `σ²/ρ²`); `m_t = w_t − θ⁻¹w_{t−1}` (the fitted root is `θ⁻¹ = ρ`, not `ρ⁻¹`);
and the structural shock `e_t` is not in the closed span of current and past surpluses. -/
theorem wold_innovation [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (hσ : σ2 ≠ 0) {θ : ℝ} (hθ : 1 < |θ|) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|))
    (ha0 : a 0 = 1) (hroot : gen a θ⁻¹ = 0)
    (hm : ∀ t, maOne θ e t - maProc a e t ∈ pastSpan (maProc a e) (t - 1)) (t : ℤ) :
    woldInnov θ (maOne θ e) t ∈ (pastSpan (maProc a e) (t - 1))ᗮ ∧
    maProc a e t - woldInnov θ (maOne θ e) t ∈ pastSpan (maProc a e) (t - 1) ∧
    (haveI : (pastSpan (maProc a e) (t - 1)).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      (pastSpan (maProc a e) (t - 1)).starProjection (maProc a e t)) =
      maProc a e t - woldInnov θ (maOne θ e) t ∧
    ⟪woldInnov θ (maOne θ e) t, woldInnov θ (maOne θ e) t⟫ = θ ^ 2 * σ2 ∧
    (∀ u, u < t → ⟪woldInnov θ (maOne θ e) t, woldInnov θ (maOne θ e) u⟫ = 0) ∧
    maOne θ e t = woldInnov θ (maOne θ e) t - θ⁻¹ • woldInnov θ (maOne θ e) (t - 1) ∧
    e t ∉ pastSpan (maProc a e) t := by
  set s := maProc a e with hs
  set w := woldInnov θ (maOne θ e) with hw
  have hθ0 : θ ≠ 0 := by intro h; rw [h, abs_zero] at hθ; linarith
  have hq : |θ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hθ
  -- orthogonality of `w τ` to the past of `s` at `τ − 1`
  have horth : ∀ τ, w τ ∈ (pastSpan s (τ - 1))ᗮ := by
    intro τ
    refine mem_orthogonal_pastSpan fun k => ?_
    rw [show τ - 1 - (k : ℤ) = τ - ((k + 1 : ℕ) : ℤ) by push_cast; ring, hs,
      inner_wold_maProc he hθ ha τ k, hroot, mul_zero]
  -- `m τ` and `w τ` lie in the past span at `τ`
  have hmS : ∀ τ, maOne θ e τ ∈ pastSpan s τ := by
    intro τ
    have h1 := pastSpan_mono s (show τ - 1 ≤ τ by omega) (hm τ)
    have h2 : s τ ∈ pastSpan s τ := by simpa using mem_pastSpan_self s τ 0
    simpa using Submodule.add_mem _ h1 h2
  have hwS : ∀ τ, w τ ∈ pastSpan s τ := by
    intro τ
    refine hasSum_mem_pastSpan (woldInnov_hasSum he hθ τ) fun k => ?_
    exact Submodule.smul_mem _ _ (pastSpan_mono s (by omega) (hmS (τ - k)))
  have hrec := wold_recursion he hθ t
  have hsub : s t - w t ∈ pastSpan s (t - 1) := by
    have : s t - w t = -(maOne θ e t - s t) - θ⁻¹ • w (t - 1) := by
      rw [hrec]; abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ (hm t)) (Submodule.smul_mem _ _ (hwS _))
  have : (pastSpan s (t - 1)).HasOrthogonalProjection := by
    unfold pastSpan; infer_instance
  have hproj : (pastSpan s (t - 1)).starProjection (s t) = s t - w t :=
    Submodule.eq_starProjection_of_mem_orthogonal hsub (by simpa using horth t)
  -- the variance of `w`
  have hnorm : ⟪w t, w t⟫ = θ ^ 2 * σ2 := by
    have h0 : ⟪w t, s t - w t⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal hsub (horth t)
    have hws : ⟪w t, s t⟫ = θ ^ 2 * σ2 := by
      have h := inner_hasSum_right (maProc_hasSum he ha t) (w t)
      have hsa : Summable (fun i => a i * (θ⁻¹) ^ i) :=
        Summable.of_norm_bounded ha fun i => by
          rw [Real.norm_eq_abs, abs_mul, abs_pow]
          exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hq.le)
      have h2 : HasSum (fun i => σ2 * (1 - θ ^ 2) * (a i * (θ⁻¹) ^ i) +
          (if i = 0 then σ2 * θ ^ 2 * a 0 else 0)) (σ2 * (1 - θ ^ 2) * gen a θ⁻¹ +
          σ2 * θ ^ 2 * a 0) :=
        (hsa.hasSum.mul_left _).add (hasSum_ite_eq 0 _)
      rw [hroot, ha0] at h2
      rw [h.unique (h2.congr_fun fun i => ?_)]
      · ring
      · rw [real_inner_smul_right, real_inner_comm, inner_e_wold he hθ t]
        rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi; simp [ha0]; field_simp; ring
        · simp only [show i ≠ 0 by omega, ↓reduceIte, add_zero]
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
          rw [Nat.succ_sub_one, pow_succ]
          field_simp
    rw [inner_sub_right] at h0
    linarith
  have hwhite : ∀ u, u < t → ⟪w t, w u⟫ = 0 := by
    intro u hu
    exact Submodule.inner_left_of_mem_orthogonal
      (pastSpan_mono s (show u ≤ t - 1 by omega) (hwS u)) (horth t)
  have hnot : e t ∉ pastSpan s t :=
    not_mem_pastSpan_of_aRho_eq_zero he hσ ha hq hroot t
  exact ⟨horth t, hsub, hproj, hnorm, hwhite, hrec, hnot⟩

/-- Cochrane (2023), Online Appendix p. 597 (the lag operator on coefficients): `L a = (0, a₀, a₁,
…)`. -/
def shiftSeq (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => a k

/-- Cochrane (2023), Online Appendix p. 597 (tool): the shifted coefficients are absolutely
summable. -/
theorem summable_abs_shiftSeq {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) :
    Summable (fun k => |shiftSeq a k|) := by
  rw [← summable_nat_add_iff 1]
  exact ha

/-- Cochrane (2023), Online Appendix p. 597 (tool): the lagged moving average,
`∑ (La)_k e_{t−k} = s_{t−1}`. -/
theorem maProc_shift_hasSum [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) :
    HasSum (fun k : ℕ => shiftSeq a k • e (t - k)) (maProc a e (t - 1)) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, shiftSeq, zero_smul, sub_zero]
  refine (maProc_hasSum he ha (t - 1)).congr_fun fun k => ?_
  congr 2
  push_cast
  ring

/-- Cochrane (2023), Online Appendix p. 597 (tool): `maProc (La) e t = maProc a e (t − 1)`. -/
theorem maProc_shiftSeq [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (t : ℤ) :
    maProc (shiftSeq a) e t = maProc a e (t - 1) :=
  (maProc_shift_hasSum he ha t).tsum_eq

/-- Cochrane (2023), Online Appendix eqs. (2.3)–(2.5), (2.32), pp. 595–609 (tool): if the MA
coefficients satisfy the AR(2) recursion with an MA(1) numerator, `a₀ = 1`, `a₁ − φ₁a₀ = −θ`,
`a_{k+2} − φ₁a_{k+1} − φ₂a_k = 0`, then `s_t − φ₁s_{t−1} − φ₂s_{t−2} = e_t − θe_{t−1}` in the
Hilbert space (the ARMA(2,1) `(1 − φ₁L − φ₂L²)s = (1 − θL)e`; ARMA(1,1) when `φ₂ = 0`). -/
theorem ar2_filter_eq_maOne [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) {φ1 φ2 θ : ℝ} (h0 : a 0 = 1)
    (h1 : a 1 - φ1 * a 0 = -θ) (h2 : ∀ k, a (k + 2) - φ1 * a (k + 1) - φ2 * a k = 0) (t : ℤ) :
    maProc a e t - φ1 • maProc a e (t - 1) - φ2 • maProc a e (t - 1 - 1) = maOne θ e t := by
  have hs0 := maProc_hasSum he ha t
  have hs1 := maProc_shift_hasSum he ha t
  have hs2 : HasSum (fun k : ℕ => shiftSeq (shiftSeq a) k • e (t - k))
      (maProc a e (t - 1 - 1)) := by
    have := maProc_shift_hasSum he (summable_abs_shiftSeq ha) t
    rwa [maProc_shiftSeq he ha] at this
  have hc := (hs0.sub (hs1.const_smul φ1)).sub (hs2.const_smul φ2)
  refine hc.unique ?_
  have hval : (∑ k ∈ Finset.range 2, ((a k • e (t - k) - φ1 • shiftSeq a k • e (t - k)) -
      φ2 • shiftSeq (shiftSeq a) k • e (t - k))) = maOne θ e t := by
    have ha1 : a 1 = φ1 - θ := by rw [h0] at h1; linarith
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, shiftSeq, Nat.cast_zero,
      Nat.cast_one, sub_zero, maOne, h0, ha1, one_smul, zero_smul, smul_zero]
    rw [sub_smul]
    abel
  rw [← hval]
  refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
  have hk2 : 2 ≤ k := by simp at hk; omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
  rw [show 2 + j = j + 2 by omega]
  simp only [shiftSeq, smul_smul, ← sub_smul]
  rw [show a (j + 2) - φ1 * a (j + 1) - φ2 * a j = 0 from h2 j, zero_smul]

/-- Cochrane (2023), p. 102 ("an autoregression will estimate `s̃_t = u_t − θu_{t−1}` with
`θ = ρ`"), and Online Appendix (2.13), p. 599 (with `θ = R`): for the MA(1) `s_t = e_t − θe_{t−1}`
with `|θ| > 1` (`θ = ρ⁻¹`, so `a(ρ) = 0`), the Wold innovation `w_t` is the prediction error of
`s_t` on its past, has variance `θ²σ²`, and `s_t = w_t − θ⁻¹w_{t−1}`; the structural shock is not
in the closed span of the surplus history. -/
theorem ma1_wold [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0)
    {θ : ℝ} (hθ : 1 < |θ|) (t : ℤ) :
    maProc (armaCoeff 0 θ) e t = maOne θ e t ∧
    (haveI : (pastSpan (maProc (armaCoeff 0 θ) e) (t - 1)).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      (pastSpan (maProc (armaCoeff 0 θ) e) (t - 1)).starProjection
        (maProc (armaCoeff 0 θ) e t)) =
      maProc (armaCoeff 0 θ) e t - woldInnov θ (maOne θ e) t ∧
    ⟪woldInnov θ (maOne θ e) t, woldInnov θ (maOne θ e) t⟫ = θ ^ 2 * σ2 ∧
    maProc (armaCoeff 0 θ) e t =
      woldInnov θ (maOne θ e) t - θ⁻¹ • woldInnov θ (maOne θ e) (t - 1) ∧
    e t ∉ pastSpan (maProc (armaCoeff 0 θ) e) t := by
  have hθ0 : θ ≠ 0 := by intro h; rw [h, abs_zero] at hθ; linarith
  have ha := summable_abs_armaCoeff (show |(0 : ℝ)| < 1 by simp) θ
  have hfilt : ∀ τ, maProc (armaCoeff 0 θ) e τ = maOne θ e τ := by
    intro τ
    have := ar2_filter_eq_maOne he ha (φ1 := 0) (φ2 := 0) (θ := θ) rfl (by simp [armaCoeff])
      (fun k => by simp [armaCoeff]) τ
    simpa using this
  have hroot : gen (armaCoeff 0 θ) θ⁻¹ = 0 := by
    rw [ma1_aRho, mul_inv_cancel₀ hθ0, sub_self]
  have hm : ∀ τ, maOne θ e τ - maProc (armaCoeff 0 θ) e τ ∈
      pastSpan (maProc (armaCoeff 0 θ) e) (τ - 1) := by
    intro τ
    rw [hfilt τ, sub_self]
    exact Submodule.zero_mem _
  obtain ⟨-, -, hproj, hnorm, -, hrec, hnot⟩ :=
    wold_innovation he hσ hθ ha rfl hroot hm t
  exact ⟨hfilt t, hproj, hnorm, (hfilt t).trans hrec, hnot⟩

/-- Cochrane (2023), Online Appendix eqs. (2.4)–(2.5), p. 597 ("if you generate data by (2.4),
run an autoregression, and find the implied moving average, you recover (2.5)"): for the
ARMA(1,1) `(1 − θL)/(1 − φL)` with `|φ| < 1 < |θ|` (`θ = ρ⁻¹`, so `a(ρ) = 0`), the Wold
innovation `w_t` is the prediction error of `s_t` on its past, has variance `θ²σ²` (= `σ²/ρ²`,
survey E12), and the fitted representation is `s_t − φs_{t−1} = w_t − θ⁻¹w_{t−1}` — the numerator
root `ρ` replaces `ρ⁻¹`; the structural shock is not in the closed span of the surplus history. -/
theorem arma11_wold [CompleteSpace H] {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2)
    (hσ : σ2 ≠ 0) {φ θ : ℝ} (hφ : |φ| < 1) (hθ : 1 < |θ|) (t : ℤ) :
    maProc (armaCoeff φ θ) e t - φ • maProc (armaCoeff φ θ) e (t - 1) =
      woldInnov θ (maOne θ e) t - θ⁻¹ • woldInnov θ (maOne θ e) (t - 1) ∧
    (haveI : (pastSpan (maProc (armaCoeff φ θ) e) (t - 1)).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      (pastSpan (maProc (armaCoeff φ θ) e) (t - 1)).starProjection
        (maProc (armaCoeff φ θ) e t)) =
      maProc (armaCoeff φ θ) e t - woldInnov θ (maOne θ e) t ∧
    ⟪woldInnov θ (maOne θ e) t, woldInnov θ (maOne θ e) t⟫ = θ ^ 2 * σ2 ∧
    e t ∉ pastSpan (maProc (armaCoeff φ θ) e) t := by
  have hθ0 : θ ≠ 0 := by intro h; rw [h, abs_zero] at hθ; linarith
  have ha := summable_abs_armaCoeff hφ θ
  have hfilt : ∀ τ, maProc (armaCoeff φ θ) e τ - φ • maProc (armaCoeff φ θ) e (τ - 1) =
      maOne θ e τ := by
    intro τ
    have := ar2_filter_eq_maOne he ha (φ1 := φ) (φ2 := 0) (θ := θ) rfl
      (by simp [armaCoeff]) (fun k => by simp [armaCoeff]; ring) τ
    simpa using this
  have hinv : |θ⁻¹| ≤ 1 := by rw [abs_inv]; exact inv_le_one_of_one_le₀ hθ.le
  have hφθ : |φ * θ⁻¹| < 1 := by
    rw [abs_mul]
    calc |φ| * |θ⁻¹| ≤ |φ| * 1 := mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
      _ < 1 := by linarith
  have hroot : gen (armaCoeff φ θ) θ⁻¹ = 0 := by
    rw [genFn_armaCoeff hφθ, mul_inv_cancel₀ hθ0, sub_self, zero_div]
  have hm : ∀ τ, maOne θ e τ - maProc (armaCoeff φ θ) e τ ∈
      pastSpan (maProc (armaCoeff φ θ) e) (τ - 1) := by
    intro τ
    rw [← hfilt τ, show maProc (armaCoeff φ θ) e τ - φ • maProc (armaCoeff φ θ) e (τ - 1) -
      maProc (armaCoeff φ θ) e τ = -(φ • maProc (armaCoeff φ θ) e (τ - 1)) by abel]
    refine Submodule.neg_mem _ (Submodule.smul_mem _ _ ?_)
    simpa using mem_pastSpan_self (maProc (armaCoeff φ θ) e) (τ - 1) 0
  obtain ⟨-, -, hproj, hnorm, -, hrec, hnot⟩ :=
    wold_innovation he hσ hθ ha rfl hroot hm t
  exact ⟨(hfilt t).trans hrec, hproj, hnorm, hnot⟩

end Hilbert

end Cochrane.DebtDeficitsInflation.Invertibility
