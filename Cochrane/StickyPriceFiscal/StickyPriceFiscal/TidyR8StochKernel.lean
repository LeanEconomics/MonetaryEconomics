/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR7StochCTUnique

/-!
# Two-mode Wiener integrals, discounting by parts, and brackets with `W`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §§5.7.2–5.7.5,
pp. 167–179, and Online Appendix A1, §§1.12–1.13, pp. 579–585: tools for the stochastic
versions of the s-shaped surplus, the bond price and the policy rules with Brownian shocks.

The responses of §§5.7.2–5.7.5 to an MIT shock are sums of a constant and decaying
exponentials (`CTSurplus.expSum`). With one Brownian motion `W`, the stochastic solution is the
response integrated against `dW`, and on every path it is a combination of `W` and the OU noises
`Y^η = ∫ e^{−η(t−u)} dW_u` (`TidyR7StochCTPath.ouNoise`). This module extends T8's one-mode
kernels (`TidyR7StochCTBrownian.kerProc`) to two modes.

## Main results

* `ker2Proc`, `ker2Proc_ae_eq_itoInt`: `cW_T + d₁Y^{η₁}_T + d₂Y^{η₂}_T` is a.s. the Wiener
  integral `∫_0^T (c + d₁e^{−η₁(T−u)} + d₂e^{−η₂(T−u)}) dW_u`; `condExp_ker2Proc` (forecasts
  decay each mode), `condExp_ker2Proc_itoInt` (the moving-average form of A1 §1.13),
  `integral_ker2Proc_sq` (the isometry), `integral_abs_ker2Proc_le`, `regProc_ker2Proc`,
  `tendsto_condExp_exp_ker2` (the discounted forecast vanishes in `L¹`).
* `expWiener`, `expWiener_ae_eq_itoInt`, `condExp_expWiener`: the discounted Wiener integral
  `∫_t^T e^{−a(τ−t)} dW_τ` in by-parts form, and `E_t[·]` of it is `0`.
* **`discounted_byParts`** (the product rule for `e^{−aτ}X_τ` with `X = F + kw`, `F` of class
  `C¹`, on every continuous path): `∫_t^T e^{−a(τ−t)}(aX − F') = X_t − e^{−a(T−t)}X_T +
  k∫_t^T e^{−a(τ−t)}dw`. This is how every present-value identity of §§5.7.2–5.7.5 is proved
  with a diffusive state; there is no Itô term because `e^{−aτ}` is deterministic.
* **`tendsto_crossSum_affine`** (the bracket): if `X = aW + F`, `Y = bW + G` with `F`, `G` of
  class `C¹` on every path, then a.s. along the dyadic partitions of `[s, t]`
  `Σ ΔX ΔY → ab(t − s)`: `[X, Y] = ab t`. Only the `dW`-loadings enter.
-/

namespace Cochrane.StickyPriceFiscal.TidyR8StochKernel

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.StickyPriceFiscal.TidyR7StieltjesSums Cochrane.StickyPriceFiscal.TidyR7BrownianTools
open Cochrane.StickyPriceFiscal.TidyR7BrownianQV Cochrane.StickyPriceFiscal.TidyR7ItoL2
open Cochrane.StickyPriceFiscal.TidyR7ItoSums Cochrane.StickyPriceFiscal.TidyR7ItoIntegral
open Cochrane.StickyPriceFiscal.TidyR7ItoBridge Cochrane.StickyPriceFiscal.TidyR7BrownianExist
open Cochrane.StickyPriceFiscal.TidyR7StieltjesCalculus
open Cochrane.StickyPriceFiscal.TidyR7StochCTPath Cochrane.StickyPriceFiscal.TidyR7StochCTBrownian
open Cochrane.StickyPriceFiscal.TidyR7StochCTUnique
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-! ### Two-mode kernels -/

/-- Cochrane (2023), (5.101), p. 168: a two-mode response kernel
`R(τ) = c + d₁e^{−η₁τ} + d₂e^{−η₂τ}`. -/
noncomputable def ker2Fn (c d₁ η₁ d₂ η₂ τ : ℝ) : ℝ :=
  c + d₁ * exp (-(η₁ * τ)) + d₂ * exp (-(η₂ * τ))

/-- Cochrane (2023), (5.101), p. 168: the process `cW_T + d₁Y^{η₁}_T + d₂Y^{η₂}_T` on the
Brownian path (`Y^η` the OU noise). -/
noncomputable def ker2Proc (W : ℝ≥0 → Ω → ℝ) (c d₁ η₁ d₂ η₂ T : ℝ) (ω : Ω) : ℝ :=
  kerProc W c d₁ η₁ T ω + kerProc W 0 d₂ η₂ T ω

/-- Cochrane (2023), (5.101), p. 168: the two-mode kernel is the sum of two one-mode kernels.
The sum of two `TidyR7StochCTBrownian.kerFn` kernels. -/
theorem ker2Fn_eq (c d₁ η₁ d₂ η₂ τ : ℝ) :
    ker2Fn c d₁ η₁ d₂ η₂ τ = kerFn c d₁ η₁ τ + kerFn 0 d₂ η₂ τ := by
  simp only [ker2Fn, kerFn]
  ring

/-- Cochrane (2023), (5.101), p. 168: the kernel is continuous in the integration variable. -/
theorem continuous_ker2Fn (c d₁ η₁ d₂ η₂ T : ℝ) :
    Continuous fun u => ker2Fn c d₁ η₁ d₂ η₂ (T - u) := by
  unfold ker2Fn
  fun_prop

/-- Cochrane (2023), (5.101), p. 168: on a path, the process is `cw + d₁Y^{η₁} + d₂Y^{η₂}`. -/
theorem ker2Proc_eq (c d₁ η₁ d₂ η₂ T : ℝ) (ω : Ω) :
    ker2Proc W c d₁ η₁ d₂ η₂ T ω = c * bmReal W T ω
      + d₁ * ouNoise η₁ (fun u => bmReal W u ω) T + d₂ * ouNoise η₂ (fun u => bmReal W u ω) T := by
  simp only [ker2Proc, kerProc]
  ring

/-- **Cochrane (2023), (5.101), p. 168: the two-mode process is the Wiener integral of the
two-mode response**, `ker2Proc_T = ∫_0^T R(T − u) dW_u` a.s. for `T ≥ 0`.
The two-mode version of `TidyR7StochCTBrownian.kerProc_ae_eq_itoInt`. -/
theorem ker2Proc_ae_eq_itoInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d₁ η₁ d₂ η₂ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ker2Proc W c d₁ η₁ d₂ η₂ T =ᵐ[P]
      itoInt P 𝓕 W (fun u _ => ker2Fn c d₁ η₁ d₂ η₂ (T - u)) 0 T := by
  obtain ⟨C₁, h₁⟩ := exists_itoIntegrand_kerFn (P := P) (𝓕 := 𝓕) c d₁ η₁ T 0 T
  obtain ⟨C₂, h₂⟩ := exists_itoIntegrand_kerFn (P := P) (𝓕 := 𝓕) 0 d₂ η₂ T 0 T
  have hadd := itoInt_add hB hW h𝓕 le_rfl h₁ h₂
  have e : (fun u (_ : Ω) => ker2Fn c d₁ η₁ d₂ η₂ (T - u))
      = fun u ω => (fun u (_ : Ω) => kerFn c d₁ η₁ (T - u)) u ω
        + (fun u (_ : Ω) => kerFn 0 d₂ η₂ (T - u)) u ω := by
    funext u ω
    exact ker2Fn_eq c d₁ η₁ d₂ η₂ (T - u)
  rw [e]
  filter_upwards [hadd, kerProc_ae_eq_itoInt hB hW h𝓕 hcont hW0 c d₁ η₁ hT,
    kerProc_ae_eq_itoInt hB hW h𝓕 hcont hW0 0 d₂ η₂ hT] with ω h1 h2 h3
  rw [h1, ker2Proc, h2, h3]

/-- Cochrane (2023), (5.101), p. 168: the two-mode process is square integrable.
The two-mode version of `TidyR7StochCTBrownian.memLp_kerProc`. -/
theorem memLp_ker2Proc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d₁ η₁ d₂ η₂ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    MemLp (ker2Proc W c d₁ η₁ d₂ η₂ T) 2 P :=
  (memLp_kerProc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 c d₁ η₁ hT).add
    (memLp_kerProc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 0 d₂ η₂ hT)

/-- Cochrane (2023), (5.101), p. 168: the two-mode process is integrable.
The two-mode version of `TidyR7StochCTBrownian.integrable_kerProc`. -/
theorem integrable_ker2Proc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d₁ η₁ d₂ η₂ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (ker2Proc W c d₁ η₁ d₂ η₂ T) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact (memLp_ker2Proc hB hW h𝓕 hcont hW0 c d₁ η₁ d₂ η₂ hT).integrable one_le_two

/-- Cochrane (2023), (5.101), p. 168: the two-mode process is adapted.
The two-mode version of `TidyR7StochCTBrownian.aesm_kerProc`. -/
theorem aesm_ker2Proc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d₁ η₁ d₂ η₂ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    AEStronglyMeasurable[𝓕 T] (ker2Proc W c d₁ η₁ d₂ η₂ T) P :=
  ⟨_, stronglyMeasurable_itoInt, ker2Proc_ae_eq_itoInt hB hW h𝓕 hcont hW0 c d₁ η₁ d₂ η₂ hT⟩

/-- **Cochrane (2023), §5.7.2, p. 168 and A1 §1.13 (forecasts of a two-mode process)**: for
`0 ≤ t ≤ T`, `E_t[ker2Proc_T]` is the two-mode process at `t` with each mode decayed,
`cW_t + d₁e^{−η₁(T−t)}Y^{η₁}_t + d₂e^{−η₂(T−t)}Y^{η₂}_t`, a.s.
The two-mode version of `TidyR7StochCTBrownian.condExp_kerProc`. -/
theorem condExp_ker2Proc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d₁ η₁ d₂ η₂ : ℝ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    P[ker2Proc W c d₁ η₁ d₂ η₂ T | 𝓕 t] =ᵐ[P]
      ker2Proc W c (d₁ * exp (-(η₁ * (T - t)))) η₁ (d₂ * exp (-(η₂ * (T - t)))) η₂ t := by
  have i1 := integrable_kerProc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 c d₁ η₁ (ht.trans htT)
  have i2 := integrable_kerProc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 0 d₂ η₂ (ht.trans htT)
  have e : ker2Proc W c d₁ η₁ d₂ η₂ T = kerProc W c d₁ η₁ T + kerProc W 0 d₂ η₂ T := rfl
  rw [e]
  filter_upwards [condExp_add i1 i2 (𝓕 t), condExp_kerProc hB hW h𝓕 hcont hW0 c d₁ η₁ ht htT,
    condExp_kerProc hB hW h𝓕 hcont hW0 0 d₂ η₂ ht htT] with ω h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]
  rfl

/-- **Cochrane (2023), A1 §1.13, p. 581 (moving-average form of forecasts)**: for
`0 ≤ t ≤ T`, `E_t[ker2Proc_T] = ∫_0^t R(T − u) dW_u` a.s.
The two-mode version of `TidyR7StochCTBrownian.condExp_kerProc_itoInt`. -/
theorem condExp_ker2Proc_itoInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d₁ η₁ d₂ η₂ : ℝ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    P[ker2Proc W c d₁ η₁ d₂ η₂ T | 𝓕 t] =ᵐ[P]
      itoInt P 𝓕 W (fun u _ => ker2Fn c d₁ η₁ d₂ η₂ (T - u)) 0 t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc 0 T)
    (continuous_ker2Fn c d₁ η₁ d₂ η₂ T).continuousOn
  have hI : ItoIntegrand P 𝓕 (fun u _ => ker2Fn c d₁ η₁ d₂ η₂ (T - u)) 0 T C :=
    itoIntegrand_deterministic (continuous_ker2Fn c d₁ η₁ d₂ η₂ T).continuousOn fun u hu => by
      simpa [Real.norm_eq_abs] using hC u hu
  exact (condExp_congr_ae (ker2Proc_ae_eq_itoInt hB hW h𝓕 hcont hW0 c d₁ η₁ d₂ η₂
    (ht.trans htT))).trans (condExp_itoInt hB hW h𝓕 le_rfl ht htT hI)

/-- Cochrane (2023), (5.101), p. 168: the variance of the two-mode process is
`∫_0^T R(T − u)² du` (the Wiener isometry).
The two-mode version of `TidyR7StochCTBrownian.integral_kerProc_sq`. -/
theorem integral_ker2Proc_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d₁ η₁ d₂ η₂ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, ker2Proc W c d₁ η₁ d₂ η₂ T ω ^ 2 ∂P
      = ∫ u in (0 : ℝ)..T, ker2Fn c d₁ η₁ d₂ η₂ (T - u) ^ 2 := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc 0 T)
    (continuous_ker2Fn c d₁ η₁ d₂ η₂ T).continuousOn
  rw [← integral_itoInt_deterministic_sq (𝓕 := 𝓕) hB hW h𝓕 le_rfl hT
    (continuous_ker2Fn c d₁ η₁ d₂ η₂ T).continuousOn (fun u hu => by
      simpa [Real.norm_eq_abs] using hC u hu)]
  refine integral_congr_ae ?_
  filter_upwards [ker2Proc_ae_eq_itoInt hB hW h𝓕 hcont hW0 c d₁ η₁ d₂ η₂ hT] with ω hω
  simp only [hω]

/-- Cochrane (2023), (5.101), p. 168: with nonnegative rates the kernel is bounded on
`[0, ∞)`, `|R(τ)| ≤ |c| + |d₁| + |d₂|`. -/
theorem abs_ker2Fn_le {c d₁ η₁ d₂ η₂ τ : ℝ} (h₁ : 0 ≤ η₁) (h₂ : 0 ≤ η₂) (hτ : 0 ≤ τ) :
    |ker2Fn c d₁ η₁ d₂ η₂ τ| ≤ |c| + |d₁| + |d₂| := by
  have e1 : exp (-(η₁ * τ)) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  have e2 : exp (-(η₂ * τ)) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  unfold ker2Fn
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
  · rw [abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_right (abs_nonneg _) e1
  · rw [abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_right (abs_nonneg _) e2

/-- Cochrane (2023), (5.101), p. 168: with nonnegative rates, `E|X_T| ≤ 1 + T(|c|+|d₁|+|d₂|)²`
for `T ≥ 0`.
Generalises `TidyR7StochCTBrownian.integral_abs_vProc_le`. -/
theorem integral_abs_ker2Proc_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {c d₁ η₁ d₂ η₂ : ℝ} (h₁ : 0 ≤ η₁) (h₂ : 0 ≤ η₂) {T : ℝ}
    (hT : 0 ≤ T) :
    ∫ ω, |ker2Proc W c d₁ η₁ d₂ η₂ T ω| ∂P ≤ 1 + T * (|c| + |d₁| + |d₂|) ^ 2 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm := memLp_ker2Proc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 c d₁ η₁ d₂ η₂ hT
  have hsq := hm.integrable_sq
  have h1 : ∫ ω, |ker2Proc W c d₁ η₁ d₂ η₂ T ω| ∂P
      ≤ ∫ ω, (1 + ker2Proc W c d₁ η₁ d₂ η₂ T ω ^ 2) ∂P :=
    integral_mono (hm.integrable one_le_two).abs ((integrable_const 1).add hsq) fun ω => by
      have := abs_nonneg (ker2Proc W c d₁ η₁ d₂ η₂ T ω)
      have := sq_abs (ker2Proc W c d₁ η₁ d₂ η₂ T ω)
      nlinarith
  have h2 : ∫ u in (0 : ℝ)..T, ker2Fn c d₁ η₁ d₂ η₂ (T - u) ^ 2
      ≤ ∫ u in (0 : ℝ)..T, (|c| + |d₁| + |d₂|) ^ 2 := by
    refine intervalIntegral.integral_mono_on hT
      (((continuous_ker2Fn c d₁ η₁ d₂ η₂ T).pow 2).intervalIntegrable 0 T)
      intervalIntegrable_const fun u hu => ?_
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_ker2Fn_le h₁ h₂ (by linarith [hu.2])) 2
  rw [integral_add (integrable_const 1) hsq,
    integral_ker2Proc_sq hB hW h𝓕 hcont hW0 c d₁ η₁ d₂ η₂ hT] at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h2
  linarith

/-- Cochrane (2023), (5.101), p. 168: with nonnegative rates the two-mode process is regular
(`TidyR7StochCTUnique.RegProc`).
The two-mode version of `TidyR7StochCTUnique.regProc_kerProc`. -/
theorem regProc_ker2Proc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {η₁ η₂ : ℝ} (h₁ : 0 ≤ η₁) (h₂ : 0 ≤ η₂) (c d₁ d₂ : ℝ) :
    RegProc P (ker2Proc W c d₁ η₁ d₂ η₂) :=
  ((regProc_kerProc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 h₁ c d₁).lin
    (regProc_kerProc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 h₂ 0 d₂) 1 1).congr
    (by funext t ω; simp only [ker2Proc, one_mul])

/-- **Cochrane (2023), §5.7.1–§5.7.3 (transversality under uncertainty, two modes)**: for
`a > 0`, nonnegative rates and `t ≥ 0`, `E_t[e^{−a(T−t)}X_T] → 0` in `L¹` as `T → ∞`.
The two-mode version of `TidyR7StochCTBrownian.tvc_L1`. -/
theorem tendsto_condExp_exp_ker2 (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {a c d₁ η₁ d₂ η₂ : ℝ} (ha : 0 < a) (h₁ : 0 ≤ η₁) (h₂ : 0 ≤ η₂)
    (t : ℝ) :
    Tendsto (fun T => ∫ ω, |P[fun ω => exp (-(a * (T - t))) * ker2Proc W c d₁ η₁ d₂ η₂ T ω
      | 𝓕 t] ω| ∂P) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _)
    ?_ (tendsto_exp_mul_affine ha t ((|c| + |d₁| + |d₂|) ^ 2))
  filter_upwards [eventually_ge_atTop 0] with T hT
  refine (integral_abs_condExp_le _).trans ?_
  have e : (fun ω => |exp (-(a * (T - t))) * ker2Proc W c d₁ η₁ d₂ η₂ T ω|)
      = fun ω => exp (-(a * (T - t))) * |ker2Proc W c d₁ η₁ d₂ η₂ T ω| := by
    funext ω
    rw [abs_mul, abs_of_pos (exp_pos _)]
  rw [e, integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_abs_ker2Proc_le hB hW h𝓕 hcont hW0 h₁ h₂ hT)
    (exp_pos _).le

/-! ### Discounted Wiener integrals -/

/-- Cochrane (2023), §5.7.2, p. 168 (Hansen–Sargent): the discounted Wiener integral
`∫_t^T e^{−a(τ−t)} dW_τ` in by-parts form,
`e^{−a(T−t)}W_T − W_t + a∫_t^T e^{−a(τ−t)}W_τ dτ`. -/
noncomputable def expWiener (a : ℝ) (W : ℝ≥0 → Ω → ℝ) (t T : ℝ) (ω : Ω) : ℝ :=
  exp (-(a * (T - t))) * bmReal W T ω - bmReal W t ω
    + a * ∫ τ in t..T, exp (-(a * (τ - t))) * bmReal W τ ω

/-- Cochrane (2023), §5.7.2, p. 168: the discount factor `u ↦ e^{−a(u−t)}` is an admissible
deterministic integrand on `[t, T]`.
The analogue of `TidyR7StochCTBrownian.exists_itoIntegrand_kerFn`. -/
theorem exists_itoIntegrand_exp (a t T : ℝ) :
    ∃ C, ItoIntegrand P 𝓕 (fun u _ => exp (-(a * (u - t)))) t T C := by
  have hc : Continuous fun u : ℝ => exp (-(a * (u - t))) := by fun_prop
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc t T)
    hc.continuousOn
  exact ⟨C, itoIntegrand_deterministic hc.continuousOn fun u hu => by
    simpa [Real.norm_eq_abs] using hC u hu⟩

/-- **Cochrane (2023), §5.7.2, p. 168: the by-parts form is the Itô integral**,
`expWiener a t T = ∫_t^T e^{−a(u−t)} dW_u` a.s. for `0 ≤ t ≤ T`.
A special case of `TidyR7StochCTBrownian.itoInt_ae_eq_wienerBP`. -/
theorem expWiener_ae_eq_itoInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) (a : ℝ) {t T : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) :
    expWiener a W t T =ᵐ[P] itoInt P 𝓕 W (fun u _ => exp (-(a * (u - t)))) t T := by
  rcases htT.lt_or_eq with hlt | heq
  · have hh : ∀ x, HasDerivAt (fun u => exp (-(a * (u - t))))
        (-a * exp (-(a * (x - t)))) x := by
      intro x
      have h1 : HasDerivAt (fun u => -(a * (u - t))) (-a) x := by
        have := (((hasDerivAt_id' x).sub_const t).const_mul a).neg
        exact this.congr_deriv (by ring)
      exact h1.exp.congr_deriv (by ring)
    refine ((itoInt_ae_eq_wienerBP hB hW h𝓕 hcont hh (by fun_prop) ht hlt).trans
      (ae_of_all _ fun ω => ?_)).symm
    simp only [wienerBP, expWiener, sub_self, mul_zero, neg_zero, exp_zero, one_mul]
    have e : (fun u => bmReal W u ω * (-a * exp (-(a * (u - t)))))
        = fun u => -a * (exp (-(a * (u - t))) * bmReal W u ω) := by
      funext u
      ring
    rw [e, intervalIntegral.integral_const_mul]
    ring
  · subst heq
    rw [itoInt_of_le le_rfl]
    exact ae_of_all _ fun ω => by simp [expWiener]

/-- **Cochrane (2023), §5.7.2, p. 168: `E_t∫_t^T e^{−a(τ−t)} dW_τ = 0`** a.s. for
`0 ≤ t ≤ T`.
An instance of `TidyR7ItoIntegral.condExp_itoInt`. -/
theorem condExp_expWiener (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) (a : ℝ) {t T : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) :
    P[expWiener a W t T | 𝓕 t] =ᵐ[P] 0 := by
  obtain ⟨C, hC⟩ := exists_itoIntegrand_exp (P := P) (𝓕 := 𝓕) a t T
  refine (condExp_congr_ae (expWiener_ae_eq_itoInt hB hW h𝓕 hcont a ht htT)).trans ?_
  refine (condExp_itoInt hB hW h𝓕 ht le_rfl htT hC).trans ?_
  rw [itoInt_of_le le_rfl]

/-- Cochrane (2023), §5.7.2, p. 168: the discounted Wiener integral is integrable. -/
theorem integrable_expWiener (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) (a : ℝ) {t T : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) : Integrable (expWiener a W t T) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hC⟩ := exists_itoIntegrand_exp (P := P) (𝓕 := 𝓕) a t T
  exact ((memLp_itoInt hB hW h𝓕 ht hC).integrable one_le_two).congr
    (expWiener_ae_eq_itoInt hB hW h𝓕 hcont a ht htT).symm

/-- **Cochrane (2023), §§5.7.2–5.7.3 (discounting a diffusive state, on a path).** If `F` is
`C¹` with continuous derivative `F'`, `w` is continuous and `X = F + kw`, then for all `t, T`,
`∫_t^T e^{−a(τ−t)}(aX_τ − F'_τ)dτ = X_t − e^{−a(T−t)}X_T
  + k(e^{−a(T−t)}w_T − w_t + a∫_t^T e^{−a(τ−t)}w_τ dτ)`
(the last bracket is `∫_t^T e^{−a(τ−t)} dw` by parts). -/
theorem discounted_byParts {F F' w : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
    (hF' : Continuous F') (hw : Continuous w) (a k t T : ℝ) :
    ∫ τ in t..T, exp (-(a * (τ - t))) * (a * (F τ + k * w τ) - F' τ)
      = (F t + k * w t) - exp (-(a * (T - t))) * (F T + k * w T)
        + k * (exp (-(a * (T - t))) * w T - w t
          + a * ∫ τ in t..T, exp (-(a * (τ - t))) * w τ) := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hF x).continuousAt
  have hE : ∀ τ, HasDerivAt (fun τ => exp (-(a * (τ - t)))) (exp (-(a * (τ - t))) * -a) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ => -(a * (τ - t))) (-a) τ := by
      have := (((hasDerivAt_id' τ).sub_const t).const_mul a).neg
      exact this.congr_deriv (by ring)
    exact h1.exp
  have hG : ∀ τ, HasDerivAt (fun τ => -(exp (-(a * (τ - t))) * F τ))
      (exp (-(a * (τ - t))) * (a * F τ - F' τ)) τ := fun τ =>
    ((hE τ).mul (hF τ)).neg.congr_deriv (by ring)
  have c1 : Continuous fun τ => exp (-(a * (τ - t))) * (a * F τ - F' τ) := by fun_prop
  have c2 : Continuous fun τ => exp (-(a * (τ - t))) * w τ := by fun_prop
  have hsplit : (fun τ => exp (-(a * (τ - t))) * (a * (F τ + k * w τ) - F' τ))
      = fun τ => exp (-(a * (τ - t))) * (a * F τ - F' τ)
        + (a * k) * (exp (-(a * (τ - t))) * w τ) := by
    funext τ
    ring
  rw [hsplit, intervalIntegral.integral_add (c1.intervalIntegrable t T)
    ((c2.const_mul _).intervalIntegrable t T), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG x) (c1.intervalIntegrable t T)]
  simp only [sub_self, mul_zero, neg_zero, exp_zero, one_mul]
  ring

/-! ### Brackets with `W` -/

/-- Cochrane (2023), A1 §1.6, p. 567 (tool): the cross sum is bilinear,
`Σ Δ(aw + F)Δ(bw + G) = ab Σ(Δw)² + a ΣΔwΔG + b ΣΔFΔw + ΣΔFΔG`. -/
theorem crossSum_affine {s t : ℝ} (p : Partition s t) (a b : ℝ) (w F G : ℝ → ℝ) :
    crossSum p (fun u => a * w u + F u) (fun u => b * w u + G u)
      = a * b * crossSum p w w + a * crossSum p w G + b * crossSum p F w + crossSum p F G := by
  simp only [crossSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Cochrane (2023), §5.7.2, p. 168, and A1 §1.6 (the bracket of two diffusive states).** If
on every path `X = aW + F` and `Y = bW + G` with `F, G` of class `C¹` (continuous derivatives),
then for `0 ≤ s < t`, a.s. along the dyadic partitions of `[s, t]`,
`Σ ΔX_i ΔY_i → ab(t − s)`: only the `dW`-loadings enter `[X, Y]`.
Generalises `TidyR7BrownianQV.ae_tendsto_qvSum_dyadic` and
`TidyR7StochCTBrownian.crossSum_v_tendsto_zero`. -/
theorem tendsto_crossSum_affine (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (a b : ℝ)
    {F G F' G' : Ω → ℝ → ℝ} (hF : ∀ ω x, HasDerivAt (F ω) (F' ω x) x)
    (hF' : ∀ ω, Continuous (F' ω)) (hG : ∀ ω x, HasDerivAt (G ω) (G' ω x) x)
    (hG' : ∀ ω, Continuous (G' ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => crossSum (dyadic hst k)
      (fun u => a * bmReal W u ω + F ω u) (fun u => b * bmReal W u ω + G ω u))
      atTop (𝓝 (a * b * (t - s))) := by
  filter_upwards [ae_tendsto_qvSum_dyadic hB hW hs hst] with ω hω
  have hw := continuous_bmReal (hcont ω)
  have hFc : Continuous (F ω) := continuous_iff_continuousAt.2 fun x => (hF ω x).continuousAt
  have hm := tendsto_mesh_dyadic hst
  have hGbv := bv_of_hasDerivAt (hG ω) (hG' ω) hst.le
  have hFbv := bv_of_hasDerivAt (hF ω) (hF' ω) hst.le
  have t1 := tendsto_crossSum_zero_of_continuousOn hw.continuousOn hGbv _ hm
  have t2 := tendsto_crossSum_zero_of_continuousOn hw.continuousOn hFbv _ hm
  have t3 := tendsto_crossSum_zero_of_continuousOn hFc.continuousOn hGbv _ hm
  simp_rw [qvSum_eq_crossSum] at hω
  have hlim := (((hω.const_mul (a * b)).add (t1.const_mul a)).add
    ((t2.const_mul b).congr fun k => by rw [crossSum_comm])).add t3
  simp only [mul_zero, add_zero] at hlim
  refine hlim.congr fun k => ?_
  rw [crossSum_affine]

end Cochrane.StickyPriceFiscal.TidyR8StochKernel
