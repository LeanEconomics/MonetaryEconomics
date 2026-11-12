/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7ItoDiscountFactorCex
import Generality.ContinuousLinear

/-!
# Innovations of Itô processes (3.44)–(3.45) and the AR(1) surplus

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6.3, pp. 76–77,
eqs. (3.44)–(3.45) and the AR(1) example after them. The book writes a process as
`dx_t = μ_t dt + σ_t dz_t`, `E_t dz_t = 0`, so `E_t(dx_t) = μ_t dt` and the innovation is
`Δ_t(dx_t) = dx_t − E_t(dx_t) = σ_t dz_t` (3.45); conditional expectations `y_t = E_t x_{t+τ}`
follow such a process (3.44) and their innovation is again the `dz` part. The deterministic
project (`ContinuousLinear`) represents an innovation as the difference of two perfect-foresight
paths (`ContinuousLinear.ar1_news`); here the innovation is the genuine stochastic one.

## General Itô processes (`dz` a Brownian motion)

For `x` an Itô process on `[s, t]` with drift `a` (bounded by `C`) and diffusion `H`:
* `expected_increment`: `E_s[x_t − x_s] = E_s[∫_s^t a du]` (the book's `E_t dx = μ dt`);
* `innovation_eq`: `x_t − E_s[x_t] = ∫_s^t H dW + (∫_s^t a − E_s∫_s^t a)` a.s. — the
  innovation is the `dW` integral plus the unexpected part of the drift;
* `innovation_sq_le`: `E[(x_t − E_s x_t − ∫_s^t H dW)²] ≤ (2C(t − s))²`, while
  `E[(∫_s^t H dW)²] = E∫_s^t H² ≥ c²(t − s)` if `H² ≥ c²`: `innovation_relative`,
  `c²·E[(x_t − E_s x_t − ∫H dW)²] ≤ (2C)²(t − s)·E[(∫H dW)²]`. **(3.45) is exact to first order:
  the innovation is `σ dz` up to a term whose mean square is `O((t − s)²)`, against `O(t − s)` for
  `σ dz`.** It is not exact at finite `t − s` (the drift may itself be random).

## The AR(1) surplus `ds = −η s dt + σ dε` (p. 77)

`ou η σ s₀`: `s_u = e^{−ηu}(s₀ + σ∫_0^u e^{ηv} dW_v)` (a Wiener integral; no existence
result for SDEs is needed):
* `ou_sde`: `s_t − s_r = −η∫_r^t s du + σ(W_t − W_r)` a.s. (Itô's product rule): it is the
  book's AR(1);
* `ou_condExp`: `E_r s_t = e^{−η(t−r)} s_r` (the book's `E_t s_{t+τ} = e^{−ητ}s_t`; its printed
  `+ s` is not part of the forecast, cf. `ContinuousLinear.ar1_printed_not_solution`);
* `pv_expected_path`: `∫_0^∞ e^{−rτ}E_t s_{t+τ} dτ = s_t/(r + η)`;
* `ou_innovation`: `s_t − E_r s_t = σe^{−ηt}∫_r^t e^{ηv} dW_v`; `ou_innovation_sq_le`:
  `E[(s_t − E_r s_t − σ(W_t − W_r))²] ≤ σ²η²(t − r)³` (`η ≥ 0`): **`Δ s = σ dε`**;
* `forecast_condExp`, `forecast_sde`, `forecast_innovation` (3.44): the forecast
  `y_u = E_u s_{u+τ} = e^{−ητ}s_u` follows `dy = −ηy du + e^{−ητ}σ dε`, innovation
  `e^{−ητ}σ dε` up to `O`-terms;
* `pv_innovation`, `pv_innovation_sq_le`: **the innovation of the present value is
  `σ/(r + η) dε`** (p. 77): `PV_t − E_r PV_t = (σ/(r + η))e^{−ηt}∫_r^t e^{ηv}dW`, within mean
  square `σ²η²(t − r)³/(r + η)²` of `(σ/(r + η))(W_t − W_r)`;
* `news_link`: for almost every `ω`, the two perfect-foresight paths `τ ↦ e^{−ητ}E_r s_t` and
  `τ ↦ e^{−ητ}s_t` are the deterministic project's old and new paths, and
  `ContinuousLinear.ar1_news` turns the stochastic innovation into the present-value news;
* `ou_sigma_zero`: with `σ = 0` the process is the deterministic `e^{−ηu}s₀`
  (`ContinuousLinear.ar1_hasDerivAt`) and the innovation vanishes.

## Non-vacuity

`ou_innovation_sq_eq`: `E[(s_t − E_r s_t)²] = ∫_r^t (σe^{−η(t−v)})² dv`, and on the constructed
motion `bmPath`, `ou_bmPath_innovation_pos`: it is `> 0` for `σ ≠ 0`, `r < t`.
-/

namespace Cochrane.Generality.TidyR7ItoInnovation

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
  Cochrane.Generality.TidyR7ItoUnbounded Cochrane.Generality.TidyR7ItoProducts
  Cochrane.Generality.TidyR7ItoProcess Cochrane.Generality.TidyR7ItoProductRule
  Cochrane.Generality.TidyR7ItoBondStep Cochrane.Generality.TidyR7ItoBridge
  Cochrane.Generality.TidyR7BrownianExist Cochrane.Generality.TidyR7BrownianSchauder
  Cochrane.Generality.TidyR7ItoDiscountFactor Cochrane.Generality.TidyR7ItoDiscountFactorCex
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ} {s t : ℝ}

/-! ## (3.44)–(3.45) for a general Itô process -/

/-- **Cochrane (2023), §3.6.3, p. 76 (`E_t(dx_t) = μ_t dt`, `E_t dz_t = 0`):** for an Itô process
`x` on `[s, t]`, `0 ≤ s ≤ t`, with drift `a`, a.s. `E_s[x_t − x_s] = E_s[∫_s^t a du]`. -/
theorem expected_increment (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess μ 𝓕 W X a H s t Ca CH) :
    μ[fun ω => X t ω - X s ω | 𝓕 s] =ᵐ[μ] μ[fun ω => ∫ r in s..t, a r ω | 𝓕 s] := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have e : (fun ω => X t ω - X s ω) =ᵐ[μ]
      (fun ω => ∫ r in s..t, a r ω) + itoInt μ 𝓕 W H s t := by
    filter_upwards [hX.eq t ⟨hst, le_rfl⟩] with ω hω
    simp only [Pi.add_apply]
    rw [hω]
    ring
  have h0 : μ[itoInt μ 𝓕 W H s t | 𝓕 s] =ᵐ[μ] 0 := by
    have h := condExp_itoInt hBM hWm h𝓕 hs le_rfl hst hX.diff
    rwa [itoInt_of_le le_rfl] at h
  exact condExp_eq_of_ae_eq_add e
    ((memLp_integral_drift hX.drift le_rfl hst le_rfl).integrable one_le_two)
    ((memLp_itoInt hBM hWm h𝓕 hs hX.diff).integrable one_le_two) h0

/-- **Cochrane (2023), §3.6.3, eq. (3.45), p. 77: the innovation of an Itô process.** For `x` on
`[s, t]`, `0 ≤ s ≤ t`, drift `a`, diffusion `H`: a.s.
`x_t − E_s[x_t] = ∫_s^t H dW + (∫_s^t a du − E_s[∫_s^t a du])`. The first term is the book's
`σ dz`; the second is the unexpected part of the drift. -/
theorem innovation_eq (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess μ 𝓕 W X a H s t Ca CH) :
    (fun ω => X t ω - μ[X t | 𝓕 s] ω) =ᵐ[μ] fun ω => itoInt μ 𝓕 W H s t ω
      + ((∫ r in s..t, a r ω) - μ[fun ω => ∫ r in s..t, a r ω | 𝓕 s] ω) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have iT : Integrable (X t) μ := (hX.memLp hBM hWm h𝓕 hs ⟨hst, le_rfl⟩).integrable one_le_two
  have iS : Integrable (X s) μ := hX.init.integrable one_le_two
  have h1 := expected_increment hBM hWm h𝓕 hs hst hX
  have h2 := condExp_sub (m := 𝓕 s) iT iS
  have h3 : μ[X s | 𝓕 s] = X s :=
    condExp_of_stronglyMeasurable (𝓕.le s) (hX.adapted s ⟨le_rfl, hst⟩) iS
  filter_upwards [h1, h2, hX.eq t ⟨hst, le_rfl⟩] with ω e1 e2 e3
  have e4 : μ[fun ω => X t ω - X s ω | 𝓕 s] ω = μ[X t | 𝓕 s] ω - X s ω := by
    rw [show (fun ω => X t ω - X s ω) = X t - X s from rfl, e2, Pi.sub_apply, h3]
  linarith

/-- **Cochrane (2023), §3.6.3, eq. (3.45), p. 77: the innovation is `σ dz` to first order.** For
an Itô process with drift bounded by `C` on `[s, t]`, `0 ≤ s ≤ t`:
`E[(x_t − E_s x_t − ∫_s^t H dW)²] ≤ (2C(t − s))²`. -/
theorem innovation_sq_le (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess μ 𝓕 W X a H s t Ca CH) :
    ∫ ω, (X t ω - μ[X t | 𝓕 s] ω - itoInt μ 𝓕 W H s t ω) ^ 2 ∂μ ≤ (2 * (Ca * (t - s))) ^ 2 := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hb : ∀ ω, |∫ r in s..t, a r ω| ≤ Ca * (t - s) := fun ω =>
    abs_integral_drift_le hX.drift.bound le_rfl hst le_rfl ω
  have hE := ae_bdd_abs_condExp_of_ae_bdd_abs (μ := μ) (m := 𝓕 s) (R := Ca * (t - s))
    (f := fun ω => ∫ r in s..t, a r ω) (ae_of_all μ fun ω => hb ω)
  have hle : ∀ᵐ ω ∂μ, (X t ω - μ[X t | 𝓕 s] ω - itoInt μ 𝓕 W H s t ω) ^ 2 ≤
      (2 * (Ca * (t - s))) ^ 2 := by
    filter_upwards [innovation_eq hBM hWm h𝓕 hs hst hX, hE] with ω h1 h2
    have e : X t ω - μ[X t | 𝓕 s] ω - itoInt μ 𝓕 W H s t ω =
        (∫ r in s..t, a r ω) - μ[fun ω => ∫ r in s..t, a r ω | 𝓕 s] ω := by
      rw [h1]; ring
    rw [e]
    have h2' : |μ[fun ω => ∫ r in s..t, a r ω | 𝓕 s] ω| ≤ Ca * (t - s) := h2
    have h3 : |(∫ r in s..t, a r ω) - μ[fun ω => ∫ r in s..t, a r ω | 𝓕 s] ω| ≤
        2 * (Ca * (t - s)) := by
      have := abs_sub (∫ r in s..t, a r ω) (μ[fun ω => ∫ r in s..t, a r ω | 𝓕 s] ω)
      linarith [hb ω]
    have h4 := abs_nonneg ((∫ r in s..t, a r ω) - μ[fun ω => ∫ r in s..t, a r ω | 𝓕 s] ω)
    rw [← sq_abs]
    nlinarith
  calc ∫ ω, (X t ω - μ[X t | 𝓕 s] ω - itoInt μ 𝓕 W H s t ω) ^ 2 ∂μ
      ≤ ∫ _ω, (2 * (Ca * (t - s))) ^ 2 ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) (integrable_const _) hle
    _ = (2 * (Ca * (t - s))) ^ 2 := by simp

/-- **Cochrane (2023), §3.6.3, eq. (3.45), p. 77: relative size of the two parts of the
innovation.** If moreover `c² ≤ H²` on `[s, t]`, then
`c²·E[(x_t − E_s x_t − ∫_s^t H dW)²] ≤ (2C)²(t − s)·E[(∫_s^t H dW)²]`: the mean square of the
non-`σ dz` part is `O(t − s)` times that of `σ dz`, so it vanishes relative to `σ dz` as
`t ↓ s`. -/
theorem innovation_relative (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) {X a H : ℝ → Ω → ℝ} {Ca CH c : ℝ}
    (hX : ItoProcess μ 𝓕 W X a H s t Ca CH) (hc : ∀ u ∈ Set.Icc s t, ∀ ω, c ^ 2 ≤ H u ω ^ 2) :
    c ^ 2 * ∫ ω, (X t ω - μ[X t | 𝓕 s] ω - itoInt μ 𝓕 W H s t ω) ^ 2 ∂μ ≤
      (2 * Ca) ^ 2 * (t - s) * ∫ ω, itoInt μ 𝓕 W H s t ω ^ 2 ∂μ := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have h1 := innovation_sq_le hBM hWm h𝓕 hs hst hX
  have hI : c ^ 2 * (t - s) ≤ ∫ ω, itoInt μ 𝓕 W H s t ω ^ 2 ∂μ := by
    rw [integral_itoInt_sq hBM hWm h𝓕 hs hst hX.diff]
    have hlow : ∀ᵐ ω ∂μ, c ^ 2 * (t - s) ≤ ∫ u in s..t, H u ω ^ 2 := by
      filter_upwards [hX.diff.cont] with ω hω
      have := intervalIntegral.integral_mono_on (μ := volume) hst intervalIntegrable_const
        ((hω.pow 2).intervalIntegrable_of_Icc hst) (fun u hu => hc u hu ω)
      simpa [mul_comm] using this
    calc c ^ 2 * (t - s) = ∫ _ω, c ^ 2 * (t - s) ∂μ := by simp
      _ ≤ ∫ ω, (∫ u in s..t, H u ω ^ 2) ∂μ :=
        integral_mono_ae (integrable_const _) (integrable_integral_sq hX.diff hst) hlow
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hts : 0 ≤ t - s := by linarith
  calc c ^ 2 * ∫ ω, (X t ω - μ[X t | 𝓕 s] ω - itoInt μ 𝓕 W H s t ω) ^ 2 ∂μ
      ≤ c ^ 2 * (2 * (Ca * (t - s))) ^ 2 := mul_le_mul_of_nonneg_left h1 hc2
    _ = (2 * Ca) ^ 2 * (t - s) * (c ^ 2 * (t - s)) := by ring
    _ ≤ (2 * Ca) ^ 2 * (t - s) * ∫ ω, itoInt μ 𝓕 W H s t ω ^ 2 ∂μ :=
        mul_le_mul_of_nonneg_left hI (by positivity)

/-! ## The AR(1) surplus as an Ornstein–Uhlenbeck process -/

variable (μ 𝓕 W)

/-- Cochrane (2023), §3.6.3, p. 77 (the AR(1) example): the Wiener integral
`I_u = ∫_0^u e^{ηv} dW_v`. -/
noncomputable def ouI (η u : ℝ) (ω : Ω) : ℝ := itoInt μ 𝓕 W (fun v _ => Real.exp (η * v)) 0 u ω

/-- **Cochrane (2023), §3.6.3, p. 77: the AR(1) surplus `ds = −ηs dt + σ dε`**, explicitly
`s_u = e^{−ηu}(s₀ + σ∫_0^u e^{ηv} dW_v)`. -/
noncomputable def ou (η σ s0 u : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(η * u)) * (s0 + σ * ouI μ 𝓕 W η u ω)

variable {μ 𝓕 W}

/-- Cochrane (2023), §3.6.3, p. 77: `|e^{ηv}| ≤ e^{|η|t}` on `[0, t]`. -/
theorem abs_exp_le (η : ℝ) {t v : ℝ} (hv : v ∈ Set.Icc 0 t) :
    |Real.exp (η * v)| ≤ Real.exp (|η| * t) := by
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  calc η * v ≤ |η| * v := mul_le_mul_of_nonneg_right (le_abs_self η) hv.1
    _ ≤ |η| * t := mul_le_mul_of_nonneg_left hv.2 (abs_nonneg η)

/-- Cochrane (2023), §3.6.3, p. 77: `e^{ηv}` is an admissible (bounded, continuous,
deterministic) integrand on `[0, t]`. -/
theorem ouIntegrand (η t : ℝ) :
    ItoIntegrand μ 𝓕 (fun v _ => Real.exp (η * v)) 0 t (Real.exp (|η| * t)) :=
  itoIntegrand_deterministic (Real.continuous_exp.comp (continuous_const.mul continuous_id)
    ).continuousOn fun _ hv => abs_exp_le η hv

/-- Cochrane (2023), §3.6.3, p. 77: `e^{−ηt} = e^{−η(t−r)}e^{−ηr}`.
Mathlib `Real.exp_add`. -/
theorem exp_split (η r t : ℝ) :
    Real.exp (-(η * t)) = Real.exp (-(η * (t - r))) * Real.exp (-(η * r)) := by
  rw [← Real.exp_add]
  ring_nf

/-- **Cochrane (2023), §3.6.3, p. 77: `E_r s_t = e^{−η(t−r)} s_r`** a.s., `0 ≤ r ≤ t` (the
book's `E_t s_{t+τ} = e^{−ητ}s_t`), from the martingale property of the Wiener integral
(`TidyR7ItoIntegral.condExp_itoInt`). -/
theorem ou_condExp (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (η σ s0 : ℝ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
    μ[ou μ 𝓕 W η σ s0 t | 𝓕 r] =ᵐ[μ] fun ω => Real.exp (-(η * (t - r))) * ou μ 𝓕 W η σ s0 r ω := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hI := condExp_itoInt hBM hWm h𝓕 le_rfl hr hrt (ouIntegrand (μ := μ) (𝓕 := 𝓕) η t)
  have iI : Integrable (ouI μ 𝓕 W η t) μ :=
    (memLp_itoInt hBM hWm h𝓕 le_rfl (ouIntegrand η t)).integrable one_le_two
  have e : ou μ 𝓕 W η σ s0 t = (fun _ => Real.exp (-(η * t)) * s0)
      + (Real.exp (-(η * t)) * σ) • ouI μ 𝓕 W η t := by
    funext ω
    simp only [ou, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  filter_upwards [condExp_add (m := 𝓕 r) (integrable_const (Real.exp (-(η * t)) * s0))
    (iI.smul (Real.exp (-(η * t)) * σ)), condExp_smul (m := 𝓕 r) (Real.exp (-(η * t)) * σ)
    (ouI μ 𝓕 W η t), hI] with ω h1 h2 h3
  rw [h1, Pi.add_apply, condExp_const (𝓕.le r), h2, Pi.smul_apply, smul_eq_mul]
  change Real.exp (-(η * t)) * s0 + Real.exp (-(η * t)) * σ *
      μ[itoInt μ 𝓕 W (fun v _ => Real.exp (η * v)) 0 t | 𝓕 r] ω = _
  rw [h3, exp_split η r t]
  simp only [ou, ouI]
  ring

/-- **Cochrane (2023), §3.6.3, eq. (3.45), p. 77: the innovation of the AR(1) surplus.** For
`0 ≤ r ≤ t`, a.s. `s_t − E_r s_t = σe^{−ηt}∫_r^t e^{ηv} dW_v`. -/
theorem ou_innovation (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (η σ s0 : ℝ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
    (fun ω => ou μ 𝓕 W η σ s0 t ω - μ[ou μ 𝓕 W η σ s0 t | 𝓕 r] ω) =ᵐ[μ]
      fun ω => σ * Real.exp (-(η * t)) * itoInt μ 𝓕 W (fun v _ => Real.exp (η * v)) r t ω := by
  filter_upwards [ou_condExp hBM hWm h𝓕 η σ s0 hr hrt,
    itoInt_add_itoInt hBM hWm h𝓕 le_rfl hr hrt (ouIntegrand (μ := μ) (𝓕 := 𝓕) η t)]
    with ω h1 h2
  rw [h1]
  simp only [ou, ouI]
  rw [h2, exp_split η r t]
  ring

/-- **Cochrane (2023), §3.6.3, p. 77 (non-vacuity of the innovation): its mean square.** For
`0 ≤ r ≤ t`, `E[(s_t − E_r s_t)²] = ∫_r^t (σe^{−ηt}e^{ηv})² dv` (Wiener isometry).
The Wiener isometry `TidyR7ItoBridge.integral_itoInt_deterministic_sq`. -/
theorem ou_innovation_sq_eq (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (η σ s0 : ℝ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
    ∫ ω, (ou μ 𝓕 W η σ s0 t ω - μ[ou μ 𝓕 W η σ s0 t | 𝓕 r] ω) ^ 2 ∂μ =
      ∫ v in r..t, (σ * Real.exp (-(η * t)) * Real.exp (η * v)) ^ 2 := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hH : ItoIntegrand μ 𝓕 (fun v _ => Real.exp (η * v)) r t (Real.exp (|η| * t)) :=
    (ouIntegrand η t).mono hr le_rfl
  have hc := itoInt_const_mul hBM hWm h𝓕 hr hH (σ * Real.exp (-(η * t)))
  have e : (fun ω => ou μ 𝓕 W η σ s0 t ω - μ[ou μ 𝓕 W η σ s0 t | 𝓕 r] ω) =ᵐ[μ]
      itoInt μ 𝓕 W (fun u _ => σ * Real.exp (-(η * t)) * Real.exp (η * u)) r t := by
    filter_upwards [ou_innovation hBM hWm h𝓕 η σ s0 hr hrt, hc] with ω h1 h2
    rw [h1, h2]
  have e2 : (fun ω => (ou μ 𝓕 W η σ s0 t ω - μ[ou μ 𝓕 W η σ s0 t | 𝓕 r] ω) ^ 2) =ᵐ[μ]
      fun ω => itoInt μ 𝓕 W (fun u _ => σ * Real.exp (-(η * t)) * Real.exp (η * u)) r t ω ^ 2 := by
    filter_upwards [e] with ω h
    rw [h]
  rw [integral_congr_ae e2]
  exact integral_itoInt_deterministic_sq hBM hWm h𝓕 hr hrt
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
      ).continuousOn)
    (C := |σ * Real.exp (-(η * t))| * Real.exp (|η| * t)) fun v hv => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_exp_le η ⟨hr.trans hv.1, hv.2⟩) (abs_nonneg _)

/-- Cochrane (2023), §3.6.3, p. 77: for `x ≥ 0`, `|e^{−x} − 1| ≤ x`.
From Mathlib `Real.add_one_le_exp`. -/
theorem abs_exp_neg_sub_one_le {x : ℝ} (hx : 0 ≤ x) : |Real.exp (-x) - 1| ≤ x := by
  have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 := Real.add_one_le_exp (-x)
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **Cochrane (2023), §3.6.3, eq. (3.45), p. 77: `Δ s = σ dε` for the AR(1) surplus.** For
`η ≥ 0`, `0 ≤ r ≤ t`: `E[(s_t − E_r s_t − σ(W_t − W_r))²] ≤ σ²η²(t − r)³`, while
`E[(σ(W_t − W_r))²] = σ²(t − r)`. -/
theorem ou_innovation_sq_le (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) {η : ℝ} (hη : 0 ≤ η) (σ s0 : ℝ) {r t : ℝ} (hr : 0 ≤ r)
    (hrt : r ≤ t) :
    ∫ ω, (ou μ 𝓕 W η σ s0 t ω - μ[ou μ 𝓕 W η σ s0 t | 𝓕 r] ω - σ * incr W r t ω) ^ 2 ∂μ ≤
      σ ^ 2 * η ^ 2 * (t - r) ^ 3 := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  set k : ℝ → ℝ := fun v => σ * Real.exp (-(η * (t - v))) - σ with hk
  have kc : Continuous k := (continuous_const.mul (Real.continuous_exp.comp
    ((continuous_const.mul (continuous_const.sub continuous_id)).neg))).sub continuous_const
  have kb : ∀ v ∈ Set.Icc r t, |k v| ≤ |σ| * (η * (t - r)) := fun v hv => by
    have hx : 0 ≤ η * (t - v) := mul_nonneg hη (by linarith [hv.2])
    have e : k v = σ * (Real.exp (-(η * (t - v))) - 1) := by simp only [hk]; ring
    rw [e, abs_mul]
    refine mul_le_mul_of_nonneg_left ((abs_exp_neg_sub_one_le hx).trans ?_) (abs_nonneg σ)
    exact mul_le_mul_of_nonneg_left (by linarith [hv.1]) hη
  have hH : ItoIntegrand μ 𝓕 (fun v _ => Real.exp (η * v)) r t (Real.exp (|η| * t)) :=
    (ouIntegrand η t).mono hr le_rfl
  have hK : ItoIntegrand μ 𝓕 (fun _ _ => -σ) r t |σ| :=
    itoIntegrand_const stronglyMeasurable_const fun _ => by rw [abs_neg]
  have hadd := itoInt_add hBM hWm h𝓕 hr (hH.const_mul (σ * Real.exp (-(η * t)))) hK
  have hc := itoInt_const_mul hBM hWm h𝓕 hr hH (σ * Real.exp (-(η * t)))
  have hcst := itoInt_const hBM hWm h𝓕 hr hrt (c := fun _ => -σ) stronglyMeasurable_const
    (C := |σ|) fun _ => by rw [abs_neg]
  have ek : (fun u (_ : Ω) => k u) = fun u ω =>
      (fun u ω => σ * Real.exp (-(η * t)) * (fun v (_ : Ω) => Real.exp (η * v)) u ω) u ω
        + (fun _ _ => -σ) u ω := by
    funext u ω
    simp only [hk]
    rw [show -(η * (t - u)) = -(η * t) + η * u by ring, Real.exp_add]
    ring
  have e : (fun ω => ou μ 𝓕 W η σ s0 t ω - μ[ou μ 𝓕 W η σ s0 t | 𝓕 r] ω - σ * incr W r t ω)
      =ᵐ[μ] itoInt μ 𝓕 W (fun u _ => k u) r t := by
    rw [ek]
    filter_upwards [ou_innovation hBM hWm h𝓕 η σ s0 hr hrt, hadd, hc, hcst] with ω h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    ring
  have e2 : (fun ω => (ou μ 𝓕 W η σ s0 t ω - μ[ou μ 𝓕 W η σ s0 t | 𝓕 r] ω
      - σ * incr W r t ω) ^ 2) =ᵐ[μ] fun ω => itoInt μ 𝓕 W (fun u _ => k u) r t ω ^ 2 := by
    filter_upwards [e] with ω h
    rw [h]
  rw [integral_congr_ae e2,
    integral_itoInt_deterministic_sq hBM hWm h𝓕 hr hrt kc.continuousOn kb]
  have hb : ∀ v ∈ Set.Icc r t, k v ^ 2 ≤ σ ^ 2 * η ^ 2 * (t - r) ^ 2 := fun v hv => by
    have h := kb v hv
    have h0 := abs_nonneg (k v)
    rw [← sq_abs]
    calc |k v| ^ 2 ≤ (|σ| * (η * (t - r))) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = σ ^ 2 * η ^ 2 * (t - r) ^ 2 := by rw [mul_pow, sq_abs]; ring
  have := intervalIntegral.integral_mono_on (μ := volume) hrt ((kc.pow 2).intervalIntegrable _ _)
    intervalIntegrable_const hb
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  calc ∫ v in r..t, k v ^ 2 ≤ (t - r) * (σ ^ 2 * η ^ 2 * (t - r) ^ 2) := this
    _ = σ ^ 2 * η ^ 2 * (t - r) ^ 3 := by ring

/-- **Cochrane (2023), §3.6.3, p. 77: the surplus `s` solves the AR(1)
`ds = −ηs dt + σ dε`.** For `0 ≤ r < t`, a.s.
`s_t − s_r = −η∫_r^t s_u du + σ(W_t − W_r)` (mean-square time integral
`TidyR7ItoProducts.dtInt`), by Itô's product rule for `e^{−ηu}·(s₀ + σ∫_0^u e^{ηv}dW)`.
Generalises `ContinuousLinear.ar1_hasDerivAt` (the case `σ = 0`). -/
theorem ou_sde (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (η σ s0 : ℝ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r < t) :
    (fun ω => ou μ 𝓕 W η σ s0 t ω - ou μ 𝓕 W η σ s0 r ω) =ᵐ[μ]
      fun ω => -η * dtInt μ 𝓕 (ou μ 𝓕 W η σ s0) r t ω + σ * incr W r t ω := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have cE : Continuous fun u => Real.exp (-(η * u)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
  have dE : ∀ u, HasDerivAt (fun u => Real.exp (-(η * u))) (-η * Real.exp (-(η * u))) u :=
    fun u => (((hasDerivAt_id u).const_mul η).neg.exp).congr_deriv (by simp; ring)
  have gc : Continuous fun u => -η * Real.exp (-(η * u)) := continuous_const.mul cE
  obtain ⟨Cg, hCg⟩ := exists_bound_Icc gc r t
  obtain ⟨CE, hCE⟩ := exists_bound_Icc cE r t
  have hX : ItoProcess μ 𝓕 W (fun u _ => Real.exp (-(η * u)))
      (fun u _ => -η * Real.exp (-(η * u))) (fun _ _ => 0) r t Cg 0 :=
    itoProcess_det hBM hWm h𝓕 hr gc.continuousOn hCg (fun u _ => ftc_split dE gc r u)
  have hY := itoProcess_wiener hBM hWm h𝓕 hr hrt.le (f := fun _ => s0) (g := fun _ => 0)
    (h := fun v => Real.exp (η * v)) (Cg := 0) σ
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    (fun _ hv => abs_exp_le η hv) continuousOn_const (fun _ _ => by simp) (fun _ _ => by simp)
  have hpr := product_rule hBM hWm h𝓕 hr hrt hX hY
  -- the four terms
  have z1 : dtInt μ 𝓕 (fun u ω => (fun u (_ : Ω) => Real.exp (-(η * u))) u ω
      * (fun _ (_ : Ω) => (0 : ℝ)) u ω) r t =ᵐ[μ] 0 := dtInt_of_eq_zero fun u _ ω => by simp
  have e2 : (fun u ω => (fun u (_ : Ω) => Real.exp (-(η * u))) u ω
      * (fun u (_ : Ω) => σ * Real.exp (η * u)) u ω) = fun _ _ => σ := by
    funext u ω
    simp only
    rw [show Real.exp (-(η * u)) * (σ * Real.exp (η * u)) =
      σ * (Real.exp (-(η * u)) * Real.exp (η * u)) by ring, ← Real.exp_add]
    simp
  have z2 := itoInt_const hBM hWm h𝓕 hr hrt.le (c := fun _ => σ) stronglyMeasurable_const
    (C := |σ|) fun _ => le_rfl
  have hMS : MSIntegrand μ 𝓕 (ou μ 𝓕 W η σ s0) r t := by
    have h0 := MSIntegrand.mul_itoIntegrand (hY.toMS hBM hWm h𝓕 hr)
      (itoIntegrand_deterministic (C := CE) (P := μ) (𝓕 := 𝓕) cE.continuousOn hCE)
    refine msIntegrand_congr h0 fun u _ ω => ?_
    simp only [ou, ouI]
    ring
  have e3 : (fun u ω => (fun u ω => (fun _ => s0) u + σ * itoInt μ 𝓕 W
      (fun r _ => Real.exp (η * r)) 0 u ω) u ω * (fun u (_ : Ω) => -η * Real.exp (-(η * u))) u ω)
      = fun u ω => -η * ou μ 𝓕 W η σ s0 u ω := by
    funext u ω
    simp only [ou, ouI]
    ring
  have z3 := dtInt_const_mul hMS (-η)
  have e4 : (fun u ω => (fun u ω => (fun _ => s0) u + σ * itoInt μ 𝓕 W
      (fun r _ => Real.exp (η * r)) 0 u ω) u ω * (fun _ (_ : Ω) => (0 : ℝ)) u ω)
      = fun _ _ => 0 := by
    funext u ω
    simp
  have z4 := itoInt_const hBM hWm h𝓕 hr hrt.le (c := fun _ => (0 : ℝ)) stronglyMeasurable_const
    (C := 0) fun _ => by simp
  rw [e2, e3, e4] at hpr
  filter_upwards [hpr, z1, z2, z3, z4] with ω h0 h1 h2 h3 h4
  simp only [Pi.zero_apply] at h1 h4
  have h0' := h0
  rw [h1, h2, h3, h4] at h0'
  simp only [ou, ouI] at h0' ⊢
  simp only [intervalIntegral.integral_zero, zero_mul] at h0'
  linarith

/-! ## The forecast process (3.44) and the present value -/

/-- **Cochrane (2023), §3.6.3, eq. (3.44), p. 77: conditional expectations follow a process.** For
`τ ≥ 0` and `u ≥ 0`, the forecast `y_u = E_u s_{u+τ}` is `e^{−ητ}s_u` a.s. -/
theorem forecast_condExp (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (η σ s0 : ℝ) {τ u : ℝ} (hτ : 0 ≤ τ) (hu : 0 ≤ u) :
    μ[ou μ 𝓕 W η σ s0 (u + τ) | 𝓕 u] =ᵐ[μ]
      fun ω => Real.exp (-(η * τ)) * ou μ 𝓕 W η σ s0 u ω := by
  filter_upwards [ou_condExp hBM hWm h𝓕 η σ s0 hu (by linarith : u ≤ u + τ)] with ω h
  rw [h]
  ring_nf

/-- **Cochrane (2023), §3.6.3, eq. (3.44), p. 77: the forecast process is
`dy = −ηy dt + e^{−ητ}σ dε`.** With `y_u = e^{−ητ}s_u`, for `0 ≤ r < t`, a.s.
`y_t − y_r = −η∫_r^t y du + e^{−ητ}σ(W_t − W_r)`: drift `μ_y = −ηy`, diffusion `e^{−ητ}σ`. -/
theorem forecast_sde (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (η σ s0 τ : ℝ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r < t) :
    (fun ω => Real.exp (-(η * τ)) * ou μ 𝓕 W η σ s0 t ω
      - Real.exp (-(η * τ)) * ou μ 𝓕 W η σ s0 r ω) =ᵐ[μ]
      fun ω => -η * (Real.exp (-(η * τ)) * dtInt μ 𝓕 (ou μ 𝓕 W η σ s0) r t ω)
        + Real.exp (-(η * τ)) * σ * incr W r t ω := by
  filter_upwards [ou_sde hBM hWm h𝓕 η σ s0 hr hrt] with ω h
  rw [← mul_sub, h]
  ring

/-- **Cochrane (2023), §3.6.3, eq. (3.45), p. 77: the innovation of the forecast** is the `dε`
part: `y_t − E_r y_t = e^{−ητ}σe^{−ηt}∫_r^t e^{ηv}dW`, `0 ≤ r ≤ t`, a.s. -/
theorem forecast_innovation (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (η σ s0 τ : ℝ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
    (fun ω => Real.exp (-(η * τ)) * ou μ 𝓕 W η σ s0 t ω
      - μ[fun ω => Real.exp (-(η * τ)) * ou μ 𝓕 W η σ s0 t ω | 𝓕 r] ω) =ᵐ[μ]
      fun ω => Real.exp (-(η * τ)) *
        (σ * Real.exp (-(η * t)) * itoInt μ 𝓕 W (fun v _ => Real.exp (η * v)) r t ω) := by
  have hs := condExp_smul (μ := μ) (m := 𝓕 r) (Real.exp (-(η * τ))) (ou μ 𝓕 W η σ s0 t)
  filter_upwards [ou_innovation hBM hWm h𝓕 η σ s0 hr hrt, hs] with ω h1 h2
  have e : (fun ω => Real.exp (-(η * τ)) * ou μ 𝓕 W η σ s0 t ω) =
      Real.exp (-(η * τ)) • ou μ 𝓕 W η σ s0 t := by
    funext ω
    simp [smul_eq_mul]
  rw [e, h2, Pi.smul_apply, smul_eq_mul, ← h1]
  ring

/-- **Cochrane (2023), §3.6.3, p. 77: the present value of the expected surplus path.** For
`r + η > 0`, every `t` and `ω`, `∫_0^∞ e^{−rτ}(e^{−ητ}s_t) dτ = s_t/(r + η)`, where
`e^{−ητ}s_t` is `E_t s_{t+τ}` (`forecast_condExp`).
An instance of `ContinuousLinear.ar1_pv`. -/
theorem pv_expected_path {r η : ℝ} (h : 0 < r + η) (σ s0 t : ℝ) (ω : Ω) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (Real.exp (-(η * τ)) * ou μ 𝓕 W η σ s0 t ω) =
      ou μ 𝓕 W η σ s0 t ω / (r + η) :=
  ContinuousLinear.ar1_pv h

/-- **Cochrane (2023), §3.6.3, p. 77: the innovation of the present value is
`σ/(r + η) dε`.** With `PV_u = s_u/(r + η)`, for `0 ≤ q ≤ t`, a.s.
`PV_t − E_q PV_t = (σ/(r + η))e^{−ηt}∫_q^t e^{ηv}dW`.
The stochastic version of `ContinuousLinear.ar1_news`. -/
theorem pv_innovation (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (r η σ s0 : ℝ) {q t : ℝ} (hq : 0 ≤ q) (hqt : q ≤ t) :
    (fun ω => ou μ 𝓕 W η σ s0 t ω / (r + η)
      - μ[fun ω => ou μ 𝓕 W η σ s0 t ω / (r + η) | 𝓕 q] ω) =ᵐ[μ]
      fun ω => σ / (r + η) * Real.exp (-(η * t))
        * itoInt μ 𝓕 W (fun v _ => Real.exp (η * v)) q t ω := by
  have hs := condExp_smul (μ := μ) (m := 𝓕 q) (1 / (r + η)) (ou μ 𝓕 W η σ s0 t)
  filter_upwards [ou_innovation hBM hWm h𝓕 η σ s0 hq hqt, hs] with ω h1 h2
  have e : (fun ω => ou μ 𝓕 W η σ s0 t ω / (r + η)) = (1 / (r + η)) • ou μ 𝓕 W η σ s0 t := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, h2, Pi.smul_apply, smul_eq_mul]
  have e3 : ou μ 𝓕 W η σ s0 t ω / (r + η) - 1 / (r + η) * μ[ou μ 𝓕 W η σ s0 t | 𝓕 q] ω =
      (ou μ 𝓕 W η σ s0 t ω - μ[ou μ 𝓕 W η σ s0 t | 𝓕 q] ω) / (r + η) := by ring
  rw [e3, h1]
  ring

/-- **Cochrane (2023), §3.6.3, p. 77: `Δ_t ∫_0^∞ e^{−rτ}s_{t+τ}dτ = σ/(r + η) dε` in mean
square.** For `η ≥ 0`, `r + η ≠ 0`, `0 ≤ q ≤ t`:
`E[(PV_t − E_q PV_t − (σ/(r + η))(W_t − W_q))²] ≤ σ²η²(t − q)³/(r + η)²`. -/
theorem pv_innovation_sq_le (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (r : ℝ) {η : ℝ} (hη : 0 ≤ η) (hrη : r + η ≠ 0) (σ s0 : ℝ)
    {q t : ℝ} (hq : 0 ≤ q) (hqt : q ≤ t) :
    ∫ ω, (ou μ 𝓕 W η σ s0 t ω / (r + η) - μ[fun ω => ou μ 𝓕 W η σ s0 t ω / (r + η) | 𝓕 q] ω
      - σ / (r + η) * incr W q t ω) ^ 2 ∂μ ≤ σ ^ 2 * η ^ 2 * (t - q) ^ 3 / (r + η) ^ 2 := by
  have hs := condExp_smul (μ := μ) (m := 𝓕 q) (1 / (r + η)) (ou μ 𝓕 W η σ s0 t)
  have e0 : (fun ω => ou μ 𝓕 W η σ s0 t ω / (r + η)) = (1 / (r + η)) • ou μ 𝓕 W η σ s0 t := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have e : (fun ω => (ou μ 𝓕 W η σ s0 t ω / (r + η)
      - μ[fun ω => ou μ 𝓕 W η σ s0 t ω / (r + η) | 𝓕 q] ω - σ / (r + η) * incr W q t ω) ^ 2)
      =ᵐ[μ] fun ω => (1 / (r + η)) ^ 2 * (ou μ 𝓕 W η σ s0 t ω - μ[ou μ 𝓕 W η σ s0 t | 𝓕 q] ω
        - σ * incr W q t ω) ^ 2 := by
    filter_upwards [hs] with ω h
    rw [e0, h, Pi.smul_apply, smul_eq_mul]
    ring
  rw [integral_congr_ae e, integral_const_mul]
  have h := ou_innovation_sq_le hBM hWm h𝓕 hη σ s0 hq hqt
  have hp : 0 ≤ (1 / (r + η)) ^ 2 := sq_nonneg _
  calc (1 / (r + η)) ^ 2 * ∫ ω, (ou μ 𝓕 W η σ s0 t ω - μ[ou μ 𝓕 W η σ s0 t | 𝓕 q] ω
        - σ * incr W q t ω) ^ 2 ∂μ ≤ (1 / (r + η)) ^ 2 * (σ ^ 2 * η ^ 2 * (t - q) ^ 3) :=
        mul_le_mul_of_nonneg_left h hp
    _ = σ ^ 2 * η ^ 2 * (t - q) ^ 3 / (r + η) ^ 2 := by
        field_simp

/-- **Cochrane (2023), §3.6.3, p. 77: link with the deterministic news of `ContinuousLinear`.** For
`r + η > 0`, `0 ≤ q ≤ t`, for almost every `ω`, the perfect-foresight paths
`τ ↦ e^{−ητ}E_q[s_t](ω)` (old) and `τ ↦ e^{−ητ}s_t(ω)` (new) solve `s' = −ηs`, differ at `τ = 0`
by the stochastic innovation, and their present values differ by the innovation over `r + η`
(`ContinuousLinear.ar1_news`). -/
theorem news_link (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) {r η : ℝ} (h : 0 < r + η) (σ s0 : ℝ) {q t : ℝ} (hq : 0 ≤ q)
    (hqt : q ≤ t) :
    ∀ᵐ ω ∂μ, (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        (Real.exp (-(η * τ)) * ou μ 𝓕 W η σ s0 t ω)) -
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        (Real.exp (-(η * τ)) * μ[ou μ 𝓕 W η σ s0 t | 𝓕 q] ω)) =
      σ * Real.exp (-(η * t)) * itoInt μ 𝓕 W (fun v _ => Real.exp (η * v)) q t ω / (r + η) := by
  filter_upwards [ou_innovation hBM hWm h𝓕 η σ s0 hq hqt] with ω hω
  refine ContinuousLinear.ar1_news h (fun τ => ContinuousLinear.ar1_hasDerivAt η _ τ)
    (fun τ => ContinuousLinear.ar1_hasDerivAt η _ τ) ?_
  simp only [mul_zero, neg_zero, Real.exp_zero, one_mul]
  exact hω

/-- **Cochrane (2023), §3.6.3, p. 77 (`σ = 0`):** with no shocks the process is the
deterministic AR(1) path `e^{−ηu}s₀` of `ContinuousLinear.ar1_hasDerivAt`, and the innovation
vanishes: `s_t − E_r s_t = 0` a.s. for `0 ≤ r ≤ t`. -/
theorem ou_sigma_zero (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (η s0 : ℝ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
    (∀ u ω, ou μ 𝓕 W η 0 s0 u ω = Real.exp (-(η * u)) * s0) ∧
      (fun ω => ou μ 𝓕 W η 0 s0 t ω - μ[ou μ 𝓕 W η 0 s0 t | 𝓕 r] ω) =ᵐ[μ] 0 := by
  refine ⟨fun u ω => by simp [ou], ?_⟩
  filter_upwards [ou_innovation hBM hWm h𝓕 η 0 s0 hr hrt] with ω h
  rw [h]
  simp

/-! ## Non-vacuity on the constructed Brownian motion -/

/-- **Cochrane (2023), §3.6.3, p. 77 (non-vacuity): the AR(1) innovation is not zero.** On the
constructed motion `bmPath`, for `σ ≠ 0` and `0 ≤ r < t`, `E[(s_t − E_r s_t)²] > 0`. -/
theorem ou_bmPath_innovation_pos (η s0 : ℝ) {σ : ℝ} (hσ : σ ≠ 0) {r t : ℝ} (hr : 0 ≤ r)
    (hrt : r < t) :
    0 < ∫ ω, (ou gaussSeq bmF bmPath η σ s0 t ω
      - gaussSeq[ou gaussSeq bmF bmPath η σ s0 t | bmF r] ω) ^ 2 ∂gaussSeq := by
  rw [ou_innovation_sq_eq isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) η σ s0 hr hrt.le]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
      ).pow 2).intervalIntegrable _ _) (fun v _ => ?_) hrt
  have : σ * Real.exp (-(η * t)) * Real.exp (η * v) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hσ (Real.exp_pos _).ne') (Real.exp_pos _).ne'
  positivity

end Cochrane.Generality.TidyR7ItoInnovation
