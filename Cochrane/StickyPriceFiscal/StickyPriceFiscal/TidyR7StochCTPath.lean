/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.CTSimple

/-!
# The continuous-time sticky-price model with a diffusive shock, path by path

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.7 and §5.7.1,
pp. 162–167, (5.85)–(5.96), and Online Appendix A1, §1.12, pp. 579–580.

The book's model (5.85)–(5.90) is
`dx = σ(i − π)dt + dδx`, `dπ = (ρπ − κx)dt + dδπ`, `dp = π dt`, `dv = (rv + i − π − s̃)dt`,
`di = dε_m`, `ds̃ = dε_s`, with structural shocks `dε` that "may be diffusions or compensated
jump processes" (p. 164). This module takes ONE driving path `w` (later a Brownian path) and the
shocks `dε_m = σ_i dw`, `dε_s = σ_s dw` (the permanent interest-rate and surplus shocks of the
example on p. 166, now arriving continuously). With additive noise the model is linear in `w`
and the solution is explicit, with no stochastic calculus: writing
`Y_t = w_t − λ₂e^{−λ₂t}∫_0^t e^{λ₂u}w_u du` (`ouNoise`, the by-parts form of
`∫_0^t e^{−λ₂(t−u)}dw_u`) and `A = −(r + λ₂)σ_s/r` (`fiscalLoad`),

`i = σ_i w`, `s̃ = σ_s w`, `π = σ_i w + A Y`, `x = (ρσ_i w + λ₁A Y)/κ`, `v = (σ_s/r)(w − Y)`,
`p_t = ∫_0^t π`.

## Main results

* `ouNoise_incr`: `Y_b − Y_a = (w_b − w_a) − η∫_a^b Y` (the OU equation `dY = −ηY dt + dw`;
  the OU noise is restated from the Cochrane FiscalConstraints project).
* **`path_solves`** ((5.85)–(5.90) on every continuous path, over every interval `[a, b]`):
  `x_b − x_a = ∫_a^b σ(i − π) + R_x(0)(w_b − w_a)`,
  `π_b − π_a = ∫_a^b (ρπ − κx) + R_π(0)(w_b − w_a)`, `v` and `p` are `C¹` with
  `v̇ = rv + i − π − s̃` and `ṗ = π` (no price-level jump or diffusion, no innovation in the value
  of debt),
  `i_b − i_a = σ_i(w_b − w_a)`, `s̃_b − s̃_a = σ_s(w_b − w_a)`. The expectational errors are
  `dδx = R_x(0)dw`, `dδπ = R_π(0)dw`: the loading of each on `dw` is the impact response.
* The deterministic responses `respPi`, `respX`, `respV` (`R_π(τ) = σ_i + Ae^{−λ₂τ}`, ...):
  `resp_eq_ct_step` — they are exactly the step equilibrium of `CTSimple` (p. 166, (5.96)) with
  `v₀ = 0`, `i₀ = σ_i`, `s̃₀ = σ_s`; `ct_step_exists` supplies one.
* `pi_jumpPath`, `x_jumpPath`, `v_jumpPath`: **the same solution map, applied to a single jump
  of size `Δ` at the news date `u`** (the book's MIT shock), gives `Δ R(t − u)` after `u` and `0`
  before: the diffusive solution and the jump-at-news-date responses are one linear map.
* `stoch_zero_loading`: with `σ_i = σ_s = 0` everything is `0` (the deterministic steady state).
-/

namespace Cochrane.StickyPriceFiscal.TidyR7StochCTPath

open Real MeasureTheory Filter Topology
open Cochrane.StickyPriceFiscal.CTSimple

/-! ### The OU noise (restated from the Cochrane FiscalConstraints project) -/

/-- Cochrane (2023), §5.7, p. 164: the primitive `∫_0^t e^{ηu} w_u du` of the discounted driving
path. Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouPrim). -/
noncomputable def ouPrim (η : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, exp (η * u) * w u

/-- Cochrane (2023), §5.7, p. 164: the OU noise driven by the path `w`,
`Y_t = w_t − η e^{−ηt}∫_0^t e^{ηu} w_u du` (`= ∫_0^t e^{−η(t−u)} dw_u` by parts when
`w_0 = 0`). Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouNoise). -/
noncomputable def ouNoise (η : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  w t - η * (exp (-η * t) * ouPrim η w t)

variable {w : ℝ → ℝ}

/-- Cochrane (2023), §5.7, p. 164: `t ↦ ∫_0^t e^{ηu}w_u du` has derivative `e^{ηt}w_t`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.hasDerivAt_ouPrim). -/
theorem hasDerivAt_ouPrim (η : ℝ) (hw : Continuous w) (t : ℝ) :
    HasDerivAt (ouPrim η w) (exp (η * t) * w t) t :=
  ((by fun_prop : Continuous fun u => exp (η * u) * w u).integral_hasStrictDerivAt 0 t).hasDerivAt

/-- Cochrane (2023), §5.7, p. 164: the primitive is continuous.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.continuous_ouPrim). -/
theorem continuous_ouPrim (η : ℝ) (hw : Continuous w) : Continuous (ouPrim η w) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_ouPrim η hw t).continuousAt

/-- Cochrane (2023), §5.7, p. 164: the primitive vanishes at `0`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouPrim_zero). -/
theorem ouPrim_zero (η : ℝ) (w : ℝ → ℝ) : ouPrim η w 0 = 0 := by
  simp [ouPrim]

/-- Cochrane (2023), §5.7, p. 164: the OU noise is continuous.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.continuous_ouNoise). -/
theorem continuous_ouNoise (η : ℝ) (hw : Continuous w) : Continuous (ouNoise η w) := by
  have := continuous_ouPrim η hw
  unfold ouNoise
  fun_prop

/-- Cochrane (2023), §5.7, p. 164: the OU noise starts at `Y_0 = w_0`. -/
theorem ouNoise_zero (η : ℝ) (w : ℝ → ℝ) : ouNoise η w 0 = w 0 := by
  simp [ouNoise, ouPrim_zero]

/-- Cochrane (2023), §5.7, p. 164: `w − Y` is differentiable with derivative `ηY`.
A special case of the Cochrane FiscalConstraints project's TidyR7OUPath.hasDerivAt_ouPath_sub. -/
theorem hasDerivAt_sub_ouNoise (η : ℝ) (hw : Continuous w) (t : ℝ) :
    HasDerivAt (fun u => w u - ouNoise η w u) (η * ouNoise η w t) t := by
  have hE : HasDerivAt (fun u => exp (-η * u)) (exp (-η * t) * -η) t := by
    simpa using ((hasDerivAt_id' t).const_mul (-η)).exp
  have h := (hE.mul (hasDerivAt_ouPrim η hw t)).const_mul η
  have hf : (fun u => w u - ouNoise η w u) = fun u => η * (exp (-η * u) * ouPrim η w u) := by
    funext u
    simp only [ouNoise]
    ring
  have he : exp (-η * t) * exp (η * t) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  rw [hf]
  refine h.congr_deriv ?_
  simp only [ouNoise]
  linear_combination (η * w t) * he

/-- **Cochrane (2023), §5.7, p. 164: the OU equation `dY = −ηY dt + dw` in increment form**, on
every continuous path: `Y_b − Y_a = (w_b − w_a) − η∫_a^b Y`.
The increment form of the Cochrane FiscalConstraints project's TidyR7OUPath.ouPath_integral_eq. -/
theorem ouNoise_incr (η : ℝ) (hw : Continuous w) (a b : ℝ) :
    ouNoise η w b - ouNoise η w a = (w b - w a) - η * ∫ u in a..b, ouNoise η w u := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_sub_ouNoise η hw x)
    ((continuous_const.mul (continuous_ouNoise η hw)).intervalIntegrable a b)
  rw [intervalIntegral.integral_const_mul] at h
  linarith

/-! ### The solution on a path -/

/-- Cochrane (2023), (5.96), p. 166: the inflation loading of the fiscal shock,
`A = −(r + λ₂)σ_s/r` (the coefficient of `e^{−λ₂t}` in (5.96) with `v₀ = 0`, `s̃₀ = σ_s`). -/
noncomputable def fiscalLoad (r σ κ ρ σs : ℝ) : ℝ := -((r + lam2 ρ κ σ) * σs / r)

/-- Cochrane (2023), (5.89), p. 162: the interest rate `i = σ_i w` (`di = dε_m = σ_i dw`). -/
def iPath (σi : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ := σi * w t

/-- Cochrane (2023), (5.90), p. 163: the surplus `s̃ = σ_s w` (`ds̃ = dε_s = σ_s dw`). -/
def sPath (σs : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ := σs * w t

/-- Cochrane (2023), (5.94)–(5.96), pp. 164–166: inflation driven by the path,
`π = σ_i w + A Y`. -/
noncomputable def piPath (r σ κ ρ σi σs : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  σi * w t + fiscalLoad r σ κ ρ σs * ouNoise (lam2 ρ κ σ) w t

/-- Cochrane (2023), (5.92), p. 164: the output gap driven by the path,
`x = (ρσ_i w + λ₁A Y)/κ`. -/
noncomputable def xPath (r σ κ ρ σi σs : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  (ρ * σi * w t + lam1 ρ κ σ * fiscalLoad r σ κ ρ σs * ouNoise (lam2 ρ κ σ) w t) / κ

/-- Cochrane (2023), (5.93), p. 166: the real value of debt driven by the path,
`v = (σ_s/r)(w − Y)`. -/
noncomputable def vPath (r σ κ ρ σs : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  σs / r * (w t - ouNoise (lam2 ρ κ σ) w t)

/-- Cochrane (2023), (5.87), p. 162: the (log) price level `p_t = ∫_0^t π`. -/
noncomputable def pPath (r σ κ ρ σi σs : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, piPath r σ κ ρ σi σs w u

/-- Cochrane (2023), (5.96), p. 166: the deterministic inflation response at horizon `τ` to a
unit shock, `R_π(τ) = σ_i + Ae^{−λ₂τ}`. -/
noncomputable def respPi (r σ κ ρ σi σs τ : ℝ) : ℝ :=
  σi + fiscalLoad r σ κ ρ σs * exp (-(lam2 ρ κ σ * τ))

/-- Cochrane (2023), p. 166: the deterministic output response,
`R_x(τ) = (ρσ_i + λ₁Ae^{−λ₂τ})/κ`. -/
noncomputable def respX (r σ κ ρ σi σs τ : ℝ) : ℝ :=
  (ρ * σi + lam1 ρ κ σ * fiscalLoad r σ κ ρ σs * exp (-(lam2 ρ κ σ * τ))) / κ

/-- Cochrane (2023), p. 166: the deterministic debt response, `R_v(τ) = (σ_s/r)(1 − e^{−λ₂τ})`. -/
noncomputable def respV (r σ κ ρ σs τ : ℝ) : ℝ := σs / r * (1 - exp (-(lam2 ρ κ σ * τ)))

/-- Cochrane (2023), (5.85), p. 162: the impact response `R_π(0) = σ_i + A`. -/
theorem respPi_zero (r σ κ ρ σi σs : ℝ) :
    respPi r σ κ ρ σi σs 0 = σi + fiscalLoad r σ κ ρ σs := by
  simp [respPi]

/-- Cochrane (2023), (5.85), p. 162: the impact response `R_x(0) = (ρσ_i + λ₁A)/κ`. -/
theorem respX_zero (r σ κ ρ σi σs : ℝ) :
    respX r σ κ ρ σi σs 0 = (ρ * σi + lam1 ρ κ σ * fiscalLoad r σ κ ρ σs) / κ := by
  simp [respX]

/-- Cochrane (2023), §5.7.1, p. 165: the value of debt does not move on impact, `R_v(0) = 0`. -/
theorem respV_zero (r σ κ ρ σs : ℝ) : respV r σ κ ρ σs 0 = 0 := by
  simp [respV]

variable {r σ κ ρ σi σs : ℝ}

/-- **Cochrane (2023), (5.85), p. 162, on a path**: over every `[a, b]`,
`x_b − x_a = ∫_a^b σ(i − π) + R_x(0)(w_b − w_a)`; the expectational error is
`δx_b − δx_a = R_x(0)(w_b − w_a)`. -/
theorem x_incr (hκ : 0 < κ) (hσ : 0 < σ) (hw : Continuous w) (a b : ℝ) :
    xPath r σ κ ρ σi σs w b - xPath r σ κ ρ σi σs w a
      = (∫ u in a..b, σ * (iPath σi w u - piPath r σ κ ρ σi σs w u))
        + respX r σ κ ρ σi σs 0 * (w b - w a) := by
  have hI := ouNoise_incr (lam2 ρ κ σ) hw a b
  have hm := lam_mul (ρ := ρ) hκ hσ
  have hint : (∫ u in a..b, σ * (iPath σi w u - piPath r σ κ ρ σi σs w u))
      = -(σ * fiscalLoad r σ κ ρ σs) * ∫ u in a..b, ouNoise (lam2 ρ κ σ) w u := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    simp only [iPath, piPath]
    ring
  rw [hint, respX_zero]
  simp only [xPath]
  field_simp
  linear_combination (lam1 ρ κ σ * fiscalLoad r σ κ ρ σs) * hI
    - (fiscalLoad r σ κ ρ σs * ∫ u in a..b, ouNoise (lam2 ρ κ σ) w u) * hm

/-- **Cochrane (2023), (5.86), p. 162, on a path**: over every `[a, b]`,
`π_b − π_a = ∫_a^b (ρπ − κx) + R_π(0)(w_b − w_a)`. -/
theorem pi_incr (hκ : 0 < κ) (hw : Continuous w) (a b : ℝ) :
    piPath r σ κ ρ σi σs w b - piPath r σ κ ρ σi σs w a
      = (∫ u in a..b, (ρ * piPath r σ κ ρ σi σs w u - κ * xPath r σ κ ρ σi σs w u))
        + respPi r σ κ ρ σi σs 0 * (w b - w a) := by
  have hI := ouNoise_incr (lam2 ρ κ σ) hw a b
  have hs := lam_sub ρ κ σ
  have hint : (∫ u in a..b, (ρ * piPath r σ κ ρ σi σs w u - κ * xPath r σ κ ρ σi σs w u))
      = -(lam2 ρ κ σ * fiscalLoad r σ κ ρ σs) * ∫ u in a..b, ouNoise (lam2 ρ κ σ) w u := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    simp only [piPath, xPath]
    field_simp
    linear_combination (-(fiscalLoad r σ κ ρ σs * ouNoise (lam2 ρ κ σ) w u)) * hs
  rw [hint, respPi_zero]
  simp only [piPath]
  linear_combination fiscalLoad r σ κ ρ σs * hI

/-- **Cochrane (2023), (5.88)/(5.93), pp. 162–164, on a path: the value of debt has no
innovation.** `v` is differentiable at every date with `v̇ = rv + i − π − s̃`. -/
theorem v_hasDerivAt (hr : r ≠ 0) (hw : Continuous w) (t : ℝ) :
    HasDerivAt (vPath r σ κ ρ σs w)
      (r * vPath r σ κ ρ σs w t + iPath σi w t - piPath r σ κ ρ σi σs w t - sPath σs w t) t := by
  have h := (hasDerivAt_sub_ouNoise (lam2 ρ κ σ) hw t).const_mul (σs / r)
  refine h.congr_deriv ?_
  simp only [vPath, iPath, piPath, sPath, fiscalLoad]
  field_simp
  ring

/-- Cochrane (2023), (5.93), p. 164: the value of debt is continuous. -/
theorem continuous_vPath (hw : Continuous w) : Continuous (vPath r σ κ ρ σs w) := by
  have := continuous_ouNoise (lam2 ρ κ σ) hw
  unfold vPath
  fun_prop

/-- Cochrane (2023), (5.94), p. 164: inflation is continuous. -/
theorem continuous_piPath (hw : Continuous w) : Continuous (piPath r σ κ ρ σi σs w) := by
  have := continuous_ouNoise (lam2 ρ κ σ) hw
  unfold piPath
  fun_prop

/-- Cochrane (2023), (5.92), p. 164: output is continuous. -/
theorem continuous_xPath (hw : Continuous w) : Continuous (xPath r σ κ ρ σi σs w) := by
  have := continuous_ouNoise (lam2 ρ κ σ) hw
  unfold xPath
  fun_prop

/-- Cochrane (2023), (5.88), p. 162, in increment form: `v_b − v_a = ∫_a^b (rv + i − π − s̃)`. -/
theorem v_incr (hr : r ≠ 0) (hw : Continuous w) (a b : ℝ) :
    vPath r σ κ ρ σs w b - vPath r σ κ ρ σs w a
      = ∫ u in a..b, (r * vPath r σ κ ρ σs w u + iPath σi w u - piPath r σ κ ρ σi σs w u
        - sPath σs w u) := by
  have hc : Continuous fun u => r * vPath r σ κ ρ σs w u + iPath σi w u
      - piPath r σ κ ρ σi σs w u - sPath σs w u := by
    have := continuous_vPath (r := r) (σ := σ) (κ := κ) (ρ := ρ) (σs := σs) hw
    have := continuous_piPath (r := r) (σ := σ) (κ := κ) (ρ := ρ) (σi := σi) (σs := σs) hw
    simp only [iPath, sPath]
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => v_hasDerivAt hr hw x)
    (hc.intervalIntegrable a b)]

/-- **Cochrane (2023), (5.87), p. 162, on a path: the price level is differentiable**,
`ṗ = π` at every date (no jump, no diffusion: `dp = E_t dp = π dt`). -/
theorem p_hasDerivAt (hw : Continuous w) (t : ℝ) :
    HasDerivAt (pPath r σ κ ρ σi σs w) (piPath r σ κ ρ σi σs w t) t :=
  ((continuous_piPath hw).integral_hasStrictDerivAt 0 t).hasDerivAt

/-- Cochrane (2023), (5.89)–(5.90), pp. 162–163: `i_b − i_a = σ_i(w_b − w_a)` and
`s̃_b − s̃_a = σ_s(w_b − w_a)`. -/
theorem shocks_incr (a b : ℝ) :
    iPath σi w b - iPath σi w a = σi * (w b - w a) ∧
      sPath σs w b - sPath σs w a = σs * (w b - w a) := by
  simp only [iPath, sPath]
  constructor <;> ring

/-- Cochrane (2023), §5.7.1, p. 164 ("before time 0, all variables are at the steady state"):
with `w_0 = 0` every variable starts at `0`; in particular `v_0 = 0` (debt predetermined) and
`p_0 = 0`. -/
theorem path_zero (hw0 : w 0 = 0) :
    xPath r σ κ ρ σi σs w 0 = 0 ∧ piPath r σ κ ρ σi σs w 0 = 0 ∧ vPath r σ κ ρ σs w 0 = 0 ∧
      pPath r σ κ ρ σi σs w 0 = 0 := by
  simp [xPath, piPath, vPath, pPath, ouNoise_zero, hw0]

/-- **Cochrane (2023), (5.85)–(5.90), pp. 162–163: the solution on every continuous path.**
For `r ≠ 0`, `κ, σ > 0`, over every interval `[a, b]`: the IS curve with expectational error
`R_x(0)dw`, the Phillips curve with expectational error `R_π(0)dw`, the debt equation with no
error term, `ṗ = π`, and the shock equations. -/
theorem path_solves (hr : r ≠ 0) (hκ : 0 < κ) (hσ : 0 < σ) (hw : Continuous w) (a b : ℝ) :
    (xPath r σ κ ρ σi σs w b - xPath r σ κ ρ σi σs w a
      = (∫ u in a..b, σ * (iPath σi w u - piPath r σ κ ρ σi σs w u))
        + respX r σ κ ρ σi σs 0 * (w b - w a)) ∧
    (piPath r σ κ ρ σi σs w b - piPath r σ κ ρ σi σs w a
      = (∫ u in a..b, (ρ * piPath r σ κ ρ σi σs w u - κ * xPath r σ κ ρ σi σs w u))
        + respPi r σ κ ρ σi σs 0 * (w b - w a)) ∧
    (vPath r σ κ ρ σs w b - vPath r σ κ ρ σs w a
      = ∫ u in a..b, (r * vPath r σ κ ρ σs w u + iPath σi w u - piPath r σ κ ρ σi σs w u
        - sPath σs w u)) ∧
    (∀ t, HasDerivAt (pPath r σ κ ρ σi σs w) (piPath r σ κ ρ σi σs w t) t) ∧
    iPath σi w b - iPath σi w a = σi * (w b - w a) ∧
    sPath σs w b - sPath σs w a = σs * (w b - w a) :=
  ⟨x_incr hκ hσ hw a b, pi_incr hκ hw a b, v_incr hr hw a b, p_hasDerivAt hw,
    (shocks_incr (σi := σi) (σs := σs) a b).1, (shocks_incr (σi := σi) (σs := σs) a b).2⟩

/-! ### The responses are the step equilibrium of `CTSimple` -/

/-- **Cochrane (2023), (5.96), p. 166: the responses are the book's deterministic responses.**
Every equilibrium of `CTSimple` after a time-`0` step to `i₀ = σ_i`, `s̃₀ = σ_s` from `v₀ = 0`
(i.e. the response to a unit MIT shock) is `(R_x, R_π, R_v)` on `[0, ∞)`. -/
theorem resp_eq_ct_step (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ) {x infl v : ℝ → ℝ}
    (h : IsCTEquilibrium r σ κ ρ 0 (fun _ => σi) (fun _ => σs) x infl v) (τ : ℝ) (hτ : 0 ≤ τ) :
    infl τ = respPi r σ κ ρ σi σs τ ∧ x τ = respX r σ κ ρ σi σs τ ∧
      v τ = respV r σ κ ρ σs τ := by
  have hπ := ct_step_solution hr hκ hσ h τ hτ
  have hπ0 := ct_step_solution hr hκ hσ h 0 le_rfl
  have hx := (ct_step_family hκ hσ h.1 τ hτ).2
  have hv := (ct_step_debt hr hκ hσ h τ hτ).2
  simp only [mul_zero, neg_zero, exp_zero, mul_one] at hπ0
  refine ⟨?_, ?_, ?_⟩
  · rw [hπ, respPi, fiscalLoad]
    ring
  · rw [hx, hπ0, respX, fiscalLoad]
    ring
  · rw [respV]
    linear_combination hv

/-! ### A single jump at the news date -/

/-- Cochrane (2023), §5.7, p. 164 ("MIT shocks, one-time unexpected shocks `dε₀` at time 0, and
perfect foresight thereafter"): the driving path with one jump of size `Δ` at date `u`. -/
noncomputable def jumpPath (u Δ : ℝ) (t : ℝ) : ℝ := if u < t then Δ else 0

/-- Cochrane (2023), §5.7, p. 164: the OU noise of the jump path is `Δe^{−η(t−u)}` after the
jump (`0 ≤ u < t`, `η ≠ 0`). -/
theorem ouNoise_jumpPath_of_lt {η u Δ t : ℝ} (hη : η ≠ 0) (hu : 0 ≤ u) (hut : u < t) :
    ouNoise η (jumpPath u Δ) t = Δ * exp (-(η * (t - u))) := by
  have hcont : Continuous fun s => exp (η * s) * Δ := by fun_prop
  have h0 : IntervalIntegrable (fun s => exp (η * s) * jumpPath u Δ s) volume 0 u := by
    refine (intervalIntegrable_iff.2 ?_)
    refine (integrableOn_zero).congr_fun (fun s hs => ?_) measurableSet_uIoc
    rw [Set.uIoc_of_le hu] at hs
    simp [jumpPath, not_lt.2 hs.2]
  have h1 : IntervalIntegrable (fun s => exp (η * s) * jumpPath u Δ s) volume u t := by
    refine (intervalIntegrable_iff.2 ?_)
    refine ((hcont.intervalIntegrable u t).def').congr_fun (fun s hs => ?_) measurableSet_uIoc
    rw [Set.uIoc_of_le hut.le] at hs
    simp [jumpPath, hs.1]
  have hP : ouPrim η (jumpPath u Δ) t = Δ * ((exp (η * t) - exp (η * u)) / η) := by
    rw [ouPrim, ← intervalIntegral.integral_add_adjacent_intervals h0 h1]
    have e0 : (∫ s in (0 : ℝ)..u, exp (η * s) * jumpPath u Δ s) = 0 := by
      rw [intervalIntegral.integral_of_le hu]
      refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
      simp [jumpPath, not_lt.2 hs.2]
    have e1 : (∫ s in u..t, exp (η * s) * jumpPath u Δ s) = ∫ s in u..t, exp (η * s) * Δ := by
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
      rw [Set.uIoc_of_le hut.le] at hs
      simp [jumpPath, hs.1]
    have hd : ∀ s ∈ Set.uIcc u t, HasDerivAt (fun s => exp (η * s) / η * Δ)
        (exp (η * s) * Δ) s := by
      intro s _
      have := ((((hasDerivAt_id' s).const_mul η).exp).div_const η).mul_const Δ
      refine this.congr_deriv ?_
      field_simp
    rw [e0, e1, zero_add, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (hcont.intervalIntegrable u t)]
    ring
  have he : exp (-η * t) * exp (η * t) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  have he2 : exp (-η * t) * exp (η * u) = exp (-(η * (t - u))) := by rw [← exp_add]; ring_nf
  simp only [ouNoise, hP, jumpPath, hut, ↓reduceIte]
  have key : η * (exp (-η * t) * (Δ * ((exp (η * t) - exp (η * u)) / η)))
      = Δ * (exp (-η * t) * exp (η * t) - exp (-η * t) * exp (η * u)) := by
    field_simp
  rw [key, he, he2]
  ring

/-- Cochrane (2023), §5.7, p. 164: before (and at) the news date the OU noise of the jump path
is `0` (`0 ≤ t ≤ u`). -/
theorem ouNoise_jumpPath_of_le {η u Δ t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    ouNoise η (jumpPath u Δ) t = 0 := by
  have hP : ouPrim η (jumpPath u Δ) t = 0 := by
    rw [ouPrim, intervalIntegral.integral_of_le ht]
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
    simp [jumpPath, not_lt.2 (hs.2.trans htu)]
  simp [ouNoise, hP, jumpPath, not_lt.2 htu]

/-- **Cochrane (2023), §5.7, p. 164 and (5.96), p. 166: the solution map applied to a jump at
the news date gives the impulse response.** For `0 ≤ u < t`, `π_t = Δ R_π(t − u)`; for
`0 ≤ t ≤ u`, `π_t = 0`. -/
theorem pi_jumpPath (hκ : 0 < κ) (hσ : 0 < σ) {u Δ t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) :
    piPath r σ κ ρ σi σs (jumpPath u Δ) t
      = if u < t then Δ * respPi r σ κ ρ σi σs (t - u) else 0 := by
  have h2 := (lam2_pos (ρ := ρ) hκ hσ).ne'
  by_cases hut : u < t
  · simp only [piPath, ouNoise_jumpPath_of_lt h2 hu hut, jumpPath, hut, ↓reduceIte, respPi]
    ring
  · simp only [piPath, ouNoise_jumpPath_of_le ht (not_lt.1 hut), jumpPath, hut, ↓reduceIte]
    ring

/-- Cochrane (2023), §5.7, p. 164 and p. 166: the output response to a jump at the news date,
`x_t = Δ R_x(t − u)` after `u`, `0` before. -/
theorem x_jumpPath (hκ : 0 < κ) (hσ : 0 < σ) {u Δ t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) :
    xPath r σ κ ρ σi σs (jumpPath u Δ) t
      = if u < t then Δ * respX r σ κ ρ σi σs (t - u) else 0 := by
  have h2 := (lam2_pos (ρ := ρ) hκ hσ).ne'
  by_cases hut : u < t
  · simp only [xPath, ouNoise_jumpPath_of_lt h2 hu hut, jumpPath, hut, ↓reduceIte, respX]
    ring
  · simp only [xPath, ouNoise_jumpPath_of_le ht (not_lt.1 hut), jumpPath, hut, ↓reduceIte]
    ring

/-- Cochrane (2023), §5.7, p. 164 and p. 166: the debt response to a jump at the news date,
`v_t = Δ R_v(t − u)` after `u`, `0` before. -/
theorem v_jumpPath (hκ : 0 < κ) (hσ : 0 < σ) {u Δ t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) :
    vPath r σ κ ρ σs (jumpPath u Δ) t = if u < t then Δ * respV r σ κ ρ σs (t - u) else 0 := by
  have h2 := (lam2_pos (ρ := ρ) hκ hσ).ne'
  by_cases hut : u < t
  · simp only [vPath, ouNoise_jumpPath_of_lt h2 hu hut, jumpPath, hut, ↓reduceIte, respV]
    ring
  · simp only [vPath, ouNoise_jumpPath_of_le ht (not_lt.1 hut), jumpPath, hut, ↓reduceIte]
    ring

/-- Cochrane (2023), §5.7, p. 164 (the deterministic case `σ = 0`): with no shock loadings,
`σ_i = σ_s = 0`, the solution is the steady state, `x = π = v = 0`. -/
theorem stoch_zero_loading (w : ℝ → ℝ) (t : ℝ) :
    xPath r σ κ ρ 0 0 w t = 0 ∧ piPath r σ κ ρ 0 0 w t = 0 ∧ vPath r σ κ ρ 0 w t = 0 := by
  simp [xPath, piPath, vPath, fiscalLoad]

end Cochrane.StickyPriceFiscal.TidyR7StochCTPath
