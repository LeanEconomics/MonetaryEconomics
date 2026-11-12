/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR8StochKernel
import StickyPriceFiscal.CTSurplus
import StickyPriceFiscal.CTRulesEquilibrium

/-!
# Long-term debt, policy rules and coordination with Brownian shocks

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §§5.7.3–5.7.5,
pp. 169–179, (5.105)–(5.117).

`CTRules` and `CTRulesEquilibrium` treat (5.105)–(5.113) with the shocks `dε`, `dδ` as jumps at
the news date. Here the monetary shock is a diffusion, `dε_i = σ_i dW`, and the expectational
errors are processes.

## Main results

* **The partial-adjustment rate (5.107), (5.112)** with `θ_{iπ} = θ_{ix} = 0` (Figs. 5.11–5.13):
  `rate_incr` (on every path `di = −ζ(i − u_i)dt + θσ_i dW`, `du_i = −ηu_i dt + σ_i dW`),
  `rate_ito` (`i_T = ∫_0^T σ_i R_i(T − u) dW_u` a.s.) with the response `rateIRF` of
  `CTRulesEquilibrium.fig511i` (`rateIRF_fig511`).
* **The bond price (5.105) with a diffusive rate**, for any two-mode rate
  `i = c₁Y^η + c₂Y^ζ`: `bond_incr` (on every path `dq = ((r+ω)q + i)dt + dδ_q` with
  `dδ_q = δ dW`), `bondLoading_eq` (the bond-price innovation is minus the discounted rate
  response, `δ = −∫_0^∞ e^{−(r+ω)τ}R_i(τ)dτ`), `bondKernel_eq_fwd` (the `dW`-loading of `q(T)` at
  horizon `τ` is the deterministic bond price `−∫e^{−(r+ω)s}R_i(τ + s)ds` of
  `CTRules.ct_bond_price`),
  `bond_ito`, `bond_book_equation` (`E_t dq = ((r+ω)q + i)dt`), **`bond_valuation_L1`**
  (`q_t = −E_t∫_t^∞ e^{−(r+ω)(τ−t)}i_τ dτ`) and **`bond_unique`** (every regular adapted solution
  of the `E_t[·]`-equation is `q`).
* **The `v − v*` elimination (p. 172) under diffusion**, `elim_stoch`: if the two debt
  equations (5.106), (5.109) share the bond-price innovation, (5.110) holds as
  `E_t[(π* − π)_T − (π* − π)_t] = 0`, all processes are regular (the stochastic
  transversality condition) and `v*₀ = v₀` (E49), then `v* = v` and `π* = π` a.s. at every
  date; so `dδ_π = dπ* − E_t dπ* = −β_s dε_s − β_i dε_i` (5.111).
* **"Fiscal policy chooses only unexpected inflation" (p. 177) under diffusion**,
  `pinned_by_innovation`: given the interest-rate process, two solutions of the `E_t[·]` IS
  curve and the Phillips curve with the same inflation innovation process and the same `π₀` are
  equal a.s. at every date — whatever the fiscal rules.
* No covariation correction: in (5.105)–(5.113) the price level is `C¹` (`dp = π dt`), so the
  only diffusive factors are `q`, `v`, `i`, `π`, which enter linearly; `bond_bracket` computes
  `[q, W] = δ t` and `bond_price_level_bracket` shows `[q, p] = 0` for any `C¹` price level
  (the nonlinear `QB/P` needs no Itô term).
* Non-vacuity on `bmPath`: `bmPath_bond`.
-/

namespace Cochrane.StickyPriceFiscal.TidyR8StochCTRules

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.StickyPriceFiscal.TidyR7StieltjesSums Cochrane.StickyPriceFiscal.TidyR7BrownianTools
open Cochrane.StickyPriceFiscal.TidyR7BrownianQV Cochrane.StickyPriceFiscal.TidyR7ItoIntegral
open Cochrane.StickyPriceFiscal.TidyR7ItoBridge Cochrane.StickyPriceFiscal.TidyR7BrownianExist
open Cochrane.StickyPriceFiscal.TidyR7BrownianSchauder Cochrane.StickyPriceFiscal.TidyR7ItoSums
open Cochrane.StickyPriceFiscal.TidyR7StieltjesCalculus
open Cochrane.StickyPriceFiscal.TidyR7StochCTPath Cochrane.StickyPriceFiscal.TidyR7StochCTBrownian
open Cochrane.StickyPriceFiscal.TidyR7StochCTUnique Cochrane.StickyPriceFiscal.TidyR8StochKernel
open Cochrane.StickyPriceFiscal.CTSimple
open scoped ENNReal NNReal

/-! ### The partial-adjustment interest rate -/

/-- Cochrane (2023), (5.107), (5.112), p. 169: the response of `i` to a unit monetary shock
with partial adjustment `ζ`, disturbance persistence `η` and impact `θ = θ_{iε}`,
`R_i(τ) = ζ/(ζ−η) e^{−ητ} + (θ − ζ/(ζ−η)) e^{−ζτ}`. -/
noncomputable def rateIRF (θ ζ η τ : ℝ) : ℝ :=
  ζ / (ζ - η) * exp (-(η * τ)) + (θ - ζ / (ζ - η)) * exp (-(ζ * τ))

/-- Cochrane (2023), Figs. 5.11–5.13, p. 175: with `θ_{iε} = 1/4`, `ζ_i = 1`, `η_i = 0.3`,
`R_i(τ)` is the rate path `CTRulesEquilibrium.fig511i`. -/
theorem rateIRF_fig511 (τ : ℝ) :
    rateIRF (1 / 4) 1 (3 / 10) τ = CTRulesEquilibrium.fig511i τ := by
  simp only [rateIRF, CTRulesEquilibrium.fig511i]
  norm_num
  ring

/-- Cochrane (2023), (5.112), p. 169: the disturbance `u_i = σ_iY^η`. -/
noncomputable def uiPath (σi η : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ := σi * ouNoise η w t

/-- Cochrane (2023), (5.107), p. 169: the rate
`i = σ_i(θY^ζ + ζ(Y^η − Y^ζ)/(ζ − η))`. -/
noncomputable def ratePath (σi θ ζ η : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  σi * (θ * ouNoise ζ w t + ζ * (ouNoise η w t - ouNoise ζ w t) / (ζ - η))

variable {w : ℝ → ℝ}

/-- Cochrane (2023), (5.107), p. 169: the `C¹` part `i − θσ_i w` has derivative `−ζ(i − u_i)`. -/
theorem rate_sub_hasDerivAt {σi θ ζ η : ℝ} (h : ζ - η ≠ 0) (hw : Continuous w) (t : ℝ) :
    HasDerivAt (fun u => ratePath σi θ ζ η w u - θ * σi * w u)
      (-ζ * (ratePath σi θ ζ η w t - uiPath σi η w t)) t := by
  have h1 := hasDerivAt_sub_ouNoise ζ hw t
  have h2 := hasDerivAt_sub_ouNoise η hw t
  have hf : (fun u => ratePath σi θ ζ η w u - θ * σi * w u) = fun u =>
      σi * (-θ * (w u - ouNoise ζ w u) + ζ * ((w u - ouNoise ζ w u)
        - (w u - ouNoise η w u)) / (ζ - η)) := by
    funext u
    simp only [ratePath]
    ring
  rw [hf]
  refine ((HasDerivAt.add (h1.const_mul (-θ)) (((HasDerivAt.sub h1 h2).const_mul ζ).div_const
    (ζ - η))).const_mul σi).congr_deriv ?_
  simp only [ratePath, uiPath]
  field_simp
  ring

/-- **Cochrane (2023), (5.107), (5.112), p. 169, on every path**: over every `[a, b]`,
`i_b − i_a = ∫_a^b −ζ(i − u_i) + θσ_i(w_b − w_a)` and
`u_b − u_a = −η∫_a^b u_i + σ_i(w_b − w_a)`. -/
theorem rate_incr {σi θ ζ η : ℝ} (h : ζ - η ≠ 0) (hw : Continuous w) (a b : ℝ) :
    ratePath σi θ ζ η w b - ratePath σi θ ζ η w a
        = (∫ u in a..b, -ζ * (ratePath σi θ ζ η w u - uiPath σi η w u)) + θ * σi * (w b - w a)
      ∧ uiPath σi η w b - uiPath σi η w a
        = -η * (∫ u in a..b, uiPath σi η w u) + σi * (w b - w a) := by
  have hYz := continuous_ouNoise ζ hw
  have hYe := continuous_ouNoise η hw
  have hc : Continuous fun u => -ζ * (ratePath σi θ ζ η w u - uiPath σi η w u) := by
    unfold ratePath uiPath
    fun_prop
  refine ⟨?_, ?_⟩
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => rate_sub_hasDerivAt (σi := σi) (θ := θ) h hw x) (hc.intervalIntegrable a b)]
    ring
  · have hI := ouNoise_incr η hw a b
    simp only [uiPath]
    rw [intervalIntegral.integral_const_mul]
    linear_combination σi * hI

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-- Cochrane (2023), (5.107), p. 169: the rate as a process. -/
noncomputable def rateProc (σi θ ζ η : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ratePath σi θ ζ η (fun u => bmReal W u ω) t

/-- Cochrane (2023), (5.107), p. 169: the rate is the two-mode process with loadings
`σ_iζ/(ζ−η)` on `Y^η` and `σ_i(θ − ζ/(ζ−η))` on `Y^ζ`. -/
theorem rateProc_eq_ker2 {σi θ ζ η : ℝ} (h : ζ - η ≠ 0) : rateProc σi θ ζ η W = fun t =>
    ker2Proc W 0 (σi * (ζ / (ζ - η))) η (σi * (θ - ζ / (ζ - η))) ζ t := by
  funext t ω
  rw [ker2Proc_eq]
  simp only [rateProc, ratePath]
  field_simp
  ring

/-- **Cochrane (2023), (5.107), (5.112), p. 169, and Figs. 5.11–5.13: the rate is the response
`R_i(τ)` integrated against `dW`.** For `ζ ≠ η` and `T ≥ 0`, a.s.
`i_T = ∫_0^T σ_iR_i(T − u) dW_u`. -/
theorem rate_ito (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {σi θ ζ η : ℝ} (h : ζ - η ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    rateProc σi θ ζ η W T =ᵐ[P] itoInt P 𝓕 W (fun u _ => σi * rateIRF θ ζ η (T - u)) 0 T := by
  rw [rateProc_eq_ker2 h]
  have e : (fun u (_ : Ω) => σi * rateIRF θ ζ η (T - u)) = fun u _ =>
      ker2Fn 0 (σi * (ζ / (ζ - η))) η (σi * (θ - ζ / (ζ - η))) ζ (T - u) := by
    funext u _
    simp only [rateIRF, ker2Fn]
    ring
  rw [e]
  exact ker2Proc_ae_eq_itoInt hB hW h𝓕 hcont hW0 _ _ _ _ _ hT

/-! ### The bond price (5.105) -/

/-- Cochrane (2023), (5.105), p. 169: a two-mode interest rate `i = c₁Y^η + c₂Y^ζ`. -/
noncomputable def rate2Path (c₁ η c₂ ζ : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  c₁ * ouNoise η w t + c₂ * ouNoise ζ w t

/-- Cochrane (2023), (5.105), p. 169: the bond price
`q = −(c₁/(R+η) Y^η + c₂/(R+ζ) Y^ζ)` with `R = r + ω`. -/
noncomputable def bondPath (R c₁ η c₂ ζ : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(c₁ / (R + η) * ouNoise η w t + c₂ / (R + ζ) * ouNoise ζ w t)

/-- Cochrane (2023), (5.114), p. 170: the loading of the unexpected bond return,
`δ = −(c₁/(R+η) + c₂/(R+ζ))` (`dδ_q = δ dW`). -/
noncomputable def bondLoading (R c₁ η c₂ ζ : ℝ) : ℝ := -(c₁ / (R + η) + c₂ / (R + ζ))

/-- Cochrane (2023), (5.105), p. 169: `q − δw` has derivative `Rq + i`. -/
theorem bond_sub_hasDerivAt {R c₁ η c₂ ζ : ℝ} (h1 : R + η ≠ 0) (h2 : R + ζ ≠ 0)
    (hw : Continuous w) (t : ℝ) :
    HasDerivAt (fun u => bondPath R c₁ η c₂ ζ w u - bondLoading R c₁ η c₂ ζ * w u)
      (R * bondPath R c₁ η c₂ ζ w t + rate2Path c₁ η c₂ ζ w t) t := by
  have ha := hasDerivAt_sub_ouNoise η hw t
  have hb := hasDerivAt_sub_ouNoise ζ hw t
  have hf : (fun u => bondPath R c₁ η c₂ ζ w u - bondLoading R c₁ η c₂ ζ * w u) = fun u =>
      c₁ / (R + η) * (w u - ouNoise η w u) + c₂ / (R + ζ) * (w u - ouNoise ζ w u) := by
    funext u
    simp only [bondPath, bondLoading]
    ring
  rw [hf]
  refine (HasDerivAt.add (ha.const_mul _) (hb.const_mul _)).congr_deriv ?_
  simp only [bondPath, rate2Path]
  field_simp
  ring

/-- **Cochrane (2023), (5.105), p. 169, on every path**: over every `[a, b]`,
`q_b − q_a = ∫_a^b ((r+ω)q + i) + δ(w_b − w_a)`: the bond price has the expectational error
`dδ_q = δ dw`. -/
theorem bond_incr {R c₁ η c₂ ζ : ℝ} (h1 : R + η ≠ 0) (h2 : R + ζ ≠ 0) (hw : Continuous w)
    (a b : ℝ) :
    bondPath R c₁ η c₂ ζ w b - bondPath R c₁ η c₂ ζ w a
      = (∫ u in a..b, (R * bondPath R c₁ η c₂ ζ w u + rate2Path c₁ η c₂ ζ w u))
        + bondLoading R c₁ η c₂ ζ * (w b - w a) := by
  have hYe := continuous_ouNoise η hw
  have hYz := continuous_ouNoise ζ hw
  have hc : Continuous fun u => R * bondPath R c₁ η c₂ ζ w u + rate2Path c₁ η c₂ ζ w u := by
    unfold bondPath rate2Path
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => bond_sub_hasDerivAt h1 h2 hw x) (hc.intervalIntegrable a b)]
  ring

/-- **Cochrane (2023), (5.114), p. 170: the bond-price innovation is minus the discounted rate
response**: for `R + η > 0`, `R + ζ > 0`,
`δ = −∫_0^∞ e^{−Rτ}(c₁e^{−ητ} + c₂e^{−ζτ}) dτ`. -/
theorem bondLoading_eq {R c₁ η c₂ ζ : ℝ} (h1 : 0 < R + η) (h2 : 0 < R + ζ) :
    bondLoading R c₁ η c₂ ζ
      = -∫ τ in Set.Ioi 0, exp (-(R * τ)) * (c₁ * exp (-(η * τ)) + c₂ * exp (-(ζ * τ))) := by
  have h := (CTSurplus.hs_pv ![c₁, c₂] ![η, ζ] (r := R)
    (fun k => by fin_cases k <;> simp [h1, h2]) 0).2
  simp only [zero_add] at h
  have e : (fun τ => exp (-(R * τ)) * (c₁ * exp (-(η * τ)) + c₂ * exp (-(ζ * τ))))
      = fun τ => exp (-(R * τ)) * CTSurplus.expSum ![c₁, c₂] ![η, ζ] τ := by
    funext τ
    simp [CTSurplus.expSum, Fin.sum_univ_two]
  rw [e, h]
  simp [CTSurplus.expSum, Fin.sum_univ_two, bondLoading]

/-- **Cochrane (2023), (5.105), p. 169, and `CTRules.ct_bond_price`: the bond-price kernel is
the deterministic bond price.** For `R + η > 0`, `R + ζ > 0` and every horizon `τ`,
`−(c₁/(R+η)e^{−ητ} + c₂/(R+ζ)e^{−ζτ}) = −∫_0^∞ e^{−Rs}R_i(τ + s) ds` with
`R_i = c₁e^{−η·} + c₂e^{−ζ·}`. -/
theorem bondKernel_eq_fwd {R c₁ η c₂ ζ : ℝ} (h1 : 0 < R + η) (h2 : 0 < R + ζ) (τ : ℝ) :
    -(c₁ / (R + η) * exp (-(η * τ)) + c₂ / (R + ζ) * exp (-(ζ * τ)))
      = -fwdInt R (fun s => c₁ * exp (-(η * s)) + c₂ * exp (-(ζ * s))) τ := by
  have h := (CTSurplus.hs_pv ![c₁, c₂] ![η, ζ] (r := R)
    (fun k => by fin_cases k <;> simp [h1, h2]) τ).2
  have e : (fun s => exp (-(R * s)) * (c₁ * exp (-(η * (τ + s))) + c₂ * exp (-(ζ * (τ + s)))))
      = fun s => exp (-(R * s)) * CTSurplus.expSum ![c₁, c₂] ![η, ζ] (τ + s) := by
    funext s
    simp [CTSurplus.expSum, Fin.sum_univ_two]
  simp only [fwdInt]
  rw [e, h]
  simp [CTSurplus.expSum, Fin.sum_univ_two]

/-- Cochrane (2023), (5.105), p. 169: the two-mode rate as a process. -/
noncomputable def rate2Proc (c₁ η c₂ ζ : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  rate2Path c₁ η c₂ ζ (fun u => bmReal W u ω) t

/-- Cochrane (2023), (5.105), p. 169: the bond price as a process. -/
noncomputable def bondProc (R c₁ η c₂ ζ : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  bondPath R c₁ η c₂ ζ (fun u => bmReal W u ω) t

/-- Cochrane (2023), (5.105), p. 169: the rate is a two-mode process. -/
theorem rate2Proc_eq_ker2 {c₁ η c₂ ζ : ℝ} :
    rate2Proc c₁ η c₂ ζ W = fun t => ker2Proc W 0 c₁ η c₂ ζ t := by
  funext t ω
  rw [ker2Proc_eq]
  simp only [rate2Proc, rate2Path]
  ring

/-- Cochrane (2023), (5.105), p. 169: the bond price is a two-mode process. -/
theorem bondProc_eq_ker2 {R c₁ η c₂ ζ : ℝ} : bondProc R c₁ η c₂ ζ W = fun t =>
    ker2Proc W 0 (-(c₁ / (R + η))) η (-(c₂ / (R + ζ))) ζ t := by
  funext t ω
  rw [ker2Proc_eq]
  simp only [bondProc, bondPath]
  ring

/-- **Cochrane (2023), (5.105), p. 169: the bond price is its deterministic response
integrated against `dW`.** For `T ≥ 0`, a.s.
`q_T = ∫_0^T −(c₁/(R+η)e^{−η(T−u)} + c₂/(R+ζ)e^{−ζ(T−u)}) dW_u`. -/
theorem bond_ito (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (R c₁ η c₂ ζ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    bondProc R c₁ η c₂ ζ W T =ᵐ[P] itoInt P 𝓕 W (fun u _ => -(c₁ / (R + η) * exp (-(η * (T - u)))
      + c₂ / (R + ζ) * exp (-(ζ * (T - u))))) 0 T := by
  rw [bondProc_eq_ker2]
  have e : (fun u (_ : Ω) => -(c₁ / (R + η) * exp (-(η * (T - u)))
      + c₂ / (R + ζ) * exp (-(ζ * (T - u))))) = fun u _ =>
        ker2Fn 0 (-(c₁ / (R + η))) η (-(c₂ / (R + ζ))) ζ (T - u) := by
    funext u _
    simp only [ker2Fn]
    ring
  rw [e]
  exact ker2Proc_ae_eq_itoInt hB hW h𝓕 hcont hW0 _ _ _ _ _ hT

/-- **Cochrane (2023), (5.105), p. 169, in the book's `E_t d` form**: for `0 ≤ t ≤ T`,
`E_t[q_T − q_t] = E_t∫_t^T ((r+ω)q + i)` a.s. -/
theorem bond_book_equation (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {R c₁ η c₂ ζ : ℝ} (h1 : R + η ≠ 0) (h2 : R + ζ ≠ 0) {t T : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) :
    P[fun ω => bondProc R c₁ η c₂ ζ W T ω - bondProc R c₁ η c₂ ζ W t ω | 𝓕 t]
      =ᵐ[P] P[fun ω => ∫ u in t..T, (R * bondProc R c₁ η c₂ ζ W u ω
        + rate2Proc c₁ η c₂ ζ W u ω) | 𝓕 t] := by
  have iq : ∀ τ, 0 ≤ τ → Integrable (bondProc R c₁ η c₂ ζ W τ) P := fun τ hτ => by
    rw [bondProc_eq_ker2]
    exact integrable_ker2Proc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 _ _ _ _ _ hτ
  refine condExp_drift (c := bondLoading R c₁ η c₂ ζ) hB hW h𝓕 ht htT
    ((iq T (ht.trans htT)).sub (iq t ht)) fun ω => ?_
  have := bond_incr (c₁ := c₁) (c₂ := c₂) h1 h2 (continuous_bmReal (hcont ω)) t T
  simp only [bondProc, rate2Proc, incr]
  linarith

/-- Cochrane (2023), (5.105), p. 169: on every path,
`−∫_t^T e^{−R(τ−t)}i_τ dτ = q_t − e^{−R(T−t)}q_T + δ∫_t^T e^{−R(τ−t)}dW_τ`. -/
theorem bond_pv_identity {R c₁ η c₂ ζ : ℝ} (h1 : R + η ≠ 0) (h2 : R + ζ ≠ 0)
    (hcont : ∀ ω, Continuous fun t => W t ω) (t T : ℝ) (ω : Ω) :
    -(∫ τ in t..T, exp (-(R * (τ - t))) * rate2Proc c₁ η c₂ ζ W τ ω)
      = bondProc R c₁ η c₂ ζ W t ω - exp (-(R * (T - t))) * bondProc R c₁ η c₂ ζ W T ω
        + bondLoading R c₁ η c₂ ζ * expWiener R W t T ω := by
  have hw := continuous_bmReal (hcont ω)
  set w := fun u => bmReal W u ω
  have hYe := continuous_ouNoise η hw
  have hYz := continuous_ouNoise ζ hw
  have hc : Continuous fun u => R * bondPath R c₁ η c₂ ζ w u + rate2Path c₁ η c₂ ζ w u := by
    unfold bondPath rate2Path
    fun_prop
  have hBP := discounted_byParts (fun x => bond_sub_hasDerivAt (c₁ := c₁) (c₂ := c₂) h1 h2 hw x)
    hc hw R (bondLoading R c₁ η c₂ ζ) t T
  have e1 : ∀ τ, bondPath R c₁ η c₂ ζ w τ - bondLoading R c₁ η c₂ ζ * w τ
      + bondLoading R c₁ η c₂ ζ * w τ = bondPath R c₁ η c₂ ζ w τ := fun τ => by ring
  simp only [e1] at hBP
  have e2 : (fun τ => exp (-(R * (τ - t))) * (R * bondPath R c₁ η c₂ ζ w τ
      - (R * bondPath R c₁ η c₂ ζ w τ + rate2Path c₁ η c₂ ζ w τ)))
      = fun τ => -(exp (-(R * (τ - t))) * rate2Path c₁ η c₂ ζ w τ) := by
    funext τ
    ring
  rw [e2, intervalIntegral.integral_neg] at hBP
  simp only [rate2Proc, bondProc, expWiener]
  rw [hBP]

/-- **Cochrane (2023), (5.105), p. 169: the bond price is the expected discounted rate path,
`q_t = −E_t∫_t^∞ e^{−(r+ω)(τ−t)}i_τ dτ`.** For `R = r + ω > 0`, `η, ζ ≥ 0`, `t ≥ 0`:
`−E_t∫_t^T e^{−R(τ−t)}i_τ dτ → q_t` in `L¹` as `T → ∞`.
The stochastic version of `CTRules.ct_bond_price`. -/
theorem bond_valuation_L1 (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {R c₁ η c₂ ζ : ℝ} (hR : 0 < R) (hη : 0 ≤ η) (hζ : 0 ≤ ζ) {t : ℝ}
    (ht : 0 ≤ t) :
    Tendsto (fun T => ∫ ω, |-P[fun ω => ∫ τ in t..T, exp (-(R * (τ - t)))
      * rate2Proc c₁ η c₂ ζ W τ ω | 𝓕 t] ω - bondProc R c₁ η c₂ ζ W t ω| ∂P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h1 : R + η ≠ 0 := by linarith
  have h2 : R + ζ ≠ 0 := by linarith
  set K := (|(0 : ℝ)| + |-(c₁ / (R + η))| + |-(c₂ / (R + ζ))|) ^ 2
  refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _)
    ?_ (tendsto_exp_mul_affine hR t K)
  filter_upwards [eventually_ge_atTop t] with T hT
  have iq : ∀ τ, 0 ≤ τ → Integrable (bondProc R c₁ η c₂ ζ W τ) P := fun τ hτ => by
    rw [bondProc_eq_ker2]
    exact integrable_ker2Proc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 _ _ _ _ _ hτ
  have hqm : AEStronglyMeasurable[𝓕 t] (bondProc R c₁ η c₂ ζ W t) P := by
    rw [bondProc_eq_ker2]
    exact aesm_ker2Proc hB hW h𝓕 hcont hW0 _ _ _ _ _ ht
  have iE := integrable_expWiener hB hW h𝓕 hcont R ht hT
  have e : (fun ω => ∫ τ in t..T, exp (-(R * (τ - t))) * rate2Proc c₁ η c₂ ζ W τ ω)
      = (-1 : ℝ) • ((bondProc R c₁ η c₂ ζ W t
        - (exp (-(R * (T - t)))) • bondProc R c₁ η c₂ ζ W T)
          + (bondLoading R c₁ η c₂ ζ) • expWiener R W t T) := by
    funext ω
    have := bond_pv_identity (c₁ := c₁) (c₂ := c₂) h1 h2 hcont t T ω
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    linarith
  have i1 := (iq t ht).sub ((iq T (ht.trans hT)).smul (exp (-(R * (T - t)))))
  have hcond : P[fun ω => ∫ τ in t..T, exp (-(R * (τ - t))) * rate2Proc c₁ η c₂ ζ W τ ω | 𝓕 t]
      =ᵐ[P] fun ω => -(bondProc R c₁ η c₂ ζ W t ω
        - exp (-(R * (T - t))) * P[bondProc R c₁ η c₂ ζ W T | 𝓕 t] ω) := by
    rw [e]
    filter_upwards [condExp_smul (μ := P) (-1 : ℝ) ((bondProc R c₁ η c₂ ζ W t
        - (exp (-(R * (T - t)))) • bondProc R c₁ η c₂ ζ W T)
          + (bondLoading R c₁ η c₂ ζ) • expWiener R W t T) (𝓕 t),
      condExp_add i1 (iE.smul (bondLoading R c₁ η c₂ ζ)) (𝓕 t),
      condExp_sub (iq t ht) ((iq T (ht.trans hT)).smul (exp (-(R * (T - t))))) (𝓕 t),
      condExp_of_aestronglyMeasurable' (𝓕.le t) hqm (iq t ht),
      condExp_smul (μ := P) (exp (-(R * (T - t)))) (bondProc R c₁ η c₂ ζ W T) (𝓕 t),
      condExp_smul (μ := P) (bondLoading R c₁ η c₂ ζ) (expWiener R W t T) (𝓕 t),
      condExp_expWiener hB hW h𝓕 hcont R ht hT] with ω h0 h1' h2' h3 h4 h5 h6
    rw [h0, Pi.smul_apply, h1', Pi.add_apply, h2', Pi.sub_apply, h3, h4, h5]
    simp only [Pi.smul_apply, smul_eq_mul, h6, Pi.zero_apply, mul_zero, add_zero]
    ring
  have e2 : ∫ ω, |-P[fun ω => ∫ τ in t..T, exp (-(R * (τ - t))) * rate2Proc c₁ η c₂ ζ W τ ω
      | 𝓕 t] ω - bondProc R c₁ η c₂ ζ W t ω| ∂P
      = exp (-(R * (T - t))) * ∫ ω, |P[bondProc R c₁ η c₂ ζ W T | 𝓕 t] ω| ∂P := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hcond] with ω hω
    rw [hω, neg_neg, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos (exp_pos _)]
  rw [e2]
  refine mul_le_mul_of_nonneg_left ((integral_abs_condExp_le _).trans ?_) (exp_pos _).le
  rw [bondProc_eq_ker2]
  exact integral_abs_ker2Proc_le hB hW h𝓕 hcont hW0 hη hζ (ht.trans hT)

/-- **Cochrane (2023), (5.105), p. 169: uniqueness of the bond price under uncertainty.** For
`R = r + ω > 0`, `η, ζ ≥ 0`: every regular, adapted process `q'` satisfying the book's equation
`E_t[q'_T − q'_t] = E_t∫_t^T(Rq' + i)` (with ANY expectational error) equals `q` a.s. at every
date `t ≥ 0`: the unstable root `R` is solved forward.
The stochastic version of `CTRules.ct_bond_price`. -/
theorem bond_unique (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {R c₁ η c₂ ζ : ℝ} (hR : 0 < R) (hη : 0 ≤ η) (hζ : 0 ≤ ζ)
    {q' : ℝ → Ω → ℝ} (hq' : RegProc P q') (ha : ∀ t, 0 ≤ t → AEStronglyMeasurable[𝓕 t] (q' t) P)
    (heq : ∀ t T, 0 ≤ t → t ≤ T → P[fun ω => q' T ω - q' t ω | 𝓕 t]
      =ᵐ[P] P[fun ω => ∫ u in t..T, (R * q' u ω + rate2Proc c₁ η c₂ ζ W u ω) | 𝓕 t])
    {t : ℝ} (ht : 0 ≤ t) : q' t =ᵐ[P] bondProc R c₁ η c₂ ζ W t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h1 : R + η ≠ 0 := by linarith
  have h2 : R + ζ ≠ 0 := by linarith
  have hq : RegProc P (bondProc R c₁ η c₂ ζ W) := by
    rw [bondProc_eq_ker2]
    exact regProc_ker2Proc hB hW h𝓕 hcont hW0 hη hζ _ _ _
  have hi : RegProc P (rate2Proc c₁ η c₂ ζ W) := by
    rw [rate2Proc_eq_ker2]
    exact regProc_ker2Proc hB hW h𝓕 hcont hW0 hη hζ _ _ _
  have hqm : AEStronglyMeasurable[𝓕 t] (bondProc R c₁ η c₂ ζ W t) P := by
    rw [bondProc_eq_ker2]
    exact aesm_ker2Proc hB hW h𝓕 hcont hW0 _ _ _ _ _ ht
  have hG' : RegProc P fun u ω => R * q' u ω + 1 * rate2Proc c₁ η c₂ ζ W u ω := hq'.lin hi R 1
  have hG : RegProc P fun u ω => R * bondProc R c₁ η c₂ ζ W u ω
      + 1 * rate2Proc c₁ η c₂ ζ W u ω := hq.lin hi R 1
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (𝓕.le t)
    (fun _ _ _ => (hq'.2.2.1 t ht).integrableOn) (fun _ _ _ => (hq.2.2.1 t ht).integrableOn)
    (fun A hA _ => ?_) (ha t ht) hqm
  obtain ⟨C1, hC10, hC1⟩ := hq'.exists_nonneg
  obtain ⟨C2, hC20, hC2⟩ := hq.exists_nonneg
  set f := fun u => ∫ ω in A, q' u ω ∂P - ∫ ω in A, bondProc R c₁ η c₂ ζ W u ω ∂P with hf
  have hmeas : Measurable f :=
    (measurable_setIntegral_proc hq'.1 hq'.2.1 A).sub (measurable_setIntegral_proc hq.1 hq.2.1 A)
  have hb : ∀ u, t ≤ u → |f u| ≤ (C1 + C2) * (1 + u) := fun u hu => by
    have a1 := abs_setIntegral_le hq' hC1 A (ht.trans hu)
    have a2 := abs_setIntegral_le hq hC2 A (ht.trans hu)
    calc |f u| ≤ |∫ ω in A, q' u ω ∂P| + |∫ ω in A, bondProc R c₁ η c₂ ζ W u ω ∂P| :=
          abs_sub _ _
      _ ≤ C1 * (1 + u) + C2 * (1 + u) := add_le_add a1 a2
      _ = (C1 + C2) * (1 + u) := by ring
  have h0 := unstable_zero hmeas ht (add_nonneg hC10 hC20) hR hb fun τ hτ => by
    have e1 := setIntegral_of_condExp hq' hG' ht hτ hA
      ((heq t τ ht hτ).trans (by simp only [one_mul]; rfl))
    have e2 := setIntegral_of_condExp hq hG ht hτ hA
      ((bond_book_equation (c₁ := c₁) (c₂ := c₂) hB hW h𝓕 hcont hW0 h1 h2 ht hτ).trans
        (by simp only [one_mul]; rfl))
    have i1 := intervalIntegrable_setIntegral hG' A ht hτ
    have i2 := intervalIntegrable_setIntegral hG A ht hτ
    simp only [hf]
    rw [show (∫ ω in A, q' τ ω ∂P - ∫ ω in A, bondProc R c₁ η c₂ ζ W τ ω ∂P)
        - (∫ ω in A, q' t ω ∂P - ∫ ω in A, bondProc R c₁ η c₂ ζ W t ω ∂P)
        = (∫ ω in A, q' τ ω ∂P - ∫ ω in A, q' t ω ∂P)
          - (∫ ω in A, bondProc R c₁ η c₂ ζ W τ ω ∂P - ∫ ω in A, bondProc R c₁ η c₂ ζ W t ω ∂P)
        by ring, e1, e2, ← intervalIntegral.integral_sub i1 i2,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hτ] at hu
    have hu0 : 0 ≤ u := ht.trans hu.1
    rw [setIntegral_lin hq' hi R 1 A hu0, setIntegral_lin hq hi R 1 A hu0]
    ring
  simp only [hf] at h0
  linarith

/-! ### Brackets: no covariation correction -/

/-- Cochrane (2023), (5.114), p. 170: the bracket of the bond price with `W`: for
`R + η ≠ 0`, `R + ζ ≠ 0`, `0 ≤ s < t`, a.s. along the dyadic partitions `Σ ΔqΔW → δ(t − s)`. -/
theorem bond_bracket (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {R c₁ η c₂ ζ : ℝ} (h1 : R + η ≠ 0)
    (h2 : R + ζ ≠ 0) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∀ᵐ ω ∂P, Tendsto (fun k => crossSum (dyadic hst k) (fun u => bondProc R c₁ η c₂ ζ W u ω)
      (fun u => bmReal W u ω)) atTop (𝓝 (bondLoading R c₁ η c₂ ζ * (t - s))) := by
  have hT := tendsto_crossSum_affine (P := P) hB hW hcont hs hst (bondLoading R c₁ η c₂ ζ) 1
    (F := fun ω u => bondProc R c₁ η c₂ ζ W u ω - bondLoading R c₁ η c₂ ζ * bmReal W u ω)
    (F' := fun ω u => R * bondProc R c₁ η c₂ ζ W u ω + rate2Proc c₁ η c₂ ζ W u ω)
    (G := fun _ _ => 0) (G' := fun _ _ => 0)
    (fun ω x => bond_sub_hasDerivAt h1 h2 (continuous_bmReal (hcont ω)) x)
    (fun ω => by
      have hw := continuous_bmReal (hcont ω)
      have := continuous_ouNoise η hw
      have := continuous_ouNoise ζ hw
      simp only [bondProc, rate2Proc, bondPath, rate2Path]
      fun_prop)
    (fun _ _ => hasDerivAt_const _ _) (fun _ => continuous_const)
  filter_upwards [hT] with ω hω
  simp only [mul_one, one_mul, add_zero] at hω
  refine hω.congr fun k => ?_
  congr 1
  funext u
  ring

/-- **Cochrane (2023), (5.105)–(5.106), p. 170 (no covariation correction with long-term
debt)**: for any price-level path `p` of class `C¹` (here `dp = π dt`), on every Brownian path
`Σ ΔqΔp → 0` along any partitions with mesh `→ 0`: the nominal bond price and the price level
have zero bracket, so `d(QB/P)` has no Itô cross term.
From `TidyR7StieltjesCalculus.tendsto_crossSum_zero_of_continuousOn` and
`TidyR7StochCTBrownian.bv_of_hasDerivAt`. -/
theorem bond_price_level_bracket (hcont : ∀ ω, Continuous fun t => W t ω) {R c₁ η c₂ ζ : ℝ}
    {p p' : ℝ → ℝ} (hp : ∀ x, HasDerivAt p (p' x) x) (hp' : Continuous p') (ω : Ω) {a b : ℝ}
    (ps : ℕ → Partition a b) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => crossSum (ps k) (fun u => bondProc R c₁ η c₂ ζ W u ω) p) atTop (𝓝 0) := by
  have hw := continuous_bmReal (hcont ω)
  have : Continuous fun u => bondProc R c₁ η c₂ ζ W u ω := by
    have := continuous_ouNoise η hw
    have := continuous_ouNoise ζ hw
    simp only [bondProc, bondPath]
    fun_prop
  exact tendsto_crossSum_zero_of_continuousOn this.continuousOn
    (bv_of_hasDerivAt hp hp' (a_le_b (ps 0))) ps hps

/-! ### The `v − v*` elimination under diffusion -/

/-- **Cochrane (2023), (5.106), (5.109)–(5.111), p. 172: the elimination of the starred
variables with diffusive shocks.** Let `v, v*, π, π*` be regular processes (continuous paths,
`E|·| ≤ C(1 + t)`: the stochastic transversality condition), `π, π*` adapted, `r > 0`, and
suppose
* the two debt equations share their bond-price innovation, so that on every path
  `(v* − v)_T − (v* − v)_t = ∫_t^T (r(v* − v) − (π* − π))`;
* (5.110): `E_t[(π* − π)_T − (π* − π)_t] = 0` for `0 ≤ t ≤ T`;
* `v*₀ = v₀` (survey E49) on every path.
Then for every `t ≥ 0`, a.s. `v*_t = v_t` and `π*_t = π_t`. In particular the inflation
innovation is the target's, `dδ_π = −β_s dε_s − β_i dε_i` (5.111).
Generalises `CTRules.ct_elim` to diffusion. -/
theorem elim_stoch [IsProbabilityMeasure P] {r : ℝ} (hr : 0 < r) {v vs infl infls : ℝ → Ω → ℝ}
    (hv : RegProc P v) (hvs : RegProc P vs) (hπ : RegProc P infl) (hπs : RegProc P infls)
    (hvm : ∀ t, 0 ≤ t → AEStronglyMeasurable[𝓕 t] (v t) P)
    (hvsm : ∀ t, 0 ≤ t → AEStronglyMeasurable[𝓕 t] (vs t) P)
    (hπm : ∀ t, 0 ≤ t → AEStronglyMeasurable[𝓕 t] (infl t) P)
    (hπsm : ∀ t, 0 ≤ t → AEStronglyMeasurable[𝓕 t] (infls t) P)
    (hdebt : ∀ ω t T, (vs T ω - v T ω) - (vs t ω - v t ω)
      = ∫ u in t..T, (r * (vs u ω - v u ω) - (infls u ω - infl u ω)))
    (htarget : ∀ t T, 0 ≤ t → t ≤ T →
      P[fun ω => (infls T ω - infl T ω) - (infls t ω - infl t ω) | 𝓕 t] =ᵐ[P] 0)
    (h0 : ∀ ω, vs 0 ω = v 0 ω) {t : ℝ} (ht : 0 ≤ t) :
    vs t =ᵐ[P] v t ∧ infls t =ᵐ[P] infl t := by
  set D : ℝ → Ω → ℝ := fun u ω => 1 * vs u ω + (-1) * v u ω with hD
  set M : ℝ → Ω → ℝ := fun u ω => 1 * infls u ω + (-1) * infl u ω with hM
  have hDr : RegProc P D := hvs.lin hv 1 (-1)
  have hMr : RegProc P M := hπs.lin hπ 1 (-1)
  have hFr : RegProc P fun u ω => r * D u ω + (-1) * M u ω := hDr.lin hMr r (-1)
  have hDm : ∀ u, 0 ≤ u → AEStronglyMeasurable[𝓕 u] (D u) P := fun u hu =>
    ((hvsm u hu).const_mul 1).add ((hvm u hu).const_mul (-1))
  have hMm : ∀ u, 0 ≤ u → AEStronglyMeasurable[𝓕 u] (M u) P := fun u hu =>
    ((hπsm u hu).const_mul 1).add ((hπm u hu).const_mul (-1))
  have hpath : ∀ ω t T, D T ω - D t ω = ∫ u in t..T, (r * D u ω + (-1) * M u ω) := by
    intro ω t T
    simp only [hD, hM]
    rw [show 1 * vs T ω + -1 * v T ω - (1 * vs t ω + -1 * v t ω)
      = (vs T ω - v T ω) - (vs t ω - v t ω) by ring, hdebt ω t T]
    refine intervalIntegral.integral_congr fun u _ => ?_
    ring
  -- step 1: `D_s = M_s / r` a.s. at every date
  have step1 : ∀ s, 0 ≤ s → D s =ᵐ[P] fun ω => r⁻¹ * M s ω := by
    intro s hs
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (𝓕.le s)
      (fun _ _ _ => (hDr.2.2.1 s hs).integrableOn)
      (fun _ _ _ => ((hMr.2.2.1 s hs).const_mul _).integrableOn) (fun A hA _ => ?_) (hDm s hs)
      ((hMm s hs).const_mul _)
    have hMconst : ∀ u, s ≤ u → ∫ ω in A, M u ω ∂P = ∫ ω in A, M s ω ∂P := by
      intro u hu
      have hi : Integrable (fun ω => M u ω - M s ω) P :=
        (hMr.2.2.1 u (hs.trans hu)).sub (hMr.2.2.1 s hs)
      have e := setIntegral_condExp (𝓕.le s) hi hA
      have ef : (fun ω => M u ω - M s ω)
          = fun ω => (infls u ω - infl u ω) - (infls s ω - infl s ω) := by
        funext ω
        simp only [hM]
        ring
      have hz : P[fun ω => M u ω - M s ω | 𝓕 s] =ᵐ[P] 0 := by
        rw [ef]
        exact htarget s u hs hu
      rw [setIntegral_congr_ae (𝓕.le s A hA) (hz.mono fun ω hω _ => hω)] at e
      simp only [Pi.zero_apply, integral_zero] at e
      rw [integral_sub (hMr.2.2.1 u (hs.trans hu)).integrableOn
        (hMr.2.2.1 s hs).integrableOn] at e
      linarith
    obtain ⟨C1, hC10, hC1⟩ := hDr.exists_nonneg
    set c := ∫ ω in A, M s ω ∂P
    set f := fun u => ∫ ω in A, D u ω ∂P - r⁻¹ * c with hf
    have hmeas : Measurable f := (measurable_setIntegral_proc hDr.1 hDr.2.1 A).sub_const _
    have hb : ∀ u, s ≤ u → |f u| ≤ (C1 + |r⁻¹ * c|) * (1 + u) := fun u hu => by
      have a1 := abs_setIntegral_le hDr hC1 A (hs.trans hu)
      have : |r⁻¹ * c| ≤ |r⁻¹ * c| * (1 + u) := le_mul_of_one_le_right (abs_nonneg _)
        (by linarith [hs.trans hu])
      calc |f u| ≤ |∫ ω in A, D u ω ∂P| + |r⁻¹ * c| := abs_sub _ _
        _ ≤ C1 * (1 + u) + |r⁻¹ * c| * (1 + u) := add_le_add a1 this
        _ = (C1 + |r⁻¹ * c|) * (1 + u) := by ring
    have hz := unstable_zero hmeas hs (add_nonneg hC10 (abs_nonneg _)) hr hb fun τ hτ => by
      have e1 := setIntegral_of_path (A := A) hDr hFr hs hτ (hpath · s τ)
      have i1 := intervalIntegrable_setIntegral hFr A hs hτ
      simp only [hf]
      rw [show ∫ ω in A, D τ ω ∂P - r⁻¹ * c - (∫ ω in A, D s ω ∂P - r⁻¹ * c)
        = ∫ ω in A, D τ ω ∂P - ∫ ω in A, D s ω ∂P by ring, e1,
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le hτ] at hu
      have hu0 : 0 ≤ u := hs.trans hu.1
      rw [setIntegral_lin hDr hMr r (-1) A hu0, hMconst u hu.1]
      field_simp
      ring
    simp only [hf] at hz
    rw [integral_const_mul]
    linarith
  -- step 2: `D_t = 0` a.s.
  have hF0 : ∀ u, 0 ≤ u → ∀ A : Set Ω, ∫ ω in A, (r * D u ω + (-1) * M u ω) ∂P = 0 := by
    intro u hu A
    have hz : (fun ω => r * D u ω + (-1) * M u ω) =ᵐ[P] 0 := by
      filter_upwards [step1 u hu] with ω hω
      rw [hω]
      simp only [Pi.zero_apply]
      field_simp
      ring
    rw [integral_congr_ae (ae_restrict_of_ae hz)]
    simp
  have hDt : D t =ᵐ[P] 0 := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (𝓕.le t)
      (fun _ _ _ => (hDr.2.2.1 t ht).integrableOn) (fun _ _ _ => integrableOn_zero)
      (fun A _ _ => ?_) (hDm t ht) aestronglyMeasurable_const
    have e1 := setIntegral_of_path (A := A) hDr hFr le_rfl ht (hpath · 0 t)
    have hD0 : ∫ ω in A, D 0 ω ∂P = 0 := by
      have : D 0 = 0 := by
        funext ω
        simp only [hD, h0 ω, Pi.zero_apply]
        ring
      rw [this]
      simp
    rw [hD0, sub_zero, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))
      (fun u hu => by
        rw [Set.uIcc_of_le ht] at hu
        exact hF0 u hu.1 A)] at e1
    simp only [intervalIntegral.integral_zero] at e1
    rw [e1]
    simp
  have hMt : M t =ᵐ[P] 0 := by
    filter_upwards [step1 t ht, hDt] with ω h1 h2
    rw [h2] at h1
    simp only [Pi.zero_apply] at h1 ⊢
    have := hr.ne'
    have h3 : r⁻¹ * M t ω = 0 := h1.symm
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h (inv_ne_zero this)
    · exact h
  refine ⟨?_, ?_⟩
  · filter_upwards [hDt] with ω hω
    simp only [hD, Pi.zero_apply] at hω
    linarith
  · filter_upwards [hMt] with ω hω
    simp only [hM, Pi.zero_apply] at hω
    linarith

/-! ### Fiscal policy chooses only unexpected inflation -/

/-- **Cochrane (2023), §5.7.5, p. 177 ("the interest-rate path sets the family of solutions.
Fiscal policy chooses only unexpected inflation at time zero"), with diffusive shocks.** Let
`I` be any regular interest-rate process and `(x, π)`, `(x', π')` regular adapted processes
(`κ, σ > 0`) that both satisfy the `E_t[·]` IS curve `E_t[x_T − x_t] = E_t∫_t^T σ(I − π)` and the
Phillips curve on every path with the SAME expectational error process `δ` (the same
unexpected inflation), `π_T − π_t = ∫_t^T(ρπ − κx) + (δ_T − δ_t)`, and start from the same
`π₀`. Then for every `t ≥ 0`, a.s. `π_t = π'_t` and `x_t = x'_t` — whatever the fiscal rules
(`θ_s`, `α`, `u_s(t)`) that generated them.
Generalises `CTRules.ct_rules_pinned`. -/
theorem pinned_by_innovation [IsProbabilityMeasure P] {σ κ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    {I x infl x' infl' δ : ℝ → Ω → ℝ} (hI : RegProc P I) (hx : RegProc P x)
    (hπ : RegProc P infl) (hx' : RegProc P x') (hπ' : RegProc P infl')
    (hxm : ∀ t, 0 ≤ t → AEStronglyMeasurable[𝓕 t] (x t) P)
    (hπm : ∀ t, 0 ≤ t → AEStronglyMeasurable[𝓕 t] (infl t) P)
    (hxm' : ∀ t, 0 ≤ t → AEStronglyMeasurable[𝓕 t] (x' t) P)
    (hπm' : ∀ t, 0 ≤ t → AEStronglyMeasurable[𝓕 t] (infl' t) P)
    (hIS : ∀ t T, 0 ≤ t → t ≤ T → P[fun ω => x T ω - x t ω | 𝓕 t]
      =ᵐ[P] P[fun ω => ∫ u in t..T, σ * (I u ω - infl u ω) | 𝓕 t])
    (hIS' : ∀ t T, 0 ≤ t → t ≤ T → P[fun ω => x' T ω - x' t ω | 𝓕 t]
      =ᵐ[P] P[fun ω => ∫ u in t..T, σ * (I u ω - infl' u ω) | 𝓕 t])
    (hPC : ∀ ω t T, infl T ω - infl t ω
      = (∫ u in t..T, (ρ * infl u ω - κ * x u ω)) + (δ T ω - δ t ω))
    (hPC' : ∀ ω t T, infl' T ω - infl' t ω
      = (∫ u in t..T, (ρ * infl' u ω - κ * x' u ω)) + (δ T ω - δ t ω))
    (h0 : ∀ ω, infl 0 ω = infl' 0 ω) {t : ℝ} (ht : 0 ≤ t) :
    infl t =ᵐ[P] infl' t ∧ x t =ᵐ[P] x' t := by
  have h1 := lam1_pos (ρ := ρ) hκ hσ
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hroot := lam1_root (ρ := ρ) hκ hσ
  have hsub := lam_sub ρ κ σ
  set EX : ℝ → Ω → ℝ := fun u ω => 1 * x u ω + (-1) * x' u ω with hEX
  set EP : ℝ → Ω → ℝ := fun u ω => 1 * infl u ω + (-1) * infl' u ω with hEP
  have hEXr : RegProc P EX := hx.lin hx' 1 (-1)
  have hEPr : RegProc P EP := hπ.lin hπ' 1 (-1)
  have hGP : RegProc P fun u ω => ρ * EP u ω + (-κ) * EX u ω := hEPr.lin hEXr ρ (-κ)
  have hG1 : RegProc P fun u ω => σ * I u ω + (-σ) * infl u ω := hI.lin hπ σ (-σ)
  have hG2 : RegProc P fun u ω => σ * I u ω + (-σ) * infl' u ω := hI.lin hπ' σ (-σ)
  have hEXm : ∀ u, 0 ≤ u → AEStronglyMeasurable[𝓕 u] (EX u) P := fun u hu =>
    ((hxm u hu).const_mul 1).add ((hxm' u hu).const_mul (-1))
  have hEPm : ∀ u, 0 ≤ u → AEStronglyMeasurable[𝓕 u] (EP u) P := fun u hu =>
    ((hπm u hu).const_mul 1).add ((hπm' u hu).const_mul (-1))
  have hpath : ∀ ω a b, EP b ω - EP a ω = ∫ u in a..b, (ρ * EP u ω + (-κ) * EX u ω) := by
    intro ω a b
    have c1 : Continuous fun u => ρ * infl u ω - κ * x u ω :=
      ((hπ.1 ω).const_mul ρ).sub ((hx.1 ω).const_mul κ)
    have c2 : Continuous fun u => ρ * infl' u ω - κ * x' u ω :=
      ((hπ'.1 ω).const_mul ρ).sub ((hx'.1 ω).const_mul κ)
    have e := intervalIntegral.integral_sub (c1.intervalIntegrable (μ := volume) a b)
      (c2.intervalIntegrable a b)
    have p1 := hPC ω a b
    have p2 := hPC' ω a b
    have hint : (∫ u in a..b, (ρ * EP u ω + (-κ) * EX u ω))
        = (∫ u in a..b, (ρ * infl u ω - κ * x u ω))
          - ∫ u in a..b, (ρ * infl' u ω - κ * x' u ω) := by
      rw [← e]
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [hEP, hEX]
      ring
    rw [hint]
    have hEPv : ∀ s, EP s ω = infl s ω - infl' s ω := fun s => by simp only [hEP]; ring
    rw [hEPv, hEPv]
    linarith
  -- the unstable combination `λ₁(π − π') − κ(x − x')` vanishes
  have hunst : ∀ s, 0 ≤ s → EX s =ᵐ[P] fun ω => lam1 ρ κ σ / κ * EP s ω := by
    intro s hs
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (𝓕.le s)
      (fun _ _ _ => (hEXr.2.2.1 s hs).integrableOn)
      (fun _ _ _ => ((hEPr.2.2.1 s hs).const_mul _).integrableOn) (fun A hA _ => ?_) (hEXm s hs)
      ((hEPm s hs).const_mul _)
    obtain ⟨C1, hC10, hC1⟩ := hEPr.exists_nonneg
    obtain ⟨C2, hC20, hC2⟩ := hEXr.exists_nonneg
    set f := fun u => lam1 ρ κ σ * ∫ ω in A, EP u ω ∂P - κ * ∫ ω in A, EX u ω ∂P with hf
    have hmeas : Measurable f :=
      ((measurable_setIntegral_proc hEPr.1 hEPr.2.1 A).const_mul _).sub
        ((measurable_setIntegral_proc hEXr.1 hEXr.2.1 A).const_mul _)
    have hb : ∀ u, s ≤ u → |f u| ≤ (|lam1 ρ κ σ| * C1 + |κ| * C2) * (1 + u) := fun u hu => by
      have a1 := abs_setIntegral_le hEPr hC1 A (hs.trans hu)
      have a2 := abs_setIntegral_le hEXr hC2 A (hs.trans hu)
      calc |f u| ≤ |lam1 ρ κ σ| * |∫ ω in A, EP u ω ∂P| + |κ| * |∫ ω in A, EX u ω ∂P| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_mul]
        _ ≤ |lam1 ρ κ σ| * (C1 * (1 + u)) + |κ| * (C2 * (1 + u)) :=
            add_le_add (mul_le_mul_of_nonneg_left a1 (abs_nonneg _))
              (mul_le_mul_of_nonneg_left a2 (abs_nonneg _))
        _ = (|lam1 ρ κ σ| * C1 + |κ| * C2) * (1 + u) := by ring
    have hz := unstable_zero hmeas hs (add_nonneg (mul_nonneg (abs_nonneg _) hC10)
      (mul_nonneg (abs_nonneg _) hC20)) h1 hb fun τ hτ => by
      have eP := setIntegral_of_path (A := A) hEPr hGP hs hτ (hpath · s τ)
      have ex1 := setIntegral_of_condExp hx hG1 hs hτ hA ((hIS s τ hs hτ).trans
        (condExp_congr_ae (Eventually.of_forall fun ω => by
          simp only
          refine intervalIntegral.integral_congr fun u _ => ?_
          ring)))
      have ex2 := setIntegral_of_condExp hx' hG2 hs hτ hA ((hIS' s τ hs hτ).trans
        (condExp_congr_ae (Eventually.of_forall fun ω => by
          simp only
          refine intervalIntegral.integral_congr fun u _ => ?_
          ring)))
      have iP := intervalIntegrable_setIntegral hGP A hs hτ
      have i1 := intervalIntegrable_setIntegral hG1 A hs hτ
      have i2 := intervalIntegrable_setIntegral hG2 A hs hτ
      have eX : ∫ ω in A, EX τ ω ∂P - ∫ ω in A, EX s ω ∂P
          = ∫ u in s..τ, ((∫ ω in A, (σ * I u ω + (-σ) * infl u ω) ∂P)
            - ∫ ω in A, (σ * I u ω + (-σ) * infl' u ω) ∂P) := by
        rw [intervalIntegral.integral_sub i1 i2, ← ex1, ← ex2,
          setIntegral_lin hx hx' 1 (-1) A (hs.trans hτ), setIntegral_lin hx hx' 1 (-1) A hs]
        ring
      simp only [hf]
      rw [show lam1 ρ κ σ * ∫ ω in A, EP τ ω ∂P - κ * ∫ ω in A, EX τ ω ∂P
          - (lam1 ρ κ σ * ∫ ω in A, EP s ω ∂P - κ * ∫ ω in A, EX s ω ∂P)
          = lam1 ρ κ σ * (∫ ω in A, EP τ ω ∂P - ∫ ω in A, EP s ω ∂P)
            - κ * (∫ ω in A, EX τ ω ∂P - ∫ ω in A, EX s ω ∂P) by ring, eP, eX,
        ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (iP.const_mul _) ((i1.sub i2).const_mul _),
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le hτ] at hu
      have hu0 : 0 ≤ u := hs.trans hu.1
      rw [setIntegral_lin hEPr hEXr ρ (-κ) A hu0, setIntegral_lin hI hπ σ (-σ) A hu0,
        setIntegral_lin hI hπ' σ (-σ) A hu0]
      have eEP : ∫ ω in A, EP u ω ∂P = ∫ ω in A, infl u ω ∂P - ∫ ω in A, infl' u ω ∂P := by
        rw [setIntegral_lin hπ hπ' 1 (-1) A hu0]
        ring
      rw [eEP]
      linear_combination (-(∫ ω in A, infl u ω ∂P - ∫ ω in A, infl' u ω ∂P)) * hroot
    simp only [hf] at hz
    rw [integral_const_mul]
    have hk := hκ.ne'
    field_simp
    linarith
  -- the stable root: `π − π'` starts at `0` and decays
  have hEP0 : ∀ τ, 0 ≤ τ → ∀ A : Set Ω, ∫ ω in A, EP τ ω ∂P = 0 := by
    intro τ hτ A
    obtain ⟨C1, hC10, hC1⟩ := hEPr.exists_nonneg
    have hmeas := measurable_setIntegral_proc (P := P) hEPr.1 hEPr.2.1 A
    refine stable_zero (c := -lam2 ρ κ σ) hmeas hC10 (fun u hu => abs_setIntegral_le hEPr hC1 A hu)
      (fun τ' hτ' => ?_) hτ
    have eP := setIntegral_of_path (A := A) hEPr hGP le_rfl hτ' (hpath · 0 τ')
    have hz0 : ∫ ω in A, EP 0 ω ∂P = 0 := by
      have : EP 0 = 0 := by
        funext ω
        simp only [hEP, h0 ω, Pi.zero_apply]
        ring
      rw [this]
      simp
    rw [hz0, sub_zero] at eP
    rw [eP, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hτ'] at hu
    rw [setIntegral_lin hEPr hEXr ρ (-κ) A hu.1,
      integral_congr_ae (ae_restrict_of_ae (hunst u hu.1)), integral_const_mul]
    have hk := hκ.ne'
    have e : -κ * (lam1 ρ κ σ / κ * ∫ ω in A, EP u ω ∂P)
        = -lam1 ρ κ σ * ∫ ω in A, EP u ω ∂P := by field_simp
    rw [e]
    linear_combination (-(∫ ω in A, EP u ω ∂P)) * hsub
  have hEPt : EP t =ᵐ[P] 0 :=
    ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (𝓕.le t)
      (fun _ _ _ => (hEPr.2.2.1 t ht).integrableOn) (fun _ _ _ => integrableOn_zero)
      (fun A _ _ => by rw [hEP0 t ht A]; simp) (hEPm t ht) aestronglyMeasurable_const
  refine ⟨?_, ?_⟩
  · filter_upwards [hEPt] with ω hω
    simp only [hEP, Pi.zero_apply] at hω
    linarith
  · filter_upwards [hEPt, hunst t ht] with ω hω hx0
    simp only [hEP, Pi.zero_apply] at hω
    simp only [hEX] at hx0
    rw [show EP t ω = 0 from hω, mul_zero] at hx0
    linarith

/-! ### Non-vacuity -/

/-- **Cochrane (2023), (5.105), p. 169, and Figs. 5.11–5.13 (non-vacuity on the constructed
motion `bmPath`)**: with the rate of Figs. 5.11–5.13 (`θ_{iε} = 1/4`, `ζ_i = 1`, `η_i = 0.3`)
and `r + ω > 0`, the bond price is the expected discounted rate path in `L¹`, and every regular
adapted solution of the bond-price equation is the explicit one. -/
theorem bmPath_bond {R σi : ℝ} (hR : 0 < R) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => ∫ ω, |-gaussSeq[fun ω => ∫ τ in t..T, exp (-(R * (τ - t)))
      * rate2Proc (σi * (1 / (1 - 3 / 10))) (3 / 10) (σi * (1 / 4 - 1 / (1 - 3 / 10))) 1
        bmPath τ ω | bmFiltrationReal bmPath measurable_bmPath t] ω
      - bondProc R (σi * (1 / (1 - 3 / 10))) (3 / 10) (σi * (1 / 4 - 1 / (1 - 3 / 10))) 1
        bmPath t ω| ∂gaussSeq) atTop (𝓝 0) ∧
    rateProc σi (1 / 4) 1 (3 / 10) bmPath
      = rate2Proc (σi * (1 / (1 - 3 / 10))) (3 / 10) (σi * (1 / 4 - 1 / (1 - 3 / 10))) 1
        bmPath := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  refine ⟨bond_valuation_L1 hB measurable_bmPath h𝓕 continuous_bmPath bmPath_zero hR
    (by norm_num) zero_le_one ht, ?_⟩
  rw [rateProc_eq_ker2 (by norm_num), rate2Proc_eq_ker2]

/-- **Cochrane (2023), §5.7.5, p. 177 (non-vacuity of `pinned_by_innovation` on `bmPath`)**:
for `r, κ, σ > 0`, the equilibrium of §5.7.1 with Brownian shocks (`TidyR7StochCTUnique`)
satisfies its hypotheses on the constructed motion: `i`, `x`, `π` are regular and adapted, the
`E_t[·]` IS curve holds, and the Phillips curve holds on every path with the innovation process
`δ = R_π(0)W`. -/
theorem bmPath_pinned_hypotheses {r σ κ ρ σi σs : ℝ} (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ) :
    RegProc gaussSeq (iProc σi bmPath) ∧ RegProc gaussSeq (xProc r σ κ ρ σi σs bmPath) ∧
      RegProc gaussSeq (piProc r σ κ ρ σi σs bmPath) ∧
      (∀ t, 0 ≤ t → AEStronglyMeasurable[bmFiltrationReal bmPath measurable_bmPath t]
        (piProc r σ κ ρ σi σs bmPath t) gaussSeq) ∧
      (∀ t T, 0 ≤ t → t ≤ T → gaussSeq[fun ω => xProc r σ κ ρ σi σs bmPath T ω
          - xProc r σ κ ρ σi σs bmPath t ω | bmFiltrationReal bmPath measurable_bmPath t]
        =ᵐ[gaussSeq] gaussSeq[fun ω => ∫ u in t..T, σ * (iProc σi bmPath u ω
          - piProc r σ κ ρ σi σs bmPath u ω) | bmFiltrationReal bmPath measurable_bmPath t]) ∧
      ∀ ω t T, piProc r σ κ ρ σi σs bmPath T ω - piProc r σ κ ρ σi σs bmPath t ω
        = (∫ u in t..T, (ρ * piProc r σ κ ρ σi σs bmPath u ω - κ * xProc r σ κ ρ σi σs bmPath u ω))
          + (respPi r σ κ ρ σi σs 0 * bmReal bmPath T ω
            - respPi r σ κ ρ σi σs 0 * bmReal bmPath t ω) := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hE := stochCTEq_exists (ρ := ρ) (σi := σi) (σs := σs) hB measurable_bmPath h𝓕
    continuous_bmPath bmPath_zero hr hκ hσ
  refine ⟨regProc_iProc hB measurable_bmPath h𝓕 continuous_bmPath bmPath_zero σi, hE.regX,
    hE.regPi, hE.adaptPi, hE.isCurve, fun ω t T => ?_⟩
  have := (expectational_errors (r := r) (ρ := ρ) (σi := σi) (σs := σs) hκ hσ continuous_bmPath
    t T ω).2
  simp only [incr] at this
  linarith

end Cochrane.StickyPriceFiscal.TidyR8StochCTRules
