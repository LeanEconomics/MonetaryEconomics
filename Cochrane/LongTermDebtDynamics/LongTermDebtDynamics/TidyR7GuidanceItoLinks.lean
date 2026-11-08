/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR7GuidanceItoBM

/-!
# Links: the deterministic formula (`σ = 0`) and the discrete formula of p. 560

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.2.1,
pp. 560–561.

* `bmSDF_zero_eq`, `sigma_zero_value`: with no diffusion (`κ = 0`) the model discount factor
  is the book's deterministic bond price `e^{−(r min(j,T) + i max(j−T,0))}` and the debt value
  is `ForwardGuidance.integral_cfg` path by path; the stochastic results of
  TidyR7GuidanceItoValuation then reduce to `ForwardGuidance.cfg_jump`.
* `fgJump_exp_factor`, `tendsto_fgJump_cfgJump`: **the discrete formula converges to the
  continuous one.** With periods of length `Δ = T/n`, one-period rates `e^{rΔ} − 1`,
  `e^{iΔ} − 1` and maturity decay `ω = e^{−ϖΔ}` (the book's `ω = e^{−ϖ}` per period), the
  discrete jump `ForwardGuidance.fgJump` of p. 560 — which
  `TidyR5GuidanceUncertainty.stoch_fg_jump` proves state by state under uncertainty — tends to
  the continuous jump `ForwardGuidance.cfgJump r i ϖ T` of p. 561 as `n → ∞`, which
  `TidyR7GuidanceItoValuation.guidance_jump_ito` proves state by state under Brownian
  uncertainty.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoLinks

open MeasureTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoBM Cochrane.LongTermDebtDynamics.ForwardGuidance

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561 (`σ = 0`): without diffusion the model economy
discount factor is the book's deterministic bond price,
`Λ_t = e^{−(r min(t,T) + i max(t−T,0))}` (`T ≥ 0`). -/
theorem bmSDF_zero_eq (r i : ℝ) {T : ℝ} (t : ℝ) (ω : ℕ → ℝ) :
    bmSDF 0 r T (fun _ => i) t ω = Real.exp (-(r * min t T + i * max (t - T) 0)) := by
  rcases le_or_gt t T with h | h
  · simp only [bmSDF, h, ↓reduceIte, zero_mul, add_zero, mul_one, min_eq_left h,
      max_eq_right (sub_nonpos.2 h), mul_zero]
    ring_nf
  · simp only [bmSDF, not_le.2 h, ↓reduceIte, zero_mul, add_zero, mul_one, min_eq_right h.le,
      max_eq_left (sub_nonneg.2 h.le), ← Real.exp_add]
    ring_nf

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (`σ = 0`): the deterministic limit.**
With `κ = 0`, for every path, `∫_0^∞ ϖe^{−ϖj}Λ_j dj = cfgValue r i ϖ T` (it is
`ForwardGuidance.integral_cfg`; `r + ϖ > 0`, `i + ϖ > 0`, `T ≥ 0`). -/
theorem sigma_zero_value {r i ϖ T : ℝ} (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ) (hT : 0 ≤ T)
    (ω : ℕ → ℝ) :
    ∫ j in Set.Ioi (0 : ℝ), ϖ * Real.exp (-ϖ * j) * bmSDF 0 r T (fun _ => i) j ω
      = cfgValue r i ϖ T := by
  simp_rw [bmSDF_zero_eq]
  exact integral_cfg hrv hiv hT

/-- Cochrane (2023), Online Appendix §A1.2.1, pp. 560–561: with periods of length `T/n`, the
discount factor of the discrete formula over the `n` periods to `T` is exactly the continuous
one, `(e^{−ϖT/n}/e^{rT/n})^n = e^{−(r+ϖ)T}`. -/
theorem fgJump_exp_factor (r ϖ T : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (Real.exp (-ϖ * (T / n)) / (1 + (Real.exp (r * (T / n)) - 1))) ^ n
      = Real.exp (-(r + ϖ) * T) := by
  rw [add_sub_cancel, ← Real.exp_sub, ← Real.exp_nat_mul]
  congr 1
  field_simp
  ring

/-- **Cochrane (2023), Online Appendix §A1.2.1, pp. 560–561: the discrete forward-guidance
formula converges to the continuous one.** For `T > 0`, `i + ϖ ≠ 0`, with `n` periods of
length `T/n`, one-period rates `e^{rT/n} − 1` and `e^{iT/n} − 1` and decay `e^{−ϖT/n}`,
`fgJump → cfgJump r i ϖ T`. -/
theorem tendsto_fgJump_cfgJump {r i ϖ T : ℝ} (hT : 0 < T) (hiv : i + ϖ ≠ 0) :
    Tendsto (fun n : ℕ => fgJump (Real.exp (r * (T / n)) - 1) (Real.exp (i * (T / n)) - 1)
      (Real.exp (-ϖ * (T / n))) n) atTop (𝓝 (cfgJump r i ϖ T)) := by
  set f : ℝ → ℝ := fun x => Real.exp (r * x) - Real.exp (-ϖ * x) with hf
  set g : ℝ → ℝ := fun x => Real.exp (i * x) - Real.exp (-ϖ * x) with hg
  have hfd : HasDerivAt f (r + ϖ) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul r).exp).sub
      (((hasDerivAt_id (0 : ℝ)).const_mul (-ϖ)).exp)
    refine h.congr_deriv ?_
    simp
  have hgd : HasDerivAt g (i + ϖ) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul i).exp).sub
      (((hasDerivAt_id (0 : ℝ)).const_mul (-ϖ)).exp)
    refine h.congr_deriv ?_
    simp
  have hf0 : f 0 = 0 := by simp [hf]
  have hg0 : g 0 = 0 := by simp [hg]
  have hfs := hasDerivAt_iff_tendsto_slope.1 hfd
  have hgs := hasDerivAt_iff_tendsto_slope.1 hgd
  have hx : Tendsto (fun n : ℕ => T / n) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_div_atTop_nhds_zero_nat T, ?_⟩
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact div_ne_zero hT.ne' (Nat.cast_ne_zero.2 hn)
  have hE : Tendsto (fun x : ℝ => Real.exp (i * x) / Real.exp (r * x)) (𝓝[≠] 0) (𝓝 1) := by
    have h : Continuous fun x : ℝ => Real.exp (i * x) / Real.exp (r * x) :=
      (by fun_prop : Continuous fun x : ℝ => Real.exp (i * x)).div (by fun_prop)
        fun x => (Real.exp_pos _).ne'
    have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa using this
  have hbr : Tendsto (fun x : ℝ => Real.exp (i * x) / Real.exp (r * x)
      * (slope f 0 x / slope g 0 x)) (𝓝[≠] 0) (𝓝 (1 * ((r + ϖ) / (i + ϖ)))) :=
    hE.mul (hfs.div hgs hiv)
  have hlim := ((hbr.sub_const 1).const_mul (Real.exp (-(r + ϖ) * T))).comp hx
  rw [one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hx0 : T / n ≠ 0 := div_ne_zero hT.ne' (Nat.cast_ne_zero.2 hn)
  simp only [Function.comp_apply]
  rw [fgJump, fgJump_exp_factor r ϖ T hn]
  congr 1
  rw [slope_def_field, slope_def_field, hf0, hg0, sub_zero, sub_zero, sub_zero]
  have hgx : g (T / n) ≠ 0 := by
    intro h0
    have hgi : Real.exp (i * (T / n)) = Real.exp (-ϖ * (T / n)) := by
      have := h0; simp only [hg] at this; linarith
    have := Real.exp_injective hgi
    have : (i + ϖ) * (T / n) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact hiv h
    · exact hx0 h
  simp only [hf, hg] at hgx ⊢
  have hr1 : (1 : ℝ) + (Real.exp (r * (T / n)) - 1) = Real.exp (r * (T / n)) := by ring
  have hi1 : (1 : ℝ) + (Real.exp (i * (T / n)) - 1) = Real.exp (i * (T / n)) := by ring
  rw [hr1, hi1]
  have h1 := Real.exp_pos (r * (T / n))
  have h2 := Real.exp_pos (i * (T / n))
  field_simp

end Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoLinks
