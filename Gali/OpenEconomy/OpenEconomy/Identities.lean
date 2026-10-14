/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OpenEconomy.Preferences
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Domestic inflation, CPI inflation, the real exchange rate and the terms of trade

Galí (2015), Chapter 8, §8.1.1.1, pp. 229–230: eqs. (12), (13), (14) and `q = (1−υ)s`.

Lower-case letters are logs: `p_H = log P_H`, `p_F = log P_F`, `s = p_F − p_H` (terms of
trade), `p = log P` with `P` the CPI of `Preferences`.

## Main results

* `log_cpi_eq` (eq. (12), exact for every `η ≠ 1`): `p = p_H + h(s)` where
  `h(s) = log P(1, e^s)` (`cpiGap`) — a consequence of the CPI being homogeneous of degree
  one (`cpi_homog`).
* `cpiGap_zero`, `hasDerivAt_cpiGap`: `h(0) = 0`, `h'(0) = υ`; hence (12) to first order.
* `hasFDerivAt_logCPI` (eq. (12) as an exact derivative): the log CPI as a function of
  `(p_H, p_F)` has derivative `(1−υ) dp_H + υ dp_F` at every symmetric point `p_H = p_F`.
* `log_cpiCD_eq` (fn. 4): at `η = 1`, `p = (1−υ)p_H + υp_F = p_H + υs` exactly.
* `cpi_inflation` (eq. (13)): `π_t = π_{H,t} + h(s_t) − h(s_{t−1})` exactly, with
  `hasFDerivAt_inflationGap` (first order: `υΔs_t`) and `cpi_inflation_cd` (exact at `η = 1`).
* `tot_lop` (eq. (14)): the law of one price `P_F = ℰP*` gives `s = e + p* − p_H`.
* `rer_eq` (p. 230): `q = p_F − p = s + p_H − p = s − h(s)`; `hasDerivAt_rerGap`:
  first order `q = (1−υ)s`; `rer_cd`: exact at `η = 1`.
-/

namespace Gali.OpenEconomy.Identities

open Preferences

variable {υ η : ℝ}

/-- Galí (2015), (12), p. 229: the CPI is homogeneous of degree one,
`P(λP_H, λP_F) = λ P(P_H, P_F)`. -/
theorem cpi_homog (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) {l a b : ℝ} (hl : 0 < l)
    (ha : 0 < a) (hb : 0 < b) : cpi υ η (l * a) (l * b) = l * cpi υ η a b := by
  have h1υ : 0 < 1 - υ := by linarith
  have hne : 1 - η ≠ 0 := sub_ne_zero.2 (Ne.symm hη1)
  unfold cpi
  rw [Real.mul_rpow hl.le ha.le, Real.mul_rpow hl.le hb.le,
    show (1 - υ) * (l ^ (1 - η) * a ^ (1 - η)) + υ * (l ^ (1 - η) * b ^ (1 - η))
      = l ^ (1 - η) * ((1 - υ) * a ^ (1 - η) + υ * b ^ (1 - η)) by ring,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hl.le,
    mul_one_div_cancel hne, Real.rpow_one]

/-- Galí (2015), (12), p. 229: the log CPI in excess of the log domestic price as a function
of the log terms of trade, `h(s) = log P(1, e^s) = p − p_H`. -/
noncomputable def cpiGap (υ η s : ℝ) : ℝ := Real.log (cpi υ η 1 (Real.exp s))

/-- Galí (2015), eq. (12), p. 229, **exact form**: `p = p_H + h(s)` with `s = p_F − p_H`. -/
theorem log_cpi_eq (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (pH pF : ℝ) :
    Real.log (cpi υ η (Real.exp pH) (Real.exp pF)) = pH + cpiGap υ η (pF - pH) := by
  have hpos := cpi_pos (η := η) hυ0 hυ1 one_pos (Real.exp_pos (pF - pH))
  have e2 : Real.exp pF = Real.exp pH * Real.exp (pF - pH) := by
    rw [← Real.exp_add]; ring_nf
  have hh := cpi_homog hυ0 hυ1 hη1 (Real.exp_pos pH) one_pos (Real.exp_pos (pF - pH))
  rw [mul_one] at hh
  rw [cpiGap, e2, hh, Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp]

/-- Galí (2015), (12), p. 229: an explicit formula,
`h(s) = log((1−υ) + υ e^{(1−η)s}) / (1−η)`. -/
theorem cpiGap_eq (hυ0 : 0 < υ) (hυ1 : υ < 1) (s : ℝ) :
    cpiGap υ η s = Real.log ((1 - υ) + υ * Real.exp ((1 - η) * s)) / (1 - η) := by
  have h1υ : 0 < 1 - υ := by linarith
  have hS : 0 < (1 - υ) + υ * Real.exp ((1 - η) * s) := by positivity
  unfold cpiGap cpi
  rw [Real.one_rpow, mul_one, ← Real.exp_mul, mul_comm s, Real.log_rpow hS]
  ring

/-- Galí (2015), (12), p. 229: in the symmetric steady state (`S = 1`, `s = 0`) the CPI equals
the domestic price index: `h(0) = 0`. -/
theorem cpiGap_zero (hυ0 : 0 < υ) (hυ1 : υ < 1) : cpiGap υ η 0 = 0 := by
  rw [cpiGap_eq hυ0 hυ1, mul_zero, Real.exp_zero, mul_one, sub_add_cancel, Real.log_one,
    zero_div]

/-- Galí (2015), eq. (12), p. 229 (**first order**): `h'(0) = υ`, so that
`p = p_H + υ s` up to first order around the symmetric steady state `s = 0`. -/
theorem hasDerivAt_cpiGap (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) :
    HasDerivAt (cpiGap υ η) υ 0 := by
  have hne : 1 - η ≠ 0 := sub_ne_zero.2 (Ne.symm hη1)
  have hfun : cpiGap υ η = fun s => Real.log ((1 - υ) + υ * Real.exp ((1 - η) * s)) / (1 - η) :=
    funext (cpiGap_eq hυ0 hυ1)
  rw [hfun]
  have hin : HasDerivAt (fun s => (1 - υ) + υ * Real.exp ((1 - η) * s))
      (υ * (Real.exp ((1 - η) * 0) * ((1 - η) * 1))) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul (1 - η)).exp.const_mul υ).const_add (1 - υ)
  have hval : (1 - υ) + υ * Real.exp ((1 - η) * 0) = 1 := by simp
  have hlog := hin.log (by rw [hval]; exact one_ne_zero)
  rw [hval] at hlog
  convert hlog.div_const (1 - η) using 1
  field_simp
  simp

/-- Galí (2015), eq. (12), p. 229, as an **exact derivative**: the log CPI
`(p_H, p_F) ↦ log P(e^{p_H}, e^{p_F})` has Fréchet derivative `(1−υ) dp_H + υ dp_F` at every
symmetric point `p_H = p_F = p̄`. -/
theorem hasFDerivAt_logCPI (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (pbar : ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => Real.log (cpi υ η (Real.exp x.1) (Real.exp x.2)))
      ((1 - υ) • ContinuousLinearMap.fst ℝ ℝ ℝ + υ • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (pbar, pbar) := by
  have hfun : (fun x : ℝ × ℝ => Real.log (cpi υ η (Real.exp x.1) (Real.exp x.2)))
      = fun x => x.1 + cpiGap υ η (x.2 - x.1) :=
    funext fun x => log_cpi_eq hυ0 hυ1 hη1 x.1 x.2
  rw [hfun]
  have hd : HasDerivAt (cpiGap υ η) υ ((pbar, pbar).2 - (pbar, pbar).1) := by
    simp only [sub_self]
    exact hasDerivAt_cpiGap hυ0 hυ1 hη1
  have hlin : HasFDerivAt (fun x : ℝ × ℝ => x.2 - x.1)
      (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) (pbar, pbar) :=
    hasFDerivAt_snd.sub hasFDerivAt_fst
  have hcomp := hd.comp_hasFDerivAt (pbar, pbar) hlin
  have hsum := hasFDerivAt_fst.add hcomp
  have hL : (1 - υ) • ContinuousLinearMap.fst ℝ ℝ ℝ + υ • ContinuousLinearMap.snd ℝ ℝ ℝ
      = ContinuousLinearMap.fst ℝ ℝ ℝ
        + υ • (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [_root_.add_apply, _root_.smul_apply,
      _root_.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul]
    ring
  rw [hL]
  exact hsum

/-- Galí (2015), eq. (12) and fn. 4, p. 229: **at `η = 1` the relation is exact**,
`p = (1−υ)p_H + υ p_F = p_H + υ s`. -/
theorem log_cpiCD_eq (pH pF : ℝ) :
    Real.log (cpiCD υ (Real.exp pH) (Real.exp pF)) = (1 - υ) * pH + υ * pF ∧
      (1 - υ) * pH + υ * pF = pH + υ * (pF - pH) := by
  refine ⟨?_, by ring⟩
  unfold cpiCD
  rw [Real.log_mul (Real.rpow_pos_of_pos (Real.exp_pos _) _).ne'
    (Real.rpow_pos_of_pos (Real.exp_pos _) _).ne', Real.log_rpow (Real.exp_pos _),
    Real.log_rpow (Real.exp_pos _), Real.log_exp, Real.log_exp]

/-- Galí (2015), eq. (13), p. 229, **exact form**: with `p_t = log P_t` the CPI of the
domestic and import price paths, CPI inflation is
`π_{t+1} = π_{H,t+1} + h(s_{t+1}) − h(s_t)`. -/
theorem cpi_inflation (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (pH pF : ℕ → ℝ) (t : ℕ) :
    Real.log (cpi υ η (Real.exp (pH (t + 1))) (Real.exp (pF (t + 1))))
        - Real.log (cpi υ η (Real.exp (pH t)) (Real.exp (pF t)))
      = (pH (t + 1) - pH t)
        + (cpiGap υ η (pF (t + 1) - pH (t + 1)) - cpiGap υ η (pF t - pH t)) := by
  rw [log_cpi_eq hυ0 hυ1 hη1, log_cpi_eq hυ0 hυ1 hη1]
  ring

/-- Galí (2015), eq. (13), p. 229 (**first order**): the inflation gap
`(s_t, s_{t+1}) ↦ h(s_{t+1}) − h(s_t)` has derivative `υ (ds_{t+1} − ds_t)` at the steady
state, i.e. `π = π_H + υ Δs` to first order. -/
theorem hasFDerivAt_inflationGap (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) :
    HasFDerivAt (fun x : ℝ × ℝ => cpiGap υ η x.2 - cpiGap υ η x.1)
      (υ • (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ)) (0, 0) := by
  have hd := hasDerivAt_cpiGap hυ0 hυ1 hη1
  have hs : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) :=
    hasFDerivAt_snd
  have hf : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 0) :=
    hasFDerivAt_fst
  have h2 := hd.comp_hasFDerivAt ((0 : ℝ), (0 : ℝ)) hs
  have h1 := hd.comp_hasFDerivAt ((0 : ℝ), (0 : ℝ)) hf
  rw [smul_sub]
  exact h2.sub h1

/-- Galí (2015), eq. (13) and fn. 4, p. 229: **at `η = 1`**, exactly
`π_{t+1} = π_{H,t+1} + υ Δs_{t+1}`. -/
theorem cpi_inflation_cd (pH pF : ℕ → ℝ) (t : ℕ) :
    Real.log (cpiCD υ (Real.exp (pH (t + 1))) (Real.exp (pF (t + 1))))
        - Real.log (cpiCD υ (Real.exp (pH t)) (Real.exp (pF t)))
      = (pH (t + 1) - pH t) + υ * ((pF (t + 1) - pH (t + 1)) - (pF t - pH t)) := by
  rw [(log_cpiCD_eq _ _).1, (log_cpiCD_eq _ _).1]
  ring

/-- Galí (2015), eq. (14), p. 230: the law of one price `P_F = ℰ P*` gives
`s = log(P_F/P_H) = e + p* − p_H`. -/
theorem tot_lop {PH PF Ex Ps : ℝ} (hPH : 0 < PH) (hEx : 0 < Ex) (hPs : 0 < Ps)
    (hlop : PF = Ex * Ps) :
    Real.log (PF / PH) = Real.log Ex + Real.log Ps - Real.log PH := by
  rw [hlop, Real.log_div (by positivity) hPH.ne', Real.log_mul hEx.ne' hPs.ne']

/-- Galí (2015), p. 230: the log real exchange rate as a function of the terms of trade,
`g(s) = s − h(s)`. -/
noncomputable def rerGap (υ η s : ℝ) : ℝ := s - cpiGap υ η s

/-- Galí (2015), p. 230, **exact form**: with `𝒬 = P_F/P` (`= ℰP*/P` under the law of one
price), `q = p_F − p = s + p_H − p = s − h(s)`. -/
theorem rer_eq (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (pH pF : ℝ) :
    Real.log (Real.exp pF / cpi υ η (Real.exp pH) (Real.exp pF))
        = (pF - pH) + pH - Real.log (cpi υ η (Real.exp pH) (Real.exp pF)) ∧
      Real.log (Real.exp pF / cpi υ η (Real.exp pH) (Real.exp pF))
        = rerGap υ η (pF - pH) := by
  have hpos := cpi_pos (η := η) hυ0 hυ1 (Real.exp_pos pH) (Real.exp_pos pF)
  have h1 : Real.log (Real.exp pF / cpi υ η (Real.exp pH) (Real.exp pF))
      = pF - Real.log (cpi υ η (Real.exp pH) (Real.exp pF)) := by
    rw [Real.log_div (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
  refine ⟨by rw [h1]; ring, ?_⟩
  rw [h1, log_cpi_eq hυ0 hυ1 hη1, rerGap]
  ring

/-- Galí (2015), p. 230 (**first order**): `g(0) = 0` and `g'(0) = 1 − υ`, i.e.
`q = (1−υ)s` up to first order. -/
theorem hasDerivAt_rerGap (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) :
    rerGap υ η 0 = 0 ∧ HasDerivAt (rerGap υ η) (1 - υ) 0 := by
  refine ⟨by rw [rerGap, cpiGap_zero hυ0 hυ1, sub_zero], ?_⟩
  exact (hasDerivAt_id' (0 : ℝ)).sub (hasDerivAt_cpiGap hυ0 hυ1 hη1)

/-- Galí (2015), p. 230: **at `η = 1` exactly** `q = s + p_H − p = (1−υ)s`. -/
theorem rer_cd (pH pF : ℝ) :
    Real.log (Real.exp pF / cpiCD υ (Real.exp pH) (Real.exp pF)) = (1 - υ) * (pF - pH) := by
  have hpos : 0 < cpiCD υ (Real.exp pH) (Real.exp pF) := by
    unfold cpiCD; positivity
  rw [Real.log_div (Real.exp_pos _).ne' hpos.ne', Real.log_exp, (log_cpiCD_eq _ _).1]
  ring

end Gali.OpenEconomy.Identities
