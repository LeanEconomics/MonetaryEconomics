/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5GovPurchases
import StabilizationWelfare.NonlinearNKMarkovRamseyLin

/-!
# The exact Ramsey conditions with government purchases (`s_C < 1`)

Woodford (2003), *Interest and Prices*, Chapter 6, §5, pp. 455–463 (Assumption 6.2 with
`s_C = C̄/Ȳ < 1`, Benigno–Woodford), and Chapter 7, §1–2 (the timeless perspective).

With purchases, utility is `u(C_t) = u(Y_t − G_t)` and the `F` recursion of the Calvo reset
problem uses `f̂ = LargeDistortions.fhatIso` (`TidyR5GovPurchases`). In the Ramsey Lagrangian
of `NonlinearNKMarkovRamsey`, `ŷ` now enters through consumption `ĉ^C = log((e^{ŷ} − (1 − s_C) −
Ĝ)/s_C)`. As for the Taylor-rule equilibrium, replacing the preference disturbance `ĉ` by
`Θ = s_Cĉ + ŷ − s_Cĉ^C` turns the `s_C = 1` conditions `NonlinearNKMarkovRamsey.ramseyQ` into the
true ones, EXCEPT in the
output condition, where the `λ₁` term carries `∂f̂/∂ŷ = 1 − s_Cσe^{ŷ}/(e^{ŷ} − (1 − s_C) − Ĝ)`
(`DfT`) instead of `1 − σ`; the difference is the correction `govCorr`.

## Main results

* `ThetaR`, `DfT`, `govCorr`, `TidyR6bGovRamsey.ramseyQG` (the true conditions) and
  **`ramseyQG_deriv_y`**: the
  output condition is the derivative of the Lagrangian with `u(Y − G)` (`lagYG`), with
  `u(C) = A_u s_C e^{(1−σ̃)ĉ^C + σ̃ĉ}/(1 − σ̃)`, `σ̃ = s_Cσ ≠ 1`; the other eight conditions are
  those of `NonlinearNKMarkovRamsey.ramseyQ` with the substitute disturbance (`ramseyQG_other`).
* `ThetaS`, `DfS`, `corrS`, `QdG`: the smooth version in deviations; **`QdG_eq`**: it equals the
  true conditions whenever `|ŷ|, |Ĝ| ≤ s_C/4`.
* `QdG_Nd_zero`: the zero-inflation steady state solves the conditions for every `s_C > 0`.
* **`fderiv_QdG`**: the linearisation is `DQr` PLUS `γ_G ŷ` in the output condition, with
  `γ_G = −λ̄₁(1−αβ)σ(1 − s_C)/s_C = ΦA_uσ(1 − s_C)/(s_C(σ + ω))` (`gamG`): purchases change the
  weight of output in the targeting rule from `A_uG` to `H = A_uG − γ_G` (`Hy`).
-/

namespace Woodford.StabilizationWelfare.TidyR6bGovRamsey

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin TidyR5GovPurchases

/-! ## The true conditions -/

/-- Woodford (2003), §5: the TRUE substitute preference disturbance
`Θ = s_Cĉ + ŷ − s_Cĉ^C` (other disturbances unchanged), `e = (ν, ĉ, τ̂, q, μ̂ʷ, Ĝ)`. -/
noncomputable def ThetaR (sC : ℝ) (e : Fin 6 → ℝ) (y : ℝ) : Fin 5 → ℝ :=
  ![e 0, sC * e 1 + y - sC * cGt sC y (e 5), e 2, e 3, e 4]

/-- Woodford (2003), §5: `∂f̂/∂ŷ = 1 − s_Cσe^{ŷ}/(e^{ŷ} − (1 − s_C) − Ĝ)`. -/
noncomputable def DfT (σ sC y g : ℝ) : ℝ :=
  1 - sC * σ * Real.exp y / (Real.exp y - (1 - sC) - g)

/-- Woodford (2003), §5: the correction of the output condition,
`−λ₁(1−αβ)e^{f̂}(∂f̂/∂ŷ − (1−σ))`. -/
noncomputable def govCorr (p : Par) (sC : ℝ) (e : Fin 6 → ℝ) (w : Fin 9 → ℝ) : ℝ :=
  -(w 5 * (1 - p.α * p.β) *
    Real.exp ((1 - p.σ) * w 0 + p.σ * ThetaR sC e (w 0) 1 + e 2) *
      (DfT p.σ sC (w 0) (e 5) - (1 - p.σ)))

/-- Woodford (2003), §5 (**the exact Ramsey conditions with purchases**), current part:
`NonlinearNKMarkovRamsey.ramseyQ` at the substitute disturbance plus the correction in the output
condition. -/
noncomputable def ramseyQG (p : Par) (R : RPar) (sC : ℝ) (e : Fin 6 → ℝ) (wm w : Fin 9 → ℝ) :
    Fin 9 → ℝ :=
  ramseyQ p R (ThetaR sC e (w 0)) wm w + ![govCorr p sC e w, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Woodford (2003), §5: the date-`t` terms of the Lagrangian that involve `ŷ_t` with purchases:
`u(Y − G) − v(Y)Δ + λ₁[e^{F̂} − (1−αβ)e^{f̂}] + λ₂[e^{K̂} − (1−αβ)e^{k̂}]`, with
`u(C) = A_u s_C e^{(1−σ̃)ĉ^C + σ̃ĉ}/(1 − σ̃)`, `σ̃ = s_Cσ`, and `f̂ = LargeDistortions.fhatIso`. -/
noncomputable def lagYG (p : Par) (R : RPar) (sC : ℝ) (e : Fin 6 → ℝ) (w : Fin 9 → ℝ) (y : ℝ) :
    ℝ :=
  R.Au * sC * Real.exp ((1 - sC * p.σ) * cGt sC y (e 5) + sC * p.σ * e 1) / (1 - sC * p.σ)
    - (1 - R.Φ) * R.Au * w 4 * Real.exp ((1 + p.ω) * y - p.ω * e 3) / (1 + p.ω)
    + w 5 * (Real.exp (w 2) - (1 - p.α * p.β) *
      Real.exp (LargeDistortions.fhatIso p.σ sC y (e 5) (e 1) (e 2)))
    + w 6 * (Real.exp (w 3) - (1 - p.α * p.β) * Real.exp ((1 + p.ω) * y - p.ω * e 3 + e 4))

/-- Woodford (2003), §5: the substitute disturbance leaves `τ̂, q, μ̂ʷ` unchanged. -/
theorem ThetaR_234 (sC : ℝ) (e : Fin 6 → ℝ) (y : ℝ) :
    ThetaR sC e y 2 = e 2 ∧ ThetaR sC e y 3 = e 3 ∧ ThetaR sC e y 4 = e 4 := by
  simp [ThetaR]

/-- Woodford (2003), §5: with the substitute disturbance, the exponent of the `F` recursion is
`f̂ = LargeDistortions.fhatIso`. -/
theorem fh_eq (p : Par) (sC : ℝ) (e : Fin 6 → ℝ) (y : ℝ) :
    (1 - p.σ) * y + p.σ * ThetaR sC e y 1 + e 2 =
      LargeDistortions.fhatIso p.σ sC y (e 5) (e 1) (e 2) := by
  simp only [ThetaR, cGt, LargeDistortions.fhatIso, Matrix.cons_val]
  ring

/-- **Woodford (2003), §5 (the output condition with purchases is `∂ℒ/∂ŷ`).** If consumption is
positive (`e^{ŷ} − (1 − s_C) − Ĝ > 0`), `s_C > 0`, `s_Cσ ≠ 1`, then the derivative of `lagYG` in
`ŷ` is the output component of `TidyR6bGovRamsey.ramseyQG`. -/
theorem ramseyQG_deriv_y (p : Par) (R : RPar) {sC : ℝ} (hs : 0 < sC) (hσ : sC * p.σ ≠ 1)
    (hω : 1 + p.ω ≠ 0) (e : Fin 6 → ℝ) (wm w : Fin 9 → ℝ)
    (hC : 0 < Real.exp (w 0) - (1 - sC) - e 5) :
    HasDerivAt (lagYG p R sC e w) (ramseyQG p R sC e wm w 0) (w 0) := by
  have h1σ : 1 - sC * p.σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  set D := Real.exp (w 0) - (1 - sC) - e 5 with hD
  have hD0 := hC.ne'
  have hexp : ∀ c d : ℝ, HasDerivAt (fun y => Real.exp (c * y + d))
      (Real.exp (c * w 0 + d) * c) (w 0) := fun c d => by
    have := (((hasDerivAt_id (w 0)).const_mul c).add_const d).exp
    simpa using this
  -- the logarithm of consumption
  have hcarg : HasDerivAt (fun y => (Real.exp y - (1 - sC) - e 5) / sC)
      (Real.exp (w 0) / sC) (w 0) :=
    (((Real.hasDerivAt_exp (w 0)).sub_const (1 - sC)).sub_const (e 5)).div_const sC
  have hpos : 0 < (Real.exp (w 0) - (1 - sC) - e 5) / sC := div_pos hC hs
  have hc : HasDerivAt (fun y => cGt sC y (e 5)) (Real.exp (w 0) / D) (w 0) := by
    have := hcarg.log hpos.ne'
    refine this.congr_deriv ?_
    rw [hD]; field_simp
  -- the utility term
  have hu : HasDerivAt (fun y => R.Au * sC * Real.exp ((1 - sC * p.σ) * cGt sC y (e 5) +
      sC * p.σ * e 1) / (1 - sC * p.σ))
      (R.Au * sC * (Real.exp ((1 - sC * p.σ) * cGt sC (w 0) (e 5) + sC * p.σ * e 1) *
        ((1 - sC * p.σ) * (Real.exp (w 0) / D))) / (1 - sC * p.σ)) (w 0) :=
    ((((hc.const_mul (1 - sC * p.σ)).add_const (sC * p.σ * e 1)).exp).const_mul
      (R.Au * sC)).div_const (1 - sC * p.σ)
  -- the `f̂` term
  have hf : HasDerivAt (fun y => LargeDistortions.fhatIso p.σ sC y (e 5) (e 1) (e 2))
      (1 - sC * p.σ * (Real.exp (w 0) / D)) (w 0) := by
    have h := (((hasDerivAt_id (w 0)).add_const (sC * p.σ * e 1)).add_const (e 2)).sub
      (hc.const_mul (sC * p.σ))
    refine (h.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp only [LargeDistortions.fhatIso, cGt, id, Pi.sub_apply]
  have d2 := HasDerivAt.div_const (HasDerivAt.const_mul ((1 - R.Φ) * R.Au * w 4)
    (hexp (1 + p.ω) (-(p.ω * e 3)))) (1 + p.ω)
  have d3 := HasDerivAt.const_mul (w 5) (HasDerivAt.const_sub (Real.exp (w 2))
    (HasDerivAt.const_mul (1 - p.α * p.β) hf.exp))
  have d4 := HasDerivAt.const_mul (w 6) (HasDerivAt.const_sub (Real.exp (w 3))
    (HasDerivAt.const_mul (1 - p.α * p.β) (hexp (1 + p.ω) (-(p.ω * e 3) + e 4))))
  have h := HasDerivAt.add (HasDerivAt.add (HasDerivAt.sub hu d2) d3) d4
  have hfun : lagYG p R sC e w = fun y => R.Au * sC * Real.exp ((1 - sC * p.σ) *
      cGt sC y (e 5) + sC * p.σ * e 1) / (1 - sC * p.σ) -
      (1 - R.Φ) * R.Au * w 4 * Real.exp ((1 + p.ω) * y + -(p.ω * e 3)) / (1 + p.ω) +
      w 5 * (Real.exp (w 2) - (1 - p.α * p.β) *
        Real.exp (LargeDistortions.fhatIso p.σ sC y (e 5) (e 1) (e 2))) +
      w 6 * (Real.exp (w 3) - (1 - p.α * p.β) * Real.exp ((1 + p.ω) * y +
        (-(p.ω * e 3) + e 4))) := by
    funext y; simp only [lagYG]; ring_nf
  rw [hfun]
  refine h.congr_deriv ?_
  -- the utility derivative is `A_u e^{(1−σ)ŷ + σΘ}`
  have hcl : Real.exp (cGt sC (w 0) (e 5)) = D / sC := by
    simp only [cGt]; rw [Real.exp_log hpos]
  have hU : R.Au * sC * (Real.exp ((1 - sC * p.σ) * cGt sC (w 0) (e 5) + sC * p.σ * e 1) *
      ((1 - sC * p.σ) * (Real.exp (w 0) / D))) / (1 - sC * p.σ) =
      R.Au * Real.exp ((1 - p.σ) * w 0 + p.σ * ThetaR sC e (w 0) 1) := by
    have e1 : (1 - p.σ) * w 0 + p.σ * ThetaR sC e (w 0) 1 =
        ((1 - sC * p.σ) * cGt sC (w 0) (e 5) + sC * p.σ * e 1) + (w 0 -
          cGt sC (w 0) (e 5)) := by
      simp only [ThetaR, Matrix.cons_val]; ring
    rw [e1, Real.exp_add ((1 - sC * p.σ) * cGt sC (w 0) (e 5) + sC * p.σ * e 1)
      (w 0 - cGt sC (w 0) (e 5)), Real.exp_sub, hcl]
    field_simp
  have hfh := fh_eq p sC e (w 0)
  obtain ⟨t2, t3, t4⟩ := ThetaR_234 sC e (w 0)
  simp only [ramseyQG, govCorr, Pi.add_apply, ramseyQ, Matrix.cons_val, hU, hfh, DfT, ← hD,
    t2, t3, t4]
  field_simp
  ring_nf

/-- Woodford (2003), §5: the other eight conditions with purchases are those of
`NonlinearNKMarkovRamsey.ramseyQ` at the
substitute disturbance (the `F` recursion with `f̂ = fhatIso`). -/
theorem ramseyQG_other (p : Par) (R : RPar) (sC : ℝ) (e : Fin 6 → ℝ) (wm w : Fin 9 → ℝ)
    (i : Fin 9) (hi : i ≠ 0) :
    ramseyQG p R sC e wm w i = ramseyQ p R (ThetaR sC e (w 0)) wm w i := by
  fin_cases i
  · exact absurd rfl hi
  all_goals simp [ramseyQG]

/-- Woodford (2003), §5: with purchases the `F` recursion is `e^{F̂} − (1−αβ)e^{f̂}` with
`f̂ = LargeDistortions.fhatIso`. -/
theorem ramseyQG_F (p : Par) (R : RPar) (sC : ℝ) (e : Fin 6 → ℝ) (wm w : Fin 9 → ℝ) :
    ramseyQG p R sC e wm w 5 = Real.exp (w 2) -
      (1 - p.α * p.β) * Real.exp (LargeDistortions.fhatIso p.σ sC (w 0) (e 5) (e 1) (e 2)) := by
  rw [ramseyQG_other p R sC e wm w 5 (by decide), ← fh_eq]
  simp [ramseyQ, (ThetaR_234 sC e (w 0)).1]

/-! ## The smooth version in deviations -/

/-- Woodford (2003), App. A.3: the smooth substitute disturbance (`TidyR5GovPurchases.ThetaG`). -/
noncomputable def ThetaS (sC : ℝ) (e : Fin 6 → ℝ) (y : ℝ) : Fin 5 → ℝ :=
  ThetaG sC (e, fun _ => y)

/-- Woodford (2003), App. A.3: the smooth `∂f̂/∂ŷ`. -/
noncomputable def DfS (σ sC y g : ℝ) : ℝ :=
  1 - σ * Real.exp y / sfloor ((Real.exp y - (1 - sC) - g) / sC)

/-- Woodford (2003), App. A.3: the smooth correction, in deviations from the steady state. -/
noncomputable def corrS (p : Par) (R : RPar) (sC : ℝ) (e : Fin 6 → ℝ) (u : Fin 9 → ℝ) : ℝ :=
  -((ramseyLam p R 0 + u 5) * (1 - p.α * p.β) *
    Real.exp ((1 - p.σ) * u 0 + p.σ * ThetaS sC e (u 0) 1 + e 2) *
      (DfS p.σ sC (u 0) (e 5) - (1 - p.σ)))

/-- Woodford (2003), §5 and App. A.3 (**the smooth Ramsey conditions with purchases**), current
part in deviations `(w₋ − w̄, w − w̄)`. -/
noncomputable def QdG (p : Par) (R : RPar) (sC : ℝ)
    (q : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ)) : Fin 9 → ℝ :=
  Qd p R (ThetaS sC q.1 (q.2.2 0), q.2.1, q.2.2) +
    ![corrS p R sC q.1 q.2.2, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Woodford (2003), App. A.3: the smooth floor is the identity on `[1/2, ∞)`, so the smooth and
true `∂f̂/∂ŷ` agree where consumption is at least half its steady-state value. -/
theorem DfS_eq {σ sC y g : ℝ} (hs : 0 < sC) (h : 1 / 2 ≤ (Real.exp y - (1 - sC) - g) / sC) :
    DfS σ sC y g = DfT σ sC y g := by
  have hpos : 0 < Real.exp y - (1 - sC) - g := by
    have := (le_div_iff₀ hs).1 h; nlinarith
  simp only [DfS, DfT, sfloor_of_ge h]
  field_simp

/-- Woodford (2003), §5 (**the smooth and the true conditions agree near the steady state**): if
`|ŷ|, |Ĝ| ≤ s_C/4`, the smooth conditions in deviations are the true conditions
`TidyR6bGovRamsey.ramseyQG` at
`(w̄ + u₋, w̄ + u)`. -/
theorem QdG_eq {p : Par} (R : RPar) {sC : ℝ} (hs : 0 < sC)
    {q : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ)} (hy : |q.2.2 0| ≤ sC / 4)
    (hg : |q.1 5| ≤ sC / 4) :
    QdG p R sC q = ramseyQG p R sC q.1 (ramseySS p R + q.2.1) (ramseySS p R + q.2.2) := by
  have hexp : 1 + q.2.2 0 ≤ Real.exp (q.2.2 0) := by
    have := Real.add_one_le_exp (q.2.2 0); linarith
  have h1 : 1 / 2 ≤ (Real.exp (q.2.2 0) - (1 - sC) - q.1 5) / sC := by
    rw [le_div_iff₀ hs]
    have := (abs_le.1 hy).1
    have := (abs_le.1 hg).2
    linarith
  have hw0 : (ramseySS p R + q.2.2) 0 = q.2.2 0 := by simp [ramseySS]
  have hw5 : (ramseySS p R + q.2.2) 5 = ramseyLam p R 0 + q.2.2 5 := by simp [ramseySS]
  have hΘ : ThetaS sC q.1 (q.2.2 0) = ThetaR sC q.1 (q.2.2 0) := by
    have := theta_agree hs (q := (q.1, fun _ => q.2.2 0)) (by simpa using hy) hg
    simp only [ThetaS, this, ThetaGt, ThetaR]
  simp only [QdG, ramseyQG, Qd, corrS, govCorr, hw0, hw5, hΘ, DfS_eq hs h1]

/-- Woodford (2003), App. A.3: the smooth `∂f̂/∂ŷ` is `C^∞`. -/
theorem contDiff_DfS {n : ℕ∞} (σ sC : ℝ) :
    ContDiff ℝ n (fun q : ℝ × ℝ => DfS σ sC q.1 q.2) := by
  unfold DfS
  refine contDiff_const.sub ((contDiff_const.mul (Real.contDiff_exp.comp contDiff_fst)).div
    (contDiff_sfloor.comp (by fun_prop)) fun x => ?_)
  exact (lt_of_lt_of_le (by norm_num) (sfloor_ge _)).ne'

/-- Woodford (2003), App. A.3: the smooth substitute disturbance is `C^∞` in `(e, ŷ)`. -/
theorem contDiff_ThetaS {n : ℕ∞} (sC : ℝ) :
    ContDiff ℝ n (fun q : (Fin 6 → ℝ) × ℝ => ThetaS sC q.1 q.2) :=
  (contDiff_ThetaG (n := n) sC).comp (contDiff_fst.prodMk (contDiff_pi.2 fun _ => contDiff_snd))

/-- Woodford (2003), App. A.3: the smooth conditions are `C^∞`. -/
theorem contDiff_QdG {n : ℕ∞} (p : Par) (R : RPar) (sC : ℝ) : ContDiff ℝ n (QdG p R sC) := by
  have hΘ : ContDiff ℝ n (fun q : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) =>
      ThetaS sC q.1 (q.2.2 0)) :=
    (contDiff_ThetaS (n := n) sC).comp (contDiff_fst.prodMk
      ((contDiff_apply ℝ ℝ (0 : Fin 9)).comp (contDiff_snd.comp contDiff_snd)))
  have h1 : ContDiff ℝ n (fun q : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) =>
      Qd p R (ThetaS sC q.1 (q.2.2 0), q.2.1, q.2.2)) :=
    (contDiff_Qd (n := n) p R).comp (hΘ.prodMk (by fun_prop))
  have hΘ1 : ContDiff ℝ n (fun q : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) =>
      ThetaS sC q.1 (q.2.2 0) 1) := (contDiff_apply ℝ ℝ (1 : Fin 5)).comp hΘ
  have hD : ContDiff ℝ n (fun q : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) =>
      DfS p.σ sC (q.2.2 0) (q.1 5)) :=
    (contDiff_DfS (n := n) p.σ sC).comp (((contDiff_apply ℝ ℝ (0 : Fin 9)).comp
      (contDiff_snd.comp contDiff_snd)).prodMk ((contDiff_apply ℝ ℝ (5 : Fin 6)).comp
        contDiff_fst))
  have hc : ContDiff ℝ n (fun q : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) =>
      corrS p R sC q.1 q.2.2) := by
    unfold corrS
    refine ContDiff.neg (ContDiff.mul (ContDiff.mul (ContDiff.mul (by fun_prop)
      contDiff_const) ?_) (hD.sub contDiff_const))
    exact Real.contDiff_exp.comp (((contDiff_const.mul (by fun_prop)).add
      (contDiff_const.mul hΘ1)).add (by fun_prop))
  refine h1.add (contDiff_pi.2 fun i => ?_)
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
    Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
  · exact hc
  all_goals exact contDiff_const

/-- Woodford (2003), App. A.3: at the steady state the smooth substitute disturbance vanishes. -/
theorem ThetaS_zero {sC : ℝ} (hs : 0 < sC) : ThetaS sC 0 0 = 0 := by
  have : ((0 : Fin 6 → ℝ), fun _ : Fin 4 => (0 : ℝ)) = (0, 0) := rfl
  simp only [ThetaS, this, ThetaG_zero hs]

/-- Woodford (2003), App. A.3: at the steady state the smooth `∂f̂/∂ŷ` is `1 − σ`. -/
theorem DfS_zero (σ : ℝ) {sC : ℝ} (hs : 0 < sC) : DfS σ sC 0 0 = 1 - σ := by
  have h : (Real.exp 0 - (1 - sC) - 0) / sC = 1 := by
    rw [Real.exp_zero]; field_simp; ring
  unfold DfS
  rw [h, sfloor_of_ge (by norm_num : (1 : ℝ) / 2 ≤ 1), Real.exp_zero]
  ring

/-- Woodford (2003), §5 and Ch. 7 (**the zero-inflation steady state with purchases**): for every
`s_C > 0`, `Q(0, 0, 0) + N(0) = 0`. -/
theorem QdG_Nd_zero {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC) :
    QdG p R sC 0 + Nd p R 0 = 0 := by
  have hc : corrS p R sC 0 0 = 0 := by
    simp only [corrS, Pi.zero_apply, DfS_zero p.σ hs]; ring
  have e0 : QdG p R sC 0 = Qd p R (0, 0, 0) := by
    have hq : (0 : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ)) = (0, 0, 0) := rfl
    rw [hq]
    simp only [QdG, Pi.zero_apply, ThetaS_zero hs, hc]
    funext i; fin_cases i <;> simp
  rw [e0]; exact Qd_Nd_zero R hp

/-! ## The linearisation -/

/-- Woodford (2003), §5: the extra weight of output in the linearised output condition,
`γ_G = −λ̄₁(1−αβ)σ(1 − s_C)/s_C`. -/
noncomputable def gamG (p : Par) (R : RPar) (sC : ℝ) : ℝ :=
  -(ramseyLam p R 0 * (1 - p.α * p.β) * (p.σ * (1 - sC) / sC))

/-- Woodford (2003), §5: `γ_G = ΦA_uσ(1 − s_C)/(s_C(σ + ω))`. -/
theorem gamG_eq {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC) :
    gamG p R sC = R.Φ * R.Au * p.σ * (1 - sC) / (sC * (p.σ + p.ω)) := by
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.ω + p.σ ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hωσ' : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  simp only [gamG, ramseyLam, Matrix.cons_val]
  field_simp
  ring

/-- Woodford (2003), §5: the weight of output in the targeting rule with purchases,
`H = A_uG − γ_G`. -/
noncomputable def Hy (p : Par) (R : RPar) (sC : ℝ) : ℝ := R.Au * Gw p R - gamG p R sC

/-- Woodford (2003), §5: the linearised current part with an extra output weight `γ` in the
output condition. -/
noncomputable def DQrX (p : Par) (R : RPar) (γ : ℝ) (um u : Fin 9 → ℝ) : Fin 9 → ℝ :=
  DQr p R um u + ![γ * u 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Woodford (2003), App. A.3: the derivative of the smooth `∂f̂/∂ŷ` along `t ↦ tŷ` at `0` is
`σ(1 − s_C)ŷ/s_C`. -/
theorem hasDerivAt_DfS_line (σ : ℝ) {sC : ℝ} (hs : 0 < sC) (y : ℝ) :
    HasDerivAt (fun t : ℝ => DfS σ sC (t * y) 0) (σ * (1 - sC) / sC * y) 0 := by
  have harg : HasDerivAt (fun t : ℝ => (Real.exp (t * y) - (1 - sC) - 0) / sC) (y / sC) 0 :=
    ((((hasDerivAt_mul_const y).exp.sub_const (1 - sC)).sub_const 0).div_const
      sC).congr_deriv (by simp)
  have hval : (Real.exp (0 * y) - (1 - sC) - 0) / sC = 1 := by
    rw [zero_mul, Real.exp_zero]; field_simp; ring
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 1 / 2 ≤ (Real.exp (t * y) - (1 - sC) - 0) / sC := by
    have hc : ContinuousAt (fun t : ℝ => (Real.exp (t * y) - (1 - sC) - 0) / sC) 0 :=
      harg.continuousAt
    have := hc.eventually (lt_mem_nhds (by rw [hval]; norm_num : (1 / 2 : ℝ) <
      (Real.exp (0 * y) - (1 - sC) - 0) / sC))
    filter_upwards [this] with t ht using ht.le
  have hq : HasDerivAt (fun t : ℝ => Real.exp (t * y) / ((Real.exp (t * y) - (1 - sC) - 0) /
      sC)) ((Real.exp (0 * y) * y * ((Real.exp (0 * y) - (1 - sC) - 0) / sC) -
        Real.exp (0 * y) * (y / sC)) / ((Real.exp (0 * y) - (1 - sC) - 0) / sC) ^ 2) 0 := by
    exact ((hasDerivAt_mul_const y).exp).div harg (by rw [hval]; norm_num)
  have hm := (hq.const_mul σ).const_sub 1
  refine (hm.congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [hval]; simp only [zero_mul, Real.exp_zero]; field_simp; ring
  · filter_upwards [hev] with t ht
    simp only [DfS, sfloor_of_ge ht]
    ring

/-- Woodford (2003), App. A.3: the derivative of the smooth correction along `t ↦ t(0, u)` at
`0` is `γ_G u₀`. -/
theorem hasDerivAt_corrS_line {p : Par} (R : RPar) {sC : ℝ} (hs : 0 < sC) (u : Fin 9 → ℝ) :
    HasDerivAt (fun t : ℝ => corrS p R sC 0 (t • u)) (gamG p R sC * u 0) 0 := by
  -- the exponent
  have hΘ : HasDerivAt (fun t : ℝ => (fun q : (Fin 6 → ℝ) × ℝ => ThetaS sC q.1 q.2 1)
      ((0 : Fin 6 → ℝ), t * u 0)) (fderiv ℝ (fun q : (Fin 6 → ℝ) × ℝ => ThetaS sC q.1 q.2 1)
        ((0 : Fin 6 → ℝ), 0 * u 0) ((0 : Fin 6 → ℝ), u 0)) 0 := by
    have hd : DifferentiableAt ℝ (fun q : (Fin 6 → ℝ) × ℝ => ThetaS sC q.1 q.2 1)
        ((0 : Fin 6 → ℝ), 0 * u 0) :=
      (((contDiff_apply ℝ ℝ (1 : Fin 5)).comp (contDiff_ThetaS (n := 1) sC)).differentiable
        one_ne_zero) _
    have hl : HasDerivAt (fun t : ℝ => ((0 : Fin 6 → ℝ), t * u 0)) ((0 : Fin 6 → ℝ), u 0) 0 := by
      have := (hasDerivAt_const (0 : ℝ) (0 : Fin 6 → ℝ)).prodMk
        ((hasDerivAt_id (0 : ℝ)).mul_const (u 0))
      simpa using this
    exact hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  have hexp := (((((hasDerivAt_id (0 : ℝ)).mul_const (u 0)).const_mul (1 - p.σ)).add
    (hΘ.const_mul p.σ)).add_const ((0 : Fin 6 → ℝ) 2)).exp
  have hl5 : HasDerivAt (fun t : ℝ => ramseyLam p R 0 + t * u 5) (u 5) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (u 5)).const_add (ramseyLam p R 0)
  have hDf := (hasDerivAt_DfS_line p.σ hs (u 0)).sub_const (1 - p.σ)
  have h := (((hl5.mul_const (1 - p.α * p.β)).mul hexp).mul hDf).neg
  have hfun : (fun t : ℝ => corrS p R sC 0 (t • u)) = fun t =>
      -((ramseyLam p R 0 + t * u 5) * (1 - p.α * p.β) *
        Real.exp ((1 - p.σ) * (id t * u 0) + p.σ * ThetaS sC ((0 : Fin 6 → ℝ), t * u 0).1
          ((0 : Fin 6 → ℝ), t * u 0).2 1 + (0 : Fin 6 → ℝ) 2) *
        (DfS p.σ sC (t * u 0) 0 - (1 - p.σ))) := by
    funext t; simp [corrS]
  rw [hfun]
  refine h.congr_deriv ?_
  have h0 : DfS p.σ sC (0 * u 0) 0 - (1 - p.σ) = 0 := by rw [zero_mul, DfS_zero p.σ hs]; ring
  rw [h0]
  simp only [Pi.mul_apply, Pi.add_apply, id, zero_mul, mul_zero, zero_add, add_zero,
    Pi.zero_apply]
  rw [ThetaS_zero hs]
  simp only [Pi.zero_apply, mul_zero, Real.exp_zero, gamG]
  ring

/-- Woodford (2003), App. A.3: the derivative of the smooth substitute disturbance in the
endogenous variables vanishes at the steady state. -/
theorem fderiv_ThetaS_dir {sC : ℝ} (hs : 0 < sC) (um u : Fin 9 → ℝ) :
    fderiv ℝ (fun q : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) => ThetaS sC q.1 (q.2.2 0)) 0
      (0, um, u) = 0 := by
  set ι : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) →L[ℝ] (Fin 6 → ℝ) × (Fin 4 → ℝ) :=
    (ContinuousLinearMap.fst ℝ _ _).prod ((ContinuousLinearMap.pi fun _ =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 9 => ℝ) 0).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))) with hι
  have hf : (fun q : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) => ThetaS sC q.1 (q.2.2 0)) =
      ThetaG sC ∘ ι := by
    funext q; rfl
  have hΘ : HasFDerivAt (ThetaG sC) (fderiv ℝ (ThetaG sC) (0, 0)) (ι 0) := by
    have : ι 0 = (0, 0) := by rw [map_zero]; rfl
    rw [this]
    exact ((contDiff_ThetaG (n := 1) sC).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  rw [hf, (hΘ.comp 0 ι.hasFDerivAt).fderiv]
  have hv : ι (0, um, u) = (0, fun _ => u 0) := by simp [hι]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hv]
  exact fderiv_ThetaG_inr hs _

/-- **Woodford (2003), §5 (the linearisation with purchases).** The derivative of the smooth
conditions at the steady state in the direction `(0, u₋, u)` is `DQr(u₋, u)` plus `γ_G u₀` in the
output condition: `DQrX` with `γ = γ_G`. -/
theorem fderiv_QdG {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC) (um u : Fin 9 → ℝ) :
    fderiv ℝ (QdG p R sC) 0 (0, um, u) = DQrX p R (gamG p R sC) um u := by
  set F1 : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) → Fin 9 → ℝ :=
    fun q => Qd p R (ThetaS sC q.1 (q.2.2 0), q.2.1, q.2.2) with hF1
  set F2 : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) → Fin 9 → ℝ :=
    fun q => ![corrS p R sC q.1 q.2.2, 0, 0, 0, 0, 0, 0, 0, 0] with hF2
  have hΘc : ContDiff ℝ 1 (fun q : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) =>
      ThetaS sC q.1 (q.2.2 0)) :=
    (contDiff_ThetaS (n := 1) sC).comp (contDiff_fst.prodMk (by fun_prop))
  have hP : ContDiff ℝ 1 (fun q : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) =>
      (ThetaS sC q.1 (q.2.2 0), q.2.1, q.2.2)) := hΘc.prodMk (by fun_prop)
  have hd1 : DifferentiableAt ℝ F1 0 :=
    (((contDiff_Qd (n := 1) p R).comp hP).differentiable one_ne_zero) 0
  have hsum : QdG p R sC = fun q => F1 q + F2 q := rfl
  have hd2 : DifferentiableAt ℝ F2 0 := by
    have : F2 = fun q => QdG p R sC q - F1 q := by
      funext q; change F2 q = (F1 q + F2 q) - F1 q; abel
    rw [this]
    exact (((contDiff_QdG (n := 1) p R sC).differentiable one_ne_zero) 0).sub hd1
  rw [hsum, fderiv_fun_add hd1 hd2]
  simp only [add_apply]
  -- the first part
  have e1 : fderiv ℝ F1 0 (0, um, u) = DQr p R um u := by
    set P : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) → (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) :=
      fun q => (ThetaS sC q.1 (q.2.2 0), q.2.1, q.2.2) with hPdef
    have hPd : HasFDerivAt P (fderiv ℝ P 0) 0 := ((hP.differentiable one_ne_zero) 0).hasFDerivAt
    have hP0 : P 0 = 0 := by
      simp only [hPdef, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, ThetaS_zero hs]; rfl
    have hQd : HasFDerivAt (Qd p R) (fderiv ℝ (Qd p R) 0) (P 0) := by
      rw [hP0]
      exact ((contDiff_Qd (n := 1) p R).differentiable one_ne_zero 0).hasFDerivAt
    have hc := (hQd.comp 0 hPd).fderiv
    have hF : F1 = Qd p R ∘ P := rfl
    rw [hF, hc]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    have hdir : fderiv ℝ P 0 (0, um, u) = (0, um, u) := by
      have h1 : HasFDerivAt (fun q : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) =>
          ThetaS sC q.1 (q.2.2 0)) (fderiv ℝ (fun q : (Fin 6 → ℝ) × (Fin 9 → ℝ) ×
            (Fin 9 → ℝ) => ThetaS sC q.1 (q.2.2 0)) 0) 0 :=
        ((hΘc.differentiable one_ne_zero) 0).hasFDerivAt
      have h2 : HasFDerivAt (fun q : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) => q.2)
          (ContinuousLinearMap.snd ℝ _ _) 0 := hasFDerivAt_snd
      rw [(h1.prodMk h2).fderiv]
      simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_snd',
        fderiv_ThetaS_dir hs]
    rw [hdir]
    exact fderiv_Qd R hp um u
  -- the second part
  have e2 : fderiv ℝ F2 0 (0, um, u) = ![gamG p R sC * u 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    have hl : HasDerivAt (fun t : ℝ => ((0 : Fin 6 → ℝ), t • um, t • u))
        ((0 : Fin 6 → ℝ), um, u) 0 := by
      have := (hasDerivAt_const (0 : ℝ) (0 : Fin 6 → ℝ)).prodMk
        (((hasDerivAt_id (0 : ℝ)).smul_const um).prodMk
          ((hasDerivAt_id (0 : ℝ)).smul_const u))
      simpa using this
    have hc := hd2.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp; rfl)
    refine hc.unique (hasDerivAt_pi.2 fun i => ?_)
    fin_cases i
    · change HasDerivAt (fun t : ℝ => corrS p R sC 0 (t • u)) (gamG p R sC * u 0) 0
      exact hasDerivAt_corrS_line R hs u
    all_goals
      change HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0
      exact hasDerivAt_const _ _
  rw [e1, e2]
  rfl

end Woodford.StabilizationWelfare.TidyR6bGovRamsey
