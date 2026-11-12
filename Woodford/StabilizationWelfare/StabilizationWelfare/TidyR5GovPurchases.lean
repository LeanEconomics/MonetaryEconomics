/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5GovNewton
import StabilizationWelfare.LargeDistortions
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Government purchases in the exact Calvo model: existence and uniqueness

Woodford (2003), *Interest and Prices*, Chapter 6, §5, pp. 455–463 (Assumption 6.2 with
`s_C = C̄/Ȳ < 1` and exogenous purchases `Ĝ`), Chapter 4, §2.2 (the Taylor principle,
Proposition 4.3) and Appendix A.3.

With government purchases, consumption is `C_t = Y_t − G_t`; in log deviations
`ĉ^C_t = log((e^{Ŷ_t} − (1 − s_C) − Ĝ_t)/s_C)` (`cGt`), with `Ĝ_t = (G_t − Ḡ)/Ȳ`. The Euler
equation and the revenue term of the Calvo reset problem use the marginal utility of CONSUMPTION:
`exp(−σ̃(ĉ^C − ĉ))` with `σ̃ = s_Cσ` (`σ` the output-units `σ⁻¹ = σ̃/s_C` of the book), and
`f̂ = LargeDistortions.fhatIso` (`QGt_apply`). The model is EXACTLY the `s_C = 1` model of
NonlinearNKMarkov with the preference disturbance replaced by `s_Cĉ + Ŷ − s_Cĉ^C`
(`ThetaGt`), which is a disturbance plus a SECOND-ORDER function of `Ŷ`: the linearisation in the
endogenous variables is unchanged (`fderiv_ThetaG_inr`), so the linear theory (the Taylor
principle, `apriori`, `linSol`, `apriori_ae`, `linSolA`) applies verbatim, and the Newton step of
TidyR5GovNewton does the rest.

The logarithm is only smooth on positive arguments; the theorems use a `C^∞` function `slog`
equal to `Real.log` on `[1/2, ∞)` (`slog_of_ge`), and the radii are chosen so that every point
of the balls lies in that region (`theta_agree`), so the statements are about the TRUE conditions.

## Main results

* `sfloor`, `slog`, `contDiff_slog`, `slog_of_ge`, `hasDerivAt_slog_one`.
* `cGt`, `ThetaGt`, `QGt`, `NGt` (the true conditions) and **`QGt_apply`**, **`NGt_apply`**: the
  Euler equation with consumption `Y − G`, the Calvo recursions with
  `LargeDistortions.fhatIso`, the price index.
* `ThetaG`, `QG`, `NG`, `GMaps`: the smooth version is an `NKMaps` instance (`fderiv_ThetaG_inr`
  computes the derivatives, the steady state is the zero point).
* **`gov_markov_equilibrium`**: existence and local uniqueness of the Markov equilibrium on every
  state space with every Markov operator, radii uniform.
* **`gov_seq_existence`**: the same in sequence space for every `ExpectationSystem` (every event
  tree): existence and uniqueness among all bounded processes; the solution satisfies the Euler
  equation with consumption `Y − G` (`gov_euler`) and EXACTLY the Calvo model
  `LargeDistortions.CalvoModel.CalvoAS` with `s_{C}` and `Ĝ` (**`gov_calvoAS`**), the hypothesis of
  (5.4) and Proposition 6.15.
* **`gov_seq_existence_ae`**: on every filtered probability space with Mathlib's conditional
  expectations: an adapted solution exists and is a.s. unique among a.s. measurable bounded
  processes.
-/

namespace Woodford.StabilizationWelfare.TidyR5GovPurchases

open MeasureTheory Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovLinks NonlinearNKMarkovGeneral ExpectationsMeasure
open NonlinearNKMarkovAE NonlinearNKMarkovAEAdapted TidyR5GovNewton

/-! ## A smooth logarithm -/

/-- A smooth floor: `x` for `x ≥ 1/2`, `1/4` for `x ≤ 1/4`, smooth in between (Woodford (2003),
App. A.3: the conditions are only needed near the steady state). -/
noncomputable def sfloor (x : ℝ) : ℝ := 1 / 4 + (x - 1 / 4) * Real.smoothTransition (4 * x - 1)

/-- Woodford (2003), App. A.3: the smooth floor is the identity on `[1/2, ∞)`. -/
theorem sfloor_of_ge {x : ℝ} (hx : 1 / 2 ≤ x) : sfloor x = x := by
  unfold sfloor
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

/-- Woodford (2003), App. A.3: the smooth floor is at least `1/4`. -/
theorem sfloor_ge (x : ℝ) : 1 / 4 ≤ sfloor x := by
  unfold sfloor
  rcases le_or_gt x (1 / 4) with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · have := Real.smoothTransition.nonneg (4 * x - 1)
    nlinarith

/-- Woodford (2003), App. A.3: the smooth floor is `C^∞`. -/
theorem contDiff_sfloor {n : ℕ∞} : ContDiff ℝ n sfloor := by
  unfold sfloor
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)))

/-- Woodford (2003), App. A.3: a smooth logarithm, `Real.log` on `[1/2, ∞)`. -/
noncomputable def slog (x : ℝ) : ℝ := Real.log (sfloor x)

/-- Woodford (2003), App. A.3: the smooth logarithm is `C^∞`. -/
theorem contDiff_slog {n : ℕ∞} : ContDiff ℝ n slog :=
  contDiff_sfloor.log fun x => (lt_of_lt_of_le (by norm_num) (sfloor_ge x)).ne'

/-- Woodford (2003), App. A.3: the smooth logarithm is `Real.log` on `[1/2, ∞)`. -/
theorem slog_of_ge {x : ℝ} (hx : 1 / 2 ≤ x) : slog x = Real.log x := by
  rw [slog, sfloor_of_ge hx]

/-- Woodford (2003), App. A.3: `slog′(1) = 1`. -/
theorem hasDerivAt_slog_one : HasDerivAt slog 1 1 := by
  have hl : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log (one_ne_zero)
  refine hl.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)] with x hx
  exact slog_of_ge (le_of_lt hx)

/-! ## The model with government purchases -/

/-- Woodford (2003), §5, Assumption 6.2: log consumption relative to steady state,
`ĉ^C = log((e^{Ŷ} − (1 − s_C) − Ĝ)/s_C)` (consumption `C = Y − G`). -/
noncomputable def cGt (sC y g : ℝ) : ℝ := Real.log ((Real.exp y - (1 - sC) - g) / sC)

/-- Woodford (2003), §5: the TRUE substitute disturbance vector: the preference disturbance
`ĉ` is replaced by `s_Cĉ + Ŷ − s_Cĉ^C`; disturbances `e = (ν, ĉ, τ̂, q, μ̂ʷ, Ĝ)`. -/
noncomputable def ThetaGt (sC : ℝ) (q : (Fin 6 → ℝ) × (Fin 4 → ℝ)) : Fin 5 → ℝ :=
  ![q.1 0, sC * q.1 1 + q.2 0 - sC * cGt sC (q.2 0) (q.1 5), q.1 2, q.1 3, q.1 4]

/-- Woodford (2003), §5: the current part of the exact conditions with government purchases. -/
noncomputable def QGt (p : Par) (sC : ℝ) (q : (Fin 6 → ℝ) × (Fin 4 → ℝ)) : Fin 4 → ℝ :=
  Qmap p (ThetaGt sC q, q.2)

/-- Woodford (2003), §5: the part inside `Eₜ` of the exact conditions with government
purchases (evaluated at next period's disturbances and variables). -/
noncomputable def NGt (p : Par) (sC : ℝ) (q : (Fin 6 → ℝ) × (Fin 4 → ℝ)) : Fin 4 → ℝ :=
  Nmap p (ThetaGt sC q, q.2)

/-- **Woodford (2003), §5 (the exact conditions with government purchases).** With
`e = (ν, ĉ, τ̂, q, μ̂ʷ, Ĝ)`, `w = (ŷ, π, F̂, K̂)` and `ĉ^C = cGt s_C ŷ Ĝ`:
the Euler equation with the rule uses the marginal utility of consumption
`exp(−(φ_ππ + φ_yŷ + ν + s_Cσ(ĉ^C − ĉ)))`, the `F` recursion uses
`f̂ = LargeDistortions.fhatIso σ s_C ŷ Ĝ ĉ τ̂`, and the `K` recursion and the price index are those
of `NonlinearNKMarkov.Qmap`. -/
theorem QGt_apply (p : Par) (sC : ℝ) (e : Fin 6 → ℝ) (w : Fin 4 → ℝ) :
    QGt p sC (e, w) 0 = -Real.exp (-(p.φ * w 1 + p.φy * w 0 + e 0 +
      sC * p.σ * (cGt sC (w 0) (e 5) - e 1))) ∧
    QGt p sC (e, w) 1 = Real.exp (w 2) -
      (1 - p.α * p.β) * Real.exp (LargeDistortions.fhatIso p.σ sC (w 0) (e 5) (e 1) (e 2)) ∧
    QGt p sC (e, w) 2 = Qmap p (![e 0, e 1, e 2, e 3, e 4], w) 2 ∧
    QGt p sC (e, w) 3 = Qmap p (![e 0, e 1, e 2, e 3, e 4], w) 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [QGt, Qmap, ThetaGt, Matrix.cons_val]
    congr 2; ring
  · simp only [QGt, Qmap, ThetaGt, Matrix.cons_val, LargeDistortions.fhatIso, cGt]
    congr 3; ring
  · simp [QGt, Qmap, ThetaGt]
  · simp [QGt, Qmap, ThetaGt]

/-- **Woodford (2003), §5 (the expectational part with government purchases).** The Euler term
inside `Eₜ` is `exp(−s_Cσ(ĉ^C′ − ĉ′) − π′)`; the `F`, `K` terms are those of `Nmap`. -/
theorem NGt_apply (p : Par) (sC : ℝ) (e : Fin 6 → ℝ) (w : Fin 4 → ℝ) :
    NGt p sC (e, w) 0 = Real.exp (-(sC * p.σ * (cGt sC (w 0) (e 5) - e 1)) - w 1) ∧
    NGt p sC (e, w) 1 = Nmap p (![e 0, e 1, e 2, e 3, e 4], w) 1 ∧
    NGt p sC (e, w) 2 = Nmap p (![e 0, e 1, e 2, e 3, e 4], w) 2 ∧
    NGt p sC (e, w) 3 = Nmap p (![e 0, e 1, e 2, e 3, e 4], w) 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [NGt, Nmap, ThetaGt, Matrix.cons_val]
    congr 2; ring
  · simp [NGt, Nmap, ThetaGt]
  · simp [NGt, Nmap, ThetaGt]
  · simp [NGt, Nmap, ThetaGt]

/-- Woodford (2003), App. A.3: the smooth version of the consumption log. -/
noncomputable def cG (sC y g : ℝ) : ℝ := slog ((Real.exp y - (1 - sC) - g) / sC)

/-- Woodford (2003), App. A.3: the smooth substitute disturbance vector. -/
noncomputable def ThetaG (sC : ℝ) (q : (Fin 6 → ℝ) × (Fin 4 → ℝ)) : Fin 5 → ℝ :=
  ![q.1 0, sC * q.1 1 + q.2 0 - sC * cG sC (q.2 0) (q.1 5), q.1 2, q.1 3, q.1 4]

/-- Woodford (2003), App. A.3: the smooth current part. -/
noncomputable def QG (p : Par) (sC : ℝ) (q : (Fin 6 → ℝ) × (Fin 4 → ℝ)) : Fin 4 → ℝ :=
  Qmap p (ThetaG sC q, q.2)

/-- Woodford (2003), App. A.3: the smooth lead part. -/
noncomputable def NG (p : Par) (sC : ℝ) (q : (Fin 6 → ℝ) × (Fin 4 → ℝ)) : Fin 4 → ℝ :=
  Nmap p (ThetaG sC q, q.2)

/-- Woodford (2003), §5 (**the smooth and the true conditions agree near the steady state**): if
`|ŷ|, |Ĝ| ≤ s_C/4` then consumption is at least half its steady-state value and the smooth
logarithm is the logarithm. -/
theorem theta_agree {sC : ℝ} (hs : 0 < sC) {q : (Fin 6 → ℝ) × (Fin 4 → ℝ)}
    (hy : |q.2 0| ≤ sC / 4) (hg : |q.1 5| ≤ sC / 4) : ThetaG sC q = ThetaGt sC q := by
  have hexp : 1 + q.2 0 ≤ Real.exp (q.2 0) := by
    have := Real.add_one_le_exp (q.2 0); linarith
  have h1 : 1 / 2 ≤ (Real.exp (q.2 0) - (1 - sC) - q.1 5) / sC := by
    rw [le_div_iff₀ hs]
    have := (abs_le.1 hy).1
    have := (abs_le.1 hg).2
    linarith
  simp only [ThetaG, ThetaGt, cG, cGt, slog_of_ge h1]

/-- Woodford (2003), App. A.3: the norm of a pair bounds its components. -/
theorem comp_le {q : (Fin 6 → ℝ) × (Fin 4 → ℝ)} {ρ : ℝ} (hq1 : ‖q.1‖ ≤ ρ) (hq2 : ‖q.2‖ ≤ ρ) :
    |q.2 0| ≤ ρ ∧ |q.1 5| ≤ ρ := by
  constructor
  · have := (norm_le_pi_norm q.2 0).trans hq2; rwa [Real.norm_eq_abs] at this
  · have := (norm_le_pi_norm q.1 5).trans hq1; rwa [Real.norm_eq_abs] at this

/-- Woodford (2003), App. A.3: at small points the smooth conditions are the true ones. -/
theorem QG_eq {p : Par} {sC : ℝ} (hs : 0 < sC) {q : (Fin 6 → ℝ) × (Fin 4 → ℝ)}
    (hq1 : ‖q.1‖ ≤ sC / 4) (hq2 : ‖q.2‖ ≤ sC / 4) : QG p sC q = QGt p sC q ∧
      NG p sC q = NGt p sC q := by
  obtain ⟨h1, h2⟩ := comp_le hq1 hq2
  simp only [QG, QGt, NG, NGt, theta_agree hs h1 h2, and_self]

/-- Woodford (2003), App. A.3: the smooth substitute disturbances are `C^∞`. -/
theorem contDiff_ThetaG {n : ℕ∞} (sC : ℝ) : ContDiff ℝ n (ThetaG sC) := by
  have hc : ContDiff ℝ n (fun q : (Fin 6 → ℝ) × (Fin 4 → ℝ) => cG sC (q.2 0) (q.1 5)) :=
    contDiff_slog.comp (by fun_prop)
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp only [ThetaG, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
  · fun_prop
  · exact ((contDiff_const.mul (by fun_prop)).add (by fun_prop)).sub (contDiff_const.mul hc)
  · fun_prop
  · fun_prop
  · fun_prop

/-- Woodford (2003), App. A.3: at the steady state the substitute disturbances vanish. -/
theorem ThetaG_zero {sC : ℝ} (hs : 0 < sC) : ThetaG sC (0, 0) = 0 := by
  have hc : cG sC 0 0 = 0 := by
    simp only [cG, Real.exp_zero, sub_zero]
    rw [show (1 - (1 - sC)) / sC = 1 by field_simp; ring, slog_of_ge (by norm_num), Real.log_one]
  funext i
  fin_cases i <;> simp [ThetaG, hc]

/-- **Woodford (2003), §5 (the purchases enter the substitute disturbance only at second order
in the endogenous variables)**: the partial derivative of `ThetaG` in `w` at the steady state is
zero, because `∂ĉ^C/∂Ŷ = 1/s_C` at the steady state. -/
theorem fderiv_ThetaG_inr {sC : ℝ} (hs : 0 < sC) (v : Fin 4 → ℝ) :
    fderiv ℝ (ThetaG sC) (0, 0) (0, v) = 0 := by
  have hd : HasFDerivAt (ThetaG sC) (fderiv ℝ (ThetaG sC) (0, 0)) (0, 0) :=
    ((contDiff_ThetaG (n := 1) sC).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => ((0 : Fin 6 → ℝ), t • v)) ((0 : Fin 6 → ℝ), v) 0 := by
    have := (hasDerivAt_const (0 : ℝ) (0 : Fin 6 → ℝ)).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const v)
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  refine hc.unique (hasDerivAt_pi.2 fun i => ?_)
  -- the line `t ↦ ThetaG (0, t v)` has zero derivative
  have harg : HasDerivAt (fun t : ℝ => (Real.exp (t * v 0) - (1 - sC) - 0) / sC) (v 0 / sC) 0 :=
    (((((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).exp.sub_const (1 - sC)).sub_const 0).div_const
      sC).congr_deriv (by simp)
  have hval : (Real.exp (0 * v 0) - (1 - sC) - 0) / sC = 1 := by
    rw [zero_mul, Real.exp_zero]; field_simp; ring
  have hs1 : HasDerivAt slog 1 ((Real.exp (0 * v 0) - (1 - sC) - 0) / sC) := by
    rw [hval]; exact hasDerivAt_slog_one
  have hslog' : HasDerivAt (slog ∘ fun t : ℝ => (Real.exp (t * v 0) - (1 - sC) - 0) / sC)
      (1 * (v 0 / sC)) 0 := hs1.comp 0 harg
  have hslog : HasDerivAt (fun t : ℝ => slog ((Real.exp (t * v 0) - (1 - sC) - 0) / sC))
      (1 * (v 0 / sC)) 0 := hslog'
  fin_cases i
  · change HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0
    exact hasDerivAt_const _ _
  · change HasDerivAt (fun t : ℝ => sC * 0 + t * v 0 -
      sC * slog ((Real.exp (t * v 0) - (1 - sC) - 0) / sC)) 0 0
    have h := ((hasDerivAt_const (0 : ℝ) (sC * 0)).add ((hasDerivAt_id (0 : ℝ)).mul_const
      (v 0))).sub (hslog.const_mul sC)
    refine h.congr_deriv ?_
    field_simp
    ring
  · change HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0
    exact hasDerivAt_const _ _
  · change HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0
    exact hasDerivAt_const _ _
  · change HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0
    exact hasDerivAt_const _ _

/-- Woodford (2003), App. A.3: the chain rule for `Qmap ∘ (ThetaG, id)` at the steady state. -/
theorem fderiv_comp_inr {sC : ℝ} (hs : 0 < sC) {G : (Fin 5 → ℝ) × (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hG : ContDiff ℝ 1 G) (v : Fin 4 → ℝ) :
    fderiv ℝ (fun q => G (ThetaG sC q, q.2)) (0, 0) (0, v) = fderiv ℝ G (0, 0) (0, v) := by
  have hΘ : HasFDerivAt (ThetaG sC) (fderiv ℝ (ThetaG sC) (0, 0)) (0, 0) :=
    ((contDiff_ThetaG (n := 1) sC).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hP := hΘ.prodMk (hasFDerivAt_snd (p := ((0 : Fin 6 → ℝ), (0 : Fin 4 → ℝ))))
  have hGd : HasFDerivAt G (fderiv ℝ G (ThetaG sC (0, 0), (0 : Fin 4 → ℝ)))
      (ThetaG sC (0, 0), (0 : Fin 4 → ℝ)) :=
    (hG.differentiable one_ne_zero _).hasFDerivAt
  have hcomp := hGd.comp ((0 : Fin 6 → ℝ), (0 : Fin 4 → ℝ)) hP
  have e : (fun q => G (ThetaG sC q, q.2)) = G ∘ fun x => (ThetaG sC x, x.2) := rfl
  rw [e, hcomp.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_snd']
  rw [fderiv_ThetaG_inr hs, ThetaG_zero hs]

/-- **Woodford (2003), §5 and App. A.3 (the model with purchases is an `NKMaps` instance).** -/
noncomputable def GMaps (p : Par) {sC : ℝ} (hs : 0 < sC) : NKMaps p 6 where
  Q := QG p sC
  N := NG p sC
  smoothQ := (contDiff_Qmap (p := p)).comp ((contDiff_ThetaG sC).prodMk contDiff_snd)
  smoothN := (contDiff_Nmap (p := p)).comp ((contDiff_ThetaG sC).prodMk contDiff_snd)
  derivQ v := by
    rw [show QG p sC = fun q => Qmap p (ThetaG sC q, q.2) from rfl,
      fderiv_comp_inr hs contDiff_Qmap v, fderiv_Qmap_inr]
  derivN v := by
    rw [show NG p sC = fun q => Nmap p (ThetaG sC q, q.2) from rfl,
      fderiv_comp_inr hs contDiff_Nmap v, fderiv_Nmap_inr]
  steady := by
    simp only [QG, NG, ThetaG_zero hs]
    funext i
    fin_cases i <;> simp [Qmap, Nmap]

/-! ## Existence and uniqueness with government purchases -/

variable {X : Type*}

/-- Woodford (2003), §5 and App. A.3 (**a Markov equilibrium with government purchases**): at every
state, `Q_G(εξ(x), z(x)) + M[N_G(εξ, z)](x) = 0` with the TRUE conditions `QGt`, `NGt`. -/
def GovEqm (p : Par) (sC : ℝ) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (ξ : X → Fin 6 → ℝ) (ε : ℝ)
    (z : X → Fin 4 → ℝ) : Prop :=
  ∀ x, QGt p sC (ε • ξ x, z x) + Mv M (fun x' => NGt p sC (ε • ξ x', z x')) x = 0

/-- Woodford (2003), App. A.3: within `s_C/4` of the steady state the smooth and the true Markov
conditions coincide. -/
theorem gov_eqm_iff {p : Par} {sC : ℝ} (hs : 0 < sC) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ))
    (ξ : X → Fin 6 → ℝ) (ε : ℝ) (z : X → Fin 4 → ℝ) (he : ∀ x, ‖ε • ξ x‖ ≤ sC / 4)
    (hz : ∀ x, ‖z x‖ ≤ sC / 4) : GEqm (GMaps p hs) M ξ ε z ↔ GovEqm p sC M ξ ε z := by
  have hQ : ∀ x, (GMaps p hs).Q (ε • ξ x, z x) = QGt p sC (ε • ξ x, z x) := fun x =>
    (QG_eq hs (q := (ε • ξ x, z x)) (he x) (hz x)).1
  have hN : (fun x' => (GMaps p hs).N (ε • ξ x', z x')) = fun x' => NGt p sC (ε • ξ x', z x') :=
    funext fun x' => (QG_eq hs (q := (ε • ξ x', z x')) (he x') (hz x')).2
  constructor
  · intro h x
    have := congrFun h x
    simp only [GPhi, Pi.zero_apply] at this
    rw [hQ, hN] at this
    exact this
  · intro h
    funext x
    simp only [GPhi, Pi.zero_apply]
    rw [hQ, hN]
    exact h x

/-- **Woodford (2003), §5, Ch. 4 Proposition 4.3 and App. A.3 (existence and local uniqueness of
the Markov equilibrium WITH GOVERNMENT PURCHASES, `0 < s_C`).** Under the Taylor principle there
are `r, δ > 0`, depending only on the parameters and `s_{C}`, such that for every state space, every
Markov operator and every disturbance pattern `(ν, ĉ, τ̂, q, μ̂ʷ, Ĝ)` with `‖εξ‖ ≤ δ`, there is
exactly one Markov equilibrium of the exact conditions `GovEqm` with `‖z‖ ≤ r`. -/
theorem gov_markov_equilibrium {p : Par} (hp : p.Std) {sC : ℝ} (hs : 0 < sC) :
    ∃ r > 0, ∃ δ > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)), IsMarkov M →
      ∀ (ξ : X → Fin 6 → ℝ) (ε : ℝ), (∀ x, ‖ε • ξ x‖ ≤ δ) →
        ∃ z : X → Fin 4 → ℝ, ((∀ x, ‖z x‖ ≤ r) ∧ GovEqm p sC M ξ ε z) ∧
          ∀ z' : X → Fin 4 → ℝ, (∀ x, ‖z' x‖ ≤ r) → GovEqm p sC M ξ ε z' → z' = z := by
  obtain ⟨r0, hr0, hex⟩ := gen_existence (GMaps p hs) hp
  obtain ⟨ρ, hρ, hun⟩ := gen_uniqueness (GMaps p hs) hp
  set r := min (min r0 ρ) (sC / 4) with hr
  have hr0' : 0 < r := lt_min (lt_min hr0 hρ) (by positivity)
  have hrr0 : r ≤ r0 := (min_le_left _ _).trans (min_le_left _ _)
  have hrρ : r ≤ ρ := (min_le_left _ _).trans (min_le_right _ _)
  have hrs : r ≤ sC / 4 := min_le_right _ _
  obtain ⟨δ1, hδ1, hex1⟩ := hex r hr0' hrr0
  set δ := min δ1 (min ρ (sC / 4)) with hδ
  refine ⟨r, hr0', δ, lt_min hδ1 (lt_min hρ (by positivity)), fun X M hM ξ ε he => ?_⟩
  have he1 : ∀ x, ‖ε • ξ x‖ ≤ δ1 := fun x => (he x).trans (min_le_left _ _)
  have heρ : ∀ x, ‖ε • ξ x‖ ≤ ρ := fun x =>
    (he x).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hes : ∀ x, ‖ε • ξ x‖ ≤ sC / 4 := fun x =>
    (he x).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨z, hzB, hz⟩ := hex1 X M hM ξ ε he1
  have hzs : ∀ x, ‖z x‖ ≤ sC / 4 := fun x => (hzB x).trans hrs
  refine ⟨z, ⟨hzB, (gov_eqm_iff hs M ξ ε z hes hzs).1 hz⟩, fun z' hz'B hz' => ?_⟩
  have hz'G := (gov_eqm_iff hs M ξ ε z' hes fun x => (hz'B x).trans hrs).2 hz'
  exact hun X M hM ξ ε z' z heρ (fun x => (hz'B x).trans hrρ) (fun x => (hzB x).trans hrρ)
    hz'G hz

/-- Woodford (2003), (A.11) with government purchases (**the exact stochastic conditions in
sequence space**): `Q_G(e_t, z_t) + E_t[N_G(e_{t+1}, z_{t+1})] = 0` at every date and state. -/
def GovSeqEqm {Ω : Type*} (p : Par) (sC : ℝ) (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin 6 → ℝ)
    (z : ℕ → Ω → Fin 4 → ℝ) : Prop :=
  ∀ t ω, QGt p sC (e t ω, z t ω) +
    (fun i => 𝔼.E t (fun ω' => NGt p sC (e (t + 1) ω', z (t + 1) ω') i) ω) = 0

/-- Woodford (2003), App. A.3: the sequence-space conditions are the Markov conditions on
`ℕ × Ω` with the expectation operator `seqOp`. -/
theorem govSeqEqm_iff {Ω : Type*} (p : Par) (sC : ℝ) (𝔼 : ExpectationSystem Ω)
    (e : ℕ → Ω → Fin 6 → ℝ) (z : ℕ → Ω → Fin 4 → ℝ) :
    GovSeqEqm p sC 𝔼 e z ↔
      GovEqm p sC (seqOp 𝔼) (fun q => e q.1 q.2) 1 (fun q => z q.1 q.2) := by
  constructor
  · intro h q
    simp only [one_smul]
    exact h q.1 q.2
  · intro h t ω
    have := h (t, ω)
    simp only [one_smul] at this
    exact this

/-- **Woodford (2003), App. A.3 and Proposition 4.3 (sequence-space existence and uniqueness with
government purchases).** For every expectation system (in particular every event tree) and every
disturbance process with `‖e_t(ω)‖ ≤ δ`, the exact stochastic conditions with government
purchases have a solution with `‖z_t(ω)‖ ≤ r`, and it is the only one within `r` among ALL
processes (no adaptedness or Markov structure assumed). -/
theorem gov_seq_existence {p : Par} (hp : p.Std) {sC : ℝ} (hs : 0 < sC) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin 6 → ℝ),
      (∀ t ω, ‖e t ω‖ ≤ δ) → ∃ z : ℕ → Ω → Fin 4 → ℝ, ((∀ t ω, ‖z t ω‖ ≤ r) ∧
        GovSeqEqm p sC 𝔼 e z) ∧ ∀ z' : ℕ → Ω → Fin 4 → ℝ, (∀ t ω, ‖z' t ω‖ ≤ r) →
          GovSeqEqm p sC 𝔼 e z' → z' = z := by
  obtain ⟨r, hr, δ, hδ, h⟩ := gov_markov_equilibrium hp hs
  refine ⟨r, hr, δ, hδ, fun Ω 𝔼 e he => ?_⟩
  obtain ⟨z, ⟨hzB, hz⟩, hu⟩ := h (ℕ × Ω) (seqOp 𝔼) (seqOp_isMarkov 𝔼) (fun q => e q.1 q.2) 1
    (fun q => by simpa using he q.1 q.2)
  refine ⟨fun t ω => z (t, ω), ⟨fun t ω => hzB (t, ω), (govSeqEqm_iff p sC 𝔼 e _).2 hz⟩,
    fun z' hz'B hz' => ?_⟩
  have := hu (fun q => z' q.1 q.2) (fun q => hz'B q.1 q.2) ((govSeqEqm_iff p sC 𝔼 e z').1 hz')
  funext t ω; exact congrFun this (t, ω)

/-- **Woodford (2003), Ch. 4, (2.7)–(2.8), with government purchases (the Euler equation of the
solution, exactly)**: `E_t[e^{−s_Cσ(ĉ^C_{t+1} − ĉ_{t+1}) − π_{t+1}}] =
e^{−(φ_ππ_t + φ_yŶ_t + ν_t + s_Cσ(ĉ^C_t − ĉ_t))}`, the marginal utility of CONSUMPTION
`C = Y − G` in the Euler equation with the rule. -/
theorem gov_euler {Ω : Type*} {p : Par} {sC : ℝ} {𝔼 : ExpectationSystem Ω}
    {e : ℕ → Ω → Fin 6 → ℝ} {z : ℕ → Ω → Fin 4 → ℝ} (h : GovSeqEqm p sC 𝔼 e z) (t : ℕ)
    (ω : Ω) :
    𝔼.E t (fun ω' => Real.exp (-(sC * p.σ * (cGt sC (z (t + 1) ω' 0) (e (t + 1) ω' 5) -
        e (t + 1) ω' 1)) - z (t + 1) ω' 1)) ω =
      Real.exp (-(p.φ * z t ω 1 + p.φy * z t ω 0 + e t ω 0 +
        sC * p.σ * (cGt sC (z t ω 0) (e t ω 5) - e t ω 1))) := by
  have h0 := congrFun (h t ω) 0
  simp only [Pi.add_apply, Pi.zero_apply] at h0
  rw [(QGt_apply p sC _ _).1] at h0
  have e1 : (fun ω' => NGt p sC (e (t + 1) ω', z (t + 1) ω') 0) = fun ω' =>
      Real.exp (-(sC * p.σ * (cGt sC (z (t + 1) ω' 0) (e (t + 1) ω' 5) - e (t + 1) ω' 1)) -
        z (t + 1) ω' 1) := funext fun ω' => (NGt_apply p sC _ _).1
  rw [e1] at h0
  linarith

/-- **Woodford (2003), §5, pp. 457–458 (the Calvo block with government purchases)**: a solution of
the exact conditions with purchases satisfies EXACTLY the Calvo model
`LargeDistortions.CalvoModel.CalvoAS` with `s_{C}` and `Ĝ`: the price index, the reset price, the
recursions for `F` and `K`, `k̂ = (1+ω)Ŷ − ωq + μ̂ʷ` and the revenue term
`f̂ = fhatIso σ s_C Ŷ Ĝ ĉ τ̂` — the hypothesis of (5.4) and Proposition 6.15. -/
theorem gov_calvoAS {Ω : Type*} {p : Par} (hp : p.Std) {sC : ℝ} {𝔼 : ExpectationSystem Ω}
    {e : ℕ → Ω → Fin 6 → ℝ} {z : ℕ → Ω → Fin 4 → ℝ} (h : GovSeqEqm p sC 𝔼 e z) :
    LargeDistortions.CalvoModel.CalvoAS 𝔼 p.α p.β p.θ p.ω p.σ sC
      (fun t ω => z t ω 1) (fun t ω => (z t ω 3 - z t ω 2) / p.c0)
      (fun t ω => z t ω 2) (fun t ω => z t ω 3)
      (fun t ω => LargeDistortions.fhatIso p.σ sC (z t ω 0) (e t ω 5) (e t ω 1) (e t ω 2))
      (fun t ω => (1 + p.ω) * z t ω 0 - p.ω * e t ω 3 + e t ω 4)
      (fun t ω => z t ω 0) (fun t ω => e t ω 5) (fun t ω => e t ω 1)
      (fun t ω => e t ω 3) (fun t ω => e t ω 4) (fun t ω => e t ω 2) where
  priceIndex := by
    intro t ω
    have h3 := congrFun (h t ω) 3
    simp only [Pi.add_apply, Pi.zero_apply] at h3
    rw [(QGt_apply p sC _ _).2.2.2] at h3
    have e1 : (fun ω' => NGt p sC (e (t + 1) ω', z (t + 1) ω') 3) = fun _ => 0 :=
      funext fun ω' => by rw [(NGt_apply p sC _ _).2.2.2]; simp [Nmap]
    rw [e1, 𝔼.const] at h3
    simp only [Qmap, Matrix.cons_val, add_zero] at h3
    rw [mul_div_assoc] at h3
    exact h3
  resetPrice := by
    intro t ω
    have hc0 := hp.c0_pos.ne'
    change p.c0 * ((z t ω 3 - z t ω 2) / p.c0) = _
    field_simp
  recF := by
    intro t
    funext ω
    have h1 := congrFun (h t ω) 1
    simp only [Pi.add_apply, Pi.zero_apply] at h1
    rw [(QGt_apply p sC _ _).2.1] at h1
    have e1 : (fun ω' => NGt p sC (e (t + 1) ω', z (t + 1) ω') 1) = (-(p.α * p.β)) •
        fun ω' => Real.exp ((p.θ - 1) * z (t + 1) ω' 1 + z (t + 1) ω' 2) := funext fun ω' => by
      rw [(NGt_apply p sC _ _).2.1]; simp [Nmap]
    rw [e1, map_smul] at h1
    have e2 : (fun ω' => Real.exp ((p.θ - 1) * z (t + 1) ω' 1 + z (t + 1) ω' 2) - 1) =
        (fun ω' => Real.exp ((p.θ - 1) * z (t + 1) ω' 1 + z (t + 1) ω' 2)) + fun _ => -1 := by
      funext ω'; simp only [Pi.add_apply]; ring
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [e2, map_add, 𝔼.const]
    simp only [Pi.add_apply]
    linear_combination h1
  recK := by
    intro t
    funext ω
    have h2 := congrFun (h t ω) 2
    simp only [Pi.add_apply, Pi.zero_apply] at h2
    rw [(QGt_apply p sC _ _).2.2.1] at h2
    have e1 : (fun ω' => NGt p sC (e (t + 1) ω', z (t + 1) ω') 2) = (-(p.α * p.β)) •
        fun ω' => Real.exp (p.θ * (1 + p.ω) * z (t + 1) ω' 1 + z (t + 1) ω' 3) :=
      funext fun ω' => by rw [(NGt_apply p sC _ _).2.2.1]; simp [Nmap]
    rw [e1, map_smul] at h2
    have e2 : (fun ω' => Real.exp (p.θ * (1 + p.ω) * z (t + 1) ω' 1 + z (t + 1) ω' 3) - 1) =
        (fun ω' => Real.exp (p.θ * (1 + p.ω) * z (t + 1) ω' 1 + z (t + 1) ω' 3)) +
          fun _ => -1 := by
      funext ω'; simp only [Pi.add_apply]; ring
    simp only [Qmap, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2 ⊢
    rw [e2, map_add, 𝔼.const]
    simp only [Pi.add_apply]
    linear_combination h2
  costK := fun _ _ => rfl
  revF := fun _ _ => rfl

/-! ## Almost surely on a filtered probability space -/

variable {Ω : Type*} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)

/-- Woodford (2003), (A.11) with government purchases on a probability space (**the exact
conditions almost surely**): `Q_G(e_t, z_t) + μ[N_G(e_{t+1}, z_{t+1}) | 𝓕_t] = 0` a.s. -/
def GovSeqEqmAE (p : Par) (sC : ℝ) (e : ℕ → Ω → Fin 6 → ℝ) (z : ℕ → Ω → Fin 4 → ℝ) : Prop :=
  ∀ t, (fun ω => QGt p sC (e t ω, z t ω) + MvA E (fun s ω' => NGt p sC (e s ω', z s ω')) t ω)
    =ᵐ[E.μ] 0

/-- Woodford (2003), App. A.3: within `s_C/4` of the steady state the smooth and the true
conditions coincide almost surely. -/
theorem gov_ae_iff {p : Par} {sC : ℝ} (hs : 0 < sC) {e : ℕ → Ω → Fin 6 → ℝ}
    {z : ℕ → Ω → Fin 4 → ℝ} (he : Bd E e (sC / 4)) (hz : Bd E z (sC / 4)) :
    GSeqEqmAE E (GMaps p hs) e z ↔ GovSeqEqmAE E p sC e z := by
  have hN : ∀ t, (fun ω => (GMaps p hs).N (e t ω, z t ω)) =ᵐ[E.μ]
      fun ω => NGt p sC (e t ω, z t ω) := fun t => by
    filter_upwards [he t, hz t] with ω h1 h2
    exact (QG_eq hs (q := (e t ω, z t ω)) h1 h2).2
  have hM := MvA_congr E hN
  constructor
  · intro h t
    filter_upwards [h t, hM t, he t, hz t] with ω h0 hm h1 h2
    simp only [Pi.zero_apply] at h0 ⊢
    rw [← (QG_eq hs (q := (e t ω, z t ω)) h1 h2).1, ← hm]
    exact h0
  · intro h t
    filter_upwards [h t, hM t, he t, hz t] with ω h0 hm h1 h2
    simp only [Pi.zero_apply] at h0 ⊢
    rw [hm, show (GMaps p hs).Q (e t ω, z t ω) = QGt p sC (e t ω, z t ω) from
      (QG_eq hs (q := (e t ω, z t ω)) h1 h2).1]
    exact h0

/-- **Woodford (2003), App. A.3, p. 633, and Proposition 4.3 (existence, adaptedness and
uniqueness WITH GOVERNMENT PURCHASES on a general probability space).** Under the Taylor
principle there are `r, δ > 0` such that on every filtered probability space, for every adapted,
a.s. measurable disturbance process `(ν, ĉ, τ̂, q, μ̂ʷ, Ĝ)` with `‖e_t‖ ≤ δ` a.s., the exact
stochastic conditions with Mathlib's conditional expectations have an adapted, a.s. measurable
solution with `‖z_t‖ ≤ r` a.s., and every a.s. measurable solution within `r` is a.s. equal to it
at every date. -/
theorem gov_seq_existence_ae {p : Par} (hp : p.Std) {sC : ℝ} (hs : 0 < sC) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin 6 → ℝ), Gd E e → Bd E e δ → AdA E e →
        ∃ z : ℕ → Ω → Fin 4 → ℝ, ((Gd E z ∧ Bd E z r ∧ GovSeqEqmAE E p sC e z) ∧ AdA E z) ∧
          ∀ z' : ℕ → Ω → Fin 4 → ℝ, Gd E z' → Bd E z' r → GovSeqEqmAE E p sC e z' →
            ∀ t, z' t =ᵐ[E.μ] z t := by
  obtain ⟨r1, hr1, hex⟩ := gen_seq_existence_ae_adapted (GMaps p hs) hp
  set r := min r1 (sC / 4) with hr
  have hr0 : 0 < r := lt_min hr1 (by positivity)
  have hrs : r ≤ sC / 4 := min_le_right _ _
  obtain ⟨δ1, hδ1, hex1⟩ := hex r hr0 (min_le_left _ _)
  refine ⟨r, hr0, min δ1 (sC / 4), lt_min hδ1 (by positivity), fun Ω _ E e he heb heA => ?_⟩
  have heb1 : Bd E e δ1 := fun t => by
    filter_upwards [heb t] with ω hω; exact hω.trans (min_le_left _ _)
  have hebs : Bd E e (sC / 4) := fun t => by
    filter_upwards [heb t] with ω hω; exact hω.trans (min_le_right _ _)
  obtain ⟨z, ⟨⟨hzG, hzB, hzE⟩, hzA⟩, hu⟩ := hex1 Ω E e he heb1 heA
  have hzs : Bd E z (sC / 4) := fun t => by
    filter_upwards [hzB t] with ω hω; exact hω.trans hrs
  refine ⟨z, ⟨⟨hzG, hzB, (gov_ae_iff E hs hebs hzs).1 hzE⟩, hzA⟩, fun z' hz'G hz'B hz' => ?_⟩
  have hz's : Bd E z' (sC / 4) := fun t => by
    filter_upwards [hz'B t] with ω hω; exact hω.trans hrs
  exact hu z' hz'G hz'B ((gov_ae_iff E hs hebs hz's).2 hz')

end Woodford.StabilizationWelfare.TidyR5GovPurchases
