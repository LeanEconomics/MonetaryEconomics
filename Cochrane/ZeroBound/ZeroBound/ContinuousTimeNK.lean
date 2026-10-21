/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The continuous-time new-Keynesian model: roots, integrals and linear ODEs

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–475
(the roots `λ^f`, `λ^b` and the forward-stable solution (20.8)), building on §5.7 and Online
Appendix A1 §1.12, pp. 579–580. Much of the calculus is restated from the Cochrane Chapter 5
project (`StickyPriceFiscal.CTSimple`).

Continuous time is formalised with deterministic paths `ℝ → ℝ`, exact `HasDerivAt` ODEs, and
infinite-horizon integrals as genuine Bochner integrals with proved integrability.

## Main results

* The roots `λ^f = (√(ρ²+4κσ)+ρ)/2`, `λ^b = (√(ρ²+4κσ)−ρ)/2` (p. 475): `lamf_pos`, `lamb_pos`,
  `lamf_mul_lamb` (`λ^fλ^b = κσ`), `lamf_sub_lamb` (`λ^f − λ^b = ρ`), `lamf_add_lamb`,
  `charpoly_factor` (`D² − ρD − κσ = (D − λ^f)(D + λ^b)`); monotonicity and divergence in `κ`
  (`lamb_strictMono`, `lamb_tendsto_atTop`, `lamf_tendsto_atTop`).
* Forward and backward integrals: `fwdInt a z t = ∫_0^∞ e^{−aτ} z_{t+τ} dτ` and the two-sided
  backward integral `bwdInfInt b z t = ∫_0^∞ e^{−bτ} z_{t−τ} dτ = ∫_{−∞}^t e^{−b(t−s)} z_s ds`,
  with their ODEs `fwdInt_hasDerivAt`, `bwdInfInt_hasDerivAt`.
* Variation of constants with a countable exceptional set (piecewise-smooth paths):
  `linear_ode_Icc`, `affine_ode_Icc`, `linear_ode_Ici`, `unstable_bdd_zero`, `linear_ode_univ`.
* The Green's-function solution (20.8): `greenPi`, `greenPi_hasDerivAt`, and
  `forward_stable_iff`: a solution of `(D − λ^f)(D + λ^b)π = −z` is forward-stable
  (`e^{−λ^f t}π_t → 0`) iff it is `greenPi C` for some `C` (then unique, `greenPi_injective`).
-/

namespace Cochrane.ZeroBound.ContinuousTimeNK

open Filter Topology MeasureTheory

/-! ## The roots `λ^f`, `λ^b` (p. 475) -/

/-- Cochrane (2023), §20.2.2, p. 475: the forward root `λ^f = (√(ρ² + 4κσ) + ρ)/2`. -/
noncomputable def lamf (ρ κ σ : ℝ) : ℝ := (Real.sqrt (ρ ^ 2 + 4 * κ * σ) + ρ) / 2

/-- Cochrane (2023), §20.2.2, p. 475: the backward root `λ^b = (√(ρ² + 4κσ) − ρ)/2`. -/
noncomputable def lamb (ρ κ σ : ℝ) : ℝ := (Real.sqrt (ρ ^ 2 + 4 * κ * σ) - ρ) / 2

/-- Cochrane (2023), §20.2.2, p. 475: for `κ, σ > 0`, `|ρ| < √(ρ² + 4κσ)`. -/
theorem abs_lt_sqrt_disc {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    |ρ| < Real.sqrt (ρ ^ 2 + 4 * κ * σ) := by
  rw [Real.lt_sqrt (abs_nonneg ρ), sq_abs]
  nlinarith [mul_pos hκ hσ]

/-- Cochrane (2023), §20.2.2, p. 475: `(√(ρ² + 4κσ))² = ρ² + 4κσ` for `κσ ≥ 0`. -/
theorem sq_sqrt_disc {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    Real.sqrt (ρ ^ 2 + 4 * κ * σ) ^ 2 = ρ ^ 2 + 4 * κ * σ :=
  Real.sq_sqrt (by nlinarith [mul_pos hκ hσ, sq_nonneg ρ])

/-- Cochrane (2023), §20.2.2, p. 475: `λ^f > 0`. -/
theorem lamf_pos {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) : 0 < lamf ρ κ σ := by
  have h1 := abs_lt_sqrt_disc (ρ := ρ) hκ hσ
  have h2 := neg_abs_le ρ
  unfold lamf
  linarith

/-- Cochrane (2023), §20.2.2, p. 475: `λ^b > 0`. -/
theorem lamb_pos {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) : 0 < lamb ρ κ σ := by
  have h1 := abs_lt_sqrt_disc (ρ := ρ) hκ hσ
  have h2 := le_abs_self ρ
  unfold lamb
  linarith

/-- Cochrane (2023), §20.2.2, p. 475 (A1 p. 579): `λ^f λ^b = κσ`. -/
theorem lamf_mul_lamb {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    lamf ρ κ σ * lamb ρ κ σ = κ * σ := by
  have h := sq_sqrt_disc (ρ := ρ) hκ hσ
  unfold lamf lamb
  linear_combination h / 4

/-- Cochrane (2023), §20.2.2, p. 475: `λ^f − λ^b = ρ`. -/
theorem lamf_sub_lamb (ρ κ σ : ℝ) : lamf ρ κ σ - lamb ρ κ σ = ρ := by
  unfold lamf lamb
  ring

/-- Cochrane (2023), §20.2.2, p. 475: `λ^f + λ^b = √(ρ² + 4κσ)`. -/
theorem lamf_add_lamb (ρ κ σ : ℝ) :
    lamf ρ κ σ + lamb ρ κ σ = Real.sqrt (ρ ^ 2 + 4 * κ * σ) := by
  unfold lamf lamb
  ring

/-- Cochrane (2023), §20.2.2, p. 475: `λ^f + λ^b > 0`. -/
theorem lamf_add_lamb_pos {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    0 < lamf ρ κ σ + lamb ρ κ σ :=
  add_pos (lamf_pos hκ hσ) (lamb_pos hκ hσ)

/-- Cochrane (2023), §20.2.2, p. 475: `λ^f` is a root of `λ² − ρλ − κσ`. -/
theorem lamf_root {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    lamf ρ κ σ ^ 2 = ρ * lamf ρ κ σ + κ * σ := by
  linear_combination lamf_mul_lamb (ρ := ρ) hκ hσ + lamf ρ κ σ * lamf_sub_lamb ρ κ σ

/-- Cochrane (2023), §20.2.2, p. 475: `−λ^b` is a root of `λ² − ρλ − κσ`. -/
theorem lamb_root {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    lamb ρ κ σ ^ 2 + ρ * lamb ρ κ σ = κ * σ := by
  linear_combination lamf_mul_lamb (ρ := ρ) hκ hσ - lamb ρ κ σ * lamf_sub_lamb ρ κ σ

/-- Cochrane (2023), §20.2.2, p. 475 (A1 p. 579): the factorisation
`(D − λ^f)(D + λ^b) = D² − ρD − κσ` of the characteristic polynomial. -/
theorem charpoly_factor {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (z : ℝ) :
    (z - lamf ρ κ σ) * (z + lamb ρ κ σ) = z ^ 2 - ρ * z - κ * σ := by
  linear_combination (-z) * lamf_sub_lamb ρ κ σ - lamf_mul_lamb (ρ := ρ) hκ hσ

/-- Cochrane (2023), §20.2.2, p. 475: `κσ/λ^f = λ^b`. -/
theorem kappa_sigma_div_lamf {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    κ * σ / lamf ρ κ σ = lamb ρ κ σ := by
  rw [div_eq_iff (lamf_pos hκ hσ).ne', ← lamf_mul_lamb hκ hσ]
  ring

/-- Cochrane (2023), §20.2.2, p. 475: with a nonnegative discount rate, `λ^b ≤ λ^f`. -/
theorem lamb_le_lamf {ρ κ σ : ℝ} (hρ : 0 ≤ ρ) : lamb ρ κ σ ≤ lamf ρ κ σ := by
  have := lamf_sub_lamb ρ κ σ
  linarith

/-- Cochrane (2023), §20.2.2, p. 475: the lower bound `λ^b ≥ √(κσ) − ρ/2`. -/
theorem sqrt_sub_le_lamb (ρ κ σ : ℝ) :
    Real.sqrt (κ * σ) - ρ / 2 ≤ lamb ρ κ σ := by
  have h4 : Real.sqrt (4 * (κ * σ)) = 2 * Real.sqrt (κ * σ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hle : Real.sqrt (4 * (κ * σ)) ≤ Real.sqrt (ρ ^ 2 + 4 * κ * σ) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ρ])
  unfold lamb
  linarith

/-- Cochrane (2023), §20.2.2, p. 475: the lower bound `λ^f ≥ √(κσ) + ρ/2`. -/
theorem sqrt_add_le_lamf (ρ κ σ : ℝ) :
    Real.sqrt (κ * σ) + ρ / 2 ≤ lamf ρ κ σ := by
  have := sqrt_sub_le_lamb ρ κ σ
  have := lamf_sub_lamb ρ κ σ
  linarith

/-- Cochrane (2023), §20.2.4, p. 479 ("less sticky ⇒ faster dynamics"): `λ^b` is strictly
increasing in `κ` on `κ > 0`. -/
theorem lamb_strictMono {ρ κ κ' σ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hlt : κ < κ') :
    lamb ρ κ σ < lamb ρ κ' σ := by
  have h : Real.sqrt (ρ ^ 2 + 4 * κ * σ) < Real.sqrt (ρ ^ 2 + 4 * κ' * σ) :=
    Real.sqrt_lt_sqrt (by nlinarith [mul_pos hκ hσ, sq_nonneg ρ]) (by nlinarith)
  unfold lamb
  linarith

/-- Cochrane (2023), §20.2.3, p. 477: `λ^f` is strictly increasing in `κ` on `κ > 0`. -/
theorem lamf_strictMono {ρ κ κ' σ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hlt : κ < κ') :
    lamf ρ κ σ < lamf ρ κ' σ := by
  have := lamb_strictMono (ρ := ρ) hσ hκ hlt
  have := lamf_sub_lamb ρ κ σ
  have := lamf_sub_lamb ρ κ' σ
  linarith

/-- Cochrane (2023), §20.2.3, p. 477: `√(κσ) → ∞` as `κ → ∞` (`σ > 0`). -/
theorem sqrt_kappa_tendsto {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun κ : ℝ => Real.sqrt (κ * σ)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_mul_const hσ)

/-- Cochrane (2023), §20.2.3–20.2.4, pp. 477–479: `λ^b → ∞` as prices become flexible,
`κ → ∞`. -/
theorem lamb_tendsto_atTop (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun κ => lamb ρ κ σ) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_right atTop (-(ρ / 2)) (sqrt_kappa_tendsto hσ))
  exact Eventually.of_forall fun κ => by
    have := sqrt_sub_le_lamb ρ κ σ
    linarith

/-- Cochrane (2023), §20.2.3, p. 477: `λ^f → ∞` as `κ → ∞`. -/
theorem lamf_tendsto_atTop (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun κ => lamf ρ κ σ) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_right atTop (ρ / 2) (sqrt_kappa_tendsto hσ))
  exact Eventually.of_forall fun κ => sqrt_add_le_lamf ρ κ σ

/-! ## Exponentials and improper integrals (restated from the Cochrane Chapter 5 project) -/

/-- Cochrane (2023), §5.7, p. 164 (restated from the Cochrane Chapter 5 project): the discount
factor `e^{−aτ}` has derivative `−a e^{−aτ}`. -/
theorem hasDerivAt_expNeg (a τ : ℝ) :
    HasDerivAt (fun u => Real.exp (-(a * u))) (-a * Real.exp (-(a * τ))) τ := by
  have h1 : HasDerivAt (fun u => -(a * u)) (-a) τ :=
    (HasDerivAt.neg ((hasDerivAt_id' τ).const_mul a)).congr_deriv (by ring)
  exact (HasDerivAt.exp h1).congr_deriv (by ring)

/-- Cochrane (2023), §5.7, p. 164 (restated from the Cochrane Chapter 5 project): the growth
factor `e^{aτ}` has derivative `a e^{aτ}`. -/
theorem hasDerivAt_expPos (a τ : ℝ) :
    HasDerivAt (fun u => Real.exp (a * u)) (a * Real.exp (a * τ)) τ :=
  (HasDerivAt.exp ((hasDerivAt_id' τ).const_mul a)).congr_deriv (by ring)

/-- Cochrane (2023), §20.2.2, p. 475: `e^{−at} → 0` as `t → ∞` for `a > 0`. -/
theorem tendsto_expNeg {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t => Real.exp (-(a * t))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)

/-- Cochrane (2023), §20.2.2, p. 475: `e^{at} → ∞` as `t → ∞` for `a > 0`. -/
theorem tendsto_expPos {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t => Real.exp (a * t)) atTop atTop :=
  Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)

/-- Cochrane (2023), §5.7, p. 163 (restated from the Cochrane Chapter 5 project): if `G' = g`
on `(t, ∞)`, `G` is continuous on `[t, ∞)` and `g` is integrable on `(t, ∞)`, then
`G(T) → G(t) + ∫_t^∞ g`. -/
theorem tendsto_of_deriv_Ioi {G g : ℝ → ℝ} {t : ℝ} (hc : ContinuousOn G (Set.Ici t))
    (hd : ∀ τ, t < τ → HasDerivAt G (g τ) τ) (hg : IntegrableOn g (Set.Ioi t)) :
    Tendsto G atTop (𝓝 (G t + ∫ τ in Set.Ioi t, g τ)) := by
  have hI := (intervalIntegral_tendsto_integral_Ioi t hg tendsto_id).const_add (G t)
  refine hI.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  have hint : IntervalIntegrable g volume t T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 (hg.mono_set Set.Ioc_subset_Ioi_self)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (hc.mono Set.Icc_subset_Ici_self) (fun x hx => hd x hx.1) hint
  simp only [id]
  rw [hftc]
  ring

/-- Cochrane (2023), §5.7, p. 163 (restated from the Cochrane Chapter 5 project): the shift
`∫_0^∞ g(t+τ) dτ = ∫_t^∞ g(τ) dτ`. -/
theorem integral_Ioi_shift (g : ℝ → ℝ) (t : ℝ) :
    ∫ τ in Set.Ioi 0, g (t + τ) = ∫ τ in Set.Ioi t, g τ := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have h : (Set.Ioi (0 : ℝ)).indicator (fun τ => g (t + τ)) =
      fun τ => (Set.Ioi t).indicator g (t + τ) := by
    funext τ
    by_cases hτ : 0 < τ
    · have : t < t + τ := by linarith
      simp [Set.indicator, hτ, this]
    · have : ¬ t < t + τ := by linarith
      simp [Set.indicator, hτ, this]
  rw [h, integral_add_left_eq_self (fun x => (Set.Ioi t).indicator g x) t]

/-- Cochrane (2023), §5.7, p. 165 (restated from the Cochrane Chapter 5 project):
`∫_0^∞ e^{−aτ} f(t+τ) dτ = e^{at} ∫_t^∞ e^{−aτ} f(τ) dτ`. -/
theorem integral_exp_shift (a t : ℝ) (f : ℝ → ℝ) :
    ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * f (t + τ) =
      Real.exp (a * t) * ∫ τ in Set.Ioi t, Real.exp (-(a * τ)) * f τ := by
  rw [← integral_const_mul,
    ← integral_Ioi_shift (fun τ => Real.exp (a * t) * (Real.exp (-(a * τ)) * f τ)) t]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), §5.7.1, p. 165 (restated from the Cochrane Chapter 5 project): a path
bounded on `[t, ∞)` satisfies `e^{−aT}x_T → 0` for `a > 0`. -/
theorem tvc_of_bounded {x : ℝ → ℝ} {a t K : ℝ} (ha : 0 < a) (hb : ∀ T, t ≤ T → |x T| ≤ K) :
    Tendsto (fun T => Real.exp (-(a * T)) * x T) atTop (𝓝 0) := by
  have hK := (tendsto_expNeg ha).mul_const K
  rw [zero_mul] at hK
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [eventually_ge_atTop t] with T hT
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb T hT) (Real.exp_pos _).le

/-- Cochrane (2023), §5.7.1, p. 165 (restated from the Cochrane Chapter 5 project): a
measurable path bounded on `(t, ∞)`, discounted at `a > 0`, is integrable on `(t, ∞)`. -/
theorem integrableOn_exp_mul_of_bdd {z : ℝ → ℝ} {a t M : ℝ} (ha : 0 < a)
    (hm : AEStronglyMeasurable z (volume.restrict (Set.Ioi t)))
    (hb : ∀ τ, t < τ → |z τ| ≤ M) :
    IntegrableOn (fun τ => Real.exp (-(a * τ)) * z τ) (Set.Ioi t) := by
  have hint := (integrableOn_exp_mul_Ioi (a := -a) (by linarith) t).const_mul M
  have hc : Continuous fun τ : ℝ => Real.exp (-(a * τ)) := by fun_prop
  refine Integrable.mono' hint (hc.aestronglyMeasurable.mul hm)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : t < τ) => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hb τ hτ) (Real.exp_pos _).le

/-- Cochrane (2023), §5.7.1, p. 165 (restated from the Cochrane Chapter 5 project):
`|∫_0^∞ e^{−aτ} z(τ) dτ| ≤ M/a` when `|z| ≤ M` on `(0, ∞)`, `a > 0`. -/
theorem abs_integral_exp_le {z : ℝ → ℝ} {a M : ℝ} (ha : 0 < a)
    (hb : ∀ τ, 0 < τ → |z τ| ≤ M) :
    |∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * z τ| ≤ M / a := by
  have hint := (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).const_mul M
  have hbound : ‖∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * z τ‖ ≤
      ∫ τ in Set.Ioi 0, M * Real.exp (-a * τ) := by
    refine norm_integral_le_of_norm_le hint
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : (0 : ℝ) < τ) => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hb τ hτ) (Real.exp_pos _).le
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0] at hbound
  simp only [mul_zero, Real.exp_zero] at hbound
  have hval : M * (-1 / -a) = M / a := by field_simp
  rw [hval, Real.norm_eq_abs] at hbound
  exact hbound

/-- Cochrane (2023), §5.7.1, p. 166 (restated from the Cochrane Chapter 5 project):
`∫_0^∞ e^{−aτ} dτ = 1/a` for `a > 0`. -/
theorem integral_exp_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ τ in Set.Ioi (0 : ℝ), Real.exp (-(a * τ)) = 1 / a := by
  have h := integral_exp_mul_Ioi (a := -a) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_mul] at h
  rw [h]
  field_simp

/-- Cochrane (2023), §5.7.1, p. 166 (restated from the Cochrane Chapter 5 project): `e^{−aτ}` is
integrable on `(0, ∞)` for `a > 0`. -/
theorem integrableOn_exp_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun τ : ℝ => Real.exp (-(a * τ))) (Set.Ioi 0) := by
  have h := integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
  simpa only [neg_mul] using h

/-- Cochrane (2023), §5.7.1, p. 167 (restated from the Cochrane Chapter 5 project):
`∫_0^T e^{−bτ} dτ = (1 − e^{−bT})/b` for `b ≠ 0`. -/
theorem intervalIntegral_exp {b : ℝ} (hb : b ≠ 0) (T : ℝ) :
    ∫ τ in (0 : ℝ)..T, Real.exp (-(b * τ)) = (1 - Real.exp (-(b * T))) / b := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun u => -Real.exp (-(b * u)) / b) (Real.exp (-(b * x))) x := by
    intro x _
    have := ((hasDerivAt_expNeg b x).neg).div_const b
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun τ : ℝ => Real.exp (-(b * τ))).intervalIntegrable 0 T)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  ring

/-- Cochrane (2023), §5.7.1, p. 165, (5.95) (restated from the Cochrane Chapter 5 project):
**the forward value iff the transversality condition.** If `v' = a v − f` on `(t, ∞)`, `v` is
continuous on `[t, ∞)` and `e^{−aτ} f_τ` is integrable on `(t, ∞)`, then `e^{−aT} v_T → 0` iff
`v_t = ∫_0^∞ e^{−aτ} f_{t+τ} dτ`. -/
theorem tvc_iff_forward {v f : ℝ → ℝ} {a t : ℝ} (hc : ContinuousOn v (Set.Ici t))
    (hd : ∀ τ, t < τ → HasDerivAt v (a * v τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-(a * τ)) * f τ) (Set.Ioi t)) :
    Tendsto (fun T => Real.exp (-(a * T)) * v T) atTop (𝓝 0) ↔
      v t = ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * f (t + τ) := by
  have hG : ∀ τ, t < τ → HasDerivAt (fun u => Real.exp (-(a * u)) * v u)
      (-(Real.exp (-(a * τ)) * f τ)) τ := fun τ hτ =>
    ((hasDerivAt_expNeg a τ).mul (hd τ hτ)).congr_deriv (by ring)
  have hGc : ContinuousOn (fun u => Real.exp (-(a * u)) * v u) (Set.Ici t) :=
    (by fun_prop : Continuous fun u : ℝ => Real.exp (-(a * u))).continuousOn.mul hc
  have hlim := tendsto_of_deriv_Ioi hGc hG hint.neg
  rw [integral_neg] at hlim
  rw [integral_exp_shift]
  have hinv : Real.exp (a * t) * Real.exp (-(a * t)) = 1 := by
    rw [← Real.exp_add]; simp
  constructor
  · intro h0
    have h := tendsto_nhds_unique hlim h0
    have : Real.exp (-(a * t)) * v t = ∫ τ in Set.Ioi t, Real.exp (-(a * τ)) * f τ := by
      linarith
    rw [← this, ← mul_assoc, hinv, one_mul]
  · intro hv
    have : Real.exp (-(a * t)) * v t + -∫ τ in Set.Ioi t, Real.exp (-(a * τ)) * f τ = 0 := by
      rw [hv, ← mul_assoc, mul_comm (Real.exp (-(a * t))), hinv, one_mul]
      ring
    rwa [this] at hlim

/-! ## The forward and backward integrals (A1 §1.12) -/

/-- Cochrane (2023), (20.8), p. 474 (A1 §1.12, p. 580): the forward integral
`∫_t^∞ e^{−a(s−t)} z_s ds = ∫_0^∞ e^{−aτ} z_{t+τ} dτ`. -/
noncomputable def fwdInt (a : ℝ) (z : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * z (t + τ)

/-- Cochrane (2023), A1 §1.12, p. 580 (restated from the Cochrane Chapter 5 project): for a
globally bounded continuous `z` and `a > 0`,
`F_a(z)(t) = e^{at}(∫_0^∞ e^{−as} z_s ds − ∫_0^t e^{−as} z_s ds)`. -/
theorem fwdInt_eq {a M : ℝ} {z : ℝ → ℝ} (ha : 0 < a) (hz : Continuous z)
    (hM : ∀ s, |z s| ≤ M) (t : ℝ) :
    fwdInt a z t = Real.exp (a * t) * ((∫ s in Set.Ioi 0, Real.exp (-(a * s)) * z s) -
      ∫ s in (0 : ℝ)..t, Real.exp (-(a * s)) * z s) := by
  have hI : ∀ c, IntegrableOn (fun s => Real.exp (-(a * s)) * z s) (Set.Ioi c) := fun c =>
    integrableOn_exp_mul_of_bdd ha hz.aestronglyMeasurable (fun τ _ => hM τ)
  rw [fwdInt, integral_exp_shift, ← intervalIntegral.integral_interval_add_Ioi (hI 0) (hI t)]
  ring

/-- Cochrane (2023), A1 §1.12, p. 580 (restated from the Cochrane Chapter 5 project): for a
globally bounded continuous `z` and `a > 0`, `F_a(z)' = a F_a(z) − z` at every date. -/
theorem fwdInt_hasDerivAt {a M : ℝ} {z : ℝ → ℝ} (ha : 0 < a) (hz : Continuous z)
    (hM : ∀ s, |z s| ≤ M) (t : ℝ) :
    HasDerivAt (fwdInt a z) (a * fwdInt a z t - z t) t := by
  have hfun : fwdInt a z = fun u => Real.exp (a * u) *
      ((∫ s in Set.Ioi 0, Real.exp (-(a * s)) * z s) -
        ∫ s in (0 : ℝ)..u, Real.exp (-(a * s)) * z s) := funext (fwdInt_eq ha hz hM)
  have hgc : Continuous fun s => Real.exp (-(a * s)) * z s := by fun_prop
  have hP := HasDerivAt.sub (hasDerivAt_const t (∫ s in Set.Ioi 0, Real.exp (-(a * s)) * z s))
    (hgc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have h := (hasDerivAt_expPos a t).mul hP
  rw [hfun]
  convert h using 1
  rw [← hfun]
  have hinv : Real.exp (a * t) * Real.exp (-(a * t)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [fwdInt_eq ha hz hM t]
  simp only [Pi.sub_apply]
  linear_combination (z t) * hinv

/-- Cochrane (2023), A1 §1.12, p. 580: `|F_a(z)(t)| ≤ M/a` when `|z| ≤ M` on `[t, ∞)`. -/
theorem fwdInt_abs_le {a M t : ℝ} {z : ℝ → ℝ} (ha : 0 < a) (hM : ∀ s, t ≤ s → |z s| ≤ M) :
    |fwdInt a z t| ≤ M / a :=
  abs_integral_exp_le ha fun τ hτ => hM (t + τ) (by linarith)

/-- Cochrane (2023), (20.8), p. 474: the two-sided backward integral
`∫_{−∞}^t e^{−b(t−s)} z_s ds = ∫_0^∞ e^{−bτ} z_{t−τ} dτ`. -/
noncomputable def bwdInfInt (b : ℝ) (z : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in Set.Ioi 0, Real.exp (-(b * τ)) * z (t - τ)

/-- Cochrane (2023), (20.8), p. 474: the backward integral is the forward integral of the
time-reversed path, `B_b(z)(t) = F_b(z ∘ neg)(−t)`. -/
theorem bwdInfInt_eq_fwdInt (b : ℝ) (z : ℝ → ℝ) (t : ℝ) :
    bwdInfInt b z t = fwdInt b (fun u => z (-u)) (-t) := by
  unfold bwdInfInt fwdInt
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
  simp only [neg_add, neg_neg, sub_eq_add_neg]

/-- Cochrane (2023), (20.8), p. 474: for a globally bounded continuous `z` and `b > 0`, the
backward integral solves `B' = −b B + z` at every date. -/
theorem bwdInfInt_hasDerivAt {b M : ℝ} {z : ℝ → ℝ} (hb : 0 < b) (hz : Continuous z)
    (hM : ∀ s, |z s| ≤ M) (t : ℝ) :
    HasDerivAt (bwdInfInt b z) (-b * bwdInfInt b z t + z t) t := by
  have hz' : Continuous fun u => z (-u) := hz.comp continuous_neg
  have hF := fwdInt_hasDerivAt hb hz' (fun s => hM (-s)) (-t)
  have hc := HasDerivAt.scomp t hF (hasDerivAt_neg t)
  have hfun : bwdInfInt b z = (fwdInt b fun u => z (-u)) ∘ fun u => -u :=
    funext fun u => bwdInfInt_eq_fwdInt b z u
  rw [hfun]
  refine hc.congr_deriv ?_
  simp only [Function.comp, smul_eq_mul, neg_neg]
  ring

/-- Cochrane (2023), (20.8), p. 474: `|B_b(z)(t)| ≤ M/b` when `|z| ≤ M` on `(−∞, t]`. -/
theorem bwdInfInt_abs_le {b M t : ℝ} {z : ℝ → ℝ} (hb : 0 < b)
    (hM : ∀ s, s ≤ t → |z s| ≤ M) : |bwdInfInt b z t| ≤ M / b :=
  abs_integral_exp_le hb fun τ hτ => hM (t - τ) (by linarith)

/-- Cochrane (2023), (20.8), p. 474: the backward integral is continuous (globally bounded
continuous `z`, `b > 0`). -/
theorem bwdInfInt_continuous {b M : ℝ} {z : ℝ → ℝ} (hb : 0 < b) (hz : Continuous z)
    (hM : ∀ s, |z s| ≤ M) : Continuous (bwdInfInt b z) :=
  continuous_iff_continuousAt.2 fun t => (bwdInfInt_hasDerivAt hb hz hM t).continuousAt

/-- Cochrane (2023), (20.8), p. 474: the forward integral is continuous (globally bounded
continuous `z`, `a > 0`). -/
theorem fwdInt_continuous {a M : ℝ} {z : ℝ → ℝ} (ha : 0 < a) (hz : Continuous z)
    (hM : ∀ s, |z s| ≤ M) : Continuous (fwdInt a z) :=
  continuous_iff_continuousAt.2 fun t => (fwdInt_hasDerivAt ha hz hM t).continuousAt

/-! ## Variation of constants for piecewise-smooth paths -/

/-- Cochrane (2023), §20.2.2, p. 475 (solving piecewise): a function continuous on `[p, q]`
whose derivative vanishes on `(p, q)` off a countable set is constant: `G q = G p`. -/
theorem const_of_hasDerivAt_zero_off {G : ℝ → ℝ} {p q : ℝ} {S : Set ℝ} (hpq : p ≤ q)
    (hS : S.Countable) (hc : ContinuousOn G (Set.Icc p q))
    (hd : ∀ t ∈ Set.Ioo p q \ S, HasDerivAt G 0 t) : G q = G p := by
  have h := integral_eq_of_hasDerivAt_off_countable_of_le G (fun _ => (0 : ℝ)) hpq hS hc hd
    intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at h
  linarith

/-- Cochrane (2023), §20.2.2, p. 475 (A1 §1.12): **uniqueness for `f' = a f` on an interval**,
off a countable set: `f t = e^{a(t−p)} f p` on `[p, q]`. -/
theorem linear_ode_Icc {f : ℝ → ℝ} {a p q : ℝ} {S : Set ℝ} (hS : S.Countable)
    (hc : ContinuousOn f (Set.Icc p q))
    (hd : ∀ t ∈ Set.Ioo p q \ S, HasDerivAt f (a * f t) t) :
    ∀ t ∈ Set.Icc p q, f t = Real.exp (a * (t - p)) * f p := by
  intro t ht
  have hG := const_of_hasDerivAt_zero_off (G := fun u => Real.exp (-(a * u)) * f u)
    (p := p) (q := t) ht.1 hS
    (((by fun_prop : Continuous fun u : ℝ => Real.exp (-(a * u))).continuousOn).mul
      (hc.mono (Set.Icc_subset_Icc le_rfl ht.2)))
    (fun u hu => ((hasDerivAt_expNeg a u).mul (hd u ⟨⟨hu.1.1, lt_of_lt_of_le hu.1.2 ht.2⟩,
      hu.2⟩)).congr_deriv (by ring))
  have h1 : Real.exp (a * (t - p)) * Real.exp (-(a * t)) = Real.exp (-(a * p)) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (a * t) * Real.exp (-(a * t)) = 1 := by
    rw [← Real.exp_add]; simp
  calc f t = Real.exp (a * t) * (Real.exp (-(a * t)) * f t) := by
        rw [← mul_assoc, h2, one_mul]
    _ = Real.exp (a * t) * (Real.exp (-(a * p)) * f p) := by rw [hG]
    _ = Real.exp (a * (t - p)) * f p := by
        rw [← mul_assoc, ← Real.exp_add]; ring_nf

/-- Cochrane (2023), §20.2.2, p. 475 (A1 §1.12): **the affine ODE `f' = a f + b` on an
interval** (off a countable set), `a ≠ 0`:
`f t + b/a = e^{a(t−p)}(f p + b/a)` on `[p, q]`. -/
theorem affine_ode_Icc {f : ℝ → ℝ} {a b p q : ℝ} {S : Set ℝ} (ha : a ≠ 0) (hS : S.Countable)
    (hc : ContinuousOn f (Set.Icc p q))
    (hd : ∀ t ∈ Set.Ioo p q \ S, HasDerivAt f (a * f t + b) t) :
    ∀ t ∈ Set.Icc p q, f t + b / a = Real.exp (a * (t - p)) * (f p + b / a) :=
  linear_ode_Icc (f := fun u => f u + b / a) hS (hc.add continuousOn_const)
    fun t ht => ((hd t ht).add_const (b / a)).congr_deriv (by field_simp)

/-- Cochrane (2023), §20.2.2, p. 475: uniqueness for `f' = a f` on a half-line `[p, ∞)`, off a
countable set: `f t = e^{a(t−p)} f p`. -/
theorem linear_ode_Ici {f : ℝ → ℝ} {a p : ℝ} {S : Set ℝ} (hS : S.Countable)
    (hc : ContinuousOn f (Set.Ici p))
    (hd : ∀ t, p < t → t ∉ S → HasDerivAt f (a * f t) t) :
    ∀ t, p ≤ t → f t = Real.exp (a * (t - p)) * f p := fun t ht =>
  linear_ode_Icc (q := t) hS (hc.mono Set.Icc_subset_Ici_self)
    (fun u hu => hd u hu.1.1 hu.2) t ⟨ht, le_rfl⟩

/-- Cochrane (2023), §20.2.2, p. 475 ("forward-explosive solutions are ruled out"): if
`f' = a f` with `a > 0` on `(p, ∞)` off a countable set, `f` is continuous on `[p, ∞)` and
bounded there, then `f ≡ 0` on `[p, ∞)`. -/
theorem unstable_bdd_zero {f : ℝ → ℝ} {a p K : ℝ} {S : Set ℝ} (ha : 0 < a) (hS : S.Countable)
    (hc : ContinuousOn f (Set.Ici p))
    (hd : ∀ t, p < t → t ∉ S → HasDerivAt f (a * f t) t)
    (hb : ∀ t, p ≤ t → |f t| ≤ K) : ∀ t, p ≤ t → f t = 0 := by
  have hsol := linear_ode_Ici hS hc hd
  have hp : f p = 0 := by
    by_contra hne
    have hpos : 0 < |f p| := abs_pos.2 hne
    have ht : Tendsto (fun t => Real.exp (a * (t - p)) * |f p|) atTop atTop := by
      refine Tendsto.atTop_mul_const hpos ?_
      exact Real.tendsto_exp_atTop.comp
        ((tendsto_atTop_add_const_right atTop (-p) tendsto_id).const_mul_atTop ha |>.congr
          fun t => by simp [sub_eq_add_neg])
    obtain ⟨t, ht1, ht2⟩ := ((ht.eventually_gt_atTop K).and (eventually_ge_atTop p)).exists
    have := hb t ht2
    rw [hsol t ht2, abs_mul, abs_of_pos (Real.exp_pos _)] at this
    linarith
  intro t ht
  rw [hsol t ht, hp, mul_zero]

/-- Cochrane (2023), (20.8), p. 474: uniqueness for `f' = a f` on the whole line:
`f t = e^{at} f 0`. -/
theorem linear_ode_univ {f : ℝ → ℝ} {a : ℝ} (hd : ∀ t, HasDerivAt f (a * f t) t) (t : ℝ) :
    f t = Real.exp (a * t) * f 0 := by
  have hG : ∀ u, HasDerivAt (fun u => Real.exp (-(a * u)) * f u) 0 u := fun u =>
    ((hasDerivAt_expNeg a u).mul (hd u)).congr_deriv (by ring)
  have hc : ∀ u v, Real.exp (-(a * u)) * f u = Real.exp (-(a * v)) * f v := fun u v =>
    is_const_of_deriv_eq_zero (fun w => (hG w).differentiableAt)
      (fun w => (hG w).deriv) u v
  have h0 := hc t 0
  simp only [mul_zero, neg_zero, Real.exp_zero, one_mul] at h0
  have h2 : Real.exp (a * t) * Real.exp (-(a * t)) = 1 := by
    rw [← Real.exp_add]; simp
  calc f t = Real.exp (a * t) * (Real.exp (-(a * t)) * f t) := by
        rw [← mul_assoc, h2, one_mul]
    _ = Real.exp (a * t) * f 0 := by rw [h0]

/-! ## The forward-stable solution (20.8) -/

/-- Cochrane (2023), (20.8), p. 474: the forward-stable family
`π_t = C e^{−λ^b t} + (λ^f + λ^b)⁻¹[∫_{−∞}^t e^{−λ^b(t−s)} z_s ds + ∫_t^∞ e^{−λ^f(s−t)} z_s ds]`,
written for generic roots `lf, lb`. -/
noncomputable def greenPi (lf lb : ℝ) (z : ℝ → ℝ) (C t : ℝ) : ℝ :=
  C * Real.exp (-(lb * t)) + (bwdInfInt lb z t + fwdInt lf z t) / (lf + lb)

/-- Cochrane (2023), (20.8), p. 474: every member of the family satisfies
`π' = −λ^b π + ∫_t^∞ e^{−λ^f(s−t)} z_s ds` (globally bounded continuous `z`, `lf, lb > 0`). -/
theorem greenPi_hasDerivAt {lf lb M C : ℝ} {z : ℝ → ℝ} (hf : 0 < lf) (hb : 0 < lb)
    (hz : Continuous z) (hM : ∀ s, |z s| ≤ M) (t : ℝ) :
    HasDerivAt (greenPi lf lb z C) (-lb * greenPi lf lb z C t + fwdInt lf z t) t := by
  have hd := ((hasDerivAt_expNeg lb t).const_mul C).add
    (((bwdInfInt_hasDerivAt hb hz hM t).add (fwdInt_hasDerivAt hf hz hM t)).div_const (lf + lb))
  refine hd.congr_deriv ?_
  simp only [greenPi]
  field_simp
  ring

/-- Cochrane (2023), (20.8), p. 474: `|π_t − C e^{−λ^b t}| ≤ (M/λ^b + M/λ^f)/(λ^f + λ^b)` —
the particular part of the family is bounded. -/
theorem greenPi_sub_abs_le {lf lb M C : ℝ} {z : ℝ → ℝ} (hf : 0 < lf) (hb : 0 < lb)
    (hM : ∀ s, |z s| ≤ M) (t : ℝ) :
    |greenPi lf lb z C t - C * Real.exp (-(lb * t))| ≤ (M / lb + M / lf) / (lf + lb) := by
  simp only [greenPi, add_sub_cancel_left]
  rw [abs_div, abs_of_pos (by linarith : 0 < lf + lb)]
  exact div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add
    (bwdInfInt_abs_le hb fun s _ => hM s) (fwdInt_abs_le hf fun s _ => hM s)))
    (by linarith)

/-- Cochrane (2023), (20.8), p. 474: the family is injective in `C` (the constant is pinned by
`π_0`). -/
theorem greenPi_injective {lf lb C C' : ℝ} {z : ℝ → ℝ}
    (h : greenPi lf lb z C = greenPi lf lb z C') : C = C' := by
  have := congrFun h 0
  simp only [greenPi, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
  linarith

/-- Cochrane (2023), (20.8), p. 474, the "forward-stable" criterion: along the family,
`e^{−λ^f t} π_t → 0`. -/
theorem greenPi_forward_stable {lf lb M C : ℝ} {z : ℝ → ℝ} (hf : 0 < lf) (hb : 0 < lb)
    (hM : ∀ s, |z s| ≤ M) :
    Tendsto (fun t => Real.exp (-(lf * t)) * greenPi lf lb z C t) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t => C * Real.exp (-((lf + lb) * t))) atTop (𝓝 0) := by
    simpa using (tendsto_expNeg (by linarith : 0 < lf + lb)).const_mul C
  have h2 := tvc_of_bounded (x := fun t => greenPi lf lb z C t - C * Real.exp (-(lb * t)))
    (t := 0) hf fun T _ => greenPi_sub_abs_le hf hb hM T
  have := h1.add h2
  rw [add_zero] at this
  refine this.congr fun t => ?_
  have he : Real.exp (-((lf + lb) * t)) = Real.exp (-(lf * t)) * Real.exp (-(lb * t)) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  ring

/-- Cochrane (2023), (20.8), p. 474: **the forward-stable solutions are exactly the family
(20.8).** Let `z` be continuous and bounded, `lf, lb > 0`. Suppose `π' = −λ^b π + y` and
`y' = λ^f y − z` at every date (i.e. `(D − λ^f)(D + λ^b)π = −z` in first-order form). Then
`e^{−λ^f t}π_t → 0` iff `π = greenPi C` for some `C`; and then `y = ∫_t^∞ e^{−λ^f(s−t)}z_s ds`. -/
theorem forward_stable_iff {lf lb M : ℝ} {z π y : ℝ → ℝ} (hf : 0 < lf) (hb : 0 < lb)
    (hz : Continuous z) (hM : ∀ s, |z s| ≤ M)
    (hπ : ∀ t, HasDerivAt π (-lb * π t + y t) t) (hy : ∀ t, HasDerivAt y (lf * y t - z t) t) :
    Tendsto (fun t => Real.exp (-(lf * t)) * π t) atTop (𝓝 0) ↔
      ∃ C, π = greenPi lf lb z C ∧ y = fwdInt lf z := by
  set F := fwdInt lf z with hF
  -- `w = y − F` solves `w' = λ^f w`
  have hw := linear_ode_univ (f := fun t => y t - F t) (a := lf) fun t =>
    ((hy t).sub (fwdInt_hasDerivAt hf hz hM t)).congr_deriv (by ring)
  set w0 := y 0 - F 0
  -- `D = π − greenPi 0 − w0 e^{λ^f t}/(lf+lb)` solves `D' = −λ^b D`
  have hD := linear_ode_univ (a := -lb)
    (f := fun t => π t - greenPi lf lb z 0 t - w0 * Real.exp (lf * t) / (lf + lb)) fun t => by
      have := ((hπ t).sub (greenPi_hasDerivAt (C := 0) hf hb hz hM t)).sub
        (((hasDerivAt_expPos lf t).const_mul w0).div_const (lf + lb))
      refine this.congr_deriv ?_
      have hwt := hw t
      field_simp
      linear_combination (lf + lb) * hwt
  set D0 := π 0 - greenPi lf lb z 0 0 - w0 * Real.exp (lf * 0) / (lf + lb)
  have hrep : ∀ t, π t = greenPi lf lb z D0 t + w0 * Real.exp (lf * t) / (lf + lb) := by
    intro t
    have h := hD t
    simp only [greenPi] at h ⊢
    have he : Real.exp (-lb * t) = Real.exp (-(lb * t)) := by ring_nf
    rw [he] at h
    linarith
  constructor
  · intro hlim
    have hstab := greenPi_forward_stable (C := D0) hf hb hM
    have hdiff : Tendsto (fun _ : ℝ => w0 / (lf + lb)) atTop (𝓝 0) := by
      have hs := hlim.sub hstab
      rw [sub_zero] at hs
      refine hs.congr fun t => ?_
      rw [hrep t]
      have : Real.exp (-(lf * t)) * Real.exp (lf * t) = 1 := by
        rw [← Real.exp_add]; simp
      field_simp
      linear_combination w0 * this
    have hw0 : w0 / (lf + lb) = 0 := tendsto_nhds_unique tendsto_const_nhds hdiff
    have hw00 : w0 = 0 := by
      rcases div_eq_zero_iff.1 hw0 with h | h
      · exact h
      · linarith
    refine ⟨D0, funext fun t => ?_, funext fun t => ?_⟩
    · rw [hrep t, hw00]; ring
    · have := hw t
      rw [hw00, mul_zero] at this
      linarith
  · rintro ⟨C, hC, -⟩
    rw [hC]
    exact greenPi_forward_stable hf hb hM

end Cochrane.ZeroBound.ContinuousTimeNK
