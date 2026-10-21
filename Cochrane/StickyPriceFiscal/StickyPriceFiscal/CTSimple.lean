/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The simple sticky-price model in continuous time

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.7 and §5.7.1,
pp. 162–167, (5.85)–(5.96), and Online Appendix A1, §1.12, pp. 579–580.

Continuous time is formalised with deterministic paths `ℝ → ℝ` after an unexpected ("MIT")
shock at date `0`: the model equations (5.91)–(5.93) hold as exact `HasDerivAt` ODEs on
`(0, ∞)`, the paths are continuous on `[0, ∞)` (initial values are the right limits after the
time-`0` news), and infinite-horizon integrals are genuine Bochner integrals over `(0, ∞)` with
proved integrability. Only the values on `[0, ∞)` matter.

## Main results

* Scalar linear ODEs (A1 §1.12): `ode_forward_bounded` (`y' = a y + z`, `a > 0`, bounded ⇒
  `y = −∫₀^∞ e^{−aτ} z_{t+τ} dτ`, existence `fwdInt_hasDerivAt`), `ode_backward`
  (`y' = −b y + z` iff `y = e^{−bt}y_0 + ∫₀^t e^{−bτ}z_{t−τ}dτ`), `tvc_iff_forward`.
* The roots `λ₁, λ₂` (p. 165, A1 p. 579): `lam1_pos`, `lam2_pos`, `lam_mul` (`λ₁λ₂ = κσ`),
  `lam_sub` (`λ₁ − λ₂ = ρ`), `charpoly_factor` (`(D − λ₁)(D + λ₂) = D² − ρD − κσ`),
  `second_order` (A1 p. 579).
* p. 163 integral forms: `ct_is_integral`, `ct_pc_integral`.
* (5.94): `ct_family` — for any bounded continuous interest-rate path, `(x, π)` is a bounded
  solution of (5.91)–(5.92) **iff** `π` is of the form (5.94) for some `C₀` (and `x` is given
  by (5.92)); `ct_family_pinned_by_pi0`: the family is indexed by `π₀`.
* (5.95): `ct_value` (iff the transversality condition), `ct_value_flexible`,
  `flexible_value_must_jump`; the flexible-price case of (5.94), `ct_flexible_limit`
  (`π_t → i_t` as `κ → ∞`, via the approximate identity `approx_identity`).
* `ct_equilibrium_exists_unique`, `ct_equilibrium_pi0`: with debt predetermined (no price-level
  jump), the valuation equation selects exactly one member of the family.
* The step example and (5.96): `ct_step_family`, `ct_step_value`, `ct_step_solution`,
  `ct_step_debt`, `ct_fisherian`, `ct_fiscal_shock`, `ct_step_price`.
* Cumulative inflation and the frictionless limit (p. 167): `ct_cum_inflation`,
  `lam2_tendsto_atTop`, `ct_frictionless_limit`, `ct_price_limit`.
* Figure 5.10 (pp. 172–173): the perpetuity bond price `fig510_bond_price`, initial inflation
  `fig510` (π₀ and the price path, with no jump: `p(0) = 0`), and its smooth limit
  `fig510_price_limit` (`p(t) → t − 1/(r + ω)` for every `t > 0` as `κ → ∞`); initial
  disinflation iff `ω < λ₂` (`fig510_initial_disinflation`), the disinflation period
  (`fig510_disinflation_iff`) and its lengthening as `κ` falls (`fig510_disinflation_longer`).
-/

namespace Cochrane.StickyPriceFiscal.CTSimple

open Filter Topology MeasureTheory

/-! ## Improper integrals and scalar linear ODEs (A1 §1.12) -/

/-- Cochrane (2023), §5.7, p. 163 (integrating a flow forward): if `G' = g` on `(t, ∞)`, `G` is
continuous on `[t, ∞)` and `g` is integrable on `(t, ∞)`, then `G(T) → G(t) + ∫_t^∞ g`. -/
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

/-- Cochrane (2023), §5.7, p. 163 (restated from the Cochrane Chapter 3 project): the shift
`τ ↦ t + τ`, `∫_0^∞ g(t+τ) dτ = ∫_t^∞ g(τ) dτ`. -/
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

/-- Cochrane (2023), §5.7, p. 165: the discounted shifted integral,
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

/-- Cochrane (2023), §5.7, p. 164: the discount factor `e^{−aτ}` has derivative `−a e^{−aτ}`. -/
theorem hasDerivAt_expNeg (a τ : ℝ) :
    HasDerivAt (fun u => Real.exp (-(a * u))) (-a * Real.exp (-(a * τ))) τ := by
  have h1 : HasDerivAt (fun u => -(a * u)) (-a) τ :=
    (HasDerivAt.neg ((hasDerivAt_id' τ).const_mul a)).congr_deriv (by ring)
  exact (HasDerivAt.exp h1).congr_deriv (by ring)

/-- Cochrane (2023), §5.7, p. 164: the growth factor `e^{aτ}` has derivative `a e^{aτ}`. -/
theorem hasDerivAt_expPos (a τ : ℝ) :
    HasDerivAt (fun u => Real.exp (a * u)) (a * Real.exp (a * τ)) τ :=
  (HasDerivAt.exp ((hasDerivAt_id' τ).const_mul a)).congr_deriv (by ring)

/-- Cochrane (2023), §5.7.1, p. 165 (restated from the Cochrane Chapter 3 project): a path
bounded on `[t, ∞)` satisfies the transversality condition `e^{−aT}x_T → 0` for `a > 0`. -/
theorem tvc_of_bounded {x : ℝ → ℝ} {a t K : ℝ} (ha : 0 < a) (hb : ∀ T, t ≤ T → |x T| ≤ K) :
    Tendsto (fun T => Real.exp (-(a * T)) * x T) atTop (𝓝 0) := by
  have he : Tendsto (fun T => Real.exp (-(a * T))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)
  have hK := he.mul_const K
  rw [zero_mul] at hK
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [eventually_ge_atTop t] with T hT
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb T hT) (Real.exp_pos _).le

/-- Cochrane (2023), §5.7.1, p. 165: a measurable path bounded by `M` on `(t, ∞)`, discounted at
`a > 0`, is integrable on `(t, ∞)`. -/
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

/-- Cochrane (2023), §5.7.1, p. 165: `|∫_0^∞ e^{−aτ} z(τ) dτ| ≤ M/a` when `|z| ≤ M` on
`(0, ∞)` and `a > 0`. -/
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

/-- Cochrane (2023), §5.7.1, p. 166: `∫_0^∞ e^{−aτ} dτ = 1/a` for `a > 0`. -/
theorem integral_exp_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ τ in Set.Ioi (0 : ℝ), Real.exp (-(a * τ)) = 1 / a := by
  have h := integral_exp_mul_Ioi (a := -a) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_mul] at h
  rw [h]
  field_simp

/-- Cochrane (2023), §5.7.1, p. 166: `e^{−aτ}` is integrable on `(0, ∞)` for `a > 0`. -/
theorem integrableOn_exp_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun τ : ℝ => Real.exp (-(a * τ))) (Set.Ioi 0) := by
  have h := integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
  simpa only [neg_mul] using h

/-- Cochrane (2023), §5.7.1, p. 167: `∫_0^T e^{−bτ} dτ = (1 − e^{−bT})/b` for `b ≠ 0`. -/
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

/-- Cochrane (2023), §5.7.1, p. 165, (5.95): **the forward value iff the transversality
condition.** If `v' = a v − f` on `(t, ∞)`, `v` is continuous on `[t, ∞)` and `e^{−aτ} f_τ` is
integrable on `(t, ∞)`, then `e^{−aT} v_T → 0` iff `v_t = ∫_0^∞ e^{−aτ} f_{t+τ} dτ`. -/
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
  have hpos := Real.exp_pos (a * t)
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

/-! ### The forward integral -/

/-- Cochrane (2023), A1 §1.12, p. 580: the forward (stationary) integral
`F_a(z)(t) = ∫_0^∞ e^{−aτ} z_{t+τ} dτ`. -/
noncomputable def fwdInt (a : ℝ) (z : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * z (t + τ)

/-- Cochrane (2023), A1 §1.12, p. 580: for a globally bounded continuous `z` and `a > 0`,
`F_a(z)(t) = e^{at}(∫_0^∞ e^{−as} z_s ds − ∫_0^t e^{−as} z_s ds)`. -/
theorem fwdInt_eq {a M : ℝ} {z : ℝ → ℝ} (ha : 0 < a) (hz : Continuous z)
    (hM : ∀ s, |z s| ≤ M) (t : ℝ) :
    fwdInt a z t = Real.exp (a * t) * ((∫ s in Set.Ioi 0, Real.exp (-(a * s)) * z s) -
      ∫ s in (0 : ℝ)..t, Real.exp (-(a * s)) * z s) := by
  have hI : ∀ c, IntegrableOn (fun s => Real.exp (-(a * s)) * z s) (Set.Ioi c) := fun c =>
    integrableOn_exp_mul_of_bdd ha hz.aestronglyMeasurable (fun τ _ => hM τ)
  rw [fwdInt, integral_exp_shift, ← intervalIntegral.integral_interval_add_Ioi (hI 0) (hI t)]
  ring

/-- Cochrane (2023), A1 §1.12, p. 580: **existence of the forward solution**: for a globally
bounded continuous `z` and `a > 0`, `F_a(z)` has derivative `a F_a(z) − z` at every date, so
`y = −F_a(z)` solves `y' = a y + z`. -/
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

/-- Cochrane (2023), A1 §1.12, p. 580: `F_a(z)` is continuous (globally bounded continuous `z`,
`a > 0`). -/
theorem fwdInt_continuous {a M : ℝ} {z : ℝ → ℝ} (ha : 0 < a) (hz : Continuous z)
    (hM : ∀ s, |z s| ≤ M) : Continuous (fwdInt a z) :=
  continuous_iff_continuousAt.2 fun t => (fwdInt_hasDerivAt ha hz hM t).continuousAt

/-- Cochrane (2023), A1 §1.12, p. 580: the forward integral is bounded, `|F_a(z)| ≤ M/a`, when
`|z| ≤ M` on `[t, ∞)`. -/
theorem fwdInt_abs_le {a M t : ℝ} {z : ℝ → ℝ} (ha : 0 < a) (hM : ∀ s, t ≤ s → |z s| ≤ M) :
    |fwdInt a z t| ≤ M / a :=
  abs_integral_exp_le ha fun τ hτ => hM (t + τ) (by linarith)

/-- Cochrane (2023), §5.7.1, p. 166: the forward integral of a constant, `F_a(c) = c/a`. -/
theorem fwdInt_const {a : ℝ} (ha : 0 < a) (c t : ℝ) : fwdInt a (fun _ => c) t = c / a := by
  rw [fwdInt, integral_mul_const, integral_exp_Ioi ha]
  ring

/-- Cochrane (2023), A1 §1.12, p. 580: linearity, `F_a(c z) = c F_a(z)`. -/
theorem fwdInt_const_mul (a c : ℝ) (z : ℝ → ℝ) (t : ℝ) :
    fwdInt a (fun s => c * z s) t = c * fwdInt a z t := by
  rw [fwdInt, fwdInt, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  ring

/-- Cochrane (2023), A1 §1.12, p. 580: `F_a(z)(t)` for `t ≥ 0` depends only on `z` on
`[0, ∞)`. -/
theorem fwdInt_congr {a t : ℝ} {z z' : ℝ → ℝ} (ht : 0 ≤ t) (h : ∀ s, 0 ≤ s → z s = z' s) :
    fwdInt a z t = fwdInt a z' t := by
  refine setIntegral_congr_fun measurableSet_Ioi fun τ (hτ : (0 : ℝ) < τ) => ?_
  simp only [h (t + τ) (by linarith)]

/-- Cochrane (2023), A1 §1.12, p. 580: **uniqueness of the forward solution.** If `a > 0`,
`z` is globally bounded and continuous, `y` is continuous on `[0, ∞)`, bounded there, and
`y' = a y + z` on `(0, ∞)`, then `y_t = −∫_0^∞ e^{−aτ} z_{t+τ} dτ` for every `t ≥ 0`. -/
theorem ode_forward_bounded {a M K : ℝ} {y z : ℝ → ℝ} (ha : 0 < a) (hz : Continuous z)
    (hM : ∀ s, |z s| ≤ M) (hc : ContinuousOn y (Set.Ici 0))
    (hd : ∀ τ, 0 < τ → HasDerivAt y (a * y τ + z τ) τ) (hb : ∀ τ, 0 ≤ τ → |y τ| ≤ K)
    (t : ℝ) (ht : 0 ≤ t) : y t = -fwdInt a z t := by
  have hint : IntegrableOn (fun τ => Real.exp (-(a * τ)) * (-z τ)) (Set.Ioi t) :=
    integrableOn_exp_mul_of_bdd ha hz.neg.aestronglyMeasurable
      (fun τ _ => by rw [abs_neg]; exact hM τ)
  have h := (tvc_iff_forward (f := fun τ => -z τ) (hc.mono (Set.Ici_subset_Ici.2 ht))
    (fun τ hτ => (hd τ (by linarith)).congr_deriv (by ring)) hint).1
    (tvc_of_bounded ha fun T hT => hb T (by linarith))
  rw [h, fwdInt, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  ring

/-! ### The backward integral -/

/-- Cochrane (2023), A1 §1.12, p. 580: the backward integral
`B_b(z)(t) = ∫_0^t e^{−bτ} z_{t−τ} dτ`. -/
noncomputable def bwdInt (b : ℝ) (z : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..t, Real.exp (-(b * τ)) * z (t - τ)

/-- Cochrane (2023), A1 §1.12, p. 580: `B_b(z)(t) = e^{−bt} ∫_0^t e^{bs} z_s ds`. -/
theorem bwdInt_eq (b : ℝ) (z : ℝ → ℝ) (t : ℝ) :
    bwdInt b z t = Real.exp (-(b * t)) * ∫ s in (0 : ℝ)..t, Real.exp (b * s) * z s := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun u => Real.exp (-(b * (t - u))) * z u) t (a := 0) (b := t)
  simp only [sub_sub_cancel, sub_self, sub_zero] at h
  rw [bwdInt, h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), A1 §1.12, p. 580: **the backward solution solves `y' = −b y + z`**:
for continuous `z`, `B_b(z)' = −b B_b(z) + z` at every date. -/
theorem bwdInt_hasDerivAt {b : ℝ} {z : ℝ → ℝ} (hz : Continuous z) (t : ℝ) :
    HasDerivAt (bwdInt b z) (-b * bwdInt b z t + z t) t := by
  have hfun : bwdInt b z = fun u =>
      Real.exp (-(b * u)) * ∫ s in (0 : ℝ)..u, Real.exp (b * s) * z s :=
    funext (bwdInt_eq b z)
  have hgc : Continuous fun s => Real.exp (b * s) * z s := by fun_prop
  have h := (hasDerivAt_expNeg b t).mul (hgc.integral_hasStrictDerivAt 0 t).hasDerivAt
  rw [hfun]
  convert h using 1
  have hinv : Real.exp (-(b * t)) * Real.exp (b * t) = 1 := by
    rw [← Real.exp_add]; simp
  simp only
  linear_combination (-(z t)) * hinv

/-- Cochrane (2023), A1 §1.12, p. 580: `B_b(z)` is continuous for continuous `z`. -/
theorem bwdInt_continuous {b : ℝ} {z : ℝ → ℝ} (hz : Continuous z) : Continuous (bwdInt b z) :=
  continuous_iff_continuousAt.2 fun t => (bwdInt_hasDerivAt hz t).continuousAt

/-- Cochrane (2023), A1 §1.12, p. 580: `B_b(z)(0) = 0`. -/
theorem bwdInt_zero (b : ℝ) (z : ℝ → ℝ) : bwdInt b z 0 = 0 := by
  simp [bwdInt]

/-- Cochrane (2023), A1 §1.12, p. 580: `|B_b(z)(t)| ≤ M/b` for `b > 0`, `t ≥ 0` and `|z| ≤ M`
on `[0, t]`. -/
theorem bwdInt_abs_le {b M t : ℝ} {z : ℝ → ℝ} (hb : 0 < b) (ht : 0 ≤ t)
    (hM : ∀ s, 0 ≤ s → s ≤ t → |z s| ≤ M) : |bwdInt b z t| ≤ M / b := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 le_rfl ht)
  have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht
    (f := fun τ => Real.exp (-(b * τ)) * z (t - τ)) (g := fun τ => M * Real.exp (-(b * τ)))
    (ae_of_all _ fun τ (hτ : τ ∈ Set.Ioc 0 t) => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM (t - τ) (by linarith [hτ.2]) (by linarith [hτ.1]))
        (Real.exp_pos _).le)
    ((by fun_prop : Continuous fun τ : ℝ => M * Real.exp (-(b * τ))).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul, intervalIntegral_exp hb.ne', Real.norm_eq_abs] at hle
  rw [bwdInt]
  refine hle.trans ?_
  have he := Real.exp_pos (-(b * t))
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right (by nlinarith) hb.le

/-- Cochrane (2023), §5.7.1, p. 166: the backward integral of a constant,
`B_b(c)(t) = c (1 − e^{−bt})/b`. -/
theorem bwdInt_const {b : ℝ} (hb : b ≠ 0) (c t : ℝ) :
    bwdInt b (fun _ => c) t = c * (1 - Real.exp (-(b * t))) / b := by
  rw [bwdInt, intervalIntegral.integral_mul_const, intervalIntegral_exp hb]
  ring

/-- Cochrane (2023), A1 §1.12, p. 580: `B_b(z)(t)` for `t ≥ 0` depends only on `z` on
`[0, t]`. -/
theorem bwdInt_congr {b t : ℝ} {z z' : ℝ → ℝ} (ht : 0 ≤ t) (h : ∀ s, 0 ≤ s → z s = z' s) :
    bwdInt b z t = bwdInt b z' t := by
  refine intervalIntegral.integral_congr fun τ hτ => ?_
  rw [Set.uIcc_of_le ht] at hτ
  simp only [h (t - τ) (by linarith [hτ.2])]

/-- Cochrane (2023), A1 §1.12, p. 580: **uniqueness for `y' = −b y`**: a path continuous on
`[0, ∞)` with `w' = −b w` on `(0, ∞)` is `w_t = e^{−bt} w_0`. -/
theorem decay_unique {b : ℝ} {w : ℝ → ℝ} (hc : ContinuousOn w (Set.Ici 0))
    (hd : ∀ τ, 0 < τ → HasDerivAt w (-b * w τ) τ) (t : ℝ) (ht : 0 ≤ t) :
    w t = Real.exp (-(b * t)) * w 0 := by
  have hG : ∀ τ ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt (fun u => Real.exp (b * u) * w u) ((fun _ => (0 : ℝ)) τ) τ := fun τ hτ =>
    ((hasDerivAt_expPos b τ).mul (hd τ hτ.1)).congr_deriv (by ring)
  have hGc : ContinuousOn (fun u => Real.exp (b * u) * w u) (Set.Icc 0 t) :=
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (b * u)).continuousOn.mul hc).mono
      Set.Icc_subset_Ici_self
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hGc hG
    (intervalIntegrable_const (μ := (volume : Measure ℝ)))
  simp only [intervalIntegral.integral_zero, mul_zero, Real.exp_zero, one_mul] at h
  have hinv : Real.exp (-(b * t)) * Real.exp (b * t) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (-(Real.exp (-(b * t)))) * h + (-(w t)) * hinv

/-- Cochrane (2023), A1 §1.12, p. 580: **the backward solution, characterised.** For continuous
`z`, a path `y` is continuous on `[0, ∞)` with `y' = −b y + z` on `(0, ∞)` iff
`y_t = C e^{−bt} + ∫_0^t e^{−bτ} z_{t−τ} dτ` on `[0, ∞)`, with `C = y_0`. -/
theorem ode_backward {b : ℝ} {y z : ℝ → ℝ} (hz : Continuous z) :
    (ContinuousOn y (Set.Ici 0) ∧ ∀ τ, 0 < τ → HasDerivAt y (-b * y τ + z τ) τ) ↔
      ∀ t, 0 ≤ t → y t = Real.exp (-(b * t)) * y 0 + bwdInt b z t := by
  constructor
  · rintro ⟨hc, hd⟩ t ht
    have hw := decay_unique (b := b) (w := fun u => y u - bwdInt b z u)
      (hc.sub (bwdInt_continuous hz).continuousOn)
      (fun τ hτ => ((hd τ hτ).sub (bwdInt_hasDerivAt hz τ)).congr_deriv (by ring)) t ht
    simp only [bwdInt_zero, sub_zero] at hw
    linarith
  · intro h
    set Y : ℝ → ℝ := fun u => Real.exp (-(b * u)) * y 0 + bwdInt b z u with hY
    have hYc : Continuous Y := by
      have := bwdInt_continuous (b := b) hz
      fun_prop
    have hYd : ∀ τ, HasDerivAt Y (-b * Y τ + z τ) τ := fun τ =>
      (((hasDerivAt_expNeg b τ).mul_const (y 0)).add (bwdInt_hasDerivAt hz τ)).congr_deriv
        (by simp only [hY]; ring)
    refine ⟨hYc.continuousOn.congr fun t ht => h t ht, fun τ hτ => ?_⟩
    have hev : Y =ᶠ[𝓝 τ] y := by
      filter_upwards [Ioi_mem_nhds hτ] with u hu
      exact (h u (le_of_lt hu)).symm
    rw [h τ hτ.le]
    exact (hYd τ).congr_of_eventuallyEq hev.symm

/-! ## The roots `λ₁`, `λ₂` (p. 165, A1 §1.12) -/

/-- Cochrane (2023), §5.7.1, p. 165: the unstable root `λ₁ = (ρ + √(ρ² + 4κσ))/2`. -/
noncomputable def lam1 (ρ κ σ : ℝ) : ℝ := (ρ + Real.sqrt (ρ ^ 2 + 4 * κ * σ)) / 2

/-- Cochrane (2023), §5.7.1, p. 165: the (negative of the) stable root
`λ₂ = (−ρ + √(ρ² + 4κσ))/2`. -/
noncomputable def lam2 (ρ κ σ : ℝ) : ℝ := (-ρ + Real.sqrt (ρ ^ 2 + 4 * κ * σ)) / 2

/-- Cochrane (2023), §5.7.1, p. 165: for `κ, σ > 0`, `|ρ| < √(ρ² + 4κσ)`. -/
theorem abs_lt_sqrt_disc {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    |ρ| < Real.sqrt (ρ ^ 2 + 4 * κ * σ) := by
  rw [Real.lt_sqrt (abs_nonneg ρ), sq_abs]
  nlinarith [mul_pos hκ hσ]

/-- Cochrane (2023), §5.7.1, p. 165: `λ₁ > 0` (for every `ρ`, given `κ, σ > 0`). -/
theorem lam1_pos {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) : 0 < lam1 ρ κ σ := by
  have h1 := abs_lt_sqrt_disc (ρ := ρ) hκ hσ
  have h2 := neg_abs_le ρ
  unfold lam1
  linarith

/-- Cochrane (2023), §5.7.1, p. 165: `λ₂ > 0` (for every `ρ`, given `κ, σ > 0`). -/
theorem lam2_pos {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) : 0 < lam2 ρ κ σ := by
  have h1 := abs_lt_sqrt_disc (ρ := ρ) hκ hσ
  have h2 := le_abs_self ρ
  unfold lam2
  linarith

/-- Cochrane (2023), A1 §1.12, p. 579: `λ₁ λ₂ = κσ`. -/
theorem lam_mul {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) : lam1 ρ κ σ * lam2 ρ κ σ = κ * σ := by
  have h : Real.sqrt (ρ ^ 2 + 4 * κ * σ) ^ 2 = ρ ^ 2 + 4 * κ * σ :=
    Real.sq_sqrt (by nlinarith [mul_pos hκ hσ, sq_nonneg ρ])
  unfold lam1 lam2
  linear_combination h / 4

/-- Cochrane (2023), A1 §1.12, p. 579: `λ₁ − λ₂ = ρ`. -/
theorem lam_sub (ρ κ σ : ℝ) : lam1 ρ κ σ - lam2 ρ κ σ = ρ := by
  unfold lam1 lam2
  ring

/-- Cochrane (2023), A1 §1.12, p. 579: `λ₁` is a root of `D² − ρD − κσ`: `λ₁² = ρλ₁ + κσ`. -/
theorem lam1_root {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    lam1 ρ κ σ ^ 2 = ρ * lam1 ρ κ σ + κ * σ := by
  linear_combination lam_mul (ρ := ρ) hκ hσ + lam1 ρ κ σ * lam_sub ρ κ σ

/-- Cochrane (2023), A1 §1.12, p. 579: `−λ₂` is a root of `D² − ρD − κσ`: `λ₂² + ρλ₂ = κσ`. -/
theorem lam2_root {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    lam2 ρ κ σ ^ 2 + ρ * lam2 ρ κ σ = κ * σ := by
  linear_combination lam_mul (ρ := ρ) hκ hσ - lam2 ρ κ σ * lam_sub ρ κ σ

/-- Cochrane (2023), A1 §1.12, p. 579: the factorisation
`(D − λ₁)(D + λ₂) = D² − ρD − κσ` of the characteristic polynomial. -/
theorem charpoly_factor {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (z : ℝ) :
    (z - lam1 ρ κ σ) * (z + lam2 ρ κ σ) = z ^ 2 - ρ * z - κ * σ := by
  linear_combination (-z) * lam_sub ρ κ σ - lam_mul (ρ := ρ) hκ hσ

/-- Cochrane (2023), (5.94), p. 164: the weight `W = (1/λ₂ + 1/λ₁)⁻¹` on the two-sided moving
average. -/
noncomputable def piWeight (ρ κ σ : ℝ) : ℝ := (1 / lam2 ρ κ σ + 1 / lam1 ρ κ σ)⁻¹

/-- Cochrane (2023), A1 §1.12, p. 580: `W > 0`. -/
theorem piWeight_pos {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) : 0 < piWeight ρ κ σ := by
  have h1 := lam1_pos (ρ := ρ) hκ hσ
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  unfold piWeight
  positivity

/-- Cochrane (2023), A1 §1.12, p. 580: `W (1/λ₂ + 1/λ₁) = 1`. -/
theorem piWeight_mul_inv {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    piWeight ρ κ σ * (1 / lam2 ρ κ σ + 1 / lam1 ρ κ σ) = 1 := by
  have h1 := lam1_pos (ρ := ρ) hκ hσ
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  unfold piWeight
  exact inv_mul_cancel₀ (by positivity)

/-- Cochrane (2023), A1 §1.12, p. 580: `W (λ₁ + λ₂) = κσ`, i.e.
`(1/λ₂ + 1/λ₁)⁻¹ = κσ/(λ₁ + λ₂)`. -/
theorem piWeight_mul_add {ρ κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    piWeight ρ κ σ * (lam1 ρ κ σ + lam2 ρ κ σ) = κ * σ := by
  have h1 := lam1_pos (ρ := ρ) hκ hσ
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hW := piWeight_mul_inv (ρ := ρ) hκ hσ
  have hm := lam_mul (ρ := ρ) hκ hσ
  have e : lam1 ρ κ σ + lam2 ρ κ σ =
      (1 / lam2 ρ κ σ + 1 / lam1 ρ κ σ) * (lam1 ρ κ σ * lam2 ρ κ σ) := by
    field_simp
  rw [e, ← mul_assoc, hW, one_mul, hm]

/-! ## The model (5.91)–(5.92) -/

/-- Cochrane (2023), (5.91)–(5.92), p. 164: `(x, π)` solves the perfect-foresight IS curve
`dx/dt = σ(i − π)` and Phillips curve `dπ/dt = ρπ − κx` on `(0, ∞)` after the time-`0` news,
with both paths continuous on `[0, ∞)` (their time-`0` values are the right limits). -/
def IsCTSolution (σ κ ρ : ℝ) (i x π : ℝ → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧ ContinuousOn π (Set.Ici 0) ∧
    ∀ t, 0 < t → HasDerivAt x (σ * (i t - π t)) t ∧ HasDerivAt π (ρ * π t - κ * x t) t

/-- Cochrane (2023), §5.7.1, p. 165 ("stable solutions"): a path bounded on `[0, ∞)`. -/
def BddOnIci (f : ℝ → ℝ) : Prop := ∃ K, ∀ t, 0 ≤ t → |f t| ≤ K

/-- Cochrane (2023), A1 §1.12, p. 579: **the second-order equation.** Along a solution of
(5.91)–(5.92), `π` is twice differentiable on `(0, ∞)` with
`d²π/dt² − ρ dπ/dt − κσπ = −κσ i`. -/
theorem second_order {σ κ ρ t : ℝ} {i x π : ℝ → ℝ} (h : IsCTSolution σ κ ρ i x π)
    (ht : 0 < t) :
    ∃ π2, HasDerivAt (deriv π) π2 t ∧ π2 - ρ * deriv π t - κ * σ * π t = -(κ * σ) * i t := by
  have hev : (fun u => ρ * π u - κ * x u) =ᶠ[𝓝 t] deriv π := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact ((h.2.2 u hu).2.deriv).symm
  have hd := ((h.2.2 t ht).2.const_mul ρ).sub ((h.2.2 t ht).1.const_mul κ)
  refine ⟨_, hd.congr_of_eventuallyEq hev.symm, ?_⟩
  rw [(h.2.2 t ht).2.deriv]
  ring

/-- Cochrane (2023), A1 §1.12, p. 579: **the factorisation in the time domain.** Along a
solution, `y = λ₁π − κx` (which equals `dπ/dt + λ₂π`) satisfies `(D − λ₁) y = −κσ i`. -/
theorem factor_y {σ κ ρ t : ℝ} {i x π : ℝ → ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (h : IsCTSolution σ κ ρ i x π) (ht : 0 < t) :
    HasDerivAt (fun u => lam1 ρ κ σ * π u - κ * x u)
        (lam1 ρ κ σ * (lam1 ρ κ σ * π t - κ * x t) + -(κ * σ) * i t) t ∧
      ρ * π t - κ * x t + lam2 ρ κ σ * π t = lam1 ρ κ σ * π t - κ * x t := by
  refine ⟨(((h.2.2 t ht).2.const_mul (lam1 ρ κ σ)).sub
    ((h.2.2 t ht).1.const_mul κ)).congr_deriv ?_, ?_⟩
  · linear_combination (-(π t)) * lam1_root (ρ := ρ) hκ hσ
  · linear_combination (-(π t)) * lam_sub ρ κ σ

/-- Cochrane (2023), §5.7, p. 163: **the integrated IS curve.** Along a solution, if output
converges to its steady state (`x_T → 0`) and `i − π` is integrable on `(t, ∞)`, then
`x_t = −σ ∫_0^∞ (i_{t+τ} − π_{t+τ}) dτ`. -/
theorem ct_is_integral {σ κ ρ t : ℝ} {i x π : ℝ → ℝ} (h : IsCTSolution σ κ ρ i x π)
    (ht : 0 ≤ t) (hx : Tendsto x atTop (𝓝 0))
    (hint : IntegrableOn (fun τ => i τ - π τ) (Set.Ioi t)) :
    x t = -σ * ∫ τ in Set.Ioi 0, (i (t + τ) - π (t + τ)) := by
  have hl := tendsto_of_deriv_Ioi (G := x) (g := fun τ => σ * (i τ - π τ))
    (h.1.mono (Set.Ici_subset_Ici.2 ht)) (fun τ hτ => (h.2.2 τ (by linarith)).1)
    (hint.const_mul σ)
  have hu := tendsto_nhds_unique hl hx
  rw [integral_const_mul] at hu
  have hs := integral_Ioi_shift (fun τ => i τ - π τ) t
  rw [hs]
  linarith

/-- Cochrane (2023), §5.7, p. 163: **the integrated Phillips curve.** For `ρ > 0`, along a
solution with `x` and `π` bounded on `[0, ∞)`, `π_t = κ ∫_0^∞ e^{−ρτ} x_{t+τ} dτ`. -/
theorem ct_pc_integral {σ κ ρ t Kπ Kx : ℝ} {i x π : ℝ → ℝ} (h : IsCTSolution σ κ ρ i x π)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hπ : ∀ s, 0 ≤ s → |π s| ≤ Kπ) (hx : ∀ s, 0 ≤ s → |x s| ≤ Kx) :
    π t = κ * ∫ τ in Set.Ioi 0, Real.exp (-(ρ * τ)) * x (t + τ) := by
  have hm : AEStronglyMeasurable (fun τ => κ * x τ) (volume.restrict (Set.Ioi t)) :=
    ((continuousOn_const.mul h.1).mono fun s (hs : t < s) =>
      (show (0 : ℝ) ≤ s by linarith : s ∈ Set.Ici (0 : ℝ))).aestronglyMeasurable
      measurableSet_Ioi
  have hint := integrableOn_exp_mul_of_bdd (M := |κ| * Kx) hρ hm fun τ hτ => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hx τ (by linarith)) (abs_nonneg κ)
  have hv := (tvc_iff_forward (f := fun τ => κ * x τ) (h.2.1.mono (Set.Ici_subset_Ici.2 ht))
    (fun τ hτ => (h.2.2 τ (by linarith)).2) hint).1
    (tvc_of_bounded hρ fun T hT => hπ T (by linarith))
  rw [hv, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  ring

/-! ## (5.94): the family of bounded solutions -/

/-- Cochrane (2023), (5.94), p. 164: the family
`π_t = C₀ e^{−λ₂t} + (1/λ₂ + 1/λ₁)⁻¹ [∫_0^t e^{−λ₂τ} i_{t−τ} dτ + ∫_0^∞ e^{−λ₁τ} i_{t+τ} dτ]`. -/
noncomputable def piFamily (ρ κ σ : ℝ) (i : ℝ → ℝ) (C t : ℝ) : ℝ :=
  C * Real.exp (-(lam2 ρ κ σ * t)) +
    piWeight ρ κ σ * (bwdInt (lam2 ρ κ σ) i t + fwdInt (lam1 ρ κ σ) i t)

/-- Cochrane (2023), (5.94), p. 164: for a globally bounded continuous `i`, every member of the
family has `dπ/dt = −λ₂π + κσ ∫_0^∞ e^{−λ₁τ} i_{t+τ} dτ`. -/
theorem piFamily_hasDerivAt {ρ κ σ M C : ℝ} {i : ℝ → ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (hi : Continuous i) (hM : ∀ s, |i s| ≤ M) (t : ℝ) :
    HasDerivAt (piFamily ρ κ σ i C)
      (-lam2 ρ κ σ * piFamily ρ κ σ i C t + κ * σ * fwdInt (lam1 ρ κ σ) i t) t := by
  have h1 := lam1_pos (ρ := ρ) hκ hσ
  have hW := piWeight_mul_add (ρ := ρ) hκ hσ
  have hd := ((hasDerivAt_expNeg (lam2 ρ κ σ) t).const_mul C).add
    (((bwdInt_hasDerivAt (b := lam2 ρ κ σ) hi t).add
      (fwdInt_hasDerivAt h1 hi hM t)).const_mul (piWeight ρ κ σ))
  refine hd.congr_deriv ?_
  simp only [piFamily]
  linear_combination (fwdInt (lam1 ρ κ σ) i t) * hW

/-- Cochrane (2023), (5.94), p. 164: the family is continuous (globally bounded continuous
`i`). -/
theorem piFamily_continuous {ρ κ σ M C : ℝ} {i : ℝ → ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (hi : Continuous i) (hM : ∀ s, |i s| ≤ M) : Continuous (piFamily ρ κ σ i C) :=
  continuous_iff_continuousAt.2 fun t =>
    (piFamily_hasDerivAt (C := C) (ρ := ρ) hκ hσ hi hM t).continuousAt

/-- Cochrane (2023), (5.94), p. 164: at `t = 0`, `π_0 = C₀ + W ∫_0^∞ e^{−λ₁τ} i_τ dτ`. -/
theorem piFamily_zero (ρ κ σ : ℝ) (i : ℝ → ℝ) (C : ℝ) :
    piFamily ρ κ σ i C 0 = C + piWeight ρ κ σ * fwdInt (lam1 ρ κ σ) i 0 := by
  simp [piFamily, bwdInt_zero]

/-- Cochrane (2023), (5.94), p. 164: the family is bounded on `[0, ∞)`:
`|π_t| ≤ |C₀| + W (M/λ₂ + M/λ₁)` when `|i| ≤ M` on `[0, ∞)`. -/
theorem piFamily_abs_le {ρ κ σ M C t : ℝ} {i : ℝ → ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (hM : ∀ s, 0 ≤ s → |i s| ≤ M) (ht : 0 ≤ t) :
    |piFamily ρ κ σ i C t| ≤
      |C| + piWeight ρ κ σ * (M / lam2 ρ κ σ + M / lam1 ρ κ σ) := by
  have hW := piWeight_pos (ρ := ρ) hκ hσ
  have hB := bwdInt_abs_le (z := i) (lam2_pos (ρ := ρ) hκ hσ) ht fun s hs _ => hM s hs
  have hF := fwdInt_abs_le (z := i) (t := t) (lam1_pos (ρ := ρ) hκ hσ)
    fun s hs => hM s (le_trans ht hs)
  have he : |C * Real.exp (-(lam2 ρ κ σ * t))| ≤ |C| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_of_le_one_right (abs_nonneg C) ?_
    rw [Real.exp_le_one_iff]
    nlinarith [lam2_pos (ρ := ρ) hκ hσ]
  have hG : |piWeight ρ κ σ * (bwdInt (lam2 ρ κ σ) i t + fwdInt (lam1 ρ κ σ) i t)| ≤
      piWeight ρ κ σ * (M / lam2 ρ κ σ + M / lam1 ρ κ σ) := by
    rw [abs_mul, abs_of_pos hW]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hB hF)) hW.le
  exact (abs_add_le _ _).trans (add_le_add he hG)

/-- Cochrane (2023), (5.94), p. 164 (globally bounded continuous `i`): **the bounded solutions
of (5.91)–(5.92) are exactly the family (5.94).** `(x, π)` is a solution bounded on `[0, ∞)`
iff for some `C₀`, on `[0, ∞)`, `π` is given by (5.94) and `x = (λ₁π − κσ∫_0^∞ e^{−λ₁τ}
i_{t+τ} dτ)/κ` (equivalently `x = (ρπ − dπ/dt)/κ`, (5.92)). -/
theorem ct_family_global {ρ κ σ M : ℝ} {i x π : ℝ → ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (hi : Continuous i) (hM : ∀ s, |i s| ≤ M) :
    (IsCTSolution σ κ ρ i x π ∧ BddOnIci x ∧ BddOnIci π) ↔
      ∃ C, ∀ t, 0 ≤ t → π t = piFamily ρ κ σ i C t ∧
        x t = (lam1 ρ κ σ * π t - κ * σ * fwdInt (lam1 ρ κ σ) i t) / κ := by
  have h1 := lam1_pos (ρ := ρ) hκ hσ
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  set F := fwdInt (lam1 ρ κ σ) i with hFdef
  constructor
  · rintro ⟨⟨hxc, hπc, hd⟩, ⟨Kx, hKx⟩, ⟨Kπ, hKπ⟩⟩
    -- the forward step: `y = λ₁π − κx = κσ F`
    have hyF : ∀ t, 0 ≤ t → lam1 ρ κ σ * π t - κ * x t = κ * σ * F t := by
      intro t ht
      have hy := ode_forward_bounded (a := lam1 ρ κ σ) (z := fun u => -(κ * σ) * i u)
        (M := κ * σ * M) (K := lam1 ρ κ σ * Kπ + κ * Kx) (y := fun u =>
          lam1 ρ κ σ * π u - κ * x u) h1 (continuous_const.mul hi)
        (fun s => by
          rw [abs_mul, abs_neg, abs_of_pos (mul_pos hκ hσ)]
          exact mul_le_mul_of_nonneg_left (hM s) (mul_pos hκ hσ).le)
        ((continuousOn_const.mul hπc).sub (continuousOn_const.mul hxc))
        (fun τ hτ => (factor_y hκ hσ ⟨hxc, hπc, hd⟩ hτ).1)
        (fun τ hτ => by
          calc |lam1 ρ κ σ * π τ - κ * x τ| ≤ |lam1 ρ κ σ * π τ| + |κ * x τ| := abs_sub _ _
            _ = lam1 ρ κ σ * |π τ| + κ * |x τ| := by
              rw [abs_mul, abs_mul, abs_of_pos h1, abs_of_pos hκ]
            _ ≤ lam1 ρ κ σ * Kπ + κ * Kx := add_le_add
              (mul_le_mul_of_nonneg_left (hKπ τ hτ) h1.le)
              (mul_le_mul_of_nonneg_left (hKx τ hτ) hκ.le)) t ht
      rw [hy, fwdInt_const_mul]
      ring
    -- the backward step: `π − P₀` decays at rate `λ₂`
    have hw := decay_unique (b := lam2 ρ κ σ) (w := fun u => π u - piFamily ρ κ σ i 0 u)
      (hπc.sub (piFamily_continuous hκ hσ hi hM).continuousOn)
      (fun τ hτ => ((hd τ hτ).2.sub (piFamily_hasDerivAt hκ hσ hi hM τ)).congr_deriv (by
        linear_combination (-(π τ)) * lam_sub ρ κ σ + hyF τ hτ.le))
    refine ⟨π 0 - piWeight ρ κ σ * F 0, fun t ht => ⟨?_, ?_⟩⟩
    · have := hw t ht
      simp only [piFamily_zero] at this
      simp only [piFamily] at this ⊢
      rw [← hFdef] at this ⊢
      linarith
    · rw [eq_div_iff hκ.ne']
      linarith [hyF t ht]
  · rintro ⟨C, hC⟩
    set P := piFamily ρ κ σ i C with hP
    have hPc : Continuous P := piFamily_continuous hκ hσ hi hM
    have hFc : Continuous F := fwdInt_continuous h1 hi hM
    set X : ℝ → ℝ := fun u => (lam1 ρ κ σ * P u - κ * σ * F u) / κ with hX
    have hXc : Continuous X := by
      simp only [hX]
      fun_prop
    have hπ : ∀ t, 0 ≤ t → π t = P t := fun t ht => (hC t ht).1
    have hx : ∀ t, 0 ≤ t → x t = X t := fun t ht => by rw [(hC t ht).2, hπ t ht]
    have hPd := fun τ => piFamily_hasDerivAt (C := C) (ρ := ρ) hκ hσ hi hM τ
    have hXd : ∀ τ, HasDerivAt X (σ * (i τ - P τ)) τ := by
      intro τ
      have := (((hPd τ).const_mul (lam1 ρ κ σ)).sub
        ((fwdInt_hasDerivAt h1 hi hM τ).const_mul (κ * σ))).div_const κ
      refine this.congr_deriv ?_
      rw [div_eq_iff hκ.ne']
      linear_combination (-(P τ)) * lam_mul (ρ := ρ) hκ hσ
    have hBP : ∀ t, 0 ≤ t → |P t| ≤
        |C| + piWeight ρ κ σ * (M / lam2 ρ κ σ + M / lam1 ρ κ σ) :=
      fun t ht => piFamily_abs_le hκ hσ (fun s _ => hM s) ht
    refine ⟨⟨hXc.continuousOn.congr fun t ht => hx t ht,
      hPc.continuousOn.congr fun t ht => hπ t ht, fun τ hτ => ⟨?_, ?_⟩⟩, ?_, ?_⟩
    · have hev : x =ᶠ[𝓝 τ] X := by
        filter_upwards [Ioi_mem_nhds hτ] with u hu
        exact hx u hu.le
      rw [hπ τ hτ.le]
      exact (hXd τ).congr_of_eventuallyEq hev
    · have hev : π =ᶠ[𝓝 τ] P := by
        filter_upwards [Ioi_mem_nhds hτ] with u hu
        exact hπ u hu.le
      rw [hπ τ hτ.le, hx τ hτ.le]
      refine (hPd τ).congr_of_eventuallyEq hev |>.congr_deriv ?_
      simp only [hX]
      rw [mul_div_cancel₀ _ hκ.ne']
      linear_combination (P τ) * lam_sub ρ κ σ
    · refine ⟨(lam1 ρ κ σ * (|C| + piWeight ρ κ σ * (M / lam2 ρ κ σ + M / lam1 ρ κ σ)) +
        κ * σ * (M / lam1 ρ κ σ)) / κ, fun t ht => ?_⟩
      rw [hx t ht, hX]
      simp only
      rw [abs_div, abs_of_pos hκ, div_le_div_iff_of_pos_right hκ]
      have hF' : |F t| ≤ M / lam1 ρ κ σ := fwdInt_abs_le h1 fun s _ => hM s
      calc |lam1 ρ κ σ * P t - κ * σ * F t| ≤ |lam1 ρ κ σ * P t| + |κ * σ * F t| :=
            abs_sub _ _
        _ = lam1 ρ κ σ * |P t| + κ * σ * |F t| := by
            rw [abs_mul, abs_mul, abs_of_pos h1, abs_of_pos (mul_pos hκ hσ)]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hBP t ht) h1.le)
            (mul_le_mul_of_nonneg_left hF' (mul_pos hκ hσ).le)
    · exact ⟨_, fun t ht => by rw [hπ t ht]; exact hBP t ht⟩

/-! ### Interest-rate paths that are only given on `[0, ∞)` -/

/-- Cochrane (2023), §5.7.1, p. 164 (only values after the news date matter): the extension
`t ↦ f(max t 0)` of a path given on `[0, ∞)` to the whole line. -/
noncomputable def ext0 (f : ℝ → ℝ) : ℝ → ℝ := fun t => f (max t 0)

/-- Cochrane (2023), §5.7.1, p. 164: the extension agrees with `f` on `[0, ∞)`. -/
theorem ext0_eq {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) : ext0 f t = f t := by
  simp [ext0, max_eq_left ht]

/-- Cochrane (2023), §5.7.1, p. 164: the extension of a path continuous on `[0, ∞)` is
continuous. -/
theorem ext0_continuous {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 0)) : Continuous (ext0 f) :=
  hf.comp_continuous (continuous_id.max continuous_const) fun t =>
    Set.mem_Ici.2 (le_max_right t 0)

/-- Cochrane (2023), §5.7.1, p. 164: the extension of a path bounded on `[0, ∞)` is bounded
by the same constant. -/
theorem ext0_abs_le {f : ℝ → ℝ} {M : ℝ} (hM : ∀ s, 0 ≤ s → |f s| ≤ M) (t : ℝ) :
    |ext0 f t| ≤ M :=
  hM _ (le_max_right t 0)

/-- Cochrane (2023), (5.91), p. 164: the solution concept depends only on `i` on `[0, ∞)`. -/
theorem isCTSolution_congr {σ κ ρ : ℝ} {i i' x π : ℝ → ℝ} (h : ∀ s, 0 ≤ s → i s = i' s) :
    IsCTSolution σ κ ρ i x π ↔ IsCTSolution σ κ ρ i' x π := by
  unfold IsCTSolution
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨h1, h2, fun t ht => ?_⟩
  · rw [← h t ht.le]; exact h3 t ht
  · rw [h t ht.le]; exact h3 t ht

/-- Cochrane (2023), (5.94), p. 164: on `[0, ∞)` the family depends only on `i` on `[0, ∞)`. -/
theorem piFamily_congr {ρ κ σ C t : ℝ} {i i' : ℝ → ℝ} (ht : 0 ≤ t)
    (h : ∀ s, 0 ≤ s → i s = i' s) : piFamily ρ κ σ i C t = piFamily ρ κ σ i' C t := by
  simp only [piFamily, bwdInt_congr ht h, fwdInt_congr ht h]

/-- Cochrane (2023), (5.94), pp. 164–165: **the bounded solutions of (5.91)–(5.92) are exactly
the family (5.94)**, for any interest-rate path `i` continuous and bounded on `[0, ∞)`:
`(x, π)` is a solution bounded on `[0, ∞)` iff for some `C₀`, on `[0, ∞)`,
`π_t = C₀e^{−λ₂t} + (1/λ₂ + 1/λ₁)⁻¹[∫_0^t e^{−λ₂τ}i_{t−τ}dτ + ∫_0^∞ e^{−λ₁τ}i_{t+τ}dτ]` and
`x_t = (λ₁π_t − κσ∫_0^∞ e^{−λ₁τ}i_{t+τ}dτ)/κ` (which is `(ρπ − dπ/dt)/κ`, (5.92)). -/
theorem ct_family {ρ κ σ M : ℝ} {i x π : ℝ → ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ s, 0 ≤ s → |i s| ≤ M) :
    (IsCTSolution σ κ ρ i x π ∧ BddOnIci x ∧ BddOnIci π) ↔
      ∃ C, ∀ t, 0 ≤ t → π t = piFamily ρ κ σ i C t ∧
        x t = (lam1 ρ κ σ * π t - κ * σ * fwdInt (lam1 ρ κ σ) i t) / κ := by
  have he : ∀ s, 0 ≤ s → i s = ext0 i s := fun s hs => (ext0_eq hs).symm
  rw [isCTSolution_congr he, ct_family_global hκ hσ (ext0_continuous hi) (ext0_abs_le hM)]
  constructor <;> rintro ⟨C, hC⟩ <;> refine ⟨C, fun t ht => ?_⟩
  · rw [piFamily_congr ht he, fwdInt_congr ht he]
    exact hC t ht
  · rw [← piFamily_congr ht he, ← fwdInt_congr ht he]
    exact hC t ht

/-- Cochrane (2023), (5.94), p. 165: **the family is indexed by initial inflation `π₀`**: two
bounded solutions with the same `π₀` coincide on `[0, ∞)`. -/
theorem ct_family_pinned_by_pi0 {ρ κ σ M : ℝ} {i x π x' π' : ℝ → ℝ} (hκ : 0 < κ)
    (hσ : 0 < σ) (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ s, 0 ≤ s → |i s| ≤ M)
    (h : IsCTSolution σ κ ρ i x π ∧ BddOnIci x ∧ BddOnIci π)
    (h' : IsCTSolution σ κ ρ i x' π' ∧ BddOnIci x' ∧ BddOnIci π') (h0 : π 0 = π' 0) :
    ∀ t, 0 ≤ t → π t = π' t ∧ x t = x' t := by
  obtain ⟨C, hC⟩ := (ct_family hκ hσ hi hM).1 h
  obtain ⟨C', hC'⟩ := (ct_family hκ hσ hi hM).1 h'
  have hCC : C = C' := by
    have a := (hC 0 le_rfl).1
    have b := (hC' 0 le_rfl).1
    rw [piFamily_zero] at a b
    linarith
  intro t ht
  have hp : π t = π' t := by rw [(hC t ht).1, (hC' t ht).1, hCC]
  exact ⟨hp, by rw [(hC t ht).2, (hC' t ht).2, hp]⟩

/-- Cochrane (2023), (5.94), p. 165: **every initial inflation is attained**: for each `π₀`
there is a bounded solution with `π(0) = π₀` (so the bounded solutions form a one-parameter
family, indexed by `C₀` or equivalently by `π₀`). -/
theorem ct_family_exists {ρ κ σ M : ℝ} {i : ℝ → ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ s, 0 ≤ s → |i s| ≤ M) (π0 : ℝ) :
    ∃ x π : ℝ → ℝ, (IsCTSolution σ κ ρ i x π ∧ BddOnIci x ∧ BddOnIci π) ∧ π 0 = π0 := by
  set C := π0 - piWeight ρ κ σ * fwdInt (lam1 ρ κ σ) i 0
  refine ⟨fun t => (lam1 ρ κ σ * piFamily ρ κ σ i C t -
    κ * σ * fwdInt (lam1 ρ κ σ) i t) / κ, fun t => piFamily ρ κ σ i C t,
    (ct_family hκ hσ hi hM).2 ⟨C, fun t _ => ⟨rfl, rfl⟩⟩, ?_⟩
  simp only [piFamily_zero, C]
  ring

/-! ## (5.95): the valuation equation -/

/-- Cochrane (2023), (5.93) and (5.95), p. 165, at any date `t ≥ 0`: along
`dv/dt = rv + i − π − s̃` on `(0, ∞)`, the transversality condition `e^{−rT}v_T → 0` holds iff
`v_t = ∫_0^∞ e^{−rτ}[s̃_{t+τ} − (i_{t+τ} − π_{t+τ})] dτ`. -/
theorem ct_value_at {r t : ℝ} {i π s v : ℝ → ℝ} (ht : 0 ≤ t) (hc : ContinuousOn v (Set.Ici 0))
    (hd : ∀ τ, 0 < τ → HasDerivAt v (r * v τ + i τ - π τ - s τ) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ - (i τ - π τ))) (Set.Ioi t)) :
    Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0) ↔
      v t = ∫ τ in Set.Ioi 0,
        Real.exp (-(r * τ)) * (s (t + τ) - (i (t + τ) - π (t + τ))) :=
  tvc_iff_forward (f := fun τ => s τ - (i τ - π τ)) (hc.mono (Set.Ici_subset_Ici.2 ht))
    (fun τ hτ => (hd τ (by linarith)).congr_deriv (by ring)) hint

/-- Cochrane (2023), (5.95), p. 165: **the linearised present-value formula**: along (5.93),
the transversality condition holds iff `v_0 = ∫_0^∞ e^{−rτ}[s̃_τ − (i_τ − π_τ)] dτ`. -/
theorem ct_value {r : ℝ} {i π s v : ℝ → ℝ} (hc : ContinuousOn v (Set.Ici 0))
    (hd : ∀ τ, 0 < τ → HasDerivAt v (r * v τ + i τ - π τ - s τ) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ - (i τ - π τ))) (Set.Ioi 0)) :
    Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0) ↔
      v 0 = ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s τ - (i τ - π τ)) := by
  have := ct_value_at le_rfl hc hd hint
  simpa only [zero_add] using this

/-- Cochrane (2023), p. 165, the flexible-price case: if `π = i` on `(0, ∞)` then the valuation
equation is `v_0 = ∫_0^∞ e^{−rτ} s̃_τ dτ`. -/
theorem ct_value_flexible {r : ℝ} {i π s v : ℝ → ℝ} (hc : ContinuousOn v (Set.Ici 0))
    (hd : ∀ τ, 0 < τ → HasDerivAt v (r * v τ + i τ - π τ - s τ) τ)
    (hπ : ∀ τ, 0 < τ → π τ = i τ)
    (hint : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi 0)) :
    Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0) ↔
      v 0 = ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ := by
  have heq : Set.EqOn (fun τ => Real.exp (-(r * τ)) * s τ)
      (fun τ => Real.exp (-(r * τ)) * (s τ - (i τ - π τ))) (Set.Ioi 0) := fun τ hτ => by
    simp only [hπ τ hτ, sub_self, sub_zero]
  rw [ct_value hc hd (hint.congr_fun heq measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Ioi heq]

/-- Cochrane (2023), p. 165: **with flexible prices the value of debt must jump**: if two
flexible-price paths (`π = i`), both satisfying the transversality condition, have different
present values of surpluses, their time-`0` values of debt differ; with `B₀` predetermined,
`P₀` in `V₀ = B₀/P₀` must jump. -/
theorem flexible_value_must_jump {r : ℝ} {i π s v i' π' s' v' : ℝ → ℝ}
    (hc : ContinuousOn v (Set.Ici 0))
    (hd : ∀ τ, 0 < τ → HasDerivAt v (r * v τ + i τ - π τ - s τ) τ)
    (hπ : ∀ τ, 0 < τ → π τ = i τ)
    (hint : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi 0))
    (htvc : Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0))
    (hc' : ContinuousOn v' (Set.Ici 0))
    (hd' : ∀ τ, 0 < τ → HasDerivAt v' (r * v' τ + i' τ - π' τ - s' τ) τ)
    (hπ' : ∀ τ, 0 < τ → π' τ = i' τ)
    (hint' : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s' τ) (Set.Ioi 0))
    (htvc' : Tendsto (fun T => Real.exp (-(r * T)) * v' T) atTop (𝓝 0))
    (hne : ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ ≠
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s' τ) : v 0 ≠ v' 0 := by
  rw [(ct_value_flexible hc hd hπ hint).1 htvc, (ct_value_flexible hc' hd' hπ' hint').1 htvc']
  exact hne

/-! ## Equilibrium: the valuation equation selects the member of the family -/

/-- Cochrane (2023), §5.7.1, pp. 164–166: an **equilibrium** after the time-`0` news with
predetermined (instantaneous) debt `v₀`: `(x, π)` is a bounded solution of (5.91)–(5.92), `v`
solves (5.93) on `(0, ∞)`, is continuous on `[0, ∞)` with `v(0) = v₀` (the price level does
not jump, so the real value of instantaneous debt is predetermined), and the transversality
condition `e^{−rT}v_T → 0` holds. -/
def IsCTEquilibrium (r σ κ ρ v0 : ℝ) (i s x π v : ℝ → ℝ) : Prop :=
  (IsCTSolution σ κ ρ i x π ∧ BddOnIci x ∧ BddOnIci π) ∧ ContinuousOn v (Set.Ici 0) ∧
    (∀ t, 0 < t → HasDerivAt v (r * v t + i t - π t - s t) t) ∧ v 0 = v0 ∧
      Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0)

/-- Cochrane (2023), §5.7.1, p. 165: a path continuous and bounded on `[0, ∞)`, discounted at
`a > 0`, is integrable on `(t, ∞)` for every `t ≥ 0`. -/
theorem integrableOn_of_contOn_bdd {g : ℝ → ℝ} {a t K : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    (hc : ContinuousOn g (Set.Ici 0)) (hb : ∀ s, 0 ≤ s → |g s| ≤ K) :
    IntegrableOn (fun τ => Real.exp (-(a * τ)) * g τ) (Set.Ioi t) :=
  integrableOn_exp_mul_of_bdd ha ((hc.mono fun s (hs : t < s) =>
    (show (0 : ℝ) ≤ s by linarith : s ∈ Set.Ici (0 : ℝ))).aestronglyMeasurable
      measurableSet_Ioi) fun τ hτ => hb τ (by linarith)

/-- Cochrane (2023), (5.94), p. 164: the forward integral of a path continuous and bounded on
`[0, ∞)` is continuous on `[0, ∞)`. -/
theorem fwdInt_continuousOn {a M : ℝ} {i : ℝ → ℝ} (ha : 0 < a)
    (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ s, 0 ≤ s → |i s| ≤ M) :
    ContinuousOn (fwdInt a i) (Set.Ici 0) :=
  (fwdInt_continuous ha (ext0_continuous hi) (ext0_abs_le hM)).continuousOn.congr
    fun _ ht => fwdInt_congr ht fun _ hs => (ext0_eq hs).symm

/-- Cochrane (2023), (5.94), p. 164: the backward integral of a path continuous on `[0, ∞)` is
continuous on `[0, ∞)`. -/
theorem bwdInt_continuousOn {b : ℝ} {i : ℝ → ℝ} (hi : ContinuousOn i (Set.Ici 0)) :
    ContinuousOn (bwdInt b i) (Set.Ici 0) :=
  (bwdInt_continuous (b := b) (ext0_continuous hi)).continuousOn.congr
    fun _ ht => bwdInt_congr ht fun _ hs => (ext0_eq hs).symm

/-- Cochrane (2023), (5.94)–(5.95), p. 165 ("we substitute (5.94) into (5.95)"): for `π` in the
family with constant `C₀`,
`∫_0^∞ e^{−rτ}[s̃ − (i − π)] = ∫_0^∞ e^{−rτ}(s̃ − i) + C₀/(r + λ₂) + W ∫_0^∞ e^{−rτ}G_τ`, where
`G` is the two-sided average in (5.94). -/
theorem value_of_family {r ρ κ σ C : ℝ} {i s π : ℝ → ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hσ : 0 < σ) (hπ : ∀ t, 0 ≤ t → π t = piFamily ρ κ σ i C t)
    (hA : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ - i τ)) (Set.Ioi 0))
    (hG : IntegrableOn (fun τ => Real.exp (-(r * τ)) *
      (bwdInt (lam2 ρ κ σ) i τ + fwdInt (lam1 ρ κ σ) i τ)) (Set.Ioi 0)) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s τ - (i τ - π τ)) =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s τ - i τ)) + C / (r + lam2 ρ κ σ) +
        piWeight ρ κ σ * ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
          (bwdInt (lam2 ρ κ σ) i τ + fwdInt (lam1 ρ κ σ) i τ) := by
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hE := integrableOn_exp_Ioi (a := r + lam2 ρ κ σ) (by linarith)
  have hsplit : Set.EqOn (fun τ => Real.exp (-(r * τ)) * (s τ - (i τ - π τ)))
      (fun τ => Real.exp (-(r * τ)) * (s τ - i τ) +
        (C * Real.exp (-((r + lam2 ρ κ σ) * τ)) + piWeight ρ κ σ * (Real.exp (-(r * τ)) *
          (bwdInt (lam2 ρ κ σ) i τ + fwdInt (lam1 ρ κ σ) i τ)))) (Set.Ioi 0) := by
    intro τ hτ
    have he : Real.exp (-((r + lam2 ρ κ σ) * τ)) =
        Real.exp (-(r * τ)) * Real.exp (-(lam2 ρ κ σ * τ)) := by
      rw [← Real.exp_add]; ring_nf
    simp only
    rw [hπ τ (le_of_lt hτ), he]
    simp only [piFamily]
    ring
  have i1 : IntegrableOn (fun τ => C * Real.exp (-((r + lam2 ρ κ σ) * τ))) (Set.Ioi 0) :=
    hE.const_mul C
  have i2 : IntegrableOn (fun τ => piWeight ρ κ σ * (Real.exp (-(r * τ)) *
      (bwdInt (lam2 ρ κ σ) i τ + fwdInt (lam1 ρ κ σ) i τ))) (Set.Ioi 0) :=
    hG.const_mul _
  have i12 : IntegrableOn (fun τ => C * Real.exp (-((r + lam2 ρ κ σ) * τ)) +
      piWeight ρ κ σ * (Real.exp (-(r * τ)) *
        (bwdInt (lam2 ρ κ σ) i τ + fwdInt (lam1 ρ κ σ) i τ))) (Set.Ioi 0) := i1.add i2
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_add hA i12, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_exp_Ioi (by linarith)]
  ring

/-- Cochrane (2023), (5.94)–(5.95), p. 165: **solving for `π₀`.** In any equilibrium (bounded
continuous `i`, `s̃` on `[0, ∞)`, `r > 0`),
`π₀ = (r + λ₂)(v₀ − ∫_0^∞ e^{−rτ}(s̃_τ − i_τ)dτ − W∫_0^∞ e^{−rτ}G_τ dτ) + W∫_0^∞ e^{−λ₁τ}i_τ dτ`. -/
theorem ct_equilibrium_pi0 {r σ κ ρ v0 M Ms : ℝ} {i s x π v : ℝ → ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hσ : 0 < σ) (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M)
    (hs : ContinuousOn s (Set.Ici 0)) (hMs : ∀ t, 0 ≤ t → |s t| ≤ Ms)
    (h : IsCTEquilibrium r σ κ ρ v0 i s x π v) :
    π 0 = (r + lam2 ρ κ σ) * (v0 - (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s τ - i τ)) -
      piWeight ρ κ σ * ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        (bwdInt (lam2 ρ κ σ) i τ + fwdInt (lam1 ρ κ σ) i τ)) +
      piWeight ρ κ σ * fwdInt (lam1 ρ κ σ) i 0 := by
  obtain ⟨hsol, hvc, hvd, hv0, htvc⟩ := h
  have h1 := lam1_pos (ρ := ρ) hκ hσ
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  obtain ⟨C, hC⟩ := (ct_family hκ hσ hi hM).1 hsol
  obtain ⟨Kπ, hKπ⟩ := hsol.2.2
  have hint : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ - (i τ - π τ))) (Set.Ioi 0) :=
    integrableOn_of_contOn_bdd (K := Ms + (M + Kπ)) hr le_rfl
      (hs.sub (hi.sub hsol.1.2.1)) fun t ht => by
        calc |s t - (i t - π t)| ≤ |s t| + (|i t| + |π t|) :=
              (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
          _ ≤ Ms + (M + Kπ) := add_le_add (hMs t ht) (add_le_add (hM t ht) (hKπ t ht))
  have hA : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ - i τ)) (Set.Ioi 0) :=
    integrableOn_of_contOn_bdd (K := Ms + M) hr le_rfl (hs.sub hi) fun t ht =>
      (abs_sub _ _).trans (add_le_add (hMs t ht) (hM t ht))
  have hG : IntegrableOn (fun τ => Real.exp (-(r * τ)) *
      (bwdInt (lam2 ρ κ σ) i τ + fwdInt (lam1 ρ κ σ) i τ)) (Set.Ioi 0) :=
    integrableOn_of_contOn_bdd (K := M / lam2 ρ κ σ + M / lam1 ρ κ σ) hr le_rfl
      ((bwdInt_continuousOn hi).add (fwdInt_continuousOn h1 hi hM)) fun t ht =>
        (abs_add_le _ _).trans (add_le_add
          (bwdInt_abs_le h2 ht fun s hs _ => hM s hs)
          (fwdInt_abs_le h1 fun s hs => hM s (le_trans ht hs)))
  have hval := (ct_value hvc hvd hint).1 htvc
  rw [value_of_family hr hκ hσ (fun t ht => (hC t ht).1) hA hG, hv0] at hval
  have hπ0 := (hC 0 le_rfl).1
  rw [piFamily_zero] at hπ0
  rw [hπ0, hval]
  field_simp
  ring

/-- Cochrane (2023), §5.7.1, pp. 164–166: **existence and uniqueness of equilibrium.** For
`r > 0`, `κ, σ > 0`, interest-rate and surplus paths continuous and bounded on `[0, ∞)`, and any
predetermined value of debt `v₀`, there is an equilibrium, and any two equilibria coincide on
`[0, ∞)`. The valuation equation (5.95), not a price-level jump, selects the member of the
family (5.94). -/
theorem ct_equilibrium_exists_unique {r σ κ ρ v0 M Ms : ℝ} {i s : ℝ → ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hσ : 0 < σ) (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M)
    (hs : ContinuousOn s (Set.Ici 0)) (hMs : ∀ t, 0 ≤ t → |s t| ≤ Ms) :
    (∃ x π v : ℝ → ℝ, IsCTEquilibrium r σ κ ρ v0 i s x π v) ∧
      ∀ x π v x' π' v' : ℝ → ℝ, IsCTEquilibrium r σ κ ρ v0 i s x π v →
        IsCTEquilibrium r σ κ ρ v0 i s x' π' v' →
          ∀ t, 0 ≤ t → x t = x' t ∧ π t = π' t ∧ v t = v' t := by
  have h1 := lam1_pos (ρ := ρ) hκ hσ
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hA : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ - i τ)) (Set.Ioi 0) :=
    integrableOn_of_contOn_bdd (K := Ms + M) hr le_rfl (hs.sub hi) fun t ht =>
      (abs_sub _ _).trans (add_le_add (hMs t ht) (hM t ht))
  have hG : IntegrableOn (fun τ => Real.exp (-(r * τ)) *
      (bwdInt (lam2 ρ κ σ) i τ + fwdInt (lam1 ρ κ σ) i τ)) (Set.Ioi 0) :=
    integrableOn_of_contOn_bdd (K := M / lam2 ρ κ σ + M / lam1 ρ κ σ) hr le_rfl
      ((bwdInt_continuousOn hi).add (fwdInt_continuousOn h1 hi hM)) fun t ht =>
        (abs_add_le _ _).trans (add_le_add
          (bwdInt_abs_le h2 ht fun s hs _ => hM s hs)
          (fwdInt_abs_le h1 fun s hs => hM s (le_trans ht hs)))
  refine ⟨?_, ?_⟩
  · -- existence
    set A := ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s τ - i τ)
    set J := ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
      (bwdInt (lam2 ρ κ σ) i τ + fwdInt (lam1 ρ κ σ) i τ)
    set C := (r + lam2 ρ κ σ) * (v0 - A - piWeight ρ κ σ * J)
    set π : ℝ → ℝ := fun t => piFamily ρ κ σ i C t with hπdef
    set x : ℝ → ℝ := fun t => (lam1 ρ κ σ * π t - κ * σ * fwdInt (lam1 ρ κ σ) i t) / κ
    have hsol : IsCTSolution σ κ ρ i x π ∧ BddOnIci x ∧ BddOnIci π :=
      (ct_family hκ hσ hi hM).2 ⟨C, fun t _ => ⟨rfl, rfl⟩⟩
    obtain ⟨Kπ, hKπ⟩ := hsol.2.2
    set f : ℝ → ℝ := fun t => s t - (i t - π t) with hfdef
    have hfc : ContinuousOn f (Set.Ici 0) := hs.sub (hi.sub hsol.1.2.1)
    have hfb : ∀ t, 0 ≤ t → |f t| ≤ Ms + (M + Kπ) := fun t ht => by
      calc |s t - (i t - π t)| ≤ |s t| + (|i t| + |π t|) :=
            (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
        _ ≤ Ms + (M + Kπ) := add_le_add (hMs t ht) (add_le_add (hM t ht) (hKπ t ht))
    have hfe := ext0_continuous hfc
    have hfeb := ext0_abs_le hfb
    refine ⟨x, π, fwdInt r (ext0 f), hsol, (fwdInt_continuous hr hfe hfeb).continuousOn,
      fun t ht => (fwdInt_hasDerivAt hr hfe hfeb t).congr_deriv ?_, ?_,
      tvc_of_bounded (t := 0) hr fun T _ => fwdInt_abs_le hr fun u _ => hfeb u⟩
    · rw [ext0_eq ht.le, hfdef]
      ring
    · have hv : fwdInt r (ext0 f) 0 = ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * f τ := by
        refine setIntegral_congr_fun measurableSet_Ioi fun τ (hτ : (0 : ℝ) < τ) => ?_
        simp only [zero_add, ext0_eq hτ.le]
      rw [hv, hfdef, value_of_family hr hκ hσ (fun t _ => rfl) hA hG]
      simp only [C]
      field_simp
      ring
  · -- uniqueness
    intro x π v x' π' v' e e' t ht
    have p0 := ct_equilibrium_pi0 hr hκ hσ hi hM hs hMs e
    have p0' := ct_equilibrium_pi0 hr hκ hσ hi hM hs hMs e'
    have hpin := ct_family_pinned_by_pi0 hκ hσ hi hM e.1 e'.1 (by rw [p0, p0'])
    refine ⟨(hpin t ht).2, (hpin t ht).1, ?_⟩
    obtain ⟨Kπ, hKπ⟩ := e.1.2.2
    obtain ⟨Kπ', hKπ'⟩ := e'.1.2.2
    have hint : ∀ (p : ℝ → ℝ) (K : ℝ), ContinuousOn p (Set.Ici 0) →
        (∀ u, 0 ≤ u → |p u| ≤ K) →
        IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ - (i τ - p τ))) (Set.Ioi t) :=
      fun p K hp hK => integrableOn_of_contOn_bdd (K := Ms + (M + K)) hr ht
        (hs.sub (hi.sub hp)) fun u hu => by
          calc |s u - (i u - p u)| ≤ |s u| + (|i u| + |p u|) :=
                (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
            _ ≤ Ms + (M + K) := add_le_add (hMs u hu) (add_le_add (hM u hu) (hK u hu))
    rw [(ct_value_at ht e.2.1 e.2.2.1 (hint π Kπ e.1.1.2.1 hKπ)).1 e.2.2.2.2,
      (ct_value_at ht e'.2.1 e'.2.2.1 (hint π' Kπ' e'.1.1.2.1 hKπ')).1 e'.2.2.2.2]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ (hτ : (0 : ℝ) < τ) => ?_
    simp only [(hpin (t + τ) (by linarith)).1]

/-! ## The step example and (5.96) (p. 166) -/

/-- Cochrane (2023), p. 166: `∫_0^∞ e^{−rτ}(c + D e^{−lτ}) dτ = c/r + D/(r + l)` (with
integrability), for `r, l > 0`. -/
theorem integral_exp_two {r l c D : ℝ} (hr : 0 < r) (hl : 0 < l) :
    IntegrableOn (fun τ => Real.exp (-(r * τ)) * (c + D * Real.exp (-(l * τ)))) (Set.Ioi 0) ∧
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (c + D * Real.exp (-(l * τ))) =
        c / r + D / (r + l) := by
  have he : (fun τ => Real.exp (-(r * τ)) * (c + D * Real.exp (-(l * τ)))) =
      fun τ => c * Real.exp (-(r * τ)) + D * Real.exp (-((r + l) * τ)) := by
    funext τ
    have : Real.exp (-((r + l) * τ)) = Real.exp (-(r * τ)) * Real.exp (-(l * τ)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    ring
  have i1 : IntegrableOn (fun τ => c * Real.exp (-(r * τ))) (Set.Ioi 0) :=
    (integrableOn_exp_Ioi hr).const_mul c
  have i2 : IntegrableOn (fun τ => D * Real.exp (-((r + l) * τ))) (Set.Ioi 0) :=
    (integrableOn_exp_Ioi (by linarith)).const_mul D
  rw [he]
  refine ⟨i1.add i2, ?_⟩
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul, integral_exp_Ioi hr,
    integral_exp_Ioi (by linarith)]
  ring

/-- Cochrane (2023), p. 166: **with a constant interest rate `i₀` the family (5.94) is
`π_t = (π₀ − i₀)e^{−λ₂t} + i₀`**, and then `x_t = (λ₁(π₀ − i₀)e^{−λ₂t} + ρi₀)/κ`. -/
theorem ct_step_family {ρ κ σ i0 : ℝ} {x π : ℝ → ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (h : IsCTSolution σ κ ρ (fun _ => i0) x π ∧ BddOnIci x ∧ BddOnIci π) (t : ℝ)
    (ht : 0 ≤ t) :
    π t = (π 0 - i0) * Real.exp (-(lam2 ρ κ σ * t)) + i0 ∧
      x t = (lam1 ρ κ σ * (π 0 - i0) * Real.exp (-(lam2 ρ κ σ * t)) + ρ * i0) / κ := by
  have h1 := lam1_pos (ρ := ρ) hκ hσ
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hWi := piWeight_mul_inv (ρ := ρ) hκ hσ
  obtain ⟨C, hC⟩ := (ct_family_global (M := |i0|) hκ hσ continuous_const
    (fun _ => le_refl _)).1 h
  have hP : ∀ u, piFamily ρ κ σ (fun _ => i0) C u =
      (C - piWeight ρ κ σ * i0 / lam2 ρ κ σ) * Real.exp (-(lam2 ρ κ σ * u)) + i0 := by
    intro u
    simp only [piFamily, bwdInt_const h2.ne', fwdInt_const h1]
    linear_combination i0 * hWi
  have hπt : π t = (π 0 - i0) * Real.exp (-(lam2 ρ κ σ * t)) + i0 := by
    have a := (hC t ht).1
    have b := (hC 0 le_rfl).1
    rw [hP] at a b
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at b
    rw [a, b]
    ring
  refine ⟨hπt, ?_⟩
  have hk : κ * σ * (i0 / lam1 ρ κ σ) = lam2 ρ κ σ * i0 := by
    rw [← lam_mul (ρ := ρ) hκ hσ]
    field_simp
  rw [(hC t ht).2, fwdInt_const h1, hk, hπt]
  congr 1
  linear_combination i0 * lam_sub ρ κ σ

/-- Cochrane (2023), p. 166: **the valuation equation in the step example**: with constant
`i₀`, `s̃₀` and `r > 0`, every equilibrium has `v₀ = s̃₀/r + (π₀ − i₀)/(r + λ₂)`. -/
theorem ct_step_value {r σ κ ρ v0 i0 s0 : ℝ} {x π v : ℝ → ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hσ : 0 < σ) (h : IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v) :
    v0 = s0 / r + (π 0 - i0) / (r + lam2 ρ κ σ) := by
  obtain ⟨hsol, hvc, hvd, hv0, htvc⟩ := h
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  obtain ⟨hI, hval⟩ := integral_exp_two (c := s0) (D := π 0 - i0) hr h2
  have heq : Set.EqOn (fun τ => Real.exp (-(r * τ)) * (s0 + (π 0 - i0) *
      Real.exp (-(lam2 ρ κ σ * τ))))
      (fun τ => Real.exp (-(r * τ)) * (s0 - (i0 - π τ))) (Set.Ioi 0) := fun τ hτ => by
    simp only [(ct_step_family hκ hσ hsol τ (le_of_lt hτ)).1]
    ring
  have hv := (ct_value hvc hvd (hI.congr_fun heq measurableSet_Ioi)).1 htvc
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, hval, hv0] at hv
  exact hv

/-- Cochrane (2023), (5.96), p. 166: **the unique inflation path in the step example**:
`π_t = (r + λ₂)(v₀ − s̃₀/r) e^{−λ₂t} + i₀`. -/
theorem ct_step_solution {r σ κ ρ v0 i0 s0 : ℝ} {x π v : ℝ → ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hσ : 0 < σ) (h : IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v)
    (t : ℝ) (ht : 0 ≤ t) :
    π t = (r + lam2 ρ κ σ) * (v0 - s0 / r) * Real.exp (-(lam2 ρ κ σ * t)) + i0 := by
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hv := ct_step_value hr hκ hσ h
  have hD : π 0 - i0 = (r + lam2 ρ κ σ) * (v0 - s0 / r) := by
    rw [hv]
    field_simp
    ring
  rw [(ct_step_family hκ hσ h.1 t ht).1, hD]

/-- Cochrane (2023), p. 166: **the step-example equilibrium exists** (and, by
`ct_equilibrium_exists_unique`, is unique). -/
theorem ct_step_exists {r σ κ ρ v0 i0 s0 : ℝ} (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ) :
    ∃ x π v : ℝ → ℝ, IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v :=
  (ct_equilibrium_exists_unique (M := |i0|) (Ms := |s0|) hr hκ hσ continuousOn_const
    (fun _ _ => le_refl _) continuousOn_const (fun _ _ => le_refl _)).1

/-- Cochrane (2023), p. 166: **the value of debt in the step example**:
`v_t − s̃₀/r = (π_t − i₀)/(r + λ₂) = (v₀ − s̃₀/r) e^{−λ₂t}`: initially unchanged, it erodes to
the new steady state `s̃₀/r`. -/
theorem ct_step_debt {r σ κ ρ v0 i0 s0 : ℝ} {x π v : ℝ → ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hσ : 0 < σ) (h : IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v)
    (t : ℝ) (ht : 0 ≤ t) :
    v t - s0 / r = (π t - i0) / (r + lam2 ρ κ σ) ∧
      v t - s0 / r = (v0 - s0 / r) * Real.exp (-(lam2 ρ κ σ * t)) := by
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  set D := (r + lam2 ρ κ σ) * (v0 - s0 / r) with hD
  have hπ := fun u (hu : 0 ≤ u) => ct_step_solution hr hκ hσ h u hu
  obtain ⟨hsol, hvc, hvd, -, htvc⟩ := h
  obtain ⟨Kπ, hKπ⟩ := hsol.2.2
  have hint : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s0 - (i0 - π τ))) (Set.Ioi t) :=
    integrableOn_of_contOn_bdd (K := |s0| + (|i0| + Kπ)) hr ht
      (continuousOn_const.sub (continuousOn_const.sub hsol.1.2.1)) fun u hu => by
        calc |s0 - (i0 - π u)| ≤ |s0| + (|i0| + |π u|) :=
              (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
          _ ≤ |s0| + (|i0| + Kπ) := by linarith [hKπ u hu]
  have hv := (ct_value_at (i := fun _ => i0) (s := fun _ => s0) ht hvc hvd hint).1 htvc
  obtain ⟨-, hval⟩ := integral_exp_two (c := s0)
    (D := D * Real.exp (-(lam2 ρ κ σ * t))) hr h2
  have heq : Set.EqOn (fun τ => Real.exp (-(r * τ)) * (s0 - (i0 - π (t + τ))))
      (fun τ => Real.exp (-(r * τ)) * (s0 + D * Real.exp (-(lam2 ρ κ σ * t)) *
        Real.exp (-(lam2 ρ κ σ * τ)))) (Set.Ioi 0) := fun τ hτ => by
    have : Real.exp (-(lam2 ρ κ σ * (t + τ))) =
        Real.exp (-(lam2 ρ κ σ * t)) * Real.exp (-(lam2 ρ κ σ * τ)) := by
      rw [← Real.exp_add]; ring_nf
    simp only [hπ (t + τ) (by linarith [le_of_lt (show (0 : ℝ) < τ from hτ)]), this]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq, hval] at hv
  rw [hv, hπ t ht, hD]
  constructor <;> field_simp <;> ring

/-- Cochrane (2023), p. 166: **the Fisherian response.** With no fiscal shock (`s̃₀ = r v₀`)
inflation jumps immediately to the new interest rate and stays there: `π_t = i₀`. -/
theorem ct_fisherian {r σ κ ρ v0 i0 s0 : ℝ} {x π v : ℝ → ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hσ : 0 < σ) (h : IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v)
    (hs : s0 = r * v0) (t : ℝ) (ht : 0 ≤ t) : π t = i0 := by
  rw [ct_step_solution hr hκ hσ h t ht, hs, mul_div_cancel_left₀ _ hr.ne']
  ring

/-- Cochrane (2023), p. 166 and the bullet on p. 165: **a fiscal shock** (`s̃₀ < r v₀`, a decline
in surpluses) produces a transitory rise in inflation that melts away at rate `λ₂`: `π_t > i₀`,
strictly decreasing, `π_t → i₀`; the value of debt erodes strictly to `s̃₀/r`. -/
theorem ct_fiscal_shock {r σ κ ρ v0 i0 s0 : ℝ} {x π v : ℝ → ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hσ : 0 < σ) (h : IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v)
    (hs : s0 < r * v0) :
    (∀ t, 0 ≤ t → i0 < π t) ∧ StrictAntiOn π (Set.Ici 0) ∧ Tendsto π atTop (𝓝 i0) ∧
      StrictAntiOn v (Set.Ici 0) ∧ Tendsto v atTop (𝓝 (s0 / r)) := by
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hD : 0 < (r + lam2 ρ κ σ) * (v0 - s0 / r) := by
    have : s0 / r < v0 := by rw [div_lt_iff₀ hr]; linarith
    have : 0 < r + lam2 ρ κ σ := by linarith
    positivity
  have hπ := fun t (ht : 0 ≤ t) => ct_step_solution hr hκ hσ h t ht
  have hv := fun t (ht : 0 ≤ t) => (ct_step_debt hr hκ hσ h t ht).2
  have hdec : StrictAnti fun t => Real.exp (-(lam2 ρ κ σ * t)) := fun a b hab => by
    simp only
    rw [Real.exp_lt_exp]
    nlinarith
  have hlim : Tendsto (fun t => Real.exp (-(lam2 ρ κ σ * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop h2)
  have hD' : 0 < v0 - s0 / r := by
    have : 0 < r + lam2 ρ κ σ := by linarith
    exact pos_of_mul_pos_right hD this.le
  refine ⟨fun t ht => ?_, fun a ha b hb hab => ?_, ?_, fun a ha b hb hab => ?_, ?_⟩
  · rw [hπ t ht]
    have := Real.exp_pos (-(lam2 ρ κ σ * t))
    nlinarith
  · rw [hπ a ha, hπ b hb]
    have := hdec hab
    nlinarith
  · have := ((hlim.const_mul ((r + lam2 ρ κ σ) * (v0 - s0 / r))).add_const i0)
    rw [mul_zero, zero_add] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [hπ t ht]
  · have e1 := hv a ha
    have e2 := hv b hb
    have := hdec hab
    nlinarith
  · have := ((hlim.const_mul (v0 - s0 / r)).add_const (s0 / r))
    rw [mul_zero, zero_add] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    linarith [hv t ht]

/-- Cochrane (2023), pp. 165–167: **the price level in the step example**: `p_t = ∫_0^t π`
(`dp = π dt`, (5.87)) is
`p_t = i₀t + (r + λ₂)(v₀ − s̃₀/r)(1 − e^{−λ₂t})/λ₂` for `t ≥ 0`. -/
theorem ct_step_price {r σ κ ρ v0 i0 s0 : ℝ} {x π v : ℝ → ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hσ : 0 < σ) (h : IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ τ in (0 : ℝ)..t, π τ = i0 * t +
      (r + lam2 ρ κ σ) * (v0 - s0 / r) * (1 - Real.exp (-(lam2 ρ κ σ * t))) / lam2 ρ κ σ := by
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  set D := (r + lam2 ρ κ σ) * (v0 - s0 / r)
  have hc : ∫ τ in (0 : ℝ)..t, π τ =
      ∫ τ in (0 : ℝ)..t, (D * Real.exp (-(lam2 ρ κ σ * τ)) + i0) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le ht] at hτ
    exact ct_step_solution hr hκ hσ h τ hτ.1
  have hi1 : IntervalIntegrable (fun τ => D * Real.exp (-(lam2 ρ κ σ * τ))) volume 0 t :=
    (by fun_prop : Continuous fun τ : ℝ => D * Real.exp (-(lam2 ρ κ σ * τ))).intervalIntegrable
      0 t
  rw [hc, intervalIntegral.integral_add hi1 intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral_exp h2.ne',
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Cochrane (2023), pp. 165–167: **no price-level jump**: in the step example the price level
`p_t = ∫_0^t π` is continuous from the right at the news date, `p_t → p_0 = 0`. -/
theorem ct_no_price_jump {r σ κ ρ v0 i0 s0 : ℝ} {x π v : ℝ → ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hσ : 0 < σ) (h : IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v) :
    Tendsto (fun t => ∫ τ in (0 : ℝ)..t, π τ) (𝓝[≥] 0) (𝓝 0) := by
  set D := (r + lam2 ρ κ σ) * (v0 - s0 / r)
  have hcont : Continuous fun t : ℝ =>
      i0 * t + D * (1 - Real.exp (-(lam2 ρ κ σ * t))) / lam2 ρ κ σ := by fun_prop
  have h0 := hcont.tendsto 0
  simp only [mul_zero, neg_zero, Real.exp_zero, sub_self, zero_div, add_zero] at h0
  refine (tendsto_nhdsWithin_of_tendsto_nhds h0).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : (0 : ℝ) ≤ t)
  rw [ct_step_price hr hκ hσ h t ht]

/-- Cochrane (2023), p. 167: **cumulative inflation** in the step example,
`∫_0^∞ (π_t − i₀) dt = (r/λ₂ + 1)(v₀ − s̃₀/r)`. -/
theorem ct_cum_inflation {r σ κ ρ v0 i0 s0 : ℝ} {x π v : ℝ → ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hσ : 0 < σ) (h : IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v) :
    ∫ t in Set.Ioi 0, (π t - i0) = (r / lam2 ρ κ σ + 1) * (v0 - s0 / r) := by
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have heq : Set.EqOn (fun t => π t - i0) (fun t => (r + lam2 ρ κ σ) * (v0 - s0 / r) *
      Real.exp (-(lam2 ρ κ σ * t))) (Set.Ioi 0) := fun t ht => by
    simp only [ct_step_solution hr hκ hσ h t (le_of_lt ht)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul, integral_exp_Ioi h2]
  field_simp

/-! ## The frictionless limit `κ → ∞` (p. 167) -/

/-- Cochrane (2023), p. 167: `λ₂` is strictly increasing in `κ` (for `σ > 0`). -/
theorem lam2_strictMono {ρ σ κ κ' : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hκκ : κ < κ') :
    lam2 ρ κ σ < lam2 ρ κ' σ := by
  have : Real.sqrt (ρ ^ 2 + 4 * κ * σ) < Real.sqrt (ρ ^ 2 + 4 * κ' * σ) :=
    Real.sqrt_lt_sqrt (by nlinarith [sq_nonneg ρ, mul_pos hκ hσ]) (by nlinarith)
  unfold lam2
  linarith

/-- Cochrane (2023), p. 167: "as `κ → ∞`, `λ₂ → ∞`". -/
theorem lam2_tendsto_atTop {ρ σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun κ => lam2 ρ κ σ) atTop atTop := by
  have h1 : Tendsto (fun κ : ℝ => Real.sqrt (4 * σ * κ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
  have h2 : Tendsto (fun κ : ℝ => (-ρ + Real.sqrt (4 * σ * κ)) / 2) atTop atTop :=
    (tendsto_atTop_add_const_left _ (-ρ) h1).atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' _ ((eventually_ge_atTop 0).mono fun κ hκ => ?_) h2
  have : Real.sqrt (4 * σ * κ) ≤ Real.sqrt (ρ ^ 2 + 4 * κ * σ) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ρ])
  unfold lam2
  linarith

/-- Cochrane (2023), p. 167: **the frictionless limit of cumulative inflation**: for any family
of step-example equilibria indexed by `κ > 0`, `∫_0^∞ (π^κ_t − i₀) dt → v₀ − s̃₀/r` as `κ → ∞`,
exactly the price-level jump of the frictionless model. -/
theorem ct_frictionless_limit {r σ ρ v0 i0 s0 : ℝ} {X P V : ℝ → ℝ → ℝ} (hr : 0 < r)
    (hσ : 0 < σ) (h : ∀ κ, 0 < κ →
      IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) (X κ) (P κ) (V κ)) :
    Tendsto (fun κ => ∫ t in Set.Ioi 0, (P κ t - i0)) atTop (𝓝 (v0 - s0 / r)) := by
  have hl : Tendsto (fun κ => r / lam2 ρ κ σ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (lam2_tendsto_atTop hσ)
  have := (hl.add_const 1).mul_const (v0 - s0 / r)
  rw [zero_add, one_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  rw [ct_cum_inflation hr hκ hσ (h κ hκ)]

/-- Cochrane (2023), p. 167: **the price level approaches the frictionless jump smoothly**: for
every `t > 0`, `p^κ_t = ∫_0^t π^κ → i₀t + (v₀ − s̃₀/r)` as `κ → ∞`, while `p^κ_0 = 0` and `p^κ`
is continuous for every finite `κ` (`ct_no_price_jump`). -/
theorem ct_price_limit {r σ ρ v0 i0 s0 t : ℝ} {X P V : ℝ → ℝ → ℝ} (hr : 0 < r) (hσ : 0 < σ)
    (h : ∀ κ, 0 < κ →
      IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) (X κ) (P κ) (V κ))
    (ht : 0 < t) :
    Tendsto (fun κ => ∫ τ in (0 : ℝ)..t, P κ τ) atTop (𝓝 (i0 * t + (v0 - s0 / r))) := by
  have hL := lam2_tendsto_atTop (ρ := ρ) hσ
  have hl : Tendsto (fun κ => r / lam2 ρ κ σ) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hL
  have he : Tendsto (fun κ => Real.exp (-(lam2 ρ κ σ * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hL.atTop_mul_const ht)
  have := (((hl.add_const 1).mul_const (v0 - s0 / r)).mul
    (he.const_sub 1)).const_add (i0 * t)
  rw [zero_add, one_mul, sub_zero, mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  rw [ct_step_price hr hκ hσ (h κ hκ) t ht.le]
  have := lam2_pos (ρ := ρ) hκ hσ
  field_simp

/-! ## Figure 5.10: a permanent interest-rate rise with long-term debt (pp. 172–173) -/

/-- Cochrane (2023), (5.105) and Fig. 5.10, pp. 169, 172: with a permanent unit rise in the
interest rate, the bounded solution of the bond-price equation `dq/dt = (r + ω)q + i` is
`q_t = −1/(r + ω)` (a perpetuity, `ω = 0`, falls by `1/r`). -/
theorem fig510_bond_price {r ω K : ℝ} {q : ℝ → ℝ} (h : 0 < r + ω)
    (hc : ContinuousOn q (Set.Ici 0)) (hd : ∀ t, 0 < t → HasDerivAt q ((r + ω) * q t + 1) t)
    (hb : ∀ t, 0 ≤ t → |q t| ≤ K) (t : ℝ) (ht : 0 ≤ t) : q t = -1 / (r + ω) := by
  rw [ode_forward_bounded (z := fun _ => 1) (M := 1) h continuous_const (fun _ => by simp) hc hd
    hb t ht, fwdInt_const h]
  ring

/-- Cochrane (2023), Fig. 5.10, pp. 172–173 (`α = θ = 0`, surpluses unchanged, permanent unit
rise in `i`): with long-term debt the value of debt jumps with the bond price at `0`
(`v₀ = q₀`, the face value is predetermined and the price level does not jump), and then
`π₀ = 1 − (r + λ₂)/(r + ω)`, `π_t = 1 − (r + λ₂)/(r + ω) e^{−λ₂t}`, and the price level is
`p_t = t − (r + λ₂)(1 − e^{−λ₂t})/(λ₂(r + ω))` (`p_0 = 0`: no jump). -/
theorem fig510 {r ω σ κ ρ K : ℝ} {q x π v : ℝ → ℝ} (hr : 0 < r) (hω : 0 ≤ ω) (hκ : 0 < κ)
    (hσ : 0 < σ) (hc : ContinuousOn q (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt q ((r + ω) * q t + 1) t) (hb : ∀ t, 0 ≤ t → |q t| ≤ K)
    (h : IsCTEquilibrium r σ κ ρ (q 0) (fun _ => 1) (fun _ => 0) x π v) :
    π 0 = 1 - (r + lam2 ρ κ σ) / (r + ω) ∧
      (∀ t, 0 ≤ t → π t = 1 - (r + lam2 ρ κ σ) / (r + ω) * Real.exp (-(lam2 ρ κ σ * t))) ∧
      ∀ t, 0 ≤ t → ∫ τ in (0 : ℝ)..t, π τ =
        t - (r + lam2 ρ κ σ) * (1 - Real.exp (-(lam2 ρ κ σ * t))) / (lam2 ρ κ σ * (r + ω)) := by
  have hrw : 0 < r + ω := by linarith
  have hq0 := fig510_bond_price hrw hc hd hb 0 le_rfl
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hπ : ∀ t, 0 ≤ t → π t = 1 - (r + lam2 ρ κ σ) / (r + ω) *
      Real.exp (-(lam2 ρ κ σ * t)) := fun t ht => by
    rw [ct_step_solution hr hκ hσ h t ht, hq0]
    field_simp
    ring
  refine ⟨?_, hπ, fun t ht => ?_⟩
  · rw [hπ 0 le_rfl]
    simp
  · rw [ct_step_price hr hκ hσ h t ht, hq0]
    field_simp
    ring

/-- Cochrane (2023), Fig. 5.10 and p. 172: **"long-term debt means that higher nominal interest
rates can produce lower inflation"**: in the Fig. 5.10 equilibrium inflation falls on impact
iff `ω < λ₂` (always, for a perpetuity `ω = 0`), and in the long run inflation rises to the new
interest rate, `π_t → 1`. -/
theorem fig510_initial_disinflation {r ω σ κ ρ K : ℝ} {q x π v : ℝ → ℝ} (hr : 0 < r)
    (hω : 0 ≤ ω) (hκ : 0 < κ) (hσ : 0 < σ) (hc : ContinuousOn q (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt q ((r + ω) * q t + 1) t) (hb : ∀ t, 0 ≤ t → |q t| ≤ K)
    (h : IsCTEquilibrium r σ κ ρ (q 0) (fun _ => 1) (fun _ => 0) x π v) :
    (π 0 < 0 ↔ ω < lam2 ρ κ σ) ∧ Tendsto π atTop (𝓝 1) := by
  have hrw : 0 < r + ω := by linarith
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  obtain ⟨h0, hπ, -⟩ := fig510 hr hω hκ hσ hc hd hb h
  refine ⟨?_, ?_⟩
  · rw [h0, sub_neg, one_lt_div hrw]
    constructor <;> intro <;> linarith
  · have hlim : Tendsto (fun t => Real.exp (-(lam2 ρ κ σ * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop h2)
    have := (hlim.const_mul ((r + lam2 ρ κ σ) / (r + ω))).const_sub 1
    rw [mul_zero, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [hπ t ht]

/-- Cochrane (2023), Fig. 5.10 bottom panel, p. 173: **the smooth frictionless limit**: for a
family of Fig. 5.10 equilibria indexed by `κ > 0`, for every `t > 0` the price level
`p^κ_t → t − 1/(r + ω)` as `κ → ∞` (the downward jump of the frictionless model followed by
inflation), while `p^κ_0 = 0` for every `κ`. -/
theorem fig510_price_limit {r ω σ ρ K t : ℝ} {q : ℝ → ℝ} {X P V : ℝ → ℝ → ℝ} (hr : 0 < r)
    (hω : 0 ≤ ω) (hσ : 0 < σ) (hc : ContinuousOn q (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt q ((r + ω) * q t + 1) t) (hb : ∀ t, 0 ≤ t → |q t| ≤ K)
    (h : ∀ κ, 0 < κ → IsCTEquilibrium r σ κ ρ (q 0) (fun _ => 1) (fun _ => 0) (X κ) (P κ) (V κ))
    (ht : 0 < t) :
    Tendsto (fun κ => ∫ τ in (0 : ℝ)..t, P κ τ) atTop (𝓝 (t - 1 / (r + ω))) := by
  have hq0 := fig510_bond_price (by linarith) hc hd hb 0 le_rfl
  have := ct_price_limit hr hσ h ht
  rw [hq0] at this
  convert this using 2
  ring

/-- Cochrane (2023), Fig. 5.10, pp. 172–173: **the disinflation period.** In the Fig. 5.10
equilibrium, inflation is negative exactly before `T = log((r + λ₂)/(r + ω))/λ₂`:
`π_t < 0 ↔ λ₂t < log((r + λ₂)/(r + ω))`. -/
theorem fig510_disinflation_iff {r ω σ κ ρ K : ℝ} {q x π v : ℝ → ℝ} (hr : 0 < r) (hω : 0 ≤ ω)
    (hκ : 0 < κ) (hσ : 0 < σ) (hc : ContinuousOn q (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt q ((r + ω) * q t + 1) t) (hb : ∀ t, 0 ≤ t → |q t| ≤ K)
    (h : IsCTEquilibrium r σ κ ρ (q 0) (fun _ => 1) (fun _ => 0) x π v) (t : ℝ) (ht : 0 ≤ t) :
    π t < 0 ↔ lam2 ρ κ σ * t < Real.log ((r + lam2 ρ κ σ) / (r + ω)) := by
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hrw : 0 < r + ω := by linarith
  have hA : 0 < (r + lam2 ρ κ σ) / (r + ω) := by positivity
  rw [(fig510 hr hω hκ hσ hc hd hb h).2.1 t ht, Real.lt_log_iff_exp_lt hA]
  have he := Real.exp_pos (lam2 ρ κ σ * t)
  have hinv : Real.exp (-(lam2 ρ κ σ * t)) = (Real.exp (lam2 ρ κ σ * t))⁻¹ := by
    rw [Real.exp_neg]
  rw [hinv]
  constructor
  · intro hlt
    have : 1 < (r + lam2 ρ κ σ) / (r + ω) * (Real.exp (lam2 ρ κ σ * t))⁻¹ := by linarith
    rwa [← div_eq_mul_inv, one_lt_div he] at this
  · intro hlt
    have : 1 < (r + lam2 ρ κ σ) / (r + ω) * (Real.exp (lam2 ρ κ σ * t))⁻¹ := by
      rwa [← div_eq_mul_inv, one_lt_div he]
    linarith

/-- Cochrane (2023), p. 172 and Fig. 5.10: **"as prices become stickier, as `κ` declines, the
period of disinflation lasts longer"** (perpetuity, `ω = 0`): the disinflation period
`T(κ) = log(1 + λ₂/r)/λ₂` is strictly decreasing in `κ`. -/
theorem fig510_disinflation_longer {r σ ρ κ κ' : ℝ} (hr : 0 < r) (hσ : 0 < σ) (hκ : 0 < κ)
    (hκκ : κ < κ') :
    Real.log ((r + lam2 ρ κ' σ) / (r + 0)) / lam2 ρ κ' σ <
      Real.log ((r + lam2 ρ κ σ) / (r + 0)) / lam2 ρ κ σ := by
  have hl := lam2_pos (ρ := ρ) hκ hσ
  have hm := lam2_pos (ρ := ρ) (lt_trans hκ hκκ) hσ
  have hlm := lam2_strictMono (ρ := ρ) hσ hκ hκκ
  set l := lam2 ρ κ σ
  set m := lam2 ρ κ' σ
  rw [add_zero]
  have hx : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hy : (r + m) / r ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.2 (by positivity)
  have hne : (1 : ℝ) ≠ (r + m) / r := by
    rw [ne_eq, eq_div_iff hr.ne']
    linarith
  have ha : (0 : ℝ) < 1 - l / m := by rw [sub_pos, div_lt_one hm]; exact hlm
  have hb : (0 : ℝ) < l / m := by positivity
  have hc := strictConcaveOn_log_Ioi.2 hx hy hne ha hb (by ring)
  have hpt : (1 - l / m) • (1 : ℝ) + (l / m) • ((r + m) / r) = (r + l) / r := by
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hpt, smul_eq_mul, smul_eq_mul, Real.log_one, mul_zero, zero_add] at hc
  rw [div_lt_div_iff₀ hm hl]
  have : l / m * Real.log ((r + m) / r) * m = l * Real.log ((r + m) / r) := by
    field_simp
  nlinarith

/-! ## The flexible-price limit of the family (5.94) (p. 165) -/

/-- Cochrane (2023), p. 165 (infrastructure): **the exponential kernel is an approximate
identity**: for a bounded measurable `g` with `g(τ) → g₀` as `τ ↓ 0`,
`a ∫_0^∞ e^{−aτ} g(τ) dτ → g₀` as `a → ∞`. -/
theorem approx_identity {g : ℝ → ℝ} {g0 M : ℝ} (hm : Measurable g) (hM : ∀ τ, |g τ| ≤ M)
    (hg : Tendsto g (𝓝[>] 0) (𝓝 g0)) :
    Tendsto (fun a => a * ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * g τ) atTop (𝓝 g0) := by
  have hsub : ∀ a, 0 < a → a * ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * g τ =
      ∫ u in Set.Ioi 0, Real.exp (-u) * g (u / a) := by
    intro a ha
    have h := integral_comp_mul_left_Ioi (fun u => Real.exp (-u) * g (u / a)) 0 ha
    simp only [mul_zero, smul_eq_mul] at h
    have e : ∫ x in Set.Ioi 0, Real.exp (-(a * x)) * g (a * x / a) =
        ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * g τ := by
      refine integral_congr_ae (ae_of_all _ fun τ => ?_)
      simp only [mul_div_cancel_left₀ τ ha.ne']
    rw [← e, h, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  have hE : ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) = 1 := by
    have := integral_exp_Ioi (a := 1) one_pos
    simpa using this
  have hlim : Tendsto (fun a => ∫ u in Set.Ioi 0, Real.exp (-u) * g (u / a)) atTop
      (𝓝 (∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * g0)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u => M * Real.exp (-u))
      (Eventually.of_forall fun a => ((by fun_prop : Continuous fun u : ℝ =>
        Real.exp (-u)).measurable.mul (hm.comp (measurable_id.div_const a))).aestronglyMeasurable)
      (Eventually.of_forall fun a => ae_of_all _ fun u => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm M]
        exact mul_le_mul_of_nonneg_left (hM _) (Real.exp_pos _).le) ?_ ?_
    · have := (integrableOn_exp_Ioi (a := 1) one_pos).const_mul M
      simpa only [one_mul] using this
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u (hu : (0 : ℝ) < u) => ?_)
      have h1 : Tendsto (fun a : ℝ => u / a) atTop (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
        filter_upwards [eventually_gt_atTop 0] with a ha
        exact div_pos hu ha
      exact (hg.comp h1).const_mul _
  rw [integral_mul_const, hE, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with a ha
  rw [hsub a ha]

/-- Cochrane (2023), p. 165: **"in the flexible-price case, (5.94) becomes `π_t = i_t`"**: for an
interest-rate path continuous and bounded on `[0, ∞)`, every member of the family (5.94)
(any fixed `C₀`) converges to `i_t` at every `t > 0` as `κ → ∞`. -/
theorem ct_flexible_limit {ρ σ M C t : ℝ} {i : ℝ → ℝ} (hσ : 0 < σ)
    (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ s, 0 ≤ s → |i s| ≤ M) (ht : 0 < t) :
    Tendsto (fun κ => piFamily ρ κ σ i C t) atTop (𝓝 (i t)) := by
  have hie := ext0_continuous hi
  have hieb := ext0_abs_le hM
  have hit : ext0 i t = i t := ext0_eq ht.le
  have hL2 := lam2_tendsto_atTop (ρ := ρ) hσ
  have hL1 : Tendsto (fun κ => lam1 ρ κ σ) atTop atTop := by
    refine (tendsto_atTop_add_const_right _ ρ hL2).congr fun κ => ?_
    linarith [lam_sub ρ κ σ]
  -- the forward part
  set gF : ℝ → ℝ := fun τ => ext0 i (t + τ)
  have hgFc : Continuous gF := hie.comp (continuous_const.add continuous_id)
  have hgF : Tendsto gF (𝓝[>] 0) (𝓝 (i t)) := by
    have := hgFc.tendsto 0
    simp only [gF, add_zero, hit] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hF := (approx_identity hgFc.measurable (fun τ => hieb (t + τ)) hgF).comp hL1
  -- the backward part
  set gB : ℝ → ℝ := (Set.Iic t).indicator fun τ => ext0 i (t - τ)
  have hgBm : Measurable gB :=
    (hie.comp (continuous_const.sub continuous_id)).measurable.indicator measurableSet_Iic
  have hgBb : ∀ τ, |gB τ| ≤ M := by
    intro τ
    by_cases hτ : τ ∈ Set.Iic t
    · simp only [gB, Set.indicator_of_mem hτ]
      exact hieb _
    · simp only [gB, Set.indicator_of_notMem hτ, abs_zero]
      exact le_trans (abs_nonneg _) (hieb 0)
  have hgB : Tendsto gB (𝓝[>] 0) (𝓝 (i t)) := by
    have hcont : Continuous fun τ : ℝ => ext0 i (t - τ) :=
      hie.comp (continuous_const.sub continuous_id)
    have hc := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simp only [sub_zero, hit] at hc
    refine hc.congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds ht)] with τ hτ
    simp only [gB, Set.indicator_of_mem (show τ ∈ Set.Iic t from le_of_lt hτ)]
  have hB := (approx_identity hgBm hgBb hgB).comp hL2
  -- rewrite the family
  have hFeq : ∀ κ, fwdInt (lam1 ρ κ σ) i t =
      ∫ τ in Set.Ioi 0, Real.exp (-(lam1 ρ κ σ * τ)) * gF τ := fun κ =>
    fwdInt_congr ht.le fun s hs => (ext0_eq hs).symm
  have hBeq : ∀ κ, bwdInt (lam2 ρ κ σ) i t =
      ∫ τ in Set.Ioi 0, Real.exp (-(lam2 ρ κ σ * τ)) * gB τ := by
    intro κ
    rw [bwdInt_congr ht.le fun s hs => (ext0_eq hs).symm, bwdInt,
      intervalIntegral.integral_of_le ht.le, ← Set.Ioi_inter_Iic,
      ← setIntegral_indicator measurableSet_Iic]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only [gB]
    rw [Set.indicator_mul_right]
  -- the weights tend to 1/2
  have hw2 : Tendsto (fun κ => lam2 ρ κ σ / (lam1 ρ κ σ + lam2 ρ κ σ)) atTop (𝓝 (1 / 2)) := by
    have h0 : Tendsto (fun κ => ρ / lam2 ρ κ σ) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hL2
    have := (h0.const_add 2).inv₀ (by norm_num : (2 : ℝ) + 0 ≠ 0)
    rw [add_zero, ← one_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with κ hκ
    have h1 := lam1_pos (ρ := ρ) hκ hσ
    have h2 := lam2_pos (ρ := ρ) hκ hσ
    have e : lam1 ρ κ σ + lam2 ρ κ σ = (2 + ρ / lam2 ρ κ σ) * lam2 ρ κ σ := by
      field_simp
      linarith [lam_sub ρ κ σ]
    have hA : 2 + ρ / lam2 ρ κ σ ≠ 0 := by
      intro h0'
      rw [h0', zero_mul] at e
      linarith
    rw [e]
    field_simp
  have hw1 : Tendsto (fun κ => lam1 ρ κ σ / (lam1 ρ κ σ + lam2 ρ κ σ)) atTop (𝓝 (1 / 2)) := by
    have := hw2.const_sub 1
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with κ hκ
    have h1 := lam1_pos (ρ := ρ) hκ hσ
    have h2 := lam2_pos (ρ := ρ) hκ hσ
    field_simp
    ring
  have hexp : Tendsto (fun κ => C * Real.exp (-(lam2 ρ κ σ * t))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (hL2.atTop_mul_const ht)).const_mul C
    rwa [mul_zero] at this
  have hsum := hexp.add ((hw1.mul hB).add (hw2.mul hF))
  rw [zero_add, ← add_mul, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, one_mul] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  have h1 := lam1_pos (ρ := ρ) hκ hσ
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hW : piWeight ρ κ σ = lam1 ρ κ σ * lam2 ρ κ σ / (lam1 ρ κ σ + lam2 ρ κ σ) := by
    rw [eq_div_iff (by positivity), piWeight_mul_add hκ hσ, lam_mul hκ hσ]
  simp only [Function.comp_apply]
  rw [piFamily, hW, hBeq κ, hFeq κ]
  field_simp

end Cochrane.StickyPriceFiscal.CTSimple
