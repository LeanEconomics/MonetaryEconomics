/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.ZLBSelection
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Magical multipliers and Bastiat banished

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.5, pp. 480–482.

A Phillips-curve disturbance `g` (government spending, or deliberate cost increases) is `g` on
the trap `[0, T)` and `0` afterwards. The multiplier is `∂x_t/∂g` at `g = 0`.

## Main results

* The IS curve solved forward (p. 480): `is_forward` (any path with `x_T → 0` and an
  integrable real-rate gap) and `experiment_is_forward` (every bounded path of the experiment):
  `x_t = −∫_0^∞ σ(i_{t+s} − u_{r,t+s} − π_{t+s}) ds`.
* Output is affine in `g` (`xNK_affine`, `xNJ_affine`), with exact derivatives
  `hasDerivAt_xNK`, `hasDerivAt_xNJ` — the multipliers `multNK` (standard, `π_T = 0`) and
  `multNJ` (no-jump, `π_0 = 0`).
* Standard multipliers (p. 481): `multNK_pos`; `multNK_tendsto_kappa` (→ ∞ as prices become
  flexible), `multNK_strictMono_kappa` (increasing as `κ` rises); `multNK0_strictMonoOn_T`,
  `multNK0_ge` (exponential lower bound), `multNK0_tendsto_T`, `multNK0_gt_one_eventually`
  (`> 1` for long traps). **E20**: the book's "substantially greater than one" fails for short
  traps — `multNK0_lt_one_short` (`< 1` for all small `T`) and the numerical counterexample
  `e20_counterexample` (`0 < m₀ < 1` at `κ = σ = 1`, `ρ = 0.05`, `T = 1`).
* The limit point (p. 481): `frictionless_multiplier` (`x = −g`, multiplier `−1`).
* No-jump multipliers (p. 481): `multNJ_formula`, `multNJ_bounds` (`−1 < m < 0` during the
  trap: small, near the frictionless value), `multNJ_tendsto_kappa`, `multNJ_tendsto_T`
  (→ `−1`).
* "Spending in the future is exponentially more effective" (p. 481, not shown in the book):
  `window_isPath`, `window_unique`, `window_x0`, `windowMult_strictMono`, `windowMult_tendsto`.
-/

namespace Cochrane.ZeroBound.Multipliers

open Filter Topology MeasureTheory
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.ZLBSelection

/-! ## The IS curve solved forward (p. 480) -/

/-- Cochrane (2023), §20.2.5, p. 480: **the IS equation (20.5) solved forward.** Along a path
(differentiable off a countable set), if `x_T → 0` and the real-rate gap `i − u_r − π` is
integrable on `(t, ∞)` (`t ≥ 0`), then `x_t = −∫_0^∞ σ(i_{t+s} − u_{r,t+s} − π_{t+s}) ds`. -/
theorem is_forward {σ ρ κ t : ℝ} {i u g x π : ℝ → ℝ} {S : Set ℝ} (hS : S.Countable)
    (h : IsPath σ ρ κ i u g S x π) (ht : 0 ≤ t) (hx : Tendsto x atTop (𝓝 0))
    (hint : IntegrableOn (fun s => i s - u s - π s) (Set.Ioi t)) :
    x t = -∫ s in Set.Ioi 0, σ * (i (t + s) - u (t + s) - π (t + s)) := by
  have hf : IntegrableOn (fun s => σ * (i s - π s - u s)) (Set.Ioi t) :=
    IntegrableOn.congr_fun (hint.const_mul σ) (fun s _ => by ring) measurableSet_Ioi
  have hftc : ∀ b, t ≤ b → ∫ s in t..b, σ * (i s - π s - u s) = x b - x t := fun b hb =>
    integral_eq_of_hasDerivAt_off_countable_of_le x _ hb hS
      (h.1.mono fun s hs => le_trans ht hs.1)
      (fun s hs => (h.2.2 s (by linarith [hs.1.1]) hs.2).1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).2
        (hf.mono_set Set.Ioc_subset_Ioi_self))
  have hlim := intervalIntegral_tendsto_integral_Ioi t hf tendsto_id
  have hlim2 : Tendsto (fun b => x b - x t) atTop
      (𝓝 (∫ s in Set.Ioi t, σ * (i s - π s - u s))) :=
    hlim.congr' (by filter_upwards [eventually_ge_atTop t] with b hb; exact hftc b hb)
  have hlim3 := hx.sub_const (x t)
  have := tendsto_nhds_unique hlim3 hlim2
  rw [← integral_Ioi_shift] at this
  have e : ∫ s in Set.Ioi 0, σ * (i (t + s) - π (t + s) - u (t + s)) =
      ∫ s in Set.Ioi 0, σ * (i (t + s) - u (t + s) - π (t + s)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    ring
  rw [← e]
  linarith

/-- Cochrane (2023), §20.2.5, p. 480: the natural-rate step `trapStep u T` is integrable on
every `(t, ∞)`. -/
theorem trapStep_integrableOn (u T t : ℝ) : IntegrableOn (trapStep u T) (Set.Ioi t) := by
  have hind : trapStep u T = (Set.Iio T).indicator fun _ => u := by
    funext s
    by_cases hs : s < T <;> simp [trapStep, hs, Set.indicator]
  rw [hind, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
  exact integrableOn_const (by simp)

/-- Cochrane (2023), §20.2.5, p. 480: **the forward IS solution holds along every bounded path of
the experiment** (for every `t ≥ 0`). -/
theorem experiment_is_forward {σ κ ρ T u g t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : 0 ≤ t)
    {x π : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
      BddOnIci π) :
    x t = -∫ s in Set.Ioi 0, σ * (0 - trapStep u T (t + s) - π (t + s)) := by
  obtain ⟨πT, hπT⟩ := (bdd_path_iff hκ hσ).1 h
  have hb := lamb_pos (ρ := ρ) hκ hσ
  obtain ⟨K, hK⟩ := h.2.2
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0 le_rfl)
  -- `|π_s| ≤ M e^{−λ^b s}` on `[0, ∞)`
  set M := (K + |πT|) * Real.exp (lamb ρ κ σ * T)
  have hbound : ∀ s, 0 ≤ s → |π s| ≤ M * Real.exp (-(lamb ρ κ σ * s)) := by
    intro s hs
    have e : M * Real.exp (-(lamb ρ κ σ * s)) =
        (K + |πT|) * Real.exp (lamb ρ κ σ * (T - s)) := by
      simp only [M]; rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [e]
    rcases le_or_gt s T with hsT | hsT
    · have : 1 ≤ Real.exp (lamb ρ κ σ * (T - s)) := Real.one_le_exp (by nlinarith)
      nlinarith [hK s hs, abs_nonneg πT]
    · rw [(hπT s hs).1]
      simp only [wPi, not_le.2 hsT, ↓reduceIte]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have : -(lamb ρ κ σ * (s - T)) = lamb ρ κ σ * (T - s) := by ring
      rw [this]
      nlinarith [Real.exp_pos (lamb ρ κ σ * (T - s))]
  have hπint : IntegrableOn π (Set.Ioi t) := by
    have hdom := (integrableOn_exp_mul_Ioi (a := -lamb ρ κ σ) (by linarith) t).const_mul M
    refine Integrable.mono' hdom
      ((h.1.2.1.mono fun s (hs : t < s) => (show (0 : ℝ) ≤ s by linarith :
        s ∈ Set.Ici (0 : ℝ))).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s (hs : t < s) => ?_))
    rw [Real.norm_eq_abs, neg_mul]
    exact hbound s (by linarith)
  have hint : IntegrableOn (fun s => (fun _ => (0 : ℝ)) s - trapStep u T s - π s)
      (Set.Ioi t) := by
    have := (trapStep_integrableOn u T t).neg.sub hπint
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  have hx : Tendsto x atTop (𝓝 0) := by
    have hl : Tendsto (fun s => lamf ρ κ σ * (πT * Real.exp (-(lamb ρ κ σ * (s - T)))) / κ)
        atTop (𝓝 0) := by
      have := ((tendsto_expNeg hb).comp (tendsto_atTop_add_const_right atTop (-T) tendsto_id))
      have := ((this.const_mul πT).const_mul (lamf ρ κ σ)).div_const κ
      simp only [mul_zero, zero_div] at this
      refine this.congr fun s => ?_
      simp [Function.comp, sub_eq_add_neg]
    refine hl.congr' ?_
    filter_upwards [eventually_gt_atTop T, eventually_ge_atTop 0] with s hs hs0
    rw [(hπT s hs0).2]
    simp [wX, not_le.2 hs]
  exact is_forward (Set.countable_singleton T) h.1 ht hx hint

/-! ## Multipliers -/

/-- Cochrane (2023), §20.2.5, p. 481: the output gap in the standard (`π_T = 0`) equilibrium
with Phillips-curve disturbance `g` during the trap. -/
noncomputable def xNK (σ κ ρ T u g t : ℝ) : ℝ := wX σ κ ρ T u g 0 t

/-- Cochrane (2023), §20.2.5, p. 481: end-of-trap inflation of the no-jump (`π_0 = 0`)
equilibrium with disturbance `g`. -/
noncomputable def piTnjg (σ κ ρ T u g : ℝ) : ℝ :=
  -(-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) T) + κ * g * kk (lamf ρ κ σ) (lamb ρ κ σ) T) *
    Real.exp (-(lamb ρ κ σ * T))

/-- Cochrane (2023), §20.2.5, p. 481: the output gap in the no-jump equilibrium with
disturbance `g`. -/
noncomputable def xNJ (σ κ ρ T u g t : ℝ) : ℝ := wX σ κ ρ T u g (piTnjg σ κ ρ T u g) t

/-- Cochrane (2023), §20.2.5, p. 481: the standard multiplier `∂x_t/∂g`:
`h(T − t) − 1` during the trap and `0` afterwards. -/
noncomputable def multNK (σ κ ρ T t : ℝ) : ℝ :=
  if t ≤ T then hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t) - 1 else 0

/-- Cochrane (2023), §20.2.5, p. 481: the no-jump multiplier `∂x_t/∂g`:
the standard one minus `λ^f k(T) e^{−λ^b t}`. -/
noncomputable def multNJ (σ κ ρ T t : ℝ) : ℝ :=
  multNK σ κ ρ T t - lamf ρ κ σ * kk (lamf ρ κ σ) (lamb ρ κ σ) T * Real.exp (-(lamb ρ κ σ * t))

/-- Cochrane (2023), §20.2.5, p. 481: the no-jump selection with disturbance `g` has `π_0 = 0`. -/
theorem nj_g_pi0 {σ κ ρ T u g : ℝ} (hT : 0 ≤ T) :
    wPi σ κ ρ T u g (piTnjg σ κ ρ T u g) 0 = 0 := by
  simp only [wPi, hT, ↓reduceIte, trapPi, piTnjg, sub_zero]
  have : Real.exp (-(lamb ρ κ σ * T)) * Real.exp (lamb ρ κ σ * T) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (-(-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) T) +
    κ * g * kk (lamf ρ κ σ) (lamb ρ κ σ) T)) * this

/-- Cochrane (2023), §20.2.5, p. 481: in the standard equilibrium output is affine in `g`,
`x_t(g) = x_t(0) + g · multNK_t`. -/
theorem xNK_affine {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T u g t : ℝ) :
    xNK σ κ ρ T u g t = xNK σ κ ρ T u 0 t + g * multNK σ κ ρ T t := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  unfold xNK multNK wX
  split_ifs
  · simp only [trapPi, trapY, hh, kk]
    field_simp
    ring
  · simp

/-- Cochrane (2023), §20.2.5, p. 481: in the no-jump equilibrium output is affine in `g`,
`x_t(g) = x_t(0) + g · multNJ_t`. -/
theorem xNJ_affine {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T u g t : ℝ) :
    xNJ σ κ ρ T u g t = xNJ σ κ ρ T u 0 t + g * multNJ σ κ ρ T t := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have e1 : Real.exp (-(lamb ρ κ σ * T)) * Real.exp (lamb ρ κ σ * (T - t)) =
      Real.exp (-(lamb ρ κ σ * t)) := by rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(lamb ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * (t - T))) =
      Real.exp (-(lamb ρ κ σ * t)) := by rw [← Real.exp_add]; ring_nf
  unfold xNJ multNJ multNK wX piTnjg
  split_ifs
  · simp only [trapPi, trapY, hh, kk]
    rw [← e1]
    field_simp
    ring
  · rw [← e2]
    field_simp
    ring

/-- Cochrane (2023), §20.2.5, p. 481: **the standard multiplier is the exact derivative**
`∂x_t/∂g` (at any `g`, in particular at `g = 0`). -/
theorem hasDerivAt_xNK {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T u t g0 : ℝ) :
    HasDerivAt (fun g => xNK σ κ ρ T u g t) (multNK σ κ ρ T t) g0 := by
  have h : (fun g => xNK σ κ ρ T u g t) =
      fun g => xNK σ κ ρ T u 0 t + g * multNK σ κ ρ T t :=
    funext fun g => xNK_affine hσ hκ T u g t
  rw [h]
  exact ((hasDerivAt_id g0).mul_const _).const_add _ |>.congr_deriv (by simp)

/-- Cochrane (2023), §20.2.5, p. 481: the no-jump multiplier is the exact derivative
`∂x_t/∂g`. -/
theorem hasDerivAt_xNJ {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T u t g0 : ℝ) :
    HasDerivAt (fun g => xNJ σ κ ρ T u g t) (multNJ σ κ ρ T t) g0 := by
  have h : (fun g => xNJ σ κ ρ T u g t) =
      fun g => xNJ σ κ ρ T u 0 t + g * multNJ σ κ ρ T t :=
    funext fun g => xNJ_affine hσ hκ T u g t
  rw [h]
  exact ((hasDerivAt_id g0).mul_const _).const_add _ |>.congr_deriv (by simp)

/-! ### Standard multipliers -/

/-- Cochrane (2023), §20.2.5, p. 481: the standard multiplier is positive during the trap. -/
theorem multNK_pos {σ κ ρ T t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (htT : t < T) :
    0 < multNK σ κ ρ T t := by
  simp only [multNK, htT.le, ↓reduceIte]
  linarith [one_lt_hh (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) (sub_pos.2 htT)]

/-- Cochrane (2023), §20.2.5, p. 481 ("in the limit that price stickiness goes to zero, the
multiplier goes to infinity"): for `t < T` and `ρ ≥ 0`, `multNK_t → ∞` as `κ → ∞`. -/
theorem multNK_tendsto_kappa {σ ρ T t : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (htT : t < T) :
    Tendsto (fun κ => multNK σ κ ρ T t) atTop atTop := by
  have hE := expLamb_tendsto_kappa (ρ := ρ) hσ (sub_pos.2 htT)
  have h1 : Tendsto (fun κ => Real.exp (lamb ρ κ σ * (T - t)) / 2 - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hE.atTop_div_const (by norm_num))
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  simp only [multNK, htT.le, ↓reduceIte]
  have hh1 := hh_ge (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) (T - t)
  have hw := half_le_weight hρ hσ hκ
  have hE0 := Real.exp_pos (lamb ρ κ σ * (T - t))
  have := mul_le_mul_of_nonneg_right hw hE0.le
  rw [mul_div_right_comm] at hh1
  linarith

/-- Cochrane (2023), §20.2.5, p. 481 ("multipliers increase as price stickiness is reduced"):
for `t < T` and `ρ ≥ 0`, `multNK_t` is strictly increasing in `κ`. -/
theorem multNK_strictMono_kappa {σ ρ T t κ κ' : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (htT : t < T)
    (hκ : 0 < κ) (hlt : κ < κ') : multNK σ κ ρ T t < multNK σ κ' ρ T t := by
  simp only [multNK, htT.le, ↓reduceIte]
  linarith [hh_strictMono_kappa hρ hσ hκ hlt (sub_pos.2 htT) (ρ := ρ)]

/-- Cochrane (2023), §20.2.5, p. 481: the time-0 standard multiplier is `h(T) − 1`. -/
theorem multNK0_eq {σ κ ρ T : ℝ} (hT : 0 ≤ T) :
    multNK σ κ ρ T 0 = hh (lamf ρ κ σ) (lamb ρ κ σ) T - 1 := by
  simp [multNK, hT]

/-- Cochrane (2023), §20.2.5, p. 481 ("the multipliers increase … as the length of the liquidity
trap increases"): `m_0(T)` is strictly increasing in `T ≥ 0`. -/
theorem multNK0_strictMonoOn_T {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    StrictMonoOn (fun T => multNK σ κ ρ T 0) (Set.Ici 0) := by
  intro T1 h1 T2 h2 hlt
  simp only
  rw [multNK0_eq h1, multNK0_eq h2]
  linarith [hh_strictMonoOn (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) h1 h2 hlt]

/-- Cochrane (2023), §20.2.5, p. 481 ("increase exponentially"): the exponential lower bound
`m_0(T) ≥ λ^f e^{λ^b T}/(λ^f + λ^b) − 1`. -/
theorem multNK0_ge {σ κ ρ T : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 ≤ T) :
    lamf ρ κ σ * Real.exp (lamb ρ κ σ * T) / (lamf ρ κ σ + lamb ρ κ σ) - 1 ≤
      multNK σ κ ρ T 0 := by
  rw [multNK0_eq hT]
  linarith [hh_ge (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) T]

/-- Cochrane (2023), §20.2.5, p. 481: `m_0(T) → ∞` as the trap lengthens. -/
theorem multNK0_tendsto_T {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    Tendsto (fun T => multNK σ κ ρ T 0) atTop atTop := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have h1 : Tendsto (fun T => lamf ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) *
      Real.exp (lamb ρ κ σ * T) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      ((tendsto_expPos (lamb_pos (ρ := ρ) hκ hσ)).const_mul_atTop (by positivity))
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_ge_atTop 0] with T hT
  have := multNK0_ge (ρ := ρ) hσ hκ hT
  rw [mul_div_right_comm] at this
  linarith

/-- Cochrane (2023), §20.2.5, p. 481: for long enough traps the standard multiplier exceeds
one. -/
theorem multNK0_gt_one_eventually {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ∃ T0, ∀ T, T0 ≤ T → 1 < multNK σ κ ρ T 0 := by
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 ((multNK0_tendsto_T (ρ := ρ) hσ hκ).eventually_gt_atTop 1)
  exact ⟨T0, hT0⟩

/-- Cochrane (2023), §20.2.5, p. 481, **survey error E20** ("multipliers are large and
substantially greater than one" needs a long trap): for every `κ, σ > 0` there is `T₀ > 0` with
`0 < m_0(T) < 1` for all `T ∈ (0, T₀)`. -/
theorem multNK0_lt_one_short {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ∃ T0, 0 < T0 ∧ ∀ T, 0 < T → T < T0 → 0 < multNK σ κ ρ T 0 ∧ multNK σ κ ρ T 0 < 1 := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hc : ContinuousAt (hh (lamf ρ κ σ) (lamb ρ κ σ)) 0 :=
    (hh_hasDerivAt hne 0).continuousAt
  have hev : ∀ᶠ T in 𝓝 0, hh (lamf ρ κ σ) (lamb ρ κ σ) T < 2 := by
    have := hc.eventually (gt_mem_nhds (show hh (lamf ρ κ σ) (lamb ρ κ σ) 0 < 2 by
      rw [hh_zero hne]; norm_num))
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun T hT hTε => ⟨multNK_pos hσ hκ hT, ?_⟩⟩
  rw [multNK0_eq hT.le]
  have := hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hT]; exact hTε)
  linarith

/-- Cochrane (2023), §20.2.5, p. 481, **E20 counterexample**: at `κ = σ = 1`, `ρ = 0.05` and a
trap of length `T = 1`, the standard time-0 multiplier satisfies `0 < m_0 < 1` (numerically
`0.53`). -/
theorem e20_counterexample :
    0 < multNK 1 1 (1 / 20) 1 0 ∧ multNK 1 1 (1 / 20) 1 0 < 1 := by
  refine ⟨multNK_pos one_pos one_pos one_pos, ?_⟩
  rw [multNK0_eq zero_le_one]
  set S := Real.sqrt ((1 / 20 : ℝ) ^ 2 + 4 * 1 * 1) with hSdef
  have hS2 : 2 < S := by
    rw [hSdef, Real.lt_sqrt (by norm_num)]; norm_num
  have hS3 : S < 2001 / 1000 := by
    rw [hSdef, Real.sqrt_lt' (by norm_num)]; norm_num
  have hf : lamf (1 / 20) 1 1 = (S + 1 / 20) / 2 := by simp only [lamf, hSdef]
  have hb : lamb (1 / 20) 1 1 = (S - 1 / 20) / 2 := by simp only [lamb, hSdef]
  have hsum : lamf (1 / 20) 1 1 + lamb (1 / 20) 1 1 = S := by rw [hf, hb]; ring
  have hlb1 : lamb (1 / 20) 1 1 * 1 ≤ 1 := by rw [hb]; linarith
  have he1 : Real.exp (lamb (1 / 20) 1 1 * 1) < 2.7182818286 :=
    lt_of_le_of_lt (Real.exp_le_exp.2 hlb1) Real.exp_one_lt_d9
  have he2 : Real.exp (-(lamf (1 / 20) 1 1 * 1)) ≤ 1 := by
    rw [Real.exp_le_one_iff, hf]; linarith
  have hpf : 0 < lamf (1 / 20) 1 1 := by rw [hf]; linarith
  have hpb : 0 < lamb (1 / 20) 1 1 := by rw [hb]; linarith
  unfold hh
  rw [hsum, sub_lt_iff_lt_add, div_lt_iff₀ (by linarith)]
  have : lamf (1 / 20) 1 1 * Real.exp (lamb (1 / 20) 1 1 * 1) ≤
      lamf (1 / 20) 1 1 * 2.7182818286 := mul_le_mul_of_nonneg_left he1.le hpf.le
  have : lamb (1 / 20) 1 1 * Real.exp (-(lamf (1 / 20) 1 1 * 1)) ≤ lamb (1 / 20) 1 1 :=
    by nlinarith
  rw [hf, hb] at *
  nlinarith

/-- Cochrane (2023), §20.2.5, p. 481 ("the multiplier is −1 at the limit point, since
`x_t = −g_t`"): in the frictionless model, for each `g` let `x_g` be a frictionless solution;
then `∂x_t/∂g = −1` during the trap (`0 ≤ t < T`). -/
theorem frictionless_multiplier {σ T u t g0 : ℝ} (hσ : σ ≠ 0) (ht : 0 ≤ t) (htT : t < T)
    {X P : ℝ → ℝ → ℝ}
    (h : ∀ g, IsFrictionless σ (fun _ => 0) (trapStep u T) (trapStep g T) {T} (X g) (P g)) :
    HasDerivAt (fun g => X g t) (-1) g0 := by
  have e : (fun g => X g t) = fun g => -g := funext fun g => by
    rw [((frictionless_iff hσ).1 (h g)).1 t ht]
    simp [trapStep, htT]
  rw [e]
  exact (hasDerivAt_id g0).neg

/-! ### No-jump multipliers -/

/-- Cochrane (2023), §20.2.5, p. 481: the no-jump multiplier during the trap,
`m_t = −1 + (λ^b e^{−λ^f(T−t)} + λ^f e^{−λ^f T}e^{−λ^b t})/(λ^f + λ^b)`. -/
theorem multNJ_formula {σ κ ρ T t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (htT : t ≤ T) :
    multNJ σ κ ρ T t = -1 + (lamb ρ κ σ * Real.exp (-(lamf ρ κ σ * (T - t))) +
      lamf ρ κ σ * Real.exp (-(lamf ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * t))) /
        (lamf ρ κ σ + lamb ρ κ σ) := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have e1 : Real.exp (lamb ρ κ σ * (T - t)) =
      Real.exp (lamb ρ κ σ * T) * Real.exp (-(lamb ρ κ σ * t)) := by
    rw [← Real.exp_add]; ring_nf
  simp only [multNJ, multNK, htT, ↓reduceIte, hh, kk]
  rw [e1]
  field_simp
  ring

/-- Cochrane (2023), §20.2.5, p. 481 ("the multiplier in the no-jump equilibrium is small, and
clustered around the frictionless value −1"): `−1 < m_t < 0` throughout the trap. -/
theorem multNJ_bounds {σ κ ρ T t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 < T) (ht : 0 ≤ t)
    (htT : t ≤ T) : -1 < multNJ σ κ ρ T t ∧ multNJ σ κ ρ T t < 0 := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  rw [multNJ_formula hσ hκ htT]
  have b1 : Real.exp (-(lamf ρ κ σ * (T - t))) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have b2 : Real.exp (-(lamf ρ κ σ * T)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith
  have b3 : Real.exp (-(lamb ρ κ σ * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have p1 := Real.exp_pos (-(lamf ρ κ σ * (T - t)))
  have p2 := Real.exp_pos (-(lamf ρ κ σ * T))
  have p3 := Real.exp_pos (-(lamb ρ κ σ * t))
  have hpos : 0 < (lamb ρ κ σ * Real.exp (-(lamf ρ κ σ * (T - t))) +
      lamf ρ κ σ * Real.exp (-(lamf ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * t))) /
        (lamf ρ κ σ + lamb ρ κ σ) := by positivity
  have hlt : (lamb ρ κ σ * Real.exp (-(lamf ρ κ σ * (T - t))) +
      lamf ρ κ σ * Real.exp (-(lamf ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * t))) /
        (lamf ρ κ σ + lamb ρ κ σ) < 1 := by
    rw [div_lt_one hS]
    have : Real.exp (-(lamf ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * t)) < 1 := by nlinarith
    nlinarith
  constructor <;> linarith

/-- Cochrane (2023), §20.2.5, p. 481: `|m_t + 1| ≤ e^{−λ^f(T−t)} + e^{−λ^f T}` during the trap
(no-jump multiplier). -/
theorem multNJ_dist {σ κ ρ T t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : 0 ≤ t) (htT : t ≤ T) :
    |multNJ σ κ ρ T t - -1| ≤
      Real.exp (-(lamf ρ κ σ * (T - t))) + Real.exp (-(lamf ρ κ σ * T)) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have e : multNJ σ κ ρ T t - -1 = (lamb ρ κ σ * Real.exp (-(lamf ρ κ σ * (T - t))) +
      lamf ρ κ σ * Real.exp (-(lamf ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * t))) /
        (lamf ρ κ σ + lamb ρ κ σ) := by
    rw [multNJ_formula hσ hκ htT]; ring
  rw [e]
  have b3 : Real.exp (-(lamb ρ κ σ * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have p1 := Real.exp_pos (-(lamf ρ κ σ * (T - t)))
  have p2 := Real.exp_pos (-(lamf ρ κ σ * T))
  have p3 := Real.exp_pos (-(lamb ρ κ σ * t))
  rw [abs_of_pos (by positivity), div_le_iff₀ hS]
  have q1 := mul_le_mul_of_nonneg_left b3 (mul_pos hf p2).le
  have q2 := mul_pos hf p1
  have q3 := mul_pos hb p2
  nlinarith

/-- Cochrane (2023), §20.2.5, p. 481 ("as price-stickiness is reduced … the no-jump equilibrium
multipliers converge smoothly to −1"): for `0 ≤ t < T`, `m_t → −1` as `κ → ∞`. -/
theorem multNJ_tendsto_kappa {σ ρ T t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) (htT : t < T) :
    Tendsto (fun κ => multNJ σ κ ρ T t) atTop (𝓝 (-1)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := (expNeg_lam_tendsto (ρ := ρ) hσ (sub_pos.2 htT)).2
  have h2 := (expNeg_lam_tendsto (ρ := ρ) hσ (by linarith : 0 < T)).2
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h3
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  exact multNJ_dist hσ hκ ht htT.le

/-- Cochrane (2023), §20.2.5, p. 481 ("or the period of the trap lengthens"): for fixed `t ≥ 0`,
the no-jump multiplier `m_t → −1` as `T → ∞`. -/
theorem multNJ_tendsto_T {σ κ ρ t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : 0 ≤ t) :
    Tendsto (fun T => multNJ σ κ ρ T t) atTop (𝓝 (-1)) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun T => Real.exp (-(lamf ρ κ σ * (T - t)))) atTop (𝓝 0) :=
    (tendsto_expNeg hf).comp ((tendsto_atTop_add_const_right atTop (-t) tendsto_id).congr
      fun T => by simp [sub_eq_add_neg])
  have h3 := h1.add (tendsto_expNeg hf)
  rw [add_zero] at h3
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h3
  filter_upwards [eventually_ge_atTop t] with T hT
  exact multNJ_dist hσ hκ ht hT

/-! ### Future spending (p. 481, "not shown") -/

/-- Cochrane (2023), §20.2.5, p. 481: spending `g` on the window `[a, a + Δ)` and `0`
otherwise. -/
noncomputable def gWindow (g a Δ t : ℝ) : ℝ := trapStep g (a + Δ) t - trapStep g a t

/-- Cochrane (2023), §20.2.5, p. 481: the output path of the standard equilibrium for spending
on the window `[a, a + Δ)` (no natural-rate shock; superposition of two traps). -/
noncomputable def windowX (σ κ ρ g a Δ t : ℝ) : ℝ := wX σ κ ρ (a + Δ) 0 g 0 t - wX σ κ ρ a 0 g 0 t

/-- Cochrane (2023), §20.2.5, p. 481: the corresponding inflation path. -/
noncomputable def windowPi (σ κ ρ g a Δ t : ℝ) : ℝ :=
  wPi σ κ ρ (a + Δ) 0 g 0 t - wPi σ κ ρ a 0 g 0 t

/-- Cochrane (2023), §20.2.5, p. 481: the window path solves (20.5)–(20.6) with `i = u_r = 0`
and disturbance `gWindow` (off `{a + Δ, a}`). -/
theorem window_isPath {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (g a Δ : ℝ) :
    IsPath σ ρ κ (fun _ => 0) (fun _ => 0) (gWindow g a Δ) ({a + Δ} ∪ {a})
      (windowX σ κ ρ g a Δ) (windowPi σ κ ρ g a Δ) := by
  have h1 := wPath_isPath (ρ := ρ) hκ hσ (a + Δ) 0 g 0
  have h2 := wPath_isPath (ρ := ρ) hκ hσ a 0 g 0
  refine ⟨h1.1.sub h2.1, h1.2.1.sub h2.2.1, fun t ht hS => ?_⟩
  have hS1 : t ∉ ({a + Δ} : Set ℝ) := fun hh => hS (Or.inl hh)
  have hS2 : t ∉ ({a} : Set ℝ) := fun hh => hS (Or.inr hh)
  obtain ⟨p1, q1⟩ := h1.2.2 t ht hS1
  obtain ⟨p2, q2⟩ := h2.2.2 t ht hS2
  have z1 : trapStep 0 (a + Δ) t = 0 := by simp [trapStep]
  have z2 : trapStep 0 a t = 0 := by simp [trapStep]
  rw [z1] at p1
  rw [z2] at p2
  exact ⟨(p1.sub p2).congr_deriv (by simp only [windowPi]; ring),
    (q1.sub q2).congr_deriv (by simp only [windowPi, windowX, gWindow]; ring)⟩

/-- Cochrane (2023), §20.2.5, p. 481: the window path vanishes from `a + Δ` on, so it is the
standard (`π_T = 0`) equilibrium for any trap end `T ≥ a + Δ`; it is bounded. -/
theorem window_after {σ κ ρ g a Δ t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hΔ : 0 ≤ Δ)
    (ht : a + Δ ≤ t) : windowPi σ κ ρ g a Δ t = 0 ∧ windowX σ κ ρ g a Δ t = 0 := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have k1 : ∀ T' : ℝ, T' ≤ t → wPi σ κ ρ T' 0 g 0 t = 0 ∧ wX σ κ ρ T' 0 g 0 t = 0 := by
    intro T' hT'
    rcases eq_or_lt_of_le hT' with h | h
    · subst h
      refine ⟨by simp [wPi, trapPi_zero hne], ?_⟩
      simp [wX, trapPi_zero hne, trapY_zero]
      field_simp
      ring
    · exact ⟨by simp [wPi, not_le.2 h], by simp [wX, not_le.2 h]⟩
  obtain ⟨a1, b1⟩ := k1 (a + Δ) ht
  obtain ⟨a2, b2⟩ := k1 a (by linarith)
  simp only [windowPi, windowX, a1, b1, a2, b2, sub_zero, and_self]

/-- Cochrane (2023), §20.2.5, p. 481: the window path is bounded. -/
theorem window_bdd {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (g a Δ : ℝ) :
    BddOnIci (windowX σ κ ρ g a Δ) ∧ BddOnIci (windowPi σ κ ρ g a Δ) := by
  obtain ⟨⟨K1, h1⟩, ⟨K2, h2⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ (a + Δ) 0 g 0
  obtain ⟨⟨K3, h3⟩, ⟨K4, h4⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ a 0 g 0
  exact ⟨⟨K1 + K3, fun t ht => (abs_sub _ _).trans (add_le_add (h1 t ht) (h3 t ht))⟩,
    ⟨K2 + K4, fun t ht => (abs_sub _ _).trans (add_le_add (h2 t ht) (h4 t ht))⟩⟩

/-- Cochrane (2023), §20.2.5, p. 481: **uniqueness**: for a trap end `T ≥ a + Δ`, any bounded
path for the window disturbance with `π_T = 0` is the window path. -/
theorem window_unique {σ κ ρ g a Δ T : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hΔ : 0 ≤ Δ)
    (hT : a + Δ ≤ T) (hT0 : 0 ≤ T) {x π : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (fun _ => 0) (gWindow g a Δ) ({a + Δ} ∪ {a}) x π)
    (hx : BddOnIci x) (hπ : BddOnIci π) (hπT : π T = 0) :
    ∀ t, 0 ≤ t → π t = windowPi σ κ ρ g a Δ t ∧ x t = windowX σ κ ρ g a Δ t := by
  obtain ⟨Kx, hKx⟩ := hx
  obtain ⟨Kπ, hKπ⟩ := hπ
  obtain ⟨⟨Kx0, hKx0⟩, ⟨Kπ0, hKπ0⟩⟩ := window_bdd (ρ := ρ) hσ hκ g a Δ
  have hS : ({a + Δ} ∪ {a} ∪ ({a + Δ} ∪ {a}) : Set ℝ).Countable :=
    ((Set.countable_singleton _).union (Set.countable_singleton _)).union
      ((Set.countable_singleton _).union (Set.countable_singleton _))
  have hh := homog_bdd hσ hκ hS (h.sub (window_isPath (ρ := ρ) hσ hκ g a Δ))
    ⟨Kx + Kx0, fun t ht => (abs_sub _ _).trans (add_le_add (hKx t ht) (hKx0 t ht))⟩
    ⟨Kπ + Kπ0, fun t ht => (abs_sub _ _).trans (add_le_add (hKπ t ht) (hKπ0 t ht))⟩
  have hc : π 0 - windowPi σ κ ρ g a Δ 0 = 0 := by
    have := (hh T hT0).1
    rw [hπT, (window_after (ρ := ρ) hσ hκ hΔ hT).1, sub_zero] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h (Real.exp_pos _).ne'
    · exact h
  intro t ht
  obtain ⟨h1, h2⟩ := hh t ht
  rw [hc, mul_zero] at h1
  have h1' : π t = windowPi σ κ ρ g a Δ t := by linarith
  refine ⟨h1', ?_⟩
  rw [h1', sub_self, mul_zero] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h hκ.ne'
  · linarith

/-- Cochrane (2023), §20.2.5, p. 481: the time-0 multiplier of window spending,
`h(a + Δ) − h(a)`. -/
noncomputable def windowMult (σ κ ρ a Δ : ℝ) : ℝ :=
  hh (lamf ρ κ σ) (lamb ρ κ σ) (a + Δ) - hh (lamf ρ κ σ) (lamb ρ κ σ) a

/-- Cochrane (2023), §20.2.5, p. 481: time-0 output responds to window spending by
`x_0 = g · windowMult` (`a ≥ 0`, `Δ ≥ 0`). -/
theorem window_x0 {σ κ ρ g a Δ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ha : 0 ≤ a) (hΔ : 0 ≤ Δ) :
    windowX σ κ ρ g a Δ 0 = g * windowMult σ κ ρ a Δ := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  simp only [windowX, windowMult, wX, ha, (by linarith : (0 : ℝ) ≤ a + Δ), ↓reduceIte, trapPi,
    trapY, hh, kk, sub_zero]
  field_simp
  ring

/-- Cochrane (2023), §20.2.5, p. 481: the window multiplier in closed form,
`[λ^f(e^{λ^b Δ} − 1)e^{λ^b a} − λ^b(1 − e^{−λ^f Δ})e^{−λ^f a}]/(λ^f + λ^b)`. -/
theorem windowMult_eq (σ κ ρ a Δ : ℝ) :
    windowMult σ κ ρ a Δ = (lamf ρ κ σ * (Real.exp (lamb ρ κ σ * Δ) - 1) *
      Real.exp (lamb ρ κ σ * a) - lamb ρ κ σ * (1 - Real.exp (-(lamf ρ κ σ * Δ))) *
        Real.exp (-(lamf ρ κ σ * a))) / (lamf ρ κ σ + lamb ρ κ σ) := by
  have e1 : Real.exp (lamb ρ κ σ * (a + Δ)) =
      Real.exp (lamb ρ κ σ * Δ) * Real.exp (lamb ρ κ σ * a) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(lamf ρ κ σ * (a + Δ))) =
      Real.exp (-(lamf ρ κ σ * Δ)) * Real.exp (-(lamf ρ κ σ * a)) := by
    rw [← Real.exp_add]; ring_nf
  simp only [windowMult, hh, e1, e2]
  ring

/-- Cochrane (2023), §20.2.5, p. 481 ("spending … in the future is exponentially more effective
than spending today"): for a window of fixed length `Δ > 0`, the time-0 multiplier is strictly
increasing in the window's start date `a`. -/
theorem windowMult_strictMono {σ κ ρ Δ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hΔ : 0 < Δ) :
    StrictMono fun a => windowMult σ κ ρ a Δ := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have c1 : 0 < lamf ρ κ σ * (Real.exp (lamb ρ κ σ * Δ) - 1) := by
    have : 1 < Real.exp (lamb ρ κ σ * Δ) := Real.one_lt_exp_iff.2 (by positivity)
    nlinarith
  have c2 : 0 < lamb ρ κ σ * (1 - Real.exp (-(lamf ρ κ σ * Δ))) := by
    have : Real.exp (-(lamf ρ κ σ * Δ)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    nlinarith
  intro a1 a2 hlt
  simp only [windowMult_eq]
  rw [div_lt_div_iff_of_pos_right hS]
  have e1 : Real.exp (lamb ρ κ σ * a1) < Real.exp (lamb ρ κ σ * a2) :=
    Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hlt hb)
  have e2 : Real.exp (-(lamf ρ κ σ * a2)) < Real.exp (-(lamf ρ κ σ * a1)) :=
    Real.exp_lt_exp.2 (by nlinarith)
  nlinarith [mul_lt_mul_of_pos_left e1 c1, mul_lt_mul_of_pos_left e2 c2]

/-- Cochrane (2023), §20.2.5, p. 481: the window multiplier grows without bound (exponentially)
as the window moves into the future. -/
theorem windowMult_tendsto {σ κ ρ Δ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hΔ : 0 < Δ) :
    Tendsto (fun a => windowMult σ κ ρ a Δ) atTop atTop := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have c1 : 0 < lamf ρ κ σ * (Real.exp (lamb ρ κ σ * Δ) - 1) := by
    have : 1 < Real.exp (lamb ρ κ σ * Δ) := Real.one_lt_exp_iff.2 (by positivity)
    nlinarith
  have hc0 : 0 ≤ lamb ρ κ σ * (1 - Real.exp (-(lamf ρ κ σ * Δ))) := by
    have : Real.exp (-(lamf ρ κ σ * Δ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith
  have h1 : Tendsto (fun a => (lamf ρ κ σ * (Real.exp (lamb ρ κ σ * Δ) - 1) *
      Real.exp (lamb ρ κ σ * a) - lamb ρ κ σ) / (lamf ρ κ σ + lamb ρ κ σ)) atTop atTop :=
    (tendsto_atTop_add_const_right _ _ ((tendsto_expPos hb).const_mul_atTop c1)).atTop_div_const
      hS
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_ge_atTop 0] with a ha
  rw [windowMult_eq, div_le_div_iff_of_pos_right hS]
  have : Real.exp (-(lamf ρ κ σ * a)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hc1 : lamb ρ κ σ * (1 - Real.exp (-(lamf ρ κ σ * Δ))) ≤ lamb ρ κ σ := by
    have := Real.exp_pos (-(lamf ρ κ σ * Δ))
    nlinarith
  nlinarith [Real.exp_pos (-(lamf ρ κ σ * a))]

end Cochrane.ZeroBound.Multipliers
