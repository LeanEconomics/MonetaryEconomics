/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.LinksTidy
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Continuous-time transversality with discontinuous forcing

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.4.2, eq. (5.44), p. 140
(`NonlinearCT.tvc_iff_integral`) and §5.7.1, eq. (5.95), p. 165 (`CTSimple.tvc_iff_forward`).

`NonlinearCT.tvc_iff_integral` assumes a surplus continuous on `[0, ∞)`; `CTSimple`'s flows
`v' = a v − f` need only an integrable discounted forcing, so `f = a v − v'` may be
discontinuous. `LinksTidy.forward_hyps_discontinuous` only had a witness discontinuous at the
valuation date. This module builds an **interior** witness and closes the gap.

## 1. A Darboux-type interior witness

`wv τ = (τ − 1)² sin(1/(τ − 1))` is differentiable everywhere (`wv_hasDerivAt`), with derivative
`wdv` discontinuous at `τ = 1`. With `a = 2` the forcing `wf = 2 wv − wv'` satisfies every
hypothesis of `CTSimple.tvc_iff_forward` at `t = 0` and NonlinearCT's flow
(`witness_ctsimple_hyps`, `witness_flow`), but it has **no** limit from the right at the
interior point `1` (`wf_no_right_limit`: along `1 + 1/(2πn)` it tends to `1`, along
`1 + 1/(2πn + π)` to `−1`). Hence (`witness_not_covered`) for every valuation date `t' ∈ [0, 1]`,
every surplus `s` and debt path `b` that put these data into NonlinearCT's form
(`b(u) = wv(t' + u)`, `db/du = 2b − s`), `s` is not continuous on `[0, ∞)`:
`NonlinearCT.tvc_iff_integral` cannot be applied.

## 2. NonlinearCT's route for integrable forcing

* `flow_integrated_int`, `tvc_iff_integral_int`: (5.44) and the transversality theorem proved by
  NonlinearCT's own argument (integrate the flow forward) with merely integrable discounted
  forcing; `IntegralIntStmt`, `integralIntStmt_holds`.
* `forwardStmt_of_integralIntStmt`: **the full `CTSimple.tvc_iff_forward` (`LinksTidy.ForwardStmt`,
  arbitrary integrable forcing, no derivative at the valuation date) follows from
  `IntegralIntStmt`**: apply it at every later date `t' > t` to the flow minus the homogeneous
  solution `c e^{a u}` that makes the valuation equation hold, read off the limit of the
  discounted debt, and let `t' ↓ t`. `tvc_iff_forward_of_integralInt` is the instance; it covers
  the witness (`witness_valuation`: its transversality condition holds, so
  `wv(0) = ∫_0^∞ e^{−2τ} wf(τ) dτ`).
-/

namespace Cochrane.StickyPriceFiscal.TidyR5TVC

open Filter Topology MeasureTheory

/-! ### 1. The interior witness -/

/-- Cochrane (2023), (5.95), p. 165 (witness): the path `wv τ = (τ − 1)² sin(1/(τ − 1))`
(`wv 1 = 0`). -/
noncomputable def wv (τ : ℝ) : ℝ := (τ - 1) ^ 2 * Real.sin (τ - 1)⁻¹

/-- Cochrane (2023), (5.95), p. 165 (witness): the derivative of `wv`,
`2(τ − 1) sin(1/(τ − 1)) − cos(1/(τ − 1))` off `τ = 1`, and `0` at `τ = 1`. -/
noncomputable def wdv (τ : ℝ) : ℝ :=
  if τ = 1 then 0 else 2 * (τ - 1) * Real.sin (τ - 1)⁻¹ - Real.cos (τ - 1)⁻¹

/-- Cochrane (2023), (5.95), p. 165 (witness): the forcing `f = a v − v'` with `a = 2`. -/
noncomputable def wf (τ : ℝ) : ℝ := 2 * wv τ - wdv τ

/-- Cochrane (2023), (5.95), p. 165 (witness): `wv` has derivative `wdv τ` at every `τ`
(at `τ = 1` because `|wv(1 + h)| ≤ h²`). -/
theorem wv_hasDerivAt (τ : ℝ) : HasDerivAt wv (wdv τ) τ := by
  by_cases hτ : τ = 1
  · subst hτ
    simp only [wdv, ↓reduceIte]
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have hb : (fun h : ℝ => wv (1 + h) - wv 1 - h • (0 : ℝ)) =O[𝓝 0] fun h : ℝ => h ^ 2 := by
      refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h => ?_)
      simp only [wv, sub_self, smul_zero, sub_zero, add_sub_cancel_left, Real.norm_eq_abs,
        one_mul]
      rw [show (0 : ℝ) ^ 2 * Real.sin 0⁻¹ = 0 by simp, sub_zero, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
    exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))
  · have h1 : τ - 1 ≠ 0 := sub_ne_zero.mpr hτ
    have hs : HasDerivAt (fun u => u - 1) 1 τ := (hasDerivAt_id τ).sub_const 1
    have hinv : HasDerivAt (fun u => (u - 1)⁻¹) (-1 / (τ - 1) ^ 2) τ := hs.inv h1
    have hsin := hinv.sin
    have hsq : HasDerivAt (fun u => (u - 1) ^ 2) (2 * (τ - 1)) τ := by
      refine (hs.pow 2).congr_deriv ?_
      norm_num
    refine (hsq.mul hsin).congr_deriv ?_
    simp only [wdv, hτ, ↓reduceIte]
    field_simp
    ring

/-- Cochrane (2023), (5.95), p. 165 (witness): `wv` is continuous. -/
theorem wv_continuous : Continuous wv :=
  continuous_iff_continuousAt.mpr fun τ => (wv_hasDerivAt τ).continuousAt

/-- Cochrane (2023), (5.95), p. 165 (witness): `deriv wv = wdv`, so `wdv` and `wf` are
measurable. -/
theorem wf_measurable : Measurable wf := by
  have hd : deriv wv = wdv := funext fun τ => (wv_hasDerivAt τ).deriv
  have hm : Measurable wdv := hd ▸ measurable_deriv wv
  exact (wv_continuous.measurable.const_mul 2).sub hm

/-- Cochrane (2023), (5.95), p. 165 (witness): `|wv τ| ≤ (τ − 1)²` and
`|wdv τ| ≤ 2|τ − 1| + 1`. -/
theorem wv_wdv_bound (τ : ℝ) : |wv τ| ≤ (τ - 1) ^ 2 ∧ |wdv τ| ≤ 2 * |τ - 1| + 1 := by
  constructor
  · rw [wv, abs_mul, abs_pow]
    simp only [sq_abs]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  · unfold wdv
    split_ifs
    · simp only [abs_zero]; positivity
    · refine (abs_sub _ _).trans (add_le_add ?_ (Real.abs_cos_le_one _))
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)

/-- Cochrane (2023), §5.7.1, p. 165 (tool): `(τ + 2)² ≤ 4 e^τ` for `τ ≥ 0`. -/
theorem sq_le_four_exp {τ : ℝ} (hτ : 0 ≤ τ) : (τ + 2) ^ 2 ≤ 4 * Real.exp τ := by
  have h := Real.add_one_le_exp (τ / 2)
  have h2 : (τ / 2 + 1) ^ 2 ≤ Real.exp (τ / 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) h 2
  rw [← Real.exp_nat_mul] at h2
  have : ((2 : ℕ) : ℝ) * (τ / 2) = τ := by push_cast; ring
  rw [this] at h2
  nlinarith

/-- Cochrane (2023), (5.95), p. 165 (witness): `|e^{−2τ} wf τ| ≤ 8 e^{−τ}` for `τ ≥ 0`. -/
theorem wf_disc_bound {τ : ℝ} (hτ : 0 ≤ τ) :
    |Real.exp (-(2 * τ)) * wf τ| ≤ 8 * Real.exp (-τ) := by
  obtain ⟨b1, b2⟩ := wv_wdv_bound τ
  have hτ1 : |τ - 1| ≤ τ + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hf : |wf τ| ≤ 2 * (τ + 2) ^ 2 := by
    unfold wf
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_two]
    have : (τ - 1) ^ 2 ≤ (τ + 1) ^ 2 := by
      rw [← sq_abs (τ - 1)]
      exact pow_le_pow_left₀ (abs_nonneg _) hτ1 2
    nlinarith
  have he := sq_le_four_exp hτ
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hsplit : Real.exp (-(2 * τ)) * Real.exp τ = Real.exp (-τ) := by
    rw [← Real.exp_add]; ring_nf
  calc Real.exp (-(2 * τ)) * |wf τ| ≤ Real.exp (-(2 * τ)) * (2 * (4 * Real.exp τ)) :=
        mul_le_mul_of_nonneg_left (hf.trans (by linarith)) (Real.exp_pos _).le
    _ = 8 * Real.exp (-τ) := by rw [← hsplit]; ring

/-- Cochrane (2023), (5.95), p. 165 (witness): `e^{−2τ} wf τ` is integrable on `(0, ∞)`. -/
theorem wf_integrable : IntegrableOn (fun τ => Real.exp (-(2 * τ)) * wf τ) (Set.Ioi 0) := by
  have hint : IntegrableOn (fun τ : ℝ => 8 * Real.exp (-1 * τ)) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 one_pos).const_mul 8
  refine Integrable.mono' hint
    ((by fun_prop : Continuous fun τ : ℝ => Real.exp (-(2 * τ))).measurable.mul
      wf_measurable).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : (0 : ℝ) < τ) => ?_)
  rw [Real.norm_eq_abs, neg_one_mul]
  exact wf_disc_bound hτ.le

/-- Cochrane (2023), (5.95), p. 165 (witness): along `x_n = 1 + 1/(2πn)`, `wdv x_n = −1`; along
`y_n = 1 + 1/(2πn + π)`, `wdv y_n = 1` (`n ≥ 1`). -/
theorem wdv_seq (n : ℕ) (hn : 1 ≤ n) :
    wdv (1 + ((n : ℝ) * (2 * Real.pi))⁻¹) = -1 ∧
      wdv (1 + ((n : ℝ) * (2 * Real.pi) + Real.pi)⁻¹) = 1 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hx : (0 : ℝ) < (n : ℝ) * (2 * Real.pi) := by positivity
  have hy : (0 : ℝ) < (n : ℝ) * (2 * Real.pi) + Real.pi := by positivity
  constructor
  · have hne : 1 + ((n : ℝ) * (2 * Real.pi))⁻¹ ≠ 1 := by
      intro h; have : ((n : ℝ) * (2 * Real.pi))⁻¹ = 0 := by linarith
      exact (inv_pos.mpr hx).ne' this
    simp only [wdv, hne, ↓reduceIte, add_sub_cancel_left, inv_inv, Real.cos_nat_mul_two_pi]
    have : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
      rw [show (n : ℝ) * (2 * Real.pi) = ((2 * n : ℕ) : ℝ) * Real.pi by push_cast; ring]
      exact Real.sin_nat_mul_pi _
    rw [this]
    ring
  · have hne : 1 + ((n : ℝ) * (2 * Real.pi) + Real.pi)⁻¹ ≠ 1 := by
      intro h; have : ((n : ℝ) * (2 * Real.pi) + Real.pi)⁻¹ = 0 := by linarith
      exact (inv_pos.mpr hy).ne' this
    simp only [wdv, hne, ↓reduceIte, add_sub_cancel_left, inv_inv, Real.cos_add_pi,
      Real.sin_add_pi, Real.cos_nat_mul_two_pi]
    have : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
      rw [show (n : ℝ) * (2 * Real.pi) = ((2 * n : ℕ) : ℝ) * Real.pi by push_cast; ring]
      exact Real.sin_nat_mul_pi _
    rw [this]
    ring

/-- Cochrane (2023), (5.95), p. 165 (witness): **the forcing has no limit from the right at the
interior point `1`**: no `c` has `wf τ → c` as `τ → 1⁺`. -/
theorem wf_no_right_limit (c : ℝ) : ¬ Tendsto wf (𝓝[>] 1) (𝓝 c) := by
  intro hc
  have hw1 : wv 1 = 0 := by simp [wv]
  -- the two sequences
  have hxs : Tendsto (fun n : ℕ => ((n : ℝ) * (2 * Real.pi))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity))
  have hys : Tendsto (fun n : ℕ => ((n : ℝ) * (2 * Real.pi) + Real.pi)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)))
  have hwithin : ∀ u : ℕ → ℝ, Tendsto u atTop (𝓝 0) → (∀ n, 1 ≤ n → 0 < u n) →
      Tendsto (fun n => 1 + u n) atTop (𝓝[>] 1) := by
    intro u hu hpos
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using hu.const_add 1
    · filter_upwards [eventually_ge_atTop 1] with n hn
      simp only [Set.mem_Ioi]
      linarith [hpos n hn]
  have hlim : ∀ (u : ℕ → ℝ) (d : ℝ), Tendsto u atTop (𝓝 0) → (∀ n, 1 ≤ n → 0 < u n) →
      (∀ n, 1 ≤ n → wdv (1 + u n) = d) → c = 2 * 0 - d := by
    intro u d hu hpos hd
    have h1 := hc.comp (hwithin u hu hpos)
    have hv : Tendsto (fun n => wv (1 + u n)) atTop (𝓝 0) := by
      have := (wv_continuous.tendsto 1).comp (by simpa using hu.const_add 1 :
        Tendsto (fun n => 1 + u n) atTop (𝓝 1))
      rwa [hw1] at this
    have h2 : Tendsto (fun n => wf (1 + u n)) atTop (𝓝 (2 * 0 - d)) := by
      refine ((hv.const_mul 2).sub_const d).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      simp only [wf, hd n hn]
    exact tendsto_nhds_unique h1 h2
  have hp1 : ∀ n : ℕ, 1 ≤ n → 0 < ((n : ℝ) * (2 * Real.pi))⁻¹ := fun n hn => by
    have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    positivity
  have hp2 : ∀ n : ℕ, 1 ≤ n → 0 < ((n : ℝ) * (2 * Real.pi) + Real.pi)⁻¹ := fun n hn => by
    have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    positivity
  have e1 := hlim _ (-1) hxs hp1 (fun n hn => (wdv_seq n hn).1)
  have e2 := hlim _ 1 hys hp2 (fun n hn => (wdv_seq n hn).2)
  linarith

/-- Cochrane (2023), (5.95), p. 165 (witness): `wf` is not continuous at the interior point `1`. -/
theorem wf_not_continuousAt : ¬ ContinuousAt wf 1 := fun h =>
  wf_no_right_limit (wf 1) (h.tendsto.mono_left nhdsWithin_le_nhds)

/-- Cochrane (2023), (5.95), p. 165: **the witness satisfies CTSimple's hypotheses** at `a = 2`,
`t = 0` (continuity on `[0, ∞)`, the flow on `(0, ∞)`, integrable discounted forcing), and its
forcing is discontinuous at the interior point `1 ∈ (0, ∞)`. -/
theorem witness_ctsimple_hyps :
    ContinuousOn wv (Set.Ici 0) ∧ (∀ τ, 0 < τ → HasDerivAt wv (2 * wv τ - wf τ) τ) ∧
      IntegrableOn (fun τ => Real.exp (-(2 * τ)) * wf τ) (Set.Ioi 0) ∧
      (1 : ℝ) ∈ Set.Ioi 0 ∧ ¬ ContinuousAt wf 1 := by
  refine ⟨wv_continuous.continuousOn, fun τ _ => ?_, wf_integrable, by norm_num,
    wf_not_continuousAt⟩
  have : 2 * wv τ - wf τ = wdv τ := by unfold wf; ring
  rw [this]
  exact wv_hasDerivAt τ

/-- Cochrane (2023), (5.43), p. 140: the witness even satisfies NonlinearCT's flow
`db/dt = 2b − s` at every `τ ≥ 0` with `b = wv`, `s = wf`. -/
theorem witness_flow : NonlinearCT.Flow 2 wf wv := fun τ _ => by
  have : 2 * wv τ - wf τ = wdv τ := by unfold wf; ring
  rw [this]
  exact wv_hasDerivAt τ

/-- Cochrane (2023), (5.44), p. 140 and (5.95), p. 165: **`NonlinearCT.tvc_iff_integral` does not
cover the witness**: for every shift `t' ≤ 1` (in particular every valuation date
`t' ∈ [0, 1]`), every surplus `s` and debt path `b` with `b(u) = wv(t' + u)` for `u ≥ 0` and
NonlinearCT's flow `db/du = 2b − s`, the surplus `s` is not continuous on `[0, ∞)` (the
continuity hypothesis of `NonlinearCT.tvc_iff_integral` fails). -/
theorem witness_not_covered {t' : ℝ} (ht1 : t' ≤ 1) (s b : ℝ → ℝ)
    (hb : ∀ u, 0 ≤ u → b u = wv (t' + u)) (hflow : NonlinearCT.Flow 2 s b) :
    ¬ ContinuousOn s (Set.Ici 0) := by
  intro hs
  -- on `(0, ∞)` the flow pins `s(u) = wf(t' + u)`
  have hsu : ∀ u, 0 < u → s u = wf (t' + u) := by
    intro u hu
    have hev : b =ᶠ[𝓝 u] fun y => wv (t' + y) := by
      filter_upwards [lt_mem_nhds hu] with y hy
      exact hb y hy.le
    have h1 : HasDerivAt (fun y => wv (t' + y)) (2 * b u - s u) u :=
      (hflow u hu.le).congr_of_eventuallyEq hev.symm
    have h2 : HasDerivAt (fun y => wv (t' + y)) (wdv (t' + u)) u :=
      HasDerivAt.comp_const_add t' u (wv_hasDerivAt (t' + u))
    have := h1.unique h2
    rw [hb u hu.le] at this
    unfold wf
    linarith
  set u0 := 1 - t' with hu0
  have hu00 : 0 ≤ u0 := by linarith
  have hc : Tendsto s (𝓝[>] u0) (𝓝 (s u0)) :=
    ((hs u0 (Set.mem_Ici.mpr hu00)).mono
      (fun y (hy : u0 < y) => Set.mem_Ici.mpr (by linarith))).tendsto
  have hmap : Tendsto (fun x => x - t') (𝓝[>] 1) (𝓝[>] u0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_id.sub continuous_const).tendsto (1 : ℝ) :
        Tendsto (fun x : ℝ => x - t') (𝓝 1) (𝓝 (1 - t')))
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Ioi] at hx ⊢
      linarith
  have hcomp := hc.comp hmap
  refine wf_no_right_limit (s u0) (hcomp.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Function.comp_apply, Set.mem_Ioi] at hx ⊢
  rw [hsu (x - t') (by linarith)]
  ring_nf

/-! ### 2. NonlinearCT's route with integrable forcing -/

/-- Cochrane (2023), eq. (5.44), p. 140, **with integrable forcing** (NonlinearCT's argument
without continuity): for a flow `db/dt = c b − f` on `[0, ∞)`, `t, T ≥ 0` and `e^{−cτ} f_{t+τ}`
interval integrable on `[0, T]`, `e^{−cT} b_{t+T} = b_t − ∫_0^T e^{−cτ} f_{t+τ} dτ`. -/
theorem flow_integrated_int {c : ℝ} {f b : ℝ → ℝ} (hb : NonlinearCT.Flow c f b) {t : ℝ}
    (ht : 0 ≤ t) {T : ℝ} (hT : 0 ≤ T)
    (hint : IntervalIntegrable (fun τ => Real.exp (-c * τ) * f (t + τ)) volume 0 T) :
    Real.exp (-c * T) * b (t + T) =
      b t - ∫ τ in (0 : ℝ)..T, Real.exp (-c * τ) * f (t + τ) := by
  have hderiv : ∀ x ∈ Set.uIcc 0 T, HasDerivAt (fun τ => Real.exp (-c * τ) * b (t + τ))
      (-(Real.exp (-c * x) * f (t + x))) x := by
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    have h1 : HasDerivAt (fun τ => Real.exp (-c * τ)) (Real.exp (-c * x) * (-c)) x := by
      have := ((hasDerivAt_id x).const_mul (-c)).exp
      simpa using this
    have h2 : HasDerivAt (fun τ => b (t + τ)) (c * b (t + x) - f (t + x)) x :=
      HasDerivAt.comp_const_add t x (hb (t + x) (by linarith [hx.1]))
    convert h1.mul h2 using 1
    ring
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint.neg
  rw [intervalIntegral.integral_neg] at this
  simp only [mul_zero, Real.exp_zero, one_mul, add_zero] at this
  linarith

/-- Cochrane (2023), (5.44), p. 140, **with integrable forcing**: for a flow `db/dt = rb − s` on
`[0, ∞)`, `t ≥ 0` and `e^{−rτ} s_{t+τ}` integrable on `(0, ∞)`, the transversality condition
holds iff `b_t = ∫_0^∞ e^{−rτ} s_{t+τ} dτ` (no continuity of `s`). -/
theorem tvc_iff_integral_int {r : ℝ} {s b : ℝ → ℝ} (hb : NonlinearCT.Flow r s b) {t : ℝ}
    (ht : 0 ≤ t) (hint : IntegrableOn (fun τ => Real.exp (-r * τ) * s (t + τ)) (Set.Ioi 0)) :
    Tendsto (fun T => Real.exp (-r * T) * b (t + T)) atTop (𝓝 0) ↔
      b t = ∫ τ in Set.Ioi 0, Real.exp (-r * τ) * s (t + τ) := by
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hev : (fun T => Real.exp (-r * T) * b (t + T)) =ᶠ[atTop]
      fun T => b t - ∫ τ in (0 : ℝ)..T, Real.exp (-r * τ) * s (t + τ) := by
    filter_upwards [eventually_ge_atTop 0] with T hT
    exact flow_integrated_int hb ht hT ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
      (hint.mono_set Set.Ioc_subset_Ioi_self))
  rw [tendsto_congr' hev]
  constructor
  · intro h
    have h2 := (tendsto_const_nhds (x := b t)).sub h
    simp only [sub_sub_cancel, sub_zero] at h2
    exact tendsto_nhds_unique h2 hlim
  · intro h
    have := (tendsto_const_nhds (x := b t)).sub hlim
    rwa [← h, sub_self] at this

/-- Cochrane (2023), (5.44), p. 140: the statement of `NonlinearCT.tvc_iff_integral` with the
continuity of the surplus dropped (integrable discounted surplus only). -/
def IntegralIntStmt : Prop :=
  ∀ (r : ℝ) (s b : ℝ → ℝ), NonlinearCT.Flow r s b → ∀ t : ℝ, 0 ≤ t →
    IntegrableOn (fun τ => Real.exp (-r * τ) * s (t + τ)) (Set.Ioi 0) →
    (Tendsto (fun T => Real.exp (-r * T) * b (t + T)) atTop (𝓝 0) ↔
      b t = ∫ τ in Set.Ioi 0, Real.exp (-r * τ) * s (t + τ))

/-- Cochrane (2023), (5.44), p. 140: `IntegralIntStmt` holds (`tvc_iff_integral_int`). -/
theorem integralIntStmt_holds : IntegralIntStmt :=
  fun _ _ _ hb _ ht hint => tvc_iff_integral_int hb ht hint

/-- Cochrane (2023), (5.44) and (5.95) (tool): a limit of the relative-time discounted path from
date `t'` gives the absolute-time limit, `e^{−aT} v_{t'+T} → c ⇒ e^{−aT} v_T → e^{−at'} c`. -/
theorem tvc_shift_limit {a t' c : ℝ} {v : ℝ → ℝ}
    (h : Tendsto (fun T => Real.exp (-a * T) * v (t' + T)) atTop (𝓝 c)) :
    Tendsto (fun T => Real.exp (-(a * T)) * v T) atTop (𝓝 (Real.exp (-(a * t')) * c)) := by
  have hs : Tendsto (fun T : ℝ => -t' + T) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_id
  have h2 := (h.comp hs).const_mul (Real.exp (-(a * t')))
  refine h2.congr fun T => ?_
  simp only [Function.comp_apply]
  rw [show t' + (-t' + T) = T by ring, ← mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), §5.7.1, p. 165 (tool): for `g` integrable on `(t, ∞)`,
`∫_{t'}^∞ g → ∫_t^∞ g` as `t' → t⁺`. -/
theorem tendsto_integral_Ioi_right {g : ℝ → ℝ} {t : ℝ} (hg : IntegrableOn g (Set.Ioi t)) :
    Tendsto (fun t' => ∫ τ in Set.Ioi t', g τ) (𝓝[>] t) (𝓝 (∫ τ in Set.Ioi t, g τ)) := by
  have hII : IntervalIntegrable g volume (min t t) (max t (t + 1)) := by
    rw [min_self, max_eq_right (by linarith)]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2
      (hg.mono_set Set.Ioc_subset_Ioi_self)
  have hcw := intervalIntegral.continuousWithinAt_primitive (μ := volume) (a := t) (b₀ := t)
    (b₁ := t) (b₂ := t + 1) (by simp) hII
  have hmem : Set.Icc t (t + 1) ∈ 𝓝[>] t :=
    mem_of_superset (Ioo_mem_nhdsGT (by linarith : t < t + 1)) Set.Ioo_subset_Icc_self
  have hP : Tendsto (fun b => ∫ x in t..b, g x) (𝓝[>] t) (𝓝 0) := by
    have := (hcw.mono_of_mem_nhdsWithin hmem).tendsto
    simpa using this
  have := (tendsto_const_nhds (x := ∫ τ in Set.Ioi t, g τ)).sub hP
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t' ht'
  have ht'' : t ≤ t' := le_of_lt ht'
  rw [intervalIntegral.integral_of_le ht'', ← Set.Ioc_union_Ioi_eq_Ioi ht'',
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hg.mono_set Set.Ioc_subset_Ioi_self) (hg.mono_set (Set.Ioi_subset_Ioi ht''))]
  ring

/-- Cochrane (2023), (5.44) and (5.95): **`CTSimple.tvc_iff_forward` in full (any integrable
forcing, continuous or not, no derivative at the valuation date) follows from
`IntegralIntStmt`**, NonlinearCT's statement with integrable forcing. -/
theorem forwardStmt_of_integralIntStmt (H : IntegralIntStmt) : LinksTidy.ForwardStmt := by
  intro v f a t hc hd hint
  set g : ℝ → ℝ := fun τ => Real.exp (-(a * τ)) * f τ with hg
  -- Step 1: from every later date `t'`, the discounted debt converges to `e^{−at'}v_{t'} − G(t')`
  have step1 : ∀ t', t < t' → Tendsto (fun T => Real.exp (-(a * T)) * v T) atTop
      (𝓝 (Real.exp (-(a * t')) * v t' - ∫ τ in Set.Ioi t', g τ)) := by
    intro t' htt'
    set F := ∫ τ in Set.Ioi 0, Real.exp (-a * τ) * f (t' + τ) with hF
    set c := v t' - F with hcdef
    set b : ℝ → ℝ := fun u => v (t' + u) - c * Real.exp (a * u) with hbdef
    have hflow : NonlinearCT.Flow a (fun u => f (t' + u)) b := by
      intro u hu
      have h1 : HasDerivAt (fun y => v (t' + y)) (a * v (t' + u) - f (t' + u)) u :=
        HasDerivAt.comp_const_add t' u (hd (t' + u) (by linarith))
      have h2 := (CTSimple.hasDerivAt_expPos a u).const_mul c
      convert HasDerivAt.sub h1 h2 using 1
      simp only [hbdef]
      ring
    have hint' : IntegrableOn (fun τ => Real.exp (-a * τ) * (fun u => f (t' + u)) (0 + τ))
        (Set.Ioi 0) := by
      simp only [zero_add]
      exact (LinksTidy.integrable_rel_iff_abs a t' f).2
        (hint.mono_set (Set.Ioi_subset_Ioi htt'.le))
    have key := (H a (fun u => f (t' + u)) b hflow 0 le_rfl hint').2 (by
      simp only [hbdef, zero_add, add_zero, mul_zero, Real.exp_zero, mul_one, hcdef]
      ring)
    have hlim : Tendsto (fun T => Real.exp (-a * T) * v (t' + T)) atTop (𝓝 c) := by
      have := key.add_const c
      rw [zero_add] at this
      refine this.congr fun T => ?_
      simp only [hbdef, zero_add]
      have hee : Real.exp (-a * T) * Real.exp (a * T) = 1 := by rw [← Real.exp_add]; simp
      linear_combination (-c) * hee
    have hres := tvc_shift_limit hlim
    have hval : Real.exp (-(a * t')) * c =
        Real.exp (-(a * t')) * v t' - ∫ τ in Set.Ioi t', g τ := by
      rw [hcdef, mul_sub, hF, (LinksTidy.valuation_rel_eq a t' f).1,
        (LinksTidy.valuation_rel_eq a t' f).2, ← mul_assoc, ← Real.exp_add]
      simp [hg]
    rwa [hval] at hres
  -- Step 2: the limit `L` is pinned at `t` by letting `t' ↓ t`
  set L := Real.exp (-(a * (t + 1))) * v (t + 1) - ∫ τ in Set.Ioi (t + 1), g τ with hL
  have hconst : ∀ t', t < t' → Real.exp (-(a * t')) * v t' - ∫ τ in Set.Ioi t', g τ = L :=
    fun t' ht' => tendsto_nhds_unique (step1 t' ht') (step1 (t + 1) (by linarith))
  have hcont : Tendsto (fun t' => Real.exp (-(a * t')) * v t' - ∫ τ in Set.Ioi t', g τ)
      (𝓝[>] t) (𝓝 (Real.exp (-(a * t)) * v t - ∫ τ in Set.Ioi t, g τ)) := by
    have he : ContinuousWithinAt (fun u => Real.exp (-(a * u)) * v u) (Set.Ioi t) t :=
      (((by fun_prop : Continuous fun u : ℝ => Real.exp (-(a * u))).continuousWithinAt).mul
        (hc t (Set.mem_Ici.mpr le_rfl))).mono Set.Ioi_subset_Ici_self
    exact he.tendsto.sub (tendsto_integral_Ioi_right hint)
  have hLt : L = Real.exp (-(a * t)) * v t - ∫ τ in Set.Ioi t, g τ := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hcont
    filter_upwards [self_mem_nhdsWithin] with t' ht'
    exact (hconst t' ht').symm
  have hlimL : Tendsto (fun T => Real.exp (-(a * T)) * v T) atTop (𝓝 L) := by
    have := step1 (t + 1) (by linarith)
    rwa [← hL] at this
  -- Step 3: the transversality condition holds iff `L = 0` iff the valuation equation holds
  have hpos := Real.exp_pos (a * t)
  have hinv : Real.exp (a * t) * Real.exp (-(a * t)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [CTSimple.integral_exp_shift]
  constructor
  · intro h0
    have hL0 : L = 0 := tendsto_nhds_unique hlimL h0
    rw [hL0] at hLt
    have : Real.exp (-(a * t)) * v t = ∫ τ in Set.Ioi t, g τ := by linarith
    rw [← this, ← mul_assoc, hinv, one_mul]
  · intro hv
    have hL0 : L = 0 := by
      rw [hLt, hv, ← mul_assoc, mul_comm (Real.exp (-(a * t))), hinv, one_mul]
      simp [hg]
    rwa [hL0] at hlimL

/-- Cochrane (2023), (5.95), p. 165: `CTSimple.tvc_iff_forward` for **any** integrable forcing
(including discontinuous forcing such as `wf`), re-derived along NonlinearCT's route
(`tvc_iff_integral_int`). -/
theorem tvc_iff_forward_of_integralInt {v f : ℝ → ℝ} {a t : ℝ}
    (hc : ContinuousOn v (Set.Ici t)) (hd : ∀ τ, t < τ → HasDerivAt v (a * v τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-(a * τ)) * f τ) (Set.Ioi t)) :
    Tendsto (fun T => Real.exp (-(a * T)) * v T) atTop (𝓝 0) ↔
      v t = ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * f (t + τ) :=
  forwardStmt_of_integralIntStmt integralIntStmt_holds v f a t hc hd hint

/-- Cochrane (2023), (5.95), p. 165: **the witness is covered by the re-derived theorem**: its
transversality condition `e^{−2T} wv_T → 0` holds, so `wv(0) = ∫_0^∞ e^{−2τ} wf(τ) dτ`, although
`wf` is discontinuous at `1`. -/
theorem witness_valuation :
    Tendsto (fun T => Real.exp (-(2 * T)) * wv T) atTop (𝓝 0) ∧
      wv 0 = ∫ τ in Set.Ioi 0, Real.exp (-(2 * τ)) * wf (0 + τ) := by
  obtain ⟨hc, hd, hint, -, -⟩ := witness_ctsimple_hyps
  have htvc : Tendsto (fun T => Real.exp (-(2 * T)) * wv T) atTop (𝓝 0) := by
    have he : Tendsto (fun T : ℝ => 4 * Real.exp (-T)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul 4
      rwa [mul_zero] at this
    refine squeeze_zero_norm' ?_ he
    filter_upwards [eventually_ge_atTop 0] with T hT
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 := (wv_wdv_bound T).1
    have h2 : (T - 1) ^ 2 ≤ (T + 2) ^ 2 := by nlinarith
    have h3 := sq_le_four_exp hT
    have hsplit : Real.exp (-(2 * T)) * Real.exp T = Real.exp (-T) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp (-(2 * T)) * |wv T| ≤ Real.exp (-(2 * T)) * (4 * Real.exp T) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 4 * Real.exp (-T) := by rw [← hsplit]; ring
  exact ⟨htvc, (tvc_iff_forward_of_integralInt hc hd hint).1 htvc⟩

end Cochrane.StickyPriceFiscal.TidyR5TVC
