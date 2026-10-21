/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Unemployment.Expectations
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exercise 7.2: wage inflation with wage-markup and labour-supply shocks

Galí (2015), Chapter 7, Exercise 7.2, p. 221. Member `(j, s)` has labour disutility `χ_t s^φ`
with `ξ_t = log χ_t` exogenous, and the elasticity of substitution between labour types is
time-varying, so the desired wage markup `μ^w_t = log(ε_{w,t}/(ε_{w,t} − 1))` varies.

## (a) The wage equation: `ξ_t` and `μ^w_t` enter symmetrically

* `eq13` and `eq15_iff` are restated from the Chapter 6 project (the reset-wage rule (12) ⇒ its
  recursive form (13); (13) + the wage index (14) ⟺ the wage-inflation equation (15)).
* `eq13_timeVarying`: with a time-varying desired markup `μ^w_t` inside the reset-wage sum (12)
  (`μ^w_{t+k}` in place of the constant `μ^w`; the elasticity in labour demand is evaluated at
  its steady-state value, the usual first-order approximation), the recursive rule (13) holds
  with the markup gap `μ̂^w_t = (w_t − p_t − mrs_t) − μ^w_t`.
* `wageEq_iff_errorForm`, `ex7_2a`: with `mrs_t = σc_t + φn_t + ξ_t`,
  `π^w_{t+1} = β E_{t+1} π^w_{t+2} − λ_w(ω_{t+1} − σc_{t+1} − φn_{t+1}) + λ_w(ξ_{t+1} + μ^w_{t+1})`;
  `errorForm_hat`: around a steady state the error is `λ_w(ξ̂_t + μ̂^w_t)`.
* `errorForm_depends_on_sum`, `errorForm_shift_iff`, `not_identified`: the equation depends on the
  two shocks only through `ξ_t + μ^w_t`; `(ξ + d, μ^w − d)` is observationally equivalent to
  `(ξ, μ^w)` for every process `d` (the Chari–Kehoe–McGrattan identification problem).

## (b) The unemployment form

* `participation_log`: the marginal participant `W/P = χ_t C^σ L^φ` gives (6) with `ξ_t`,
  `ω_t = σc_t + φl_t + ξ_t` (exact, in logs).
* `ex7_2b`: with participation and `u = l − n`, the wage equation is equivalent to
  `π^w_t = β E_t π^w_{t+1} − λ_wφ(u_t − uⁿ_t)`, `uⁿ_t = μ^w_t/φ`: only `μ^w_t` appears.
* `identified`: in the unemployment form, together with the participation equation, the
  observables `(π^w, ω, c, n, l)` determine both `ξ` and `μ^w` uniquely.
-/

namespace Gali.Unemployment.Ex7_2

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Restated from the Chapter 6 project: (12) ⇒ (13), and (13) + (14) ⟺ (15) -/

/-- Galí (2015), Ch. 6, p. 169 (restated from the Chapter 6 project): the gap of the average log
wage markup from its constant desired value, `μ̂^w_t = (w_t − p_t − mrs_t) − μ^w`. -/
noncomputable def markupGap (μw : ℝ) (w p mrs : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (w t ω - p t ω - mrs t ω) - μw

/-- Galí (2015), Ch. 6, eqs. (12)–(13), p. 169 (**the recursive wage-setting rule**; restated
from the Chapter 6 project). Let the reset
wage satisfy (12), `w*_t = μ^w + (1 − βθ_w) ∑ₖ (βθ_w)ᵏ E_t[mrs_{t+k|t} + p_{t+k}]`, with
`mrs_{t+k|t} = mrs_{t+k} − ε_wφ(w*_t − w_{t+k})` (p. 169), for bounded adapted `w`, `p`, `mrs`
and adapted `w*`. Then (i) (13) holds,
`w*_t = βθ_w E_t w*_{t+1} + (1 − βθ_w)(w_t − (1 + ε_wφ)⁻¹ μ̂^w_t)`; (ii) `w*` is the forward
series; (iii) it is the **unique bounded solution** of (13). -/
theorem eq13 {β θ ε φ μw M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hεφ : 0 ≤ ε * φ) {wstar w p mrs : ℕ → Ω → ℝ} {mrsR : ℕ → ℕ → Ω → ℝ}
    (hw : ∀ t ω, |w t ω| ≤ M) (hp : ∀ t ω, |p t ω| ≤ M) (hm : ∀ t ω, |mrs t ω| ≤ M)
    (hwa : 𝔼.Adapted w) (hpa : 𝔼.Adapted p) (hma : 𝔼.Adapted mrs) (hsa : 𝔼.Adapted wstar)
    (h12 : ∀ t ω, wstar t ω = μw + (1 - β * θ) *
      ∑' k, (β * θ) ^ k * 𝔼.E t (fun ω' => mrsR t k ω' + p (t + k) ω') ω)
    (hmrs : ∀ t k ω, mrsR t k ω = mrs (t + k) ω - ε * φ * (wstar t ω - w (t + k) ω)) :
    (∀ t, wstar t = (β * θ) • 𝔼.E t (wstar (t + 1)) +
      (1 - β * θ) • (w t - (1 + ε * φ)⁻¹ • markupGap μw w p mrs t)) ∧
    wstar = 𝔼.forwardSeries (β * θ)
      (fun t => (1 - β * θ) • (w t - (1 + ε * φ)⁻¹ • markupGap μw w p mrs t)) ∧
    ∀ z : ℕ → Ω → ℝ, BoundedProc z → (∀ t, z t = (β * θ) • 𝔼.E t (z (t + 1)) +
      (1 - β * θ) • (w t - (1 + ε * φ)⁻¹ • markupGap μw w p mrs t)) → z = wstar := by
  set a := β * θ with ha
  have ha0 : 0 ≤ a := mul_nonneg hβ0 hθ0
  have ha1 : a < 1 := by nlinarith
  have hd : 1 + ε * φ ≠ 0 := by linarith
  set c := (1 + ε * φ)⁻¹ with hc
  have hc0 : 0 ≤ c := inv_nonneg.mpr (by linarith)
  set u : ℕ → Ω → ℝ := fun t => (1 - a) • (w t - c • markupGap μw w p mrs t) with hu
  set y : ℕ → Ω → ℝ := fun s ω => mrs s ω + ε * φ * w s ω + p s ω with hy
  -- bounds and adaptedness
  have hyb : ∀ t ω, |y t ω| ≤ M + ε * φ * M + M := fun t ω => by
    have h1 := abs_add_le (mrs t ω + ε * φ * w t ω) (p t ω)
    have h2 := abs_add_le (mrs t ω) (ε * φ * w t ω)
    have h3 : |ε * φ * w t ω| ≤ ε * φ * M := by
      rw [abs_mul, abs_of_nonneg hεφ]
      exact mul_le_mul_of_nonneg_left (hw t ω) hεφ
    simp only [hy]
    linarith [hm t ω, hp t ω]
  have hgap : ∀ t, markupGap μw w p mrs t = w t - p t - mrs t - fun _ => μw := fun t => rfl
  have hub : ∀ t ω, |u t ω| ≤ (1 - a) * (M + c * (3 * M + |μw|)) := fun t ω => by
    have hg : |markupGap μw w p mrs t ω| ≤ 3 * M + |μw| := by
      simp only [markupGap]
      have := abs_sub (w t ω - p t ω - mrs t ω) μw
      have := abs_sub (w t ω - p t ω) (mrs t ω)
      have := abs_sub (w t ω) (p t ω)
      linarith [hw t ω, hp t ω, hm t ω]
    simp only [hu, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - a)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hc0]
    exact add_le_add (hw t ω) (mul_le_mul_of_nonneg_left hg hc0)
  have hua : 𝔼.Adapted u := fun t => by
    simp only [hu, hgap, map_smul, map_sub, 𝔼.const, hwa t, hpa t, hma t]
  -- `w*` is the forward series of `u`
  have hS : ∀ t ω, Summable fun k => a ^ k * 𝔼.E t (y (t + k)) ω :=
    fun t ω => 𝔼.forwardSeries_summable ha0 ha1 hyb t ω
  have hgeo := summable_geometric_of_lt_one ha0 ha1
  have hkey : ∀ t ω, wstar t ω = c * (μw + (1 - a) * ∑' k, a ^ k * 𝔼.E t (y (t + k)) ω) := by
    intro t ω
    have hin : ∀ k, 𝔼.E t (fun ω' => mrsR t k ω' + p (t + k) ω') ω
        = 𝔼.E t (y (t + k)) ω - ε * φ * wstar t ω := by
      intro k
      have hf : (fun ω' => mrsR t k ω' + p (t + k) ω') = y (t + k) - (ε * φ) • wstar t := by
        funext ω'
        simp only [hy, hmrs, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hf, map_sub, map_smul, hsa t]
      rfl
    have h := h12 t ω
    simp_rw [hin, mul_sub] at h
    rw [Summable.tsum_sub (hS t ω) (hgeo.mul_right _), tsum_mul_right,
      tsum_geometric_of_lt_one ha0 ha1] at h
    have h1a : (1 : ℝ) - a ≠ 0 := by linarith
    rw [hc, eq_inv_mul_iff_mul_eq₀ hd]
    field_simp at h
    linear_combination h
  have hfs : ∀ t, wstar t = 𝔼.forwardSeries a u t := by
    intro t
    funext ω
    have hEu : ∀ k, 𝔼.E t (u (t + k)) ω = (1 - a) * c * (𝔼.E t (y (t + k)) ω + μw) := by
      intro k
      have hf : u (t + k) = ((1 - a) * c) • (y (t + k) + fun _ => μw) := by
        funext ω'
        simp only [hu, hy, markupGap, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
        rw [hc]
        field_simp
        ring
      rw [hf, map_smul, map_add, 𝔼.const]
      rfl
    change wstar t ω = ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω
    simp_rw [hEu]
    have e : ∀ k, a ^ k * ((1 - a) * c * (𝔼.E t (y (t + k)) ω + μw))
        = (1 - a) * c * (a ^ k * 𝔼.E t (y (t + k)) ω) + (1 - a) * c * μw * a ^ k :=
      fun k => by ring
    simp_rw [e]
    rw [Summable.tsum_add ((hS t ω).mul_left _) (hgeo.mul_left _), tsum_mul_left,
      tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1, hkey t ω]
    have h1a : (1 : ℝ) - a ≠ 0 := by linarith
    field_simp
    ring
  have hfs' : wstar = 𝔼.forwardSeries a u := funext hfs
  refine ⟨fun t => ?_, hfs', fun z hz hzrec => ?_⟩
  · rw [hfs', 𝔼.forwardSeries_solves ha0 ha1 hub hua t]
  · rw [hfs']
    exact 𝔼.eq_forwardSeries ha0 ha1 hub hua hzrec hz

/-- Galí (2015), p. 170: `λ_w = (1 − θ_w)(1 − βθ_w)/(θ_w(1 + ε_wφ))`. -/
noncomputable def lambdaW (β θ ε φ : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / (θ * (1 + ε * φ))

/-- Galí (2015), p. 169: wage inflation `π^w_{t+1} = w_{t+1} − w_t` (dated `t + 1`). -/
noncomputable def wageInfl {Ω : Type*} (w : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := w (t + 1) - w t

/-- Galí (2015), Ch. 6, eqs. (13)–(15), pp. 169–170 (**(13) + (14) ⟺ (15)**; restated from the
Chapter 6 project): with
`0 < θ_w < 1`, `1 + ε_wφ ≠ 0`, an adapted (log) wage index `w` and the index recursion (14),
`w_{t+1} = θ_w w_t + (1 − θ_w) w*_{t+1}` at every date, the recursive wage-setting rule (13)
holds at every date `t + 1` **if and only if** the wage-inflation equation (15),
`π^w_{t+1} = β E_{t+1} π^w_{t+2} − λ_w μ̂^w_{t+1}`, does. -/
theorem eq15_iff {β θ ε φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hεφ : 1 + ε * φ ≠ 0)
    {wstar w μhat : ℕ → Ω → ℝ} (hwa : 𝔼.Adapted w)
    (h14 : ∀ t, w (t + 1) = θ • w t + (1 - θ) • wstar (t + 1)) :
    (∀ t, wstar (t + 1) = (β * θ) • 𝔼.E (t + 1) (wstar (t + 2)) +
        (1 - β * θ) • (w (t + 1) - (1 + ε * φ)⁻¹ • μhat (t + 1))) ↔
      ∀ t, wageInfl w t = β • 𝔼.E (t + 1) (wageInfl w (t + 1)) -
        lambdaW β θ ε φ • μhat (t + 1) := by
  have h1θ : (1 : ℝ) - θ ≠ 0 := by linarith
  have hθ : θ ≠ 0 := hθ0.ne'
  have hL : θ * lambdaW β θ ε φ = (1 - θ) * (1 - β * θ) * (1 + ε * φ)⁻¹ := by
    unfold lambdaW
    field_simp
  have hA : ∀ t ω, w (t + 1) ω = θ * w t ω + (1 - θ) * wstar (t + 1) ω := fun t ω => by
    have := congrFun (h14 t) ω
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have hB : ∀ t ω, 𝔼.E (t + 1) (w (t + 2)) ω
      = θ * w (t + 1) ω + (1 - θ) * 𝔼.E (t + 1) (wstar (t + 2)) ω := fun t ω => by
    have h' : w (t + 2) = θ • w (t + 1) + (1 - θ) • wstar (t + 2) := h14 (t + 1)
    rw [h', map_add, map_smul, map_smul, hwa (t + 1)]
    rfl
  have hEπ : ∀ t ω, 𝔼.E (t + 1) (wageInfl w (t + 1)) ω = 𝔼.E (t + 1) (w (t + 2)) ω -
      w (t + 1) ω := by
    intro t ω
    simp only [wageInfl, map_sub, hwa (t + 1), Pi.sub_apply]
  constructor
  · intro h13 t
    funext ω
    have E13 : wstar (t + 1) ω = β * θ * 𝔼.E (t + 1) (wstar (t + 2)) ω +
        (1 - β * θ) * (w (t + 1) ω - (1 + ε * φ)⁻¹ * μhat (t + 1) ω) := by
      have := congrFun (h13 t) ω
      simpa only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using this
    have hgoal : θ * (w (t + 1) ω - w t ω - (β * (𝔼.E (t + 1) (w (t + 2)) ω - w (t + 1) ω) -
        lambdaW β θ ε φ * μhat (t + 1) ω)) = 0 := by
      linear_combination (1 - θ) * E13 + hA t ω - β * θ * hB t ω + μhat (t + 1) ω * hL
    have hq := (mul_eq_zero.mp hgoal).resolve_left hθ
    change wageInfl w t ω = β * 𝔼.E (t + 1) (wageInfl w (t + 1)) ω -
      lambdaW β θ ε φ * μhat (t + 1) ω
    rw [hEπ t ω]
    simp only [wageInfl, Pi.sub_apply]
    linarith
  · intro h15 t
    funext ω
    have F15 : w (t + 1) ω - w t ω = β * (𝔼.E (t + 1) (w (t + 2)) ω - w (t + 1) ω) -
        lambdaW β θ ε φ * μhat (t + 1) ω := by
      have h := congrFun (h15 t) ω
      have e : (β • 𝔼.E (t + 1) (wageInfl w (t + 1)) - lambdaW β θ ε φ • μhat (t + 1)) ω
          = β * 𝔼.E (t + 1) (wageInfl w (t + 1)) ω - lambdaW β θ ε φ * μhat (t + 1) ω := rfl
      rw [e, hEπ t ω] at h
      simpa only [wageInfl, Pi.sub_apply] using h
    have hgoal : (1 - θ) * (wstar (t + 1) ω - (β * θ * 𝔼.E (t + 1) (wstar (t + 2)) ω +
        (1 - β * θ) * (w (t + 1) ω - (1 + ε * φ)⁻¹ * μhat (t + 1) ω))) = 0 := by
      linear_combination θ * F15 - μhat (t + 1) ω * hL - hA t ω + β * θ * hB t ω
    have hq := (mul_eq_zero.mp hgoal).resolve_left h1θ
    change wstar (t + 1) ω = β * θ * 𝔼.E (t + 1) (wstar (t + 2)) ω +
      (1 - β * θ) * (w (t + 1) ω - (1 + ε * φ)⁻¹ * μhat (t + 1) ω)
    linarith

/-- Galí (2015), p. 170 (**`λ_w > 0`**): for `0 < θ_w < 1`, `βθ_w < 1` and `1 + ε_wφ > 0`. -/
theorem lambdaW_pos {β θ ε φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hεφ : 0 < 1 + ε * φ) : 0 < lambdaW β θ ε φ := by
  unfold lambdaW
  have h1 : 0 < 1 - θ := by linarith
  have h2 : 0 < 1 - β * θ := by linarith
  positivity

/-! ### (a) A time-varying desired markup -/

/-- Galí (2015), Exercise 7.2(a), p. 221: the gap between the actual average wage markup
`w_t − p_t − mrs_t` and the time-varying desired markup `μ^w_t`. -/
def markupGapTV (w p mrs μd : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => w t ω - p t ω - mrs t ω - μd t ω

/-- Galí (2015), Exercise 7.2(a), p. 221 (**the recursive wage-setting rule with a time-varying
desired markup**): if the reset wage satisfies
`w*_t = (1 − βθ_w) ∑ₖ (βθ_w)ᵏ E_t[μ^w_{t+k} + mrs_{t+k|t} + p_{t+k}]` with
`mrs_{t+k|t} = mrs_{t+k} − ε_wφ(w*_t − w_{t+k})` (bounded adapted `w, p, mrs, μ^w`, adapted `w*`),
then `w*_t = βθ_w E_t w*_{t+1} + (1 − βθ_w)(w_t − (1 + ε_wφ)⁻¹ μ̂^w_t)` with
`μ̂^w_t = (w_t − p_t − mrs_t) − μ^w_t`. -/
theorem eq13_timeVarying {β θ ε φ M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hεφ : 0 ≤ ε * φ) {wstar w p mrs μd : ℕ → Ω → ℝ} {mrsR : ℕ → ℕ → Ω → ℝ}
    (hw : ∀ t ω, |w t ω| ≤ M) (hp : ∀ t ω, |p t ω| ≤ M) (hm : ∀ t ω, |mrs t ω| ≤ M)
    (hμ : ∀ t ω, |μd t ω| ≤ M)
    (hwa : 𝔼.Adapted w) (hpa : 𝔼.Adapted p) (hma : 𝔼.Adapted mrs) (hμa : 𝔼.Adapted μd)
    (hsa : 𝔼.Adapted wstar)
    (h12 : ∀ t ω, wstar t ω = (1 - β * θ) *
      ∑' k, (β * θ) ^ k * 𝔼.E t (fun ω' => mrsR t k ω' + μd (t + k) ω' + p (t + k) ω') ω)
    (hmrs : ∀ t k ω, mrsR t k ω = mrs (t + k) ω - ε * φ * (wstar t ω - w (t + k) ω)) :
    ∀ t, wstar t = (β * θ) • 𝔼.E t (wstar (t + 1)) +
      (1 - β * θ) • (w t - (1 + ε * φ)⁻¹ • markupGapTV w p mrs μd t) := by
  have hm' : ∀ t ω, |(mrs + μd) t ω| ≤ M + M := fun t ω => by
    simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hm t ω) (hμ t ω))
  have hw' : ∀ t ω, |w t ω| ≤ M + M := fun t ω => by
    have := abs_nonneg (μd t ω)
    linarith [hw t ω, hμ t ω]
  have hp' : ∀ t ω, |p t ω| ≤ M + M := fun t ω => by
    have := abs_nonneg (μd t ω)
    linarith [hp t ω, hμ t ω]
  have hma' : 𝔼.Adapted (mrs + μd) := fun t => by
    simp only [Pi.add_apply, map_add, hma t, hμa t]
  have h12' : ∀ t ω, wstar t ω = 0 + (1 - β * θ) * ∑' k, (β * θ) ^ k *
      𝔼.E t (fun ω' => (fun t k ω => mrsR t k ω + μd (t + k) ω) t k ω' + p (t + k) ω') ω :=
    fun t ω => by rw [zero_add]; exact h12 t ω
  have hmrs' : ∀ t k ω, (fun t k ω => mrsR t k ω + μd (t + k) ω) t k ω =
      (mrs + μd) (t + k) ω - ε * φ * (wstar t ω - w (t + k) ω) := fun t k ω => by
    simp only [Pi.add_apply, hmrs]
    ring
  have h := (eq13 𝔼 hβ0 hβ1 hθ0 hθ1 hεφ hw' hp' hm' hwa hpa hma' hsa h12' hmrs').1
  intro t
  have e : markupGap 0 w p (mrs + μd) t = markupGapTV w p mrs μd t := by
    funext ω
    simp only [markupGap, markupGapTV, Pi.add_apply]
    ring
  rw [h t, e]

/-- Galí (2015), Exercise 7.2(a), p. 221: the wage-inflation equation written as a function of
the real wage `ω`, consumption and employment, with the error term `λ_w (ξ_t + μ^w_t)`:
`π^w_t = β E_t π^w_{t+1} − λ_w (ω_t − σ c_t − φ n_t) + λ_w (ξ_t + μ^w_t)`. -/
def ErrorForm (β lamW σ φ : ℝ) (piW wr c n ξ μd : ℕ → Ω → ℝ) : Prop :=
  ∀ t, piW t = β • 𝔼.E t (piW (t + 1)) - lamW • (wr t - σ • c t - φ • n t) +
    lamW • (ξ t + μd t)

/-- Galí (2015), Exercise 7.2(a), p. 221 (**exact algebra**): with `mrs = σc + φn + ξ`, the
wage-inflation equation (15) `π^w_t = β E_t π^w_{t+1} − λ_w μ̂^w_t`,
`μ̂^w_t = ω_t − mrs_t − μ^w_t`, is the error form with error `λ_w(ξ_t + μ^w_t)`. -/
theorem wageEq_iff_errorForm {β lamW σ φ : ℝ} {piW wr c n ξ μd : ℕ → Ω → ℝ} :
    (∀ t, piW t = β • 𝔼.E t (piW (t + 1)) -
        lamW • (wr t - (σ • c t + φ • n t + ξ t) - μd t)) ↔
      ErrorForm 𝔼 β lamW σ φ piW wr c n ξ μd := by
  refine forall_congr' fun t => ?_
  have e : β • 𝔼.E t (piW (t + 1)) - lamW • (wr t - (σ • c t + φ • n t + ξ t) - μd t) =
      β • 𝔼.E t (piW (t + 1)) - lamW • (wr t - σ • c t - φ • n t) + lamW • (ξ t + μd t) := by
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]

/-- **Galí (2015), Exercise 7.2(a), p. 221 (the wage equation, derived)**: given the reset-wage
rule (12) with time-varying desired markup `μ^w_t` (`eq13_timeVarying`), the wage index (14),
`mrs_t = σc_t + φn_t + ξ_t` and real wage `ω_t = w_t − p_t`, wage inflation
`π^w_{t+1} = w_{t+1} − w_t` satisfies the error form at every date `t + 1`:
`π^w_{t+1} = β E_{t+1} π^w_{t+2} − λ_w(ω_{t+1} − σc_{t+1} − φn_{t+1}) + λ_w(ξ_{t+1} + μ^w_{t+1})`.
-/
theorem ex7_2a {β θ ε φ σ M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hε : 0 ≤ ε) (hφ : 0 ≤ φ) {wstar w p mrs μd c n ξ : ℕ → Ω → ℝ} {mrsR : ℕ → ℕ → Ω → ℝ}
    (hw : ∀ t ω, |w t ω| ≤ M) (hp : ∀ t ω, |p t ω| ≤ M) (hm : ∀ t ω, |mrs t ω| ≤ M)
    (hμ : ∀ t ω, |μd t ω| ≤ M)
    (hwa : 𝔼.Adapted w) (hpa : 𝔼.Adapted p) (hma : 𝔼.Adapted mrs) (hμa : 𝔼.Adapted μd)
    (hsa : 𝔼.Adapted wstar)
    (h12 : ∀ t ω, wstar t ω = (1 - β * θ) *
      ∑' k, (β * θ) ^ k * 𝔼.E t (fun ω' => mrsR t k ω' + μd (t + k) ω' + p (t + k) ω') ω)
    (hmrsR : ∀ t k ω, mrsR t k ω = mrs (t + k) ω - ε * φ * (wstar t ω - w (t + k) ω))
    (h14 : ∀ t, w (t + 1) = θ • w t + (1 - θ) • wstar (t + 1))
    (hmrs : ∀ t, mrs t = σ • c t + φ • n t + ξ t) :
    ∀ t, wageInfl w t = β • 𝔼.E (t + 1) (wageInfl w (t + 1)) -
      lambdaW β θ ε φ • ((w (t + 1) - p (t + 1)) - σ • c (t + 1) - φ • n (t + 1)) +
      lambdaW β θ ε φ • (ξ (t + 1) + μd (t + 1)) := by
  have hεφ : 0 ≤ ε * φ := mul_nonneg hε hφ
  have h13 := eq13_timeVarying 𝔼 hβ0 hβ1 hθ0.le hθ1 hεφ hw hp hm hμ hwa hpa hma hμa hsa h12 hmrsR
  have h15 := (eq15_iff 𝔼 hθ0 hθ1 (by linarith) (μhat := markupGapTV w p mrs μd) hwa h14).mp
    fun t => h13 (t + 1)
  intro t
  rw [h15 t]
  funext ω
  simp only [markupGapTV, hmrs, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), Exercise 7.2(a), p. 221 (**the error in deviations, `λ_w(ξ̂ + μ̂^w)`**): if the
steady state satisfies `ω̄ − σc̄ − φn̄ = ξ̄ + μ̄` (the wage-markup condition), then writing every
variable as steady state plus deviation (`ω = ω̄ + ω̂`, …), the error form in levels holds iff
`π^w_t = β E_t π^w_{t+1} − λ_w(ω̂_t − σĉ_t − φn̂_t) + λ_w(ξ̂_t + μ̂^w_t)`. -/
theorem errorForm_hat {β lamW σ φ wbar cbar nbar ξbar μbar : ℝ}
    (hss : wbar - σ * cbar - φ * nbar = ξbar + μbar) {piW wh ch nh ξh μh : ℕ → Ω → ℝ} :
    ErrorForm 𝔼 β lamW σ φ piW (fun t => wh t + fun _ => wbar) (fun t => ch t + fun _ => cbar)
        (fun t => nh t + fun _ => nbar) (fun t => ξh t + fun _ => ξbar)
        (fun t => μh t + fun _ => μbar) ↔
      ErrorForm 𝔼 β lamW σ φ piW wh ch nh ξh μh := by
  refine forall_congr' fun t => ?_
  have e : β • 𝔼.E t (piW (t + 1)) - lamW • ((wh t + fun _ => wbar) -
      σ • (ch t + fun _ => cbar) - φ • (nh t + fun _ => nbar)) +
      lamW • ((ξh t + fun _ => ξbar) + (μh t + fun _ => μbar)) =
      β • 𝔼.E t (piW (t + 1)) - lamW • (wh t - σ • ch t - φ • nh t) + lamW • (ξh t + μh t) := by
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-lamW) * hss
  rw [e]

/-- Galí (2015), Exercise 7.2(a), p. 221 (**symmetry: only the sum `ξ + μ^w` matters**): if
`ξ_t + μ^w_t = ξ'_t + μ'^w_t` at every date, the error forms with `(ξ, μ^w)` and `(ξ', μ'^w)`
are the same restriction on the observables `(π^w, ω, c, n)`. -/
theorem errorForm_depends_on_sum {β lamW σ φ : ℝ} {piW wr c n ξ μd ξ' μd' : ℕ → Ω → ℝ}
    (hsum : ∀ t, ξ t + μd t = ξ' t + μd' t) :
    ErrorForm 𝔼 β lamW σ φ piW wr c n ξ μd ↔ ErrorForm 𝔼 β lamW σ φ piW wr c n ξ' μd' := by
  refine forall_congr' fun t => ?_
  rw [hsum t]

/-- Galí (2015), Exercise 7.2(a), p. 221 (**observational equivalence**): for every process `d`,
`(ξ + d, μ^w − d)` satisfies the wage equation exactly when `(ξ, μ^w)` does. -/
theorem errorForm_shift_iff {β lamW σ φ : ℝ} {piW wr c n ξ μd : ℕ → Ω → ℝ}
    (d : ℕ → Ω → ℝ) :
    ErrorForm 𝔼 β lamW σ φ piW wr c n (fun t => ξ t + d t) (fun t => μd t - d t) ↔
      ErrorForm 𝔼 β lamW σ φ piW wr c n ξ μd :=
  errorForm_depends_on_sum 𝔼 fun t => by abel

/-- Galí (2015), Exercise 7.2(a), p. 221 (**the identification problem**, Chari, Kehoe and
McGrattan 2009): given any observables `(π^w, ω, c, n)` consistent with the wage equation for
some shocks `(ξ, μ^w)`, there is a **different** pair of shocks (`(ξ + 1, μ^w − 1)`) consistent
with the same observables: the wage equation alone cannot separate preference shocks from
wage-markup shocks. -/
theorem not_identified [Nonempty Ω] {β lamW σ φ : ℝ} {piW wr c n ξ μd : ℕ → Ω → ℝ}
    (h : ErrorForm 𝔼 β lamW σ φ piW wr c n ξ μd) :
    ∃ ξ' μd' : ℕ → Ω → ℝ, ErrorForm 𝔼 β lamW σ φ piW wr c n ξ' μd' ∧ ξ' ≠ ξ ∧ μd' ≠ μd := by
  refine ⟨fun t => ξ t + fun _ => 1, fun t => μd t - fun _ => 1,
    (errorForm_shift_iff 𝔼 (fun _ _ => 1)).mpr h, fun he => ?_, fun he => ?_⟩
  · obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun he 0) ω
    simp only [Pi.add_apply] at this
    linarith
  · obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun he 0) ω
    simp only [Pi.sub_apply] at this
    linarith

/-! ### (b) The unemployment form -/

/-- Galí (2015), Exercise 7.2(b), p. 221 (with (5)–(6), p. 204, **exact in logs**): the marginal
participant of a labour type satisfies `W/P = χ_t C^σ L^φ`; taking logs,
`ω = σc + φl + ξ` with `ω = log(W/P)`, `c = log C`, `l = log L`, `ξ = log χ`. -/
theorem participation_log {σ φ χ C L WP : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hL : 0 < L)
    (h5 : WP = χ * C ^ σ * L ^ φ) :
    Real.log WP = σ * Real.log C + φ * Real.log L + Real.log χ := by
  rw [h5, Real.log_mul (by positivity) (by positivity), Real.log_mul hχ.ne' (by positivity),
    Real.log_rpow hC, Real.log_rpow hL]
  ring

/-- Galí (2015), Exercise 7.2(b), p. 221: the wage equation in terms of the unemployment rate,
`π^w_t = β E_t π^w_{t+1} − λ_wφ(u_t − uⁿ_t)` with the natural rate `uⁿ_t = μ^w_t/φ`. -/
def UnempForm (β lamW φ : ℝ) (piW u μd : ℕ → Ω → ℝ) : Prop :=
  ∀ t, piW t = β • 𝔼.E t (piW (t + 1)) - (lamW * φ) • (u t - φ⁻¹ • μd t)

/-- **Galí (2015), Exercise 7.2(b), p. 221 (only `μ^w_t` appears)**: with the participation
equation `ω_t = σc_t + φl_t + ξ_t` and `u_t = l_t − n_t`, the wage equation (error form, with
both shocks) holds iff the unemployment form holds, in which the preference shock `ξ_t` no
longer appears (it is absorbed into the labour force through participation) and the
wage-markup shock enters through the natural rate `uⁿ_t = μ^w_t/φ` (`φ ≠ 0`). -/
theorem ex7_2b {β lamW σ φ : ℝ} (hφ : φ ≠ 0) {piW wr c n l u ξ μd : ℕ → Ω → ℝ}
    (h6 : ∀ t, wr t = σ • c t + φ • l t + ξ t) (h7 : ∀ t, u t = l t - n t) :
    ErrorForm 𝔼 β lamW σ φ piW wr c n ξ μd ↔ UnempForm 𝔼 β lamW φ piW u μd := by
  refine forall_congr' fun t => ?_
  have e : β • 𝔼.E t (piW (t + 1)) - lamW • (wr t - σ • c t - φ • n t) + lamW • (ξ t + μd t) =
      β • 𝔼.E t (piW (t + 1)) - (lamW * φ) • (u t - φ⁻¹ • μd t) := by
    rw [h6 t, h7 t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [e]

/-- **Galí (2015), Exercise 7.2(b), p. 221 (the unemployment form restores identification)**:
for `λ_w ≠ 0`, `φ ≠ 0`, if two pairs of shocks `(ξ, μ^w)` and `(ξ', μ'^w)` are both consistent
with the same observables `(π^w, ω, c, l, u)` through the participation equation and the
unemployment form of the wage equation, then `ξ = ξ'` and `μ^w = μ'^w`: the participation
equation identifies `ξ_t = ω_t − σc_t − φl_t`, and the wage equation identifies
`μ^w_t = φ u_t − (π^w_t − β E_t π^w_{t+1})/λ_w`. -/
theorem identified {β lamW σ φ : ℝ} (hlam : lamW ≠ 0) (hφ : φ ≠ 0)
    {piW wr c l u ξ μd ξ' μd' : ℕ → Ω → ℝ}
    (h6 : ∀ t, wr t = σ • c t + φ • l t + ξ t) (h6' : ∀ t, wr t = σ • c t + φ • l t + ξ' t)
    (hU : UnempForm 𝔼 β lamW φ piW u μd) (hU' : UnempForm 𝔼 β lamW φ piW u μd') :
    ξ = ξ' ∧ μd = μd' := by
  refine ⟨funext fun t => ?_, funext fun t => funext fun ω => ?_⟩
  · have := (h6 t).symm.trans (h6' t)
    exact add_left_cancel this
  · have a := congrFun (hU t) ω
    have b := congrFun (hU' t) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b
    have hc : lamW * φ * φ⁻¹ ≠ 0 := by
      rw [mul_assoc, mul_inv_cancel₀ hφ, mul_one]
      exact hlam
    have : lamW * φ * φ⁻¹ * (μd t ω - μd' t ω) = 0 := by linear_combination b - a
    have := (mul_eq_zero.mp this).resolve_left hc
    linarith

end Gali.Unemployment.Ex7_2
