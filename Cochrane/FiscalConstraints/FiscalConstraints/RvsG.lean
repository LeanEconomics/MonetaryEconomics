/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.LinearODE
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# What if r < g?

Cochrane (2023), Chapter 6, §6.4 *What if r < g?*, §6.4.1–§6.4.3, eqs. (6.3)–(6.5),
pp. 195–199.

The debt-to-GDP ratio `x = b/y` obeys (6.4), `x' = a x - σ` with `a = r - g` and `σ = s/y`. We
prove the dichotomy behind "in a perfect-foresight frictionless model, `r < g` implies price-level
indeterminacy, not infinity" (p. 195), in continuous and in discrete time:

* (D1) `a > 0`: the forward present value `x̂_t = ∫₀^∞ e^{-a u} σ_{t+u} du` is a bounded solution;
  every solution satisfies `x_t - x̂_t = e^{a t}(x₀ - x̂₀)`; a solution is bounded iff `x₀ = x̂₀`,
  and otherwise `|x_t| → ∞`; the transversality condition `e^{-a t} x_t → 0` (equivalently
  `e^{-r t} b_t → 0`) holds iff `x₀ = x̂₀`. With nominal debt `B₀` and `x₀ = B₀/(P₀ y₀)`, exactly
  one price level `P₀ = B₀/(y₀ x̂₀)` gives a bounded path.
* (D2) `a < 0`: every solution is bounded, `|x_t| ≤ |x₀| + M/|a|`, and any two converge; so every
  `P₀ > 0` gives a bounded debt-to-GDP path (indeterminacy). The transversality condition
  `e^{-r t} b_t → 0` instead fails for every solution when the surplus ratio is a nonzero
  constant: no `P₀` satisfies it ("infinity" in the present-value sense).
* (D3) `a = 0`: `x_t = x₀ - ∫₀^t σ`, bounded iff the cumulated surpluses are bounded; with a
  constant nonzero surplus ratio no solution is bounded.
* (D4) temporary `r < g`: `a = a₁` on `[0, T₀)`, `a = a₂ > 0` after. There is exactly one bounded
  solution, the forward present value with time-varying discounting,
  `x̂_t = ∫_t^{T₀} e^{-a₁(v-t)} σ_v dv + e^{-a₁(T₀-t)} x̂^{(2)}_{T₀}`, and every other solution
  diverges. For `a₁ = -0.01`, `T₀ = 20`, `a₂ = 0.01` this is the book's 20-year formula with
  FUTURE surpluses `σ_{t+τ}`; the printed version with past surpluses `σ_{t-τ}` is wrong
  (survey E6.2).
* (D5) discrete time, `x_{t+1} = γ x_t - w_t` with `γ = (1+r)/(1+g)`: `γ > 1` gives the unique
  bounded solution `x_t = ∑_j γ^{-(j+1)} w_{t+j}`; `0 < γ < 1` makes every solution bounded and
  any two converge; `γ = 1` is the knife edge.
* (D6) the steady-state surplus `σ* = a x*` is continuous across `a = 0` (§6.4.2), with the book's
  numbers: `±0.01%` of GDP at 100% debt, `log 3/10⁻⁴ ∈ (10986, 10987)` years ("11,000"),
  `150 e^{1.1} ∈ (450.6, 450.7)`, exact factors `1/3` and `3`; `r - g = -1%` at 100% debt funds a
  1% of GDP deficit (§6.4.3); `e^{-0.2} ∈ (0.8187, 0.8188)`, not 80%.

Continuous-time solutions are taken on `[0, ∞)`: `x` is continuous on `[0, ∞)` and satisfies the
ODE at every `t > 0`. Surplus ratios are continuous and bounded by `M`.
-/

namespace Cochrane.FiscalConstraints.RvsG

open Real MeasureTheory Filter Topology
open Cochrane.FiscalConstraints.ExpIntegrals Cochrane.FiscalConstraints.LinearODE

/-- Cochrane (2023), eq. (6.4), p. 196: `x` solves the debt-to-GDP equation `x' = a x - σ` on
`[0, ∞)` (continuous on `[0, ∞)`, differentiable with the right derivative at every `t > 0`). -/
def SolvesOn (a : ℝ) (σ x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧ ∀ t, 0 < t → HasDerivAt x (a * x t - σ t) t

/-- Cochrane (2023), §6.4.1, p. 196: the debt-to-GDP path is bounded on `[0, ∞)` (it does not
explode). -/
def BddOn (x : ℝ → ℝ) : Prop := ∃ K, ∀ t, 0 ≤ t → |x t| ≤ K

/-- Cochrane (2023), eqs. (6.3), p. 195, and §6.4.1, p. 196: the forward present value of
surplus/GDP ratios discounted at `a = r - g`, `x̂_t = ∫₀^∞ e^{-a u} σ_{t+u} du`. -/
noncomputable def pv (a : ℝ) (σ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), exp (-a * u) * σ (t + u)

variable {a M a₂ : ℝ} {σ x z : ℝ → ℝ}

/-- Cochrane (2023), eq. (6.5), p. 196: every solution on `[0, ∞)` is the backward
(variation-of-constants) solution from its initial value. -/
theorem solvesOn_eq (hσ : Continuous σ) (hx : SolvesOn a σ x) {t : ℝ} (ht : 0 ≤ t) :
    x t = vocFrom a σ 0 (x 0) t :=
  eq_vocFrom a hσ ht (hx.1.mono Set.Icc_subset_Ici_self) (fun s hs => hx.2 s hs.1)

/-- Cochrane (2023), eq. (6.5), p. 196: for every initial value `x₀` the backward solution solves
(6.4): any initial debt-to-GDP ratio is consistent with the flow equation. -/
theorem vocFrom_solvesOn (a : ℝ) (hσ : Continuous σ) (x0 : ℝ) :
    SolvesOn a σ (vocFrom a σ 0 x0) :=
  ⟨fun t _ => (vocFrom_hasDerivAt a hσ 0 x0 t).continuousAt.continuousWithinAt,
    fun t _ => vocFrom_hasDerivAt a hσ 0 x0 t⟩

/-- Cochrane (2023), eq. (6.5), p. 196: two backward solutions differ by `e^{a t}(x₀ - z₀)`. -/
theorem vocFrom_sub (a : ℝ) (σ : ℝ → ℝ) (x0 z0 t : ℝ) :
    vocFrom a σ 0 x0 t - vocFrom a σ 0 z0 t = exp (a * t) * (x0 - z0) := by
  unfold vocFrom
  rw [mul_zero, exp_zero, one_mul, one_mul]
  ring

/-- Cochrane (2023), §6.4.1, p. 196: for `a > 0` the forward present value is the backward
solution started at `x̂₀`: `x̂_t = e^{a t}(x̂₀ - ∫₀^t e^{-a u} σ_u du)`, for every `t`. -/
theorem pv_eq_voc (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) (t : ℝ) :
    pv a σ t = vocFrom a σ 0 (pv a σ 0) t := by
  have hint : ∀ c, IntegrableOn (fun v => exp (-a * v) * σ v) (Set.Ioi c) :=
    integrableOn_exp_mul_bdd ha hσ hM
  have h0 : pv a σ 0 = ∫ v in Set.Ioi (0 : ℝ), exp (-a * v) * σ v := by
    unfold pv
    simp only [zero_add]
  unfold vocFrom
  rw [h0, mul_zero, exp_zero, one_mul, integral_Ioi_sub_interval hint t]
  unfold pv
  exact integral_exp_shift a t σ

/-- Cochrane (2023), §6.4.1, p. 196: the forward present value is bounded, `|x̂_t| ≤ M/a`. -/
theorem abs_pv_le (ha : 0 < a) (hM : ∀ u, |σ u| ≤ M) (t : ℝ) : |pv a σ t| ≤ M / a := by
  have := abs_integral_exp_mul_le ha (σ := fun u => σ (t + u)) (fun u => hM (t + u)) 0
  rw [mul_zero, exp_zero] at this
  unfold pv
  calc _ ≤ M * (1 / a) := this
    _ = M / a := by ring

/-- Cochrane (2023), §6.4.1, p. 196: the forward present value solves (6.4) at every date. -/
theorem pv_hasDerivAt (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) (t : ℝ) :
    HasDerivAt (pv a σ) (a * pv a σ t - σ t) t := by
  have he : pv a σ = vocFrom a σ 0 (pv a σ 0) := funext (pv_eq_voc ha hσ hM)
  rw [he]
  exact vocFrom_hasDerivAt a hσ 0 _ t

/-- Cochrane (2023), §6.4.1, p. 196 (D1): for `r > g` the forward present value is a solution of
(6.4) on `[0, ∞)`. -/
theorem pv_solvesOn (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) :
    SolvesOn a σ (pv a σ) :=
  ⟨fun t _ => (pv_hasDerivAt ha hσ hM t).continuousAt.continuousWithinAt,
    fun t _ => pv_hasDerivAt ha hσ hM t⟩

/-- Cochrane (2023), §6.4.1, p. 196 (D1): for `r > g` the forward present value is bounded. -/
theorem pv_bddOn (ha : 0 < a) (hM : ∀ u, |σ u| ≤ M) : BddOn (pv a σ) :=
  ⟨M / a, fun t _ => abs_pv_le ha hM t⟩

/-- Cochrane (2023), eq. (6.3), p. 195: with a constant surplus/GDP ratio `c` and `r > g`, the
present value is `b/y = c/(r - g)`. -/
theorem pv_const (ha : 0 < a) (c t : ℝ) : pv a (fun _ => c) t = c / a := by
  unfold pv
  rw [integral_mul_const, integral_exp_neg_mul_Ioi_zero ha]
  ring

/-- Cochrane (2023), eq. (6.3), p. 195: with a constant surplus/GDP ratio `c ≠ 0` and `r ≤ g`,
the present-value integral diverges ("the present value of surpluses is then apparently
infinite"). -/
theorem pv_const_not_integrable (ha : a ≤ 0) {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    ¬ IntegrableOn (fun u => exp (-a * u) * (fun _ => c) (t + u)) (Set.Ioi 0) := by
  have := not_integrableOn_exp_neg_mul ha hc
  simp only [mul_comm (exp _) c] at this ⊢
  exact this

/-- Cochrane (2023), §6.4.1, p. 196 (D1): every solution differs from the present value by an
exploding term, `x_t - x̂_t = e^{a t}(x₀ - x̂₀)`. -/
theorem sub_pv (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) (hx : SolvesOn a σ x)
    {t : ℝ} (ht : 0 ≤ t) : x t - pv a σ t = exp (a * t) * (x 0 - pv a σ 0) := by
  rw [solvesOn_eq hσ hx ht, pv_eq_voc ha hσ hM t, vocFrom_sub]

/-- Cochrane (2023), §6.4.1, p. 196 (D1): for `r > g`, a solution that does not start at the
present value explodes: `|x_t| → ∞`. -/
theorem tendsto_abs_of_ne (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hx : SolvesOn a σ x) (hne : x 0 ≠ pv a σ 0) :
    Tendsto (fun t => |x t|) atTop atTop := by
  set d := |x 0 - pv a σ 0| with hd_def
  have hd : 0 < d := abs_pos.2 (sub_ne_zero.2 hne)
  have hlow : ∀ t, 0 ≤ t → exp (a * t) * d + -(M / a) ≤ |x t| := by
    intro t ht
    have h1 := sub_pv ha hσ hM hx ht
    have h2 := abs_pv_le ha hM t
    have h3 : exp (a * t) * d = |x t - pv a σ t| := by
      rw [h1, abs_mul, abs_of_pos (exp_pos _)]
    have h4 := abs_sub (x t) (pv a σ t)
    linarith
  have hlim : Tendsto (fun t => exp (a * t) * d + -(M / a)) atTop atTop := by
    have : Tendsto (fun t => exp (a * t)) atTop atTop :=
      tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)
    exact tendsto_atTop_add_const_right _ _ (this.atTop_mul_const hd)
  exact tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono hlow) hlim

/-- Cochrane (2023), §6.4.1, p. 196 (D1): for `r > g` a solution of (6.4) is bounded iff it starts
at the present value of surpluses, `x₀ = ∫₀^∞ e^{-(r-g)u} σ_u du`. -/
theorem bddOn_iff (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hx : SolvesOn a σ x) : BddOn x ↔ x 0 = pv a σ 0 := by
  constructor
  · rintro ⟨K, hK⟩
    by_contra hne
    have h1 := (tendsto_abs_of_ne ha hσ hM hx hne).eventually_gt_atTop K
    obtain ⟨t, ht1, ht2⟩ := (h1.and (eventually_ge_atTop 0)).exists
    linarith [hK t ht2]
  · intro h
    refine ⟨M / a, fun t ht => ?_⟩
    have := sub_pv ha hσ hM hx ht
    rw [h, sub_self, mul_zero, sub_eq_zero] at this
    rw [this]
    exact abs_pv_le ha hM t

/-- Cochrane (2023), §6.4.1, p. 196 (D1): for `r > g` a bounded solution IS the present value at
every date: `x_t = ∫₀^∞ e^{-(r-g)u} σ_{t+u} du`. -/
theorem eq_pv_of_bddOn (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hx : SolvesOn a σ x) (hb : BddOn x) {t : ℝ} (ht : 0 ≤ t) : x t = pv a σ t := by
  have := sub_pv ha hσ hM hx ht
  rw [(bddOn_iff ha hσ hM hx).1 hb, sub_self, mul_zero, sub_eq_zero] at this
  exact this

/-- Cochrane (2023), §6.4.1, p. 196 (D1): for `r > g` the debt-to-GDP equation has exactly one
bounded solution on `[0, ∞)` (up to values before date 0). -/
theorem existsUnique_bdd (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) :
    SolvesOn a σ (pv a σ) ∧ BddOn (pv a σ) ∧
      ∀ x, SolvesOn a σ x → BddOn x → ∀ t, 0 ≤ t → x t = pv a σ t :=
  ⟨pv_solvesOn ha hσ hM, pv_bddOn ha hM, fun _ hx hb _ ht => eq_pv_of_bddOn ha hσ hM hx hb ht⟩

/-- Cochrane (2023), §6.4.1, p. 196 (D1, transversality): for `r > g`, `e^{-a t} x_t → 0` iff
`x₀` equals the present value. -/
theorem tvc_iff (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hx : SolvesOn a σ x) :
    Tendsto (fun t => exp (-a * t) * x t) atTop (𝓝 0) ↔ x 0 = pv a σ 0 := by
  have hev : ∀ᶠ t in atTop,
      exp (-a * t) * pv a σ t + (x 0 - pv a σ 0) = exp (-a * t) * x t := by
    filter_upwards [eventually_ge_atTop 0] with t ht
    have h1 := sub_pv ha hσ hM hx ht
    have e : exp (-a * t) * exp (a * t) = 1 := by
      rw [← exp_add]
      ring_nf
      exact exp_zero
    have : x t = pv a σ t + exp (a * t) * (x 0 - pv a σ 0) := by linarith
    rw [this]
    linear_combination (-(x 0 - pv a σ 0)) * e
  have hdec : Tendsto (fun t => exp (-a * t)) atTop (𝓝 0) := by
    have := tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)
    refine this.congr fun t => ?_
    simp [neg_mul]
  have hpv : Tendsto (fun t => exp (-a * t) * pv a σ t) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun t => exp (-a * t) * (M / a)) (fun t => ?_)
      (by simpa using hdec.mul_const (M / a))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_left (abs_pv_le ha hM t) (exp_pos _).le
  have hlim : Tendsto (fun t => exp (-a * t) * x t) atTop (𝓝 (x 0 - pv a σ 0)) := by
    have := hpv.add_const (x 0 - pv a σ 0)
    rw [zero_add] at this
    exact this.congr' hev
  constructor
  · intro h
    have := tendsto_nhds_unique hlim h
    linarith
  · intro h
    rw [h, sub_self] at hlim
    exact hlim

/-- Cochrane (2023), §6.4.1, p. 196 (D1, transversality in levels): with debt `b_t = x_t y_t`,
GDP `y_t = y₀ e^{g t}` and discount rate `r = a + g > g`, `e^{-r t} b_t → 0` iff `x₀` equals the
present value of surpluses. -/
theorem tvc_levels_iff {g y0 : ℝ} (hy0 : y0 ≠ 0) (ha : 0 < a) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hx : SolvesOn a σ x) :
    Tendsto (fun t => exp (-(a + g) * t) * (x t * (y0 * exp (g * t)))) atTop (𝓝 0) ↔
      x 0 = pv a σ 0 := by
  have e : ∀ t, exp (-(a + g) * t) * (x t * (y0 * exp (g * t))) =
      y0 * (exp (-a * t) * x t) := by
    intro t
    have : exp (-(a + g) * t) * exp (g * t) = exp (-a * t) := by
      rw [← exp_add]
      ring_nf
    linear_combination (y0 * x t) * this
  simp_rw [e]
  rw [← tvc_iff ha hσ hM hx]
  constructor
  · intro h
    have := h.const_mul y0⁻¹
    simp only [mul_zero] at this
    refine this.congr fun t => ?_
    field_simp
  · intro h
    simpa using h.const_mul y0

/-- Cochrane (2023), §6.4.1, p. 196 (D1, nominal debt): for `r > g`, with nominal debt
`B₀ > 0` and GDP `y₀ > 0`, the price level `P₀ > 0` yields a bounded debt-to-GDP path iff
`P₀ = B₀/(y₀ x̂₀)`: the valuation equation determines the price level. -/
theorem nominal_determinacy (ha : 0 < a) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    {B0 y0 P0 : ℝ} (hB0 : 0 < B0) (hy0 : 0 < y0) (hP0 : 0 < P0) :
    (∃ x, SolvesOn a σ x ∧ x 0 = B0 / (P0 * y0) ∧ BddOn x) ↔
      P0 = B0 / (y0 * pv a σ 0) := by
  constructor
  · rintro ⟨x, hx, hx0, hb⟩
    have h := (bddOn_iff ha hσ hM hx).1 hb
    rw [hx0] at h
    have hpv : 0 < pv a σ 0 := by rw [← h]; positivity
    rw [← h]
    field_simp
  · intro hP
    have hpos : 0 < y0 * pv a σ 0 := by
      have : 0 < B0 / (y0 * pv a σ 0) := hP ▸ hP0
      have h2 := (div_pos_iff.1 this)
      rcases h2 with ⟨_, h2⟩ | ⟨h2, _⟩
      · exact h2
      · linarith
    have hpv : 0 < pv a σ 0 := pos_of_mul_pos_right hpos hy0.le
    refine ⟨pv a σ, pv_solvesOn ha hσ hM, ?_, pv_bddOn ha hM⟩
    rw [hP]
    field_simp

/-- Cochrane (2023), §6.4.1, p. 196 (D2): for `r < g` every solution of (6.4) is bounded,
`|x_t| ≤ |x₀| + M/(g - r)`. -/
theorem abs_le_of_neg (ha : a < 0) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hx : SolvesOn a σ x) {t : ℝ} (ht : 0 ≤ t) : |x t| ≤ |x 0| + M / (-a) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hna : 0 < -a := neg_pos.2 ha
  have hI : |∫ u in (0 : ℝ)..t, exp (-a * u) * σ u| ≤ M * ((1 - exp (-a * t)) / a) := by
    have hg : IntervalIntegrable (fun u => M * exp (-a * u)) volume 0 t :=
      (by fun_prop : Continuous (fun u => M * exp (-a * u))).intervalIntegrable _ _
    have := intervalIntegral.norm_integral_le_of_norm_le ht
      (f := fun u => exp (-a * u) * σ u) (ae_of_all _ fun u _ => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), mul_comm]
        exact mul_le_mul_of_nonneg_right (hM u) (exp_pos _).le) hg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      intervalIntegral_exp_neg_mul ha.ne t] at this
    exact this
  have hE : exp (a * t) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  have hE0 := exp_pos (a * t)
  have hprod : exp (a * t) * exp (-a * t) = 1 := by
    rw [← exp_add]
    ring_nf
    exact exp_zero
  rw [solvesOn_eq hσ hx ht]
  unfold vocFrom
  rw [mul_zero, exp_zero, one_mul, abs_mul, abs_of_pos hE0]
  have h1 : |x 0 - ∫ u in (0 : ℝ)..t, exp (-a * u) * σ u| ≤
      |x 0| + M * ((1 - exp (-a * t)) / a) :=
    (abs_sub _ _).trans (by linarith)
  have h2 : exp (a * t) * (M * ((1 - exp (-a * t)) / a)) = M * (1 - exp (a * t)) / (-a) := by
    rw [neg_mul, exp_neg]
    field_simp
    ring
  calc exp (a * t) * |x 0 - ∫ u in (0 : ℝ)..t, exp (-a * u) * σ u|
      ≤ exp (a * t) * (|x 0| + M * ((1 - exp (-a * t)) / a)) :=
        mul_le_mul_of_nonneg_left h1 hE0.le
    _ = exp (a * t) * |x 0| + M * (1 - exp (a * t)) / (-a) := by rw [mul_add, h2]
    _ ≤ |x 0| + M / (-a) := by
        have h3 : exp (a * t) * |x 0| ≤ |x 0| := by
          nlinarith [abs_nonneg (x 0)]
        have h4 : M * (1 - exp (a * t)) / (-a) ≤ M / (-a) := by
          apply div_le_div_of_nonneg_right _ hna.le
          nlinarith
        linarith

/-- Cochrane (2023), §6.4.1, p. 196 (D2): for `r < g` every solution of (6.4) is bounded. -/
theorem bddOn_of_neg (ha : a < 0) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hx : SolvesOn a σ x) : BddOn x :=
  ⟨_, fun _ ht => abs_le_of_neg ha hσ hM hx ht⟩

/-- Cochrane (2023), §6.4.1, p. 196 (D2): for `r < g` any two solutions converge:
`x_t - z_t = e^{a t}(x₀ - z₀) → 0` ("the larger debt-to-GDP ratio melts away"). -/
theorem tendsto_sub_of_neg (ha : a < 0) (hσ : Continuous σ) (hx : SolvesOn a σ x)
    (hz : SolvesOn a σ z) : Tendsto (fun t => x t - z t) atTop (𝓝 0) := by
  have hdec : Tendsto (fun t => exp (a * t)) atTop (𝓝 0) := by
    have := tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (neg_pos.2 ha))
    refine this.congr fun t => ?_
    simp
  have := hdec.mul_const (x 0 - z 0)
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [solvesOn_eq hσ hx ht, solvesOn_eq hσ hz ht, vocFrom_sub]

/-- Cochrane (2023), §6.4.1, p. 196 (D2, "indeterminacy, not infinity"): for `r < g`, every
price level `P₀ > 0` gives a solution of (6.4) from `x₀ = B₀/(P₀ y₀)` that is bounded: boundedness
of the debt-to-GDP ratio cannot select `P₀`. -/
theorem nominal_indeterminacy (ha : a < 0) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (B0 y0 P0 : ℝ) : ∃ x, SolvesOn a σ x ∧ x 0 = B0 / (P0 * y0) ∧ BddOn x :=
  ⟨_, vocFrom_solvesOn a hσ _, vocFrom_self a σ 0 _,
    bddOn_of_neg ha hσ hM (vocFrom_solvesOn a hσ _)⟩

/-- Cochrane (2023), §6.4.1, pp. 195–196 (D2, the transversality condition): for `r < g` and a
constant nonzero surplus ratio `c`, NO solution satisfies `e^{-a t} x_t → 0` (equivalently
`e^{-r t} b_t → 0`): in this sense the present value is infinite for every `P₀`. -/
theorem tvc_fails_of_neg (ha : a < 0) {c : ℝ} (hc : c ≠ 0)
    (hx : SolvesOn a (fun _ => c) x) :
    ¬ Tendsto (fun t => exp (-a * t) * x t) atTop (𝓝 0) := by
  intro h
  have hk : c / a ≠ 0 := div_ne_zero hc ha.ne
  have hform : ∀ t, 0 ≤ t → exp (-a * t) = (exp (-a * t) * x t - (x 0 - c / a)) / (c / a) := by
    intro t ht
    rw [solvesOn_eq continuous_const hx ht]
    unfold vocFrom
    rw [intervalIntegral.integral_mul_const, intervalIntegral_exp_neg_mul ha.ne t, mul_zero,
      exp_zero, one_mul]
    rw [neg_mul, exp_neg]
    have hE := (exp_pos (a * t)).ne'
    have ha0 : a ≠ 0 := ha.ne
    field_simp
    ring
  have hlim : Tendsto (fun t => (exp (-a * t) * x t - (x 0 - c / a)) / (c / a)) atTop
      (𝓝 ((0 - (x 0 - c / a)) / (c / a))) :=
    (h.sub_const _).div_const _
  have hinf : Tendsto (fun t => exp (-a * t)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (neg_pos.2 ha))
  have hlim' : Tendsto (fun t => exp (-a * t)) atTop (𝓝 ((0 - (x 0 - c / a)) / (c / a))) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (hform t ht).symm
  exact not_tendsto_nhds_of_tendsto_atTop hinf _ hlim'

/-- Cochrane (2023), §6.4.1, p. 196 (D3, the knife edge `r = g`): every solution is
`x_t = x₀ - ∫₀^t σ`. -/
theorem eq_of_zero (hσ : Continuous σ) (hx : SolvesOn 0 σ x) {t : ℝ} (ht : 0 ≤ t) :
    x t = x 0 - ∫ u in (0 : ℝ)..t, σ u := by
  rw [solvesOn_eq hσ hx ht]
  unfold vocFrom
  simp

/-- Cochrane (2023), §6.4.1, p. 196 (D3): for `r = g` a solution is bounded iff the cumulated
surplus ratios `∫₀^t σ` are bounded. -/
theorem bddOn_iff_zero (hσ : Continuous σ) (hx : SolvesOn 0 σ x) :
    BddOn x ↔ ∃ K, ∀ t, 0 ≤ t → |∫ u in (0 : ℝ)..t, σ u| ≤ K := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K + |x 0|, fun t ht => ?_⟩
    have h1 := eq_of_zero hσ hx ht
    have h2 := hK t ht
    have : ∫ u in (0 : ℝ)..t, σ u = x 0 - x t := by linarith
    rw [this]
    exact (abs_sub _ _).trans (by linarith)
  · rintro ⟨K, hK⟩
    refine ⟨|x 0| + K, fun t ht => ?_⟩
    rw [eq_of_zero hσ hx ht]
    exact (abs_sub _ _).trans (by linarith [hK t ht])

/-- Cochrane (2023), §6.4.1, p. 196 (D3): for `r = g` and a constant nonzero surplus ratio, no
solution is bounded. -/
theorem not_bddOn_zero_const {c : ℝ} (hc : c ≠ 0) (hx : SolvesOn 0 (fun _ => c) x) :
    ¬ BddOn x := by
  rw [bddOn_iff_zero continuous_const hx]
  rintro ⟨K, hK⟩
  have hcpos : 0 < |c| := abs_pos.2 hc
  have := hK ((|K| + 1) / |c|) (by positivity)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (|K| + 1) / |c|), div_mul_cancel₀ _ hcpos.ne'] at this
  linarith [le_abs_self K]

/-! ### (D4) Temporary `r < g` -/

/-- Cochrane (2023), §6.4.1, p. 196: `x` solves (6.4) on `[0, ∞)` with `r - g = a₁` before `T₀`
and `r - g = a₂` after (continuous on `[0, ∞)`, the ODE on `(0, T₀)` and on `(T₀, ∞)`). -/
def SolvesStep (a₁ a₂ T0 : ℝ) (σ x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧ (∀ t ∈ Set.Ioo 0 T0, HasDerivAt x (a₁ * x t - σ t) t) ∧
    ∀ t, T0 < t → HasDerivAt x (a₂ * x t - σ t) t

/-- Cochrane (2023), §6.4.1, p. 196 (corrected 20-year formula, survey E6.2): the forward present
value at date 0 with time-varying discounting,
`x̂₀ = ∫₀^{T₀} e^{-a₁ v} σ_v dv + e^{-a₁ T₀} ∫₀^∞ e^{-a₂ u} σ_{T₀+u} du`. -/
noncomputable def stepPV0 (a₁ a₂ T0 : ℝ) (σ : ℝ → ℝ) : ℝ :=
  (∫ v in (0 : ℝ)..T0, exp (-a₁ * v) * σ v) + exp (-a₁ * T0) * pv a₂ σ T0

/-- Cochrane (2023), §6.4.1, p. 196 (corrected 20-year formula at every date): the forward
present value `∫₀^∞ exp(-∫_t^{t+u} a) σ_{t+u} du`, written out for the two-regime `a`. -/
noncomputable def pvStep (a₁ a₂ T0 : ℝ) (σ : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ T0 then
    (∫ v in t..T0, exp (-a₁ * (v - t)) * σ v) + exp (-a₁ * (T0 - t)) * pv a₂ σ T0
  else pv a₂ σ t

/-- Cochrane (2023), §6.4.1, p. 196: the glued solution: the backward solution from `x̂₀` before
`T₀`, the forward present value after. -/
noncomputable def stepSol (a₁ a₂ T0 : ℝ) (σ : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ T0 then vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ) t else pv a₂ σ t

/-- Cochrane (2023), eq. (6.5), p. 196: two backward solutions from the same date `t₀` differ by
`e^{a(t - t₀)}(x₀ - z₀)`. -/
theorem vocFrom_sub_from (a : ℝ) (σ : ℝ → ℝ) (t0 x0 z0 t : ℝ) :
    vocFrom a σ t0 x0 t - vocFrom a σ t0 z0 t = exp (a * (t - t0)) * (x0 - z0) := by
  unfold vocFrom
  have : exp (a * t) * exp (-a * t0) = exp (a * (t - t0)) := by rw [← exp_add]; ring_nf
  linear_combination (x0 - z0) * this

/-- Cochrane (2023), §6.4.1, p. 196: started from `x̂₀`, the backward solution reaches the forward
present value of the post-`T₀` surpluses at `T₀`. -/
theorem vocFrom_stepPV0 (a₁ a₂ T0 : ℝ) (σ : ℝ → ℝ) :
    vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ) T0 = pv a₂ σ T0 := by
  unfold vocFrom stepPV0
  rw [mul_zero, exp_zero, one_mul, add_sub_cancel_left, ← mul_assoc, ← exp_add]
  ring_nf
  rw [exp_zero, one_mul]

/-- Cochrane (2023), §6.4.1, p. 196: a two-regime solution, after `T₀`, is the backward solution
from its value at `T₀`. -/
theorem step_after (hσ : Continuous σ) {a₁ a₂ T0 : ℝ} (hT0 : 0 ≤ T0)
    (hx : SolvesStep a₁ a₂ T0 σ x) {t : ℝ} (ht : T0 ≤ t) :
    x t = vocFrom a₂ σ T0 (x T0) t :=
  eq_vocFrom a₂ hσ ht (hx.1.mono fun _ hs => le_trans hT0 hs.1) (fun s hs => hx.2.2 s hs.1)

/-- Cochrane (2023), §6.4.1, p. 196: a two-regime solution, before `T₀`, is the backward solution
from its initial value. -/
theorem step_before (hσ : Continuous σ) {a₁ a₂ T0 : ℝ} (hx : SolvesStep a₁ a₂ T0 σ x) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ T0) : x t = vocFrom a₁ σ 0 (x 0) t :=
  eq_vocFrom a₁ hσ ht0 (hx.1.mono Set.Icc_subset_Ici_self)
    (fun s hs => hx.2.1 s ⟨hs.1, lt_of_lt_of_le hs.2 ht⟩)

/-- Cochrane (2023), §6.4.1, p. 196: after `T₀` every two-regime solution differs from the forward
present value by `e^{a₂(t - T₀)} e^{a₁ T₀}(x₀ - x̂₀)`. -/
theorem step_sub_pv (ha₂ : 0 < a₂) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) {a₁ T0 : ℝ}
    (hT0 : 0 ≤ T0) (hx : SolvesStep a₁ a₂ T0 σ x) {t : ℝ} (ht : T0 ≤ t) :
    x t - pv a₂ σ t =
      exp (a₂ * (t - T0)) * (exp (a₁ * T0) * (x 0 - stepPV0 a₁ a₂ T0 σ)) := by
  have hpv : pv a₂ σ t = vocFrom a₂ σ T0 (pv a₂ σ T0) t :=
    eq_vocFrom a₂ hσ ht (fun s _ => (pv_hasDerivAt ha₂ hσ hM s).continuousAt.continuousWithinAt)
      (fun s _ => pv_hasDerivAt ha₂ hσ hM s)
  rw [step_after hσ hT0 hx ht, hpv, vocFrom_sub_from]
  congr 1
  rw [step_before hσ hx hT0 le_rfl, ← vocFrom_stepPV0 a₁ a₂ T0 σ, vocFrom_sub]

/-- Cochrane (2023), §6.4.1, p. 196 (D4): with temporary `r < g`, a solution that does not start
at the forward present value `x̂₀` explodes: `|x_t| → ∞`. -/
theorem step_tendsto_abs_of_ne (ha₂ : 0 < a₂) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    {a₁ T0 : ℝ} (hT0 : 0 ≤ T0) (hx : SolvesStep a₁ a₂ T0 σ x)
    (hne : x 0 ≠ stepPV0 a₁ a₂ T0 σ) : Tendsto (fun t => |x t|) atTop atTop := by
  set d := exp (a₁ * T0) * |x 0 - stepPV0 a₁ a₂ T0 σ| with hd_def
  have hd : 0 < d := mul_pos (exp_pos _) (abs_pos.2 (sub_ne_zero.2 hne))
  have hlow : ∀ t, T0 ≤ t → exp (a₂ * (t - T0)) * d + -(M / a₂) ≤ |x t| := by
    intro t ht
    have h1 := step_sub_pv ha₂ hσ hM hT0 hx ht
    have h2 := abs_pv_le ha₂ hM t
    have h3 : exp (a₂ * (t - T0)) * d = |x t - pv a₂ σ t| := by
      rw [h1, abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_pos (exp_pos _), hd_def]
    have h4 := abs_sub (x t) (pv a₂ σ t)
    linarith
  have hlim : Tendsto (fun t => exp (a₂ * (t - T0)) * d + -(M / a₂)) atTop atTop := by
    have h1 : Tendsto (fun t => a₂ * (t - T0)) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-T0) tendsto_id).const_mul_atTop ha₂
    exact tendsto_atTop_add_const_right _ _ ((tendsto_exp_atTop.comp h1).atTop_mul_const hd)
  exact tendsto_atTop_mono' atTop ((eventually_ge_atTop T0).mono hlow) hlim

/-- Cochrane (2023), §6.4.1, p. 196 (D4): with temporary `r < g` (`a₂ > 0` after `T₀`), a solution
is bounded iff it starts at the forward present value `x̂₀`: "values of debt different from this
forward-looking integral lead to explosions". -/
theorem step_bddOn_iff (ha₂ : 0 < a₂) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) {a₁ T0 : ℝ}
    (hT0 : 0 ≤ T0) (hx : SolvesStep a₁ a₂ T0 σ x) :
    BddOn x ↔ x 0 = stepPV0 a₁ a₂ T0 σ := by
  constructor
  · rintro ⟨K, hK⟩
    by_contra hne
    have h1 := (step_tendsto_abs_of_ne ha₂ hσ hM hT0 hx hne).eventually_gt_atTop K
    obtain ⟨t, ht1, ht2⟩ := (h1.and (eventually_ge_atTop 0)).exists
    linarith [hK t ht2]
  · intro h
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T0)).exists_bound_of_continuousOn
      (hx.1.mono Set.Icc_subset_Ici_self)
    refine ⟨max C (M / a₂), fun t ht => ?_⟩
    rcases le_total t T0 with htT | htT
    · exact (hC t ⟨ht, htT⟩).trans (le_max_left _ _)
    · have := step_sub_pv ha₂ hσ hM hT0 hx htT
      rw [h, sub_self, mul_zero, mul_zero, sub_eq_zero] at this
      rw [this]
      exact (abs_pv_le ha₂ hM t).trans (le_max_right _ _)

/-- Cochrane (2023), §6.4.1, p. 196 (D4): the bounded solution at every date `t ≤ T₀` is the
forward present value with time-varying discounting,
`x̂_t = ∫_t^{T₀} e^{-a₁(v-t)} σ_v dv + e^{-a₁(T₀-t)} x̂^{(2)}_{T₀}`. -/
theorem vocFrom_stepPV0_eq (hσ : Continuous σ) (a₁ a₂ T0 t : ℝ) :
    vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ) t =
      (∫ v in t..T0, exp (-a₁ * (v - t)) * σ v) + exp (-a₁ * (T0 - t)) * pv a₂ σ T0 := by
  have hf : Continuous (fun v => exp (-a₁ * v) * σ v) := by fun_prop
  have hsplit := intervalIntegral.integral_interval_sub_left
    (hf.intervalIntegrable (μ := volume) 0 T0) (hf.intervalIntegrable (μ := volume) 0 t)
  unfold vocFrom stepPV0
  rw [mul_zero, exp_zero, one_mul]
  have e1 : (∫ v in (0 : ℝ)..T0, exp (-a₁ * v) * σ v) + exp (-a₁ * T0) * pv a₂ σ T0 -
      ∫ v in (0 : ℝ)..t, exp (-a₁ * v) * σ v =
      (∫ v in t..T0, exp (-a₁ * v) * σ v) + exp (-a₁ * T0) * pv a₂ σ T0 := by
    rw [← hsplit]
    ring
  rw [e1, mul_add, ← intervalIntegral.integral_const_mul, ← mul_assoc, ← exp_add]
  congr 1
  · congr 1
    funext v
    rw [← mul_assoc, ← exp_add]
    ring_nf
  · ring_nf

/-- Cochrane (2023), §6.4.1, p. 196 (D4): the glued path coincides with the forward present value
`pvStep` at every date. -/
theorem stepSol_eq_pvStep (hσ : Continuous σ) (a₁ a₂ T0 t : ℝ) :
    stepSol a₁ a₂ T0 σ t = pvStep a₁ a₂ T0 σ t := by
  unfold stepSol pvStep
  split_ifs
  · exact vocFrom_stepPV0_eq hσ a₁ a₂ T0 t
  · rfl

/-- Cochrane (2023), §6.4.1, p. 196 (D4): the glued path solves the two-regime equation. -/
theorem stepSol_solvesStep (ha₂ : 0 < a₂) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (a₁ T0 : ℝ) : SolvesStep a₁ a₂ T0 σ (stepSol a₁ a₂ T0 σ) := by
  have hv : ∀ t, HasDerivAt (vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ))
      (a₁ * vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ) t - σ t) t :=
    fun t => vocFrom_hasDerivAt a₁ hσ 0 _ t
  have hp : ∀ t, HasDerivAt (pv a₂ σ) (a₂ * pv a₂ σ t - σ t) t :=
    fun t => pv_hasDerivAt ha₂ hσ hM t
  have hcont : Continuous (stepSol a₁ a₂ T0 σ) := by
    unfold stepSol
    refine Continuous.if_le (continuous_iff_continuousAt.2 fun t => (hv t).continuousAt)
      (continuous_iff_continuousAt.2 fun t => (hp t).continuousAt) continuous_id
      continuous_const ?_
    intro t ht
    rw [ht]
    exact vocFrom_stepPV0 a₁ a₂ T0 σ
  refine ⟨hcont.continuousOn, fun t ht => ?_, fun t ht => ?_⟩
  · have hev : stepSol a₁ a₂ T0 σ =ᶠ[𝓝 t] vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ) := by
      filter_upwards [eventually_lt_nhds ht.2] with s hs
      unfold stepSol
      simp only [hs.le, ↓reduceIte]
    have h := (hv t).congr_of_eventuallyEq hev
    rw [show stepSol a₁ a₂ T0 σ t = vocFrom a₁ σ 0 (stepPV0 a₁ a₂ T0 σ) t from hev.eq_of_nhds]
    exact h
  · have hev : stepSol a₁ a₂ T0 σ =ᶠ[𝓝 t] pv a₂ σ := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      unfold stepSol
      simp only [not_le.2 hs, ↓reduceIte]
    have h := (hp t).congr_of_eventuallyEq hev
    rw [show stepSol a₁ a₂ T0 σ t = pv a₂ σ t from hev.eq_of_nhds]
    exact h

/-- Cochrane (2023), §6.4.1, p. 196 (D4): with temporary `r < g` and permanent `r > g` after
`T₀ ≥ 0`, there is exactly one bounded solution: it exists (`stepSol`), and every bounded solution
equals the forward present value `pvStep` at every date `t ≥ 0`. -/
theorem step_existsUnique (ha₂ : 0 < a₂) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    {a₁ T0 : ℝ} (hT0 : 0 ≤ T0) :
    SolvesStep a₁ a₂ T0 σ (stepSol a₁ a₂ T0 σ) ∧ BddOn (stepSol a₁ a₂ T0 σ) ∧
      ∀ x, SolvesStep a₁ a₂ T0 σ x → BddOn x → ∀ t, 0 ≤ t → x t = pvStep a₁ a₂ T0 σ t := by
  have hS := stepSol_solvesStep ha₂ hσ hM a₁ T0
  have h0 : stepSol a₁ a₂ T0 σ 0 = stepPV0 a₁ a₂ T0 σ := by
    unfold stepSol
    simp only [hT0, ↓reduceIte, vocFrom_self]
  refine ⟨hS, (step_bddOn_iff ha₂ hσ hM hT0 hS).2 h0, fun x hx hb t ht => ?_⟩
  have hx0 := (step_bddOn_iff ha₂ hσ hM hT0 hx).1 hb
  rw [← stepSol_eq_pvStep hσ]
  rcases le_total t T0 with htT | htT
  · rw [step_before hσ hx ht htT, hx0]
    unfold stepSol
    simp only [htT, ↓reduceIte]
  · have h1 := step_sub_pv ha₂ hσ hM hT0 hx htT
    rw [hx0, sub_self, mul_zero, mul_zero, sub_eq_zero] at h1
    rw [h1]
    unfold stepSol
    rcases eq_or_lt_of_le htT with h | h
    · simp only [h.ge, ↓reduceIte]
      rw [← h, vocFrom_stepPV0]
    · simp only [not_le.2 h, ↓reduceIte]

/-- Cochrane (2023), §6.4.1, p. 196 (corrected 20-year formula, survey E6.2): with
`r - g = -1%` for 20 years and `+1%` after, the unique non-explosive initial debt-to-GDP ratio is
`∫₀^{20} e^{0.01τ} σ_τ dτ + e^{0.01·20} ∫_{20}^∞ e^{-0.01(τ-20)} σ_τ dτ`: the book's display with
FUTURE surplus ratios `σ_{t+τ}` (at `t = 0`). -/
theorem book_twenty_year_formula (σ : ℝ → ℝ) :
    stepPV0 (-0.01) 0.01 20 σ = (∫ τ in (0 : ℝ)..20, exp (0.01 * τ) * σ τ) +
      exp (0.01 * 20) * ∫ τ in Set.Ioi (20 : ℝ), exp (-0.01 * (τ - 20)) * σ τ := by
  unfold stepPV0 pv
  rw [← integral_Ioi_comp_add (fun τ => exp (-0.01 * (τ - 20)) * σ τ) 20]
  congr 2
  · funext τ
    ring_nf
  · ring_nf
  · congr 1
    funext u
    ring_nf

/-- Cochrane (2023), §6.4.1, p. 196, the 20-year display as printed (at `t = 0`): it discounts
PAST surplus ratios `σ_{t-τ}`. -/
noncomputable def printed20 (σ : ℝ → ℝ) : ℝ :=
  (∫ τ in (0 : ℝ)..20, exp (0.01 * τ) * σ (0 - τ)) +
    exp (0.01 * 20) * ∫ τ in Set.Ioi (20 : ℝ), exp (-0.01 * (τ - 20)) * σ (0 - τ)

/-- Cochrane (2023), §6.4.1, p. 196 (survey E6.2): a surplus path that is zero from date 0 on but
positive in the past, `σ_v = min(1, max(0, -v))`. -/
noncomputable def pastOnly (v : ℝ) : ℝ := min 1 (max 0 (-v))

/-- Cochrane (2023), §6.4.1, p. 196 (survey E6.2): the printed 20-year formula is wrong. For the
surplus path `pastOnly` (zero from date 0 on), the unique bounded solution starts at `x̂₀ = 0`, but
the printed formula is strictly positive. -/
theorem printed20_wrong :
    stepPV0 (-0.01) 0.01 20 pastOnly = 0 ∧ 0 < printed20 pastOnly := by
  have hc : Continuous pastOnly := by unfold pastOnly; fun_prop
  have hM : ∀ u, |pastOnly u| ≤ 1 := by
    intro u
    unfold pastOnly
    rw [abs_le]
    constructor
    · exact le_min (by norm_num) (le_trans (by norm_num) (le_max_left 0 (-u)))
    · exact min_le_left _ _
  have hz : ∀ t, 0 ≤ t → pastOnly t = 0 := by
    intro t ht
    unfold pastOnly
    rw [max_eq_left (by linarith), min_eq_right (by norm_num)]
  refine ⟨?_, ?_⟩
  · have hS : SolvesStep (-0.01) 0.01 20 pastOnly (fun _ => 0) := by
      refine ⟨continuousOn_const, fun t ht => ?_, fun t ht => ?_⟩
      · rw [hz t ht.1.le, mul_zero, sub_zero]
        exact hasDerivAt_const t 0
      · rw [hz t (by linarith), mul_zero, sub_zero]
        exact hasDerivAt_const t 0
    have := (step_bddOn_iff (by norm_num) hc hM (by norm_num) hS).1
      ⟨0, fun _ _ => by simp⟩
    exact this.symm
  · unfold printed20
    have h1 : 0 < ∫ τ in (0 : ℝ)..20, exp (0.01 * τ) * pastOnly (0 - τ) := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on
        ((by fun_prop : Continuous fun τ => exp (0.01 * τ) * pastOnly (0 - τ)).intervalIntegrable
          _ _) (fun τ hτ => ?_) (by norm_num)
      refine mul_pos (exp_pos _) ?_
      unfold pastOnly
      rw [zero_sub, neg_neg, max_eq_right hτ.1.le]
      exact lt_min (by norm_num) hτ.1
    have h2 : 0 ≤ ∫ τ in Set.Ioi (20 : ℝ), exp (-0.01 * (τ - 20)) * pastOnly (0 - τ) := by
      refine setIntegral_nonneg measurableSet_Ioi fun τ _ => ?_
      refine mul_nonneg (exp_pos _).le ?_
      unfold pastOnly
      exact le_min (by norm_num) (le_max_left _ _)
    have h3 := exp_pos (0.01 * 20 : ℝ)
    nlinarith

/-! ### (D5) Discrete time -/

/-- Cochrane (2023), §6.4.1, p. 196 (discrete analogue of (6.4)): `x_{t+1} = γ x_t - w_t`, with
`γ = (1+r)/(1+g)`. -/
def SolvesD (γ : ℝ) (w x : ℕ → ℝ) : Prop := ∀ t, x (t + 1) = γ * x t - w t

/-- Cochrane (2023), §6.4.1, p. 196: a bounded sequence. -/
def BddD (x : ℕ → ℝ) : Prop := ∃ K, ∀ t, |x t| ≤ K

/-- Cochrane (2023), §6.4.1, p. 196: the discrete forward present value
`x̂_t = ∑_{j ≥ 0} w_{t+j}/γ^{j+1}`. -/
noncomputable def pvD (γ : ℝ) (w : ℕ → ℝ) (t : ℕ) : ℝ := ∑' j : ℕ, w (t + j) / γ ^ (j + 1)

/-- Cochrane (2023), §6.4.1, p. 196: the discrete backward solution from `x₀`. -/
noncomputable def iterD (γ : ℝ) (w : ℕ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | t + 1 => γ * iterD γ w x0 t - w t

variable {γ : ℝ} {w y v : ℕ → ℝ}

/-- Cochrane (2023), §6.4.1, p. 196: `γ = (1+r)/(1+g) > 1` iff `r > g` (for `1 + g > 0`). -/
theorem gamma_gt_one_iff {r g : ℝ} (hg : 0 < 1 + g) : 1 < (1 + r) / (1 + g) ↔ g < r := by
  rw [one_lt_div hg]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §6.4.1, p. 196: the backward solution solves the discrete equation. -/
theorem iterD_solves (γ : ℝ) (w : ℕ → ℝ) (x0 : ℝ) : SolvesD γ w (iterD γ w x0) := fun _ => rfl

/-- Cochrane (2023), §6.4.1, p. 196: two discrete solutions differ by `γ^t (x₀ - z₀)`. -/
theorem solvesD_sub (hy : SolvesD γ w y) (hv : SolvesD γ w v) (t : ℕ) :
    y t - v t = γ ^ t * (y 0 - v 0) := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hy n, hv n, pow_succ]
    linear_combination γ * ih

/-- Cochrane (2023), §6.4.1, p. 196: the terms of the discrete present value are bounded by
`(M/γ)(1/γ)^j`. -/
theorem abs_pvD_term_le (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (t j : ℕ) :
    |w (t + j) / γ ^ (j + 1)| ≤ M / γ * (1 / γ) ^ j := by
  have hγ0 : 0 < γ := by linarith
  rw [abs_div, abs_of_pos (pow_pos hγ0 _), div_le_iff₀ (pow_pos hγ0 _)]
  calc |w (t + j)| ≤ M := hw _
    _ = M / γ * (1 / γ) ^ j * γ ^ (j + 1) := by
        rw [div_pow, one_pow, pow_succ]
        field_simp

/-- Cochrane (2023), §6.4.1, p. 196: for `γ > 1` and bounded `w` the discrete present value is an
absolutely convergent series. -/
theorem summable_pvD (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (t : ℕ) :
    Summable (fun j : ℕ => w (t + j) / γ ^ (j + 1)) := by
  have hγ0 : 0 < γ := by linarith
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (by positivity)
    ((div_lt_one hγ0).2 hγ)).mul_left (M / γ)) (fun j => ?_)
  rw [Real.norm_eq_abs]
  exact abs_pvD_term_le hγ hw t j

/-- Cochrane (2023), §6.4.1, p. 196: `|x̂_t| ≤ M/(γ - 1)`. -/
theorem abs_pvD_le (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (t : ℕ) : |pvD γ w t| ≤ M / (γ - 1) := by
  have hγ0 : 0 < γ := by linarith
  have hq0 : (0 : ℝ) ≤ 1 / γ := by positivity
  have hq1 : 1 / γ < 1 := (div_lt_one hγ0).2 hγ
  have hg := (summable_geometric_of_lt_one hq0 hq1).mul_left (M / γ)
  have hn : Summable (fun j : ℕ => ‖w (t + j) / γ ^ (j + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun j => (Real.norm_eq_abs _).trans_le (abs_pvD_term_le hγ hw t j)) hg
  have hsum : ∑' j : ℕ, M / γ * (1 / γ) ^ j = M / (γ - 1) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    have : γ - 1 ≠ 0 := by linarith
    field_simp
  calc |pvD γ w t| = ‖∑' j : ℕ, w (t + j) / γ ^ (j + 1)‖ := rfl
    _ ≤ ∑' j : ℕ, ‖w (t + j) / γ ^ (j + 1)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j : ℕ, M / γ * (1 / γ) ^ j :=
        Summable.tsum_le_tsum (fun j => (Real.norm_eq_abs _).trans_le
          (abs_pvD_term_le hγ hw t j)) hn hg
    _ = M / (γ - 1) := hsum

/-- Cochrane (2023), §6.4.1, p. 196: the present value satisfies `x̂_t = (w_t + x̂_{t+1})/γ`. -/
theorem pvD_succ (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (t : ℕ) :
    pvD γ w t = (w t + pvD γ w (t + 1)) / γ := by
  have hγ0 : γ ≠ 0 := by linarith
  unfold pvD
  rw [(summable_pvD hγ hw t).tsum_eq_zero_add]
  have : ∀ j : ℕ, w (t + (j + 1)) / γ ^ (j + 1 + 1) = w (t + 1 + j) / γ ^ (j + 1) / γ := by
    intro j
    rw [show t + (j + 1) = t + 1 + j by ring, pow_succ γ (j + 1)]
    field_simp
  simp_rw [this, tsum_div_const]
  simp only [add_zero, zero_add, pow_one]
  ring

/-- Cochrane (2023), §6.4.1, p. 196 (D5): for `γ > 1` the present value solves the discrete
equation. -/
theorem pvD_solves (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) : SolvesD γ w (pvD γ w) := by
  intro t
  have hγ0 : γ ≠ 0 := by linarith
  rw [pvD_succ hγ hw t]
  field_simp
  ring

/-- Cochrane (2023), §6.4.1, p. 196 (D5): for `γ > 1` a solution that does not start at the
present value explodes. -/
theorem tendsto_abs_of_ne_D (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (hy : SolvesD γ w y)
    (hne : y 0 ≠ pvD γ w 0) : Tendsto (fun t => |y t|) atTop atTop := by
  set d := |y 0 - pvD γ w 0| with hd_def
  have hd : 0 < d := abs_pos.2 (sub_ne_zero.2 hne)
  have hγ0 : 0 < γ := by linarith
  have hlow : ∀ t, γ ^ t * d + -(M / (γ - 1)) ≤ |y t| := by
    intro t
    have h1 := solvesD_sub hy (pvD_solves hγ hw) t
    have h2 := abs_pvD_le hγ hw t
    have h3 : γ ^ t * d = |y t - pvD γ w t| := by
      rw [h1, abs_mul, abs_of_pos (pow_pos hγ0 _)]
    have h4 := abs_sub (y t) (pvD γ w t)
    linarith
  exact tendsto_atTop_mono hlow (tendsto_atTop_add_const_right _ _
    ((tendsto_pow_atTop_atTop_of_one_lt hγ).atTop_mul_const hd))

/-- Cochrane (2023), §6.4.1, p. 196 (D5): for `γ > 1` a discrete solution is bounded iff it
starts at the present value. -/
theorem bddD_iff (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (hy : SolvesD γ w y) :
    BddD y ↔ y 0 = pvD γ w 0 := by
  constructor
  · rintro ⟨K, hK⟩
    by_contra hne
    obtain ⟨t, ht⟩ := ((tendsto_abs_of_ne_D hγ hw hy hne).eventually_gt_atTop K).exists
    linarith [hK t]
  · intro h
    refine ⟨M / (γ - 1), fun t => ?_⟩
    have := solvesD_sub hy (pvD_solves hγ hw) t
    rw [h, sub_self, mul_zero, sub_eq_zero] at this
    rw [this]
    exact abs_pvD_le hγ hw t

/-- Cochrane (2023), §6.4.1, p. 196 (D5): for `γ > 1` the unique bounded solution is
`x_t = ∑_j w_{t+j}/γ^{j+1}` at every date. -/
theorem eq_pvD_of_bddD (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (hy : SolvesD γ w y) (hb : BddD y)
    (t : ℕ) : y t = pvD γ w t := by
  have := solvesD_sub hy (pvD_solves hγ hw) t
  rw [(bddD_iff hγ hw hy).1 hb, sub_self, mul_zero, sub_eq_zero] at this
  exact this

/-- Cochrane (2023), §6.4.1, p. 196 (D5, transversality): for `γ > 1`, `x_t/γ^t → 0` iff the
solution starts at the present value. -/
theorem tvcD_iff (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) (hy : SolvesD γ w y) :
    Tendsto (fun t => y t / γ ^ t) atTop (𝓝 0) ↔ y 0 = pvD γ w 0 := by
  have hγ0 : 0 < γ := by linarith
  have he : ∀ t, pvD γ w t / γ ^ t + (y 0 - pvD γ w 0) = y t / γ ^ t := by
    intro t
    have h1 := solvesD_sub hy (pvD_solves hγ hw) t
    have hp := (pow_pos hγ0 t).ne'
    field_simp
    linarith
  have hq : Tendsto (fun t : ℕ => (1 / γ) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hγ0).2 hγ)
  have hpv : Tendsto (fun t => pvD γ w t / γ ^ t) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun t => M / (γ - 1) * (1 / γ) ^ t) (fun t => ?_)
      (by simpa using hq.const_mul (M / (γ - 1)))
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hγ0 _), div_pow, one_pow,
      ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right (abs_pvD_le hγ hw t) (pow_pos hγ0 _).le
  have hlim : Tendsto (fun t => y t / γ ^ t) atTop (𝓝 (y 0 - pvD γ w 0)) := by
    have := hpv.add_const (y 0 - pvD γ w 0)
    rw [zero_add] at this
    exact this.congr he
  constructor
  · intro h
    have := tendsto_nhds_unique hlim h
    linarith
  · intro h
    rw [h, sub_self] at hlim
    exact hlim

/-- Cochrane (2023), §6.4.1, p. 196 (D5): for `0 ≤ γ < 1` every discrete solution is bounded,
`|x_t| ≤ |x₀| + M/(1 - γ)`. -/
theorem abs_le_of_lt_one (hγ0 : 0 ≤ γ) (hγ : γ < 1) (hw : ∀ t, |w t| ≤ M) (hy : SolvesD γ w y)
    (t : ℕ) : |y t| ≤ |y 0| + M / (1 - γ) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hw 0)
  have h1γ : 0 < 1 - γ := by linarith
  have hB : 0 ≤ M / (1 - γ) := div_nonneg hM0 h1γ.le
  induction t with
  | zero => linarith
  | succ n ih =>
    rw [hy n]
    have hkey : γ * (M / (1 - γ)) + M = M / (1 - γ) := by
      field_simp
      ring
    calc |γ * y n - w n| ≤ |γ * y n| + |w n| := abs_sub _ _
      _ = γ * |y n| + |w n| := by rw [abs_mul, abs_of_nonneg hγ0]
      _ ≤ γ * (|y 0| + M / (1 - γ)) + M := by gcongr; exact hw n
      _ ≤ |y 0| + M / (1 - γ) := by nlinarith [abs_nonneg (y 0)]

/-- Cochrane (2023), §6.4.1, p. 196 (D5): for `0 ≤ γ < 1` any two discrete solutions converge. -/
theorem tendsto_sub_D (hγ0 : 0 ≤ γ) (hγ : γ < 1) (hy : SolvesD γ w y) (hv : SolvesD γ w v) :
    Tendsto (fun t => y t - v t) atTop (𝓝 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ).mul_const (y 0 - v 0)
  rw [zero_mul] at this
  exact this.congr fun t => (solvesD_sub hy hv t).symm

/-- Cochrane (2023), §6.4.1, p. 196 (D5, knife edge `γ = 1`): `x_t = x₀ - ∑_{j<t} w_j`. -/
theorem eq_of_one (hy : SolvesD 1 w y) (t : ℕ) : y t = y 0 - ∑ j ∈ Finset.range t, w j := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hy n, ih, Finset.sum_range_succ]
    ring

/-- Cochrane (2023), §6.4.1, p. 196 (D5, knife edge): for `γ = 1` a solution is bounded iff
the partial sums of `w` are bounded. -/
theorem bddD_iff_one (hy : SolvesD 1 w y) :
    BddD y ↔ ∃ K, ∀ t, |∑ j ∈ Finset.range t, w j| ≤ K := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K + |y 0|, fun t => ?_⟩
    have h1 := eq_of_one hy t
    have : ∑ j ∈ Finset.range t, w j = y 0 - y t := by linarith
    rw [this]
    exact (abs_sub _ _).trans (by linarith [hK t])
  · rintro ⟨K, hK⟩
    refine ⟨|y 0| + K, fun t => ?_⟩
    rw [eq_of_one hy t]
    exact (abs_sub _ _).trans (by linarith [hK t])

/-- Cochrane (2023), §6.4.1, p. 196 (D5, nominal debt): for `γ > 1` the price level `P₀ > 0`
yields a bounded path from `x₀ = B₀/(P₀ y₀)` iff `P₀ = B₀/(y₀ x̂₀)`. -/
theorem nominal_determinacy_D (hγ : 1 < γ) (hw : ∀ t, |w t| ≤ M) {B0 y0 P0 : ℝ} (hB0 : 0 < B0)
    (hy0 : 0 < y0) (hP0 : 0 < P0) :
    (∃ x, SolvesD γ w x ∧ x 0 = B0 / (P0 * y0) ∧ BddD x) ↔ P0 = B0 / (y0 * pvD γ w 0) := by
  constructor
  · rintro ⟨x, hx, hx0, hb⟩
    have h := (bddD_iff hγ hw hx).1 hb
    rw [hx0] at h
    have hpv : 0 < pvD γ w 0 := by rw [← h]; positivity
    rw [← h]
    field_simp
  · intro hP
    have hpos : 0 < y0 * pvD γ w 0 := by
      have : 0 < B0 / (y0 * pvD γ w 0) := hP ▸ hP0
      rcases div_pos_iff.1 this with ⟨_, h2⟩ | ⟨h2, _⟩
      · exact h2
      · linarith
    have hpv : 0 < pvD γ w 0 := pos_of_mul_pos_right hpos hy0.le
    refine ⟨pvD γ w, pvD_solves hγ hw, ?_, ⟨_, abs_pvD_le hγ hw⟩⟩
    rw [hP]
    field_simp

/-- Cochrane (2023), §6.4.1, p. 196 (D5, "indeterminacy, not infinity"): for `0 ≤ γ < 1` every
price level gives a bounded discrete debt-to-GDP path. -/
theorem nominal_indeterminacy_D (hγ0 : 0 ≤ γ) (hγ : γ < 1) (hw : ∀ t, |w t| ≤ M)
    (B0 y0 P0 : ℝ) : ∃ x, SolvesD γ w x ∧ x 0 = B0 / (P0 * y0) ∧ BddD x :=
  ⟨iterD γ w (B0 / (P0 * y0)), iterD_solves γ w _, rfl,
    ⟨_, abs_le_of_lt_one hγ0 hγ hw (iterD_solves γ w _)⟩⟩

/-! ### (D6) Flows and the `r = g` discontinuity; numbers -/

/-- Cochrane (2023), §6.4.2, p. 198 (D6): a constant debt-to-GDP ratio `x*` solves (6.4) with a
constant surplus ratio `σ*` iff `σ* = (r - g) x*`. -/
theorem steady_state_iff (a xs ss : ℝ) :
    SolvesOn a (fun _ => ss) (fun _ => xs) ↔ ss = a * xs := by
  constructor
  · rintro ⟨-, h⟩
    have := (h 1 one_pos).unique (hasDerivAt_const (1 : ℝ) xs)
    linarith
  · intro h
    refine ⟨continuousOn_const, fun t _ => ?_⟩
    rw [h, sub_self]
    exact hasDerivAt_const t xs

/-- Cochrane (2023), §6.4.2, p. 198 (D6): the steady-state surplus `(r - g) x*` is continuous in
`r - g`, in particular across `r = g`. -/
theorem steady_surplus_continuous (xs : ℝ) : Continuous (fun a : ℝ => a * xs) :=
  continuous_id.mul continuous_const

/-- Cochrane (2023), §6.4.2, p. 198 (D6, discrete): a constant `x*` solves the discrete equation
with constant `w*` iff `w* = (γ - 1) x*`. -/
theorem steady_state_iff_D (γ xs ws : ℝ) :
    SolvesD γ (fun _ => ws) (fun _ => xs) ↔ ws = (γ - 1) * xs := by
  constructor
  · intro h
    have := h 0
    linarith
  · intro h t
    rw [h]
    ring

/-- Cochrane (2023), §6.4.2, p. 198: at 100% debt-to-GDP, `r - g = ±0.01%` needs a steady surplus
of `±0.01%` of GDP. -/
theorem book_flow_basis_point :
    SolvesOn 0.0001 (fun _ => 0.0001) (fun _ => 1) ∧
      SolvesOn (-0.0001) (fun _ => -0.0001) (fun _ => 1) := by
  constructor <;> rw [steady_state_iff] <;> norm_num

/-- Cochrane (2023), §6.4.3, p. 199: at 100% debt-to-GDP, `r - g = -1%` funds a steady primary
deficit of 1% of GDP (and no more). -/
theorem book_one_percent_deficit (ss : ℝ) :
    SolvesOn (-0.01) (fun _ => ss) (fun _ => 1) ↔ ss = -0.01 := by
  rw [steady_state_iff]
  norm_num

/-- Cochrane (2023), §6.4.2, p. 198: with zero primary surpluses the debt-to-GDP ratio is
`x_t = e^{(r-g) t} x₀`. -/
theorem zero_surplus_path (hx : SolvesOn a (fun _ => 0) x) {t : ℝ} (ht : 0 ≤ t) :
    x t = exp (a * t) * x 0 := by
  rw [solvesOn_eq continuous_const hx ht]
  unfold vocFrom
  simp

/-- Cochrane (2023), §6.4.2, p. 198: with zero surpluses and `r - g = -0.01%`, 150% debt-to-GDP
falls to exactly 50% after `T = -log(0.5/1.5)/0.0001 = log 3/0.0001` years, while with
`r - g = +0.01%` it rises to exactly 450% over the same span. -/
theorem book_growth_out_of_debt {x z : ℝ → ℝ} (hx : SolvesOn (-0.0001) (fun _ => 0) x)
    (hz : SolvesOn 0.0001 (fun _ => 0) z) (hx0 : x 0 = 1.5) (hz0 : z 0 = 1.5) :
    -log (0.5 / 1.5) / 0.0001 = log 3 / 0.0001 ∧
      x (log 3 / 0.0001) = 0.5 ∧ z (log 3 / 0.0001) = 4.5 := by
  have hT : (0 : ℝ) ≤ log 3 / 0.0001 := div_nonneg (log_nonneg (by norm_num)) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [show (0.5 : ℝ) / 1.5 = 3⁻¹ by norm_num, log_inv, neg_neg]
  · rw [zero_surplus_path hx hT, hx0, show -0.0001 * (log 3 / 0.0001) = -log 3 by ring,
      exp_neg, exp_log (by norm_num)]
    norm_num
  · rw [zero_surplus_path hz hT, hz0, show 0.0001 * (log 3 / 0.0001) = log 3 by ring,
      exp_log (by norm_num)]
    norm_num

/-- Cochrane (2023), §6.4.2, p. 198: `1.0986 < log 3 < 1.0987`. -/
theorem log_three_bounds : (1.0986 : ℝ) < log 3 ∧ log 3 < 1.0987 := by
  have he1 := Real.exp_one_lt_d9
  have he2 := Real.exp_one_gt_d9
  constructor
  · rw [lt_log_iff_exp_lt (by norm_num), show (1.0986 : ℝ) = 1 + 0.0986 by norm_num, exp_add]
    have hb := Real.exp_bound (x := 0.0986) (by norm_num [abs_of_pos]) (n := 4) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
    norm_num at hb
    have hu := (abs_le.1 hb).2
    have h0 := exp_pos (0.0986 : ℝ)
    nlinarith
  · rw [log_lt_iff_lt_exp (by norm_num), show (1.0987 : ℝ) = 1 + 0.0987 by norm_num, exp_add]
    have hb := Real.exp_bound (x := 0.0987) (by norm_num [abs_of_pos]) (n := 4) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
    norm_num at hb
    have hl := (abs_le.1 hb).1
    have h0 := exp_pos (1 : ℝ)
    nlinarith

/-- Cochrane (2023), §6.4.2, p. 198: the book's "11,000 years" is `log 3/0.0001`, strictly between
10,986 and 10,987 years. -/
theorem book_years_bounds : (10986 : ℝ) < log 3 / 0.0001 ∧ log 3 / 0.0001 < 10987 := by
  obtain ⟨h1, h2⟩ := log_three_bounds
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [div_lt_iff₀ (by norm_num)]
    linarith

/-- Cochrane (2023), §6.4.2, p. 198: the book's rounded computation
`150 × e^{0.0001 × 11000} = 150 e^{1.1}` lies between 450.6 and 450.7 ("450%"). -/
theorem book_450_bounds :
    (450.6 : ℝ) < 150 * exp (0.0001 * 11000) ∧ 150 * exp (0.0001 * 11000) < 450.7 := by
  rw [show (0.0001 : ℝ) * 11000 = 1 + 0.1 by norm_num, exp_add]
  have he1 := Real.exp_one_lt_d9
  have he2 := Real.exp_one_gt_d9
  have hb := Real.exp_bound (x := 0.1) (by norm_num [abs_of_pos]) (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num at hb
  have hl := (abs_le.1 hb).1
  have hu := (abs_le.1 hb).2
  have h0 := exp_pos (1 : ℝ)
  have h1 := exp_pos (0.1 : ℝ)
  constructor <;> nlinarith

/-- Cochrane (2023), §6.4.1, p. 196: with `r - g = -1%` and zero surpluses for 20 years, the
debt-to-GDP ratio falls to `e^{-0.2}` of its initial value. -/
theorem twenty_years_zero_surplus (hx : SolvesOn (-0.01) (fun _ => 0) x) :
    x 20 = exp (-0.2) * x 0 := by
  rw [zero_surplus_path hx (by norm_num)]
  norm_num

/-- Cochrane (2023), §6.4.1, p. 196 (survey E6.2, rounding): `e^{-0.2}` is between 81.87% and
81.88%, not the stated 80%. -/
theorem exp_neg_two_tenths_bounds :
    (0.8187 : ℝ) < exp (-0.2) ∧ exp (-0.2) < 0.8188 ∧ exp (-0.2 : ℝ) ≠ 0.8 := by
  have hb := Real.exp_bound (x := -0.2) (by norm_num [abs_of_neg]) (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num at hb
  have hl := (abs_le.1 hb).1
  have hu := (abs_le.1 hb).2
  refine ⟨by linarith, by linarith, fun h => by linarith⟩

end Cochrane.FiscalConstraints.RvsG
