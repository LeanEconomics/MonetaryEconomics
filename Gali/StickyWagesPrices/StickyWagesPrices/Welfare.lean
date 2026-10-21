/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.WageDispersion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The welfare loss function with sticky wages and prices

Galí (2015), Chapter 6, §6.3 (p. 179, eqs. (28)–(29)) and Appendix 6.1 (pp. 188–192): the
second-order approximation to the household's welfare around an efficient steady state, with
price **and** wage dispersion, the loss function `𝕎`, the average loss `L`, and the
comparative statics of the wage-inflation weight.

This module builds on `LaborAggregation` (CES indices, labour demand, `dispIntegral`, `d_w`,
`d_p`, the exact employment identity) and `WageDispersion` (cumulant expansions, `d_w`, `d_p`
to second order, the Calvo wage cross-section `wageMix` and the exact Lemma 2), and imports
them rather than restating them.

## Dispersion terms (pp. 189–190)

* `effWageDisp` `d_w^φ = ((1−α)/(1+φ)) log ∫ (W(j)/W)^{−ε_w(1+φ)}`: `d_w^φ = (Υ/2) var_j w + O(s³)`
  (`effWageDisp_second_order`), `Υ = ε_w(1−α)(1+ε_wφ)`; `effWageDisp_sub_wageDisp` is the book's
  `∫ n̂(j)² = n̂² + ε_w² var_j w` step (p. 189).
* With the book's power disutility the exact identity
  `∫ (N^d (W(j)/W)^{−ε_w})^{1+φ}/(1+φ) dj = (N^d e^{log Δ_w^φ/(1+φ)})^{1+φ}/(1+φ)`
  (`disutility_types_eq`) reduces the labour-type cross-section to **effective hours** `Ñ` with
  `(1 − α) log(Ñ/N) = y − a + d_p + d_w^φ` exactly (`effectiveHours_identity`).

## Two layers for (28)

* **(A) exact algebra.** `secondOrderUtility_eq`: given an efficient steady state and the
  exact identity `(1 − α) n = y − a + d`, the second-order polynomial in log deviations equals
  `−(K/2)[(σ + (φ+α)/(1−α))(y − ψ_ya a)² + (ε_p/Θ) var_p + Υ var_w] + t.i.p.` plus explicit
  higher-order terms; `secondOrderUtility_distorted` is the inefficient case (`Φ ŷ` term).
* **(B) the analytic bridge.** `period_utility_second_order`: for `C³` utility, along any
  one-parameter family of size `s`, period utility equals that quadratic form plus t.i.p.
  up to `O(s³)`. `period_utility_second_order_families` discharges every hypothesis for the
  actual model: price and wage cross-sections `p̄ + s ζ(i)`, `w̄ + s ξ(j)`, firm labour demand
  from (1) and (7), type-`j` employment from (3), the book's disutility, and output,
  technology and preference deviations `O(s)`.

## Lemma 2 and the loss

* Lemma 2 is `WageDispersion.lemma2` / `wage_lemma2_calvo` (the Calvo mixture is the same for
  prices with `θ_p`). **Survey error 8:** the book's equality holds only up to the
  policy-independent term `θ V_0/(1 − βθ)` (`lemma2_inherited`,
  `lemma2_printed_fails_with_inherited`, `welfare_eq_loss_inherited`).
* `welfare_eq_loss`, `welfare_eq_loss_calvo`: (28),
  `𝕎 = ½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ² + (ε_p/λ_p)(π^p)² + (ε_w(1−α)/λ_w)(π^w)²]`;
  `welfare_stationary`: (29).
* `wageWeight_strictMonoOn_eps`, `wageWeight_strictAnti_alpha`, `wageWeight_strictMonoOn_theta`:
  the wage-inflation weight `ε_w(1−α)/λ_w` is increasing in `ε_w`, in `1 − α` and in `θ_w`
  (all three claims of p. 179 hold); `lambdaW_strictAntiOn_theta`: `λ_w` is decreasing in
  `θ_w`.

The one-dimensional Taylor tools of layer (B) are restated from the Chapter 4 project.
-/

namespace Gali.StickyWagesPrices.Welfare

open MeasureTheory ProbabilityTheory Asymptotics Filter Topology
open Gali.StickyWagesPrices.LaborAggregation Gali.StickyWagesPrices.WageDispersion

variable {G : Type*} [MeasurableSpace G]

variable {μ : Measure G}

/-! ### Dispersion of wages, effective hours (pp. 189–190) -/

/-- Galí (2015), App. 6.1, p. 190: `Υ = ε_w(1 − α)(1 + ε_w φ)`. -/
noncomputable def upsilon (α φ εw : ℝ) : ℝ := εw * (1 - α) * (1 + εw * φ)

/-- Galí (2015), App. 6.1, pp. 189–190: the **effective** wage dispersion
`d_w^φ = ((1 − α)/(1 + φ)) log ∫ (W(j)/W)^{−ε_w(1+φ)}`, which collects `d_w` and the extra
disutility of unequal hours across types. -/
noncomputable def effWageDisp (ν : Measure G) (α φ εw : ℝ) (W : G → ℝ) : ℝ :=
  (1 - α) / (1 + φ) * Real.log (dispIntegral ν εw (-(εw * (1 + φ))) W)

/-- Galí (2015), App. 6.1, p. 190: along `X(i) = exp(x̄ + s z(i))`, relative values raised to
`e` are `(X(i)/X)^e = e^{−e K((1−ε)s)/(1−ε)} e^{e s z(i)}`. -/
theorem ratio_rpow_family [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) {ε : ℝ} (hε : ε ≠ 1) (e pbar s : ℝ) (i : G) :
    (Real.exp (pbar + s * z i) / cesIndex μ ε (fun i => Real.exp (pbar + s * z i))) ^ e
      = Real.exp (-(e * (cgf z μ ((1 - ε) * s) / (1 - ε)))) * Real.exp (e * s * z i) := by
  rw [cesIndex_family hz hB hε, ← Real.exp_sub, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- Galí (2015), App. 6.1, p. 190: along the family the dispersion integrand is integrable and
the dispersion integral `∫ (X(i)/X)^e` is positive. -/
theorem dispIntegral_family_pos [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) {ε : ℝ} (hε : ε ≠ 1) (e pbar s : ℝ) :
    Integrable (fun i => (Real.exp (pbar + s * z i) /
        cesIndex μ ε (fun i => Real.exp (pbar + s * z i))) ^ e) μ ∧
      0 < dispIntegral μ ε e (fun i => Real.exp (pbar + s * z i)) := by
  have hrel := ratio_rpow_family (μ := μ) hz hB hε e pbar s
  refine ⟨?_, ?_⟩
  · simp_rw [hrel]
    exact (integrable_exp_mul hz hB (e * s)).const_mul _
  · rw [dispIntegral]
    simp_rw [hrel]
    rw [integral_const_mul]
    exact mul_pos (Real.exp_pos _) (mgf_pos (integrable_exp_mul hz hB (e * s)))

/-- Galí (2015), App. 6.1, pp. 189–190: the effective wage dispersion satisfies
`d_w^φ = (Υ/2) var_j w + O(s³)`, `Υ = ε_w(1 − α)(1 + ε_w φ)`. -/
theorem effWageDisp_second_order [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) {α φ εw : ℝ} (hφ : 0 ≤ φ) (hεw : 1 < εw) (wbar : ℝ) :
    (fun s => effWageDisp μ α φ εw (fun i => Real.exp (wbar + s * z i)) -
        upsilon α φ εw / 2 * crossVar μ (fun i => wbar + s * z i))
      =O[𝓝 0] fun s => s ^ 3 := by
  have h1 : (1 : ℝ) + φ ≠ 0 := by linarith
  have h := (log_dispIntegral_second_order (μ := μ) hz hB (ε := εw) (by linarith)
    (-(εw * (1 + φ))) wbar).const_mul_left ((1 - α) / (1 + φ))
  refine h.congr_left fun s => ?_
  rw [effWageDisp, upsilon]
  field_simp
  ring

/-- Galí (2015), App. 6.1, p. 189 (**the `∫ n̂(j)² = n̂² + ε_w² var_j w` step**): the effective
wage dispersion exceeds `d_w` by `((1 − α) ε_w² φ/2) var_j w + O(s³)`, the extra disutility of
hours that differ across labour types. -/
theorem effWageDisp_sub_wageDisp [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) {α φ εw : ℝ} (hφ : 0 ≤ φ) (hεw : 1 < εw) (wbar : ℝ) :
    (fun s => effWageDisp μ α φ εw (fun i => Real.exp (wbar + s * z i)) -
        dW μ α εw (fun i => Real.exp (wbar + s * z i)) -
        (1 - α) * εw ^ 2 * φ / 2 * crossVar μ (fun i => wbar + s * z i))
      =O[𝓝 0] fun s => s ^ 3 := by
  refine ((effWageDisp_second_order (μ := μ) (α := α) hz hB hφ hεw wbar).sub
    (dW_second_order (μ := μ) hz hB (ε := εw) (by linarith) α wbar)).congr_left fun s => ?_
  rw [upsilon]
  ring

/-! ### Exact employment and disutility identities (pp. 189–190) -/

/-- Galí (2015), pp. 189–190 (exact, pointwise): firm labour demand `N(i) = (Y(i)/A)^{1/(1−α)}`
with `Y(i) = (P(i)/P)^{−ε_p} Y` is `(Y/A)^{1/(1−α)} (P(i)/P)^{−ε_p/(1−α)}` (the integrated form
is `LaborAggregation.firm_index_level`). -/
theorem firmLabour_eq {α εp Y A x : ℝ} (hY : 0 ≤ Y) (hA : 0 < A) (hx : 0 ≤ x) :
    (Y * x ^ (-εp) / A) ^ (1 - α)⁻¹ = (Y / A) ^ (1 - α)⁻¹ * x ^ (-εp / (1 - α)) := by
  rw [mul_div_right_comm, Real.mul_rpow (div_nonneg hY hA.le) (Real.rpow_nonneg hx _),
    ← Real.rpow_mul hx]
  rfl

/-- Galí (2015), pp. 189–190 (**exact disutility identity**): with type employment
`𝒩(j) = (W(j)/W)^{−ε_w} N^d` and the book's disutility, if `Δ_w^φ = ∫ (W(j)/W)^{−ε_w(1+φ)}`
is positive, then `∫ 𝒩(j)^{1+φ}/(1+φ) dj = (N^d e^{log Δ_w^φ/(1+φ)})^{1+φ}/(1+φ)`: the
cross-section of hours acts exactly like **effective hours** `N^d (Δ_w^φ)^{1/(1+φ)}`. -/
theorem disutility_types_eq {φ εw Nd : ℝ} (hφ : 0 ≤ φ) (hNd : 0 ≤ Nd)
    {W : G → ℝ} (hW : ∀ j, 0 < W j) (hWbar : 0 < cesIndex μ εw W)
    (hpos : 0 < dispIntegral μ εw (-(εw * (1 + φ))) W) :
    ∫ j, ((W j / cesIndex μ εw W) ^ (-εw) * Nd) ^ (1 + φ) / (1 + φ) ∂μ
      = (Nd * Real.exp (Real.log (dispIntegral μ εw (-(εw * (1 + φ))) W) / (1 + φ))) ^ (1 + φ)
        / (1 + φ) := by
  have h1 : (1 : ℝ) + φ ≠ 0 := by linarith
  have hx : ∀ j, 0 ≤ W j / cesIndex μ εw W := fun j => (div_pos (hW j) hWbar).le
  have hpt : ∀ j, ((W j / cesIndex μ εw W) ^ (-εw) * Nd) ^ (1 + φ) / (1 + φ)
      = Nd ^ (1 + φ) / (1 + φ) * (W j / cesIndex μ εw W) ^ (-(εw * (1 + φ))) := fun j => by
    rw [Real.mul_rpow (Real.rpow_nonneg (hx j) _) hNd, ← Real.rpow_mul (hx j)]
    rw [show -εw * (1 + φ) = -(εw * (1 + φ)) by ring]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, Real.mul_rpow hNd (Real.exp_pos _).le, ← Real.exp_mul,
    div_mul_cancel₀ _ h1, Real.exp_log hpos, dispIntegral]
  ring

/-- Galí (2015), p. 190 (**exact employment identity in logs**): with steady state
`C = A N^{1−α}` (`N > 0`), output `Y = C e^{y}`, technology `A_t = A e^{a}`, aggregate firm
labour `N^d = (Y/A_t)^{1/(1−α)} Δ_p` with `Δ_p = e^{d_p/(1−α)}`, effective hours
`Ñ = N^d e^{log Δ_w^φ/(1+φ)}` with `log Δ_w^φ = (1+φ) d_w^φ/(1−α)`, one has `Ñ = N e^{n}` with
`(1 − α) n = y − a + d_p + d_w^φ`. -/
theorem effectiveHours_identity {α A N y a dp dw : ℝ} (hα1 : α < 1) (hA : 0 < A) (hN : 0 < N) :
    (A * N ^ (1 - α) * Real.exp y / (A * Real.exp a)) ^ (1 - α)⁻¹ *
        Real.exp (dp / (1 - α)) * Real.exp (dw / (1 - α))
      = N * Real.exp ((y - a + dp + dw) / (1 - α)) := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have hY : A * N ^ (1 - α) * Real.exp y / (A * Real.exp a)
      = N ^ (1 - α) * Real.exp (y - a) := by
    rw [Real.exp_sub]
    field_simp
  rw [hY, Real.mul_rpow (Real.rpow_nonneg hN.le _) (Real.exp_pos _).le,
    Real.rpow_rpow_inv hN.le h1, ← Real.exp_mul, mul_assoc, mul_assoc, ← Real.exp_add,
    ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- A process that is `O(s)` tends to `0` (Galí 2015, App. 6.1). Restated from the Chapter 4
project. -/
theorem tendsto_zero_of_bigO {f : ℝ → ℝ} (hf : f =O[𝓝 0] fun s => s ^ 1) :
    Tendsto f (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => s ^ 1) (𝓝 0) (𝓝 0) := by
    simp only [pow_one]
    exact tendsto_id
  exact hf.trans_tendsto h

/-! ### One-dimensional Taylor expansions (restated from the Chapter 4 project) -/

/-- Galí (2015), App. 6.1, p. 188 (**second-order Taylor expansion with a cubic remainder**).
Restated from the Chapter 4 project. -/
theorem taylor_two {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContDiffAt ℝ 3 f x₀) :
    (fun x => f x - f x₀ - deriv f x₀ * (x - x₀) - iteratedDeriv 2 f x₀ / 2 * (x - x₀) ^ 2)
      =O[𝓝 x₀] fun x => (x - x₀) ^ 3 := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hs : ContDiffOn ℝ 3 f (Metric.ball x₀ r) := hfU.mono hball
  have hT := taylor_isLittleO (convex_ball x₀ r) (Metric.mem_ball_self hr) hs
  rw [nhdsWithin_eq_nhds.2 (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] at hT
  have hx0 := Metric.mem_ball_self hr (x := x₀)
  have e1 := iteratedDerivWithin_of_isOpen (n := 1) (f := f) Metric.isOpen_ball hx0
  have e2 := iteratedDerivWithin_of_isOpen (n := 2) (f := f) Metric.isOpen_ball hx0
  have e3 := iteratedDerivWithin_of_isOpen (n := 3) (f := f) Metric.isOpen_ball hx0
  have heq : (fun x => f x - f x₀ - deriv f x₀ * (x - x₀) -
      iteratedDeriv 2 f x₀ / 2 * (x - x₀) ^ 2)
      = fun x => (f x - taylorWithinEval f 3 (Metric.ball x₀ r) x₀ x) +
        iteratedDeriv 3 f x₀ / 6 * (x - x₀) ^ 3 := by
    funext x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_zero, e1, e2,
      e3, iteratedDeriv_one, smul_eq_mul]
    norm_num [Nat.factorial]
    ring
  rw [heq]
  exact hT.isBigO.add ((isBigO_refl _ _).const_mul_left _)

/-- Galí (2015), App. 6.1, p. 188: `e^x = 1 + x + x²/2 + O(x³)`. Restated from the Chapter 4
project. -/
theorem exp_taylor_two :
    (fun x => Real.exp x - 1 - x - x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 3 := by
  have h := taylor_two (f := Real.exp) (x₀ := 0) Real.contDiff_exp.contDiffAt
  have h2 : iteratedDeriv 2 Real.exp 0 = 1 := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.exp_zero]
  simp only [Real.deriv_exp, Real.exp_zero, h2, sub_zero] at h
  convert h using 2 with x
  ring

/-- Galí (2015), App. 6.1, p. 188: `e^x − 1 = O(x)`. Restated from the Chapter 4 project. -/
theorem exp_sub_one_bigO : (fun x => Real.exp x - 1) =O[𝓝 0] fun x => x ^ 1 := by
  have h3 := bigO_weaken (by norm_num : 1 ≤ 3) exp_taylor_two
  have h1 : (fun x : ℝ => x) =O[𝓝 0] fun x => x ^ 1 := by simpa using isBigO_refl _ _
  have h2 : (fun x : ℝ => x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 1 :=
    bigO_weaken (by norm_num : 1 ≤ 2) ((isBigO_refl _ _).const_mul_left (1 / 2) |>.congr_left
      (fun x => by ring))
  have := (h3.add h1).add h2
  refine this.congr_left fun x => ?_
  ring

/-- Galí (2015), App. 6.1, p. 188 (**second-order expansion in log deviations**):
`f(X e^{x}) − f(X) = f'(X) X (x + x²/2) + f''(X) X² x²/2 + O(x³)`. Restated from the
Chapter 4 project. -/
theorem logdev_taylor {f : ℝ → ℝ} {X : ℝ} (hf : ContDiffAt ℝ 3 f X) :
    (fun x => f (X * Real.exp x) - f X - deriv f X * X * (x + x ^ 2 / 2) -
        iteratedDeriv 2 f X / 2 * X ^ 2 * x ^ 2) =O[𝓝 0] fun x => x ^ 3 := by
  have hT := taylor_two hf
  have hg : Tendsto (fun x => X * Real.exp x) (𝓝 0) (𝓝 X) := by
    have := ((Real.continuous_exp.tendsto 0).const_mul X)
    simpa using this
  have hE1 := exp_sub_one_bigO
  have h1 : (fun x => f (X * Real.exp x) - f X - deriv f X * (X * Real.exp x - X) -
      iteratedDeriv 2 f X / 2 * (X * Real.exp x - X) ^ 2) =O[𝓝 0] fun x => x ^ 3 := by
    refine (hT.comp_tendsto hg).trans ?_
    have hc : (fun x => (X * Real.exp x - X) ^ 3) =O[𝓝 0] fun x => x ^ 3 := by
      have : (fun x => (X * Real.exp x - X) ^ 3) = fun x => X ^ 3 * (Real.exp x - 1) ^ 3 := by
        funext x
        ring
      rw [this]
      have := hE1.pow 3
      simp only [← pow_mul] at this
      exact this.const_mul_left _
    exact hc
  have h2 : (fun x => deriv f X * X * (Real.exp x - 1 - x - x ^ 2 / 2)) =O[𝓝 0]
      fun x => x ^ 3 := exp_taylor_two.const_mul_left _
  have hA : (fun x => Real.exp x - 1 - x) =O[𝓝 0] fun x => x ^ 2 := by
    have : (fun x : ℝ => x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 2 :=
      (isBigO_refl _ _).const_mul_left (1 / 2) |>.congr_left (fun x => by ring)
    refine ((bigO_weaken (by norm_num : 2 ≤ 3) exp_taylor_two).add this).congr_left
      fun x => ?_
    ring
  have hB : (fun x => Real.exp x - 1 + x) =O[𝓝 0] fun x => x ^ 1 :=
    hE1.add (by simpa using isBigO_refl (fun x : ℝ => x) (𝓝 0))
  have h3 : (fun x => iteratedDeriv 2 f X / 2 * X ^ 2 *
      ((Real.exp x - 1 - x) * (Real.exp x - 1 + x))) =O[𝓝 0] fun x => x ^ 3 :=
    (bigO_mul hA hB).const_mul_left _
  refine ((h1.add h2).add h3).congr_left fun x => ?_
  ring

/-! ### Layer (A): the exact algebra of App. 6.1 -/

/-- Galí (2015), eq. (28), p. 179: the output-gap coefficient `σ + (φ + α)/(1 − α)`. -/
noncomputable def gapCoeff (σ φ α : ℝ) : ℝ := σ + (φ + α) / (1 - α)

/-- Galí (2015), p. 191: `ψ_ya = (1 + φ)/(σ(1 − α) + φ + α)`, so that `ŷ^e_t = ψ_ya a_t`. -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- Galí (2015), App. 6.1, p. 188 (the second-order polynomial in log deviations): with
`Ū = U(C, N)`, `K = U_c C`, `U_n N`, log deviations `y` (output = consumption), `n` (hours)
and `z` (`Z = e^z`). Restated from the Chapter 4 project. -/
noncomputable def secondOrderUtility (Ubar K UnN σ φ y n z : ℝ) : ℝ :=
  Ubar * (z + z ^ 2 / 2) + K * (y + (1 - σ) / 2 * y ^ 2) + UnN * (n + (1 + φ) / 2 * n ^ 2) +
    K * y * z + UnN * n * z

/-- Galí (2015), App. 6.1, p. 191: the terms independent of policy, an explicit function of the
shocks `a`, `z` only. Restated from the Chapter 4 project. -/
noncomputable def tip (Ubar K σ φ α a z : ℝ) : ℝ :=
  Ubar * (z + z ^ 2 / 2) +
    K * (a + a * z + (gapCoeff σ φ α * psiYA σ φ α ^ 2 - (1 + φ) / (1 - α)) / 2 * a ^ 2)

/-- Galí (2015), App. 6.1, p. 191, last display (with `Φ = 0`): the policy-relevant quadratic
form `−(K/2)[(σ + (φ+α)/(1−α))(y − ŷ^e)² + (ε_p/Θ) var_i p + Υ var_j w]`, `ŷ^e = ψ_ya a`. -/
noncomputable def welfareQuadratic (K σ φ α εp εw y a vp vw : ℝ) : ℝ :=
  -K / 2 * (gapCoeff σ φ α * (y - psiYA σ φ α * a) ^ 2 + εp / bigTheta α εp * vp +
    upsilon α φ εw * vw)

/-- Galí (2015), p. 191: `(σ + (φ+α)/(1−α)) ψ_ya = (1 + φ)/(1 − α)`. -/
theorem gapCoeff_mul_psiYA {σ φ α : ℝ} (hα : α ≠ 1) (hden : σ * (1 - α) + φ + α ≠ 0) :
    gapCoeff σ φ α * psiYA σ φ α = (1 + φ) / (1 - α) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold gapCoeff psiYA
  field_simp
  ring

/-- Galí (2015), p. 191, the completing-the-square coefficient:
`−(1 − σ) + (1 + φ)/(1 − α) = σ + (φ + α)/(1 − α)`. -/
theorem gapCoeff_eq {σ φ α : ℝ} (hα : α ≠ 1) :
    -(1 - σ) + (1 + φ) / (1 - α) = gapCoeff σ φ α := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold gapCoeff
  field_simp
  ring

/-- Galí (2015), p. 190: the bookkeeping `ε_w/2 + ε_w² φ/2 = Υ/(2(1 − α))`: `d_w` plus the
`∫ n̂(j)²` term (times `(1 − α)`) give `Υ/2`. -/
theorem upsilon_split {α φ εw : ℝ} :
    (1 - α) * εw / 2 + (1 - α) * εw ^ 2 * φ / 2 = upsilon α φ εw / 2 := by
  unfold upsilon
  ring

/-- Galí (2015), App. 6.1, pp. 188–191 (**completing the square, exact**). Suppose the steady
state is efficient, `U_n N = −(1 − α) U_c C`, and hours satisfy `(1 − α) n = y − a + d`. Then
for every `v_p`, `v_w` the second-order polynomial equals
`−(K/2)[Γ(y − ψ_ya a)² + (ε_p/Θ) v_p + Υ v_w] + t.i.p. + K((ε_p/2Θ) v_p + (Υ/2) v_w − d)`
`− K((1+φ)/(2(1−α))(2(y−a)d + d²) + d z)`; the last two terms are of third order once
`d − (ε_p/2Θ) v_p − (Υ/2) v_w = O(s³)` and `d = O(s²)`. -/
theorem secondOrderUtility_eq {Ubar K UnN σ φ α εp εw y n z a d vp vw : ℝ} (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0) (hUn : UnN = -(1 - α) * K)
    (hn : (1 - α) * n = y - a + d) :
    secondOrderUtility Ubar K UnN σ φ y n z
      = welfareQuadratic K σ φ α εp εw y a vp vw + tip Ubar K σ φ α a z +
        K * (εp / (2 * bigTheta α εp) * vp + upsilon α φ εw / 2 * vw - d) -
        K * ((1 + φ) / (2 * (1 - α)) * (2 * (y - a) * d + d ^ 2) + d * z) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hn' : n = (y - a + d) / (1 - α) := by
    field_simp
    linarith
  have hgp := gapCoeff_mul_psiYA (σ := σ) (φ := φ) hα hden
  have hgp2 : gapCoeff σ φ α * psiYA σ φ α ^ 2 = (1 + φ) / (1 - α) * psiYA σ φ α := by
    rw [← hgp]
    ring
  have hg : gapCoeff σ φ α = σ + (φ + α) / (1 - α) := rfl
  subst hUn hn'
  unfold secondOrderUtility welfareQuadratic tip
  rw [hgp2]
  have hexp : gapCoeff σ φ α * (y - psiYA σ φ α * a) ^ 2
      = gapCoeff σ φ α * y ^ 2 - 2 * (gapCoeff σ φ α * psiYA σ φ α) * a * y +
        (1 + φ) / (1 - α) * psiYA σ φ α * a ^ 2 := by
    rw [← hgp2]
    ring
  rw [hexp, hgp, hg]
  field_simp
  ring

/-- Galí (2015), App. 6.1, pp. 190–191 (**an inefficient steady state**): if
`U_n N = −(1 − Φ)(1 − α) U_c C` (steady-state distortion `Φ`) and `(1 − α) n = y − a + d`,
the polynomial equals its value at the efficient coefficient plus
`Φ K (y − a + d) + Φ (1 − α) K ((1+φ)/2 n² + n z)`: the book's `Φ ŷ` term (`−Φ K a` is
t.i.p.) plus `Φ` times second-order terms, dropped by the "small distortion" assumption. -/
theorem secondOrderUtility_distorted {Ubar K UnN σ φ α Φ y n z a d : ℝ}
    (hUn : UnN = -(1 - Φ) * (1 - α) * K) (hn : (1 - α) * n = y - a + d) :
    secondOrderUtility Ubar K UnN σ φ y n z
      = secondOrderUtility Ubar K (-(1 - α) * K) σ φ y n z + Φ * K * (y - a + d) +
        Φ * (1 - α) * K * ((1 + φ) / 2 * n ^ 2 + n * z) := by
  subst hUn
  unfold secondOrderUtility
  linear_combination (Φ * K) * hn

/-! ### Layer (B): the analytic bridge -/

/-- Galí (2015), App. 6.1, pp. 188–191 (**second-order approximation of period utility,
rigorous form**). Period utility is `(u(C) + w(N)) Z` with `u`, `w` of class `C³` near the
steady state, `σ = −U_cc C/U_c`, `φ = U_nn N/U_n`, efficient steady state
`U_n N = −(1 − α) U_c C`. Along a one-parameter family of size `s` with `y, a, z = O(s)`,
variances `v_p, v_w = O(s²)`, the exact identity `(1 − α) n = y − a + d` and the dispersion
relation `d − (ε_p/2Θ) v_p − (Υ/2) v_w = O(s³)`:
`U_t − U = −(U_c C/2)[Γ(y − ψ_ya a)² + (ε_p/Θ) v_p + Υ v_w] + t.i.p.(a, z) + O(s³)`. -/
theorem period_utility_second_order {u w : ℝ → ℝ} {C N σ φ α εp εw : ℝ}
    {y n a z d vp vw : ℝ → ℝ}
    (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hφ : iteratedDeriv 2 w N * N = φ * deriv w N)
    (hEff : deriv w N * N = -(1 - α) * (deriv u C * C)) (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) (hvp : vp =O[𝓝 0] fun s => s ^ 2)
    (hvw : vw =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - εp / (2 * bigTheta α εp) * vp s - upsilon α φ εw / 2 * vw s)
      =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, (1 - α) * n s = y s - a s + d s) :
    (fun s => (u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) - (u C + w N)
        - (welfareQuadratic (deriv u C * C) σ φ α εp εw (y s) (a s) (vp s) (vw s) +
          tip (u C + w N) (deriv u C * C) σ φ α (a s) (z s)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  set K := deriv u C * C with hK
  set UnN := deriv w N * N with hUnN
  set Ubar := u C + w N with hUbar
  set cp := εp / (2 * bigTheta α εp) with hcp
  set cw := upsilon α φ εw / 2 with hcw
  have hd2 : d =O[𝓝 0] fun s => s ^ 2 :=
    (((bigO_weaken (by norm_num : 2 ≤ 3) hd).add (hvp.const_mul_left cp)).add
      (hvw.const_mul_left cw)).congr_left fun s => by ring
  have hd1 : d =O[𝓝 0] fun s => s ^ 1 := bigO_weaken (by norm_num) hd2
  have hn1 : n =O[𝓝 0] fun s => s ^ 1 :=
    (((hy.sub ha).add hd1).const_mul_left (1 - α)⁻¹).congr_left fun s => by
      rw [← hn s]
      field_simp
  have cube : ∀ {f : ℝ → ℝ}, f =O[𝓝 0] (fun s => s ^ 1) →
      (fun s => f s ^ 3) =O[𝓝 0] fun s => s ^ 3 := fun {f} hf => by
    have := hf.pow 3
    simpa [← pow_mul] using this
  have hRu : (fun s => u (C * Real.exp (y s)) - u C - K * (y s + (1 - σ) / 2 * y s ^ 2))
      =O[𝓝 0] fun s => s ^ 3 := by
    have h := ((logdev_taylor hu).comp_tendsto (tendsto_zero_of_bigO hy)).trans (cube hy)
    refine h.congr_left fun s => ?_
    simp only [Function.comp_apply]
    linear_combination (-(C / 2 * y s ^ 2)) * hσ
  have hRw : (fun s => w (N * Real.exp (n s)) - w N - UnN * (n s + (1 + φ) / 2 * n s ^ 2))
      =O[𝓝 0] fun s => s ^ 3 := by
    have h := ((logdev_taylor hw).comp_tendsto (tendsto_zero_of_bigO hn1)).trans (cube hn1)
    refine h.congr_left fun s => ?_
    simp only [Function.comp_apply]
    linear_combination (-(N / 2 * n s ^ 2)) * hφ
  have hRe : (fun s => Real.exp (z s) - 1 - z s - z s ^ 2 / 2) =O[𝓝 0] fun s => s ^ 3 :=
    (exp_taylor_two.comp_tendsto (tendsto_zero_of_bigO hz)).trans (cube hz)
  have hez : (fun s => Real.exp (z s)) =O[𝓝 0] fun s => s ^ 0 := by
    have ht : Tendsto (fun s => Real.exp (z s)) (𝓝 0) (𝓝 1) := by
      have := (Real.continuous_exp.tendsto 0).comp (tendsto_zero_of_bigO hz)
      rw [Real.exp_zero] at this
      exact this
    simpa using ht.isBigO_one ℝ
  have hsq : ∀ {f : ℝ → ℝ}, f =O[𝓝 0] (fun s => s ^ 1) →
      (fun s => f s ^ 2) =O[𝓝 0] fun s => s ^ 2 := fun {f} hf => by
    have := hf.pow 2
    simpa [← pow_mul] using this
  have hpoly : ∀ {f : ℝ → ℝ} (k₁ k₂ : ℝ), f =O[𝓝 0] (fun s => s ^ 1) →
      (fun s => k₁ * f s + k₂ * f s ^ 2) =O[𝓝 0] fun s => s ^ 1 := fun {f} k₁ k₂ hf =>
    (hf.const_mul_left k₁).add (bigO_weaken (by norm_num) ((hsq hf).const_mul_left k₂))
  have hA : ∀ s, secondOrderUtility Ubar K UnN σ φ (y s) (n s) (z s)
      = welfareQuadratic K σ φ α εp εw (y s) (a s) (vp s) (vw s) + tip Ubar K σ φ α (a s) (z s) +
        K * (cp * vp s + cw * vw s - d s) -
        K * ((1 + φ) / (2 * (1 - α)) * (2 * (y s - a s) * d s + d s ^ 2) + d s * z s) :=
    fun s => secondOrderUtility_eq hα hden hEff (hn s)
  have T1 := hRe.const_mul_left Ubar
  have T2 : (fun s => (K * (1 - σ) / 2 * y s ^ 2 + UnN * (1 + φ) / 2 * n s ^ 2) *
      (z s + z s ^ 2 / 2)) =O[𝓝 0] fun s => s ^ (2 + 1) :=
    bigO_mul (((hsq hy).const_mul_left _).add ((hsq hn1).const_mul_left _))
      ((hpoly 1 (1 / 2) hz).congr_left fun s => by ring)
  have T3 : (fun s => (K * y s + UnN * n s) * (z s ^ 2 / 2)) =O[𝓝 0] fun s => s ^ (1 + 2) :=
    bigO_mul ((hy.const_mul_left _).add (hn1.const_mul_left _))
      (((hsq hz).const_mul_left (1 / 2)).congr_left fun s => by ring)
  have T4 : (fun s => (K * (y s + (1 - σ) / 2 * y s ^ 2) + UnN * (n s + (1 + φ) / 2 * n s ^ 2)) *
      (Real.exp (z s) - 1 - z s - z s ^ 2 / 2)) =O[𝓝 0] fun s => s ^ 3 :=
    bigO_weaken (by norm_num : 3 ≤ 1 + 3) (bigO_mul
      ((((hpoly 1 ((1 - σ) / 2) hy).const_mul_left K).add
        ((hpoly 1 ((1 + φ) / 2) hn1).const_mul_left UnN)).congr_left fun s => by ring) hRe)
  have T5 : (fun s => ((u (C * Real.exp (y s)) - u C - K * (y s + (1 - σ) / 2 * y s ^ 2)) +
      (w (N * Real.exp (n s)) - w N - UnN * (n s + (1 + φ) / 2 * n s ^ 2))) *
      Real.exp (z s)) =O[𝓝 0] fun s => s ^ (3 + 0) := bigO_mul (hRu.add hRw) hez
  have T6 : (fun s => K * (cp * vp s + cw * vw s - d s)) =O[𝓝 0] fun s => s ^ 3 :=
    (hd.neg_left.const_mul_left K).congr_left fun s => by ring
  have T7 : (fun s => K * ((1 + φ) / (2 * (1 - α)) * (2 * (y s - a s) * d s + d s ^ 2) +
      d s * z s)) =O[𝓝 0] fun s => s ^ 3 := by
    have e1 : (fun s => 2 * (y s - a s) * d s) =O[𝓝 0] fun s => s ^ (1 + 2) :=
      (bigO_mul ((hy.sub ha).const_mul_left 2) hd2).congr_left fun s => by ring
    have e2 : (fun s => d s ^ 2) =O[𝓝 0] fun s => s ^ 3 :=
      bigO_weaken (by norm_num : 3 ≤ 2 + 2) ((bigO_mul hd2 hd2).congr_left fun s => by ring)
    have e3 : (fun s => d s * z s) =O[𝓝 0] fun s => s ^ (2 + 1) := bigO_mul hd2 hz
    exact ((((e1.add e2).const_mul_left ((1 + φ) / (2 * (1 - α)))).add e3).const_mul_left K)
  refine (((((((T1.add T2).add T3).add T4).add T5).add T6).sub T7)).congr_left fun s => ?_
  have hs := hA s
  unfold secondOrderUtility at hs
  linear_combination (-1 : ℝ) * hs

/-- Galí (2015), pp. 167 and 188: the book's disutility of hours, as a function of (effective)
hours, `w(N) = −N^{1+φ}/(1+φ)`, has derivative `−N^φ` everywhere (`φ ≥ 0`). -/
theorem deriv_negDisutil {φ : ℝ} (hφ : 0 ≤ φ) :
    deriv (fun x : ℝ => -(x ^ (1 + φ) / (1 + φ))) = fun x => -x ^ φ := by
  funext x
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  have h : HasDerivAt (fun x : ℝ => -(x ^ (1 + φ) / (1 + φ)))
      (-((1 + φ) * x ^ (1 + φ - 1) / (1 + φ))) x :=
    ((Real.hasDerivAt_rpow_const (x := x) (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).neg
  rw [h.deriv, show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), p. 189: for the book's disutility, `φ = U_nn N/U_n` at every `N > 0`:
`w''(N) N = φ w'(N)`. -/
theorem negDisutil_phi {φ N : ℝ} (hφ : 0 ≤ φ) (hN : 0 < N) :
    iteratedDeriv 2 (fun x : ℝ => -(x ^ (1 + φ) / (1 + φ))) N * N
      = φ * deriv (fun x : ℝ => -(x ^ (1 + φ) / (1 + φ))) N := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_negDisutil hφ]
  have h : HasDerivAt (fun x : ℝ => -x ^ φ) (-(φ * N ^ (φ - 1))) N :=
    (Real.hasDerivAt_rpow_const (x := N) (p := φ) (Or.inl hN.ne')).neg
  rw [h.deriv]
  have : N ^ (φ - 1) * N = N ^ φ := by
    rw [Real.rpow_sub_one hN.ne']
    field_simp
  linear_combination (-φ) * this

/-- Galí (2015), p. 188: the book's disutility is `C³` at every `N > 0`. -/
theorem negDisutil_contDiffAt {φ N : ℝ} (hN : 0 < N) :
    ContDiffAt ℝ 3 (fun x : ℝ => -(x ^ (1 + φ) / (1 + φ))) N :=
  ((Real.contDiffAt_rpow_const_of_ne (p := 1 + φ) hN.ne').div_const _).neg

/-- Galí (2015), App. 6.1, pp. 188–191 (**the second-order approximation for the actual
model**). Goods on a probability space `(G, μ)`, labour types on `(J, ν)`. Steady state
`N > 0`, `A > 0`, `C = A N^{1−α}`; `u` is `C³` at `C` with `σ = −u''C/u'`; the book's
disutility; efficient steady state `N^φ N = (1 − α) u'(C) C` (i.e. `MRS = MPN`). Families of
size `s`: prices `P(i) = e^{p̄ + s ζ(i)}`, wages `W(j) = e^{w̄ + s ξ(j)}` (`ζ, ξ` bounded and
measurable), output `Y = C e^{y}`, technology `A e^{a}`, preference shifter `e^{z}`
(`y, a, z = O(s)`). Firm labour is `N(i) = (Y(i)/A_t)^{1/(1−α)}` with `Y(i) = (P(i)/P)^{−ε_p} Y`
(eqs. (1), (7)), aggregate firm labour `N^d = ∫ N(i)`, and type employment
`𝒩(j) = (W(j)/W)^{−ε_w} N^d` (eq. (3)). Then period utility
`(u(Y) − ∫ 𝒩(j)^{1+φ}/(1+φ) dj) e^{z}` minus its steady-state value equals
`−(u'(C)C/2)[Γ(y − ψ_ya a)² + (ε_p/Θ) var_i p + Υ var_j w] + t.i.p.(a, z)` up to `O(s³)`. -/
theorem period_utility_second_order_families {J : Type*} [MeasurableSpace J] {ν : Measure J}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {u : ℝ → ℝ}
    {N A σ φ α εp εw pbar wbar Bp Bw : ℝ} {ζ : G → ℝ} {ξ : J → ℝ} {y a z : ℝ → ℝ}
    (hζ : Measurable ζ) (hBp : ∀ i, |ζ i| ≤ Bp) (hξ : Measurable ξ) (hBw : ∀ j, |ξ j| ≤ Bw)
    (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hσ0 : 0 < σ) (hφ0 : 0 ≤ φ)
    (hN : 0 < N) (hA : 0 < A) (hu : ContDiffAt ℝ 3 u (A * N ^ (1 - α)))
    (hσ : iteratedDeriv 2 u (A * N ^ (1 - α)) * (A * N ^ (1 - α))
      = -σ * deriv u (A * N ^ (1 - α)))
    (hEff : N ^ φ * N = (1 - α) * (deriv u (A * N ^ (1 - α)) * (A * N ^ (1 - α))))
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) :
    (fun s => (u (A * N ^ (1 - α) * Real.exp (y s)) -
          ∫ j, ((Real.exp (wbar + s * ξ j) / cesIndex ν εw (fun j => Real.exp (wbar + s * ξ j)))
              ^ (-εw) *
            ∫ i, ((A * N ^ (1 - α) * Real.exp (y s)) *
              (Real.exp (pbar + s * ζ i) / cesIndex μ εp (fun i => Real.exp (pbar + s * ζ i)))
                ^ (-εp) / (A * Real.exp (a s))) ^ (1 - α)⁻¹ ∂μ) ^ (1 + φ) / (1 + φ) ∂ν) *
          Real.exp (z s) -
        (u (A * N ^ (1 - α)) - N ^ (1 + φ) / (1 + φ)) -
        (welfareQuadratic (deriv u (A * N ^ (1 - α)) * (A * N ^ (1 - α))) σ φ α εp εw (y s) (a s)
            (crossVar μ (fun i => pbar + s * ζ i)) (crossVar ν (fun j => wbar + s * ξ j)) +
          tip (u (A * N ^ (1 - α)) - N ^ (1 + φ) / (1 + φ))
            (deriv u (A * N ^ (1 - α)) * (A * N ^ (1 - α))) σ φ α (a s) (z s)))
      =O[𝓝 0] fun s => s ^ 3 := by
  set C := A * N ^ (1 - α) with hCdef
  set w : ℝ → ℝ := fun x => -(x ^ (1 + φ) / (1 + φ)) with hwdef
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have h1φ : (1 : ℝ) + φ ≠ 0 := by linarith
  have hden : σ * (1 - α) + φ + α ≠ 0 := by
    have : 0 < σ * (1 - α) := mul_pos hσ0 (by linarith)
    linarith
  set dp : ℝ → ℝ := fun s => dP μ α εp (fun i => Real.exp (pbar + s * ζ i)) with hdp
  set dw : ℝ → ℝ := fun s => effWageDisp ν α φ εw (fun j => Real.exp (wbar + s * ξ j))
    with hdw
  set n : ℝ → ℝ := fun s => (y s - a s + dp s + dw s) / (1 - α) with hndef
  have hn : ∀ s, (1 - α) * n s = y s - a s + (dp s + dw s) := fun s => by
    simp only [hndef]
    field_simp
    ring
  have hdd : (fun s => (dp s + dw s) - εp / (2 * bigTheta α εp) *
      crossVar μ (fun i => pbar + s * ζ i) - upsilon α φ εw / 2 *
      crossVar ν (fun j => wbar + s * ξ j)) =O[𝓝 0] fun s => s ^ 3 :=
    ((dP_second_order hζ hBp hεp hα0 hα1 pbar).add
      (effWageDisp_second_order (α := α) hξ hBw hφ0 hεw wbar)).congr_left fun s => by ring
  have hwd : deriv w N = -N ^ φ := by
    rw [hwdef, deriv_negDisutil hφ0]
  have hEff' : deriv w N * N = -(1 - α) * (deriv u C * C) := by
    rw [hwd]
    linarith
  have key := period_utility_second_order (u := u) (w := w) (C := C) (N := N) (εp := εp)
    (εw := εw) (d := fun s => dp s + dw s) hu (negDisutil_contDiffAt hN) hσ
    (negDisutil_phi hφ0 hN) hEff' hα1.ne hden hy ha hz
    (crossVar_family_isBigO hζ hBp pbar) (crossVar_family_isBigO hξ hBw wbar) hdd hn
  refine key.congr_left fun s => ?_
  -- the exact identities of the model
  have hPint := dispIntegral_family_pos (μ := μ) hζ hBp (ε := εp) (by linarith)
    (-εp / (1 - α)) pbar s
  have hWint := dispIntegral_family_pos (μ := ν) hξ hBw (ε := εw) (by linarith)
    (-(εw * (1 + φ))) wbar s
  have hPpos : 0 < cesIndex μ εp (fun i => Real.exp (pbar + s * ζ i)) := by
    rw [cesIndex_family hζ hBp (by linarith)]
    exact Real.exp_pos _
  have hWpos : 0 < cesIndex ν εw (fun j => Real.exp (wbar + s * ξ j)) := by
    rw [cesIndex_family hξ hBw (by linarith)]
    exact Real.exp_pos _
  have hYpos : 0 ≤ C * Real.exp (y s) :=
    (mul_pos (mul_pos hA (Real.rpow_pos_of_pos hN _)) (Real.exp_pos _)).le
  have hNd : ∫ i, ((C * Real.exp (y s)) *
        (Real.exp (pbar + s * ζ i) / cesIndex μ εp (fun i => Real.exp (pbar + s * ζ i)))
          ^ (-εp) / (A * Real.exp (a s))) ^ (1 - α)⁻¹ ∂μ
      = (C * Real.exp (y s) / (A * Real.exp (a s))) ^ (1 - α)⁻¹ *
          Real.exp (dp s / (1 - α)) := by
    have hpt : ∀ i, ((C * Real.exp (y s)) *
        (Real.exp (pbar + s * ζ i) / cesIndex μ εp (fun i => Real.exp (pbar + s * ζ i)))
          ^ (-εp) / (A * Real.exp (a s))) ^ (1 - α)⁻¹
        = (C * Real.exp (y s) / (A * Real.exp (a s))) ^ (1 - α)⁻¹ *
          (Real.exp (pbar + s * ζ i) / cesIndex μ εp (fun i => Real.exp (pbar + s * ζ i)))
            ^ (-εp / (1 - α)) := fun i =>
      firmLabour_eq hYpos (mul_pos hA (Real.exp_pos _))
        (div_pos (Real.exp_pos _) hPpos).le
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
    rw [hdp]
    simp only [dP, priceDisp]
    rw [mul_div_cancel_left₀ _ h1, Real.exp_log hPint.2, dispIntegral]
  have hNdpos : 0 ≤ (C * Real.exp (y s) / (A * Real.exp (a s))) ^ (1 - α)⁻¹ *
      Real.exp (dp s / (1 - α)) :=
    mul_nonneg (Real.rpow_nonneg (div_nonneg hYpos (mul_pos hA (Real.exp_pos _)).le) _)
      (Real.exp_pos _).le
  have hD := disutility_types_eq (μ := ν) (εw := εw) hφ0 hNdpos
    (W := fun j => Real.exp (wbar + s * ξ j)) (fun j => Real.exp_pos _) hWpos hWint.2
  have hdwexp : Real.exp (Real.log (dispIntegral ν εw (-(εw * (1 + φ)))
      (fun j => Real.exp (wbar + s * ξ j))) / (1 + φ)) = Real.exp (dw s / (1 - α)) := by
    rw [hdw]
    simp only [effWageDisp]
    congr 1
    field_simp
  have hEH := effectiveHours_identity (y := y s) (a := a s) (dp := dp s) (dw := dw s) hα1 hA hN
  rw [hNd, hD, hdwexp, hEH]
  have hnN : N * Real.exp ((y s - a s + dp s + dw s) / (1 - α)) = N * Real.exp (n s) := rfl
  rw [hnN]
  simp only [hwdef]
  ring_nf

/-- Galí (2015), p. 192 (**Lemma 2 with inherited dispersion**, survey error 8): with any
`V_0 ≥ 0`, `∑ βᵗ V_{t+1} = θ V_0/(1 − βθ) + θ/((1 − βθ)(1 − θ)) ∑ βᵗ q_t`: the printed
equality holds only up to the policy-independent term `θ V_0/(1 − βθ)`. -/
theorem lemma2_inherited {θ β : ℝ} {V q : ℕ → ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hV0 : 0 ≤ V 0) (hq : ∀ t, 0 ≤ q t)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * q t) (hQ : Summable fun t => β ^ t * q t) :
    HasSum (fun t => β ^ t * V (t + 1))
      (θ * V 0 / (1 - β * θ) + θ / ((1 - β * θ) * (1 - θ)) * ∑' t, β ^ t * q t) := by
  have hβθ : β * θ < 1 := by nlinarith
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h := lemma2_hasSum hθ0 hβ0 hβθ (div_nonneg hθ0 (by linarith)) hV0 hq hrec hQ
  convert h using 1
  field_simp

/-- Galí (2015), p. 192 (**survey error 8, counterexample**): with inherited dispersion
`V_0 = 1`, `θ ∈ (0, 1)` and no inflation (`q ≡ 0`), `V_t = θᵗ` satisfies the Calvo recursion and
`∑ βᵗ V_{t+1} = θ/(1 − βθ) > 0`, while the printed Lemma 2 gives `0`: the equality holds only
up to terms independent of policy. -/
theorem lemma2_printed_fails_with_inherited {θ β : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∀ t, θ ^ (t + 1) = θ * θ ^ t + θ / (1 - θ) * 0) ∧
      HasSum (fun t => β ^ t * θ ^ (t + 1)) (θ / (1 - β * θ)) ∧
      θ / (1 - β * θ) ≠ θ / ((1 - β * θ) * (1 - θ)) * ∑' _ : ℕ, β ^ 0 * (0 : ℝ) := by
  have hβθ : β * θ < 1 := by nlinarith
  refine ⟨fun t => by ring, ?_, ?_⟩
  · have h := (hasSum_geometric_of_lt_one (mul_nonneg hβ0 hθ0.le) hβθ).mul_left θ
    have e : (fun t => β ^ t * θ ^ (t + 1)) = fun t => θ * (β * θ) ^ t := by
      funext t
      rw [mul_pow, pow_succ]
      ring
    rw [e, div_eq_mul_inv]
    exact h
  · simp only [mul_zero, tsum_zero]
    exact (div_pos hθ0 (by linarith)).ne'

/-! ### The welfare loss (28) and the average loss (29) -/

/-- Galí (2015), p. 166: `λ_p = (1 − θ_p)(1 − βθ_p)Θ/θ_p`. -/
noncomputable def lambdaP (β θp α εp : ℝ) : ℝ := (1 - θp) * (1 - β * θp) / θp * bigTheta α εp

/-- Galí (2015), eq. (15), p. 170: `λ_w = (1 − θ_w)(1 − βθ_w)/(θ_w(1 + ε_w φ))`. -/
noncomputable def lambdaW (β θw φ εw : ℝ) : ℝ := (1 - θw) * (1 - β * θw) / (θw * (1 + εw * φ))

/-- Galí (2015), eq. (28), p. 179: the weight on price inflation `ε_p/λ_p`. -/
noncomputable def priceWeight (β θp α εp : ℝ) : ℝ := εp / lambdaP β θp α εp

/-- Galí (2015), eq. (28), p. 179: the weight on wage inflation `ε_w(1 − α)/λ_w`. -/
noncomputable def wageWeight (β θw α φ εw : ℝ) : ℝ := εw * (1 - α) / lambdaW β θw φ εw

/-- Galí (2015), eq. (28), p. 179: the period loss
`½[(σ + (φ+α)/(1−α)) ỹ² + (ε_p/λ_p)(π^p)² + (ε_w(1−α)/λ_w)(π^w)²]`. -/
noncomputable def periodLoss (β θp θw σ φ α εp εw ygap pp pw : ℝ) : ℝ :=
  (gapCoeff σ φ α * ygap ^ 2 + priceWeight β θp α εp * pp ^ 2 +
    wageWeight β θw α φ εw * pw ^ 2) / 2

/-- Galí (2015), eq. (28), p. 179 (**the welfare loss `𝕎`**, for a given path, up to t.i.p.). -/
noncomputable def welfareLoss (β θp θw σ φ α εp εw : ℝ) (ygap pp pw : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * periodLoss β θp θw σ φ α εp εw (ygap t) (pp t) (pw t)

/-- Galí (2015), eq. (29), p. 179 (**the average period loss `L`**) as a function of the
variances. -/
noncomputable def avgLoss (β θp θw σ φ α εp εw varY varP varW : ℝ) : ℝ :=
  (gapCoeff σ φ α * varY + priceWeight β θp α εp * varP + wageWeight β θw α φ εw * varW) / 2

/-- Galí (2015), p. 192: `(ε_p/Θ) · θ_p/((1 − βθ_p)(1 − θ_p)) = ε_p/λ_p`. -/
theorem priceWeight_of_dispersion {β θ α εp : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβθ : β * θ < 1) (hα : α < 1) :
    εp / bigTheta α εp * (θ / ((1 - β * θ) * (1 - θ))) = priceWeight β θ α εp := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold priceWeight lambdaP bigTheta
  field_simp

/-- Galí (2015), p. 192: `Υ · θ_w/((1 − βθ_w)(1 − θ_w)) = ε_w(1 − α)/λ_w`, the step from the
wage dispersion term to the wage-inflation weight. -/
theorem wageWeight_of_dispersion {β θ α φ εw : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβθ : β * θ < 1) (hφε : 1 + εw * φ ≠ 0) :
    upsilon α φ εw * (θ / ((1 - β * θ) * (1 - θ))) = wageWeight β θ α φ εw := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  unfold wageWeight lambdaW upsilon
  field_simp

/-- Galí (2015), p. 192 (**(28) from the dispersion form, exact**): if the price and wage
cross-sectional variances follow the exact Calvo recursions
`V_{t+1} = θ V_t + (θ/(1−θ)) (Δm_t)²` with no inherited dispersion, then
`½ ∑ βᵗ [Γ ỹ_t² + (ε_p/Θ) V^p_{t+1} + Υ V^w_{t+1}] = 𝕎(ỹ, Δm^p, Δm^w)`. -/
theorem welfare_eq_loss {β θp θw σ φ α εp εw : ℝ} (hθp0 : 0 < θp) (hθp1 : θp < 1)
    (hθw0 : 0 < θw) (hθw1 : θw < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα : α < 1)
    (hφε : 1 + εw * φ ≠ 0) {ygap Dp Dw Vp Vw : ℕ → ℝ} (hVp0 : Vp 0 = 0) (hVw0 : Vw 0 = 0)
    (hrecp : ∀ t, Vp (t + 1) = θp * Vp t + θp / (1 - θp) * Dp t ^ 2)
    (hrecw : ∀ t, Vw (t + 1) = θw * Vw t + θw / (1 - θw) * Dw t ^ 2)
    (hY : Summable fun t => β ^ t * ygap t ^ 2) (hDp : Summable fun t => β ^ t * Dp t ^ 2)
    (hDw : Summable fun t => β ^ t * Dw t ^ 2) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * ygap t ^ 2 + εp / bigTheta α εp * Vp (t + 1) +
        upsilon α φ εw * Vw (t + 1)) / 2))
      (welfareLoss β θp θw σ φ α εp εw ygap Dp Dw) := by
  have hβθp : β * θp < 1 := by nlinarith
  have hβθw : β * θw < 1 := by nlinarith
  have hLp := lemma2 (q := fun t => Dp t ^ 2) hθp0.le hθp1 hβ0 hβ1 hVp0 (fun _ => sq_nonneg _)
    hrecp hDp
  have hLw := lemma2 (q := fun t => Dw t ^ 2) hθw0.le hθw1 hβ0 hβ1 hVw0 (fun _ => sq_nonneg _)
    hrecw hDw
  have hA := (((hY.hasSum.mul_left (gapCoeff σ φ α)).add
    (hLp.mul_left (εp / bigTheta α εp))).add (hLw.mul_left (upsilon α φ εw))).div_const 2
  have hB := (((hY.hasSum.mul_left (gapCoeff σ φ α)).add
    (hDp.hasSum.mul_left (priceWeight β θp α εp))).add
    (hDw.hasSum.mul_left (wageWeight β θw α φ εw))).div_const 2
  have hW : welfareLoss β θp θw σ φ α εp εw ygap Dp Dw
      = (gapCoeff σ φ α * ∑' t, β ^ t * ygap t ^ 2 +
        priceWeight β θp α εp * ∑' t, β ^ t * Dp t ^ 2 +
        wageWeight β θw α φ εw * ∑' t, β ^ t * Dw t ^ 2) / 2 := by
    rw [← hB.tsum_eq]
    unfold welfareLoss periodLoss
    congr 1
    funext t
    ring
  rw [hW, ← priceWeight_of_dispersion hθp0 hθp1 hβθp hα,
    ← wageWeight_of_dispersion (α := α) hθw0 hθw1 hβθw hφε]
  convert hA using 1
  · funext t
    ring
  · ring

/-- Galí (2015), p. 192 (**(28) with inherited dispersion**, survey error 8): with any
inherited `V^p_0, V^w_0 ≥ 0` the discounted dispersion form equals `𝕎` **plus** the
policy-independent constant `½[(ε_p/Θ) θ_p V^p_0/(1 − βθ_p) + Υ θ_w V^w_0/(1 − βθ_w)]`. -/
theorem welfare_eq_loss_inherited {β θp θw σ φ α εp εw : ℝ} (hθp0 : 0 < θp) (hθp1 : θp < 1)
    (hθw0 : 0 < θw) (hθw1 : θw < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα : α < 1)
    (hφε : 1 + εw * φ ≠ 0) {ygap Dp Dw Vp Vw : ℕ → ℝ} (hVp0 : 0 ≤ Vp 0) (hVw0 : 0 ≤ Vw 0)
    (hrecp : ∀ t, Vp (t + 1) = θp * Vp t + θp / (1 - θp) * Dp t ^ 2)
    (hrecw : ∀ t, Vw (t + 1) = θw * Vw t + θw / (1 - θw) * Dw t ^ 2)
    (hY : Summable fun t => β ^ t * ygap t ^ 2) (hDp : Summable fun t => β ^ t * Dp t ^ 2)
    (hDw : Summable fun t => β ^ t * Dw t ^ 2) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * ygap t ^ 2 + εp / bigTheta α εp * Vp (t + 1) +
        upsilon α φ εw * Vw (t + 1)) / 2))
      (welfareLoss β θp θw σ φ α εp εw ygap Dp Dw +
        (εp / bigTheta α εp * (θp * Vp 0 / (1 - β * θp)) +
          upsilon α φ εw * (θw * Vw 0 / (1 - β * θw))) / 2) := by
  have hβθp : β * θp < 1 := by nlinarith
  have hβθw : β * θw < 1 := by nlinarith
  have hLp := lemma2_inherited (q := fun t => Dp t ^ 2) hθp0.le hθp1 hβ0 hβ1 hVp0
    (fun _ => sq_nonneg _) hrecp hDp
  have hLw := lemma2_inherited (q := fun t => Dw t ^ 2) hθw0.le hθw1 hβ0 hβ1 hVw0
    (fun _ => sq_nonneg _) hrecw hDw
  have hA := (((hY.hasSum.mul_left (gapCoeff σ φ α)).add
    (hLp.mul_left (εp / bigTheta α εp))).add (hLw.mul_left (upsilon α φ εw))).div_const 2
  have hB := (((hY.hasSum.mul_left (gapCoeff σ φ α)).add
    (hDp.hasSum.mul_left (priceWeight β θp α εp))).add
    (hDw.hasSum.mul_left (wageWeight β θw α φ εw))).div_const 2
  have hW : welfareLoss β θp θw σ φ α εp εw ygap Dp Dw
      = (gapCoeff σ φ α * ∑' t, β ^ t * ygap t ^ 2 +
        priceWeight β θp α εp * ∑' t, β ^ t * Dp t ^ 2 +
        wageWeight β θw α φ εw * ∑' t, β ^ t * Dw t ^ 2) / 2 := by
    rw [← hB.tsum_eq]
    unfold welfareLoss periodLoss
    congr 1
    funext t
    ring
  rw [hW, ← priceWeight_of_dispersion hθp0 hθp1 hβθp hα,
    ← wageWeight_of_dispersion (α := α) hθw0 hθw1 hβθw hφε]
  convert hA using 1
  · funext t
    ring
  · ring

/-- Galí (2015), pp. 179 and 192 (**(28) for the Calvo economy, exact in `Δm`**): along the
Calvo sequences of price and wage cross-sections (both following the Calvo mixture `wageMix`,
with `θ_p` and `θ_w`) with no inherited dispersion,
`½ ∑ βᵗ [Γ ỹ_t² + (ε_p/Θ) var_i p_t + Υ var_j w_t] = 𝕎(ỹ, Δm^p, Δm^w)`. -/
theorem welfare_eq_loss_calvo {β θp θw σ φ α εp εw : ℝ} (hθp0 : 0 < θp) (hθp1 : θp < 1)
    (hθw0 : 0 < θw) (hθw1 : θw < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα : α < 1)
    (hφε : 1 + εw * φ ≠ 0) {ygap : ℕ → ℝ} {νp νw : ℕ → Measure ℝ} {pstar wstar : ℕ → ℝ}
    (hνp : ∀ t, νp (t + 1) = wageMix θp (νp t) (pstar t))
    (hνw : ∀ t, νw (t + 1) = wageMix θw (νw t) (wstar t))
    (hgp : GoodDist (νp 0)) (hgw : GoodDist (νw 0))
    (hVp0 : crossVarDist (νp 0) = 0) (hVw0 : crossVarDist (νw 0) = 0)
    (hY : Summable fun t => β ^ t * ygap t ^ 2)
    (hDp : Summable fun t => β ^ t * (crossMean (νp (t + 1)) - crossMean (νp t)) ^ 2)
    (hDw : Summable fun t => β ^ t * (crossMean (νw (t + 1)) - crossMean (νw t)) ^ 2) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * ygap t ^ 2 +
        εp / bigTheta α εp * crossVarDist (νp (t + 1)) +
        upsilon α φ εw * crossVarDist (νw (t + 1))) / 2))
      (welfareLoss β θp θw σ φ α εp εw ygap (fun t => crossMean (νp (t + 1)) - crossMean (νp t))
        fun t => crossMean (νw (t + 1)) - crossMean (νw t)) :=
  welfare_eq_loss (Vp := fun t => crossVarDist (νp t)) (Vw := fun t => crossVarDist (νw t))
    hθp0 hθp1 hθw0 hθw1 hβ0 hβ1 hα hφε hVp0 hVw0 (wage_var_recursion hθp0.le hθp1 hνp hgp)
    (wage_var_recursion hθw0.le hθw1 hνw hgw) hY hDp hDw

/-- Galí (2015), eq. (29), p. 179 (**from `𝕎` to `L`**): if the expected squared gap and
squared price and wage inflation equal stationary variances at every date, the discounted
expected loss is `L/(1 − β)`. -/
theorem welfare_stationary {β θp θw σ φ α εp εw varY varP varW : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {eY eP eW : ℕ → ℝ} (heY : ∀ t, eY t = varY) (heP : ∀ t, eP t = varP)
    (heW : ∀ t, eW t = varW) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * eY t + priceWeight β θp α εp * eP t +
        wageWeight β θw α φ εw * eW t) / 2))
      (avgLoss β θp θw σ φ α εp εw varY varP varW / (1 - β)) := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right
    (avgLoss β θp θw σ φ α εp εw varY varP varW)
  convert h using 1
  · funext t
    rw [heY, heP, heW, avgLoss]
  · rw [div_eq_inv_mul]

/-! ### Comparative statics of the wage-inflation weight (p. 179) -/

/-- Galí (2015), p. 179: the wage-inflation weight in closed form,
`ε_w(1 − α)/λ_w = ε_w(1 − α) θ_w (1 + ε_w φ)/((1 − θ_w)(1 − βθ_w))`. -/
theorem wageWeight_eq {β θ α φ εw : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hφε : 1 + εw * φ ≠ 0) :
    wageWeight β θ α φ εw = εw * (1 - α) * θ * (1 + εw * φ) / ((1 - θ) * (1 - β * θ)) := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  unfold wageWeight lambdaW
  field_simp

/-- Galí (2015), p. 179, claim (i): the wage-inflation weight is strictly **increasing in the
elasticity of substitution among labour types** `ε_w` (on `ε_w > 0`, for `φ ≥ 0`, `α < 1`). -/
theorem wageWeight_strictMonoOn_eps {β θ α φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β ≤ 1)
    (hα1 : α < 1) (hφ : 0 ≤ φ) :
    StrictMonoOn (fun εw => wageWeight β θ α φ εw) (Set.Ioi 0) := by
  have hβθ : β * θ < 1 := by nlinarith
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hφa : 1 + a * φ ≠ 0 := by nlinarith
  have hφb : 1 + b * φ ≠ 0 := by nlinarith
  simp only
  rw [wageWeight_eq hθ0 hθ1 hβθ hφa, wageWeight_eq hθ0 hθ1 hβθ hφb]
  have hD : 0 < (1 - θ) * (1 - β * θ) := mul_pos (by linarith) (by linarith)
  apply div_lt_div_of_pos_right _ hD
  have hk : a * (1 + a * φ) < b * (1 + b * φ) := by
    have h0 : 0 < (b - a) * (1 + (a + b) * φ) := mul_pos (by linarith) (by nlinarith)
    nlinarith [h0]
  have hc : 0 < (1 - α) * θ := mul_pos (by linarith) hθ0
  nlinarith

/-- Galí (2015), p. 179, claim (ii): the wage-inflation weight is strictly **increasing in the
labour elasticity `1 − α`**, i.e. strictly decreasing in `α` (for `ε_w > 0`, `φ ≥ 0`). -/
theorem wageWeight_strictAnti_alpha {β θ φ εw : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β ≤ 1)
    (hεw : 0 < εw) (hφ : 0 ≤ φ) :
    StrictAnti fun α => wageWeight β θ α φ εw := by
  have hβθ : β * θ < 1 := by nlinarith
  have hφε : 1 + εw * φ ≠ 0 := by nlinarith
  intro a b hab
  simp only
  rw [wageWeight_eq hθ0 hθ1 hβθ hφε, wageWeight_eq hθ0 hθ1 hβθ hφε]
  have hD : 0 < (1 - θ) * (1 - β * θ) := mul_pos (by linarith) (by linarith)
  apply div_lt_div_of_pos_right _ hD
  have hc : 0 < εw * θ * (1 + εw * φ) := mul_pos (mul_pos hεw hθ0) (by nlinarith)
  nlinarith

/-- Galí (2015), p. 179, claim (iii): the wage-inflation weight is strictly **increasing in
the degree of wage stickiness** `θ_w ∈ (0, 1)` (for `β ≤ 1`, `ε_w > 0`, `φ ≥ 0`, `α < 1`). -/
theorem wageWeight_strictMonoOn_theta {β α φ εw : ℝ} (hβ1 : β ≤ 1) (hα1 : α < 1)
    (hεw : 0 < εw) (hφ : 0 ≤ φ) :
    StrictMonoOn (fun θ => wageWeight β θ α φ εw) (Set.Ioo 0 1) := by
  have hφε : 1 + εw * φ ≠ 0 := by nlinarith
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hβa : β * a < 1 := by nlinarith
  have hβb : β * b < 1 := by nlinarith
  simp only
  rw [wageWeight_eq ha0 ha1 hβa hφε, wageWeight_eq hb0 hb1 hβb hφε]
  have hDa : 0 < (1 - a) * (1 - β * a) := mul_pos (by linarith) (by linarith)
  have hDb : 0 < (1 - b) * (1 - β * b) := mul_pos (by linarith) (by linarith)
  rw [div_lt_div_iff₀ hDa hDb]
  have hk : 0 < εw * (1 - α) * (1 + εw * φ) :=
    mul_pos (mul_pos hεw (by linarith)) (by nlinarith)
  have hkey : a * ((1 - b) * (1 - β * b)) < b * ((1 - a) * (1 - β * a)) := by
    have h1 : 0 < (b - a) * (1 - β * a * b) := mul_pos (by linarith) (by nlinarith)
    nlinarith
  have e1 : εw * (1 - α) * a * (1 + εw * φ) * ((1 - b) * (1 - β * b))
      = εw * (1 - α) * (1 + εw * φ) * (a * ((1 - b) * (1 - β * b))) := by ring
  have e2 : εw * (1 - α) * b * (1 + εw * φ) * ((1 - a) * (1 - β * a))
      = εw * (1 - α) * (1 + εw * φ) * (b * ((1 - a) * (1 - β * a))) := by ring
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left hkey hk

/-- Galí (2015), p. 179 ("θ_w … inversely related to λ_w"): `λ_w` is strictly decreasing in
`θ_w ∈ (0, 1)` (for `β ≤ 1`, `ε_w φ > −1`). -/
theorem lambdaW_strictAntiOn_theta {β φ εw : ℝ} (hβ1 : β ≤ 1) (hφε : 0 < 1 + εw * φ) :
    StrictAntiOn (fun θ => lambdaW β θ φ εw) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  simp only [lambdaW]
  rw [div_lt_div_iff₀ (mul_pos hb0 hφε) (mul_pos ha0 hφε)]
  have hab1 : a * b < 1 := by nlinarith
  have hβab : β * (a * b) ≤ a * b := by
    nlinarith [mul_nonneg (sub_nonneg.2 hβ1) (mul_pos ha0 hb0).le]
  have hkey : a * ((1 - b) * (1 - β * b)) < b * ((1 - a) * (1 - β * a)) := by
    have h1 : 0 < (b - a) * (1 - β * a * b) := mul_pos (by linarith) (by nlinarith)
    nlinarith
  have e1 : (1 - b) * (1 - β * b) * (a * (1 + εw * φ))
      = (1 + εw * φ) * (a * ((1 - b) * (1 - β * b))) := by ring
  have e2 : (1 - a) * (1 - β * a) * (b * (1 + εw * φ))
      = (1 + εw * φ) * (b * ((1 - a) * (1 - β * a))) := by ring
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left hkey hφε

/-- Galí (2015), p. 179: the wage-inflation weight is positive for `θ_w ∈ (0, 1)`, `β ≤ 1`,
`ε_w > 0`, `φ ≥ 0`, `α < 1`. -/
theorem wageWeight_pos {β θ α φ εw : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β ≤ 1)
    (hα1 : α < 1) (hεw : 0 < εw) (hφ : 0 ≤ φ) : 0 < wageWeight β θ α φ εw := by
  have hβθ : β * θ < 1 := by nlinarith
  have hφε : 0 < 1 + εw * φ := by nlinarith
  rw [wageWeight_eq hθ0 hθ1 hβθ hφε.ne']
  exact div_pos (mul_pos (mul_pos (mul_pos hεw (by linarith)) hθ0) hφε)
    (mul_pos (by linarith) (by linarith))

end Gali.StickyWagesPrices.Welfare
