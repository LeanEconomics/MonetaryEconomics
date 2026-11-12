/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR6MeasTable51

/-!
# The Euler equation behind (5.1) as an exact derivative in a probability model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1, p. 118 (the
linearisation of the consumer's first-order condition into (5.1)).

`NKModel.euler_deriv` differentiates `ε ↦ −log E_t[exp(ε X_{t+1})]` at the steady state `ε = 0`
for the abstract `ExpectationSystem`. With Mathlib's conditional expectation each `E_t[exp(εX)]`
is only an a.e.-class, so the derivative is stated in the two forms that survive this:

* **a uniform (essential-supremum) second-order bound**: for `|ε| ≤ ε₀`, a.e.
  `|−log E_t[exp(εX)] − ε(−E_t X)| ≤ Q ε²` (`mlog_E_exp_quadratic`; first `mE_exp_quadratic`),
  i.e. the map `ε ↦ −log E_t[exp(εX)]` into `L^∞` is differentiable at `0` with derivative
  `−E_t X`;
* **the pathwise derivative along every sequence**: for every `ε_n → 0` (`ε_n ≠ 0`), a.e. the
  difference quotients converge to `−E_t X(ω)` (`mlog_E_exp_seq`); no version selection is
  needed because a countable family of a.e. statements holds simultaneously.

Applied to `X = −γ(c_{t+1} − c_t) − π_{t+1}`: **`meuler_deriv`** and **`meuler_deriv_seq`** give
the derivative `γ(E_t c_{t+1} − c_t) + E_t π_{t+1}`, the right-hand side of the linearised Euler
equation (with `NKModel.is_iff_linear_euler` this is (5.1)).
-/

namespace Cochrane.StickyPriceFiscal.TidyR6MeasEuler

open MeasureTheory Filter Topology ExpectationsMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), p. 118 (tool): for `|h|(|K| + 1) ≤ 1` and `|X| ≤ K`,
`|E_t[exp(hX)] − 1 − h E_t X| ≤ K² h²` a.e. -/
theorem mE_exp_quadratic {K : ℝ} {X : Ω → ℝ} (hXm : AEStronglyMeasurable X S.μ)
    (hX : ∀ ω, |X ω| ≤ K) (t : ℕ) {h : ℝ} (hh : |h| * (|K| + 1) ≤ 1) :
    ∀ᵐ ω ∂S.μ, |S.E t (fun ω' => Real.exp (h * X ω')) ω - 1 - h * S.E t X ω| ≤
      |K| ^ 2 * h ^ 2 := by
  have hXi : Integrable X S.μ := Integrable.of_bound hXm K (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hX ω)
  have hem : AEStronglyMeasurable (fun ω' => Real.exp (h * X ω')) S.μ :=
    (Real.continuous_exp.comp_aestronglyMeasurable (hXm.const_mul h))
  have hei : Integrable (fun ω' => Real.exp (h * X ω')) S.μ :=
    Integrable.of_bound hem (Real.exp (|h| * |K|)) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
      calc h * X ω ≤ |h * X ω| := le_abs_self _
        _ = |h| * |X ω| := abs_mul _ _
        _ ≤ |h| * |K| := mul_le_mul_of_nonneg_left ((hX ω).trans (le_abs_self K))
            (abs_nonneg _))
  have hrem : ∀ ω', |Real.exp (h * X ω') - 1 - h * X ω'| ≤ |K| ^ 2 * h ^ 2 := by
    intro ω'
    have hx : |h * X ω'| ≤ 1 := by
      rw [abs_mul]
      have h1 : |X ω'| ≤ |K| := (hX ω').trans (le_abs_self K)
      nlinarith [abs_nonneg h, abs_nonneg (X ω')]
    refine (Real.abs_exp_sub_one_sub_id_le hx).trans ?_
    rw [mul_pow, mul_comm (|K| ^ 2)]
    have : X ω' ^ 2 ≤ |K| ^ 2 := by
      rw [← sq_abs (X ω')]
      exact pow_le_pow_left₀ (abs_nonneg _) ((hX ω').trans (le_abs_self K)) 2
    exact mul_le_mul_of_nonneg_left this (sq_nonneg h)
  have hfun : (fun ω' => Real.exp (h * X ω') - 1 - h * X ω') =
      ((fun ω' => Real.exp (h * X ω')) - fun _ => (1 : ℝ)) - h • X := by
    funext ω'
    simp
  filter_upwards [S.abs_E_le (Eventually.of_forall hrem) t,
    S.E_sub (hei.sub (integrable_const 1)) (hXi.smul h) t,
    S.E_sub hei (integrable_const (1 : ℝ)) t, S.E_smul h X t] with ω e1 e2 e3 e4
  rw [hfun, e2, Pi.sub_apply, e3, Pi.sub_apply, e4, S.E_const, Pi.smul_apply,
    smul_eq_mul] at e1
  exact e1

/-- Cochrane (2023), p. 118, **the linearisation as an `L^∞` derivative**: for `|X| ≤ K` and
`|h| ≤ 1/(2(|K| + 1)²)`, a.e.
`|−log E_t[exp(hX)] − h(−E_t X)| ≤ (|K|² + 2(|K| + |K|²)²) h²`. -/
theorem mlog_E_exp_quadratic {K : ℝ} {X : Ω → ℝ} (hXm : AEStronglyMeasurable X S.μ)
    (hX : ∀ ω, |X ω| ≤ K) (t : ℕ) {h : ℝ} (hh : |h| ≤ 1 / (2 * (|K| + 1) ^ 2)) :
    ∀ᵐ ω ∂S.μ, |-Real.log (S.E t (fun ω' => Real.exp (h * X ω')) ω) - h * (-S.E t X ω)| ≤
      (|K| ^ 2 + 2 * (|K| + |K| ^ 2) ^ 2) * h ^ 2 := by
  set k := |K|
  have hk : 0 ≤ k := abs_nonneg K
  have hk1 : 1 ≤ (k + 1) ^ 2 := by nlinarith
  have hh1 : |h| * (k + 1) ^ 2 ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hh
    linarith
  have hh2 : |h| * (k + 1) ≤ 1 := by nlinarith [abs_nonneg h]
  have hhle : |h| ≤ 1 := by nlinarith [abs_nonneg h]
  filter_upwards [mE_exp_quadratic S hXm hX t hh2,
    S.abs_E_le (Eventually.of_forall fun ω => (hX ω).trans (le_abs_self K)) t] with ω e1 e2
  set y := S.E t (fun ω' => Real.exp (h * X ω')) ω
  set e := S.E t X ω
  have hy1 : |y - 1| ≤ (k + k ^ 2) * |h| := by
    have : |y - 1| ≤ |y - 1 - h * e| + |h * e| := by
      have := abs_add_le (y - 1 - h * e) (h * e)
      rwa [sub_add_cancel] at this
    rw [abs_mul] at this
    have h3 : |h| * |e| ≤ |h| * k := mul_le_mul_of_nonneg_left e2 (abs_nonneg h)
    have h4 : k ^ 2 * h ^ 2 ≤ k ^ 2 * |h| := by
      rw [← sq_abs h]
      exact mul_le_mul_of_nonneg_left (by nlinarith [abs_nonneg h]) (sq_nonneg k)
    nlinarith
  have hyhalf : 1 / 2 ≤ y := by
    have : (k + k ^ 2) * |h| ≤ 1 / 2 := by nlinarith [abs_nonneg h]
    have := (abs_le.1 (hy1.trans this)).1
    linarith
  have hypos : 0 < y := by linarith
  have hlog1 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hypos
  have hlog2 : 1 - y⁻¹ ≤ Real.log y := Real.one_sub_inv_le_log_of_pos hypos
  have hlog : |Real.log y - (y - 1)| ≤ 2 * (y - 1) ^ 2 := by
    rw [abs_le]
    constructor
    · have : (y - 1) - (1 - y⁻¹) = (y - 1) ^ 2 / y := by field_simp
      have h5 : (y - 1) ^ 2 / y ≤ 2 * (y - 1) ^ 2 := by
        rw [div_le_iff₀ hypos]
        nlinarith [sq_nonneg (y - 1)]
      linarith
    · nlinarith [sq_nonneg (y - 1)]
  have hsq : (y - 1) ^ 2 ≤ (k + k ^ 2) ^ 2 * h ^ 2 := by
    rw [← sq_abs (y - 1), ← sq_abs h, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hy1 2
  have : |-Real.log y - h * -e| ≤ |Real.log y - (y - 1)| + |y - 1 - h * e| := by
    rw [show -Real.log y - h * -e = -((Real.log y - (y - 1)) + (y - 1 - h * e)) by ring,
      abs_neg]
    exact abs_add_le _ _
  nlinarith

/-- Cochrane (2023), p. 118, **the pathwise derivative along every sequence**: for `|X| ≤ K` and
any `h_n → 0` with `h_n ≠ 0`, a.e. `(−log E_t[exp(h_n X)])/h_n → −E_t X`. -/
theorem mlog_E_exp_seq {K : ℝ} {X : Ω → ℝ} (hXm : AEStronglyMeasurable X S.μ)
    (hX : ∀ ω, |X ω| ≤ K) (t : ℕ) {hs : ℕ → ℝ} (hlim : Tendsto hs atTop (𝓝 0))
    (hne : ∀ n, hs n ≠ 0) :
    ∀ᵐ ω ∂S.μ, Tendsto (fun n => -Real.log (S.E t (fun ω' => Real.exp (hs n * X ω')) ω) / hs n)
      atTop (𝓝 (-S.E t X ω)) := by
  set Q := |K| ^ 2 + 2 * (|K| + |K| ^ 2) ^ 2
  have h0 : 0 < 1 / (2 * (|K| + 1) ^ 2) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_zero_iff_abs_tendsto_zero _).1 hlim
    |>.eventually (gt_mem_nhds h0))
  have hb : ∀ n, ∀ᵐ ω ∂S.μ, N ≤ n →
      |-Real.log (S.E t (fun ω' => Real.exp (hs n * X ω')) ω) - hs n * (-S.E t X ω)| ≤
        Q * hs n ^ 2 := fun n => by
    by_cases hn : N ≤ n
    · filter_upwards [mlog_E_exp_quadratic S hXm hX t (hN n hn).le] with ω e _
      exact e
    · exact Eventually.of_forall fun ω h => absurd h hn
  filter_upwards [ae_all_iff.2 hb] with ω e
  have hQ : Tendsto (fun n => Q * |hs n|) atTop (𝓝 0) := by
    have := ((tendsto_zero_iff_abs_tendsto_zero _).1 hlim).const_mul Q
    rwa [mul_zero] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ hQ
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn0 := hne n
  rw [norm_norm, Real.norm_eq_abs,
    show -Real.log (S.E t (fun ω' => Real.exp (hs n * X ω')) ω) / hs n - -S.E t X ω =
      (-Real.log (S.E t (fun ω' => Real.exp (hs n * X ω')) ω) - hs n * (-S.E t X ω)) / hs n by
      field_simp, abs_div]
  rw [div_le_iff₀ (abs_pos.2 hn0)]
  calc _ ≤ Q * hs n ^ 2 := e n hn
    _ = Q * |hs n| * |hs n| := by rw [mul_assoc, ← sq, sq_abs]

/-- Cochrane (2023), p. 118 (`NKModel.euler_deriv`), **in a probability model**: along a bounded
direction of log deviations `(c, π)` with `c` adapted, for `|h| ≤ 1/(2(|K|+1)²)`, a.e.
`|−log E_t[exp(h(−γ(c_{t+1} − c_t) − π_{t+1}))] − h(γ(E_t c_{t+1} − c_t) + E_t π_{t+1})| ≤ Q h²`:
the Euler equation's right-hand side has derivative `γ(E_t c_{t+1} − c_t) + E_t π_{t+1}` at the
steady state. -/
theorem meuler_deriv {K γ : ℝ} {c π : ℕ → Ω → ℝ} (hca : StronglyAdapted S.𝓕 c)
    (hci : ∀ t, Integrable (c t) S.μ) (hπm : ∀ t, AEStronglyMeasurable (π t) S.μ)
    (hπi : ∀ t, Integrable (π t) S.μ) (t : ℕ)
    (hb : ∀ ω, |-γ * (c (t + 1) ω - c t ω) - π (t + 1) ω| ≤ K) {h : ℝ}
    (hh : |h| ≤ 1 / (2 * (|K| + 1) ^ 2)) :
    ∀ᵐ ω ∂S.μ, |-Real.log (S.E t (fun ω' => Real.exp
      (h * (-γ * (c (t + 1) ω' - c t ω') - π (t + 1) ω'))) ω) -
        h * (γ * (S.E t (c (t + 1)) ω - c t ω) + S.E t (π (t + 1)) ω)| ≤
      (|K| ^ 2 + 2 * (|K| + |K| ^ 2) ^ 2) * h ^ 2 := by
  have hXm : AEStronglyMeasurable (fun ω' => -γ * (c (t + 1) ω' - c t ω') - π (t + 1) ω')
      S.μ := ((((hca (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable.sub
        ((hca t).mono (S.𝓕.le _)).aestronglyMeasurable).const_mul _).sub (hπm (t + 1))
  have hEX : S.E t (fun ω' => -γ * (c (t + 1) ω' - c t ω') - π (t + 1) ω') =ᵐ[S.μ]
      fun ω => -(γ * (S.E t (c (t + 1)) ω - c t ω) + S.E t (π (t + 1)) ω) := by
    have hfun : (fun ω' => -γ * (c (t + 1) ω' - c t ω') - π (t + 1) ω') =
        (-γ) • (c (t + 1) - c t) - π (t + 1) := rfl
    filter_upwards [S.E_sub (((hci (t + 1)).sub (hci t)).smul (-γ)) (hπi (t + 1)) t,
      S.E_smul (-γ) (c (t + 1) - c t) t, S.E_sub (hci (t + 1)) (hci t) t] with ω e1 e2 e3
    rw [hfun, e1, Pi.sub_apply, e2, Pi.smul_apply, e3, Pi.sub_apply,
      S.E_of_stronglyMeasurable (hca t) (hci t), smul_eq_mul]
    ring
  filter_upwards [mlog_E_exp_quadratic S hXm hb t hh, hEX] with ω e1 e2
  rw [e2, neg_neg] at e1
  exact e1

/-- Cochrane (2023), p. 118 (`NKModel.euler_deriv`), **the pathwise derivative in a probability
model**: for every `h_n → 0`, `h_n ≠ 0`, a.e. the difference quotients of
`h ↦ −log E_t[exp(h(−γ(c_{t+1} − c_t) − π_{t+1}))]` converge to
`γ(E_t c_{t+1} − c_t) + E_t π_{t+1}`. -/
theorem meuler_deriv_seq {K γ : ℝ} {c π : ℕ → Ω → ℝ} (hca : StronglyAdapted S.𝓕 c)
    (hci : ∀ t, Integrable (c t) S.μ) (hπm : ∀ t, AEStronglyMeasurable (π t) S.μ)
    (hπi : ∀ t, Integrable (π t) S.μ) (t : ℕ)
    (hb : ∀ ω, |-γ * (c (t + 1) ω - c t ω) - π (t + 1) ω| ≤ K) {hs : ℕ → ℝ}
    (hlim : Tendsto hs atTop (𝓝 0)) (hne : ∀ n, hs n ≠ 0) :
    ∀ᵐ ω ∂S.μ, Tendsto (fun n => -Real.log (S.E t (fun ω' => Real.exp
      (hs n * (-γ * (c (t + 1) ω' - c t ω') - π (t + 1) ω'))) ω) / hs n) atTop
      (𝓝 (γ * (S.E t (c (t + 1)) ω - c t ω) + S.E t (π (t + 1)) ω)) := by
  have hXm : AEStronglyMeasurable (fun ω' => -γ * (c (t + 1) ω' - c t ω') - π (t + 1) ω')
      S.μ := ((((hca (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable.sub
        ((hca t).mono (S.𝓕.le _)).aestronglyMeasurable).const_mul _).sub (hπm (t + 1))
  have hEX : S.E t (fun ω' => -γ * (c (t + 1) ω' - c t ω') - π (t + 1) ω') =ᵐ[S.μ]
      fun ω => -(γ * (S.E t (c (t + 1)) ω - c t ω) + S.E t (π (t + 1)) ω) := by
    have hfun : (fun ω' => -γ * (c (t + 1) ω' - c t ω') - π (t + 1) ω') =
        (-γ) • (c (t + 1) - c t) - π (t + 1) := rfl
    filter_upwards [S.E_sub (((hci (t + 1)).sub (hci t)).smul (-γ)) (hπi (t + 1)) t,
      S.E_smul (-γ) (c (t + 1) - c t) t, S.E_sub (hci (t + 1)) (hci t) t] with ω e1 e2 e3
    rw [hfun, e1, Pi.sub_apply, e2, Pi.smul_apply, e3, Pi.sub_apply,
      S.E_of_stronglyMeasurable (hca t) (hci t), smul_eq_mul]
    ring
  filter_upwards [mlog_E_exp_seq S hXm hb t hlim hne, hEX] with ω e1 e2
  rw [e2, neg_neg] at e1
  exact e1

end Cochrane.StickyPriceFiscal.TidyR6MeasEuler
