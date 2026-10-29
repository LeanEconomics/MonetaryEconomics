/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.ActivePassive
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The regression of p. 18 as a statistical estimate

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §1.9, pp. 18–19: "One is
tempted to run a regression, say `s₁ = a + γ(B₀/P₁) + u₁` … The regression would estimate
`γ = 1`", and the regression `s₁ = α(B₀/P₁*) + γ(B₀/P₁ − B₀/P₁*) + u₁` in which "`γ` … is not
identified". `ActivePassive.rule_regression_gamma_one` proves only that equilibrium data satisfy
`s₁ = 0 + 1 · B₀/P₁` exactly. This module gives the claims their statistical content: least
squares in a finite sample and in the population, with a precise consistency statement.

The precise content: in every equilibrium the valuation equation (1.4) `s₁ = B₀/P₁` holds
exactly, whatever the surplus rule. Hence
* the least-squares fit of `s₁` on a constant and `B₀/P₁` is **exactly** `(a, γ̂) = (0, 1)` in
  every sample in which `B₀/P₁` varies (`ols_iff`, `olsSlope_eq_one`), and in the population
  whenever `B₀/P₁` is square integrable and not almost surely constant (`popOLS_iff`);
* the estimator is therefore a consistent estimator of the structural response `γ` of the
  `γ`-rule iff `γ = 1` (`ols_consistent_iff`): an active rule (`γ ≠ 1`) is estimated as passive;
* in the second regression the regressor `B₀/P₁ − B₀/P₁*` is identically zero in every
  equilibrium of a determinate `γ`-rule, so every `γ` minimises the sum of squares, in the sample
  and in the population (`gamma_not_identified_sample`, `gamma_not_identified_pop`).
There is no sampling error to speak of: the equilibrium relation is exact, so "consistency" is
the statement that the estimate is identically `1`.
-/

namespace Cochrane.TwoPeriodModel.TidyR6Regression

open MeasureTheory Filter Topology Cochrane.TwoPeriodModel.TwoPeriod
open Cochrane.TwoPeriodModel.ActivePassive

/-! ### Least squares in a finite sample -/

/-- Cochrane (2023), p. 18: the sum of squared residuals of the regression
`y_i = a + b x_i + u_i` in a sample of size `n`. -/
noncomputable def ssr {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ) : ℝ := ∑ i, (y i - a - b * x i) ^ 2

/-- Cochrane (2023), p. 18: `(a, b)` is an ordinary-least-squares estimate: it minimises the sum
of squared residuals. -/
def IsOLS {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ) : Prop := ∀ a' b', ssr x y a b ≤ ssr x y a' b'

/-- Cochrane (2023), p. 18: the sample mean. -/
noncomputable def mean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

/-- Cochrane (2023), p. 18: the textbook OLS slope `∑(x − x̄)(y − ȳ)/∑(x − x̄)²`. -/
noncomputable def olsSlope {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (∑ i, (x i - mean x) * (y i - mean y)) / ∑ i, (x i - mean x) ^ 2

/-- Cochrane (2023), p. 18: the sum of squared residuals is nonnegative. -/
theorem ssr_nonneg {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ) : 0 ≤ ssr x y a b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Cochrane (2023), p. 18 (**the regression estimates `γ = 1`**): when the data satisfy the
equilibrium relation `y_i = x_i` (`s₁ = B₀/P₁`) and the regressor varies in the sample, the
OLS estimates are exactly `a = 0`, `b = 1`. -/
theorem ols_iff {n : ℕ} {x y : Fin n → ℝ} (hy : y = x) (hvar : ∃ i j, x i ≠ x j) (a b : ℝ) :
    IsOLS x y a b ↔ a = 0 ∧ b = 1 := by
  subst hy
  have h01 : ssr y y 0 1 = 0 := by simp [ssr]
  constructor
  · intro h
    have hle := h 0 1
    rw [h01] at hle
    have hz : ∀ i, y i - a - b * y i = 0 := fun i => by
      have h0 : ssr y y a b = 0 := le_antisymm hle (ssr_nonneg _ _ _ _)
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (y i - a - b * y i))).mp
        h0 i (Finset.mem_univ i)
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    obtain ⟨i, j, hij⟩ := hvar
    have hi := hz i
    have hj := hz j
    have hb : b = 1 := by
      have : (1 - b) * (y i - y j) = 0 := by linear_combination hi - hj
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd (sub_eq_zero.mp h) hij
    refine ⟨?_, hb⟩
    rw [hb] at hi
    linarith
  · rintro ⟨rfl, rfl⟩ a' b'
    rw [h01]
    exact ssr_nonneg _ _ _ _

/-- Cochrane (2023), p. 18: with equilibrium data `y_i = x_i` and a varying regressor, the
textbook OLS slope is `1`. -/
theorem olsSlope_eq_one {n : ℕ} {x y : Fin n → ℝ} (hy : y = x) (hvar : ∃ i j, x i ≠ x j) :
    olsSlope x y = 1 := by
  subst hy
  unfold olsSlope
  have hpos : 0 < ∑ i, (y i - mean y) ^ 2 := by
    obtain ⟨i, j, hij⟩ := hvar
    by_contra hle
    push Not at hle
    have h0 : ∑ i, (y i - mean y) ^ 2 = 0 :=
      le_antisymm hle (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hz : ∀ k, y k - mean y = 0 := fun k => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (y k - mean y))).mp h0 k
        (Finset.mem_univ k)
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    exact hij (by linarith [hz i, hz j])
  rw [div_eq_one_iff_eq hpos.ne']
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Cochrane (2023), pp. 18–19: in every two-period equilibrium (any surplus rule), the
observation `(B₀/P₁, s₁)` lies on the line `s₁ = 0 + 1 · B₀/P₁`: (1.4) is an exact identity in
the data. -/
theorem equilibrium_data {B0 P1 s1 : ℝ} (h : B0 / P1 = s1) : s1 = 0 + 1 * (B0 / P1) := by
  rw [h]; ring

/-- Cochrane (2023), pp. 18–19 (**consistency, precisely**): let the data come from equilibria
of the `γ`-rule `s₁ = B₀/P₁* + γ(B₀/P₁ − B₀/P₁*)` (each observation an equilibrium
`B₀/P₁ = s₁`), with samples of size `n_k` in which `B₀/P₁` varies. Then the OLS slope estimate
of the regression `s₁ = a + γ(B₀/P₁) + u₁` is `1` in every sample, so the sequence of estimates
converges to the structural `γ` iff `γ = 1`. -/
theorem ols_consistent_iff {γ : ℝ} {n : ℕ → ℕ} {B0 P1 Pstar : (k : ℕ) → Fin (n k) → ℝ}
    (heq : ∀ k i, 0 < P1 k i ∧ B0 k i / P1 k i = gammaRule 1 γ (B0 k i) (Pstar k i) (P1 k i))
    (hvar : ∀ k, ∃ i j, B0 k i / P1 k i ≠ B0 k j / P1 k j) {b : ℕ → ℝ}
    (hb : ∀ k, ∃ a, IsOLS (fun i => B0 k i / P1 k i)
      (fun i => gammaRule 1 γ (B0 k i) (Pstar k i) (P1 k i)) a (b k)) :
    Tendsto b atTop (𝓝 γ) ↔ γ = 1 := by
  have hb1 : ∀ k, b k = 1 := by
    intro k
    obtain ⟨a, ha⟩ := hb k
    have hy : (fun i => gammaRule 1 γ (B0 k i) (Pstar k i) (P1 k i)) =
        fun i => B0 k i / P1 k i := funext fun i => (heq k i).2.symm
    exact ((ols_iff hy (hvar k) a (b k)).mp ha).2
  have hconst : b = fun _ => 1 := funext hb1
  rw [hconst]
  constructor
  · intro h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  · rintro rfl
    exact tendsto_const_nhds

/-- Cochrane (2023), p. 19 (**`γ` is not identified, in the sample**): in data from equilibria of
a `γ`-rule with `α = 1` and `γ ≠ 1` (so `P₁ = P₁*` and the regressor `B₀/P₁ − B₀/P₁*` is zero),
every coefficient `g` attains the least sum of squares `0` of the regression
`s₁ = α(B₀/P₁*) + g(B₀/P₁ − B₀/P₁*) + u₁` (with `α = 1`). -/
theorem gamma_not_identified_sample {γ : ℝ} (hγ : γ ≠ 1) {n : ℕ} {B0 P1 Pstar : Fin n → ℝ}
    (hB : ∀ i, 0 < B0 i) (hPs : ∀ i, 0 < Pstar i)
    (heq : ∀ i, 0 < P1 i ∧ B0 i / P1 i = gammaRule 1 γ (B0 i) (Pstar i) (P1 i)) (g : ℝ) :
    ∑ i, (gammaRule 1 γ (B0 i) (Pstar i) (P1 i) - 1 * (B0 i / Pstar i) -
      g * (B0 i / P1 i - B0 i / Pstar i)) ^ 2 = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨Q, -, hu⟩ := (gamma_rule_determinate_iff (hB i) (hPs i)).mpr hγ
  have hP : P1 i = Pstar i := (hu _ (heq i)).trans (hu _ ⟨hPs i, by simp [gammaRule]⟩).symm
  rw [hP]
  simp [gammaRule]

/-! ### Least squares in the population -/

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Cochrane (2023), p. 18, in the population: the mean squared residual
`E[(Y − a − bX)²]` of the regression of `Y` on a constant and `X`. -/
noncomputable def popSSR (X Y : Ω → ℝ) (a b : ℝ) : ℝ := ∫ ω, (Y ω - a - b * X ω) ^ 2 ∂μ

/-- Cochrane (2023), p. 18, in the population: `(a, b)` are the population least-squares
coefficients. -/
def IsPopOLS (X Y : Ω → ℝ) (a b : ℝ) : Prop := ∀ a' b', popSSR μ X Y a b ≤ popSSR μ X Y a' b'

/-- Cochrane (2023), p. 18 (**the population regression coefficient is `1`**): on a probability
space, if `Y = X` almost surely (the equilibrium relation `s₁ = B₀/P₁`), `X` and `X²` are
integrable, and `X` is not almost surely constant, then the population least-squares
coefficients are exactly `a = 0`, `b = 1`. -/
theorem popOLS_iff [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hYX : Y =ᵐ[μ] X)
    (hX : Integrable X μ) (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    (hnc : ∀ c : ℝ, ¬ X =ᵐ[μ] fun _ => c) (a b : ℝ) :
    IsPopOLS μ X Y a b ↔ a = 0 ∧ b = 1 := by
  have hint : ∀ a b : ℝ, Integrable (fun ω => (Y ω - a - b * X ω) ^ 2) μ := by
    intro a b
    have h1 : Integrable (fun ω => (1 - b) ^ 2 * X ω ^ 2 - 2 * a * (1 - b) * X ω + a ^ 2) μ :=
      ((hX2.const_mul _).sub (hX.const_mul _)).add (integrable_const _)
    refine h1.congr ?_
    filter_upwards [hYX] with ω h
    rw [h]; ring
  have h01 : popSSR μ X Y 0 1 = 0 := by
    unfold popSSR
    rw [integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
      (hint 0 1)]
    filter_upwards [hYX] with ω h
    simp [h]
  have hnn : ∀ a b, 0 ≤ popSSR μ X Y a b := fun _ _ =>
    integral_nonneg fun _ => sq_nonneg _
  constructor
  · intro h
    have hle := h 0 1
    rw [h01] at hle
    have h0 : popSSR μ X Y a b = 0 := le_antisymm hle (hnn a b)
    have hz := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun _ => sq_nonneg _) (hint a b)).mp h0
    have hlin : ∀ᵐ ω ∂μ, (1 - b) * X ω = a := by
      filter_upwards [hz, hYX] with ω h1 h2
      simp only [Pi.zero_apply] at h1
      have := pow_eq_zero_iff two_ne_zero |>.mp h1
      rw [h2] at this
      linarith
    have hb : b = 1 := by
      by_contra hb
      have hne : (1 - b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
      refine hnc (a / (1 - b)) ?_
      filter_upwards [hlin] with ω h
      field_simp
      linarith
    refine ⟨?_, hb⟩
    have ha : ∀ᵐ ω ∂μ, a = 0 := by
      filter_upwards [hlin] with ω h
      rw [hb] at h
      linarith
    obtain ⟨ω, hω⟩ := ha.exists
    exact hω
  · rintro ⟨rfl, rfl⟩ a' b'
    rw [h01]
    exact hnn a' b'

/-- Cochrane (2023), pp. 18–19, in the population: in every two-period equilibrium the
observables satisfy `s₁ = B₀/P₁` exactly (`Valuation1`), so with `B₀/P₁` integrable, square
integrable and not almost surely constant the population regression of `s₁` on a constant and
`B₀/P₁` has coefficients exactly `(0, 1)`, whatever the surplus rule. -/
theorem popOLS_equilibrium [IsProbabilityMeasure μ] {B0 P1 s1 : Ω → ℝ}
    (hv : Valuation1 B0 P1 s1) (hX : Integrable (B0 / P1) μ)
    (hX2 : Integrable (fun ω => (B0 / P1) ω ^ 2) μ)
    (hnc : ∀ c : ℝ, ¬ (B0 / P1) =ᵐ[μ] fun _ => c) (a b : ℝ) :
    IsPopOLS μ (B0 / P1) s1 a b ↔ a = 0 ∧ b = 1 :=
  popOLS_iff μ (Eventually.of_forall fun ω => (congrFun hv ω).symm) hX hX2 hnc a b

/-- Cochrane (2023), p. 19 (**`γ` is not identified, in the population**): if the surplus
follows a `γ`-rule with `α = 1`, `γ ≠ 1`, positive `B₀` and target `P₁*`, and `P₁` is an
equilibrium state by state, then for every `g` the regression
`s₁ = 1 · (B₀/P₁*) + g(B₀/P₁ − B₀/P₁*) + u₁` has mean squared residual `0`, the least possible:
every `g` is a population least-squares coefficient. -/
theorem gamma_not_identified_pop {γ : ℝ} (hγ : γ ≠ 1) {B0 P1 Pstar : Ω → ℝ}
    (hB : ∀ ω, 0 < B0 ω) (hPs : ∀ ω, 0 < Pstar ω) (hP1 : ∀ ω, 0 < P1 ω)
    (hv : Valuation1 B0 P1 (fun ω => gammaRule 1 γ (B0 ω) (Pstar ω) (P1 ω))) (g : ℝ) :
    ∫ ω, (gammaRule 1 γ (B0 ω) (Pstar ω) (P1 ω) - 1 * (B0 ω / Pstar ω) -
      g * (B0 ω / P1 ω - B0 ω / Pstar ω)) ^ 2 ∂μ = 0 := by
  have hP : P1 = Pstar := ((gamma_rule_random hB hPs).1 hγ P1 hP1).mp hv
  subst hP
  simp [gammaRule]

end Cochrane.TwoPeriodModel.TidyR6Regression
