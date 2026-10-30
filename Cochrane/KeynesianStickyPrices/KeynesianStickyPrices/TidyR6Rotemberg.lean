/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6PriceSetting
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Rotemberg price setter: smooth payoff, concavity region, first-order conditions

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1, p. 118: "The Phillips
curve (5.2) comes from the first-order condition for monopolistically-competitive price setters,
facing costs of changing prices", and eq. (17.17), p. 407. The book does not write the
price-setting problem down (it refers to King (2000), Woodford (2003) and Galí (2015)); of the two
specifications it names, this module takes the costs of changing prices (Rotemberg): a
monopolistically competitive producer facing CES demand `y = Ye^{−εq}` (elasticity `ε > 1`, `q`
its log relative price) earns, in utility units at date `t`,

`Φ(q_t, q_{t−1}; A_t, B_t, π_t) =
A_te^{(1−ε)q_t} − B_te^{−ηq_t} − (φ/2)(e^{q_t − q_{t−1} + π_t} − 1)²`

(`rotPay`): sales revenue valued at marginal utility (`A_t = u′(Y_t)Y_t`), the disutility of
producing (`B_te^{−ηq}`, `η = ε(1 + ϕ)` for the disutility `y^{1+ϕ}/(1 + ϕ)`), and the quadratic
cost of changing its nominal price, `p_t/p_{t−1} = e^{q_t − q_{t−1} + π_t}`.

## Main results

* `rot_smooth`: the payoff and its partial derivatives `rotD1`, `rotD2` satisfy
  `TidyR6PriceSetting.Smooth`, so `TidyR6PriceSetting.foc_of_optimal` applies: an optimal plan
  satisfies the first-order condition (necessity holds over **all** plans).
* `not_tangentConcave` (**counterexample**): the payoff is not concave in `(q_t, q_{t−1})`, for any
  `ε ≠ 1`, so the global sufficiency theorem `TidyR6PriceSetting.optimal_iff_foc` does not apply
  (and global sufficiency is false: module TidyR6RotembergGlobal gives a symmetric equilibrium
  satisfying the first-order condition in which charging the aggregate price is not optimal).
* `rot_supergrad` (the corrected statement): the payoff is concave on the region `rotRegion`
  where the static profit is concave (`(ε − 1)²A e^{(1−ε+η)q} ≤ η²B`) and the price is not cut
  by more than half (`e^{q_t − q_{t−1} + π_t} ≥ 1/2`); `tangent_of_antitoneOn` and
  `antitoneOn_of_deriv_nonpos'` are the one-variable tools.
* `RPlan`: uniformly bounded plans staying in the region; `rplan_perturb`: a plan inside the
  region with a uniform margin has all small one-date perturbations in `RPlan`.
* `optimal_iff_foc_region`: for such a plan, optimality among plans in the region is
  **equivalent** to the first-order condition at every date.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6Rotemberg

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6PriceSetting

/-! ### One-variable concavity tools -/

/-- Cochrane (2023), p. 118 (second-order conditions): a function whose derivative is
nonpositive on an order-connected set is antitone there. -/
theorem antitoneOn_of_deriv_nonpos' {g g' : ℝ → ℝ} {D : Set ℝ} (hD : D.OrdConnected)
    (hg : ∀ x, HasDerivAt g (g' x) x) (h : ∀ x ∈ D, g' x ≤ 0) : AntitoneOn g D := by
  intro x hx y hy hxy
  rcases hxy.lt_or_eq with hlt | heq
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope g g' hlt
      (continuous_iff_continuousAt.2 fun z => (hg z).continuousAt).continuousOn
      fun z _ => hg z
    have hcD : c ∈ D := hD.out hx hy ⟨hc.1.le, hc.2.le⟩
    have h1 := h c hcD
    rw [hcs, div_le_iff₀ (by linarith), zero_mul] at h1
    linarith
  · rw [heq]

/-- Cochrane (2023), p. 118 (second-order conditions): a differentiable function whose
derivative is antitone on an order-connected set lies below its tangent lines there,
`f(a′) ≤ f(a) + f′(a)(a′ − a)`. -/
theorem tangent_of_antitoneOn {f f' : ℝ → ℝ} {D : Set ℝ} (hD : D.OrdConnected)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hanti : AntitoneOn f' D) {a a' : ℝ} (ha : a ∈ D)
    (ha' : a' ∈ D) : f a' ≤ f a + f' a * (a' - a) := by
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (continuous_iff_continuousAt.2 fun z => (hf z).continuousAt).continuousOn
      fun z _ => hf z
    have hcD : c ∈ D := hD.out ha ha' ⟨hc.1.le, hc.2.le⟩
    have h1 : f' c ≤ f' a := hanti ha hcD hc.1.le
    rw [hcs, div_le_iff₀ (by linarith)] at h1
    linarith
  · subst heq
    simp
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hgt
      (continuous_iff_continuousAt.2 fun z => (hf z).continuousAt).continuousOn
      fun z _ => hf z
    have hcD : c ∈ D := hD.out ha' ha ⟨hc.1.le, hc.2.le⟩
    have h1 : f' a ≤ f' c := hanti hcD ha hc.2.le
    rw [hcs, le_div_iff₀ (by linarith)] at h1
    nlinarith

/-! ### The payoff and its derivatives -/

/-- Cochrane (2023), p. 118 ("costs of changing prices"): the Rotemberg payoff
`A e^{(1−ε)a} − B e^{−ηa} − (φ/2)(e^{a − b + π} − 1)²` with data `v = (A, B, π)`. -/
noncomputable def rotPay (ε η φ : ℝ) (a b : ℝ) (v : ℝ × ℝ × ℝ) : ℝ :=
  v.1 * Real.exp ((1 - ε) * a) - v.2.1 * Real.exp (-(η * a)) -
    φ / 2 * (Real.exp (a - b + v.2.2) - 1) ^ 2

/-- Cochrane (2023), p. 118: the derivative of the payoff in this period's price,
`(1 − ε)Ae^{(1−ε)a} + ηBe^{−ηa} − φ(e^d − 1)e^d`, `d = a − b + π`. -/
noncomputable def rotD1 (ε η φ : ℝ) (a b : ℝ) (v : ℝ × ℝ × ℝ) : ℝ :=
  v.1 * (1 - ε) * Real.exp ((1 - ε) * a) + v.2.1 * η * Real.exp (-(η * a)) -
    φ * (Real.exp (a - b + v.2.2) - 1) * Real.exp (a - b + v.2.2)

/-- Cochrane (2023), p. 118: the derivative of the payoff in last period's price,
`φ(e^d − 1)e^d`. -/
noncomputable def rotD2 (φ : ℝ) (a b : ℝ) (v : ℝ × ℝ × ℝ) : ℝ :=
  φ * (Real.exp (a - b + v.2.2) - 1) * Real.exp (a - b + v.2.2)

/-- Cochrane (2023), p. 118: `rotD1` is the partial derivative in `a`. -/
theorem hasDerivAt_rot_a (ε η φ a b : ℝ) (v : ℝ × ℝ × ℝ) :
    HasDerivAt (fun a => rotPay ε η φ a b v) (rotD1 ε η φ a b v) a := by
  have h1 : HasDerivAt (fun a => Real.exp ((1 - ε) * a)) (Real.exp ((1 - ε) * a) * (1 - ε)) a :=
    ((hasDerivAt_id a).const_mul (1 - ε)).exp.congr_deriv (by simp)
  have h2 : HasDerivAt (fun a => Real.exp (-(η * a))) (Real.exp (-(η * a)) * (-η)) a :=
    (((hasDerivAt_id a).const_mul η).neg).exp.congr_deriv (by simp)
  have h3 : HasDerivAt (fun a => Real.exp (a - b + v.2.2)) (Real.exp (a - b + v.2.2)) a := by
    have := (((hasDerivAt_id a).sub_const b).add_const v.2.2).exp
    simpa using this
  have h4 := (h3.sub_const 1).pow 2
  have h := ((h1.const_mul v.1).sub (h2.const_mul v.2.1)).sub (h4.const_mul (φ / 2))
  refine h.congr_deriv ?_
  simp only [rotD1]
  push_cast
  ring

/-- Cochrane (2023), p. 118: `rotD2` is the partial derivative in `b`. -/
theorem hasDerivAt_rot_b (ε η φ a b : ℝ) (v : ℝ × ℝ × ℝ) :
    HasDerivAt (fun b => rotPay ε η φ a b v) (rotD2 φ a b v) b := by
  have h3 : HasDerivAt (fun b => Real.exp (a - b + v.2.2)) (Real.exp (a - b + v.2.2) * (-1)) b :=
    ((((hasDerivAt_id b).const_sub a).add_const v.2.2).exp).congr_deriv (by simp)
  have h4 := (h3.sub_const 1).pow 2
  have h := (h4.const_mul (φ / 2)).const_sub
    (v.1 * Real.exp ((1 - ε) * a) - v.2.1 * Real.exp (-(η * a)))
  refine h.congr_deriv ?_
  simp only [rotD2]
  push_cast
  ring

/-- Cochrane (2023), p. 118: the Rotemberg payoff is smooth (`TidyR6PriceSetting.Smooth`). -/
theorem rot_smooth (ε η φ : ℝ) : Smooth (rotPay ε η φ) (rotD1 ε η φ) (rotD2 φ) := by
  refine ⟨hasDerivAt_rot_a ε η φ, hasDerivAt_rot_b ε η φ, ?_, ?_, ?_⟩ <;>
    · simp only [rotPay, rotD1, rotD2]
      fun_prop

/-! ### The payoff is not concave -/

/-- Cochrane (2023), p. 118, **counterexample**: for every `ε ≠ 1` the Rotemberg payoff is not
concave in `(q_t, q_{t−1})`: with data `(A, B, π) = (1, 0, 0)`, moving from `(0, 0)` to `(1, 1)`
(no price change) gives `e^{1−ε}`, above the tangent value `2 − ε`. Global sufficiency of the
first-order condition therefore cannot be obtained from concavity. -/
theorem not_tangentConcave {ε : ℝ} (hε : ε ≠ 1) (η φ : ℝ) :
    ¬ TangentConcave (rotPay ε η φ) (rotD1 ε η φ) (rotD2 φ) := by
  intro h
  have h1 := h 0 0 1 1 (1, 0, 0)
  simp only [rotPay, rotD1, rotD2, mul_zero, mul_one, sub_self, add_zero, Real.exp_zero,
    zero_mul, sub_zero, one_mul, neg_zero] at h1
  have h2 := Real.add_one_lt_exp (show 1 - ε ≠ 0 from sub_ne_zero.2 (Ne.symm hε))
  norm_num at h1
  linarith

/-! ### The concavity region -/

/-- Cochrane (2023), p. 118: the static profit is concave at the log relative price `a`,
`(ε − 1)²A e^{(1−ε+η)a} ≤ η²B`. -/
def staticOK (ε η : ℝ) (v : ℝ × ℝ × ℝ) (a : ℝ) : Prop :=
  (ε - 1) ^ 2 * v.1 * Real.exp ((1 - ε + η) * a) ≤ η ^ 2 * v.2.1

/-- Cochrane (2023), p. 118: the price is not cut by more than half, `e^{a − b + π} ≥ 1/2`. -/
def costOK (v : ℝ × ℝ × ℝ) (a b : ℝ) : Prop := 1 / 2 ≤ Real.exp (a - b + v.2.2)

/-- Cochrane (2023), p. 118: the region on which the Rotemberg payoff is concave. -/
def rotRegion (ε η : ℝ) (v : ℝ × ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | staticOK ε η v p.1 ∧ costOK v p.1 p.2}

/-- Cochrane (2023), p. 118: the static-concavity set is a half-line, hence order-connected
(`A ≥ 0`, `1 − ε + η ≥ 0`). -/
theorem staticOK_ordConnected {ε η : ℝ} (hη : 0 ≤ 1 - ε + η) {v : ℝ × ℝ × ℝ} (hA : 0 ≤ v.1) :
    {a | staticOK ε η v a}.OrdConnected := by
  refine ⟨fun x _ y hy z hz => ?_⟩
  have h1 : Real.exp ((1 - ε + η) * z) ≤ Real.exp ((1 - ε + η) * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz.2 hη)
  have h2 : 0 ≤ (ε - 1) ^ 2 * v.1 := mul_nonneg (sq_nonneg _) hA
  exact (mul_le_mul_of_nonneg_left h1 h2).trans hy

/-- Cochrane (2023), p. 118: the static profit `Ae^{(1−ε)a} − Be^{−ηa}` lies below its tangent
lines on the static-concavity set. -/
theorem static_tangent {ε η : ℝ} (hη : 0 ≤ 1 - ε + η) {v : ℝ × ℝ × ℝ} (hA : 0 ≤ v.1)
    {a a' : ℝ} (ha : staticOK ε η v a) (ha' : staticOK ε η v a') :
    v.1 * Real.exp ((1 - ε) * a') - v.2.1 * Real.exp (-(η * a')) ≤
      v.1 * Real.exp ((1 - ε) * a) - v.2.1 * Real.exp (-(η * a)) +
        (v.1 * (1 - ε) * Real.exp ((1 - ε) * a) + v.2.1 * η * Real.exp (-(η * a))) *
          (a' - a) := by
  set f : ℝ → ℝ := fun a => v.1 * Real.exp ((1 - ε) * a) - v.2.1 * Real.exp (-(η * a))
  set f' : ℝ → ℝ := fun a =>
    v.1 * (1 - ε) * Real.exp ((1 - ε) * a) + v.2.1 * η * Real.exp (-(η * a))
  set f'' : ℝ → ℝ := fun a =>
    v.1 * (1 - ε) ^ 2 * Real.exp ((1 - ε) * a) - v.2.1 * η ^ 2 * Real.exp (-(η * a))
  have e1 : ∀ c : ℝ, ∀ x, HasDerivAt (fun a => Real.exp (c * a)) (Real.exp (c * x) * c) x :=
    fun c x => ((hasDerivAt_id x).const_mul c).exp.congr_deriv (by simp)
  have hf : ∀ x, HasDerivAt f (f' x) x := fun x => by
    have h := ((e1 (1 - ε) x).const_mul v.1).sub ((e1 (-η) x).const_mul v.2.1)
    simp only [neg_mul] at h
    exact h.congr_deriv (by simp only [f']; ring)
  have hf' : ∀ x, HasDerivAt f' (f'' x) x := fun x => by
    have h := ((e1 (1 - ε) x).const_mul (v.1 * (1 - ε))).add
      ((e1 (-η) x).const_mul (v.2.1 * η))
    simp only [neg_mul] at h
    exact h.congr_deriv (by simp only [f'']; ring)
  have hD := staticOK_ordConnected hη hA
  have hneg : ∀ x ∈ {a | staticOK ε η v a}, f'' x ≤ 0 := by
    intro x hx
    have hx' : (ε - 1) ^ 2 * v.1 * Real.exp ((1 - ε + η) * x) ≤ η ^ 2 * v.2.1 := hx
    have hsplit : Real.exp ((1 - ε + η) * x) = Real.exp ((1 - ε) * x) * Real.exp (η * x) := by
      rw [← Real.exp_add]
      ring_nf
    have hpos := Real.exp_pos (η * x)
    have hinv : Real.exp (-(η * x)) * Real.exp (η * x) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [hsplit] at hx'
    have : f'' x * Real.exp (η * x) ≤ 0 := by
      have key : f'' x * Real.exp (η * x) = (ε - 1) ^ 2 * v.1 *
          (Real.exp ((1 - ε) * x) * Real.exp (η * x)) - η ^ 2 * v.2.1 := by
        simp only [f'']
        linear_combination (-(v.2.1 * η ^ 2)) * hinv
      linarith
    nlinarith
  have hanti := antitoneOn_of_deriv_nonpos' hD hf' hneg
  exact tangent_of_antitoneOn hD hf hanti ha ha'

/-- Cochrane (2023), p. 118: the adjustment cost `−(φ/2)(e^d − 1)²` lies below its tangent lines
on `e^d ≥ 1/2` (`φ ≥ 0`). -/
theorem cost_tangent {φ : ℝ} (hφ : 0 ≤ φ) {d d' : ℝ} (hd : 1 / 2 ≤ Real.exp d)
    (hd' : 1 / 2 ≤ Real.exp d') :
    -(φ / 2 * (Real.exp d' - 1) ^ 2) ≤ -(φ / 2 * (Real.exp d - 1) ^ 2) +
      -(φ * (Real.exp d - 1) * Real.exp d) * (d' - d) := by
  set h : ℝ → ℝ := fun d => -(φ / 2 * (Real.exp d - 1) ^ 2)
  set h' : ℝ → ℝ := fun d => -(φ * (Real.exp d - 1) * Real.exp d)
  set h'' : ℝ → ℝ := fun d => -(φ * (2 * Real.exp d - 1) * Real.exp d)
  have hh : ∀ x, HasDerivAt h (h' x) x := fun x => by
    have := (((Real.hasDerivAt_exp x).sub_const 1).pow 2).const_mul (φ / 2) |>.neg
    exact this.congr_deriv (by simp only [h']; push_cast; ring)
  have hh' : ∀ x, HasDerivAt h' (h'' x) x := fun x => by
    have := ((((Real.hasDerivAt_exp x).sub_const 1).const_mul φ).mul
      (Real.hasDerivAt_exp x)).neg
    exact this.congr_deriv (by simp only [h'']; ring)
  have hD : {d : ℝ | 1 / 2 ≤ Real.exp d}.OrdConnected :=
    ⟨fun x hx _ _ z hz => hx.trans (Real.exp_le_exp.2 hz.1)⟩
  have hneg : ∀ x ∈ {d : ℝ | 1 / 2 ≤ Real.exp d}, h'' x ≤ 0 := by
    intro x hx
    have hx' : (1 : ℝ) / 2 ≤ Real.exp x := hx
    have := Real.exp_pos x
    simp only [h'']
    have : 0 ≤ φ * (2 * Real.exp x - 1) := mul_nonneg hφ (by linarith)
    nlinarith
  exact tangent_of_antitoneOn hD hh (antitoneOn_of_deriv_nonpos' hD hh' hneg) hd hd'

/-- Cochrane (2023), p. 118 (the corrected statement): on `rotRegion` the Rotemberg payoff is
concave, `Φ(a′, b′) ≤ Φ(a, b) + Φ₁(a, b)(a′ − a) + Φ₂(a, b)(b′ − b)` for `(a, b)` and `(a′, b′)`
in the region (`A ≥ 0`, `φ ≥ 0`, `1 − ε + η ≥ 0`). -/
theorem rot_supergrad {ε η φ : ℝ} (hη : 0 ≤ 1 - ε + η) (hφ : 0 ≤ φ) {v : ℝ × ℝ × ℝ}
    (hA : 0 ≤ v.1) {a b a' b' : ℝ} (h : (a, b) ∈ rotRegion ε η v)
    (h' : (a', b') ∈ rotRegion ε η v) :
    rotPay ε η φ a' b' v ≤ rotPay ε η φ a b v + rotD1 ε η φ a b v * (a' - a) +
      rotD2 φ a b v * (b' - b) := by
  have h1 := static_tangent hη hA h.1 h'.1
  have h2 := cost_tangent hφ h.2 h'.2
  simp only [rotPay, rotD1, rotD2]
  have e : a' - b' + v.2.2 - (a - b + v.2.2) = (a' - a) - (b' - b) := by ring
  rw [e] at h2
  nlinarith

/-! ### Plans in the region -/

variable {Ω : Type*} [MeasurableSpace Ω]

variable (S : MeasExpectationSystem Ω) in
/-- Cochrane (2023), p. 118: a uniformly bounded plan that stays in the concavity region at every
date, almost surely. -/
def RPlan (ε η : ℝ) (θ : ℕ → Ω → ℝ × ℝ × ℝ) (q0 : Ω → ℝ) (q : ℕ → Ω → ℝ) : Prop :=
  UPlan S q ∧ ∀ t, ∀ᵐ ω ∂S.μ, (q t ω, lag q0 q t ω) ∈ rotRegion ε η (θ t ω)

variable (S : MeasExpectationSystem Ω) in
/-- Cochrane (2023), p. 118: the plan is inside the region with the uniform margin `m`:
`(ε − 1)²Ae^{(1−ε+η)q_t} ≤ e^{−m}η²B` and `e^{q_t − q_{t−1} + π_t} ≥ e^m/2`. -/
def Margin (ε η : ℝ) (θ : ℕ → Ω → ℝ × ℝ × ℝ) (q0 : Ω → ℝ) (q : ℕ → Ω → ℝ) (m : ℝ) : Prop :=
  ∀ t, ∀ᵐ ω ∂S.μ,
    (ε - 1) ^ 2 * (θ t ω).1 * Real.exp ((1 - ε + η) * q t ω) ≤
        Real.exp (-m) * (η ^ 2 * (θ t ω).2.1) ∧
      Real.exp m / 2 ≤ Real.exp (q t ω - lag q0 q t ω + (θ t ω).2.2)

/-- Cochrane (2023), p. 118: a point with a margin stays in the region after a shift `(da, db)`
with `(1 − ε + η)da ≤ m` and `|da − db| ≤ m` (`A ≥ 0`). -/
theorem region_of_shift {ε η m : ℝ} {v : ℝ × ℝ × ℝ} (hA : 0 ≤ v.1) {a b : ℝ}
    (h1 : (ε - 1) ^ 2 * v.1 * Real.exp ((1 - ε + η) * a) ≤ Real.exp (-m) * (η ^ 2 * v.2.1))
    (h2 : Real.exp m / 2 ≤ Real.exp (a - b + v.2.2)) {da db : ℝ}
    (hda : (1 - ε + η) * da ≤ m) (hd : |da - db| ≤ m) :
    (a + da, b + db) ∈ rotRegion ε η v := by
  have hmm : Real.exp (-m) * Real.exp m = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos m
  refine ⟨?_, ?_⟩
  · have hexp : Real.exp ((1 - ε + η) * (a + da)) ≤ Real.exp ((1 - ε + η) * a) * Real.exp m := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    have hk : 0 ≤ (ε - 1) ^ 2 * v.1 := mul_nonneg (sq_nonneg _) hA
    have h3 := mul_le_mul_of_nonneg_left hexp hk
    have h4 := mul_le_mul_of_nonneg_right h1 hpos.le
    change (ε - 1) ^ 2 * v.1 * Real.exp ((1 - ε + η) * (a + da)) ≤ η ^ 2 * v.2.1
    have e : Real.exp (-m) * (η ^ 2 * v.2.1) * Real.exp m = η ^ 2 * v.2.1 := by
      linear_combination (η ^ 2 * v.2.1) * hmm
    nlinarith
  · change 1 / 2 ≤ Real.exp (a + da - (b + db) + v.2.2)
    have hexp : Real.exp (a - b + v.2.2) * Real.exp (-m) ≤
        Real.exp (a + da - (b + db) + v.2.2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := neg_abs_le (da - db)
      linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-m)).le
    have e : Real.exp m / 2 * Real.exp (-m) = 1 / 2 := by
      linear_combination (1 / 2 : ℝ) * hmm
    linarith

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: last period's price after a perturbation at `t`, seen at `t + 1`. -/
theorem lag_perturb_succ (q0 : Ω → ℝ) (q : ℕ → Ω → ℝ) (z : Ω → ℝ) (t : ℕ) (s : ℝ) :
    lag q0 (perturb q z t s) (t + 1) = fun ω => q t ω + s * z ω :=
  perturb_self q z t s

/-- Cochrane (2023), p. 118: a uniformly bounded plan in the region with a positive margin has
every small one-date perturbation (by a bounded variable known at `t`) in `RPlan` (`A ≥ 0`
almost surely at every date, `1 − ε + η ≥ 0`). -/
theorem rplan_perturb {S : MeasExpectationSystem Ω} {ε η m : ℝ} (hη : 0 ≤ 1 - ε + η)
    (hm : 0 < m) {θ : ℕ → Ω → ℝ × ℝ × ℝ} (hA : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ (θ t ω).1)
    {q0 : Ω → ℝ} {q : ℕ → Ω → ℝ} (hq : UPlan S q) (hM : Margin S ε η θ q0 q m) {t : ℕ}
    {z : Ω → ℝ} (hz : StronglyMeasurable[S.𝓕 t] z) (hzb : BddAt S z) :
    ∀ᶠ s in 𝓝 (0 : ℝ), RPlan S ε η θ q0 (perturb q z t s) := by
  obtain ⟨Kz, hKz0, hKz⟩ := hzb.exists_pos
  set c := 2 - ε + η with hc
  have hc0 : 0 < c := by linarith
  have hδ : 0 < m / (c * Kz) := div_pos hm (mul_pos hc0 hKz0)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with s hs
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, lt_div_iff₀ (mul_pos hc0 hKz0)] at hs
  refine ⟨uplan_perturb hq hz ⟨Kz, hKz⟩ s, fun n => ?_⟩
  have hsz : ∀ᵐ ω ∂S.μ, |s * z ω| * c ≤ m := by
    filter_upwards [hKz] with ω h
    rw [abs_mul]
    nlinarith [abs_nonneg s, abs_nonneg (z ω)]
  have hsz1 : ∀ᵐ ω ∂S.μ, |s * z ω| ≤ m := hsz.mono fun ω h => by
    nlinarith [abs_nonneg (s * z ω)]
  have hsz2 : ∀ᵐ ω ∂S.μ, (1 - ε + η) * (s * z ω) ≤ m := hsz.mono fun ω h => by
    nlinarith [abs_nonneg (s * z ω), le_abs_self (s * z ω)]
  by_cases hn : n = t
  · subst hn
    rw [perturb_self, lag_perturb_ne (show n ≠ n + 1 by omega)]
    filter_upwards [hM n, hA n, hsz1, hsz2] with ω h hAω h1 h2
    have := region_of_shift hAω h.1 h.2 h2 (db := 0) (by simpa using h1)
    simpa using this
  · by_cases hn1 : n = t + 1
    · subst hn1
      rw [perturb_ne hn, lag_perturb_succ]
      filter_upwards [hM (t + 1), hA (t + 1), hsz1] with ω h hAω h1
      have := region_of_shift hAω h.1 h.2 (da := 0) (db := s * z ω) (by simp [hm.le])
        (by simpa [abs_neg] using h1)
      simpa [lag] using this
    · rw [perturb_ne hn, lag_perturb_ne hn1]
      filter_upwards [hM n, hA n] with ω h hAω
      have := region_of_shift hAω h.1 h.2 (da := 0) (db := 0) (by simp [hm.le])
        (by simp [hm.le])
      simpa using this

/-- Cochrane (2023), p. 118: a plan with a margin `m ≥ 0` is in the region. -/
theorem inRegion_of_margin {S : MeasExpectationSystem Ω} {ε η m : ℝ} (hm : 0 ≤ m)
    {θ : ℕ → Ω → ℝ × ℝ × ℝ} (hA : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ (θ t ω).1) {q0 : Ω → ℝ}
    {q : ℕ → Ω → ℝ} (hM : Margin S ε η θ q0 q m) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (q t ω, lag q0 q t ω) ∈ rotRegion ε η (θ t ω) := by
  filter_upwards [hM t, hA t] with ω h hAω
  have := region_of_shift hAω h.1 h.2 (da := 0) (db := 0) (by simp [hm]) (by simp [hm])
  simpa using this

/-- Cochrane (2023), p. 118 and eq. (17.17), p. 407: the Rotemberg price setter. For a uniformly
bounded admissible plan inside the concavity region with a positive margin, uniformly bounded
data with `A ≥ 0`, `0 < β < 1`, `φ ≥ 0` and `1 − ε + η ≥ 0`, optimality among the plans in the
region (`RPlan`) is **equivalent** to the first-order condition at every date. -/
theorem optimal_iff_foc_region {S : MeasExpectationSystem Ω} {β ε η φ m : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hη : 0 ≤ 1 - ε + η) (hφ : 0 ≤ φ) (hm : 0 < m)
    {θ : ℕ → Ω → ℝ × ℝ × ℝ} (hθ : DataReg S θ) (hθu : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ‖θ t ω‖ ≤ K)
    (hA : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ (θ t ω).1) {q0 : Ω → ℝ} (hq0 : StronglyMeasurable[S.𝓕 0] q0)
    (hq0b : BddAt S q0) {q : ℕ → Ω → ℝ} (hq : UPlan S q) (hM : Margin S ε η θ q0 q m)
    (hadm : Admissible S β (rotPay ε η φ) θ q0 q) :
    OptimalIn S (RPlan S ε η θ q0) β (rotPay ε η φ) θ q0 q ↔
      ∀ t, FOC S β (rotD1 ε η φ) (rotD2 φ) θ q0 q t := by
  constructor
  · intro hopt t
    exact foc_of_optimalIn hβ (rot_smooth ε η φ) hθ hq0 hq0b hq.1 hopt
      fun _ hz hzb => rplan_perturb hη hm hA hq hM hz hzb
  · intro hfoc
    refine optimalIn_of_foc hβ hβ1 (rot_smooth ε η φ) hθ hθu hq0 hq0b (fun _ h => h.1)
      ⟨hq, inRegion_of_margin hm.le hA hM⟩ hadm hfoc fun q' hq' t => ?_
    filter_upwards [inRegion_of_margin hm.le hA hM t, hq'.2 t, hA t] with ω h1 h2 hAω
    exact rot_supergrad hη hφ hAω h1 h2

end Cochrane.KeynesianStickyPrices.TidyR6Rotemberg
