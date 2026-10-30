/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6HouseholdPref
import KeynesianStickyPrices.TidyR6Rotemberg

/-!
# The joint yeoman-farmer problem equals the decentralised problems

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1, p. 118 ("a big point of
the new-Keynesian enterprise is that this structure has detailed micro-foundations"), and
Chapter 17, eqs. (17.15)–(17.17), p. 407.

TidyR6DerivedModel poses two problems: the household's consumption–bond problem given its
income, and the price setter's problem valuing revenue at the household's marginal utility. Here
a **single producer-household** (yeoman farmer) solves the **joint** problem: it chooses
consumption `c`, bonds `b` and its log relative price `q` to maximise
`E ∑ βᵗ[u(c_t) − D_te^{−ηq_t} − (φ/2)(e^{q_t − q_{t−1} + π_t} − 1)²]` subject to
`B_{t−1} + P_ty = P_tc_t + P_t(τ_t − Y_te^{(1−ε)q_t}) + Q_tB_t`, `B_t ≥ 0` (its sales revenue
`Y_te^{(1−ε)q_t}` is part of its income, `sq`). The objective is `jointValue`: the household's
expected utility plus the value of the non-consumption payoff, which is the Rotemberg payoff with
zero revenue weight (`dataN`).

## Main results

* `hh_of_joint`: in a joint optimum, `(c, b)` is optimal for the household given the income from
  `q` (the restriction to `q′ = q`).
* `foc_of_joint`: in a joint optimum (prices in any class closed under small one-date
  perturbations), `q` satisfies the price setter's first-order condition with revenue valued at
  `u′(c_t)` (`dataF`). The proof poses the auxiliary price-setting problem in which a price
  change is paid for by consumption at the same date (`auxPay`, `cOf`), whose value is the joint
  value (`auxValue_eq`), and applies `TidyR6PriceSetting.foc_of_optimalIn`.
* `joint_of_decentral`: conversely, a household plan satisfying the Euler equation and the
  transversality condition together with a price plan satisfying the price setter's first-order
  condition is jointly optimal among the joint plans whose prices lie in the concavity region
  (household budget comparison `TidyR6HouseholdPref.partial_bound_w` plus the price setter's
  `TidyR6PriceSetting.partial_le`).
* `joint_iff_decentral`: **the joint problem and the decentralised problems coincide**: under
  the stated regularity, `(c, b, q)` is jointly optimal (prices in the concavity region) iff
  `(c, b)` is optimal for the household and `q` is optimal for the price setter (in the same
  region). The two formulations do not differ.

`TidyR6JointGlobal` removes the concavity-region restriction for the decentralised-to-joint
direction and proves the equivalence near the steady state.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6JointYeoman

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6HouseholdMeasureTVC TidyR6PriceSetting TidyR6Rotemberg
open TidyR6HouseholdPref

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### The joint problem -/

/-- Cochrane (2023), p. 118: the producer-household's taxes net of its sales revenue,
`τ_t − Y_te^{(1−ε)q_t}`. -/
noncomputable def sq (τ Y : ℕ → Ω → ℝ) (ε : ℝ) (q : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => τ n ω - Y n ω * Real.exp ((1 - ε) * q n ω)

/-- Cochrane (2023), p. 118: the data of the non-consumption payoff (zero revenue weight). -/
def dataN (D π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ × ℝ × ℝ := fun t ω => (0, D t ω, π t ω)

/-- Cochrane (2023), p. 118: the decentralised price setter's data, revenue valued at the
household's marginal utility, `(u′(c_t)Y_t, D_t, π_t)`. -/
def dataF (u' : ℝ → ℝ) (c Y D π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ × ℝ × ℝ :=
  fun t ω => (u' (c t ω) * Y t ω, D t ω, π t ω)

variable (S) in
/-- Cochrane (2023), p. 118: a joint plan is admissible if its consumption utility and its
non-consumption payoff are. -/
def JointAdmissible (β : ℝ) (u : ℝ → ℝ) (ε η φ : ℝ) (D π : ℕ → Ω → ℝ) (q0 : Ω → ℝ)
    (c q : ℕ → Ω → ℝ) : Prop :=
  TidyR6HouseholdMeasure.Admissible S β u c ∧
    TidyR6PriceSetting.Admissible S β (rotPay ε η φ) (dataN D π) q0 q

variable (S) in
/-- Cochrane (2023), p. 118: the joint objective
`E ∑ βᵗu(c_t) + ∑ βᵗE[−D_te^{−ηq_t} − (φ/2)(e^{q_t − q_{t−1} + π_t} − 1)²]`. -/
noncomputable def jointValue (β : ℝ) (u : ℝ → ℝ) (ε η φ : ℝ) (D π : ℕ → Ω → ℝ) (q0 : Ω → ℝ)
    (c q : ℕ → Ω → ℝ) : ℝ :=
  expUtil S β u c + value S β (rotPay ε η φ) (dataN D π) q0 q

variable (S) in
/-- Cochrane (2023), p. 118: the yeoman farmer's joint optimum, with prices restricted to
the class `C`. -/
def JointOptimal (C : (ℕ → Ω → ℝ) → Prop) (β y : ℝ) (u : ℝ → ℝ) (ε η φ : ℝ)
    (P τ Y D π Q : ℕ → Ω → ℝ) (b₀ q0 : Ω → ℝ) (c b q : ℕ → Ω → ℝ) : Prop :=
  Feasible S y P (sq τ Y ε q) Q b₀ c b ∧ C q ∧ JointAdmissible S β u ε η φ D π q0 c q ∧
    ∀ c' b' q', Feasible S y P (sq τ Y ε q') Q b₀ c' b' → C q' →
      JointAdmissible S β u ε η φ D π q0 c' q' →
        jointValue S β u ε η φ D π q0 c' q' ≤ jointValue S β u ε η φ D π q0 c q

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: the decentralised price setter's payoff is the revenue valued at
`u′(c_t)` plus the non-consumption payoff. -/
theorem pay_split (ε η φ : ℝ) (u' : ℝ → ℝ) (c Y D π : ℕ → Ω → ℝ) (q0 : Ω → ℝ)
    (q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    pay (rotPay ε η φ) (dataF u' c Y D π) q0 q t ω =
      u' (c t ω) * Y t ω * Real.exp ((1 - ε) * q t ω) +
        pay (rotPay ε η φ) (dataN D π) q0 q t ω := by
  simp only [pay, rotPay, dataF, dataN]
  ring

/-- Cochrane (2023), p. 21: an admissible consumption plan has summable expected discounted
absolute utilities and `E ∑ βⁿu(c_n) = ∑ βⁿE u(c_n)`. -/
theorem admissible_tsum {β : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} {c : ℕ → Ω → ℝ}
    (h : TidyR6HouseholdMeasure.Admissible S β u c) :
    Summable (fun n => β ^ n * ∫ ω, |u (c n ω)| ∂S.μ) ∧
      expUtil S β u c = ∑' n, β ^ n * ∫ ω, u (c n ω) ∂S.μ := by
  have hi := h.integrable hβ
  have hs : Summable (fun n => β ^ n * ∫ ω, |u (c n ω)| ∂S.μ) := by
    refine summable_of_sum_range_le (c := ∫ ω, ∑' n, β ^ n * |u (c n ω)| ∂S.μ)
      (fun n => mul_nonneg (pow_nonneg hβ.le n) (integral_nonneg fun _ => abs_nonneg _))
      fun N => ?_
    have e : ∑ n ∈ Finset.range N, β ^ n * ∫ ω, |u (c n ω)| ∂S.μ =
        ∫ ω, ∑ n ∈ Finset.range N, β ^ n * |u (c n ω)| ∂S.μ := by
      rw [integral_finsetSum _ fun n _ => ((hi n).abs).const_mul _]
      simp_rw [integral_const_mul]
    rw [e]
    refine integral_mono_ae (integrable_finsetSum _ fun n _ => ((hi n).abs).const_mul _)
      h.2.2 ?_
    filter_upwards [h.2.1] with ω hω
    exact hω.sum_le_tsum _ fun n _ => mul_nonneg (pow_nonneg hβ.le n) (abs_nonneg _)
  refine ⟨hs, ?_⟩
  unfold expUtil
  rw [← integral_tsum_of_summable_integral_norm (fun n => (hi n).const_mul (β ^ n))]
  · simp_rw [integral_const_mul]
  · refine hs.congr fun n => ?_
    simp_rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ.le n), integral_const_mul]

/-- Cochrane (2023), p. 118: **in a joint optimum the household is optimal** given the income
from its price plan. -/
theorem hh_of_joint {C : (ℕ → Ω → ℝ) → Prop} {β y : ℝ} {u : ℝ → ℝ} {ε η φ : ℝ}
    {P τ Y D π Q : ℕ → Ω → ℝ} {b₀ q0 : Ω → ℝ} {c b q : ℕ → Ω → ℝ}
    (h : JointOptimal S C β y u ε η φ P τ Y D π Q b₀ q0 c b q) :
    Optimal S β y u P (sq τ Y ε q) Q b₀ c b := by
  refine ⟨h.1, h.2.2.1.1, fun c' b' hf ha => ?_⟩
  have := h.2.2.2 c' b' q hf h.2.1 ⟨ha, h.2.2.1.2⟩
  unfold jointValue at this
  linarith

/-! ### The auxiliary price-setting problem: price changes paid for by consumption -/

/-- Cochrane (2023), p. 118: consumption when the price plan is `q′` and the extra (or lost)
revenue is consumed at once, `c_t + Y_t(e^{(1−ε)q′_t} − e^{(1−ε)q_t})`. -/
noncomputable def cOf (c Y : ℕ → Ω → ℝ) (ε : ℝ) (q q' : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => c n ω + Y n ω * (Real.exp ((1 - ε) * q' n ω) - Real.exp ((1 - ε) * q n ω))

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: with the candidate's own prices, consumption is unchanged. -/
theorem cOf_self (c Y : ℕ → Ω → ℝ) (ε : ℝ) (q : ℕ → Ω → ℝ) : cOf c Y ε q q = c := by
  funext n ω
  simp [cOf]

/-- Cochrane (2023), p. 118: the auxiliary payoff `u(c + Y(e^{(1−ε)a} − k)) − De^{−ηa} −
(φ/2)(e^{a − b + π} − 1)²` with data `(c, Y, k, D, π)`. -/
noncomputable def auxPay (u : ℝ → ℝ) (ε η φ : ℝ) (a b : ℝ) (v : ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ :=
  u (v.1 + v.2.1 * (Real.exp ((1 - ε) * a) - v.2.2.1)) - v.2.2.2.1 * Real.exp (-(η * a)) -
    φ / 2 * (Real.exp (a - b + v.2.2.2.2) - 1) ^ 2

/-- Cochrane (2023), p. 118: its derivative in this period's price. -/
noncomputable def auxD1 (u' : ℝ → ℝ) (ε η φ : ℝ) (a b : ℝ) (v : ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ :=
  u' (v.1 + v.2.1 * (Real.exp ((1 - ε) * a) - v.2.2.1)) *
      (v.2.1 * (Real.exp ((1 - ε) * a) * (1 - ε))) +
    v.2.2.2.1 * η * Real.exp (-(η * a)) -
      φ * (Real.exp (a - b + v.2.2.2.2) - 1) * Real.exp (a - b + v.2.2.2.2)

/-- Cochrane (2023), p. 118: its derivative in last period's price. -/
noncomputable def auxD2 (φ : ℝ) (a b : ℝ) (v : ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ :=
  φ * (Real.exp (a - b + v.2.2.2.2) - 1) * Real.exp (a - b + v.2.2.2.2)

/-- Cochrane (2023), p. 118: the auxiliary data `(c_t, Y_t, e^{(1−ε)q_t}, D_t, π_t)`. -/
noncomputable def dataJ (c Y : ℕ → Ω → ℝ) (ε : ℝ) (q D π : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ × ℝ × ℝ × ℝ × ℝ :=
  fun t ω => (c t ω, Y t ω, Real.exp ((1 - ε) * q t ω), D t ω, π t ω)

/-- Cochrane (2023), p. 118: the auxiliary payoff is smooth for differentiable `u` with
continuous derivative. -/
theorem aux_smooth {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x) (hu'c : Continuous u')
    (ε η φ : ℝ) : Smooth (auxPay u ε η φ) (auxD1 u' ε η φ) (auxD2 φ) := by
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  refine ⟨fun a b v => ?_, fun a b v => ?_, ?_, ?_, ?_⟩
  · have h1 : HasDerivAt (fun a => Real.exp ((1 - ε) * a)) (Real.exp ((1 - ε) * a) * (1 - ε)) a :=
      ((hasDerivAt_id a).const_mul (1 - ε)).exp.congr_deriv (by simp)
    have hin : HasDerivAt (fun a => v.1 + v.2.1 * (Real.exp ((1 - ε) * a) - v.2.2.1))
        (v.2.1 * (Real.exp ((1 - ε) * a) * (1 - ε))) a :=
      ((h1.sub_const v.2.2.1).const_mul v.2.1).const_add v.1
    have h2 : HasDerivAt (fun a => Real.exp (-(η * a))) (Real.exp (-(η * a)) * (-η)) a :=
      (((hasDerivAt_id a).const_mul η).neg).exp.congr_deriv (by simp)
    have h3 : HasDerivAt (fun a => Real.exp (a - b + v.2.2.2.2)) (Real.exp (a - b + v.2.2.2.2))
        a := by
      have := (((hasDerivAt_id a).sub_const b).add_const v.2.2.2.2).exp
      simpa using this
    have h := (((hu _).comp a hin).sub (h2.const_mul v.2.2.2.1)).sub
      (((h3.sub_const 1).pow 2).const_mul (φ / 2))
    refine h.congr_deriv ?_
    simp only [auxD1]
    push_cast
    ring
  · have h3 : HasDerivAt (fun b => Real.exp (a - b + v.2.2.2.2))
        (Real.exp (a - b + v.2.2.2.2) * (-1)) b :=
      ((((hasDerivAt_id b).const_sub a).add_const v.2.2.2.2).exp).congr_deriv (by simp)
    have h := (((h3.sub_const 1).pow 2).const_mul (φ / 2)).const_sub
      (u (v.1 + v.2.1 * (Real.exp ((1 - ε) * a) - v.2.2.1)) -
        v.2.2.2.1 * Real.exp (-(η * a)))
    refine h.congr_deriv ?_
    simp only [auxD2]
    push_cast
    ring
  · simp only [auxPay]
    fun_prop
  · simp only [auxD1]
    fun_prop
  · simp only [auxD2]
    fun_prop

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: the auxiliary payoff of `q′` is the utility of `cOf q′` plus the
non-consumption payoff of `q′`. -/
theorem pay_aux (u : ℝ → ℝ) (ε η φ : ℝ) (c Y q D π : ℕ → Ω → ℝ) (q0 : Ω → ℝ)
    (q' : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    pay (auxPay u ε η φ) (dataJ c Y ε q D π) q0 q' t ω =
      u (cOf c Y ε q q' t ω) + pay (rotPay ε η φ) (dataN D π) q0 q' t ω := by
  simp only [pay, auxPay, rotPay, dataJ, dataN, cOf]
  ring

/-- Cochrane (2023), p. 118: if `(cOf q′, q′)` is jointly admissible, the auxiliary plan `q′` is
admissible and its value is the joint value of `(cOf q′, q′)`. -/
theorem auxValue_eq {β : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} {ε η φ : ℝ} {c Y q D π : ℕ → Ω → ℝ}
    {q0 : Ω → ℝ} {q' : ℕ → Ω → ℝ}
    (h : JointAdmissible S β u ε η φ D π q0 (cOf c Y ε q q') q') :
    TidyR6PriceSetting.Admissible S β (auxPay u ε η φ) (dataJ c Y ε q D π) q0 q' ∧
      value S β (auxPay u ε η φ) (dataJ c Y ε q D π) q0 q' =
        jointValue S β u ε η φ D π q0 (cOf c Y ε q q') q' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hs, he⟩ := admissible_tsum hβ h1
  have hi1 := h1.integrable hβ
  have hpe : ∀ t, pay (auxPay u ε η φ) (dataJ c Y ε q D π) q0 q' t =
      fun ω => u (cOf c Y ε q q' t ω) + pay (rotPay ε η φ) (dataN D π) q0 q' t ω := fun t =>
    funext fun ω => pay_aux u ε η φ c Y q D π q0 q' t ω
  have hint : ∀ t, Integrable (pay (auxPay u ε η φ) (dataJ c Y ε q D π) q0 q' t) S.μ :=
    fun t => by rw [hpe]; exact (hi1 t).add (h2.1 t)
  have hsu : Summable fun t => β ^ t * ∫ ω, u (cOf c Y ε q q' t ω) ∂S.μ :=
    Summable.of_norm_bounded hs fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ.le t)]
      exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (pow_nonneg hβ.le t)
  have hsn := h2.summable hβ.le
  refine ⟨⟨hint, ?_⟩, ?_⟩
  · refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ.le t)
      (integral_nonneg fun _ => abs_nonneg _)) (fun t => ?_) (hs.add h2.2)
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ.le t)
    rw [← integral_add (hi1 t).abs (h2.1 t).abs]
    refine integral_mono (hint t).abs ((hi1 t).abs.add (h2.1 t).abs) fun ω => ?_
    rw [hpe]
    exact abs_add_le _ _
  · rw [jointValue, he, value, value, ← hsu.tsum_add hsn]
    refine tsum_congr fun t => ?_
    rw [hpe, integral_add (hi1 t) (h2.1 t), mul_add]

/-- Cochrane (2023), p. 118: paying for a price change with same-date consumption keeps the
budget: if `(c, b)` is feasible with the income of `q`, `(cOf q′, b)` is feasible with the income
of `q′`. -/
theorem feasible_cOf {y ε : ℝ} {P τ Y Q c b q q' : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (h : Feasible S y P (sq τ Y ε q) Q b₀ c b) (hY : StronglyAdapted S.𝓕 Y)
    (hq : StronglyAdapted S.𝓕 q) (hq' : StronglyAdapted S.𝓕 q') :
    Feasible S y P (sq τ Y ε q') Q b₀ (cOf c Y ε q q') b := by
  obtain ⟨h0, hc, hb, hflow, hnn⟩ := h
  refine ⟨h0, fun n => ?_, hb, fun n => ?_, hnn⟩
  · have m1 : Measurable[S.𝓕 n] (c n) := (hc n).measurable
    have m2 : Measurable[S.𝓕 n] (Y n) := (hY n).measurable
    have m3 : Measurable[S.𝓕 n] (q n) := (hq n).measurable
    have m4 : Measurable[S.𝓕 n] (q' n) := (hq' n).measurable
    exact (m1.add (m2.mul ((Real.continuous_exp.measurable.comp (m4.const_mul (1 - ε))).sub
      (Real.continuous_exp.measurable.comp (m3.const_mul (1 - ε)))))).stronglyMeasurable
  · filter_upwards [hflow n] with ω hω
    simp only [cOf, sq] at hω ⊢
    linear_combination hω

/-- Cochrane (2023), p. 118: a vector of five bounded numbers is bounded in norm. -/
theorem norm5_le {a b c d e K : ℝ} (ha : |a| ≤ K) (hb : |b| ≤ K) (hc : |c| ≤ K) (hd : |d| ≤ K)
    (he : |e| ≤ K) : ‖((a, b, c, d, e) : ℝ × ℝ × ℝ × ℝ × ℝ)‖ ≤ K := by
  simp only [Prod.norm_mk, Real.norm_eq_abs]
  exact max_le ha (max_le hb (max_le hc (max_le hd he)))

/-- Cochrane (2023), p. 118: the auxiliary data are known at `t` and essentially bounded at every
date. -/
theorem dataJ_reg {ε : ℝ} {c Y q D π : ℕ → Ω → ℝ} (hc : StronglyAdapted S.𝓕 c)
    (hY : StronglyAdapted S.𝓕 Y) (hq : StronglyAdapted S.𝓕 q) (hD : StronglyAdapted S.𝓕 D)
    (hπ : StronglyAdapted S.𝓕 π) (hcb : ∀ t, BddAt S (c t)) (hYb : ∀ t, BddAt S (Y t))
    (hqb : ∀ t, BddAt S (q t)) (hDb : ∀ t, BddAt S (D t)) (hπb : ∀ t, BddAt S (π t)) :
    DataReg S (dataJ c Y ε q D π) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · exact ((hc t).measurable.prodMk ((hY t).measurable.prodMk
      ((Real.continuous_exp.measurable.comp ((hq t).measurable.const_mul (1 - ε))).prodMk
        ((hD t).measurable.prodMk (hπ t).measurable)))).stronglyMeasurable
  · obtain ⟨K1, hK1⟩ := hcb t
    obtain ⟨K2, hK2⟩ := hYb t
    obtain ⟨K3, hK3⟩ := BddAt.comp (v := fun z => Real.exp ((1 - ε) * z)) (by fun_prop) (hqb t)
    obtain ⟨K4, hK4⟩ := hDb t
    obtain ⟨K5, hK5⟩ := hπb t
    refine ⟨max K1 (max K2 (max K3 (max K4 K5))), ?_⟩
    filter_upwards [hK1, hK2, hK3, hK4, hK5] with ω h1 h2 h3 h4 h5
    exact norm5_le (h1.trans (le_max_left _ _))
      (h2.trans ((le_max_left _ _).trans (le_max_right _ _)))
      (h3.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
      (h4.trans ((le_max_left _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))))
      (h5.trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))))

/-- Cochrane (2023), p. 118: the non-consumption data are known at `t` and essentially bounded. -/
theorem dataN_reg {D π : ℕ → Ω → ℝ} (hD : StronglyAdapted S.𝓕 D)
    (hπ : StronglyAdapted S.𝓕 π) (hDb : ∀ t, BddAt S (D t)) (hπb : ∀ t, BddAt S (π t)) :
    DataReg S (dataN D π) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · exact (measurable_const.prodMk ((hD t).measurable.prodMk
      (hπ t).measurable)).stronglyMeasurable
  · obtain ⟨K4, hK4⟩ := hDb t
    obtain ⟨K5, hK5⟩ := hπb t
    refine ⟨max K4 K5, ?_⟩
    filter_upwards [hK4, hK5] with ω h4 h5
    simp only [dataN, Prod.norm_mk, Real.norm_eq_abs, abs_zero]
    exact max_le ((abs_nonneg _).trans (h4.trans (le_max_left _ _)))
      (max_le (h4.trans (le_max_left _ _)) (h5.trans (le_max_right _ _)))

/-! ### Joint optimum ⇒ the price setter's first-order condition -/

/-- Cochrane (2023), p. 118: **in a joint optimum the price plan satisfies the decentralised
price setter's first-order condition** at `t`, with revenue valued at the household's marginal
utility `u′(c_t)` (`dataF`). The price class `C` consists of plans and contains all small
one-date perturbations of `q` (as `Plan`, `UPlan` and `TidyR6Rotemberg.RPlan` with a margin
do); consumption, output, disutility scale and inflation are adapted and essentially bounded at
every date. -/
theorem foc_of_joint {C : (ℕ → Ω → ℝ) → Prop} {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu'c : Continuous u') {ε η φ : ℝ}
    {P τ Y D π Q : ℕ → Ω → ℝ} {b₀ q0 : Ω → ℝ} {c b q : ℕ → Ω → ℝ}
    (hopt : JointOptimal S C β y u ε η φ P τ Y D π Q b₀ q0 c b q)
    (hCP : ∀ q', C q' → Plan S q') (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0)
    (hc : StronglyAdapted S.𝓕 c) (hY : StronglyAdapted S.𝓕 Y) (hD : StronglyAdapted S.𝓕 D)
    (hπ : StronglyAdapted S.𝓕 π) (hcb : ∀ t, BddAt S (c t)) (hYb : ∀ t, BddAt S (Y t))
    (hDb : ∀ t, BddAt S (D t)) (hπb : ∀ t, BddAt S (π t)) {t : ℕ}
    (hC : ∀ z : Ω → ℝ, StronglyMeasurable[S.𝓕 t] z → BddAt S z →
      ∀ᶠ s in 𝓝 (0 : ℝ), C (perturb q z t s)) :
    FOC S β (rotD1 ε η φ) (rotD2 φ) (dataF u' c Y D π) q0 q t := by
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  have hq := hCP q hopt.2.1
  set C' : (ℕ → Ω → ℝ) → Prop := fun q' =>
    C q' ∧ JointAdmissible S β u ε η φ D π q0 (cOf c Y ε q q') q' with hC'def
  have hJq : JointAdmissible S β u ε η φ D π q0 (cOf c Y ε q q) q := by
    rw [cOf_self]
    exact hopt.2.2.1
  have hval := auxValue_eq (c := c) (Y := Y) hβ hJq
  have haux : OptimalIn S C' β (auxPay u ε η φ) (dataJ c Y ε q D π) q0 q := by
    refine ⟨⟨hopt.2.1, hJq⟩, hval.1, fun q' hq' _ => ?_⟩
    rw [hval.2, (auxValue_eq hβ hq'.2).2, cOf_self]
    exact hopt.2.2.2 _ _ q' (feasible_cOf hopt.1 hY hq.1 (hCP q' hq'.1).1) hq'.1 hq'.2
  have hC' : ∀ z : Ω → ℝ, StronglyMeasurable[S.𝓕 t] z → BddAt S z →
      ∀ᶠ s in 𝓝 (0 : ℝ), C' (perturb q z t s) := by
    intro z hz hzb
    filter_upwards [hC z hz hzb] with s hs
    refine ⟨hs, ?_, admissible_perturb (rot_smooth ε η φ).2.2.1 (dataN_reg hD hπ hDb hπb) hq0
      hq0b hq hopt.2.2.1.2 hz hzb s⟩
    refine (admissible_modify hβ hopt.2.2.1.1 {t} (fun n hn => ?_) (fun n hn => ?_)).1
    · funext ω
      rw [Finset.mem_singleton] at hn
      simp [cOf, perturb_ne hn]
    · rw [Finset.mem_singleton] at hn
      subst hn
      have e : cOf c Y ε q (perturb q z n s) n = fun ω => c n ω + Y n ω *
          (Real.exp ((1 - ε) * (q n ω + s * z ω)) - Real.exp ((1 - ε) * q n ω)) := by
        funext ω
        simp [cOf, perturb]
      have hb : BddAt S (cOf c Y ε q (perturb q z n s) n) := by
        rw [e]
        have := (hcb n).add ((hYb n).mul ((BddAt.comp (v := Real.exp) Real.continuous_exp
          ((BddAt.const (S := S) (1 - ε)).mul ((hq.2 n).add ((BddAt.const s).mul hzb)))).add
          (BddAt.comp (v := Real.exp) Real.continuous_exp
            ((BddAt.const (S := S) (1 - ε)).mul (hq.2 n))).neg))
        simpa [cOf, sub_eq_add_neg] using this
      have hm : StronglyMeasurable[S.𝓕 n] (cOf c Y ε q (perturb q z n s) n) := by
        rw [e]
        exact ((hc n).measurable.add ((hY n).measurable.mul
          ((Real.continuous_exp.measurable.comp (((hq.1 n).measurable.add
            (hz.measurable.const_mul s)).const_mul (1 - ε))).sub
          (Real.continuous_exp.measurable.comp
            ((hq.1 n).measurable.const_mul (1 - ε)))))).stronglyMeasurable
      exact (BddAt.comp huc hb).integrable
        (huc.comp_aestronglyMeasurable (hm.mono (S.𝓕.le n)).aestronglyMeasurable)
  have hfoc := foc_of_optimalIn hβ (aux_smooth hu hu'c ε η φ)
    (dataJ_reg hc hY hq.1 hD hπ hcb hYb hq.2 hDb hπb) hq0 hq0b hq haux hC'
  have e2 : (fun ω => auxD2 φ (q (t + 1) ω) (q t ω) (dataJ c Y ε q D π (t + 1) ω)) =
      fun ω => rotD2 φ (q (t + 1) ω) (q t ω) (dataF u' c Y D π (t + 1) ω) := by
    funext ω
    simp [auxD2, rotD2, dataJ, dataF]
  unfold FOC at hfoc ⊢
  rw [e2] at hfoc
  filter_upwards [hfoc] with ω h
  have e1 : auxD1 u' ε η φ (q t ω) (lag q0 q t ω) (dataJ c Y ε q D π t ω) =
      rotD1 ε η φ (q t ω) (lag q0 q t ω) (dataF u' c Y D π t ω) := by
    simp only [auxD1, rotD1, dataJ, dataF, sub_self, mul_zero, add_zero]
    ring
  rw [← e1]
  exact h

/-! ### Decentralised optimum ⇒ joint optimum -/

/-- Cochrane (2023), p. 118: **a decentralised optimum is a joint optimum**. Let the household
plan `(c, b)` (income from `q`) satisfy the Euler equation at every date and the
transversality condition, with concave increasing differentiable `u`; let the price plan `q` lie
in the concavity region of the decentralised payoff (data `dataF`, revenue valued at `u′(c_t)`,
`u′(c_t)Y_t ≥ 0`, uniformly bounded) and satisfy its first-order condition at every date. Then
`(c, b, q)` is jointly optimal among the joint plans whose prices lie in that region
(`0 < β < 1`, `φ ≥ 0`, `1 − ε + η ≥ 0`). -/
theorem joint_of_decentral {β y : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu'c : Continuous u') (hconc : ConcaveOn ℝ Set.univ u)
    (hmono : Monotone u) {ε η φ : ℝ} (hη : 0 ≤ 1 - ε + η) (hφ : 0 ≤ φ)
    {P τ Y D π Q : ℕ → Ω → ℝ} {b₀ q0 : Ω → ℝ} {c b q : ℕ → Ω → ℝ}
    (hfeas : Feasible S y P (sq τ Y ε q) Q b₀ c b)
    (hjadm : JointAdmissible S β u ε η φ D π q0 c q)
    (hqR : RPlan S ε η (dataF u' c Y D π) q0 q) (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω)
    (hm : ∀ n, Integrable (fun ω => u' (c n ω) / P n ω) S.μ)
    (hW : ∀ n, Integrable (fun ω => u' (c n ω) * b n ω / P n ω) S.μ)
    (heul : ∀ n, ∀ᵐ ω ∂S.μ, Q n ω * (u' (c n ω) / P n ω) =
      β * S.E n (fun ω => u' (c (n + 1) ω) / P (n + 1) ω) ω)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, u' (c N ω) * b N ω / P N ω ∂S.μ) atTop (𝓝 0))
    (hfoc : ∀ t, FOC S β (rotD1 ε η φ) (rotD2 φ) (dataF u' c Y D π) q0 q t)
    (hθ : DataReg S (dataF u' c Y D π)) (hθu : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ‖dataF u' c Y D π t ω‖ ≤ K)
    (hA : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ u' (c t ω) * Y t ω) (hq0 : StronglyMeasurable[S.𝓕 0] q0)
    (hq0b : BddAt S q0) (hc : StronglyAdapted S.𝓕 c) (hY : StronglyAdapted S.𝓕 Y)
    (hD : StronglyAdapted S.𝓕 D) (hπ : StronglyAdapted S.𝓕 π) (hcb : ∀ t, BddAt S (c t))
    (hYb : ∀ t, BddAt S (Y t)) (hDb : ∀ t, BddAt S (D t)) (hπb : ∀ t, BddAt S (π t)) :
    JointOptimal S (RPlan S ε η (dataF u' c Y D π) q0) β y u ε η φ P τ Y D π Q b₀ q0 c b q := by
  refine ⟨hfeas, hqR, hjadm, fun c' b' q' hf' hq'R hjadm' => ?_⟩
  have hq := hqR.1.1
  have hq' := hq'R.1.1
  set e : (ℕ → Ω → ℝ) → ℕ → Ω → ℝ :=
    fun r n ω => u' (c n ω) * Y n ω * Real.exp ((1 - ε) * r n ω) with hedef
  have hei : ∀ (r : ℕ → Ω → ℝ), Plan S r → ∀ n, Integrable (e r n) S.μ := by
    intro r hr n
    have hb := ((BddAt.comp hu'c (hcb n)).mul (hYb n)).mul
      (BddAt.comp (v := fun z => Real.exp ((1 - ε) * z)) (by fun_prop) (hr.2 n))
    refine hb.integrable ?_
    have hm : Measurable[S.𝓕 n] (e r n) :=
      ((hu'c.measurable.comp (hc n).measurable).mul (hY n).measurable).mul
        (Real.continuous_exp.measurable.comp ((hr.1 n).measurable.const_mul (1 - ε)))
    exact (hm.stronglyMeasurable.mono (S.𝓕.le n)).aestronglyMeasurable
  -- the household's budget comparison
  have hhB : ∀ N, ∑ n ∈ Finset.range N, β ^ n * (∫ ω, u (c' n ω) ∂S.μ - ∫ ω, u (c n ω) ∂S.μ) ≤
      β ^ N * ∫ ω, u' (c N ω) * b N ω / P N ω ∂S.μ +
        ∑ n ∈ Finset.range N, β ^ n * (∫ ω, e q' n ω ∂S.μ - ∫ ω, e q n ω ∂S.μ) := by
    intro N
    have h := partial_bound_w (w := fun _ _ => 1) hβ hu hconc hmono
      (fun _ => Eventually.of_forall fun _ => zero_le_one) hfeas hf'
      (fun n => (hjadm.1.integrable hβ n).congr (Eventually.of_forall fun ω => by simp [felic]))
      (fun n => (hjadm'.1.integrable hβ n).congr (Eventually.of_forall fun ω => by simp [felic]))
      hP
      (fun n => by simpa using hm n) (fun n => by simpa using hW n)
      (fun n => by
        have h2 := (hei q' hq' n).sub (hei q hq n)
        refine h2.congr (Eventually.of_forall fun ω => ?_)
        simp only [hedef, Pi.sub_apply, sq]
        ring)
      (fun n => by simpa using heul n) N
    have e2 : ∀ n, ∫ ω, u' (c n ω) * (sq τ Y ε q n ω - sq τ Y ε q' n ω) ∂S.μ =
        ∫ ω, e q' n ω ∂S.μ - ∫ ω, e q n ω ∂S.μ := by
      intro n
      rw [← integral_sub (hei q' hq' n) (hei q hq n)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hedef, sq]
      ring
    simp only [felic, one_mul] at h
    simp only [e2] at h
    simpa using h
  -- the price setter's comparison
  have hsg : ∀ t, SuperGrad S (rotPay ε η φ) (rotD1 ε η φ) (rotD2 φ) (dataF u' c Y D π) q0 q q'
      t := fun t => by
    filter_upwards [hqR.2 t, hq'R.2 t, hA t] with ω h1 h2 h3
    exact rot_supergrad hη hφ h3 h1 h2
  have hfB := partial_le hβ (rot_smooth ε η φ) hθ hq0 hq0b hq hq' hfoc hsg
  have hpF : ∀ (r : ℕ → Ω → ℝ), Plan S r → ∀ n,
      ∫ ω, pay (rotPay ε η φ) (dataF u' c Y D π) q0 r n ω ∂S.μ =
      ∫ ω, e r n ω ∂S.μ + ∫ ω, pay (rotPay ε η φ) (dataN D π) q0 r n ω ∂S.μ := by
    intro r hr n
    have hN := pay_integrable (rot_smooth ε η φ).2.2.1 (dataN_reg hD hπ hDb hπb) hq0 hq0b hr n
    rw [← integral_add (hei r hr n) hN]
    exact integral_congr_ae (Eventually.of_forall fun ω => pay_split ε η φ u' c Y D π q0 r n ω)
  -- the limits
  have hlimH := tendsto_partial_utilDiff hβ hjadm.1 hjadm'.1
  have hlimN := ((hjadm'.2.summable hβ.le).sub (hjadm.2.summable hβ.le)).hasSum.tendsto_sum_nat
  rw [(hjadm'.2.summable hβ.le).tsum_sub (hjadm.2.summable hβ.le)] at hlimN
  have hlim := (tendsto_add_atTop_iff_nat 1).2 (hlimH.add hlimN)
  have hr : Tendsto (fun T => β ^ (T + 1) * ∫ ω, u' (c (T + 1) ω) * b (T + 1) ω / P (T + 1) ω ∂S.μ +
      β ^ T * ∫ ω, rotD1 ε η φ (q T ω) (lag q0 q T ω) (dataF u' c Y D π T ω) *
        (q' T ω - q T ω) ∂S.μ) atTop (𝓝 (0 + 0)) :=
    ((tendsto_add_atTop_iff_nat 1).2 htvc).add
      (tvc_of_ubdd hβ hβ1 (rot_smooth ε η φ).2.2.2.1 hθu hq0b hqR.1 hq'R.1)
  have hle := le_of_tendsto_of_tendsto' hlim hr fun T => by
    have h1 := hhB (T + 1)
    have h2 := hfB T
    have e3 : ∀ n, β ^ n * (∫ ω, pay (rotPay ε η φ) (dataF u' c Y D π) q0 q' n ω ∂S.μ -
        ∫ ω, pay (rotPay ε η φ) (dataF u' c Y D π) q0 q n ω ∂S.μ) =
        β ^ n * (∫ ω, e q' n ω ∂S.μ - ∫ ω, e q n ω ∂S.μ) +
          (β ^ n * ∫ ω, pay (rotPay ε η φ) (dataN D π) q0 q' n ω ∂S.μ -
            β ^ n * ∫ ω, pay (rotPay ε η φ) (dataN D π) q0 q n ω ∂S.μ) := fun n => by
      rw [hpF q' hq' n, hpF q hq n]
      ring
    have h2' : ∑ n ∈ Finset.range (T + 1), β ^ n *
        (∫ ω, pay (rotPay ε η φ) (dataF u' c Y D π) q0 q' n ω ∂S.μ -
          ∫ ω, pay (rotPay ε η φ) (dataF u' c Y D π) q0 q n ω ∂S.μ) =
        ∑ n ∈ Finset.range (T + 1), β ^ n * (∫ ω, e q' n ω ∂S.μ - ∫ ω, e q n ω ∂S.μ) +
          (∑ n ∈ Finset.range (T + 1), β ^ n * ∫ ω, pay (rotPay ε η φ) (dataN D π) q0 q' n ω ∂S.μ -
            ∑ n ∈ Finset.range (T + 1),
              β ^ n * ∫ ω, pay (rotPay ε η φ) (dataN D π) q0 q n ω ∂S.μ) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => e3 n
    rw [h2'] at h2
    rw [Finset.sum_sub_distrib]
    linarith
  unfold jointValue value
  linarith

/-! ### The equivalence -/

/-- Cochrane (2023), p. 118: a uniformly bounded price plan with uniformly bounded data is
admissible (`0 ≤ β < 1`). -/
theorem admissible_of_uplan {β ε η φ : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) {θ : ℕ → Ω → ℝ × ℝ × ℝ}
    (hθ : DataReg S θ) (hθu : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ‖θ t ω‖ ≤ K) {q0 : Ω → ℝ}
    (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0) {q : ℕ → Ω → ℝ}
    (hq : UPlan S q) : TidyR6PriceSetting.Admissible S β (rotPay ε η φ) θ q0 q := by
  obtain ⟨K, hK⟩ := hθu
  obtain ⟨R, hR⟩ := hq.2
  obtain ⟨R0, hR0⟩ := hq0b
  obtain ⟨M, hM0, hM⟩ := exists_box_bound (rot_smooth ε η φ).2.2.1 (max R R0) K
  have hb : ∀ t, ∀ᵐ ω ∂S.μ, |pay (rotPay ε η φ) θ q0 q t ω| ≤ M := fun t => by
    have hl : ∀ᵐ ω ∂S.μ, |lag q0 q t ω| ≤ max R R0 := by
      cases t with
      | zero => exact hR0.mono fun ω h => h.trans (le_max_right _ _)
      | succ n => exact (hR n).mono fun ω h => h.trans (le_max_left _ _)
    filter_upwards [hK t, hR t, hl] with ω h1 h2 h3
    exact hM _ _ _ (h2.trans (le_max_left _ _)) h3 h1
  have hint : ∀ t, Integrable (pay (rotPay ε η φ) θ q0 q t) S.μ := fun t =>
    pay_integrable (rot_smooth ε η φ).2.2.1 hθ hq0 ⟨R0, hR0⟩ hq.1 t
  refine ⟨hint, Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ t)
    (integral_nonneg fun _ => abs_nonneg _)) (fun t => ?_)
    ((summable_geometric_of_lt_one hβ hβ1).mul_right M)⟩
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ t)
  have := integral_mono_ae (hint t).abs (integrable_const M) (hb t)
  simpa using this

/-- Cochrane (2023), p. 118, **the joint yeoman-farmer problem coincides with the decentralised
problems**. Let `0 < β < 1`, `φ ≥ 0`, `1 − ε + η ≥ 0`, `u` concave, increasing and
differentiable with continuous derivative; prices and bond prices adapted, prices positive, the
household's `EulerRegular` regularity at every date, bonds held at every date, integrable
marginal-utility-weighted bonds and the transversality condition; consumption, output, disutility
scale and inflation adapted and bounded at every date (output nonnegative), the decentralised data
uniformly bounded; and the price plan uniformly bounded, in the concavity region with a positive
margin `m`. Then `(c, b, q)` is jointly optimal (prices in the region) **iff** `(c, b)` is optimal
for the household given the income from `q` **and** `q` is optimal for the price setter that
values revenue at `u′(c_t)` (prices in the same region). -/
theorem joint_iff_decentral {β y : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu'c : Continuous u') (hconc : ConcaveOn ℝ Set.univ u)
    (hmono : Monotone u) {ε η φ m : ℝ} (hη : 0 ≤ 1 - ε + η) (hφ : 0 ≤ φ) (hm : 0 < m)
    {P τ Y D π Q : ℕ → Ω → ℝ} {b₀ q0 : Ω → ℝ} {c b q : ℕ → Ω → ℝ}
    (hfeas : Feasible S y P (sq τ Y ε q) Q b₀ c b)
    (hjadm : JointAdmissible S β u ε η φ D π q0 c q) (hq : UPlan S q)
    (hM : Margin S ε η (dataF u' c Y D π) q0 q m) (hPad : StronglyAdapted S.𝓕 P)
    (hQad : StronglyAdapted S.𝓕 Q) (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω)
    (hreg : ∀ t, EulerRegular S P Q c t) (hb : ∀ t, ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω)
    (hW : ∀ n, Integrable (fun ω => u' (c n ω) * b n ω / P n ω) S.μ)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, u' (c N ω) * b N ω / P N ω ∂S.μ) atTop (𝓝 0))
    (hθu : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ‖dataF u' c Y D π t ω‖ ≤ K)
    (hY0 : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ Y t ω) (hq0 : StronglyMeasurable[S.𝓕 0] q0)
    (hq0b : BddAt S q0) (hc : StronglyAdapted S.𝓕 c) (hY : StronglyAdapted S.𝓕 Y)
    (hD : StronglyAdapted S.𝓕 D) (hπ : StronglyAdapted S.𝓕 π) (hcb : ∀ t, BddAt S (c t))
    (hYb : ∀ t, BddAt S (Y t)) (hDb : ∀ t, BddAt S (D t)) (hπb : ∀ t, BddAt S (π t)) :
    JointOptimal S (RPlan S ε η (dataF u' c Y D π) q0) β y u ε η φ P τ Y D π Q b₀ q0 c b q ↔
      Optimal S β y u P (sq τ Y ε q) Q b₀ c b ∧
        OptimalIn S (RPlan S ε η (dataF u' c Y D π) q0) β (rotPay ε η φ) (dataF u' c Y D π)
          q0 q := by
  have hu'0 : ∀ x, 0 ≤ u' x := fun x => deriv_nonneg_of_monotone hmono (hu x)
  have hA : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ (dataF u' c Y D π t ω).1 := fun t =>
    (hY0 t).mono fun ω h => mul_nonneg (hu'0 _) h
  have hθ : DataReg S (dataF u' c Y D π) := by
    refine ⟨fun t => ?_, fun t => ?_⟩
    · exact ((((hu'c.measurable.comp (hc t).measurable).mul (hY t).measurable)).prodMk
        ((hD t).measurable.prodMk (hπ t).measurable)).stronglyMeasurable
    · obtain ⟨K1, hK1⟩ := (BddAt.comp hu'c (hcb t)).mul (hYb t)
      obtain ⟨K4, hK4⟩ := hDb t
      obtain ⟨K5, hK5⟩ := hπb t
      refine ⟨max K1 (max K4 K5), ?_⟩
      filter_upwards [hK1, hK4, hK5] with ω h1 h4 h5
      simp only [dataF, Prod.norm_mk, Real.norm_eq_abs]
      exact max_le (h1.trans (le_max_left _ _)) (max_le
        (h4.trans ((le_max_left _ _).trans (le_max_right _ _)))
        (h5.trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hadmF := admissible_of_uplan hβ.le hβ1 hθ hθu hq0 hq0b hq (ε := ε) (η := η) (φ := φ)
  have hiff := optimal_iff_foc_region hβ hβ1 hη hφ hm hθ hθu hA hq0 hq0b hq hM hadmF
  constructor
  · intro hJ
    refine ⟨hh_of_joint hJ, hiff.2 fun t => foc_of_joint hβ hu hu'c hJ (fun _ h => h.1.1) hq0
      hq0b hc hY hD hπ hcb hYb hDb hπb fun _ hz hzb => rplan_perturb hη hm hA hq hM hz hzb⟩
  · rintro ⟨hH, hF⟩
    have hm' : ∀ n, Integrable (fun ω => u' (c n ω) / P n ω) S.μ := fun n => by
      have hbd := (BddAt.comp hu'c (hreg n).1).mul (hreg n).2.2.2.1
      refine (show BddAt S (fun ω => u' (c n ω) / P n ω) by
        simpa [div_eq_mul_inv] using hbd).integrable ?_
      have hmm : Measurable[S.𝓕 n] (fun ω => u' (c n ω) / P n ω) :=
        (hu'c.measurable.comp (hc n).measurable).div (hPad n).measurable
      exact (hmm.stronglyMeasurable.mono (S.𝓕.le n)).aestronglyMeasurable
    refine joint_of_decentral hβ hβ1 hu hu'c hconc hmono hη hφ hfeas hjadm
      ⟨hq, inRegion_of_margin hm.le hA hM⟩ hP hm' hW (fun n => ?_) htvc (hiff.1 hF) hθ hθu
      (fun t => (hY0 t).mono fun ω h => mul_nonneg (hu'0 _) h) hq0 hq0b hc hY hD hπ hcb hYb
      hDb hπb
    filter_upwards [euler_of_pos hβ hu hu'c hH hPad hP (hQad n) (hreg n) (hb n)] with ω hω
    simpa using hω

end Cochrane.KeynesianStickyPrices.TidyR6JointYeoman
