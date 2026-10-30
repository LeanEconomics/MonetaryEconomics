/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6HouseholdMeasure
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The price-setting problem on a probability space: first-order conditions

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1, p. 118: "The Phillips
curve (5.2) comes from the first-order condition for monopolistically-competitive price setters,
facing costs of changing prices ... Firms set prices today knowing that prices will be stuck for
a while, so they set prices with expected future prices in mind", and Chapter 17, eq. (17.17),
p. 407.

A price setter with costs of changing prices chooses a plan `q_t` (its log relative price) to
maximise `E ∑_t βᵗ Φ(q_t, q_{t−1}, θ_t)`, where the period payoff `Φ` depends on this period's
and last period's choice (the cost of changing prices) and on the aggregate data `θ_t` (known at
`t`), with `q_{−1}` given. This module proves, for a general smooth payoff, on a genuine
probability space whose information may grow forever:

* `foc_of_optimalIn` (**necessity**): if `q` is optimal within any class of plans that contains
  the one-date perturbations `q_t + εz` (`z` bounded and known at `t`, `ε` small), then the
  first-order condition (Euler equation of the price setter)
  `Φ₁(q_t, q_{t−1}, θ_t) + βE_t Φ₂(q_{t+1}, q_t, θ_{t+1}) = 0` holds almost surely (`FOC`). The
  proof differentiates expected payoff under the integral sign.
* `partial_le` and `value_le_of_foc` (**sufficiency**): if the FOC holds at every date and the
  payoff satisfies the supergradient (concavity) inequality between `q` and a competitor `q′`,
  then `value q′ − value q` is bounded by the limit of the terminal terms
  `βᵀE[Φ₁(q_T, q_{T−1}, θ_T)(q′_T − q_T)]`; with the transversality condition (`Tendsto … 0`),
  `q′` does no better.
* `tvc_of_ubdd`: for uniformly bounded plans and data and `β < 1` the transversality condition
  holds automatically; `optimal_iff_foc`: within the class `UPlan` of uniformly bounded plans,
  for a payoff concave in `(q_t, q_{t−1})`, optimality is equivalent to the FOC at every date.
* `value_eq_integral_tsum`: the value is the genuine expectation `E ∑ βᵗΦ_t`.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6PriceSetting

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}
variable {V : Type*}

/-! ### Plans, payoffs and values -/

/-- Cochrane (2023), p. 118 ("costs of changing prices"): last period's choice, `q_{t−1}`, with
`q_{−1} = q₀` given. -/
def lag (q0 : Ω → ℝ) (q : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => q0
  | t + 1 => q t

/-- Cochrane (2023), p. 118: the period payoff `Φ(q_t, q_{t−1}, θ_t)` of the plan `q`. -/
def pay (Φ : ℝ → ℝ → V → ℝ) (θ : ℕ → Ω → V) (q0 : Ω → ℝ) (q : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ω => Φ (q t ω) (lag q0 q t ω) (θ t ω)

variable (S) in
/-- Cochrane (2023), p. 118: a plan whose expected discounted payoff converges absolutely: every
period payoff is integrable and `∑ βᵗE|Φ_t| < ∞`. -/
def Admissible (β : ℝ) (Φ : ℝ → ℝ → V → ℝ) (θ : ℕ → Ω → V) (q0 : Ω → ℝ)
    (q : ℕ → Ω → ℝ) : Prop :=
  (∀ t, Integrable (pay Φ θ q0 q t) S.μ) ∧
    Summable fun t => β ^ t * ∫ ω, |pay Φ θ q0 q t ω| ∂S.μ

variable (S) in
/-- Cochrane (2023), p. 118: the value `∑ₜ βᵗ E Φ(q_t, q_{t−1}, θ_t)` of a plan. -/
noncomputable def value (β : ℝ) (Φ : ℝ → ℝ → V → ℝ) (θ : ℕ → Ω → V) (q0 : Ω → ℝ)
    (q : ℕ → Ω → ℝ) : ℝ :=
  ∑' t, β ^ t * ∫ ω, pay Φ θ q0 q t ω ∂S.μ

variable (S) in
/-- Cochrane (2023), p. 118: a plan of the price setter, adapted (the price set at `t` is
chosen with date-`t` information) and essentially bounded at every date. -/
def Plan (q : ℕ → Ω → ℝ) : Prop := StronglyAdapted S.𝓕 q ∧ ∀ t, BddAt S (q t)

variable (S) in
/-- Cochrane (2023), p. 118: a uniformly bounded plan. -/
def UPlan (q : ℕ → Ω → ℝ) : Prop := Plan S q ∧ ∃ R, ∀ t, ∀ᵐ ω ∂S.μ, |q t ω| ≤ R

variable (S) in
/-- Cochrane (2023), p. 118: `q` is optimal within the class `C` of plans: `q ∈ C` is admissible
and no admissible plan in `C` has a higher value. -/
def OptimalIn (C : (ℕ → Ω → ℝ) → Prop) (β : ℝ) (Φ : ℝ → ℝ → V → ℝ) (θ : ℕ → Ω → V)
    (q0 : Ω → ℝ) (q : ℕ → Ω → ℝ) : Prop :=
  C q ∧ Admissible S β Φ θ q0 q ∧
    ∀ q', C q' → Admissible S β Φ θ q0 q' → value S β Φ θ q0 q' ≤ value S β Φ θ q0 q

/-- Cochrane (2023), p. 118: the regularity of the payoff: `Φ` has partial derivatives `D₁`
(own current price) and `D₂` (own last price) everywhere, and `Φ`, `D₁`, `D₂` are jointly
continuous. -/
def Smooth [TopologicalSpace V] (Φ D1 D2 : ℝ → ℝ → V → ℝ) : Prop :=
  (∀ a b v, HasDerivAt (fun a => Φ a b v) (D1 a b v) a) ∧
    (∀ a b v, HasDerivAt (fun b => Φ a b v) (D2 a b v) b) ∧
    Continuous (fun p : ℝ × ℝ × V => Φ p.1 p.2.1 p.2.2) ∧
    Continuous (fun p : ℝ × ℝ × V => D1 p.1 p.2.1 p.2.2) ∧
    Continuous (fun p : ℝ × ℝ × V => D2 p.1 p.2.1 p.2.2)

variable (S) in
/-- Cochrane (2023), p. 118: the aggregate data are known at `t` and essentially bounded at
every date. -/
def DataReg [NormedAddCommGroup V] (θ : ℕ → Ω → V) : Prop :=
  StronglyAdapted S.𝓕 θ ∧ ∀ t, ∃ K, ∀ᵐ ω ∂S.μ, ‖θ t ω‖ ≤ K

variable (S) in
/-- Cochrane (2023), p. 118 and eq. (17.17), p. 407: the price setter's first-order condition
at `t`, `Φ₁(q_t, q_{t−1}, θ_t) + βE_tΦ₂(q_{t+1}, q_t, θ_{t+1}) = 0` almost surely. -/
def FOC (β : ℝ) (D1 D2 : ℝ → ℝ → V → ℝ) (θ : ℕ → Ω → V) (q0 : Ω → ℝ) (q : ℕ → Ω → ℝ)
    (t : ℕ) : Prop :=
  ∀ᵐ ω ∂S.μ, D1 (q t ω) (lag q0 q t ω) (θ t ω) +
    β * S.E t (fun ω => D2 (q (t + 1) ω) (q t ω) (θ (t + 1) ω)) ω = 0

/-! ### Measurability and bounds -/

/-- Cochrane (2023), p. 118: last period's price is known at `t`. -/
theorem lag_sm {q0 : Ω → ℝ} {q : ℕ → Ω → ℝ} (hq0 : StronglyMeasurable[S.𝓕 0] q0)
    (hq : StronglyAdapted S.𝓕 q) (t : ℕ) : StronglyMeasurable[S.𝓕 t] (lag q0 q t) := by
  cases t with
  | zero => exact hq0
  | succ n => exact (hq n).mono (S.𝓕.mono (Nat.le_succ n))

/-- Cochrane (2023), p. 118: last period's price is essentially bounded. -/
theorem lag_bdd {q0 : Ω → ℝ} {q : ℕ → Ω → ℝ} (hq0 : BddAt S q0) (hq : ∀ t, BddAt S (q t))
    (t : ℕ) : BddAt S (lag q0 q t) := by
  cases t with
  | zero => exact hq0
  | succ n => exact hq n

/-- Cochrane (2023), p. 118: a continuous function of variables known at `t` is known at `t`. -/
theorem sm_comp [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] {G : ℝ × ℝ × V → ℝ} (hG : Continuous G) {t : ℕ} {a b : Ω → ℝ}
    {v : Ω → V}
    (ha : StronglyMeasurable[S.𝓕 t] a) (hb : StronglyMeasurable[S.𝓕 t] b)
    (hv : StronglyMeasurable[S.𝓕 t] v) :
    StronglyMeasurable[S.𝓕 t] fun ω => G (a ω, b ω, v ω) :=
  (hG.measurable.comp
    (ha.measurable.prodMk (hb.measurable.prodMk hv.measurable))).stronglyMeasurable

/-- Cochrane (2023), p. 118: a continuous function is bounded on the box
`|a|, |b| ≤ R`, `‖v‖ ≤ K`. -/
theorem exists_box_bound [NormedAddCommGroup V] [ProperSpace V] {G : ℝ × ℝ × V → ℝ}
    (hG : Continuous G) (R K : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ a b v, |a| ≤ R → |b| ≤ R → ‖v‖ ≤ K → |G (a, b, v)| ≤ M := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := -R) (b := R)).prod ((isCompact_Icc (a := -R)
    (b := R)).prod (isCompact_closedBall (0 : V) K))).exists_bound_of_continuousOn
    hG.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun a b v ha hb hv => ?_⟩
  have := hC (a, b, v) ⟨Set.mem_Icc.2 (abs_le.1 ha), Set.mem_Icc.2 (abs_le.1 hb),
    mem_closedBall_zero_iff.2 hv⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- Cochrane (2023), p. 118: a continuous function of essentially bounded variables is
essentially bounded. -/
theorem bddAt_comp [NormedAddCommGroup V] [ProperSpace V] {G : ℝ × ℝ × V → ℝ}
    (hG : Continuous G) {a b : Ω → ℝ} {v : Ω → V}
    (ha : BddAt S a) (hb : BddAt S b) (hv : ∃ K, ∀ᵐ ω ∂S.μ, ‖v ω‖ ≤ K) :
    BddAt S fun ω => G (a ω, b ω, v ω) := by
  obtain ⟨Ra, hRa⟩ := ha
  obtain ⟨Rb, hRb⟩ := hb
  obtain ⟨K, hK⟩ := hv
  obtain ⟨M, -, hM⟩ := exists_box_bound hG (max Ra Rb) K
  refine ⟨M, ?_⟩
  filter_upwards [hRa, hRb, hK] with ω h1 h2 h3
  exact hM _ _ _ (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _)) h3

/-- Cochrane (2023), p. 118: the period payoff is known at `t`. -/
theorem pay_sm [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] {Φ : ℝ → ℝ → V → ℝ}
    (hΦ : Continuous (fun p : ℝ × ℝ × V => Φ p.1 p.2.1 p.2.2))
    {θ : ℕ → Ω → V} (hθ : DataReg S θ) {q0 : Ω → ℝ} (hq0 : StronglyMeasurable[S.𝓕 0] q0)
    {q : ℕ → Ω → ℝ} (hq : StronglyAdapted S.𝓕 q) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (pay Φ θ q0 q t) :=
  sm_comp hΦ (hq t) (lag_sm hq0 hq t) (hθ.1 t)

/-- Cochrane (2023), p. 118: the period payoff of a plan is integrable. -/
theorem pay_integrable [NormedAddCommGroup V] [ProperSpace V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {Φ : ℝ → ℝ → V → ℝ}
    (hΦ : Continuous (fun p : ℝ × ℝ × V => Φ p.1 p.2.1 p.2.2)) {θ : ℕ → Ω → V}
    (hθ : DataReg S θ) {q0 : Ω → ℝ} (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0)
    {q : ℕ → Ω → ℝ} (hq : Plan S q) (t : ℕ) : Integrable (pay Φ θ q0 q t) S.μ :=
  (bddAt_comp hΦ (hq.2 t) (lag_bdd hq0b hq.2 t) (hθ.2 t)).integrable
    ((pay_sm hΦ hθ hq0 hq.1 t).mono (S.𝓕.le t)).aestronglyMeasurable

/-- Cochrane (2023), p. 118: the discounted expected payoffs of an admissible plan are summable
(`β ≥ 0`). -/
theorem Admissible.summable {β : ℝ} (hβ : 0 ≤ β) {Φ : ℝ → ℝ → V → ℝ} {θ : ℕ → Ω → V}
    {q0 : Ω → ℝ} {q : ℕ → Ω → ℝ} (h : Admissible S β Φ θ q0 q) :
    Summable fun t => β ^ t * ∫ ω, pay Φ θ q0 q t ω ∂S.μ :=
  Summable.of_norm_bounded h.2 fun t => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ t)]
    exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (pow_nonneg hβ t)

/-- Cochrane (2023), p. 118: the value is the genuine expectation of the discounted payoff
stream, `∑ₜ βᵗ E Φ_t = E ∑ₜ βᵗ Φ_t`. -/
theorem value_eq_integral_tsum {β : ℝ} (hβ : 0 ≤ β) {Φ : ℝ → ℝ → V → ℝ} {θ : ℕ → Ω → V}
    {q0 : Ω → ℝ} {q : ℕ → Ω → ℝ} (h : Admissible S β Φ θ q0 q) :
    value S β Φ θ q0 q = ∫ ω, ∑' t, β ^ t * pay Φ θ q0 q t ω ∂S.μ := by
  rw [value, ← integral_tsum_of_summable_integral_norm (fun t => (h.1 t).const_mul _)]
  · simp_rw [integral_const_mul]
  · refine h.2.congr fun t => ?_
    simp_rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ t), integral_const_mul]

/-! ### One-date perturbations -/

/-- Cochrane (2023), p. 118: the plan `q` with the date-`t` price moved to `q_t + εz`. -/
def perturb (q : ℕ → Ω → ℝ) (z : Ω → ℝ) (t : ℕ) (ε : ℝ) : ℕ → Ω → ℝ :=
  fun n ω => if n = t then q t ω + ε * z ω else q n ω

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: the perturbation leaves other dates unchanged. -/
theorem perturb_ne {q : ℕ → Ω → ℝ} {z : Ω → ℝ} {t n : ℕ} {ε : ℝ} (hn : n ≠ t) :
    perturb q z t ε n = q n := by
  funext ω
  simp [perturb, hn]

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: the perturbed date-`t` price. -/
theorem perturb_self (q : ℕ → Ω → ℝ) (z : Ω → ℝ) (t : ℕ) (ε : ℝ) :
    perturb q z t ε t = fun ω => q t ω + ε * z ω := by
  funext ω
  simp [perturb]

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: the perturbation changes last period's price only at `t + 1`. -/
theorem lag_perturb_ne {q0 : Ω → ℝ} {q : ℕ → Ω → ℝ} {z : Ω → ℝ} {t n : ℕ} {ε : ℝ}
    (hn : n ≠ t + 1) : lag q0 (perturb q z t ε) n = lag q0 q n := by
  cases n with
  | zero => rfl
  | succ m => exact perturb_ne (by omega)

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: the payoff changes only at `t` and `t + 1`. -/
theorem pay_perturb_other {Φ : ℝ → ℝ → V → ℝ} {θ : ℕ → Ω → V} {q0 : Ω → ℝ}
    {q : ℕ → Ω → ℝ} {z : Ω → ℝ} {t n : ℕ} {ε : ℝ} (hn : n ≠ t) (hn1 : n ≠ t + 1) :
    pay Φ θ q0 (perturb q z t ε) n = pay Φ θ q0 q n := by
  funext ω
  simp only [pay, perturb_ne hn, lag_perturb_ne hn1]

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: the perturbed payoff at `t`. -/
theorem pay_perturb_t (Φ : ℝ → ℝ → V → ℝ) (θ : ℕ → Ω → V) (q0 : Ω → ℝ) (q : ℕ → Ω → ℝ)
    (z : Ω → ℝ) (t : ℕ) (ε : ℝ) :
    pay Φ θ q0 (perturb q z t ε) t =
      fun ω => Φ (q t ω + ε * z ω) (lag q0 q t ω) (θ t ω) := by
  funext ω
  simp only [pay, perturb_self, lag_perturb_ne (show t ≠ t + 1 by omega)]

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: the perturbed payoff at `t + 1` (the cost of changing the price
from the perturbed `q_t`). -/
theorem pay_perturb_succ (Φ : ℝ → ℝ → V → ℝ) (θ : ℕ → Ω → V) (q0 : Ω → ℝ)
    (q : ℕ → Ω → ℝ) (z : Ω → ℝ) (t : ℕ) (ε : ℝ) :
    pay Φ θ q0 (perturb q z t ε) (t + 1) =
      fun ω => Φ (q (t + 1) ω) (q t ω + ε * z ω) (θ (t + 1) ω) := by
  funext ω
  simp only [pay, perturb_ne (show t + 1 ≠ t by omega), lag, perturb_self]

/-- Cochrane (2023), p. 118: a perturbation of a plan by a bounded variable known at `t` is a
plan. -/
theorem plan_perturb {q : ℕ → Ω → ℝ} (hq : Plan S q) {t : ℕ} {z : Ω → ℝ}
    (hz : StronglyMeasurable[S.𝓕 t] z) (hzb : BddAt S z) (ε : ℝ) :
    Plan S (perturb q z t ε) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · by_cases hn : n = t
    · subst hn
      rw [perturb_self]
      exact (hq.1 n).add (hz.const_mul ε)
    · rw [perturb_ne hn]
      exact hq.1 n
  · by_cases hn : n = t
    · subst hn
      rw [perturb_self]
      exact (hq.2 n).add ((BddAt.const ε).mul hzb)
    · rw [perturb_ne hn]
      exact hq.2 n

/-- Cochrane (2023), p. 118: a perturbation of a uniformly bounded plan is uniformly bounded. -/
theorem uplan_perturb {q : ℕ → Ω → ℝ} (hq : UPlan S q) {t : ℕ} {z : Ω → ℝ}
    (hz : StronglyMeasurable[S.𝓕 t] z) (hzb : BddAt S z) (ε : ℝ) :
    UPlan S (perturb q z t ε) := by
  obtain ⟨R, hR⟩ := hq.2
  obtain ⟨K, hK⟩ := hzb
  refine ⟨plan_perturb hq.1 hz ⟨K, hK⟩ ε, R + |ε| * K, fun n => ?_⟩
  have hK0 : ∀ᵐ ω ∂S.μ, 0 ≤ |ε| * K := hK.mono fun ω h =>
    mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans h)
  by_cases hn : n = t
  · subst hn
    rw [perturb_self]
    filter_upwards [hR n, hK] with ω h1 h2
    calc |q n ω + ε * z ω| ≤ |q n ω| + |ε| * |z ω| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ R + |ε| * K := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
  · rw [perturb_ne hn]
    filter_upwards [hR n, hK0] with ω h1 h2
    linarith

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: the zero perturbation is the plan itself. -/
theorem perturb_zero (q : ℕ → Ω → ℝ) (z : Ω → ℝ) (t : ℕ) : perturb q z t 0 = q := by
  funext n ω
  by_cases hn : n = t
  · subst hn
    simp [perturb]
  · simp [perturb, hn]

/-- Cochrane (2023), p. 118: a one-date perturbation of an admissible plan is admissible. -/
theorem admissible_perturb [NormedAddCommGroup V] [ProperSpace V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {β : ℝ} {Φ : ℝ → ℝ → V → ℝ}
    (hΦ : Continuous (fun p : ℝ × ℝ × V => Φ p.1 p.2.1 p.2.2)) {θ : ℕ → Ω → V}
    (hθ : DataReg S θ) {q0 : Ω → ℝ} (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0)
    {q : ℕ → Ω → ℝ} (hq : Plan S q) (hadm : Admissible S β Φ θ q0 q) {t : ℕ} {z : Ω → ℝ}
    (hz : StronglyMeasurable[S.𝓕 t] z) (hzb : BddAt S z) (ε : ℝ) :
    Admissible S β Φ θ q0 (perturb q z t ε) := by
  refine ⟨pay_integrable hΦ hθ hq0 hq0b (plan_perturb hq hz hzb ε), ?_⟩
  refine (hasSum_of_eq_off_finset hadm.2 {t, t + 1} fun n hn => ?_).summable
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  rw [pay_perturb_other hn.1 hn.2]

/-- Cochrane (2023), p. 118: the value of a one-date perturbation differs from the value of the
plan only through the payoffs at `t` and `t + 1`. -/
theorem value_perturb {β : ℝ} (hβ : 0 ≤ β) {Φ : ℝ → ℝ → V → ℝ} {θ : ℕ → Ω → V} {q0 : Ω → ℝ}
    {q : ℕ → Ω → ℝ} (hadm : Admissible S β Φ θ q0 q) (z : Ω → ℝ) (t : ℕ) (ε : ℝ) :
    value S β Φ θ q0 (perturb q z t ε) = value S β Φ θ q0 q +
      (β ^ t * (∫ ω, pay Φ θ q0 (perturb q z t ε) t ω ∂S.μ - ∫ ω, pay Φ θ q0 q t ω ∂S.μ) +
        β ^ (t + 1) * (∫ ω, pay Φ θ q0 (perturb q z t ε) (t + 1) ω ∂S.μ -
          ∫ ω, pay Φ θ q0 q (t + 1) ω ∂S.μ)) := by
  have h := hasSum_of_eq_off_finset (hadm.summable hβ) {t, t + 1}
    (f' := fun n => β ^ n * ∫ ω, pay Φ θ q0 (perturb q z t ε) n ω ∂S.μ) fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      rw [pay_perturb_other hn.1 hn.2]
  rw [value, h.tsum_eq, Finset.sum_pair (show t ≠ t + 1 by omega), value]
  ring

/-! ### Necessity of the first-order condition -/

/-- Cochrane (2023), p. 118 ("the first-order condition for monopolistically-competitive price
setters"), in variational form: if `q` is optimal within a class `C` containing every small
one-date perturbation at `t` by bounded variables known at `t`, then for every such `z`,
`E[z (Φ₁(q_t, q_{t−1}, θ_t) + βΦ₂(q_{t+1}, q_t, θ_{t+1}))] = 0`. The proof differentiates the
expected payoff under the integral sign. -/
theorem integral_mul_gap [NormedAddCommGroup V] [ProperSpace V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {β : ℝ} (hβ : 0 < β)
    {Φ D1 D2 : ℝ → ℝ → V → ℝ} (hs : Smooth Φ D1 D2) {θ : ℕ → Ω → V} (hθ : DataReg S θ)
    {q0 : Ω → ℝ} (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0)
    {C : (ℕ → Ω → ℝ) → Prop} {q : ℕ → Ω → ℝ} (hq : Plan S q)
    (hopt : OptimalIn S C β Φ θ q0 q) {t : ℕ} {z : Ω → ℝ} (hz : StronglyMeasurable[S.𝓕 t] z)
    (hzb : BddAt S z) (hC : ∀ᶠ ε in 𝓝 (0 : ℝ), C (perturb q z t ε)) :
    ∫ ω, z ω * (D1 (q t ω) (lag q0 q t ω) (θ t ω) +
      β * D2 (q (t + 1) ω) (q t ω) (θ (t + 1) ω)) ∂S.μ = 0 := by
  obtain ⟨hD1, hD2, hΦc, hD1c, hD2c⟩ := hs
  set F : ℝ → Ω → ℝ := fun ε ω => β ^ t * Φ (q t ω + ε * z ω) (lag q0 q t ω) (θ t ω) +
    β ^ (t + 1) * Φ (q (t + 1) ω) (q t ω + ε * z ω) (θ (t + 1) ω) with hFdef
  set F' : ℝ → Ω → ℝ := fun ε ω =>
    (β ^ t * D1 (q t ω + ε * z ω) (lag q0 q t ω) (θ t ω) +
      β ^ (t + 1) * D2 (q (t + 1) ω) (q t ω + ε * z ω) (θ (t + 1) ω)) * z ω with hF'def
  have hFeq : ∀ ε, F ε = fun ω => β ^ t * pay Φ θ q0 (perturb q z t ε) t ω +
      β ^ (t + 1) * pay Φ θ q0 (perturb q z t ε) (t + 1) ω := fun ε => by
    rw [pay_perturb_t, pay_perturb_succ]
  have hint : ∀ ε n, Integrable (pay Φ θ q0 (perturb q z t ε) n) S.μ := fun ε =>
    pay_integrable hΦc hθ hq0 hq0b (plan_perturb hq hz hzb ε)
  have hFi : ∀ ε, Integrable (F ε) S.μ := fun ε => by
    rw [hFeq]
    exact ((hint ε t).const_mul _).add ((hint ε (t + 1)).const_mul _)
  have hFint : ∀ ε, ∫ ω, F ε ω ∂S.μ = β ^ t * ∫ ω, pay Φ θ q0 (perturb q z t ε) t ω ∂S.μ +
      β ^ (t + 1) * ∫ ω, pay Φ θ q0 (perturb q z t ε) (t + 1) ω ∂S.μ := fun ε => by
    rw [hFeq, integral_add ((hint ε t).const_mul _) ((hint ε (t + 1)).const_mul _),
      integral_const_mul, integral_const_mul]
  -- the value difference
  have hval : ∀ ε, value S β Φ θ q0 (perturb q z t ε) - value S β Φ θ q0 q =
      ∫ ω, F ε ω ∂S.μ - ∫ ω, F 0 ω ∂S.μ := fun ε => by
    rw [value_perturb hβ.le hopt.2.1 z t ε, hFint, hFint, perturb_zero]
    ring
  have hmax : IsLocalMax (fun ε => ∫ ω, F ε ω ∂S.μ) 0 := by
    filter_upwards [hC] with ε hε
    have h1 := hopt.2.2 _ hε (admissible_perturb hΦc hθ hq0 hq0b hq hopt.2.1 hz hzb ε)
    have h2 := hval ε
    linarith
  -- bounds
  obtain ⟨R1, hR1⟩ := hq.2 t
  obtain ⟨R2, hR2⟩ := lag_bdd hq0b hq.2 t
  obtain ⟨R3, hR3⟩ := hq.2 (t + 1)
  obtain ⟨K1, hK1⟩ := hθ.2 t
  obtain ⟨K2, hK2⟩ := hθ.2 (t + 1)
  obtain ⟨Kz, hKz0, hKz⟩ := hzb.exists_pos
  set R := max (max R1 R2) R3 + Kz
  set K := max K1 K2
  obtain ⟨M1, hM10, hM1⟩ := exists_box_bound hD1c R K
  obtain ⟨M2, hM20, hM2⟩ := exists_box_bound hD2c R K
  have hqm : ∀ ε, StronglyMeasurable[S.𝓕 t] fun ω => q t ω + ε * z ω := fun ε =>
    (hq.1 t).add (hz.const_mul ε)
  have hF'm : AEStronglyMeasurable (F' 0) S.μ := by
    have h1 := sm_comp hD1c (hqm 0) (lag_sm hq0 hq.1 t) (hθ.1 t)
    have h2 := sm_comp hD2c (hq.1 (t + 1)) ((hqm 0).mono (S.𝓕.mono (Nat.le_succ t)))
      (hθ.1 (t + 1))
    exact ((((h1.mono (S.𝓕.le t)).const_mul (β ^ t)).add
      ((h2.mono (S.𝓕.le (t + 1))).const_mul (β ^ (t + 1)))).mul
      (hz.mono (S.𝓕.le t))).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := S.μ) (x₀ := (0 : ℝ))
    (F := F) (F' := F') (bound := fun _ => (β ^ t * M1 + β ^ (t + 1) * M2) * Kz)
    (s := Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun ε => (hFi ε).aestronglyMeasurable) (hFi 0) hF'm ?_
    (integrable_const _) ?_
  · have h0 := hmax.hasDerivAt_eq_zero key.2
    have e : ∀ ω, F' 0 ω = β ^ t * (z ω * (D1 (q t ω) (lag q0 q t ω) (θ t ω) +
        β * D2 (q (t + 1) ω) (q t ω) (θ (t + 1) ω))) := fun ω => by
      simp only [hF'def, zero_mul, add_zero]
      ring
    simp_rw [e, integral_const_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero t hβ.ne')
  · filter_upwards [hR1, hR2, hR3, hK1, hK2, hKz] with ω h1 h2 h3 h4 h5 h6
    intro ε hε
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
    have hqe : |q t ω + ε * z ω| ≤ R := by
      calc |q t ω + ε * z ω| ≤ |q t ω| + |ε| * |z ω| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ max (max R1 R2) R3 + 1 * Kz := add_le_add
            (h1.trans ((le_max_left _ _).trans (le_max_left _ _)))
            (mul_le_mul hε.le h6 (abs_nonneg _) zero_le_one)
        _ = R := by ring
    have hR0 : max (max R1 R2) R3 ≤ R := by linarith
    have hl : |lag q0 q t ω| ≤ R :=
      h2.trans (((le_max_right _ _).trans (le_max_left _ _)).trans hR0)
    have hq1 : |q (t + 1) ω| ≤ R := h3.trans ((le_max_right _ _).trans hR0)
    have b1 := hM1 _ _ _ hqe hl (h4.trans (le_max_left _ _))
    have b2 := hM2 _ _ _ hq1 hqe (h5.trans (le_max_right _ _))
    simp only [hF'def, Real.norm_eq_abs, abs_mul]
    have hb1 : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have hb2 : 0 ≤ β ^ (t + 1) := pow_nonneg hβ.le (t + 1)
    refine mul_le_mul ((abs_add_le _ _).trans (add_le_add ?_ ?_)) h6 (abs_nonneg _)
      (by positivity)
    · rw [abs_mul, abs_of_nonneg hb1]
      exact mul_le_mul_of_nonneg_left b1 hb1
    · rw [abs_mul, abs_of_nonneg hb2]
      exact mul_le_mul_of_nonneg_left b2 hb2
  · refine Eventually.of_forall fun ω ε _ => ?_
    have ha : HasDerivAt (fun ε => q t ω + ε * z ω) (z ω) ε := by
      simpa using (hasDerivAt_mul_const (z ω)).const_add (q t ω)
    have h1 := (hD1 (q t ω + ε * z ω) (lag q0 q t ω) (θ t ω)).comp ε ha
    have h2 := (hD2 (q (t + 1) ω) (q t ω + ε * z ω) (θ (t + 1) ω)).comp ε ha
    exact ((h1.const_mul (β ^ t)).add (h2.const_mul (β ^ (t + 1)))).congr_deriv (by
      simp only [hF'def]
      ring)

/-- Cochrane (2023), p. 118 and eq. (17.17), p. 407, **necessity of the price setter's
first-order condition**: if `q` is optimal within a class `C` that contains every small one-date
perturbation at `t` by a bounded variable known at `t` (`hC`), then the FOC
`Φ₁(q_t, q_{t−1}, θ_t) + βE_tΦ₂(q_{t+1}, q_t, θ_{t+1}) = 0` holds almost surely at `t`. -/
theorem foc_of_optimalIn [NormedAddCommGroup V] [ProperSpace V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {β : ℝ} (hβ : 0 < β)
    {Φ D1 D2 : ℝ → ℝ → V → ℝ} (hs : Smooth Φ D1 D2) {θ : ℕ → Ω → V} (hθ : DataReg S θ)
    {q0 : Ω → ℝ} (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0)
    {C : (ℕ → Ω → ℝ) → Prop} {q : ℕ → Ω → ℝ} (hq : Plan S q)
    (hopt : OptimalIn S C β Φ θ q0 q) {t : ℕ}
    (hC : ∀ z : Ω → ℝ, StronglyMeasurable[S.𝓕 t] z → BddAt S z →
      ∀ᶠ ε in 𝓝 (0 : ℝ), C (perturb q z t ε)) :
    FOC S β D1 D2 θ q0 q t := by
  have hD1c := hs.2.2.2.1
  have hD2c := hs.2.2.2.2
  set a : Ω → ℝ := fun ω => D1 (q t ω) (lag q0 q t ω) (θ t ω) with hadef
  set d : Ω → ℝ := fun ω => D2 (q (t + 1) ω) (q t ω) (θ (t + 1) ω) with hddef
  have ham : StronglyMeasurable[S.𝓕 t] a := sm_comp hD1c (hq.1 t) (lag_sm hq0 hq.1 t) (hθ.1 t)
  have hab : BddAt S a := bddAt_comp hD1c (hq.2 t) (lag_bdd hq0b hq.2 t) (hθ.2 t)
  have hdm : StronglyMeasurable[S.𝓕 (t + 1)] d :=
    sm_comp hD2c (hq.1 (t + 1)) ((hq.1 t).mono (S.𝓕.mono (Nat.le_succ t))) (hθ.1 (t + 1))
  have hdb : BddAt S d := bddAt_comp hD2c (hq.2 (t + 1)) (hq.2 t) (hθ.2 (t + 1))
  have hai : Integrable a S.μ := hab.integrable (ham.mono (S.𝓕.le t)).aestronglyMeasurable
  have hdi : Integrable d S.μ :=
    hdb.integrable (hdm.mono (S.𝓕.le (t + 1))).aestronglyMeasurable
  have hGi : Integrable (a + β • d) S.μ := hai.add (hdi.smul β)
  set w : Ω → ℝ := S.E t (a + β • d) with hwdef
  have hwm : StronglyMeasurable[S.𝓕 t] w := S.stronglyMeasurable_E t _
  have hwb : BddAt S w := by
    have e : a + β • d = fun ω => a ω + β * d ω := by
      funext ω
      simp
    have : BddAt S (a + β • d) := e ▸ hab.add ((BddAt.const β).mul hdb)
    exact this.E t
  obtain ⟨Kw, hKw⟩ := hwb
  have h0 := integral_mul_gap hβ hs hθ hq0 hq0b hq hopt hwm ⟨Kw, hKw⟩ (hC w hwm ⟨Kw, hKw⟩)
  have e1 : ∫ ω, w ω * (a + β • d) ω ∂S.μ = ∫ ω, w ω * w ω ∂S.μ := by
    rw [integral_mul_E hwm hKw hGi]
  have e2 : ∫ ω, w ω * (a + β • d) ω ∂S.μ = 0 := by
    rw [← h0]
    rfl
  have hsq : Integrable (fun ω => w ω * w ω) S.μ := by
    have hwi : Integrable w S.μ := S.integrable_E t _
    exact hwi.bdd_mul (hwm.mono (S.𝓕.le t)).aestronglyMeasurable
      (hKw.mono fun ω h => by rwa [Real.norm_eq_abs])
  have hz : (fun ω => w ω * w ω) =ᵐ[S.μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => mul_self_nonneg (w ω)) hsq).1 (e1 ▸ e2)
  have hEa : S.E t a = a := S.E_of_stronglyMeasurable ham hai
  filter_upwards [hz, S.E_add hai (hdi.smul β) t, S.E_smul β d t] with ω h1 h2 h3
  have hw0 : w ω = 0 := mul_self_eq_zero.1 h1
  rw [hwdef, h2, Pi.add_apply, hEa, h3, Pi.smul_apply, smul_eq_mul] at hw0
  exact hw0

/-- Cochrane (2023), p. 118: within the class of all plans (`Plan`), every one-date perturbation
is again a plan, so an optimal plan satisfies the FOC at every date. -/
theorem foc_of_optimal [NormedAddCommGroup V] [ProperSpace V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {β : ℝ} (hβ : 0 < β)
    {Φ D1 D2 : ℝ → ℝ → V → ℝ} (hs : Smooth Φ D1 D2) {θ : ℕ → Ω → V} (hθ : DataReg S θ)
    {q0 : Ω → ℝ} (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0) {q : ℕ → Ω → ℝ}
    (hopt : OptimalIn S (Plan S) β Φ θ q0 q) (t : ℕ) : FOC S β D1 D2 θ q0 q t :=
  foc_of_optimalIn hβ hs hθ hq0 hq0b hopt.1 hopt fun _ hz hzb =>
    Eventually.of_forall fun ε => plan_perturb hopt.1 hz hzb ε

/-- Cochrane (2023), p. 118: the same within the class `UPlan` of uniformly bounded plans. -/
theorem foc_of_optimal_u [NormedAddCommGroup V] [ProperSpace V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {β : ℝ} (hβ : 0 < β)
    {Φ D1 D2 : ℝ → ℝ → V → ℝ} (hs : Smooth Φ D1 D2) {θ : ℕ → Ω → V} (hθ : DataReg S θ)
    {q0 : Ω → ℝ} (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0) {q : ℕ → Ω → ℝ}
    (hopt : OptimalIn S (UPlan S) β Φ θ q0 q) (t : ℕ) : FOC S β D1 D2 θ q0 q t :=
  foc_of_optimalIn hβ hs hθ hq0 hq0b hopt.1.1 hopt fun _ hz hzb =>
    Eventually.of_forall fun ε => uplan_perturb hopt.1 hz hzb ε

/-! ### Sufficiency -/

variable (S) in
/-- Cochrane (2023), p. 118: the supergradient (concavity) inequality at `t` between the plan `q`
and a competitor `q′`: almost surely
`Φ(q′_t, q′_{t−1}, θ_t) ≤ Φ(q_t, q_{t−1}, θ_t) + Φ₁·(q′_t − q_t) + Φ₂·(q′_{t−1} − q_{t−1})`. -/
def SuperGrad (Φ D1 D2 : ℝ → ℝ → V → ℝ) (θ : ℕ → Ω → V) (q0 : Ω → ℝ) (q q' : ℕ → Ω → ℝ)
    (t : ℕ) : Prop :=
  ∀ᵐ ω ∂S.μ, Φ (q' t ω) (lag q0 q' t ω) (θ t ω) ≤ Φ (q t ω) (lag q0 q t ω) (θ t ω) +
    D1 (q t ω) (lag q0 q t ω) (θ t ω) * (q' t ω - q t ω) +
      D2 (q t ω) (lag q0 q t ω) (θ t ω) * (lag q0 q' t ω - lag q0 q t ω)

/-- Cochrane (2023), p. 118: the payoff is concave in `(q_t, q_{t−1})` in tangent form: for every
datum, `Φ(a′, b′) ≤ Φ(a, b) + Φ₁(a, b)(a′ − a) + Φ₂(a, b)(b′ − b)`. -/
def TangentConcave (Φ D1 D2 : ℝ → ℝ → V → ℝ) : Prop :=
  ∀ a b a' b' v, Φ a' b' v ≤ Φ a b v + D1 a b v * (a' - a) + D2 a b v * (b' - b)

/-- Cochrane (2023), p. 118, **sufficiency, finite horizon**: if `q` satisfies the FOC at every
date and the supergradient inequality holds against the admissible competitor `q′` at every date
(both plans, same `q_{−1}`), then the discounted gain of `q′` over the dates `0, …, T` is at most
the terminal term `βᵀE[Φ₁(q_T, q_{T−1}, θ_T)(q′_T − q_T)]`. -/
theorem partial_le [NormedAddCommGroup V] [ProperSpace V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {β : ℝ} (hβ : 0 < β)
    {Φ D1 D2 : ℝ → ℝ → V → ℝ} (hs : Smooth Φ D1 D2) {θ : ℕ → Ω → V} (hθ : DataReg S θ)
    {q0 : Ω → ℝ} (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0)
    {q q' : ℕ → Ω → ℝ} (hq : Plan S q) (hq' : Plan S q')
    (hfoc : ∀ t, FOC S β D1 D2 θ q0 q t) (hsg : ∀ t, SuperGrad S Φ D1 D2 θ q0 q q' t) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * (∫ ω, pay Φ θ q0 q' t ω ∂S.μ -
      ∫ ω, pay Φ θ q0 q t ω ∂S.μ) ≤
      β ^ T * ∫ ω, D1 (q T ω) (lag q0 q T ω) (θ T ω) * (q' T ω - q T ω) ∂S.μ := by
  obtain ⟨-, -, hΦc, hD1c, hD2c⟩ := hs
  -- integrability of the ingredients
  have hpi := pay_integrable hΦc hθ hq0 hq0b hq
  have hpi' := pay_integrable hΦc hθ hq0 hq0b hq'
  have hint : ∀ {G : ℝ × ℝ × V → ℝ}, Continuous G → ∀ {t s : ℕ} {a b x : Ω → ℝ},
      StronglyMeasurable[S.𝓕 t] a → StronglyMeasurable[S.𝓕 t] b → BddAt S a → BddAt S b →
      t ≤ s → StronglyMeasurable[S.𝓕 s] x → BddAt S x →
      Integrable (fun ω => G (a ω, b ω, θ t ω) * x ω) S.μ := by
    intro G hG t s a b x ha hb hab hbb hts hx hxb
    have h1 := sm_comp hG ha hb (hθ.1 t)
    have hb1 := bddAt_comp hG hab hbb (hθ.2 t)
    exact (hb1.mul hxb).integrable (((h1.mono (S.𝓕.mono hts)).measurable.mul
      hx.measurable).stronglyMeasurable.mono (S.𝓕.le s)).aestronglyMeasurable
  have hΔm : ∀ t, StronglyMeasurable[S.𝓕 t] fun ω => q' t ω - q t ω := fun t =>
    (hq'.1 t).sub (hq.1 t)
  have hΔb : ∀ t, BddAt S fun ω => q' t ω - q t ω := fun t =>
    (hq'.2 t).add (hq.2 t).neg
  have hlm := lag_sm hq0 hq.1
  have hlb := lag_bdd hq0b hq.2
  -- the date-`t` supergradient bound, integrated
  have hstep : ∀ t, ∫ ω, pay Φ θ q0 q' t ω ∂S.μ - ∫ ω, pay Φ θ q0 q t ω ∂S.μ ≤
      ∫ ω, D1 (q t ω) (lag q0 q t ω) (θ t ω) * (q' t ω - q t ω) ∂S.μ +
        ∫ ω, D2 (q t ω) (lag q0 q t ω) (θ t ω) * (lag q0 q' t ω - lag q0 q t ω) ∂S.μ := by
    intro t
    have i1 : Integrable (fun ω => D1 (q t ω) (lag q0 q t ω) (θ t ω) * (q' t ω - q t ω)) S.μ :=
      hint hD1c (hq.1 t) (hlm t) (hq.2 t) (hlb t) le_rfl (hΔm t) (hΔb t)
    have i2 : Integrable (fun ω => D2 (q t ω) (lag q0 q t ω) (θ t ω) *
        (lag q0 q' t ω - lag q0 q t ω)) S.μ := hint hD2c (hq.1 t) (hlm t) (hq.2 t) (hlb t) le_rfl
      ((lag_sm hq0 hq'.1 t).sub (hlm t)) ((lag_bdd hq0b hq'.2 t).add (hlb t).neg)
    rw [← integral_sub (hpi' t) (hpi t), ← integral_add i1 i2]
    refine integral_mono_ae ((hpi' t).sub (hpi t)) (i1.add i2) ?_
    filter_upwards [hsg t] with ω h
    simp only [pay]
    linarith
  -- the first-order condition, integrated against `Δ_t`
  have hfz : ∀ t, ∫ ω, D1 (q t ω) (lag q0 q t ω) (θ t ω) * (q' t ω - q t ω) ∂S.μ +
      β * ∫ ω, D2 (q (t + 1) ω) (q t ω) (θ (t + 1) ω) * (q' t ω - q t ω) ∂S.μ = 0 := by
    intro t
    set a : Ω → ℝ := fun ω => D1 (q t ω) (lag q0 q t ω) (θ t ω)
    set d : Ω → ℝ := fun ω => D2 (q (t + 1) ω) (q t ω) (θ (t + 1) ω)
    have ham : StronglyMeasurable[S.𝓕 t] a := sm_comp hD1c (hq.1 t) (hlm t) (hθ.1 t)
    have hab : BddAt S a := bddAt_comp hD1c (hq.2 t) (hlb t) (hθ.2 t)
    have hdm : StronglyMeasurable[S.𝓕 (t + 1)] d :=
      sm_comp hD2c (hq.1 (t + 1)) ((hq.1 t).mono (S.𝓕.mono (Nat.le_succ t))) (hθ.1 (t + 1))
    have hdb : BddAt S d := bddAt_comp hD2c (hq.2 (t + 1)) (hq.2 t) (hθ.2 (t + 1))
    have hai : Integrable a S.μ := hab.integrable (ham.mono (S.𝓕.le t)).aestronglyMeasurable
    have hdi : Integrable d S.μ :=
      hdb.integrable (hdm.mono (S.𝓕.le (t + 1))).aestronglyMeasurable
    obtain ⟨KΔ, hKΔ⟩ := hΔb t
    have hpo := integral_mul_E (hΔm t) hKΔ (hai.add (hdi.smul β))
    have hEa : S.E t a = a := S.E_of_stronglyMeasurable ham hai
    have hE0 : ∀ᵐ ω ∂S.μ, S.E t (a + β • d) ω = 0 := by
      filter_upwards [hfoc t, S.E_add hai (hdi.smul β) t, S.E_smul β d t] with ω h1 h2 h3
      rw [h2, Pi.add_apply, hEa, h3, Pi.smul_apply, smul_eq_mul]
      exact h1
    have hr : ∫ ω, (q' t ω - q t ω) * S.E t (a + β • d) ω ∂S.μ = 0 := by
      rw [integral_congr_ae (hE0.mono fun ω h => by rw [h, mul_zero])]
      simp
    have ia : Integrable (fun ω => a ω * (q' t ω - q t ω)) S.μ :=
      hint hD1c (hq.1 t) (hlm t) (hq.2 t) (hlb t) le_rfl (hΔm t) (hΔb t)
    have id : Integrable (fun ω => d ω * (q' t ω - q t ω)) S.μ :=
      hint hD2c (hq.1 (t + 1)) ((hq.1 t).mono (S.𝓕.mono (Nat.le_succ t))) (hq.2 (t + 1))
        (hq.2 t) le_rfl ((hΔm t).mono (S.𝓕.mono (Nat.le_succ t))) (hΔb t)
    rw [← integral_const_mul, ← integral_add ia (id.const_mul β), ← hr, ← hpo]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  induction T with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul]
    have h := hstep 0
    have e : ∫ ω, D2 (q 0 ω) (lag q0 q 0 ω) (θ 0 ω) * (lag q0 q' 0 ω - lag q0 q 0 ω) ∂S.μ = 0 := by
      simp [lag]
    linarith
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := hstep (n + 1)
    have e : ∫ ω, D2 (q (n + 1) ω) (lag q0 q (n + 1) ω) (θ (n + 1) ω) *
        (lag q0 q' (n + 1) ω - lag q0 q (n + 1) ω) ∂S.μ =
        ∫ ω, D2 (q (n + 1) ω) (q n ω) (θ (n + 1) ω) * (q' n ω - q n ω) ∂S.μ := rfl
    have hf := hfz n
    have hbn : 0 ≤ β ^ (n + 1) := pow_nonneg hβ.le _
    have h2 := mul_le_mul_of_nonneg_left h hbn
    rw [e] at h2
    have key : β ^ n * (∫ ω, D1 (q n ω) (lag q0 q n ω) (θ n ω) * (q' n ω - q n ω) ∂S.μ) +
        β ^ (n + 1) * ∫ ω, D2 (q (n + 1) ω) (q n ω) (θ (n + 1) ω) * (q' n ω - q n ω) ∂S.μ =
          0 := by
      rw [pow_succ, mul_assoc, ← mul_add, hf, mul_zero]
    linarith

/-- Cochrane (2023), p. 118, **sufficiency**: if `q` satisfies the FOC at every date, the
supergradient inequality holds against the admissible competitor `q′` at every date, and the
transversality condition `βᵀE[Φ₁(q_T, q_{T−1}, θ_T)(q′_T − q_T)] → 0` holds, then `q′` does no
better than `q`. -/
theorem value_le_of_foc [NormedAddCommGroup V] [ProperSpace V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {β : ℝ} (hβ : 0 < β)
    {Φ D1 D2 : ℝ → ℝ → V → ℝ} (hs : Smooth Φ D1 D2) {θ : ℕ → Ω → V} (hθ : DataReg S θ)
    {q0 : Ω → ℝ} (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0)
    {q q' : ℕ → Ω → ℝ} (hq : Plan S q) (hq' : Plan S q') (hadm : Admissible S β Φ θ q0 q)
    (hadm' : Admissible S β Φ θ q0 q') (hfoc : ∀ t, FOC S β D1 D2 θ q0 q t)
    (hsg : ∀ t, SuperGrad S Φ D1 D2 θ q0 q q' t)
    (htvc : Tendsto (fun T => β ^ T * ∫ ω, D1 (q T ω) (lag q0 q T ω) (θ T ω) *
      (q' T ω - q T ω) ∂S.μ) atTop (𝓝 0)) :
    value S β Φ θ q0 q' ≤ value S β Φ θ q0 q := by
  have hsum := ((hadm'.summable hβ.le).sub (hadm.summable hβ.le)).hasSum
  have hlim := (tendsto_add_atTop_iff_nat 1).2 hsum.tendsto_sum_nat
  have hle := le_of_tendsto_of_tendsto' hlim htvc fun T => by
    refine le_trans (le_of_eq ?_) (partial_le hβ hs hθ hq0 hq0b hq hq' hfoc hsg T)
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [(hadm'.summable hβ.le).tsum_sub (hadm.summable hβ.le)] at hle
  unfold value
  linarith

/-- Cochrane (2023), p. 118: for uniformly bounded plans and data and `0 < β < 1`, the
transversality condition of `value_le_of_foc` holds automatically. -/
theorem tvc_of_ubdd [NormedAddCommGroup V] [ProperSpace V] {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {D1 : ℝ → ℝ → V → ℝ} (hD1c : Continuous (fun p : ℝ × ℝ × V => D1 p.1 p.2.1 p.2.2))
    {θ : ℕ → Ω → V} (hθu : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ‖θ t ω‖ ≤ K) {q0 : Ω → ℝ}
    (hq0b : BddAt S q0) {q q' : ℕ → Ω → ℝ} (hq : UPlan S q) (hq' : UPlan S q') :
    Tendsto (fun T => β ^ T * ∫ ω, D1 (q T ω) (lag q0 q T ω) (θ T ω) *
      (q' T ω - q T ω) ∂S.μ) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := hθu
  obtain ⟨R, hR⟩ := hq.2
  obtain ⟨R', hR'⟩ := hq'.2
  obtain ⟨R0, hR0⟩ := hq0b
  set L := max (max R R') R0
  obtain ⟨M, hM0, hM⟩ := exists_box_bound hD1c L K
  have hbd : ∀ T, |∫ ω, D1 (q T ω) (lag q0 q T ω) (θ T ω) * (q' T ω - q T ω) ∂S.μ| ≤
      M * (2 * L) := by
    intro T
    have hlag : ∀ᵐ ω ∂S.μ, |lag q0 q T ω| ≤ L := by
      cases T with
      | zero => exact hR0.mono fun ω h => h.trans (le_max_right _ _)
      | succ n =>
        have hL : R ≤ L := (le_max_left _ _).trans (le_max_left _ _)
        exact (hR n).mono fun ω h => h.trans hL
    have hb : ∀ᵐ ω ∂S.μ, ‖D1 (q T ω) (lag q0 q T ω) (θ T ω) * (q' T ω - q T ω)‖ ≤
        M * (2 * L) := by
      filter_upwards [hR T, hR' T, hK T, hlag] with ω h1 h2 h3 h4
      have hq1 : |q T ω| ≤ L := h1.trans ((le_max_left _ _).trans (le_max_left _ _))
      have hq2 : |q' T ω| ≤ L := h2.trans ((le_max_right _ _).trans (le_max_left _ _))
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul (hM _ _ _ hq1 h4 h3) ?_ (abs_nonneg _) hM0
      calc |q' T ω - q T ω| ≤ |q' T ω| + |q T ω| := abs_sub _ _
        _ ≤ 2 * L := by linarith
    have := norm_integral_le_of_norm_le_const hb
    simpa using this
  have hgeo := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const (M * (2 * L))
  rw [zero_mul] at hgeo
  refine squeeze_zero_norm (fun T => ?_) hgeo
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ.le T)]
  exact mul_le_mul_of_nonneg_left (hbd T) (pow_nonneg hβ.le T)

/-- Cochrane (2023), p. 118, **sufficiency within a class**: let `C` be a class of uniformly
bounded plans containing `q`, the data be uniformly bounded and `0 < β < 1`. If `q` is admissible,
satisfies the FOC at every date, and the supergradient inequality holds against every member of
`C` at every date, then `q` is optimal within `C`. -/
theorem optimalIn_of_foc [NormedAddCommGroup V] [ProperSpace V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {Φ D1 D2 : ℝ → ℝ → V → ℝ} (hs : Smooth Φ D1 D2) {θ : ℕ → Ω → V} (hθ : DataReg S θ)
    (hθu : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ‖θ t ω‖ ≤ K) {q0 : Ω → ℝ}
    (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0) {C : (ℕ → Ω → ℝ) → Prop}
    (hCU : ∀ q', C q' → UPlan S q') {q : ℕ → Ω → ℝ} (hqC : C q)
    (hadm : Admissible S β Φ θ q0 q) (hfoc : ∀ t, FOC S β D1 D2 θ q0 q t)
    (hsg : ∀ q', C q' → ∀ t, SuperGrad S Φ D1 D2 θ q0 q q' t) :
    OptimalIn S C β Φ θ q0 q :=
  ⟨hqC, hadm, fun q' hq'C hadm' => value_le_of_foc hβ hs hθ hq0 hq0b (hCU q hqC).1
    (hCU q' hq'C).1 hadm hadm' hfoc (hsg q' hq'C)
    (tvc_of_ubdd hβ hβ1 hs.2.2.2.1 hθu hq0b (hCU q hqC) (hCU q' hq'C))⟩

/-- Cochrane (2023), p. 118 and eq. (17.17), p. 407: for a payoff concave in `(q_t, q_{t−1})`
(`TangentConcave`), uniformly bounded data and `0 < β < 1`, a uniformly bounded admissible plan is
optimal among uniformly bounded plans **iff** it satisfies the price setter's FOC at every
date. -/
theorem optimal_iff_foc [NormedAddCommGroup V] [ProperSpace V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {Φ D1 D2 : ℝ → ℝ → V → ℝ} (hs : Smooth Φ D1 D2) (hconc : TangentConcave Φ D1 D2)
    {θ : ℕ → Ω → V} (hθ : DataReg S θ) (hθu : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ‖θ t ω‖ ≤ K)
    {q0 : Ω → ℝ} (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0) {q : ℕ → Ω → ℝ}
    (hq : UPlan S q) (hadm : Admissible S β Φ θ q0 q) :
    OptimalIn S (UPlan S) β Φ θ q0 q ↔ ∀ t, FOC S β D1 D2 θ q0 q t :=
  ⟨fun hopt t => foc_of_optimal_u hβ hs hθ hq0 hq0b hopt t, fun hfoc =>
    optimalIn_of_foc hβ hβ1 hs hθ hθu hq0 hq0b (fun _ h => h) hq hadm hfoc fun _ _ _ =>
      Eventually.of_forall fun _ => hconc _ _ _ _ _⟩

end Cochrane.KeynesianStickyPrices.TidyR6PriceSetting
