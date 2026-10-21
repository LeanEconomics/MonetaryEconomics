/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.AggregateUncertaintyMeasure

/-!
# A genuine lognormal i.i.d. growth process

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.7, pp. 205–207
(lognormal consumption growth, Bohn's example, (6.15)–(6.18)).

The process: `ε_t` i.i.d. `N(μ, v)` on `Ω = ℕ → ℝ` (`ν = gaussianReal μ v`, product law
`ν^ℕ`), consumption `c_t = exp(ε_1 + ⋯ + ε_t)`, so log growth `log G_{t+1} = ε_{t+1}` is
i.i.d. normal and growth `G_{t+1} = exp ε_{t+1}` is i.i.d. with the lognormal law
`lognormalLaw μ v = exp_* N(μ, v)`. Every lognormal result of `AggregateUncertainty` (which
were statements about the numbers `lognormalMoment`) is proved here about this process, with
Mathlib conditional expectations, almost surely.

## Main results

* The process: `gaussianProb`, `lognormalGrowthLaw`, `lognormalLaw`, `map_growth`
  (each `G_{t+1}` has the lognormal law), `map_log_growth` (log growth is `N(μ, v)`),
  `iIndepFun_growth` (growth rates are independent), `lognormal_mom`
  (`E[G^a] = e^{aμ + v a²/2}`), `lognormal_E_growth`.
* (6.15)/(6.16) on the process: `lognormal_correct_term`, `lognormal_incorrect_term` (the
  corrected exponent `(γ² + 1) v/2`), `lognormal_printed_incorrect_wrong` (the printed exponent is
  wrong for the process), `lognormal_correct_pv_summable_iff`,
  `lognormal_incorrect_pv_summable_iff`.
* `lognormal_region_iff`: there are `μ, δ` making the correct present value converge and the
  incorrect one explode a.s. on the process iff `γ > 0`; `lognormal_bohn_region` adds
  `δ > 0` and `r_f < g`.
* (6.17)/(6.18) on the process: `lognormal_riskFree_prices`, `lognormal_log_riskFree`,
  `lognormal_E_tsum_bohn_pv` (`c_t = E_t Σ_{j≥1} (...)`), `lognormal_eq_6_18_diverges`.
-/

namespace Cochrane.FiscalConstraints.LognormalGrowthMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID AggregateUncertaintyMeasure
open AggregateUncertainty (growth ratio pvTerm pvDisc riskFreeGross lognormalMoment
  correctExponent incorrectExponent)

/-- Cochrane (2023), p. 205: the normal law `N(μ, v)` of log growth, as a probability measure. -/
noncomputable def gaussianProb (μ : ℝ) (v : NNReal) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal μ v, inferInstance⟩

/-- Cochrane (2023), p. 205: the lognormal law of growth, `exp_* N(μ, v)`. -/
noncomputable def lognormalLaw (μ : ℝ) (v : NNReal) : Measure ℝ :=
  (gaussianReal μ v).map Real.exp

/-- Cochrane (2023), p. 205: `G = exp ε` with `ε ~ N(μ, v)` is a growth law: measurable,
positive, and every moment `E[G^a] = E[e^{aε}]` is finite (Gaussian moment generating
function). -/
theorem lognormalGrowthLaw (μ : ℝ) (v : NNReal) : GrowthLaw (gaussianProb μ v) Real.exp where
  meas := Real.measurable_exp
  pos := Real.exp_pos
  integrable := fun a => by
    have h : (fun x => Real.exp x ^ a) = fun x => Real.exp (a * x) := by
      funext x; rw [← Real.exp_mul, mul_comm]
    rw [h]
    exact integrable_exp_mul_gaussianReal a

/-- Cochrane (2023), p. 205: the moments of the lognormal process are the lognormal moments,
`E[G^a] = e^{aμ + v a²/2}`. -/
theorem lognormal_mom (μ : ℝ) (v : NNReal) :
    mom (gaussianProb μ v) Real.exp = lognormalMoment μ v := by
  funext a
  exact AggregateUncertainty.lognormalMoment_eq_integral μ v a

/-- Cochrane (2023), p. 205: consumption is `c_t = exp(ε_1 + ⋯ + ε_t)`. -/
theorem cons_exp (t : ℕ) (ω : ℕ → ℝ) :
    cons Real.exp t ω = Real.exp (∑ i ∈ Finset.range t, ω (i + 1)) := by
  rw [cons, Real.exp_sum]

/-- Cochrane (2023), p. 205: **log growth is i.i.d. normal**: `log G_{t+1} = ε_{t+1}`, whose law
is `N(μ, v)`. -/
theorem map_log_growth (μ : ℝ) (v : NNReal) (t : ℕ) :
    Measure.map (fun ω => Real.log (growth (cons Real.exp) t ω)) (iidSystem (gaussianProb μ v)).μ
      = gaussianReal μ v := by
  have h : (fun ω : ℕ → ℝ => Real.log (growth (cons Real.exp) t ω)) = fun ω => ω (t + 1) := by
    funext ω
    rw [growth_cons (lognormalGrowthLaw μ v), Real.log_exp]
  rw [h]
  exact Measure.infinitePi_map_eval _ (t + 1)

/-- Cochrane (2023), p. 205: **each growth rate has the lognormal law**,
`G_{t+1} ~ exp_* N(μ, v)`. -/
theorem map_growth (μ : ℝ) (v : NNReal) (t : ℕ) :
    Measure.map (fun ω => growth (cons Real.exp) t ω) (iidSystem (gaussianProb μ v)).μ =
      lognormalLaw μ v := by
  have h : (fun ω : ℕ → ℝ => growth (cons Real.exp) t ω) =
      Real.exp ∘ fun ω => ω (t + 1) := by
    funext ω
    rw [growth_cons (lognormalGrowthLaw μ v)]
    rfl
  rw [h, ← Measure.map_map Real.measurable_exp (measurable_pi_apply (t + 1))]
  change Measure.map Real.exp (Measure.map (fun ω : ℕ → ℝ => ω (t + 1))
    (Measure.infinitePi fun _ => gaussianReal μ v)) = _
  rw [Measure.infinitePi_map_eval]
  rfl

/-- Cochrane (2023), p. 205: **the growth rates are mutually independent**, so
`(G_{t+1})_t` is an i.i.d. lognormal sequence. -/
theorem iIndepFun_growth (μ : ℝ) (v : NNReal) :
    iIndepFun (fun t ω => growth (cons Real.exp) t ω) (iidSystem (gaussianProb μ v)).μ := by
  have h0 : iIndepFun (fun i (ω : ℕ → ℝ) => Real.exp (ω i))
      (Measure.infinitePi fun _ => gaussianReal μ v) :=
    iIndepFun_infinitePi (P := fun _ => gaussianReal μ v) (X := fun _ => Real.exp)
      (fun _ => Real.measurable_exp)
  have h1 := h0.precomp (g := fun t => t + 1) (fun a b h => by simpa using h)
  have h : (fun t ω => growth (cons Real.exp) t ω) = fun t (ω : ℕ → ℝ) => Real.exp (ω (t + 1)) := by
    funext t ω
    rw [growth_cons (lognormalGrowthLaw μ v)]
  rw [h]
  exact h1

/-- Cochrane (2023), p. 205: on the lognormal process, `E_t[G_{t+1}^a] = e^{aμ + v a²/2}` a.e. -/
theorem lognormal_E_growth (μ : ℝ) (v : NNReal) (t : ℕ) (a : ℝ) :
    (iidSystem (gaussianProb μ v)).E t (fun ω => growth (cons Real.exp) t ω ^ a)
      =ᵐ[(iidSystem (gaussianProb μ v)).μ] fun _ => lognormalMoment μ v a := by
  rw [← lognormal_mom]
  exact meas_iidGrowth (lognormalGrowthLaw μ v) t a

/-- Cochrane (2023), (6.15) p. 205, on the lognormal process with `β = e^{−δ}`: the correct
summands are `E_t[β^j (c_{t+j}/c_t)^{1−γ}] κ = (e^{A})^j κ`, `A = −δ + (1−γ)μ + (1−γ)² v/2`. -/
theorem lognormal_correct_term (μ : ℝ) (v : NNReal) (δ γ κ : ℝ) (t j : ℕ) :
    (iidSystem (gaussianProb μ v)).E t (pvTerm (Real.exp (-δ)) γ κ (cons Real.exp) t j)
      =ᵐ[(iidSystem (gaussianProb μ v)).μ]
      fun _ => Real.exp (correctExponent δ γ μ v) ^ j * κ := by
  filter_upwards [correct_term (lognormalGrowthLaw μ v) (Real.exp (-δ)) γ κ t j] with ω h
  rw [h, lognormal_mom, AggregateUncertainty.lognormal_correct, correctExponent]

/-- Cochrane (2023), (6.16) p. 206 (corrected), on the lognormal process: the summands with the
expectation inside are `(e^{B})^j κ`, `B = −δ + (1−γ)μ + (γ² + 1) v/2`. -/
theorem lognormal_incorrect_term (μ : ℝ) (v : NNReal) (δ γ κ : ℝ) (t j : ℕ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
      (iidSystem (gaussianProb μ v)).E t
          (fun ω' => Real.exp (-δ) ^ j * ratio (cons Real.exp) t j ω' ^ (-γ)) ω *
        (iidSystem (gaussianProb μ v)).E t (ratio (cons Real.exp) t j) ω * κ =
        Real.exp (incorrectExponent δ γ μ v) ^ j * κ := by
  filter_upwards [incorrect_term (lognormalGrowthLaw μ v) (Real.exp (-δ)) γ κ t j] with ω h
  rw [h, lognormal_mom, AggregateUncertainty.lognormal_incorrect, incorrectExponent]

/-- Cochrane (2023), p. 206 (**error in the book, on the process**): for `v ≠ 0`, the product of
the one-period forecasts `E_t[G^{−γ}] E_t[G]` is a.s. not the printed `e^{(1−γ)μ + γ² v/2}`. -/
theorem lognormal_printed_incorrect_wrong (μ : ℝ) {v : NNReal} (hv : v ≠ 0) (γ : ℝ) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
      (iidSystem (gaussianProb μ v)).E t (fun ω' => growth (cons Real.exp) t ω' ^ (-γ)) ω *
        (iidSystem (gaussianProb μ v)).E t (fun ω' => growth (cons Real.exp) t ω' ^ (1 : ℝ)) ω ≠
        Real.exp ((1 - γ) * μ + γ ^ 2 * v / 2) := by
  filter_upwards [lognormal_E_growth μ v t (-γ), lognormal_E_growth μ v t 1] with ω h1 h2
  rw [h1, h2]
  exact AggregateUncertainty.printed_incorrect_wrong γ μ (by exact_mod_cast hv)

/-- Cochrane (2023), (6.15) p. 205, on the lognormal process: almost surely the correct present
value converges iff `A = −δ + (1−γ)μ + (1−γ)² v/2 < 0` (for `κ ≠ 0`). -/
theorem lognormal_correct_pv_summable_iff (μ : ℝ) (v : NNReal) (δ γ : ℝ) {κ : ℝ} (hκ : κ ≠ 0)
    (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
      (Summable (fun j => (iidSystem (gaussianProb μ v)).E t
          (pvTerm (Real.exp (-δ)) γ κ (cons Real.exp) t (j + 1)) ω) ↔
        correctExponent δ γ μ v < 0) := by
  filter_upwards [correct_pv_summable_iff (lognormalGrowthLaw μ v) (Real.exp (-δ)) γ hκ t]
    with ω h
  rw [h, lognormal_mom, AggregateUncertainty.lognormal_correct, abs_of_pos (Real.exp_pos _),
    Real.exp_lt_one_iff, correctExponent]

/-- Cochrane (2023), (6.16) p. 206 (corrected), on the lognormal process: almost surely the
incorrect present value converges iff `B = −δ + (1−γ)μ + (γ² + 1) v/2 < 0` (for `κ ≠ 0`). -/
theorem lognormal_incorrect_pv_summable_iff (μ : ℝ) (v : NNReal) (δ γ : ℝ) {κ : ℝ}
    (hκ : κ ≠ 0) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
      (Summable (fun j => (iidSystem (gaussianProb μ v)).E t
          (fun ω' => Real.exp (-δ) ^ (j + 1) * ratio (cons Real.exp) t (j + 1) ω' ^ (-γ)) ω *
        (iidSystem (gaussianProb μ v)).E t (ratio (cons Real.exp) t (j + 1)) ω * κ) ↔
        incorrectExponent δ γ μ v < 0) := by
  filter_upwards [incorrect_pv_summable_iff (lognormalGrowthLaw μ v) (Real.exp (-δ)) γ hκ t]
    with ω h
  rw [h, lognormal_mom, AggregateUncertainty.lognormal_incorrect, abs_of_pos (Real.exp_pos _),
    Real.exp_lt_one_iff, incorrectExponent]

/-- Cochrane (2023), p. 206: the event "the correct present value (6.15) converges and the
incorrect one (6.16) does not" on the lognormal process. -/
def Explodes (μ : ℝ) (v : NNReal) (δ γ κ : ℝ) (t : ℕ) (ω : ℕ → ℝ) : Prop :=
  Summable (fun j => (iidSystem (gaussianProb μ v)).E t
      (pvTerm (Real.exp (-δ)) γ κ (cons Real.exp) t (j + 1)) ω) ∧
    ¬ Summable (fun j => (iidSystem (gaussianProb μ v)).E t
        (fun ω' => Real.exp (-δ) ^ (j + 1) * ratio (cons Real.exp) t (j + 1) ω' ^ (-γ)) ω *
      (iidSystem (gaussianProb μ v)).E t (ratio (cons Real.exp) t (j + 1)) ω * κ)

/-- Cochrane (2023), p. 206, on the lognormal process: almost surely, the correct present value
converges while the incorrect one explodes iff `A < 0 ≤ B`. -/
theorem lognormal_explodes_iff (μ : ℝ) (v : NNReal) (δ γ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
      (Explodes μ v δ γ κ t ω ↔
        correctExponent δ γ μ v < 0 ∧ 0 ≤ incorrectExponent δ γ μ v) := by
  filter_upwards [lognormal_correct_pv_summable_iff μ v δ γ hκ t,
    lognormal_incorrect_pv_summable_iff μ v δ γ hκ t] with ω h1 h2
  rw [Explodes, h1, h2, not_lt]

/-- Cochrane (2023), p. 206 (corrected; "it is entirely possible", **on the lognormal process**):
for `v = σ² > 0` and `κ ≠ 0`, there are a mean log growth `μ` and a discount rate `δ` such that,
almost surely, the correct present value converges and the incorrect one explodes, iff
`γ > 0`. -/
theorem lognormal_region_iff (γ : ℝ) {v : NNReal} (hv : v ≠ 0) {κ : ℝ} (hκ : κ ≠ 0) (t : ℕ) :
    (∃ μ δ, ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ, Explodes μ v δ γ κ t ω) ↔ 0 < γ := by
  have hv' : (0 : ℝ) < v := by
    have h := pos_iff_ne_zero.2 hv
    exact_mod_cast h
  constructor
  · rintro ⟨μ, δ, h⟩
    obtain ⟨ω, h1, h2⟩ := (h.and (lognormal_explodes_iff μ v δ γ hκ t)).exists
    obtain ⟨hA, hB⟩ := h2.1 h1
    simp only [correctExponent, incorrectExponent] at hA hB
    by_contra hγ
    push Not at hγ
    nlinarith
  · intro hγ
    obtain ⟨μ, δ, -, hA, hB⟩ := AggregateUncertainty.region_pos_delta hγ hv'
    refine ⟨μ, δ, ?_⟩
    filter_upwards [lognormal_explodes_iff μ v δ γ hκ t] with ω h
    exact h.2 ⟨hA, hB.le⟩

/-- Cochrane (2023), pp. 205–206 (**Theorem B, lognormal form, on the process**): for every
`γ > 0` and `v > 0` there are `μ` and `δ > 0` such that on the lognormal process the risk-free
rate is below mean growth and, almost surely, the correct present value converges while the
incorrect one explodes. -/
theorem lognormal_bohn_region {γ : ℝ} (hγ : 0 < γ) {v : NNReal} (hv : v ≠ 0) {κ : ℝ}
    (hκ : κ ≠ 0) (t : ℕ) :
    ∃ μ δ, 0 < δ ∧
      riskFreeGross (Real.exp (-δ)) γ (mom (gaussianProb μ v) Real.exp) <
        mom (gaussianProb μ v) Real.exp 1 ∧
      ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ, Explodes μ v δ γ κ t ω := by
  have hv' : (0 : ℝ) < v := by
    have h := pos_iff_ne_zero.2 hv
    exact_mod_cast h
  obtain ⟨μ, δ, hδ, hA, hB⟩ := AggregateUncertainty.region_pos_delta hγ hv'
  refine ⟨μ, δ, hδ, ?_, ?_⟩
  · rw [lognormal_mom]
    exact (AggregateUncertainty.riskFree_lt_growth_iff δ γ μ v).2 hB
  · filter_upwards [lognormal_explodes_iff μ v δ γ hκ t] with ω h
    exact h.2 ⟨hA, hB.le⟩

/-- Cochrane (2023), p. 206, on the lognormal process: the risk-free rate prices the riskless
bond, `E_t[e^{−δ} G_{t+1}^{−γ}] (1 + r_f) = 1` a.e. -/
theorem lognormal_riskFree_prices (μ : ℝ) (v : NNReal) (δ γ : ℝ) (t : ℕ) :
    (iidSystem (gaussianProb μ v)).E t (fun ω => Real.exp (-δ) * growth (cons Real.exp) t ω ^ (-γ) *
        riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v))
      =ᵐ[(iidSystem (gaussianProb μ v)).μ] fun _ => 1 := by
  rw [← lognormal_mom]
  exact riskFree_prices (lognormalGrowthLaw μ v) (Real.exp_pos _).ne' t

/-- Cochrane (2023), p. 206 (Bohn's risk-free rate, corrected, for the process):
`log(1 + r_f) = δ + γ μ − γ² v/2`. -/
theorem lognormal_log_riskFree (μ : ℝ) (v : NNReal) (δ γ : ℝ) :
    Real.log (riskFreeGross (Real.exp (-δ)) γ (mom (gaussianProb μ v) Real.exp)) =
      δ + γ * μ - γ ^ 2 * v / 2 := by
  rw [lognormal_mom]
  exact AggregateUncertainty.log_riskFree_lognormal δ γ μ v

/-- **(6.17), genuine infinite horizon, lognormal process**, Cochrane (2023), p. 207: with
`β = e^{−δ}` and `A = −δ + (1−γ)μ + (1−γ)² v/2 < 0`, debt equal to consumption rolled over at
the risk-free rate is the conditional expectation of its infinite discounted surplus stream,
which converges a.s.: `c_t = E_t Σ_{j≥1} β^j (c_{t+j}/c_t)^{−γ} s_{t+j}`. -/
theorem lognormal_E_tsum_bohn_pv (μ : ℝ) (v : NNReal) {δ γ : ℝ}
    (hA : correctExponent δ γ μ v < 0) {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω = riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v) *
      cons Real.exp u ω - cons Real.exp (u + 1) ω) (t : ℕ) :
    (∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
        Summable fun j => pvDisc (Real.exp (-δ)) γ (cons Real.exp) t (j + 1) ω * s (t + j + 1) ω) ∧
      (iidSystem (gaussianProb μ v)).E t
          (fun ω => ∑' j, pvDisc (Real.exp (-δ)) γ (cons Real.exp) t (j + 1) ω * s (t + j + 1) ω)
        =ᵐ[(iidSystem (gaussianProb μ v)).μ] cons Real.exp t := by
  have hR : Real.exp (-δ) * mom (gaussianProb μ v) Real.exp (-γ) *
      riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v) = 1 := by
    rw [lognormal_mom, riskFreeGross]
    have : Real.exp (-δ) * lognormalMoment μ v (-γ) ≠ 0 :=
      mul_ne_zero (Real.exp_pos _).ne' (Real.exp_pos _).ne'
    field_simp
    exact div_self (by unfold lognormalMoment; exact (Real.exp_pos _).ne')
  have hq : Real.exp (-δ) * mom (gaussianProb μ v) Real.exp (1 - γ) < 1 := by
    rw [lognormal_mom, AggregateUncertainty.lognormal_correct, Real.exp_lt_one_iff]
    exact hA
  exact E_tsum_bohn_pv (lognormalGrowthLaw μ v) (Real.exp_pos _) hR hq hs t

/-- **(6.18) on the lognormal process**, Cochrane (2023), p. 207 ("the present value of
cashflows term builds to negative infinity, and the terminal value builds to positive
infinity"): if `0 < R < E[G]` (`r < g`), then almost surely
`E_t[Σ_{j=1}^T R^{−j} s_{t+j}] → −∞` and `E_t[R^{−T} c_{t+T}] → +∞` as `T → ∞`. -/
theorem lognormal_eq_6_18_diverges (μ : ℝ) (v : NNReal) {R : ℝ} (hR0 : 0 < R)
    (hRg : R < lognormalMoment μ v 1) {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω = R * cons Real.exp u ω - cons Real.exp (u + 1) ω) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb μ v)).μ,
      Tendsto (fun T => (iidSystem (gaussianProb μ v)).E t
          (fun ω' => ∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω') ω) atTop atBot ∧
      Tendsto (fun T => (iidSystem (gaussianProb μ v)).E t
          (fun ω' => (R⁻¹) ^ T * cons Real.exp (t + T) ω') ω) atTop atTop := by
  have h := fun T => eq_6_18 (lognormalGrowthLaw μ v) hR0.ne' hs t T
  filter_upwards [ae_all_iff.2 fun T => (h T).1, ae_all_iff.2 fun T => (h T).2] with ω h1 h2
  simp only [h1, h2, lognormal_mom]
  obtain ⟨d1, d2⟩ := AggregateUncertainty.eq_6_18_diverges hR0 hRg
    (cons_pos (lognormalGrowthLaw μ v) t ω)
  exact ⟨d1, by simpa only [mul_comm] using d2⟩

end Cochrane.FiscalConstraints.LognormalGrowthMeasure
