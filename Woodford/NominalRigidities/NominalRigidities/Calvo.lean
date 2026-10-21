/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.QuadraticRoots
import NominalRigidities.DixitStiglitz
import NominalRigidities.ForwardSolution
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The Calvo model of pricesetting

Woodford (2003), *Interest and Prices*, Chapter 3, §2.1 (pp. 177–187) and Appendix B.3
(pp. 659–661, the proof of Proposition 3.4).

## The price index (2.1)

Goods form a measure space `(F, m)` (the book's `[0, 1]`). In period `t` the goods in a measurable
set `S` of mass `1 − α` get the new price `p*_t`; the others keep last period's price, and the
book's key assumption ("each price appearing in the period `t` distribution of unchanged prices
with the same relative frequency as in the period `t − 1` price distribution", p. 178) is taken
literally as the hypothesis `(m.restrict Sᶜ).map p_{t−1} = α • m.map p_{t−1}`.
`dist_law_of_motion` derives the law of motion of the price distribution and `calvo_index`
derives (2.1) exactly. This is the exact statement for a continuum of goods; no law of large
numbers is involved, and `lottery_model` shows the hypothesis holds for every initial price
distribution when the Calvo lottery is an independent uniform draw (the product measure). The
same recursion in cohort form (`cohort_decomposition`) expresses `P_{t+k}^{1−θ}` by date of last
price change. (The construction follows the Galí (2015) Chapter 3 project's `CalvoIndex`,
restated with Woodford's notation: `θ` is the elasticity of substitution and `α` the fraction of
unchanged prices.)

## The reset-price problem (2.2)–(2.4)

`resetObjective` is the genuine infinite discounted sum (2.2) `∑ αᵏ E_t[Q_{t,t+k} Π_{t+k}(p)]`
for an arbitrary `ExpectationSystem`; `hasDerivAt_resetObjective` differentiates it under `E_t`
and the infinite sum; `foc_of_isLocalMax` gives the first-order condition (2.3), and
`isMaxOn_iff_foc` shows that it characterises the optimum when profits are concave in the price.
`objective_fn31` is footnote 31. `hom_deg_zero_of_hom_deg_one` is the homogeneity step of
Assumption 3.1 (`Π₁` is homogeneous of degree zero), `steady_state_solves` the zero-inflation
steady state (p. 179).

## Log-linearisation as exact derivatives

* (2.5): `hasFDerivAt_logIndexFn` — `log P_t` as a function of `(log p*_t, log P_{t−1})` has
  derivative `(1 − α) dx + α dy` at every point of the diagonal (`log_calvo_index`).
* (2.6): `hasDerivAt_focPath` — along any bounded perturbation of the zero-inflation steady
  state (stochastic discount factor, relative price, output and disturbance), the first-order
  condition (2.4) has derivative `ψ_p ∑ₖ (αβ)ᵏ E_t[x̂ₖ − ζ(ŷₖ − ŷⁿₖ)]` (`focPath_deriv_eq`);
  the discount-factor perturbation drops out because `Π₁ = 0` at the steady state.
  `natRate_deriv` identifies `ŷⁿ` as the exact derivative of the natural rate (1.21).
  `eq26_iff_deriv_zero`: vanishing derivative ⟺ (2.6).
* (2.6) ⟺ (2.8): `eq26_iff_eq28`.

## Proposition 3.4

`DiffStationary` makes "difference-stationary" precise: `|E_t x_{t+j} − x_t| ≤ K j` uniformly
(the survey's `E_t log P_{t+j} = O(j)`); `BoundedIncr` is bounded first differences. The forward
sums of (2.8) and (B.14) (the core `forwardSeries`) are handled for such unbounded processes by
`fwd_decomp`, `ForwardSolution.E_tsum_dom`, `E_fwd_succ`, `fwd_rec` (the tower property),
`fwd_diffStationary`, `fwd_boundedIncr`, and
`forward_unique_growth` (the book's growth argument). Then:

* `prop34`: (2.9) (`Psol`, `psol_eq29`) solves (2.5) and (2.8) with predetermined price index and
  bounded inflation, and is the unique solution with predetermined difference-stationary price
  index (`prop34_unique`); `prop34_exists_iff`: such a solution exists iff the initial gap
  `log P_{−1} − log S_0` is bounded (`prop34_init_necessary`; automatic under perfect foresight).
* `prop34_continuum`, `prop34_continuum_injective`, `perturbation_not_diffStationary`: when
  `ω̃θ > 0` there is a continuum of further solutions `Pcont c` (adding `c(λ₂ᵗ − λ₁ᵗ)`), all
  outside the class; `perturbation_not_summable`: for `ω̃θ < 0` these perturbations violate (2.8),
  and `prop34_pf_unique_of_w_neg` shows uniqueness among all perfect-foresight solutions;
  `prop34_unique_of_w_zero`: for `ω̃θ = 0` the solution is unique among all solutions.
* Survey error E4 (B.3, p. 659): `recursive_reset_price` is the correct recursive form, with
  `+ω̃θ log P_t`, and `recursive_iff_B13`, `B13_iff_B14` give (B.13)/(B.14) from it;
  `printed_E4_fails` refutes the printed `−ω̃θ log P_t`.
* `flexible_limit`: as `ξ → ∞`, (2.9) gives `log P_t = log µ + log S_t` (p. 183).
-/

namespace Woodford.NominalRigidities.Calvo

open MeasureTheory Filter Topology
open DixitStiglitz (priceIndex priceIndex_pos priceIndex_rpow_of_ne integral_pos_of_pos)

/-! ### The Dixit–Stiglitz index and the Calvo recursion (2.1)

The Dixit–Stiglitz index is `DixitStiglitz.priceIndex` (with `priceIndex_rpow_of_ne`,
`priceIndex_pos`, `integral_pos_of_pos`). -/

/-- Woodford (2003), p. 178: integrating against the Calvo mixture `α ν + (1 − α) δ_{p*}` gives
`α ∫ f dν + (1 − α) f(p*)` (restated from the Galí Chapter 3 project). -/
theorem integral_calvo_mix {ν : Measure ℝ} {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (pstar : ℝ)
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    ∫ x, f x ∂(ENNReal.ofReal α • ν + ENNReal.ofReal (1 - α) • Measure.dirac pstar)
      = α * ∫ x, f x ∂ν + (1 - α) * f pstar := by
  have hd : Integrable f (Measure.dirac pstar) := integrable_dirac (by simp)
  rw [integral_add_measure (hf.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul]

/-- Woodford (2003), p. 178 (**law of motion of the price distribution**; restated from the Galí
Chapter 3 project). Goods `(F, m)`; those in `S` (mass `1 − α`) get the new price `p*`, the rest
keep `p_{t−1}`, and the unchanged prices are a representative subsample (their distribution is
`α` times that of all prices). Then `ν_t = α ν_{t−1} + (1 − α) δ_{p*}`, `ν_s = m.map p_s`. -/
theorem dist_law_of_motion {F : Type*} [MeasurableSpace F] (m : Measure F) {α : ℝ}
    {S : Set F} (hS : MeasurableSet S) {pprev pnow : F → ℝ} (hnow : Measurable pnow)
    {pstar : ℝ} (hreset : ∀ i ∈ S, pnow i = pstar) (hkeep : ∀ i ∉ S, pnow i = pprev i)
    (hmass : m S = ENNReal.ofReal (1 - α))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal α • m.map pprev) :
    m.map pnow = ENNReal.ofReal α • m.map pprev + ENNReal.ofReal (1 - α) • Measure.dirac pstar := by
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := m) hS]
  rw [Measure.map_add _ _ hnow]
  have h1 : (m.restrict S).map pnow = ENNReal.ofReal (1 - α) • Measure.dirac pstar := by
    rw [Measure.map_congr (g := fun _ => pstar) ((ae_restrict_iff' hS).2
      (Filter.Eventually.of_forall hreset)), Measure.map_const, Measure.restrict_apply_univ,
      hmass]
  have h2 : (m.restrict Sᶜ).map pnow = (m.restrict Sᶜ).map pprev :=
    Measure.map_congr ((ae_restrict_iff' hS.compl).2 (Filter.Eventually.of_forall hkeep))
  rw [h1, h2, hind, add_comm]

/-- Woodford (2003), eq. (2.1), p. 178, first display (**the Calvo index recursion**, exact, as
an integral): with the firm-level hypotheses of `dist_law_of_motion`,
`∫ p_t(i)^{1−θ} di = (1 − α) p*_t^{1−θ} + α P_{t−1}^{1−θ}`. -/
theorem calvo_integral {F : Type*} [MeasurableSpace F] (m : Measure F) {θ α : ℝ}
    (hθ : θ ≠ 1) (h0 : 0 ≤ α) (h1 : α < 1) {S : Set F} (hS : MeasurableSet S)
    {pprev pnow : F → ℝ} (hprev : Measurable pprev) (hnow : Measurable pnow) {pstar : ℝ}
    (hreset : ∀ i ∈ S, pnow i = pstar)
    (hkeep : ∀ i ∉ S, pnow i = pprev i) (hmass : m S = ENNReal.ofReal (1 - α))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal α • m.map pprev)
    (hint : Integrable (fun i => pprev i ^ (1 - θ)) m)
    (hpos : 0 < ∫ i, pprev i ^ (1 - θ) ∂m) :
    ∫ i, pnow i ^ (1 - θ) ∂m
      = (1 - α) * pstar ^ (1 - θ) + α * priceIndex m θ pprev ^ (1 - θ) := by
  have hmeas : Measurable fun x : ℝ => x ^ (1 - θ) := measurable_id.pow_const _
  have hmap : ∀ p : F → ℝ, Measurable p →
      ∫ i, p i ^ (1 - θ) ∂m = ∫ x, x ^ (1 - θ) ∂(m.map p) := fun p hp =>
    (integral_map hp.aemeasurable hmeas.aestronglyMeasurable).symm
  have hint' : Integrable (fun x : ℝ => x ^ (1 - θ)) (m.map pprev) :=
    (integrable_map_measure hmeas.aestronglyMeasurable hprev.aemeasurable).2 hint
  rw [hmap pnow hnow, dist_law_of_motion m hS hnow hreset hkeep hmass hind,
    integral_calvo_mix h0 h1.le pstar hint', ← hmap pprev hprev,
    priceIndex_rpow_of_ne (μ := m) hθ hpos]
  ring

/-- Woodford (2003), eq. (2.1), p. 178, first display (**the Calvo index recursion**, exact):
with the firm-level hypotheses of `dist_law_of_motion`,
`P_t^{1−θ} = (1 − α) p*_t^{1−θ} + α P_{t−1}^{1−θ}`. -/
theorem calvo_index_rpow {F : Type*} [MeasurableSpace F] (m : Measure F) {θ α : ℝ}
    (hθ : θ ≠ 1) (h0 : 0 ≤ α) (h1 : α < 1) {S : Set F} (hS : MeasurableSet S)
    {pprev pnow : F → ℝ} (hprev : Measurable pprev) (hnow : Measurable pnow) {pstar : ℝ}
    (hpstar : 0 < pstar) (hreset : ∀ i ∈ S, pnow i = pstar)
    (hkeep : ∀ i ∉ S, pnow i = pprev i) (hmass : m S = ENNReal.ofReal (1 - α))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal α • m.map pprev)
    (hint : Integrable (fun i => pprev i ^ (1 - θ)) m)
    (hpos : 0 < ∫ i, pprev i ^ (1 - θ) ∂m) :
    priceIndex m θ pnow ^ (1 - θ)
      = (1 - α) * pstar ^ (1 - θ) + α * priceIndex m θ pprev ^ (1 - θ) := by
  have h := calvo_integral m hθ h0 h1 hS hprev hnow hreset hkeep hmass hind hint hpos
  have hnowpos : 0 < ∫ i, pnow i ^ (1 - θ) ∂m := by
    rw [h]
    have : 0 < (1 - α) * pstar ^ (1 - θ) :=
      mul_pos (by linarith) (Real.rpow_pos_of_pos hpstar _)
    have : 0 ≤ α * priceIndex m θ pprev ^ (1 - θ) :=
      mul_nonneg h0 (Real.rpow_nonneg (priceIndex_pos (μ := m) (θ := θ) hpos).le _)
    linarith
  rw [priceIndex_rpow_of_ne (μ := m) hθ hnowpos, h]

/-- Woodford (2003), eq. (2.1), p. 178 (**the Calvo index recursion**, exact):
`P_t = [(1 − α) p*_t^{1−θ} + α P_{t−1}^{1−θ}]^{1/(1−θ)}`. -/
theorem calvo_index {F : Type*} [MeasurableSpace F] (m : Measure F) {θ α : ℝ}
    (hθ : θ ≠ 1) (h0 : 0 ≤ α) (h1 : α < 1) {S : Set F} (hS : MeasurableSet S)
    {pprev pnow : F → ℝ} (hprev : Measurable pprev) (hnow : Measurable pnow) {pstar : ℝ}
    (hreset : ∀ i ∈ S, pnow i = pstar)
    (hkeep : ∀ i ∉ S, pnow i = pprev i) (hmass : m S = ENNReal.ofReal (1 - α))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal α • m.map pprev)
    (hint : Integrable (fun i => pprev i ^ (1 - θ)) m)
    (hpos : 0 < ∫ i, pprev i ^ (1 - θ) ∂m) :
    priceIndex m θ pnow
      = ((1 - α) * pstar ^ (1 - θ) + α * priceIndex m θ pprev ^ (1 - θ)) ^ (1 - θ)⁻¹ := by
  conv_lhs => rw [priceIndex]
  rw [calvo_integral m hθ h0 h1 hS hprev hnow hreset hkeep hmass hind hint hpos]

/-- Woodford (2003), p. 177 (**the Calvo lottery gives a representative subsample**; restated
from the Galí Chapter 3 project): for any probability space of goods `(Ω, μ₀)` with prices `p`,
give each good an independent uniform draw `u ∈ [0, 1]` and let its price change iff `u > α`.
On `Ω × [0, 1]` with the product measure the changed prices have mass `1 − α`, the unchanged
prices' distribution is `α` times the full one, and the full distribution is that of `p`. -/
theorem lottery_model {Ω : Type*} [MeasurableSpace Ω] (μ₀ : Measure Ω)
    [IsProbabilityMeasure μ₀] {p : Ω → ℝ} (hp : Measurable p) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α ≤ 1) :
    μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.univ ×ˢ Set.Ioi α)
        = ENNReal.ofReal (1 - α) ∧
      ((μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).restrict (Set.univ ×ˢ Set.Ioi α)ᶜ).map
          (fun x => p x.1)
        = ENNReal.ofReal α •
          (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map (fun x => p x.1) ∧
      (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map (fun x => p x.1) = μ₀.map p := by
  have hfst : ∀ ν : Measure ℝ, SFinite ν →
      (μ₀.prod ν).map (fun x => p x.1) = ν Set.univ • μ₀.map p := by
    intro ν _
    have : (fun x : Ω × ℝ => p x.1) = p ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map hp measurable_fst, Measure.map_fst_prod, Measure.map_smul]
    exact hp.aemeasurable
  have hall : (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map (fun x => p x.1)
      = μ₀.map p := by
    rw [hfst _ inferInstance, Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  refine ⟨?_, ?_, hall⟩
  · rw [Measure.prod_prod, measure_univ, one_mul,
      Measure.restrict_apply measurableSet_Ioi]
    have : Set.Ioi α ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc α 1 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by linarith, h'⟩
    rw [this, Real.volume_Ioc]
  · have hc : (Set.univ ×ˢ Set.Ioi α : Set (Ω × ℝ))ᶜ = Set.univ ×ˢ Set.Iic α := by
      ext x
      simp
    rw [hc, ← Measure.prod_restrict, Measure.restrict_univ, hfst _ inferInstance, hall,
      Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Iic]
    have : Set.Iic α ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 α := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h, h', -⟩; exact ⟨h', h⟩
      · rintro ⟨h, h'⟩; exact ⟨h', h, by linarith⟩
    rw [this, Real.volume_Icc, sub_zero]

/-- Woodford (2003), eq. (2.1), p. 178, for the **explicit Calvo-lottery economy** of
`lottery_model`: goods `(ω, u) ∈ Ω × [0, 1]`, last period's price `p ω`, and this period's price
`p*` if `u > α` and `p ω` otherwise. Then `P_t^{1−θ} = (1 − α)p*^{1−θ} + α P_{t−1}^{1−θ}`. -/
theorem calvo_index_lottery {Ω : Type*} [MeasurableSpace Ω] (μ₀ : Measure Ω)
    [IsProbabilityMeasure μ₀] {θ α : ℝ} (hθ : θ ≠ 1) (h0 : 0 ≤ α) (h1 : α < 1) {p : Ω → ℝ}
    (hp : Measurable p) (hp0 : ∀ ω, 0 < p ω) (hint : Integrable (fun ω => p ω ^ (1 - θ)) μ₀)
    {pstar : ℝ} (hpstar : 0 < pstar) :
    priceIndex (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) θ
        (fun x => if α < x.2 then pstar else p x.1) ^ (1 - θ)
      = (1 - α) * pstar ^ (1 - θ) + α * priceIndex μ₀ θ p ^ (1 - θ) := by
  obtain ⟨hmass, hind, hall⟩ := lottery_model μ₀ hp h0 h1.le
  have hmeas : Measurable fun x : ℝ => x ^ (1 - θ) := measurable_id.pow_const _
  have hpp : Measurable fun x : Ω × ℝ => p x.1 := hp.comp measurable_fst
  have hI : ∫ x, p x.1 ^ (1 - θ) ∂(μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ∫ ω, p ω ^ (1 - θ) ∂μ₀ := by
    rw [← integral_map hpp.aemeasurable hmeas.aestronglyMeasurable, hall,
      integral_map hp.aemeasurable hmeas.aestronglyMeasurable]
  have hidx : priceIndex (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) θ (fun x => p x.1)
      = priceIndex μ₀ θ p := by
    unfold priceIndex
    rw [hI]
  have hint' : Integrable (fun x => p x.1 ^ (1 - θ))
      (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have := (integrable_map_measure hmeas.aestronglyMeasurable hp.aemeasurable).2 hint
    rw [← hall] at this
    exact (integrable_map_measure hmeas.aestronglyMeasurable hpp.aemeasurable).1 this
  have hpos : 0 < ∫ ω, p ω ^ (1 - θ) ∂μ₀ :=
    integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ₀)
      (fun ω => Real.rpow_pos_of_pos (hp0 ω) _) hint
  have hS : MeasurableSet (Set.univ ×ˢ Set.Ioi α : Set (Ω × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioi
  have hnow : Measurable fun x : Ω × ℝ => if α < x.2 then pstar else p x.1 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const hpp
  rw [← hidx]
  refine calvo_index_rpow _ hθ h0 h1 hS hpp hnow hpstar ?_ ?_ hmass hind hint'
    (by rw [hI]; exact hpos)
  · intro x hx
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hx
    simp only [hx, ↓reduceIte]
  · intro x hx
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hx
    simp only [hx, ↓reduceIte]

/-- Woodford (2003), p. 178 ("one need only know its initial value and the single new price
`p*_t` that is chosen each period"; **decomposition by date of last price change**): if
`X_{s+1} = (1 − α) Y_{s+1} + α X_s` (with `X = P^{1−θ}`, `Y = p*^{1−θ}`), then
`X_{t+k} = αᵏ X_t + ∑_{h<k} (1 − α) α^{k−1−h} Y_{t+h+1}`: mass `αᵏ` still charges date-`t`
prices and mass `(1 − α)α^{k−1−h}` last changed price at `t + h + 1`. -/
theorem cohort_decomposition {α : ℝ} {X Y : ℕ → ℝ}
    (hrec : ∀ s, X (s + 1) = (1 - α) * Y (s + 1) + α * X s) (t k : ℕ) :
    X (t + k) = α ^ k * X t + ∑ h ∈ Finset.range k, (1 - α) * α ^ (k - 1 - h) * Y (t + h + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, hrec, ih, Finset.sum_range_succ, mul_add, Finset.mul_sum]
    have hs : ∀ h ∈ Finset.range k, α * ((1 - α) * α ^ (k - 1 - h) * Y (t + h + 1))
        = (1 - α) * α ^ (k + 1 - 1 - h) * Y (t + h + 1) := by
      intro h hh
      rw [Finset.mem_range] at hh
      rw [show k + 1 - 1 - h = (k - 1 - h) + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl hs, show k + 1 - 1 - k = 0 by omega, pow_zero, pow_succ]
    ring

/-- Woodford (2003), p. 178: the cohort weights add up to one,
`αᵏ + ∑_{h<k} (1 − α) α^{k−1−h} = 1`. -/
theorem cohort_weights_sum (α : ℝ) (k : ℕ) :
    α ^ k + ∑ h ∈ Finset.range k, (1 - α) * α ^ (k - 1 - h) = 1 := by
  have h := cohort_decomposition (α := α) (X := fun _ => 1) (Y := fun _ => 1)
    (fun _ => by ring) 0 k
  simpa using h.symm

/-! ### The reset-price problem (2.2)–(2.4) -/


variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eq. (2.2), p. 178 (**the reset-price objective**): the genuine infinite
discounted sum `∑_{k ≥ 0} αᵏ E_t[Q_{t,t+k} Π(p, p^I_{t+k}, P_{t+k}; Y_{t+k}, ξ̃_{t+k})]`, where
`prof k ω p` is the horizon-`k` nominal profit (1.17) at the state `ω` when the price is `p`,
and `Q k` is the stochastic discount factor `Q_{t,t+k}`. -/
noncomputable def resetObjective (α : ℝ) (Q : ℕ → Ω → ℝ) (prof : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (p : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, α ^ k * 𝔼.E t (fun ω' => Q k ω' * prof k ω' p) ω

/-- Woodford (2003), eq. (2.3), p. 179: the left-hand side of the first-order condition,
`∑_{k ≥ 0} αᵏ E_t[Q_{t,t+k} Π₁(p, …)]`, where `dprof k ω p` is the marginal profit `Π₁`. -/
noncomputable def resetFOC (α : ℝ) (Q : ℕ → Ω → ℝ) (dprof : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (p : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, α ^ k * 𝔼.E t (fun ω' => Q k ω' * dprof k ω' p) ω

/-- Woodford (2003), p. 179 (differentiating (2.2) under `E_t`; restated from the Galí Chapter 3
project): if the second-order remainder of `z ↦ g z` at `x` is bounded by `C h²` uniformly in the
state, then `z ↦ E_t[g z]` has derivative `E_t[g']` at `x`. -/
theorem hasDerivAt_E_of_remainder {g : ℝ → Ω → ℝ} {g' : Ω → ℝ} {x C δ : ℝ} (hδ : 0 < δ)
    (hrem : ∀ h, |h| < δ → ∀ ω, |g (x + h) ω - g x ω - h * g' ω| ≤ C * h ^ 2)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t g' ω) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h => 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω)
      =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    have hh' : |h| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hh
    have key : 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω
        = 𝔼.E t (g (x + h) - g x - h • g') ω := by
      simp [map_sub, map_smul]
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    exact 𝔼.abs_E_le (fun ω' => by simpa [smul_eq_mul] using hrem h hh' ω') t ω
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

omit 𝔼 in
/-- Woodford (2003), p. 179 (restated from the Galí Chapter 3 project): a Lipschitz bound on
the derivative bounds the second-order remainder, `|f(x+h) − f(x) − h f'(x)| ≤ L h²`. -/
theorem remainder_le_of_lipschitz_deriv {f f' : ℝ → ℝ} {x r L : ℝ} (hL0 : 0 ≤ L)
    (hf : ∀ y ∈ Metric.ball x r, HasDerivAt f (f' y) y)
    (hL : ∀ y ∈ Metric.ball x r, |f' y - f' x| ≤ L * |y - x|) {h : ℝ} (hh : |h| < r) :
    |f (x + h) - f x - h * f' x| ≤ L * h ^ 2 := by
  have hsub : Metric.closedBall x |h| ⊆ Metric.ball x r :=
    Metric.closedBall_subset_ball hh
  have hd : ∀ y ∈ Metric.closedBall x |h|,
      HasDerivWithinAt (fun z => f z - z * f' x) (f' y - f' x) (Metric.closedBall x |h|) y := by
    intro y hy
    have h1 := hf y (hsub hy)
    have h2 : HasDerivAt (fun z : ℝ => z * f' x) (f' x) y := by
      simpa using (hasDerivAt_id y).mul_const (f' x)
    exact (HasDerivAt.sub h1 h2).hasDerivWithinAt
  have hb : ∀ y ∈ Metric.closedBall x |h|, ‖f' y - f' x‖ ≤ L * |h| := by
    intro y hy
    rw [Real.norm_eq_abs]
    refine (hL y (hsub hy)).trans (mul_le_mul_of_nonneg_left ?_ hL0)
    simpa [Metric.mem_closedBall, Real.dist_eq] using hy
  have hx : x ∈ Metric.closedBall x |h| := Metric.mem_closedBall_self (abs_nonneg h)
  have hxh : x + h ∈ Metric.closedBall x |h| := by
    simp [Metric.mem_closedBall]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_closedBall x |h|) hx hxh
  rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left] at this
  calc |f (x + h) - f x - h * f' x| = |f (x + h) - (x + h) * f' x - (f x - x * f' x)| := by
        ring_nf
    _ ≤ L * |h| * |h| := this
    _ = L * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- Woodford (2003), p. 179 (differentiation under `E_t`, Lipschitz form; restated from the Galí
Chapter 3 project): if `z ↦ g z ω` has derivative `g' z ω` near `x`, Lipschitz at `x` uniformly in
the state, then `z ↦ E_t[g z]` has derivative `E_t[g' x]` at `x`. -/
theorem hasDerivAt_E {g g' : ℝ → Ω → ℝ} {x r L : ℝ} (hr : 0 < r) (hL0 : 0 ≤ L)
    (hg : ∀ y ∈ Metric.ball x r, ∀ ω, HasDerivAt (fun z => g z ω) (g' y ω) y)
    (hL : ∀ y ∈ Metric.ball x r, ∀ ω, |g' y ω - g' x ω| ≤ L * |y - x|) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t (g' x) ω) x :=
  hasDerivAt_E_of_remainder 𝔼 hr (fun _ hh ω' => remainder_le_of_lipschitz_deriv hL0
    (fun y hy => hg y hy ω') (fun y hy => hL y hy ω') hh) t ω

/-- Woodford (2003), eqs. (2.2)–(2.3), p. 179 (term-by-term differentiation of a discounted sum
of conditional expectations; restated from the Galí Chapter 3 project): `z ↦ ∑ₖ αᵏ E_t[gₖ z]`
has derivative `∑ₖ αᵏ E_t[g'ₖ x]` on an open interval `U`, provided each `g'ₖ` is locally
Lipschitz uniformly in the state and dominated by `uₖ` with `∑ |α|ᵏ uₖ < ∞`, and the series
converges at one point of `U`. -/
theorem hasDerivAt_tsum_E {α : ℝ} {g g' : ℕ → ℝ → Ω → ℝ} {U : Set ℝ} {u : ℕ → ℝ}
    (hU : IsOpen U) (hU' : IsPreconnected U)
    (hg : ∀ k, ∀ y ∈ U, ∀ ω, HasDerivAt (fun z => g k z ω) (g' k y ω) y)
    (hLip : ∀ k, ∀ y ∈ U, ∃ L, 0 ≤ L ∧ ∃ r > 0,
      ∀ z ∈ Metric.ball y r, ∀ ω, |g' k z ω - g' k y ω| ≤ L * |z - y|)
    (hdom : ∀ k, ∀ y ∈ U, ∀ ω, |g' k y ω| ≤ u k) (hu : Summable fun k => |α| ^ k * u k)
    {y₀ : ℝ} (hy₀ : y₀ ∈ U) (t : ℕ) (ω : Ω)
    (hs : Summable fun k => α ^ k * 𝔼.E t (g k y₀) ω) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun z => ∑' k, α ^ k * 𝔼.E t (g k z) ω)
      (∑' k, α ^ k * 𝔼.E t (g' k x) ω) x := by
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k => |α| ^ k * u k)
    (g := fun k z => α ^ k * 𝔼.E t (g k z) ω) (g' := fun k z => α ^ k * 𝔼.E t (g' k z) ω)
    hu hU hU' (fun k y hy => ?_) (fun k y hy => ?_) hy₀ hs hx
  · obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.mp hU y hy
    obtain ⟨L, hL0, r, hr, hL⟩ := hLip k y hy
    have hsub : Metric.ball y (min r r₁) ⊆ Metric.ball y r₁ :=
      Metric.ball_subset_ball (min_le_right _ _)
    have hsub' : Metric.ball y (min r r₁) ⊆ Metric.ball y r :=
      Metric.ball_subset_ball (min_le_left _ _)
    exact (hasDerivAt_E 𝔼 (lt_min hr hr₁) hL0 (fun z hz ω' => hg k z (hball (hsub hz)) ω')
      (fun z hz ω' => hL z (hsub' hz) ω') t ω).const_mul (α ^ k)
  · rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdom k y hy) t ω)
      (pow_nonneg (abs_nonneg α) k)

/-- Woodford (2003), eqs. (2.2)–(2.3), p. 179 (**the derivative of the reset-price objective**):
under local-Lipschitz and domination hypotheses on discounted marginal profits
`Q_{t,t+k} Π₁`, and convergence of (2.2) at one price, the objective (2.2) has derivative
`∑ₖ αᵏ E_t[Q_{t,t+k} Π₁(p, …)]` at every price of an open interval `U`. -/
theorem hasDerivAt_resetObjective {α : ℝ} {Q : ℕ → Ω → ℝ} {prof dprof : ℕ → Ω → ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) (hU' : IsPreconnected U)
    (hprof : ∀ k ω, ∀ y ∈ U, HasDerivAt (prof k ω) (dprof k ω y) y)
    (hLip : ∀ k, ∀ y ∈ U, ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |Q k ω * dprof k ω z - Q k ω * dprof k ω y| ≤ L * |z - y|)
    {u : ℕ → ℝ} (hdom : ∀ k, ∀ y ∈ U, ∀ ω, |Q k ω * dprof k ω y| ≤ u k)
    (hu : Summable fun k => |α| ^ k * u k) {y₀ : ℝ} (hy₀ : y₀ ∈ U) (t : ℕ) (ω : Ω)
    (hs : Summable fun k => α ^ k * 𝔼.E t (fun ω' => Q k ω' * prof k ω' y₀) ω)
    {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun p => resetObjective 𝔼 α Q prof t p ω) (resetFOC 𝔼 α Q dprof t x ω) x :=
  hasDerivAt_tsum_E 𝔼 (g := fun k z ω' => Q k ω' * prof k ω' z)
    (g' := fun k z ω' => Q k ω' * dprof k ω' z) hU hU'
    (fun k y hy ω' => (hprof k ω' y hy).const_mul (Q k ω')) hLip hdom hu hy₀ t ω hs hx

/-- Woodford (2003), eq. (2.3), p. 179 (**the first-order condition is necessary**): if `p` is
a local maximum of the objective (2.2) at which it has the derivative of
`hasDerivAt_resetObjective`, then `∑ₖ αᵏ E_t[Q_{t,t+k} Π₁(p, …)] = 0`. -/
theorem foc_of_isLocalMax {α : ℝ} {Q : ℕ → Ω → ℝ} {prof dprof : ℕ → Ω → ℝ → ℝ} {t : ℕ}
    {ω : Ω} {x : ℝ}
    (hder : HasDerivAt (fun p => resetObjective 𝔼 α Q prof t p ω) (resetFOC 𝔼 α Q dprof t x ω) x)
    (hmax : IsLocalMax (fun p => resetObjective 𝔼 α Q prof t p ω) x) :
    resetFOC 𝔼 α Q dprof t x ω = 0 :=
  hmax.hasDerivAt_eq_zero hder

/-- Woodford (2003), eq. (2.2), p. 178: if every horizon's profit is concave in the price on a
convex set `U`, discount factors are nonnegative and the objective converges on `U`, then the
objective (2.2) is concave on `U`. -/
theorem concaveOn_resetObjective {α : ℝ} (hα : 0 ≤ α) {Q : ℕ → Ω → ℝ}
    {prof : ℕ → Ω → ℝ → ℝ} {U : Set ℝ} (hUc : Convex ℝ U) (hQ : ∀ k ω, 0 ≤ Q k ω)
    (hconc : ∀ k ω, ConcaveOn ℝ U (prof k ω)) (t : ℕ) (ω : Ω)
    (hs : ∀ y ∈ U, Summable fun k => α ^ k * 𝔼.E t (fun ω' => Q k ω' * prof k ω' y) ω) :
    ConcaveOn ℝ U (fun p => resetObjective 𝔼 α Q prof t p ω) := by
  refine ⟨hUc, fun x hx y hy a b ha hb hab => ?_⟩
  dsimp only [resetObjective, smul_eq_mul]
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add ((hs x hx).mul_left a)
    ((hs y hy).mul_left b)]
  refine Summable.tsum_le_tsum (fun k => ?_) (((hs x hx).mul_left a).add ((hs y hy).mul_left b))
    (hs _ (hUc hx hy ha hb hab))
  have hpt : (a • fun ω' => Q k ω' * prof k ω' x) + (b • fun ω' => Q k ω' * prof k ω' y)
      ≤ fun ω' => Q k ω' * prof k ω' (a • x + b • y) := by
    intro ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h := (hconc k ω').2 hx hy ha hb hab
    simp only [smul_eq_mul] at h
    nlinarith [hQ k ω']
  have hE := 𝔼.mono t hpt ω
  rw [map_add, map_smul, map_smul] at hE
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hE
  nlinarith [pow_nonneg hα k]

omit 𝔼 in
/-- Woodford (2003), p. 179: a concave function with zero derivative at a point of its convex
domain attains its maximum there. -/
theorem isMaxOn_of_concaveOn_of_deriv_zero {f : ℝ → ℝ} {U : Set ℝ} (hf : ConcaveOn ℝ U f)
    {x : ℝ} (hx : x ∈ U) (hd : HasDerivAt f 0 x) : IsMaxOn f U x := by
  intro y hy
  change f y ≤ f x
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := hf.slope_le_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field] at h
    have : f y - f x ≤ 0 := by
      have hpos : 0 < y - x := by linarith
      by_contra hc
      push Not at hc
      have := div_pos hc hpos
      linarith
    linarith
  · exact le_rfl
  · have h := hf.le_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field] at h
    have : f x - f y ≥ 0 := by
      have hpos : 0 < x - y := by linarith
      by_contra hc
      push Not at hc
      have := div_neg_of_neg_of_pos hc hpos
      linarith
    linarith

/-- Woodford (2003), eqs. (2.2)–(2.4), p. 179 (**the first-order condition characterises the
optimal reset price**, concave profits): on an open convex set of prices `U`, with the
objective differentiable at `x ∈ U`, `x` maximises (2.2) over `U` iff (2.3) holds at `x`. -/
theorem isMaxOn_iff_foc {α : ℝ} (hα : 0 ≤ α) {Q : ℕ → Ω → ℝ} {prof dprof : ℕ → Ω → ℝ → ℝ}
    {U : Set ℝ} (hUo : IsOpen U) (hUc : Convex ℝ U) (hQ : ∀ k ω, 0 ≤ Q k ω)
    (hconc : ∀ k ω, ConcaveOn ℝ U (prof k ω)) (t : ℕ) (ω : Ω)
    (hs : ∀ y ∈ U, Summable fun k => α ^ k * 𝔼.E t (fun ω' => Q k ω' * prof k ω' y) ω)
    {x : ℝ} (hx : x ∈ U)
    (hder : HasDerivAt (fun p => resetObjective 𝔼 α Q prof t p ω) (resetFOC 𝔼 α Q dprof t x ω)
      x) :
    IsMaxOn (fun p => resetObjective 𝔼 α Q prof t p ω) U x ↔ resetFOC 𝔼 α Q dprof t x ω = 0 := by
  constructor
  · intro hmax
    exact foc_of_isLocalMax 𝔼 hder (hmax.isLocalMax (hUo.mem_nhds hx))
  · intro h0
    rw [h0] at hder
    exact isMaxOn_of_concaveOn_of_deriv_zero
      (concaveOn_resetObjective 𝔼 hα hUc hQ hconc t ω hs) hx hder

/-- Woodford (2003), fn. 31, p. 179: replacing `αᵏ` by the indicator of `k = 1` turns (2.2) into
the one-period objective (1.22), `E_t[Q_{t,t+1} Π(p, …)]`. -/
theorem objective_fn31 (Q : ℕ → Ω → ℝ) (prof : ℕ → Ω → ℝ → ℝ) (t : ℕ) (p : ℝ) (ω : Ω) :
    ∑' k, (if k = 1 then (1 : ℝ) else 0) * 𝔼.E t (fun ω' => Q k ω' * prof k ω' p) ω
      = 𝔼.E t (fun ω' => Q 1 ω' * prof 1 ω' p) ω := by
  rw [tsum_eq_single 1 (fun k hk => by simp [hk])]
  simp

omit 𝔼 in
/-- Woodford (2003), Assumption 3.1, p. 153, and p. 154 ("`Π₁` must be a function that is
homogeneous of degree zero"): if `Π(p, p^I, P)` is homogeneous of degree one and has partial
derivative `Π₁` in its first argument at every positive price, then `Π₁` is homogeneous of degree
zero: `Π₁(λp, λp^I, λP) = Π₁(p, p^I, P)` for `λ > 0`, `p > 0`. -/
theorem hom_deg_zero_of_hom_deg_one {Pi Pi1 : ℝ → ℝ → ℝ → ℝ}
    (hhom : ∀ l, 0 < l → ∀ p q P, Pi (l * p) (l * q) (l * P) = l * Pi p q P)
    (hder : ∀ p q P, 0 < p → HasDerivAt (fun z => Pi z q P) (Pi1 p q P) p)
    {l : ℝ} (hl : 0 < l) {p : ℝ} (hp : 0 < p) (q P : ℝ) :
    Pi1 (l * p) (l * q) (l * P) = Pi1 p q P := by
  have h1 : HasDerivAt (fun z => Pi (l * z) (l * q) (l * P)) (Pi1 (l * p) (l * q) (l * P) * l) p :=
    (hder (l * p) (l * q) (l * P) (mul_pos hl hp)).comp p (by
      simpa using (hasDerivAt_id p).const_mul l)
  have h2 : HasDerivAt (fun z => Pi (l * z) (l * q) (l * P)) (l * Pi1 p q P) p := by
    have : (fun z => Pi (l * z) (l * q) (l * P)) = fun z => l * Pi z q P := by
      funext z; exact hhom l hl z q P
    rw [this]
    exact (hder p q P hp).const_mul l
  have := h1.unique h2
  rw [mul_comm] at this
  exact mul_left_cancel₀ hl.ne' this

omit 𝔼 in
/-- Woodford (2003), p. 158 ("`Π₁(p, p, P; Y, ξ̃)` depends only on the values of `p/P`, `Y`, and
`ξ̃`"): `Π₁(p, p, P) = Π₁(p/P, p/P, 1)` for `p, P > 0`. -/
theorem foc_relative_price {Pi Pi1 : ℝ → ℝ → ℝ → ℝ}
    (hhom : ∀ l, 0 < l → ∀ p q P, Pi (l * p) (l * q) (l * P) = l * Pi p q P)
    (hder : ∀ p q P, 0 < p → HasDerivAt (fun z => Pi z q P) (Pi1 p q P) p)
    {p P : ℝ} (hp : 0 < p) (hP : 0 < P) :
    Pi1 p p P = Pi1 (p / P) (p / P) 1 := by
  have h := hom_deg_zero_of_hom_deg_one hhom hder (l := P) hP (div_pos hp hP) (p / P) 1
  rw [mul_div_cancel₀ _ hP.ne', mul_one] at h
  exact h

/-- Woodford (2003), p. 179 (**the zero-inflation steady state**): if `ξ̃ = 0`, `Y = Ȳ` and
`Π₁(1, 1, 1; Ȳ, 0) = 0` ((1.21)), then `P_t = p*_t = P_{t−1} = P̄` solves (2.1) and (2.4): with
the marginal profit at horizon `k` equal to `Π₁(p*/P̄, p*/P̄, 1; Ȳ, 0) = 0`, the first-order
condition holds for any discount factors. -/
theorem steady_state_solves {θ α Pbar : ℝ} (hP : 0 < Pbar) (Q : ℕ → Ω → ℝ) {Pi1 : ℝ → ℝ → ℝ → ℝ}
    (hss : Pi1 1 1 1 = 0) (t : ℕ) :
    Pbar ^ (1 - θ) = (1 - α) * Pbar ^ (1 - θ) + α * Pbar ^ (1 - θ) ∧
      resetFOC 𝔼 α Q (fun _ _ p => Pi1 (p / Pbar) (p / Pbar) 1) t Pbar = 0 := by
  refine ⟨by ring, ?_⟩
  funext ω
  simp only [resetFOC, div_self hP.ne', hss, mul_zero]
  have : (fun _ : Ω => (0 : ℝ)) = fun _ => 0 := rfl
  rw [𝔼.const]
  simp

/-! ### (2.5) as the exact derivative of (2.1) -/

/-- Woodford (2003), eq. (2.1), p. 178, in logs: `log P_t` as a function of `x = log p*_t` and
`y = log P_{t−1}`, `(1 − θ)⁻¹ log((1 − α) e^{(1−θ)x} + α e^{(1−θ)y})`. -/
noncomputable def logIndexFn (α θ x y : ℝ) : ℝ :=
  (1 - θ)⁻¹ * Real.log ((1 - α) * Real.exp ((1 - θ) * x) + α * Real.exp ((1 - θ) * y))

omit 𝔼 in
/-- Woodford (2003), eq. (2.1), p. 178: if (2.1) holds then
`log P_t = logIndexFn α θ (log p*_t) (log P_{t−1})` exactly (`θ ≠ 1`, positive prices). -/
theorem log_calvo_index {α θ P pstar Pprev : ℝ} (hθ : θ ≠ 1) (hP : 0 < P) (hps : 0 < pstar)
    (hPp : 0 < Pprev) (hrec : P ^ (1 - θ) = (1 - α) * pstar ^ (1 - θ) + α * Pprev ^ (1 - θ)) :
    Real.log P = logIndexFn α θ (Real.log pstar) (Real.log Pprev) := by
  have hsub : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  have h := congrArg Real.log hrec
  rw [Real.log_rpow hP, Real.rpow_def_of_pos hps, Real.rpow_def_of_pos hPp,
    mul_comm (Real.log pstar), mul_comm (Real.log Pprev)] at h
  rw [logIndexFn, ← h]
  field_simp

omit 𝔼 in
/-- Woodford (2003), p. 179: on the diagonal (zero inflation, `p*_t = P_{t−1}`),
`logIndexFn α θ x x = x`, i.e. `P_t = p*_t = P_{t−1}`. -/
theorem logIndexFn_diag (α : ℝ) {θ : ℝ} (hθ : θ ≠ 1) (x : ℝ) : logIndexFn α θ x x = x := by
  have hsub : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  unfold logIndexFn
  rw [show (1 - α) * Real.exp ((1 - θ) * x) + α * Real.exp ((1 - θ) * x)
      = Real.exp ((1 - θ) * x) by ring, Real.log_exp]
  field_simp

omit 𝔼 in
/-- Woodford (2003), eq. (2.5), p. 180 (**(2.5) is the exact derivative of (2.1)**): at every
zero-inflation point `(x, x)` the map `(log p*_t, log P_{t−1}) ↦ log P_t` has Fréchet derivative
`(dx, dy) ↦ (1 − α) dx + α dy`, so `log P_t = α log P_{t−1} + (1 − α) log p*_t` to first order. -/
theorem hasFDerivAt_logIndexFn (α : ℝ) {θ : ℝ} (hθ : θ ≠ 1) (x : ℝ) :
    HasFDerivAt (fun v : ℝ × ℝ => logIndexFn α θ v.1 v.2)
      ((1 - α) • ContinuousLinearMap.fst ℝ ℝ ℝ + α • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, x) := by
  have hsub : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  have h1 : HasFDerivAt (fun v : ℝ × ℝ => (1 - θ) * v.1)
      ((1 - θ) • ContinuousLinearMap.fst ℝ ℝ ℝ) (x, x) := hasFDerivAt_fst.const_mul (1 - θ)
  have h2 : HasFDerivAt (fun v : ℝ × ℝ => (1 - θ) * v.2)
      ((1 - θ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, x) := hasFDerivAt_snd.const_mul (1 - θ)
  have hs := (h1.exp.const_mul (1 - α)).add (h2.exp.const_mul α)
  have hval : (1 - α) * Real.exp ((1 - θ) * (x, x).1) + α * Real.exp ((1 - θ) * (x, x).2)
      = Real.exp ((1 - θ) * x) := by simp only; ring
  have hne : (1 - α) * Real.exp ((1 - θ) * (x, x).1) + α * Real.exp ((1 - θ) * (x, x).2) ≠ 0 := by
    rw [hval]; exact (Real.exp_pos _).ne'
  have hl := (hs.log hne).const_mul (1 - θ)⁻¹
  refine hl.congr_fderiv ?_
  have hv2 : ((fun y : ℝ × ℝ => (1 - α) * Real.exp ((1 - θ) * y.1))
      + fun y : ℝ × ℝ => α * Real.exp ((1 - θ) * y.2)) (x, x) = Real.exp ((1 - θ) * x) := by
    simp only [Pi.add_apply]; ring
  rw [hv2]
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply,
    Pi.add_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  have he := (Real.exp_pos ((1 - θ) * x)).ne'
  field_simp

omit 𝔼 in
/-- Woodford (2003), eq. (2.5), p. 180, along a path: perturbing `log p*_t = x + s a` and
`log P_{t−1} = x + s b`, `log P_t` has derivative `(1 − α) a + α b` at `s = 0`. -/
theorem hasDerivAt_logIndexFn_path (α : ℝ) {θ : ℝ} (hθ : θ ≠ 1) (x a b : ℝ) :
    HasDerivAt (fun s => logIndexFn α θ (x + s * a) (x + s * b)) ((1 - α) * a + α * b) 0 := by
  have hγ : HasDerivAt (fun s : ℝ => (x + s * a, x + s * b)) (a, b) 0 := by
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).const_add x
    · simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add x
  have hF := hasFDerivAt_logIndexFn α hθ x
  have hγ0 : ((fun s : ℝ => (x + s * a, x + s * b)) 0) = (x, x) := by simp
  rw [← hγ0] at hF
  refine (hF.comp_hasDerivAt (0 : ℝ) hγ).congr_deriv ?_
  simp [smul_eq_mul]

/-! ### (2.6) as the exact derivative of the first-order condition (2.4) -/

omit 𝔼 in
/-- Woodford (2003), p. 180 (the derivative of the marginal-profit function): writing
`mp(x, y, z) = Π₁(eˣ, eˣ, 1; Ȳ eʸ, z)` (log relative price, log output deviation, disturbance),
a Fréchet derivative `D` of `mp` at the steady state `0` with `mp 0 = 0` gives the uniform
first-order expansion `|mp(sx, sy, sz) − s(ψ_p x + ψ_y y + ψ_z z)| ≤ ε|s|` for bounded
`(x, y, z)`, with `ψ_p = D(1,0,0)`, `ψ_y = D(0,1,0)`, `ψ_z = D(0,0,1)`. -/
theorem mp_uniform_expansion {mp : ℝ → ℝ → ℝ → ℝ} {D : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun v : ℝ × ℝ × ℝ => mp v.1 v.2.1 v.2.2) D 0) (h0 : mp 0 0 0 = 0)
    {B : ℝ} (hB : 0 ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s x y z : ℝ, |s| < δ → |x| ≤ B → |y| ≤ B → |z| ≤ B →
      |mp (s * x) (s * y) (s * z) - s * (D (1, 0, 0) * x + D (0, 1, 0) * y + D (0, 0, 1) * z)|
        ≤ ε * |s| := by
  have hlo := hD.isLittleO
  rw [Asymptotics.isLittleO_iff] at hlo
  have hε' : 0 < ε / (B + 1) := div_pos hε (by linarith)
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff.mp (hlo hε')
  refine ⟨δ₀ / (B + 1), div_pos hδ₀ (by linarith), fun s x y z hs hx hy hz => ?_⟩
  have hDv : D (s * x, s * y, s * z)
      = s * (D (1, 0, 0) * x + D (0, 1, 0) * y + D (0, 0, 1) * z) := by
    have : ((s * x, s * y, s * z) : ℝ × ℝ × ℝ)
        = (s * x) • ((1, 0, 0) : ℝ × ℝ × ℝ) + (s * y) • ((0, 1, 0) : ℝ × ℝ × ℝ)
          + (s * z) • ((0, 0, 1) : ℝ × ℝ × ℝ) := by
      ext <;> simp
    rw [this, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring
  have hnorm : ‖((s * x, s * y, s * z) : ℝ × ℝ × ℝ)‖ ≤ |s| * B := by
    rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_mul]
    refine max_le (mul_le_mul_of_nonneg_left hx (abs_nonneg s)) (max_le ?_ ?_)
    · exact mul_le_mul_of_nonneg_left hy (abs_nonneg s)
    · exact mul_le_mul_of_nonneg_left hz (abs_nonneg s)
  have hsB : |s| * B < δ₀ := by
    have h1 : |s| * B ≤ |s| * (B + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s)
    have h2 : |s| * (B + 1) < δ₀ := by rwa [lt_div_iff₀ (by linarith)] at hs
    linarith
  have hmem : dist ((s * x, s * y, s * z) : ℝ × ℝ × ℝ) 0 < δ₀ := by
    rw [dist_zero_right]; linarith
  have h := hball hmem
  simp only [h0, sub_zero, Prod.fst_zero, Prod.snd_zero] at h
  rw [Real.norm_eq_abs, hDv] at h
  calc _ ≤ ε / (B + 1) * ‖((s * x, s * y, s * z) : ℝ × ℝ × ℝ)‖ := h
    _ ≤ ε / (B + 1) * (|s| * B) := mul_le_mul_of_nonneg_left hnorm hε'.le
    _ ≤ ε * |s| := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [abs_nonneg s]

omit 𝔼 in
/-- Woodford (2003), p. 180: the stochastic-discount-factor perturbation `e^{s q}` multiplies a
term that vanishes at the steady state, so it does not affect the first-order expansion:
`|e^{sq} m(s) − s g| ≤ ε|s|` whenever `|m(s) − s g| ≤ ε'|s|`, for bounded `q`, `g`. -/
theorem exp_mul_expansion {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ ε' > 0, ∃ δ > 0, ∀ s q g m : ℝ, |s| < δ → |q| ≤ B → |g| ≤ B →
      |m - s * g| ≤ ε' * |s| → |Real.exp (s * q) * m - s * g| ≤ ε * |s| := by
  set E := Real.exp B with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hB
  refine ⟨ε / (2 * E), by positivity, min (1 / (B + 1)) (ε / (4 * (B + 1) ^ 2)),
    lt_min (by positivity) (by positivity), fun s q g m hs hq hg hm => ?_⟩
  have hs1 : |s| < 1 / (B + 1) := lt_of_lt_of_le hs (min_le_left _ _)
  have hs2 : |s| < ε / (4 * (B + 1) ^ 2) := lt_of_lt_of_le hs (min_le_right _ _)
  have hsB1 : |s| * (B + 1) < 1 := by rwa [lt_div_iff₀ (by linarith)] at hs1
  have hsq1 : |s * q| ≤ |s| * (B + 1) := by
    rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg q]
  have hsq : |s * q| ≤ B := by
    have : |s| ≤ 1 := by nlinarith [abs_nonneg s]
    rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg q]
  have hexp : Real.exp (s * q) ≤ E := Real.exp_le_exp.mpr ((le_abs_self _).trans hsq)
  have hexp1 : |Real.exp (s * q) - 1| ≤ 2 * (|s| * (B + 1)) :=
    (Real.abs_exp_sub_one_le (by linarith)).trans (by linarith)
  have key : Real.exp (s * q) * m - s * g
      = Real.exp (s * q) * (m - s * g) + (Real.exp (s * q) - 1) * (s * g) := by ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
  have t1 : Real.exp (s * q) * |m - s * g| ≤ E * (ε / (2 * E) * |s|) :=
    mul_le_mul hexp hm (abs_nonneg _) (by linarith)
  have t2 : |Real.exp (s * q) - 1| * (|s| * |g|) ≤ 2 * (|s| * (B + 1)) * (|s| * (B + 1)) := by
    refine mul_le_mul hexp1 (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s))
      (by positivity) (by positivity)
  have t3 : 2 * (|s| * (B + 1)) * (|s| * (B + 1)) ≤ ε / 2 * |s| := by
    have hB1 : 0 < (B + 1) ^ 2 := by positivity
    have : |s| * (B + 1) ^ 2 ≤ ε / 4 := by
      rw [lt_div_iff₀ (by positivity)] at hs2; linarith
    nlinarith [abs_nonneg s]
  have t1' : E * (ε / (2 * E) * |s|) = ε / 2 * |s| := by field_simp
  linarith

/-- Woodford (2003), pp. 179–180 (differentiating (2.4) under `E_t` and the infinite sum at the
steady state): if `gₖ(s) − s g'ₖ = o(s)` uniformly in `k` and the state, and the `g'ₖ` are
uniformly bounded, then `s ↦ ∑ₖ aᵏ E_t[gₖ(s)]` has derivative `∑ₖ aᵏ E_t[g'ₖ]` at `s = 0`
(`0 ≤ a < 1`). -/
theorem hasDerivAt_tsum_E_of_expansion {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {g : ℕ → ℝ → Ω → ℝ} {g' : ℕ → Ω → ℝ} {B : ℝ} (hg'b : ∀ k ω, |g' k ω| ≤ B)
    (hexp : ∀ ε > 0, ∃ δ > 0, ∀ s, |s| < δ → ∀ k ω, |g k s ω - s * g' k ω| ≤ ε * |s|)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => ∑' k, a ^ k * 𝔼.E t (g k s) ω) (∑' k, a ^ k * 𝔼.E t (g' k) ω) 0 := by
  have hgeo := summable_geometric_of_lt_one ha0 ha1
  -- `g k 0 = 0`
  have hg0 : ∀ k, g k 0 = 0 := by
    intro k
    funext ω'
    obtain ⟨δ, hδ, h⟩ := hexp 1 one_pos
    have := h 0 (by simpa using hδ) k ω'
    simpa using this
  have hF0 : ∑' k, a ^ k * 𝔼.E t (g k 0) ω = 0 := by
    simp [hg0]
  have hsum' : Summable (fun k => a ^ k * 𝔼.E t (g' k) ω) := by
    refine Summable.of_norm_bounded (hgeo.mul_right B) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0 k)]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hg'b k) t ω) (pow_nonneg ha0 k)
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hca : 0 < c * (1 - a) := mul_pos hc (by linarith)
  obtain ⟨δ, hδ, h⟩ := hexp (c * (1 - a)) hca
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with s hs
  have hs' : |s| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hs
  have hb : ∀ k ω', |(g k s - s • g' k) ω'| ≤ c * (1 - a) * |s| := fun k ω' => by
    simpa [smul_eq_mul] using h s hs' k ω'
  have hsumd : Summable (fun k => a ^ k * 𝔼.E t (g k s - s • g' k) ω) := by
    refine Summable.of_norm_bounded (hgeo.mul_right (c * (1 - a) * |s|)) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0 k)]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hb k) t ω) (pow_nonneg ha0 k)
  have hsum : Summable (fun k => a ^ k * 𝔼.E t (g k s) ω) := by
    refine (hsumd.add (hsum'.mul_left s)).congr (fun k => ?_)
    rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hexpr : ∑' k, a ^ k * 𝔼.E t (g k (0 + s)) ω - ∑' k, a ^ k * 𝔼.E t (g k 0) ω
      - s • ∑' k, a ^ k * 𝔼.E t (g' k) ω
      = ∑' k, a ^ k * 𝔼.E t (g k s - s • g' k) ω := by
    rw [zero_add, hF0, sub_zero, smul_eq_mul, ← tsum_mul_left, ← hsum.tsum_sub
      (hsum'.mul_left s)]
    refine tsum_congr fun k => ?_
    rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hexpr, Real.norm_eq_abs, Real.norm_eq_abs]
  have hg2 : Summable (fun k => c * (1 - a) * |s| * a ^ k) := hgeo.mul_left _
  calc |∑' k, a ^ k * 𝔼.E t (g k s - s • g' k) ω|
      ≤ ∑' k, c * (1 - a) * |s| * a ^ k := by
        have hn : |∑' k, a ^ k * 𝔼.E t (g k s - s • g' k) ω|
            ≤ ∑' k, |a ^ k * 𝔼.E t (g k s - s • g' k) ω| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm (f := fun k => a ^ k * 𝔼.E t (g k s - s • g' k) ω)
              (by simpa only [Real.norm_eq_abs] using hsumd.abs)
        refine hn.trans (Summable.tsum_le_tsum (fun k => ?_) hsumd.abs hg2)
        rw [abs_mul, abs_of_nonneg (pow_nonneg ha0 k), mul_comm]
        exact mul_le_mul_of_nonneg_right (𝔼.abs_E_le (hb k) t ω) (pow_nonneg ha0 k)
    _ = c * |s| := by
        have h1a : 1 - a ≠ 0 := by linarith
        rw [tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1]
        field_simp

/-- Woodford (2003), eq. (2.4), p. 179, along a perturbation of the zero-inflation steady state:
the left-hand side of (2.4) at the state `ω`, when the stochastic discount factor is
`Q_{t,t+k} = βᵏ e^{s q̂ₖ}`, the price index is `log P_{t+k} = lP + s P̂ₖ`, the reset price is
`log p*_t = lP + s p̂*`, log output deviates by `s ŷₖ` and the disturbance is `s ẑₖ`. The
marginal profit is `Π₁(p*, p*, P_{t+k}; Y_{t+k}, ξ̃_{t+k}) = mp(log p* − log P_{t+k}, ŷ, ẑ)` with
`mp(x, y, z) = Π₁(eˣ, eˣ, 1; Ȳ eʸ, z)` (`foc_relative_price`). -/
noncomputable def focPath (α β lP : ℝ) (mp : ℝ → ℝ → ℝ → ℝ) (qhat Phat yhat zhat : ℕ → Ω → ℝ)
    (pshat : Ω → ℝ) (t : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  resetFOC 𝔼 α (fun k ω' => β ^ k * Real.exp (s * qhat k ω'))
    (fun k ω' p => mp (Real.log p - (lP + s * Phat k ω')) (s * yhat k ω') (s * zhat k ω')) t
    (Real.exp (lP + s * pshat ω)) ω

/-- Woodford (2003), p. 179: at `s = 0` the path is the zero-inflation steady state, where (2.4)
holds because `Π₁(1, 1, 1; Ȳ, 0) = 0`. -/
theorem focPath_zero {α β lP : ℝ} {mp : ℝ → ℝ → ℝ → ℝ} (h0 : mp 0 0 0 = 0)
    (qhat Phat yhat zhat : ℕ → Ω → ℝ) (pshat : Ω → ℝ) (t : ℕ) (ω : Ω) :
    focPath 𝔼 α β lP mp qhat Phat yhat zhat pshat t 0 ω = 0 := by
  simp [focPath, resetFOC, Real.log_exp, h0, 𝔼.const]

/-- Woodford (2003), eq. (2.6), p. 180 (**the derivative of the first-order condition (2.4) at the
zero-inflation steady state**). With `0 ≤ α < 1`, `0 ≤ β ≤ 1`, `mp` Fréchet differentiable at
`0` with derivative `D` and `mp 0 = 0`, and all perturbation directions bounded, the left-hand
side of (2.4) has derivative `∑ₖ (αβ)ᵏ E_t[ψ_p (p̂* − P̂ₖ) + ψ_y ŷₖ + ψ_z ẑₖ]` at `s = 0`. The
discount-factor direction `q̂` drops out. -/
theorem hasDerivAt_focPath {α β lP : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) {mp : ℝ → ℝ → ℝ → ℝ} {D : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun v : ℝ × ℝ × ℝ => mp v.1 v.2.1 v.2.2) D 0) (h0 : mp 0 0 0 = 0)
    {qhat Phat yhat zhat : ℕ → Ω → ℝ} {pshat : Ω → ℝ} {B : ℝ}
    (hq : ∀ k ω, |qhat k ω| ≤ B) (hP : ∀ k ω, |Phat k ω| ≤ B) (hy : ∀ k ω, |yhat k ω| ≤ B)
    (hz : ∀ k ω, |zhat k ω| ≤ B) (hps : ∀ ω, |pshat ω| ≤ B) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => focPath 𝔼 α β lP mp qhat Phat yhat zhat pshat t s ω)
      (∑' k, (α * β) ^ k * 𝔼.E t (fun ω' => D (1, 0, 0) * (pshat ω - Phat k ω')
        + D (0, 1, 0) * yhat k ω' + D (0, 0, 1) * zhat k ω') ω) 0 := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hps ω)
  set ψp := D (1, 0, 0)
  set ψy := D (0, 1, 0)
  set ψz := D (0, 0, 1)
  set C := |ψp| + |ψy| + |ψz| with hC
  set Bg := C * (2 * B) + B with hBg
  have hC0 : 0 ≤ C := by positivity
  set g : ℕ → ℝ → Ω → ℝ := fun k s ω' => Real.exp (s * qhat k ω') *
    (β ^ k * mp (s * (pshat ω - Phat k ω')) (s * yhat k ω') (s * zhat k ω')) with hg
  set g' : ℕ → Ω → ℝ := fun k ω' => β ^ k * (ψp * (pshat ω - Phat k ω') + ψy * yhat k ω'
    + ψz * zhat k ω') with hg'
  have hxB : ∀ k ω', |pshat ω - Phat k ω'| ≤ 2 * B := fun k ω' =>
    (abs_sub _ _).trans (by linarith [hps ω, hP k ω'])
  have hlin : ∀ k ω', |ψp * (pshat ω - Phat k ω') + ψy * yhat k ω' + ψz * zhat k ω'|
      ≤ C * (2 * B) := by
    intro k ω'
    have h1 : |ψp * (pshat ω - Phat k ω')| ≤ |ψp| * (2 * B) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hxB k ω') (abs_nonneg _)
    have h2 : |ψy * yhat k ω'| ≤ |ψy| * (2 * B) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (by linarith [hy k ω']) (abs_nonneg _)
    have h3 : |ψz * zhat k ω'| ≤ |ψz| * (2 * B) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (by linarith [hz k ω']) (abs_nonneg _)
    have h4 := abs_add_le (ψp * (pshat ω - Phat k ω')) (ψy * yhat k ω')
    calc _ ≤ |ψp * (pshat ω - Phat k ω')| + |ψy * yhat k ω'| + |ψz * zhat k ω'| :=
          (abs_add_le _ _).trans (by linarith)
      _ ≤ C * (2 * B) := by rw [hC]; linarith
  have hβk : ∀ k : ℕ, 0 ≤ β ^ k ∧ β ^ k ≤ 1 := fun k => ⟨pow_nonneg hβ0 k, pow_le_one₀ hβ0 hβ1⟩
  have hg'b : ∀ k ω', |g' k ω'| ≤ Bg := by
    intro k ω'
    simp only [hg', abs_mul, abs_of_nonneg (hβk k).1]
    calc β ^ k * |ψp * (pshat ω - Phat k ω') + ψy * yhat k ω' + ψz * zhat k ω'|
        ≤ 1 * (C * (2 * B)) := mul_le_mul (hβk k).2 (hlin k ω') (abs_nonneg _) zero_le_one
      _ ≤ Bg := by rw [hBg]; linarith
  have hexp : ∀ ε > 0, ∃ δ > 0, ∀ s, |s| < δ → ∀ k ω', |g k s ω' - s * g' k ω'| ≤ ε * |s| := by
    intro ε hε
    have hBg0 : 0 ≤ Bg := by rw [hBg]; positivity
    obtain ⟨ε', hε', δ₁, hδ₁, h1⟩ := exp_mul_expansion hBg0 hε
    obtain ⟨δ₂, hδ₂, h2⟩ := mp_uniform_expansion hD h0 (B := 2 * B) (by linarith) hε'
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs k ω' => ?_⟩
    have hs1 : |s| < δ₁ := lt_of_lt_of_le hs (min_le_left _ _)
    have hs2 : |s| < δ₂ := lt_of_lt_of_le hs (min_le_right _ _)
    have hCB : 0 ≤ C * (2 * B) := by positivity
    have hqk := hq k ω'
    refine h1 s (qhat k ω') (g' k ω') _ hs1 (by rw [hBg]; linarith) (hg'b k ω') ?_
    have hyk := hy k ω'
    have hzk := hz k ω'
    have hm := h2 s (pshat ω - Phat k ω') (yhat k ω') (zhat k ω') hs2 (hxB k ω')
      (by linarith) (by linarith)
    have e : β ^ k * mp (s * (pshat ω - Phat k ω')) (s * yhat k ω') (s * zhat k ω')
        - s * g' k ω' = β ^ k * (mp (s * (pshat ω - Phat k ω')) (s * yhat k ω')
          (s * zhat k ω') - s * (ψp * (pshat ω - Phat k ω') + ψy * yhat k ω'
            + ψz * zhat k ω')) := by
      simp only [hg']; ring
    rw [e, abs_mul, abs_of_nonneg (hβk k).1]
    calc β ^ k * |mp (s * (pshat ω - Phat k ω')) (s * yhat k ω') (s * zhat k ω')
          - s * (ψp * (pshat ω - Phat k ω') + ψy * yhat k ω' + ψz * zhat k ω')|
        ≤ 1 * (ε' * |s|) := mul_le_mul (hβk k).2 hm (abs_nonneg _) zero_le_one
      _ = ε' * |s| := one_mul _
  have hfun : (fun s => focPath 𝔼 α β lP mp qhat Phat yhat zhat pshat t s ω)
      = fun s => ∑' k, α ^ k * 𝔼.E t (g k s) ω := by
    have hk : ∀ k s, (fun ω' => β ^ k * Real.exp (s * qhat k ω') *
        mp (Real.log (Real.exp (lP + s * pshat ω)) - (lP + s * Phat k ω')) (s * yhat k ω')
          (s * zhat k ω')) = g k s := by
      intro k s
      funext ω'
      rw [Real.log_exp, show lP + s * pshat ω - (lP + s * Phat k ω')
        = s * (pshat ω - Phat k ω') by ring]
      simp only [hg]
      ring
    funext s
    simp only [focPath, resetFOC, hk]
  rw [hfun]
  refine (hasDerivAt_tsum_E_of_expansion 𝔼 hα0 hα1 hg'b hexp t ω).congr_deriv ?_
  refine tsum_congr fun k => ?_
  have : g' k = β ^ k • fun ω' => ψp * (pshat ω - Phat k ω') + ψy * yhat k ω'
      + ψz * zhat k ω' := by
    funext ω'; simp [hg']
  rw [this, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

omit 𝔼 in
/-- Woodford (2003), eq. (1.21), p. 154, and p. 157 (the natural rate, linearised exactly): if
the natural rate of output `ŷⁿ(z)` (in logs, relative to `Ȳ`) solves `Π₁(1, 1, 1; Ȳ e^{ŷⁿ(z)}, z)
= 0` for every disturbance `z`, `ŷⁿ(0) = 0` and `ŷⁿ` has derivative `d` at `0`, then
`ψ_y d + ψ_z = 0`; i.e. `ŷⁿ = −(ψ_z/ψ_y) z` to first order. -/
theorem natRate_deriv {mp : ℝ → ℝ → ℝ → ℝ} {D : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun v : ℝ × ℝ × ℝ => mp v.1 v.2.1 v.2.2) D 0) {yn : ℝ → ℝ} {d : ℝ}
    (hyn0 : yn 0 = 0) (hyn : HasDerivAt yn d 0) (himp : ∀ z, mp 0 (yn z) z = 0) :
    D (0, 1, 0) * d + D (0, 0, 1) = 0 := by
  have hγ : HasDerivAt (fun z : ℝ => ((0 : ℝ), yn z, z)) ((0 : ℝ), d, (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hyn.prodMk (hasDerivAt_id (0 : ℝ)))
  have hγ0 : (fun z : ℝ => ((0 : ℝ), yn z, z)) 0 = 0 := by simp [hyn0]
  rw [← hγ0] at hD
  have hc := hD.comp_hasDerivAt (0 : ℝ) hγ
  have hconst : HasDerivAt ((fun v : ℝ × ℝ × ℝ => mp v.1 v.2.1 v.2.2) ∘
      fun z : ℝ => ((0 : ℝ), yn z, z)) 0 0 := by
    have : ((fun v : ℝ × ℝ × ℝ => mp v.1 v.2.1 v.2.2) ∘ fun z : ℝ => ((0 : ℝ), yn z, z))
        = fun _ => 0 := by
      funext z; exact himp z
    rw [this]; exact hasDerivAt_const _ _
  have h := hc.unique hconst
  have hlin : ((0 : ℝ), d, (1 : ℝ)) = d • ((0, 1, 0) : ℝ × ℝ × ℝ) + ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    ext <;> simp
  rw [hlin, map_add, map_smul, smul_eq_mul] at h
  linarith

omit 𝔼 in
/-- Woodford (2003), (1.30), p. 158 and (2.6), p. 180: with `ζ = −ψ_y/ψ_p` and the natural rate
`ŷⁿ = −(ψ_z/ψ_y) z`, the linear marginal profit is `ψ_p x + ψ_y y + ψ_z z = ψ_p (x − ζ(y − ŷⁿ))`. -/
theorem marginal_profit_gap_form {ψp ψy : ℝ} (hp : ψp ≠ 0) (hy : ψy ≠ 0) (ψz x y z : ℝ) :
    ψp * x + ψy * y + ψz * z = ψp * (x - (-ψy / ψp) * (y - (-(ψz / ψy) * z))) := by
  field_simp
  ring

/-- Woodford (2003), eq. (2.6), p. 180 (**(2.6) is the vanishing of the derivative of (2.4)**):
with `ψ_p ≠ 0`, `ψ_y ≠ 0`, `ζ = −ψ_y/ψ_p` and `ŷⁿ = −(ψ_z/ψ_y) ẑ`, the derivative of
`hasDerivAt_focPath` equals `ψ_p ∑ₖ (αβ)ᵏ E_t[(p̂* − P̂ₖ) − ζ(ŷₖ − ŷⁿₖ)]`, so it vanishes iff
`∑ₖ (αβ)ᵏ E_t[log p*_t − log P_{t+k} − ζ(Ŷ_{t+k} − Ŷⁿ_{t+k})] = 0` to first order. -/
theorem focPath_deriv_eq {ψp ψy ψz : ℝ} (hp : ψp ≠ 0) (hy : ψy ≠ 0) (a : ℝ)
    (Phat yhat zhat : ℕ → Ω → ℝ) (pshat : Ω → ℝ) (t : ℕ) (ω : Ω) :
    ∑' k, a ^ k * 𝔼.E t (fun ω' => ψp * (pshat ω - Phat k ω') + ψy * yhat k ω'
        + ψz * zhat k ω') ω
      = ψp * ∑' k, a ^ k * 𝔼.E t (fun ω' => (pshat ω - Phat k ω')
        - (-ψy / ψp) * (yhat k ω' - (-(ψz / ψy) * zhat k ω'))) ω := by
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have : (fun ω' => ψp * (pshat ω - Phat k ω') + ψy * yhat k ω' + ψz * zhat k ω')
      = ψp • fun ω' => (pshat ω - Phat k ω') - (-ψy / ψp) * (yhat k ω' - (-(ψz / ψy)
        * zhat k ω')) := by
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul]
    exact marginal_profit_gap_form hp hy _ _ _ _
  rw [this, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), eq. (2.6), p. 180: since `ψ_p ≠ 0`, the derivative of (2.4) vanishes iff the
log-linear condition (2.6) holds. -/
theorem eq26_iff_deriv_zero {ψp ψy ψz : ℝ} (hp : ψp ≠ 0) (hy : ψy ≠ 0) (a : ℝ)
    (Phat yhat zhat : ℕ → Ω → ℝ) (pshat : Ω → ℝ) (t : ℕ) (ω : Ω) :
    ∑' k, a ^ k * 𝔼.E t (fun ω' => ψp * (pshat ω - Phat k ω') + ψy * yhat k ω'
        + ψz * zhat k ω') ω = 0 ↔
      ∑' k, a ^ k * 𝔼.E t (fun ω' => (pshat ω - Phat k ω')
        - (-ψy / ψp) * (yhat k ω' - (-(ψz / ψy) * zhat k ω'))) ω = 0 := by
  rw [focPath_deriv_eq 𝔼 hp hy, mul_eq_zero]
  exact ⟨fun h => h.resolve_left hp, Or.inr⟩

/-! ### (2.6) ⟺ (2.8) -/

/-- Woodford (2003), eq. (2.8), p. 181: the term `log µ + log S_T + ω̃θ log P_T` inside the
forward sum, with `m = log µ`, `w = ω̃θ`, `s T = log S_T`, and the price index indexed so that
`P (T + 1) = log P_T` (`P t` is the index in force at the start of period `t`, i.e.
`log P_{t−1}`, known at date `t − 1`). -/
def costTerm (m w : ℝ) (s P : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun T ω => m + s T ω + w * P (T + 1) ω

/-- Woodford (2003), eq. (2.8), p. 181 (in levels): the forward sum converges and
`log p*_t = (1 − αβ)/(1 + ω̃θ) ∑_{j ≥ 0} (αβ)ʲ E_t[log µ + log S_{t+j} + ω̃θ log P_{t+j}]`. -/
def Eq28 (α β w m : ℝ) (s P pstar : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Summable (fun j => (α * β) ^ j * 𝔼.E t (costTerm m w s P (t + j)) ω) ∧
    pstar t ω = (1 - α * β) / (1 + w) * ∑' j, (α * β) ^ j * 𝔼.E t (costTerm m w s P (t + j)) ω

/-- Woodford (2003), eq. (2.6), p. 180 (in levels): the forward sum converges and
`∑_{j ≥ 0} (αβ)ʲ E_t[log p*_t − log P_{t+j} − ζ(Ŷ_{t+j} − Ŷⁿ_{t+j})] = 0`, where
`gap T = ζ(Ŷ_T − Ŷⁿ_T)`. -/
def Eq26 (α β : ℝ) (P pstar gap : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Summable (fun j => (α * β) ^ j *
      𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω' - gap (t + j) ω') ω) ∧
    ∑' j, (α * β) ^ j * 𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω' - gap (t + j) ω') ω = 0

/-- Woodford (2003), (2.6) ⟹ (2.8), p. 181 (**and conversely**): when each term `ζ(Ŷ_T − Ŷⁿ_T)`
is replaced by `(1 + ω̃θ)⁻¹ ŝ_T`, `ŝ_T = log µ + log S_T − log P_T` (real marginal cost in
deviation from `log s̄ = −log µ`), and `p*_t` is known at `t`, (2.6) and (2.8) are equivalent
(`0 ≤ αβ < 1`, `1 + ω̃θ ≠ 0`), including the convergence of the sums. -/
theorem eq26_iff_eq28 {α β w m : ℝ} (hab0 : 0 ≤ α * β) (hab1 : α * β < 1) (hw : 1 + w ≠ 0)
    {s P pstar gap : ℕ → Ω → ℝ} (hpa : ∀ t, 𝔼.E t (pstar t) = pstar t)
    (hgap : ∀ T ω, gap T ω = (1 + w)⁻¹ * (m + s T ω - P (T + 1) ω)) :
    Eq26 𝔼 α β P pstar gap ↔ Eq28 𝔼 α β w m s P pstar := by
  set a := α * β
  have hg := summable_geometric_of_lt_one hab0 hab1
  have hpt : ∀ t j ω, 𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω' - gap (t + j) ω') ω
      = pstar t ω - (1 + w)⁻¹ * 𝔼.E t (costTerm m w s P (t + j)) ω := by
    intro t j ω
    have hf : (fun ω' => pstar t ω' - P (t + j + 1) ω' - gap (t + j) ω')
        = pstar t - (1 + w)⁻¹ • costTerm m w s P (t + j) := by
      funext ω'
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, costTerm, hgap]
      field_simp
      ring
    rw [hf, map_sub, map_smul, hpa t]
    rfl
  have hsum_iff : ∀ t ω, Summable (fun j => a ^ j *
      𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω' - gap (t + j) ω') ω) ↔
      Summable (fun j => a ^ j * 𝔼.E t (costTerm m w s P (t + j)) ω) := by
    intro t ω
    simp_rw [hpt, mul_sub]
    constructor
    · intro h
      have h2 := ((hg.mul_right (pstar t ω)).sub h).mul_left (1 + w)
      refine h2.congr fun j => ?_
      field_simp
      ring
    · intro h
      exact (hg.mul_right (pstar t ω)).sub ((h.mul_left (1 + w)⁻¹).congr fun j => by ring)
  have hval : ∀ t ω, Summable (fun j => a ^ j * 𝔼.E t (costTerm m w s P (t + j)) ω) →
      ∑' j, a ^ j * 𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω' - gap (t + j) ω') ω
        = pstar t ω * (1 - a)⁻¹ - (1 + w)⁻¹ * ∑' j, a ^ j * 𝔼.E t (costTerm m w s P (t + j)) ω := by
    intro t ω h
    simp_rw [hpt, mul_sub]
    rw [Summable.tsum_sub (hg.mul_right _) ((h.mul_left (1 + w)⁻¹).congr fun j => by ring),
      tsum_mul_right, tsum_geometric_of_lt_one hab0 hab1, ← tsum_mul_left,
      mul_comm (1 - a)⁻¹]
    congr 1
    exact tsum_congr fun j => by ring
  have h1a : 1 - a ≠ 0 := by linarith
  constructor
  · intro h t ω
    obtain ⟨hs, h0⟩ := h t ω
    have hs' := (hsum_iff t ω).mp hs
    refine ⟨hs', ?_⟩
    rw [hval t ω hs'] at h0
    field_simp at h0 ⊢
    linarith
  · intro h t ω
    obtain ⟨hs, h0⟩ := h t ω
    refine ⟨(hsum_iff t ω).mpr hs, ?_⟩
    rw [hval t ω hs, h0]
    field_simp
    ring

/-! ### Difference-stationary processes and forward sums -/

/-- Woodford (2003), Prop. 3.4, p. 182, and App. B.3, p. 660 (**"difference-stationary", made
precise**): expected `j`-period-ahead changes grow at most linearly, uniformly in the date and
the state, `|E_t x_{t+j} − x_t| ≤ K j`. (Taking `j = 0` makes `x` adapted.) -/
def DiffStationary (x : ℕ → Ω → ℝ) : Prop :=
  ∃ K, ∀ t j ω, |𝔼.E t (x (t + j)) ω - x t ω| ≤ K * j

/-- Woodford (2003), App. B.3, p. 660 (the bound `|E_t log S_{t+j+1} − E_t log S_{t+j}| ≤ K`):
bounded first differences, `|x_{t+1} − x_t| ≤ K`. -/
def BoundedIncr (x : ℕ → Ω → ℝ) : Prop := ∃ K, ∀ t ω, |x (t + 1) ω - x t ω| ≤ K

/-- Woodford (2003), App. B.3: a difference-stationary process is adapted. -/
theorem diffStationary_adapted {x : ℕ → Ω → ℝ} (hx : DiffStationary 𝔼 x) : 𝔼.Adapted x := by
  obtain ⟨K, hK⟩ := hx
  intro t
  funext ω
  have h := hK t 0 ω
  simp only [add_zero, Nat.cast_zero, mul_zero, abs_nonpos_iff, sub_eq_zero] at h
  exact h

/-- Woodford (2003), App. B.3, p. 660: an adapted process with bounded first differences is
difference-stationary (`|E_t x_{t+j} − x_t| ≤ K j`). -/
theorem diffStationary_of_boundedIncr {x : ℕ → Ω → ℝ} (ha : 𝔼.Adapted x)
    (hb : BoundedIncr x) : DiffStationary 𝔼 x := by
  obtain ⟨K, hK⟩ := hb
  refine ⟨K, fun t j => ?_⟩
  induction j with
  | zero => intro ω; simp [ha t]
  | succ j ih =>
    intro ω
    have hd : 𝔼.E t (x (t + (j + 1))) ω - x t ω
        = (𝔼.E t (x (t + j)) ω - x t ω) + 𝔼.E t (x (t + j + 1) - x (t + j)) ω := by
      rw [map_sub, Pi.sub_apply, ← add_assoc]
      ring
    rw [hd]
    have h1 := 𝔼.abs_E_le (x := x (t + j + 1) - x (t + j)) (fun ω' => hK (t + j) ω') t ω
    push_cast
    linarith [abs_add_le (𝔼.E t (x (t + j)) ω - x t ω) (𝔼.E t (x (t + j + 1) - x (t + j)) ω),
      ih ω]

/-- Woodford (2003), App. B.3: the constant in `DiffStationary` can be taken nonnegative. -/
theorem diffStationary_nonneg {x : ℕ → Ω → ℝ} (hx : DiffStationary 𝔼 x) :
    ∃ K, 0 ≤ K ∧ ∀ t j ω, |𝔼.E t (x (t + j)) ω - x t ω| ≤ K * j := by
  obtain ⟨K, hK⟩ := hx
  exact ⟨|K|, abs_nonneg K, fun t j ω => (hK t j ω).trans
    (mul_le_mul_of_nonneg_right (le_abs_self K) (Nat.cast_nonneg j))⟩

/-- Woodford (2003), App. B.3: difference-stationary processes form a vector space (closed under
`c + a x + b y`). -/
theorem diffStationary_linear {x y : ℕ → Ω → ℝ} (hx : DiffStationary 𝔼 x)
    (hy : DiffStationary 𝔼 y) (c a b : ℝ) :
    DiffStationary 𝔼 (fun T ω => c + a * x T ω + b * y T ω) := by
  obtain ⟨Kx, hKx0, hKx⟩ := diffStationary_nonneg 𝔼 hx
  obtain ⟨Ky, hKy0, hKy⟩ := diffStationary_nonneg 𝔼 hy
  refine ⟨|a| * Kx + |b| * Ky, fun t j ω => ?_⟩
  change |𝔼.E t (fun ω => c + a * x (t + j) ω + b * y (t + j) ω) ω
    - (c + a * x t ω + b * y t ω)| ≤ _
  have hf : (fun ω => c + a * x (t + j) ω + b * y (t + j) ω)
      = (fun _ => c) + a • x (t + j) + b • y (t + j) := by
    funext ω; simp [smul_eq_mul]
  rw [hf, map_add, map_add, map_smul, map_smul, 𝔼.const]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e : c + a * 𝔼.E t (x (t + j)) ω + b * 𝔼.E t (y (t + j)) ω - (c + a * x t ω + b * y t ω)
      = a * (𝔼.E t (x (t + j)) ω - x t ω) + b * (𝔼.E t (y (t + j)) ω - y t ω) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h1 := mul_le_mul_of_nonneg_left (hKx t j ω) (abs_nonneg a)
  have h2 := mul_le_mul_of_nonneg_left (hKy t j ω) (abs_nonneg b)
  nlinarith

/-- Woodford (2003), App. B.3: a predetermined difference-stationary process stays
difference-stationary when shifted one period, `T ↦ P_{T+1}` (`P_{T+1}` known at `T`). -/
theorem diffStationary_shift {P : ℕ → Ω → ℝ} (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1))
    (hP : DiffStationary 𝔼 P) : DiffStationary 𝔼 (fun T => P (T + 1)) := by
  obtain ⟨K, hK⟩ := hP
  refine ⟨K, fun t j ω => ?_⟩
  have e : 𝔼.E t (P (t + j + 1)) ω - P (t + 1) ω
      = 𝔼.E t (𝔼.E (t + 1) (P (t + 1 + j)) - P (t + 1)) ω := by
    rw [map_sub, 𝔼.tower (Nat.le_succ t), hpre t, show t + 1 + j = t + j + 1 by omega]
    rfl
  rw [e]
  exact 𝔼.abs_E_le (fun ω' => hK (t + 1) j ω') t ω

/-- Woodford (2003), App. B.3: the forward sum of expected changes,
`∑_{j ≥ 0} aʲ (E_t x_{t+j} − x_t)`. -/
noncomputable def fwdRem (a : ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, a ^ j * (𝔼.E t (x (t + j)) ω - x t ω)

omit 𝔼 in
/-- Woodford (2003), App. B.3: `∑ j aʲ` converges for `0 ≤ a < 1`. -/
theorem summable_nat_mul_geom {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Summable (fun j : ℕ => (j : ℝ) * a ^ j) := by
  have := summable_pow_mul_geometric_of_norm_lt_one 1
    (by rwa [Real.norm_eq_abs, abs_of_nonneg ha0] : ‖a‖ < 1)
  simpa using this

/-- Woodford (2003), App. B.3, p. 660: for difference-stationary `x` the expected changes are
summable with geometric weights, and their sum is bounded uniformly by `K ∑ j aʲ`. -/
theorem summable_fwdRem {a K : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {x : ℕ → Ω → ℝ}
    (hK : ∀ t j ω, |𝔼.E t (x (t + j)) ω - x t ω| ≤ K * j) (t : ℕ) (ω : Ω) :
    Summable (fun j => a ^ j * (𝔼.E t (x (t + j)) ω - x t ω)) := by
  refine Summable.of_norm_bounded ((summable_nat_mul_geom ha0 ha1).mul_left K) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0 j)]
  calc a ^ j * |𝔼.E t (x (t + j)) ω - x t ω| ≤ a ^ j * (K * j) :=
        mul_le_mul_of_nonneg_left (hK t j ω) (pow_nonneg ha0 j)
    _ = K * (j * a ^ j) := by ring

/-- Woodford (2003), App. B.3, p. 660: `|∑ aʲ (E_t x_{t+j} − x_t)| ≤ K ∑ j aʲ`. -/
theorem abs_fwdRem_le {a K : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {x : ℕ → Ω → ℝ}
    (hK : ∀ t j ω, |𝔼.E t (x (t + j)) ω - x t ω| ≤ K * j) (t : ℕ) (ω : Ω) :
    |fwdRem 𝔼 a x t ω| ≤ K * ∑' j : ℕ, (j : ℝ) * a ^ j := by
  have hs := summable_fwdRem 𝔼 ha0 ha1 hK t ω
  have hg := (summable_nat_mul_geom ha0 ha1).mul_left K
  have hn : |fwdRem 𝔼 a x t ω| ≤ ∑' j, |a ^ j * (𝔼.E t (x (t + j)) ω - x t ω)| := by
    simpa [Real.norm_eq_abs, fwdRem] using
      norm_tsum_le_tsum_norm (f := fun j => a ^ j * (𝔼.E t (x (t + j)) ω - x t ω))
        (by simpa only [Real.norm_eq_abs] using hs.abs)
  refine hn.trans ?_
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun j => ?_) hs.abs hg
  rw [abs_mul, abs_of_nonneg (pow_nonneg ha0 j)]
  calc a ^ j * |𝔼.E t (x (t + j)) ω - x t ω| ≤ a ^ j * (K * j) :=
        mul_le_mul_of_nonneg_left (hK t j ω) (pow_nonneg ha0 j)
    _ = K * (j * a ^ j) := by ring

/-- Woodford (2003), App. B.3, p. 660: the forward sum converges for difference-stationary `x`
(the book's "the infinite sum in the definition of `z̄_t` is well defined and finite"). -/
theorem summable_fwd {a K : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {x : ℕ → Ω → ℝ}
    (hK : ∀ t j ω, |𝔼.E t (x (t + j)) ω - x t ω| ≤ K * j) (t : ℕ) (ω : Ω) :
    Summable (fun j => a ^ j * 𝔼.E t (x (t + j)) ω) :=
  (((summable_geometric_of_lt_one ha0 ha1).mul_right (x t ω)).add
    (summable_fwdRem 𝔼 ha0 ha1 hK t ω)).congr fun j => by ring

/-- Woodford (2003), App. B.3, p. 660 (the decomposition behind (B.15)): the forward sum is
`x_t/(1 − a)` plus a uniformly bounded term, `∑ aʲ E_t x_{t+j} = x_t/(1 − a) + ∑ aʲ (E_t x_{t+j} −
x_t)`. -/
theorem fwd_decomp {a K : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {x : ℕ → Ω → ℝ}
    (hK : ∀ t j ω, |𝔼.E t (x (t + j)) ω - x t ω| ≤ K * j) (t : ℕ) (ω : Ω) :
    𝔼.forwardSeries a x t ω = (1 - a)⁻¹ * x t ω + fwdRem 𝔼 a x t ω := by
  have hg := summable_geometric_of_lt_one ha0 ha1
  have hr := summable_fwdRem 𝔼 ha0 ha1 hK t ω
  simp only [ExpectationSystem.forwardSeries, fwdRem]
  rw [← tsum_geometric_of_lt_one ha0 ha1, ← tsum_mul_right, ← (hg.mul_right _).tsum_add hr]
  exact tsum_congr fun j => by ring

/-- Woodford (2003), App. B.3, p. 659 (the tower property behind "if (2.8) is expected to hold in
period `t + 1`"): `E_t[∑ aʲ E_{t+1} x_{t+1+j}] = ∑ aʲ E_t x_{t+1+j}` for difference-stationary
`x` — `E_t` passes through the forward sum although `x` itself is unbounded. -/
theorem E_fwd_succ {a K : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {x : ℕ → Ω → ℝ}
    (hK : ∀ t j ω, |𝔼.E t (x (t + j)) ω - x t ω| ≤ K * j) (t : ℕ) (ω : Ω) :
    𝔼.E t (𝔼.forwardSeries a x (t + 1)) ω = ∑' j, a ^ j * 𝔼.E t (x (t + 1 + j)) ω := by
  have hg := summable_geometric_of_lt_one ha0 ha1
  have hu := (summable_nat_mul_geom ha0 ha1).mul_left K
  have hfd : 𝔼.forwardSeries a x (t + 1) = (1 - a)⁻¹ • x (t + 1) + fun ω' => ∑' j,
      a ^ j * (𝔼.E (t + 1) (x (t + 1 + j)) ω' - x (t + 1) ω') := by
    funext ω'
    rw [fwd_decomp 𝔼 ha0 ha1 hK]
    rfl
  have hdom : ∀ j ω', |a ^ j * (𝔼.E (t + 1) (x (t + 1 + j)) ω' - x (t + 1) ω')|
      ≤ K * ((j : ℝ) * a ^ j) := by
    intro j ω'
    rw [abs_mul, abs_of_nonneg (pow_nonneg ha0 j)]
    calc a ^ j * |𝔼.E (t + 1) (x (t + 1 + j)) ω' - x (t + 1) ω'| ≤ a ^ j * (K * j) :=
          mul_le_mul_of_nonneg_left (hK (t + 1) j ω') (pow_nonneg ha0 j)
      _ = K * (j * a ^ j) := by ring
  rw [hfd, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    ForwardSolution.E_tsum_dom 𝔼 hu hdom t ω]
  have hE : ∀ j, 𝔼.E t (fun ω' => a ^ j * (𝔼.E (t + 1) (x (t + 1 + j)) ω' - x (t + 1) ω')) ω
      = a ^ j * (𝔼.E t (x (t + 1 + j)) ω - 𝔼.E t (x (t + 1)) ω) := by
    intro j
    have : (fun ω' => a ^ j * (𝔼.E (t + 1) (x (t + 1 + j)) ω' - x (t + 1) ω'))
        = a ^ j • (𝔼.E (t + 1) (x (t + 1 + j)) - x (t + 1)) := rfl
    rw [this, map_smul, map_sub, 𝔼.tower (Nat.le_succ t)]
    rfl
  simp_rw [hE]
  have hs2 : Summable (fun j => a ^ j * (𝔼.E t (x (t + 1 + j)) ω - 𝔼.E t (x (t + 1)) ω)) := by
    refine Summable.of_norm_bounded hu (fun j => ?_)
    rw [Real.norm_eq_abs, ← hE j]
    exact 𝔼.abs_E_le (hdom j) t ω
  rw [← tsum_geometric_of_lt_one ha0 ha1, ← tsum_mul_right, ← (hg.mul_right _).tsum_add hs2]
  exact tsum_congr fun j => by ring

/-- Woodford (2003), App. B.3, p. 659 (**the recursive form of a forward sum**, by the tower
property): for difference-stationary `x` and `0 ≤ a < 1`,
`∑ aʲ E_t x_{t+j} = x_t + a E_t[∑ aʲ E_{t+1} x_{t+1+j}]`. -/
theorem fwd_rec {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {x : ℕ → Ω → ℝ}
    (hx : DiffStationary 𝔼 x) (t : ℕ) :
    𝔼.forwardSeries a x t = x t + a • 𝔼.E t (𝔼.forwardSeries a x (t + 1)) := by
  obtain ⟨K, hK⟩ := hx
  have hxa := diffStationary_adapted 𝔼 ⟨K, hK⟩
  funext ω
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, E_fwd_succ 𝔼 ha0 ha1 hK t ω,
    ExpectationSystem.forwardSeries,
    (summable_fwd 𝔼 ha0 ha1 hK t ω).tsum_eq_zero_add, pow_zero, one_mul, add_zero, hxa t,
    ← tsum_mul_left]
  congr 1
  exact tsum_congr fun j => by rw [pow_succ, show t + (j + 1) = t + 1 + j by omega]; ring

/-- Woodford (2003), App. B.3: the forward sum of a difference-stationary process is adapted. -/
theorem fwd_adapted {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {x : ℕ → Ω → ℝ}
    (hx : DiffStationary 𝔼 x) : 𝔼.Adapted (𝔼.forwardSeries a x) := by
  intro t
  have hxa := diffStationary_adapted 𝔼 hx
  conv_rhs => rw [fwd_rec 𝔼 ha0 ha1 hx t]
  conv_lhs => rw [fwd_rec 𝔼 ha0 ha1 hx t]
  rw [map_add, map_smul, 𝔼.E_E_self, hxa t]

/-- Woodford (2003), (B.15), p. 660 (**the forward sum inherits difference-stationarity**): "while
`{z̄_t}` inherits any unit root in `{log S_t}`, it is also a difference-stationary process". -/
theorem fwd_diffStationary {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {x : ℕ → Ω → ℝ}
    (hx : DiffStationary 𝔼 x) : DiffStationary 𝔼 (𝔼.forwardSeries a x) := by
  obtain ⟨K, hK0, hK⟩ := diffStationary_nonneg 𝔼 hx
  have hfa := fwd_adapted 𝔼 ha0 ha1 hx
  set M := K * ∑' j : ℕ, (j : ℝ) * a ^ j with hM
  have hM0 : 0 ≤ M := mul_nonneg hK0 (tsum_nonneg fun j => mul_nonneg (Nat.cast_nonneg j)
    (pow_nonneg ha0 j))
  have h1a : 0 < 1 - a := by linarith
  refine ⟨(1 - a)⁻¹ * K + 2 * M, fun t j ω => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hfa t]
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hdec : ∀ T, 𝔼.forwardSeries a x T = (1 - a)⁻¹ • x T + fwdRem 𝔼 a x T := fun T => by
    funext ω'; rw [fwd_decomp 𝔼 ha0 ha1 hK]; rfl
  have hE : 𝔼.E t (𝔼.forwardSeries a x (t + j)) ω - 𝔼.forwardSeries a x t ω
      = (1 - a)⁻¹ * (𝔼.E t (x (t + j)) ω - x t ω)
        + (𝔼.E t (fwdRem 𝔼 a x (t + j)) ω - fwdRem 𝔼 a x t ω) := by
    rw [hdec (t + j), hdec t, map_add, map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hE]
  have hR1 : |𝔼.E t (fwdRem 𝔼 a x (t + j)) ω| ≤ M :=
    𝔼.abs_E_le (fun ω' => abs_fwdRem_le 𝔼 ha0 ha1 hK (t + j) ω') t ω
  have hR2 : |fwdRem 𝔼 a x t ω| ≤ M := abs_fwdRem_le 𝔼 ha0 ha1 hK t ω
  have hX : |(1 - a)⁻¹ * (𝔼.E t (x (t + j)) ω - x t ω)| ≤ (1 - a)⁻¹ * K * j := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr h1a), mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK t j ω) (inv_pos.mpr h1a).le
  have hsub := abs_sub (𝔼.E t (fwdRem 𝔼 a x (t + j)) ω) (fwdRem 𝔼 a x t ω)
  have hadd := abs_add_le ((1 - a)⁻¹ * (𝔼.E t (x (t + j)) ω - x t ω))
    (𝔼.E t (fwdRem 𝔼 a x (t + j)) ω - fwdRem 𝔼 a x t ω)
  nlinarith

/-- Woodford (2003), App. B.3, p. 660: if `x` is adapted with bounded first differences then so is
its forward sum (bounded growth of `log S` gives bounded growth of `z̄`). -/
theorem fwd_boundedIncr {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {x : ℕ → Ω → ℝ}
    (ha : 𝔼.Adapted x) (hb : BoundedIncr x) : BoundedIncr (𝔼.forwardSeries a x) := by
  have hx := diffStationary_of_boundedIncr 𝔼 ha hb
  obtain ⟨K, hK0, hK⟩ := diffStationary_nonneg 𝔼 hx
  obtain ⟨Kb, hKb⟩ := hb
  set M := K * ∑' j : ℕ, (j : ℝ) * a ^ j with hM
  have h1a : 0 < 1 - a := by linarith
  refine ⟨(1 - a)⁻¹ * Kb + 2 * M, fun t ω => ?_⟩
  rw [fwd_decomp 𝔼 ha0 ha1 hK, fwd_decomp 𝔼 ha0 ha1 hK]
  have hR1 := abs_fwdRem_le 𝔼 ha0 ha1 hK (t + 1) ω
  have hR2 := abs_fwdRem_le 𝔼 ha0 ha1 hK t ω
  have hX : |(1 - a)⁻¹ * (x (t + 1) ω - x t ω)| ≤ (1 - a)⁻¹ * Kb := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr h1a)]
    exact mul_le_mul_of_nonneg_left (hKb t ω) (inv_pos.mpr h1a).le
  have e : (1 - a)⁻¹ * x (t + 1) ω + fwdRem 𝔼 a x (t + 1) ω
      - ((1 - a)⁻¹ * x t ω + fwdRem 𝔼 a x t ω)
      = (1 - a)⁻¹ * (x (t + 1) ω - x t ω) + (fwdRem 𝔼 a x (t + 1) ω - fwdRem 𝔼 a x t ω) := by
    ring
  rw [e]
  have hsub := abs_sub (fwdRem 𝔼 a x (t + 1) ω) (fwdRem 𝔼 a x t ω)
  have hadd := abs_add_le ((1 - a)⁻¹ * (x (t + 1) ω - x t ω))
    (fwdRem 𝔼 a x (t + 1) ω - fwdRem 𝔼 a x t ω)
  linarith

/-- Woodford (2003), App. B.3, p. 661 (**uniqueness by the growth argument**): if
`d_t = a E_t d_{t+1}` with `|a| < 1` and `d` is difference-stationary, then `d = 0` — the book's
`E_t[z_{t+j} − z̄_{t+j}] = λ₂ʲ (z_t − z̄_t)` would otherwise grow like `λ₂ʲ`. -/
theorem forward_unique_growth {a : ℝ} (ha : |a| < 1) {d : ℕ → Ω → ℝ}
    (hd : ∀ t, d t = a • 𝔼.E t (d (t + 1))) (hg : DiffStationary 𝔼 d) : d = 0 := by
  obtain ⟨K, hK0, hK⟩ := diffStationary_nonneg 𝔼 hg
  funext t ω
  have hle : ∀ j : ℕ, |d t ω| ≤ |a| ^ j * |d t ω| + K * ((j : ℝ) * |a| ^ j) := by
    intro j
    have h := congrFun (𝔼.forward_iterate hd t j) ω
    rw [Pi.smul_apply, smul_eq_mul] at h
    have h1 : |𝔼.E t (d (t + j)) ω| ≤ |d t ω| + K * j := by
      have := hK t j ω
      have := abs_sub_abs_le_abs_sub (𝔼.E t (d (t + j)) ω) (d t ω)
      linarith
    calc |d t ω| = |a| ^ j * |𝔼.E t (d (t + j)) ω| := by rw [h, abs_mul, abs_pow]
      _ ≤ |a| ^ j * (|d t ω| + K * j) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg (abs_nonneg a) j)
      _ = |a| ^ j * |d t ω| + K * ((j : ℝ) * |a| ^ j) := by ring
  have hlim : Tendsto (fun j : ℕ => |a| ^ j * |d t ω| + K * ((j : ℝ) * |a| ^ j)) atTop
      (𝓝 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const |d t ω|
    have h2 := (tendsto_self_mul_const_pow_of_lt_one (abs_nonneg a) ha).const_mul K
    simpa using h1.add h2
  have h0 : |d t ω| ≤ 0 := ge_of_tendsto' hlim hle
  simpa using h0

/-! ### Proposition 3.4 -/

open QuadraticRoots in
omit 𝔼 in
/-- Woodford (2003), App. B.3, p. 659 (**substituting (2.5) into the recursive form of (2.8)
gives (B.13)**): with `ξ` as in (2.11), `p₀ = log P_{t−1}`, `p₁ = log P_t`, `Ep₂ = E_t log P_{t+1}`
and `c₀ = log µ + log S_t`, the recursive pricing condition
`(p₁ − αp₀)/(1 − α) = (1 − αβ)/(1 + ω̃θ) (c₀ + ω̃θ p₁) + αβ (Ep₂ − αp₁)/(1 − α)` holds iff
`β Ep₂ − (1 + β + ξ) p₁ + p₀ = −ξ c₀`, i.e. `E_t[A(L) log P_{t+1}] = −ξ(log µ + log S_t)`. -/
theorem recursive_iff_B13 {α β w : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hw : 1 + w ≠ 0)
    (p0 p1 Ep2 c0 : ℝ) :
    (p1 - α * p0) / (1 - α) = (1 - α * β) / (1 + w) * (c0 + w * p1)
        + α * β * ((Ep2 - α * p1) / (1 - α)) ↔
      β * Ep2 - (1 + β + calvoXi α β w) * p1 + p0 = -(calvoXi α β w * c0) := by
  have h1a : 1 - α ≠ 0 := by linarith
  have key : β * Ep2 - (1 + β + calvoXi α β w) * p1 + p0 + calvoXi α β w * c0
      = -((1 - α) / α) * ((p1 - α * p0) / (1 - α) - ((1 - α * β) / (1 + w) * (c0 + w * p1)
        + α * β * ((Ep2 - α * p1) / (1 - α)))) := by
    unfold calvoXi
    field_simp
    ring
  have hc : -((1 - α) / α) ≠ 0 := neg_ne_zero.mpr (div_ne_zero h1a hα0.ne')
  constructor
  · intro h
    have : β * Ep2 - (1 + β + calvoXi α β w) * p1 + p0 + calvoXi α β w * c0 = 0 := by
      rw [key, h, sub_self, mul_zero]
    linarith
  · intro h
    have h0 : -((1 - α) / α) * ((p1 - α * p0) / (1 - α) - ((1 - α * β) / (1 + w) * (c0 + w * p1)
        + α * β * ((Ep2 - α * p1) / (1 - α)))) = 0 := by
      rw [← key]; linarith
    have := (mul_eq_zero.mp h0).resolve_left hc
    linarith

open QuadraticRoots in
omit 𝔼 in
/-- Woodford (2003), App. B.3, p. 660 (**(B.13) ⟺ (B.14)**, by the factorisation
`A(L) = β(1 − λ₁L)(1 − λ₂L)`): `β Ep₂ − (1 + β + c) p₁ + p₀ = −c c₀` iff
`z = λ₂⁻¹ Ez' + (1 − λ₁)(1 − λ₂⁻¹) c₀` with `z = p₁ − λ₁ p₀`, `Ez' = Ep₂ − λ₁ p₁`. -/
theorem B13_iff_B14 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (p0 p1 Ep2 c0 : ℝ) :
    β * Ep2 - (1 + β + c) * p1 + p0 = -(c * c0) ↔
      p1 - lam1 β c * p0 = (lam2 β c)⁻¹ * (Ep2 - lam1 β c * p1)
        + (1 - lam1 β c) * (1 - (lam2 β c)⁻¹) * c0 := by
  rw [one_sub_mul_one_sub_inv hβ hc, inv_lam2 hβ hc]
  have hs := lam1_add_lam2 (c := c) hβ
  have hp := lam1_mul_lam2 hβ hc
  have hs' : β * (lam1 β c + lam2 β c) = 1 + β + c := by rw [hs]; field_simp
  have hp' : β * (lam1 β c * lam2 β c) = 1 := by rw [hp]; field_simp
  have hl2 : 0 < β * lam2 β c := mul_pos hβ (lt_trans one_pos (one_lt_lam2 hβ hc))
  have key : β * Ep2 - (1 + β + c) * p1 + p0 + c * c0
      = -(β * lam2 β c) * (p1 - lam1 β c * p0 - (β * lam1 β c * (Ep2 - lam1 β c * p1)
        + c * lam1 β c * c0)) := by
    linear_combination (-(β * Ep2) - p0 - c * c0 + β * lam1 β c * p1) * hp' + p1 * hs'
  constructor
  · intro h
    have h0 : -(β * lam2 β c) * (p1 - lam1 β c * p0 - (β * lam1 β c * (Ep2 - lam1 β c * p1)
        + c * lam1 β c * c0)) = 0 := by rw [← key]; linarith
    have := (mul_eq_zero.mp h0).resolve_left (neg_ne_zero.mpr hl2.ne')
    linarith
  · intro h
    have : β * Ep2 - (1 + β + c) * p1 + p0 + c * c0 = 0 := by
      rw [key, h, sub_self, mul_zero]
    linarith

/-- Woodford (2003), eq. (2.5), p. 180 (in levels, with `P (t + 1) = log P_t`, `P t = log P_{t−1}`):
`log P_t = α log P_{t−1} + (1 − α) log p*_t` at every date. -/
def Eq25 (α : ℝ) (P pstar : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, P (t + 1) ω = α * P t ω + (1 - α) * pstar t ω

/-- Woodford (2003), (2.9), p. 182: the forcing term `log µ + log S_T`. -/
def mcost (m : ℝ) (s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun T ω => m + s T ω

open QuadraticRoots in
/-- Woodford (2003), App. B.3, p. 660: the forward solution of (B.14),
`z̄_t = (1 − λ₁)(1 − λ₂⁻¹) ∑_{j ≥ 0} λ₂⁻ʲ [log µ + E_t log S_{t+j}]` (`= β⁻¹λ₂⁻¹ξ ∑ …`). -/
noncomputable def zbar (α β w m : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (1 - lam1 β (calvoXi α β w)) * (1 - (lam2 β (calvoXi α β w))⁻¹) *
    𝔼.forwardSeries (lam2 β (calvoXi α β w))⁻¹ (mcost m s) t ω

open QuadraticRoots in
/-- Woodford (2003), eq. (2.9), p. 182 (**the solution of Proposition 3.4**), from the initial
price level `P0 = log P_{−1}`: `log P_t = λ₁ log P_{t−1} + z̄_t`. -/
noncomputable def Psol (α β w m : ℝ) (s : ℕ → Ω → ℝ) (P0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => P0
  | t + 1 => fun ω => lam1 β (calvoXi α β w) * Psol α β w m s P0 t ω + zbar 𝔼 α β w m s t ω

/-- Woodford (2003), eq. (2.5), p. 180: the reset price implied by the solution (2.9),
`log p*_t = (log P_t − α log P_{t−1})/(1 − α)`. -/
noncomputable def pstarSol (α β w m : ℝ) (s : ℕ → Ω → ℝ) (P0 : Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (Psol 𝔼 α β w m s P0 (t + 1) ω - α * Psol 𝔼 α β w m s P0 t ω) / (1 - α)

/-- Woodford (2003), App. B.3: `log µ + log S_t` is difference-stationary when `log S_t` is. -/
theorem mcost_diffStationary {m : ℝ} {s : ℕ → Ω → ℝ} (hs : DiffStationary 𝔼 s) :
    DiffStationary 𝔼 (mcost m s) := by
  have h := diffStationary_linear 𝔼 hs hs m 1 0
  change DiffStationary 𝔼 (fun T ω => m + s T ω)
  simpa using h

open QuadraticRoots in
omit 𝔼 in
/-- Woodford (2003), Prop. 3.4, p. 182 (the root facts used throughout B.3): for `0 < α < 1`,
`0 < β < 1`, `1 + ω̃θ > 0`: `ξ > 0`, `0 < λ₁ < 1`, `0 < λ₂⁻¹ < 1`. -/
theorem calvo_roots {α β w : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hw : 0 < 1 + w) :
    0 < calvoXi α β w ∧ 0 < lam1 β (calvoXi α β w) ∧ lam1 β (calvoXi α β w) < 1 ∧
      0 < (lam2 β (calvoXi α β w))⁻¹ ∧ (lam2 β (calvoXi α β w))⁻¹ < 1 := by
  have hξ := calvoXi_pos hα0 hα1 hβ1 hw
  exact ⟨hξ, lam1_pos hβ0 hξ, lam1_lt_one hβ0 hξ, (inv_lam2_lt_one hβ0 hξ).1,
    (inv_lam2_lt_one hβ0 hξ).2⟩

open QuadraticRoots in
/-- Woodford (2003), (B.14), p. 660: `z̄` solves `z̄_t = λ₂⁻¹ E_t z̄_{t+1} + β⁻¹λ₂⁻¹ξ(log µ + log
S_t)` (written with `β⁻¹λ₂⁻¹ξ = (1 − λ₁)(1 − λ₂⁻¹)`). -/
theorem zbar_rec {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ} (hs : DiffStationary 𝔼 s) (t : ℕ) :
    zbar 𝔼 α β w m s t = (lam2 β (calvoXi α β w))⁻¹ • 𝔼.E t (zbar 𝔼 α β w m s (t + 1))
      + ((1 - lam1 β (calvoXi α β w)) * (1 - (lam2 β (calvoXi α β w))⁻¹)) • mcost m s t := by
  obtain ⟨-, -, -, ha0, ha1⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  have hfr := fwd_rec 𝔼 ha0.le ha1 (mcost_diffStationary 𝔼 (m := m) hs) t
  set κ := (1 - lam1 β (calvoXi α β w)) * (1 - (lam2 β (calvoXi α β w))⁻¹)
  have hz : ∀ T, zbar 𝔼 α β w m s T =
      κ • 𝔼.forwardSeries (lam2 β (calvoXi α β w))⁻¹ (mcost m s) T :=
    fun T => rfl
  rw [hz, hz, hfr, map_smul]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

open QuadraticRoots in
/-- Woodford (2003), (B.15), p. 660: `z̄` is adapted, difference-stationary, and inherits
bounded first differences from `log S`. -/
theorem zbar_props {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s) (hsb : BoundedIncr s) :
    𝔼.Adapted (zbar 𝔼 α β w m s) ∧ DiffStationary 𝔼 (zbar 𝔼 α β w m s) ∧
      BoundedIncr (zbar 𝔼 α β w m s) := by
  obtain ⟨-, -, -, ha0, ha1⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  have hs := diffStationary_of_boundedIncr 𝔼 hsa hsb
  have hm := mcost_diffStationary 𝔼 (m := m) hs
  set a := (lam2 β (calvoXi α β w))⁻¹
  set κ := (1 - lam1 β (calvoXi α β w)) * (1 - (lam2 β (calvoXi α β w))⁻¹)
  have hz : zbar 𝔼 α β w m s = fun T ω => κ * 𝔼.forwardSeries a (mcost m s) T ω := rfl
  have hma : 𝔼.Adapted (mcost m s) := diffStationary_adapted 𝔼 hm
  have hmb : BoundedIncr (mcost m s) := by
    obtain ⟨K, hK⟩ := hsb
    exact ⟨K, fun t ω => by simpa [mcost] using hK t ω⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t
    change 𝔼.E t (fun ω => κ * 𝔼.forwardSeries a (mcost m s) t ω) =
      fun ω => κ * 𝔼.forwardSeries a (mcost m s) t ω
    have : (fun ω => κ * 𝔼.forwardSeries a (mcost m s) t ω) =
        κ • 𝔼.forwardSeries a (mcost m s) t := rfl
    rw [this, map_smul, fwd_adapted 𝔼 ha0.le ha1 hm t]
  · have h := diffStationary_linear 𝔼 (fwd_diffStationary 𝔼 ha0.le ha1 hm)
      (fwd_diffStationary 𝔼 ha0.le ha1 hm) 0 κ 0
    rw [hz]
    simpa using h
  · obtain ⟨K, hK⟩ := fwd_boundedIncr 𝔼 ha0.le ha1 hma hmb
    refine ⟨|κ| * K, fun t ω => ?_⟩
    rw [hz]
    simp only
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (hK t ω) (abs_nonneg κ)

open QuadraticRoots in
/-- Woodford (2003), eq. (2.9), p. 182, written out: the solution satisfies
`log P_t = λ₁ log P_{t−1} + (1 − λ₁)(1 − λ₂⁻¹) ∑_{j ≥ 0} λ₂⁻ʲ [log µ + E_t log S_{t+j}]`. -/
theorem psol_eq29 (α β w m : ℝ) (s : ℕ → Ω → ℝ) (P0 : Ω → ℝ) (t : ℕ) (ω : Ω) :
    Psol 𝔼 α β w m s P0 (t + 1) ω = lam1 β (calvoXi α β w) * Psol 𝔼 α β w m s P0 t ω
      + (1 - lam1 β (calvoXi α β w)) * (1 - (lam2 β (calvoXi α β w))⁻¹) *
        ∑' j, ((lam2 β (calvoXi α β w))⁻¹) ^ j * (m + 𝔼.E t (s (t + j)) ω) := by
  simp only [Psol, zbar, ExpectationSystem.forwardSeries]
  congr 2
  refine tsum_congr fun j => ?_
  have : mcost m s (t + j) = (fun _ => m) + s (t + j) := rfl
  rw [this, map_add, 𝔼.const]
  rfl

open QuadraticRoots in
/-- Woodford (2003), Prop. 3.4: the solution's price index is predetermined — `log P_{t−1}` and
`log P_t` are known at date `t` — given an initial `log P_{−1}` known at date `0`. -/
theorem psol_known {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s) (hsb : BoundedIncr s) {P0 : Ω → ℝ}
    (hP0 : 𝔼.E 0 P0 = P0) (t : ℕ) :
    𝔼.E t (Psol 𝔼 α β w m s P0 t) = Psol 𝔼 α β w m s P0 t ∧
      𝔼.E t (Psol 𝔼 α β w m s P0 (t + 1)) = Psol 𝔼 α β w m s P0 (t + 1) := by
  have hza := (zbar_props 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hsa hsb).1
  have hstep : ∀ t, 𝔼.E t (Psol 𝔼 α β w m s P0 t) = Psol 𝔼 α β w m s P0 t →
      𝔼.E t (Psol 𝔼 α β w m s P0 (t + 1)) = Psol 𝔼 α β w m s P0 (t + 1) := by
    intro t ht
    have : Psol 𝔼 α β w m s P0 (t + 1)
        = lam1 β (calvoXi α β w) • Psol 𝔼 α β w m s P0 t + zbar 𝔼 α β w m s t := rfl
    rw [this, map_add, map_smul, ht, hza t]
  induction t with
  | zero => exact ⟨hP0, hstep 0 hP0⟩
  | succ t ih =>
    have h1 : 𝔼.E (t + 1) (Psol 𝔼 α β w m s P0 (t + 1)) = Psol 𝔼 α β w m s P0 (t + 1) :=
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih.2
    exact ⟨h1, hstep (t + 1) h1⟩

open QuadraticRoots in
/-- Woodford (2003), Prop. 3.4 ("inflation is a stationary process"; App. B.3, p. 661): if the
initial gap `log P_{−1} − log S_0` is bounded, the solution (2.9) has bounded inflation
`log P_t − log P_{t−1}`. -/
theorem psol_boundedIncr {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s) (hsb : BoundedIncr s) {P0 : Ω → ℝ}
    (hinit : ∃ B, ∀ ω, |P0 ω - s 0 ω| ≤ B) : BoundedIncr (Psol 𝔼 α β w m s P0) := by
  obtain ⟨hξ, hl0, hl1, ha0, ha1⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  obtain ⟨-, -, hzb⟩ := zbar_props 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hsa hsb
  obtain ⟨Kz, hKz⟩ := hzb
  obtain ⟨B, hB⟩ := hinit
  have hs := diffStationary_of_boundedIncr 𝔼 hsa hsb
  obtain ⟨K, hK0, hK⟩ := diffStationary_nonneg 𝔼 (mcost_diffStationary 𝔼 (m := m) hs)
  set l1 := lam1 β (calvoXi α β w)
  set a := (lam2 β (calvoXi α β w))⁻¹
  set κ := (1 - l1) * (1 - a)
  set M := K * ∑' j : ℕ, (j : ℝ) * a ^ j
  have hκ : 0 < κ := mul_pos (by linarith) (by linarith)
  set u : ℕ → Ω → ℝ := fun t ω => Psol 𝔼 α β w m s P0 (t + 1) ω - Psol 𝔼 α β w m s P0 t ω
  have hu_succ : ∀ t ω, u (t + 1) ω = l1 * u t ω
      + (zbar 𝔼 α β w m s (t + 1) ω - zbar 𝔼 α β w m s t ω) := by
    intro t ω
    simp only [u, Psol]
    ring
  have hu0 : ∀ ω, |u 0 ω| ≤ (1 - l1) * (|m| + |B|) + κ * M := by
    intro ω
    have hz0 : zbar 𝔼 α β w m s 0 ω = (1 - l1) * (m + s 0 ω) + κ * fwdRem 𝔼 a (mcost m s) 0 ω := by
      have h1a : 1 - a ≠ 0 := by linarith
      have hzd : zbar 𝔼 α β w m s 0 ω = κ * 𝔼.forwardSeries a (mcost m s) 0 ω := rfl
      have hmc : mcost m s 0 ω = m + s 0 ω := rfl
      rw [hzd, fwd_decomp 𝔼 ha0.le ha1 hK, hmc]
      have : κ * (1 - a)⁻¹ = 1 - l1 := by simp only [κ]; field_simp
      linear_combination (m + s 0 ω) * this
    have e : u 0 ω = (1 - l1) * (m + (s 0 ω - P0 ω)) + κ * fwdRem 𝔼 a (mcost m s) 0 ω := by
      simp only [u, Psol]
      rw [hz0]
      ring
    rw [e]
    have hR := abs_fwdRem_le 𝔼 ha0.le ha1 hK 0 ω
    have h1 : |(1 - l1) * (m + (s 0 ω - P0 ω))| ≤ (1 - l1) * (|m| + |B|) := by
      rw [abs_mul, abs_of_pos (by linarith : 0 < 1 - l1)]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_sub_comm]
      exact (hB ω).trans (le_abs_self B)
    have h2 : |κ * fwdRem 𝔼 a (mcost m s) 0 ω| ≤ κ * M := by
      rw [abs_mul, abs_of_pos hκ]
      exact mul_le_mul_of_nonneg_left hR hκ.le
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  set B0 := (1 - l1) * (|m| + |B|) + κ * M
  have hM0 : 0 ≤ M := mul_nonneg hK0 (tsum_nonneg fun j => mul_nonneg (Nat.cast_nonneg j)
    (pow_nonneg ha0.le j))
  have hB0 : 0 ≤ B0 := by
    have : 0 ≤ (1 - l1) * (|m| + |B|) := mul_nonneg (by linarith) (by positivity)
    positivity
  have hKz0 : 0 ≤ |Kz| / (1 - l1) := div_nonneg (abs_nonneg _) (by linarith)
  refine ⟨B0 + |Kz| / (1 - l1), fun t => ?_⟩
  induction t with
  | zero =>
    intro ω
    have h := hu0 ω
    simp only [u] at h
    linarith
  | succ t ih =>
    intro ω
    have h := hu_succ t ω
    simp only [u] at h
    rw [h]
    have hz := (hKz t ω).trans (le_abs_self Kz)
    have hih := ih ω
    have e1 : |l1 * (Psol 𝔼 α β w m s P0 (t + 1) ω - Psol 𝔼 α β w m s P0 t ω)|
        ≤ l1 * (B0 + |Kz| / (1 - l1)) := by
      rw [abs_mul, abs_of_pos hl0]
      exact mul_le_mul_of_nonneg_left hih hl0.le
    have e2 : l1 * (B0 + |Kz| / (1 - l1)) + |Kz| ≤ B0 + |Kz| / (1 - l1) := by
      have h1l : 0 < 1 - l1 := by linarith
      have : |Kz| / (1 - l1) * (1 - l1) = |Kz| := by field_simp
      nlinarith [abs_nonneg Kz]
    calc _ ≤ |l1 * (Psol 𝔼 α β w m s P0 (t + 1) ω - Psol 𝔼 α β w m s P0 t ω)|
          + |zbar 𝔼 α β w m s (t + 1) ω - zbar 𝔼 α β w m s t ω| := abs_add_le _ _
      _ ≤ B0 + |Kz| / (1 - l1) := by linarith

omit 𝔼 in
/-- Woodford (2003), eq. (2.5), p. 180: (2.5) determines the reset price,
`log p*_t = (log P_t − α log P_{t−1})/(1 − α)`. -/
theorem pstar_of_eq25 {α : ℝ} (hα1 : α < 1) {P pstar : ℕ → Ω → ℝ} (h25 : Eq25 α P pstar)
    (t : ℕ) : pstar t = fun ω => (P (t + 1) ω - α * P t ω) / (1 - α) := by
  funext ω
  have h1a : 1 - α ≠ 0 := by linarith
  rw [h25 t ω]
  field_simp
  ring

/-- Woodford (2003), App. B.3, p. 659: `E_t log p*_{t+1} = (E_t log P_{t+1} − α log P_t)/(1 − α)`
when `log P_t` is known at `t`. -/
theorem E_pstar_succ {α : ℝ} (hα1 : α < 1) {P pstar : ℕ → Ω → ℝ} (h25 : Eq25 α P pstar)
    (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (t : ℕ) (ω : Ω) :
    𝔼.E t (pstar (t + 1)) ω = (𝔼.E t (P (t + 2)) ω - α * P (t + 1) ω) / (1 - α) := by
  have hf : pstar (t + 1) = (1 - α)⁻¹ • (P (t + 1 + 1) - α • P (t + 1)) := by
    rw [pstar_of_eq25 hα1 h25 (t + 1)]
    funext ω'
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hf, map_smul, map_sub, map_smul, hpre t]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Woodford (2003), App. B.3, p. 659: `log µ + log S_T + ω̃θ log P_T` is difference-stationary
when `log S` and the (predetermined) price index are. -/
theorem costTerm_diffStationary {m w : ℝ} {s P : ℕ → Ω → ℝ} (hs : DiffStationary 𝔼 s)
    (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (hP : DiffStationary 𝔼 P) :
    DiffStationary 𝔼 (costTerm m w s P) := by
  have h := diffStationary_linear 𝔼 hs (diffStationary_shift 𝔼 hpre hP) m 1 w
  change DiffStationary 𝔼 (fun T ω => m + s T ω + w * P (T + 1) ω)
  simpa using h

/-- Woodford (2003), App. B.3, p. 659 (**the recursive form of (2.8), with the sign corrected**,
survey error E4): if (2.8) holds at `t` and `t + 1` and the price index is difference-stationary,
then `log p*_t = (1 − αβ)/(1 + ω̃θ)[log µ + log S_t + ω̃θ log P_t] + αβ E_t log p*_{t+1}`. -/
theorem recursive_reset_price {α β w m : ℝ} (hab0 : 0 ≤ α * β) (hab1 : α * β < 1)
    {s P pstar : ℕ → Ω → ℝ} (hs : DiffStationary 𝔼 s) (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1))
    (hP : DiffStationary 𝔼 P) (h28 : Eq28 𝔼 α β w m s P pstar) (t : ℕ) :
    pstar t = ((1 - α * β) / (1 + w)) • costTerm m w s P t + (α * β) • 𝔼.E t (pstar (t + 1)) := by
  have hc := costTerm_diffStationary 𝔼 (m := m) (w := w) hs hpre hP
  have hp : ∀ T, pstar T =
      ((1 - α * β) / (1 + w)) • 𝔼.forwardSeries (α * β) (costTerm m w s P) T := by
    intro T
    funext ω
    rw [(h28 T ω).2]
    rfl
  rw [hp t, hp (t + 1), fwd_rec 𝔼 hab0 hab1 hc t, map_smul, smul_add, smul_comm]

open QuadraticRoots in
/-- Woodford (2003), (B.13), p. 659: every solution of (2.5) and (2.8) in the
difference-stationary class satisfies `E_t[A(L) log P_{t+1}] = −ξ(log µ + log S_t)`, i.e.
`β E_t log P_{t+1} − (1 + β + ξ) log P_t + log P_{t−1} = −ξ(log µ + log S_t)`. -/
theorem solution_B13 {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hw : 0 < 1 + w) {s P pstar : ℕ → Ω → ℝ} (hs : DiffStationary 𝔼 s)
    (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (hP : DiffStationary 𝔼 P)
    (h25 : Eq25 α P pstar) (h28 : Eq28 𝔼 α β w m s P pstar) (t : ℕ) (ω : Ω) :
    β * 𝔼.E t (P (t + 2)) ω - (1 + β + calvoXi α β w) * P (t + 1) ω + P t ω
      = -(calvoXi α β w * (m + s t ω)) := by
  have hab0 : 0 ≤ α * β := (mul_pos hα0 hβ0).le
  have hab1 : α * β < 1 := by nlinarith
  have hr := congrFun (recursive_reset_price 𝔼 hab0 hab1 hs hpre hP h28 t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, costTerm] at hr
  rw [E_pstar_succ 𝔼 hα1 h25 hpre t ω, congrFun (pstar_of_eq25 hα1 h25 t) ω] at hr
  exact (recursive_iff_B13 hα0 hα1 hw.ne' _ _ _ _).mp hr

open QuadraticRoots in
/-- Woodford (2003), (B.14), p. 660: every solution in the class satisfies
`z_t = λ₂⁻¹ E_t z_{t+1} + β⁻¹λ₂⁻¹ξ(log µ + log S_t)` with `z_t = log P_t − λ₁ log P_{t−1}`. -/
theorem solution_B14 {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hw : 0 < 1 + w) {s P pstar : ℕ → Ω → ℝ} (hs : DiffStationary 𝔼 s)
    (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (hP : DiffStationary 𝔼 P)
    (h25 : Eq25 α P pstar) (h28 : Eq28 𝔼 α β w m s P pstar) (t : ℕ) (ω : Ω) :
    P (t + 1) ω - lam1 β (calvoXi α β w) * P t ω
      = (lam2 β (calvoXi α β w))⁻¹ * (𝔼.E t (P (t + 2)) ω - lam1 β (calvoXi α β w) * P (t + 1) ω)
        + (1 - lam1 β (calvoXi α β w)) * (1 - (lam2 β (calvoXi α β w))⁻¹) * (m + s t ω) :=
  (B13_iff_B14 hβ0 (calvoXi_pos hα0 hα1 hβ1 hw) _ _ _ _).mp
    (solution_B13 𝔼 hα0 hα1 hβ0 hβ1 hw hs hpre hP h25 h28 t ω)

open QuadraticRoots in
/-- Woodford (2003), Prop. 3.4, p. 182, and App. B.3, p. 661 (**uniqueness**): every solution
`(log P, log p*)` of (2.5) and (2.8) with initial price level `log P_{−1} = P0`, whose price index
is predetermined and difference-stationary (`E_t log P_{t+j} − log P_t = O(j)`), is the solution
(2.9). Here `log S` is adapted with bounded first differences. -/
theorem prop34_unique {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s) (hsb : BoundedIncr s) {P0 : Ω → ℝ}
    {P pstar : ℕ → Ω → ℝ} (hP0 : P 0 = P0) (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1))
    (hP : DiffStationary 𝔼 P) (h25 : Eq25 α P pstar) (h28 : Eq28 𝔼 α β w m s P pstar) :
    P = Psol 𝔼 α β w m s P0 ∧ pstar = pstarSol 𝔼 α β w m s P0 := by
  obtain ⟨-, -, -, ha0, ha1⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  have hs := diffStationary_of_boundedIncr 𝔼 hsa hsb
  obtain ⟨-, hzs, -⟩ := zbar_props 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hsa hsb
  have hB14 := solution_B14 𝔼 hα0 hα1 hβ0 hβ1 hw hs hpre hP h25 h28
  have hZ := fun t => congrFun (zbar_rec 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hs t)
  set l1 := lam1 β (calvoXi α β w)
  set a := (lam2 β (calvoXi α β w))⁻¹
  set z := zbar 𝔼 α β w m s
  set d : ℕ → Ω → ℝ := fun t ω => P (t + 1) ω - l1 * P t ω - z t ω with hd_def
  have hd : ∀ t, d t = a • 𝔼.E t (d (t + 1)) := by
    intro t
    have hf : d (t + 1) = P (t + 1 + 1) - l1 • P (t + 1) - z (t + 1) := by
      funext ω; simp [hd_def, smul_eq_mul]
    funext ω
    rw [hf, map_sub, map_sub, map_smul, hpre t]
    have hb := hB14 t ω
    have hz := hZ t ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mcost] at hz ⊢
    simp only [hd_def]
    linear_combination hb - hz
  have hdS : DiffStationary 𝔼 d := by
    have h1 := diffStationary_linear 𝔼 (diffStationary_shift 𝔼 hpre hP) hP 0 1 (-l1)
    have h2 := diffStationary_linear 𝔼 h1 hzs 0 1 (-1)
    have e : d = fun T ω => 0 + 1 * (0 + 1 * P (T + 1) ω + -l1 * P T ω) + -1 * z T ω := by
      funext T ω; simp only [hd_def]; ring
    rw [e]; exact h2
  have hd0 := forward_unique_growth 𝔼 (by rw [abs_of_pos ha0]; exact ha1) hd hdS
  have hPeq : ∀ t, P t = Psol 𝔼 α β w m s P0 t := by
    intro t
    induction t with
    | zero => exact hP0
    | succ t ih =>
      funext ω
      have := congrFun (congrFun hd0 t) ω
      simp only [hd_def, Pi.zero_apply] at this
      change P (t + 1) ω = l1 * Psol 𝔼 α β w m s P0 t ω + z t ω
      rw [← ih]
      linarith
  have hPf : P = Psol 𝔼 α β w m s P0 := funext hPeq
  refine ⟨hPf, ?_⟩
  funext t
  rw [pstar_of_eq25 hα1 h25 t, hPf]
  rfl

/-- Woodford (2003), eq. (2.5): the solution (2.9) and its reset price satisfy (2.5). -/
theorem psol_eq25 {α : ℝ} (hα1 : α < 1) (β w m : ℝ) (s : ℕ → Ω → ℝ) (P0 : Ω → ℝ) :
    Eq25 α (Psol 𝔼 α β w m s P0) (pstarSol 𝔼 α β w m s P0) := by
  intro t ω
  have h1a : 1 - α ≠ 0 := by linarith
  simp only [pstarSol]
  field_simp
  ring

open QuadraticRoots in
/-- Woodford (2003), Prop. 3.4, App. B.3, pp. 660–661 (**existence**): the solution (2.9) and its
reset price satisfy (2.8) — the forward sum converges and equals `log p*_t`. -/
theorem psol_eq28 {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s) (hsb : BoundedIncr s) {P0 : Ω → ℝ}
    (hP0 : 𝔼.E 0 P0 = P0) (hinit : ∃ B, ∀ ω, |P0 ω - s 0 ω| ≤ B) :
    Eq28 𝔼 α β w m s (Psol 𝔼 α β w m s P0) (pstarSol 𝔼 α β w m s P0) := by
  have hab0 : 0 ≤ α * β := (mul_pos hα0 hβ0).le
  have hab1 : α * β < 1 := by nlinarith
  have hs := diffStationary_of_boundedIncr 𝔼 hsa hsb
  have hknown := psol_known 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hsa hsb hP0
  have hpre : ∀ t, 𝔼.E t (Psol 𝔼 α β w m s P0 (t + 1)) = Psol 𝔼 α β w m s P0 (t + 1) :=
    fun t => (hknown t).2
  have hPa : 𝔼.Adapted (Psol 𝔼 α β w m s P0) := fun t => (hknown t).1
  have hPS : DiffStationary 𝔼 (Psol 𝔼 α β w m s P0) :=
    diffStationary_of_boundedIncr 𝔼 hPa (psol_boundedIncr 𝔼 hα0 hα1 hβ0 hβ1 hw hsa hsb hinit)
  have h25 := psol_eq25 𝔼 hα1 β w m s P0
  have hZ := fun t => congrFun (zbar_rec 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hs t)
  have hEp := E_pstar_succ 𝔼 hα1 h25 hpre
  have hps := fun t => congrFun (pstar_of_eq25 hα1 h25 t)
  obtain ⟨K, hK⟩ := costTerm_diffStationary 𝔼 (m := m) (w := w) hs hpre hPS
  have hFr := fun t => congrFun (fwd_rec 𝔼 hab0 hab1 ⟨K, hK⟩ t)
  have hFS := fwd_diffStationary 𝔼 hab0 hab1 ⟨K, hK⟩
  set P := Psol 𝔼 α β w m s P0 with hPdef
  set pstar := pstarSol 𝔼 α β w m s P0 with hpsdef
  set z := zbar 𝔼 α β w m s
  set l1 := lam1 β (calvoXi α β w)
  -- the recursive form of (2.8) holds for the solution
  have hrec : ∀ t ω, pstar t ω = (1 - α * β) / (1 + w) * costTerm m w s P t ω
      + α * β * 𝔼.E t (pstar (t + 1)) ω := by
    intro t ω
    rw [hEp t ω, hps t ω]
    simp only [costTerm]
    refine (recursive_iff_B13 hα0 hα1 hw.ne' _ _ _ _).mpr ?_
    refine (B13_iff_B14 hβ0 (calvoXi_pos hα0 hα1 hβ1 hw) _ _ _ _).mpr ?_
    have hP1 : P (t + 1) = l1 • P t + z t := rfl
    have hP2 : P (t + 2) = l1 • P (t + 1) + z (t + 1) := rfl
    have hz := hZ t ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mcost] at hz
    rw [hP2, map_add, map_smul, hpre t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hP1]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hz
  set F := 𝔼.forwardSeries (α * β) (costTerm m w s P)
  set c := (1 - α * β) / (1 + w)
  set d : ℕ → Ω → ℝ := fun t ω => pstar t ω - c * F t ω with hd_def
  have hd : ∀ t, d t = (α * β) • 𝔼.E t (d (t + 1)) := by
    intro t
    have hf : d (t + 1) = pstar (t + 1) - c • F (t + 1) := by
      funext ω; simp [hd_def, smul_eq_mul]
    funext ω
    rw [hf, map_sub, map_smul]
    simp only [hd_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have hF := hFr t ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hF
    rw [hrec t ω, hF]
    ring
  have hdS : DiffStationary 𝔼 d := by
    have h1 := diffStationary_linear 𝔼 (diffStationary_shift 𝔼 hpre hPS) hPS 0 (1 - α)⁻¹
      (-(α * (1 - α)⁻¹))
    have h2 := diffStationary_linear 𝔼 h1 hFS 0 1 (-c)
    have e : d = fun T ω => 0 + 1 * (0 + (1 - α)⁻¹ * P (T + 1) ω + -(α * (1 - α)⁻¹) * P T ω)
        + -c * F T ω := by
      funext T ω
      simp only [hd_def, hpsdef, pstarSol]
      ring
    rw [e]; exact h2
  have hd0 := forward_unique_growth 𝔼 (by rw [abs_of_nonneg hab0]; exact hab1) hd hdS
  intro t ω
  refine ⟨summable_fwd 𝔼 hab0 hab1 hK t ω, ?_⟩
  have := congrFun (congrFun hd0 t) ω
  simp only [hd_def, Pi.zero_apply] at this
  have hF : F t ω = ∑' j, (α * β) ^ j * 𝔼.E t (costTerm m w s P (t + j)) ω := rfl
  rw [← hF]
  linarith

open QuadraticRoots in
/-- Woodford (2003), **Proposition 3.4** (p. 182; App. B.3, pp. 659–661). Let `0 < α < 1`,
`0 < β < 1`, `1 + ω̃θ > 0`, let `log S` be adapted with bounded first differences
(difference-stationary marginal cost), and let the initial price level `log P_{−1} = P0` be known at
date `0` with `log P_{−1} − log S_0` bounded. Then (2.9) defines a solution of (2.5) and (2.8) whose
price index is predetermined with bounded inflation (in particular difference-stationary), and it
is the only solution whose price index is predetermined and difference-stationary. -/
theorem prop34 {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s) (hsb : BoundedIncr s) {P0 : Ω → ℝ}
    (hP0 : 𝔼.E 0 P0 = P0) (hinit : ∃ B, ∀ ω, |P0 ω - s 0 ω| ≤ B) :
    (Psol 𝔼 α β w m s P0 0 = P0 ∧
      (∀ t, 𝔼.E t (Psol 𝔼 α β w m s P0 (t + 1)) = Psol 𝔼 α β w m s P0 (t + 1)) ∧
      Eq25 α (Psol 𝔼 α β w m s P0) (pstarSol 𝔼 α β w m s P0) ∧
      Eq28 𝔼 α β w m s (Psol 𝔼 α β w m s P0) (pstarSol 𝔼 α β w m s P0) ∧
      BoundedIncr (Psol 𝔼 α β w m s P0) ∧ DiffStationary 𝔼 (Psol 𝔼 α β w m s P0)) ∧
    ∀ P pstar : ℕ → Ω → ℝ, P 0 = P0 → (∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) →
      DiffStationary 𝔼 P → Eq25 α P pstar → Eq28 𝔼 α β w m s P pstar →
      P = Psol 𝔼 α β w m s P0 ∧ pstar = pstarSol 𝔼 α β w m s P0 := by
  have hknown := psol_known 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hsa hsb hP0
  have hbi := psol_boundedIncr 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hsa hsb hinit
  refine ⟨⟨rfl, fun t => (hknown t).2, psol_eq25 𝔼 hα1 β w m s P0,
    psol_eq28 𝔼 hα0 hα1 hβ0 hβ1 hw hsa hsb hP0 hinit, hbi,
    diffStationary_of_boundedIncr 𝔼 (fun t => (hknown t).1) hbi⟩, ?_⟩
  intro P pstar hP0' hpre hP h25 h28
  exact prop34_unique 𝔼 hα0 hα1 hβ0 hβ1 hw hsa hsb hP0' hpre hP h25 h28

open QuadraticRoots in
/-- Woodford (2003), Prop. 3.4 (**the initial condition is necessary**): if the solution (2.9)
is difference-stationary, then the initial gap `log P_{−1} − log S_0` is bounded across states. -/
theorem prop34_init_necessary {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s) (hsb : BoundedIncr s)
    {P0 : Ω → ℝ} (hP0 : 𝔼.E 0 P0 = P0) (hDS : DiffStationary 𝔼 (Psol 𝔼 α β w m s P0)) :
    ∃ B, ∀ ω, |P0 ω - s 0 ω| ≤ B := by
  obtain ⟨hξ, hl0, hl1, ha0, ha1⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  have hs := diffStationary_of_boundedIncr 𝔼 hsa hsb
  obtain ⟨K, hK0, hK⟩ := diffStationary_nonneg 𝔼 (mcost_diffStationary 𝔼 (m := m) hs)
  obtain ⟨KP, hKP0, hKP⟩ := diffStationary_nonneg 𝔼 hDS
  have hknown := psol_known 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hsa hsb hP0 0
  set l1 := lam1 β (calvoXi α β w)
  set a := (lam2 β (calvoXi α β w))⁻¹
  set κ := (1 - l1) * (1 - a)
  set M := K * ∑' j : ℕ, (j : ℝ) * a ^ j
  have hκ : 0 < κ := mul_pos (by linarith) (by linarith)
  have h1l : 0 < 1 - l1 := by linarith
  refine ⟨(KP + κ * M) / (1 - l1) + |m|, fun ω => ?_⟩
  have hu := hKP 0 1 ω
  simp only [zero_add, Nat.cast_one, mul_one] at hu
  rw [hknown.2] at hu
  have hzd : zbar 𝔼 α β w m s 0 ω = κ * 𝔼.forwardSeries a (mcost m s) 0 ω := rfl
  have hmc : mcost m s 0 ω = m + s 0 ω := rfl
  have he : Psol 𝔼 α β w m s P0 1 ω - Psol 𝔼 α β w m s P0 0 ω
      = (1 - l1) * (m + s 0 ω - P0 ω) + κ * fwdRem 𝔼 a (mcost m s) 0 ω := by
    have h1 : Psol 𝔼 α β w m s P0 1 ω = l1 * P0 ω + zbar 𝔼 α β w m s 0 ω := rfl
    have h0 : Psol 𝔼 α β w m s P0 0 ω = P0 ω := rfl
    rw [h1, h0, hzd, fwd_decomp 𝔼 ha0.le ha1 hK, hmc]
    have h1a : 1 - a ≠ 0 := by linarith
    have : κ * (1 - a)⁻¹ = 1 - l1 := by simp only [κ]; field_simp
    linear_combination (m + s 0 ω) * this
  rw [he] at hu
  have hR := abs_fwdRem_le 𝔼 ha0.le ha1 hK 0 ω
  have hR' : |κ * fwdRem 𝔼 a (mcost m s) 0 ω| ≤ κ * M := by
    rw [abs_mul, abs_of_pos hκ]; exact mul_le_mul_of_nonneg_left hR hκ.le
  have h2 : (1 - l1) * |m + s 0 ω - P0 ω| ≤ KP + κ * M := by
    set X := (1 - l1) * (m + s 0 ω - P0 ω)
    set Y := κ * fwdRem 𝔼 a (mcost m s) 0 ω
    have hX : |X| ≤ |X + Y| + |Y| := by
      have := abs_sub (X + Y) Y
      rwa [add_sub_cancel_right] at this
    have hXe : |X| = (1 - l1) * |m + s 0 ω - P0 ω| := by
      simp only [X]; rw [abs_mul, abs_of_pos h1l]
    linarith
  have h3 : |m + s 0 ω - P0 ω| ≤ (KP + κ * M) / (1 - l1) := by
    rw [le_div_iff₀ h1l]; linarith
  have h4 : |P0 ω - s 0 ω| ≤ |m + s 0 ω - P0 ω| + |m| := by
    have := abs_sub (m + s 0 ω - P0 ω) m
    have e : P0 ω - s 0 ω = -(m + s 0 ω - P0 ω - m) := by ring
    rw [e, abs_neg]
    linarith [abs_sub (m + s 0 ω - P0 ω) m]
  linarith

open QuadraticRoots in
/-- Woodford (2003), **Proposition 3.4, existence and uniqueness in the class** (pp. 182, 659–661):
under the hypotheses of `prop34` except the initial-gap bound, a solution of (2.5) and (2.8) with
predetermined, difference-stationary price index exists iff `log P_{−1} − log S_0` is bounded;
it is then unique and equal to (2.9). (Under perfect foresight the gap bound is automatic.) -/
theorem prop34_exists_iff {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s) (hsb : BoundedIncr s) {P0 : Ω → ℝ}
    (hP0 : 𝔼.E 0 P0 = P0) :
    (∃ P pstar : ℕ → Ω → ℝ, P 0 = P0 ∧ (∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) ∧
      DiffStationary 𝔼 P ∧ Eq25 α P pstar ∧ Eq28 𝔼 α β w m s P pstar) ↔
      ∃ B, ∀ ω, |P0 ω - s 0 ω| ≤ B := by
  constructor
  · rintro ⟨P, pstar, h0, hpre, hP, h25, h28⟩
    have := (prop34_unique 𝔼 hα0 hα1 hβ0 hβ1 hw hsa hsb h0 hpre hP h25 h28).1
    rw [this] at hP
    exact prop34_init_necessary 𝔼 hα0 hα1 hβ0 hβ1 hw hsa hsb hP0 hP
  · intro hinit
    obtain ⟨⟨h0, hpre, h25, h28, -, hDS⟩, -⟩ :=
      prop34 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hsa hsb hP0 hinit
    exact ⟨_, _, h0, hpre, hDS, h25, h28⟩

/-! ### Survey error E4: the sign of `ω̃θ log P_t` in the recursive form -/

/-- Woodford (2003), App. B.3, p. 659, survey error E4 (**the printed recursive form is false**):
under perfect foresight with `α = β = 1/2`, `ω̃θ = 1`, `log µ = 0`, `log S ≡ 0`, `log P ≡ 1`, the
reset price `log p* ≡ 1/2` satisfies (2.8) at every date, and the corrected recursive form
`log p*_t = (1 − αβ)/(1 + ω̃θ)[log µ + log S_t + ω̃θ log P_t] + αβ log p*_{t+1}` holds, but the
printed form with `− ω̃θ log P_t` fails (`1/2 ≠ −1/4`). -/
theorem printed_E4_fails :
    Eq28 perfectForesight (1 / 2) (1 / 2) 1 0 (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => 1 / 2) ∧
      (1 / 2 : ℝ) = (1 - 1 / 2 * (1 / 2)) / (1 + 1) * (0 + 0 + 1 * 1) + 1 / 2 * (1 / 2) * (1 / 2)
      ∧ (1 / 2 : ℝ) ≠ (1 - 1 / 2 * (1 / 2)) / (1 + 1) * (0 + 0 - 1 * 1)
        + 1 / 2 * (1 / 2) * (1 / 2) := by
  refine ⟨fun t ω => ?_, by norm_num, by norm_num⟩
  have hg : Summable (fun j : ℕ => ((1 : ℝ) / 2 * (1 / 2)) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hE : ∀ j, perfectForesight.E t (costTerm 0 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (1 : ℝ))
      (t + j)) ω = 1 := by
    intro j
    simp [perfectForesight, costTerm]
  simp only [hE, mul_one]
  refine ⟨hg, ?_⟩
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-! ### Solutions outside the class -/

/-- Woodford (2003), App. B.3, p. 661: the deterministic solution `λ₂ᵗ − λ₁ᵗ` of the
homogeneous equation `A(L) x_{t+1} = 0` with `x_0 = 0` (in our indexing, `x_0 = log P_{−1}`). -/
noncomputable def hpath (β c : ℝ) (t : ℕ) : ℝ :=
  QuadraticRoots.lam2 β c ^ t - QuadraticRoots.lam1 β c ^ t

open QuadraticRoots in
omit 𝔼 in
/-- Woodford (2003), App. B.3 (the `P(α)` identity at a root): every root `λ` of (2.10) with
`ξ` of (2.11) satisfies `(λ − α)(1 − αβλ) = (1 − α)(1 − αβ) ω̃θ λ/(1 + ω̃θ)`. -/
theorem root_calvo_identity {α β w : ℝ} (hα0 : 0 < α) (hw : 1 + w ≠ 0) {l : ℝ}
    (hl : charPoly β (calvoXi α β w) l = 0) :
    (l - α) * (1 - α * β * l) = (1 - α) * (1 - α * β) * w * l / (1 + w) := by
  unfold charPoly calvoXi at hl
  have hα : α ≠ 0 := hα0.ne'
  field_simp at hl ⊢
  linear_combination (-1 : ℝ) * hl

open QuadraticRoots in
omit 𝔼 in
/-- Woodford (2003), App. B.3: at a root `λ` of (2.10) with `αβλ ≠ 1`,
`(λ^{t+1} − αλᵗ)/(1 − α) = (1 − αβ)/(1 + ω̃θ) · ω̃θ λ^{t+1}/(1 − αβλ)`: the reset price implied by
(2.5) along `λᵗ` equals the (2.8) forward sum along it. -/
theorem root_reset_identity {α β w : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hw : 1 + w ≠ 0) {l : ℝ}
    (hl : charPoly β (calvoXi α β w) l = 0) (hne : 1 - α * β * l ≠ 0) (t : ℕ) :
    (l ^ (t + 1) - α * l ^ t) / (1 - α)
      = (1 - α * β) / (1 + w) * (w * (l ^ (t + 1) * (1 - α * β * l)⁻¹)) := by
  have h := root_calvo_identity hα0 hw hl
  have h1a : 1 - α ≠ 0 := by linarith
  have h' : (1 - α) * (1 - α * β) * w * l = (l - α) * (1 - α * β * l) * (1 + w) := by
    rw [h]; field_simp
  rw [div_eq_iff h1a, eq_comm]
  calc (1 - α * β) / (1 + w) * (w * (l ^ (t + 1) * (1 - α * β * l)⁻¹)) * (1 - α)
      = l ^ t * ((1 - α) * (1 - α * β) * w * l) / ((1 + w) * (1 - α * β * l)) := by
        field_simp; ring
    _ = l ^ t * ((l - α) * (1 - α * β * l) * (1 + w)) / ((1 + w) * (1 - α * β * l)) := by
        rw [h']
    _ = l ^ (t + 1) - α * l ^ t := by
        rw [div_eq_iff (mul_ne_zero hw hne)]; ring

omit 𝔼 in
/-- Woodford (2003), App. B.3: `∑_{j ≥ 0} qʲ λ^{t+j+1} = λ^{t+1}/(1 − qλ)` for `0 ≤ qλ < 1`. -/
theorem hasSum_root_path {q l : ℝ} (h0 : 0 ≤ q * l) (h1 : q * l < 1) (t : ℕ) :
    HasSum (fun j : ℕ => q ^ j * l ^ (t + j + 1)) (l ^ (t + 1) * (1 - q * l)⁻¹) := by
  have := (hasSum_geometric_of_lt_one h0 h1).mul_left (l ^ (t + 1))
  refine this.congr_fun fun j => ?_
  rw [mul_pow, show t + j + 1 = (t + 1) + j by omega, pow_add]
  ring

omit 𝔼 in
/-- Woodford (2003), App. B.3, p. 661 ("`E_t z_{t+j}` must grow asymptotically at the rate
`λ₂ʲ`"): for `r > 1` and `d > 0`, `d(rʲ − 1)` eventually exceeds any linear function `Cj`. -/
theorem exists_lin_lt_pow {r : ℝ} (hr : 1 < r) (C : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ j : ℕ, C * j < d * (r ^ j - 1) := by
  set δ := r - 1 with hδ
  have hδ0 : 0 < δ := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (2 * |C| / (d * δ ^ 2)))
  have hn1 : (1 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hn2 : 2 * |C| / (d * δ ^ 2) < n := lt_of_le_of_lt (le_max_right _ _) hn
  refine ⟨2 * n, ?_⟩
  have hb : 1 + (n : ℝ) * δ ≤ r ^ n := by
    have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ δ) n
    rwa [hδ, add_sub_cancel] at this
  have hsq : (1 + (n : ℝ) * δ) ^ 2 ≤ r ^ (2 * n) := by
    rw [pow_mul', sq, sq]
    exact mul_le_mul hb hb (by positivity) (by positivity)
  have hdd : 0 < d * δ ^ 2 := by positivity
  have hC : 2 * |C| < n * (d * δ ^ 2) := by rwa [div_lt_iff₀ hdd] at hn2
  push_cast
  have h1 : C * (2 * n) ≤ 2 * |C| * n := by nlinarith [le_abs_self C, (by linarith : (0 : ℝ) < n)]
  have h2 : 2 * |C| * n < n * (d * δ ^ 2) * n := by nlinarith
  have h3 : d * (n * δ) ^ 2 ≤ d * (r ^ (2 * n) - 1) := by
    refine mul_le_mul_of_nonneg_left ?_ hd.le
    nlinarith [hsq]
  nlinarith

open QuadraticRoots in
/-- Woodford (2003), App. B.3, p. 661: the perturbed price path `log P_t + c(λ₂^{t+1} − λ₁^{t+1})`
(in our indexing `P t + c hₜ`, `h = hpath`), a solution of (2.5) and (2.8) outside the
difference-stationary class when `c ≠ 0` and `ω̃θ > 0`. -/
noncomputable def Pcont (α β w m : ℝ) (s : ℕ → Ω → ℝ) (P0 : Ω → ℝ) (c : ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ω => Psol 𝔼 α β w m s P0 t ω + c * hpath β (calvoXi α β w) t

open QuadraticRoots in
/-- Woodford (2003), eq. (2.5): the reset price implied by `Pcont` through (2.5). -/
noncomputable def pstarCont (α β w m : ℝ) (s : ℕ → Ω → ℝ) (P0 : Ω → ℝ) (c : ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ω => pstarSol 𝔼 α β w m s P0 t ω + c * ((hpath β (calvoXi α β w) (t + 1)
    - α * hpath β (calvoXi α β w) t) / (1 - α))

open QuadraticRoots in
/-- Woodford (2003), Prop. 3.4 (**a continuum of solutions outside the class**): when
`ω̃θ > 0` (so `α < λ₁` and `αβλ₂ < 1`), for every `c ∈ ℝ` the path `Pcont c` with reset price
`pstarCont c` has the same initial price level, is predetermined, and satisfies (2.5) and (2.8)
(with convergent forward sums). -/
theorem prop34_continuum {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hwpos : 0 < w) {s : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s) (hsb : BoundedIncr s) {P0 : Ω → ℝ}
    (hP0 : 𝔼.E 0 P0 = P0) (hinit : ∃ B, ∀ ω, |P0 ω - s 0 ω| ≤ B) (c : ℝ) :
    Pcont 𝔼 α β w m s P0 c 0 = P0 ∧
      (∀ t, 𝔼.E t (Pcont 𝔼 α β w m s P0 c (t + 1)) = Pcont 𝔼 α β w m s P0 c (t + 1)) ∧
      Eq25 α (Pcont 𝔼 α β w m s P0 c) (pstarCont 𝔼 α β w m s P0 c) ∧
      Eq28 𝔼 α β w m s (Pcont 𝔼 α β w m s P0 c) (pstarCont 𝔼 α β w m s P0 c) := by
  have hw : 0 < 1 + w := by linarith
  obtain ⟨hξ, hl0, hl1, -, -⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  obtain ⟨⟨-, hpre, h25, h28, -, -⟩, -⟩ := prop34 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hsa hsb hP0 hinit
  set ξ := calvoXi α β w
  set l1 := lam1 β ξ
  set l2 := lam2 β ξ
  have hl2 : 1 < l2 := one_lt_lam2 hβ0 hξ
  have hαl1 : α < l1 := (alpha_lt_lam1_calvo_iff hα0 hα1 hβ0 hβ1 hw).mpr hwpos
  have hq2 : α * β * l2 < 1 := by
    rw [alpha_beta_lam2 hβ0 hξ, div_lt_one hl0]; exact hαl1
  have hq1 : α * β * l1 < 1 := by
    have : α * β < 1 := by nlinarith
    nlinarith
  have hq20 : 0 ≤ α * β * l2 := by positivity
  have hq10 : 0 ≤ α * β * l1 := by positivity
  have hroot1 := charPoly_lam1 hβ0 hξ
  have hroot2 := charPoly_lam2 hβ0 hξ
  have h1a : 1 - α ≠ 0 := by linarith
  refine ⟨?_, fun t => ?_, fun t ω => ?_, fun t ω => ?_⟩
  · funext ω; simp [Pcont, hpath, Psol]
  · have hf : Pcont 𝔼 α β w m s P0 c (t + 1)
        = Psol 𝔼 α β w m s P0 (t + 1) + fun _ => c * hpath β ξ (t + 1) := rfl
    rw [hf, map_add, hpre t, 𝔼.const]
  · simp only [Pcont, pstarCont]
    rw [h25 t ω]
    field_simp
    ring
  · -- the forward sum splits into the solution's sum and a deterministic geometric sum
    obtain ⟨hs0, hv0⟩ := h28 t ω
    have hE : ∀ j, 𝔼.E t (costTerm m w s (Pcont 𝔼 α β w m s P0 c) (t + j)) ω
        = 𝔼.E t (costTerm m w s (Psol 𝔼 α β w m s P0) (t + j)) ω
          + w * c * hpath β ξ (t + j + 1) := by
      intro j
      have hf : costTerm m w s (Pcont 𝔼 α β w m s P0 c) (t + j)
          = costTerm m w s (Psol 𝔼 α β w m s P0) (t + j)
            + fun _ => w * c * hpath β ξ (t + j + 1) := by
        funext ω'
        simp only [costTerm, Pcont, Pi.add_apply]
        ring
      rw [hf, map_add, 𝔼.const]
      rfl
    have hs2 := hasSum_root_path hq20 hq2 t
    have hs1 := hasSum_root_path hq10 hq1 t
    have hH : HasSum (fun j : ℕ => (α * β) ^ j * hpath β ξ (t + j + 1))
        (l2 ^ (t + 1) * (1 - α * β * l2)⁻¹ - l1 ^ (t + 1) * (1 - α * β * l1)⁻¹) := by
      refine (hs2.sub hs1).congr_fun fun j => ?_
      simp only [hpath]
      ring
    have hsum : Summable (fun j => (α * β) ^ j *
        𝔼.E t (costTerm m w s (Pcont 𝔼 α β w m s P0 c) (t + j)) ω) := by
      refine (hs0.add (hH.summable.mul_left (w * c))).congr fun j => ?_
      rw [hE j]; ring
    refine ⟨hsum, ?_⟩
    have htsum : ∑' j, (α * β) ^ j * 𝔼.E t (costTerm m w s (Pcont 𝔼 α β w m s P0 c) (t + j)) ω
        = ∑' j, (α * β) ^ j * 𝔼.E t (costTerm m w s (Psol 𝔼 α β w m s P0) (t + j)) ω
          + w * c * (l2 ^ (t + 1) * (1 - α * β * l2)⁻¹ - l1 ^ (t + 1) * (1 - α * β * l1)⁻¹) := by
      rw [← (hH.mul_left (w * c)).tsum_eq, ← hs0.tsum_add (hH.mul_left (w * c)).summable]
      exact tsum_congr fun j => by rw [hE j]; ring
    rw [htsum]
    simp only [pstarCont]
    rw [hv0]
    have k2 := root_reset_identity hα0 hα1 hw.ne' hroot2 (by linarith) t
    have k1 := root_reset_identity hα0 hα1 hw.ne' hroot1 (by linarith) t
    have hk : (hpath β ξ (t + 1) - α * hpath β ξ t) / (1 - α)
        = (l2 ^ (t + 1) - α * l2 ^ t) / (1 - α) - (l1 ^ (t + 1) - α * l1 ^ t) / (1 - α) := by
      simp only [hpath]
      field_simp
      ring
    rw [hk, k2, k1]
    ring

open QuadraticRoots in
/-- Woodford (2003), Prop. 3.4 (**the continuum is genuine**): distinct `c` give distinct price
paths (`λ₂ ≠ λ₁`). -/
theorem prop34_continuum_injective [Nonempty Ω] {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hw : 0 < 1 + w) (s : ℕ → Ω → ℝ) (P0 : Ω → ℝ) {c₁ c₂ : ℝ}
    (h : Pcont 𝔼 α β w m s P0 c₁ = Pcont 𝔼 α β w m s P0 c₂) : c₁ = c₂ := by
  obtain ⟨hξ, -, -, -, -⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  have h1 := congrFun (congrFun h 1) (Classical.arbitrary Ω)
  simp only [Pcont, hpath, pow_one, add_right_inj] at h1
  have hne : lam2 β (calvoXi α β w) - lam1 β (calvoXi α β w) ≠ 0 :=
    sub_ne_zero.mpr (lam1_lt_lam2 hβ0 hξ).ne'
  exact mul_right_cancel₀ hne h1

open QuadraticRoots in
/-- Woodford (2003), Prop. 3.4 and App. B.3, p. 661 (**the extra solutions are not
difference-stationary**): for `c ≠ 0`, `E_0 log P_{j−1} − log P_{−1}` grows like `λ₂ʲ`, so
`Pcont c` lies outside the class. -/
theorem perturbation_not_diffStationary [Nonempty Ω] {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s)
    (hsb : BoundedIncr s) {P0 : Ω → ℝ} (hP0 : 𝔼.E 0 P0 = P0)
    (hinit : ∃ B, ∀ ω, |P0 ω - s 0 ω| ≤ B) {c : ℝ} (hc : c ≠ 0) :
    ¬ DiffStationary 𝔼 (Pcont 𝔼 α β w m s P0 c) := by
  obtain ⟨hξ, hl0, hl1, -, -⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  obtain ⟨⟨-, -, -, -, -, hDS⟩, -⟩ := prop34 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hsa hsb hP0 hinit
  obtain ⟨K₂, hK₂0, hK₂⟩ := diffStationary_nonneg 𝔼 hDS
  rintro hc'
  obtain ⟨K₁, hK₁0, hK₁⟩ := diffStationary_nonneg 𝔼 hc'
  set ξ := calvoXi α β w
  have hl2 : 1 < lam2 β ξ := one_lt_lam2 hβ0 hξ
  obtain ⟨j, hj⟩ := exists_lin_lt_pow hl2 (K₁ + K₂) (abs_pos.mpr hc)
  set ω := Classical.arbitrary Ω
  have h1 := hK₁ 0 j ω
  have h2 := hK₂ 0 j ω
  have hf : Pcont 𝔼 α β w m s P0 c (0 + j) = Psol 𝔼 α β w m s P0 (0 + j)
      + fun _ => c * hpath β ξ (0 + j) := rfl
  rw [hf, map_add, 𝔼.const] at h1
  simp only [Pi.add_apply, Pcont, hpath, pow_zero, sub_self, mul_zero, add_zero, zero_add] at h1 h2
  have hpow : lam1 β ξ ^ j ≤ 1 := pow_le_one₀ hl0.le hl1.le
  have hgrow : |c| * (lam2 β ξ ^ j - 1) ≤ |c * (lam2 β ξ ^ j - lam1 β ξ ^ j)| := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    have : 0 ≤ lam2 β ξ ^ j - lam1 β ξ ^ j := by
      have := one_le_pow₀ hl2.le (n := j)
      linarith
    rw [abs_of_nonneg this]
    linarith
  set A := 𝔼.E 0 (Psol 𝔼 α β w m s P0 j) ω - Psol 𝔼 α β w m s P0 0 ω
  set X := c * (lam2 β ξ ^ j - lam1 β ξ ^ j)
  have h1' : |A + X| ≤ K₁ * j := by
    have e : 𝔼.E 0 (Psol 𝔼 α β w m s P0 j) ω + X - Psol 𝔼 α β w m s P0 0 ω = A + X := by
      simp only [A]; ring
    rw [← e]; exact h1
  have htri : |X| ≤ |A + X| + |A| := by
    have := abs_sub (A + X) A
    rwa [add_sub_cancel_left] at this
  nlinarith

open QuadraticRoots in
/-- Woodford (2003), Prop. 3.4 (**no such continuum when `ω̃θ < 0`**): then `αβλ₂ ≥ 1`, and for
`c ≠ 0` the forward sum in (2.8) along `Pcont c` diverges at date `0`, so `Pcont c` solves (2.8)
for no reset-price process. -/
theorem perturbation_not_summable [Nonempty Ω] {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hwneg : w < 0) (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ}
    (hsa : 𝔼.Adapted s) (hsb : BoundedIncr s) {P0 : Ω → ℝ} (hP0 : 𝔼.E 0 P0 = P0)
    (hinit : ∃ B, ∀ ω, |P0 ω - s 0 ω| ≤ B) {c : ℝ} (hc : c ≠ 0) (pstar : ℕ → Ω → ℝ) :
    ¬ Eq28 𝔼 α β w m s (Pcont 𝔼 α β w m s P0 c) pstar := by
  intro h
  obtain ⟨hξ, hl0, hl1, -, -⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  obtain ⟨⟨-, -, -, h28, -, -⟩, -⟩ := prop34 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hsa hsb hP0 hinit
  set ξ := calvoXi α β w
  set l1 := lam1 β ξ
  set l2 := lam2 β ξ
  set ω := Classical.arbitrary Ω
  have hl12 : l1 < l2 := lam1_lt_lam2 hβ0 hξ
  have hge : 1 ≤ α * β * l2 := by
    rw [alpha_beta_lam2 hβ0 hξ, one_le_div hl0]
    by_contra hlt
    push Not at hlt
    have := (alpha_lt_lam1_calvo_iff hα0 hα1 hβ0 hβ1 hw).mp hlt
    linarith
  have hq1 : α * β * l1 ≤ 1 := by
    have : α * β < 1 := by nlinarith
    nlinarith
  obtain ⟨hs0, -⟩ := h28 0 ω
  obtain ⟨hsc, -⟩ := h 0 ω
  have hE : ∀ j, 𝔼.E 0 (costTerm m w s (Pcont 𝔼 α β w m s P0 c) (0 + j)) ω
      = 𝔼.E 0 (costTerm m w s (Psol 𝔼 α β w m s P0) (0 + j)) ω
        + w * c * hpath β ξ (0 + j + 1) := by
    intro j
    have hf : costTerm m w s (Pcont 𝔼 α β w m s P0 c) (0 + j)
        = costTerm m w s (Psol 𝔼 α β w m s P0) (0 + j)
          + fun _ => w * c * hpath β ξ (0 + j + 1) := by
      funext ω'
      simp only [costTerm, Pcont, Pi.add_apply]
      ring
    rw [hf, map_add, 𝔼.const]
    rfl
  have hw0 : w ≠ 0 := hwneg.ne
  have hwc : w * c ≠ 0 := mul_ne_zero hw0 hc
  have hg : Summable (fun j : ℕ => (α * β) ^ j * hpath β ξ (0 + j + 1)) := by
    refine ((hsc.sub hs0).mul_left (w * c)⁻¹).congr fun j => ?_
    rw [hE j]
    field_simp
    ring
  have hlow : ∀ j : ℕ, l2 - l1 ≤ (α * β) ^ j * hpath β ξ (0 + j + 1) := by
    intro j
    have e : (α * β) ^ j * hpath β ξ (0 + j + 1)
        = l2 * (α * β * l2) ^ j - l1 * (α * β * l1) ^ j := by
      simp only [hpath, zero_add, mul_pow, pow_succ]
      ring
    rw [e]
    have h2 : 1 ≤ (α * β * l2) ^ j := one_le_pow₀ hge
    have h1 : (α * β * l1) ^ j ≤ 1 := pow_le_one₀ (by positivity) hq1
    nlinarith
  have hlim := hg.tendsto_atTop_zero
  have : l2 - l1 ≤ 0 := ge_of_tendsto' hlim hlow
  linarith

/-- Woodford (2003), Prop. 3.4 with `ω̃θ = 0` (**uniqueness among all solutions**): when
`ω̃θ = 0`, (2.8) does not involve the price index, so any two solutions of (2.5) and (2.8) with
the same initial price level coincide, in or out of the difference-stationary class. -/
theorem prop34_unique_of_w_zero {α β m : ℝ} {s P pstar P' pstar' : ℕ → Ω → ℝ}
    (h0 : P 0 = P' 0) (h25 : Eq25 α P pstar) (h25' : Eq25 α P' pstar')
    (h28 : Eq28 𝔼 α β 0 m s P pstar) (h28' : Eq28 𝔼 α β 0 m s P' pstar') :
    P = P' ∧ pstar = pstar' := by
  have hc : costTerm m 0 s P = costTerm m 0 s P' := by
    funext T ω; simp [costTerm]
  have hps : pstar = pstar' := by
    funext t ω
    rw [(h28 t ω).2, (h28' t ω).2, hc]
  refine ⟨?_, hps⟩
  funext t
  induction t with
  | zero => exact h0
  | succ t ih =>
    funext ω
    rw [h25 t ω, h25' t ω, ih, hps]

open QuadraticRoots in
/-- Woodford (2003), Prop. 3.4 under perfect foresight with `ω̃θ < 0` (**uniqueness among all
solutions**): every perfect-foresight solution of (2.5) and (2.8) with initial price level `P0`
is (2.9) — no growth restriction is needed, because a deviation from (2.9) must be a multiple of
`λ₂ᵗ − λ₁ᵗ`, which `perturbation_not_summable` excludes. -/
theorem prop34_pf_unique_of_w_neg {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hwneg : w < 0) (hw : 0 < 1 + w) {s : ℕ → Unit → ℝ} (hsb : BoundedIncr s)
    {P0 : Unit → ℝ} {P pstar : ℕ → Unit → ℝ} (h0 : P 0 = P0) (h25 : Eq25 α P pstar)
    (h28 : Eq28 perfectForesight α β w m s P pstar) :
    P = Psol perfectForesight α β w m s P0 := by
  set 𝔽 := perfectForesight
  have hsa : 𝔽.Adapted s := fun _ => rfl
  have hP0 : 𝔽.E 0 P0 = P0 := rfl
  have hinit : ∃ B, ∀ ω, |P0 ω - s 0 ω| ≤ B := ⟨|P0 () - s 0 ()|, fun _ => le_rfl⟩
  obtain ⟨hξ, hl0, hl1, ha0, ha1⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  have hs := diffStationary_of_boundedIncr 𝔽 hsa hsb
  have hab0 : 0 ≤ α * β := (mul_pos hα0 hβ0).le
  have hZ := fun t => congrFun (zbar_rec 𝔽 (m := m) hα0 hα1 hβ0 hβ1 hw hs t) ()
  set ξ := calvoXi α β w
  set l1 := lam1 β ξ
  set l2 := lam2 β ξ
  have hl12 : l1 < l2 := lam1_lt_lam2 hβ0 hξ
  have hl2pos : 0 < l2 := lt_trans hl0 hl12
  set z := zbar 𝔽 α β w m s
  -- the recursive form under perfect foresight
  have hrec : ∀ t, pstar t () = (1 - α * β) / (1 + w) * costTerm m w s P t ()
      + α * β * pstar (t + 1) () := by
    intro t
    obtain ⟨hs0, hv0⟩ := h28 t ()
    obtain ⟨-, hv1⟩ := h28 (t + 1) ()
    rw [hv0, hv1, hs0.tsum_eq_zero_add]
    have e : ∀ j, (α * β) ^ (j + 1) * 𝔽.E t (costTerm m w s P (t + (j + 1))) ()
        = α * β * ((α * β) ^ j * 𝔽.E (t + 1) (costTerm m w s P (t + 1 + j)) ()) := by
      intro j
      rw [show t + (j + 1) = t + 1 + j by omega, pow_succ]
      simp only [𝔽, perfectForesight, LinearMap.id_apply]
      ring
    simp only [e, tsum_mul_left]
    simp only [𝔽, perfectForesight, LinearMap.id_apply, pow_zero, one_mul, add_zero]
    ring
  -- (B.14) under perfect foresight
  have hB14 : ∀ t, P (t + 1) () - l1 * P t () = l2⁻¹ * (P (t + 2) () - l1 * P (t + 1) ())
      + (1 - l1) * (1 - l2⁻¹) * (m + s t ()) := by
    intro t
    have hr := hrec t
    rw [congrFun (pstar_of_eq25 hα1 h25 t) (), congrFun (pstar_of_eq25 hα1 h25 (t + 1)) ()] at hr
    simp only [costTerm] at hr
    exact (B13_iff_B14 hβ0 hξ _ _ _ _).mp ((recursive_iff_B13 hα0 hα1 hw.ne' _ _ _ _).mp hr)
  set d : ℕ → ℝ := fun t => P (t + 1) () - l1 * P t () - z t () with hd_def
  have hd : ∀ t, d (t + 1) = l2 * d t := by
    intro t
    have hb := hB14 t
    have hz := hZ t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mcost, 𝔽, perfectForesight,
      LinearMap.id_apply] at hz
    simp only [hd_def]
    have hl2ne : l2 ≠ 0 := hl2pos.ne'
    field_simp at hb hz ⊢
    linear_combination -hb + hz
  have hdpow : ∀ t, d t = l2 ^ t * d 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [hd t, ih, pow_succ]; ring
  set c := d 0 / (l2 - l1)
  have hl21 : l2 - l1 ≠ 0 := sub_ne_zero.mpr hl12.ne'
  have hPc : P = Pcont 𝔽 α β w m s P0 c := by
    have he : ∀ t, P t () = Psol 𝔽 α β w m s P0 t () + c * hpath β ξ t := by
      intro t
      induction t with
      | zero => simp [hpath, Psol, h0]
      | succ t ih =>
        have h1 : P (t + 1) () = l1 * P t () + z t () + d t := by simp only [hd_def]; ring
        have h2 : Psol 𝔽 α β w m s P0 (t + 1) () = l1 * Psol 𝔽 α β w m s P0 t () + z t () := rfl
        rw [h1, h2, ih, hdpow t]
        simp only [c, hpath]
        field_simp
        ring
    funext t ω
    exact he t
  by_cases hd0 : d 0 = 0
  · have hc0 : c = 0 := by simp [c, hd0]
    rw [hPc, hc0]
    funext t ω
    simp [Pcont]
  · have hc0 : c ≠ 0 := div_ne_zero hd0 hl21
    exact absurd (hPc ▸ h28) (perturbation_not_summable 𝔽 hα0 hα1 hβ0 hβ1 hwneg hw hsa hsb hP0
      hinit hc0 pstar)

open QuadraticRoots in
/-- Woodford (2003), p. 183 (**the flexible-price limit `ξ → ∞`**): for any lagged price level
`p`, the right-hand side of (2.9),
`λ₁ p + (1 − λ₁)(1 − λ₂⁻¹) ∑ λ₂⁻ʲ [log µ + E_t log S_{t+j}]`, tends to `log µ + log S_t` as
`ξ → ∞` (`log S` adapted with bounded first differences). -/
theorem flexible_limit {β : ℝ} (hβ0 : 0 < β) {m : ℝ} {s : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s)
    (hsb : BoundedIncr s) (p : ℝ) (t : ℕ) (ω : Ω) :
    Tendsto (fun c => lam1 β c * p + (1 - lam1 β c) * (1 - (lam2 β c)⁻¹) *
      𝔼.forwardSeries (lam2 β c)⁻¹ (mcost m s) t ω) atTop (𝓝 (m + s t ω)) := by
  have hs := diffStationary_of_boundedIncr 𝔼 hsa hsb
  obtain ⟨K, hK0, hK⟩ := diffStationary_nonneg 𝔼 (mcost_diffStationary 𝔼 (m := m) hs)
  have hl1 := tendsto_lam1_atTop hβ0
  have ha := tendsto_inv_lam2_atTop hβ0
  -- the remainder term vanishes
  have hg : Tendsto (fun a : ℝ => K * (a / (1 - a) ^ 2)) (𝓝 0) (𝓝 0) := by
    have : ContinuousAt (fun a : ℝ => K * (a / (1 - a) ^ 2)) 0 := by
      refine continuousAt_const.mul (continuousAt_id.div (by fun_prop) (by norm_num))
    simpa using this.tendsto
  have hRem : Tendsto (fun c => (1 - lam1 β c) * (1 - (lam2 β c)⁻¹) *
      fwdRem 𝔼 (lam2 β c)⁻¹ (mcost m s) t ω) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun c => abs_nonneg _) ?_ (hg.comp ha)
    filter_upwards [eventually_gt_atTop 0] with c hc
    obtain ⟨-, hl0', hl1', ha0, ha1⟩ : 0 < c ∧ 0 < lam1 β c ∧ lam1 β c < 1 ∧
        0 < (lam2 β c)⁻¹ ∧ (lam2 β c)⁻¹ < 1 :=
      ⟨hc, lam1_pos hβ0 hc, lam1_lt_one hβ0 hc, (inv_lam2_lt_one hβ0 hc).1,
        (inv_lam2_lt_one hβ0 hc).2⟩
    have hR := abs_fwdRem_le 𝔼 ha0.le ha1 hK t ω
    rw [tsum_coe_mul_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_pos ha0])]
      at hR
    have hκ0 : 0 ≤ (1 - lam1 β c) * (1 - (lam2 β c)⁻¹) := mul_nonneg (by linarith) (by linarith)
    have hκ1 : (1 - lam1 β c) * (1 - (lam2 β c)⁻¹) ≤ 1 := by nlinarith
    simp only [Function.comp_apply]
    rw [abs_mul, abs_of_nonneg hκ0]
    calc (1 - lam1 β c) * (1 - (lam2 β c)⁻¹) * |fwdRem 𝔼 (lam2 β c)⁻¹ (mcost m s) t ω|
        ≤ 1 * (K * ((lam2 β c)⁻¹ / (1 - (lam2 β c)⁻¹) ^ 2)) :=
          mul_le_mul hκ1 hR (abs_nonneg _) zero_le_one
      _ = K * ((lam2 β c)⁻¹ / (1 - (lam2 β c)⁻¹) ^ 2) := one_mul _
  have hmain : Tendsto (fun c => lam1 β c * p + (1 - lam1 β c) * (m + s t ω)
      + (1 - lam1 β c) * (1 - (lam2 β c)⁻¹) * fwdRem 𝔼 (lam2 β c)⁻¹ (mcost m s) t ω) atTop
      (𝓝 (0 * p + (1 - 0) * (m + s t ω) + 0)) :=
    ((hl1.mul_const p).add ((tendsto_const_nhds.sub hl1).mul_const _)).add hRem
  simp only [zero_mul, sub_zero, one_mul, zero_add, add_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  have ha1 := (inv_lam2_lt_one hβ0 hc).2
  have ha0 := (inv_lam2_lt_one hβ0 hc).1
  rw [fwd_decomp 𝔼 ha0.le ha1 hK]
  have h1a : 1 - (lam2 β c)⁻¹ ≠ 0 := by linarith
  have hmc : mcost m s t ω = m + s t ω := rfl
  rw [hmc]
  have hinv : (1 - (lam2 β c)⁻¹) * (1 - (lam2 β c)⁻¹)⁻¹ = 1 := mul_inv_cancel₀ h1a
  linear_combination (-(1 - lam1 β c) * (m + s t ω)) * hinv

end Woodford.NominalRigidities.Calvo
