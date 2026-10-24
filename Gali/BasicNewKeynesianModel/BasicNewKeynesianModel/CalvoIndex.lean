/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.CES
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Calvo aggregate price dynamics

Galí (2015), Chapter 3, §3.2.1 (p. 55), eqs. (7)–(8), and Appendix 3.2 (p. 84), eq. (36);
the probability identity of Appendix 3.3 (pp. 84–85).

## The model of the cross-section

Firms form a measure space `(F, m)` (the book's `[0, 1]`). In period `t` firms in a measurable
set `S` reset their price to the common value `P*_t`; the others keep last period's price.
Appendix 3.2 asserts that "the distribution of prices among firms not adjusting in period `t`
corresponds to the distribution of effective prices in period `t − 1`, though with total mass
reduced to `θ`". We take exactly this as the hypothesis (the non-resetters are a
representative subsample):

  `(m.restrict Sᶜ).map p_{t−1} = θ • m.map p_{t−1}`,  `m S = 1 − θ`.

`dist_law_of_motion` then derives the law of motion of the price distribution
`ν_t = θ ν_{t−1} + (1 − θ) δ_{P*_t}`, and `calvo_recursion` derives (7)/(36),
`Π_t^{1−ε} = θ + (1 − θ)(P*_t / P_{t−1})^{1−ε}`. The hypothesis is not vacuous:
`lottery_model` shows that it holds for *every* initial price distribution when the Calvo
lottery is a uniform draw `u ∈ [0, 1]` independent of the firm's price (firms
`Ω × [0, 1]` with the product measure, resetting iff `u > θ`), and `calvo_recursion_lottery`
states (7) for that explicit model. This is the cleanest rigorous reading of "a fraction
`1 − θ` resets, independently of the time elapsed and of the current price": a law of large
numbers is not needed because the continuum of firms carries the product measure.

## Main results

* `dist_law_of_motion`, `integral_calvo_mix`, `calvo_recursion_of_dist`, `calvo_recursion`,
  `lottery_model`, `calvo_recursion_lottery`: eq. (7)/(36).
* `dist_k_step`, `prob_identity`, `dist_k_step_mass`: App. 3.3's decomposition of the
  period-`t + k` distribution by date of last reset, and `θᵏ + (1−θ) ∑_{h=1}^k θ^{k−h} = 1`.
* `zero_inflation_iff`, `zero_inflation_levels`: `Π = 1 ⟺ P* = P_{t−1}` (p. 55).
* `log_infl_eq_inflFn`, `inflFn_zero`, `hasDerivAt_inflFn`, `inflFn_isLittleO`: eq. (8) as
  the exact derivative of `log Π_t` in `log(P*_t/P_{t−1})` at `0`, equal to `1 − θ`.
-/

namespace Gali.BasicNewKeynesianModel.CalvoIndex

open MeasureTheory Gali.BasicNewKeynesianModel.CES

/-- Galí (2015), App. 3.2, p. 84: integrating against the Calvo mixture
`θ ν + (1 − θ) δ_{P*}` gives `θ ∫ f dν + (1 − θ) f(P*)`. -/
theorem integral_calvo_mix {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (Pstar : ℝ)
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    ∫ x, f x ∂(ENNReal.ofReal θ • ν + ENNReal.ofReal (1 - θ) • Measure.dirac Pstar)
      = θ * ∫ x, f x ∂ν + (1 - θ) * f Pstar := by
  have hd : Integrable f (Measure.dirac Pstar) := integrable_dirac (by simp)
  rw [integral_add_measure (hf.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul]

/-- Galí (2015), eq. (36), p. 84, at the level of price distributions: if
`ν_t = θ ν_{t−1} + (1 − θ) δ_{P*}`, where `ν_{t−1}` has a positive, integrable
`∫ p^{1−ε}`, then with `P_s = (∫ p^{1−ε} dν_s)^{1/(1−ε)}`,
`(P_t/P_{t−1})^{1−ε} = θ + (1 − θ)(P*/P_{t−1})^{1−ε}`. -/
theorem calvo_recursion_of_dist {ε θ : ℝ} (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1)
    {νprev : Measure ℝ} {Pstar : ℝ} (hPstar : 0 < Pstar)
    (hint : Integrable (fun x : ℝ => x ^ (1 - ε)) νprev)
    (hpos : 0 < ∫ x, x ^ (1 - ε) ∂νprev) :
    (priceIndex (ENNReal.ofReal θ • νprev + ENNReal.ofReal (1 - θ) • Measure.dirac Pstar) ε
        (fun x => x) / priceIndex νprev ε (fun x => x)) ^ (1 - ε)
      = θ + (1 - θ) * (Pstar / priceIndex νprev ε (fun x => x)) ^ (1 - ε) := by
  have hmix := integral_calvo_mix h0 h1.le Pstar hint
  have hnew : 0 < θ * ∫ x, x ^ (1 - ε) ∂νprev + (1 - θ) * Pstar ^ (1 - ε) := by
    have : 0 < (1 - θ) * Pstar ^ (1 - ε) :=
      mul_pos (by linarith) (Real.rpow_pos_of_pos hPstar _)
    have : 0 ≤ θ * ∫ x, x ^ (1 - ε) ∂νprev := mul_nonneg h0 hpos.le
    linarith
  have hI := priceIndex_pos (P := fun x : ℝ => x) hpos
  have hsub : (1 : ℝ) - ε ≠ 0 := by linarith
  have hPt : priceIndex (ENNReal.ofReal θ • νprev + ENNReal.ofReal (1 - θ) • Measure.dirac Pstar)
      ε (fun x => x) ^ (1 - ε) = θ * ∫ x, x ^ (1 - ε) ∂νprev + (1 - θ) * Pstar ^ (1 - ε) := by
    unfold priceIndex
    rw [hmix, Real.rpow_inv_rpow hnew.le hsub]
  have hPt0 : 0 ≤ priceIndex (ENNReal.ofReal θ • νprev + ENNReal.ofReal (1 - θ) •
      Measure.dirac Pstar) ε (fun x => x) := by
    unfold priceIndex
    rw [hmix]
    exact Real.rpow_nonneg hnew.le _
  rw [Real.div_rpow hPt0 hI.le, Real.div_rpow hPstar.le hI.le, hPt,
    priceIndex_rpow (P := fun x : ℝ => x) hε hpos]
  field_simp

/-- Galí (2015), App. 3.2, p. 84 (**law of motion of the price distribution**). Firms
`(F, m)`; those in `S` (mass `1 − θ`) reset to `P*`, the rest keep `p_{t−1}`, and the
non-resetters are a representative subsample (their price distribution is `θ` times that of
all firms). Then `ν_t = θ ν_{t−1} + (1 − θ) δ_{P*}` where `ν_s = m.map p_s`. -/
theorem dist_law_of_motion {F : Type*} [MeasurableSpace F] (m : Measure F) {θ : ℝ}
    {S : Set F} (hS : MeasurableSet S) {pprev pnow : F → ℝ} (hnow : Measurable pnow)
    {Pstar : ℝ} (hreset : ∀ i ∈ S, pnow i = Pstar) (hkeep : ∀ i ∉ S, pnow i = pprev i)
    (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal θ • m.map pprev) :
    m.map pnow = ENNReal.ofReal θ • m.map pprev + ENNReal.ofReal (1 - θ) • Measure.dirac Pstar := by
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := m) hS]
  rw [Measure.map_add _ _ hnow]
  have h1 : (m.restrict S).map pnow = ENNReal.ofReal (1 - θ) • Measure.dirac Pstar := by
    rw [Measure.map_congr (g := fun _ => Pstar) ((ae_restrict_iff' hS).2
      (Filter.Eventually.of_forall hreset)), Measure.map_const, Measure.restrict_apply_univ,
      hmass]
  have h2 : (m.restrict Sᶜ).map pnow = (m.restrict Sᶜ).map pprev :=
    Measure.map_congr ((ae_restrict_iff' hS.compl).2 (Filter.Eventually.of_forall hkeep))
  rw [h1, h2, hind, add_comm]

/-- Galí (2015), eq. (7), p. 55 and eq. (36), p. 84 (**Calvo price-index recursion**),
derived from the firm-level model of `dist_law_of_motion`: with `P_s` the CES price index of
the cross-section `p_s`, `(P_t/P_{t−1})^{1−ε} = θ + (1 − θ)(P*_t/P_{t−1})^{1−ε}`. -/
theorem calvo_recursion {F : Type*} [MeasurableSpace F] (m : Measure F) {ε θ : ℝ}
    (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1) {S : Set F} (hS : MeasurableSet S)
    {pprev pnow : F → ℝ} (hprev : Measurable pprev) (hnow : Measurable pnow) {Pstar : ℝ}
    (hPstar : 0 < Pstar) (hreset : ∀ i ∈ S, pnow i = Pstar)
    (hkeep : ∀ i ∉ S, pnow i = pprev i) (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal θ • m.map pprev)
    (hint : Integrable (fun i => pprev i ^ (1 - ε)) m)
    (hpos : 0 < ∫ i, pprev i ^ (1 - ε) ∂m) :
    (priceIndex m ε pnow / priceIndex m ε pprev) ^ (1 - ε)
      = θ + (1 - θ) * (Pstar / priceIndex m ε pprev) ^ (1 - ε) := by
  have hmeas : Measurable fun x : ℝ => x ^ (1 - ε) := measurable_id.pow_const _
  have hmap : ∀ p : F → ℝ, Measurable p →
      ∫ i, p i ^ (1 - ε) ∂m = ∫ x, x ^ (1 - ε) ∂(m.map p) := fun p hp =>
    (integral_map hp.aemeasurable hmeas.aestronglyMeasurable).symm
  have hidx : ∀ p : F → ℝ, Measurable p →
      priceIndex m ε p = priceIndex (m.map p) ε (fun x => x) := fun p hp => by
    unfold priceIndex
    rw [hmap p hp]
  have hint' : Integrable (fun x : ℝ => x ^ (1 - ε)) (m.map pprev) :=
    (integrable_map_measure hmeas.aestronglyMeasurable hprev.aemeasurable).2 hint
  rw [hidx pnow hnow, hidx pprev hprev, dist_law_of_motion m hS hnow hreset hkeep hmass hind]
  rw [hmap pprev hprev] at hpos
  exact calvo_recursion_of_dist hε h0 h1 hPstar hint' hpos

/-- Galí (2015), §3.2, p. 55 (**the Calvo lottery is a representative subsample**): for any
probability space of firms `(Ω, μ₀)` with prices `p`, give each firm an independent uniform
draw `u ∈ [0, 1]` and let it reset iff `u > θ`. On `Ω × [0, 1]` with the product measure the
resetters have mass `1 − θ`, the non-resetters' price distribution is `θ` times the full one,
and the full distribution is that of `p` under `μ₀`. -/
theorem lottery_model {Ω : Type*} [MeasurableSpace Ω] (μ₀ : Measure Ω)
    [IsProbabilityMeasure μ₀] {p : Ω → ℝ} (hp : Measurable p) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) :
    μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.univ ×ˢ Set.Ioi θ)
        = ENNReal.ofReal (1 - θ) ∧
      ((μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).restrict (Set.univ ×ˢ Set.Ioi θ)ᶜ).map
          (fun x => p x.1)
        = ENNReal.ofReal θ •
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
    have : Set.Ioi θ ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc θ 1 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by linarith, h'⟩
    rw [this, Real.volume_Ioc]
  · have hc : (Set.univ ×ˢ Set.Ioi θ : Set (Ω × ℝ))ᶜ = Set.univ ×ˢ Set.Iic θ := by
      ext x
      simp
    rw [hc, ← Measure.prod_restrict, Measure.restrict_univ, hfst _ inferInstance, hall,
      Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Iic]
    have : Set.Iic θ ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 θ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h, h', -⟩; exact ⟨h', h⟩
      · rintro ⟨h, h'⟩; exact ⟨h', h, by linarith⟩
    rw [this, Real.volume_Icc, sub_zero]

/-- Galí (2015), eq. (7), p. 55 and eq. (36), p. 84, for the **explicit Calvo-lottery
economy** of `lottery_model`: firms `(ω, u) ∈ Ω × [0, 1]`, last period's price `p ω`, and
this period's price `P*` if `u > θ` and `p ω` otherwise. With `P_{t−1}` the index of `p`
under `μ₀`, `(P_t/P_{t−1})^{1−ε} = θ + (1 − θ)(P*/P_{t−1})^{1−ε}`. -/
theorem calvo_recursion_lottery {Ω : Type*} [MeasurableSpace Ω] (μ₀ : Measure Ω)
    [IsProbabilityMeasure μ₀] {ε θ : ℝ} (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1) {p : Ω → ℝ}
    (hp : Measurable p) (hp0 : ∀ ω, 0 < p ω) (hint : Integrable (fun ω => p ω ^ (1 - ε)) μ₀)
    {Pstar : ℝ} (hPstar : 0 < Pstar) :
    (priceIndex (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) ε
        (fun x => if θ < x.2 then Pstar else p x.1) / priceIndex μ₀ ε p) ^ (1 - ε)
      = θ + (1 - θ) * (Pstar / priceIndex μ₀ ε p) ^ (1 - ε) := by
  obtain ⟨hmass, hind, hall⟩ := lottery_model μ₀ hp h0 h1.le
  have hmeas : Measurable fun x : ℝ => x ^ (1 - ε) := measurable_id.pow_const _
  have hpp : Measurable fun x : Ω × ℝ => p x.1 := hp.comp measurable_fst
  have hI : ∫ x, p x.1 ^ (1 - ε) ∂(μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ∫ ω, p ω ^ (1 - ε) ∂μ₀ := by
    rw [← integral_map hpp.aemeasurable hmeas.aestronglyMeasurable, hall,
      integral_map hp.aemeasurable hmeas.aestronglyMeasurable]
  have hidx : priceIndex (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) ε (fun x => p x.1)
      = priceIndex μ₀ ε p := by
    unfold priceIndex
    rw [hI]
  have hint' : Integrable (fun x => p x.1 ^ (1 - ε))
      (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have := (integrable_map_measure hmeas.aestronglyMeasurable hp.aemeasurable).2 hint
    rw [← hall] at this
    exact (integrable_map_measure hmeas.aestronglyMeasurable hpp.aemeasurable).1 this
  have hpos : 0 < ∫ ω, p ω ^ (1 - ε) ∂μ₀ :=
    integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ₀)
      (fun ω => Real.rpow_pos_of_pos (hp0 ω) _) hint
  have hS : MeasurableSet (Set.univ ×ˢ Set.Ioi θ : Set (Ω × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioi
  have hnow : Measurable fun x : Ω × ℝ => if θ < x.2 then Pstar else p x.1 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const hpp
  rw [← hidx]
  refine calvo_recursion _ hε h0 h1 hS hpp hnow hPstar ?_ ?_ hmass hind hint'
    (by rw [hI]; exact hpos)
  · intro x hx
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hx
    simp only [hx, ↓reduceIte]
  · intro x hx
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hx
    simp only [hx, ↓reduceIte]

/-- Galí (2015), App. 3.3, p. 84 (**decomposition by date of last reset**): if the price
distribution follows `ν_{s+1} = θ ν_s + (1 − θ) δ_{P*_{s+1}}`, then
`ν_{t+k} = θᵏ ν_t + ∑_{h=1}^{k} (1 − θ) θ^{k−h} δ_{P*_{t+h}}` (written with `h ↦ h + 1`): a
mass `θᵏ` still charges the prices of date `t`, and a mass `(1 − θ)θ^{k−h}` last reset at
`t + h`. -/
theorem dist_k_step {θ : ℝ} (h0 : 0 ≤ θ) {ν : ℕ → Measure ℝ} {Pstar : ℕ → ℝ}
    (hlaw : ∀ t, ν (t + 1)
      = ENNReal.ofReal θ • ν t + ENNReal.ofReal (1 - θ) • Measure.dirac (Pstar (t + 1)))
    (t k : ℕ) :
    ν (t + k) = ENNReal.ofReal (θ ^ k) • ν t + ∑ h ∈ Finset.range k,
      ENNReal.ofReal ((1 - θ) * θ ^ (k - 1 - h)) • Measure.dirac (Pstar (t + h + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, hlaw, ih, smul_add, Finset.smul_sum, smul_smul, Finset.sum_range_succ]
    simp_rw [smul_smul]
    have hc : ∀ h ∈ Finset.range k, ENNReal.ofReal θ * ENNReal.ofReal ((1 - θ) * θ ^ (k - 1 - h))
        = ENNReal.ofReal ((1 - θ) * θ ^ (k + 1 - 1 - h)) := by
      intro h hh
      rw [Finset.mem_range] at hh
      rw [← ENNReal.ofReal_mul h0]
      congr 1
      rw [show k + 1 - 1 - h = (k - 1 - h) + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl fun h hh => by rw [hc h hh], ← ENNReal.ofReal_mul h0, ← pow_succ',
      show k + 1 - 1 - k = 0 by omega, pow_zero, mul_one, add_assoc]

/-- Galí (2015), App. 3.3, p. 84: the probabilities in (37) sum to one,
`θᵏ + (1 − θ) ∑_{h=1}^{k} θ^{k−h} = 1`. -/
theorem prob_identity (θ : ℝ) (k : ℕ) :
    θ ^ k + (1 - θ) * ∑ h ∈ Finset.Icc 1 k, θ ^ (k - h) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero]
    have hs : ∑ h ∈ Finset.Icc 1 k, θ ^ (k + 1 - h) = θ * ∑ h ∈ Finset.Icc 1 k, θ ^ (k - h) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [Finset.mem_Icc] at hh
      rw [show k + 1 - h = (k - h) + 1 by omega, pow_succ]
      ring
    rw [hs]
    linear_combination θ * ih

/-- Galí (2015), App. 3.3, p. 84: the identity of `prob_identity` in the indexing of
`dist_k_step`, `θᵏ + ∑_{h<k} (1 − θ) θ^{k−1−h} = 1`. -/
theorem prob_identity_range (θ : ℝ) (k : ℕ) :
    θ ^ k + ∑ h ∈ Finset.range k, (1 - θ) * θ ^ (k - 1 - h) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, show k + 1 - 1 - k = 0 by omega, pow_zero]
    have hs : ∑ h ∈ Finset.range k, (1 - θ) * θ ^ (k + 1 - 1 - h)
        = θ * ∑ h ∈ Finset.range k, (1 - θ) * θ ^ (k - 1 - h) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [Finset.mem_range] at hh
      rw [show k + 1 - 1 - h = (k - 1 - h) + 1 by omega, pow_succ]
      ring
    rw [hs]
    linear_combination θ * ih

/-- Galí (2015), App. 3.3, p. 84: if `ν_t` is a probability distribution, so is `ν_{t+k}`;
the masses of `dist_k_step` add up to one. -/
theorem dist_k_step_mass {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ν : ℕ → Measure ℝ}
    {Pstar : ℕ → ℝ}
    (hlaw : ∀ t, ν (t + 1)
      = ENNReal.ofReal θ • ν t + ENNReal.ofReal (1 - θ) • Measure.dirac (Pstar (t + 1)))
    (t k : ℕ) (hν : ν t Set.univ = 1) : ν (t + k) Set.univ = 1 := by
  have hnn : ∀ h ∈ Finset.range k, 0 ≤ (1 - θ) * θ ^ (k - 1 - h) :=
    fun h _ => mul_nonneg (by linarith) (pow_nonneg h0 _)
  rw [dist_k_step h0 hlaw t k]
  simp only [Measure.coe_add, Measure.coe_smul, Measure.coe_finsetSum, Pi.add_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, measure_univ, hν, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← ENNReal.ofReal_add (pow_nonneg h0 _)
    (Finset.sum_nonneg hnn), prob_identity_range, ENNReal.ofReal_one]

/-- Galí (2015), p. 55: a positive number `y` satisfies `y^{1−ε} = 1` iff `y = 1` (`ε ≠ 1`). -/
theorem rpow_eq_one_iff {ε y : ℝ} (hε : ε ≠ 1) (hy : 0 < y) : y ^ (1 - ε) = 1 ↔ y = 1 := by
  constructor
  · intro h
    have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
    rw [← Real.rpow_rpow_inv hy.le hsub, h, Real.one_rpow]
  · rintro rfl
    exact Real.one_rpow _

/-- Galí (2015), p. 55 (**zero-inflation steady state**): under (7), gross inflation is one
iff the reset price equals last period's price index, `Π = 1 ⟺ P*/P_{t−1} = 1`
(`0 ≤ θ < 1`, `ε ≠ 1`). -/
theorem zero_inflation_iff {θ ε Pi x : ℝ} (h1 : θ < 1) (hε : ε ≠ 1) (hPi : 0 < Pi)
    (hx : 0 < x) (hrec : Pi ^ (1 - ε) = θ + (1 - θ) * x ^ (1 - ε)) : Pi = 1 ↔ x = 1 := by
  rw [← rpow_eq_one_iff hε hPi, ← rpow_eq_one_iff hε hx, hrec]
  have : (1 : ℝ) - θ ≠ 0 := by linarith
  constructor
  · intro h
    have h' : (1 - θ) * x ^ (1 - ε) = (1 - θ) * 1 := by linarith
    exact mul_left_cancel₀ this h'
  · intro h
    rw [h]
    ring

/-- Galí (2015), p. 55, in levels: under (7), `P_t = P_{t−1}` iff `P*_t = P_{t−1}`, and then
`P*_t = P_{t−1} = P_t`. -/
theorem zero_inflation_levels {θ ε Pt Pprev Pstar : ℝ} (h1 : θ < 1) (hε : ε ≠ 1)
    (hPt : 0 < Pt) (hPprev : 0 < Pprev) (hPstar : 0 < Pstar)
    (hrec : (Pt / Pprev) ^ (1 - ε) = θ + (1 - θ) * (Pstar / Pprev) ^ (1 - ε)) :
    (Pt = Pprev ↔ Pstar = Pprev) ∧ (Pt = Pprev → Pstar = Pprev ∧ Pstar = Pt) := by
  have h := zero_inflation_iff h1 hε (div_pos hPt hPprev) (div_pos hPstar hPprev) hrec
  rw [div_eq_one_iff_eq hPprev.ne', div_eq_one_iff_eq hPprev.ne'] at h
  exact ⟨h, fun he => ⟨h.1 he, (h.1 he).trans he.symm⟩⟩

/-- Galí (2015), eq. (8), p. 55: log gross inflation as a function of the log relative reset
price `y = log(P*_t/P_{t−1})`, as implied by (7):
`π(y) = (1 − ε)⁻¹ log(θ + (1 − θ) e^{(1−ε) y})`. -/
noncomputable def inflFn (θ ε y : ℝ) : ℝ :=
  (1 - ε)⁻¹ * Real.log (θ + (1 - θ) * Real.exp ((1 - ε) * y))

/-- Galí (2015), eq. (8), p. 55: the exact (nonlinear) relation (7) says
`log Π_t = inflFn θ ε (log(P*_t/P_{t−1}))`. -/
theorem log_infl_eq_inflFn {θ ε Pi x : ℝ} (hε : ε ≠ 1) (hPi : 0 < Pi) (hx : 0 < x)
    (hrec : Pi ^ (1 - ε) = θ + (1 - θ) * x ^ (1 - ε)) :
    Real.log Pi = inflFn θ ε (Real.log x) := by
  have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have h := congrArg Real.log hrec
  rw [Real.log_rpow hPi, Real.rpow_def_of_pos hx, mul_comm (Real.log x)] at h
  rw [inflFn, ← h]
  field_simp

/-- Galí (2015), p. 55: at the zero-inflation steady state (`P* = P_{t−1}`, i.e. `y = 0`),
`π = 0`. -/
theorem inflFn_zero (θ ε : ℝ) : inflFn θ ε 0 = 0 := by
  simp [inflFn]

/-- Galí (2015), eq. (8), p. 55 (**exact derivative**): `d log Π_t / d log(P*_t/P_{t−1}) = 1 − θ`
at the zero-inflation steady state; i.e. `π_t = (1 − θ)(p*_t − p_{t−1})` is the first-order
approximation of (7). -/
theorem hasDerivAt_inflFn (θ : ℝ) {ε : ℝ} (hε : ε ≠ 1) : HasDerivAt (inflFn θ ε) (1 - θ) 0 := by
  have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have h1 : HasDerivAt (fun y : ℝ => (1 - ε) * y) (1 - ε) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (1 - ε)
  have h2 := HasDerivAt.exp h1
  have h3 := HasDerivAt.const_add θ (HasDerivAt.const_mul (1 - θ) h2)
  have hne : θ + (1 - θ) * Real.exp ((1 - ε) * 0) ≠ 0 := by simp
  have h4 := HasDerivAt.const_mul (1 - ε)⁻¹ (HasDerivAt.log h3 hne)
  unfold inflFn
  convert h4 using 1
  simp only [mul_zero, Real.exp_zero, mul_one]
  field_simp
  ring

/-- Galí (2015), eq. (8), p. 55: the remainder of the log-linear approximation is
`o(y)`, `inflFn θ ε y − (1 − θ) y = o(y)` as `y → 0`. -/
theorem inflFn_isLittleO (θ : ℝ) {ε : ℝ} (hε : ε ≠ 1) :
    (fun y => inflFn θ ε y - (1 - θ) * y) =o[nhds 0] fun y => y := by
  have h := (hasDerivAt_iff_isLittleO.1 (hasDerivAt_inflFn θ hε))
  simpa [inflFn_zero, mul_comm] using h

end Gali.BasicNewKeynesianModel.CalvoIndex
