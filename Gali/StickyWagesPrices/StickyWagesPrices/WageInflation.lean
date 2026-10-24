/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.WageSetting
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Wage inflation dynamics

Galí (2015), Chapter 6, §6.1.2.2 (pp. 169–170), eqs. (14)–(15).

## The cross-section of wages

Labour types form a measure space `(F, m)`. In period `t` the types in a measurable set `S`
(mass `1 − θ_w`) reset their wage to the common `W*_t`; the others keep last period's wage, and
the non-resetters are a representative subsample. `wage_dist_law_of_motion` derives the law of
motion of the wage distribution `ν_t = θ_w ν_{t−1} + (1 − θ_w) δ_{W*_t}`, `wage_recursion` and
`wage_index_recursion` the CES wage-index recursion of p. 169,
`W_t^{1−ε_w} = θ_w W_{t−1}^{1−ε_w} + (1 − θ_w)(W*_t)^{1−ε_w}`, and `lottery_model` /
`wage_recursion_lottery` show the hypotheses hold for an explicit Calvo lottery. The
cross-section of **log** wages obeys the same law (`log_wage_law_of_motion`), which is the
`wageMix` recursion behind the wage Lemma 2 of `WageDispersion`. All of this is restated from
the Chapter 3 project (`CalvoIndex.lean`), with prices replaced by wages.

## Main results

* `log_wageIndex_eq`, `hasDerivAt_inflFn`, `eq14_tangent`: (14) is the exact first-order
  approximation of the wage-index recursion: `log W_t = w_{t−1} + f(w*_t − w_{t−1})` with
  `f(0) = 0`, `f'(0) = 1 − θ_w`, and the tangent line is `θ_w w_{t−1} + (1 − θ_w) w*_t`.
* `eq15_iff`: given (14), the recursive wage-setting rule (13) holds at every date iff the
  **wage-inflation equation (15)** `π^w_t = β E_t π^w_{t+1} − λ_w μ̂^w_t` does, with
  `λ_w = (1 − θ_w)(1 − βθ_w)/(θ_w(1 + ε_wφ))`.
* `lambdaW_pos`, `lambdaW_strictAntiOn_theta`, `lambdaW_strictAntiOn_eps`,
  `lambdaW_strictAntiOn_phi`: `λ_w > 0`, strictly decreasing in `θ_w`, `ε_w` and `φ` (p. 170).
-/

namespace Gali.StickyWagesPrices.WageInflation

open MeasureTheory
open Gali.StickyWagesPrices.LaborAggregation Gali.StickyWagesPrices.WageDispersion

/-- Galí (2015), §6.1.2.2, p. 169: integrating against the Calvo mixture
`θ ν + (1 − θ) δ_{W*}` gives `θ ∫ f dν + (1 − θ) f(W*)`. -/
theorem integral_wage_mix {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (Wstar : ℝ)
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    ∫ x, f x ∂(ENNReal.ofReal θ • ν + ENNReal.ofReal (1 - θ) • Measure.dirac Wstar)
      = θ * ∫ x, f x ∂ν + (1 - θ) * f Wstar := by
  have hd : Integrable f (Measure.dirac Wstar) := integrable_dirac (by simp)
  rw [integral_add_measure (hf.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul]

/-- Galí (2015), eq. (4), p. 165, at the level of wage distributions: if
`ν_t = θ ν_{t−1} + (1 − θ) δ_{W*}`, where `ν_{t−1}` has a positive, integrable
`∫ p^{1−ε}`, then with `W_s = (∫ p^{1−ε} dν_s)^{1/(1−ε)}`,
`(W_t/W_{t−1})^{1−ε} = θ + (1 − θ)(W*/W_{t−1})^{1−ε}`. -/
theorem wage_recursion_of_dist {ε θ : ℝ} (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1)
    {νprev : Measure ℝ} {Wstar : ℝ} (hWstar : 0 < Wstar)
    (hint : Integrable (fun x : ℝ => x ^ (1 - ε)) νprev)
    (hpos : 0 < ∫ x, x ^ (1 - ε) ∂νprev) :
    (cesIndex (ENNReal.ofReal θ • νprev + ENNReal.ofReal (1 - θ) • Measure.dirac Wstar) ε
        (fun x => x) / cesIndex νprev ε (fun x => x)) ^ (1 - ε)
      = θ + (1 - θ) * (Wstar / cesIndex νprev ε (fun x => x)) ^ (1 - ε) := by
  have hmix := integral_wage_mix h0 h1.le Wstar hint
  have hnew : 0 < θ * ∫ x, x ^ (1 - ε) ∂νprev + (1 - θ) * Wstar ^ (1 - ε) := by
    have : 0 < (1 - θ) * Wstar ^ (1 - ε) :=
      mul_pos (by linarith) (Real.rpow_pos_of_pos hWstar _)
    have : 0 ≤ θ * ∫ x, x ^ (1 - ε) ∂νprev := mul_nonneg h0 hpos.le
    linarith
  have hI := cesIndex_pos (W := fun x : ℝ => x) hpos
  have hsub : (1 : ℝ) - ε ≠ 0 := by linarith
  have hPt : cesIndex (ENNReal.ofReal θ • νprev + ENNReal.ofReal (1 - θ) • Measure.dirac Wstar)
      ε (fun x => x) ^ (1 - ε) = θ * ∫ x, x ^ (1 - ε) ∂νprev + (1 - θ) * Wstar ^ (1 - ε) := by
    unfold cesIndex
    rw [hmix, Real.rpow_inv_rpow hnew.le hsub]
  have hPt0 : 0 ≤ cesIndex (ENNReal.ofReal θ • νprev + ENNReal.ofReal (1 - θ) •
      Measure.dirac Wstar) ε (fun x => x) := by
    unfold cesIndex
    rw [hmix]
    exact Real.rpow_nonneg hnew.le _
  rw [Real.div_rpow hPt0 hI.le, Real.div_rpow hWstar.le hI.le, hPt,
    cesIndex_rpow (W := fun x : ℝ => x) hε hpos]
  field_simp

/-- Galí (2015), §6.1.2.2, p. 169 (**law of motion of the wage distribution**). Labour types
`(F, m)`; those in `S` (mass `1 − θ`) reset to `W*`, the rest keep `w_{t−1}`, and the
non-resetters are a representative subsample (their wage distribution is `θ` times that of
all labour types). Then `ν_t = θ ν_{t−1} + (1 − θ) δ_{W*}` where `ν_s = m.map p_s`. -/
theorem wage_dist_law_of_motion {F : Type*} [MeasurableSpace F] (m : Measure F) {θ : ℝ}
    {S : Set F} (hS : MeasurableSet S) {pprev pnow : F → ℝ} (hnow : Measurable pnow)
    {Wstar : ℝ} (hreset : ∀ i ∈ S, pnow i = Wstar) (hkeep : ∀ i ∉ S, pnow i = pprev i)
    (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal θ • m.map pprev) :
    m.map pnow = ENNReal.ofReal θ • m.map pprev + ENNReal.ofReal (1 - θ) • Measure.dirac Wstar := by
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := m) hS]
  rw [Measure.map_add _ _ hnow]
  have h1 : (m.restrict S).map pnow = ENNReal.ofReal (1 - θ) • Measure.dirac Wstar := by
    rw [Measure.map_congr (g := fun _ => Wstar) ((ae_restrict_iff' hS).2
      (Filter.Eventually.of_forall hreset)), Measure.map_const, Measure.restrict_apply_univ,
      hmass]
  have h2 : (m.restrict Sᶜ).map pnow = (m.restrict Sᶜ).map pprev :=
    Measure.map_congr ((ae_restrict_iff' hS.compl).2 (Filter.Eventually.of_forall hkeep))
  rw [h1, h2, hind, add_comm]

/-- Galí (2015), the wage-index recursion, p. 169 (**Calvo wage-index recursion**),
derived from the type-level model of `wage_dist_law_of_motion`: with `W_s` the CES wage index of
the cross-section `p_s`, `(W_t/W_{t−1})^{1−ε} = θ + (1 − θ)(W*_t/W_{t−1})^{1−ε}`. -/
theorem wage_recursion {F : Type*} [MeasurableSpace F] (m : Measure F) {ε θ : ℝ}
    (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1) {S : Set F} (hS : MeasurableSet S)
    {pprev pnow : F → ℝ} (hprev : Measurable pprev) (hnow : Measurable pnow) {Wstar : ℝ}
    (hWstar : 0 < Wstar) (hreset : ∀ i ∈ S, pnow i = Wstar)
    (hkeep : ∀ i ∉ S, pnow i = pprev i) (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal θ • m.map pprev)
    (hint : Integrable (fun i => pprev i ^ (1 - ε)) m)
    (hpos : 0 < ∫ i, pprev i ^ (1 - ε) ∂m) :
    (cesIndex m ε pnow / cesIndex m ε pprev) ^ (1 - ε)
      = θ + (1 - θ) * (Wstar / cesIndex m ε pprev) ^ (1 - ε) := by
  have hmeas : Measurable fun x : ℝ => x ^ (1 - ε) := measurable_id.pow_const _
  have hmap : ∀ p : F → ℝ, Measurable p →
      ∫ i, p i ^ (1 - ε) ∂m = ∫ x, x ^ (1 - ε) ∂(m.map p) := fun p hp =>
    (integral_map hp.aemeasurable hmeas.aestronglyMeasurable).symm
  have hidx : ∀ p : F → ℝ, Measurable p →
      cesIndex m ε p = cesIndex (m.map p) ε (fun x => x) := fun p hp => by
    unfold cesIndex
    rw [hmap p hp]
  have hint' : Integrable (fun x : ℝ => x ^ (1 - ε)) (m.map pprev) :=
    (integrable_map_measure hmeas.aestronglyMeasurable hprev.aemeasurable).2 hint
  rw [hidx pnow hnow, hidx pprev hprev, wage_dist_law_of_motion m hS hnow hreset hkeep hmass hind]
  rw [hmap pprev hprev] at hpos
  exact wage_recursion_of_dist hε h0 h1 hWstar hint' hpos

/-- Galí (2015), §6.1.2.1, p. 167 (**the Calvo lottery is a representative subsample**): for any
probability space of labour types `(Ω, μ₀)` with wages `p`, give each type an independent uniform
draw `u ∈ [0, 1]` and let it reset iff `u > θ`. On `Ω × [0, 1]` with the product measure the
resetters have mass `1 − θ`, the non-resetters' wage distribution is `θ` times the full one,
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

/-- Galí (2015), the wage-index recursion, p. 169, for the **explicit Calvo-lottery
economy** of `lottery_model`: labour types `(ω, u) ∈ Ω × [0, 1]`, last period's wage `w ω`, and
this period's wage `W*` if `u > θ` and `w ω` otherwise. With `W_{t−1}` the index of `w`
under `μ₀`, `(W_t/W_{t−1})^{1−ε} = θ + (1 − θ)(W*/W_{t−1})^{1−ε}`. -/
theorem wage_recursion_lottery {Ω : Type*} [MeasurableSpace Ω] (μ₀ : Measure Ω)
    [IsProbabilityMeasure μ₀] {ε θ : ℝ} (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1) {p : Ω → ℝ}
    (hp : Measurable p) (hp0 : ∀ ω, 0 < p ω) (hint : Integrable (fun ω => p ω ^ (1 - ε)) μ₀)
    {Wstar : ℝ} (hWstar : 0 < Wstar) :
    (cesIndex (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) ε
        (fun x => if θ < x.2 then Wstar else p x.1) / cesIndex μ₀ ε p) ^ (1 - ε)
      = θ + (1 - θ) * (Wstar / cesIndex μ₀ ε p) ^ (1 - ε) := by
  obtain ⟨hmass, hind, hall⟩ := lottery_model μ₀ hp h0 h1.le
  have hmeas : Measurable fun x : ℝ => x ^ (1 - ε) := measurable_id.pow_const _
  have hpp : Measurable fun x : Ω × ℝ => p x.1 := hp.comp measurable_fst
  have hI : ∫ x, p x.1 ^ (1 - ε) ∂(μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ∫ ω, p ω ^ (1 - ε) ∂μ₀ := by
    rw [← integral_map hpp.aemeasurable hmeas.aestronglyMeasurable, hall,
      integral_map hp.aemeasurable hmeas.aestronglyMeasurable]
  have hidx : cesIndex (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) ε (fun x => p x.1)
      = cesIndex μ₀ ε p := by
    unfold cesIndex
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
  have hnow : Measurable fun x : Ω × ℝ => if θ < x.2 then Wstar else p x.1 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const hpp
  rw [← hidx]
  refine wage_recursion _ hε h0 h1 hS hpp hnow hWstar ?_ ?_ hmass hind hint'
    (by rw [hI]; exact hpos)
  · intro x hx
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hx
    simp only [hx, ↓reduceIte]
  · intro x hx
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hx
    simp only [hx, ↓reduceIte]

/-- Galí (2015), §6.1.2.1, p. 167 (**decomposition by date of last reset**): if the wage
distribution follows `ν_{s+1} = θ ν_s + (1 − θ) δ_{W*_{s+1}}`, then
`ν_{t+k} = θᵏ ν_t + ∑_{h=1}^{k} (1 − θ) θ^{k−h} δ_{W*_{t+h}}` (written with `h ↦ h + 1`): a
mass `θᵏ` still charges the wages of date `t`, and a mass `(1 − θ)θ^{k−h}` last reset at
`t + h`. -/
theorem dist_k_step {θ : ℝ} (h0 : 0 ≤ θ) {ν : ℕ → Measure ℝ} {Wstar : ℕ → ℝ}
    (hlaw : ∀ t, ν (t + 1)
      = ENNReal.ofReal θ • ν t + ENNReal.ofReal (1 - θ) • Measure.dirac (Wstar (t + 1)))
    (t k : ℕ) :
    ν (t + k) = ENNReal.ofReal (θ ^ k) • ν t + ∑ h ∈ Finset.range k,
      ENNReal.ofReal ((1 - θ) * θ ^ (k - 1 - h)) • Measure.dirac (Wstar (t + h + 1)) := by
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

/-- Galí (2015), §6.1.2.1, p. 167: the probabilities in (10) sum to one,
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

/-- Galí (2015), §6.1.2.1, p. 167: the identity of `prob_identity` in the indexing of
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

/-- Galí (2015), §6.1.2.1, p. 167: if `ν_t` is a probability distribution, so is `ν_{t+k}`;
the masses of `dist_k_step` add up to one. -/
theorem dist_k_step_mass {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ν : ℕ → Measure ℝ}
    {Wstar : ℕ → ℝ}
    (hlaw : ∀ t, ν (t + 1)
      = ENNReal.ofReal θ • ν t + ENNReal.ofReal (1 - θ) • Measure.dirac (Wstar (t + 1)))
    (t k : ℕ) (hν : ν t Set.univ = 1) : ν (t + k) Set.univ = 1 := by
  have hnn : ∀ h ∈ Finset.range k, 0 ≤ (1 - θ) * θ ^ (k - 1 - h) :=
    fun h _ => mul_nonneg (by linarith) (pow_nonneg h0 _)
  rw [dist_k_step h0 hlaw t k]
  simp only [Measure.coe_add, Measure.coe_smul, Measure.coe_finsetSum, Pi.add_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, measure_univ, hν, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← ENNReal.ofReal_add (pow_nonneg h0 _)
    (Finset.sum_nonneg hnn), prob_identity_range, ENNReal.ofReal_one]

/-- Galí (2015), p. 169: a positive number `y` satisfies `y^{1−ε} = 1` iff `y = 1` (`ε ≠ 1`). -/
theorem rpow_eq_one_iff {ε y : ℝ} (hε : ε ≠ 1) (hy : 0 < y) : y ^ (1 - ε) = 1 ↔ y = 1 := by
  constructor
  · intro h
    have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
    rw [← Real.rpow_rpow_inv hy.le hsub, h, Real.one_rpow]
  · rintro rfl
    exact Real.one_rpow _

/-- Galí (2015), p. 169 (**zero-wage-inflation steady state**): under the wage-index recursion,
gross wage inflation is one
iff the reset wage equals last period's wage index, `Π = 1 ⟺ W*/W_{t−1} = 1`
(`0 ≤ θ < 1`, `ε ≠ 1`). -/
theorem zero_wage_inflation_iff {θ ε Pi x : ℝ} (h1 : θ < 1) (hε : ε ≠ 1) (hPi : 0 < Pi)
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

/-- Galí (2015), p. 169, in levels: under the wage-index recursion, `W_t = W_{t−1}` iff
`W*_t = W_{t−1}`, and then
`W*_t = W_{t−1} = W_t`. -/
theorem zero_wage_inflation_levels {θ ε Pt Pprev Wstar : ℝ} (h1 : θ < 1) (hε : ε ≠ 1)
    (hPt : 0 < Pt) (hPprev : 0 < Pprev) (hWstar : 0 < Wstar)
    (hrec : (Pt / Pprev) ^ (1 - ε) = θ + (1 - θ) * (Wstar / Pprev) ^ (1 - ε)) :
    (Pt = Pprev ↔ Wstar = Pprev) ∧ (Pt = Pprev → Wstar = Pprev ∧ Wstar = Pt) := by
  have h := zero_wage_inflation_iff h1 hε (div_pos hPt hPprev) (div_pos hWstar hPprev) hrec
  rw [div_eq_one_iff_eq hPprev.ne', div_eq_one_iff_eq hPprev.ne'] at h
  exact ⟨h, fun he => ⟨h.1 he, (h.1 he).trans he.symm⟩⟩

/-- Galí (2015), eq. (14), p. 169: log gross wage inflation as a function of the log relative reset
wage `y = log(W*_t/W_{t−1})`, as implied by (7):
`π(y) = (1 − ε)⁻¹ log(θ + (1 − θ) e^{(1−ε) y})`. -/
noncomputable def inflFn (θ ε y : ℝ) : ℝ :=
  (1 - ε)⁻¹ * Real.log (θ + (1 - θ) * Real.exp ((1 - ε) * y))

/-- Galí (2015), eq. (14), p. 169: the exact (nonlinear) wage-index recursion says
`log Π_t = inflFn θ ε (log(W*_t/W_{t−1}))`. -/
theorem log_infl_eq_inflFn {θ ε Pi x : ℝ} (hε : ε ≠ 1) (hPi : 0 < Pi) (hx : 0 < x)
    (hrec : Pi ^ (1 - ε) = θ + (1 - θ) * x ^ (1 - ε)) :
    Real.log Pi = inflFn θ ε (Real.log x) := by
  have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have h := congrArg Real.log hrec
  rw [Real.log_rpow hPi, Real.rpow_def_of_pos hx, mul_comm (Real.log x)] at h
  rw [inflFn, ← h]
  field_simp

/-- Galí (2015), p. 169: at the zero-wage-inflation steady state (`W* = W_{t−1}`, i.e. `y = 0`),
`π = 0`. -/
theorem inflFn_zero (θ ε : ℝ) : inflFn θ ε 0 = 0 := by
  simp [inflFn]

/-- Galí (2015), eq. (14), p. 169 (**exact derivative**): `d log Π_t / d log(W*_t/W_{t−1}) = 1 − θ`
at the zero-wage-inflation steady state; i.e. `π_t = (1 − θ)(p*_t − p_{t−1})` is the first-order
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

/-- Galí (2015), eq. (14), p. 169: the remainder of the log-linear approximation is
`o(y)`, `inflFn θ ε y − (1 − θ) y = o(y)` as `y → 0`. -/
theorem inflFn_isLittleO (θ : ℝ) {ε : ℝ} (hε : ε ≠ 1) :
    (fun y => inflFn θ ε y - (1 - θ) * y) =o[nhds 0] fun y => y := by
  have h := (hasDerivAt_iff_isLittleO.1 (hasDerivAt_inflFn θ hε))
  simpa [inflFn_zero, mul_comm] using h


/-! ### The wage-index recursion in levels and the log-wage cross-section -/

/-- Galí (2015), p. 169: the wage-index recursion in relative form,
`(W_t/W_{t−1})^{1−ε} = θ + (1 − θ)(W*/W_{t−1})^{1−ε}`, is the book's level form
`W_t^{1−ε} = θ W_{t−1}^{1−ε} + (1 − θ)(W*)^{1−ε}`. -/
theorem recursion_levels_iff {θ ε Wt Wp Ws : ℝ} (hWt : 0 < Wt) (hWp : 0 < Wp) (hWs : 0 < Ws) :
    (Wt / Wp) ^ (1 - ε) = θ + (1 - θ) * (Ws / Wp) ^ (1 - ε) ↔
      Wt ^ (1 - ε) = θ * Wp ^ (1 - ε) + (1 - θ) * Ws ^ (1 - ε) := by
  have hp : 0 < Wp ^ (1 - ε) := Real.rpow_pos_of_pos hWp _
  rw [Real.div_rpow hWt.le hWp.le, Real.div_rpow hWs.le hWp.le]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp

/-- Galí (2015), p. 169 (**the CES wage-index recursion, level form**), derived from the
type-level Calvo model of `wage_recursion`: `W_t^{1−ε_w} = θ_w W_{t−1}^{1−ε_w} +
(1 − θ_w)(W*_t)^{1−ε_w}`. -/
theorem wage_index_recursion {F : Type*} [MeasurableSpace F] (m : Measure F) {ε θ : ℝ}
    (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1) {S : Set F} (hS : MeasurableSet S)
    {wprev wnow : F → ℝ} (hprev : Measurable wprev) (hnow : Measurable wnow) {Wstar : ℝ}
    (hWstar : 0 < Wstar) (hreset : ∀ i ∈ S, wnow i = Wstar)
    (hkeep : ∀ i ∉ S, wnow i = wprev i) (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map wprev = ENNReal.ofReal θ • m.map wprev)
    (hint : Integrable (fun i => wprev i ^ (1 - ε)) m)
    (hpos : 0 < ∫ i, wprev i ^ (1 - ε) ∂m) (hnowpos : 0 < cesIndex m ε wnow) :
    cesIndex m ε wnow ^ (1 - ε)
      = θ * cesIndex m ε wprev ^ (1 - ε) + (1 - θ) * Wstar ^ (1 - ε) :=
  (recursion_levels_iff hnowpos (cesIndex_pos hpos) hWstar).1
    (wage_recursion m hε h0 h1 hS hprev hnow hWstar hreset hkeep hmass hind hint hpos)

/-- Galí (2015), p. 169 and App. 6.1, p. 192 (**law of motion of the cross-section of log
wages**): under the type-level Calvo model, the distribution of log wages follows the
`wageMix` recursion `ν_t = θ_w ν_{t−1} + (1 − θ_w) δ_{w*_t}` used in the wage Lemma 2. The
representative-subsample hypothesis on wages implies it for log wages. -/
theorem log_wage_law_of_motion {F : Type*} [MeasurableSpace F] (m : Measure F) {θ : ℝ}
    {S : Set F} (hS : MeasurableSet S) {wprev wnow : F → ℝ} (hprev : Measurable wprev)
    (hnow : Measurable wnow) {Wstar : ℝ} (hreset : ∀ i ∈ S, wnow i = Wstar)
    (hkeep : ∀ i ∉ S, wnow i = wprev i) (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map wprev = ENNReal.ofReal θ • m.map wprev) :
    m.map (fun i => Real.log (wnow i))
      = wageMix θ (m.map (fun i => Real.log (wprev i))) (Real.log Wstar) := by
  have hlog : Measurable Real.log := Real.measurable_log
  have hind' : (m.restrict Sᶜ).map (fun i => Real.log (wprev i))
      = ENNReal.ofReal θ • m.map (fun i => Real.log (wprev i)) := by
    have e1 : (fun i => Real.log (wprev i)) = Real.log ∘ wprev := rfl
    rw [e1, ← Measure.map_map hlog hprev, ← Measure.map_map hlog hprev, hind,
      Measure.map_smul _ hlog.aemeasurable]
  exact wage_dist_law_of_motion m hS (hlog.comp hnow)
    (fun i hi => by simp only [Function.comp_apply, hreset i hi])
    (fun i hi => by simp only [Function.comp_apply, hkeep i hi]) hmass hind'

/-! ### Eq. (14) as the exact first-order approximation -/

/-- Galí (2015), p. 169: the wage-index recursion gives, exactly,
`log W_t = log W_{t−1} + f(log W*_t − log W_{t−1})` with `f = inflFn θ_w ε_w`. -/
theorem log_wageIndex_eq {θ ε Wt Wp Ws : ℝ} (hε : ε ≠ 1) (hWt : 0 < Wt) (hWp : 0 < Wp)
    (hWs : 0 < Ws) (hrec : Wt ^ (1 - ε) = θ * Wp ^ (1 - ε) + (1 - θ) * Ws ^ (1 - ε)) :
    Real.log Wt = Real.log Wp + inflFn θ ε (Real.log Ws - Real.log Wp) := by
  have h := log_infl_eq_inflFn hε (div_pos hWt hWp) (div_pos hWs hWp)
    ((recursion_levels_iff hWt hWp hWs).2 hrec)
  rw [Real.log_div hWt.ne' hWp.ne', Real.log_div hWs.ne' hWp.ne'] at h
  linarith

/-- Galí (2015), eq. (14), p. 169 (**exact linearisation**): `w*_t ↦ log W_t` has value `w_{t−1}`
and derivative `1 − θ_w` at the zero-wage-inflation point `w*_t = w_{t−1}`, and its tangent
line there is `w_t = θ_w w_{t−1} + (1 − θ_w) w*_t`, eq. (14). -/
theorem eq14_tangent (θ : ℝ) {ε : ℝ} (hε : ε ≠ 1) (wp : ℝ) :
    wp + inflFn θ ε (wp - wp) = wp ∧
      HasDerivAt (fun ws => wp + inflFn θ ε (ws - wp)) (1 - θ) wp ∧
      ∀ ws, wp + (1 - θ) * (ws - wp) = θ * wp + (1 - θ) * ws := by
  refine ⟨by rw [sub_self, inflFn_zero, add_zero], ?_, fun ws => by ring⟩
  have h1 : HasDerivAt (fun ws : ℝ => ws - wp) 1 wp := (hasDerivAt_id wp).sub_const wp
  have h2 : HasDerivAt (inflFn θ ε) (1 - θ) ((fun ws : ℝ => ws - wp) wp) := by
    simp only [sub_self]
    exact hasDerivAt_inflFn θ hε
  have h3 := (HasDerivAt.comp (h := fun ws : ℝ => ws - wp) wp h2 h1).const_add wp
  simpa using h3

/-- Galí (2015), eq. (14), p. 169: `w_t = θ_w w_{t−1} + (1 − θ_w) w*_t` iff
`π^w_t = (1 − θ_w)(w*_t − w_{t−1})`. -/
theorem eq14_iff (θ w wp ws : ℝ) :
    w = θ * wp + (1 - θ) * ws ↔ w - wp = (1 - θ) * (ws - wp) := by
  constructor <;> intro h <;> linarith

/-! ### The wage-inflation equation (15) -/

/-- Galí (2015), p. 170: `λ_w = (1 − θ_w)(1 − βθ_w)/(θ_w(1 + ε_wφ))`. -/
noncomputable def lambdaW (β θ ε φ : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / (θ * (1 + ε * φ))

/-- Galí (2015), p. 169: wage inflation `π^w_{t+1} = w_{t+1} − w_t` (dated `t + 1`). -/
noncomputable def wageInfl {Ω : Type*} (w : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := w (t + 1) - w t

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eqs. (13)–(15), pp. 169–170 (**(13) + (14) ⟺ (15)**): with
`0 < θ_w < 1`, `1 + ε_wφ ≠ 0`, an adapted (log) wage index `w` and the index recursion (14),
`w_{t+1} = θ_w w_t + (1 − θ_w) w*_{t+1}` at every date, the recursive wage-setting rule (13)
holds at every date `t + 1` **if and only if** the wage-inflation equation (15),
`π^w_{t+1} = β E_{t+1} π^w_{t+2} − λ_w μ̂^w_{t+1}`, does. -/
theorem eq15_iff {β θ ε φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hεφ : 1 + ε * φ ≠ 0)
    {wstar w μhat : ℕ → Ω → ℝ} (hwa : 𝔼.Adapted w)
    (h14 : ∀ t, w (t + 1) = θ • w t + (1 - θ) • wstar (t + 1)) :
    (∀ t, wstar (t + 1) = (β * θ) • 𝔼.E (t + 1) (wstar (t + 2)) +
        (1 - β * θ) • (w (t + 1) - (1 + ε * φ)⁻¹ • μhat (t + 1))) ↔
      ∀ t, wageInfl w t = β • 𝔼.E (t + 1) (wageInfl w (t + 1)) -
        lambdaW β θ ε φ • μhat (t + 1) := by
  have h1θ : (1 : ℝ) - θ ≠ 0 := by linarith
  have hθ : θ ≠ 0 := hθ0.ne'
  have hL : θ * lambdaW β θ ε φ = (1 - θ) * (1 - β * θ) * (1 + ε * φ)⁻¹ := by
    unfold lambdaW
    field_simp
  have hA : ∀ t ω, w (t + 1) ω = θ * w t ω + (1 - θ) * wstar (t + 1) ω := fun t ω => by
    have := congrFun (h14 t) ω
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have hB : ∀ t ω, 𝔼.E (t + 1) (w (t + 2)) ω
      = θ * w (t + 1) ω + (1 - θ) * 𝔼.E (t + 1) (wstar (t + 2)) ω := fun t ω => by
    have h' : w (t + 2) = θ • w (t + 1) + (1 - θ) • wstar (t + 2) := h14 (t + 1)
    rw [h', map_add, map_smul, map_smul, hwa (t + 1)]
    rfl
  have hEπ : ∀ t ω, 𝔼.E (t + 1) (wageInfl w (t + 1)) ω = 𝔼.E (t + 1) (w (t + 2)) ω -
      w (t + 1) ω := by
    intro t ω
    simp only [wageInfl, map_sub, hwa (t + 1), Pi.sub_apply]
  constructor
  · intro h13 t
    funext ω
    have E13 : wstar (t + 1) ω = β * θ * 𝔼.E (t + 1) (wstar (t + 2)) ω +
        (1 - β * θ) * (w (t + 1) ω - (1 + ε * φ)⁻¹ * μhat (t + 1) ω) := by
      have := congrFun (h13 t) ω
      simpa only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using this
    have hgoal : θ * (w (t + 1) ω - w t ω - (β * (𝔼.E (t + 1) (w (t + 2)) ω - w (t + 1) ω) -
        lambdaW β θ ε φ * μhat (t + 1) ω)) = 0 := by
      linear_combination (1 - θ) * E13 + hA t ω - β * θ * hB t ω + μhat (t + 1) ω * hL
    have hq := (mul_eq_zero.mp hgoal).resolve_left hθ
    change wageInfl w t ω = β * 𝔼.E (t + 1) (wageInfl w (t + 1)) ω -
      lambdaW β θ ε φ * μhat (t + 1) ω
    rw [hEπ t ω]
    simp only [wageInfl, Pi.sub_apply]
    linarith
  · intro h15 t
    funext ω
    have F15 : w (t + 1) ω - w t ω = β * (𝔼.E (t + 1) (w (t + 2)) ω - w (t + 1) ω) -
        lambdaW β θ ε φ * μhat (t + 1) ω := by
      have h := congrFun (h15 t) ω
      have e : (β • 𝔼.E (t + 1) (wageInfl w (t + 1)) - lambdaW β θ ε φ • μhat (t + 1)) ω
          = β * 𝔼.E (t + 1) (wageInfl w (t + 1)) ω - lambdaW β θ ε φ * μhat (t + 1) ω := rfl
      rw [e, hEπ t ω] at h
      simpa only [wageInfl, Pi.sub_apply] using h
    have hgoal : (1 - θ) * (wstar (t + 1) ω - (β * θ * 𝔼.E (t + 1) (wstar (t + 2)) ω +
        (1 - β * θ) * (w (t + 1) ω - (1 + ε * φ)⁻¹ * μhat (t + 1) ω))) = 0 := by
      linear_combination θ * F15 - μhat (t + 1) ω * hL - hA t ω + β * θ * hB t ω
    have hq := (mul_eq_zero.mp hgoal).resolve_left h1θ
    change wstar (t + 1) ω = β * θ * 𝔼.E (t + 1) (wstar (t + 2)) ω +
      (1 - β * θ) * (w (t + 1) ω - (1 + ε * φ)⁻¹ * μhat (t + 1) ω)
    linarith

/-- Galí (2015), p. 170 (**`λ_w > 0`**): for `0 < θ_w < 1`, `βθ_w < 1` and `1 + ε_wφ > 0`. -/
theorem lambdaW_pos {β θ ε φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hεφ : 0 < 1 + ε * φ) : 0 < lambdaW β θ ε φ := by
  unfold lambdaW
  have h1 : 0 < 1 - θ := by linarith
  have h2 : 0 < 1 - β * θ := by linarith
  positivity

/-- Galí (2015), p. 170 (`λ_w` and wage stickiness): for `0 ≤ β ≤ 1` and `1 + ε_wφ > 0`,
`λ_w` is strictly decreasing in `θ_w` on `(0, 1)`. -/
theorem lambdaW_strictAntiOn_theta {β ε φ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hεφ : 0 < 1 + ε * φ) : StrictAntiOn (fun θ => lambdaW β θ ε φ) (Set.Ioo 0 1) := by
  intro θ₁ h₁ θ₂ h₂ hlt
  simp only [lambdaW]
  have a1 : 0 < θ₁ := h₁.1
  have a2 : 0 < θ₂ := h₂.1
  have b2 : 0 < 1 - β * θ₂ := by nlinarith [h₂.2]
  have hB : 1 - β * θ₂ ≤ 1 - β * θ₁ := by nlinarith
  have hA : (1 - θ₂) / θ₂ < (1 - θ₁) / θ₁ := by
    rw [div_lt_div_iff₀ a2 a1]
    nlinarith
  have hA1 : 0 ≤ (1 - θ₁) / θ₁ := div_nonneg (by linarith [h₁.2]) a1.le
  have key : (1 - θ₂) / θ₂ * (1 - β * θ₂) < (1 - θ₁) / θ₁ * (1 - β * θ₁) :=
    calc (1 - θ₂) / θ₂ * (1 - β * θ₂) < (1 - θ₁) / θ₁ * (1 - β * θ₂) :=
          mul_lt_mul_of_pos_right hA b2
      _ ≤ (1 - θ₁) / θ₁ * (1 - β * θ₁) := mul_le_mul_of_nonneg_left hB hA1
  have e : ∀ θ : ℝ, θ ≠ 0 → (1 - θ) * (1 - β * θ) / (θ * (1 + ε * φ))
      = (1 - θ) / θ * (1 - β * θ) / (1 + ε * φ) := fun θ hθ => by
    field_simp
  rw [e θ₁ a1.ne', e θ₂ a2.ne']
  exact div_lt_div_of_pos_right key hεφ

/-- Galí (2015), p. 170: for `0 < θ_w < 1`, `βθ_w < 1` and `φ > 0`, `λ_w` is strictly
decreasing in the elasticity of substitution `ε_w ≥ 0`. -/
theorem lambdaW_strictAntiOn_eps {β θ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hφ : 0 < φ) : StrictAntiOn (fun ε => lambdaW β θ ε φ) (Set.Ici 0) := by
  intro ε₁ h₁ ε₂ h₂ hlt
  simp only [lambdaW]
  have hK : 0 < (1 - θ) * (1 - β * θ) := mul_pos (by linarith) (by linarith)
  have hd1 : 0 < θ * (1 + ε₁ * φ) := mul_pos hθ0 (by nlinarith [Set.mem_Ici.mp h₁])
  have hlt' : θ * (1 + ε₁ * φ) < θ * (1 + ε₂ * φ) :=
    mul_lt_mul_of_pos_left (by nlinarith) hθ0
  exact div_lt_div_of_pos_left hK hd1 hlt'

/-- Galí (2015), p. 170: for `0 < θ_w < 1`, `βθ_w < 1` and `ε_w > 0`, `λ_w` is strictly
decreasing in the inverse Frisch elasticity `φ ≥ 0`. -/
theorem lambdaW_strictAntiOn_phi {β θ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hε : 0 < ε) : StrictAntiOn (fun φ => lambdaW β θ ε φ) (Set.Ici 0) := by
  intro φ₁ h₁ φ₂ h₂ hlt
  simp only [lambdaW]
  have hK : 0 < (1 - θ) * (1 - β * θ) := mul_pos (by linarith) (by linarith)
  have hd1 : 0 < θ * (1 + ε * φ₁) := mul_pos hθ0 (by nlinarith [Set.mem_Ici.mp h₁])
  have hlt' : θ * (1 + ε * φ₁) < θ * (1 + ε * φ₂) :=
    mul_lt_mul_of_pos_left (by nlinarith) hθ0
  exact div_lt_div_of_pos_left hK hd1 hlt'

end Gali.StickyWagesPrices.WageInflation
