/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.Calvo
import NominalRigidities.FlexiblePrices
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Staggered wage setting: the nonlinear model and its log-linearisation

Woodford (2003), *Interest and Prices*, Chapter 3, §4.1 "A Model of Staggered Wagesetting",
pp. 221–224, eqs. (4.1)–(4.7) (following Erceg, Henderson and Levin 2000).

Notation. `θ` is the elasticity of substitution `θ_w > 1` among labour types (the book's
`θ_w`), `α` the Calvo probability `α_w` that a wage is *not* reset in a period, `β` the discount
factor, `μ_w = θ/(θ − 1)` the desired wage markup (`markup θ`). Processes that enter the reset
problem of date `t` are indexed by the horizon `k` (date `T = t + k`); expectations are an
arbitrary `ExpectationSystem`, so everything holds under perfect foresight and under
uncertainty.

The CES labour aggregate and wage index are those of `DixitStiglitz`, and the Calvo law of
motion of the wage distribution, the lottery model and differentiation under `E_t` and under an
infinite discounted sum are those of `Calvo` (one generic statement, instantiated here for
wages). The remaining machinery (necessity and, with convex costs, sufficiency and uniqueness of
the reset first-order condition; the exact first-order approximations) is **restated from the
Galí Chapter 6 project** (`WageSetting`, `WageInflation`), with Galí's `ε_w, θ_w` renamed to
Woodford's `θ_w, α_w` and the citations replaced by the corresponding places in Woodford's §4.1;
`objective_eq_resetObjective` identifies its reset objective with `Calvo.resetObjective` (2.2).

## Main results

* `Labor.cost_min_iff`, `Labor.unitInterval_cost_minimisation`: with the CES aggregate (4.1),
  the labour-demand schedule (4.2) `h(j) = H (w(j)/W)^{−θ_w}` is the **unique** cost-minimising
  bundle (a.e.), it delivers `H` and costs `W H` (`Labor.laborIndex_demand`,
  `Labor.wageBill_demand`).
* `Index.wage_index_recursion`, `Index.wage_recursion_lottery`: the Calvo law of motion of the
  wage distribution gives the CES wage-index recursion
  `W_t^{1−θ} = α W_{t−1}^{1−θ} + (1 − α) w*_t^{1−θ}` (analogue of (2.1)); for an explicit
  Calvo lottery; `Index.dist_k_step`: a wage set at `t` is still in force at `t + k` with
  probability `αᵏ` (the weights of (4.3)).
* `Index.index_tangent`, `Index.hasDerivAt_inflFn`: **(4.6)** is the exact first-order
  approximation of the index recursion.
* `wageObjective`, `wageObjective_eq`: the wage-setting objective (4.3) is an instance of the
  generic Calvo reset objective; `eq44_iff_focSum`: the first-order condition (4.4) (with the
  stochastic discount factor `Q_{t,T}`); `wage_isMaxOn_iff_foc`: **(4.4) is necessary and
  sufficient** for the optimal wage, which is the unique (strict) maximiser, whenever the
  disutility of work is convex; `mrs_nominal_eq`: (4.5).
* `Primitives`, `lipschitz_of_primitives`, `dominated_of_primitives`,
  `summable_profit_of_primitives`, `isMaxOn_iff_foc_of_primitives` (restated from Galí Ch. 6),
  `wage_primitives`, `wage_isMaxOn_iff_foc_of_primitives`: the regularity hypotheses of
  `wage_isMaxOn_iff_foc` follow from primitive bounds (marginal utility of income in
  `[m_Λ, M_Λ]`, wage index and hours in `[m, M̄]`, convex `v` with `v, v_h, v_hh` bounded on
  compact ranges of positive hours).
* `priceObjective`, `priceObjective_eq`, `hasDerivAt_priceCost`, `priceMC_monotoneOn`,
  `price_isMaxOn_iff_foc`, `hasDerivAt_log_mc`, `price_reset_rule_of_linearisation`: the Calvo
  price setter with an economy-wide labour market (behind (4.9)) as an instance of the same
  generic problem, its first-order condition necessary and sufficient, and its exact
  linearisation with own-output elasticity `ω_p`.
* `wage_flexible_iff`: with `α_w = 0` the optimal wage is `μ_w V_t P_t`;
  `wage_steadyState_iff`: at the steady state `w̄ = μ_w v̄`.
* `indexed_profit_eq`: indexation of non-reset wages (p. 234) is again an instance of the
  generic problem, so all of the above applies to it.
* `log_demand_sub`, `hasDerivAt_log_vh`: the log MRS of a type is `log v_t + ν log(h(j)/H)`
  to first order with `ν = h̄ v_hh / v_h` and `log(h(j)/H) = −θ_w log(w(j)/W)` exactly.
* `reset_rule_iff`, `eq47_of_linearisation`: **(4.7)** is exactly the vanishing of the first-order
  term of (4.4) at the steady state (`linear_reset_rule_iff`, `hasDerivAt_focLHS_path`), once
  the own-hours effect on the MRS is substituted. The same theorem with `(ν, θ_w)` replaced
  by `(ω_p, θ_p)` is the price-setting rule behind (4.9).
-/

namespace Woodford.NominalRigidities.WageSetting

open Filter Topology MeasureTheory

/-! ### The labour aggregate (4.1) and labour demand (4.2)

The labour index (4.1), the wage index and the labour-demand schedule (4.2) are the
Dixit–Stiglitz objects `DixitStiglitz.cesAgg`, `DixitStiglitz.priceIndex` and
`DixitStiglitz.demand` on a measure space of labour types, and their properties are those of
`DixitStiglitz`; the book-facing statements of pp. 221–222 are restated here from that module. -/

namespace Labor

open DixitStiglitz

variable {J : Type*} [MeasurableSpace J] {μ : Measure J} {θ : ℝ} {W : J → ℝ}

/-- Woodford (2003), eq. (4.2), p. 221: the labour-demand schedule `N(j) = (W(j)/W)^{−θ} N`
delivers exactly the aggregate `N` (restated from `DixitStiglitz.cesAgg_demand`). -/
theorem laborIndex_demand (hθ : 1 < θ) (hW : ∀ j, 0 < W j) (hpos : 0 < ∫ j, W j ^ (1 - θ) ∂μ)
    {N : ℝ} (hN : 0 ≤ N) : cesAgg μ θ (demand μ θ W N) = N :=
  cesAgg_demand hθ hW hpos hN

/-- Woodford (2003), (4.2): under the labour-demand schedule, the wage bill is
`∫ W(j) N(j) di = W N` (restated from `DixitStiglitz.spend_demand`). -/
theorem wageBill_demand (hθ : 1 < θ) (hW : ∀ j, 0 < W j) (hpos : 0 < ∫ j, W j ^ (1 - θ) ∂μ)
    (N : ℝ) : ∫ j, W j * demand μ θ W N j ∂μ = priceIndex μ θ W * N :=
  spend_demand hθ hW hpos N

/-- Woodford (2003), eqs. (4.1)–(4.2), pp. 221–222, on the book's **continuum of labour types
`[0, 1]` with Lebesgue measure**: (i) every bundle `N(·) ≥ 0` costs at least `W · N`;
(ii) it costs exactly `W · N` iff `N(j) = (W(j)/W)^{−θ} N` for a.e. `j ∈ [0, 1]`;
(iii) the labour-demand schedule attains any aggregate `N ≥ 0`; (iv) it costs `W N`
(restated from `DixitStiglitz.unitInterval_expenditure_minimisation`). -/
theorem unitInterval_cost_minimisation (hθ : 1 < θ) {Q : ℝ → ℝ} (hQ : ∀ j, 0 < Q j)
    (hQi : IntegrableOn (fun j => Q j ^ (1 - θ)) (Set.Icc 0 1)) {n : ℝ → ℝ}
    (hn : ∀ j, 0 ≤ n j) (hQc : IntegrableOn (fun j => Q j * n j) (Set.Icc 0 1)) :
    priceIndex (volume.restrict (Set.Icc 0 1)) θ Q * cesAgg (volume.restrict (Set.Icc 0 1)) θ n
        ≤ ∫ j in Set.Icc 0 1, Q j * n j ∧
      (∫ j in Set.Icc 0 1, Q j * n j
          = priceIndex (volume.restrict (Set.Icc 0 1)) θ Q *
            cesAgg (volume.restrict (Set.Icc 0 1)) θ n ↔
        ∀ᵐ j ∂(volume.restrict (Set.Icc 0 1)),
          n j = demand (volume.restrict (Set.Icc 0 1)) θ Q
            (cesAgg (volume.restrict (Set.Icc 0 1)) θ n) j) ∧
      (∀ N : ℝ, 0 ≤ N → cesAgg (volume.restrict (Set.Icc 0 1)) θ
        (demand (volume.restrict (Set.Icc 0 1)) θ Q N) = N) ∧
      ∀ N : ℝ, ∫ j in Set.Icc 0 1, Q j * demand (volume.restrict (Set.Icc 0 1)) θ Q N j
        = priceIndex (volume.restrict (Set.Icc 0 1)) θ Q * N :=
  unitInterval_expenditure_minimisation hθ hQ hQi hn hQc

/-! ### Labour demand (4.2) is the unique cost minimiser -/

/-- Woodford (2003), eq. (4.2), p. 221: the labour-demand schedule is a feasible bundle: it is
nonnegative and its wage bill is integrable. -/
theorem laborDemand_feasible (hW : ∀ j, 0 < W j) (hWi : Integrable (fun j => W j ^ (1 - θ)) μ)
    (hpos : 0 < ∫ j, W j ^ (1 - θ) ∂μ) {N : ℝ} (hN : 0 ≤ N) :
    (∀ j, 0 ≤ demand μ θ W N j) ∧ Integrable (fun j => W j * demand μ θ W N j) μ :=
  ⟨demand_nonneg hW hpos hN, integrable_spend_demand hW hWi hpos N⟩

/-- Woodford (2003), eq. (4.2), p. 221 (**labour demand is the unique cost minimiser**): a firm that
needs the labour index `N ≥ 0` and uses a bundle `n(·) ≥ 0` with `N(n) = N` minimises its wage
bill `∫ W(j) n(j) dj` over all such bundles **if and only if** `n(j) = (W(j)/W)^{−θ_w} N` for
almost every `j`. -/
theorem cost_min_iff (hθ : 1 < θ) (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - θ)) μ) (hpos : 0 < ∫ j, W j ^ (1 - θ) ∂μ)
    {N : ℝ} (hN : 0 ≤ N) {n : J → ℝ} (hn : ∀ j, 0 ≤ n j)
    (hWn : Integrable (fun j => W j * n j) μ) (hnN : cesAgg μ θ n = N) :
    (∀ m : J → ℝ, (∀ j, 0 ≤ m j) → Integrable (fun j => W j * m j) μ →
        cesAgg μ θ m = N → ∫ j, W j * n j ∂μ ≤ ∫ j, W j * m j ∂μ) ↔
      n =ᵐ[μ] demand μ θ W N := by
  obtain ⟨hd0, hdi⟩ := laborDemand_feasible hW hWi hpos hN
  constructor
  · intro hmin
    have h1 := hmin _ hd0 hdi (laborIndex_demand hθ hW hpos hN)
    rw [wageBill_demand hθ hW hpos N] at h1
    have h2 := spend_ge hθ hW hWi hpos hn hWn
    rw [hnN] at h2
    have heq : ∫ j, W j * n j ∂μ = priceIndex μ θ W * cesAgg μ θ n := by
      rw [hnN]
      linarith
    have := (spend_eq_iff hθ hW hWi hpos hn hWn).1 heq
    rwa [hnN] at this
  · intro hae m hm hWm hmN
    have hc : ∫ j, W j * n j ∂μ = priceIndex μ θ W * N := by
      rw [← wageBill_demand hθ hW hpos N]
      refine integral_congr_ae ?_
      filter_upwards [hae] with j hj
      rw [hj]
    rw [hc, ← hmN]
    exact spend_ge hθ hW hWi hpos hm hWm

end Labor

/-! ### The Calvo law of motion of the wage index (restated from Galí Ch. 6) -/

namespace Index

open DixitStiglitz (priceIndex priceIndex_pos priceIndex_rpow integral_pos_of_pos)
open Calvo (integral_calvo_mix dist_law_of_motion lottery_model calvo_index_rpow)

/-- Woodford (2003), the CES wage index of p. 222, at the level of wage distributions: if
`ν_t = α ν_{t−1} + (1 − α) δ_{W*}`, where `ν_{t−1}` has a positive, integrable
`∫ p^{1−θ}`, then with `W_s = (∫ p^{1−θ} dν_s)^{1/(1−θ)}`,
`(W_t/W_{t−1})^{1−θ} = α + (1 − α)(W*/W_{t−1})^{1−θ}`. -/
theorem wage_recursion_of_dist {θ α : ℝ} (hθ : 1 < θ) (h0 : 0 ≤ α) (h1 : α < 1)
    {νprev : Measure ℝ} {Wstar : ℝ} (hWstar : 0 < Wstar)
    (hint : Integrable (fun x : ℝ => x ^ (1 - θ)) νprev)
    (hpos : 0 < ∫ x, x ^ (1 - θ) ∂νprev) :
    (priceIndex (ENNReal.ofReal α • νprev + ENNReal.ofReal (1 - α) • Measure.dirac Wstar) θ
        (fun x => x) / priceIndex νprev θ (fun x => x)) ^ (1 - θ)
      = α + (1 - α) * (Wstar / priceIndex νprev θ (fun x => x)) ^ (1 - θ) := by
  have hmix := integral_calvo_mix h0 h1.le Wstar hint
  have hnew : 0 < α * ∫ x, x ^ (1 - θ) ∂νprev + (1 - α) * Wstar ^ (1 - θ) := by
    have : 0 < (1 - α) * Wstar ^ (1 - θ) :=
      mul_pos (by linarith) (Real.rpow_pos_of_pos hWstar _)
    have : 0 ≤ α * ∫ x, x ^ (1 - θ) ∂νprev := mul_nonneg h0 hpos.le
    linarith
  have hI := priceIndex_pos (P := fun x : ℝ => x) hpos
  have hsub : (1 : ℝ) - θ ≠ 0 := by linarith
  have hPt : priceIndex (ENNReal.ofReal α • νprev + ENNReal.ofReal (1 - α) • Measure.dirac Wstar)
      θ (fun x => x) ^ (1 - θ) = α * ∫ x, x ^ (1 - θ) ∂νprev + (1 - α) * Wstar ^ (1 - θ) := by
    unfold priceIndex
    rw [hmix, Real.rpow_inv_rpow hnew.le hsub]
  have hPt0 : 0 ≤ priceIndex (ENNReal.ofReal α • νprev + ENNReal.ofReal (1 - α) •
      Measure.dirac Wstar) θ (fun x => x) := by
    unfold priceIndex
    rw [hmix]
    exact Real.rpow_nonneg hnew.le _
  rw [Real.div_rpow hPt0 hI.le, Real.div_rpow hWstar.le hI.le, hPt,
    priceIndex_rpow (P := fun x : ℝ => x) hθ hpos]
  field_simp

/-- Woodford (2003), the wage-index law of motion, p. 223 (**Calvo wage-index recursion**),
derived from the type-level model of `dist_law_of_motion`: with `W_s` the CES wage index of
the cross-section `p_s`, `(W_t/W_{t−1})^{1−θ} = α + (1 − α)(W*_t/W_{t−1})^{1−θ}`. -/
theorem wage_recursion {F : Type*} [MeasurableSpace F] (m : Measure F) {θ α : ℝ}
    (hθ : 1 < θ) (h0 : 0 ≤ α) (h1 : α < 1) {S : Set F} (hS : MeasurableSet S)
    {pprev pnow : F → ℝ} (hprev : Measurable pprev) (hnow : Measurable pnow) {Wstar : ℝ}
    (hWstar : 0 < Wstar) (hreset : ∀ i ∈ S, pnow i = Wstar)
    (hkeep : ∀ i ∉ S, pnow i = pprev i) (hmass : m S = ENNReal.ofReal (1 - α))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal α • m.map pprev)
    (hint : Integrable (fun i => pprev i ^ (1 - θ)) m)
    (hpos : 0 < ∫ i, pprev i ^ (1 - θ) ∂m) :
    (priceIndex m θ pnow / priceIndex m θ pprev) ^ (1 - θ)
      = α + (1 - α) * (Wstar / priceIndex m θ pprev) ^ (1 - θ) := by
  have hmeas : Measurable fun x : ℝ => x ^ (1 - θ) := measurable_id.pow_const _
  have hmap : ∀ p : F → ℝ, Measurable p →
      ∫ i, p i ^ (1 - θ) ∂m = ∫ x, x ^ (1 - θ) ∂(m.map p) := fun p hp =>
    (integral_map hp.aemeasurable hmeas.aestronglyMeasurable).symm
  have hidx : ∀ p : F → ℝ, Measurable p →
      priceIndex m θ p = priceIndex (m.map p) θ (fun x => x) := fun p hp => by
    unfold priceIndex
    rw [hmap p hp]
  have hint' : Integrable (fun x : ℝ => x ^ (1 - θ)) (m.map pprev) :=
    (integrable_map_measure hmeas.aestronglyMeasurable hprev.aemeasurable).2 hint
  rw [hidx pnow hnow, hidx pprev hprev, dist_law_of_motion m hS hnow hreset hkeep hmass hind]
  rw [hmap pprev hprev] at hpos
  exact wage_recursion_of_dist hθ h0 h1 hWstar hint' hpos

/-- Woodford (2003), the wage-index law of motion, p. 223, for the **explicit Calvo-lottery
economy** of `lottery_model`: labour types `(ω, u) ∈ Ω × [0, 1]`, last period's wage `w ω`, and
this period's wage `W*` if `u > α` and `w ω` otherwise. With `W_{t−1}` the index of `w`
under `μ₀`, `(W_t/W_{t−1})^{1−θ} = α + (1 − α)(W*/W_{t−1})^{1−θ}`. -/
theorem wage_recursion_lottery {Ω : Type*} [MeasurableSpace Ω] (μ₀ : Measure Ω)
    [IsProbabilityMeasure μ₀] {θ α : ℝ} (hθ : 1 < θ) (h0 : 0 ≤ α) (h1 : α < 1) {p : Ω → ℝ}
    (hp : Measurable p) (hp0 : ∀ ω, 0 < p ω) (hint : Integrable (fun ω => p ω ^ (1 - θ)) μ₀)
    {Wstar : ℝ} (hWstar : 0 < Wstar) :
    (priceIndex (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) θ
        (fun x => if α < x.2 then Wstar else p x.1) / priceIndex μ₀ θ p) ^ (1 - θ)
      = α + (1 - α) * (Wstar / priceIndex μ₀ θ p) ^ (1 - θ) := by
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
  have hnow : Measurable fun x : Ω × ℝ => if α < x.2 then Wstar else p x.1 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const hpp
  rw [← hidx]
  refine wage_recursion _ hθ h0 h1 hS hpp hnow hWstar ?_ ?_ hmass hind hint'
    (by rw [hI]; exact hpos)
  · intro x hx
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hx
    simp only [hx, ↓reduceIte]
  · intro x hx
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hx
    simp only [hx, ↓reduceIte]

/-- Woodford (2003), p. 222 (**decomposition by date of last reset**): if the wage
distribution follows `ν_{s+1} = α ν_s + (1 − α) δ_{W*_{s+1}}`, then
`ν_{t+k} = αᵏ ν_t + ∑_{h=1}^{k} (1 − α) α^{k−h} δ_{W*_{t+h}}` (written with `h ↦ h + 1`): a
mass `αᵏ` still charges the wages of date `t`, and a mass `(1 − α)α^{k−h}` last reset at
`t + h`. -/
theorem dist_k_step {α : ℝ} (h0 : 0 ≤ α) {ν : ℕ → Measure ℝ} {Wstar : ℕ → ℝ}
    (hlaw : ∀ t, ν (t + 1)
      = ENNReal.ofReal α • ν t + ENNReal.ofReal (1 - α) • Measure.dirac (Wstar (t + 1)))
    (t k : ℕ) :
    ν (t + k) = ENNReal.ofReal (α ^ k) • ν t + ∑ h ∈ Finset.range k,
      ENNReal.ofReal ((1 - α) * α ^ (k - 1 - h)) • Measure.dirac (Wstar (t + h + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, hlaw, ih, smul_add, Finset.smul_sum, smul_smul, Finset.sum_range_succ]
    simp_rw [smul_smul]
    have hc : ∀ h ∈ Finset.range k, ENNReal.ofReal α * ENNReal.ofReal ((1 - α) * α ^ (k - 1 - h))
        = ENNReal.ofReal ((1 - α) * α ^ (k + 1 - 1 - h)) := by
      intro h hh
      rw [Finset.mem_range] at hh
      rw [← ENNReal.ofReal_mul h0]
      congr 1
      rw [show k + 1 - 1 - h = (k - 1 - h) + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl fun h hh => by rw [hc h hh], ← ENNReal.ofReal_mul h0, ← pow_succ',
      show k + 1 - 1 - k = 0 by omega, pow_zero, mul_one, add_assoc]

/-- Woodford (2003), p. 222: the probabilities in (4.3) sum to one,
`αᵏ + (1 − α) ∑_{h=1}^{k} α^{k−h} = 1`. -/
theorem prob_identity (α : ℝ) (k : ℕ) :
    α ^ k + (1 - α) * ∑ h ∈ Finset.Icc 1 k, α ^ (k - h) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero]
    have hs : ∑ h ∈ Finset.Icc 1 k, α ^ (k + 1 - h) = α * ∑ h ∈ Finset.Icc 1 k, α ^ (k - h) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [Finset.mem_Icc] at hh
      rw [show k + 1 - h = (k - h) + 1 by omega, pow_succ]
      ring
    rw [hs]
    linear_combination α * ih

/-- Woodford (2003), p. 222: if `ν_t` is a probability distribution, so is `ν_{t+k}`;
the masses of `dist_k_step` add up to one. -/
theorem dist_k_step_mass {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {ν : ℕ → Measure ℝ}
    {Wstar : ℕ → ℝ}
    (hlaw : ∀ t, ν (t + 1)
      = ENNReal.ofReal α • ν t + ENNReal.ofReal (1 - α) • Measure.dirac (Wstar (t + 1)))
    (t k : ℕ) (hν : ν t Set.univ = 1) : ν (t + k) Set.univ = 1 := by
  have hnn : ∀ h ∈ Finset.range k, 0 ≤ (1 - α) * α ^ (k - 1 - h) :=
    fun h _ => mul_nonneg (by linarith) (pow_nonneg h0 _)
  rw [dist_k_step h0 hlaw t k]
  simp only [Measure.coe_add, Measure.coe_smul, Measure.coe_finsetSum, Pi.add_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, measure_univ, hν, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← ENNReal.ofReal_add (pow_nonneg h0 _)
    (Finset.sum_nonneg hnn), Calvo.cohort_weights_sum, ENNReal.ofReal_one]

/-- Woodford (2003), p. 223: a positive number `y` satisfies `y^{1−θ} = 1` iff `y = 1` (`θ ≠ 1`). -/
theorem rpow_eq_one_iff {θ y : ℝ} (hθ : θ ≠ 1) (hy : 0 < y) : y ^ (1 - θ) = 1 ↔ y = 1 := by
  constructor
  · intro h
    have hsub : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
    rw [← Real.rpow_rpow_inv hy.le hsub, h, Real.one_rpow]
  · rintro rfl
    exact Real.one_rpow _

/-- Woodford (2003), p. 223 (**zero-wage-inflation steady state**): under the wage-index recursion,
gross wage inflation is one
iff the reset wage equals last period's wage index, `Π = 1 ⟺ W*/W_{t−1} = 1`
(`0 ≤ α < 1`, `θ ≠ 1`). -/
theorem zero_wage_inflation_iff {α θ Pi x : ℝ} (h1 : α < 1) (hθ : θ ≠ 1) (hPi : 0 < Pi)
    (hx : 0 < x) (hrec : Pi ^ (1 - θ) = α + (1 - α) * x ^ (1 - θ)) : Pi = 1 ↔ x = 1 := by
  rw [← rpow_eq_one_iff hθ hPi, ← rpow_eq_one_iff hθ hx, hrec]
  have : (1 : ℝ) - α ≠ 0 := by linarith
  constructor
  · intro h
    have h' : (1 - α) * x ^ (1 - θ) = (1 - α) * 1 := by linarith
    exact mul_left_cancel₀ this h'
  · intro h
    rw [h]
    ring

/-- Woodford (2003), p. 223, in levels: under the wage-index recursion, `W_t = W_{t−1}` iff
`W*_t = W_{t−1}`, and then
`W*_t = W_{t−1} = W_t`. -/
theorem zero_wage_inflation_levels {α θ Pt Pprev Wstar : ℝ} (h1 : α < 1) (hθ : θ ≠ 1)
    (hPt : 0 < Pt) (hPprev : 0 < Pprev) (hWstar : 0 < Wstar)
    (hrec : (Pt / Pprev) ^ (1 - θ) = α + (1 - α) * (Wstar / Pprev) ^ (1 - θ)) :
    (Pt = Pprev ↔ Wstar = Pprev) ∧ (Pt = Pprev → Wstar = Pprev ∧ Wstar = Pt) := by
  have h := zero_wage_inflation_iff h1 hθ (div_pos hPt hPprev) (div_pos hWstar hPprev) hrec
  rw [div_eq_one_iff_eq hPprev.ne', div_eq_one_iff_eq hPprev.ne'] at h
  exact ⟨h, fun he => ⟨h.1 he, (h.1 he).trans he.symm⟩⟩
/-- Woodford (2003), (4.6): log gross wage inflation as a function of the log relative reset
wage `y = log(W*_t/W_{t−1})`, as implied by (7):
`π(y) = (1 − θ)⁻¹ log(α + (1 − α) e^{(1−θ) y})`. -/
noncomputable def inflFn (α θ y : ℝ) : ℝ :=
  (1 - θ)⁻¹ * Real.log (α + (1 - α) * Real.exp ((1 - θ) * y))

/-- Woodford (2003), eq. (4.6), p. 223: the exact (nonlinear) wage-index recursion says
`log Π_t = inflFn α θ (log(W*_t/W_{t−1}))`. -/
theorem log_infl_eq_inflFn {α θ Pi x : ℝ} (hθ : θ ≠ 1) (hPi : 0 < Pi) (hx : 0 < x)
    (hrec : Pi ^ (1 - θ) = α + (1 - α) * x ^ (1 - θ)) :
    Real.log Pi = inflFn α θ (Real.log x) := by
  have hsub : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have h := congrArg Real.log hrec
  rw [Real.log_rpow hPi, Real.rpow_def_of_pos hx, mul_comm (Real.log x)] at h
  rw [inflFn, ← h]
  field_simp

/-- Woodford (2003), p. 223: at the zero-wage-inflation steady state (`W* = W_{t−1}`, i.e. `y = 0`),
`π = 0`. -/
theorem inflFn_zero (α θ : ℝ) : inflFn α θ 0 = 0 := by
  simp [inflFn]

/-- Woodford (2003), (4.6) (**exact derivative**): `d log Π_t / d log(W*_t/W_{t−1}) = 1 − α`
at the zero-wage-inflation steady state; i.e. `π_t = (1 − α)(p*_t − p_{t−1})` is the first-order
approximation of (7). -/
theorem hasDerivAt_inflFn (α : ℝ) {θ : ℝ} (hθ : θ ≠ 1) : HasDerivAt (inflFn α θ) (1 - α) 0 := by
  have hsub : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have h1 : HasDerivAt (fun y : ℝ => (1 - θ) * y) (1 - θ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (1 - θ)
  have h2 := HasDerivAt.exp h1
  have h3 := HasDerivAt.const_add α (HasDerivAt.const_mul (1 - α) h2)
  have hne : α + (1 - α) * Real.exp ((1 - θ) * 0) ≠ 0 := by simp
  have h4 := HasDerivAt.const_mul (1 - θ)⁻¹ (HasDerivAt.log h3 hne)
  unfold inflFn
  convert h4 using 1
  simp only [mul_zero, Real.exp_zero, mul_one]
  field_simp
  ring

/-- Woodford (2003), eq. (4.6), p. 223: the remainder of the log-linear approximation is
`o(y)`, `inflFn α θ y − (1 − α) y = o(y)` as `y → 0`. -/
theorem inflFn_isLittleO (α : ℝ) {θ : ℝ} (hθ : θ ≠ 1) :
    (fun y => inflFn α θ y - (1 - α) * y) =o[nhds 0] fun y => y := by
  have h := (hasDerivAt_iff_isLittleO.1 (hasDerivAt_inflFn α hθ))
  simpa [inflFn_zero, mul_comm] using h


/-! ### The wage-index recursion in levels and the log-wage cross-section -/

/-- Woodford (2003), p. 223: the wage-index recursion in relative form,
`(W_t/W_{t−1})^{1−θ} = α + (1 − α)(W*/W_{t−1})^{1−θ}`, is the book's level form
`W_t^{1−θ} = α W_{t−1}^{1−θ} + (1 − α)(W*)^{1−θ}`. -/
theorem recursion_levels_iff {α θ Wt Wp Ws : ℝ} (hWt : 0 < Wt) (hWp : 0 < Wp) (hWs : 0 < Ws) :
    (Wt / Wp) ^ (1 - θ) = α + (1 - α) * (Ws / Wp) ^ (1 - θ) ↔
      Wt ^ (1 - θ) = α * Wp ^ (1 - θ) + (1 - α) * Ws ^ (1 - θ) := by
  have hp : 0 < Wp ^ (1 - θ) := Real.rpow_pos_of_pos hWp _
  rw [Real.div_rpow hWt.le hWp.le, Real.div_rpow hWs.le hWp.le]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp

/-- Woodford (2003), p. 223 (**the CES wage-index recursion, level form**): the instance for wages
of the generic Calvo index recursion `Calvo.calvo_index_rpow` (eq. (2.1)):
`W_t^{1−θ_w} = α_w W_{t−1}^{1−θ_w} + (1 − α_w)(W*_t)^{1−θ_w}`. -/
theorem wage_index_recursion {F : Type*} [MeasurableSpace F] (m : Measure F) {θ α : ℝ}
    (hθ : 1 < θ) (h0 : 0 ≤ α) (h1 : α < 1) {S : Set F} (hS : MeasurableSet S)
    {wprev wnow : F → ℝ} (hprev : Measurable wprev) (hnow : Measurable wnow) {Wstar : ℝ}
    (hWstar : 0 < Wstar) (hreset : ∀ i ∈ S, wnow i = Wstar)
    (hkeep : ∀ i ∉ S, wnow i = wprev i) (hmass : m S = ENNReal.ofReal (1 - α))
    (hind : (m.restrict Sᶜ).map wprev = ENNReal.ofReal α • m.map wprev)
    (hint : Integrable (fun i => wprev i ^ (1 - θ)) m)
    (hpos : 0 < ∫ i, wprev i ^ (1 - θ) ∂m) :
    priceIndex m θ wnow ^ (1 - θ)
      = α * priceIndex m θ wprev ^ (1 - θ) + (1 - α) * Wstar ^ (1 - θ) := by
  rw [calvo_index_rpow m hθ.ne' h0 h1 hS hprev hnow hWstar hreset hkeep hmass hind hint hpos]
  ring

/-! ### Eq. (4.6) as the exact first-order approximation -/

/-- Woodford (2003), p. 223: the wage-index recursion gives, exactly,
`log W_t = log W_{t−1} + f(log W*_t − log W_{t−1})` with `f = inflFn α_w θ_w`. -/
theorem log_wageIndex_eq {α θ Wt Wp Ws : ℝ} (hθ : θ ≠ 1) (hWt : 0 < Wt) (hWp : 0 < Wp)
    (hWs : 0 < Ws) (hrec : Wt ^ (1 - θ) = α * Wp ^ (1 - θ) + (1 - α) * Ws ^ (1 - θ)) :
    Real.log Wt = Real.log Wp + inflFn α θ (Real.log Ws - Real.log Wp) := by
  have h := log_infl_eq_inflFn hθ (div_pos hWt hWp) (div_pos hWs hWp)
    ((recursion_levels_iff hWt hWp hWs).2 hrec)
  rw [Real.log_div hWt.ne' hWp.ne', Real.log_div hWs.ne' hWp.ne'] at h
  linarith

/-- Woodford (2003), (4.6) (**exact linearisation**): `w*_t ↦ log W_t` has value `w_{t−1}`
and derivative `1 − α_w` at the zero-wage-inflation point `w*_t = w_{t−1}`, and its tangent
line there is `w_t = α_w w_{t−1} + (1 − α_w) w*_t`, eq. (4.6). -/
theorem index_tangent (α : ℝ) {θ : ℝ} (hθ : θ ≠ 1) (wp : ℝ) :
    wp + inflFn α θ (wp - wp) = wp ∧
      HasDerivAt (fun ws => wp + inflFn α θ (ws - wp)) (1 - α) wp ∧
      ∀ ws, wp + (1 - α) * (ws - wp) = α * wp + (1 - α) * ws := by
  refine ⟨by rw [sub_self, inflFn_zero, add_zero], ?_, fun ws => by ring⟩
  have h1 : HasDerivAt (fun ws : ℝ => ws - wp) 1 wp := (hasDerivAt_id wp).sub_const wp
  have h2 : HasDerivAt (inflFn α θ) (1 - α) ((fun ws : ℝ => ws - wp) wp) := by
    simp only [sub_self]
    exact hasDerivAt_inflFn α hθ
  have h3 := (HasDerivAt.comp (h := fun ws : ℝ => ws - wp) wp h2 h1).const_add wp
  simpa using h3

/-- Woodford (2003), eq. (4.6), p. 223: `w_t = α_w w_{t−1} + (1 − α_w) w*_t` iff
`π^w_t = (1 − α_w)(w*_t − w_{t−1})`. -/
theorem index_law_iff (α w wp ws : ℝ) :
    w = α * wp + (1 - α) * ws ↔ w - wp = (1 - α) * (ws - wp) := by
  constructor <;> intro h <;> linarith

end Index

/-! ### The generic Calvo reset problem (restated from Galí Ch. 6) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

open Calvo (hasDerivAt_E_of_remainder remainder_le_of_lipschitz_deriv hasDerivAt_E
  hasDerivAt_tsum_E)

/-! ### Conditional expectations of discounted sums -/

/-- A geometrically weighted series of uniformly bounded random variables
converges at every state (used throughout Woodford (2003), eqs. (4.3)–(4.7), pp. 222–223). -/
theorem summable_geometric_bounded {a : ℝ} (ha : |a| < 1) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ k ω, |y k ω| ≤ M) (ω : Ω) : Summable fun k => a ^ k * y k ω := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hy k ω) (pow_nonneg (abs_nonneg a) k)

/-! ### Differentiating under `E_t` -/

/-- The desired (frictionless) gross markup `M = θ/(θ − 1)` (Woodford (2003), p. 223). -/
noncomputable def markup (θ : ℝ) : ℝ := θ / (θ - 1)

/-- The desired markup exceeds one: `M > 1` for `θ > 1` (Woodford (2003), p. 223). -/
theorem one_lt_markup {θ : ℝ} (hθ : 1 < θ) : 1 < markup θ := by
  unfold markup
  rw [one_lt_div (by linarith)]
  linarith

/-- The desired markup is positive (Woodford (2003), p. 223). -/
theorem markup_pos {θ : ℝ} (hθ : 1 < θ) : 0 < markup θ :=
  lt_trans one_pos (one_lt_markup hθ)

/-- The labour-demand constraint, Woodford (2003), pp. 222–223:
`Y_{t+k|t} = (P*_t / P_{t+k})^{−θ} C_{t+k}`, as a random variable. -/
noncomputable def demand (θ Pstar : ℝ) (P C : Ω → ℝ) : Ω → ℝ :=
  fun ω => (Pstar / P ω) ^ (-θ) * C ω

/-- Demand factorises as `P*^{−θ} · P^θ C` (Woodford (2003), eq. (4.2), p. 221). -/
theorem demand_eq {θ x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    demand θ x P C ω = x ^ (-θ) * (P ω ^ θ * C ω) := by
  unfold demand
  rw [Real.div_rpow hx.le (hP ω).le, Real.rpow_neg (hP ω).le θ, div_inv_eq_mul]
  ring

/-- Demand is positive (Woodford (2003), eq. (4.2), p. 221). -/
theorem demand_pos {θ x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω)
    (hC : ∀ ω, 0 < C ω) (ω : Ω) : 0 < demand θ x P C ω :=
  mul_pos (Real.rpow_pos_of_pos (div_pos hx (hP ω)) _) (hC ω)

/-- The price elasticity of labour demand is `−θ`: `dY/dP* = −θ Y / P*`
(Woodford (2003), pp. 222–223; the demand curve (1.12) of `FlexiblePrices.hasDerivAt_dem`). -/
theorem hasDerivAt_demand {θ x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    HasDerivAt (fun z => demand θ z P C ω) (-θ * demand θ x P C ω / x) x := by
  have e : (fun z => demand θ z P C ω) = FlexiblePrices.dem (C ω) (P ω) θ := by
    funext z
    simp only [demand, FlexiblePrices.dem, mul_comm]
  have hx' : demand θ x P C ω = FlexiblePrices.dem (C ω) (P ω) θ x := congrFun e x
  rw [e, hx']
  exact FlexiblePrices.hasDerivAt_dem (hP ω) hx

/-- Generic horizon-`k` payoff of an agent (here the wage setter) that reset its wage (price) to
`P*` (Woodford (2003), pp. 222–223):
`Q_{t,t+k} (P* Y_{t+k|t} − Ψ_{t+k}(Y_{t+k|t}))`, where
`Q_{t,t+k} = Λ_{t,t+k}/P_{t+k}` converts nominal date-`t+k` income into date-`t`
utility and `Ψ_{t+k}` is the nominal cost (for the wage setter: money disutility of work). -/
noncomputable def profit (θ : ℝ) (Q P C : Ω → ℝ) (Ψ : Ω → ℝ → ℝ) (Pstar : ℝ) : Ω → ℝ :=
  fun ω => Q ω * (Pstar * demand θ Pstar P C ω - Ψ ω (demand θ Pstar P C ω))

/-- **The reset-wage objective** (Woodford (2003), pp. 222–223):
`∑ₖ αᵏ E_t[Q_{t,t+k} (P* Y_{t+k|t} − Ψ_{t+k}(Y_{t+k|t}))]`, a genuine infinite
discounted sum, evaluated at the state `ω`. -/
noncomputable def objective (α θ : ℝ) (Q P C : ℕ → Ω → ℝ) (Ψ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (Pstar : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, α ^ k * 𝔼.E t (profit θ (Q k) (P k) (C k) (Ψ k) Pstar) ω

/-- Woodford (2003), eq. (2.2), p. 178, and pp. 222–223: the generic reset objective here is
Calvo's reset-price objective (2.2) (`Calvo.resetObjective`) with discount factor `Q`
and horizon profit `P* Y_{t+k|t} − Ψ_{t+k}(Y_{t+k|t})`, so wage setting (4.3) and the price
setter behind (4.9) are instances of the same problem as (2.2). -/
theorem objective_eq_resetObjective (α θ : ℝ) (Q P C : ℕ → Ω → ℝ) (Ψ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (x : ℝ) :
    objective 𝔼 α θ Q P C Ψ t x = Calvo.resetObjective 𝔼 α Q
      (fun k ω z => z * demand θ z (P k) (C k) ω - Ψ k ω (demand θ z (P k) (C k) ω)) t x :=
  rfl

/-- The summand of (4.4), Woodford (2003), pp. 222–223:
`Q_{t,t+k} Y_{t+k|t} (P* − M Ψ'_{t+k|t})`, with `Ψ'_{t+k|t} = Ψ'_{t+k}(Y_{t+k|t})`
the nominal marginal cost. -/
noncomputable def focTerm (θ : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (Pstar : ℝ) : Ω → ℝ :=
  fun ω => Q ω * demand θ Pstar P C ω * (Pstar - markup θ * dΨ ω (demand θ Pstar P C ω))

/-- The left-hand side of the optimality condition (4.4), Woodford (2003), pp. 222–223:
`∑ₖ αᵏ E_t[Q_{t,t+k} Y_{t+k|t} (P* − M Ψ'_{t+k|t})]`. -/
noncomputable def focSum (α θ : ℝ) (Q P C : ℕ → Ω → ℝ) (dΨ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (Pstar : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, α ^ k * 𝔼.E t (focTerm θ (Q k) (P k) (C k) (dΨ k) Pstar) ω

/-- The derivative of horizon-`k` profits in `P*`:
`((1 − θ)/P*) Q Y (P* − M Ψ')` (Woodford (2003), pp. 222–223). -/
noncomputable def profitDeriv (θ : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (Pstar : ℝ) :
    Ω → ℝ :=
  fun ω => (1 - θ) / Pstar * focTerm θ Q P C dΨ Pstar ω

/-- **Marginal profit at one horizon** (Woodford (2003), pp. 222–223):
`d/dP* [Q (P* Y − Ψ(Y))] = ((1 − θ)/P*) Q Y (P* − M Ψ'(Y))`. -/
theorem hasDerivAt_profit {θ x : ℝ} (hθ : 1 < θ) (hx : 0 < x) {Q P C : Ω → ℝ}
    {Ψ dΨ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hΨ : ∀ ω y, 0 < y → HasDerivAt (Ψ ω) (dΨ ω y) y) (ω : Ω) :
    HasDerivAt (fun z => profit θ Q P C Ψ z ω) (profitDeriv θ Q P C dΨ x ω) x := by
  have hY := hasDerivAt_demand (θ := θ) (C := C) hx hP ω
  have hΨY := (hΨ ω _ (demand_pos hx hP hC ω)).comp x hY
  have h := (((hasDerivAt_id x).mul hY).sub hΨY).const_mul (Q ω)
  refine h.congr_deriv ?_
  unfold profitDeriv focTerm markup
  have h1 : θ - 1 ≠ 0 := by linarith
  have h2 : x ≠ 0 := hx.ne'
  simp only [id]
  field_simp
  ring

/-- `E_t` of marginal profit: the constant `(1 − θ)/P*` comes out of `E_t`
(Woodford (2003), pp. 222–223). -/
theorem E_profitDeriv (θ : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (x : ℝ) (t : ℕ) (ω : Ω) :
    𝔼.E t (profitDeriv θ Q P C dΨ x) ω = (1 - θ) / x * 𝔼.E t (focTerm θ Q P C dΨ x) ω := by
  have : profitDeriv θ Q P C dΨ x = ((1 - θ) / x) • focTerm θ Q P C dΨ x := rfl
  rw [this, 𝔼.E_smul]
  rfl

/-- **The derivative of the reset-wage objective** (Woodford (2003), eq. (4.4), p. 222):
under explicit domination and local-Lipschitz hypotheses on marginal profits and
convergence of the objective at one price, the objective has derivative
`((1 − θ)/P*) ∑ₖ αᵏ E_t[Q_{t,t+k} Y_{t+k|t}(P* − M Ψ'_{t+k|t})]` at every `P*` in
an open interval `U ⊆ (0, ∞)`. -/
theorem hasDerivAt_objective {α θ : ℝ} (hθ : 1 < θ) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hP : ∀ k ω, 0 < P k ω) (hC : ∀ k ω, 0 < C k ω)
    (hΨ : ∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y)
    {U : Set ℝ} (hU : IsOpen U) (hU' : IsPreconnected U) (hUpos : U ⊆ Set.Ioi 0)
    {u : ℕ → ℝ}
    (hLip : ∀ k, ∀ y ∈ U, ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv θ (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv θ (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y|)
    (hdom : ∀ k, ∀ y ∈ U, ∀ ω, |profitDeriv θ (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k)
    (hu : Summable fun k => |α| ^ k * u k) {y₀ : ℝ} (hy₀ : y₀ ∈ U) (t : ℕ) (ω : Ω)
    (hs : Summable fun k => α ^ k * 𝔼.E t (profit θ (Q k) (P k) (C k) (Ψ k) y₀) ω)
    {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun z => objective 𝔼 α θ Q P C Ψ t z ω)
      ((1 - θ) / x * focSum 𝔼 α θ Q P C dΨ t x ω) x := by
  have h := hasDerivAt_tsum_E 𝔼 (α := α)
    (g := fun k z => profit θ (Q k) (P k) (C k) (Ψ k) z)
    (g' := fun k z => profitDeriv θ (Q k) (P k) (C k) (dΨ k) z) hU hU'
    (fun k y hy ω' => hasDerivAt_profit hθ (hUpos hy) (hP k) (hC k) (hΨ k) ω')
    hLip hdom hu hy₀ t ω hs hx
  refine h.congr_deriv ?_
  simp only [E_profitDeriv, focSum]
  rw [← tsum_mul_left]
  congr 1
  funext k
  ring

/-- **The optimality condition (4.4) is necessary** (Woodford (2003), eq. (4.4), p. 222):
if `P*` is a local maximum of the reset-wage objective, then
`∑ₖ αᵏ E_t[Q_{t,t+k} Y_{t+k|t} (P* − M Ψ'_{t+k|t})] = 0`. -/
theorem foc_of_isLocalMax {α θ : ℝ} (hθ : 1 < θ) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} {t : ℕ} {ω : Ω} {x : ℝ} (hx : 0 < x)
    (hder : HasDerivAt (fun z => objective 𝔼 α θ Q P C Ψ t z ω)
      ((1 - θ) / x * focSum 𝔼 α θ Q P C dΨ t x ω) x)
    (hmax : IsLocalMax (fun z => objective 𝔼 α θ Q P C Ψ t z ω) x) :
    focSum 𝔼 α θ Q P C dΨ t x ω = 0 := by
  have h := hmax.hasDerivAt_eq_zero hder
  have hc : (1 - θ) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  exact (mul_eq_zero.mp h).resolve_left hc

/-- The objective is differentiable at every positive price when marginal profits
are dominated on every bounded interval `(a, b)` with `a > 0` (Woodford (2003), pp. 222–223). -/
theorem hasDerivAt_objective_of_pos {α θ : ℝ} (hθ : 1 < θ) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hP : ∀ k ω, 0 < P k ω) (hC : ∀ k ω, 0 < C k ω)
    (hΨ : ∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y)
    (hLip : ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv θ (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv θ (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y|)
    (hloc : ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |α| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω, |profitDeriv θ (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k)
    (t : ℕ) (ω : Ω)
    (hs : ∀ y, 0 < y → Summable fun k => α ^ k * 𝔼.E t (profit θ (Q k) (P k) (C k) (Ψ k) y) ω)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => objective 𝔼 α θ Q P C Ψ t z ω)
      ((1 - θ) / x * focSum 𝔼 α θ Q P C dΨ t x ω) x := by
  obtain ⟨u, hu, hdom⟩ := hloc (x / 2) (x + 1) (by positivity)
  have hxU : x ∈ Set.Ioo (x / 2) (x + 1) := ⟨by linarith, by linarith⟩
  have hUpos : Set.Ioo (x / 2) (x + 1) ⊆ Set.Ioi 0 := fun y hy => by
    simp only [Set.mem_Ioi]; linarith [hy.1]
  exact hasDerivAt_objective 𝔼 hθ hP hC hΨ isOpen_Ioo isPreconnected_Ioo hUpos
    (fun k y hy => hLip k y (hUpos hy)) hdom hu hxU t ω (hs x hx) hxU

/-! ### The first-order condition characterises the optimum (convex costs) -/

/-- The `P*`-dependent core of the summand of (4.4) once the factor `P*^{−θ}` of
demand is taken out: `Q P^θ C (P* − M Ψ'(Y))` (Woodford (2003), pp. 222–223). -/
noncomputable def focCore (θ : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (Pstar : ℝ) : Ω → ℝ :=
  fun ω => Q ω * (P ω ^ θ * C ω) * (Pstar - markup θ * dΨ ω (demand θ Pstar P C ω))

/-- The summand of (4.4) is `P*^{−θ}` times its core (Woodford (2003), pp. 222–223). -/
theorem focTerm_eq {θ x : ℝ} (hx : 0 < x) {Q P C : Ω → ℝ} (dΨ : Ω → ℝ → ℝ)
    (hP : ∀ ω, 0 < P ω) : focTerm θ Q P C dΨ x = x ^ (-θ) • focCore θ Q P C dΨ x := by
  funext ω
  simp only [focTerm, focCore, Pi.smul_apply, smul_eq_mul]
  rw [demand_eq hx hP ω]
  ring

/-- With convex costs (nondecreasing marginal cost), the core of (4.4) increases in
`P*` at least at rate `Q P^θ C`: a higher price lowers demand and hence marginal
cost (Woodford (2003), pp. 222–223). -/
theorem focCore_sub_ge {θ : ℝ} (hθ : 1 < θ) {Q P C : Ω → ℝ} {dΨ : Ω → ℝ → ℝ}
    (hQ : ∀ ω, 0 < Q ω) (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hconv : ∀ ω, MonotoneOn (dΨ ω) (Set.Ioi 0)) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (ω : Ω) :
    (y - x) * (Q ω * (P ω ^ θ * C ω)) ≤ focCore θ Q P C dΨ y ω - focCore θ Q P C dΨ x ω := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hK : 0 < P ω ^ θ * C ω := mul_pos (Real.rpow_pos_of_pos (hP ω) θ) (hC ω)
  have hdem : demand θ y P C ω ≤ demand θ x P C ω := by
    rw [demand_eq hx hP ω, demand_eq hy hP ω]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))
      hK.le
  have hd : dΨ ω (demand θ y P C ω) ≤ dΨ ω (demand θ x P C ω) :=
    hconv ω (demand_pos hy hP hC ω) (demand_pos hx hP hC ω) hdem
  have key : focCore θ Q P C dΨ y ω - focCore θ Q P C dΨ x ω
        - (y - x) * (Q ω * (P ω ^ θ * C ω))
      = Q ω * (P ω ^ θ * C ω) *
        (markup θ * (dΨ ω (demand θ x P C ω) - dΨ ω (demand θ y P C ω))) := by
    unfold focCore; ring
  have h0 : 0 ≤ Q ω * (P ω ^ θ * C ω) *
      (markup θ * (dΨ ω (demand θ x P C ω) - dΨ ω (demand θ y P C ω))) :=
    mul_nonneg (mul_pos (hQ ω) hK).le
      (mul_nonneg (markup_pos hθ).le (sub_nonneg.mpr hd))
  linarith

/-- `E_t` version of `focCore_sub_ge` (Woodford (2003), pp. 222–223). -/
theorem E_focCore_le {θ : ℝ} (hθ : 1 < θ) {Q P C : Ω → ℝ} {dΨ : Ω → ℝ → ℝ}
    (hQ : ∀ ω, 0 < Q ω) (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hconv : ∀ ω, MonotoneOn (dΨ ω) (Set.Ioi 0)) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (t : ℕ) (ω : Ω) :
    (y - x) * 𝔼.E t (fun ω' => Q ω' * (P ω' ^ θ * C ω')) ω + 𝔼.E t (focCore θ Q P C dΨ x) ω
      ≤ 𝔼.E t (focCore θ Q P C dΨ y) ω := by
  have hle : (y - x) • (fun ω' => Q ω' * (P ω' ^ θ * C ω')) + focCore θ Q P C dΨ x
      ≤ focCore θ Q P C dΨ y := fun ω' => by
    have := focCore_sub_ge hθ hQ hP hC hconv hx hxy ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have := 𝔼.mono t hle ω
  simpa [map_add, map_smul] using this

/-- The expected-revenue weight `E_t[Q P^θ C]` is nonnegative (Woodford (2003), pp. 222–223). -/
theorem E_weight_nonneg {θ : ℝ} {Q P C : Ω → ℝ} (hQ : ∀ ω, 0 < Q ω) (hP : ∀ ω, 0 < P ω)
    (hC : ∀ ω, 0 < C ω) (t : ℕ) (ω : Ω) :
    0 ≤ 𝔼.E t (fun ω' => Q ω' * (P ω' ^ θ * C ω')) ω := by
  have h0 : (0 : Ω → ℝ) ≤ fun ω' => Q ω' * (P ω' ^ θ * C ω') := fun ω' =>
    (mul_pos (hQ ω') (mul_pos (Real.rpow_pos_of_pos (hP ω') θ) (hC ω'))).le
  simpa using 𝔼.mono t h0 ω

/-- `E_t` of the summand of (4.4) in terms of marginal profit
(Woodford (2003), pp. 222–223). -/
theorem E_focCore_eq {θ x : ℝ} (hθ : 1 < θ) (hx : 0 < x) {Q P C : Ω → ℝ}
    (dΨ : Ω → ℝ → ℝ) (hP : ∀ ω, 0 < P ω) (t : ℕ) (ω : Ω) :
    𝔼.E t (focCore θ Q P C dΨ x) ω
      = ((1 - θ) / x * x ^ (-θ))⁻¹ * 𝔼.E t (profitDeriv θ Q P C dΨ x) ω := by
  rw [E_profitDeriv, focTerm_eq hx dΨ hP, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul]
  have h1 : (1 - θ) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  have h2 : x ^ (-θ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have h3 : 1 - θ ≠ 0 := by linarith
  field_simp

/-- **The optimality condition (4.4) characterises the optimal reset wage**
(Woodford (2003), eq. (4.4), p. 222). With convex costs (nondecreasing marginal cost),
positive discount factors, prices and demand, and a positive current-period
revenue weight, a positive price `P*` maximises the reset-wage objective over
all positive prices if and only if it satisfies (4.4); such a maximiser is then
the strict, hence unique, maximiser. -/
theorem isMaxOn_iff_foc {α θ : ℝ} (hθ : 1 < θ) (hα : 0 ≤ α) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hQ : ∀ k ω, 0 < Q k ω) (hP : ∀ k ω, 0 < P k ω)
    (hC : ∀ k ω, 0 < C k ω) (hΨ : ∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y)
    (hconv : ∀ k ω, MonotoneOn (dΨ k ω) (Set.Ioi 0))
    (hLip : ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv θ (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv θ (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y|)
    (hloc : ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |α| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω, |profitDeriv θ (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k)
    (t : ℕ) (ω : Ω)
    (hs : ∀ y, 0 < y → Summable fun k => α ^ k * 𝔼.E t (profit θ (Q k) (P k) (C k) (Ψ k) y) ω)
    (hpos : 0 < 𝔼.E t (fun ω' => Q 0 ω' * (P 0 ω' ^ θ * C 0 ω')) ω)
    {x : ℝ} (hx : 0 < x) :
    (IsMaxOn (fun z => objective 𝔼 α θ Q P C Ψ t z ω) (Set.Ioi 0) x ↔
        focSum 𝔼 α θ Q P C dΨ t x ω = 0) ∧
      (focSum 𝔼 α θ Q P C dΨ t x ω = 0 → ∀ y, 0 < y → y ≠ x →
        objective 𝔼 α θ Q P C Ψ t y ω < objective 𝔼 α θ Q P C Ψ t x ω) := by
  set V := fun z => objective 𝔼 α θ Q P C Ψ t z ω with hV
  set H : ℝ → ℝ := fun z => ∑' k, α ^ k * 𝔼.E t (focCore θ (Q k) (P k) (C k) (dΨ k) z) ω
    with hH
  have hder : ∀ z, 0 < z → HasDerivAt V ((1 - θ) / z * focSum 𝔼 α θ Q P C dΨ t z ω) z :=
    fun z hz => hasDerivAt_objective_of_pos 𝔼 hθ hP hC hΨ hLip hloc t ω hs hz
  -- summability of the core series
  have hsum : ∀ z, 0 < z →
      Summable fun k => α ^ k * 𝔼.E t (focCore θ (Q k) (P k) (C k) (dΨ k) z) ω := by
    intro z hz
    obtain ⟨u, hu, hdom⟩ := hloc (z / 2) (z + 1) (by positivity)
    have hzU : z ∈ Set.Ioo (z / 2) (z + 1) := ⟨by linarith, by linarith⟩
    have hs' : Summable fun k =>
        α ^ k * 𝔼.E t (profitDeriv θ (Q k) (P k) (C k) (dΨ k) z) ω := by
      refine Summable.of_norm_bounded hu fun k => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdom k z hzU) t ω)
        (pow_nonneg (abs_nonneg α) k)
    refine (hs'.mul_left ((1 - θ) / z * z ^ (-θ))⁻¹).congr fun k => ?_
    rw [E_focCore_eq 𝔼 hθ hz _ (hP k)]
    ring
  -- (4.4) in terms of the core series
  have hfocH : ∀ z, 0 < z → focSum 𝔼 α θ Q P C dΨ t z ω = z ^ (-θ) * H z := by
    intro z hz
    simp only [focSum, hH, focTerm_eq hz _ (hP _), 𝔼.E_smul, Pi.smul_apply, smul_eq_mul]
    rw [← tsum_mul_left]
    congr 1
    funext k
    ring
  -- the core series is strictly increasing
  have hHmono : ∀ z y, 0 < z → z < y → H z < H y := by
    intro z y hz hzy
    refine Summable.tsum_lt_tsum (i := 0) (fun k => ?_) ?_ (hsum z hz)
      (hsum y (hz.trans hzy))
    · have h1 := E_focCore_le 𝔼 hθ (hQ k) (hP k) (hC k) (hconv k) hz hzy.le t ω
      have h2 := E_weight_nonneg 𝔼 (θ := θ) (hQ k) (hP k) (hC k) t ω
      have h3 : 0 ≤ (y - z) * 𝔼.E t (fun ω' => Q k ω' * (P k ω' ^ θ * C k ω')) ω :=
        mul_nonneg (by linarith) h2
      exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hα k)
    · have h1 := E_focCore_le 𝔼 hθ (hQ 0) (hP 0) (hC 0) (hconv 0) hz hzy.le t ω
      have h3 : 0 < (y - z) * 𝔼.E t (fun ω' => Q 0 ω' * (P 0 ω' ^ θ * C 0 ω')) ω :=
        mul_pos (by linarith) hpos
      simp only [pow_zero, one_mul]
      linarith
  have hcoef : ∀ z, 0 < z → (1 - θ) / z < 0 := fun z hz => div_neg_of_neg_of_pos (by linarith) hz
  -- the strict-maximum part
  have hstrict : focSum 𝔼 α θ Q P C dΨ t x ω = 0 → ∀ y, 0 < y → y ≠ x → V y < V x := by
    intro hfoc
    have hHx : H x = 0 := by
      have := hfocH x hx
      rw [hfoc] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (Real.rpow_pos_of_pos hx _).ne'
    have hcont : ∀ z, 0 < z → ContinuousAt V z := fun z hz => (hder z hz).continuousAt
    have hinc : StrictMonoOn V (Set.Ioc 0 x) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioc 0 x)
        (fun z hz => (hcont z hz.1).continuousWithinAt) fun z hz => ?_
      rw [interior_Ioc] at hz
      rw [(hder z hz.1).deriv, hfocH z hz.1]
      have hHz : H z < 0 := hHx ▸ hHmono z x hz.1 hz.2
      have := mul_neg_of_neg_of_pos hHz (Real.rpow_pos_of_pos hz.1 (-θ))
      nlinarith [hcoef z hz.1]
    have hdec : StrictAntiOn V (Set.Ici x) := by
      refine strictAntiOn_of_deriv_neg (convex_Ici x)
        (fun z hz => (hcont z (lt_of_lt_of_le hx hz)).continuousWithinAt) fun z hz => ?_
      rw [interior_Ici] at hz
      have hz0 : 0 < z := hx.trans hz
      rw [(hder z hz0).deriv, hfocH z hz0]
      have hHz : 0 < H z := hHx ▸ hHmono x z hx hz
      have := mul_pos (Real.rpow_pos_of_pos hz0 (-θ)) hHz
      nlinarith [hcoef z hz0]
    intro y hy hyx
    rcases lt_or_gt_of_ne hyx with h | h
    · exact hinc ⟨hy, h.le⟩ ⟨hx, le_rfl⟩ h
    · exact hdec (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h.le) h
  refine ⟨⟨fun hmax => ?_, fun hfoc => ?_⟩, hstrict⟩
  · exact foc_of_isLocalMax 𝔼 hθ hx (hder x hx) (hmax.isLocalMax (Ioi_mem_nhds hx))
  · intro y hy
    rcases eq_or_ne y x with h | h
    · rw [h]; exact le_refl (V x)
    · exact (hstrict hfoc y hy h).le

/-! ### Flexible prices and the zero-wage-inflation steady state -/

/-- With flexible wages (`α = 0`) the objective reduces to current expected
profits (Woodford (2003), p. 223). -/
theorem objective_flexible (θ : ℝ) (Q P C : ℕ → Ω → ℝ) (Ψ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (z : ℝ) (ω : Ω) :
    objective 𝔼 0 θ Q P C Ψ t z ω = 𝔼.E t (profit θ (Q 0) (P 0) (C 0) (Ψ 0) z) ω := by
  unfold objective
  rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
  simp

/-- With flexible wages (`α = 0`) condition (4.4) involves only the current period
(Woodford (2003), p. 223). -/
theorem focSum_flexible (θ : ℝ) (Q P C : ℕ → Ω → ℝ) (dΨ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (z : ℝ) (ω : Ω) :
    focSum 𝔼 0 θ Q P C dΨ t z ω = 𝔼.E t (focTerm θ (Q 0) (P 0) (C 0) (dΨ 0) z) ω := by
  unfold focSum
  rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
  simp

/-- **Flexible-wage wage-setting rule** (Woodford (2003), p. 223): with `α = 0` and the
current-period variables known at `t`, condition (4.4) holds if and only if
`P*_t = M Ψ'_{t|t}`, the frictionless markup over marginal cost. -/
theorem flexible_foc_iff {θ x : ℝ} (hx : 0 < x) {Q P C : ℕ → Ω → ℝ}
    {dΨ : ℕ → Ω → ℝ → ℝ} (hQ : ∀ ω, 0 < Q 0 ω) (hP : ∀ ω, 0 < P 0 ω) (hC : ∀ ω, 0 < C 0 ω)
    {t : ℕ} (hknown : 𝔼.E t (focTerm θ (Q 0) (P 0) (C 0) (dΨ 0) x)
      = focTerm θ (Q 0) (P 0) (C 0) (dΨ 0) x) (ω : Ω) :
    focSum 𝔼 0 θ Q P C dΨ t x ω = 0 ↔ x = markup θ * dΨ 0 ω (demand θ x (P 0) (C 0) ω) := by
  rw [focSum_flexible, hknown]
  unfold focTerm
  have h := mul_pos (hQ ω) (demand_pos (θ := θ) hx hP hC ω)
  constructor
  · intro h0
    have := (mul_eq_zero.mp h0).resolve_left h.ne'
    linarith
  · intro h0
    rw [← h0, sub_self, mul_zero]

/-- **Flexible-wage optimum** (Woodford (2003), p. 223): with `α = 0`, if the
current-period profit function is known at `t` and `P*` is a local maximum of
the objective, then `P* = M Ψ'_{t|t}`. -/
theorem flexible_optimum {θ x : ℝ} (hθ : 1 < θ) (hx : 0 < x) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hQ : ∀ ω, 0 < Q 0 ω) (hP : ∀ ω, 0 < P 0 ω) (hC : ∀ ω, 0 < C 0 ω)
    (hΨ : ∀ ω y, 0 < y → HasDerivAt (Ψ 0 ω) (dΨ 0 ω y) y) {t : ℕ}
    (hknown : ∀ z, 𝔼.E t (profit θ (Q 0) (P 0) (C 0) (Ψ 0) z)
      = profit θ (Q 0) (P 0) (C 0) (Ψ 0) z) {ω : Ω}
    (hmax : IsLocalMax (fun z => objective 𝔼 0 θ Q P C Ψ t z ω) x) :
    x = markup θ * dΨ 0 ω (demand θ x (P 0) (C 0) ω) := by
  have hfun : (fun z => objective 𝔼 0 θ Q P C Ψ t z ω)
      = fun z => profit θ (Q 0) (P 0) (C 0) (Ψ 0) z ω := by
    funext z; rw [objective_flexible, hknown]
  rw [hfun] at hmax
  have h0 := hmax.hasDerivAt_eq_zero (hasDerivAt_profit hθ hx hP hC hΨ ω)
  unfold profitDeriv focTerm at h0
  have hc : (1 - θ) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  have h := mul_pos (hQ ω) (demand_pos (θ := θ) hx hP hC ω)
  have h1 := (mul_eq_zero.mp h0).resolve_left hc
  have := (mul_eq_zero.mp h1).resolve_left h.ne'
  linarith

/-- **The zero-wage-inflation steady state** (Woodford (2003), p. 223): with constant price
level `P`, consumption `C`, discount factors `Λ_{t,t+k} = βᵏ` and marginal cost `Ψ`
at the steady-state output, condition (4.4) at `P* = P` holds if and only if
`P = M Ψ`: actual markups equal the frictionless markup. -/
theorem steadyState_foc_iff {β α θ Pbar Cbar Ψbar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hP : 0 < Pbar) (hC : 0 < Cbar) {dΨ : ℕ → Ω → ℝ → ℝ}
    (hdΨ : ∀ k ω, dΨ k ω Cbar = Ψbar) (t : ℕ) (ω : Ω) :
    focSum 𝔼 α θ (fun k _ => β ^ k / Pbar) (fun _ _ => Pbar) (fun _ _ => Cbar) dΨ t Pbar ω = 0
      ↔ Pbar = markup θ * Ψbar := by
  have hY : ∀ ω' : Ω, demand θ Pbar (fun _ => Pbar) (fun _ => Cbar) ω' = Cbar := by
    intro ω'; simp [demand, div_self hP.ne']
  have hterm : ∀ k, focTerm θ (fun _ => β ^ k / Pbar) (fun _ => Pbar) (fun _ => Cbar) (dΨ k) Pbar
      = fun _ => β ^ k / Pbar * Cbar * (Pbar - markup θ * Ψbar) := by
    intro k; funext ω'
    simp only [focTerm, hY, hdΨ]
  have hβα0 : 0 ≤ β * α := mul_nonneg hβ0 hα0
  have hβα1 : β * α < 1 := by nlinarith
  have hsum : focSum 𝔼 α θ (fun k _ => β ^ k / Pbar) (fun _ _ => Pbar) (fun _ _ => Cbar) dΨ t
      Pbar ω = (1 - β * α)⁻¹ * (Cbar / Pbar * (Pbar - markup θ * Ψbar)) := by
    simp only [focSum, hterm, 𝔼.const]
    rw [← tsum_geometric_of_lt_one hβα0 hβα1, ← tsum_mul_right]
    congr 1; funext k
    rw [mul_pow]; field_simp
  rw [hsum]
  have h1 : (1 - β * α)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have h2 : Cbar / Pbar ≠ 0 := (div_pos hC hP).ne'
  constructor
  · intro h0
    have := (mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left h1)).resolve_left h2
    linarith
  · intro h0
    rw [← h0, sub_self, mul_zero, mul_zero]

/-! ### The log-linear wage-setting rule (4.7) as the exact linearisation of (4.4) -/

/-- The log desired markup `μ = log M` (Woodford (2003), p. 223). -/
noncomputable def logMarkup (θ : ℝ) : ℝ := Real.log (markup θ)

/-- The left-hand side of (4.4) written in terms of the weights
`wₖ = Λ_{t,t+k} Y_{t+k|t} / P_{t+k}` and the nominal marginal costs
`Ψ_{t+k|t}` (Woodford (2003), eq. (4.4), p. 222):
`∑ₖ αᵏ E_t[wₖ (P* − M Ψ_{t+k|t})]`. -/
noncomputable def focLHS (α θ : ℝ) (w : ℕ → Ω → ℝ) (Pstar : ℝ) (Ψm : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ω => ∑' k, α ^ k * 𝔼.E t (fun ω' => w k ω' * (Pstar - markup θ * Ψm k ω')) ω

/-- The reset-wage condition `focSum` is (4.4) with weights `Q_{t,t+k} Y_{t+k|t}`
and marginal costs `Ψ'_{t+k}(Y_{t+k|t})` (Woodford (2003), pp. 222–223). -/
theorem focSum_eq_focLHS (α θ : ℝ) (Q P C : ℕ → Ω → ℝ) (dΨ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (x : ℝ) :
    focSum 𝔼 α θ Q P C dΨ t x = focLHS 𝔼 α θ (fun k ω => Q k ω * demand θ x (P k) (C k) ω) x
      (fun k ω => dΨ k ω (demand θ x (P k) (C k) ω)) t := rfl

/-- Differentiating `E_t[exp(s g)]` in `s` for a bounded random variable `g`:
the derivative is `E_t[g exp(s g)]` (used for (4.7), Woodford (2003), p. 223). -/
theorem hasDerivAt_E_exp {g : Ω → ℝ} {B : ℝ} (hg : ∀ ω, |g ω| ≤ B) (t : ℕ) (ω : Ω) (s : ℝ) :
    HasDerivAt (fun r => 𝔼.E t (fun ω' => Real.exp (r * g ω')) ω)
      (𝔼.E t (fun ω' => g ω' * Real.exp (s * g ω')) ω) s := by
  refine hasDerivAt_E_of_remainder 𝔼 (g := fun r ω' => Real.exp (r * g ω'))
    (δ := 1 / (|B| + 1)) (C := Real.exp (|s| * |B|) * B ^ 2) (by positivity)
    (fun h hh ω' => ?_) t ω
  have hgB : |g ω'| ≤ |B| := (hg ω').trans (le_abs_self B)
  have hhB : |h| * |B| ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hh
    nlinarith [abs_nonneg B, abs_nonneg h]
  have hhg : |h * g ω'| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hgB (abs_nonneg h)).trans hhB
  have hexp := Real.abs_exp_sub_one_sub_id_le hhg
  have key : Real.exp ((s + h) * g ω') - Real.exp (s * g ω') - h * (g ω' * Real.exp (s * g ω'))
      = Real.exp (s * g ω') * (Real.exp (h * g ω') - 1 - h * g ω') := by
    rw [add_mul, Real.exp_add]; ring
  rw [key, abs_mul, abs_of_pos (Real.exp_pos _)]
  have e1 : Real.exp (s * g ω') ≤ Real.exp (|s| * |B|) := by
    rw [Real.exp_le_exp]
    calc s * g ω' ≤ |s * g ω'| := le_abs_self _
      _ = |s| * |g ω'| := abs_mul _ _
      _ ≤ |s| * |B| := mul_le_mul_of_nonneg_left hgB (abs_nonneg s)
  have e2 : (h * g ω') ^ 2 ≤ B ^ 2 * h ^ 2 := by
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (sq_le_sq.mpr hgB) (sq_nonneg h)
  calc Real.exp (s * g ω') * |Real.exp (h * g ω') - 1 - h * g ω'|
      ≤ Real.exp (|s| * |B|) * (B ^ 2 * h ^ 2) :=
        mul_le_mul e1 (hexp.trans e2) (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (|s| * |B|) * B ^ 2 * h ^ 2 := by ring

/-- **Exact linearisation of (4.4) at the zero-wage-inflation steady state**
(Woodford (2003), p. 223). Perturb the steady state along an arbitrary bounded
direction: log weights `log wₖ = log(βᵏ w̄) + s ŵₖ` (stochastic discount factor,
demand and price level combined), log reset wage `p* = p̄ + s x̂`, and log
marginal costs `ψ_{t+k|t} = ψ̄ + s ψ̂ₖ`, where the steady state satisfies
`p̄ = μ + ψ̄` (`P = M Ψ`). Then the left-hand side of (4.4) has derivative
`w̄ e^{p̄} ∑ₖ (βα)ᵏ (x̂ − E_t ψ̂ₖ)` at `s = 0`. The weight deviations `ŵ` drop out:
to first order only prices and marginal costs matter. -/
theorem hasDerivAt_focLHS_path {α β θ wbar pbar xhat B : ℝ} (hθ : 1 < θ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1) {what ψhat : ℕ → Ω → ℝ}
    (hw : ∀ k ω, |what k ω| ≤ B) (hψ : ∀ k ω, |ψhat k ω| ≤ B) (hxB : |xhat| ≤ B)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => focLHS 𝔼 α θ (fun k ω' => β ^ k * wbar * Real.exp (s * what k ω'))
        (Real.exp (pbar + s * xhat))
        (fun k ω' => Real.exp (pbar - logMarkup θ + s * ψhat k ω')) t ω)
      (wbar * Real.exp pbar * ∑' k, (β * α) ^ k * (xhat - 𝔼.E t (ψhat k) ω)) 0 := by
  set c := wbar * Real.exp pbar with hc
  set a : ℕ → Ω → ℝ := fun k ω' => what k ω' + xhat with ha
  set b : ℕ → Ω → ℝ := fun k ω' => what k ω' + ψhat k ω' with hb
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hxB
  have haB : ∀ k ω', |a k ω'| ≤ 2 * B := fun k ω' =>
    (abs_add_le _ _).trans (by linarith [hw k ω'])
  have hbB : ∀ k ω', |b k ω'| ≤ 2 * B := fun k ω' =>
    (abs_add_le _ _).trans (by linarith [hw k ω', hψ k ω'])
  have hβα0 : 0 ≤ β * α := mul_nonneg hβ0 hα0
  have hβα1 : β * α < 1 := by nlinarith
  -- rewrite the path of (4.4) through exponentials of `s a` and `s b`
  have hfun : (fun s => focLHS 𝔼 α θ (fun k ω' => β ^ k * wbar * Real.exp (s * what k ω'))
        (Real.exp (pbar + s * xhat))
        (fun k ω' => Real.exp (pbar - logMarkup θ + s * ψhat k ω')) t ω)
      = fun s => ∑' k, (β * α) ^ k * (c * (𝔼.E t (fun ω' => Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => Real.exp (s * b k ω')) ω)) := by
    funext s
    unfold focLHS
    congr 1; funext k
    have hint : (fun ω' => β ^ k * wbar * Real.exp (s * what k ω') *
          (Real.exp (pbar + s * xhat)
            - markup θ * Real.exp (pbar - logMarkup θ + s * ψhat k ω')))
        = (β ^ k * c) • ((fun ω' => Real.exp (s * a k ω'))
            - fun ω' => Real.exp (s * b k ω')) := by
      funext ω'
      have hM : markup θ * Real.exp (pbar - logMarkup θ + s * ψhat k ω')
          = Real.exp (pbar + s * ψhat k ω') := by
        rw [logMarkup, show pbar - Real.log (markup θ) + s * ψhat k ω'
            = (pbar + s * ψhat k ω') + -Real.log (markup θ) by ring, Real.exp_add,
          Real.exp_neg, Real.exp_log (markup_pos hθ)]
        have := (markup_pos hθ).ne'
        field_simp
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hM]
      simp only [ha, hb, hc, mul_add, Real.exp_add]
      ring
    rw [hint, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_pow]
    ring
  rw [hfun]
  -- term-by-term differentiation on `(-1, 1)`
  have hbd : ∀ (g : Ω → ℝ), (∀ ω', |g ω'| ≤ 2 * B) → ∀ s ∈ Set.Ioo (-1 : ℝ) 1,
      |𝔼.E t (fun ω' => g ω' * Real.exp (s * g ω')) ω| ≤ 2 * B * Real.exp (2 * B) := by
    intro g hg s hs
    refine 𝔼.abs_E_le (fun ω' => ?_) t ω
    have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hg ω') ?_ (Real.exp_pos _).le (by linarith)
    rw [Real.exp_le_exp]
    calc s * g ω' ≤ |s * g ω'| := le_abs_self _
      _ = |s| * |g ω'| := abs_mul _ _
      _ ≤ 1 * (2 * B) := mul_le_mul hs1 (hg ω') (abs_nonneg _) zero_le_one
      _ = 2 * B := one_mul _
  have hD := hasDerivAt_tsum_of_isPreconnected
    (u := fun k => (β * α) ^ k * (|c| * (2 * (2 * B * Real.exp (2 * B)))))
    (g := fun k s => (β * α) ^ k * (c * (𝔼.E t (fun ω' => Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => Real.exp (s * b k ω')) ω)))
    (g' := fun k s => (β * α) ^ k * (c * (𝔼.E t (fun ω' => a k ω' * Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => b k ω' * Real.exp (s * b k ω')) ω)))
    (t := Set.Ioo (-1 : ℝ) 1) (y₀ := 0) (y := 0)
    ((summable_geometric_of_lt_one hβα0 hβα1).mul_right _) isOpen_Ioo isPreconnected_Ioo
    (fun k s _ => (((hasDerivAt_E_exp 𝔼 (haB k) t ω s).sub
      (hasDerivAt_E_exp 𝔼 (hbB k) t ω s)).const_mul c).const_mul _)
    (fun k s hs => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβα0 k), abs_mul]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg c))
        (pow_nonneg hβα0 k)
      refine (abs_sub _ _).trans ?_
      linarith [hbd _ (haB k) s hs, hbd _ (hbB k) s hs])
    ⟨by norm_num, by norm_num⟩
    (by simp)
    ⟨by norm_num, by norm_num⟩
  refine hD.congr_deriv ?_
  rw [← tsum_mul_left]
  congr 1; funext k
  have hab : (fun ω' => a k ω' * Real.exp (0 * a k ω'))
      - (fun ω' => b k ω' * Real.exp (0 * b k ω')) = (fun _ => xhat) - ψhat k := by
    funext ω'; simp [ha, hb]
  rw [← Pi.sub_apply (𝔼.E t _), ← map_sub, hab, map_sub, 𝔼.const]
  simp only [Pi.sub_apply]
  ring

/-- **The log-linear reset rule behind (4.7)** (Woodford (2003), eq. (4.7), p. 223). The
first-order term of (4.4) at the zero-wage-inflation steady state vanishes if and only if
`p*_t = μ + (1 − βα) ∑ₖ (βα)ᵏ E_t ψ_{t+k|t}`, where `p*_t = p̄ + x̂` and
`ψ_{t+k|t} = ψ̄ + ψ̂ₖ` with `ψ̄ = p̄ − μ`. -/
theorem linear_reset_rule_iff {α β θ wbar pbar xhat B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hwbar : 0 < wbar) {ψhat : ℕ → Ω → ℝ} (hψ : ∀ k ω, |ψhat k ω| ≤ B)
    (t : ℕ) (ω : Ω) :
    wbar * Real.exp pbar * ∑' k, (β * α) ^ k * (xhat - 𝔼.E t (ψhat k) ω) = 0 ↔
      pbar + xhat = logMarkup θ + (1 - β * α) *
        ∑' k, (β * α) ^ k * 𝔼.E t (fun ω' => (pbar - logMarkup θ) + ψhat k ω') ω := by
  have hβα0 : 0 ≤ β * α := mul_nonneg hβ0 hα0
  have hβα1 : β * α < 1 := by nlinarith
  have hβα : |β * α| < 1 := by rwa [abs_of_nonneg hβα0]
  have hg := summable_geometric_of_lt_one hβα0 hβα1
  have hT := summable_geometric_bounded hβα (fun k ω' => 𝔼.abs_E_le (hψ k) t ω') ω
  set T := ∑' k, (β * α) ^ k * 𝔼.E t (ψhat k) ω with hTdef
  have h1 : ∑' k, (β * α) ^ k * (xhat - 𝔼.E t (ψhat k) ω) = xhat * (1 - β * α)⁻¹ - T := by
    simp_rw [mul_sub]
    rw [Summable.tsum_sub (hg.mul_right xhat) hT, tsum_mul_right,
      tsum_geometric_of_lt_one hβα0 hβα1]
    ring
  have h2 : ∑' k, (β * α) ^ k * 𝔼.E t (fun ω' => (pbar - logMarkup θ) + ψhat k ω') ω
      = (pbar - logMarkup θ) * (1 - β * α)⁻¹ + T := by
    have : ∀ k, 𝔼.E t (fun ω' => (pbar - logMarkup θ) + ψhat k ω') ω
        = (pbar - logMarkup θ) + 𝔼.E t (ψhat k) ω := by
      intro k
      have hf : (fun ω' => (pbar - logMarkup θ) + ψhat k ω')
          = (fun _ => pbar - logMarkup θ) + ψhat k := rfl
      rw [hf, map_add, 𝔼.const]; rfl
    simp_rw [this, mul_add]
    rw [Summable.tsum_add (hg.mul_right _) hT, tsum_mul_right,
      tsum_geometric_of_lt_one hβα0 hβα1, mul_comm]
  rw [h1, h2]
  have hc : wbar * Real.exp pbar ≠ 0 := (mul_pos hwbar (Real.exp_pos _)).ne'
  have hd : 1 - β * α ≠ 0 := by linarith
  constructor
  · intro h
    have h3 := (mul_eq_zero.mp h).resolve_left hc
    field_simp at h3 ⊢
    linarith
  · intro h
    have h3 : xhat * (1 - β * α)⁻¹ - T = 0 := by
      field_simp at h ⊢
      linarith
    rw [h3, mul_zero]


/-! ### Regularity of the reset problem from primitives (restated from Galí Ch. 6) -/

/-- **Primitive assumptions on the reset-wage problem** (Woodford (2003), pp. 222–223): Calvo
`α ≥ 0` and a discount bound `β ≥ 0` with `αβ < 1`; `θ > 1`; nominal discount factors
`0 < Q_{t,t+k} ≤ Q̄ βᵏ`; price levels and consumption in `[m, M̄]` with `m > 0`; a
nominal cost function `Ψ` twice differentiable at positive output, with `Ψ`, `Ψ'`,
`Ψ''` bounded, uniformly in the horizon and the state, on every compact range of
positive output. -/
def Primitives (α β θ Qb m Mx : ℝ) (Q P C : ℕ → Ω → ℝ) (Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ) :
    Prop :=
  0 ≤ α ∧ 0 ≤ β ∧ α * β < 1 ∧ 1 < θ ∧ 0 < m ∧
  (∀ k ω, 0 < Q k ω ∧ Q k ω ≤ Qb * β ^ k) ∧
  (∀ k ω, m ≤ P k ω ∧ P k ω ≤ Mx) ∧ (∀ k ω, m ≤ C k ω ∧ C k ω ≤ Mx) ∧
  (∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y) ∧
  (∀ k ω y, 0 < y → HasDerivAt (dΨ k ω) (d2Ψ k ω y) y) ∧
  (∀ y₁ y₂, 0 < y₁ → ∃ K, ∀ k ω y, y₁ ≤ y → y ≤ y₂ →
    |Ψ k ω y| ≤ K ∧ |dΨ k ω y| ≤ K ∧ |d2Ψ k ω y| ≤ K)

/-- Bounds on the demand shifter `P^θ C ∈ [m^θ m, M̄^θ M̄]` (Woodford (2003),
pp. 222–223). -/
theorem weight_bounds {θ m Mx : ℝ} (hθ : 0 ≤ θ) (hm : 0 < m) {P C : Ω → ℝ}
    (hP : ∀ ω, m ≤ P ω ∧ P ω ≤ Mx) (hC : ∀ ω, m ≤ C ω ∧ C ω ≤ Mx) (ω : Ω) :
    m ^ θ * m ≤ P ω ^ θ * C ω ∧ P ω ^ θ * C ω ≤ Mx ^ θ * Mx := by
  have hP0 : 0 ≤ P ω := hm.le.trans (hP ω).1
  have hC0 : 0 ≤ C ω := hm.le.trans (hC ω).1
  refine ⟨mul_le_mul (Real.rpow_le_rpow hm.le (hP ω).1 hθ) (hC ω).1 hm.le
    (Real.rpow_nonneg hP0 _), mul_le_mul (Real.rpow_le_rpow hP0 (hP ω).2 hθ) (hC ω).2 hC0
    (Real.rpow_nonneg (hP0.trans (hP ω).2) _)⟩

/-- **Demand stays in a compact range of positive output** when the reset wage
ranges over `[lo, hi] ⊂ (0, ∞)` (Woodford (2003), eq. (4.2), p. 221). -/
theorem demand_bounds {θ m Mx lo hi z : ℝ} (hθ : 0 ≤ θ) (hm : 0 < m) (hlo : 0 < lo)
    (hz1 : lo ≤ z) (hz2 : z ≤ hi) {P C : Ω → ℝ} (hP : ∀ ω, m ≤ P ω ∧ P ω ≤ Mx)
    (hC : ∀ ω, m ≤ C ω ∧ C ω ≤ Mx) (ω : Ω) :
    hi ^ (-θ) * (m ^ θ * m) ≤ demand θ z P C ω ∧
      demand θ z P C ω ≤ lo ^ (-θ) * (Mx ^ θ * Mx) := by
  have hz : 0 < z := hlo.trans_le hz1
  have hPpos : ∀ ω, 0 < P ω := fun ω => hm.trans_le (hP ω).1
  obtain ⟨hw1, hw2⟩ := weight_bounds hθ hm hP hC ω
  rw [demand_eq hz hPpos ω]
  have hm0 : 0 ≤ m ^ θ * m := by positivity
  exact ⟨mul_le_mul (Real.rpow_le_rpow_of_nonpos hz hz2 (by linarith)) hw1 hm0
      (Real.rpow_nonneg hz.le _),
    mul_le_mul (Real.rpow_le_rpow_of_nonpos hlo hz1 (by linarith)) hw2 (hm0.trans hw1)
      (Real.rpow_nonneg hlo.le _)⟩

/-- Marginal profit in factored form:
`((1 − θ)/P*) Q Y (P* − M Ψ') = (1 − θ) Q P^θ C (P*^{−θ} − M P*^{−θ−1} Ψ')`
(Woodford (2003), pp. 222–223). -/
theorem profitDeriv_eq {θ z : ℝ} (hz : 0 < z) {Q P C : Ω → ℝ} (dΨ : Ω → ℝ → ℝ)
    (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    profitDeriv θ Q P C dΨ z ω = (1 - θ) * Q ω * (P ω ^ θ * C ω) *
      (z ^ (-θ) - markup θ * (z ^ (-θ - 1) * dΨ ω (demand θ z P C ω))) := by
  unfold profitDeriv focTerm
  rw [demand_eq hz hP ω, Real.rpow_sub_one hz.ne']
  field_simp

/-- The derivative of marginal profit in the reset wage (Woodford (2003), pp. 222–223). -/
noncomputable def profitDeriv2 (θ : ℝ) (Q P C : Ω → ℝ) (dΨ d2Ψ : Ω → ℝ → ℝ) (z : ℝ) :
    Ω → ℝ :=
  fun ω => (1 - θ) * Q ω * (P ω ^ θ * C ω) * (-θ * z ^ (-θ - 1) - markup θ *
    ((-θ - 1) * z ^ (-θ - 1 - 1) * dΨ ω (demand θ z P C ω)
      + z ^ (-θ - 1) * (d2Ψ ω (demand θ z P C ω) * (-θ * demand θ z P C ω / z))))

/-- Marginal profit is differentiable in the reset wage, with derivative
`profitDeriv2` (Woodford (2003), pp. 222–223). -/
theorem hasDerivAt_profitDeriv {θ z : ℝ} (hz : 0 < z) {Q P C : Ω → ℝ}
    {dΨ d2Ψ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hdΨ : ∀ ω y, 0 < y → HasDerivAt (dΨ ω) (d2Ψ ω y) y) (ω : Ω) :
    HasDerivAt (fun x => profitDeriv θ Q P C dΨ x ω) (profitDeriv2 θ Q P C dΨ d2Ψ z ω) z := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (-θ)) (-θ * z ^ (-θ - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz.ne')
  have h2 : HasDerivAt (fun x : ℝ => x ^ (-θ - 1)) ((-θ - 1) * z ^ (-θ - 1 - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz.ne')
  have h3 : HasDerivAt (fun x => dΨ ω (demand θ x P C ω))
      (d2Ψ ω (demand θ z P C ω) * (-θ * demand θ z P C ω / z)) z :=
    (hdΨ ω _ (demand_pos hz hP hC ω)).comp z (hasDerivAt_demand hz hP ω)
  have hG := (HasDerivAt.sub h1 ((HasDerivAt.mul h2 h3).const_mul (markup θ))).const_mul
    ((1 - θ) * Q ω * (P ω ^ θ * C ω))
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hz] with x hx
  exact profitDeriv_eq hx dΨ hP ω

/-- A bound on marginal profit on prices `≥ lo > 0` (Woodford (2003), pp. 222–223). -/
theorem abs_profitDeriv_le {θ z lo Qm W K : ℝ} (hθ : 1 < θ) (hlo : 0 < lo) (hz : lo ≤ z)
    {Q P C : Ω → ℝ} {dΨ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) (hQ0 : 0 < Q ω)
    (hQ : Q ω ≤ Qm) (hW0 : 0 ≤ P ω ^ θ * C ω) (hW : P ω ^ θ * C ω ≤ W)
    (hd : |dΨ ω (demand θ z P C ω)| ≤ K) :
    |profitDeriv θ Q P C dΨ z ω|
      ≤ (θ - 1) * Qm * W * (lo ^ (-θ) + markup θ * (lo ^ (-θ - 1) * K)) := by
  have hz0 : 0 < z := hlo.trans_le hz
  rw [profitDeriv_eq hz0 dΨ hP ω]
  have hM := markup_pos hθ
  have a0 : 0 ≤ z ^ (-θ) := Real.rpow_nonneg hz0.le _
  have a1 : 0 ≤ z ^ (-θ - 1) := Real.rpow_nonneg hz0.le _
  have b0 : z ^ (-θ) ≤ lo ^ (-θ) := Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have b1 : z ^ (-θ - 1) ≤ lo ^ (-θ - 1) := Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have hc : |(1 - θ) * Q ω * (P ω ^ θ * C ω)| ≤ (θ - 1) * Qm * W := by
    rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : 1 - θ ≤ 0), abs_of_pos hQ0,
      abs_of_nonneg hW0, neg_sub]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hQ (by linarith)) hW hW0
      (mul_nonneg (by linarith) (hQ0.le.trans hQ))
  have hi : |z ^ (-θ) - markup θ * (z ^ (-θ - 1) * dΨ ω (demand θ z P C ω))|
      ≤ lo ^ (-θ) + markup θ * (lo ^ (-θ - 1) * K) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg a0, abs_mul, abs_of_pos hM, abs_mul, abs_of_nonneg a1]
    gcongr
  rw [abs_mul]
  exact mul_le_mul hc hi (abs_nonneg _)
    (mul_nonneg (mul_nonneg (by linarith) (hQ0.le.trans hQ)) (hW0.trans hW))

/-- A bound on the derivative of marginal profit on prices `≥ lo > 0`
(Woodford (2003), pp. 222–223). -/
theorem abs_profitDeriv2_le {θ z lo Qm W K Yh : ℝ} (hθ : 1 < θ) (hlo : 0 < lo)
    (hz : lo ≤ z) {Q P C : Ω → ℝ} {dΨ d2Ψ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω)
    (hC : ∀ ω, 0 < C ω) (ω : Ω) (hQ0 : 0 < Q ω) (hQ : Q ω ≤ Qm) (hW0 : 0 ≤ P ω ^ θ * C ω)
    (hW : P ω ^ θ * C ω ≤ W) (hd : |dΨ ω (demand θ z P C ω)| ≤ K)
    (hd2 : |d2Ψ ω (demand θ z P C ω)| ≤ K) (hY : demand θ z P C ω ≤ Yh) :
    |profitDeriv2 θ Q P C dΨ d2Ψ z ω| ≤ (θ - 1) * Qm * W * (θ * lo ^ (-θ - 1)
      + markup θ * ((θ + 1) * lo ^ (-θ - 1 - 1) * K + lo ^ (-θ - 1) * (K * (θ * (Yh / lo))))) := by
  have hz0 : 0 < z := hlo.trans_le hz
  have hM := markup_pos hθ
  have hθ0 : 0 < θ := by linarith
  have hY0 := demand_pos (θ := θ) hz0 hP hC ω
  have a1 : 0 ≤ z ^ (-θ - 1) := Real.rpow_nonneg hz0.le _
  have a2 : 0 ≤ z ^ (-θ - 1 - 1) := Real.rpow_nonneg hz0.le _
  have b1 : z ^ (-θ - 1) ≤ lo ^ (-θ - 1) := Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have b2 : z ^ (-θ - 1 - 1) ≤ lo ^ (-θ - 1 - 1) :=
    Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have bY : demand θ z P C ω / z ≤ Yh / lo := div_le_div₀ (hY0.le.trans hY) hY hlo hz
  have hK : 0 ≤ K := (abs_nonneg _).trans hd
  have hc : |(1 - θ) * Q ω * (P ω ^ θ * C ω)| ≤ (θ - 1) * Qm * W := by
    rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : 1 - θ ≤ 0), abs_of_pos hQ0,
      abs_of_nonneg hW0, neg_sub]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hQ (by linarith)) hW hW0
      (mul_nonneg (by linarith) (hQ0.le.trans hQ))
  have e1 : |-θ * z ^ (-θ - 1)| = θ * z ^ (-θ - 1) := by
    rw [abs_mul, abs_neg, abs_of_pos hθ0, abs_of_nonneg a1]
  have e2 : |(-θ - 1) * z ^ (-θ - 1 - 1) * dΨ ω (demand θ z P C ω)|
      = (θ + 1) * z ^ (-θ - 1 - 1) * |dΨ ω (demand θ z P C ω)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg a2, abs_of_nonpos (by linarith : -θ - 1 ≤ 0)]
    ring
  have e3 : |z ^ (-θ - 1) * (d2Ψ ω (demand θ z P C ω) * (-θ * demand θ z P C ω / z))|
      = z ^ (-θ - 1) * (|d2Ψ ω (demand θ z P C ω)| * (θ * (demand θ z P C ω / z))) := by
    have hn : -θ * demand θ z P C ω / z ≤ 0 := by
      rw [neg_mul, neg_div]; exact neg_nonpos.mpr (by positivity)
    rw [abs_mul, abs_mul, abs_of_nonneg a1, abs_of_nonpos hn]
    ring
  have hi : |-θ * z ^ (-θ - 1) - markup θ *
      ((-θ - 1) * z ^ (-θ - 1 - 1) * dΨ ω (demand θ z P C ω)
        + z ^ (-θ - 1) * (d2Ψ ω (demand θ z P C ω) * (-θ * demand θ z P C ω / z)))|
      ≤ θ * lo ^ (-θ - 1)
        + markup θ * ((θ + 1) * lo ^ (-θ - 1 - 1) * K + lo ^ (-θ - 1) * (K * (θ * (Yh / lo)))) := by
    refine (abs_sub _ _).trans ?_
    rw [e1, abs_mul, abs_of_pos hM]
    refine add_le_add (by gcongr) (mul_le_mul_of_nonneg_left ?_ hM.le)
    refine (abs_add_le _ _).trans ?_
    rw [e2, e3]
    have hYz : 0 ≤ demand θ z P C ω / z := by positivity
    gcongr
  unfold profitDeriv2
  rw [abs_mul]
  exact mul_le_mul hc hi (abs_nonneg _)
    (mul_nonneg (mul_nonneg (by linarith) (hQ0.le.trans hQ)) (hW0.trans hW))

/-- **Local Lipschitz bounds on marginal profit from primitives** (Woodford (2003),
pp. 222–223): under `Primitives`, marginal profit is Lipschitz in the reset wage near
every positive price, uniformly in the state. -/
theorem lipschitz_of_primitives {α β θ Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives α β θ Qb m Mx Q P C Ψ dΨ d2Ψ) :
    ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv θ (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv θ (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y| := by
  obtain ⟨-, hβ, -, hθ, hm, hQ, hP, hC, -, hdΨ, hΨb⟩ := hprim
  intro k y hy
  have hθ0 : 0 ≤ θ := by linarith
  have hPpos : ∀ ω, 0 < P k ω := fun ω => hm.trans_le (hP k ω).1
  have hCpos : ∀ ω, 0 < C k ω := fun ω => hm.trans_le (hC k ω).1
  set lo := y / 2 with hlo_def
  set hi := 2 * y with hhi_def
  have hlo : 0 < lo := by positivity
  set Klo := m ^ θ * m
  set Khi := Mx ^ θ * Mx
  set Yh := lo ^ (-θ) * Khi
  have hy1 : 0 < hi ^ (-θ) * Klo := by positivity
  obtain ⟨K, hK⟩ := hΨb (hi ^ (-θ) * Klo) Yh hy1
  set L₀ := (θ - 1) * (|Qb| * β ^ k) * Khi * (θ * lo ^ (-θ - 1) + markup θ *
    ((θ + 1) * lo ^ (-θ - 1 - 1) * |K| + lo ^ (-θ - 1) * (|K| * (θ * (Yh / lo)))))
  refine ⟨max L₀ 0, le_max_right _ _, lo, hlo, fun z hz ω => ?_⟩
  have hball : ∀ x ∈ Metric.ball y lo, lo ≤ x ∧ x ≤ hi := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    constructor <;> linarith
  have hd : ∀ x ∈ Metric.ball y lo, HasDerivWithinAt
      (fun x => profitDeriv θ (Q k) (P k) (C k) (dΨ k) x ω)
      (profitDeriv2 θ (Q k) (P k) (C k) (dΨ k) (d2Ψ k) x ω) (Metric.ball y lo) x :=
    fun x hx => (hasDerivAt_profitDeriv (hlo.trans_le (hball x hx).1) hPpos hCpos (hdΨ k)
      ω).hasDerivWithinAt
  have hb : ∀ x ∈ Metric.ball y lo,
      ‖profitDeriv2 θ (Q k) (P k) (C k) (dΨ k) (d2Ψ k) x ω‖ ≤ max L₀ 0 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hball x hx
    obtain ⟨hY1, hY2⟩ := demand_bounds hθ0 hm hlo hx1 hx2 (hP k) (hC k) ω
    obtain ⟨hw1, hw2⟩ := weight_bounds hθ0 hm (hP k) (hC k) ω
    obtain ⟨-, hK1, hK2⟩ := hK k ω _ hY1 hY2
    have hQm : Q k ω ≤ |Qb| * β ^ k :=
      (hQ k ω).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hβ k))
    rw [Real.norm_eq_abs]
    exact (abs_profitDeriv2_le hθ hlo hx1 hPpos hCpos ω (hQ k ω).1 hQm
      ((by positivity : (0 : ℝ) ≤ m ^ θ * m).trans hw1) hw2 (hK1.trans (le_abs_self _))
      (hK2.trans (le_abs_self _)) hY2).trans (le_max_left _ _)
  have hyb : y ∈ Metric.ball y lo := Metric.mem_ball_self hlo
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_ball y lo) hyb hz
  simpa only [Real.norm_eq_abs] using this

/-- **Domination of marginal profit from primitives** (Woodford (2003), pp. 222–223): under
`Primitives`, on every interval `(a, b)` with `a > 0`, marginal profit at horizon `k`
is bounded by `uₖ = c βᵏ`, and `∑ αᵏ uₖ < ∞` since `αβ < 1`. -/
theorem dominated_of_primitives {α β θ Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives α β θ Qb m Mx Q P C Ψ dΨ d2Ψ) :
    ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |α| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω, |profitDeriv θ (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k := by
  obtain ⟨hα, hβ, hαβ, hθ, hm, hQ, hP, hC, -, -, hΨb⟩ := hprim
  intro a b ha
  have hθ0 : 0 ≤ θ := by linarith
  set hi := max b a
  have hhi : 0 < hi := ha.trans_le (le_max_right _ _)
  set Klo := m ^ θ * m
  set Khi := Mx ^ θ * Mx
  obtain ⟨K, hK⟩ := hΨb (hi ^ (-θ) * Klo) (a ^ (-θ) * Khi) (by positivity)
  set c := (θ - 1) * |Qb| * Khi * (a ^ (-θ) + markup θ * (a ^ (-θ - 1) * |K|))
  refine ⟨fun k => (θ - 1) * (|Qb| * β ^ k) * Khi * (a ^ (-θ) + markup θ * (a ^ (-θ - 1) * |K|)),
    ?_, fun k y hy ω => ?_⟩
  · refine ((summable_geometric_of_lt_one (mul_nonneg hα hβ) hαβ).mul_left c).congr
      fun k => ?_
    rw [abs_of_nonneg hα, mul_pow]
    ring
  · have hy1 : a ≤ y := hy.1.le
    have hy2 : y ≤ hi := hy.2.le.trans (le_max_left _ _)
    have hPpos : ∀ ω, 0 < P k ω := fun ω => hm.trans_le (hP k ω).1
    obtain ⟨hY1, hY2⟩ := demand_bounds hθ0 hm ha hy1 hy2 (hP k) (hC k) ω
    obtain ⟨hw1, hw2⟩ := weight_bounds hθ0 hm (hP k) (hC k) ω
    obtain ⟨-, hK1, -⟩ := hK k ω _ hY1 hY2
    have hQm : Q k ω ≤ |Qb| * β ^ k :=
      (hQ k ω).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hβ k))
    exact abs_profitDeriv_le hθ ha hy1 hPpos ω (hQ k ω).1 hQm
      ((by positivity : (0 : ℝ) ≤ m ^ θ * m).trans hw1) hw2 (hK1.trans (le_abs_self _))

/-- **Convergence of the objective from primitives** (Woodford (2003), pp. 222–223): under
`Primitives`, the reset-wage objective converges at every positive price. -/
theorem summable_profit_of_primitives {α β θ Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives α β θ Qb m Mx Q P C Ψ dΨ d2Ψ) (t : ℕ)
    (ω : Ω) : ∀ y, 0 < y →
      Summable fun k => α ^ k * 𝔼.E t (profit θ (Q k) (P k) (C k) (Ψ k) y) ω := by
  obtain ⟨hα, hβ, hαβ, hθ, hm, hQ, hP, hC, -, -, hΨb⟩ := hprim
  intro y hy
  have hθ0 : 0 ≤ θ := by linarith
  set Klo := m ^ θ * m
  set Khi := Mx ^ θ * Mx
  obtain ⟨K, hK⟩ := hΨb (y ^ (-θ) * Klo) (y ^ (-θ) * Khi) (by positivity)
  set c := |Qb| * (y * |y ^ (-θ) * Khi| + |K|)
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (mul_nonneg hα hβ) hαβ).mul_left c) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hα]
  have hb : ∀ ω', |profit θ (Q k) (P k) (C k) (Ψ k) y ω'| ≤ |Qb| * β ^ k *
      (y * |y ^ (-θ) * Khi| + |K|) := by
    intro ω'
    obtain ⟨hY1, hY2⟩ := demand_bounds hθ0 hm hy le_rfl le_rfl (hP k) (hC k) ω'
    obtain ⟨hK0, -, -⟩ := hK k ω' _ hY1 hY2
    have hY0 : 0 < demand θ y (P k) (C k) ω' :=
      demand_pos hy (fun ω => hm.trans_le (hP k ω).1) (fun ω => hm.trans_le (hC k ω).1) ω'
    have hQm : Q k ω' ≤ |Qb| * β ^ k :=
      (hQ k ω').2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hβ k))
    unfold profit
    rw [abs_mul, abs_of_pos (hQ k ω').1]
    refine mul_le_mul hQm ((abs_sub _ _).trans (add_le_add ?_
      (hK0.trans (le_abs_self _)))) (abs_nonneg _) ((hQ k ω').1.le.trans hQm)
    rw [abs_mul, abs_of_pos hy, abs_of_pos hY0]
    exact mul_le_mul_of_nonneg_left (hY2.trans (le_abs_self _)) hy.le
  calc α ^ k * |𝔼.E t (profit θ (Q k) (P k) (C k) (Ψ k) y) ω|
      ≤ α ^ k * (|Qb| * β ^ k * (y * |y ^ (-θ) * Khi| + |K|)) :=
        mul_le_mul_of_nonneg_left (𝔼.abs_E_le hb t ω) (pow_nonneg hα k)
    _ = c * (α * β) ^ k := by rw [mul_pow]; ring

/-- **The derivative of the reset-wage objective, from primitives only**
(Woodford (2003), eq. (4.4), p. 222): under `Primitives`, at every positive price the
objective has derivative `((1 − θ)/P*) ∑ₖ αᵏ E_t[Q_{t,t+k} Y_{t+k|t}(P* − M Ψ'_{t+k|t})]`. -/
theorem hasDerivAt_objective_of_primitives {α β θ Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives α β θ Qb m Mx Q P C Ψ dΨ d2Ψ) (t : ℕ)
    (ω : Ω) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => objective 𝔼 α θ Q P C Ψ t z ω)
      ((1 - θ) / x * focSum 𝔼 α θ Q P C dΨ t x ω) x := by
  have hLip := lipschitz_of_primitives hprim
  have hloc := dominated_of_primitives hprim
  have hs := summable_profit_of_primitives 𝔼 hprim t ω
  obtain ⟨-, -, -, hθ, hm, -, hP, hC, hΨ, -, -⟩ := hprim
  exact hasDerivAt_objective_of_pos 𝔼 hθ (fun k ω => hm.trans_le (hP k ω).1)
    (fun k ω => hm.trans_le (hC k ω).1) hΨ hLip hloc t ω hs hx

/-- **(4.4) is necessary, from primitives only** (Woodford (2003), eq. (4.4), p. 222): under
`Primitives`, a local maximum `P* > 0` of the reset-wage objective satisfies (4.4). -/
theorem foc_of_isLocalMax_of_primitives {α β θ Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives α β θ Qb m Mx Q P C Ψ dΨ d2Ψ) {t : ℕ}
    {ω : Ω} {x : ℝ} (hx : 0 < x)
    (hmax : IsLocalMax (fun z => objective 𝔼 α θ Q P C Ψ t z ω) x) :
    focSum 𝔼 α θ Q P C dΨ t x ω = 0 :=
  foc_of_isLocalMax 𝔼 hprim.2.2.2.1 hx (hasDerivAt_objective_of_primitives 𝔼 hprim t ω hx) hmax

/-- **(4.4) characterises the optimal reset wage, from primitives only**
(Woodford (2003), eq. (4.4), p. 222): under `Primitives`, convex costs (`Ψ'' ≥ 0`) and the
a current-period discount factor bounded away from zero, a positive wage
maximises the objective over all positive wages if and only if it satisfies (4.4), and it is
then the unique maximiser. -/
theorem isMaxOn_iff_foc_of_primitives {α β θ Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives α β θ Qb m Mx Q P C Ψ dΨ d2Ψ)
    (hconv : ∀ k ω y, 0 < y → 0 ≤ d2Ψ k ω y) (hQ0 : ∃ q, 0 < q ∧ ∀ ω, q ≤ Q 0 ω) (t : ℕ)
    (ω : Ω) {x : ℝ} (hx : 0 < x) :
    (IsMaxOn (fun z => objective 𝔼 α θ Q P C Ψ t z ω) (Set.Ioi 0) x ↔
        focSum 𝔼 α θ Q P C dΨ t x ω = 0) ∧
      (focSum 𝔼 α θ Q P C dΨ t x ω = 0 → ∀ y, 0 < y → y ≠ x →
        objective 𝔼 α θ Q P C Ψ t y ω < objective 𝔼 α θ Q P C Ψ t x ω) := by
  have hLip := lipschitz_of_primitives hprim
  have hloc := dominated_of_primitives hprim
  have hs := summable_profit_of_primitives 𝔼 hprim t ω
  obtain ⟨hα, -, -, hθ, hm, hQ, hP, hC, hΨ, hdΨ, -⟩ := hprim
  have hθ0 : 0 ≤ θ := by linarith
  have hmono : ∀ k ω, MonotoneOn (dΨ k ω) (Set.Ioi 0) := by
    intro k ω
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun y hy => (hdΨ k ω y hy).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ioi]
      exact fun y hy => (hdΨ k ω y hy).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro y hy
      rw [(hdΨ k ω y hy).deriv]
      exact hconv k ω y hy
  have hpos : 0 < 𝔼.E t (fun ω' => Q 0 ω' * (P 0 ω' ^ θ * C 0 ω')) ω := by
    obtain ⟨q, hq, hqle⟩ := hQ0
    have hc : 0 < q * (m ^ θ * m) := by positivity
    have hle : (fun _ : Ω => q * (m ^ θ * m))
        ≤ fun ω' => Q 0 ω' * (P 0 ω' ^ θ * C 0 ω') := fun ω' =>
      mul_le_mul (hqle ω') (weight_bounds hθ0 hm (hP 0) (hC 0) ω').1 (by positivity)
        (hQ 0 ω').1.le
    have := 𝔼.mono t hle ω
    rw [𝔼.const] at this
    exact hc.trans_le this
  exact isMaxOn_iff_foc 𝔼 hθ hα (fun k ω => (hQ k ω).1) (fun k ω => hm.trans_le (hP k ω).1)
    (fun k ω => hm.trans_le (hC k ω).1) hΨ hmono hLip hloc t ω hs hpos hx



/-! ### The wage setter's problem (4.3)–(4.5) -/

/-- Woodford (2003), eq. (4.3), p. 222: the discount factors of a wage setter,
`Q_k = βᵏ Λ_{t+k}`, with `Λ` the marginal utility of nominal income. -/
def wageQ (β : ℝ) (Λ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun k ω => β ^ k * Λ k ω

/-- Woodford (2003), eq. (4.3), p. 222: the money value `v(h; ξ_{t+k})/Λ_{t+k}` of the
disutility of supplying `h` hours (the wage setter's nominal cost). -/
noncomputable def wageCost (Λ : ℕ → Ω → ℝ) (v : ℕ → Ω → ℝ → ℝ) : ℕ → Ω → ℝ → ℝ :=
  fun k ω h => v k ω h / Λ k ω

/-- Woodford (2003), eq. (4.3), p. 222: the objective of the supplier of a labour type that
resets its wage to `w` at date `t`,
`∑ₖ (α_w β)ᵏ E_t[Λ_{t+k} w h_{t+k}(w) − v(h_{t+k}(w); ξ_{t+k})]`, with labour demand (4.2)
`h_{t+k}(w) = H_{t+k} (w/W_{t+k})^{−θ_w}` (`demand θ w W H`), a genuine infinite sum. -/
noncomputable def wageObjective (α β θ : ℝ) (Λ W H : ℕ → Ω → ℝ) (v : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (w : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, (α * β) ^ k * 𝔼.E t (fun ω' => Λ k ω' * w * demand θ w (W k) (H k) ω'
    - v k ω' (demand θ w (W k) (H k) ω')) ω

/-- Woodford (2003), eq. (4.3), p. 222: the wage-setting objective is the generic Calvo reset
objective with discount factors `βᵏ Λ_{t+k}`, "price index" `W`, "demand shifter" `H` and
nominal cost `v/Λ`. -/
theorem wageObjective_eq {α β θ : ℝ} {Λ W H : ℕ → Ω → ℝ} (v : ℕ → Ω → ℝ → ℝ)
    (hΛ : ∀ k ω, 0 < Λ k ω) (t : ℕ) (w : ℝ) :
    wageObjective 𝔼 α β θ Λ W H v t w = objective 𝔼 α θ (wageQ β Λ) W H (wageCost Λ v) t w := by
  funext ω
  unfold wageObjective objective
  congr 1
  funext k
  have hfun : profit θ (wageQ β Λ k) (W k) (H k) (wageCost Λ v k) w
      = (β ^ k) • fun ω' => Λ k ω' * w * demand θ w (W k) (H k) ω'
        - v k ω' (demand θ w (W k) (H k) ω') := by
    funext ω'
    simp only [profit, wageQ, wageCost, Pi.smul_apply, smul_eq_mul]
    have := (hΛ k ω').ne'
    field_simp
  rw [hfun, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Woodford (2003), eq. (4.5), p. 223, and footnote 73: with `Λ = u_c/P`, the nominal marginal
cost of supplying hours, `v_h/Λ`, is the marginal rate of substitution `V = v_h/u_c` between
work and consumption expressed in money, `V P`. -/
theorem mrs_nominal_eq {vh uc P : ℝ} (huc : uc ≠ 0) (hP : P ≠ 0) :
    vh / (uc / P) = vh / uc * P := by
  field_simp

/-- Woodford (2003), eq. (4.4), p. 222: the left-hand side
`∑ₖ α_wᵏ E_t[Q_{t,t+k} H_{t+k} W_{t+k}^{θ_w} (w − μ_w V_{t+k} P_{t+k})]` with the stochastic
discount factor `Q_{t,t+k} = βᵏ Λ_{t+k}/Λ_t` (`Λ 0` is date-`t` marginal utility) and
`VP k ω h` the nominal MRS of the supplier when it works `h` hours. -/
noncomputable def eq44LHS (α β θ : ℝ) (Λ W H : ℕ → Ω → ℝ) (VP : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (w : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, α ^ k * 𝔼.E t (fun ω' => β ^ k * Λ k ω' / Λ 0 ω' * H k ω' * W k ω' ^ θ *
    (w - markup θ * VP k ω' (demand θ w (W k) (H k) ω'))) ω

/-- Woodford (2003), eq. (4.4), p. 222: the first-order condition `focSum = 0` of the generic
reset problem (the derivative of (4.3) is `((1 − θ_w)/w) focSum`) holds iff (4.4) holds, when
`1/Λ_t` is known at `t` and expectations have the pull-out property (the common factor
`w^{−θ_w}` is dropped, as in the book). -/
theorem eq44_iff_focSum {α β θ w : ℝ} (hw : 0 < w) {Λ W H : ℕ → Ω → ℝ}
    {VP : ℕ → Ω → ℝ → ℝ} (hΛ : ∀ k ω, 0 < Λ k ω) (hW : ∀ k ω, 0 < W k ω) {t : ℕ}
    (hpull : 𝔼.PullOut) (hΛ0 : 𝔼.E t (fun ω => (Λ 0 ω)⁻¹) = fun ω => (Λ 0 ω)⁻¹) (ω : Ω) :
    focSum 𝔼 α θ (wageQ β Λ) W H VP t w ω = 0 ↔ eq44LHS 𝔼 α β θ Λ W H VP t w ω = 0 := by
  set X : ℕ → Ω → ℝ := fun k ω' => β ^ k * Λ k ω' * H k ω' * W k ω' ^ θ *
    (w - markup θ * VP k ω' (demand θ w (W k) (H k) ω')) with hX
  have h1 : focSum 𝔼 α θ (wageQ β Λ) W H VP t w ω
      = w ^ (-θ) * ∑' k, α ^ k * 𝔼.E t (X k) ω := by
    unfold focSum
    rw [← tsum_mul_left]
    congr 1
    funext k
    have hk : focTerm θ (wageQ β Λ k) (W k) (H k) (VP k) w = w ^ (-θ) • X k := by
      funext ω'
      simp only [focTerm, wageQ, Pi.smul_apply, smul_eq_mul, hX]
      rw [demand_eq hw (hW k) ω']
      ring
    rw [hk, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have h2 : eq44LHS 𝔼 α β θ Λ W H VP t w ω
      = (Λ 0 ω)⁻¹ * ∑' k, α ^ k * 𝔼.E t (X k) ω := by
    unfold eq44LHS
    rw [← tsum_mul_left]
    congr 1
    funext k
    have hk : (fun ω' => β ^ k * Λ k ω' / Λ 0 ω' * H k ω' * W k ω' ^ θ *
        (w - markup θ * VP k ω' (demand θ w (W k) (H k) ω')))
        = (fun ω' => (Λ 0 ω')⁻¹) * X k := by
      funext ω'
      simp only [Pi.mul_apply, hX]
      ring
    rw [hk, hpull t _ _ hΛ0, Pi.mul_apply]
    ring
  rw [h1, h2]
  have hw' : w ^ (-θ) ≠ 0 := (Real.rpow_pos_of_pos hw _).ne'
  have hl : (Λ 0 ω)⁻¹ ≠ 0 := inv_ne_zero (hΛ 0 ω).ne'
  constructor
  · intro h
    rw [(mul_eq_zero.mp h).resolve_left hw', mul_zero]
  · intro h
    rw [(mul_eq_zero.mp h).resolve_left hl, mul_zero]

/-- Woodford (2003), eqs. (4.3)–(4.4), pp. 222–223 (**(4.4) characterises the optimal wage**):
if the disutility of work `v(·; ξ)` is differentiable with nondecreasing marginal disutility
`v_h` (convex `v`), then under the regularity conditions of `isMaxOn_iff_foc` (local Lipschitz
and domination of marginal payoffs, convergence of the objective, positive current weight) a
wage `w > 0` maximises the objective (4.3) over all positive wages iff the first-order
condition holds, and it is then the unique (strict) maximiser. -/
theorem wage_isMaxOn_iff_foc {α β θ : ℝ} (hθ : 1 < θ) (hα : 0 ≤ α) (hβ : 0 < β)
    {Λ W H : ℕ → Ω → ℝ} {v vh : ℕ → Ω → ℝ → ℝ} (hΛ : ∀ k ω, 0 < Λ k ω)
    (hW : ∀ k ω, 0 < W k ω) (hH : ∀ k ω, 0 < H k ω)
    (hv : ∀ k ω h, 0 < h → HasDerivAt (v k ω) (vh k ω h) h)
    (hconv : ∀ k ω, MonotoneOn (vh k ω) (Set.Ioi 0))
    (hLip : ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv θ (wageQ β Λ k) (W k) (H k) (wageCost Λ vh k) z ω
        - profitDeriv θ (wageQ β Λ k) (W k) (H k) (wageCost Λ vh k) y ω| ≤ L * |z - y|)
    (hloc : ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |α| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω,
        |profitDeriv θ (wageQ β Λ k) (W k) (H k) (wageCost Λ vh k) y ω| ≤ u k)
    (t : ℕ) (ω : Ω)
    (hs : ∀ y, 0 < y → Summable fun k =>
      α ^ k * 𝔼.E t (profit θ (wageQ β Λ k) (W k) (H k) (wageCost Λ v k) y) ω)
    (hpos : 0 < 𝔼.E t (fun ω' => Λ 0 ω' * (W 0 ω' ^ θ * H 0 ω')) ω) {w : ℝ} (hw : 0 < w) :
    (IsMaxOn (fun z => wageObjective 𝔼 α β θ Λ W H v t z ω) (Set.Ioi 0) w ↔
        focSum 𝔼 α θ (wageQ β Λ) W H (wageCost Λ vh) t w ω = 0) ∧
      (focSum 𝔼 α θ (wageQ β Λ) W H (wageCost Λ vh) t w ω = 0 → ∀ y, 0 < y → y ≠ w →
        wageObjective 𝔼 α β θ Λ W H v t y ω < wageObjective 𝔼 α β θ Λ W H v t w ω) := by
  have hQ : ∀ k ω, 0 < wageQ β Λ k ω := fun k ω => mul_pos (pow_pos hβ k) (hΛ k ω)
  have hΨ : ∀ k ω y, 0 < y → HasDerivAt (wageCost Λ v k ω) (wageCost Λ vh k ω y) y :=
    fun k ω y hy => (hv k ω y hy).div_const (Λ k ω)
  have hc : ∀ k ω, MonotoneOn (wageCost Λ vh k ω) (Set.Ioi 0) := fun k ω a ha b hb hab =>
    div_le_div_of_nonneg_right (hconv k ω ha hb hab) (hΛ k ω).le
  have hpos' : 0 < 𝔼.E t (fun ω' => wageQ β Λ 0 ω' * (W 0 ω' ^ θ * H 0 ω')) ω := by
    simpa [wageQ] using hpos
  have h := isMaxOn_iff_foc 𝔼 hθ hα hQ hW hH hΨ hc hLip hloc t ω hs hpos' hw
  simp only [← wageObjective_eq 𝔼 v hΛ t] at h
  exact h

/-- Woodford (2003), p. 223 (**flexible wages**): with `α_w = 0` and current variables known at
`t`, the first-order condition holds iff `w = μ_w V_t(h_t(w)) P_t`, the desired markup over the
nominal MRS (`VP 0` is the nominal MRS at date `t`). -/
theorem wage_flexible_iff {β θ w : ℝ} (hβ : 0 < β) (hw : 0 < w) {Λ W H : ℕ → Ω → ℝ}
    {VP : ℕ → Ω → ℝ → ℝ} (hΛ : ∀ ω, 0 < Λ 0 ω) (hW : ∀ ω, 0 < W 0 ω) (hH : ∀ ω, 0 < H 0 ω)
    {t : ℕ} (hknown : 𝔼.E t (focTerm θ (wageQ β Λ 0) (W 0) (H 0) (VP 0) w)
      = focTerm θ (wageQ β Λ 0) (W 0) (H 0) (VP 0) w) (ω : Ω) :
    focSum 𝔼 0 θ (wageQ β Λ) W H VP t w ω = 0 ↔
      w = markup θ * VP 0 ω (demand θ w (W 0) (H 0) ω) :=
  flexible_foc_iff 𝔼 hw (fun ω => mul_pos (pow_pos hβ 0) (hΛ ω)) hW hH hknown ω

/-- Woodford (2003), p. 223 (**the steady state**): at the zero-inflation steady state with wage
`W̄`, hours `H̄`, discount factors `βᵏ/W̄` and nominal MRS `V̄P̄` at `H̄`, the first-order
condition at `w = W̄` holds iff `W̄ = μ_w V̄P̄`, i.e. the steady-state real wage is
`w̄ = μ_w v̄`. -/
theorem wage_steadyState_iff {β α θ Wbar Hbar VPbar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hW : 0 < Wbar) (hH : 0 < Hbar) {VP : ℕ → Ω → ℝ → ℝ}
    (hVP : ∀ k ω, VP k ω Hbar = VPbar) (t : ℕ) (ω : Ω) :
    focSum 𝔼 α θ (fun k _ => β ^ k / Wbar) (fun _ _ => Wbar) (fun _ _ => Hbar) VP t Wbar ω = 0
      ↔ Wbar = markup θ * VPbar :=
  steadyState_foc_iff 𝔼 hβ0 hβ1 hα0 hα1 hW hH hVP t ω

/-- Woodford (2003), p. 234 (**indexation of wages that are not reoptimised**): if the wage set
at `t` is `w I_{t+k}` at date `t + k` (with `I` the cumulated indexation factor,
`log I_{t+k} = γ_w (log P_{t+k−1} − log P_{t−1})`), the horizon payoff `Q (w I h − Ψ(h))`,
`h = H (w I/W)^{−θ_w}`, is the generic payoff `profit` with discount factor `Q I`,
"price index" `W/I` and cost `Ψ/I`; all results on the generic reset problem therefore apply
to indexed wage setting, with log marginal cost `ψ − log I` in the linearisation. -/
theorem indexed_profit_eq {θ x : ℝ} {Q W H I : Ω → ℝ} (Ψ : Ω → ℝ → ℝ) (hI : ∀ ω, 0 < I ω)
    (hW : ∀ ω, 0 < W ω) :
    (fun ω => Q ω * (x * I ω * ((x * I ω / W ω) ^ (-θ) * H ω)
      - Ψ ω ((x * I ω / W ω) ^ (-θ) * H ω)))
      = profit θ (fun ω => Q ω * I ω) (fun ω => W ω / I ω) H (fun ω h => Ψ ω h / I ω) x := by
  funext ω
  have hI0 := (hI ω).ne'
  have hW0 := (hW ω).ne'
  have hb : x / (W ω / I ω) = x * I ω / W ω := by
    field_simp
  simp only [profit, demand, hb]
  field_simp

/-! ### The log-linear wage-setting rule (4.7) -/

/-- Woodford (2003), eq. (4.2), p. 221: the hours of a supplier relative to the aggregate,
`log h(j) − log H = −θ_w (log w(j) − log W)`, exactly. -/
theorem log_demand_sub {θ w : ℝ} (hw : 0 < w) {W H : Ω → ℝ} (hW : ∀ ω, 0 < W ω)
    (hH : ∀ ω, 0 < H ω) (ω : Ω) :
    Real.log (demand θ w W H ω) - Real.log (H ω) = -θ * (Real.log w - Real.log (W ω)) := by
  have hb : 0 < w / W ω := div_pos hw (hW ω)
  unfold demand
  rw [Real.log_mul (Real.rpow_pos_of_pos hb _).ne' (hH ω).ne', Real.log_rpow hb,
    Real.log_div hw.ne' (hW ω).ne']
  ring

/-- Woodford (2003), p. 223: the log marginal disutility of work of a supplier working
`h = H e^{s a}` hours has derivative `ν a` at `s = 0`, with `ν = H v_hh(H)/v_h(H)` the elasticity
of the marginal disutility; hence its log MRS is `log v_t + ν log(h(j)/H_t)` to first order. -/
theorem hasDerivAt_log_vh {vh : ℝ → ℝ} {vh' Hbar a : ℝ} (hv : 0 < vh Hbar)
    (hd : HasDerivAt vh vh' Hbar) :
    HasDerivAt (fun s => Real.log (vh (Hbar * Real.exp (s * a)))) (vh' * Hbar / vh Hbar * a) 0 := by
  have h1 : HasDerivAt (fun s => Hbar * Real.exp (s * a)) (Hbar * a) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const a).exp).const_mul Hbar
    simpa using this
  have hd' : HasDerivAt vh vh' (Hbar * Real.exp (0 * a)) := by simpa using hd
  have h2 := hd'.comp (0 : ℝ) h1
  have e : (vh ∘ fun s => Hbar * Real.exp (s * a)) 0 = vh Hbar := by simp
  have h3 := h2.log (by rw [e]; exact hv.ne')
  rw [e] at h3
  have h4 : vh' * Hbar / vh Hbar * a = vh' * (Hbar * a) / vh Hbar := by ring
  rw [h4]
  exact h3

/-- Woodford (2003), eq. (4.7), p. 223 (**the algebra of (4.7)**): with bounded log nominal
average MRS `lV` and log wage index `lW`, the reset rule
`x = log μ + (1 − αβ) ∑ₖ (αβ)ᵏ E_t[lV_{t+k} − εθ (x − lW_{t+k})]` (the own-hours effect
substituted into the log MRS of the resetting type) holds iff
`x = (1 − αβ)/(1 + εθ) ∑ₖ (αβ)ᵏ E_t[log μ + lV_{t+k} + εθ lW_{t+k}]`, which is (4.7) for
`(ε, θ) = (ν, θ_w)` and the price-setting analogue for `(ε, θ) = (ω_p, θ_p)`. -/
theorem reset_rule_iff {α β ε θ lμ x B : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαβ : α * β < 1)
    (hεθ : 0 < 1 + ε * θ) {lV lW : ℕ → Ω → ℝ} (hV : ∀ k ω, |lV k ω| ≤ B)
    (hW : ∀ k ω, |lW k ω| ≤ B) (t : ℕ) (ω : Ω) :
    x = lμ + (1 - α * β) *
        ∑' k, (α * β) ^ k * 𝔼.E t (fun ω' => lV k ω' - ε * θ * (x - lW k ω')) ω ↔
      x = (1 - α * β) / (1 + ε * θ) *
        ∑' k, (α * β) ^ k * 𝔼.E t (fun ω' => lμ + lV k ω' + ε * θ * lW k ω') ω := by
  have ha0 : 0 ≤ α * β := mul_nonneg hα0 hβ0
  have ha : |α * β| < 1 := by rwa [abs_of_nonneg ha0]
  have hg := summable_geometric_of_lt_one ha0 hαβ
  have hsV := summable_geometric_bounded ha (fun k ω' => 𝔼.abs_E_le (hV k) t ω') ω
  have hsW := summable_geometric_bounded ha (fun k ω' => 𝔼.abs_E_le (hW k) t ω') ω
  have e1 : ∀ k, 𝔼.E t (fun ω' => lV k ω' - ε * θ * (x - lW k ω')) ω
      = 𝔼.E t (lV k) ω - ε * θ * x + ε * θ * 𝔼.E t (lW k) ω := by
    intro k
    have hf : (fun ω' => lV k ω' - ε * θ * (x - lW k ω'))
        = lV k - (fun _ => ε * θ * x) + (ε * θ) • lW k := by
      funext ω'
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hf, map_add, map_sub, 𝔼.const, map_smul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have e2 : ∀ k, 𝔼.E t (fun ω' => lμ + lV k ω' + ε * θ * lW k ω') ω
      = lμ + 𝔼.E t (lV k) ω + ε * θ * 𝔼.E t (lW k) ω := by
    intro k
    have hf : (fun ω' => lμ + lV k ω' + ε * θ * lW k ω')
        = (fun _ => lμ) + lV k + (ε * θ) • lW k := by
      funext ω'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf, map_add, map_add, 𝔼.const, map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  set A := ∑' k, (α * β) ^ k * 𝔼.E t (lV k) ω with hA
  set C := ∑' k, (α * β) ^ k * 𝔼.E t (lW k) ω with hC
  have hG : ∑' k : ℕ, (α * β) ^ k = (1 - α * β)⁻¹ := tsum_geometric_of_lt_one ha0 hαβ
  have s1 : ∑' k, (α * β) ^ k * 𝔼.E t (fun ω' => lV k ω' - ε * θ * (x - lW k ω')) ω
      = A - ε * θ * x * (1 - α * β)⁻¹ + ε * θ * C := by
    simp_rw [e1, mul_add, mul_sub]
    rw [Summable.tsum_add (hsV.sub (hg.mul_right _)) (hsW.mul_left (ε * θ) |>.congr
        (fun k => by ring)), Summable.tsum_sub hsV (hg.mul_right _), tsum_mul_right, hG]
    have : ∑' k, (α * β) ^ k * (ε * θ * 𝔼.E t (lW k) ω) = ε * θ * C := by
      rw [hC, ← tsum_mul_left]
      congr 1; funext k; ring
    rw [this]
    ring
  have s2 : ∑' k, (α * β) ^ k * 𝔼.E t (fun ω' => lμ + lV k ω' + ε * θ * lW k ω') ω
      = lμ * (1 - α * β)⁻¹ + A + ε * θ * C := by
    simp_rw [e2, mul_add]
    rw [Summable.tsum_add ((hg.mul_right _).add hsV) (hsW.mul_left (ε * θ) |>.congr
        (fun k => by ring)), Summable.tsum_add (hg.mul_right _) hsV, tsum_mul_right, hG]
    have : ∑' k, (α * β) ^ k * (ε * θ * 𝔼.E t (lW k) ω) = ε * θ * C := by
      rw [hC, ← tsum_mul_left]
      congr 1; funext k; ring
    rw [this]
    ring
  rw [s1, s2]
  have h1 : (1 : ℝ) - α * β ≠ 0 := by linarith
  have h2 : (1 : ℝ) + ε * θ ≠ 0 := hεθ.ne'
  constructor
  · intro h
    field_simp at h ⊢
    linear_combination h
  · intro h
    field_simp at h ⊢
    linear_combination h

/-- Woodford (2003), eq. (4.7), p. 223 (**(4.7) is the exact linearisation of (4.4)**): perturb
the steady state (log wage `p̄`) along bounded directions as in `hasDerivAt_focLHS_path`, so that
the first-order term of (4.4) is `w̄ e^{p̄} ∑ₖ (βα)ᵏ (x̂ − E_t ψ̂ₖ)`. If the log nominal MRS of
the resetting supplier is `lV_{t+k} − νθ(log w* − lW_{t+k})` (`log_demand_sub`,
`hasDerivAt_log_vh`), then this first-order term vanishes iff the reset wage
`log w* = p̄ + x̂` satisfies (4.7):
`log w* = (1 − α_wβ)/(1 + νθ_w) ∑ₖ (α_wβ)ᵏ E_t[log μ_w + log V_{t+k} + νθ_w log W_{t+k}]`. -/
theorem eq47_of_linearisation {α β θ ν wbar pbar xhat B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hwbar : 0 < wbar) (hνθ : 0 < 1 + ν * θ)
    {ψhat lV lW : ℕ → Ω → ℝ} (hψ : ∀ k ω, |ψhat k ω| ≤ B) (hV : ∀ k ω, |lV k ω| ≤ B)
    (hW : ∀ k ω, |lW k ω| ≤ B)
    (hmrs : ∀ k ω, (pbar - logMarkup θ) + ψhat k ω = lV k ω - ν * θ * (pbar + xhat - lW k ω))
    (t : ℕ) (ω : Ω) :
    wbar * Real.exp pbar * ∑' k, (β * α) ^ k * (xhat - 𝔼.E t (ψhat k) ω) = 0 ↔
      pbar + xhat = (1 - α * β) / (1 + ν * θ) *
        ∑' k, (α * β) ^ k * 𝔼.E t (fun ω' => logMarkup θ + lV k ω' + ν * θ * lW k ω') ω := by
  refine (linear_reset_rule_iff 𝔼 (θ := θ) hβ0 hβ1 hα0 hα1 hwbar hψ t ω).trans ?_
  have hs : ∑' k, (β * α) ^ k * 𝔼.E t (fun ω' => (pbar - logMarkup θ) + ψhat k ω') ω
      = ∑' k, (α * β) ^ k * 𝔼.E t (fun ω' => lV k ω' - ν * θ * (pbar + xhat - lW k ω')) ω := by
    refine tsum_congr fun k => ?_
    rw [mul_comm β α, show (fun ω' => (pbar - logMarkup θ) + ψhat k ω')
      = fun ω' => lV k ω' - ν * θ * (pbar + xhat - lW k ω') from funext (hmrs k)]
  rw [hs, mul_comm β α]
  exact reset_rule_iff 𝔼 hα0 hβ0 (by nlinarith) hνθ hV hW t ω

/-! ### The wage setter's problem from primitives -/

/-- Woodford (2003), eqs. (4.3)–(4.5), pp. 222–223 (**regularity of the wage setter's problem
from primitives**): if `β > 0`, `α_w β < 1`, `θ_w > 1`, the marginal utility of nominal
income lies in `[m_Λ, M_Λ]` with `m_Λ > 0`, the wage index and the labour aggregate lie in
`[m, M̄]` with `m > 0`, and the disutility `v(·; ξ)` is twice differentiable at positive hours
with `v`, `v_h`, `v_hh` bounded uniformly in the horizon and the state on every compact range
of positive hours, then the transformed problem (`wageObjective_eq`) satisfies `Primitives`. -/
theorem wage_primitives {α β θ mΛ MΛ m Mx : ℝ} {Λ W H : ℕ → Ω → ℝ}
    {v vh vhh : ℕ → Ω → ℝ → ℝ} (hα : 0 ≤ α) (hβ : 0 < β) (hαβ : α * β < 1) (hθ : 1 < θ)
    (hm : 0 < m) (hmΛ : 0 < mΛ) (hΛ : ∀ k ω, mΛ ≤ Λ k ω ∧ Λ k ω ≤ MΛ)
    (hW : ∀ k ω, m ≤ W k ω ∧ W k ω ≤ Mx) (hH : ∀ k ω, m ≤ H k ω ∧ H k ω ≤ Mx)
    (hv : ∀ k ω y, 0 < y → HasDerivAt (v k ω) (vh k ω y) y)
    (hvh : ∀ k ω y, 0 < y → HasDerivAt (vh k ω) (vhh k ω y) y)
    (hvb : ∀ y₁ y₂, 0 < y₁ → ∃ K, ∀ k ω y, y₁ ≤ y → y ≤ y₂ →
      |v k ω y| ≤ K ∧ |vh k ω y| ≤ K ∧ |vhh k ω y| ≤ K) :
    Primitives α β θ MΛ m Mx (wageQ β Λ) W H (wageCost Λ v) (wageCost Λ vh) (wageCost Λ vhh) := by
  have hΛpos : ∀ k ω, 0 < Λ k ω := fun k ω => hmΛ.trans_le (hΛ k ω).1
  have hdiv : ∀ {a K : ℝ} (k : ℕ) (ω : Ω), |a| ≤ K → |a / Λ k ω| ≤ K / mΛ := by
    intro a K k ω ha
    rw [abs_div, abs_of_pos (hΛpos k ω)]
    exact (div_le_div_of_nonneg_left (abs_nonneg a) hmΛ (hΛ k ω).1).trans
      (div_le_div_of_nonneg_right ha hmΛ.le)
  refine ⟨hα, hβ.le, hαβ, hθ, hm, fun k ω => ⟨mul_pos (pow_pos hβ k) (hΛpos k ω), ?_⟩, hW, hH,
    fun k ω y hy => (hv k ω y hy).div_const _, fun k ω y hy => (hvh k ω y hy).div_const _, ?_⟩
  · simp only [wageQ]
    rw [mul_comm MΛ]
    exact mul_le_mul_of_nonneg_left (hΛ k ω).2 (pow_nonneg hβ.le k)
  · intro y₁ y₂ hy₁
    obtain ⟨K, hK⟩ := hvb y₁ y₂ hy₁
    refine ⟨K / mΛ, fun k ω y h1 h2 => ?_⟩
    obtain ⟨a, b, c⟩ := hK k ω y h1 h2
    exact ⟨hdiv k ω a, hdiv k ω b, hdiv k ω c⟩

/-- Woodford (2003), eqs. (4.3)–(4.4), pp. 222–223 (**(4.4) characterises the optimal wage,
from primitives only**): under the primitive bounds of `wage_primitives` and a convex
disutility (`v_hh ≥ 0`), a wage `w > 0` maximises (4.3) over all positive wages iff the
first-order condition holds, and it is then the unique (strict) maximiser. All Lipschitz,
domination and summability conditions of `wage_isMaxOn_iff_foc` are derived. -/
theorem wage_isMaxOn_iff_foc_of_primitives {α β θ mΛ MΛ m Mx : ℝ} {Λ W H : ℕ → Ω → ℝ}
    {v vh vhh : ℕ → Ω → ℝ → ℝ} (hα : 0 ≤ α) (hβ : 0 < β) (hαβ : α * β < 1) (hθ : 1 < θ)
    (hm : 0 < m) (hmΛ : 0 < mΛ) (hΛ : ∀ k ω, mΛ ≤ Λ k ω ∧ Λ k ω ≤ MΛ)
    (hW : ∀ k ω, m ≤ W k ω ∧ W k ω ≤ Mx) (hH : ∀ k ω, m ≤ H k ω ∧ H k ω ≤ Mx)
    (hv : ∀ k ω y, 0 < y → HasDerivAt (v k ω) (vh k ω y) y)
    (hvh : ∀ k ω y, 0 < y → HasDerivAt (vh k ω) (vhh k ω y) y)
    (hvb : ∀ y₁ y₂, 0 < y₁ → ∃ K, ∀ k ω y, y₁ ≤ y → y ≤ y₂ →
      |v k ω y| ≤ K ∧ |vh k ω y| ≤ K ∧ |vhh k ω y| ≤ K)
    (hconv : ∀ k ω y, 0 < y → 0 ≤ vhh k ω y) (t : ℕ) (ω : Ω) {w : ℝ} (hw : 0 < w) :
    (IsMaxOn (fun z => wageObjective 𝔼 α β θ Λ W H v t z ω) (Set.Ioi 0) w ↔
        focSum 𝔼 α θ (wageQ β Λ) W H (wageCost Λ vh) t w ω = 0) ∧
      (focSum 𝔼 α θ (wageQ β Λ) W H (wageCost Λ vh) t w ω = 0 → ∀ y, 0 < y → y ≠ w →
        wageObjective 𝔼 α β θ Λ W H v t y ω < wageObjective 𝔼 α β θ Λ W H v t w ω) := by
  have hΛpos : ∀ k ω, 0 < Λ k ω := fun k ω => hmΛ.trans_le (hΛ k ω).1
  have hprim := wage_primitives hα hβ hαβ hθ hm hmΛ hΛ hW hH hv hvh hvb
  have hc : ∀ k ω y, 0 < y → 0 ≤ wageCost Λ vhh k ω y := fun k ω y hy =>
    div_nonneg (hconv k ω y hy) (hΛpos k ω).le
  have hQ0 : ∃ q, 0 < q ∧ ∀ ω, q ≤ wageQ β Λ 0 ω :=
    ⟨mΛ, hmΛ, fun ω => by simpa [wageQ] using (hΛ 0 ω).1⟩
  have h := isMaxOn_iff_foc_of_primitives 𝔼 hprim hc hQ0 t ω hw
  simp only [← wageObjective_eq 𝔼 v hΛpos t] at h
  exact h

/-! ### The price setter's problem behind (4.9) -/

/-- Woodford (2003), p. 224: with a single economy-wide labour market and a fixed allocation of
capital (production `y = A f(h)`, (1.7)), the nominal cost of producing `y` at date `t + k` is
`W_{t+k} f⁻¹(y/A_{t+k})`. -/
noncomputable def priceCost (W A : ℕ → Ω → ℝ) (finv : ℝ → ℝ) : ℕ → Ω → ℝ → ℝ :=
  fun k ω y => W k ω * finv (y / A k ω)

/-- Woodford (2003), p. 224: nominal marginal cost
`S = W/(A f'(f⁻¹(y/A)))` (wage over the marginal product of labour). -/
noncomputable def priceMC (W A : ℕ → Ω → ℝ) (df finv : ℝ → ℝ) : ℕ → Ω → ℝ → ℝ :=
  fun k ω y => W k ω / (A k ω * df (finv (y / A k ω)))

/-- Woodford (2003), p. 224 (with (2.2)–(2.4)): the objective of a supplier that resets its price
to `p` at date `t` under Calvo pricing (probability `α_p` of no reset),
`∑ₖ (α_p β)ᵏ E_t[Λ_{t+k}(p y_{t+k}(p) − W_{t+k} f⁻¹(y_{t+k}(p)/A_{t+k}))]`, with demand
`y_{t+k}(p) = Y_{t+k}(p/P_{t+k})^{−θ_p}` (`demand θ p P Y`). -/
noncomputable def priceObjective (α β θ : ℝ) (Λ P Y W A : ℕ → Ω → ℝ) (finv : ℝ → ℝ) (t : ℕ)
    (p : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, (α * β) ^ k * 𝔼.E t (fun ω' => Λ k ω' * (p * demand θ p (P k) (Y k) ω'
    - W k ω' * finv (demand θ p (P k) (Y k) ω' / A k ω'))) ω

/-- Woodford (2003), p. 224: the price-setting objective is the generic Calvo reset objective with
discount factors `βᵏ Λ_{t+k}`, price index `P`, demand shifter `Y` and nominal cost
`W f⁻¹(y/A)`. -/
theorem priceObjective_eq {α β θ : ℝ} (Λ P Y W A : ℕ → Ω → ℝ) (finv : ℝ → ℝ) (t : ℕ)
    (p : ℝ) : priceObjective 𝔼 α β θ Λ P Y W A finv t p =
      objective 𝔼 α θ (wageQ β Λ) P Y (priceCost W A finv) t p := by
  funext ω
  unfold priceObjective objective
  congr 1
  funext k
  have hfun : profit θ (wageQ β Λ k) (P k) (Y k) (priceCost W A finv k) p
      = (β ^ k) • fun ω' => Λ k ω' * (p * demand θ p (P k) (Y k) ω'
        - W k ω' * finv (demand θ p (P k) (Y k) ω' / A k ω')) := by
    funext ω'
    simp only [profit, wageQ, priceCost, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Woodford (2003), p. 224: the derivative of the nominal cost is nominal marginal cost,
`d/dy [W f⁻¹(y/A)] = W/(A f'(f⁻¹(y/A)))`, when `(f⁻¹)'(x) = 1/f'(f⁻¹(x))`. -/
theorem hasDerivAt_priceCost {W A : ℕ → Ω → ℝ} {df finv : ℝ → ℝ} (hA : ∀ k ω, 0 < A k ω)
    (hfinv : ∀ x, 0 < x → HasDerivAt finv (1 / df (finv x)) x) (k : ℕ) (ω : Ω) {y : ℝ}
    (hy : 0 < y) : HasDerivAt (priceCost W A finv k ω) (priceMC W A df finv k ω y) y := by
  have h1 : HasDerivAt (fun y => y / A k ω) (1 / A k ω) y := by
    simpa using (hasDerivAt_id y).div_const (A k ω)
  have h2 := ((hfinv (y / A k ω) (div_pos hy (hA k ω))).comp y h1).const_mul (W k ω)
  refine h2.congr_deriv ?_
  simp only [priceMC]
  have := (hA k ω).ne'
  field_simp

/-- Woodford (2003), p. 224: nominal marginal cost is nondecreasing in output (convex costs)
when `f⁻¹` is increasing and positive and the marginal product `f'` is positive and
nonincreasing (concave `f`). -/
theorem priceMC_monotoneOn {W A : ℕ → Ω → ℝ} {df finv : ℝ → ℝ} (hW : ∀ k ω, 0 < W k ω)
    (hA : ∀ k ω, 0 < A k ω) (hfinv : MonotoneOn finv (Set.Ioi 0))
    (hfinv0 : ∀ x, 0 < x → 0 < finv x) (hdf : AntitoneOn df (Set.Ioi 0))
    (hdf0 : ∀ h, 0 < h → 0 < df h) (k : ℕ) (ω : Ω) :
    MonotoneOn (priceMC W A df finv k ω) (Set.Ioi 0) := by
  intro y₁ hy₁ y₂ hy₂ h
  simp only [Set.mem_Ioi] at hy₁ hy₂
  have hA0 := hA k ω
  have hx₁ : 0 < y₁ / A k ω := div_pos hy₁ hA0
  have hx₂ : 0 < y₂ / A k ω := div_pos hy₂ hA0
  have hf : finv (y₁ / A k ω) ≤ finv (y₂ / A k ω) :=
    hfinv hx₁ hx₂ (div_le_div_of_nonneg_right h hA0.le)
  have hd : df (finv (y₂ / A k ω)) ≤ df (finv (y₁ / A k ω)) :=
    hdf (hfinv0 _ hx₁) (hfinv0 _ hx₂) hf
  have hd2 := hdf0 _ (hfinv0 _ hx₂)
  simp only [priceMC]
  exact div_le_div_of_nonneg_left (hW k ω).le (mul_pos hA0 hd2)
    (mul_le_mul_of_nonneg_left hd hA0.le)

/-- Woodford (2003), p. 224 (**the price-setting first-order condition characterises the optimal
price**): with concave technology (`priceMC_monotoneOn`) and the regularity conditions of
`isMaxOn_iff_foc`, a price `p > 0` maximises the Calvo objective over all positive prices iff
`∑ₖ α_pᵏ E_t[Q_{t,t+k} y_{t+k}(p)(p − μ_p S_{t+k}(y_{t+k}(p)))] = 0`, and it is then the unique
maximiser. -/
theorem price_isMaxOn_iff_foc {α β θ : ℝ} (hθ : 1 < θ) (hα : 0 ≤ α) (hβ : 0 < β)
    {Λ P Y W A : ℕ → Ω → ℝ} {df finv : ℝ → ℝ} (hΛ : ∀ k ω, 0 < Λ k ω) (hP : ∀ k ω, 0 < P k ω)
    (hY : ∀ k ω, 0 < Y k ω) (hW : ∀ k ω, 0 < W k ω) (hA : ∀ k ω, 0 < A k ω)
    (hfd : ∀ x, 0 < x → HasDerivAt finv (1 / df (finv x)) x)
    (hfinv : MonotoneOn finv (Set.Ioi 0)) (hfinv0 : ∀ x, 0 < x → 0 < finv x)
    (hdf : AntitoneOn df (Set.Ioi 0)) (hdf0 : ∀ h, 0 < h → 0 < df h)
    (hLip : ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv θ (wageQ β Λ k) (P k) (Y k) (priceMC W A df finv k) z ω
        - profitDeriv θ (wageQ β Λ k) (P k) (Y k) (priceMC W A df finv k) y ω| ≤ L * |z - y|)
    (hloc : ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |α| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω,
        |profitDeriv θ (wageQ β Λ k) (P k) (Y k) (priceMC W A df finv k) y ω| ≤ u k)
    (t : ℕ) (ω : Ω)
    (hs : ∀ y, 0 < y → Summable fun k =>
      α ^ k * 𝔼.E t (profit θ (wageQ β Λ k) (P k) (Y k) (priceCost W A finv k) y) ω)
    (hpos : 0 < 𝔼.E t (fun ω' => Λ 0 ω' * (P 0 ω' ^ θ * Y 0 ω')) ω) {p : ℝ} (hp : 0 < p) :
    (IsMaxOn (fun z => priceObjective 𝔼 α β θ Λ P Y W A finv t z ω) (Set.Ioi 0) p ↔
        focSum 𝔼 α θ (wageQ β Λ) P Y (priceMC W A df finv) t p ω = 0) ∧
      (focSum 𝔼 α θ (wageQ β Λ) P Y (priceMC W A df finv) t p ω = 0 → ∀ y, 0 < y → y ≠ p →
        priceObjective 𝔼 α β θ Λ P Y W A finv t y ω
          < priceObjective 𝔼 α β θ Λ P Y W A finv t p ω) := by
  have hQ : ∀ k ω, 0 < wageQ β Λ k ω := fun k ω => mul_pos (pow_pos hβ k) (hΛ k ω)
  have hpos' : 0 < 𝔼.E t (fun ω' => wageQ β Λ 0 ω' * (P 0 ω' ^ θ * Y 0 ω')) ω := by
    simpa [wageQ] using hpos
  have h := isMaxOn_iff_foc 𝔼 hθ hα hQ hP hY
    (fun k ω y hy => hasDerivAt_priceCost hA hfd k ω hy)
    (priceMC_monotoneOn hW hA hfinv hfinv0 hdf hdf0) hLip hloc t ω hs hpos' hp
  simp only [← priceObjective_eq 𝔼 Λ P Y W A finv t] at h
  exact h

/-- Woodford (2003), p. 224 (with (1.16)): the log nominal marginal cost of a supplier producing
`ȳ e^{s a}` has own-output elasticity `ω_p`: `s ↦ −log f'(f⁻¹(ȳ e^{s a}))` has derivative
`ω_p a` at `s = 0`, with `ω_p = −ȳ f''(h̄)(f⁻¹)'(ȳ)/f'(h̄)` (`= −f f''/f'²`). Hence the reset
supplier's log marginal cost is `log S_{t+k} + ω_p(log y(i) − log Y) =
log S_{t+k} − ω_pθ_p(log p* − log P_{t+k})` to first order (`log_demand_sub`). -/
theorem hasDerivAt_log_mc {df finv : ℝ → ℝ} {d2f dfinv ybar hbar a : ℝ} (hy : 0 < ybar)
    (hh : finv ybar = hbar) (hfinv : HasDerivAt finv dfinv ybar) (hdf : HasDerivAt df d2f hbar)
    (hd : 0 < df hbar) :
    HasDerivAt (fun s => -Real.log (df (finv (ybar * Real.exp (s * a)))))
      (-(d2f * ybar * dfinv / df hbar) * a) 0 := by
  have h1 : HasDerivAt (fun s => ybar * Real.exp (s * a)) (ybar * a) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const a).exp).const_mul ybar
    simpa using this
  have h2 : HasDerivAt (fun s => finv (ybar * Real.exp (s * a))) (dfinv * (ybar * a)) 0 :=
    HasDerivAt.comp_of_eq (0 : ℝ) hfinv h1 (by simp)
  have h3 : HasDerivAt (fun s => df (finv (ybar * Real.exp (s * a))))
      (d2f * (dfinv * (ybar * a))) 0 :=
    HasDerivAt.comp_of_eq (0 : ℝ) hdf h2 (by simp [hh])
  have e : df (finv (ybar * Real.exp (0 * a))) = df hbar := by simp [hh]
  have h4 := (h3.log (by rw [e]; exact hd.ne')).neg
  rw [e] at h4
  refine h4.congr_deriv ?_
  field_simp

/-- Woodford (2003), p. 224 (**the price-setting analogue of (4.7)**, behind (4.9)): along the
perturbation of `hasDerivAt_focLHS_path`, if the reset supplier's log nominal marginal cost is
`lS_{t+k} − ω_pθ_p(log p* − lP_{t+k})` (`hasDerivAt_log_mc`, `log_demand_sub`), the first-order
term of the price-setting condition vanishes iff
`log p*_t = (1 − α_pβ)/(1 + ω_pθ_p) ∑ₖ (α_pβ)ᵏ E_t[log μ_p + log S_{t+k} + ω_pθ_p log P_{t+k}]`.
Combined with the price-index law of motion this is equivalent to (4.9)
(`StickyWages.eq48_eq49_iff` with `(ε, θ) = (ω_p, θ_p)`). -/
theorem price_reset_rule_of_linearisation {α β θ ωp wbar pbar xhat B : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1) (hwbar : 0 < wbar) (hωθ : 0 < 1 + ωp * θ)
    {ψhat lS lP : ℕ → Ω → ℝ} (hψ : ∀ k ω, |ψhat k ω| ≤ B) (hS : ∀ k ω, |lS k ω| ≤ B)
    (hP : ∀ k ω, |lP k ω| ≤ B)
    (hmc : ∀ k ω, (pbar - logMarkup θ) + ψhat k ω = lS k ω - ωp * θ * (pbar + xhat - lP k ω))
    (t : ℕ) (ω : Ω) :
    wbar * Real.exp pbar * ∑' k, (β * α) ^ k * (xhat - 𝔼.E t (ψhat k) ω) = 0 ↔
      pbar + xhat = (1 - α * β) / (1 + ωp * θ) *
        ∑' k, (α * β) ^ k * 𝔼.E t (fun ω' => logMarkup θ + lS k ω' + ωp * θ * lP k ω') ω :=
  eq47_of_linearisation 𝔼 hβ0 hβ1 hα0 hα1 hwbar hωθ hψ hS hP hmc t ω

end Woodford.NominalRigidities.WageSetting
