/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OpenEconomy.Identities
import OpenEconomy.Expectations
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Arrow securities, the stochastic discount factor and international risk sharing

Galí (2015), Chapter 8, §8.1.1 and §8.1.1.2, pp. 227–231: eqs. (8), (9), (10), fn. 3, (15),
(16), (17).

Uncertainty is modelled **state by state**, with no conditional-expectation operator in the
pricing conditions: at a node of the event tree the successor states form a finite set `ι`
with conditional probabilities `ξ j > 0`; an Arrow security `j` costs `V j` (domestic
currency) and pays one unit of domestic currency in state `j` only.

## Main results

* `periodUtility` (p. 227), `hasDerivAt_periodUtility`, `periodUtility_tangent`: the book's
  consumption utility `(C^{1−σ} − 1)/(1−σ)` (`log C` at `σ = 1`), with marginal utility
  `C^{−σ}` and the tangent (concavity) inequality.
* `arrow_foc_of_optimal` (eq. (8), **necessity by perturbation**): if a plan maximises
  `Z u(C) + β Σ_j ξ_j Z'_j u(C'_j)` subject to the budget `P C + Σ_j V_j D_j ≤ W`,
  `C'_j = (D_j + Y_j)/P'_j`, then `(V_j/P) Z C^{−σ} = ξ_j β Z'_j C'_j^{−σ}/P'_j` for every `j`.
* `optimal_of_arrow_foc` (sufficiency) and `arrow_optimal_iff`: with the budget binding,
  (8) for all `j` is necessary **and** sufficient for optimality.
* `arrow_sdf_iff` (eq. (9)): with `Q_{t,t+1} ≡ V/ξ` (fn. 3), (8) ⇔
  `β (C'/C)^{−σ} (Z'/Z)(P/P') = Q_{t,t+1}`; `portfolio_price` (fn. 3), `bond_price` and
  `bond_price_expectation` (eq. (10)).
* `foreign_optimal_iff`, `foreign_sdf_iff` (eq. (15)): the foreign household's problem and
  its Arrow condition `β (C*'/C*)^{−σ} (P*/P*')(ℰ/ℰ') = Q_{t,t+1}`.
* `riskSharing_ratio_const` (eq. (16)): if (9) and (15) hold at every date along every
  path, `C^{−σ} Z C*^σ 𝒬` is constant along every path (telescoping);
  `riskSharing` gives `C = ϑ C* Z^{1/σ} 𝒬^{1/σ}` and `vartheta_eq_one` gives `ϑ = 1` under
  symmetric initial conditions.
* `riskSharing_log` (eq. (17), first line), `riskSharing_log_tot` (general `η`:
  `c = y* + z/σ + g(s)/σ` with `g'(0) = 1 − υ`), `riskSharing_log_cd` (exact at `η = 1`).
-/

namespace Gali.OpenEconomy.RiskSharing

open Filter Topology Preferences Identities

/-! ### Period utility -/

/-- Galí (2015), p. 227: the consumption part of period utility,
`(C^{1−σ} − 1)/(1−σ)` for `σ ≠ 1` and `log C` for `σ = 1`. -/
noncomputable def periodUtility (σ c : ℝ) : ℝ :=
  if σ = 1 then Real.log c else (c ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 227: marginal utility of consumption is `C^{−σ}`. -/
theorem hasDerivAt_periodUtility (σ : ℝ) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (periodUtility σ) (c ^ (-σ)) c := by
  by_cases hσ : σ = 1
  · have hfun : periodUtility σ = Real.log := funext fun x => by simp [periodUtility, hσ]
    rw [hfun, hσ, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hc.ne'
  · have hfun : periodUtility σ = fun x => (x ^ (1 - σ) - 1) / (1 - σ) :=
      funext fun x => by simp [periodUtility, hσ]
    rw [hfun]
    have hne : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    have h := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).sub_const 1).div_const
      (1 - σ)
    convert h using 1
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp

/-- Galí (2015), p. 227 (concavity of utility): the tangent inequality
`u(c) − u(c₀) ≤ c₀^{−σ}(c − c₀)` for `σ > 0`, `c, c₀ > 0`. -/
theorem periodUtility_tangent {σ c c₀ : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hc₀ : 0 < c₀) :
    periodUtility σ c - periodUtility σ c₀ ≤ c₀ ^ (-σ) * (c - c₀) := by
  by_cases h1 : σ = 1
  · simp only [periodUtility, h1, ↓reduceIte, Real.rpow_neg_one]
    have := Real.log_le_sub_one_of_pos (div_pos hc hc₀)
    rw [Real.log_div hc.ne' hc₀.ne'] at this
    have e : c / c₀ - 1 = c₀⁻¹ * (c - c₀) := by field_simp
    linarith
  · simp only [periodUtility, h1, ↓reduceIte]
    have hr0 : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    have key := rpow_tangent_le (r := 1 - σ) (u := c / c₀) (by linarith) hr0
      (div_pos hc hc₀).le (Or.inr (div_pos hc hc₀))
    have hcr : c ^ (1 - σ) = (c / c₀) ^ (1 - σ) * c₀ ^ (1 - σ) := by
      rw [Real.div_rpow hc.le hc₀.le]
      field_simp
    have hneg : c₀ ^ (-σ) = c₀ ^ (1 - σ) / c₀ := by
      rw [← Real.rpow_sub_one hc₀.ne']
      ring_nf
    have hpos : 0 < c₀ ^ (1 - σ) := Real.rpow_pos_of_pos hc₀ _
    have e1 : (c ^ (1 - σ) - 1) / (1 - σ) - (c₀ ^ (1 - σ) - 1) / (1 - σ)
        = c₀ ^ (1 - σ) * (((c / c₀) ^ (1 - σ) - 1) / (1 - σ)) := by
      rw [hcr]; field_simp; ring
    have e2 : c₀ ^ (-σ) * (c - c₀) = c₀ ^ (1 - σ) * (c / c₀ - 1) := by
      rw [hneg]; field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left key hpos.le

/-! ### The one-node portfolio problem: eq. (8) -/

variable {ι : Type*} [Fintype ι]

/-- Galí (2015), (1), (3), p. 226: the part of expected discounted utility affected by the
date-`t` choices at a node: `Z u(C) + β Σ_j ξ_j Z'_j u(C'_j)`, with next-period consumption
`C'_j = (D_j + Y_j)/P'_j` financed by the Arrow-security holdings `D_j` and other income
`Y_j` (wages, dividends, other assets) in state `j`. -/
noncomputable def nodeObjective (σ β Z : ℝ) (ξ Z' P' Y : ι → ℝ) (C : ℝ) (D : ι → ℝ) : ℝ :=
  Z * periodUtility σ C + β * ∑ j, ξ j * (Z' j * periodUtility σ ((D j + Y j) / P' j))

/-- Galí (2015), eq. (3), p. 226: feasibility at the node — positive consumption now and
in every successor state, and the budget `P C + Σ_j V_j D_j ≤ W`. -/
def NodeFeasible (P W : ℝ) (V P' Y : ι → ℝ) (C : ℝ) (D : ι → ℝ) : Prop :=
  0 < C ∧ (∀ j, 0 < (D j + Y j) / P' j) ∧ P * C + ∑ j, V j * D j ≤ W

/-- Galí (2015), eq. (8), p. 227: the Arrow-security optimality condition
`(V_j/P) Z C^{−σ} = ξ_j β Z'_j C'_j^{−σ} / P'_j`. -/
def ArrowFOC (σ β Z P : ℝ) (ξ Z' P' V Y : ι → ℝ) (C : ℝ) (D : ι → ℝ) (j : ι) : Prop :=
  V j / P * (Z * C ^ (-σ)) = ξ j * β * (Z' j * ((D j + Y j) / P' j) ^ (-σ)) / P' j

/-- Galí (2015), eq. (8), p. 227 (**necessity, by perturbation**): if `(C, D)` maximises the
node objective over all feasible plans, then (8) holds for every Arrow security `j`. The
perturbation buys `x` more units of security `j` and finances it by consuming `V_j x/P`
less; it leaves the budget unchanged, so `x = 0` is a local maximum. -/
theorem arrow_foc_of_optimal {σ β Z P W : ℝ} {ξ Z' P' V Y : ι → ℝ} {C : ℝ} {D : ι → ℝ}
    (hP : 0 < P) (hfeas : NodeFeasible P W V P' Y C D)
    (hopt : ∀ C₂ D₂, NodeFeasible P W V P' Y C₂ D₂ →
      nodeObjective σ β Z ξ Z' P' Y C₂ D₂ ≤ nodeObjective σ β Z ξ Z' P' Y C D) (j : ι) :
    ArrowFOC σ β Z P ξ Z' P' V Y C D j := by
  classical
  obtain ⟨hC, hC', hbud⟩ := hfeas
  set φ : ℝ → ℝ := fun x => nodeObjective σ β Z ξ Z' P' Y (C - V j * x / P)
    (fun k => D k + if k = j then x else 0) with hφ
  have hφ0 : φ 0 = nodeObjective σ β Z ξ Z' P' Y C D := by
    simp [φ]
  -- feasibility of the perturbation near `x = 0`
  have hcont1 : ContinuousAt (fun x : ℝ => C - V j * x / P) 0 := by fun_prop
  have hcont2 : ContinuousAt (fun x : ℝ => (D j + x + Y j) / P' j) 0 := by fun_prop
  have hev1 : ∀ᶠ x in 𝓝 (0 : ℝ), (0 : ℝ) < C - V j * x / P := by
    have h0 : (0 : ℝ) < C - V j * 0 / P := by rw [mul_zero, zero_div, sub_zero]; exact hC
    exact hcont1.eventually (lt_mem_nhds h0)
  have hev2 : ∀ᶠ x in 𝓝 (0 : ℝ), (0 : ℝ) < (D j + x + Y j) / P' j := by
    have h0 : (0 : ℝ) < (D j + 0 + Y j) / P' j := by rw [add_zero]; exact hC' j
    exact hcont2.eventually (lt_mem_nhds h0)
  have hmax : IsLocalMax φ 0 := by
    filter_upwards [hev1, hev2] with x hx1 hx2
    rw [hφ0]
    refine hopt _ _ ⟨hx1, fun k => ?_, ?_⟩
    · by_cases hk : k = j
      · subst hk; simpa [add_right_comm] using hx2
      · simpa [hk] using hC' k
    · have hs : ∑ k, V k * (D k + if k = j then x else 0) = ∑ k, V k * D k + V j * x := by
        simp [mul_add, Finset.sum_add_distrib]
      rw [hs]
      have : P * (C - V j * x / P) = P * C - V j * x := by field_simp
      linarith
  -- the derivative of the perturbed objective at `0`
  have hd1 : HasDerivAt (fun x => periodUtility σ (C - V j * x / P))
      (C ^ (-σ) * (-(V j) / P)) 0 := by
    have hl : HasDerivAt (fun x : ℝ => C - V j * x / P) (-(V j) / P) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).const_mul (V j)).div_const P
      have := this.const_sub C
      convert this using 1
      ring
    have hy : C = C - V j * 0 / P := by rw [mul_zero, zero_div, sub_zero]
    exact HasDerivAt.comp_of_eq 0 (hasDerivAt_periodUtility σ hC) hl hy
  have hterm : ∀ k ∈ (Finset.univ : Finset ι), HasDerivAt
      (fun x => ξ k * (Z' k * periodUtility σ ((D k + (if k = j then x else 0) + Y k) / P' k)))
      (if k = j then ξ j * (Z' j * (((D j + Y j) / P' j) ^ (-σ) * (1 / P' j))) else 0) 0 := by
    intro k _
    by_cases hk : k = j
    · subst hk
      simp only [↓reduceIte]
      have hl : HasDerivAt (fun x : ℝ => (D k + x + Y k) / P' k) (1 / P' k) 0 := by
        have := (((hasDerivAt_id' (0 : ℝ)).const_add (D k)).add_const (Y k)).div_const (P' k)
        simpa using this
      have hy : (D k + Y k) / P' k = (D k + 0 + Y k) / P' k := by rw [add_zero]
      have hc := HasDerivAt.comp_of_eq 0 (hasDerivAt_periodUtility σ (hC' k)) hl hy
      have hc2 := HasDerivAt.const_mul (Z' k) hc
      have hc3 := HasDerivAt.const_mul (ξ k) hc2
      simpa [Function.comp_def, mul_one_div] using hc3
    · simp only [hk, ↓reduceIte, add_zero]
      exact hasDerivAt_const _ _
  have hsum := HasDerivAt.fun_sum hterm
  rw [Finset.sum_ite_eq' Finset.univ j] at hsum
  simp only [Finset.mem_univ, ↓reduceIte] at hsum
  have hφd : HasDerivAt φ (Z * (C ^ (-σ) * (-(V j) / P)) +
      β * (ξ j * (Z' j * (((D j + Y j) / P' j) ^ (-σ) * (1 / P' j))))) 0 :=
    (hd1.const_mul Z).add (hsum.const_mul β)
  have h0 := hmax.hasDerivAt_eq_zero hφd
  unfold ArrowFOC
  have hP'j : P' j ≠ 0 := by
    intro h
    have := hC' j
    rw [h, div_zero] at this
    exact lt_irrefl 0 this
  field_simp at h0 ⊢
  linarith

/-- Galí (2015), eq. (8), p. 227 (**sufficiency**): if the budget binds and (8) holds for
every security, the plan maximises the node objective among all feasible plans
(`σ > 0`, positive `Z`, `P`, `P'`). -/
theorem optimal_of_arrow_foc {σ β Z P W : ℝ} {ξ Z' P' V Y : ι → ℝ} {C : ℝ} {D : ι → ℝ}
    (hσ : 0 < σ) (hβ : 0 < β) (hZ : 0 < Z) (hP : 0 < P) (hξ : ∀ j, 0 < ξ j)
    (hZ' : ∀ j, 0 < Z' j) (hP' : ∀ j, 0 < P' j)
    (hfeas : NodeFeasible P W V P' Y C D) (hbind : P * C + ∑ j, V j * D j = W)
    (hfoc : ∀ j, ArrowFOC σ β Z P ξ Z' P' V Y C D j) :
    ∀ C₂ D₂, NodeFeasible P W V P' Y C₂ D₂ →
      nodeObjective σ β Z ξ Z' P' Y C₂ D₂ ≤ nodeObjective σ β Z ξ Z' P' Y C D := by
  intro C₂ D₂ ⟨hC₂, hC₂', hbud₂⟩
  obtain ⟨hC, hC', _⟩ := hfeas
  set m := Z * C ^ (-σ) / P with hm
  -- (8) rewritten: `β ξ_j Z'_j u'(C'_j) = m V_j P'_j`
  have hfoc' : ∀ j, β * (ξ j * (Z' j * ((D j + Y j) / P' j) ^ (-σ))) = m * V j * P' j := by
    intro j
    have h := hfoc j
    unfold ArrowFOC at h
    have hP'j := (hP' j).ne'
    rw [hm]
    field_simp at h ⊢
    linarith
  have hterm : ∀ j, β * (ξ j * (Z' j * periodUtility σ ((D₂ j + Y j) / P' j)))
      - β * (ξ j * (Z' j * periodUtility σ ((D j + Y j) / P' j)))
      ≤ m * V j * (D₂ j - D j) := by
    intro j
    have ht := periodUtility_tangent hσ (hC₂' j) (hC' j)
    have hw : 0 ≤ β * (ξ j * Z' j) := by
      have := hξ j; have := hZ' j; positivity
    have := mul_le_mul_of_nonneg_left ht hw
    have e : ((D₂ j + Y j) / P' j - (D j + Y j) / P' j) = (D₂ j - D j) / P' j := by
      field_simp; ring
    rw [e] at this
    have h8 := hfoc' j
    have hP'j := (hP' j).ne'
    have e2 : β * (ξ j * Z' j) * (((D j + Y j) / P' j) ^ (-σ) * ((D₂ j - D j) / P' j))
        = m * V j * (D₂ j - D j) := by
      rw [show β * (ξ j * Z' j) * (((D j + Y j) / P' j) ^ (-σ) * ((D₂ j - D j) / P' j))
        = β * (ξ j * (Z' j * ((D j + Y j) / P' j) ^ (-σ))) * (D₂ j - D j) / P' j by ring, h8]
      field_simp
    nlinarith
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
  rw [Finset.sum_sub_distrib] at hsum
  have h0 := periodUtility_tangent hσ hC₂ hC
  have hZm : Z * (C ^ (-σ) * (C₂ - C)) = m * (P * (C₂ - C)) := by rw [hm]; field_simp
  have hm0 : 0 ≤ m := by rw [hm]; have := Real.rpow_pos_of_pos hC (-σ); positivity
  have hS : ∑ j, m * V j * (D₂ j - D j) = m * (∑ j, V j * D₂ j - ∑ j, V j * D j) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hS] at hsum
  have hzt := mul_le_mul_of_nonneg_left h0 hZ.le
  rw [hZm] at hzt
  have hbig : m * (P * (C₂ - C)) + m * (∑ j, V j * D₂ j - ∑ j, V j * D j) ≤ 0 := by
    have : P * (C₂ - C) + (∑ j, V j * D₂ j - ∑ j, V j * D j) ≤ 0 := by linarith
    nlinarith
  unfold nodeObjective
  rw [Finset.mul_sum, Finset.mul_sum]
  nlinarith

/-- Galí (2015), eq. (8), p. 227: for a feasible plan with a binding budget, **optimality is
equivalent to the Arrow-security condition (8) for every state**. -/
theorem arrow_optimal_iff {σ β Z P W : ℝ} {ξ Z' P' V Y : ι → ℝ} {C : ℝ} {D : ι → ℝ}
    (hσ : 0 < σ) (hβ : 0 < β) (hZ : 0 < Z) (hP : 0 < P) (hξ : ∀ j, 0 < ξ j)
    (hZ' : ∀ j, 0 < Z' j) (hP' : ∀ j, 0 < P' j)
    (hfeas : NodeFeasible P W V P' Y C D) (hbind : P * C + ∑ j, V j * D j = W) :
    (∀ C₂ D₂, NodeFeasible P W V P' Y C₂ D₂ →
        nodeObjective σ β Z ξ Z' P' Y C₂ D₂ ≤ nodeObjective σ β Z ξ Z' P' Y C D) ↔
      ∀ j, ArrowFOC σ β Z P ξ Z' P' V Y C D j :=
  ⟨fun hopt => arrow_foc_of_optimal hP hfeas hopt,
    fun hfoc => optimal_of_arrow_foc hσ hβ hZ hP hξ hZ' hP' hfeas hbind hfoc⟩

/-! ### The stochastic discount factor: eqs. (9), (10) and fn. 3 -/

/-- Galí (2015), eq. (9), p. 228: with the stochastic discount factor `Q_{t,t+1} ≡ V/ξ`
(fn. 3), condition (8) is equivalent to `β (C'/C)^{−σ} (Z'/Z) (P/P') = Q_{t,t+1}`. -/
theorem arrow_sdf_iff {σ β Z Z' P P' C C' V ξ : ℝ} (hZ : 0 < Z) (hP : 0 < P)
    (hP' : 0 < P') (hC : 0 < C) (hC' : 0 < C') (hξ : 0 < ξ) :
    V / P * (Z * C ^ (-σ)) = ξ * β * (Z' * C' ^ (-σ)) / P' ↔
      β * (C' / C) ^ (-σ) * (Z' / Z) * (P / P') = V / ξ := by
  rw [Real.div_rpow hC'.le hC.le]
  have ha := Real.rpow_pos_of_pos hC (-σ)
  have hb := Real.rpow_pos_of_pos hC' (-σ)
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    field_simp at h ⊢
    linarith

/-- Galí (2015), fn. 3, p. 228: under complete markets a portfolio paying `D_j` in state `j`
costs `Σ_j V_j D_j = Σ_j ξ_j Q_j D_j`, the conditional expectation `E_t{Q_{t,t+1} D_{t+1}}`. -/
theorem portfolio_price (ξ V D : ι → ℝ) (hξ : ∀ j, 0 < ξ j) :
    ∑ j, V j * D j = ∑ j, ξ j * (V j / ξ j * D j) :=
  Finset.sum_congr rfl fun j _ => by field_simp [(hξ j).ne']

/-- Galí (2015), eq. (10), p. 228: the riskless bond (one unit of domestic currency in every
state) costs `Q_t = Σ_j V_j = E_t{Q_{t,t+1}}`, and under (9) in every state
`Q_t = β E_t{(C'/C)^{−σ}(Z'/Z)(P/P')}`. -/
theorem bond_price {σ β Z P C : ℝ} {ξ Z' P' C' V : ι → ℝ} (hξ : ∀ j, 0 < ξ j)
    (h9 : ∀ j, β * (C' j / C) ^ (-σ) * (Z' j / Z) * (P / P' j) = V j / ξ j) :
    ∑ j, V j = ∑ j, ξ j * (V j / ξ j) ∧
      ∑ j, V j = β * ∑ j, ξ j * ((C' j / C) ^ (-σ) * (Z' j / Z) * (P / P' j)) := by
  have h1 : ∑ j, V j = ∑ j, ξ j * (V j / ξ j) :=
    Finset.sum_congr rfl fun j _ => by field_simp [(hξ j).ne']
  refine ⟨h1, ?_⟩
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← h9 j]
  ring

/-- Galí (2015), eq. (10), p. 228, for an arbitrary expectation system: if (9) holds in every
state, `Q_{t,t+1} = β M_{t+1}` with `M` the nominal marginal rate of substitution, then
`Q_t ≡ E_t{Q_{t,t+1}} = β E_t{M_{t+1}}`. -/
theorem bond_price_expectation {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β : ℝ}
    {Qtt1 M : ℕ → Ω → ℝ} (h9 : ∀ t, Qtt1 t = β • M t) (t : ℕ) :
    𝔼.E t (Qtt1 t) = β • 𝔼.E t (M t) := by
  rw [h9, map_smul]

/-! ### The foreign household: eq. (15) -/

/-- Galí (2015), p. 230: the foreign household's problem is the node problem in domestic
currency with price level `ℰP*`, next-period price `ℰ'_j P*'_j` and no preference shock;
its optimum is characterised by its Arrow condition (necessity and sufficiency). -/
theorem foreign_optimal_iff {σ β Ex Ps W : ℝ} {ξ Exn Psn V Y : ι → ℝ} {C : ℝ} {D : ι → ℝ}
    (hσ : 0 < σ) (hβ : 0 < β) (hEx : 0 < Ex) (hPs : 0 < Ps) (hξ : ∀ j, 0 < ξ j)
    (hP' : ∀ j, 0 < Exn j * Psn j)
    (hfeas : NodeFeasible (Ex * Ps) W V (fun j => Exn j * Psn j) Y C D)
    (hbind : Ex * Ps * C + ∑ j, V j * D j = W) :
    (∀ C₂ D₂, NodeFeasible (Ex * Ps) W V (fun j => Exn j * Psn j) Y C₂ D₂ →
        nodeObjective σ β 1 ξ (fun _ => 1) (fun j => Exn j * Psn j) Y C₂ D₂
          ≤ nodeObjective σ β 1 ξ (fun _ => 1) (fun j => Exn j * Psn j) Y C D) ↔
      ∀ j, ArrowFOC σ β 1 (Ex * Ps) ξ (fun _ => 1) (fun j => Exn j * Psn j) V Y C D j :=
  arrow_optimal_iff hσ hβ one_pos (mul_pos hEx hPs) hξ (fun _ => one_pos) hP' hfeas hbind

/-- Galí (2015), eq. (15), p. 230: the foreign Arrow condition
`(V/(ℰP*)) C*^{−σ} = ξ β C*'^{−σ}/(ℰ'P*')` is equivalent to
`β (C*'/C*)^{−σ} (P*/P*') (ℰ/ℰ') = Q_{t,t+1}`. -/
theorem foreign_sdf_iff {σ β Ex Exn Ps Psn Cs Csn V ξ : ℝ} (hEx : 0 < Ex) (hExn : 0 < Exn)
    (hPs : 0 < Ps) (hPsn : 0 < Psn) (hCs : 0 < Cs) (hCsn : 0 < Csn) (hξ : 0 < ξ) :
    V / (Ex * Ps) * (1 * Cs ^ (-σ)) = ξ * β * (1 * Csn ^ (-σ)) / (Exn * Psn) ↔
      β * (Csn / Cs) ^ (-σ) * (Ps / Psn) * (Ex / Exn) = V / ξ := by
  rw [arrow_sdf_iff one_pos (mul_pos hEx hPs) (mul_pos hExn hPsn) hCs hCsn hξ]
  have : β * (Csn / Cs) ^ (-σ) * (1 / 1) * (Ex * Ps / (Exn * Psn))
      = β * (Csn / Cs) ^ (-σ) * (Ps / Psn) * (Ex / Exn) := by
    field_simp
  rw [this]

/-! ### International risk sharing: eqs. (16) and (17) -/

variable {Ω : Type*}

/-- Galí (2015), (16), p. 231: the risk-sharing ratio `C^{−σ} Z C*^{σ} 𝒬` with the real
exchange rate `𝒬 = ℰP*/P`. -/
noncomputable def rsRatio (σ : ℝ) (C Z Cs P Ps Ex : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  C t ω ^ (-σ) * Z t ω * Cs t ω ^ σ * (Ex t ω * Ps t ω / P t ω)

/-- Galí (2015), eq. (16), p. 231 (**telescoping**): if the domestic condition (9) and the
foreign condition (15) price the same Arrow securities at every date along every path `ω`,
the ratio `C^{−σ} Z C*^{σ} 𝒬` is constant along every path. -/
theorem riskSharing_ratio_const {σ β : ℝ} {C Z P Cs Ps Ex Q : ℕ → Ω → ℝ} (hβ : 0 < β)
    (hC : ∀ t ω, 0 < C t ω) (hZ : ∀ t ω, 0 < Z t ω) (hP : ∀ t ω, 0 < P t ω)
    (hCs : ∀ t ω, 0 < Cs t ω) (hPs : ∀ t ω, 0 < Ps t ω) (hEx : ∀ t ω, 0 < Ex t ω)
    (h9 : ∀ t ω, β * (C (t + 1) ω / C t ω) ^ (-σ) * (Z (t + 1) ω / Z t ω) *
      (P t ω / P (t + 1) ω) = Q t ω)
    (h15 : ∀ t ω, β * (Cs (t + 1) ω / Cs t ω) ^ (-σ) * (Ps t ω / Ps (t + 1) ω) *
      (Ex t ω / Ex (t + 1) ω) = Q t ω) :
    ∀ t ω, rsRatio σ C Z Cs P Ps Ex t ω = rsRatio σ C Z Cs P Ps Ex 0 ω := by
  intro t ω
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [← ih]
    have h := (h9 t ω).trans (h15 t ω).symm
    have hc0 := hC t ω; have hc1 := hC (t + 1) ω
    have hs0 := hCs t ω; have hs1 := hCs (t + 1) ω
    have hz0 := hZ t ω; have hz1 := hZ (t + 1) ω
    have hp0 := hP t ω; have hp1 := hP (t + 1) ω
    have hq0 := hPs t ω; have hq1 := hPs (t + 1) ω
    have he0 := hEx t ω; have he1 := hEx (t + 1) ω
    rw [Real.div_rpow hc1.le hc0.le, Real.div_rpow hs1.le hs0.le] at h
    have a0 := Real.rpow_pos_of_pos hc0 (-σ); have a1 := Real.rpow_pos_of_pos hc1 (-σ)
    have b0 := Real.rpow_pos_of_pos hs0 (-σ); have b1 := Real.rpow_pos_of_pos hs1 (-σ)
    have g0 : Cs t ω ^ σ = (Cs t ω ^ (-σ))⁻¹ := by rw [Real.rpow_neg hs0.le, inv_inv]
    have g1 : Cs (t + 1) ω ^ σ = (Cs (t + 1) ω ^ (-σ))⁻¹ := by
      rw [Real.rpow_neg hs1.le, inv_inv]
    unfold rsRatio
    rw [g0, g1]
    set x0 := C t ω ^ (-σ); set x1 := C (t + 1) ω ^ (-σ)
    set y0 := Cs t ω ^ (-σ); set y1 := Cs (t + 1) ω ^ (-σ)
    have h' : x1 / x0 * (Z (t + 1) ω / Z t ω) * (P t ω / P (t + 1) ω)
        = y1 / y0 * (Ps t ω / Ps (t + 1) ω) * (Ex t ω / Ex (t + 1) ω) := by
      have := mul_left_cancel₀ hβ.ne' (by simpa only [mul_assoc] using h)
      simpa only [mul_assoc] using this
    have hB : 0 < y1 / y0 * (Ps t ω / Ps (t + 1) ω) * (Ex t ω / Ex (t + 1) ω) := by positivity
    have key : x1 * Z (t + 1) ω * y1⁻¹ * (Ex (t + 1) ω * Ps (t + 1) ω / P (t + 1) ω)
        = x0 * Z t ω * y0⁻¹ * (Ex t ω * Ps t ω / P t ω)
          * (x1 / x0 * (Z (t + 1) ω / Z t ω) * (P t ω / P (t + 1) ω))
          / (y1 / y0 * (Ps t ω / Ps (t + 1) ω) * (Ex t ω / Ex (t + 1) ω)) := by
      field_simp
    rw [key, h', mul_div_assoc, div_self hB.ne', mul_one]

/-- Galí (2015), eq. (16), p. 231: the constant `ϑ = R_0^{−1/σ}` determined by initial
conditions, `R_0` the initial risk-sharing ratio. -/
noncomputable def vartheta (σ : ℝ) (C Z Cs P Ps Ex : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  rsRatio σ C Z Cs P Ps Ex 0 ω ^ (-1 / σ)

/-- Galí (2015), eq. (16), p. 231: from a constant ratio, `C = ϑ C* Z^{1/σ} 𝒬^{1/σ}` at every
date along every path (`σ > 0`). -/
theorem riskSharing {σ : ℝ} (hσ : 0 < σ) {C Z P Cs Ps Ex : ℕ → Ω → ℝ}
    (hC : ∀ t ω, 0 < C t ω) (hZ : ∀ t ω, 0 < Z t ω) (hP : ∀ t ω, 0 < P t ω)
    (hCs : ∀ t ω, 0 < Cs t ω) (hPs : ∀ t ω, 0 < Ps t ω) (hEx : ∀ t ω, 0 < Ex t ω)
    (hconst : ∀ t ω, rsRatio σ C Z Cs P Ps Ex t ω = rsRatio σ C Z Cs P Ps Ex 0 ω) (t : ℕ)
    (ω : Ω) :
    C t ω = vartheta σ C Z Cs P Ps Ex ω * Cs t ω * Z t ω ^ (1 / σ) *
      (Ex t ω * Ps t ω / P t ω) ^ (1 / σ) := by
  have hc := hC t ω; have hz := hZ t ω; have hs := hCs t ω
  have hq : 0 < Ex t ω * Ps t ω / P t ω := by
    have := hEx t ω; have := hPs t ω; have := hP t ω; positivity
  unfold vartheta
  rw [← hconst t ω, rsRatio]
  set q := Ex t ω * Ps t ω / P t ω
  have hσ0 : σ ≠ 0 := hσ.ne'
  rw [Real.mul_rpow (by positivity) hq.le, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) hz.le, ← Real.rpow_mul hc.le, ← Real.rpow_mul hs.le]
  have e1 : -σ * (-1 / σ) = 1 := by field_simp
  have e2 : σ * (-1 / σ) = -1 := by field_simp
  rw [e1, e2, Real.rpow_one, Real.rpow_neg_one]
  have hz1 : Z t ω ^ (-1 / σ) * Z t ω ^ (1 / σ) = 1 := by
    rw [← Real.rpow_add hz, show -1 / σ + 1 / σ = (0 : ℝ) by ring, Real.rpow_zero]
  have hq1 : q ^ (-1 / σ) * q ^ (1 / σ) = 1 := by
    rw [← Real.rpow_add hq, show -1 / σ + 1 / σ = (0 : ℝ) by ring, Real.rpow_zero]
  symm
  calc _ = C t ω * ((Cs t ω)⁻¹ * Cs t ω) * (Z t ω ^ (-1 / σ) * Z t ω ^ (1 / σ))
        * (q ^ (-1 / σ) * q ^ (1 / σ)) := by ring
    _ = C t ω := by rw [inv_mul_cancel₀ hs.ne', hz1, hq1]; ring

/-- Galí (2015), p. 231: under symmetric initial conditions (`C_0 = C*_0`, `Z_0 = 1`,
`𝒬_0 = 1`), `ϑ = 1`. -/
theorem vartheta_eq_one {σ : ℝ} {C Z P Cs Ps Ex : ℕ → Ω → ℝ} {ω : Ω} (hC0 : 0 < C 0 ω)
    (hsym : Cs 0 ω = C 0 ω) (hZ0 : Z 0 ω = 1) (hQ0 : Ex 0 ω * Ps 0 ω / P 0 ω = 1) :
    vartheta σ C Z Cs P Ps Ex ω = 1 := by
  unfold vartheta rsRatio
  rw [hsym, hZ0, hQ0, mul_one, mul_one, ← Real.rpow_add hC0, neg_add_cancel, Real.rpow_zero,
    Real.one_rpow]

/-- Galí (2015), eq. (17), p. 231 (first line): with `ϑ = 1` and `C* = Y*`,
`C = Y* Z^{1/σ} 𝒬^{1/σ}` gives `c = y* + (1/σ)(z + q)`. -/
theorem riskSharing_log {σ C Ys Z Qr : ℝ} (hYs : 0 < Ys) (hZ : 0 < Z) (hQr : 0 < Qr)
    (h16 : C = Ys * Z ^ (1 / σ) * Qr ^ (1 / σ)) :
    Real.log C = Real.log Ys + 1 / σ * (Real.log Z + Real.log Qr) := by
  rw [h16, Real.log_mul (by positivity) (by positivity), Real.log_mul hYs.ne' (by positivity),
    Real.log_rpow hZ, Real.log_rpow hQr]
  ring

/-- Galí (2015), eq. (17), p. 231 (second line, **general `η`**): with the law of one price
`ℰP* = P_F` and the CES CPI, `c = y* + z/σ + g(s)/σ` where `g(s) = s − h(s)` satisfies
`g(0) = 0`, `g'(0) = 1 − υ` (`Identities.hasDerivAt_rerGap`): the second line of (17) holds
to first order. -/
theorem riskSharing_log_tot {υ η σ C Ys Z pH pF : ℝ} (hυ0 : 0 < υ) (hυ1 : υ < 1)
    (hη1 : η ≠ 1) (hYs : 0 < Ys) (hZ : 0 < Z)
    (h16 : C = Ys * Z ^ (1 / σ) *
      (Real.exp pF / cpi υ η (Real.exp pH) (Real.exp pF)) ^ (1 / σ)) :
    Real.log C = Real.log Ys + 1 / σ * Real.log Z + 1 / σ * rerGap υ η (pF - pH) := by
  have hpos := cpi_pos (η := η) hυ0 hυ1 (Real.exp_pos pH) (Real.exp_pos pF)
  rw [riskSharing_log hYs hZ (div_pos (Real.exp_pos _) hpos) h16,
    (rer_eq hυ0 hυ1 hη1 pH pF).2]
  ring

/-- Galí (2015), eq. (17), p. 231, **exact at `η = 1`**:
`c = y* + z/σ + ((1−υ)/σ) s`. -/
theorem riskSharing_log_cd {υ σ C Ys Z pH pF : ℝ} (hYs : 0 < Ys) (hZ : 0 < Z)
    (h16 : C = Ys * Z ^ (1 / σ) *
      (Real.exp pF / cpiCD υ (Real.exp pH) (Real.exp pF)) ^ (1 / σ)) :
    Real.log C = Real.log Ys + 1 / σ * Real.log Z + (1 - υ) / σ * (pF - pH) := by
  have hpos : 0 < cpiCD υ (Real.exp pH) (Real.exp pF) := by unfold cpiCD; positivity
  rw [riskSharing_log hYs hZ (div_pos (Real.exp_pos _) hpos) h16, rer_cd]
  ring

end Gali.OpenEconomy.RiskSharing
