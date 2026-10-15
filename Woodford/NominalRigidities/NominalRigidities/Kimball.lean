/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.StrategicComplementarity
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Kimball demand, variable markups and intermediate inputs

Woodford (2003), *Interest and Prices*, Appendix B, §B.1 "Non-CES demand and variable markups"
(pp. 656–657) and §B.2 "Proof of Proposition 3.3" (pp. 657–658), with Chapter 3, (1.38)–(1.43),
pp. 168–171.

The appendix proof of Proposition 3.3 is a sketch. Here it is completed:

* (B.1)–(B.3): with finitely many goods, the demand (B.2) with the index (B.3) is the
  cost-minimising bundle for the Kimball aggregator (`kimball_demand_cost_min`); demand is
  unique (`kimball_demand_unique`); CES is the case `ψ(x) = x^{(θ−1)/θ}` (`ces_theta_const`).
* (B.4): `kimball_demand_exists` (implicit function theorem) and `kimball_demand_elasticity`:
  the elasticity of demand is `θ(x) = −ψ'(x)/(xψ''(x))`; `kimball_log_demand`: log demand has
  slope `−θ(1)` at the symmetric point.
* (B.5): `kimball_foc_iff`: the flexible-price supplier's first-order condition is
  `p/P = µ(y/Y) s`, `µ(x) = θ(x)/(θ(x) − 1)` (this is (1.39)).
* `markup_elasticity`, `markup_elasticity_pos_iff`: `ε_µ = −θ'(1)/(θ(θ − 1))`, positive iff
  `θ(·)` is decreasing at `1` (p. 169).
* (1.42), (B.8): `leontief_feasible_iff`, `leontief_cost_min`, `leontief_marginal_cost`.
* The value-added/gross-output identification the book leaves unstated:
  `value_added_log_deviation`, `aggregate_value_added_hasDerivAt`, `final_demand_value_added`.
* (B.9): `steady_state_B9`, `steady_state_needs_sm_lt` (the hypothesis `s_m < µ⁻¹` is necessary
  and sufficient for a positive steady-state value-added marginal cost), `steady_state_exists`.
* `kimball_unit_cost_symmetric` and `kimball_unit_cost_counterexample`: the claim (p. 657) that
  the cost per unit of the materials aggregate is `P` holds at symmetric prices but is false in
  general for a non-CES aggregator.
* `thetaK_hasStrictDerivAt`, `strictDerivs_of_contDiff`: `θ'(1)` computed from `ψ` (C³).
* `prop_3_3_complete`, `prop_3_3_from_psi` ((B.6)): from the primitives `ψ` (C³ near 1), the
  log value-added marginal cost and `s_m`, the notional SRAS exists and has slope
  `(1 − µ s_m)(s_y + s_Y)/(1 + θ[ε_µ + (1 − µ s_m) s_y])`.
* A continuum of goods (a probability space): `kimball_demand_cost_min_continuum` and
  `kimball_unit_cost_ae` (unit cost of the aggregate is `P` when all but a null set of goods
  charge `P`, the measure-zero deviating industry of B.2).
-/

namespace Woodford.NominalRigidities.Kimball

open Filter Topology

/-! ### (B.1)–(B.3): Kimball demand as cost minimisation -/

/-- Woodford (2003), eqs. (B.1)–(B.3), p. 656 (finitely many goods with weights `w`): if the
bundle `c` satisfies the demand curves (B.2) `ψ'(cᵢ/C) = ψ'(1) pᵢ/P` and the index condition
(B.3) (equivalently the aggregator (B.1) `∑ wᵢ ψ(cᵢ/C) = 1`), then it minimises expenditure
`∑ wᵢ pᵢ cᵢ` among all positive bundles delivering at least `C`, for `ψ` concave and
increasing at `1`. -/
theorem kimball_demand_cost_min {ι : Type*} [Fintype ι] {ψ ψ1 : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) ψ) (hder : ∀ x, 0 < x → HasDerivAt ψ (ψ1 x) x)
    (hψ1 : 0 < ψ1 1) {C P : ℝ} (hC : 0 < C) (hP : 0 < P) {w p c c' : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (hB2 : ∀ i, ψ1 (c i / C) = ψ1 1 * (p i / P)) (hB3 : ∑ i, w i * ψ (c i / C) = 1)
    (hfeas : 1 ≤ ∑ i, w i * ψ (c' i / C)) :
    ∑ i, w i * p i * c i ≤ ∑ i, w i * p i * c' i := by
  have k : 0 < ψ1 1 / (P * C) := div_pos hψ1 (mul_pos hP hC)
  have key : ∀ i, w i * (ψ (c' i / C) - ψ (c i / C)) ≤
      ψ1 1 / (P * C) * (w i * p i * c' i - w i * p i * c i) := by
    intro i
    have ht := Predetermined.concave_tangent_le hconc (Set.mem_Ioi.mpr (div_pos (hc i) hC))
      (Set.mem_Ioi.mpr (div_pos (hc' i) hC)) (hder _ (div_pos (hc i) hC))
    rw [hB2 i] at ht
    have e : ψ1 1 / (P * C) * (w i * p i * c' i - w i * p i * c i) =
        w i * (ψ1 1 * (p i / P) * (c' i / C - c i / C)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (hw i)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  have hl : 0 ≤ ∑ i, w i * (ψ (c' i / C) - ψ (c i / C)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith
  have := le_trans hl hsum
  have h2 : 0 ≤ ∑ i, w i * p i * c' i - ∑ i, w i * p i * c i := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg k hneg
    linarith
  linarith

/-- Woodford (2003), (B.2), p. 656: with `ψ` strictly concave (so `ψ'` strictly decreasing),
the relative demand solving (B.2) is unique. -/
theorem kimball_demand_unique {ψ1 : ℝ → ℝ} (hanti : StrictAntiOn ψ1 (Set.Ioi 0)) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (h : ψ1 x = ψ1 y) : x = y :=
  hanti.injOn hx hy h

/-- Woodford (2003), p. 657 (cost of the materials aggregate) at symmetric prices: if every
price equals `P`, the cost-minimising bundle is `cᵢ = C` and its cost is `P C`, so the unit cost
of the aggregate equals `P`. -/
theorem kimball_unit_cost_symmetric {ι : Type*} [Fintype ι] {ψ1 : ℝ → ℝ}
    (hanti : StrictAntiOn ψ1 (Set.Ioi 0)) {C P : ℝ} (hC : 0 < C)
    (hP : 0 < P) {w c : ι → ℝ} (hw : ∑ i, w i = 1) (hc : ∀ i, 0 < c i)
    (hB2 : ∀ i, ψ1 (c i / C) = ψ1 1 * (P / P)) :
    (∀ i, c i = C) ∧ ∑ i, w i * P * c i = P * C := by
  have hcC : ∀ i, c i = C := by
    intro i
    have h := hB2 i
    rw [div_self hP.ne', mul_one] at h
    have := hanti.injOn (div_pos (hc i) hC) (show (0 : ℝ) < 1 from one_pos) h
    field_simp at this
    exact this
  refine ⟨hcC, ?_⟩
  simp only [hcC]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hw, one_mul]

/-- Woodford (2003), p. 657 (a non-CES aggregator): `ψ(x) = (4x − x²)/3`, concave with
`ψ(1) = 1` and increasing on `(0, 2)`. -/
noncomputable def psiQ (x : ℝ) : ℝ := (4 * x - x ^ 2) / 3

/-- Woodford (2003), p. 657, CORRECTION: "the cost per unit of materials inputs will be the same
price index `P_t`" is false for a general Kimball aggregator. With `ψ = psiQ`, two goods of
weight `1/2`, `P = C = 1` and prices `(7/5, 1/5)`, the bundle `(3/5, 9/5)` satisfies (B.2) and
(B.3) and minimises cost among all bundles delivering `C = 1`, yet its cost is `3/5 ≠ P = 1`.
(The claim holds at symmetric prices, `kimball_unit_cost_symmetric`, which is the case used in
§B.2, where a single industry of measure zero deviates.) -/
theorem kimball_unit_cost_counterexample :
    psiQ 1 = 1 ∧ ConcaveOn ℝ (Set.Ioi 0) psiQ ∧
    (∀ x, HasDerivAt psiQ ((4 - 2 * x) / 3) x) ∧
    (4 - 2 * (3 / 5 : ℝ)) / 3 = (4 - 2 * 1) / 3 * (7 / 5 / 1) ∧
    (4 - 2 * (9 / 5 : ℝ)) / 3 = (4 - 2 * 1) / 3 * (1 / 5 / 1) ∧
    (1 / 2 : ℝ) * psiQ (3 / 5 / 1) + 1 / 2 * psiQ (9 / 5 / 1) = 1 ∧
    (1 / 2 : ℝ) * (7 / 5) * (3 / 5) + 1 / 2 * (1 / 5) * (9 / 5) = 3 / 5 ∧
    (∀ c' : Fin 2 → ℝ, (∀ i, 0 < c' i) →
      1 ≤ ∑ i, (1 / 2 : ℝ) * psiQ (c' i / 1) →
      (3 / 5 : ℝ) ≤ ∑ i, (1 / 2 : ℝ) * ![7 / 5, 1 / 5] i * c' i) := by
  have hconc : ConcaveOn ℝ (Set.Ioi 0) psiQ := by
    refine ⟨convex_Ioi 0, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul, psiQ]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [sq_nonneg (x - y), mul_nonneg ha hb]
  have hder : ∀ x, HasDerivAt psiQ ((4 - 2 * x) / 3) x := by
    intro x
    have := (((hasDerivAt_id' x).const_mul 4).sub (hasDerivAt_pow 2 x)).div_const 3
    unfold psiQ
    convert this using 1
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
  refine ⟨by norm_num [psiQ], hconc, hder, by norm_num, by norm_num, by norm_num [psiQ],
    by norm_num, ?_⟩
  intro c' hc' hfeas
  have := kimball_demand_cost_min (ι := Fin 2) hconc (fun x _ => hder x)
    (by norm_num) one_pos one_pos (w := fun _ => 1 / 2) (p := ![7 / 5, 1 / 5])
    (c := ![3 / 5, 9 / 5]) (c' := c') (fun _ => by norm_num)
    (fun i => by fin_cases i <;> norm_num) hc'
    (fun i => by fin_cases i <;> norm_num) (by simp [Fin.sum_univ_two, psiQ]; norm_num) hfeas
  simp only [Fin.sum_univ_two] at this ⊢
  norm_num at this ⊢
  linarith

/-- Woodford (2003), p. 168: the Dixit–Stiglitz case `ψ(x) = x^{(θ−1)/θ}`: the demand
elasticity `θ(x) = −ψ'(x)/(xψ''(x))` equals the constant `θ`. -/
theorem ces_theta_const {θ x : ℝ} (hθ : 1 < θ) (hx : 0 < x) :
    -(((θ - 1) / θ) * x ^ ((θ - 1) / θ - 1)) /
      (x * (((θ - 1) / θ) * ((θ - 1) / θ - 1) * x ^ ((θ - 1) / θ - 1 - 1))) = θ := by
  have hθ0 : θ ≠ 0 := by linarith
  have hθ1 : θ - 1 ≠ 0 := by linarith
  have hsplit : x ^ ((θ - 1) / θ - 1) = x * x ^ ((θ - 1) / θ - 1 - 1) := by
    rw [show (θ - 1) / θ - 1 = 1 + ((θ - 1) / θ - 1 - 1) by ring, Real.rpow_add hx,
      Real.rpow_one]
    ring_nf
  have hpos : 0 < x ^ ((θ - 1) / θ - 1 - 1) := Real.rpow_pos_of_pos hx _
  rw [hsplit]
  field_simp
  ring

/-! ### (B.4): the elasticity of demand -/

/-- Woodford (2003), eq. (B.4), p. 656: `θ(x) = −ψ'(x)/(x ψ''(x))`. -/
noncomputable def thetaK (ψ1 ψ2 : ℝ → ℝ) (x : ℝ) : ℝ := -ψ1 x / (x * ψ2 x)

/-- Woodford (2003), (B.2) and (B.4), p. 656 (existence): if `ψ'` is strictly differentiable at
`1` with `ψ''(1) ≠ 0`, the relative demand `d(r)` solving `ψ'(d(r)) = ψ'(1) r` exists near
`r = 1`, is locally unique, has `d(1) = 1` and `d'(1) = ψ'(1)/ψ''(1) = −θ(1)`. -/
theorem kimball_demand_exists {ψ1 : ℝ → ℝ} {ψ2one : ℝ} (hψ : HasStrictDerivAt ψ1 ψ2one 1)
    (h2 : ψ2one ≠ 0) :
    ∃ d : ℝ → ℝ, d 1 = 1 ∧ (∀ᶠ r in 𝓝 1, ψ1 (d r) = ψ1 1 * r) ∧
      (∀ᶠ q in 𝓝 ((1 : ℝ), (1 : ℝ)), ψ1 q.2 = ψ1 1 * q.1 ↔ d q.1 = q.2) ∧
      HasStrictDerivAt d (ψ1 1 / ψ2one) 1 ∧ ψ1 1 / ψ2one = -thetaK ψ1 (fun _ => ψ2one) 1 := by
  set f : ℝ × ℝ → ℝ := fun q => ψ1 q.2 - ψ1 1 * q.1
  set L : ℝ × ℝ →L[ℝ] ℝ := ψ2one • ContinuousLinearMap.snd ℝ ℝ ℝ -
    ψ1 1 • ContinuousLinearMap.fst ℝ ℝ ℝ with hL
  have hf : HasStrictFDerivAt f L ((1 : ℝ), (1 : ℝ)) := by
    have h1 : HasStrictFDerivAt (fun q : ℝ × ℝ => ψ1 q.2)
        (ψ2one • ContinuousLinearMap.snd ℝ ℝ ℝ) ((1 : ℝ), (1 : ℝ)) :=
      HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq ((1 : ℝ), (1 : ℝ)) hψ
        hasStrictFDerivAt_snd rfl
    exact h1.sub (hasStrictFDerivAt_fst.const_mul (ψ1 1))
  have v01 : L (0, 1) = ψ2one := by simp [hL]
  have v10 : L (1, 0) = -ψ1 1 := by simp [hL]
  obtain ⟨d, h1, h2', h3, h4⟩ := Predetermined.implicit_function_real hf (by rw [v01]; exact h2)
  have hf1 : f ((1 : ℝ), (1 : ℝ)) = 0 := by simp [f]
  refine ⟨d, h1, ?_, ?_, ?_, ?_⟩
  · filter_upwards [h2'] with r hr
    rw [hf1] at hr
    simp only [f] at hr
    linarith
  · filter_upwards [h3] with q hq
    rw [hf1] at hq
    simp only [f] at hq
    rw [← hq, sub_eq_zero]
  · convert h4 using 1
    rw [v01, v10]
    ring
  · unfold thetaK
    field_simp

/-- Woodford (2003), eq. (B.4), p. 656: at any relative price `r` where the demand `d` solving
`ψ'(d(r)) = ψ'(1) r` is differentiable, the elasticity of demand is
`r d'(r)/d(r) = −θ(d(r))`. -/
theorem kimball_demand_elasticity {ψ1 ψ2 d : ℝ → ℝ} {r d' : ℝ} (hr : r ≠ 0)
    (hd : HasDerivAt d d' r) (hdr : d r ≠ 0) (hψ : HasDerivAt ψ1 (ψ2 (d r)) (d r))
    (h2 : ψ2 (d r) ≠ 0) (hid : ∀ᶠ s in 𝓝 r, ψ1 (d s) = ψ1 1 * s) :
    r * d' / d r = -thetaK ψ1 ψ2 (d r) := by
  have hcomp : HasDerivAt (fun s => ψ1 (d s)) (ψ2 (d r) * d') r := hψ.comp r hd
  have hrhs : HasDerivAt (fun s => ψ1 (d s)) (ψ1 1) r :=
    ((hasDerivAt_id r).const_mul (ψ1 1)).congr_of_eventuallyEq hid |>.congr_deriv (by simp)
  have hu := hcomp.unique hrhs
  have hval : ψ1 (d r) = ψ1 1 * r := hid.self_of_nhds
  have hd' : d' = ψ1 1 / ψ2 (d r) := by
    rw [eq_div_iff h2]; linarith
  unfold thetaK
  rw [hval, hd']
  field_simp

/-- Woodford (2003), (1.40) and (B.4): log demand `u ↦ log d(eᵘ)` (log relative demand as a
function of the log relative price) vanishes at `0` and has strict derivative `−θ` there, given
`d(1) = 1` and `d'(1) = −θ`. -/
theorem kimball_log_demand {d : ℝ → ℝ} {θ : ℝ} (hd : HasStrictDerivAt d (-θ) 1) (hd1 : d 1 = 1) :
    Real.log (d (Real.exp 0)) = 0 ∧
    HasStrictDerivAt (fun u => Real.log (d (Real.exp u))) (-θ) 0 := by
  refine ⟨by simp [hd1], ?_⟩
  have he : HasStrictDerivAt Real.exp 1 0 := by simpa using Real.hasStrictDerivAt_exp 0
  have hde : HasStrictDerivAt (fun u => d (Real.exp u)) (-θ * 1) 0 := by
    have hd' : HasStrictDerivAt d (-θ) (Real.exp 0) := by rw [Real.exp_zero]; exact hd
    exact hd'.comp 0 he
  have hl := hde.log (by simp [hd1])
  convert hl using 1
  simp [hd1]

/-! ### (B.5): the desired markup -/

/-- Woodford (2003), (B.5), p. 656: `µ(x) = θ(x)/(θ(x) − 1)`. -/
noncomputable def muK (θf : ℝ → ℝ) (x : ℝ) : ℝ := θf x / (θf x - 1)

/-- Woodford (2003), (B.5) and (1.39), pp. 656 and 168: nominal profit
`p Y d(p/P) − P Γ(Y d(p/P))` (real total cost `Γ`, marginal cost `s = Γ'`) has derivative
`Y d(r) (1 − θ + θ P s/p)` at `p` when demand has elasticity `r d'/d = −θ` there, so the
first-order condition holds if and only if `p/P = µ s` with `µ = θ/(θ − 1)` (`θ > 1`): the
desired relative price (1.39). -/
theorem kimball_foc_iff {d Γ : ℝ → ℝ} {Y P p d' s θx : ℝ} (hY : 0 < Y) (hP : 0 < P)
    (hp : 0 < p) (hd : HasDerivAt d d' (p / P)) (hdpos : 0 < d (p / P))
    (hel : p / P * d' / d (p / P) = -θx) (hθ : 1 < θx)
    (hΓ : HasDerivAt Γ s (Y * d (p / P))) :
    HasDerivAt (fun q => q * (Y * d (q / P)) - P * Γ (Y * d (q / P)))
        (Y * d (p / P) * (1 - θx + θx * P * s / p)) p ∧
      (Y * d (p / P) * (1 - θx + θx * P * s / p) = 0 ↔ p / P = θx / (θx - 1) * s) := by
  have hr : HasDerivAt (fun q => q / P) (1 / P) p := by
    simpa using (hasDerivAt_id p).div_const P
  have hD : HasDerivAt (fun q => Y * d (q / P)) (Y * (d' * (1 / P))) p :=
    (hd.comp p hr).const_mul Y
  have hd'eq : d' = -θx * d (p / P) / (p / P) := by
    field_simp at hel ⊢
    linarith
  constructor
  · have := ((hasDerivAt_id p).mul hD).sub ((hΓ.comp p hD).const_mul P)
    convert this using 1
    · funext q
      simp
    · rw [hd'eq]
      simp only [id]
      field_simp
      ring
  · have hθ1 : θx - 1 ≠ 0 := by linarith
    have hYd : Y * d (p / P) ≠ 0 := (mul_pos hY hdpos).ne'
    constructor
    · intro h
      have h' := (mul_eq_zero.mp h).resolve_left hYd
      field_simp at h' ⊢
      linarith
    · intro h
      apply mul_eq_zero_of_right
      rw [div_mul_eq_mul_div, eq_div_iff hθ1] at h
      field_simp at h
      field_simp
      linarith

/-- Woodford (2003), (1.40), p. 168: the log desired markup relative to steady state,
`m(u) = log(µ(eᵘ)/µ(1))`. -/
noncomputable def markupLog (θf : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.log (muK θf (Real.exp u) / muK θf 1)

/-- Woodford (2003), p. 168: the markup elasticity at the symmetric point,
`ε_µ = d log µ(x)/d log x |_{x=1} = −θ'(1)/(θ(1)(θ(1) − 1))`, with `m(0) = 0`. -/
theorem markup_elasticity {θf : ℝ → ℝ} {θ' : ℝ} (hθ : HasStrictDerivAt θf θ' 1)
    (h1 : 1 < θf 1) :
    markupLog θf 0 = 0 ∧
    HasStrictDerivAt (markupLog θf) (-θ' / (θf 1 * (θf 1 - 1))) 0 := by
  have hθ0 : θf 1 ≠ 0 := by linarith
  have hθ1 : θf 1 - 1 ≠ 0 := by linarith
  have hmu1 : muK θf 1 ≠ 0 := by unfold muK; exact div_ne_zero hθ0 hθ1
  refine ⟨by simp [markupLog, div_self hmu1], ?_⟩
  have he : HasStrictDerivAt Real.exp 1 0 := by simpa using Real.hasStrictDerivAt_exp 0
  have hte : HasStrictDerivAt (fun u => θf (Real.exp u)) (θ' * 1) 0 := by
    have hθ' : HasStrictDerivAt θf θ' (Real.exp 0) := by rw [Real.exp_zero]; exact hθ
    exact hθ'.comp 0 he
  have hval : θf (Real.exp 0) = θf 1 := by rw [Real.exp_zero]
  have hq : HasStrictDerivAt (fun u => θf (Real.exp u) / (θf (Real.exp u) - 1))
      ((θ' * 1 * (θf (Real.exp 0) - 1) - θf (Real.exp 0) * (θ' * 1)) /
        (θf (Real.exp 0) - 1) ^ 2) 0 :=
    hte.div (hte.sub_const 1) (by rw [hval]; exact hθ1)
  have hmu := hq.div_const (muK θf 1)
  have hne : θf (Real.exp 0) / (θf (Real.exp 0) - 1) / muK θf 1 ≠ 0 := by
    rw [hval]; exact div_ne_zero (div_ne_zero hθ0 hθ1) hmu1
  have hlog := hmu.log hne
  have e : markupLog θf =
      fun u => Real.log (θf (Real.exp u) / (θf (Real.exp u) - 1) / muK θf 1) := rfl
  rw [e]
  convert hlog using 1
  simp only [hval, muK]
  field_simp
  ring

/-- Woodford (2003), p. 169: "a positive ε_µ — which means θ(x) decreasing in x": for
`θ(1) > 1`, `ε_µ > 0` if and only if `θ'(1) < 0`. -/
theorem markup_elasticity_pos_iff {θ1 θ' : ℝ} (h1 : 1 < θ1) :
    0 < -θ' / (θ1 * (θ1 - 1)) ↔ θ' < 0 := by
  have hp : 0 < θ1 * (θ1 - 1) := mul_pos (by linarith) (by linarith)
  rw [div_pos_iff_of_pos_right hp]
  constructor <;> intro h <;> linarith

/-! ### (1.42), (B.7)–(B.9): Leontief technology and the steady state -/

/-- Woodford (2003), eq. (1.42), p. 170: for `0 < s_m < 1`, gross output `y` is feasible from
value added `a` and materials `m` (`y ≤ min(a/(1 − s_m), m/s_m)`) iff
`(1 − s_m) y ≤ a` and `s_m y ≤ m`. -/
theorem leontief_feasible_iff {sm y a m : ℝ} (h0 : 0 < sm) (h1 : sm < 1) :
    y ≤ min (a / (1 - sm)) (m / sm) ↔ (1 - sm) * y ≤ a ∧ sm * y ≤ m := by
  rw [le_min_iff, le_div_iff₀ (by linarith), le_div_iff₀ h0, mul_comm y, mul_comm y]

/-- Woodford (2003), (1.42) and (B.8), pp. 170 and 657: with a nondecreasing real cost `C_VA` of
value added and materials priced at `P` (real price one), the cheapest way to produce `y` is
`a = (1 − s_m) y`, `m = s_m y`, at real cost `C_VA((1 − s_m) y) + s_m y`. -/
theorem leontief_cost_min {CVA : ℝ → ℝ} (hmono : Monotone CVA) {sm y a m : ℝ}
    (ha : (1 - sm) * y ≤ a) (hm : sm * y ≤ m) :
    CVA ((1 - sm) * y) + sm * y ≤ CVA a + m := by
  have := hmono ha
  linarith

/-- Woodford (2003), eq. (B.8), p. 657: real marginal cost of gross output is
`s = (1 − s_m) s^{VA} + s_m`, the derivative of the minimal cost `C_VA((1 − s_m) y) + s_m y`,
where `s^{VA} = C_VA'` is the marginal cost of value added. -/
theorem leontief_marginal_cost {CVA sVA : ℝ → ℝ} {sm y : ℝ}
    (hC : HasDerivAt CVA (sVA ((1 - sm) * y)) ((1 - sm) * y)) :
    HasDerivAt (fun z => CVA ((1 - sm) * z) + sm * z) ((1 - sm) * sVA ((1 - sm) * y) + sm) y := by
  have h1 : HasDerivAt (fun z => (1 - sm) * z) (1 - sm) y := by
    simpa using (hasDerivAt_id y).const_mul (1 - sm)
  have := (hC.comp y h1).add ((hasDerivAt_id y).const_mul sm)
  convert this using 1
  · funext z
    simp
  · ring

/-- Woodford (2003), p. 658 (the value-added/gross-output identification left implicit in
B.2): firm value added is `(1 − s_m) y`, so its log deviation equals that of gross output. -/
theorem value_added_log_deviation {sm y ybar : ℝ} (h1 : sm < 1) (hy : 0 < y) (hyb : 0 < ybar) :
    Real.log ((1 - sm) * y) - Real.log ((1 - sm) * ybar) = Real.log y - Real.log ybar := by
  have h : 0 < 1 - sm := by linarith
  rw [Real.log_mul h.ne' hy.ne', Real.log_mul h.ne' hyb.ne']
  ring

/-- Woodford (2003), p. 658: aggregate value added `Y − s_m X` (with `X̄ = Ȳ` and `X̂ = Ŷ` to first
order) has log deviation equal to `Ŷ` to first order: `b ↦ log(Ȳ eᵇ − s_m Ȳ e^{x(b)})` has
derivative `1` at `0` when `x(0) = 0`, `x'(0) = 1` and `s_m < 1`. -/
theorem aggregate_value_added_hasDerivAt {sm Ybar : ℝ} {x : ℝ → ℝ} (h1 : sm < 1)
    (hY : 0 < Ybar) (hx : HasDerivAt x 1 0) (hx0 : x 0 = 0) :
    HasDerivAt (fun b => Real.log (Ybar * Real.exp b - sm * (Ybar * Real.exp (x b)))) 1 0 := by
  have he : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
  have hex : HasDerivAt (fun b => Real.exp (x b)) (Real.exp (x 0) * 1) 0 := hx.exp
  have hin := (he.const_mul Ybar).sub ((hex.const_mul Ybar).const_mul sm)
  have hne : Ybar * Real.exp 0 - sm * (Ybar * Real.exp (x 0)) ≠ 0 := by
    rw [hx0, Real.exp_zero]
    have : 0 < Ybar * (1 - sm) := mul_pos hY (by linarith)
    nlinarith
  have hl := hin.log hne
  have hs1 : (1 : ℝ) - sm ≠ 0 := (by linarith : (0 : ℝ) < 1 - sm).ne'
  convert hl using 1
  simp only [Pi.sub_apply, hx0, Real.exp_zero]
  field_simp

/-- Woodford (2003), eq. (B.7), p. 657, at the symmetric point: aggregate demand
`Y = C + ∫ m(i) di` with `m(i) = s_m y(i) = s_m Y` gives `C = (1 − s_m) Y`: final demand equals
value added ("final-goods demand (or real value added)", p. 658). -/
theorem final_demand_value_added {Y C sm : ℝ} (h : Y = C + sm * Y) : C = (1 - sm) * Y := by
  linarith

/-- Woodford (2003), eq. (B.9), p. 658: in the symmetric flexible-price steady state real
marginal cost is `µ⁻¹`, so by (B.8) `(1 − s_m) s̄^{VA} + s_m = µ⁻¹` iff
`s̄^{VA} = (1 − µ s_m)/(µ(1 − s_m))`. -/
theorem steady_state_B9 {μ sm v : ℝ} (hμ : μ ≠ 0) (hsm : sm ≠ 1) :
    (1 - sm) * v + sm = μ⁻¹ ↔ v = (1 - μ * sm) / (μ * (1 - sm)) := by
  have h1 : (1 : ℝ) - sm ≠ 0 := sub_ne_zero.mpr (Ne.symm hsm)
  constructor
  · intro h
    field_simp
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Woodford (2003), p. 658: "the existence of a symmetric steady state then requires that
`s_m < µ⁻¹`": for `µ > 0` and `s_m < 1`, the steady-state value-added marginal cost (B.9) is
positive if and only if `s_m < µ⁻¹`. -/
theorem steady_state_needs_sm_lt {μ sm : ℝ} (hμ : 0 < μ) (hsm : sm < 1) :
    0 < (1 - μ * sm) / (μ * (1 - sm)) ↔ sm < μ⁻¹ := by
  have hd : 0 < μ * (1 - sm) := mul_pos hμ (by linarith)
  rw [div_pos_iff_of_pos_right hd, sub_pos, inv_eq_one_div, lt_div_iff₀' hμ]

/-- Woodford (2003), p. 658: with `0 ≤ s_m < µ⁻¹` the factor `1 − µ s_m` multiplying the
marginal-cost elasticities lies in `(0, 1]` (in `(0, 1)` when `s_m > 0`), the source of "real
rigidity". -/
theorem factor_mem {μ sm : ℝ} (hμ : 0 < μ) (h0 : 0 ≤ sm) (h1 : sm < μ⁻¹) :
    0 < 1 - μ * sm ∧ 1 - μ * sm ≤ 1 ∧ (0 < sm → 1 - μ * sm < 1) := by
  have : μ * sm < 1 := by
    have := mul_lt_mul_of_pos_left h1 hμ
    rwa [mul_inv_cancel₀ hμ.ne'] at this
  refine ⟨by linarith, by nlinarith, fun h => by nlinarith⟩

/-- Woodford (2003), eq. (B.9), p. 658 ("Ȳ implicitly defined by"): if `g(Y) = s(Y, Y; 0)` is
continuous on `[a, b]` and the target `(1 − µ s_m)/(µ(1 − s_m))` lies between `g a` and `g b`,
a steady state `Ȳ ∈ [a, b]` exists; it is unique when `g` is strictly increasing. -/
theorem steady_state_exists {g : ℝ → ℝ} {a b target : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) (ha : g a ≤ target) (hb : target ≤ g b) :
    (∃ Y ∈ Set.Icc a b, g Y = target) ∧
      (StrictMonoOn g (Set.Icc a b) →
        ∀ Y₁ ∈ Set.Icc a b, ∀ Y₂ ∈ Set.Icc a b, g Y₁ = target → g Y₂ = target → Y₁ = Y₂) := by
  refine ⟨?_, fun hm Y₁ h₁ Y₂ h₂ e₁ e₂ => hm.injOn h₁ h₂ (e₁.trans e₂.symm)⟩
  obtain ⟨Y, hY, hYt⟩ := intermediate_value_Icc hab hg ⟨ha, hb⟩
  exact ⟨Y, hY, hYt⟩

/-- Woodford (2003), (1.43), p. 171: the denominator `1 + θ[ε_µ + (1 − µ s_m) s_y]` is positive
when `θ > 0`, `ε_µ ≥ 0`, `s_y ≥ 0` and `µ s_m ≤ 1`. -/
theorem den_pos {θ εμ μsm sy : ℝ} (hθ : 0 < θ) (hε : 0 ≤ εμ) (hsy : 0 ≤ sy) (hm : μsm ≤ 1) :
    0 < 1 + θ * (εμ + (1 - μsm) * sy) := by
  have : 0 ≤ (1 - μsm) * sy := mul_nonneg (by linarith) hsy
  positivity

/-! ### (B.6): Proposition 3.3 from the primitives -/

/-- Woodford (2003), (B.4), p. 656: `θ'(1)` in terms of `ψ'(1), ψ''(1), ψ'''(1)`:
`θ'(1) = −1 + ψ'(1)(ψ''(1) + ψ'''(1))/ψ''(1)²`. -/
noncomputable def thetaKDeriv (ψ1one ψ2one ψ3one : ℝ) : ℝ :=
  -1 + ψ1one * (ψ2one + ψ3one) / ψ2one ^ 2

/-- Woodford (2003), (B.4)–(B.5), pp. 656–657: if `ψ'` has strict derivative `ψ''(1)` at `1` and
`ψ''` has strict derivative `ψ'''(1)` there, with `ψ''(1) ≠ 0`, then `θ(x) = −ψ'(x)/(xψ''(x))`
has strict derivative `thetaKDeriv` at `1`. -/
theorem thetaK_hasStrictDerivAt {ψ1 ψ2 : ℝ → ℝ} {ψ3one : ℝ} (h1 : HasStrictDerivAt ψ1 (ψ2 1) 1)
    (h2 : HasStrictDerivAt ψ2 ψ3one 1) (hne : ψ2 1 ≠ 0) :
    HasStrictDerivAt (thetaK ψ1 ψ2) (thetaKDeriv (ψ1 1) (ψ2 1) ψ3one) 1 := by
  have hden : HasStrictDerivAt (fun x => x * ψ2 x) (1 * ψ2 1 + 1 * ψ3one) 1 :=
    (hasStrictDerivAt_id (1 : ℝ)).mul h2
  have := h1.neg.div hden (by simpa using hne)
  unfold thetaK thetaKDeriv
  convert this using 1
  simp only [Pi.neg_apply]
  field_simp
  ring

/-- Woodford (2003), (B.1), p. 656 (ψ of class C³): the strict derivatives used in (B.4)–(B.6),
`ψ' = deriv ψ` with derivative `ψ''(1)` and `ψ'' = deriv (deriv ψ)` with derivative `ψ'''(1)`,
follow from `ContDiff ℝ 3 ψ`. -/
theorem strictDerivs_of_contDiff {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 3 ψ) :
    HasStrictDerivAt (deriv ψ) (deriv (deriv ψ) 1) 1 ∧
      HasStrictDerivAt (deriv (deriv ψ)) (deriv (deriv (deriv ψ)) 1) 1 := by
  have h2 : ContDiff ℝ 2 (deriv ψ) := (contDiff_succ_iff_deriv.mp hψ).2.2
  have h1 : ContDiff ℝ 1 (deriv (deriv ψ)) := (contDiff_succ_iff_deriv.mp h2).2.2
  exact ⟨h2.contDiffAt.hasStrictDerivAt (by norm_num),
    h1.contDiffAt.hasStrictDerivAt (by norm_num)⟩

/-- **Proposition 3.3, complete proof** (Woodford (2003), (B.6), pp. 657–658; (1.43), p. 171).
Primitives: `ψ'` with strict derivative `ψ''(1)` at `1`, `ψ''` with strict derivative `ψ'''(1)`
(both follow from `ψ ∈ C³`, `strictDerivs_of_contDiff`), `ψ''(1) < 0`, and
`θ = θ(1) = −ψ'(1)/ψ''(1) > 1` (B.4); `θ'(1) = thetaKDeriv` is derived
(`thetaK_hasStrictDerivAt`), giving `ε_µ = −θ'(1)/(θ(θ − 1))` (`markup_elasticity`); the
steady-state markup `µ = θ/(θ − 1)` (B.5); the log marginal cost of value added `ℓ`, as a function
of the log deviations of own and aggregate gross output (equal to those of value added:
`value_added_log_deviation`, `aggregate_value_added_hasDerivAt`), strictly differentiable with
elasticities `s_y, s_Y`; materials share `s_m ≠ 1`; and the steady state (B.9). Then the Kimball
demand `d` exists (`d(1) = 1`), and with log demand `u ↦ log d(eᵘ)`, log markup `markupLog θ`
and gross-output log real marginal cost `ŝ = log(µ((1 − s_m) s̄^{VA} e^{ℓ} + s_m))` from (B.8),
the notional SRAS exists, is locally unique and has slope
`ζ = (1 − µ s_m)(s_y + s_Y)/(1 + θ[ε_µ + (1 − µ s_m) s_y])`, provided this denominator is nonzero
(positive under `den_pos`). The hypothesis `s_m < µ⁻¹` (`steady_state_needs_sm_lt`) is what makes
`s̄^{VA} > 0`; it is not needed for the derivative computation itself. -/
theorem prop_3_3_complete {ψ1 ψ2 : ℝ → ℝ} {ψ3one sm sy sY : ℝ} {ell : ℝ × ℝ → ℝ}
    {Lℓ : ℝ × ℝ →L[ℝ] ℝ} (hψ : HasStrictDerivAt ψ1 (ψ2 1) 1) (hψ2d : HasStrictDerivAt ψ2 ψ3one 1)
    (hψ2 : ψ2 1 < 0) (hθgt : 1 < thetaK ψ1 ψ2 1)
    (hsm : sm ≠ 1) (hℓ : HasStrictFDerivAt ell Lℓ 0) (hℓ0 : ell 0 = 0)
    (hL : ∀ q, Lℓ q = sy * q.1 + sY * q.2)
    (hden : 1 + thetaK ψ1 ψ2 1 * (-thetaKDeriv (ψ1 1) (ψ2 1) ψ3one /
      (thetaK ψ1 ψ2 1 * (thetaK ψ1 ψ2 1 - 1)) +
      (1 - thetaK ψ1 ψ2 1 / (thetaK ψ1 ψ2 1 - 1) * sm) * sy) ≠ 0) :
    ∃ d : ℝ → ℝ, d 1 = 1 ∧ (∀ᶠ r in 𝓝 1, ψ1 (d r) = ψ1 1 * r) ∧
      ∃ x : ℝ → ℝ, x 0 = 0 ∧
        (∀ᶠ y in 𝓝 0, StrategicComplementarity.sras (markupLog (thetaK ψ1 ψ2))
          (fun u => Real.log (d (Real.exp u)))
          (fun q => Real.log (thetaK ψ1 ψ2 1 / (thetaK ψ1 ψ2 1 - 1) * ((1 - sm) *
            ((1 - thetaK ψ1 ψ2 1 / (thetaK ψ1 ψ2 1 - 1) * sm) /
              (thetaK ψ1 ψ2 1 / (thetaK ψ1 ψ2 1 - 1) * (1 - sm)) *
              Real.exp (ell q)) + sm))) (y, x y) = 0) ∧
        HasStrictDerivAt x (StrategicComplementarity.zeta33 (thetaK ψ1 ψ2 1)
          (-thetaKDeriv (ψ1 1) (ψ2 1) ψ3one / (thetaK ψ1 ψ2 1 * (thetaK ψ1 ψ2 1 - 1)))
          (thetaK ψ1 ψ2 1 / (thetaK ψ1 ψ2 1 - 1) * sm) sy sY) 0 := by
  have hθ := thetaK_hasStrictDerivAt hψ hψ2d hψ2.ne
  obtain ⟨d, hd1, hdid, -, hdd, -⟩ := kimball_demand_exists hψ hψ2.ne
  have hθ1 : thetaK ψ1 ψ2 1 = -ψ1 1 / ψ2 1 := by simp [thetaK]
  have hdθ : HasStrictDerivAt d (-thetaK ψ1 ψ2 1) 1 := by
    rw [hθ1]; convert hdd using 1; ring
  obtain ⟨hlog0, hlog⟩ := kimball_log_demand hdθ hd1
  obtain ⟨hm0, hm⟩ := markup_elasticity hθ hθgt
  have hμ : thetaK ψ1 ψ2 1 / (thetaK ψ1 ψ2 1 - 1) ≠ 0 :=
    div_ne_zero (by linarith) (by linarith)
  obtain ⟨hs0, hs⟩ := StrategicComplementarity.intermediate_input_elasticities
    (μ := thetaK ψ1 ψ2 1 / (thetaK ψ1 ψ2 1 - 1)) hμ hsm hℓ hℓ0
  obtain ⟨x, hx0, hx, -, hxd⟩ := StrategicComplementarity.prop_3_3 (sy := sy) (sY := sY)
    (μsm := thetaK ψ1 ψ2 1 / (thetaK ψ1 ψ2 1 - 1) * sm) hm hlog hlog0 hm0 hs hs0
    (fun q => by simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hL]; ring) hden
  exact ⟨d, hd1, hdid, x, hx0, hx, hxd⟩

/-- **Proposition 3.3 from `ψ`** (Woodford (2003), (B.6)): the same conclusion for
`ψ ∈ C³` with `ψ''(1) < 0` and `θ(1) > 1`: every derivative input of `prop_3_3_complete` is
computed from `ψ` itself. -/
theorem prop_3_3_from_psi {ψ : ℝ → ℝ} {sm sy sY : ℝ} {ell : ℝ × ℝ → ℝ} {Lℓ : ℝ × ℝ →L[ℝ] ℝ}
    (hψ : ContDiff ℝ 3 ψ) (hψ2 : deriv (deriv ψ) 1 < 0)
    (hθgt : 1 < thetaK (deriv ψ) (deriv (deriv ψ)) 1)
    (hsm : sm ≠ 1) (hℓ : HasStrictFDerivAt ell Lℓ 0) (hℓ0 : ell 0 = 0)
    (hL : ∀ q, Lℓ q = sy * q.1 + sY * q.2)
    (hden : 1 + thetaK (deriv ψ) (deriv (deriv ψ)) 1 *
      (-thetaKDeriv (deriv ψ 1) (deriv (deriv ψ) 1) (deriv (deriv (deriv ψ)) 1) /
        (thetaK (deriv ψ) (deriv (deriv ψ)) 1 * (thetaK (deriv ψ) (deriv (deriv ψ)) 1 - 1)) +
      (1 - thetaK (deriv ψ) (deriv (deriv ψ)) 1 /
        (thetaK (deriv ψ) (deriv (deriv ψ)) 1 - 1) * sm) * sy) ≠ 0) :
    ∃ d : ℝ → ℝ, d 1 = 1 ∧ (∀ᶠ r in 𝓝 1, deriv ψ (d r) = deriv ψ 1 * r) ∧
      ∃ x : ℝ → ℝ, x 0 = 0 ∧
        HasStrictDerivAt x (StrategicComplementarity.zeta33
          (thetaK (deriv ψ) (deriv (deriv ψ)) 1)
          (-thetaKDeriv (deriv ψ 1) (deriv (deriv ψ) 1) (deriv (deriv (deriv ψ)) 1) /
            (thetaK (deriv ψ) (deriv (deriv ψ)) 1 *
              (thetaK (deriv ψ) (deriv (deriv ψ)) 1 - 1)))
          (thetaK (deriv ψ) (deriv (deriv ψ)) 1 /
            (thetaK (deriv ψ) (deriv (deriv ψ)) 1 - 1) * sm) sy sY) 0 := by
  obtain ⟨h1, h2⟩ := strictDerivs_of_contDiff hψ
  obtain ⟨d, hd1, hdid, x, hx0, -, hxd⟩ :=
    prop_3_3_complete h1 h2 hψ2 hθgt hsm hℓ hℓ0 hL hden
  exact ⟨d, hd1, hdid, x, hx0, hxd⟩

/-! ### (B.1)–(B.3) for a continuum of goods -/

/-- Woodford (2003), eqs. (B.1)–(B.3), p. 656, with a continuum of goods (a measure space of
goods `μ`, e.g. `[0, 1]` with Lebesgue measure): a positive bundle `c` satisfying the demand
curves (B.2) and the aggregator (B.1) `∫ ψ(c/C) = 1` minimises expenditure `∫ p c` among all
positive bundles with `∫ ψ(c'/C) ≥ 1`, for `ψ` concave and increasing at `1` (integrability of the
four integrands is assumed). -/
theorem kimball_demand_cost_min_continuum {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {ψ ψ1 : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) ψ) (hder : ∀ x, 0 < x → HasDerivAt ψ (ψ1 x) x)
    (hψ1 : 0 < ψ1 1) {C P : ℝ} (hC : 0 < C) (hP : 0 < P) {p c c' : α → ℝ}
    (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (hB2 : ∀ i, ψ1 (c i / C) = ψ1 1 * (p i / P)) (hB3 : ∫ i, ψ (c i / C) ∂μ = 1)
    (hfeas : 1 ≤ ∫ i, ψ (c' i / C) ∂μ)
    (i1 : MeasureTheory.Integrable (fun i => ψ (c i / C)) μ)
    (i2 : MeasureTheory.Integrable (fun i => ψ (c' i / C)) μ)
    (i3 : MeasureTheory.Integrable (fun i => p i * c i) μ)
    (i4 : MeasureTheory.Integrable (fun i => p i * c' i) μ) :
    ∫ i, p i * c i ∂μ ≤ ∫ i, p i * c' i ∂μ := by
  set k := ψ1 1 / (P * C)
  have hk : 0 < k := div_pos hψ1 (mul_pos hP hC)
  have key : (fun i => ψ (c' i / C) - ψ (c i / C)) ≤
      fun i => k * (p i * c' i - p i * c i) := by
    intro i
    have ht := Predetermined.concave_tangent_le hconc (Set.mem_Ioi.mpr (div_pos (hc i) hC))
      (Set.mem_Ioi.mpr (div_pos (hc' i) hC)) (hder _ (div_pos (hc i) hC))
    rw [hB2 i] at ht
    have e : k * (p i * c' i - p i * c i) = ψ1 1 * (p i / P) * (c' i / C - c i / C) := by
      simp only [k]; field_simp
    simp only
    rw [e]
    linarith
  have hint := MeasureTheory.integral_mono (i2.sub i1) ((i4.sub i3).const_mul k) key
  simp only [Pi.sub_apply] at hint
  rw [MeasureTheory.integral_sub i2 i1, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub i4 i3] at hint
  have h2 : 0 ≤ ∫ i, p i * c' i ∂μ - ∫ i, p i * c i ∂μ := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg hk hneg
    linarith
  linarith

/-- Woodford (2003), p. 657 (B.2's measure-zero deviating industry), continuum of goods: if all
goods except a null set charge `P` (`p = P` almost everywhere), the bundle satisfying (B.2) is
`c = C` almost everywhere, the aggregator (B.1) holds (`∫ ψ(c/C) = ψ(1) = 1`), and its cost is
`∫ p c = P C`: the unit cost of the materials (or consumption) aggregate is exactly `P`. -/
theorem kimball_unit_cost_ae {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {ψ ψ1 : ℝ → ℝ} (hanti : StrictAntiOn ψ1 (Set.Ioi 0))
    (hψ1one : ψ 1 = 1) {C P : ℝ} (hC : 0 < C) (hP : 0 < P) {p c : α → ℝ}
    (hc : ∀ i, 0 < c i) (hB2 : ∀ i, ψ1 (c i / C) = ψ1 1 * (p i / P))
    (hp : p =ᵐ[μ] fun _ => P) :
    (c =ᵐ[μ] fun _ => C) ∧ ∫ i, ψ (c i / C) ∂μ = 1 ∧ ∫ i, p i * c i ∂μ = P * C := by
  have hcC : c =ᵐ[μ] fun _ => C := by
    filter_upwards [hp] with i hi
    have h := hB2 i
    rw [hi, div_self hP.ne', mul_one] at h
    have := hanti.injOn (div_pos (hc i) hC) (show (0 : ℝ) < 1 from one_pos) h
    field_simp at this
    exact this
  refine ⟨hcC, ?_, ?_⟩
  · have : (fun i => ψ (c i / C)) =ᵐ[μ] fun _ => (1 : ℝ) := by
      filter_upwards [hcC] with i hi
      rw [hi, div_self hC.ne', hψ1one]
    rw [MeasureTheory.integral_congr_ae this]
    simp
  · have : (fun i => p i * c i) =ᵐ[μ] fun _ => P * C := by
      filter_upwards [hcC, hp] with i hi hj
      rw [hi, hj]
    rw [MeasureTheory.integral_congr_ae this]
    simp

end Woodford.NominalRigidities.Kimball
