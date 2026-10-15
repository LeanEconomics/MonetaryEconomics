/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.DixitStiglitz
import NominalRigidities.MarginalCost
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Flexible prices and the natural rate of output

Woodford (2003), *Interest and Prices*, Chapter 3, §1.1, pp. 150–154: optimal pricing under
flexible prices, the natural rate of output (1.12)–(1.14), the general profit function (1.17)–
(1.18), Assumption 3.1 and Proposition 3.1 (eqs. (1.19)–(1.21)); together with the regularity of
the natural rate needed to make (1.15) an exact derivative.

## Main results

* Assumption 3.1: `HomogeneousOne`, `SinglePeakedAt`, `Assumption31`; `euler` (Euler's theorem
  `pΠ₁ + qΠ₂ + PΠ₃ = Π`), `deriv_homogeneous_zero` (`Π₁` homogeneous of degree zero),
  `singlePeaked_isOptimal_iff` (unique optimal price), `isOptimal_deriv_zero` (necessity of
  (1.19)), `foc_iff_optimal` (sufficiency under the strengthened hypothesis).
* Proposition 3.1: `flexEqm_iff_one` (neutrality: equilibrium output does not depend on `P`),
  `flexEqm_foc` ((1.21) is necessary), `prop_3_1_characterisation`, and `prop_3_1` (existence
  and uniqueness of `Yⁿ` under the strengthened hypotheses: `Π₁` vanishes only at the peak and
  `Y ↦ Π₁(1, 1, 1; Y)` is continuous, strictly decreasing, and changes sign).
* Survey error E2 CONFIRMED, with Lean counterexamples satisfying Assumption 3.1:
  `twoRoots_counterexample` (`Π₁` has a spurious root, so (1.19) has two solutions and (1.21)
  holds for every `Y` although no equilibrium exists), `noNaturalRate_counterexample` (no
  `Yⁿ`), `continuumNaturalRate_counterexample` (every `Y` is an equilibrium).
* The baseline model: `hasDerivAt_dem`, `hasDerivAt_profit`, `lerner_foc_iff` (the Lerner markup
  `μ = θ/(θ − 1)`), `lerner_singlePeaked` and `baseline_singlePeaked` (the example satisfies
  single-peakedness, p. 154), `baselineProfit_homogeneous` ((1.18) is homogeneous),
  `baseline_markup` ((1.13)), `baseline_flexEqm_iff` ((1.21) is (1.14) in the baseline).
* (1.13)–(1.14): `relative_supply_existsUnique` (unique solution of the relative-supply
  equation; only `s` nondecreasing is needed), `symmetric_flexible_eqm` (all suppliers produce
  `Y`, and `μ s(Y, Y) = 1`), `symmetric_flexible_eqm_of`, `naturalRate_existsUnique_iff`
  (existence ⟺ a boundary condition), `diag_strictMonoOn`, `isoelastic_naturalRate`.
* The book's claim that (1.14) "must have a unique solution" is FALSE as to existence:
  `noNaturalRate_baseline` and `baseline_noFlexEqm` (primitives satisfying every stated
  hypothesis — `s` increasing in both arguments — with `s(Y, Y) < μ⁻¹` for all `Y`).
* Natural-rate regularity: `root_continuousAt`, `implicit_hasFDerivAt` (an implicit-function
  step proved here), `logRmcGap_diag_strictMono`, and `eq_1_15_unconditional`: (1.15) holds as
  an exact Fréchet derivative with `Dn` the (proved) derivative of the log natural rate.
-/

namespace Woodford.NominalRigidities.FlexiblePrices

open Filter Topology

/-! ### Assumption 3.1 -/

/-- Woodford (2003), Assumption 3.1, p. 153: the profit function `Π(p, p^I, P; Y, ξ̃)` is
homogeneous of degree one in its first three arguments (positive prices). -/
def HomogeneousOne {X : Type*} (prof : ℝ → ℝ → ℝ → ℝ → X → ℝ) : Prop :=
  ∀ (l p q P Y : ℝ) (ξ : X), 0 < l → 0 < p → 0 < q → 0 < P →
    prof (l * p) (l * q) (l * P) Y ξ = l * prof p q P Y ξ

/-- Woodford (2003), Assumption 3.1, p. 153: `g` is single-peaked on `(0, ∞)` with its maximum
at the positive price `m`: strictly increasing on `(0, m]`, strictly decreasing on `[m, ∞)`. -/
def SinglePeakedAt (g : ℝ → ℝ) (m : ℝ) : Prop :=
  0 < m ∧ StrictMonoOn g (Set.Ioc 0 m) ∧ StrictAntiOn g (Set.Ici m)

/-- Woodford (2003), Assumption 3.1, p. 153: homogeneity of degree one plus single-peakedness in
the own price, with a maximum at a positive price, for all values of the other arguments. -/
def Assumption31 {X : Type*} (prof : ℝ → ℝ → ℝ → ℝ → X → ℝ) : Prop :=
  HomogeneousOne prof ∧
    ∀ (q P Y : ℝ) (ξ : X), 0 < q → 0 < P → ∃ m, SinglePeakedAt (fun p => prof p q P Y ξ) m

/-- Woodford (2003), p. 151: `p` is an optimal (profit-maximising) positive price for `g`. -/
def IsOptimal (g : ℝ → ℝ) (p : ℝ) : Prop :=
  0 < p ∧ ∀ x, 0 < x → g x ≤ g p

/-- Woodford (2003), p. 154: a flexible-price equilibrium with price level `P` and output `Y`:
the common price `P` (charged also by the rest of the industry) is optimal for each supplier. -/
def FlexEqm {X : Type*} (prof : ℝ → ℝ → ℝ → ℝ → X → ℝ) (P Y : ℝ) (ξ : X) : Prop :=
  IsOptimal (fun p => prof p P P Y ξ) P

/-- Woodford (2003), Assumption 3.1, p. 153: at a single peak `m`, every other positive price
gives strictly lower profit. -/
theorem singlePeaked_lt {g : ℝ → ℝ} {m : ℝ} (h : SinglePeakedAt g m) {p : ℝ} (hp : 0 < p)
    (hpm : p ≠ m) : g p < g m := by
  obtain ⟨hm, hinc, hdec⟩ := h
  rcases lt_or_gt_of_ne hpm with hlt | hgt
  · exact hinc ⟨hp, hlt.le⟩ ⟨hm, le_rfl⟩ hlt
  · exact hdec (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hgt.le) hgt

/-- Woodford (2003), p. 154: under single-peakedness the optimal price exists and is unique:
`p` is optimal iff `p` is the peak. -/
theorem singlePeaked_isOptimal_iff {g : ℝ → ℝ} {m : ℝ} (h : SinglePeakedAt g m) {p : ℝ} :
    IsOptimal g p ↔ p = m := by
  constructor
  · rintro ⟨hp, hopt⟩
    by_contra hpm
    exact absurd (hopt m h.1) (not_le.2 (singlePeaked_lt h hp hpm))
  · rintro rfl
    refine ⟨h.1, fun x hx => ?_⟩
    rcases eq_or_ne x p with rfl | hxp
    · exact le_rfl
    · exact (singlePeaked_lt h hx hxp).le

/-- Woodford (2003), eq. (1.19), p. 154 (necessity of the first-order condition): if profit is
differentiable at an optimal price, its derivative there vanishes. -/
theorem isOptimal_deriv_zero {g : ℝ → ℝ} {p d : ℝ} (h : IsOptimal g p) (hd : HasDerivAt g d p) :
    d = 0 := by
  refine IsLocalMax.hasDerivAt_eq_zero ?_ hd
  filter_upwards [Ioi_mem_nhds h.1] with x hx using h.2 x hx

/-- Woodford (2003), eq. (1.19), p. 154 (**corrected**): the first-order condition `Π₁ = 0`
characterises the optimum when `Π₁` does not vanish away from the peak — the strengthened
hypothesis that Assumption 3.1's single-peakedness alone does not supply (see
`twoRoots_counterexample`). -/
theorem foc_iff_optimal {g g' : ℝ → ℝ} {m : ℝ} (h : SinglePeakedAt g m)
    (hnz : ∀ x, 0 < x → x ≠ m → g' x ≠ 0) {p : ℝ} (hp : 0 < p) (hd : HasDerivAt g (g' p) p) :
    g' p = 0 ↔ IsOptimal g p := by
  rw [singlePeaked_isOptimal_iff h]
  constructor
  · intro h0
    by_contra hpm
    exact hnz p hp hpm h0
  · rintro rfl
    exact isOptimal_deriv_zero ((singlePeaked_isOptimal_iff h).2 rfl) hd

/-- Woodford (2003), p. 154 ("`Π₁` is homogeneous of degree zero"): if `Π` is homogeneous of
degree one and `Π₁(p, q, P) = d`, then `Π₁(lp, lq, lP) = d` for every `l > 0`. -/
theorem deriv_homogeneous_zero {X : Type*} {prof : ℝ → ℝ → ℝ → ℝ → X → ℝ}
    (hhom : HomogeneousOne prof) {l p q P Y d : ℝ} {ξ : X} (hl : 0 < l) (hp : 0 < p)
    (hq : 0 < q) (hP : 0 < P) (hd : HasDerivAt (fun x => prof x q P Y ξ) d p) :
    HasDerivAt (fun x => prof x (l * q) (l * P) Y ξ) d (l * p) := by
  have hdiv : HasDerivAt (fun x : ℝ => x / l) (1 / l) (l * p) := (hasDerivAt_id _).div_const l
  have hcomp := (hd.comp_of_eq (l * p) hdiv (by field_simp)).const_mul l
  refine (HasDerivAt.congr_deriv hcomp (by field_simp)).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds (mul_pos hl hp)] with x hx
  have hx' : 0 < x / l := div_pos hx hl
  have := hhom l (x / l) q P Y ξ hl hx' hq hP
  rw [mul_div_cancel₀ x hl.ne'] at this
  simpa only [Function.comp_apply] using this

/-- Woodford (2003), Assumption 3.1, p. 153 (**Euler's theorem**): if `Π` is homogeneous of
degree one and differentiable at `(p, q, P)` with derivative `D`, then
`p Π₁ + q Π₂ + P Π₃ = Π`. -/
theorem euler {X : Type*} {prof : ℝ → ℝ → ℝ → ℝ → X → ℝ} (hhom : HomogeneousOne prof)
    {p q P Y : ℝ} {ξ : X} (hp : 0 < p) (hq : 0 < q) (hP : 0 < P) {D : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun v : ℝ × ℝ × ℝ => prof v.1 v.2.1 v.2.2 Y ξ) D (p, q, P)) :
    p * D (1, 0, 0) + q * D (0, 1, 0) + P * D (0, 0, 1) = prof p q P Y ξ := by
  have hpath : HasDerivAt (fun l : ℝ => (l * p, l * q, l * P)) (p, q, P) 1 := by
    have h1 := (hasDerivAt_id (1 : ℝ)).mul_const p
    have h2 := (hasDerivAt_id (1 : ℝ)).mul_const q
    have h3 := (hasDerivAt_id (1 : ℝ)).mul_const P
    simp only [one_mul] at h1 h2 h3
    exact h1.prodMk (h2.prodMk h3)
  have hcomp := hD.comp_hasDerivAt_of_eq 1 hpath (by simp)
  have hline : HasDerivAt (fun l : ℝ => l * prof p q P Y ξ) (prof p q P Y ξ) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (prof p q P Y ξ)
  have heq := hcomp.unique (hline.congr_of_eventuallyEq (by
    filter_upwards [Ioi_mem_nhds one_pos] with l hl
    simp only [Function.comp_apply]
    exact hhom l p q P Y ξ hl hp hq hP))
  have hsplit : ((p, q, P) : ℝ × ℝ × ℝ) = p • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) +
      q • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) + P • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    simp
  rw [hsplit, map_add, map_add, map_smul, map_smul, map_smul] at heq
  simpa only [smul_eq_mul] using heq

/-! ### Proposition 3.1 -/

/-- Woodford (2003), Proposition 3.1, p. 154 (**neutrality**): by homogeneity, a flexible-price
equilibrium with output `Y` exists at price level `P` iff it exists at `P = 1`; the equilibrium
level of output is independent of the price level, hence of monetary policy. -/
theorem flexEqm_iff_one {X : Type*} {prof : ℝ → ℝ → ℝ → ℝ → X → ℝ} (hhom : HomogeneousOne prof)
    {P Y : ℝ} {ξ : X} (hP : 0 < P) : FlexEqm prof P Y ξ ↔ FlexEqm prof 1 Y ξ := by
  have key : ∀ x, 0 < x → prof x P P Y ξ = P * prof (x / P) 1 1 Y ξ := by
    intro x hx
    have := hhom P (x / P) 1 1 Y ξ hP (div_pos hx hP) one_pos one_pos
    rwa [mul_div_cancel₀ x hP.ne', mul_one] at this
  constructor
  · rintro ⟨-, hopt⟩
    refine ⟨one_pos, fun x hx => ?_⟩
    have h := hopt (P * x) (mul_pos hP hx)
    dsimp only at h ⊢
    rw [key _ (mul_pos hP hx), key _ hP, mul_div_cancel_left₀ x hP.ne', div_self hP.ne'] at h
    exact le_of_mul_le_mul_left h hP
  · rintro ⟨-, hopt⟩
    refine ⟨hP, fun x hx => ?_⟩
    dsimp only at hopt ⊢
    rw [key _ hx, key _ hP, div_self hP.ne']
    exact mul_le_mul_of_nonneg_left (hopt _ (div_pos hx hP)) hP.le

/-- Woodford (2003), eq. (1.21), p. 154 (**necessity**): in a flexible-price equilibrium the
natural-rate condition `Π₁(1, 1, 1; Y, ξ̃) = 0` holds (when `Π` is differentiable there). -/
theorem flexEqm_foc {X : Type*} {prof : ℝ → ℝ → ℝ → ℝ → X → ℝ} (hhom : HomogeneousOne prof)
    {P Y d : ℝ} {ξ : X} (hP : 0 < P) (h : FlexEqm prof P Y ξ)
    (hd : HasDerivAt (fun p => prof p 1 1 Y ξ) d 1) : d = 0 :=
  isOptimal_deriv_zero ((flexEqm_iff_one hhom hP).1 h) hd

/-- Woodford (2003), Proposition 3.1 and eq. (1.21), p. 154 (**characterisation, corrected**):
under Assumption 3.1, output `Y` is a flexible-price equilibrium at any price level `P > 0` iff
the peak of `p ↦ Π(p, 1, 1; Y, ξ̃)` is at `p = 1`. If moreover `Π₁(·, 1, 1; Y, ξ̃)` vanishes only
at the peak, this is equivalent to (1.21), `Π₁(1, 1, 1; Y, ξ̃) = 0`. -/
theorem prop_3_1_characterisation {X : Type*} {prof : ℝ → ℝ → ℝ → ℝ → X → ℝ}
    (hA : Assumption31 prof) {P Y : ℝ} {ξ : X} (hP : 0 < P) {m : ℝ}
    (hm : SinglePeakedAt (fun p => prof p 1 1 Y ξ) m) :
    (FlexEqm prof P Y ξ ↔ m = 1) ∧
      ∀ g' : ℝ → ℝ, (∀ x, 0 < x → x ≠ m → g' x ≠ 0) →
        HasDerivAt (fun p => prof p 1 1 Y ξ) (g' 1) 1 → (FlexEqm prof P Y ξ ↔ g' 1 = 0) := by
  have h1 : FlexEqm prof P Y ξ ↔ m = 1 := by
    rw [flexEqm_iff_one hA.1 hP, FlexEqm, singlePeaked_isOptimal_iff hm, eq_comm]
  refine ⟨h1, fun g' hnz hd => ?_⟩
  rw [flexEqm_iff_one hA.1 hP, FlexEqm, foc_iff_optimal hm hnz one_pos hd]

/-- Woodford (2003), Proposition 3.1, p. 154 (**existence and uniqueness of the natural rate,
under strengthened hypotheses**): suppose (Assumption 3.1 and) that for each `Y > 0` the profit
`p ↦ Π(p, 1, 1; Y, ξ̃)` is single-peaked with derivative `Π₁` vanishing only at the peak, and the
boundary/monotonicity conditions hold: `F(Y) = Π₁(1, 1, 1; Y, ξ̃)` is continuous and strictly
decreasing on `(0, ∞)`, positive somewhere and negative somewhere. Then there is a unique
`Yⁿ > 0` such that, at EVERY price level `P > 0`, `Y` is a flexible-price equilibrium output iff
`Y = Yⁿ`; and `Yⁿ` solves (1.21). -/
theorem prop_3_1 {X : Type*} {prof : ℝ → ℝ → ℝ → ℝ → X → ℝ} (hA : Assumption31 prof) {ξ : X}
    (g' : ℝ → ℝ → ℝ)
    (hpeak : ∀ Y, 0 < Y → ∃ m, SinglePeakedAt (fun p => prof p 1 1 Y ξ) m ∧
      ∀ x, 0 < x → x ≠ m → g' Y x ≠ 0)
    (hd : ∀ Y, 0 < Y → HasDerivAt (fun p => prof p 1 1 Y ξ) (g' Y 1) 1)
    (hcont : ContinuousOn (fun Y => g' Y 1) (Set.Ioi 0))
    (hanti : StrictAntiOn (fun Y => g' Y 1) (Set.Ioi 0))
    {Y₁ Y₂ : ℝ} (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (h₁ : 0 < g' Y₁ 1) (h₂ : g' Y₂ 1 < 0) :
    ∃ Yn, 0 < Yn ∧ g' Yn 1 = 0 ∧ ∀ P Y, 0 < P → 0 < Y → (FlexEqm prof P Y ξ ↔ Y = Yn) := by
  have hle : Y₁ ≤ Y₂ := by
    by_contra hlt
    push Not at hlt
    have := hanti hY₂ hY₁ hlt
    linarith
  obtain ⟨Yn, hYn, hYn0⟩ := intermediate_value_Icc' hle
    (hcont.mono fun y hy => lt_of_lt_of_le hY₁ hy.1) ⟨h₂.le, h₁.le⟩
  have hYnpos : 0 < Yn := lt_of_lt_of_le hY₁ hYn.1
  have hchar : ∀ P Y, 0 < P → 0 < Y → (FlexEqm prof P Y ξ ↔ g' Y 1 = 0) := by
    intro P Y hP hY
    obtain ⟨m, hm, hnz⟩ := hpeak Y hY
    exact (prop_3_1_characterisation hA hP hm).2 (g' Y) hnz (hd Y hY)
  refine ⟨Yn, hYnpos, hYn0, fun P Y hP hY => ?_⟩
  rw [hchar P Y hP hY]
  constructor
  · intro h0
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hanti hY hYnpos hlt
      simp only at this
      linarith
    · have := hanti hYnpos hY hgt
      simp only at this
      linarith
  · rintro rfl
    exact hYn0

/-! ### Counterexamples to the printed Assumption 3.1 / Proposition 3.1 -/

/-- Woodford (2003), p. 154: the quartic `g(x) = −x⁴/4 + 4x³/3 − 5x²/2 + 2x`, whose derivative
is `(x − 1)²(2 − x)`: a stationary inflection at `1`, a single peak at `2`. -/
noncomputable def quartic (x : ℝ) : ℝ := -1 / 4 * x ^ 4 + 4 / 3 * x ^ 3 + (-5 / 2 * x ^ 2 + 2 * x)

/-- Woodford (2003), p. 154: `quartic' x = (x − 1)²(2 − x)`. -/
theorem hasDerivAt_quartic (x : ℝ) : HasDerivAt quartic ((x - 1) ^ 2 * (2 - x)) x := by
  have h4 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * x ^ 3) x := by
    simpa using hasDerivAt_pow 4 x
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h := ((h4.const_mul (-1 / 4)).add (h3.const_mul (4 / 3))).add
    ((h2.const_mul (-5 / 2)).add ((hasDerivAt_id x).const_mul 2))
  exact HasDerivAt.congr_deriv h (by ring)

/-- Woodford (2003), p. 154: the quartic is single-peaked with peak `2`. -/
theorem quartic_singlePeaked : SinglePeakedAt quartic 2 := by
  have hcont : Continuous quartic := by unfold quartic; fun_prop
  have hderiv : ∀ x, deriv quartic x = (x - 1) ^ 2 * (2 - x) := fun x =>
    (hasDerivAt_quartic x).deriv
  have hA : StrictMonoOn quartic (Set.Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [hderiv]
    have : 0 < (x - 1) ^ 2 := by nlinarith [hx.2]
    nlinarith [hx.2]
  have hB : StrictMonoOn quartic (Set.Icc 1 2) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 1 2) hcont.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [hderiv]
    have : 0 < (x - 1) ^ 2 := by nlinarith [hx.1]
    nlinarith [hx.2]
  refine ⟨two_pos, fun a ha b hb hab => ?_, ?_⟩
  · rcases le_or_gt b 1 with hb1 | hb1
    · exact hA ⟨ha.1.le, hab.le.trans hb1⟩ ⟨ha.1.le.trans hab.le, hb1⟩ hab
    · rcases le_or_gt 1 a with ha1 | ha1
      · exact hB ⟨ha1, hab.le.trans hb.2⟩ ⟨hb1.le, hb.2⟩ hab
      · exact (hA ⟨ha.1.le, ha1.le⟩ ⟨zero_le_one, le_rfl⟩ ha1).trans
          (hB ⟨le_rfl, one_le_two⟩ ⟨hb1.le, hb.2⟩ hb1)
  · refine strictAntiOn_of_deriv_neg (convex_Ici 2) hcont.continuousOn fun x hx => ?_
    rw [interior_Ici] at hx
    rw [hderiv]
    have hx2 : 2 < x := hx
    have : 0 < (x - 1) ^ 2 := by nlinarith
    nlinarith

/-- Woodford (2003), p. 154: a profit function `Π(p, q, P; Y) = P g(p/P)` built from a function
`g` of the relative price. -/
noncomputable def relProfit (g : ℝ → ℝ) (p _q P _Y : ℝ) (_ξ : Unit) : ℝ := P * g (p / P)

/-- Woodford (2003), Assumption 3.1, p. 153: `P g(p/P)` is homogeneous of degree one. -/
theorem relProfit_homogeneous (g : ℝ → ℝ) : HomogeneousOne (relProfit g) := by
  intro l p q P Y ξ hl _ _ hP
  simp only [relProfit]
  rw [mul_div_mul_left p P hl.ne']
  ring

/-- Woodford (2003), Assumption 3.1, p. 153: if `g` is single-peaked at `m`, then
`p ↦ P g(p/P)` is single-peaked at `m P`. -/
theorem relProfit_singlePeaked {g : ℝ → ℝ} {m : ℝ} (hg : SinglePeakedAt g m) {q P Y : ℝ}
    (hP : 0 < P) : SinglePeakedAt (fun p => relProfit g p q P Y ()) (m * P) := by
  obtain ⟨hm, hinc, hdec⟩ := hg
  refine ⟨mul_pos hm hP, fun a ha b hb hab => ?_, fun a ha b hb hab => ?_⟩
  · have hab' : a / P < b / P := div_lt_div_of_pos_right hab hP
    have ha' : a / P ∈ Set.Ioc 0 m :=
      ⟨div_pos ha.1 hP, (div_le_iff₀ hP).2 ha.2⟩
    have hb' : b / P ∈ Set.Ioc 0 m :=
      ⟨div_pos hb.1 hP, (div_le_iff₀ hP).2 hb.2⟩
    exact mul_lt_mul_of_pos_left (hinc ha' hb' hab') hP
  · have hab' : a / P < b / P := div_lt_div_of_pos_right hab hP
    have ha' : a / P ∈ Set.Ici m := (le_div_iff₀ hP).2 ha
    have hb' : b / P ∈ Set.Ici m := (le_div_iff₀ hP).2 hb
    exact mul_lt_mul_of_pos_left (hdec ha' hb' hab') hP

/-- Woodford (2003), Assumption 3.1, eqs. (1.19)–(1.21), p. 154 (**counterexample: the
first-order condition has a spurious root**). `Π(p, q, P; Y) = P g(p/P)` with `g = quartic`
satisfies Assumption 3.1 (homogeneous, single-peaked with maximum at `p = 2P > 0`), yet
`Π₁(1, 1, 1; Y) = 0` for EVERY `Y` while no `Y` is a flexible-price equilibrium: single-peakedness
does not make the root of `Π₁` unique, and (1.21) does not characterise equilibrium. -/
theorem twoRoots_counterexample :
    Assumption31 (relProfit quartic) ∧
      (∀ Y : ℝ, HasDerivAt (fun p => relProfit quartic p 1 1 Y ()) 0 1) ∧
      (∀ P : ℝ, 0 < P → HasDerivAt (fun p => relProfit quartic p P P 0 ()) 0 P ∧
        HasDerivAt (fun p => relProfit quartic p P P 0 ()) 0 (2 * P)) ∧
      ∀ P Y : ℝ, 0 < P → ¬ FlexEqm (relProfit quartic) P Y () := by
  have hA : Assumption31 (relProfit quartic) :=
    ⟨relProfit_homogeneous quartic, fun q P Y ξ _ hP =>
      ⟨2 * P, by cases ξ; exact relProfit_singlePeaked quartic_singlePeaked hP⟩⟩
  have hderivP : ∀ P x : ℝ, 0 < P → HasDerivAt (fun p => relProfit quartic p P P 0 ())
      ((x / P - 1) ^ 2 * (2 - x / P)) x := by
    intro P x hP
    have h := ((hasDerivAt_quartic (x / P)).comp x ((hasDerivAt_id x).div_const P)).const_mul P
    refine HasDerivAt.congr_deriv h ?_
    field_simp
  refine ⟨hA, fun Y => ?_, fun P hP => ⟨?_, ?_⟩, fun P Y hP h => ?_⟩
  · have h := hderivP 1 1 one_pos
    simpa [relProfit] using h
  · have h := hderivP P P hP
    rwa [div_self hP.ne', sub_self, sq, zero_mul, zero_mul] at h
  · have h := hderivP P (2 * P) hP
    rwa [mul_div_assoc, div_self hP.ne', mul_one, sub_self, mul_zero] at h
  · have hpk := relProfit_singlePeaked (q := P) (Y := Y) quartic_singlePeaked hP
    have := (singlePeaked_isOptimal_iff hpk).1 h
    linarith

/-- Woodford (2003), p. 154: `h(x) = 4x − x²`, single-peaked at `2`. -/
theorem quad4_singlePeaked : SinglePeakedAt (fun x : ℝ => 4 * x - x ^ 2) 2 := by
  refine ⟨two_pos, fun a ha b hb hab => ?_, fun a ha b hb hab => ?_⟩
  · simp only
    nlinarith [ha.1, hb.2]
  · simp only
    have : (2 : ℝ) ≤ a := ha
    nlinarith

/-- Woodford (2003), p. 154: `h(x) = 2x − x²`, single-peaked at `1`. -/
theorem quad2_singlePeaked : SinglePeakedAt (fun x : ℝ => 2 * x - x ^ 2) 1 := by
  refine ⟨one_pos, fun a ha b hb hab => ?_, fun a ha b hb hab => ?_⟩
  · simp only
    nlinarith [ha.1, hb.2]
  · simp only
    have : (1 : ℝ) ≤ a := ha
    nlinarith

/-- Woodford (2003), Proposition 3.1, p. 154 (**counterexample: no natural rate**).
`Π(p, q, P; Y) = P h(p/P)`, `h(x) = 4x − x²`, satisfies Assumption 3.1 (peak at `2P > 0`), but
`Π₁(1, 1, 1; Y) = 2 ≠ 0` for every `Y` and no output level is a flexible-price equilibrium. -/
theorem noNaturalRate_counterexample :
    Assumption31 (relProfit fun x => 4 * x - x ^ 2) ∧
      (∀ Y : ℝ, HasDerivAt (fun p => relProfit (fun x => 4 * x - x ^ 2) p 1 1 Y ()) 2 1) ∧
      ∀ P Y : ℝ, 0 < P → ¬ FlexEqm (relProfit fun x => 4 * x - x ^ 2) P Y () := by
  refine ⟨⟨relProfit_homogeneous _, fun q P Y ξ _ hP =>
    ⟨2 * P, by cases ξ; exact relProfit_singlePeaked quad4_singlePeaked hP⟩⟩,
    fun Y => ?_, fun P Y hP h => ?_⟩
  · have h := ((hasDerivAt_id (1 : ℝ)).const_mul 4).sub ((hasDerivAt_id (1 : ℝ)).pow 2)
    simp only [relProfit, div_one, one_mul]
    refine HasDerivAt.congr_deriv h ?_
    norm_num
  · have hpk := relProfit_singlePeaked (q := P) (Y := Y) quad4_singlePeaked hP
    have := (singlePeaked_isOptimal_iff hpk).1 h
    linarith

/-- Woodford (2003), Proposition 3.1, p. 154 (**counterexample: a continuum of natural rates**).
`Π(p, q, P; Y) = P h(p/P)`, `h(x) = 2x − x²`, satisfies Assumption 3.1 and EVERY output level is
a flexible-price equilibrium: (1.21) does not pin down `Yⁿ`. -/
theorem continuumNaturalRate_counterexample :
    Assumption31 (relProfit fun x => 2 * x - x ^ 2) ∧
      ∀ P Y : ℝ, 0 < P → FlexEqm (relProfit fun x => 2 * x - x ^ 2) P Y () := by
  refine ⟨⟨relProfit_homogeneous _, fun q P Y ξ _ hP =>
    ⟨1 * P, by cases ξ; exact relProfit_singlePeaked quad2_singlePeaked hP⟩⟩,
    fun P Y hP => ?_⟩
  have hpk := relProfit_singlePeaked (q := P) (Y := Y) quad2_singlePeaked hP
  rw [one_mul] at hpk
  exact (singlePeaked_isOptimal_iff hpk).2 rfl

/-! ### The baseline model: demand (1.12), the Lerner markup, and single-peakedness (p. 154) -/

/-- Woodford (2003), eq. (1.12), p. 151: the demand curve `y(p) = Y (p/P)^{−θ}`. -/
noncomputable def dem (Y P θ p : ℝ) : ℝ := Y * (p / P) ^ (-θ)

/-- Woodford (2003), eq. (1.12), p. 151: demand is positive. -/
theorem dem_pos {Y P θ p : ℝ} (hY : 0 < Y) (hP : 0 < P) (hp : 0 < p) : 0 < dem Y P θ p :=
  mul_pos hY (Real.rpow_pos_of_pos (div_pos hp hP) _)

/-- Woodford (2003), eq. (1.12), p. 151: `y'(p) = −θ y(p)/p` (constant elasticity `θ`). -/
theorem hasDerivAt_dem {Y P θ p : ℝ} (hP : 0 < P) (hp : 0 < p) :
    HasDerivAt (dem Y P θ) (-θ * dem Y P θ p / p) p := by
  have hb : 0 < p / P := div_pos hp hP
  have h := (((hasDerivAt_id p).div_const P).rpow_const (p := -θ)
    (Or.inl hb.ne')).const_mul Y
  refine HasDerivAt.congr_deriv h ?_
  simp only [id]
  rw [Real.rpow_sub_one hb.ne', dem]
  field_simp

/-- Woodford (2003), eq. (1.12), p. 151: demand is strictly decreasing in the own price. -/
theorem dem_strictAntiOn {Y P θ : ℝ} (hY : 0 < Y) (hP : 0 < P) (hθ : 0 < θ) :
    StrictAntiOn (dem Y P θ) (Set.Ioi 0) := by
  intro a ha b _ hab
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg (div_pos ha hP)
    (div_lt_div_of_pos_right hab hP) (by linarith)) hY

/-- Woodford (2003), p. 151: profit `π(p) = p y(p) − C(y(p))` for a cost function `C` with
marginal cost `S`; its derivative is `y(p) [(1 − θ) + θ S(y(p))/p]`. -/
theorem hasDerivAt_profit {Y P θ p : ℝ} {C S : ℝ → ℝ} (hY : 0 < Y) (hP : 0 < P) (hp : 0 < p)
    (hC : ∀ y, 0 < y → HasDerivAt C (S y) y) :
    HasDerivAt (fun p => p * dem Y P θ p - C (dem Y P θ p))
      (dem Y P θ p * ((1 - θ) + θ * S (dem Y P θ p) / p)) p := by
  have hd := hasDerivAt_dem (Y := Y) (θ := θ) hP hp
  have h := ((hasDerivAt_id p).mul hd).sub ((hC _ (dem_pos hY hP hp)).comp p hd)
  refine HasDerivAt.congr_deriv h ?_
  simp only [id]
  have := hp.ne'
  field_simp
  ring

/-- Woodford (2003), p. 151 (**the Lerner formula**): the first-order condition for the optimal
price holds iff `p = μ S(y(p))` with the desired markup `μ = θ/(θ − 1) > 1`. -/
theorem lerner_foc_iff {Y P θ p : ℝ} {S : ℝ → ℝ} (hθ : 1 < θ) (hY : 0 < Y) (hP : 0 < P)
    (hp : 0 < p) :
    dem Y P θ p * ((1 - θ) + θ * S (dem Y P θ p) / p) = 0 ↔
      p = θ / (θ - 1) * S (dem Y P θ p) := by
  have hd := (dem_pos (θ := θ) hY hP hp).ne'
  have hθ1 : θ - 1 ≠ 0 := by linarith
  set Sv := S (dem Y P θ p) with hSv
  rw [mul_eq_zero, or_iff_right hd]
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    have hSv0 : Sv ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h
      linarith
    rw [h]
    field_simp
    ring

/-- Woodford (2003), p. 154 ("the elements of Assumption 3.1 are easily seen to be satisfied"):
with constant-elasticity demand (`θ > 1`) and a positive, nondecreasing, continuous marginal
cost `S` (convex costs), profit is single-peaked in the own price, and the peak `p*` is the
unique positive price satisfying the Lerner formula `p* = μ S(y(p*))`. -/
theorem lerner_singlePeaked {Y P θ : ℝ} {C S : ℝ → ℝ} (hθ : 1 < θ) (hY : 0 < Y) (hP : 0 < P)
    (hC : ∀ y, 0 < y → HasDerivAt C (S y) y) (hS : ∀ y, 0 < y → 0 < S y)
    (hSm : MonotoneOn S (Set.Ioi 0)) (hSc : ContinuousOn S (Set.Ioi 0)) :
    ∃ pstar, SinglePeakedAt (fun p => p * dem Y P θ p - C (dem Y P θ p)) pstar ∧
      pstar = θ / (θ - 1) * S (dem Y P θ pstar) ∧
      ∀ p, 0 < p → p = θ / (θ - 1) * S (dem Y P θ p) → p = pstar := by
  have hθ0 : 0 < θ := by linarith
  have hθ1 : 0 < θ - 1 := by linarith
  set φ : ℝ → ℝ := fun p => θ * S (dem Y P θ p) - (θ - 1) * p with hφ
  have hdemc : ContinuousOn (dem Y P θ) (Set.Ioi 0) := fun p hp =>
    (hasDerivAt_dem (Y := Y) (θ := θ) hP hp).continuousAt.continuousWithinAt
  have hφc : ContinuousOn φ (Set.Ioi 0) :=
    ((continuousOn_const.mul (hSc.comp hdemc fun p hp => dem_pos hY hP hp)).sub
      (continuousOn_const.mul continuousOn_id))
  have hSd : ∀ a b, 0 < a → a ≤ b → S (dem Y P θ b) ≤ S (dem Y P θ a) := by
    intro a b ha hab
    rcases hab.lt_or_eq with hlt | rfl
    · exact hSm (dem_pos hY hP (ha.trans hlt)) (dem_pos hY hP ha)
        ((dem_strictAntiOn hY hP hθ0 ha (ha.trans hlt) hlt).le)
    · exact le_rfl
  have hφanti : StrictAntiOn φ (Set.Ioi 0) := by
    intro a ha b _ hab
    have := hSd a b ha hab.le
    simp only [hφ]
    nlinarith
  set s1 := S (dem Y P θ 1) with hs1
  have hs1pos : 0 < s1 := hS _ (dem_pos hY hP one_pos)
  set plo := min 1 (θ * s1 / (2 * (θ - 1))) with hplo
  set phi := max 1 (2 * θ * s1 / (θ - 1)) with hphi
  have hplo0 : 0 < plo := lt_min one_pos (by positivity)
  have hplo1 : plo ≤ 1 := min_le_left _ _
  have hphi1 : 1 ≤ phi := le_max_left _ _
  have hφlo : 0 < φ plo := by
    have h1 := hSd plo 1 hplo0 hplo1
    have h2 : (θ - 1) * plo ≤ θ * s1 / 2 := by
      have := min_le_right 1 (θ * s1 / (2 * (θ - 1)))
      rw [← hplo] at this
      calc (θ - 1) * plo ≤ (θ - 1) * (θ * s1 / (2 * (θ - 1))) :=
            mul_le_mul_of_nonneg_left this hθ1.le
        _ = θ * s1 / 2 := by field_simp
    simp only [hφ]
    nlinarith
  have hφhi : φ phi < 0 := by
    have h1 := hSd 1 phi one_pos hphi1
    have h2 : 2 * θ * s1 ≤ (θ - 1) * phi := by
      have := le_max_right 1 (2 * θ * s1 / (θ - 1))
      rw [← hphi] at this
      calc 2 * θ * s1 = (θ - 1) * (2 * θ * s1 / (θ - 1)) := by field_simp
        _ ≤ (θ - 1) * phi := mul_le_mul_of_nonneg_left this hθ1.le
    simp only [hφ]
    nlinarith
  obtain ⟨pstar, hps, hps0⟩ := intermediate_value_Icc' (hplo1.trans hphi1)
    (hφc.mono fun p hp => lt_of_lt_of_le hplo0 hp.1) ⟨hφhi.le, hφlo.le⟩
  have hpos : 0 < pstar := lt_of_lt_of_le hplo0 hps.1
  have hderiv : ∀ p, 0 < p → HasDerivAt (fun p => p * dem Y P θ p - C (dem Y P θ p))
      (dem Y P θ p * φ p / p) p := by
    intro p hp
    refine HasDerivAt.congr_deriv (hasDerivAt_profit hY hP hp hC) ?_
    simp only [hφ]
    field_simp
    ring
  have hcont : ∀ p, 0 < p → ContinuousAt (fun p => p * dem Y P θ p - C (dem Y P θ p)) p :=
    fun p hp => (hderiv p hp).continuousAt
  refine ⟨pstar, ⟨hpos, ?_, ?_⟩, ?_, fun p hp hpeq => ?_⟩
  · refine strictMonoOn_of_deriv_pos (convex_Ioc 0 pstar)
      (fun p hp => (hcont p hp.1).continuousWithinAt) fun p hp => ?_
    rw [interior_Ioc] at hp
    rw [(hderiv p hp.1).deriv]
    have : 0 < φ p := by rw [← hps0]; exact hφanti hp.1 hpos hp.2
    exact div_pos (mul_pos (dem_pos hY hP hp.1) this) hp.1
  · refine strictAntiOn_of_deriv_neg (convex_Ici pstar)
      (fun p hp => (hcont p (lt_of_lt_of_le hpos hp)).continuousWithinAt) fun p hp => ?_
    rw [interior_Ici] at hp
    have hp0 : 0 < p := hpos.trans hp
    rw [(hderiv p hp0).deriv]
    have : φ p < 0 := by rw [← hps0]; exact hφanti hpos hp0 hp
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (dem_pos hY hP hp0) this) hp0
  · have : θ * S (dem Y P θ pstar) - (θ - 1) * pstar = 0 := hps0
    field_simp
    linarith
  · have hφp : φ p = 0 := by
      simp only [hφ]
      have h' := hpeq
      field_simp at h'
      linarith
    exact hφanti.injOn hp hpos (hφp.trans hps0.symm)

/-- Woodford (2003), eq. (1.18), p. 153: the baseline profit function
`Π(p, p^I, P; Y, ξ̃) = p Y (p/P)^{−θ}
  − [v_h(f⁻¹(Y (p^I/P)^{−θ}/A); ξ)/u_c(Y; ξ)] P f⁻¹(Y (p/P)^{−θ}/A)`
(with government purchases absorbed into the disturbance, n. 8). -/
noncomputable def baselineProfit {E : Type*} (T : MarginalCost.Technology) (vh uc : ℝ → E → ℝ)
    (θ : ℝ) (p pI P Y : ℝ) (ζ : ℝ × E) : ℝ :=
  p * dem Y P θ p - vh (T.finv (dem Y P θ pI / ζ.1)) ζ.2 / uc Y ζ.2 * P *
    T.finv (dem Y P θ p / ζ.1)

/-- Woodford (2003), Assumption 3.1, p. 153: the baseline profit function (1.18) is homogeneous
of degree one in `(p, p^I, P)`. -/
theorem baselineProfit_homogeneous {E : Type*} (T : MarginalCost.Technology)
    (vh uc : ℝ → E → ℝ) (θ : ℝ) : HomogeneousOne (baselineProfit T vh uc θ) := by
  intro l p q P Y ζ hl _ _ _
  simp only [baselineProfit, dem, mul_div_mul_left _ P hl.ne']
  ring

/-- Woodford (2003), pp. 151–154 (**the baseline model satisfies Assumption 3.1, and the
optimal price is the Lerner markup over marginal cost**): for concave `f` with continuous `f'`,
positive `v_h` and `u_c`, and `θ > 1`, the profit (1.18) is single-peaked in the own price with
peak `p* = μ S(y(p*))`, `S(y) = (w/A) Ψ(y/A)` the nominal marginal cost (1.8) at the industry
wage `w = P v_h(·)/u_c`. -/
theorem baseline_singlePeaked {E : Type*} (T : MarginalCost.Technology) (vh uc : ℝ → E → ℝ)
    {θ pI P Y A : ℝ} {ξ : E} (hθ : 1 < θ) (hY : 0 < Y) (hP : 0 < P) (hA : 0 < A)
    (hdf : AntitoneOn T.df (Set.Ioi 0)) (hdfc : ContinuousOn T.df (Set.Ioi 0))
    (hw : 0 < P * (vh (T.finv (dem Y P θ pI / A)) ξ / uc Y ξ)) :
    ∃ pstar, SinglePeakedAt (fun p => baselineProfit T vh uc θ p pI P Y (A, ξ)) pstar ∧
      pstar = θ / (θ - 1) * (P * (vh (T.finv (dem Y P θ pI / A)) ξ / uc Y ξ) / A *
        T.Psi (dem Y P θ pstar / A)) ∧
      ∀ p, 0 < p → p = θ / (θ - 1) * (P * (vh (T.finv (dem Y P θ pI / A)) ξ / uc Y ξ) / A *
        T.Psi (dem Y P θ p / A)) → p = pstar := by
  set w := P * (vh (T.finv (dem Y P θ pI / A)) ξ / uc Y ξ) with hwdef
  have hC : ∀ y, 0 < y → HasDerivAt (fun y => w * T.finv (y / A)) (w / A * T.Psi (y / A)) y :=
    fun y hy => T.hasDerivAt_variableCost w hA hy
  have hS : ∀ y, 0 < y → 0 < w / A * T.Psi (y / A) := fun y hy =>
    mul_pos (div_pos hw hA) (T.Psi_pos (div_pos hy hA))
  have hSm : MonotoneOn (fun y => w / A * T.Psi (y / A)) (Set.Ioi 0) := by
    intro a ha b hb hab
    exact mul_le_mul_of_nonneg_left (T.Psi_monotoneOn hdf (div_pos ha hA) (div_pos hb hA)
      (div_le_div_of_nonneg_right hab hA.le)) (div_pos hw hA).le
  have hSc : ContinuousOn (fun y => w / A * T.Psi (y / A)) (Set.Ioi 0) :=
    continuousOn_const.mul ((T.Psi_continuousOn hdfc).comp (continuousOn_id.div_const A)
      fun y hy => div_pos hy hA)
  obtain ⟨pstar, hpk, hmk, huniq⟩ := lerner_singlePeaked hθ hY hP hC hS hSm hSc
  refine ⟨pstar, ?_, hmk, huniq⟩
  have hfun : (fun p => baselineProfit T vh uc θ p pI P Y (A, ξ))
      = fun p => p * dem Y P θ p - w * T.finv (dem Y P θ p / A) := by
    funext p
    simp only [baselineProfit, hwdef]
    ring
  rw [hfun]
  exact hpk

/-- Woodford (2003), eq. (1.13), p. 151: at the optimal price, when the rest of the industry
charges the same price (`p^I = p`), the relative price is the desired markup times real marginal
cost: `p/P = μ s(y, Y; ξ̃)` with `y = Y (p/P)^{−θ}`. -/
theorem baseline_markup {E : Type*} (T : MarginalCost.Technology) (vh uc : ℝ → E → ℝ)
    {θ p P Y A : ℝ} {ξ : E} (hP : 0 < P) (hA : 0 < A) (huc : 0 < uc Y ξ)
    (hp : p = θ / (θ - 1) * (P * (vh (T.finv (dem Y P θ p / A)) ξ / uc Y ξ) / A *
      T.Psi (dem Y P θ p / A))) :
    p / P = θ / (θ - 1) * MarginalCost.rmc T vh uc (dem Y P θ p) Y A ξ := by
  have := hP.ne'
  have := hA.ne'
  have := huc.ne'
  rw [MarginalCost.rmc]
  nth_rewrite 1 [hp]
  field_simp

/-- Woodford (2003), p. 151 and Proposition 3.1, p. 154 (**for the baseline model, (1.21) is
(1.14)**): with `p^I = P`, output `Y` is a flexible-price equilibrium at price level `P` iff
`μ s(Y, Y; ξ̃) = 1`, `μ = θ/(θ − 1)`. -/
theorem baseline_flexEqm_iff {E : Type*} (T : MarginalCost.Technology) (vh uc : ℝ → E → ℝ)
    {θ P Y A : ℝ} {ξ : E} (hθ : 1 < θ) (hY : 0 < Y) (hP : 0 < P) (hA : 0 < A)
    (hdf : AntitoneOn T.df (Set.Ioi 0)) (hdfc : ContinuousOn T.df (Set.Ioi 0))
    (hvh : 0 < vh (T.finv (Y / A)) ξ) (huc : 0 < uc Y ξ) :
    FlexEqm (baselineProfit T vh uc θ) P Y (A, ξ) ↔
      θ / (θ - 1) * MarginalCost.rmc T vh uc Y Y A ξ = 1 := by
  have hdemP : dem Y P θ P = Y := by
    rw [dem, div_self hP.ne', Real.one_rpow, mul_one]
  have hw : 0 < P * (vh (T.finv (dem Y P θ P / A)) ξ / uc Y ξ) := by
    rw [hdemP]; exact mul_pos hP (div_pos hvh huc)
  obtain ⟨pstar, hpk, hmk, huniq⟩ :=
    baseline_singlePeaked T vh uc (pI := P) hθ hY hP hA hdf hdfc hw
  have hθ1 : θ - 1 ≠ 0 := by linarith
  have hiff : FlexEqm (baselineProfit T vh uc θ) P Y (A, ξ) ↔ P = pstar :=
    singlePeaked_isOptimal_iff hpk
  rw [hiff, MarginalCost.rmc]
  have := hA.ne'
  have := huc.ne'
  have := hP.ne'
  constructor
  · intro h
    rw [← h, hdemP] at hmk
    field_simp at hmk ⊢
    linarith
  · intro h
    refine huniq P hP ?_
    rw [hdemP]
    field_simp at h ⊢
    linarith

/-! ### Relative supply (1.13) and the symmetric equilibrium (1.14) -/

/-- Woodford (2003), p. 151 ("this equation must have a unique solution for `y(i)` given `Y`"):
for `θ > 1`, `μ > 0`, and `s(·, Y)` positive, nondecreasing and continuous on `(0, ∞)`, the
relative-supply equation `(y/Y)^{−1/θ} = μ s(y, Y)` has exactly one positive solution
(existence needs only these conditions; the book's argument gives uniqueness). -/
theorem relative_supply_existsUnique {θ μm Y : ℝ} {s : ℝ → ℝ} (hθ : 1 < θ) (hμ : 0 < μm)
    (hY : 0 < Y) (hs : ∀ y, 0 < y → 0 < s y) (hsm : MonotoneOn s (Set.Ioi 0))
    (hsc : ContinuousOn s (Set.Ioi 0)) :
    ∃! y, 0 < y ∧ (y / Y) ^ (-1 / θ) = μm * s y := by
  have hθ0 : 0 < θ := by linarith
  have he : -1 / θ < 0 := div_neg_of_neg_of_pos (by norm_num) hθ0
  set ψ : ℝ → ℝ := fun y => (y / Y) ^ (-1 / θ) - μm * s y with hψ
  have hψc : ContinuousOn ψ (Set.Ioi 0) := by
    refine ContinuousOn.sub ?_ (continuousOn_const.mul hsc)
    refine fun y hy => (ContinuousAt.continuousWithinAt ?_)
    exact (continuousAt_id.div_const Y).rpow_const (Or.inl (div_pos hy hY).ne')
  have hψanti : StrictAntiOn ψ (Set.Ioi 0) := by
    intro a ha b hb hab
    have h1 : (b / Y) ^ (-1 / θ) < (a / Y) ^ (-1 / θ) :=
      Real.rpow_lt_rpow_of_neg (div_pos ha hY) (div_lt_div_of_pos_right hab hY) he
    have h2 := hsm ha hb hab.le
    simp only [hψ]
    nlinarith
  set M := μm * s 1 with hM
  have hM0 : 0 < M := mul_pos hμ (hs 1 one_pos)
  set ylo := min 1 (Y * (M + 1) ^ (-θ)) with hylo
  set yhi := max 1 (Y * (M / 2) ^ (-θ)) with hyhi
  have hylo0 : 0 < ylo := lt_min one_pos (mul_pos hY (Real.rpow_pos_of_pos (by linarith) _))
  have hylo1 : ylo ≤ 1 := min_le_left _ _
  have hyhi1 : 1 ≤ yhi := le_max_left _ _
  have hrt : ∀ c : ℝ, 0 < c → ((c ^ (-θ)) ^ (-1 / θ)) = c := by
    intro c hc
    rw [← Real.rpow_mul hc.le]
    have : -θ * (-1 / θ) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hψlo : 0 < ψ ylo := by
    have h1 : (M + 1) ≤ (ylo / Y) ^ (-1 / θ) := by
      have hle : ylo / Y ≤ (M + 1) ^ (-θ) := by
        rw [div_le_iff₀ hY, mul_comm]
        exact min_le_right _ _
      calc M + 1 = ((M + 1) ^ (-θ)) ^ (-1 / θ) := (hrt _ (by linarith)).symm
        _ ≤ (ylo / Y) ^ (-1 / θ) := Real.rpow_le_rpow_of_nonpos (div_pos hylo0 hY) hle he.le
    have h2 : μm * s ylo ≤ M := mul_le_mul_of_nonneg_left
      (hsm hylo0 (show (1 : ℝ) ∈ Set.Ioi 0 from Set.mem_Ioi.2 one_pos) hylo1) hμ.le
    simp only [hψ]
    linarith
  have hψhi : ψ yhi < 0 := by
    have hyhi0 : 0 < yhi := lt_of_lt_of_le one_pos hyhi1
    have h1 : (yhi / Y) ^ (-1 / θ) ≤ M / 2 := by
      have hle : (M / 2) ^ (-θ) ≤ yhi / Y := by
        rw [le_div_iff₀ hY, mul_comm]
        exact le_max_right _ _
      calc (yhi / Y) ^ (-1 / θ) ≤ ((M / 2) ^ (-θ)) ^ (-1 / θ) :=
            Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (by linarith) _) hle he.le
        _ = M / 2 := hrt _ (by linarith)
    have h2 : M ≤ μm * s yhi := mul_le_mul_of_nonneg_left
      (hsm (show (1 : ℝ) ∈ Set.Ioi 0 from Set.mem_Ioi.2 one_pos) hyhi0 hyhi1) hμ.le
    simp only [hψ]
    linarith
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' (hylo1.trans hyhi1)
    (hψc.mono fun y hy => lt_of_lt_of_le hylo0 hy.1) ⟨hψhi.le, hψlo.le⟩
  have hypos : 0 < y := lt_of_lt_of_le hylo0 hy.1
  refine ⟨y, ⟨hypos, by simp only [hψ] at hy0; linarith⟩, fun z ⟨hz, hzeq⟩ => ?_⟩
  have hz0 : ψ z = 0 := by simp only [hψ]; linarith
  exact hψanti.injOn hz hypos (hz0.trans hy0.symm)

/-- Woodford (2003), p. 151 (**the symmetric flexible-price equilibrium**): if every supplier's
output solves the relative-supply equation (1.13) and `Y` is the Dixit–Stiglitz index (1.2) of
the outputs (goods form a probability space), then every supplier produces `Y` and
`μ s(Y, Y; ξ̃) = 1`, i.e. (1.14). -/
theorem symmetric_flexible_eqm {G : Type*} [MeasurableSpace G] (μ : MeasureTheory.Measure G)
    [MeasureTheory.IsProbabilityMeasure μ] {θ μm Y : ℝ} {s : ℝ → ℝ → ℝ} (hθ : 1 < θ)
    (hμ : 0 < μm) (hY : 0 < Y) (hs : ∀ y, 0 < y → 0 < s y Y)
    (hsm : MonotoneOn (fun y => s y Y) (Set.Ioi 0))
    (hsc : ContinuousOn (fun y => s y Y) (Set.Ioi 0)) {y : G → ℝ}
    (hy : ∀ i, 0 < y i ∧ (y i / Y) ^ (-1 / θ) = μm * s (y i) Y)
    (hagg : Y = DixitStiglitz.cesAgg μ θ y) :
    (∀ i, y i = Y) ∧ μm * s Y Y = 1 := by
  obtain ⟨yh, ⟨hyh, hyheq⟩, huniq⟩ := relative_supply_existsUnique hθ hμ hY hs hsm hsc
  have hall : ∀ i, y i = yh := fun i => huniq (y i) (hy i)
  have hconst : y = fun _ => yh := funext hall
  have hYyh : Y = yh := by
    rw [hagg, hconst, DixitStiglitz.cesAgg_const hθ hyh.le]
  refine ⟨fun i => (hall i).trans hYyh.symm, ?_⟩
  rw [← hYyh, div_self hY.ne', Real.one_rpow] at hyheq
  exact hyheq.symm

/-- Woodford (2003), eq. (1.14), p. 151 (converse): if `μ s(Y, Y; ξ̃) = 1`, the symmetric
allocation `y(i) = Y` solves (1.13) for every supplier and has index `Y`. -/
theorem symmetric_flexible_eqm_of {G : Type*} [MeasurableSpace G] (μ : MeasureTheory.Measure G)
    [MeasureTheory.IsProbabilityMeasure μ] {θ μm Y : ℝ} {s : ℝ → ℝ → ℝ} (hθ : 1 < θ)
    (hY : 0 < Y) (h : μm * s Y Y = 1) :
    (∀ _i : G, 0 < Y ∧ (Y / Y) ^ (-1 / θ) = μm * s Y Y) ∧
      Y = DixitStiglitz.cesAgg μ θ (fun _ => Y) := by
  refine ⟨fun _ => ⟨hY, by rw [div_self hY.ne', Real.one_rpow, h]⟩, ?_⟩
  rw [DixitStiglitz.cesAgg_const hθ hY.le]

/-! ### Existence and uniqueness of the natural rate (1.14) -/

/-- Woodford (2003), eq. (1.14), p. 151 (**existence and uniqueness of `Yⁿ`, minimal
conditions**): if `S(Y) = s(Y, Y; ξ̃)` is continuous and strictly increasing on `(0, ∞)`, then
(1.14) `S(Yⁿ) = μ⁻¹` has a unique positive solution IFF `μ⁻¹` lies between two values of `S`
(a boundary condition the book omits). -/
theorem naturalRate_existsUnique_iff {Sd : ℝ → ℝ} {c : ℝ} (hc : ContinuousOn Sd (Set.Ioi 0))
    (hm : StrictMonoOn Sd (Set.Ioi 0)) :
    (∃! Yn, 0 < Yn ∧ Sd Yn = c) ↔
      ∃ Y₁ Y₂, 0 < Y₁ ∧ 0 < Y₂ ∧ Sd Y₁ ≤ c ∧ c ≤ Sd Y₂ := by
  constructor
  · rintro ⟨Yn, ⟨hYn, hS⟩, -⟩
    exact ⟨Yn, Yn, hYn, hYn, hS.le, hS.ge⟩
  · rintro ⟨Y₁, Y₂, h₁, h₂, hS₁, hS₂⟩
    have hle : Y₁ ≤ Y₂ := by
      by_contra hlt
      push Not at hlt
      have := hm h₂ h₁ hlt
      linarith
    obtain ⟨Yn, hYn, hSn⟩ := intermediate_value_Icc hle
      (hc.mono fun y hy => lt_of_lt_of_le h₁ hy.1) ⟨hS₁, hS₂⟩
    have hpos : 0 < Yn := lt_of_lt_of_le h₁ hYn.1
    exact ⟨Yn, ⟨hpos, hSn⟩, fun Z ⟨hZ, hSZ⟩ => hm.injOn hZ hpos (hSZ.trans hSn.symm)⟩

/-- Woodford (2003), p. 151: if `s` is strictly increasing in each argument, the diagonal
`Y ↦ s(Y, Y; ξ̃)` is strictly increasing (the source of uniqueness of `Yⁿ`). -/
theorem diag_strictMonoOn {s : ℝ → ℝ → ℝ}
    (h1 : ∀ Y, 0 < Y → StrictMonoOn (fun y => s y Y) (Set.Ioi 0))
    (h2 : ∀ y, 0 < y → StrictMonoOn (fun Y => s y Y) (Set.Ioi 0)) :
    StrictMonoOn (fun Y => s Y Y) (Set.Ioi 0) := by
  intro a ha b hb hab
  exact (h1 a ha ha hb hab).trans (h2 b hb ha hb hab)

/-- Woodford (2003), p. 151: a marginal disutility `v_h(h) = k h/(1 + h)` (`v` increasing,
convex) and marginal utility `u_c(Y) = 1 + 1/Y` (`u(Y) = Y + log Y`, increasing, concave). -/
noncomputable def boundedVh (k : ℝ) (h : ℝ) (_ξ : Unit) : ℝ := k * h / (1 + h)

/-- Woodford (2003), p. 151: the marginal utility `u_c(Y) = 1 + 1/Y`. -/
noncomputable def boundedUc (Y : ℝ) (_ξ : Unit) : ℝ := 1 + 1 / Y

/-- Woodford (2003), p. 151: in the bounded example, `s(y, Y) = k y Y / ((1 + y)(1 + Y))`. -/
theorem bounded_rmc (k : ℝ) {y Y : ℝ} (hy : 0 < y) (hY : 0 < Y) :
    MarginalCost.rmc MarginalCost.linearTech (boundedVh k) boundedUc y Y 1 ()
      = k * y * Y / ((1 + y) * (1 + Y)) := by
  simp only [MarginalCost.rmc, MarginalCost.linearTech_Psi, boundedVh, boundedUc, div_one]
  simp only [MarginalCost.linearTech, id]
  have : 1 + y ≠ 0 := by linarith
  have : 1 + Y ≠ 0 := by linarith
  have := hY.ne'
  field_simp
  ring

/-- Woodford (2003), p. 144 and p. 151: the bounded example satisfies the book's hypotheses —
`v_h > 0` strictly increasing (`v` increasing, strictly convex), `u_c > 0` strictly decreasing
(`u` increasing, strictly concave), `f` linear (increasing, concave). -/
theorem bounded_primitives {k : ℝ} (hk : 0 < k) :
    (∀ h, 0 < h → 0 < boundedVh k h ()) ∧
      StrictMonoOn (fun h => boundedVh k h ()) (Set.Ioi 0) ∧
      (∀ Y, 0 < Y → 0 < boundedUc Y ()) ∧
      StrictAntiOn (fun Y => boundedUc Y ()) (Set.Ioi 0) := by
  refine ⟨fun h hh => by unfold boundedVh; positivity, fun a ha b hb hab => ?_,
    fun Y hY => by unfold boundedUc; positivity, fun a ha b hb hab => ?_⟩
  · have ha' : (0 : ℝ) < a := ha
    have hb' : (0 : ℝ) < b := hb
    simp only [boundedVh]
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · have ha' : (0 : ℝ) < a := ha
    simp only [boundedUc]
    have : 1 / b < 1 / a := one_div_lt_one_div_of_lt ha' hab
    linarith

/-- Woodford (2003), p. 151: in the bounded example `s` is strictly increasing in each
argument (as the book requires). -/
theorem bounded_rmc_strictMono {k : ℝ} (hk : 0 < k) :
    (∀ Y, 0 < Y → StrictMonoOn
      (fun y => MarginalCost.rmc MarginalCost.linearTech (boundedVh k) boundedUc y Y 1 ())
      (Set.Ioi 0)) ∧
    (∀ y, 0 < y → StrictMonoOn
      (fun Y => MarginalCost.rmc MarginalCost.linearTech (boundedVh k) boundedUc y Y 1 ())
      (Set.Ioi 0)) := by
  constructor
  · intro Y hY a ha b hb hab
    have ha' : (0 : ℝ) < a := ha
    have hb' : (0 : ℝ) < b := hb
    simp only [bounded_rmc k ha' hY, bounded_rmc k hb' hY]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : 0 < k * Y * (1 + Y) := by positivity
    nlinarith [mul_pos this (sub_pos.2 hab)]
  · intro y hy a ha b hb hab
    have ha' : (0 : ℝ) < a := ha
    have hb' : (0 : ℝ) < b := hb
    simp only [bounded_rmc k hy ha', bounded_rmc k hy hb']
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : 0 < k * y * (1 + y) := by positivity
    nlinarith [mul_pos this (sub_pos.2 hab)]

/-- Woodford (2003), eq. (1.14), p. 151 (**counterexample: no natural rate**). With
`k = μ⁻¹ = (θ − 1)/θ`, the bounded example satisfies every stated hypothesis (`s` increasing in
both arguments, `v` increasing convex, `u` increasing concave, `f` increasing concave), yet
`s(Y, Y) < μ⁻¹` for all `Y > 0`: (1.14) has NO solution. -/
theorem noNaturalRate_baseline {θ : ℝ} (hθ : 1 < θ) {Y : ℝ} (hY : 0 < Y) :
    MarginalCost.rmc MarginalCost.linearTech (boundedVh ((θ - 1) / θ)) boundedUc Y Y 1 ()
      < (θ - 1) / θ := by
  have hk : 0 < (θ - 1) / θ := div_pos (by linarith) (by linarith)
  rw [bounded_rmc _ hY hY, div_lt_iff₀ (by positivity)]
  nlinarith [mul_pos hk hY]

/-- Woodford (2003), Proposition 3.1, p. 154 (**counterexample in the baseline model**): with
the bounded example and `k = μ⁻¹`, the baseline profit function (1.18) is single-peaked in the own
price (`baseline_singlePeaked`), yet NO output level is a flexible-price equilibrium at any
price level. -/
theorem baseline_noFlexEqm {θ : ℝ} (hθ : 1 < θ) {P Y : ℝ} (hP : 0 < P) (hY : 0 < Y) :
    ¬ FlexEqm (baselineProfit MarginalCost.linearTech (boundedVh ((θ - 1) / θ)) boundedUc θ)
      P Y (1, ()) := by
  have hk : 0 < (θ - 1) / θ := div_pos (by linarith) (by linarith)
  obtain ⟨hvpos, -, hupos, -⟩ := bounded_primitives hk
  intro h
  have hiff := baseline_flexEqm_iff MarginalCost.linearTech (boundedVh ((θ - 1) / θ)) boundedUc
    (ξ := ()) hθ hY hP one_pos (fun _ _ _ _ _ => le_rfl) continuousOn_const
    (hvpos _ (by simpa [MarginalCost.linearTech] using hY)) (hupos _ hY)
  have h1 := hiff.1 h
  have h2 := noNaturalRate_baseline hθ hY
  have hθ0 : 0 < θ / (θ - 1) := div_pos (by linarith) (by linarith)
  have h3 : θ / (θ - 1) * MarginalCost.rmc MarginalCost.linearTech (boundedVh ((θ - 1) / θ))
      boundedUc Y Y 1 () < θ / (θ - 1) * ((θ - 1) / θ) := mul_lt_mul_of_pos_left h2 hθ0
  have h4 : θ / (θ - 1) * ((θ - 1) / θ) = 1 := by
    have : θ - 1 ≠ 0 := by linarith
    have : θ ≠ 0 := by linarith
    field_simp
  linarith

/-- Woodford (2003), eq. (1.14), p. 151 (a case where the natural rate exists): if
`s(Y, Y) = κ Y^e` with `κ, e > 0` (isoelastic preferences and technology, `e = ω + σ⁻¹`), then
(1.14) has the unique solution `Yⁿ = (μ⁻¹/κ)^{1/e}`. -/
theorem isoelastic_naturalRate {κ e c : ℝ} (hκ : 0 < κ) (he : 0 < e) (hc : 0 < c) :
    ∃! Yn, 0 < Yn ∧ κ * Yn ^ e = c := by
  have hck : 0 < c / κ := div_pos hc hκ
  refine ⟨(c / κ) ^ (1 / e), ⟨Real.rpow_pos_of_pos hck _, ?_⟩, fun Y ⟨hY, hYe⟩ => ?_⟩
  · rw [one_div, Real.rpow_inv_rpow hck.le he.ne']
    field_simp
  · have : Y ^ e = c / κ := by rw [← hYe]; field_simp
    rw [← this, one_div, Real.rpow_rpow_inv hY.le he.ne']

/-! ### Regularity of the natural rate and the exact log-linearisation (1.15) -/

/-- Woodford (2003), p. 152: the root `n(z)` of an equation `F(k, z) = 0` that is strictly
increasing in `k` and continuous in `z` at `z₀` is continuous at `z₀` (continuity of the natural
rate in the shocks). -/
theorem root_continuousAt {Z : Type*} [TopologicalSpace Z] {F : ℝ → Z → ℝ} {n : Z → ℝ}
    {z₀ : Z} (hmono : ∀ z, StrictMono fun k => F k z)
    (hcont : ∀ k, ContinuousAt (fun z => F k z) z₀) (hroot : ∀ z, F (n z) z = 0) :
    ContinuousAt n z₀ := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have h0 : F a z₀ < 0 := by rw [← hroot z₀]; exact hmono z₀ ha
    filter_upwards [(hcont a).eventually (gt_mem_nhds h0)] with z hz
    by_contra hle
    push Not at hle
    have := (hmono z).monotone hle
    rw [hroot z] at this
    linarith
  · have h0 : 0 < F b z₀ := by rw [← hroot z₀]; exact hmono z₀ hb
    filter_upwards [(hcont b).eventually (lt_mem_nhds h0)] with z hz
    by_contra hle
    push Not at hle
    have := (hmono z).monotone hle
    rw [hroot z] at this
    linarith

/-- Woodford (2003), p. 152 (the implicit-function step behind (1.15), proved here): let
`H(k, z)` be differentiable at `0` with `κ = ∂H/∂k ≠ 0`, and let `n` be continuous at `0` with
`n(0) = 0` and `H(n(z), z) = H(0)` near `0`. Then `n` is differentiable at `0` with
`Dn = −κ⁻¹ ∂H/∂z`. -/
theorem implicit_hasFDerivAt {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {H : ℝ × Z → ℝ} {D : ℝ × Z →L[ℝ] ℝ} (hH : HasFDerivAt H D 0) (hκ : D (1, 0) ≠ 0)
    {n : Z → ℝ} (hn : ContinuousAt n 0) (hn0 : n 0 = 0)
    (hroot : ∀ᶠ z in 𝓝 (0 : Z), H (n z, z) = H 0) :
    HasFDerivAt n (-(D (1, 0))⁻¹ • D.comp (ContinuousLinearMap.inr ℝ ℝ Z)) 0 := by
  set κ := D (1, 0) with hκdef
  have hsplit : ∀ z, D (n z, z) = κ * n z + D (0, z) := by
    intro z
    have : ((n z, z) : ℝ × Z) = n z • ((1 : ℝ), (0 : Z)) + ((0 : ℝ), z) := by simp
    rw [this, map_add, map_smul, smul_eq_mul, hκdef]
    ring
  have hφ : Tendsto (fun z : Z => ((n z, z) : ℝ × Z)) (𝓝 0) (𝓝 0) := by
    have := hn.tendsto.prodMk_nhds (tendsto_id (x := 𝓝 (0 : Z)))
    rw [hn0] at this
    exact this
  have ho := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hH).comp_tendsto hφ
  have he : (fun z => D (n z, z)) =o[𝓝 (0 : Z)] (fun z => ((n z, z) : ℝ × Z)) := by
    refine ho.neg_left.congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards [hroot] with z hz
    simp only [Function.comp_apply, zero_add, hz]
    ring
  have hκpos : 0 < |κ| := abs_pos.2 hκ
  set C := 1 + 2 * ‖D‖ / |κ| with hC
  have hbig : (fun z => ((n z, z) : ℝ × Z)) =O[𝓝 (0 : Z)] (fun z => z) := by
    refine Asymptotics.IsBigO.of_bound (max C 1) ?_
    filter_upwards [he.def (c := |κ| / 2) (by positivity)] with z hz
    have hD0 : ‖D (0, z)‖ ≤ ‖D‖ * ‖z‖ := by
      have := D.le_opNorm (0, z)
      simpa using this
    rw [Prod.norm_mk] at hz ⊢
    rw [hsplit] at hz
    set a := ‖n z‖
    set b := ‖z‖
    have hb : 0 ≤ b := norm_nonneg _
    have ha : 0 ≤ a := norm_nonneg _
    have hka : |κ| * a ≤ |κ| / 2 * (a + b) + ‖D‖ * b := by
      have h1 : |κ| * a = ‖κ * n z‖ := by rw [norm_mul, Real.norm_eq_abs]
      have h2 : ‖κ * n z‖ ≤ ‖κ * n z + D (0, z)‖ + ‖D (0, z)‖ := by
        have := norm_sub_le (κ * n z + D (0, z)) (D (0, z))
        simpa using this
      have h3 : max a b ≤ a + b := max_le (by linarith) (by linarith)
      nlinarith
    have hac : a ≤ C * b := by
      have : |κ| * a ≤ |κ| * (C * b) := by
        have e : |κ| * (C * b) = |κ| * b + 2 * ‖D‖ * b := by
          rw [hC]; field_simp
        rw [e]
        linarith
      exact le_of_mul_le_mul_left this hκpos
    refine max_le (hac.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hb)) ?_
    calc b = 1 * b := (one_mul b).symm
      _ ≤ max C 1 * b := mul_le_mul_of_nonneg_right (le_max_right _ _) hb
  have he' := (he.trans_isBigO hbig).const_mul_left κ⁻¹
  have hL : ∀ z : Z, (-(D (1, 0))⁻¹ • D.comp (ContinuousLinearMap.inr ℝ ℝ Z)) z
      = -κ⁻¹ * D (0, z) := fun z => rfl
  refine hasFDerivAt_iff_isLittleO_nhds_zero.2 (he'.congr_left fun z => ?_)
  rw [hL, zero_add, hn0, sub_zero, hsplit]
  field_simp
  ring

/-- Woodford (2003), p. 151: when `v_h(·; ξ)` is positive and nondecreasing, `f` concave (one of
them strictly), and `u_c(·; ξ)` positive and strictly decreasing, for every shock the log real
marginal cost along the diagonal `y = Y = Ȳ eᵏ` is strictly increasing in `k`. -/
theorem logRmcGap_diag_strictMono {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : MarginalCost.Technology) (vh uc : ℝ → F → ℝ) {Ybar : ℝ} (hY : 0 < Ybar)
    (hvh : ∀ ξ h, 0 < h → 0 < vh h ξ) (hvm : ∀ ξ, MonotoneOn (fun h => vh h ξ) (Set.Ioi 0))
    (huc : ∀ ξ Y, 0 < Y → 0 < uc Y ξ) (hanti : ∀ ξ, StrictAntiOn (fun Y => uc Y ξ) (Set.Ioi 0))
    (hdf : AntitoneOn T.df (Set.Ioi 0))
    (hstrict : ∀ ξ, StrictMonoOn (fun h => vh h ξ) (Set.Ioi 0) ∨ StrictAntiOn T.df (Set.Ioi 0))
    (z : ℝ × F) : StrictMono fun k => MarginalCost.logRmcGap T vh uc Ybar (k, k, z.1, z.2) := by
  intro k₁ k₂ hk
  have hA := Real.exp_pos z.1
  have hy₁ : 0 < Ybar * Real.exp k₁ := mul_pos hY (Real.exp_pos _)
  have hy₂ : 0 < Ybar * Real.exp k₂ := mul_pos hY (Real.exp_pos _)
  have hlt : Ybar * Real.exp k₁ < Ybar * Real.exp k₂ :=
    mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 hk) hY
  have hpos : 0 < MarginalCost.rmc T vh uc (Ybar * Real.exp k₁) (Ybar * Real.exp k₁)
      (Real.exp z.1) z.2 := by
    unfold MarginalCost.rmc
    have hu := div_pos hy₁ hA
    exact mul_pos (div_pos (hvh _ _ (T.finv_pos _ hu)) (mul_pos (huc _ _ hy₁) hA))
      (T.Psi_pos hu)
  have h1 := MarginalCost.rmc_strictMonoOn_y T vh uc hA (huc z.2 _ hy₁) (hvh z.2) (hvm z.2) hdf
    (hstrict z.2)
    hy₁ hy₂ hlt
  have h2 := MarginalCost.rmc_strictMonoOn_Y T vh uc (ξ := z.2) hy₂ hA (hvh z.2) (huc z.2)
    (hanti z.2)
    hy₁ hy₂ hlt
  simp only [MarginalCost.logRmcGap]
  exact sub_lt_sub_right (Real.log_lt_log hpos (h1.trans h2)) _

/-- Woodford (2003), eqs. (1.14)–(1.15), p. 152 (**the log-linear real marginal cost function,
unconditionally**): if the log natural rate `n(a, ξ) = log(Yⁿ/Ȳ)` solves (1.14),
`s(Yⁿ, Yⁿ; ξ̃) = s̄`, for every shock, the diagonal of `ŝ` is strictly increasing and continuous
in the shocks, and `ω + σ⁻¹ ≠ 0`, then `n` is differentiable at the steady state (no assumption)
and `Dŝ(ŷ, Ŷ, a, ξ) = ω ŷ + σ⁻¹ Ŷ − (ω + σ⁻¹) Dn(a, ξ)` exactly. -/
theorem eq_1_15_unconditional {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : MarginalCost.Technology) (vh uc : ℝ → F → ℝ) {vhh d2f ucc Ybar : ℝ}
    (hY : 0 < Ybar) (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar))
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar))
    (hucc : HasDerivAt (fun Y => uc Y 0) ucc Ybar)
    (hvhd : DifferentiableAt ℝ (fun q : ℝ × F => vh q.1 q.2) (T.finv Ybar, 0))
    (hucd : DifferentiableAt ℝ (fun q : ℝ × F => uc q.1 q.2) (Ybar, 0))
    (hvh : ∀ h, 0 < h → 0 < vh h 0) (huc : ∀ Y, 0 < Y → 0 < uc Y 0)
    (hκ : MarginalCost.omegaW T vh vhh Ybar + MarginalCost.omegaP T d2f Ybar
      + MarginalCost.sigmaInv uc ucc Ybar ≠ 0)
    (hmono : ∀ z : ℝ × F, StrictMono fun k => MarginalCost.logRmcGap T vh uc Ybar (k, k, z.1, z.2))
    (hcont : ∀ k, ContinuousAt
      (fun z : ℝ × F => MarginalCost.logRmcGap T vh uc Ybar (k, k, z.1, z.2)) 0)
    {n : ℝ × F → ℝ} (hroot : ∀ z, MarginalCost.logRmcGap T vh uc Ybar (n z, n z, z.1, z.2) = 0) :
    ∃ Dn : ℝ × F →L[ℝ] ℝ, HasFDerivAt n Dn 0 ∧ ∀ (x X a : ℝ) (ξ : F),
      fderiv ℝ (MarginalCost.logRmcGap T vh uc Ybar) 0 (x, X, a, ξ)
        = (MarginalCost.omegaW T vh vhh Ybar + MarginalCost.omegaP T d2f Ybar) * x
          + MarginalCost.sigmaInv uc ucc Ybar * X
          - (MarginalCost.omegaW T vh vhh Ybar + MarginalCost.omegaP T d2f Ybar
            + MarginalCost.sigmaInv uc ucc Ybar) * Dn (a, ξ) := by
  have hG0 : MarginalCost.logRmcGap T vh uc Ybar 0 = 0 := by
    simp [MarginalCost.logRmcGap]
  have hn0 : n 0 = 0 := by
    have h1 := hroot 0
    have h2 : MarginalCost.logRmcGap T vh uc Ybar (0, 0, (0 : ℝ × F).1, (0 : ℝ × F).2) = 0 := hG0
    exact (hmono 0).injective (h1.trans h2.symm)
  have hncont : ContinuousAt n 0 :=
    root_continuousAt
      (F := fun (k : ℝ) (z : ℝ × F) => MarginalCost.logRmcGap T vh uc Ybar (k, k, z.1, z.2))
      (z₀ := (0 : ℝ × F)) hmono hcont hroot
  have hD := (MarginalCost.logRmcGap_differentiableAt T vh uc hY hd2f hvhd hucd
    (hvh _ (T.finv_pos _ hY))
    (huc _ hY)).hasFDerivAt
  set D := fderiv ℝ (MarginalCost.logRmcGap T vh uc Ybar) 0
  set L : ℝ × (ℝ × F) →L[ℝ] ℝ × ℝ × ℝ × F :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × F)).prod
      ((ContinuousLinearMap.fst ℝ ℝ (ℝ × F)).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × F)))
  have hD' : HasFDerivAt (MarginalCost.logRmcGap T vh uc Ybar) D (L 0) := by
    rw [map_zero]; exact hD
  have hH := hD'.comp (0 : ℝ × (ℝ × F)) L.hasFDerivAt
  have hdiag := MarginalCost.fderiv_logRmcGap T vh uc hY hvhh hd2f hucc hvhd hucd hvh huc 1 1 0 0
  rw [show ((0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : F)) = 0 from rfl, map_zero] at hdiag
  have hκ' : (D.comp L) (1, 0) ≠ 0 := by
    have : (D.comp L) (1, 0) = D (1, 1, 0, 0) := rfl
    rw [this, hdiag]
    simpa using hκ
  have hrootH : ∀ᶠ z in 𝓝 (0 : ℝ × F),
      (MarginalCost.logRmcGap T vh uc Ybar ∘ L) (n z, z)
        = (MarginalCost.logRmcGap T vh uc Ybar ∘ L) 0 := by
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [Function.comp_apply, map_zero, hG0]
    exact hroot z
  have hn := implicit_hasFDerivAt hH hκ' hncont hn0 hrootH
  refine ⟨_, hn, fun x X a ξ => ?_⟩
  exact MarginalCost.eq_1_15 T vh uc hY hvhh hd2f hucc hvhd hucd hvh huc hn hn0
    (Filter.Eventually.of_forall hroot) x X a ξ

end Woodford.NominalRigidities.FlexiblePrices
