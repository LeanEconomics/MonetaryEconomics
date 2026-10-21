/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Order.Field

/-!
# The characteristic polynomial `βλ² − (1 + β + c)λ + 1`

Woodford (2003), *Interest and Prices*, Chapter 3, §2.1, Proposition 3.4, eqs. (2.10)–(2.11),
p. 182, footnote 41, p. 186, and Appendix B.3, eqs. (B.11)–(B.14), pp. 659–661 (the same
polynomial recurs in Propositions 3.6 and 3.7, App. B.5–B.6, with `c = κ`).

For `β > 0` and `c > 0` the polynomial `P(λ) = βλ² − (1 + β + c)λ + 1` has two real roots
`λ₁ < λ₂`, given explicitly through the discriminant `(1 + β + c)² − 4β > 0`. This module proves
everything the book (and the other Chapter 3 propositions) use about them:

* `charPoly_factor`, `lam1_add_lam2`, `lam1_mul_lam2` (footnote 41: `λ₁λ₂ = β⁻¹`),
  `charPoly_eq_zero_iff`: factorisation and Vieta;
* `lagPoly_factor`: the lag polynomial `A(L) = L² − (1 + β + c)L + β = β(1 − λ₁L)(1 − λ₂L)`
  of (B.13);
* `charPoly_zero`, `charPoly_one`, `charPoly_inv`, `root_location`: `P(0) > 0`, `P(1) = −c`,
  `P(β⁻¹) = −c/β`, hence `0 < λ₁ < 1 < β⁻¹ < λ₂` for `0 < β < 1` (Prop. 3.4);
* `lam1_strictAntiOn`, `lam2_strictMonoOn`: `λ₁` falls and `λ₂` rises with `c`;
* `tendsto_lam1_zero`, `tendsto_lam2_zero`, `tendsto_lam1_atTop`, `tendsto_lam2_atTop`,
  `tendsto_inv_lam2_atTop`: `λ₁ → 1`, `λ₂ → β⁻¹` as `c → 0⁺`, and `λ₁ → 0`, `λ₂⁻¹ → 0`
  as `c → ∞` (the flexible-price limit `ξ → ∞`, p. 183);
* `one_sub_mul_one_sub_inv` (App. B.3, p. 660): `(1 − λ₁)(1 − λ₂⁻¹) = cλ₁ = c/(βλ₂)`;
  survey error E5: the printed `(1 − λ₁)(1 − λ₂)` is negative (`printed_E5_neg`,
  `printed_E5_ne`), and the concrete instance `β = 1/2`, `c = 3/4`, `λ₁ = 1/2`, `λ₂ = 4`
  (`printed_E5_counterexample`);
* the `P(α)` identities: `charPoly_alpha` `P(α) = (1 − α)(1 − αβ) − cα`,
  `calvo_coeff_identity` `(1 + α²β)/α − (1 + β) = (1 − α)(1 − αβ)/α` (B.3), and
  `charPoly_alpha_calvo` `P(α) = (1 − α)(1 − αβ)w/(1 + w)` at `c = (1 − α)(1 − αβ)/(α(1 + w))`;
  the comparison `alpha_lt_lam1_iff`: `α < λ₁ ⟺ c < (1 − α)(1 − αβ)/α`.
-/

namespace Woodford.NominalRigidities.QuadraticRoots

open Filter Topology

/-- Woodford (2003), eq. (2.10), p. 182, and eq. (B.11), p. 659: the characteristic polynomial
`P(λ) = βλ² − (1 + β + c)λ + 1` (with `c = ξ` in Proposition 3.4 and `c = κ` in
Propositions 3.6–3.7). -/
def charPoly (β c x : ℝ) : ℝ := β * x ^ 2 - (1 + β + c) * x + 1

/-- Woodford (2003), App. B.3, p. 659 (after (B.13)): the lag polynomial
`A(L) = L² − (1 + β + c)L + β`. -/
def lagPoly (β c L : ℝ) : ℝ := L ^ 2 - (1 + β + c) * L + β

/-- Woodford (2003), App. B.3, p. 659: the discriminant `(1 + β + c)² − 4β` of `P`. -/
def charDisc (β c : ℝ) : ℝ := (1 + β + c) ^ 2 - 4 * β

/-- Woodford (2003), Prop. 3.4, p. 182: the smaller root
`λ₁ = ((1 + β + c) − √((1 + β + c)² − 4β)) / (2β)` of (2.10). -/
noncomputable def lam1 (β c : ℝ) : ℝ := ((1 + β + c) - Real.sqrt (charDisc β c)) / (2 * β)

/-- Woodford (2003), Prop. 3.4, p. 182: the larger root
`λ₂ = ((1 + β + c) + √((1 + β + c)² − 4β)) / (2β)` of (2.10). -/
noncomputable def lam2 (β c : ℝ) : ℝ := ((1 + β + c) + Real.sqrt (charDisc β c)) / (2 * β)

/-- Woodford (2003), App. B.3, p. 659: for `β > 0` and `c > 0` the discriminant is positive,
`(1 + β + c)² > (1 + β)² ≥ 4β`, so (B.11) has two distinct real roots. -/
theorem charDisc_pos {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : 0 < charDisc β c := by
  unfold charDisc
  nlinarith [sq_nonneg (1 - β)]

/-- Woodford (2003), App. B.3, p. 659: `(√D)² = D` for the positive discriminant. -/
theorem sq_sqrt_charDisc {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    Real.sqrt (charDisc β c) ^ 2 = charDisc β c :=
  Real.sq_sqrt (charDisc_pos hβ hc).le

/-- Woodford (2003), App. B.3, p. 660 (Vieta): `λ₁ + λ₂ = (1 + β + c)/β`. -/
theorem lam1_add_lam2 {β c : ℝ} (hβ : 0 < β) : lam1 β c + lam2 β c = (1 + β + c) / β := by
  unfold lam1 lam2
  field_simp
  ring

/-- Woodford (2003), fn. 41, p. 186, and App. B.3, p. 660 (Vieta): `λ₁λ₂ = β⁻¹`. -/
theorem lam1_mul_lam2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : lam1 β c * lam2 β c = β⁻¹ := by
  have h := sq_sqrt_charDisc hβ hc
  have hm : ((1 + β + c) - Real.sqrt (charDisc β c)) * ((1 + β + c) + Real.sqrt (charDisc β c))
      = 4 * β := by
    unfold charDisc at h ⊢
    linear_combination (-1 : ℝ) * h
  unfold lam1 lam2
  rw [div_mul_div_comm, hm]
  field_simp
  ring

/-- Woodford (2003), App. B.3, p. 659: the factorisation `P(x) = β(x − λ₁)(x − λ₂)`. -/
theorem charPoly_factor {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (x : ℝ) :
    charPoly β c x = β * (x - lam1 β c) * (x - lam2 β c) := by
  have hs := lam1_add_lam2 (c := c) hβ
  have hp := lam1_mul_lam2 hβ hc
  have e : β * (x - lam1 β c) * (x - lam2 β c)
      = β * x ^ 2 - β * (lam1 β c + lam2 β c) * x + β * (lam1 β c * lam2 β c) := by ring
  rw [e, hs, hp, charPoly]
  field_simp

/-- Woodford (2003), eq. (2.10), p. 182: `λ₁` is a root of (2.10). -/
theorem charPoly_lam1 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : charPoly β c (lam1 β c) = 0 := by
  rw [charPoly_factor hβ hc]; ring

/-- Woodford (2003), eq. (2.10), p. 182: `λ₂` is a root of (2.10). -/
theorem charPoly_lam2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : charPoly β c (lam2 β c) = 0 := by
  rw [charPoly_factor hβ hc]; ring

/-- Woodford (2003), eq. (2.10), p. 182: `λ₁` and `λ₂` are the only roots of (2.10). -/
theorem charPoly_eq_zero_iff {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (x : ℝ) :
    charPoly β c x = 0 ↔ x = lam1 β c ∨ x = lam2 β c := by
  rw [charPoly_factor hβ hc, mul_assoc, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  exact ⟨fun h => h.resolve_left hβ.ne', Or.inr⟩

/-- Woodford (2003), Prop. 3.4, p. 182: the two roots are distinct, `λ₁ < λ₂`. -/
theorem lam1_lt_lam2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : lam1 β c < lam2 β c := by
  have h := Real.sqrt_pos.mpr (charDisc_pos hβ hc)
  unfold lam1 lam2
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

/-- Woodford (2003), App. B.3, p. 660, and App. B.5, p. 663 (Vieta, cleared of `β`):
`β(λ₁ + λ₂) = 1 + β + c`. -/
theorem beta_mul_sum {β c : ℝ} (hβ : 0 < β) : β * (lam1 β c + lam2 β c) = 1 + β + c := by
  rw [lam1_add_lam2 hβ]; field_simp

/-- Woodford (2003), App. B.3, p. 660, and App. B.5, p. 663 (Vieta, cleared of `β`):
`βλ₁λ₂ = 1`. -/
theorem beta_mul_prod {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : β * (lam1 β c * lam2 β c) = 1 := by
  rw [lam1_mul_lam2 hβ hc]; field_simp

/-- Woodford (2003), eq. (2.19), p. 190, and App. B.3, p. 659: `P(x) > 0` exactly outside
`[λ₁, λ₂]`. -/
theorem charPoly_pos_iff_outside {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (x : ℝ) :
    0 < charPoly β c x ↔ x < lam1 β c ∨ lam2 β c < x := by
  rw [charPoly_factor hβ hc, mul_assoc, mul_pos_iff_of_pos_left hβ]
  have hlt := lam1_lt_lam2 hβ hc
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith [hc.1, hc.2]
  · rintro (h | h) <;> nlinarith

/-- Woodford (2003), eq. (2.19), p. 190, and App. B.3, p. 659: `P(x) < 0` exactly strictly
between the roots. -/
theorem charPoly_neg_iff {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (x : ℝ) :
    charPoly β c x < 0 ↔ lam1 β c < x ∧ x < lam2 β c := by
  rw [charPoly_factor hβ hc, mul_assoc]
  have hlt := lam1_lt_lam2 hβ hc
  constructor
  · intro h
    have h' : (x - lam1 β c) * (x - lam2 β c) < 0 := by
      by_contra hc; push Not at hc; nlinarith
    by_contra hc
    rcases not_and_or.1 hc with hc | hc <;> push Not at hc <;> nlinarith
  · rintro ⟨h1, h2⟩
    have : (x - lam1 β c) * (x - lam2 β c) < 0 := mul_neg_of_pos_of_neg (by linarith)
      (by linarith)
    nlinarith

/-- Woodford (2003), App. B.3, p. 659: `P(0) = 1 > 0`. -/
theorem charPoly_zero (β c : ℝ) : charPoly β c 0 = 1 := by
  simp [charPoly]

/-- Woodford (2003), App. B.3, p. 659: `P(1) = −c < 0`. -/
theorem charPoly_one (β c : ℝ) : charPoly β c 1 = -c := by
  simp only [charPoly]; ring

/-- Woodford (2003), App. B.3, p. 659: `P(β⁻¹) = −c/β < 0`. -/
theorem charPoly_inv {β : ℝ} (hβ : β ≠ 0) (c : ℝ) : charPoly β c β⁻¹ = -c / β := by
  simp only [charPoly]
  field_simp
  ring

/-- Woodford (2003), App. B.3, p. 659 (the sign argument): if `P(x) < 0` then `x` lies strictly
between the roots, `λ₁ < x < λ₂`. -/
theorem between_roots_of_neg {β c x : ℝ} (hβ : 0 < β) (hc : 0 < c) (hx : charPoly β c x < 0) :
    lam1 β c < x ∧ x < lam2 β c := by
  rw [charPoly_factor hβ hc] at hx
  have h12 := lam1_lt_lam2 hβ hc
  constructor
  · by_contra h
    push Not at h
    have : 0 ≤ β * (x - lam1 β c) * (x - lam2 β c) :=
      mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hβ.le (by linarith))
        (by linarith)
    linarith
  · by_contra h
    push Not at h
    have : 0 ≤ β * (x - lam1 β c) * (x - lam2 β c) :=
      mul_nonneg (mul_nonneg hβ.le (by linarith)) (by linarith)
    linarith

/-- Woodford (2003), App. B.3, p. 659: below the larger root, `P(x) > 0` iff `x < λ₁`. -/
theorem charPoly_pos_iff {β c x : ℝ} (hβ : 0 < β) (hc : 0 < c) (hx : x < lam2 β c) :
    0 < charPoly β c x ↔ x < lam1 β c := by
  rw [charPoly_factor hβ hc]
  have h2 : x - lam2 β c < 0 := by linarith
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have : β * (x - lam1 β c) * (x - lam2 β c) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hβ.le (by linarith)) h2.le
    linarith
  · intro h
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hβ (by linarith)) h2

/-- Woodford (2003), App. B.3, p. 659: below the larger root, `P(x) = 0` iff `x = λ₁`. -/
theorem charPoly_eq_zero_iff_of_lt {β c x : ℝ} (hβ : 0 < β) (hc : 0 < c) (hx : x < lam2 β c) :
    charPoly β c x = 0 ↔ x = lam1 β c := by
  rw [charPoly_eq_zero_iff hβ hc]
  exact ⟨fun h => h.resolve_right hx.ne, Or.inl⟩

/-- Woodford (2003), Prop. 3.4, p. 182: `λ₁ > 0`. -/
theorem lam1_pos {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : 0 < lam1 β c := by
  have h1 := (between_roots_of_neg hβ hc (x := 1) (by rw [charPoly_one]; linarith)).2
  have hp := lam1_mul_lam2 hβ hc
  have hinv : 0 < β⁻¹ := inv_pos.mpr hβ
  by_contra h
  push Not at h
  have : lam1 β c * lam2 β c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by linarith)
  linarith

/-- Woodford (2003), Prop. 3.4, p. 182: `λ₁ < 1`. -/
theorem lam1_lt_one {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : lam1 β c < 1 :=
  (between_roots_of_neg hβ hc (by rw [charPoly_one]; linarith)).1

/-- Woodford (2003), Prop. 3.4, p. 182: `λ₂ > 1`. -/
theorem one_lt_lam2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : 1 < lam2 β c :=
  (between_roots_of_neg hβ hc (by rw [charPoly_one]; linarith)).2

/-- Woodford (2003), Prop. 3.4, p. 182, and App. B.5, p. 663: `λ₁ < 1 < λ₂`. -/
theorem lam1_lt_one_lt_lam2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    lam1 β c < 1 ∧ 1 < lam2 β c :=
  ⟨lam1_lt_one hβ hc, one_lt_lam2 hβ hc⟩

/-- Woodford (2003), Prop. 3.4, p. 182: `λ₂ > β⁻¹`. -/
theorem inv_lt_lam2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : β⁻¹ < lam2 β c := by
  have h : charPoly β c β⁻¹ < 0 := by
    rw [charPoly_inv hβ.ne']
    exact div_neg_of_neg_of_pos (by linarith) hβ
  exact (between_roots_of_neg hβ hc h).2

/-- Woodford (2003), Prop. 3.4, p. 182: `λ₁ < β⁻¹` (`β⁻¹` lies between the roots). -/
theorem lam1_lt_inv {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : lam1 β c < β⁻¹ := by
  have h : charPoly β c β⁻¹ < 0 := by
    rw [charPoly_inv hβ.ne']
    exact div_neg_of_neg_of_pos (by linarith) hβ
  exact (between_roots_of_neg hβ hc h).1

/-- Woodford (2003), Prop. 3.4, p. 182, and App. B.3, p. 659 (**root location**): for
`0 < β < 1` and `c > 0`, `0 < λ₁ < 1 < β⁻¹ < λ₂`. -/
theorem root_location {β c : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hc : 0 < c) :
    0 < lam1 β c ∧ lam1 β c < 1 ∧ 1 < β⁻¹ ∧ β⁻¹ < lam2 β c :=
  ⟨lam1_pos hβ hc, lam1_lt_one hβ hc, one_lt_inv₀ hβ |>.mpr hβ1, inv_lt_lam2 hβ hc⟩

/-- Woodford (2003), App. B.3, p. 660: `λ₂⁻¹ = βλ₁` (from `λ₁λ₂ = β⁻¹`). -/
theorem inv_lam2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : (lam2 β c)⁻¹ = β * lam1 β c := by
  have hp := lam1_mul_lam2 hβ hc
  have h2 : lam2 β c ≠ 0 := (lt_trans one_pos (one_lt_lam2 hβ hc)).ne'
  rw [inv_eq_iff_eq_inv, eq_comm, ← one_div, div_eq_iff (mul_ne_zero hβ.ne'
    (lam1_pos hβ hc).ne')]
  symm
  calc lam2 β c * (β * lam1 β c) = β * (lam1 β c * lam2 β c) := by ring
    _ = 1 := by rw [hp, mul_inv_cancel₀ hβ.ne']

/-- Woodford (2003), App. B.3, p. 660: `0 < λ₂⁻¹ < 1`, so the forward solution of (B.14)
converges. -/
theorem inv_lam2_lt_one {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    0 < (lam2 β c)⁻¹ ∧ (lam2 β c)⁻¹ < 1 :=
  ⟨inv_pos.mpr (lt_trans one_pos (one_lt_lam2 hβ hc)), inv_lt_one_of_one_lt₀ (one_lt_lam2 hβ hc)⟩

/-- Woodford (2003), App. B.3, p. 659 (**the lag-polynomial factorisation**):
`A(L) = L² − (1 + β + c)L + β = β(1 − λ₁L)(1 − λ₂L)`. -/
theorem lagPoly_factor {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (L : ℝ) :
    lagPoly β c L = β * (1 - lam1 β c * L) * (1 - lam2 β c * L) := by
  have hs := lam1_add_lam2 (c := c) hβ
  have hp := lam1_mul_lam2 hβ hc
  have e : β * (1 - lam1 β c * L) * (1 - lam2 β c * L)
      = β - β * (lam1 β c + lam2 β c) * L + β * (lam1 β c * lam2 β c) * L ^ 2 := by ring
  rw [e, hs, hp, lagPoly]
  field_simp
  ring

/-- Woodford (2003), App. B.3, p. 659: `A(L)` is the reciprocal polynomial of `P`,
`A(L) = L² P(1/L)` for `L ≠ 0`. -/
theorem lagPoly_eq_reciprocal (β c : ℝ) {L : ℝ} (hL : L ≠ 0) :
    lagPoly β c L = L ^ 2 * charPoly β c L⁻¹ := by
  simp only [lagPoly, charPoly]
  field_simp
  ring

/-- Woodford (2003), App. B.3, p. 659: the smaller root in rationalised form,
`λ₁ = 2 / ((1 + β + c) + √D)`. -/
theorem lam1_eq_rationalised {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    lam1 β c = 2 / ((1 + β + c) + Real.sqrt (charDisc β c)) := by
  have h := sq_sqrt_charDisc hβ hc
  have hs : 0 ≤ Real.sqrt (charDisc β c) := Real.sqrt_nonneg _
  have hpos : 0 < (1 + β + c) + Real.sqrt (charDisc β c) := by linarith
  unfold lam1
  rw [div_eq_div_iff (by positivity) hpos.ne']
  unfold charDisc at h ⊢
  linear_combination (-1 : ℝ) * h

/-- Woodford (2003), App. B.3: the discriminant and the root sum both rise with `c`, so
`(1 + β + c) + √D` is strictly increasing in `c > 0`. -/
theorem sum_sqrt_strictMonoOn {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun c => (1 + β + c) + Real.sqrt (charDisc β c)) (Set.Ioi 0) := by
  intro c₁ hc₁ c₂ _ h
  simp only [Set.mem_Ioi] at hc₁
  have hD : charDisc β c₁ < charDisc β c₂ := by
    unfold charDisc; nlinarith
  have := Real.sqrt_lt_sqrt (charDisc_pos hβ hc₁).le hD
  simp only
  linarith

/-- Woodford (2003), §2.1 (the smoothing parameter): `λ₁` is strictly decreasing in `c > 0`. -/
theorem lam1_strictAntiOn {β : ℝ} (hβ : 0 < β) :
    StrictAntiOn (fun c => lam1 β c) (Set.Ioi 0) := by
  intro c₁ hc₁ c₂ hc₂ h
  simp only
  rw [lam1_eq_rationalised hβ hc₁, lam1_eq_rationalised hβ hc₂]
  have h1 := sum_sqrt_strictMonoOn hβ hc₁ hc₂ h
  simp only at h1
  have hpos : 0 < (1 + β + c₁) + Real.sqrt (charDisc β c₁) := by
    simp only [Set.mem_Ioi] at hc₁
    linarith [Real.sqrt_nonneg (charDisc β c₁)]
  exact div_lt_div_of_pos_left two_pos hpos h1

/-- Woodford (2003), §2.1: `λ₂` is strictly increasing in `c > 0`. -/
theorem lam2_strictMonoOn {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun c => lam2 β c) (Set.Ioi 0) := by
  intro c₁ hc₁ c₂ hc₂ h
  have h1 := sum_sqrt_strictMonoOn hβ hc₁ hc₂ h
  simp only at h1 ⊢
  unfold lam2
  exact div_lt_div_of_pos_right h1 (by positivity)

/-- Woodford (2003), §2.1: `λ₁` depends continuously on `c` (on all of `ℝ`, with the
explicit formula). -/
theorem continuous_lam1 (β : ℝ) : Continuous fun c => lam1 β c := by
  unfold lam1 charDisc
  fun_prop

/-- Woodford (2003), §2.1: `λ₂` depends continuously on `c`. -/
theorem continuous_lam2 (β : ℝ) : Continuous fun c => lam2 β c := by
  unfold lam2 charDisc
  fun_prop

/-- Woodford (2003), §2.1: at `c = 0`, for `0 < β ≤ 1`, the smaller root is `1`. -/
theorem lam1_at_zero {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) : lam1 β 0 = 1 := by
  have h : charDisc β 0 = (1 - β) ^ 2 := by unfold charDisc; ring
  unfold lam1
  rw [h, Real.sqrt_sq (by linarith)]
  field_simp
  ring

/-- Woodford (2003), §2.1: at `c = 0`, for `0 < β ≤ 1`, the larger root is `β⁻¹`. -/
theorem lam2_at_zero {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) : lam2 β 0 = β⁻¹ := by
  have h : charDisc β 0 = (1 - β) ^ 2 := by unfold charDisc; ring
  unfold lam2
  rw [h, Real.sqrt_sq (by linarith)]
  field_simp
  ring

/-- Woodford (2003), §2.1 (the limit `ξ → 0⁺`, e.g. completely rigid prices `α → 1`):
`λ₁ → 1` as `c → 0⁺` (`0 < β ≤ 1`). -/
theorem tendsto_lam1_zero {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    Tendsto (fun c => lam1 β c) (𝓝[>] 0) (𝓝 1) := by
  have h := (continuous_lam1 β).tendsto 0
  rw [lam1_at_zero hβ hβ1] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- Woodford (2003), §2.1: `λ₂ → β⁻¹` as `c → 0⁺` (`0 < β ≤ 1`). -/
theorem tendsto_lam2_zero {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    Tendsto (fun c => lam2 β c) (𝓝[>] 0) (𝓝 β⁻¹) := by
  have h := (continuous_lam2 β).tendsto 0
  rw [lam2_at_zero hβ hβ1] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- Woodford (2003), p. 183 (the flexible-price limit `ξ → ∞`): `λ₁ → 0` as `c → ∞`. -/
theorem tendsto_lam1_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun c => lam1 β c) atTop (𝓝 0) := by
  have hS : Tendsto (fun c : ℝ => 1 + β + c) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_id
  have hup : Tendsto (fun c : ℝ => 2 / (1 + β + c)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hS
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with c hc
    exact (lam1_pos hβ hc).le
  · filter_upwards [eventually_gt_atTop 0] with c hc
    rw [lam1_eq_rationalised hβ hc]
    exact div_le_div_of_nonneg_left zero_le_two (by linarith)
      (by linarith [Real.sqrt_nonneg (charDisc β c)])

/-- Woodford (2003), p. 183 (the flexible-price limit): `λ₂ → ∞` as `c → ∞`. -/
theorem tendsto_lam2_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun c => lam2 β c) atTop atTop := by
  have hS : Tendsto (fun c : ℝ => (1 + β + c) / (2 * β)) atTop atTop :=
    (tendsto_atTop_add_const_left _ _ tendsto_id).atTop_div_const (by positivity)
  refine tendsto_atTop_mono (fun c => ?_) hS
  unfold lam2
  exact div_le_div_of_nonneg_right (by linarith [Real.sqrt_nonneg (charDisc β c)])
    (by positivity)

/-- Woodford (2003), p. 183 and (2.9): in the flexible-price limit the forward weights vanish,
`λ₂⁻¹ → 0` as `c → ∞`. -/
theorem tendsto_inv_lam2_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun c => (lam2 β c)⁻¹) atTop (𝓝 0) :=
  (tendsto_lam2_atTop hβ).inv_tendsto_atTop

/-- Woodford (2003), App. B.3, p. 660 (corrected; survey error E5): the coefficient of (2.9),
`(1 − λ₁)(1 − λ₂⁻¹) = cλ₁`. -/
theorem one_sub_mul_one_sub_inv {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    (1 - lam1 β c) * (1 - (lam2 β c)⁻¹) = c * lam1 β c := by
  have h := charPoly_lam1 hβ hc
  rw [inv_lam2 hβ hc]
  unfold charPoly at h
  linear_combination h

/-- Woodford (2003), App. B.3, p. 660: `cλ₁ = β⁻¹λ₂⁻¹c`, the coefficient of (B.14). -/
theorem c_mul_lam1 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    c * lam1 β c = β⁻¹ * (lam2 β c)⁻¹ * c := by
  rw [inv_lam2 hβ hc]
  field_simp

/-- Woodford (2003), App. B.3, p. 660: the coefficient `(1 − λ₁)(1 − λ₂⁻¹)` of (2.9) is
positive and less than one. -/
theorem coeff_pos_lt_one {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    0 < (1 - lam1 β c) * (1 - (lam2 β c)⁻¹) ∧ (1 - lam1 β c) * (1 - (lam2 β c)⁻¹) < 1 := by
  have h1 := lam1_pos hβ hc
  have h2 := lam1_lt_one hβ hc
  have ⟨h3, h4⟩ := inv_lam2_lt_one hβ hc
  constructor
  · exact mul_pos (by linarith) (by linarith)
  · nlinarith

/-- Woodford (2003), App. B.3, p. 660, survey error E5: the printed product `(1 − λ₁)(1 − λ₂)`
is negative (because `λ₁ < 1 < λ₂`). -/
theorem printed_E5_neg {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    (1 - lam1 β c) * (1 - lam2 β c) < 0 :=
  mul_neg_of_pos_of_neg (by linarith [lam1_lt_one hβ hc]) (by linarith [one_lt_lam2 hβ hc])

/-- Woodford (2003), App. B.3, p. 660, survey error E5: the printed identity
`(1 − λ₁)(1 − λ₂) = ξλ₁` is false for every `β > 0`, `c > 0`. -/
theorem printed_E5_ne {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    (1 - lam1 β c) * (1 - lam2 β c) ≠ c * lam1 β c := by
  have := printed_E5_neg hβ hc
  have := mul_pos hc (lam1_pos hβ hc)
  intro h
  linarith

/-- Woodford (2003), App. B.3, p. 660, survey error E5: the printed first step
`(1 − λ₁)(1 − λ₂) = (1 − λ₁)(1 − βλ₁)` is false too (`βλ₁ = λ₂⁻¹ ≠ λ₂`). -/
theorem printed_E5_step_ne {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    (1 - lam1 β c) * (1 - lam2 β c) ≠ (1 - lam1 β c) * (1 - β * lam1 β c) := by
  have h := one_sub_mul_one_sub_inv hβ hc
  rw [inv_lam2 hβ hc] at h
  rw [h]
  exact printed_E5_ne hβ hc

/-- Woodford (2003), App. B.3, p. 660, survey error E5 (a concrete instance): with `β = 1/2`,
`c = 3/4` the roots are `λ₁ = 1/2`, `λ₂ = 4`; then `(1 − λ₁)(1 − λ₂⁻¹) = 3/8 = cλ₁`, while the
printed `(1 − λ₁)(1 − λ₂) = −3/2`. -/
theorem printed_E5_counterexample :
    lam1 (1 / 2) (3 / 4) = 1 / 2 ∧ lam2 (1 / 2) (3 / 4) = 4 ∧
      (1 - lam1 (1 / 2) (3 / 4)) * (1 - (lam2 (1 / 2) (3 / 4))⁻¹) = 3 / 8 ∧
      (3 / 4 : ℝ) * lam1 (1 / 2) (3 / 4) = 3 / 8 ∧
      (1 - lam1 (1 / 2) (3 / 4)) * (1 - lam2 (1 / 2) (3 / 4)) = -3 / 2 := by
  have hD : charDisc (1 / 2) (3 / 4) = (7 / 4) ^ 2 := by unfold charDisc; norm_num
  have h1 : lam1 (1 / 2) (3 / 4) = 1 / 2 := by
    unfold lam1; rw [hD, Real.sqrt_sq (by norm_num)]; norm_num
  have h2 : lam2 (1 / 2) (3 / 4) = 4 := by
    unfold lam2; rw [hD, Real.sqrt_sq (by norm_num)]; norm_num
  rw [h1, h2]
  norm_num

/-! ### The `P(α)` identities -/

/-- Woodford (2003), App. B.3 and B.5: `P(α) = (1 − α)(1 − αβ) − cα`. -/
theorem charPoly_alpha (β c α : ℝ) :
    charPoly β c α = (1 - α) * (1 - α * β) - c * α := by
  simp only [charPoly]; ring

/-- Woodford (2003), App. B.3, p. 659 (the coefficient identity behind (B.13)):
`(1 + α²β)/α − (1 + β) = (1 − α)(1 − αβ)/α`. -/
theorem calvo_coeff_identity {α : ℝ} (hα : α ≠ 0) (β : ℝ) :
    (1 + α ^ 2 * β) / α - (1 + β) = (1 - α) * (1 - α * β) / α := by
  field_simp
  ring

/-- Woodford (2003), eq. (2.11), p. 182: the Calvo slope
`ξ = (1 − α)(1 − αβ) / (α(1 + w))`, with `w = ω̃θ`. -/
noncomputable def calvoXi (α β w : ℝ) : ℝ := (1 - α) * (1 - α * β) / (α * (1 + w))

/-- Woodford (2003), eq. (2.11), p. 182: `ξ > 0` for `0 < α < 1`, `β < 1`, `1 + w > 0`. -/
theorem calvoXi_pos {α β w : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1)
    (hw : 0 < 1 + w) : 0 < calvoXi α β w := by
  unfold calvoXi
  have : α * β < 1 := by nlinarith
  exact div_pos (mul_pos (by linarith) (by linarith)) (mul_pos hα0 hw)

/-- Woodford (2003), eq. (2.13), p. 187: the slope `κ = (1 − α)(1 − αβ)ζ/α` of the New
Keynesian Phillips curve (2.12). -/
noncomputable def kappa (α β ζ : ℝ) : ℝ := (1 - α) * (1 - α * β) * ζ / α

/-- Woodford (2003), eq. (2.13), p. 187: `κ > 0` for `0 < α < 1`, `β < 1`, `ζ > 0`. -/
theorem kappa_pos {α β ζ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1) (hζ : 0 < ζ) :
    0 < kappa α β ζ := by
  unfold kappa
  have : α * β < 1 := by nlinarith
  exact div_pos (mul_pos (mul_pos (by linarith) (by linarith)) hζ) hα0

/-- Woodford (2003), App. B.3 (the `P(α)` identity): at `c = ξ` of (2.11),
`P(α) = (1 − α)(1 − αβ) w/(1 + w)`. -/
theorem charPoly_alpha_calvo {α β w : ℝ} (hα : α ≠ 0) (hw : 1 + w ≠ 0) :
    charPoly β (calvoXi α β w) α = (1 - α) * (1 - α * β) * w / (1 + w) := by
  rw [charPoly_alpha]
  unfold calvoXi
  field_simp
  ring

/-- Woodford (2003), §2.3 (persistence comparison): for `0 < α < 1`, `α < λ₁` iff
`c < (1 − α)(1 − αβ)/α`. -/
theorem alpha_lt_lam1_iff {β c α : ℝ} (hβ : 0 < β) (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) :
    α < lam1 β c ↔ c < (1 - α) * (1 - α * β) / α := by
  have hα2 : α < lam2 β c := lt_trans hα1 (one_lt_lam2 hβ hc)
  rw [← charPoly_pos_iff hβ hc hα2, charPoly_alpha, lt_div_iff₀ hα0]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), §2.3: for `0 < α < 1`, `λ₁ = α` iff `c = (1 − α)(1 − αβ)/α`. -/
theorem lam1_eq_alpha_iff {β c α : ℝ} (hβ : 0 < β) (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) :
    lam1 β c = α ↔ c = (1 - α) * (1 - α * β) / α := by
  have hα2 : α < lam2 β c := lt_trans hα1 (one_lt_lam2 hβ hc)
  rw [eq_comm, ← charPoly_eq_zero_iff_of_lt hβ hc hα2, charPoly_alpha, eq_div_iff hα0.ne']
  constructor <;> intro h <;> linarith

/-- Woodford (2003), Prop. 3.4 with `c = ξ` of (2.11): for `0 < α < 1`, `0 < β < 1` and
`1 + w > 0`, `α < λ₁` iff `w > 0` (strategic complementarity `ω̃θ > 0`). -/
theorem alpha_lt_lam1_calvo_iff {α β w : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hw : 0 < 1 + w) : α < lam1 β (calvoXi α β w) ↔ 0 < w := by
  have hc := calvoXi_pos hα0 hα1 hβ1 hw
  have hα2 : α < lam2 β (calvoXi α β w) := lt_trans hα1 (one_lt_lam2 hβ0 hc)
  rw [← charPoly_pos_iff hβ0 hc hα2, charPoly_alpha_calvo hα0.ne' hw.ne']
  have hk : 0 < (1 - α) * (1 - α * β) := mul_pos (by linarith) (by nlinarith)
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have : (1 - α) * (1 - α * β) * w / (1 + w) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hk.le h') hw.le
    linarith
  · intro h
    exact div_pos (mul_pos hk h) hw

/-- Woodford (2003), Prop. 3.4: `αβλ₂ = α/λ₁`, so `αβλ₂ < 1` iff `α < λ₁`. -/
theorem alpha_beta_lam2 {β c α : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    α * β * lam2 β c = α / lam1 β c := by
  have hp := lam1_mul_lam2 hβ hc
  have h1 := (lam1_pos hβ hc).ne'
  rw [eq_div_iff h1]
  calc α * β * lam2 β c * lam1 β c = α * β * (lam1 β c * lam2 β c) := by ring
    _ = α := by rw [hp]; field_simp

end Woodford.NominalRigidities.QuadraticRoots
