/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.Determinacy
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Complex.Basic

/-!
# Root location for real quadratics and cubics (Woodford, Appendix C.1)

Woodford (2003), *Interest and Prices*, Appendix C.1, pp. 670–676: Propositions C.1 and C.2,
the root-location criteria behind every determinacy result of Chapter 4, §2.2.

## Proposition C.1 (pp. 670–672)

For `P(λ) = λ² − Tλ + D` (`T = tr A`, `D = det A`) both roots lie strictly outside the unit
circle (`BothOutside`) if and only if Case I (`1 < D`, `D − T > −1`, `D + T > −1`) or Case II
(`D − T < −1`, `D + T < −1`) holds (`bothOutside_iff_cases`), equivalently
`1 < |D| ∧ |T| < |1 + D|` (`bothOutside_iff_abs`), equivalently the roots of the reciprocal
polynomial are inside (`bothOutside_iff_schurStable_inv`). The equivalence is exact: no boundary
case has to be excluded.

* Survey gap **E24** (p. 671): in the real-root case, (C.7) and (C.8) alone do not force both
  roots below `−1` or both above `1` — both roots may lie in `(−1, 1)`
  (`e24_printed_step_fails`); (C.6) is needed (`e24_corrected_step`).

## Proposition C.2 (pp. 672–676)

For `P(λ) = λ³ + A₂λ² + A₁λ + A₀`, "exactly one root in the open unit disc and two outside the
closed disc" (`OneInTwoOut`, with multiplicity, via a complex factorisation) is characterised
in `oneInTwoOut_iff_cases`:

* Case I: `P(1) < 0 < P(−1)` (C.11)–(C.12);
* Case II: `P(−1) < 0 < P(1)` and `A₀² − A₀A₂ + A₁ − 1 > 0` (C.13)–(C.15);
* Case III′: `P(−1) < 0 < P(1)` and `|A₂| > 3` (C.13), (C.14), (C.17) — **without** (C.16).

The key identity `A₀² − A₀A₂ + A₁ − 1 = (λ₁λ₂ − 1)(λ₁λ₃ − 1)(λ₂λ₃ − 1)` is `C15_eq_prod`; its
real form through the stable root `μ` is `C15_eq_of_realSplit`.

The proof is complete and covers every root configuration (three real roots, or one real root
and a complex pair) without a case enumeration: the root inside is real
(`real_of_factors`), splitting it off leaves a real quadratic, and Prop C.1 is applied to it.

**Boundary cases (honest strictness).** With Case III exactly as printed (including (C.16)
`A₀² − A₀A₂ + A₁ − 1 < 0`) the conditions are sufficient (`oneInTwoOut_of_printed_cases`) but
*not* necessary: when a product of roots equals one, a determinate configuration satisfies none
of the printed cases (`printed_C2_not_necessary`, roots `−2, −3, −1/2`). They are necessary
whenever `A₀² − A₀A₂ + A₁ − 1 ≠ 0` (`printed_cases_of_oneInTwoOut`), the book's "generic"
qualification (fn. 2). Dropping (C.16), as footnote 3 says is possible, gives the exact
equivalence.

* **E25** (p. 673, twice): the printed claims "(C.11) and (C.12) imply `P(1) > 0` and
  `P(−1) < 0`" and "(C.13) and (C.14) imply `P(1) < 0` and `P(−1) > 0`" have the signs swapped
  (`e25_caseI_signs`, `e25_caseII_signs`); with the printed signs the IVT argument does not give
  three real roots (`e25_printed_signs_one_real_root`, the cubic `λ³ + λ`).
* **E26** (p. 675, (b2)): "`λ₁ + λ₂ + λ₃ < λ₃ + λ₃⁻¹ − 1 < 3`" must read `< −3`
  (`e26_b2_sum_lt`); the printed bound cannot deliver (C.17) (`e26_printed_bound_too_weak`).
-/

namespace Woodford.NeoWicksellianFramework.SchurCohn

open ComplexConjugate

/-! ### Proposition C.1 -/

/-- Woodford (2003), Prop. C.1, p. 670: both roots of `λ² − Tλ + D` lie strictly outside the
unit circle. -/
def BothOutside (T D : ℝ) : Prop := 1 < ‖root₁ T D‖ ∧ 1 < ‖root₂ T D‖

/-- Woodford (2003), Prop. C.1, (C.1)–(C.3), p. 670: Case I, `det A > 1`, `det A − tr A > −1`,
`det A + tr A > −1`. -/
def CaseI2 (T D : ℝ) : Prop := 1 < D ∧ -1 < D - T ∧ -1 < D + T

/-- Woodford (2003), Prop. C.1, (C.4)–(C.5), p. 671: Case II, `det A − tr A < −1`,
`det A + tr A < −1`. -/
def CaseII2 (T D : ℝ) : Prop := D - T < -1 ∧ D + T < -1

/-- Woodford (2003), Prop. C.1, proof, p. 671: for two real roots `u, v`, both lie outside the
unit circle iff Case I or Case II holds for `T = u + v`, `D = u v`. -/
theorem real_roots_iff (u v : ℝ) :
    (1 < |u| ∧ 1 < |v|) ↔ CaseI2 (u + v) (u * v) ∨ CaseII2 (u + v) (u * v) := by
  unfold CaseI2 CaseII2
  constructor
  · rintro ⟨hu, hv⟩
    rcases lt_abs.mp hu with hu | hu <;> rcases lt_abs.mp hv with hv | hv
    · left; refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · right; constructor <;> nlinarith
    · right; constructor <;> nlinarith
    · left; refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · have e1 : 0 < (u - 1) * (v - 1) := by nlinarith
      have e2 : 0 < (u + 1) * (v + 1) := by nlinarith
      by_contra hc
      have hc' : |u| ≤ 1 ∨ |v| ≤ 1 := by
        by_contra h
        push Not at h
        exact hc ⟨h.1, h.2⟩
      rcases hc' with hc' | hc'
      · obtain ⟨hl, hr⟩ := abs_le.mp hc'
        rcases eq_or_lt_of_le hr with hr | hr
        · subst hr; nlinarith
        rcases eq_or_lt_of_le hl with hl | hl
        · rw [← hl] at e2; nlinarith
        have hv1 : v < 1 := by nlinarith
        have hv2 : -1 < v := by nlinarith
        nlinarith
      · obtain ⟨hl, hr⟩ := abs_le.mp hc'
        rcases eq_or_lt_of_le hr with hr | hr
        · subst hr; nlinarith
        rcases eq_or_lt_of_le hl with hl | hl
        · rw [← hl] at e2; nlinarith
        have hu1 : u < 1 := by nlinarith
        have hu2 : -1 < u := by nlinarith
        nlinarith
    · have e1 : (u - 1) * (v - 1) < 0 := by nlinarith
      have e2 : (u + 1) * (v + 1) < 0 := by nlinarith
      rcases lt_or_ge 1 u with hu | hu
      · have hv : v < 1 := by nlinarith
        have hv' : v < -1 := by nlinarith
        exact ⟨lt_abs.mpr (Or.inl hu), lt_abs.mpr (Or.inr (by linarith))⟩
      · have hv : 1 < v := by
          rcases eq_or_lt_of_le hu with h | h
          · subst h; nlinarith
          · nlinarith
        have hu' : u < -1 := by nlinarith
        exact ⟨lt_abs.mpr (Or.inr (by linarith)), lt_abs.mpr (Or.inl hv)⟩

/-- **Proposition C.1** (Woodford (2003), p. 670): both roots of the characteristic polynomial
`λ² − Tλ + D` lie strictly outside the unit circle if and only if Case I or Case II holds.
Exact, with no boundary case excluded. -/
theorem bothOutside_iff_cases (T D : ℝ) : BothOutside T D ↔ CaseI2 T D ∨ CaseII2 T D := by
  unfold BothOutside
  by_cases h : 0 ≤ disc T D
  · obtain ⟨h1, h2⟩ := norm_root_of_nonneg h
    rw [h1, h2]
    have hs2 : Real.sqrt (disc T D) ^ 2 = T ^ 2 - 4 * D := by rw [Real.sq_sqrt h]; rfl
    have key := real_roots_iff ((T + Real.sqrt (disc T D)) / 2) ((T - Real.sqrt (disc T D)) / 2)
    have hsum : (T + Real.sqrt (disc T D)) / 2 + (T - Real.sqrt (disc T D)) / 2 = T := by ring
    have hprod : (T + Real.sqrt (disc T D)) / 2 * ((T - Real.sqrt (disc T D)) / 2) = D := by
      nlinarith [hs2]
    rw [hsum, hprod] at key
    exact key
  · have hneg : disc T D < 0 := not_le.mp h
    obtain ⟨h1, h2⟩ := normSq_root_of_neg hneg
    have hd : disc T D = T ^ 2 - 4 * D := rfl
    have hD0 : 0 < D := by nlinarith [sq_nonneg T]
    have n1 := norm_nonneg (root₁ T D)
    have n2 := norm_nonneg (root₂ T D)
    unfold CaseI2 CaseII2
    constructor
    · rintro ⟨r1, -⟩
      have hD1 : 1 < D := by nlinarith
      have hsq : T ^ 2 < (1 + D) ^ 2 := by nlinarith [sq_nonneg (1 - D)]
      have hT : |T| < 1 + D := abs_lt_of_sq_lt_sq hsq (by linarith)
      obtain ⟨hT1, hT2⟩ := abs_lt.mp hT
      left; exact ⟨hD1, by linarith, by linarith⟩
    · rintro (⟨hD1, -, -⟩ | ⟨e1, e2⟩)
      · constructor <;> nlinarith
      · exfalso; linarith

/-- Woodford (2003), Prop. C.1, p. 670 (the clean form, survey §4.1): both roots outside iff
`1 < |D|` and `|T| < |1 + D|`. -/
theorem bothOutside_iff_abs (T D : ℝ) : BothOutside T D ↔ 1 < |D| ∧ |T| < |1 + D| := by
  rw [bothOutside_iff_cases]
  unfold CaseI2 CaseII2
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · rw [abs_of_pos (by linarith : (0 : ℝ) < D), abs_of_pos (by linarith : (0 : ℝ) < 1 + D)]
      exact ⟨h1, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
    · rw [abs_of_neg (by linarith : D < 0), abs_of_neg (by linarith : 1 + D < 0)]
      exact ⟨by linarith, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  · rintro ⟨hD, hT⟩
    obtain ⟨hT1, hT2⟩ := abs_lt.mp hT
    rcases lt_abs.mp hD with hD | hD
    · rw [abs_of_pos (by linarith : (0 : ℝ) < 1 + D)] at hT1 hT2
      left; exact ⟨hD, by linarith, by linarith⟩
    · rw [abs_of_neg (by linarith : 1 + D < 0)] at hT1 hT2
      right; exact ⟨by linarith, by linarith⟩

/-- Woodford (2003), Prop. C.1, p. 670: both roots of `λ² − Tλ + D` outside the unit circle iff
`D ≠ 0` and both roots of the reciprocal polynomial `λ² − (T/D)λ + 1/D` (the eigenvalues of
`A⁻¹`) are inside (the core Schur–Cohn condition). -/
theorem bothOutside_iff_schurStable_inv (T D : ℝ) :
    BothOutside T D ↔ D ≠ 0 ∧ SchurStable (T / D) (1 / D) := by
  rw [bothOutside_iff_abs]
  unfold SchurStable
  constructor
  · rintro ⟨hD, hT⟩
    have hD0 : D ≠ 0 := by
      rintro rfl; norm_num at hD
    refine ⟨hD0, ?_, ?_⟩
    · rw [abs_div, abs_one, div_lt_one (by linarith)]; exact hD
    · rcases lt_abs.mp hD with hD' | hD'
      · rw [abs_of_pos (by linarith : (0 : ℝ) < 1 + D)] at hT
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < D), div_lt_iff₀ (by linarith),
          add_mul, one_div_mul_cancel hD0]
        linarith
      · rw [abs_of_neg (by linarith : 1 + D < 0)] at hT
        rw [abs_div, abs_of_neg (by linarith : D < 0), div_lt_iff₀ (by linarith),
          add_mul, one_mul, one_div, inv_mul_eq_div, neg_div, div_self hD0]
        linarith
  · rintro ⟨hD0, h1, h2⟩
    rw [abs_div, abs_one, div_lt_one (abs_pos.mpr hD0)] at h1
    refine ⟨h1, ?_⟩
    rcases lt_abs.mp h1 with hD' | hD'
    · rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < D), div_lt_iff₀ (by linarith),
        add_mul, one_div_mul_cancel hD0] at h2
      rw [abs_of_pos (by linarith : (0 : ℝ) < 1 + D)]
      linarith
    · rw [abs_div, abs_of_neg (by linarith : D < 0), div_lt_iff₀ (by linarith),
        add_mul, one_mul, one_div, inv_mul_eq_div, neg_div, div_self hD0] at h2
      rw [abs_of_neg (by linarith : 1 + D < 0)]
      linarith

/-- Woodford (2003), Prop. C.1, p. 671: the roots of `λ² − Tλ + D` are exactly `root₁`, `root₂`,
so "both roots outside" is the intrinsic statement "every root has modulus above one". -/
theorem bothOutside_iff_forall (T D : ℝ) :
    BothOutside T D ↔ ∀ z : ℂ, z ^ 2 - T * z + D = 0 → 1 < ‖z‖ := by
  constructor
  · rintro ⟨h1, h2⟩ z hz
    rcases eq_root_of_eq hz with rfl | rfl
    · exact h1
    · exact h2
  · intro h
    exact ⟨h _ (root_eq T D _ (Or.inl rfl)), h _ (root_eq T D _ (Or.inr rfl))⟩

/-- Woodford (2003), Prop. C.1, p. 671: `λ² − Tλ + D = (λ − λ₁)(λ − λ₂)`. -/
theorem quadratic_factor (T D : ℝ) (z : ℂ) :
    z ^ 2 - T * z + D = (z - root₁ T D) * (z - root₂ T D) := by
  have hs := root_sum T D
  have hp := root_prod T D
  linear_combination z * hs - hp

/-- Woodford (2003), Prop. C.1, p. 671: if `λ² − Tλ + D = (λ − p)(λ − q)`, the roots `root₁`,
`root₂` are `p` and `q`. -/
theorem roots_of_factor {T D : ℝ} {p q : ℂ}
    (h : ∀ z : ℂ, z ^ 2 - T * z + D = (z - p) * (z - q)) :
    (root₁ T D = p ∨ root₁ T D = q) ∧ (root₂ T D = p ∨ root₂ T D = q) := by
  have e : ∀ r : ℂ, r ^ 2 - T * r + D = 0 → r = p ∨ r = q := by
    intro r hr
    rw [h r] at hr
    rcases mul_eq_zero.mp hr with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (sub_eq_zero.mp h')
  exact ⟨e _ (root_eq T D _ (Or.inl rfl)), e _ (root_eq T D _ (Or.inr rfl))⟩

/-- Woodford (2003), Prop. C.1, p. 671: if `λ² − Tλ + D = (λ − p)(λ − q)` with `|p|, |q| > 1`,
both roots are outside the unit circle. -/
theorem bothOutside_of_factor {T D : ℝ} {p q : ℂ}
    (h : ∀ z : ℂ, z ^ 2 - T * z + D = (z - p) * (z - q)) (hp : 1 < ‖p‖) (hq : 1 < ‖q‖) :
    BothOutside T D := by
  obtain ⟨h1, h2⟩ := roots_of_factor h
  refine ⟨?_, ?_⟩
  · rcases h1 with e | e <;> rw [e] <;> assumption
  · rcases h2 with e | e <;> rw [e] <;> assumption

/-- Woodford (2003), Prop. C.1, p. 671 (the inside version): if `λ² − Tλ + D = (λ − p)(λ − q)`
with `|p|, |q| < 1`, the Schur–Cohn condition holds. -/
theorem schurStable_of_factor {T D : ℝ} {p q : ℂ}
    (h : ∀ z : ℂ, z ^ 2 - T * z + D = (z - p) * (z - q)) (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    SchurStable T D := by
  obtain ⟨h1, h2⟩ := roots_of_factor h
  rw [schurStable_iff_roots]
  refine ⟨?_, ?_⟩
  · rcases h1 with e | e <;> rw [e] <;> assumption
  · rcases h2 with e | e <;> rw [e] <;> assumption

/-- Woodford (2003), Prop. C.1, p. 671: two real numbers of modulus above one are the roots of a
quadratic with both roots outside the unit circle. -/
theorem bothOutside_of_reals {u v : ℝ} (hu : 1 < |u|) (hv : 1 < |v|) :
    BothOutside (u + v) (u * v) :=
  bothOutside_of_factor (p := u) (q := v) (fun z => by push_cast; ring)
    (by rwa [Complex.norm_real, Real.norm_eq_abs]) (by rwa [Complex.norm_real, Real.norm_eq_abs])

/-- Woodford (2003), Prop. C.1, p. 671: two real numbers of modulus below one are the roots of a
quadratic satisfying the Schur–Cohn condition. -/
theorem schurStable_of_reals {u v : ℝ} (hu : |u| < 1) (hv : |v| < 1) :
    SchurStable (u + v) (u * v) :=
  schurStable_of_factor (p := u) (q := v) (fun z => by push_cast; ring)
    (by rwa [Complex.norm_real, Real.norm_eq_abs]) (by rwa [Complex.norm_real, Real.norm_eq_abs])

/-- Woodford (2003), proof of Prop. C.1, p. 671, corrected step (survey E24): for real roots,
(C.6) `λ₁λ₂ > 1` together with (C.7) and (C.8) puts both roots below `−1` or both above `1`. -/
theorem e24_corrected_step {u v : ℝ} (h6 : 1 < u * v) (h7 : 0 < (u - 1) * (v - 1))
    (h8 : 0 < (u + 1) * (v + 1)) : (u < -1 ∧ v < -1) ∨ (1 < u ∧ 1 < v) := by
  have hc : CaseI2 (u + v) (u * v) := ⟨h6, by nlinarith, by nlinarith⟩
  obtain ⟨hu, hv⟩ := (real_roots_iff u v).mpr (Or.inl hc)
  rcases lt_abs.mp hu with hu | hu <;> rcases lt_abs.mp hv with hv | hv
  · exact Or.inr ⟨hu, hv⟩
  · nlinarith
  · nlinarith
  · exact Or.inl ⟨by linarith, by linarith⟩

/-- Woodford (2003), proof of Prop. C.1, p. 671 (survey E24, the gap): the printed step "(C.7) and
(C.8) imply both roots are below `−1` or both above `1`" is false — the roots `1/2, 1/2` satisfy
(C.7) and (C.8) but lie inside the unit circle; (C.6) is needed to exclude them. -/
theorem e24_printed_step_fails :
    ∃ u v : ℝ, 0 < (u - 1) * (v - 1) ∧ 0 < (u + 1) * (v + 1) ∧
      ¬ ((u < -1 ∧ v < -1) ∨ (1 < u ∧ 1 < v)) :=
  ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num⟩

/-! ### Proposition C.2: the cubic -/

/-- Woodford (2003), Prop. C.2, p. 672: the characteristic polynomial
`P(λ) = λ³ + A₂λ² + A₁λ + A₀` at a complex point. -/
def cubic (a2 a1 a0 : ℝ) (z : ℂ) : ℂ := z ^ 3 + a2 * z ^ 2 + a1 * z + a0

/-- Woodford (2003), Prop. C.2, p. 672: `P(λ)` at a real point. -/
def cubicR (a2 a1 a0 x : ℝ) : ℝ := x ^ 3 + a2 * x ^ 2 + a1 * x + a0

/-- Woodford (2003), Prop. C.2, p. 674: `P(λ) = (λ − λ₁)(λ − λ₂)(λ − λ₃)`, the roots listed with
multiplicity. -/
def Factors (a2 a1 a0 : ℝ) (l1 l2 l3 : ℂ) : Prop :=
  ∀ z : ℂ, cubic a2 a1 a0 z = (z - l1) * (z - l2) * (z - l3)

/-- Woodford (2003), Prop. C.2, p. 672: exactly one root (with multiplicity) in the open unit disc
and two strictly outside the closed unit disc. -/
def OneInTwoOut (a2 a1 a0 : ℝ) : Prop :=
  ∃ l1 l2 l3 : ℂ, Factors a2 a1 a0 l1 l2 l3 ∧ ‖l1‖ < 1 ∧ 1 < ‖l2‖ ∧ 1 < ‖l3‖

/-- Woodford (2003), Prop. C.2, p. 674: the real factorisation
`P(λ) = (λ − μ)(λ² − Tλ + D)` written through the coefficients. -/
def RealSplit (a2 a1 a0 μ T D : ℝ) : Prop :=
  a2 = -(μ + T) ∧ a1 = D + μ * T ∧ a0 = -(μ * D)

/-- Woodford (2003), (C.11)/(C.13), p. 673: `P(1) = 1 + A₂ + A₁ + A₀`. -/
def P1 (a2 a1 a0 : ℝ) : ℝ := 1 + a2 + a1 + a0

/-- Woodford (2003), (C.12)/(C.14), p. 673: `P(−1) = −1 + A₂ − A₁ + A₀`. -/
def Pm1 (a2 a1 a0 : ℝ) : ℝ := -1 + a2 - a1 + a0

/-- Woodford (2003), (C.15)/(C.16), p. 673: `A₀² − A₀A₂ + A₁ − 1`. -/
def C15 (a2 a1 a0 : ℝ) : ℝ := a0 ^ 2 - a0 * a2 + a1 - 1

/-- Woodford (2003), Prop. C.2, Case I, (C.11)–(C.12), p. 673. -/
def CaseI3 (a2 a1 a0 : ℝ) : Prop := P1 a2 a1 a0 < 0 ∧ 0 < Pm1 a2 a1 a0

/-- Woodford (2003), Prop. C.2, Case II, (C.13)–(C.15), p. 673. -/
def CaseII3 (a2 a1 a0 : ℝ) : Prop :=
  0 < P1 a2 a1 a0 ∧ Pm1 a2 a1 a0 < 0 ∧ 0 < C15 a2 a1 a0

/-- Woodford (2003), Prop. C.2, Case III as printed, (C.13), (C.14), (C.16), (C.17), p. 673. -/
def CaseIII3 (a2 a1 a0 : ℝ) : Prop :=
  0 < P1 a2 a1 a0 ∧ Pm1 a2 a1 a0 < 0 ∧ C15 a2 a1 a0 < 0 ∧ 3 < |a2|

/-- Woodford (2003), Prop. C.2, fn. 3, p. 673: Case III without (C.16), which the footnote says
is only there to make the cases disjoint. -/
def CaseIII3' (a2 a1 a0 : ℝ) : Prop := 0 < P1 a2 a1 a0 ∧ Pm1 a2 a1 a0 < 0 ∧ 3 < |a2|

/-- Woodford (2003), Prop. C.2, p. 674: the cubic at a real point is the real cubic. -/
theorem cubic_ofReal (a2 a1 a0 x : ℝ) : cubic a2 a1 a0 x = (cubicR a2 a1 a0 x : ℂ) := by
  unfold cubic cubicR; push_cast; ring

/-- Woodford (2003), Prop. C.2, p. 674: the cubic has real coefficients, `P(z̄) = conj P(z)`. -/
theorem cubic_conj (a2 a1 a0 : ℝ) (z : ℂ) : cubic a2 a1 a0 (conj z) = conj (cubic a2 a1 a0 z) := by
  unfold cubic; simp [map_add, map_mul, map_pow]

/-- Woodford (2003), (C.11)/(C.13), p. 673: `P(1)` is the cubic at `1`. -/
theorem P1_eq (a2 a1 a0 : ℝ) : P1 a2 a1 a0 = cubicR a2 a1 a0 1 := by unfold P1 cubicR; ring

/-- Woodford (2003), (C.12)/(C.14), p. 673: `P(−1)` is the cubic at `−1`. -/
theorem Pm1_eq (a2 a1 a0 : ℝ) : Pm1 a2 a1 a0 = cubicR a2 a1 a0 (-1) := by
  unfold Pm1 cubicR; ring

/-- Woodford (2003), Prop. C.2, p. 674: the real factorisation `P(x) = (x − μ)(x² − Tx + D)`. -/
theorem cubicR_of_realSplit {a2 a1 a0 μ T D : ℝ} (h : RealSplit a2 a1 a0 μ T D) (x : ℝ) :
    cubicR a2 a1 a0 x = (x - μ) * (x ^ 2 - T * x + D) := by
  obtain ⟨h2, h1, h0⟩ := h
  subst h2 h1 h0
  unfold cubicR; ring

/-- Woodford (2003), Prop. C.2, p. 674: the real factorisation, at complex points. -/
theorem cubic_of_realSplit {a2 a1 a0 μ T D : ℝ} (h : RealSplit a2 a1 a0 μ T D) (z : ℂ) :
    cubic a2 a1 a0 z = (z - μ) * (z ^ 2 - T * z + D) := by
  obtain ⟨h2, h1, h0⟩ := h
  subst h2 h1 h0
  unfold cubic; push_cast; ring

/-- Woodford (2003), Prop. C.2, p. 674: a real factorisation gives a complex factorisation with
roots `μ`, `root₁ T D`, `root₂ T D`. -/
theorem factors_of_realSplit {a2 a1 a0 μ T D : ℝ} (h : RealSplit a2 a1 a0 μ T D) :
    Factors a2 a1 a0 μ (root₁ T D) (root₂ T D) := by
  intro z
  rw [cubic_of_realSplit h, quadratic_factor, mul_assoc]

/-- Woodford (2003), (C.11)/(C.13), p. 673: `P(1) = (1 − μ)(1 − T + D)`. -/
theorem P1_of_realSplit {a2 a1 a0 μ T D : ℝ} (h : RealSplit a2 a1 a0 μ T D) :
    P1 a2 a1 a0 = (1 - μ) * (1 - T + D) := by
  rw [P1_eq, cubicR_of_realSplit h]; ring

/-- Woodford (2003), (C.12)/(C.14), p. 673: `P(−1) = −(1 + μ)(1 + T + D)`. -/
theorem Pm1_of_realSplit {a2 a1 a0 μ T D : ℝ} (h : RealSplit a2 a1 a0 μ T D) :
    Pm1 a2 a1 a0 = -((1 + μ) * (1 + T + D)) := by
  rw [Pm1_eq, cubicR_of_realSplit h]; ring

/-- Woodford (2003), (C.15), p. 674 (real form of the key identity): with the root `μ` split off,
`A₀² − A₀A₂ + A₁ − 1 = (Dμ² − Tμ + 1)(D − 1)`, i.e. `(λ₁λ₂ − 1)(λ₁λ₃ − 1) · (λ₂λ₃ − 1)`. -/
theorem C15_eq_of_realSplit {a2 a1 a0 μ T D : ℝ} (h : RealSplit a2 a1 a0 μ T D) :
    C15 a2 a1 a0 = (D * μ ^ 2 - T * μ + 1) * (D - 1) := by
  obtain ⟨h2, h1, h0⟩ := h
  subst h2 h1 h0
  unfold C15; ring

/-- Woodford (2003), p. 674 (Vieta): `A₀ = −λ₁λ₂λ₃`, `A₁ = λ₁λ₂ + λ₁λ₃ + λ₂λ₃`,
`A₂ = −λ₁ − λ₂ − λ₃`. -/
theorem factors_vieta {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3) :
    (a2 : ℂ) = -(l1 + l2 + l3) ∧ (a1 : ℂ) = l1 * l2 + l1 * l3 + l2 * l3 ∧
      (a0 : ℂ) = -(l1 * l2 * l3) := by
  have e0 := h 0
  have e1 := h 1
  have e2 := h (-1)
  unfold cubic at e0 e1 e2
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (e1 + e2) / 2 - e0
  · linear_combination (e1 - e2) / 2
  · linear_combination e0

/-- **The key identity** (Woodford (2003), (C.15), p. 674):
`A₀² − A₀A₂ + A₁ − 1 = (λ₁λ₂ − 1)(λ₁λ₃ − 1)(λ₂λ₃ − 1)`. -/
theorem C15_eq_prod {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3) :
    (C15 a2 a1 a0 : ℂ) = (l1 * l2 - 1) * (l1 * l3 - 1) * (l2 * l3 - 1) := by
  obtain ⟨h2, h1, h0⟩ := factors_vieta h
  unfold C15
  push_cast
  rw [h2, h1, h0]
  ring

/-- Woodford (2003), (C.11)/(C.13), p. 674: `P(1) = (1 − λ₁)(1 − λ₂)(1 − λ₃)`. -/
theorem P1_eq_prod {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3) :
    (P1 a2 a1 a0 : ℂ) = (1 - l1) * (1 - l2) * (1 - l3) := by
  rw [P1_eq, ← cubic_ofReal]; push_cast; exact h 1

/-- Woodford (2003), (C.12)/(C.14), p. 674: `P(−1) = −(1 + λ₁)(1 + λ₂)(1 + λ₃)`. -/
theorem Pm1_eq_prod {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3) :
    (Pm1 a2 a1 a0 : ℂ) = -((1 + l1) * (1 + l2) * (1 + l3)) := by
  rw [Pm1_eq, ← cubic_ofReal]; push_cast; rw [h (-1)]; ring

/-- Woodford (2003), Prop. C.2, p. 673: a real root splits off a real quadratic factor. -/
theorem realSplit_of_root {a2 a1 a0 μ : ℝ} (h : cubicR a2 a1 a0 μ = 0) :
    RealSplit a2 a1 a0 μ (-(a2 + μ)) (a1 + μ * a2 + μ ^ 2) := by
  unfold cubicR at h
  refine ⟨by ring, by ring, by linear_combination h⟩

/-- Woodford (2003), Prop. C.2, p. 673 ("the `λ³` term dominates"): a real cubic has a real root
(intermediate value theorem on `[−M, M]`, `M = 1 + |A₂| + |A₁| + |A₀|`). -/
theorem exists_real_root (a2 a1 a0 : ℝ) : ∃ r : ℝ, cubicR a2 a1 a0 r = 0 := by
  set M : ℝ := 1 + |a2| + |a1| + |a0| with hM
  have hM1 : 1 ≤ M := by
    have := abs_nonneg a2; have := abs_nonneg a1; have := abs_nonneg a0; linarith
  have hM0 : 0 < M := by linarith
  have hb2 := neg_abs_le a2
  have hb1 := neg_abs_le a1
  have hb0 := neg_abs_le a0
  have hc2 := le_abs_self a2
  have hc1 := le_abs_self a1
  have hc0 := le_abs_self a0
  have hMM : M ≤ M ^ 2 := by nlinarith
  have hpos : 0 < cubicR a2 a1 a0 M := by
    unfold cubicR
    have e1 : -|a2| * M ^ 2 ≤ a2 * M ^ 2 := by nlinarith [sq_nonneg M]
    have e2 : -|a1| * M ^ 2 ≤ a1 * M := by nlinarith [abs_nonneg a1]
    have e3 : -|a0| * M ^ 2 ≤ a0 := by nlinarith [abs_nonneg a0]
    have e4 : M ^ 3 = M ^ 2 * (1 + |a2| + |a1| + |a0|) := by rw [← hM]; ring
    nlinarith [sq_nonneg M]
  have hneg : cubicR a2 a1 a0 (-M) < 0 := by
    unfold cubicR
    have e1 : a2 * (-M) ^ 2 ≤ |a2| * M ^ 2 := by nlinarith [sq_nonneg M]
    have e2 : a1 * (-M) ≤ |a1| * M ^ 2 := by nlinarith [abs_nonneg a1]
    have e3 : a0 ≤ |a0| * M ^ 2 := by nlinarith [abs_nonneg a0]
    have e4 : M ^ 3 = M ^ 2 * (1 + |a2| + |a1| + |a0|) := by rw [← hM]; ring
    nlinarith [sq_nonneg M]
  have hcont : ContinuousOn (cubicR a2 a1 a0) (Set.Icc (-M) M) := by
    unfold cubicR; fun_prop
  obtain ⟨r, -, hr⟩ := intermediate_value_Icc (by linarith) hcont ⟨hneg.le, hpos.le⟩
  exact ⟨r, hr⟩

/-- Woodford (2003), Prop. C.2, p. 674: every real cubic splits as `(λ − r)(λ² − Tλ + D)` with
`r, T, D` real (hence, by `factors_of_realSplit`, into three linear factors over `ℂ`). -/
theorem exists_realSplit (a2 a1 a0 : ℝ) : ∃ r T D : ℝ, RealSplit a2 a1 a0 r T D := by
  obtain ⟨r, hr⟩ := exists_real_root a2 a1 a0
  exact ⟨r, _, _, realSplit_of_root hr⟩

/-- Woodford (2003), Prop. C.2, p. 674: a root in the open unit disc, when the other two roots
are outside the closed disc, is real (the conjugate of a root is a root). -/
theorem real_of_factors {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3)
    (h1 : ‖l1‖ < 1) (h2 : 1 < ‖l2‖) (h3 : 1 < ‖l3‖) : ((l1.re : ℝ) : ℂ) = l1 := by
  have hz : cubic a2 a1 a0 l1 = 0 := by rw [h l1]; ring
  have hc : cubic a2 a1 a0 (conj l1) = 0 := by rw [cubic_conj, hz, map_zero]
  rw [h (conj l1)] at hc
  rcases mul_eq_zero.mp hc with hc | hc
  · rcases mul_eq_zero.mp hc with hc | hc
    · exact Complex.conj_eq_iff_re.mp (sub_eq_zero.mp hc)
    · exfalso
      have : ‖conj l1‖ = ‖l2‖ := by rw [sub_eq_zero.mp hc]
      rw [Complex.norm_conj] at this
      linarith
  · exfalso
    have : ‖conj l1‖ = ‖l3‖ := by rw [sub_eq_zero.mp hc]
    rw [Complex.norm_conj] at this
    linarith

/-- Woodford (2003), Prop. C.2, p. 674: "one root inside, two outside" in real terms — a real root
`|μ| < 1` splits off a quadratic factor with both roots outside the unit circle. -/
theorem oneInTwoOut_iff_real (a2 a1 a0 : ℝ) :
    OneInTwoOut a2 a1 a0 ↔ ∃ μ T D : ℝ, |μ| < 1 ∧ BothOutside T D ∧ RealSplit a2 a1 a0 μ T D := by
  constructor
  · rintro ⟨l1, l2, l3, h, h1, h2, h3⟩
    have hre := real_of_factors h h1 h2 h3
    set μ := l1.re with hμ
    have hμ1 : |μ| < 1 := by rwa [← hre, Complex.norm_real, Real.norm_eq_abs] at h1
    have hroot : cubicR a2 a1 a0 μ = 0 := by
      have e := h μ
      rw [hre, sub_self, zero_mul, zero_mul, ← hre, cubic_ofReal] at e
      exact_mod_cast e
    have hs := realSplit_of_root hroot
    refine ⟨μ, _, _, hμ1, ?_, hs⟩
    obtain ⟨v2, v1, -⟩ := factors_vieta h
    refine bothOutside_of_factor (p := l2) (q := l3) (fun z => ?_) h2 h3
    push_cast
    rw [v2, v1, hre]
    ring
  · rintro ⟨μ, T, D, hμ, hT, hs⟩
    refine ⟨μ, root₁ T D, root₂ T D, factors_of_realSplit hs, ?_, hT.1, hT.2⟩
    rwa [Complex.norm_real, Real.norm_eq_abs]

/-- Woodford (2003), proof of Prop. C.2, p. 674 (Case II, the step "all three inside contradicts
(C.15)", in real form): if `|μ| < 1`, `D ≤ 1` and `|T| < 1 + D` then `Dμ² − Tμ + 1 > 0`. -/
theorem key_pos {μ T D : ℝ} (hμ : |μ| < 1) (hD : D ≤ 1) (hT : |T| < 1 + D) :
    0 < D * μ ^ 2 - T * μ + 1 := by
  have hm0 := abs_nonneg μ
  have hTm : T * μ ≤ |T| * |μ| := by rw [← abs_mul]; exact le_abs_self _
  have hTm' : |T| * |μ| ≤ (1 + D) * |μ| := mul_le_mul_of_nonneg_right hT.le hm0
  have hsq : μ ^ 2 = |μ| ^ 2 := (sq_abs μ).symm
  have hDm : D * |μ| < 1 := by
    rcases le_or_gt D 0 with h | h
    · nlinarith
    · nlinarith
  nlinarith

/-- Woodford (2003), proof of Prop. C.2, (b2), pp. 675–676, in real form: if `|μ| < 1`, `D > 1`,
`|T| < 1 + D` and `Dμ² − Tμ + 1 ≤ 0`, then `|μ + T| > 3`, i.e. (C.17). -/
theorem three_lt_of_key_nonpos {μ T D : ℝ} (hμ : |μ| < 1) (hD : 1 < D) (hT : |T| < 1 + D)
    (hk : D * μ ^ 2 - T * μ + 1 ≤ 0) : 3 < |μ + T| := by
  obtain ⟨hT1, hT2⟩ := abs_lt.mp hT
  obtain ⟨hm1, hm2⟩ := abs_lt.mp hμ
  rcases lt_trichotomy μ 0 with h | h | h
  · -- `μ < 0`, then `T < 0`
    have hT0 : T < 0 := by nlinarith
    rw [abs_of_neg (by linarith : μ + T < 0)]
    have hDm : 1 < D * (-μ) := by nlinarith
    nlinarith
  · subst h; nlinarith
  · have hT0 : 0 < T := by nlinarith
    rw [abs_of_pos (by linarith : 0 < μ + T)]
    have hDm : 1 < D * μ := by nlinarith
    nlinarith

/-- **Proposition C.2, sufficiency** (Woodford (2003), pp. 673–675): Case I, Case II, or Case III
without (C.16) implies exactly one root inside and two outside the unit circle. The root
`μ ∈ (−1, 1)` comes from the intermediate value theorem; Prop. C.1 locates the other two. -/
theorem oneInTwoOut_of_cases {a2 a1 a0 : ℝ}
    (h : CaseI3 a2 a1 a0 ∨ CaseII3 a2 a1 a0 ∨ CaseIII3' a2 a1 a0) : OneInTwoOut a2 a1 a0 := by
  have hcont : ContinuousOn (cubicR a2 a1 a0) (Set.Icc (-1) 1) := by
    unfold cubicR; fun_prop
  -- a root in `[−1, 1]`
  obtain ⟨μ, hμI, hμ⟩ : ∃ μ ∈ Set.Icc (-1 : ℝ) 1, cubicR a2 a1 a0 μ = 0 := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · rw [P1_eq] at h1; rw [Pm1_eq] at h2
      exact intermediate_value_Icc' (by norm_num) hcont ⟨h1.le, h2.le⟩
    · rw [P1_eq] at h1; rw [Pm1_eq] at h2
      exact intermediate_value_Icc (by norm_num) hcont ⟨h2.le, h1.le⟩
    · rw [P1_eq] at h1; rw [Pm1_eq] at h2
      exact intermediate_value_Icc (by norm_num) hcont ⟨h2.le, h1.le⟩
  have hs := realSplit_of_root hμ
  set T := -(a2 + μ) with hT
  set D := a1 + μ * a2 + μ ^ 2 with hD
  have hp1 := P1_of_realSplit hs
  have hpm := Pm1_of_realSplit hs
  have hc := C15_eq_of_realSplit hs
  have hne1 : μ ≠ 1 := by
    rintro rfl
    have e : P1 a2 a1 a0 = 0 := by rw [P1_eq]; exact hμ
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith
  have hne2 : μ ≠ -1 := by
    rintro rfl
    have e : Pm1 a2 a1 a0 = 0 := by rw [Pm1_eq]; exact hμ
    rcases h with ⟨-, h1⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> linarith
  have hμ1 : |μ| < 1 := abs_lt.mpr ⟨lt_of_le_of_ne hμI.1 (Ne.symm hne2),
    lt_of_le_of_ne hμI.2 hne1⟩
  obtain ⟨hl, hr⟩ := abs_lt.mp hμ1
  refine (oneInTwoOut_iff_real a2 a1 a0).mpr ⟨μ, T, D, hμ1, ?_, hs⟩
  rw [bothOutside_iff_cases]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · -- Case I: `q(1) < 0`, `q(−1) < 0`, so Case II of Prop. C.1
    right
    rw [hp1] at h1; rw [hpm] at h2
    have e1 : 1 - T + D < 0 := by
      by_contra hc'; push Not at hc'; nlinarith
    have e2 : 1 + T + D < 0 := by
      by_contra hc'; push Not at hc'; nlinarith
    exact ⟨by linarith, by linarith⟩
  · -- Case II
    left
    rw [hp1] at h1; rw [hpm] at h2
    have e1 : 0 < 1 - T + D := by
      by_contra hc'; push Not at hc'; nlinarith
    have e2 : 0 < 1 + T + D := by
      by_contra hc'; push Not at hc'; nlinarith
    refine ⟨?_, by linarith, by linarith⟩
    by_contra hD1
    push Not at hD1
    have hk := key_pos (T := T) hμ1 hD1 (abs_lt.mpr ⟨by linarith, by linarith⟩)
    rw [hc] at h3
    nlinarith
  · -- Case III′
    left
    rw [hp1] at h1; rw [hpm] at h2
    have e1 : 0 < 1 - T + D := by
      by_contra hc'; push Not at hc'; nlinarith
    have e2 : 0 < 1 + T + D := by
      by_contra hc'; push Not at hc'; nlinarith
    refine ⟨?_, by linarith, by linarith⟩
    by_contra hD1
    push Not at hD1
    have ha2 : a2 = -(μ + T) := hs.1
    rw [ha2, abs_neg] at h3
    have : |μ + T| < 3 := by
      rw [abs_lt]; constructor <;> linarith
    linarith

/-- **Proposition C.2, necessity** (Woodford (2003), pp. 675–676), in exact form: one root inside
and two outside implies Case I, Case II, or Case III without (C.16). Covers three real roots and
a real root with a complex pair alike. -/
theorem cases_of_oneInTwoOut {a2 a1 a0 : ℝ} (h : OneInTwoOut a2 a1 a0) :
    CaseI3 a2 a1 a0 ∨ CaseII3 a2 a1 a0 ∨ CaseIII3' a2 a1 a0 := by
  obtain ⟨μ, T, D, hμ, hTD, hs⟩ := (oneInTwoOut_iff_real a2 a1 a0).mp h
  obtain ⟨hl, hr⟩ := abs_lt.mp hμ
  have hp1 := P1_of_realSplit hs
  have hpm := Pm1_of_realSplit hs
  have hc := C15_eq_of_realSplit hs
  rcases (bothOutside_iff_cases T D).mp hTD with ⟨hD, e1, e2⟩ | ⟨e1, e2⟩
  · have q1 : 0 < P1 a2 a1 a0 := by rw [hp1]; nlinarith
    have q2 : Pm1 a2 a1 a0 < 0 := by rw [hpm]; nlinarith
    by_cases hk : 0 < D * μ ^ 2 - T * μ + 1
    · right; left
      refine ⟨q1, q2, ?_⟩
      rw [hc]; nlinarith
    · right; right
      push Not at hk
      refine ⟨q1, q2, ?_⟩
      rw [hs.1, abs_neg]
      exact three_lt_of_key_nonpos (T := T) hμ hD (abs_lt.mpr ⟨by linarith, by linarith⟩) hk
  · left
    constructor
    · rw [hp1]; nlinarith
    · rw [hpm]; nlinarith

/-- **Proposition C.2** (Woodford (2003), pp. 672–676), exact form: exactly one root inside and
two outside the unit circle iff Case I, Case II, or Case III without (C.16). -/
theorem oneInTwoOut_iff_cases (a2 a1 a0 : ℝ) :
    OneInTwoOut a2 a1 a0 ↔ CaseI3 a2 a1 a0 ∨ CaseII3 a2 a1 a0 ∨ CaseIII3' a2 a1 a0 :=
  ⟨cases_of_oneInTwoOut, oneInTwoOut_of_cases⟩

/-- Woodford (2003), Prop. C.2, p. 673, sufficiency of the printed cases (Case III with (C.16)). -/
theorem oneInTwoOut_of_printed_cases {a2 a1 a0 : ℝ}
    (h : CaseI3 a2 a1 a0 ∨ CaseII3 a2 a1 a0 ∨ CaseIII3 a2 a1 a0) : OneInTwoOut a2 a1 a0 := by
  rcases h with h | h | ⟨h1, h2, -, h4⟩
  · exact oneInTwoOut_of_cases (Or.inl h)
  · exact oneInTwoOut_of_cases (Or.inr (Or.inl h))
  · exact oneInTwoOut_of_cases (Or.inr (Or.inr ⟨h1, h2, h4⟩))

/-- Woodford (2003), Prop. C.2, pp. 675–676 and fn. 2 (generic necessity of the printed cases):
if `A₀² − A₀A₂ + A₁ − 1 ≠ 0` (no product of two roots equals one), one root inside and two
outside implies one of the three printed cases. -/
theorem printed_cases_of_oneInTwoOut {a2 a1 a0 : ℝ} (h : OneInTwoOut a2 a1 a0)
    (hg : C15 a2 a1 a0 ≠ 0) : CaseI3 a2 a1 a0 ∨ CaseII3 a2 a1 a0 ∨ CaseIII3 a2 a1 a0 := by
  rcases cases_of_oneInTwoOut h with h | h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases lt_or_gt_of_ne hg with hc | hc
    · exact Or.inr (Or.inr ⟨h1, h2, hc, h3⟩)
    · exact Or.inr (Or.inl ⟨h1, h2, hc⟩)

/-- Woodford (2003), Prop. C.2, p. 673 (the printed cases are not necessary at the boundary
`A₀² − A₀A₂ + A₁ − 1 = 0`): `P(λ) = (λ + 1/2)(λ + 2)(λ + 3)` has one root inside and two outside,
but satisfies none of Cases I, II, III as printed (`λ₁λ₃ = 1` makes (C.15) and (C.16) both fail).
-/
theorem printed_C2_not_necessary :
    OneInTwoOut (11 / 2) (17 / 2) 3 ∧
      ¬ (CaseI3 (11 / 2) (17 / 2) 3 ∨ CaseII3 (11 / 2) (17 / 2) 3 ∨ CaseIII3 (11 / 2) (17 / 2) 3)
    := by
  refine ⟨(oneInTwoOut_iff_real _ _ _).mpr ⟨-1 / 2, -5, 6, by norm_num [abs_of_neg], ?_, ?_⟩, ?_⟩
  · rw [bothOutside_iff_cases]; left; unfold CaseI2; norm_num
  · unfold RealSplit; norm_num
  · unfold CaseI3 CaseII3 CaseIII3 P1 Pm1 C15; norm_num

/-- Woodford (2003), proof of Prop. C.2, p. 673 (survey E25, first instance): (C.11) and (C.12)
say `P(1) < 0` and `P(−1) > 0`; the printed "imply that `P(1) > 0` and `P(−1) < 0`" is false
for every coefficient vector in Case I. -/
theorem e25_caseI_signs {a2 a1 a0 : ℝ} (h : CaseI3 a2 a1 a0) :
    cubicR a2 a1 a0 1 < 0 ∧ 0 < cubicR a2 a1 a0 (-1) ∧
      ¬ (0 < cubicR a2 a1 a0 1 ∧ cubicR a2 a1 a0 (-1) < 0) := by
  rw [← P1_eq, ← Pm1_eq]
  exact ⟨h.1, h.2, fun h' => by linarith [h.1, h'.1]⟩

/-- Woodford (2003), proof of Prop. C.2, p. 673 (survey E25, second instance): (C.13) and (C.14)
say `P(1) > 0` and `P(−1) < 0`; the printed "imply that `P(1) < 0` and `P(−1) > 0`" is false. -/
theorem e25_caseII_signs {a2 a1 a0 : ℝ} (h1 : 0 < P1 a2 a1 a0) (h2 : Pm1 a2 a1 a0 < 0) :
    0 < cubicR a2 a1 a0 1 ∧ cubicR a2 a1 a0 (-1) < 0 ∧
      ¬ (cubicR a2 a1 a0 1 < 0 ∧ 0 < cubicR a2 a1 a0 (-1)) := by
  rw [← P1_eq, ← Pm1_eq]
  exact ⟨h1, h2, fun h' => by linarith [h'.1]⟩

/-- Woodford (2003), proof of Prop. C.2, p. 673 (survey E25): with the printed signs
`P(1) > 0`, `P(−1) < 0` the intermediate-value argument for three real roots fails — `λ³ + λ`
has these signs and only one real root. -/
theorem e25_printed_signs_one_real_root :
    0 < cubicR 0 1 0 1 ∧ cubicR 0 1 0 (-1) < 0 ∧ ∀ x : ℝ, cubicR 0 1 0 x = 0 → x = 0 := by
  refine ⟨by norm_num [cubicR], by norm_num [cubicR], fun x hx => ?_⟩
  unfold cubicR at hx
  have : x * (x ^ 2 + 1) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · nlinarith [sq_nonneg x]

/-- Woodford (2003), proof of Prop. C.2, (b2), p. 675 (survey E26, corrected): if
`λ₁ < λ₃⁻¹ < λ₂ < −1 < λ₃ < 0`, then `λ₁ + λ₂ + λ₃ < λ₃ + λ₃⁻¹ − 1 < −3`, so (C.17) holds. -/
theorem e26_b2_sum_lt {l1 l2 l3 : ℝ} (h1 : l1 < l3⁻¹) (h2 : l2 < -1) (h3 : -1 < l3)
    (h4 : l3 < 0) : l1 + l2 + l3 < l3 + l3⁻¹ - 1 ∧ l3 + l3⁻¹ - 1 < -3 := by
  refine ⟨by linarith, ?_⟩
  have hinv : l3⁻¹ * l3 = 1 := inv_mul_cancel₀ h4.ne
  have hi : l3⁻¹ < 0 := inv_lt_zero.mpr h4
  nlinarith

/-- Woodford (2003), proof of Prop. C.2, (b2), p. 675 (survey E26): the printed final bound
"`< 3`" cannot give (C.17) `|A₂| > 3`; a sum below `3` need not exceed `3` in modulus. -/
theorem e26_printed_bound_too_weak : ¬ ∀ s : ℝ, s < 3 → 3 < |s| := by
  intro h
  have := h 0 (by norm_num)
  norm_num at this

end Woodford.NeoWicksellianFramework.SchurCohn
