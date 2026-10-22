/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.Determinacy
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial

/-!
# Root counts for real polynomials of degree at most two

Cochrane (2023), *The Fiscal Theory of the Price Level*, Ch. 18, eq. (18.2), p. 427, and Online
Appendix A1, §1.9, pp. 573–576 (counting stable roots): the tool for the case
`1 − σφ_{x,1} = 0` of the inertial rule (module TidyR5InertiaSingular), where the generalised
eigenvalue polynomial `det(λM − N)` drops to degree at most two.

**`count_one_iff`**: for `p = aλ² + bλ + c` with real coefficients, `p ≠ 0`, no complex root on
the unit circle and exactly one root (with multiplicity) in the open unit disc iff
`p(1) p(−1) < 0`. The proof splits on the degree: for `a ≠ 0` the two complex roots have real sum
and product, so a root of modulus below one forces both roots to be real (`real_of_sum_prod`),
and conversely `p(1) p(−1) < 0` gives a real root in `(−1, 1)` by the intermediate value theorem
(`exists_root_Ioo`); the linear and constant cases are direct.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5QuadRoots

open Polynomial

/-- Cochrane (2023), A1 §1.9: a real polynomial with `p(1) p(−1) < 0` has a real root in
`(−1, 1)` (intermediate value theorem). -/
theorem exists_root_Ioo {p : ℝ[X]} (h : p.eval 1 * p.eval (-1) < 0) :
    ∃ ρ : ℝ, -1 < ρ ∧ ρ < 1 ∧ p.eval ρ = 0 := by
  have hc : ContinuousOn (fun x => p.eval x) (Set.Icc (-1) 1) :=
    p.continuous.continuousOn
  rcases mul_neg_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨ρ, hρ, e⟩ := intermediate_value_Ioo (by norm_num : (-1 : ℝ) ≤ 1) hc
      (show (0 : ℝ) ∈ Set.Ioo (p.eval (-1)) (p.eval 1) from ⟨h2, h1⟩)
    exact ⟨ρ, hρ.1, hρ.2, e⟩
  · obtain ⟨ρ, hρ, e⟩ := intermediate_value_Ioo' (by norm_num : (-1 : ℝ) ≤ 1) hc
      (show (0 : ℝ) ∈ Set.Ioo (p.eval 1) (p.eval (-1)) from ⟨h1, h2⟩)
    exact ⟨ρ, hρ.1, hρ.2, e⟩

/-- Two complex numbers with real sum and real product, one of them of modulus different from
the other's, are both real. -/
theorem real_of_sum_prod {r1 r2 : ℂ} (hs : (r1 + r2).im = 0) (hp : (r1 * r2).im = 0)
    (hn : ‖r1‖ ≠ ‖r2‖) : r1.im = 0 ∧ r2.im = 0 := by
  simp only [Complex.add_im, Complex.mul_im] at hs hp
  by_contra hc
  have h1 : r1.im ≠ 0 := by
    intro h
    exact hc ⟨h, by linarith⟩
  have h2 : r2.im = -r1.im := by linarith
  rw [h2] at hp
  have h3 : r2.re = r1.re := by
    have : r1.im * (r2.re - r1.re) = 0 := by linear_combination hp
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h1
    · linarith
  apply hn
  rw [← Real.sqrt_sq (norm_nonneg r1), ← Real.sqrt_sq (norm_nonneg r2), Complex.sq_norm,
    Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, h2, h3]
  ring_nf

/-- The count condition for a two-element multiset of roots. -/
theorem count_pair (r1 r2 : ℂ) :
    ((∀ μ ∈ ({r1, r2} : Multiset ℂ), ‖μ‖ ≠ 1) ∧
        Multiset.card (({r1, r2} : Multiset ℂ).filter (fun μ => ‖μ‖ < 1)) = 1) ↔
      (‖r1‖ < 1 ∧ 1 < ‖r2‖) ∨ (‖r2‖ < 1 ∧ 1 < ‖r1‖) := by
  have hc : Multiset.card (({r1, r2} : Multiset ℂ).filter (fun μ => ‖μ‖ < 1)) =
      (if ‖r1‖ < 1 then 1 else 0) + (if ‖r2‖ < 1 then 1 else 0) := by
    rw [show ({r1, r2} : Multiset ℂ) = r1 ::ₘ {r2} from rfl, Multiset.filter_cons,
      Multiset.filter_singleton]
    split_ifs <;> simp
  have hm : (∀ μ ∈ ({r1, r2} : Multiset ℂ), ‖μ‖ ≠ 1) ↔ ‖r1‖ ≠ 1 ∧ ‖r2‖ ≠ 1 := by
    rw [show ({r1, r2} : Multiset ℂ) = r1 ::ₘ {r2} from rfl, Multiset.forall_mem_cons]
    simp
  rw [hc, hm]
  split_ifs with h1 h2 h2
  · constructor
    · rintro ⟨-, h⟩; omega
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> linarith
  · constructor
    · rintro ⟨⟨-, h⟩, -⟩
      exact Or.inl ⟨h1, lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h)⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact ⟨⟨h1.ne, h.ne'⟩, rfl⟩
      · exact absurd h h2
  · constructor
    · rintro ⟨⟨h, -⟩, -⟩
      exact Or.inr ⟨h2, lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h)⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h h1
      · exact ⟨⟨h.ne', h2.ne⟩, rfl⟩
  · constructor
    · rintro ⟨-, h⟩; omega
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact absurd h h1
      · exact absurd h h2

/-- **Root count for degree at most two** (Cochrane (2023), A1 §1.9, pp. 573–576): for
`p = aλ² + bλ + c` with real coefficients, `p ≠ 0`, no complex root of `p` on the unit circle
and exactly one root (with multiplicity) in the open unit disc iff `p(1) p(−1) < 0`. -/
theorem count_one_iff (a b c : ℝ) :
    (C a * X ^ 2 + C b * X + C c ≠ 0 ∧
        (∀ μ ∈ ((C a * X ^ 2 + C b * X + C c).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
        Multiset.card (((C a * X ^ 2 + C b * X + C c).map Complex.ofRealHom).roots.filter
          (fun μ => ‖μ‖ < 1)) = 1) ↔
      (C a * X ^ 2 + C b * X + C c).eval 1 * (C a * X ^ 2 + C b * X + C c).eval (-1) < 0 := by
  set p := C a * X ^ 2 + C b * X + C c with hp
  have hev : ∀ x : ℝ, p.eval x = a * x ^ 2 + b * x + c := fun x => by
    simp [hp]
  rw [hev, hev]
  by_cases ha : a = 0
  · subst ha
    by_cases hb : b = 0
    · subst hb
      have hpc : p = C c := by simp [hp]
      by_cases hc : c = 0
      · subst hc
        simp only [hpc, map_zero, ne_eq, not_true_eq_false, false_and, false_iff, not_lt]
        norm_num
      · have hr : (p.map Complex.ofRealHom).roots = 0 := by
          rw [hpc, map_C, roots_C]
        rw [hr]
        simp only [Multiset.filter_zero, Multiset.card_zero, zero_ne_one, and_false, false_iff,
          not_lt]
        nlinarith [sq_nonneg c]
    · have hbc : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
      have hmap : p.map Complex.ofRealHom = C (b : ℂ) * (X - C (-(c / b) : ℂ)) := by
        apply Polynomial.funext
        intro z
        simp [hp]
        field_simp
      have hr : (p.map Complex.ofRealHom).roots = {(-(c / b) : ℂ)} := by
        rw [hmap, roots_C_mul _ hbc, roots_X_sub_C]
      have hpne : p ≠ 0 := by
        intro h0
        exact hb (by simpa [hp] using congrArg (fun q => q.coeff 1) h0)
      rw [hr]
      have hn : ‖(-(c / b) : ℂ)‖ = |c / b| := by
        rw [← Complex.ofReal_div, ← Complex.ofReal_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_neg]
      simp only [ne_eq, hpne, not_false_eq_true, Multiset.mem_singleton, forall_eq, hn,
        Multiset.filter_singleton, true_and]
      have hb2 : 0 < b ^ 2 := by positivity
      constructor
      · rintro ⟨h1, h2⟩
        have hlt : |c / b| < 1 := by
          by_contra hn'
          simp [hn'] at h2
        rw [abs_div, div_lt_one (abs_pos.mpr hb)] at hlt
        have : c ^ 2 < b ^ 2 := by nlinarith [abs_nonneg c, sq_abs c, sq_abs b, abs_nonneg b]
        nlinarith
      · intro h
        have : c ^ 2 < b ^ 2 := by nlinarith
        have hlt : |c / b| < 1 := by
          rw [abs_div, div_lt_one (abs_pos.mpr hb)]
          exact sq_lt_sq.mp this
        exact ⟨hlt.ne, by simp [hlt]⟩
  · -- `a ≠ 0`: two complex roots with real sum and product
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self ((b : ℂ) ^ 2 - 4 * a * c)
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
    set r1 : ℂ := (-b + s) / (2 * a) with hr1
    set r2 : ℂ := (-b - s) / (2 * a) with hr2
    have hsum : r1 + r2 = ((-(b / a) : ℝ) : ℂ) := by
      rw [hr1, hr2]; push_cast; field_simp; ring
    have hprod : r1 * r2 = ((c / a : ℝ) : ℂ) := by
      rw [hr1, hr2]; push_cast; field_simp
      linear_combination hs
    have hmap : p.map Complex.ofRealHom = C (a : ℂ) * ((X - C r1) * (X - C r2)) := by
      apply Polynomial.funext
      intro z
      simp only [hp, Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_pow,
        map_X, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_sub,
        Complex.ofRealHom_eq_coe]
      have e1 : (a : ℂ) * (r1 + r2) = -b := by
        rw [hsum]; push_cast; field_simp
      have e2 : (a : ℂ) * (r1 * r2) = c := by
        rw [hprod]; push_cast; field_simp
      have hai : (a : ℂ) * (a : ℂ)⁻¹ = 1 := mul_inv_cancel₀ haC
      linear_combination (-z) * e1 - e2 - 2 * z * b * hai
    have hne : (X - C r1) * (X - C r2) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero r1) (X_sub_C_ne_zero r2)
    have hroots : (p.map Complex.ofRealHom).roots = {r1, r2} := by
      rw [hmap, roots_C_mul _ haC, roots_mul hne, roots_X_sub_C, roots_X_sub_C]
      rfl
    have hpne : p ≠ 0 := by
      intro h0
      exact ha (by simpa [hp] using congrArg (fun q => q.coeff 2) h0)
    rw [hroots]
    simp only [ne_eq, hpne, not_false_eq_true, true_and]
    rw [count_pair]
    -- real roots `x₁ x₂` with Vieta's relations
    have key : ∀ x1 x2 : ℝ, x1 + x2 = -(b / a) → x1 * x2 = c / a →
        (a * 1 ^ 2 + b * 1 + c) * (a * (-1) ^ 2 + b * (-1) + c) =
          a ^ 2 * ((1 - x1 ^ 2) * (1 - x2 ^ 2)) := by
      intro x1 x2 e1 e2
      have f1 : b = -(a * (x1 + x2)) := by rw [e1]; field_simp
      have f2 : c = a * (x1 * x2) := by rw [e2]; field_simp
      rw [f1, f2]; ring
    have hsi : (r1 + r2).im = 0 := by rw [hsum, Complex.ofReal_im]
    have hpi : (r1 * r2).im = 0 := by rw [hprod, Complex.ofReal_im]
    have ha2 : 0 < a ^ 2 := by positivity
    constructor
    · intro h
      have hn : ‖r1‖ ≠ ‖r2‖ := by
        rcases h with h | h <;> intro e <;> linarith [h.1, h.2]
      obtain ⟨i1, i2⟩ := real_of_sum_prod hsi hpi hn
      have e1 : r1 = (r1.re : ℂ) := Complex.ext rfl (by simp [i1])
      have e2 : r2 = (r2.re : ℂ) := Complex.ext rfl (by simp [i2])
      have hs' : r1.re + r2.re = -(b / a) := by
        have := congrArg Complex.re hsum; simpa using this
      have hp' : r1.re * r2.re = c / a := by
        have := congrArg Complex.re hprod; simp [Complex.mul_re, i1, i2] at this; linarith
      rw [key r1.re r2.re hs' hp']
      have n1 : ‖r1‖ = |r1.re| := by rw [e1, Complex.norm_real, Real.norm_eq_abs]; rfl
      have n2 : ‖r2‖ = |r2.re| := by rw [e2, Complex.norm_real, Real.norm_eq_abs]; rfl
      rw [n1, n2] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have q1 : 0 < 1 - r1.re ^ 2 := by nlinarith [sq_abs r1.re, abs_nonneg r1.re]
        have q2 : 1 - r2.re ^ 2 < 0 := by nlinarith [sq_abs r2.re, abs_nonneg r2.re]
        exact mul_neg_of_pos_of_neg ha2 (mul_neg_of_pos_of_neg q1 q2)
      · have q1 : 1 - r1.re ^ 2 < 0 := by nlinarith [sq_abs r1.re, abs_nonneg r1.re]
        have q2 : 0 < 1 - r2.re ^ 2 := by nlinarith [sq_abs r2.re, abs_nonneg r2.re]
        exact mul_neg_of_pos_of_neg ha2 (mul_neg_of_neg_of_pos q1 q2)
    · intro h
      have h' : p.eval 1 * p.eval (-1) < 0 := by rw [hev, hev]; exact h
      obtain ⟨ρ, hρ1, hρ2, hρ⟩ := exists_root_Ioo h'
      have hmem : (ρ : ℂ) ∈ (p.map Complex.ofRealHom).roots := by
        rw [mem_roots (Polynomial.map_ne_zero hpne), IsRoot, eval_map,
          ← Complex.ofRealHom_eq_coe, Polynomial.eval₂_hom, hρ, map_zero]
      rw [hroots] at hmem
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
      have habs : |ρ| < 1 := abs_lt.mpr ⟨hρ1, hρ2⟩
      have nρ : ‖(ρ : ℂ)‖ = |ρ| := by rw [Complex.norm_real, Real.norm_eq_abs]
      rcases hmem with e | e
      · -- `r₁ = ρ`, `r₂ = τ` real
        set τ := -(b / a) - ρ with hτ
        have e2 : r2 = (τ : ℂ) := by
          rw [hτ]; push_cast
          have := hsum; push_cast at this; rw [← e] at this; linear_combination this
        have hp' : ρ * τ = c / a := by
          have := hprod; rw [← e, e2] at this; exact_mod_cast this
        rw [key ρ τ (by rw [hτ]; ring) hp'] at h
        have q1 : 0 < 1 - ρ ^ 2 := by nlinarith [sq_abs ρ, abs_nonneg ρ]
        have q2 : 1 - τ ^ 2 < 0 := by
          by_contra hq
          push Not at hq
          have := mul_nonneg ha2.le (mul_nonneg q1.le hq)
          linarith
        refine Or.inl ⟨by rw [← e, nρ]; exact habs, ?_⟩
        rw [e2, Complex.norm_real, Real.norm_eq_abs]
        nlinarith [sq_abs τ, abs_nonneg τ]
      · set τ := -(b / a) - ρ with hτ
        have e1 : r1 = (τ : ℂ) := by
          rw [hτ]; push_cast
          have := hsum; push_cast at this; rw [← e] at this; linear_combination this
        have hp' : τ * ρ = c / a := by
          have := hprod; rw [← e, e1] at this; exact_mod_cast this
        rw [key τ ρ (by rw [hτ]; ring) hp'] at h
        have q2 : 0 < 1 - ρ ^ 2 := by nlinarith [sq_abs ρ, abs_nonneg ρ]
        have q1 : 1 - τ ^ 2 < 0 := by
          by_contra hq
          push Not at hq
          have := mul_nonneg ha2.le (mul_nonneg hq q2.le)
          linarith
        refine Or.inr ⟨by rw [← e, nρ]; exact habs, ?_⟩
        rw [e1, Complex.norm_real, Real.norm_eq_abs]
        nlinarith [sq_abs τ, abs_nonneg τ]

end Cochrane.KeynesianStickyPrices.TidyR5QuadRoots
