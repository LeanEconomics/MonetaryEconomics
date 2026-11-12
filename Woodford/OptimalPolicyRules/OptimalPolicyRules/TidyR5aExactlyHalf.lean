/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureMultiplicity
import OptimalPolicyRules.TidyR5aCaseIIExample

/-!
# Footnote 8: "exactly half of the roots have modulus less than `β^{−1/2}`"

Woodford (2003), *Interest and Prices*, Chapter 8, fn 8 (p. 542): the roots of the
characteristic equation of the system (1.1) + (1.9) pair as `μ ↔ β⁻¹μ⁻¹`, "hence exactly half of
the roots have modulus less than `β^{−1/2}`".

The characteristic polynomial is `E(ν) = det(νF − G)` of the Euler pencil
(`OptimalRulesMeasureEulerPencil.eulerPoly`, size `2n + 1`, `n = n_Z + n_z`); the pairing is
`OptimalRulesMeasureEulerPencil.rootMultiplicity_pairMap`, and `deg E + mult₀ E = 2n`
(`OptimalRulesMeasureEulerPencil.natDegree_add_rootMultiplicity_zero`): the `mult₀ E` zero roots
pair with `2n − deg E` roots at infinity.

## The general count (corrected statement)

For a regular pencil (`E ≢ 0`), counting roots with multiplicity, the zero root inside and the
roots at infinity outside:

* `two_lower_add_circle`: `2·#{β|ν|² < 1} + #{β|ν|² = 1} = 2n`;
* `lower_eq_upper`: `#{β|ν|² < 1} = #{β|ν|² > 1} + (2n − deg E)` (the halves);
* `lower_eq_half_iff`: **exactly half (`n`) of the `2n` roots lie inside `|ν| = β^{−1/2}` iff no
  root lies on that circle**; `lower_le_half`: never more than half;
* `exactly_half_of_assumption81`: under (perfect-foresight) Assumption 8.1 there is no root on the
  circle (`OptimalRulesMeasureMultiplicity.eulerRoot_gap`), so the book's count holds.

## Counterexamples to the printed claim

* `fn8Problem`, `fn8_lowerCount`, `fn8_not_exactly_half`: the system `E_tz_{t+1} = az_t + i_t`
  with loss `½i_t²` and `a = β^{−1/2}` has a regular pencil whose roots all lie on the circle
  (`fn8_root_eq`): no root inside, `n = 1` (the problem of `GeneralFOC.Pencil.fn8_counterexample`,
  now as an `LQProblem`).
* `ex_eulerPoly_eq_zero`: for the case-(ii) example `CaseIIInstance.exProblem` the pencil is
  singular — every `ν` is a root — so the count is meaningless without regularity.
-/

namespace Woodford.OptimalPolicyRules.TidyR5aExactlyHalf

open Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ OptimalRulesMeasureSpectrum
  OptimalRulesMeasureEulerPencil

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-! ### The counts -/

/-- Woodford (2003), fn 8, p. 542: the number of roots of `det(νF − G)` (with multiplicity,
including the zero root) with `|ν| < β^{−1/2}`. -/
noncomputable def lowerCount (P : LQProblem ιZ ιz ιτ) : ℕ :=
  Multiset.card ((eulerPoly P).roots.filter fun r => P.β * ‖r‖ ^ 2 < 1)

/-- Woodford (2003), fn 8, p. 542: the number of roots on the circle `|ν| = β^{−1/2}`. -/
noncomputable def circleCount (P : LQProblem ιZ ιz ιτ) : ℕ :=
  Multiset.card ((eulerPoly P).roots.filter fun r => P.β * ‖r‖ ^ 2 = 1)

/-- Woodford (2003), fn 8, p. 542: the number of roots with `|ν| > β^{−1/2}`, including the
`2n − deg E` roots at infinity. -/
noncomputable def upperCount (P : LQProblem ιZ ιz ιτ) : ℕ :=
  Multiset.card ((eulerPoly P).roots.filter fun r => 1 < P.β * ‖r‖ ^ 2) +
    (Fintype.card (ιZ ⊕ ιz) + Fintype.card (ιZ ⊕ ιz) - (eulerPoly P).natDegree)

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), fn 8 (tool): splitting a multiset of complex numbers by `β|r|² < 1`,
`= 1`, `> 1`. -/
theorem card_trichotomy (β : ℝ) (s : Multiset ℂ) :
    Multiset.card s = Multiset.card (s.filter fun r => β * ‖r‖ ^ 2 < 1) +
      Multiset.card (s.filter fun r => β * ‖r‖ ^ 2 = 1) +
      Multiset.card (s.filter fun r => 1 < β * ‖r‖ ^ 2) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.filter_cons, Multiset.card_cons, Multiset.card_add]
    rcases lt_trichotomy (β * ‖a‖ ^ 2) 1 with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le, ih]
      omega
    · simp [h, ih]
      omega
    · simp [h, h.ne', not_lt.mpr h.le, ih]
      omega

/-- Woodford (2003), fn 8, p. 542, with App. G.1: the roots split into the `mult₀ E` zero roots
and the nonzero roots `OptimalRulesMeasureEulerPencil.nzRoots`. -/
theorem card_roots_split (P : LQProblem ιZ ιz ιτ) :
    Multiset.card (eulerPoly P).roots =
      (eulerPoly P).rootMultiplicity 0 + Multiset.card (nzRoots P) := by
  have h := Multiset.filter_add_not (fun r : ℂ => r = 0) (eulerPoly P).roots
  rw [← h, Multiset.card_add]
  congr 1
  rw [← count_roots, Multiset.count_eq_card_filter_eq]
  congr 1
  exact Multiset.filter_congr fun r _ => eq_comm

/-- Woodford (2003), fn 8, p. 542: the inside count is the zero root plus the nonzero roots
inside. -/
theorem lowerCount_eq (P : LQProblem ιZ ιz ιτ) :
    lowerCount P = (eulerPoly P).rootMultiplicity 0 +
      Multiset.card ((nzRoots P).filter fun r => P.β * ‖r‖ ^ 2 < 1) := by
  have h := Multiset.filter_add_not (fun r : ℂ => r = 0) (eulerPoly P).roots
  unfold lowerCount
  rw [← h, Multiset.filter_add, Multiset.card_add]
  congr 1
  rw [← count_roots, Multiset.count_eq_card_filter_eq, Multiset.filter_filter]
  congr 1
  refine Multiset.filter_congr fun r _ => ?_
  constructor
  · rintro ⟨-, rfl⟩
    rfl
  · rintro rfl
    exact ⟨by simp, rfl⟩

/-- Woodford (2003), fn 8, p. 542: the zero root is not on the circle, so the circle count is
that of the nonzero roots. -/
theorem circleCount_eq (P : LQProblem ιZ ιz ιτ) :
    circleCount P = Multiset.card ((nzRoots P).filter fun r => P.β * ‖r‖ ^ 2 = 1) := by
  unfold circleCount nzRoots
  rw [Multiset.filter_filter]
  congr 1
  refine Multiset.filter_congr fun r _ => ?_
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rintro rfl
    simp at h
  · exact fun h => h.1

/-- Woodford (2003), fn 8, p. 542: the outside count of finite roots is that of the nonzero
roots. -/
theorem upper_finite_eq (P : LQProblem ιZ ιz ιτ) :
    Multiset.card ((eulerPoly P).roots.filter fun r => 1 < P.β * ‖r‖ ^ 2) =
      Multiset.card ((nzRoots P).filter fun r => 1 < P.β * ‖r‖ ^ 2) := by
  unfold nzRoots
  rw [Multiset.filter_filter]
  congr 1
  refine Multiset.filter_congr fun r _ => ?_
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rintro rfl
    simp at h
    linarith
  · exact fun h => h.1

/-! ### The corrected "exactly half" -/

/-- **Woodford (2003), fn 8, p. 542, the corrected count.** For a regular Euler pencil, counting
roots with multiplicity, `2·#{|ν| < β^{−1/2}} + #{|ν| = β^{−1/2}} = 2n`, `n = n_Z + n_z` (the zero
roots pair with the `2n − deg E` roots at infinity, the nonzero roots with each other). -/
theorem two_lower_add_circle (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) :
    2 * lowerCount P + circleCount P = 2 * Fintype.card (ιZ ⊕ ιz) := by
  have h1 := natDegree_add_rootMultiplicity_zero P hE
  have h2 := card_lower_eq_upper P hE
  have h3 := card_trichotomy P.β (nzRoots P)
  have h4 := card_roots_split P
  have h5 : Multiset.card (eulerPoly P).roots = (eulerPoly P).natDegree :=
    (splits_iff_card_roots.mp (IsAlgClosed.splits _))
  rw [lowerCount_eq, circleCount_eq]
  omega

/-- **Woodford (2003), fn 8, p. 542: the two halves.** For a regular Euler pencil the roots with
`|ν| < β^{−1/2}` (including the zero roots) are exactly as many as those with `|ν| > β^{−1/2}`
(including the roots at infinity). -/
theorem lower_eq_upper (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) :
    lowerCount P = upperCount P := by
  have h1 := natDegree_add_rootMultiplicity_zero P hE
  have h2 := card_lower_eq_upper P hE
  unfold upperCount
  rw [lowerCount_eq, upper_finite_eq]
  omega

/-- **Woodford (2003), fn 8, p. 542, corrected: "exactly half of the roots have modulus less than
`β^{−1/2}`" holds iff no root lies on the circle `|ν| = β^{−1/2}`** (regular pencil; `2n` roots
counting those at infinity). -/
theorem lower_eq_half_iff (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) :
    lowerCount P = Fintype.card (ιZ ⊕ ιz) ↔ circleCount P = 0 := by
  have := two_lower_add_circle P hE
  omega

/-- Woodford (2003), fn 8, p. 542: at most half of the roots lie inside `|ν| = β^{−1/2}`. -/
theorem lower_le_half (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) :
    lowerCount P ≤ Fintype.card (ιZ ⊕ ιz) := by
  have := two_lower_add_circle P hE
  omega

/-- Woodford (2003), fn 8, p. 542: if no root of the pencil lies on `|ν| = β^{−1/2}`, exactly half
of the roots lie inside. -/
theorem exactly_half_of_noCircle (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0)
    (h : ∀ ν, EulerRoot P ν → P.β * ‖ν‖ ^ 2 ≠ 1) :
    lowerCount P = Fintype.card (ιZ ⊕ ιz) := by
  rw [lower_eq_half_iff P hE, circleCount, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro r hr
  refine h r ?_
  rw [eulerRoot_iff, ← eulerPoly_eval]
  exact (mem_roots hE).mp hr

/-- **Woodford (2003), fn 8, p. 542, under Assumption 8.1 (perfect foresight)**: the pencil is
regular (`OptimalRulesMeasureMultiplicity.eulerPoly_ne_zero`), every root has `|ν| ≤ 1` or
`|ν| ≥ β⁻¹` (`OptimalRulesMeasureMultiplicity.eulerRoot_gap`), none lies on `|ν| = β^{−1/2}`, and
exactly half of the `2n` roots lie inside. -/
theorem exactly_half_of_assumption81 {P : LQProblem ιZ ιz ιτ}
    (hA81 : Assumption81 P perfectForesight 0) :
    lowerCount P = Fintype.card (ιZ ⊕ ιz) := by
  have hβ0 := P.β_pos
  have hβ1 := P.β_lt_one
  refine exactly_half_of_noCircle P (OptimalRulesMeasureMultiplicity.eulerPoly_ne_zero hA81)
    fun ν hν => ?_
  rcases OptimalRulesMeasureMultiplicity.eulerRoot_gap hA81 hν with h | h
  · have h2 : ‖ν‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) h
    have : P.β * ‖ν‖ ^ 2 < 1 := by nlinarith
    exact this.ne
  · have h0 : 0 < P.β⁻¹ := inv_pos.mpr hβ0
    have h2 : P.β⁻¹ ^ 2 ≤ ‖ν‖ ^ 2 := pow_le_pow_left₀ h0.le h 2
    have h3 : P.β * P.β⁻¹ ^ 2 = P.β⁻¹ := by field_simp
    have h4 : 1 < P.β⁻¹ := (one_lt_inv₀ hβ0).mpr hβ1
    have : 1 < P.β * ‖ν‖ ^ 2 := by nlinarith
    exact this.ne'

/-! ### The counterexample of fn 8 as a policy problem -/

/-- Woodford (2003), fn 8, p. 542 (the counterexample): one forward-looking variable, no
predetermined variable, `E_tz_{t+1} = az_t + i_t` (`Ẽ = 1`, `A₂₂ = a ≠ 0`, `B₂ = 1`). -/
noncomputable def fn8Sys (a : ℝ) (ha : a ≠ 0) : LinearRESystem Empty (Fin 1) where
  A11 := 0
  A12 := 0
  A21 := 0
  A22 := !![a]
  Et := !![1]
  B2 := ![1]
  A22_isUnit := by simpa using ha
  B2_ne_zero := by
    intro h
    have := congrFun h 0
    simp at this

/-- Woodford (2003), fn 8, p. 542: the counterexample as a policy problem, with the instrument as
the only target, `L = ½i²` (`T̃ = 0`, `T_i = 1`, `W = 1`). -/
noncomputable def fn8Problem (a : ℝ) (ha : a ≠ 0) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    LQProblem Empty (Fin 1) (Fin 1) where
  sys := fn8Sys a ha
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  Ttil := 0
  Ti := ![1]
  W := 1
  τstar := 0
  W_posDef := Matrix.PosDef.one

/-- Woodford (2003), fn 8, p. 542: the roots of the counterexample's pencil are `a` and its partner
`(βa)⁻¹`. -/
theorem fn8_root_eq {a : ℝ} (ha : a ≠ 0) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {ν : ℂ}
    (h : EulerRoot (fn8Problem a ha β hβ0 hβ1) ν) :
    ν = (a : ℂ) ∨ ν = ((β : ℂ) * a)⁻¹ := by
  obtain ⟨u, p, hne, h1, h2⟩ := h
  have r1 : ν * u (Sum.inl (Sum.inr 0)) = (a : ℂ) * u (Sum.inl (Sum.inr 0)) + u (Sum.inr ()) := by
    simpa [fn8Problem, fn8Sys, LinearRESystem.Atil, LinearRESystem.Itil, LinearRESystem.Ahat,
      LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct, Fintype.sum_sum_type]
      using congrFun h1 (Sum.inr 0)
  have r2 : ν * ((a : ℂ) * p (Sum.inr 0)) - (β : ℂ)⁻¹ * p (Sum.inr 0) = 0 := by
    simpa [fn8Problem, fn8Sys, LinearRESystem.Atil, LinearRESystem.Itil, LinearRESystem.Ahat,
      LinearRESystem.Ihat, LinearRESystem.Bvec, LQProblem.T, mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.mul_apply] using congrFun h2 (Sum.inl (Sum.inr 0))
  have r3 : ν * p (Sum.inr 0) + u (Sum.inr ()) = 0 := by
    simpa [fn8Problem, fn8Sys, LinearRESystem.Atil, LinearRESystem.Itil, LinearRESystem.Ahat,
      LinearRESystem.Ihat, LinearRESystem.Bvec, LQProblem.T, mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.mul_apply] using congrFun h2 (Sum.inr ())
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ0.ne'
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  by_cases hp : p (Sum.inr 0) = 0
  · left
    have hui : u (Sum.inr ()) = 0 := by
      rw [hp, mul_zero, zero_add] at r3
      exact r3
    by_contra hν
    apply hne.elim
    · intro hu
      apply hu
      funext k
      rcases k with (e | j) | k
      · exact e.elim
      · rw [Subsingleton.elim j 0]
        have : (ν - a) * u (Sum.inl (Sum.inr 0)) = 0 := by linear_combination r1 + hui
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hν)
      · rw [Subsingleton.elim k ()]
        exact hui
    · intro hp'
      apply hp'
      funext k
      rcases k with e | j
      · exact e.elim
      · rw [Subsingleton.elim j 0]
        exact hp
  · right
    have : (ν * a - (β : ℂ)⁻¹) * p (Sum.inr 0) = 0 := by linear_combination r2
    have e := sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hp)
    have e2 : ν = (β : ℂ)⁻¹ * (a : ℂ)⁻¹ := by
      rw [← e]
      field_simp
    rw [e2, mul_inv]

/-- Woodford (2003), fn 8, p. 542: `ν = 0` is not a root, so the counterexample's pencil is
regular. -/
theorem fn8_eulerPoly_ne_zero {a : ℝ} (ha : a ≠ 0) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    eulerPoly (fn8Problem a ha β hβ0 hβ1) ≠ 0 := by
  intro h0
  have := fn8_root_eq ha hβ0 hβ1 ((OptimalRulesMeasureMultiplicity.eulerPoly_eq_zero_iff _).mp
    h0 0)
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ0.ne'
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  rcases this with h | h
  · exact hac h.symm
  · exact inv_ne_zero (mul_ne_zero hβc hac) h.symm

/-- **Woodford (2003), fn 8, p. 542: the printed claim fails.** With `a = β^{−1/2}` the pencil is
regular but **no** root lies inside `|ν| = β^{−1/2}` (both roots equal `a`, on the circle), while
`n = 1`. -/
theorem fn8_lowerCount {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    lowerCount (fn8Problem (Real.sqrt β)⁻¹ (inv_ne_zero (Real.sqrt_pos.mpr hβ0).ne') β hβ0
      hβ1) = 0 := by
  set a := (Real.sqrt β)⁻¹ with ha
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ0
  have ha2 : β * a ^ 2 = 1 := by
    rw [ha, inv_pow, Real.sq_sqrt hβ0.le]
    field_simp
  have hpair : ((β : ℂ) * a)⁻¹ = a := by
    have : (β : ℂ) * a * a = 1 := by exact_mod_cast (by rw [mul_assoc, ← sq]; exact ha2)
    rw [inv_eq_of_mul_eq_one_right this]
  rw [lowerCount, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro r hr
  have hroot : EulerRoot (fn8Problem a (inv_ne_zero hs.ne') β hβ0 hβ1) r := by
    rw [eulerRoot_iff, ← eulerPoly_eval]
    exact (mem_roots (fn8_eulerPoly_ne_zero _ hβ0 hβ1)).mp hr
  have hr' : r = (a : ℂ) := by
    rcases fn8_root_eq _ hβ0 hβ1 hroot with h | h
    · exact h
    · rw [h, hpair]
  change ¬ β * ‖r‖ ^ 2 < 1
  rw [hr', Complex.norm_real, Real.norm_eq_abs, sq_abs, ha2]
  exact lt_irrefl 1

/-- **Woodford (2003), fn 8, p. 542: "exactly half of the roots have modulus less than `β^{−1/2}`"
is false as printed** (`n = 1`, no root inside), although the pencil is regular and the pairing
holds; the corrected statement is `lower_eq_half_iff`. -/
theorem fn8_not_exactly_half {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    lowerCount (fn8Problem (Real.sqrt β)⁻¹ (inv_ne_zero (Real.sqrt_pos.mpr hβ0).ne') β hβ0
      hβ1) ≠ Fintype.card (Empty ⊕ Fin 1) := by
  rw [fn8_lowerCount hβ0 hβ1]
  simp

/-- Woodford (2003), fn 8, p. 542: in the counterexample both roots lie on the circle,
`#{|ν| = β^{−1/2}} = 2 = 2n` (`two_lower_add_circle`). -/
theorem fn8_circleCount {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    circleCount (fn8Problem (Real.sqrt β)⁻¹ (inv_ne_zero (Real.sqrt_pos.mpr hβ0).ne') β hβ0
      hβ1) = 2 := by
  have h := two_lower_add_circle _ (fn8_eulerPoly_ne_zero (inv_ne_zero
    (Real.sqrt_pos.mpr hβ0).ne') hβ0 hβ1)
  rw [fn8_lowerCount hβ0 hβ1] at h
  simpa using h

/-! ### A singular pencil -/

/-- **Woodford (2003), fn 8, p. 542: the count needs a regular pencil.** For the case-(ii) example
`CaseIIInstance.exProblem` (zero loss) every `ν` is a root of the Euler pencil
(`u = (1, ν − 1, 1 + (ν − 1)²)`, `p = 0`), so `det(νF − G) ≡ 0`. -/
theorem ex_eulerPoly_eq_zero : eulerPoly CaseIIInstance.exProblem = 0 := by
  refine (OptimalRulesMeasureMultiplicity.eulerPoly_eq_zero_iff _).mpr fun ν => ?_
  refine ⟨Sum.elim (Sum.elim (fun _ => 1) (fun _ => ν - 1)) (fun _ => 1 + (ν - 1) ^ 2), 0,
    Or.inl fun h => by simpa using congrFun h (Sum.inl (Sum.inl 0)), ?_, ?_⟩
  · funext r
    rcases r with r | r
    · rw [Subsingleton.elim r 0]
      simp [CaseIIInstance.exProblem, CaseIIInstance.exSys, LinearRESystem.Atil,
        LinearRESystem.Itil, LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec,
        mulVec, dotProduct, Fintype.sum_sum_type]
    · rw [Subsingleton.elim r 0]
      simp [CaseIIInstance.exProblem, CaseIIInstance.exSys, LinearRESystem.Atil,
        LinearRESystem.Itil, LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec,
        mulVec, dotProduct, Fintype.sum_sum_type]
      ring
  · funext k
    simp [CaseIIInstance.exProblem, LQProblem.T, mulVec, dotProduct, Matrix.mul_apply]

end Woodford.OptimalPolicyRules.TidyR5aExactlyHalf
