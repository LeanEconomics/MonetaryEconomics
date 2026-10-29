/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR6aGeneralBKSingular
import OptimalPolicyRules.GeneralBKCopy

/-!
# The singular-pencil Blanchard–Kahn theorem with random initial conditions

Woodford (2003), *Interest and Prices*, Appendix C.1, p. 670 (Blanchard and Kahn 1980; King and
Watson 1998; Klein 2000). The copied chain TidyR6aGeneralBK, TidyR6aGeneralBKPencil,
TidyR6aGeneralBKSingular takes the initial value `x₀` of the predetermined block to be a
**number**. Chapter 8 needs initial conditions `Z_{t₀}`, `M_{t₀−1}` that are random variables
known at date `0`, as in `GeneralBKCopy.Determinate`. Here:

* `determinateR_iff`: for the standard form `E_t y_{t+1} = Ay_t + w_t`, determinacy with random
  bounded `x₀` known at `0` (`GeneralBKCopy.Determinate`) is equivalent to determinacy with
  deterministic `x₀` (`TidyR6aGeneralBK.Determinate`), on any nonempty sample space;
* `EquilPencilR`, `DeterminatePencilR`: the pencil system `A₀E_ty_{t+1} = A₁y_t + w_t` with random
  `x₀`; `determinatePencilR_iff_ahat` (the reduction of TidyR6aGeneralBKSingular with random
  `x₀`, its proof restated from there), `determinatePencilR_iff`,
  **`determinatePencilR_iff_general`**: Klein's theorem with random initial conditions —
  determinate iff the pencil is regular, no root of `det(λA₀ − A₁)` is on the unit circle,
  exactly `|X|` lie inside, and `TidyR6aGeneralBKSingular.GenericPencil` holds.
-/

namespace Woodford.OptimalPolicyRules.TidyR6aBKRandom

open Polynomial BKInvariantSplit BKForward TidyR6aGeneralBKPencil TidyR6aGeneralBKSingular
open GeneralBKCopy
open scoped Matrix

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)
variable {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X]

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 670: **determinacy does not depend on whether `x₀` is random**:
on a nonempty sample space, the standard-form system is determinate for every bounded `x₀` known
at `0` iff it is determinate for every deterministic `x₀`. -/
theorem determinateR_iff [Nonempty Ω] (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    GeneralBKCopy.Determinate 𝔼 A ↔ TidyR6aGeneralBK.Determinate 𝔼 A := by
  classical
  constructor
  · intro hR w hwb hwa x0
    obtain ⟨y, hy, hu⟩ := hR w hwb hwa (fun j _ => x0 j) (fun j => 𝔼.const 0 (x0 j))
      ⟨∑ j, |x0 j|, fun j _ => Finset.single_le_sum (f := fun j => |x0 j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)⟩
    exact ⟨y, hy, fun y' hy' => hu y' hy'⟩
  · intro hD
    obtain ⟨hnu, hd, hg⟩ := (TidyR6aGeneralBK.determinate_iff 𝔼 A).mp hD
    exact GeneralBKCopy.determinate_of 𝔼 hnu hd hg

/-- Woodford (2003), App. C.1, p. 670: a bounded equilibrium of the pencil system
`A₀ E_t y_{t+1} = A₁ y_t + w_t` whose predetermined block starts at the **random** vector `x₀`. -/
def EquilPencilR (A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (w : ℕ → Z ⊕ X → Ω → ℝ) (x0 : X → Ω → ℝ)
    (y : ℕ → Z ⊕ X → Ω → ℝ) : Prop :=
  SolvesPencil 𝔼 A0 A1 w y ∧ AdaptedV 𝔼 y ∧
    (∀ t j, 𝔼.E t (y (t + 1) (Sum.inr j)) = y (t + 1) (Sum.inr j)) ∧
    (∀ j, y 0 (Sum.inr j) = x0 j) ∧ BoundedV y

/-- Woodford (2003), App. C.1, p. 670: determinacy of the pencil system with random initial
conditions: for every bounded adapted forcing and every bounded `x₀` known at date `0` there is
exactly one bounded equilibrium. -/
def DeterminatePencilR (A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) : Prop :=
  ∀ w : ℕ → Z ⊕ X → Ω → ℝ, BoundedV w → AdaptedV 𝔼 w → ∀ x0 : X → Ω → ℝ,
    (∀ j, 𝔼.E 0 (x0 j) = x0 j) → (∃ K, ∀ j ω, |x0 j ω| ≤ K) → ∃! y, EquilPencilR 𝔼 A0 A1 w x0 y

/-- **Singular pencils reduce to standard form, with random initial conditions** (Woodford (2003),
App. C.1, p. 670; King and Watson (1998), Klein (2000)); the proof is restated from
`TidyR6aGeneralBKSingular.determinatePencil_iff_ahat`. -/
theorem determinatePencilR_iff_ahat {A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {c : ℝ}
    (hB : IsUnit (c • A0 - A1).det) {m : ℕ} {P Q Ni : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (hF : Fitting ((c • A0 - A1)⁻¹ * A0) m P Q Ni) :
    DeterminatePencilR 𝔼 A0 A1 ↔ GeneralBKCopy.Determinate 𝔼 (ahat c P Q Ni) := by
  set B := c • A0 - A1 with hBdef
  set N := B⁻¹ * A0 with hN
  obtain ⟨hPP, hQQ, hPNi, hQNP⟩ := hF.basic
  have hFc := hF
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := hFc
  have hNiA : Ni * (c • N - 1) = c • P - Ni := by
    rw [Matrix.mul_sub, Matrix.mul_smul, h7, Matrix.mul_one]
  have hQA : Q * (c • N - 1) = (c • N - 1) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h5, Matrix.mul_one,
      Matrix.one_mul]
  have hPq : ∀ a : Z ⊕ X → Ω → ℝ, mv Q a = a → mv P a = 0 := fun a ha => by
    rw [← ha, mv_mv, h2, zero_mv]
  have hNiq : ∀ a : Z ⊕ X → Ω → ℝ, mv Q a = a → mv Ni a = 0 := fun a ha => by
    rw [← ha, mv_mv, h9, zero_mv]
  have hQidem : ∀ a : Z ⊕ X → Ω → ℝ, mv Q (mv Q a) = mv Q a := fun a => by rw [mv_mv, hQQ]
  have hEQ : ∀ (q : ℕ → Z ⊕ X → Ω → ℝ) t, (∀ t, mv Q (q t) = q t) →
      mv Q (fun i => 𝔼.E t (q (t + 1) i)) = fun i => 𝔼.E t (q (t + 1) i) := by
    intro q t hq
    rw [← Enext_mv, hq]
  constructor
  · -- pencil determinacy gives standard-form determinacy
    intro hd wh hwb hwa x0 hx0k hx0b
    obtain ⟨q, ⟨hq2, hqa, hqb⟩, hqu⟩ :=
      twoBlock_existsUnique 𝔼 (boundedV_mv Q hwb) (adaptedV_mv 𝔼 Q hwa)
    have hqQ : ∀ t, mv Q (q t) = q t := by
      have h' : (fun t => mv Q (q t)) = q := by
        refine hqu _ ⟨fun t => ?_, adaptedV_mv 𝔼 Q hqa, boundedV_mv Q hqb⟩
        change (fun i => 𝔼.E t (mv Q (q (t + 1)) i)) = (2 : ℝ) • mv Q (q t) + mv Q (wh t)
        rw [Enext_mv, hq2 t, mv_add, mv_smul, hQidem]
      exact fun t => congrFun h' t
    set wt : ℕ → Z ⊕ X → Ω → ℝ := fun t => mv N (mv P (wh t)) +
      (mv N (fun i => 𝔼.E t (q (t + 1) i)) - mv (c • N - 1) (q t)) with hwt
    have hwtb : BoundedV wt := boundedV_add (boundedV_mv N (boundedV_mv P hwb))
      (boundedV_sub (boundedV_mv N (boundedV_Enext 𝔼 hqb)) (boundedV_mv _ hqb))
    have hwta : AdaptedV 𝔼 wt := adaptedV_add 𝔼 (adaptedV_mv 𝔼 N (adaptedV_mv 𝔼 P hwa))
      (adaptedV_sub 𝔼 (adaptedV_mv 𝔼 N (adaptedV_Enext 𝔼 q)) (adaptedV_mv 𝔼 _ hqa))
    have hBw : ∀ t, mv B⁻¹ (mv B (wt t)) = wt t := fun t => by
      rw [mv_mv, Matrix.nonsing_inv_mul _ hB, mv_one]
    have hPw : ∀ t, mv P (wh t) = mv Ni (mv B⁻¹ (mv B (wt t))) := by
      intro t
      rw [hBw, hwt]
      simp only
      rw [mv_add, mv_sub, mv_mv N P, mv_mv Ni (N * P), ← Matrix.mul_assoc Ni N P, h7, hPP,
        mv_mv Ni N, h7, hPq _ (hEQ q t hqQ), mv_mv Ni (c • N - 1), hNiA, sub_mv, smul_mv,
        hPq _ (hqQ t), hNiq _ (hqQ t), smul_zero, sub_zero, sub_zero, add_zero]
    have hqN : ∀ t, mv N (fun i => 𝔼.E t (q (t + 1) i)) =
        mv (c • N - 1) (q t) + mv Q (mv B⁻¹ (mv B (wt t))) := by
      intro t
      rw [hBw, hwt]
      simp only
      have e1 : mv Q (mv N (mv P (wh t))) = 0 := by
        rw [mv_mv N P, mv_mv Q (N * P), ← Matrix.mul_assoc Q N P, hQNP, zero_mv]
      have e2 : mv Q (mv N (fun i => 𝔼.E t (q (t + 1) i))) =
          mv N (fun i => 𝔼.E t (q (t + 1) i)) := by
        rw [mv_mv Q N, ← h5, ← mv_mv N Q, hEQ q t hqQ]
      have e3 : mv Q (mv (c • N - 1) (q t)) = mv (c • N - 1) (q t) := by
        rw [mv_mv Q (c • N - 1), hQA, ← mv_mv (c • N - 1) Q, hqQ t]
      rw [mv_add, mv_sub, e1, e2, e3, zero_add]
      abel
    obtain ⟨y, hy, hyu⟩ := hd (fun t => mv B (wt t)) (boundedV_mv B hwtb)
      (adaptedV_mv 𝔼 B hwta) x0 hx0k hx0b
    have hgb : BoundedV (fun t => mv Q (mv B⁻¹ (mv B (wt t)))) :=
      boundedV_mv Q (boundedV_mv _ (boundedV_mv B hwtb))
    have hga : AdaptedV 𝔼 (fun t => mv Q (mv B⁻¹ (mv B (wt t)))) :=
      adaptedV_mv 𝔼 Q (adaptedV_mv 𝔼 _ (adaptedV_mv 𝔼 B hwta))
    have hVu := (pencilV_existsUnique 𝔼 hF c (g := fun t => mv Q (mv B⁻¹ (mv B (wt t))))
      (fun t => hQidem _) hgb hga).2
    have hyq : ∀ t, mv Q (y t) = q t := by
      have := hVu (fun t => mv Q (y t)) q (fun t => hQidem _)
        (fun t => pencil_Vpart 𝔼 hB hF hy.1 t) (adaptedV_mv 𝔼 Q hy.2.1)
        (boundedV_mv Q hy.2.2.2.2) hqQ hqN hqa hqb
      exact fun t => congrFun this t
    refine ⟨y, ⟨(pencil_iff_ahat 𝔼 hB hF (w := fun t => mv B (wt t)) hPw hq2 hqN hyq).mp hy.1,
      hy.2⟩, fun y'' hy'' => ?_⟩
    have hyq'' : ∀ t, mv Q (y'' t) = q t := by
      have := hqu (fun t => mv Q (y'' t)) ⟨fun t => ahat_Vpart 𝔼 hF c hy''.1 t,
        adaptedV_mv 𝔼 Q hy''.2.1, boundedV_mv Q hy''.2.2.2.2⟩
      exact fun t => congrFun this t
    exact hyu y'' ⟨(pencil_iff_ahat 𝔼 hB hF (w := fun t => mv B (wt t)) hPw hq2 hqN
      hyq'').mpr hy''.1, hy''.2⟩
  · -- standard-form determinacy gives pencil determinacy
    intro hd w hwb hwa x0 hx0k hx0b
    have hgQ : ∀ t, mv Q (mv Q (mv B⁻¹ (w t))) = mv Q (mv B⁻¹ (w t)) := fun t => hQidem _
    have hgb : BoundedV (fun t => mv Q (mv B⁻¹ (w t))) := boundedV_mv Q (boundedV_mv _ hwb)
    have hga : AdaptedV 𝔼 (fun t => mv Q (mv B⁻¹ (w t))) :=
      adaptedV_mv 𝔼 Q (adaptedV_mv 𝔼 _ hwa)
    obtain ⟨⟨s, hsQ, hs, hsa, hsb⟩, hsu⟩ := pencilV_existsUnique 𝔼 hF c hgQ hgb hga
    set wh : ℕ → Z ⊕ X → Ω → ℝ := fun t => mv Ni (mv B⁻¹ (w t)) +
      ((fun i => 𝔼.E t (s (t + 1) i)) - (2 : ℝ) • s t) with hwh
    have hwhb : BoundedV wh := boundedV_add (boundedV_mv Ni (boundedV_mv _ hwb))
      (boundedV_sub (boundedV_Enext 𝔼 hsb) (boundedV_smul 2 hsb))
    have hwha : AdaptedV 𝔼 wh := adaptedV_add 𝔼 (adaptedV_mv 𝔼 Ni (adaptedV_mv 𝔼 _ hwa))
      (adaptedV_sub 𝔼 (adaptedV_Enext 𝔼 s) (adaptedV_smul 𝔼 2 hsa))
    have hPw : ∀ t, mv P (wh t) = mv Ni (mv B⁻¹ (w t)) := by
      intro t
      simp only [hwh]
      rw [mv_add, mv_sub, mv_mv P Ni, hPNi, hPq _ (hEQ s t hsQ), mv_smul, hPq _ (hsQ t),
        smul_zero, sub_zero, add_zero]
    have hq2 : ∀ t, (fun i => 𝔼.E t (s (t + 1) i)) = (2 : ℝ) • s t + mv Q (wh t) := by
      intro t
      simp only [hwh]
      rw [mv_add, mv_sub, mv_mv Q Ni, h8, zero_mv, hEQ s t hsQ, mv_smul, hsQ t]
      abel
    obtain ⟨y, hy, hyu⟩ := hd wh hwhb hwha x0 hx0k hx0b
    have h2u := twoBlock_existsUnique 𝔼 (boundedV_mv Q hwhb) (adaptedV_mv 𝔼 Q hwha)
    have hyq : ∀ t, mv Q (y t) = s t := by
      have := h2u.unique ⟨fun t => ahat_Vpart 𝔼 hF c hy.1 t, adaptedV_mv 𝔼 Q hy.2.1,
        boundedV_mv Q hy.2.2.2.2⟩ ⟨hq2, hsa, hsb⟩
      exact fun t => congrFun this t
    refine ⟨y, ⟨(pencil_iff_ahat 𝔼 hB hF hPw hq2 hs hyq).mpr hy.1, hy.2⟩, fun y'' hy'' => ?_⟩
    have hyq'' : ∀ t, mv Q (y'' t) = s t := by
      have := hsu (fun t => mv Q (y'' t)) s (fun t => hQidem _)
        (fun t => pencil_Vpart 𝔼 hB hF hy''.1 t) (adaptedV_mv 𝔼 Q hy''.2.1)
        (boundedV_mv Q hy''.2.2.2.2) hsQ hs hsa hsb
      exact fun t => congrFun this t
    exact hyu y'' ⟨(pencil_iff_ahat 𝔼 hB hF hPw hq2 hs hyq'').mp hy''.1, hy''.2⟩

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 670: on a nonempty sample space the pencil system is
determinate with random initial conditions iff it is determinate with deterministic ones. -/
theorem determinatePencilR_iff [Nonempty Ω] (A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    DeterminatePencilR 𝔼 A0 A1 ↔ DeterminatePencil 𝔼 A0 A1 := by
  classical
  constructor
  · intro hR w hwb hwa x0
    obtain ⟨y, hy, hu⟩ := hR w hwb hwa (fun j _ => x0 j) (fun j => 𝔼.const 0 (x0 j))
      ⟨∑ j, |x0 j|, fun j _ => Finset.single_le_sum (f := fun j => |x0 j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)⟩
    exact ⟨y, hy, fun y' hy' => hu y' hy'⟩
  · intro hD
    have hreg : pencilPoly A0 A1 ≠ 0 := by
      intro h0
      obtain ⟨w, hwb, hwa, hno⟩ := nonexist_of_not_regular 𝔼 h0
      obtain ⟨y, hy, -⟩ := hD w hwb hwa 0
      exact hno y hy.1
    obtain ⟨c, hB⟩ := exists_regular_point hreg
    obtain ⟨m, P, Q, Ni, hFit⟩ := exists_fitting ((c • A0 - A1)⁻¹ * A0)
    have hF : Fitting ((c • A0 - A1)⁻¹ * A0) m P Q Ni := hFit
    exact (determinatePencilR_iff_ahat 𝔼 hB hF).mpr ((determinateR_iff 𝔼 _).mpr
      ((determinatePencil_iff_ahat 𝔼 hB hF).mp hD))

/-- **The Blanchard–Kahn theorem for arbitrary pencils with random initial conditions**
(Woodford (2003), App. C.1, p. 670 and fn. 1–2; Blanchard and Kahn (1980), King and Watson
(1998), Klein (2000)): for any expectation system on a nonempty sample space,
`A₀ E_t y_{t+1} = A₁ y_t + w_t` is determinate (every bounded `x₀` known at `0`) iff the pencil is
regular, no root of `det(λA₀ − A₁)` lies on the unit circle, exactly `|X|` roots lie in the open
unit disc, and `GenericPencil` holds. -/
theorem determinatePencilR_iff_general [Nonempty Ω] (A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    DeterminatePencilR 𝔼 A0 A1 ↔ pencilPoly A0 A1 ≠ 0 ∧
      (∀ μ ∈ ((pencilPoly A0 A1).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
      Multiset.card (((pencilPoly A0 A1).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card X ∧ GenericPencil A0 A1 := by
  rw [determinatePencilR_iff, determinatePencil_iff_general]

end Woodford.OptimalPolicyRules.TidyR6aBKRandom
