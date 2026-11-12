/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR6aBKRandom
import OptimalPolicyRules.Tidy
import OptimalPolicyRules.GeneralFOC

/-!
# Is the generalised Taylor principle necessary for determinacy within the family (3.7)?

Woodford (2003), *Interest and Prices*, Chapter 8, §3.1, (2.1), (3.1), (3.7) (pp. 583–585), and
Chapter 4, §2.2, (2.9) and footnote 27 (pp. 255–256); Appendix C.1 (Blanchard–Kahn).

The book does not claim that the generalised Taylor principle (`Tidy.TaylorPrinciple.GTP`,
`φπ + ρ₁ > 1` for a rule of the form (3.7)) is necessary for determinacy. Both answers are
proved here, with determinacy in the sense of Appendix C.1 for the system (2.1), (3.1), (3.7)
written as a pencil `A₀ E_t y_{t+1} = A₁ y_t + w_t` in `y = (π, x, i; i_{−1}, i_{−2}, x_{−1})`
(the rule is a static row, so `A₀` is singular; `TidyR6aBKRandom.DeterminatePencilR`).

* `A0g`, `A1g`, `pencil_rows`: the pencil and its rows: (2.1), (3.1), (3.7) and the three
  lag identities.
* `charC`, `pencilPoly_eq`: `det(λA₀ − A₁) = −λ C(λ)` with
  `C(λ) = (σκλ − (1−λ)(1−βλ))(λ² − (ρ₁+ρ₂)λ + ρ₂) − σκφπλ² − σ(φₓ/4)λ(λ−1)(1−βλ)`;
  `charC_one`: `C(1) = −σκ (φπ + ρ₁ − 1)`, the slack of the principle (footnote 27).
* `odd_inside`: for a real polynomial with no root on the unit circle, `p(1)p(−1) < 0` forces an
  **odd** number of roots in the open unit disc (the roots pair as `r² − 1`).
* **`gtp_necessary`** (necessity, corrected statement): if `φπ ≥ 0`, `φₓ ≥ 0` and
  `1 + ρ₁ + 2ρ₂ > 0` (true for the book's signs), determinacy implies the generalised Taylor
  principle. Proof: if `φπ + ρ₁ ≤ 1`, either `C(1) = 0` (a unit root) or `C(1) > 0 > C(−1)`, so `C`
  has an odd number of roots inside and `det(λA₀ − A₁)` cannot have the `3` required.
* **`gtp_not_necessary`** (refutation without sign restrictions): with `ρ₁ = ρ₂ = φₓ = 0` and
  `φπ < −1 − 2(1+β)/(σκ)` the system is determinate under every expectation system, although the
  principle fails (`φπ + ρ₁ − 1 < 0`).
-/

namespace Woodford.OptimalPolicyRules.TidyR6aTaylorNecessity

open Matrix Polynomial ComplexConjugate TidyR6aGeneralBKPencil TidyR6aGeneralBKSingular
open TidyR6aBKRandom Tidy.TaylorPrinciple GeneralFOC.Selection

/-! ### The pencil of (2.1), (3.1), (3.7) -/

/-- Woodford (2003), §3.1 (tool): the coordinates `(π, x, i, i_{−1}, i_{−2}, x_{−1})` as `Fin 6`. -/
def e6 : Fin 6 ≃ Fin 3 ⊕ Fin 3 where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1, Sum.inr 2]
  invFun := Sum.elim ![0, 1, 2] ![3, 4, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by
    intro a
    rcases a with a | a <;> fin_cases a <;> rfl

/-- Woodford (2003), (2.1), (3.1), (3.7): the lead matrix `A₀` (rows: (2.1), (3.1), (3.7), then
`p_{t+1} = i_t`, `q_{t+1} = p_t`, `r_{t+1} = x_t`; columns `(π, x, i; p, q, r)` with
`p = i_{−1}`, `q = i_{−2}`, `r = x_{−1}` predetermined). The rule row is static. -/
def A0g (β σ : ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  fromBlocks !![β, 0, 0; σ, 1, 0; 0, 0, 0] 0 0 1

/-- Woodford (2003), (2.1), (3.1), (3.7): the current-date matrix `A₁` for a rule of the form
(3.7) with coefficients `ρ₁, ρ₂, φπ, φₓ`. -/
noncomputable def A1g (κ σ r1 r2 fp fx : ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  fromBlocks !![1, -κ, 0; 0, 1, σ; fp, fx / 4, -1] !![0, 0, 0; 0, 0, 0; r1 + r2, -r2, -(fx / 4)]
    !![0, 0, 1; 0, 0, 0; 0, 1, 0] !![0, 0, 0; 1, 0, 0; 0, 0, 0]

/-- Woodford (2003), (2.1), (3.1), (3.7), pointwise: `A₀ e = A₁ y + w` row by row: `βe_π = π − κx
+ w₀` ((2.1) with `w₀ = −u`), `σe_π + e_x = x + σi + w₁` ((3.1) with `w₁ = −σrⁿ`),
`0 = φπ π + (φₓ/4)(x − r) − i + (ρ₁+ρ₂)p − ρ₂q + w₂` ((3.7)), and `e_p = i + w₃`,
`e_q = p + w₄`, `e_r = x + w₅`. -/
theorem pencil_rows (β σ κ r1 r2 fp fx : ℝ) (e y w : Fin 3 ⊕ Fin 3 → ℝ) :
    A0g β σ *ᵥ e = A1g κ σ r1 r2 fp fx *ᵥ y + w ↔
      β * e (Sum.inl 0) = y (Sum.inl 0) - κ * y (Sum.inl 1) + w (Sum.inl 0) ∧
      σ * e (Sum.inl 0) + e (Sum.inl 1) = y (Sum.inl 1) + σ * y (Sum.inl 2) + w (Sum.inl 1) ∧
      0 = fp * y (Sum.inl 0) + fx / 4 * (y (Sum.inl 1) - y (Sum.inr 2)) - y (Sum.inl 2) +
        (r1 + r2) * y (Sum.inr 0) - r2 * y (Sum.inr 1) + w (Sum.inl 2) ∧
      e (Sum.inr 0) = y (Sum.inl 2) + w (Sum.inr 0) ∧
      e (Sum.inr 1) = y (Sum.inr 0) + w (Sum.inr 1) ∧
      e (Sum.inr 2) = y (Sum.inl 1) + w (Sum.inr 2) := by
  constructor
  · intro h
    have h0 := congrFun h (Sum.inl 0)
    have h1 := congrFun h (Sum.inl 1)
    have h2 := congrFun h (Sum.inl 2)
    have h3 := congrFun h (Sum.inr 0)
    have h4 := congrFun h (Sum.inr 1)
    have h5 := congrFun h (Sum.inr 2)
    simp [A0g, A1g, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three,
      one_apply] at h0 h1 h2 h3 h4 h5
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    funext a
    rcases a with a | a <;> fin_cases a <;>
      simp [A0g, A1g, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three,
        one_apply] <;> linarith

/-- Woodford (2003), §3.1 and Ch. 4, fn 27: the characteristic polynomial of (2.1), (3.1), (3.7),
`C(λ) = (σκλ − (1−λ)(1−βλ))(λ² − (ρ₁+ρ₂)λ + ρ₂) − σκφπλ² − σ(φₓ/4)λ(λ−1)(1−βλ)`. -/
noncomputable def charC (β σ κ r1 r2 fp fx : ℝ) : ℝ[X] :=
  (C (σ * κ) * X - (1 - X) * (1 - C β * X)) * (X ^ 2 - C (r1 + r2) * X + C r2) -
    C (σ * κ * fp) * X ^ 2 - C (σ * (fx / 4)) * X * (X - 1) * (1 - C β * X)

/-- Woodford (2003), §3.1: `C(λ)` evaluated. -/
theorem charC_eval (β σ κ r1 r2 fp fx l : ℝ) :
    (charC β σ κ r1 r2 fp fx).eval l =
      (σ * κ * l - (1 - l) * (1 - β * l)) * (l ^ 2 - (r1 + r2) * l + r2) -
        σ * κ * fp * l ^ 2 - σ * (fx / 4) * l * (l - 1) * (1 - β * l) := by
  simp [charC]

/-- **Woodford (2003), (2.1), (3.1), (3.7) and App. C.1: `det(λA₀ − A₁) = −λ C(λ)`.** -/
theorem pencilPoly_eq (β σ κ r1 r2 fp fx : ℝ) :
    pencilPoly (A0g β σ) (A1g κ σ r1 r2 fp fx) = -X * charC β σ κ r1 r2 fp fx := by
  refine Polynomial.funext fun l => ?_
  rw [eval_pencilPoly, eval_mul, eval_neg, eval_X, charC_eval, ← det_submatrix_equiv_self e6]
  have : (l • A0g β σ - A1g κ σ r1 r2 fp fx).submatrix e6 e6 =
      !![l * β - 1, κ, 0, 0, 0, 0; l * σ, l - 1, -σ, 0, 0, 0;
        -fp, -(fx / 4), 1, -(r1 + r2), r2, fx / 4;
        0, 0, -1, l, 0, 0; 0, 0, 0, -1, l, 0; 0, -1, 0, 0, 0, l] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e6, A0g, A1g]
  rw [this]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [Fin.succAbove, Fin.lt_def]
  ring

/-- Woodford (2003), Ch. 4, fn 27, for (3.7): `C(1) = −σκ(φπ + ρ₁ − 1)`, minus `σκ` times the
slack of the generalised Taylor principle. -/
theorem charC_one (β σ κ r1 r2 fp fx : ℝ) :
    (charC β σ κ r1 r2 fp fx).eval 1 = -(σ * κ) * (fp + r1 - 1) := by
  rw [charC_eval]
  ring

/-- Woodford (2003), §3.1: `C(−1) = −(σκ + 2(1+β))(1 + ρ₁ + 2ρ₂) − σκφπ − σφₓ(1+β)/2`. -/
theorem charC_neg_one (β σ κ r1 r2 fp fx : ℝ) :
    (charC β σ κ r1 r2 fp fx).eval (-1) =
      -(σ * κ + 2 * (1 + β)) * (1 + r1 + 2 * r2) - σ * κ * fp - σ * fx * (1 + β) / 2 := by
  rw [charC_eval]
  ring

/-! ### Parity of the number of roots inside the unit circle -/

/-- Woodford (2003), Ch. 4, fn 27 (tool): for a conjugation-closed multiset with no element on the
unit circle, `∏ (r² − 1)` is a nonzero real number, negative iff an odd number of elements lie
inside the unit circle (real `r` inside give `r² − 1 < 0`, real `r` outside `> 0`, and a
conjugate pair gives `|r² − 1|² > 0` with both members on the same side). -/
theorem parity_prod : ∀ (n : ℕ) (S : Multiset ℂ), Multiset.card S = n → ConjClosed S →
    (∀ μ ∈ S, ‖μ‖ ≠ 1) → ∃ x : ℝ, (S.map fun r => r ^ 2 - 1).prod = (x : ℂ) ∧ x ≠ 0 ∧
      (x < 0 ↔ Odd (Multiset.card (S.filter fun r => ‖r‖ < 1))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hS hS1
    rcases Multiset.empty_or_exists_mem S with h0 | ⟨μ, hμ⟩
    · subst h0
      exact ⟨1, by simp, one_ne_zero, by simp⟩
    · by_cases hr : conj μ = μ
      · -- a real element
        set T := S.erase μ with hT
        have hST : S = μ ::ₘ T := (Multiset.cons_erase hμ).symm
        have hTc : ConjClosed T := by
          unfold ConjClosed
          rw [hT, Multiset.map_erase _ conj_injective, hS, hr]
        have hcard : Multiset.card T < n := by
          rw [← hn, hST, Multiset.card_cons]
          omega
        obtain ⟨x, hx, hx0, hxs⟩ := ih _ hcard T rfl hTc fun ν hν =>
          hS1 ν (Multiset.mem_of_mem_erase hν)
        set a := μ.re with ha
        have hμa : μ = (a : ℂ) := (Complex.conj_eq_iff_re.mp hr).symm
        have hna : |a| ≠ 1 := by
          have := hS1 μ hμ
          rwa [hμa, Complex.norm_real, Real.norm_eq_abs] at this
        have ha2 : a ^ 2 - 1 ≠ 0 := by
          intro h
          apply hna
          have : |a| ^ 2 = 1 := by rw [sq_abs]; linarith
          nlinarith [abs_nonneg a]
        refine ⟨(a ^ 2 - 1) * x, ?_, mul_ne_zero ha2 hx0, ?_⟩
        · rw [hST, Multiset.map_cons, Multiset.prod_cons, hx, hμa]
          push_cast
          ring
        · rw [hST]
          have hnorm : ‖μ‖ = |a| := by rw [hμa, Complex.norm_real, Real.norm_eq_abs]
          by_cases hin : ‖μ‖ < 1
          · rw [Multiset.filter_cons_of_pos (p := fun r : ℂ => ‖r‖ < 1) _ hin, Multiset.card_cons,
              Nat.odd_add_one, ← hxs]
            have : a ^ 2 - 1 < 0 := by
              rw [hnorm] at hin
              nlinarith [abs_nonneg a, sq_abs a]
            constructor
            · intro h hx'
              nlinarith
            · intro h
              have : 0 < x := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hx0)
              nlinarith
          · rw [Multiset.filter_cons_of_neg (p := fun r : ℂ => ‖r‖ < 1) _ hin, ← hxs]
            have hgt : 0 < a ^ 2 - 1 := by
              rw [hnorm] at hin
              have h1 : 1 < |a| := lt_of_le_of_ne (not_lt.mp hin) (Ne.symm hna)
              nlinarith [abs_nonneg a, sq_abs a]
            constructor
            · intro h
              by_contra hx'
              have : 0 < x := lt_of_le_of_ne (not_lt.mp hx') (Ne.symm hx0)
              nlinarith
            · intro h
              nlinarith
      · -- a conjugate pair
        have hc : conj μ ∈ S.erase μ := (Multiset.mem_erase_of_ne hr).mpr (hS.conj_mem hμ)
        set T := (S.erase μ).erase (conj μ) with hT
        have hST : S = μ ::ₘ conj μ ::ₘ T := by
          rw [hT, Multiset.cons_erase hc, Multiset.cons_erase hμ]
        have hcard : Multiset.card T < n := by
          rw [← hn, hST, Multiset.card_cons, Multiset.card_cons]
          omega
        obtain ⟨x, hx, hx0, hxs⟩ := ih _ hcard T rfl (hS.erase_pair μ) fun ν hν =>
          hS1 ν (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hν))
        have hz : μ ^ 2 - 1 ≠ 0 := by
          intro h
          have : μ ^ 2 = 1 := by linear_combination h
          rcases sq_eq_one_iff.mp this with h1 | h1
          · exact hr (by rw [h1]; simp)
          · exact hr (by rw [h1]; simp)
        have hpos : 0 < Complex.normSq (μ ^ 2 - 1) := Complex.normSq_pos.mpr hz
        refine ⟨Complex.normSq (μ ^ 2 - 1) * x, ?_, mul_ne_zero hpos.ne' hx0, ?_⟩
        · rw [hST, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
            hx, ← mul_assoc, Complex.ofReal_mul]
          congr 1
          rw [← Complex.mul_conj, map_sub, map_pow, map_one]
        · have hnc : ‖conj μ‖ = ‖μ‖ := Complex.norm_conj μ
          rw [hST]
          by_cases hin : ‖μ‖ < 1
          · rw [Multiset.filter_cons_of_pos (p := fun r : ℂ => ‖r‖ < 1) _ hin,
              Multiset.filter_cons_of_pos (p := fun r : ℂ => ‖r‖ < 1) _ (hnc ▸ hin),
              Multiset.card_cons, Multiset.card_cons,
              add_assoc, show (1 : ℕ) + 1 = 2 from rfl, Nat.odd_add, ← hxs]
            constructor
            · intro h
              have : x < 0 := by
                by_contra hx'
                have : 0 < x := lt_of_le_of_ne (not_lt.mp hx') (Ne.symm hx0)
                nlinarith
              exact ⟨fun _ => even_two, fun _ => this⟩
            · intro h
              have := h.2 even_two
              nlinarith
          · rw [Multiset.filter_cons_of_neg (p := fun r : ℂ => ‖r‖ < 1) _ hin,
              Multiset.filter_cons_of_neg (p := fun r : ℂ => ‖r‖ < 1) _
                (by rw [hnc]; exact hin), ← hxs]
            constructor
            · intro h
              by_contra hx'
              have : 0 < x := lt_of_le_of_ne (not_lt.mp hx') (Ne.symm hx0)
              nlinarith
            · intro h
              nlinarith

/-- Woodford (2003), App. C.1 (tool): the roots of a real polynomial, as complex numbers, are
closed under conjugation. -/
theorem roots_conjClosed (p : ℝ[X]) : ConjClosed (p.map Complex.ofRealHom).roots := by
  set q := p.map Complex.ofRealHom
  have hmap : q.map (starRingEnd ℂ) = q := by
    rw [Polynomial.map_map]
    congr 1
    ext x
    simp
  unfold ConjClosed
  rw [roots_map_of_injective_of_card_eq_natDegree (starRingEnd ℂ).injective
    (IsAlgClosed.card_roots_eq_natDegree), hmap]

/-- Woodford (2003), App. C.1 (tool): `p(1) p(−1) = lc(p)² ∏ (r² − 1)` over the complex roots. -/
theorem eval_one_mul_eval_neg_one (p : ℝ[X]) :
    ((p.eval 1 * p.eval (-1) : ℝ) : ℂ) =
      ((p.leadingCoeff ^ 2 : ℝ) : ℂ) *
        ((p.map Complex.ofRealHom).roots.map fun r => r ^ 2 - 1).prod := by
  set q := p.map Complex.ofRealHom with hq
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := q))
  have e1 : ((p.eval 1 : ℝ) : ℂ) = q.eval 1 := by
    rw [hq, eval_map, ← Complex.ofRealHom_eq_coe, ← map_one Complex.ofRealHom, eval₂_at_apply]
  have e2 : ((p.eval (-1) : ℝ) : ℂ) = q.eval (-1) := by
    rw [hq, eval_map, ← Complex.ofRealHom_eq_coe, show (-1 : ℂ) = Complex.ofRealHom (-1) by simp,
      eval₂_at_apply]
  have hlc : q.leadingCoeff = ((p.leadingCoeff : ℝ) : ℂ) := by
    rw [hq, leadingCoeff_map_of_injective Complex.ofRealHom.injective]
    rfl
  have h1 : q.eval 1 = q.leadingCoeff * (q.roots.map (eval 1 ∘ fun a : ℂ => X - C a)).prod := by
    conv_lhs => rw [← hfac]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
  have h2 : q.eval (-1) =
      q.leadingCoeff * (q.roots.map (eval (-1) ∘ fun a : ℂ => X - C a)).prod := by
    conv_lhs => rw [← hfac]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
  push_cast
  rw [e1, e2, h1, h2, hlc]
  have hprod : (q.roots.map (eval 1 ∘ fun a : ℂ => X - C a)).prod *
      (q.roots.map (eval (-1) ∘ fun a : ℂ => X - C a)).prod =
        (q.roots.map fun r => r ^ 2 - 1).prod := by
    rw [← Multiset.prod_map_mul]
    congr 1
    refine Multiset.map_congr rfl fun r _ => ?_
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    ring
  rw [← hprod]
  ring

/-- **Woodford (2003), App. C.1 and Ch. 4, fn 27 (the parity argument)**: if a real polynomial has
no root on the unit circle and `p(1) p(−1) < 0`, it has an **odd** number of roots (with
multiplicity) in the open unit disc. -/
theorem odd_inside (p : ℝ[X]) (h1 : ∀ r ∈ (p.map Complex.ofRealHom).roots, ‖r‖ ≠ 1)
    (hs : p.eval 1 * p.eval (-1) < 0) :
    Odd (Multiset.card ((p.map Complex.ofRealHom).roots.filter fun r => ‖r‖ < 1)) := by
  obtain ⟨x, hx, -, hxs⟩ := parity_prod _ _ rfl (roots_conjClosed p) h1
  have e := eval_one_mul_eval_neg_one p
  rw [hx, ← Complex.ofReal_mul] at e
  have e' := Complex.ofReal_injective e
  refine hxs.mp ?_
  by_contra hx'
  have : 0 ≤ p.leadingCoeff ^ 2 * x := mul_nonneg (sq_nonneg _) (not_lt.mp hx')
  linarith

/-! ### The roots of `det(λA₀ − A₁)` -/

/-- Woodford (2003), App. C.1 (tool): the roots of `det(λA₀ − A₁) = −λ C(λ)` are `0` and the roots
of `C`. -/
theorem roots_pencil {β σ κ r1 r2 fp fx : ℝ} (hp : charC β σ κ r1 r2 fp fx ≠ 0) :
    ((pencilPoly (A0g β σ) (A1g κ σ r1 r2 fp fx)).map Complex.ofRealHom).roots =
      0 ::ₘ ((charC β σ κ r1 r2 fp fx).map Complex.ofRealHom).roots := by
  rw [pencilPoly_eq, Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_X,
    roots_mul (mul_ne_zero (neg_ne_zero.mpr X_ne_zero)
      ((Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hp)), roots_neg, roots_X,
    Multiset.singleton_add]

/-- **Woodford (2003), §3.1, Ch. 4, fn 27 and App. C.1: the generalised Taylor principle is
necessary for determinacy within the family (3.7)** when `φπ ≥ 0`, `φₓ ≥ 0` and
`1 + ρ₁ + 2ρ₂ > 0` (in particular for the book's signs): for any expectation system on a
nonempty sample space, if (2.1), (3.1) and the rule (3.7) form a determinate system, then
`φπ + ρ₁ > 1`. -/
theorem gtp_necessary {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    {β σ κ r1 r2 fp fx : ℝ} (hβ0 : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (hfp : 0 ≤ fp)
    (hfx : 0 ≤ fx) (hr : 0 < 1 + r1 + 2 * r2)
    (hD : DeterminatePencilR 𝔼 (A0g β σ) (A1g κ σ r1 r2 fp fx)) :
    GTP β κ 2 (rho37 r1 r2) (pi37 fp) (x37 fx) := by
  rw [gtp37_iff]
  obtain ⟨-, hnu, hcnt, -⟩ := (determinatePencilR_iff_general 𝔼 _ _).mp hD
  set p := charC β σ κ r1 r2 fp fx with hpdef
  have hm1 : p.eval (-1) < 0 := by
    rw [hpdef, charC_neg_one]
    have h1 : 0 < (σ * κ + 2 * (1 + β)) * (1 + r1 + 2 * r2) := mul_pos (by positivity) hr
    have h2 : 0 ≤ σ * κ * fp := by positivity
    have h3 : 0 ≤ σ * fx * (1 + β) / 2 := by positivity
    linarith
  have hp0 : p ≠ 0 := fun h => by rw [h, eval_zero] at hm1; exact lt_irrefl 0 hm1
  have hroots := roots_pencil hp0
  have hp1 : ∀ r ∈ (p.map Complex.ofRealHom).roots, ‖r‖ ≠ 1 := fun r hr =>
    hnu r (by rw [hroots]; exact Multiset.mem_cons_of_mem hr)
  have hc2 : Multiset.card ((p.map Complex.ofRealHom).roots.filter fun r => ‖r‖ < 1) = 2 := by
    rw [hroots, Multiset.filter_cons_of_pos (p := fun r : ℂ => ‖r‖ < 1) _ (by simp),
      Multiset.card_cons] at hcnt
    simp at hcnt
    omega
  by_contra hg
  rcases (not_lt.mp hg).eq_or_lt with he | hlt
  · have h1 : p.eval 1 = 0 := by rw [hpdef, charC_one, he]; ring
    have hmem : (1 : ℂ) ∈ (p.map Complex.ofRealHom).roots := by
      rw [mem_roots ((Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hp0),
        IsRoot.def, eval_one_map, h1, map_zero]
    exact hp1 1 hmem (by simp)
  · have h1 : 0 < p.eval 1 := by
      rw [hpdef, charC_one]
      have : 0 < σ * κ := by positivity
      nlinarith
    have hodd := odd_inside p hp1 (by nlinarith)
    rw [hc2] at hodd
    exact (by decide : ¬ Odd 2) hodd

/-! ### Without sign restrictions the principle is not necessary -/

/-- Woodford (2003), §3.1 with `ρ₁ = ρ₂ = φₓ = 0` (the rule `i_t = i* + φπ π_t`): the quadratic
factor `Q(λ) = −βλ² + (1 + β + σκ)λ − (1 + σκφπ)` of `C(λ) = λ² Q(λ)`. -/
noncomputable def quadQ (β σ κ fp : ℝ) : ℝ[X] :=
  -(C β * X ^ 2) + C (1 + β + σ * κ) * X - C (1 + σ * κ * fp)

/-- Woodford (2003), §3.1: for `ρ₁ = ρ₂ = φₓ = 0`, `C(λ) = λ² Q(λ)`. -/
theorem charC_zero (β σ κ fp : ℝ) : charC β σ κ 0 0 fp 0 = X ^ 2 * quadQ β σ κ fp := by
  refine Polynomial.funext fun l => ?_
  rw [charC_eval]
  simp [quadQ]
  ring

/-- Woodford (2003), Ch. 4, Prop. 4.3's second region, for the rule `i_t = i* + φπ π_t`: if
`φπ < −1 − 2(1+β)/(σκ)` then `Q` has no root in the closed unit disc. -/
theorem quadQ_root_gt {β σ κ fp : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ)
    (hfp : fp < -1 - 2 * (1 + β) / (σ * κ)) {l : ℂ}
    (hl : ((quadQ β σ κ fp).map Complex.ofRealHom).eval l = 0) : 1 < ‖l‖ := by
  have hsk : 0 < σ * κ := mul_pos hσ hκ
  have hD : σ * κ * fp < -(σ * κ) - 2 * (1 + β) := by
    have := (lt_div_iff₀ hsk).mp (show fp + 1 < -(2 * (1 + β)) / (σ * κ) by
      rw [neg_div]; linarith)
    nlinarith
  simp only [quadQ, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_neg,
    Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, eval_add, eval_sub, eval_neg,
    eval_mul, eval_pow, eval_C, eval_X, Complex.ofRealHom_eq_coe] at hl
  have hre := congrArg Complex.re hl
  have him := congrArg Complex.im hl
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, pow_two, Complex.zero_re, Complex.add_im, Complex.sub_im,
    Complex.neg_im, Complex.mul_im, Complex.zero_im] at hre him
  by_contra hle
  push Not at hle
  have hn : l.re ^ 2 + l.im ^ 2 ≤ 1 := by
    have h1 := Complex.sq_norm l
    rw [Complex.normSq_apply] at h1
    nlinarith [norm_nonneg l]
  have hb : l.im = 0 := by
    have h1 : l.im * (1 + β + σ * κ - 2 * β * l.re) = 0 := by linarith
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exfalso
      have hre1 : l.re ≤ 1 := by nlinarith [sq_nonneg l.im]
      nlinarith
  rw [hb] at hre hn
  have ha1 : -1 ≤ l.re := by nlinarith
  have ha2 : l.re ≤ 1 := by nlinarith
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + l.re) (by linarith : (0 : ℝ) ≤ 1 - l.re)]

/-- Woodford (2003), §3.1 (tool): the pencil of the rule `i_t = i* + φπ π_t` is
`−λ³ Q(λ)`; its roots are `0` (three times) and the roots of `Q`. -/
theorem roots_pencil_zero {β σ κ fp : ℝ} (hQ : quadQ β σ κ fp ≠ 0) :
    ((pencilPoly (A0g β σ) (A1g κ σ 0 0 fp 0)).map Complex.ofRealHom).roots =
      0 ::ₘ 0 ::ₘ 0 ::ₘ ((quadQ β σ κ fp).map Complex.ofRealHom).roots := by
  have hC : charC β σ κ 0 0 fp 0 ≠ 0 := by
    rw [charC_zero]
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) hQ
  rw [roots_pencil hC, charC_zero, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero)
      ((Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hQ)), roots_X_pow,
    two_nsmul]
  simp [Multiset.singleton_add]

/-- Woodford (2003), §3.1 and App. C.1 (genericity for the rule `i_t = i* + φπ π_t`): a bounded
deterministic solution of `A₀ y_{t+1} = A₁ y_t` with `(i_{−1}, i_{−2}, x_{−1}) = 0` vanishes —
`(π, x)` obey `(π, x)_t = A (π, x)_{t+1}` with `A` Schur-stable, hence are `0`, and `i = φπ π`. -/
theorem generic_zero {β σ κ fp : ℝ} (hβ0 : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ)
    (hfp : fp < -1 - 2 * (1 + β) / (σ * κ)) :
    GenericPencil (A0g β σ) (A1g κ σ 0 0 fp 0) := by
  rintro v ⟨y, hy0, ⟨Cb, hC⟩, hrec⟩ hvX
  have hsk : 0 < σ * κ := mul_pos hσ hκ
  set D := 1 + σ * κ * fp with hDdef
  have hD : D < -(1 + 2 * β + σ * κ) := by
    have := (lt_div_iff₀ hsk).mp (show fp + 1 < -(2 * (1 + β)) / (σ * κ) by
      rw [neg_div]; linarith)
    rw [hDdef]
    nlinarith
  have hD0 : D ≠ 0 := by linarith
  have rows : ∀ t, β * y (t + 1) (Sum.inl 0) = y t (Sum.inl 0) - κ * y t (Sum.inl 1) ∧
      σ * y (t + 1) (Sum.inl 0) + y (t + 1) (Sum.inl 1) =
        y t (Sum.inl 1) + σ * y t (Sum.inl 2) ∧ y t (Sum.inl 2) = fp * y t (Sum.inl 0) := by
    intro t
    obtain ⟨h0, h1, h2, -⟩ := (pencil_rows β σ κ 0 0 fp 0 (y (t + 1)) (y t) 0).mp
      (by rw [add_zero]; exact hrec t)
    simp only [Pi.zero_apply, add_zero, zero_mul, zero_div, sub_zero] at h0 h1 h2
    exact ⟨h0, h1, by linarith⟩
  set A : Matrix (Fin 2) (Fin 2) ℝ :=
    !![(β + κ * σ) / D, κ / D; σ * (1 - β * fp) / D, 1 / D] with hA
  set z : ℕ → Fin 2 → Unit → ℝ := fun t i _ => ![y t (Sum.inl 0), y t (Sum.inl 1)] i with hz
  have hzs : perfectForesight.Solves A 0 z := by
    intro t i
    funext u
    obtain ⟨h0, h1, h2⟩ := rows t
    fin_cases i
    · change y t (Sum.inl 0) = (β + κ * σ) / D * y (t + 1) (Sum.inl 0) +
        κ / D * y (t + 1) (Sum.inl 1) + 0
      field_simp
      rw [hDdef]
      linear_combination (-1 : ℝ) * h0 - κ * h1 - κ * σ * h2
    · change y t (Sum.inl 1) = σ * (1 - β * fp) / D * y (t + 1) (Sum.inl 0) +
        1 / D * y (t + 1) (Sum.inl 1) + 0
      field_simp
      rw [hDdef]
      linear_combination (σ * fp) * h0 - (1 : ℝ) * h1 - σ * h2
  have hS : SchurStable (tr2 A) (det2 A) := by
    have htr : tr2 A = (1 + β + σ * κ) / D := by
      simp only [tr2, hA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      field_simp
      ring
    have hdet : det2 A = β / D := by
      simp only [det2, hA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      field_simp
      rw [hDdef]
      ring
    rw [htr, hdet]
    have hDn : D < 0 := by linarith
    constructor
    · rw [abs_lt, lt_div_iff_of_neg hDn, div_lt_iff_of_neg hDn]
      constructor <;> linarith
    · rw [abs_of_neg (div_neg_of_pos_of_neg (by linarith) hDn), ← neg_div,
        div_lt_iff_of_neg hDn, add_mul, one_mul, div_mul_cancel₀ _ hD0]
      linarith
  have hzero := perfectForesight.system_unique hS hzs
    (w := 0) (y := 0) (fun t i => by simp) (fun _ _ => rfl) (fun _ _ => rfl)
    ⟨Cb, fun t i u => by fin_cases i <;> exact hC t _⟩ ⟨0, fun _ _ _ => by simp⟩
  have hπ : ∀ t, y t (Sum.inl 0) = 0 := fun t => by
    have := congrFun (congrFun (congrFun hzero t) 0) ()
    simpa [hz] using this
  have hx : ∀ t, y t (Sum.inl 1) = 0 := fun t => by
    have := congrFun (congrFun (congrFun hzero t) 1) ()
    simpa [hz] using this
  rw [← hy0]
  funext k
  rcases k with k | j
  · fin_cases k
    · exact hπ 0
    · exact hx 0
    · change y 0 (Sum.inl 2) = 0
      rw [(rows 0).2.2, hπ 0, mul_zero]
  · rw [hy0]
    exact hvX j

/-- **Woodford (2003), §3.1 and Ch. 4, fn 27: without sign restrictions the generalised Taylor
principle is not necessary for determinacy within the family (3.7).** For `ρ₁ = ρ₂ = φₓ = 0` and
`φπ < −1 − 2(1+β)/(σκ)` (a strongly *negative* response to inflation), (2.1), (3.1), (3.7) form a
determinate system under every expectation system, although `φπ + ρ₁ − 1 < 0`. -/
theorem gtp_not_necessary {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω) {β σ κ fp : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ)
    (hfp : fp < -1 - 2 * (1 + β) / (σ * κ)) :
    DeterminatePencilR 𝔼 (A0g β σ) (A1g κ σ 0 0 fp 0) ∧
      ¬ GTP β κ 2 (rho37 0 0) (pi37 fp) (x37 0) := by
  have hsk : 0 < σ * κ := mul_pos hσ hκ
  have hfp1 : fp < -1 := by
    have : 0 < 2 * (1 + β) / (σ * κ) := by positivity
    linarith
  have hQ1 : 0 < (quadQ β σ κ fp).eval 1 := by
    simp only [quadQ, eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_X]
    nlinarith
  have hQ : quadQ β σ κ fp ≠ 0 := fun h => by rw [h, eval_zero] at hQ1; exact lt_irrefl 0 hQ1
  have hout : ∀ μ ∈ ((quadQ β σ κ fp).map Complex.ofRealHom).roots, 1 < ‖μ‖ := fun μ hμ =>
    quadQ_root_gt hβ0 hβ1 hσ hκ hfp ((mem_roots ((Polynomial.map_ne_zero_iff
      Complex.ofRealHom.injective).mpr hQ)).mp hμ)
  refine ⟨(determinatePencilR_iff_general 𝔼 _ _).mpr ⟨?_, ?_, ?_, generic_zero hβ0 hσ hκ hfp⟩,
    ?_⟩
  · rw [pencilPoly_eq, charC_zero]
    exact mul_ne_zero (neg_ne_zero.mpr X_ne_zero) (mul_ne_zero (pow_ne_zero _ X_ne_zero) hQ)
  · intro μ hμ
    rw [roots_pencil_zero hQ] at hμ
    simp only [Multiset.mem_cons] at hμ
    rcases hμ with rfl | rfl | rfl | hμ
    · simp
    · simp
    · simp
    · exact (hout μ hμ).ne'
  · rw [roots_pencil_zero hQ]
    have hf : ((quadQ β σ κ fp).map Complex.ofRealHom).roots.filter (fun r => ‖r‖ < 1) = 0 :=
      Multiset.filter_eq_nil.mpr fun μ hμ h => absurd h (not_lt.mpr (hout μ hμ).le)
    simp [hf]
  · rw [gtp37_iff]
    linarith

end Woodford.OptimalPolicyRules.TidyR6aTaylorNecessity
