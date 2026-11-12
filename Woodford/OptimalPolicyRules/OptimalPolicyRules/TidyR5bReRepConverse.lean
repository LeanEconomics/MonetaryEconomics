/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5bReRep
import OptimalPolicyRules.ExpectationsMeasure

/-!
# The exact criterion for uniqueness of `Λ` in Proposition 8.1 (p. 553 remark)

Woodford (2003), *Interest and Prices*, Chapter 8, Proposition 8.1 and the remark after it
(p. 553), that `Λ` and `Υ` are "uniquely defined".

`TidyR5bReRep.unique_of_powBdd` shows that `Λ`, `Υ` are unique when `Λ` is power-bounded and
(1.18) has one bounded solution; `TidyR5bReRep.jordan_nonunique` shows non-uniqueness for one
Jordan block on the circle. This module proves the **general converse** under perfect
foresight: whenever `Λ` is not power-bounded, some other representation of Proposition 8.1 has a
different `Λ` (and the same `Υ`). Together:

* `unique_iff_powBdd`: given one bounded solution of (1.18), `Λ` (equivalently the pair
  `(Λ, Υ)`) is the same in every representation **iff** `Λ` is power-bounded;
* `unique_iff_powBdd_of_assumption81`: the same under Assumption 8.1.

## The construction (`not_unique_of_not_powBdd`)

Let `V` (`bddOrb`) be the vectors whose `Λ`-orbit is bounded. If `Λ` is not power-bounded then
`V ≠ ⊤`, so some `w ≠ 0` annihilates `V`.

* If `Λ` is not a scalar matrix, some `u` makes `G = 1 + u w'` invertible and not commuting with
  `Λ`; `G` fixes `V` pointwise, so `Λ' = G Λ G⁻¹ ≠ Λ` has the same bounded homogeneous
  solutions, and `b_t = G q_t` blows up exactly when `q_t` does (`conj_rep`).
* If `Λ = c I` then `|c| > 1`; the only bounded homogeneous solution is zero for both `c I` and
  `2c I`, and every bounded forcing has a bounded forward solution (`scal_rep`).
-/

namespace Woodford.OptimalPolicyRules.TidyR5bReRepConverse

open Matrix GeneralSetup PencilSplit PencilEigen Prop81General
open TargetCriterion.Prop81 GeneralFOC GeneralFOC.LQ TidyR5bReRep

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-! ### Bounded orbits and power-boundedness -/

/-- Woodford (2003), p. 553 (tool): the vectors `m` whose orbit `Λᵏ m` is bounded. -/
def bddOrb (Λ : Matrix ιz ιz ℝ) : Submodule ℝ (ιz → ℝ) where
  carrier := {m | ∃ K, ∀ k i, |(Λ ^ k *ᵥ m) i| ≤ K}
  add_mem' := by
    rintro a b ⟨K1, h1⟩ ⟨K2, h2⟩
    refine ⟨K1 + K2, fun k i => ?_⟩
    rw [mulVec_add, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (h1 k i) (h2 k i))
  zero_mem' := ⟨0, fun k i => by simp⟩
  smul_mem' := by
    rintro c m ⟨K, h⟩
    refine ⟨|c| * K, fun k i => ?_⟩
    rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (h k i) (abs_nonneg c)

/-- Woodford (2003), p. 553 (tool): `Λ` is power-bounded (the entries of `Λᵏ` are bounded). -/
def PowBdd (Λ : Matrix ιz ιz ℝ) : Prop := ∃ K, ∀ k i j, |(Λ ^ k) i j| ≤ K

/-- Woodford (2003), p. 553 (tool): if every orbit is bounded, `Λ` is power-bounded. -/
theorem powBdd_of_top {Λ : Matrix ιz ιz ℝ} (h : bddOrb Λ = ⊤) : PowBdd Λ := by
  have hj : ∀ j : ιz, ∃ K, ∀ k i, |(Λ ^ k *ᵥ Pi.single j 1) i| ≤ K := fun j => by
    have : Pi.single j (1 : ℝ) ∈ bddOrb Λ := by rw [h]; trivial
    exact this
  choose K hK using hj
  refine ⟨∑ j, |K j|, fun k i j => ?_⟩
  have := hK j k i
  rw [mulVec_single_one] at this
  exact this.trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |K j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)))

/-- Woodford (2003), (1.20) (tool): a bounded homogeneous solution `D_{t+1} = Λ D_t` from `t₀`
has `D_t` in `bddOrb Λ` for every `t ≥ t₀`. -/
theorem mem_bddOrb_of_sol {Λ : Matrix ιz ιz ℝ} {t0 : ℕ} {D : ℕ → ιz → ℝ} (hD : BddS D)
    (h : ∀ t, t0 ≤ t → D (t + 1) = Λ *ᵥ D t) (t : ℕ) (ht : t0 ≤ t) : D t ∈ bddOrb Λ := by
  obtain ⟨K, hK⟩ := hD
  have hp : ∀ k, Λ ^ k *ᵥ D t = D (t + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, ← add_assoc, h _ (by omega)]
  exact ⟨K, fun k i => by rw [hp]; exact hK _ i⟩

/-! ### Conjugation by a matrix fixing the bounded orbits -/

/-- Woodford (2003), p. 553 (tool): if `G` (with inverse `Gi`) fixes every bounded-orbit vector
of `Λ`, then `G Λ Gi` has the same bounded homogeneous solutions as `Λ`. -/
theorem conj_homSame (t0 : ℕ) {Λ G Gi : Matrix ιz ιz ℝ} (hGGi : G * Gi = 1) (hGiG : Gi * G = 1)
    (hfix : ∀ v ∈ bddOrb Λ, G *ᵥ v = v) : HomSame t0 Λ (G * Λ * Gi) := by
  have hfix' : ∀ v ∈ bddOrb Λ, Gi *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hfix v hv]
    rw [mulVec_mulVec, hGiG, one_mulVec]
  intro D hD
  constructor
  · intro h t ht
    have h1 := mem_bddOrb_of_sol hD h t ht
    have h2 := mem_bddOrb_of_sol hD h (t + 1) (by omega)
    rw [← mulVec_mulVec, ← mulVec_mulVec, hfix' _ h1, ← h t ht, hfix _ h2]
  · intro h
    set E : ℕ → ιz → ℝ := fun t => Gi *ᵥ D t with hE
    have hEb : BddS E := by
      obtain ⟨K, hK⟩ := hD
      obtain ⟨K', hK'⟩ := exists_bound_mulVec Gi K
      exact ⟨K', fun t i => hK' _ (hK t) i⟩
    have hEs : ∀ t, t0 ≤ t → E (t + 1) = Λ *ᵥ E t := by
      intro t ht
      simp only [hE]
      rw [h t ht, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG,
        Matrix.one_mul]
    have hDE : ∀ t, t0 ≤ t → D t = E t := by
      intro t ht
      have := hfix _ (mem_bddOrb_of_sol hEb hEs t ht)
      simp only [hE] at this ⊢
      rw [mulVec_mulVec, hGGi, one_mulVec] at this
      exact this
    intro t ht
    rw [hDE t ht, hDE (t + 1) (by omega), hEs t ht]

/-- Woodford (2003), Proposition 8.1, p. 553 (**conjugated representation**, perfect
foresight): if `G` (inverse `Gi`) fixes the bounded orbits of `H.Λ`, then there is a
representation with `Λ' = G Λ Gi` and the same `Υ`. -/
theorem conj_rep {P : LQProblem ιZ ιz ιτ} {t0 : ℕ} (H : Prop81ConclusionM P perfectForesight t0)
    {G Gi : Matrix ιz ιz ℝ} (hGGi : G * Gi = 1) (hGiG : Gi * G = 1)
    (hfix : ∀ v ∈ bddOrb H.Λ, G *ᵥ v = v) :
    ∃ H' : Prop81ConclusionM P perfectForesight t0, H'.Λ = G * H.Λ * Gi ∧ H'.Υ = H.Υ := by
  refine ⟨reRep H (G * H.Λ * Gi) (conj_homSame t0 hGGi hGiG hfix)
    (fun x t => G *ᵥ H.Qop x t ()) (fun x hx _ => ?_) (fun x _ hs D hD hDs => ?_), rfl, rfl⟩
  · obtain ⟨K, hK⟩ := H.Qbounded x hx
    obtain ⟨K', hK'⟩ := exists_bound_mulVec G K
    exact ⟨K', fun t i => hK' _ (hK t ()) i⟩
  · refine hs ⟨fun t => Gi *ᵥ D t, ?_, fun t ht => ?_⟩
    · obtain ⟨K, hK⟩ := hD
      obtain ⟨K', hK'⟩ := exists_bound_mulVec Gi K
      exact ⟨K', fun t i => hK' _ (hK t) i⟩
    · change Gi *ᵥ D (t + 1) = H.Λ *ᵥ (Gi *ᵥ D t) + H.Qop x t ()
      rw [hDs t ht, mulVec_add, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hGiG, Matrix.one_mul, one_mulVec]

/-! ### The scalar case `Λ = c I`, `|c| > 1` -/

/-- Woodford (2003), (1.20) (tool): with `|c| > 1`, the only bounded homogeneous solution of
`D_{t+1} = c D_t` from `t₀` is zero from `t₀` on. -/
theorem zero_of_scalar {c : ℝ} (hc : 1 < |c|) {t0 : ℕ} {D : ℕ → ιz → ℝ} (hD : BddS D)
    (h : ∀ t, t0 ≤ t → D (t + 1) = (c • (1 : Matrix ιz ιz ℝ)) *ᵥ D t) (t : ℕ) (ht : t0 ≤ t) :
    D t = 0 := by
  obtain ⟨K, hK⟩ := mem_bddOrb_of_sol hD h t ht
  funext i
  by_contra hne
  have hpos : 0 < |D t i| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (K / |D t i|) hc
  have h1 := hK n i
  rw [smul_pow, one_pow, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_pow] at h1
  rw [div_lt_iff₀ hpos] at hn
  linarith

/-- Woodford (2003), (1.20) (tool): with `|c| > 1`, every bounded forcing `q` has a bounded
solution of `M_{t+1} = c M_t + q_t`, the forward sum `M_t = −∑_k c^{−k−1} q_{t+k}`. -/
theorem recSol_scalar {c : ℝ} (hc : 1 < |c|) (t0 : ℕ) {q : ℕ → ιz → ℝ} (hq : BddS q) :
    ∃ M, RecSol t0 (c • (1 : Matrix ιz ιz ℝ)) q M := by
  obtain ⟨K, hK⟩ := hq
  have hc0 : c ≠ 0 := fun h => by rw [h, abs_zero] at hc; linarith
  have ha : |c⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hc
  have hb : ∀ s i, |-c⁻¹ * q s i| ≤ |c⁻¹| * K := fun s i => by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hK s i) (abs_nonneg _)
  have hsum : ∀ t i, Summable fun k => c⁻¹ ^ k * (-c⁻¹ * q (t + k) i) := fun t i =>
    ExpectationsMeasure.MeasExpectationSystem.summable_geom_mul ha fun k => hb (t + k) i
  refine ⟨fun t i => ∑' k, c⁻¹ ^ k * (-c⁻¹ * q (t + k) i), ⟨_, fun t i =>
    ExpectationsMeasure.MeasExpectationSystem.abs_tsum_geom_mul_le ha fun k => hb (t + k) i⟩,
    fun t _ => ?_⟩
  funext i
  have hs := (hsum t i).tsum_eq_zero_add
  have e : ∑' k, c⁻¹ ^ (k + 1) * (-c⁻¹ * q (t + (k + 1)) i) =
      c⁻¹ * ∑' k, c⁻¹ ^ k * (-c⁻¹ * q (t + 1 + k) i) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
    ring
  rw [e, pow_zero, one_mul, add_zero] at hs
  beta_reduce
  rw [Pi.add_apply, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul, hs]
  field_simp
  ring

/-- Woodford (2003), Proposition 8.1, p. 553 (**scalar re-representation**, perfect
foresight): if `Λ = c I` with `|c| > 1`, then `Λ' = 2c I` (same `Υ`) is also a representation. -/
theorem scal_rep {P : LQProblem ιZ ιz ιτ} {t0 : ℕ} (H : Prop81ConclusionM P perfectForesight t0)
    {c : ℝ} (hΛ : H.Λ = c • 1) (hc : 1 < |c|) :
    ∃ H' : Prop81ConclusionM P perfectForesight t0, H'.Λ = (2 * c) • 1 ∧ H'.Υ = H.Υ := by
  have hc2 : 1 < |2 * c| := by rw [abs_mul, abs_two]; linarith
  have hsame : HomSame t0 H.Λ ((2 * c) • 1) := by
    intro D hD
    rw [hΛ]
    have key : ∀ (d : ℝ), 1 < |d| → (∀ t, t0 ≤ t → D (t + 1) = (d • (1 : Matrix ιz ιz ℝ)) *ᵥ D t) →
        ∀ (e : ℝ), ∀ t, t0 ≤ t → D (t + 1) = (e • (1 : Matrix ιz ιz ℝ)) *ᵥ D t := by
      intro d hd h e t ht
      rw [zero_of_scalar hd hD h t ht, zero_of_scalar hd hD h (t + 1) (by omega), mulVec_zero]
    exact ⟨fun h => key c hc h (2 * c), fun h => key (2 * c) hc2 h c⟩
  refine ⟨reRep H ((2 * c) • 1) hsame (fun _ _ => 0) (fun _ _ _ => ⟨0, fun _ _ => by simp⟩)
    (fun x hx hs => absurd ?_ hs), rfl, rfl⟩
  obtain ⟨K, hK⟩ := H.Qbounded x hx
  rw [hΛ]
  exact recSol_scalar hc t0 ⟨K, fun t i => hK t () i⟩

/-! ### The general converse -/

/-- Woodford (2003), p. 553 (tool): if every rank-one perturbation `e_i (w'Λ)` agrees with
`(Λ e_i) w'` (up to a nonzero scale `s`), and `w ≠ 0`, then `Λ` is a scalar matrix. -/
theorem scalar_of_comm {Λ : Matrix ιz ιz ℝ} {w : ιz → ℝ} {b : ιz} (hwb : w b ≠ 0)
    (h : ∀ i, ∃ s : ℝ, s ≠ 0 ∧
      vecMulVec (Pi.single i s) (w ᵥ* Λ) = vecMulVec (Λ *ᵥ Pi.single i s) w) :
    Λ = ((w ᵥ* Λ) b / w b) • 1 := by
  ext a i
  obtain ⟨s, hs, hi⟩ := h i
  have e := congrFun (congrFun hi a) b
  have hm : (Λ *ᵥ Pi.single i s) a = Λ a i * s := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [vecMulVec_apply, vecMulVec_apply, hm] at e
  rw [Matrix.smul_apply, smul_eq_mul]
  by_cases hai : a = i
  · subst hai
    rw [Pi.single_eq_same] at e
    rw [Matrix.one_apply_eq, mul_one, eq_div_iff hwb]
    have h0 : s * (Λ a a * w b - (w ᵥ* Λ) b) = 0 := by linear_combination (-1 : ℝ) * e
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hs
    · linarith
  · rw [Pi.single_eq_of_ne hai, zero_mul] at e
    rw [Matrix.one_apply_ne hai, mul_zero]
    have : Λ a i * s * w b = 0 := e.symm
    rcases mul_eq_zero.mp this with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 hs
    · exact absurd h1 hwb

/-- Woodford (2003), p. 553, the remark after Proposition 8.1 (**general converse**, perfect
foresight): if `Λ` is **not** power-bounded, then some other representation of Proposition 8.1
has a different `Λ'` (and the same `Υ`). So the remark's uniqueness of `Λ` fails exactly off the
power-bounded case. -/
theorem not_unique_of_not_powBdd {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : Prop81ConclusionM P perfectForesight t0) (hnp : ¬ PowBdd H.Λ) :
    ∃ H' : Prop81ConclusionM P perfectForesight t0, H'.Λ ≠ H.Λ ∧ H'.Υ = H.Υ := by
  have hne : Nonempty ιz := by
    by_contra h0
    exact hnp ⟨0, fun _ i => absurd ⟨i⟩ h0⟩
  obtain ⟨i0⟩ := hne
  by_cases hsc : ∃ c : ℝ, H.Λ = c • 1
  · obtain ⟨c, hc⟩ := hsc
    have hc1 : 1 < |c| := by
      by_contra hle
      push Not at hle
      refine hnp ⟨1, fun k i j => ?_⟩
      rw [hc, smul_pow, one_pow, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, abs_mul,
        abs_pow]
      have h1 : |c| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg c) hle
      split_ifs <;> simp [h1]
    obtain ⟨H', h1, h2⟩ := scal_rep H hc hc1
    refine ⟨H', fun h => ?_, h2⟩
    have e := congrFun (congrFun (h1.symm.trans (h.trans hc)) i0) i0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e
    have hc0 : c ≠ 0 := fun h0 => by rw [h0, abs_zero] at hc1; linarith
    exact hc0 (by linarith)
  · have hlt : bddOrb H.Λ < ⊤ := lt_top_iff_ne_top.mpr fun h => hnp (powBdd_of_top h)
    obtain ⟨f, hf0, hfV⟩ := (bddOrb H.Λ).exists_le_ker_of_lt_top hlt
    set w : ιz → ℝ := fun i => f (Pi.single i 1) with hw
    have hwf : ∀ v, w ⬝ᵥ v = f v := by
      intro v
      conv_rhs => rw [pi_eq_sum_univ v]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, dotProduct, hw]
      exact Finset.sum_congr rfl fun i _ => by
        rw [mul_comm]
        congr 2
        funext j
        simp only [Pi.single_apply, eq_comm]
    have hw0 : ∃ b, w b ≠ 0 := by
      by_contra hall
      push Not at hall
      refine hf0 (LinearMap.ext fun v => ?_)
      rw [← hwf, LinearMap.zero_apply, dotProduct]
      exact Finset.sum_eq_zero fun i _ => by rw [hall i, zero_mul]
    obtain ⟨b, hb⟩ := hw0
    have hnc : ∃ i, ∀ s : ℝ, s ≠ 0 →
        vecMulVec (Pi.single i s) (w ᵥ* H.Λ) ≠ vecMulVec (H.Λ *ᵥ Pi.single i s) w := by
      by_contra hall
      push Not at hall
      exact hsc ⟨_, scalar_of_comm hb hall⟩
    obtain ⟨i, hi⟩ := hnc
    obtain ⟨s, hs0, hsdet⟩ : ∃ s : ℝ, s ≠ 0 ∧ 1 + w i * s ≠ 0 := by
      by_cases h1 : 1 + w i * 1 = 0
      · refine ⟨2, two_ne_zero, ?_⟩
        intro h2
        linarith
      · exact ⟨1, one_ne_zero, h1⟩
    set u : ιz → ℝ := Pi.single i s with hu
    set G : Matrix ιz ιz ℝ := 1 + vecMulVec u w with hG
    have hdet : IsUnit G.det := by
      rw [hG, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, hu,
        dotProduct_single]
      exact isUnit_iff_ne_zero.mpr hsdet
    have hfix : ∀ v ∈ bddOrb H.Λ, G *ᵥ v = v := by
      intro v hv
      have h0 : w ⬝ᵥ v = 0 := by rw [hwf]; exact hfV hv
      rw [hG, add_mulVec, one_mulVec]
      conv_rhs => rw [← add_zero v]
      congr 1
      funext a
      simp only [mulVec, dotProduct, vecMulVec_apply, Pi.zero_apply, mul_assoc,
        ← Finset.mul_sum]
      rw [show (∑ x, w x * v x) = w ⬝ᵥ v from rfl, h0, mul_zero]
    obtain ⟨H', h1, h2⟩ := conj_rep H (mul_nonsing_inv G hdet) (nonsing_inv_mul G hdet) hfix
    refine ⟨H', fun h => hi s hs0 ?_, h2⟩
    have hcomm : G * H.Λ = H.Λ * G := by
      calc G * H.Λ = G * H.Λ * G⁻¹ * G := by
            rw [Matrix.mul_assoc _ G⁻¹, nonsing_inv_mul G hdet, Matrix.mul_one]
        _ = H.Λ * G := by rw [← h1, h]
    rw [hG, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, vecMulVec_mul,
      mul_vecMulVec] at hcomm
    exact add_left_cancel hcomm

/-! ### The exact criterion -/

/-- Woodford (2003), p. 553, the remark after Proposition 8.1 (**exact criterion**, perfect
foresight): if (1.18) has one bounded solution, then `Λ` and `Υ` are the same in every
representation **iff** `Λ` is power-bounded (`TidyR5bReRep.unique_of_powBdd` and
`not_unique_of_not_powBdd`). -/
theorem unique_iff_powBdd {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : Prop81ConclusionM P perfectForesight t0) {y0 : ℕ → Unit → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ0 : ℕ → Unit → ιZ ⊕ ιz → ℝ} (hy0b : BoundedV y0) (hy0a : AdaptedV perfectForesight y0)
    (hφ0b : BoundedV φ0) (hφ0k : MultKnown perfectForesight t0 φ0)
    (h118 : Eq118 P perfectForesight t0 y0 φ0) :
    (∀ H' : Prop81ConclusionM P perfectForesight t0, H'.Λ = H.Λ ∧ H'.Υ = H.Υ) ↔
      PowBdd H.Λ := by
  constructor
  · intro hall
    by_contra hnp
    obtain ⟨H', h1, -⟩ := not_unique_of_not_powBdd H hnp
    exact h1 (hall H').1
  · intro hpb H'
    obtain ⟨h1, h2⟩ := unique_of_powBdd H H' hy0b hy0a hφ0b hφ0k h118 hpb
    exact ⟨h1.symm, h2.symm⟩

/-- Woodford (2003), p. 553 (**exact criterion for `Λ` alone**, perfect foresight): with one
bounded solution of (1.18), `Λ` is unique iff it is power-bounded. -/
theorem uniqueΛ_iff_powBdd {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : Prop81ConclusionM P perfectForesight t0) {y0 : ℕ → Unit → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ0 : ℕ → Unit → ιZ ⊕ ιz → ℝ} (hy0b : BoundedV y0) (hy0a : AdaptedV perfectForesight y0)
    (hφ0b : BoundedV φ0) (hφ0k : MultKnown perfectForesight t0 φ0)
    (h118 : Eq118 P perfectForesight t0 y0 φ0) :
    (∀ H' : Prop81ConclusionM P perfectForesight t0, H'.Λ = H.Λ) ↔ PowBdd H.Λ := by
  constructor
  · intro hall
    by_contra hnp
    obtain ⟨H', h1, -⟩ := not_unique_of_not_powBdd H hnp
    exact h1 (hall H')
  · intro hpb H'
    exact ((unique_iff_powBdd H hy0b hy0a hφ0b hφ0k h118).mpr hpb H').1

/-- Woodford (2003), p. 553 (**exact criterion under Assumption 8.1**, perfect foresight): `Λ`
and `Υ` are the same in every representation of Proposition 8.1 iff `Λ` is power-bounded. -/
theorem unique_iff_powBdd_of_assumption81 {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (hA : Assumption81 P perfectForesight t0) (H : Prop81ConclusionM P perfectForesight t0) :
    (∀ H' : Prop81ConclusionM P perfectForesight t0, H'.Λ = H.Λ ∧ H'.Υ = H.Υ) ↔
      PowBdd H.Λ := by
  obtain ⟨y, φ, hy, hya, hφ, hφk, h118⟩ := Prop83.exists_base_of_assumption81 hA
  exact unique_iff_powBdd H hy hya hφ hφk h118

end Woodford.OptimalPolicyRules.TidyR5bReRepConverse
