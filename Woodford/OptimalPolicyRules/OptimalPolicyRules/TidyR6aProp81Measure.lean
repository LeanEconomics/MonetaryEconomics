/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR6aReRepMeasure
import OptimalPolicyRules.TidyR5aMeasBK

/-!
# Proposition 8.1 on the conditional-expectation model

Woodford (2003), *Interest and Prices*, Chapter 8, Section 1.4, Proposition 8.1 (pp. 552–553,
(1.18)–(1.21)) with Appendix G.1 (pp. 716–718), on a filtered probability space with Mathlib's
conditional expectation.

`Prop81General.prop81` builds a representation from a real deflating pair
(`PencilSplit.DeflatingSplit`) for every exact expectation system. Here the same construction is
carried out with `condExp`, giving an inhabitant of `TidyR6aReRepMeasure.MProp81Conclusion` on
**every** probability space (`mprop81`), with the explicit matrices `Λ = β⁻¹K⁻¹Ẽ'` and
`Υ = −(J₁')⁻¹J₂'Ẽ'` (`mprop81_matrices`):

* `mRop`: `r_t = (J₁')⁻¹ E_t ∑_k (βΨ')ᵏ βJ'x_{t+k}` (the forward sum `TidyR5aMeasBK.fwdM`);
* `mQop`: `q_t = −K⁻¹(E_t x^z_t + A₁₂'E_t r_{t+1})`;
* `mprop81_equiv`: the equivalence (1.18) ⟺ (1.20) ∧ (1.21) almost surely, for essentially
  bounded adapted plans and essentially bounded a.e.-measurable multipliers with `M_t` known at
  `t`. The step "(1.18) ⟹ `w_t = J'Î'φ_t` is the forward sum" uses the a.s. forward uniqueness
  `OptimalRulesMeasureQuasiSplit.m_fwd_zero`.

So the criterion `TidyR6aReRepMeasure.munique_iff_powBdd` applies to `mprop81`
(`mprop81_unique_iff`): the representation built from a deflating split is the only one iff its
`Λ` is power-bounded.
-/

namespace Woodford.OptimalPolicyRules.TidyR6aProp81Measure

open MeasureTheory Filter Matrix GeneralSetup Prop81General TargetCriterion.Prop81 GeneralFOC
open GeneralFOC.LQ PencilSplit ExpectationsMeasure OptimalRulesMeasure TidyR6aReRepMeasure
open TidyR5bReRepConverse

variable {Ω : Type*} [MeasurableSpace Ω] {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz]
  [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz]

/-! ### The operators -/

/-- Woodford (2003), eq. (1.21), p. 553, with conditional expectations: the operator
`E_t R(L⁻¹)`, `r_t = (J₁')⁻¹ E_t ∑_{k ≥ 0} (βΨ')ᵏ βJ'x_{t+k}`. -/
noncomputable def mRop (S : MeasExpectationSystem Ω) {Sy : LinearRESystem ιZ ιz} {β : ℝ}
    (D : DeflatingSplit Sy β) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) : ℕ → Ω → ιZ → ℝ :=
  fun t ω => ((J1 D.J)ᵀ)⁻¹ *ᵥ TidyR5aMeasBK.fwdM S (β • D.Ψᵀ) (fpart β D.J x) t ω

/-- Woodford (2003), eq. (1.20), p. 553, with conditional expectations: the operator
`E_t Q(L⁻¹)`, `q_t = −K⁻¹(E_t x^z_t + A₁₂' E_t r_{t+1})`. -/
noncomputable def mQop (S : MeasExpectationSystem Ω) {Sy : LinearRESystem ιZ ιz} {β : ℝ}
    (D : DeflatingSplit Sy β) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) : ℕ → Ω → ιz → ℝ :=
  fun t ω => -((Kmat Sy D.J)⁻¹ *ᵥ (EVm S t (fun ω' => Mpart (x t ω')) ω +
    Sy.A12ᵀ *ᵥ EVm S t (mRop S D x (t + 1)) ω))

/-! ### Tools -/

omit [DecidableEq ιZ] in
/-- Woodford (2003), p. 553 (tool): `x = T̃'W(τ − τ*)` of an adapted plan is adapted. -/
theorem madaptedV_xproc {S : MeasExpectationSystem Ω} (P : LQProblem ιZ ιz ιτ)
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MAdaptedV S y) : MAdaptedV S (xproc P y) :=
  fun t i => sm_comp (hy t) (g := fun v => (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar))) i)
    ((continuous_apply i).comp (continuous_const.matrix_mulVec (continuous_const.matrix_mulVec
      ((continuous_const.matrix_mulVec continuous_id).sub continuous_const))))

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): a fixed matrix applied to a random vector with integrable
components has integrable components. -/
theorem integrable_mulVec' {S : MeasExpectationSystem Ω} {κ ι : Type*} [Fintype ι]
    (A : Matrix κ ι ℝ) {x : Ω → ι → ℝ} (hx : ∀ j, Integrable (fun ω => x ω j) S.μ) (i : κ) :
    Integrable (fun ω => (A *ᵥ x ω) i) S.μ := by
  have e : (fun ω => (A *ᵥ x ω) i) = fun ω => ∑ j, A i j * x ω j := by
    funext ω
    simp [mulVec, dotProduct]
  rw [e]
  exact integrable_finsetSum _ fun j _ => (hx j).const_mul _

/-- Woodford (2003), (1.18) and (G.4) (tool, pointwise): `J'` times the left side of (1.18) is
`Ψ'(J'Î'e) + J'x − β⁻¹ J'Î'u`. -/
theorem J_lhs {Sy : LinearRESystem ιZ ιz} {J : Matrix (ιZ ⊕ ιz) ιZ ℝ}
    {Ψ : Matrix ιZ ιZ ℝ} (hd : Sy.Ahat * J = Sy.Ihat * J * Ψ) (β : ℝ) (e xx u : ιZ ⊕ ιz → ℝ) :
    Jᵀ *ᵥ (Sy.Ahatᵀ *ᵥ e + xx - β⁻¹ • (Sy.Ihatᵀ *ᵥ u)) =
      Ψᵀ *ᵥ ((Jᵀ * Sy.Ihatᵀ) *ᵥ e) + Jᵀ *ᵥ xx - β⁻¹ • ((Jᵀ * Sy.Ihatᵀ) *ᵥ u) := by
  rw [mulVec_sub, mulVec_add, deflate_transpose hd, mulVec_smul, ← mulVec_mulVec,
    ← mulVec_mulVec]

/-- Woodford (2003), (1.18) (tool, pointwise): the `z`-rows of the left side of (1.18). -/
theorem Mpart_lhs (Sy : LinearRESystem ιZ ιz) (β : ℝ) (e xx u : ιZ ⊕ ιz → ℝ) :
    Mpart (Sy.Ahatᵀ *ᵥ e + xx - β⁻¹ • (Sy.Ihatᵀ *ᵥ u)) =
      Sy.A12ᵀ *ᵥ ξpart e + Sy.A22ᵀ *ᵥ Mpart e + Mpart xx - β⁻¹ • (Sy.Etᵀ *ᵥ Mpart u) := by
  rw [Ahat_transpose_mulVec, Ihat_transpose_mulVec]
  rfl

/-! ### Proposition 8.1 -/

/-- **Woodford (2003), Proposition 8.1, p. 553, on a probability space (the equivalence)**: for a
real deflating pair, essentially bounded adapted plans and essentially bounded a.e.-measurable
multipliers with `M_t` known at `t` satisfy (1.18) a.s. for all `t ≥ t₀` iff they satisfy (1.20)
with `Λ = β⁻¹K⁻¹Ẽ'` and (1.21) with `Υ = −(J₁')⁻¹J₂'Ẽ'` a.s., with the operators `mQop`,
`mRop`. -/
theorem mprop81_equiv (P : LQProblem ιZ ιz ιτ) (D : DeflatingSplit P.sys P.β)
    (S : MeasExpectationSystem Ω) (t0 : ℕ) :
    MProp81Equiv S P t0 (Λmat P.sys P.β D.J) (Υmat P.sys D.J) (mQop S D) (mRop S D) := by
  intro y φ hyb hya hφb hφa hφk
  set x := xproc P y with hx
  have hxb : MBoundedV S x := mboundedV_xproc P hyb
  have hxa : MAdaptedV S x := madaptedV_xproc P hya
  set G : Matrix ιZ ιZ ℝ := P.β • D.Ψᵀ with hGdef
  have hG : PowDecay G := D.powDecay_G P.β_pos
  set f := fpart P.β D.J x with hf
  have hfb : MBoundedV S f := by
    obtain ⟨K, hK⟩ := hxb
    obtain ⟨K', hK'⟩ := exists_bound_mulVec (P.β • D.Jᵀ) K
    exact ⟨K', fun t => (hK t).mono fun _ h i => hK' _ h i⟩
  have hfa : MAdaptedV S f := fun t => mknownV_mulVec (P.β • D.Jᵀ) (hxa t)
  set F := TidyR5aMeasBK.fwdM S G f with hF
  have hFrec := TidyR5aMeasBK.fwdM_rec hG hfb hfa
  have hFb : MBoundedV S F := TidyR5aMeasBK.fwdM_bdd hG hfb
  have hFi : ∀ t i, Integrable (fun ω => F t ω i) S.μ := fun t i => S.integrable_E t _
  have hφi : ∀ s i, Integrable (fun ω => φ s ω i) S.μ := integrable_comp hφb hφa
  have hβ : P.β ≠ 0 := P.β_pos.ne'
  set w : ℕ → Ω → ιZ → ℝ := fun t ω => (D.Jᵀ * P.sys.Ihatᵀ) *ᵥ φ t ω with hw
  have hwi : ∀ s i, Integrable (fun ω => w s ω i) S.μ := fun s =>
    integrable_mulVec' (D.Jᵀ * P.sys.Ihatᵀ) (hφi s)
  have hEw : ∀ t, ∀ᵐ ω ∂S.μ, EVm S t (w (t + 1)) ω =
      (D.Jᵀ * P.sys.Ihatᵀ) *ᵥ EVm S t (φ (t + 1)) ω := fun t =>
    EVm_mulVec S t _ (hφi (t + 1))
  set L : ℕ → Ω → ιZ ⊕ ιz → ℝ := fun t ω => P.sys.Ahatᵀ *ᵥ EVm S t (φ (t + 1)) ω + x t ω -
    P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ φ t ω) with hL
  have h118L : MEq118 S P t0 y φ ↔ ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, L t ω = 0 := Iff.rfl
  -- the `z`-rows once (1.21) holds at `t + 1`
  have hMrows : ∀ t, t0 ≤ t → MEq121 S t0 (Υmat P.sys D.J) (mRop S D x) φ →
      ∀ᵐ ω ∂S.μ, Mpart (L t ω) = Kmat P.sys D.J *ᵥ Mpart (φ (t + 1) ω) +
        P.sys.A12ᵀ *ᵥ EVm S t (mRop S D x (t + 1)) ω +
        EVm S t (fun ω' => Mpart (x t ω')) ω - P.β⁻¹ • (P.sys.Etᵀ *ᵥ Mpart (φ t ω)) := by
    intro t ht h121
    have hRi : ∀ i, Integrable (fun ω => mRop S D x (t + 1) ω i) S.μ :=
      integrable_mulVec' ((J1 D.J)ᵀ)⁻¹ (hFi (t + 1))
    have hMi : ∀ i, Integrable (fun ω => Mpart (φ (t + 1) ω) i) S.μ := fun i => hφi _ _
    have hξ := EVm_congr (S := S) t (h121 (t + 1) (by omega))
    have hadd := EVm_add (S := S) t (integrable_mulVec' (Υmat P.sys D.J) hMi) hRi
    have hmul := EVm_mulVec S t (Υmat P.sys D.J) hMi
    have hM : EVm S t (fun ω' => Mpart (φ (t + 1) ω')) = fun ω' => Mpart (φ (t + 1) ω') :=
      EVm_of_known (hφk t ht) hMi
    have hxz : EVm S t (fun ω' => Mpart (x t ω')) = fun ω' => Mpart (x t ω') :=
      EVm_of_known (fun i => hxa t (Sum.inr i))
        (fun i => OptimalRulesMeasureMarkov.integrable_of_adapted hxb hxa t (Sum.inr i))
    filter_upwards [hξ, hadd, hmul] with ω e1 e2 e3
    have hξE : ξpart (EVm S t (φ (t + 1)) ω) =
        EVm S t (fun ω' => ξpart (φ (t + 1) ω')) ω := rfl
    have hME : Mpart (EVm S t (φ (t + 1)) ω) =
        EVm S t (fun ω' => Mpart (φ (t + 1) ω')) ω := rfl
    rw [hL]
    simp only
    rw [Mpart_lhs, hξE, hME, e1, e2, e3, hM, hxz, Kmat, add_mulVec, mulVec_add,
      ← mulVec_mulVec]
    abel
  constructor
  · intro h118
    have hweq : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, w t ω = G *ᵥ EVm S t (w (t + 1)) ω + f t ω := by
      intro t ht
      filter_upwards [h118 t ht, hEw t] with ω e1 e2
      have h0 := congrArg (D.Jᵀ *ᵥ ·) e1
      simp only [mulVec_zero] at h0
      rw [J_lhs D.deflate, sub_eq_zero] at h0
      change D.Ψᵀ *ᵥ ((D.Jᵀ * P.sys.Ihatᵀ) *ᵥ EVm S t (φ (t + 1)) ω) + D.Jᵀ *ᵥ x t ω =
        P.β⁻¹ • ((D.Jᵀ * P.sys.Ihatᵀ) *ᵥ φ t ω) at h0
      rw [e2, hGdef, hf, fpart, smul_mulVec, smul_mulVec, ← smul_add, h0, smul_smul,
        mul_inv_cancel₀ hβ, one_smul]
    have hwb : MBoundedV S w := by
      obtain ⟨K, hK⟩ := hφb
      obtain ⟨K', hK'⟩ := exists_bound_mulVec (D.Jᵀ * P.sys.Ihatᵀ) K
      exact ⟨K', fun t => (hK t).mono fun _ h i => hK' _ h i⟩
    set d : ℕ → Ω → ιZ → ℝ := fun t ω => w t ω - F t ω with hd
    have hdb : MBoundedV S d := by
      obtain ⟨K1, h1⟩ := hwb
      obtain ⟨K2, h2⟩ := hFb
      exact ⟨K1 + K2, fun t => by
        filter_upwards [h1 t, h2 t] with ω a b i
        exact (abs_sub _ _).trans (add_le_add (a i) (b i))⟩
    have hdrec : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, d t ω = G *ᵥ EVm S t (d (t + 1)) ω := by
      intro t ht
      have hE := OptimalRulesMeasureMarkov.EVm_affine3 S t (1 : Matrix ιZ ιZ ℝ)
        (-1 : Matrix ιZ ιZ ℝ) (0 : Matrix ιZ ιZ ℝ) 0 (hwi (t + 1)) (hFi (t + 1)) (hwi (t + 1))
      filter_upwards [hweq t ht, hFrec t, hE] with ω e1 e2 e3
      have e4 : EVm S t (d (t + 1)) ω = EVm S t (w (t + 1)) ω - EVm S t (F (t + 1)) ω := by
        have hfun : d (t + 1) = fun ω => (1 : Matrix ιZ ιZ ℝ) *ᵥ w (t + 1) ω +
            (-1 : Matrix ιZ ιZ ℝ) *ᵥ F (t + 1) ω + (0 : Matrix ιZ ιZ ℝ) *ᵥ w (t + 1) ω + 0 := by
          funext ω'
          rw [one_mulVec, neg_mulVec, one_mulVec, zero_mulVec, add_zero, add_zero,
            ← sub_eq_add_neg]
        rw [hfun, e3, one_mulVec, neg_mulVec, one_mulVec, zero_mulVec, add_zero, add_zero,
          ← sub_eq_add_neg]
      change F t ω = f t ω + G *ᵥ EVm S t (F (t + 1)) ω at e2
      change w t ω - F t ω = _
      rw [e4, e1, e2, mulVec_sub]
      abel
    have hwF : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, w t ω = F t ω := fun t ht =>
      (OptimalRulesMeasureQuasiSplit.m_fwd_zero hG hdb hdrec t ht).mono fun ω h =>
        sub_eq_zero.mp h
    have h121 : MEq121 S t0 (Υmat P.sys D.J) (mRop S D x) φ := by
      intro t ht
      filter_upwards [hwF t ht] with ω e
      refine (eq121_iff P.sys D.J1_det _ _ _).mpr ?_
      rw [← w_split]
      exact e
    refine ⟨fun t ht => ?_, h121⟩
    filter_upwards [h118 t ht, hMrows t ht h121] with ω e1 e2
    refine (eq120_iff P.sys P.β D.K_det _ _ _ _).mpr ?_
    rw [← e2]
    exact congrArg Mpart e1
  · rintro ⟨h120, h121⟩
    rw [h118L]
    intro t ht
    have hwF : ∀ s, t0 ≤ s → ∀ᵐ ω ∂S.μ, w s ω = F s ω := fun s hs =>
      (h121 s hs).mono fun ω h => by
        have := (eq121_iff P.sys D.J1_det _ _ _).mp h
        rw [← w_split] at this
        exact this
    filter_upwards [hMrows t ht h121, h120 t ht, hwF t ht, hEw t,
      EVm_congr (S := S) t (hwF (t + 1) (by omega)), hFrec t] with ω e1 e2 e3 e4 e5 e6
    change F t ω = f t ω + G *ᵥ EVm S t (F (t + 1)) ω at e6
    have hz : Mpart (L t ω) = 0 := by
      rw [e1]
      exact (eq120_iff P.sys P.β D.K_det _ _ _ _).mp e2
    have hJ : D.Jᵀ *ᵥ L t ω = 0 := by
      rw [hL]
      simp only
      rw [J_lhs D.deflate, ← e4, e5]
      change D.Ψᵀ *ᵥ EVm S t (F (t + 1)) ω + D.Jᵀ *ᵥ x t ω - P.β⁻¹ • w t ω = 0
      rw [e3, e6, hGdef, hf, fpart, smul_mulVec, smul_mulVec, ← smul_add, smul_smul,
        inv_mul_cancel₀ hβ, one_smul, add_comm, sub_self]
    rw [J_transpose_mulVec] at hJ
    change (J1 D.J)ᵀ *ᵥ ξpart (L t ω) + (J2 D.J)ᵀ *ᵥ Mpart (L t ω) = 0 at hJ
    rw [hz, mulVec_zero, add_zero] at hJ
    have hdet : ((J1 D.J)ᵀ).det ≠ 0 := by rw [det_transpose]; exact D.J1_det
    have hZ := eq_zero_of_mulVec_eq_zero hdet hJ
    funext a
    rcases a with i | r
    · exact congrFun hZ i
    · exact congrFun hz r

/-- Woodford (2003), Proposition 8.1, p. 553, on a probability space: `E_t R(L⁻¹)` maps
essentially bounded processes to essentially bounded processes. -/
theorem mRop_bdd (S : MeasExpectationSystem Ω) {Sy : LinearRESystem ιZ ιz} {β : ℝ}
    (hβ : 0 < β) (D : DeflatingSplit Sy β) {x : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hx : MBoundedV S x) :
    MBoundedV S (mRop S D x) := by
  have hfb : MBoundedV S (fpart β D.J x) := by
    obtain ⟨K, hK⟩ := hx
    obtain ⟨K', hK'⟩ := exists_bound_mulVec (β • D.Jᵀ) K
    exact ⟨K', fun t => (hK t).mono fun _ h i => hK' _ h i⟩
  obtain ⟨KF, hKF⟩ := TidyR5aMeasBK.fwdM_bdd (D.powDecay_G hβ) hfb
  obtain ⟨K', hK'⟩ := exists_bound_mulVec ((J1 D.J)ᵀ)⁻¹ KF
  exact ⟨K', fun t => (hKF t).mono fun _ h i => hK' _ h i⟩

/-- Woodford (2003), Proposition 8.1, p. 553, on a probability space: `E_t R(L⁻¹)x` is known at
`t` for every `x`. -/
theorem mRop_adapted (S : MeasExpectationSystem Ω) {Sy : LinearRESystem ιZ ιz} {β : ℝ}
    (D : DeflatingSplit Sy β) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) : MAdaptedV S (mRop S D x) :=
  fun t => mknownV_mulVec _ (TidyR5aMeasBK.fwdM_adapted S _ _ t)

/-- Woodford (2003), Proposition 8.1, p. 553, on a probability space: `E_t Q(L⁻¹)` maps
essentially bounded processes to essentially bounded processes. -/
theorem mQop_bdd (S : MeasExpectationSystem Ω) {Sy : LinearRESystem ιZ ιz} {β : ℝ}
    (hβ : 0 < β) (D : DeflatingSplit Sy β) {x : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hx : MBoundedV S x) :
    MBoundedV S (mQop S D x) := by
  obtain ⟨Kx, hKx⟩ := hx
  obtain ⟨KR, hKR⟩ := mRop_bdd S hβ D ⟨Kx, hKx⟩
  have h1 : ∀ t, ∀ᵐ ω ∂S.μ, ∀ r, |EVm S t (fun ω' => Mpart (x t ω')) ω r| ≤ Kx := fun t =>
    ae_all_iff.mpr fun r => S.abs_E_le ((hKx t).mono fun _ h => h (Sum.inr r)) t
  have h2 : ∀ t, ∀ᵐ ω ∂S.μ, ∀ i, |EVm S t (mRop S D x (t + 1)) ω i| ≤ KR := fun t =>
    ae_all_iff.mpr fun i => S.abs_E_le ((hKR (t + 1)).mono fun _ h => h i) t
  obtain ⟨KA, hKA⟩ := exists_bound_mulVec Sy.A12ᵀ KR
  obtain ⟨K, hK⟩ := exists_bound_mulVec (Kmat Sy D.J)⁻¹ (Kx + KA)
  refine ⟨K, fun t => ?_⟩
  filter_upwards [h1 t, h2 t] with ω a b r
  change |(-((Kmat Sy D.J)⁻¹ *ᵥ _)) r| ≤ K
  rw [Pi.neg_apply, abs_neg]
  exact hK _ (fun j => (abs_add_le _ _).trans (add_le_add (a j) (hKA _ b j))) r

/-- Woodford (2003), Proposition 8.1, p. 553, on a probability space: `E_t Q(L⁻¹)x` is known at
`t` for every `x`. -/
theorem mQop_adapted (S : MeasExpectationSystem Ω) {Sy : LinearRESystem ιZ ιz} {β : ℝ}
    (D : DeflatingSplit Sy β) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) : MAdaptedV S (mQop S D x) :=
  fun t r => sm_comp₂ (fun _ => S.stronglyMeasurable_E t _) (fun _ => S.stronglyMeasurable_E t _)
    (g := fun p => (-((Kmat Sy D.J)⁻¹ *ᵥ (p.1 + Sy.A12ᵀ *ᵥ p.2))) r)
    ((continuous_apply r).comp ((continuous_const.matrix_mulVec (continuous_fst.add
      (continuous_const.matrix_mulVec continuous_snd))).neg))

/-- **Woodford (2003), Proposition 8.1, p. 553, on the conditional-expectation model**: a real
deflating pair for `n_Z` roots of (1.15) inside `|μ| < β⁻¹` yields `Λ`, `Υ`, `Q(L⁻¹)`, `R(L⁻¹)`
representing the essentially bounded solutions of (1.18), on every filtered probability space. -/
noncomputable def mprop81 (P : LQProblem ιZ ιz ιτ) (D : DeflatingSplit P.sys P.β)
    (S : MeasExpectationSystem Ω) (t0 : ℕ) : MProp81Conclusion S P t0 where
  Λ := Λmat P.sys P.β D.J
  Υ := Υmat P.sys D.J
  Qop := mQop S D
  Rop := mRop S D
  equiv := mprop81_equiv P D S t0
  Qbounded := fun _ hx => mQop_bdd S P.β_pos D hx
  Rbounded := fun _ hx => mRop_bdd S P.β_pos D hx
  Qadapted := mQop_adapted S D
  Radapted := fun y _ => mRop_adapted S D y

/-- Woodford (2003), Proposition 8.1, p. 553: the matrices of `mprop81` are the explicit
`Λ = β⁻¹K⁻¹Ẽ'` and `Υ = −(J₁')⁻¹J₂'Ẽ'` (the same as for the exact systems,
`Prop81General.prop81_matrices`). -/
theorem mprop81_matrices (P : LQProblem ιZ ιz ιτ) (D : DeflatingSplit P.sys P.β)
    (S : MeasExpectationSystem Ω) (t0 : ℕ) :
    (mprop81 P D S t0).Λ = Λmat P.sys P.β D.J ∧ (mprop81 P D S t0).Υ = Υmat P.sys D.J :=
  ⟨rfl, rfl⟩

/-- **Woodford (2003), p. 553, the remark after Proposition 8.1, for the representation from a
deflating split, on every probability space**: `(Λ, Υ)` of `mprop81` is the same in every
representation iff `Λ = β⁻¹K⁻¹Ẽ'` is power-bounded. -/
theorem mprop81_unique_iff (P : LQProblem ιZ ιz ιτ) (D : DeflatingSplit P.sys P.β)
    (S : MeasExpectationSystem Ω) (t0 : ℕ) :
    (∀ H' : MProp81Conclusion S P t0, H'.Λ = Λmat P.sys P.β D.J ∧ H'.Υ = Υmat P.sys D.J) ↔
      PowBdd (Λmat P.sys P.β D.J) :=
  munique_iff_powBdd (mprop81 P D S t0)

end Woodford.OptimalPolicyRules.TidyR6aProp81Measure
