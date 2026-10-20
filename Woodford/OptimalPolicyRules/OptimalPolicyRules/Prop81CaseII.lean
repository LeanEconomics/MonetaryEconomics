/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.PencilRepeated

/-!
# Propositions 8.1 and 8.2 in case (ii) of Assumption 8.2

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.2 (ii) (p. 552), Propositions 8.1
(p. 553) and 8.2 (p. 555), Assumption 8.4 (ii) and Appendix G.1 (pp. 716–718).

In case (ii) the selection contains one complex root `μ` whose conjugate is not selected. A real
`Ψ` has a conjugation-closed spectrum, so no real deflating pair `A J = Î J Ψ` with `n_Z`
columns carries that selection (`Prop81Unique.realSelection_misses_unpaired`), and the book's
Assumption 8.4 (ii), `det[Re Γ₂] ≠ 0`, depends on how the complex eigenvector is scaled
(`Prop81Unique.re_det_rescale_zero`).

## The corrected construction

* Take the real invariant subspace for the selection **plus** `conj μ` (`selPlus`): a real pair
  `A J⁺ = Î J⁺ Ψ⁺` with `n_Z + 1` columns, all eigenvalues of `Ψ⁺` in `|ν| < β⁻¹` (since
  `|conj μ| = |μ|`). It exists with repeated roots allowed (`PencilRepeated.exists_deflating_cols`).
* Choose an `(n_Z + 1) × n_Z` real `P` and use `J = J⁺P` in (1.20)–(1.21):
  `Υ = −(J₁')⁻¹ J₂' Ẽ'`, `Λ = β⁻¹ K⁻¹ Ẽ'`, `K = A₂₂' + A₁₂' Υ`, and
  `R(L⁻¹)x = (J₁')⁻¹ P' ∑_k (βΨ⁺')^k E_t β J⁺' x_{t+k}`.
* `J⁺'` applied to (1.18) is a stable forward equation, so (1.18) ⇒ (1.20)–(1.21). For the
  converse, `D_t = w⁺_t − F⁺_t` lies in `ker P'`, and the remaining ξ-rows of (1.18) give
  `D_t = β H E_t D_{t+1}` with `H` the **residual root** on `ker P'`:
  `(I − J⁺₁'(J₁')⁻¹P') Ψ⁺' v = h v` for `P' v = 0`. Bounded `D` must vanish iff `|βh| < 1`.

## The normalisation-free replacement for Assumption 8.4 (ii)

`Assumption84IIall` (universal form): for **every** real basis `(J⁺, Ψ⁺)` of the invariant subspace
of the selection plus `conj μ`, some real `P` makes `J₁ = (J⁺P)₁` and `K` invertible and has
residual root `h` with `|βh| < 1`. It involves no eigenvector scaling. The existential form, its
basis invariance, a worked example and the `n_Z = 1` link to the book's `|Re μ⁻¹| > β` are in
`CaseIIBasis`.

## Main results

* `QuasiSplit`, `prop81II`, `prop81_equivII`: Proposition 8.1 from the corrected construction, for
  any expectation system (`DeflatingSplit` is the special case `quasiOfDeflating`).
* `prop82_of_quasiSplit`: Proposition 8.2 from it.
* `prop81_caseII_all`, `prop82_caseII_all`: Propositions 8.1 and 8.2 under Assumption 8.2
  (case (ii)), `Assumption84IIall` and a nonzero (1.15), with repeated roots allowed (`SelWhole`);
  distinct roots give `SelWhole` (`selWhole_selPlus_of_83`).
-/

namespace Woodford.OptimalPolicyRules.Prop81CaseII

open Matrix GeneralSetup GeneralFOC.LQ PencilSplit Prop81General TargetCriterion.Prop81
  PencilEigen PencilAssumptions PencilRepeated GeneralFOC.Selection Adjugate

variable {Ω : Type*} {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]
variable {ιc : Type*} [Fintype ιc] [DecidableEq ιc]

/-! ### The quasi-split -/

/-- Woodford (2003), App. G.1, case (ii): the projection `I − J⁺₁'(J₁')⁻¹P'` (with `J = J⁺P`)
that defines the residual root. -/
noncomputable def residProj (J : Matrix (ιZ ⊕ ιz) ιc ℝ) (P : Matrix ιc ιZ ℝ) : Matrix ιc ιc ℝ :=
  1 - (J1 J)ᵀ * ((J1 (J * P))ᵀ)⁻¹ * Pᵀ

set_option linter.style.longLine false in
/-- Woodford (2003), Proposition 8.1 and App. G.1, case (ii) of Assumption 8.2 (corrected): a real
deflating pair `A J⁺ = Î J⁺ Ψ⁺` with all eigenvalues of `Ψ⁺` in `|ν| < β⁻¹`, a real `P` with
`J₁ = (J⁺P)₁` and `K` invertible, and a residual map `H` on `ker P'` whose powers `(βH)^k`
decay. -/
structure QuasiSplit (S : LinearRESystem ιZ ιz) (β : ℝ) (ιc : Type*) [Fintype ιc] [DecidableEq ιc] where
  Jp : Matrix (ιZ ⊕ ιz) ιc ℝ
  Ψp : Matrix ιc ιc ℝ
  deflate : S.Ahat * Jp = S.Ihat * Jp * Ψp
  eig_lt : ∀ μ : ℂ, (Matrix.scalar ιc μ - Ψp.map Complex.ofReal).det = 0 → ‖μ‖ < β⁻¹
  P : Matrix ιc ιZ ℝ
  J1_det : (J1 (Jp * P)).det ≠ 0
  K_det : (Kmat S (Jp * P)).det ≠ 0
  H : Matrix ιc ιc ℝ
  resid : ∀ v, Pᵀ *ᵥ v = 0 → (residProj Jp P * Ψpᵀ) *ᵥ v = H *ᵥ v
  decay : PowDecay (β • H)

/-- Woodford (2003), App. G.1, p. 717: the powers of `β Ψ⁺'` decay geometrically (`β > 0`). -/
theorem QuasiSplit.powDecay_Gp {S : LinearRESystem ιZ ιz} {β : ℝ} (Q : QuasiSplit S β ιc)
    (hβ : 0 < β) : PowDecay (β • Q.Ψpᵀ) := by
  refine powDecay_of_eig _ fun w hw => ?_
  set X := Q.Ψp.map Complex.ofReal with hX
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  have hmap : (β • Q.Ψpᵀ).map Complex.ofReal = (β : ℂ) • Xᵀ := by
    ext i j
    simp [hX]
  have hsc : Matrix.scalar ιc w - (β : ℂ) • Xᵀ =
      ((β : ℂ) • (Matrix.scalar ιc (w / β) - X))ᵀ := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply]
      field_simp
    · simp [Matrix.scalar_apply, hij, Ne.symm hij]
  rw [hmap, hsc, det_transpose, det_smul] at hw
  have hd : (Matrix.scalar ιc (w / β) - X).det = 0 := by
    rcases mul_eq_zero.mp hw with h | h
    · exact absurd h (pow_ne_zero _ hβc)
    · exact h
  have hlt := Q.eig_lt (w / β) hd
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ] at hlt
  rw [div_lt_iff₀ hβ, inv_mul_cancel₀ hβ.ne'] at hlt
  exact hlt

omit [DecidableEq ιc] in
/-- Woodford (2003), App. G.1: `P' w⁺ = J' Î' φ` for `J = J⁺P`. -/
theorem wp_P (S : LinearRESystem ιZ ιz) (J : Matrix (ιZ ⊕ ιz) ιc ℝ) (P : Matrix ιc ιZ ℝ)
    (v : ιZ ⊕ ιz → ℝ) : Pᵀ *ᵥ ((Jᵀ * S.Ihatᵀ) *ᵥ v) = ((J * P)ᵀ * S.Ihatᵀ) *ᵥ v := by
  rw [mulVec_mulVec, transpose_mul, Matrix.mul_assoc]

/-- Woodford (2003), (1.18) and (G.4): `J⁺'` times the left side of (1.18) is
`Ψ⁺' E_t w⁺_{t+1} + J⁺' x_t − β⁻¹ w⁺_t` with `w⁺_t = J⁺' Î' φ_t`. -/
theorem Jp_lhs118 (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω)
    (Q : QuasiSplit P.sys P.β ιc) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ)
    (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) (t : ℕ) (ω : Ω) :
    Q.Jpᵀ *ᵥ lhs118 P 𝔼 y φ t ω =
      Q.Ψpᵀ *ᵥ EV 𝔼 t (fun ω' => (Q.Jpᵀ * P.sys.Ihatᵀ) *ᵥ φ (t + 1) ω') ω +
        Q.Jpᵀ *ᵥ xproc P y t ω - P.β⁻¹ • ((Q.Jpᵀ * P.sys.Ihatᵀ) *ᵥ φ t ω) := by
  unfold lhs118
  have ht : Q.Jpᵀ * P.sys.Ahatᵀ = Q.Ψpᵀ * (Q.Jpᵀ * P.sys.Ihatᵀ) := by
    rw [← transpose_mul, Q.deflate, transpose_mul, transpose_mul]
  have h1 : Q.Jpᵀ *ᵥ (P.sys.Ahatᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω) =
      Q.Ψpᵀ *ᵥ (Q.Jpᵀ *ᵥ (P.sys.Ihatᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω)) := by
    rw [mulVec_mulVec, ht, ← mulVec_mulVec, ← mulVec_mulVec]
  have h2 : EV 𝔼 t (fun ω' => (Q.Jpᵀ * P.sys.Ihatᵀ) *ᵥ φ (t + 1) ω') ω =
      (Q.Jpᵀ * P.sys.Ihatᵀ) *ᵥ EV 𝔼 t (φ (t + 1)) ω := by rw [EV_mulVec]
  rw [h2, mulVec_sub, mulVec_add, h1, mulVec_smul, ← mulVec_mulVec, ← mulVec_mulVec]

/-! ### The operators -/

/-- Woodford (2003), App. G.1, case (ii): the forward solution
`F⁺_t = ∑_{k ≥ 0} (βΨ⁺')^k E_t β J⁺' x_{t+k}`. -/
noncomputable def Fp (𝔼 : ExpectationSystem Ω) {S : LinearRESystem ιZ ιz} {β : ℝ}
    (Q : QuasiSplit S β ιc) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) : ℕ → Ω → ιc → ℝ :=
  fwdSum 𝔼 (β • Q.Ψpᵀ) (fun t ω => (β • Q.Jpᵀ) *ᵥ x t ω)

/-- Woodford (2003), eq. (1.21), case (ii): `r_t = (J₁')⁻¹ P' F⁺_t`. -/
noncomputable def RopII (𝔼 : ExpectationSystem Ω) {S : LinearRESystem ιZ ιz} {β : ℝ}
    (Q : QuasiSplit S β ιc) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) : ℕ → Ω → ιZ → ℝ :=
  fun t ω => ((J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ Fp 𝔼 Q x t ω)

/-- Woodford (2003), eq. (1.20), case (ii): `q_t = −K⁻¹ (E_t x^z_t + A₁₂' E_t r_{t+1})`. -/
noncomputable def QopII (𝔼 : ExpectationSystem Ω) {S : LinearRESystem ιZ ιz} {β : ℝ}
    (Q : QuasiSplit S β ιc) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) : ℕ → Ω → ιz → ℝ :=
  fun t ω => -((Kmat S (Q.Jp * Q.P))⁻¹ *ᵥ (EV 𝔼 t (fun ω' => Mpart (x t ω')) ω +
    S.A12ᵀ *ᵥ EV 𝔼 t (RopII 𝔼 Q x (t + 1)) ω))

/-! ### Proposition 8.1 from a quasi-split -/

/-- Woodford (2003), Proposition 8.1, p. 553 (the equivalence, corrected, case (ii)): for a
`QuasiSplit`, bounded adapted plans and bounded multipliers with `M_t` known at `t` satisfy (1.18)
for all `t ≥ t₀` iff they satisfy (1.20)–(1.21) with `J = J⁺P`, for any expectation system. -/
theorem prop81_equivII (P : LQProblem ιZ ιz ιτ) (Q : QuasiSplit P.sys P.β ιc)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Prop81EquivM P 𝔼 t0 (Λmat P.sys P.β (Q.Jp * Q.P)) (Υmat P.sys (Q.Jp * Q.P)) (QopII 𝔼 Q)
      (RopII 𝔼 Q) := by
  intro y φ hyb hya hφb hmk
  set x := xproc P y with hx
  have hxb : BoundedV x := boundedV_xproc hyb
  have hxa : AdaptedV 𝔼 x := adaptedV_xproc P hya
  have hG : PowDecay (P.β • Q.Ψpᵀ) := Q.powDecay_Gp P.β_pos
  have hfb : BoundedV (fun t ω => (P.β • Q.Jpᵀ) *ᵥ x t ω) := boundedV_mulVec _ hxb
  have hfk : ∀ t, KnownV 𝔼 t (fun ω => (P.β • Q.Jpᵀ) *ᵥ x t ω) :=
    fun t => knownV_mulVec 𝔼 _ (hxa t)
  obtain ⟨hF, -, hFb⟩ := fwdSum_spec 𝔼 hG hfb
  have hβ : P.β ≠ 0 := P.β_pos.ne'
  have hFrec : ∀ t ω, P.β⁻¹ • Fp 𝔼 Q x t ω =
      Q.Ψpᵀ *ᵥ EV 𝔼 t (Fp 𝔼 Q x (t + 1)) ω + Q.Jpᵀ *ᵥ x t ω := by
    intro t ω
    have h := hF t ω
    rw [EV_of_known 𝔼 (hfk t)] at h
    change Fp 𝔼 Q x t ω = (P.β • Q.Ψpᵀ) *ᵥ EV 𝔼 t (Fp 𝔼 Q x (t + 1)) ω +
      (P.β • Q.Jpᵀ) *ᵥ x t ω at h
    rw [h, smul_mulVec, smul_mulVec, ← smul_add, smul_smul, inv_mul_cancel₀ hβ, one_smul]
  set wp : ℕ → Ω → ιc → ℝ := fun t ω => (Q.Jpᵀ * P.sys.Ihatᵀ) *ᵥ φ t ω with hwp
  have hwJ : ∀ t ω, (J1 (Q.Jp * Q.P))ᵀ *ᵥ ξpart (φ t ω) +
      (J2 (Q.Jp * Q.P))ᵀ *ᵥ (P.sys.Etᵀ *ᵥ Mpart (φ t ω)) = Q.Pᵀ *ᵥ wp t ω := by
    intro t ω
    rw [← w_split, hwp, wp_P]
  -- the `z`-rows once (1.21) holds at `t + 1`
  have hMrows : ∀ t, t0 ≤ t → Eq121 t0 (Υmat P.sys (Q.Jp * Q.P)) (RopII 𝔼 Q x) φ → ∀ ω,
      Mpart (lhs118 P 𝔼 y φ t ω) = Kmat P.sys (Q.Jp * Q.P) *ᵥ Mpart (φ (t + 1) ω) +
        P.sys.A12ᵀ *ᵥ EV 𝔼 t (RopII 𝔼 Q x (t + 1)) ω +
        EV 𝔼 t (fun ω' => Mpart (x t ω')) ω - P.β⁻¹ • (P.sys.Etᵀ *ᵥ Mpart (φ t ω)) := by
    intro t ht h121 ω
    have hξ : (fun ω' => ξpart (φ (t + 1) ω')) =
        fun ω' => Υmat P.sys (Q.Jp * Q.P) *ᵥ Mpart (φ (t + 1) ω') + RopII 𝔼 Q x (t + 1) ω' :=
      funext fun ω' => h121 (t + 1) (by omega) ω'
    have hM : EV 𝔼 t (fun ω' => Mpart (φ (t + 1) ω')) = fun ω' => Mpart (φ (t + 1) ω') :=
      EV_of_known 𝔼 (hmk t ht)
    have hxz : EV 𝔼 t (fun ω' => Mpart (x t ω')) = fun ω' => Mpart (x t ω') := by
      funext ω' r
      exact congrFun (hxa t (Sum.inr r)) ω'
    rw [Mpart_lhs118, hξ, EV_add, EV_mulVec, hM, hxz, Kmat, add_mulVec, mulVec_add,
      ← mulVec_mulVec]
    abel
  have hwb : BoundedV wp := boundedV_mulVec _ hφb
  constructor
  · intro h118
    have hweq : ∀ t, t0 ≤ t → ∀ ω,
        wp t ω = (P.β • Q.Ψpᵀ) *ᵥ EV 𝔼 t (wp (t + 1)) ω + (P.β • Q.Jpᵀ) *ᵥ x t ω := by
      intro t ht ω
      have h0 := congrArg (Q.Jpᵀ *ᵥ ·) (h118 t ht ω)
      change Q.Jpᵀ *ᵥ lhs118 P 𝔼 y φ t ω = Q.Jpᵀ *ᵥ 0 at h0
      rw [Jp_lhs118, mulVec_zero, sub_eq_zero] at h0
      change Q.Ψpᵀ *ᵥ EV 𝔼 t (wp (t + 1)) ω + Q.Jpᵀ *ᵥ x t ω = P.β⁻¹ • wp t ω at h0
      rw [smul_mulVec, smul_mulVec, ← smul_add, h0, smul_smul, mul_inv_cancel₀ hβ, one_smul]
    have hwF := eq_fwdSum 𝔼 hG hfb hwb (fun t _ => hfk t) hweq
    have h121 : Eq121 t0 (Υmat P.sys (Q.Jp * Q.P)) (RopII 𝔼 Q x) φ := by
      intro t ht ω
      refine (eq121_iff P.sys Q.J1_det _ (Q.Pᵀ *ᵥ Fp 𝔼 Q x t ω) _).mpr ?_
      rw [hwJ, hwF t ht]
      rfl
    refine ⟨fun t ht ω => ?_, h121⟩
    refine (eq120_iff P.sys P.β Q.K_det _ _ _ _).mpr ?_
    rw [← hMrows t ht h121 ω]
    exact congrArg Mpart (h118 t ht ω)
  · rintro ⟨h120, h121⟩
    have hz : ∀ t, t0 ≤ t → ∀ ω, Mpart (lhs118 P 𝔼 y φ t ω) = 0 := fun t ht ω => by
      rw [hMrows t ht h121 ω]
      exact (eq120_iff P.sys P.β Q.K_det _ _ _ _).mp (h120 t ht ω)
    set Dp : ℕ → Ω → ιc → ℝ := fun s ω => wp s ω - Fp 𝔼 Q x s ω with hDp
    have hPD : ∀ s, t0 ≤ s → ∀ ω, Q.Pᵀ *ᵥ Dp s ω = 0 := by
      intro s hs ω
      have h := (eq121_iff P.sys Q.J1_det _ (Q.Pᵀ *ᵥ Fp 𝔼 Q x s ω) _).mp (h121 s hs ω)
      rw [hwJ] at h
      rw [hDp, mulVec_sub]
      exact sub_eq_zero.mpr h
    have hEsub : ∀ s ω, EV 𝔼 s (Dp (s + 1)) ω =
        EV 𝔼 s (wp (s + 1)) ω - EV 𝔼 s (Fp 𝔼 Q x (s + 1)) ω :=
      fun s ω => congrFun (EV_sub 𝔼 s (wp (s + 1)) (Fp 𝔼 Q x (s + 1))) ω
    -- `J⁺'` applied to (1.18), with the `z`-rows already zero
    have hkey : ∀ s, t0 ≤ s → ∀ ω, (J1 Q.Jp)ᵀ *ᵥ ξpart (lhs118 P 𝔼 y φ s ω) =
        Q.Ψpᵀ *ᵥ EV 𝔼 s (Dp (s + 1)) ω - P.β⁻¹ • Dp s ω := by
      intro s hs ω
      have h1 := Jp_lhs118 P 𝔼 Q y φ s ω
      rw [J_transpose_mulVec] at h1
      change (J1 Q.Jp)ᵀ *ᵥ ξpart (lhs118 P 𝔼 y φ s ω) +
        (J2 Q.Jp)ᵀ *ᵥ Mpart (lhs118 P 𝔼 y φ s ω) =
        Q.Ψpᵀ *ᵥ EV 𝔼 s (wp (s + 1)) ω + Q.Jpᵀ *ᵥ x s ω - P.β⁻¹ • wp s ω at h1
      rw [hz s hs ω, mulVec_zero, add_zero] at h1
      rw [h1, hEsub, hDp, mulVec_sub, smul_sub, hFrec s ω]
      abel
    have hu : IsUnit ((J1 (Q.Jp * Q.P))ᵀ).det := by
      rw [det_transpose]
      exact Ne.isUnit Q.J1_det
    have hJ1T : (J1 (Q.Jp * Q.P))ᵀ = Q.Pᵀ * (J1 Q.Jp)ᵀ := by
      rw [J1_mul, transpose_mul]
    have hξ : ∀ s, t0 ≤ s → ∀ ω, ξpart (lhs118 P 𝔼 y φ s ω) =
        ((J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ (Q.Ψpᵀ *ᵥ EV 𝔼 s (Dp (s + 1)) ω)) := by
      intro s hs ω
      have h2 := congrArg (Q.Pᵀ *ᵥ ·) (hkey s hs ω)
      rw [mulVec_mulVec, ← hJ1T, mulVec_sub, mulVec_smul, hPD s hs ω, smul_zero,
        sub_zero] at h2
      rw [← h2, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
    have hEPD : ∀ s, t0 ≤ s → ∀ ω, Q.Pᵀ *ᵥ EV 𝔼 s (Dp (s + 1)) ω = 0 := by
      intro s hs ω
      have h3 := congrFun (EV_mulVec 𝔼 s Q.Pᵀ (Dp (s + 1))) ω
      have h0 : (fun ω' => Q.Pᵀ *ᵥ Dp (s + 1) ω') = fun _ => (0 : ιZ → ℝ) :=
        funext fun ω' => hPD (s + 1) (by omega) ω'
      rw [← h3, h0, EV_const]
    have hdrec : ∀ s, t0 ≤ s → ∀ ω, Dp s ω =
        (P.β • Q.H) *ᵥ EV 𝔼 s (Dp (s + 1)) ω + (fun _ _ _ => (0 : ℝ)) s ω := by
      intro s hs ω
      have h1 := hkey s hs ω
      rw [hξ s hs ω] at h1
      have h3 : (residProj Q.Jp Q.P * Q.Ψpᵀ) *ᵥ EV 𝔼 s (Dp (s + 1)) ω = P.β⁻¹ • Dp s ω := by
        rw [residProj, Matrix.sub_mul, Matrix.one_mul, sub_mulVec, ← mulVec_mulVec,
          ← mulVec_mulVec, ← mulVec_mulVec, h1]
        abel
      rw [Q.resid _ (hEPD s hs ω)] at h3
      change Dp s ω = (P.β • Q.H) *ᵥ EV 𝔼 s (Dp (s + 1)) ω + 0
      rw [add_zero, smul_mulVec, h3, smul_smul, mul_inv_cancel₀ hβ, one_smul]
    have hDb : BoundedV Dp := by
      obtain ⟨M1, h1⟩ := hwb
      obtain ⟨M2, h2⟩ := hFb
      refine ⟨M1 + M2, fun t ω i => ?_⟩
      exact (abs_sub _ _).trans (add_le_add (h1 t ω i) (h2 t ω i))
    have hzero : BoundedV (fun (_ : ℕ) (_ : Ω) (_ : ιc) => (0 : ℝ)) :=
      ⟨0, fun _ _ _ => by simp⟩
    have hd0 := eq_fwdSum 𝔼 Q.decay hzero hDb (fun t _ i => 𝔼.const t 0) hdrec
    have hE0 : ∀ t, EV 𝔼 t (fun (_ : Ω) (_ : ιc) => (0 : ℝ)) = fun _ _ => 0 :=
      fun t => EV_const 𝔼 t 0
    have hfz : ∀ t, fwdSum 𝔼 (P.β • Q.H) (fun _ _ _ => (0 : ℝ)) t = fun _ _ => 0 := by
      intro t
      funext ω i
      have hz0 : ∀ M : Matrix ιc ιc ℝ, (M *ᵥ fun _ => (0 : ℝ)) = 0 := fun M => mulVec_zero M
      simp [fwdSum, hE0, hz0]
    intro t ht ω
    have hD1 : Dp (t + 1) = fun _ _ => 0 := by
      rw [hd0 (t + 1) (by omega), hfz]
    have hξ0 : ξpart (lhs118 P 𝔼 y φ t ω) = 0 := by
      rw [hξ t ht ω, hD1, hE0]
      change ((J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ (Q.Ψpᵀ *ᵥ (0 : ιc → ℝ))) = 0
      rw [mulVec_zero, mulVec_zero, mulVec_zero]
    funext a
    rcases a with i | r
    · exact congrFun hξ0 i
    · exact congrFun (hz t ht ω) r


/-- Woodford (2003), Proposition 8.1, p. 553, case (ii): `Q(L⁻¹)`, `R(L⁻¹)` map bounded processes
to bounded processes and `E_t R(L⁻¹)` is known at `t`. -/
theorem fwII_spec (𝔼 : ExpectationSystem Ω) {S : LinearRESystem ιZ ιz} {β : ℝ} (hβ : 0 < β)
    (Q : QuasiSplit S β ιc) {x : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hx : BoundedV x) :
    BoundedV (RopII 𝔼 Q x) ∧ AdaptedV 𝔼 (RopII 𝔼 Q x) ∧ BoundedV (QopII 𝔼 Q x) := by
  obtain ⟨-, hFa, hFb⟩ := fwdSum_spec 𝔼 (Q.powDecay_Gp hβ) (boundedV_mulVec (β • Q.Jpᵀ) hx)
  have hRb : BoundedV (RopII 𝔼 Q x) := boundedV_mulVec _ (boundedV_mulVec Q.Pᵀ hFb)
  refine ⟨hRb, fun t => knownV_mulVec 𝔼 _ (knownV_mulVec 𝔼 _ (hFa t)), ?_⟩
  obtain ⟨Mx, hMx⟩ := hx
  obtain ⟨MR, hMR⟩ := hRb
  have h1 : BoundedV (fun t ω => EV 𝔼 t (fun ω' => Mpart (x t ω')) ω +
      S.A12ᵀ *ᵥ EV 𝔼 t (RopII 𝔼 Q x (t + 1)) ω) := by
    refine boundedV_add ⟨Mx, fun t ω r => abs_EV_le 𝔼 (fun ω' r' => hMx t ω' (Sum.inr r')) t ω r⟩
      (boundedV_mulVec (x := fun t ω => EV 𝔼 t (RopII 𝔼 Q x (t + 1)) ω) _
        ⟨MR, fun t ω i => abs_EV_le 𝔼 (hMR (t + 1)) t ω i⟩)
  obtain ⟨K, hK⟩ := boundedV_mulVec (Kmat S (Q.Jp * Q.P))⁻¹ h1
  exact ⟨K, fun t ω r => by
    change |(-((Kmat S (Q.Jp * Q.P))⁻¹ *ᵥ _)) r| ≤ K
    rw [Pi.neg_apply, abs_neg]
    exact hK t ω r⟩

/-- Woodford (2003), Proposition 8.1, p. 553, case (ii): `E_t Q(L⁻¹) x` is known at `t`. -/
theorem qopII_adapted (𝔼 : ExpectationSystem Ω) {S : LinearRESystem ιZ ιz} {β : ℝ}
    (Q : QuasiSplit S β ιc) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) : AdaptedV 𝔼 (QopII 𝔼 Q x) := by
  intro t
  have h1 := knownV_add 𝔼 (knownV_EV 𝔼 t (fun ω' => Mpart (x t ω')))
    (knownV_mulVec 𝔼 S.A12ᵀ (knownV_EV 𝔼 t (RopII 𝔼 Q x (t + 1))))
  have h2 := knownV_mulVec 𝔼 (-(Kmat S (Q.Jp * Q.P))⁻¹) h1
  have h3 : (fun ω => (-(Kmat S (Q.Jp * Q.P))⁻¹) *ᵥ (EV 𝔼 t (fun ω' => Mpart (x t ω')) ω +
      S.A12ᵀ *ᵥ EV 𝔼 t (RopII 𝔼 Q x (t + 1)) ω)) = QopII 𝔼 Q x t := by
    funext ω
    rw [neg_mulVec]
    rfl
  rw [← h3]
  exact h2

/-- Woodford (2003), **Proposition 8.1**, p. 553 (corrected), from a `QuasiSplit` (case (ii) of
Assumption 8.2): `Λ = β⁻¹ K⁻¹ Ẽ'`, `Υ = −(J₁')⁻¹ J₂' Ẽ'` with `J = J⁺P`, and `Q(L⁻¹)`,
`R(L⁻¹)`; bounded `(φ, τ)` (`M_t` known at `t`, adapted plans) satisfy (1.18) for `t ≥ t₀` iff
they satisfy (1.20)–(1.21). Any expectation system. -/
noncomputable def prop81II (P : LQProblem ιZ ιz ιτ) (Q : QuasiSplit P.sys P.β ιc)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) : Prop81ConclusionM P 𝔼 t0 where
  Λ := Λmat P.sys P.β (Q.Jp * Q.P)
  Υ := Υmat P.sys (Q.Jp * Q.P)
  Qop := QopII 𝔼 Q
  Rop := RopII 𝔼 Q
  equiv := prop81_equivII P Q 𝔼 t0
  Qbounded := fun _ hx => (fwII_spec 𝔼 P.β_pos Q hx).2.2
  Rbounded := fun _ hx => (fwII_spec 𝔼 P.β_pos Q hx).1
  Qadapted := qopII_adapted 𝔼 Q
  Radapted := fun _ hx => (fwII_spec 𝔼 P.β_pos Q hx).2.1

/-- Woodford (2003), App. G.1: `|c| < 1` makes the powers of `c I` decay. -/
theorem powDecay_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} (hc : |c| < 1) :
    PowDecay (c • (1 : Matrix ι ι ℝ)) := by
  refine ⟨1, |c|, abs_nonneg c, hc, fun k i j => ?_⟩
  rw [smul_pow, one_pow, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, abs_mul, abs_pow,
    one_mul]
  by_cases h : i = j
  · simp [h]
  · simp [h, pow_nonneg (abs_nonneg c)]

/-- Woodford (2003), Proposition 8.1: a `DeflatingSplit` (case (i)) is the quasi-split with
`J⁺ = J`, `P = I` and no residual root. -/
noncomputable def quasiOfDeflating {S : LinearRESystem ιZ ιz} {β : ℝ} (D : DeflatingSplit S β) :
    QuasiSplit S β ιZ where
  Jp := D.J
  Ψp := D.Ψ
  deflate := D.deflate
  eig_lt := D.eig_lt
  P := 1
  J1_det := by rw [Matrix.mul_one]; exact D.J1_det
  K_det := by rw [Matrix.mul_one]; exact D.K_det
  H := (0 : ℝ) • 1
  resid := fun v hv => by
    rw [transpose_one, one_mulVec] at hv
    rw [hv, mulVec_zero, mulVec_zero]
  decay := by
    rw [smul_smul]
    exact powDecay_smul_one (by simp)

/-! ### Proposition 8.2 from a quasi-split -/

/-- Woodford (2003), **Proposition 8.2**, p. 555, for the matrices of `prop81II` (case (ii)):
under Assumption 8.1, Assumption 8.5 for `Λ = β⁻¹ K⁻¹ Ẽ'` (`J = J⁺P`), a lag length
`D ≥ max(1, rank Ẽ)` and a consistent bounded history, commitment to (1.23) is robustly
optimal. -/
theorem prop82_of_quasiSplit {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hpull : 𝔼.PullOut) (hA : Prop82General.Assumption81M P 𝔼 t0) (Q : QuasiSplit P.sys P.β ιc)
    (h85 : TargetCriterion.Krylov.Assumption85b (Λmat P.sys P.β (Q.Jp * Q.P)) P.sys.B2)
    {D : ℕ} (hD : D + 1 ≤ t0) (hDk : P.sys.Et.rank ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ}
    {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK (Λmat P.sys P.β (Q.Jp * Q.P)) P.sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimal (κ := ιz) P 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM (prop81II P Q 𝔼 t0) D qh vh y)
      (fun _ y t ω => zpart (y t ω)) := by
  have hrk : (Λmat P.sys P.β (Q.Jp * Q.P)).rank ≤ D := by
    rw [rank_Λmat P.sys P.β_pos.ne' Q.K_det]
    exact hDk
  exact Prop82General.Prop82M.prop82M_robustlyOptimal hpull hA (prop81II P Q 𝔼 t0) h85 hD
    (fun i c => (natDegree_Bpoly_le_rank _ i c).trans hrk)
    ((natDegree_alpha_le_rank _).trans hrk) hhist hMhb hMhk hqhb hvhb

/-! ### Case (ii) of Assumption 8.2 and the corrected Assumption 8.4 (ii) -/

/-- Woodford (2003), Assumption 8.2 (ii): the selection with the conjugate of the unpaired root
added. -/
noncomputable def selPlus (sel : Multiset ℂ) (μ : ℂ) : Multiset ℂ := starRingEnd ℂ μ ::ₘ sel

/-- Woodford (2003), Assumption 8.2 (ii): adding `conj μ` closes the selection under
conjugation. -/
theorem conjClosed_selPlus {sel : Multiset ℂ} {μ : ℂ} (hμ : μ ∈ sel)
    (hc : ConjClosed (sel.erase μ)) : ConjClosed (selPlus sel μ) := by
  unfold ConjClosed selPlus at *
  rw [← Multiset.cons_erase hμ, Multiset.map_cons, Multiset.map_cons, hc, Complex.conj_conj,
    Multiset.cons_swap]

/-- Woodford (2003), (1.15): the roots of the real pencil come in conjugate pairs. -/
theorem pencil_eval_conj (S : LinearRESystem ιZ ιz) {μ : ℂ} (h : S.pencilPoly.eval μ = 0) :
    S.pencilPoly.eval (starRingEnd ℂ μ) = 0 := by
  obtain ⟨w, hw0, hw⟩ := exists_pencil_eigvec S h
  rw [pencilPoly_eval]
  refine exists_mulVec_eq_zero_iff.mp ⟨fun i => starRingEnd ℂ (w i), ?_, ?_⟩
  · intro h0
    apply hw0
    funext i
    have := congrFun h0 i
    simpa using this
  · rw [sub_mulVec, map_mulVec_conj, smul_mulVec, map_mulVec_conj, hw]
    funext i
    simp

/-- Woodford (2003), **Assumption 8.4 (ii), corrected for case (ii) of Assumption 8.2
(normalisation-free)**: for every real basis `J⁺` (with `A J⁺ = Î J⁺ Ψ⁺`) of the invariant
subspace of the selection `sel'` (the selection plus `conj μ`, `n_Z + 1` columns), there is a real
`(n_Z + 1) × n_Z` matrix `P` with `J₁ = (J⁺P)₁` and `K = A₂₂' + A₁₂' Υ` invertible whose residual
root `h` — `(I − J⁺₁'(J₁')⁻¹P') Ψ⁺' v = h v` on `ker P'` — satisfies `|βh| < 1`. No eigenvector
is scaled. -/
def Assumption84IIall (S : LinearRESystem ιZ ιz) (β : ℝ) (sel' : Multiset ℂ) : Prop :=
  ∀ (Jp : Matrix (ιZ ⊕ ιz) (Option ιZ) ℝ) (Ψp : Matrix (Option ιZ) (Option ιZ) ℝ),
    S.Ahat * Jp = S.Ihat * Jp * Ψp → LinearIndependent ℝ Jpᵀ →
    (∀ ν : ℂ, (Matrix.scalar (Option ιZ) ν - Ψp.map Complex.ofReal).det = 0 → ν = 0 ∨ ν ∈ sel') →
    ∃ (P : Matrix (Option ιZ) ιZ ℝ) (h : ℝ), (J1 (Jp * P)).det ≠ 0 ∧
      (Kmat S (Jp * P)).det ≠ 0 ∧ |β * h| < 1 ∧
      ∀ v, Pᵀ *ᵥ v = 0 → (residProj Jp P * Ψpᵀ) *ᵥ v = h • v

/-- Woodford (2003), Assumptions 8.2 (ii) and 8.4 (ii) (corrected), App. G.1: a selection with one
unpaired root `μ` (`sel.erase μ` closed under conjugation), whole root classes for the selection
plus `conj μ`, a nonzero (1.15) and `Assumption84IIall` give a quasi-split. -/
theorem nonempty_quasiSplit {S : LinearRESystem ιZ ιz} {β : ℝ} (hβ : 0 < β)
    (h82 : Assumption82 S β) {μ : ℂ} (hμ : μ ∈ h82.sel) (hc : ConjClosed (h82.sel.erase μ))
    (hreg : S.pencilPoly ≠ 0) (hw : SelWhole S (selPlus h82.sel μ))
    (h84 : Assumption84IIall S β (selPlus h82.sel μ)) : Nonempty (QuasiSplit S β (Option ιZ)) := by
  have hsel : ∀ ν ∈ h82.sel, ν ≠ 0 ∧ S.pencilPoly.eval ν = 0 ∧ ‖ν‖ < β⁻¹ := by
    intro ν hν
    have := Multiset.mem_of_le h82.sel_le hν
    rw [Multiset.mem_filter, Polynomial.mem_roots hreg] at this
    exact ⟨this.2.1, this.1, this.2.2⟩
  have hsel' : ∀ ν ∈ selPlus h82.sel μ, ν ≠ 0 ∧ S.pencilPoly.eval ν = 0 ∧ ‖ν‖ < β⁻¹ := by
    intro ν hν
    rw [selPlus, Multiset.mem_cons] at hν
    rcases hν with rfl | hν
    · obtain ⟨h0, hr, hn⟩ := hsel μ hμ
      exact ⟨by rwa [ne_eq, map_eq_zero], pencil_eval_conj S hr, by rwa [Complex.norm_conj]⟩
    · exact hsel ν hν
  obtain ⟨Jp, Ψp, hd, hind, heig⟩ := exists_deflating_cols S (κ := Option ιZ)
    (conjClosed_selPlus hμ hc) (fun ν hν => ⟨(hsel' ν hν).1, (hsel' ν hν).2.1⟩) hreg hw (by
      rw [selPlus, Multiset.card_cons, Fintype.card_option]
      have := h82.sel_card
      omega)
  obtain ⟨P, h, hJ1, hK, hh, hres⟩ := h84 Jp Ψp hd hind heig
  refine ⟨⟨Jp, Ψp, hd, fun ν hν => ?_, P, hJ1, hK, h • 1,
    fun v hv => by rw [hres v hv, smul_mulVec, one_mulVec],
    by rw [smul_smul]; exact powDecay_smul_one hh⟩⟩
  rcases heig ν hν with h0 | hm
  · rw [h0, norm_zero]
    exact inv_pos.mpr hβ
  · exact (hsel' ν hm).2.2

/-- Woodford (2003), Assumption 8.3: with distinct nonzero roots, the selection plus `conj μ`
takes whole root classes (`conj μ` unselected, as in case (ii)). -/
theorem selWhole_selPlus_of_83 {S : LinearRESystem ιZ ιz} {β : ℝ} (h82 : Assumption82 S β)
    (h83 : Assumption83 S) {μ : ℂ} (hμ : μ ∈ h82.sel) (hnot : starRingEnd ℂ μ ∉ h82.sel) :
    SelWhole S (selPlus h82.sel μ) := by
  have hle : h82.sel ≤ nonzeroRoots S :=
    h82.sel_le.trans (Multiset.monotone_filter_right _ fun ν h => h.1)
  have hnd : h82.sel.Nodup := Multiset.nodup_of_le hle h83.nodup
  have hndp : (selPlus h82.sel μ).Nodup := Multiset.nodup_cons.mpr ⟨hnot, hnd⟩
  have hμn : μ ∈ nonzeroRoots S := Multiset.mem_of_le hle hμ
  intro ν hν
  have hνn : ν ∈ nonzeroRoots S := by
    rw [selPlus, Multiset.mem_cons] at hν
    rcases hν with rfl | hν
    · obtain ⟨hr, h0⟩ := Multiset.mem_filter.mp hμn
      rw [nonzeroRoots, Multiset.mem_filter, Polynomial.mem_roots h83.regular]
      exact ⟨pencil_eval_conj S ((Polynomial.mem_roots h83.regular).mp hr),
        by rwa [ne_eq, map_eq_zero]⟩
    · exact Multiset.mem_of_le hle hν
  have hν0 : ν ≠ 0 := (Multiset.mem_filter.mp hνn).2
  rw [Multiset.count_eq_one_of_mem hndp hν,
    ← Multiset.count_filter_of_pos (p := fun ν : ℂ => ν ≠ 0) hν0]
  exact (Multiset.count_eq_one_of_mem h83.nodup hνn).symm

/-- Woodford (2003), App. G.1: the quasi-split chosen from Assumptions 8.2 (ii) and 8.4 (ii)
(corrected). -/
noncomputable def quasiSplitOf (P : LQProblem ιZ ιz ιτ) (h82 : Assumption82 P.sys P.β) {μ : ℂ}
    (hμ : μ ∈ h82.sel) (hc : ConjClosed (h82.sel.erase μ)) (hreg : P.sys.pencilPoly ≠ 0)
    (hw : SelWhole P.sys (selPlus h82.sel μ))
    (h84 : Assumption84IIall P.sys P.β (selPlus h82.sel μ)) :
    QuasiSplit P.sys P.β (Option ιZ) :=
  (nonempty_quasiSplit P.β_pos h82 hμ hc hreg hw h84).some

/-- Woodford (2003), **Proposition 8.1**, p. 553, **in case (ii) of Assumption 8.2**: one selected
complex root `μ` with its conjugate unselected, the corrected (normalisation-free) Assumption 8.4
(ii), a nonzero (1.15) and whole root classes (repeated roots allowed): the corrected Proposition
8.1 holds for any expectation system. -/
theorem prop81_caseII_all (P : LQProblem ιZ ιz ιτ) (h82 : Assumption82 P.sys P.β) {μ : ℂ}
    (hμ : μ ∈ h82.sel) (hc : ConjClosed (h82.sel.erase μ)) (hreg : P.sys.pencilPoly ≠ 0)
    (hw : SelWhole P.sys (selPlus h82.sel μ))
    (h84 : Assumption84IIall P.sys P.β (selPlus h82.sel μ))
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) : Nonempty (Prop81ConclusionM P 𝔼 t0) :=
  ⟨prop81II P (quasiSplitOf P h82 hμ hc hreg hw h84) 𝔼 t0⟩

/-- Woodford (2003), **Proposition 8.2**, p. 555, **in case (ii) of Assumption 8.2**: under
Assumptions 8.1, 8.2 (ii), the corrected 8.4 (ii), 8.5 and a nonzero (1.15), commitment to (1.23)
is robustly optimal. -/
theorem prop82_caseII_all {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hpull : 𝔼.PullOut) (hA : Prop82General.Assumption81M P 𝔼 t0)
    (h82 : Assumption82 P.sys P.β) {μ : ℂ} (hμ : μ ∈ h82.sel) (hc : ConjClosed (h82.sel.erase μ))
    (hreg : P.sys.pencilPoly ≠ 0) (hw : SelWhole P.sys (selPlus h82.sel μ))
    (h84 : Assumption84IIall P.sys P.β (selPlus h82.sel μ))
    (h85 : Assumption85 (Λmat P.sys P.β ((quasiSplitOf P h82 hμ hc hreg hw h84).Jp *
      (quasiSplitOf P h82 hμ hc hreg hw h84).P)) P.sys.B2)
    {D : ℕ} (hD : D + 1 ≤ t0) (hDk : P.sys.Et.rank ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ}
    {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK (Λmat P.sys P.β
      ((quasiSplitOf P h82 hμ hc hreg hw h84).Jp * (quasiSplitOf P h82 hμ hc hreg hw h84).P))
      P.sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimal (κ := ιz) P 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM
        (prop81II P (quasiSplitOf P h82 hμ hc hreg hw h84) 𝔼 t0) D qh vh y)
      (fun _ y t ω => zpart (y t ω)) :=
  prop82_of_quasiSplit hpull hA _ h85.2 hD hDk hhist hMhb hMhk hqhb hvhb

end Woodford.OptimalPolicyRules.Prop81CaseII
