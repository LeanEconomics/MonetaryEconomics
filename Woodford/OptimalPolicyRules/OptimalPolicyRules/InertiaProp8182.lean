/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InertiaSplit
import OptimalPolicyRules.CaseIIInstance

/-!
# The inflation-inertia model: Assumption 8.5, Proposition 8.2, and case (ii) of Assumption 8.2

Woodford (2003), *Interest and Prices*, Chapter 8, Assumptions 8.2, 8.4 and 8.5 and Propositions
8.1–8.2 (pp. 552–555, App. G.1–G.2, pp. 716–719), for the inflation-inertia model of §3.2
(pp. 592–604).

## Main results

* `assumption85_two`: for a `2 × 2` matrix `Λ` with `det Λ ≠ 0`, `Λ₁₀ ≠ 0` and `B₂ = (0, σ)`,
  `σ ≠ 0`, Assumption 8.5 holds (used for the basic model in `GeneralTheoryLinks` too).
* `in_assumption85`: **Assumption 8.5 for the inertia model**, for the `Λ` of every deflating split
  (`InertiaSplit.inSplit`, the real case).
* `in_prop82_real`: **Proposition 8.2 for the inertia model in the real case**, from
  `Prop82General.prop82_of_split`, given the corrected Assumption 8.1
  (`Prop82General.Assumption81M`).
* **The complex case `S² < 4P₂₃`: Proposition 8.1 through case (ii) of Assumption 8.2.**
  `in_eigvec`: `u = (1, μ, σμ²/(1 − μ))` is a complex eigenvector of the pencil for every root
  `μ ≠ 1`; `in_assumption82II`: selecting `μ₂ = (βλ₂)⁻¹` alone is case (ii) of Assumption 8.2
  (`μ₃ = conj μ₂` unselected, `|Re μ₂⁻¹| = βS/2 > β`); `in_Kdet_complex`: with `J = Re(μu)` the
  matrix `K` has `det K = γ/Re μ ≠ 0`; `in_assumption84II`: the corrected Assumption 8.4 (ii)
  holds (`J⁺ = (Re μu, Im μu)`, `P = e₁`, residual root `h` with `h⁻¹ = Re μ⁻¹`); hence
  `in_prop81_complex` (Proposition 8.1 in the complex case, any expectation system) and
  `in_prop81_all` (Proposition 8.1 for the model at every admissible calibration).
-/

namespace Woodford.OptimalPolicyRules.InertiaProp8182

open Matrix Polynomial GeneralSetup PencilSplit
open IRuleBasic (Calib)
open CubicRoots
open InertiaSplit
open GeneralLinksInertia (inSys inProblem in_det_ne)

variable {Ω : Type*}

/-! ### Assumption 8.5 for a `2 × 2` matrix -/

/-- Woodford (2003), Assumption 8.5 (tool): a family indexed by `Fin (rank Λ)` for a rank-2
`2 × 2` matrix is the pair `![f 0, f 1]`. -/
theorem linearIndependent_fin_rank {Λ : Matrix (Fin 2) (Fin 2) ℝ} {f : ℕ → Fin 2 → ℝ}
    (hr : Λ.rank = 2) (h : LinearIndependent ℝ ![f 0, f 1]) :
    LinearIndependent ℝ (fun j : Fin Λ.rank => f j.val) := by
  generalize hk : Λ.rank = k at hr ⊢
  subst hr
  convert h using 1
  funext j
  fin_cases j <;> rfl

/-- **Woodford (2003), Assumption 8.5, App. G.2, p. 719, for `2 × 2` systems with `B₂ = (0, σ)`**:
if `det Λ ≠ 0` (so `k = rank Λ = 2`), `σ ≠ 0` and `Λ₁₀ ≠ 0`, then `B₂', B₂'Λ` are linearly
independent and so are `B₂'Λ, B₂'Λ²`. -/
theorem assumption85_two {Λ : Matrix (Fin 2) (Fin 2) ℝ} {σ : ℝ} (hσ : σ ≠ 0) (h10 : Λ 1 0 ≠ 0)
    (hdet : Λ.det ≠ 0) : PencilAssumptions.Assumption85 Λ ![0, σ] := by
  have hdu : IsUnit Λ.det := isUnit_iff_ne_zero.mpr hdet
  have hr : Λ.rank = 2 := by
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr hdu)]
    simp
  have h1 : LinearIndependent ℝ ![![0, σ], ![0, σ] ᵥ* Λ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e0 := congrFun hst 0
    have e1 := congrFun hst 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at e0 e1
    have ht : t = 0 := by
      have h' : t * (σ * Λ 1 0) = 0 := by linarith
      rcases mul_eq_zero.mp h' with h | h
      · exact h
      · exact absurd h (mul_ne_zero hσ h10)
    subst ht
    have h' : s * σ = 0 := by linarith
    exact ⟨(mul_eq_zero.mp h').resolve_right hσ, rfl⟩
  refine ⟨?_, ?_⟩
  · refine linearIndependent_fin_rank (f := fun j => ![0, σ] ᵥ* Λ ^ j) hr ?_
    simpa using h1
  · unfold TargetCriterion.Krylov.Assumption85b
    have h2 : LinearIndependent ℝ ![![0, σ] ᵥ* Λ, (![0, σ] ᵥ* Λ) ᵥ* Λ] := by
      rw [LinearIndependent.pair_iff] at h1 ⊢
      intro s t hst
      refine h1 s t ?_
      have e := congrArg (fun v => v ᵥ* Λ⁻¹) hst
      simp only [add_vecMul, smul_vecMul, vecMul_vecMul, Matrix.mul_assoc,
        mul_nonsing_inv _ hdu, Matrix.mul_one, vecMul_one, zero_vecMul] at e
      exact e
    refine linearIndependent_fin_rank (f := fun j => ![0, σ] ᵥ* Λ ^ (j + 1)) hr ?_
    simpa [pow_two, vecMul_vecMul] using h2

/-! ### The real case: Assumption 8.5 and Proposition 8.2 -/

variable (c : Calib) (γ : ℝ)

/-- **Woodford (2003), Assumption 8.5, App. G.2, p. 719, for the inflation-inertia model**: for the
`Λ = (μ/(βγ))[β, σ + d; κβ, κσ + 1 + βγ − βμ]` of the split of any real root `λₛ` of
`λ² − Sλ + P₂₃` (`μ = (βλₛ)⁻¹`), with `B₂ = (0, σ)`. -/
theorem in_assumption85 (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {ls : ℝ}
    (hq : quadQ c.β γ c.κ c.σ ls = 0) :
    PencilAssumptions.Assumption85
      (Λmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)) c.β (inJ c (c.β * ls)⁻¹))
      (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)).B2 := by
  have h := standing_of c γ hc hγ0 hγ1
  obtain ⟨hp, h1, h0, -, -⟩ := mu_facts c γ h hq
  have hΛ := in_Λmat c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le) hc.1.ne' hγ0.ne' hp h1 h0
  have hdt := in_Λ_det c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le) hc.1.ne' hγ0.ne' hp h1 h0
  refine assumption85_two hc.2.2.1.ne' ?_ ?_
  · rw [hΛ]
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
    exact mul_ne_zero (div_ne_zero h0 (mul_ne_zero hc.1.ne' hγ0.ne'))
      (mul_ne_zero hc.2.2.2.1.ne' hc.1.ne')
  · rw [hdt]
    exact div_ne_zero h0 (mul_ne_zero hc.1.ne' hγ0.ne')

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model, real case
(`S² ≥ 4P₂₃`, including the double root)**: given the corrected Assumption 8.1 and an expectation
system with pull-out, commitment to the target criterion (1.23) built from the split solving
`λ₂ʳ` forward is robustly optimal (a window of `D ≥ 2` lags, any consistent bounded history);
Assumption 8.5 holds (`in_assumption85`). -/
theorem in_prop82_real {𝔼 : ExpectationSystem Ω} {t0 : ℕ} (hc : c.Adm) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hD : 0 ≤ discQ c.β γ c.κ c.σ) (hpull : 𝔼.PullOut)
    (hA : Prop82General.Assumption81M (inProblem c γ hc hγ0.le) 𝔼 t0) {D : ℕ}
    (hD1 : D + 1 ≤ t0) (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK
      (Λmat (inProblem c γ hc hγ0.le).sys c.β (inSplit c γ hc hγ0 hγ1 (quadQ_lam2r hD)).J)
      (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimal (κ := Fin 2) (inProblem c γ hc hγ0.le) 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM
        (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 (quadQ_lam2r hD)) 𝔼 t0) D qh vh y)
      (fun _ y t ω => zpart (y t ω)) := by
  have hE : (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)).Et.rank = 2 := by
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
    · simp
    · rw [in_Et_det]
      exact isUnit_iff_ne_zero.mpr hc.1.ne'
  refine Prop82General.prop82_of_split hpull hA _ ?_ hD1 ?_ hhist hMhb hMhk hqhb hvhb
  · rw [show (inSplit c γ hc hγ0 hγ1 (quadQ_lam2r hD)).J =
        inJ c (c.β * lam2r c.β γ c.κ c.σ)⁻¹ from rfl,
      show (inProblem c γ hc hγ0.le).sys = inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)
        from rfl,
      show (inProblem c γ hc hγ0.le).β = c.β from rfl]
    exact (in_assumption85 c γ hc hγ0 hγ1 (quadQ_lam2r hD)).2
  · change (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)).Et.rank ≤ D
    rw [hE]
    exact hD2

/-- Woodford (2003), (1.15) at `μ = 0`: `A` is invertible for the inertia model
(`det A = γ > 0`), so `rank A = 3`. -/
theorem in_rank_Ahat (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) : (inSys c γ hσ hd).Ahat.rank = 3 := by
  rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
  · simp
  · rw [in_Ahat_det]
    exact isUnit_iff_ne_zero.mpr h.gamma_pos.ne'

/-- Woodford (2003), **Proposition 8.1**, p. 553, for the inflation-inertia model in the real
case `S² ≥ 4P₂₃`, **including the double root** `S² = 4P₂₃` (where Assumption 8.3 fails): the
deflating split solving `λ₂ʳ` forward (`InertiaSplit.inSplit`) gives the corrected Proposition
8.1 for any expectation system. -/
theorem in_prop81_real (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hD : 0 ≤ discQ c.β γ c.κ c.σ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Nonempty (Prop81General.Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0) :=
  ⟨Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 (quadQ_lam2r hD)) 𝔼 t0⟩

/-! ### The complex case: case (ii) of Assumption 8.2 -/

/-- Woodford (2003), App. G.1, (G.1), for the inertia model: the complex vector
`u(μ) = (1, μ, σμ²/(1 − μ))` (`Z`-, `π`-, `x`-rows). -/
noncomputable def inU (μ : ℂ) : Unit ⊕ Fin 2 → ℂ :=
  Sum.elim (fun _ => 1) ![μ, c.σ * μ ^ 2 / (1 - μ)]

/-- Woodford (2003), App. G.1, (G.1), for the inertia model: for every root `μ ≠ 1` of (1.15),
real or complex, `A u(μ) = μ Î u(μ)`. -/
theorem in_eigvec (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) {μ : ℂ}
    (hp : (inSys c γ hσ hd).pencilPoly.eval μ = 0) (h1 : 1 - μ ≠ 0) :
    (inSys c γ hσ hd).Ahat.map Complex.ofReal *ᵥ inU c μ =
      μ • ((inSys c γ hσ hd).Ihat.map Complex.ofReal *ᵥ inU c μ) := by
  rw [in_pencil_eval] at hp
  funext r
  rcases r with r | j
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, LinearRESystem.Ahat, LinearRESystem.Ihat,
      inSys, inU]
  · fin_cases j
    · simp [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, LinearRESystem.Ahat,
        LinearRESystem.Ihat, inSys, inU]
      field_simp
      linear_combination -hp
    · simp [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, LinearRESystem.Ahat,
        LinearRESystem.Ihat, inSys, inU]
      field_simp
      ring

open CaseIIInstance (pairJ rotΨ selA hOf resid_of_eigvec book_iff inv_fin_one)

/-- Woodford (2003), App. G.1 (tool): the eigenvalues of the real block `[[ρ, σ], [−σ, ρ]]` of
`μ = ρ + iσ` (`σ ≠ 0`) are `μ` and `conj μ`. -/
theorem rotΨ_eig {μ ν : ℂ} (hτ : μ.im ≠ 0)
    (hν : (Matrix.scalar (Option Unit) ν - (rotΨ μ.re μ.im).map Complex.ofReal).det = 0) :
    ν = μ ∨ ν = starRingEnd ℂ μ := by
  obtain ⟨z, hz0, hz⟩ := PencilEigen.exists_eigvec hν
  have e1 : (μ.re : ℂ) * z none + (μ.im : ℂ) * z (some ()) = ν * z none := by
    simpa [mulVec, dotProduct, Fintype.sum_option, rotΨ] using congrFun hz none
  have e2 : -(μ.im : ℂ) * z none + (μ.re : ℂ) * z (some ()) = ν * z (some ()) := by
    simpa [mulVec, dotProduct, Fintype.sum_option, rotΨ] using congrFun hz (some ())
  have hτc : (μ.im : ℂ) ≠ 0 := by exact_mod_cast hτ
  have hzn : z none ≠ 0 := by
    intro h0
    apply hz0
    funext c
    rcases c with _ | c
    · exact h0
    · rw [h0, mul_zero, zero_add, mul_zero] at e1
      rcases c
      exact (mul_eq_zero.mp e1).resolve_left hτc
  have hq : ((ν - μ.re) ^ 2 + (μ.im : ℂ) ^ 2) * z none = 0 := by
    linear_combination (μ.re - ν) * e1 - (μ.im : ℂ) * e2
  have key : (ν - μ) * (ν - starRingEnd ℂ μ) = (ν - μ.re) ^ 2 + (μ.im : ℂ) ^ 2 := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, pow_two] <;> ring
  have hq2 : (ν - μ) * (ν - starRingEnd ℂ μ) = 0 := by
    rw [key]
    exact (mul_eq_zero.mp hq).resolve_right hzn
  rcases mul_eq_zero.mp hq2 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- Woodford (2003), eq. (1.20), p. 553, for the inertia model and any real `J` (`3 × 1`, `J₁ ≠ 0`):
`det K · J₁ = (1 + βγ)J₁ − (β + κσ)J_π − κJ_x`. -/
theorem in_Kdet_gen (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) (J : Matrix (Unit ⊕ Fin 2) Unit ℝ)
    (h0 : J (Sum.inl ()) () ≠ 0) :
    (Kmat (inSys c γ hσ hd) J).det * J (Sum.inl ()) () =
      (1 + c.β * γ) * J (Sum.inl ()) () - (c.β + c.κ * c.σ) * J (Sum.inr 0) () -
        c.κ * J (Sum.inr 1) () := by
  have hinv : ((J1 J)ᵀ)⁻¹ = Matrix.of fun _ _ => (J (Sum.inl ()) ())⁻¹ := by
    rw [inv_fin_one (M := (J1 J)ᵀ) (by exact h0)]
    rfl
  rw [Kmat, Υmat, hinv, det_fin_two]
  simp [inSys, Matrix.mul_apply, Fin.sum_univ_two, J2]
  field_simp
  ring

/-- Woodford (2003), Prop. 8.7, p. 594, complex case `S² < 4P₂₃`: the selected root
`μ₂ = (βλ₂)⁻¹` of (1.15) is not real, has `Re μ₂ > 0`, its conjugate is `μ₃ = (βλ₃)⁻¹`, and
`|Re μ₂⁻¹| = β Re λ₂ = βS/2 > β`. -/
theorem mu2_facts (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hD : discQ c.β γ c.κ c.σ < 0) :
    (muj c (lam2 c.β γ c.κ c.σ)).im ≠ 0 ∧ 0 < (muj c (lam2 c.β γ c.κ c.σ)).re ∧
      starRingEnd ℂ (muj c (lam2 c.β γ c.κ c.σ)) = muj c (lam3 c.β γ c.κ c.σ) ∧
      c.β < |((muj c (lam2 c.β γ c.κ c.σ))⁻¹).re| := by
  have h := standing_of c γ hc hγ0 hγ1
  obtain ⟨him, -, hre⟩ := lam2_complex h hD
  have hβ := hc.1
  set l := lam2 c.β γ c.κ c.σ with hl
  have hz : ((c.β : ℂ) * l).re = c.β * l.re := Complex.re_ofReal_mul _ _
  have hzi : ((c.β : ℂ) * l).im = c.β * l.im := Complex.im_ofReal_mul _ _
  have hn : 0 < Complex.normSq ((c.β : ℂ) * l) := by
    rw [Complex.normSq_pos]
    intro h0
    have := congrArg Complex.re h0
    rw [hz, Complex.zero_re] at this
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [muj, Complex.inv_im, hzi]
    intro h0
    rw [neg_div, neg_eq_zero, div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact him ((mul_eq_zero.mp h0).resolve_left hβ.ne')
    · exact hn.ne' h0
  · rw [muj, Complex.inv_re, hz]
    exact div_pos (mul_pos hβ (by linarith)) hn
  · simp [muj, hl, lam3_eq_conj hD, map_inv₀, map_mul, Complex.conj_ofReal]
  · rw [muj, inv_inv, hz, abs_of_pos (mul_pos hβ (by linarith))]
    nlinarith

/-- **Woodford (2003), Assumption 8.2, p. 552, case (ii), for the inflation-inertia model in the
complex case `S² < 4P₂₃`**: select `μ₂ = (βλ₂)⁻¹` alone (`n_Z = 1`, `A` invertible); its conjugate
`μ₃` is not selected and `|Re μ₂⁻¹| > β`. -/
noncomputable def in_assumption82II (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hD : discQ c.β γ c.κ c.σ < 0) :
    PencilEigen.Assumption82 (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)) c.β where
  count := by
    unfold LinearRESystem.Assumption82Count
    rw [in_stableCount c γ (standing_of c γ hc hγ0 hγ1)]
    omega
  sel := {muj c (lam2 c.β γ c.κ c.σ)}
  sel_le := by
    have h := standing_of c γ hc hγ0 hγ1
    refine Multiset.singleton_le.mpr (Multiset.mem_filter.mpr ⟨?_, ?_, (in_root_norms c γ h).2.1⟩)
    · rw [in_roots c γ h]
      simp
    · exact muj_ne_zero c γ h (lam2_ne_zero h)
  sel_card := by
    rw [in_rank_Ahat c γ (standing_of c γ hc hγ0 hγ1)]
    simp
  cases := by
    obtain ⟨him, -, -, hbook⟩ := mu2_facts c γ hc hγ0 hγ1 hD
    refine Or.inr ⟨_, Multiset.mem_singleton_self _, ?_, ?_, hbook⟩
    · rw [Multiset.mem_singleton]
      intro h0
      have := congrArg Complex.im h0
      rw [Complex.conj_im] at this
      exact him (by linarith)
    · rw [Multiset.erase_singleton]
      simp [GeneralFOC.Selection.ConjClosed]

/-- **Woodford (2003), Assumption 8.4 (ii), corrected (`CaseIIBasis.Assumption84II`), for the
inflation-inertia model in the complex case**: with `u = (1, μ, σμ²/(1 − μ))` for `μ = μ₂`, the
basis `J⁺ = (Re μu, Im μu)` is admissible for `{μ₂, conj μ₂}`; with `P = e₁` (`J = Re μu`),
`J₁ = Re μ ≠ 0`, `det K = γ/Re μ ≠ 0`, and the residual root `h` has `h⁻¹ = Re μ⁻¹`, so
`|βh| < 1` is the book's `|Re μ⁻¹| > β`. -/
theorem in_assumption84II (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hD : discQ c.β γ c.κ c.σ < 0) :
    CaseIIBasis.Assumption84II (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)) c.β
      (Prop81CaseII.selPlus (in_assumption82II c γ hc hγ0 hγ1 hD).sel
        (muj c (lam2 c.β γ c.κ c.σ))) := by
  have h := standing_of c γ hc hγ0 hγ1
  have hσ : c.σ ≠ 0 := hc.2.2.1.ne'
  have hd := in_det_ne c γ hc hγ0.le
  obtain ⟨him, hre, hconj, hbook⟩ := mu2_facts c γ hc hγ0 hγ1 hD
  set μ := muj c (lam2 c.β γ c.κ c.σ) with hμ
  have hroot : (inSys c γ hσ hd).pencilPoly.eval μ = 0 := by
    rw [in_pencilPoly c γ h]
    simp [hμ]
  have h1 : 1 - μ ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.one_im, Complex.zero_im] at this
    exact him (by linarith)
  have hu := in_eigvec c γ hσ hd hroot h1
  have hu1 : inU c μ (Sum.inl default) = 1 := rfl
  have ha : (μ * inU c μ (Sum.inl default)).re ≠ 0 := by
    rw [hu1, mul_one]
    exact hre.ne'
  obtain ⟨hdef, hres⟩ := resid_of_eigvec (inSys c γ hσ hd) hu μ ha
  -- the complex identity behind `det K = γ/Re μ`
  rw [in_pencil_eval] at hroot
  have hid : ((1 + c.β * γ : ℝ) : ℂ) * μ - ((c.β + c.κ * c.σ : ℝ) : ℂ) * (μ * μ) -
      ((c.κ : ℝ) : ℂ) * (μ * ((c.σ : ℂ) * μ ^ 2 / (1 - μ))) = ((γ : ℝ) : ℂ) := by
    push_cast
    field_simp
    linear_combination -hroot
  have hidr := congrArg Complex.re hid
  simp only [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hidr
  refine ⟨pairJ (μ • inU c μ), rotΨ μ.re μ.im, ⟨hdef, ?_, fun ν hν => Or.inr ?_⟩, selA,
    hOf μ.re μ.im (μ * inU c μ (Sum.inl default)), ?_, ?_, ?_, hres⟩
  · refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
    have e1 : g none * μ.re + g (some ()) * μ.im = 0 := by
      simpa [Fintype.sum_option, pairJ, inU, Complex.mul_re, Complex.mul_im] using
        congrFun hg (Sum.inl ())
    have e2 : g none * (μ.re * μ.re - μ.im * μ.im) +
        g (some ()) * (μ.re * μ.im + μ.im * μ.re) = 0 := by
      simpa [Fintype.sum_option, pairJ, inU, Complex.mul_re, Complex.mul_im] using
        congrFun hg (Sum.inr 0)
    have hpos : 0 < μ.re ^ 2 + μ.im ^ 2 := by positivity
    have g1 : g none * (μ.im * (μ.re ^ 2 + μ.im ^ 2)) = 0 := by
      linear_combination (2 * μ.re * μ.im) * e1 - μ.im * e2
    have g2 : g (some ()) * (μ.im * (μ.re ^ 2 + μ.im ^ 2)) = 0 := by
      linear_combination -((μ.re ^ 2 - μ.im ^ 2) * e1 - μ.re * e2)
    have hne : μ.im * (μ.re ^ 2 + μ.im ^ 2) ≠ 0 := mul_ne_zero him hpos.ne'
    rcases i with _ | i
    · exact (mul_eq_zero.mp g1).resolve_right hne
    · rcases i
      exact (mul_eq_zero.mp g2).resolve_right hne
  · change ν ∈ starRingEnd ℂ μ ::ₘ ({μ} : Multiset ℂ)
    rcases rotΨ_eig him hν with e | e
    · rw [e]
      exact Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _)
    · rw [e]
      exact Multiset.mem_cons_self _ _
  · rw [Matrix.det_unique]
    simpa [J1, Matrix.mul_apply, Fintype.sum_option, pairJ, selA, inU] using hre.ne'
  · set J' : Matrix (Unit ⊕ Fin 2) Unit ℝ := pairJ (μ • inU c μ) * selA with hJ'
    have hJ0 : J' (Sum.inl ()) () = μ.re := by
      simp [hJ', Matrix.mul_apply, Fintype.sum_option, pairJ, selA, inU]
    have hk := in_Kdet_gen c γ hσ hd J' (by rw [hJ0]; exact hre.ne')
    have hJ1' : J' (Sum.inr 0) () = (μ * μ).re := by
      simp [hJ', Matrix.mul_apply, Fintype.sum_option, pairJ, selA, inU]
    have hJ2' : J' (Sum.inr 1) () = (μ * ((c.σ : ℂ) * μ ^ 2 / (1 - μ))).re := by
      simp [hJ', Matrix.mul_apply, Fintype.sum_option, pairJ, selA, inU]
    rw [hJ0, hJ1', hJ2'] at hk
    intro h0
    rw [h0, zero_mul] at hk
    exact hγ0.ne' (by linarith)
  · have e : μ * inU c μ (Sum.inl default) = ((1 : ℝ) : ℂ) * μ := by
      rw [hu1]
      simp
    rw [e]
    exact (book_iff hre.ne' one_ne_zero hc.1).mpr hbook

/-- **Woodford (2003), Proposition 8.1, p. 553, for the inflation-inertia model in the complex
case `S² < 4P₂₃`**, through case (ii) of Assumption 8.2 (`in_assumption82II`) and the corrected
Assumption 8.4 (ii) (`in_assumption84II`) — `CaseIIBasis.prop81_caseII`; any expectation
system. (There is no real deflating split in this case, `InertiaSplit.split_isEmpty`.) -/
theorem in_prop81_complex (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hD : discQ c.β γ c.κ c.σ < 0) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Nonempty (Prop81General.Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0) :=
  CaseIIBasis.prop81_caseII (inProblem c γ hc hγ0.le) (in_assumption82II c γ hc hγ0 hγ1 hD)
    (Multiset.mem_singleton_self _) (in_assumption84II c γ hc hγ0 hγ1 hD) 𝔼 t0

/-- **Woodford (2003), Proposition 8.1, p. 553, for the inflation-inertia model at every
admissible calibration** (`0 < γ ≤ 1`; real roots, the double root, or a complex pair), for any
expectation system. -/
theorem in_prop81_all (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) : Nonempty (Prop81General.Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0) := by
  rcases le_or_gt 0 (discQ c.β γ c.κ c.σ) with hD | hD
  · exact in_prop81_real c γ hc hγ0 hγ1 hD 𝔼 t0
  · exact in_prop81_complex c γ hc hγ0 hγ1 hD 𝔼 t0

end Woodford.OptimalPolicyRules.InertiaProp8182
