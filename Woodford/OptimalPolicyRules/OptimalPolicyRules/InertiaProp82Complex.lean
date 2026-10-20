/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InertiaAssumption81

/-!
# Proposition 8.2 for the inflation-inertia model in the complex case, and at every calibration

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.5 (App. G.2, p. 719) and
Proposition 8.2 (p. 555), for the inflation-inertia model of §3.2 (pp. 592–604) when
`S² < 4P₂₃` (the roots `λ₂, λ₃` of Proposition 8.7 are a complex pair), where Proposition 8.1 holds
through case (ii) of Assumption 8.2 (`InertiaProp8182.in_prop81_complex`).

## Main results

* `in_assumption85_gen`: **Assumption 8.5 for the `Λ` of every `J`** with `K = A₂₂' + A₁₂'Υ`
  invertible: `K Λ = β⁻¹Ẽ'` and the second row of `K` is `(−κ, 1)`, so
  `Λ₁₀ = κ/det K ≠ 0` and `det Λ = (β det K)⁻¹ ≠ 0` (`InertiaProp8182.assumption85_two`). In
  particular for the `Λ` of the case-(ii) construction (`CaseIIBasis.quasiSplitOfEx`, whatever
  basis it picks), and again for the real splits.
* `in_prop82_complex_B`, `in_prop82_complex_finite`: **Proposition 8.2 in the complex case**,
  unconditionally (Assumption 8.1 from `InertiaAssumption81`): robust optimality with bounded
  initial conditions for any expectation system with pull-out, and in the original sense on a
  finite sample space.
* `in_prop82_all_B`, `in_prop82_all_finite`: **Proposition 8.2 for the inflation-inertia model at
  every admissible calibration** (`0 < γ ≤ 1`; real roots, the double root, or a complex pair).
-/

namespace Woodford.OptimalPolicyRules.InertiaProp82Complex

open Matrix GeneralSetup GeneralFOC GeneralFOC.LQ PencilSplit
open IRuleBasic (Calib)
open CubicRoots CubicRoots.Assumptions
open GeneralLinksInertia (inSys inProblem in_det_ne)
open InertiaSplit
open InertiaAssumption81 (RobustlyOptimalB prop82M_robustlyOptimalB in_assumption81MB
  in_assumption81M_of_finite)

variable (c : Calib) (γ : ℝ) {Ω : Type*}

/-- **Woodford (2003), Assumption 8.5, App. G.2, p. 719, for the inflation-inertia model, for the
`Λ = β⁻¹K⁻¹Ẽ'` of every `3 × 1` matrix `J` with `K` invertible**: `B₂'`, `B₂'Λ` (and `B₂'Λ`,
`B₂'Λ²`) are linearly independent, `B₂ = (0, σ)`. -/
theorem in_assumption85_gen (hc : c.Adm) (hγ : 0 ≤ γ) (J : Matrix (Unit ⊕ Fin 2) Unit ℝ)
    (hK : (Kmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)) J).det ≠ 0) :
    PencilAssumptions.Assumption85
      (Λmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)) c.β J)
      (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).B2 := by
  set S := inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ) with hS
  set K := Kmat S J with hKdef
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hKu : IsUnit K.det := isUnit_iff_ne_zero.mpr hK
  set L := K⁻¹ * S.Etᵀ with hL
  have hKL : K * L = S.Etᵀ := by rw [hL, mul_nonsing_inv_cancel_left _ _ hKu]
  -- the second row of `K` is `(−κ, 1)`
  have hK10 : K 1 0 = -c.κ := by
    simp [hKdef, Kmat, hS, inSys, Matrix.add_apply, Matrix.mul_apply]
  have hK11 : K 1 1 = 1 := by
    simp [hKdef, Kmat, hS, inSys, Matrix.add_apply, Matrix.mul_apply]
  have e10 : -c.κ * L 0 0 + L 1 0 = 0 := by
    have := congrFun (congrFun hKL 1) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, hK10, hK11] at this
    simpa [hS, inSys] using this
  have e00 : K 0 0 * L 0 0 + K 0 1 * L 1 0 = c.β := by
    have := congrFun (congrFun hKL 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two] at this
    simpa [hS, inSys] using this
  have hdetK : K.det = K 0 0 + c.κ * K 0 1 := by
    rw [det_fin_two, hK10, hK11]
    ring
  have hL00 : L 0 0 ≠ 0 := by
    intro h0
    have : K.det * L 0 0 = c.β := by rw [hdetK]; linear_combination e00 - K 0 1 * e10
    rw [h0, mul_zero] at this
    exact hβ this.symm
  have hΛ : Λmat S c.β J = c.β⁻¹ • L := by rw [Λmat, hL]
  refine InertiaProp8182.assumption85_two hc.2.2.1.ne' ?_ ?_
  · rw [hΛ, Matrix.smul_apply, smul_eq_mul]
    refine mul_ne_zero (inv_ne_zero hβ) ?_
    have : L 1 0 = c.κ * L 0 0 := by linarith
    rw [this]
    exact mul_ne_zero hc.2.2.2.1.ne' hL00
  · rw [hΛ, det_smul, hL, det_mul, det_nonsing_inv, det_transpose, in_Et_det,
      Ring.inverse_eq_inv']
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hβ)) (mul_ne_zero (inv_ne_zero hK) hβ)

/-! ### The complex case -/

/-- Woodford (2003), App. G.1 and Assumption 8.4 (ii), for the inflation-inertia model in the
complex case `S² < 4P₂₃`: the real basis construction behind Proposition 8.1 in case (ii)
(`CaseIIBasis.quasiSplitOfEx` for `InertiaProp8182.in_assumption82II` and
`InertiaProp8182.in_assumption84II`). -/
noncomputable def inQ (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hD : discQ c.β γ c.κ c.σ < 0) :
    Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β
      (Option Unit) :=
  CaseIIBasis.quasiSplitOfEx (inProblem c γ hc hγ0.le)
    (InertiaProp8182.in_assumption82II c γ hc hγ0 hγ1 hD) (Multiset.mem_singleton_self _)
    (InertiaProp8182.in_assumption84II c γ hc hγ0 hγ1 hD)

/-- **Woodford (2003), Assumption 8.5, App. G.2, p. 719, for the inflation-inertia model in the
complex case**: it holds for the `Λ` of the case-(ii) construction (`in_assumption85_gen`, with
`K` invertible by construction). -/
theorem in_assumption85_complex (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hD : discQ c.β γ c.κ c.σ < 0) :
    PencilAssumptions.Assumption85 (Λmat (inProblem c γ hc hγ0.le).sys c.β
      ((inQ c γ hc hγ0 hγ1 hD).Jp * (inQ c γ hc hγ0 hγ1 hD).P))
      (inProblem c γ hc hγ0.le).sys.B2 :=
  in_assumption85_gen c γ hc hγ0.le _ (inQ c γ hc hγ0 hγ1 hD).K_det

/-- Woodford (2003), p. 555 (tool): `rank Ẽ = 2` for the inertia model, so `rank Λ = 2`
(`Prop81General.rank_Λmat`) and the criterion (1.23) needs `D ≥ 2` lags. -/
theorem in_rank_Λ (hc : c.Adm) (hγ0 : 0 < γ) {J : Matrix (Unit ⊕ Fin 2) Unit ℝ}
    (hK : (Kmat (inProblem c γ hc hγ0.le).sys J).det ≠ 0) :
    (Λmat (inProblem c γ hc hγ0.le).sys c.β J).rank = 2 := by
  rw [Prop81General.rank_Λmat (inProblem c γ hc hγ0.le).sys hc.1.ne' hK]
  change (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)).Et.rank = 2
  rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
  · simp
  · rw [in_Et_det]
    exact isUnit_iff_ne_zero.mpr hc.1.ne'

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model in the complex
case `S² < 4P₂₃`, unconditionally**: commitment to the target criterion (1.23) built from the
case-(ii) construction of Proposition 8.1 (`Prop81CaseII.prop81II`) is robustly optimal for every
bounded adapted disturbance and every bounded initial condition, for any expectation system with
pull-out, a window of `D ≥ 2` lags and any consistent bounded history (Assumption 8.1:
`InertiaAssumption81.in_assumption81MB`; Assumption 8.5: `in_assumption85_complex`). -/
theorem in_prop82_complex_B {𝔼 : ExpectationSystem Ω} {t0 : ℕ} (hc : c.Adm) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hD : discQ c.β γ c.κ c.σ < 0) (hpull : 𝔼.PullOut) {D : ℕ}
    (hD1 : D + 1 ≤ t0) (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK (Λmat (inProblem c γ hc hγ0.le).sys c.β
      ((inQ c γ hc hγ0 hγ1 hD).Jp * (inQ c γ hc hγ0 hγ1 hD).P))
      (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimalB (κ := Fin 2) (inProblem c γ hc hγ0.le) 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM
        (Prop81CaseII.prop81II _ (inQ c γ hc hγ0 hγ1 hD) 𝔼 t0) D qh vh y)
      (fun _ y t ω => zpart (y t ω)) := by
  have hrk := in_rank_Λ c γ hc hγ0 (inQ c γ hc hγ0 hγ1 hD).K_det
  have hrk' : (Λmat (inProblem c γ hc hγ0.le).sys c.β
      ((inQ c γ hc hγ0 hγ1 hD).Jp * (inQ c γ hc hγ0 hγ1 hD).P)).rank ≤ D := by
    rw [hrk]
    exact hD2
  exact prop82M_robustlyOptimalB hpull (in_assumption81MB c γ hc hγ0 hγ1 𝔼 t0)
    (Prop81CaseII.prop81II _ (inQ c γ hc hγ0 hγ1 hD) 𝔼 t0)
    (in_assumption85_complex c γ hc hγ0 hγ1 hD).2 hD1
    (fun i j => (Adjugate.natDegree_Bpoly_le_rank _ i j).trans hrk')
    ((Adjugate.natDegree_alpha_le_rank _).trans hrk') hhist hMhb hMhk hqhb hvhb

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model in the complex
case, on a finite sample space, in the original robust-optimality sense** (every initial
condition): `CaseIIBasis.prop82_caseII` with Assumption 8.1 from
`InertiaAssumption81.in_assumption81M_of_finite` and Assumption 8.5 from
`in_assumption85_complex`. -/
theorem in_prop82_complex_finite [Finite Ω] {𝔼 : ExpectationSystem Ω} {t0 : ℕ} (hc : c.Adm)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hD : discQ c.β γ c.κ c.σ < 0) (hpull : 𝔼.PullOut) {D : ℕ}
    (hD1 : D + 1 ≤ t0) (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK (Λmat (inProblem c γ hc hγ0.le).sys c.β
      ((inQ c γ hc hγ0 hγ1 hD).Jp * (inQ c γ hc hγ0 hγ1 hD).P))
      (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimal (κ := Fin 2) (inProblem c γ hc hγ0.le) 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM
        (Prop81CaseII.prop81II _ (inQ c γ hc hγ0 hγ1 hD) 𝔼 t0) D qh vh y)
      (fun _ y t ω => zpart (y t ω)) := by
  have hE : (inProblem c γ hc hγ0.le).sys.Et.rank ≤ D := by
    have := in_rank_Λ c γ hc hγ0 (inQ c γ hc hγ0 hγ1 hD).K_det
    rw [Prop81General.rank_Λmat (inProblem c γ hc hγ0.le).sys hc.1.ne'
      (inQ c γ hc hγ0 hγ1 hD).K_det] at this
    rw [this]
    exact hD2
  exact CaseIIBasis.prop82_caseII hpull (in_assumption81M_of_finite c γ hc hγ0 hγ1 𝔼 t0)
    (InertiaProp8182.in_assumption82II c γ hc hγ0 hγ1 hD) (Multiset.mem_singleton_self _)
    (InertiaProp8182.in_assumption84II c γ hc hγ0 hγ1 hD)
    (in_assumption85_complex c γ hc hγ0 hγ1 hD) hD1 hE hhist hMhb hMhk hqhb hvhb

/-! ### Every admissible calibration -/

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model at every
admissible calibration** (`0 < γ ≤ 1`; three real roots, the double root, or a complex pair), for
any expectation system with pull-out: there is a matrix set of the corrected Proposition 8.1 (the
real split solving `λ₂ʳ` forward, or the case-(ii) construction) such that, for every window of
`D ≥ 2` lags and every consistent bounded history, commitment to the target criterion (1.23)
determines a unique bounded equilibrium, optimal from a timeless perspective, for every bounded
adapted disturbance and every bounded initial condition. -/
theorem in_prop82_all_B (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) (hpull : 𝔼.PullOut) :
    ∃ H : Prop81General.Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0,
      ∀ D, D + 1 ≤ t0 → 2 ≤ D → ∀ (Mh qh : ℕ → Ω → Fin 2 → ℝ) (vh : ℕ → Ω → ℝ),
        TargetCriterion.Prop82.HistoryOK H.Λ (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh →
        BoundedV Mh → AdaptedV 𝔼 Mh → BoundedV qh → (∃ K, ∀ t ω, |vh t ω| ≤ K) →
        RobustlyOptimalB (κ := Fin 2) (inProblem c γ hc hγ0.le) 𝔼 t0
          (fun _ y => Prop82General.Prop82M.CriterionM H D qh vh y)
          (fun _ y t ω => zpart (y t ω)) := by
  rcases le_or_gt 0 (discQ c.β γ c.κ c.σ) with hD | hD
  · exact ⟨_, fun D hD1 hD2 Mh qh vh hhist hMhb hMhk hqhb hvhb =>
      InertiaAssumption81.in_prop82_real_B c γ hc hγ0 hγ1 hD hpull hD1 hD2 hhist hMhb hMhk
        hqhb hvhb⟩
  · exact ⟨_, fun D hD1 hD2 Mh qh vh hhist hMhb hMhk hqhb hvhb =>
      in_prop82_complex_B c γ hc hγ0 hγ1 hD hpull hD1 hD2 hhist hMhb hMhk hqhb hvhb⟩

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model at every
admissible calibration, on a finite sample space, in the original robust-optimality sense**
(every initial condition; e.g. perfect foresight or any finite event tree). -/
theorem in_prop82_all_finite [Finite Ω] (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (hpull : 𝔼.PullOut) :
    ∃ H : Prop81General.Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0,
      ∀ D, D + 1 ≤ t0 → 2 ≤ D → ∀ (Mh qh : ℕ → Ω → Fin 2 → ℝ) (vh : ℕ → Ω → ℝ),
        TargetCriterion.Prop82.HistoryOK H.Λ (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh →
        BoundedV Mh → AdaptedV 𝔼 Mh → BoundedV qh → (∃ K, ∀ t ω, |vh t ω| ≤ K) →
        RobustlyOptimal (κ := Fin 2) (inProblem c γ hc hγ0.le) 𝔼 t0
          (fun _ y => Prop82General.Prop82M.CriterionM H D qh vh y)
          (fun _ y t ω => zpart (y t ω)) := by
  rcases le_or_gt 0 (discQ c.β γ c.κ c.σ) with hD | hD
  · exact ⟨_, fun D hD1 hD2 Mh qh vh hhist hMhb hMhk hqhb hvhb =>
      InertiaAssumption81.in_prop82_real_finite c γ hc hγ0 hγ1 hD hpull hD1 hD2 hhist hMhb hMhk
        hqhb hvhb⟩
  · exact ⟨_, fun D hD1 hD2 Mh qh vh hhist hMhb hMhk hqhb hvhb =>
      in_prop82_complex_finite c γ hc hγ0 hγ1 hD hpull hD1 hD2 hhist hMhb hMhk hqhb hvhb⟩

end Woodford.OptimalPolicyRules.InertiaProp82Complex
