/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureStabilityModels
import OptimalPolicyRules.GeneralTheoryLinks
import OptimalPolicyRules.InertiaProp8182

/-!
# Proposition 8.2 with genuine conditional expectations in the book's two models

Woodford (2003), *Interest and Prices*, Chapter 8, Proposition 8.2 (p. 555) with Assumption 8.5
(App. G.2, p. 719) and the deflating split of App. G.1 (pp. 717–718), for the basic
neo-Wicksellian model of §3.1 (`GeneralLinks.nkProblem`) and the inflation-inertia model of §3.2
(`GeneralLinksInertia.inProblem`).

`OptimalRulesMeasureGeneral.m_prop82_general` (every bounded adapted disturbance) and
`OptimalRulesMeasureConverse.m_prop82_var` (VAR disturbances) take as hypotheses a geometrically
stable `H`, a deflating split and Assumption 8.5 for its `Λ`, and degree bounds on the
representation. Here all of them are discharged:

* **basic model** (`nk_m_prop82_general`, `nk_m_prop82_var`): with `n_Z = 0` the split is the
  **empty split** (`emptySplit`: `J`, `Ψ` empty, `K = A₂₂'`), its `Λ` is the hand-computed
  `GeneralLinks.nkΛ` (`GeneralTheoryLinks.NK.nk_Λmat`), Assumption 8.5 is
  `GeneralTheoryLinks.NK.nk_assumption85`, and `H` is geometrically stable
  (`OptimalRulesMeasureStabilityModels.NK.nk_powDecay`);
* **inflation-inertia model, real case** `S² ≥ 4P₂₃` (`in_m_prop82_general`, `in_m_prop82_var`):
  the split is `InertiaSplit.inSplit` solving `λ₂ʳ` forward, Assumption 8.5 is
  `InertiaProp8182.in_assumption85`, and `H` is geometrically stable
  (`OptimalRulesMeasureStabilityModels.Inertia.in_powDecay`).

In both models the degree bounds hold for every window `D ≥ 2 = n_z` (`rank Λ ≤ 2`). So
commitment to the target criterion (1.23) determines exactly one bounded equilibrium a.s., on
every filtered probability space and for every bounded adapted disturbance, and it is the optimal
plan (the solution of (1.1) + (1.9)).

In the complex case `S² < 4P₂₃` of the inertia model no real deflating split exists
(`InertiaSplit.split_isEmpty`), so these theorems do not apply there; the core treats that case
with a quasi-split (`InertiaProp82Complex`).
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureModelsProp82

open MeasureTheory Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure OptimalRulesMeasure OptimalRulesMeasureMarkov OptimalRulesMeasureForecast
  OptimalRulesMeasureGeneral

/-! ### The empty split (`n_Z = 0`) -/

/-- Woodford (2003), App. G.1, pp. 717–718, (G.4), when there are no predetermined variables
(`n_Z = 0`): the **empty deflating split** — `J` and `Ψ` are empty, `J₁` is the empty matrix
(determinant one), there are no selected roots, and `K = A₂₂'` is invertible. -/
noncomputable def emptySplit {ιz : Type*} [Fintype ιz] [DecidableEq ιz]
    (S : LinearRESystem Empty ιz) (β : ℝ) : PencilSplit.DeflatingSplit S β where
  J := 0
  Ψ := 0
  deflate := by
    ext i j
    exact j.elim
  eig_lt := fun μ h => by
    rw [Matrix.det_isEmpty] at h
    exact absurd h one_ne_zero
  J1_det := by
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  K_det := by
    have hK : PencilSplit.Kmat S 0 = S.A22ᵀ := by
      ext i j
      simp [PencilSplit.Kmat, Matrix.mul_apply]
    rw [hK, det_transpose]
    exact S.A22_isUnit.ne_zero

/-! ### The basic model -/

namespace NK

open GeneralLinks GeneralTheoryLinks.NK NKAssumption81.NK
open IRuleBasic (Calib)

variable (c : Calib) (hc : c.Adm)

/-- Woodford (2003), App. G.1 and §3.1, p. 582: the deflating split of the basic model (the
empty split, `n_Z = 0`). -/
noncomputable def nkSplit : PencilSplit.DeflatingSplit (nkProblem c hc).sys (nkProblem c hc).β :=
  emptySplit (nkProblem c hc).sys (nkProblem c hc).β

/-- Woodford (2003), (1.20), p. 553, for the basic model: the `Λ` of the split is
`GeneralLinks.nkΛ = [1 σ/β; κ (1 + κσ)/β]`. -/
theorem nk_Λ_split :
    PencilSplit.Λmat (nkProblem c hc).sys (nkProblem c hc).β (nkSplit c hc).J = nkΛ c :=
  nk_Λmat c hc.2.2.1.ne' hc.1.ne' _

/-- Woodford (2003), **Assumption 8.5**, App. G.2, p. 719, for the basic model, in the form used
by the measure-theoretic Proposition 8.2 (the Krylov part `Assumption85b`). -/
theorem nk_h85 : TargetCriterion.Krylov.Assumption85b
    (PencilSplit.Λmat (nkProblem c hc).sys (nkProblem c hc).β (nkSplit c hc).J)
    (nkProblem c hc).sys.B2 := by
  rw [nk_Λ_split]
  exact (nk_assumption85 c hc).2

/-- Woodford (2003), (1.22), p. 554, for the basic model: the representation has degree at most
`rank Λ ≤ n_z = 2`, so every window `D ≥ 2` carries it. -/
theorem nk_degrees {D : ℕ} (hD2 : 2 ≤ D) :
    (∀ i j, (Adjugate.Bpoly (PencilSplit.Λmat (nkProblem c hc).sys (nkProblem c hc).β
      (nkSplit c hc).J) i j).natDegree ≤ D) ∧
    (Adjugate.alpha (PencilSplit.Λmat (nkProblem c hc).sys (nkProblem c hc).β
      (nkSplit c hc).J)).natDegree ≤ D := by
  have hrk : (PencilSplit.Λmat (nkProblem c hc).sys (nkProblem c hc).β
      (nkSplit c hc).J).rank ≤ D :=
    (rank_le_width _).trans (by simpa using hD2)
  exact ⟨fun i j => (Adjugate.natDegree_Bpoly_le_rank _ i j).trans hrk,
    (Adjugate.natDegree_alpha_le_rank _).trans hrk⟩

/-- **Woodford (2003), Proposition 8.2, p. 555, for the basic model, on every filtered
probability space and for every bounded adapted disturbance**, with Mathlib's conditional
expectation and no hypothesis left: commitment to the target criterion (1.23) built from
`Λ = nkΛ` (a window of `D ≥ 2` lags, any consistent bounded history) determines a bounded
feasible plan, unique a.s., and it solves (1.1) + (1.9) with the history's multiplier — the
optimal plan. -/
theorem nk_m_prop82_general {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)
    (t0 : ℕ) {D : ℕ} (hD : D + 1 ≤ t0) (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ}
    {vh : ℕ → Ω → ℝ} (hhist : HistoryOKm S (nkΛ c) (nkProblem c hc).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {e : ℕ → Ω → Fin 2 → ℝ} (heb : MBoundedV S e)
    (hea : MAdaptedV S e) (Z0 : Ω → Empty → ℝ) :
    ∃ y, MFeasible S (nkProblem c hc) e t0 Z0 y ∧
      MCriterion (nkProblem c hc) (nkSplit c hc) S D t0 qh vh y ∧
      (∀ y', MFeasible S (nkProblem c hc) e t0 Z0 y' →
        MCriterion (nkProblem c hc) (nkSplit c hc) S D t0 qh vh y' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MFOCSystem S (nkProblem c hc) e t0 Z0 (Mh (t0 - 1)) y φ := by
  rw [← nk_Λ_split c hc] at hhist
  exact m_prop82_general (nk_assumption81_perfectForesight c hc 0) S t0
    (OptimalRulesMeasureStabilityModels.NK.nk_powDecay c hc)
    (nkSplit c hc) (nk_h85 c hc) hD (nk_degrees c hc hD2).1 (nk_degrees c hc hD2).2 hhist
    hMhb hMhk hqhb hvhb heb hea (fun i => i.elim)
    ⟨0, Filter.Eventually.of_forall fun _ i => i.elim⟩

/-- **Woodford (2003), Proposition 8.2, p. 555, for the basic model on every VAR economy**
(`s_{t+1} = A s_t + ε_{t+1}`, `c_t = C₂ s_t`, `A` power-bounded), with no hypothesis left: the
criterion (1.23) with `Λ = nkΛ` determines exactly one bounded equilibrium a.s., and it is
optimal from a timeless perspective. -/
theorem nk_m_prop82_var {Ω : Type*} [MeasurableSpace Ω] {ιs : Type*} [Fintype ιs]
    [DecidableEq ιs] (A : Matrix ιs ιs ℝ) (C2 : Matrix (Fin 2) ιs ℝ) (hA : PowBdd A)
    {S : MeasExpectationSystem Ω} {D t0 : ℕ} (hD : D + 1 ≤ t0) (hD2 : 2 ≤ D)
    {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (nkΛ c) (nkProblem c hc).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    (Z0 : Ω → Empty → ℝ) :
    ∃ y, MFeasible S (nkProblem c hc) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y ∧
      MCriterion (nkProblem c hc) (nkSplit c hc) S D t0 qh vh y ∧
      (∀ y', MFeasible S (nkProblem c hc) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y' →
        MCriterion (nkProblem c hc) (nkSplit c hc) S D t0 qh vh y' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MTimelesslyOptimalPlan S (nkProblem c hc) (fun t ω => C2 *ᵥ s t ω) t0 Z0
        (stateX y φ s)
        (zpart (fY (nkProblem c hc) A C2 (nk_assumption81_perfectForesight c hc 0) hA))
        ((FY (nkProblem c hc) A C2 (nk_assumption81_perfectForesight c hc 0) hA).submatrix
          (Sum.inl ∘ Sum.inr) id) y := by
  rw [← nk_Λ_split c hc] at hhist
  exact OptimalRulesMeasureConverse.m_prop82_var (Dsp := nkSplit c hc) A C2
    (nk_assumption81_perfectForesight c hc 0) hA
    (OptimalRulesMeasureStabilityModels.NK.nk_powDecay_Hn c hc A C2 hA) (nk_h85 c hc) hD
    (nk_degrees c hc hD2).1 (nk_degrees c hc hD2).2 hhist hMhb hMhk hqhb hvhb hs
    (fun i => i.elim) ⟨0, Filter.Eventually.of_forall fun _ i => i.elim⟩

end NK

/-! ### The inflation-inertia model, real case -/

namespace Inertia

open GeneralLinksInertia InertiaSplit CubicRoots InertiaAssumption81
open IRuleBasic (Calib)

variable (c : Calib) (γ : ℝ) (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
  (hdisc : 0 ≤ discQ c.β γ c.κ c.σ)

/-- Woodford (2003), App. G.6, pp. 725–726, and §3.2: the deflating split of the
inflation-inertia model in the real case `S² ≥ 4P₂₃` (`InertiaSplit.inSplit`, solving the root
`λ₂ʳ` forward). -/
noncomputable def inRealSplit :
    PencilSplit.DeflatingSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β :=
  inSplit c γ hc hγ0 hγ1 (quadQ_lam2r hdisc)

/-- Woodford (2003), **Assumption 8.5**, App. G.2, p. 719, for the inflation-inertia model in the
real case (`InertiaProp8182.in_assumption85`), in the form used by the measure-theoretic
Proposition 8.2. -/
theorem in_h85 : TargetCriterion.Krylov.Assumption85b
    (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β
      (inRealSplit c γ hc hγ0 hγ1 hdisc).J) (inProblem c γ hc hγ0.le).sys.B2 :=
  (InertiaProp8182.in_assumption85 c γ hc hγ0 hγ1 (quadQ_lam2r hdisc)).2

/-- Woodford (2003), (1.22), p. 554, for the inflation-inertia model: the representation has
degree at most `rank Λ ≤ n_z = 2`, so every window `D ≥ 2` carries it. -/
theorem in_degrees {D : ℕ} (hD2 : 2 ≤ D) :
    (∀ i j, (Adjugate.Bpoly (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys
      (inProblem c γ hc hγ0.le).β (inRealSplit c γ hc hγ0 hγ1 hdisc).J) i j).natDegree ≤ D) ∧
    (Adjugate.alpha (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β
      (inRealSplit c γ hc hγ0 hγ1 hdisc).J)).natDegree ≤ D := by
  have hrk : (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β
      (inRealSplit c γ hc hγ0 hγ1 hdisc).J).rank ≤ D :=
    (rank_le_width _).trans (by simpa using hD2)
  exact ⟨fun i j => (Adjugate.natDegree_Bpoly_le_rank _ i j).trans hrk,
    (Adjugate.natDegree_alpha_le_rank _).trans hrk⟩

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model in the real case
`S² ≥ 4P₂₃`, on every filtered probability space and for every bounded adapted disturbance**, with
Mathlib's conditional expectation and no hypothesis left beyond the calibration (`0 < γ ≤ 1`):
commitment to the target criterion (1.23) built from the split `inRealSplit` (a window of
`D ≥ 2` lags, any consistent bounded history) determines a bounded feasible plan, unique a.s.,
and it solves (1.1) + (1.9) — the optimal plan. -/
theorem in_m_prop82_general {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)
    (t0 : ℕ) {D : ℕ} (hD : D + 1 ≤ t0) (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ}
    {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys
      (inProblem c γ hc hγ0.le).β (inRealSplit c γ hc hγ0 hγ1 hdisc).J)
      (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {e : ℕ → Ω → Fin 2 → ℝ} (heb : MBoundedV S e)
    (hea : MAdaptedV S e) {Z0 : Ω → Unit → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S (inProblem c γ hc hγ0.le) e t0 Z0 y ∧
      MCriterion (inProblem c γ hc hγ0.le) (inRealSplit c γ hc hγ0 hγ1 hdisc) S D t0 qh vh y ∧
      (∀ y', MFeasible S (inProblem c γ hc hγ0.le) e t0 Z0 y' →
        MCriterion (inProblem c γ hc hγ0.le) (inRealSplit c γ hc hγ0 hγ1 hdisc) S D t0 qh vh y' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MFOCSystem S (inProblem c γ hc hγ0.le) e t0 Z0 (Mh (t0 - 1)) y φ :=
  m_prop82_general (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) S t0
    (OptimalRulesMeasureStabilityModels.Inertia.in_powDecay c γ hc hγ0 hγ1)
    (inRealSplit c γ hc hγ0 hγ1 hdisc) (in_h85 c γ hc hγ0 hγ1 hdisc) hD
    (in_degrees c γ hc hγ0 hγ1 hdisc hD2).1 (in_degrees c γ hc hγ0 hγ1 hdisc hD2).2 hhist
    hMhb hMhk hqhb hvhb heb hea hZk hZb

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model in the real case,
on every VAR economy** (`A` power-bounded), with no hypothesis left beyond the calibration: the
criterion (1.23) determines exactly one bounded equilibrium a.s., and it is optimal from a
timeless perspective. -/
theorem in_m_prop82_var {Ω : Type*} [MeasurableSpace Ω] {ιs : Type*} [Fintype ιs]
    [DecidableEq ιs] (A : Matrix ιs ιs ℝ) (C2 : Matrix (Fin 2) ιs ℝ) (hA : PowBdd A)
    {S : MeasExpectationSystem Ω} {D t0 : ℕ} (hD : D + 1 ≤ t0) (hD2 : 2 ≤ D)
    {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys
      (inProblem c γ hc hγ0.le).β (inRealSplit c γ hc hγ0 hγ1 hdisc).J)
      (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {Z0 : Ω → Unit → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y ∧
      MCriterion (inProblem c γ hc hγ0.le) (inRealSplit c γ hc hγ0 hγ1 hdisc) S D t0 qh vh y ∧
      (∀ y', MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y' →
        MCriterion (inProblem c γ hc hγ0.le) (inRealSplit c γ hc hγ0 hγ1 hdisc) S D t0 qh vh y' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MTimelesslyOptimalPlan S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0
        (stateX y φ s)
        (zpart (fY (inProblem c γ hc hγ0.le) A C2
          (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA))
        ((FY (inProblem c γ hc hγ0.le) A C2
          (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA).submatrix
          (Sum.inl ∘ Sum.inr) id) y :=
  OptimalRulesMeasureConverse.m_prop82_var (Dsp := inRealSplit c γ hc hγ0 hγ1 hdisc) A C2
    (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA
    (OptimalRulesMeasureStabilityModels.Inertia.in_powDecay_Hn c γ hc hγ0 hγ1 A C2 hA)
    (in_h85 c γ hc hγ0 hγ1 hdisc) hD (in_degrees c γ hc hγ0 hγ1 hdisc hD2).1
    (in_degrees c γ hc hγ0 hγ1 hdisc hD2).2 hhist hMhb hMhk hqhb hvhb hs hZk hZb

end Inertia

end Woodford.OptimalPolicyRules.OptimalRulesMeasureModelsProp82
