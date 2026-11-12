/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureQuasiSplit
import OptimalPolicyRules.OptimalRulesMeasureModelsProp82
import OptimalPolicyRules.InertiaProp82Complex

/-!
# Proposition 8.2 for the inflation-inertia model in the complex case, with conditional expectations

Woodford (2003), *Interest and Prices*, Chapter 8, Proposition 8.2 (p. 555) with Assumption 8.5
(App. G.2, p. 719), for the inflation-inertia model of §3.2 (pp. 592–604) when `S² < 4P₂₃`: the
roots `λ₂, λ₃` of Proposition 8.7 are a complex pair, no real deflating split exists
(`InertiaSplit.split_isEmpty`), and the core proves Proposition 8.2 through the case-(ii)
quasi-split `InertiaProp82Complex.inQ` (`InertiaProp82Complex.in_prop82_complex_B`).

Here the measure-theoretic Proposition 8.2 is proved for that case on **every filtered
probability space**, with Mathlib's conditional expectation, using the quasi-split theory of
`OptimalRulesMeasureQuasiSplit`; no hypothesis is left beyond the calibration (`0 < γ ≤ 1`):

* `in_h85_quasi`, `in_degrees_quasi`: for **every** quasi-split of the inertia model,
  Assumption 8.5 holds for its `Λ` (`InertiaProp82Complex.in_assumption85_gen`, since `K` is
  invertible) and the representation has degree `≤ rank Λ ≤ 2`;
* `in_m_prop82_quasi_general`, `in_m_prop82_quasi_var`: Proposition 8.2 for every quasi-split
  (every bounded adapted disturbance; VAR disturbances with timeless optimality);
* `in_m_prop82_complex_general`, `in_m_prop82_complex_var`: **the complex case** `discQ < 0`, with
  `inQ`;
* `in_m_prop82_all_general`, `in_m_prop82_all_var`: **every admissible calibration** — a
  quasi-split exists (the real split of `OptimalRulesMeasureModelsProp82.Inertia.inRealSplit` as
  a quasi-split when `discQ ≥ 0`, `inQ` when `discQ < 0`) for which the measure Proposition 8.2
  holds;
* links with the core: `in_mCriterion_unit_iff` (on the one-point space the criterion is the
  core criterion of `InertiaProp82Complex.in_prop82_complex_B` under perfect foresight),
  `in_m_prop82_complex_unit` (the measure theorem there, stated with the core criterion and
  sure equality), and `in_real_criterion_iff` (in the real case the quasi-split criterion is the
  criterion of `OptimalRulesMeasureModelsProp82.Inertia.in_m_prop82_general`).
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureInertiaComplex

open MeasureTheory Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure OptimalRulesMeasure OptimalRulesMeasureMarkov OptimalRulesMeasureQuasiSplit
open GeneralLinksInertia CubicRoots InertiaAssumption81
open IRuleBasic (Calib)

variable (c : Calib) (γ : ℝ) (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)

/-! ### Every quasi-split of the inertia model -/

/-- Woodford (2003), **Assumption 8.5**, App. G.2, p. 719, for the inflation-inertia model, for the
`Λ` of **every** quasi-split (`K` is invertible by construction;
`InertiaProp82Complex.in_assumption85_gen`), in the form used by the measure Proposition 8.2. -/
theorem in_h85_quasi {ιc : Type*} [Fintype ιc] [DecidableEq ιc]
    (Q : Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β ιc) :
    TargetCriterion.Krylov.Assumption85b
      (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β (Q.Jp * Q.P))
      (inProblem c γ hc hγ0.le).sys.B2 :=
  (InertiaProp82Complex.in_assumption85_gen c γ hc hγ0.le (Q.Jp * Q.P) Q.K_det).2

/-- Woodford (2003), (1.22), p. 554, for the inflation-inertia model and any quasi-split: the
representation has degree at most `rank Λ ≤ n_z = 2`, so every window `D ≥ 2` carries it. -/
theorem in_degrees_quasi {ιc : Type*} [Fintype ιc] [DecidableEq ιc]
    (Q : Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β ιc)
    {D : ℕ} (hD2 : 2 ≤ D) :
    (∀ i j, (Adjugate.Bpoly (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys
      (inProblem c γ hc hγ0.le).β (Q.Jp * Q.P)) i j).natDegree ≤ D) ∧
    (Adjugate.alpha (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β
      (Q.Jp * Q.P))).natDegree ≤ D := by
  have hrk : (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β
      (Q.Jp * Q.P)).rank ≤ D :=
    (rank_le_width _).trans (by simpa using hD2)
  exact ⟨fun i j => (Adjugate.natDegree_Bpoly_le_rank _ i j).trans hrk,
    (Adjugate.natDegree_alpha_le_rank _).trans hrk⟩

include hγ1 in
/-- Woodford (2003), **Proposition 8.2, p. 555, for the inflation-inertia model and any
quasi-split, on every filtered probability space and for every bounded adapted disturbance**:
commitment to the criterion (1.23) built from the quasi-split (a window of `D ≥ 2` lags, any
consistent bounded history) determines a bounded feasible plan, unique a.s., and it solves
(1.1) + (1.9) — the optimal plan. No hypothesis beyond the calibration `0 < γ ≤ 1`. -/
theorem in_m_prop82_quasi_general {ιc : Type*} [Fintype ιc] [DecidableEq ιc]
    (Q : Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β ιc)
    {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω) (t0 : ℕ) {D : ℕ}
    (hD : D + 1 ≤ t0) (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys
      (inProblem c γ hc hγ0.le).β (Q.Jp * Q.P)) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {e : ℕ → Ω → Fin 2 → ℝ} (heb : MBoundedV S e)
    (hea : MAdaptedV S e) {Z0 : Ω → Unit → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S (inProblem c γ hc hγ0.le) e t0 Z0 y ∧
      MCriterionQ (inProblem c γ hc hγ0.le) Q S D t0 qh vh y ∧
      (∀ y', MFeasible S (inProblem c γ hc hγ0.le) e t0 Z0 y' →
        MCriterionQ (inProblem c γ hc hγ0.le) Q S D t0 qh vh y' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MFOCSystem S (inProblem c γ hc hγ0.le) e t0 Z0 (Mh (t0 - 1)) y φ :=
  m_prop82_generalQ (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) S t0
    (OptimalRulesMeasureStabilityModels.Inertia.in_powDecay c γ hc hγ0 hγ1) Q
    (in_h85_quasi c γ hc hγ0 Q) hD (in_degrees_quasi c γ hc hγ0 Q hD2).1
    (in_degrees_quasi c γ hc hγ0 Q hD2).2 hhist hMhb hMhk hqhb hvhb heb hea hZk hZb

/-- Woodford (2003), **Proposition 8.2, p. 555, for the inflation-inertia model and any
quasi-split, on every VAR economy** (`A` power-bounded): the criterion (1.23) determines exactly
one bounded equilibrium a.s., and it is optimal from a timeless perspective. -/
theorem in_m_prop82_quasi_var {ιc : Type*} [Fintype ιc] [DecidableEq ιc]
    (Q : Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β ιc)
    {Ω : Type*} [MeasurableSpace Ω] {ιs : Type*} [Fintype ιs] [DecidableEq ιs]
    (A : Matrix ιs ιs ℝ) (C2 : Matrix (Fin 2) ιs ℝ) (hA : PowBdd A) {S : MeasExpectationSystem Ω}
    {D t0 : ℕ} (hD : D + 1 ≤ t0) (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys
      (inProblem c γ hc hγ0.le).β (Q.Jp * Q.P)) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {Z0 : Ω → Unit → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y ∧
      MCriterionQ (inProblem c γ hc hγ0.le) Q S D t0 qh vh y ∧
      (∀ y', MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y' →
        MCriterionQ (inProblem c γ hc hγ0.le) Q S D t0 qh vh y' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MTimelesslyOptimalPlan S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0
        (stateX y φ s)
        (zpart (fY (inProblem c γ hc hγ0.le) A C2
          (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA))
        ((FY (inProblem c γ hc hγ0.le) A C2
          (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA).submatrix
          (Sum.inl ∘ Sum.inr) id) y :=
  m_prop82_varQ (Q := Q) A C2 (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA
    (OptimalRulesMeasureStabilityModels.Inertia.in_powDecay_Hn c γ hc hγ0 hγ1 A C2 hA)
    (in_h85_quasi c γ hc hγ0 Q) hD (in_degrees_quasi c γ hc hγ0 Q hD2).1
    (in_degrees_quasi c γ hc hγ0 Q hD2).2 hhist hMhb hMhk hqhb hvhb hs hZk hZb

/-! ### The complex case -/

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model in the complex
case `S² < 4P₂₃`, on every filtered probability space and for every bounded adapted
disturbance**, with Mathlib's conditional expectation and no hypothesis left beyond the
calibration (`0 < γ ≤ 1`): commitment to the target criterion (1.23) built from the case-(ii)
quasi-split `InertiaProp82Complex.inQ` (a window of `D ≥ 2` lags, any consistent bounded history)
determines a bounded feasible plan, unique a.s., and it solves (1.1) + (1.9) — the optimal
plan. -/
theorem in_m_prop82_complex_general (hdisc : discQ c.β γ c.κ c.σ < 0) {Ω : Type*}
    [MeasurableSpace Ω] (S : MeasExpectationSystem Ω) (t0 : ℕ) {D : ℕ} (hD : D + 1 ≤ t0)
    (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys
      (inProblem c γ hc hγ0.le).β ((InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc).Jp *
        (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc).P))
      (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {e : ℕ → Ω → Fin 2 → ℝ} (heb : MBoundedV S e)
    (hea : MAdaptedV S e) {Z0 : Ω → Unit → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S (inProblem c γ hc hγ0.le) e t0 Z0 y ∧
      MCriterionQ (inProblem c γ hc hγ0.le) (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc) S D
        t0 qh vh y ∧
      (∀ y', MFeasible S (inProblem c γ hc hγ0.le) e t0 Z0 y' →
        MCriterionQ (inProblem c γ hc hγ0.le) (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc) S
          D t0 qh vh y' → ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MFOCSystem S (inProblem c γ hc hγ0.le) e t0 Z0 (Mh (t0 - 1)) y φ :=
  in_m_prop82_quasi_general c γ hc hγ0 hγ1 (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc) S t0
    hD hD2 hhist hMhb hMhk hqhb hvhb heb hea hZk hZb

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model in the complex
case, on every VAR economy** (`A` power-bounded), with no hypothesis left beyond the calibration:
the criterion (1.23) of the case-(ii) quasi-split determines exactly one bounded equilibrium
a.s., and it is optimal from a timeless perspective. -/
theorem in_m_prop82_complex_var (hdisc : discQ c.β γ c.κ c.σ < 0) {Ω : Type*} [MeasurableSpace Ω]
    {ιs : Type*} [Fintype ιs] [DecidableEq ιs] (A : Matrix ιs ιs ℝ) (C2 : Matrix (Fin 2) ιs ℝ)
    (hA : PowBdd A) {S : MeasExpectationSystem Ω} {D t0 : ℕ} (hD : D + 1 ≤ t0) (hD2 : 2 ≤ D)
    {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys
      (inProblem c γ hc hγ0.le).β ((InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc).Jp *
        (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc).P))
      (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {Z0 : Ω → Unit → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y ∧
      MCriterionQ (inProblem c γ hc hγ0.le) (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc) S D
        t0 qh vh y ∧
      (∀ y', MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y' →
        MCriterionQ (inProblem c γ hc hγ0.le) (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc) S
          D t0 qh vh y' → ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MTimelesslyOptimalPlan S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0
        (stateX y φ s)
        (zpart (fY (inProblem c γ hc hγ0.le) A C2
          (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA))
        ((FY (inProblem c γ hc hγ0.le) A C2
          (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA).submatrix
          (Sum.inl ∘ Sum.inr) id) y :=
  in_m_prop82_quasi_var c γ hc hγ0 hγ1 (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc) A C2 hA
    hD hD2 hhist hMhb hMhk hqhb hvhb hs hZk hZb

/-! ### Every admissible calibration -/

include hγ1 in
/-- Woodford (2003), §3.2 and App. G.1: **a quasi-split of the inflation-inertia model exists at
every admissible calibration** (`0 < γ ≤ 1`): the real split
`OptimalRulesMeasureModelsProp82.Inertia.inRealSplit` as a quasi-split
(`Prop81CaseII.quasiOfDeflating`, `ιc = Unit`) when `S² ≥ 4P₂₃`, and the case-(ii) construction
`InertiaProp82Complex.inQ` (`ιc = Option Unit`) when `S² < 4P₂₃`. -/
theorem in_exists_quasi :
    ∃ (ιc : Type) (_ : Fintype ιc) (_ : DecidableEq ιc),
      Nonempty (Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β
        ιc) := by
  rcases le_or_gt 0 (discQ c.β γ c.κ c.σ) with hD | hD
  · exact ⟨Unit, inferInstance, inferInstance, ⟨Prop81CaseII.quasiOfDeflating
      (OptimalRulesMeasureModelsProp82.Inertia.inRealSplit c γ hc hγ0 hγ1 hD)⟩⟩
  · exact ⟨Option Unit, inferInstance, inferInstance,
      ⟨InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hD⟩⟩

include hγ1 in
/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model at every admissible
calibration** (`0 < γ ≤ 1`; three real roots, the double root, or a complex pair), on every
filtered probability space and for every bounded adapted disturbance: there is a quasi-split (the
real split when `S² ≥ 4P₂₃`, the case-(ii) construction when `S² < 4P₂₃`) such that, for every
window of `D ≥ 2` lags and every consistent bounded history, commitment to the criterion (1.23)
determines a bounded feasible plan, unique a.s., that solves (1.1) + (1.9). -/
theorem in_m_prop82_all_general (Ω : Type*) [MeasurableSpace Ω] :
    ∃ (ιc : Type) (_ : Fintype ιc) (_ : DecidableEq ιc)
      (Q : Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β ιc),
      ∀ (S : MeasExpectationSystem Ω) (t0 D : ℕ), D + 1 ≤ t0 → 2 ≤ D →
        ∀ (Mh qh : ℕ → Ω → Fin 2 → ℝ) (vh : ℕ → Ω → ℝ),
        HistoryOKm S (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β
          (Q.Jp * Q.P)) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh →
        MBoundedV S Mh → MAdaptedV S Mh → MBoundedV S qh →
        (∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) →
        ∀ (e : ℕ → Ω → Fin 2 → ℝ), MBoundedV S e → MAdaptedV S e →
        ∀ (Z0 : Ω → Unit → ℝ), MKnownV S t0 Z0 → MBoundedRV S Z0 →
        ∃ y, MFeasible S (inProblem c γ hc hγ0.le) e t0 Z0 y ∧
          MCriterionQ (inProblem c γ hc hγ0.le) Q S D t0 qh vh y ∧
          (∀ y', MFeasible S (inProblem c γ hc hγ0.le) e t0 Z0 y' →
            MCriterionQ (inProblem c γ hc hγ0.le) Q S D t0 qh vh y' →
            ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
          ∃ φ, MFOCSystem S (inProblem c γ hc hγ0.le) e t0 Z0 (Mh (t0 - 1)) y φ := by
  obtain ⟨ιc, i1, i2, ⟨Q⟩⟩ := in_exists_quasi c γ hc hγ0 hγ1
  exact ⟨ιc, i1, i2, Q, fun S t0 D hD hD2 Mh qh vh hhist hMhb hMhk hqhb hvhb e heb hea Z0 hZk
    hZb => in_m_prop82_quasi_general c γ hc hγ0 hγ1 Q S t0 hD hD2 hhist hMhb hMhk hqhb hvhb heb
      hea hZk hZb⟩

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model at every admissible
calibration, on every VAR economy** (`A` power-bounded): there is a quasi-split such that the
criterion (1.23) determines exactly one bounded equilibrium a.s., optimal from a timeless
perspective. -/
theorem in_m_prop82_all_var (Ω : Type*) [MeasurableSpace Ω] :
    ∃ (ιc : Type) (_ : Fintype ιc) (_ : DecidableEq ιc)
      (Q : Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β ιc),
      ∀ {ιs : Type} [Fintype ιs] [DecidableEq ιs] (A : Matrix ιs ιs ℝ)
        (C2 : Matrix (Fin 2) ιs ℝ) (hA : PowBdd A) (S : MeasExpectationSystem Ω) (t0 D : ℕ),
        D + 1 ≤ t0 → 2 ≤ D → ∀ (Mh qh : ℕ → Ω → Fin 2 → ℝ) (vh : ℕ → Ω → ℝ),
        HistoryOKm S (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β
          (Q.Jp * Q.P)) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh →
        MBoundedV S Mh → MAdaptedV S Mh → MBoundedV S qh →
        (∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) →
        ∀ (s : ℕ → Ω → ιs → ℝ), IsVAR S A s →
        ∀ (Z0 : Ω → Unit → ℝ), MKnownV S t0 Z0 → MBoundedRV S Z0 →
        ∃ y, MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y ∧
          MCriterionQ (inProblem c γ hc hγ0.le) Q S D t0 qh vh y ∧
          (∀ y', MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y' →
            MCriterionQ (inProblem c γ hc hγ0.le) Q S D t0 qh vh y' →
            ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
          ∃ φ, MTimelesslyOptimalPlan S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0
            (stateX y φ s)
            (zpart (fY (inProblem c γ hc hγ0.le) A C2
              (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA))
            ((FY (inProblem c γ hc hγ0.le) A C2
              (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA).submatrix
              (Sum.inl ∘ Sum.inr) id) y := by
  obtain ⟨ιc, i1, i2, ⟨Q⟩⟩ := in_exists_quasi c γ hc hγ0 hγ1
  exact ⟨ιc, i1, i2, Q, fun A C2 hA S t0 D hD hD2 Mh qh vh hhist hMhb hMhk hqhb hvhb s hs Z0 hZk
    hZb => in_m_prop82_quasi_var c γ hc hγ0 hγ1 Q A C2 hA hD hD2 hhist hMhb hMhk hqhb hvhb hs
      hZk hZb⟩

/-! ### Links with the core and with the real case -/

/-- Woodford (2003), **(1.23), complex case (link with the core)**: on the one-point probability
space the measure-theoretic criterion of `inQ` is exactly the core criterion
`Prop82General.Prop82M.CriterionM (Prop81CaseII.prop81II _ inQ perfectForesight t₀)` of
`InertiaProp82Complex.in_prop82_complex_B` (at `𝔼 = perfectForesight`). -/
theorem in_mCriterion_unit_iff (hdisc : discQ c.β γ c.κ c.σ < 0) {D t0 : ℕ}
    (qh : ℕ → Unit → Fin 2 → ℝ) (vh : ℕ → Unit → ℝ)
    (y : ℕ → Unit → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) :
    MCriterionQ (inProblem c γ hc hγ0.le) (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc)
        Bridge.unitSystem D t0 qh vh y ↔
      Prop82General.Prop82M.CriterionM (Prop81CaseII.prop81II _
        (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc) perfectForesight t0) D qh vh y :=
  mCriterionQ_unit_iff qh vh y

/-- Woodford (2003), **Proposition 8.2, p. 555, inertia model, complex case, on the one-point
space (link with the core)**: `in_m_prop82_complex_general` on `Bridge.unitSystem`, stated with
the core criterion of `InertiaProp82Complex.in_prop82_complex_B` (perfect foresight) and sure
equality: there is a bounded feasible plan satisfying the core criterion, every bounded feasible
plan satisfying it equals that plan from `t₀` on, and it solves (1.1) + (1.9). -/
theorem in_m_prop82_complex_unit (hdisc : discQ c.β γ c.κ c.σ < 0) (t0 : ℕ) {D : ℕ}
    (hD : D + 1 ≤ t0) (hD2 : 2 ≤ D) {Mh qh : ℕ → Unit → Fin 2 → ℝ} {vh : ℕ → Unit → ℝ}
    (hhist : HistoryOKm Bridge.unitSystem (PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys
      (inProblem c γ hc hγ0.le).β ((InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc).Jp *
        (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc).P))
      (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV Bridge.unitSystem Mh) (hMhk : MAdaptedV Bridge.unitSystem Mh)
    (hqhb : MBoundedV Bridge.unitSystem qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂Bridge.unitSystem.μ, |vh t ω| ≤ K) {e : ℕ → Unit → Fin 2 → ℝ}
    (heb : MBoundedV Bridge.unitSystem e) (hea : MAdaptedV Bridge.unitSystem e)
    {Z0 : Unit → Unit → ℝ} (hZk : MKnownV Bridge.unitSystem t0 Z0)
    (hZb : MBoundedRV Bridge.unitSystem Z0) :
    ∃ y, MFeasible Bridge.unitSystem (inProblem c γ hc hγ0.le) e t0 Z0 y ∧
      Prop82General.Prop82M.CriterionM (Prop81CaseII.prop81II _
        (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc) perfectForesight t0) D qh vh y ∧
      (∀ y', MFeasible Bridge.unitSystem (inProblem c γ hc hγ0.le) e t0 Z0 y' →
        Prop82General.Prop82M.CriterionM (Prop81CaseII.prop81II _
          (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hdisc) perfectForesight t0) D qh vh y' →
        ∀ t, t0 ≤ t → y' t = y t) ∧
      ∃ φ, MFOCSystem Bridge.unitSystem (inProblem c γ hc hγ0.le) e t0 Z0 (Mh (t0 - 1)) y φ := by
  obtain ⟨y, h1, h2, h3, h4⟩ := in_m_prop82_complex_general c γ hc hγ0 hγ1 hdisc
    Bridge.unitSystem t0 hD hD2 hhist hMhb hMhk hqhb hvhb heb hea hZk hZb
  refine ⟨y, h1, (in_mCriterion_unit_iff c γ hc hγ0 hγ1 hdisc qh vh y).mp h2,
    fun y' hy' hc' t ht => ?_, h4⟩
  exact (Bridge.ae_eq_iff_eq Bridge.unitSystem_full _ _).mp
    (h3 y' hy' ((in_mCriterion_unit_iff c γ hc hγ0 hγ1 hdisc qh vh y').mpr hc') t ht)

/-- Woodford (2003), (1.23), real case `S² ≥ 4P₂₃` (link with
`OptimalRulesMeasureModelsProp82`): the quasi-split criterion of the real split, used by
`in_m_prop82_all_general` when `discQ ≥ 0`, is exactly the criterion of
`OptimalRulesMeasureModelsProp82.Inertia.in_m_prop82_general`. -/
theorem in_real_criterion_iff (hdisc : 0 ≤ discQ c.β γ c.κ c.σ) {Ω : Type*} [MeasurableSpace Ω]
    (S : MeasExpectationSystem Ω) (D t0 : ℕ) (qh : ℕ → Ω → Fin 2 → ℝ) (vh : ℕ → Ω → ℝ)
    (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) :
    MCriterionQ (inProblem c γ hc hγ0.le) (Prop81CaseII.quasiOfDeflating
        (OptimalRulesMeasureModelsProp82.Inertia.inRealSplit c γ hc hγ0 hγ1 hdisc)) S D t0 qh vh y ↔
      OptimalRulesMeasureForecast.MCriterion (inProblem c γ hc hγ0.le)
        (OptimalRulesMeasureModelsProp82.Inertia.inRealSplit c γ hc hγ0 hγ1 hdisc) S D t0 qh vh y :=
  mCriterionQ_quasiOfDeflating_iff _ S D t0 qh vh y

end Woodford.OptimalPolicyRules.OptimalRulesMeasureInertiaComplex
