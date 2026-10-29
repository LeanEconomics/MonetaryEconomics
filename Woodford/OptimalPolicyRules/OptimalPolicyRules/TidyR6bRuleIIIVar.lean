/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5aRuleIIIMeasure

/-!
# Rule III on VAR economies: timeless optimality with conditional expectations

Woodford (2003), *Interest and Prices*, Chapter 8, Rule III (3.24), p. 595, with Proposition 8.2
(p. 555) and the Definition of optimality from a timeless perspective (pp. 538–539), on every
filtered probability space with Mathlib's conditional expectation.

`TidyR5aRuleIIIMeasure.AllCases.m_prop82_III_all` proves that commitment to Rule III's target
criterion determines a bounded plan, unique a.s., that solves (1.1) + (1.9), for every bounded
adapted disturbance. This module adds the VAR / timeless-optimality packaging, the analogue for
Rule III of `OptimalRulesMeasureInertiaComplex.in_m_prop82_quasi_var` and
`OptimalRulesMeasureInertiaComplex.in_m_prop82_all_var`: when the exogenous state is a VAR(1) in
the conditional-expectation sense (`OptimalRulesMeasureMarkov.IsVAR`, `A` power-bounded), the plan
that Rule III determines is **optimal from a timeless perspective**
(`OptimalRulesMeasure.MTimelesslyOptimalPlan`): `z_t = f⁰ + F X̄_t` a.s. with time-invariant
`f⁰`, `F` and the state `X̄_t = (Z_t, M_{t−1}, s_t)`, and it minimises (1.2) a.s. among all
bounded feasible plans with the same initial constraint.

* `QuasiCase.m_prop82_IIIQ_var`: for the `Λ'` of every quasi-split with the spectral data
  `TidyR5aRuleIIIMeasure.QuasiCase.FactsQ`.
* `AllCases.m_prop82_III_all_var`: **at every admissible calibration `0 < γ ≤ 1`**, there is a
  `Λ'` with Rule III's lag polynomial `(1 − λ₁L)(1 − ½(λ₂ + λ₃)L)` such that on every VAR economy
  Rule III's criterion determines exactly one bounded equilibrium a.s., and it is optimal from a
  timeless perspective.
* `AllCases.m_prop82_III_all_both`: both packagings at once (every bounded adapted disturbance,
  and VAR economies with timeless optimality) from one `Λ'`.
-/

namespace Woodford.OptimalPolicyRules.TidyR6bRuleIIIVar

open MeasureTheory Filter Matrix
open ExpectationsMeasure OptimalRulesMeasure OptimalRulesMeasureMarkov GeneralSetup GeneralFOC.LQ

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Any quasi-split with the spectral data -/

namespace QuasiCase

open IRuleBasic (Calib)
open GeneralLinksInertia (inProblem)
open InertiaAssumption81 (in_assumption81_perfectForesight)
open TidyR5aRuleIIIMeasure.QuasiCase (FactsQ ΛIIIQ MCriterionIIIQ)

variable (c : Calib) (γ : ℝ) (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {ιc : Type*} [Fintype ιc]
  [DecidableEq ιc]
  (Q : Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β ιc)
  (lb : ℝ)

include hγ1 in
/-- **Woodford (2003), Rule III (3.24), p. 595, and Proposition 8.2, p. 555, on every VAR
economy** (`A` power-bounded), with conditional expectations, for the `Λ'` of any quasi-split
with the spectral data `FactsQ`: for every window `D ≥ 2`, every consistent bounded history and
every bounded `Z_{t₀}` known at `t₀`, Rule III's target criterion determines a bounded feasible
plan, every bounded feasible plan satisfying it equals that plan a.s. from `t₀` on, and the plan
is **optimal from a timeless perspective** (Definition, pp. 538–539) with the state
`X̄_t = (Z_t, M_{t−1}, s_t)` and time-invariant coefficients. -/
theorem m_prop82_IIIQ_var (hF : FactsQ c γ hc hγ0 Q lb) {ιs : Type*} [Fintype ιs]
    [DecidableEq ιs] (A : Matrix ιs ιs ℝ) (C2 : Matrix (Fin 2) ιs ℝ) (hA : PowBdd A)
    {S : MeasExpectationSystem Ω} {t0 D : ℕ} (hD1 : D + 1 ≤ t0) (hD2 : 2 ≤ D)
    {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (ΛIIIQ c γ hc hγ0 Q lb) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {Z0 : Ω → Unit → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y ∧
      MCriterionIIIQ c γ hc hγ0 Q lb S D t0 qh vh y ∧
      (∀ y', MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y' →
        MCriterionIIIQ c γ hc hγ0 Q lb S D t0 qh vh y' → ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MTimelesslyOptimalPlan S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0
        (stateX y φ s)
        (zpart (fY (inProblem c γ hc hγ0.le) A C2
          (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA))
        ((FY (inProblem c γ hc hγ0.le) A C2
          (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA).submatrix
          (Sum.inl ∘ Sum.inr) id) y := by
  have hA81 := in_assumption81_perfectForesight c γ hc hγ0 hγ1 0
  have hMb : MBoundedRV S (Mh (t0 - 1)) := by
    obtain ⟨K, hK⟩ := hMhb
    exact ⟨K, hK (t0 - 1)⟩
  obtain ⟨y, φ, hsol, -, hopt⟩ := m_existsUnique_var (inProblem c γ hc hγ0.le) A C2 hA81 hA
    (OptimalRulesMeasureStabilityModels.Inertia.in_powDecay_Hn c γ hc hγ0 hγ1 A C2 hA) hs hZk
    hZb hMb (hMhk (t0 - 1))
  refine ⟨y, hsol.1, TidyR5aRuleIIIMeasure.QuasiCase.m_criterionIIIQ c γ hc hγ0 hγ1 Q lb hF hD1
    hD2 hhist hMhb hMhk hsol, fun y' hy' hc' t ht => ?_, φ, hopt⟩
  obtain ⟨φ', h'⟩ := TidyR5aRuleIIIMeasure.QuasiCase.m_focSystem_of_criterionIIIQ c γ hc hγ0 hγ1
    Q lb hF hD1 hD2 hhist hMhb hMhk hqhb hvhb hy' hc'
  exact (OptimalRulesMeasureForecast.m_focUnique_of_pf hA81.unique S t0 _ Z0 (Mh (t0 - 1)) y' y
    φ' φ h' hsol t ht).1

end QuasiCase

/-! ### Every admissible calibration -/

namespace AllCases

open IRuleBasic (Calib)
open GeneralLinksInertia (inProblem)
open InertiaAssumption81 (in_assumption81_perfectForesight)
open TidyR5aRuleIIIMeasure.QuasiCase (FactsQ ΛIIIQ MCriterionIIIQ)

variable (c : Calib) (γ : ℝ) (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)

include hγ1 in
/-- **Woodford (2003), Rule III (3.24), p. 595, Proposition 8.2, p. 555, and the Definition of
pp. 538–539, at every admissible calibration** (`0 < γ ≤ 1`: three real roots, the double root,
or a complex pair), on every filtered probability space and every VAR economy (`A`
power-bounded): there is a `Λ'` with Rule III's lag polynomial
`det(I − Λ'L) = (1 − λ₁L)(1 − ½(λ₂ + λ₃)L)` such that, for every window `D ≥ 2`, every consistent
bounded history and every bounded `Z_{t₀}` known at `t₀`, Rule III's target criterion determines
exactly one bounded equilibrium a.s., and it is optimal from a timeless perspective. -/
theorem m_prop82_III_all_var :
    ∃ (ιc : Type) (_ : Fintype ιc) (_ : DecidableEq ιc)
      (Q : Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β ιc)
      (lb : ℝ), Adjugate.alpha (ΛIIIQ c γ hc hγ0 Q lb) =
        TidyR5aRuleIIIStochastic.Inertia.ruleIIIpoly c γ ∧
      ∀ {ιs : Type} [Fintype ιs] [DecidableEq ιs] (A : Matrix ιs ιs ℝ)
        (C2 : Matrix (Fin 2) ιs ℝ) (hA : PowBdd A) (S : MeasExpectationSystem Ω) (t0 D : ℕ),
        D + 1 ≤ t0 → 2 ≤ D → ∀ (Mh qh : ℕ → Ω → Fin 2 → ℝ) (vh : ℕ → Ω → ℝ),
        HistoryOKm S (ΛIIIQ c γ hc hγ0 Q lb) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh →
        MBoundedV S Mh → MAdaptedV S Mh → MBoundedV S qh →
        (∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) →
        ∀ (s : ℕ → Ω → ιs → ℝ), IsVAR S A s →
        ∀ (Z0 : Ω → Unit → ℝ), MKnownV S t0 Z0 → MBoundedRV S Z0 →
        ∃ y, MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y ∧
          MCriterionIIIQ c γ hc hγ0 Q lb S D t0 qh vh y ∧
          (∀ y', MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y' →
            MCriterionIIIQ c γ hc hγ0 Q lb S D t0 qh vh y' →
            ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
          ∃ φ, MTimelesslyOptimalPlan S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0
            (stateX y φ s)
            (zpart (fY (inProblem c γ hc hγ0.le) A C2
              (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA))
            ((FY (inProblem c γ hc hγ0.le) A C2
              (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA).submatrix
              (Sum.inl ∘ Sum.inr) id) y := by
  obtain ⟨ιc, i1, i2, Q, lb, hF⟩ := TidyR5aRuleIIIMeasure.AllCases.exists_quasi_facts c γ hc hγ0
    hγ1
  exact ⟨ιc, i1, i2, Q, lb, TidyR5aRuleIIIMeasure.QuasiCase.alpha_ΛIIIQ c γ hc hγ0 hγ1 Q lb hF,
    fun A C2 hA S t0 D hD1 hD2 Mh qh vh hhist hMhb hMhk hqhb hvhb s hs Z0 hZk hZb =>
      QuasiCase.m_prop82_IIIQ_var c γ hc hγ0 hγ1 Q lb hF A C2 hA (S := S) hD1 hD2 hhist hMhb
        hMhk hqhb hvhb hs hZk hZb⟩

include hγ1 in
/-- **Woodford (2003), Rule III (3.24), p. 595, with Proposition 8.2, p. 555, both packagings from
one `Λ'`, at every admissible calibration** (`0 < γ ≤ 1`): there is a `Λ'` with Rule III's lag
polynomial such that (i) for every bounded adapted disturbance Rule III's criterion determines a
bounded plan, unique a.s., solving (1.1) + (1.9), and (ii) on every VAR economy that plan is
optimal from a timeless perspective. -/
theorem m_prop82_III_all_both :
    ∃ (ιc : Type) (_ : Fintype ιc) (_ : DecidableEq ιc)
      (Q : Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β ιc)
      (lb : ℝ), Adjugate.alpha (ΛIIIQ c γ hc hγ0 Q lb) =
        TidyR5aRuleIIIStochastic.Inertia.ruleIIIpoly c γ ∧
      (∀ (S : MeasExpectationSystem Ω) (t0 D : ℕ), D + 1 ≤ t0 → 2 ≤ D →
        ∀ (Mh qh : ℕ → Ω → Fin 2 → ℝ) (vh : ℕ → Ω → ℝ),
        HistoryOKm S (ΛIIIQ c γ hc hγ0 Q lb) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh →
        MBoundedV S Mh → MAdaptedV S Mh → MBoundedV S qh →
        (∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) →
        ∀ (e : ℕ → Ω → Fin 2 → ℝ), MBoundedV S e → MAdaptedV S e →
        ∀ (Z0 : Ω → Unit → ℝ), MKnownV S t0 Z0 → MBoundedRV S Z0 →
        ∃ y, MFeasible S (inProblem c γ hc hγ0.le) e t0 Z0 y ∧
          MCriterionIIIQ c γ hc hγ0 Q lb S D t0 qh vh y ∧
          (∀ y', MFeasible S (inProblem c γ hc hγ0.le) e t0 Z0 y' →
            MCriterionIIIQ c γ hc hγ0 Q lb S D t0 qh vh y' →
            ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
          ∃ φ, MFOCSystem S (inProblem c γ hc hγ0.le) e t0 Z0 (Mh (t0 - 1)) y φ) ∧
      ∀ {ιs : Type} [Fintype ιs] [DecidableEq ιs] (A : Matrix ιs ιs ℝ)
        (C2 : Matrix (Fin 2) ιs ℝ) (hA : PowBdd A) (S : MeasExpectationSystem Ω) (t0 D : ℕ),
        D + 1 ≤ t0 → 2 ≤ D → ∀ (Mh qh : ℕ → Ω → Fin 2 → ℝ) (vh : ℕ → Ω → ℝ),
        HistoryOKm S (ΛIIIQ c γ hc hγ0 Q lb) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh →
        MBoundedV S Mh → MAdaptedV S Mh → MBoundedV S qh →
        (∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) →
        ∀ (s : ℕ → Ω → ιs → ℝ), IsVAR S A s →
        ∀ (Z0 : Ω → Unit → ℝ), MKnownV S t0 Z0 → MBoundedRV S Z0 →
        ∃ y, MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y ∧
          MCriterionIIIQ c γ hc hγ0 Q lb S D t0 qh vh y ∧
          (∀ y', MFeasible S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y' →
            MCriterionIIIQ c γ hc hγ0 Q lb S D t0 qh vh y' →
            ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
          ∃ φ, MTimelesslyOptimalPlan S (inProblem c γ hc hγ0.le) (fun t ω => C2 *ᵥ s t ω) t0 Z0
            (stateX y φ s)
            (zpart (fY (inProblem c γ hc hγ0.le) A C2
              (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA))
            ((FY (inProblem c γ hc hγ0.le) A C2
              (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA).submatrix
              (Sum.inl ∘ Sum.inr) id) y := by
  obtain ⟨ιc, i1, i2, Q, lb, hF⟩ := TidyR5aRuleIIIMeasure.AllCases.exists_quasi_facts c γ hc hγ0
    hγ1
  exact ⟨ιc, i1, i2, Q, lb, TidyR5aRuleIIIMeasure.QuasiCase.alpha_ΛIIIQ c γ hc hγ0 hγ1 Q lb hF,
    fun S t0 D hD1 hD2 Mh qh vh hhist hMhb hMhk hqhb hvhb e heb hea Z0 hZk hZb =>
      TidyR5aRuleIIIMeasure.QuasiCase.m_prop82_IIIQ c γ hc hγ0 hγ1 Q lb hF t0 hD1 hD2 hhist hMhb
        hMhk hqhb hvhb heb hea hZk hZb,
    fun A C2 hA S t0 D hD1 hD2 Mh qh vh hhist hMhb hMhk hqhb hvhb s hs Z0 hZk hZb =>
      QuasiCase.m_prop82_IIIQ_var c γ hc hγ0 hγ1 Q lb hF A C2 hA (S := S) hD1 hD2 hhist hMhb
        hMhk hqhb hvhb hs hZk hZb⟩

end AllCases

end Woodford.OptimalPolicyRules.TidyR6bRuleIIIVar
