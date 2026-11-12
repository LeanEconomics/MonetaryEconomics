/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5aInertiaGammaZero
import OptimalPolicyRules.OptimalRulesMeasureSpectrum

/-!
# The inflation-inertia model at `γ = 0` on a filtered probability space

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.1 (p. 541) and Proposition 8.2
(p. 555), for the inflation-inertia model of §3.2 at `γ = 0`, with Mathlib's conditional
expectation (the measure-theoretic framework of `OptimalRulesMeasure`).

`OptimalRulesMeasureStabilityModels.Inertia.in_m_assumption81MB` and
`OptimalRulesMeasureModelsProp82.Inertia.in_m_prop82_general` cover `0 < γ ≤ 1` (real case). At
`γ = 0` the perfect-foresight Assumption 8.1 is
`TidyR5aInertiaGammaZero.in0_assumption81_perfectForesight`, and the stability of `H` follows from
the Euler pencil:

* `eulerRoot0_nk`: at `γ = 0` a nonzero root `ν` of the Euler pencil of (1.1) + (1.9) is a root of
  the basic model's Euler pencil (the multiplier `ξ` on `Z_{t+1} = π_t` vanishes, and
  `νZ = π` recovers `Z`);
* `in0_noEulerRoot`, `in0_powDecay`: no root on the unit circle
  (`OptimalRulesMeasureSpectrum.nk_noEulerRoot`), so `H` is geometrically stable;
* `in0_m_assumption81MB`: **Assumption 8.1 at `γ = 0` on every filtered probability space and
  for every bounded adapted disturbance**;
* `in0_m_prop82_general`, `in0_m_prop82_var`: **Proposition 8.2 at `γ = 0`** with the split
  `TidyR5aInertiaGammaZero.in0Split` (general disturbances; VAR economies with timeless
  optimality).
-/

namespace Woodford.OptimalPolicyRules.TidyR5aInertiaGammaZeroMeasure

open MeasureTheory Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure OptimalRulesMeasure OptimalRulesMeasureMarkov OptimalRulesMeasureForecast
  OptimalRulesMeasureGeneral
open IRuleBasic (Calib)
open GeneralLinks (nkProblem)
open GeneralLinksInertia (inProblem)
open OptimalRulesMeasureSpectrum (EulerRoot)
open TidyR5aInertiaGammaZero

variable (c : Calib)

/-- **Woodford (2003), (1.1) + (1.9) at `γ = 0`: the Euler pencil of the inertia model reduces
to the basic model's.** A nonzero root `ν` of the Euler pencil of `inProblem` at `γ = 0` is a
root of the Euler pencil of the basic model `nkProblem`. -/
theorem eulerRoot0_nk (hc : c.Adm) {ν : ℂ} (hν : ν ≠ 0)
    (h : EulerRoot (inProblem c 0 hc le_rfl) ν) : EulerRoot (nkProblem c hc) ν := by
  obtain ⟨u, p, hne, h1, h2⟩ := h
  have hβ : (c.β : ℂ) ≠ 0 := by exact_mod_cast hc.1.ne'
  have s1 : ν * u (Sum.inl (Sum.inl ())) = u (Sum.inl (Sum.inr 0)) := by
    have h := congrFun h1 (Sum.inl ())
    simp [inProblem, GeneralLinksInertia.inSys, LinearRESystem.Itil, LinearRESystem.Atil,
      LinearRESystem.Ihat, LinearRESystem.Ahat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have f1 : p (Sum.inl ()) = 0 := by
    have h := congrFun h2 (Sum.inl (Sum.inl ()))
    simp [inProblem, GeneralLinksInertia.inSys, GeneralLinksInertia.inTtil, LinearRESystem.Itil,
      LinearRESystem.Atil, LinearRESystem.Ihat, LinearRESystem.Ahat, LinearRESystem.Bvec,
      LQProblem.T, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three,
      Matrix.mul_apply] at h
    exact h.resolve_left hc.1.ne'
  have hsimpS : ∀ r, (ν • ((inProblem c 0 hc le_rfl).sys.Itil.map Complex.ofReal *ᵥ u)) r =
      ((inProblem c 0 hc le_rfl).sys.Atil.map Complex.ofReal *ᵥ u) r := fun r => congrFun h1 r
  have s2 : ν * (c.β * u (Sum.inl (Sum.inr 0))) =
      u (Sum.inl (Sum.inr 0)) - c.κ * u (Sum.inl (Sum.inr 1)) := by
    have h := hsimpS (Sum.inr 0)
    simp [inProblem, GeneralLinksInertia.inSys, LinearRESystem.Itil, LinearRESystem.Atil,
      LinearRESystem.Ihat, LinearRESystem.Ahat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have s3 : ν * (c.σ * u (Sum.inl (Sum.inr 0)) + u (Sum.inl (Sum.inr 1))) =
      u (Sum.inl (Sum.inr 1)) + c.σ * u (Sum.inr ()) := by
    have h := hsimpS (Sum.inr 1)
    simp [inProblem, GeneralLinksInertia.inSys, LinearRESystem.Itil, LinearRESystem.Atil,
      LinearRESystem.Ihat, LinearRESystem.Ahat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have hF : ∀ r, (ν • ((inProblem c 0 hc le_rfl).sys.Atilᵀ.map Complex.ofReal *ᵥ p) +
      (inProblem c 0 hc le_rfl).Tᵀ.map Complex.ofReal *ᵥ ((inProblem c 0 hc le_rfl).W.map
        Complex.ofReal *ᵥ ((inProblem c 0 hc le_rfl).T.map Complex.ofReal *ᵥ u)) -
      (((inProblem c 0 hc le_rfl).β⁻¹ : ℝ) : ℂ) •
        ((inProblem c 0 hc le_rfl).sys.Itilᵀ.map Complex.ofReal *ᵥ p)) r = 0 :=
    fun r => congrFun h2 r
  set uN : (Empty ⊕ Fin 2) ⊕ Unit → ℂ :=
    fun v => u (Sum.map (Sum.map (fun e => e.elim) id) id v) with huN
  set pN : Empty ⊕ Fin 2 → ℂ := fun v => p (Sum.map (fun e => e.elim) id v) with hpN
  refine ⟨uN, pN, ?_, funext fun r => ?_, funext fun r => ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨hu0, hp0⟩ := hcon
    have hu : ∀ v, uN v = 0 := fun v => congrFun hu0 v
    have hp : ∀ v, pN v = 0 := fun v => congrFun hp0 v
    have uπ : u (Sum.inl (Sum.inr 0)) = 0 := hu (Sum.inl (Sum.inr 0))
    have uZ : u (Sum.inl (Sum.inl ())) = 0 := by
      rw [uπ] at s1
      exact (mul_eq_zero.mp s1).resolve_left hν
    apply hne.elim
    · intro h
      apply h
      funext v
      rcases v with ((e | j) | e)
      · exact uZ
      · exact hu (Sum.inl (Sum.inr j))
      · exact hu (Sum.inr e)
    · intro h
      apply h
      funext v
      rcases v with e | j
      · exact f1
      · exact hp (Sum.inr j)
  · rcases r with e | j
    · exact e.elim
    · fin_cases j
      · simp [nkProblem, GeneralLinks.nkSys, LinearRESystem.Itil, LinearRESystem.Atil,
          LinearRESystem.Ihat, LinearRESystem.Ahat, LinearRESystem.Bvec, mulVec, dotProduct,
          Fintype.sum_sum_type, Fin.sum_univ_two, huN]
        linear_combination s2
      · simp [nkProblem, GeneralLinks.nkSys, LinearRESystem.Itil, LinearRESystem.Atil,
          LinearRESystem.Ihat, LinearRESystem.Ahat, LinearRESystem.Bvec, mulVec, dotProduct,
          Fintype.sum_sum_type, Fin.sum_univ_two, huN]
        linear_combination s3
  · rcases r with (e | j) | e
    · exact e.elim
    · fin_cases j
      · have h := hF (Sum.inl (Sum.inr 0))
        simp [inProblem, GeneralLinksInertia.inSys, GeneralLinksInertia.inTtil,
          LinearRESystem.Itil, LinearRESystem.Atil, LinearRESystem.Ihat, LinearRESystem.Ahat,
          LinearRESystem.Bvec, LQProblem.T, mulVec, dotProduct, Fintype.sum_sum_type,
          Fin.sum_univ_three, Matrix.mul_apply] at h
        simp [nkProblem, GeneralLinks.nkSys, GeneralLinks.nkTtil, LinearRESystem.Itil,
          LinearRESystem.Atil, LinearRESystem.Ihat, LinearRESystem.Ahat, LinearRESystem.Bvec,
          LQProblem.T, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three,
          Matrix.mul_apply, huN, hpN]
        linear_combination h - ν * f1
      · have h := hF (Sum.inl (Sum.inr 1))
        simp [inProblem, GeneralLinksInertia.inSys, GeneralLinksInertia.inTtil,
          LinearRESystem.Itil, LinearRESystem.Atil, LinearRESystem.Ihat, LinearRESystem.Ahat,
          LinearRESystem.Bvec, LQProblem.T, mulVec, dotProduct, Fintype.sum_sum_type,
          Fin.sum_univ_three, Matrix.mul_apply] at h
        simp [nkProblem, GeneralLinks.nkSys, GeneralLinks.nkTtil, LinearRESystem.Itil,
          LinearRESystem.Atil, LinearRESystem.Ihat, LinearRESystem.Ahat, LinearRESystem.Bvec,
          LQProblem.T, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three,
          Matrix.mul_apply, huN, hpN]
        linear_combination h
    · have h := hF (Sum.inr ())
      simp [inProblem, GeneralLinksInertia.inSys, GeneralLinksInertia.inTtil,
        LinearRESystem.Itil, LinearRESystem.Atil, LinearRESystem.Ihat, LinearRESystem.Ahat,
        LinearRESystem.Bvec, LQProblem.T, mulVec, dotProduct, Fintype.sum_sum_type,
        Fin.sum_univ_three, Matrix.mul_apply] at h
      simp [nkProblem, GeneralLinks.nkSys, GeneralLinks.nkTtil, LinearRESystem.Itil,
        LinearRESystem.Atil, LinearRESystem.Ihat, LinearRESystem.Ahat, LinearRESystem.Bvec,
        LQProblem.T, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three,
        Matrix.mul_apply, huN, hpN]
      linear_combination h

/-- **Woodford (2003), §3.2 at `γ = 0`: the Euler pencil of (1.1) + (1.9) has no root on the unit
circle**, by `eulerRoot0_nk` and the basic model's `OptimalRulesMeasureSpectrum.nk_noEulerRoot`. -/
theorem in0_noEulerRoot (hc : c.Adm) :
    ∀ ν : ℂ, ‖ν‖ = 1 → ¬ EulerRoot (inProblem c 0 hc le_rfl) ν := by
  intro ν hν hr
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hν
  exact OptimalRulesMeasureSpectrum.nk_noEulerRoot c hc ν hν (eulerRoot0_nk c hc hν0 hr)

/-- Woodford (2003), p. 541, for the inflation-inertia model at `γ = 0`: the forward map `H` built
from the perfect-foresight Assumption 8.1 is geometrically stable. -/
theorem in0_powDecay (hc : c.Adm) :
    PencilSplit.PowDecay (Hgen (in0_assumption81_perfectForesight c hc 0)) :=
  (OptimalRulesMeasureSpectrum.powDecay_Hgen_iff_noEulerRoot
    (in0_assumption81_perfectForesight c hc 0)).mpr (in0_noEulerRoot c hc)

/-- **Woodford (2003), Assumption 8.1, p. 541, for the inflation-inertia model at `γ = 0`, on
every filtered probability space**: for every bounded adapted disturbance and bounded initial
conditions (1.1) + (1.9) has an a.s. unique bounded solution with Mathlib's conditional
expectation. -/
theorem in0_m_assumption81MB (hc : c.Adm) {Ω : Type*} [MeasurableSpace Ω]
    (S : MeasExpectationSystem Ω) (t0 : ℕ) :
    MAssumption81MB S (inProblem c 0 hc le_rfl) t0 :=
  OptimalRulesMeasureSpectrum.m_assumption81MB_of_noEulerRoot
    (in0_assumption81_perfectForesight c hc 0) (in0_noEulerRoot c hc) S t0

/-- Woodford (2003), Assumption 8.5, App. G.2, p. 719, at `γ = 0` in the form used by the
measure-theoretic Proposition 8.2. -/
theorem in0_h85 (hc : c.Adm) : TargetCriterion.Krylov.Assumption85b
    (PencilSplit.Λmat (inProblem c 0 hc le_rfl).sys (inProblem c 0 hc le_rfl).β
      (in0Split c hc).J) (inProblem c 0 hc le_rfl).sys.B2 :=
  (in0_assumption85 c hc).2

/-- Woodford (2003), (1.22), p. 554, at `γ = 0`: the representation has degree at most
`rank Λ ≤ 2`, so every window `D ≥ 2` carries it. -/
theorem in0_degrees (hc : c.Adm) {D : ℕ} (hD2 : 2 ≤ D) :
    (∀ i j, (Adjugate.Bpoly (PencilSplit.Λmat (inProblem c 0 hc le_rfl).sys
      (inProblem c 0 hc le_rfl).β (in0Split c hc).J) i j).natDegree ≤ D) ∧
    (Adjugate.alpha (PencilSplit.Λmat (inProblem c 0 hc le_rfl).sys (inProblem c 0 hc le_rfl).β
      (in0Split c hc).J)).natDegree ≤ D := by
  have hrk : (PencilSplit.Λmat (inProblem c 0 hc le_rfl).sys (inProblem c 0 hc le_rfl).β
      (in0Split c hc).J).rank ≤ D :=
    (rank_le_width _).trans (by simpa using hD2)
  exact ⟨fun i j => (Adjugate.natDegree_Bpoly_le_rank _ i j).trans hrk,
    (Adjugate.natDegree_alpha_le_rank _).trans hrk⟩

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model at `γ = 0`, on
every filtered probability space and for every bounded adapted disturbance**: commitment to the
target criterion (1.23) built from `in0Split` (a window of `D ≥ 2` lags, any consistent bounded
history) determines a bounded feasible plan, unique a.s., and it solves (1.1) + (1.9). -/
theorem in0_m_prop82_general (hc : c.Adm) {Ω : Type*} [MeasurableSpace Ω]
    (S : MeasExpectationSystem Ω) (t0 : ℕ) {D : ℕ} (hD : D + 1 ≤ t0) (hD2 : 2 ≤ D)
    {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat (inProblem c 0 hc le_rfl).sys
      (inProblem c 0 hc le_rfl).β (in0Split c hc).J) (inProblem c 0 hc le_rfl).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {e : ℕ → Ω → Fin 2 → ℝ} (heb : MBoundedV S e)
    (hea : MAdaptedV S e) {Z0 : Ω → Unit → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S (inProblem c 0 hc le_rfl) e t0 Z0 y ∧
      MCriterion (inProblem c 0 hc le_rfl) (in0Split c hc) S D t0 qh vh y ∧
      (∀ y', MFeasible S (inProblem c 0 hc le_rfl) e t0 Z0 y' →
        MCriterion (inProblem c 0 hc le_rfl) (in0Split c hc) S D t0 qh vh y' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MFOCSystem S (inProblem c 0 hc le_rfl) e t0 Z0 (Mh (t0 - 1)) y φ :=
  m_prop82_general (in0_assumption81_perfectForesight c hc 0) S t0 (in0_powDecay c hc)
    (in0Split c hc) (in0_h85 c hc) hD (in0_degrees c hc hD2).1 (in0_degrees c hc hD2).2 hhist
    hMhb hMhk hqhb hvhb heb hea hZk hZb

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model at `γ = 0`, on
every VAR economy** (`A` power-bounded): the criterion (1.23) determines exactly one bounded
equilibrium a.s., and it is optimal from a timeless perspective. -/
theorem in0_m_prop82_var (hc : c.Adm) {Ω : Type*} [MeasurableSpace Ω] {ιs : Type*} [Fintype ιs]
    [DecidableEq ιs] (A : Matrix ιs ιs ℝ) (C2 : Matrix (Fin 2) ιs ℝ) (hA : PowBdd A)
    {S : MeasExpectationSystem Ω} {D t0 : ℕ} (hD : D + 1 ≤ t0) (hD2 : 2 ≤ D)
    {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat (inProblem c 0 hc le_rfl).sys
      (inProblem c 0 hc le_rfl).β (in0Split c hc).J) (inProblem c 0 hc le_rfl).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {Z0 : Ω → Unit → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S (inProblem c 0 hc le_rfl) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y ∧
      MCriterion (inProblem c 0 hc le_rfl) (in0Split c hc) S D t0 qh vh y ∧
      (∀ y', MFeasible S (inProblem c 0 hc le_rfl) (fun t ω => C2 *ᵥ s t ω) t0 Z0 y' →
        MCriterion (inProblem c 0 hc le_rfl) (in0Split c hc) S D t0 qh vh y' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MTimelesslyOptimalPlan S (inProblem c 0 hc le_rfl) (fun t ω => C2 *ᵥ s t ω) t0 Z0
        (stateX y φ s)
        (zpart (fY (inProblem c 0 hc le_rfl) A C2 (in0_assumption81_perfectForesight c hc 0) hA))
        ((FY (inProblem c 0 hc le_rfl) A C2 (in0_assumption81_perfectForesight c hc 0)
          hA).submatrix (Sum.inl ∘ Sum.inr) id) y := by
  have hpow : PencilSplit.PowDecay (Hn (inProblem c 0 hc le_rfl) A C2
      (in0_assumption81_perfectForesight c hc 0) hA) := by
    rw [OptimalRulesMeasureStability.Hn_eq_Hgen]
    exact in0_powDecay c hc
  exact OptimalRulesMeasureConverse.m_prop82_var (Dsp := in0Split c hc) A C2
    (in0_assumption81_perfectForesight c hc 0) hA hpow (in0_h85 c hc) hD
    (in0_degrees c hc hD2).1 (in0_degrees c hc hD2).2 hhist hMhb hMhk hqhb hvhb hs hZk hZb

end Woodford.OptimalPolicyRules.TidyR5aInertiaGammaZeroMeasure
