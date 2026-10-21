/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureGeneral
import OptimalPolicyRules.Prop81CaseII

/-!
# Proposition 8.2 with genuine conditional expectations from a quasi-split

Woodford (2003), *Interest and Prices*, Chapter 8, Propositions 8.1 and 8.2 (pp. 552–555,
(1.18)–(1.27)), Assumption 8.2 (ii) (p. 552) and Appendix G.1–G.2 (pp. 716–719), on a filtered
probability space with Mathlib's conditional expectation and an arbitrary bounded disturbance.

`OptimalRulesMeasureConverse` and `OptimalRulesMeasureGeneral` prove the measure-theoretic
Proposition 8.2 from a real **deflating split** (`PencilSplit.DeflatingSplit`). When a selected
root is complex and its conjugate is not selected (case (ii) of Assumption 8.2), no real
deflating split exists; the core replaces it by a **quasi-split** (`Prop81CaseII.QuasiSplit`): a
real deflating pair `A J⁺ = Î J⁺ Ψ⁺` with one extra column (the conjugate root added, a real
`2 × 2` block), a real `P` with `J = J⁺P`, and a residual map `H` on `ker P'` with `(βH)ᵏ → 0`.
Here the whole measure-theoretic theory is redone for a quasi-split.

## The construction

* `qMQ`, `MCriterionQ`: the operator `Q(L⁻¹)` of the quasi-split (`Prop81CaseII.QopII`) on the
  conditional forecast path, and the target criterion (1.23) a.s. with `Λ = β⁻¹K⁻¹Ẽ'`, `J = J⁺P`.
* Forward direction (`m_eq119_120Q`, `m_criterionQ`): the core case-(ii) Proposition 8.1
  (`Prop81CaseII.prop81II`) applied to the perfect-foresight forecast path of a solution.
* Converse (`m_focSystem_of_criterionQ`): with `R⁺_t = ∑_k (βΨ⁺')ᵏ βJ⁺'x_{t+k}` (realised),
  `F⁺_t = E_tR⁺_t`, `r_t = (J₁')⁻¹P'F⁺_t`, the multipliers `φcQ` built from (1.20)–(1.21) satisfy
  the `z`-rows of (1.18) by (1.20); the residual `D_t = J⁺'Î'φ_t − F⁺_t` lies in `ker P'`
  (`pD_zero`) and satisfies `D_t = βH E_t D_{t+1}` a.s.; bounded, it vanishes a.s.
  (`m_fwd_zero`, the measure-theoretic forward uniqueness), so the `ξ`-rows of (1.18) hold a.s.

## Main results

* `m_focSystem_of_criterionQ`, `m_criterionQ_iff`, `m_criterionQ_eq_foc`, `m_prop82_uniqueQ`.
* `m_prop82_generalQ`: **Proposition 8.2 from a quasi-split, every bounded adapted
  disturbance** (existence, a.s. uniqueness, the plan solves (1.1) + (1.9)).
* `m_prop82_varQ`: the VAR form, with optimality from a timeless perspective.
* **The real split is a special case**: `mCriterionQ_quasiOfDeflating_iff`
  (`Prop81CaseII.quasiOfDeflating` gives the same criterion), and `m_prop82_general_of_quasi`,
  `m_prop82_var_of_quasi` re-derive `OptimalRulesMeasureGeneral.m_prop82_general` and
  `OptimalRulesMeasureConverse.m_prop82_var` from the quasi-split theorems.
* Link with the core: `mCriterionQ_unit_iff` — on the one-point space `MCriterionQ` is the core
  `Prop82General.Prop82M.CriterionM` for `Prop81CaseII.prop81II … perfectForesight`.
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureQuasiSplit

open MeasureTheory Filter Topology Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure OptimalRulesMeasure OptimalRulesMeasureMarkov OptimalRulesMeasureForecast
open OptimalRulesMeasureConverse
open TargetCriterion.Prop81 TargetCriterion.Recursion

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]
variable {ιc : Type*} [Fintype ιc] [DecidableEq ιc]

/-! ### The criterion from a quasi-split -/

/-- Woodford (2003), eq. (1.25), p. 554, case (ii) of Assumption 8.2: `q_t = E_t Q(L⁻¹)x_t` for
the quasi-split `Q` — the core operator `Prop81CaseII.QopII` applied to the conditional forecast
path `k ↦ E_t T̃'W(τ_{t+k} − τ*)`. -/
noncomputable def qMQ (P : LQProblem ιZ ιz ιτ) (Q : Prop81CaseII.QuasiSplit P.sys P.β ιc)
    (S : MeasExpectationSystem Ω) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ) (ω : Ω) :
    ιz → ℝ :=
  Prop81CaseII.QopII perfectForesight Q (xproc P (fun k (_ : Unit) => EVm S t (y (t + k)) ω)) 0 ()

/-- Woodford (2003), eq. (1.23), p. 554, and fn 14, case (ii) of Assumption 8.2, with genuine
conditional expectations: commitment to the target criterion at all `t ≥ t₀`, a.s., with
`Λ = β⁻¹K⁻¹Ẽ'` for `J = J⁺P` of the quasi-split, `q_t = qMQ`, and the historical `q`, `v`
before `t₀`. -/
def MCriterionQ (P : LQProblem ιZ ιz ιτ) (Q : Prop81CaseII.QuasiSplit P.sys P.β ιc)
    (S : MeasExpectationSystem Ω) (D t0 : ℕ) (qh : ℕ → Ω → ιz → ℝ) (vh : ℕ → Ω → ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, TargetCriterion.Crit.crit
    (Adjugate.alpha (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)))
    (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))) D P.sys.B2
    (splice t0 vh (vproc P y)) (splice t0 qh (qMQ P Q S y)) t ω = 0

/-! ### The forward direction: the optimal plan satisfies the criterion -/

/-- Woodford (2003), **(1.20) and (1.19)**, p. 553, case (ii), with genuine conditional
expectations, for every disturbance: along every bounded solution of (1.1) + (1.9) whose initial
multiplier is a.e. known at `t₀`, a.s. for all `t ≥ t₀`, `M_t = Λ M_{t−1} + q_t` (`Λ` and
`q_t = qMQ` of the quasi-split) and `B₂'M_t + v_t = 0` (the core `Prop81CaseII.prop81II` on the
perfect-foresight forecast path, `OptimalRulesMeasureForecast.fc_focSystem`). -/
theorem m_eq119_120Q (P : LQProblem ιZ ιz ιτ) (Q : Prop81CaseII.QuasiSplit P.sys P.β ιc)
    {S : MeasExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ}
    {M0 : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P c t0 Z0 M0 y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => M0 ω r) S.μ) {t : ℕ} (ht : t0 ≤ t) :
    ∀ᵐ ω ∂S.μ, Mpart (φ (t + 1) ω) =
        PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P) *ᵥ Mpart (φ t ω) + qMQ P Q S y t ω ∧
      P.sys.B2 ⬝ᵥ Mpart (φ (t + 1) ω) + vproc P y t ω = 0 := by
  classical
  have hyi := integrable_of_adapted h.1.2.2.1 h.1.2.2.2
  have hMk : ∀ ω, Mpart (EVm S t (φ (t + 1)) ω) = Mpart (φ (t + 1) ω) :=
    mpart_EVm_of_le h.2.1 h.2.2.1 h.2.2.2.1 le_rfl
  have hy0 : EVm S t (y t) = y t := EVm_of_known S (h.1.2.2.2 t) (hyi t)
  filter_upwards [fc_focSystem P h ht,
    mpart_EVm_self h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 hM0 ht] with ω hω hMs
  obtain ⟨⟨-, -, hyb, -⟩, hφb, hmm, -, hfoc⟩ := hω
  have h118 : Eq118 P perfectForesight 0
      (fun k _ => EVm S t (y (t + k)) ω) (fun k _ => EVm S t (φ (t + k)) ω) := by
    intro k _ u
    have := hfoc k (Nat.zero_le k) u
    exact ((foc_iff_split P hmm (fun k _ => EVm S t (y (t + k)) ω) k u).mp this).1
  have h119 := ((foc_iff_split P hmm (fun k _ => EVm S t (y (t + k)) ω) 0 ()).mp
    (hfoc 0 le_rfl ())).2
  have heq := ((Prop81CaseII.prop81II P Q perfectForesight 0).equiv _ _ hyb (fun _ _ => rfl)
    hφb (fun _ _ _ => rfl)).mp h118
  have h120 := heq.1 0 le_rfl ()
  change Mpart (EVm S t (φ (t + 1)) ω) = PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P) *ᵥ
    Mpart (EVm S t (φ (t + 0)) ω) + qMQ P Q S y t ω at h120
  have hM' : Mpart (EVm S t (φ (t + 0)) ω) = Mpart (φ t ω) := hMs
  rw [hMk, hM'] at h120
  refine ⟨h120, ?_⟩
  change P.sys.B2 ⬝ᵥ Mpart (EVm S t (φ (t + 1)) ω) +
    P.Ti ⬝ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + 0)) ω - P.τstar)) = 0 at h119
  have hy0' : EVm S t (y (t + 0)) = y t := hy0
  rw [hMk, hy0'] at h119
  exact h119

/-- Woodford (2003), (1.20) and (1.19), case (ii), for the spliced processes (history before
`t₀`, the solution from `t₀` on), a.s. for all dates `s ≥ t₀ − D`, for every disturbance. -/
theorem m_spliced_119_120Q (P : LQProblem ιZ ιz ιτ) (Q : Prop81CaseII.QuasiSplit P.sys P.β ιc)
    {S : MeasExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ} {t0 D : ℕ} (ht0 : 1 ≤ t0)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) P.sys.B2 t0 D Mh qh vh)
    {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P c t0 Z0 (Mh (t0 - 1)) y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ) :
    ∀ᵐ ω ∂S.μ, ∀ u, t0 - D ≤ u →
      splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) u ω =
        PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P) *ᵥ
          splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) (u - 1) ω +
          splice t0 qh (qMQ P Q S y) u ω ∧
      P.sys.B2 ⬝ᵥ splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) u ω +
        splice t0 vh (vproc P y) u ω = 0 := by
  classical
  have hsol : ∀ u, ∀ᵐ ω ∂S.μ, t0 ≤ u → Mpart (φ (u + 1) ω) =
        PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P) *ᵥ Mpart (φ u ω) + qMQ P Q S y u ω ∧
      P.sys.B2 ⬝ᵥ Mpart (φ (u + 1) ω) + vproc P y u ω = 0 := by
    intro u
    by_cases hu : t0 ≤ u
    · filter_upwards [m_eq119_120Q P Q h hM0 hu] with ω e _
      exact e
    · exact Eventually.of_forall fun _ h' => absurd h' hu
  have hh1 : ∀ u, ∀ᵐ ω ∂S.μ, t0 - D ≤ u → u < t0 →
      Mh u ω = PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P) *ᵥ Mh (u - 1) ω + qh u ω := by
    intro u
    by_cases hu : t0 - D ≤ u ∧ u < t0
    · filter_upwards [hhist.1 u hu.1 hu.2] with ω e _ _
      exact e
    · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hu
  have hh2 : ∀ u, ∀ᵐ ω ∂S.μ, t0 - D ≤ u → u < t0 → P.sys.B2 ⬝ᵥ Mh u ω + vh u ω = 0 := by
    intro u
    by_cases hu : t0 - D ≤ u ∧ u < t0
    · filter_upwards [hhist.2 u hu.1 hu.2] with ω e _ _
      exact e
    · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hu
  filter_upwards [ae_all_iff.2 hsol, ae_all_iff.2 hh1, ae_all_iff.2 hh2, h.2.2.2.2.1]
    with ω e1 e2 e3 e4 u hu
  unfold splice
  by_cases hlt : u < t0
  · simp only [hlt, ↓reduceIte, show u - 1 < t0 by omega]
    exact ⟨e2 u hu hlt, e3 u hu hlt⟩
  · push Not at hlt
    simp only [show ¬ u < t0 by omega, ↓reduceIte]
    refine ⟨?_, (e1 u hlt).2⟩
    rw [(e1 u hlt).1]
    by_cases hu0 : u = t0
    · simp only [show u - 1 < t0 by omega, ↓reduceIte]
      rw [hu0, e4]
    · simp only [show ¬ u - 1 < t0 by omega, ↓reduceIte, show u - 1 + 1 = u by omega]

/-- Woodford (2003), **(1.23)**, p. 554, case (ii), with genuine conditional expectations, for
every disturbance: along every bounded solution of (1.1) + (1.9) whose initial multiplier comes
from a consistent history, the target criterion of the quasi-split holds a.s. at every
`t ≥ t₀`. -/
theorem m_criterionQ (P : LQProblem ιZ ιz ιτ) (Q : Prop81CaseII.QuasiSplit P.sys P.β ιc)
    {S : MeasExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ} {t0 D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) P.sys.B2 t0 D Mh qh vh)
    {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P c t0 Z0 (Mh (t0 - 1)) y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ) :
    MCriterionQ P Q S D t0 qh vh y := by
  classical
  intro t ht
  filter_upwards [m_spliced_119_120Q P Q (by omega) hhist h hM0] with ω e
  exact TargetCriterion.Crit.eq123_of_eq119_eq120 (Adjugate.eq122 _) hB hα P.sys.B2
    (M := fun u (_ : Unit) => splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) u ω)
    (q := fun u (_ : Unit) => splice t0 qh (qMQ P Q S y) u ω)
    (v := fun u (_ : Unit) => splice t0 vh (vproc P y) u ω)
    (t0 := t0 - D) (fun u hu _ => (e u hu).2) (fun u hu _ => (e u hu).1) t (by omega) ()

/-! ### Forward uniqueness with conditional expectations -/

omit [MeasurableSpace Ω] in
/-- Woodford (2003), App. G.1, p. 717 (tool): if the powers of `G` decay geometrically, the
bound `card ι · C rᵏ⁺¹ K` on `|(Gᵏ⁺¹ v)_i|` tends to zero. -/
theorem pow_bound_tendsto {ι : Type*} [Fintype ι] {C r K : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun k : ℕ => (Fintype.card ι : ℝ) * (C * r ^ (k + 1) * K)) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp (tendsto_add_atTop_nat 1)
  have h2 := ((h.const_mul C).mul_const K).const_mul (Fintype.card ι : ℝ)
  rw [mul_zero, zero_mul, mul_zero] at h2
  exact h2

/-- Woodford (2003), App. G.1, p. 717 (the forward-uniqueness step of Proposition 8.1, case (ii),
with genuine conditional expectations): if the powers of `G` decay geometrically, an essentially
bounded process with `D_t = G E_t D_{t+1}` a.s. for all `t ≥ t₀` vanishes a.s. at
every `t ≥ t₀` (`D_t = Gᵏ⁺¹ E_t D_{t+k+1}` by the law of iterated expectations). -/
theorem m_fwd_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {S : MeasExpectationSystem Ω}
    {G : Matrix ι ι ℝ} (hG : PencilSplit.PowDecay G) {D : ℕ → Ω → ι → ℝ} {t0 : ℕ}
    (hb : MBoundedV S D)
    (hrec : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, D t ω = G *ᵥ EVm S t (D (t + 1)) ω) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, D t ω = 0 := by
  intro t ht
  have hit : ∀ k, ∀ᵐ ω ∂S.μ, D t ω = G ^ (k + 1) *ᵥ EVm S t (D (t + k + 1)) ω := by
    intro k
    induction k with
    | zero =>
      filter_upwards [hrec t ht] with ω e
      rw [e, zero_add, pow_one]
    | succ k ih =>
      have hE : ∀ᵐ ω ∂S.μ, EVm S t (D (t + k + 1)) ω = G *ᵥ EVm S t (D (t + k + 1 + 1)) ω := by
        have h1 := hrec (t + k + 1) (by omega)
        have hEi : ∀ i, Integrable (fun ω => EVm S (t + k + 1) (D (t + k + 1 + 1)) ω i) S.μ :=
          fun i => S.integrable_E _ _
        filter_upwards [EVm_congr S t h1, EVm_mulVec S t G hEi,
          EVm_tower S (show t ≤ t + k + 1 by omega) (D (t + k + 1 + 1))] with ω e1 e2 e3
        rw [e1, e2, e3]
      filter_upwards [ih, hE] with ω e1 e2
      rw [show t + (k + 1) + 1 = t + k + 1 + 1 by omega, e1, e2, mulVec_mulVec, ← pow_succ]
  obtain ⟨K, hK⟩ := hb
  obtain ⟨C, r, hr0, hr1, hC⟩ := hG
  have hEb : ∀ k, ∀ᵐ ω ∂S.μ, ∀ i, |EVm S t (D (t + k + 1)) ω i| ≤ K := fun k =>
    ae_all_iff.2 fun i => S.abs_E_le ((hK (t + k + 1)).mono fun ω h => h i) t
  filter_upwards [ae_all_iff.2 hit, ae_all_iff.2 hEb] with ω e1 e2
  funext i
  have hle : ∀ k, |D t ω i| ≤ (Fintype.card ι : ℝ) * (C * r ^ (k + 1) * K) := fun k => by
    rw [e1 k]
    exact PencilSplit.abs_mulVec_pow_le hC (k + 1) (e2 k) i
  have h0 : |D t ω i| ≤ 0 := ge_of_tendsto' (pow_bound_tendsto hr0 hr1) hle
  exact abs_nonpos_iff.mp h0

/-! ### The operators of the quasi-split with conditional expectations -/

variable (P : LQProblem ιZ ιz ιτ) (Q : Prop81CaseII.QuasiSplit P.sys P.β ιc)

/-- Woodford (2003), App. G.1, case (ii): the realised forward sum
`R⁺_t = ∑_{k ≥ 0} (βΨ⁺')ᵏ βJ⁺' T̃'W(τ_{t+k} − τ*)` along a plan. -/
noncomputable def RsumQ (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ) (ω : Ω) : ιc → ℝ :=
  fun i => ∑' k, ((P.β • Q.Ψpᵀ) ^ k *ᵥ ((P.β • Q.Jpᵀ) *ᵥ xproc P y (t + k) ω)) i

/-- Woodford (2003), App. G.1, case (ii): `F⁺_t = E_t R⁺_t`, the forward solution of
`w⁺_t = βΨ⁺' E_t w⁺_{t+1} + βJ⁺' x_t` with genuine conditional expectations. -/
noncomputable def FmQ (S : MeasExpectationSystem Ω) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ) :
    Ω → ιc → ℝ :=
  EVm S t (RsumQ P Q y t)

/-- Woodford (2003), eq. (1.21), p. 553, case (ii): `r_t = (J₁')⁻¹ P' F⁺_t` with `J = J⁺P`. -/
noncomputable def rmQ (S : MeasExpectationSystem Ω) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ)
    (ω : Ω) : ιZ → ℝ :=
  ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ FmQ P Q S y t ω)

/-- Woodford (2003), eqs. (1.20) and (1.25), p. 553, case (ii):
`q_t = −K⁻¹(x^z_t + A₁₂' E_t r_{t+1})` with `K` for `J = J⁺P`. -/
noncomputable def qmQ (S : MeasExpectationSystem Ω) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ)
    (ω : Ω) : ιz → ℝ :=
  -((PencilSplit.Kmat P.sys (Q.Jp * Q.P))⁻¹ *ᵥ
    (Mpart (xproc P y t ω) + P.sys.A12ᵀ *ᵥ EVm S t (rmQ P Q S y (t + 1)) ω))

variable {P Q}

/-- Woodford (2003), App. G.1, case (ii) (the forward sum): along an essentially bounded plan,
a.s. at every date the series `R⁺_t` converges absolutely, is bounded by a constant, and satisfies
`R⁺_t = βJ⁺'x_t + βΨ⁺' R⁺_{t+1}`. -/
theorem rsumQ_spec {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) :
    ∃ KR, ∀ᵐ ω ∂S.μ, ∀ t, (∀ i, HasSum (fun k => ((P.β • Q.Ψpᵀ) ^ k *ᵥ
        ((P.β • Q.Jpᵀ) *ᵥ xproc P y (t + k) ω)) i) (RsumQ P Q y t ω i)) ∧
      (∀ i, |RsumQ P Q y t ω i| ≤ KR) ∧
      RsumQ P Q y t ω = (P.β • Q.Jpᵀ) *ᵥ xproc P y t ω +
        (P.β • Q.Ψpᵀ) *ᵥ RsumQ P Q y (t + 1) ω := by
  obtain ⟨Ky, hKy⟩ := hyb
  obtain ⟨KX, hKX⟩ := xv_bound P Ky
  obtain ⟨Mw, hMw⟩ := exists_bound_mulVec (P.β • Q.Jpᵀ) KX
  obtain ⟨K, hK⟩ := geom_vec (Q.powDecay_Gp P.β_pos) Mw
  refine ⟨K, ?_⟩
  filter_upwards [ae_all_iff.2 hKy] with ω hω t
  have hw : ∀ s, ∀ k j, |((P.β • Q.Jpᵀ) *ᵥ xproc P y (s + k) ω) j| ≤ Mw := fun s k j =>
    hMw _ (fun j' => hKX _ (hω (s + k)) j') j
  have h0 := fun i => hK _ (hw t) i
  have h1 := fun i => hK _ (hw (t + 1)) i
  refine ⟨fun i => (h0 i).1.hasSum, fun i => (h0 i).2, ?_⟩
  have hs1 : ∀ i, Summable (fun k => ((P.β • Q.Ψpᵀ) ^ k *ᵥ
      ((P.β • Q.Jpᵀ) *ᵥ xproc P y (t + (k + 1)) ω)) i) := by
    intro i
    refine (h1 i).1.congr fun k => ?_
    rw [show t + (k + 1) = t + 1 + k by omega]
  have := geom_shift (P.β • Q.Ψpᵀ) (fun k => (P.β • Q.Jpᵀ) *ᵥ xproc P y (t + k) ω)
    (fun i => (h0 i).1) hs1
  have e1 : RsumQ P Q y t ω = fun i => ∑' k, ((P.β • Q.Ψpᵀ) ^ k *ᵥ
      ((fun k => (P.β • Q.Jpᵀ) *ᵥ xproc P y (t + k) ω) k)) i := rfl
  rw [e1, this]
  refine congrArg₂ (· + ·) rfl (congrArg _ (funext fun i => tsum_congr fun k => ?_))
  show ((P.β • Q.Ψpᵀ) ^ k *ᵥ ((P.β • Q.Jpᵀ) *ᵥ xproc P y (t + (k + 1)) ω)) i =
    ((P.β • Q.Ψpᵀ) ^ k *ᵥ ((P.β • Q.Jpᵀ) *ᵥ xproc P y (t + 1 + k) ω)) i
  rw [show t + (k + 1) = t + 1 + k by omega]

/-- Woodford (2003), App. G.1, case (ii) (tool): the realised forward sum is a.e. strongly
measurable (the a.e. limit of its partial sums) and integrable. -/
theorem rsumQ_integrable {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) (hya : MAdaptedV S y) (t : ℕ) (i : ιc) :
    Integrable (fun ω => RsumQ P Q y t ω i) S.μ := by
  obtain ⟨KR, hKR⟩ := rsumQ_spec (P := P) (Q := Q) hyb
  have hterm : ∀ k, AEStronglyMeasurable (fun ω => ((P.β • Q.Ψpᵀ) ^ k *ᵥ
      ((P.β • Q.Jpᵀ) *ᵥ xproc P y (t + k) ω)) i) S.μ := fun k =>
    aesm_comp (fun j => (((xproc_int_known (P := P) hyb hya (t + k)).2 j).mono
      (S.𝓕.le _)).aestronglyMeasurable)
      (g := fun v => ((P.β • Q.Ψpᵀ) ^ k *ᵥ ((P.β • Q.Jpᵀ) *ᵥ v)) i) (by fun_prop)
  have hm : AEStronglyMeasurable (fun ω => RsumQ P Q y t ω i) S.μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N ω => ∑ k ∈ Finset.range N, ((P.β • Q.Ψpᵀ) ^ k *ᵥ
        ((P.β • Q.Jpᵀ) *ᵥ xproc P y (t + k) ω)) i)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ => hterm k) ?_
    filter_upwards [hKR] with ω h
    exact ((h t).1 i).tendsto_sum_nat
  exact integrable_of_bound hm (hKR.mono fun ω h => (h t).2.1 i)

/-- Woodford (2003), App. G.1, (G.5), case (ii), with genuine conditional expectations: the
forward recursion `F⁺_t = βJ⁺'x_t + βΨ⁺' E_t F⁺_{t+1}` a.s. (law of iterated expectations). -/
theorem FmQ_rec {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) (hya : MAdaptedV S y) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, FmQ P Q S y t ω = (P.β • Q.Jpᵀ) *ᵥ xproc P y t ω +
      (P.β • Q.Ψpᵀ) *ᵥ EVm S t (FmQ P Q S y (t + 1)) ω := by
  obtain ⟨KR, hKR⟩ := rsumQ_spec (P := P) (Q := Q) hyb
  obtain ⟨hxi, hxk⟩ := xproc_int_known (P := P) hyb hya t
  have hRi := rsumQ_integrable (P := P) (Q := Q) hyb hya (t + 1)
  have hrec : ∀ᵐ ω ∂S.μ, RsumQ P Q y t ω = (P.β • Q.Jpᵀ) *ᵥ xproc P y t ω +
      (P.β • Q.Ψpᵀ) *ᵥ RsumQ P Q y (t + 1) ω + (0 : Matrix ιc ιc ℝ) *ᵥ RsumQ P Q y t ω +
        0 := by
    filter_upwards [hKR] with ω h
    rw [zero_mulVec, add_zero, add_zero]
    exact (h t).2.2
  filter_upwards [EVm_congr S t hrec, EVm_affine3 S t (P.β • Q.Jpᵀ) (P.β • Q.Ψpᵀ)
    (0 : Matrix ιc ιc ℝ) 0 hxi hRi (rsumQ_integrable (P := P) (Q := Q) hyb hya t),
    EVm_tower S (Nat.le_succ t) (RsumQ P Q y (t + 1))] with ω e1 e2 e3
  unfold FmQ
  rw [e1, e2, zero_mulVec, add_zero, add_zero, EVm_of_known S hxk hxi, e3]

/-- Woodford (2003), (1.21), case (ii) (tool): `F⁺_t` and `r_t` are essentially bounded,
uniformly in `t`. -/
theorem FmQ_bdd {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) :
    ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, (∀ i, |FmQ P Q S y t ω i| ≤ K) ∧ ∀ i, |rmQ P Q S y t ω i| ≤ K := by
  obtain ⟨KR, hKR⟩ := rsumQ_spec (P := P) (Q := Q) hyb
  obtain ⟨K1, hK1⟩ := exists_bound_mulVec Q.Pᵀ KR
  obtain ⟨Kr, hKr⟩ := exists_bound_mulVec ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ K1
  refine ⟨max KR Kr, fun t => ?_⟩
  have hF : ∀ᵐ ω ∂S.μ, ∀ i, |FmQ P Q S y t ω i| ≤ KR :=
    ae_all_iff.2 fun i => S.abs_E_le (hKR.mono fun ω h => (h t).2.1 i) t
  filter_upwards [hF] with ω h
  exact ⟨fun i => (h i).trans (le_max_left _ _),
    fun i => (hKr _ (hK1 _ h) i).trans (le_max_right _ _)⟩

/-- Woodford (2003), p. 553, case (ii): `F⁺_t` and `r_t` are known at `t`. -/
theorem rmQ_known (S : MeasExpectationSystem Ω) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ) :
    MKnownV S t (FmQ P Q S y t) ∧ MKnownV S t (rmQ P Q S y t) := by
  have hF : MKnownV S t (FmQ P Q S y t) := fun i => S.stronglyMeasurable_E t _
  exact ⟨hF, fun i => sm_comp hF
    (g := fun v => (((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ v)) i) (by fun_prop)⟩

/-- Woodford (2003), eq. (1.25), p. 554, case (ii): `q_t` is known at `t` and essentially
bounded. -/
theorem qmQ_known_bdd {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) (hya : MAdaptedV S y) :
    (∀ t, MKnownV S t (qmQ P Q S y t)) ∧
      ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ∀ r, |qmQ P Q S y t ω r| ≤ K := by
  refine ⟨fun t r => ?_, ?_⟩
  · have h1 := (xproc_int_known (P := P) hyb hya t).2
    have h2 : MKnownV S t (EVm S t (rmQ P Q S y (t + 1))) := fun i =>
      S.stronglyMeasurable_E t _
    exact sm_comp₂ h1 h2 (g := fun p => (-((PencilSplit.Kmat P.sys (Q.Jp * Q.P))⁻¹ *ᵥ
      (Mpart p.1 + P.sys.A12ᵀ *ᵥ p.2))) r) (by unfold Mpart; fun_prop)
  · obtain ⟨Ky, hKy⟩ := hyb
    obtain ⟨KX, hKX⟩ := xv_bound P Ky
    obtain ⟨KF, hKF⟩ := FmQ_bdd (P := P) (Q := Q) ⟨Ky, hKy⟩
    obtain ⟨K1, hK1⟩ := exists_bound_mulVec P.sys.A12ᵀ KF
    obtain ⟨K2, hK2⟩ := exists_bound_mulVec (PencilSplit.Kmat P.sys (Q.Jp * Q.P))⁻¹ (KX + K1)
    refine ⟨K2, fun t => ?_⟩
    have hE : ∀ᵐ ω ∂S.μ, ∀ i, |EVm S t (rmQ P Q S y (t + 1)) ω i| ≤ KF :=
      ae_all_iff.2 fun i => S.abs_E_le ((hKF (t + 1)).mono fun ω h => h.2 i) t
    filter_upwards [hKy t, hE] with ω h1 h2 r
    change |(-((PencilSplit.Kmat P.sys (Q.Jp * Q.P))⁻¹ *ᵥ _)) r| ≤ K2
    rw [Pi.neg_apply, abs_neg]
    refine hK2 _ (fun j => ?_) r
    exact (abs_add_le _ _).trans (add_le_add (hKX _ h1 (Sum.inr j)) (hK1 _ h2 j))

/-- Woodford (2003), eq. (1.25), p. 554, case (ii): the forecast-based `q_t` of `qMQ` written
out — `−K⁻¹(x̂^z_0 + A₁₂'(J₁')⁻¹P' ∑_k (βΨ⁺')ᵏ βJ⁺' x̂_{1+k})` for the conditional forecast path
`x̂_k = T̃'W(T E_t y_{t+k} − τ*)`. -/
theorem qMQ_eq (S : MeasExpectationSystem Ω) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ)
    (ω : Ω) : qMQ P Q S y t ω = -((PencilSplit.Kmat P.sys (Q.Jp * Q.P))⁻¹ *ᵥ
      (Mpart (xproc P (fun k (_ : Unit) => EVm S t (y (t + k)) ω) 0 ()) + P.sys.A12ᵀ *ᵥ
        (((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ fun i => ∑' k, ((P.β • Q.Ψpᵀ) ^ k *ᵥ
          ((P.β • Q.Jpᵀ) *ᵥ xproc P (fun k (_ : Unit) => EVm S t (y (t + k)) ω)
            (0 + 1 + k) ())) i)))) := rfl

/-- Woodford (2003), eq. (1.25), p. 554, case (ii) (link): the operator `q_t` built with
conditional expectations equals a.s. the forecast-based `qMQ` used in the criterion; `E_t` is
passed through the forward series (`ExpectationsMeasure.MeasExpectationSystem.E_hasSum`). -/
theorem qmQ_eq_qMQ {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) (hya : MAdaptedV S y) (t : ℕ) :
    qmQ P Q S y t =ᵐ[S.μ] qMQ P Q S y t := by
  have hyi := integrable_of_adapted hyb hya
  set G := P.β • Q.Ψpᵀ with hG
  set BJ := P.β • Q.Jpᵀ with hBJ
  obtain ⟨Ky, hKy⟩ := hyb
  obtain ⟨KX, hKX⟩ := xv_bound P Ky
  obtain ⟨Mw, hMw⟩ := exists_bound_mulVec BJ KX
  obtain ⟨g, hgs, hg⟩ := geom_bound (Q.powDecay_Gp P.β_pos) Mw
  have hser : ∀ i, ∀ᵐ ω ∂S.μ, EVm S t (RsumQ P Q y (t + 1)) ω i =
      ∑' k, (G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + 1 + k)) ω -
        P.τstar))))) i := by
    intro i
    set a : ℕ → Ω → ℝ := fun k ω => (G ^ k *ᵥ (BJ *ᵥ xproc P y (t + 1 + k) ω)) i with ha
    have ham : ∀ k, AEStronglyMeasurable (a k) S.μ := fun k =>
      aesm_comp (fun j => ((hya (t + 1 + k) j).mono (S.𝓕.le _)).aestronglyMeasurable)
        (g := fun v => (G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar))))) i)
        (by fun_prop)
    have hab : ∀ k, ∀ᵐ ω ∂S.μ, |a k ω| ≤ g k := fun k => by
      filter_upwards [hKy (t + 1 + k)] with ω h
      exact hg k _ (fun j => hMw _ (fun j' => hKX _ h j') j) i
    have hEk : ∀ k, ∀ᵐ ω ∂S.μ, S.E t (a k) ω = (G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ
        (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + 1 + k)) ω - P.τstar))))) i := by
      intro k
      set B := G ^ k * BJ * (P.Ttilᵀ * P.W * P.T) with hB
      set b := G ^ k *ᵥ (BJ *ᵥ -(P.Ttilᵀ *ᵥ (P.W *ᵥ P.τstar))) with hb
      have haff : ∀ v : (ιZ ⊕ ιz) ⊕ Unit → ℝ, G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ
          (P.W *ᵥ (P.T *ᵥ v - P.τstar)))) = B *ᵥ v + (0 : Matrix ιc ((ιZ ⊕ ιz) ⊕ Unit) ℝ) *ᵥ v +
            (0 : Matrix ιc ((ιZ ⊕ ιz) ⊕ Unit) ℝ) *ᵥ v + b := by
        intro v
        rw [xv_affine, zero_mulVec, add_zero, add_zero, mulVec_add, mulVec_add, hB, hb]
        simp only [mulVec_mulVec, Matrix.mul_assoc]
      have hfun : a k = fun ω => (B *ᵥ y (t + 1 + k) ω +
          (0 : Matrix ιc ((ιZ ⊕ ιz) ⊕ Unit) ℝ) *ᵥ y (t + 1 + k) ω +
          (0 : Matrix ιc ((ιZ ⊕ ιz) ⊕ Unit) ℝ) *ᵥ y (t + 1 + k) ω + b) i := by
        funext ω
        simp only [ha]
        rw [← haff]
        rfl
      filter_upwards [EVm_affine3 S t B 0 0 b (hyi (t + 1 + k)) (hyi (t + 1 + k))
        (hyi (t + 1 + k))] with ω e
      have := congrFun e i
      simp only [EVm] at this
      rw [hfun, this, haff]
    filter_upwards [S.E_hasSum hgs ham hab t, ae_all_iff.2 hEk] with ω h1 h2
    change S.E t (fun ω' => RsumQ P Q y (t + 1) ω' i) ω = _
    have hR : (fun ω' => RsumQ P Q y (t + 1) ω' i) = fun ω' => ∑' k, a k ω' := rfl
    rw [hR, ← h1.tsum_eq]
    exact tsum_congr h2
  have hFi : ∀ i, Integrable (fun ω => FmQ P Q S y (t + 1) ω i) S.μ := fun i =>
    S.integrable_E _ _
  filter_upwards [EVm_mulVec S t (((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ * Q.Pᵀ) hFi,
    EVm_tower S (Nat.le_succ t) (RsumQ P Q y (t + 1)), ae_all_iff.2 hser] with ω e1 e2 e3
  have hy0 : EVm S t (y (t + 0)) ω = y t ω := by
    rw [Nat.add_zero, EVm_of_known S (hya t) (hyi t)]
  have hv : EVm S t (FmQ P Q S y (t + 1)) ω = fun i => ∑' k, (G ^ k *ᵥ (BJ *ᵥ
      (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + 1 + k)) ω - P.τstar))))) i := by
    funext i
    rw [← e3 i]
    exact congrFun e2 i
  have hrm : EVm S t (rmQ P Q S y (t + 1)) ω = ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ
      (Q.Pᵀ *ᵥ fun i => ∑' k, (G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ
        (P.T *ᵥ EVm S t (y (t + 1 + k)) ω - P.τstar))))) i) := by
    have : EVm S t (rmQ P Q S y (t + 1)) ω = EVm S t
        (fun ω => (((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ * Q.Pᵀ) *ᵥ FmQ P Q S y (t + 1) ω) ω := by
      unfold rmQ
      simp only [mulVec_mulVec]
    rw [this, e1, ← mulVec_mulVec, hv]
  have h1 : xproc P (fun k (_ : Unit) => EVm S t (y (t + k)) ω) 0 () = xproc P y t ω := by
    change P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + 0)) ω - P.τstar)) = _
    rw [hy0]
    rfl
  have h2 : (fun i => ∑' k, (G ^ k *ᵥ (BJ *ᵥ
      xproc P (fun k (_ : Unit) => EVm S t (y (t + k)) ω) (0 + 1 + k) ())) i) =
      fun i => ∑' k, (G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + 1 + k)) ω -
        P.τstar))))) i := by
    funext i
    refine tsum_congr fun k => ?_
    change (G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + (0 + 1 + k))) ω -
      P.τstar))))) i = _
    rw [show t + (0 + 1 + k) = t + 1 + k by omega]
  rw [qMQ_eq, h1, h2]
  unfold qmQ
  rw [hrm]

/-! ### The converse: the criterion implies (1.1) + (1.9) -/

/-- Woodford (2003), (1.18), p. 552, case (ii) (pointwise algebra): with
`e = (ΥM + (J₁')⁻¹P'F', M)` (the forecast of `φ_{t+1}`), `φ₀ = (ΥM₋ + (J₁')⁻¹P'F, M₋)`,
`M = ΛM₋ − K⁻¹(x^z + A₁₂'(J₁')⁻¹P'F')` (1.20) and `F = βJ⁺'x + βΨ⁺'F'`, the `z`-rows of the
left side `L` of (1.18) vanish and `J⁺₁'` times its `ξ`-rows is
`Ψ⁺'(J⁺'Î'e − F') − β⁻¹(J⁺'Î'φ₀ − F)` (the residual equation). -/
theorem eq118Q_pt {Mm M : ιz → ℝ} {F Fn : ιc → ℝ} {v : (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hM : M = PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P) *ᵥ Mm +
      -((PencilSplit.Kmat P.sys (Q.Jp * Q.P))⁻¹ *ᵥ
        (Mpart (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar))) +
          P.sys.A12ᵀ *ᵥ (((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ Fn)))))
    (hF : F = (P.β • Q.Jpᵀ) *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar))) +
      (P.β • Q.Ψpᵀ) *ᵥ Fn) :
    Mpart (P.sys.Ahatᵀ *ᵥ Sum.elim (PencilSplit.Υmat P.sys (Q.Jp * Q.P) *ᵥ M +
          ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ Fn)) M +
        P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) -
        P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ Sum.elim (PencilSplit.Υmat P.sys (Q.Jp * Q.P) *ᵥ Mm +
          ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ F)) Mm)) = 0 ∧
    (PencilSplit.J1 Q.Jp)ᵀ *ᵥ ξpart (P.sys.Ahatᵀ *ᵥ Sum.elim
          (PencilSplit.Υmat P.sys (Q.Jp * Q.P) *ᵥ M +
            ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ Fn)) M +
        P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) -
        P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ Sum.elim (PencilSplit.Υmat P.sys (Q.Jp * Q.P) *ᵥ Mm +
          ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ F)) Mm)) =
      Q.Ψpᵀ *ᵥ ((Q.Jpᵀ * P.sys.Ihatᵀ) *ᵥ Sum.elim (PencilSplit.Υmat P.sys (Q.Jp * Q.P) *ᵥ M +
          ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ Fn)) M - Fn) -
        P.β⁻¹ • ((Q.Jpᵀ * P.sys.Ihatᵀ) *ᵥ Sum.elim (PencilSplit.Υmat P.sys (Q.Jp * Q.P) *ᵥ Mm +
          ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ F)) Mm - F) := by
  set x := P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) with hx
  set Υ := PencilSplit.Υmat P.sys (Q.Jp * Q.P) with hΥ
  set Ji := ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ with hJi
  set pp : ιZ ⊕ ιz → ℝ := Sum.elim (Υ *ᵥ M + Ji *ᵥ (Q.Pᵀ *ᵥ Fn)) M with hpp
  set qq : ιZ ⊕ ιz → ℝ := Sum.elim (Υ *ᵥ Mm + Ji *ᵥ (Q.Pᵀ *ᵥ F)) Mm with hqq
  set L := P.sys.Ahatᵀ *ᵥ pp + x - P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ qq) with hL
  have hβ : P.β ≠ 0 := P.β_pos.ne'
  -- the `z`-rows vanish
  have hz : Mpart L = 0 := by
    have h120 := (Prop81General.eq120_iff P.sys P.β Q.K_det M Mm (Mpart x)
      (Ji *ᵥ (Q.Pᵀ *ᵥ Fn))).mp hM
    have hML : Mpart L = PencilSplit.Kmat P.sys (Q.Jp * Q.P) *ᵥ M +
        P.sys.A12ᵀ *ᵥ (Ji *ᵥ (Q.Pᵀ *ᵥ Fn)) + Mpart x - P.β⁻¹ • (P.sys.Etᵀ *ᵥ Mm) := by
      have e1 : Mpart (P.sys.Ahatᵀ *ᵥ pp) = P.sys.A12ᵀ *ᵥ (Υ *ᵥ M + Ji *ᵥ (Q.Pᵀ *ᵥ Fn)) +
          P.sys.A22ᵀ *ᵥ M := by
        rw [PencilSplit.Ahat_transpose_mulVec]
        rfl
      have e2 : Mpart (P.sys.Ihatᵀ *ᵥ qq) = P.sys.Etᵀ *ᵥ Mm := by
        rw [PencilSplit.Ihat_transpose_mulVec]
        rfl
      have e3 : Mpart L = Mpart (P.sys.Ahatᵀ *ᵥ pp) + Mpart x -
          P.β⁻¹ • Mpart (P.sys.Ihatᵀ *ᵥ qq) := rfl
      rw [e3, e1, e2, PencilSplit.Kmat, add_mulVec, mulVec_add, ← mulVec_mulVec]
      abel
    rw [hML]
    exact h120
  refine ⟨hz, ?_⟩
  have ht : Q.Jpᵀ * P.sys.Ahatᵀ = Q.Ψpᵀ * (Q.Jpᵀ * P.sys.Ihatᵀ) := by
    rw [← transpose_mul, Q.deflate, transpose_mul, transpose_mul]
  have hJL : Q.Jpᵀ *ᵥ L = Q.Ψpᵀ *ᵥ ((Q.Jpᵀ * P.sys.Ihatᵀ) *ᵥ pp) + Q.Jpᵀ *ᵥ x -
      P.β⁻¹ • ((Q.Jpᵀ * P.sys.Ihatᵀ) *ᵥ qq) := by
    have e1 : Q.Jpᵀ *ᵥ (P.sys.Ahatᵀ *ᵥ pp) = Q.Ψpᵀ *ᵥ ((Q.Jpᵀ * P.sys.Ihatᵀ) *ᵥ pp) := by
      rw [mulVec_mulVec, ht, ← mulVec_mulVec]
    have e2 : Q.Jpᵀ *ᵥ (P.sys.Ihatᵀ *ᵥ qq) = (Q.Jpᵀ * P.sys.Ihatᵀ) *ᵥ qq := mulVec_mulVec _ _ _
    rw [hL, mulVec_sub, mulVec_add, mulVec_smul, e1, e2]
  have hsplit := PencilSplit.J_transpose_mulVec Q.Jp L
  have hz' : L ∘ Sum.inr = 0 := hz
  rw [hz', mulVec_zero, add_zero] at hsplit
  change (PencilSplit.J1 Q.Jp)ᵀ *ᵥ (L ∘ Sum.inl) = _
  rw [← hsplit, hJL, hF]
  simp only [smul_mulVec, smul_add, smul_smul, inv_mul_cancel₀ hβ, one_smul, mulVec_sub,
    smul_sub]
  abel

variable (P Q)

/-- Woodford (2003), p. 555, case (ii): the multipliers `M_t` implied by a plan under the
criterion: the history `M_s = Mh_s` before `t₀`, then (1.20) `M_t = ΛM_{t−1} + q_t` with
`q_t = qmQ`. -/
noncomputable def McQ (S : MeasExpectationSystem Ω) (Mh : ℕ → Ω → ιz → ℝ) (t0 : ℕ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : ℕ → Ω → ιz → ℝ :=
  Mseq (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) Mh t0 (qmQ P Q S y)

/-- Woodford (2003), p. 555 and (1.21), case (ii): the full multiplier vector
`φ_t = (ξ_t, M_{t−1})` with `ξ_t = ΥM_{t−1} + r_t` from `t₀` on. -/
noncomputable def φcQ (S : MeasExpectationSystem Ω) (Mh : ℕ → Ω → ιz → ℝ) (t0 : ℕ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : ℕ → Ω → ιZ ⊕ ιz → ℝ :=
  fun s ω => Sum.elim (if t0 ≤ s then PencilSplit.Υmat P.sys (Q.Jp * Q.P) *ᵥ
    McQ P Q S Mh t0 y (s - 1) ω + rmQ P Q S y s ω else 0) (McQ P Q S Mh t0 y (s - 1) ω)

variable {P Q}

/-- Woodford (2003), p. 540, case (ii): the implied `M_t` is known at `t`. -/
theorem McQ_known {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) (hya : MAdaptedV S y) {Mh : ℕ → Ω → ιz → ℝ} (hMhk : MAdaptedV S Mh)
    {t0 : ℕ} (ht0 : 1 ≤ t0) : ∀ s, MKnownV S s (McQ P Q S Mh t0 y s) := by
  intro s
  induction s with
  | zero =>
    have : McQ P Q S Mh t0 y 0 = Mh 0 := by
      simp only [McQ, Mseq, show 0 < t0 by omega, ↓reduceIte]
    rw [this]
    exact hMhk 0
  | succ s ih =>
    by_cases hs : s + 1 < t0
    · have : McQ P Q S Mh t0 y (s + 1) = Mh (s + 1) := by
        simp only [McQ, Mseq, hs, ↓reduceIte]
      rw [this]
      exact hMhk _
    · have hrec : McQ P Q S Mh t0 y (s + 1) = fun ω =>
          PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P) *ᵥ McQ P Q S Mh t0 y s ω +
            qmQ P Q S y (s + 1) ω := funext fun ω => by
        have := Mseq_rec (Λ := PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) (Mh := Mh)
          (q := qmQ P Q S y) ht0 (s + 1) (by omega) ω
        rw [Nat.add_sub_cancel] at this
        exact this
      rw [hrec]
      intro i
      exact sm_comp₂ (fun j => (ih j).mono (S.𝓕.mono (Nat.le_succ s)))
        ((qmQ_known_bdd (P := P) (Q := Q) hyb hya).1 (s + 1))
        (g := fun p => (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P) *ᵥ p.1 + p.2) i) (by fun_prop)

omit [MeasurableSpace Ω] [Fintype ιτ] in
/-- Woodford (2003), (1.21), p. 553, case (ii): the residual `D = J⁺'Î'φ − F⁺` of a multiplier
vector `φ = (ΥM + (J₁')⁻¹P'F⁺, M)` lies in `ker P'` (for `J = J⁺P`). -/
theorem pD_zero (M : ιz → ℝ) (F : ιc → ℝ) :
    Q.Pᵀ *ᵥ ((Q.Jpᵀ * P.sys.Ihatᵀ) *ᵥ Sum.elim (PencilSplit.Υmat P.sys (Q.Jp * Q.P) *ᵥ M +
      ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ F)) M - F) = 0 := by
  rw [mulVec_sub, Prop81CaseII.wp_P, Prop81General.w_split]
  have := (Prop81General.eq121_iff P.sys Q.J1_det (ξpart (Sum.elim
    (PencilSplit.Υmat P.sys (Q.Jp * Q.P) *ᵥ M +
      ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ F)) M)) (Q.Pᵀ *ᵥ F) M).mp rfl
  change (PencilSplit.J1 (Q.Jp * Q.P))ᵀ *ᵥ ξpart (Sum.elim
    (PencilSplit.Υmat P.sys (Q.Jp * Q.P) *ᵥ M +
      ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ F)) M) +
    (PencilSplit.J2 (Q.Jp * Q.P))ᵀ *ᵥ (P.sys.Etᵀ *ᵥ M) - Q.Pᵀ *ᵥ F = 0
  rw [this, sub_self]

/-- Woodford (2003), **Proposition 8.2 (the converse direction), p. 555, case (ii) of
Assumption 8.2, with genuine conditional expectations**: for a quasi-split, a bounded feasible
plan that satisfies the target criterion (1.23) a.s. at all `t ≥ t₀` (with a consistent, bounded,
adapted history and Assumption 8.5) **solves (1.1) + (1.9)**, with the multipliers `φcQ` and the
initial multiplier `M_{t₀−1}` from the history. Any disturbance; no stability of `Λ`. The
`ξ`-rows of (1.18) follow from the a.s. forward uniqueness of the residual
`D_t = βH E_t D_{t+1}` (`m_fwd_zero`). -/
theorem m_focSystem_of_criterionQ {S : MeasExpectationSystem Ω}
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))
      P.sys.B2)
    {D t0 : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MFeasible S P c t0 Z0 y)
    (hcrit : MCriterionQ P Q S D t0 qh vh y) :
    MFOCSystem S P c t0 Z0 (Mh (t0 - 1)) y (φcQ P Q S Mh t0 y) := by
  classical
  have hyb := hy.2.2.1
  have hya := hy.2.2.2
  set Λ := PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P) with hΛ
  set Υ := PencilSplit.Υmat P.sys (Q.Jp * Q.P) with hΥ
  set Ji := ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ with hJi
  set B1 := Q.Jpᵀ * P.sys.Ihatᵀ with hB1
  set Ms := McQ P Q S Mh t0 y with hMs
  set φs := φcQ P Q S Mh t0 y with hφs
  set qs := splice t0 qh (qmQ P Q S y) with hqs
  set vs := splice t0 vh (vproc P y) with hvs
  have ht0 : 1 ≤ t0 := by omega
  have hβ : P.β ≠ 0 := P.β_pos.ne'
  -- the criterion with `qmQ`
  have hc' : ∀ᵐ ω ∂S.μ, ∀ t, t0 ≤ t → TargetCriterion.Crit.crit (Adjugate.alpha Λ)
      (Adjugate.Bpoly Λ) D P.sys.B2 vs qs t ω = 0 := by
    have hq : ∀ᵐ ω ∂S.μ, ∀ u, qmQ P Q S y u ω = qMQ P Q S y u ω :=
      ae_all_iff.2 fun u => qmQ_eq_qMQ (P := P) (Q := Q) hyb hya u
    refine ae_all_iff.2 fun t => ?_
    by_cases ht : t0 ≤ t
    · filter_upwards [hcrit t ht, hq] with ω e hω _
      have hqq : ∀ u, qs u ω = splice t0 qh (qMQ P Q S y) u ω := fun u => by
        simp only [hqs, splice]
        split_ifs
        · rfl
        · exact hω u
      rw [crit_congr _ _ _ _ _ t ω hqq]
      exact e
    · exact Eventually.of_forall fun _ h => absurd h ht
  -- (1.20) for the spliced processes
  have h120 : ∀ᵐ ω ∂S.μ, ∀ s, t0 - D ≤ s → Ms s ω = Λ *ᵥ Ms (s - 1) ω + qs s ω := by
    have hh : ∀ s, ∀ᵐ ω ∂S.μ, t0 - D ≤ s → s < t0 → Mh s ω = Λ *ᵥ Mh (s - 1) ω + qh s ω := by
      intro s
      by_cases hs : t0 - D ≤ s ∧ s < t0
      · filter_upwards [hhist.1 s hs.1 hs.2] with ω e _ _
        exact e
      · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hs
    filter_upwards [ae_all_iff.2 hh] with ω e s hs
    by_cases hlt : s < t0
    · simp only [hMs, McQ, Mseq, hqs, splice, hlt, ↓reduceIte, show s - 1 < t0 by omega]
      exact e s hs hlt
    · simp only [hqs, splice, hlt, ↓reduceIte]
      exact Mseq_rec ht0 s (by omega) ω
  -- (1.19) from the criterion
  have h119 : ∀ᵐ ω ∂S.μ, ∀ s, t0 - D ≤ s → P.sys.B2 ⬝ᵥ Ms s ω + vs s ω = 0 := by
    have hh : ∀ s, ∀ᵐ ω ∂S.μ, t0 - D ≤ s → s < t0 → P.sys.B2 ⬝ᵥ Mh s ω + vh s ω = 0 := by
      intro s
      by_cases hs : t0 - D ≤ s ∧ s < t0
      · filter_upwards [hhist.2 s hs.1 hs.2] with ω e _ _
        exact e
      · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hs
    filter_upwards [hc', h120, ae_all_iff.2 hh] with ω e1 e2 e3
    have := TargetCriterion.Crit.eq119_of_criterion (Adjugate.eq122 Λ)
      (Adjugate.alpha_coeff_zero Λ) hB hα P.sys.B2 (M := fun u (_ : Unit) => Ms u ω)
      (q := fun u (_ : Unit) => qs u ω) (v := fun u (_ : Unit) => vs u ω) (t1 := t0 - D)
      (t0 := t0) (by omega) (fun u hu _ => e2 u hu)
      (fun u hu hlt _ => by
        simp only [hMs, McQ, Mseq, hvs, splice, hlt, ↓reduceIte]
        exact e3 u hu hlt)
      (fun u hu _ => e1 u hu)
    exact fun s hs => this s hs ()
  -- the multipliers are bounded (Assumption 8.5)
  obtain ⟨KMh, hKMh⟩ := hMhb
  obtain ⟨Kqh, hKqh⟩ := hqhb
  obtain ⟨Kvh, hKvh⟩ := hvhb
  obtain ⟨Kqm, hKqm⟩ := (qmQ_known_bdd (P := P) (Q := Q) hyb hya).2
  obtain ⟨Ky, hKy⟩ := hyb
  obtain ⟨Kv, hKv⟩ := vv_bound P Ky
  obtain ⟨KM, hKM⟩ : ∃ KM, ∀ s, ∀ᵐ ω ∂S.μ, ∀ i, |Ms s ω i| ≤ KM := by
    refine krylov_ae h85 (q := qs) (v := vs) (s0 := t0 - D - 1) (Kq := max Kqh Kqm)
      (Kv := max Kvh Kv) (K0 := KMh) ?_
    filter_upwards [h120, h119, ae_all_iff.2 hKMh, ae_all_iff.2 hKqh, ae_all_iff.2 hKvh,
      ae_all_iff.2 hKqm, ae_all_iff.2 hKy] with ω e1 e2 b1 b2 b3 b4 b5
    refine ⟨fun s i => ?_, fun s => ?_, fun s hs i => ?_, fun s hs => e1 s (by omega),
      fun s hs => e2 s (by omega)⟩
    · simp only [hqs, splice]
      split_ifs
      · exact (b2 s i).trans (le_max_left _ _)
      · exact (b4 s i).trans (le_max_right _ _)
    · simp only [hvs, splice]
      split_ifs
      · exact (b3 s).trans (le_max_left _ _)
      · exact (hKv _ (b5 s)).trans (le_max_right _ _)
    · simp only [hMs, McQ, Mseq, show s < t0 by omega, ↓reduceIte]
      exact b1 s i
  have hyb : MBoundedV S y := ⟨Ky, hKy⟩
  obtain ⟨KF, hKF⟩ := FmQ_bdd (P := P) (Q := Q) hyb
  have hMk := McQ_known (P := P) (Q := Q) hyb hya hMhk ht0
  have hMi : ∀ s i, Integrable (fun ω => Ms s ω i) S.μ := fun s i =>
    integrable_of_bound ((hMk s i).mono (S.𝓕.le s)).aestronglyMeasurable
      ((hKM s).mono fun ω h => h i)
  have hri : ∀ s i, Integrable (fun ω => rmQ P Q S y s ω i) S.μ := fun s i =>
    integrable_of_bound (((rmQ_known (P := P) (Q := Q) S y s).2 i).mono
      (S.𝓕.le s)).aestronglyMeasurable ((hKF s).mono fun ω h => h.2 i)
  obtain ⟨KΥ, hKΥ⟩ := exists_bound_mulVec Υ KM
  -- bounds and measurability of the multipliers
  have hφb : MBoundedV S φs := by
    refine ⟨max (max (KΥ + KF) KM) 0, fun s => ?_⟩
    filter_upwards [hKM (s - 1), hKF s] with ω h1 h2 i
    rcases i with j | r
    · simp only [hφs, φcQ, Sum.elim_inl]
      split_ifs
      · exact ((abs_add_le _ _).trans (add_le_add (hKΥ _ h1 j) (h2.2 j))).trans
          ((le_max_left _ _).trans (le_max_left _ _))
      · simp only [Pi.zero_apply, abs_zero]
        exact le_max_right _ _
    · exact (h1 r).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hφm : MAEMeasV S φs := by
    intro s i
    rcases i with j | r
    · by_cases hs : t0 ≤ s
      · have : (fun ω => φs s ω (Sum.inl j)) =
            fun ω => (Υ *ᵥ Ms (s - 1) ω + rmQ P Q S y s ω) j := by
          funext ω
          simp only [hφs, φcQ, hs, ↓reduceIte, Sum.elim_inl]
          rfl
        rw [this]
        exact ((integrable_mulVec _ (hMi (s - 1)) j).add (hri s j)).aestronglyMeasurable
      · have : (fun ω => φs s ω (Sum.inl j)) = fun _ => 0 := by
          funext ω
          simp only [hφs, φcQ, hs, ↓reduceIte, Sum.elim_inl, Pi.zero_apply]
        rw [this]
        exact aestronglyMeasurable_const
    · exact ((hMk (s - 1) r).mono (S.𝓕.le _)).aestronglyMeasurable
  have hφi : ∀ s i, Integrable (fun ω => φs s ω i) S.μ := by
    obtain ⟨Kφ, hKφ⟩ := hφb
    exact fun s i => integrable_of_bound (hφm s i) ((hKφ s).mono fun ω h => h i)
  -- the shape of `φ_t` and of `E_t φ_{t+1}`
  have hφ0 : ∀ t, t0 ≤ t → ∀ ω, φs t ω =
      Sum.elim (Υ *ᵥ Ms (t - 1) ω + Ji *ᵥ (Q.Pᵀ *ᵥ FmQ P Q S y t ω)) (Ms (t - 1) ω) :=
    fun t ht ω => by
      simp only [hφs, φcQ, ht, ↓reduceIte]
      rfl
  have hφ1 : ∀ t, t0 ≤ t → ∀ ω, φs (t + 1) ω =
      Sum.elim (Υ *ᵥ Ms t ω + rmQ P Q S y (t + 1) ω) (Ms t ω) := fun t ht ω => by
    simp only [hφs, φcQ, show t0 ≤ t + 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
    rfl
  have hErm : ∀ t, ∀ᵐ ω ∂S.μ, EVm S t (rmQ P Q S y (t + 1)) ω =
      Ji *ᵥ (Q.Pᵀ *ᵥ EVm S t (FmQ P Q S y (t + 1)) ω) := by
    intro t
    have hFi : ∀ i, Integrable (fun ω => FmQ P Q S y (t + 1) ω i) S.μ := fun i =>
      S.integrable_E _ _
    filter_upwards [EVm_mulVec S t (Ji * Q.Pᵀ) hFi] with ω e
    have : EVm S t (rmQ P Q S y (t + 1)) ω =
        EVm S t (fun ω => (Ji * Q.Pᵀ) *ᵥ FmQ P Q S y (t + 1) ω) ω := by
      unfold rmQ
      simp only [hJi, mulVec_mulVec]
    rw [this, e, ← mulVec_mulVec]
  have hE : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, EVm S t (φs (t + 1)) ω =
      Sum.elim (Υ *ᵥ Ms t ω + Ji *ᵥ (Q.Pᵀ *ᵥ EVm S t (FmQ P Q S y (t + 1)) ω)) (Ms t ω) := by
    intro t ht
    filter_upwards [EVm_add S t (x := fun ω => Υ *ᵥ Ms t ω) (x' := rmQ P Q S y (t + 1))
      (integrable_mulVec _ (hMi t)) (hri (t + 1)), EVm_mulVec S t Υ (hMi t), hErm t]
      with ω e1 e2 e3
    funext idx
    rcases idx with j | r
    · have hfun : (fun ω' => φs (t + 1) ω' (Sum.inl j)) =
          fun ω' => (Υ *ᵥ Ms t ω' + rmQ P Q S y (t + 1) ω') j := funext fun ω' => by
        rw [hφ1 t ht]
        rfl
      change S.E t (fun ω' => φs (t + 1) ω' (Sum.inl j)) ω = _
      rw [hfun]
      have := congrFun e1 j
      simp only [EVm] at this
      rw [this, Pi.add_apply, e2, e3, EVm_of_known S (hMk t) (hMi t)]
      rfl
    · change S.E t (fun ω' => φs (t + 1) ω' (Sum.inr r)) ω = _
      exact congrFun (S.E_of_stronglyMeasurable (hMk t r) (hMi t r)) ω
  -- (1.20) at `t` in the form of `eq118Q_pt`
  have hMrec : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, Ms t ω = Λ *ᵥ Ms (t - 1) ω +
      -((PencilSplit.Kmat P.sys (Q.Jp * Q.P))⁻¹ *ᵥ
        (Mpart (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar))) +
          P.sys.A12ᵀ *ᵥ (Ji *ᵥ (Q.Pᵀ *ᵥ EVm S t (FmQ P Q S y (t + 1)) ω)))) := by
    intro t ht
    filter_upwards [hErm t] with ω h
    have := Mseq_rec (Λ := Λ) (Mh := Mh) (q := qmQ P Q S y) ht0 t ht ω
    refine this.trans ?_
    unfold qmQ
    rw [h]
    rfl
  -- the residual `D_t = J⁺'Î'φ_t − F⁺_t`
  set Dq : ℕ → Ω → ιc → ℝ := fun s ω => B1 *ᵥ φs s ω - FmQ P Q S y s ω with hDq
  have hPD : ∀ s, t0 ≤ s → ∀ ω, Q.Pᵀ *ᵥ Dq s ω = 0 := fun s hs ω => by
    simp only [hDq]
    rw [hφ0 s hs ω]
    exact pD_zero (Ms (s - 1) ω) (FmQ P Q S y s ω)
  have hDi : ∀ s i, Integrable (fun ω => Dq s ω i) S.μ := fun s i =>
    (integrable_mulVec B1 (hφi s) i).sub (S.integrable_E _ _)
  have hDb : MBoundedV S Dq := by
    obtain ⟨Kφ, hKφ⟩ := hφb
    obtain ⟨KB, hKB⟩ := exists_bound_mulVec B1 Kφ
    refine ⟨KB + KF, fun s => ?_⟩
    filter_upwards [hKφ s, hKF s] with ω h1 h2 i
    exact (abs_sub _ _).trans (add_le_add (hKB _ h1 i) (h2.1 i))
  have hEsub : ∀ t, ∀ᵐ ω ∂S.μ, EVm S t (Dq (t + 1)) ω =
      B1 *ᵥ EVm S t (φs (t + 1)) ω - EVm S t (FmQ P Q S y (t + 1)) ω := by
    intro t
    have hfun : Dq (t + 1) = fun ω => B1 *ᵥ φs (t + 1) ω +
        (-1 : Matrix ιc ιc ℝ) *ᵥ FmQ P Q S y (t + 1) ω +
        (0 : Matrix ιc ιc ℝ) *ᵥ FmQ P Q S y (t + 1) ω + 0 := by
      funext ω
      simp only [hDq, neg_mulVec, one_mulVec, zero_mulVec, add_zero, sub_eq_add_neg]
    have hFi : ∀ i, Integrable (fun ω => FmQ P Q S y (t + 1) ω i) S.μ := fun i =>
      S.integrable_E _ _
    filter_upwards [EVm_affine3 S t B1 (-1 : Matrix ιc ιc ℝ) (0 : Matrix ιc ιc ℝ) 0 (hφi (t + 1))
      hFi hFi] with ω e
    rw [hfun, e, neg_mulVec, one_mulVec, zero_mulVec, add_zero, add_zero, sub_eq_add_neg]
  -- the left side of (1.18)
  set L : ℕ → Ω → ιZ ⊕ ιz → ℝ := fun t ω => P.sys.Ahatᵀ *ᵥ EVm S t (φs (t + 1)) ω +
    P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar)) - P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ φs t ω) with hL
  have hkey : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, Mpart (L t ω) = 0 ∧
      (PencilSplit.J1 Q.Jp)ᵀ *ᵥ ξpart (L t ω) =
        Q.Ψpᵀ *ᵥ EVm S t (Dq (t + 1)) ω - P.β⁻¹ • Dq t ω := by
    intro t ht
    filter_upwards [hE t ht, FmQ_rec (P := P) (Q := Q) hyb hya t, hMrec t ht, hEsub t]
      with ω e f m d
    have hpt := eq118Q_pt (P := P) (Q := Q) m f
    have hL' : L t ω = P.sys.Ahatᵀ *ᵥ Sum.elim (Υ *ᵥ Ms t ω +
          Ji *ᵥ (Q.Pᵀ *ᵥ EVm S t (FmQ P Q S y (t + 1)) ω)) (Ms t ω) +
        P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar)) -
        P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ Sum.elim (Υ *ᵥ Ms (t - 1) ω +
          Ji *ᵥ (Q.Pᵀ *ᵥ FmQ P Q S y t ω)) (Ms (t - 1) ω)) := by
      simp only [hL]
      rw [e, hφ0 t ht ω]
    have hDt : Dq t ω = B1 *ᵥ Sum.elim (Υ *ᵥ Ms (t - 1) ω +
        Ji *ᵥ (Q.Pᵀ *ᵥ FmQ P Q S y t ω)) (Ms (t - 1) ω) - FmQ P Q S y t ω := by
      simp only [hDq]
      rw [hφ0 t ht ω]
    rw [hL', d, e, hDt]
    exact ⟨hpt.1, hpt.2⟩
  -- the residual recursion `D_t = βH E_t D_{t+1}`
  have hJ1T : (PencilSplit.J1 (Q.Jp * Q.P))ᵀ = Q.Pᵀ * (PencilSplit.J1 Q.Jp)ᵀ := by
    rw [PencilSplit.J1_mul, transpose_mul]
  have hu : IsUnit ((PencilSplit.J1 (Q.Jp * Q.P))ᵀ).det := by
    rw [det_transpose]
    exact Ne.isUnit Q.J1_det
  have hEPD : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, Q.Pᵀ *ᵥ EVm S t (Dq (t + 1)) ω = 0 := by
    intro t ht
    filter_upwards [EVm_mulVec S t Q.Pᵀ (hDi (t + 1))] with ω e
    have h0 : (fun ω' => Q.Pᵀ *ᵥ Dq (t + 1) ω') = fun _ => (0 : ιZ → ℝ) :=
      funext fun ω' => hPD (t + 1) (by omega) ω'
    rw [← e, h0, EVm_const]
  have hξ : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, ξpart (L t ω) =
      Ji *ᵥ (Q.Pᵀ *ᵥ (Q.Ψpᵀ *ᵥ EVm S t (Dq (t + 1)) ω)) := by
    intro t ht
    filter_upwards [hkey t ht] with ω k
    have h2 := congrArg (Q.Pᵀ *ᵥ ·) k.2
    rw [mulVec_mulVec, ← hJ1T, mulVec_sub, mulVec_smul, hPD t ht ω, smul_zero,
      sub_zero] at h2
    rw [← h2, hJi, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  have hrecD : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, Dq t ω = (P.β • Q.H) *ᵥ EVm S t (Dq (t + 1)) ω := by
    intro t ht
    filter_upwards [hkey t ht, hξ t ht, hEPD t ht] with ω k x p
    have h3 : (Prop81CaseII.residProj Q.Jp Q.P * Q.Ψpᵀ) *ᵥ EVm S t (Dq (t + 1)) ω =
        P.β⁻¹ • Dq t ω := by
      have h1 := k.2
      rw [x] at h1
      rw [Prop81CaseII.residProj, Matrix.sub_mul, Matrix.one_mul, sub_mulVec, ← mulVec_mulVec,
        ← mulVec_mulVec, ← mulVec_mulVec, h1]
      abel
    rw [Q.resid _ p] at h3
    rw [smul_mulVec, h3, smul_smul, mul_inv_cancel₀ hβ, one_smul]
  have hD0 := m_fwd_zero Q.decay hDb hrecD
  -- (1.18) a.s.
  have h118 : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, L t ω = 0 := by
    intro t ht
    have hED : ∀ᵐ ω ∂S.μ, EVm S t (Dq (t + 1)) ω = 0 := by
      filter_upwards [EVm_congr S t (hD0 (t + 1) (by omega))] with ω e
      rw [e, EVm_const]
    filter_upwards [hkey t ht, hξ t ht, hED] with ω k x z
    funext a
    rcases a with i | r
    · have := congrFun x i
      rw [z, mulVec_zero, mulVec_zero, mulVec_zero] at this
      exact this
    · exact congrFun k.1 r
  refine ⟨hy, hφb, hφm, fun t r => ?_, Eventually.of_forall fun ω => ?_, fun t ht => ?_⟩
  · exact hMk t r
  · funext r
    simp only [hφs, φcQ, Mpart, Sum.elim_inr, McQ, Mseq, show t0 - 1 < t0 by omega, ↓reduceIte]
  · filter_upwards [hE t ht, h118 t ht, h119] with ω e l g
    have hMp : Mpart (EVm S t (φs (t + 1)) ω) = Ms t ω := by
      rw [e]
      rfl
    refine (foc_split_pt (P := P) hMp).mpr ⟨l, ?_⟩
    have := g t (by omega)
    simp only [hvs, splice, show ¬ t < t0 by omega, ↓reduceIte] at this
    exact this

/-! ### Determinacy and the equivalence -/

/-- Woodford (2003), **Proposition 8.2 (determinacy, uniqueness)**, p. 555, case (ii), with
genuine conditional expectations: under the measure Assumption 8.1 (uniqueness half) and
Assumption 8.5, two bounded feasible plans that satisfy the quasi-split criterion (1.23) a.s. from
`t₀` on agree a.s. at every `t ≥ t₀`. -/
theorem m_prop82_uniqueQ {S : MeasExpectationSystem Ω} {t0 : ℕ} (hU : MFOCUnique S P t0)
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))
      P.sys.B2)
    {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y y' : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MFeasible S P c t0 Z0 y)
    (hy' : MFeasible S P c t0 Z0 y') (hcrit : MCriterionQ P Q S D t0 qh vh y)
    (hcrit' : MCriterionQ P Q S D t0 qh vh y') : ∀ t, t0 ≤ t → y t =ᵐ[S.μ] y' t := fun t ht =>
  (hU c Z0 (Mh (t0 - 1)) y y' _ _
    (m_focSystem_of_criterionQ h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy hcrit)
    (m_focSystem_of_criterionQ h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy' hcrit') t ht).1

/-- Woodford (2003), **Proposition 8.2**, p. 555, case (ii): the plan determined by commitment to
the quasi-split criterion is the optimal plan — it equals a.s., from `t₀` on, the solution of
(1.1) + (1.9) with `M_{t₀−1}` from the history (under the measure Assumption 8.1, uniqueness
half). -/
theorem m_criterionQ_eq_foc {S : MeasExpectationSystem Ω} {t0 : ℕ} (hU : MFOCUnique S P t0)
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))
      P.sys.B2)
    {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {ys : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φs : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hs : MFOCSystem S P c t0 Z0 (Mh (t0 - 1)) ys φs) {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hy : MFeasible S P c t0 Z0 y) (hcrit : MCriterionQ P Q S D t0 qh vh y) :
    ∀ t, t0 ≤ t → y t =ᵐ[S.μ] ys t := fun t ht =>
  (hU c Z0 (Mh (t0 - 1)) y ys _ φs
    (m_focSystem_of_criterionQ h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy hcrit) hs t ht).1

/-- Woodford (2003), **Propositions 8.1–8.2 (the equivalence)**, p. 555, case (ii), with genuine
conditional expectations: for a bounded feasible plan and a consistent history, the quasi-split
criterion (1.23) holds a.s. from `t₀` on **iff** the plan solves (1.1) + (1.9) with `M_{t₀−1}`
from the history. Any disturbance. -/
theorem m_criterionQ_iff {S : MeasExpectationSystem Ω}
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))
      P.sys.B2)
    {D t0 : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MFeasible S P c t0 Z0 y) :
    MCriterionQ P Q S D t0 qh vh y ↔ ∃ φ, MFOCSystem S P c t0 Z0 (Mh (t0 - 1)) y φ := by
  have hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ := fun r =>
    ((hMhk (t0 - 1) r).mono (S.𝓕.mono (Nat.sub_le t0 1))).aestronglyMeasurable
  exact ⟨fun h => ⟨_, m_focSystem_of_criterionQ h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy h⟩,
    fun ⟨_, h⟩ => m_criterionQ P Q hD hB hα hhist h hM0⟩

/-- Woodford (2003), **Proposition 8.2, p. 555, from a quasi-split (case (ii) of Assumption 8.2),
for every bounded adapted disturbance**: under the perfect-foresight Assumption 8.1, geometric
stability of `H` (`OptimalRulesMeasureGeneral.Hgen`), Assumption 8.5 for the `Λ` of `J = J⁺P` and
degree bounds, on every filtered probability space, commitment to the criterion (1.23) built from
the quasi-split (any consistent bounded history) determines a bounded feasible plan, unique a.s.,
and it solves (1.1) + (1.9) — the optimal plan. -/
theorem m_prop82_generalQ {P : LQProblem ιZ ιz ιτ} (hA81 : Assumption81 P perfectForesight 0)
    (S : MeasExpectationSystem Ω) (t0 : ℕ)
    (hstab : PencilSplit.PowDecay (OptimalRulesMeasureGeneral.Hgen hA81))
    (Q : Prop81CaseII.QuasiSplit P.sys P.β ιc)
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))
      P.sys.B2)
    {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} (hcb : MBoundedV S c)
    (hca : MAdaptedV S c) {Z0 : Ω → ιZ → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S P c t0 Z0 y ∧ MCriterionQ P Q S D t0 qh vh y ∧
      (∀ y', MFeasible S P c t0 Z0 y' → MCriterionQ P Q S D t0 qh vh y' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MFOCSystem S P c t0 Z0 (Mh (t0 - 1)) y φ := by
  have hMb : MBoundedRV S (Mh (t0 - 1)) := by
    obtain ⟨K, hK⟩ := hMhb
    exact ⟨K, hK (t0 - 1)⟩
  have hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ := fun r =>
    ((hMhk (t0 - 1) r).mono (S.𝓕.mono (Nat.sub_le t0 1))).aestronglyMeasurable
  obtain ⟨y, φ, hsol⟩ := OptimalRulesMeasureGeneral.m_focSolvableMB_of_powDecay hA81 S t0 hstab
    c Z0 (Mh (t0 - 1)) hcb hca hZk hZb hMb (hMhk (t0 - 1))
  refine ⟨y, hsol.1, m_criterionQ P Q hD hB hα hhist hsol hM0, fun y' hy' hc' t ht => ?_,
    φ, hsol⟩
  exact m_criterionQ_eq_foc (m_focUnique_of_pf hA81.unique S t0) h85 hD hB hα hhist hMhb hMhk
    hqhb hvhb hsol hy' hc' t ht

/-- Woodford (2003), **Proposition 8.2 on every VAR economy, p. 555, from a quasi-split**: under
the perfect-foresight Assumption 8.1, geometric stability of `H_n` and Assumption 8.5, for every
VAR(1) exogenous state, every bounded `Z_{t₀}` known at `t₀` and every consistent bounded adapted
history, commitment to the quasi-split criterion (1.23) determines exactly one bounded equilibrium
a.s., and it is optimal from a timeless perspective (with `X̄_t = (Z_t, M_{t−1}, s_t)`). -/
theorem m_prop82_varQ {ιs : Type*} [Fintype ιs] [DecidableEq ιs] (A : Matrix ιs ιs ℝ)
    (C2 : Matrix ιz ιs ℝ) (hA81 : Assumption81 P perfectForesight 0) (hA : PowBdd A)
    (hstab : PencilSplit.PowDecay (Hn P A C2 hA81 hA)) {S : MeasExpectationSystem Ω}
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))
      P.sys.B2)
    {D t0 : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P))).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β (Q.Jp * Q.P)) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {Z0 : Ω → ιZ → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 y ∧ MCriterionQ P Q S D t0 qh vh y ∧
      (∀ y', MFeasible S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 y' →
        MCriterionQ P Q S D t0 qh vh y' → ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MTimelesslyOptimalPlan S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 (stateX y φ s)
        (zpart (fY P A C2 hA81 hA)) ((FY P A C2 hA81 hA).submatrix (Sum.inl ∘ Sum.inr) id) y := by
  have hMb : MBoundedRV S (Mh (t0 - 1)) := by
    obtain ⟨K, hK⟩ := hMhb
    exact ⟨K, hK (t0 - 1)⟩
  have hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ := fun r =>
    ((hMhk (t0 - 1) r).mono (S.𝓕.mono (Nat.sub_le t0 1))).aestronglyMeasurable
  obtain ⟨y, φ, hsol, -, hopt⟩ :=
    m_existsUnique_var P A C2 hA81 hA hstab hs hZk hZb hMb (hMhk (t0 - 1))
  refine ⟨y, hsol.1, m_criterionQ P Q hD hB hα hhist hsol hM0, fun y' hy' hc' t ht => ?_,
    φ, hopt⟩
  exact m_criterionQ_eq_foc (m_focUnique_of_pf hA81.unique S t0) h85 hD hB hα hhist hMhb hMhk
    hqhb hvhb hsol hy' hc' t ht

/-! ### The real split as a special case -/

omit [Fintype ιτ] in
/-- Woodford (2003), App. G.1 (special case): the quasi-split of a real deflating split
(`Prop81CaseII.quasiOfDeflating`: `J⁺ = J`, `P = I`) has the same `Λ`. -/
theorem Λmat_quasiOfDeflating (Dsp : PencilSplit.DeflatingSplit P.sys P.β) :
    PencilSplit.Λmat P.sys P.β ((Prop81CaseII.quasiOfDeflating Dsp).Jp *
      (Prop81CaseII.quasiOfDeflating Dsp).P) = PencilSplit.Λmat P.sys P.β Dsp.J := by
  change PencilSplit.Λmat P.sys P.β (Dsp.J * 1) = _
  rw [Matrix.mul_one]

omit [Fintype ιτ] in
/-- Woodford (2003), eq. (1.21) (special case): for the quasi-split of a real deflating split the
operator `R(L⁻¹)` of case (ii) is the operator of case (i), for any expectation system. -/
theorem ropII_quasiOfDeflating {Ω' : Type*} (𝔼 : ExpectationSystem Ω')
    (Dsp : PencilSplit.DeflatingSplit P.sys P.β) (x : ℕ → Ω' → ιZ ⊕ ιz → ℝ) :
    Prop81CaseII.RopII 𝔼 (Prop81CaseII.quasiOfDeflating Dsp) x = Prop81General.Rop 𝔼 Dsp x := by
  funext t ω
  change ((PencilSplit.J1 (Dsp.J * 1))ᵀ)⁻¹ *ᵥ ((1 : Matrix ιZ ιZ ℝ)ᵀ *ᵥ
    PencilSplit.fwdSum 𝔼 (P.β • Dsp.Ψᵀ) (fun t ω => (P.β • Dsp.Jᵀ) *ᵥ x t ω) t ω) =
    ((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ *ᵥ PencilSplit.fwdSum 𝔼 (P.β • Dsp.Ψᵀ)
      (Prop81General.fpart P.β Dsp.J x) t ω
  rw [Matrix.mul_one, transpose_one, one_mulVec]
  rfl

omit [Fintype ιτ] in
/-- Woodford (2003), eq. (1.25) (special case): for the quasi-split of a real deflating split the
operator `Q(L⁻¹)` of case (ii) is the operator of case (i), for any expectation system. -/
theorem qopII_quasiOfDeflating {Ω' : Type*} (𝔼 : ExpectationSystem Ω')
    (Dsp : PencilSplit.DeflatingSplit P.sys P.β) (x : ℕ → Ω' → ιZ ⊕ ιz → ℝ) :
    Prop81CaseII.QopII 𝔼 (Prop81CaseII.quasiOfDeflating Dsp) x = Prop81General.Qop 𝔼 Dsp x := by
  funext t ω
  change -((PencilSplit.Kmat P.sys (Dsp.J * 1))⁻¹ *ᵥ (EV 𝔼 t (fun ω' => Mpart (x t ω')) ω +
    P.sys.A12ᵀ *ᵥ EV 𝔼 t (Prop81CaseII.RopII 𝔼 (Prop81CaseII.quasiOfDeflating Dsp) x (t + 1)) ω))
    = _
  rw [Matrix.mul_one, ropII_quasiOfDeflating]
  rfl

/-- Woodford (2003), eq. (1.25) (special case): `qMQ` of the quasi-split of a real deflating split
is `OptimalRulesMeasureMarkov.qM` of that split. -/
theorem qMQ_quasiOfDeflating (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    (S : MeasExpectationSystem Ω) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    qMQ P (Prop81CaseII.quasiOfDeflating Dsp) S y = qM P Dsp S y := by
  funext t ω
  unfold qMQ qM
  rw [qopII_quasiOfDeflating]

/-- Woodford (2003), (1.23) (**the real split is a special case**): the quasi-split criterion of
`Prop81CaseII.quasiOfDeflating Dsp` is exactly the criterion `MCriterion` of the real split. -/
theorem mCriterionQ_quasiOfDeflating_iff (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    (S : MeasExpectationSystem Ω) (D t0 : ℕ) (qh : ℕ → Ω → ιz → ℝ) (vh : ℕ → Ω → ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    MCriterionQ P (Prop81CaseII.quasiOfDeflating Dsp) S D t0 qh vh y ↔
      MCriterion P Dsp S D t0 qh vh y := by
  unfold MCriterionQ MCriterion
  rw [Λmat_quasiOfDeflating, qMQ_quasiOfDeflating]

/-- Woodford (2003), **Proposition 8.2, p. 555 (the real split is a special case)**:
`OptimalRulesMeasureGeneral.m_prop82_general` re-derived from the quasi-split theorem
`m_prop82_generalQ` applied to `Prop81CaseII.quasiOfDeflating Dsp`. -/
theorem m_prop82_general_of_quasi {P : LQProblem ιZ ιz ιτ}
    (hA81 : Assumption81 P perfectForesight 0) (S : MeasExpectationSystem Ω) (t0 : ℕ)
    (hstab : PencilSplit.PowDecay (OptimalRulesMeasureGeneral.Hgen hA81))
    (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2)
    {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β Dsp.J) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β Dsp.J)).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} (hcb : MBoundedV S c)
    (hca : MAdaptedV S c) {Z0 : Ω → ιZ → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S P c t0 Z0 y ∧ MCriterion P Dsp S D t0 qh vh y ∧
      (∀ y', MFeasible S P c t0 Z0 y' → MCriterion P Dsp S D t0 qh vh y' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MFOCSystem S P c t0 Z0 (Mh (t0 - 1)) y φ := by
  have hΛ := Λmat_quasiOfDeflating (P := P) Dsp
  obtain ⟨y, h1, h2, h3, h4⟩ := m_prop82_generalQ hA81 S t0 hstab
    (Prop81CaseII.quasiOfDeflating Dsp) (by rw [hΛ]; exact h85) hD (by rw [hΛ]; exact hB)
    (by rw [hΛ]; exact hα) (by rw [hΛ]; exact hhist) hMhb hMhk hqhb hvhb hcb hca hZk hZb
  refine ⟨y, h1, (mCriterionQ_quasiOfDeflating_iff Dsp S D t0 qh vh y).mp h2,
    fun y' hy' hc' => h3 y' hy' ((mCriterionQ_quasiOfDeflating_iff Dsp S D t0 qh vh y').mpr hc'),
    h4⟩

/-- Woodford (2003), **Proposition 8.2 on every VAR economy, p. 555 (the real split is a special
case)**: `OptimalRulesMeasureConverse.m_prop82_var` re-derived from `m_prop82_varQ` applied to
`Prop81CaseII.quasiOfDeflating Dsp`. -/
theorem m_prop82_var_of_quasi {ιs : Type*} [Fintype ιs] [DecidableEq ιs] (A : Matrix ιs ιs ℝ)
    (C2 : Matrix ιz ιs ℝ) (hA81 : Assumption81 P perfectForesight 0) (hA : PowBdd A)
    (hstab : PencilSplit.PowDecay (Hn P A C2 hA81 hA)) {S : MeasExpectationSystem Ω}
    (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2)
    {D t0 : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β Dsp.J) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β Dsp.J)).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {Z0 : Ω → ιZ → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 y ∧ MCriterion P Dsp S D t0 qh vh y ∧
      (∀ y', MFeasible S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 y' →
        MCriterion P Dsp S D t0 qh vh y' → ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MTimelesslyOptimalPlan S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 (stateX y φ s)
        (zpart (fY P A C2 hA81 hA)) ((FY P A C2 hA81 hA).submatrix (Sum.inl ∘ Sum.inr) id) y := by
  have hΛ := Λmat_quasiOfDeflating (P := P) Dsp
  obtain ⟨y, h1, h2, h3, h4⟩ := m_prop82_varQ (Q := Prop81CaseII.quasiOfDeflating Dsp) A C2
    hA81 hA hstab (by rw [hΛ]; exact h85) hD (by rw [hΛ]; exact hB) (by rw [hΛ]; exact hα)
    (by rw [hΛ]; exact hhist) hMhb hMhk hqhb hvhb hs hZk hZb
  refine ⟨y, h1, (mCriterionQ_quasiOfDeflating_iff Dsp S D t0 qh vh y).mp h2,
    fun y' hy' hc' => h3 y' hy' ((mCriterionQ_quasiOfDeflating_iff Dsp S D t0 qh vh y').mpr hc'),
    h4⟩

/-! ### Link with the core (perfect foresight) -/

omit [Fintype ιτ] in
/-- Woodford (2003), eq. (1.25), case (ii), under perfect foresight: `Prop81CaseII.QopII`
written out. -/
theorem QopII_pf_eq (x : ℕ → Unit → ιZ ⊕ ιz → ℝ) (t : ℕ) :
    Prop81CaseII.QopII perfectForesight Q x t () =
      -((PencilSplit.Kmat P.sys (Q.Jp * Q.P))⁻¹ *ᵥ (Mpart (x t ()) + P.sys.A12ᵀ *ᵥ
        (((PencilSplit.J1 (Q.Jp * Q.P))ᵀ)⁻¹ *ᵥ (Q.Pᵀ *ᵥ fun i => ∑' k, ((P.β • Q.Ψpᵀ) ^ k *ᵥ
          ((P.β • Q.Jpᵀ) *ᵥ x (t + 1 + k) ())) i)))) := rfl

/-- Woodford (2003), eq. (1.25), case (ii) (link): on the one-point probability space the
forecast-based `qMQ` is the core operator `Prop81CaseII.QopII perfectForesight` applied to the
plan. -/
theorem qMQ_unit (y : ℕ → Unit → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ) :
    qMQ P Q Bridge.unitSystem y t () =
      Prop81CaseII.QopII perfectForesight Q (xproc P y) t () := by
  rw [qMQ_eq, QopII_pf_eq]
  have hfc : ∀ k, EVm Bridge.unitSystem t (y (t + k)) () = y (t + k) () := fun k =>
    fc_unitSystem y t k ()
  have h0 : xproc P (fun k (_ : Unit) => EVm Bridge.unitSystem t (y (t + k)) ()) 0 () =
      xproc P y t () := by
    change P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm Bridge.unitSystem t (y (t + 0)) () - P.τstar)) = _
    rw [hfc 0]
    rfl
  have h1 : (fun i => ∑' k, ((P.β • Q.Ψpᵀ) ^ k *ᵥ ((P.β • Q.Jpᵀ) *ᵥ
      xproc P (fun k (_ : Unit) => EVm Bridge.unitSystem t (y (t + k)) ()) (0 + 1 + k) ())) i) =
      fun i => ∑' k, ((P.β • Q.Ψpᵀ) ^ k *ᵥ ((P.β • Q.Jpᵀ) *ᵥ xproc P y (t + 1 + k) ())) i := by
    funext i
    refine tsum_congr fun k => ?_
    change ((P.β • Q.Ψpᵀ) ^ k *ᵥ ((P.β • Q.Jpᵀ) *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ
      EVm Bridge.unitSystem t (y (t + (0 + 1 + k))) () - P.τstar))))) i = _
    rw [hfc, show t + (0 + 1 + k) = t + 1 + k by omega]
    rfl
  rw [h0, h1]

/-- Woodford (2003), **(1.23), case (ii) (link with the core)**: on the one-point probability
space the measure-theoretic quasi-split criterion `MCriterionQ` is exactly the core criterion
`Prop82General.Prop82M.CriterionM` for the matrices of `Prop81CaseII.prop81II` under perfect
foresight. -/
theorem mCriterionQ_unit_iff {D t0 : ℕ} (qh : ℕ → Unit → ιz → ℝ) (vh : ℕ → Unit → ℝ)
    (y : ℕ → Unit → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    MCriterionQ P Q Bridge.unitSystem D t0 qh vh y ↔
      Prop82General.Prop82M.CriterionM (Prop81CaseII.prop81II P Q perfectForesight t0) D qh vh
        y := by
  have hq : ∀ u, splice t0 qh (qMQ P Q Bridge.unitSystem y) u () =
      splice t0 qh (Prop81CaseII.QopII perfectForesight Q (xproc P y)) u () := fun u => by
    simp only [splice]
    split_ifs
    · rfl
    · exact qMQ_unit y u
  constructor
  · intro h t ht ω
    rcases ω
    have := (Bridge.ae_iff_forall Bridge.unitSystem_full).mp (h t ht) ()
    rw [crit_congr _ _ _ _ _ t () hq] at this
    exact this
  · intro h t ht
    refine (Bridge.ae_iff_forall Bridge.unitSystem_full).mpr fun ω => ?_
    rcases ω
    rw [crit_congr _ _ _ _ _ t () hq]
    exact h t ht ()

end Woodford.OptimalPolicyRules.OptimalRulesMeasureQuasiSplit
