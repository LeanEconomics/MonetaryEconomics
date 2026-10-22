/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5aRuleIIIStochastic
import OptimalPolicyRules.OptimalRulesMeasureInertiaComplex
import OptimalPolicyRules.TidyR5aMeasBK

/-!
# Rule III with conditional expectations

Woodford (2003), *Interest and Prices*, Chapter 8, Propositions 8.1 and 8.2 (pp. 553–555) and
Rule III (3.24), p. 595, on every filtered probability space with Mathlib's conditional
expectation. This is the measure-theoretic version of `TidyR5aRuleIIIStochastic`.

Rule III's target criterion has lag polynomial `(1 − λ₁L)(1 − ½(λ₂ + λ₃)L)`. It is not the
criterion of a deflating split; it comes from changing the unstable eigenvalue `λ_b` of the `Λ`
of (1.20) into `ν = S/2`: `Λ' = Λ + c(Λ − λ₁I)`, `c = (ν − λ_b)/(λ_b − λ₁)`, with forcing
`q' = q − cF`, `F_t = −∑_k λ_b^{−k−1} E_t N q_{t+k}` (`ModifyM.FNm`, `ModifyM.qModm`).

* `ModifyM.m_eq120_modify`: for essentially bounded adapted `q`, `M`,
  `M_t = ΛM_{t−1} + q_t` a.s. for all `t ≥ t₀` iff `M_t = Λ'M_{t−1} + q'_t` a.s. for all
  `t ≥ t₀` (both directions by a.s. uniqueness of bounded forward solutions).
* `ModifyM.crit_of_rel120`, `ModifyM.rel120_of_crit`: (1.19) + (1.20) for `Λ'` give the target
  criterion built from `Λ'`, and conversely (under Assumption 8.5 for `Λ'`) the criterion gives
  bounded adapted multipliers satisfying (1.19) + (1.20).
* `RealCase` (`S² ≥ 4P₂₃`, base split the Rule I split `RealCase.Dsp`): `RealCase.alpha_ΛIII`,
  `RealCase.m_criterionIII` (the optimal plan satisfies Rule III's criterion a.s.),
  `RealCase.m_focSystem_of_criterionIII` (the converse) and `RealCase.m_prop82_III`
  (Proposition 8.2 for Rule III: existence, a.s. uniqueness, optimality).
* `QuasiCase`: the same for the `Λ` of every quasi-split with the spectral data `QuasiCase.FactsQ`
  (`QuasiCase.m_prop82_IIIQ`), which covers the complex case `S² < 4P₂₃` (case-(ii)
  construction `InertiaProp82Complex.inQ`).
* `AllCases.m_prop82_III_all`: **at every admissible calibration `0 < γ ≤ 1`** there is a `Λ'`
  with Rule III's lag polynomial whose target criterion determines a bounded plan, unique a.s.,
  that solves (1.1) + (1.9).
-/

namespace Woodford.OptimalPolicyRules.TidyR5aRuleIIIMeasure

open MeasureTheory Filter Matrix
open ExpectationsMeasure OptimalRulesMeasure OptimalRulesMeasureMarkov

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The modification of (1.20) with conditional expectations -/

namespace ModifyM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Woodford (2003), App. G.1, with conditional expectations: the forward solution
`F_t = −∑_k λ_b^{−k−1} E_t N q_{t+k}` of `F_t = λ_b⁻¹E_tF_{t+1} − λ_b⁻¹Nq_t`. -/
noncomputable def FNm (S : MeasExpectationSystem Ω) (N : Matrix ι ι ℝ) (lb : ℝ)
    (q : ℕ → Ω → ι → ℝ) : ℕ → Ω → ι → ℝ :=
  TidyR5aMeasBK.fwdM S (lb⁻¹ • (1 : Matrix ι ι ℝ)) (fun t ω => (-lb⁻¹) • (N *ᵥ q t ω))

/-- Woodford (2003), (1.20), with conditional expectations: the modified forcing
`q'_t = q_t − cF_t`, `c = (ν − λ_b)/(λ_b − λ₁)`. -/
noncomputable def qModm (S : MeasExpectationSystem Ω) (N : Matrix ι ι ℝ) (l1 lb ν : ℝ)
    (q : ℕ → Ω → ι → ℝ) : ℕ → Ω → ι → ℝ :=
  fun t ω => q t ω - ((ν - lb) / (lb - l1)) • FNm S N lb q t ω

/-- Woodford (2003), (1.20), a.s. for all `t ≥ t₀`: `M_t = ΛM_{t−1} + q_t`. -/
def Rel120 (S : MeasExpectationSystem Ω) (t0 : ℕ) (Λ : Matrix ι ι ℝ) (q M : ℕ → Ω → ι → ℝ) :
    Prop :=
  ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, M t ω = Λ *ᵥ M (t - 1) ω + q t ω

/-- Woodford (2003), App. G.1 (tool): `λ_b⁻¹I` has geometrically decaying powers. -/
theorem powDecay_inv {lb : ℝ} (hb : 1 < |lb|) :
    PencilSplit.PowDecay (lb⁻¹ • (1 : Matrix ι ι ℝ)) := by
  refine TidyR5aRuleIIIStochastic.Modify.powDecay_smul_one ?_
  rw [abs_inv]
  exact inv_lt_one_of_one_lt₀ hb

omit [DecidableEq ι] in
/-- Woodford (2003), App. G.1 (tool): the forcing `−λ_b⁻¹Nq` is bounded and adapted. -/
theorem fN_spec {S : MeasExpectationSystem Ω} (N : Matrix ι ι ℝ) (lb : ℝ)
    {q : ℕ → Ω → ι → ℝ} (hqb : MBoundedV S q) (hqa : MAdaptedV S q) :
    MBoundedV S (fun t ω => (-lb⁻¹) • (N *ᵥ q t ω)) ∧
      MAdaptedV S (fun t ω => (-lb⁻¹) • (N *ᵥ q t ω)) := by
  refine ⟨?_, fun t i => sm_comp (hqa t) (g := fun v => ((-lb⁻¹) • (N *ᵥ v)) i)
    (by fun_prop)⟩
  obtain ⟨K, hK⟩ := hqb
  obtain ⟨K2, hK2⟩ := GeneralFOC.exists_bound_mulVec ((-lb⁻¹) • N) K
  refine ⟨K2, fun t => ?_⟩
  filter_upwards [hK t] with ω h i
  have := hK2 _ h i
  rwa [Matrix.smul_mulVec] at this

/-- Woodford (2003), App. G.1, with conditional expectations: the properties of `F`:
`F_t = −λ_b⁻¹Nq_t + λ_b⁻¹E_tF_{t+1}` a.s., adaptedness and boundedness. -/
theorem FNm_spec {S : MeasExpectationSystem Ω} (N : Matrix ι ι ℝ) {lb : ℝ} (hb : 1 < |lb|)
    {q : ℕ → Ω → ι → ℝ} (hqb : MBoundedV S q) (hqa : MAdaptedV S q) :
    (∀ t, ∀ᵐ ω ∂S.μ, FNm S N lb q t ω =
      (-lb⁻¹) • (N *ᵥ q t ω) + lb⁻¹ • EVm S t (FNm S N lb q (t + 1)) ω) ∧
      MAdaptedV S (FNm S N lb q) ∧ MBoundedV S (FNm S N lb q) := by
  obtain ⟨hfb, hfa⟩ := fN_spec N lb hqb hqa
  refine ⟨fun t => ?_, TidyR5aMeasBK.fwdM_adapted S _ _,
    TidyR5aMeasBK.fwdM_bdd (powDecay_inv hb) hfb⟩
  filter_upwards [TidyR5aMeasBK.fwdM_rec (powDecay_inv hb) hfb hfa t] with ω e
  unfold FNm
  rw [e, TidyR5aRuleIIIStochastic.Modify.smul_one_mulVec]

/-- Woodford (2003), App. G.1 (tool), with conditional expectations: `NF_t = (λ_b − λ₁)F_t` a.s.
when `N² = (λ_b − λ₁)N` (both solve the same forward equation). -/
theorem N_FNm {S : MeasExpectationSystem Ω} {N : Matrix ι ι ℝ} {l1 lb : ℝ} (hb : 1 < |lb|)
    (hNN : N * N = (lb - l1) • N) {q : ℕ → Ω → ι → ℝ} (hqb : MBoundedV S q)
    (hqa : MAdaptedV S q) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, N *ᵥ FNm S N lb q t ω = (lb - l1) • FNm S N lb q t ω := by
  obtain ⟨hrec, hFa, hFb⟩ := FNm_spec N hb hqb hqa
  set F := FNm S N lb q with hF
  have hFi := integrable_of_adapted hFb hFa
  set D : ℕ → Ω → ι → ℝ := fun s ω => N *ᵥ F s ω - (lb - l1) • F s ω with hD
  have hDb : MBoundedV S D := by
    obtain ⟨K, hK⟩ := hFb
    obtain ⟨K2, hK2⟩ := GeneralFOC.exists_bound_mulVec (N - (lb - l1) • (1 : Matrix ι ι ℝ)) K
    refine ⟨K2, fun s => ?_⟩
    filter_upwards [hK s] with ω h i
    have := hK2 _ h i
    rwa [sub_mulVec, TidyR5aRuleIIIStochastic.Modify.smul_one_mulVec] at this
  have hNF : ∀ s i, Integrable (fun ω => (N *ᵥ F s ω) i) S.μ := fun s i =>
    integrable_mulVec N (hFi s) i
  have hcF : ∀ s i, Integrable (fun ω => ((lb - l1) • F s ω) i) S.μ := fun s i => by
    simpa [Pi.smul_apply, smul_eq_mul] using (hFi s i).const_mul (lb - l1)
  have hDrec : ∀ s, 0 ≤ s → ∀ᵐ ω ∂S.μ, D s ω = (lb⁻¹ • (1 : Matrix ι ι ℝ)) *ᵥ
      EVm S s (D (s + 1)) ω := by
    intro s _
    filter_upwards [hrec s, TidyR5aMeasBK.EVm_sub' S s (hNF (s + 1)) (hcF (s + 1)),
      EVm_mulVec S s N (hFi (s + 1)),
      EVm_mulVec S s ((lb - l1) • (1 : Matrix ι ι ℝ)) (hFi (s + 1))] with ω e1 e2 e3 e4
    rw [TidyR5aRuleIIIStochastic.Modify.smul_one_mulVec]
    change N *ᵥ F s ω - (lb - l1) • F s ω = lb⁻¹ • EVm S s (fun ω => N *ᵥ F (s + 1) ω -
      (lb - l1) • F (s + 1) ω) ω
    have e4' : EVm S s (fun ω => (lb - l1) • F (s + 1) ω) ω = (lb - l1) • EVm S s (F (s + 1)) ω :=
        by
      have := e4
      simp only [TidyR5aRuleIIIStochastic.Modify.smul_one_mulVec] at this
      exact this
    rw [e2, e3, e4', e1, mulVec_add, mulVec_smul, mulVec_smul, mulVec_mulVec, hNN,
      Matrix.smul_mulVec]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hz := OptimalRulesMeasureQuasiSplit.m_fwd_zero (powDecay_inv hb) hDb hDrec t (Nat.zero_le t)
  filter_upwards [hz] with ω e
  have := congrFun e
  funext i
  have h1 := this i
  simp only [hD, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h1
  exact h1

/-- **Woodford (2003), (1.20), p. 553, with conditional expectations: changing the unstable
eigenvalue of `Λ`.** If `(Λ − λ_bI)(Λ − λ₁I) = 0`, `λ₁ ≠ λ_b`, `|λ_b| > 1`, `|ν| > 1`, then for
essentially bounded adapted `q` and `M` (`M_t` known at `t`), `M_t = ΛM_{t−1} + q_t` a.s. for all
`t ≥ t₀` iff `M_t = Λ'M_{t−1} + q'_t` a.s. for all `t ≥ t₀`, with `Λ' = Λ + c(Λ − λ₁I)` and
`q' = qModm`. -/
theorem m_eq120_modify {S : MeasExpectationSystem Ω} {t0 : ℕ}
    {Λ : Matrix ι ι ℝ} {l1 lb ν : ℝ}
    (hmin : (Λ - lb • (1 : Matrix ι ι ℝ)) * (Λ - l1 • (1 : Matrix ι ι ℝ)) = 0)
    (h1b : l1 ≠ lb) (hb : 1 < |lb|) (hν : 1 < |ν|) {q M : ℕ → Ω → ι → ℝ}
    (hqb : MBoundedV S q) (hqa : MAdaptedV S q) (hMb : MBoundedV S M) (hMa : MAdaptedV S M) :
    Rel120 S t0 Λ q M ↔
      Rel120 S t0 (Λ + ((ν - lb) / (lb - l1)) • (Λ - l1 • (1 : Matrix ι ι ℝ)))
        (qModm S (Λ - l1 • (1 : Matrix ι ι ℝ)) l1 lb ν q) M := by
  set N := Λ - l1 • (1 : Matrix ι ι ℝ) with hN
  set cc := (ν - lb) / (lb - l1) with hcc
  have hsub : lb - l1 ≠ 0 := sub_ne_zero.mpr h1b.symm
  have hlb0 : lb ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hb
    linarith
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hν
    linarith
  have hΛN : Λ * N = lb • N := by
    have h := hmin
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h
  have hNΛ : N * Λ = lb • N := by
    have : N * Λ = Λ * N := by
      rw [hN, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one]
    rw [this, hΛN]
  have hNN : N * N = (lb - l1) • N := by
    calc N * N = Λ * N - l1 • N := by
          rw [hN, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = (lb - l1) • N := by rw [hΛN, sub_smul]
  have hcν : lb + cc * (lb - l1) = ν := by
    rw [hcc]
    field_simp
    ring
  obtain ⟨hrec, hFa, hFb⟩ := FNm_spec N hb hqb hqa
  set F := FNm S N lb q with hF
  have hFi := integrable_of_adapted hFb hFa
  have hMi := integrable_of_adapted hMb hMa
  set U : ℕ → Ω → ι → ℝ := fun s ω => N *ᵥ M (s - 1) ω with hU
  have hUk : ∀ s, t0 ≤ s → MKnownV S s (U (s + 1)) := fun s _ i => by
    simp only [hU, Nat.add_sub_cancel]
    exact sm_comp (hMa s) (g := fun v => (N *ᵥ v) i) (by fun_prop)
  have hUi : ∀ s i, Integrable (fun ω => U s ω i) S.μ := fun s i =>
    integrable_mulVec N (hMi (s - 1)) i
  have hUb : MBoundedV S U := by
    obtain ⟨K, hK⟩ := hMb
    obtain ⟨K2, hK2⟩ := GeneralFOC.exists_bound_mulVec N K
    exact ⟨K2, fun s => (hK (s - 1)).mono fun ω h i => hK2 _ h i⟩
  have hEU : ∀ s, t0 ≤ s → EVm S s (U (s + 1)) = U (s + 1) := fun s hs =>
    EVm_of_known S (hUk s hs) (hUi (s + 1))
  have hDb : MBoundedV S (fun s ω => U s ω - F s ω) := by
    obtain ⟨K1, hK1⟩ := hUb
    obtain ⟨K2, hK2⟩ := hFb
    refine ⟨K1 + K2, fun s => ?_⟩
    filter_upwards [hK1 s, hK2 s] with ω a b i
    exact (abs_sub _ _).trans (add_le_add (a i) (b i))
  have hEsub : ∀ s, ∀ᵐ ω ∂S.μ, EVm S s (fun ω => U (s + 1) ω - F (s + 1) ω) ω =
      EVm S s (U (s + 1)) ω - EVm S s (F (s + 1)) ω := fun s =>
    TidyR5aMeasBK.EVm_sub' S s (hUi (s + 1)) (hFi (s + 1))
  have hEF : ∀ s, ∀ᵐ ω ∂S.μ, EVm S s (F (s + 1)) ω = lb • F s ω + N *ᵥ q s ω := by
    intro s
    filter_upwards [hrec s] with ω e
    rw [e]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  constructor
  · intro h t ht
    have hDrec : ∀ s, t0 ≤ s → ∀ᵐ ω ∂S.μ, U s ω - F s ω =
        (lb⁻¹ • (1 : Matrix ι ι ℝ)) *ᵥ EVm S s (fun ω => U (s + 1) ω - F (s + 1) ω) ω := by
      intro s hs
      filter_upwards [h s hs, hEsub s, hEF s] with ω e1 e2 e3
      rw [TidyR5aRuleIIIStochastic.Modify.smul_one_mulVec, e2, e3, hEU s hs]
      have eU : U (s + 1) ω = lb • U s ω + N *ᵥ q s ω := by
        simp only [hU, Nat.add_sub_cancel]
        rw [e1, mulVec_add, mulVec_mulVec, hNΛ, Matrix.smul_mulVec]
      rw [eU]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    have hz := OptimalRulesMeasureQuasiSplit.m_fwd_zero (powDecay_inv hb) hDb hDrec t ht
    filter_upwards [h t ht, hz] with ω e1 e2
    have hUF : U t ω = F t ω := sub_eq_zero.mp e2
    rw [e1]
    simp only [qModm]
    rw [← hF, ← hUF, Matrix.add_mulVec, Matrix.smul_mulVec]
    simp only [hU]
    abel
  · intro h t ht
    have hNF : ∀ s, ∀ᵐ ω ∂S.μ, N *ᵥ F s ω = (lb - l1) • F s ω := fun s => N_FNm hb hNN hqb hqa s
    have hDrec : ∀ s, t0 ≤ s → ∀ᵐ ω ∂S.μ, U s ω - F s ω =
        (ν⁻¹ • (1 : Matrix ι ι ℝ)) *ᵥ EVm S s (fun ω => U (s + 1) ω - F (s + 1) ω) ω := by
      intro s hs
      filter_upwards [h s hs, hEsub s, hEF s, hNF s] with ω e1 e2 e3 e4
      rw [TidyR5aRuleIIIStochastic.Modify.smul_one_mulVec, e2, e3, hEU s hs]
      have eU : U (s + 1) ω = ν • U s ω + N *ᵥ q s ω - (cc * (lb - l1)) • F s ω := by
        simp only [hU, Nat.add_sub_cancel]
        rw [e1]
        simp only [qModm]
        rw [← hcc, ← hF, mulVec_add, mulVec_sub, mulVec_mulVec, Matrix.mul_add, Matrix.mul_smul,
            hNΛ,
          hNN, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, mulVec_smul, e4,
          ← hcν]
        funext i
        simp only [Matrix.smul_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [eU]
      have hc' : cc * (lb - l1) = ν - lb := by rw [← hcν]; ring
      rw [hc']
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    have hz := OptimalRulesMeasureQuasiSplit.m_fwd_zero
        (TidyR5aRuleIIIStochastic.Modify.powDecay_smul_one
      (by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hν)) hDb hDrec t ht
    filter_upwards [h t ht, hz] with ω e1 e2
    have hUF : U t ω = F t ω := sub_eq_zero.mp e2
    rw [e1]
    simp only [qModm]
    rw [← hF, ← hUF, Matrix.add_mulVec, Matrix.smul_mulVec]
    simp only [hU]
    abel

open TargetCriterion.Recursion in
/-- **Woodford (2003), (1.23), p. 554, with conditional expectations, from (1.20) and (1.19).**
If `M` agrees with the history before `t₀`, satisfies (1.20) with `Λ'` and `q` a.s. from `t₀` on and
(1.19) a.s. from `t₀` on, and the history is consistent (`HistoryOKm`), the target criterion
built from `Λ'` holds a.s. at every `t ≥ t₀`. -/
theorem crit_of_rel120 {S : MeasExpectationSystem Ω} {t0 D : ℕ} (hD : D + 1 ≤ t0)
    {Λ' : Matrix ι ι ℝ} (hB : ∀ i c, (Adjugate.Bpoly Λ' i c).natDegree ≤ D)
    (hα : (Adjugate.alpha Λ').natDegree ≤ D) {B2 : ι → ℝ} {Mh qh : ℕ → Ω → ι → ℝ}
    {vh : ℕ → Ω → ℝ} (hhist : HistoryOKm S Λ' B2 t0 D Mh qh vh) {M q : ℕ → Ω → ι → ℝ}
    {v : ℕ → Ω → ℝ} (hMh : ∀ u, u < t0 → M u = Mh u) (h120 : Rel120 S t0 Λ' q M)
    (h119 : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, B2 ⬝ᵥ M t ω + v t ω = 0) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, TargetCriterion.Crit.crit (Adjugate.alpha Λ')
      (Adjugate.Bpoly Λ') D B2 (splice t0 vh v) (splice t0 qh q) t ω = 0 := by
  classical
  have hs1 : ∀ u, ∀ᵐ ω ∂S.μ, t0 ≤ u → M u ω = Λ' *ᵥ M (u - 1) ω + q u ω ∧
      B2 ⬝ᵥ M u ω + v u ω = 0 := by
    intro u
    by_cases hu : t0 ≤ u
    · filter_upwards [h120 u hu, h119 u hu] with ω e1 e2 _
      exact ⟨e1, e2⟩
    · exact Eventually.of_forall fun _ h' => absurd h' hu
  have hh1 : ∀ u, ∀ᵐ ω ∂S.μ, t0 - D ≤ u → u < t0 →
      Mh u ω = Λ' *ᵥ Mh (u - 1) ω + qh u ω := by
    intro u
    by_cases hu : t0 - D ≤ u ∧ u < t0
    · filter_upwards [hhist.1 u hu.1 hu.2] with ω e _ _
      exact e
    · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hu
  have hh2 : ∀ u, ∀ᵐ ω ∂S.μ, t0 - D ≤ u → u < t0 → B2 ⬝ᵥ Mh u ω + vh u ω = 0 := by
    intro u
    by_cases hu : t0 - D ≤ u ∧ u < t0
    · filter_upwards [hhist.2 u hu.1 hu.2] with ω e _ _
      exact e
    · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hu
  intro t ht
  filter_upwards [ae_all_iff.2 hs1, ae_all_iff.2 hh1, ae_all_iff.2 hh2] with ω e1 e2 e3
  refine TargetCriterion.Crit.eq123_of_eq119_eq120 (Adjugate.eq122 _) hB hα B2
    (M := fun u (_ : Unit) => M u ω) (q := fun u (_ : Unit) => splice t0 qh q u ω)
    (v := fun u (_ : Unit) => splice t0 vh v u ω) (t0 := t0 - D) (fun u hu _ => ?_)
    (fun u hu _ => ?_) t (by omega) ()
  · unfold splice
    by_cases hlt : u < t0
    · simp only [hlt, ↓reduceIte, hMh u hlt]
      exact e3 u hu hlt
    · simp only [hlt, ↓reduceIte]
      exact (e1 u (by omega)).2
  · unfold splice
    by_cases hlt : u < t0
    · simp only [hlt, ↓reduceIte, hMh u hlt, hMh (u - 1) (by omega)]
      exact e2 u hu hlt
    · simp only [hlt, ↓reduceIte]
      exact (e1 u (by omega)).1

open TargetCriterion.Recursion in
/-- **Woodford (2003), Proposition 8.2 (the key step), p. 555, with conditional expectations.**
Under Assumption 8.5 for `Λ'`, commitment to the criterion built from `Λ'` (with a consistent
bounded history) makes the multipliers `Mseq Λ' Mh t₀ q` of (1.20) essentially bounded, adapted,
and satisfy (1.19) a.s. at every date `≥ t₀ − D`. -/
theorem rel120_of_crit {S : MeasExpectationSystem Ω} {t0 D : ℕ} (hD : D + 1 ≤ t0)
    {Λ' : Matrix ι ι ℝ} {B2 : ι → ℝ} (h85 : TargetCriterion.Krylov.Assumption85b Λ' B2)
    (hB : ∀ i c, (Adjugate.Bpoly Λ' i c).natDegree ≤ D) (hα : (Adjugate.alpha Λ').natDegree ≤ D)
    {Mh qh : ℕ → Ω → ι → ℝ} {vh : ℕ → Ω → ℝ} (hhist : HistoryOKm S Λ' B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {q : ℕ → Ω → ι → ℝ} (hqb : MBoundedV S q)
    (hqa : MAdaptedV S q) {v : ℕ → Ω → ℝ} (hvb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ K)
    (hcrit : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, TargetCriterion.Crit.crit (Adjugate.alpha Λ')
      (Adjugate.Bpoly Λ') D B2 (splice t0 vh v) (splice t0 qh q) t ω = 0) :
    MBoundedV S (Mseq Λ' Mh t0 q) ∧ MAdaptedV S (Mseq Λ' Mh t0 q) ∧
      Rel120 S t0 Λ' q (Mseq Λ' Mh t0 q) ∧
      ∀ᵐ ω ∂S.μ, ∀ s, t0 - D ≤ s → B2 ⬝ᵥ Mseq Λ' Mh t0 q s ω + splice t0 vh v s ω = 0 := by
  classical
  have ht0 : 1 ≤ t0 := by omega
  set Ms := Mseq Λ' Mh t0 q with hMs
  set qs := splice t0 qh q with hqs
  set vs := splice t0 vh v with hvs
  have hc' : ∀ᵐ ω ∂S.μ, ∀ t, t0 ≤ t → TargetCriterion.Crit.crit (Adjugate.alpha Λ')
      (Adjugate.Bpoly Λ') D B2 vs qs t ω = 0 := by
    refine ae_all_iff.2 fun t => ?_
    by_cases ht : t0 ≤ t
    · filter_upwards [hcrit t ht] with ω e _
      exact e
    · exact Eventually.of_forall fun _ h => absurd h ht
  have h120 : ∀ᵐ ω ∂S.μ, ∀ s, t0 - D ≤ s → Ms s ω = Λ' *ᵥ Ms (s - 1) ω + qs s ω := by
    have hh : ∀ s, ∀ᵐ ω ∂S.μ, t0 - D ≤ s → s < t0 → Mh s ω = Λ' *ᵥ Mh (s - 1) ω + qh s ω := by
      intro s
      by_cases hs : t0 - D ≤ s ∧ s < t0
      · filter_upwards [hhist.1 s hs.1 hs.2] with ω e _ _
        exact e
      · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hs
    filter_upwards [ae_all_iff.2 hh] with ω e s hs
    by_cases hlt : s < t0
    · simp only [hMs, Mseq, hqs, splice, hlt, ↓reduceIte, show s - 1 < t0 by omega]
      exact e s hs hlt
    · simp only [hqs, splice, hlt, ↓reduceIte]
      exact TargetCriterion.Recursion.Mseq_rec ht0 s (by omega) ω
  have h119 : ∀ᵐ ω ∂S.μ, ∀ s, t0 - D ≤ s → B2 ⬝ᵥ Ms s ω + vs s ω = 0 := by
    have hh : ∀ s, ∀ᵐ ω ∂S.μ, t0 - D ≤ s → s < t0 → B2 ⬝ᵥ Mh s ω + vh s ω = 0 := by
      intro s
      by_cases hs : t0 - D ≤ s ∧ s < t0
      · filter_upwards [hhist.2 s hs.1 hs.2] with ω e _ _
        exact e
      · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hs
    filter_upwards [hc', h120, ae_all_iff.2 hh] with ω e1 e2 e3
    have := TargetCriterion.Crit.eq119_of_criterion (Adjugate.eq122 Λ')
      (Adjugate.alpha_coeff_zero Λ') hB hα B2 (M := fun u (_ : Unit) => Ms u ω)
      (q := fun u (_ : Unit) => qs u ω) (v := fun u (_ : Unit) => vs u ω) (t1 := t0 - D)
      (t0 := t0) (by omega) (fun u hu _ => e2 u hu)
      (fun u hu hlt _ => by
        simp only [hMs, Mseq, hvs, splice, hlt, ↓reduceIte]
        exact e3 u hu hlt)
      (fun u hu _ => e1 u hu)
    exact fun s hs => this s hs ()
  obtain ⟨KMh, hKMh⟩ := hMhb
  obtain ⟨Kqh, hKqh⟩ := hqhb
  obtain ⟨Kvh, hKvh⟩ := hvhb
  obtain ⟨Kq, hKq⟩ := hqb
  obtain ⟨Kv, hKv⟩ := hvb
  obtain ⟨KM, hKM⟩ : ∃ KM, ∀ s, ∀ᵐ ω ∂S.μ, ∀ i, |Ms s ω i| ≤ KM := by
    refine OptimalRulesMeasureConverse.krylov_ae h85 (q := qs) (v := vs) (s0 := t0 - D - 1)
      (Kq := max Kqh Kq) (Kv := max Kvh Kv) (K0 := KMh) ?_
    filter_upwards [h120, h119, ae_all_iff.2 hKMh, ae_all_iff.2 hKqh, ae_all_iff.2 hKvh,
      ae_all_iff.2 hKq, ae_all_iff.2 hKv] with ω e1 e2 b1 b2 b3 b4 b5
    refine ⟨fun s i => ?_, fun s => ?_, fun s hs i => ?_, fun s hs => e1 s (by omega),
      fun s hs => e2 s (by omega)⟩
    · simp only [hqs, splice]
      split_ifs
      · exact (b2 s i).trans (le_max_left _ _)
      · exact (b4 s i).trans (le_max_right _ _)
    · simp only [hvs, splice]
      split_ifs
      · exact (b3 s).trans (le_max_left _ _)
      · exact (b5 s).trans (le_max_right _ _)
    · simp only [hMs, Mseq, show s < t0 by omega, ↓reduceIte]
      exact b1 s i
  have hMk : ∀ s, MKnownV S s (Ms s) := by
    intro s
    induction s with
    | zero =>
      have : Ms 0 = Mh 0 := by simp only [hMs, Mseq, show 0 < t0 by omega, ↓reduceIte]
      rw [this]
      exact hMhk 0
    | succ s ih =>
      by_cases hs : s + 1 < t0
      · have : Ms (s + 1) = Mh (s + 1) := by simp only [hMs, Mseq, hs, ↓reduceIte]
        rw [this]
        exact hMhk _
      · have hrec : Ms (s + 1) = fun ω => Λ' *ᵥ Ms s ω + q (s + 1) ω := funext fun ω => by
          have := TargetCriterion.Recursion.Mseq_rec (Λ := Λ') (Mh := Mh) (q := q) ht0 (s + 1)
            (by omega) ω
          rw [Nat.add_sub_cancel] at this
          exact this
        rw [hrec]
        intro i
        exact sm_comp₂ (fun j => (ih j).mono (S.𝓕.mono (Nat.le_succ s))) (hqa (s + 1))
          (g := fun p => (Λ' *ᵥ p.1 + p.2) i) (by fun_prop)
  refine ⟨⟨KM, hKM⟩, hMk, fun t ht => Eventually.of_forall fun ω =>
    TargetCriterion.Recursion.Mseq_rec ht0 t ht ω, ?_⟩
  filter_upwards [h119] with ω e s hs
  exact e s hs

end ModifyM

/-! ### Rule III for the inflation-inertia model, real case -/

namespace RealCase

open IRuleBasic (Calib)
open CubicRoots
open GeneralLinksInertia (inSys inProblem in_det_ne)
open TargetCriterion.Recursion (splice Mseq)
open TargetCriterion.Prop81 (vproc)
open GeneralFOC.LQ (Mpart)

variable (c : Calib) (γ : ℝ) (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
  (hD : 0 ≤ discQ c.β γ c.κ c.σ)

/-- Woodford (2003), App. G.6 and Rule I (3.22): the base deflating split of the inertia model in
the real case (`λ₃` solved forward), whose `Λ` has the eigenvalues `λ₁, λ₂`. -/
noncomputable def Dsp :
    PencilSplit.DeflatingSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β :=
  InertiaSplit.inSplit c γ hc hγ0 hγ1 (InertiaSplit.quadQ_lam3r hD)

/-- Woodford (2003), (1.20): the `Λ` of the base split. -/
noncomputable def Λb : Matrix (Fin 2) (Fin 2) ℝ :=
  PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β
    (Dsp c γ hc hγ0 hγ1 hD).J

/-- Woodford (2003), Rule III (3.24): `Λ' = Λ + c(Λ − λ₁I)` with
`c = (S/2 − λ₂)/(λ₂ − λ₁)`, so that `det(I − Λ'L) = (1 − λ₁L)(1 − ½(λ₂ + λ₃)L)`. -/
noncomputable def ΛIII : Matrix (Fin 2) (Fin 2) ℝ :=
  Λb c γ hc hγ0 hγ1 hD + ((sumS c.β γ c.κ c.σ / 2 - lam2r c.β γ c.κ c.σ) /
    (lam2r c.β γ c.κ c.σ - lam1 c.β γ c.κ c.σ)) •
    (Λb c γ hc hγ0 hγ1 hD - lam1 c.β γ c.κ c.σ • (1 : Matrix (Fin 2) (Fin 2) ℝ))

/-- Woodford (2003), Rule III (3.24), with conditional expectations: the forcing
`q'_t = q_t − cE_tF_t` of Rule III's target criterion, `q_t` the base split's `E_tQ(L⁻¹)` on
the realised forward sums (`OptimalRulesMeasureConverse.qm`). -/
noncomputable def qIII (S : MeasExpectationSystem Ω)
    (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) : ℕ → Ω → Fin 2 → ℝ :=
  ModifyM.qModm S (Λb c γ hc hγ0 hγ1 hD - lam1 c.β γ c.κ c.σ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (lam1 c.β γ c.κ c.σ) (lam2r c.β γ c.κ c.σ) (sumS c.β γ c.κ c.σ / 2)
    (OptimalRulesMeasureConverse.qm (inProblem c γ hc hγ0.le) (Dsp c γ hc hγ0 hγ1 hD) S y)

/-- **Woodford (2003), Rule III (3.24), p. 595, as a target criterion (1.23) with conditional
expectations**: `α(L)v_t + B₂'B(L)q'_t = 0` a.s. at all `t ≥ t₀` with `α = det(I − Λ'L)` Rule III's
lag polynomial, `B = adj(I − Λ'L)`, and the historical `q`, `v` before `t₀`. -/
def MCriterionIII (S : MeasExpectationSystem Ω) (D t0 : ℕ) (qh : ℕ → Ω → Fin 2 → ℝ)
    (vh : ℕ → Ω → ℝ) (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, TargetCriterion.Crit.crit (Adjugate.alpha (ΛIII c γ hc hγ0 hγ1 hD))
    (Adjugate.Bpoly (ΛIII c γ hc hγ0 hγ1 hD)) D (inProblem c γ hc hγ0.le).sys.B2
    (splice t0 vh (vproc (inProblem c γ hc hγ0.le) y)) (splice t0 qh (qIII c γ hc hγ0 hγ1 hD S y))
    t ω = 0

/-- Woodford (2003), App. G.6 (tool): `tr Λ = λ₁ + λ₂`, `det Λ = λ₁λ₂` for the base split, with
`λ₂ > 1 > λ₁ > 0`. -/
theorem Λb_facts : (Λb c γ hc hγ0 hγ1 hD).trace = lam1 c.β γ c.κ c.σ + lam2r c.β γ c.κ c.σ ∧
    (Λb c γ hc hγ0 hγ1 hD).det = lam1 c.β γ c.κ c.σ * lam2r c.β γ c.κ c.σ ∧
    1 < lam2r c.β γ c.κ c.σ ∧ 0 < lam1 c.β γ c.κ c.σ ∧ lam1 c.β γ c.κ c.σ < 1 := by
  have h := InertiaSplit.standing_of c γ hc hγ0 hγ1
  have hσ : c.σ ≠ 0 := hc.2.2.1.ne'
  have hd := in_det_ne c γ hc hγ0.le
  have hq := InertiaSplit.quadQ_lam3r hD
  obtain ⟨hp, h1, h0, -⟩ := InertiaSplit.mu_facts c γ h hq
  have hls : lam3r c.β γ c.κ c.σ ≠ 0 := by linarith [one_lt_lam3r h]
  have hb : sumS c.β γ c.κ c.σ - lam3r c.β γ c.κ c.σ = lam2r c.β γ c.κ c.σ := by
    rw [← InertiaSplit.lam2r_add_lam3r]
    ring
  have htr := InertiaSplit.in_Λ_trace c γ hσ hd hc.1.ne' hγ0.ne' hp h1 h0
  rw [InertiaSplit.tr_eq c γ h hls hp, hb] at htr
  have hdet := InertiaSplit.in_Λ_det c γ hσ hd hc.1.ne' hγ0.ne' hp h1 h0
  rw [InertiaSplit.det_eq c γ h hls hq, hb] at hdet
  obtain ⟨hl1p, hl1lt, -⟩ := lam1_spec h
  exact ⟨htr, hdet, one_lt_lam2r h, hl1p, hl1lt⟩

/-- **Woodford (2003), Rule III (3.24): `det(I − Λ'L) = (1 − λ₁L)(1 − ½(λ₂ + λ₃)L)`.** -/
theorem alpha_ΛIII : Adjugate.alpha (ΛIII c γ hc hγ0 hγ1 hD) =
    TidyR5aRuleIIIStochastic.Inertia.ruleIIIpoly c γ := by
  obtain ⟨htr, hdet, h2, hl1p, hl1lt⟩ := Λb_facts c γ hc hγ0 hγ1 hD
  exact InertiaRuleIII.alpha_modify _ htr hdet (by linarith)

/-- Woodford (2003), Rule III (3.24) (tool): `Λ'₁₀ ≠ 0` and `det Λ' = λ₁S/2`. -/
theorem ΛIII_facts : ΛIII c γ hc hγ0 hγ1 hD 1 0 ≠ 0 ∧
    (ΛIII c γ hc hγ0 hγ1 hD).det = lam1 c.β γ c.κ c.σ * (sumS c.β γ c.κ c.σ / 2) := by
  obtain ⟨htr, hdet, h2, hl1p, hl1lt⟩ := Λb_facts c γ hc hγ0 hγ1 hD
  have h := InertiaSplit.standing_of c γ hc hγ0 hγ1
  set l1 := lam1 c.β γ c.κ c.σ with hl1
  set lb := lam2r c.β γ c.κ c.σ with hlb
  set ν := sumS c.β γ c.κ c.σ / 2 with hνdef
  have hS := two_lt_sumS h
  have h1b : l1 ≠ lb := by linarith
  have h10 : Λb c γ hc hγ0 hγ1 hD 1 0 ≠ 0 :=
    TidyR5aRuleIIIStochastic.Inertia.in_Λ10_ne_zero c γ hc hγ0.le _ (Dsp c γ hc hγ0 hγ1 hD).K_det
  refine ⟨?_, ?_⟩
  · have hsub : lb - l1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h1b)
    have h1c : 1 + (ν - lb) / (lb - l1) ≠ 0 := by
      rw [show 1 + (ν - lb) / (lb - l1) = (ν - l1) / (lb - l1) by field_simp; ring]
      exact div_ne_zero (by linarith) hsub
    simp only [ΛIII, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_ne
      (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, mul_zero, sub_zero]
    rw [show Λb c γ hc hγ0 hγ1 hD 1 0 + (ν - lb) / (lb - l1) * Λb c γ hc hγ0 hγ1 hD 1 0 =
      (1 + (ν - lb) / (lb - l1)) * Λb c γ hc hγ0 hγ1 hD 1 0 by ring]
    exact mul_ne_zero h1c h10
  · have hα := alpha_ΛIII c γ hc hγ0 hγ1 hD
    rw [InertiaSplit.alpha_fin_two] at hα
    have e : TidyR5aRuleIIIStochastic.Inertia.ruleIIIpoly c γ =
        1 - Polynomial.C (l1 + ν) * Polynomial.X + Polynomial.C (l1 * ν) * Polynomial.X ^ 2 := by
      simp only [TidyR5aRuleIIIStochastic.Inertia.ruleIIIpoly, Polynomial.C_add,
        Polynomial.C_mul]
      ring
    rw [e] at hα
    have := congrArg (fun p : Polynomial ℝ => p.coeff 2) hα
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow] at this
    norm_num at this
    linear_combination this

/-- Woodford (2003), Assumption 8.5, App. G.2, p. 719, for Rule III's `Λ'`. -/
theorem h85III : TargetCriterion.Krylov.Assumption85b (ΛIII c γ hc hγ0 hγ1 hD)
    (inProblem c γ hc hγ0.le).sys.B2 :=
  (TidyR5aRuleIIIStochastic.Inertia.ruleIII_assumption85 c γ hc hγ0 hγ1
    (ΛIII_facts c γ hc hγ0 hγ1 hD).1 (ΛIII_facts c γ hc hγ0 hγ1 hD).2).2

/-- Woodford (2003), Assumption 8.5, App. G.2, p. 719, for the base split
(`InertiaProp8182.in_assumption85`). -/
theorem h85b : TargetCriterion.Krylov.Assumption85b (Λb c γ hc hγ0 hγ1 hD)
    (inProblem c γ hc hγ0.le).sys.B2 :=
  (InertiaProp8182.in_assumption85 c γ hc hγ0 hγ1 (InertiaSplit.quadQ_lam3r hD)).2

/-- Woodford (2003), (1.22), p. 554 (tool): a `2 × 2` matrix's representation has degree at most
`2`, so every window `D ≥ 2` carries it. -/
theorem degrees2 (Λ : Matrix (Fin 2) (Fin 2) ℝ) {D : ℕ} (hD2 : 2 ≤ D) :
    (∀ i j, (Adjugate.Bpoly Λ i j).natDegree ≤ D) ∧ (Adjugate.alpha Λ).natDegree ≤ D := by
  have hrk : Λ.rank ≤ D := (rank_le_width Λ).trans (by simpa using hD2)
  exact ⟨fun i j => (Adjugate.natDegree_Bpoly_le_rank _ i j).trans hrk,
    (Adjugate.natDegree_alpha_le_rank _).trans hrk⟩

/-- Woodford (2003), Rule III (tool): the data of the modification: `(Λ − λ₂I)(Λ − λ₁I) = 0`,
`λ₁ ≠ λ₂`, `|λ₂| > 1`, `|S/2| > 1`. -/
theorem mod_data :
    (Λb c γ hc hγ0 hγ1 hD - lam2r c.β γ c.κ c.σ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
      (Λb c γ hc hγ0 hγ1 hD - lam1 c.β γ c.κ c.σ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0 ∧
    lam1 c.β γ c.κ c.σ ≠ lam2r c.β γ c.κ c.σ ∧ 1 < |lam2r c.β γ c.κ c.σ| ∧
    1 < |sumS c.β γ c.κ c.σ / 2| := by
  obtain ⟨htr, hdet, h2, hl1p, hl1lt⟩ := Λb_facts c γ hc hγ0 hγ1 hD
  have h := InertiaSplit.standing_of c γ hc hγ0 hγ1
  have hS := two_lt_sumS h
  refine ⟨InertiaRuleIII.cayley_two _ htr hdet, by linarith, ?_, ?_⟩
  · rw [abs_of_pos (by linarith)]
    exact h2
  · rw [abs_of_pos (by linarith)]
    linarith

/-- **Woodford (2003), Rule III (3.24) with conditional expectations: the optimal plan satisfies
Rule III's target criterion.** Along every bounded solution of (1.1) + (1.9) whose initial
multiplier comes from a history consistent with Rule III's `Λ'`, the criterion holds a.s. at every
`t ≥ t₀`, for every disturbance (the base (1.20) of `OptimalRulesMeasureForecast.m_eq119_120`,
modified by `ModifyM.m_eq120_modify`). -/
theorem m_criterionIII {S : MeasExpectationSystem Ω} {cd : ℕ → Ω → Fin 2 → ℝ} {t0 D : ℕ}
    (hD1 : D + 1 ≤ t0) (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (ΛIII c γ hc hγ0 hγ1 hD) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) {Z0 : Ω → Unit → ℝ}
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} {φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ}
    (h : MFOCSystem S (inProblem c γ hc hγ0.le) cd t0 Z0 (Mh (t0 - 1)) y φ) :
    MCriterionIII c γ hc hγ0 hγ1 hD S D t0 qh vh y := by
  classical
  have ht0 : 1 ≤ t0 := by omega
  obtain ⟨hmin, h1b, hb, hν⟩ := mod_data c γ hc hγ0 hγ1 hD
  have hyb := h.1.2.2.1
  have hya := h.1.2.2.2
  obtain ⟨hqk, hqb⟩ := OptimalRulesMeasureConverse.qm_known_bdd
    (P := inProblem c γ hc hγ0.le) (Dsp := Dsp c γ hc hγ0 hγ1 hD) hyb hya
  set M : ℕ → Ω → Fin 2 → ℝ := splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) with hM
  have hMb : MBoundedV S M := by
    obtain ⟨K1, hK1⟩ := hMhb
    obtain ⟨K2, hK2⟩ := h.2.1
    refine ⟨max K1 K2, fun u => ?_⟩
    filter_upwards [hK1 u, hK2 (u + 1)] with ω a b i
    simp only [hM, splice]
    split_ifs
    · exact (a i).trans (le_max_left _ _)
    · exact (b (Sum.inr i)).trans (le_max_right _ _)
  have hMa : MAdaptedV S M := by
    intro u i
    simp only [hM, splice]
    split_ifs
    · exact hMhk u i
    · exact h.2.2.2.1 u i
  have hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ := fun r =>
    ((hMhk (t0 - 1) r).mono (S.𝓕.mono (Nat.sub_le t0 1))).aestronglyMeasurable
  have hrel : ModifyM.Rel120 S t0 (Λb c γ hc hγ0 hγ1 hD)
      (OptimalRulesMeasureConverse.qm (inProblem c γ hc hγ0.le) (Dsp c γ hc hγ0 hγ1 hD) S y) M := by
    intro t ht
    filter_upwards [OptimalRulesMeasureForecast.m_eq119_120 (inProblem c γ hc hγ0.le)
      (Dsp c γ hc hγ0 hγ1 hD) h hM0 ht,
      OptimalRulesMeasureConverse.qm_eq_qM (P := inProblem c γ hc hγ0.le)
        (Dsp := Dsp c γ hc hγ0 hγ1 hD) hyb hya t, h.2.2.2.2.1] with ω e eq e0
    have hMt : M t ω = Mpart (φ (t + 1) ω) := by
      simp only [hM, splice, show ¬ t < t0 by omega, ↓reduceIte]
    have hMt1 : M (t - 1) ω = Mpart (φ t ω) := by
      by_cases hte : t = t0
      · subst hte
        simp only [hM, splice, show t - 1 < t by omega, ↓reduceIte]
        exact e0.symm
      · simp only [hM, splice, show ¬ t - 1 < t0 by omega, ↓reduceIte]
        rw [show t - 1 + 1 = t by omega]
    rw [hMt, hMt1, e.1, eq]
    rfl
  have hrel' := (ModifyM.m_eq120_modify hmin h1b hb hν hqb hqk hMb hMa).mp hrel
  obtain ⟨hB, hα⟩ := degrees2 (ΛIII c γ hc hγ0 hγ1 hD) hD2
  have h119 : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, (inProblem c γ hc hγ0.le).sys.B2 ⬝ᵥ M t ω +
      vproc (inProblem c γ hc hγ0.le) y t ω = 0 := by
    intro t ht
    filter_upwards [OptimalRulesMeasureForecast.m_eq119_120 (inProblem c γ hc hγ0.le)
      (Dsp c γ hc hγ0 hγ1 hD) h hM0 ht] with ω e
    have hMt : M t ω = Mpart (φ (t + 1) ω) := by
      simp only [hM, splice, show ¬ t < t0 by omega, ↓reduceIte]
    rw [hMt]
    exact e.2
  exact ModifyM.crit_of_rel120 hD1 hB hα hhist (M := M)
    (fun u hu => by simp only [hM, splice, hu, ↓reduceIte]) hrel' h119

/-- Woodford (2003), Rule III (tool): the forcing `q'` of Rule III's criterion is essentially
bounded and adapted along a bounded adapted plan. -/
theorem qIII_spec {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) (hya : MAdaptedV S y) :
    MBoundedV S (qIII c γ hc hγ0 hγ1 hD S y) ∧ MAdaptedV S (qIII c γ hc hγ0 hγ1 hD S y) := by
  obtain ⟨-, -, hb, -⟩ := mod_data c γ hc hγ0 hγ1 hD
  obtain ⟨hqk, hqb⟩ := OptimalRulesMeasureConverse.qm_known_bdd
    (P := inProblem c γ hc hγ0.le) (Dsp := Dsp c γ hc hγ0 hγ1 hD) hyb hya
  obtain ⟨-, hFa, hFb⟩ := ModifyM.FNm_spec (Λb c γ hc hγ0 hγ1 hD -
    lam1 c.β γ c.κ c.σ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) hb hqb hqk
  set cc := (sumS c.β γ c.κ c.σ / 2 - lam2r c.β γ c.κ c.σ) /
    (lam2r c.β γ c.κ c.σ - lam1 c.β γ c.κ c.σ)
  refine ⟨?_, fun t i => ?_⟩
  · obtain ⟨K1, hK1⟩ := hqb
    obtain ⟨K2, hK2⟩ := hFb
    refine ⟨K1 + |cc| * K2, fun t => ?_⟩
    filter_upwards [hK1 t, hK2 t] with ω a b i
    simp only [qIII, ModifyM.qModm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (a i) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (b i) (abs_nonneg _)
  · exact (hqk t i).sub ((hFa t i).const_mul cc)

/-- **Woodford (2003), Proposition 8.2 (the converse), p. 555, for Rule III, with conditional
expectations.** A bounded feasible plan that satisfies Rule III's target criterion a.s. at all
`t ≥ t₀` (consistent bounded history) solves (1.1) + (1.9) with `M_{t₀−1}` from the history: the
multipliers of (1.20) with `Λ'` are bounded (Assumption 8.5 for `Λ'`), the modification
(`ModifyM.m_eq120_modify`) turns them into multipliers of (1.20) for the base split, and the base
converse `OptimalRulesMeasureConverse.m_focSystem_of_criterion` applies. -/
theorem m_focSystem_of_criterionIII {S : MeasExpectationSystem Ω} {t0 D : ℕ} (hD1 : D + 1 ≤ t0)
    (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (ΛIII c γ hc hγ0 hγ1 hD) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {cd : ℕ → Ω → Fin 2 → ℝ} {Z0 : Ω → Unit → ℝ}
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ}
    (hy : MFeasible S (inProblem c γ hc hγ0.le) cd t0 Z0 y)
    (hcrit : MCriterionIII c γ hc hγ0 hγ1 hD S D t0 qh vh y) :
    ∃ φ, MFOCSystem S (inProblem c γ hc hγ0.le) cd t0 Z0 (Mh (t0 - 1)) y φ := by
  classical
  obtain ⟨hmin, h1b, hb, hν⟩ := mod_data c γ hc hγ0 hγ1 hD
  have hyb := hy.2.2.1
  have hya := hy.2.2.2
  obtain ⟨hqk, hqb⟩ := OptimalRulesMeasureConverse.qm_known_bdd
    (P := inProblem c γ hc hγ0.le) (Dsp := Dsp c γ hc hγ0 hγ1 hD) hyb hya
  obtain ⟨hq3b, hq3a⟩ := qIII_spec c γ hc hγ0 hγ1 hD hyb hya
  have hvb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vproc (inProblem c γ hc hγ0.le) y t ω| ≤ K := by
    obtain ⟨Ky, hKy⟩ := hyb
    obtain ⟨Kv, hKv⟩ := OptimalRulesMeasureConverse.vv_bound (inProblem c γ hc hγ0.le) Ky
    exact ⟨Kv, fun t => (hKy t).mono fun ω h => hKv _ h⟩
  obtain ⟨hB', hα'⟩ := degrees2 (ΛIII c γ hc hγ0 hγ1 hD) hD2
  obtain ⟨hB, hα⟩ := degrees2 (Λb c γ hc hγ0 hγ1 hD) hD2
  obtain ⟨hMsb, hMsa, hrel3, h119⟩ := ModifyM.rel120_of_crit hD1 (h85III c γ hc hγ0 hγ1 hD)
    hB' hα' hhist hMhb hMhk hqhb hvhb hq3b hq3a hvb hcrit
  set Ms := Mseq (ΛIII c γ hc hγ0 hγ1 hD) Mh t0 (qIII c γ hc hγ0 hγ1 hD S y) with hMs
  have hrelb := (ModifyM.m_eq120_modify hmin h1b hb hν hqb hqk hMsb hMsa).mpr hrel3
  set qhB : ℕ → Ω → Fin 2 → ℝ := fun s ω => Ms s ω - Λb c γ hc hγ0 hγ1 hD *ᵥ Ms (s - 1) ω
    with hqhB
  have hMsh : ∀ u, u < t0 → Ms u = Mh u := fun u hu => by
    simp only [hMs, Mseq, hu, ↓reduceIte]
  have hhistB : HistoryOKm S (Λb c γ hc hγ0 hγ1 hD) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh
      qhB vh := by
    refine ⟨fun s _ hs2 => Eventually.of_forall fun ω => ?_, hhist.2⟩
    simp only [hqhB, hMsh s hs2, hMsh (s - 1) (by omega)]
    abel
  have hqhBb : MBoundedV S qhB := by
    obtain ⟨K, hK⟩ := hMsb
    obtain ⟨K2, hK2⟩ := GeneralFOC.exists_bound_mulVec (Λb c γ hc hγ0 hγ1 hD) K
    refine ⟨K + K2, fun s => ?_⟩
    filter_upwards [hK s, hK (s - 1)] with ω a b i
    exact (abs_sub _ _).trans (add_le_add (a i) (hK2 _ b i))
  have hrelM : ModifyM.Rel120 S t0 (Λb c γ hc hγ0 hγ1 hD)
      (qM (inProblem c γ hc hγ0.le) (Dsp c γ hc hγ0 hγ1 hD) S y) Ms := by
    intro t ht
    filter_upwards [hrelb t ht, OptimalRulesMeasureConverse.qm_eq_qM
      (P := inProblem c γ hc hγ0.le) (Dsp := Dsp c γ hc hγ0 hγ1 hD) hyb hya t] with ω e1 e2
    rw [e1, e2]
  have h119' : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, (inProblem c γ hc hγ0.le).sys.B2 ⬝ᵥ Ms t ω +
      vproc (inProblem c γ hc hγ0.le) y t ω = 0 := by
    intro t ht
    filter_upwards [h119] with ω e
    have := e t (by omega)
    simpa [TargetCriterion.Recursion.splice, show ¬ t < t0 by omega] using this
  have hcritB : OptimalRulesMeasureForecast.MCriterion (inProblem c γ hc hγ0.le) (Dsp c γ hc hγ0
      hγ1 hD) S D t0 qhB vh y :=
    ModifyM.crit_of_rel120 hD1 hB hα hhistB hMsh hrelM h119'
  exact ⟨_, OptimalRulesMeasureConverse.m_focSystem_of_criterion (h85b c γ hc hγ0 hγ1 hD) hD1 hB
    hα hhistB hMhb hMhk hqhBb hvhb hy hcritB⟩

/-- **Woodford (2003), Proposition 8.2, p. 555, for Rule III (3.24), on every filtered probability
space and for every bounded adapted disturbance (real case `S² ≥ 4P₂₃`).** Commitment to Rule
III's target criterion (a window of `D ≥ 2` lags and any consistent bounded history) determines a
bounded feasible plan, unique a.s., and it solves (1.1) + (1.9) — the optimal plan. -/
theorem m_prop82_III {S : MeasExpectationSystem Ω} (t0 : ℕ) {D : ℕ} (hD1 : D + 1 ≤ t0)
    (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (ΛIII c γ hc hγ0 hγ1 hD) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {cd : ℕ → Ω → Fin 2 → ℝ}
    (hcb : MBoundedV S cd) (hca : MAdaptedV S cd) {Z0 : Ω → Unit → ℝ} (hZk : MKnownV S t0 Z0)
    (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S (inProblem c γ hc hγ0.le) cd t0 Z0 y ∧
      MCriterionIII c γ hc hγ0 hγ1 hD S D t0 qh vh y ∧
      (∀ y', MFeasible S (inProblem c γ hc hγ0.le) cd t0 Z0 y' →
        MCriterionIII c γ hc hγ0 hγ1 hD S D t0 qh vh y' → ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MFOCSystem S (inProblem c γ hc hγ0.le) cd t0 Z0 (Mh (t0 - 1)) y φ := by
  have hA81 := InertiaAssumption81.in_assumption81_perfectForesight c γ hc hγ0 hγ1 0
  have hMb : MBoundedRV S (Mh (t0 - 1)) := by
    obtain ⟨K, hK⟩ := hMhb
    exact ⟨K, hK (t0 - 1)⟩
  obtain ⟨y, φ, hsol⟩ := OptimalRulesMeasureGeneral.m_focSolvableMB_of_powDecay hA81 S t0
    (OptimalRulesMeasureStabilityModels.Inertia.in_powDecay c γ hc hγ0 hγ1) cd Z0 (Mh (t0 - 1))
    hcb hca hZk hZb hMb (hMhk (t0 - 1))
  refine ⟨y, hsol.1, m_criterionIII c γ hc hγ0 hγ1 hD hD1 hD2 hhist hMhb hMhk hsol,
    fun y' hy' hc' t ht => ?_, φ, hsol⟩
  obtain ⟨φ', h'⟩ := m_focSystem_of_criterionIII c γ hc hγ0 hγ1 hD hD1 hD2 hhist hMhb hMhk hqhb
    hvhb hy' hc'
  exact (OptimalRulesMeasureForecast.m_focUnique_of_pf hA81.unique S t0 cd Z0 (Mh (t0 - 1)) y' y
    φ' φ h' hsol t ht).1

end RealCase

/-! ### Rule III for the inflation-inertia model, any quasi-split -/

namespace QuasiCase

open IRuleBasic (Calib)
open CubicRoots
open GeneralLinksInertia (inSys inProblem in_det_ne)
open TargetCriterion.Recursion (splice Mseq)
open TargetCriterion.Prop81 (vproc)
open GeneralFOC.LQ (Mpart)

variable (c : Calib) (γ : ℝ) (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {ιc : Type*} [Fintype ιc]
  [DecidableEq ιc]
  (Q : Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β ιc)
  (lb : ℝ)

/-- Woodford (2003), (1.20) and App. G.1, case (ii): the `Λ = β⁻¹K⁻¹Ẽ'` of a quasi-split
(`J = J⁺P`). -/
noncomputable def ΛQ : Matrix (Fin 2) (Fin 2) ℝ :=
  PencilSplit.Λmat (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β (Q.Jp * Q.P)

/-- Woodford (2003), Propositions 8.1 and 8.3 (the spectral data used by Rule III):
`tr Λ = λ₁ + λ_b`, `det Λ = λ₁λ_b`, `|λ_b| > 1`. -/
def FactsQ : Prop :=
  (ΛQ c γ hc hγ0 Q).trace = lam1 c.β γ c.κ c.σ + lb ∧
    (ΛQ c γ hc hγ0 Q).det = lam1 c.β γ c.κ c.σ * lb ∧ 1 < |lb|

/-- Woodford (2003), Rule III (3.24): `Λ' = Λ + c(Λ − λ₁I)`, `c = (S/2 − λ_b)/(λ_b − λ₁)`. -/
noncomputable def ΛIIIQ : Matrix (Fin 2) (Fin 2) ℝ :=
  ΛQ c γ hc hγ0 Q + ((sumS c.β γ c.κ c.σ / 2 - lb) / (lb - lam1 c.β γ c.κ c.σ)) •
    (ΛQ c γ hc hγ0 Q - lam1 c.β γ c.κ c.σ • (1 : Matrix (Fin 2) (Fin 2) ℝ))

/-- Woodford (2003), Rule III (3.24), with conditional expectations: the forcing
`q'_t = q_t − cE_tF_t`, `q_t` the quasi-split's (1.25) on the realised forward sums
(`OptimalRulesMeasureQuasiSplit.qmQ`). -/
noncomputable def qIIIQ (S : MeasExpectationSystem Ω)
    (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) : ℕ → Ω → Fin 2 → ℝ :=
  ModifyM.qModm S (ΛQ c γ hc hγ0 Q - lam1 c.β γ c.κ c.σ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (lam1 c.β γ c.κ c.σ) lb (sumS c.β γ c.κ c.σ / 2)
    (OptimalRulesMeasureQuasiSplit.qmQ (inProblem c γ hc hγ0.le) Q S y)

/-- **Woodford (2003), Rule III (3.24), p. 595, as a target criterion (1.23) with conditional
expectations, from a quasi-split**: `α(L)v_t + B₂'B(L)q'_t = 0` a.s. at all `t ≥ t₀`, with
`α = det(I − Λ'L)`, `B = adj(I − Λ'L)`, and the historical `q`, `v` before `t₀`. -/
def MCriterionIIIQ (S : MeasExpectationSystem Ω) (D t0 : ℕ) (qh : ℕ → Ω → Fin 2 → ℝ)
    (vh : ℕ → Ω → ℝ) (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, TargetCriterion.Crit.crit (Adjugate.alpha (ΛIIIQ c γ hc hγ0 Q lb))
    (Adjugate.Bpoly (ΛIIIQ c γ hc hγ0 Q lb)) D (inProblem c γ hc hγ0.le).sys.B2
    (splice t0 vh (vproc (inProblem c γ hc hγ0.le) y)) (splice t0 qh (qIIIQ c γ hc hγ0 Q lb S y))
    t ω = 0

/-- Woodford (2003), Assumption 8.5, App. G.2, p. 719, for the `Λ` of every quasi-split
(`OptimalRulesMeasureInertiaComplex.in_h85_quasi`). -/
theorem h85Q : TargetCriterion.Krylov.Assumption85b (ΛQ c γ hc hγ0 Q)
    (inProblem c γ hc hγ0.le).sys.B2 :=
  OptimalRulesMeasureInertiaComplex.in_h85_quasi c γ hc hγ0 Q

include hγ1

/-- Woodford (2003), Rule III (tool): the data of the modification: `(Λ − λ_bI)(Λ − λ₁I) = 0`,
`λ₁ ≠ λ_b`, `|λ_b| > 1`, `|S/2| > 1`. -/
theorem mod_dataQ (hF : FactsQ c γ hc hγ0 Q lb) :
    (ΛQ c γ hc hγ0 Q - lb • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
      (ΛQ c γ hc hγ0 Q - lam1 c.β γ c.κ c.σ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0 ∧
    lam1 c.β γ c.κ c.σ ≠ lb ∧ 1 < |lb| ∧ 1 < |sumS c.β γ c.κ c.σ / 2| := by
  obtain ⟨htr, hdet, hb⟩ := hF
  have h := InertiaSplit.standing_of c γ hc hγ0 hγ1
  have hS := two_lt_sumS h
  obtain ⟨hl1p, hl1lt, -⟩ := lam1_spec h
  refine ⟨InertiaRuleIII.cayley_two _ htr hdet, fun e => ?_, hb, ?_⟩
  · rw [← e, abs_of_pos hl1p] at hb
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith

/-- **Woodford (2003), Rule III (3.24): `det(I − Λ'L) = (1 − λ₁L)(1 − ½(λ₂ + λ₃)L)`** for the
modification of every quasi-split with the spectral data `FactsQ`. -/
theorem alpha_ΛIIIQ (hF : FactsQ c γ hc hγ0 Q lb) : Adjugate.alpha (ΛIIIQ c γ hc hγ0 Q lb) =
    TidyR5aRuleIIIStochastic.Inertia.ruleIIIpoly c γ :=
  InertiaRuleIII.alpha_modify _ hF.1 hF.2.1 (mod_dataQ c γ hc hγ0 hγ1 Q lb hF).2.1

/-- Woodford (2003), Rule III (3.24) (tool): `Λ'₁₀ ≠ 0` and `det Λ' = λ₁S/2`. -/
theorem ΛIIIQ_facts (hF : FactsQ c γ hc hγ0 Q lb) : ΛIIIQ c γ hc hγ0 Q lb 1 0 ≠ 0 ∧
    (ΛIIIQ c γ hc hγ0 Q lb).det = lam1 c.β γ c.κ c.σ * (sumS c.β γ c.κ c.σ / 2) := by
  obtain ⟨-, h1b, -, -⟩ := mod_dataQ c γ hc hγ0 hγ1 Q lb hF
  have h := InertiaSplit.standing_of c γ hc hγ0 hγ1
  set l1 := lam1 c.β γ c.κ c.σ with hl1
  set ν := sumS c.β γ c.κ c.σ / 2 with hνdef
  have hS := two_lt_sumS h
  obtain ⟨hl1p, hl1lt, -⟩ := lam1_spec h
  have h10 : ΛQ c γ hc hγ0 Q 1 0 ≠ 0 :=
    TidyR5aRuleIIIStochastic.Inertia.in_Λ10_ne_zero c γ hc hγ0.le _ Q.K_det
  refine ⟨?_, ?_⟩
  · have hsub : lb - l1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h1b)
    have h1c : 1 + (ν - lb) / (lb - l1) ≠ 0 := by
      rw [show 1 + (ν - lb) / (lb - l1) = (ν - l1) / (lb - l1) by field_simp; ring]
      exact div_ne_zero (by linarith) hsub
    simp only [ΛIIIQ, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_ne
      (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, mul_zero, sub_zero]
    rw [show ΛQ c γ hc hγ0 Q 1 0 + (ν - lb) / (lb - l1) * ΛQ c γ hc hγ0 Q 1 0 =
      (1 + (ν - lb) / (lb - l1)) * ΛQ c γ hc hγ0 Q 1 0 by ring]
    exact mul_ne_zero h1c h10
  · have hα := alpha_ΛIIIQ c γ hc hγ0 hγ1 Q lb hF
    rw [InertiaSplit.alpha_fin_two] at hα
    have e : TidyR5aRuleIIIStochastic.Inertia.ruleIIIpoly c γ =
        1 - Polynomial.C (l1 + ν) * Polynomial.X + Polynomial.C (l1 * ν) * Polynomial.X ^ 2 := by
      simp only [TidyR5aRuleIIIStochastic.Inertia.ruleIIIpoly, Polynomial.C_add,
        Polynomial.C_mul]
      ring
    rw [e] at hα
    have := congrArg (fun p : Polynomial ℝ => p.coeff 2) hα
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow] at this
    norm_num at this
    linear_combination this

/-- Woodford (2003), Assumption 8.5, App. G.2, p. 719, for Rule III's `Λ'` from a quasi-split. -/
theorem h85IIIQ (hF : FactsQ c γ hc hγ0 Q lb) : TargetCriterion.Krylov.Assumption85b
    (ΛIIIQ c γ hc hγ0 Q lb) (inProblem c γ hc hγ0.le).sys.B2 :=
  (TidyR5aRuleIIIStochastic.Inertia.ruleIII_assumption85 c γ hc hγ0 hγ1
    (ΛIIIQ_facts c γ hc hγ0 hγ1 Q lb hF).1 (ΛIIIQ_facts c γ hc hγ0 hγ1 Q lb hF).2).2

/-- **Woodford (2003), Rule III (3.24) with conditional expectations: the optimal plan satisfies
Rule III's target criterion.** Along every bounded solution of (1.1) + (1.9) whose initial
multiplier comes from a history consistent with Rule III's `Λ'`, the criterion holds a.s. at every
`t ≥ t₀`, for every disturbance (the base (1.20) of `OptimalRulesMeasureForecast.m_eq119_120`,
modified by `ModifyM.m_eq120_modify`). -/
theorem m_criterionIIIQ (hF : FactsQ c γ hc hγ0 Q lb) {S : MeasExpectationSystem Ω} {cd : ℕ → Ω →
    Fin 2 → ℝ} {t0 D : ℕ}
    (hD1 : D + 1 ≤ t0) (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (ΛIIIQ c γ hc hγ0 Q lb) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) {Z0 : Ω → Unit → ℝ}
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} {φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ}
    (h : MFOCSystem S (inProblem c γ hc hγ0.le) cd t0 Z0 (Mh (t0 - 1)) y φ) :
    MCriterionIIIQ c γ hc hγ0 Q lb S D t0 qh vh y := by
  classical
  have ht0 : 1 ≤ t0 := by omega
  obtain ⟨hmin, h1b, hb, hν⟩ := mod_dataQ c γ hc hγ0 hγ1 Q lb hF
  have hyb := h.1.2.2.1
  have hya := h.1.2.2.2
  obtain ⟨hqk, hqb⟩ := OptimalRulesMeasureQuasiSplit.qmQ_known_bdd
    (P := inProblem c γ hc hγ0.le) (Q := Q) hyb hya
  set M : ℕ → Ω → Fin 2 → ℝ := splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) with hM
  have hMb : MBoundedV S M := by
    obtain ⟨K1, hK1⟩ := hMhb
    obtain ⟨K2, hK2⟩ := h.2.1
    refine ⟨max K1 K2, fun u => ?_⟩
    filter_upwards [hK1 u, hK2 (u + 1)] with ω a b i
    simp only [hM, splice]
    split_ifs
    · exact (a i).trans (le_max_left _ _)
    · exact (b (Sum.inr i)).trans (le_max_right _ _)
  have hMa : MAdaptedV S M := by
    intro u i
    simp only [hM, splice]
    split_ifs
    · exact hMhk u i
    · exact h.2.2.2.1 u i
  have hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ := fun r =>
    ((hMhk (t0 - 1) r).mono (S.𝓕.mono (Nat.sub_le t0 1))).aestronglyMeasurable
  have hrel : ModifyM.Rel120 S t0 (ΛQ c γ hc hγ0 Q)
      (OptimalRulesMeasureQuasiSplit.qmQ (inProblem c γ hc hγ0.le) Q S y) M := by
    intro t ht
    filter_upwards [OptimalRulesMeasureQuasiSplit.m_eq119_120Q (inProblem c γ hc hγ0.le)
      Q h hM0 ht,
      OptimalRulesMeasureQuasiSplit.qmQ_eq_qMQ (P := inProblem c γ hc hγ0.le)
        (Q := Q) hyb hya t, h.2.2.2.2.1] with ω e eq e0
    have hMt : M t ω = Mpart (φ (t + 1) ω) := by
      simp only [hM, splice, show ¬ t < t0 by omega, ↓reduceIte]
    have hMt1 : M (t - 1) ω = Mpart (φ t ω) := by
      by_cases hte : t = t0
      · subst hte
        simp only [hM, splice, show t - 1 < t by omega, ↓reduceIte]
        exact e0.symm
      · simp only [hM, splice, show ¬ t - 1 < t0 by omega, ↓reduceIte]
        rw [show t - 1 + 1 = t by omega]
    rw [hMt, hMt1, e.1, eq]
    rfl
  have hrel' := (ModifyM.m_eq120_modify hmin h1b hb hν hqb hqk hMb hMa).mp hrel
  obtain ⟨hB, hα⟩ := RealCase.degrees2 (ΛIIIQ c γ hc hγ0 Q lb) hD2
  have h119 : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, (inProblem c γ hc hγ0.le).sys.B2 ⬝ᵥ M t ω +
      vproc (inProblem c γ hc hγ0.le) y t ω = 0 := by
    intro t ht
    filter_upwards [OptimalRulesMeasureQuasiSplit.m_eq119_120Q (inProblem c γ hc hγ0.le)
      Q h hM0 ht] with ω e
    have hMt : M t ω = Mpart (φ (t + 1) ω) := by
      simp only [hM, splice, show ¬ t < t0 by omega, ↓reduceIte]
    rw [hMt]
    exact e.2
  exact ModifyM.crit_of_rel120 hD1 hB hα hhist (M := M)
    (fun u hu => by simp only [hM, splice, hu, ↓reduceIte]) hrel' h119

/-- Woodford (2003), Rule III (tool): the forcing `q'` of Rule III's criterion is essentially
bounded and adapted along a bounded adapted plan. -/
theorem qIIIQ_spec (hF : FactsQ c γ hc hγ0 Q lb) {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (Unit
    ⊕ Fin 2) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) (hya : MAdaptedV S y) :
    MBoundedV S (qIIIQ c γ hc hγ0 Q lb S y) ∧ MAdaptedV S (qIIIQ c γ hc hγ0 Q lb S y) := by
  obtain ⟨-, -, hb, -⟩ := mod_dataQ c γ hc hγ0 hγ1 Q lb hF
  obtain ⟨hqk, hqb⟩ := OptimalRulesMeasureQuasiSplit.qmQ_known_bdd
    (P := inProblem c γ hc hγ0.le) (Q := Q) hyb hya
  obtain ⟨-, hFa, hFb⟩ := ModifyM.FNm_spec (ΛQ c γ hc hγ0 Q -
    lam1 c.β γ c.κ c.σ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) hb hqb hqk
  set cc := (sumS c.β γ c.κ c.σ / 2 - lb) /
    (lb - lam1 c.β γ c.κ c.σ)
  refine ⟨?_, fun t i => ?_⟩
  · obtain ⟨K1, hK1⟩ := hqb
    obtain ⟨K2, hK2⟩ := hFb
    refine ⟨K1 + |cc| * K2, fun t => ?_⟩
    filter_upwards [hK1 t, hK2 t] with ω a b i
    simp only [qIIIQ, ModifyM.qModm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (a i) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (b i) (abs_nonneg _)
  · exact (hqk t i).sub ((hFa t i).const_mul cc)

/-- **Woodford (2003), Proposition 8.2 (the converse), p. 555, for Rule III, with conditional
expectations.** A bounded feasible plan that satisfies Rule III's target criterion a.s. at all
`t ≥ t₀` (consistent bounded history) solves (1.1) + (1.9) with `M_{t₀−1}` from the history: the
multipliers of (1.20) with `Λ'` are bounded (Assumption 8.5 for `Λ'`), the modification
(`ModifyM.m_eq120_modify`) turns them into multipliers of (1.20) for the base split, and the base
converse `OptimalRulesMeasureConverse.m_focSystem_of_criterion` applies. -/
theorem m_focSystem_of_criterionIIIQ (hF : FactsQ c γ hc hγ0 Q lb) {S : MeasExpectationSystem Ω}
    {t0 D : ℕ} (hD1 : D + 1 ≤ t0)
    (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (ΛIIIQ c γ hc hγ0 Q lb) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {cd : ℕ → Ω → Fin 2 → ℝ} {Z0 : Ω → Unit → ℝ}
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ}
    (hy : MFeasible S (inProblem c γ hc hγ0.le) cd t0 Z0 y)
    (hcrit : MCriterionIIIQ c γ hc hγ0 Q lb S D t0 qh vh y) :
    ∃ φ, MFOCSystem S (inProblem c γ hc hγ0.le) cd t0 Z0 (Mh (t0 - 1)) y φ := by
  classical
  obtain ⟨hmin, h1b, hb, hν⟩ := mod_dataQ c γ hc hγ0 hγ1 Q lb hF
  have hyb := hy.2.2.1
  have hya := hy.2.2.2
  obtain ⟨hqk, hqb⟩ := OptimalRulesMeasureQuasiSplit.qmQ_known_bdd
    (P := inProblem c γ hc hγ0.le) (Q := Q) hyb hya
  obtain ⟨hq3b, hq3a⟩ := qIIIQ_spec c γ hc hγ0 hγ1 Q lb hF hyb hya
  have hvb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vproc (inProblem c γ hc hγ0.le) y t ω| ≤ K := by
    obtain ⟨Ky, hKy⟩ := hyb
    obtain ⟨Kv, hKv⟩ := OptimalRulesMeasureConverse.vv_bound (inProblem c γ hc hγ0.le) Ky
    exact ⟨Kv, fun t => (hKy t).mono fun ω h => hKv _ h⟩
  obtain ⟨hB', hα'⟩ := RealCase.degrees2 (ΛIIIQ c γ hc hγ0 Q lb) hD2
  obtain ⟨hB, hα⟩ := RealCase.degrees2 (ΛQ c γ hc hγ0 Q) hD2
  obtain ⟨hMsb, hMsa, hrel3, h119⟩ := ModifyM.rel120_of_crit hD1 (h85IIIQ c γ hc hγ0 hγ1 Q lb hF)
    hB' hα' hhist hMhb hMhk hqhb hvhb hq3b hq3a hvb hcrit
  set Ms := Mseq (ΛIIIQ c γ hc hγ0 Q lb) Mh t0 (qIIIQ c γ hc hγ0 Q lb S y) with hMs
  have hrelb := (ModifyM.m_eq120_modify hmin h1b hb hν hqb hqk hMsb hMsa).mpr hrel3
  set qhB : ℕ → Ω → Fin 2 → ℝ := fun s ω => Ms s ω - ΛQ c γ hc hγ0 Q *ᵥ Ms (s - 1) ω
    with hqhB
  have hMsh : ∀ u, u < t0 → Ms u = Mh u := fun u hu => by
    simp only [hMs, Mseq, hu, ↓reduceIte]
  have hhistB : HistoryOKm S (ΛQ c γ hc hγ0 Q) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh
      qhB vh := by
    refine ⟨fun s _ hs2 => Eventually.of_forall fun ω => ?_, hhist.2⟩
    simp only [hqhB, hMsh s hs2, hMsh (s - 1) (by omega)]
    abel
  have hqhBb : MBoundedV S qhB := by
    obtain ⟨K, hK⟩ := hMsb
    obtain ⟨K2, hK2⟩ := GeneralFOC.exists_bound_mulVec (ΛQ c γ hc hγ0 Q) K
    refine ⟨K + K2, fun s => ?_⟩
    filter_upwards [hK s, hK (s - 1)] with ω a b i
    exact (abs_sub _ _).trans (add_le_add (a i) (hK2 _ b i))
  have hrelM : ModifyM.Rel120 S t0 (ΛQ c γ hc hγ0 Q)
      (OptimalRulesMeasureQuasiSplit.qMQ (inProblem c γ hc hγ0.le) Q S y) Ms := by
    intro t ht
    filter_upwards [hrelb t ht, OptimalRulesMeasureQuasiSplit.qmQ_eq_qMQ
      (P := inProblem c γ hc hγ0.le) (Q := Q) hyb hya t] with ω e1 e2
    rw [e1, e2]
  have h119' : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, (inProblem c γ hc hγ0.le).sys.B2 ⬝ᵥ Ms t ω +
      vproc (inProblem c γ hc hγ0.le) y t ω = 0 := by
    intro t ht
    filter_upwards [h119] with ω e
    have := e t (by omega)
    simpa [TargetCriterion.Recursion.splice, show ¬ t < t0 by omega] using this
  have hcritB : OptimalRulesMeasureQuasiSplit.MCriterionQ (inProblem c γ hc hγ0.le) Q S D t0 qhB
      vh y :=
    ModifyM.crit_of_rel120 hD1 hB hα hhistB hMsh hrelM h119'
  exact ⟨_, OptimalRulesMeasureQuasiSplit.m_focSystem_of_criterionQ (h85Q c γ hc hγ0 Q) hD1 hB
    hα hhistB hMhb hMhk hqhBb hvhb hy hcritB⟩

/-- **Woodford (2003), Proposition 8.2, p. 555, for Rule III (3.24), on every filtered probability
space and for every bounded adapted disturbance (any quasi-split with `FactsQ`).** Commitment to
Rule III's target criterion (a window of `D ≥ 2` lags and any consistent bounded history) determines
a bounded feasible plan, unique a.s., and it solves (1.1) + (1.9) — the optimal plan. -/
theorem m_prop82_IIIQ (hF : FactsQ c γ hc hγ0 Q lb) {S : MeasExpectationSystem Ω} (t0 : ℕ) {D : ℕ}
    (hD1 : D + 1 ≤ t0)
    (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (ΛIIIQ c γ hc hγ0 Q lb) (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {cd : ℕ → Ω → Fin 2 → ℝ}
    (hcb : MBoundedV S cd) (hca : MAdaptedV S cd) {Z0 : Ω → Unit → ℝ} (hZk : MKnownV S t0 Z0)
    (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S (inProblem c γ hc hγ0.le) cd t0 Z0 y ∧
      MCriterionIIIQ c γ hc hγ0 Q lb S D t0 qh vh y ∧
      (∀ y', MFeasible S (inProblem c γ hc hγ0.le) cd t0 Z0 y' →
        MCriterionIIIQ c γ hc hγ0 Q lb S D t0 qh vh y' → ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MFOCSystem S (inProblem c γ hc hγ0.le) cd t0 Z0 (Mh (t0 - 1)) y φ := by
  have hA81 := InertiaAssumption81.in_assumption81_perfectForesight c γ hc hγ0 hγ1 0
  have hMb : MBoundedRV S (Mh (t0 - 1)) := by
    obtain ⟨K, hK⟩ := hMhb
    exact ⟨K, hK (t0 - 1)⟩
  obtain ⟨y, φ, hsol⟩ := OptimalRulesMeasureGeneral.m_focSolvableMB_of_powDecay hA81 S t0
    (OptimalRulesMeasureStabilityModels.Inertia.in_powDecay c γ hc hγ0 hγ1) cd Z0 (Mh (t0 - 1))
    hcb hca hZk hZb hMb (hMhk (t0 - 1))
  refine ⟨y, hsol.1, m_criterionIIIQ c γ hc hγ0 hγ1 Q lb hF hD1 hD2 hhist hMhb hMhk hsol,
    fun y' hy' hc' t ht => ?_, φ, hsol⟩
  obtain ⟨φ', h'⟩ := m_focSystem_of_criterionIIIQ c γ hc hγ0 hγ1 Q lb hF hD1 hD2 hhist hMhb hMhk
      hqhb
    hvhb hy' hc'
  exact (OptimalRulesMeasureForecast.m_focUnique_of_pf hA81.unique S t0 cd Z0 (Mh (t0 - 1)) y' y
    φ' φ h' hsol t ht).1


end QuasiCase

/-! ### Rule III at every admissible calibration -/

namespace AllCases

open IRuleBasic (Calib)
open CubicRoots
open GeneralLinksInertia (inProblem)
open QuasiCase (ΛQ FactsQ ΛIIIQ MCriterionIIIQ)

variable (c : Calib) (γ : ℝ) (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)

include hγ1 in
/-- Woodford (2003), Propositions 8.1 and 8.3 and App. G.1: **at every admissible calibration
there is a quasi-split with the spectral data Rule III needs** — the Rule I split
(`RealCase.Dsp`, `λ_b = λ₂`) as a quasi-split when `S² ≥ 4P₂₃`, and the case-(ii) construction
`InertiaProp82Complex.inQ` (`λ_b` from `TidyR5aRuleIIIStochastic.Inertia.in_Λ_struct`) when
`S² < 4P₂₃`. -/
theorem exists_quasi_facts :
    ∃ (ιc : Type) (_ : Fintype ιc) (_ : DecidableEq ιc)
      (Q : Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β ιc)
      (lb : ℝ), FactsQ c γ hc hγ0 Q lb := by
  rcases le_or_gt 0 (discQ c.β γ c.κ c.σ) with hD | hD
  · obtain ⟨htr, hdet, h2, -, -⟩ := RealCase.Λb_facts c γ hc hγ0 hγ1 hD
    refine ⟨Unit, inferInstance, inferInstance,
      Prop81CaseII.quasiOfDeflating (RealCase.Dsp c γ hc hγ0 hγ1 hD), lam2r c.β γ c.κ c.σ, ?_⟩
    have e : ΛQ c γ hc hγ0 (Prop81CaseII.quasiOfDeflating (RealCase.Dsp c γ hc hγ0 hγ1 hD)) =
        RealCase.Λb c γ hc hγ0 hγ1 hD :=
      OptimalRulesMeasureQuasiSplit.Λmat_quasiOfDeflating _
    refine ⟨by rw [e]; exact htr, by rw [e]; exact hdet, ?_⟩
    rw [abs_of_pos (by linarith)]
    exact h2
  · obtain ⟨lb, htr, hdet, hb⟩ := TidyR5aRuleIIIStochastic.Inertia.in_Λ_struct c γ hc hγ0 hγ1
      hD.ne (Prop81CaseII.prop81II _ (InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hD)
        perfectForesight 0)
    exact ⟨Option Unit, inferInstance, inferInstance,
      InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hD, lb, htr, hdet, hb⟩

include hγ1 in
/-- **Woodford (2003), Rule III (3.24), p. 595, and Proposition 8.2, p. 555, with conditional
expectations, at every admissible calibration** (`0 < γ ≤ 1`: three real roots, the double root,
or a complex pair), on every filtered probability space: there is a `Λ'` with Rule III's lag
polynomial `det(I − Λ'L) = (1 − λ₁L)(1 − ½(λ₂ + λ₃)L)` such that, for every window `D ≥ 2`, every
consistent bounded history and every bounded adapted disturbance, commitment to the target
criterion built from `Λ'` determines a bounded feasible plan, unique a.s., and it solves
(1.1) + (1.9) — the optimal plan. -/
theorem m_prop82_III_all :
    ∃ (ιc : Type) (_ : Fintype ιc) (_ : DecidableEq ιc)
      (Q : Prop81CaseII.QuasiSplit (inProblem c γ hc hγ0.le).sys (inProblem c γ hc hγ0.le).β ιc)
      (lb : ℝ), Adjugate.alpha (ΛIIIQ c γ hc hγ0 Q lb) =
        TidyR5aRuleIIIStochastic.Inertia.ruleIIIpoly c γ ∧
      ∀ (S : MeasExpectationSystem Ω) (t0 D : ℕ), D + 1 ≤ t0 → 2 ≤ D →
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
          ∃ φ, MFOCSystem S (inProblem c γ hc hγ0.le) e t0 Z0 (Mh (t0 - 1)) y φ := by
  obtain ⟨ιc, i1, i2, Q, lb, hF⟩ := exists_quasi_facts c γ hc hγ0 hγ1
  exact ⟨ιc, i1, i2, Q, lb, QuasiCase.alpha_ΛIIIQ c γ hc hγ0 hγ1 Q lb hF,
    fun S t0 D hD1 hD2 Mh qh vh hhist hMhb hMhk hqhb hvhb e heb hea Z0 hZk hZb =>
      QuasiCase.m_prop82_IIIQ c γ hc hγ0 hγ1 Q lb hF t0 hD1 hD2 hhist hMhb hMhk hqhb hvhb heb
        hea hZk hZb⟩

end AllCases

end Woodford.OptimalPolicyRules.TidyR5aRuleIIIMeasure
