/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureMarkov

/-!
# Conditional forecasts of the first-order system for an arbitrary disturbance

Woodford (2003), *Interest and Prices*, Chapter 8, Sections 1.1–1.4 (pp. 536–555): the system
(1.1) + (1.9), Assumption 8.1 (p. 541) and the target criterion (1.23) (p. 554), on a probability
space with Mathlib's conditional expectation, for an **arbitrary** disturbance process `c_t`
(not only the VAR of `OptimalRulesMeasureMarkov`).

## Main results

* `fc_focSystem`: for every bounded solution `(y, φ)` of (1.1) + (1.9) and every `t ≥ t₀`, almost
  every `ω` gives a bounded **perfect-foresight** solution `k ↦ (E_t y_{t+k}, E_t φ_{t+k})(ω)` with
  forcing `k ↦ E_t c_{t+k}(ω)` (`cfc`), from the state `(Z_t, E_t M_{t−1})(ω)`. No hypothesis on
  the disturbance is needed: the structural equations make `c_t` integrable
  (`integrable_dist`).
* `m_focUnique_of_pf`: **the uniqueness half of Assumption 8.1 holds on every probability space,
  at every `t₀`, for every disturbance, as soon as it holds under perfect foresight**
  (`GeneralFOC.LQ.FOCUnique P perfectForesight 0`). The two solutions have the same forecast
  paths at every date (they solve the same deterministic system from the same state), by
  induction on the state `(Z_t, E_t M_{t−1})`.
* `m_eq119_120`, `MCriterion`, `m_criterion`: along every bounded solution, for every
  disturbance, `M_t = Λ M_{t−1} + q_t` (1.20) and `B₂'M_t + v_t = 0` (1.19) hold a.s.
  (`q_t` = `OptimalRulesMeasureMarkov.qM`, the operator `Q(L⁻¹)` of Proposition 8.1 on the
  conditional forecasts), and so does the target criterion (1.23) — generalising
  `OptimalRulesMeasureMarkov.eq119_120_var` and `criterion_var` from VAR disturbances to all.
* `fc_unitSystem`: on the one-point probability space the forecast path is the solution itself
  (link with the core perfect-foresight system).
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureForecast

open MeasureTheory Filter Topology Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure OptimalRulesMeasure OptimalRulesMeasureMarkov

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-! ### The forecast path of the disturbance -/

/-- Woodford (2003), p. 537 and fn 4 (the disturbance enters only through `c_t = C₂ s_t`): the
date-`t` forecast path `k ↦ E_t c_{t+k}(ω)` of the disturbance, as a perfect-foresight
forcing. -/
noncomputable def cfc (S : MeasExpectationSystem Ω) (c : ℕ → Ω → ιz → ℝ) (t : ℕ) (ω : Ω) :
    ℕ → Unit → ιz → ℝ :=
  fun k _ => EVm S t (c (t + k)) ω

omit [MeasurableSpace Ω] [Fintype ιZ] [DecidableEq ιZ] in
/-- Woodford (2003), p. 537 (tool): the disturbance `[0; c_t]` of (1.1) as a matrix,
`[0; I] c_t`. -/
theorem liftDist_one (c : ℕ → Ω → ιz → ℝ) (t : ℕ) (ω : Ω) :
    liftDist (ιZ := ιZ) c t ω = Matrix.fromRows (0 : Matrix ιZ ιz ℝ) 1 *ᵥ c t ω := by
  rw [fromRows_mulVec, zero_mulVec, one_mulVec]
  rfl

omit [Fintype ιτ] [DecidableEq ιZ] in
/-- Woodford (2003), eq. (1.1), p. 537 (tool): along a bounded adapted plan satisfying the
expectational rows of (1.1) from `t₀` on, the disturbance `c_s` (`s ≥ t₀`) is integrable — it is
a.s. a linear function of `E_s z_{s+1}` and `y_s`. -/
theorem integrable_dist {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hs : MStructural S P c t0 y) (hyb : MBoundedV S y) (hya : MAdaptedV S y) {s : ℕ}
    (hs0 : t0 ≤ s) (r : ιz) : Integrable (fun ω => c s ω r) S.μ := by
  have hyi := integrable_of_adapted hyb hya
  have h1 : Integrable (fun ω => (P.sys.Et *ᵥ EVm S s (fun ω' => zpart (y (s + 1) ω')) ω) r)
      S.μ := integrable_mulVec P.sys.Et (fun j => S.integrable_E s _) r
  have h2 : Integrable (fun ω => (P.sys.A21 *ᵥ Zpart (y s ω)) r) S.μ :=
    integrable_mulVec P.sys.A21 (fun j => hyi s _) r
  have h3 : Integrable (fun ω => (P.sys.A22 *ᵥ zpart (y s ω)) r) S.μ :=
    integrable_mulVec P.sys.A22 (fun j => hyi s _) r
  have h4 : Integrable (fun ω => ipart (y s ω) * P.sys.B2 r) S.μ :=
    (hyi s (Sum.inr ())).mul_const _
  refine (((h1.sub h2).sub h3).sub h4).congr ?_
  filter_upwards [(hs s hs0).2] with ω e
  simp only [Pi.sub_apply]
  rw [e]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Conditional forecasts of a solution solve the perfect-foresight system -/

/-- Woodford (2003), pp. 538–541: **the conditional forecast path of a solution is a
perfect-foresight solution, for every disturbance.** If `(y, φ)` is a bounded solution of
(1.1) + (1.9) on a probability space, then for every `t ≥ t₀` and almost every `ω` the paths
`k ↦ E_t y_{t+k}(ω)`, `k ↦ E_t φ_{t+k}(ω)` solve (1.1) + (1.9) under perfect foresight with
forcing `k ↦ E_t c_{t+k}(ω)` from `Z = Z_t(ω)`, `M = E_t M_{t−1}(ω)` (linearity, the law of
iterated expectations). -/
theorem fc_focSystem (P : LQProblem ιZ ιz ιτ) {S : MeasExpectationSystem Ω}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P c t0 Z0 M0 y φ) {t : ℕ} (ht : t0 ≤ t) :
    ∀ᵐ ω ∂S.μ, FOCSystem P perfectForesight (cfc S c t ω) 0 (fun _ => Zpart (y t ω))
      (fun _ => Mpart (EVm S t (φ t) ω)) (fun k _ => EVm S t (y (t + k)) ω)
      (fun k _ => EVm S t (φ (t + k)) ω) := by
  have hy := h.1
  obtain ⟨⟨hst, -, hyb, hya⟩, hφb, hφm, -, -, hfoc⟩ := h
  have hyi := integrable_of_adapted hyb hya
  have hci : ∀ k r, Integrable (fun ω => c (t + k) ω r) S.μ := fun k r =>
    integrable_dist hst hyb hya (le_trans ht (Nat.le_add_right t k)) r
  obtain ⟨Ky, hKy⟩ := hyb
  obtain ⟨Kφ, hKφ⟩ := hφb
  have hφi : ∀ t i, Integrable (fun ω => φ t ω i) S.μ := fun t i =>
    integrable_of_bound (hφm t i) ((hKφ t).mono fun ω h => h i)
  have hEyi : ∀ s' t' i, Integrable (fun ω => EVm S s' (y t') ω i) S.μ := fun _ _ _ =>
    S.integrable_E _ _
  have hEφi : ∀ s' t' i, Integrable (fun ω => EVm S s' (φ t') ω i) S.μ := fun _ _ _ =>
    S.integrable_E _ _
  -- (1.1) in abstract form along the forecasts
  have hcons : ∀ k, ∀ᵐ ω ∂S.μ, P.sys.Itil *ᵥ EVm S t (y (t + k + 1)) ω =
      P.sys.Atil *ᵥ EVm S t (y (t + k)) ω +
        Matrix.fromRows (0 : Matrix ιZ ιz ℝ) 1 *ᵥ EVm S t (c (t + k)) ω := by
    intro k
    have hc := m_constraints P hy (le_trans ht (Nat.le_add_right t k))
    have hz : ∀ᵐ ω ∂S.μ, P.sys.Itil *ᵥ EVm S (t + k) (y (t + k + 1)) ω +
        (-P.sys.Atil) *ᵥ y (t + k) ω +
          (-Matrix.fromRows (0 : Matrix ιZ ιz ℝ) 1) *ᵥ c (t + k) ω + 0 = 0 := by
      filter_upwards [hc] with ω e
      rw [e, liftDist_one, neg_mulVec, neg_mulVec]
      abel
    filter_upwards [EVm_congr S t hz, EVm_affine3 S t P.sys.Itil (-P.sys.Atil)
      (-Matrix.fromRows (0 : Matrix ιZ ιz ℝ) 1) 0 (hEyi (t + k) (t + k + 1)) (hyi (t + k))
      (hci k), EVm_tower S (Nat.le_add_right t k) (y (t + k + 1))] with ω e1 e2 e3
    rw [EVm_const] at e1
    beta_reduce at e1
    have key := e2.symm.trans e1
    rw [e3, neg_mulVec, neg_mulVec, add_zero] at key
    rw [← sub_eq_zero, ← key]
    abel
  -- (1.9) along the forecasts
  have hfocE : ∀ k, ∀ᵐ ω ∂S.μ, P.sys.Atilᵀ *ᵥ EVm S t (φ (t + k + 1)) ω +
      P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + k)) ω - P.τstar)) -
        P.β⁻¹ • (P.sys.Itilᵀ *ᵥ EVm S t (φ (t + k)) ω) = 0 := by
    intro k
    have hz : ∀ᵐ ω ∂S.μ, P.sys.Atilᵀ *ᵥ EVm S (t + k) (φ (t + k + 1)) ω +
        (P.Tᵀ * P.W * P.T) *ᵥ y (t + k) ω + (-(P.β⁻¹ • P.sys.Itilᵀ)) *ᵥ φ (t + k) ω +
          -(P.Tᵀ *ᵥ (P.W *ᵥ P.τstar)) = 0 := by
      filter_upwards [hfoc (t + k) (le_trans ht (Nat.le_add_right t k))] with ω e
      rw [← foc_affine]
      exact e
    filter_upwards [EVm_congr S t hz, EVm_affine3 S t P.sys.Atilᵀ (P.Tᵀ * P.W * P.T)
      (-(P.β⁻¹ • P.sys.Itilᵀ)) (-(P.Tᵀ *ᵥ (P.W *ᵥ P.τstar))) (hEφi (t + k) (t + k + 1))
      (hyi (t + k)) (hφi (t + k)), EVm_tower S (Nat.le_add_right t k) (φ (t + k + 1))]
      with ω e1 e2 e3
    rw [EVm_const] at e1
    beta_reduce at e1
    have key := e2.symm.trans e1
    rw [e3, ← foc_affine] at key
    exact key
  have hZi : EVm S t (y t) = y t := EVm_of_known S (hya t) (hyi t)
  -- bounds
  have hyB : ∀ᵐ ω ∂S.μ, ∀ k i, |EVm S t (y (t + k)) ω i| ≤ Ky :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun i => S.abs_E_le ((hKy (t + k)).mono fun ω h => h i) t
  have hφB : ∀ᵐ ω ∂S.μ, ∀ k i, |EVm S t (φ (t + k)) ω i| ≤ Kφ :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun i => S.abs_E_le ((hKφ (t + k)).mono fun ω h => h i) t
  filter_upwards [ae_all_iff.2 hcons, ae_all_iff.2 hfocE, hyB, hφB] with ω e1 e2 e4 e5
  have hL : ∀ k, Matrix.fromRows (0 : Matrix ιZ ιz ℝ) 1 *ᵥ EVm S t (c (t + k)) ω =
      liftDist (ιZ := ιZ) (cfc S c t ω) k () := by
    intro k
    rw [fromRows_mulVec, zero_mulVec, one_mulVec]
    rfl
  refine ⟨⟨(structural_iff P.sys perfectForesight _ 0 _).mpr
    fun k _ u => ⟨fun r => ?_, fun r => ?_⟩, fun u => ?_, ⟨Ky, fun k u i => e4 k i⟩,
    fun _ _ => rfl⟩, ⟨Kφ, fun k u i => e5 k i⟩, fun _ _ => rfl, fun u => rfl, fun k _ u => ?_⟩
  · have := congrFun (e1 k) (Sum.inl r)
    rw [hL k] at this
    exact this
  · have := congrFun (e1 k) (Sum.inr r)
    rw [hL k] at this
    exact this
  · change Zpart (EVm S t (y t) ω) = Zpart (y t ω)
    rw [hZi]
  · exact e2 k

/-! ### Uniqueness on every probability space from uniqueness under perfect foresight -/

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): a multiplier `M_t` known at `t` is its own forecast at every
later date `s ≥ t` (exactly). -/
theorem mpart_EVm_of_le {S : MeasExpectationSystem Ω} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hb : MBoundedV S φ) (hm : MAEMeasV S φ) (hM : MMultMeas S φ) {t s : ℕ} (hts : t ≤ s)
    (ω : Ω) : Mpart (EVm S s (φ (t + 1)) ω) = Mpart (φ (t + 1) ω) := by
  obtain ⟨K, hK⟩ := hb
  funext r
  exact congrFun (S.E_of_stronglyMeasurable ((hM t r).mono (S.𝓕.mono hts))
    (integrable_of_bound (hm (t + 1) _) ((hK (t + 1)).mono fun ω h => h _))) ω

/-- Woodford (2003), eq. (1.9), p. 541 (tool): the multipliers `ξ_t` on the predetermined rows are
pinned down by `E_t φ_{t+1}` and `y_t` (the `Z`-rows of (1.9) read `β⁻¹ ξ_t = …`). -/
theorem ξ_eq_of_foc (P : LQProblem ιZ ιz ιτ) {v : (ιZ ⊕ ιz) ⊕ Unit → ℝ} {e q q' : ιZ ⊕ ιz → ℝ}
    (h : P.sys.Atilᵀ *ᵥ e + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) -
      P.β⁻¹ • (P.sys.Itilᵀ *ᵥ q) = 0)
    (h' : P.sys.Atilᵀ *ᵥ e + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) -
      P.β⁻¹ • (P.sys.Itilᵀ *ᵥ q') = 0) (j : ιZ) : q (Sum.inl j) = q' (Sum.inl j) := by
  have hd : P.β⁻¹ • (P.sys.Itilᵀ *ᵥ q) = P.β⁻¹ • (P.sys.Itilᵀ *ᵥ q') :=
    sub_right_injective (h.trans h'.symm)
  have hd' : P.sys.Itilᵀ *ᵥ q = P.sys.Itilᵀ *ᵥ q' :=
    smul_right_injective _ (inv_ne_zero P.β_pos.ne') hd
  have := congrFun hd' (Sum.inl (Sum.inl j))
  rwa [Itil_transpose_inl, Itil_transpose_inl] at this

/-- Woodford (2003), **Assumption 8.1 (uniqueness)**, p. 541, **on every probability space from
its perfect-foresight form**: if bounded solutions of (1.1) + (1.9) are unique under perfect
foresight (`GeneralFOC.LQ.FOCUnique P perfectForesight 0`, e.g. from the core Assumption 8.1),
then on every filtered probability space, at every `t₀`, for every disturbance and all initial
conditions, two bounded solutions agree a.s. at every date `t ≥ t₀`. No VAR structure, no
stability hypothesis and no measurability of `M_{t₀−1}` are needed. -/
theorem m_focUnique_of_pf {P : LQProblem ιZ ιz ιτ} (hU : FOCUnique P perfectForesight 0)
    (S : MeasExpectationSystem Ω) (t0 : ℕ) : MFOCUnique S P t0 := by
  intro c Z0 M0 y y' φ φ' h h'
  have hyi := integrable_of_adapted h.1.2.2.1 h.1.2.2.2
  have hyi' := integrable_of_adapted h'.1.2.2.1 h'.1.2.2.2
  -- forecasts agree once the states agree
  have hfc : ∀ t, t0 ≤ t → (∀ᵐ ω ∂S.μ, Zpart (y t ω) = Zpart (y' t ω) ∧
      Mpart (EVm S t (φ t) ω) = Mpart (EVm S t (φ' t) ω)) →
      ∀ᵐ ω ∂S.μ, ∀ k, EVm S t (y (t + k)) ω = EVm S t (y' (t + k)) ω ∧
        EVm S t (φ (t + k)) ω = EVm S t (φ' (t + k)) ω := by
    intro t ht hs
    filter_upwards [hs, fc_focSystem P h ht, fc_focSystem P h' ht] with ω e f f' k
    rw [← e.1, ← e.2] at f'
    have := hU _ _ _ _ _ _ _ f f' k (Nat.zero_le k)
    exact ⟨congrFun this.1 (), congrFun this.2 ()⟩
  -- the states agree
  have hst : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, Zpart (y t ω) = Zpart (y' t ω) ∧
      Mpart (EVm S t (φ t) ω) = Mpart (EVm S t (φ' t) ω) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      have hc : ∀ r, S.E t0 (fun ω => φ t0 ω (Sum.inr r)) =ᵐ[S.μ]
          S.E t0 (fun ω => φ' t0 ω (Sum.inr r)) := fun r => S.E_congr (by
        filter_upwards [h.2.2.2.2.1, h'.2.2.2.2.1] with ω e1 e2
        exact (congrFun e1 r).trans (congrFun e2 r).symm) t0
      filter_upwards [h.1.2.1, h'.1.2.1, ae_all_iff.2 hc] with ω e1 e2 e3
      exact ⟨e1.trans e2.symm, funext fun r => e3 r⟩
    | succ t ht ih =>
      filter_upwards [hfc t ht ih, (h.1.1 t ht).1, (h'.1.1 t ht).1] with ω e z z'
      have hy0 : y t ω = y' t ω := by
        have := (e 0).1
        rwa [Nat.add_zero, EVm_of_known S (h.1.2.2.2 t) (hyi t),
          EVm_of_known S (h'.1.2.2.2 t) (hyi' t)] at this
      refine ⟨by rw [z, z', hy0], ?_⟩
      rw [mpart_EVm_of_le h.2.1 h.2.2.1 h.2.2.2.1 (Nat.le_succ t),
        mpart_EVm_of_le h'.2.1 h'.2.2.1 h'.2.2.2.1 (Nat.le_succ t),
        ← mpart_EVm_of_le h.2.1 h.2.2.1 h.2.2.2.1 le_rfl,
        ← mpart_EVm_of_le h'.2.1 h'.2.2.1 h'.2.2.2.1 le_rfl, (e 1).2]
  intro t ht
  have hE := hfc t ht (hst t ht)
  refine ⟨?_, ?_⟩
  · filter_upwards [hE] with ω e
    have := (e 0).1
    rwa [Nat.add_zero, EVm_of_known S (h.1.2.2.2 t) (hyi t),
      EVm_of_known S (h'.1.2.2.2 t) (hyi' t)] at this
  · have hM : ∀ᵐ ω ∂S.μ, Mpart (φ t ω) = Mpart (φ' t ω) := by
      rcases Nat.eq_or_lt_of_le ht with h0 | h0
      · subst h0
        filter_upwards [h.2.2.2.2.1, h'.2.2.2.2.1] with ω e1 e2
        rw [e1, e2]
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        filter_upwards [hst (s + 1) ht] with ω e
        rw [← mpart_EVm_of_le h.2.1 h.2.2.1 h.2.2.2.1 (Nat.le_succ s),
          ← mpart_EVm_of_le h'.2.1 h'.2.2.1 h'.2.2.2.1 (Nat.le_succ s), e.2]
    filter_upwards [hE, hM, h.2.2.2.2.2 t ht, h'.2.2.2.2.2 t ht] with ω e eM f f'
    have hy0 : y t ω = y' t ω := by
      have := (e 0).1
      rwa [Nat.add_zero, EVm_of_known S (h.1.2.2.2 t) (hyi t),
        EVm_of_known S (h'.1.2.2.2 t) (hyi' t)] at this
    rw [(e 1).2, hy0] at f
    funext i
    rcases i with j | r
    · exact ξ_eq_of_foc P f f' j
    · exact congrFun eM r

/-! ### (1.19), (1.20) and the target criterion (1.23) along every solution -/

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): at every `t ≥ t₀` the lagged multiplier `M_{t−1}` is a.s. its
own forecast, given that the initial `M_{t₀−1}` is a.e. known at `t₀`. -/
theorem mpart_EVm_self [Countable ιz] {S : MeasExpectationSystem Ω} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hb : MBoundedV S φ) (hm : MAEMeasV S φ) (hM : MMultMeas S φ) {t0 : ℕ}
    {M0 : Ω → ιz → ℝ} (hM0e : ∀ᵐ ω ∂S.μ, Mpart (φ t0 ω) = M0 ω)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => M0 ω r) S.μ) {t : ℕ} (ht : t0 ≤ t) :
    ∀ᵐ ω ∂S.μ, Mpart (EVm S t (φ t) ω) = Mpart (φ t ω) := by
  rcases Nat.eq_or_lt_of_le ht with h0 | h0
  · subst h0
    obtain ⟨K, hK⟩ := hb
    have hc : ∀ r, S.E t0 (fun ω => φ t0 ω (Sum.inr r)) =ᵐ[S.μ] fun ω => φ t0 ω (Sum.inr r) :=
      fun r => S.E_of_aestronglyMeasurable
        ((hM0 r).congr (hM0e.mono fun ω e => (congrFun e r).symm))
        (integrable_of_bound (hm t0 _) ((hK t0).mono fun ω h => h _))
    filter_upwards [ae_all_iff.2 hc] with ω e
    funext r
    exact e r
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact Eventually.of_forall fun ω => mpart_EVm_of_le hb hm hM (Nat.le_succ s) ω

/-- Woodford (2003), **(1.20) and (1.19)**, p. 553, with genuine conditional expectations, **for
every disturbance**: along every bounded solution of (1.1) + (1.9) whose initial multiplier is
a.e. known at `t₀`, a.s. for all `t ≥ t₀`, `M_t = Λ M_{t−1} + q_t` (`Λ = β⁻¹K⁻¹Ẽ'` of
Proposition 8.1, `q_t` of (1.25) on the conditional forecasts, `OptimalRulesMeasureMarkov.qM`)
and `B₂'M_t + v_t = 0`. -/
theorem m_eq119_120 (P : LQProblem ιZ ιz ιτ) (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    {S : MeasExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ}
    {M0 : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P c t0 Z0 M0 y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => M0 ω r) S.μ) {t : ℕ} (ht : t0 ≤ t) :
    ∀ᵐ ω ∂S.μ, Mpart (φ (t + 1) ω) =
        PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ Mpart (φ t ω) + qM P Dsp S y t ω ∧
      P.sys.B2 ⬝ᵥ Mpart (φ (t + 1) ω) + TargetCriterion.Prop81.vproc P y t ω = 0 := by
  classical
  have hyi := integrable_of_adapted h.1.2.2.1 h.1.2.2.2
  have hMk : ∀ ω, Mpart (EVm S t (φ (t + 1)) ω) = Mpart (φ (t + 1) ω) :=
    mpart_EVm_of_le h.2.1 h.2.2.1 h.2.2.2.1 le_rfl
  have hy0 : EVm S t (y t) = y t := EVm_of_known S (h.1.2.2.2 t) (hyi t)
  filter_upwards [fc_focSystem P h ht,
    mpart_EVm_self h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 hM0 ht] with ω hω hMs
  obtain ⟨⟨-, -, hyb, -⟩, hφb, hmm, hM, hfoc⟩ := hω
  have h118 : TargetCriterion.Prop81.Eq118 P perfectForesight 0
      (fun k _ => EVm S t (y (t + k)) ω) (fun k _ => EVm S t (φ (t + k)) ω) := by
    intro k _ u
    have := hfoc k (Nat.zero_le k) u
    exact ((foc_iff_split P hmm (fun k _ => EVm S t (y (t + k)) ω) k u).mp this).1
  have h119 := ((foc_iff_split P hmm (fun k _ => EVm S t (y (t + k)) ω) 0 ()).mp
    (hfoc 0 le_rfl ())).2
  have heq := ((Prop81General.prop81 P Dsp perfectForesight 0).equiv _ _ hyb (fun _ _ => rfl)
    hφb (fun _ _ _ => rfl)).mp h118
  have h120 := heq.1 0 le_rfl ()
  change Mpart (EVm S t (φ (t + 1)) ω) = PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ
    Mpart (EVm S t (φ (t + 0)) ω) + qM P Dsp S y t ω at h120
  have hM' : Mpart (EVm S t (φ (t + 0)) ω) = Mpart (φ t ω) := hMs
  rw [hMk, hM'] at h120
  refine ⟨h120, ?_⟩
  change P.sys.B2 ⬝ᵥ Mpart (EVm S t (φ (t + 1)) ω) +
    P.Ti ⬝ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + 0)) ω - P.τstar)) = 0 at h119
  have hy0' : EVm S t (y (t + 0)) = y t := hy0
  rw [hMk, hy0'] at h119
  exact h119

/-- Woodford (2003), eq. (1.23), p. 554, and fn 14, with genuine conditional expectations:
**commitment to the target criterion** at all `t ≥ t₀`, a.s. —
`α(L) v_t + B₂' B(L) q_t = 0` with `α = det(I − ΛL)`, `B = adj(I − ΛL)` for the `Λ` of
Proposition 8.1 (deflating split `Dsp`), `v_t = T_i'W(τ_t − τ*)` (1.26), `q_t` of (1.25) on the
conditional forecasts (`qM`), and the historical `q`, `v` before `t₀`. -/
def MCriterion (P : LQProblem ιZ ιz ιτ) (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    (S : MeasExpectationSystem Ω) (D t0 : ℕ) (qh : ℕ → Ω → ιz → ℝ) (vh : ℕ → Ω → ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, TargetCriterion.Crit.crit
    (Adjugate.alpha (PencilSplit.Λmat P.sys P.β Dsp.J))
    (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β Dsp.J)) D P.sys.B2
    (TargetCriterion.Recursion.splice t0 vh (TargetCriterion.Prop81.vproc P y))
    (TargetCriterion.Recursion.splice t0 qh (qM P Dsp S y)) t ω = 0

/-- Woodford (2003), (1.20) and (1.19) for the spliced processes (history before `t₀`, the
solution from `t₀` on), a.s. for all dates `s ≥ t₀ − D`, **for every disturbance**. -/
theorem m_spliced_119_120 (P : LQProblem ιZ ιz ιτ) (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    {S : MeasExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ} {t0 D : ℕ} (ht0 : 1 ≤ t0)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P c t0 Z0 (Mh (t0 - 1)) y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ) :
    ∀ᵐ ω ∂S.μ, ∀ u, t0 - D ≤ u →
      TargetCriterion.Recursion.splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) u ω =
        PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ
          TargetCriterion.Recursion.splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) (u - 1) ω +
          TargetCriterion.Recursion.splice t0 qh (qM P Dsp S y) u ω ∧
      P.sys.B2 ⬝ᵥ TargetCriterion.Recursion.splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) u ω +
        TargetCriterion.Recursion.splice t0 vh (TargetCriterion.Prop81.vproc P y) u ω = 0 := by
  classical
  have hsol : ∀ u, ∀ᵐ ω ∂S.μ, t0 ≤ u → Mpart (φ (u + 1) ω) =
        PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ Mpart (φ u ω) + qM P Dsp S y u ω ∧
      P.sys.B2 ⬝ᵥ Mpart (φ (u + 1) ω) + TargetCriterion.Prop81.vproc P y u ω = 0 := by
    intro u
    by_cases hu : t0 ≤ u
    · filter_upwards [m_eq119_120 P Dsp h hM0 hu] with ω e _
      exact e
    · exact Eventually.of_forall fun _ h' => absurd h' hu
  have hh1 : ∀ u, ∀ᵐ ω ∂S.μ, t0 - D ≤ u → u < t0 →
      Mh u ω = PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ Mh (u - 1) ω + qh u ω := by
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
  unfold TargetCriterion.Recursion.splice
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

/-- Woodford (2003), **(1.23)**, p. 554, and fn 14, with genuine conditional expectations, **for
every disturbance**: along every bounded solution of (1.1) + (1.9) whose initial multiplier
comes from a consistent history, the target criterion holds a.s. at every `t ≥ t₀`
(generalising `OptimalRulesMeasureMarkov.criterion_var` from VAR disturbances to all). -/
theorem m_criterion (P : LQProblem ιZ ιz ιτ) (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    {S : MeasExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ} {t0 D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β Dsp.J) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β Dsp.J)).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P c t0 Z0 (Mh (t0 - 1)) y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ) :
    MCriterion P Dsp S D t0 qh vh y := by
  classical
  intro t ht
  filter_upwards [m_spliced_119_120 P Dsp (by omega) hhist h hM0] with ω e
  exact TargetCriterion.Crit.eq123_of_eq119_eq120 (Adjugate.eq122 _) hB hα P.sys.B2
    (M := fun u (_ : Unit) =>
      TargetCriterion.Recursion.splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) u ω)
    (q := fun u (_ : Unit) => TargetCriterion.Recursion.splice t0 qh (qM P Dsp S y) u ω)
    (v := fun u (_ : Unit) =>
      TargetCriterion.Recursion.splice t0 vh (TargetCriterion.Prop81.vproc P y) u ω)
    (t0 := t0 - D) (fun u hu _ => (e u hu).2) (fun u hu _ => (e u hu).1) t (by omega) ()

/-! ### Link with perfect foresight -/

/-- Woodford (2003), p. 541 (link): on the one-point probability space (perfect foresight,
`OptimalRulesMeasure.Bridge.unitSystem`) the forecast path of a solution is the solution itself,
`E_t y_{t+k} = y_{t+k}`. -/
theorem fc_unitSystem {ι : Type*} (x : ℕ → Unit → ι → ℝ) (t k : ℕ) (u : Unit) :
    EVm Bridge.unitSystem t (x (t + k)) u = x (t + k) u := by
  funext i
  have hm : StronglyMeasurable[Bridge.unitSystem.𝓕 t] (fun ω => x (t + k) ω i) :=
    stronglyMeasurable_const' fun a b => by rcases a; rcases b; rfl
  have hi : Integrable (fun ω => x (t + k) ω i) Bridge.unitSystem.μ := by
    have : (fun ω => x (t + k) ω i) = fun _ => x (t + k) () i := by
      funext ω
      rcases ω
      rfl
    rw [this]
    exact integrable_const _
  exact congrFun (Bridge.unitSystem.E_of_stronglyMeasurable hm hi) u

end Woodford.OptimalPolicyRules.OptimalRulesMeasureForecast
