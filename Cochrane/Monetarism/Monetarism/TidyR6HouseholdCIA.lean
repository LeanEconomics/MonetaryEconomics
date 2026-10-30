/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6HouseholdSuff
import Monetarism.CashInAdvanceMeasure

/-!
# The cash-in-advance household without regularity hypotheses

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.5.1–19.5.2,
pp. 447–451, eqs. (19.24)–(19.33), on a probability space (`CashInAdvanceMeasure`). The earlier
derivation of the Euler equation (`CashInAdvanceMeasure.euler_step`,
`CashInAdvanceMeasure.multiplier_const`) assumed regular prices, nonnegative nominal rates
`Q_t ≤ 1`, bounded consumption, overnight money bounded and bounded away from zero, and a utility
smooth on all of `ℝ`; sufficiency (`CashInAdvanceMeasure.optimal_of_foc`) assumed a binding cash
constraint. Here the utility `u(c)` need only be `C¹` on an open set `I` of consumption levels
(e.g. `I = (0, ∞)`), with the plan in `I`.

## Main results

* `cia_multiplier`: at an optimum, with only `PriceWeak` prices, there is one constant `λ` with
  `βᵗu'(c_t) = λΛ_tw_t` almost surely **wherever overnight money is positive**
  (`w_t = 1 + (1/V − 1)ι_t`); no bound on consumption, money or prices, and no `Q_t ≤ 1`.
* `cia_iota_nonneg`: if `u' > 0` at the plan, then `ι_t ≥ 0`, i.e. `Q_t ≤ 1`, almost surely at
  every date: nonnegative nominal rates are a consequence of optimality, not an assumption
  (otherwise money would be a free lunch); then `w_t ≥ min(1, 1/V) > 0` (`cia_wedge_pos`).
* `cia_optimal_of_kkt`: sufficiency with the Karush–Kuhn–Tucker conditions in place of a binding
  cash constraint: multipliers `μ_t, ν_t ≥ 0` with `ι_t = μ_t + ν_t`,
  `μ_t(m_t − (1/V − 1)c_t − y_t) = 0`, `ν_tm_t = 0`, `βᵗu'(c_t) = λΛ_t(1 + (1/V − 1)μ_t)`, and the
  liminf transversality condition.
* `WedgeCx.wedge_euler_needs_money`: the hypothesis "money positive" cannot be dropped from
  the wedge Euler equation: for `V = 2`, linear utility and a price level whose growth
  alternates between `2` and `1`, holding no money with a slack cash constraint is optimal (by
  `cia_optimal_of_kkt`), yet no constant `λ` has `βᵗu'(c_t) = λΛ_tw_t` at dates `0` and `1`. It
  is also an optimum at which the cash constraint does not bind, which
  `CashInAdvanceMeasure.optimal_of_foc` could not certify.
-/

namespace Cochrane.Monetarism.TidyR6HouseholdCIA

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure HouseholdMeasure
  TidyR6HouseholdRoll TidyR6HouseholdLocal TidyR6HouseholdFOC TidyR6HouseholdSuff
  CashInAdvanceMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### Localization on a family of events -/

/-- Cochrane (2023), footnote 1, p. 440, **from tests to almost-sure equations on an event.**
As `TidyR6HouseholdFOC.ae_eq_of_tests`, with the tests also restricted to an increasing family of
events `E K` known at `t`: then `v(c_t, m_t) = w` almost surely on `⋃_K E K`. -/
theorem ae_eq_of_tests_on {U : Set (ℝ × ℝ)} (hU : IsOpen U) {Λ P c m : ℕ → Ω → ℝ}
    (hp : PriceWeak S Λ P) (hca : StronglyAdapted S.𝓕 c) (hma : StronglyAdapted S.𝓕 m)
    (hdom : DomainCon S U c m) {t : ℕ} {E : ℕ → Set Ω} (hEm : ∀ K, MeasurableSet[S.𝓕 t] (E K))
    (hEmono : Monotone E) {v : ℝ × ℝ → ℝ} (hv : ContinuousOn v U) {w : Ω → ℝ}
    (hw : StronglyMeasurable[S.𝓕 t] w)
    (hwb : ∀ K : ℕ, ∃ C, ∀ ω, Loc S U Λ P c m t K ω → |w ω| ≤ C)
    (htest : ∀ (K : ℕ) (B : ℝ) (z : Ω → ℝ), StronglyMeasurable[S.𝓕 t] z →
      (∀ ω, z ω = 0 ∨ ((Loc S U Λ P c m t K ω ∧ ω ∈ E K) ∧ |z ω| ≤ B)) →
      ∫ ω, (v (c t ω, m t ω) - w ω) * z ω ∂S.μ = 0) :
    ∀ᵐ ω ∂S.μ, (∃ K, ω ∈ E K) → v (c t ω, m t ω) = w ω := by
  have hK : ∀ K : ℕ, ∀ᵐ ω ∂S.μ, (Loc S U Λ P c m t K ω ∧ ω ∈ E K) →
      v (c t ω, m t ω) = w ω := by
    intro K
    obtain ⟨C₁, hC₁0, hC₁⟩ := kc_bound (U := U) K hv
    obtain ⟨C₂, hC₂⟩ := hwb K
    set L := {ω | Loc S U Λ P c m t K ω} ∩ E K with hL
    have hLm : MeasurableSet[S.𝓕 t] L := (measurableSet_loc (U := U) hp hca hma t K).inter (hEm K)
    set g : Ω → ℝ := L.indicator (fun ω => U.indicator v (c t ω, m t ω) - w ω) with hg
    have hgm : StronglyMeasurable[S.𝓕 t] g :=
      (((measurable_indicator_of_continuousOn hU hv).comp ((hca t).measurable.prodMk
        (hma t).measurable)).sub hw.measurable).stronglyMeasurable.indicator hLm
    have hgL : ∀ ω, ω ∈ L → g ω = v (c t ω, m t ω) - w ω := fun ω hω => by
      rw [hg, Set.indicator_of_mem hω,
        Set.indicator_of_mem (kc_subset U K (good_mem_kc hω.1.1))]
    have hgsupp : ∀ ω, g ω = 0 ∨ ((Loc S U Λ P c m t K ω ∧ ω ∈ E K) ∧ |g ω| ≤ C₁ + |C₂|) := by
      intro ω
      by_cases hω : ω ∈ L
      · right
        refine ⟨hω, ?_⟩
        rw [hgL ω hω]
        exact (abs_sub _ _).trans (add_le_add (hC₁ _ (good_mem_kc hω.1.1))
          ((hC₂ ω hω.1).trans (le_abs_self _)))
      · left
        rw [hg, Set.indicator_of_notMem hω]
    have h0 := htest K (C₁ + |C₂|) g hgm hgsupp
    have heq : (fun ω => (v (c t ω, m t ω) - w ω) * g ω) = fun ω => g ω * g ω := by
      funext ω
      by_cases hω : ω ∈ L
      · rw [hgL ω hω]
      · rw [hg, Set.indicator_of_notMem hω, mul_zero, mul_zero]
    rw [heq] at h0
    have hgi : Integrable (fun ω => g ω * g ω) S.μ := by
      refine Integrable.of_bound ((hgm.mul hgm).mono (S.𝓕.le t)).aestronglyMeasurable
        ((C₁ + |C₂|) * (C₁ + |C₂|)) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have hb : |g ω| ≤ C₁ + |C₂| := by
        rcases hgsupp ω with h | h
        · rw [h, abs_zero]
          exact add_nonneg hC₁0 (abs_nonneg _)
        · exact h.2
      exact mul_le_mul hb hb (abs_nonneg _) ((abs_nonneg _).trans hb)
    filter_upwards [ae_eq_zero_of_integral_mul_self hgi h0] with ω hω hl
    have := hgL ω hl
    rw [hω, Pi.zero_apply] at this
    linarith
  filter_upwards [ae_all_iff.2 hK, ae_exists_loc (Λ := Λ) (P := P) hU hdom t] with ω h1 h2 h3
  obtain ⟨K, hl⟩ := h2
  obtain ⟨K', hE⟩ := h3
  exact h1 (max K K') ⟨loc_mono (le_max_left _ _) hl, hEmono (le_max_right _ _) hE⟩

/-! ### Utility of consumption on an open interval -/

/-- Cochrane (2023), §19.5.1, p. 448: a utility of consumption differentiable on the open set `I`
with derivative `u'` continuous on `I` is a utility `C¹` on the domain `I × ℝ` of
`(c, m)`, with `u_c = u'` and `u_m = 0`. -/
theorem c1On_cons {u u' : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (hu : ∀ x ∈ I, HasDerivAt u (u' x) x)
    (hu' : ContinuousOn u' I) :
    C1On (fun x _ => u x) (fun x _ => u' x) (fun _ _ => 0) (I ×ˢ Set.univ) := by
  refine ⟨hI.prod isOpen_univ, fun p hp => ?_, ?_, continuousOn_const⟩
  · have := (hu p.1 hp.1).hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
    have e : (ContinuousLinearMap.toSpanSingleton ℝ (u' p.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ) = u' p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
      ext <;> simp [mul_comm]
    rw [e] at this
    exact this
  · exact hu'.comp continuousOn_fst fun p hp => hp.1

variable (S) in
/-- Cochrane (2023), eqs. (19.24)–(19.26), pp. 448–449, with consumption in the domain `I` of the
utility: the cash-in-advance and no-printing constraints (`CashInAdvanceMeasure.CIACon`) and
`c_t ∈ I` almost surely at every date. -/
def CIAConD (V : ℝ) (I : Set ℝ) (y : ℕ → Ω → ℝ) (c m : ℕ → Ω → ℝ) : Prop :=
  CIACon S V y c m ∧ DomainCon S (I ×ˢ Set.univ) c m

/-! ### The Euler equation with the velocity wedge -/

/-- Cochrane (2023), (19.31), p. 450 and (19.24)–(19.26), pp. 448–449, **the cash-in-advance
Euler equation with one constant multiplier, without regularity hypotheses.** Let `u` be `C¹` on
the open set `I` of consumption levels, let prices satisfy only `PriceWeak`, and let `(c, m, a)`
be optimal among feasible plans satisfying the cash-in-advance and no-printing constraints with
consumption in `I`. Then there is one real `λ` such that at every date, almost surely where
overnight money is positive, `βᵗu'(c_t) = λΛ_tw_t` with `w_t = 1 + (1/V − 1)ι_t`. -/
theorem cia_multiplier {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hu : ∀ x ∈ I, HasDerivAt u (u' x) x) (hu' : ContinuousOn u' I) {V : ℝ}
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : Optimal S β (fun x _ => u x) (CIAConD S V I y) Λ P y s N0 a0 c m a)
    (hp : PriceWeak S Λ P) :
    ∃ lam : ℝ, ∀ t, ∀ᵐ ω ∂S.μ, 0 < m t ω →
      β ^ t * u' (c t ω) = lam * (Λ t ω * wedge S (1 / V - 1) Λ P t ω) := by
  have hC := c1On_cons hI hu hu'
  set U : Set (ℝ × ℝ) := I ×ˢ Set.univ with hUdef
  have hfeas := hopt.1
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have hcia := hopt.2.1.1
  have hdom := hopt.2.1.2
  have hnp := hfeas.2.2.2.2.2.2.2.2.2
  set θ : ℝ := 1 / V - 1 with hθ
  set Adm : ℕ → (Ω → ℝ) × (Ω → ℝ) → Prop := fun t v =>
    ∃ (K : ℕ) (B : ℝ), RollTest S U Λ P c m t K B v.1 v.2 ∧ v.2 = θ • v.1 ∧
      ∀ ω, v.1 ω ≠ 0 → 1 / ((K : ℝ) + 1) ≤ m t ω with hAdm
  set Lu : ℕ → (Ω → ℝ) × (Ω → ℝ) → ℝ := fun t v => β ^ t * ∫ ω, (u' (c t ω) * v.1 ω +
    0 * v.2 ω) ∂S.μ with hLu
  set Lp : ℕ → (Ω → ℝ) × (Ω → ℝ) → ℝ := fun t v =>
    ∫ ω, Λ t ω * (v.1 ω + iota S Λ P t ω * v.2 ω) ∂S.μ with hLp
  have hucU : ContinuousOn (fun p : ℝ × ℝ => u' p.1) U := hC.2.2.1
  have iu : ∀ t v, Adm t v → Integrable (fun ω => u' (c t ω) * v.1 ω + 0 * v.2 ω) S.μ := by
    rintro t v ⟨K, B, h, -, -⟩
    exact (h.integrable_util hC.1 hca hma hucU).1.add ((integrable_zero _ _ _).congr
      (Eventually.of_forall fun ω => by simp))
  have ip : ∀ t v, Adm t v → Integrable (fun ω => Λ t ω * (v.1 ω + iota S Λ P t ω * v.2 ω))
      S.μ := by
    rintro t v ⟨K, B, h, -, -⟩
    have := (h.integrable hp).2.2.2
    refine this.neg.congr (Eventually.of_forall fun ω => ?_)
    simp [rollX]
  have hXLp : ∀ t v, ∫ ω, rollX S Λ P t v.1 v.2 ω ∂S.μ = -Lp t v := fun t v => by
    rw [hLp, ← integral_neg]
    rfl
  obtain ⟨lam, hlam⟩ := lagrange (V := (Ω → ℝ) × (Ω → ℝ)) Adm Lu Lp
    (fun t => ⟨0, 0, rollTest_zero U Λ P c m t 0 0, by ext ω; simp, fun ω h => by
      simp at h⟩)
    (fun t v w a ⟨K, B, h, hv2, hvm⟩ ⟨K', B', h', hw2, hwm⟩ => by
      refine ⟨_, _, h.comb h' a, ?_, fun ω hne => ?_⟩
      · funext ω
        have e1 := congrFun hv2 ω
        have e2 := congrFun hw2 ω
        simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
        change v.2 ω + a * w.2 ω = θ * (v.1 ω + a * w.1 ω)
        rw [e1, e2]
        ring
      · have hK : 1 / ((max K K' : ℕ) + 1 : ℝ) ≤ 1 / ((K : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by
            have : (K : ℝ) ≤ (max K K' : ℕ) := by exact_mod_cast le_max_left _ _
            linarith)
        have hK' : 1 / ((max K K' : ℕ) + 1 : ℝ) ≤ 1 / ((K' : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by
            have : (K' : ℝ) ≤ (max K K' : ℕ) := by exact_mod_cast le_max_right _ _
            linarith)
        by_cases h1 : v.1 ω = 0
        · have h2 : w.1 ω ≠ 0 := by
            intro h2
            apply hne
            change v.1 ω + a * w.1 ω = 0
            rw [h1, h2]
            ring
          exact hK'.trans (hwm ω h2)
        · exact hK.trans (hvm ω h1))
    (fun t v w a hv hw => by
      have e : ∀ ω, (v + a • w).1 ω = v.1 ω + a * w.1 ω := fun ω => rfl
      have e' : ∀ ω, (v + a • w).2 ω = v.2 ω + a * w.2 ω := fun ω => rfl
      have h1 := integral_add (iu t v hv) ((iu t w hw).const_mul a)
      rw [integral_const_mul] at h1
      simp only [hLu, e, e']
      rw [mul_left_comm a, ← mul_add, ← h1]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring))
    (fun t v w a hv hw => by
      have e : ∀ ω, (v + a • w).1 ω = v.1 ω + a * w.1 ω := fun ω => rfl
      have e' : ∀ ω, (v + a • w).2 ω = v.2 ω + a * w.2 ω := fun ω => rfl
      have h1 := integral_add (ip t v hv) ((ip t w hw).const_mul a)
      rw [integral_const_mul] at h1
      simp only [hLp, e, e']
      rw [← h1]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring))
    (fun t₁ t₂ hne v w ⟨K₁, B₁, h₁, hv2, hvm⟩ ⟨K₂, B₂, h₂, hw2, hwm⟩ hsum => by
      obtain ⟨r, hr, φ, hφ0, hφd, hφle⟩ := roll_gain hβ hC hopt hp hne h₁ h₂
      set a₁ : ℝ := 1 / (2 * ((K₁ : ℝ) + 1)) / (|B₁| + 1) with ha₁
      set a₂ : ℝ := 1 / (2 * ((K₂ : ℝ) + 1)) / (|B₂| + 1) with ha₂
      set b₁ : ℝ := 1 / ((K₁ : ℝ) + 1) / ((|θ| + 1) * (|B₁| + 1)) with hb₁
      set b₂ : ℝ := 1 / ((K₂ : ℝ) + 1) / ((|θ| + 1) * (|B₂| + 1)) with hb₂
      set η := min r (min (min a₁ a₂) (min b₁ b₂)) with hη
      have hη0 : 0 < η := lt_min hr (lt_min (lt_min (by positivity) (by positivity))
        (lt_min (by positivity) (by positivity)))
      have hmax : IsLocalMax φ 0 := by
        refine Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hη0) fun ε hε => ?_
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
        rw [hφ0]
        have hεa₁ : |ε| < a₁ := lt_of_lt_of_le hε
          ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
        have hεa₂ : |ε| < a₂ := lt_of_lt_of_le hε
          ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
        have hεb₁ : |ε| < b₁ := lt_of_lt_of_le hε
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
        have hεb₂ : |ε| < b₂ := lt_of_lt_of_le hε
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
        have hε₁ : |ε| * (|B₁| + 1) < 1 / (2 * ((K₁ : ℝ) + 1)) := by
          rw [← lt_div_iff₀ (by positivity)]
          exact hεa₁
        have hε₂ : |ε| * (|B₂| + 1) < 1 / (2 * ((K₂ : ℝ) + 1)) := by
          rw [← lt_div_iff₀ (by positivity)]
          exact hεa₂
        -- the money change is small where the test is active
        have hsmall : ∀ (K : ℕ) (B x : ℝ), |x| ≤ |B| →
            |ε| < 1 / ((K : ℝ) + 1) / ((|θ| + 1) * (|B| + 1)) →
            |ε * (θ * x)| < 1 / ((K : ℝ) + 1) := by
          intro K B x hx hεK
          rw [lt_div_iff₀ (by positivity)] at hεK
          rw [abs_mul, abs_mul]
          calc |ε| * (|θ| * |x|) ≤ |ε| * ((|θ| + 1) * (|B| + 1)) := by
                refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
                exact mul_le_mul (by linarith) (by linarith) (abs_nonneg _) (by positivity)
            _ < 1 / ((K : ℝ) + 1) := hεK
        have hbd : ∀ {t : ℕ} {K : ℕ} {B : ℝ} {z ζ : Ω → ℝ},
            RollTest S U Λ P c m t K B z ζ → ∀ ω, |z ω| ≤ |B| := by
          intro t K B z ζ h ω
          rcases h.2.2 ω with h0 | h0
          · rw [h0.1, abs_zero]
            exact abs_nonneg _
          · exact h0.2.1.trans (le_abs_self _)
        refine hφle ε (lt_of_lt_of_le hε (min_le_left _ _)) ⟨fun n => ?_,
          domainCon_roll hdom hne h₁ h₂ hε₁ hε₂⟩ fun δ hδ => ?_
        · filter_upwards [hcia n] with ω ⟨hc1, hc2⟩
          have ev : v.2 ω = θ * v.1 ω := by
            have := congrFun hv2 ω
            simpa using this
          have ew : w.2 ω = θ * w.1 ω := by
            have := congrFun hw2 ω
            simpa using this
          have hm' : m n ω + ε * (rollC t₁ v.2 n ω + rollC t₂ w.2 n ω) =
              m n ω + ε * (θ * (rollC t₁ v.1 n ω + rollC t₂ w.1 n ω)) := by
            simp only [rollC]
            split_ifs <;> simp [ev, ew, mul_add]
          refine ⟨?_, ?_⟩
          · rw [hm']
            nlinarith
          · rw [hm']
            by_cases h1 : n = t₁
            · subst h1
              simp only [rollC, ↓reduceIte, hne, add_zero]
              by_cases hz : v.1 ω = 0
              · rw [hz]
                simpa using hc2
              · have := hvm ω hz
                have := hsmall K₁ B₁ (v.1 ω) (hbd h₁ ω) hεb₁
                linarith [neg_abs_le (ε * (θ * v.1 ω))]
            · by_cases h2 : n = t₂
              · subst h2
                simp only [rollC, ↓reduceIte, h1, zero_add]
                by_cases hz : w.1 ω = 0
                · rw [hz]
                  simpa using hc2
                · have := hwm ω hz
                  have := hsmall K₂ B₂ (w.1 ω) (hbd h₂ ω) hεb₂
                  linarith [neg_abs_le (ε * (θ * w.1 ω))]
              · simpa [rollC, h1, h2] using hc2
        · have e := hXLp t₁ v
          have e' := hXLp t₂ w
          rw [e, e', ← neg_add, hsum, neg_zero, mul_zero]
          simpa using hnp δ hδ
      exact hmax.hasDerivAt_eq_zero hφd)
  refine ⟨lam, fun t => ?_⟩
  have hE : Monotone (fun K : ℕ => {ω | 1 / ((K : ℝ) + 1) ≤ m t ω}) := by
    intro K K' hKK ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hc : (K : ℝ) ≤ K' := Nat.cast_le.2 hKK
    exact (one_div_le_one_div_of_le (by positivity) (by linarith)).trans hω
  have key := ae_eq_of_tests_on (E := fun K : ℕ => {ω | 1 / ((K : ℝ) + 1) ≤ m t ω})
    (v := fun p => β ^ t * u' p.1) (w := fun ω => lam * (Λ t ω * wedge S θ Λ P t ω))
    hC.1 hp hca hma hdom (fun K => measurableSet_le measurable_const (hma t).measurable) hE
    (hucU.const_smul (β ^ t))
    (((hp.1 t).mul (stronglyMeasurable_const.add ((hp.sm_iota t).const_mul θ))).const_mul lam)
    (fun K => ⟨|lam| * (K * (1 + |θ| * K)), fun ω hl => by
      rw [abs_mul, abs_mul, abs_of_pos (hp.2.2.1 t ω)]
      refine mul_le_mul_of_nonneg_left (mul_le_mul hl.2.1 ?_ (abs_nonneg _) (by positivity))
        (abs_nonneg _)
      simp only [wedge]
      refine (abs_add_le _ _).trans ?_
      rw [abs_one, abs_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hl.2.2.2 (abs_nonneg _))⟩)
    fun K B z hz hzs => ?_
  · filter_upwards [key] with ω hω hm
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hm
    exact hω ⟨K, hK.le⟩
  · have hT : RollTest S U Λ P c m t K (|B| * (|θ| + 1)) z (θ • z) := by
      refine ⟨hz, hz.const_smul θ, fun ω => ?_⟩
      rcases hzs ω with h0 | ⟨⟨hl, -⟩, hzB⟩
      · left
        simp [h0]
      · right
        refine ⟨hl, ?_, ?_⟩
        · calc |z ω| ≤ |B| := hzB.trans (le_abs_self _)
            _ ≤ |B| * (|θ| + 1) := le_mul_of_one_le_right (abs_nonneg _) (by
              linarith [abs_nonneg θ])
        · rw [Pi.smul_apply, smul_eq_mul, abs_mul]
          calc |θ| * |z ω| ≤ |θ| * |B| :=
                mul_le_mul_of_nonneg_left (hzB.trans (le_abs_self _)) (abs_nonneg _)
            _ ≤ |B| * (|θ| + 1) := by nlinarith [abs_nonneg θ, abs_nonneg B]
    have hAd : Adm t (z, θ • z) := ⟨K, _, hT, rfl, fun ω hne => by
      rcases hzs ω with h0 | ⟨⟨-, hE'⟩, -⟩
      · exact absurd h0 hne
      · exact hE'⟩
    have h := hlam t (z, θ • z) hAd
    simp only [hLu, hLp, zero_mul, add_zero, Pi.smul_apply, smul_eq_mul] at h
    have i1 := (hT.integrable_util hC.1 hca hma hucU).1
    have i2 : Integrable (fun ω => Λ t ω * (z ω + iota S Λ P t ω * (θ * z ω))) S.μ := by
      have := ip t (z, θ • z) hAd
      simpa using this
    rw [← integral_const_mul, ← integral_const_mul, ← sub_eq_zero, ← integral_sub
      (i1.const_mul _) (i2.const_mul _)] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [wedge]
    ring

/-! ### Nonnegative nominal rates are a consequence of optimality -/

/-- Cochrane (2023), §19.5.1, p. 449 and (19.33), p. 451 (money is dominated unless `i ≥ 0`):
**at a cash-in-advance optimum the nominal rate is nonnegative.** If `u' > 0` at the plan at
date `t`, then `ι_t = 1 − Q_t ≥ 0` almost surely. Otherwise, on an event of positive probability
where `ι_t < 0`, holding more overnight money is profitable: the household can hold `M` more units
of money and consume one more unit, for less than nothing, and roll the gain over for ever. No
bounds on prices or the plan are used. -/
theorem cia_iota_nonneg {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hu : ∀ x ∈ I, HasDerivAt u (u' x) x) (hu' : ContinuousOn u' I) {V : ℝ}
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : Optimal S β (fun x _ => u x) (CIAConD S V I y) Λ P y s N0 a0 c m a)
    (hp : PriceWeak S Λ P) (t : ℕ) (hpos : ∀ᵐ ω ∂S.μ, 0 < u' (c t ω)) :
    ∀ᵐ ω ∂S.μ, 0 ≤ iota S Λ P t ω := by
  have hC := c1On_cons hI hu hu'
  set U : Set (ℝ × ℝ) := I ×ˢ Set.univ with hUdef
  have hfeas := hopt.1
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have hcia := hopt.2.1.1
  have hdom := hopt.2.1.2
  have hnp := hfeas.2.2.2.2.2.2.2.2.2
  set θ : ℝ := 1 / V - 1 with hθ
  have hK : ∀ K : ℕ, ∀ᵐ ω ∂S.μ,
      ¬ (Loc S U Λ P c m t K ω ∧ iota S Λ P t ω ≤ -(1 / ((K : ℝ) + 1))) := by
    intro K
    set B := {ω | Loc S U Λ P c m t K ω ∧ iota S Λ P t ω ≤ -(1 / ((K : ℝ) + 1))} with hBdef
    have hBm : MeasurableSet[S.𝓕 t] B := (measurableSet_loc (U := U) hp hca hma t K).inter
      (measurableSet_le (hp.sm_iota t).measurable measurable_const)
    rw [ae_iff]
    simp only [not_not]
    by_contra hB0
    have hBpos : 0 < S.μ B := pos_iff_ne_zero.2 hB0
    set M : ℝ := 2 * ((K : ℝ) + 1) + |θ| with hM
    have hM1 : 1 ≤ M := by
      have : (0 : ℝ) ≤ K := K.cast_nonneg
      linarith [abs_nonneg θ]
    set z : Ω → ℝ := B.indicator (fun _ => 1) with hz
    set ζ : Ω → ℝ := B.indicator (fun _ => M) with hζ
    have hT : RollTest S U Λ P c m t K M z ζ := by
      refine ⟨stronglyMeasurable_const.indicator hBm, stronglyMeasurable_const.indicator hBm,
        fun ω => ?_⟩
      by_cases hω : ω ∈ B
      · right
        refine ⟨hω.1, ?_, ?_⟩
        · rw [hz, Set.indicator_of_mem hω, abs_one]
          exact hM1
        · rw [hζ, Set.indicator_of_mem hω, abs_of_pos (by linarith)]
      · left
        simp [hz, hζ, Set.indicator_of_notMem hω]
    have hT0 := rollTest_zero (S := S) U Λ P c m (t + 1) 0 0
    obtain ⟨r, hr, φ, hφ0, hφd, hφle⟩ := roll_gain hβ hC hopt hp (by omega) hT hT0
    -- the deviation earns money: `z + ιζ ≤ −1` on `B`
    have hcost : ∀ ω, Λ t ω * (z ω + iota S Λ P t ω * ζ ω) ≤ 0 := by
      intro ω
      by_cases hω : ω ∈ B
      · rw [hz, hζ, Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        refine mul_nonpos_of_nonneg_of_nonpos (hp.2.2.1 t ω).le ?_
        have h1 := hω.2
        have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
        have h2 : iota S Λ P t ω * M ≤ -(1 / ((K : ℝ) + 1)) * M :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
        have h3 : 2 ≤ 1 / ((K : ℝ) + 1) * M := by
          have e : 1 / ((K : ℝ) + 1) * M = 2 + 1 / ((K : ℝ) + 1) * |θ| := by
            rw [hM]
            field_simp
          rw [e]
          have : (0 : ℝ) ≤ 1 / ((K : ℝ) + 1) * |θ| := by positivity
          linarith
        nlinarith
      · simp [hz, hζ, Set.indicator_of_notMem hω]
    have hXnn : 0 ≤ ∫ ω, rollX S Λ P t z ζ ω ∂S.μ := by
      refine integral_nonneg fun ω => ?_
      exact neg_nonneg.2 (hcost ω)
    have hX0 : ∫ ω, rollX S Λ P (t + 1) 0 0 ω ∂S.μ = 0 := by simp [rollX]
    -- the derivative is positive
    have hDpos : 0 < β ^ t * ∫ ω, (u' (c t ω) * z ω + 0 * ζ ω) ∂S.μ +
        β ^ (t + 1) * ∫ ω, (u' (c (t + 1) ω) * 0 + 0 * 0) ∂S.μ := by
      simp only [mul_zero, add_zero, zero_mul, integral_zero]
      refine mul_pos (pow_pos hβ t) ?_
      have hi := (hT.integrable_util hC.1 hca hma hC.2.2.1).1
      rw [integral_pos_iff_support_of_nonneg_ae ?_ hi]
      · refine lt_of_lt_of_le hBpos (measure_mono_ae ?_)
        filter_upwards [hpos] with ω hω hB
        simp only [Function.mem_support, hz, Set.indicator_of_mem hB, mul_one]
        exact hω.ne'
      · filter_upwards [hpos] with ω hω
        simp only [hz, Pi.zero_apply]
        by_cases hB : ω ∈ B
        · rw [Set.indicator_of_mem hB, mul_one]
          exact hω.le
        · rw [Set.indicator_of_notMem hB, mul_zero]
    set η := min r (1 / (2 * ((K : ℝ) + 1)) / (|M| + 1)) with hη
    have hη0 : 0 < η := lt_min hr (by positivity)
    have hDle := slope_nonpos hφd hφ0 hη0 fun ε hε0 hεη => by
      have hε : |ε| = ε := abs_of_pos hε0
      have hε₁ : |ε| * (|M| + 1) < 1 / (2 * ((K : ℝ) + 1)) := by
        rw [← lt_div_iff₀ (by positivity), hε]
        exact lt_of_lt_of_le hεη (min_le_right _ _)
      have hε₂ : |ε| * (|(0 : ℝ)| + 1) < 1 / (2 * ((0 : ℕ) + 1 : ℝ)) := by
        have h1 : ε < 1 / (2 * ((K : ℝ) + 1)) / (|M| + 1) := lt_of_lt_of_le hεη (min_le_right _ _)
        have h2 : 1 / (2 * ((K : ℝ) + 1)) / (|M| + 1) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]
          have : 1 / (2 * ((K : ℝ) + 1)) ≤ 1 / 2 :=
            one_div_le_one_div_of_le (by norm_num) (by linarith [K.cast_nonneg (α := ℝ)])
          nlinarith [abs_nonneg M]
        rw [hε, abs_zero]
        push_cast
        linarith
      refine hφle ε (by rw [hε]; exact lt_of_lt_of_le hεη (min_le_left _ _))
        ⟨fun n => ?_, domainCon_roll hdom (by omega) hT hT0 hε₁ hε₂⟩ fun δ hδ => ?_
      · filter_upwards [hcia n] with ω ⟨hc1, hc2⟩
        by_cases hn : n = t
        · subst hn
          simp only [rollC, ↓reduceIte, show n ≠ n + 1 by omega, add_zero]
          by_cases hω : ω ∈ B
          · rw [hz, hζ, Set.indicator_of_mem hω, Set.indicator_of_mem hω]
            refine ⟨?_, by nlinarith⟩
            have : θ ≤ M := (le_abs_self θ).trans (by
              have : (0 : ℝ) ≤ K := K.cast_nonneg
              linarith)
            nlinarith
          · rw [hz, hζ, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
            simp only [mul_zero, add_zero]
            exact ⟨hc1, hc2⟩
        · by_cases hn' : n = t + 1
          · subst hn'
            simp only [rollC, ↓reduceIte, hn, Pi.zero_apply, add_zero, mul_zero]
            exact ⟨hc1, hc2⟩
          · simp only [rollC, hn, hn', ↓reduceIte, add_zero, mul_zero]
            exact ⟨hc1, hc2⟩
      · rw [hX0, add_zero]
        filter_upwards [hnp δ hδ] with T hT'
        nlinarith
    simp only [Pi.zero_apply] at hDle
    linarith
  filter_upwards [ae_all_iff.2 hK, ae_exists_loc (Λ := Λ) (P := P) hC.1 hdom t] with ω h1 h2
  obtain ⟨K₁, hl⟩ := h2
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.2 hneg)
  have hm : (n : ℝ) ≤ (max K₁ n : ℕ) := by exact_mod_cast le_max_right _ _
  refine h1 (max K₁ n) ⟨loc_mono (le_max_left _ _) hl, ?_⟩
  have : 1 / ((max K₁ n : ℕ) + 1 : ℝ) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- Cochrane (2023), p. 450 (`CashInAdvance.MoneyDemand.binding_cost_wedge`): where `0 ≤ ι_t`,
the bond price is nonnegative and `V > 0`, the velocity wedge `w_t = 1 + (1/V − 1)ι_t` is at
least `min 1 (1/V) > 0`. Combined with `cia_iota_nonneg`, at an optimum with `u' > 0` the wedge
is bounded away from zero, with no assumption on `Q_t`. -/
theorem cia_wedge_pos {Λ P : ℕ → Ω → ℝ} (hp : PriceWeak S Λ P) {V : ℝ} (hV : 0 < V) {t : ℕ}
    (hι : ∀ᵐ ω ∂S.μ, 0 ≤ iota S Λ P t ω) :
    ∀ᵐ ω ∂S.μ, min 1 (1 / V) ≤ wedge S (1 / V - 1) Λ P t ω := by
  have hQ : ∀ᵐ ω ∂S.μ, 0 ≤ bondPrice S Λ P t ω := by
    have h0 : 0 ≤ᵐ[S.μ] pk Λ P (t + 1) := Eventually.of_forall fun ω => (hp.pk_pos _ ω).le
    filter_upwards [condExp_nonneg (m := S.𝓕 t) h0] with ω hω
    exact div_nonneg hω (hp.pk_pos t ω).le
  filter_upwards [hι, hQ] with ω h1 h2
  simp only [wedge]
  have hι1 : iota S Λ P t ω ≤ 1 := by simp only [iota]; linarith
  rcases le_or_gt V 1 with hV1 | hV1
  · have hθ : 0 ≤ 1 / V - 1 := by
      rw [sub_nonneg, le_div_iff₀ hV]
      linarith
    exact (min_le_left _ _).trans (by nlinarith)
  · have hθ : 1 / V - 1 < 0 := by
      rw [sub_neg, div_lt_one hV]
      exact hV1
    refine (min_le_right _ _).trans ?_
    nlinarith

/-! ### Sufficiency with the Karush–Kuhn–Tucker conditions -/

/-- Cochrane (2023), p. 453 ("first order conditions and transversality conditions are
necessary and sufficient"), on a probability space, **sufficiency without a binding cash
constraint**: for `u` with the supergradient property on `I` (concavity), `PriceWeak` prices,
integrable endowment and tax values, a feasible, admissible plan satisfying the cash-in-advance
and domain constraints is optimal if there are a constant `λ ≥ 0` and processes `μ_t, ν_t ≥ 0`
with, almost surely at every date, `ι_t = μ_t + ν_t`, `μ_t(m_t − (1/V − 1)c_t − y_t) = 0`
(the cash multiplier vanishes when the cash constraint is slack), `ν_tm_t = 0` (the no-printing
multiplier vanishes when money is held) and `βᵗu'(c_t) = λΛ_t(1 + (1/V − 1)μ_t)`, and if the
liminf transversality condition holds. With a binding constraint, `μ = ι`, `ν = 0` recovers
`CashInAdvanceMeasure.optimal_of_foc`. -/
theorem cia_optimal_of_kkt {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} {I : Set ℝ}
    (hsg : ∀ x ∈ I, ∀ x' ∈ I, u x' ≤ u x + u' x * (x' - x)) {V : ℝ} {Λ P y s : ℕ → Ω → ℝ}
    {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ} (hp : PriceWeak S Λ P)
    (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ) {lam : ℝ} (hlam : 0 ≤ lam)
    {μ ν : ℕ → Ω → ℝ} (hf : Feasible S Λ P y s N0 a0 c m a) (hcon : CIAConD S V I y c m)
    (hadm : UAdmissible S β (fun n ω => u (c n ω)))
    (hkkt : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ μ t ω ∧ 0 ≤ ν t ω ∧ iota S Λ P t ω = μ t ω + ν t ω ∧
      μ t ω * (m t ω - ((1 / V - 1) * c t ω + y t ω)) = 0 ∧ ν t ω * m t ω = 0 ∧
      β ^ t * u' (c t ω) = lam * (Λ t ω * (1 + (1 / V - 1) * μ t ω)))
    (hlim : ∀ L, 0 < L → ∃ᶠ T in atTop, wealthPV S Λ P N0 m a T < L) :
    Optimal S β (fun x _ => u x) (CIAConD S V I y) Λ P y s N0 a0 c m a := by
  refine optimal_of_supergradient_liminf hβ hp hy hs hlam hf hcon hadm hlim
    fun c' m' a' _ hcon' t => ?_
  filter_upwards [hkkt t, hcon.1 t, hcon.2 t, hcon'.1 t, hcon'.2 t] with ω h h1 h2 h3 h4
  obtain ⟨hμ, hν, hι, hcs1, hcs2, hfoc⟩ := h
  set θ : ℝ := 1 / V - 1
  have hk := mul_le_mul_of_nonneg_left (show u (c' t ω) - u (c t ω) ≤ u' (c t ω) *
    (c' t ω - c t ω) by linarith [hsg _ h2.1 _ h4.1]) (pow_nonneg hβ.le t)
  have key : iota S Λ P t ω * (m' t ω - m t ω) - θ * μ t ω * (c' t ω - c t ω) =
      μ t ω * (m' t ω - (θ * c' t ω + y t ω)) + ν t ω * m' t ω := by
    rw [hι]
    linear_combination -hcs1 - hcs2
  have hnn : 0 ≤ iota S Λ P t ω * (m' t ω - m t ω) - θ * μ t ω * (c' t ω - c t ω) := by
    rw [key]
    exact add_nonneg (mul_nonneg hμ (by linarith [h3.1])) (mul_nonneg hν h3.2)
  have hΛ := (hp.2.2.1 t ω).le
  calc β ^ t * ((fun x _ => u x : ℝ → ℝ → ℝ) (c' t ω) (m' t ω) -
        (fun x _ => u x : ℝ → ℝ → ℝ) (c t ω) (m t ω))
      ≤ β ^ t * (u' (c t ω) * (c' t ω - c t ω)) := hk
    _ = lam * (Λ t ω * (1 + θ * μ t ω)) * (c' t ω - c t ω) := by rw [← hfoc]; ring
    _ ≤ lam * (Λ t ω * ((c' t ω - c t ω) + iota S Λ P t ω * (m' t ω - m t ω))) := by
        have := mul_nonneg (mul_nonneg hlam hΛ) hnn
        nlinarith

/-! ### Money must be positive for the wedge Euler equation -/

namespace WedgeCx

/-- Cochrane (2023), p. 450 (counterexample economy): the state prices `Λ_t = βᵗ`. -/
noncomputable def cxΛ (β : ℝ) (t : ℕ) (_ : Ω) : ℝ := β ^ t

/-- Cochrane (2023), p. 450 (counterexample economy): a price level whose growth factor
alternates between `2` and `1`: `P_t = 2^{⌊(t + 1)/2⌋}`. -/
noncomputable def cxP (t : ℕ) (_ : Ω) : ℝ := (2 : ℝ) ^ ((t + 1) / 2)

/-- Cochrane (2023), p. 450: the counterexample prices are weakly regular. -/
theorem cx_priceWeak {β : ℝ} (hβ0 : 0 < β) :
    PriceWeak S (cxΛ (Ω := Ω) β) (cxP (Ω := Ω)) :=
  ⟨fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const,
    fun t _ => pow_pos hβ0 t, fun t _ => by simp only [cxP]; positivity,
    fun t => by
      change Integrable (fun _ => β ^ t / (2 : ℝ) ^ ((t + 1) / 2)) S.μ
      exact integrable_const _⟩

/-- Cochrane (2023), (19.15), p. 441: in the counterexample economy the bond price is
`Q_t = βP_t/P_{t+1}`. -/
theorem cx_bondPrice {β : ℝ} (hβ0 : 0 < β) (t : ℕ) (ω : Ω) :
    bondPrice S (cxΛ β) cxP t ω = β * ((2 : ℝ) ^ ((t + 1) / 2) / (2 : ℝ) ^ ((t + 1 + 1) / 2)) := by
  have hE : S.E t (pk (cxΛ (Ω := Ω) β) cxP (t + 1)) =
      fun _ => β ^ (t + 1) / (2 : ℝ) ^ ((t + 1 + 1) / 2) := by
    change S.E t (fun _ => β ^ (t + 1) / (2 : ℝ) ^ ((t + 1 + 1) / 2)) = _
    exact S.E_const t _
  simp only [bondPrice, hE, pk, cxΛ, cxP]
  have h1 : (0 : ℝ) < 2 ^ ((t + 1) / 2) := by positivity
  have h2 : (0 : ℝ) < 2 ^ ((t + 1 + 1) / 2) := by positivity
  have h3 : (0 : ℝ) < β ^ t := pow_pos hβ0 t
  field_simp
  ring

/-- Cochrane (2023), (19.12), p. 439: in the counterexample economy `0 < ι_t`. -/
theorem cx_iota_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) (ω : Ω) :
    0 < iota S (cxΛ β) cxP t ω := by
  simp only [iota, cx_bondPrice hβ0]
  have h : (2 : ℝ) ^ ((t + 1) / 2) / (2 : ℝ) ^ ((t + 1 + 1) / 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) (Nat.div_le_div_right (by omega))
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((t + 1) / 2) / (2 : ℝ) ^ ((t + 1 + 1) / 2) := by positivity
  nlinarith

/-- Cochrane (2023), (19.31), p. 450 and footnote 13, **the wedge Euler equation needs positive
money.** Let `0 < β < 1`, velocity `V = 2`, linear utility `u(c) = c` on `I = ℝ`, endowment `1`,
transfers `2` (taxes `−2`), state prices `Λ_t = βᵗ` and the price level `cxP` (growth alternating
between `2` and `1`, so `ι_t` alternates). Consuming `3` and holding no overnight money is optimal
(the cash constraint `−c/2 + 1 ≤ m` is slack; by `cia_optimal_of_kkt` with `μ = 0`, `ν = ι`), yet
there is no constant `λ` with `βᵗu'(c_t) = λΛ_tw_t` almost surely at every date, although nominal
rates are positive at every date and the cash constraint is slack: the conclusion
of `cia_multiplier` and of `CashInAdvanceMeasure.multiplier_const` fails once overnight money is
zero. At this optimum the cash constraint does not bind, so `CashInAdvanceMeasure.optimal_of_foc`
does not apply. -/
theorem wedge_euler_needs_money {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Optimal S β (fun x _ => x) (CIAConD S 2 Set.univ (fun _ _ => 1)) (cxΛ β) cxP
        (fun _ _ => 1) (fun _ _ => -2) 0 0 (fun _ _ => 3) (fun _ _ => 0) (fun _ _ => 0) ∧
      (∀ t ω, 0 < iota S (cxΛ β) cxP t ω) ∧ (1 / 2 - 1 : ℝ) * 3 + 1 < 0 ∧
      ¬ ∃ lam : ℝ, ∀ t, ∀ᵐ ω ∂S.μ, β ^ t * (1 : ℝ) =
        lam * (cxΛ β t ω * wedge S (1 / 2 - 1) (cxΛ β) cxP t ω) := by
  have hp := cx_priceWeak (S := S) hβ0
  have hzero : ∀ t : ℕ, S.E t (fun ω => pk (cxΛ (Ω := Ω) β) cxP (t + 1) ω * (0 : ℝ)) = 0 := by
    intro t
    have e : (fun ω => pk (cxΛ (Ω := Ω) β) cxP (t + 1) ω * (0 : ℝ)) = fun _ => 0 := by
      funext ω
      ring
    rw [e, S.E_const]
    rfl
  refine ⟨?_, fun t ω => cx_iota_pos hβ0 hβ1 t ω, by norm_num, ?_⟩
  · refine cia_optimal_of_kkt (u' := fun _ => 1) (I := Set.univ) (lam := 1) (μ := fun _ _ => 0)
      (ν := fun t ω => iota S (cxΛ β) cxP t ω) hβ0 (fun x _ x' _ => by ring_nf; rfl) hp
      (fun t => by
        change Integrable (fun _ => β ^ t * 1) S.μ
        exact integrable_const _)
      (fun t => by
        change Integrable (fun _ => β ^ t * (-2)) S.μ
        exact integrable_const _) zero_le_one ?_ ?_ ?_ ?_ ?_
    · refine ⟨rfl, fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const,
        fun _ => stronglyMeasurable_const, fun t => Eventually.of_forall fun ω => ?_,
        fun _ => ?_, fun _ => ?_, fun t => ?_, fun t => ?_, ?_⟩
      · simp only [claimCost, hzero, Pi.zero_apply]
        cases t with
        | zero => simp [moneyIn]; ring
        | succ k => simp [moneyIn]; ring
      · simp only [mul_zero]
        exact integrable_zero _ _ _
      · refine (integrable_zero Ω ℝ S.μ).congr (Eventually.of_forall fun ω => ?_)
        cases ‹ℕ› with
        | zero => simp [moneyIn]
        | succ k => simp [moneyIn]
      · change Integrable (fun _ => β ^ t * 0) S.μ
        exact integrable_const _
      · change Integrable (fun _ => β ^ t * 3) S.μ
        exact integrable_const _
      · intro δ hδ
        refine Eventually.of_forall fun T => ?_
        have : wealthPV S (cxΛ β) cxP 0 (fun _ _ => (0 : ℝ)) (fun _ _ => 0) T = 0 := by
          simp only [wealthPV]
          refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans (integral_zero Ω ℝ)
          cases T with
          | zero => simp [moneyIn]
          | succ k => simp [moneyIn]
        rw [this]
        linarith
    · refine ⟨fun t => Eventually.of_forall fun ω => ⟨by norm_num, le_rfl⟩,
        fun t => Eventually.of_forall fun ω => ⟨Set.mem_univ _, Set.mem_univ _⟩⟩
    · exact UAdmissible.of_bdd hβ0.le hβ1 (fun _ => aestronglyMeasurable_const) (K := 3)
        fun _ _ => by norm_num
    · intro t
      refine Eventually.of_forall fun ω => ⟨le_rfl, (cx_iota_pos hβ0 hβ1 t ω).le, by ring,
        by ring, by ring, ?_⟩
      simp [cxΛ]
    · intro L hL
      refine Frequently.of_forall fun T => ?_
      have : wealthPV S (cxΛ β) cxP 0 (fun _ _ => (0 : ℝ)) (fun _ _ => 0) T = 0 := by
        simp only [wealthPV]
        refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans (integral_zero Ω ℝ)
        cases T with
        | zero => simp [moneyIn]
        | succ k => simp [moneyIn]
      rw [this]
      exact hL
  · rintro ⟨lam, hlam⟩
    obtain ⟨ω, h0, h1⟩ := ((hlam 0).and (hlam 1)).exists
    have q0 := cx_bondPrice (S := S) hβ0 0 ω
    have q1 := cx_bondPrice (S := S) hβ0 1 ω
    norm_num at q0 q1
    simp only [wedge, iota, q0, q1, cxΛ] at h0 h1
    norm_num at h0 h1
    have hb : β ≠ 0 := hβ0.ne'
    have h1' : 1 = lam * (1 + (1 / 2 - 1) * (1 - β)) := by
      have := h1
      field_simp at this
      linarith
    nlinarith

end WedgeCx

end Cochrane.Monetarism.TidyR6HouseholdCIA
