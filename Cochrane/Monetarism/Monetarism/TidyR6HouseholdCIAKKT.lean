/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6HouseholdCIA

/-!
# The cash-in-advance optimum characterised by the Karush–Kuhn–Tucker conditions

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.5.1–19.5.2,
pp. 447–451, eqs. (19.24)–(19.33) and p. 453 ("first order conditions and transversality
conditions are necessary and sufficient"), on a probability space. `TidyR6HouseholdCIA` derived
the wedge Euler equation where overnight money is positive (`cia_multiplier`) and proved
sufficiency of the KKT conditions (`cia_optimal_of_kkt`). Here the first-order conditions are
derived everywhere, including where money is zero, and the two directions are joined.

## Main results

* `lagrange_cone`: a one-sided Lagrange-multiplier lemma for convex cones of feasible
  directions: if budget-neutral pairs of feasible directions never raise utility to first order,
  one constant `λ` has `Lu ≤ λLp` on every feasible direction.
* `OneTest`, `ciaConD_roll`: localized deviations that are feasible for small `ε ≥ 0`: where
  money is not bounded away from zero real balances may only rise, and where the cash constraint
  is not slack they must rise at least `(1/V − 1)` per unit of consumption.
* `cia_one_sided`: at an optimum, with `u' > 0` and only `PriceWeak` prices, one constant
  `λ > 0` has `Lu ≤ λLp` for every such deviation.
* **`cia_kkt_necessary`**: hence the KKT conditions hold almost surely at every date:
  `βᵗu'(c_t) = λΛ_t` where the cash constraint is slack, `βᵗu'(c_t) = λΛ_tw_t` where money is
  positive, `ι_t = 0` where both hold, and at corners (money zero, constraint binding) the
  one-sided bounds `λΛ_t(1 − ι_t max(0, −θ)) ≤ βᵗu'(c_t) ≤ λΛ_t(1 + ι_t max(0, θ))`; these
  assemble into multipliers `μ_t, ν_t ≥ 0` satisfying exactly the hypotheses of
  `cia_optimal_of_kkt`.
* `cia_liminf_tvc`: the liminf transversality condition at a cash-in-advance optimum.
* **`cia_optimal_iff`**: a feasible, admissible plan satisfying the constraints is optimal if and
  only if the KKT conditions hold with some `λ > 0` and the liminf transversality condition
  holds (the analogue of `TidyR6HouseholdSuff.miu_optimal_iff`).
-/

namespace Cochrane.Monetarism.TidyR6HouseholdCIAKKT

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure HouseholdMeasure
  TidyR6HouseholdRoll TidyR6HouseholdLocal TidyR6HouseholdFOC TidyR6HouseholdSuff
  TidyR6HouseholdCIA CashInAdvanceMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### A one-sided Lagrange-multiplier lemma -/

/-- Cochrane (2023), (19.31), p. 450 (one multiplier, with inequality constraints): let `C t` be
a convex cone of feasible directions at date `t` on which `Lu t`, `Lp t` are additive and
positively homogeneous. If for all dates `t₁ ≠ t₂`, `Lp_{t₁}(v) + Lp_{t₂}(w) = 0` implies
`Lu_{t₁}(v) + Lu_{t₂}(w) ≤ 0`, and directions with `Lp > 0` and with `Lp < 0` exist, then one
constant `λ` has `Lu_t(v) ≤ λLp_t(v)` for every feasible direction at every date. -/
theorem lagrange_cone {V : Type*} [AddCommGroup V] [Module ℝ V] (C : ℕ → V → Prop)
    (Lu Lp : ℕ → V → ℝ) (hzero : ∀ t, C t 0)
    (hcomb : ∀ t v w (a : ℝ), 0 ≤ a → C t v → C t w → C t (v + a • w))
    (hLu : ∀ t v w (a : ℝ), 0 ≤ a → C t v → C t w → Lu t (v + a • w) = Lu t v + a * Lu t w)
    (hLp : ∀ t v w (a : ℝ), 0 ≤ a → C t v → C t w → Lp t (v + a • w) = Lp t v + a * Lp t w)
    (hpair : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ v w, C t₁ v → C t₂ w → Lp t₁ v + Lp t₂ w = 0 →
      Lu t₁ v + Lu t₂ w ≤ 0)
    (hA : ∃ t v, C t v ∧ 0 < Lp t v) (hB : ∃ t v, C t v ∧ Lp t v < 0) :
    ∃ lam : ℝ, ∀ t v, C t v → Lu t v ≤ lam * Lp t v := by
  have hLu0 : ∀ t, Lu t 0 = 0 := fun t => by
    have := hLu t 0 0 1 zero_le_one (hzero t) (hzero t)
    simp only [one_smul, add_zero, one_mul] at this
    linarith
  have hLp0 : ∀ t, Lp t 0 = 0 := fun t => by
    have := hLp t 0 0 1 zero_le_one (hzero t) (hzero t)
    simp only [one_smul, add_zero, one_mul] at this
    linarith
  -- a pair `v, aw` with zero total cost does not raise utility
  have hcross : ∀ t t' v w (a : ℝ), 0 ≤ a → C t v → C t' w → Lp t v + a * Lp t' w = 0 →
      Lu t v + a * Lu t' w ≤ 0 := by
    intro t t' v w a ha hv hw hsum
    by_cases htt : t = t'
    · subst htt
      have h := hpair t (t + 1) (by omega) _ 0 (hcomb t v w a ha hv hw) (hzero (t + 1))
        (by rw [hLp t v w a ha hv hw, hLp0, add_zero, hsum])
      rwa [hLu t v w a ha hv hw, hLu0, add_zero] at h
    · have h := hpair t t' htt v (0 + a • w) hv (hcomb t' 0 w a ha (hzero t') hw)
        (by rw [hLp t' 0 w a ha (hzero t') hw, hLp0, zero_add, hsum])
      rwa [hLu t' 0 w a ha (hzero t') hw, hLu0, zero_add] at h
  -- ratios on the two sides are ordered
  have hord : ∀ t v t' w, C t v → 0 < Lp t v → C t' w → Lp t' w < 0 →
      Lu t v / Lp t v ≤ Lu t' w / Lp t' w := by
    intro t v t' w hv hpv hw hpw
    have ha : 0 ≤ Lp t v / -Lp t' w := div_nonneg hpv.le (by linarith)
    have hw0 : Lp t' w ≠ 0 := hpw.ne
    have h := hcross t t' v w _ ha hv hw (by field_simp; ring)
    rw [div_le_iff₀ hpv]
    have e : Lp t v / -Lp t' w * Lu t' w = -(Lu t' w / Lp t' w * Lp t v) := by
      field_simp
    linarith
  obtain ⟨t₀, v₀, hv₀, hp₀⟩ := hA
  obtain ⟨t₁, w₁, hw₁, hp₁⟩ := hB
  set A : Set ℝ := {r | ∃ t v, C t v ∧ 0 < Lp t v ∧ r = Lu t v / Lp t v} with hAdef
  have hne : A.Nonempty := ⟨_, t₀, v₀, hv₀, hp₀, rfl⟩
  have hbdd : BddAbove A := ⟨Lu t₁ w₁ / Lp t₁ w₁, fun r ⟨t, v, hv, hp, hr⟩ =>
    hr ▸ hord t v t₁ w₁ hv hp hw₁ hp₁⟩
  refine ⟨sSup A, fun t v hv => ?_⟩
  rcases lt_trichotomy (Lp t v) 0 with hneg | h0 | hpos'
  · have h := csSup_le hne fun r ⟨t', v', hv', hp', hr⟩ => hr ▸ hord t' v' t v hv' hp' hv hneg
    exact (le_div_iff_of_neg hneg).1 h
  · have h := hcross t (t + 1) v 0 1 zero_le_one hv (hzero _) (by rw [h0, hLp0]; ring)
    rw [hLu0] at h
    rw [h0]
    linarith
  · have h : Lu t v / Lp t v ≤ sSup A := le_csSup hbdd ⟨t, v, hv, hpos', rfl⟩
    exact (div_le_iff₀ hpos').1 h

/-! ### One-sided localized deviations -/

variable (S) in
/-- Cochrane (2023), (19.24)–(19.26), pp. 448–449 and footnote 1, p. 440: a localized deviation
`(z, ζ)` at date `t` (a `TidyR6HouseholdFOC.RollTest`) that is feasible for small `ε ≥ 0`: at
each state either overnight money is at least `1/(K + 1)` or real balances do not fall
(`ζ ≥ 0`), and either the cash constraint has slack at least `1/(K + 1)` or real balances rise at
least `(1/V − 1)` per unit of consumption (`ζ ≥ (1/V − 1)z`). -/
def OneTest (U : Set (ℝ × ℝ)) (V : ℝ) (Λ P y c m : ℕ → Ω → ℝ) (t K : ℕ) (B : ℝ)
    (z ζ : Ω → ℝ) : Prop :=
  RollTest S U Λ P c m t K B z ζ ∧ ∀ ω, (1 / ((K : ℝ) + 1) ≤ m t ω ∨ 0 ≤ ζ ω) ∧
    (1 / ((K : ℝ) + 1) ≤ m t ω - ((1 / V - 1) * c t ω + y t ω) ∨ (1 / V - 1) * z ω ≤ ζ ω)

/-- Cochrane (2023), footnote 1, p. 440: the zero deviation is a one-sided test. -/
theorem oneTest_zero (U : Set (ℝ × ℝ)) (V : ℝ) (Λ P y c m : ℕ → Ω → ℝ) (t K : ℕ) (B : ℝ) :
    OneTest S U V Λ P y c m t K B 0 0 :=
  ⟨rollTest_zero U Λ P c m t K B, fun _ => ⟨Or.inr le_rfl, Or.inr (by simp)⟩⟩

/-- Cochrane (2023), footnote 1, p. 440: one-sided tests at a date form a convex cone: `v + aw`
with `a ≥ 0` is a one-sided test at the larger level. -/
theorem OneTest.comb {U : Set (ℝ × ℝ)} {V : ℝ} {Λ P y c m : ℕ → Ω → ℝ} {t K K' : ℕ} {B B' : ℝ}
    {z ζ z' ζ' : Ω → ℝ} (h : OneTest S U V Λ P y c m t K B z ζ)
    (h' : OneTest S U V Λ P y c m t K' B' z' ζ') {a : ℝ} (ha : 0 ≤ a) :
    OneTest S U V Λ P y c m t (max K K') (|B| + |a| * |B'|) (fun ω => z ω + a * z' ω)
      (fun ω => ζ ω + a * ζ' ω) := by
  have hK : 1 / ((max K K' : ℕ) + 1 : ℝ) ≤ 1 / ((K : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by
      have : (K : ℝ) ≤ (max K K' : ℕ) := by exact_mod_cast le_max_left _ _
      linarith)
  have hK' : 1 / ((max K K' : ℕ) + 1 : ℝ) ≤ 1 / ((K' : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by
      have : (K' : ℝ) ≤ (max K K' : ℕ) := by exact_mod_cast le_max_right _ _
      linarith)
  refine ⟨h.1.comb h'.1 a, fun ω => ⟨?_, ?_⟩⟩
  · rcases (h.2 ω).1 with h1 | h1
    · exact Or.inl (hK.trans h1)
    · rcases (h'.2 ω).1 with h2 | h2
      · exact Or.inl (hK'.trans h2)
      · exact Or.inr (add_nonneg h1 (mul_nonneg ha h2))
  · rcases (h.2 ω).2 with h1 | h1
    · exact Or.inl (hK.trans h1)
    · rcases (h'.2 ω).2 with h2 | h2
      · exact Or.inl (hK'.trans h2)
      · right
        have := mul_le_mul_of_nonneg_left h2 ha
        nlinarith

/-- Cochrane (2023), (19.24)–(19.26), pp. 448–449: **one-sided tests keep the constraints for
small `ε ≥ 0`**: the cash-in-advance, no-printing and domain constraints survive two one-sided
tests at different dates scaled by a small `ε ≥ 0`. -/
theorem ciaConD_roll {I : Set ℝ} {V : ℝ} {Λ P y c m : ℕ → Ω → ℝ}
    (hcon : CIAConD S V I y c m) {t₁ t₂ K₁ K₂ : ℕ} {B₁ B₂ : ℝ} {z₁ ζ₁ z₂ ζ₂ : Ω → ℝ}
    (hne : t₁ ≠ t₂) (h₁ : OneTest S (I ×ˢ Set.univ) V Λ P y c m t₁ K₁ B₁ z₁ ζ₁)
    (h₂ : OneTest S (I ×ˢ Set.univ) V Λ P y c m t₂ K₂ B₂ z₂ ζ₂) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε₁ : ε * ((|1 / V - 1| + 1) * (|B₁| + 1)) < 1 / ((K₁ : ℝ) + 1))
    (hε₂ : ε * ((|1 / V - 1| + 1) * (|B₂| + 1)) < 1 / ((K₂ : ℝ) + 1))
    (hd₁ : |ε| * (|B₁| + 1) < 1 / (2 * ((K₁ : ℝ) + 1)))
    (hd₂ : |ε| * (|B₂| + 1) < 1 / (2 * ((K₂ : ℝ) + 1))) :
    CIAConD S V I y (fun n ω => c n ω + ε * (rollC t₁ z₁ n ω + rollC t₂ z₂ n ω))
      (fun n ω => m n ω + ε * (rollC t₁ ζ₁ n ω + rollC t₂ ζ₂ n ω)) := by
  set θ : ℝ := 1 / V - 1 with hθ
  -- the change at one date keeps both constraints
  have hone : ∀ {t K : ℕ} {B : ℝ} {z ζ : Ω → ℝ}, OneTest S (I ×ˢ Set.univ) V Λ P y c m t K B z ζ →
      ε * ((|θ| + 1) * (|B| + 1)) < 1 / ((K : ℝ) + 1) → ∀ ω,
      θ * c t ω + y t ω ≤ m t ω → 0 ≤ m t ω →
      θ * (c t ω + ε * z ω) + y t ω ≤ m t ω + ε * ζ ω ∧ 0 ≤ m t ω + ε * ζ ω := by
    intro t K B z ζ h hε ω hc1 hc2
    have hbz : |z ω| ≤ |B| ∧ |ζ ω| ≤ |B| := by
      rcases h.1.2.2 ω with h0 | h0
      · rw [h0.1, h0.2, abs_zero]
        exact ⟨abs_nonneg _, abs_nonneg _⟩
      · exact ⟨h0.2.1.trans (le_abs_self _), h0.2.2.trans (le_abs_self _)⟩
    obtain ⟨hbz1, hbz2⟩ := hbz
    have hθ0 := abs_nonneg θ
    have hB0 := abs_nonneg B
    have hz0 := abs_nonneg (z ω)
    have hmag1 : |ζ ω| ≤ (|θ| + 1) * (|B| + 1) := by nlinarith
    have hmag2 : |ζ ω| + |θ| * |z ω| ≤ (|θ| + 1) * (|B| + 1) := by nlinarith
    have hεζ : ε * |ζ ω| < 1 / ((K : ℝ) + 1) :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hmag1 hε0) hε
    have hεd : ε * (|ζ ω| + |θ| * |z ω|) < 1 / ((K : ℝ) + 1) :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hmag2 hε0) hε
    constructor
    · rcases (h.2 ω).2 with hs | hs
      · have h1 : -(ε * (|ζ ω| + |θ| * |z ω|)) ≤ ε * (ζ ω - θ * z ω) := by
          have : |ζ ω - θ * z ω| ≤ |ζ ω| + |θ| * |z ω| := by
            rw [← abs_mul]
            exact abs_sub _ _
          nlinarith [neg_abs_le (ζ ω - θ * z ω)]
        nlinarith
      · nlinarith
    · rcases (h.2 ω).1 with hm | hm
      · nlinarith [neg_abs_le (ζ ω)]
      · nlinarith
  refine ⟨fun n => ?_, domainCon_roll hcon.2 hne h₁.1 h₂.1 hd₁ hd₂⟩
  filter_upwards [hcon.1 n] with ω ⟨hc1, hc2⟩
  by_cases h1 : n = t₁
  · subst h1
    simp only [rollC, ↓reduceIte, hne, add_zero]
    exact hone h₁ hε₁ ω hc1 hc2
  · by_cases h2 : n = t₂
    · subst h2
      simp only [rollC, ↓reduceIte, h1, zero_add]
      exact hone h₂ hε₂ ω hc1 hc2
    · simp only [rollC, h1, h2, ↓reduceIte, add_zero, mul_zero]
      exact ⟨hc1, hc2⟩

/-! ### One multiplier for all one-sided deviations -/

/-- Cochrane (2023), (19.24)–(19.26), p. 449: a localization of positive probability exists at
every date when the plan lies in the open domain. -/
theorem exists_loc_pos {U : Set (ℝ × ℝ)} (hU : IsOpen U) {Λ P c m : ℕ → Ω → ℝ}
    (hdom : DomainCon S U c m) (t : ℕ) : ∃ K : ℕ, 0 < S.μ {ω | Loc S U Λ P c m t K ω} := by
  by_contra hno
  push Not at hno
  have h0 : ∀ K : ℕ, S.μ {ω | Loc S U Λ P c m t K ω} = 0 := fun K =>
    nonpos_iff_eq_zero.1 (hno K)
  have hU0 := measure_iUnion_null h0
  have hall := ae_exists_loc (Λ := Λ) (P := P) hU hdom t
  rw [ae_iff] at hall
  have : S.μ Set.univ = 0 := by
    refine measure_mono_null (fun ω _ => ?_) (measure_union_null hU0 hall)
    by_cases h : ∃ K, Loc S U Λ P c m t K ω
    · obtain ⟨K, hK⟩ := h
      exact Or.inl (Set.mem_iUnion.2 ⟨K, hK⟩)
    · exact Or.inr h
  simp at this

/-- Cochrane (2023), (19.15), p. 441: the interest cost is at most one, `ι_t ≤ 1` (the bond price
is nonnegative), almost surely. -/
theorem iota_le_one {Λ P : ℕ → Ω → ℝ} (hp : PriceWeak S Λ P) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, iota S Λ P t ω ≤ 1 := by
  have h0 : 0 ≤ᵐ[S.μ] pk Λ P (t + 1) := Eventually.of_forall fun ω => (hp.pk_pos _ ω).le
  filter_upwards [condExp_nonneg (m := S.𝓕 t) h0] with ω hω
  simp only [iota, bondPrice]
  have := div_nonneg hω (hp.pk_pos t ω).le
  linarith

/-- Cochrane (2023), (19.31), p. 450 and p. 449 (Karush–Kuhn–Tucker conditions), **one multiplier
for all one-sided deviations**: at a cash-in-advance optimum (utility `C¹` on the open set `I`
with `u' > 0`, `V > 0`, only `PriceWeak` prices), there is one constant `λ > 0` such that every
one-sided localized deviation `(z, ζ)` at every date satisfies
`βᵗE[u'(c_t)z] ≤ λE[Λ_t(z + ι_tζ)]` (its utility gain is at most `λ` times its cost). -/
theorem cia_one_sided {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hu : ∀ x ∈ I, HasDerivAt u (u' x) x) (hu' : ContinuousOn u' I)
    (hupos : ∀ x ∈ I, 0 < u' x) {V : ℝ} (hV : 0 < V) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ}
    (hopt : Optimal S β (fun x _ => u x) (CIAConD S V I y) Λ P y s N0 a0 c m a)
    (hp : PriceWeak S Λ P) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ (t K : ℕ) (B : ℝ) (z ζ : Ω → ℝ),
      OneTest S (I ×ˢ Set.univ) V Λ P y c m t K B z ζ →
      β ^ t * ∫ ω, u' (c t ω) * z ω ∂S.μ ≤
        lam * ∫ ω, Λ t ω * (z ω + iota S Λ P t ω * ζ ω) ∂S.μ := by
  have hC := c1On_cons hI hu hu'
  set U : Set (ℝ × ℝ) := I ×ˢ Set.univ with hUdef
  have hfeas := hopt.1
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have hcon := hopt.2.1
  have hdom := hopt.2.1.2
  have hnp := hfeas.2.2.2.2.2.2.2.2.2
  set θ : ℝ := 1 / V - 1 with hθ
  set Ct : ℕ → (Ω → ℝ) × (Ω → ℝ) → Prop := fun t v =>
    ∃ (K : ℕ) (B : ℝ), OneTest S U V Λ P y c m t K B v.1 v.2 with hCt
  set Lu : ℕ → (Ω → ℝ) × (Ω → ℝ) → ℝ := fun t v => β ^ t * ∫ ω, (u' (c t ω) * v.1 ω +
    0 * v.2 ω) ∂S.μ with hLu
  set Lp : ℕ → (Ω → ℝ) × (Ω → ℝ) → ℝ := fun t v =>
    ∫ ω, Λ t ω * (v.1 ω + iota S Λ P t ω * v.2 ω) ∂S.μ with hLp
  have hucU : ContinuousOn (fun p : ℝ × ℝ => u' p.1) U := hC.2.2.1
  have iu : ∀ t v, Ct t v → Integrable (fun ω => u' (c t ω) * v.1 ω + 0 * v.2 ω) S.μ := by
    rintro t v ⟨K, B, h⟩
    exact (h.1.integrable_util hC.1 hca hma hucU).1.add ((integrable_zero _ _ _).congr
      (Eventually.of_forall fun ω => by simp))
  have ip : ∀ t v, Ct t v → Integrable (fun ω => Λ t ω * (v.1 ω + iota S Λ P t ω * v.2 ω))
      S.μ := by
    rintro t v ⟨K, B, h⟩
    have := (h.1.integrable hp).2.2.2
    refine this.neg.congr (Eventually.of_forall fun ω => ?_)
    simp [rollX]
  have hXLp : ∀ t v, ∫ ω, rollX S Λ P t v.1 v.2 ω ∂S.μ = -Lp t v := fun t v => by
    rw [hLp, ← integral_neg]
    rfl
  -- test directions at date 0 of either sign
  have hι0 : ∀ᵐ ω ∂S.μ, 0 ≤ iota S Λ P 0 ω :=
    cia_iota_nonneg hβ hI hu hu' hopt hp 0 (by
      filter_upwards [hdom 0] with ω hω
      exact hupos _ hω.1)
  have hι1 := iota_le_one hp 0
  obtain ⟨K, hKpos⟩ := exists_loc_pos (Λ := Λ) (P := P) hC.1 hdom 0
  set L₀ := {ω | Loc S U Λ P c m 0 K ω} with hL₀
  have hLm := measurableSet_loc (U := U) hp hca hma 0 K
  set z₀ : Ω → ℝ := L₀.indicator (fun _ => 1) with hz₀
  have hz₀0 : ∀ ω, 0 ≤ z₀ ω := fun ω => by
    simp only [hz₀]
    by_cases h : ω ∈ L₀
    · rw [Set.indicator_of_mem h]
      norm_num
    · rw [Set.indicator_of_notMem h]
  have hroll : ∀ (a b : ℝ), RollTest S U Λ P c m 0 K (|a| + |b|) (fun ω => a * z₀ ω)
      (fun ω => b * z₀ ω) := by
    intro a b
    refine ⟨(stronglyMeasurable_const.indicator hLm).const_mul a,
      (stronglyMeasurable_const.indicator hLm).const_mul b, fun ω => ?_⟩
    by_cases hω : ω ∈ L₀
    · right
      simp only [hz₀, Set.indicator_of_mem hω, mul_one]
      exact ⟨hω, by linarith [abs_nonneg b], by linarith [abs_nonneg a]⟩
    · left
      simp [hz₀, Set.indicator_of_notMem hω]
  have hplus : OneTest S U V Λ P y c m 0 K (|1| + |max 0 θ|) (fun ω => 1 * z₀ ω)
      (fun ω => max 0 θ * z₀ ω) :=
    ⟨hroll 1 (max 0 θ), fun ω => ⟨Or.inr (mul_nonneg (le_max_left _ _) (hz₀0 ω)),
      Or.inr (by nlinarith [le_max_right 0 θ, hz₀0 ω])⟩⟩
  have hminus : OneTest S U V Λ P y c m 0 K (|-1| + |max 0 (-θ)|) (fun ω => -1 * z₀ ω)
      (fun ω => max 0 (-θ) * z₀ ω) :=
    ⟨hroll (-1) (max 0 (-θ)), fun ω => ⟨Or.inr (mul_nonneg (le_max_left _ _) (hz₀0 ω)),
      Or.inr (by nlinarith [le_max_right 0 (-θ), hz₀0 ω])⟩⟩
  have hzi : Integrable (fun ω => Λ 0 ω * z₀ ω) S.μ := ((hroll 1 0).integrable hp).1.congr
    (Eventually.of_forall fun ω => by simp)
  have hc₀pos : 0 < ∫ ω, Λ 0 ω * z₀ ω ∂S.μ := by
    rw [integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun ω =>
      mul_nonneg (hp.2.2.1 0 ω).le (hz₀0 ω)) hzi]
    refine lt_of_lt_of_le hKpos (measure_mono fun ω hω => ?_)
    simp only [Function.mem_support, hz₀, Set.indicator_of_mem hω, mul_one]
    exact (hp.2.2.1 0 ω).ne'
  have hθ1 : max 0 (-θ) < 1 := max_lt one_pos (by
    have : 0 < 1 / V := one_div_pos.2 hV
    linarith)
  obtain ⟨lam, hlam⟩ := lagrange_cone (V := (Ω → ℝ) × (Ω → ℝ)) Ct Lu Lp
    (fun t => ⟨0, 0, oneTest_zero U V Λ P y c m t 0 0⟩)
    (fun t v w a ha ⟨K, B, h⟩ ⟨K', B', h'⟩ => ⟨_, _, h.comb h' ha⟩)
    (fun t v w a _ hv hw => by
      have e : ∀ ω, (v + a • w).1 ω = v.1 ω + a * w.1 ω := fun ω => rfl
      have e' : ∀ ω, (v + a • w).2 ω = v.2 ω + a * w.2 ω := fun ω => rfl
      have h1 := integral_add (iu t v hv) ((iu t w hw).const_mul a)
      rw [integral_const_mul] at h1
      simp only [hLu, e, e']
      rw [mul_left_comm a, ← mul_add, ← h1]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring))
    (fun t v w a _ hv hw => by
      have e : ∀ ω, (v + a • w).1 ω = v.1 ω + a * w.1 ω := fun ω => rfl
      have e' : ∀ ω, (v + a • w).2 ω = v.2 ω + a * w.2 ω := fun ω => rfl
      have h1 := integral_add (ip t v hv) ((ip t w hw).const_mul a)
      rw [integral_const_mul] at h1
      simp only [hLp, e, e']
      rw [← h1]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring))
    (fun t₁ t₂ hne v w ⟨K₁, B₁, h₁⟩ ⟨K₂, B₂, h₂⟩ hsum => by
      obtain ⟨r, hr, φ, hφ0, hφd, hφle⟩ := roll_gain hβ hC hopt hp hne h₁.1 h₂.1
      set a₁ : ℝ := 1 / (2 * ((K₁ : ℝ) + 1)) / (|B₁| + 1) with ha₁
      set a₂ : ℝ := 1 / (2 * ((K₂ : ℝ) + 1)) / (|B₂| + 1) with ha₂
      set b₁ : ℝ := 1 / ((K₁ : ℝ) + 1) / ((|θ| + 1) * (|B₁| + 1)) with hb₁
      set b₂ : ℝ := 1 / ((K₂ : ℝ) + 1) / ((|θ| + 1) * (|B₂| + 1)) with hb₂
      set η := min r (min (min a₁ a₂) (min b₁ b₂)) with hη
      have hη0 : 0 < η := lt_min hr (lt_min (lt_min (by positivity) (by positivity))
        (lt_min (by positivity) (by positivity)))
      have hD := slope_nonpos hφd hφ0 hη0 fun ε hε0 hεη => by
        have hε : |ε| = ε := abs_of_pos hε0
        have hεa₁ : ε < a₁ := lt_of_lt_of_le hεη
          ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
        have hεa₂ : ε < a₂ := lt_of_lt_of_le hεη
          ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
        have hεb₁ : ε < b₁ := lt_of_lt_of_le hεη
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
        have hεb₂ : ε < b₂ := lt_of_lt_of_le hεη
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
        refine hφle ε (by rw [hε]; exact lt_of_lt_of_le hεη (min_le_left _ _))
          (ciaConD_roll hcon hne h₁ h₂ hε0.le ((lt_div_iff₀ (by positivity)).1 hεb₁)
            ((lt_div_iff₀ (by positivity)).1 hεb₂)
            (by rw [hε]; exact (lt_div_iff₀ (by positivity)).1 hεa₁)
            (by rw [hε]; exact (lt_div_iff₀ (by positivity)).1 hεa₂)) fun δ hδ => ?_
        have e := hXLp t₁ v
        have e' := hXLp t₂ w
        rw [e, e', ← neg_add, hsum, neg_zero, mul_zero]
        simpa using hnp δ hδ
      exact hD)
    ⟨0, (fun ω => 1 * z₀ ω, fun ω => max 0 θ * z₀ ω), ⟨K, _, hplus⟩, by
      refine lt_of_lt_of_le hc₀pos (integral_mono_ae hzi (ip 0 _ ⟨K, _, hplus⟩) ?_)
      filter_upwards [hι0] with ω hω
      have := mul_nonneg (mul_nonneg hω (le_max_left 0 θ)) (hz₀0 ω)
      have hΛ := (hp.2.2.1 0 ω).le
      nlinarith⟩
    ⟨0, (fun ω => -1 * z₀ ω, fun ω => max 0 (-θ) * z₀ ω), ⟨K, _, hminus⟩, by
      have hle : ∫ ω, Λ 0 ω * ((fun ω => -1 * z₀ ω, fun ω => max 0 (-θ) * z₀ ω).1 ω +
          iota S Λ P 0 ω * (fun ω => -1 * z₀ ω, fun ω => max 0 (-θ) * z₀ ω).2 ω) ∂S.μ ≤
          ∫ ω, -(1 - max 0 (-θ)) * (Λ 0 ω * z₀ ω) ∂S.μ := by
        refine integral_mono_ae (ip 0 _ ⟨K, _, hminus⟩) (hzi.const_mul _) ?_
        filter_upwards [hι1] with ω hω
        have hΛz := mul_nonneg (hp.2.2.1 0 ω).le (hz₀0 ω)
        have hm0 := le_max_left 0 (-θ)
        nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hω hm0) hΛz]
      rw [integral_const_mul] at hle
      have : 0 < 1 - max 0 (-θ) := by linarith
      nlinarith⟩
  -- the multiplier is positive
  have hLuplus : 0 < Lu 0 (fun ω => 1 * z₀ ω, fun ω => max 0 θ * z₀ ω) := by
    simp only [hLu, pow_zero, one_mul, zero_mul, add_zero]
    have hi : Integrable (fun ω => u' (c 0 ω) * z₀ ω) S.μ :=
      ((hroll 1 0).integrable_util hC.1 hca hma hucU).1.congr
        (Eventually.of_forall fun ω => by simp)
    rw [integral_pos_iff_support_of_nonneg_ae ?_ hi]
    · refine lt_of_lt_of_le hKpos (measure_mono_ae ?_)
      filter_upwards [hdom 0] with ω hω hL
      simp only [Function.mem_support, hz₀, Set.indicator_of_mem hL, mul_one]
      exact (hupos _ hω.1).ne'
    · filter_upwards [hdom 0] with ω hω
      simp only [Pi.zero_apply]
      exact mul_nonneg (hupos _ hω.1).le (by simpa using hz₀0 ω)
  have hLpplus : 0 < Lp 0 (fun ω => 1 * z₀ ω, fun ω => max 0 θ * z₀ ω) := by
    refine lt_of_lt_of_le hc₀pos (integral_mono_ae hzi
      (ip 0 (fun ω => 1 * z₀ ω, fun ω => max 0 θ * z₀ ω) ⟨K, _, hplus⟩) ?_)
    filter_upwards [hι0] with ω hω
    have := mul_nonneg (mul_nonneg hω (le_max_left 0 θ)) (hz₀0 ω)
    have hΛ := (hp.2.2.1 0 ω).le
    nlinarith
  have hlam0 : 0 < lam := by
    have h := hlam 0 (fun ω => 1 * z₀ ω, fun ω => max 0 θ * z₀ ω) ⟨K, _, hplus⟩
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  refine ⟨lam, hlam0, fun t K B z ζ h => ?_⟩
  have h' := hlam t (z, ζ) ⟨K, B, h⟩
  simp only [hLu, hLp, zero_mul, add_zero] at h'
  exact h'

/-! ### From one-sided tests to almost-sure inequalities -/

/-- Cochrane (2023), footnote 1, p. 440 (one-sided version of
`TidyR6HouseholdFOC.ae_eq_of_tests`): if `v` is continuous on the open domain, `w` is known at `t`
and bounded on each localization, the plan lies in the domain, and
`E[(v(c_t, m_t) − w)1_A] ≤ 0` for every event `A` known at `t` inside a localization, then
`v(c_t, m_t) ≤ w` almost surely. -/
theorem ae_le_of_tests {U : Set (ℝ × ℝ)} (hU : IsOpen U) {Λ P c m : ℕ → Ω → ℝ}
    (hp : PriceWeak S Λ P) (hca : StronglyAdapted S.𝓕 c) (hma : StronglyAdapted S.𝓕 m)
    (hdom : DomainCon S U c m) {t : ℕ} {v : ℝ × ℝ → ℝ} (hv : ContinuousOn v U) {w : Ω → ℝ}
    (hw : StronglyMeasurable[S.𝓕 t] w)
    (hwb : ∀ K : ℕ, ∃ C, ∀ ω, Loc S U Λ P c m t K ω → |w ω| ≤ C)
    (htest : ∀ (K : ℕ) (A : Set Ω), MeasurableSet[S.𝓕 t] A →
      A ⊆ {ω | Loc S U Λ P c m t K ω} →
      ∫ ω, (v (c t ω, m t ω) - w ω) * A.indicator (fun _ => 1) ω ∂S.μ ≤ 0) :
    ∀ᵐ ω ∂S.μ, v (c t ω, m t ω) ≤ w ω := by
  have hK : ∀ K : ℕ, ∀ᵐ ω ∂S.μ, Loc S U Λ P c m t K ω → v (c t ω, m t ω) ≤ w ω := by
    intro K
    obtain ⟨C₁, hC₁0, hC₁⟩ := kc_bound (U := U) K hv
    obtain ⟨C₂, hC₂⟩ := hwb K
    set G : Ω → ℝ := fun ω => U.indicator v (c t ω, m t ω) - w ω with hG
    have hGm : StronglyMeasurable[S.𝓕 t] G :=
      (((measurable_indicator_of_continuousOn hU hv).comp ((hca t).measurable.prodMk
        (hma t).measurable)).sub hw.measurable).stronglyMeasurable
    set A := {ω | Loc S U Λ P c m t K ω} ∩ {ω | 0 < G ω} with hA
    have hAm : MeasurableSet[S.𝓕 t] A := (measurableSet_loc (U := U) hp hca hma t K).inter
      (measurableSet_lt measurable_const hGm.measurable)
    have hGA : ∀ ω, ω ∈ A → G ω = v (c t ω, m t ω) - w ω := fun ω hω => by
      rw [hG]
      simp only
      rw [Set.indicator_of_mem (kc_subset U K (good_mem_kc hω.1.1))]
    have h0 := htest K A hAm Set.inter_subset_left
    have heq : (fun ω => (v (c t ω, m t ω) - w ω) * A.indicator (fun _ => 1) ω) =
        A.indicator G := by
      funext ω
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hGA ω hω, mul_one]
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, mul_zero]
    rw [heq] at h0
    have hnn : 0 ≤ᵐ[S.μ] A.indicator G := Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]
        exact hω.2.le
      · rw [Set.indicator_of_notMem hω]
        simp
    have hint : Integrable (A.indicator G) S.μ := by
      refine Integrable.of_bound ((hGm.mono (S.𝓕.le t)).aestronglyMeasurable.indicator
        (S.𝓕.le t _ hAm)) (C₁ + |C₂|) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, hGA ω hω]
        exact (abs_sub _ _).trans (add_le_add (hC₁ _ (good_mem_kc hω.1.1))
          ((hC₂ ω hω.1).trans (le_abs_self _)))
      · rw [Set.indicator_of_notMem hω, abs_zero]
        exact add_nonneg hC₁0 (abs_nonneg _)
    have hzero : ∫ ω, A.indicator G ω ∂S.μ = 0 :=
      le_antisymm h0 (integral_nonneg_of_ae hnn)
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hzero] with ω hω hl
    by_contra hlt
    rw [not_le] at hlt
    have hGpos : 0 < G ω := by
      rw [hG]
      simp only
      rw [Set.indicator_of_mem (kc_subset U K (good_mem_kc hl.1))]
      linarith
    have hmem : ω ∈ A := ⟨hl, hGpos⟩
    have := hω
    rw [Pi.zero_apply, Set.indicator_of_mem hmem] at this
    linarith
  filter_upwards [ae_all_iff.2 hK, ae_exists_loc (Λ := Λ) (P := P) hU hdom t] with ω h1 h2
  obtain ⟨K, hl⟩ := h2
  exact h1 K hl

/-! ### The Karush–Kuhn–Tucker conditions -/

/-- Cochrane (2023), (19.24)–(19.26), p. 449 (KKT multipliers): the multiplier on the cash
constraint per unit of `λΛ_t`: zero where the constraint is slack, `ι_t` where money is positive
and the constraint binds, and at a corner the value `(G − λΛ)/(λΛθ)` (with `G = βᵗu'(c_t)`)
that makes the Euler equation exact. -/
noncomputable def kktMu (θ lam G Λt ι m sl : ℝ) : ℝ :=
  if 0 < m then (if 0 < sl then 0 else ι) else
    (if 0 < sl then 0 else if θ = 0 then 0 else (G - lam * Λt) / (lam * Λt * θ))

/-- Cochrane (2023), (19.24)–(19.26) and (19.31), pp. 449–450: **the KKT conditions at a state
from the first-order conditions on each region.** With `λ, Λ > 0`, money and slack
nonnegative, `ι ≥ 0`, the wedge Euler equation where money is positive, the plain Euler
equation where the constraint is slack, `λΛι = 0` where both hold, and the two one-sided bounds,
the multiplier `μ = kktMu …` and `ν = ι − μ` satisfy `μ, ν ≥ 0`, `ι = μ + ν`, `μ·slack = 0`,
`ν·m = 0` and `G = λΛ(1 + θμ)`. -/
theorem kkt_pointwise {θ lam G Λt ι m sl : ℝ} (hlam : 0 < lam) (hΛ : 0 < Λt) (hm : 0 ≤ m)
    (hsl : 0 ≤ sl) (hι : 0 ≤ ι) (hR1 : 0 < m → G = lam * (Λt * (1 + ι * θ)))
    (hR2 : 0 < sl → G = lam * (Λt * (1 + ι * 0)))
    (hR3 : 0 < m → 0 < sl → 0 = lam * (Λt * (0 + ι * 1)))
    (hR4a : G ≤ lam * (Λt * (1 + ι * max 0 θ)))
    (hR4b : -G ≤ lam * (Λt * (-1 + ι * max 0 (-θ)))) :
    0 ≤ kktMu θ lam G Λt ι m sl ∧ 0 ≤ ι - kktMu θ lam G Λt ι m sl ∧
      ι = kktMu θ lam G Λt ι m sl + (ι - kktMu θ lam G Λt ι m sl) ∧
      kktMu θ lam G Λt ι m sl * sl = 0 ∧ (ι - kktMu θ lam G Λt ι m sl) * m = 0 ∧
      G = lam * (Λt * (1 + θ * kktMu θ lam G Λt ι m sl)) := by
  have hLΛ : 0 < lam * Λt := mul_pos hlam hΛ
  unfold kktMu
  by_cases hm0 : 0 < m
  · by_cases hs0 : 0 < sl
    · simp only [hm0, hs0, ↓reduceIte]
      have hι0 : ι = 0 := by
        have := hR3 hm0 hs0
        have h2 : lam * Λt * ι = 0 := by linarith
        rcases mul_eq_zero.1 h2 with h | h
        · exact absurd h hLΛ.ne'
        · exact h
      refine ⟨le_rfl, by linarith, by ring, by ring, by rw [hι0]; ring, ?_⟩
      rw [hR2 hs0]
      ring
    · have hsl0 : sl = 0 := le_antisymm (not_lt.1 hs0) hsl
      simp only [hm0, hs0, ↓reduceIte]
      refine ⟨hι, by linarith, by ring, by rw [hsl0]; ring, by ring, ?_⟩
      rw [hR1 hm0]
      ring
  · have hm00 : m = 0 := le_antisymm (not_lt.1 hm0) hm
    by_cases hs0 : 0 < sl
    · simp only [hm0, hs0, ↓reduceIte]
      refine ⟨le_rfl, by linarith, by ring, by ring, by rw [hm00]; ring, ?_⟩
      rw [hR2 hs0]
      ring
    · have hsl0 : sl = 0 := le_antisymm (not_lt.1 hs0) hsl
      simp only [hm0, hs0, ↓reduceIte]
      by_cases hθ : θ = 0
      · simp only [hθ, ↓reduceIte, max_self, mul_zero, add_zero, neg_zero] at hR4a hR4b ⊢
        refine ⟨le_rfl, by linarith, by ring, by ring, by rw [hm00]; ring, by nlinarith⟩
      · simp only [hθ, ↓reduceIte]
        have hfoc : G = lam * (Λt * (1 + θ * ((G - lam * Λt) / (lam * Λt * θ)))) := by
          field_simp
          ring
        rcases lt_or_gt_of_ne hθ with hneg | hpos
        · have h1 : max 0 θ = 0 := max_eq_left hneg.le
          have h2 : max 0 (-θ) = -θ := max_eq_right (by linarith)
          rw [h1] at hR4a
          rw [h2] at hR4b
          have hd : lam * Λt * θ < 0 := mul_neg_of_pos_of_neg hLΛ hneg
          refine ⟨div_nonneg_of_nonpos (by nlinarith) hd.le, ?_, by ring, by rw [hsl0]; ring,
            by rw [hm00]; ring, hfoc⟩
          rw [sub_nonneg, div_le_iff_of_neg hd]
          nlinarith
        · have h1 : max 0 θ = θ := max_eq_right hpos.le
          have h2 : max 0 (-θ) = 0 := max_eq_left (by linarith)
          rw [h1] at hR4a
          rw [h2] at hR4b
          have hd : 0 < lam * Λt * θ := mul_pos hLΛ hpos
          refine ⟨div_nonneg (by nlinarith) hd.le, ?_, by ring, by rw [hsl0]; ring,
            by rw [hm00]; ring, hfoc⟩
          rw [sub_nonneg, div_le_iff₀ hd]
          nlinarith

/-- Cochrane (2023), (19.24)–(19.26), (19.31) and (19.33), pp. 449–451, **the KKT conditions are
necessary at a cash-in-advance optimum, everywhere.** With `u` `C¹` on the open set `I`,
`u' > 0` on `I`, `V > 0` and only `PriceWeak` prices, there are a constant `λ > 0` and processes
`μ, ν` such that almost surely at every date `μ_t, ν_t ≥ 0`, `ι_t = μ_t + ν_t`,
`μ_t(m_t − (1/V − 1)c_t − y_t) = 0`, `ν_tm_t = 0` and `βᵗu'(c_t) = λΛ_t(1 + (1/V − 1)μ_t)`:
exactly the hypotheses of `TidyR6HouseholdCIA.cia_optimal_of_kkt`. No restriction on where money
is zero. -/
theorem cia_kkt_necessary {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hu : ∀ x ∈ I, HasDerivAt u (u' x) x) (hu' : ContinuousOn u' I)
    (hupos : ∀ x ∈ I, 0 < u' x) {V : ℝ} (hV : 0 < V) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ}
    (hopt : Optimal S β (fun x _ => u x) (CIAConD S V I y) Λ P y s N0 a0 c m a)
    (hp : PriceWeak S Λ P) (hya : StronglyAdapted S.𝓕 y) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ μ ν : ℕ → Ω → ℝ, ∀ t, ∀ᵐ ω ∂S.μ,
      0 ≤ μ t ω ∧ 0 ≤ ν t ω ∧ iota S Λ P t ω = μ t ω + ν t ω ∧
      μ t ω * (m t ω - ((1 / V - 1) * c t ω + y t ω)) = 0 ∧ ν t ω * m t ω = 0 ∧
      β ^ t * u' (c t ω) = lam * (Λ t ω * (1 + (1 / V - 1) * μ t ω)) := by
  have hC := c1On_cons hI hu hu'
  set U : Set (ℝ × ℝ) := I ×ˢ Set.univ with hUdef
  have hfeas := hopt.1
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have hcia := hopt.2.1.1
  have hdom := hopt.2.1.2
  set θ : ℝ := 1 / V - 1 with hθ
  obtain ⟨lam, hlam0, hone⟩ := cia_one_sided hβ hI hu hu' hupos hV hopt hp
  have hucU : ContinuousOn (fun p : ℝ × ℝ => u' p.1) U := hC.2.2.1
  have hvU : ∀ t : ℕ, ContinuousOn (fun p : ℝ × ℝ => β ^ t * u' p.1) U := fun t =>
    hucU.const_smul (β ^ t)
  -- integrability of a test's two integrands
  have hint : ∀ {t K : ℕ} {B : ℝ} {z ζ : Ω → ℝ}, RollTest S U Λ P c m t K B z ζ →
      Integrable (fun ω => u' (c t ω) * z ω) S.μ ∧
        Integrable (fun ω => Λ t ω * (z ω + iota S Λ P t ω * ζ ω)) S.μ := by
    intro t K B z ζ h
    refine ⟨(h.integrable_util hC.1 hca hma hucU).1, ?_⟩
    have := (h.integrable hp).2.2.2
    refine this.neg.congr (Eventually.of_forall fun ω => ?_)
    simp [rollX]
  -- scalar tests, scaled, are roll tests
  have hroll : ∀ {t K : ℕ} {B : ℝ} {z : Ω → ℝ} (a b : ℝ), StronglyMeasurable[S.𝓕 t] z →
      (∀ ω, z ω = 0 ∨ (Loc S U Λ P c m t K ω ∧ |z ω| ≤ B)) →
      RollTest S U Λ P c m t K (|B| * (|a| + |b| + 1)) (fun ω => a * z ω)
        (fun ω => b * z ω) := by
    intro t K B z a b hz hzs
    refine ⟨hz.const_mul a, hz.const_mul b, fun ω => ?_⟩
    rcases hzs ω with h0 | ⟨hl, hzB⟩
    · left
      simp [h0]
    · right
      have hzB' : |z ω| ≤ |B| := hzB.trans (le_abs_self _)
      refine ⟨hl, ?_, ?_⟩
      · rw [abs_mul]
        nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg B, abs_nonneg (z ω)]
      · rw [abs_mul]
        nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg B, abs_nonneg (z ω)]
  -- building one-sided tests from scalar tests
  have hmk : ∀ {t K : ℕ} {B : ℝ} {z : Ω → ℝ} {E : Set Ω} (a b : ℝ),
      StronglyMeasurable[S.𝓕 t] z →
      (∀ ω, z ω = 0 ∨ ((Loc S U Λ P c m t K ω ∧ ω ∈ E) ∧ |z ω| ≤ B)) →
      (∀ ω, ω ∈ E → 1 / ((K : ℝ) + 1) ≤ m t ω ∨ b = 0) →
      (∀ ω, ω ∈ E → 1 / ((K : ℝ) + 1) ≤ m t ω - (θ * c t ω + y t ω) ∨ θ * a = b) →
      OneTest S U V Λ P y c m t K (|B| * (|a| + |b| + 1)) (fun ω => a * z ω)
        (fun ω => b * z ω) := by
    intro t K B z E a b hz hzs hm hs
    have hzs' : ∀ ω, z ω = 0 ∨ (Loc S U Λ P c m t K ω ∧ |z ω| ≤ B) := fun ω =>
      (hzs ω).imp id fun h => ⟨h.1.1, h.2⟩
    refine ⟨hroll a b hz hzs', fun ω => ⟨?_, ?_⟩⟩
    · rcases hzs ω with h0 | ⟨⟨_, hE⟩, _⟩
      · exact Or.inr (by simp [h0])
      · rcases hm ω hE with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])
    · rcases hzs ω with h0 | ⟨⟨_, hE⟩, _⟩
      · exact Or.inr (by simp [h0])
      · rcases hs ω hE with h | h
        · exact Or.inl h
        · exact Or.inr (le_of_eq (by rw [← h]; ring))
  -- two-sided tests give equalities
  have heq2 : ∀ {t K : ℕ} {B : ℝ} {z : Ω → ℝ} (a b : ℝ),
      OneTest S U V Λ P y c m t K B (fun ω => a * z ω) (fun ω => b * z ω) →
      OneTest S U V Λ P y c m t K B (fun ω => -a * z ω) (fun ω => -b * z ω) →
      β ^ t * ∫ ω, u' (c t ω) * (a * z ω) ∂S.μ =
        lam * ∫ ω, Λ t ω * (a * z ω + iota S Λ P t ω * (b * z ω)) ∂S.μ := by
    intro t K B z a b h h'
    have h1 := hone t K B _ _ h
    have h2 := hone t K B _ _ h'
    have e1 : ∫ ω, u' (c t ω) * (-a * z ω) ∂S.μ = -∫ ω, u' (c t ω) * (a * z ω) ∂S.μ := by
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have e2 : ∫ ω, Λ t ω * (-a * z ω + iota S Λ P t ω * (-b * z ω)) ∂S.μ =
        -∫ ω, Λ t ω * (a * z ω + iota S Λ P t ω * (b * z ω)) ∂S.μ := by
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    rw [e1, e2] at h2
    linarith
  -- bounds and measurability of the multiplier terms
  have hwb : ∀ (t : ℕ) (x b : ℝ) (K : ℕ), ∃ C, ∀ ω, Loc S U Λ P c m t K ω →
      |lam * (Λ t ω * (x + iota S Λ P t ω * b))| ≤ C := fun t x b K =>
    ⟨|lam| * (K * (|x| + K * |b|)), fun ω hl => by
      rw [abs_mul, abs_mul, abs_of_pos (hp.2.2.1 t ω)]
      refine mul_le_mul_of_nonneg_left (mul_le_mul hl.2.1 ?_ (abs_nonneg _) (by positivity))
        (abs_nonneg _)
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hl.2.2.2 (abs_nonneg _)⟩
  have hwm : ∀ (t : ℕ) (x b : ℝ), StronglyMeasurable[S.𝓕 t]
      (fun ω => lam * (Λ t ω * (x + iota S Λ P t ω * b))) := fun t x b =>
    ((hp.1 t).mul (stronglyMeasurable_const.add ((hp.sm_iota t).mul
      stronglyMeasurable_const))).const_mul lam
  -- equalities on regions where two-sided deviations exist
  have hreg : ∀ (t : ℕ) (a b : ℝ) (E : ℕ → Set Ω), (∀ K, MeasurableSet[S.𝓕 t] (E K)) →
      Monotone E → (∀ K ω, ω ∈ E K → 1 / ((K : ℝ) + 1) ≤ m t ω ∨ b = 0) →
      (∀ K ω, ω ∈ E K → 1 / ((K : ℝ) + 1) ≤ m t ω - (θ * c t ω + y t ω) ∨ θ * a = b) →
      ∀ᵐ ω ∂S.μ, (∃ K, ω ∈ E K) →
        β ^ t * u' (c t ω) * a = lam * (Λ t ω * (a + iota S Λ P t ω * b)) := by
    intro t a b E hEm hEmono hm hs
    refine ae_eq_of_tests_on (v := fun p => β ^ t * u' p.1 * a)
      (w := fun ω => lam * (Λ t ω * (a + iota S Λ P t ω * b))) hC.1 hp hca hma hdom hEm hEmono
      ((hvU t).mul continuousOn_const) (hwm t a b) (hwb t a b) fun K B z hz hzs => ?_
    have h1 := hmk a b hz hzs (hm K) (hs K)
    have h2 := hmk (-a) (-b) hz hzs (fun ω hω => (hm K ω hω).imp id fun h => by rw [h]; ring)
      (fun ω hω => (hs K ω hω).imp id fun h => by rw [← h]; ring)
    rw [abs_neg, abs_neg] at h2
    have key2 := heq2 a b h1 h2
    obtain ⟨i1, i2⟩ := hint (hroll a b hz fun ω => (hzs ω).imp id fun h => ⟨h.1.1, h.2⟩)
    calc ∫ ω, ((fun p : ℝ × ℝ => β ^ t * u' p.1 * a) (c t ω, m t ω) -
          lam * (Λ t ω * (a + iota S Λ P t ω * b))) * z ω ∂S.μ
        = β ^ t * ∫ ω, u' (c t ω) * (a * z ω) ∂S.μ -
          lam * ∫ ω, Λ t ω * (a * z ω + iota S Λ P t ω * (b * z ω)) ∂S.μ := by
          rw [← integral_const_mul, ← integral_const_mul,
            ← integral_sub (i1.const_mul _) (i2.const_mul _)]
          exact integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)
      _ = 0 := by rw [key2]; ring
  -- inequalities from one-sided deviations
  have hineq : ∀ (t : ℕ) (a b : ℝ), 0 ≤ b → θ * a ≤ b →
      ∀ᵐ ω ∂S.μ, β ^ t * u' (c t ω) * a ≤ lam * (Λ t ω * (a + iota S Λ P t ω * b)) := by
    intro t a b hb hab
    refine ae_le_of_tests (v := fun p => β ^ t * u' p.1 * a)
      (w := fun ω => lam * (Λ t ω * (a + iota S Λ P t ω * b))) hC.1 hp hca hma hdom
      ((hvU t).mul continuousOn_const) (hwm t a b) (hwb t a b) fun K A hA hAsub => ?_
    set z : Ω → ℝ := A.indicator (fun _ => (1 : ℝ)) with hzdef
    have hz : StronglyMeasurable[S.𝓕 t] z := stronglyMeasurable_const.indicator hA
    have hz0 : ∀ ω, 0 ≤ z ω := fun ω => by
      by_cases h : ω ∈ A
      · rw [hzdef, Set.indicator_of_mem h]
        norm_num
      · rw [hzdef, Set.indicator_of_notMem h]
    have hzs : ∀ ω, z ω = 0 ∨ (Loc S U Λ P c m t K ω ∧ |z ω| ≤ 1) := fun ω => by
      by_cases h : ω ∈ A
      · right
        rw [hzdef, Set.indicator_of_mem h]
        exact ⟨hAsub h, by norm_num⟩
      · left
        rw [hzdef, Set.indicator_of_notMem h]
    have hTr := hroll a b hz hzs
    have hO : OneTest S U V Λ P y c m t K (|(1 : ℝ)| * (|a| + |b| + 1)) (fun ω => a * z ω)
        (fun ω => b * z ω) :=
      ⟨hTr, fun ω => ⟨Or.inr (mul_nonneg hb (hz0 ω)), Or.inr (by nlinarith [hz0 ω])⟩⟩
    have h := hone t K _ _ _ hO
    obtain ⟨i1, i2⟩ := hint hTr
    calc ∫ ω, ((fun p : ℝ × ℝ => β ^ t * u' p.1 * a) (c t ω, m t ω) -
          lam * (Λ t ω * (a + iota S Λ P t ω * b))) * z ω ∂S.μ
        = β ^ t * ∫ ω, u' (c t ω) * (a * z ω) ∂S.μ -
          lam * ∫ ω, Λ t ω * (a * z ω + iota S Λ P t ω * (b * z ω)) ∂S.μ := by
          rw [← integral_const_mul, ← integral_const_mul,
            ← integral_sub (i1.const_mul _) (i2.const_mul _)]
          exact integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)
      _ ≤ 0 := by linarith
  -- the regions
  set sl : ℕ → Ω → ℝ := fun t ω => m t ω - (θ * c t ω + y t ω) with hsl
  have hslm : ∀ t, StronglyMeasurable[S.𝓕 t] (sl t) := fun t =>
    (hma t).sub (((hca t).const_mul θ).add (hya t))
  have hmono : ∀ f : Ω → ℝ, Monotone (fun K : ℕ => {ω | 1 / ((K : ℝ) + 1) ≤ f ω}) := by
    intro f K K' hKK ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hc : (K : ℝ) ≤ K' := Nat.cast_le.2 hKK
    exact (one_div_le_one_div_of_le (by positivity) (by linarith)).trans hω
  have hEm : ∀ t (f : Ω → ℝ), StronglyMeasurable[S.𝓕 t] f → ∀ K : ℕ,
      MeasurableSet[S.𝓕 t] {ω | 1 / ((K : ℝ) + 1) ≤ f ω} := fun t f hf K =>
    measurableSet_le measurable_const hf.measurable
  have hexK : ∀ x : ℝ, 0 < x → ∃ K : ℕ, 1 / ((K : ℝ) + 1) ≤ x := fun x hx => by
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hx
    exact ⟨K, hK.le⟩
  refine ⟨lam, hlam0, fun t ω => kktMu θ lam (β ^ t * u' (c t ω)) (Λ t ω) (iota S Λ P t ω)
    (m t ω) (sl t ω), fun t ω => iota S Λ P t ω - kktMu θ lam (β ^ t * u' (c t ω)) (Λ t ω)
    (iota S Λ P t ω) (m t ω) (sl t ω), fun t => ?_⟩
  have hR1 := hreg t 1 θ (fun K => {ω | 1 / ((K : ℝ) + 1) ≤ m t ω}) (hEm t _ (hma t))
    (hmono _) (fun K ω hω => Or.inl hω) (fun K ω hω => Or.inr (by ring))
  have hR2 := hreg t 1 0 (fun K => {ω | 1 / ((K : ℝ) + 1) ≤ sl t ω}) (hEm t _ (hslm t))
    (hmono _) (fun K ω hω => Or.inr rfl) (fun K ω hω => Or.inl hω)
  have hR3 := hreg t 0 1 (fun K => {ω | 1 / ((K : ℝ) + 1) ≤ m t ω} ∩
    {ω | 1 / ((K : ℝ) + 1) ≤ sl t ω}) (fun K => (hEm t _ (hma t) K).inter (hEm t _ (hslm t) K))
    (fun K K' h ω hω => ⟨hmono _ h hω.1, hmono _ h hω.2⟩) (fun K ω hω => Or.inl hω.1)
    (fun K ω hω => Or.inl hω.2)
  have hR4a := hineq t 1 (max 0 θ) (le_max_left _ _) (by rw [mul_one]; exact le_max_right _ _)
  have hR4b := hineq t (-1) (max 0 (-θ)) (le_max_left _ _)
    (by rw [mul_neg_one]; exact le_max_right _ _)
  have hι : ∀ᵐ ω ∂S.μ, 0 ≤ iota S Λ P t ω :=
    cia_iota_nonneg hβ hI hu hu' hopt hp t (by
      filter_upwards [hdom t] with ω hω
      exact hupos _ hω.1)
  filter_upwards [hR1, hR2, hR3, hR4a, hR4b, hcia t, hι] with ω h1 h2 h3 h4a h4b hc hιω
  obtain ⟨hc1, hc2⟩ := hc
  exact kkt_pointwise hlam0 (hp.2.2.1 t ω) hc2 (by simp only [hsl]; linarith) hιω
    (fun hm0 => by
      obtain ⟨K, hK⟩ := hexK _ hm0
      have := h1 ⟨K, hK⟩
      linarith)
    (fun hs0 => by
      obtain ⟨K, hK⟩ := hexK _ hs0
      have := h2 ⟨K, hK⟩
      linarith)
    (fun hm0 hs0 => by
      obtain ⟨K₁, hK₁⟩ := hexK _ hm0
      obtain ⟨K₂, hK₂⟩ := hexK _ hs0
      have := h3 ⟨max K₁ K₂, hmono _ (le_max_left _ _) hK₁, hmono _ (le_max_right _ _) hK₂⟩
      linarith)
    (by linarith) (by linarith)


/-! ### The liminf transversality condition and the characterisation -/

/-- Cochrane (2023), (19.28), p. 449, **the liminf transversality condition at a cash-in-advance
optimum**: with `u` `C¹` on the open set `I`, `u' > 0` there, `V > 0` and `PriceWeak` prices,
the date-0 value of wealth satisfies the no-Ponzi bound and is below every `L > 0` infinitely
often (otherwise the household could consume more at date `0`, with the overnight money that
requires, and roll the debt over for ever). No concavity, reference plan or bounds. -/
theorem cia_liminf_tvc {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hu : ∀ x ∈ I, HasDerivAt u (u' x) x) (hu' : ContinuousOn u' I)
    (hupos : ∀ x ∈ I, 0 < u' x) {V : ℝ} {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ}
    (hopt : Optimal S β (fun x _ => u x) (CIAConD S V I y) Λ P y s N0 a0 c m a)
    (hp : PriceWeak S Λ P) :
    (∀ δ, 0 < δ → ∀ᶠ T in atTop, -δ ≤ wealthPV S Λ P N0 m a T) ∧
      ∀ L, 0 < L → ∃ᶠ T in atTop, wealthPV S Λ P N0 m a T < L := by
  have hC := c1On_cons hI hu hu'
  set U : Set (ℝ × ℝ) := I ×ˢ Set.univ with hUdef
  have hfeas := hopt.1
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have hcon := hopt.2.1
  have hdom := hopt.2.1.2
  have hnp := hfeas.2.2.2.2.2.2.2.2.2
  set θ : ℝ := 1 / V - 1 with hθ
  refine ⟨hnp, fun L hL => ?_⟩
  by_contra hcon'
  rw [Filter.not_frequently] at hcon'
  have hι0 : ∀ᵐ ω ∂S.μ, 0 ≤ iota S Λ P 0 ω :=
    cia_iota_nonneg hβ hI hu hu' hopt hp 0 (by
      filter_upwards [hdom 0] with ω hω
      exact hupos _ hω.1)
  obtain ⟨K, hKpos⟩ := exists_loc_pos (Λ := Λ) (P := P) hC.1 hdom 0
  set L₀ := {ω | Loc S U Λ P c m 0 K ω} with hL₀
  have hLm := measurableSet_loc (U := U) hp hca hma 0 K
  set z₀ : Ω → ℝ := L₀.indicator (fun _ => 1) with hz₀
  have hz₀0 : ∀ ω, 0 ≤ z₀ ω := fun ω => by
    simp only [hz₀]
    by_cases h : ω ∈ L₀
    · rw [Set.indicator_of_mem h]
      norm_num
    · rw [Set.indicator_of_notMem h]
  have hT : OneTest S U V Λ P y c m 0 K (|1| + |max 0 θ|) (fun ω => 1 * z₀ ω)
      (fun ω => max 0 θ * z₀ ω) := by
    refine ⟨⟨(stronglyMeasurable_const.indicator hLm).const_mul 1,
      (stronglyMeasurable_const.indicator hLm).const_mul _, fun ω => ?_⟩,
      fun ω => ⟨Or.inr (mul_nonneg (le_max_left _ _) (hz₀0 ω)),
        Or.inr (by nlinarith [le_max_right 0 θ, hz₀0 ω])⟩⟩
    by_cases hω : ω ∈ L₀
    · right
      simp only [hz₀, Set.indicator_of_mem hω, mul_one]
      exact ⟨hω, by linarith [abs_nonneg (max 0 θ)], by linarith [abs_nonneg (1 : ℝ)]⟩
    · left
      simp [hz₀, Set.indicator_of_notMem hω]
  have hT0 := oneTest_zero (S := S) U V Λ P y c m 1 0 0
  obtain ⟨r, hr, φ, hφ0, hφd, hφle⟩ := roll_gain hβ hC hopt hp (show (0 : ℕ) ≠ 1 by omega)
    hT.1 hT0.1
  -- the cost of the extra consumption
  have hzi : Integrable (fun ω => Λ 0 ω * z₀ ω) S.μ := (hT.1.integrable hp).1.congr
    (Eventually.of_forall fun ω => by simp)
  have hc₀pos : 0 < ∫ ω, Λ 0 ω * z₀ ω ∂S.μ := by
    rw [integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun ω =>
      mul_nonneg (hp.2.2.1 0 ω).le (hz₀0 ω)) hzi]
    refine lt_of_lt_of_le hKpos (measure_mono fun ω hω => ?_)
    simp only [Function.mem_support, hz₀, Set.indicator_of_mem hω, mul_one]
    exact (hp.2.2.1 0 ω).ne'
  set c₀ := ∫ ω, Λ 0 ω * (1 * z₀ ω + iota S Λ P 0 ω * (max 0 θ * z₀ ω)) ∂S.μ with hc₀
  have hXi := (hT.1.integrable hp).2.2.2
  have hc₀ge : ∫ ω, Λ 0 ω * z₀ ω ∂S.μ ≤ c₀ := by
    refine integral_mono_ae hzi (hXi.neg.congr (Eventually.of_forall fun ω => by
      simp [rollX])) ?_
    filter_upwards [hι0] with ω hω
    have := mul_nonneg (mul_nonneg hω (le_max_left 0 θ)) (hz₀0 ω)
    have hΛ := (hp.2.2.1 0 ω).le
    nlinarith
  have hc₀pos' : 0 < c₀ := lt_of_lt_of_le hc₀pos hc₀ge
  have hX : ∫ ω, rollX S Λ P 0 (fun ω => 1 * z₀ ω) (fun ω => max 0 θ * z₀ ω) ω ∂S.μ = -c₀ := by
    rw [hc₀, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp [rollX])
  have hX0 : ∫ ω, rollX S Λ P 1 0 0 ω ∂S.μ = 0 := by simp [rollX]
  -- the derivative is positive
  have hDpos : 0 < β ^ 0 * ∫ ω, (u' (c 0 ω) * (1 * z₀ ω) + 0 * (max 0 θ * z₀ ω)) ∂S.μ +
      β ^ 1 * ∫ ω, (u' (c 1 ω) * (0 : Ω → ℝ) ω + 0 * (0 : Ω → ℝ) ω) ∂S.μ := by
    simp only [Pi.zero_apply, mul_zero, add_zero, zero_mul, integral_zero, pow_zero, one_mul]
    have hi : Integrable (fun ω => u' (c 0 ω) * z₀ ω) S.μ :=
      (hT.1.integrable_util hC.1 hca hma hC.2.2.1).1.congr
        (Eventually.of_forall fun ω => by simp)
    rw [integral_pos_iff_support_of_nonneg_ae ?_ hi]
    · refine lt_of_lt_of_le hKpos (measure_mono_ae ?_)
      filter_upwards [hdom 0] with ω hω hL'
      simp only [Function.mem_support, hz₀, Set.indicator_of_mem hL', mul_one]
      exact (hupos _ hω.1).ne'
    · filter_upwards [hdom 0] with ω hω
      simp only [Pi.zero_apply]
      exact mul_nonneg (hupos _ hω.1).le (hz₀0 ω)
  set B₁ : ℝ := |1| + |max 0 θ| with hB₁
  set η := min r (min (min (1 / (2 * ((K : ℝ) + 1)) / (|B₁| + 1))
    (1 / (2 * ((0 : ℕ) + 1 : ℝ)) / (|(0 : ℝ)| + 1)))
    (min (1 / ((K : ℝ) + 1) / ((|θ| + 1) * (|B₁| + 1)))
      (min (1 / ((0 : ℕ) + 1 : ℝ) / ((|θ| + 1) * (|(0 : ℝ)| + 1))) (L / c₀)))) with hη
  have hη0 : 0 < η := lt_min hr (lt_min (lt_min (by positivity) (by positivity))
    (lt_min (by positivity) (lt_min (by positivity) (div_pos hL hc₀pos'))))
  have hDle := slope_nonpos hφd hφ0 hη0 fun ε hε0 hεη => by
    have hε : |ε| = ε := abs_of_pos hε0
    have g1 := lt_of_lt_of_le hεη (min_le_right _ _)
    have ga₁ := lt_of_lt_of_le g1 ((min_le_left _ _).trans (min_le_left _ _))
    have ga₂ := lt_of_lt_of_le g1 ((min_le_left _ _).trans (min_le_right _ _))
    have gb₁ := lt_of_lt_of_le g1 ((min_le_right _ _).trans (min_le_left _ _))
    have gb₂ := lt_of_lt_of_le g1 ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have gL := lt_of_lt_of_le g1 ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    refine hφle ε (by rw [hε]; exact lt_of_lt_of_le hεη (min_le_left _ _))
      (ciaConD_roll hcon (show (0 : ℕ) ≠ 1 by omega) hT hT0 hε0.le
        ((lt_div_iff₀ (by positivity)).1 gb₁) ((lt_div_iff₀ (by positivity)).1 gb₂)
        (by rw [hε]; exact (lt_div_iff₀ (by positivity)).1 ga₁)
        (by rw [hε]; exact (lt_div_iff₀ (by positivity)).1 ga₂)) fun δ hδ => ?_
    rw [hX, hX0]
    filter_upwards [hcon'] with T hT'
    rw [not_lt] at hT'
    have : ε * c₀ < L := (lt_div_iff₀ hc₀pos').1 gL
    linarith
  linarith

/-- Cochrane (2023), p. 453 ("first order conditions and transversality conditions are
necessary and sufficient") and (19.24)–(19.33), pp. 448–451, **the cash-in-advance household
optimum characterised.** Let `u` be `C¹` on the open set `I` of consumption levels, with the
supergradient inequality on `I` (concavity) and `u' > 0` there; `V > 0`; prices `PriceWeak`; the
endowment adapted with integrable values and taxes with integrable values. A feasible, admissible
plan satisfying the cash-in-advance, no-printing and domain constraints is optimal if and only if
there are a constant `λ > 0` and multipliers `μ, ν` satisfying the KKT conditions of
`TidyR6HouseholdCIA.cia_optimal_of_kkt` almost surely at every date, and the date-0 value of
wealth has liminf zero. -/
theorem cia_optimal_iff {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hu : ∀ x ∈ I, HasDerivAt u (u' x) x) (hu' : ContinuousOn u' I)
    (hupos : ∀ x ∈ I, 0 < u' x) (hsg : ∀ x ∈ I, ∀ x' ∈ I, u x' ≤ u x + u' x * (x' - x))
    {V : ℝ} (hV : 0 < V) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceWeak S Λ P) (hya : StronglyAdapted S.𝓕 y)
    (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ)
    (hf : Feasible S Λ P y s N0 a0 c m a) (hcon : CIAConD S V I y c m)
    (hadm : UAdmissible S β (fun n ω => u (c n ω))) :
    Optimal S β (fun x _ => u x) (CIAConD S V I y) Λ P y s N0 a0 c m a ↔
      ∃ lam : ℝ, 0 < lam ∧ (∃ μ ν : ℕ → Ω → ℝ, ∀ t, ∀ᵐ ω ∂S.μ,
        0 ≤ μ t ω ∧ 0 ≤ ν t ω ∧ iota S Λ P t ω = μ t ω + ν t ω ∧
        μ t ω * (m t ω - ((1 / V - 1) * c t ω + y t ω)) = 0 ∧ ν t ω * m t ω = 0 ∧
        β ^ t * u' (c t ω) = lam * (Λ t ω * (1 + (1 / V - 1) * μ t ω))) ∧
        ∀ L, 0 < L → ∃ᶠ T in atTop, wealthPV S Λ P N0 m a T < L := by
  constructor
  · intro hopt
    obtain ⟨lam, hlam, μ, ν, hkkt⟩ := cia_kkt_necessary hβ hI hu hu' hupos hV hopt hp hya
    exact ⟨lam, hlam, ⟨μ, ν, hkkt⟩, (cia_liminf_tvc hβ hI hu hu' hupos hopt hp).2⟩
  · rintro ⟨lam, hlam, ⟨μ, ν, hkkt⟩, hlim⟩
    exact cia_optimal_of_kkt hβ hsg hp hy hs hlam.le hf hcon hadm hkkt hlim

end Cochrane.Monetarism.TidyR6HouseholdCIAKKT
