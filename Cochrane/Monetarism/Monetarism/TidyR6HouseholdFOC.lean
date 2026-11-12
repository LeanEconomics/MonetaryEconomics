/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6HouseholdLocal

/-!
# The household first-order conditions without regularity hypotheses

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.3, pp. 439–441,
eqs. (19.9)–(19.14) and footnote 1, on a probability space (`HouseholdMeasure`). The earlier
derivation (`HouseholdMeasure.pair_foc`, `HouseholdMeasure.bundle_multiplier_const`,
`MoneyInUtilityMeasure.foc_1913`, `MoneyInUtilityMeasure.foc_1914`) assumed consumption and real
balances essentially bounded at each date, prices bounded and bounded away from zero
(`HouseholdMeasure.PriceRegular`) and a utility smooth on all of `ℝ²`, and it delivered a
multiplier `λ = u_c(0)/Λ_0` known at date `0`. Here none of these is needed.

## Main results

* `roll_gain`: two perpetual rollovers (`TidyR6HouseholdRoll.roll_homDev`) at different dates,
  localized where the plan is in a compact part of the utility domain and prices are moderate,
  change expected utility by `φ(ε)` with `φ(0) = 0` and
  `φ'(0) = βᵗ¹E[u_c z₁ + u_m ζ₁] + βᵗ²E[u_c z₂ + u_m ζ₂]`, and `φ(ε) ≤ 0` at an optimum whenever
  the perturbed plan satisfies the extra constraint and the shifted no-Ponzi condition.
* `lagrange`: an abstract Lagrange-multiplier lemma: if two linear functionals `Lu`, `Lp` on
  date-indexed test spaces satisfy `Lp_{t₁}(v) + Lp_{t₂}(w) = 0 ⇒ Lu_{t₁}(v) + Lu_{t₂}(w) = 0`
  for all dates `t₁ ≠ t₂`, then `Lu = λLp` with one constant `λ`.
* **`miu_multiplier`, (19.13)–(19.14) with one constant multiplier**: at an optimum of the
  money-in-utility household, for a utility `C¹` on an open domain `U` containing the plan, with
  merely `PriceWeak` prices, there is a single real `λ` with
  `βᵗu_c(c_t, m_t) = λΛ_t` and `βᵗu_m(c_t, m_t) = λΛ_tι_t` almost surely at every date. No
  boundedness of consumption, real balances or prices, and no smoothness outside `U`. The
  multiplier is a constant, not merely known at date `0`: the no-Ponzi condition of
  `HouseholdMeasure.Feasible` is unconditional, so wealth can be moved across date-0 states.
* `miu_liminf_tvc`: at such an optimum, if `u_c > 0` at some date, the date-0 value of wealth has
  `liminf_T E[pk_T(a_T + M_{T−1})] = 0`: the transversality condition holds along a subsequence
  with no concavity, no reference plan and no bounds (compare `TidyR6HouseholdTVC`).
-/

namespace Cochrane.Monetarism.TidyR6HouseholdFOC

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure HouseholdMeasure
  TidyR6HouseholdRoll TidyR6HouseholdLocal

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### Localized test deviations -/

variable (S) in
/-- Cochrane (2023), (19.9), p. 439: the domain constraint: almost surely at every date the plan
`(c_t, m_t)` lies in the domain `U` of the utility. -/
def DomainCon (U : Set (ℝ × ℝ)) (c m : ℕ → Ω → ℝ) : Prop := ∀ t, ∀ᵐ ω ∂S.μ, (c t ω, m t ω) ∈ U

variable (S) in
/-- Cochrane (2023), footnote 1, p. 440: the date-`t` localization at level `K`: `(c_t, m_t)` is
good for the domain `U` (`TidyR6HouseholdLocal.Good`) and `Λ_t`, `P_t`, `|ι_t|` are at most `K`. -/
def Loc (U : Set (ℝ × ℝ)) (Λ P c m : ℕ → Ω → ℝ) (t K : ℕ) (ω : Ω) : Prop :=
  Good U K (c t ω, m t ω) ∧ Λ t ω ≤ K ∧ P t ω ≤ K ∧ |iota S Λ P t ω| ≤ K

variable (S) in
/-- Cochrane (2023), footnote 1, p. 440: a test deviation at date `t`: `(z, ζ)` known at `t`,
vanishing off the localization `Loc t K` and bounded by `B` on it. -/
def RollTest (U : Set (ℝ × ℝ)) (Λ P c m : ℕ → Ω → ℝ) (t K : ℕ) (B : ℝ) (z ζ : Ω → ℝ) : Prop :=
  StronglyMeasurable[S.𝓕 t] z ∧ StronglyMeasurable[S.𝓕 t] ζ ∧
    ∀ ω, (z ω = 0 ∧ ζ ω = 0) ∨ (Loc S U Λ P c m t K ω ∧ |z ω| ≤ B ∧ |ζ ω| ≤ B)

/-- Cochrane (2023), footnote 1, p. 440: the localization is monotone in its level. -/
theorem loc_mono {U : Set (ℝ × ℝ)} {Λ P c m : ℕ → Ω → ℝ} {t K K' : ℕ} (h : K ≤ K') {ω : Ω}
    (hl : Loc S U Λ P c m t K ω) : Loc S U Λ P c m t K' ω := by
  have hc : (K : ℝ) ≤ K' := Nat.cast_le.2 h
  exact ⟨good_mono h hl.1, hl.2.1.trans hc, hl.2.2.1.trans hc, hl.2.2.2.trans hc⟩

/-- Cochrane (2023), footnote 1, p. 440: the localization is an event known at `t`. -/
theorem measurableSet_loc {U : Set (ℝ × ℝ)} {Λ P c m : ℕ → Ω → ℝ} (hp : PriceWeak S Λ P)
    (hca : StronglyAdapted S.𝓕 c) (hma : StronglyAdapted S.𝓕 m) (t K : ℕ) :
    MeasurableSet[S.𝓕 t] {ω | Loc S U Λ P c m t K ω} := by
  have h1 : MeasurableSet[S.𝓕 t] {ω | Good U K (c t ω, m t ω)} :=
    ((hca t).measurable.prodMk (hma t).measurable) (measurableSet_good U K)
  have h2 : MeasurableSet[S.𝓕 t] {ω | Λ t ω ≤ K} := measurableSet_le (hp.1 t).measurable
    measurable_const
  have h3 : MeasurableSet[S.𝓕 t] {ω | P t ω ≤ K} := measurableSet_le (hp.2.1 t).measurable
    measurable_const
  have h4 : MeasurableSet[S.𝓕 t] {ω | |iota S Λ P t ω| ≤ K} :=
    measurableSet_le (continuous_abs.measurable.comp (hp.sm_iota t).measurable) measurable_const
  exact h1.inter (h2.inter (h3.inter h4))

/-- Cochrane (2023), footnote 1, p. 440: if the plan lies in the open domain almost surely, then
almost surely it is localized at some level, at every date. -/
theorem ae_exists_loc {U : Set (ℝ × ℝ)} (hU : IsOpen U) {Λ P c m : ℕ → Ω → ℝ}
    (hdom : DomainCon S U c m) (t : ℕ) : ∀ᵐ ω ∂S.μ, ∃ K, Loc S U Λ P c m t K ω := by
  filter_upwards [hdom t] with ω hω
  obtain ⟨K₁, hK₁⟩ := exists_good hU hω
  refine ⟨max K₁ (max ⌈Λ t ω⌉₊ (max ⌈P t ω⌉₊ ⌈|iota S Λ P t ω|⌉₊)),
    good_mono (le_max_left _ _) hK₁, ?_, ?_, ?_⟩
  · refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (le_max_left _ _).trans (le_max_right _ _)
  · refine (Nat.le_ceil _).trans ?_
    exact_mod_cast ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  · refine (Nat.le_ceil _).trans ?_
    exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

/-- Cochrane (2023), footnote 1, p. 440: a test vanishes off its localization and is bounded on
it, so in particular its utility point is good. -/
theorem RollTest.good {U : Set (ℝ × ℝ)} {Λ P c m : ℕ → Ω → ℝ} {t K : ℕ} {B : ℝ}
    {z ζ : Ω → ℝ} (h : RollTest S U Λ P c m t K B z ζ) (ω : Ω) :
    (z ω = 0 ∧ ζ ω = 0) ∨ (Good U K (c t ω, m t ω) ∧ |z ω| ≤ B ∧ |ζ ω| ≤ B) :=
  (h.2.2 ω).imp id fun h' => ⟨h'.1.1, h'.2⟩

/-- Cochrane (2023), footnote 1, p. 440: the zero deviation is a test. -/
theorem rollTest_zero (U : Set (ℝ × ℝ)) (Λ P c m : ℕ → Ω → ℝ) (t K : ℕ) (B : ℝ) :
    RollTest S U Λ P c m t K B 0 0 :=
  ⟨stronglyMeasurable_const, stronglyMeasurable_const, fun _ => Or.inl ⟨rfl, rfl⟩⟩

/-- Cochrane (2023), footnote 1, p. 440: tests at the same date form a vector space: `v + aw` is a
test at the larger level with bound `|B| + |a||B'|`. -/
theorem RollTest.comb {U : Set (ℝ × ℝ)} {Λ P c m : ℕ → Ω → ℝ} {t K K' : ℕ} {B B' : ℝ}
    {z ζ z' ζ' : Ω → ℝ} (h : RollTest S U Λ P c m t K B z ζ)
    (h' : RollTest S U Λ P c m t K' B' z' ζ') (a : ℝ) :
    RollTest S U Λ P c m t (max K K') (|B| + |a| * |B'|) (fun ω => z ω + a * z' ω)
      (fun ω => ζ ω + a * ζ' ω) := by
  refine ⟨h.1.add (h'.1.const_mul a), h.2.1.add (h'.2.1.const_mul a), fun ω => ?_⟩
  have hb : ∀ x : ℝ, (x = 0 ∨ |x| ≤ B) → |x| ≤ |B| := fun x hx => by
    rcases hx with hx | hx
    · rw [hx, abs_zero]
      exact abs_nonneg _
    · exact hx.trans (le_abs_self _)
  have hb' : ∀ x : ℝ, (x = 0 ∨ |x| ≤ B') → |x| ≤ |B'| := fun x hx => by
    rcases hx with hx | hx
    · rw [hx, abs_zero]
      exact abs_nonneg _
    · exact hx.trans (le_abs_self _)
  have hsum : ∀ x y : ℝ, |x| ≤ |B| → |y| ≤ |B'| → |x + a * y| ≤ |B| + |a| * |B'| :=
    fun x y hx hy => (abs_add_le _ _).trans (add_le_add hx (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hy (abs_nonneg a)))
  rcases h.2.2 ω with h0 | ⟨hl, hz, hζ⟩ <;> rcases h'.2.2 ω with h0' | ⟨hl', hz', hζ'⟩
  · left
    simp [h0.1, h0.2, h0'.1, h0'.2]
  · right
    exact ⟨loc_mono (le_max_right _ _) hl', hsum _ _ (hb _ (Or.inl h0.1)) (hb' _ (Or.inr hz')),
      hsum _ _ (hb _ (Or.inl h0.2)) (hb' _ (Or.inr hζ'))⟩
  · right
    exact ⟨loc_mono (le_max_left _ _) hl, hsum _ _ (hb _ (Or.inr hz)) (hb' _ (Or.inl h0'.1)),
      hsum _ _ (hb _ (Or.inr hζ)) (hb' _ (Or.inl h0'.2))⟩
  · right
    exact ⟨loc_mono (le_max_left _ _) hl, hsum _ _ (hb _ (Or.inr hz)) (hb' _ (Or.inr hz')),
      hsum _ _ (hb _ (Or.inr hζ)) (hb' _ (Or.inr hζ'))⟩

/-- Cochrane (2023), footnote 1, p. 440: a bound on a test and a factor that is at most `K` on the
localization bound their product. -/
theorem RollTest.bound_mul {U : Set (ℝ × ℝ)} {Λ P c m : ℕ → Ω → ℝ} {t K : ℕ} {B : ℝ}
    {z ζ : Ω → ℝ} (h : RollTest S U Λ P c m t K B z ζ) {w : Ω → ℝ}
    (hw : ∀ ω, Loc S U Λ P c m t K ω → |w ω| ≤ K) (ω : Ω) :
    |w ω * z ω| ≤ K * |B| ∧ |w ω * ζ ω| ≤ K * |B| := by
  rcases h.2.2 ω with h0 | ⟨hl, hz, hζ⟩
  · rw [h0.1, h0.2]
    simp only [mul_zero, abs_zero, and_self]
    positivity
  · rw [abs_mul, abs_mul]
    exact ⟨mul_le_mul (hw ω hl) (hz.trans (le_abs_self _)) (abs_nonneg _) (by positivity),
      mul_le_mul (hw ω hl) (hζ.trans (le_abs_self _)) (abs_nonneg _) (by positivity)⟩

/-- Cochrane (2023), footnote 1, p. 440 and (19.12), p. 439: the integrability that the perpetual
rollover of a test requires: `Λ_tz`, `Λ_tζ`, `pk_{t+1}P_tζ` and `X = −Λ_t(z + ι_tζ)` are
integrable. -/
theorem RollTest.integrable {U : Set (ℝ × ℝ)} {Λ P c m : ℕ → Ω → ℝ} (hp : PriceWeak S Λ P)
    {t K : ℕ} {B : ℝ} {z ζ : Ω → ℝ} (h : RollTest S U Λ P c m t K B z ζ) :
    Integrable (fun ω => Λ t ω * z ω) S.μ ∧ Integrable (fun ω => Λ t ω * ζ ω) S.μ ∧
      Integrable (fun ω => pk Λ P (t + 1) ω * (P t ω * ζ ω)) S.μ ∧
      Integrable (rollX S Λ P t z ζ) S.μ := by
  have ae : ∀ {f : Ω → ℝ}, StronglyMeasurable[S.𝓕 t] f → AEStronglyMeasurable f S.μ :=
    fun h => (h.mono (S.𝓕.le t)).aestronglyMeasurable
  have hΛ : ∀ ω, Loc S U Λ P c m t K ω → |Λ t ω| ≤ K := fun ω hl => by
    rw [abs_of_pos (hp.2.2.1 t ω)]
    exact hl.2.1
  have hP : ∀ ω, Loc S U Λ P c m t K ω → |P t ω| ≤ K := fun ω hl => by
    rw [abs_of_pos (hp.2.2.2.1 t ω)]
    exact hl.2.2.1
  have hι : ∀ ω, Loc S U Λ P c m t K ω → |iota S Λ P t ω| ≤ K := fun ω hl => hl.2.2.2
  have i1 : Integrable (fun ω => Λ t ω * z ω) S.μ :=
    Integrable.of_bound (ae ((hp.1 t).mul h.1)) (K * |B|)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact (h.bound_mul hΛ ω).1)
  have i2 : Integrable (fun ω => Λ t ω * ζ ω) S.μ :=
    Integrable.of_bound (ae ((hp.1 t).mul h.2.1)) (K * |B|)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact (h.bound_mul hΛ ω).2)
  refine ⟨i1, i2, ?_, ?_⟩
  · have := (hp.2.2.2.2 (t + 1)).bdd_mul (c := K * |B|) (ae ((hp.2.1 t).mul h.2.1))
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact (h.bound_mul hP ω).2)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply]
    ring
  · have hX : rollX S Λ P t z ζ = fun ω => -(Λ t ω * z ω + Λ t ω * (iota S Λ P t ω * ζ ω)) := by
      funext ω
      simp only [rollX]
      ring
    rw [hX]
    refine (i1.add (Integrable.of_bound (ae ((hp.1 t).mul ((hp.sm_iota t).mul h.2.1)))
      (K * (K * |B|)) (Eventually.of_forall fun ω => ?_))).neg
    rw [Real.norm_eq_abs]
    simp only [Pi.mul_apply]
    rcases h.2.2 ω with h0 | ⟨hl, -, -⟩
    · rw [h0.2]
      simp only [mul_zero, abs_zero]
      positivity
    · rw [abs_mul]
      refine mul_le_mul (hΛ ω hl) ?_ (abs_nonneg _) (by positivity)
      exact (h.bound_mul hι ω).2

/-- Cochrane (2023), (19.13)–(19.14), p. 440: for a function continuous on the domain (such as
`u_c`, `u_m`), its value at the plan times a test is integrable. -/
theorem RollTest.integrable_util {U : Set (ℝ × ℝ)} (hU : IsOpen U) {Λ P c m : ℕ → Ω → ℝ}
    (hca : StronglyAdapted S.𝓕 c) (hma : StronglyAdapted S.𝓕 m) {t K : ℕ} {B : ℝ}
    {z ζ : Ω → ℝ} (h : RollTest S U Λ P c m t K B z ζ) {v : ℝ × ℝ → ℝ} (hv : ContinuousOn v U) :
    Integrable (fun ω => v (c t ω, m t ω) * z ω) S.μ ∧
      Integrable (fun ω => v (c t ω, m t ω) * ζ ω) S.μ := by
  obtain ⟨C, hC0, hC⟩ := kc_bound (U := U) K hv
  have hm : Measurable (fun ω => U.indicator v (c t ω, m t ω)) :=
    (measurable_indicator_of_continuousOn hU hv).comp
      (((hca t).mono (S.𝓕.le t)).measurable.prodMk ((hma t).mono (S.𝓕.le t)).measurable)
  have hz := (h.1.mono (S.𝓕.le t)).measurable
  have hζ := (h.2.1.mono (S.𝓕.le t)).measurable
  have e : ∀ (x : Ω → ℝ), (∀ ω, x ω = 0 ∨ (Good U K (c t ω, m t ω) ∧ |x ω| ≤ B)) →
      (fun ω => v (c t ω, m t ω) * x ω) = fun ω => U.indicator v (c t ω, m t ω) * x ω := by
    intro x hx
    funext ω
    rcases hx ω with h0 | ⟨hg, -⟩
    · rw [h0]
      simp
    · rw [Set.indicator_of_mem (kc_subset U K (good_mem_kc hg))]
  have hbd : ∀ (x : Ω → ℝ), (∀ ω, x ω = 0 ∨ (Good U K (c t ω, m t ω) ∧ |x ω| ≤ B)) →
      ∀ ω, ‖v (c t ω, m t ω) * x ω‖ ≤ C * |B| := by
    intro x hx ω
    rw [Real.norm_eq_abs, abs_mul]
    rcases hx ω with h0 | ⟨hg, hxB⟩
    · rw [h0, abs_zero, mul_zero]
      positivity
    · exact mul_le_mul (hC _ (good_mem_kc hg)) (hxB.trans (le_abs_self _)) (abs_nonneg _) hC0
  have hz' : ∀ ω, z ω = 0 ∨ (Good U K (c t ω, m t ω) ∧ |z ω| ≤ B) := fun ω =>
    (h.good ω).imp (fun h0 => h0.1) fun h' => ⟨h'.1, h'.2.1⟩
  have hζ' : ∀ ω, ζ ω = 0 ∨ (Good U K (c t ω, m t ω) ∧ |ζ ω| ≤ B) := fun ω =>
    (h.good ω).imp (fun h0 => h0.2) fun h' => ⟨h'.1, h'.2.2⟩
  refine ⟨Integrable.of_bound ?_ (C * |B|) (Eventually.of_forall (hbd z hz')),
    Integrable.of_bound ?_ (C * |B|) (Eventually.of_forall (hbd ζ hζ'))⟩
  · rw [e z hz']
    exact (hm.mul hz).aestronglyMeasurable
  · rw [e ζ hζ']
    exact (hm.mul hζ).aestronglyMeasurable

/-! ### The utility gain of two rollovers -/

/-- Cochrane (2023), (19.13)–(19.14), p. 440 and footnote 1 ("consider each item as a function of
state"), **the gain from two localized rollovers.** At an optimal plan (utility `C¹` on the open
domain `U`, `PriceWeak` prices), for tests `(z₁, ζ₁)` at `t₁` and `(z₂, ζ₂)` at `t₂ ≠ t₁`, there is
`r > 0` and a function `φ` with `φ(0) = 0`, derivative
`βᵗ¹E[u_c z₁ + u_m ζ₁] + βᵗ²E[u_c z₂ + u_m ζ₂]` at `0`, and `φ(ε) ≤ 0` for `|ε| < r` whenever the
plan perturbed by `ε` times both rollovers satisfies the extra constraint `Con` and the no-Ponzi
condition shifted by `ε(E[X₁] + E[X₂])`. -/
theorem roll_gain {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hu : C1On u uc um U) {Con : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop} {Λ P y s : ℕ → Ω → ℝ}
    {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ} (hopt : Optimal S β u Con Λ P y s N0 a0 c m a)
    (hp : PriceWeak S Λ P) {t₁ t₂ : ℕ} (hne : t₁ ≠ t₂) {K₁ K₂ : ℕ} {B₁ B₂ : ℝ}
    {z₁ ζ₁ z₂ ζ₂ : Ω → ℝ} (h₁ : RollTest S U Λ P c m t₁ K₁ B₁ z₁ ζ₁)
    (h₂ : RollTest S U Λ P c m t₂ K₂ B₂ z₂ ζ₂) :
    ∃ r, 0 < r ∧ ∃ φ : ℝ → ℝ, φ 0 = 0 ∧
      HasDerivAt φ (β ^ t₁ * ∫ ω, (uc (c t₁ ω) (m t₁ ω) * z₁ ω +
          um (c t₁ ω) (m t₁ ω) * ζ₁ ω) ∂S.μ +
        β ^ t₂ * ∫ ω, (uc (c t₂ ω) (m t₂ ω) * z₂ ω + um (c t₂ ω) (m t₂ ω) * ζ₂ ω) ∂S.μ) 0 ∧
      ∀ ε, |ε| < r →
        Con (fun n ω => c n ω + ε * (rollC t₁ z₁ n ω + rollC t₂ z₂ n ω))
          (fun n ω => m n ω + ε * (rollC t₁ ζ₁ n ω + rollC t₂ ζ₂ n ω)) →
        (∀ δ, 0 < δ → ∀ᶠ T in atTop, -δ ≤ wealthPV S Λ P N0 m a T +
          ε * ((∫ ω, rollX S Λ P t₁ z₁ ζ₁ ω ∂S.μ) + ∫ ω, rollX S Λ P t₂ z₂ ζ₂ ω ∂S.μ)) →
        φ ε ≤ 0 := by
  obtain ⟨hfeas, -, hadm, hmax⟩ := hopt
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have mz : ∀ {t : ℕ} {f : Ω → ℝ}, StronglyMeasurable[S.𝓕 t] f → Measurable f :=
    fun {t} _ h => (h.mono (S.𝓕.le t)).measurable
  obtain ⟨j1, j2, j3, j4⟩ := h₁.integrable hp
  obtain ⟨k1, k2, k3, k4⟩ := h₂.integrable hp
  have hd := (roll_homDev hp h₁.1 h₁.2.1 j1 j2 j3 j4).add hp
    (roll_homDev hp h₂.1 h₂.2.1 k1 k2 k3 k4)
  obtain ⟨r₁, hr₁, hI₁, hD₁⟩ := loc_deriv (μ := S.μ) hu (mz (hca t₁)) (mz (hma t₁)) (mz h₁.1)
    (mz h₁.2.1) h₁.good (hadm.integrable hβ t₁)
  obtain ⟨r₂, hr₂, hI₂, hD₂⟩ := loc_deriv (μ := S.μ) hu (mz (hca t₂)) (mz (hma t₂)) (mz h₂.1)
    (mz h₂.2.1) h₂.good (hadm.integrable hβ t₂)
  set φ : ℝ → ℝ := fun ε =>
    β ^ t₁ * (∫ ω, u (c t₁ ω + ε * z₁ ω) (m t₁ ω + ε * ζ₁ ω) ∂S.μ -
      ∫ ω, u (c t₁ ω) (m t₁ ω) ∂S.μ) +
    β ^ t₂ * (∫ ω, u (c t₂ ω + ε * z₂ ω) (m t₂ ω + ε * ζ₂ ω) ∂S.μ -
      ∫ ω, u (c t₂ ω) (m t₂ ω) ∂S.μ) with hφ
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, φ, by simp [hφ], ?_, fun ε hε hcon hnp => ?_⟩
  · have := ((hD₁.sub_const (∫ ω, u (c t₁ ω) (m t₁ ω) ∂S.μ)).const_mul (β ^ t₁)).add
      ((hD₂.sub_const (∫ ω, u (c t₂ ω) (m t₂ ω) ∂S.μ)).const_mul (β ^ t₂))
    exact this
  have hε₁ : |ε| < r₁ := lt_of_lt_of_le hε (min_le_left _ _)
  have hε₂ : |ε| < r₂ := lt_of_lt_of_le hε (min_le_right _ _)
  have hF := feasible_add hp hfeas hd (ε := ε) hnp
  -- the perturbed plan at the two dates
  have ec : ∀ n ω, c n ω + ε * (rollC t₁ z₁ n ω + rollC t₂ z₂ n ω) =
      if n = t₁ then c t₁ ω + ε * z₁ ω else if n = t₂ then c t₂ ω + ε * z₂ ω else c n ω := by
    intro n ω
    by_cases h1 : n = t₁
    · subst h1
      simp [rollC, hne]
    · by_cases h2 : n = t₂
      · subst h2
        simp [rollC, h1]
      · simp [rollC, h1, h2]
  have em : ∀ n ω, m n ω + ε * (rollC t₁ ζ₁ n ω + rollC t₂ ζ₂ n ω) =
      if n = t₁ then m t₁ ω + ε * ζ₁ ω else if n = t₂ then m t₂ ω + ε * ζ₂ ω else m n ω := by
    intro n ω
    by_cases h1 : n = t₁
    · subst h1
      simp [rollC, hne]
    · by_cases h2 : n = t₂
      · subst h2
        simp [rollC, h1]
      · simp [rollC, h1, h2]
  have hmod := hadm.modify hβ {t₁, t₂}
    (f' := fun n ω => u (c n ω + ε * (rollC t₁ z₁ n ω + rollC t₂ z₂ n ω))
      (m n ω + ε * (rollC t₁ ζ₁ n ω + rollC t₂ ζ₂ n ω)))
    (fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      funext ω
      rw [ec, em]
      simp [hn.1, hn.2])
    (fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl
      · refine (hI₁ ε hε₁).congr (Eventually.of_forall fun ω => ?_)
        simp only
        rw [ec, em]
        simp
      · refine (hI₂ ε hε₂).congr (Eventually.of_forall fun ω => ?_)
        simp only
        rw [ec, em]
        simp [hne.symm])
  have hle := hmax _ _ _ hF hcon hmod.1
  rw [hmod.2, Finset.sum_pair hne] at hle
  have e1 : ∫ ω, u (c t₁ ω + ε * (rollC t₁ z₁ t₁ ω + rollC t₂ z₂ t₁ ω))
      (m t₁ ω + ε * (rollC t₁ ζ₁ t₁ ω + rollC t₂ ζ₂ t₁ ω)) ∂S.μ =
      ∫ ω, u (c t₁ ω + ε * z₁ ω) (m t₁ ω + ε * ζ₁ ω) ∂S.μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by simp [rollC, hne])
  have e2 : ∫ ω, u (c t₂ ω + ε * (rollC t₁ z₁ t₂ ω + rollC t₂ z₂ t₂ ω))
      (m t₂ ω + ε * (rollC t₁ ζ₁ t₂ ω + rollC t₂ ζ₂ t₂ ω)) ∂S.μ =
      ∫ ω, u (c t₂ ω + ε * z₂ ω) (m t₂ ω + ε * ζ₂ ω) ∂S.μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by simp [rollC, hne.symm])
  rw [e1, e2] at hle
  simp only [hφ]
  linarith

/-! ### An abstract Lagrange-multiplier lemma -/

/-- Cochrane (2023), (19.13), p. 440 ("`βᵗu_c = Λ_t`" with one multiplier): let `Adm t` be a set
of admissible test vectors at date `t`, containing `0` and closed under `v + aw`, on which `Lu t`
and `Lp t` are linear. If for all dates `t₁ ≠ t₂`, `Lp_{t₁}(v) + Lp_{t₂}(w) = 0` implies
`Lu_{t₁}(v) + Lu_{t₂}(w) = 0` (budget-neutral pairs of deviations do not change utility to first
order), then there is a single constant `λ` with `Lu_t = λLp_t` on every admissible test, at
every date. -/
theorem lagrange {V : Type*} [AddCommGroup V] [Module ℝ V] (Adm : ℕ → V → Prop)
    (Lu Lp : ℕ → V → ℝ) (hzero : ∀ t, Adm t 0)
    (hcomb : ∀ t v w (a : ℝ), Adm t v → Adm t w → Adm t (v + a • w))
    (hLu : ∀ t v w (a : ℝ), Adm t v → Adm t w → Lu t (v + a • w) = Lu t v + a * Lu t w)
    (hLp : ∀ t v w (a : ℝ), Adm t v → Adm t w → Lp t (v + a • w) = Lp t v + a * Lp t w)
    (hpair : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ v w, Adm t₁ v → Adm t₂ w → Lp t₁ v + Lp t₂ w = 0 →
      Lu t₁ v + Lu t₂ w = 0) :
    ∃ lam : ℝ, ∀ t v, Adm t v → Lu t v = lam * Lp t v := by
  have hLu0 : ∀ t, Lu t 0 = 0 := fun t => by
    have := hLu t 0 0 1 (hzero t) (hzero t)
    simp only [one_smul, add_zero, one_mul] at this
    linarith
  have hLp0 : ∀ t, Lp t 0 = 0 := fun t => by
    have := hLp t 0 0 1 (hzero t) (hzero t)
    simp only [one_smul, add_zero, one_mul] at this
    linarith
  by_cases hex : ∃ r w, Adm r w ∧ Lp r w ≠ 0
  · obtain ⟨r, w, hw, hpw⟩ := hex
    refine ⟨Lu r w / Lp r w, fun t v hv => ?_⟩
    set a := -(Lp t v / Lp r w) with ha
    have hsum : Lp t v + a * Lp r w = 0 := by
      rw [ha]
      field_simp
      ring
    have key : Lu t v + a * Lu r w = 0 := by
      by_cases htr : t = r
      · subst htr
        have h := hpair t (t + 1) (by omega) _ 0 (hcomb t v w a hv hw) (hzero (t + 1))
          (by rw [hLp t v w a hv hw, hLp0, add_zero, hsum])
        rwa [hLu t v w a hv hw, hLu0, add_zero] at h
      · have h := hpair t r htr v (0 + a • w) hv (hcomb r 0 w a (hzero r) hw)
          (by rw [hLp r 0 w a (hzero r) hw, hLp0, zero_add, hsum])
        rwa [hLu r 0 w a (hzero r) hw, hLu0, zero_add] at h
    rw [ha] at key
    field_simp at key ⊢
    linarith
  · push Not at hex
    refine ⟨0, fun t v hv => ?_⟩
    have h := hpair t (t + 1) (by omega) v 0 hv (hzero (t + 1))
      (by rw [hex t v hv, hex (t + 1) 0 (hzero _), add_zero])
    rw [hLu0, add_zero] at h
    rw [h, zero_mul]

/-! ### Stability of the domain constraint and localization of the conditions -/

/-- Cochrane (2023), (19.9), p. 439: a small deviation `ε(x, y)` from a good point, with
`|x|, |y| ≤ B` and `|ε|(|B| + 1) < 1/(2(K + 1))`, stays in the domain. -/
theorem good_perturb_mem {U : Set (ℝ × ℝ)} {K : ℕ} {p : ℝ × ℝ} (hp : Good U K p) {x y B ε : ℝ}
    (hx : |x| ≤ B) (hy : |y| ≤ B) (hε : |ε| * (|B| + 1) < 1 / (2 * ((K : ℝ) + 1))) :
    (p.1 + ε * x, p.2 + ε * y) ∈ U := by
  have hb : ∀ z : ℝ, |z| ≤ B → |ε| * |z| < 1 / (2 * ((K : ℝ) + 1)) := fun z hz =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hz.trans ((le_abs_self B).trans (by linarith)))
      (abs_nonneg ε)) hε
  have := good_add hp (d := (ε * x, ε * y)) (by
    rw [Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    exact max_lt (hb x hx) (hb y hy))
  exact kc_subset U K this

/-- Cochrane (2023), (19.9), p. 439 and footnote 1, p. 440: the domain constraint survives two
small localized rollovers at different dates. -/
theorem domainCon_roll {U : Set (ℝ × ℝ)} {Λ P c m : ℕ → Ω → ℝ} (hdom : DomainCon S U c m)
    {t₁ t₂ K₁ K₂ : ℕ} {B₁ B₂ : ℝ} {z₁ ζ₁ z₂ ζ₂ : Ω → ℝ} (hne : t₁ ≠ t₂)
    (h₁ : RollTest S U Λ P c m t₁ K₁ B₁ z₁ ζ₁) (h₂ : RollTest S U Λ P c m t₂ K₂ B₂ z₂ ζ₂)
    {ε : ℝ} (hε₁ : |ε| * (|B₁| + 1) < 1 / (2 * ((K₁ : ℝ) + 1)))
    (hε₂ : |ε| * (|B₂| + 1) < 1 / (2 * ((K₂ : ℝ) + 1))) :
    DomainCon S U (fun n ω => c n ω + ε * (rollC t₁ z₁ n ω + rollC t₂ z₂ n ω))
      (fun n ω => m n ω + ε * (rollC t₁ ζ₁ n ω + rollC t₂ ζ₂ n ω)) := by
  intro n
  filter_upwards [hdom n] with ω hω
  by_cases h1 : n = t₁
  · subst h1
    simp only [rollC, ↓reduceIte, hne, add_zero]
    rcases h₁.good ω with h0 | ⟨hG, hx, hy⟩
    · rw [h0.1, h0.2]
      simpa using hω
    · exact good_perturb_mem hG hx hy hε₁
  · by_cases h2 : n = t₂
    · subst h2
      simp only [rollC, ↓reduceIte, h1, zero_add]
      rcases h₂.good ω with h0 | ⟨hG, hx, hy⟩
      · rw [h0.1, h0.2]
        simpa using hω
      · exact good_perturb_mem hG hx hy hε₂
    · simpa [rollC, h1, h2] using hω

/-- Cochrane (2023), footnote 1, p. 440 ("consider each item as a function of state"), **from
tests to almost-sure equations.** If `v` is continuous on the open domain, `w` is known at `t` and
bounded on each localization, the plan lies in the domain almost surely, and
`E[(v(c_t, m_t) − w)z] = 0` for every scalar test `z` at `t`, then `v(c_t, m_t) = w` almost
surely. -/
theorem ae_eq_of_tests {U : Set (ℝ × ℝ)} (hU : IsOpen U) {Λ P c m : ℕ → Ω → ℝ}
    (hp : PriceWeak S Λ P) (hca : StronglyAdapted S.𝓕 c) (hma : StronglyAdapted S.𝓕 m)
    (hdom : DomainCon S U c m) {t : ℕ} {v : ℝ × ℝ → ℝ} (hv : ContinuousOn v U) {w : Ω → ℝ}
    (hw : StronglyMeasurable[S.𝓕 t] w)
    (hwb : ∀ K : ℕ, ∃ C, ∀ ω, Loc S U Λ P c m t K ω → |w ω| ≤ C)
    (htest : ∀ (K : ℕ) (B : ℝ) (z : Ω → ℝ), StronglyMeasurable[S.𝓕 t] z →
      (∀ ω, z ω = 0 ∨ (Loc S U Λ P c m t K ω ∧ |z ω| ≤ B)) →
      ∫ ω, (v (c t ω, m t ω) - w ω) * z ω ∂S.μ = 0) :
    ∀ᵐ ω ∂S.μ, v (c t ω, m t ω) = w ω := by
  have hK : ∀ K : ℕ, ∀ᵐ ω ∂S.μ, Loc S U Λ P c m t K ω → v (c t ω, m t ω) = w ω := by
    intro K
    obtain ⟨C₁, hC₁0, hC₁⟩ := kc_bound (U := U) K hv
    obtain ⟨C₂, hC₂⟩ := hwb K
    set L := {ω | Loc S U Λ P c m t K ω} with hL
    have hLm := measurableSet_loc (U := U) hp hca hma t K
    set g : Ω → ℝ := L.indicator (fun ω => U.indicator v (c t ω, m t ω) - w ω) with hg
    have hgm : StronglyMeasurable[S.𝓕 t] g :=
      (((measurable_indicator_of_continuousOn hU hv).comp ((hca t).measurable.prodMk
        (hma t).measurable)).sub hw.measurable).stronglyMeasurable.indicator hLm
    have hgL : ∀ ω, ω ∈ L → g ω = v (c t ω, m t ω) - w ω := fun ω hω => by
      rw [hg, Set.indicator_of_mem hω, Set.indicator_of_mem (kc_subset U K (good_mem_kc hω.1))]
    have hgsupp : ∀ ω, g ω = 0 ∨ (Loc S U Λ P c m t K ω ∧ |g ω| ≤ C₁ + |C₂|) := by
      intro ω
      by_cases hω : ω ∈ L
      · right
        refine ⟨hω, ?_⟩
        rw [hgL ω hω]
        exact (abs_sub _ _).trans (add_le_add (hC₁ _ (good_mem_kc hω.1))
          ((hC₂ ω hω).trans (le_abs_self _)))
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
  filter_upwards [ae_all_iff.2 hK, ae_exists_loc (Λ := Λ) (P := P) hU hdom t] with ω h1 h2
  obtain ⟨K, hl⟩ := h2
  exact h1 K hl

/-! ### The money-in-utility first-order conditions -/

/-- Cochrane (2023), (19.13)–(19.14), p. 440 and footnote 1 (`βᵗpr(xᵗ)u_c = pr(xᵗ)(Λ_t/Λ_0)λ`),
**the money-in-utility first-order conditions with one constant multiplier, without regularity
hypotheses.** Let the utility be `C¹` on an open domain `U` (`TidyR6HouseholdLocal.C1On`, e.g.
`U = (0, ∞)²` for log or power utility), let prices satisfy only `PriceWeak` (adapted, positive,
`Λ_t/P_t` integrable), and let `(c, m, a)` be optimal among feasible plans lying in `U`
(`DomainCon`). Then there is one real `λ` such that at every date, almost surely,
`βᵗu_c(c_t, m_t) = λΛ_t` and `βᵗu_m(c_t, m_t) = λΛ_tι_t`. Consumption, real balances and prices
need not be bounded, and `λ` is a constant (not merely known at date `0`). -/
theorem miu_multiplier {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hu : C1On u uc um U) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : Optimal S β u (DomainCon S U) Λ P y s N0 a0 c m a) (hp : PriceWeak S Λ P) :
    ∃ lam : ℝ, ∀ t, (∀ᵐ ω ∂S.μ, β ^ t * uc (c t ω) (m t ω) = lam * Λ t ω) ∧
      ∀ᵐ ω ∂S.μ, β ^ t * um (c t ω) (m t ω) = lam * (Λ t ω * iota S Λ P t ω) := by
  have hfeas := hopt.1
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have hdom := hopt.2.1
  have hnp := hfeas.2.2.2.2.2.2.2.2.2
  set Adm : ℕ → (Ω → ℝ) × (Ω → ℝ) → Prop := fun t v =>
    ∃ (K : ℕ) (B : ℝ), RollTest S U Λ P c m t K B v.1 v.2 with hAdm
  set Lu : ℕ → (Ω → ℝ) × (Ω → ℝ) → ℝ := fun t v => β ^ t * ∫ ω, (uc (c t ω) (m t ω) * v.1 ω +
    um (c t ω) (m t ω) * v.2 ω) ∂S.μ with hLu
  set Lp : ℕ → (Ω → ℝ) × (Ω → ℝ) → ℝ := fun t v =>
    ∫ ω, Λ t ω * (v.1 ω + iota S Λ P t ω * v.2 ω) ∂S.μ with hLp
  have hucU : ContinuousOn (fun p : ℝ × ℝ => uc p.1 p.2) U := hu.2.2.1
  have humU : ContinuousOn (fun p : ℝ × ℝ => um p.1 p.2) U := hu.2.2.2
  -- integrability of the pieces of `Lu` and `Lp` on tests
  have iu : ∀ t v, Adm t v → Integrable (fun ω => uc (c t ω) (m t ω) * v.1 ω +
      um (c t ω) (m t ω) * v.2 ω) S.μ := by
    rintro t v ⟨K, B, h⟩
    exact (h.integrable_util hu.1 hca hma hucU).1.add (h.integrable_util hu.1 hca hma humU).2
  have ip : ∀ t v, Adm t v → Integrable (fun ω => Λ t ω * (v.1 ω + iota S Λ P t ω * v.2 ω))
      S.μ := by
    rintro t v ⟨K, B, h⟩
    have := (h.integrable hp).2.2.2
    refine this.neg.congr (Eventually.of_forall fun ω => ?_)
    simp [rollX]
  have hXLp : ∀ t v, ∫ ω, rollX S Λ P t v.1 v.2 ω ∂S.μ = -Lp t v := fun t v => by
    rw [hLp, ← integral_neg]
    rfl
  obtain ⟨lam, hlam⟩ := lagrange (V := (Ω → ℝ) × (Ω → ℝ)) Adm Lu Lp
    (fun t => ⟨0, 0, rollTest_zero U Λ P c m t 0 0⟩)
    (fun t v w a ⟨K, B, h⟩ ⟨K', B', h'⟩ => ⟨_, _, h.comb h' a⟩)
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
    (fun t₁ t₂ hne v w ⟨K₁, B₁, h₁⟩ ⟨K₂, B₂, h₂⟩ hsum => by
      obtain ⟨r, hr, φ, hφ0, hφd, hφle⟩ := roll_gain hβ hu hopt hp hne h₁ h₂
      set η := min r (min (1 / (2 * ((K₁ : ℝ) + 1)) / (|B₁| + 1))
        (1 / (2 * ((K₂ : ℝ) + 1)) / (|B₂| + 1))) with hη
      have hη0 : 0 < η := lt_min hr (lt_min (by positivity) (by positivity))
      have hmax : IsLocalMax φ 0 := by
        refine Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hη0) fun ε hε => ?_
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
        rw [hφ0]
        have hε₁ : |ε| * (|B₁| + 1) < 1 / (2 * ((K₁ : ℝ) + 1)) := by
          rw [← lt_div_iff₀ (by positivity)]
          exact lt_of_lt_of_le hε ((min_le_right _ _).trans (min_le_left _ _))
        have hε₂ : |ε| * (|B₂| + 1) < 1 / (2 * ((K₂ : ℝ) + 1)) := by
          rw [← lt_div_iff₀ (by positivity)]
          exact lt_of_lt_of_le hε ((min_le_right _ _).trans (min_le_right _ _))
        refine hφle ε (lt_of_lt_of_le hε (min_le_left _ _))
          (domainCon_roll hdom hne h₁ h₂ hε₁ hε₂) fun δ hδ => ?_
        have e := hXLp t₁ v
        have e' := hXLp t₂ w
        rw [e, e', ← neg_add, hsum, neg_zero, mul_zero]
        simpa using hnp δ hδ
      exact hmax.hasDerivAt_eq_zero hφd)
  refine ⟨lam, fun t => ⟨?_, ?_⟩⟩
  · -- consumption
    refine ae_eq_of_tests (v := fun p => β ^ t * uc p.1 p.2) (w := fun ω => lam * Λ t ω) hu.1 hp
      hca hma hdom (hucU.const_smul (β ^ t)) ((hp.1 t).const_mul lam)
      (fun K => ⟨|lam| * K, fun ω hl => by
        rw [abs_mul, abs_of_pos (hp.2.2.1 t ω)]
        exact mul_le_mul_of_nonneg_left hl.2.1 (abs_nonneg _)⟩) fun K B z hz hzs => ?_
    have hT : RollTest S U Λ P c m t K B z 0 :=
      ⟨hz, stronglyMeasurable_const, fun ω => (hzs ω).imp (fun h => ⟨h, rfl⟩)
        fun h => ⟨h.1, h.2, by
          simp only [Pi.zero_apply, abs_zero]
          exact (abs_nonneg _).trans h.2⟩⟩
    have h := hlam t (z, 0) ⟨K, B, hT⟩
    simp only [hLu, hLp, Pi.zero_apply, mul_zero, add_zero] at h
    have i1 := (hT.integrable_util hu.1 hca hma hucU).1
    have i2 := (hT.integrable hp).1
    rw [← integral_const_mul, ← integral_const_mul, ← sub_eq_zero, ← integral_sub
      (i1.const_mul _) (i2.const_mul _)] at h
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  · -- real balances
    refine ae_eq_of_tests (v := fun p => β ^ t * um p.1 p.2)
      (w := fun ω => lam * (Λ t ω * iota S Λ P t ω)) hu.1 hp hca hma hdom
      (humU.const_smul (β ^ t)) (((hp.1 t).mul (hp.sm_iota t)).const_mul lam)
      (fun K => ⟨|lam| * (K * K), fun ω hl => by
        rw [abs_mul, abs_mul, abs_of_pos (hp.2.2.1 t ω)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hl.2.1 hl.2.2.2 (abs_nonneg _)
          (by positivity)) (abs_nonneg _)⟩) fun K B z hz hzs => ?_
    have hT : RollTest S U Λ P c m t K B 0 z :=
      ⟨stronglyMeasurable_const, hz, fun ω => (hzs ω).imp (fun h => ⟨rfl, h⟩)
        fun h => ⟨h.1, by
          rw [Pi.zero_apply, abs_zero]
          exact (abs_nonneg _).trans h.2, h.2⟩⟩
    have h := hlam t (0, z) ⟨K, B, hT⟩
    simp only [hLu, hLp, Pi.zero_apply, mul_zero, zero_add] at h
    have i1 := (hT.integrable_util hu.1 hca hma humU).2
    have i2 : Integrable (fun ω => Λ t ω * (iota S Λ P t ω * z ω)) S.μ := by
      have := (ip t (0, z) ⟨K, B, hT⟩)
      simpa using this
    rw [← integral_const_mul, ← integral_const_mul, ← sub_eq_zero, ← integral_sub
      (i1.const_mul _) (i2.const_mul _)] at h
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)

/-- Cochrane (2023), (19.13)–(19.14), p. 440, for the money-in-utility problem of
`MoneyInUtilityMeasure` (utility smooth on all of `ℝ²`, no constraint beyond the budget):
**one constant multiplier with only `PriceWeak` prices** and no bounds on the plan. -/
theorem miu_multiplier_global {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ}
    (hu : Smooth₂ u uc um) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : Optimal S β u (fun _ _ => True) Λ P y s N0 a0 c m a) (hp : PriceWeak S Λ P) :
    ∃ lam : ℝ, ∀ t, (∀ᵐ ω ∂S.μ, β ^ t * uc (c t ω) (m t ω) = lam * Λ t ω) ∧
      ∀ᵐ ω ∂S.μ, β ^ t * um (c t ω) (m t ω) = lam * (Λ t ω * iota S Λ P t ω) := by
  have hdom : ∀ c m : ℕ → Ω → ℝ, DomainCon S Set.univ c m := fun _ _ _ =>
    Eventually.of_forall fun _ => Set.mem_univ _
  exact miu_multiplier hβ (c1On_of_smooth₂ hu)
    ⟨hopt.1, hdom c m, hopt.2.2.1, fun c' m' a' hf _ hu' => hopt.2.2.2 c' m' a' hf trivial hu'⟩
    hp

/-! ### The transversality condition along a subsequence -/

/-- Cochrane (2023), p. 439 ("their optimal choices include transversality conditions") and
(19.28), p. 449: **the liminf form of the transversality condition needs no concavity, no
reference plan and no bounds.** At a money-in-utility optimum (utility `C¹` on the open domain
`U`, `PriceWeak` prices) with `u_c > 0` almost surely at some date `t₀`, the date-0 value of
wealth `W_T = E[pk_T(a_T + M_{T−1})]` satisfies the no-Ponzi bound `W_T ≥ −δ` eventually and
`W_T < L` infinitely often for every `L > 0`: `liminf W_T = 0`. (Otherwise the household could
consume more at `t₀` and roll the debt over for ever.) -/
theorem miu_liminf_tvc {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hu : C1On u uc um U) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : Optimal S β u (DomainCon S U) Λ P y s N0 a0 c m a) (hp : PriceWeak S Λ P)
    {t₀ : ℕ} (hpos : ∀ᵐ ω ∂S.μ, 0 < uc (c t₀ ω) (m t₀ ω)) :
    (∀ δ, 0 < δ → ∀ᶠ T in atTop, -δ ≤ wealthPV S Λ P N0 m a T) ∧
      ∀ L, 0 < L → ∃ᶠ T in atTop, wealthPV S Λ P N0 m a T < L := by
  have hfeas := hopt.1
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have hdom := hopt.2.1
  have hnp := hfeas.2.2.2.2.2.2.2.2.2
  refine ⟨hnp, fun L hL => ?_⟩
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  -- a localization of positive probability at `t₀`
  obtain ⟨K, hKpos⟩ : ∃ K : ℕ, 0 < S.μ {ω | Loc S U Λ P c m t₀ K ω} := by
    by_contra hno
    push Not at hno
    have h0 : ∀ K : ℕ, S.μ {ω | Loc S U Λ P c m t₀ K ω} = 0 := fun K =>
      nonpos_iff_eq_zero.1 (hno K)
    have hU0 := measure_iUnion_null h0
    have hall := ae_exists_loc (Λ := Λ) (P := P) hu.1 hdom t₀
    rw [ae_iff] at hall
    have : S.μ Set.univ = 0 := by
      refine measure_mono_null (fun ω _ => ?_) (measure_union_null hU0 hall)
      by_cases h : ∃ K, Loc S U Λ P c m t₀ K ω
      · obtain ⟨K, hK⟩ := h
        exact Or.inl (Set.mem_iUnion.2 ⟨K, hK⟩)
      · exact Or.inr h
    simp at this
  set L₀ := {ω | Loc S U Λ P c m t₀ K ω} with hL₀
  have hLm := measurableSet_loc (U := U) hp hca hma t₀ K
  set z : Ω → ℝ := L₀.indicator (fun _ => 1) with hz
  have hT : RollTest S U Λ P c m t₀ K 1 z 0 := by
    refine ⟨stronglyMeasurable_const.indicator hLm, stronglyMeasurable_const, fun ω => ?_⟩
    by_cases hω : ω ∈ L₀
    · right
      refine ⟨hω, ?_, ?_⟩ <;> simp [hz, Set.indicator_of_mem hω]
    · left
      simp [hz, Set.indicator_of_notMem hω]
  have hT0 := rollTest_zero (S := S) U Λ P c m (t₀ + 1) 0 0
  obtain ⟨r, hr, φ, hφ0, hφd, hφle⟩ := roll_gain hβ hu hopt hp (by omega) hT hT0
  -- the value of the extra consumption
  set c₀ := ∫ ω, Λ t₀ ω * z ω ∂S.μ with hc₀
  have hzi := (hT.integrable hp).1
  have hc₀pos : 0 < c₀ := by
    rw [hc₀, integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun ω => ?_) hzi]
    · refine lt_of_lt_of_le hKpos (measure_mono fun ω hω => ?_)
      simp only [Function.mem_support, hz, Set.indicator_of_mem hω, mul_one]
      exact (hp.2.2.1 t₀ ω).ne'
    · simp only [hz, Pi.zero_apply]
      by_cases hω : ω ∈ L₀
      · rw [Set.indicator_of_mem hω, mul_one]
        exact (hp.2.2.1 t₀ ω).le
      · rw [Set.indicator_of_notMem hω, mul_zero]
  have hX : ∫ ω, rollX S Λ P t₀ z 0 ω ∂S.μ = -c₀ := by
    rw [hc₀, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp [rollX])
  have hX0 : ∫ ω, rollX S Λ P (t₀ + 1) 0 0 ω ∂S.μ = 0 := by simp [rollX]
  -- the derivative is positive
  have hDpos : 0 < β ^ t₀ * ∫ ω, (uc (c t₀ ω) (m t₀ ω) * z ω + um (c t₀ ω) (m t₀ ω) * 0) ∂S.μ +
      β ^ (t₀ + 1) * ∫ ω, (uc (c (t₀ + 1) ω) (m (t₀ + 1) ω) * 0 +
        um (c (t₀ + 1) ω) (m (t₀ + 1) ω) * 0) ∂S.μ := by
    simp only [mul_zero, add_zero, integral_zero]
    refine mul_pos (pow_pos hβ t₀) ?_
    have hi := (hT.integrable_util hu.1 hca hma hu.2.2.1).1
    rw [integral_pos_iff_support_of_nonneg_ae ?_ hi]
    · refine lt_of_lt_of_le hKpos (measure_mono_ae ?_)
      filter_upwards [hpos] with ω hω hL
      simp only [Function.mem_support, hz, Set.indicator_of_mem hL, mul_one]
      exact hω.ne'
    · filter_upwards [hpos] with ω hω
      simp only [hz, Pi.zero_apply]
      by_cases hL : ω ∈ L₀
      · rw [Set.indicator_of_mem hL, mul_one]
        exact hω.le
      · rw [Set.indicator_of_notMem hL, mul_zero]
  -- but it is nonpositive
  set η := min r (min (1 / (2 * ((K : ℝ) + 1)) / (|(1 : ℝ)| + 1)) (L / c₀)) with hη
  have hη0 : 0 < η := lt_min hr (lt_min (by positivity) (div_pos hL hc₀pos))
  have hDle := slope_nonpos hφd hφ0 hη0 fun ε hε0 hεη => by
    have hε : |ε| = ε := abs_of_pos hε0
    have hε₁ : |ε| * (|(1 : ℝ)| + 1) < 1 / (2 * ((K : ℝ) + 1)) := by
      rw [← lt_div_iff₀ (by positivity), hε]
      exact lt_of_lt_of_le hεη ((min_le_right _ _).trans (min_le_left _ _))
    have hε₂ : |ε| * (|(0 : ℝ)| + 1) < 1 / (2 * ((0 : ℕ) + 1 : ℝ)) := by
      have : ε < L / c₀ := lt_of_lt_of_le hεη ((min_le_right _ _).trans (min_le_right _ _))
      have h1 : ε < 1 / (2 * ((K : ℝ) + 1)) / (|(1 : ℝ)| + 1) :=
        lt_of_lt_of_le hεη ((min_le_right _ _).trans (min_le_left _ _))
      have h2 : 1 / (2 * ((K : ℝ) + 1)) / (|(1 : ℝ)| + 1) ≤ 1 / 2 := by
        rw [abs_one, div_le_iff₀ (by norm_num)]
        have : 1 / (2 * ((K : ℝ) + 1)) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith [K.cast_nonneg (α := ℝ)])
        linarith
      rw [hε, abs_zero]
      push_cast
      linarith
    refine hφle ε (by rw [hε]; exact lt_of_lt_of_le hεη (min_le_left _ _))
      (domainCon_roll hdom (by omega) hT hT0 hε₁ hε₂) fun δ hδ => ?_
    rw [hX, hX0]
    filter_upwards [hcon] with T hT'
    rw [not_lt] at hT'
    have : ε * c₀ < L := by
      have := lt_of_lt_of_le hεη ((min_le_right _ _).trans (min_le_right _ _))
      rwa [lt_div_iff₀ hc₀pos] at this
    linarith
  simp only [Pi.zero_apply] at hDle
  linarith

end Cochrane.Monetarism.TidyR6HouseholdFOC
