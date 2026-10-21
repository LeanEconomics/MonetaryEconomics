/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.CashInAdvanceMeasure
import Monetarism.HouseholdMeasureTVC

/-!
# The cash-in-advance household: transversality, binding money, and the i.i.d. wedge

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.5.1–19.5.2,
pp. 448–451, eqs. (19.28) and (19.33), on a genuine probability space (`CashInAdvanceMeasure`,
`HouseholdMeasureTVC`).

## Main results

* `tvc_necessary`: at an optimal plan of the cash-in-advance household, for every velocity `V`,
  the transversality condition (19.28) `E[Λ_T(a_T + M_{T−1})/P_T] → 0` holds (Kamihigashi
  scaling deviation, `HouseholdMeasureTVC.tvc_of_optimal`, with the bundle `ϑ = 1/V − 1`).
* **Fact 2, (19.33)** (`money_binds`): at an optimum, wherever the nominal rate is positive
  (`ι_t > 0`), the household holds the least overnight money the constraints allow,
  `m_t = max((1/V − 1)c_t + y_t, 0)`; at the endowment plan (`money_binds_1933`)
  `M_tV = P_ty_t`.
* **The i.i.d. economy with `V ≠ 1`** (`IIDWedge.iid_optimal`, `IIDWedge.coin_wedge`): with
  linear utility, coin endowment shocks and an endogenous price level, consuming the endowment is
  optimal, the bond price `Q_t = y_t/4` and the wedge `w_t = 1 + (1/V − 1)(1 − y_t/4)` are
  genuinely random, `Λ_tw_t = βᵗu'(y_t)` with `Λ_t ≠ βᵗu'(y_t)`, and the printed (19.32) fails
  almost surely at every date, while the corrected `bond_1932` holds.
-/

namespace Cochrane.Monetarism.CashInAdvanceMeasureTVC

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure HouseholdMeasure
  HouseholdMeasureTVC CashInAdvanceMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### Necessity of the transversality condition -/

/-- Cochrane (2023), (19.28), p. 449 ("The household's money and debt demands must also obey the
transversality condition"), **the transversality condition is necessary in the cash-in-advance
problem, for every velocity `V > 0`, on a probability space**: at an optimal plan with `u`
concave, continuously differentiable with `u' > 0`, regular prices, nonnegative nominal rates,
consumption, overnight money, claims, endowment and taxes bounded at each date (endowment and taxes
adapted), overnight money bounded away from zero, the reference plan (`HouseholdMeasureTVC.cRef`
with `ϑ = 1/V − 1`) admissible with nonnegative money, and the normalisation `Λ_0w_0 = u'(c_0)`,
`E[Λ_T(a_T + M_{T−1})/P_T] → 0`. -/
theorem tvc_necessary {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hpos : ∀ x, 0 < u' x) {V : ℝ}
    (hV : 0 < V) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : CIAOptimal S β u V Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) (hab : ∀ n, BddAt S (a n))
    (hyb : ∀ n, BddAt S (y n)) (hsb : ∀ n, BddAt S (s n)) (hya : StronglyAdapted S.𝓕 y)
    (hsa : StronglyAdapted S.𝓕 s) {δ : ℝ} (hδ : 0 < δ) (hmδ : ∀ t, ∀ᵐ ω ∂S.μ, δ ≤ m t ω)
    (hrate : ∀ t, ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1)
    (href : UAdmissible S β (fun n ω => u (cRef S (1 / V - 1) Λ P y s c m n ω)))
    (hmr : ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ mRef S (1 / V - 1) Λ P y s c m n ω)
    (hnorm : ∀ ω, Λ 0 ω * wedge S (1 / V - 1) Λ P 0 ω = u' (c 0 ω)) :
    Tendsto (wealthPV S Λ P N0 m a) atTop (𝓝 0) := by
  set ϑ := 1 / V - 1 with hϑ
  have hreg := fun n => wedge_regular hp hV (hrate n)
  have hconc' : ∀ x z : ℝ, ConcaveOn ℝ Set.univ
      (fun e => (fun x _ => u x : ℝ → ℝ → ℝ) (x + e) (z + ϑ * e)) := by
    intro x z
    change ConcaveOn ℝ Set.univ (fun e => u (x + e))
    refine ⟨convex_univ, fun a _ b _ p q hp hq hpq => ?_⟩
    have := hconc.2 (Set.mem_univ (x + a)) (Set.mem_univ (x + b)) hp hq hpq
    simp only [smul_eq_mul] at this ⊢
    convert this using 2
    linear_combination (-x) * hpq
  have hmono' : ∀ x z : ℝ, Monotone
      (fun e => (fun x _ => u x : ℝ → ℝ → ℝ) (x + e) (z + ϑ * e)) := fun x z a b h =>
    hmono (by linarith)
  refine tvc_of_optimal hβ (smooth₂_of_deriv hu hu') hconc' hmono' hopt hp hcb hmb hab hyb hsb
    hya hsa (fun n => (hreg n).1) (fun n => (hreg n).2) href (fun T => ?_) (fun T => ?_)
  · -- the constraints along the deviation
    obtain ⟨hkm, hkb⟩ := kw_regular hp hopt.1 hmb hab (fun n => (hreg n).2) (ϑ := ϑ) T
    obtain ⟨K, hK0, hK⟩ := hkb.exists_pos
    set θ₀ := min 1 (δ / ((|ϑ| + 1) * K)) with hθ₀
    have hθ₀p : 0 < θ₀ := lt_min one_pos (by positivity)
    refine ⟨θ₀, hθ₀p, min_le_left _ _, fun θ h0 hθ t => ?_⟩
    have hθ1 : θ < 1 := lt_of_lt_of_le hθ (min_le_left _ _)
    have hθδ : θ * ((|ϑ| + 1) * K) < δ :=
      (lt_div_iff₀ (by positivity)).1 (lt_of_lt_of_le hθ (min_le_right _ _))
    filter_upwards [hopt.2.1 t, hmδ t, hK, hmr t] with ω h1 h2 h3 h4
    rcases lt_trichotomy t T with h | h | h
    · rw [Kam.kamC_lt h, Kam.kamM_lt h]
      exact h1
    · subst h
      rw [Kam.kamC_eq, Kam.kamM_eq]
      refine ⟨by linarith [h1.1], ?_⟩
      have hs : |ϑ * (θ * (kOut S Λ P a m t ω / wedge S ϑ Λ P t ω))| < δ := by
        rw [abs_mul, abs_mul, abs_of_pos h0]
        have := mul_le_mul_of_nonneg_left h3 (abs_nonneg ϑ)
        nlinarith [abs_nonneg ϑ, abs_nonneg (kOut S Λ P a m t ω / wedge S ϑ Λ P t ω)]
      linarith [neg_abs_le (ϑ * (θ * (kOut S Λ P a m t ω / wedge S ϑ Λ P t ω)))]
    · rw [Kam.kamC_gt h, Kam.kamM_gt h]
      simp only [mRef] at h4 ⊢
      constructor
      · nlinarith [h1.1]
      · nlinarith [h1.2]
  · -- the normalised first-order condition
    filter_upwards [multiplier_const hβ hu hu' hV hopt hp hcb hmb hδ hmδ hrate T,
      (hreg T).1] with ω h h2
    rw [hnorm ω, div_self (hpos _).ne',
      div_eq_one_iff_eq (mul_ne_zero (hp.2.2.1 T ω).ne' h2)] at h
    simpa using h

/-! ### Fact 2: money binds when the nominal rate is positive -/

/-- Cochrane (2023), p. 450, **Fact 2 under uncertainty, for every velocity `V`** ("With positive
nominal interest rates, money is strictly dominated by bonds, so the household will hold as little
money as possible overnight"), on a probability space: at an optimal plan (`u'` positive and
continuous, regular prices, `Q ≤ 1`, consumption and overnight money bounded, overnight money
bounded away from zero, endowment adapted), almost surely where `ι_t = i_t/(1 + i_t) > 0` the
overnight money is the least the constraints (19.24)–(19.26) allow,
`m_t = max((1/V − 1)c_t + y_t, 0)`. The deviation holds the slack `min(slack, 1)` less money at
`t` on `{ι_t > 0}` and consumes the interest saved at `t + 1`. -/
theorem money_binds {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') (hpos : ∀ x, 0 < u' x) {V : ℝ} (hV : 0 < V)
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : CIAOptimal S β u V Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) (hya : StronglyAdapted S.𝓕 y)
    {δ : ℝ} (hδ : 0 < δ) (hmδ : ∀ t, ∀ᵐ ω ∂S.μ, δ ≤ m t ω)
    (hrate : ∀ t, ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, 0 < iota S Λ P t ω → m t ω = max ((1 / V - 1) * c t ω + y t ω) 0 := by
  set ϑ := 1 / V - 1 with hϑ
  have hca := hopt.1.2.1
  have hma := hopt.1.2.2.1
  have hle : S.𝓕 t ≤ S.𝓕 (t + 1) := S.𝓕.mono (Nat.le_succ t)
  have ae : ∀ {k : ℕ} {f : Ω → ℝ}, StronglyMeasurable[S.𝓕 k] f → AEStronglyMeasurable f S.μ :=
    fun {k} _ h => (h.mono (S.𝓕.le k)).aestronglyMeasurable
  have hreg := fun n => wedge_regular hp hV (hrate n)
  have hwm : ∀ k, StronglyMeasurable[S.𝓕 k] (wedge S ϑ Λ P k) := fun k =>
    stronglyMeasurable_const.add ((hp.stronglyMeasurable_iota k).const_mul ϑ)
  -- the slack and the deviation
  set slack : Ω → ℝ := fun ω => m t ω - max (ϑ * c t ω + y t ω) 0 with hslack
  have hsl0 : ∀ᵐ ω ∂S.μ, 0 ≤ slack ω := by
    filter_upwards [hopt.2.1 t] with ω h
    simp only [hslack]
    have := max_le h.1 h.2
    linarith
  set A : Set Ω := {ω | 0 < iota S Λ P t ω} with hA
  have hAm : MeasurableSet[S.𝓕 t] A :=
    measurableSet_lt measurable_const (hp.stronglyMeasurable_iota t).measurable
  set r : Ω → ℝ := A.indicator (fun ω => min (slack ω) 1) with hr
  have hrm : StronglyMeasurable[S.𝓕 t] r :=
    (((hma t).sub (((((hca t).const_mul ϑ).add (hya t)).measurable.max
      measurable_const).stronglyMeasurable)).measurable.min measurable_const
      |>.stronglyMeasurable).indicator hAm
  have hr01 : ∀ᵐ ω ∂S.μ, 0 ≤ r ω ∧ r ω ≤ slack ω ∧ r ω ≤ 1 := by
    filter_upwards [hsl0] with ω h
    simp only [hr, Set.indicator]
    split_ifs
    · exact ⟨le_min h zero_le_one, min_le_left _ _, min_le_right _ _⟩
    · exact ⟨le_rfl, h, zero_le_one⟩
  have hrb : BddAt S r := ⟨1, hr01.mono fun ω h => by
    rw [abs_of_nonneg h.1]; exact h.2.2⟩
  set z₂ : Ω → ℝ := fun ω => iota S Λ P t ω * r ω * Λ t ω /
    (Λ (t + 1) ω * wedge S ϑ Λ P (t + 1) ω) with hz₂
  have hz₂m : StronglyMeasurable[S.𝓕 (t + 1)] z₂ :=
    (((((hp.stronglyMeasurable_iota t).mul hrm).mul (hp.1 t)).mono hle).measurable.div
      ((hp.1 (t + 1)).mul (hwm (t + 1))).measurable).stronglyMeasurable
  have hz₂b : BddAt S z₂ := by
    have := ((((hp.iota_bdd t).mul hrb).mul (hp.2.2.2.2 t).1).mul
      (hp.2.2.2.2 (t + 1)).2.1).mul (hreg (t + 1)).2
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [hz₂]
    ring
  have hX : StronglyMeasurable[S.𝓕 t] (fun ω => iota S Λ P t ω * r ω * Λ t ω) :=
    ((hp.stronglyMeasurable_iota t).mul hrm).mul (hp.1 t)
  have hXi : Integrable (fun ω => iota S Λ P t ω * r ω * Λ t ω) S.μ :=
    (((hp.iota_bdd t).mul hrb).mul (hp.2.2.2.2 t).1).integrable (ae hX)
  have hfin : ∀ᵐ ω ∂S.μ, Λ t ω * ((fun _ => (0 : ℝ)) ω + iota S Λ P t ω * (-r ω)) +
      S.E t (fun ω => Λ (t + 1) ω * (z₂ ω + iota S Λ P (t + 1) ω * (ϑ * z₂ ω))) ω = 0 := by
    have hae : (fun ω => Λ (t + 1) ω * (z₂ ω + iota S Λ P (t + 1) ω * (ϑ * z₂ ω))) =ᵐ[S.μ]
        fun ω => iota S Λ P t ω * r ω * Λ t ω := by
      filter_upwards [(hreg (t + 1)).1] with ω hw
      have := (hp.2.2.1 (t + 1) ω).ne'
      have e : wedge S ϑ Λ P (t + 1) ω = 1 + ϑ * iota S Λ P (t + 1) ω := rfl
      simp only [hz₂]
      rw [e] at hw ⊢
      field_simp
    filter_upwards [S.E_congr hae t] with ω h
    rw [h, S.E_of_stronglyMeasurable hX hXi]
    ring
  -- the deviation respects the constraints for small steps
  obtain ⟨K, hK0, hK⟩ := hz₂b.exists_pos
  set η := min 1 (δ / ((|ϑ| + 1) * K)) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hcon : ∃ η, 0 < η ∧ ∀ ε, |ε| < η → CIACon S V y (bump c t (fun _ => 0) z₂ ε)
      (bump m t (fun ω => -r ω) (fun ω => ϑ * z₂ ω) ε) := by
    refine ⟨η, hη0, fun ε hε n => ?_⟩
    have hε1 : |ε| < 1 := lt_of_lt_of_le hε (min_le_left _ _)
    have hεδ : |ε| * ((|ϑ| + 1) * K) < δ :=
      (lt_div_iff₀ (by positivity)).1 (lt_of_lt_of_le hε (min_le_right _ _))
    filter_upwards [hopt.2.1 n, hmδ n, hK, hr01] with ω h1 h2 h3 h4
    by_cases hn : n = t
    · subst hn
      rw [bump_self, bump_self]
      simp only [mul_zero, add_zero]
      have hεr : ε * r ω ≤ slack ω := by
        rcases le_or_gt ε 0 with he | he
        · nlinarith [mul_nonneg (neg_nonneg.2 he) h4.1, h4.1, h4.2.1]
        · have : ε < 1 := by rw [abs_lt] at hε1; exact hε1.2
          nlinarith [mul_nonneg (sub_nonneg.2 this.le) h4.1, h4.1, h4.2.1]
      simp only [hslack] at hεr
      constructor
      · linarith [le_max_left (ϑ * c n ω + y n ω) 0]
      · linarith [le_max_right (ϑ * c n ω + y n ω) 0]
    · by_cases hn1 : n = t + 1
      · subst hn1
        rw [bump_succ, bump_succ]
        refine ⟨by nlinarith [h1.1], ?_⟩
        have : |ε * (ϑ * z₂ ω)| < δ := by
          rw [abs_mul, abs_mul]
          have hz : |ϑ| * |z₂ ω| ≤ (|ϑ| + 1) * K := by
            nlinarith [abs_nonneg ϑ, abs_nonneg (z₂ ω)]
          have := mul_le_mul_of_nonneg_left hz (abs_nonneg ε)
          linarith
        linarith [neg_abs_le (ε * (ϑ * z₂ ω))]
      · rw [bump_of_ne hn hn1, bump_of_ne hn hn1]
        exact h1
  have key := pair_foc hβ (smooth₂_of_deriv hu hu') hopt hp (hcb t) (hcb (t + 1)) (hmb t)
    (hmb (t + 1)) (stronglyMeasurable_const) hrm.neg hz₂m (hz₂m.const_mul ϑ)
    (BddAt.const 0) hrb.neg hz₂b ((BddAt.const ϑ).mul hz₂b) hfin hcon
  simp only [mul_zero, add_zero, zero_mul, integral_zero] at key
  -- with the Euler equation the gain is `E[κ ι r Λ]`
  set κ : Ω → ℝ := fun ω => β ^ t * u' (c t ω) / (Λ t ω * wedge S ϑ Λ P t ω) with hκ
  have hκb : BddAt S κ := by
    obtain ⟨M, hM⟩ := hcb t
    obtain ⟨C, -, hC⟩ := exists_abs_le_of_continuous₂ (v := fun x _ => u' x)
      (hu'.comp continuous_fst) M
    have h1 : BddAt S (fun ω => u' (c t ω)) :=
      ⟨C, hM.mono fun ω h => hC _ 0 h (by rw [abs_zero]; exact (abs_nonneg _).trans h)⟩
    have := (((BddAt.const (β ^ t)).mul h1).mul (hp.2.2.2.2 t).2.1).mul (hreg t).2
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [hκ]
    ring
  have hκm : StronglyMeasurable[S.𝓕 t] κ :=
    ((((hu'.measurable.comp (hca t).measurable).const_mul _)).div
      ((hp.1 t).measurable.mul (hwm t).measurable)).stronglyMeasurable
  have hI : Integrable (fun ω => κ ω * (iota S Λ P t ω * r ω * Λ t ω)) S.μ :=
    (hκb.mul (((hp.iota_bdd t).mul hrb).mul (hp.2.2.2.2 t).1)).integrable
      ((ae hκm).mul (ae hX))
  have hEu := euler_step hβ hu hu' hV hopt hp hcb hmb hδ hmδ hrate t
  have hzero : ∫ ω, κ ω * (iota S Λ P t ω * r ω * Λ t ω) ∂S.μ = 0 := by
    have e : ∫ ω, κ ω * (iota S Λ P t ω * r ω * Λ t ω) ∂S.μ =
        β ^ (t + 1) * ∫ ω, u' (c (t + 1) ω) * z₂ ω ∂S.μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hEu, (hreg (t + 1)).1] with ω h hw
      rw [← hϑ] at h
      have := (hp.2.2.1 (t + 1) ω).ne'
      simp only [hz₂, hκ]
      rw [show β ^ (t + 1) * (u' (c (t + 1) ω) * (iota S Λ P t ω * r ω * Λ t ω /
        (Λ (t + 1) ω * wedge S ϑ Λ P (t + 1) ω))) = β ^ (t + 1) * u' (c (t + 1) ω) *
          (iota S Λ P t ω * r ω * Λ t ω / (Λ (t + 1) ω * wedge S ϑ Λ P (t + 1) ω)) by ring, h]
      set W0 := wedge S ϑ Λ P t ω
      set W1 := wedge S ϑ Λ P (t + 1) ω
      have := (hp.2.2.1 t ω).ne'
      field_simp
    rw [e]
    have hb := pow_pos hβ t
    linarith [key]
  have hnn : 0 ≤ᵐ[S.μ] fun ω => κ ω * (iota S Λ P t ω * r ω * Λ t ω) := by
    filter_upwards [hr01, wedge_lower hp hV (hrate t)] with ω h hwl
    have hw : 0 < wedge S ϑ Λ P t ω :=
      lt_of_lt_of_le (lt_min one_pos (one_div_pos.2 hV)) hwl
    have hκ0 : 0 ≤ κ ω := div_nonneg (mul_nonneg (pow_pos hβ t).le (hpos _).le)
      (mul_pos (hp.2.2.1 t ω) hw).le
    have hιr : 0 ≤ iota S Λ P t ω * r ω := by
      by_cases hω : ω ∈ A
      · exact mul_nonneg (le_of_lt hω) h.1
      · rw [show r ω = 0 from Set.indicator_of_notMem hω _, mul_zero]
    exact mul_nonneg hκ0 (mul_nonneg hιr (hp.2.2.1 t ω).le)
  have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn hI).1 hzero
  filter_upwards [h0, hsl0, wedge_lower hp hV (hrate t)] with ω h hs hwl hι
  have hw : 0 < wedge S ϑ Λ P t ω := lt_of_lt_of_le (lt_min one_pos (one_div_pos.2 hV)) hwl
  have hκ0 : 0 < κ ω := div_pos (mul_pos (pow_pos hβ t) (hpos _))
    (mul_pos (hp.2.2.1 t ω) hw)
  have hrω : r ω = 0 := by
    simp only [Pi.zero_apply] at h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h hκ0.ne'
    · rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hι.ne'
        · exact h
      · exact absurd h (hp.2.2.1 t ω).ne'
  have hmin : min (slack ω) 1 = 0 := by
    simpa [hr, Set.indicator, show ω ∈ A from hι] using hrω
  have : slack ω = 0 := by
    rcases min_choice (slack ω) 1 with h' | h'
    · rw [h'] at hmin; exact hmin
    · rw [h'] at hmin; norm_num at hmin
  simp only [hslack] at this
  linarith

/-- Cochrane (2023), eq. (19.33), p. 450, **Fact 2 at the endowment plan**: at an optimum
consuming a nonnegative endowment (hypotheses of `money_binds`), almost surely where the nominal
rate is positive, `M_tV = P_ty_t` (overnight money `M_t = P_tm_t`). -/
theorem money_binds_1933 {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') (hpos : ∀ x, 0 < u' x) {V : ℝ} (hV : 0 < V)
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {m a : ℕ → Ω → ℝ}
    (hopt : CIAOptimal S β u V Λ P y s N0 a0 y m a) (hp : PriceRegular S Λ P)
    (hyb : ∀ n, BddAt S (y n)) (hmb : ∀ n, BddAt S (m n)) (hy0 : ∀ t ω, 0 ≤ y t ω)
    {δ : ℝ} (hδ : 0 < δ) (hmδ : ∀ t, ∀ᵐ ω ∂S.μ, δ ≤ m t ω)
    (hrate : ∀ t, ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, 0 < iota S Λ P t ω → (P t ω * m t ω) * V = P t ω * y t ω := by
  filter_upwards [money_binds hβ hu hu' hpos hV hopt hp hyb hmb hopt.1.2.1 hδ hmδ hrate t]
    with ω h hι
  have e : (1 / V - 1) * y t ω + y t ω = y t ω / V := by field_simp; ring
  rw [h hι, e, max_eq_left (div_nonneg (hy0 t ω) hV.le)]
  field_simp

/-! ### The i.i.d. economy with `V ≠ 1`: a stochastic wedge -/

namespace IIDWedge

open ExpectationsMeasureIID MoneyInUtilityMeasure.IID

/-- Cochrane (2023), §19.5.2, p. 450: the bond price as a function of the endowment,
`q(y) = y/4 ∈ [3/8, 5/8]`. -/
noncomputable def qf (x : ℝ) : ℝ := x / 4

/-- Cochrane (2023), p. 450: the consumption wedge as a function of the endowment,
`w(y) = 1 + (1/V − 1)(1 − q(y))`. -/
noncomputable def wf (V x : ℝ) : ℝ := 1 + (1 / V - 1) * (1 - qf x)

/-- Cochrane (2023), p. 450: `E[1/w(y)]` under the shock law `ν`. -/
noncomputable def cnu (ν : ProbabilityMeasure ℝ) (V : ℝ) : ℝ :=
  ∫ x, 1 / wf V (2 + clamp x / 2) ∂(ν : Measure ℝ)

/-- Cochrane (2023), §19.5.2, p. 450: the gross inflation rate `P_{t+1}/P_t = g(y_t)`,
`g(y) = βw(y)E[1/w]/(q(y)u'(y))` with `u' = 1`, chosen so that `Q_t = q(y_t)`. -/
noncomputable def gf (ν : ProbabilityMeasure ℝ) (β V x : ℝ) : ℝ := β * wf V x * cnu ν V / qf x

/-- Cochrane (2023), §19.5.2, p. 450: the price level `P_0 = 1`, `P_{t+1} = P_t g(y_t)`. -/
noncomputable def priceLvl (ν : ProbabilityMeasure ℝ) (β V : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun ω => priceLvl ν β V t ω * gf ν β V (endow t ω)

/-- Cochrane (2023), (19.31), p. 450 with the wedge: the state prices `Λ_t = βᵗu'(y_t)/w(y_t)`
(`u' = 1`). -/
noncomputable def lamW (β V : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := β ^ t / wf V (endow t ω)

/-- Cochrane (2023), (19.33), p. 450: the binding overnight money `m_t = y_t/V`. -/
noncomputable def moneyW (V : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := endow t ω / V

/-- Cochrane (2023), (19.27), p. 449: the transfers that make the flow constraint hold with no
bonds, `s_t = (M_{t−1} − P_tm_t)/P_t`, `M_{−1} = 0`. -/
noncomputable def taxesW (ν : ProbabilityMeasure ℝ) (β V : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (moneyIn (fun _ => 0) (priceLvl ν β V) (moneyW V) t ω - priceLvl ν β V t ω * moneyW V t ω) /
    priceLvl ν β V t ω

/-- Cochrane (2023), p. 450: for `V > 0` and `y ∈ [3/2, 5/2]`, `3/8 ≤ w(y) ≤ 1 + |1/V − 1|`. -/
theorem wf_bounds {V x : ℝ} (hV : 0 < V) (h1 : 3 / 2 ≤ x) (h2 : x ≤ 5 / 2) :
    3 / 8 ≤ wf V x ∧ wf V x ≤ 1 + |1 / V - 1| := by
  have hθ : -1 < 1 / V - 1 := by have := one_div_pos.2 hV; linarith
  simp only [wf, qf]
  constructor
  · rcases le_or_gt 0 (1 / V - 1) with h | h
    · nlinarith
    · nlinarith
  · nlinarith [le_abs_self (1 / V - 1), neg_abs_le (1 / V - 1)]

/-- Cochrane (2023), p. 450: `w(y_t) ≥ 3/8`. -/
theorem wf_endow_bounds {V : ℝ} (hV : 0 < V) (t : ℕ) (ω : ℕ → ℝ) :
    3 / 8 ≤ wf V (endow t ω) ∧ wf V (endow t ω) ≤ 1 + |1 / V - 1| :=
  wf_bounds hV (endow_bounds t ω).1 (endow_bounds t ω).2

/-- Cochrane (2023), p. 450: `1/(1 + |1/V − 1|) ≤ E[1/w] ≤ 8/3`. -/
theorem cnu_bounds (ν : ProbabilityMeasure ℝ) {V : ℝ} (hV : 0 < V) :
    1 / (1 + |1 / V - 1|) ≤ cnu ν V ∧ cnu ν V ≤ 8 / 3 := by
  have hb : ∀ x : ℝ, 1 / (1 + |1 / V - 1|) ≤ 1 / wf V (2 + clamp x / 2) ∧
      1 / wf V (2 + clamp x / 2) ≤ 8 / 3 := by
    intro x
    have hc := abs_le.1 (abs_clamp_le x)
    obtain ⟨h1, h2⟩ := wf_bounds (x := 2 + clamp x / 2) hV (by linarith) (by linarith)
    constructor
    · exact one_div_le_one_div_of_le (by linarith) h2
    · rw [div_le_iff₀ (by linarith)]
      nlinarith
  have hm : Measurable fun x => 1 / wf V (2 + clamp x / 2) :=
    measurable_const.div (measurable_const.add (measurable_const.mul
      (measurable_const.sub (((continuous_clamp.measurable.div_const 2).const_add 2).div_const
        4))))
  have hi : Integrable (fun x => 1 / wf V (2 + clamp x / 2)) (ν : Measure ℝ) :=
    Integrable.of_bound hm.aestronglyMeasurable (8 / 3) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(hb x).1,
        (show 0 < 1 / (1 + |1 / V - 1|) by positivity)])]
      exact (hb x).2)
  constructor
  · have := integral_mono (integrable_const _) hi fun x => (hb x).1
    simpa [cnu] using this
  · have := integral_mono hi (integrable_const _) fun x => (hb x).2
    simpa [cnu] using this

variable {ν : ProbabilityMeasure ℝ} {β V : ℝ}

/-- Cochrane (2023), §19.5.2, p. 450: the inflation factor is positive and bounded,
`0 < g(y_t) ≤ β(1 + |1/V − 1|)(8/3)/(3/8)`, with `1/g(y_t) ≤ (5/8)/(β(3/8)/(1 + |1/V − 1|))`. -/
theorem gf_bounds (hβ0 : 0 < β) (hV : 0 < V) (t : ℕ) (ω : ℕ → ℝ) :
    0 < gf ν β V (endow t ω) ∧
      gf ν β V (endow t ω) ≤ β * (1 + |1 / V - 1|) * (8 / 3) / (3 / 8) ∧
      (gf ν β V (endow t ω))⁻¹ ≤ (5 / 8) / (β * (3 / 8) * (1 / (1 + |1 / V - 1|))) := by
  obtain ⟨hw1, hw2⟩ := wf_endow_bounds hV t ω
  obtain ⟨hc1, hc2⟩ := cnu_bounds ν hV
  obtain ⟨hy1, hy2⟩ := endow_bounds t ω
  have hq1 : 3 / 8 ≤ qf (endow t ω) := by simp only [qf]; linarith
  have hq2 : qf (endow t ω) ≤ 5 / 8 := by simp only [qf]; linarith
  have hcp : 0 < cnu ν V := lt_of_lt_of_le (by positivity) hc1
  refine ⟨by simp only [gf]; positivity, ?_, ?_⟩
  · simp only [gf]
    gcongr
  · simp only [gf]
    rw [inv_div]
    gcongr

/-- Cochrane (2023), §19.5.2, p. 450: the price level is positive. -/
theorem priceLvl_pos (hβ0 : 0 < β) (hV : 0 < V) (t : ℕ) (ω : ℕ → ℝ) :
    0 < priceLvl ν β V t ω := by
  induction t with
  | zero => simp [priceLvl]
  | succ k ih => exact mul_pos ih (gf_bounds hβ0 hV k ω).1

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), §19.5.2, p. 450: the price level and its reciprocal are bounded at each
date. -/
theorem priceLvl_bdd (hβ0 : 0 < β) (hV : 0 < V) (t : ℕ) :
    ∃ B, ∀ ω, |priceLvl ν β V t ω| ≤ B ∧ |(priceLvl ν β V t ω)⁻¹| ≤ B := by
  induction t with
  | zero => exact ⟨1, fun ω => by simp [priceLvl]⟩
  | succ k ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨B * (β * (1 + |1 / V - 1|) * (8 / 3) / (3 / 8) +
      (5 / 8) / (β * (3 / 8) * (1 / (1 + |1 / V - 1|)))), fun ω => ?_⟩
    obtain ⟨g0, g1, g2⟩ := gf_bounds (ν := ν) hβ0 hV k ω
    have hP := priceLvl_pos (ν := ν) hβ0 hV k ω
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB ω).1
    have hK2 : 0 ≤ (5 / 8) / (β * (3 / 8) * (1 / (1 + |1 / V - 1|))) := by positivity
    have hK1 : 0 ≤ β * (1 + |1 / V - 1|) * (8 / 3) / (3 / 8) := by positivity
    simp only [priceLvl]
    rw [abs_mul, abs_of_pos g0, mul_inv, abs_mul, abs_of_pos (inv_pos.2 g0)]
    constructor
    · exact (mul_le_mul (hB ω).1 g1 g0.le hB0).trans
        (mul_le_mul_of_nonneg_left (by linarith) hB0)
    · exact (mul_le_mul (hB ω).2 g2 (inv_pos.2 g0).le hB0).trans
        (mul_le_mul_of_nonneg_left (by linarith) hB0)

/-- Cochrane (2023), §19.5.2, p. 450: the price level of date `t` is known at `t`. -/
theorem priceLvl_meas (t : ℕ) :
    StronglyMeasurable[(iidSystem ν).𝓕 t] (priceLvl ν β V t) := by
  induction t with
  | zero => exact stronglyMeasurable_const
  | succ k ih =>
    have hg : StronglyMeasurable[(iidSystem ν).𝓕 k] (fun ω => gf ν β V (endow k ω)) := by
      have he := (measurable_endow ν k).measurable
      exact (((measurable_const.mul (measurable_const.add (measurable_const.mul
        (measurable_const.sub (he.div_const 4))))).mul_const _).div
          (he.div_const 4)).stronglyMeasurable
    exact (ih.mul hg).mono ((iidSystem ν).𝓕.mono (Nat.le_succ k))

/-- Cochrane (2023), p. 450: the i.i.d. state prices and price level are regular. -/
theorem wedge_priceRegular (hβ0 : 0 < β) (hV : 0 < V) :
    PriceRegular (iidSystem ν) (lamW β V) (priceLvl ν β V) := by
  refine ⟨fun t => ?_, fun t => priceLvl_meas t, fun t ω => ?_, fun t ω => priceLvl_pos hβ0 hV t ω,
    fun t => ⟨⟨β ^ t * (8 / 3), Eventually.of_forall fun ω => ?_⟩,
      ⟨(1 + |1 / V - 1|) / β ^ t, Eventually.of_forall fun ω => ?_⟩,
      ⟨_, Eventually.of_forall fun ω => ((priceLvl_bdd (ν := ν) hβ0 hV t).choose_spec ω).1⟩,
      ⟨_, Eventually.of_forall fun ω => ((priceLvl_bdd (ν := ν) hβ0 hV t).choose_spec ω).2⟩⟩⟩
  · have he := (measurable_endow ν t).measurable
    exact (measurable_const.div (measurable_const.add (measurable_const.mul
      (measurable_const.sub (he.div_const 4))))).stronglyMeasurable
  · exact div_pos (pow_pos hβ0 t) (by linarith [(wf_endow_bounds hV t ω).1])
  · obtain ⟨h1, -⟩ := wf_endow_bounds hV t ω
    have hb := pow_pos hβ0 t
    simp only [lamW]
    rw [abs_of_pos (div_pos hb (by linarith)), div_le_iff₀ (by linarith)]
    nlinarith
  · obtain ⟨h1, h2⟩ := wf_endow_bounds hV t ω
    have hb := pow_pos hβ0 t
    simp only [lamW]
    rw [inv_div, abs_of_pos (div_pos (by linarith) hb)]
    exact div_le_div_of_nonneg_right h2 hb.le

/-- Cochrane (2023), (19.32), p. 450: in the wedge economy the bond price is
`Q_t = q(y_t) = y_t/4` almost surely (genuinely random). -/
theorem wedge_bondPrice (hβ0 : 0 < β) (hV : 0 < V) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, bondPrice (iidSystem ν) (lamW β V) (priceLvl ν β V) t ω =
      qf (endow t ω) := by
  set f : ℝ → ℝ := fun x => 1 / wf V (2 + clamp x / 2) with hf
  have hfm : Measurable f :=
    measurable_const.div (measurable_const.add (measurable_const.mul
      (measurable_const.sub (((continuous_clamp.measurable.div_const 2).const_add 2).div_const
        4))))
  have hfb : ∀ x, |f x| ≤ 8 / 3 := fun x => by
    have hc := abs_le.1 (abs_clamp_le x)
    obtain ⟨h1, -⟩ := wf_bounds (x := 2 + clamp x / 2) hV (by linarith) (by linarith)
    rw [abs_of_pos (by simp only [hf]; exact one_div_pos.2 (by linarith)), hf,
      div_le_iff₀ (by linarith)]
    nlinarith
  have hfi : Integrable (fun ω : ℕ → ℝ => f (ω (t + 1))) (iidSystem ν).μ :=
    Integrable.of_bound ((hfm.comp (measurable_pi_apply (t + 1))).aestronglyMeasurable)
      (8 / 3) (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfb _)
  set Z : (ℕ → ℝ) → ℝ := fun ω => β ^ (t + 1) / (priceLvl ν β V t ω * gf ν β V (endow t ω))
    with hZ
  have hZm : StronglyMeasurable[(iidSystem ν).𝓕 t] Z := by
    have he := (measurable_endow ν t).measurable
    have hg : Measurable[(iidSystem ν).𝓕 t] (fun ω => gf ν β V (endow t ω)) :=
      ((measurable_const.mul (measurable_const.add (measurable_const.mul
        (measurable_const.sub (he.div_const 4))))).mul_const _).div (he.div_const 4)
    exact (measurable_const.div ((priceLvl_meas t).measurable.mul hg)).stronglyMeasurable
  obtain ⟨B, hB⟩ := priceLvl_bdd (ν := ν) hβ0 hV t
  have hZK : ∀ᵐ ω ∂(iidSystem ν).μ, |Z ω| ≤ β ^ (t + 1) * (B *
      ((5 / 8) / (β * (3 / 8) * (1 / (1 + |1 / V - 1|))))) := Eventually.of_forall fun ω => by
    obtain ⟨g0, -, g2⟩ := gf_bounds (ν := ν) hβ0 hV t ω
    have hP := priceLvl_pos (ν := ν) hβ0 hV t ω
    simp only [hZ]
    rw [abs_div, abs_of_pos (pow_pos hβ0 _), div_eq_mul_inv, abs_mul, mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (pow_pos hβ0 _).le
    rw [← abs_inv, ← abs_inv, abs_of_pos (inv_pos.2 g0)]
    exact mul_le_mul (hB ω).2 g2 (inv_pos.2 g0).le ((abs_nonneg _).trans (hB ω).2)
  have e : pk (lamW β V) (priceLvl ν β V) (t + 1) = Z * fun ω => f (ω (t + 1)) := by
    funext ω
    simp only [pk, lamW, priceLvl, Pi.mul_apply, hZ, hf, endow]
    ring
  filter_upwards [(iidSystem ν).E_pullOut hZm hZK hfi, E_shock_fun ν t hfm] with ω h1 h2
  simp only [bondPrice]
  rw [e, h1, Pi.mul_apply, h2]
  obtain ⟨g0, -, -⟩ := gf_bounds (ν := ν) hβ0 hV t ω
  have hP := (priceLvl_pos (ν := ν) hβ0 hV t ω).ne'
  have hw := (show 0 < wf V (endow t ω) by linarith [(wf_endow_bounds hV t ω).1]).ne'
  have hc := (lt_of_lt_of_le (by positivity) (cnu_bounds ν hV).1).ne'
  have hq := (show 0 < qf (endow t ω) by
    simp only [qf]; linarith [(endow_bounds t ω).1]).ne'
  have hb := (pow_pos hβ0 t).ne'
  have hβ := hβ0.ne'
  change Z ω * cnu ν V / pk (lamW β V) (priceLvl ν β V) t ω = qf (endow t ω)
  simp only [hZ, pk, lamW, gf]
  field_simp
  ring

/-- Cochrane (2023), p. 450 (`CashInAdvance.MoneyDemand.binding_cost_wedge`): in the wedge economy
the consumption wedge is `w_t = w(y_t) = 1 + (1/V − 1)(1 − y_t/4)` almost surely (genuinely
random when `V ≠ 1`). -/
theorem wedge_eq (hβ0 : 0 < β) (hV : 0 < V) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, wedge (iidSystem ν) (1 / V - 1) (lamW β V) (priceLvl ν β V) t ω =
      wf V (endow t ω) := by
  filter_upwards [wedge_bondPrice hβ0 hV t] with ω h
  simp only [wedge, iota, h, wf]

/-- Cochrane (2023), §19.5.1–19.5.2, pp. 448–450, **the i.i.d. cash-in-advance economy with any
velocity `V > 0`**: on `ExpectationsMeasureIID.iidSystem ν`, with `0 < β < 1`, linear utility
`u(c) = c`, the endogenous price level `P_{t+1} = P_tg(y_t)`, state prices
`Λ_t = βᵗ/w(y_t)` and transfers `taxesW`, consuming the endowment with the binding overnight money
`m_t = y_t/V` and no bonds is optimal (`CashInAdvanceMeasure.optimal_of_foc`). -/
theorem iid_optimal (hβ0 : 0 < β) (hβ1 : β < 1) (hV : 0 < V) :
    CIAOptimal (iidSystem ν) β (fun x => x) V (lamW β V) (priceLvl ν β V) endow
      (taxesW ν β V) (fun _ => 0) (fun _ => 0) endow (moneyW V) (fun _ _ => 0) := by
  set S := iidSystem ν with hS
  have hp : PriceRegular S (lamW β V) (priceLvl ν β V) := wedge_priceRegular hβ0 hV
  have ae : ∀ {k : ℕ} {f : (ℕ → ℝ) → ℝ}, StronglyMeasurable[S.𝓕 k] f →
      AEStronglyMeasurable f S.μ := fun {k} _ h => (h.mono (S.𝓕.le k)).aestronglyMeasurable
  have hint : ∀ {k : ℕ} {f : (ℕ → ℝ) → ℝ}, StronglyMeasurable[S.𝓕 k] f → BddAt S f →
      Integrable f S.μ := fun h hb => hb.integrable (ae h)
  have hym := fun t => measurable_endow ν t
  have hyb : ∀ t, BddAt S (endow t) := fun t => ⟨5 / 2, Eventually.of_forall fun ω => by
    have h1 := endow_bounds t ω; rw [abs_le]; constructor <;> linarith⟩
  have hmm : ∀ t, StronglyMeasurable[S.𝓕 t] (moneyW V t) := fun t =>
    ((hym t).measurable.div_const V).stronglyMeasurable
  have hmb : ∀ t, BddAt S (moneyW V t) := fun t =>
    ((hyb t).mul (BddAt.const V⁻¹)).congr (Eventually.of_forall fun ω => by
      simp [moneyW, div_eq_mul_inv])
  have hPb : ∀ t, BddAt S (priceLvl ν β V t) := fun t => (hp.2.2.2.2 t).2.2.1
  have hNm : ∀ t, StronglyMeasurable[S.𝓕 t] (moneyIn (fun _ => 0) (priceLvl ν β V)
      (moneyW V) t) := by
    intro t
    cases t with
    | zero => exact stronglyMeasurable_const
    | succ k => exact ((priceLvl_meas k).mul (hmm k)).mono (S.𝓕.mono (Nat.le_succ k))
  have hNb : ∀ t, BddAt S (moneyIn (fun _ => 0) (priceLvl ν β V) (moneyW V) t) := by
    intro t
    cases t with
    | zero => exact BddAt.const 0
    | succ k => exact (hPb k).mul (hmb k)
  have hNpos : ∀ t ω, 0 ≤ moneyIn (fun _ => 0) (priceLvl ν β V) (moneyW V) t ω := by
    intro t ω
    cases t with
    | zero => exact le_rfl
    | succ k =>
      exact mul_nonneg (priceLvl_pos hβ0 hV k ω).le
        (div_nonneg (by linarith [(endow_bounds k ω).1]) hV.le)
  have hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (taxesW ν β V t) := fun t =>
    ((((hNm t).sub ((priceLvl_meas t).mul (hmm t))).measurable.div
      (priceLvl_meas t).measurable)).stronglyMeasurable
  have hsb : ∀ t, BddAt S (taxesW ν β V t) := fun t =>
    (((hNb t).sub ((hPb t).mul (hmb t))).mul (hp.2.2.2.2 t).2.2.2).congr
      (Eventually.of_forall fun ω => by simp [taxesW, div_eq_mul_inv])
  -- feasibility
  have hflow : Flow S (lamW β V) (priceLvl ν β V) endow (taxesW ν β V) (fun _ => 0) endow
      (moneyW V) (fun _ _ => 0) := by
    intro t
    refine Eventually.of_forall fun ω => ?_
    have e0 : S.E t (fun _ => (0 : ℝ)) = 0 := S.E_zero t
    have hP := (priceLvl_pos (ν := ν) hβ0 hV t ω).ne'
    simp only [claimCost, mul_zero, e0, taxesW, Pi.zero_apply, zero_div, sub_self, zero_add]
    field_simp
    ring
  have hfeas : Feasible S (lamW β V) (priceLvl ν β V) endow (taxesW ν β V) (fun _ => 0)
      (fun _ => 0) endow (moneyW V) (fun _ _ => 0) := by
    refine ⟨rfl, hym, hmm, fun _ => stronglyMeasurable_const, hflow, fun t => by simp,
      fun t => hint ((hp.stronglyMeasurable_pk t).mul (hNm t)) ((hp.pk_bdd t).mul (hNb t)),
      fun t => hint ((hp.1 t).mul (hmm t)) ((hp.2.2.2.2 t).1.mul (hmb t)),
      fun t => hint ((hp.1 t).mul (hym t)) ((hp.2.2.2.2 t).1.mul (hyb t)),
      fun δ hδ => Eventually.of_forall fun T => ?_⟩
    refine le_trans (by linarith) (integral_nonneg fun ω => ?_)
    simp only [zero_add]
    exact mul_nonneg (hp.pk_pos T ω).le (hNpos T ω)
  -- transversality
  set K₂ := (5 / 8) / (β * (3 / 8) * (1 / (1 + |1 / V - 1|))) with hK₂
  have htvc : Tendsto (wealthPV S (lamW β V) (priceLvl ν β V) (fun _ => 0) (moneyW V)
      (fun _ _ => 0)) atTop (𝓝 0) := by
    set C := 8 / 3 * (5 / 2 / V) * K₂ with hC
    have hb : ∀ T, ‖wealthPV S (lamW β V) (priceLvl ν β V) (fun _ => 0) (moneyW V)
        (fun _ _ => 0) T‖ ≤ C * β ^ T := by
      intro T
      have h := norm_integral_le_of_norm_le_const (μ := S.μ) (C := C * β ^ T)
        (f := fun ω => pk (lamW β V) (priceLvl ν β V) T ω * ((fun _ _ => (0 : ℝ)) T ω +
          moneyIn (fun _ => 0) (priceLvl ν β V) (moneyW V) T ω))
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, zero_add]
          cases T with
          | zero =>
            simp only [moneyIn, mul_zero, abs_zero]
            positivity
          | succ k =>
            obtain ⟨g0, -, g2⟩ := gf_bounds (ν := ν) hβ0 hV k ω
            obtain ⟨w1, -⟩ := wf_endow_bounds hV (k + 1) ω
            obtain ⟨y1, y2⟩ := endow_bounds k ω
            have hP := priceLvl_pos (ν := ν) hβ0 hV k ω
            have e : pk (lamW β V) (priceLvl ν β V) (k + 1) ω *
                moneyIn (fun _ => 0) (priceLvl ν β V) (moneyW V) (k + 1) ω =
                β ^ (k + 1) * ((wf V (endow (k + 1) ω))⁻¹ * (endow k ω / V) *
                  (gf ν β V (endow k ω))⁻¹) := by
              simp only [pk, lamW, priceLvl, moneyIn, moneyW]
              field_simp
            rw [e, abs_mul, abs_of_pos (pow_pos hβ0 _), mul_comm C]
            refine mul_le_mul_of_nonneg_left ?_ (pow_pos hβ0 _).le
            have hwi : (wf V (endow (k + 1) ω))⁻¹ ≤ 8 / 3 := by
              rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
            have hyv : endow k ω / V ≤ 5 / 2 / V := div_le_div_of_nonneg_right y2 hV.le
            rw [abs_of_nonneg (by positivity)]
            calc (wf V (endow (k + 1) ω))⁻¹ * (endow k ω / V) * (gf ν β V (endow k ω))⁻¹
                ≤ 8 / 3 * (5 / 2 / V) * K₂ := by
                  gcongr
              _ = C := rfl)
      rw [probReal_univ, mul_one] at h
      exact h
    have hlim : Tendsto (fun T : ℕ => C * β ^ T) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul C
    exact squeeze_zero_norm hb hlim
  refine optimal_of_foc (u' := fun _ => 1) hβ0 (fun x x' => by ring_nf; exact le_rfl) hp
    (fun t => hint ((hp.1 t).mul (hym t)) ((hp.2.2.2.2 t).1.mul (hyb t)))
    (fun t => hint ((hp.1 t).mul (hsm t)) ((hp.2.2.2.2 t).1.mul (hsb t))) zero_le_one hfeas
    (fun t => Eventually.of_forall fun ω => ⟨by simp only [moneyW]; field_simp; ring_nf; rfl,
      div_nonneg (by linarith [(endow_bounds t ω).1]) hV.le⟩)
    (UAdmissible.of_bdd hβ0.le hβ1 (fun n => ae (hym n)) (K := 5 / 2) fun n ω => by
      have h1 := endow_bounds n ω; rw [abs_le]; constructor <;> linarith)
    (fun t => Eventually.of_forall fun ω => by simp only [moneyW]; field_simp; ring)
    (fun t => (wedge_bondPrice hβ0 hV t).mono fun ω h => by
      rw [← hS] at h
      simp only [iota, h, qf]; linarith [(endow_bounds t ω).2])
    (fun t => (wedge_eq hβ0 hV t).mono fun ω h => by
      rw [← hS] at h
      rw [h]
      have := (show 0 < wf V (endow t ω) by linarith [(wf_endow_bounds hV t ω).1]).ne'
      simp only [lamW, one_mul, mul_one]
      field_simp) htvc

/-- Cochrane (2023), §19.5.2, p. 450 (the fair coin): the coin takes the values `±1` almost
surely. -/
theorem coin_pm : ∀ᵐ x ∂(coin : Measure ℝ), x = 1 ∨ x = -1 := by
  change ∀ᵐ x ∂coinMeasure, x = 1 ∨ x = -1
  rw [ae_iff]
  have hs : MeasurableSet {x : ℝ | ¬ (x = 1 ∨ x = -1)} :=
    ((measurableSet_singleton (1 : ℝ)).union (measurableSet_singleton (-1 : ℝ))).compl
  simp only [coinMeasure, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hs,
    Set.indicator, Set.mem_ofPred_eq]
  norm_num

/-- Cochrane (2023), §19.5.2, p. 450: with coin shocks `E[1/w(y)] = (1/w(5/2) + 1/w(3/2))/2`. -/
theorem cnu_coin (V : ℝ) :
    cnu coin V = (1 / wf V (5 / 2) + 1 / wf V (3 / 2)) / 2 := by
  simp only [cnu, integral_coin, clamp]
  norm_num

/-- Cochrane (2023), eqs. (19.31)–(19.32) and p. 450, **the i.i.d. wedge with coin shocks and
`V ≠ 1`**: on `ExpectationsMeasureIID.iidSystem coin` (every history null), with `0 < β < 1`,
`V > 0`, `V ≠ 1`, the endowment plan of `iid_optimal` is optimal, and
(1) the bond price is genuinely random, `Q_t = y_t/4` almost surely;
(2) the wedge shows in the state prices: `Λ_tw(y_t) = βᵗu'(y_t)` but `Λ_t ≠ βᵗu'(y_t)`;
(3) the corrected (19.32) `Q_t = βE_t[(u'_{t+1}/u'_t)(w_t/w_{t+1})(P_t/P_{t+1})]` holds almost
surely (`CashInAdvanceMeasure.bond_1932`), while
(4) the printed (19.32) `Q_t = βE_t[(u'_{t+1}/u'_t)(P_t/P_{t+1})]` fails almost surely at every
date. -/
theorem coin_wedge (hβ0 : 0 < β) (hβ1 : β < 1) (hV : 0 < V) (hV1 : V ≠ 1) :
    CIAOptimal (iidSystem coin) β (fun x => x) V (lamW β V) (priceLvl coin β V) endow
        (taxesW coin β V) (fun _ => 0) (fun _ => 0) endow (moneyW V) (fun _ _ => 0) ∧
      (∀ t, ∀ᵐ ω ∂(iidSystem coin).μ,
        bondPrice (iidSystem coin) (lamW β V) (priceLvl coin β V) t ω = endow t ω / 4) ∧
      (∀ t ω, lamW β V t ω * wf V (endow t ω) = β ^ t * 1 ∧ lamW β V t ω ≠ β ^ t * 1) ∧
      (∀ t, ∀ᵐ ω ∂(iidSystem coin).μ,
        bondPrice (iidSystem coin) (lamW β V) (priceLvl coin β V) t ω =
          (iidSystem coin).E t (fun ω => β * (1 / 1) *
            (wedge (iidSystem coin) (1 / V - 1) (lamW β V) (priceLvl coin β V) t ω /
              wedge (iidSystem coin) (1 / V - 1) (lamW β V) (priceLvl coin β V) (t + 1) ω) *
            (priceLvl coin β V t ω / priceLvl coin β V (t + 1) ω)) ω) ∧
      ∀ t, ∀ᵐ ω ∂(iidSystem coin).μ,
        bondPrice (iidSystem coin) (lamW β V) (priceLvl coin β V) t ω ≠
          β * (iidSystem coin).E t (fun ω => 1 / 1 *
            (priceLvl coin β V t ω / priceLvl coin β V (t + 1) ω)) ω := by
  have hopt := iid_optimal (ν := coin) hβ0 hβ1 hV
  have hp := wedge_priceRegular (ν := coin) hβ0 hV
  have hθ0 : 1 / V - 1 ≠ 0 := by
    intro h
    apply hV1
    have : 1 / V = 1 := by linarith
    rw [div_eq_one_iff_eq hV.ne'] at this
    exact this.symm
  have hwpos : ∀ x, 3 / 2 ≤ x → x ≤ 5 / 2 → 0 < wf V x := fun x h1 h2 => by
    linarith [(wf_bounds hV h1 h2).1]
  refine ⟨hopt, fun t => (wedge_bondPrice hβ0 hV t).mono fun ω h => by rw [h]; rfl,
    fun t ω => ⟨?_, ?_⟩, fun t => ?_, fun t => ?_⟩
  · have := (hwpos _ (endow_bounds t ω).1 (endow_bounds t ω).2).ne'
    simp only [lamW]
    field_simp
  · intro h
    have hw := hwpos _ (endow_bounds t ω).1 (endow_bounds t ω).2
    have hb := pow_pos hβ0 t
    simp only [lamW, mul_one] at h
    rw [div_eq_iff hw.ne'] at h
    have h1 : wf V (endow t ω) = 1 := by
      have := mul_left_cancel₀ hb.ne' (show β ^ t * wf V (endow t ω) = β ^ t * 1 by linarith)
      exact this
    simp only [wf, qf] at h1
    have h2 : (1 / V - 1) * (1 - endow t ω / 4) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact hθ0 h3
    · linarith [(endow_bounds t ω).2]
  · have hyb : ∀ n, BddAt (iidSystem coin) (endow n) := fun n => ⟨5 / 2,
      Eventually.of_forall fun ω => by
        have h1 := endow_bounds n ω; rw [abs_le]; constructor <;> linarith⟩
    have hmb : ∀ n, BddAt (iidSystem coin) (moneyW V n) := fun n =>
      ((hyb n).mul (BddAt.const V⁻¹)).congr (Eventually.of_forall fun ω => by
        simp [moneyW, div_eq_mul_inv])
    have h := bond_1932 hβ0 (u := fun x => x) (u' := fun _ => 1)
      (fun x => hasDerivAt_id' x) continuous_const hV hopt hp hyb hmb
      (δ := 3 / (2 * V)) (by positivity)
      (fun t => Eventually.of_forall fun ω => by
        simp only [moneyW]
        rw [div_le_div_iff₀ (by positivity) hV]
        nlinarith [(endow_bounds t ω).1])
      (fun t => (wedge_bondPrice hβ0 hV t).mono fun ω h => by
        rw [h]; simp only [qf]; linarith [(endow_bounds t ω).2])
      (fun _ _ => one_ne_zero) t
    exact h
  · -- the printed formula fails
    have hP1 : StronglyMeasurable[(iidSystem coin).𝓕 t]
        (fun ω => 1 / 1 * (priceLvl coin β V t ω / priceLvl coin β V (t + 1) ω)) := by
      have he := (measurable_endow coin t).measurable
      have hg : Measurable[(iidSystem coin).𝓕 t] (fun ω => gf coin β V (endow t ω)) :=
        ((measurable_const.mul (measurable_const.add (measurable_const.mul
          (measurable_const.sub (he.div_const 4))))).mul_const _).div (he.div_const 4)
      exact (measurable_const.mul ((priceLvl_meas t).measurable.div
        ((priceLvl_meas t).measurable.mul hg))).stronglyMeasurable
    have hP1i : Integrable (fun ω => 1 / 1 * (priceLvl coin β V t ω /
        priceLvl coin β V (t + 1) ω)) (iidSystem coin).μ := by
      have hb : BddAt (iidSystem coin) (fun ω => 1 / 1 * (priceLvl coin β V t ω /
          priceLvl coin β V (t + 1) ω)) :=
        ((hp.2.2.2.2 t).2.2.1.mul (hp.2.2.2.2 (t + 1)).2.2.2).congr
          (Eventually.of_forall fun ω => by simp [div_eq_mul_inv])
      exact hb.integrable ((hP1.mono ((iidSystem coin).𝓕.le t)).aestronglyMeasurable)
    have hpm : ∀ᵐ ω ∂(iidSystem coin).μ, ω t = 1 ∨ ω t = -1 :=
      (measurePreserving_eval_infinitePi (fun _ => (coin : Measure ℝ)) t
        ).quasiMeasurePreserving.ae coin_pm
    filter_upwards [wedge_bondPrice hβ0 hV t, hpm] with ω hQ hω
    rw [(iidSystem coin).E_of_stronglyMeasurable hP1 hP1i, hQ]
    intro h
    obtain ⟨g0, -, -⟩ := gf_bounds (ν := coin) hβ0 hV t ω
    have hP := (priceLvl_pos (ν := coin) hβ0 hV t ω).ne'
    have ha := hwpos (5 / 2) (by norm_num) le_rfl
    have hb := hwpos (3 / 2) le_rfl (by norm_num)
    simp only [priceLvl, gf, cnu_coin] at h
    have hyω : endow t ω = 5 / 2 ∨ endow t ω = 3 / 2 := by
      rcases hω with h1 | h1
      · left; simp only [endow, h1, clamp]; norm_num
      · right; simp only [endow, h1, clamp]; norm_num
    have hdiff : wf V (5 / 2) ≠ wf V (3 / 2) := by
      simp only [wf, qf]
      intro h'
      apply hθ0
      nlinarith
    rcases hyω with hy | hy
    · rw [hy] at h
      apply hdiff
      simp only [qf] at h
      field_simp at h
      nlinarith [h]
    · rw [hy] at h
      apply hdiff
      simp only [qf] at h
      field_simp at h
      nlinarith [h]

end IIDWedge

end Cochrane.Monetarism.CashInAdvanceMeasureTVC
