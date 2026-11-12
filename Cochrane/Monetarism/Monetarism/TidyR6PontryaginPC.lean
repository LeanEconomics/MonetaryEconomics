/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6Pontryagin

/-!
# Pontryagin necessity with piecewise-continuous optimal consumption

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix Chapter 4, §4.1.3,
(4.16)–(4.17), pp. 640–641. `TidyR6Pontryagin.costate_necessary` and
`TidyR6Pontryagin.tvc_necessary` assume the optimal consumption path continuous on `[0, ∞)`.
Here consumption may jump: it is only assumed continuous outside a countable set `E_c` and, on
every `[0, b]`, bounded between two positive constants (e.g. piecewise continuous with positive
one-sided limits).

## Main results

* `dubois_reymond_pc`: the du Bois-Reymond lemma for locally integrable `G`: `G(t₁) = G(t₂)` at
  continuity points.
* `aestronglyMeasurable_comp_pos`: `f ∘ g` is a.e. strongly measurable when `f` is continuous on
  `(0, ∞)` and `g > 0` is a.e. measurable.
* `dir_deriv_nonpos_meas`: `TidyR6Pontryagin.dir_deriv_nonpos` with measurability in place of
  continuity.
* `first_variation_pc`: the first variation vanishes at a piecewise-continuous optimum.
* `costate_necessary_pc`: **the costate exists and is `C¹`**: there is `µ̃`, continuous on
  `[0, ∞)`, with `µ̃̇ = (δ + π)µ̃ − v'(m)` at every `t > 0` and `u'(c_t) = µ̃_t` at every `t > 0`
  outside `E_c`. So the costate (4.17) is continuous even when consumption jumps, and it equals
  `u'(c)` wherever consumption is continuous.
* `tvc_necessary_pc`: the transversality condition `e^{−δt}µ̃_tm_t → 0` under the scaling
  condition of `TidyR6Pontryagin.tvc_necessary`.
-/

namespace Cochrane.Monetarism.TidyR6PontryaginPC

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR6PontryaginTools Cochrane.Monetarism.TidyR6Pontryagin

/-! ## Tools -/

/-- **Cochrane (2023), A4 (4.17), p. 640: du Bois-Reymond, one direction, for locally integrable
`G`.** If `G` is interval integrable on every `[a, b] ⊂ (0, ∞)`, continuous at `0 < t₁ < t₂`,
and `G(t₂) < G(t₁)`, some `w > 0` with `t₁ + w < t₂` has
`∫_{t₁}^{t₂+w} G·(ρ_{t₁} − ρ_{t₂}) > 0`.
Generalises `TidyR6PontryaginTools.dubois_reymond_aux`. -/
theorem dubois_reymond_aux_pc {G : ℝ → ℝ}
    (hGi : ∀ a b, 0 < a → a ≤ b → IntervalIntegrable G volume a b) {t1 t2 : ℝ} (h1 : 0 < t1)
    (h12 : t1 < t2) (hc1 : ContinuousAt G t1) (hc2 : ContinuousAt G t2) (hlt : G t2 < G t1) :
    ∃ w, 0 < w ∧ t1 + w < t2 ∧
      0 < ∫ t in t1..(t2 + w), G t * (rho t1 w t - rho t2 w t) := by
  set ε := (G t1 - G t2) / 3 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨η1, hη1, hb1⟩ := Metric.continuousAt_iff.mp hc1 ε hεpos
  obtain ⟨η2, hη2, hb2⟩ := Metric.continuousAt_iff.mp hc2 ε hεpos
  set w := min (min η1 η2 / 2) ((t2 - t1) / 2) with hw
  have hwpos : 0 < w := by
    rw [hw]; refine lt_min (by positivity) (by linarith)
  have hw1 : w < η1 := by
    have : w ≤ min η1 η2 / 2 := min_le_left _ _
    have : min η1 η2 ≤ η1 := min_le_left _ _
    linarith
  have hw2 : w < η2 := by
    have : w ≤ min η1 η2 / 2 := min_le_left _ _
    have : min η1 η2 ≤ η2 := min_le_right _ _
    linarith
  have hw12 : t1 + w < t2 := by
    have : w ≤ (t2 - t1) / 2 := min_le_right _ _
    linarith
  refine ⟨w, hwpos, hw12, ?_⟩
  have hab : t1 ≤ t2 + w := by linarith
  have hGI := hGi t1 (t2 + w) h1 hab
  have hi1 : IntervalIntegrable (fun t => G t * rho t1 w t) volume t1 (t2 + w) :=
    hGI.mul_continuousOn (continuous_rho t1 w).continuousOn
  have hi2 : IntervalIntegrable (fun t => G t * rho t2 w t) volume t1 (t2 + w) :=
    hGI.mul_continuousOn (continuous_rho t2 w).continuousOn
  have hI1 : G t1 - ε ≤ ∫ t in t1..(t2 + w), G t * rho t1 w t := by
    have hmono := intervalIntegral.integral_mono_on hab
      (((continuous_rho t1 w).const_mul (G t1 - ε)).intervalIntegrable _ _) hi1
      (fun t ht => by
        rcases le_or_gt t (t1 + w) with hle | hgt
        · have hd : dist t t1 < η1 := by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1]
          have := hb1 hd
          rw [Real.dist_eq, abs_lt] at this
          exact mul_le_mul_of_nonneg_right (by linarith [this.1]) (rho_nonneg t1 hwpos t)
        · rw [rho_eq_zero_of_gt hwpos hgt]; simp)
    beta_reduce at hmono
    rw [intervalIntegral.integral_const_mul, integral_rho hwpos le_rfl (by linarith),
      mul_one] at hmono
    exact hmono
  have hI2 : ∫ t in t1..(t2 + w), G t * rho t2 w t ≤ G t2 + ε := by
    have hmono := intervalIntegral.integral_mono_on hab hi2
      (((continuous_rho t2 w).const_mul (G t2 + ε)).intervalIntegrable _ _)
      (fun t ht => by
        rcases lt_or_ge t t2 with hlt' | hge
        · rw [rho_eq_zero_of_lt hwpos hlt']; simp
        · have hd : dist t t2 < η2 := by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.2]
          have := hb2 hd
          rw [Real.dist_eq, abs_lt] at this
          exact mul_le_mul_of_nonneg_right (by linarith [this.2]) (rho_nonneg t2 hwpos t))
    beta_reduce at hmono
    rw [intervalIntegral.integral_const_mul, integral_rho hwpos (by linarith) le_rfl,
      mul_one] at hmono
    exact hmono
  have hsplit : ∫ t in t1..(t2 + w), G t * (rho t1 w t - rho t2 w t) =
      (∫ t in t1..(t2 + w), G t * rho t1 w t) - ∫ t in t1..(t2 + w), G t * rho t2 w t := by
    have e : (fun t => G t * (rho t1 w t - rho t2 w t)) =
        fun t => G t * rho t1 w t - G t * rho t2 w t := by funext t; ring
    rw [e]
    exact intervalIntegral.integral_sub hi1 hi2
  rw [hsplit]
  linarith

/-- **Cochrane (2023), A4 (4.17), p. 640: the du Bois-Reymond lemma for locally integrable
`G`.** If `G` is interval integrable on every `[a, b] ⊂ (0, ∞)` and
`∫_{t₁}^{t₂+w} G·(ρ_{t₁} − ρ_{t₂}) = 0` for all bumps, then `G(t₁) = G(t₂)` whenever
`0 < t₁ < t₂` and `G` is continuous at `t₁` and `t₂`.
Generalises `TidyR6PontryaginTools.dubois_reymond`. -/
theorem dubois_reymond_pc {G : ℝ → ℝ}
    (hGi : ∀ a b, 0 < a → a ≤ b → IntervalIntegrable G volume a b)
    (hzero : ∀ t1 t2 w, 0 < t1 → 0 < w → t1 + w < t2 →
      ∫ t in t1..(t2 + w), G t * (rho t1 w t - rho t2 w t) = 0) :
    ∀ t1 t2, 0 < t1 → t1 < t2 → ContinuousAt G t1 → ContinuousAt G t2 → G t1 = G t2 := by
  intro t1 t2 h1 h12 hc1 hc2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hGi' : ∀ a b, 0 < a → a ≤ b → IntervalIntegrable (fun t => -G t) volume a b :=
      fun a b ha hab => (hGi a b ha hab).neg
    obtain ⟨w, hw, hw12, hpos⟩ := dubois_reymond_aux_pc hGi' h1 h12 hc1.neg hc2.neg
      (by linarith)
    have := hzero t1 t2 w h1 hw hw12
    have e : ∫ t in t1..(t2 + w), -G t * (rho t1 w t - rho t2 w t) =
        -∫ t in t1..(t2 + w), G t * (rho t1 w t - rho t2 w t) := by
      rw [← intervalIntegral.integral_neg]; congr 1; funext t; ring
    rw [e, this] at hpos
    simp at hpos
  · obtain ⟨w, hw, hw12, hpos⟩ := dubois_reymond_aux_pc hGi h1 h12 hc1 hc2 hgt
    rw [hzero t1 t2 w h1 hw hw12] at hpos
    exact lt_irrefl _ hpos

/-- Cochrane (2023), A4 p. 640 (measurability): if `f` is continuous on `(0, ∞)` and `g` is
a.e. measurable and a.e. positive, `f ∘ g` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_comp_pos {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    {μ : Measure ℝ} {g : ℝ → ℝ} (hg : AEMeasurable g μ) (hpos : ∀ᵐ t ∂μ, 0 < g t) :
    AEStronglyMeasurable (fun t => f (g t)) μ := by
  classical
  have hF : Measurable ((Set.Ioi (0 : ℝ)).piecewise f fun _ => 0) :=
    hf.measurable_piecewise continuousOn_const measurableSet_Ioi
  refine (hF.comp_aemeasurable hg).aestronglyMeasurable.congr ?_
  filter_upwards [hpos] with t ht
  simp [Set.piecewise_eq_of_mem _ _ _ (Set.mem_Ioi.mpr ht)]

/-- Cochrane (2023), A4 (4.16), p. 640 (measurability): consumption integrable on every
`[0, T]` is a.e. measurable on `(0, ∞)`. -/
theorem aemeasurable_of_locInt {c : ℝ → ℝ} (hci : ∀ T, IntegrableOn c (Set.Icc 0 T)) :
    AEMeasurable c (volume.restrict (Set.Ioi 0)) := by
  have hsub : Set.Ioi (0 : ℝ) ⊆ ⋃ n : ℕ, Set.Icc 0 (n : ℝ) := fun t ht => by
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact Set.mem_iUnion.2 ⟨n, ⟨le_of_lt ht, hn⟩⟩
  have h : AEMeasurable c (volume.restrict (⋃ n : ℕ, Set.Icc 0 (n : ℝ))) :=
    aemeasurable_iUnion_iff.2 fun n => (hci n).aemeasurable
  exact h.mono_measure (Measure.restrict_mono hsub le_rfl)

variable {δ : ℝ} {u v y s π : ℝ → ℝ} {m0 : ℝ} {up vp : ℝ → ℝ}

/-- **Cochrane (2023), A4 (4.16)–(4.17), p. 640: the one-sided first-order condition with
measurability in place of continuity** (otherwise as `TidyR6Pontryagin.dir_deriv_nonpos`). -/
theorem dir_deriv_nonpos_meas (hU : RegularUtility u up) (hV : RegularUtility v vp)
    {c m A B : ℝ → ℝ} {ε0 : ℝ} (hopt : Optimal δ u v y s π m0 c m) (hε0 : 0 < ε0)
    (hmeasF : ∀ ε ∈ Set.Icc 0 ε0, AEStronglyMeasurable
      (felicity δ u v (fun r => c r + ε * A r) (fun r => m r + ε * B r))
      (volume.restrict (Set.Ioi 0)))
    (hpos : ∀ t, 0 < t → ∀ ε ∈ Set.Icc 0 ε0, 0 < c t + ε * A t ∧ 0 < m t + ε * B t)
    (hfeas : ∀ ε ∈ Set.Ioc 0 ε0,
      Feasible y s π m0 (fun r => c r + ε * A r) (fun r => m r + ε * B r))
    (hint1 : IntegrableOn (felicity δ u v (fun r => c r + ε0 * A r) (fun r => m r + ε0 * B r))
      (Set.Ioi 0)) :
    IntegrableOn (fun t => Real.exp (-(δ * t)) * (up (c t) * A t + vp (m t) * B t))
        (Set.Ioi 0) ∧
      ∫ t in Set.Ioi 0, Real.exp (-(δ * t)) * (up (c t) * A t + vp (m t) * B t) ≤ 0 := by
  set F : ℝ → ℝ → ℝ := fun t ε =>
    felicity δ u v (fun r => c r + ε * A r) (fun r => m r + ε * B r) t with hF
  have hF0 : ∀ t, F t 0 = felicity δ u v c m t := fun t => by simp [hF, felicity]
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 < t :=
    ae_restrict_mem measurableSet_Ioi
  refine integral_dirDeriv_nonpos (F := F) hε0 ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hae] with t ht
    have h1 := concaveOn_comp_affine hU.concave (c := c t) (a := A t) (ε0 := ε0)
      fun ε hε => (hpos t ht ε hε).1
    have h2 := concaveOn_comp_affine hV.concave (c := m t) (a := B t) (ε0 := ε0)
      fun ε hε => (hpos t ht ε hε).2
    exact (h1.add h2).smul (Real.exp_pos _).le
  · filter_upwards [hae] with t ht
    have hc0 : 0 < c t := by simpa using (hpos t ht 0 ⟨le_rfl, hε0.le⟩).1
    have hm0 : 0 < m t := by simpa using (hpos t ht 0 ⟨le_rfl, hε0.le⟩).2
    have i1 : HasDerivAt (fun ε => c t + ε * A t) (A t) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (A t)).const_add (c t)
    have i2 : HasDerivAt (fun ε => m t + ε * B t) (B t) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (B t)).const_add (m t)
    have o1 : HasDerivAt (fun ε => u (c t + ε * A t)) (up (c t) * A t) 0 :=
      HasDerivAt.comp_of_eq 0 (hU.deriv (c t) hc0) i1 (by simp)
    have o2 : HasDerivAt (fun ε => v (m t + ε * B t)) (vp (m t) * B t) 0 :=
      HasDerivAt.comp_of_eq 0 (hV.deriv (m t) hm0) i2 (by simp)
    exact ((o1.add o2).const_mul (Real.exp (-(δ * t)))).hasDerivWithinAt
  · exact hmeasF
  · have e : (fun t => F t 0) = felicity δ u v c m := funext hF0
    rw [e]; exact hopt.2.1
  · exact hint1
  · intro ε hε
    simp only [hF0]
    exact hopt.2.2 _ _ (hfeas ε hε)

/-- Cochrane (2023), A4 p. 640 (measurability): the utility flow of an a.e. measurable plan
that is positive on `(0, ∞)` is a.e. strongly measurable on `(0, ∞)`. -/
theorem felicity_aesm (hU : RegularUtility u up) (hV : RegularUtility v vp) {c m : ℝ → ℝ}
    (hc : AEMeasurable c (volume.restrict (Set.Ioi 0)))
    (hm : AEMeasurable m (volume.restrict (Set.Ioi 0)))
    (hpos : ∀ t, 0 < t → 0 < c t ∧ 0 < m t) :
    AEStronglyMeasurable (felicity δ u v c m) (volume.restrict (Set.Ioi 0)) := by
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 < t :=
    ae_restrict_mem measurableSet_Ioi
  have h1 := aestronglyMeasurable_comp_pos hU.continuousOn hc
    (by filter_upwards [hae] with t ht using (hpos t ht).1)
  have h2 := aestronglyMeasurable_comp_pos hV.continuousOn hm
    (by filter_upwards [hae] with t ht using (hpos t ht).2)
  have he : Continuous fun t : ℝ => Real.exp (-(δ * t)) := by fun_prop
  exact he.aestronglyMeasurable.mul (h1.add h2)

/-! ## The first variation and the costate -/

/-- Cochrane (2023), A4 (4.16), p. 640: **piecewise-regular consumption**: on every `[0, b]`
consumption lies between two positive constants. -/
def LocBounded (c : ℝ → ℝ) : Prop :=
  ∀ b, 0 ≤ b → ∃ lo hi, 0 < lo ∧ ∀ t ∈ Set.Icc 0 b, lo ≤ c t ∧ c t ≤ hi

/-- **Cochrane (2023), A4 (4.16)–(4.17), p. 640: the first variation vanishes at an optimum
with locally bounded (possibly discontinuous) consumption.** As
`TidyR6Pontryagin.first_variation`, with continuity of consumption replaced by `LocBounded`. -/
theorem first_variation_pc (hU : RegularUtility u up) (hV : RegularUtility v vp)
    (hπ : Continuous π) {c m : ℝ → ℝ} (hopt : Optimal δ u v y s π m0 c m)
    (hcb : LocBounded c) {h h' : ℝ → ℝ} (hh : ∀ t, HasDerivAt h (h' t) t)
    (hh' : Continuous h') {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hout : ∀ t, t < a ∨ b < t → h t = 0 ∧ h' t = 0) :
    ∫ t in Set.Ioi 0, Real.exp (-(δ * t)) *
      (up (c t) * (-(π t * h t + h' t)) + vp (m t) * h t) = 0 := by
  obtain ⟨hm0, hmc, ⟨E, hE, hmd⟩, hpos, hci⟩ := hopt.1
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hh t).continuousAt
  obtain ⟨k, hk⟩ : ∃ k : ℝ → ℝ, k = fun t => π t * h t + h' t := ⟨_, rfl⟩
  have hkt : ∀ t, k t = π t * h t + h' t := fun t => by rw [hk]
  have hkc : Continuous k := by rw [hk]; exact (hπ.mul hhc).add hh'
  have hKsub : Set.Icc a b ⊆ Set.Ici 0 := fun t ht => le_trans ha.le ht.1
  have hKsub' : Set.Icc a b ⊆ Set.Ioi 0 := fun t ht => lt_of_lt_of_le ha ht.1
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.2 hab
  obtain ⟨lo, hi, hlo, hlohi⟩ := hcb b (le_trans ha.le hab)
  obtain ⟨tm, htm, hmtm⟩ := isCompact_Icc.exists_isMinOn hne (hmc.mono hKsub)
  obtain ⟨Ck, hCk⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hkc.continuousOn
  obtain ⟨Ch, hCh⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hhc.continuousOn
  obtain ⟨Cm, hCm⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hmc.mono hKsub)
  have hmmin : 0 < m tm := (hpos tm (hKsub htm)).2
  set ε0 := min (min (lo / (2 * (|Ck| + 1))) (m tm / (2 * (|Ch| + 1)))) 1 with hε0def
  have hε0 : 0 < ε0 := lt_min (lt_min (by positivity) (by positivity)) one_pos
  have hε0c : ε0 ≤ lo / (2 * (|Ck| + 1)) := (min_le_left _ _).trans (min_le_left _ _)
  have hε0m : ε0 ≤ m tm / (2 * (|Ch| + 1)) := (min_le_left _ _).trans (min_le_right _ _)
  have hε01 : ε0 ≤ 1 := min_le_right _ _
  have hbnd : ∀ ε, |ε| ≤ ε0 → ∀ t ∈ Set.Icc a b,
      lo / 2 ≤ c t + ε * (-k t) ∧ c t + ε * (-k t) ≤ hi + (|Ck| + 1) ∧
      m tm / 2 ≤ m t + ε * h t ∧ m t + ε * h t ≤ |Cm| + (|Ch| + 1) := by
    intro ε hε t htK
    have hk1 : |k t| ≤ |Ck| + 1 := by
      have := hCk t htK; rw [Real.norm_eq_abs] at this; linarith [le_abs_self Ck]
    have hh1 : |h t| ≤ |Ch| + 1 := by
      have := hCh t htK; rw [Real.norm_eq_abs] at this; linarith [le_abs_self Ch]
    have hm1 : m t ≤ |Cm| := by
      have := hCm t htK; rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (m t), le_abs_self Cm]
    have hε1 : |ε| ≤ 1 := hε.trans hε01
    have e1 : |ε * k t| ≤ lo / 2 := by
      rw [abs_mul]
      calc |ε| * |k t| ≤ ε0 * (|Ck| + 1) := mul_le_mul hε hk1 (abs_nonneg _) hε0.le
        _ ≤ lo / (2 * (|Ck| + 1)) * (|Ck| + 1) :=
          mul_le_mul_of_nonneg_right hε0c (by positivity)
        _ = lo / 2 := by field_simp
    have e1' : |ε * k t| ≤ |Ck| + 1 := by
      rw [abs_mul]
      calc |ε| * |k t| ≤ 1 * (|Ck| + 1) := mul_le_mul hε1 hk1 (abs_nonneg _) zero_le_one
        _ = |Ck| + 1 := one_mul _
    have e2 : |ε * h t| ≤ m tm / 2 := by
      rw [abs_mul]
      calc |ε| * |h t| ≤ ε0 * (|Ch| + 1) := mul_le_mul hε hh1 (abs_nonneg _) hε0.le
        _ ≤ m tm / (2 * (|Ch| + 1)) * (|Ch| + 1) :=
          mul_le_mul_of_nonneg_right hε0m (by positivity)
        _ = m tm / 2 := by field_simp
    have e2' : |ε * h t| ≤ |Ch| + 1 := by
      rw [abs_mul]
      calc |ε| * |h t| ≤ 1 * (|Ch| + 1) := mul_le_mul hε1 hh1 (abs_nonneg _) zero_le_one
        _ = |Ch| + 1 := one_mul _
    have hct := hlohi t ⟨le_trans ha.le htK.1, htK.2⟩
    have h3 := isMinOn_iff.1 hmtm t htK
    have h5 := le_abs_self (ε * k t)
    have h5' := neg_abs_le (ε * k t)
    have h6 := neg_abs_le (ε * h t)
    have h6' := le_abs_self (ε * h t)
    have e : c t + ε * -k t = c t - ε * k t := by ring
    rw [e]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have key : ∀ ε, |ε| ≤ ε0 → ∀ t, 0 ≤ t → 0 < c t + ε * (-k t) ∧ 0 < m t + ε * h t := by
    intro ε hε t ht
    by_cases htK : t ∈ Set.Icc a b
    · have := hbnd ε hε t htK
      exact ⟨by linarith [this.1], by linarith [this.2.2.1]⟩
    · have hout' : t < a ∨ b < t := by
        simp only [Set.mem_Icc, not_and_or, not_le] at htK; exact htK
      obtain ⟨h0, h0'⟩ := hout t hout'
      have : k t = 0 := by rw [hkt, h0, h0']; ring
      simp [this, h0, hpos t ht]
  have feas : ∀ ε, |ε| ≤ ε0 →
      Feasible y s π m0 (fun r => c r + ε * (-k r)) (fun r => m r + ε * h r) := by
    intro ε hε
    refine ⟨?_, hmc.add (continuous_const.mul hhc).continuousOn, ⟨E, hE, fun t ht htE => ?_⟩,
      fun t ht => key ε hε t ht, fun T => ?_⟩
    · simp [hm0, (hout 0 (Or.inl ha)).1]
    · have := (hmd t ht htE).add ((hh t).const_mul ε)
      convert this using 1
      beta_reduce
      rw [hkt]; ring
    · exact (hci T).add (continuous_const.mul hkc.neg).integrableOn_Icc
  have hcm := aemeasurable_of_locInt hci
  have hmm : AEMeasurable m (volume.restrict (Set.Ioi 0)) :=
    ((hmc.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi).aemeasurable
  have hmeasF : ∀ ε, |ε| ≤ ε0 → AEStronglyMeasurable
      (felicity δ u v (fun r => c r + ε * (-k r)) (fun r => m r + ε * h r))
      (volume.restrict (Set.Ioi 0)) := fun ε hε =>
    felicity_aesm hU hV (hcm.add (continuous_const.mul hkc.neg).aemeasurable)
      (hmm.add (continuous_const.mul hhc).aemeasurable) (fun t ht => key ε hε t ht.le)
  -- uniform bounds on `[a, b]`
  have hsubU : Set.Icc (lo / 2) (hi + (|Ck| + 1)) ⊆ Set.Ioi 0 := fun x hx =>
    lt_of_lt_of_le (by positivity) hx.1
  have hsubV : Set.Icc (m tm / 2) (|Cm| + (|Ch| + 1)) ⊆ Set.Ioi 0 := fun x hx =>
    lt_of_lt_of_le (by positivity) hx.1
  obtain ⟨Ku, hKu⟩ := (isCompact_Icc (a := lo / 2)
    (b := hi + (|Ck| + 1))).exists_bound_of_continuousOn (hU.continuousOn.mono hsubU)
  obtain ⟨Kv, hKv⟩ := (isCompact_Icc (a := m tm / 2)
    (b := |Cm| + (|Ch| + 1))).exists_bound_of_continuousOn (hV.continuousOn.mono hsubV)
  obtain ⟨Ke, hKe⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (f := fun t : ℝ => Real.exp (-(δ * t))) (by fun_prop)
  have hfbd : ∀ ε, |ε| ≤ ε0 → ∀ t ∈ Set.Icc a b,
      |felicity δ u v (fun r => c r + ε * (-k r)) (fun r => m r + ε * h r) t| ≤
        |Ke| * (|Ku| + |Kv|) := by
    intro ε hε t ht
    obtain ⟨b1, b2, b3, b4⟩ := hbnd ε hε t ht
    have hu1 := hKu _ ⟨b1, b2⟩
    have hv1 := hKv _ ⟨b3, b4⟩
    have he1 := hKe t ht
    rw [Real.norm_eq_abs] at hu1 hv1 he1
    simp only [felicity]
    rw [abs_mul]
    refine mul_le_mul (he1.trans (le_abs_self _)) ((abs_add_le _ _).trans
      (add_le_add (hu1.trans (le_abs_self _)) (hv1.trans (le_abs_self _)))) (abs_nonneg _)
      (abs_nonneg _)
  have hF0 : felicity δ u v (fun r => c r + 0 * (-k r)) (fun r => m r + 0 * h r) =
      felicity δ u v c m := by funext t; simp [felicity]
  have hint : ∀ ε, |ε| ≤ ε0 → IntegrableOn
      (felicity δ u v (fun r => c r + ε * (-k r)) (fun r => m r + ε * h r)) (Set.Ioi 0) := by
    intro ε hε
    have hfin : (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Icc a b) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp [Real.volume_Icc])
        (Measure.restrict_apply_le _ _)
    have hdK : IntegrableOn (fun t => felicity δ u v (fun r => c r + ε * (-k r))
        (fun r => m r + ε * h r) t - felicity δ u v c m t) (Set.Icc a b)
        (volume.restrict (Set.Ioi 0)) := by
      refine Measure.integrableOn_of_bounded hfin ((hmeasF ε hε).sub hopt.2.1.1)
        (M := 2 * (|Ke| * (|Ku| + |Kv|))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have h1 := hfbd ε hε t ht
      have h2 := hfbd 0 (by rw [abs_zero]; exact hε0.le) t ht
      rw [hF0] at h2
      rw [Real.norm_eq_abs]
      calc |felicity δ u v (fun r => c r + ε * (-k r)) (fun r => m r + ε * h r) t -
            felicity δ u v c m t| ≤ _ := abs_sub _ _
        _ ≤ _ := by linarith
    rw [IntegrableOn, Measure.restrict_restrict_of_subset hKsub'] at hdK
    have hdiff : IntegrableOn (fun t => felicity δ u v (fun r => c r + ε * (-k r))
        (fun r => m r + ε * h r) t - felicity δ u v c m t) (Set.Ioi 0) := by
      refine IntegrableOn.of_forall_sdiff_eq_zero hdK measurableSet_Ioi ?_
      intro t ht
      have hout' : t < a ∨ b < t := by
        have := ht.2
        simp only [Set.mem_Icc, not_and_or, not_le] at this; exact this
      obtain ⟨h0, h0'⟩ := hout t hout'
      have : k t = 0 := by rw [hkt, h0, h0']; ring
      simp [felicity, this, h0]
    exact (hdiff.add hopt.2.1).congr_fun (fun t _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioi
  have r1 := dir_deriv_nonpos_meas (A := fun r => -k r) (B := h) hU hV hopt hε0
    (fun ε hε => hmeasF ε (by rw [abs_of_nonneg hε.1]; exact hε.2))
    (fun t ht ε hε => key ε (by rw [abs_of_nonneg hε.1]; exact hε.2) t ht.le)
    (fun ε hε => feas ε (by rw [abs_of_pos hε.1]; exact hε.2))
    (hint ε0 (abs_of_pos hε0).le)
  have e1 : ∀ ε, (fun r => c r + ε * k r) = fun r => c r + (-ε) * (-k r) := fun ε => by
    funext r; ring
  have e2 : ∀ ε, (fun r => m r + ε * (-h r)) = fun r => m r + (-ε) * h r := fun ε => by
    funext r; ring
  have r2 := dir_deriv_nonpos_meas (A := k) (B := fun r => -h r) hU hV hopt hε0
    (fun ε hε => by
      rw [e1, e2]; exact hmeasF (-ε) (by rw [abs_neg, abs_of_nonneg hε.1]; exact hε.2))
    (fun t ht ε hε => by
      have := key (-ε) (by rw [abs_neg, abs_of_nonneg hε.1]; exact hε.2) t ht.le
      exact ⟨by linarith [this.1], by linarith [this.2]⟩)
    (fun ε hε => by
      rw [e1, e2]; exact feas (-ε) (by rw [abs_neg, abs_of_pos hε.1]; exact hε.2))
    (by rw [e1, e2]; exact hint (-ε0) (by rw [abs_neg, abs_of_pos hε0]))
  have hneg : (fun t => Real.exp (-(δ * t)) * (up (c t) * k t + vp (m t) * -h t)) =
      fun t => -(Real.exp (-(δ * t)) * (up (c t) * -k t + vp (m t) * h t)) := by
    funext t; ring
  have h2 := r2.2
  rw [hneg, integral_neg] at h2
  have h1 := r1.2
  simp only [hkt] at h1 h2
  linarith

/-- Cochrane (2023), A4 p. 640 (bookkeeping): a function a.e. strongly measurable on `(0, ∞)`
and bounded on `(a, b]`, `0 ≤ a`, is integrable on `(a, b]`. -/
theorem integrableOn_Ioc_of_bdd {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0))) {a b K : ℝ} (ha : 0 ≤ a)
    (hK : ∀ t ∈ Set.Ioc a b, |f t| ≤ K) : IntegrableOn f (Set.Ioc a b) := by
  have hsub : Set.Ioc a b ⊆ Set.Ioi 0 := fun t ht => lt_of_le_of_lt ha ht.1
  have hfin : (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Ioc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Ioc]) (Measure.restrict_apply_le _ _)
  have h := Measure.integrableOn_of_bounded hfin hf (M := K) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]; exact hK t ht)
  rwa [IntegrableOn, Measure.restrict_restrict_of_subset hsub] at h

/-- **Cochrane (2023), A4 (4.17), p. 640: necessity of the costate equation with
piecewise-continuous consumption.** At an optimum whose consumption is continuous at every
`t > 0` outside a countable set `E_c` and `LocBounded` (`π` continuous), there is a costate
`µ̃`, continuous on `[0, ∞)`, differentiable at every `t > 0` with
`µ̃̇_t = (δ + π_t)µ̃_t − v'(m_t)` (i.e. `µ̃̇ − δµ̃ = −v'(m) + µ̃Ṗ/P`), and `u'(c_t) = µ̃_t` at
every `t > 0` outside `E_c`.
Generalises `TidyR6Pontryagin.costate_necessary`. -/
theorem costate_necessary_pc (hU : RegularUtility u up) (hV : RegularUtility v vp)
    (hπ : Continuous π) {c m : ℝ → ℝ} (hopt : Optimal δ u v y s π m0 c m)
    (hcb : LocBounded c) {Ec : Set ℝ} (hEc : Ec.Countable)
    (hcc : ∀ t, 0 < t → t ∉ Ec → ContinuousAt c t) :
    ∃ μt : ℝ → ℝ, ContinuousOn μt (Set.Ici 0) ∧
      (∀ t, 0 < t → HasDerivAt μt ((δ + π t) * μt t - vp (m t)) t) ∧
      ∀ t, 0 < t → t ∉ Ec → up (c t) = μt t := by
  obtain ⟨-, hmc, -, hpos, hci⟩ := hopt.1
  set bf : ℝ → ℝ := fun t => Real.exp (-(δ * t)) * up (c t) with hbf
  set αf : ℝ → ℝ := fun t => Real.exp (-(δ * t)) * (vp (m t) - π t * up (c t)) with hαf
  set Af : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, αf r with hAf
  have hexp : Continuous fun t : ℝ => Real.exp (-(δ * t)) := by fun_prop
  have hIoi : Set.Ioi (0 : ℝ) ⊆ Set.Ici 0 := Set.Ioi_subset_Ici_self
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 < t :=
    ae_restrict_mem measurableSet_Ioi
  have hupc_m : AEStronglyMeasurable (fun t => up (c t)) (volume.restrict (Set.Ioi 0)) :=
    aestronglyMeasurable_comp_pos hU.cont (aemeasurable_of_locInt hci)
      (by filter_upwards [hae] with t ht using (hpos t ht.le).1)
  have hvpm : ContinuousOn (fun t => vp (m t)) (Set.Ici 0) :=
    hV.cont.comp hmc fun t ht => Set.mem_Ioi.mpr (hpos t ht).2
  have hαm : AEStronglyMeasurable αf (volume.restrict (Set.Ioi 0)) :=
    hexp.aestronglyMeasurable.mul (((hvpm.mono hIoi).aestronglyMeasurable measurableSet_Ioi).sub
      (hπ.aestronglyMeasurable.mul hupc_m))
  have hbm : AEStronglyMeasurable bf (volume.restrict (Set.Ioi 0)) :=
    hexp.aestronglyMeasurable.mul hupc_m
  -- bounds on `[0, b]`
  have hbds : ∀ b, 0 ≤ b → ∃ K, ∀ t ∈ Set.Icc 0 b, |αf t| ≤ K ∧ |bf t| ≤ K := by
    intro b hb
    obtain ⟨lo, hi, hlo, hlohi⟩ := hcb b hb
    have hsub : Set.Icc lo hi ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hlo hx.1
    obtain ⟨Ku, hKu⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn
      (hU.cont.mono hsub)
    obtain ⟨Ke, hKe⟩ := (isCompact_Icc (a := 0) (b := b)).exists_bound_of_continuousOn
      hexp.continuousOn
    obtain ⟨Kv, hKv⟩ := (isCompact_Icc (a := 0) (b := b)).exists_bound_of_continuousOn
      (hvpm.mono Set.Icc_subset_Ici_self)
    obtain ⟨Kp, hKp⟩ := (isCompact_Icc (a := 0) (b := b)).exists_bound_of_continuousOn
      hπ.continuousOn
    refine ⟨|Ke| * (|Kv| + |Kp| * |Ku|) + |Ke| * |Ku|, fun t ht => ?_⟩
    have hu1 := hKu (c t) (hlohi t ht)
    have he1 := hKe t ht
    have hv1 := hKv t ht
    have hp1 := hKp t ht
    simp only [Real.norm_eq_abs] at hu1 he1 hv1 hp1
    have hu2 : |up (c t)| ≤ |Ku| := hu1.trans (le_abs_self _)
    have he2 : |Real.exp (-(δ * t))| ≤ |Ke| := he1.trans (le_abs_self _)
    have hv2 : |vp (m t)| ≤ |Kv| := hv1.trans (le_abs_self _)
    have hp2 : |π t| ≤ |Kp| := hp1.trans (le_abs_self _)
    have hb1 : |bf t| ≤ |Ke| * |Ku| := by
      simp only [hbf, abs_mul]; exact mul_le_mul he2 hu2 (abs_nonneg _) (abs_nonneg _)
    have ha1 : |αf t| ≤ |Ke| * (|Kv| + |Kp| * |Ku|) := by
      simp only [hαf, abs_mul]
      refine mul_le_mul he2 ((abs_sub _ _).trans (add_le_add hv2 ?_)) (abs_nonneg _)
        (abs_nonneg _)
      rw [abs_mul]; exact mul_le_mul hp2 hu2 (abs_nonneg _) (abs_nonneg _)
    have h0 : 0 ≤ |Ke| * (|Kv| + |Kp| * |Ku|) := by positivity
    have h0' : 0 ≤ |Ke| * |Ku| := by positivity
    exact ⟨by linarith, by linarith⟩
  have hαI : ∀ a b, 0 ≤ a → a ≤ b → IntervalIntegrable αf volume a b := by
    intro a b ha hab
    obtain ⟨K, hK⟩ := hbds b (ha.trans hab)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact integrableOn_Ioc_of_bdd hαm ha fun t ht =>
      (hK t ⟨(ha.trans_lt ht.1).le, ht.2⟩).1
  have hbI : ∀ a b, 0 ≤ a → a ≤ b → IntervalIntegrable bf volume a b := by
    intro a b ha hab
    obtain ⟨K, hK⟩ := hbds b (ha.trans hab)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact integrableOn_Ioc_of_bdd hbm ha fun t ht =>
      (hK t ⟨(ha.trans_lt ht.1).le, ht.2⟩).2
  -- the primitive `A`
  have hAcon : ∀ T, 0 ≤ T → ContinuousOn Af (Set.Icc 0 T) := by
    intro T hT
    have h := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := T)
      (f := αf) (μ := volume) (by
        rw [Set.uIcc_of_le hT, integrableOn_Icc_iff_integrableOn_Ioc]
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 (hαI 0 T le_rfl hT))
    rwa [Set.uIcc_of_le hT] at h
  have hAca : ∀ t, 0 < t → ContinuousAt Af t := fun t ht =>
    (hAcon (t + 1) (by linarith)).continuousAt (Icc_mem_nhds ht (by linarith))
  have hαc : ∀ t, 0 < t → t ∉ Ec → ContinuousAt αf t := by
    intro t ht htE
    have h1 : ContinuousAt (fun r => up (c r)) t :=
      (hU.cont.continuousAt (Ioi_mem_nhds (hpos t ht.le).1)).comp (hcc t ht htE)
    have h2 : ContinuousAt (fun r => vp (m r)) t :=
      (hvpm.mono hIoi).continuousAt (Ioi_mem_nhds ht)
    exact hexp.continuousAt.mul (h2.sub (hπ.continuousAt.mul h1))
  have hAd : ∀ t, 0 < t → t ∉ Ec → HasDerivAt Af (αf t) t := by
    intro t ht htE
    refine intervalIntegral.integral_hasDerivAt_right (hαI 0 t le_rfl ht.le) ?_ (hαc t ht htE)
    refine ⟨Set.Ioo (t / 2) (t + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    exact hαm.mono_measure (Measure.restrict_mono (Set.Ioo_subset_Ioi_self.trans
      (Set.Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ t / 2))) le_rfl)
  set G : ℝ → ℝ := fun t => Af t + bf t with hG
  have hGi : ∀ a b, 0 < a → a ≤ b → IntervalIntegrable G volume a b := fun a b ha hab =>
    ((hAcon b (ha.le.trans hab)).mono (by
      rw [Set.uIcc_of_le hab]; exact Set.Icc_subset_Icc ha.le le_rfl)).intervalIntegrable.add
      (hbI a b ha.le hab)
  have hGc : ∀ t, 0 < t → t ∉ Ec → ContinuousAt G t := fun t ht htE =>
    (hAca t ht).add (hexp.continuousAt.mul
      ((hU.cont.continuousAt (Ioi_mem_nhds (hpos t ht.le).1)).comp (hcc t ht htE)))
  have hzero : ∀ t1 t2 w, 0 < t1 → 0 < w → t1 + w < t2 →
      ∫ t in t1..(t2 + w), G t * (rho t1 w t - rho t2 w t) = 0 := by
    intro t1 t2 w h1 hw h12
    have hab : t1 ≤ t2 + w := by linarith
    have hd : ∀ t, HasDerivAt (fun t => bump t1 w t - bump t2 w t)
        (rho t1 w t - rho t2 w t) t := fun t => (hasDerivAt_bump t1 w t).sub
          (hasDerivAt_bump t2 w t)
    have hdc : Continuous fun t => rho t1 w t - rho t2 w t :=
      (continuous_rho t1 w).sub (continuous_rho t2 w)
    have hbumpc : Continuous fun t => bump t1 w t - bump t2 w t :=
      continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
    have hout : ∀ t, t < t1 ∨ t2 + w < t →
        bump t1 w t - bump t2 w t = 0 ∧ rho t1 w t - rho t2 w t = 0 := by
      rintro t (ht | ht)
      · rw [bump_eq_zero hw ht.le, bump_eq_zero hw (by linarith), rho_eq_zero_of_lt hw ht,
          rho_eq_zero_of_lt hw (by linarith)]
        simp
      · rw [bump_eq_one hw (by linarith), bump_eq_one hw ht.le, rho_eq_zero_of_gt hw
          (by linarith), rho_eq_zero_of_gt hw ht]
        simp
    have hfv := first_variation_pc hU hV hπ hopt hcb hd hdc h1 hab hout
    have hsub : Set.Ioc t1 (t2 + w) ⊆ Set.Ioi 0 := fun t ht => lt_trans h1 ht.1
    have hne1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ t1 := by
      rw [ae_iff]; simp
    rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet hsub
      (by
        filter_upwards [hne1] with t ht htd
        have : t < t1 ∨ t2 + w < t := by
          rcases htd with ⟨_, hn⟩
          simp only [Set.mem_Ioc, not_and_or, not_le, not_lt] at hn
          rcases hn with hn | hn
          · exact Or.inl (lt_of_le_of_ne hn ht)
          · exact Or.inr hn
        obtain ⟨e1, e2⟩ := hout t this
        simp only [sub_eq_zero] at e1 e2
        rw [e1, e2]; ring), ← intervalIntegral.integral_of_le hab] at hfv
    have h1' : 0 ≤ t1 := h1.le
    have i1 : IntervalIntegrable (fun t => αf t * (bump t1 w t - bump t2 w t)) volume t1
        (t2 + w) := (hαI t1 (t2 + w) h1' hab).mul_continuousOn hbumpc.continuousOn
    have i2 : IntervalIntegrable (fun t => bf t * (rho t1 w t - rho t2 w t)) volume t1
        (t2 + w) := (hbI t1 (t2 + w) h1' hab).mul_continuousOn hdc.continuousOn
    have hAcIcc : ContinuousOn Af (Set.Icc t1 (t2 + w)) :=
      (hAcon (t2 + w) (by linarith)).mono (Set.Icc_subset_Icc h1' le_rfl)
    have hAcI : ContinuousOn Af (Set.uIcc t1 (t2 + w)) := by
      rw [Set.uIcc_of_le hab]; exact hAcIcc
    have i3 : IntervalIntegrable (fun t => Af t * (rho t1 w t - rho t2 w t)) volume t1
        (t2 + w) := (hAcI.mul hdc.continuousOn).intervalIntegrable
    have hfv' : ∫ t in t1..(t2 + w), (αf t * (bump t1 w t - bump t2 w t) -
        bf t * (rho t1 w t - rho t2 w t)) = 0 := by
      rw [← hfv]
      congr 1; funext t; simp only [hαf, hbf]; ring
    rw [intervalIntegral.integral_sub i1 i2] at hfv'
    -- integration by parts off the countable set
    have hibp := integral_eq_of_hasDerivAt_off_countable_of_le
      (fun t => Af t * (bump t1 w t - bump t2 w t))
      (fun t => αf t * (bump t1 w t - bump t2 w t) + Af t * (rho t1 w t - rho t2 w t)) hab hEc
      (hAcIcc.mul hbumpc.continuousOn)
      (fun x hx => (hAd x (lt_trans h1 hx.1.1) hx.2).mul (hd x)) (i1.add i3)
    rw [intervalIntegral.integral_add i1 i3] at hibp
    have b1 : bump t1 w (t2 + w) - bump t2 w (t2 + w) = 0 := by
      rw [bump_eq_one hw (by linarith), bump_eq_one hw le_rfl]; ring
    have b2 : bump t1 w t1 - bump t2 w t1 = 0 := by
      rw [bump_eq_zero hw le_rfl, bump_eq_zero hw (by linarith)]; ring
    simp only [b1, b2, mul_zero, sub_zero] at hibp
    have hgoal : ∫ t in t1..(t2 + w), G t * (rho t1 w t - rho t2 w t) =
        ∫ t in t1..(t2 + w), (Af t * (rho t1 w t - rho t2 w t) +
          bf t * (rho t1 w t - rho t2 w t)) := by
      congr 1; funext t; simp only [hG]; ring
    rw [hgoal, intervalIntegral.integral_add i3 i2]
    linarith
  have hconst := dubois_reymond_pc hGi hzero
  -- a reference continuity point
  have hEc0 : volume Ec = 0 := hEc.measure_zero volume
  obtain ⟨tb, htb, htbE⟩ : (Set.Ioi (0 : ℝ) \ Ec).Nonempty :=
    nonempty_of_measure_ne_zero (μ := (volume : Measure ℝ)) (by
      rw [measure_sdiff_null hEc0]; simp)
  have htb0 : (0 : ℝ) < tb := htb
  have hGtb : ∀ t, 0 < t → t ∉ Ec → G t = G tb := by
    intro t ht htE
    rcases lt_trichotomy t tb with h | h | h
    · exact hconst t tb ht h (hGc t ht htE) (hGc tb htb0 htbE)
    · rw [h]
    · exact (hconst tb t htb0 h (hGc tb htb0 htbE) (hGc t ht htE)).symm
  set μt : ℝ → ℝ := fun t => Real.exp (δ * t) * (G tb - Af t) with hμt
  have hμeq : ∀ t, 0 < t → t ∉ Ec → up (c t) = μt t := by
    intro t ht htE
    have h1 := hGtb t ht htE
    simp only [hμt]
    rw [← h1]
    simp only [hG, hbf]
    rw [add_sub_cancel_left, ← mul_assoc, ← Real.exp_add]
    simp
  have hAci : ContinuousOn Af (Set.Ici 0) := fun t ht => by
    have ht0 : (0 : ℝ) ≤ t := ht
    have h1 := (hAcon (t + 1) (by linarith)).continuousWithinAt ⟨ht0, by linarith⟩
    refine h1.mono_of_mem_nhdsWithin ?_
    rw [← Set.Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  have hμcon : ContinuousOn μt (Set.Ici 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (continuousOn_const.sub hAci)
  have hμd0 : ∀ t, 0 < t → t ∉ Ec → HasDerivAt μt ((δ + π t) * μt t - vp (m t)) t := by
    intro t ht htE
    have he : HasDerivAt (fun r => Real.exp (δ * r)) (Real.exp (δ * t) * δ) t :=
      (((hasDerivAt_id' t).const_mul δ).exp).congr_deriv (by ring)
    have := he.mul ((hAd t ht htE).const_sub (G tb))
    refine this.congr_deriv ?_
    have hE : Real.exp (δ * t) * Real.exp (-(δ * t)) = 1 := by rw [← Real.exp_add]; simp
    have hup := hμeq t ht htE
    simp only [hμt] at hup ⊢
    simp only [hαf]
    rw [hup]
    linear_combination (π t * (Real.exp (δ * t) * (G tb - Af t)) - vp (m t)) * hE
  set gf : ℝ → ℝ := fun t => (δ + π t) * μt t - vp (m t) with hgf
  have hgc : ContinuousOn gf (Set.Ioi 0) :=
    ((continuous_const.add hπ).continuousOn.mul (hμcon.mono hIoi)).sub (hvpm.mono hIoi)
  refine ⟨μt, hμcon, fun t ht => ?_, hμeq⟩
  have hloc : ∀ x, 0 < x → μt x = μt t + ∫ r in t..x, gf r := by
    intro x hx
    have hmin : 0 < min t x := lt_min ht hx
    have hsub : Set.uIcc t x ⊆ Set.Ioi 0 := fun r hr => lt_of_lt_of_le hmin hr.1
    have := integral_eq_of_hasDerivAt_off_countable μt gf hEc (hμcon.mono (hsub.trans hIoi))
      (fun r hr => hμd0 r (lt_trans hmin hr.1.1) hr.2) (hgc.mono hsub).intervalIntegrable
    linarith
  have hΨ : HasDerivAt (fun x => μt t + ∫ r in t..x, gf r) (gf t) t :=
    (intervalIntegral.integral_hasDerivAt_right (IntervalIntegrable.refl)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hgc t ht)
      (hgc.continuousAt (Ioi_mem_nhds ht))).const_add (μt t)
  exact hΨ.congr_of_eventuallyEq (by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact hloc x hx)

/-- **Cochrane (2023), A4 (4.17), pp. 640–641: necessity of the transversality condition with
piecewise-continuous consumption.** Under the hypotheses of `costate_necessary_pc`, with
`u' ≥ 0`, `y, s` continuous, `y ≥ s` on `[0, ∞)`, and the scaling condition of
`TidyR6Pontryagin.tvc_necessary` for some `ε₀ ∈ (0, 1)`, every costate `µ̃` as in
`costate_necessary_pc` satisfies `e^{−δt}µ̃_tm_t → 0`. -/
theorem tvc_necessary_pc (hU : RegularUtility u up) (hV : RegularUtility v vp)
    (hup : ∀ x, 0 < x → 0 ≤ up x) (hy : Continuous y) (hs : Continuous s)
    {c m : ℝ → ℝ} (hopt : Optimal δ u v y s π m0 c m) {Ec : Set ℝ} (hEc : Ec.Countable)
    (hys : ∀ t, 0 ≤ t → s t ≤ y t) {ε0 : ℝ} (hε0 : 0 < ε0) (hε1 : ε0 < 1)
    (hscale : IntegrableOn (felicity δ u v (fun r => c r + ε0 * scaleA y s c m r)
      (fun r => m r + ε0 * scaleB m r)) (Set.Ioi 0))
    {μt : ℝ → ℝ} (hμc : ContinuousOn μt (Set.Ici 0))
    (hμd : ∀ t, 0 < t → HasDerivAt μt ((δ + π t) * μt t - vp (m t)) t)
    (hμeq : ∀ t, 0 < t → t ∉ Ec → up (c t) = μt t) :
    Tendsto (fun t => Real.exp (-(δ * t)) * μt t * m t) atTop (𝓝 0) := by
  obtain ⟨hm0, hmc, ⟨E, hE, hmd⟩, hpos, hci⟩ := hopt.1
  have hEc0 : volume Ec = 0 := hEc.measure_zero volume
  have hφ : ∀ t, 0 ≤ t → 0 ≤ 1 - Real.exp (-t) ∧ 1 - Real.exp (-t) < 1 := fun t ht => by
    have h1 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    exact ⟨by linarith, by linarith [Real.exp_pos (-t)]⟩
  have hposS : ∀ t, 0 ≤ t → ∀ ε ∈ Set.Icc 0 ε0,
      0 < c t + ε * scaleA y s c m t ∧ 0 < m t + ε * scaleB m t := by
    intro t ht ε hε
    obtain ⟨hφ0, hφ1⟩ := hφ t ht
    have hεφ : ε * (1 - Real.exp (-t)) < 1 := by
      have : ε * (1 - Real.exp (-t)) ≤ ε * 1 := mul_le_mul_of_nonneg_left hφ1.le hε.1
      linarith [hε.2]
    have hct := (hpos t ht).1
    have hmt := (hpos t ht).2
    constructor
    · have e : c t + ε * scaleA y s c m t = (1 - ε * (1 - Real.exp (-t))) * c t +
          ε * (1 - Real.exp (-t)) * (y t - s t) + ε * Real.exp (-t) * m t := by
        unfold scaleA; ring
      rw [e]
      have h1 : 0 < (1 - ε * (1 - Real.exp (-t))) * c t := mul_pos (by linarith) hct
      have h2 : 0 ≤ ε * (1 - Real.exp (-t)) * (y t - s t) :=
        mul_nonneg (mul_nonneg hε.1 hφ0) (by linarith [hys t ht])
      have h3 : 0 ≤ ε * Real.exp (-t) * m t :=
        mul_nonneg (mul_nonneg hε.1 (Real.exp_pos _).le) hmt.le
      linarith
    · have e : m t + ε * scaleB m t = (1 - ε * (1 - Real.exp (-t))) * m t := by
        unfold scaleB; ring
      rw [e]
      exact mul_pos (by linarith) hmt
  have hφc : Continuous fun r : ℝ => 1 - Real.exp (-r) := by fun_prop
  have hBc : ContinuousOn (scaleB m) (Set.Ici 0) := (hφc.continuousOn.mul hmc).neg
  have hIoi : Set.Ioi (0 : ℝ) ⊆ Set.Ici 0 := Set.Ioi_subset_Ici_self
  have hcm := aemeasurable_of_locInt hci
  have hmm : AEMeasurable m (volume.restrict (Set.Ioi 0)) :=
    ((hmc.mono hIoi).aestronglyMeasurable measurableSet_Ioi).aemeasurable
  have hAm : AEMeasurable (scaleA y s c m) (volume.restrict (Set.Ioi 0)) :=
    (hφc.aemeasurable.mul ((hy.sub hs).aemeasurable.sub hcm)).add
      ((Real.continuous_exp.comp continuous_neg).aemeasurable.mul hmm)
  have hBm : AEMeasurable (scaleB m) (volume.restrict (Set.Ioi 0)) :=
    (hφc.aemeasurable.mul hmm).neg
  have hfeas : ∀ ε ∈ Set.Ioc 0 ε0, Feasible y s π m0 (fun r => c r + ε * scaleA y s c m r)
      (fun r => m r + ε * scaleB m r) := by
    intro ε hε
    refine ⟨?_, hmc.add (continuousOn_const.mul hBc), ⟨E, hE, fun t ht htE => ?_⟩,
      fun t ht => hposS t ht ε ⟨hε.1.le, hε.2⟩, fun T => ?_⟩
    · simp [scaleB, hm0]
    · have hB := ((hasDerivAt_phi t).mul (hmd t ht htE)).neg
      have := (hmd t ht htE).add (hB.const_mul ε)
      refine this.congr_deriv ?_
      simp only [scaleA, scaleB]
      ring
    · have h1 : IntegrableOn (fun r => (1 - ε * (1 - Real.exp (-r))) * c r) (Set.Icc 0 T) :=
        IntegrableOn.continuousOn_mul (by fun_prop) (hci T) isCompact_Icc
      have h2 : IntegrableOn (fun r => ε * (1 - Real.exp (-r)) * (y r - s r) +
          ε * Real.exp (-r) * m r) (Set.Icc 0 T) :=
        ((((continuous_const.mul hφc).mul (hy.sub hs)).continuousOn).add
          ((continuous_const.mul (Real.continuous_exp.comp continuous_neg)).continuousOn.mul
            (hmc.mono Set.Icc_subset_Ici_self))).integrableOn_Icc
      refine (h1.add h2).congr_fun (fun r _ => ?_) measurableSet_Icc
      simp only [Pi.add_apply, scaleA]; ring
  have hD := dir_deriv_nonpos_meas (A := scaleA y s c m) (B := scaleB m) hU hV hopt hε0
    (fun ε hε => felicity_aesm hU hV (hcm.add (aemeasurable_const.mul hAm))
      (hmm.add (aemeasurable_const.mul hBm)) (fun t ht => hposS t ht.le ε hε))
    (fun t ht ε hε => hposS t ht.le ε hε) hfeas hscale
  set D : ℝ → ℝ := fun t => Real.exp (-(δ * t)) *
    (μt t * scaleA y s c m t + vp (m t) * scaleB m t) with hDdef
  have hDae : (fun t => Real.exp (-(δ * t)) *
      (up (c t) * scaleA y s c m t + vp (m t) * scaleB m t)) =ᵐ[volume.restrict (Set.Ioi 0)] D := by
    have hnE : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), t ∉ Ec :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hEc0)
    filter_upwards [hnE, ae_restrict_mem measurableSet_Ioi] with t htE ht
    simp only [hDdef, hμeq t ht htE]
  have hDi : IntegrableOn D (Set.Ioi 0) := hD.1.congr_fun_ae hDae
  have hDle : ∫ t in Set.Ioi 0, D t ≤ 0 := by rw [← integral_congr_ae hDae]; exact hD.2
  set P : ℝ → ℝ := fun t => (1 - Real.exp (-t)) * (Real.exp (-(δ * t)) * μt t * m t)
    with hPdef
  have hPd : ∀ t, 0 < t → t ∉ E → HasDerivAt P (D t) t := by
    intro t ht htE
    have := (hasDerivAt_phi t).mul (((hasDerivAt_disc δ t).mul (hμd t ht)).mul
      (hmd t ht htE))
    refine this.congr_deriv ?_
    rw [hDdef]
    simp only [scaleA, scaleB, Pi.mul_apply]
    ring
  have hexpc : Continuous fun t : ℝ => Real.exp (-(δ * t)) := by fun_prop
  have hPc : ContinuousOn P (Set.Ici 0) :=
    hφc.continuousOn.mul ((hexpc.continuousOn.mul hμc).mul hmc)
  have hP0 : P 0 = 0 := by simp [hPdef]
  have hftc : ∀ R, 0 < R → ∫ t in (0 : ℝ)..R, D t = P R := by
    intro R hR
    have := integral_eq_of_hasDerivAt_off_countable_of_le P D hR.le hE
      (hPc.mono Set.Icc_subset_Ici_self) (fun x hx => hPd x hx.1.1 hx.2)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).2
        (hDi.mono_set Set.Ioc_subset_Ioi_self))
    rw [this, hP0, sub_zero]
  have hPlim : Tendsto P atTop (𝓝 (∫ t in Set.Ioi 0, D t)) := by
    refine (intervalIntegral_tendsto_integral_Ioi 0 hDi tendsto_id).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact hftc R hR
  -- the costate is nonnegative (it is `u' ≥ 0` off a null set and continuous)
  have hμnn : ∀ t, 0 < t → 0 ≤ μt t := by
    intro t ht
    by_contra hneg
    push Not at hneg
    have hca : ContinuousAt μt t := (hμd t ht).continuousAt
    obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.mp hca (-μt t) (by linarith)
    set a := max (t - η) (t / 2) with ha
    have hat : a < t := max_lt (by linarith) (by linarith)
    obtain ⟨r, hr, hrE⟩ : (Set.Ioo a t \ Ec).Nonempty :=
      nonempty_of_measure_ne_zero (μ := (volume : Measure ℝ)) (by
        rw [measure_sdiff_null hEc0, Real.volume_Ioo]; simp [hat])
    have hr0 : 0 < r := lt_of_le_of_lt (le_trans (by linarith) (le_max_right _ _)) hr.1
    have hd : dist r t < η := by
      rw [Real.dist_eq, abs_lt]; constructor
      · linarith [le_max_left (t - η) (t / 2), hr.1]
      · linarith [hr.2]
    have h1 := hball hd
    rw [Real.dist_eq, abs_lt] at h1
    have h2 := hμeq r hr0 hrE
    have h3 := hup _ (hpos r hr0.le).1
    linarith [h1.2]
  have hPnn : ∀ R, 0 < R → 0 ≤ P R := fun R hR =>
    mul_nonneg (hφ R hR.le).1 (mul_nonneg (mul_nonneg (Real.exp_pos _).le (hμnn R hR))
      (hpos R hR.le).2.le)
  have hL0 : 0 ≤ ∫ t in Set.Ioi 0, D t := ge_of_tendsto hPlim
    (by filter_upwards [eventually_gt_atTop 0] with R hR; exact hPnn R hR)
  have hL : ∫ t in Set.Ioi 0, D t = 0 := le_antisymm hDle hL0
  rw [hL] at hPlim
  have hφlim : Tendsto (fun r : ℝ => 1 - Real.exp (-r)) atTop (𝓝 1) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_sub 1
  have hdiv := hPlim.div hφlim one_ne_zero
  rw [zero_div] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hpos' : 0 < 1 - Real.exp (-R) := by
    have : Real.exp (-R) < 1 := by
      have := Real.exp_lt_exp.2 (show -R < 0 by linarith); rwa [Real.exp_zero] at this
    linarith
  simp only [hPdef, Pi.div_apply]
  field_simp

/-- **Cochrane (2023), A4 (4.16)–(4.17), pp. 640–641: Pontryagin necessity with
piecewise-continuous consumption.** At an optimum whose consumption is `LocBounded` and
continuous off a countable set `E_c` (`π, y, s` continuous, `y ≥ s`, `u' ≥ 0`, and the scaling
condition), there is a continuous costate `µ̃` with `u'(c_t) = µ̃_t` off `E_c`,
`µ̃̇ = (δ + π)µ̃ − v'(m)` at every `t > 0`, and `e^{−δt}µ̃_tm_t → 0`. -/
theorem pontryagin_pc (hU : RegularUtility u up) (hV : RegularUtility v vp)
    (hup : ∀ x, 0 < x → 0 ≤ up x) (hπ : Continuous π) (hy : Continuous y) (hs : Continuous s)
    {c m : ℝ → ℝ} (hopt : Optimal δ u v y s π m0 c m) (hcb : LocBounded c) {Ec : Set ℝ}
    (hEc : Ec.Countable) (hcc : ∀ t, 0 < t → t ∉ Ec → ContinuousAt c t)
    (hys : ∀ t, 0 ≤ t → s t ≤ y t) {ε0 : ℝ} (hε0 : 0 < ε0) (hε1 : ε0 < 1)
    (hscale : IntegrableOn (felicity δ u v (fun r => c r + ε0 * scaleA y s c m r)
      (fun r => m r + ε0 * scaleB m r)) (Set.Ioi 0)) :
    ∃ μt : ℝ → ℝ, ContinuousOn μt (Set.Ici 0) ∧
      (∀ t, 0 < t → HasDerivAt μt ((δ + π t) * μt t - vp (m t)) t) ∧
      (∀ t, 0 < t → t ∉ Ec → up (c t) = μt t) ∧
      Tendsto (fun t => Real.exp (-(δ * t)) * μt t * m t) atTop (𝓝 0) := by
  obtain ⟨μt, h1, h2, h3⟩ := costate_necessary_pc hU hV hπ hopt hcb hEc hcc
  exact ⟨μt, h1, h2, h3, tvc_necessary_pc hU hV hup hy hs hopt hEc hys hε0 hε1 hscale h1 h2 h3⟩

end Cochrane.Monetarism.TidyR6PontryaginPC
