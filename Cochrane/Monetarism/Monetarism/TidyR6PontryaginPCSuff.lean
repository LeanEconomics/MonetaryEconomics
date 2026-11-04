/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6PontryaginPC

/-!
# Sufficiency and the characterisation with piecewise-continuous consumption

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix Chapter 4, §4.1.3,
(4.16)–(4.17), pp. 640–641. `TidyR6PontryaginPC.pontryagin_pc` proves the Hamiltonian
conditions necessary when optimal consumption is `LocBounded` and continuous off a countable set
`E_c`, with a continuous costate `µ̃` equal to `u'(c)` off `E_c`. Here they are proved
sufficient for the same class, giving the characterisation.

* `optimal_of_costate_pc`: **sufficiency (Mangasarian/Arrow)**: a feasible plan with integrable
  utility and a costate `µ̃`, continuous on `[0, ∞)`, with `µ̃̇ = (δ + π)µ̃ − v'(m)` at every
  `t > 0`, `u'(c_t) = µ̃_t` off a countable set and `e^{−δt}µ̃_tm_t → 0`, is optimal (no
  continuity of consumption is needed).
* `optimal_iff_pc`: under the hypotheses of `TidyR6PontryaginPC.pontryagin_pc`, the plan is
  optimal iff such a costate exists.
-/

namespace Cochrane.Monetarism.TidyR6PontryaginPCSuff

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR6PontryaginTools Cochrane.Monetarism.TidyR6Pontryagin
open Cochrane.Monetarism.TidyR6PontryaginPC

variable {δ : ℝ} {u v y s π : ℝ → ℝ} {m0 : ℝ} {up vp : ℝ → ℝ}

/-- **Cochrane (2023), A4 (4.16)–(4.17), p. 640: sufficiency with a continuous costate.** With
`u, v` regular and `u' ≥ 0`, a feasible plan with integrable utility, a costate `µ̃` continuous
on `[0, ∞)` with `µ̃̇ = (δ + π)µ̃ − v'(m)` at every `t > 0` and `u'(c_t) = µ̃_t` off a countable
set `E_c`, and the transversality condition `e^{−δt}µ̃_tm_t → 0`, is optimal.
Generalises `TidyR6Pontryagin.optimal_of_costate`. -/
theorem optimal_of_costate_pc (hU : RegularUtility u up) (hV : RegularUtility v vp)
    (hup : ∀ x, 0 < x → 0 ≤ up x) {c m : ℝ → ℝ} (hfeas : Feasible y s π m0 c m)
    (hint : IntegrableOn (felicity δ u v c m) (Set.Ioi 0)) {Ec : Set ℝ} (hEc : Ec.Countable)
    {μt : ℝ → ℝ} (hμc : ContinuousOn μt (Set.Ici 0))
    (hμd : ∀ t, 0 < t → HasDerivAt μt ((δ + π t) * μt t - vp (m t)) t)
    (hμeq : ∀ t, 0 < t → t ∉ Ec → up (c t) = μt t)
    (htvc : Tendsto (fun t => Real.exp (-(δ * t)) * μt t * m t) atTop (𝓝 0)) :
    Optimal δ u v y s π m0 c m := by
  refine ⟨hfeas, hint, fun c' m' hf' => ?_⟩
  obtain ⟨hm0, hmc, ⟨E, hE, hmd⟩, hpos, hci⟩ := hfeas
  have hEc0 : volume Ec = 0 := hEc.measure_zero volume
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
  obtain ⟨hm0', hmc', ⟨E', hE', hmd'⟩, hpos', hci'⟩ := hf'
  set D : ℝ → ℝ := fun t => felicity δ u v c' m' t - felicity δ u v c m t with hDdef
  set g : ℝ → ℝ := fun t => Real.exp (-(δ * t)) *
    (μt t * (c' t - c t) + vp (m t) * (m' t - m t)) with hgdef
  have hDg : ∀ t, 0 < t → t ∉ Ec → D t ≤ g t := by
    intro t ht' htE
    have ht := ht'.le
    have h1 := concave_tangent hU.concave (hpos t ht).1 (hpos' t ht).1 (hU.deriv _ (hpos t ht).1)
    rw [hμeq t ht' htE] at h1
    have h2 := concave_tangent hV.concave (hpos t ht).2 (hpos' t ht).2 (hV.deriv _ (hpos t ht).2)
    simp only [hDdef, hgdef, felicity]
    have he := Real.exp_pos (-(δ * t))
    nlinarith
  set Bf : ℝ → ℝ := fun t => Real.exp (-(δ * t)) * μt t * (m' t - m t) with hBf
  have hBd : ∀ t, 0 < t → t ∉ E ∪ E' → HasDerivAt Bf (-g t) t := by
    intro t ht htE
    have h1 : t ∉ E := fun h => htE (Or.inl h)
    have h2 : t ∉ E' := fun h => htE (Or.inr h)
    have := ((hasDerivAt_disc δ t).mul (hμd t ht)).mul ((hmd' t ht h2).sub (hmd t ht h1))
    refine this.congr_deriv ?_
    simp only [hgdef, Pi.mul_apply, Pi.sub_apply]
    ring
  have hupc : ContinuousOn μt (Set.Ici 0) := hμc
  have hvpm : ContinuousOn (fun t => vp (m t)) (Set.Ici 0) :=
    hV.cont.comp hmc fun t ht => Set.mem_Ioi.mpr (hpos t ht).2
  have hexpc : Continuous fun t : ℝ => Real.exp (-(δ * t)) := by fun_prop
  have hBc : ContinuousOn Bf (Set.Ici 0) :=
    (hexpc.continuousOn.mul hupc).mul (hmc'.sub hmc)
  have hB0 : Bf 0 = 0 := by simp [hBf, hm0, hm0']
  have hgI : ∀ T, 0 ≤ T → IntegrableOn g (Set.Icc 0 T) := by
    intro T hT
    have hK : IsCompact (Set.Icc (0 : ℝ) T) := isCompact_Icc
    have hw : ContinuousOn (fun t => Real.exp (-(δ * t)) * μt t) (Set.Icc 0 T) :=
      (hexpc.continuousOn.mul hupc).mono Set.Icc_subset_Ici_self
    have i1 := IntegrableOn.continuousOn_mul hw (hci' T) hK
    have i0 := IntegrableOn.continuousOn_mul hw (hci T) hK
    have i2 : IntegrableOn (fun t => Real.exp (-(δ * t)) * vp (m t) * (m' t - m t))
        (Set.Icc 0 T) :=
      (((hexpc.continuousOn.mul hvpm).mul (hmc'.sub hmc)) |>.mono
        Set.Icc_subset_Ici_self).integrableOn_Icc
    refine ((i1.sub i0).add i2).congr_fun (fun t _ => ?_) measurableSet_Icc
    simp only [hgdef, Pi.sub_apply, Pi.add_apply]; ring
  have hgint : ∀ T, 0 ≤ T → ∫ t in Set.Ioc 0 T, g t ≤
      Real.exp (-(δ * T)) * μt T * m T := by
    intro T hT
    have hftc := integral_eq_of_hasDerivAt_off_countable_of_le Bf (fun t => -g t) hT
      (hE.union hE') (hBc.mono Set.Icc_subset_Ici_self) (fun x hx => hBd x hx.1.1 hx.2)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 (hgI T hT).neg)
    rw [hB0, sub_zero, intervalIntegral.integral_neg, intervalIntegral.integral_of_le hT]
      at hftc
    have hmT := (hpos' T hT).2
    have hw : 0 ≤ Real.exp (-(δ * T)) * μt T := by
      rcases hT.lt_or_eq with hT' | hT'
      · exact mul_nonneg (Real.exp_pos _).le (hμnn T hT')
      · subst hT'
        have hlim : Tendsto μt (𝓝[>] 0) (𝓝 (μt 0)) :=
          (hμc 0 (Set.mem_Ici.mpr le_rfl)).tendsto.mono_left
            (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
        exact mul_nonneg (Real.exp_pos _).le (ge_of_tendsto hlim
          (by filter_upwards [self_mem_nhdsWithin] with r hr using hμnn r hr))
    have : -(Bf T) ≤ Real.exp (-(δ * T)) * μt T * m T := by
      simp only [hBf]; nlinarith
    linarith
  -- the lintegral comparison on each `(0, n]`
  set N := ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (felicity δ u v c m t - felicity δ u v c' m' t)
    with hN
  have hstep : ∀ n : ℕ, ∫⁻ t in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (D t) ≤
      ENNReal.ofReal (Real.exp (-(δ * n)) * μt n * m n) + N := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hgi : IntegrableOn g (Set.Ioc 0 (n : ℝ)) := (hgI n hn).mono_set Set.Ioc_subset_Icc_self
    set Gp := ∫⁻ t in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (g t) with hGp
    set Gn := ∫⁻ t in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (-g t) with hGn
    have hGp_lt : Gp < ⊤ := lt_of_le_of_lt (lintegral_mono fun t => Real.ofReal_le_enorm (g t))
      hgi.hasFiniteIntegral
    have hGn_lt : Gn < ⊤ := lt_of_le_of_lt (lintegral_mono fun t => by
      have := Real.ofReal_le_enorm (-g t); rwa [enorm_neg] at this) hgi.hasFiniteIntegral
    have hint_eq : ∫ t in Set.Ioc 0 (n : ℝ), g t = Gp.toReal - Gn.toReal :=
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgi
    have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 (n : ℝ))),
        ENNReal.ofReal (D t) + ENNReal.ofReal (-g t) ≤
          ENNReal.ofReal (g t) + ENNReal.ofReal (-D t) := by
      have hnE : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 (n : ℝ))), t ∉ Ec :=
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hEc0)
      filter_upwards [ae_restrict_mem measurableSet_Ioc, hnE] with t ht htE
      exact ofReal_add_neg_le (hDg t ht.1 htE)
    have h1 : (∫⁻ t in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (D t)) + Gn ≤ Gp +
        ∫⁻ t in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (-D t) := by
      calc (∫⁻ t in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (D t)) + Gn
          ≤ ∫⁻ t in Set.Ioc 0 (n : ℝ), (ENNReal.ofReal (D t) + ENNReal.ofReal (-g t)) :=
            le_lintegral_add _ _
        _ ≤ ∫⁻ t in Set.Ioc 0 (n : ℝ), (ENNReal.ofReal (g t) + ENNReal.ofReal (-D t)) :=
            lintegral_mono_ae hpt
        _ = Gp + ∫⁻ t in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (-D t) :=
            lintegral_add_left' hgi.aemeasurable.ennreal_ofReal _
    have h2 : ∫⁻ t in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (-D t) ≤ N := by
      rw [hN]
      refine (lintegral_mono_set Set.Ioc_subset_Ioi_self).trans (le_of_eq ?_)
      congr 1; funext t; simp only [hDdef, neg_sub]
    have h3 : Gp ≤ ENNReal.ofReal (Real.exp (-(δ * n)) * μt n * m n) + Gn := by
      have e : Gp = ENNReal.ofReal ((∫ t in Set.Ioc 0 (n : ℝ), g t) + Gn.toReal) := by
        rw [hint_eq, sub_add_cancel, ENNReal.ofReal_toReal hGp_lt.ne]
      rw [e]
      refine ENNReal.ofReal_add_le.trans (add_le_add (ENNReal.ofReal_le_ofReal (hgint n hn)) ?_)
      rw [ENNReal.ofReal_toReal hGn_lt.ne]
    refine ENNReal.le_of_add_le_add_right hGn_lt.ne ?_
    calc (∫⁻ t in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (D t)) + Gn
        ≤ Gp + ∫⁻ t in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (-D t) := h1
      _ ≤ (ENNReal.ofReal (Real.exp (-(δ * n)) * μt n * m n) + Gn) + N := add_le_add h3 h2
      _ = ENNReal.ofReal (Real.exp (-(δ * n)) * μt n * m n) + N + Gn := by ring
  have hlimE : Tendsto (fun j : ℕ => ENNReal.ofReal (Real.exp (-(δ * j)) * μt j * m j) + N)
      atTop (𝓝 (ENNReal.ofReal 0 + N)) :=
    ((ENNReal.continuous_ofReal.tendsto 0).comp (htvc.comp tendsto_natCast_atTop_atTop)).add
      tendsto_const_nhds
  rw [ENNReal.ofReal_zero, zero_add] at hlimE
  refine lintegral_Ioi_le fun n => ?_
  refine ge_of_tendsto hlimE (eventually_atTop.2 ⟨n, fun j hj => ?_⟩)
  have hnj : (n : ℝ) ≤ j := by exact_mod_cast hj
  refine (lintegral_mono_set (Set.Ioc_subset_Ioc_right hnj)).trans ?_
  exact hstep j


/-- **Cochrane (2023), A4 (4.16)–(4.17), pp. 640–641: the characterisation with
piecewise-continuous consumption.** Let `u, v` be regular with `u' ≥ 0`, `π, y, s` continuous,
`y ≥ s` on `[0, ∞)`, and `(c, m)` feasible with integrable utility, consumption `LocBounded`
and continuous at every `t > 0` off a countable set `E_c`, and the scaling condition for some
`ε₀ ∈ (0, 1)`. Then `(c, m)` is optimal iff there is a costate `µ̃`, continuous on `[0, ∞)`,
with `µ̃̇ = (δ + π)µ̃ − v'(m)` at every `t > 0`, `u'(c_t) = µ̃_t` off `E_c`, and
`e^{−δt}µ̃_tm_t → 0`.
Generalises `TidyR6Pontryagin.optimal_iff`. -/
theorem optimal_iff_pc (hU : RegularUtility u up) (hV : RegularUtility v vp)
    (hup : ∀ x, 0 < x → 0 ≤ up x) (hπ : Continuous π) (hy : Continuous y) (hs : Continuous s)
    (hys : ∀ t, 0 ≤ t → s t ≤ y t) {c m : ℝ → ℝ} (hfeas : Feasible y s π m0 c m)
    (hint : IntegrableOn (felicity δ u v c m) (Set.Ioi 0)) (hcb : LocBounded c) {Ec : Set ℝ}
    (hEc : Ec.Countable) (hcc : ∀ t, 0 < t → t ∉ Ec → ContinuousAt c t) {ε0 : ℝ}
    (hε0 : 0 < ε0) (hε1 : ε0 < 1)
    (hscale : IntegrableOn (felicity δ u v (fun r => c r + ε0 * scaleA y s c m r)
      (fun r => m r + ε0 * scaleB m r)) (Set.Ioi 0)) :
    Optimal δ u v y s π m0 c m ↔
      ∃ μt : ℝ → ℝ, ContinuousOn μt (Set.Ici 0) ∧
        (∀ t, 0 < t → HasDerivAt μt ((δ + π t) * μt t - vp (m t)) t) ∧
        (∀ t, 0 < t → t ∉ Ec → up (c t) = μt t) ∧
        Tendsto (fun t => Real.exp (-(δ * t)) * μt t * m t) atTop (𝓝 0) := by
  constructor
  · intro hopt
    exact pontryagin_pc hU hV hup hπ hy hs hopt hcb hEc hcc hys hε0 hε1 hscale
  · rintro ⟨μt, h1, h2, h3, h4⟩
    exact optimal_of_costate_pc hU hV hup hfeas hint hEc h1 h2 h3 h4

end Cochrane.Monetarism.TidyR6PontryaginPCSuff
