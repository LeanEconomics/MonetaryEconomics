/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6PontryaginTools
import Monetarism.ContinuousTime
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Pontryagin necessity and sufficiency for the Hamiltonian conditions (4.16)–(4.17)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix Chapter 4, §4.1.3,
"A Hamiltonian approach", pp. 640–641 (the money-in-utility problem of Obstfeld (1984)).
`ContinuousTime` proved only the consequences of the first-order conditions. Here the book's
problem is stated precisely and the conditions are proved NECESSARY and SUFFICIENT.

## The problem

Given `δ`, exogenous paths `y, s, π` (`π = Ṗ/P`), initial real balances `m₀`, and utilities
`u, v` concave on `(0, ∞)` with continuous derivatives `u', v'` there (`RegularUtility`):
maximise `∫_0^∞ e^{−δt}(u(c_t) + v(m_t)) dt` over plans `(c, m)` that are **feasible**
(`Feasible`): `m_0 = m₀`, `m` continuous on `[0, ∞)`, the budget (4.16)
`ṁ_t = (y_t − c_t − s_t) − m_tπ_t` at every `t > 0` outside a countable set (so piecewise
continuous consumption is admissible), `c, m > 0` on `[0, ∞)` and `c` integrable on every
`[0, T]`. A plan is **optimal** (`Optimal`) if it is feasible, its utility integrand is
integrable, and no feasible plan has a utility gain whose positive part exceeds its negative
part (`∫⁻(gain)⁺ ≤ ∫⁻(gain)⁻`; for plans with integrable utility this is `U(c', m') ≤ U(c, m)`,
and it also rules out plans with utility `+∞`).

## Main results

* `hamiltonian_partials`: the current-value Hamiltonian `H = u(c) + v(m) + µ(y − c − s − mπ)`
  has `∂H/∂c = u'(c) − µ`, `∂H/∂m = v'(m) − µπ`, `∂H/∂µ = ṁ`, so the conditions (4.17) are
  `u'(c) = µ`, `µ̇ − δµ = −∂H/∂m`.
* `first_variation`: at an optimum with continuous consumption, every compactly supported `C¹`
  variation of real balances has zero first variation (two applications of the concave
  monotone-convergence lemma `TidyR6PontryaginTools.integral_dirDeriv_nonpos`).
* `costate_necessary`: **necessity of the costate equation**: with `µ_t := u'(c_t)`, `µ` is
  differentiable on `(0, ∞)` and `µ̇ = (δ + π)µ − v'(m)`, i.e. `µ̇ − δµ = −v'(m) + µṖ/P`
  ((4.17), second line). No differentiability of `c` is assumed: it is a conclusion (du
  Bois-Reymond, `TidyR6PontryaginTools.dubois_reymond`).
* `tvc_necessary`: **necessity of the transversality condition** (4.17)
  `e^{−δt}u'(c_t)m_t → 0`, if `y − s ≥ 0` and the plan with real balances scaled down by
  `1 − ε₀(1 − e^{−t})` (and consumption raised accordingly) has integrable utility for one
  `ε₀ ∈ (0, 1)` (Kamihigashi's (2001) condition; without some such condition the transversality
  condition is not necessary on an infinite horizon, Halkin (1974)).
* `optimal_of_costate`: **sufficiency (Mangasarian/Arrow)**: a feasible plan with continuous
  consumption and integrable utility satisfying the costate equation and the transversality
  condition is optimal.
* `optimal_iff`: **characterisation**: under the hypotheses of both directions, optimal iff
  costate equation and transversality condition.
* `money_demand_of_optimal`: the book's consequence `v'(m)/u'(c) = −µ̇/µ + δ + Ṗ/P` at every
  `t > 0` (with `ContinuousTime.hamiltonian_money_demand`).
-/

namespace Cochrane.Monetarism.TidyR6Pontryagin

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR6PontryaginTools

variable (f fp : ℝ → ℝ)

/-- Cochrane (2023), A4 p. 640: a regular utility: concave on `(0, ∞)` with derivative `f'`
there, `f'` continuous on `(0, ∞)`. -/
structure RegularUtility where
  concave : ConcaveOn ℝ (Set.Ioi 0) f
  deriv : ∀ x, 0 < x → HasDerivAt f (fp x) x
  cont : ContinuousOn fp (Set.Ioi 0)

variable {f fp}

/-- Cochrane (2023), A4 p. 640: a regular utility is continuous on `(0, ∞)`. -/
theorem RegularUtility.continuousOn (hU : RegularUtility f fp) : ContinuousOn f (Set.Ioi 0) :=
  fun x hx => (hU.deriv x hx).continuousAt.continuousWithinAt

variable (δ : ℝ) (u v : ℝ → ℝ) (y s π : ℝ → ℝ) (m0 : ℝ)

/-- Cochrane (2023), A4 p. 640: the discounted utility flow `e^{−δt}(u(c_t) + v(m_t))`. -/
noncomputable def felicity (c m : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(δ * t)) * (u (c t) + v (m t))

/-- Cochrane (2023), A4 (4.16), p. 640: a feasible plan: `m_0 = m₀`, `m` continuous on
`[0, ∞)`, `ṁ = (y − c − s) − mπ` at every `t > 0` off a countable set, `c, m > 0` on `[0, ∞)`,
and `c` integrable on every `[0, T]`. -/
def Feasible (c m : ℝ → ℝ) : Prop :=
  m 0 = m0 ∧ ContinuousOn m (Set.Ici 0) ∧
    (∃ E : Set ℝ, E.Countable ∧
      ∀ t, 0 < t → t ∉ E → HasDerivAt m (y t - c t - s t - π t * m t) t) ∧
    (∀ t, 0 ≤ t → 0 < c t ∧ 0 < m t) ∧ ∀ T, IntegrableOn c (Set.Icc 0 T)

/-- Cochrane (2023), A4 p. 640, "max `∫_0^∞ e^{−δt}[u(c_t) + v(m_t)] dt`": an optimal plan is
feasible, has integrable utility, and no feasible plan has a utility gain whose positive part
has larger integral than its negative part. -/
def Optimal (c m : ℝ → ℝ) : Prop :=
  Feasible y s π m0 c m ∧ IntegrableOn (felicity δ u v c m) (Set.Ioi 0) ∧
    ∀ c' m', Feasible y s π m0 c' m' →
      ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (felicity δ u v c' m' t - felicity δ u v c m t) ≤
        ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (felicity δ u v c m t - felicity δ u v c' m' t)

/-- Cochrane (2023), A4 p. 640: the current-value Hamiltonian
`H = u(c) + v(m) + µ[(y_t − c − s_t) − mπ_t]`. -/
noncomputable def hamiltonian (c m μ t : ℝ) : ℝ := u c + v m + μ * (y t - c - s t - m * π t)

variable {δ u v y s π m0} {up vp : ℝ → ℝ}

/-- Cochrane (2023), A4 p. 640: **the partial derivatives of the Hamiltonian**:
`∂H/∂c = u'(c) − µ`, `∂H/∂m = v'(m) − µπ_t`, `∂H/∂µ = (y_t − c − s_t) − mπ_t`. So `∂H/∂c = 0`
is `u'(c) = µ`, `−∂H/∂m = µ̇ − δµ` is `µ̇ − δµ = −v'(m) + µπ`, and `∂H/∂µ = ṁ` is (4.16). -/
theorem hamiltonian_partials {upc vpm c m μ t : ℝ} (hu : HasDerivAt u upc c)
    (hv : HasDerivAt v vpm m) :
    HasDerivAt (fun c' => hamiltonian u v y s π c' m μ t) (upc - μ) c ∧
      HasDerivAt (fun m' => hamiltonian u v y s π c m' μ t) (vpm - μ * π t) m ∧
      HasDerivAt (fun μ' => hamiltonian u v y s π c m μ' t) (y t - c - s t - m * π t) μ := by
  refine ⟨?_, ?_, ?_⟩
  · have e : (fun c' => hamiltonian u v y s π c' m μ t) =
        fun c' => (u c' + (v m + μ * (y t - s t - m * π t))) - μ * c' := by
      funext c'; unfold hamiltonian; ring
    rw [e]
    exact ((hu.add_const _).sub ((hasDerivAt_id' c).const_mul μ)).congr_deriv (by ring)
  · have e : (fun m' => hamiltonian u v y s π c m' μ t) =
        fun m' => (v m' + (u c + μ * (y t - c - s t))) - (μ * π t) * m' := by
      funext m'; unfold hamiltonian; ring
    rw [e]
    exact ((hv.add_const _).sub ((hasDerivAt_id' m).const_mul (μ * π t))).congr_deriv (by ring)
  · have e : (fun μ' => hamiltonian u v y s π c m μ' t) =
        fun μ' => (u c + v m) + (y t - c - s t - m * π t) * μ' := by
      funext μ'; unfold hamiltonian; ring
    rw [e]
    exact (((hasDerivAt_id' μ).const_mul (y t - c - s t - m * π t)).const_add
      (u c + v m)).congr_deriv (by ring)

/-- Cochrane (2023), A4 p. 640 (bookkeeping): the utility flow is continuous on any set where
the plan is continuous and positive. -/
theorem felicity_continuousOn (hU : RegularUtility u up) (hV : RegularUtility v vp)
    {c m : ℝ → ℝ} {S : Set ℝ} (hc : ContinuousOn c S) (hm : ContinuousOn m S)
    (hpos : ∀ t ∈ S, 0 < c t ∧ 0 < m t) : ContinuousOn (felicity δ u v c m) S := by
  have h1 : ContinuousOn (fun t => u (c t)) S :=
    hU.continuousOn.comp hc fun t ht => Set.mem_Ioi.mpr (hpos t ht).1
  have h2 : ContinuousOn (fun t => v (m t)) S :=
    hV.continuousOn.comp hm fun t ht => Set.mem_Ioi.mpr (hpos t ht).2
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn.mul
    (h1.add h2)

/-- **Cochrane (2023), A4 (4.16)–(4.17), p. 640: the one-sided first-order condition along a
direction.** At an optimum `(c, m)` (continuous on `(0, ∞)`), let `(A, B)` be continuous on
`(0, ∞)` with `c + εA, m + εB > 0` for `t > 0`, `ε ∈ [0, ε₀]`, the plans `(c + εA, m + εB)`
feasible for `ε ∈ (0, ε₀]`, and the plan at `ε₀` of integrable utility. Then
`e^{−δt}(u'(c)A + v'(m)B)` is integrable on `(0, ∞)` with nonpositive integral. -/
theorem dir_deriv_nonpos (hU : RegularUtility u up) (hV : RegularUtility v vp)
    {c m A B : ℝ → ℝ} {ε0 : ℝ} (hopt : Optimal δ u v y s π m0 c m) (hε0 : 0 < ε0)
    (hc : ContinuousOn c (Set.Ioi 0)) (hm : ContinuousOn m (Set.Ioi 0))
    (hA : ContinuousOn A (Set.Ioi 0)) (hB : ContinuousOn B (Set.Ioi 0))
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
  · intro ε hε
    refine (felicity_continuousOn hU hV (hc.add (continuousOn_const.mul hA))
      (hm.add (continuousOn_const.mul hB)) fun t ht => hpos t ht ε hε).aestronglyMeasurable
      measurableSet_Ioi
  · have e : (fun t => F t 0) = felicity δ u v c m := funext hF0
    rw [e]; exact hopt.2.1
  · exact hint1
  · intro ε hε
    simp only [hF0]
    exact hopt.2.2 _ _ (hfeas ε hε)

/-- **Cochrane (2023), A4 (4.16)–(4.17), p. 640: the first variation vanishes.** At an optimum
with consumption continuous on `[0, ∞)` (`π` continuous), every `C¹` variation `h` of real
balances vanishing with `h'` outside `[a, b] ⊂ (0, ∞)` (consumption varies by `−(πh + ḣ)`,
so (4.16) is preserved) has
`∫_0^∞ e^{−δt}(u'(c_t)(−(π_th_t + ḣ_t)) + v'(m_t)h_t) dt = 0`. -/
theorem first_variation (hU : RegularUtility u up) (hV : RegularUtility v vp)
    (hπ : Continuous π) {c m : ℝ → ℝ} (hopt : Optimal δ u v y s π m0 c m)
    (hc : ContinuousOn c (Set.Ici 0)) {h h' : ℝ → ℝ} (hh : ∀ t, HasDerivAt h (h' t) t)
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
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.2 hab
  obtain ⟨tc, htc, hctc⟩ := isCompact_Icc.exists_isMinOn hne (hc.mono hKsub)
  obtain ⟨tm, htm, hmtm⟩ := isCompact_Icc.exists_isMinOn hne (hmc.mono hKsub)
  obtain ⟨Ck, hCk⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hkc.continuousOn
  obtain ⟨Ch, hCh⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hhc.continuousOn
  have hcmin : 0 < c tc := (hpos tc (hKsub htc)).1
  have hmmin : 0 < m tm := (hpos tm (hKsub htm)).2
  set ε0 := min (c tc / (2 * (|Ck| + 1))) (m tm / (2 * (|Ch| + 1))) with hε0def
  have hε0 : 0 < ε0 := lt_min (by positivity) (by positivity)
  have key : ∀ ε, |ε| ≤ ε0 → ∀ t, 0 ≤ t → 0 < c t + ε * (-k t) ∧ 0 < m t + ε * h t := by
    intro ε hε t ht
    by_cases htK : t ∈ Set.Icc a b
    · have hk1 : |k t| ≤ |Ck| + 1 := by
        have := hCk t htK; rw [Real.norm_eq_abs] at this; linarith [le_abs_self Ck]
      have hh1 : |h t| ≤ |Ch| + 1 := by
        have := hCh t htK; rw [Real.norm_eq_abs] at this; linarith [le_abs_self Ch]
      have h1 : |ε * k t| ≤ c tc / 2 := by
        rw [abs_mul]
        calc |ε| * |k t| ≤ ε0 * (|Ck| + 1) := mul_le_mul hε hk1 (abs_nonneg _) hε0.le
          _ ≤ c tc / (2 * (|Ck| + 1)) * (|Ck| + 1) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
          _ = c tc / 2 := by field_simp
      have h2 : |ε * h t| ≤ m tm / 2 := by
        rw [abs_mul]
        calc |ε| * |h t| ≤ ε0 * (|Ch| + 1) := mul_le_mul hε hh1 (abs_nonneg _) hε0.le
          _ ≤ m tm / (2 * (|Ch| + 1)) * (|Ch| + 1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
          _ = m tm / 2 := by field_simp
      have h3 := isMinOn_iff.1 hctc t htK
      have h4 := isMinOn_iff.1 hmtm t htK
      have h5 := le_abs_self (ε * k t)
      have h6 := neg_abs_le (ε * h t)
      constructor
      · have e : c t + ε * -k t = c t - ε * k t := by ring
        rw [e]; linarith
      · linarith
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
  have hint : ∀ ε, |ε| ≤ ε0 → IntegrableOn
      (felicity δ u v (fun r => c r + ε * (-k r)) (fun r => m r + ε * h r)) (Set.Ioi 0) := by
    intro ε hε
    have hcont1 : ContinuousOn
        (felicity δ u v (fun r => c r + ε * (-k r)) (fun r => m r + ε * h r)) (Set.Icc a b) :=
      felicity_continuousOn hU hV ((hc.mono hKsub).add (continuous_const.mul hkc.neg).continuousOn)
        ((hmc.mono hKsub).add (continuous_const.mul hhc).continuousOn)
        (fun t ht => key ε hε t (hKsub ht))
    have hcont0 : ContinuousOn (felicity δ u v c m) (Set.Icc a b) :=
      felicity_continuousOn hU hV (hc.mono hKsub) (hmc.mono hKsub)
        (fun t ht => hpos t (hKsub ht))
    have hdiff : IntegrableOn (fun t => felicity δ u v (fun r => c r + ε * (-k r))
        (fun r => m r + ε * h r) t - felicity δ u v c m t) (Set.Ioi 0) := by
      refine IntegrableOn.of_forall_sdiff_eq_zero ((hcont1.sub hcont0).integrableOn_Icc)
        measurableSet_Ioi ?_
      intro t ht
      have hout' : t < a ∨ b < t := by
        have := ht.2
        simp only [Set.mem_Icc, not_and_or, not_le] at this; exact this
      obtain ⟨h0, h0'⟩ := hout t hout'
      have : k t = 0 := by rw [hkt, h0, h0']; ring
      simp [felicity, this, h0]
    exact (hdiff.add hopt.2.1).congr_fun (fun t _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioi
  have hIoi : Set.Ioi (0 : ℝ) ⊆ Set.Ici 0 := Set.Ioi_subset_Ici_self
  have r1 := dir_deriv_nonpos (A := fun r => -k r) (B := h) hU hV hopt hε0 (hc.mono hIoi)
    (hmc.mono hIoi) hkc.neg.continuousOn hhc.continuousOn
    (fun t ht ε hε => key ε (by rw [abs_of_nonneg hε.1]; exact hε.2) t ht.le)
    (fun ε hε => feas ε (by rw [abs_of_pos hε.1]; exact hε.2))
    (hint ε0 (abs_of_pos hε0).le)
  have e1 : ∀ ε, (fun r => c r + ε * k r) = fun r => c r + (-ε) * (-k r) := fun ε => by
    funext r; ring
  have e2 : ∀ ε, (fun r => m r + ε * (-h r)) = fun r => m r + (-ε) * h r := fun ε => by
    funext r; ring
  have r2 := dir_deriv_nonpos (A := k) (B := fun r => -h r) hU hV hopt hε0 (hc.mono hIoi)
    (hmc.mono hIoi) hkc.continuousOn hhc.neg.continuousOn
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

/-- **Cochrane (2023), A4 (4.17), p. 640: necessity of the costate equation.** At an optimum
with consumption continuous on `[0, ∞)` (`π` continuous), the costate `µ_t = u'(c_t)` (the
condition `∂H/∂c = 0`) is differentiable at every `t > 0` with
`µ̇_t = (δ + π_t)µ_t − v'(m_t)`, i.e. `µ̇ − δµ = −v'(m) + µṖ/P`. -/
theorem costate_necessary (hU : RegularUtility u up) (hV : RegularUtility v vp)
    (hπ : Continuous π) {c m : ℝ → ℝ} (hopt : Optimal δ u v y s π m0 c m)
    (hc : ContinuousOn c (Set.Ici 0)) :
    ∀ t, 0 < t → HasDerivAt (fun r => up (c r)) ((δ + π t) * up (c t) - vp (m t)) t := by
  obtain ⟨-, hmc, -, hpos, -⟩ := hopt.1
  set bf : ℝ → ℝ := fun t => Real.exp (-(δ * t)) * up (c t) with hbf
  set αf : ℝ → ℝ := fun t => Real.exp (-(δ * t)) * (vp (m t) - π t * up (c t)) with hαf
  set Af : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, αf r with hAf
  have hupc : ContinuousOn (fun t => up (c t)) (Set.Ici 0) :=
    hU.cont.comp hc fun t ht => Set.mem_Ioi.mpr (hpos t ht).1
  have hvpm : ContinuousOn (fun t => vp (m t)) (Set.Ici 0) :=
    hV.cont.comp hmc fun t ht => Set.mem_Ioi.mpr (hpos t ht).2
  have hexp : Continuous fun t : ℝ => Real.exp (-(δ * t)) := by fun_prop
  have hαc : ContinuousOn αf (Set.Ici 0) :=
    hexp.continuousOn.mul (hvpm.sub (hπ.continuousOn.mul hupc))
  have hbc : ContinuousOn bf (Set.Ici 0) := hexp.continuousOn.mul hupc
  have hIoi : Set.Ioi (0 : ℝ) ⊆ Set.Ici 0 := Set.Ioi_subset_Ici_self
  have hAd : ∀ t, 0 < t → HasDerivAt Af (αf t) t := by
    intro t ht
    have hio : IntervalIntegrable αf volume 0 t :=
      (hαc.mono fun r hr => by rw [Set.uIcc_of_le ht.le] at hr; exact hr.1).intervalIntegrable
    exact intervalIntegral.integral_hasDerivAt_right hio
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi (hαc.mono hIoi) t ht)
      ((hαc.mono hIoi).continuousAt (Ioi_mem_nhds ht))
  set G : ℝ → ℝ := fun t => Af t + bf t with hG
  have hAc' : ContinuousOn Af (Set.Ioi 0) := fun t ht =>
    (hAd t ht).continuousAt.continuousWithinAt
  have hGc : ContinuousOn G (Set.Ioi 0) := hAc'.add (hbc.mono hIoi)
  have hzero : ∀ t1 t2 w, 0 < t1 → 0 < w → t1 + w < t2 →
      ∫ t in t1..(t2 + w), G t * (rho t1 w t - rho t2 w t) = 0 := by
    intro t1 t2 w h1 hw h12
    have hab : t1 ≤ t2 + w := by linarith
    have hd : ∀ t, HasDerivAt (fun t => bump t1 w t - bump t2 w t)
        (rho t1 w t - rho t2 w t) t := fun t => (hasDerivAt_bump t1 w t).sub
          (hasDerivAt_bump t2 w t)
    have hdc : Continuous fun t => rho t1 w t - rho t2 w t :=
      (continuous_rho t1 w).sub (continuous_rho t2 w)
    have hout : ∀ t, t < t1 ∨ t2 + w < t →
        bump t1 w t - bump t2 w t = 0 ∧ rho t1 w t - rho t2 w t = 0 := by
      rintro t (ht | ht)
      · rw [bump_eq_zero hw ht.le, bump_eq_zero hw (by linarith), rho_eq_zero_of_lt hw ht,
          rho_eq_zero_of_lt hw (by linarith)]
        simp
      · rw [bump_eq_one hw (by linarith), bump_eq_one hw ht.le, rho_eq_zero_of_gt hw
          (by linarith), rho_eq_zero_of_gt hw ht]
        simp
    have hfv := first_variation hU hV hπ hopt hc hd hdc h1 hab hout
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
    have hmem : ∀ t ∈ Set.uIcc t1 (t2 + w), 0 < t := fun t ht => by
      rw [Set.uIcc_of_le hab] at ht; exact lt_of_lt_of_le h1 ht.1
    have hsubI : Set.uIcc t1 (t2 + w) ⊆ Set.Ici 0 := fun t ht => (hmem t ht).le
    have hbumpc : Continuous fun t => bump t1 w t - bump t2 w t :=
      continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
    have hAc : ContinuousOn Af (Set.uIcc t1 (t2 + w)) :=
      fun t ht => (hAd t (hmem t ht)).continuousAt.continuousWithinAt
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun t => bump t1 w t - bump t2 w t) (v := Af) (fun t _ => hd t)
      (fun t ht => hAd t (hmem t ht)) (hdc.intervalIntegrable _ _)
      ((hαc.mono hsubI).intervalIntegrable)
    have b1 : bump t1 w (t2 + w) - bump t2 w (t2 + w) = 0 := by
      rw [bump_eq_one hw (by linarith), bump_eq_one hw le_rfl]; ring
    have b2 : bump t1 w t1 - bump t2 w t1 = 0 := by
      rw [bump_eq_zero hw le_rfl, bump_eq_zero hw (by linarith)]; ring
    rw [b1, b2, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
    have i1 : IntervalIntegrable (fun t => αf t * (bump t1 w t - bump t2 w t)) volume t1
        (t2 + w) := ((hαc.mono hsubI).mul hbumpc.continuousOn).intervalIntegrable
    have i2 : IntervalIntegrable (fun t => bf t * (rho t1 w t - rho t2 w t)) volume t1
        (t2 + w) := ((hbc.mono hsubI).mul hdc.continuousOn).intervalIntegrable
    have i3 : IntervalIntegrable (fun t => (rho t1 w t - rho t2 w t) * Af t) volume t1
        (t2 + w) := (hdc.continuousOn.mul hAc).intervalIntegrable
    have hfv' : ∫ t in t1..(t2 + w), (αf t * (bump t1 w t - bump t2 w t) -
        bf t * (rho t1 w t - rho t2 w t)) = 0 := by
      rw [← hfv]
      congr 1; funext t; simp only [hαf, hbf]; ring
    rw [intervalIntegral.integral_sub i1 i2] at hfv'
    have hcomm : ∫ t in t1..(t2 + w), (bump t1 w t - bump t2 w t) * αf t =
        ∫ t in t1..(t2 + w), αf t * (bump t1 w t - bump t2 w t) := by
      congr 1; funext t; ring
    have hgoal : ∫ t in t1..(t2 + w), G t * (rho t1 w t - rho t2 w t) =
        ∫ t in t1..(t2 + w), ((rho t1 w t - rho t2 w t) * Af t +
          bf t * (rho t1 w t - rho t2 w t)) := by
      congr 1; funext t; simp only [hG]; ring
    rw [hgoal, intervalIntegral.integral_add i3 i2]
    linarith
  have hconst := dubois_reymond hGc hzero
  have hG1 : ∀ t, 0 < t → G t = G 1 := by
    intro t ht
    rcases lt_trichotomy t 1 with h | h | h
    · exact hconst t 1 ht h
    · rw [h]
    · exact (hconst 1 t one_pos h).symm
  have hbd : ∀ t, 0 < t → HasDerivAt bf (-αf t) t := by
    intro t ht
    have h1 : HasDerivAt (fun x => G 1 - Af x) (-αf t) t := (hAd t ht).const_sub (G 1)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with x hx
    have := hG1 x hx
    simp only [hG] at this
    linarith
  intro t ht
  have hup_eq : (fun r => up (c r)) = fun r => Real.exp (δ * r) * bf r := by
    funext r; simp only [hbf]; rw [← mul_assoc, ← Real.exp_add]; simp
  rw [hup_eq]
  have he : HasDerivAt (fun r => Real.exp (δ * r)) (Real.exp (δ * t) * δ) t := by
    exact (((hasDerivAt_id' t).const_mul δ).exp).congr_deriv (by ring)
  refine (he.mul (hbd t ht)).congr_deriv ?_
  simp only [hbf, hαf]
  have hE : Real.exp (δ * t) * Real.exp (-(δ * t)) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (δ * up (c t) - vp (m t) + π t * up (c t)) * hE

/-! ## Necessity of the transversality condition -/

/-- Cochrane (2023), A4 (4.17), p. 640 (the scaling variation behind the transversality
condition): the consumption direction `φ_t(y_t − s_t − c_t) + φ'_tm_t`, `φ_t = 1 − e^{−t}`,
which keeps (4.16) when real balances are scaled by `1 − εφ_t`. -/
noncomputable def scaleA (y s c m : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 - Real.exp (-t)) * (y t - s t - c t) + Real.exp (-t) * m t

/-- Cochrane (2023), A4 (4.17), p. 640 (the scaling variation): the real-balance direction
`−φ_tm_t`, `φ_t = 1 − e^{−t}`. -/
noncomputable def scaleB (m : ℝ → ℝ) (t : ℝ) : ℝ := -((1 - Real.exp (-t)) * m t)

/-- Cochrane (2023), A4 (4.17), p. 640 (bookkeeping): `φ_t = 1 − e^{−t}` has derivative
`e^{−t}`. -/
theorem hasDerivAt_phi (t : ℝ) : HasDerivAt (fun r => 1 - Real.exp (-r)) (Real.exp (-t)) t :=
  ((hasDerivAt_neg' t).exp.const_sub 1).congr_deriv (by ring)

/-- Cochrane (2023), A4 (4.17), p. 640 (bookkeeping): `t ↦ e^{−δt}` has derivative
`−δe^{−δt}`. -/
theorem hasDerivAt_disc (δ t : ℝ) :
    HasDerivAt (fun r => Real.exp (-(δ * r))) (Real.exp (-(δ * t)) * (-δ)) t :=
  (((hasDerivAt_id' t).const_mul δ).neg.exp).congr_deriv (by simp only [Pi.neg_apply]; ring)

/-- **Cochrane (2023), A4 (4.17), pp. 640–641: necessity of the transversality condition**
`lim e^{−δt}u'(c_t)m_t = 0`. At an optimum with consumption continuous on `[0, ∞)`, with `u' ≥ 0`,
`y, s, π` continuous and `y ≥ s` on `[0, ∞)`, suppose that for one `ε₀ ∈ (0, 1)` the plan with
real balances `(1 − ε₀φ_t)m_t` (`φ_t = 1 − e^{−t}`) and consumption `c + ε₀ scaleA` has
integrable utility (Kamihigashi's condition). Then the transversality condition holds. -/
theorem tvc_necessary (hU : RegularUtility u up) (hV : RegularUtility v vp)
    (hup : ∀ x, 0 < x → 0 ≤ up x) (hπ : Continuous π) (hy : Continuous y) (hs : Continuous s)
    {c m : ℝ → ℝ} (hopt : Optimal δ u v y s π m0 c m) (hc : ContinuousOn c (Set.Ici 0))
    (hys : ∀ t, 0 ≤ t → s t ≤ y t) {ε0 : ℝ} (hε0 : 0 < ε0) (hε1 : ε0 < 1)
    (hscale : IntegrableOn (felicity δ u v (fun r => c r + ε0 * scaleA y s c m r)
      (fun r => m r + ε0 * scaleB m r)) (Set.Ioi 0)) :
    Tendsto (fun t => Real.exp (-(δ * t)) * up (c t) * m t) atTop (𝓝 0) := by
  obtain ⟨hm0, hmc, ⟨E, hE, hmd⟩, hpos, -⟩ := hopt.1
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
  have hAc : ContinuousOn (scaleA y s c m) (Set.Ici 0) :=
    (hφc.continuousOn.mul ((hy.sub hs).continuousOn.sub hc)).add
      ((Real.continuous_exp.comp continuous_neg).continuousOn.mul hmc)
  have hBc : ContinuousOn (scaleB m) (Set.Ici 0) := (hφc.continuousOn.mul hmc).neg
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
    · exact ((hc.add (continuousOn_const.mul hAc)).mono Set.Icc_subset_Ici_self).integrableOn_Icc
  have hIoi : Set.Ioi (0 : ℝ) ⊆ Set.Ici 0 := Set.Ioi_subset_Ici_self
  have hD := dir_deriv_nonpos (A := scaleA y s c m) (B := scaleB m) hU hV hopt hε0
    (hc.mono hIoi) (hmc.mono hIoi) (hAc.mono hIoi) (hBc.mono hIoi)
    (fun t ht ε hε => hposS t ht.le ε hε) hfeas hscale
  have hcost := costate_necessary hU hV hπ hopt hc
  set D : ℝ → ℝ := fun t => Real.exp (-(δ * t)) *
    (up (c t) * scaleA y s c m t + vp (m t) * scaleB m t) with hDdef
  set P : ℝ → ℝ := fun t => (1 - Real.exp (-t)) * (Real.exp (-(δ * t)) * up (c t) * m t)
    with hPdef
  have hPd : ∀ t, 0 < t → t ∉ E → HasDerivAt P (D t) t := by
    intro t ht htE
    have := (hasDerivAt_phi t).mul (((hasDerivAt_disc δ t).mul (hcost t ht)).mul
      (hmd t ht htE))
    refine this.congr_deriv ?_
    rw [hDdef]
    simp only [scaleA, scaleB, Pi.mul_apply]
    ring
  have hupc : ContinuousOn (fun t => up (c t)) (Set.Ici 0) :=
    hU.cont.comp hc fun t ht => Set.mem_Ioi.mpr (hpos t ht).1
  have hexpc : Continuous fun t : ℝ => Real.exp (-(δ * t)) := by fun_prop
  have hPc : ContinuousOn P (Set.Ici 0) :=
    hφc.continuousOn.mul ((hexpc.continuousOn.mul hupc).mul hmc)
  have hP0 : P 0 = 0 := by simp [hPdef]
  have hftc : ∀ R, 0 < R → ∫ t in (0 : ℝ)..R, D t = P R := by
    intro R hR
    have := integral_eq_of_hasDerivAt_off_countable_of_le P D hR.le hE
      (hPc.mono Set.Icc_subset_Ici_self) (fun x hx => hPd x hx.1.1 hx.2)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).2
        (hD.1.mono_set Set.Ioc_subset_Ioi_self))
    rw [this, hP0, sub_zero]
  have hlimI := intervalIntegral_tendsto_integral_Ioi 0 hD.1 tendsto_id
  have hPlim : Tendsto P atTop (𝓝 (∫ t in Set.Ioi 0, D t)) := by
    refine hlimI.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact hftc R hR
  have hPnn : ∀ R, 0 ≤ R → 0 ≤ P R := fun R hR =>
    mul_nonneg (hφ R hR).1 (mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (hup _ (hpos R hR).1)) (hpos R hR).2.le)
  have hL0 : 0 ≤ ∫ t in Set.Ioi 0, D t := ge_of_tendsto hPlim
    (by filter_upwards [eventually_ge_atTop 0] with R hR; exact hPnn R hR)
  have hL : ∫ t in Set.Ioi 0, D t = 0 := le_antisymm hD.2 hL0
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

/-! ## Sufficiency (Mangasarian/Arrow) -/

/-- Cochrane (2023), A4 p. 640 (bookkeeping for sufficiency): if `d ≤ g` then
`d⁺ + g⁻ ≤ g⁺ + d⁻` in `ℝ≥0∞`. -/
theorem ofReal_add_neg_le {d g : ℝ} (h : d ≤ g) :
    ENNReal.ofReal d + ENNReal.ofReal (-g) ≤ ENNReal.ofReal g + ENNReal.ofReal (-d) := by
  rcases le_total 0 d with hd | hd
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -g ≤ 0),
      ENNReal.ofReal_of_nonpos (by linarith : -d ≤ 0), add_zero, add_zero]
    exact ENNReal.ofReal_le_ofReal h
  · rw [ENNReal.ofReal_of_nonpos hd, zero_add]
    rcases le_total 0 g with hg | hg
    · rw [ENNReal.ofReal_of_nonpos (by linarith : -g ≤ 0)]; exact bot_le
    · rw [ENNReal.ofReal_of_nonpos hg, zero_add]
      exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Cochrane (2023), A4 p. 640 (bookkeeping for sufficiency): a lintegral over `(0, ∞)` is
bounded by `N` if its restrictions to every `(0, n]` are. -/
theorem lintegral_Ioi_le {f : ℝ → ENNReal} {N : ENNReal}
    (h : ∀ n : ℕ, ∫⁻ x in Set.Ioc 0 (n : ℝ), f x ≤ N) : ∫⁻ x in Set.Ioi 0, f x ≤ N := by
  have hU : Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Ioc (n : ℝ) (n + 1) := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · intro hx
      refine ⟨⌈x⌉₊ - 1, ?_, ?_⟩
      · have h1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (by positivity)
        have h2 := Nat.ceil_lt_add_one hx.le
        rw [Nat.cast_sub h1]; push_cast; linarith
      · have h1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (by positivity)
        rw [Nat.cast_sub h1]; push_cast; linarith [Nat.le_ceil x]
    · rintro ⟨n, hn, -⟩
      exact lt_of_le_of_lt (Nat.cast_nonneg n) hn
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ => Set.Ioc (n : ℝ) (n + 1)) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hx hx' => hij ?_
    simp only [Set.mem_Ioc] at hx hx'
    have h1 : (i : ℝ) < j + 1 := lt_of_lt_of_le hx.1 hx'.2
    have h2 : (j : ℝ) < i + 1 := lt_of_lt_of_le hx'.1 hx.2
    have h1' : i < j + 1 := by exact_mod_cast h1
    have h2' : j < i + 1 := by exact_mod_cast h2
    omega
  rw [hU, lintegral_iUnion (fun n => measurableSet_Ioc) hdisj]
  refine ENNReal.tsum_le_of_sum_range_le fun K => ?_
  have hsum : ∀ K : ℕ, ∑ i ∈ Finset.range K, ∫⁻ x in Set.Ioc (i : ℝ) (i + 1), f x =
      ∫⁻ x in Set.Ioc 0 (K : ℝ), f x := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, ← lintegral_union measurableSet_Ioc
        (Set.Ioc_disjoint_Ioc_of_le le_rfl)]
      congr 2
      push_cast
      exact Set.Ioc_union_Ioc_eq_Ioc (Nat.cast_nonneg K) (by linarith)
  rw [hsum K]
  exact h K

/-- **Cochrane (2023), A4 (4.16)–(4.17), p. 640: sufficiency (Mangasarian/Arrow).** With
`u, v` regular, `u' ≥ 0`, a feasible plan with consumption continuous on `[0, ∞)` and integrable
utility that satisfies the costate equation `µ̇ = (δ + π)µ − v'(m)` (`µ = u'(c)`) at every
`t > 0` and the transversality condition `e^{−δt}u'(c_t)m_t → 0` is optimal. -/
theorem optimal_of_costate (hU : RegularUtility u up) (hV : RegularUtility v vp)
    (hup : ∀ x, 0 < x → 0 ≤ up x) {c m : ℝ → ℝ} (hfeas : Feasible y s π m0 c m)
    (hc : ContinuousOn c (Set.Ici 0)) (hint : IntegrableOn (felicity δ u v c m) (Set.Ioi 0))
    (hcost : ∀ t, 0 < t → HasDerivAt (fun r => up (c r)) ((δ + π t) * up (c t) - vp (m t)) t)
    (htvc : Tendsto (fun t => Real.exp (-(δ * t)) * up (c t) * m t) atTop (𝓝 0)) :
    Optimal δ u v y s π m0 c m := by
  refine ⟨hfeas, hint, fun c' m' hf' => ?_⟩
  obtain ⟨hm0, hmc, ⟨E, hE, hmd⟩, hpos, -⟩ := hfeas
  obtain ⟨hm0', hmc', ⟨E', hE', hmd'⟩, hpos', hci'⟩ := hf'
  set D : ℝ → ℝ := fun t => felicity δ u v c' m' t - felicity δ u v c m t with hDdef
  set g : ℝ → ℝ := fun t => Real.exp (-(δ * t)) *
    (up (c t) * (c' t - c t) + vp (m t) * (m' t - m t)) with hgdef
  have hDg : ∀ t, 0 ≤ t → D t ≤ g t := by
    intro t ht
    have h1 := concave_tangent hU.concave (hpos t ht).1 (hpos' t ht).1 (hU.deriv _ (hpos t ht).1)
    have h2 := concave_tangent hV.concave (hpos t ht).2 (hpos' t ht).2 (hV.deriv _ (hpos t ht).2)
    simp only [hDdef, hgdef, felicity]
    have he := Real.exp_pos (-(δ * t))
    nlinarith
  set Bf : ℝ → ℝ := fun t => Real.exp (-(δ * t)) * up (c t) * (m' t - m t) with hBf
  have hBd : ∀ t, 0 < t → t ∉ E ∪ E' → HasDerivAt Bf (-g t) t := by
    intro t ht htE
    have h1 : t ∉ E := fun h => htE (Or.inl h)
    have h2 : t ∉ E' := fun h => htE (Or.inr h)
    have := ((hasDerivAt_disc δ t).mul (hcost t ht)).mul ((hmd' t ht h2).sub (hmd t ht h1))
    refine this.congr_deriv ?_
    simp only [hgdef, Pi.mul_apply, Pi.sub_apply]
    ring
  have hupc : ContinuousOn (fun t => up (c t)) (Set.Ici 0) :=
    hU.cont.comp hc fun t ht => Set.mem_Ioi.mpr (hpos t ht).1
  have hvpm : ContinuousOn (fun t => vp (m t)) (Set.Ici 0) :=
    hV.cont.comp hmc fun t ht => Set.mem_Ioi.mpr (hpos t ht).2
  have hexpc : Continuous fun t : ℝ => Real.exp (-(δ * t)) := by fun_prop
  have hBc : ContinuousOn Bf (Set.Ici 0) :=
    (hexpc.continuousOn.mul hupc).mul (hmc'.sub hmc)
  have hB0 : Bf 0 = 0 := by simp [hBf, hm0, hm0']
  have hgI : ∀ T, 0 ≤ T → IntegrableOn g (Set.Icc 0 T) := by
    intro T hT
    have hK : IsCompact (Set.Icc (0 : ℝ) T) := isCompact_Icc
    have hw : ContinuousOn (fun t => Real.exp (-(δ * t)) * up (c t)) (Set.Icc 0 T) :=
      (hexpc.continuousOn.mul hupc).mono Set.Icc_subset_Ici_self
    have i1 := IntegrableOn.continuousOn_mul hw (hci' T) hK
    have i2 : IntegrableOn (fun t => Real.exp (-(δ * t)) * up (c t) * c t -
        Real.exp (-(δ * t)) * vp (m t) * (m' t - m t)) (Set.Icc 0 T) :=
      (((hexpc.continuousOn.mul hupc).mul hc).sub ((hexpc.continuousOn.mul hvpm).mul
        (hmc'.sub hmc)) |>.mono Set.Icc_subset_Ici_self).integrableOn_Icc
    refine (i1.sub i2).congr_fun (fun t _ => ?_) measurableSet_Icc
    simp only [hgdef, Pi.sub_apply]; ring
  have hgint : ∀ T, 0 ≤ T → ∫ t in Set.Ioc 0 T, g t ≤
      Real.exp (-(δ * T)) * up (c T) * m T := by
    intro T hT
    have hftc := integral_eq_of_hasDerivAt_off_countable_of_le Bf (fun t => -g t) hT
      (hE.union hE') (hBc.mono Set.Icc_subset_Ici_self) (fun x hx => hBd x hx.1.1 hx.2)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 (hgI T hT).neg)
    rw [hB0, sub_zero, intervalIntegral.integral_neg, intervalIntegral.integral_of_le hT]
      at hftc
    have hmT := (hpos' T hT).2
    have hw : 0 ≤ Real.exp (-(δ * T)) * up (c T) :=
      mul_nonneg (Real.exp_pos _).le (hup _ (hpos T hT).1)
    have : -(Bf T) ≤ Real.exp (-(δ * T)) * up (c T) * m T := by
      simp only [hBf]; nlinarith
    linarith
  -- the lintegral comparison on each `(0, n]`
  set N := ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (felicity δ u v c m t - felicity δ u v c' m' t)
    with hN
  have hstep : ∀ n : ℕ, ∫⁻ t in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (D t) ≤
      ENNReal.ofReal (Real.exp (-(δ * n)) * up (c n) * m n) + N := by
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
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact ofReal_add_neg_le (hDg t ht.1.le)
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
    have h3 : Gp ≤ ENNReal.ofReal (Real.exp (-(δ * n)) * up (c n) * m n) + Gn := by
      have e : Gp = ENNReal.ofReal ((∫ t in Set.Ioc 0 (n : ℝ), g t) + Gn.toReal) := by
        rw [hint_eq, sub_add_cancel, ENNReal.ofReal_toReal hGp_lt.ne]
      rw [e]
      refine ENNReal.ofReal_add_le.trans (add_le_add (ENNReal.ofReal_le_ofReal (hgint n hn)) ?_)
      rw [ENNReal.ofReal_toReal hGn_lt.ne]
    refine ENNReal.le_of_add_le_add_right hGn_lt.ne ?_
    calc (∫⁻ t in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (D t)) + Gn
        ≤ Gp + ∫⁻ t in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (-D t) := h1
      _ ≤ (ENNReal.ofReal (Real.exp (-(δ * n)) * up (c n) * m n) + Gn) + N := add_le_add h3 h2
      _ = ENNReal.ofReal (Real.exp (-(δ * n)) * up (c n) * m n) + N + Gn := by ring
  have hlimE : Tendsto (fun j : ℕ => ENNReal.ofReal (Real.exp (-(δ * j)) * up (c j) * m j) + N)
      atTop (𝓝 (ENNReal.ofReal 0 + N)) :=
    ((ENNReal.continuous_ofReal.tendsto 0).comp (htvc.comp tendsto_natCast_atTop_atTop)).add
      tendsto_const_nhds
  rw [ENNReal.ofReal_zero, zero_add] at hlimE
  refine lintegral_Ioi_le fun n => ?_
  refine ge_of_tendsto hlimE (eventually_atTop.2 ⟨n, fun j hj => ?_⟩)
  have hnj : (n : ℝ) ≤ j := by exact_mod_cast hj
  refine (lintegral_mono_set (Set.Ioc_subset_Ioc_right hnj)).trans ?_
  exact hstep j

/-! ## The characterisation -/

/-- **Cochrane (2023), A4 (4.16)–(4.17), pp. 640–641: the Hamiltonian conditions characterise
the optimum.** Let `u, v` be regular with `u' ≥ 0`, `y, s, π` continuous, `y ≥ s` on `[0, ∞)`,
and `(c, m)` feasible with consumption continuous on `[0, ∞)`, integrable utility, and the
scaling condition of `tvc_necessary` for some `ε₀ ∈ (0, 1)`. Then `(c, m)` is optimal iff
`µ = u'(c)` satisfies the costate equation `µ̇ = (δ + π)µ − v'(m)` on `(0, ∞)` and the
transversality condition `e^{−δt}µ_tm_t → 0` holds. -/
theorem optimal_iff (hU : RegularUtility u up) (hV : RegularUtility v vp)
    (hup : ∀ x, 0 < x → 0 ≤ up x) (hπ : Continuous π) (hy : Continuous y) (hs : Continuous s)
    (hys : ∀ t, 0 ≤ t → s t ≤ y t) {c m : ℝ → ℝ} (hfeas : Feasible y s π m0 c m)
    (hc : ContinuousOn c (Set.Ici 0)) (hint : IntegrableOn (felicity δ u v c m) (Set.Ioi 0))
    {ε0 : ℝ} (hε0 : 0 < ε0) (hε1 : ε0 < 1)
    (hscale : IntegrableOn (felicity δ u v (fun r => c r + ε0 * scaleA y s c m r)
      (fun r => m r + ε0 * scaleB m r)) (Set.Ioi 0)) :
    Optimal δ u v y s π m0 c m ↔
      (∀ t, 0 < t → HasDerivAt (fun r => up (c r)) ((δ + π t) * up (c t) - vp (m t)) t) ∧
        Tendsto (fun t => Real.exp (-(δ * t)) * up (c t) * m t) atTop (𝓝 0) :=
  ⟨fun hopt => ⟨costate_necessary hU hV hπ hopt hc,
      tvc_necessary hU hV hup hπ hy hs hopt hc hys hε0 hε1 hscale⟩,
    fun h => optimal_of_costate hU hV hup hfeas hc hint h.1 h.2⟩

/-- Cochrane (2023), A4 p. 640, "substituting out µ, we can write the familiar money demand
conditions": at an optimum with continuous consumption and `u' > 0`, at every `t > 0` the
costate `µ = u'(c)` has a derivative `µ̇_t` with `v'(m_t)/u'(c_t) = −µ̇_t/µ_t + δ + π_t`
(`costate_necessary` with `ContinuousTime.hamiltonian_money_demand`). -/
theorem money_demand_of_optimal (hU : RegularUtility u up) (hV : RegularUtility v vp)
    (hupp : ∀ x, 0 < x → 0 < up x) (hπ : Continuous π) {c m : ℝ → ℝ}
    (hopt : Optimal δ u v y s π m0 c m) (hc : ContinuousOn c (Set.Ici 0)) {t : ℝ}
    (ht : 0 < t) : ∃ dμ, HasDerivAt (fun r => up (c r)) dμ t ∧
      vp (m t) / up (c t) = -dμ / up (c t) + δ + π t := by
  have hu := hupp _ (hopt.1.2.2.2.1 t ht.le).1
  exact ⟨_, costate_necessary hU hV hπ hopt hc t ht,
    ContinuousTime.hamiltonian_money_demand rfl (by ring) hu.ne'⟩

/-! ## The hypotheses are satisfiable: the logarithmic steady state -/

/-- Cochrane (2023), A4 p. 640 (an instance): `log` is a regular utility with `log' = 1/x`. -/
theorem log_regular : RegularUtility Real.log (fun x => x⁻¹) where
  concave := strictConcaveOn_log_Ioi.concaveOn
  deriv := fun _x hx => Real.hasDerivAt_log hx.ne'
  cont := continuousOn_inv₀.mono fun _x hx => ne_of_gt hx

/-- **Cochrane (2023), A4 pp. 640–641, a non-vacuous instance of `optimal_of_costate`.** With
`u = v = log`, `δ > 0`, constant `y − s = c̄ > 0`, zero inflation `π = 0` and initial real
balances `m₀ = c̄/δ`, the steady state `c_t = c̄`, `m_t = c̄/δ` is optimal: `v'(m) = δ/c̄ = δu'(c)`
makes `µ = 1/c̄` constant and solves the costate equation, and `e^{−δt}m/c̄ → 0`. -/
theorem log_steady_state_optimal {δ cbar : ℝ} (hδ : 0 < δ) (hc : 0 < cbar) {y s : ℝ → ℝ}
    (hys : ∀ t, y t - s t = cbar) :
    Optimal δ Real.log Real.log y s (fun _ => 0) (cbar / δ) (fun _ => cbar)
      (fun _ => cbar / δ) := by
  have hm : 0 < cbar / δ := div_pos hc hδ
  have hfeas : Feasible y s (fun _ => 0) (cbar / δ) (fun _ => cbar) (fun _ => cbar / δ) := by
    refine ⟨rfl, continuousOn_const, ⟨∅, Set.countable_empty, fun t _ _ => ?_⟩,
      fun _ _ => ⟨hc, hm⟩, fun _ => integrableOn_const (by simp)⟩
    have : y t - cbar - s t - 0 * (cbar / δ) = 0 := by linarith [hys t]
    rw [this]
    exact hasDerivAt_const t _
  have hint : IntegrableOn (felicity δ Real.log Real.log (fun _ => cbar) (fun _ => cbar / δ))
      (Set.Ioi 0) := by
    have : IntegrableOn (fun x : ℝ => Real.exp (-δ * x) *
        (Real.log cbar + Real.log (cbar / δ))) (Set.Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hδ).mul_const _
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [felicity, neg_mul]
  refine optimal_of_costate log_regular log_regular (fun x hx => (inv_pos.2 hx).le) hfeas
    continuousOn_const hint (fun t _ => ?_) ?_
  · have : (δ + 0) * cbar⁻¹ - (cbar / δ)⁻¹ = 0 := by field_simp; ring
    exact (hasDerivAt_const t (cbar⁻¹)).congr_deriv (by linarith [this])
  · have h1 : Tendsto (fun t : ℝ => δ * t) atTop atTop := tendsto_id.const_mul_atTop hδ
    have h3 := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)).mul_const
      (cbar⁻¹ * (cbar / δ))
    simp only [zero_mul] at h3
    refine h3.congr fun t => ?_
    simp only [Function.comp]
    ring

end Cochrane.Monetarism.TidyR6Pontryagin
