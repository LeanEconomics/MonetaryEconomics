/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6HouseholdRoll
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Utility on an open domain and localized differentiation of expected utility

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.3, pp. 439–441
(eq. (19.9) and the first-order conditions (19.13)–(19.14)) and §19.5.1, p. 448. The household
problem of `HouseholdMeasure` assumed a period utility `u(c, m)` that is continuously
differentiable on all of `ℝ²` (`HouseholdMeasure.Smooth₂`), which excludes the standard utilities
with Inada conditions (`log c`, `c^{1−γ}/(1−γ)`), defined only for positive arguments. This module
replaces global smoothness by smoothness on an open domain and proves the differentiation of
expected utility under the integral sign for deviations localized where the plan is in a compact
part of the domain, with no boundedness assumption on the plan.

## Main definitions and results

* `C1On u uc um U`: `U ⊆ ℝ²` is open and `u` is differentiable at every point of `U` with partial
  derivatives `uc`, `um` continuous on `U` (`c1On_of_smooth₂`: global smoothness is the case
  `U = univ`).
* `Good U K p`: the point `p` has norm at most `K` and is at distance more than `1/(K + 1)` from
  the complement of `U`; `Kc U K` is a compact subset of `U` containing every point within
  `1/(2(K + 1))` of a good point (`good_add`, `kc_isCompact`, `kc_subset`); every point of `U` is
  good for some `K` (`exists_good`).
* `loc_deriv`: if `g`, `k` vanish wherever `(f, h)` is not good and are bounded where it is, then
  `ε ↦ E u(f + εg, h + εk)` is integrable for small `ε` and differentiable at `0` with derivative
  `E[u_c(f, h)g + u_m(f, h)k]`, whatever the size of `f` and `h` elsewhere.
* `slope_nonpos`: a function with derivative `D` at `0`, vanishing at `0` and nonpositive on the
  right of `0`, has `D ≤ 0` (one-sided first-order conditions).
-/

namespace Cochrane.Monetarism.TidyR6HouseholdLocal

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Utility that is smooth on an open domain -/

/-- Cochrane (2023), (19.9), p. 439, with Inada-type utilities in mind: the period utility
`u(c, m)` is differentiable at every point of the open set `U ⊆ ℝ²`, with partial derivatives
`u_c`, `u_m` continuous on `U`. -/
def C1On (u uc um : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) : Prop :=
  IsOpen U ∧ (∀ p ∈ U, HasFDerivAt (fun q : ℝ × ℝ => u q.1 q.2)
      (uc p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + um p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)
      p) ∧
    ContinuousOn (fun p : ℝ × ℝ => uc p.1 p.2) U ∧ ContinuousOn (fun p : ℝ × ℝ => um p.1 p.2) U

/-- Cochrane (2023), (19.9), p. 439: a utility smooth on all of `ℝ²`
(`HouseholdMeasure.Smooth₂`) is smooth on the domain `U = ℝ²`. -/
theorem c1On_of_smooth₂ {u uc um : ℝ → ℝ → ℝ} (h : HouseholdMeasure.Smooth₂ u uc um) :
    C1On u uc um Set.univ :=
  ⟨isOpen_univ, fun p _ => h.1 p.1 p.2, h.2.1.continuousOn, h.2.2.continuousOn⟩

/-- Cochrane (2023), (19.9), p. 439: a utility smooth on `U` is continuous on `U`. -/
theorem C1On.continuousOn {u uc um : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (h : C1On u uc um U) :
    ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) U :=
  fun p hp => (h.2.1 p hp).continuousAt.continuousWithinAt

/-- Cochrane (2023), (19.13)–(19.14), p. 440: along the line `e ↦ (x + eg, y + ek)`, at a
parameter `ε` whose point lies in `U`, a utility smooth on `U` has derivative `u_c g + u_m k`. -/
theorem C1On.hasDerivAt_line {u uc um : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (h : C1On u uc um U)
    {x y g k ε : ℝ} (hq : (x + ε * g, y + ε * k) ∈ U) :
    HasDerivAt (fun e => u (x + e * g) (y + e * k))
      (uc (x + ε * g) (y + ε * k) * g + um (x + ε * g) (y + ε * k) * k) ε := by
  have hpath : HasDerivAt (fun e : ℝ => (x + e * g, y + e * k)) (g, k) ε := by
    have h1 : HasDerivAt (fun e : ℝ => x + e * g) g ε := by
      simpa using ((hasDerivAt_id ε).mul_const g).const_add x
    have h2 : HasDerivAt (fun e : ℝ => y + e * k) k ε := by
      simpa using ((hasDerivAt_id ε).mul_const k).const_add y
    exact h1.prodMk h2
  have := (h.2.1 _ hq).comp_hasDerivAt ε hpath
  have e : (uc (x + ε * g) (y + ε * k) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      um (x + ε * g) (y + ε * k) • ContinuousLinearMap.snd ℝ ℝ ℝ) (g, k) =
      uc (x + ε * g) (y + ε * k) * g + um (x + ε * g) (y + ε * k) * k := by
    simp [smul_eq_mul]
  rw [e] at this
  exact this

/-- Cochrane (2023), (19.9), p. 439: a function continuous on an open set, extended by zero, is
Borel measurable. -/
theorem measurable_indicator_of_continuousOn {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {v : ℝ × ℝ → ℝ} (hv : ContinuousOn v U) : Measurable (U.indicator v) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hv.measurable_piecewise continuousOn_const hU.measurableSet

/-! ### Good points and compact parts of the domain -/

/-- Cochrane (2023), (19.9), p. 439: the point `p` is good at level `K` for the domain `U`: its
norm is at most `K` and it lies at distance more than `1/(K + 1)` from the complement of `U`. -/
def Good (U : Set (ℝ × ℝ)) (K : ℕ) (p : ℝ × ℝ) : Prop :=
  ‖p‖ ≤ K ∧ ENNReal.ofReal (1 / ((K : ℝ) + 1)) < Metric.infEDist p Uᶜ

/-- Cochrane (2023), (19.9), p. 439: the compact part of the domain reached by small deviations
from good points: norm at most `K + 1`, distance at least `1/(2(K + 1))` from the complement. -/
def Kc (U : Set (ℝ × ℝ)) (K : ℕ) : Set (ℝ × ℝ) :=
  {q | ‖q‖ ≤ (K : ℝ) + 1 ∧ ENNReal.ofReal (1 / (2 * ((K : ℝ) + 1))) ≤ Metric.infEDist q Uᶜ}

/-- Cochrane (2023), (19.9), p. 439: a deviation of norm less than `1/(2(K + 1))` from a good
point stays in the compact part `Kc U K`. -/
theorem good_add {U : Set (ℝ × ℝ)} {K : ℕ} {p d : ℝ × ℝ} (hp : Good U K p)
    (hd : ‖d‖ < 1 / (2 * ((K : ℝ) + 1))) : p + d ∈ Kc U K := by
  have hK : (0 : ℝ) ≤ K := K.cast_nonneg
  have ha1 : 1 / (2 * ((K : ℝ) + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  refine ⟨?_, ?_⟩
  · calc ‖p + d‖ ≤ ‖p‖ + ‖d‖ := norm_add_le _ _
      _ ≤ (K : ℝ) + 1 := by linarith [hp.1]
  · by_contra hlt
    rw [not_le] at hlt
    have h1 := Metric.infEDist_le_infEDist_add_edist (x := p) (y := p + d) (s := Uᶜ)
    have h2 : edist p (p + d) < ENNReal.ofReal (1 / (2 * ((K : ℝ) + 1))) := by
      rw [edist_dist, dist_eq_norm, show p - (p + d) = -d by abel, norm_neg]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hd
    have h3 := lt_of_le_of_lt h1 (ENNReal.add_lt_add hlt h2)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      show 1 / (2 * ((K : ℝ) + 1)) + 1 / (2 * ((K : ℝ) + 1)) = 1 / ((K : ℝ) + 1) by
        field_simp; ring] at h3
    exact absurd hp.2 (not_lt.2 h3.le)

/-- Cochrane (2023), (19.9), p. 439: a good point lies in the compact part `Kc U K`. -/
theorem good_mem_kc {U : Set (ℝ × ℝ)} {K : ℕ} {p : ℝ × ℝ} (hp : Good U K p) : p ∈ Kc U K := by
  have := good_add (d := 0) hp (by rw [norm_zero]; positivity)
  rwa [add_zero] at this

/-- Cochrane (2023), (19.9), p. 439: `Kc U K` is compact. -/
theorem kc_isCompact (U : Set (ℝ × ℝ)) (K : ℕ) : IsCompact (Kc U K) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const Metric.continuous_infEDist)
  · refine (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := (K : ℝ) + 1)).subset
      fun q hq => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hq.1

/-- Cochrane (2023), (19.9), p. 439: `Kc U K` lies inside the domain `U`. -/
theorem kc_subset (U : Set (ℝ × ℝ)) (K : ℕ) : Kc U K ⊆ U := by
  intro q hq
  by_contra h
  have h0 := Metric.infEDist_zero_of_mem (show q ∈ Uᶜ from h)
  have hq2 := hq.2
  rw [h0] at hq2
  have : (0 : ℝ) < 1 / (2 * ((K : ℝ) + 1)) := by positivity
  exact absurd hq2 (not_le.2 (ENNReal.ofReal_pos.2 this))

/-- Cochrane (2023), (19.9), p. 439: goodness is monotone in the level `K`. -/
theorem good_mono {U : Set (ℝ × ℝ)} {K K' : ℕ} (hKK : K ≤ K') {p : ℝ × ℝ} (hp : Good U K p) :
    Good U K' p := by
  have hc : (K : ℝ) ≤ K' := Nat.cast_le.2 hKK
  refine ⟨hp.1.trans hc, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hp.2⟩
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- Cochrane (2023), (19.9), p. 439: every point of an open domain is good at some level. -/
theorem exists_good {U : Set (ℝ × ℝ)} (hU : IsOpen U) {p : ℝ × ℝ} (hp : p ∈ U) :
    ∃ K, Good U K p := by
  have hpos : 0 < Metric.infEDist p Uᶜ := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have := Metric.mem_closure_iff_infEDist_zero.2 h0
    rw [hU.isClosed_compl.closure_eq] at this
    exact this hp
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ENNReal.ofReal (1 / ((n : ℝ) + 1)) < Metric.infEDist p Uᶜ := by
    by_cases htop : Metric.infEDist p Uᶜ = ⊤
    · exact ⟨0, by rw [htop]; exact ENNReal.ofReal_lt_top⟩
    · have hr : 0 < (Metric.infEDist p Uᶜ).toReal := ENNReal.toReal_pos hpos.ne' htop
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
      refine ⟨n, ?_⟩
      rw [← ENNReal.ofReal_toReal htop]
      exact (ENNReal.ofReal_lt_ofReal_iff hr).2 hn
  refine ⟨max n ⌈‖p‖⌉₊, ?_, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hn⟩
  · exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  · have hc : (n : ℝ) ≤ (max n ⌈‖p‖⌉₊ : ℕ) := by exact_mod_cast le_max_left _ _
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- Cochrane (2023), (19.9), p. 439: the set of good points is Borel measurable. -/
theorem measurableSet_good (U : Set (ℝ × ℝ)) (K : ℕ) : MeasurableSet {p | Good U K p} :=
  (isClosed_le continuous_norm continuous_const).measurableSet.inter
    (isOpen_lt continuous_const Metric.continuous_infEDist).measurableSet

/-- Cochrane (2023), (19.9), p. 439: a function continuous on the domain is bounded on its
compact part `Kc U K`. -/
theorem kc_bound {U : Set (ℝ × ℝ)} (K : ℕ) {v : ℝ × ℝ → ℝ} (hv : ContinuousOn v U) :
    ∃ C, 0 ≤ C ∧ ∀ q ∈ Kc U K, |v q| ≤ C := by
  obtain ⟨C, hC⟩ := (kc_isCompact U K).exists_bound_of_continuousOn (hv.mono (kc_subset U K))
  exact ⟨max C 0, le_max_right _ _, fun q hq => (hC q hq).trans (le_max_left _ _)⟩

/-! ### Localized differentiation under the integral sign -/

/-- Cochrane (2023), (19.13)–(19.14), p. 440 ("The first-order conditions"), **differentiation
of expected utility for localized deviations.** For `u` smooth on the open domain `U`,
measurable `f, h, g, k` and an integrable `u(f, h)`, if `(g, k)` vanishes wherever `(f, h)` is not
good at level `K` and is bounded by `B` where it is, then for small `ε` the utility
`u(f + εg, h + εk)` is integrable, and `ε ↦ E u(f + εg, h + εk)` has derivative
`E[u_c(f, h)g + u_m(f, h)k]` at `0`. No bound on `f` or `h` is needed. -/
theorem loc_deriv {μ : Measure Ω} [IsFiniteMeasure μ] {u uc um : ℝ → ℝ → ℝ}
    {U : Set (ℝ × ℝ)} (hu : C1On u uc um U) {f h g k : Ω → ℝ} (hf : Measurable f)
    (hh : Measurable h) (hg : Measurable g) (hk : Measurable k) {K : ℕ} {B : ℝ}
    (hloc : ∀ ω, (g ω = 0 ∧ k ω = 0) ∨ (Good U K (f ω, h ω) ∧ |g ω| ≤ B ∧ |k ω| ≤ B))
    (hint : Integrable (fun ω => u (f ω) (h ω)) μ) :
    ∃ r, 0 < r ∧ (∀ ε, |ε| < r → Integrable (fun ω => u (f ω + ε * g ω) (h ω + ε * k ω)) μ) ∧
      HasDerivAt (fun ε => ∫ ω, u (f ω + ε * g ω) (h ω + ε * k ω) ∂μ)
        (∫ ω, (uc (f ω) (h ω) * g ω + um (f ω) (h ω) * k ω) ∂μ) 0 := by
  set a : ℝ := 1 / (2 * ((K : ℝ) + 1)) with ha
  have ha0 : 0 < a := by positivity
  obtain ⟨Cu, hCu0, hCu⟩ := kc_bound (U := U) K hu.continuousOn
  obtain ⟨Cc, hCc0, hCc⟩ := kc_bound (U := U) K hu.2.2.1
  obtain ⟨Cm, hCm0, hCm⟩ := kc_bound (U := U) K hu.2.2.2
  set r : ℝ := a / (|B| + 1) with hr
  have hB1 : 0 < |B| + 1 := by positivity
  have hr0 : 0 < r := div_pos ha0 hB1
  -- the perturbed points stay in the compact part of the domain
  have hin : ∀ ω (ε : ℝ), |ε| < r → Good U K (f ω, h ω) → |g ω| ≤ B → |k ω| ≤ B →
      (f ω + ε * g ω, h ω + ε * k ω) ∈ Kc U K := by
    intro ω ε hε hG hgB hkB
    have hεB : ∀ x : ℝ, |x| ≤ B → |ε| * |x| < a := by
      intro x hx
      calc |ε| * |x| ≤ |ε| * (|B| + 1) :=
            mul_le_mul_of_nonneg_left (hx.trans ((le_abs_self B).trans (by linarith)))
              (abs_nonneg ε)
        _ < r * (|B| + 1) := mul_lt_mul_of_pos_right hε hB1
        _ = a := by rw [hr]; field_simp
    have e : (f ω + ε * g ω, h ω + ε * k ω) = (f ω, h ω) + (ε * g ω, ε * k ω) := rfl
    rw [e]
    refine good_add hG ?_
    rw [Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    exact max_lt (hεB _ hgB) (hεB _ hkB)
  set A : Set Ω := {ω | g ω = 0 ∧ k ω = 0} with hAdef
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun hg measurable_const).inter (measurableSet_eq_fun hk measurable_const)
  set uU : ℝ × ℝ → ℝ := U.indicator (fun p => u p.1 p.2) with huU
  have huUm : Measurable uU := measurable_indicator_of_continuousOn hu.1 hu.continuousOn
  have hrep : ∀ ε : ℝ, |ε| < r → (fun ω => u (f ω + ε * g ω) (h ω + ε * k ω)) =
      A.indicator (fun ω => u (f ω) (h ω)) +
        Aᶜ.indicator (fun ω => uU (f ω + ε * g ω, h ω + ε * k ω)) := by
    intro ε hε
    funext ω
    by_cases hω : ω ∈ A
    · have hω' : ω ∉ Aᶜ := fun h' => h' hω
      simp only [Pi.add_apply, Set.indicator_of_mem hω, Set.indicator_of_notMem hω']
      rw [hω.1, hω.2]
      simp
    · simp only [Pi.add_apply, Set.indicator_of_notMem hω,
        Set.indicator_of_mem (show ω ∈ Aᶜ from hω), zero_add]
      rcases hloc ω with h0 | ⟨hG, hgB, hkB⟩
      · exact absurd h0 hω
      · rw [huU, Set.indicator_of_mem (kc_subset U K (hin ω ε hε hG hgB hkB))]
  have hFm : ∀ ε : ℝ, Measurable (fun ω => uU (f ω + ε * g ω, h ω + ε * k ω)) := fun ε =>
    huUm.comp ((hf.add (hg.const_mul ε)).prodMk (hh.add (hk.const_mul ε)))
  have hbd : ∀ ε : ℝ, |ε| < r → ∀ ω,
      ‖Aᶜ.indicator (fun ω => uU (f ω + ε * g ω, h ω + ε * k ω)) ω‖ ≤ Cu := by
    intro ε hε ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_notMem (show ω ∉ Aᶜ from fun h' => h' hω), norm_zero]
      exact hCu0
    · rw [Set.indicator_of_mem (show ω ∈ Aᶜ from hω), Real.norm_eq_abs]
      rcases hloc ω with h0 | ⟨hG, hgB, hkB⟩
      · exact absurd h0 hω
      · have hq := hin ω ε hε hG hgB hkB
        rw [huU, Set.indicator_of_mem (kc_subset U K hq)]
        exact hCu _ hq
  have hFint : ∀ ε : ℝ, |ε| < r →
      Integrable (fun ω => u (f ω + ε * g ω) (h ω + ε * k ω)) μ := by
    intro ε hε
    rw [hrep ε hε]
    exact (hint.indicator hA).add (Integrable.of_bound
      ((hFm ε).aestronglyMeasurable.indicator hA.compl) Cu
      (Eventually.of_forall (hbd ε hε)))
  refine ⟨r, hr0, hFint, ?_⟩
  -- the derivative
  set ucU : ℝ × ℝ → ℝ := U.indicator (fun p => uc p.1 p.2) with hucU
  set umU : ℝ × ℝ → ℝ := U.indicator (fun p => um p.1 p.2) with humU
  have hucm : Measurable ucU := measurable_indicator_of_continuousOn hu.1 hu.2.2.1
  have humm : Measurable umU := measurable_indicator_of_continuousOn hu.1 hu.2.2.2
  have hF'0 : (fun ω => uc (f ω + 0 * g ω) (h ω + 0 * k ω) * g ω +
      um (f ω + 0 * g ω) (h ω + 0 * k ω) * k ω) =
      Aᶜ.indicator (fun ω => ucU (f ω, h ω) * g ω + umU (f ω, h ω) * k ω) := by
    funext ω
    simp only [zero_mul, add_zero]
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_notMem (show ω ∉ Aᶜ from fun h' => h' hω), hω.1, hω.2]
      simp
    · rw [Set.indicator_of_mem (show ω ∈ Aᶜ from hω)]
      rcases hloc ω with h0 | ⟨hG, -, -⟩
      · exact absurd h0 hω
      · have hq := kc_subset U K (good_mem_kc hG)
        rw [hucU, humU, Set.indicator_of_mem hq, Set.indicator_of_mem hq]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun ε ω => u (f ω + ε * g ω) (h ω + ε * k ω))
    (F' := fun ε ω => uc (f ω + ε * g ω) (h ω + ε * k ω) * g ω +
      um (f ω + ε * g ω) (h ω + ε * k ω) * k ω)
    (bound := fun _ => Cc * |B| + Cm * |B|) (s := Metric.ball 0 r)
    (Metric.ball_mem_nhds 0 hr0)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr0) fun ε hε => (hFint ε (by
      rwa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε)).aestronglyMeasurable)
    (by simpa using hFint 0 (by simpa using hr0))
    (by
      rw [hF'0]
      exact (((hucm.comp (hf.prodMk hh)).mul hg).add
        ((humm.comp (hf.prodMk hh)).mul hk)).aestronglyMeasurable.indicator hA.compl)
    ?_ (integrable_const _) ?_
  · simpa using key.2
  · refine Eventually.of_forall fun ω ε hε => ?_
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
    rcases hloc ω with h0 | ⟨hG, hgB, hkB⟩
    · rw [h0.1, h0.2]
      simp only [mul_zero, add_zero, norm_zero]
      exact add_nonneg (mul_nonneg hCc0 (abs_nonneg _)) (mul_nonneg hCm0 (abs_nonneg _))
    · have hq := hin ω ε hε hG hgB hkB
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul (hCc _ hq) (hgB.trans (le_abs_self B)) (abs_nonneg _) hCc0
      · rw [abs_mul]
        exact mul_le_mul (hCm _ hq) (hkB.trans (le_abs_self B)) (abs_nonneg _) hCm0
  · refine Eventually.of_forall fun ω ε hε => ?_
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
    rcases hloc ω with h0 | ⟨hG, hgB, hkB⟩
    · have e : (fun e : ℝ => u (f ω + e * g ω) (h ω + e * k ω)) = fun _ => u (f ω) (h ω) := by
        funext e
        rw [h0.1, h0.2]
        simp
      rw [e, h0.1, h0.2]
      simpa using hasDerivAt_const ε (u (f ω) (h ω))
    · exact hu.hasDerivAt_line (kc_subset U K (hin ω ε hε hG hgB hkB))

/-- Cochrane (2023), (19.13)–(19.14), p. 440 (one-sided first-order conditions at a corner): if
`φ(0) = 0`, `φ` has derivative `D` at `0` and `φ(ε) ≤ 0` for `0 < ε < η`, then `D ≤ 0`. -/
theorem slope_nonpos {φ : ℝ → ℝ} {D η : ℝ} (hd : HasDerivAt φ D 0) (h0 : φ 0 = 0) (hη : 0 < η)
    (hle : ∀ ε, 0 < ε → ε < η → φ ε ≤ 0) : D ≤ 0 := by
  have ht := hd.tendsto_slope_zero_right
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
  rw [zero_add, h0, sub_zero, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hε.1.le) (hle ε hε.1 hε.2)

end Cochrane.Monetarism.TidyR6HouseholdLocal
