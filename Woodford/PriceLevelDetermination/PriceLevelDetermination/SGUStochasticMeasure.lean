/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.SGUStochastic
import Mathlib.Probability.Distributions.Geometric
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Process.Filtration

/-!
# The perpetual sunspot of the Schmitt-Grohé–Uribe example on a probability space

Woodford (2003), *Interest and Prices*, Chapter 2, §4.3, p. 137 and Appendix A.17, pp. 653–655.
Module `SGUStochastic` refutes the book's claim that `Π*` is the unique rational-expectations
equilibrium "even allowing for stochastic equilibria of arbitrary form" with an explicit
switching-date forecast `geomE`. Here the same equilibrium is realised with Mathlib's measure
theory: `Ω = ℕ` with the geometric probability measure (`muSw`), the filtration `𝓕_t = σ(min(n, t))`
(`filtSw`), and `MeasureTheory.condExp`.

* `condExp_eq_geomE`, `condExp_apply`: `geomE` is the conditional expectation `μ[· | 𝓕_t]` of
  bounded variables (a.s., and at every state since all states have positive probability).
* `sgu_sunspot_measure`: adapted, positive sunspot `Π`, `P`; (4.5) with `μ[· | 𝓕_t]`; the
  transversality condition (1.24) and the bound (4.4); `Π₀ ≠ Π*`.
* The obstruction: `pos_functional_finite_support`, `expectationSystem_finite_support`,
  `no_expectationSystem_geomE` (countable state space; for uncountable ones the analogue is
  independent of the foundations, see the section docstring).
-/

namespace Woodford.PriceLevelDetermination.SGUStochasticMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open Woodford.PriceLevelDetermination.SGUStochastic (geomE Bdd summable_geom tsum_geom_weights
  geomE_of_le abs_geomE_le sunPi sunP sunV sun_eq45 sun_tvc sun_bound44 sunPi_bdd sunB_bdd
  sunP_pos sunP_succ)
open Woodford.PriceLevelDetermination.SchmittGroheUribe (sguA sguB sguC lamSGU phiSGU LSGU)

/-! ## The probability space -/

/-- Woodford (2003), p. 137 (counterexample): the switching probability `p = 2/3`. -/
noncomputable def pSw : unitInterval := ⟨2 / 3, by norm_num, by norm_num⟩

/-- Woodford (2003), p. 137 (counterexample): the switching-date distribution, the geometric
probability measure `P(n) = (1 − p)ⁿ p` on `ℕ`. -/
noncomputable abbrev muSw : Measure ℕ := geometricMeasure pSw

/-- Woodford (2003), p. 137 (counterexample): the date-`t` observation `min(n, t)` (the switching
date if it has occurred, otherwise "not yet"). -/
def obs (t n : ℕ) : ℕ := min n t

/-- Woodford (2003), p. 137 (counterexample): the date-`t` information, the σ-algebra generated
by `min(n, t)`. -/
abbrev infoSw (t : ℕ) : MeasurableSpace ℕ := MeasurableSpace.comap (obs t) inferInstance

/-- Woodford (2003), p. 137 (counterexample): every function on `ℕ` is measurable. -/
theorem measurable_nat {β : Type*} [MeasurableSpace β] (f : ℕ → β) : Measurable f :=
  measurable_from_nat

/-- Woodford (2003), p. 137 (counterexample): information is a sub-σ-algebra. -/
theorem infoSw_le (t : ℕ) : infoSw t ≤ (inferInstance : MeasurableSpace ℕ) :=
  (measurable_nat (obs t)).comap_le

/-- Woodford (2003), p. 137 (counterexample): **information accumulates** — `(infoSw t)` is a
filtration. -/
noncomputable def filtSw : Filtration ℕ (inferInstance : MeasurableSpace ℕ) where
  seq := infoSw
  mono' s t hst := by
    have h : obs s = obs s ∘ obs t := by
      funext n
      simp only [obs, Function.comp_apply]
      omega
    change MeasurableSpace.comap (obs s) _ ≤ MeasurableSpace.comap (obs t) _
    rw [h, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_nat (obs s)).comap_le
  le' := infoSw_le

/-- Woodford (2003), p. 137 (counterexample): a function of `min(n, t)` is `infoSw t`-strongly
measurable. -/
theorem stronglyMeasurable_of_obs {t : ℕ} (G : ℕ → ℝ) :
    StronglyMeasurable[infoSw t] (fun n => G (obs t n)) :=
  ((measurable_nat G).comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable

/-- Woodford (2003), p. 137 (counterexample): `infoSw t`-measurable sets do not separate states
that have not switched by `t`. -/
theorem mem_of_measurableSet {t : ℕ} {s : Set ℕ} (hs : MeasurableSet[infoSw t] s) {n n' : ℕ}
    (hn : t ≤ n) (hn' : t ≤ n') : n ∈ s ↔ n' ∈ s := by
  obtain ⟨S, -, rfl⟩ := hs
  simp only [Set.mem_preimage, obs, min_eq_right hn, min_eq_right hn']

/-- Woodford (2003), p. 137 (counterexample): bounded functions are integrable. -/
theorem integrable_of_bdd {f : ℕ → ℝ} (hf : Bdd f) : Integrable f muSw := by
  obtain ⟨C, hC⟩ := hf
  exact Integrable.of_bound (measurable_nat f).aestronglyMeasurable C
    (Eventually.of_forall fun n => by rw [Real.norm_eq_abs]; exact hC n)

/-- Woodford (2003), p. 137 (counterexample): `p ≠ 0`. -/
theorem pSw_ne_zero : pSw ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  norm_num [pSw] at this

/-- Woodford (2003), p. 137 (counterexample): set integrals as weighted sums. -/
theorem setIntegral_eq_tsum (s : Set ℕ) (f : ℕ → ℝ) :
    ∫ n in s, f n ∂muSw = ∑' n : ℕ, (1 - 2 / 3 : ℝ) ^ n * (2 / 3) * s.indicator f n := by
  rw [← integral_indicator MeasurableSet.of_discrete, muSw,
    integral_geometricMeasure pSw_ne_zero]
  rfl

/-- Woodford (2003), p. 137 (counterexample): **the explicit forecast `geomE` is (a version of)
Mathlib's conditional expectation** `μ[f | 𝓕_t]` for bounded `f`: almost surely, and — every state
having positive probability — at every state. -/
theorem condExp_eq_geomE {f : ℕ → ℝ} (hf : Bdd f) (t : ℕ) :
    muSw[f | infoSw t] =ᵐ[muSw] geomE (2 / 3) t f := by
  have hm := infoSw_le t
  have : SigmaFinite (muSw.trim hm) := inferInstance
  set c := ∑' k, 2 / 3 * (1 - 2 / 3 : ℝ) ^ k * f (t + k) with hc
  have hg : geomE (2 / 3) t f = fun n => (fun k => if k < t then f k else c) (obs t n) := by
    funext n
    unfold geomE obs
    by_cases hn : n < t
    · simp only [hn, ↓reduceIte, min_eq_left hn.le]
    · simp only [hn, ↓reduceIte, min_eq_right (not_lt.mp hn), lt_irrefl]
      exact hc.symm
  obtain ⟨C, hC⟩ := hf
  have hgb : Bdd (geomE (2 / 3) t f) := ⟨C, abs_geomE_le (by norm_num) (by norm_num) hC t⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm (integrable_of_bdd ⟨C, hC⟩)
    (fun s _ _ => (integrable_of_bdd hgb).integrableOn) (fun s hs _ => ?_) ?_).symm
  · rw [setIntegral_eq_tsum, setIntegral_eq_tsum]
    have hw : ∀ (z : ℕ → ℝ), Bdd z → Summable (fun n : ℕ =>
        (1 - 2 / 3 : ℝ) ^ n * (2 / 3) * s.indicator z n) := by
      intro z ⟨D, hD⟩
      refine Summable.of_norm_bounded
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 - 2 / 3 : ℝ) < 1)).mul_right
          (2 / 3 * |D|)) (fun n => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
      have h1 : |s.indicator z n| ≤ |D| := by
        unfold Set.indicator
        split_ifs
        · exact (hD n).trans (le_abs_self D)
        · simp
      have h2 : (0 : ℝ) ≤ (1 - 2 / 3) ^ n * (2 / 3) := by positivity
      nlinarith
    rw [← (hw _ hgb).sum_add_tsum_nat_add t, ← (hw _ ⟨C, hC⟩).sum_add_tsum_nat_add t]
    congr 1
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_range] at hn
      unfold Set.indicator geomE
      simp only [hn, ↓reduceIte]
    · by_cases hts : t ∈ s
      · have hin : ∀ k, k + t ∈ s := fun k => (mem_of_measurableSet hs le_rfl (by omega)).mp hts
        have e1 : ∀ k, (1 - 2 / 3 : ℝ) ^ (k + t) * (2 / 3) * s.indicator (geomE (2 / 3) t f)
            (k + t) = (1 - 2 / 3) ^ t * (2 / 3 * (1 - 2 / 3) ^ k * c) := fun k => by
          rw [Set.indicator_of_mem (hin k), geomE_of_le f (by omega), pow_add]
          ring
        have e2 : ∀ k, (1 - 2 / 3 : ℝ) ^ (k + t) * (2 / 3) * s.indicator f (k + t) =
            (1 - 2 / 3) ^ t * (2 / 3 * (1 - 2 / 3) ^ k * f (t + k)) := fun k => by
          rw [Set.indicator_of_mem (hin k), pow_add, add_comm k t]
          ring
        simp only [e1, e2]
        rw [tsum_mul_left, tsum_mul_left, tsum_mul_right, tsum_geom_weights (by norm_num)
          (by norm_num), one_mul]
      · have hout : ∀ k, k + t ∉ s := fun k h =>
          hts ((mem_of_measurableSet hs (by omega) le_rfl).mp h)
        simp only [Set.indicator_of_notMem (hout _), mul_zero]
  · rw [hg]
    exact (stronglyMeasurable_of_obs (t := t)
      (fun k => if k < t then f k else c)).aestronglyMeasurable

/-- Woodford (2003), p. 137 (counterexample): every state has positive probability, so an almost
sure equality on `ℕ` holds everywhere. -/
theorem eq_of_ae_eq {f g : ℕ → ℝ} (h : f =ᵐ[muSw] g) (n : ℕ) : f n = g n := by
  by_contra hne
  have hpos : 0 < muSw {n} := by
    rw [muSw, geometricMeasure_singleton pSw_ne_zero, ENNReal.ofReal_pos]
    exact geometricMeasure_pos pSw_ne_zero (by
      intro h1
      have := congrArg Subtype.val h1
      norm_num [pSw] at this) n
  have hsub : ({n} : Set ℕ) ⊆ {m | f m ≠ g m} := by
    intro m hm
    rw [Set.mem_singleton_iff] at hm
    subst hm
    exact hne
  have h0 : muSw {m | f m ≠ g m} = 0 := ae_iff.mp h
  exact absurd (measure_mono_null hsub h0) hpos.ne'

/-- Woodford (2003), p. 137 (counterexample): `μ[f | 𝓕_t] = geomE t f` at every state, for bounded
`f`. -/
theorem condExp_apply {f : ℕ → ℝ} (hf : Bdd f) (t n : ℕ) :
    muSw[f | infoSw t] n = geomE (2 / 3) t f n :=
  eq_of_ae_eq (condExp_eq_geomE hf t) n

/-! ## The sunspot equilibrium with Mathlib conditional expectations -/

/-- Woodford (2003), A.17 (counterexample): the transversality integrand is bounded at each
date. -/
theorem sunV_bdd {μ : ℝ} (hμ : 0 < μ) (T : ℕ) : Bdd (sunV μ T) :=
  ⟨3 * (μ / 2) ^ T * 3 ^ T, fun m => by
    obtain ⟨h0, h1⟩ := SGUStochastic.sunV_bounds hμ T m
    rw [abs_of_nonneg h0]
    have h3 : (3 : ℝ) ^ min T m ≤ 3 ^ T := pow_le_pow_right₀ (by norm_num) (min_le_left _ _)
    have h4 : 0 ≤ 3 * (μ / 2) ^ T := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 h4]⟩

/-- Woodford (2003), p. 137 and A.17, **the refutation on a genuine probability space**: on
`(ℕ, geometric(2/3))` with the filtration `𝓕_t = σ(min(n, t))` of the switching date and
Mathlib's conditional expectation `μ[· | 𝓕_t]`, with `θ = Ȳ = 1`, `β = 1/2`, `Π* = 1`,
`φ_π = 5/4` (E5 holds) and any `1 < μ̄ < 2`: the sunspot inflation `Π_t` and prices `P_t` are
`𝓕_t`-adapted, positive, `P_{t+1} = Π_{t+1} P_t`; (4.5) `μ[B(Π_{t+1}) | 𝓕_t] = A(Π_t)` holds (in
every state, hence a.s.); the transversality condition `μ[β^T λ_T D_T/P_T | 𝓕_t] → 0` and the
bound (4.4) hold in every state; and `Π₀ ≠ Π*`. -/
theorem sgu_sunspot_measure {μ : ℝ} (hμ1 : 1 < μ) (hμ2 : μ < 2) :
    (0 < sguC 1 (1 / 2) 1 (5 / 4) ∧ (1 : ℝ) < 5 / 4 ∧ (1 / 2 : ℝ) < 1 ∧ 1 / 2 * μ < 1) ∧
    (∀ t, StronglyMeasurable[filtSw t] (sunPi t) ∧ StronglyMeasurable[filtSw t] (sunP t)) ∧
    (∀ t n, 0 < sunPi t n ∧ 0 < sunP t n ∧ sunP (t + 1) n = sunPi (t + 1) n * sunP t n) ∧
    (∀ t n, muSw[fun m => sguB 1 1 (1 / 2) 1 (5 / 4) (sunPi (t + 1) m) | filtSw t] n =
      sguA 1 1 (1 / 2) 1 (5 / 4) (sunPi t n)) ∧
    (∀ t n, Tendsto (fun T => muSw[sunV μ T | filtSw t] n) atTop (𝓝 0)) ∧
    (∀ t n, Summable (fun T : ℕ => (1 / 2 : ℝ) ^ T * muSw[fun m =>
      lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi T m)) *
        (1 + phiSGU (1 / 2) 1 (5 / 4) (sunPi T m) / (1 + phiSGU (1 / 2) 1 (5 / 4) (sunPi T m)) *
          LSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi T m))) | filtSw t] n)) ∧
    (∀ n, sunPi 0 n ≠ 1) := by
  have hμ0 : 0 < μ := by linarith
  refine ⟨⟨by unfold sguC; norm_num, by norm_num, by norm_num, by linarith⟩, fun t => ⟨?_, ?_⟩,
    fun t n => ⟨SGUStochastic.sunPi_pos t n, sunP_pos t n, sunP_succ t n⟩, fun t n => ?_,
    fun t n => ?_, fun t n => ?_, fun n => ?_⟩
  · have h : sunPi t = fun n => (fun k => if k < t then (1 : ℝ) else 1 / 3) (obs t n) := by
      funext n
      unfold sunPi obs
      by_cases hn : n < t
      · simp only [hn, ↓reduceIte, min_eq_left hn.le]
      · simp only [hn, ↓reduceIte, min_eq_right (not_lt.mp hn), lt_irrefl]
    rw [h]
    exact stronglyMeasurable_of_obs (t := t) (fun k => if k < t then (1 : ℝ) else 1 / 3)
  · have h : sunP t = fun n => (fun k => (1 / 3 : ℝ) ^ k) (obs t n) := by
      funext n
      unfold sunP obs
      rw [min_comm]
    rw [h]
    exact stronglyMeasurable_of_obs (t := t) (fun k => (1 / 3 : ℝ) ^ k)
  · change muSw[_ | infoSw t] n = _
    rw [condExp_apply (sunB_bdd (t + 1)), sun_eq45]
  · change Tendsto (fun T => muSw[sunV μ T | infoSw t] n) atTop (𝓝 0)
    simp only [condExp_apply (sunV_bdd hμ0 _)]
    exact sun_tvc hμ1 hμ2 t n
  · have hb : ∀ T, Bdd (fun m => lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi T m)) *
        (1 + phiSGU (1 / 2) 1 (5 / 4) (sunPi T m) / (1 + phiSGU (1 / 2) 1 (5 / 4) (sunPi T m)) *
          LSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi T m)))) := by
      intro T
      refine ⟨6, fun m => ?_⟩
      obtain ⟨hl0, hl3⟩ := SGUStochastic.sun_lam_bounds T m
      set i := phiSGU (1 / 2) 1 (5 / 4) (sunPi T m) with hi
      have hi0 : 0 ≤ i := SchmittGroheUribe.phiSGU_nonneg _ _ _ _
      have hq0 : 0 ≤ i / (1 + i) := by positivity
      have hq1 : i / (1 + i) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hL0 : 0 ≤ LSGU 1 1 i := by unfold LSGU; positivity
      have hL1 : LSGU 1 1 i ≤ 1 := by unfold LSGU; rw [div_le_one (by linarith)]; linarith
      have hprod : i / (1 + i) * LSGU 1 1 i ≤ 1 := by nlinarith
      have hin : 0 ≤ 1 + i / (1 + i) * LSGU 1 1 i := by positivity
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    change Summable (fun T : ℕ => (1 / 2 : ℝ) ^ T * muSw[_ | infoSw t] n)
    simp only [condExp_apply (hb _)]
    exact sun_bound44 t n
  · unfold sunPi
    simp

/-! ## Why the core `ExpectationSystem` cannot carry the sunspot

A core `ExpectationSystem` defines `E_t` on **all** functions `Ω → ℝ`. For `Ω = ℕ` (any countable
state space) every positive linear functional on all of `ℝ^ℕ` depends on finitely many
coordinates (`pos_functional_finite_support`), so each `E_t(·)(ω)` is a finitely supported
average (`expectationSystem_finite_support`) and no expectation system extends the geometric
switching-date forecasts (`no_expectationSystem_geomE`). For an arbitrary (uncountable) `Ω` the
analogous statement is **not provable**: if `Ω` carries a countably complete nonprincipal
ultrafilter `U` (`|Ω|` at least a measurable cardinal), `E y := U-lim y` (every real function is
`U`-a.e. constant) is a positive, constant-preserving, idempotent linear operator — an
`ExpectationSystem` with `E_t = E` — that is not finitely supported; the existence of measurable
cardinals cannot be refuted in Lean's foundations (assuming their consistency). -/

/-- Woodford (2003), p. 137 (obstruction): **a positive linear functional on all of `ℝ^ℕ` depends
on finitely many coordinates**: there is `N` such that `φ y = 0` whenever `y` vanishes on
`{0, …, N}`. -/
theorem pos_functional_finite_support (φ : (ℕ → ℝ) →ₗ[ℝ] ℝ) (hpos : ∀ y, 0 ≤ y → 0 ≤ φ y) :
    ∃ N, ∀ y : ℕ → ℝ, (∀ n ≤ N, y n = 0) → φ y = 0 := by
  by_contra h
  push Not at h
  have hz : ∀ N, ∃ z : ℕ → ℝ, 0 ≤ z ∧ (∀ n ≤ N, z n = 0) ∧ 0 < φ z := by
    intro N
    obtain ⟨y, hy, hφ⟩ := h N
    set yp : ℕ → ℝ := fun n => max (y n) 0 with hyp
    set ym : ℕ → ℝ := fun n => max (-y n) 0 with hym
    have hsplit : y = yp - ym := by
      funext n
      simp only [hyp, hym, Pi.sub_apply]
      rcases le_total 0 (y n) with h0 | h0
      · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
    have hp0 : 0 ≤ yp := fun n => le_max_right _ _
    have hm0 : 0 ≤ ym := fun n => le_max_right _ _
    have hpN : ∀ n ≤ N, yp n = 0 := fun n hn => by simp [hyp, hy n hn]
    have hmN : ∀ n ≤ N, ym n = 0 := fun n hn => by simp [hym, hy n hn]
    rw [hsplit, map_sub] at hφ
    rcases (hpos yp hp0).lt_or_eq with h1 | h1
    · exact ⟨yp, hp0, hpN, h1⟩
    · rcases (hpos ym hm0).lt_or_eq with h2 | h2
      · exact ⟨ym, hm0, hmN, h2⟩
      · exact absurd (by rw [← h1, ← h2, sub_self]) hφ
  choose z hz0 hzN hzpos using hz
  set c : ℕ → ℝ := fun N => ((N : ℝ) + 1) / φ (z N) with hc
  have hc0 : ∀ N, 0 ≤ c N := fun N => div_nonneg (by positivity) (hzpos N).le
  set Z : ℕ → ℝ := fun n => ∑ N ∈ Finset.range n, c N * z N n with hZ
  have hle : ∀ M, (∑ N ∈ Finset.range M, c N • z N) ≤ Z := by
    intro M n
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hZ]
    calc ∑ N ∈ Finset.range M, c N * z N n ≤ ∑ N ∈ Finset.range (n + M), c N * z N n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
            (fun N _ _ => mul_nonneg (hc0 N) (hz0 N n))
      _ = ∑ N ∈ Finset.range n, c N * z N n := by
          rw [Finset.sum_range_add]
          have : ∑ k ∈ Finset.range M, c (n + k) * z (n + k) n = 0 :=
            Finset.sum_eq_zero fun k _ => by rw [hzN (n + k) n (by omega), mul_zero]
          rw [this, add_zero]
  have hval : ∀ M, φ (∑ N ∈ Finset.range M, c N • z N) = ∑ N ∈ Finset.range M, ((N : ℝ) + 1) :=
    fun M => by
      rw [map_sum]
      refine Finset.sum_congr rfl fun N _ => ?_
      rw [map_smul, smul_eq_mul, hc, div_mul_cancel₀ _ (hzpos N).ne']
  set M := ⌈φ Z⌉₊ + 1 with hM
  have h1 : φ (∑ N ∈ Finset.range M, c N • z N) ≤ φ Z := by
    have := hpos _ (sub_nonneg.mpr (hle M))
    rw [map_sub] at this
    linarith
  have h2 : (M : ℝ) ≤ ∑ N ∈ Finset.range M, ((N : ℝ) + 1) := by
    have := Finset.card_nsmul_le_sum (Finset.range M) (fun N : ℕ => (N : ℝ) + 1) 1
      (fun N _ => by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
    simpa using this
  have h3 : φ Z < M := by
    rw [hM]
    push_cast
    linarith [Nat.le_ceil (φ Z)]
  rw [hval] at h1
  linarith

/-- Woodford (2003), p. 137 (obstruction): **on the countable state space `ℕ`, every conditional
expectation of a core `ExpectationSystem` is finitely supported**. -/
theorem expectationSystem_finite_support (𝔼 : ExpectationSystem ℕ) (t ω : ℕ) :
    ∃ N, ∀ y : ℕ → ℝ, (∀ n ≤ N, y n = 0) → 𝔼.E t y ω = 0 :=
  pos_functional_finite_support ((LinearMap.proj ω).comp (𝔼.E t)) (fun y hy => by
    have h := 𝔼.mono t hy ω
    rw [map_zero] at h
    exact h)

/-- Woodford (2003), p. 137 (obstruction): **no core `ExpectationSystem` on `ℕ` agrees with the
switching-date forecasts on bounded variables**, so the perpetual sunspot of
`sgu_sunspot_measure` cannot be expressed with the core `ExpectationSystem` on `ℕ`. -/
theorem no_expectationSystem_geomE (𝔼 : ExpectationSystem ℕ) :
    ¬ ∀ t (y : ℕ → ℝ), Bdd y → 𝔼.E t y = geomE (2 / 3) t y := by
  intro h
  obtain ⟨N, hN⟩ := expectationSystem_finite_support 𝔼 0 0
  set y : ℕ → ℝ := fun n => if n = N + 1 then 1 else 0 with hy
  have hb : Bdd y := ⟨1, fun n => by simp only [hy]; split_ifs <;> norm_num⟩
  have h0 : 𝔼.E 0 y 0 = 0 :=
    hN y (fun n hn => by simp only [hy, show n ≠ N + 1 by omega, ↓reduceIte])
  rw [h 0 y hb, geomE_of_le y le_rfl] at h0
  have : ∑' k, 2 / 3 * (1 - 2 / 3 : ℝ) ^ k * y (0 + k) =
      2 / 3 * (1 - 2 / 3 : ℝ) ^ (N + 1) := by
    rw [tsum_eq_single (N + 1)]
    · simp [hy]
    · intro k hk
      simp [hy, hk]
  rw [this] at h0
  norm_num at h0

end Woodford.PriceLevelDetermination.SGUStochasticMeasure
